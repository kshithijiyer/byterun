"""A abstract virtual machine for bytecode that generates subtype constraints.
"""

import logging


from byterun import abstractvm
from byterun import pycfg
from byterun.constraint import constraint_store
from byterun.constraint import pytd as constraint_pytd
from byterun.constraint import types
from byterun.constraint import utils
# from byterun.constraint import sat_encoding

log = logging.getLogger(__name__)


class ConstraintVirtualMachine(abstractvm.AncestorTraversalVirtualMachine):
  """A virtual machine that generates subtype constraints."""

  def __init__(self):
    super(ConstraintVirtualMachine, self).__init__()
    self.cfg = pycfg.CFG()
    self.constraints = constraint_store.ConstraintStore(self)
    self.builtins_types = constraint_pytd.load_builtins(self)

    self.type_map = {
        native_type: self.builtins_types[native_type.__name__]
        for native_type in (int, float, str, type(None), object, tuple, type)}
    self.type_map[utils.HashableDict] = self.builtins_types["dict"]
    object_type = self.builtins_types["object"]
    log.info("%r: %r", object_type, object_type.get_structure())
    int_type = self.builtins_types["int"]
    log.info("%r: %r", int_type, int_type.get_structure())

  def make_instance(self, cls, args, kws):
    raise NotImplementedError

  def make_function(self, name, codety, globs, defaults, closure):
    assert isinstance(codety, types.ConstantType)
    code, = codety.values
    # TODO(ampere): Handle defaults.
    # TODO(ampere): Handle closure
    argtypes = [self.constraints.new_variable()
                for _ in range(code.co_argcount)]
    initial_locals = dict(zip(code.co_varnames, argtypes))
    for n, v in initial_locals.iteritems():
      v.add_name(n)
    frame = self.make_frame_with_dicts(code, globs, initial_locals)
    ret = self.run_frame(frame)
    tp = types.Function(argtypes, ret, self)
    self.constraints.add_target(tp)
    return tp

  def call_function(self, func, posargs, namedargs):
    if isinstance(func, types.Function):
      if not isinstance(func.return_type, types.ConstantType):
        retval = self.constraints.new_variable()
        self.constraints.constrain_subtype(retval,
                                           func.return_type)
      else:
        # There are no interesting subtypes of constant types, so just use it
        # directly. This is also required so that constants can be found by the
        # abstractvm when they are required.
        retval = func.return_type
    else:
      retval = self.constraints.new_variable()
    self.constraints.constrain_subtype(func,
                                       types.Function(posargs, retval, self))
    return retval

  def check_value_type(self, value):
    assert isinstance(value, types.Type)

  def load_constant(self, value):
    return types.ConstantType([value], self)

  def convert_value(self, value):
    if isinstance(value, types.Type):
      return value
    elif isinstance(value, type) and value in self.type_map:
      return types.ClassConstructor(self.type_map[value].mro, self)
    else:
      return types.ConstantType([value], self)

  def load_local(self, name):
    value = super(ConstraintVirtualMachine, self).load_local(name)
    return self.convert_value(value)

  def load_global(self, name):
    value = super(ConstraintVirtualMachine, self).load_global(name)
    return self.convert_value(value)

  def load_builtin(self, name):
    if name == "__any_object__":
      return self.constraints.new_variable()

    value = super(ConstraintVirtualMachine, self).load_builtin(name)
    return self.convert_value(value)

  def store_local(self, name, value):
    value.add_name(name)
    super(ConstraintVirtualMachine, self).store_local(name, value)

  def load_attr(self, obj, attr):
    self.check_value_type(obj)
    assert isinstance(attr, str)
    ret = obj.getattr(attr)
    self.constraints.constrain_subtype(
        obj, types.Instance(self.type_map[object].mro, {attr: ret}, self))
    ret.add_name((obj.name or "") + "." + attr)
    return ret

  def store_attr(self, obj, attr, value):
    self.check_value_type(obj)
    assert isinstance(attr, str)
    self.check_value_type(value)
    self.constraints.constrain_subtype(
        obj, types.Instance(self.type_map[object].mro, {attr: value}, self))

  def get_locals_dict(self):
    return self.frame.f_locals

  def get_locals_dict_bytecode(self):
    return self.load_constant(utils.HashableDict(self.frame.f_locals))

  def get_globals_dict(self):
    return self.frame.f_globals

  def make_class(self, name, bases, methods):
    base_mros = [list(m.mro.classes) for m in bases.get_single_value()]
    selfvar = self.constraints.new_variable()
    for func in methods.get_single_value().values():
      if isinstance(func, types.Function):
        self.constraints.constrain_equal(func.argument_types[0], selfvar)
    cls = types.Class(class_members=methods.get_single_value(),
                      instance_members={},
                      name=name.get_single_value())
    mro = types.MRO(types.merge_mros(*([[cls]] + base_mros)))
    # TODO(ampere): Equate the first parameter with the new class object for
    # class methods.
    # TODO(ampere): Run the solver to simplify the type and then generate a
    # for-all type. Calls to the constructor produce new instantiations.
    constructor = types.ClassConstructor(mro, self)
    return constructor

  def build_tuple(self, content):
    return self.load_constant(tuple(content))
