"""Convertion PyTDs into constraint.types."""

import logging


from byterun.constraint import types
from pytypedecl import pytd
from pytypedecl.parse import visitors as tdvisitors
import pytypedecl.parse.utils

# Because pytypedecl uses C++ style names we have to use a mix in this file.
# pylint: disable=invalid-name

log = logging.getLogger(__name__)

_builtin_pytds = None


def _load_pytd():
  global _builtin_pytds
  if not _builtin_pytds:
    _builtin_pytds = pytypedecl.parse.utils.GetBuiltins()
    _builtin_pytds = tdvisitors.LookupClasses(_builtin_pytds)


class PyTDConvertVisit(types.Visitor):
  """Visitor that builds PyTD types from constraint.types."""

  def visit_object(self, tp):
    return pytd.ClassType("object")

  def visit_nothing(self, tp):
    return pytd.NothingType()

  def visit_dynamic(self, tp):
    return pytd.NamedType("dynamic")

  def visit_function(self, tp):
    return pytd.Signature(tuple(tp.argument_types), tp.return_type, (), (),
                          False, None)

  def visit_union(self, tp):
    return pytd.UnionType(tuple(tp.subtypes))

  def visit_instance(self, tp):
    return pytd.ClassType(tuple(tp.name))

  def visit_any(self, tp):
    raise ValueError


def compute_mro(cls, object_class):
  parents = cls.parents
  if not parents and cls != object_class:
    parents = [object_class]
  parent_mros = [compute_mro(c, object_class) for c in parents]
  return types.merge_mros(*([[cls]] + parent_mros))


class PyTDImportVisitor(object):
  """Visitor that converts PyTD objects into matching type objects.
  """

  def __init__(self, vm):
    _load_pytd()
    self.vm = vm
    self.class_table = {}
    self.type_table = {}
    self.mro_table = {}

    for x in _builtin_pytds.classes:
      self.mro_table[x] = types.MRO(None)

    object_class = _builtin_pytds.Lookup("object")
    for x in _builtin_pytds.classes:
      self.mro_table[x].classes = [self.convert(c)
                                   for c in compute_mro(x, object_class)]

  def convert(self, td):
    return td.Visit(self)

  def VisitClass(self, cls):
    """Convert a PyTD class to a types.Class."""
    if cls in self.class_table:
      return self.class_table[cls]

    class_members = {}
    for func in cls.methods:
      if len(func.signatures) > 1:
        log.warning("Ignoring all but the first signature of %s.", func.name)
      class_members[func.name] = func.signatures[0]
    class_members.update((v.name, v.type) for v in cls.constants)
    result = types.Class(class_members, {}, name=cls.name)

    self.class_table[cls] = result
    return result

  def _cache_type(self, td, compute):
    if td in self.type_table:
      return self.type_table[td]

    result = compute()
    self.type_table[td] = result
    return result

  def VisitUnionType(self, td):
    return self._cache_type(td, lambda: types.Union(td.type_list, self.vm))

  def VisitClassType(self, td):
    # if td.name == "object":
    #   return self._cache_type(td, lambda: types.Object(self.vm))
    if td.cls:
      mro = self.mro_table[td.cls]
      return self._cache_type(
          td,
          lambda: types.Instance(mro, {}, self.vm, name=td.name))
    else:
      return self.VisitOtherType(td)

  def VisitSignature(self, td):
    params = [t.type for t in td.params]
    return self._cache_type(
        td, lambda: types.Function(params, td.return_type, self.vm))

  def VisitUnknownType(self, td):
    return self._cache_type(td, lambda: types.Dynamic(self.vm))

  def VisitNothingType(self, td):
    return self._cache_type(td, lambda: types.Nothing(self.vm))

  def VisitOtherType(self, td):
    log.warning("Unsupported PyTD type: %r", td)
    return self._cache_type(td, lambda: types.Dynamic(self.vm))

  VisitNamedType = VisitOtherType
  VisitNativeType = VisitOtherType
  VisitHomogeneousContainerType = VisitOtherType
  VisitGenericType = VisitOtherType
  VisitIntersectionType = VisitOtherType


def load_builtins(vm):
  """Load the PyTD builtins and convert them into types.

  Args:
    vm: The ConstraintVirtualMachine to use for type creation.
  Returns:
    A dict mapping names to types.
  """
  converter = PyTDImportVisitor(vm)

  builtins = {}

  for x in _builtin_pytds.constants:
    builtins[x.name] = converter.convert(x.type)

  for x in _builtin_pytds.functions:
    if len(x.signatures) > 1:
      log.warning("Ignoring all but the first signature of %s.", x.name)
    builtins[x.name] = converter.convert(x.signatures[0])

  for x in _builtin_pytds.classes:
    cls = pytd.ClassType(x.name)
    tdvisitors.FillInClasses(cls, _builtin_pytds)
    builtins[cls.name] = converter.convert(cls)

  return builtins
