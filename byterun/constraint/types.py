"""A set of classes representing a type lattice for Python."""

import collections
import logging

log = logging.getLogger(__name__)

# TODO(ampere): Make singletons for Object and Nothing and perhaps Dynamic.


class Visitor(object):
  """Base class for Type visitors."""

  def visit_any(self, tp):
    return tp

  def visit_object(self, tp):
    return self.visit_any(tp)

  def visit_nothing(self, tp):
    return self.visit_any(tp)

  def visit_dynamic(self, tp):
    return self.visit_any(tp)

  def visit_function(self, tp):
    return self.visit_any(tp)

  def visit_instance(self, tp):
    return self.visit_any(tp)

  def visit_union(self, tp):
    return self.visit_any(tp)

  def visit_constant(self, tp):
    return self.visit_any(tp)

  def visit_variable(self, tp):
    return self.visit_any(tp)

  def visit_class(self, tp):
    return self.visit_any(tp)


class ContainsVisitor(Visitor):
  """Visitor which sets self.found if self.predicate returns true for a type."""

  def __init__(self, predicate):
    self.predicate = predicate
    self.found = False

  def visit_any(self, tp):
    if self.predicate(tp):
      self.found = True
    return tp


class RemoveConstantsVisitor(Visitor):
  """Replace constants with their type."""

  def visit_constant(self, tp):
    return tp.value_type


class SubstVisitor(Visitor):
  """Substitute types for variables based on the given mapping."""

  def __init__(self, mapping):
    self.mapping = mapping

  def visit_variable(self, tp):
    return self.mapping.get(tp, tp)


class Type(object):
  """A type in the python type system.
  """

  def __init__(self, vm, name=None):
    self.vm = vm
    self.name = name

  def add_name(self, name):
    if self.name:
      if name not in self.name:
        # don't add names that are substrings. It's a hack. But it works.
        self.name += "$" + name
    else:
      self.name = name

  @property
  def constraint_store(self):
    return self.vm.constraints

  def join(self, other):
    if isinstance(other, (Object, Nothing, Dynamic)):
      return other.join(self)
    elif isinstance(other, ConstantType):
      return self.join(other.value_type)
    elif isinstance(other, Variable):
      return self.constraint_store.new_variable_supertype(other, self)
    else:
      raise TypeError("self: {} of type {}, other: {} of type {}"
                      .format(self, self.__class__,
                              other, other.__class__))

  def meet(self, other):
    if isinstance(other, (Object, Nothing, Dynamic)):
      return other.meet(self)
    elif isinstance(other, ConstantType):
      return self.meet(other.value_type)
    elif isinstance(other, Variable):
      return self.constraint_store.new_variable_subtype(other, self)
    else:
      raise TypeError("self: {} of type {}, other: {} of type {}"
                      .format(self, self.__class__,
                              other, other.__class__))

  def issubtypeof(self, other):
    if self == other:
      return True
    elif isinstance(other, Object):
      return True
    elif isinstance(other, Nothing):
      return False
    elif isinstance(other, Dynamic):
      return False
    elif isinstance(other, ConstantType):
      return self.issubtypeof(other.value_type)
    elif isinstance(other, Union):
      return other.issupertypeof(self)
    else:
      raise TypeError("self: {} of type {}, other: {} of type {}"
                      .format(self, self.__class__,
                              other, other.__class__))

  def issupertypeof(self, other):
    return other.issubtypeof(self)

  def getattr(self, attr):
    raise AttributeError(attr)

  def substitute(self, mapping):
    return self.visit(SubstVisitor(mapping))

  def remove_constants(self):
    return self.visit(RemoveConstantsVisitor())

  def contains_variable(self):
    visitor = ContainsVisitor(lambda tp: isinstance(tp, Variable))
    self.visit(visitor)
    return visitor.found

  def __contains__(self, other):
    visitor = ContainsVisitor(lambda tp: tp == other)
    self.visit(visitor)
    return visitor.found

  def __ne__(self, other):
    return not self == other


def join_seq(*seq):
  """Join all arguments.

  Args:
    *seq: A sequence of Types.
  Returns:
    The joined Type.
  """
  res = Nothing(None)
  for ty in seq:
    res = res.join(ty)
  return res


def meet_seq(*seq):
  """Meet all arguments.

  Args:
    *seq: A sequence of Types.
  Returns:
    The meeted Type.
  """
  res = Object(None)
  for ty in seq:
    res = res.meet(ty)
  return res


class Object(Type):
  """Object represents the top of the lattice."""

  def join(self, other):
    return self

  def meet(self, other):
    return other

  def issubtypeof(self, other):
    return False

  def issupertypeof(self, other):
    return True

  def __repr__(self):
    return "object"

  def __hash__(self):
    return hash(Object)

  def __eq__(self, other):
    if isinstance(other, Object):
      return True
    return False

  def visit(self, visitor):
    if hasattr(visitor, "visit_object"):
      return visitor.visit_object(self)
    else:
      return self


class Nothing(Type):
  """Object represents the uninhabited bottom of the lattice."""

  def join(self, other):
    return other

  def meet(self, other):
    return self

  def issubtypeof(self, other):
    return True

  def issupertypeof(self, other):
    return False

  def getattr(self, attr):
    return Nothing(self.vm)

  def __repr__(self):
    return "nothing"

  def __hash__(self):
    return hash(Nothing)

  def __eq__(self, other):
    if isinstance(other, Nothing):
      return True
    return False

  def visit(self, visitor):
    if hasattr(visitor, "visit_nothing"):
      return visitor.visit_nothing(self)
    else:
      return self


class Dynamic(Type):
  """A type we assume has potential for runtime errors.

  This is not really part of the lattice. It is not a supertype or subtype of
  anything and both join and meet always return Dynamic.
  """

  def join(self, other):
    return self

  def meet(self, other):
    return self

  def issubtypeof(self, other):
    return False

  def issupertypeof(self, other):
    return False

  def getattr(self, attr):
    return Dynamic(self.vm)

  def __repr__(self):
    return "dynamic"

  def __hash__(self):
    return hash(Dynamic)

  def __eq__(self, other):
    if isinstance(other, Dynamic):
      return True
    return False

  def visit(self, visitor):
    if hasattr(visitor, "visit_dynamic"):
      return visitor.visit_dynamic(self)
    else:
      return self


class Union(Type):
  """Union based on a set of specific subtypes."""

  @classmethod
  def _flatten_subtypes(cls, subtypes):
    subtype_set = set()
    # TODO(ampere): Filter out types that are subsumed by other types.
    for ty in subtypes:
      if isinstance(ty, Union):
        subtype_set |= ty.subtypes
      else:
        subtype_set.add(ty)
    return frozenset(subtype_set)

  def __new__(cls, subtypes, vm):
    subtype_set = cls._flatten_subtypes(subtypes)
    if len(subtype_set) == 1:
      ty, = subtype_set
      return ty
    elif not subtype_set:
      return Nothing(vm)
    else:
      return super(Union, cls).__new__(cls, subtype_set, vm)

  def __init__(self, _subtypes, vm):
    super(Union, self).__init__(vm)
    subtype_set = self._flatten_subtypes(_subtypes)
    assert subtype_set
    self.subtypes = subtype_set

  def join(self, other):
    if isinstance(other, Union):
      subtypes = self.subtypes | other.subtypes
      return Union(subtypes, self.vm)
    elif isinstance(other, Function) or isinstance(other, Instance):
      subtypes = self.subtypes | set([other])
      return Union(subtypes, self.vm)
    else:
      return super(Union, self).join(other)

  def meet(self, other):
    if isinstance(other, Union):
      subtypes = self.subtypes & other.subtypes
      return Union(subtypes, self.vm)
    elif isinstance(other, Function) or isinstance(other, Instance):
      subtypes = self.subtypes & set([other])
      if subtypes:
        return Union(subtypes, self.vm)
      else:
        return self.constraint_store.new_variable_subtype(other, self)
    else:
      return super(Union, self).meet(other)

  def issubtypeof(self, other):
    others = other.subtypes if isinstance(other, Union) else [other]
    return all(any(t.issubtypeof(o) for o in others) for t in self.subtypes)

  def issupertypeof(self, other):
    others = other.subtypes if isinstance(other, Union) else [other]
    return all(any(t.issubtypeof(o) for o in self.subtypes) for t in others)

  def getattr(self, attr):
    return Union([t.getattr(attr) for t in self.subtypes], self.vm)

  def __repr__(self):
    return "U({})".format(", ".join(repr(t) for t in self.subtypes))

  def __hash__(self):
    return hash(self.subtypes)

  def __eq__(self, other):
    if isinstance(other, Union):
      return self.subtypes == other.subtypes
    return False

  def visit(self, visitor):
    result = Union([t.visit(visitor) for t in self.subtypes],
                   self.vm)
    if hasattr(visitor, "visit_union"):
      return visitor.visit_union(result)
    else:
      return result


class Function(Type):
  """The type of Functions."""

  def __init__(self, argument_types, return_type, vm, name=None):
    super(Function, self).__init__(vm, name)
    # TODO(ampere): Add support for variadic and keyword arguments
    self.argument_types = tuple(argument_types)
    self.return_type = return_type

  def join(self, other):
    if (isinstance(other, Function) and
        len(other.argument_types) == len(self.argument_types)):
      arguments = tuple(a.meet(b)
                        for a, b in zip(other.argument_types,
                                        self.argument_types))
      ret_type = self.return_type.join(other.return_type)
      return Function(arguments, ret_type, self.vm)
    elif isinstance(other, Function):
      # TODO(ampere): Fix this when variadic functions are implemented.
      return Object(self.vm)
    elif isinstance(other, Union):
      return other.join(self)
    else:
      return super(Function, self).join(other)

  def meet(self, other):
    if (isinstance(other, Function) and
        len(other.argument_types) == len(self.argument_types)):
      arguments = tuple(a.join(b)
                        for a, b in zip(other.argument_types,
                                        self.argument_types))
      ret_type = self.return_type.meet(other.return_type)
      return Function(arguments, ret_type, self.vm)
    elif isinstance(other, Union):
      return other.meet(self)
    elif isinstance(other, Function):
      # TODO(ampere): Fix this when variadic functions are implemented.
      return Nothing(self.vm)
    else:
      return super(Function, self).meet(other)

  def issubtypeof(self, other):
    if (isinstance(other, Function) and
        len(other.argument_types) == len(self.argument_types)):
      return (all(b.issubtypeof(a)
                  for a, b in zip(self.argument_types,
                                  other.argument_types)) and
              self.return_type.issubtypeof(other.return_type))
    elif isinstance(other, Function):
      # TODO(ampere): Fix this when variadic functions are implemented.
      return False
    elif isinstance(other, Instance):
      return False
    else:
      return super(Function, self).issubtypeof(other)

  def __repr__(self):
    return "{}({}) -> {}".format(
        self.name or "",
        ", ".join(repr(t) for t in self.argument_types),
        repr(self.return_type))

  def __hash__(self):
    return hash(self.argument_types) ^ hash(self.return_type)

  def __eq__(self, other):
    if isinstance(other, Function):
      return (self.argument_types == other.argument_types and
              self.return_type == other.return_type)
    return False

  def visit(self, visitor):
    result = Function((t.visit(visitor) for t in self.argument_types),
                      self.return_type.visit(visitor),
                      self.vm, name=self.name)
    if hasattr(visitor, "visit_function"):
      return visitor.visit_function(result)
    else:
      return result


def visit_dict_values(d, visitor):
  new = {k: t.visit(visitor)
         for k, t in d.iteritems()}
  if new == d: new = d
  return new


# class BoundFunction(Function):
#   def __init__(self, self_type, argument_types, return_type, vm, name=None):
#     super(BoundFunction, self).__init__(argument_types, return_type, vm, name)
#     self.self_type = self_type


class Class(collections.namedtuple("ClassBase", ["class_members",
                                                 "instance_members",
                                                 "name"])):
  """Represents a class (not the type associated with it).

  Attributes:
    instance_members: A dict of members that instances have.
    class_members: A dict of members that the class has.
    name: The classes name.
  """

  def __new__(cls, class_members, instance_members, name):
    return super(Class, cls).__new__(cls, class_members, instance_members, name)

  def __init__(self, class_members, instance_members, name):
    super(Class, self).__init__(class_members, instance_members, name)

  def __repr__(self):
    if self.name:
      return "C<{}>".format(self.name)
    else:
      return "C<{}, {}>".format(self.class_members,
                                self.instance_members)

  def __hash__(self):
    return hash(self.name)

  def __eq__(self, other):
    if isinstance(other, Class):
      # We cannot compare member types here because that would create cycles in
      # the comparison.
      return self is other or (
          self.name == other.name and
          self.class_members.values() == other.class_members.values() and
          self.instance_members.values() == other.instance_members.values())
    return False

  def visit(self, visitor):
    result = Class(visit_dict_values(self.class_members, visitor),
                   visit_dict_values(self.instance_members, visitor),
                   self.name)
    if result == self: result = self
    if hasattr(visitor, "visit_class"):
      return visitor.visit_class(result)
    else:
      return result


class MRO(object):
  """Represents the MRO of an instance.

  An MRO instance is shared by all instance of a given Instance type. This
  allows the MRO to be filled in later for cyclical references. It can only be
  set once.
  """

  def __init__(self, classes, name=None):
    if classes is not None:
      self._classes = tuple(classes)
    else:
      self._classes = None
    self.name = name

  @property
  def classes(self):
    if self._classes is not None:
      return self._classes
    else:
      raise ValueError("MRO classes are not yet set")

  @classes.setter
  def classes(self, classes):
    if self._classes is None:
      assert all(isinstance(c, Class) for c in classes), [(c, c.__class__)
                                                          for c in classes]
      self._classes = tuple(classes)
    else:
      raise ValueError("MRO classes are already set")

  def __hash__(self):
    return hash(self._classes)

  def __eq__(self, other):
    if isinstance(other, MRO):
      # pylint: disable=protected-access
      return self is other or self._classes == other._classes
    return False

  def __iter__(self):
    return iter(self.classes)

  def __getitem__(self, index):
    return self.classes[index]

  def __len__(self):
    return len(self.classes)

  def __reversed__(self):
    return reversed(self.classes)


class ClassConstructor(Function):
  """A class constructor function."""

  def __init__(self, mro, vm):
    thiscls = mro[0]
    init = None
    for cls in mro:
      if "__init__" in cls.class_members:
        init = cls.class_members["__init__"]
        break
    assert init
    tp = Instance(mro, {}, vm, thiscls.name)
    super(ClassConstructor, self).__init__(init.argument_types[1:], tp,
                                           vm, thiscls.name)
    self.mro = mro
    self.cls = thiscls

  # TODO(ampere): Should this be converted to a constructor that just builds a
  # Function instance.


def merge_mros(*seqs):
  """Merge a sequence of MROs into a single resulting MRO.

  This code is copied from the following URL with print statments removed.
  https://www.python.org/download/releases/2.3/mro/

  Args:
    *seqs: A sequence of MROs.
  Returns:
    An MRO which is the merge of the given MROs.
  Raises:
    TypeError: If the merge is impossible.
  """
  seqs = [list(s) for s in seqs]
  res = []
  while True:
    nonemptyseqs = [seq for seq in seqs if seq]
    if not nonemptyseqs:
      return MRO(res)
    for seq in nonemptyseqs:  # find merge candidates among seq heads
      cand = seq[0]
      nothead = [s for s in nonemptyseqs if cand in s[1:]]
      if nothead:
        cand = None  # reject candidate
      else:
        break
    if not cand:
      raise TypeError("Illegal inheritance.")
    res.append(cand)
    for seq in nonemptyseqs:  # remove candidate
      if seq[0] == cand:
        del seq[0]


def dict_meet(*dicts):
  ret = {}
  for name in set(n for d in dicts for n in d.iterkeys()):
    types = [d[name] for d in dicts
             if name in d]
    ret[name] = meet_seq(*types)
  return ret


def dict_is_subtype(sub_dict, super_dict):
  for name, sub_type in sub_dict.iteritems():
    if name not in super_dict:
      return False
    super_type = super_dict[name]
    if not sub_type.issubtypeof(super_type):
      return False
  return True


def mro_to_structure(mro, overrides=None):
  ret = {}
  for cls in reversed(mro):
    ret.update(cls.class_members)
    ret.update(cls.instance_members)
  ret.update(overrides or {})
  return ret


def is_subsequence(left, right):
  """Return true if left is a subsequence of right."""
  left_iter = iter(left)
  right_iter = iter(right)
  try:
    while True:
      item = next(left_iter)
      try:
        while next(right_iter) != item:
          pass
      except StopIteration:
        return False
  except StopIteration:
    return True
  raise NotImplementedError("Should never reach here")


def bind_self(tp):
  # TODO(ampere): We need to give the call some information about the self type.
  if isinstance(tp, Function):
    return Function(tp.argument_types[1:], tp.return_type, tp.vm)
  else:
    return tp


def longest_common_subsequence(seq1, seq2):
  """Compute the longest common subsequence of two sequences.

  Args:
    seq1: A sequence of equality comparable objects
    seq2: See seq1
  Returns:
    A triple of an LCS, the element in seq1 that were not used, and the
    elements in seq2 that were not used.
  """
  table = [[0 for _ in range(len(seq2) + 1)] for _ in range(len(seq1) + 1)]
  # Fill the table
  for i, v1 in enumerate(seq1, start=1):
    for j, v2 in enumerate(seq2, start=1):
      if v1 == v2:
        table[i][j] = table[i - 1][j - 1] + 1
      else:
        table[i][j] = max(table[i - 1][j], table[i][j - 1])
  # Now read out the actual LCS and removed elements
  # These lists are generated backwards and then reversed
  lcs = []
  lost1 = []
  lost2 = []
  i = len(seq1) - 1
  j = len(seq2) - 1
  while i >= 0 and j >= 0:
    if seq1[i] == seq2[j]:
      lcs.append(seq1[i])
      i -= 1
      j -= 1
    else:
      if table[i][j - 1] > table[i - 1][j]:
        lost2.append(seq2[j])
        j -= 1
      else:
        lost1.append(seq1[i])
        i -= 1
  return reversed(lcs), reversed(lost1), reversed(lost2)


def dict_join(dict1, dict2):
  return {name: dict1[name].join(dict2[name])
          for name in dict1
          if name in dict2}


class Instance(Type):
  """The type of class instances."""

  def __init__(self, mro, other_members, vm, name=None):
    super(Instance, self).__init__(vm, name)
    assert isinstance(mro, MRO)
    self.mro = mro
    assert all(isinstance(v, Type) for v in other_members.values())
    self.other_members = other_members

  def join(self, other):
    if isinstance(other, Instance):
      mro, self_ignored, other_ignored = longest_common_subsequence(self.mro,
                                                                    other.mro)
      members = dict_join(
          mro_to_structure(list(self_ignored), overrides=self.other_members),
          mro_to_structure(list(other_ignored), overrides=other.other_members))
      return Instance(MRO(mro), members, self.vm)
    elif isinstance(other, Union):
      return other.join(self)
    elif isinstance(other, Function):
      # TODO(ampere): Change when __call__ is implemented.
      return Object(self.vm)
    else:
      return super(Instance, self).join(other)

  def meet(self, other):
    if isinstance(other, Instance):
      mro = merge_mros(self.mro, other.mro)
      members = dict_meet(self.other_members, other.other_members)
      return Instance(mro, members, self.vm)
    elif isinstance(other, Union):
      return other.meet(self)
    elif isinstance(other, Function):
      # TODO(ampere): Change when __call__ is implemented.
      return Nothing(self.vm)
    else:
      return super(Instance, self).meet(other)

  def issubtypeof(self, other):
    if isinstance(other, Instance):
      return (is_subsequence(other.mro, self.mro) and
              dict_is_subtype(self.other_members, other.get_structure()))
    elif isinstance(other, Function):
      # TODO(ampere): Change when __call__ is implemented.
      return False
    else:
      return super(Instance, self).issubtypeof(other)

  def get_structure(self):
    struct = mro_to_structure(self.mro)
    struct.update(self.other_members)
    return struct

  def getattr(self, attr):
    if attr in self.other_members:
      return self.other_members[attr]
    for cls in self.mro:
      if attr in cls.class_members:
        # TODO(ampere): Handle method wrapping.
        return bind_self(cls.class_members[attr])
      elif attr in cls.instance_members:
        return cls.instance_members[attr]
    # raise AttributeError(attr)
    return self.constraint_store.new_variable()

  def __repr__(self):
    if self.name:
      return self.name
    return "{}<({}), {}>".format(self.name or "I",
                                 ", ".join(repr(t) for t in self.mro),
                                 repr(self.other_members))

  def __hash__(self):
    return hash(tuple(self.other_members.items())) ^  hash(self.name)

  def __eq__(self, other):
    if isinstance(other, Instance):
      return (self.mro == other.mro and
              self.other_members == other.other_members)
    return False

  def visit(self, visitor):
    # We could also visit elements of the MRO, but this makes the traversal
    # cyclic: MRO([c.visit(visitor) for c in self.mro], self.mro.name)
    result = Instance(self.mro,
                      visit_dict_values(self.other_members, visitor),
                      self.vm, name=self.name)
    if hasattr(visitor, "visit_instance"):
      return visitor.visit_instance(result)
    else:
      return result


class ConstantType(Type):
  """Singleton types used for the type of known constant values.

  This has a value and a type. The type is always a super type of this constant
  type.
  """

  def __init__(self, values, vm, with_type=None):
    super(ConstantType, self).__init__(vm)
    # TODO(ampere): Reduce to a normal type if the list is too long.
    self.value_type = join_seq(*([with_type or Nothing(vm)] +
                                 [vm.type_map[v.__class__]
                                  for v in values
                                  if v.__class__ in vm.type_map]))
    self.values = frozenset(values)

  def get_single_value(self):
    ret, = self.values
    return ret

  def join(self, other):
    if isinstance(other, ConstantType):
      values = self.values | other.values
      return ConstantType(values, self.vm)
    else:
      return self.value_type.join(other)

  def meet(self, other):
    if isinstance(other, ConstantType):
      values = self.values & other.values
      if values:
        return ConstantType(values, self.vm)
      else:
        return self.value_type.meet(other.value_type)
    else:
      return self.value_type.meet(other)

  def issubtypeof(self, other):
    if isinstance(other, ConstantType):
      return (self.values.issubset(other.values) and
              self.value_type.issubtypeof(other.value_type))
    else:
      return self.value_type.issubtypeof(other)

  def getattr(self, attr):
    values = [getattr(v, attr)
              for v in self.values
              if hasattr(v, attr)]
    tp = self.value_type.getattr(attr)
    if values:
      return ConstantType(values, self.vm, tp)
    else:
      # If we could not find any constant values for attribute then just return
      # the type it should have based on the type of the constants.
      return tp

  def __repr__(self):
    return "`{}`({})".format(repr(self.value_type),
                             ",".join(repr(v) for v in self.values))

  def __hash__(self):
    return hash(self.value_type)

  def __eq__(self, other):
    if isinstance(other, ConstantType):
      return (self.value_type == other.value_type and
              self.values == other.values)
    return False

  def visit(self, visitor):
    if hasattr(visitor, "visit_constant"):
      return visitor.visit_constant(self)
    else:
      return self


class Variable(Type):
  """A type variable with an identity."""

  next_identity = 1

  def __init__(self, vm, name=None):
    super(Variable, self).__init__(vm, name)
    self.identity = Variable.next_identity
    Variable.next_identity += 1
    self.attributes = {}

  def getattr(self, attr):
    if attr in self.attributes:
      val = self.attributes[attr]
    else:
      val = self.constraint_store.new_variable()
      self.attributes[attr] = val
    return val

  def join(self, other):
    return self.constraint_store.new_variable_supertype(other, self)

  def meet(self, other):
    return self.constraint_store.new_variable_subtype(other, self)

  def __repr__(self):
    if self.name:
      return "T{identity}({name})".format(**self.__dict__)
    else:
      return "T{identity}".format(**self.__dict__)

  def __hash__(self):
    return hash(self.identity)

  def __eq__(self, other):
    if isinstance(other, Variable):
      return self.identity == other.identity
    return False

  def visit(self, visitor):
    if hasattr(visitor, "visit_variable"):
      return visitor.visit_variable(self)
    else:
      return self
