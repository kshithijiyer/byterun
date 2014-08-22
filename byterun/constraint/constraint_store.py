"""Tools to store and manipulate constraints on constraint.types objects."""

import collections
import logging


from byterun.constraint import types

log = logging.getLogger(__name__)


class Constraint(collections.namedtuple("ConstraintBase",
                                        ["left", "right"])):
  """The constraint base class.

  Direct use should be of SubtypeConstraint or EqualityConstraint.
  """

  def substitute(self, mapping):
    """Perform a substitution on the types in the constraint.

    Args:
      mapping: A mapping from variables to types.
    Returns:
      A new constraint with the substitutions applied.
    """
    raise NotImplementedError

  def remove_constants(self):
    """Remove any constant types in either type.

    Returns:
      A new constraint with the substitutions applied.
    """
    raise NotImplementedError

  def __contains__(self, ty):
    """Return true if this contains the type 'ty'."""
    if isinstance(ty, types.Type):
      return ty in self.left or ty in self.right
    else:
      raise ValueError

  def substitute(self, mapping):
    return self.__class__(self.left.substitute(mapping),
                          self.right.substitute(mapping))

  def remove_constants(self):
    return self.__class__(self.left.remove_constants(),
                          self.right.remove_constants())


class SubtypeConstraint(Constraint):
  """A constraint in the form a <: b."""

  def __repr__(self):
    return "{: <30} <: {: <50}".format(self.left, self.right)


class EqualityConstraint(Constraint):
  """A constraint in the form a == b."""

  def __repr__(self):
    return "{: <30} == {: <50}".format(self.left, self.right)


class ConstraintStore(object):
  """A mutable set of constraints and operations on that set.
  """

  def __init__(self, vm):
    self.constraints = set()
    self.completed_constraints = set()
    self.target_types = set()
    self.variables = set()
    self.vm = vm

  def _complete_constraint(self, constraint):
    if constraint in self.constraints:
      self.constraints.remove(constraint)
      self.completed_constraints.add(constraint)

  def add_target(self, tp):
    self.target_types.add(tp)

  def new_variable(self):
    var = types.Variable(self.vm)
    self.variables.add(var)
    return var

  def issubtypeof(self, type1, type2):
    """Check if type1 is a subtype of type2.

    This checks for subtyping using an extremely incomplete algorithm, but
    unlike Type.issubtypeof this can handle variables in some cases. In cases
    where subtyping cannot be determined it returns None which allows code that
    does not need to distinguish "not a subtype" for "not known to be a subtype"
    to just use the result as if it were a boolean.

    Args:
      type1: A type.
      type2: Another type.
    Returns:
      True if type1 is a subtype of type2, False if not, and None if the result
      is unknown.
    """
    if not type1.contains_variable() and not type2.contains_variable():
      return type1.issubtypeof(type2)
    else:
      if SubtypeConstraint(type1, type2) in self.constraints:
        return True
      else:
        # Here None means "I don't know" not False. See doc string.
        return None

  def issupertypeof(self, type1, type2):
    return self.issubtypeof(type2, type1)

  def new_variable_supertype(self, sub1, sub2):
    if self.issupertypeof(sub1, sub2):
      return sub1
    elif self.issupertypeof(sub2, sub1):
      return sub2
    else:
      var = self.new_variable()
      self.constrain_supertype(var, sub1)
      self.constrain_supertype(var, sub2)
      return var

  def new_variable_subtype(self, super1, super2=None):
    if self.issubtypeof(super1, super2):
      return super1
    if self.issubtypeof(super2, super1):
      return super2
    else:
      var = self.new_variable()
      self.constrain_subtype(var, super1)
      self.constrain_subtype(var, super2)
      return var

  def constrain_subtype(self, a, b):
    constraint = SubtypeConstraint(a, b)
    if a != b and constraint not in self.constraints:
      log.debug("%r <: %r", a, b)
      self.constraints.add(constraint)
    # if hasattr(a, "add_super_bound"):
    #   a.add_super_bound(b)
    # if hasattr(b, "add_sub_bound"):
    #   b.add_sub_bound(a)

  def constrain_supertype(self, a, b):
    self.constrain_subtype(b, a)

  def constrain_equal(self, a, b):
    constraint = EqualityConstraint(a, b)
    if a != b and constraint not in self.constraints:
      log.debug("%r = %r", a, b)
      self.constraints.add(constraint)

  def __iter__(self):
    return iter(self.constraints)

  def _update_constraints(self, func, complete_constraints=True):
    """Apply a function to each constraint.

    Args:
      func: A function that takes a constraint and return a single constraint or
        a sequence of constraints to replace the one passed in.
      complete_constraints: If true (default), then complete constraints which
        are replaced.
    Returns:
      True if anything was changed.
    """
    orig_constraints = frozenset(self.constraints)
    new_constraints = set()
    # log.info("%r with Constraints:\n%s", func,
    #         "\n".join(repr(c) for c in orig_constraints))
    for constraint in orig_constraints:
      replacement = func(constraint)
      if isinstance(replacement, Constraint):
        new_constraints.add(replacement)
      elif replacement:
        new_constraints.update(replacement)
    self.constraints = new_constraints
    added_constraints = self.constraints - orig_constraints
    removed_constraints = orig_constraints - self.constraints
    if complete_constraints:
      self.completed_constraints.update(removed_constraints)
    return bool(removed_constraints or added_constraints)

  def substitute(self, mapping):
    """Perform a substitution on every constraint in this store."""
    log.info("Applying substitution: %r", mapping)
    def substitute_update(c):
      return c.substitute(mapping)
    new_completed_constraints = set()
    for constraint in self.completed_constraints:
      new_completed_constraints.add(substitute_update(constraint))
    self.completed_constraints = new_completed_constraints
    new_target_types = set()
    for tp in self.target_types:
      new_target_types.add(substitute_update(tp))
    self.target_types = new_target_types
    return self._update_constraints(substitute_update,
                                    complete_constraints=True)

  def remove_constants(self):
    def remove_constants_update(c):
      return c.remove_constants()
    return self._update_constraints(remove_constants_update,
                                    complete_constraints=False)

  def completely_remove_a_sub_a_constraints(self):
    self.completed_constraints = {
        constraint
        for constraint in self.completed_constraints
        if constraint.left != constraint.right}

  def _in_target_types(self, ty):
    return any(ty in t for t in self.target_types)

  def constraints_on_variable(self, var):
    return [c for c in self.constraints
            if var in c]

  # Simplification and Constraint Processing Methods

  #   Most of these methods are not used because they were designed for an ad
  #   hoc constraint solver that did not turn out to work. However some may be
  #   useful for simplification before SAT or SMT encoding or other more
  #   advanced solving techniques, so they are left here for possible later use.

  def unify_subtype_constraint(self, left, right):
    """'Unify' the left and right of a subtype constraint.

    This compares the left and right values and generates constraints on
    subexpressions that are equivalent to replace the original.

    Args:
     left: The subtype of the constraint.
     right: The supertype of the constraint.
    """
    log.info("Unifying subtype constraint: %r <: %r", left, right)
    if (isinstance(left, types.Function) and
        isinstance(right, types.Function) and
        len(left.argument_types) == len(right.argument_types)):
      for la, ra in zip(left.argument_types, right.argument_types):
        self.unify_subtype_constraint(ra, la)
      self.unify_subtype_constraint(left.return_type, right.return_type)
      for c in self.constraints.copy():
        if c.left == left and c.right == right:
          self._complete_constraint(c)
    elif (isinstance(left, types.Instance) and
          isinstance(right, types.Instance) and
          types.is_subsequence(right.mro, left.mro)):
      log.info("Unifying instances")
      # TODO(ampere): Do I need to ignore pairs where the nominals don't
      # subtype?
      super_dict = right.get_structure()
      for name, sub_type in left.other_members.iteritems():
        if name not in super_dict:
          continue
        super_type = super_dict[name]
        self.unify_subtype_constraint(sub_type, super_type)
      for c in self.constraints.copy():
        if c.left == left and c.right == right:
          self._complete_constraint(c)
    else:
      self.constrain_subtype(left, right)

  def unify_subtype_constraints(self):
    orig = frozenset(self.constraints)
    for constraint in orig:
      if isinstance(constraint, SubtypeConstraint):
        self.unify_subtype_constraint(constraint.left, constraint.right)
    return orig != self.constraints

  def eliminate_trivially_super_bounded_variables(self):
    """Replace variables with trivial super bounds with the bound."""
    changed = False
    for var in self.variables:
      constraints_on_var = [
          c for c in self.constraints
          if c.left == var and isinstance(c, SubtypeConstraint)]
      if len(constraints_on_var) == 1:
        changed = True
        self._complete_constraint(constraints_on_var[0])
        replacement = constraints_on_var[0].right
        self.substitute({var: replacement})
    return changed

  def eliminate_variables_by_transitivity(self):
    """Remove variables that only appear as a "bridge" between other types."""
    changed = False
    for var in self.variables:
      constraints_on_var = self.constraints_on_variable(var)
      left_constraints = []
      right_constraints = []
      for constraint in constraints_on_var:
        if constraint.left == var and var not in constraint.right:
          left_constraints.append(constraint)
        elif constraint.right == var and var not in constraint.left:
          right_constraints.append(constraint)
        else:
          left_constraints = right_constraints = None
          break
      if not left_constraints or not right_constraints:
        continue
      for l in left_constraints:
        self._complete_constraint(l)
      for r in right_constraints:
        changed = True
        self._complete_constraint(r)
        for l in left_constraints:
          self.constrain_subtype(r.left, l.right)
    return changed

  def eliminate_equality_constrained_variables(self):
    """Replace variables with what they are constrained equal to."""
    constraints = [c for c in self.constraints
                   if isinstance(c, EqualityConstraint)]
    subst = {}
    for constraint in constraints:
      self._complete_constraint(constraint)
      left, right = constraint
      subst = {l: r.substitute({left: right})
               for l, r in subst.iteritems()}
      if left not in subst:
        subst[left] = right
    self.substitute(subst)
    return bool(constraints)

  def eliminate_trivially_constrained_unused_variables(self):
    """Eliminate variables that are used only once and at the top-level."""
    changed = False
    for var in self.variables:
      constraints_on_var = self.constraints_on_variable(var)
      if len(constraints_on_var) == 1:
        c, = constraints_on_var
        if c.left == var or c.right == var:
          self._complete_constraint(c)
          changed = True
    return changed

  def merge_super_bounds(self):
    """Same as meet_super_bounds but also force variable bounds be equal."""
    orig_variables = frozenset(self.variables)
    orig_constraints = frozenset(self.constraints)
    for var in orig_variables:
      super_bound = types.Object(self.vm)
      for constraint in orig_constraints:
        if (constraint.left == var and
            isinstance(constraint, SubtypeConstraint)):
          if not isinstance(constraint.right, types.Variable):
            super_bound = super_bound.meet(constraint.right)
          else:
            self.constrain_equal(constraint.right, var)
          self._complete_constraint(constraint)
      if not isinstance(super_bound, types.Object):
        self.constrain_subtype(var, super_bound)
    return orig_constraints != self.constraints

  def meet_super_bounds(self):
    """Meet the super bounds of each variable and constrain by the meet only."""
    orig_variables = frozenset(self.variables)
    orig_constraints = frozenset(self.constraints)
    for var in orig_variables:
      super_bound = types.Object(self.vm)
      for constraint in orig_constraints:
        if (constraint.left == var and
            isinstance(constraint, SubtypeConstraint) and
            not isinstance(constraint.right, types.Variable)):
          other = constraint.right
          super_bound = super_bound.meet(other)
          self._complete_constraint(constraint)
      if not isinstance(super_bound, types.Object):
        self.constrain_subtype(var, super_bound)
    return orig_constraints != self.constraints

  def join_sub_bounds(self):
    """Join the sub bounds of each variable and constrain by the join only."""
    orig_variables = frozenset(self.variables)
    orig_constraints = frozenset(self.constraints)
    for var in orig_variables:
      sub_bound = types.Nothing(self.vm)
      for constraint in orig_constraints:
        if (constraint.right == var and
            isinstance(constraint, SubtypeConstraint) and
            not isinstance(constraint.left, types.Variable)):
          other = constraint.left
          sub_bound = sub_bound.join(other)
          self.constraints.discard(constraint)
      if not isinstance(sub_bound, types.Nothing):
        self.constrain_supertype(var, sub_bound)
    return orig_constraints != self.constraints

  def eliminate_known_relations(self):
    """Eliminate constraints that are computable by issubtypeof."""
    def eliminate_known_relations_update(c):
      if not isinstance(c, SubtypeConstraint):
        return c
      if (not c.left.contains_variable() and
          not c.right.contains_variable() and
          c.left.issubtypeof(c.right)):
        return None
      return c
    return self._update_constraints(eliminate_known_relations_update)

  def simplify(self):
    """Run a series of techniques to try to simplify the constraints set.

    This should be sound, but is not complete. The resulting set will give
    solutions for the original, however some solutions for the original may not
    be solutions for the simplified set.
    """
    self.remove_constants()
    self.completely_remove_a_sub_a_constraints()

    while True:  # break on last line of loop
      log.info("Starting with Constraints:\n%s",
               "\n".join(repr(c) for c in self.constraints))

      orig_constraints = frozenset(self.constraints)

      changed = False

      changed |= self.eliminate_equality_constrained_variables()
      changed |= self.eliminate_known_relations()

      changed |= self.meet_super_bounds()
      changed |= self.join_sub_bounds()

      changed |= self.eliminate_trivially_super_bounded_variables()
      changed |= self.eliminate_trivially_constrained_unused_variables()

      changed |= self.unify_subtype_constraints()

      added_constraints = self.constraints - orig_constraints
      removed_constraints = orig_constraints - self.constraints
      if removed_constraints:
        log.info("Removed some constraints.\n%s",
                 "\n".join(repr(c) for c in removed_constraints))
      if added_constraints:
        log.info("Added some constraints.\n%s",
                 "\n".join(repr(c) for c in added_constraints))
      if not (added_constraints or changed):
        break

  def visit_all_types(self, visitor):
    """Run the visitor on all types in this constraint store."""
    for c in self.constraints | self.completed_constraints:
      c.left.visit(visitor)
      c.right.visit(visitor)
    for ty in self.target_types:
      ty.visit(visitor)
