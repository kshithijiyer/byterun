"""An encoder from subtype constriants to SAT problems."""

import collections
import itertools
import logging
import sys


from byterun.constraint import constraint_store
from byterun.constraint import types
from pytypedecl.match import sat_problem

log = logging.getLogger(__name__)


class FindAllTypes(types.Visitor):
  """Visitor which finds all types and member names."""

  def __init__(self):
    self.types = set()
    self.names = set()

  def visit_any(self, tp):
    # log.debug("Found type: %r", tp)
    self.types.add(tp.remove_constants())
    return tp

  def visit_instance(self, tp):
    self.names.update(tp.get_structure().iterkeys())
    return self.visit_any(tp)


class Inequality(collections.namedtuple("Inequality",
                                        ["subtype", "supertype"])):

  def __repr__(self):
    return "[{}<:{}]".format(*self)


class SatEncoder(object):
  """Action class to encode and solve subtype constraint problems using SAT."""

  UNINTERESTING_TYPES = frozenset([types.Object(None), types.Nothing(None)])
  UNINTERESTING_METHODS = frozenset(["__init__", "__new__"])
  ALWAYS_KNOWN = frozenset([types.Object(None), types.Nothing(None),
                            types.Dynamic(None)])

  def __init__(self):
    self.sat = sat_problem.SATProblem(initial_polarity=False)


  def _SatAssign(self, fmt, *args):
    self.sat.Assign(fmt.format(*args), *args)

  def _SatEquals(self, fmt, *args):
    self.sat.Equals(fmt.format(*args), *args)

  def _SatAssignFalse(self, var):
    self.sat.Assign("NOT {}".format(var), var, False)

  def _GenerateKnownRelationships(self, var):
    """Generate relationships on var based on known subtypes.

    If there is a constraint in the constraint set for the pair of types in var
    we force var to be true. If the left and right of var can be compared by
    Type.issubtype then use that to assign var a value.

    Args:
      var: The SAT variable (Inequality) to try to constrain.
    """
    left, right = var
    # Known constriants
    var_as_constraint = constraint_store.SubtypeConstraint(left, right)
    if var_as_constraint in self.constraints.constraints:
      self._SatAssign("Constraint: {}", var, True)
    # Add directly computable subtypes and non-subtypes
    if (not left.contains_variable() and not right.contains_variable() or
        left in self.ALWAYS_KNOWN or right in self.ALWAYS_KNOWN):
      self._SatAssign("Known: {} = {}", var, left.issubtypeof(right))

  def _GenerateInstanceRelationships(self, var):
    """Generate relationships on var based on instance structure.

    For variables that compare instance types we can equate the variable with a
    conjunction that requires every member of the left side to be a subtype of
    the matching member of the right side. If the types are nominally
    incompatible (their MROs don't match) or there are method missing from the
    subtype then we assign the variable to false.

    Args:
      var: The SAT variable (Inequality) to try to constrain.
    """
    left, right = var
    # "Unify" instances if they are in a subtype relations
    if isinstance(left, types.Instance) and isinstance(right, types.Instance):
      if types.is_subsequence(right.mro, left.mro):
        left_struct = left.get_structure()
        right_struct = right.get_structure()
        if frozenset(left_struct.viewkeys()).issuperset(
            right_struct.viewkeys()):
          conj = frozenset(Inequality(left_struct[name], right_struct[name])
                           for name in right_struct
                           if (name not in self.UNINTERESTING_METHODS and
                               left_struct[name] != right_struct[name]))
          value = sat_problem.Conjunction(conj)
          self._SatEquals("{} = {}", var, value)
        else:
          self._SatAssignFalse(var)
      else:
        self._SatAssignFalse(var)

  def _GenerateFunctionRelationships(self, var):
    """Generate relationships on var based on function structure.

    Similar to _GenerateInstanceRelationships.

    If both sides of the variable are functions and they match in arity, then we
    can equate the variable to a conjuction that requires right hand arguments
    to be subtypes of left hand and the left hand return value to be a subtype
    of the right hand. If the arities do not match set the variable to false.

    Args:
      var: The SAT variable (Inequality) to try to constrain.
    """
    left, right = var
    # "Unify" functions if they are in a subtype relations
    if isinstance(left, types.Function) and isinstance(right, types.Function):
      if len(left.argument_types) == len(right.argument_types):
        conj = set(Inequality(c, d)
                   for c, d in zip(right.argument_types, left.argument_types)
                   if c != d)
        if left.return_type != right.return_type:
          conj.add(Inequality(left.return_type, right.return_type))
        value = sat_problem.Conjunction(conj)
        self._SatEquals("{} = {}", var, value)
      else:
        self._SatAssignFalse(var)

  def _GenerateUnionRelationships(self, var):
    """Generate relationships on var if either side is a union.

    If either the left or right is a union, assign the variable equal to a
    conjunction of disjunctions such that every subtype of the left side must be
    a subtype of at least one type on the right side. None unions are treated as
    unions of size 1.

    Args:
      var: The SAT variable (Inequality) to try to constrain.
    """
    left, right = var
    # Equate union comparisons with the comparisons on the subtypes
    if isinstance(left, types.Union) or isinstance(right, types.Union):
      if isinstance(left, types.Union):
        leftsubtypes = left.subtypes
      else:
        leftsubtypes = [left]
      if isinstance(right, types.Union):
        rightsubtypes = right.subtypes
      else:
        rightsubtypes = [right]
      value = sat_problem.Conjunction(
          sat_problem.Disjunction(Inequality(left1, right1)
                                  for right1 in rightsubtypes)
          for left1 in leftsubtypes)
      self._SatEquals("{} = {}", var, value)

  def _GenerateConstraints(self, sat_variables):
    """Generate constraints for all the SAT variables provided."""
    for var in sat_variables:
      # This is not an elif chain because more than one case will often apply
      # and all cases that apply should be used.
      self._GenerateKnownRelationships(var)
      self._GenerateInstanceRelationships(var)
      self._GenerateFunctionRelationships(var)
      self._GenerateUnionRelationships(var)

      left, right = var
      # Handle known incomperable types
      if (isinstance(left, types.Function) and
          isinstance(right, types.Instance) or
          isinstance(right, types.Function) and
          isinstance(left, types.Instance)):
        self._SatAssignFalse(var)
      # TODO(ampere): Are there more cases that need to be handled here?

  def _FindTypes(self, type_processor):
    """Find all the types used by the constraint set.

    Also if type_processor is not None run it on the FindAllTypes visitor to
    allow it to add additional types.

    Also compute the set of member names used in all the types we are using.

    Args:
      type_processor: A function that takes an instance of FindAllTypes and
        examines and adds types to it. This is called just before the results
        are extracted from the instance.
    Returns:
      A pair of a set of types and set of names.
    """
    all_types = FindAllTypes()
    self.constraints.visit_all_types(all_types)
    last_types = None
    while last_types != all_types.types:
      last_types = set(all_types.types)
      for ty in list(all_types.types):
        if hasattr(ty, "get_structure"):
          for tyt in ty.get_structure().itervalues():
            tyt.visit(all_types)

    types.Object(None).visit(all_types)
    types.Nothing(None).visit(all_types)

    if type_processor:
      type_processor(all_types)

    type_set = frozenset(all_types.types)
    name_set = frozenset(all_types.names)
    del all_types

    log.info("%d types found", len(type_set))
    if log.isEnabledFor(logging.DEBUG):
      log.debug("\n".join(repr(c) for c in type_set))
    log.info("%d names found", len(name_set))
    if log.isEnabledFor(logging.DEBUG):
      log.debug("\n".join(name_set))

    return type_set, name_set

  def _GenerateTransitivityConstraints(self, type_set, sat_variables):
    """Generate transitivity constraints for "pivots" that contain variables.

    For example (a<:b & b<:c) ==> a<:c is generated iff b contains variables.

    Args:
      type_set: The set of all types used in the constriants.
      sat_variables: The set of all SAT variables (Inequalities).
    """
    var_types = [t for t in type_set if t.contains_variable()]
    for a in type_set:
      for b in var_types:
        if a == b:
          continue
        for c in type_set:
          if a == c or b == c:
            continue
          eq1 = Inequality(a, b)
          eq2 = Inequality(b, c)
          eq3 = Inequality(a, c)
          assert eq1 in sat_variables
          assert eq2 in sat_variables
          assert eq3 in sat_variables
          self.sat.Implies("Trans: {} & {} ==> {}".format(eq1, eq2, eq3),
                           sat_problem.Conjunction((eq1, eq2)), eq3)

  def _GenerateConcreteSolutionObjective(self, type_set):
    """Generate a linear object prefering at least some concrete relationships.

    The more subtype relationships between types with variables and types
    without variables the better.

    Args:
      type_set: The set of all types used in the constriants.
    """
    var_types = (t for t in type_set if t.contains_variable())
    conc_types = [t for t in type_set
                  if (not t.contains_variable() and
                      t not in [types.Object(None), types.Nothing(None)])]
    for vt in var_types:
      for ct in conc_types:
        self.sat.Prefer(Inequality(vt, ct), True)
        self.sat.Prefer(Inequality(ct, vt), True)

  def Generate(self, constraints, type_processor=None):
    """Generate the constraints from the given classes.

    Args:
      constraints: A constriant store populated with the constraints that need
        solving.
      type_processor: A function that takes an instance of FindAllTypes and
        examines and adds types to it. This is called just before the results
        are extracted from the instance.
    """
    constraints.eliminate_equality_constrained_variables()
    constraints.remove_constants()

    self.constraints = constraints

    type_set, _ = self._FindTypes(type_processor)

    # Generate all the SAT variables (subtype relations)
    sat_variables = frozenset(Inequality(a, b)
                              for a, b in itertools.product(type_set, type_set)
                              if a != b)

    self._GenerateConstraints(sat_variables)

    use_transitivity_constraints = True
    if use_transitivity_constraints:
      self._GenerateTransitivityConstraints(type_set, sat_variables)

    use_concrete_solution_constraints = True
    if use_concrete_solution_constraints:
      self._GenerateConcreteSolutionObjective(type_set)

  def Solve(self):
    """Solve the constraints generated by calls to generate.

    Returns:
      A map from pytd.Class to pytd.Type that had all the incomplete types that
      can been assigned by the solver.
    """
    self.sat.Solve()
    results = {}
    for var, value in self.sat:
      # Log cases where value is True or unknown (None)
      if (value is not False and isinstance(var, Inequality) and
          (var.subtype.contains_variable() or
           var.supertype.contains_variable())):
        log.info("%s = %r", var, value)
      if value and isinstance(var, Inequality):
        if isinstance(var.subtype, types.Variable):
          lower, upper = results.setdefault(var.subtype, (types.Nothing(None),
                                                          types.Object(None)))
          if not var.supertype.contains_variable():
            results[var.subtype] = (lower, upper.meet(var.supertype))
        if isinstance(var.supertype, types.Variable):
          lower, upper = results.setdefault(var.supertype, (types.Nothing(None),
                                                            types.Object(None)))
          if not var.subtype.contains_variable():
            results[var.supertype] = (lower.join(var.subtype), upper)
    return results

  def SolveIterate(self, constraints):
    """Given a set of constraints iteratively generate and solve.

    This repeatedly generates and solves the constraints and at each iteration
    add types based on what was discovered about the type variables in the
    previous iteration.

    Args:
      constraints: A constriant store populated with the constraints that need
        solving.

    Returns:
      A map from pytd.Class to pytd.Type that had all the incomplete types that
      can been assigned by the solver.
    """
    results = {}
    for i in range(2):
      def AddSubst(all_types):
        for ty in list(all_types.types):
          for var, (lower, upper) in results.iteritems():
            if lower not in self.UNINTERESTING_TYPES:
              ty.substitute({var: lower}).visit(all_types)
            if upper not in self.UNINTERESTING_TYPES:
              ty.substitute({var: upper}).visit(all_types)
      self.Generate(constraints, AddSubst)
      results = self.Solve()
      log.info("=== results %d ===", i)
      log.info("%s", "\n\n".join(repr(c) for c in results.iteritems()))
      sys.stdout.flush()
    return results
