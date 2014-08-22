"""Tests for the datalog constraint encoder.
"""

import logging
import sys
import textwrap
import unittest


from byterun.constraint import constraintvm
from byterun.constraint import datalog_encoder
from byterun.constraint import types

log = logging.getLogger(__name__)

# To allow method names to be consistent with the rest of the project.
# pylint: disable=invalid-name


class ConstraintTest(unittest.TestCase):

  def setUp(self):
    self.any_type = types.Object(None)
    self.any_type_contravariant = types.Nothing(None)
    self.vm = constraintvm.ConstraintVirtualMachine()
    self.int_type = self.vm.type_map[int]
    self.float_type = self.vm.type_map[float]

  def generate_constraints(self, src):
    vm = self.vm
    src = textwrap.dedent(src)
    if isinstance(src, str):
      vm.run_code(compile(src, "<>", "exec", 0, 1))
    else:
      vm.run_code(src)
    vm.constraints.eliminate_equality_constrained_variables()
    vm.constraints.remove_constants()
    encoder = datalog_encoder.DatalogEncoder()
    encoder.generate(vm.constraints)
    print "=== source ==="
    print src
    print "=== targets ==="
    print "\n".join(repr(c) for c in vm.constraints.target_types)
    print "=== constraints ==="
    print "\n".join(repr(c) for c in vm.constraints)
    self.constraints = vm.constraints
    self.results = encoder.solve()
    self.rules = encoder.rules
    try:
      encoder.dump()
    except IOError:
      pass  # If dump fails it doesn't matter
    self.assertTrue(self.results)
    return vm.constraints

  def assertHasSubtypeConstraint(self, left, right):
    found = False
    for constraint in self.constraints.constraints:
      try:
        if (left.issubtypeof(constraint.left) and
            constraint.right.issubtypeof(right)):
          found = constraint
          break
      except TypeError:
        # TypeError means issubtypeof was called with something it cannot
        # actually determine subtyping on (such as variables)
        pass
    if not found:
      self.fail("Could not find constraint: {} <: {}".format(left, right))
    return found

  def find_type(self, name):
    for ty in self.constraints.target_types:
      if ty.name == name:
        return ty
    self.fail("Could not find expected type named: {}".format(name))

  def testClassAndCalls(self):
    self.generate_constraints("""
      class A(object):
        def __init__(self):
          self.x = 1

        def get_x(self):
          return self.x

        def set_x(self, x):
          self.x = x
      a = A()
      y = a.x
      x1 = a.get_x()
      a.set_x(1.2)
      x2 = a.get_x()
    """)

  def testSimpleClass(self):
    self.generate_constraints("""
      class A(object):
        def __init__(self):
          self.x = 1

        def get_x(self):
          return self.x

        def set_x(self, x):
          self.x = x
    """)

  def testRelatedFunctions(self):
    self.generate_constraints("""
      def g(y):
        return y + 1

      def f(x):
        return 1.3 + g(x)

      def h(y, z):
        return f(z) + g(y)
     """)

  def testSimpleFunctionPyTD(self):
    self.generate_constraints("""
      def f(y):
        return 1 + y
    """)

  def testSimpleFunction(self):
    self.generate_constraints("""
      def f(y):
        return y + 1
    """)


if __name__ == "__main__":
  if len(sys.argv) > 1:
    logging.basicConfig(level=logging.DEBUG)
  unittest.main()
