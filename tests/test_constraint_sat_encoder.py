"""Test the constraintvm and try to solve constraints.
"""

import logging
import sys
import textwrap
import unittest


from byterun.constraint import constraintvm
from byterun.constraint import sat_encoder
from byterun.constraint import types

log = logging.getLogger(__name__)

# To allow method names to be consistent with the rest of the project.
# pylint: disable=invalid-name

# TODO(ampere): The tests here are very rough sanity checks. They should be
#               improved once it's clear what the results should really be.


class ConstraintTest(unittest.TestCase):

  def setUp(self):
    self.any_type = types.Object(None)
    self.any_type_contravariant = types.Nothing(None)
    self.vm = constraintvm.ConstraintVirtualMachine()
    self.int_type = self.vm.type_map[int]
    self.float_type = self.vm.type_map[float]
    self.object_type = self.vm.type_map[object]

  def generate_constraints(self, src):
    vm = self.vm
    src = textwrap.dedent(src)
    if isinstance(src, str):
      vm.run_code(compile(src, "<>", "exec", 0, 1))
    else:
      vm.run_code(src)
    vm.constraints.eliminate_equality_constrained_variables()
    vm.constraints.remove_constants()
    print "=== source ==="
    print src
    print "=== targets ==="
    print "\n".join(repr(c) for c in vm.constraints.target_types)
    print "=== constraints ==="
    print "\n".join(repr(c) for c in vm.constraints)
    sys.stdout.flush()
    self.constraints = vm.constraints
    return vm.constraints

  def solve_constriants(self):
    sat = sat_encoder.SatEncoder()
    sat.Generate(self.constraints)
    results = sat.Solve()
    print "=== results ==="
    print "\n\n".join(repr(c) for c in results.iteritems())
    print "==============="
    sys.stdout.flush()
    self.assertTrue(results)
    self.results = results
    return results

  def find_type(self, name):
    for ty in self.constraints.target_types:
      if ty.name == name:
        return ty
    self.fail("Could not find expected type named: {}".format(name))

  def testSimpleFunctionPyTD(self):
    self.generate_constraints("""
      def f(y):
        return 1 + y
    """)
    self.solve_constriants()
    self.assertEquals(self.results[self.find_type("f").return_type][0],
                      self.int_type)
    self.assertEquals(self.results[self.find_type("f").argument_types[0]][1],
                      self.int_type)

  def testSimpleFunction(self):
    self.generate_constraints("""
      def f(y):
        return y + 1
    """)
    self.solve_constriants()

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
    self.solve_constriants()

  def testRelatedFunctions(self):
    self.generate_constraints("""
      def g(y):
        return y + 1

      def f(x):
        return 1.3 + g(x)

      def h(y, z):
        return f(z) + g(y)
     """)
    self.solve_constriants()


if __name__ == "__main__":
  if len(sys.argv) > 1:
    logging.basicConfig(level=logging.INFO)
  unittest.main()
