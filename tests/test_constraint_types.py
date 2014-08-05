"""Tests for constraint/types.py."""

import unittest


from byterun.constraint import types


class TypesTest(unittest.TestCase):

  def setUp(self):
    self.vm = None
    self.cls_a = types.Class({}, {}, "A")
    self.ty_a = types.Instance(types.MRO((self.cls_a,)),
                               {}, self.vm, "A")

    self.cls_b = types.Class({"a": self.ty_a}, {}, "B")
    self.cls_c = types.Class({}, {}, "C")
    self.cls_d = types.Class({}, {}, "D")
    self.ty_b = types.Instance(types.MRO((self.cls_b,)),
                               {}, self.vm, "B")
    self.ty_c = types.Instance(types.MRO((self.cls_c, self.cls_b)),
                               {}, self.vm, "C")
    self.ty_d = types.Instance(types.MRO((self.cls_d, self.cls_b)),
                               {}, self.vm, "D")

  def testInstanceMROs(self):
    self.assertTrue(self.ty_c.issubtypeof(self.ty_b))
    self.assertFalse(self.ty_a.issubtypeof(self.ty_b))
    self.assertFalse(self.ty_a.issubtypeof(self.ty_c))
    self.assertFalse(self.ty_b.issubtypeof(self.ty_c))
    self.assertFalse(self.ty_c.issubtypeof(self.ty_a))

  def testInstanceSubtyping(self):
    self.assertTrue(
        self.ty_d.issubtypeof(
            types.Instance(types.MRO(()), {"a": self.ty_a}, self.vm)))

  def testUnionTypeSubtyping(self):
    self.assertTrue(
        self.ty_c.issubtypeof(
            types.Union((self.ty_b, self.ty_a), self.vm)))
    self.assertTrue(
        types.Union((self.ty_c, self.ty_d), self.vm).issubtypeof(
            self.ty_b))
    self.assertTrue(
        types.Union((self.ty_c, self.ty_d), self.vm).issubtypeof(
            types.Union((self.ty_b, self.ty_a), self.vm)))

  def testUnionTypeJoin(self):
    self.assertEqual(
        self.ty_c.join(
            types.Union((self.ty_d, self.ty_a), self.vm)),
        types.Union((self.ty_d, self.ty_a, self.ty_c), self.vm))
    self.assertEqual(
        types.Union((self.ty_d, self.ty_a), self.vm).join(self.ty_c),
        types.Union((self.ty_d, self.ty_a, self.ty_c), self.vm))
    self.assertEqual(
        types.Union((self.ty_d, self.ty_a), self.vm).join(
            types.Union((self.ty_b, self.ty_c), self.vm)),
        types.Union((self.ty_d, self.ty_a, self.ty_c, self.ty_b), self.vm))

  def testUnionTypeMeet(self):
    self.assertEqual(
        self.ty_c.meet(
            types.Union((self.ty_c, self.ty_a), self.vm)),
        self.ty_c)
    self.assertEqual(
        types.Union((self.ty_d, self.ty_a), self.vm).meet(
            types.Union((self.ty_a, self.ty_c, self.ty_d), self.vm)),
        types.Union((self.ty_d, self.ty_a), self.vm))

  def testUnionTypeSimpification(self):
    self.assertIs(types.Union((self.ty_b,), self.vm),
                  self.ty_b)
    self.assertIs(types.Union((self.ty_b, self.ty_b), self.vm),
                  self.ty_b)
    self.assertEqual(
        types.Union((self.ty_b, types.Union((self.ty_b, self.ty_a), self.vm),
                     self.ty_c), self.vm),
        types.Union((self.ty_b, self.ty_a, self.ty_c), self.vm))
    self.assertEqual(types.Union((), self.vm),
                     types.Nothing(self.vm))

  def testFunctionTypeSubtyping(self):
    self.assertTrue(
        types.Function((self.ty_a,), self.ty_c, self.vm).issubtypeof(
            types.Function((self.ty_a,), self.ty_b, self.vm)))
    self.assertTrue(
        types.Function((self.ty_b,), self.ty_a, self.vm).issubtypeof(
            types.Function((self.ty_c,), self.ty_a, self.vm)))
    self.assertTrue(
        types.Function((self.ty_b,), self.ty_c, self.vm).issubtypeof(
            types.Function((self.ty_c,), self.ty_b, self.vm)))
    self.assertFalse(
        types.Function((self.ty_c,), self.ty_a, self.vm).issubtypeof(
            types.Function((self.ty_b,), self.ty_a, self.vm)))
    self.assertFalse(
        types.Function((self.ty_a,), self.ty_b, self.vm).issubtypeof(
            types.Function((self.ty_a,), self.ty_c, self.vm)))

  def testFunctionTypeJoinMeet(self):
    self.assertEqual(
        types.Function((self.ty_a,), self.ty_c, self.vm).join(
            types.Function((self.ty_a,), self.ty_b, self.vm)),
        types.Function((self.ty_a,), self.ty_b, self.vm))
    self.assertEqual(
        types.Function((self.ty_a,), self.ty_d, self.vm).join(
            types.Function((self.ty_a,), self.ty_c, self.vm)),
        types.Function((self.ty_a,), self.ty_b, self.vm))
    self.assertEqual(
        types.Function((self.ty_a,), self.ty_c, self.vm).meet(
            types.Function((self.ty_a,), self.ty_b, self.vm)),
        types.Function((self.ty_a,), self.ty_c, self.vm))


if __name__ == "__main__":
  unittest.main()
