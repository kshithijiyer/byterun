"""Tests for constraint/pytd.py."""

import unittest


from byterun.constraint import pytd


class PyTDTest(unittest.TestCase):

  def setUp(self):
    self.vm = None
    self.builtins = pytd.load_builtins(self.vm)

  def testInt(self):
    """Test int in builtins and by extension almost all the buildin load code.
    """
    self.assertEqual(self.builtins["int"].name, "int")
    self.assertEqual(self.builtins["int"].mro[0].name, "int")
    self.assertEqual(
        self.builtins["int"].get_structure()["__add__"].argument_types,
        (self.builtins["object"], self.builtins["int"]))
    self.assertEqual(
        self.builtins["int"].get_structure()["__add__"].return_type,
        self.builtins["int"])

if __name__ == "__main__":
  unittest.main()
