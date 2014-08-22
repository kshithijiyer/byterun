"""An encoder from subtype constriants to datalog programs."""

import collections
import logging
import os.path
import subprocess
import tempfile


from byterun.constraint import constraint_store
from byterun.constraint import types
from pytypedecl import utils

log = logging.getLogger(__name__)


def get_xsb_binary():
  # TODO(ampere): Implement PATH based search
  return "xsb"


class FindAllTypes(types.Visitor):
  """Visitor which finds all types and member names.

  This visitor maintains a set of types and a set of member names and adds to
  them as it visits types.
  """

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


class PredicateCall(collections.namedtuple("PredicateCall",
                                           ["term", "arguments"])):
  __slots__ = ()

  def __str__(self):
    return "{}({})".format(self.term,
                           ", ".join(str(a) for a in self.arguments))


class PrologList(collections.namedtuple("PrologList",
                                        ["elements"])):
  __slots__ = ()

  def __new__(cls, elements):
    return super(PrologList, cls).__new__(cls, tuple(elements))

  def __str__(self):
    return "[{}]".format(", ".join(str(a) for a in self.elements))


class PrologAtom(collections.namedtuple("PrologAtom",
                                        ["name"])):
  __slots__ = ()

  def __new__(cls, name):
    return super(PrologAtom, cls).__new__(cls, str(name))

  def __str__(self):
    return "'{}'".format(self.name.replace("'", "\""))


class Rule(collections.namedtuple("Rule",
                                  ["head", "body"])):
  __slots__ = ()

  def __str__(self):
    if self.body:
      return "{} :- {},".format(str(self.head),
                                ", ".join(str(a) for a in self.body))
    else:
      return "{}.".format(str(self.head))


class TypeToDatalog(types.Visitor):
  """A visitor that converts types into datalog rules."""

  def __init__(self, encoder):
    super(TypeToDatalog, self).__init__()
    self._encoder = encoder

  def _build_member_tuple(self, structure):
    i = self._encoder.get_type_id(tuple(structure.iteritems()))
    self._encoder.add_rule(PredicateCall("tuple", (i, PrologList(
        self._encoder.get_type_id(structure[name])
        if name in structure else PrologAtom("none")
        for name in self._encoder.names))))
    return i

  def visit_object(self, tp):
    i = self._encoder.get_type_id(tp)
    self._encoder.add_rule(PredicateCall("object", (i,)))
    return tp

  def visit_nothing(self, tp):
    i = self._encoder.get_type_id(tp)
    self._encoder.add_rule(PredicateCall("nothing", (i,)))
    return tp

  def visit_dynamic(self, tp):
    i = self._encoder.get_type_id(tp)
    self._encoder.add_rule(PredicateCall("dynamic_type", (i,)))
    return tp

  def visit_function(self, tp):
    i = self._encoder.get_type_id(tp)
    argid = self._encoder.get_type_id(tp.argument_types)
    self._encoder.add_rule(PredicateCall(
        "tuple", (argid, PrologList(self._encoder.get_type_id(t)
                                    for t in tp.argument_types))))
    self._encoder.add_rule(PredicateCall(
        "function", (i, argid, self._encoder.get_type_id(tp.return_type))))
    return tp

  def visit_mro(self, mro):
    classes = list(
        self._build_member_tuple(cls.class_members)
        for cls in mro.classes)
    last_type = classes.pop()
    types_so_far = []
    while classes:
      this_type = classes.pop()
      types_so_far.insert(0, this_type)
      i = self._encoder.get_type_id(types.MRO([self._encoder.get_type(t)
                                               for t in types_so_far]))
      self._encoder.add_rule(PredicateCall("mro", (i, this_type, last_type)))
      last_type = i
    return last_type

  def visit_instance(self, tp):
    i = self._encoder.get_type_id(tp)
    mroid = self.visit_mro(tp.mro)
    membertuple = self._build_member_tuple(tp.other_members)
    self._encoder.add_rule(PredicateCall("instance", (i, mroid, membertuple)))
    self._build_member_tuple(tp.get_structure())
    return tp

  def visit_union(self, tp):
    subtypes = list(self._encoder.get_type_id(t) for t in tp.subtypes)
    last_type = subtypes.pop()
    types_so_far = set([last_type])
    while subtypes:
      this_type = subtypes.pop()
      types_so_far.add(this_type)
      i = self._encoder.get_type_id(types.Union([self._encoder.get_type(t)
                                                 for t in types_so_far], None))
      self._encoder.add_rule(PredicateCall("union", (i, last_type, this_type)))
      last_type = i
    return tp

  def visit_constant(self, tp):
    return tp.value_type.visit(self)

  def visit_variable(self, tp):
    i = self._encoder.get_type_id(tp)
    self._encoder.add_rule(PredicateCall("variable", (i,)))
    return tp


class DatalogEncoder(object):
  """Encodes a constraint set into a datalog file and solves it."""

  UNINTERESTING_TYPES = frozenset([types.Object(None), types.Nothing(None)])

  def __init__(self):
    self.rules = set()
    self.type_ids = {}
    self.types = {}

  @property
  def sorted_rules(self):
    return sorted(self.rules, key=lambda p: (p[0], len(p[1]), p[1]))

  def get_type_id(self, tp):
    i = self.type_ids.setdefault(tp, PrologAtom(len(self.type_ids)))
    assert i not in self.types or self.types[i] == tp
    self.types[i] = tp
    self.add_rule(PredicateCall("repr", (i, PrologAtom(repr(tp)))))
    return i

  def get_type(self, i):
    return self.types[i]

  def add_rule(self, *terms):
    self.rules.add(Rule(terms[0], tuple(terms[1:])))

  def _convert_type(self, ty):
    ty.visit(TypeToDatalog(self))
    return self.get_type_id(ty)

  def generate(self, constraints, type_processor=None):
    """Given a set of constraints generate datalog rules."""
    constraints.remove_constants()
    constraints.eliminate_equality_constrained_variables()

    self.constraints = constraints

    # Find all the types we need to work with
    all_types = FindAllTypes()
    constraints.visit_all_types(all_types)
    # To find all the types referenced from methods in instance types we do a
    # transitive closure over the structures of the instance types.
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

    self.type_set = frozenset(all_types.types)
    self.names = tuple(sorted(all_types.names))
    del all_types

    log.info("%d types found", len(self.type_set))
    if log.isEnabledFor(logging.DEBUG):
      log.debug("\n                 ".join(repr(c) for c in self.type_set))
    log.info("%d names found", len(self.names))
    if log.isEnabledFor(logging.DEBUG):
      log.debug("\n                 ".join(self.names))

    for ty in self.type_set:
      self._convert_type(ty)
    for left, right in self.constraints.constraints:
      self.add_rule(PredicateCall("subtype", (self._convert_type(left),
                                              self._convert_type(right))))

    log.info("Rules:\n                 %s", "\n                 ".join(
        str(r) for r in self.sorted_rules))

  def _write_datalog(self, fi):
    subtypingfile = utils.GetDataFile("../byterun/constraint/subtyping.pl")
    with open(subtypingfile, "r") as header:
      fi.write(header.read())
    fi.write("\n".join(str(r) for r in self.sorted_rules))
    fi.write("\n\n")

  def dump(self):
    with open("dump.pl", "w") as fi:
      self._write_datalog(fi)
      log.warning("Dumped data log to: %s", fi.name)

  def solve(self):
    """Generate a self contained datalog file and run XSB on it.

    Returns:
      A set of subtype constraints that XSB inferred.
    """
    with tempfile.NamedTemporaryFile(delete=False, mode="wb",
                                     suffix=".pl") as fi:
      self._write_datalog(fi)
      datalogfile = fi.name
    datalogdir, datalogmodulefile = os.path.split(datalogfile)
    datalogmodule, _ = os.path.splitext(datalogmodulefile)
    commandline = [get_xsb_binary(), datalogmodule]
    xsbproc = subprocess.Popen(commandline, cwd=datalogdir,
                               stdout=subprocess.PIPE)
    results = set()
    with xsbproc.stdout as resultstream:
      for line in resultstream:
        if line.startswith("RESULT:"):
          _, subtypeid, supertypeid = line.split()
          results.add(constraint_store.SubtypeConstraint(
              self.get_type(PrologAtom(subtypeid)),
              self.get_type(PrologAtom(supertypeid))))
        else:
          # print(line.strip("\n"))
          pass

    log.info("Results:\n                 %s", "\n                 ".join(
        repr(r) for r in sorted(results)))
    return results
