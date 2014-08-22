"""Provides a very simple dict subtype which can be hashed."""


class HashableDict(dict):
  """A dict subclass that can be hashed.

  Instances should not be modified. Some methods have been overriden to throw
  exceptions to catch common cases.
  """

  def __init__(self, *args, **kws):
    super(HashableDict, self).__init__(*args, **kws)
    self._hash = hash(tuple(sorted(self.items())))

  def __setitem__(self):
    raise TypeError

  def update(self):
    raise TypeError

  def __hash__(self):
    return self._hash
