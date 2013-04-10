
# from http://code.activestate.com/recipes/578231-probably-the-fastest-memoization-decorator-in-the-/

__all__ = ["memoize"]

def memoize(f):
    """ Memoization decorator for a function taking one or more arguments. """
    class memodict(dict):
        def __getitem__(self, *key):
            return dict.__getitem__(self, key)

        def __missing__(self, key):
            ret = self[key] = f(*key)
            return ret

    return memodict().__getitem__
