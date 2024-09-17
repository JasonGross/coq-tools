# from http://code.activestate.com/recipes/578231-probably-the-fastest-memoization-decorator-in-the-/

__all__ = ["memoize"]


def to_immutable(arg):
    """Converts a list or dict to an immutable version of itself."""
    if any(isinstance(arg, ty) for ty in (list, tuple)):
        return tuple(to_immutable(e) for e in arg)
    elif isinstance(arg, dict):
        return tuple((k, to_immutable(arg[k])) for k in sorted(arg.keys()))
    else:
        return arg


def memoize(f):
    """Memoization decorator for a function taking one or more arguments."""

    class memodict(dict):
        def __getitem__(self, *key, **kwkey):
            try:
                return dict.__getitem__(self, (tuple(key), tuple((k, kwkey[k]) for k in sorted(kwkey.keys()))))
            except TypeError:  # TypeError: unhashable type: 'dict'
                immutable_key = to_immutable((key, kwkey))
                if dict.__contains__(self, immutable_key):
                    return dict.__getitem__(self, immutable_key)
                else:
                    self[immutable_key] = ret = f(*key, **kwkey)
                    return ret

        def __missing__(self, key):
            args, kwargs = key
            self[key] = ret = f(*args, **dict(kwargs))
            return ret

    return memodict().__getitem__
