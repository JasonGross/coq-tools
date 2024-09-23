from .custom_arguments import DEFAULT_LOG

__all__ = ["process_maybe_list"]


def process_maybe_list(ls, log=DEFAULT_LOG):
    if ls is None:
        return tuple()
    if isinstance(ls, str):
        return tuple([ls])
    if isinstance(ls, tuple):
        return ls
    if isinstance(ls, list):
        return tuple(ls)
    log("Unknown type '%s' of list '%s'" % (str(type(ls)), repr(ls)))
    return tuple(ls)
