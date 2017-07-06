from __future__ import print_function
import os
from coq_version import group_coq_args
from custom_arguments import DEFAULT_LOG, DEFAULT_VERBOSITY

__all__ = ["has_dir_binding", "deduplicate_trailing_dir_bindings", "process_maybe_list"]

def topname_of_filename(file_name):
    return os.path.splitext(os.path.basename(file_name))[0].replace('-', '_DASH_')

def has_dir_binding(args, coqc_help, file_name=None):
    kwargs = dict()
    if file_name is not None: kwargs['topname'] = topname_of_filename(file_name)
    bindings = group_coq_args(args, coqc_help, **kwargs)
    return any(i[0] in ('-R', '-Q') for i in bindings)

def deduplicate_trailing_dir_bindings(args, coqc_help, coq_accepts_top, file_name=None):
    kwargs = dict()
    if file_name is not None: kwargs['topname'] = topname_of_filename(file_name)
    bindings = group_coq_args(args, coqc_help, **kwargs)
    ret = []
    for binding in bindings:
        if coq_accepts_top or binding[0] != '-top':
            ret.extend(binding)
    return tuple(ret)

def process_maybe_list(ls, log=DEFAULT_LOG, verbose=DEFAULT_VERBOSITY):
    if ls is None: return tuple()
    if isinstance(ls, str): return tuple([ls])
    if isinstance(ls, tuple): return ls
    if isinstance(ls, list): return tuple(ls)
    if verbose >= 1: log("Unknown type '%s' of list '%s'" % (str(type(ls)), repr(ls)))
    return tuple(ls)
