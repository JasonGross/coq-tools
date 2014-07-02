from __future__ import with_statement, print_function
import os, subprocess, re, sys, glob, os.path
from memoize import memoize
from import_util import filename_of_lib, lib_of_filename, get_file, recursively_get_imports

__all__ = ["include_imports"]

file_contents = {}
lib_imports_fast = {}
lib_imports_slow = {}

DEFAULT_VERBOSE=1
DEFAULT_TOPNAME='Top'

IMPORT_LINE_REG = re.compile(r'^\s*(?:Require\s+Import|Require\s+Export|Require|Load\s+Verbose|Load)\s+(.*?)\.(?:\s|$)', re.MULTILINE | re.DOTALL)

def DEFAULT_LOG(text):
    print(text)

def contents_without_imports(lib, verbose=DEFAULT_VERBOSE, log=DEFAULT_LOG, topname=DEFAULT_TOPNAME):
    v_file = filename_of_lib(lib, topname=topname, ext='.v')
    contents = get_file(v_file, verbose=verbose, log=log)
    if '(*' in ' '.join(IMPORT_LINE_REG.findall(contents)):
        print('Warning: There are comments in your Require/Import/Export lines in %s.' % filename)
    return IMPORT_LINE_REG.sub('', contents)

def escape_lib(lib):
    return lib.replace('.', '_DOT_')

def group_by_first_component(lib_libname_pairs):
    rtn = dict((lib.split('.')[0], []) for lib, libname in lib_libname_pairs)
    for lib, libname in lib_libname_pairs:
        split_lib = lib.split('.')
        rtn[split_lib[0]].append(('.'.join(split_lib[1:]), libname))
    return rtn

def nest_iter_up_to(iterator):
    so_far = []
    for i in iterator:
        so_far.append(i)
        yield tuple(so_far)


def construct_import_list(import_libs):
    '''Takes a list of library names, and returns a list of imports in an order that should have modules representing files at the end.'''
    lib_components_list = [(libname, tuple(reversed(list(nest_iter_up_to(libname.split('.')))[:-1])))
                           for libname in import_libs]
    ret = list(map(escape_lib, import_libs))
    lib_components = [(libname, i, max(map(len, lst)) - len(i))
                      for libname, lst in lib_components_list
                      for i in lst]
    for libname, components, components_left in reversed(sorted(lib_components, key=(lambda x: x[2]))):
        ret.append(escape_lib(libname) + '.' + '.'.join(components))
    return ret


def contents_as_module_without_require(lib, other_imports, verbose=DEFAULT_VERBOSE, log=DEFAULT_LOG, topname=DEFAULT_TOPNAME):
    v_name = filename_of_lib(lib, topname=topname, ext='.v')
    contents = get_file(v_name, verbose=verbose, log=log)
    reg1 = re.compile(r'^\s*Require\s+((?:Import|Export)\s)', flags=re.MULTILINE)
    contents = reg1.sub(r'\1', contents)
    reg2 = re.compile(r'^\s*Require\s+((?!Import\s+|Export\s+)(?:[^\.]|\.(?!\s|$))+\.(?:\s|$))', flags=re.MULTILINE)
    contents = reg2.sub(r'', contents)
    if verbose > 2: log(contents)
    module_name = escape_lib(lib)
    # import the top-level wrappers
    if len(other_imports) > 0:
        # we need to import the contents in the correct order.  Namely, if we have a module whose name is also the name of a directory (in the same folder), we want to import the file first.
        for imp in reversed(construct_import_list(other_imports)):
            contents = 'Import %s.\n%s' % (imp, contents)
    # wrap the contents in directory modules
    lib_parts = lib.split('.')
    contents = 'Module %s.\n%s\nEnd %s.\n' % (lib_parts[-1], contents, lib_parts[-1])
    for name in reversed(lib_parts[:-1]):
        contents = 'Module %s.\n%s\nEnd %s.\n' % (name, contents, name) # or Module Export?
    contents = 'Module %s.\n%s\nEnd %s.\n' % (module_name, contents, module_name)
    return contents


def include_imports(filename, as_modules=True, verbose=DEFAULT_VERBOSE, fast=False, log=DEFAULT_LOG, topname=DEFAULT_TOPNAME, coqc='coqc', **kwargs):
    """Return the contents of filename, with any top-level imports inlined.

    If as_modules == True, then the imports will be wrapped in modules.

    This method requires access to the coqdep program if fast == False.
    Without it, it will fall back to manual parsing of the imports,
    which may change behavior.

    >>> import tempfile, os
    >>> f = tempfile.NamedTemporaryFile(dir='.', suffix='.v', delete=False)
    >>> g = tempfile.NamedTemporaryFile(dir='.', suffix='.v', delete=False)
    >>> g_name = os.path.relpath(g.name, '.')[:-2]
    >>> f.write("  Require  Import %s Coq.Init.Logic Arith.\n  Require  Export \tPArith\t Coq.Init.Logic.\n  Require Bool.\n Import Bool. (* asdf *)\n Require Import QArith\n  ZArith\n  Setoid.\nRequire Import %s.\n Require\n  Import\n%s\n\n\t.\t(*foo*)\n\nInductive t := a | b.\n\n(*asdf*)" % (g_name, g_name, g_name))
    >>> g.write(r"Require Export Ascii String.\n\nInductive q := c | d.")
    >>> f.close()
    >>> g.close()
    >>> print(include_imports(f.name, as_modules=False, verbose=False))
    Require Import Coq.Arith.Arith Coq.Bool.Bool Coq.Init.Logic Coq.PArith.PArith Coq.QArith.QArith Coq.Setoids.Setoid Coq.ZArith.ZArith Coq.Strings.Ascii Coq.Strings.String.

    Inductive q := c | d.
    (* asdf *)


    Inductive t := a | b.

    (*asdf*)

    >>> print(include_imports(f.name, as_modules=False, fast=True, verbose=False))
    Require Import Arith Bool Coq.Init.Logic PArith QArith Setoid ZArith Ascii String.

    Inductive q := c | d.
    (* asdf *)


    Inductive t := a | b.

    (*asdf*)
    >>> exts = ('.v', '.v.d', '.glob', '.vo', '.o', '.cmi', '.cmxs', '.native', '.cmx')
    >>> names = [f.name[:-2] + ext for ext in exts] + [g.name[:-2] + ext for ext in exts]
    >>> names = [i for i in names if os.path.exists(i)]
    >>> for name in names: os.remove(name)
    """
    if filename[-2:] != '.v': filename += '.v'
    lib = lib_of_filename(filename, topname=topname)
    all_imports = recursively_get_imports(lib, verbose=verbose, fast=fast, log=log, topname=topname, coqc=coqc)
    remaining_imports = []
    rtn = ''
    imports_done = []
    for import_name in all_imports:
        try:
            if as_modules:
                rtn += contents_as_module_without_require(import_name, imports_done, verbose=verbose, log=log, topname=topname) + '\n'
            else:
                rtn += contents_without_imports(import_name, verbose=verbose, log=log, topname=topname) + '\n'
            imports_done.append(import_name)
        except IOError:
            remaining_imports.append(import_name)
    if len(remaining_imports) > 0:
        if verbose:
            log('remaining imports:')
            log(remaining_imports)
        if as_modules:
            pattern = 'Require %s.\n%s'
        else:
            pattern = 'Require Import %s.\n%s'
        for imp in reversed(remaining_imports):
            rtn = pattern % (imp, rtn)
    return rtn

if __name__ == "__main__":
    # if we're working in python 3.3, we can test this file
    try:
        import doctest
        success = True
    except ImportError:
        print('This is not the main file to use.\nOnly run it if you have doctest (python 3.3+) and are testing things.')
        success = False
    if success:
        doctest.testmod()
