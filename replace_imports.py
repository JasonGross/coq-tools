from __future__ import with_statement
import os, subprocess, re, sys

__all__ = ["include_imports"]

file_mtimes = {}
file_contents = {}
file_imports_fast = {}
file_imports_slow = {}

IMPORT_REG = re.compile('^R[0-9]+:[0-9]+ ([^ ]+) <> <> lib$', re.MULTILINE)
IMPORT_LINE_REG = re.compile(r'^\s*(?:Require\s+Import|Require\s+Export|Import|Require)\s+(.*?)\.(?:\s|$)', re.MULTILINE | re.DOTALL)

def get_file(file_name, verbose=True):
    if file_name[-2:] != '.v': file_name += '.v'
    if file_name not in file_contents.keys() or file_mtimes[file_name] < os.stat(file_name).st_mtime:
        if verbose: print(file_name)
        try:
            with open(file_name, 'r', encoding='UTF-8') as f:
                file_contents[file_name] = f.read()
        except TypeError:
            with open(file_name, 'r') as f:
                file_contents[file_name] = f.read()
        file_mtimes[file_name] = os.stat(file_name).st_mtime
    return file_contents[file_name]

def make_globs(*file_names):
    file_names_v = [i + '.v' if i[-2:] != '.v' else i for i in file_names]
    file_names_v = [os.path.relpath(i, '.') for i in file_names_v if os.path.exists(i)]
    file_names_stripped = [i[:-2] for i in file_names_v]
    file_names_glob = [i + '.glob' for i in file_names_stripped]
    if len(file_names_v) == 0: return
    p_make_makefile = subprocess.Popen(['coq_makefile'] + file_names_v, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    p_make = subprocess.Popen(['make', '-f', '-'] + file_names_glob, stdin=subprocess.PIPE, stdout=subprocess.PIPE)
    (stdout, stderr) = p_make_makefile.communicate()
    (stdout_make, stderr_make) = p_make.communicate(stdout)

def get_imports(file_name, verbose=True, fast=False):
    if file_name[-2:] == '.v': file_name = file_name[:-2]
    if not fast:
        if file_name not in file_imports_slow.keys():
            if not os.path.exists(file_name + '.glob'):
                make_globs(file_name)
            if os.path.exists(file_name + '.glob'): # making succeeded
                with open(file_name + '.glob', 'r') as f:
                    contents = f.read()
                lines = contents.split('\n')
                file_imports_slow[file_name] = tuple(sorted(set(IMPORT_REG.findall(contents))))
                return file_imports_slow[file_name]
    # making globs failed, or we want the fast way, fall back to regexp
    if file_name not in file_imports_fast.keys():
        contents = get_file(file_name + '.v', verbose=verbose)
        imports_string = re.sub('\\s+', ' ', ' '.join(IMPORT_LINE_REG.findall(contents))).strip()
        file_imports_fast[file_name] = tuple(sorted(set(imports_string.split(' '))))
    return file_imports_fast[file_name]

def merge_imports(*imports):
    rtn = []
    for import_list in imports:
        for i in import_list:
            if i not in rtn:
                rtn.append(i)
    return rtn

def recursively_get_imports(file_name, verbose=True, fast=False):
    if file_name[-2:] != '.v': file_name += '.v'
    if os.path.exists(file_name):
        imports = get_imports(file_name, verbose=verbose, fast=fast)
        make_globs(*imports)
        imports_list = [recursively_get_imports(i, verbose=verbose, fast=fast) for i in imports]
        return merge_imports(*imports_list) + [file_name[:-2]]
    return [file_name[:-2]]

def contents_without_imports(file_name, verbose=True):
    if file_name[-2:] != '.v': file_name += '.v'
    contents = get_file(file_name, verbose=verbose)
    if '(*' in ' '.join(IMPORT_LINE_REG.findall(contents)):
        print('Warning: There are comments in your Require/Import/Export lines.')
    return IMPORT_LINE_REG.sub('', contents)

def include_imports(file_name, verbose=True, fast=False):
    """Return the contents of file_name, with any top-level imports inlined.

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
    >>> print(include_imports(f.name, verbose=False))
    Require Import Coq.Arith.Arith Coq.Bool.Bool Coq.Init.Logic Coq.PArith.PArith Coq.QArith.QArith Coq.Setoids.Setoid Coq.ZArith.ZArith Coq.Strings.Ascii Coq.Strings.String.

    Inductive q := c | d.
    (* asdf *)


    Inductive t := a | b.

    (*asdf*)

    >>> print(include_imports(f.name, fast=True, verbose=False))
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
    if file_name[-2:] != '.v': file_name += '.v'
    all_imports = recursively_get_imports(file_name, verbose=verbose, fast=fast)
    remaining_imports = []
    rtn = ''
    for import_name in all_imports:
        if os.path.exists(import_name + '.v'):
            rtn += contents_without_imports(import_name, verbose=verbose) + '\n'
        else:
            remaining_imports.append(import_name)
    rtn = 'Require Import %s.\n%s' % (' '.join(remaining_imports), rtn)
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
