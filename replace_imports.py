from __future__ import with_statement
import os, subprocess, re, sys, glob

__all__ = ["include_imports"]

file_mtimes = {}
file_contents = {}
lib_imports_fast = {}
lib_imports_slow = {}

IMPORT_REG = re.compile('^R[0-9]+:[0-9]+ ([^ ]+) <> <> lib$', re.MULTILINE)
IMPORT_LINE_REG = re.compile(r'^\s*(?:Require\s+Import|Require\s+Export|Require|Load\s+Verbose|Load)\s+(.*?)\.(?:\s|$)', re.MULTILINE | re.DOTALL)

def DEFAULT_LOG(text):
    print(text)

def filename_of_lib(lib, topname='__TOP__', ext='.v'):
    if lib[:len(topname + '.')] == topname + '.':
        lib = lib[len(topname + '.'):]
        lib = lib.replace('.', os.sep)
    else:
        # is this the right thing to do?
        lib = lib.replace('.', os.sep)
    return os.path.relpath(os.path.normpath(lib + ext), '.')

def lib_of_filename(filename, topname='__TOP__', exts=('.v', '.glob')):
    filename = os.path.relpath(filename, '.')
    for ext in exts:
        if filename[-len(ext):] == ext:
            filename = filename[:-len(ext)]
            break
    if '.' in filename:
        print("WARNING: There is a dot (.) in filename %s; the library conversion probably won't work." % filename)
    return topname + '.' + filename.replace(os.sep, '.')

def get_file(filename, verbose=True, log=DEFAULT_LOG):
    if filename[-2:] != '.v': filename += '.v'
    if filename not in file_contents.keys() or file_mtimes[filename] < os.stat(filename).st_mtime:
        if verbose: log('getting %s' % filename)
        try:
            with open(filename, 'r', encoding='UTF-8') as f:
                file_contents[filename] = f.read()
        except TypeError:
            with open(filename, 'r') as f:
                file_contents[filename] = f.read()
        file_mtimes[filename] = os.stat(filename).st_mtime
    return file_contents[filename]

def get_all_v_files(directory, exclude=tuple()):
    all_files = []
    exclude = [os.path.normpath(i) for i in exclude]
    for dirpath, dirnames, filenames in os.walk(directory):
        all_files += [os.path.relpath(name, '.') for name in glob.glob(os.path.join(dirpath, '*.v'))
                      if os.path.normpath(name) not in exclude]
    return all_files

def make_globs(libnames, verbose=True, topname='__TOP__', log=DEFAULT_LOG):
    extant_libnames = [i for i in libnames
                       if os.path.exists(filename_of_lib(i, topname=topname, ext='.v'))]
    if len(extant_libnames) == 0: return
    filenames_v = [filename_of_lib(i, topname=topname, ext='.v') for i in extant_libnames]
    filenames_glob = [filename_of_lib(i, topname=topname, ext='.glob') for i in extant_libnames]
    extra_filenames_v = get_all_v_files('.', filenames_v)
    if verbose:
        log(' '.join(['coq_makefile', '-R', '.', topname] + filenames_v + extra_filenames_v))
    p_make_makefile = subprocess.Popen(['coq_makefile', '-R', '.', topname] + filenames_v + extra_filenames_v,
                                       stdout=subprocess.PIPE,
                                       stderr=subprocess.PIPE)
    (stdout, stderr) = p_make_makefile.communicate()
    if verbose:
        log(' '.join(['make', '-k', '-f', '-'] + filenames_glob))
    p_make = subprocess.Popen(['make', '-k', '-f', '-'] + filenames_glob, stdin=subprocess.PIPE, stdout=subprocess.PIPE)
    (stdout_make, stderr_make) = p_make.communicate(stdout)

def get_imports(lib, verbose=True, fast=False, log=DEFAULT_LOG, topname='__TOP__'):
    glob_name = filename_of_lib(lib, topname=topname, ext='.glob')
    v_name = filename_of_lib(lib, topname=topname, ext='.v')
    if not fast:
        if lib not in lib_imports_slow.keys():
            if not os.path.exists(glob_name):
                make_globs([lib], verbose=verbose, topname=topname, log=log)
            if os.path.exists(glob_name): # making succeeded
                with open(glob_name, 'r') as f:
                    contents = f.read()
                lines = contents.split('\n')
                lib_imports_slow[lib] = tuple(sorted(set(IMPORT_REG.findall(contents))))
                return lib_imports_slow[lib]
    # making globs failed, or we want the fast way, fall back to regexp
    if lib not in lib_imports_fast.keys():
        contents = get_file(v_name, verbose=verbose, log=log)
        imports_string = re.sub('\\s+', ' ', ' '.join(IMPORT_LINE_REG.findall(contents))).strip()
        lib_imports_fast[lib] = tuple(sorted(set(i for i in imports_string.split(' ') if i != '')))
    return lib_imports_fast[lib]

def norm_libname(lib, topname='__TOP__'):
    if lib[:len(topname + '.')] != topname + '.' and os.path.exists(filename_of_lib(lib, topname=topname)):
        return topname + '.' + lib
    return lib

def merge_imports(imports, topname='__TOP__'):
    rtn = []
    for import_list in imports:
        for i in import_list:
            if norm_libname(i, topname=topname) not in rtn:
                rtn.append(norm_libname(i, topname=topname))
    return rtn

def recursively_get_imports(lib, verbose=True, fast=False, log=DEFAULT_LOG, topname='__TOP__'):
    glob_name = filename_of_lib(lib, topname=topname, ext='.glob')
    v_name = filename_of_lib(lib, topname=topname, ext='.v')
    if os.path.exists(v_name):
        imports = get_imports(lib, verbose=verbose, fast=fast, topname=topname)
        if not fast: make_globs(imports, verbose=verbose, topname=topname, log=log)
        imports_list = [recursively_get_imports(i, verbose=verbose, fast=fast, log=log, topname=topname)
                        for i in imports]
        return merge_imports(imports_list + [[lib]], topname=topname)
    return [lib]

def contents_without_imports(lib, verbose=True, log=DEFAULT_LOG, topname='__TOP__'):
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

def recreate_path_structure(lib_libname_pairs, uid='', topname='__TOP__'):
    '''Takes a list of (<dotted name, escaped name>) pairs, and turns it into a nested module structure'''
    rtn = ''
    lib_libname_pairs = [(lib[len(topname + '.'):]
                          if lib[:len(topname + '.')] == topname + '.'
                          else lib,
                          libname)
                         for lib, libname in lib_libname_pairs]
    if topname != '': rtn += 'Module Import %s%s.\n' % (uid, topname)
    top_libnames = [libname for lib, libname in lib_libname_pairs if lib == '']
    lib_libname_pairs = [(lib, libname) for lib, libname in lib_libname_pairs
                         if lib != '']
    for top_libname in top_libnames:
        rtn += 'Include %s.\n' % top_libname
    for cur_lib, lib_list in group_by_first_component(lib_libname_pairs).items():
        rtn += 'Module %s.\n' % cur_lib
        rtn += recreate_path_structure(lib_list, topname='')
        if cur_lib in [other_lib for other_lib, other_libname in lib_list] and cur_lib not in top_libnames:
            rtn += 'Include %s.\n' % cur_lib
        rtn += 'End %s.\n' % cur_lib
    if topname != '': rtn += 'End %s%s.\n' % (uid, topname)
    return rtn

def contents_as_module_without_require(lib, other_imports, verbose=True, log=DEFAULT_LOG, topname='__TOP__'):
    v_name = filename_of_lib(lib, topname=topname, ext='.v')
    contents = get_file(v_name, verbose=verbose, log=log)
    contents = re.sub(r'^\s*Require\s+((?:Import|Export)\s)',
                      r'\1',
                      contents,
                      flags=re.MULTILINE)
    contents = re.sub(r'^\s*Require\s+((?!Import\s+|Export\s+)(?:[^\.]|\.(?!\s$))+\.(?:\s|$))',
                      r'',
                      contents,
                      flags=re.MULTILINE)
    module_name = escape_lib(lib)
    existing_imports = recreate_path_structure([(i, escape_lib(i)) for i in other_imports],
                                               uid=module_name,
                                               topname=topname)
    contents = 'Module %s.\n%s\n%s\nEnd %s.\n' % (module_name, existing_imports, contents, module_name)
    return contents


def include_imports(filename, as_modules=True, verbose=True, fast=False, log=DEFAULT_LOG, topname='__TOP__'):
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
    lib = lib_of_filename(filename)
    all_imports = recursively_get_imports(lib, verbose=verbose, fast=fast, log=log, topname=topname)
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
        rtn = pattern % (' '.join(remaining_imports), rtn)
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
