from __future__ import with_statement, print_function
import os, subprocess, re, sys, glob, os.path
from memoize import memoize

__all__ = ["filename_of_lib", "lib_of_filename", "get_file", "make_globs", "get_imports", "norm_libname", "recursively_get_imports"]

file_contents = {}
lib_imports_fast = {}
lib_imports_slow = {}

DEFAULT_VERBOSE=1
DEFAULT_TOPNAME='Top'

IMPORT_REG = re.compile('^R[0-9]+:[0-9]+ ([^ ]+) <> <> lib$', re.MULTILINE)
IMPORT_LINE_REG = re.compile(r'^\s*(?:Require\s+Import|Require\s+Export|Require|Load\s+Verbose|Load)\s+(.*?)\.(?:\s|$)', re.MULTILINE | re.DOTALL)

def DEFAULT_LOG(text):
    print(text)

@memoize
def filename_of_lib(lib, topname=DEFAULT_TOPNAME, ext='.v'):
    if lib[:len(topname + '.')] == topname + '.':
        lib = lib[len(topname + '.'):]
        lib = lib.replace('.', os.sep)
        return os.path.relpath(os.path.normpath(lib + ext), '.')
    else:
        # is this the right thing to do?
        lib = lib.replace('.', os.sep)
        for dirpath, dirname, filenames in os.walk('.', followlinks=True):
            filename = os.path.relpath(os.path.normpath(os.path.join(dirpath, lib + ext)), '.')
            if os.path.exists(filename):
                return filename
        return os.path.relpath(os.path.normpath(lib + ext), '.')

    return filename_of_lib_helper(lib, topname) + ext

def lib_of_filename(filename, topname=DEFAULT_TOPNAME, exts=('.v', '.glob')):
    filename = os.path.relpath(filename, '.')
    for ext in exts:
        if filename[-len(ext):] == ext:
            filename = filename[:-len(ext)]
            break
    if '.' in filename:
        print("WARNING: There is a dot (.) in filename %s; the library conversion probably won't work." % filename)
    return topname + '.' + filename.replace(os.sep, '.')

def get_raw_file(filename, verbose=DEFAULT_VERBOSE, log=DEFAULT_LOG):
    if verbose: log('getting %s' % filename)
    try:
        with open(filename, 'r', encoding='UTF-8') as f:
            return f.read()
    except TypeError:
        with open(filename, 'r') as f:
            return f.read()

def update_imports_with_glob(contents, globs, verbose=DEFAULT_VERBOSE, log=DEFAULT_LOG):
    for start, end, rep in reversed(re.findall('^R([0-9]+):([0-9]+) ([^ ]+) <> <> lib', globs, flags=re.MULTILINE)):
        start, end = int(start), int(end) + 1
        if verbose >= 2: log('Qualifying import %s to %s' % (contents[start:end], rep))
        contents = '%s%s%s' % (contents[:start], rep, contents[end:])
    return contents

def get_file(filename, verbose=DEFAULT_VERBOSE, log=DEFAULT_LOG, absoluteize_imports=True):
    if filename[-2:] != '.v': filename += '.v'
    globname = filename[:-2] + '.glob'
    if filename not in file_contents.keys() or file_mtimes[filename] < os.stat(filename).st_mtime:
        file_contents[filename] = get_raw_file(filename, verbose=verbose, log=log)
        file_mtimes[filename] = os.stat(filename).st_mtime
        if os.path.isfile(globname) and absoluteize_imports:
            if os.stat(globname).st_mtime >= file_mtimes[filename]:
                globs = get_raw_file(filename[:-2] + '.glob', verbose=verbose, log=log)
                file_contents[filename] = update_imports_with_glob(file_contents[filename], globs, verbose=verbose, log=log)
            elif verbose:
                log("WARNING: Assuming that %s is not a valid reflection of %s because %s is newer" % (globname, filename, filename))
    return file_contents[filename]

def get_all_v_files(directory, exclude=tuple()):
    all_files = []
    exclude = [os.path.normpath(i) for i in exclude]
    for dirpath, dirnames, filenames in os.walk(directory):
        all_files += [os.path.relpath(name, '.') for name in glob.glob(os.path.join(dirpath, '*.v'))
                      if os.path.normpath(name) not in exclude]
    return all_files

@memoize
def get_makefile_contents(coqc, topname, v_files, verbose, log):
    cmds = ['coq_makefile', 'COQC', '=', coqc, '-R', '.', topname] + list(v_files)
    if verbose:
        log(' '.join(cmds))
    p_make_makefile = subprocess.Popen(cmds,
                                       stdout=subprocess.PIPE,
                                       stderr=subprocess.PIPE)
    return p_make_makefile.communicate()

def make_globs(libnames, verbose=DEFAULT_VERBOSE, topname=DEFAULT_TOPNAME, log=DEFAULT_LOG, coqc='coqc'):
    extant_libnames = [i for i in libnames
                       if os.path.exists(filename_of_lib(i, topname=topname, ext='.v'))]
    if len(extant_libnames) == 0: return
    filenames_v = [filename_of_lib(i, topname=topname, ext='.v') for i in extant_libnames]
    filenames_glob = [filename_of_lib(i, topname=topname, ext='.glob') for i in extant_libnames]
    if all(os.path.exists(glob_name) and os.path.getmtime(glob_name) > os.path.getmtime(v_name)
           for glob_name, v_name in zip(filenames_glob, filenames_v)):
        return
    extra_filenames_v = get_all_v_files('.', filenames_v)
    (stdout, stderr) = get_makefile_contents(coqc, topname, tuple(sorted(filenames_v + extra_filenames_v)), verbose, log)
    if verbose:
        log(' '.join(['make', '-k', '-f', '-'] + filenames_glob))
    p_make = subprocess.Popen(['make', '-k', '-f', '-'] + filenames_glob, stdin=subprocess.PIPE, stdout=subprocess.PIPE)
    (stdout_make, stderr_make) = p_make.communicate(stdout)

def get_imports(lib, verbose=DEFAULT_VERBOSE, fast=False, log=DEFAULT_LOG, topname=DEFAULT_TOPNAME, coqc='coqc'):
    lib = norm_libname(lib, topname=topname)
    glob_name = filename_of_lib(lib, topname=topname, ext='.glob')
    v_name = filename_of_lib(lib, topname=topname, ext='.v')
    if not fast:
        if lib not in lib_imports_slow.keys():
            make_globs([lib], verbose=verbose, topname=topname, log=log, coqc=coqc)
            if os.path.exists(glob_name): # making succeeded
                with open(glob_name, 'r') as f:
                    contents = f.read()
                lines = contents.split('\n')
                lib_imports_slow[lib] = tuple(sorted(set(norm_libname(name, topname=topname)
                                                         for name in IMPORT_REG.findall(contents))))
                return lib_imports_slow[lib]
    # making globs failed, or we want the fast way, fall back to regexp
    if lib not in lib_imports_fast.keys():
        contents = get_file(v_name, verbose=verbose, log=log)
        imports_string = re.sub('\\s+', ' ', ' '.join(IMPORT_LINE_REG.findall(contents))).strip()
        lib_imports_fast[lib] = tuple(sorted(set(norm_libname(i, topname=topname)
                                                 for i in imports_string.split(' ') if i != '')))
    return lib_imports_fast[lib]

def norm_libname(lib, topname=DEFAULT_TOPNAME):
    filename = filename_of_lib(lib, topname=topname)
    if os.path.exists(filename):
        return lib_of_filename(filename, topname=topname)
    else:
        return lib

def merge_imports(imports, topname=DEFAULT_TOPNAME):
    rtn = []
    for import_list in imports:
        for i in import_list:
            if norm_libname(i, topname=topname) not in rtn:
                rtn.append(norm_libname(i, topname=topname))
    return rtn

# This is a bottleneck for more than around 10,000 lines of code total with many imports (around 100)
@memoize
def recursively_get_imports(lib, verbose=DEFAULT_VERBOSE, fast=False, log=DEFAULT_LOG, topname=DEFAULT_TOPNAME, coqc='coqc'):
    lib = norm_libname(lib, topname=topname)
    glob_name = filename_of_lib(lib, topname=topname, ext='.glob')
    v_name = filename_of_lib(lib, topname=topname, ext='.v')
    if os.path.exists(v_name):
        imports = get_imports(lib, verbose=verbose, fast=fast, topname=topname, coqc=coqc)
        if not fast: make_globs(imports, verbose=verbose, topname=topname, log=log, coqc=coqc)
        imports_list = [recursively_get_imports(i, verbose=verbose, fast=fast, log=log, topname=topname, coqc=coqc)
                        for i in imports]
        return merge_imports(tuple(map(tuple, imports_list + [[lib]])), topname=topname)
    return [lib]
