from __future__ import with_statement, print_function
import os, subprocess, re, sys, glob, os.path
from memoize import memoize

__all__ = ["filename_of_lib", "lib_of_filename", "get_file", "make_globs", "get_imports", "norm_libname", "recursively_get_imports", "IMPORT_ABSOLUTIZE_TUPLE", "ALL_ABSOLUTIZE_TUPLE", "absolutize_has_all_constants"]

file_mtimes = {}
file_contents = {}
lib_imports_fast = {}
lib_imports_slow = {}

DEFAULT_VERBOSE=1
DEFAULT_TOPNAME='Top'

IMPORT_ABSOLUTIZE_TUPLE = ('lib', 'mod')
ALL_ABSOLUTIZE_TUPLE = ('lib', 'proj', 'rec', 'ind', 'constr', 'def', 'syndef', 'mod', 'class', 'thm', 'lem', 'prf', 'ax', 'inst', 'prfax', 'coind', 'scheme', 'vardef')

IMPORT_REG = re.compile('^R[0-9]+:[0-9]+ ([^ ]+) <> <> lib$', re.MULTILINE)
IMPORT_LINE_REG = re.compile(r'^\s*(?:Require\s+Import|Require\s+Export|Require|Load\s+Verbose|Load)\s+(.*?)\.(?:\s|$)', re.MULTILINE | re.DOTALL)

def DEFAULT_LOG(text):
    print(text)

def fill_kwargs(kwargs):
    rtn = {
        'topname': DEFAULT_TOPNAME,
        'verbose': DEFAULT_VERBOSE,
        'log'    : DEFAULT_LOG,
        'coqc'   : 'coqc'
        }
    rtn.update(kwargs)
    return rtn

def fix_path(filename):
    return filename.replace('\\', '/')

def absolutize_has_all_constants(absolutize_tuple):
    '''Returns True if absolutizing the types of things mentioned by the tuple is enough to ensure that we only use absolute names'''
    return set(ALL_ABSOLUTIZE_TUPLE).issubset(set(absolutize_tuple))

@memoize
def filename_of_lib(lib, topname=DEFAULT_TOPNAME, ext='.v'):
    if lib[:len(topname + '.')] == topname + '.':
        lib = lib[len(topname + '.'):]
        lib = lib.replace('.', os.sep)
        return fix_path(os.path.relpath(os.path.normpath(lib + ext), '.'))
    else:
        # is this the right thing to do?
        lib = lib.replace('.', os.sep)
        for dirpath, dirname, filenames in os.walk('.', followlinks=True):
            filename = os.path.relpath(os.path.normpath(os.path.join(dirpath, lib + ext)), '.')
            if os.path.isfile(filename):
                return fix_path(filename)
        return fix_path(os.path.relpath(os.path.normpath(lib + ext), '.'))

    return fix_path(filename_of_lib_helper(lib, topname) + ext)

def lib_of_filename(filename, exts=('.v', '.glob'), **kwargs):
    kwargs = fill_kwargs(kwargs)
    filename = os.path.relpath(filename, '.')
    for ext in exts:
        if filename[-len(ext):] == ext:
            filename = filename[:-len(ext)]
            break
    if '.' in filename and kwargs['verbose']:
        kwargs['log']("WARNING: There is a dot (.) in filename %s; the library conversion probably won't work." % filename)
    return kwargs['topname'] + '.' + filename.replace(os.sep, '.')

def is_local_import(libname, topname=DEFAULT_TOPNAME, **kwargs):
    '''Returns True if libname is an import to a local file that we can discover and include, and False otherwise'''
    return os.path.isfile(filename_of_lib(libname, topname=topname))

def get_raw_file(filename, **kwargs):
    kwargs = fill_kwargs(kwargs)
    if kwargs['verbose']: kwargs['log']('getting %s' % filename)
    try:
        with open(filename, 'r', encoding='UTF-8') as f:
            return f.read()
    except TypeError:
        with open(filename, 'r') as f:
            return f.read()

@memoize
def get_constr_name(code):
    first_word = code.split(' ')[0]
    last_component = first_word.split('.')[-1]
    return last_component


def update_with_glob(contents, globs, absolutize, libname, transform_base=(lambda x: x), **kwargs):
    kwargs = fill_kwargs(kwargs)
    all_globs = set((start, end, loc, append, ty.strip())
                    for start, end, loc, append, ty
                    in re.findall('^R([0-9]+):([0-9]+) ([^ ]+) <> ([^ ]+) ([^ ]+)$', globs, flags=re.MULTILINE))
    for start, end, loc, append, ty in sorted(all_globs, key=(lambda x: int(x[0])), reverse=True):
        ty = ty.strip() # clear trailing newlines
        start, end = int(start), int(end) + 1
        if ty not in absolutize or loc == libname:
            if kwargs['verbose'] >= 2: kwargs['log']('Skipping %s at %d:%d (%s), location %s %s' % (ty, start, end, contents[start:end], loc, append))
        # sanity check for correct replacement, to skip things like record builder notation
        elif append != '<>' and get_constr_name(contents[start:end]) != append:
            if kwargs['verbose'] >= 2: kwargs['log']('Skipping invalid %s at %d:%d (%s), location %s %s' % (ty, start, end, contents[start:end], loc, append))
        else: # ty in absolutize and loc != libname
            rep = transform_base(loc) + ('.' + append if append != '<>' else '')
            if kwargs['verbose'] >= 2: kwargs['log']('Qualifying %s %s to %s' % (ty, contents[start:end], rep))
            contents = '%s%s%s' % (contents[:start], rep, contents[end:])

    return contents

def get_all_v_files(directory, exclude=tuple()):
    all_files = []
    exclude = [os.path.normpath(i) for i in exclude]
    for dirpath, dirnames, filenames in os.walk(directory):
        all_files += [os.path.relpath(name, '.') for name in glob.glob(os.path.join(dirpath, '*.v'))
                      if os.path.normpath(name) not in exclude]
    return tuple(map(fix_path, all_files))

@memoize
def get_makefile_contents(coqc, topname, v_files, verbose, log):
    cmds = ['coq_makefile', 'COQC', '=', coqc, '-R', '.', topname] + list(map(fix_path, v_files))
    if verbose:
        log(' '.join(cmds))
    p_make_makefile = subprocess.Popen(cmds,
                                       stdout=subprocess.PIPE)
    return p_make_makefile.communicate()

def make_globs(libnames, **kwargs):
    kwargs = fill_kwargs(kwargs)
    extant_libnames = [i for i in libnames
                       if os.path.isfile(filename_of_lib(i, topname=kwargs['topname'], ext='.v'))]
    if len(extant_libnames) == 0: return
    filenames_v = [filename_of_lib(i, topname=kwargs['topname'], ext='.v') for i in extant_libnames]
    filenames_glob = [filename_of_lib(i, topname=kwargs['topname'], ext='.glob') for i in extant_libnames]
    if all(os.path.isfile(glob_name) and os.path.getmtime(glob_name) > os.path.getmtime(v_name)
           for glob_name, v_name in zip(filenames_glob, filenames_v)):
        return
    extra_filenames_v = get_all_v_files('.', filenames_v)
    (stdout, stderr) = get_makefile_contents(kwargs['coqc'], kwargs['topname'], tuple(sorted(list(filenames_v) + list(extra_filenames_v))), kwargs['verbose'], kwargs['log'])
    if kwargs['verbose']:
        kwargs['log'](' '.join(['make', '-k', '-f', '-'] + filenames_glob))
    p_make = subprocess.Popen(['make', '-k', '-f', '-'] + filenames_glob, stdin=subprocess.PIPE, stdout=sys.stderr) #, stdout=subprocess.PIPE)
    (stdout_make, stderr_make) = p_make.communicate(stdout)

def get_file(filename, absolutize=('lib',), update_globs=False, **kwargs):
    kwargs = fill_kwargs(kwargs)
    filename = fix_path(filename)
    if filename[-2:] != '.v': filename += '.v'
    libname = lib_of_filename(filename, **kwargs)
    globname = filename[:-2] + '.glob'
    if filename not in file_contents.keys() or file_mtimes[filename] < os.stat(filename).st_mtime:
        file_contents[filename] = get_raw_file(filename, **kwargs)
        file_mtimes[filename] = os.stat(filename).st_mtime
        if len(absolutize) > 0:
            if update_globs:
                make_globs([libname], **kwargs)
            if os.path.isfile(globname):
                if os.stat(globname).st_mtime >= file_mtimes[filename]:
                    globs = get_raw_file(globname, **kwargs)
                    file_contents[filename] = update_with_glob(file_contents[filename], globs, absolutize, libname, **kwargs)
                elif kwargs['verbose']:
                    kwargs['log']("WARNING: Assuming that %s is not a valid reflection of %s because %s is newer" % (globname, filename, filename))
    return file_contents[filename]

def get_imports(lib, fast=False, **kwargs):
    kwargs = fill_kwargs(kwargs)
    lib = norm_libname(lib, **kwargs)
    glob_name = filename_of_lib(lib, topname=kwargs['topname'], ext='.glob')
    v_name = filename_of_lib(lib, topname=kwargs['topname'], ext='.v')
    if not fast:
        if lib not in lib_imports_slow.keys():
            make_globs([lib], **kwargs)
            if os.path.isfile(glob_name): # making succeeded
                with open(glob_name, 'r') as f:
                    contents = f.read()
                lines = contents.split('\n')
                lib_imports_slow[lib] = tuple(sorted(set(norm_libname(name, **kwargs)
                                                         for name in IMPORT_REG.findall(contents))))
                return lib_imports_slow[lib]
    # making globs failed, or we want the fast way, fall back to regexp
    if lib not in lib_imports_fast.keys():
        contents = get_file(v_name, **kwargs)
        imports_string = re.sub('\\s+', ' ', ' '.join(IMPORT_LINE_REG.findall(contents))).strip()
        lib_imports_fast[lib] = tuple(sorted(set(norm_libname(i, **kwargs)
                                                 for i in imports_string.split(' ') if i != '')))
    return lib_imports_fast[lib]

def norm_libname(lib, **kwargs):
    kwargs = fill_kwargs(kwargs)
    filename = filename_of_lib(lib, topname=kwargs['topname'])
    if os.path.isfile(filename):
        return lib_of_filename(filename, **kwargs)
    else:
        return lib

def merge_imports(imports, **kwargs):
    kwargs = fill_kwargs(kwargs)
    rtn = []
    for import_list in imports:
        for i in import_list:
            if norm_libname(i, **kwargs) not in rtn:
                rtn.append(norm_libname(i, **kwargs))
    return rtn

# This is a bottleneck for more than around 10,000 lines of code total with many imports (around 100)
@memoize
def recursively_get_imports(lib, fast=False, **kwargs):
    kwargs = fill_kwargs(kwargs)
    lib = norm_libname(lib, **kwargs)
    glob_name = filename_of_lib(lib, topname=kwargs['topname'], ext='.glob')
    v_name = filename_of_lib(lib, topname=kwargs['topname'], ext='.v')
    if os.path.isfile(v_name):
        imports = get_imports(lib, fast=fast, **kwargs)
        if not fast: make_globs(imports, **kwargs)
        imports_list = [recursively_get_imports(i, **kwargs)
                        for i in imports]
        return merge_imports(tuple(map(tuple, imports_list + [[lib]])), **kwargs)
    return [lib]
