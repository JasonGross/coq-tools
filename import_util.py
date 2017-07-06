from __future__ import with_statement, print_function
import os, subprocess, re, sys, glob, os.path, tempfile, time
from memoize import memoize
from coq_version import get_coqc_help, group_coq_args_split_recognized, coq_makefile_supports_arg
from custom_arguments import DEFAULT_VERBOSITY, DEFAULT_LOG

__all__ = ["filename_of_lib", "lib_of_filename", "get_file", "make_globs", "get_imports", "norm_libname", "recursively_get_imports", "IMPORT_ABSOLUTIZE_TUPLE", "ALL_ABSOLUTIZE_TUPLE", "absolutize_has_all_constants", "run_recursively_get_imports", "clear_libimport_cache", "get_glob_file_for", "get_references_for"]

file_mtimes = {}
file_contents = {}
lib_imports_fast = {}
lib_imports_slow = {}

DEFAULT_LIBNAMES=(('.', 'Top'), )

IMPORT_ABSOLUTIZE_TUPLE = ('lib', )# 'mod')
ALL_ABSOLUTIZE_TUPLE = ('lib', 'proj', 'rec', 'ind', 'constr', 'def', 'syndef', 'class', 'thm', 'lem', 'prf', 'ax', 'inst', 'prfax', 'coind', 'scheme', 'vardef')# , 'mod', 'modtype')

IMPORT_REG = re.compile('^R([0-9]+):([0-9]+) ([^ ]+) <> <> lib$', re.MULTILINE)
IMPORT_LINE_REG = re.compile(r'^\s*(?:Require\s+Import|Require\s+Export|Require|Load\s+Verbose|Load)\s+(.*?)\.(?:\s|$)', re.MULTILINE | re.DOTALL)

def warning(*objs):
    print("WARNING: ", *objs, file=sys.stderr)

def error(*objs):
    print("ERROR: ", *objs, file=sys.stderr)

def fill_kwargs(kwargs):
    rtn = {
        'libnames'              : DEFAULT_LIBNAMES,
        'non_recursive_libnames': tuple(),
        'verbose'               : DEFAULT_VERBOSITY,
        'log'                   : DEFAULT_LOG,
        'coqc'                  : 'coqc',
        'coq_makefile'          : 'coq_makefile',
        'walk_tree'             : True,
        'coqc_args'             : tuple(),
        'inline_coqlib'         : None,
        }
    rtn.update(kwargs)
    return rtn

def safe_kwargs(kwargs):
    for k, v in list(kwargs.items()):
        if isinstance(v, list):
            kwargs[k] = tuple(v)
    return dict((k, v) for k, v in kwargs.items() if not isinstance(v, dict))

def fix_path(filename):
    return filename.replace('\\', '/')

def absolutize_has_all_constants(absolutize_tuple):
    '''Returns True if absolutizing the types of things mentioned by the tuple is enough to ensure that we only use absolute names'''
    return set(ALL_ABSOLUTIZE_TUPLE).issubset(set(absolutize_tuple))

def libname_with_dot(logical_name):
    if logical_name in ("", '""', "''"):
        return ""
    else:
        return logical_name + "."

def clear_libimport_cache(libname):
    if libname in lib_imports_fast.keys():
        del lib_imports_fast[libname]
    if libname in lib_imports_slow.keys():
        del lib_imports_slow[libname]

@memoize
def os_walk(top, topdown=True, onerror=None, followlinks=False):
    return tuple(os.walk(top, topdown=topdown, onerror=onerror, followlinks=followlinks))

@memoize
def os_path_isfile(filename):
    return os.path.isfile(filename)

@memoize
def filename_of_lib_helper(lib, libnames, non_recursive_libnames, ext):
    for physical_name, logical_name in list(libnames) + list(non_recursive_libnames):
        if lib.startswith(libname_with_dot(logical_name)):
            lib = lib[len(libname_with_dot(logical_name)):]
            lib = os.path.join(physical_name, lib.replace('.', os.sep))
            return fix_path(os.path.relpath(os.path.normpath(lib + ext), '.'))
    # is this the right thing to do?
    lib = lib.replace('.', os.sep)
    for dirpath, dirname, filenames in os_walk('.', followlinks=True):
        filename = os.path.relpath(os.path.normpath(os.path.join(dirpath, lib + ext)), '.')
        if os_path_isfile(filename):
            return fix_path(filename)
    return fix_path(os.path.relpath(os.path.normpath(lib + ext), '.'))

def filename_of_lib(lib, ext='.v', **kwargs):
    kwargs = fill_kwargs(kwargs)
    return filename_of_lib_helper(lib, libnames=tuple(kwargs['libnames']), non_recursive_libnames=tuple(kwargs['non_recursive_libnames']), ext=ext)

@memoize
def lib_of_filename_helper(filename, libnames, non_recursive_libnames, exts):
    filename = os.path.relpath(os.path.normpath(filename), '.')
    for ext in exts:
        if filename.endswith(ext):
            filename = filename[:-len(ext)]
            break
    for physical_name, logical_name in ((os.path.relpath(os.path.normpath(phys), '.'), libname_with_dot(logical)) for phys, logical in list(libnames) + list(non_recursive_libnames)):
        if filename.startswith(physical_name) or (physical_name == '.' and not filename.startswith('..' + os.sep)):
            return (filename, logical_name + os.path.relpath(filename, physical_name).replace(os.sep, '.'))
    return (filename, filename.replace(os.sep, '.'))

def lib_of_filename(filename, exts=('.v', '.glob'), **kwargs):
    kwargs = fill_kwargs(kwargs)
    filename, libname = lib_of_filename_helper(filename, libnames=tuple(kwargs['libnames']), non_recursive_libnames=tuple(kwargs['non_recursive_libnames']), exts=exts)
    if '.' in filename and kwargs['verbose']:
        kwargs['log']("WARNING: There is a dot (.) in filename %s; the library conversion probably won't work." % filename)
    return libname

def is_local_import(libname, **kwargs):
    '''Returns True if libname is an import to a local file that we can discover and include, and False otherwise'''
    return os.path.isfile(filename_of_lib(libname, **kwargs))

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

def move_strings_once(before, after, possibility):
    for i in possibility:
        if before[-len(i):] == i:
            return before[:-len(i)], before[-len(i):] + after
    return None, None

def move_strings_pre(before, after, possibility):
    while len(before) > 0:
        new_before, new_after = move_strings_once(before, after, possibility)
        if new_before is None or new_after is None:
            return before, after
        before, after = new_before, new_after
    return (before, after)

def move_function(before, after, get_len):
    while len(before) > 0:
        n = get_len(before)
        if n is None or n <= 0:
            return before, after
        before, after = before[:-n], before[n:] + after
    return before, after

def move_strings(before, after, *possibilities):
    for possibility in possibilities:
        before, after = move_strings_pre(before, after, possibility)
    return before, after

def move_space(before, after):
    return move_strings(before, after, '\n\t\r ')

def remove_from_require_before(contents, location):
    """removes "From ... " from things like "From ... Require ..." """
    before, after = contents[:location], contents[location:]
    before, after = move_space(before, after)
    before, after = move_strings_once(before, after, ('Import', 'Export'))
    if before is None or after is None: return contents
    before, after = move_space(before, after)
    before, after = move_strings_once(before, after, ('Require',))
    if before is None or after is None: return contents
    before, _ = move_space(before, after)
    before, _ = move_function(before, after, (lambda b: 1 if b[-1] not in ' \t\r\n' else None))
    if before is None: return contents
    before, _ = move_space(before, after)
    before, _ = move_strings_once(before, after, ('From',))
    if before is None: return contents
    return before + after

def get_references_from_globs(globs):
    all_globs = set((int(start), int(end) + 1, loc, append, ty.strip())
                    for start, end, loc, append, ty
                    in re.findall('^R([0-9]+):([0-9]+) ([^ ]+) <> ([^ ]+) ([^ ]+)$', globs, flags=re.MULTILINE))
    return tuple(sorted(all_globs, key=(lambda x: x[0]), reverse=True))

def update_with_glob(contents, globs, absolutize, libname, transform_base=(lambda x: x), **kwargs):
    kwargs = fill_kwargs(kwargs)
    for start, end, loc, append, ty in get_references_from_globs(globs):
        if ty not in absolutize or loc == libname:
            if kwargs['verbose'] >= 2: kwargs['log']('Skipping %s at %d:%d (%s), location %s %s' % (ty, start, end, contents[start:end], loc, append))
        # sanity check for correct replacement, to skip things like record builder notation
        elif append != '<>' and get_constr_name(contents[start:end]) != append:
            if kwargs['verbose'] >= 2: kwargs['log']('Skipping invalid %s at %d:%d (%s), location %s %s' % (ty, start, end, contents[start:end], loc, append))
        else: # ty in absolutize and loc != libname
            rep = transform_base(loc) + ('.' + append if append != '<>' else '')
            if kwargs['verbose'] == 2: kwargs['log']('Qualifying %s %s to %s' % (ty, contents[start:end], rep))
            if kwargs['verbose'] > 2: kwargs['log']('Qualifying %s %s to %s from R%s:%s %s <> %s %s' % (ty, contents[start:end], rep, start, end, loc, append, ty))
            contents = '%s%s%s' % (contents[:start], rep, contents[end:])
            contents = remove_from_require_before(contents, start)

    return contents

def get_all_v_files(directory, exclude=tuple()):
    all_files = []
    exclude = [os.path.normpath(i) for i in exclude]
    for dirpath, dirnames, filenames in os.walk(directory):
        all_files += [os.path.relpath(name, '.') for name in glob.glob(os.path.join(dirpath, '*.v'))
                      if os.path.normpath(name) not in exclude]
    return tuple(map(fix_path, all_files))

def run_coq_makefile_and_make(v_files, targets, **kwargs):
    kwargs = safe_kwargs(fill_kwargs(kwargs))
    f = tempfile.NamedTemporaryFile(suffix='.coq', prefix='Makefile', dir='.', delete=False)
    mkfile = os.path.basename(f.name)
    f.close()
    cmds = [kwargs['coq_makefile'], 'COQC', '=', kwargs['coqc'], '-o', mkfile]
    for physical_name, logical_name in kwargs['libnames']:
        cmds += ['-R', physical_name, (logical_name if logical_name not in ("", "''", '""') else '""')]
    for physical_name, logical_name in kwargs['non_recursive_libnames']:
        cmds += ['-Q', physical_name, (logical_name if logical_name not in ("", "''", '""') else '""')]
    coq_makefile_help = get_coqc_help(kwargs['coq_makefile'], **kwargs)
    grouped_args, unrecognized_args = group_coq_args_split_recognized(kwargs['coqc_args'], coq_makefile_help, is_coq_makefile=True)
    for args in grouped_args:
        cmds.extend(args)
    if unrecognized_args:
        if coq_makefile_supports_arg(coq_makefile_help):
            for arg in unrecognized_args:
                cmds += ['-arg', arg]
        else:
            if kwargs['verbose']: kwargs['log']('WARNING: Unrecognized arguments to coq_makefile: %s' % repr(unrecognized_args))
    cmds += list(map(fix_path, v_files))
    if kwargs['verbose']:
        kwargs['log'](' '.join(cmds))
    try:
        p_make_makefile = subprocess.Popen(cmds,
                                           stdout=subprocess.PIPE)
        (stdout, stderr) = p_make_makefile.communicate()
    except OSError as e:
        error("When attempting to run coq_makefile:")
        error(repr(e))
        error("Failed to run coq_makefile using command line:")
        error(' '.join(cmds))
        error("Perhaps you forgot to add COQBIN to your PATH?")
        error("Try running coqc on your files to get a .glob files, to work around this.")
        sys.exit(1)
    if kwargs['verbose']:
        kwargs['log'](' '.join(['make', '-k', '-f', mkfile] + targets))
    try:
        p_make = subprocess.Popen(['make', '-k', '-f', mkfile] + targets, stdin=subprocess.PIPE, stdout=sys.stderr) #, stdout=subprocess.PIPE)
        return p_make.communicate()
    finally:
        for filename in (mkfile, mkfile + '.conf'):
            if os.path.exists(filename):
                os.remove(filename)

def make_globs(logical_names, **kwargs):
    kwargs = fill_kwargs(kwargs)
    extant_logical_names = [i for i in logical_names
                            if os.path.isfile(filename_of_lib(i, ext='.v', **kwargs))]
    if len(extant_logical_names) == 0: return
    filenames_v = [filename_of_lib(i, ext='.v', **kwargs) for i in extant_logical_names]
    filenames_glob = [filename_of_lib(i, ext='.glob', **kwargs) for i in extant_logical_names]
    if all(os.path.isfile(glob_name) and os.path.getmtime(glob_name) > os.path.getmtime(v_name)
           for glob_name, v_name in zip(filenames_glob, filenames_v)):
        return
    for glob_name, v_name in zip(filenames_glob, filenames_v):
        if os.path.isfile(glob_name) and not os.path.getmtime(glob_name) > os.path.getmtime(v_name):
            os.remove(glob_name)
    extra_filenames_v = (get_all_v_files('.', filenames_v) if kwargs['walk_tree'] else [])
    (stdout_make, stderr_make) = run_coq_makefile_and_make(tuple(sorted(list(filenames_v) + list(extra_filenames_v))), filenames_glob, **kwargs)

def get_glob_file_for(filename, update_globs=False, **kwargs):
    kwargs = fill_kwargs(kwargs)
    filename = fix_path(filename)
    if filename[-2:] != '.v': filename += '.v'
    libname = lib_of_filename(filename, **kwargs)
    globname = filename[:-2] + '.glob'
    if filename not in file_contents.keys() or file_mtimes[filename] < os.stat(filename).st_mtime:
        file_contents[filename] = get_raw_file(filename, **kwargs)
        file_mtimes[filename] = os.stat(filename).st_mtime
    if update_globs:
        # delay until the .v file is old enough that a .glob file will be considered newer
        while file_mtimes[filename] == time.time():
            time.sleep(0.1)
        make_globs([libname], **kwargs)
    if os.path.isfile(globname):
        if os.stat(globname).st_mtime > file_mtimes[filename]:
            return get_raw_file(globname, **kwargs)
        elif kwargs['verbose']:
            kwargs['log']("WARNING: Assuming that %s is not a valid reflection of %s because %s is newer" % (globname, filename, filename))
    return None


def get_references_for(filename, types, **kwargs):
    globs = get_glob_file_for(filename, **kwargs)
    if globs is None: return None
    references = get_references_from_globs(globs)
    return tuple((start, end, loc, append, ty) for start, end, loc, append, ty in references
                 if types is None or ty in types)

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
            globs = get_glob_file_for(filename, update_globs=update_globs, **kwargs)
            if globs is not None:
                file_contents[filename] = update_with_glob(file_contents[filename], globs, absolutize, libname, **kwargs)
    return file_contents[filename]

def get_require_dict(lib, **kwargs):
    kwargs = fill_kwargs(kwargs)
    lib = norm_libname(lib, **kwargs)
    glob_name = filename_of_lib(lib, ext='.glob', **kwargs)
    v_name = filename_of_lib(lib, ext='.v', **kwargs)
    if lib not in lib_imports_slow.keys():
        make_globs([lib], **kwargs)
        if os.path.isfile(glob_name): # making succeeded
            with open(glob_name, 'r') as f:
                contents = f.read()
            lines = contents.split('\n')
            lib_imports_slow[lib] = {}
            for start, end, name in IMPORT_REG.findall(contents):
                name = norm_libname(name, **kwargs)
                if name not in lib_imports_slow[lib].keys():
                    lib_imports_slow[lib][name] = []
                lib_imports_slow[lib][name].append((int(start), int(end)))
            for name in lib_imports_slow[lib].keys():
                lib_imports_slow[lib][name] = tuple(lib_imports_slow[lib][name])
    if lib in lib_imports_slow.keys():
        return lib_imports_slow[lib]
    return {}

def get_require_names(lib, **kwargs):
    return tuple(sorted(get_require_dict(lib, **kwargs).keys()))

def get_require_locations(lib, **kwargs):
    return sorted(set(loc for name, locs in get_require_dict(lib, **kwargs).items()
                      for loc in locs))


def get_imports(lib, fast=False, **kwargs):
    kwargs = fill_kwargs(kwargs)
    lib = norm_libname(lib, **kwargs)
    glob_name = filename_of_lib(lib, ext='.glob', **kwargs)
    v_name = filename_of_lib(lib, ext='.v', **kwargs)
    if not fast:
        get_require_dict(lib, **kwargs)
        if lib in lib_imports_slow.keys():
            return tuple(k for k, v in sorted(lib_imports_slow[lib].items(), key=(lambda kv: kv[1])))
    # making globs failed, or we want the fast way, fall back to regexp
    if lib not in lib_imports_fast.keys():
        contents = get_file(v_name, **kwargs)
        imports_string = re.sub('\\s+', ' ', ' '.join(IMPORT_LINE_REG.findall(contents))).strip()
        lib_imports_fast[lib] = tuple(sorted(set(norm_libname(i, **kwargs)
                                                 for i in imports_string.split(' ') if i != '')))
    return lib_imports_fast[lib]

def norm_libname(lib, **kwargs):
    kwargs = fill_kwargs(kwargs)
    filename = filename_of_lib(lib, **kwargs)
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
def internal_recursively_get_imports(lib, **kwargs):
    return run_recursively_get_imports(lib, recur=internal_recursively_get_imports, **kwargs)

def recursively_get_imports(lib, **kwargs):
    return internal_recursively_get_imports(lib, **safe_kwargs(kwargs))

def run_recursively_get_imports(lib, recur=recursively_get_imports, fast=False, **kwargs):
    kwargs = fill_kwargs(kwargs)
    lib = norm_libname(lib, **kwargs)
    glob_name = filename_of_lib(lib, ext='.glob', **kwargs)
    v_name = filename_of_lib(lib, ext='.v', **kwargs)
    if os.path.isfile(v_name):
        imports = get_imports(lib, fast=fast, **kwargs)
        if kwargs['inline_coqlib'] and 'Coq.Init.Prelude' not in imports:
            mykwargs = dict(kwargs)
            coqlib_libname = (os.path.join(kwargs['inline_coqlib'], 'theories'), 'Coq')
            if coqlib_libname not in mykwargs['libnames']:
                mykwargs['libnames'] = tuple(list(kwargs['libnames']) + [coqlib_libname])
            try:
                coqlib_imports = get_imports('Coq.Init.Prelude', fast=fast, **mykwargs)
                if imports and not any(i in imports for i in coqlib_imports):
                    imports = tuple(list(coqlib_imports) + list(imports))
            except IOError as e:
                kwargs['log']("WARNING: --inline-coqlib passed, but no Coq.Init.Prelude found on disk.\n  Searched in %s\n  (Error was: %s)\n\n" % (repr(mykwargs['libnames']), repr(e)))
        if not fast: make_globs(imports, **kwargs)
        imports_list = [recur(k, fast=fast, **kwargs) for k in imports]
        return merge_imports(tuple(map(tuple, imports_list + [[lib]])), **kwargs)
    return [lib]
