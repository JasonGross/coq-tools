from __future__ import with_statement, print_function
import re
from .split_file import split_leading_comments_and_whitespace
from .import_util import (
    filename_of_lib,
    lib_of_filename,
    get_file,
    run_recursively_get_imports,
    run_maybe_recursively_get_imports,
    recursively_get_imports,
    absolutize_has_all_constants,
    is_local_import,
    ALL_ABSOLUTIZE_TUPLE,
)
from .custom_arguments import DEFAULT_LOG
from .coq_running_support import get_reserved_modnames

__all__ = [
    "include_imports",
    "normalize_requires",
    "get_required_contents",
    "recursively_get_requires_from_file",
    "absolutize_and_mangle_libname",
]

file_contents = {}
lib_imports_fast = {}
lib_imports_slow = {}

DEFAULT_LIBNAMES = ((".", "Top"),)

IMPORT_LINE_REG = re.compile(
    r"^\s*(?:From|Require\s+Import|Require\s+Export|Require|Load\s+Verbose|Load)\s+(.*?)\.(?:\s|$)",
    re.MULTILINE | re.DOTALL,
)


def fill_kwargs(kwargs, for_makefile=True):
    rtn = {
        "fast": False,
        "log": DEFAULT_LOG,
        "libnames": DEFAULT_LIBNAMES,
        "non_recursive_libnames": (),
        "coqc": ("coqc",),
        "coqtop": ("coqtop",),
        "absolutize": ALL_ABSOLUTIZE_TUPLE,
        "coq_makefile": ("coq_makefile",),
    }
    rtn.update(kwargs)
    if for_makefile:
        if "make_coqc" in rtn.keys():  # handle the case where coqc for the makefile is different
            rtn["coqc"] = rtn["make_coqc"]
        if "passing_make_coqc" in rtn.keys():  # handle the case where coqc for the makefile is different
            rtn["passing_coqc"] = rtn["passing_make_coqc"]
    return rtn


def contents_without_imports(lib, **kwargs):
    v_file = filename_of_lib(lib, ext=".v", **kwargs)
    contents = get_file(v_file, **kwargs)
    if "(*" in " ".join(IMPORT_LINE_REG.findall(contents)):
        print("Warning: There are comments in your Require/Import/Export lines in %s." % v_file)
    return IMPORT_LINE_REG.sub("", contents)


def escape_lib(lib, **kwargs):
    reserved = get_reserved_modnames(kwargs["coqtop"], **kwargs)
    lib = lib.replace(".", "_DOT_").replace("-", "_DASH_")
    while lib in reserved:
        lib = "AVOID_RESERVED_" + lib
    return lib


def group_by_first_component(lib_libname_pairs):
    rtn = dict((lib.split(".")[0], []) for lib, libname in lib_libname_pairs)
    for lib, libname in lib_libname_pairs:
        split_lib = lib.split(".")
        rtn[split_lib[0]].append((".".join(split_lib[1:]), libname))
    return rtn


def nest_iter_up_to(iterator):
    so_far = []
    for i in iterator:
        so_far.append(i)
        yield tuple(so_far)


def construct_import_list(import_libs, import_all_directories=False, **kwargs):
    """Takes a list of library names, and returns a list of imports in an order that should have modules representing files at the end.  If import_all_directories is true, then the resulting imports should handle semi-absolute constants, and not just fully absolute or fully relative ones."""

    def escape_lib_local(l):
        return escape_lib(l, **kwargs)

    if import_all_directories:
        lib_components_list = [
            (libname, tuple(reversed(list(nest_iter_up_to(map(escape_lib_local, libname.split("."))))[:-1])))
            for libname in import_libs
        ]
        ret = list(map(escape_lib_local, import_libs))
        lib_components = [
            (libname, i, max(map(len, lst)) - len(i)) for libname, lst in lib_components_list for i in lst
        ]
        for libname, components, components_left in reversed(sorted(lib_components, key=(lambda x: x[2]))):
            ret.append(escape_lib_local(libname) + "." + ".".join(map(escape_lib_local, components)))
        return ret
    else:
        return map(escape_lib_local, import_libs)


def strip_requires(contents):
    reg1 = re.compile(r"^\s*Require\s+((?:Import|Export)\s)", flags=re.MULTILINE)
    contents = reg1.sub(r"\1", contents)
    reg2 = re.compile(r"^\s*Require\s+((?!Import\s+|Export\s+)(?:[^\.]|\.(?!\s|$))+\.(?:\s|$))", flags=re.MULTILINE)
    contents = reg2.sub(r"", contents)
    reg3 = re.compile(r"^\s*(From\s+[^\s]+\s+)Require\s+((?:Import|Export)\s)", flags=re.MULTILINE)
    contents = reg3.sub(r"\1\2", contents)
    reg4 = re.compile(
        r"^\s*(From\s+[^\s]+\s+)Require\s+((?!Import\s+|Export\s+)(?:[^\.]|\.(?!\s|$))+\.(?:\s|$))", flags=re.MULTILINE
    )
    contents = reg4.sub(r"", contents)
    return contents


def get_module_name_and_lib_parts(lib, first_wrap_then_include=False, **kwargs):
    def escape_lib_local(libname):
        return escape_lib(libname, **kwargs)

    module_name = escape_lib_local(lib)
    mangled_module_name = module_name + "_WRAPPED"
    lib_parts = list(map(escape_lib_local, lib.split(".")))
    # we could actually return the same thing, that is the string
    # ('%s.%s' % (module_name, '.'.join(lib_parts))), in both cases,
    # but we choose to return the module prior to Include rather than
    # the wrapped module, when we're wrapping via include, so that we
    # have a chance of removing the Include statement later (because
    # it may not be used)
    if first_wrap_then_include:
        full_module_name = "%s.%s" % (mangled_module_name, lib_parts[-1])
    else:
        full_module_name = "%s.%s" % (module_name, ".".join(lib_parts))
    return module_name, mangled_module_name, lib_parts, full_module_name


def absolutize_and_mangle_libname(lib, first_wrap_then_include=False, **kwargs):
    module_name, mangled_module_name, lib_parts, full_module_name = get_module_name_and_lib_parts(
        lib, first_wrap_then_include=first_wrap_then_include, **kwargs
    )
    return full_module_name


def contents_as_module(
    lib,
    other_imports,
    extra_contents_inside_module: str = "",
    first_wrap_then_include=False,
    export=False,
    without_require=True,
    extra_top_header=None,
    **kwargs,
):
    import_all_directories = not absolutize_has_all_constants(kwargs["absolutize"])
    if import_all_directories and not export:
        # N.B. This strategy does not work with the Include strategy
        # that we use to fix
        # https://github.com/JasonGross/coq-tools/issues/67, so we disable it
        first_wrap_then_include = False
        transform_base = lambda x: (escape_lib(x, **kwargs) + "." + x if is_local_import(x, **kwargs) else x)
    else:
        transform_base = lambda x: x
    v_name = filename_of_lib(lib, ext=".v", **kwargs)
    contents = get_file(v_name, transform_base=transform_base, **kwargs)
    if without_require:
        contents = strip_requires(contents)
    kwargs["log"](contents, level=3)
    module_name, mangled_module_name, lib_parts, _ = get_module_name_and_lib_parts(
        lib, first_wrap_then_include=first_wrap_then_include, **kwargs
    )
    # import the top-level wrappers
    if len(other_imports) > 0 and not export:
        # we need to import the contents in the correct order.  Namely, if we have a module whose name is also the name of a directory (in the same folder), we want to import the file first.
        for imp in reversed(
            construct_import_list(other_imports, import_all_directories=import_all_directories, **kwargs)
        ):
            contents = "Import %s.\n%s" % (imp, contents)
    # insert extra_top_header, e.g., Import Coq.Init.Prelude., at the top of the file
    if extra_top_header:
        contents = extra_top_header + "\n" + contents
    # wrap the contents in directory modules
    maybe_export = "Export " if export else ""
    if extra_contents_inside_module:
        contents = extra_contents_inside_module + "\n" + contents
    early_contents = ""
    if first_wrap_then_include:  # works around https://github.com/JasonGross/coq-tools/issues/67
        early_contents, contents = contents, "Include %s.%s." % (mangled_module_name, lib_parts[-1])
        early_contents = "Module %s.\n%s\nEnd %s.\n" % (lib_parts[-1], early_contents, lib_parts[-1])
        early_contents = "Module %s.\n%s\nEnd %s.\n" % (mangled_module_name, early_contents, mangled_module_name)
    contents = "Module %s.\n%s\nEnd %s.\n" % (lib_parts[-1], contents, lib_parts[-1])
    for name in reversed(lib_parts[:-1]):
        contents = "Module %s%s.\n%s\nEnd %s.\n" % (maybe_export, name, contents, name)
    contents = "Module %s%s.\n%s\nEnd %s.\n" % (maybe_export, module_name, contents, module_name)
    return early_contents + contents


def normalize_requires(filename, recursive_requires_explicit: bool = True, **kwargs):
    """Return the contents of filename, with all [Require]s split out and ordered at the top.

    Preserve any leading whitespace/comments.
    """
    if filename[-2:] != ".v":
        filename += ".v"
    kwargs = fill_kwargs(kwargs)
    lib = lib_of_filename(filename, **kwargs)
    all_imports = run_maybe_recursively_get_imports(lib, recursively=recursive_requires_explicit, **kwargs)

    v_name = filename_of_lib(lib, ext=".v", **kwargs)
    contents = get_file(v_name, **kwargs)
    header, contents = split_leading_comments_and_whitespace(contents)
    contents = strip_requires(contents)
    contents = "".join("Require %s.\n" % i for i in all_imports[:-1]) + "\n" + contents.strip() + "\n"
    return header + contents


def get_required_contents(libname, **kwargs):
    return contents_as_module(libname, other_imports=[], export=True, **fill_kwargs(kwargs))


def recursively_get_requires_from_file(filename, **kwargs):
    if filename[-2:] != ".v":
        filename += ".v"
    kwargs = fill_kwargs(kwargs)
    lib = lib_of_filename(filename, **kwargs)
    return tuple(run_recursively_get_imports(lib, **kwargs)[:-1])


def include_imports(filename, as_modules=True, absolutize=ALL_ABSOLUTIZE_TUPLE, **kwargs):
    """Return the contents of filename, with any top-level imports inlined.

    If as_modules == True, then the imports will be wrapped in modules.

    This method requires access to the coqdep program if fast == False.
    Without it, it will fall back to manual parsing of the imports,
    which may change behavior.

    >>> import tempfile, os
    >>> f = tempfile.NamedTemporaryFile(dir='.', suffix='.v', delete=False)
    >>> g = tempfile.NamedTemporaryFile(dir='.', suffix='.v', delete=False)
    >>> g_name = os.path.relpath(g.name, '.')[:-2]
    >>> f.write("  Require  Import %s Coq.Init.Logic Arith.\\n  Require  Export \tPArith\t Coq.Init.Logic.\\n  Require Bool.\\n Import Bool. (* asdf *)\\n Require Import QArith\\n  ZArith\\n  Setoid.\\nRequire Import %s.\\n Require\\n  Import\\n%s\\n\\n\t.\t(*foo*)\\n\\nInductive t := a | b.\\n\\n(*asdf*)" % (g_name, g_name, g_name))
    >>> g.write(r"Require Export Ascii String.\\n\\nInductive q := c | d.")
    >>> f.close()
    >>> g.close()
    >>> print(include_imports(f.name, as_modules=False))
    Require Import Coq.Arith.Arith Coq.Bool.Bool Coq.Init.Logic Coq.PArith.PArith Coq.QArith.QArith Coq.Setoids.Setoid Coq.ZArith.ZArith Coq.Strings.Ascii Coq.Strings.String.

    Inductive q := c | d.
    (* asdf *)


    Inductive t := a | b.

    (*asdf*)

    >>> print(include_imports(f.name, as_modules=False, fast=True))
    Require Import Arith Bool Coq.Init.Logic PArith QArith Setoid ZArith Ascii String.

    Inductive q := c | d.
    (* asdf *)


    Inductive t := a | b.

    (*asdf*)
    >>> exts = ('.v', '.v.d', '.glob', '.vo', '.o', '.cmi', '.cmxs', '.native', '.cmx', '.vok', '.vos')
    >>> names = [f.name[:-2] + ext for ext in exts] + [g.name[:-2] + ext for ext in exts]
    >>> names = [i for i in names if os.path.exists(i)]
    >>> for name in names: os.remove(name)
    """
    kwargs = fill_kwargs(kwargs)
    del kwargs["absolutize"]
    if "make_coqc" in kwargs.keys():
        kwargs["coqc"] = kwargs["make_coqc"]
    if filename[-2:] != ".v":
        filename += ".v"
    lib = lib_of_filename(filename, **kwargs)
    all_imports = recursively_get_imports(lib, **kwargs)
    remaining_imports = []
    rtn = ""
    imports_done = []
    for import_name in all_imports:
        try:
            if as_modules:
                rtn += (
                    contents_as_module(
                        import_name,
                        imports_done,
                        absolutize=absolutize,
                        without_require=True,
                        **kwargs,
                    )
                    + "\n"
                )
            else:
                rtn += contents_without_imports(import_name, absolutize=(), **kwargs) + "\n"
            imports_done.append(import_name)
        except IOError:
            remaining_imports.append(import_name)
    if len(remaining_imports) > 0:
        kwargs["log"]("remaining imports:", level=2)
        kwargs["log"](remaining_imports, level=2)
        if as_modules:
            pattern = "Require %s.\n%s"
        else:
            pattern = "Require Import %s.\n%s"
        for imp in reversed(remaining_imports):
            rtn = pattern % (imp, rtn)
    return rtn


if __name__ == "__main__":
    # if we're working in Python 3.3, we can test this file
    try:
        import doctest

        success = True
    except ImportError:
        print(
            "This is not the main file to use.\nOnly run it if you have doctest (Python 3.3+) and are testing things."
        )
        success = False
    if success:
        doctest.testmod()
