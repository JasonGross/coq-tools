from __future__ import print_function, with_statement

import glob
import os
import os.path
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import time
from collections import OrderedDict
from functools import cmp_to_key

from . import util
from .coq_version import (
    coq_makefile_supports_arg,
    get_coq_accepts_o,
    get_coqc_help,
    group_coq_args,
    group_coq_args_split_recognized,
)
from .custom_arguments import DEFAULT_LOG, LOG_ALWAYS
from .memoize import memoize
from .split_file import get_coq_statement_byte_ranges, split_coq_file_contents
from .strip_comments import strip_comments, strip_trailing_comments
from .util import cmp_compat as cmp
from .util import shlex_quote, shlex_join

__all__ = [
    "filename_of_lib",
    "lib_of_filename",
    "has_dir_binding",
    "deduplicate_trailing_dir_bindings",
    "deduplicate_trailing_dir_bindings_get_topname",
    "get_file_as_bytes",
    "get_file",
    "make_globs",
    "get_imports",
    "norm_libname",
    "recursively_get_imports",
    "IMPORT_ABSOLUTIZE_TUPLE",
    "ALL_ABSOLUTIZE_TUPLE",
    "absolutize_has_all_constants",
    "run_recursively_get_imports",
    "run_maybe_recursively_get_imports",
    "clear_libimport_cache",
    "get_byte_references_for",
    "sort_files_by_dependency",
    "get_recursive_requires",
    "get_recursive_require_names",
    "insert_references",
    "classify_require_kind",
    "REQUIRE",
    "REQUIRE_IMPORT",
    "REQUIRE_EXPORT",
    "EXPORT",
    "IMPORT",
    "get_references_from_globs",
    "split_requires_of_statements",
]

file_mtimes = {}
file_contents = {}
raw_file_contents = {}
lib_imports_fast = {}
lib_imports_slow = {}

DEFAULT_LIBNAMES = ((".", "Top"),)

IMPORT_ABSOLUTIZE_TUPLE = ("lib", "mod")
ALL_ABSOLUTIZE_TUPLE = (
    "lib",
    "proj",
    "rec",
    "ind",
    "constr",
    "def",
    "syndef",
    "class",
    "thm",
    "lem",
    "prf",
    "ax",
    "inst",
    "prfax",
    "coind",
    "scheme",
    "vardef",
    "mod",
)  # , 'modtype')

IMPORT_LINE_REG = re.compile(
    r"^\s*(?:Require\s+Import|Require\s+Export|Require|Load\s+Verbose|Load)\s+(.*?)\.(?:\s|$)",
    re.MULTILINE | re.DOTALL,
)


def warning(*objs):
    print("WARNING: ", *objs, file=sys.stderr)


def error(*objs):
    print("ERROR: ", *objs, file=sys.stderr)


def fill_kwargs(kwargs, for_makefile=False):
    rtn = {
        "libnames": DEFAULT_LIBNAMES,
        "non_recursive_libnames": tuple(),
        "ocaml_dirnames": tuple(),
        "log": DEFAULT_LOG,
        "coqc": ("coqc",),
        "coq_makefile": ("coq_makefile",),
        "coqdep": ("coqdep",),
        "use_coq_makefile_for_deps": True,
        "walk_tree": True,
        "coqc_args": tuple(),
        "cli_mapping": {
            "use_coq_makefile_for_deps": {False: ["--no-deps"]},
        },
        "coqpath_paths": tuple(),
    }
    rtn.update(kwargs)
    if for_makefile:
        if "make_coqc" in rtn.keys():  # handle the case where coqc for the makefile is different
            rtn["coqc"] = rtn["make_coqc"]
        if "passing_make_coqc" in rtn.keys():  # handle the case where coqc for the makefile is different
            rtn["passing_coqc"] = rtn["passing_make_coqc"]
    return rtn


def safe_kwargs(kwargs):
    for k, v in list(kwargs.items()):
        if isinstance(v, list):
            kwargs[k] = tuple(v)
    return dict((k, v) for k, v in kwargs.items() if not isinstance(v, dict))


def fix_path(filename):
    return filename.replace("\\", "/")


def absolutize_has_all_constants(absolutize_tuple):
    """Returns True if absolutizing the types of things mentioned by the tuple is enough to ensure that we only use absolute names"""
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


def filenames_of_lib_helper(lib, libnames, non_recursive_libnames, ext):
    for physical_name, logical_name in list(libnames) + list(non_recursive_libnames):
        if lib.startswith(libname_with_dot(logical_name)):
            cur_lib = lib[len(libname_with_dot(logical_name)) :]
            cur_lib = os.path.join(physical_name, cur_lib.replace(".", os.sep))
            yield fix_path(os.path.relpath(os.path.normpath(cur_lib + ext), "."))


def local_filenames_of_lib_helper(lib, libnames, non_recursive_libnames, ext):
    # is this the right thing to do?
    lib = lib.replace(".", os.sep)
    for dirpath, dirname, filenames in os_walk(".", followlinks=True):
        filename = os.path.relpath(os.path.normpath(os.path.join(dirpath, lib + ext)), ".")
        if os_path_isfile(filename):
            yield fix_path(filename)


@memoize
def filename_of_lib_helper(lib, libnames, non_recursive_libnames, ext):
    filenames = list(filenames_of_lib_helper(lib, libnames, non_recursive_libnames, ext))
    # kludge for https://github.com/coq/coq/pull/19310
    if lib.startswith("Stdlib.") and not filenames:
        filenames = list(filenames_of_lib_helper("Coq." + lib[len("Stdlib.") :], libnames, non_recursive_libnames, ext))
        if filenames:
            DEFAULT_LOG(
                "WARNING: Using Coq in place of Stdlib when resolving %s to %s."
                % (lib, ", ".join(sorted(set(filenames)))),
                level=LOG_ALWAYS,
            )
    local_filenames = list(local_filenames_of_lib_helper(lib, libnames, non_recursive_libnames, ext))
    existing_filenames = [f for f in filenames if os_path_isfile(f) or os_path_isfile(os.path.splitext(f)[0] + ".v")]
    if len(existing_filenames) > 0:
        retval = existing_filenames[0]
        if len(set(existing_filenames)) == 1:
            return retval
        else:
            DEFAULT_LOG(
                "WARNING: Multiple physical paths match logical path %s: %s.  Selecting %s."
                % (lib, ", ".join(sorted(set(existing_filenames))), retval),
                level=LOG_ALWAYS,
            )
            return retval
    if len(filenames) != 0:
        DEFAULT_LOG(
            "WARNING: One or more physical paths match logical path %s, but none of them exist: %s"
            % (lib, ", ".join(filenames)),
            level=LOG_ALWAYS,
        )
    if len(local_filenames) > 0:
        retval = local_filenames[0]
        if len(local_filenames) == 1:
            return retval
        else:
            DEFAULT_LOG(
                "WARNING: Multiple local physical paths match logical path %s: %s.  Selecting %s."
                % (lib, ", ".join(local_filenames), retval),
                level=LOG_ALWAYS,
            )
            return retval
    if len(filenames) > 0:
        retval = filenames[0]
        if len(set(filenames)) == 1:
            return retval
        else:
            DEFAULT_LOG(
                "WARNING: Multiple non-existent physical paths match logical path %s: %s.  Selecting %s."
                % (lib, ", ".join(sorted(set(filenames))), retval),
                level=LOG_ALWAYS,
            )
            return retval
    return fix_path(os.path.relpath(os.path.normpath(lib.replace(".", os.sep) + ext), "."))


def filename_of_lib(lib, ext=".v", **kwargs):
    kwargs = fill_kwargs(kwargs)
    return filename_of_lib_helper(
        lib,
        libnames=tuple(kwargs["libnames"]),
        non_recursive_libnames=tuple(kwargs["non_recursive_libnames"]),
        ext=ext,
    )


@memoize
def lib_of_filename_helper(filename, libnames, non_recursive_libnames, exts):
    filename = os.path.relpath(os.path.normpath(filename), ".")
    for ext in exts:
        if filename.endswith(ext):
            filename = filename[: -len(ext)]
            break
    for physical_name, logical_name in (
        (os.path.relpath(os.path.normpath(phys), "."), libname_with_dot(logical))
        for phys, logical in list(libnames) + list(non_recursive_libnames)
    ):
        filename_rel = os.path.relpath(filename, physical_name)
        if not filename_rel.startswith(".." + os.sep) and not os.path.isabs(filename_rel):
            return (filename, logical_name + filename_rel.replace(os.sep, "."))
    if filename.startswith(".." + os.sep) and not os.path.isabs(filename):
        filename = os.path.abspath(filename)
    return (filename, filename.replace(os.sep, "."))


DEFAULT_LIB_FILENAME_EXTS = (".v", ".glob")


def lib_of_filename(filename, exts=DEFAULT_LIB_FILENAME_EXTS, **kwargs):
    kwargs = fill_kwargs(kwargs)
    filename, libname = lib_of_filename_helper(
        filename,
        libnames=tuple(kwargs["libnames"]),
        non_recursive_libnames=tuple(kwargs["non_recursive_libnames"]),
        exts=exts,
    )
    #    if '.' in filename:
    #        # TODO: Do we still need this warning?
    #        kwargs['log']("WARNING: There is a dot (.) in filename %s; the library conversion probably won't work." % filename)
    return libname


DUMMY_TOPNAME = "DUMMY TOPNAME"


def adjust_dummy_topname_binding(filename, bindings, dummy_topname=DUMMY_TOPNAME):
    if filename is None:
        return tuple(bindings)
    _, topname = lib_of_filename_helper(
        filename,
        libnames=tuple(tuple(i[1:]) for i in bindings if i[0] == "-R"),
        non_recursive_libnames=tuple(tuple(i[1:]) for i in bindings if i[0] == "-Q"),
        exts=DEFAULT_LIB_FILENAME_EXTS,
    )
    if topname.startswith("."):  # absolute path, will give other errors
        topname = os.path.splitext(os.path.basename(filename))[0]
    topname = topname.replace("-", "_DASH_")
    return tuple((("-top", topname) if i == ("-top", dummy_topname) else i) for i in bindings)


def has_dir_binding(args, coqc_help, file_name=None):
    return any(i[0] in ("-R", "-Q") for i in group_coq_args(args, coqc_help))


def deduplicate_trailing_dir_bindings_get_topname(args, coqc_help, coq_accepts_top, file_name=None, topname=None):
    kwargs = dict()
    if topname is None:
        topname = DUMMY_TOPNAME
    if file_name is not None:
        kwargs["topname"] = topname
    bindings = group_coq_args(args, coqc_help, **kwargs)
    ret = []
    for binding in adjust_dummy_topname_binding(file_name, bindings):
        if binding[0] == "-top":
            topname = binding[1]
        if coq_accepts_top or binding[0] != "-top":
            ret.extend(binding)
    return tuple(ret), topname


def deduplicate_trailing_dir_bindings(args, coqc_help, coq_accepts_top, file_name=None, topname=None):
    ret, _topname = deduplicate_trailing_dir_bindings_get_topname(
        args, coqc_help, coq_accepts_top, file_name=file_name, topname=topname
    )
    return ret


def is_local_import(libname, **kwargs):
    """Returns True if libname is an import to a local file that we can discover and include, and False otherwise"""
    return os.path.isfile(filename_of_lib(libname, **kwargs))


def get_raw_file_as_bytes(filename, **kwargs):
    kwargs = fill_kwargs(kwargs)
    filename_extra = "" if os.path.isabs(filename) else " (%s)" % os.path.abspath(filename)
    kwargs["log"]("getting %s%s" % (filename, filename_extra))
    with open(filename, "rb") as f:
        contents = f.read()
    kwargs["log"](
        "====== Contents of %s%s ======\n%s\n==================\n"
        % (filename, filename_extra, contents.decode("utf-8")),
        level=4,
    )
    return contents


def get_raw_file(*args, **kwargs):
    return util.normalize_newlines(get_raw_file_as_bytes(*args, **kwargs).decode("utf-8"))


def list_endswith(ls, suffix):
    return len(suffix) <= len(ls) and ls[-len(suffix) :] == suffix


# code, endswith is string
@memoize
def constr_name_endswith(code, endswith):
    first_word = code.split(" ")[0].split(".")
    endswith = endswith.split(" ")[-1].split(".")
    return list_endswith(first_word, endswith)


# before, after are both strings
def move_strings_once(before, after, possibility, relaxed=False):
    for i in possibility:
        if before[-len(i) :] == i:
            return before[: -len(i)], before[-len(i) :] + after
    if relaxed:  # allow no matches
        return before, after
    else:
        return None, None


# before, after are both strings
def move_strings_pre(before, after, possibility):
    while len(before) > 0:
        new_before, new_after = move_strings_once(before, after, possibility)
        if new_before is None or new_after is None:
            return before, after
        before, after = new_before, new_after
    return (before, after)


# before, after are both strings
def move_function(before, after, get_len):
    while len(before) > 0:
        n = get_len(before)
        if n is None or n <= 0:
            return before, after
        before, after = before[:-n], before[n:] + after
    return before, after


# before, after are both strings
def move_strings(before, after, *possibilities):
    for possibility in possibilities:
        before, after = move_strings_pre(before, after, possibility)
    return before, after


# before, after are both strings
def move_space(before, after):
    return move_strings(before, after, "\n\t\r ")


# before, after are both strings
def move_comments_and_space(before, after):
    # TODO: this method is pretty inefficient, because it parses the entire string
    whitespace = "\n\t\r "
    before_without_trailing_comments_and_space = strip_trailing_comments(before, whitespace).rstrip(whitespace)
    i = len(before_without_trailing_comments_and_space)
    return before[:i], before[i:] + after


# before, after are both strings
def move_comments_and_space_and_import_categories(before, after):
    # TODO: this method is very inefficient, because it repeatedly parses the entire prefix to move comments and space
    before, after = move_comments_and_space(before, after)
    if len(before) == 0 or before[-1] != ")":  # no import category
        return before, after
    before, after = before[:-1], before[-1] + after
    level = 1
    while level > 0:
        if len(before) == 0:
            return None, None
        before, after = move_comments_and_space(before, after)
        if len(before) == 0:
            return None, None
        if before[-1] == ")":
            level += 1
        elif before[-1] == "(":
            level -= 1
        before, after = before[:-1], before[-1] + after
    before, after = move_comments_and_space(before, after)
    # optional negation of import categories
    before, after = move_strings_once(before, after, ("-",), relaxed=True)
    before, after = move_comments_and_space(before, after)
    return before, after


# uses byte locations
def remove_from_require_before(contents, location):
    """removes "From ... " from things like "From ... Require ..." """
    assert contents is bytes(contents)
    before, after = contents[:location].decode("utf-8"), contents[location:].decode("utf-8")
    before, after = move_comments_and_space_and_import_categories(before, after)
    if before is None or after is None:
        return contents
    before, after = move_strings_once(before, after, ("Import", "Export"), relaxed=True)
    before, after = move_comments_and_space(before, after)
    before, after = move_strings_once(before, after, ("Require",), relaxed=False)
    if before is None or after is None:
        return contents
    before, _ = move_comments_and_space(before, after)
    before, _ = move_function(before, after, (lambda b: 1 if b[-1] not in " \t\r\n" else None))
    if before is None:
        return contents
    before, _ = move_comments_and_space(before, after)
    before, _ = move_strings_once(before, after, ("From",), relaxed=False)
    if before is None:
        return contents
    return (before + after).encode("utf-8")


# returns locations as bytes
def get_references_from_globs(globs):
    all_globs = set(
        (int(start), int(end) + 1, loc, append, ty.strip())
        for start, end, loc, append, ty in re.findall(
            "^R([0-9]+):([0-9]+) ([^ ]+) <> ([^ ]+) ([^ ]+)$", globs, flags=re.MULTILINE
        )
    )
    return tuple(sorted(all_globs, key=(lambda x: x[0]), reverse=True))


# contents should be bytes
def is_absolutizable_mod_reference(contents, reference):
    start, end, loc, append, ty = reference
    if ty != "mod":
        return False
    cur_statement = re.sub(
        r"\s+",
        " ",
        ([""] + split_coq_file_contents(contents[:start].decode("utf-8")))[-1],
    ).strip()
    return cur_statement.split(" ")[0] in ("Import", "Export", "Include")


# we absolutize requires, etc, without assuming that we have access to
# the statement-splitting of the file; this is required for inlining
# installed files, where we can't guarantee that we know how to run
# coqc on the file.
#
# contents should be bytes; globs should be string
def update_one_with_glob(contents, ref, absolutize, libname, transform_base=(lambda x: x), **kwargs):
    assert contents is bytes(contents)
    kwargs = fill_kwargs(kwargs)
    start, end, loc, append, ty = ref
    cur_code = contents[start:end].decode("utf-8")
    rep = transform_base(loc) + ("." + append if append != "<>" else "")
    rep_orig = loc + ("." + append if append != "<>" else "")
    if ty not in absolutize or loc == libname:
        kwargs["log"](
            "Skipping %s at %d:%d (%s), location %s %s" % (ty, start, end, cur_code, loc, append),
            level=2,
        )
    # sanity check for correct replacement, to skip things like record builder notation
    elif append != "<>" and not constr_name_endswith(cur_code, append):
        kwargs["log"](
            "Skipping invalid %s at %d:%d (%s), location %s %s" % (ty, start, end, cur_code, loc, append),
            level=2,
        )
    elif ty == "mod" and not is_absolutizable_mod_reference(contents, ref):
        kwargs["log"](
            "Skipping non-absolutizable module reference %s at %d:%d (%s), location %s %s"
            % (ty, start, end, cur_code, loc, append),
            level=2,
        )
    elif not constr_name_endswith(rep_orig, cur_code):
        kwargs["log"](
            "Skipping invalid %s at %d:%d (%s) (expected %s), location %s %s"
            % (ty, start, end, cur_code, rep_orig, loc, append),
            level=2,
        )
    else:  # ty in absolutize and loc != libname
        kwargs["log"]("Qualifying %s %s to %s" % (ty, cur_code, rep), level=2, max_level=3)
        kwargs["log"](
            "Qualifying %s %s to %s from R%s:%s %s <> %s %s" % (ty, cur_code, rep, start, end, loc, append, ty),
            level=3,
        )
        contents = contents[:start] + rep.encode("utf-8") + contents[end:]
        contents = remove_from_require_before(contents, start)

    return contents


def update_with_glob(contents, globs, *args, **kwargs):
    assert contents is bytes(contents)
    for ref in get_references_from_globs(globs):
        new_contents = update_one_with_glob(contents, ref, *args, **kwargs)
        if new_contents != contents:
            last_successful_ref = ref
        contents = new_contents
    return contents


def get_all_v_files(directory, exclude=tuple()):
    all_files = []
    exclude = [os.path.normpath(i) for i in exclude]
    for dirpath, dirnames, filenames in os.walk(directory):
        all_files += [
            os.path.relpath(name, ".")
            for name in glob.glob(os.path.join(dirpath, "*.v"))
            if os.path.normpath(name) not in exclude
        ]
    return tuple(map(fix_path, all_files))


# we want to run on passing arguments if we're running in
# passing/non-passing mode, cf
# https://github.com/JasonGross/coq-tools/issues/57.  Hence we return
# the passing version iff passing_coqc is passed.
# However, if the passing coqc does not have built vo files,
# as will be the case on Coq's CI (cf https://github.com/JasonGross/coq-tools/issues/296),
# we also allow the caller to force the failing version, so that we can get the longest .glob file.
def get_maybe_passing_arg(kwargs, key, force_failing: bool = False):
    if not force_failing and kwargs.get("passing_coqc"):
        return kwargs["passing_" + key]
    return kwargs[key]


def get_keep_error_reversed(mkfile, **kwargs):
    # old versions of coq_makefile reversed the meaning of KEEP_ERROR,
    # see https://github.com/coq/coq/pull/15880.  So we need to not
    # pass it if the logic is reversed, but we should pass it
    # otherwise, because we need .glob files even if coqc fails.
    return r"""ifneq (,$(KEEP_ERROR))
.DELETE_ON_ERROR:
""" in get_raw_file(
        mkfile, **kwargs
    )


# these arguments prevent generation of .glob files
BAD_ARGS_FOR_MAKE_GLOB = ("-vio", "-vos", "-vok")


def run_coq_makefile_and_make(v_files, targets, **kwargs):
    kwargs = safe_kwargs(fill_kwargs(kwargs, for_makefile=True))
    f = tempfile.NamedTemporaryFile(suffix=".coq", prefix="Makefile", dir=".", delete=False)
    mkfile = os.path.basename(f.name)
    f.close()
    assert isinstance(kwargs["coq_makefile"], tuple), kwargs["coq_makefile"]
    assert isinstance(kwargs["coqdep"], tuple), kwargs["coqdep"]
    assert isinstance(get_maybe_passing_arg(kwargs, "coqc"), tuple), get_maybe_passing_arg(kwargs, "coqc")
    cmds = [
        *kwargs["coq_makefile"],
        "COQC",
        "=",
        shlex_join(get_maybe_passing_arg(kwargs, "coqc")),
        "COQDEP",
        "=",
        shlex_join(kwargs["coqdep"]),
        "-o",
        mkfile,
    ]
    for physical_name, logical_name in get_maybe_passing_arg(kwargs, "libnames"):
        cmds += [
            "-R",
            physical_name,
            (logical_name if logical_name not in ("", "''", '""') else '""'),
        ]
    for physical_name, logical_name in get_maybe_passing_arg(kwargs, "non_recursive_libnames"):
        cmds += [
            "-Q",
            physical_name,
            (logical_name if logical_name not in ("", "''", '""') else '""'),
        ]
    for dirname in get_maybe_passing_arg(kwargs, "ocaml_dirnames"):
        cmds += ["-I", dirname]
    coq_makefile_help = get_coqc_help(kwargs["coq_makefile"], **kwargs)
    grouped_args, unrecognized_args = group_coq_args_split_recognized(
        get_maybe_passing_arg(kwargs, "coqc_args"),
        coq_makefile_help,
        is_coq_makefile=True,
    )
    for args in grouped_args:
        cmds.extend(args)
    if unrecognized_args:
        if coq_makefile_supports_arg(coq_makefile_help):
            skip_next = False
            for arg in unrecognized_args:
                # coq_makefile should never get -top{,file}; this case
                # will happen if the underlying coqc does not support
                # -top, but coqtop does, and we're running coqtop as
                # coqc
                if arg in ("-top", "-topfile"):
                    skip_next = True
                elif skip_next:
                    skip_next = False
                elif arg not in BAD_ARGS_FOR_MAKE_GLOB:
                    cmds += ["-arg", shlex_quote(arg)]
        else:
            kwargs["log"]("WARNING: Unrecognized arguments to coq_makefile: %s" % repr(unrecognized_args))
    cmds += list(map(fix_path, v_files))
    kwargs["log"](shlex_join(cmds))
    try:
        p_make_makefile = subprocess.Popen(cmds, stdout=subprocess.PIPE)
        (stdout, stderr) = p_make_makefile.communicate()
    except OSError as e:
        error("When attempting to run coq_makefile:")
        error(repr(e))
        error("Failed to run coq_makefile using command line:")
        error(shlex_join(cmds))
        error("Perhaps you forgot to add COQBIN to your PATH?")
        error("Try running coqc on your files to get .glob files, to work around this.")
        sys.exit(1)
    keep_error_fragment = [] if get_keep_error_reversed(mkfile, **kwargs) else ["KEEP_ERROR=1"]
    make_cmds = ["make", "-k", "-f", mkfile] + keep_error_fragment + targets
    kwargs["log"](shlex_join(make_cmds))
    try:
        p_make = subprocess.Popen(
            make_cmds,
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
        )
        p_make_stdout, p_make_stderr = p_make.communicate()
        return p_make_stdout.decode("utf-8")
    finally:
        for filename in (
            mkfile,
            mkfile + ".conf",
            mkfile + ".d",
            ".%s.d" % mkfile,
            ".coqdeps.d",
        ):
            if os.path.exists(filename):
                os.remove(filename)


def make_one_glob_file_helper(v_file, clobber_glob_on_failure: bool = True, force_failing: bool = False, **kwargs):
    kwargs = safe_kwargs(fill_kwargs(kwargs))
    coqc_prog = get_maybe_passing_arg(kwargs, "coqc", force_failing=force_failing)
    coqpath_paths = get_maybe_passing_arg(kwargs, "coqpath_paths", force_failing=force_failing)
    assert isinstance(coqc_prog, tuple), coqc_prog
    cmds = [*coqc_prog, "-q"]
    for physical_name, logical_name in get_maybe_passing_arg(kwargs, "libnames", force_failing=force_failing):
        cmds += [
            "-R",
            physical_name,
            (logical_name if logical_name not in ("", "''", '""') else '""'),
        ]
    for physical_name, logical_name in get_maybe_passing_arg(
        kwargs, "non_recursive_libnames", force_failing=force_failing
    ):
        cmds += [
            "-Q",
            physical_name,
            (logical_name if logical_name not in ("", "''", '""') else '""'),
        ]
    for dirname in get_maybe_passing_arg(kwargs, "ocaml_dirnames", force_failing=force_failing):
        cmds += ["-I", dirname]
    cmds += list(get_maybe_passing_arg(kwargs, "coqc_args", force_failing=force_failing))
    v_file = fix_path(v_file)
    v_file_root, ext = os.path.splitext(v_file)
    o_file = os.path.join(tempfile.gettempdir(), os.path.basename(v_file_root) + ".vo")
    tmp_glob_file = os.path.join(tempfile.gettempdir(), os.path.basename(v_file_root) + ".glob")
    glob_file = v_file_root + ".glob"
    if get_coq_accepts_o(coqc_prog, **kwargs):
        cmds += ["-o", o_file]
    else:
        kwargs["log"](
            "WARNING: Clobbering '%s' because coqc does not support -o" % o_file,
            level=LOG_ALWAYS,
        )
    cmds += ["-dump-glob", tmp_glob_file, v_file]
    # if the file has user-contrib in it, we may try to its local paths with -R for more robustness
    extra_cmds_options = []
    v_file_in_coqpaths = [p for p in coqpath_paths if is_subdirectory_of(v_file, p)]
    # sort the paths by length of absolute path so that we try the longest paths first
    v_file_in_coqpaths.sort(key=lambda p: len(os.path.abspath(p)), reverse=True)
    for coqpath_path in v_file_in_coqpaths:
        relative_path = os.path.relpath(v_file, coqpath_path)
        first_component = fix_path(relative_path).split("/")[0]
        extra_cmds_options.append(["-R", os.path.join(coqpath_path, first_component), first_component])
    kwargs["log"](shlex_join(cmds))
    try:
        p = subprocess.Popen(cmds, stdout=subprocess.PIPE)
        stdout, stderr = p.communicate()
        for extra_cmds in extra_cmds_options:
            if p.returncode == 0:
                break
            kwargs["log"](
                "WARNING: coqc failed on '%s', retrying with extra %s" % (v_file, shlex_join(extra_cmds)),
                level=LOG_ALWAYS,
            )
            kwargs["log"](shlex_join(cmds + extra_cmds))
            p = subprocess.Popen(cmds + extra_cmds, stdout=subprocess.PIPE)
            stdout, stderr = p.communicate()
        if os.path.exists(tmp_glob_file) and (
            p.returncode == 0 or not os.path.exists(glob_file) or clobber_glob_on_failure
        ):
            if os.path.exists(glob_file):
                extra = " despite failure of coqc" if p.returncode != 0 else " because coqc succeeded"
                kwargs["log"](
                    f"WARNING: Clobbering '{glob_file}' ({os.path.getmtime(glob_file)}) from '{v_file}' ({os.path.getmtime(v_file_root+ext)}){extra}",
                    level=LOG_ALWAYS,
                )
            else:
                kwargs["log"](f"Moving '{tmp_glob_file}' to '{glob_file}'")
            try:
                # N.B. We need shutil.move rather than os.rename because the source and destination may be on different filesystems
                shutil.move(tmp_glob_file, glob_file)
            except PermissionError as e:
                kwargs["log"](
                    f"Failed to move '{tmp_glob_file}' to '{glob_file}' ({e}), assuming that '{glob_file}' is up to date"
                )
        elif os.path.exists(tmp_glob_file):
            kwargs["log"](
                f"WARNING: Not clobbering '{glob_file}' ({os.path.getmtime(glob_file)}) because coqc failed on '{v_file}' ({os.path.getmtime(v_file_root+ext)})",
                level=LOG_ALWAYS,
            )
        return stdout, stderr
    finally:
        if os.path.exists(o_file):
            os.remove(o_file)
        if os.path.exists(tmp_glob_file):
            os.remove(tmp_glob_file)


# we want to run on passing arguments if we're running in
# passing/non-passing mode, cf
# https://github.com/JasonGross/coq-tools/issues/57.  Hence we return
# the passing version iff passing_coqc is passed.
# However, if the passing coqc does not have built vo files,
# as will be the case on Coq's CI (cf https://github.com/JasonGross/coq-tools/issues/296),
# we also allow the caller to force the failing version, so that we can get the longest .glob file.
def get_glob_contents(v_file, **kwargs):
    kwargs = safe_kwargs(fill_kwargs(kwargs))
    v_file = Path(fix_path(v_file))
    glob_file = v_file.with_suffix(".glob")
    stdout, stderr = make_one_glob_file_helper(str(v_file), **kwargs)
    return (stdout, stderr), glob_file.read_text()


def make_one_glob_file(v_file, **kwargs):
    kwargs = safe_kwargs(fill_kwargs(kwargs))
    v_file = Path(fix_path(v_file))
    glob_file = v_file.with_suffix(".glob")
    (stdout_failing, stderr_failing), glob_contents_failing = get_glob_contents(
        str(v_file), force_failing=True, **kwargs
    )
    if not kwargs.get("passing_coqc"):
        return (stdout_failing, stderr_failing), (None, None)
    (stdout_passing, stderr_passing), glob_contents_passing = get_glob_contents(
        str(v_file), force_failing=False, **kwargs
    )
    if glob_contents_failing != glob_contents_passing:
        passing_lines = len(glob_contents_passing.splitlines())
        failing_lines = len(glob_contents_failing.splitlines())
        kwargs["log"](f"Failing .glob file:\n\n{glob_contents_failing}\n\n", level=4)
        kwargs["log"](f"Passing .glob file:\n\n{glob_contents_passing}\n\n", level=4)
        if failing_lines > passing_lines:
            kwargs["log"](
                f"Taking the failing {glob_file} file ({failing_lines} lines) because the passing version ({passing_lines} lines) is shorter"
            )
            glob_file.write_text(glob_contents_failing)
        else:
            kwargs["log"](
                f"Taking the passing {glob_file} file ({passing_lines} lines) because the failing version ({failing_lines} lines) is longer"
            )
            glob_file.write_text(glob_contents_passing)
    return (stdout_failing, stderr_failing), (stdout_passing, stderr_passing)


def is_subdirectory_of(filename, parent):
    abs_filename = os.path.normpath(os.path.abspath(filename))
    parent = os.path.normpath(os.path.abspath(parent))
    common = os.path.normpath(os.path.commonprefix([parent, abs_filename]))
    return common == parent


def is_local(filename):
    return is_subdirectory_of(filename, ".")


def remove_if_local(filename, **kwargs):
    abs_filename = os.path.abspath(filename)
    cwd = os.path.abspath(".")
    common = os.path.commonprefix([cwd, abs_filename])
    if common != cwd:
        kwargs["log"](
            "WARNING: Not removing %s (%s) because it resides in a parent (%s) of the current directory (%s)"
            % (filename, abs_filename, common, cwd)
        )
        return
    os.remove(filename)


def make_globs(logical_names, **kwargs):
    kwargs = fill_kwargs(kwargs)
    existing_logical_names = [i for i in logical_names if os.path.isfile(filename_of_lib(i, ext=".v", **kwargs))]
    if len(existing_logical_names) == 0:
        return
    filenames_vo_v_glob = [
        (
            filename_of_lib(i, ext=".vo", **kwargs),
            filename_of_lib(i, ext=".v", **kwargs),
            filename_of_lib(i, ext=".glob", **kwargs),
        )
        for i in existing_logical_names
    ]
    filenames_vo_v_glob = [
        (vo_name, v_name, glob_name)
        for vo_name, v_name, glob_name in filenames_vo_v_glob
        if not (os.path.isfile(glob_name) and os.path.getmtime(glob_name) > os.path.getmtime(v_name))
    ]
    for vo_name, v_name, glob_name in filenames_vo_v_glob:
        if os.path.isfile(glob_name) and not os.path.getmtime(glob_name) > os.path.getmtime(v_name):
            if os.path.getmtime(v_name) > time.time():
                kwargs["log"](
                    "WARNING: The file %s comes from the future! (%d > %d)"
                    % (v_name, os.path.getmtime(v_name), time.time()),
                    level=LOG_ALWAYS,
                )
            remove_if_local(glob_name, **kwargs)
        # if the .vo file already exists and is new enough, we assume
        # that all dependent .vo files also exist, and just run coqc
        # in a way that doesn't update the .vo file.  We use >= rather
        # than > because we're using .vo being new enough as a proxy
        # for the dependent .vo files existing, so we don't care as
        # much about being perfectly accurate on .vo file timing
        # (unlike .glob file timing, where we need it to be up to
        # date), and it's better to not clobber the .vo file when
        # we're unsure if it's new enough.
        ambiguous_glob_time = os.path.isfile(glob_name) and os.path.getmtime(glob_name) == os.path.getmtime(v_name)
        # We also don't want to clobber the .glob file from ambiguous non-local (e.g., installed) files if coqc fails
        if os.path.exists(vo_name) and os.path.getmtime(vo_name) >= os.path.getmtime(v_name):
            make_one_glob_file(v_name, clobber_glob_on_failure=is_local(glob_name) or not ambiguous_glob_time, **kwargs)
    filenames_vo_v_glob = [
        (vo_name, v_name, glob_name)
        for vo_name, v_name, glob_name in filenames_vo_v_glob
        if not (os.path.exists(vo_name) and os.path.getmtime(vo_name) >= os.path.getmtime(v_name))
    ]
    filenames_v = [v_name for vo_name, v_name, glob_name in filenames_vo_v_glob]
    filenames_glob = [glob_name for vo_name, v_name, glob_name in filenames_vo_v_glob]
    if len(filenames_vo_v_glob) == 0:
        return
    extra_filenames_v = list(
        get_all_v_files(".", filenames_v) if kwargs["use_coq_makefile_for_deps"] and kwargs["walk_tree"] else []
    )
    all_filenames_v = filenames_v + extra_filenames_v

    if len(all_filenames_v) <= 1 or not kwargs["use_coq_makefile_for_deps"]:
        if len(all_filenames_v) > 1:
            kwargs["log"](
                "WARNING: Making globs for %s separately without coq_makefile for dependencies, as requested"
                % ", ".join(all_filenames_v)
            )
        for v_name in all_filenames_v:
            v_name_base, _ext = os.path.splitext(v_name)
            glob_name = v_name_base + ".glob"
            ambiguous_glob_time = os.path.isfile(glob_name) and os.path.getmtime(glob_name) == os.path.getmtime(v_name)
            make_one_glob_file(
                v_name, clobber_glob_on_failure=is_local(glob_name) and not ambiguous_glob_time, **kwargs
            )
    else:
        stdouterr_make = run_coq_makefile_and_make(
            tuple(sorted(filenames_v + extra_filenames_v)), filenames_glob, **kwargs
        )
        if "Argument list too long" in stdouterr_make and re.search(
            r"No rule to make target '.*\.glob'", stdouterr_make
        ):
            kwargs["log"](
                "WARNING: Making globs may not have succeeded, consider passing "
                + kwargs["cli_mapping"]["use_coq_makefile_for_deps"][False][0]
            )


def get_glob_file_for(filename, update_globs=False, allow_ambiguous_glob_files: bool = True, **kwargs):
    kwargs = fill_kwargs(kwargs)
    filename = fix_path(filename)
    if filename[-2:] != ".v":
        filename += ".v"
    libname = lib_of_filename(filename, **kwargs)
    globname = filename[:-2] + ".glob"
    if not os.path.exists(filename):
        return None
    if filename not in raw_file_contents.keys() or file_mtimes[filename] < os.stat(filename).st_mtime:
        raw_file_contents[filename] = get_raw_file_as_bytes(filename, **kwargs)
        file_contents[filename] = {}
        file_mtimes[filename] = os.stat(filename).st_mtime
    if update_globs:
        if file_mtimes[filename] > time.time():
            kwargs["log"](
                "WARNING: The file %s comes from the future! (%d > %d)"
                % (filename, file_mtimes[filename], time.time()),
                level=LOG_ALWAYS,
            )
        if time.time() - file_mtimes[filename] < 2:
            kwargs["log"](
                "NOTE: The file %s is very new (%d, %d seconds old), delaying until it's a bit older"
                % (filename, file_mtimes[filename], time.time() - file_mtimes[filename])
            )
        # delay until the .v file is old enough that a .glob file will be considered newer
        # if we just wait until they're not equal, we apparently get issues like https://gitlab.com/Zimmi48/coq/-/jobs/535005442
        while time.time() - file_mtimes[filename] < 2:
            time.sleep(0.1)
        make_globs([libname], **kwargs)
    if os.path.isfile(globname):
        if os.stat(globname).st_mtime > file_mtimes[filename]:
            return get_raw_file(globname, **kwargs)
        elif allow_ambiguous_glob_files and os.stat(globname).st_mtime == file_mtimes[filename]:
            kwargs["log"]("WARNING: Ambiguous .glob file %s for %s (%d)" % (globname, filename, file_mtimes[filename]))
            return get_raw_file(globname, **kwargs)
        else:
            kwargs["log"](
                "WARNING: Assuming that %s is not a valid reflection of %s because %s is newer (%d >= %d)"
                % (
                    globname,
                    filename,
                    filename,
                    file_mtimes[filename],
                    os.stat(globname).st_mtime,
                )
            )
    return None


def get_byte_references_for(filename, types=None, appends=None, **kwargs):
    globs = get_glob_file_for(filename, **kwargs)
    if globs is None:
        return None
    references = get_references_from_globs(globs)
    return tuple(
        (start, end, loc, append, ty)
        for start, end, loc, append, ty in references
        if (types is None or ty in types) and (appends is None or append in appends)
    )


def get_file_as_bytes(
    filename, absolutize=("lib",), update_globs=False, mod_remap=dict(), transform_base=(lambda x: x), **kwargs
):
    kwargs = fill_kwargs(kwargs)
    filename = fix_path(filename)
    if filename[-2:] != ".v":
        filename += ".v"
    libname = lib_of_filename(filename, **kwargs)
    globname = filename[:-2] + ".glob"
    if filename not in raw_file_contents.keys() or file_mtimes[filename] < os.stat(filename).st_mtime:
        raw_file_contents[filename] = get_raw_file_as_bytes(filename, **kwargs)
        file_contents[filename] = {}
        file_mtimes[filename] = os.stat(filename).st_mtime
    if len(mod_remap.keys()) > 0:
        absolutize = list(set(list(absolutize) + ["mod"]))
    key = (tuple(sorted(absolutize)), tuple(sorted(list(mod_remap.items()))))
    if key not in file_contents[filename].keys():
        if len(absolutize) > 0 or len(mod_remap.keys()) > 0:
            globs = get_glob_file_for(filename, update_globs=update_globs, **kwargs)
            if globs is not None:
                file_contents[filename][key] = update_with_glob(
                    raw_file_contents[filename],
                    globs,
                    absolutize,
                    libname,
                    transform_base=(lambda x: mod_remap.get(x, transform_base(x))),
                    **kwargs,
                )
    return file_contents[filename].get(key, raw_file_contents[filename])


# returns string, newlines normalized
def get_file(*args, **kwargs):
    return util.normalize_newlines(get_file_as_bytes(*args, **kwargs).decode("utf-8"))


# this is used to mark which statements are tied to which requires
def insert_references(contents, ranges, references, types=("lib",), appends=("<>",), **kwargs):
    assert contents is bytes(contents)
    ret = []
    prev = 0
    bad = [
        (start, end, loc, append, ty)
        for start, end, loc, append, ty in references
        if append not in appends or ty not in types
    ]
    if bad:
        kwargs["log"](
            "Invalid glob entries: %s"
            % "\n".join("R%d:%d %s <> %s %s" % (start, end, loc, append, ty) for start, end, loc, append, ty in bad)
        )
    for start, finish in ranges:
        if prev < start:
            ret.append((contents[prev:start], tuple()))
        bad = [
            (rstart, rend, loc, append, ty)
            for rstart, rend, loc, append, ty in references
            if (start <= rstart or rend <= finish)
            and not ((start <= rstart and rend <= finish) or finish <= rstart or rend <= start)
        ]
        if bad:
            kwargs["log"](
                "Invalid glob entries partially overlapping (%d, %d]: %s"
                % (
                    start,
                    finish,
                    "\n".join(
                        "R%d:%d %s <> %s %s" % (start, end, loc, append, ty) for start, end, loc, append, ty in bad
                    ),
                )
            )

        cur_references = tuple(
            (rstart - start, rend - start, loc, append, ty)
            for rstart, rend, loc, append, ty in references
            if start <= rstart and rend <= finish
        )
        ret.append((contents[start:finish], cur_references))
        prev = finish
    if prev < len(contents):
        ret.append((contents[prev:], tuple()))
    return tuple(ret)


def get_file_statements_insert_references(filename, **kwargs):
    ranges = get_coq_statement_byte_ranges(filename, **kwargs)
    contents = get_file_as_bytes(filename, **kwargs)
    refs = get_byte_references_for(filename, **kwargs)
    if refs is None:
        return None
    return insert_references(contents, ranges, refs, **kwargs)


def remove_after_first_range(text_as_bytes, ranges):
    if ranges:
        start = min((r[0] for r in ranges))
        return text_as_bytes[:start]
    else:
        return text_as_bytes


REQUIRE, REQUIRE_IMPORT, REQUIRE_EXPORT, EXPORT, IMPORT = (
    "REQUIRE",
    "REQUIRE IMPORT",
    "REQUIRE EXPORT",
    "EXPORT",
    "IMPORT",
)


def classify_require_kind(text_as_bytes, ranges):
    """cassifies the kind of require statement

    >>> res = {REQUIRE:'R', REQUIRE_IMPORT:'RI', REQUIRE_EXPORT:'RE', EXPORT:'E', IMPORT:'I', None:None}
    >>> print(res[classify_require_kind(b'From Coq Require Export ZArith.ZArith.', ((24, 37, 'Coq.ZArith.ZArith'),))])
    RE
    """
    prefix = (
        strip_comments(
            re.sub(
                r"\s+",
                " ",
                remove_after_first_range(text_as_bytes, ranges).decode("utf-8"),
            )
        ).strip()
        + " "
    )
    is_require = "Require " in prefix
    if "Import " in prefix:
        return REQUIRE_IMPORT if is_require else IMPORT
    if "Export " in prefix:
        return REQUIRE_EXPORT if is_require else EXPORT
    return REQUIRE if is_require else None


def split_requires_of_statements(annotated_contents, types=("lib",), appends=("<>",), **kwargs):
    already_required = set()
    prefix, postfix = "\nRequire ", "."
    for statement, references in annotated_contents:
        statement_str = statement.decode("utf-8")
        if not references:
            yield (statement, references)
            continue
        rkind = classify_require_kind(statement, references)
        if rkind not in (REQUIRE, REQUIRE_IMPORT, REQUIRE_EXPORT) or (len(references) == 1 and rkind == REQUIRE):
            yield (statement, references)
            continue
        remaining_references = []
        emitted_require = False
        for start, end, loc, append, ty in references:
            if ty in types and append in appends:
                if loc not in already_required:
                    already_required.add(loc)
                    emitted_require = True
                    yield (
                        (prefix + loc + postfix).encode("utf-8"),
                        (len(prefix), len(prefix) - start + end, loc, append, ty),
                    )
            else:
                remaining_references.append((start - len("Require "), end - len("Require "), loc, append, ty))
        if rkind == REQUIRE:
            continue
        statement_str = re.sub(r"Require\s", "", statement_str, count=1)
        if emitted_require and not re.match(r"\s", statement_str[0]):
            yield ("\n".encode("utf-8"), tuple())  # we need an extra newline
        yield (statement_str.encode("utf-8"), tuple(remaining_references))


def get_require_dict(lib, update_globs=True, **kwargs):
    kwargs = fill_kwargs(kwargs)
    lib = norm_libname(lib, **kwargs)
    v_name = filename_of_lib(lib, ext=".v", **kwargs)
    if lib not in lib_imports_slow.keys():
        globs = get_byte_references_for(v_name, types=("lib",), appends=("<>",), update_globs=update_globs, **kwargs)
        if globs is not None:
            lib_imports_slow[lib] = {}
            for start, end, name, append, ty in reversed(globs):
                name = norm_libname(name, **kwargs)
                if name not in lib_imports_slow[lib].keys():
                    lib_imports_slow[lib][name] = []
                lib_imports_slow[lib][name].append((start, end))
            for name in lib_imports_slow[lib].keys():
                lib_imports_slow[lib][name] = tuple(lib_imports_slow[lib][name])
    return lib_imports_slow.get(lib, {})


def get_require_names(lib, **kwargs):
    return tuple(sorted(get_require_dict(lib, **kwargs).keys()))


def get_require_locations(lib, **kwargs):
    return sorted(set(loc for name, locs in get_require_dict(lib, **kwargs).items() for loc in locs))


def transitively_close(d, make_new_value=(lambda x: tuple()), reflexive=True):
    updated = True
    while updated:
        updated = False
        for key in tuple(d.keys()):
            newv = set(d[key])
            if reflexive:
                newv.add(key)
            for v in tuple(newv):
                if v not in d.keys():
                    d[v] = make_new_value(v)
                newv.update(set(d[v]))
            if newv != set(d[key]):
                d[key] = newv
                updated = True
    return d


def get_recursive_requires(*libnames, **kwargs):
    reverse = kwargs.get("reverse", True)
    requires = dict((lib, get_require_names(lib, **kwargs)) for lib in libnames)
    transitively_close(
        requires,
        make_new_value=(lambda lib: get_require_names(lib, **kwargs)),
        reflexive=True,
    )

    def lcmp(l1, l2):
        l1, l2 = l1[0], l2[0]  # strip off value part
        if l1 == l2:
            return cmp(l1, l2)
        # this only works correctly if the closure is *reflexive* as
        # well as transitive, because we require that if A requires B,
        # then A must have strictly more requires than B (i.e., it
        # must include itself)
        if len(requires[l1]) != len(requires[l2]):
            return cmp(len(requires[l1]), len(requires[l2]))
        return cmp(l1, l2)

    return OrderedDict(sorted(requires.items(), key=cmp_to_key(lcmp), reverse=reverse))


def get_recursive_require_names(libname, **kwargs):
    requires = get_recursive_requires(libname, **kwargs)
    return tuple(i for i in requires.keys() if i != libname)


def sort_files_by_dependency(filenames, reverse=True, **kwargs):
    kwargs = fill_kwargs(kwargs)
    filenames = map(fix_path, filenames)
    filenames = [(filename + ".v" if filename[-2:] != ".v" else filename) for filename in filenames]
    libname_map = dict((lib_of_filename(filename, **kwargs), filename) for filename in filenames)
    requires = get_recursive_requires(*sorted(libname_map.keys()), reverse=reverse, **kwargs)
    # filter the sorted requires by the ones that were in the original
    # filenames list, and use libname_map to lookup the original
    # filename.  We could probably just map filename_of_lib over the
    # requires and keep the ones that are in the original filenames,
    # but this is more robust if there are edge cases where
    # filename_of_lib(lib_of_filename(x)) != x
    filenames = [libname_map[libname] for libname in requires.keys() if libname in libname_map.keys()]
    return filenames


def get_imports(lib, fast=False, **kwargs):
    kwargs = fill_kwargs(kwargs)
    lib = norm_libname(lib, **kwargs)
    glob_name = filename_of_lib(lib, ext=".glob", **kwargs)
    v_name = filename_of_lib(lib, ext=".v", **kwargs)
    if not fast:
        get_require_dict(lib, **kwargs)
        if lib in lib_imports_slow.keys():
            return tuple(k for k, v in sorted(lib_imports_slow[lib].items(), key=(lambda kv: kv[1])))
    # making globs failed, or we want the fast way, fall back to regexp
    if lib not in lib_imports_fast.keys():
        contents = get_file(v_name, **kwargs)
        imports_string = re.sub("\\s+", " ", " ".join(IMPORT_LINE_REG.findall(contents))).strip()
        lib_imports_fast[lib] = tuple(
            sorted(set(norm_libname(i, **kwargs) for i in imports_string.split(" ") if i != ""))
        )
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
    glob_name = filename_of_lib(lib, ext=".glob", **kwargs)
    v_name = filename_of_lib(lib, ext=".v", **kwargs)
    if os.path.isfile(v_name):
        imports = get_imports(lib, fast=fast, **kwargs)
        if not fast:
            make_globs(imports, **kwargs)
        imports_list = [recur(k, fast=fast, **kwargs) for k in imports]
        return merge_imports(tuple(map(tuple, imports_list + [[lib]])), **kwargs)
    return [lib]


def run_maybe_recursively_get_imports(lib, recursively: bool = True, **kwargs):
    recursive_imports = run_recursively_get_imports(lib, **kwargs)
    if recursively:
        return recursive_imports
    else:
        # keep the order of the recursive version, but only keep the elements in the non-recursive list
        direct_imports = run_recursively_get_imports(lib, recur=lambda lib, **_kwargs: [lib], **kwargs)
        return [lib for lib in recursive_imports if lib in direct_imports]


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
