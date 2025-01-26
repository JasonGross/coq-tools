from __future__ import with_statement
import subprocess, tempfile, re, os
from .file_util import clean_v_file
from .memoize import memoize
from . import util
from .custom_arguments import (
    DEFAULT_LOG,
)

__all__ = [
    "get_coqc_version",
    "get_coqtop_version",
    "get_coqc_help",
    "get_coqc_coqlib",
    "get_coq_accepts_top",
    "get_coq_accepts_time",
    "get_coq_accepts_Q",
    "get_coq_accepts_emacs",
    "get_coq_accepts_o",
    "get_coq_accepts_compile",
    "get_coq_native_compiler_ondemand_fragment",
    "group_coq_args_split_recognized",
    "group_coq_args",
    "coq_makefile_supports_arg",
    "DEFAULT_COQTOP",
]

# {Windows,Python,coqtop} is terrible; we fail to write to (or read
# from?) coqtop.  But we can wrap it in a batch script, and it works
# fine.
DEFAULT_COQTOP = "coqtop" if os.name != "nt" else util.resource_path("coqtop.bat")


@memoize
def subprocess_Popen_memoized_helper(cmd, **kwargs):
    p = subprocess.Popen(cmd, **kwargs)
    return p.communicate(), p.returncode


def subprocess_Popen_memoized(
    cmd, stderr=subprocess.STDOUT, stdout=subprocess.PIPE, stdin=subprocess.PIPE, log=DEFAULT_LOG, **kwargs
):
    log('Running command: "%s"' % '" "'.join(cmd), level=2)
    return subprocess_Popen_memoized_helper(cmd, stderr=stderr, stdin=stdin, stdout=stdout)


def get_coqc_version(coqc_prog, **kwargs):
    (stdout, _stderr), _rc = subprocess_Popen_memoized([coqc_prog, "-q", "-v"], **kwargs)
    return (
        util.normalize_newlines(util.s(stdout).replace("The Coq Proof Assistant, version ", ""))
        .replace("\n", " ")
        .strip()
    )


def get_coqc_help(coqc_prog, **kwargs):
    (stdout, _stderr), _rc = subprocess_Popen_memoized([coqc_prog, "-q", "--help"], **kwargs)
    return util.s(stdout).strip()


def get_coqtop_version(coqtop_prog, **kwargs):
    (stdout, _stderr), _rc = subprocess_Popen_memoized([coqtop_prog, "-q"], **kwargs)
    return (
        util.normalize_newlines(util.s(stdout).replace("Welcome to Coq ", "").replace("Skipping rcfile loading.", ""))
        .replace("\n", " ")
        .strip()
    )


@memoize
def get_coq_accepts_top_helper(coqc):
    temp_file = tempfile.NamedTemporaryFile(suffix=".v", dir=".", delete=True)
    temp_file_name = temp_file.name
    (stdout, _stderr), _rc = subprocess_Popen_memoized([coqc, "-q", "-top", "Top", temp_file_name])
    temp_file.close()
    clean_v_file(temp_file_name)
    return "-top: no such file or directory" not in util.s(stdout)


def get_coq_accepts_top(coqc_prog, **kwargs):
    return get_coq_accepts_top_helper(coqc_prog)


@memoize
def get_coq_accepts_compile_helper(coqtop):
    temp_file = tempfile.NamedTemporaryFile(suffix=".v", dir=".", delete=True)
    temp_file_name = temp_file.name
    (_stdout, _stderr), rc = subprocess_Popen_memoized([coqtop, "-q", "-compile", temp_file_name])
    temp_file.close()
    clean_v_file(temp_file_name)
    return rc == 0


def get_coq_accepts_compile(coqtop_prog, **kwargs):
    return get_coq_accepts_compile_helper(coqtop_prog)


def get_coq_accepts_option(coqc_prog, option, **kwargs):
    help_text = get_coqc_help(coqc_prog, **kwargs)
    return any((option + sep) in help_text for sep in "\t ")


def get_coq_accepts_o(coqc_prog, **kwargs):
    return get_coq_accepts_option(coqc_prog, "-o", **kwargs)


def get_coq_accepts_time(coqc_prog, **kwargs):
    return get_coq_accepts_option(coqc_prog, "-time", **kwargs)


def get_coq_accepts_Q(coqc_prog, **kwargs):
    return get_coq_accepts_option(coqc_prog, "-Q", **kwargs)


def get_coq_accepts_emacs(coqc_prog, **kwargs):
    return get_coq_accepts_option(coqc_prog, "-emacs", **kwargs)


def get_coq_accepts_w(coqc_prog, **kwargs):
    return get_coq_accepts_option(coqc_prog, "-w", **kwargs)


@memoize
def get_coqc_native_compiler_ondemand_errors_helper(coqc):
    temp_file = tempfile.NamedTemporaryFile(suffix=".v", dir=".", delete=True)
    temp_file_name = temp_file.name
    (stdout, _stderr), _rc = subprocess_Popen_memoized([coqc, "-q", "-native-compiler", "ondemand", temp_file_name])
    temp_file.close()
    clean_v_file(temp_file_name)
    return any(
        v in util.s(stdout)
        for v in (
            "The native-compiler option is deprecated",
            "Native compiler is disabled",
            "native-compiler-disabled",
            "deprecated-native-compiler-option",
        )
    )


def get_coqc_native_compiler_ondemand_errors(coqc_prog, **kwargs):
    return get_coqc_native_compiler_ondemand_errors_helper(coqc_prog)


def get_coq_native_compiler_ondemand_fragment(coqc_prog, **kwargs):
    help_lines = get_coqc_help(coqc_prog, **kwargs).split("\n")
    if any("ondemand" in line for line in help_lines if line.strip().startswith("-native-compiler")):
        if get_coq_accepts_w(coqc_prog, **kwargs):
            return (
                "-w",
                "-deprecated-native-compiler-option,-native-compiler-disabled",
                "-native-compiler",
                "ondemand",
            )
        elif not get_coqc_native_compiler_ondemand_errors(coqc_prog, **kwargs):
            return ("-native-compiler", "ondemand")
    return tuple()


HELP_REG = re.compile(r"^  ([^\n]*?)(?:\t|  )", re.MULTILINE)
HELP_MAKEFILE_REG = re.compile(r"^\[(-[^\n\]]*)\]", re.MULTILINE)


def adjust_help_string(coqc_help):
    # we need to insert some spaces to make parsing easier
    for one_arg_option in ("-diffs", "-native-compiler"):
        coqc_help = re.sub(r"(\n\s*%s\s+[^\s]*)" % one_arg_option, r"\1 ", coqc_help, re.MULTILINE)
    return coqc_help


def all_help_tags(coqc_help, is_coq_makefile=False):
    coqc_help = adjust_help_string(coqc_help)
    if is_coq_makefile:
        return HELP_MAKEFILE_REG.findall(coqc_help)
    else:
        return HELP_REG.findall(coqc_help)


def get_single_help_tags(coqc_help, **kwargs):
    return tuple(
        t
        for i in all_help_tags(coqc_help, **kwargs)
        if " " not in i.replace(", ", "")
        for t in i.split(", ")
        if len(t) > 0
    )


def get_multiple_help_tags(coqc_help, **kwargs):
    result = {"-coqlib": 1, "--coqlib": 1}
    result.update(dict(
        (t.split(" ")[0], len(t.split(" ")))
        for i in all_help_tags(coqc_help, **kwargs)
        if " " in i.replace(", ", "")
        for t in re.sub(r'"[^"]*"', '""', i).split(", ")
    ))
    return result


def coq_makefile_supports_arg(coq_makefile_help):
    tags = get_multiple_help_tags(coq_makefile_help, is_coq_makefile=True)
    return any(tag == "-arg" for tag in tags.keys())


def group_coq_args_split_recognized(args, coqc_help, topname=None, is_coq_makefile=False):
    args = list(args)
    bindings = []
    unrecognized_bindings = []
    single_tags = get_single_help_tags(coqc_help, is_coq_makefile=is_coq_makefile)
    multiple_tags = get_multiple_help_tags(coqc_help, is_coq_makefile=is_coq_makefile)
    while len(args) > 0:
        if args[0] in multiple_tags.keys() and len(args) >= multiple_tags[args[0]]:
            cur_binding, args = tuple(args[: multiple_tags[args[0]]]), args[multiple_tags[args[0]] :]
            if cur_binding not in bindings:
                bindings.append(cur_binding)
        else:
            cur = tuple([args.pop(0)])
            if cur[0] not in single_tags:
                unrecognized_bindings.append(cur[0])
            elif cur not in bindings:
                bindings.append(cur)
    if topname is not None and "-top" not in [i[0] for i in bindings] and "-top" in multiple_tags.keys():
        bindings.append(("-top", topname))
    return (bindings, unrecognized_bindings)


def group_coq_args(args, coqc_help, topname=None, is_coq_makefile=False):
    bindings, unrecognized_bindings = group_coq_args_split_recognized(
        args, coqc_help, topname=topname, is_coq_makefile=is_coq_makefile
    )
    return bindings + [tuple([v]) for v in unrecognized_bindings]


def coqlib_args_of_coq_args(coqc_prog, coq_args=tuple(), **kwargs):
    grouped_args = group_coq_args(coq_args, get_coqc_help(coqc_prog, **kwargs))
    coq_args = [arg for args in grouped_args if args[0] in ("--coqlib", "-coqlib") for arg in args]
    return coq_args


def get_coqc_config(coqc_prog, coq_args=tuple(), **kwargs):
    coq_args = coqlib_args_of_coq_args(coqc_prog, coq_args, **kwargs)
    (stdout, _stderr), _rc = subprocess_Popen_memoized([coqc_prog, "-q", "-config", *coq_args], **kwargs)
    return util.normalize_newlines(util.s(stdout)).strip()


def get_coqc_coqlib(coqc_prog, **kwargs):
    return [
        line[len("COQLIB=") :]
        for line in get_coqc_config(coqc_prog, **kwargs).split("\n")
        if line.startswith("COQLIB=")
    ][0]
