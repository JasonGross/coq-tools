#!/usr/bin/env python3
import tempfile, sys, os, re, os.path
import glob
import traceback
from . import custom_arguments
from .argparse_compat import argparse
from .replace_imports import (
    include_imports,
    normalize_requires,
    get_required_contents,
    recursively_get_requires_from_file,
    absolutize_and_mangle_libname,
)
from .import_util import get_file, get_recursive_require_names
from .strip_comments import strip_comments
from .strip_newlines import strip_newlines
from .split_file import split_coq_file_contents, split_leading_comments_and_whitespace
from . import split_definitions
from .split_definitions import (
    split_statements_to_definitions,
    join_definitions,
    get_preferred_passing,
)
from .admit_abstract import transform_abstract_to_admit
from .import_util import (
    lib_of_filename,
    clear_libimport_cache,
    IMPORT_ABSOLUTIZE_TUPLE,
    ALL_ABSOLUTIZE_TUPLE,
)
from .import_util import (
    split_requires_of_statements,
    get_file_statements_insert_references,
)
from .import_util import has_dir_binding, deduplicate_trailing_dir_bindings_get_topname
from .memoize import memoize
from .coq_version import (
    get_coqc_version,
    get_coqtop_version,
    get_coqc_help,
    get_coq_accepts_top,
    get_coq_native_compiler_ondemand_fragment,
    group_coq_args,
    group_coq_args_split_recognized,
    get_coqc_coqlib,
    get_coq_accepts_compile,
    DEFAULT_COQTOP,
)
from .coq_running_support import get_ltac_support_snippet, get_default_options_settings
from .custom_arguments import (
    add_libname_arguments,
    add_passing_libname_arguments,
    update_env_with_libnames,
    update_env_with_coqpath_folders,
    add_logging_arguments,
    process_logging_arguments,
    get_parser_name_mapping,
    DEFAULT_LOG,
    LOG_ALWAYS,
)
from .binding_util import process_maybe_list
from .file_util import clean_v_file, read_from_file, write_to_file
from .util import yes_no_prompt, PY3, list_diff, BooleanOptionalAction
from . import util

if PY3:
    raw_input = util.raw_input
from . import diagnose_error

__all__ = ["main"]

parser = custom_arguments.ArgumentParser(
    description="Attempt to create a small file which reproduces a bug found in a large development."
)
parser.add_argument(
    "bug_file",
    metavar="BUGGY_FILE",
    type=argparse.FileType("r"),
    help="a .v file which displays the bug",
)
parser.add_argument(
    "output_file",
    metavar="OUT_FILE",
    type=str,
    help="a .v file which will hold intermediate results, as well as the final reduced file",
)
parser.add_argument(
    "temp_file",
    metavar="TEMP_FILE",
    nargs="?",
    type=str,
    default="",
    help="a .v file which will be used to build up intermediate files while they are being tested",
)
parser.add_argument(
    "--temp-file-log",
    metavar="TEMP_FILE_LOG",
    dest="temp_file_log",
    nargs="?",
    type=str,
    default="",
    help="a .log file which will contain the log from coqc from the last temp_file that failed",
)
parser.add_argument(
    "--fast-merge-imports",
    dest="fast_merge_imports",
    action="store_const",
    const=True,
    default=False,
    help="Use a faster method for combining imports",
)
parser.add_argument(
    "--no-wrap-modules",
    dest="wrap_modules",
    action="store_const",
    const=False,
    default=True,
    help=(
        "Don't wrap imports in Modules.  By default, the "
        + "contents of each file is wrapped in its own "
        + "module to deal with renaming issues.  This "
        + "can cause issues with subdirectories."
    ),
)
parser.add_argument(
    "--absolutize-constants",
    dest="absolutize",
    action="store_const",
    default=IMPORT_ABSOLUTIZE_TUPLE,
    const=ALL_ABSOLUTIZE_TUPLE,
    help=(
        "Replace constants with fully qualified versions.  "
        + "By default, all constants are not fully qualified.  If you have "
        + "many overlapping file names in different directories "
        + "and use partially qualified names that differ depending "
        + "on which files have been Required, not absolutizing constants "
        + "may cause name resolution to fail."
    ),
)
parser.add_argument(
    "--strip-newlines",
    dest="max_consecutive_newlines",
    metavar="N",
    nargs="?",
    type=int,
    default=2,
    help=(
        "Passing `--strip-newlines N` will cause the "
        + "program to, for all M > N, replace any "
        + "instances of M consecutive newlines with N "
        + "consecutive newlines.  The result will be a "
        + "file with no more than N consecutive newlines.  "
        + "Passing a negative number will disable this option. "
        + "(Default: 2)"
    ),
)
parser.add_argument(
    "--admit-opaque",
    dest="admit_opaque",
    action=BooleanOptionalAction,
    default=None,
    help=(
        "(Don't) try to replace opaque things ([Qed] and [abstract]) "
        + "with [admit]s."
    ),
)
parser.add_argument(
    "--admit-transparent",
    dest="admit_transparent",
    action=BooleanOptionalAction,
    default=None,
    help=("(Don't) try to replace transparent things with [admit]s."),
)
parser.add_argument(
    "--admit-obligations",
    action=BooleanOptionalAction,
    default=None,
    help=("(Don't) try to replace obligations with [Admit Obligations]."),
)
parser.add_argument(
    "--admit",
    dest="admit_any",
    action=BooleanOptionalAction,
    default=True,
    help=("(Don't) try to replace things with [admit]s."),
)
parser.add_argument(
    "--aggressive",
    action=BooleanOptionalAction,
    default=None,
    help=("Be aggressive; try to remove _all_ definitions/lines."),
)
parser.add_argument(
    "--no-remove-typeclasses",
    dest="save_typeclasses",
    action="store_const",
    const=True,
    default=False,
    help=(
        "Don't remove Hints, Instances, or Canonical Structures; "
        + "this should mostly preserve typeclass logs, and can be useful "
        + "for debugging slow typeclass bugs."
    ),
)
parser.add_argument(
    "--ignore-coq-prog-args",
    dest="use_coq_prog_args",
    action="store_const",
    const=False,
    default=True,
    help=("Don't add extra arguments from a coq-prog-args file header."),
)
parser.add_argument(
    "--dynamic-header",
    dest="dynamic_header",
    nargs="?",
    type=str,
    default="(* File reduced by coq-bug-minimizer from %(old_header)s, then from %(original_line_count)d lines to %(final_line_count)d lines *)",
    help=(
        "A line to be placed at the top of the "
        + "output file, followed by a newline.  The "
        + "variables original_line_count and "
        + "final_line_count will be available for "
        + "substitution.  The variable old_header will"
        + "have the previous contents of this comment. "
        + "The default is "
        + "`(* File reduced by coq-bug-minimizer from %%(old_header)s, then from %%(original_line_count)d lines to %%(final_line_count)d lines *)'"
    ),
)
parser.add_argument(
    "--header",
    dest="header",
    nargs="?",
    type=str,
    default="(* coqc version %(coqc_version)s\n   coqtop version %(coqtop_version)s%(module_inline_failure_string)s\n   Expected coqc runtime on this file: %(recent_runtime).3f sec *)",
    help=(
        "A line to be placed at the top of the "
        + "output file, below the dynamic header, "
        + "followed by a newline.  The variables "
        + "coqtop_version and coqc_version will be "
        + "available for substitution.  The default is "
        + "`(* coqc version %%(coqc_version)s\\n   coqtop version %%(coqtop_version)s%%(module_inline_failure_string)s\\n   Expected coqc runtime on this file: %%(recent_runtime).3f sec *)'"
    ),
)
parser.add_argument(
    "--no-strip-trailing-space",
    dest="strip_trailing_space",
    action="store_const",
    const=False,
    default=True,
    help=(
        "Don't strip trailing spaces.  By default, "
        + "trailing spaces on each line are removed."
    ),
)
parser.add_argument(
    "--strict-whitespace",
    dest="strict_whitespace",
    action="store_const",
    const=True,
    default=False,
    help=(
        "Strictly enforce whitespace matching in error "
        + "messages.  By default, locations where there "
        + "are newlines followed by spaces are interchangable "
        + "with any amount of spacing."
    ),
)
parser.add_argument(
    "--no-deps",
    dest="use_coq_makefile_for_deps",
    action="store_const",
    const=False,
    default=True,
    help=("Don't do dependency analysis with coq_makefile."),
)
parser.add_argument(
    "--no-pwd-deps",
    dest="walk_tree",
    action="store_const",
    const=False,
    default=True,
    help=("Don't add all files in the current directory to the dependency analysis."),
)
parser.add_argument(
    "--inline-coqlib",
    dest="inline_coqlib",
    action="store_const",
    const=True,
    default=False,
    help=("Attempt to inline requires from Coq's standard library"),
)
parser.add_argument(
    "--inline-stdlib",
    dest="inline_stdlib",
    action="store_const",
    const=True,
    default=False,
    help=(
        "Attempt to inline requires from Coq's standard library under the Stdlib namespace"
    ),
)
parser.add_argument(
    "--inline-prelude",
    dest="inline_prelude",
    action="store_const",
    const=True,
    default=False,
    help=("Additionally inlines Coq.Init.Prelude by adding -noinit"),
)
parser.add_argument(
    "--inline-user-contrib",
    dest="inline_user_contrib",
    action="store_const",
    const=True,
    default=False,
    help=("Attempt to inline requires from the user-contrib folder"),
)
parser.add_argument(
    "--no-inline-stdlib",
    dest="no_inline_stdlib",
    action="store_const",
    const=True,
    default=False,
    help=("Skip Stdlib directory when using --inline-user-contrib"),
)
parser.add_argument(
    "--no-inline-corelib",
    dest="no_inline_corelib",
    action="store_const",
    const=True,
    default=False,
    help=("Skip Corelib directory when using --inline-user-contrib"),
)
parser.add_argument(
    "--timeout",
    dest="timeout",
    metavar="SECONDS",
    type=int,
    default=-1,
    help=(
        "Use a timeout; make sure Coq is "
        + "killed after running for this many seconds. "
        + "If 0, there is no timeout.  If negative, then "
        + "twice the initial run of the script is used.\n\n"
        + "Default: -1"
    ),
)
parser.add_argument(
    "--no-timeout",
    dest="timeout",
    action="store_const",
    const=0,
    help=("Do not use a timeout"),
)
parser.add_argument(
    "--passing-timeout",
    dest="passing_timeout",
    metavar="SECONDS",
    type=int,
    default=-1,
    help=("Like --timeout, but only for the passing Coq"),
)
parser.add_argument(
    "--nonpassing-timeout",
    dest="nonpassing_timeout",
    metavar="SECONDS",
    type=int,
    default=-1,
    help=("Like --timeout, but only for the non-passing Coq"),
)
parser.add_argument(
    "--minimize-before-inlining",
    dest="minimize_before_inlining",
    action=BooleanOptionalAction,
    default=True,
    help=(
        "(Don't) run the full minimization script before inlining [Requires], "
        + "and between the inlining of every individual [Require].\n\n"
        + "Note that this option will not work well in conjunction with "
        + "--passing-coqc.\n"
        "Passing this option results in a much more robust "
        + "run; it removes the requirement that the compiled dependencies "
        + "of the file being debugged remain in place for the duration of the run."
    ),
)
parser.add_argument(
    "--coqbin",
    metavar="COQBIN",
    dest="coqbin",
    type=str,
    default="",
    help="The path to a folder containing the coqc and coqtop programs.",
)
parser.add_argument(
    "--ocamlpath",
    metavar="OCAMLPATH",
    dest="ocamlpath",
    type=str,
    default=None,
    help="The OCAMLPATH.",
)
parser.add_argument(
    "--nonpassing-ocamlpath",
    metavar="OCAMLPATH",
    dest="nonpassing_ocamlpath",
    type=str,
    default=None,
    help="The OCAMLPATH for the nonpassing coqc.",
)
parser.add_argument(
    "--passing-ocamlpath",
    metavar="OCAMLPATH",
    dest="passing_ocamlpath",
    type=str,
    default=None,
    help="The OCAMLPATH for the passing coqc.",
)
parser.add_argument(
    "--coqc",
    metavar="COQC",
    dest="coqc",
    type=str,
    default=None,
    action="append",
    help="The path to the coqc program.",
)
parser.add_argument(
    "--coqtop",
    metavar="COQTOP",
    dest="coqtop",
    type=str,
    default=None,
    action="append",
    help=("The path to the coqtop program (default: %s)." % DEFAULT_COQTOP),
)
parser.add_argument(
    "--coqc-is-coqtop",
    dest="coqc_is_coqtop",
    default=False,
    action="store_const",
    const=True,
    help="Strip the .v and pass -load-vernac-source to the coqc programs; this allows you to pass `--coqc coqtop'",
)
parser.add_argument(
    "--coqc-args",
    metavar="ARG",
    dest="coqc_args",
    type=str,
    action="append",
    help=(
        'Arguments to pass to coqc; e.g., " -indices-matter" (leading and trailing spaces are stripped)\n'
        + 'NOTE: If you want to pass an argument to both coqc and coqtop, use --arg="-indices-matter", not --coqc-args="-indices-matter"'
    ),
)
parser.add_argument(
    "--coqtop-args",
    metavar="ARG",
    dest="coqtop_args",
    type=str,
    action="append",
    help=(
        'Arguments to pass to coqtop; e.g., " -indices-matter" (leading and trailing spaces are stripped)\n'
        + 'NOTE: If you want to pass an argument to both coqc and coqtop, use --arg="-indices-matter", not --coqc-args="-indices-matter"'
    ),
)
parser.add_argument(
    "--coq_makefile",
    metavar="COQ_MAKEFILE",
    dest="coq_makefile",
    type=str,
    default=None,
    action="append",
    help="The path to the coq_makefile program.",
)
parser.add_argument(
    "--coqdep",
    metavar="COQDEP",
    dest="coqdep",
    type=str,
    default="coqdep",
    help="The path to the coqdep program.",
)
parser.add_argument(
    "--passing-coqc",
    metavar="COQC",
    dest="passing_coqc",
    type=str,
    default=None,
    action="append",
    help="The path to the coqc program that should compile the file successfully.",
)
parser.add_argument(
    "--passing-coqtop",
    metavar="COQTOP",
    dest="passing_coqtop",
    type=str,
    default=None,
    action="append",
    help=("The path to the coqtop program that should compile the file successfully."),
)
parser.add_argument(
    "--parse-with",
    choices=[
        split_definitions.PREFER_PASSING,
        split_definitions.PASSING,
        split_definitions.PREFER_NONPASSING,
        split_definitions.NONPASSING,
    ],
    dest="parse_with",
    type=str,
    default=split_definitions.PREFER_PASSING,
    help=(
        "Parse and split the document using coqc/coqtop vs passing-coqc/passing-coqtop (default: %s)."
        % split_definitions.PREFER_NONPASSING
    ),
)
parser.add_argument(
    "--base-dir",
    metavar="DIR",
    dest="base_dir",
    type=str,
    default="",
    help="The path to the base directory from which coqc should be run",
)
parser.add_argument(
    "--passing-base-dir",
    metavar="DIR",
    dest="passing_base_dir",
    type=str,
    default="",
    help="The path to the base directory from which the passing coqc should be run",
)
parser.add_argument(
    "--passing-coqc-args",
    metavar="ARG",
    dest="passing_coqc_args",
    type=str,
    action="append",
    help='Arguments to pass to coqc so that it compiles the file successfully; e.g., " -indices-matter" (leading and trailing spaces are stripped)',
)
parser.add_argument(
    "--nonpassing-coqc-args",
    metavar="ARG",
    dest="nonpassing_coqc_args",
    type=str,
    action="append",
    help='Arguments to pass to coqc so that it compiles the file successfully; e.g., " -indices-matter" (leading and trailing spaces are stripped)',
)
parser.add_argument(
    "--passing-coqtop-args",
    metavar="ARG",
    dest="passing_coqtop_args",
    type=str,
    action="append",
    help=(
        'Arguments to pass to coqtop so that it compiles the file successfully; e.g., " -indices-matter" (leading and trailing spaces are stripped)\n'
        + 'NOTE: If you want to pass an argument to both coqc and coqtop, use --nonpassing-arg="-indices-matter", not --coqc-args="-indices-matter"'
    ),
)
parser.add_argument(
    "--nonpassing-coqtop-args",
    metavar="ARG",
    dest="nonpassing_coqtop_args",
    type=str,
    action="append",
    help=(
        'Arguments to pass to coqtop so that it compiles the file successfully; e.g., " -indices-matter" (leading and trailing spaces are stripped)\n'
        + 'NOTE: If you want to pass an argument to both coqc and coqtop, use --nonpassing-arg="-indices-matter", not --coqc-args="-indices-matter"'
    ),
)
parser.add_argument(
    "--passing-coqc-is-coqtop",
    dest="passing_coqc_is_coqtop",
    default=False,
    action="store_const",
    const=True,
    help="Strip the .v and pass -load-vernac-source to the coqc programs; this allows you to pass `--passing-coqc coqtop'",
)
parser.add_argument(
    "--error-log",
    metavar="ERROR_LOG",
    dest="error_log",
    type=argparse.FileType("r"),
    default=None,
    help="If given, ensure that the computed error message occurs in this log.",
)
parser.add_argument(
    "-y",
    "--yes",
    "--assume-yes",
    dest="yes",
    action="store_true",
    help='Automatic yes to prompts. Assume "yes" as answer to all prompts and run non-interactively.',
)
parser.add_argument(
    "--no-color",
    dest="color_on",
    action="store_const",
    const=False,
    default=True,
    help=("Don't color any log messages."),
)
parser.add_argument(
    "--verbose-include-failure-warning",
    dest="verbose_include_failure_warning",
    action="store_const",
    const=True,
    default=False,
    help=(
        "Emit a verbose warning when include fails, including the file contents, separately for each error message."
    ),
)
parser.add_argument(
    "--verbose-include-failure-warning-prefix",
    dest="verbose_include_failure_warning_prefix",
    type=str,
    default="",
    help=("Prefix for --verbose-include-failure-warning"),
)
parser.add_argument(
    "--verbose-include-failure-warning-newline",
    dest="verbose_include_failure_warning_newline",
    type=str,
    default="\n",
    help=("Replace all newlines in --verbose-include-failure-warning with this string"),
)
parser.add_argument(
    "--no-error",
    dest="should_succeed",
    action="store_const",
    const=True,
    default=False,
    help="Require that the file succeed rather than failing.  Incompatible with --passing-* arguments, among others.",
)
parser.add_argument(
    "--export-modules",
    action=BooleanOptionalAction,
    default=True,
    help="Export all Modules.",
)
parser.add_argument(
    "--split-imports", action=BooleanOptionalAction, default=None, help="Split imports."
)
parser.add_argument(
    "--remove-modules",
    dest="remove_modules",
    action=BooleanOptionalAction,
    default=True,
    help="Remove all module definitions. Only relevant if --no-error is passed.",
)
parser.add_argument(
    "--remove-sections",
    dest="remove_sections",
    action=BooleanOptionalAction,
    default=None,
    help="Remove all sections. Only relevant if --no-error is passed.",
)
parser.add_argument(
    "--remove-comments",
    action=BooleanOptionalAction,
    default=None,
    help="Remove all comments.",
)
parser.add_argument(
    "--normalize-requires",
    action=BooleanOptionalAction,
    default=True,
    help="Normalize requires.",
)
parser.add_argument(
    "--recursive-requires-explicit",
    action=BooleanOptionalAction,
    default=None,
    help="When normalizing requires, include all recursive requires explicitly.  This is useful for removing unneeded intermediate requires rather than inlining them, but causes issues with minimization when requires are not pre-emptively removed if any require fails to inline.",
)
parser.add_argument(
    "--split-requires",
    action=BooleanOptionalAction,
    default=True,
    help="Split requires.",
)
parser.add_argument(
    "--remove-hints",
    action=BooleanOptionalAction,
    default=None,
    help="Remove all hints.",
)
parser.add_argument(
    "--remove-empty-sections",
    action=BooleanOptionalAction,
    default=True,
    help="Remove all empty sections.",
)
parser.add_argument(
    "--remove-abort",
    action=BooleanOptionalAction,
    default=True,
    help="Remove all aborts.",
)
parser.add_argument(
    "--remove-ltac",
    action=BooleanOptionalAction,
    default=None,
    help="Remove unused ltac.",
)
parser.add_argument(
    "--remove-section-variables",
    action=BooleanOptionalAction,
    default=None,
    help="Remove unused section variables.",
)
parser.add_argument(
    "--prefer-inline-via-include",
    action=BooleanOptionalAction,
    default=None,
    help="Prefer inlining dependencies via Include.",
)
parser.add_argument(
    "--add-proof-using",
    action=BooleanOptionalAction,
    default=True,
    help="Add Proof using.",
)
parser.add_argument(
    "--add-proof-using-before-admit",
    action=BooleanOptionalAction,
    default=None,
    help="Add Proof using before first attempting to admit lemmas.",
)
parser.add_argument(
    "--prefer-final-proof-using",
    action=BooleanOptionalAction,
    default=False,
    help="Use the final Proof using suggestion from Set Suggest Proof Using rather than the first.",
)
parser.add_argument(
    "--remove-non-definitions",
    action=BooleanOptionalAction,
    default=None,
    help="Remove all statements that don't add constants to the global environment, where possible.",
)

add_libname_arguments(parser)
add_passing_libname_arguments(parser)
add_logging_arguments(parser)


def adjust_no_error_defaults(args: argparse.Namespace):
    for arg in (
        "remove_comments",
        "remove_sections",
        "remove_hints",
        "remove_ltac",
        "remove_section_variables",
        "aggressive",
        "prefer_inline_via_include",
        "admit_opaque",
        "admit_transparent",
        "admit_obligations",
        "split_imports",
        "recursive_requires_explicit",
    ):
        if getattr(args, arg) is None:
            setattr(args, arg, not args.should_succeed)
    for arg in ("add_proof_using_before_admit", "remove_non_definitions"):
        if getattr(args, arg) is None:
            setattr(args, arg, args.should_succeed)

    return args


SENSITIVE_TIMEOUT_RETRY_COUNT = 3


@memoize
def re_compile(pattern, *args):
    return re.compile(pattern, *args)


# memoize the compilation
def re_search(pattern, string, flags=0):
    return re_compile(pattern, flags).search(string)


def ask(query, **kwargs):
    if kwargs["yes"]:
        print(query)
        return "y"
    else:
        return raw_input(query)


def get_error_reg_string_of_output(output, output_file_name, **kwargs):
    error_reg_string = ""
    if diagnose_error.has_error(output):
        error_string = diagnose_error.get_error_string(output)
        error_reg_string = diagnose_error.make_reg_string(
            output, strict_whitespace=kwargs["strict_whitespace"]
        )
        kwargs["log"](
            "\nI think the error is '%s'.\nThe corresponding regular expression is '%s'.\n"
            % (
                error_string,
                error_reg_string.replace("\\\n", "\\n").replace("\n", "\\n"),
            ),
            force_stdout=True,
            level=LOG_ALWAYS,
        )
        result = ""
        while result not in ("y", "n", "yes", "no"):
            result = ask("Is this correct? [(y)es/(n)o] ", **kwargs).lower().strip()
        if result in ("no", "n"):
            error_reg_string = ""
    else:
        kwargs["log"](
            "\nThe current state of the file does not have a recognizable error.",
            level=LOG_ALWAYS,
        )

    if error_reg_string == "":
        success = False
        while not success:
            error_reg_string = raw_input(
                "\nPlease enter a regular expression which matches on the output.  Leave blank to re-coq the file.\n"
            )
            try:
                re.compile(error_reg_string)
            except Exception as e:
                kwargs["log"](
                    "\nThat regular expression does not compile: %s" % e,
                    force_stdout=True,
                    level=LOG_ALWAYS,
                )
                success = False
            else:
                success = True

    while error_reg_string != "" and (
        not re.search(error_reg_string, output)
        or len(re.search(error_reg_string, output).groups()) != 2
    ):
        if not re.search(error_reg_string, output):
            kwargs["log"](
                "\nThe given regular expression does not match the output.",
                force_stdout=True,
                level=LOG_ALWAYS,
            )
        elif len(re.search(error_reg_string, output).groups()) != 2:
            kwargs["log"](
                "\nThe given regular expression does not have two groups.",
                force_stdout=True,
                level=LOG_ALWAYS,
            )
            kwargs["log"](
                "It must first have one integer group which matches on the line number,",
                force_stdout=True,
                level=LOG_ALWAYS,
            )
            kwargs["log"](
                "and second a group which matches on the error string.",
                force_stdout=True,
                level=LOG_ALWAYS,
            )
        error_reg_string = raw_input(
            "Please enter a valid regular expression which matches on the output.  Leave blank to re-coq the file (%s).\n"
            % output_file_name
        )
    return error_reg_string


def get_error_reg_string(output_file_name, **kwargs):
    error_reg_string = ""
    while error_reg_string == "":
        kwargs["log"]("\nCoqing the file (%s)..." % output_file_name)
        contents = read_from_file(output_file_name)
        diagnose_error.reset_timeout()
        kwargs["log"]("\nContents:\n\n%s\n\n" % contents, level=3)
        output, cmds, retcode, runtime = diagnose_error.get_coq_output(
            kwargs["coqc"],
            kwargs["coqc_args"],
            contents,
            kwargs["timeout"],
            is_coqtop=kwargs["coqc_is_coqtop"],
            verbose_base=1,
            cwd=kwargs["base_dir"],
            ocamlpath=kwargs["nonpassing_ocamlpath"],
            **kwargs,
        )
        result = ""
        kwargs["log"](
            "\nThis file produces the following output when Coq'ed:\n%s" % output,
            force_stdout=True,
            level=LOG_ALWAYS,
        )
        while result not in ("y", "n", "yes", "no"):
            result = (
                ask(
                    "Does this output display the correct error? [(y)es/(n)o] ",
                    **kwargs,
                )
                .lower()
                .strip()
            )
        if result in ("n", "no"):
            raw_input(
                "Please modify the file (%s) so that it errors correctly, and then press ENTER to continue, or ^C to break."
                % output_file_name
            )
            continue

        error_reg_string = get_error_reg_string_of_output(
            output, output_file_name, **kwargs
        )

        if error_reg_string == "":
            continue

    return error_reg_string


def escape_coq_prog_args(coq_prog_args):
    return " ".join(
        '"' + arg.replace("\\", "\\\\").replace('"', r"\"") + '"'
        for arg in coq_prog_args
    )


def unescape_coq_prog_args(coq_prog_args):
    ret = []
    cur = None
    in_string = False
    idx = 0
    while idx < len(coq_prog_args):
        cur_char = coq_prog_args[idx]
        idx += 1
        if not in_string:
            if cur_char == '"':
                in_string = True
                cur = ""
            elif cur_char not in " \t":
                DEFAULT_LOG(
                    "Warning: Invalid unquoted character '%s' at index %d in coq-prog-args '%s'"
                    % (cur_char, idx - 1, coq_prog_args),
                    level=LOG_ALWAYS,
                )
                return tuple(ret)
        else:
            if cur_char == '"':
                in_string = False
                ret.append(cur)
                cur = None
            elif cur_char == "\\":
                if idx < len(coq_prog_args):
                    # take the next character
                    cur += coq_prog_args[idx]
                    idx += 1
                else:
                    DEFAULT_LOG(
                        "Warning: Invalid backslash at end of coq-prog-args '%s'"
                        % coq_prog_args,
                        level=LOG_ALWAYS,
                    )
            else:
                cur += cur_char
    return tuple(ret)


COQ_PROG_ARGS_REG = re.compile(r"coq-prog-args\s*:\s*\(([^\)]+)\)")


def get_coq_prog_args(contents):
    return tuple(
        arg
        for args in COQ_PROG_ARGS_REG.findall(contents)
        for arg in unescape_coq_prog_args(args)
        if arg not in ("-emacs", "-emacs-U")
    )


COQ_PROG_ARGS_REP = re.compile(r"[ \t]*\(\*+\s+-\*-\s+.*?\s-\*-\s+\*+\)\s*")


def strip_coq_prog_args(contents):
    return COQ_PROG_ARGS_REP.sub("", contents)


def get_old_header(contents, header=""):
    contents = strip_coq_prog_args(contents)
    if header[:2] == "(*" and header[-2:] == "*)" and "*)" not in header[2:-2]:
        pre_header = header[: header.index("%")]
        if pre_header in contents and contents.index("*)") > contents.index(pre_header):
            return contents[
                contents.index(pre_header) + len(pre_header) : contents.index("*)")
            ].strip()
    return "original input"


def prepend_header(contents, dynamic_header="", header="", header_dict={}, **kwargs):
    """Fills in the variables in the header for output files"""
    contents = strip_coq_prog_args(contents)
    if (
        dynamic_header[:2] == "(*"
        and dynamic_header[-2:] == "*)"
        and "*)" not in dynamic_header[2:-2]
    ):
        pre_header = dynamic_header[: dynamic_header.index("%")]
        if contents[: len(pre_header)] == pre_header:
            # strip the old header
            contents = contents[contents.index("*)") + 2 :]
            if contents[0] == "\n":
                contents = contents[1:]
    if header[:2] == "(*" and header[-2:] == "*)" and "*)" not in header[2:-2]:
        pre_header = header[: header.index("%")]
        if contents[: len(pre_header)] == pre_header:
            # strip the old header
            contents = contents[contents.index("*)") + 2 :]
            if contents[0] == "\n":
                contents = contents[1:]
    final_line_count = len(contents.split("\n"))
    header_dict = dict(header_dict)  # clone the dict
    header_dict["final_line_count"] = final_line_count
    header_dict["inline_failure_libnames"] = ", ".join(
        kwargs["inline_failure_libnames"]
    )
    header_dict["module_inline_failure_string"] = (
        "\n   Modules that could not be inlined: %s"
        % header_dict["inline_failure_libnames"]
        if header_dict["inline_failure_libnames"]
        else ""
    )
    if "old_header" not in header_dict.keys():
        header_dict["old_header"] = "original input"
    use_header = (dynamic_header + "\n" + header) % header_dict
    coq_prog_args = (
        '(* -*- mode: coq; coq-prog-args: ("-emacs" %s) -*- *)\n'
        % escape_coq_prog_args(kwargs["coqc_args"])
        if len(kwargs["coqc_args"]) > 0
        else ""
    )
    ## de-duplicate things in a list
    ## XXX This is a hack to deal with things like "from x lines to y lines, from x lines to y lines"
    # if use_header[-3:] == ' *)':
    #    use_header = ','.join(OrderedSet(use_header[:-3].split(','))) + ' *)'
    return "%s%s\n%s" % (coq_prog_args, use_header, contents)


INSTANCE_REG = re.compile(r"(?<![\w'])Instance\s")
CANONICAL_STRUCTURE_REG = re.compile(r"(?<![\w'])Canonical\s+Structure\s")
TC_HINT_REG = re.compile("(?<![\w'])Hint\s")


def get_header_dict(contents, old_header=None, original_line_count=0, **env):
    coqc_version = get_coqc_version(env["coqc"], **env)
    coqtop_version = get_coqtop_version(env["coqtop"], **env)
    if old_header is None:
        old_header = get_old_header(contents, env["dynamic_header"])
    return {
        "original_line_count": original_line_count,
        "old_header": old_header,
        "coqc_version": coqc_version,
        "coqtop_version": coqtop_version,
        "recent_runtime": 0,
    }


CONTENTS_UNCHANGED, CHANGE_SUCCESS, CHANGE_FAILURE = (
    "contents_unchanged",
    "change_success",
    "change_failure",
)


def classify_contents_change(
    old_contents,
    new_contents,
    ignore_coq_output_cache=False,
    reset_timeout=False,
    should_succeed: bool = False,
    **kwargs,
):
    # returns (RESULT_TYPE, PADDED_CONTENTS, OUTPUT_LIST, option BAD_INDEX, DESCRIPTION_OF_FAILURE_MODE, RUNTIME, EXTRA_VERBOSE_DESCRIPTION_OF_FAILURE_MODE_TUPLE_LIST)
    kwargs["header_dict"] = kwargs.get(
        "header_dict",
        get_header_dict(
            new_contents, original_line_count=len(old_contents.split("\n")), **kwargs
        ),
    )

    # this is a function, so that once we update the header dict with the runtime, we get the right header
    def get_padded_contents():
        return prepend_header(new_contents, **kwargs)

    if new_contents == old_contents:
        return (
            CONTENTS_UNCHANGED,
            get_padded_contents(),
            tuple(),
            None,
            "No change.  ",
            None,
            [],
        )

    if reset_timeout:
        diagnose_error.reset_timeout()
    if ignore_coq_output_cache:
        diagnose_error.reset_coq_output_cache(
            kwargs["coqc"],
            kwargs["coqc_args"],
            new_contents,
            kwargs["timeout"],
            cwd=kwargs["base_dir"],
            is_coqtop=kwargs["coqc_is_coqtop"],
            verbose_base=2,
            ocamlpath=kwargs["nonpassing_ocamlpath"],
            **kwargs,
        )
    output, cmds, retcode, runtime = diagnose_error.get_coq_output(
        kwargs["coqc"],
        kwargs["coqc_args"],
        new_contents,
        kwargs["timeout"],
        cwd=kwargs["base_dir"],
        is_coqtop=kwargs["coqc_is_coqtop"],
        verbose_base=2,
        ocamlpath=kwargs["nonpassing_ocamlpath"],
        **kwargs,
    )
    if not should_succeed and diagnose_error.has_error(
        output, kwargs["error_reg_string"]
    ):
        if kwargs["passing_coqc"]:
            if ignore_coq_output_cache:
                diagnose_error.reset_coq_output_cache(
                    kwargs["passing_coqc"],
                    kwargs["passing_coqc_args"],
                    new_contents,
                    kwargs["passing_timeout"],
                    cwd=kwargs["passing_base_dir"],
                    is_coqtop=kwargs["passing_coqc_is_coqtop"],
                    verbose_base=2,
                    ocamlpath=kwargs["passing_ocamlpath"],
                    **kwargs,
                )
            passing_output, cmds, passing_retcode, passing_runtime = (
                diagnose_error.get_coq_output(
                    kwargs["passing_coqc"],
                    kwargs["passing_coqc_args"],
                    new_contents,
                    kwargs["passing_timeout"],
                    cwd=kwargs["passing_base_dir"],
                    is_coqtop=kwargs["passing_coqc_is_coqtop"],
                    verbose_base=2,
                    ocamlpath=kwargs["passing_ocamlpath"],
                    **kwargs,
                )
            )
            if not (
                diagnose_error.has_error(passing_output)
                or diagnose_error.is_timeout(passing_output)
            ):
                # we return passing_runtime, under the presumption
                # that in Coq's test-suite, the file should pass, and
                # so this is a better indicator of how long it'll take
                kwargs["header_dict"]["recent_runtime"] = passing_runtime
                return (
                    CHANGE_SUCCESS,
                    get_padded_contents(),
                    (output, passing_output),
                    None,
                    "Change successful.  ",
                    passing_runtime,
                    [],
                )
            else:
                return (
                    CHANGE_FAILURE,
                    get_padded_contents(),
                    (output, passing_output),
                    1,
                    "The alternate coqc (%s) was supposed to pass, but instead emitted an error.  "
                    % kwargs["passing_coqc"],
                    runtime,
                    [],
                )
        else:
            kwargs["header_dict"]["recent_runtime"] = runtime
            return (
                CHANGE_SUCCESS,
                get_padded_contents(),
                (output,),
                None,
                "Change successful.  ",
                runtime,
                [],
            )
    elif should_succeed and not diagnose_error.has_error(output):
        kwargs["header_dict"]["recent_runtime"] = runtime
        return (
            CHANGE_SUCCESS,
            get_padded_contents(),
            (output,),
            None,
            "Change successful.  ",
            runtime,
            [],
        )
    else:
        extra_desc = ""
        extra_desc_list = [(2, "The error was:\n%s\n" % output)]
        return (
            CHANGE_FAILURE,
            get_padded_contents(),
            (output,),
            0,
            extra_desc,
            runtime,
            extra_desc_list,
        )


def check_change_and_write_to_file(
    old_contents,
    new_contents,
    output_file_name,
    unchanged_message="No change.",
    success_message="Change successful.",
    failure_description="make a change",
    changed_description="Changed file",
    timeout_retry_count=1,
    ignore_coq_output_cache=False,
    verbose_base=1,
    display_source_to_error=False,
    write_to_temp_file=False,
    display_extra_verbose_on_error=False,
    extra_verbose_prefix="",
    extra_verbose_newline="\n",
    skip_extra_verbose_error_state=set(),
    **kwargs,
):
    kwargs["log"](
        'Running coq on the file\n"""\n%s\n"""' % new_contents, level=2 + verbose_base
    )
    (
        change_result,
        contents,
        outputs,
        output_i,
        error_desc,
        runtime,
        error_desc_verbose_list,
    ) = classify_contents_change(
        old_contents,
        new_contents,
        ignore_coq_output_cache=ignore_coq_output_cache,
        **kwargs,
    )
    if change_result == CONTENTS_UNCHANGED:
        kwargs["log"]("\n%s" % unchanged_message, level=verbose_base)
        return False
    elif change_result == CHANGE_SUCCESS:
        kwargs["log"](
            util.color(
                "\n%s" % success_message, util.colors.OKGREEN, kwargs["color_on"]
            ),
            level=verbose_base,
        )
        write_to_file(output_file_name, contents)
        return True
    elif change_result == CHANGE_FAILURE:
        kwargs["log"](
            "\nNon-fatal error: Failed to %s and preserve the error.  %s"
            % (failure_description, error_desc),
            level=verbose_base,
        )
        for lvl, msg in error_desc_verbose_list:
            kwargs["log"](msg, level=lvl)
        if write_to_temp_file and not kwargs["remove_temp_file"]:
            kwargs["log"](
                "Writing %s to %s (log in %s)."
                % (
                    changed_description.lower(),
                    kwargs["temp_file_name"],
                    kwargs["temp_file_log_name"],
                ),
                level=verbose_base,
            )
        kwargs["log"]("The new error was:", level=verbose_base)
        kwargs["log"](outputs[output_i], level=verbose_base)
        kwargs["log"]("All Outputs:\n%s" % "\n".join(outputs), level=verbose_base + 2)
        if write_to_temp_file and not kwargs["remove_temp_file"]:
            write_to_file(kwargs["temp_file_name"], contents)
            write_to_file(kwargs["temp_file_log_name"], outputs[output_i])
        else:
            kwargs["log"](
                util.color(
                    "%s not saved." % changed_description,
                    util.colors.WARNING,
                    kwargs["color_on"],
                ),
                level=verbose_base,
            )
        if timeout_retry_count > 1 and diagnose_error.is_timeout(outputs[output_i]):
            kwargs["log"](
                "\nRetrying another %d time%s..."
                % (timeout_retry_count - 1, "s" if timeout_retry_count > 2 else ""),
                level=verbose_base,
            )
            return check_change_and_write_to_file(
                old_contents,
                new_contents,
                output_file_name,
                unchanged_message=unchanged_message,
                success_message=success_message,
                failure_description=failure_description,
                changed_description=changed_description,
                timeout_retry_count=timeout_retry_count - 1,
                ignore_coq_output_cache=True,
                verbose_base=verbose_base,
                write_to_temp_file=write_to_temp_file,
                display_extra_verbose_on_error=display_extra_verbose_on_error,
                **kwargs,
            )
        else:
            if diagnose_error.has_error(outputs[output_i]):
                new_line = diagnose_error.get_error_line_number(outputs[output_i])
                new_start, new_end = diagnose_error.get_error_byte_locations(
                    outputs[output_i]
                )
                new_contents_lines = new_contents.split("\n")
                new_contents_to_error, new_contents_rest = (
                    "\n".join(new_contents_lines[: new_line - 1]),
                    "\n".join(new_contents_lines[new_line - 1 :]),
                )
                source_display = "%s\n%s\n" % (
                    new_contents_to_error,
                    new_contents_rest.encode("utf-8")[:new_end].decode("utf-8"),
                )
            else:
                source_display = new_contents
            error_key = re.sub(r'File "[^"]+"', r'File ""', outputs[output_i])
            if (
                display_extra_verbose_on_error
                and error_key not in skip_extra_verbose_error_state
            ):
                skip_extra_verbose_error_state.add(error_key)
                kwargs["log"](
                    "%s%s"
                    % (
                        extra_verbose_prefix,
                        (
                            "%sFailed to %s and preserve the error.  %s\nThe new error was:\n%s\n\nThe file generating the error was:\n%s"
                            % (
                                extra_verbose_prefix,
                                failure_description,
                                error_desc,
                                outputs[output_i],
                                source_display,
                            )
                        )
                        .replace("\r\n", "\n")
                        .replace("\n", extra_verbose_newline),
                    ),
                    level=verbose_base,
                )
            if display_source_to_error:
                kwargs["log"]("The file generating the error was:", level=verbose_base)
                kwargs["log"](source_display, level=verbose_base)
        return False
    else:
        kwargs["log"](
            "ERROR: Unrecognized change result %s on\nclassify_contents_change(\n  %s\n ,%s\n)\n%s"
            % (
                change_result,
                repr(old_contents),
                repr(new_contents),
                repr(
                    (
                        change_result,
                        contents,
                        outputs,
                        output_i,
                        error_desc,
                        runtime,
                        error_desc_verbose_list,
                    )
                ),
            ),
            level=LOG_ALWAYS,
        )
    return None


def try_transform_each(
    definitions,
    output_file_name,
    transformer,
    skip_n=1,
    returns_all_definitions: bool = False,
    **kwargs,
):
    """Tries to apply transformer to each definition in definitions,
    additionally passing in the list of subsequent definitions.  If
    the returned value of the 'statement' key is not equal to the old
    value, or if the return value is a false-y value (indicating that
    we should remove the line) then we see if the error is still
    present.  If it is, we keep the change; otherwise, we discard it.
    The order in which definitions are passed in is guaranteed to be
    reverse-order.

    Returns updated definitions."""
    kwargs["log"]("try_transform_each", level=3)
    original_definitions = [dict(i) for i in definitions]
    # TODO(jgross): Use coqtop and [BackTo] to do incremental checking
    success = False
    i = len(definitions) - 1 - skip_n
    if not returns_all_definitions:
        original_transformer = transformer
        transformer = lambda old_definition, rest_definitions: (
            original_transformer(old_definition, rest_definitions),
            rest_definitions,
        )
    while i >= 0:
        old_definition = definitions[i]
        new_definition, new_rest_definitions = transformer(
            old_definition, definitions[i + 1 :]
        )
        if not new_definition:
            if kwargs["save_typeclasses"] and (
                INSTANCE_REG.search(old_definition["statement"])
                or CANONICAL_STRUCTURE_REG.search(old_definition["statement"])
                or TC_HINT_REG.search(old_definition["statement"])
            ):
                kwargs["log"](
                    "Ignoring Instance/Canonical Structure/Hint: %s"
                    % old_definition["statement"],
                    level=3,
                )
                i -= 1
                continue
            new_definitions = []
        elif isinstance(new_definition, dict):
            if not new_definition["statement"].strip():
                new_definitions = []
            else:
                new_definitions = [new_definition]
        else:
            new_definitions = list(new_definition)
        if (
            len(new_definitions) != 1
            or re.sub(r"\s+", " ", old_definition["statement"]).strip()
            != re.sub(r"\s+", " ", new_definitions[0]["statement"]).strip()
            or new_rest_definitions != definitions[i + 1 :]
        ):
            if len(new_definitions) == 0:
                kwargs["log"](
                    "Attempting to remove %s" % repr(old_definition["statement"]),
                    level=2,
                )
                if new_rest_definitions != definitions[i + 1 :]:
                    kwargs["log"](
                        "Also modifying remainder via %s"
                        % list_diff(
                            [d["statement"] for d in definitions[i + 1 :]],
                            [d["statement"] for d in new_rest_definitions],
                        ),
                        level=3,
                    )
                try_definitions = definitions[:i] + new_rest_definitions
            else:
                kwargs["log"](
                    "Attempting to transform %s\ninto\n%s"
                    % (
                        old_definition["statement"],
                        "".join(defn["statement"] for defn in new_definitions),
                    ),
                    level=2,
                )
                if len(new_definitions) > 1:
                    kwargs["log"](
                        "Splitting definition: %s" % repr(new_definitions), level=2
                    )
                if new_rest_definitions != definitions[i + 1 :]:
                    kwargs["log"](
                        "Also modifying remainder via %s"
                        % list_diff(
                            [d["statement"] for d in definitions[i + 1 :]],
                            [d["statement"] for d in new_rest_definitions],
                        ),
                        level=3,
                    )
                try_definitions = (
                    definitions[:i] + new_definitions + new_rest_definitions
                )

            if check_change_and_write_to_file(
                "",
                join_definitions(try_definitions),
                output_file_name,
                verbose_base=2,
                **kwargs,
            ):
                success = True
                definitions = try_definitions
                # make a copy for saving
                save_definitions = [dict(defn) for defn in try_definitions]
        else:
            kwargs["log"]("No change to %s" % old_definition["statement"], level=3)
        i -= 1
    if success:
        kwargs["log"](kwargs["noun_description"] + " successful")
        if join_definitions(save_definitions) != join_definitions(definitions):
            kwargs["log"](
                "Probably fatal error: definitions != save_definitions",
                level=LOG_ALWAYS,
            )
        else:
            contents = prepend_header(join_definitions(definitions), **kwargs)
            write_to_file(output_file_name, contents)
        return definitions
    else:
        kwargs["log"](kwargs["noun_description"] + " unsuccessful.")
        return original_definitions


def try_transform_reversed(
    definitions,
    output_file_name,
    transformer,
    skip_n=1,
    returns_all_definitions: bool = False,
    **kwargs,
):
    """Replaces each definition in definitions, with transformer
    applied to that definition and the subsequent (transformed)
    definitions.  If transformer returns a false-y value, the
    definition is removed.  After transforming the entire list, we see
    if the error is still present.  If it is, we keep the change;
    otherwise, we discard it.  The order in which definitions are
    passed in is guaranteed to be reverse-order.

    Returns updated definitions."""
    kwargs["log"]("try_transform_reversed", level=3)
    definitions = list(definitions)  # clone the list of definitions
    original_definitions = list(definitions)
    kwargs["log"](len(definitions), level=3)
    kwargs["log"](definitions, level=3)
    if not returns_all_definitions:
        original_transformer = transformer
        transformer = lambda old_definition, rest_definitions: (
            original_transformer(old_definition, rest_definitions),
            rest_definitions,
        )
    for i in reversed(list(range(len(definitions) - skip_n))):
        new_definition, new_rest_definitions = transformer(
            definitions[i], definitions[i + 1 :]
        )
        if new_definition:
            if (
                definitions[i] != new_definition
                or new_rest_definitions != definitions[i + 1 :]
            ):
                kwargs["log"](
                    "Transforming %s into %s"
                    % (definitions[i]["statement"], new_definition["statement"]),
                    level=2,
                )
                if new_rest_definitions != definitions[i + 1 :]:
                    kwargs["log"](
                        "Also modifying remainder via %s"
                        % list_diff(
                            [d["statement"] for d in definitions[i + 1 :]],
                            [d["statement"] for d in new_rest_definitions],
                        ),
                        level=3,
                    )
            else:
                kwargs["log"]("No change to %s" % new_definition["statement"], level=3)
            definitions = definitions[:i] + [new_definition] + new_rest_definitions
        else:
            if kwargs["save_typeclasses"] and (
                INSTANCE_REG.search(definitions[i]["statement"])
                or CANONICAL_STRUCTURE_REG.search(definitions[i]["statement"])
                or TC_HINT_REG.search(definitions[i]["statement"])
            ):
                kwargs["log"](
                    "Ignoring Instance/Canonical Structure/Hint: %s"
                    % definitions[i]["statement"],
                    level=3,
                )
                pass
            else:
                kwargs["log"]("Removing %s" % definitions[i]["statement"], level=2)
                if new_rest_definitions != definitions[i + 1 :]:
                    kwargs["log"](
                        "Also modifying remainder via %s"
                        % list_diff(
                            [d["statement"] for d in definitions[i + 1 :]],
                            [d["statement"] for d in new_rest_definitions],
                        ),
                        level=3,
                    )
                definitions = definitions[:i] + new_rest_definitions

    if check_change_and_write_to_file(
        "",
        join_definitions(definitions),
        output_file_name,
        success_message=kwargs["noun_description"] + " successful.",
        failure_description=kwargs["verb_description"],
        changed_description="Intermediate code",
        **kwargs,
    ):
        return definitions

    return original_definitions


def try_transform_reversed_or_else_each(definitions, *args, **kwargs):
    """Invokes try_transform_reversed.  If there are no changes, then try_transform_each is tried."""
    old_definitions = join_definitions(definitions)  # for comparison,
    # to see if things have changed first, try to do everything at
    # once; python cycles are assumed to be cheap in comparison to coq
    # cycles
    definitions = try_transform_reversed(definitions, *args, **kwargs)
    new_definitions = join_definitions(definitions)
    if new_definitions == old_definitions:
        # we failed to do everything at once, try the simple thing and
        # try to admit each individually
        kwargs["log"]("Failed to do everything at once; trying one at a time.")
        definitions = try_transform_each(definitions, *args, **kwargs)
    new_definitions = join_definitions(definitions)
    if new_definitions == old_definitions:
        kwargs["log"]("No successful changes.")
    else:
        kwargs["log"]("Success!")
    return definitions


def try_remove_if_not_matches_transformer(definition_found_in, **kwargs):
    def transformer(cur_definition, rest_definitions):
        if any(
            definition_found_in(cur_definition, future_definition)
            for future_definition in rest_definitions
        ):
            kwargs["log"](
                "Definition found; found:\n%s\nin\n%s"
                % (
                    cur_definition,
                    [
                        future_definition["statement"]
                        for future_definition in rest_definitions
                        if definition_found_in(cur_definition, future_definition)
                    ][0],
                ),
                level=3,
            )
            return cur_definition
        else:
            return None

    return transformer


# don't count things like [Section ...], [End ...]
EXCLUSION_REG = re.compile(
    r"^\s*Section\s+[^\.]+\.\s*$"
    + r"|^\s*Module\s+[^\.]+\.\s*$"
    + r"|^\s*End\s+[^\.]+\.\s*$"
    + r"|^\s*Require\s+[^\.]+\.\s*$"
    + r"|^\s*Import\s+[^\.]+\.\s*$"
    + r"|^\s*Export\s+[^\.]+\.\s*$"
)


def try_remove_if_name_not_found_in_transformer(get_names, **kwargs):
    def definition_found_in(cur_definition, future_definition):
        names = get_names(cur_definition)
        if len(names) == 0:
            return True
        elif EXCLUSION_REG.search(future_definition["statement"]):
            return False  # we don't care if the name is found in a
            # statement like [Section ...] or [End ...]
        return any(
            re_search(
                r"(?<![\w'])%s(?![\w'])" % re.escape(name),
                future_definition["statement"],
            )
            for name in names
        )

    return try_remove_if_not_matches_transformer(definition_found_in, **kwargs)


def try_remove_if_name_not_found_in_section_transformer(get_names, **kwargs):
    SECTION_BEGIN_REG = re.compile(r"^\s*(?:Section|Module)\s+[^\.]+\.\s*$")
    SECTION_END_REG = re.compile(r"^\s*End\s+[^\.]+\.\s*$")

    def transformer(cur_definition, rest_definitions):
        names = get_names(cur_definition)
        if len(names) == 0:
            return cur_definition
        section_level = 0
        for future_definition in rest_definitions:
            if section_level < 0:
                break
            if SECTION_BEGIN_REG.match(future_definition["statement"]):
                section_level += 1
            elif SECTION_END_REG.match(future_definition["statement"]):
                section_level -= 1
            elif any(
                re_search(
                    r"(?<![\w'])%s(?![\w'])" % re.escape(name),
                    future_definition["statement"],
                )
                for name in names
            ):
                return cur_definition
        # we didn't find the name, so we can safely remove it
        return None

    return transformer


def try_remove_non_instance_definitions(definitions, output_file_name, **kwargs):
    def get_names(definition):
        if INSTANCE_REG.search(definition["statements"][0]):
            return tuple()
        elif CANONICAL_STRUCTURE_REG.search(definition["statements"][0]):
            return tuple()
        else:
            return definition.get("terms_defined", tuple())

    return try_transform_reversed(
        definitions,
        output_file_name,
        try_remove_if_name_not_found_in_transformer(get_names, **kwargs),
        noun_description="Non-instance definition removal",
        verb_description="remove non-instance definitions",
        **kwargs,
    )


def try_remove_definitions(definitions, output_file_name, **kwargs):
    return try_transform_reversed(
        definitions,
        output_file_name,
        try_remove_if_name_not_found_in_transformer(
            lambda definition: definition.get("terms_defined", tuple()), **kwargs
        ),
        noun_description="Definition removal",
        verb_description="remove definitions",
        **kwargs,
    )


def try_remove_each_definition(definitions, output_file_name, **kwargs):
    return try_transform_each(
        definitions,
        output_file_name,
        try_remove_if_name_not_found_in_transformer(
            lambda definition: definition.get("terms_defined", tuple()), **kwargs
        ),
        noun_description="Definition removal",
        verb_description="remove definitions",
        **kwargs,
    )


def try_remove_each_and_every_line(definitions, output_file_name, **kwargs):
    return try_transform_each(
        definitions,
        output_file_name,
        (lambda cur_definition, rest_definitions: False),
        noun_description="Line removal",
        verb_description="remove lines",
        **kwargs,
    )


EXTRA_DEFINITION_ISH = "|".join(
    ["Theorem", "Lemma", "Fact", "Remark", "Corollary", "Proposition", "Property"]
    + ["Definition", "Example", "SubClass"]
    + ["Inductive", "CoInductive"]
    + ["Variant", "Record", "Structure", "Class"]
    + ["Fixpoint", "CoFixpoint"]
    + ["Axiom", "Axioms", "Symbol", "Symbols", "Primitive"]
    + [
        "Variables",
        "Variable",
        "Hypotheses",
        "Hypothesis",
        "Parameters",
        "Parameter",
        "Conjectures",
        "Conjecture",
    ]
    + ["Instance", "Derive", "Declare"]
)

EXTRA_DEFINITION_ISH_REG = re.compile(
    r"^\s*"
    + r"(?:Local\s+|Global\s+|Polymorphic\s+|Monomorphic\s+|#\[[^\]]+\]\s*)*"
    + r"(?:"
    + EXTRA_DEFINITION_ISH
    + r"|Set\s+Universe\s+Polymorphism"
    + r"|Unet\s+Universe\s+Polymorphism"
    + r"|Require|Import|Export|Include"
    + r"|Section|Module|End"
    + r"|Set"
    + r")(?:\.\s+|\.$|\s+|$)",
    flags=re.MULTILINE,
)

SECTION_REG = re.compile(r"^\s*(?:Section|Module|End)(?:\s+|$)", flags=re.MULTILINE)


def try_remove_each_and_every_non_definition_line(
    definitions, output_file_name, **kwargs
):
    def transformer(cur_definition, rest_definitions):
        if (
            cur_definition["terms_defined"]
            or SECTION_REG.search(cur_definition["statement"])
            or EXTRA_DEFINITION_ISH_REG.search(cur_definition["statement"])
        ):
            return cur_definition
        else:
            kwargs["log"](
                "Attempting to remove non-definition line: %s"
                % cur_definition["statement"],
                level=4,
            )
            return False

    return try_transform_each(
        definitions,
        output_file_name,
        transformer,
        noun_description="Non-definition line removal",
        verb_description="remove non-definition lines",
        **kwargs,
    )


ABORT_REG = re.compile(r"\sAbort\s*\.\s*$")


def try_remove_aborted(definitions, output_file_name, **kwargs):
    return try_transform_reversed(
        definitions,
        output_file_name,
        (
            lambda definition, rest: None
            if ABORT_REG.search(definition["statement"])
            else definition
        ),
        noun_description="Aborted removal",
        verb_description="remove Aborts",
        **kwargs,
    )


LTAC_REG = re.compile(
    r"^\s*(?:Local\s+|Global\s+)?Ltac2?\s+([^\s]+)", flags=re.MULTILINE
)


def try_remove_ltac(definitions, output_file_name, **kwargs):
    return try_transform_reversed(
        definitions,
        output_file_name,
        try_remove_if_name_not_found_in_transformer(
            lambda definition: LTAC_REG.findall(
                definition["statement"].replace(
                    ":",
                    "\
 : ",
                )
            ),
            **kwargs,
        ),
        noun_description="Ltac removal",
        verb_description="remove Ltac",
        **kwargs,
    )


DEFINITION_ISH = r"Variables|Variable|Hypotheses|Hypothesis|Parameters|Parameter|Axioms|Axiom|Conjectures|Conjecture"
HINT_REG = re.compile(
    r"^\s*"
    + r"(?:Local\s+|Global\s+|Polymorphic\s+|Monomorphic\s+)*"
    + r"(?:"
    + r"Definition|Fixpoint|Record|Inductive"
    + r"|Coinductive|CoFixpoint"
    + r"|(?:Set|Unset)\s+(?:Universe\s+Polymorphism|Implicit\s+Arguments|Inductive|Polymorphic)"
    + r"|Notation|Reserved\s+Notation"
    + r"|Arguments|Implicit\s+Arguments"
    + r"|"
    + DEFINITION_ISH
    + r")\.?(?:\s+|$)"
)


def try_remove_hints(definitions, output_file_name, **kwargs):
    return try_transform_each(
        definitions,
        output_file_name,
        (
            lambda definition, rest: (
                None
                if len(definition["statements"]) == 1
                and not HINT_REG.match(definition["statement"])
                else definition
            )
        ),
        noun_description="Hint removal",
        verb_description="remove hints",
        **kwargs,
    )


VARIABLE_REG = re.compile(
    r"^\s*"
    + r"(?:Local\s+|Global\s+|Polymorphic\s+|Monomorphic\s+)*"
    + r"(?:"
    + DEFINITION_ISH
    + r")\s+"
    + r"([^\.:]+)",
    flags=re.MULTILINE,
)


def try_remove_variables(definitions, output_file_name, **kwargs):
    def get_names(definition):
        terms = VARIABLE_REG.findall(definition["statement"])
        return [i for i in sorted(set(j for term in terms for j in term.split(" ")))]

    return try_transform_reversed(
        definitions,
        output_file_name,
        try_remove_if_name_not_found_in_section_transformer(get_names, **kwargs),
        noun_description="Variable removal",
        verb_description="remove variables",
        **kwargs,
    )


CONTEXT_REG = re.compile(
    r"^\s*"
    + r"(?:Local\s+|Global\s+|Polymorphic\s+|Monomorphic\s+)*"
    + r"Context\s*`\s*[\({]\s*([^:\s]+)\s*:",
    flags=re.MULTILINE,
)


def try_remove_contexts(definitions, output_file_name, **kwargs):
    return try_transform_reversed(
        definitions,
        output_file_name,
        try_remove_if_name_not_found_in_section_transformer(
            lambda definition: CONTEXT_REG.findall(
                definition["statement"].replace(":", " : ")
            ),
            **kwargs,
        ),
        noun_description="Context removal",
        verb_description="remove Contexts",
        **kwargs,
    )


def try_admit_abstracts(definitions, output_file_name, **kwargs):
    def do_call(method, definitions, aggressive):
        return method(
            definitions,
            output_file_name,
            (
                lambda definition, rest_definitions: transform_abstract_to_admit(
                    definition,
                    rest_definitions,
                    aggressive=aggressive,
                    log=kwargs["log"],
                )
            ),
            noun_description="Admitting [abstract ...]",
            verb_description="[abstract ...] admits",
            **kwargs,
        )

    old_definitions = join_definitions(definitions)
    # for comparison, to see if things have changed first, try to do
    # everything at once; python cycles are assumed to be cheap in
    # comparison to coq cycles
    definitions = do_call(try_transform_reversed, definitions, True)
    new_definitions = join_definitions(definitions)
    if new_definitions != old_definitions:
        kwargs["log"](
            "Success with [abstract ...] admits on try_transform_reversed, aggressive: True, definitions:\n%s"
            % new_definitions,
            level=3,
        )
        return definitions

    # try the other options, each less aggressive than the last
    definitions = do_call(try_transform_reversed, definitions, False)
    new_definitions = join_definitions(definitions)
    if new_definitions != old_definitions:
        kwargs["log"](
            "Success with [abstract ...] admits on try_transform_reversed, aggressive: False, definitions:\n%s"
            % new_definitions,
            level=3,
        )
        return definitions

    definitions = do_call(try_transform_each, definitions, True)
    new_definitions = join_definitions(definitions)
    if new_definitions != old_definitions:
        kwargs["log"](
            "Success with [abstract ...] admits on try_transform_each, aggressive: True, definitions:\n%s"
            % new_definitions,
            level=3,
        )
        return definitions

    definitions = do_call(try_transform_each, definitions, False)
    new_definitions = join_definitions(definitions)
    if new_definitions != old_definitions:
        kwargs["log"](
            "Success with [abstract ...] admits on try_transform_each, aggressive: False, definitions:\n%s"
            % new_definitions,
            level=3,
        )
    else:
        kwargs["log"]("Failure with [abstract ...] admits.", level=3)
    return definitions


def statements_are_only_admitted(statements):
    proof_statements = [s.strip() for s in statements[1:]]
    proof_statements = [s for s in proof_statements if s]
    if len(proof_statements) == 0:
        return False
    if proof_statements[-1] == "Admitted.":
        proof_statements = proof_statements[:-1]
    elif len(proof_statements) >= 2 and tuple(proof_statements[-2:]) == (
        "admit.",
        "Defined.",
    ):
        proof_statements = proof_statements[:-2]
    else:
        return False
    if len(proof_statements) == 0:
        return True
    if len(proof_statements) == 1 and proof_statements[0].replace(" ", "") == "Proof.":
        return True
    if len(proof_statements) == 1 and re.match(
        r"^\s*Proof\s+using\s+", proof_statements[0]
    ):
        return True
    return False


def extract_existing_proof_using(statements):
    if len(statements) >= 2 and re.match(r"^\s*Proof\s+using\s+", statements[1]):
        return [statements[1]]
    return []


def extract_proof_using(cur_definition, **kwargs):
    proof_using = extract_existing_proof_using(cur_definition["statements"])
    if (
        (kwargs["add_proof_using_before_admit"] or kwargs["add_proof_using"])
        and not proof_using
        and cur_definition["proof_using_options"]
    ):
        proof_using_list = (
            cur_definition["proof_using_options"][0]
            if not kwargs["prefer_final_proof_using"]
            else cur_definition["proof_using_options"][-1]
        ).strip()
        proof_using = [f"Proof using {proof_using_list}."]

    return proof_using


def make_try_admit_matching_definitions(
    matcher, use_admitted=False, suppress_proof_using=False, **kwargs
):
    def transformer(cur_definition, rest_definitions):
        if (
            len(cur_definition["statements"]) > 2
            and matcher(cur_definition)
            and not statements_are_only_admitted(cur_definition["statements"])
        ):
            proof_using_block = (
                extract_proof_using(cur_definition, **kwargs)
                if not suppress_proof_using
                else []
            )
            statements = (
                cur_definition["statements"][0],
                *proof_using_block,
                *(("Admitted.",) if use_admitted else ("admit.", "Defined.")),
            )
            return {
                "statements": statements,
                "statement": "\n".join(statements),
                "terms_defined": cur_definition["terms_defined"],
                "proof_using_options": cur_definition["proof_using_options"],
                "proof_using_options_map": cur_definition["proof_using_options_map"],
            }
        else:
            return cur_definition

    def try_admit_matching_definitions(definitions, output_file_name, **kwargs2):
        return try_transform_reversed_or_else_each(
            definitions,
            output_file_name,
            transformer,
            **dict(list(kwargs.items()) + list(kwargs2.items())),
        )

    return try_admit_matching_definitions


def make_try_admit_qeds(**kwargs):
    QED_REG = re.compile(r"(?<![\w'])Qed\s*\.\s*$", flags=re.MULTILINE)
    return make_try_admit_matching_definitions(
        (lambda definition: QED_REG.search(definition["statement"])),
        noun_description="Admitting Qeds",
        verb_description="admit Qeds",
        **kwargs,
    )


def make_try_admit_lemmas(**kwargs):
    LEMMA_REG = re.compile(
        r"^\s*"
        + r"(?:Local\s+|Global\s+|Polymorphic\s+|Monomorphic\s+)*"
        + r"(?:Lemma|Remark|Fact|Corollary|Proposition)\s*",
        flags=re.MULTILINE,
    )
    return make_try_admit_matching_definitions(
        (lambda definition: LEMMA_REG.search(definition["statement"])),
        noun_description="Admitting lemmas",
        verb_description="admit lemmas",
        **kwargs,
    )


def make_try_admit_definitions(**kwargs):
    return make_try_admit_matching_definitions(
        (lambda definition: True),
        noun_description="Admitting definitions",
        verb_description="admit definitions",
        **kwargs,
    )


def try_add_proof_using(
    definitions,
    output_file_name,
    **kwargs,
):
    def transformer(cur_definition, rest_definitions):
        if (
            len(cur_definition["statements"]) > 2
            # and matcher(cur_definition)
            and cur_definition["proof_using_options"]
            and not extract_existing_proof_using(cur_definition["statements"])
        ):
            proof_using = (
                cur_definition["proof_using_options"][0]
                if not kwargs["prefer_final_proof_using"]
                else cur_definition["proof_using_options"][-1]
            )
            rest_statements = (
                cur_definition["statements"][2:]
                if cur_definition["statements"][1].strip().replace(" ", "") == "Proof."
                else cur_definition["statements"][1:]
            )
            statements = (
                cur_definition["statements"][0],
                f"Proof using {proof_using}.",
                *rest_statements,
            )
            return {
                "statements": statements,
                "statement": "\n".join(statements),
                "terms_defined": cur_definition["terms_defined"],
                "proof_using_options": cur_definition["proof_using_options"],
                "proof_using_options_map": cur_definition["proof_using_options_map"],
            }
        else:
            return cur_definition

    # def try_add_proof_using(definitions, output_file_name, **kwargs2):
    return try_transform_reversed_or_else_each(
        definitions,
        output_file_name,
        transformer,
        noun_description="Adding Proof using lines",
        verb_description="add Proof using lines",
        **kwargs,
    )


def try_split_imports(definitions, output_file_name, **kwargs):
    def transformer(cur_definition, rest_definitions):
        if (
            len(cur_definition["statements"]) > 1
            or any(ch in cur_definition["statement"] for ch in "*()")
            or cur_definition["statement"].strip()[-1] != "."
            or cur_definition["statement"].strip().replace("\n", " ").split(" ")[0]
            not in ("Import", "Export")
        ):
            return cur_definition
        else:
            terms = [
                i
                for i in cur_definition["statement"]
                .strip()
                .replace("\n", " ")[:-1]
                .split(" ")
                if i != ""
            ]
            import_or_export, terms = terms[0], terms[1:]
            pat = import_or_export + " %s."
            rtn_part = dict(cur_definition)
            rtn = []
            for term in terms:
                rtn_part["statement"] = pat % term
                rtn_part["statements"] = (pat % term,)
                rtn.append(dict(rtn_part))
            return tuple(rtn)

    return try_transform_each(
        definitions,
        output_file_name,
        transformer,
        noun_description="Import/Export splitting",
        verb_description="split Imports/Exports",
        **kwargs,
    )


def try_admit_matching_obligations(definitions, output_file_name, matcher, **kwargs):
    OBLIGATION_REG = re.compile(
        r"^\s*(Next\s+Obligation|Obligation\s+[0-9]+)\b", flags=re.DOTALL
    )

    def transformer(cur_definition, rest_definitions):
        if (
            len(cur_definition["statements"]) > 1
            and OBLIGATION_REG.match(cur_definition["statements"][0])
            and matcher(cur_definition)
        ):
            statements = ("Admit Obligations.",)
            return {
                "statements": statements,
                "statement": "\n".join(statements),
                "terms_defined": cur_definition["terms_defined"],
                "proof_using_options": (),
                "proof_using_options_map": (),
            }
        else:
            return cur_definition

    return try_transform_reversed_or_else_each(
        definitions, output_file_name, transformer, **kwargs
    )


def try_admit_qed_obligations(definitions, output_file_name, **kwargs):
    QED_REG = re.compile(r"(?<![\w'])(Qed|Admitted)\s*\.\s*$", flags=re.MULTILINE)
    return try_admit_matching_obligations(
        definitions,
        output_file_name,
        (lambda definition: QED_REG.search(definition["statement"])),
        noun_description="Admitting Qed Obligations",
        verb_description="admit Qed Obligations",
        **kwargs,
    )


def try_admit_obligations(definitions, output_file_name, **kwargs):
    return try_admit_matching_obligations(
        definitions,
        output_file_name,
        (lambda definition: True),
        noun_description="Admitting Obligations",
        verb_description="admit Obligations",
        **kwargs,
    )


def try_split_oneline_definitions(definitions, output_file_name, **kwargs):
    def update_paren(in_string, paren_count, new_string):
        for ch in new_string:
            if in_string:
                if ch == '"':
                    in_string = False
            else:
                if ch == '"':
                    in_string = True
                elif ch == "(":
                    paren_count += 1
                elif ch == ")":
                    paren_count -= 1
        return (in_string, paren_count)

    def transformer(cur_definition, rest_definitions):
        if (
            len(cur_definition["statements"]) > 1
            or cur_definition["statement"].strip()[-1] != "."
            or ":=" not in cur_definition["statement"]
            or len(cur_definition["terms_defined"]) != 1
        ):
            return cur_definition
        else:
            terms = cur_definition["statement"].strip()[:-1].split(":=")
            pre_statement = terms[0]
            in_string, paren_count = update_paren(False, 0, pre_statement)
            for i, term in list(enumerate(terms))[1:]:
                if not in_string and paren_count == 0:
                    rtn_part = dict(cur_definition)
                    rtn_part["statements"] = (
                        pre_statement.rstrip() + ".",
                        "exact (%s)." % ":=".join(terms[i:]).strip(),
                        "Defined.",
                    )
                    rtn_part["statement"] = " ".join(rtn_part["statements"])
                    return rtn_part
                else:
                    in_string, paren_count = update_paren(in_string, paren_count, term)
                    pre_statement = ":=" + term
            return cur_definition

    return try_transform_each(
        definitions,
        output_file_name,
        transformer,
        noun_description="One-line definition splitting",
        verb_description="split one-line definitions",
        **kwargs,
    )


MODULE_REG = re.compile(r"^(\s*Module)(\s+[^\s\.]+\s*\.\s*)$")


def try_export_modules(definitions, output_file_name, **kwargs):
    def transformer(cur_definition, rest_definitions):
        if len(cur_definition["statements"]) > 1 or not MODULE_REG.match(
            cur_definition["statement"]
        ):
            return cur_definition
        else:
            new_statement = MODULE_REG.sub(r"\1 Export\2", cur_definition["statement"])
            rtn = dict(cur_definition)
            rtn["statement"] = new_statement
            rtn["statements"] = (new_statement,)
            return rtn

    return try_transform_each(
        definitions,
        output_file_name,
        transformer,
        noun_description="Module exportation",
        verb_description="export modules",
        **kwargs,
    )


def try_strip_comments(output_file_name, **kwargs):
    contents = read_from_file(output_file_name)
    old_contents = contents
    new_contents = strip_comments(contents)

    check_change_and_write_to_file(
        old_contents,
        new_contents,
        output_file_name,
        unchanged_message="No strippable comments.",
        success_message="Succeeded in stripping comments.",
        failure_description="strip comments",
        changed_descruption="Stripped comments file",
        **kwargs,
    )


def try_normalize_requires(output_file_name, **kwargs):
    contents = read_from_file(output_file_name)
    old_contents = contents
    # we need to clear the libimport cache to get an accurate list of requires
    clear_libimport_cache(lib_of_filename(output_file_name, **kwargs))
    new_contents = normalize_requires(output_file_name, update_globs=True, **kwargs)

    check_change_and_write_to_file(
        old_contents,
        new_contents,
        output_file_name,
        unchanged_message="No Requires to normalize.",
        success_message="Succeeded in normalizing Requires.",
        failure_description="normalize Requires",
        changed_descruption="Normalized Requires file",
        **kwargs,
    )


def try_split_requires(output_file_name, **kwargs):
    contents = read_from_file(output_file_name)
    old_contents = contents
    annotated_contents = get_file_statements_insert_references(
        output_file_name, update_globs=True, types=("lib",), appends=("<>",), **kwargs
    )
    if annotated_contents is None:
        kwargs["log"](
            "\nNon-fatal error: Failed to get references for %s" % output_file_name,
            level=LOG_ALWAYS,
        )
        return False

    try:
        annotated_contents = split_requires_of_statements(annotated_contents, **kwargs)
        new_contents = "".join(v[0].decode("utf-8") for v in annotated_contents)
    except UnicodeDecodeError as e:
        kwargs["log"](
            "\nNon-fatal error: Invalid non-UTF-8 (maybe an outdated .glob file for %s?): %s"
            % (output_file_name, str(e)),
            level=LOG_ALWAYS,
        )
        return False

    return check_change_and_write_to_file(
        old_contents,
        new_contents,
        output_file_name,
        unchanged_message="No Requires to split.",
        success_message="Succeeded in splitting Requires.",
        failure_description="split Requires",
        changed_descruption="Split Requires file",
        **kwargs,
    )


def try_strip_newlines(
    output_file_name, max_consecutive_newlines, strip_trailing_space, **kwargs
):
    contents = read_from_file(output_file_name)
    old_contents = contents
    if strip_trailing_space:
        contents = "\n".join(line.rstrip() for line in contents.split("\n"))
    new_contents = strip_newlines(contents, max_consecutive_newlines)

    check_change_and_write_to_file(
        old_contents,
        new_contents,
        output_file_name,
        unchanged_message="No strippable newlines or spaces.",
        success_message="Succeeded in stripping newlines and spaces.",
        failure_description="strip newlines and spaces",
        changed_descruption="Stripped file",
        **kwargs,
    )


def try_strip_extra_lines(output_file_name, statements, line_num, **kwargs):
    cur_line_num = 0
    new_statements = statements
    kwargs["log"](f"Trimming file to line {line_num}...", level=4)
    for statement_num, statement in enumerate(statements):
        cur_line_num += (
            statement.count("\n") + 1
        )  # +1 for the extra newline between each statement
        kwargs["log"](f"Line {cur_line_num}: {statement!r}", level=4)
        if cur_line_num >= line_num:
            new_statements = statements[: statement_num + 1]
            break

    if check_change_and_write_to_file(
        "\n".join(statements),
        "\n".join(new_statements),
        output_file_name,
        unchanged_message="No lines to trim.",
        success_message=(
            "Trimming successful.  We removed all lines after %d; the error was on line %d."
            % (cur_line_num, line_num)
        ),
        failure_description="trim file",
        changed_descruption="Trimmed file",
        **kwargs,
    ):
        kwargs["log"]("Trimmed file:\n%s" % read_from_file(output_file_name), level=3)


def try_remove_section_module_transformer(
    *, remove_section: bool = True, remove_module: bool = True, **kwargs
):
    SECTION_BEGIN_REG = re.compile(
        r"^\s*Section\s+([^\.\s]+)\s*\.\s*$", flags=re.DOTALL
    )
    MODULE_BEGIN_REG = re.compile(
        r"^\s*Module\s+(?:(?:Import|Export|Type)\s+)?([^\.\s\(:=]+)\s*\.\s*$",
        flags=re.DOTALL,
    )
    MODULE_SECTION_BEGIN_REG = re.compile(
        r"^\s*(?:Section|Module(?:\s+(?:Import|Export|Type))?)\s+([^\.\s\(:=]+)",
        flags=re.DOTALL,
    )
    WITH_REG = re.compile(r"\s+with\s+[^\s]+\s*:=", flags=re.DOTALL)
    END_REG = lambda name: re.compile(
        rf"^\s*End\s+{re.escape(name)}\s*\.\s*$", flags=re.DOTALL
    )

    def transformer(cur_definition, rest_definitions):
        sections = SECTION_BEGIN_REG.findall(cur_definition["statement"])
        modules = MODULE_BEGIN_REG.findall(cur_definition["statement"])
        mod_assign = ":=" in WITH_REG.sub("", cur_definition["statement"])
        if not (sections and remove_section) and not (
            modules and remove_module and not mod_assign
        ):
            return cur_definition, rest_definitions
        name = sections[0] if sections else modules[0]
        end_reg = END_REG(name)
        similar_section_level = 0
        for i, future_definition in enumerate(rest_definitions):
            if similar_section_level < 0:
                # remove the section/module and the end
                return None, rest_definitions[: i - 1] + rest_definitions[i:]
            mod_sec_names = MODULE_SECTION_BEGIN_REG.findall(
                future_definition["statement"]
            )
            end_match = end_reg.match(future_definition["statement"])
            if end_match:
                similar_section_level -= 1
            elif mod_sec_names and name in mod_sec_names:
                mod_assign = ":=" in WITH_REG.sub("", future_definition["statement"])
                if not mod_assign:
                    similar_section_level += 1
        if end_reg.search("\n".join(d["statement"] for d in rest_definitions)):
            kwargs["log"](
                "Warning: Section/Module %s not closed in a recognizable way." % name,
                level=2,
            )
            kwargs["log"](
                "Contents:\n%s" % "\n".join(d["statement"] for d in rest_definitions),
                level=4,
            )
        return cur_definition, rest_definitions

    return transformer


def try_remove_module_sections(
    definitions,
    output_file_name,
    *,
    remove_section: bool = True,
    remove_module: bool = True,
    **kwargs,
):
    if remove_section and remove_module:
        noun_description = "Section/Module removal"
        verb_description = "remove Sections/Modules"
    elif remove_section and not remove_module:
        noun_description = "Section removal"
        verb_description = "remove Sections"
    elif not remove_section and remove_module:
        noun_description = "Module removal"
        verb_description = "remove Modules"
    elif not remove_section and not remove_module:
        return definitions
    return try_transform_reversed_or_else_each(
        definitions,
        output_file_name,
        try_remove_section_module_transformer(
            remove_section=remove_section, remove_module=remove_module, **kwargs
        ),
        noun_description=noun_description,
        verb_description=verb_description,
        returns_all_definitions=True,
        **kwargs,
    )


def try_remove_modules(definitions, output_file_name, **kwargs):
    return try_remove_module_sections(
        definitions,
        output_file_name,
        remove_section=False,
        remove_module=True,
        **kwargs,
    )


def try_remove_sections(definitions, output_file_name, **kwargs):
    return try_remove_module_sections(
        definitions,
        output_file_name,
        remove_section=True,
        remove_module=False,
        **kwargs,
    )


EMPTY_SECTION_REG = re.compile(
    r"(\.\s+|^\s*)(?:Section|Module\s+Export|Module)\s+([^ \.]+)\."
    + r"(?:\s"
    + r"|Local\s"
    r"|Set\s+Universe\s+Polymorphism\s*\.\s"
    + r"|Unset\s+Universe\s+Polymorphism\s*\.\s)+End\s+([^ \.]+)\.(\s+|$)",
    flags=re.MULTILINE,
)


def try_strip_empty_sections(output_file_name, **kwargs):
    contents = read_from_file(output_file_name)
    old_contents = contents
    new_contents = EMPTY_SECTION_REG.sub(r"\1", old_contents)
    while new_contents != old_contents:
        old_contents, new_contents = (
            new_contents,
            EMPTY_SECTION_REG.sub(r"\1", new_contents),
        )

    check_change_and_write_to_file(
        contents,
        new_contents,
        output_file_name,
        unchanged_message="No empty sections to remove.",
        success_message="Empty section removal successful.",
        failure_description="remove empty sections",
        changed_descruption="Trimmed file",
        **kwargs,
    )


def remove_admit_tactic(contents, tac_code: str = "", **kwargs):
    before, after = get_ltac_support_snippet(**kwargs)
    tac_code_re = r"""\s*Module Export AdmitTactic\.
?(?:Module Import LocalFalse\.)?
?(?:Inductive False : Prop := \.)?
?(End LocalFalse\.)?
?(?:Axiom proof_admitted : False\.)?
?(?:%s)?(?:Tactic Notation "admit" := abstract case proof_admitted\.)?
?End AdmitTactic\.\n*""" % re.escape(after)
    tac_code_re2 = r"""\s*(?:Module Import LocalFalse\.)?
?(?:Inductive False : Prop := \.)?
?(End LocalFalse\.)?
?(?:Axiom proof_admitted : False\.)?
?(?:%s)?Tactic Notation "admit" := abstract case proof_admitted\.
?\n*""" % re.escape(after)
    header, contents = split_leading_comments_and_whitespace(contents)
    return "%s%s%s" % (
        header,
        tac_code,
        re.sub(
            tac_code_re,
            "\n",
            re.sub(
                tac_code_re2,
                "\n",
                contents.replace(before, ""),
                flags=re.DOTALL | re.MULTILINE,
            ),
            flags=re.DOTALL | re.MULTILINE,
        ),
    )


def add_admit_tactic(contents, **kwargs):
    before, after = get_ltac_support_snippet(**kwargs)
    tac_code = r"""%sModule Export AdmitTactic.
Module Import LocalFalse.
Inductive False : Prop := .
End LocalFalse.
Axiom proof_admitted : False.
%sTactic Notation "admit" := abstract case proof_admitted.
End AdmitTactic.
""" % (
        before,
        after,
    )
    return remove_admit_tactic(contents, tac_code=tac_code, **kwargs)


def try_remove_admit_tactic_header(output_file_name, **kwargs):
    contents = read_from_file(output_file_name)
    old_contents = contents
    new_contents = remove_admit_tactic(contents, **kwargs)

    check_change_and_write_to_file(
        old_contents,
        new_contents,
        output_file_name,
        unchanged_message="No admit tactic header to remove",
        success_message="Admit tactic header removal successful.",
        failure_description="remove admit tactic header",
        changed_descruption="Removed admit tactic header",
        **kwargs,
    )


def try_add_admit_tactic_header(output_file_name, **kwargs):
    contents = read_from_file(output_file_name)
    old_contents = contents
    new_contents = add_admit_tactic(contents, **kwargs)
    if not check_change_and_write_to_file(
        old_contents,
        new_contents,
        output_file_name,
        unchanged_message="Admit tactic wrapper already present!",
        success_message="Admit tactic wrapper added.",
        failure_description="add admit tactic wrapper",
        changed_description="File",
        timeout_retry_count=SENSITIVE_TIMEOUT_RETRY_COUNT,
        write_to_temp_file=True,
        **kwargs,
    ):
        kwargs["log"]("Failed to add admit tactic wrapper, skipping...")


def default_on_fatal(message, log=DEFAULT_LOG, **env):
    if message is not None:
        log(message, level=0, force_stderr=True)
    sys.exit(1)


def minimize_file(
    output_file_name,
    die=default_on_fatal,
    return_after_requires=False,
    return_after_splitting=False,
    **env,
):
    """The workhorse of bug minimization.  The only thing it doesn't handle is inlining [Require]s and other preprocesing"""
    contents = read_from_file(output_file_name)

    coqc_help = get_coqc_help(get_preferred_passing("coqc", **env), **env)
    env["header_dict"] = get_header_dict(contents, **env)

    if not check_change_and_write_to_file(
        "",
        contents,
        output_file_name,
        unchanged_message="Invalid empty file!",
        success_message="Sanity check passed.",
        failure_description="validate all coq runs",
        changed_description="File",
        timeout_retry_count=SENSITIVE_TIMEOUT_RETRY_COUNT,
        write_to_temp_file=True,
        **env,
    ):
        if os.path.exists(output_file_name):
            env["log"](
                "\nMoving %s to %s..." % (output_file_name, env["temp_file_name"])
            )
            write_to_file(env["temp_file_name"], read_from_file(output_file_name))
            os.remove(output_file_name)
        return die("Fatal error: Sanity check failed.", **env)

    if env["admit_transparent"] or env["admit_opaque"]:
        env["log"](
            "\nNow, I will attempt to add an admit tactic wrapper to this file..."
        )
        try_add_admit_tactic_header(output_file_name, **env)

    if env["max_consecutive_newlines"] >= 0 or env["strip_trailing_space"]:
        env["log"](
            "\nNow, I will attempt to strip repeated newlines and trailing spaces from this file..."
        )
        try_strip_newlines(output_file_name, **env)

    contents = read_from_file(output_file_name)
    original_line_count = len(contents.split("\n"))
    env["header_dict"]["original_line_count"] = original_line_count

    if env["remove_comments"]:
        env["log"]("\nNow, I will attempt to strip the comments from this file...")
        try_strip_comments(output_file_name, **env)

    if env["normalize_requires"]:
        env["log"]("\nNow, I will attempt to factor out all of the [Require]s...")
        try_normalize_requires(output_file_name, **env)

        if env["split_requires"]:
            env["log"]("\nNow, I will attempt to split up [Require] statements...")
            try_split_requires(output_file_name, **env)

    if return_after_requires:
        return True

    contents = read_from_file(output_file_name)
    env["log"](
        "\nIn order to efficiently manipulate the file, I have to break it into statements.  I will attempt to do this by matching on periods."
    )
    strings = re.findall(r'"[^"\n\r]+"', contents)
    bad_strings = [
        i for i in strings if re.search(r"(?<=[^\.]\.\.\.)\s|(?<=[^\.]\.)\s", i)
    ]
    if bad_strings:
        env["log"](
            'If you have periods in strings, and these periods are essential to generating the error, then this process will fail.  Consider replacing the string with some hack to get around having a period and then a space, like ["a. b"%string] with [("a." ++ " b")%string].'
        )
        env["log"](
            "You have the following strings with periods in them:\n%s"
            % "\n".join(bad_strings)
        )
    statements = split_coq_file_contents(contents)
    if not check_change_and_write_to_file(
        "",
        "\n".join(statements),
        output_file_name,
        unchanged_message="Invalid empty file!",
        success_message="Splitting successful.",
        failure_description="split file to statements",
        changed_description="Split",
        timeout_retry_count=SENSITIVE_TIMEOUT_RETRY_COUNT,
        **env,
    ):
        env["log"]("I will not be able to proceed.")
        env["log"](
            "re.search(" + repr(env["error_reg_string"]) + ", <output above>)", level=2
        )
        return die(None, **env)

    if not env["should_succeed"]:
        env["log"](
            "\nI will now attempt to remove any lines after the line which generates the error."
        )
        output, cmds, retcode, runtime = diagnose_error.get_coq_output(
            env["coqc"],
            env["coqc_args"],
            "\n".join(statements),
            env["timeout"],
            is_coqtop=env["coqc_is_coqtop"],
            verbose_base=2,
            cwd=env["base_dir"],
            ocamlpath=env["nonpassing_ocamlpath"],
            **env,
        )
        line_num = diagnose_error.get_error_line_number(output, env["error_reg_string"])
        try_strip_extra_lines(output_file_name, statements, line_num, **env)

    env["log"](
        "\nIn order to efficiently manipulate the file, I have to break it into definitions.  I will now attempt to do this."
    )
    contents = read_from_file(output_file_name)
    statements = split_coq_file_contents(contents)
    env["log"]("I am using the following file: %s" % "\n".join(statements), level=3)
    definitions = split_statements_to_definitions(statements, **env)
    if not check_change_and_write_to_file(
        "",
        join_definitions(definitions),
        output_file_name,
        unchanged_message="Invalid empty file!",
        success_message="Splitting to definitions successful.",
        failure_description="split file to definitions",
        changed_description="Split",
        timeout_retry_count=SENSITIVE_TIMEOUT_RETRY_COUNT,
        **env,
    ):
        env["log"]("I will not be able to proceed.")
        env["log"](
            "re.search(" + repr(env["error_reg_string"]) + ", <output above>)", level=2
        )
        return die(None, **env)

    if return_after_splitting:
        return True

    recursive_tasks = ()
    if env["remove_abort"]:
        recursive_tasks += (("remove goals ending in [Abort.]", try_remove_aborted),)
    if env["remove_ltac"]:
        recursive_tasks += (("remove unused Ltacs", try_remove_ltac),)
    if not env["should_succeed"]:
        recursive_tasks += (
            ("remove unused definitions", try_remove_definitions),
            (
                "remove unused non-instance, non-canonical structure definitions",
                try_remove_non_instance_definitions,
            ),
        )
    if env["remove_section_variables"]:
        recursive_tasks += (
            ("remove unused variables", try_remove_variables),
            ("remove unused contexts", try_remove_contexts),
        )

    tasks = recursive_tasks
    if env["add_proof_using_before_admit"] and not (
        env["admit_opaque"] and env["admit_transparent"]
    ):
        tasks += (("add Proof using lines", try_add_proof_using),)
    if env["admit_opaque"]:
        if env["admit_obligations"]:
            tasks += (
                (
                    "replace Qed Obligation with Admit Obligations",
                    try_admit_qed_obligations,
                ),
            )
        for suppress_proof_using in (
            (False,) if env["add_proof_using_before_admit"] else (True, False)
        ):
            with_proof_using_suffix = (
                ""
                if suppress_proof_using
                or not (env["add_proof_using"] or env["add_proof_using_before_admit"])
                else " with Proof using"
            )
            tasks += (
                (
                    f"replace Qeds with Admitteds{with_proof_using_suffix}",
                    make_try_admit_qeds(
                        use_admitted=True,
                        suppress_proof_using=suppress_proof_using,
                        **env,
                    ),
                ),
                (
                    f"replace Qeds with admit. Defined.{with_proof_using_suffix}",
                    make_try_admit_qeds(
                        use_admitted=False,
                        suppress_proof_using=suppress_proof_using,
                        **env,
                    ),
                ),
            )
        tasks += (
            # we've probably just removed a lot, so try to remove definitions again
            recursive_tasks
            + (("admit [abstract ...]s", try_admit_abstracts),)
            +
            # we've probably just removed a lot, so try to remove definitions again
            recursive_tasks
        )

    if not env["aggressive"] and not env["should_succeed"]:
        tasks += (
            ("remove unused definitions, one at a time", try_remove_each_definition),
        )

    if env["admit_transparent"]:
        if env["admit_obligations"]:
            tasks += (
                ("replace Obligation with Admit Obligations", try_admit_obligations),
            )
        for suppress_proof_using in (
            (False,) if env["add_proof_using_before_admit"] else (True, False)
        ):
            proof_using_suffix = (
                ""
                if suppress_proof_using
                or not (env["add_proof_using"] or env["add_proof_using_before_admit"])
                else " with Proof using"
            )
            tasks += (
                (
                    f"admit lemmas with Admitted{proof_using_suffix}",
                    make_try_admit_lemmas(
                        use_admitted=True,
                        suppress_proof_using=suppress_proof_using,
                        **env,
                    ),
                ),
                (
                    f"admit definitions with Admitted{proof_using_suffix}",
                    make_try_admit_definitions(
                        use_admitted=True,
                        suppress_proof_using=suppress_proof_using,
                        **env,
                    ),
                ),
                (
                    f"admit lemmas with admit. Defined{proof_using_suffix}",
                    make_try_admit_lemmas(
                        use_admitted=False,
                        suppress_proof_using=suppress_proof_using,
                        **env,
                    ),
                ),
                (
                    f"admit definitions with admit. Defined{proof_using_suffix}",
                    make_try_admit_definitions(
                        use_admitted=False,
                        suppress_proof_using=suppress_proof_using,
                        **env,
                    ),
                ),
            )

    if env["add_proof_using"]:
        tasks += (("add Proof using lines", try_add_proof_using),)

    if not env["aggressive"] and not env["save_typeclasses"] and env["remove_hints"]:
        tasks += (("remove hints", try_remove_hints),)

    if env["export_modules"]:
        tasks += (("export modules", try_export_modules),)

    if env["split_imports"]:
        tasks += (("split imports and exports", try_split_imports),)

    if not env["should_succeed"]:
        tasks += (("split := definitions", try_split_oneline_definitions),)

    if env["aggressive"] and not env["should_succeed"]:
        tasks += (
            (("remove all lines, one at a time", try_remove_each_and_every_line),)
            +
            # we've probably just removed a lot, so try to remove definitions again
            recursive_tasks
        )

    if env["remove_non_definitions"]:
        tasks += (
            (
                (
                    "remove all lines that don't add constants to the global environment, one at a time",
                    try_remove_each_and_every_non_definition_line,
                ),
            )
            +
            # we've probably just removed a lot, so try to remove definitions again
            recursive_tasks
        )

    if env["remove_modules"]:
        tasks += (("remove modules", try_remove_modules),)
    if env["remove_sections"]:
        tasks += (("remove sections", try_remove_sections),)

    old_definitions = ""
    while old_definitions != join_definitions(definitions):
        old_definitions = join_definitions(definitions)
        env["log"]("Definitions:", level=2)
        env["log"](definitions, level=2)

        for description, task in tasks:
            env["log"]("\nI will now attempt to %s" % description)
            definitions = task(definitions, output_file_name, **env)

    if env["remove_empty_sections"]:
        env["log"]("\nI will now attempt to remove empty sections")
        try_strip_empty_sections(output_file_name, **env)

    env["log"]("\nI will now attempt to remove the admit tactic header")
    try_remove_admit_tactic_header(output_file_name, **env)

    if env["max_consecutive_newlines"] >= 0 or env["strip_trailing_space"]:
        env["log"](
            "\nNow, I will attempt to strip repeated newlines and trailing spaces from this file..."
        )
        try_strip_newlines(output_file_name, **env)

    return True


def add_coqlib_prelude_import(contents, **env):
    return "Require Coq.Init.Prelude.\nImport Coq.Init.Prelude.\n" + contents


def make_cur_output_gen(output_file_name, **kwargs):
    if kwargs["admit_transparent"] or kwargs["admit_opaque"]:
        add_admit_tactic_wrapper = add_admit_tactic
    else:
        add_admit_tactic_wrapper = lambda x, **kwargs: x

    return (
        lambda mod_remap: add_admit_tactic_wrapper(
            get_file(output_file_name, mod_remap=mod_remap, **kwargs), **kwargs
        ).strip()
        + "\n"
    )


def inline_one_require(
    output_file_name, libname_blacklist, cur_output, check_should_break, **kwargs
):
    if kwargs["admit_transparent"] or kwargs["admit_opaque"]:
        add_admit_tactic_wrapper = add_admit_tactic
    else:
        add_admit_tactic_wrapper = lambda x, **kwargs: x
    cur_output_gen = make_cur_output_gen(output_file_name, **kwargs)
    requires = recursively_get_requires_from_file(
        output_file_name, update_globs=True, **kwargs
    )

    STRIP_ADMIT_TACTIC_WRAPPER = "STRIP_ADMIT_TACTIC_WRAPPER"
    ADD_ADMIT_TACTIC_WRAPPER = "ADD_ADMIT_TACTIC_WRAPPER"

    def get_test_output(
        req_module: str,
        absolutize_mods=False,
        first_wrap_then_include=True,
        without_require=True,
        insert_at_top=False,
        extra_top_header=None,
        include_options_settings=False,
        admit_tactic_wrapper_action=ADD_ADMIT_TACTIC_WRAPPER,
    ):
        new_req_module = absolutize_and_mangle_libname(
            req_module, first_wrap_then_include=first_wrap_then_include, **kwargs
        )
        test_output = (
            cur_output
            if not absolutize_mods
            else cur_output_gen({req_module: new_req_module})
        )
        if not absolutize_mods:
            cur_rep = rep
        else:
            cur_rep = "\nRequire %s.\n" % new_req_module
        if cur_rep not in "\n" + test_output:
            kwargs["log"]("\nWarning: I cannot find Require %s." % new_req_module)
            kwargs["log"]("in contents:\n" + test_output, level=3)
        extra_contents_inside_module = ""
        require_statements_before_replacement = ""
        if include_options_settings or without_require:
            all_imports = get_recursive_require_names(
                req_module, reverse=False, **kwargs
            )  # like run_recursively_get_imports, but get_recursive_require_names also strips off the self module
            require_statements = "".join("Require %s.\n" % i for i in all_imports)
            if without_require:
                require_statements_before_replacement = "\n" + require_statements
            if include_options_settings:
                extra_contents_inside_module = get_default_options_settings(
                    kwargs["coqc"],
                    after_contents=require_statements,
                    prefix="Local ",
                    **kwargs,
                )
        replacement = (
            require_statements_before_replacement
            + "\n"
            + get_required_contents(
                req_module,
                first_wrap_then_include=first_wrap_then_include,
                without_require=without_require,
                extra_top_header=extra_top_header,
                extra_contents_inside_module=extra_contents_inside_module,
                **kwargs,
            ).strip()
            + "\n"
        )
        if insert_at_top:
            header, test_output = split_leading_comments_and_whitespace(test_output)
            body = (
                header
                + replacement
                + "\n"
                + ("\n" + test_output).replace(cur_rep, "\n")
            ).strip() + "\n"
            if admit_tactic_wrapper_action == STRIP_ADMIT_TACTIC_WRAPPER:
                return remove_admit_tactic(body, **kwargs)
            elif admit_tactic_wrapper_action == ADD_ADMIT_TACTIC_WRAPPER:
                return add_admit_tactic_wrapper(
                    body,
                    **kwargs,
                )
            else:
                return body

        else:
            body = ("\n" + test_output).replace(cur_rep, replacement, 1).replace(
                cur_rep, "\n"
            ).strip() + "\n"
            if admit_tactic_wrapper_action == STRIP_ADMIT_TACTIC_WRAPPER:
                return remove_admit_tactic(body, **kwargs)
            else:
                return body

    for req_module in reversed(requires):
        if req_module in libname_blacklist:
            continue
        else:
            libname_blacklist.append(req_module)
        rep = "\nRequire %s.\n" % req_module
        if rep not in "\n" + cur_output:
            kwargs["log"]("\nWarning: I cannot find Require %s." % req_module)
            kwargs["log"]("in contents:\n" + cur_output, level=3)
            continue
        try:
            # we prefer wrapping modules via Include,
            # because this is a bit more robust against
            # future module inlining (see example test 45)
            # we try option settings before trying anything else because option settings are the most robust to future changes
            test_output_alts = [
                (
                    (
                        (
                            " without Include"
                            if not first_wrap_then_include
                            else " via Include"
                        )
                        + (", absolutizing mod references" if absolutize_mods else "")
                        + (
                            ", stripping Requires"
                            if without_require
                            else ", with Requires"
                        )
                        + (", inserting at the top" if insert_at_top else "")
                        + (
                            f", with {extra_top_header} at the top"
                            if extra_top_header
                            else ""
                        )
                        + (
                            ", with explicit setting of options"
                            if include_options_settings
                            else ""
                        )
                        + {
                            ADD_ADMIT_TACTIC_WRAPPER: ", re-adding admit tactic wrapper",
                            STRIP_ADMIT_TACTIC_WRAPPER: ", without admit tactic wrapper",
                        }.get(
                            admit_tactic_wrapper_action,
                            ", leaving admit tactic wrapper alone",
                        )
                    ),
                    get_test_output(
                        req_module,
                        absolutize_mods=absolutize_mods,
                        first_wrap_then_include=first_wrap_then_include,
                        without_require=without_require,
                        insert_at_top=insert_at_top,
                        extra_top_header=extra_top_header,
                        include_options_settings=include_options_settings,
                        admit_tactic_wrapper_action=admit_tactic_wrapper_action,
                    ),
                )
                for admit_tactic_wrapper_action in (
                    ADD_ADMIT_TACTIC_WRAPPER,
                    "",
                    STRIP_ADMIT_TACTIC_WRAPPER,
                )
                for absolutize_mods in (False, True)
                for first_wrap_then_include in (
                    (True, False)
                    if kwargs["prefer_inline_via_include"]
                    else (False, True)
                )
                for without_require, insert_at_top in (
                    (True, False),
                    (False, True),
                    (False, False),
                    (True, True),
                )
                for extra_top_header in (None, "Import Coq.Init.Prelude.")
                for include_options_settings in (False, True)
            ]
            (test_output_descr, test_output), test_output_alts = (
                test_output_alts[0],
                test_output_alts[1:],
            )
        except IOError as e:
            kwargs["log"](
                "\nWarning: Cannot inline %s (%s)\nRecursively Searched: %s\nNonrecursively Searched: %s"
                % (
                    req_module,
                    str(e),
                    str(tuple(kwargs["libnames"])),
                    str(tuple(kwargs["non_recursive_libnames"])),
                )
            )
            continue

        temp_file_base, temp_ext = os.path.splitext(kwargs["temp_file_name"])
        temp_log_file_base, temp_log_ext = os.path.splitext(
            kwargs["temp_file_log_name"]
        )
        file_suffixes = [
            f"{req_module}{test_output_descr}".replace(" ", "-")
            .replace(",", "-")
            .replace(".", "-")
            for test_output_descr, _test_output in test_output_alts
        ]
        temp_file_names = [
            f"{temp_file_base}.{suffix}{temp_ext}.orig" for suffix in file_suffixes
        ]
        temp_log_file_names = [
            f"{temp_log_file_base}.{suffix}{temp_log_ext}.orig"
            for suffix in file_suffixes
        ]

        if not check_change_and_write_to_file(
            cur_output,
            test_output,
            output_file_name,
            unchanged_message="Invalid empty file!",
            success_message=(
                "Inlining %s%s succeeded." % (req_module, test_output_descr)
            ),
            failure_description=("inline %s%s" % (req_module, test_output_descr)),
            changed_description="File",
            reset_timeout=True,
            timeout_retry_count=SENSITIVE_TIMEOUT_RETRY_COUNT,  # is this the right retry count?
            display_source_to_error=False,
            display_extra_verbose_on_error=kwargs["verbose_include_failure_warning"],
            **kwargs,
        ):
            # any lazily evaluates the iterator, so we'll
            # only run the check up to the point of the
            # first success
            if not any(
                check_change_and_write_to_file(
                    cur_output,
                    test_output_alt,
                    output_file_name,
                    unchanged_message="Invalid empty file!",
                    success_message=("Inlining %s%s succeeded." % (req_module, descr)),
                    failure_description=("inline %s%s" % (req_module, descr)),
                    changed_description="File",
                    timeout_retry_count=SENSITIVE_TIMEOUT_RETRY_COUNT,  # is this the right retry count?
                    # reset the timeout on each different
                    # way of inlining, so that an earlier
                    # one failing doesn't hobble the
                    # ability of a later one to succeed
                    reset_timeout=True,
                    display_source_to_error=True,
                    display_extra_verbose_on_error=kwargs[
                        "verbose_include_failure_warning"
                    ],
                    write_to_temp_file=True,
                    **(
                        kwargs
                        | {
                            "temp_file_name": temp_file_name,
                            "temp_file_log_name": temp_log_file_name,
                        }
                    ),
                )
                for (descr, test_output_alt), temp_file_name, temp_log_file_name in zip(
                    test_output_alts, temp_file_names, temp_log_file_names
                )
            ):
                # let's also display the error and source
                # for the original failure to inline,
                # without the Include, so we can see
                # what's going wrong in both cases
                check_change_and_write_to_file(
                    cur_output,
                    test_output,
                    output_file_name,
                    unchanged_message="Invalid empty file!",
                    success_message=(
                        "Inlining %s%s succeeded." % (req_module, test_output_descr)
                    ),
                    failure_description=(
                        "inline %s%s" % (req_module, test_output_descr)
                    ),
                    changed_description="File",
                    timeout_retry_count=SENSITIVE_TIMEOUT_RETRY_COUNT,  # is this the right retry count?
                    reset_timeout=True,
                    display_source_to_error=True,
                    display_extra_verbose_on_error=kwargs[
                        "verbose_include_failure_warning"
                    ],
                    write_to_temp_file=True,
                    **kwargs,
                )

                for fname in temp_file_names + temp_log_file_names:
                    if os.path.exists(fname):
                        assert fname.endswith(".orig"), fname
                        os.rename(fname, fname[: -len(".orig")])
                    else:
                        kwargs["log"](f"Warning: {fname} does not exist")

                extra_blacklist = [
                    r
                    for r in get_recursive_require_names(req_module, **kwargs)
                    if r not in libname_blacklist
                ]
                if extra_blacklist:
                    kwargs["log"](
                        "\nWarning: Preemptively skipping recursive dependency module%s: %s\n"
                        % (
                            ("" if len(extra_blacklist) == 1 else "s"),
                            ", ".join(extra_blacklist),
                        )
                    )
                libname_blacklist.extend(extra_blacklist)
                kwargs["inline_failure_libnames"].append(req_module)
                continue

        if check_should_break():
            break

    clear_libimport_cache(
        lib_of_filename(
            output_file_name,
            libnames=tuple(kwargs["libnames"]),
            non_recursive_libnames=tuple(kwargs["non_recursive_libnames"]),
        )
    )


def inline_all_requires(output_file_name, check_should_break, **kwargs):
    # so long as we keep changing, we will pull all the
    # requires to the top, then try to replace them in reverse
    # order.  As soon as we succeed, we reset the list
    last_output = get_file(output_file_name, **kwargs)
    clear_libimport_cache(lib_of_filename(output_file_name, **kwargs))
    cur_output_gen = make_cur_output_gen(output_file_name, **kwargs)
    cur_output = cur_output_gen(dict())
    # keep a list of libraries we've already tried to inline, and don't try them again
    libname_blacklist = []
    first_run = True
    while cur_output != last_output or first_run:
        first_run = False
        last_output = cur_output
        inline_one_require(
            output_file_name,
            libname_blacklist,
            cur_output,
            check_should_break,
            **kwargs,
        )
        cur_output = cur_output_gen(dict())


def main():
    try:
        args = process_logging_arguments(parser.parse_args())
    except argparse.ArgumentError as exc:
        if exc.message == "expected one argument":
            exc.reraise(
                '\nNote that argparse does not accept arguments with leading dashes.\nTry --foo=bar or --foo " -bar", if this was your intent.\nSee Python issue 9334.'
            )
        else:
            exc.reraise()

    def prepend_coqbin(prog):
        if isinstance(prog, str):
            prog = (prog,)
        if args.coqbin != "":
            return (os.path.join(args.coqbin, prog[0]), *prog[1:])
        else:
            return tuple(prog)

    args = adjust_no_error_defaults(args)
    bug_file_name = args.bug_file.name
    output_file_name = args.output_file
    env = {
        "fast_merge_imports": args.fast_merge_imports,
        "log": args.log,
        "coqc": prepend_coqbin(args.coqc or "coqc"),
        "coqtop": prepend_coqbin(args.coqtop or DEFAULT_COQTOP),
        "as_modules": args.wrap_modules,
        "max_consecutive_newlines": args.max_consecutive_newlines,
        "header": args.header,
        "dynamic_header": args.dynamic_header,
        "strip_trailing_space": args.strip_trailing_space,
        "timeout": (
            args.nonpassing_timeout if args.nonpassing_timeout != -1 else args.timeout
        ),
        "passing_timeout": (
            args.passing_timeout if args.passing_timeout != -1 else args.timeout
        ),
        "absolutize": args.absolutize,
        "minimize_before_inlining": args.minimize_before_inlining,
        "save_typeclasses": args.save_typeclasses,
        "admit_opaque": args.admit_opaque and args.admit_any,
        "admit_obligations": args.admit_obligations and args.admit_any,
        "aggressive": args.aggressive,
        "admit_transparent": args.admit_transparent and args.admit_any,
        "coqc_args": tuple(
            i.strip()
            for i in (
                list(process_maybe_list(args.nonpassing_coqc_args, log=args.log))
                + list(process_maybe_list(args.nonpassing_coq_args, log=args.log))
                + list(process_maybe_list(args.coq_args, log=args.log))
            )
        ),
        "coqtop_args": tuple(
            i.strip()
            for i in (
                list(process_maybe_list(args.nonpassing_coqtop_args, log=args.log))
                + list(process_maybe_list(args.coqtop_args, log=args.log))
                + list(process_maybe_list(args.nonpassing_coq_args, log=args.log))
                + list(process_maybe_list(args.coq_args, log=args.log))
            )
        ),
        "coq_makefile": prepend_coqbin(args.coq_makefile or "coq_makefile"),
        "coqdep": prepend_coqbin(args.coqdep),
        "passing_coqc_args": tuple(
            i.strip()
            for i in (
                list(process_maybe_list(args.passing_coqc_args, log=args.log))
                + list(process_maybe_list(args.passing_coq_args, log=args.log))
                + list(process_maybe_list(args.coq_args, log=args.log))
            )
        ),
        "passing_coqtop_args": tuple(
            i.strip()
            for i in (
                list(process_maybe_list(args.passing_coqtop_args, log=args.log))
                + list(process_maybe_list(args.coqtop_args, log=args.log))
                + list(process_maybe_list(args.passing_coq_args, log=args.log))
                + list(process_maybe_list(args.coq_args, log=args.log))
            )
        ),
        "passing_coqc": (
            prepend_coqbin(args.passing_coqc)
            if args.passing_coqc
            else (
                prepend_coqbin(args.coqc)
                if args.passing_coqc_args is not None
                else None
            )
        ),
        "passing_coqtop": (
            prepend_coqbin(args.passing_coqtop)
            if args.passing_coqtop
            else (
                prepend_coqbin(args.coqtop)
                if args.passing_coqtop_args is not None
                else None
            )
        ),
        "nonpassing_ocamlpath": (
            args.nonpassing_ocamlpath
            if args.nonpassing_ocamlpath is not None
            else args.ocamlpath
        ),
        "passing_ocamlpath": (
            args.passing_ocamlpath
            if args.passing_ocamlpath is not None
            else (
                args.ocamlpath
                if args.ocamlpath is not None
                and (args.passing_coqc != "" or args.passing_coqc_args is not None)
                else args.ocamlpath
            )
        ),
        "passing_base_dir": (
            os.path.abspath(args.passing_base_dir)
            if args.passing_base_dir != ""
            else None
        ),
        "base_dir": (os.path.abspath(args.base_dir) if args.base_dir != "" else None),
        "use_coq_makefile_for_deps": args.use_coq_makefile_for_deps,
        "walk_tree": args.walk_tree,
        "strict_whitespace": args.strict_whitespace,
        "temp_file_name": args.temp_file,
        "temp_file_log_name": args.temp_file_log,
        "coqc_is_coqtop": args.coqc_is_coqtop,
        "passing_coqc_is_coqtop": args.passing_coqc_is_coqtop,
        "coqpath_paths": [],
        "passing_coqpath_paths": [],
        "yes": args.yes,
        "color_on": args.color_on,
        "inline_failure_libnames": [],
        "parse_with": args.parse_with,
        "verbose_include_failure_warning": args.verbose_include_failure_warning,
        "extra_verbose_prefix": args.verbose_include_failure_warning_prefix,
        "extra_verbose_newline": args.verbose_include_failure_warning_newline,
        "cli_mapping": get_parser_name_mapping(parser),
        "should_succeed": args.should_succeed,
        "remove_modules": args.remove_modules,
        "remove_sections": args.remove_sections,
        "remove_comments": args.remove_comments,
        "normalize_requires": args.normalize_requires,
        "recursive_requires_explicit": args.recursive_requires_explicit,
        "split_requires": args.split_requires,
        "remove_hints": args.remove_hints,
        "remove_empty_sections": args.remove_empty_sections,
        "remove_abort": args.remove_abort,
        "remove_ltac": args.remove_ltac,
        "remove_section_variables": args.remove_section_variables,
        "prefer_inline_via_include": args.prefer_inline_via_include,
        "export_modules": args.export_modules,
        "split_imports": args.split_imports,
        "add_proof_using": args.add_proof_using,
        "add_proof_using_before_admit": args.add_proof_using_before_admit,
        "prefer_final_proof_using": args.prefer_final_proof_using,
        "remove_non_definitions": args.remove_non_definitions,
    }

    try:
        if bug_file_name[-2:] != ".v":
            env["log"](
                "\nError: BUGGY_FILE must end in .v (value: %s)" % bug_file_name,
                force_stdout=True,
                level=LOG_ALWAYS,
            )
            sys.exit(1)
        if output_file_name[-2:] != ".v":
            env["log"](
                "\nError: OUT_FILE must end in .v (value: %s)" % output_file_name,
                force_stdout=True,
                level=LOG_ALWAYS,
            )
            sys.exit(1)
        if os.path.exists(output_file_name):
            env["log"](
                "\nWarning: OUT_FILE (%s) already exists.  Would you like to overwrite?\n"
                % output_file_name,
                force_stdout=True,
                level=LOG_ALWAYS,
            )
            if not yes_no_prompt(yes=env["yes"]):
                sys.exit(1)
        for k, arg in (
            ("base_dir", "--base-dir"),
            ("passing_base_dir", "--passing-base-dir"),
        ):
            if env[k] is not None and not os.path.isdir(env[k]):
                env["log"](
                    "\nError: Argument to %s (%s) must exist and be a directory."
                    % (arg, env[k]),
                    force_stdout=True,
                    level=LOG_ALWAYS,
                )
                sys.exit(1)

        env["remove_temp_file"] = False
        if env["temp_file_name"] == "":
            temp_file = tempfile.NamedTemporaryFile(suffix=".v", dir=".", delete=False)
            env["temp_file_name"] = temp_file.name
            temp_file.close()
            env["remove_temp_file"] = True
        if env["temp_file_log_name"] == "":
            env["temp_file_log_name"] = env["temp_file_name"] + ".log"

        def make_make_coqc(coqc_prog, **kwargs):
            if get_coq_accepts_compile(coqc_prog):
                return (str(util.resource_path("coqtop-as-coqc.sh")), *coqc_prog)
            if "coqtop" in coqc_prog[0]:
                return (coqc_prog[0].replace("coqtop", "coqc"), *coqc_prog[1:])
            if coqc_prog[1] == "top":
                return (coqc_prog[0], "c", *coqc_prog[2:])
            return ("coqc",)

        if env["coqc_is_coqtop"]:
            if env["coqc"] == ("coqc",):
                env["coqc"] = env["coqtop"]
            env["make_coqc"] = make_make_coqc(env["coqc"], **env)
        if env["passing_coqc_is_coqtop"]:
            if env["passing_coqc"] == ("coqc",):
                if env["passing_coqtop"] is not None:
                    env["passing_coqc"] = env["passing_coqtop"]
                else:
                    env["passing_coqc"] = env["coqtop"]
            env["passing_make_coqc"] = make_make_coqc(env["passing_coqc"], **env)

        coqc_help = get_coqc_help(get_preferred_passing("coqc", **env), **env)
        coqc_version = get_coqc_version(env["coqc"], **env)

        update_env_with_libnames(
            env,
            args,
            include_passing=env["passing_coqc"],
            use_default=not has_dir_binding(
                env["coqc_args"], coqc_help=coqc_help, file_name=bug_file_name
            ),
            use_passing_default=not has_dir_binding(
                env["passing_coqc_args"], coqc_help=coqc_help, file_name=bug_file_name
            ),
        )

        if args.inline_user_contrib:
            # Build list of directories to skip based on command-line arguments
            skip_dirs = []
            if args.no_inline_stdlib:
                skip_dirs.append("Stdlib")
            if args.no_inline_corelib:
                skip_dirs.append("Corelib")

            for passing_prefix in ("", "passing_"):
                if env[passing_prefix + "coqc"]:
                    coq_user_contrib_path = os.path.join(
                        get_coqc_coqlib(
                            env[passing_prefix + "coqc"],
                            coq_args=env[passing_prefix + "coqc_args"],
                            **env,
                        ),
                        "user-contrib",
                    )
                    update_env_with_coqpath_folders(
                        passing_prefix,
                        env,
                        coq_user_contrib_path,
                        skip_dirs=skip_dirs,
                    )
                    env[passing_prefix + "coqpath_paths"].append(coq_user_contrib_path)

        if args.inline_coqlib or args.inline_stdlib:
            for passing_prefix in ("", "passing_"):
                if env[passing_prefix + "coqc"]:
                    coq_lib_path = get_coqc_coqlib(
                        env[passing_prefix + "coqc"],
                        coq_args=env[passing_prefix + "coqc_args"],
                        **env,
                    )
                    coq_theories_path = os.path.join(coq_lib_path, "theories")
                    coq_user_contrib_path = os.path.join(
                        os.path.join(coq_lib_path, "user-contrib"), "Stdlib"
                    )
                    coqpath_path = os.environ.get("COQPATH", "")
                    coqpath_paths = (
                        coqpath_path.split(os.pathsep) if coqpath_path else []
                    )
                    if args.inline_coqlib:
                        if coqc_version != "" and coqc_version[0] == "8":
                            env[passing_prefix + "libnames"] = tuple(
                                list(env[passing_prefix + "libnames"])
                                + [(coq_theories_path, "Coq")]
                            )
                        else:
                            env[passing_prefix + "libnames"] = tuple(
                                list(env[passing_prefix + "libnames"])
                                + [(coq_theories_path, "Corelib")]
                            )
                        env[passing_prefix + "libnames"] = tuple(
                            list(env[passing_prefix + "libnames"])
                            + [(coq_user_contrib_path, "Stdlib")]
                        )
                        for p in coqpath_paths:
                            env[passing_prefix + "libnames"] = tuple(
                                list(env[passing_prefix + "libnames"])
                                + [(os.path.join(p, "Stdlib"), "Coq")]
                            )
                    if args.inline_stdlib:
                        env[passing_prefix + "libnames"] = tuple(
                            list(env[passing_prefix + "libnames"])
                            + [(coq_theories_path, "Stdlib")]
                        )
                        env[passing_prefix + "libnames"] = tuple(
                            list(env[passing_prefix + "libnames"])
                            + [(coq_user_contrib_path, "Stdlib")]
                        )
                        for p in coqpath_paths:
                            env[passing_prefix + "libnames"] = tuple(
                                list(env[passing_prefix + "libnames"])
                                + [(os.path.join(p, "Stdlib"), "Stdlib")]
                            )
                    if args.inline_coqlib or args.inline_stdlib:
                        env[passing_prefix + "coqpath_paths"].append(coq_theories_path)
                        env[passing_prefix + "coqpath_paths"].append(
                            coq_user_contrib_path
                        )
                        env[passing_prefix + "coqpath_paths"].extend(coqpath_paths)

        env["log"]("{", level=2)
        for k, v in sorted(list(env.items())):
            env["log"]("  %s: %s" % (repr(k), repr(v)), level=2)
        env["log"]("}", level=2)

        for passing_prefix in ("", "passing_"):
            if env[passing_prefix + "coqc"]:
                args_key = passing_prefix + "coqc_args"
                if "-native-compiler" not in env[args_key]:
                    env[args_key] = tuple(
                        list(env[args_key])
                        + list(
                            get_coq_native_compiler_ondemand_fragment(
                                env[passing_prefix + "coqc"], **env
                            )
                        )
                    )

        if env["temp_file_name"][-2:] != ".v":
            env["log"](
                "\nError: TEMP_FILE must end in .v (value: %s)" % env["temp_file_name"],
                force_stdout=True,
                level=LOG_ALWAYS,
            )
            sys.exit(1)

        env["log"]("\nCoq version: %s\n" % coqc_version)

        extra_args = (
            get_coq_prog_args(get_file(bug_file_name, **env))
            if args.use_coq_prog_args
            else []
        )
        # persist topname so that when we get it from failing coqc, we can use it for passing coqc
        topname = None
        for args_name, coq_prog, passing_prefix in (
            ("coqc_args", env["coqc"], ""),
            ("coqtop_args", env["coqtop"], ""),
            (
                "passing_coqc_args",
                env["passing_coqc"] if env["passing_coqc"] else env["coqc"],
                "passing_",
            ),
            (
                "passing_coqtop_args",
                env["passing_coqtop"] if env["passing_coqtop"] else env["coqtop"],
                "passing_",
            ),
        ):
            env[args_name] = tuple(list(env[args_name]) + list(extra_args))
            for dirname, libname in env.get(passing_prefix + "libnames", []):
                env[args_name] = tuple(list(env[args_name]) + ["-R", dirname, libname])
            for dirname, libname in env.get(
                passing_prefix + "non_recursive_libnames", []
            ):
                env[args_name] = tuple(list(env[args_name]) + ["-Q", dirname, libname])
            for dirname in env.get(passing_prefix + "ocaml_dirnames", []):
                env[args_name] = tuple(list(env[args_name]) + ["-I", dirname])
            env[args_name], topname = deduplicate_trailing_dir_bindings_get_topname(
                env[args_name],
                coqc_help=coqc_help,
                file_name=bug_file_name,
                coq_accepts_top=get_coq_accepts_top(coq_prog),
                topname=topname,
            )
        for arg in group_coq_args(extra_args, coqc_help):
            for passing_prefix in ("passing_", ""):
                if arg[0] == "-R":
                    env.get(passing_prefix + "libnames", []).append((arg[1], arg[2]))
                if arg[0] == "-Q":
                    env.get(passing_prefix + "non_recursive_libnames", []).append(
                        (arg[1], arg[2])
                    )
                if arg[0] == "-I":
                    env.get(passing_prefix + "ocaml_dirnames", []).append(arg[1])

        for args_name, coqtop_prog, coqc_prog, passing_prefix in (
            ("coqtop_args", env["coqtop"], env["coqc"], ""),
            (
                "passing_coqtop_args",
                env["passing_coqtop"] if env["passing_coqtop"] else env["coqtop"],
                env["passing_coqc"] if env["passing_coqc"] else env["coqc"],
                "passing_",
            ),
        ):
            coqc_prog_help = get_coqc_help(coqc_prog, **env)
            coqtop_prog_help = get_coqc_help(coqtop_prog, **env)
            # we want to skip any arguments that are recognized by coqc but not coqtop
            recognized_args, unrecognized_args = group_coq_args_split_recognized(
                env[args_name], coqtop_prog_help
            )
            coqc_but_not_coqtop_args, unrecognized_args = (
                group_coq_args_split_recognized(unrecognized_args, coqc_prog_help)
            )
            if len(coqc_but_not_coqtop_args) > 0:
                env["log"](
                    "Warning: skipping arguments to coqtop that are only valid for coqc: %s"
                    % repr(coqc_but_not_coqtop_args),
                    level=2,
                )
            env[args_name] = tuple(
                [arg for group in recognized_args for arg in group] + unrecognized_args
            )

        if env["admit_transparent"] or env["admit_opaque"]:
            add_admit_tactic_wrapper = add_admit_tactic
        else:
            add_admit_tactic_wrapper = lambda x, **kwargs: x

        # if env["minimize_before_inlining"] and not env["inline_one_at_a_time"]:
        env["log"](
            "\nFirst, I will attempt to absolutize relevant [Require]s in %s, and store the result in %s..."
            % (bug_file_name, output_file_name)
        )
        inlined_contents = get_file(bug_file_name, update_globs=True, **env)
        args.bug_file.close()
        if args.inline_prelude:
            for key in (
                "coqc_args",
                "coqtop_args",
                "passing_coqc_args",
                "passing_coqtop_args",
            ):
                env[key] = tuple(list(env[key]) + ["-noinit"])
            inlined_contents = add_coqlib_prelude_import(inlined_contents, **env)
        write_to_file(output_file_name, inlined_contents)

        if not env["should_succeed"]:
            env["log"]("\nNow, I will attempt to coq the file, and find the error...")
            env["error_reg_string"] = get_error_reg_string(output_file_name, **env)

            if args.error_log:
                env["log"](
                    "\nNow, I will attempt to find the error message in the log..."
                )
                error_log = args.error_log.read()
                args.error_log.close()
                if not diagnose_error.has_error(error_log, env["error_reg_string"]):
                    env["log"](
                        "\nMoving %s to %s..."
                        % (output_file_name, env["temp_file_name"])
                    )
                    write_to_file(
                        env["temp_file_name"], read_from_file(output_file_name)
                    )
                    os.remove(output_file_name)
                    default_on_fatal(
                        "The computed error message was not present in the given error log.",
                        **env,
                    )

        if not env["minimize_before_inlining"]:
            env["log"](
                "Now, I will attempt to inline all of the inputs in %s, and store the result in %s..."
                % (bug_file_name, output_file_name)
            )
            inlined_contents = include_imports(output_file_name, **env)
            if inlined_contents:
                inlined_contents = add_admit_tactic_wrapper(inlined_contents, **env)
                env["log"]("Stripping trailing ends")
                while re.search(r"End [^ \.]*\.\s*$", inlined_contents):
                    inlined_contents = re.sub(
                        r"End [^ \.]*\.\s*$", "", inlined_contents
                    )
                if not check_change_and_write_to_file(
                    "",
                    inlined_contents,
                    output_file_name,
                    unchanged_message="Invalid empty file!",
                    success_message="Requires inlined.",
                    failure_description="inline all requires",
                    changed_description="File",
                    timeout_retry_count=SENSITIVE_TIMEOUT_RETRY_COUNT,
                    write_to_temp_file=True,
                    **env,
                ):
                    env["log"](
                        "Failed to inline requires all at once, trying one by one..."
                    )
                    inline_all_requires(
                        output_file_name,
                        (
                            lambda: minimize_file(
                                output_file_name,
                                return_after_requires=True,
                                die=(lambda *args, **kargs: False),
                                **env,
                            )
                        ),
                        **env,
                    )
            else:
                env["log"]("Failed to inline inputs.")
                sys.exit(1)

        # initial run before we (potentially) do fancy things with the requires
        minimize_file(output_file_name, **env)

        if env["minimize_before_inlining"]:
            # if we've not already inlined everything
            # so long as we keep changing, we will pull all the
            # requires to the top, then try to replace them in reverse
            # order.  As soon as we succeed, we reset the list
            inline_all_requires(
                output_file_name,
                (
                    lambda: minimize_file(
                        output_file_name, die=(lambda *args, **kargs: False), **env
                    )
                ),
                **env,
            )

            # and we make one final run, or, in case there are no requires, one run
            minimize_file(output_file_name, **env)

    except EOFError:
        env["log"](traceback.format_exc(), level=LOG_ALWAYS)
        raise
    except Exception:
        if hasattr(traceback, "TracebackException"):
            etype, value, tb = sys.exc_info()
            env["log"](
                "".join(
                    traceback.TracebackException(
                        type(value), value, tb, capture_locals=True
                    ).format()
                ),
                level=LOG_ALWAYS,
            )
        else:
            env["log"](traceback.format_exc(), level=LOG_ALWAYS)
        raise
    finally:
        if env.get("remove_temp_file"):
            clean_v_file(env["temp_file_name"])
            if os.path.exists(env["temp_file_log_name"]):
                os.remove(env["temp_file_log_name"])
            all_matching_files = {}
            for base_temp_file in (env["temp_file_name"], env["temp_file_log_name"]):
                temp_dir = os.path.dirname(base_temp_file)
                temp_name = os.path.basename(base_temp_file)
                if "." in temp_name:
                    base_name, ext = os.path.splitext(temp_name)
                    pattern = os.path.join(temp_dir, base_name + "*" + ext)
                else:
                    pattern = os.path.join(temp_dir, temp_name + "*")
                all_matching_files[base_temp_file] = glob.glob(pattern)
            for v_file in all_matching_files[env["temp_file_name"]]:
                clean_v_file(v_file)
            for log_file in all_matching_files[env["temp_file_log_name"]]:
                if os.path.exists(log_file):
                    os.remove(log_file)


if __name__ == "__main__":
    main()
