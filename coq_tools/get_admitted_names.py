#!/usr/bin/env python
import tempfile, os
from . import custom_arguments
from .argparse_compat import argparse
from .import_util import lib_of_filename
from .diagnose_error import get_coq_output
from .import_util import lib_of_filename, norm_libname
from .import_util import has_dir_binding, deduplicate_trailing_dir_bindings
from .coq_version import (
    get_coqc_version,
    get_coqc_help,
    get_coq_accepts_top,
    DEFAULT_COQTOP,
)
from .custom_arguments import (
    add_libname_arguments,
    update_env_with_libnames,
    add_logging_arguments,
    process_logging_arguments,
    get_parser_name_mapping,
    LOG_ALWAYS,
)
from .binding_util import process_maybe_list
from .file_util import clean_v_file
from . import util
from .util import PY3

if PY3:
    from .util import raw_input

__all__ = ["main"]

parser = custom_arguments.ArgumentParser(
    description="List all identifiers which are not closed under the global context"
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
    "--coqc", metavar="COQC", dest="coqc", type=str, default=None, action="append", help="The path to the coqc program."
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
    "--coqtop",
    metavar="COQTOP",
    dest="coqtop",
    type=str,
    default=None,
    action="append",
    help=("The path to the coqtop program (default: %s)." % DEFAULT_COQTOP),
)
add_libname_arguments(parser)
add_logging_arguments(parser)


def qualify_identifiers_helper(identifiers, keep_unfound=False, **kwargs):
    for ident in identifiers:
        found_file = False
        if "." in ident:
            parts = ident.split(".")
            for i in range(len(parts) - 1, 0, -1):
                if not found_file:
                    old_libname = ".".join(parts[:i])
                    new_libname = norm_libname(old_libname, **kwargs)
                    if old_libname != new_libname:
                        yield (ident, new_libname + "." + ".".join(parts[i:]))
                        found_file = True
        if keep_unfound and not found_file:
            yield (ident, ident)


def qualify_identifiers(identifiers, keep_unfound=False, **kwargs):
    for ident, new_ident in qualify_identifiers_helper(identifiers, keep_unfound=keep_unfound, **kwargs):
        yield new_ident


def filter_local_identifiers(identifiers, keep_unfound=False, **kwargs):
    for ident, new_ident in qualify_identifiers_helper(identifiers, keep_unfound=keep_unfound, **kwargs):
        yield ident


def get_constant_name_from_locate(val):
    val = val.strip()
    for ctype in ("Constant", "Constructor", "Inductive", ""):
        if val and val[: len(ctype)] == ctype:
            val = val[len(ctype) :].strip()
            if "\n" in val:
                val = val[: val.index("\n")].strip()
            return (val, ctype)


def fix_identifiers(idents, libname):
    for ident in idents:
        if ident[: len("Warning:")] == "Warning:":
            raw_input(ident)
            continue
        elif "." not in ident:
            yield ident
        else:
            idx = ident.index(".")
            overlap, rest = ident[:idx], ident[idx:]
            if libname[-(idx + 1) :] == "." + overlap:
                yield libname + rest
            else:
                # raw_input((ident, libname))
                # yield ident
                continue


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

    env = {
        "log": args.log,
        "coqc": prepend_coqbin(args.coqc or "coqc"),
        "coqtop": prepend_coqbin(args.coqtop or DEFAULT_COQTOP),
        "coqc_args": tuple(i.strip() for i in process_maybe_list(args.coq_args, log=args.log)),
        "coqc_is_coqtop": args.coqc_is_coqtop,
        "temp_file_name": "",
        "cli_mapping": get_parser_name_mapping(parser),
    }

    env["remove_temp_file"] = False
    if env["temp_file_name"] == "":
        temp_file = tempfile.NamedTemporaryFile(suffix=".v", dir=".", delete=False)
        env["temp_file_name"] = temp_file.name
        temp_file.close()
        env["remove_temp_file"] = True

    if env["coqc_is_coqtop"]:
        if env["coqc"] == ("coqc",):
            env["coqc"] = env["coqtop"]
        env["make_coqc"] = (util.resource_path("coqtop-as-coqc.sh"), *env["coqc"])

    coqc_help = get_coqc_help(env["coqc"], **env)
    coqc_version = get_coqc_version(env["coqc"], **env)

    if has_dir_binding(env["coqc_args"], coqc_help=coqc_help):
        update_env_with_libnames(env, args, default=tuple([]))
    else:
        update_env_with_libnames(env, args)

    for dirname, libname in env["libnames"]:
        env["coqc_args"] = tuple(list(env["coqc_args"]) + ["-R", dirname, libname])
    for dirname, libname in env["non_recursive_libnames"]:
        env["coqc_args"] = tuple(list(env["coqc_args"]) + ["-Q", dirname, libname])
    for dirname in env["ocaml_dirnames"]:
        env["coqc_args"] = tuple(list(env["coqc_args"]) + ["-I", dirname])
    env["coqc_args"] = deduplicate_trailing_dir_bindings(
        env["coqc_args"], coqc_help=coqc_help, coq_accepts_top=get_coq_accepts_top(env["coqc"])
    )

    try:
        env["log"]("Listing identifiers...")
        unknown = []
        closed_idents = []
        open_idents = []
        errors = []
        ignore_header = ("Welcome to Coq", "[Loading ML file")
        error_header = ("Toplevel input, characters",)
        for filename in sorted(env["_CoqProject_v_files"]):
            env["log"]("Qualifying identifiers in %s..." % filename, level=2)
            env["log"]("Printing assumptions in %s..." % filename, max_level=2)
            libname = lib_of_filename(filename, **env)
            require_statement = "Require %s.\n" % libname
            search_code = r"""%s
Set Search Output Name Only.
SearchPattern _ inside %s.""" % (
                require_statement,
                libname,
            )
            output, cmds, retcode, runtime = get_coq_output(
                env["coqc"], env["coqc_args"], search_code, 0, is_coqtop=env["coqc_is_coqtop"], verbose_base=3, **env
            )
            identifiers = sorted(fix_identifiers(set(i.strip() for i in output.split("\n") if i.strip()), libname))
            print_assumptions_code = require_statement + "\n".join(
                "Locate %s.\nPrint Assumptions %s." % (i, i) for i in identifiers
            )
            env["log"]("Printing assumptions...", level=2)
            output, cmds, retcode, runtime = get_coq_output(
                env["coqtop"],
                env["coqc_args"],
                print_assumptions_code,
                0,
                is_coqtop=True,
                pass_on_stdin=True,
                verbose_base=3,
                **env,
            )
            i = 0
            statements = output.split("\nCoq <")
            while i < len(statements):
                if i + 1 < len(statements) and " Closed under the global context " in statements[i + 1].replace(
                    "\n", " "
                ):
                    last, ctype = get_constant_name_from_locate(statements[i])
                    closed_idents.append((last, ctype))
                    env["log"]("Closed: %s (%s)" % (last, ctype), level=2)
                    i += 2
                elif i + 1 < len(statements) and "Axioms:" in statements[i + 1].replace("\n", " "):
                    last, ctype = get_constant_name_from_locate(statements[i])
                    open_idents.append((last, ctype, statements[i + 1]))
                    env["log"]("OPEN: %s (%s)" % (last, ctype))
                    env["log"](statements[i + 1], level=3)
                    i += 2
                elif not statements[i].strip():
                    i += 1
                else:
                    found_ignore, found_error = False, False
                    for header in ignore_header:
                        if statements[i].strip()[: len(header)] == header:
                            found_ignore = True
                            env["log"]("Ignoring: %s" % statements[i], level=3)
                    for header in ignore_header:
                        if statements[i].strip()[: len(header)] == header:
                            found_error = True
                    if not found_ignore:
                        if found_error:
                            errors.append(statements[i])
                            env["log"]("ERROR: %s" % statements[i])
                        else:
                            env["log"]("UNKNOWN: %s" % statements[i])
                            unknown.append(statements[i])
                    i += 1
        env["log"](
            "Identifiers which are not closed under the global context:\n%s"
            % "\n".join(ident[0] for ident in open_idents),
            level=LOG_ALWAYS,
        )
    finally:
        if env["remove_temp_file"]:
            clean_v_file(env["temp_file_name"])


if __name__ == "__main__":
    main()
