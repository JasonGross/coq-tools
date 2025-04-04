#!/usr/bin/env python3
import os, os.path, sys
from .argparse_compat import argparse
from .import_util import get_file, sort_files_by_dependency, IMPORT_ABSOLUTIZE_TUPLE, ALL_ABSOLUTIZE_TUPLE
from .custom_arguments import (
    add_libname_arguments,
    update_env_with_libnames,
    add_logging_arguments,
    process_logging_arguments,
    get_parser_name_mapping,
)
from .file_util import write_to_file

__all__ = ["main"]

parser = argparse.ArgumentParser(description="Absolutize the imports of Coq files")
parser.add_argument("input_files", metavar="INFILE", nargs="*", type=argparse.FileType("r"), help=".v files to update")
parser.add_argument(
    "--in-place",
    "-i",
    metavar="SUFFIX",
    dest="suffix",
    nargs="?",
    type=str,
    default="",
    help="update files in place (makes backup if SUFFIX supplied)",
)
parser.add_argument(
    "--update-all",
    dest="update_all",
    action="store_const",
    default=False,
    const=True,
    help=("also update all .v files listed in any _CoqProject file passed to -f (implies --in-place, requires -f)"),
)
parser.add_argument(
    "--all",
    "-a",
    dest="absolutize",
    action="store_const",
    const=ALL_ABSOLUTIZE_TUPLE,
    default=IMPORT_ABSOLUTIZE_TUPLE,
    help="Absolutize all constants, and not just imports.",
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
    "--coq_makefile",
    metavar="COQ_MAKEFILE",
    dest="coq_makefile",
    type=str,
    default=None,
    action="append",
    help="The path to the coq_makefile program.",
)
add_libname_arguments(parser)
add_logging_arguments(parser)


def absolutize_imports(filename, **kwargs):
    kwargs["log"]("Processing %s..." % filename)
    absolutized_contents = get_file(filename, update_globs=True, **kwargs)
    if kwargs["inplace"]:
        do_backup = kwargs["suffix"] is not None and len(kwargs["suffix"]) > 0
        write_to_file(filename, absolutized_contents, do_backup=do_backup, backup_ext=kwargs["suffix"])
    else:
        print(absolutized_contents)


def main():
    args = process_logging_arguments(parser.parse_args())

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
        "inplace": args.suffix != "",  # it's None if they passed no argument, and '' if they didn't pass -i
        "suffix": args.suffix,
        "absolutize": args.absolutize,
        "coq_makefile": prepend_coqbin(args.coq_makefile or "coq_makefile"),
        "input_files": tuple(f.name for f in args.input_files),
        "cli_mapping": get_parser_name_mapping(parser),
    }
    update_env_with_libnames(env, args)

    for f in args.input_files:
        f.close()

    if args.update_all:
        if env["_CoqProject"] is None:
            parser.error("--update-all given without -f")
            sys.exit(1)
        else:
            env["inplace"] = True
            if env["suffix"] == "":
                env["suffix"] = None
            env["input_files"] = tuple(list(env["input_files"]) + list(env["_CoqProject_v_files"]))
        if len(env["input_files"]) == 0:
            parser.error("no .v files listed in %s" % args.CoqProjectFile)
    elif len(env["input_files"]) == 0:
        parser.error("not enough arguments (-f COQPROJECTFILE with .v files is required if no .v files are given)")

    env["input_files"] = sort_files_by_dependency(env["input_files"], update_globs=True, **env)

    for f in env["input_files"]:
        absolutize_imports(f, **env)


if __name__ == "__main__":
    main()
