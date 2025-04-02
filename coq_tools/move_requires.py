#!/usr/bin/env python3
from __future__ import with_statement
import os, sys, re
from .argparse_compat import argparse
from .custom_arguments import get_parser_name_mapping

__all__ = ["main"]

parser = argparse.ArgumentParser(description="Move the [Require] statements up to the top of a file")
parser.add_argument("input_files", metavar="INFILE", nargs="+", type=str, help=".v files to update")
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
parser.add_argument("--verbose", "-v", dest="verbose", action="count", help="display some extra information")
parser.add_argument("--quiet", "-q", dest="quiet", action="count", help="the inverse of --verbose")
parser.add_argument(
    "--log-file",
    "-l",
    dest="log_files",
    nargs="*",
    type=argparse.FileType("w"),
    default=[sys.stderr],
    help="The files to log output to.  Use - for stdout.",
)

DEFAULT_VERBOSITY = 1


def make_logger(log_files):
    def log(text):
        for i in log_files:
            i.write(str(text) + "\n")
            i.flush()
            if i.fileno() > 2:  # stderr
                os.fsync(i.fileno())

    return log


DEFAULT_LOG = make_logger([sys.stderr])


def backup(file_name, ext=".bak"):
    if not ext:
        raise ValueError
    if os.path.exists(file_name):
        backup(file_name + ext)
        os.rename(file_name, file_name + ext)


def write_to_file(file_name, contents, do_backup=False, ext=".bak"):
    if do_backup:
        backup(file_name, ext=ext)
    try:
        with open(file_name, "w", encoding="UTF-8") as f:
            f.write(contents)
    except TypeError:
        with open(file_name, "w") as f:
            f.write(contents)


reg = re.compile(r"Require\s.*?\.\s+", re.MULTILINE | re.DOTALL)


def move_requires(filename, **kwargs):
    if kwargs["verbose"]:
        kwargs["log"]("Processing %s..." % filename)
    with open(filename, "r") as f:
        contents = f.read()
    requires = reg.findall(contents)
    if len(requires) == 0:
        if "Require" not in contents:
            return
        else:
            kwargs["log"]("Warning: Inconsistent [Require] in %s" % filename)
    header_end = contents.index(requires[0])
    header, rest = contents[:header_end], contents[header_end:]
    rest = reg.sub("", rest)
    new_contents = header + "\n".join(map(str.strip, requires)) + "\n\n" + rest
    if kwargs["inplace"]:
        do_backup = kwargs["suffix"] is not None and len(kwargs["suffix"]) > 0
        write_to_file(filename, new_contents, do_backup=do_backup, ext=kwargs["suffix"])
    else:
        print(new_contents)


def main():
    args = parser.parse_args()
    if args.verbose is None:
        args.verbose = DEFAULT_VERBOSITY
    if args.quiet is None:
        args.quiet = 0
    verbose = args.verbose - args.quiet
    log = make_logger(args.log_files)
    env = {
        "verbose": verbose,
        "log": log,
        "inplace": args.suffix != "",  # it's None if they passed no argument, and '' if they didn't pass -i
        "suffix": args.suffix,
        "cli_mapping": get_parser_name_mapping(parser),
    }

    for f in args.input_files:
        move_requires(f, **env)


if __name__ == "__main__":
    main()
