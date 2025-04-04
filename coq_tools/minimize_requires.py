#!/usr/bin/env python3
import os, os.path, sys, re
from .argparse_compat import argparse
from .custom_arguments import (
    add_libname_arguments,
    update_env_with_libnames,
    add_logging_arguments,
    process_logging_arguments,
    get_parser_name_mapping,
    LOG_ALWAYS,
    DEFAULT_VERBOSITY,
)
from .split_file import UnsupportedCoqVersionError
from .import_util import (
    get_file_statements_insert_references,
    sort_files_by_dependency,
    classify_require_kind,
    EXPORT,
    REQUIRE_EXPORT,
)
from .file_util import write_to_file
from .memoize import memoize
from .minimizer_drivers import run_binary_search
from . import diagnose_error

__all__ = ["main"]

parser = argparse.ArgumentParser(description="Remove useless Requires in a file")
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
    "--all",
    dest="update_all",
    action="store_const",
    default=False,
    const=True,
    help=("also update all .v files listed in any _CoqProject file passed to -f (implies --in-place, requires -f)"),
)
parser.add_argument(
    "--absolutize",
    dest="absolutize",
    action="store_const",
    default=False,
    const=True,
    help=("Replace Requires with fully qualified versions."),
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
    "--no-keep-exports",
    dest="keep_exports",
    action="store_const",
    default=True,
    const=False,
    help=("Allow the removal of Require lines that have Export in them"),
)
parser.add_argument("--no-timeout", dest="timeout", action="store_const", const=0, help=("Do not use a timeout"))
parser.add_argument(
    "--keep-going",
    "-k",
    dest="keep_going",
    action="store_const",
    const=True,
    default=False,
    help=("Keep going when some files can't be minimized."),
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
add_libname_arguments(parser)
add_logging_arguments(parser)


def mark_exports(state, keep_exports):
    return tuple(
        (
            text_as_bytes,
            ranges,
            bool(keep_exports and ranges and classify_require_kind(text_as_bytes, ranges) in (EXPORT, REQUIRE_EXPORT)),
        )
        for text_as_bytes, ranges in state
    )


SKIP = "SKIP"
REMOVE = "REMOVE"


def trailing_whitespace(text):
    return "".join(sorted(re.search(r"(\s*)$", text, flags=re.DOTALL).groups()[0]))


def leading_whitespace(text):
    return "".join(sorted(re.search(r"^(\s*)", text, flags=re.DOTALL).groups()[0]))


def whitespace_to_key(ws):
    return (ws.count("\n"), ws.count("\t"), ws.count(" "), len(ws), ws)


def gobble_whitespace_text(before, after):
    before_ws, after_ws = trailing_whitespace(before), leading_whitespace(after)
    assert whitespace_to_key("") < whitespace_to_key(" ")  # sanity check
    if before_ws and after_ws:
        if whitespace_to_key(before_ws) < whitespace_to_key(after_ws):
            return (before[: -len(before_ws)], after)
        else:
            return (before, after[len(after_ws) :])
    elif before_ws:
        return (before[: -len(before_ws)], after)
    elif after_ws:
        return (before, after[len(after_ws) :])
    else:
        return (before, after)


def gobble_whitespace(before, after):
    assert before is bytes(before)
    assert after is bytes(after)
    before, after = gobble_whitespace_text(before.decode("utf-8"), after.decode("utf-8"))
    return (before.encode("utf-8"), after.encode("utf-8"))


def step_state(state, action):
    ret = []
    state = list(state)
    while len(state) > 0:
        (text_as_bytes, references, force_keep), state = state[0], state[1:]
        if references:
            (start, end, _loc, _append, _ty), new_references = references[0], tuple(references[1:])
            if action == SKIP or action is None:
                ret.append((text_as_bytes, new_references, force_keep))
            elif action == REMOVE and not force_keep:
                if new_references:  # still other imports, safe to just remove
                    pre_text_as_bytes, post_text_as_bytes = gobble_whitespace(
                        text_as_bytes[:start], text_as_bytes[end:]
                    )
                    ret.append((pre_text_as_bytes + post_text_as_bytes, new_references, force_keep))
                else:  # no other imports; remove this line completely
                    if ret and state:
                        prev_text_as_bytes, post_text_as_bytes = gobble_whitespace(ret[-1][0], state[0][0])
                        ret[-1] = (prev_text_as_bytes,) + ret[-1][1:]
                        state[0] = (post_text_as_bytes,) + state[0][1:]
                    elif ret:
                        ret[-1] = (ret[-1][0].rstrip(),) + ret[-1][1:]
                    elif state:
                        state[0] = (state[0][0].lstrip(),) + state[0][1:]
            else:
                raise ValueError
            ret.extend(state)
            return tuple(ret)
        else:
            ret.append((text_as_bytes, references, force_keep))
    return None


def state_to_contents(state):
    return "".join(reversed([v[0].decode("utf-8") for v in state]))


# the higher verbose_base, the less verbose we are, since we start at a higher level by default
def make_check_state(original_contents, verbose_base=4 - DEFAULT_VERBOSITY, **kwargs):
    # original_contents is str
    expected_output, orig_cmds, orig_retcode, runtime = diagnose_error.get_coq_output(
        kwargs["coqc"], kwargs["coqc_args"], original_contents, kwargs["timeout"], verbose_base=2, **kwargs
    )

    @memoize
    def check_contents(contents):
        output, cmds, retcode, runtime = diagnose_error.get_coq_output(
            kwargs["coqc"], kwargs["coqc_args"], contents, kwargs["timeout"], verbose_base=2, **kwargs
        )
        # TODO: Should we be checking the error message and the retcode and the output, or just the retcode?
        retval = diagnose_error.has_error(output) or output != expected_output or retcode != orig_retcode
        if retval:
            kwargs["log"](
                'Failed change.  Error when running "%s":\n%s' % ('" "'.join(cmds), output), level=verbose_base - 1
            )
        else:
            kwargs["log"]("Successful change", level=verbose_base)
            kwargs["log"]('New contents:\n"""\n%s\n"""' % contents, level=verbose_base + 1)
        return not retval

    def check_state(state):
        return check_contents(state_to_contents(state))

    return check_state


def make_save_state(filename, **kwargs):
    def save_state(state, final=False):
        contents = state_to_contents(state)
        if kwargs["inplace"]:
            do_backup = kwargs["suffix"] is not None and len(kwargs["suffix"]) > 0
            write_to_file(filename, contents, do_backup=do_backup, backup_ext=kwargs["suffix"])
        elif final:
            print(contents)

    return save_state


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
        "keep_exports": args.keep_exports,
        "keep_going": args.keep_going,
        "coqc": prepend_coqbin(args.coqc or "coqc"),
        "coqc_args": (args.coq_args if args.coq_args else tuple()),
        "timeout": args.timeout,
        "inplace": args.suffix != "",  # it's None if they passed no argument, and '' if they didn't pass -i
        "suffix": args.suffix,
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

    for dirname, libname in env["libnames"]:
        env["coqc_args"] = tuple(list(env["coqc_args"]) + ["-R", dirname, libname])
    for dirname, libname in env["non_recursive_libnames"]:
        env["coqc_args"] = tuple(list(env["coqc_args"]) + ["-Q", dirname, libname])
    for dirname in env["ocaml_dirnames"]:
        env["coqc_args"] = tuple(list(env["coqc_args"]) + ["-I", dirname])

    env["input_files"] = sort_files_by_dependency(env["input_files"], update_globs=True, **env)

    try:
        failed = []
        for name in env["input_files"]:
            try:
                annotated_contents = get_file_statements_insert_references(
                    name,
                    absolutize=(("lib",) if args.absolutize else tuple()),
                    update_globs=True,
                    types=("lib",),
                    appends=("<>",),
                    **env,
                )
                if annotated_contents is None:
                    env["log"]("ERROR: Failed to get references for %s" % name, level=LOG_ALWAYS)
                    failed.append((name, "failed to get references"))
                    if env["keep_going"]:
                        continue
                    else:
                        break
                annotated_contents = mark_exports(tuple(reversed(annotated_contents)), env["keep_exports"])
                save_state = make_save_state(name, **env)
                check_state = make_check_state(state_to_contents(annotated_contents), **env)
                verbose_check_state = make_check_state(
                    state_to_contents(annotated_contents), verbose_base=DEFAULT_VERBOSITY, **env
                )
                env["log"]("Running coq on initial contents...")
                if not verbose_check_state(annotated_contents):
                    env["log"]("ERROR: Failed to update %s" % name, level=LOG_ALWAYS)
                    failed.append((name, "failed to update"))
                    if env["keep_going"]:
                        continue
                    else:
                        break
                valid_actions = (REMOVE,)
                final_state = run_binary_search(annotated_contents, check_state, step_state, save_state, valid_actions)
                if final_state is not None:
                    if not check_state(final_state):
                        env["log"]("Internal error: Inconsistent final state on %s..." % name, level=LOG_ALWAYS)
                        failed.append((name, "inconsistent final state"))
                        if not env["keep_going"]:
                            break
                    else:
                        env["log"]("Saving final version of %s..." % name)
                        save_state(final_state, final=True)
            except KeyboardInterrupt:
                raise
            except SystemExit:
                raise
            except BaseException as e:
                if env["keep_going"]:
                    env["log"]("Failure on %s with error %s" % (name, repr(e)), level=LOG_ALWAYS)
                    failed.append((name, e))
                else:
                    raise e
        if failed:
            env["log"]("The following files failed:", level=LOG_ALWAYS)
            for name, e in failed:
                env["log"](name, level=LOG_ALWAYS)
            sys.exit(1)
    except UnsupportedCoqVersionError:
        env["log"]("ERROR: Your version of coqc (%s) does not support -time" % env["coqc"], level=LOG_ALWAYS)
        sys.exit(1)


if __name__ == "__main__":
    main()
