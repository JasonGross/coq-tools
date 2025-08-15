from __future__ import print_function
import sys, os
from .argparse_compat import argparse
from .util import PY3

__all__ = [
    "add_libname_arguments",
    "add_passing_libname_arguments",
    "ArgumentParser",
    "update_env_with_libnames",
    "add_logging_arguments",
    "process_logging_arguments",
    "update_env_with_coqpath_folders",
    "DEFAULT_LOG",
    "DEFAULT_VERBOSITY",
    "LOG_ALWAYS",
    "get_parser_name_mapping",
]


# grumble, grumble, we want to support multiple -R arguments like coqc
class CoqLibnameAction(argparse.Action):
    non_default = False

    #     def __init__(self, *args, **kwargs):
    #         super(CoqLibnameAction, self).__init__(*args, **kwargs)
    def __call__(self, parser, namespace, values, option_string=None):
        #        print('%r %r %r' % (namespace, values, option_string))
        if not self.non_default:
            setattr(namespace, self.dest, [])
            self.non_default = True
        getattr(namespace, self.dest).append(tuple(values))


DEFAULT_VERBOSITY = 1
LOG_ALWAYS = None


def make_logger(log_files):
    # log if level <= the level of the logger
    def log(
        text,
        level=DEFAULT_VERBOSITY,
        max_level=None,
        force_stdout=False,
        force_stderr=False,
        end="\n",
    ):
        selected_log_files = [
            f
            for flevel, f in log_files
            if level is LOG_ALWAYS
            or (level <= flevel and (max_level is None or flevel < max_level))
        ]
        for i in selected_log_files:
            if force_stderr and i.fileno() == 1 and not force_stdout:
                continue  # skip stdout if we write to stderr
            if force_stdout and i.fileno() == 2 and not force_stderr:
                continue  # skip stderr if we write to stdout
            i.write(str(text) + end)
            i.flush()
            if i.fileno() > 2:  # stderr
                os.fsync(i.fileno())
        for force, fno, sys_file in (
            (force_stdout, 1, sys.stdout),
            (force_stderr, 2, sys.stderr),
        ):
            if force and not any(
                i.fileno() == fno for i in selected_log_files
            ):  # not already writing to std{out,err}
                if PY3:
                    sys_file.buffer.write(text.encode("utf-8"))
                    sys_file.buffer.write(end.encode("utf-8"))
                    sys_file.flush()
                else:
                    print(text, end=end, file=sys_file)

    return log


DEFAULT_LOG = make_logger([(DEFAULT_VERBOSITY, sys.stderr)])


class DeprecatedAction(argparse.Action):
    def __init__(self, replacement=None, *args, **kwargs):
        if replacement is None:
            raise ValueError("replacement must not be None")
        super(DeprecatedAction, self).__init__(*args, **kwargs)
        self.replacement = replacement

    def __call__(self, parser, namespace, values, option_string=None):
        print(
            "ERROR: option %s is deprecated.  Use %s instead."
            % (option_string, self.replacement),
            file=sys.stderr,
        )
        sys.exit(0)


class ArgAppendWithWarningAction(argparse.Action):
    def __call__(self, parser, namespace, value, option_string=None):
        items = getattr(namespace, self.dest) or []
        items.append(value)
        setattr(namespace, self.dest, items)
        if value.startswith("-w "):
            print(
                (
                    'WARNING: You seem to be trying to pass a warning list to Coq via a single %s ("%s").'
                    + "\n  I will continue anyway, but this will most likely not work."
                    + "\n  Instead try using multiple invocations, as in"
                    + "\n    %s"
                )
                % (
                    option_string,
                    value,
                    " ".join(option_string + "=" + v for v in value.split(" ")),
                ),
                file=sys.stderr,
            )


def add_libname_arguments_gen(parser, passing):
    passing_dash = passing + "-" if passing else ""
    twodash_passing_dash = "--" + passing_dash
    onedash_passing_dash = "-" + ("-" + passing + "-" if passing else "")
    passing_underscore = passing + "_" if passing else ""
    passing_for = ", for --" + passing + "coqc" if passing else ""
    parser.add_argument(
        twodash_passing_dash + "topname",
        metavar="TOPNAME",
        dest=passing_underscore + "topname",
        type=str,
        default="Top",
        action=DeprecatedAction,
        replacement="-R",
        help="The name to bind to the current directory using -R .",
    )
    parser.add_argument(
        onedash_passing_dash + "R",
        metavar=("DIR", "COQDIR"),
        dest=passing_underscore + "libnames",
        type=str,
        default=[],
        nargs=2,
        action=CoqLibnameAction,
        help="recursively map physical DIR to logical COQDIR, as in the -R argument to coqc"
        + passing_for,
    )
    parser.add_argument(
        onedash_passing_dash + "Q",
        metavar=("DIR", "COQDIR"),
        dest=passing_underscore + "non_recursive_libnames",
        type=str,
        default=[],
        nargs=2,
        action=CoqLibnameAction,
        help="(nonrecursively) map physical DIR to logical COQDIR, as in the -Q argument to coqc"
        + passing_for,
    )
    parser.add_argument(
        onedash_passing_dash + "I",
        metavar="DIR",
        dest=passing_underscore + "ocaml_dirnames",
        type=str,
        default=[],
        action="append",
        help="Look for ML files in DIR, as in the -I argument to coqc" + passing_for,
    )
    parser.add_argument(
        twodash_passing_dash + "arg",
        metavar="ARG",
        dest=passing_underscore + "coq_args",
        type=str,
        action=ArgAppendWithWarningAction,
        help='Arguments to pass to coqc and coqtop; e.g., " -indices-matter" (leading and trailing spaces are stripped)'
        + passing_for,
    )
    parser.add_argument(
        onedash_passing_dash + "f",
        metavar="FILE",
        dest=passing_underscore + "CoqProjectFile",
        nargs=1,
        type=argparse.FileType("r"),
        default=None,
        help=("A _CoqProject file" + passing_for),
    )


def add_libname_arguments(parser):
    add_libname_arguments_gen(parser, passing="")


def add_passing_libname_arguments(parser):
    add_libname_arguments_gen(parser, "passing")
    add_libname_arguments_gen(parser, "nonpassing")


def TupleType(*types):
    def call(strings):
        vals = strings.split(",")
        if len(vals) != len(types):
            raise ValueError(
                "Got %d arguments, expected %d arguments" % (len(vals), len(types))
            )
        return tuple(ty(val) for ty, val in zip(types, vals))

    return call


def add_logging_arguments(parser):
    parser.add_argument(
        "--verbose",
        "-v",
        dest="verbose",
        action="count",
        help="display some extra information by default (does not impact --verbose-log-file)",
    )
    parser.add_argument(
        "--quiet", "-q", dest="quiet", action="count", help="the inverse of --verbose"
    )
    parser.add_argument(
        "--log-file",
        "-l",
        dest="log_files",
        nargs="+",
        type=argparse.FileType("w"),
        default=[sys.stderr],
        help="The files to log output to.  Use - for stdout.",
    )
    parser.add_argument(
        "--verbose-log-file",
        dest="verbose_log_files",
        nargs="+",
        type=TupleType(int, argparse.FileType("w")),
        default=[],
        help=(
            (
                "The files to log output to at verbosity other than the default verbosity (%d if no -v/-q arguments are passed); "
                + "each argument should be a pair of a verbosity level and a file name. "
                "Use - for stdout."
            )
            % DEFAULT_VERBOSITY
        ),
    )


def process_logging_arguments(args):
    if args.verbose is None:
        args.verbose = DEFAULT_VERBOSITY
    if args.quiet is None:
        args.quiet = 0
    args.verbose -= args.quiet
    args.log = make_logger(
        [(args.verbose, f) for f in args.log_files] + args.verbose_log_files
    )
    del args.quiet
    del args.verbose
    return args


def tokenize_CoqProject(contents):
    is_in_string = False
    is_in_comment = False
    cur = ""
    for ch in contents:
        if is_in_string:
            cur += ch
            if ch == '"':
                yield cur
                cur = ""
                is_in_string = False
        elif is_in_comment:
            if ch in "\n\r":
                is_in_comment = False
        elif ch == '"':
            cur += ch
            is_in_string = True
        elif ch == "#":
            if cur:
                yield cur
            cur = ""
            is_in_comment = True
        else:
            if ch in "\n\r\t ":
                if cur:
                    yield cur
                cur = ""
            else:
                cur += ch
    if cur:
        yield cur


def argstring_to_iterable(arg):
    if arg[:1] == '"' and arg[-1:] == '"':
        arg = arg[1:-1]
    return arg.split(" ")


def append_coq_arg(env, arg, passing=""):
    for key in ("coqc_args", "coqtop_args"):
        env[passing + key] = tuple(
            list(env.get(passing + key, [])) + list(argstring_to_iterable(arg))
        )


def process_CoqProject(env, contents, passing=""):
    if contents is None:
        return
    tokens = tuple(tokenize_CoqProject(contents))
    i = 0
    while i < len(tokens):
        if tokens[i] == "-R" and i + 2 < len(tokens):
            env[passing + "libnames"].append((tokens[i + 1], tokens[i + 2]))
            i += 3
        elif tokens[i] == "-Q" and i + 2 < len(tokens):
            env[passing + "non_recursive_libnames"].append(
                (tokens[i + 1], tokens[i + 2])
            )
            i += 3
        elif tokens[i] == "-I" and i + 1 < len(tokens):
            env[passing + "ocaml_dirnames"].append(tokens[i + 1])
            i += 2
        elif tokens[i] == "-arg" and i + 1 < len(tokens):
            append_coq_arg(env, tokens[i + 1], passing=passing)
            i += 2
        elif tokens[i][-2:] == ".v":
            env[passing + "_CoqProject_v_files"].append(tokens[i])
            i += 1
        elif any(
            tokens[i][-len(ext) :] == ext
            for ext in (".mli", ".ml", ".mlg", ".mllib", ".ml4")
        ):
            i += 1
        else:
            if "log" in env.keys():
                env["log"]("Unknown _CoqProject entry: %s" % repr(tokens[i]))
            env[passing + "_CoqProject_unknown"].append(tokens[i])
            i += 1


def update_env_with_libname_default(env, args, default=((".", "Top"),), passing=""):
    if (
        len(
            getattr(args, passing + "libnames")
            + getattr(args, passing + "non_recursive_libnames")
            + env[passing + "libnames"]
            + env[passing + "non_recursive_libnames"]
        )
        == 0
    ):
        env[passing + "libnames"].extend(list(default))


def update_env_with_libnames(
    env,
    args,
    default=((".", "Top"),),
    include_passing=False,
    use_default=True,
    use_passing_default=True,
):
    all_keys = (
        "libnames",
        "non_recursive_libnames",
        "ocaml_dirnames",
        "_CoqProject",
        "_CoqProject_v_files",
        "_CoqProject_unknown",
    )
    passing_opts = ("",) if not include_passing else ("", "passing_", "nonpassing_")
    for passing in passing_opts:
        for key in all_keys:
            env[passing + key] = []
        if getattr(args, passing + "CoqProjectFile"):
            for f in getattr(args, passing + "CoqProjectFile"):
                env[passing + "_CoqProject"] = f.read()
                f.close()
        process_CoqProject(env, env[passing + "_CoqProject"], passing=passing)
        env[passing + "libnames"].extend(getattr(args, passing + "libnames"))
        env[passing + "non_recursive_libnames"].extend(
            getattr(args, passing + "non_recursive_libnames")
        )
        env[passing + "ocaml_dirnames"].extend(
            getattr(args, passing + "ocaml_dirnames")
        )
    if include_passing:
        # The nonpassing_ prefix is actually temporary; the semantics
        # are that, e.g., libnames = libnames + nonpassing_libnames,
        # while passing_libnames = libnames + passing_libnames
        for key in all_keys:
            env["passing_" + key] = env[key] + env["passing_" + key]
            env[key] = env[key] + env["nonpassing_" + key]
            del env["nonpassing_" + key]
    if use_default:
        update_env_with_libname_default(env, args, default=default)
    if use_passing_default and include_passing:
        update_env_with_libname_default(env, args, default=default, passing="passing_")


def update_env_with_coqpath_folders(passing_prefix, env, *coqpaths, skip_dirs=None):
    if skip_dirs is None:
        skip_dirs = []

    existing_names = set()
    for libnames_key in ["libnames", "non_recursive_libnames"]:
        for _, name in env.get(passing_prefix + libnames_key, []):
            existing_names.add(name)

    def do_with_path(path):
        env.get(passing_prefix + "non_recursive_libnames", []).extend(
            (os.path.join(path, d), d)
            for d in sorted(os.listdir(path))
            if d not in skip_dirs and d not in existing_names
        )

    for coqpath in coqpaths:
        if os.path.isdir(coqpath):
            do_with_path(coqpath)
        elif ";" in coqpath:
            for path in coqpath.split(";"):
                do_with_path(path if path != "" else ".")
        elif ":" in coqpath:
            for path in coqpath.split(":"):
                do_with_path(path if path != "" else ".")


# http://stackoverflow.com/questions/5943249/python-argparse-and-controlling-overriding-the-exit-status-code
class ArgumentParser(argparse.ArgumentParser):
    def _get_action_from_name(self, name):
        """Given a name, get the Action instance registered with this parser.
        If only it were made available in the ArgumentError object. It is
        passed as it's first arg...
        """
        container = self._actions
        if name is None:
            return None
        for action in container:
            if "/".join(action.option_strings) == name:
                return action
            elif action.metavar == name:
                return action
            elif action.dest == name:
                return action

    def error(self, message):
        def reraise(extra=""):
            super(ArgumentParser, self).error(message + extra)

        exc = sys.exc_info()[1]
        if exc:
            exc.argument = self._get_action_from_name(exc.argument_name)
            exc.reraise = reraise
            raise exc
        reraise()


# returns a mapping from constant names to values to lists of command-line flags
def get_parser_name_mapping(parser):
    mapping = {}
    for action in parser._actions:
        if (
            hasattr(action, "const")
            and action.const is not None
            and len(action.option_strings) > 0
        ):
            dest = action.dest
            const = action.const
            if dest not in mapping:
                mapping[dest] = {}
            if const not in mapping[dest]:
                mapping[dest][const] = []
            mapping[dest][const] += action.option_strings
    return mapping
