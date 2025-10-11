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
    "DEFAULT_KIND_VERBOSITY",
    "KIND_INCLUDES",
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

# Default verbosity levels for logging kinds
# This maps kind names to the minimum verbosity level at which they should be logged
# This allows backwards compatibility with level-based logging
DEFAULT_KIND_VERBOSITY = {
    # Common logging kinds based on usage patterns in the codebase
    "error": 0,              # Always log errors
    "warning": 1,            # Log warnings at default verbosity
    "info": 1,               # Log info at default verbosity
    "debug": 2,              # Log debug info at verbosity 2
    "debug.detail": 3,       # Log detailed debug info at verbosity 3
    "debug.trace": 4,        # Log trace-level debug at verbosity 4
    "command": 2,            # Log commands being run at verbosity 2
    "contents": 2,           # Log file contents at verbosity 2
    "cache": 3,              # Log cache operations at verbosity 3
}

# Kind hierarchy/inclusion mapping
# This defines which kinds include other kinds
# If a file is tagged with kind k1, and kind_includes[k1][k2] is True,
# then logs with kind k2 will be written to that file
def make_kind_includes():
    from collections import defaultdict
    
    includes = {}
    
    # "all" includes everything
    includes["all"] = defaultdict(lambda: True)
    
    # You can add specific hierarchies here
    # Example: includes["debug"] = defaultdict(lambda: None, {"debug.trace": True, "debug.info": True})
    
    return includes

def check_kind_inclusion(configured_kind, log_kind):
    """
    Check if a configured kind includes a log kind.
    
    This handles:
    1. Exact matches
    2. Hierarchical matches (e.g., "debug" includes "debug.trace")
    3. Special cases defined in KIND_INCLUDES
    """
    # Exact match
    if configured_kind == log_kind:
        return True
    
    # Check if it's in the KIND_INCLUDES mapping
    if configured_kind in KIND_INCLUDES:
        return KIND_INCLUDES[configured_kind][log_kind]
    
    # Check for prefix-based hierarchy (e.g., "debug" includes "debug.trace")
    if log_kind.startswith(configured_kind + "."):
        return True
    
    return False

KIND_INCLUDES = make_kind_includes()


def make_logger(log_files, log_class_config=None):
    # log if level <= the level of the logger
    # log_class_config is a dict mapping file objects to dicts of {class_name: enabled/disabled}
    # where enabled=True, disabled=False, unset=None (fallback to verbosity)
    if log_class_config is None:
        log_class_config = {}
    
    def log(
        text,
        level=DEFAULT_VERBOSITY,
        max_level=None,
        force_stdout=False,
        force_stderr=False,
        end="\n",
        kind=None,
        kind_suffix=None,
    ):
        # Construct the full kind from kind and kind_suffix
        if kind is not None and kind_suffix is not None:
            full_kind = kind + "." + kind_suffix
        elif kind_suffix is not None:
            # If only suffix is provided, use it as the kind
            full_kind = kind_suffix
        else:
            full_kind = kind
        
        # Determine which files to write to
        selected_log_files = []
        for flevel, f in log_files:
            # LOG_ALWAYS overrides everything
            if level is LOG_ALWAYS:
                selected_log_files.append(f)
            # Check if this log should be written based on kind (class)
            elif full_kind is not None:
                # Get the class configuration for this file
                file_class_config = log_class_config.get(f, {})
                
                # Check if this kind is explicitly enabled/disabled
                class_setting = file_class_config.get(full_kind, None)
                
                if class_setting is True:
                    # Class is explicitly enabled for this file
                    selected_log_files.append(f)
                elif class_setting is False:
                    # Class is explicitly disabled for this file
                    continue
                else:
                    # Check if any configured kind includes this kind
                    should_log_via_hierarchy = False
                    for configured_kind, setting in file_class_config.items():
                        if setting is True:
                            # Check if this configured kind includes our log kind
                            if check_kind_inclusion(configured_kind, full_kind):
                                should_log_via_hierarchy = True
                                break
                        elif setting is False:
                            # Check if this configured kind includes our log kind for exclusion
                            if check_kind_inclusion(configured_kind, full_kind):
                                should_log_via_hierarchy = False
                                break
                    
                    if should_log_via_hierarchy:
                        selected_log_files.append(f)
                    else:
                        # Class is not configured, fall back to verbosity level
                        # Use the default verbosity for this kind if available
                        kind_level = DEFAULT_KIND_VERBOSITY.get(full_kind, level)
                        if kind_level <= flevel and (max_level is None or flevel < max_level):
                            selected_log_files.append(f)
            else:
                # No kind specified, use standard verbosity filtering
                if level <= flevel and (max_level is None or flevel < max_level):
                    selected_log_files.append(f)
        
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


def LogClassFileType(strings):
    """Parse log class file specification: classname,filename or classname for default files"""
    parts = strings.split(",", 1)
    if len(parts) == 1:
        # Just a class name, applies to default log files
        return (parts[0], None)
    else:
        # Class name and file
        class_name = parts[0]
        file_name = parts[1]
        if file_name == "-":
            file_obj = sys.stdout
        else:
            file_obj = argparse.FileType("w")(file_name)
        return (class_name, file_obj)


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
    parser.add_argument(
        "--log-class",
        dest="log_classes_enabled",
        action="append",
        type=LogClassFileType,
        default=[],
        help=(
            "Enable logging for specific classes. "
            "Each argument should be either 'classname' (applies to default log files) "
            "or 'classname,filename' (applies to specific file). "
            "Use - for stdout. "
            "When a class is enabled, logs with that kind will be written regardless of verbosity level."
        ),
    )
    parser.add_argument(
        "--disable-log-class",
        dest="log_classes_disabled",
        action="append",
        type=LogClassFileType,
        default=[],
        help=(
            "Disable logging for specific classes. "
            "Each argument should be either 'classname' (applies to default log files) "
            "or 'classname,filename' (applies to specific file). "
            "Use - for stdout. "
            "When a class is disabled, logs with that kind will not be written regardless of verbosity level."
        ),
    )


def process_logging_arguments(args):
    if args.verbose is None:
        args.verbose = DEFAULT_VERBOSITY
    if args.quiet is None:
        args.quiet = 0
    args.verbose -= args.quiet
    
    # Build the log files list
    log_files = [(args.verbose, f) for f in args.log_files] + args.verbose_log_files
    
    # Build the log class configuration
    # This is a dict mapping file objects to dicts of {class_name: True/False}
    log_class_config = {}
    
    # Get all unique file objects from log_files
    all_files = [f for _, f in log_files]
    
    # Process enabled log classes
    if hasattr(args, 'log_classes_enabled'):
        for class_name, file_obj in args.log_classes_enabled:
            if file_obj is None:
                # Apply to all default log files
                for f in args.log_files:
                    if f not in log_class_config:
                        log_class_config[f] = {}
                    log_class_config[f][class_name] = True
            else:
                # Apply to specific file
                if file_obj not in log_class_config:
                    log_class_config[file_obj] = {}
                log_class_config[file_obj][class_name] = True
                # Also add this file to log_files if not already there
                # Use verbosity 0 for class-specific files so only explicit classes go there
                if file_obj not in all_files:
                    log_files.append((0, file_obj))
    
    # Process disabled log classes
    if hasattr(args, 'log_classes_disabled'):
        for class_name, file_obj in args.log_classes_disabled:
            if file_obj is None:
                # Apply to all default log files
                for f in args.log_files:
                    if f not in log_class_config:
                        log_class_config[f] = {}
                    log_class_config[f][class_name] = False
            else:
                # Apply to specific file
                if file_obj not in log_class_config:
                    log_class_config[file_obj] = {}
                log_class_config[file_obj][class_name] = False
    
    args.log = make_logger(log_files, log_class_config=log_class_config)
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
        for d, name in env.get(passing_prefix + libnames_key, []):
            if os.path.isdir(d):
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
