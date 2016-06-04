from __future__ import print_function
import sys, os
import argparse

__all__ = ["add_libname_arguments", "ArgumentParser", "update_env_with_libnames", "add_logging_arguments", "process_logging_arguments", "DEFAULT_LOG", "DEFAULT_VERBOSITY"]

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

DEFAULT_VERBOSITY=1

def make_logger(log_files):
    def log(text):
        for i in log_files:
            i.write(str(text) + '\n')
            i.flush()
            if i.fileno() > 2: # stderr
                os.fsync(i.fileno())
    return log

DEFAULT_LOG = make_logger([sys.stderr])

class DeprecatedAction(argparse.Action):
    def __init__(self, replacement=None, *args, **kwargs):
        if replacement is None:
            raise ValueError("replacement must not be None")
        super(DeprecatedAction, self).__init__(*args, **kwargs)
        self.replacement = replacement
    def __call__(self, parser, namespace, values, option_string=None):
        print('ERROR: option %s is deprecated.  Use %s instead.' % (option_string, self.replacement), file=sys.stderr)
        sys.exit(0)

def add_libname_arguments(parser):
    parser.add_argument('--topname', metavar='TOPNAME', dest='topname', type=str, default='Top', action=DeprecatedAction, replacement='-R',
                        help='The name to bind to the current directory using -R .')
    parser.add_argument('-R', metavar=('DIR', 'COQDIR'), dest='libnames', type=str, default=[], nargs=2, action=CoqLibnameAction,
                        help='recursively map physical DIR to logical COQDIR, as in the -R argument to coqc')
    parser.add_argument('-Q', metavar=('DIR', 'COQDIR'), dest='non_recursive_libnames', type=str, default=[], nargs=2, action=CoqLibnameAction,
                        help='(nonrecursively) map physical DIR to logical COQDIR, as in the -Q argument to coqc')

def add_logging_arguments(parser):
    parser.add_argument('--verbose', '-v', dest='verbose',
                        action='count',
                        help='display some extra information')
    parser.add_argument('--quiet', '-q', dest='quiet',
                        action='count',
                        help='the inverse of --verbose')
    parser.add_argument('--log-file', '-l', dest='log_files', nargs='*', type=argparse.FileType('w'),
                        default=[sys.stderr],
                        help='The files to log output to.  Use - for stdout.')

def process_logging_arguments(args):
    if args.verbose is None: args.verbose = DEFAULT_VERBOSITY
    if args.quiet is None: args.quiet = 0
    args.log = make_logger(args.log_files)
    args.verbose -= args.quiet
    del args.quiet
    return args

def update_env_with_libnames(env, args, default=(('.', 'Top'), )):
    env['libnames'] = (args.libnames if len(args.libnames + args.non_recursive_libnames) > 0 else list(default))
    env['non_recursive_libnames'] = args.non_recursive_libnames

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
            if '/'.join(action.option_strings) == name:
                return action
            elif action.metavar == name:
                return action
            elif action.dest == name:
                return action

    def error(self, message):
        def reraise(extra=''):
            super(ArgumentParser, self).error(message + extra)
        exc = sys.exc_info()[1]
        if exc:
            exc.argument = self._get_action_from_name(exc.argument_name)
            exc.reraise = reraise
            raise exc
        reraise()
