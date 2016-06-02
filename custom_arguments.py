from __future__ import print_function
import sys
import argparse

__all__ = ["add_libname_arguments", "ArgumentParser", "update_env_with_libnames"]

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

def update_env_with_libnames(env, args):
    env['libnames'] = (args.libnames if len(args.libnames + args.non_recursive_libnames) > 0 else [('.', 'Top')])
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
