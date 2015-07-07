from __future__ import print_function
import sys
import argparse

__all__ = ["add_libname_arguments"]

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
        if values[0] != '.':
            print('ERROR: Only `-R . %s` is supported, not `-R %s %s`' % (values[1], values[0], values[1]), file=sys.stderr)
            sys.exit(0)
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
    parser.add_argument('-R', metavar=('DIR', 'COQDIR'), dest='libnames', type=str, default=[('.', 'Top')], nargs=2, action=CoqLibnameAction,
                        help='recursively map physical DIR to logical COQDIR, as in the -R argument to coqc')
