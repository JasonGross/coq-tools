#!/usr/bin/env python
import argparse, shutil, os, os.path, sys
from import_util import IMPORT_ABSOLUTIZE_TUPLE, ALL_ABSOLUTIZE_TUPLE
from custom_arguments import add_libname_arguments
from replace_imports import include_imports

# {Windows,Python,coqtop} is terrible; we fail to write to (or read
# from?) coqtop.  But we can wrap it in a batch scrip, and it works
# fine.
SCRIPT_DIRECTORY = os.path.dirname(os.path.realpath(__file__))
DEFAULT_COQTOP = 'coqtop' if os.name != 'nt' else os.path.join(SCRIPT_DIRECTORY, 'coqtop.bat')

parser = argparse.ArgumentParser(description='Inline the imports of a file')
parser.add_argument('input_file', metavar='IN_FILE', type=argparse.FileType('r'),
                    help='a .v file to inline the imports of')
parser.add_argument('output_file', metavar='OUT_FILE', type=argparse.FileType('w'),
                    help='a .v file to write to')
parser.add_argument('--verbose', '-v', dest='verbose',
                    action='count',
                    help='display some extra information')
parser.add_argument('--quiet', '-q', dest='quiet',
                    action='count',
                    help='the inverse of --verbose')
parser.add_argument('--fast-merge-imports', dest='fast_merge_imports',
                    action='store_const', const=True, default=False,
                    help='Use a faster method for combining imports')
parser.add_argument('--log-file', '-l', dest='log_files', nargs='*', type=argparse.FileType('w'),
                    default=[sys.stdout],
                    help='The files to log output to.  Use - for stdout.')
parser.add_argument('--no-deps', dest='walk_tree',
                    action='store_const', const=False, default=True,
                    help=("Don't do dependency analysis on all files in the current " +
                          "file tree."))
parser.add_argument('--no-wrap-modules', dest='wrap_modules',
                    action='store_const', const=False, default=True,
                    help=("Don't wrap imports in Modules.  By default, the " +
                          "contents of each file is wrapped in its own " +
                          "module to deal with renaming issues.  This " +
                          "can cause issues with subdirectories."))
parser.add_argument('--absolutize-constants', dest='absolutize',
                    action='store_const', default=IMPORT_ABSOLUTIZE_TUPLE, const=ALL_ABSOLUTIZE_TUPLE,
                    help=("Replace constants with fully qualified versions.  " +
                          "By default, all constants are not fully qualified.  If you have " +
                          "many overlapping file names in different directories " +
                          "and use partially qualified names that differ depending " +
                          "on which files have been Required, not absolutizing constants " +
                          "may cause name resolution to fail."))
parser.add_argument('--coqbin', metavar='COQBIN', dest='coqbin', type=str, default='',
                    help='The path to a folder containing the coqc and coqtop programs.')
parser.add_argument('--coqc', metavar='COQC', dest='coqc', type=str, default='coqc',
                    help='The path to the coqc program.')
parser.add_argument('--coqtop', metavar='COQTOP', dest='coqtop', type=str, default=DEFAULT_COQTOP,
                    help=('The path to the coqtop program (default: %s).' % DEFAULT_COQTOP))
parser.add_argument('--coqc-args', metavar='ARG', dest='coqc_args', type=str, nargs='?',
                    help='Arguments to pass to coqc; e.g., " -indices-matter" (leading and trailing spaces are stripped)')
parser.add_argument('--coqtop-args', metavar='ARG', dest='coqtop_args', type=str, nargs='?',
                    help='Arguments to pass to coqtop; e.g., " -indices-matter" (leading and trailing spaces are stripped)')
parser.add_argument('--coq_makefile', metavar='COQ_MAKEFILE', dest='coq_makefile', type=str, default='coq_makefile',
                    help='The path to the coq_makefile program.')
add_libname_arguments(parser)

def make_logger(log_files):
    def log(text):
        for i in log_files:
            i.write(str(text) + '\n')
            i.flush()
            if i.fileno() > 2: # stderr
                os.fsync(i.fileno())
    return log

DEFAULT_VERBOSITY=1

if __name__ == '__main__':
    args = parser.parse_args()
    if args.verbose is None: args.verbose = DEFAULT_VERBOSITY
    if args.quiet is None: args.quiet = 0
    verbose = args.verbose - args.quiet
    log = make_logger(args.log_files)

    env = {
        'libnames': args.libnames,
        'verbose': verbose,
        'log': log,
        'coqc': (args.coqc if args.coqbin == '' else os.path.join(args.coqbin, args.coqc)),
        'absolutize': args.absolutize,
        'as_modules': args.wrap_modules,
        'fast': args.fast_merge_imports,
        'coq_makefile': args.coq_makefile,
        'walk_tree': args.walk_tree
        }

    filename = args.input_file.name
    args.input_file.close()

    rtn = include_imports(filename, **env)

    args.output_file.write(rtn)
    args.output_file.close()
