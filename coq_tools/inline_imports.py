#!/usr/bin/env python
import shutil, os, os.path, sys
from .argparse_compat import argparse
from .import_util import IMPORT_ABSOLUTIZE_TUPLE, ALL_ABSOLUTIZE_TUPLE
from .custom_arguments import add_libname_arguments, update_env_with_libnames, update_env_with_coqpath_folders, add_logging_arguments, process_logging_arguments
from .coq_version import get_coqc_coqlib, DEFAULT_COQTOP
from .replace_imports import include_imports

__all__ = ['main']

parser = argparse.ArgumentParser(description='Inline the imports of a file')
parser.add_argument('input_file', metavar='IN_FILE', type=argparse.FileType('r'),
                    help='a .v file to inline the imports of')
parser.add_argument('output_file', metavar='OUT_FILE', type=argparse.FileType('w'),
                    help='a .v file to write to')
parser.add_argument('--fast-merge-imports', dest='fast_merge_imports',
                    action='store_const', const=True, default=False,
                    help='Use a faster method for combining imports')
parser.add_argument('--no-deps', dest='use_coq_makefile_for_deps',
                    action='store_const', const=False, default=True,
                    help=("Don't do dependency analysis with coq_makefile."))
parser.add_argument('--no-pwd-deps', dest='walk_tree',
                    action='store_const', const=False, default=True,
                    help=("Don't add all files in the current directory to the dependency analysis."))
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
parser.add_argument('--inline-user-contrib', dest='inline_user_contrib',
                    action='store_const', const=True, default=False,
                    help=("Attempt to inline requires from the user-contrib folder"))
add_libname_arguments(parser)
add_logging_arguments(parser)

def main():
    args = process_logging_arguments(parser.parse_args())

    env = {
        'log': args.log,
        'coqc': (args.coqc if args.coqbin == '' else os.path.join(args.coqbin, args.coqc)),
        'absolutize': args.absolutize,
        'as_modules': args.wrap_modules,
        'fast': args.fast_merge_imports,
        'coq_makefile': args.coq_makefile,
        'use_coq_makefile_for_deps': args.use_coq_makefile_for_deps,
        'walk_tree': args.walk_tree,
        }
    update_env_with_libnames(env, args)
    if args.inline_user_contrib: update_env_with_coqpath_folders(env, os.path.join(get_coqc_coqlib(env['coqc'], coq_args=env['coqc_args'], **env), 'user-contrib'))

    filename = args.input_file.name
    args.input_file.close()

    rtn = include_imports(filename, **env)

    args.output_file.write(rtn)
    args.output_file.close()

if __name__ == '__main__':
    main()
