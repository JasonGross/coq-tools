#!/usr/bin/env python
import argparse, shutil, os, os.path, sys
from import_util import get_file, IMPORT_ABSOLUTIZE_TUPLE, ALL_ABSOLUTIZE_TUPLE
from custom_arguments import add_libname_arguments, add_logging_arguments, process_logging_arguments
from file_util import write_to_file

SCRIPT_DIRECTORY = os.path.dirname(os.path.realpath(__file__))

parser = argparse.ArgumentParser(description='Absolutize the imports of Coq files')
parser.add_argument('input_files', metavar='INFILE', nargs='+', type=argparse.FileType('r'),
                    help='.v files to update')
parser.add_argument('--in-place', '-i', metavar='SUFFIX', dest='suffix', nargs='?', type=str, default='',
                    help='update files in place (makes backup if SUFFIX supplied)')
parser.add_argument('--all', '-a', dest='absolutize', action='store_const',
                    const=ALL_ABSOLUTIZE_TUPLE, default=IMPORT_ABSOLUTIZE_TUPLE,
                    help='Absolutize all constants, and not just imports.')
parser.add_argument('--coqbin', metavar='COQBIN', dest='coqbin', type=str, default='',
                    help='The path to a folder containing the coqc and coqtop programs.')
parser.add_argument('--coqc', metavar='COQC', dest='coqc', type=str, default='coqc',
                    help='The path to the coqc program.')
parser.add_argument('--coq_makefile', metavar='COQ_MAKEFILE', dest='coq_makefile', type=str, default='coq_makefile',
                    help='The path to the coq_makefile program.')
add_libname_arguments(parser)
add_logging_arguments(parser)


def absolutize_imports(infile, **kwargs):
    filename = infile.name
    if kwargs['verbose']: kwargs['log']('Processing %s...' % filename)
    absolutized_contents = get_file(filename, update_globs=True, **kwargs)
    infile.close()
    if kwargs['inplace']:
        do_backup = kwargs['suffix'] is not None and len(kwargs['suffix']) > 0
        write_to_file(filename, absolutized_contents, do_backup=do_backup, ext=kwargs['suffix'])
    else:
        print(absolutized_contents)

if __name__ == '__main__':
    args = process_logging_arguments(parser.parse_args())
    def prepend_coqbin(prog):
        if args.coqbin != '':
            return os.path.join(args.coqbin, prog)
        else:
            return prog
    env = {
        'libnames': args.libnames,
        'verbose': args.verbose,
        'log': args.log,
        'coqc': prepend_coqbin(args.coqc),
        'inplace': args.suffix != '', # it's None if they passed no argument, and '' if they didn't pass -i
        'suffix': args.suffix,
        'absolutize': args.absolutize,
        'coq_makefile': prepend_coqbin(args.coq_makefile)
        }

    for f in args.input_files:
        absolutize_imports(f, **env)
