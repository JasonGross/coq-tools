#!/usr/bin/env python
import argparse, shutil, os, os.path, sys
from import_util import get_file

SCRIPT_DIRECTORY = os.path.dirname(os.path.realpath(__file__))

parser = argparse.ArgumentParser(description='Absoluteize the imports of Coq files')
parser.add_argument('input_files', metavar='INFILE', nargs='+', type=argparse.FileType('r'),
                    help='.v files to update')
parser.add_argument('--in-place', '-i', metavar='SUFFIX', dest='suffix', nargs='?', type=str, default='',
                    help='update files in place (makes backup if SUFFIX supplied)')
parser.add_argument('--verbose', '-v', dest='verbose',
                    action='count',
                    help='display some extra information')
parser.add_argument('--quiet', '-q', dest='quiet',
                    action='count',
                    help='the inverse of --verbose')
parser.add_argument('--log-file', '-l', dest='log_files', nargs='*', type=argparse.FileType('w'),
                    default=[sys.stderr],
                    help='The files to log output to.  Use - for stdout.')
parser.add_argument('--coqc', metavar='COQC', dest='coqc', type=str, default='coqc',
                    help='The path to the coqc program.')
parser.add_argument('--topname', metavar='TOPNAME', dest='topname', type=str, default='Top',
                    help='The name to bind to the current directory using -R .')

DEFAULT_VERBOSITY=1

def make_logger(log_files):
    def log(text):
        for i in log_files:
            i.write(str(text) + '\n')
            i.flush()
            if i.fileno() > 1:
                os.fsync(i.fileno())
    return log

DEFAULT_LOG = make_logger([sys.stderr])

def backup(file_name, ext='.bak'):
    if not ext:
        raise ValueError
    if os.path.exists(file_name):
        backup(file_name + ext)
        os.rename(file_name, file_name + ext)

def write_to_file(file_name, contents, do_backup=False, ext='.bak'):
    if do_backup:
        backup(file_name, ext=ext)
    try:
        with open(file_name, 'w', encoding='UTF-8') as f:
            f.write(contents)
    except TypeError:
        with open(file_name, 'w') as f:
            f.write(contents)

def absolutize_imports(infile, **kwargs):
    filename = infile.name
    if kwargs['verbose']: kwargs['log']('Processing %s...' % filename)
    absolutized_contents = get_file(filename, absolutize_imports=True, update_globs=True, **kwargs)
    infile.close()
    if kwargs['inplace']:
        do_backup = kwargs['suffix'] is not None and len(kwargs['suffix']) > 0
        write_to_file(filename, absolutized_contents, do_backup=do_backup, ext=kwargs['suffix'])
    else:
        print(absolutized_contents)

if __name__ == '__main__':
    args = parser.parse_args()
    if args.verbose is None: args.verbose = DEFAULT_VERBOSITY
    if args.quiet is None: args.quiet = 0
    verbose = args.verbose - args.quiet
    log = make_logger(args.log_files)

    env = {
        'topname': args.topname,
        'verbose': verbose,
        'log': log,
        'coqc': args.coqc,
        'inplace': args.suffix != '', # it's None if they passed no argument, and '' if they didn't pass -i
        'suffix': args.suffix
        }

    for f in args.input_files:
        absolutize_imports(f, **env)
