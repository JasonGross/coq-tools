#!/usr/bin/env python
from __future__ import with_statement
import os, sys, re, argparse
from custom_arguments import add_libname_arguments

parser = argparse.ArgumentParser(description='Implement the suggestions of [Set Suggest Proof Using.]')
parser.add_argument('--verbose', '-v', dest='verbose',
                    action='count',
                    help='display some extra information')
parser.add_argument('--quiet', '-q', dest='quiet',
                    action='count',
                    help='the inverse of --verbose')
parser.add_argument('source', metavar='SOURCE_FILE', type=argparse.FileType('r'), nargs='?', default=sys.stdin,
                    help='the source of set suggest proof using messages; use - for stdin.')
parser.add_argument('--log-file', '-l', dest='log_files', nargs='*', type=argparse.FileType('w'),
                    default=[sys.stdout],
                    help='The files to log output to.  Use - for stdout.')
add_libname_arguments(parser)

def DEFAULT_LOG(text):
    print(text)

DEFAULT_VERBOSITY=1

def make_logger(log_files):
    def log(text):
        for i in log_files:
            i.write(str(text) + '\n')
            i.flush()
            if i.fileno() > 2: # stderr
                os.fsync(i.fileno())
    return log

def backup(file_name, ext='.bak'):
    if not ext:
        raise ValueError
    if os.path.exists(file_name):
        backup(file_name + ext)
        os.rename(file_name, file_name + ext)

FILE_CACHE = {}

def write_to_file(file_name, contents, do_backup=False):
    backed_up = False
    while not backed_up:
        try:
            if do_backup:
                backup(file_name)
            backed_up = True
        except IOError as e:
            print('Warning: f.write(%s) failed with %s\nTrying again in 10s' % (file_name, repr(e)))
            time.sleep(10)
    written = False
    while not written:
        try:
            try:
                with open(file_name, 'w', encoding='UTF-8') as f:
                    f.write(contents)
            except TypeError:
                with open(file_name, 'w') as f:
                    f.write(contents)
            written = True
            FILE_CACHE[file_name] = (os.stat(file_name).st_mtime, contents)
        except IOError as e:
            print('Warning: f.write(%s) failed with %s\nTrying again in 10s' % (file_name, repr(e)))
            time.sleep(10)

def read_from_file(file_name):
    if file_name in FILE_CACHE.keys() and os.stat(file_name).st_mtime == FILE_CACHE[file_name][0]:
        return FILE_CACHE[file_name][1]
    try:
        with open(file_name, 'r', encoding='UTF-8') as f:
            FILE_CACHE[file_name] = (os.stat(file_name).st_mtime, f.read())
            return FILE_CACHE[file_name][1]
    except TypeError:
        with open(file_name, 'r') as f:
            FILE_CACHE[file_name] = (os.stat(file_name).st_mtime, f.read())
            return FILE_CACHE[file_name][1]

REG_PROOF_USING = re.compile(r'The proof of ([^\s]+)\s*should start with:\s*(Proof using[^\.]+\.)', re.MULTILINE)

def all_matches(reg, source, **env):
    source_text = ''
    for i in source:
        source_text += i
        cur_match = reg.search(source_text)
        while cur_match:
            ignoring = source_text[:cur_match.start()].strip()
            if ignoring and env['verbose'] > 1:
                env['log']('Ignoring: ' + repr(ignoring))
            yield cur_match.groups()
            source_text = source_text[cur_match.end():]
            cur_match = reg.search(source_text)

def lib_to_dir_map(libnames):
    return dict((lib, dirname) for dirname, lib in libnames)

def split_to_file_and_rest(theorem_id, **kwargs):
    module_part, rest_part = theorem_id.split('#', 1)
    module_parts = module_part.split('.')
    if len(module_parts) == 0: return (None, None)
    rest_parts = []
    while len(module_parts) > 0:
        rest_parts.insert(0, module_parts.pop())
        if '.'.join(module_parts) in kwargs['lib_to_dir'].keys():
            dirname = kwargs['lib_to_dir']['.'.join(module_parts)]
            filename = os.path.join(dirname, rest_parts[0] + '.v')
            if os.path.exists(filename):
                return (filename, ('.'.join(rest_parts[1:]) + '#' + rest_part).strip('#'))
    return (None, None)

ALL_DEFINITONS_STR = (r'(?<!Existing )(?:' +
                      r'Theorem|Lemma|Fact|Remark|Corollary|Proposition|Property' +
                      r'|Definition|Example|SubClass' +
                      r'|Let|Fixpoint|CoFixpoint' +
                      r'|Structure|Coercion|Instance' +
                      r'|Add Parametric Morphism' +
                      r')\s+%s(?=[\s\(:{\.]|$)')

ALL_DEFINITIONS_FULL_STRS = (r'^([ \t]*)(' + ALL_DEFINITONS_STR + r'[^\.]+\.\n)',
                             r'^([ \t]*)(' + ALL_DEFINITONS_STR + r'(?:[^\.]+|\.[A-Za-z])+\.\n)')

ALL_ENDINGS = (r'(?:Qed|Defined|Save|Admitted|Abort)\s*\.')


def update_definitions(contents, filename, rest_id, suggestion, **env):
    name = rest_id.split('#')[-1]
    if len(re.findall(ALL_DEFINITONS_STR % name, contents, re.MULTILINE)) <= 1:
        match = re.search(ALL_DEFINITONS_STR % name, contents, re.MULTILINE)
        if match:
            after_match = contents[match.end():]
            ending = re.search(ALL_ENDINGS, after_match, re.MULTILINE)
            if ending:
                proof_part = after_match[:ending.start()]
                if proof_part.count('Proof') == 1:
                    proof_match = re.search('Proof(?: using[^\.]*)?\.', proof_part)
                    if proof_match:
                        if proof_match.group() == suggestion:
                            return contents # already correct
                        elif proof_match.group() == 'Proof.':
                            return (contents[:match.end()+proof_match.start()] +
                                    suggestion +
                                    contents[match.end()+proof_match.end():])
                        else:
                            if env['verbose'] >= 0:
                                env['log']('Warning: Mismatch between existing Proof using and suggested Proof using:')
                                env['log']('In %s, id %s, found %s, expected %s' % (filename, rest_id, proof_match.group(), suggestion))
                    else:
                        if env['verbose'] >= 0: env['log']('Warning: Mismatched Proofs found in %s for %s' % (filename, rest_id))
                elif proof_part.count('Proof') == 0:
                    extended_proof_part = contents[match.start():match.end()+ending.start()]
                    for ALL_DEFINITIONS_FULL_STR in ALL_DEFINITIONS_FULL_STRS:
                        reg = re.compile(ALL_DEFINITIONS_FULL_STR % name, re.MULTILINE | re.DOTALL)
                        if reg.search(extended_proof_part):
                            return contents[:match.start()] + reg.sub(r'\1\2\1%s\n' % suggestion, extended_proof_part) + contents[match.end()+ending.start():]
                    if env['verbose'] >= 0: env['log']('Warning: No Proof found in %s for %s' % (filename, rest_id))
                else:
                    if env['verbose'] >= 0: env['log']('Warning: Too many Proofs found in %s for %s' % (filename, rest_id))
            else:
                if env['verbose'] >= 0: env['log']('Warning: No %s found in %s for %s' % (ALL_ENDINGS, filename, rest_id))
        else:
            if env['verbose'] >= 0: env['log']('Warning: No %s found in %s' % (rest_id, filename))
    else:
        if env['verbose'] >= 0: env['log']('Warning: Too many %s found in %s' % (rest_id, filename))
    return contents

if __name__ == '__main__':
    args = parser.parse_args()
    source = args.source
    log = make_logger(args.log_files)
    if args.verbose is None: args.verbose = DEFAULT_VERBOSITY
    if args.quiet is None: args.quiet = 0
    verbose = args.verbose - args.quiet
    env = {
        'libnames': args.libnames,
        'lib_to_dir': lib_to_dir_map(args.libnames),
        'verbose': verbose,
        'log': log
        }
    for theorem_id, suggestion in all_matches(REG_PROOF_USING, source, **env):
        filename, rest_id = split_to_file_and_rest(theorem_id, **env)
        if filename is not None:
            orig = read_from_file(filename)
            updated = update_definitions(orig, filename, rest_id, suggestion, **env)
            if updated != orig:
                if env['verbose'] >= 1: env['log']('Updating %s in %s' % (rest_id, filename))
                write_to_file(filename, updated)
