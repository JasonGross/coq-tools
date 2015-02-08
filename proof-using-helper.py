#!/usr/bin/env python
from __future__ import with_statement
import os, sys, re, argparse
from custom_arguments import add_libname_arguments

# TODO:
# - handle fake ambiguities from [Definition foo] in a comment
# - handle theorems inside proof blocks
# - do the right thing for [Theorem foo. Theorem bar. Proof. Qed. Qed.] (we do the wrong thing right now)
# - make use of glob file?

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
parser.add_argument('--hide', dest='hide_reg', nargs='*', type=str,
                    default=['.*_subproof[0-9]*$', '.*_Proper$'],
                    help=('Regular expressions to not display warnings about on low verbosity.  ' +
                          '[Set Suggest Proof Using] can give suggestions about hard-to-find ' +
                          'identifiers, and we might want to surpress them.'))
parser.add_argument('--no-hide', dest='hide_reg', action='store_const', const=[])
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
            if ignoring and env['verbose'] > 2:
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
        elif '.'.join(module_parts) == '':
            dirname = '.'
        else:
            continue
        for split_i in range(0, len(rest_parts)):
            filename = os.path.join(dirname, *(rest_parts[:split_i] + [rest_parts[split_i] + '.v']))
            if os.path.exists(filename):
                return (filename, ('.'.join(rest_parts[1:]) + '#' + rest_part).strip('#'))
    return (None, None)

ALL_DEFINITONS_STR = (r'[ \t]*(?:' +
                      r'Theorem|Lemma|Fact|Remark|Corollary|Proposition|Property' +
                      r'|Definition|Example|SubClass' +
                      r'|Let|Fixpoint|CoFixpoint' +
                      r'|Structure|Coercion|(?<!Existing )Instance' +
                      r'|Add Parametric Morphism' +
                      r')\s+%s(?=[\s\(:{\.]|$)')

ALL_DEFINITONS_STR_QUICK = (r'(?:' +
                            r'Theorem|Lemma|Fact|Remark|Corollary|Proposition|Property' +
                            r'|Definition|Example|SubClass' +
                            r'|Let|Fixpoint|CoFixpoint' +
                            r'|Structure|Coercion|Instance' +
                            r'|Add Parametric Morphism' +
                            r')\s+%s')


ALL_DEFINITIONS_FULL_STRS = (r'^([ \t]*)(' + ALL_DEFINITONS_STR_QUICK + r'[^\.]+\.\n)',
                             r'^([ \t]*)(' + ALL_DEFINITONS_STR_QUICK + r'(?:[^\.]+|\.[A-Za-z\(\)])+\.\n)')

ALL_ENDINGS = (r'(?:Qed|Defined|Save|Admitted|Abort)\s*\.')

def update_proof(name, before_match, match, after_match, filename, rest_id, suggestion, **env):
    ending = re.search(ALL_ENDINGS, after_match, re.MULTILINE)
    if ending:
        proof_part = after_match[:ending.start()]
        if proof_part.count('Proof') == 1:
            proof_match = re.search('Proof(?: using[^\.]*)?\.', proof_part)
            if proof_match:
                if proof_match.group() == suggestion:
                    return None # already correct
                elif proof_match.group() == 'Proof.':
                    return (before_match + match.group() + after_match[:proof_match.start()] +
                            suggestion +
                            after_match[proof_match.end():])
                else:
                    if env['verbose'] >= 0:
                        env['log']('Warning: Mismatch between existing Proof using and suggested Proof using:')
                        env['log']('In %s, id %s, found %s, expected %s' % (filename, rest_id, proof_match.group(), suggestion))
            else:
                if env['verbose'] >= 0: env['log']('Warning: Mismatched Proofs found in %s for %s' % (filename, rest_id))
        elif proof_part.count('Proof') == 0:
            extended_proof_part = match.group() + proof_part
            for ALL_DEFINITIONS_FULL_STR in ALL_DEFINITIONS_FULL_STRS:
                reg = re.compile(ALL_DEFINITIONS_FULL_STR % name, re.MULTILINE | re.DOTALL)
                if env['verbose'] > 3: env['log']('re.search(%s, %s, re.MULTILINE | re.DOTALL)' % (repr(ALL_DEFINITIONS_FULL_STR % name), repr(extended_proof_part)))
                if reg.search(extended_proof_part):
                    return before_match + reg.sub(r'\1\2\1%s\n' % suggestion, extended_proof_part) + after_match[ending.start():]
            if env['verbose'] >= 0: env['log']('Warning: No Proof found in %s for %s' % (filename, rest_id))
        else:
            if env['verbose'] >= 0: env['log']('Warning: Too many Proofs found in %s for %s' % (filename, rest_id))
    else:
        if env['verbose'] >= 0: env['log']('Warning: No %s found in %s for %s' % (ALL_ENDINGS, filename, rest_id))
    return None

def unsafe_update_definitions(name, contents, filename, rest_id, suggestion, **env):
    match = re.search(ALL_DEFINITONS_STR % name, contents, re.MULTILINE)
    if match:
        return update_proof(name, contents[:match.start()], match, contents[match.end():], filename, rest_id, suggestion, **env)
    else:
        if env['verbose'] >= 0 and (env['verbose'] > 1 or not re.search('|'.join(env['hide_reg']), rest_id)):
            env['log']('Warning: No %s found in %s' % (rest_id, filename))
    return None

def update_definitions(contents, filename, rest_id, suggestion, **env):
    name = rest_id.split('#')[-1]
    if len(re.findall(ALL_DEFINITONS_STR % name, contents, re.MULTILINE)) <= 1:
        return unsafe_update_definitions(name, contents, filename, rest_id, suggestion, **env)
    else:
        modules = rest_id.split('#')[0].split('.')
        pre, mod_body, post = '', contents, ''
        while len(modules) > 0:
            mod_name = modules.pop(0)
            cur_mod = 'Module ' + mod_name
            cur_end = 'End ' + mod_name + '.'
            if mod_body.count(cur_mod) == 1:
                pre += mod_body[:mod_body.index(cur_mod) + len(cur_mod)]
                mod_body = mod_body[mod_body.index(cur_mod) + len(cur_mod):]
                if mod_body.count(cur_end) == 1:
                    post = mod_body[mod_body.index(cur_end):] + post
                    mod_body = mod_body[:mod_body.index(cur_end)]
                    if len(re.findall(ALL_DEFINITONS_STR % name, mod_body, re.MULTILINE)) <= 1:
                        ret = unsafe_update_definitions(name, mod_body, filename, rest_id, suggestion, **env)
                        if ret is not None:
                            return pre + ret + post
                        else:
                            return None
                else:
                    if env['verbose'] >= 0: env['log']('Warning: Too many %s found for %s in %s' % (cur_end, rest_id, filename))
                    break
            else:
                if env['verbose'] >= 0: env['log']('Warning: Too many %s found for %s in %s' % (cur_mod, rest_id, filename))
                break
        if env['verbose'] >= 0: env['log']('Warning: Module disambiguation was insufficient to uniqueize %s in %s' % (rest_id, filename))
        if env['verbose'] > 1: env['log']('Found: %s' % repr(re.findall(ALL_DEFINITONS_STR % name, contents, re.MULTILINE)))
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
        'log': log,
        'hide_reg': args.hide_reg
        }
    for theorem_id, suggestion in all_matches(REG_PROOF_USING, source, **env):
        filename, rest_id = split_to_file_and_rest(theorem_id, **env)
        if filename is not None:
            orig = read_from_file(filename)
            updated = update_definitions(orig, filename, rest_id, suggestion, **env)
            if updated is not None and updated != orig:
                if env['verbose'] >= 1: env['log']('Updating %s in %s' % (rest_id, filename))
                write_to_file(filename, updated, do_backup=True)
        else:
            log('Warning: Could not find theorem %s' % theorem_id)
