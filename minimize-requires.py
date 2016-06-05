#!/usr/bin/env python
import argparse, shutil, os, os.path, sys, re
from custom_arguments import add_libname_arguments, update_env_with_libnames, add_logging_arguments, process_logging_arguments
from split_file import get_coq_statement_ranges, UnsupportedCoqVersionError
from import_util import get_references_for, get_file
from file_util import write_to_file
from memoize import memoize
from minimizer_drivers import run_binary_search
import diagnose_error

# {Windows,Python,coqtop} is terrible; we fail to write to (or read
# from?) coqtop.  But we can wrap it in a batch scrip, and it works
# fine.
SCRIPT_DIRECTORY = os.path.dirname(os.path.realpath(__file__))
DEFAULT_COQTOP = 'coqtop' if os.name != 'nt' else os.path.join(SCRIPT_DIRECTORY, 'coqtop.bat')

parser = argparse.ArgumentParser(description='Remove useless Requires in a file')
parser.add_argument('input_files', metavar='INFILE', nargs='+', type=argparse.FileType('r'),
                    help='.v files to update')
parser.add_argument('--in-place', '-i', metavar='SUFFIX', dest='suffix', nargs='?', type=str, default='',
                    help='update files in place (makes backup if SUFFIX supplied)')
parser.add_argument('--absolutize', dest='absolutize',
                    action='store_const', default=False, const=True,
                    help=("Replace Requires with fully qualified versions."))
parser.add_argument('--timeout', dest='timeout', metavar='SECONDS', type=int, default=-1,
                    help=("Use a timeout; make sure Coq is " +
                          "killed after running for this many seconds. " +
                          "If 0, there is no timeout.  If negative, then " +
                          "twice the initial run of the script is used.\n\n" +
                          "Default: -1"))
parser.add_argument('--no-timeout', dest='timeout', action='store_const', const=0,
                    help=("Do not use a timeout"))
parser.add_argument('--coqbin', metavar='COQBIN', dest='coqbin', type=str, default='',
                    help='The path to a folder containing the coqc and coqtop programs.')
parser.add_argument('--coqc', metavar='COQC', dest='coqc', type=str, default='coqc',
                    help='The path to the coqc program.')
parser.add_argument('--arg', metavar='ARG', dest='coqc_args', type=str, action='append',
                    help='Arguments to pass to coqc; e.g., " -indices-matter" (leading and trailing spaces are stripped)')
add_libname_arguments(parser)
add_logging_arguments(parser)

def insert_references(contents, ranges, references, **kwargs):
    ret = []
    prev = 0
    if kwargs['verbose']:
        bad = [(start, end, loc, append, ty) for start, end, loc, append, ty in references
               if append != '<>' or ty != 'lib']
        if bad:
            kwargs['log']('Invalid glob entries: %s' % '\n'.join('R%d:%d %s <> %s %s' % (start, end, loc, append, ty)
                                                                 for start, end, loc, append, ty in bad))
    for start, finish in ranges:
        if prev < start:
            ret.append((contents[prev:start], tuple()))
        if kwargs['verbose']:
            bad = [(rstart, rend, loc, append, ty) for rstart, rend, loc, append, ty in references
                   if (start <= rstart or rend <= finish) and
                   not ((start <= rstart and rend <= finish) or
                        finish <= rstart or rend <= start)]
            if bad:
                kwargs['log']('Invalid glob entries partially overlapping (%d, %d]: %s'
                              % (start, finish,
                                 '\n'.join('R%d:%d %s <> %s %s' % (start, end, loc, append, ty)
                                           for start, end, loc, append, ty in bad)))

        cur_references = tuple((rstart - start, rend - start, loc) for rstart, rend, loc, append, ty in references
                               if start <= rstart and rend <= finish)
        ret.append((contents[start:finish], cur_references))
        prev = finish
    if prev < len(contents):
        ret.append((contents[prev:], tuple()))
    return tuple(reversed(ret))

SKIP='SKIP'
ABSOLUTIZE='ABSOLUTIZE'
REMOVE='REMOVE'

def trailing_whitespace(text):
    return ''.join(sorted(re.search(r'(\s*)$', text, flags=re.DOTALL).groups()[0]))

def leading_whitespace(text):
    return ''.join(sorted(re.search(r'^(\s*)', text, flags=re.DOTALL).groups()[0]))

def whitespace_to_key(ws):
    return (ws.count('\n'), ws.count('\t'), ws.count(' '), len(ws), ws)

def gobble_whitespace(before, after):
    before_ws, after_ws = trailing_whitespace(before), leading_whitespace(after)
    assert(whitespace_to_key('') < whitespace_to_key(' ')) # sanity check
    if before_ws and after_ws:
        if whitespace_to_key(before_ws) < whitespace_to_key(after_ws):
            return (before[:-len(before_ws)], after)
        else:
            return (before, after[len(after_ws):])
    elif before_ws:
        return (before[:-len(before_ws)], after)
    elif after_ws:
        return (before, after[len(after_ws):])
    else:
        return (before, after)

def step_state(state, action):
    ret = []
    state = list(state)
    while len(state) > 0:
        (text, references), state = state[0], state[1:]
        if references:
            (start, end, loc), new_references = references[0], tuple(references[1:])
            if action == SKIP or action is None:
                ret.append((text, new_references))
            elif action == ABSOLUTIZE:
                ret.append((text[:start] + loc + text[end:], new_references))
            elif action == REMOVE:
                if new_references: # still other imports, safe to just remove
                    pre_text, post_text = gobble_whitespace(text[:start], text[end:])
                    ret.append((pre_text + post_text, new_references))
                else: # no other imports; remove this line completely
                    if ret and state:
                        prev_text, post_text = gobble_whitespace(ret[-1][0], state[0][0])
                        ret[-1] = (prev_text, ret[-1][1])
                        state[0] = (post_text, state[0][1])
                    elif ret:
                        ret[-1] = (ret[-1][0].rstrip(), ret[-1][1])
                    elif state:
                        state[0] = (state[0][0].lstrip(), state[0][1])
            else:
                raise ValueError
            ret.extend(state)
            return tuple(ret)
        else:
            ret.append((text, references))
    return None

def state_to_contents(state):
    return ''.join(reversed([text for text, refs in state]))

def make_check_state(verbose_base=0, **kwargs):
    @memoize
    def check_contents(contents):
        output, cmds = diagnose_error.get_coq_output(kwargs['coqc'], kwargs['coqc_args'], contents, kwargs['timeout'], verbose_base=2, **kwargs)
        if diagnose_error.has_error(output):
            if kwargs['verbose'] + verbose_base >= 3:
                kwargs['log']('Failed change.  Error when running "%s":\n%s' % ('" "'.join(cmds), output))
        elif kwargs['verbose'] + verbose_base >= 4:
            kwargs['log']('Successful change')
            if kwargs['verbose'] + verbose_base >= 5:
                kwargs['log']('New contents:\n"""\n%s\n"""' % contents)
        return not diagnose_error.has_error(output)

    def check_state(state):
        return check_contents(state_to_contents(state))

    return check_state

def make_save_state(filename, **kwargs):
    def save_state(state, final=False):
        contents = state_to_contents(state)
        if kwargs['inplace']:
            do_backup = kwargs['suffix'] is not None and len(kwargs['suffix']) > 0
            write_to_file(filename, contents, do_backup=do_backup, backup_ext=kwargs['suffix'])
        elif final:
            print(contents)
    return save_state

if __name__ == '__main__':
    args = process_logging_arguments(parser.parse_args())
    env = {
        'verbose': args.verbose,
        'log': args.log,
        'coqc': (args.coqc if args.coqbin == '' else os.path.join(args.coqbin, args.coqc)),
        'coqc_args': (args.coqc_args if args.coqc_args else tuple()),
        'timeout': args.timeout,
        'inplace': args.suffix != '', # it's None if they passed no argument, and '' if they didn't pass -i
        'suffix': args.suffix,
        }
    update_env_with_libnames(env, args)

    try:
        failed = False
        for input_file in args.input_files:
            name = input_file.name
            input_file.close()
            ranges = get_coq_statement_ranges(name, **env)
            contents = get_file(name, absolutize=tuple(), update_globs=True, **env)
            refs = get_references_for(name, types=('lib',), update_globs=True, **env)
            annotated_contents = insert_references(contents, ranges, refs, **env)
            save_state = make_save_state(name, **env)
            check_state = make_check_state(**env)
            verbose_check_state = make_check_state(verbose_base=4-env['verbose'], **env)
            if env['verbose']: env['log']('Running coq on initial contents...')
            if not verbose_check_state(annotated_contents):
                env['log']('ERROR: Failed to update %s' % name)
                failed = True
                continue
            final_state = run_binary_search(annotated_contents, check_state, step_state, save_state, (REMOVE, ABSOLUTIZE))
            if final_state is not None:
                if env['verbose']: env['log']('Saving final version of %s...' % name)
                save_state(final_state, final=True)
        if failed:
            sys.exit(1)
    except UnsupportedCoqVersionError:
        env['log']('ERROR: Your version of coqc (%s) does not support -time' % env['coqc'])
        sys.exit(1)
