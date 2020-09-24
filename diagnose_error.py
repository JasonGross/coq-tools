from __future__ import with_statement, print_function
import os, sys, tempfile, subprocess, re, time, math, glob, threading
from Popen_noblock import Popen_async, Empty
from memoize import memoize
from file_util import clean_v_file
from util import re_escape
import util

__all__ = ["has_error", "get_error_line_number", "make_reg_string", "get_coq_output", "get_coq_output_iterable", "get_error_string", "get_timeout", "reset_timeout", "reset_coq_output_cache"]

DEFAULT_PRE_PRE_ERROR_REG_STRING = 'File "[^"]+", line ([0-9]+), characters [0-9-]+:\n'
DEFAULT_PRE_ERROR_REG_STRING = 'File "[^"]+", line ([0-9]+), characters [0-9-]+:\n(?!Warning)'
DEFAULT_ERROR_REG_STRING = DEFAULT_PRE_ERROR_REG_STRING + '((?:.|\n)+)'
DEFAULT_ERROR_REG_STRING_GENERIC = DEFAULT_PRE_PRE_ERROR_REG_STRING + '(%s)'

def clean_output(output):
    return output.replace('\r\n', '\n').replace('\n\r', '\n').replace('\r', '\n')

@memoize
def get_error_match(output, reg_string=DEFAULT_ERROR_REG_STRING, pre_reg_string=DEFAULT_PRE_ERROR_REG_STRING):
    """Returns the final match of reg_string"""
    locations = [0] + [m.start() for m in re.finditer(pre_reg_string, output)]
    reg = re.compile(reg_string)
    results = (reg.search(output[start_loc:]) for start_loc in reversed(locations))
    for result in results:
        if result: return result
    return None

@memoize
def has_error(output, reg_string=DEFAULT_ERROR_REG_STRING, pre_reg_string=DEFAULT_PRE_ERROR_REG_STRING):
    """Returns True if the coq output encoded in output has an error
    matching the given regular expression, False otherwise.
    """
    errors = get_error_match(output, reg_string=reg_string, pre_reg_string=pre_reg_string)
    if errors:
        return True
    else:
        return False

@memoize
def get_error_line_number(output, reg_string=DEFAULT_ERROR_REG_STRING, pre_reg_string=DEFAULT_PRE_ERROR_REG_STRING):
    """Returns the line number that the error matching reg_string
    occured on.

    Precondition: has_error(output, reg_string)
    """
    errors = get_error_match(output, reg_string=reg_string, pre_reg_string=pre_reg_string)
    return int(errors.groups()[0])

@memoize
def get_error_string(output, reg_string=DEFAULT_ERROR_REG_STRING, pre_reg_string=DEFAULT_PRE_ERROR_REG_STRING):
    """Returns the error string of the error matching reg_string.

    Precondition: has_error(output, reg_string)
    """
    errors = get_error_match(output, reg_string=reg_string, pre_reg_string=pre_reg_string)
    return errors.groups()[1]

@memoize
def make_reg_string(output, strict_whitespace=False):
    """Returns a regular expression for matching the particular error
    in output.

    Precondition: has_error(output)
    """
    unstrictify_whitespace = (lambda s: s)
    if not strict_whitespace:
        unstrictify_whitespace = (lambda s: re.sub(r'(?:\\s\\+)+', r'\\s+', re.sub(r'(?:\\ )+', r'\\s+', re.sub(r'(\\n|\n)(?:\\ )+', r'\\s+', s.replace('\\\n', '\n')))).replace('\n', '\s').replace(r'\s+\s', r'\s+').replace(r'\s++', r'\s+'))

    error_string = get_error_string(output).strip()
    if not util.PY3: error_string = error_string.decode('utf-8')
    if 'Universe inconsistency' in error_string or 'universe inconsistency' in error_string:
        re_string = re.sub(r'([Uu]niverse\\ inconsistency.*) because(.|\n)*',
                           r'\1 because.*',
                           re_escape(error_string))
        re_string = re.sub(r'(\s)[^\s]+?\.([0-9]+)',
                           r'\1[^\\s]+?\\.\2',
                           re_string)
    elif 'Unsatisfied constraints' in error_string:
        re_string = re.sub(r'Error:\\ Unsatisfied\\ constraints:.*(?:\n.+)*.*\\\(maybe\\ a\\ bugged\\ tactic\\\)',
                           r'Error:\\ Unsatisfied\\ constraints:.*(?:\\n.+)*.*\\(maybe\\ a\\ bugged\\ tactic\\)',
                           re_escape(error_string),
                           re.DOTALL)
    elif 'Unable to satisfy the following constraints' in error_string:
        re_string = re.sub(r'Error:\\ Unable\\ to\\ satisfy\\ the\\ following\\ constraints:.*(?:\n.*)*',
                           r'Error:\\ Unable\\ to\\ satisfy\\ the\\ following\\ constraints:.*(?:\\n.*)*',
                           re_escape(error_string),
                           re.DOTALL)
    else:
        re_string = re_escape(error_string)
    re_string = re.sub(r'tmp(?:[A-Za-z\d]|\\_)+',
                       r'tmp[A-Za-z_\\d]+',
                       re_string)
    if r'Universe\ instance\ should\ have\ length\ ' not in re_string:
        re_string = re.sub(r'[\d]+',
                           r'[\\d]+',
                           re_string)
    ret = DEFAULT_ERROR_REG_STRING_GENERIC % unstrictify_whitespace(re_string)
    if not util.PY3: ret = ret.encode('utf-8')
    return ret

TIMEOUT = None

def get_timeout():
    return TIMEOUT

def reset_timeout():
    global TIMEOUT
    TIMEOUT = None

def timeout_Popen_communicate(*args, **kwargs):
    ret = { 'value' : ('', ''), 'returncode': None }
    timeout = kwargs.get('timeout')
    del kwargs['timeout']
    input_val = kwargs.get('input')
    del kwargs['input']
    p = subprocess.Popen(*args, **kwargs)

    def target():
        ret['value'] = tuple(map(util.s, p.communicate(input=input_val)))
        ret['returncode'] = p.returncode

    thread = threading.Thread(target=target)
    thread.start()

    thread.join(timeout)
    if not thread.is_alive():
        return (ret['value'], ret['returncode'])

    p.terminate()
    thread.join()
    return (tuple(map((lambda s: (s if s else '') + '\nTimeout!'), ret['value'])), ret['returncode'])


def memory_robust_timeout_Popen_communicate(*args, **kwargs):
    while True:
        try:
            return timeout_Popen_communicate(*args, **kwargs)
        except OSError as e:
            print('Warning: subprocess.Popen%s%s failed with %s\nTrying again in 10s' % (repr(tuple(args)), repr(kwargs), repr(e)))
            time.sleep(10)

COQ_OUTPUT = {}

def prepare_cmds_for_coq_output(coqc_prog, coqc_prog_args, contents, cwd=None, timeout_val=0, **kwargs):
    key = (coqc_prog, tuple(coqc_prog_args), kwargs['pass_on_stdin'], contents, timeout_val, cwd)
    if key in COQ_OUTPUT.keys():
        file_name = COQ_OUTPUT[key][0]
    else:
        with tempfile.NamedTemporaryFile(suffix='.v', delete=False, mode='wb') as f:
            f.write(util.b(contents))
            file_name = f.name

    file_name_root = os.path.splitext(file_name)[0]

    cmds = [coqc_prog] + list(coqc_prog_args)
    pseudocmds = ''
    input_val = None
    if kwargs['is_coqtop']:
        if kwargs['pass_on_stdin']:
            input_val = contents
            cmds.extend(['-q'])
            pseudocmds = '" < "%s' % file_name
        else:
            cmds.extend(['-load-vernac-source', file_name_root, '-q'])
    else:
        cmds.extend([file_name, '-q'])
    if kwargs['verbose'] >= kwargs['verbose_base']:
        kwargs['log']('\nRunning command: "%s%s"' % ('" "'.join(cmds), pseudocmds))
    if kwargs['verbose'] >= kwargs['verbose_base'] + 1:
        kwargs['log']('\nContents:\n%s\n' % contents)

    return key, file_name, cmds, input_val

def reset_coq_output_cache(coqc_prog, coqc_prog_args, contents, timeout_val, cwd=None, is_coqtop=False, pass_on_stdin=False, verbose_base=1, **kwargs):
    key, file_name, cmds, input_val = prepare_cmds_for_coq_output(coqc_prog, coqc_prog_args, contents, cwd=cwd, timeout_val=timeout_val, is_coqtop=is_coqtop, pass_on_stdin=pass_on_stdin, verbose_base=verbose_base, **kwargs)

    if key in COQ_OUTPUT.keys(): del COQ_OUTPUT[key]

def get_coq_output(coqc_prog, coqc_prog_args, contents, timeout_val, cwd=None, is_coqtop=False, pass_on_stdin=False, verbose_base=1, **kwargs):
    """Returns the coqc output of running through the given
    contents.  Pass timeout_val = None for no timeout."""
    global TIMEOUT
    if timeout_val is not None and timeout_val < 0 and TIMEOUT is not None:
        return get_coq_output(coqc_prog, coqc_prog_args, contents, TIMEOUT, cwd=cwd, is_coqtop=is_coqtop, pass_on_stdin=pass_on_stdin, verbose_base=verbose_base, **kwargs)

    key, file_name, cmds, input_val = prepare_cmds_for_coq_output(coqc_prog, coqc_prog_args, contents, cwd=cwd, timeout_val=timeout_val, is_coqtop=is_coqtop, pass_on_stdin=pass_on_stdin, verbose_base=verbose_base, **kwargs)

    if key in COQ_OUTPUT.keys(): return COQ_OUTPUT[key][1]

    start = time.time()
    ((stdout, stderr), returncode) = memory_robust_timeout_Popen_communicate(cmds, stderr=subprocess.STDOUT, stdout=subprocess.PIPE, stdin=subprocess.PIPE, timeout=(timeout_val if timeout_val is not None and timeout_val > 0 else None), input=input_val, cwd=cwd)
    finish = time.time()
    if kwargs['verbose'] >= verbose_base + 1:
        kwargs['log']('\nretcode: %d\nstdout:\n%s\n\nstderr:\n%s\n\n' % (returncode, util.s(stdout), util.s(stderr)))
    if TIMEOUT is None and timeout_val is not None:
        TIMEOUT = 3 * max((1, int(math.ceil(finish - start))))
    clean_v_file(file_name)
    ## remove instances of the file name
    #stdout = stdout.replace(os.path.basename(file_name[:-2]), 'Top')
    COQ_OUTPUT[key] = (file_name, (clean_output(util.s(stdout)), tuple(cmds), returncode))
    return COQ_OUTPUT[key][1]

def get_coq_output_iterable(coqc_prog, coqc_prog_args, contents, cwd=None, is_coqtop=False, pass_on_stdin=False, verbose_base=1, sep='\nCoq <', **kwargs):
    """Returns the coqc output of running through the given
    contents."""

    key, file_name, cmds, input_val = prepare_cmds_for_coq_output(coqc_prog, coqc_prog_args, contents, cwd=cwd, timeout_val=None, is_coqtop=is_coqtop, pass_on_stdin=pass_on_stdin, verbose_base=verbose_base, **kwargs)

    if key in COQ_OUTPUT.keys():
        for i in COQ_OUTPUT[key][1].split(sep): yield i

    p = Popen_async(cmds, stderr=subprocess.STDOUT, stdout=subprocess.PIPE, stdin=subprocess.PIPE, cwd=cwd)

    so_far = []
    cur = ''
    yielded = True
    completed = False
    while True:
        if yielded and not completed:
            if input_val:
                i = input_val.index('\n') + 1 if '\n' in input_val else len(input_val)
                if kwargs['verbose'] >= 3: print(input_val[:i], end='')
                p.stdin.write(input_val[:i])
                input_val = input_val[i:]
                p.stdin.flush()
                yielded = False
            else:
                completed = True
                p.stdin.close()
        curv = p.stdout.get(True)
        if kwargs['verbose'] >= 3: print(curv, end='')
        cur += curv
        if sep in cur:
            vals = cur.split(sep)
            for val in vals[:-1]:
                yield val
                yielded = True
                so_far.append(val)
            cur = vals[-1]
    if cur != '':
        yield cur
        so_far.append(cur)
    clean_v_file(file_name)
    ## remove instances of the file name
    #stdout = stdout.replace(os.path.basename(file_name[:-2]), 'Top')
    COQ_OUTPUT[key] = (file_name, (clean_output(sep.join(so_far)), tuple(cmds), None))
