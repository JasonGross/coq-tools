from __future__ import with_statement
import subprocess, tempfile, re
from file_util import clean_v_file
from memoize import memoize

__all__ = ["get_coqc_version", "get_coqtop_version", "get_coqc_help", "get_coq_accepts_top", "group_coq_args_split_recognized", "group_coq_args", "coq_makefile_supports_arg"]

@memoize
def get_coqc_version_helper(coqc):
    p = subprocess.Popen([coqc, "-v"], stderr=subprocess.STDOUT, stdout=subprocess.PIPE, stdin=subprocess.PIPE)
    (stdout, stderr) = p.communicate()
    return stdout.replace('The Coq Proof Assistant, version ', '').replace('\r\n', ' ').replace('\n', ' ').strip()

def get_coqc_version(coqc_prog, **kwargs):
    if kwargs['verbose'] >= 2:
        kwargs['log']('Running command: "%s"' % '" "'.join([coqc_prog, "-v"]))
    return get_coqc_version_helper(coqc_prog)

@memoize
def get_coqc_help_helper(coqc):
    p = subprocess.Popen([coqc, "--help"], stderr=subprocess.STDOUT, stdout=subprocess.PIPE, stdin=subprocess.PIPE)
    (stdout, stderr) = p.communicate()
    return stdout.strip()

def get_coqc_help(coqc_prog, **kwargs):
    if kwargs['verbose'] >= 2:
        kwargs['log']('Running command: "%s"' % '" "'.join([coqc_prog, "--help"]))
    return get_coqc_help_helper(coqc_prog)

@memoize
def get_coqtop_version_helper(coqtop):
    p = subprocess.Popen([coqtop], stderr=subprocess.PIPE, stdout=subprocess.PIPE, stdin=subprocess.PIPE)
    (stdout, stderr) = p.communicate()
    return stdout.replace('Welcome to Coq ', '').replace('\r\n', ' ').replace('\n', ' ').strip()

def get_coqtop_version(coqtop_prog, **kwargs):
    if kwargs['verbose'] >= 2:
        kwargs['log']('Running command: "%s"' % '" "'.join([coqtop_prog, "-v"]))
    return get_coqtop_version_helper(coqtop_prog)

@memoize
def get_coq_accepts_top(coqc):
    temp_file = tempfile.NamedTemporaryFile(suffix='.v', dir='.', delete=True)
    temp_file_name = temp_file.name
    p = subprocess.Popen([coqc, "-top", "Top", temp_file_name], stderr=subprocess.STDOUT, stdout=subprocess.PIPE)
    (stdout, stderr) = p.communicate()
    temp_file.close()
    clean_v_file(temp_file_name)
    return '-top: no such file or directory' not in stdout


HELP_REG = re.compile(r'^  ([^\n]*?)(?:\t|  )', re.MULTILINE)
HELP_MAKEFILE_REG = re.compile(r'^\[(-[^\n\]]*)\]', re.MULTILINE)

def all_help_tags(coqc_help, is_coq_makefile=False):
    if is_coq_makefile:
        return HELP_MAKEFILE_REG.findall(coqc_help)
    else:
        return HELP_REG.findall(coqc_help)

def get_single_help_tags(coqc_help, **kwargs):
    return tuple(i for i in all_help_tags(coqc_help, **kwargs) if ' ' not in i)

def get_multiple_help_tags(coqc_help, **kwargs):
    return dict((i.split(' ')[0], len(i.split(' ')))
                for i in all_help_tags(coqc_help, **kwargs)
                if ' ' in i)

def coq_makefile_supports_arg(coq_makefile_help):
    tags = get_multiple_help_tags(coq_makefile_help, is_coq_makefile=True)
    return any(tag[0] == '-arg' for tag in tags)

def group_coq_args_split_recognized(args, coqc_help, topname=None, is_coq_makefile=False):
    args = list(args)
    bindings = []
    unrecognized_bindings = []
    single_tags = get_single_help_tags(coqc_help, is_coq_makefile=is_coq_makefile)
    multiple_tags = get_multiple_help_tags(coqc_help, is_coq_makefile=is_coq_makefile)
    while len(args) > 0:
        if args[0] in multiple_tags.keys() and len(args) >= multiple_tags[args[0]]:
            cur_binding, args = tuple(args[:multiple_tags[args[0]]]), args[multiple_tags[args[0]]:]
            if cur_binding not in bindings:
                bindings.append(cur_binding)
        else:
            cur = tuple([args.pop(0)])
            if cur[0] not in single_tags:
                unrecognized_bindings.append(cur[0])
            elif cur not in bindings:
                bindings.append(cur)
    if topname is not None and '-top' not in [i[0] for i in bindings] and '-top' in multiple_tags.keys():
        bindings.append(('-top', topname))
    return (bindings, unrecognized_bindings)

def group_coq_args(args, coqc_help, topname=None, is_coq_makefile=False):
    bindings, unrecognized_bindings = group_coq_args_split_recognized(args, coqc_help, topname=topname, is_coq_makefile=is_coq_makefile)
    return bindings + [tuple([v]) for v in unrecognized_bindings]
