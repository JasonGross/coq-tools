#!/usr/bin/env python
import argparse, tempfile, sys, os, re
import custom_arguments
from replace_imports import include_imports, normalize_requires, get_required_contents, recursively_get_requires_from_file
from import_util import get_file
from strip_comments import strip_comments
from strip_newlines import strip_newlines
from split_file import split_coq_file_contents
from split_definitions import split_statements_to_definitions, join_definitions
from admit_abstract import transform_abstract_to_admit
from import_util import lib_of_filename, clear_libimport_cache, IMPORT_ABSOLUTIZE_TUPLE, ALL_ABSOLUTIZE_TUPLE
from memoize import memoize
from coq_version import get_coqc_version, get_coqtop_version, get_coqc_help, get_coq_accepts_top
from custom_arguments import add_libname_arguments, update_env_with_libnames
from file_util import clean_v_file
from util import yes_no_prompt
import diagnose_error

# {Windows,Python,coqtop} is terrible; we fail to write to (or read
# from?) coqtop.  But we can wrap it in a batch scrip, and it works
# fine.
SCRIPT_DIRECTORY = os.path.dirname(os.path.realpath(__file__))
DEFAULT_COQTOP = 'coqtop' if os.name != 'nt' else os.path.join(SCRIPT_DIRECTORY, 'coqtop.bat')

parser = custom_arguments.ArgumentParser(description='Attempt to create a small file which reproduces a bug found in a large development.')
parser.add_argument('bug_file', metavar='BUGGY_FILE', type=argparse.FileType('r'),
                    help='a .v file which displays the bug')
parser.add_argument('output_file', metavar='OUT_FILE', type=str,
                    help='a .v file which will hold intermediate results, as well as the final reduced file')
parser.add_argument('temp_file', metavar='TEMP_FILE', nargs='?', type=str, default='',
                    help='a .v file which will be used to build up intermediate files while they are being tested')
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
parser.add_argument('--strip-newlines', dest='max_consecutive_newlines',
                    metavar='N', nargs='?', type=int, default=2,
                    help=("Passing `--strip-newlines N` will cause the " +
                          "program to, for all M > N, replace any " +
                          "instances of M consecutive newlines with N " +
                          "consecutive newlines.  The result will be a " +
                          "file with no more than N consecutive newlines.  " +
                          "Passing a negative number will disable this option. " +
                          "(Default: 2)"))
parser.add_argument('--no-admit-opaque', dest='admit_opaque',
                    action='store_const', const=False, default=True,
                    help=("Don't try to replace opaque things ([Qed] and [abstract])" +
                          "with [admit]s."))
parser.add_argument('--no-admit-transparent', dest='admit_transparent',
                    action='store_const', const=False, default=True,
                    help=("Don't try to replace transparent things with [admit]s."))
parser.add_argument('--no-aggressive', dest='aggressive',
                    action='store_const', const=False, default=True,
                    help=("Be less aggressive; don't try to remove _all_ definitions/lines."))
parser.add_argument('--no-remove-typeclasses', dest='save_typeclasses',
                    action='store_const', const=True, default=False,
                    help=("Don't remove Hints, Instances, or Canonical Structures; " +
                          "this should mostly preserve typeclass logs, and can be useful " +
                          "for debugging slow typeclass bugs."))
parser.add_argument('--dynamic-header', dest='dynamic_header', nargs='?', type=str,
                    default='(* File reduced by coq-bug-finder from %(old_header)s, then from %(original_line_count)d lines to %(final_line_count)d lines *)',
                    help=("A line to be placed at the top of the " +
                          "output file, followed by a newline.  The " +
                          "variables original_line_count and " +
                          "final_line_count will be available for " +
                          "substitution.  The variable old_header will" +
                          "have the previous contents of this comment. " +
                          "The default is " +
                          "`(* File reduced by coq-bug-finder from %%(old_header)s, then from %%(original_line_count)d lines to %%(final_line_count)d lines *)'"))
parser.add_argument('--header', dest='header', nargs='?', type=str,
                    default='(* coqc version %(coqc_version)s\n   coqtop version %(coqtop_version)s *)',
                    help=("A line to be placed at the top of the " +
                          "output file, below the dynamic header, " +
                          "followed by a newline.  The variables " +
                          "coqtop_version and coqc_version will be " +
                          "available for substitution.  The default is " +
                          "`(* coqc version %%(coqc_version)s\\n   coqtop version %%(coqtop_version) *)'"))
parser.add_argument('--no-strip-trailing-space', dest='strip_trailing_space',
                    action='store_const', const=False, default=True,
                    help=("Don't strip trailing spaces.  By default, " +
                          "trailing spaces on each line are removed."))
parser.add_argument('--no-deps', dest='walk_tree',
                    action='store_const', const=False, default=True,
                    help=("Don't do dependency analysis on all files in the current " +
                          "file tree."))
parser.add_argument('--timeout', dest='timeout', metavar='SECONDS', type=int, default=-1,
                    help=("Use a timeout; make sure Coq is " +
                          "killed after running for this many seconds. " +
                          "If 0, there is no timeout.  If negative, then " +
                          "twice the initial run of the script is used.\n\n" +
                          "Default: -1"))
parser.add_argument('--no-timeout', dest='timeout', action='store_const', const=0,
                    help=("Do not use a timeout"))
parser.add_argument('--no-minimize-before-inlining', dest='minimize_before_inlining',
                    action='store_const', const=False, default=True,
                    help=("Don't run the full minimization script before inlining [Requires], " +
                          "and between the inlining of every individual [Require].\n\n" +
                          "Note that this option will not work well in conjunction with " +
                          "--passing-coqc.\n"
                          "Passing this option results in a much more robust " +
                          "run; it removes the requirement that the compiled dependencies " +
                          "of the file being debugged remain in place for the duration of the run."))
parser.add_argument('--coqbin', metavar='COQBIN', dest='coqbin', type=str, default='',
                    help='The path to a folder containing the coqc and coqtop programs.')
parser.add_argument('--coqc', metavar='COQC', dest='coqc', type=str, default='coqc',
                    help='The path to the coqc program.')
parser.add_argument('--coqtop', metavar='COQTOP', dest='coqtop', type=str, default=DEFAULT_COQTOP,
                    help=('The path to the coqtop program (default: %s).' % DEFAULT_COQTOP))
parser.add_argument('--coqc-is-coqtop', dest='coqc_is_coqtop', default=False, action='store_const', const=True,
                    help="Strip the .v and pass -load-vernac-source to the coqc programs; this allows you to pass `--coqc coqtop'")
parser.add_argument('--coqc-args', metavar='ARG', dest='coqc_args', type=str, action='append',
                    help='Arguments to pass to coqc; e.g., " -indices-matter" (leading and trailing spaces are stripped)')
parser.add_argument('--coqtop-args', metavar='ARG', dest='coqtop_args', type=str, action='append',
                    help='Arguments to pass to coqtop; e.g., " -indices-matter" (leading and trailing spaces are stripped)')
parser.add_argument('--coq_makefile', metavar='COQ_MAKEFILE', dest='coq_makefile', type=str, default='coq_makefile',
                    help='The path to the coq_makefile program.')
parser.add_argument('--passing-coqc', metavar='COQC', dest='passing_coqc', type=str, default='',
                    help='The path to the coqc program that should compile the file successfully.')
parser.add_argument('--passing-coqc-args', metavar='ARG', dest='passing_coqc_args', type=str, action='append',
                    help='Arguments to pass to coqc so that it compiles the file successfully; e.g., " -indices-matter" (leading and trailing spaces are stripped)')
parser.add_argument('--nonpassing-coqc-args', metavar='ARG', dest='nonpassing_coqc_args', type=str, action='append',
                    help='Arguments to pass to coqc so that it compiles the file successfully; e.g., " -indices-matter" (leading and trailing spaces are stripped)')
parser.add_argument('--passing-coqc-is-coqtop', dest='passing_coqc_is_coqtop', default=False, action='store_const', const=True,
                    help="Strip the .v and pass -load-vernac-source to the coqc programs; this allows you to pass `--passing-coqc coqtop'")
parser.add_argument('--arg', metavar='ARG', dest='coq_args', type=str, action='append',
                    help='Arguments to pass to coqc and coqtop; e.g., " -indices-matter" (leading and trailing spaces are stripped)')
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

def restore_file(file_name, backup_ext='.bak', backup_backup_ext='.unbak'):
    if not os.path.exists(file_name + backup_ext):
        raise IOError
    if os.path.exists(file_name):
        if backup_backup_ext:
            backup(file_name, backup_backup_ext)
        else:
            os.remove(file_name)
    os.rename(file_name + backup_ext, file_name)

def write_to_file(file_name, contents, do_backup=False, backup_ext='.bak'):
    backed_up = False
    while not backed_up:
        try:
            if do_backup:
                backup(file_name, ext=backup_ext)
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
        except IOError as e:
            print('Warning: f.write(%s) failed with %s\nTrying again in 10s' % (file_name, repr(e)))
            time.sleep(10)

def read_from_file(file_name):
    try:
        with open(file_name, 'r', encoding='UTF-8') as f:
            return f.read()
    except TypeError:
        with open(file_name, 'r') as f:
            return f.read()

@memoize
def re_compile(pattern, *args):
    return re.compile(pattern, *args)

# memoize the compilation
def re_search(pattern, string, flags=0):
    return re_compile(pattern, flags).search(string)

def get_error_reg_string(output_file_name, **kwargs):
    error_reg_string = ''
    while error_reg_string == '':
        if kwargs['verbose']: kwargs['log']('\nCoqing the file (%s)...' % output_file_name)
        contents = read_from_file(output_file_name)
        diagnose_error.reset_timeout()
        output, cmds = diagnose_error.get_coq_output(kwargs['coqc'], kwargs['coqc_args'], contents, kwargs['timeout'], is_coqtop=kwargs['coqc_is_coqtop'], verbose_base=1, **kwargs)
        if kwargs['timeout'] < 0 and diagnose_error.get_timeout() is not None:
            kwargs['log']('The timeout has been set to: %d' % diagnose_error.get_timeout())
        result = ''
        print("\nThis file produces the following output when Coq'ed:\n%s" % output)
        while result not in ('y', 'n', 'yes', 'no'):
            result = raw_input('Does this output display the correct error? [(y)es/(n)o] ').lower().strip()
        if result in ('n', 'no'):
            raw_input('Please modify the file (%s) so that it errors correctly, and then press ENTER to continue, or ^C to break.' % output_file_name)
            continue

        if diagnose_error.has_error(output):
            error_string = diagnose_error.get_error_string(output)
            error_reg_string = diagnose_error.make_reg_string(output)
            print("\nI think the error is '%s'.\nThe corresponding regular expression is '%s'." % (error_string, error_reg_string.replace('\\\n', '\\n').replace('\n', '\\n')))
            result = ''
            while result not in ('y', 'n', 'yes', 'no'):
                result = raw_input('Is this correct? [(y)es/(n)o] ').lower().strip()
            if result in ('no', 'n'):
                error_reg_string = ''
        else:
            kwargs['log']('\nThe current state of the file does not have a recognizable error.')

        if error_reg_string == '':
            success = False
            while not success:
                error_reg_string = raw_input('\nPlease enter a regular expression which matches on the output.  Leave blank to re-coq the file.\n')
                try:
                    re.compile(error_reg_string)
                except Exception as e:
                    print('\nThat regular expression does not compile: %s' % e)
                    success = False
                else:
                    success = True

        while (error_reg_string != ''
               and (not re.search(error_reg_string, output)
                    or len(re.search(error_reg_string, output).groups()) != 2)):
            if not re.search(error_reg_string, output):
                print('\nThe given regular expression does not match the output.')
            elif len(re.search(error_reg_string, output).groups()) != 2:
                print('\nThe given regular expression does not have two groups.')
                print('It must have one integer group which matches on the line number,')
                print('and another group which matches on the error string.')
            error_reg_string = raw_input('Please enter a valid regular expression which matches on the output.  Leave blank to re-coq the file (%s).\n'
                                         % output_file_name)

        if error_reg_string == '':
            continue

    return error_reg_string

def escape_coq_prog_args(coq_prog_args):
    return ' '.join('"' + arg.replace('\\', '\\\\').replace('"', r'\"') + '"'
                    for arg in coq_prog_args)

def unescape_coq_prog_args(coq_prog_args):
    ret = []
    cur = None
    in_string = False
    idx = 0
    while idx < len(coq_prog_args):
        cur_char = coq_prog_args[idx]
        idx += 1
        if not in_string:
            if cur_char == '"':
                in_string = True
                cur = ''
            elif cur_char not in ' \t':
                print("Warning: Invalid unquoted character '%s' at index %d in coq-prog-args '%s'" % (cur_char, idx - 1, coq_prog_args))
                return tuple(ret)
        else:
            if cur_char == '"':
                in_string = False
                ret.append(cur)
                cur = None
            elif cur_char == '\\':
                if idx < len(coq_prog_args):
                    # take the next character
                    cur += coq_prog_args[idx]
                    idx += 1
                else:
                    print("Warning: Invalid backslash at end of coq-prog-args '%s'" % coq_prog_args)
            else:
                cur += cur_char
    return tuple(ret)


COQ_PROG_ARGS_REG = re.compile(r'coq-prog-args\s*:\s*\(([^\)]+)\)')
def get_coq_prog_args(contents):
     return tuple(arg
                  for args in COQ_PROG_ARGS_REG.findall(contents)
                  for arg in unescape_coq_prog_args(args)
                  if arg not in ("-emacs", "-emacs-U"))

COQ_PROG_ARGS_REP = re.compile(r'[ \t]*\(\*+\s+-\*-\s+.*?\s-\*-\s+\*+\)\s*')
def strip_coq_prog_args(contents):
    return COQ_PROG_ARGS_REP.sub('', contents)

def get_old_header(contents, header=''):
    contents = strip_coq_prog_args(contents)
    if header[:2] == '(*' and header[-2:] == '*)' and '*)' not in header[2:-2]:
        pre_header = header[:header.index('%')]
        if pre_header in contents and contents.index('*)') > contents.index(pre_header):
            return contents[contents.index(pre_header)+len(pre_header):contents.index('*)')].strip()
    return 'original input'

def prepend_header(contents, dynamic_header='', header='', header_dict={}, **kwargs):
    """Fills in the variables in the header for output files"""
    contents = strip_coq_prog_args(contents)
    if dynamic_header[:2] == '(*' and dynamic_header[-2:] == '*)' and '*)' not in dynamic_header[2:-2]:
        pre_header = dynamic_header[:dynamic_header.index('%')]
        if contents[:len(pre_header)] == pre_header:
            # strip the old header
            contents = contents[contents.index('*)')+2:]
            if contents[0] == '\n': contents = contents[1:]
    if header[:2] == '(*' and header[-2:] == '*)' and '*)' not in header[2:-2]:
        pre_header = header[:header.index('%')]
        if contents[:len(pre_header)] == pre_header:
            # strip the old header
            contents = contents[contents.index('*)')+2:]
            if contents[0] == '\n': contents = contents[1:]
    final_line_count = len(contents.split('\n'))
    header_dict = dict(header_dict) # clone the dict
    header_dict['final_line_count'] = final_line_count
    if 'old_header' not in header_dict.keys():
        header_dict['old_header'] = 'original input'
    use_header = (dynamic_header + '\n' + header)  % header_dict
    coq_prog_args = ('(* -*- mode: coq; coq-prog-args: ("-emacs" %s) -*- *)\n' % escape_coq_prog_args(kwargs['coqc_args'])
                     if len(kwargs['coqc_args']) > 0
                     else '')
    ## de-duplicate things in a list
    ## XXX This is a hack to deal with things like "from x lines to y lines, from x lines to y lines"
    #if use_header[-3:] == ' *)':
    #    use_header = ','.join(OrderedSet(use_header[:-3].split(','))) + ' *)'
    return '%s%s\n%s' % (coq_prog_args, use_header, contents)

INSTANCE_REG = re.compile(r"(?<![\w'])Instance\s")
CANONICAL_STRUCTURE_REG = re.compile(r"(?<![\w'])Canonical\s+Structure\s")
TC_HINT_REG = re.compile("(?<![\w'])Hint\s")

CONTENTS_UNCHANGED, CHANGE_SUCCESS, CHANGE_FAILURE = 'contents_unchanged', 'change_success', 'change_failure'
def classify_contents_change(old_contents, new_contents, **kwargs):
    # returns (RESULT_TYPE, PADDED_CONTENTS, OUTPUT_LIST, option BAD_INDEX, DESCRIPTION_OF_FAILURE_MODE)
    new_padded_contents = prepend_header(new_contents, **kwargs)
    if new_contents == old_contents:
        return (CONTENTS_UNCHANGED, new_padded_contents, tuple(), None, 'No change.  ')

    output, cmds = diagnose_error.get_coq_output(kwargs['coqc'], kwargs['coqc_args'], new_contents, kwargs['timeout'], is_coqtop=kwargs['coqc_is_coqtop'], verbose_base=2, **kwargs)
    if diagnose_error.has_error(output, kwargs['error_reg_string']):
        if kwargs['passing_coqc']:
            passing_output, cmds = diagnose_error.get_coq_output(kwargs['passing_coqc'], kwargs['passing_coqc_args'], new_contents, kwargs['timeout'], is_coqtop=kwargs['passing_coqc_is_coqtop'], verbose_base=2, **kwargs)
            if not diagnose_error.has_error(passing_output):
                return (CHANGE_SUCCESS, new_padded_contents, (output, passing_output), None, 'Change successful.  ')
            else:
                return (CHANGE_FAILURE, new_padded_contents, (output, passing_output), 1, 'The alternate coqc (%s) was supposed to pass, but instead emitted an error.  ' % kwargs['passing_coqc'])
        else:
            return (CHANGE_SUCCESS, new_padded_contents, (output,), None, 'Change successful.  ')
    else:
        extra_desc = ''
        if kwargs['verbose'] >= 2:
            extra_desc = 'The error was:\n%s\n' % output
        return (CHANGE_FAILURE, new_padded_contents, (output,), 0, extra_desc)

def check_change_and_write_to_file(old_contents, new_contents, output_file_name,
                                   unchanged_message='No change.', success_message='Change successful.',
                                   failure_description='make a change', changed_description='Changed file',
                                   verbose_base=1,
                                   **kwargs):
    if kwargs['verbose'] >= 2 + verbose_base:
        kwargs['log']('Running coq on the file\n"""\n%s\n"""' % new_contents)
    change_result, contents, outputs, output_i, error_desc = classify_contents_change(old_contents, new_contents, **kwargs)
    if change_result == CONTENTS_UNCHANGED:
        if kwargs['verbose'] >= verbose_base: kwargs['log']('\n%s' % unchanged_message)
        return False
    elif change_result == CHANGE_SUCCESS:
        if kwargs['verbose'] >= verbose_base: kwargs['log']('\n%s' % success_message)
        write_to_file(output_file_name, contents)
        return True
    elif change_result == CHANGE_FAILURE:
        if kwargs['verbose'] >= verbose_base:
            kwargs['log']('\nNon-fatal error: Failed to %s and preserve the error.  %s' % (failure_description, error_desc))
            if not kwargs['remove_temp_file']: kwargs['log']('Writing %s to %s.' % (changed_description.lower(), kwargs['temp_file_name']))
            kwargs['log']('The new error was:')
            kwargs['log'](outputs[output_i])
            if kwargs['verbose'] >= verbose_base+2: kwargs['log']('All Outputs:\n%s' % '\n'.join(outputs))
            if kwargs['remove_temp_file']: kwargs['log']('%s not saved.' % changed_description)
        if not kwargs['remove_temp_file']:
            write_to_file(kwargs['temp_file_name'], contents)
        return False
    else:
        kwargs['log']('ERROR: Unrecognized change result %s on\nclassify_contents_change(\n  %s\n ,%s\n)\n%s'
                      % (change_result, repr(old_contents), repr(new_contents),
                         repr((change_result, contents, outputs, output_i, error_desc))))
    return None


def try_transform_each(definitions, output_file_name, transformer, skip_n=1, **kwargs):
    """Tries to apply transformer to each definition in definitions,
    additionally passing in the list of subsequent definitions.  If
    the returned value of the 'statement' key is not equal to the old
    value, or if the return value is a false-y value (indicating that
    we should remove the line) then we see if the error is still
    present.  If it is, we keep the change; otherwise, we discard it.
    The order in which definitions are passed in is guaranteed to be
    reverse-order.

    Returns updated definitions."""
    if kwargs['verbose'] >= 3: kwargs['log']('try_transform_each')
    original_definitions = [dict(i) for i in definitions]
    # TODO(jgross): Use coqtop and [BackTo] to do incremental checking
    success = False
    i = len(definitions) - 1 - skip_n
    while i >= 0:
        old_definition = definitions[i]
        new_definition = transformer(old_definition, definitions[i + 1:])
        if not new_definition:
            if kwargs['save_typeclasses'] and \
               (INSTANCE_REG.search(old_definition['statement']) or
                CANONICAL_STRUCTURE_REG.search(old_definition['statement']) or
                TC_HINT_REG.search(old_definition['statement'])):
                if kwargs['verbose'] >= 3: kwargs['log']('Ignoring Instance/Canonical Structure/Hint: %s' % old_definition['statement'])
                i -= 1
                continue
            new_definitions = []
        elif isinstance(new_definition, dict):
            if not new_definition['statement'].strip(): new_definitions = []
            else: new_definitions = [new_definition]
        else: new_definitions = list(new_definition)
        if len(new_definitions) != 1 or \
                re.sub(r'\s+', ' ', old_definition['statement']).strip() != re.sub(r'\s+', ' ', new_definitions[0]['statement']).strip():
            if len(new_definitions) == 0:
                if kwargs['verbose'] >= 2: kwargs['log']('Attempting to remove %s' % repr(old_definition['statement']))
                try_definitions = definitions[:i] + definitions[i + 1:]
            else:
                if kwargs['verbose'] >= 2: kwargs['log']('Attempting to transform %s\ninto\n%s' % (old_definition['statement'], ''.join(defn['statement'] for defn in new_definitions)))
                if kwargs['verbose'] >= 2 and len(new_definitions) > 1: kwargs['log']('Splitting definition: %s' % repr(new_definitions))
                try_definitions = definitions[:i] + new_definitions + definitions[i + 1:]

            if check_change_and_write_to_file('', join_definitions(try_definitions), output_file_name, verbose_base=2, **kwargs):
                success = True
                definitions = try_definitions
                # make a copy for saving
                save_definitions = [dict(defn) for defn in try_definitions]
        else:
            if kwargs['verbose'] >= 3: kwargs['log']('No change to %s' % old_definition['statement'])
        i -= 1
    if success:
        if kwargs['verbose'] >= 1: kwargs['log'](kwargs['noun_description'] + ' successful')
        if join_definitions(save_definitions) != join_definitions(definitions):
            kwargs['log']('Probably fatal error: definitions != save_definitions')
        else:
            contents = prepend_header(join_definitions(definitions), **kwargs)
            write_to_file(output_file_name, contents)
        return definitions
    else:
        if kwargs['verbose'] >= 1: kwargs['log'](kwargs['noun_description'] + ' unsuccessful.')
        return original_definitions


def try_transform_reversed(definitions, output_file_name, transformer, skip_n=1, **kwargs):
    """Replaces each definition in definitions, with transformer
    applied to that definition and the subsequent (transformed)
    definitions.  If transformer returns a false-y value, the
    definition is removed.  After transforming the entire list, we see
    if the error is still present.  If it is, we keep the change;
    otherwise, we discard it.  The order in which definitions are
    passed in is guaranteed to be reverse-order.

    Returns updated definitions."""
    if kwargs['verbose'] >= 3: kwargs['log']('try_transform_reversed')
    definitions = list(definitions) # clone the list of definitions
    original_definitions = list(definitions)
    if kwargs['verbose'] >= 3: kwargs['log'](len(definitions))
    if kwargs['verbose'] >= 3: kwargs['log'](definitions)
    for i in reversed(list(range(len(definitions) - skip_n))):
        new_definition = transformer(definitions[i], definitions[i + 1:])
        if new_definition:
            if definitions[i] != new_definition:
                if kwargs['verbose'] >= 2: kwargs['log']('Transforming %s into %s' % (definitions[i]['statement'], new_definition['statement']))
            else:
                if kwargs['verbose'] >= 3: kwargs['log']('No change to %s' % new_definition['statement'])
            definitions[i] = new_definition
        else:
            if kwargs['save_typeclasses'] and \
               (INSTANCE_REG.search(definitions[i]['statement']) or
                CANONICAL_STRUCTURE_REG.search(definitions[i]['statement']) or
                TC_HINT_REG.search(definitions[i]['statement'])):
                if kwargs['verbose'] >= 3: kwargs['log']('Ignoring Instance/Canonical Structure/Hint: %s' % definitions[i]['statement'])
                pass
            else:
                if kwargs['verbose'] >= 2: kwargs['log']('Removing %s' % definitions[i]['statement'])
                definitions = definitions[:i] + definitions[i + 1:]

    if check_change_and_write_to_file('', join_definitions(definitions), output_file_name,
                                      success_message=kwargs['noun_description']+' successful.', failure_description=kwargs['verb_description'],
                                      changed_description='Intermediate code', **kwargs):
        return definitions

    return original_definitions

def try_remove_if_not_matches_transformer(definition_found_in, **kwargs):
    def transformer(cur_definition, rest_definitions):
        if any(definition_found_in(cur_definition, future_definition)
               for future_definition in rest_definitions):
            if kwargs['verbose'] >= 3: kwargs['log']('Definition found; found:\n%s\nin\n%s'
                                 % (cur_definition,
                                    [future_definition['statement']
                                     for future_definition in rest_definitions
                                     if definition_found_in(cur_definition, future_definition)][0]))
            return cur_definition
        else:
            return None
    return transformer

# don't count things like [Section ...], [End ...]
EXCLUSION_REG = re.compile(r"^\s*Section\s+[^\.]+\.\s*$" +
                           r"|^\s*Module\s+[^\.]+\.\s*$" +
                           r"|^\s*End\s+[^\.]+\.\s*$" +
                           r"|^\s*Require\s+[^\.]+\.\s*$" +
                           r"|^\s*Import\s+[^\.]+\.\s*$" +
                           r"|^\s*Export\s+[^\.]+\.\s*$")
def try_remove_if_name_not_found_in_transformer(get_names, **kwargs):
    def definition_found_in(cur_definition, future_definition):
        names = get_names(cur_definition)
        if len(names) == 0:
            return True
        elif EXCLUSION_REG.search(future_definition['statement']):
            return False # we don't care if the name is found in a
                         # statement like [Section ...] or [End ...]
        return any(re_search(r"(?<![\w'])%s(?![\w'])" % re.escape(name), future_definition['statement'])
                   for name in names)
    return try_remove_if_not_matches_transformer(definition_found_in, **kwargs)


def try_remove_if_name_not_found_in_section_transformer(get_names, **kwargs):
    SECTION_BEGIN_REG = re.compile(r'^\s*(?:Section|Module)\s+[^\.]+\.\s*$')
    SECTION_END_REG = re.compile(r'^\s*End\s+[^\.]+\.\s*$')
    def transformer(cur_definition, rest_definitions):
        names = get_names(cur_definition)
        if len(names) == 0:
            return cur_definition
        section_level = 0
        for future_definition in rest_definitions:
            if section_level < 0:
                break
            if SECTION_BEGIN_REG.match(future_definition['statement']):
                section_level += 1
            elif SECTION_END_REG.match(future_definition['statement']):
                section_level -= 1
            elif any(re_search(r"(?<![\w'])%s(?![\w'])" % re.escape(name), future_definition['statement'])
                     for name in names):
                return cur_definition
        # we didn't find the name, so we can safely remove it
        return None

    return transformer


def try_remove_non_instance_definitions(definitions, output_file_name, **kwargs):
    def get_names(definition):
        if INSTANCE_REG.search(definition['statements'][0]):
            return tuple()
        elif CANONICAL_STRUCTURE_REG.search(definition['statements'][0]):
            return tuple()
        else:
            return definition.get('terms_defined', tuple())
    return try_transform_reversed(definitions, output_file_name,
                                  try_remove_if_name_not_found_in_transformer(get_names, **kwargs),
                                  noun_description='Non-instance definition removal',
                                  verb_description='remove non-instance definitions',
                                  **kwargs)

def try_remove_definitions(definitions, output_file_name, **kwargs):
    return try_transform_reversed(definitions, output_file_name,
                                  try_remove_if_name_not_found_in_transformer(lambda definition: definition.get('terms_defined', tuple()), **kwargs),
                                  noun_description='Definition removal',
                                  verb_description='remove definitions',
                                  **kwargs)

def try_remove_each_definition(definitions, output_file_name, **kwargs):
    return try_transform_each(definitions, output_file_name,
                              try_remove_if_name_not_found_in_transformer(lambda definition: definition.get('terms_defined', tuple()), **kwargs),
                              noun_description='Definition removal',
                              verb_description='remove definitions',
                              **kwargs)

def try_remove_each_and_every_line(definitions, output_file_name, **kwargs):
    return try_transform_each(definitions, output_file_name,
                              (lambda cur_definition, rest_definitions: False),
                              noun_description='Line removal',
                              verb_description='remove lines',
                              **kwargs)

ABORT_REG = re.compile(r'\sAbort\s*\.\s*$')
def try_remove_aborted(definitions, output_file_name, **kwargs):
    return try_transform_reversed(definitions, output_file_name,
                                  (lambda definition, rest:
                                       None if ABORT_REG.search(definition['statement']) else definition),
                                  noun_description='Aborted removal',
                                  verb_description='remove Aborts',
                                  **kwargs)

LTAC_REG = re.compile(r'^\s*(?:Local\s+|Global\s+)?Ltac\s+([^\s]+)', flags=re.MULTILINE)
def try_remove_ltac(definitions, output_file_name, **kwargs):
    return try_transform_reversed(definitions, output_file_name,
                                  try_remove_if_name_not_found_in_transformer(lambda definition: LTAC_REG.findall(definition['statement'].replace(':', '\
 : ')),
                                                                              **kwargs),
                                  noun_description='Ltac removal',
                                  verb_description='remove Ltac',
                                  **kwargs)

DEFINITION_ISH = r'Variables|Variable|Hypotheses|Hypothesis|Parameters|Parameter|Axioms|Axiom|Conjectures|Conjecture'
HINT_REG = re.compile(r'^\s*' +
                      r'(?:Local\s+|Global\s+|Polymorphic\s+|Monomorphic\s+)*' +
                      r'(?:' +
                      r'Definition|Fixpoint|Record|Inductive' +
                      r'|Coinductive|CoFixpoint' +
                      r'|Set\s+Universe\s+Polymorphism' +
                      r'|Unet\s+Universe\s+Polymorphism' +
                      r'|' + DEFINITION_ISH +
                      r')\.?(?:\s+|$)')
def try_remove_hints(definitions, output_file_name, **kwargs):
    return try_transform_each(definitions, output_file_name,
                              (lambda definition, rest:
                                   (None
                                    if len(definition['statements']) == 1 and \
                                        not HINT_REG.match(definition['statement'])
                                    else definition)),
                              noun_description='Hint removal',
                              verb_description='remove hints',
                              **kwargs)

VARIABLE_REG = re.compile(r'^\s*' +
                          r'(?:Local\s+|Global\s+|Polymorphic\s+|Monomorphic\s+)*' +
                          r'(?:' + DEFINITION_ISH + r')\s+' +
                          r'([^\.:]+)',
                          flags=re.MULTILINE)
def try_remove_variables(definitions, output_file_name, **kwargs):
    def get_names(definition):
        terms = VARIABLE_REG.findall(definition['statement'])
        return [i for i in sorted(set(j
                                      for term in terms
                                      for j in term.split(' ')))]

    return try_transform_reversed(definitions, output_file_name,
                                  try_remove_if_name_not_found_in_section_transformer(get_names, **kwargs),
                                  noun_description='Variable removal',
                                  verb_description='remove variables',
                                  **kwargs)


CONTEXT_REG = re.compile(r'^\s*' +
                         r'(?:Local\s+|Global\s+|Polymorphic\s+|Monomorphic\s+)*' +
                         r'Context\s*`\s*[\({]\s*([^:\s]+)\s*:',
                         flags=re.MULTILINE)
def try_remove_contexts(definitions, output_file_name, **kwargs):
    return try_transform_reversed(definitions, output_file_name,
                                  try_remove_if_name_not_found_in_section_transformer(lambda definition: CONTEXT_REG.findall(definition['statement'].replace(':', ' : ')), **kwargs),
                                  noun_description='Context removal',
                                  verb_description='remove Contexts',
                                  **kwargs)


def try_admit_abstracts(definitions, output_file_name, **kwargs):
    def do_call(method, definitions, agressive):
        return method(definitions, output_file_name,
                      (lambda definition, rest_definitions:
                           transform_abstract_to_admit(definition, rest_definitions, agressive=agressive, verbose=kwargs['verbose'], log=kwargs['log'])),
                      noun_description='Admitting [abstract ...]',
                      verb_description='[abstract ...] admits',
                      **kwargs)

    old_definitions = join_definitions(definitions)
    # for comparison, to see if things have changed first, try to do
    # everything at once; python cycles are assumed to be cheap in
    # comparison to coq cycles
    definitions = do_call(try_transform_reversed, definitions, True)
    new_definitions = join_definitions(definitions)
    if new_definitions != old_definitions:
        if kwargs['verbose'] >= 3: kwargs['log']('Success with [abstract ...] admits on try_transform_reversed, agressive: True, definitions:\n%s'
                             % new_definitions)
        return definitions

    # try the other options, each less agressive than the last
    definitions = do_call(try_transform_reversed, definitions, False)
    new_definitions = join_definitions(definitions)
    if new_definitions != old_definitions:
        if kwargs['verbose'] >= 3: kwargs['log']('Success with [abstract ...] admits on try_transform_reversed, agressive: False, definitions:\n%s'
                             % new_definitions)
        return definitions

    definitions = do_call(try_transform_each, definitions, True)
    new_definitions = join_definitions(definitions)
    if new_definitions != old_definitions:
        if kwargs['verbose'] >= 3: kwargs['log']('Success with [abstract ...] admits on try_transform_each, agressive: True, definitions:\n%s'
                             % new_definitions)
        return definitions

    definitions = do_call(try_transform_each, definitions, False)
    new_definitions = join_definitions(definitions)
    if new_definitions != old_definitions:
        if kwargs['verbose'] >= 3: kwargs['log']('Success with [abstract ...] admits on try_transform_each, agressive: False, definitions:\n%s'
                             % new_definitions)
    else:
        if kwargs['verbose'] >= 3: kwargs['log']('Failure with [abstract ...] admits.')
    return definitions


def try_admit_matching_definitions(definitions, output_file_name, matcher, **kwargs):
    def transformer(cur_definition, rest_definitions):
        if len(cur_definition['statements']) > 2 and matcher(cur_definition):
            statements = (cur_definition['statements'][0], 'admit.', 'Defined.')
            return {'statements':statements,
                    'statement':'\n'.join(statements),
                    'terms_defined':cur_definition['terms_defined']}
        else:
            return cur_definition

    def do_call(method, definitions):
        return method(definitions, output_file_name,
                      transformer,
                      **kwargs)

    old_definitions = join_definitions(definitions) # for comparison,
    # to see if things have changed first, try to do everything at
    # once; python cycles are assumed to be cheap in comparison to coq
    # cycles
    definitions = do_call(try_transform_reversed, definitions)
    new_definitions = join_definitions(definitions)
    if new_definitions == old_definitions:
        # we failed to do everything at once, try the simple thing and
        # try to admit each individually
        if kwargs['verbose'] >= 1: kwargs['log']('Failed to do everything at once; trying one at a time.')
        definitions = do_call(try_transform_each, definitions)
    new_definitions = join_definitions(definitions)
    if new_definitions == old_definitions:
        if kwargs['verbose'] >= 1: kwargs['log']('No successful changes.')
    else:
        if kwargs['verbose'] >= 1: kwargs['log']('Success!')
    return definitions

def try_admit_qeds(definitions, output_file_name, **kwargs):
    QED_REG = re.compile(r"(?<![\w'])Qed\s*\.\s*$", flags=re.MULTILINE)
    return try_admit_matching_definitions(definitions, output_file_name,
                                          (lambda definition: QED_REG.search(definition['statement'])),
                                          noun_description='Admitting Qeds',
                                          verb_description='admit Qeds',
                                          **kwargs)

def try_admit_lemmas(definitions, output_file_name, **kwargs):
    LEMMA_REG = re.compile(r'^\s*' +
                           r'(?:Local\s+|Global\s+|Polymorphic\s+|Monomorphic\s+)*' +
                           r'(?:Lemma|Remark|Fact|Corollary|Proposition)\s*', flags=re.MULTILINE)
    return try_admit_matching_definitions(definitions, output_file_name,
                                          (lambda definition: LEMMA_REG.search(definition['statement'])),
                                          noun_description='Admitting lemmas',
                                          verb_description='admit lemmas',
                                          **kwargs)

def try_admit_definitions(definitions, output_file_name, **kwargs):
    return try_admit_matching_definitions(definitions, output_file_name,
                                          (lambda definition: True),
                                          noun_description='Admitting definitions',
                                          verb_description='admit definitions',
                                          **kwargs)


def try_split_imports(definitions, output_file_name, **kwargs):
    def transformer(cur_definition, rest_definitions):
        if (len(cur_definition['statements']) > 1
            or any(ch in cur_definition['statement'] for ch in '*()')
            or cur_definition['statement'].strip()[-1] != '.'
            or cur_definition['statement'].strip().replace('\n', ' ').split(' ')[0] not in ('Import', 'Export')):
            return cur_definition
        else:
            terms = [i for i in cur_definition['statement'].strip().replace('\n', ' ')[:-1].split(' ') if i != '']
            import_or_export, terms = terms[0], terms[1:]
            pat = import_or_export + ' %s.'
            rtn_part = dict(cur_definition)
            rtn = []
            for term in terms:
                rtn_part['statement'] = pat % term
                rtn_part['statements'] = (pat % term,)
                rtn.append(dict(rtn_part))
            return tuple(rtn)
    return try_transform_each(definitions, output_file_name,
                              transformer,
                              noun_description='Import/Export splitting',
                              verb_description='split Imports/Exports',
                              **kwargs)

def try_split_oneline_definitions(definitions, output_file_name, **kwargs):
    def update_paren(in_string, paren_count, new_string):
        for ch in new_string:
            if in_string:
                if ch == '"': in_string = False
            else:
                if ch == '"':
                    in_string = True
                elif ch == '(':
                    paren_count += 1
                elif ch == ')':
                    paren_count -= 1
        return (in_string, paren_count)

    def transformer(cur_definition, rest_definitions):
        if (len(cur_definition['statements']) > 1
            or cur_definition['statement'].strip()[-1] != '.'
            or ':=' not in cur_definition['statement']
            or len(cur_definition['terms_defined']) != 1):
            return cur_definition
        else:
            terms = cur_definition['statement'].strip()[:-1].split(':=')
            pre_statement = terms[0]
            in_string, paren_count = update_paren(False, 0, pre_statement)
            for i, term in list(enumerate(terms))[1:]:
                if not in_string and paren_count == 0:
                    rtn_part = dict(cur_definition)
                    rtn_part['statements'] = (pre_statement.rstrip() + '.',
                                              'exact (%s).' % ':='.join(terms[i:]).strip(),
                                              'Defined.')
                    rtn_part['statement'] = ' '.join(rtn_part['statements'])
                    return rtn_part
                else:
                    in_string, paren_count = update_paren(in_string, paren_count, term)
                    pre_statement = ':=' + term
            return cur_definition
    return try_transform_each(definitions, output_file_name,
                              transformer,
                              noun_description='One-line definition splitting',
                              verb_description='split one-line definitions',
                              **kwargs)

MODULE_REG = re.compile(r'^(\s*Module)(\s+[^\s\.]+\s*\.\s*)$')
def try_export_modules(definitions, output_file_name, **kwargs):
    def transformer(cur_definition, rest_definitions):
        if (len(cur_definition['statements']) > 1 or
            not MODULE_REG.match(cur_definition['statement'])):
            return cur_definition
        else:
            new_statement = MODULE_REG.sub(r'\1 Export\2', cur_definition['statement'])
            rtn = dict(cur_definition)
            rtn['statement'] = new_statement
            rtn['statements'] = (new_statement, )
            return rtn
    return try_transform_each(definitions, output_file_name,
                              transformer,
                              noun_description='Module exportation',
                              verb_description='export modules',
                              **kwargs)







def try_strip_comments(output_file_name, **kwargs):
    contents = read_from_file(output_file_name)
    old_contents = contents
    new_contents = strip_comments(contents)

    check_change_and_write_to_file(old_contents, new_contents, output_file_name,
                                   unchanged_message='No strippable comments.',
                                   success_message='Succeeded in stripping comments.',
                                   failure_description='strip comments',
                                   changed_descruption='Stripped comments file',
                                   **kwargs)



def try_strip_newlines(output_file_name, max_consecutive_newlines, strip_trailing_space, **kwargs):
    contents = read_from_file(output_file_name)
    old_contents = contents
    if strip_trailing_space:
        contents = '\n'.join(map(str.rstrip, contents.split('\n')))
    new_contents = strip_newlines(contents, max_consecutive_newlines)

    check_change_and_write_to_file(old_contents, new_contents, output_file_name,
                                   unchanged_message='No strippable newlines or spaces.',
                                   success_message='Succeeded in stripping newlines and spaces.',
                                   failure_description='strip newlines and spaces',
                                   changed_descruption='Stripped file',
                                   **kwargs)


def try_strip_extra_lines(output_file_name, line_num, **kwargs):
    contents = read_from_file(output_file_name)
    statements = split_coq_file_contents(contents)
    cur_line_num = 0
    new_statements = statements
    for statement_num, statement in enumerate(statements):
        cur_line_num += statement.count('\n') + 1 # +1 for the extra newline between each statement
        if cur_line_num >= line_num:
            new_statements = statements[:statement_num + 1]
            break

    if check_change_and_write_to_file('\n'.join(statements), '\n'.join(new_statements), output_file_name,
                                      unchanged_message='No lines to trim.',
                                      success_message=('Trimming successful.  We removed all lines after %d; the error was on line %d.' % (cur_line_num, line_num)),
                                      failure_description='trim file',
                                      changed_descruption='Trimmed file',
                                      **kwargs):
        if kwargs['verbose'] >= 3: kwargs['log']('Trimmed file:\n%s' % read_from_file(output_file_name))



EMPTY_SECTION_REG = re.compile(r'(\.\s+|^\s*)(?:Section|Module\s+Export|Module)\s+([^\.]+)\.' +
                               r'(?:\s' +
                               r'|Global\s|Local\s'
                               r'|Set\s+Universe\s+Polymorphism\s*\.\s' +
                               r'|Unset\s+Universe\s+Polymorphism\s*\.\s)+End\s+([^\.]+)\.(\s+|$)', flags=re.MULTILINE)
def try_strip_empty_sections(output_file_name, **kwargs):
    contents = read_from_file(output_file_name)
    old_contents = contents
    new_contents = EMPTY_SECTION_REG.sub(r'\1', old_contents)
    while new_contents != old_contents:
        old_contents, new_contents = new_contents, EMPTY_SECTION_REG.sub(r'\1', new_contents)

    check_change_and_write_to_file(contents, new_contents, output_file_name,
                                   unchanged_message='No empty sections to remove.',
                                   success_message='Empty section removal successful.',
                                   failure_description='remove empty sections',
                                   changed_descruption='Trimmed file',
                                   **kwargs)


def add_admit_tactic(contents):
    tac_code = r"""Module Export AdmitTactic.
Module Import LocalFalse.
Inductive False := .
End LocalFalse.
Axiom proof_admitted : False.
Tactic Notation "admit" := case proof_admitted.
End AdmitTactic.
"""
    return '%s%s' % (tac_code, re.sub(re.escape(tac_code) + r'\n*', '', contents))


def process_maybe_list(ls, log=DEFAULT_LOG, verbose=DEFAULT_VERBOSITY):
    if ls is None: return tuple()
    if isinstance(ls, str): return tuple([ls])
    if isinstance(ls, tuple): return ls
    if isinstance(ls, list): return tuple(ls)
    if verbose >= 1: log("Unknown type '%s' of list '%s'" % (str(type(ls)), repr(ls)))
    return tuple(ls)

def default_on_fatal(message):
    if message is not None: print(message)
    sys.exit(1)

def minimize_file(output_file_name, die=default_on_fatal, old_header=None, **env):
    """The workhorse of bug minimization.  The only thing it doesn't handle is inlining [Require]s and other preprocesing"""
    contents = read_from_file(output_file_name)

    coqc_version = get_coqc_version(env['coqc'], **env)
    coqtop_version = get_coqtop_version(env['coqtop'], **env)
    coqc_help = get_coqc_help(env['coqc'], **env)
    if old_header is None: old_header = get_old_header(contents, env['dynamic_header'])
    env['header_dict'] = {'original_line_count':0,
                          'old_header':old_header,
                          'coqc_version':coqc_version,
                          'coqtop_version':coqtop_version}


    if not check_change_and_write_to_file('', contents, output_file_name,
                                          unchanged_message='Invalid empty file!', success_message='Sanity check passed.',
                                          failure_description='validate all coq runs', changed_description='The',
                                          **env):
        return die('Fatal error: Sanity check failed.')

    if env['max_consecutive_newlines'] >= 0 or env['strip_trailing_space']:
        if env['verbose'] >= 1: env['log']('\nNow, I will attempt to strip repeated newlines and trailing spaces from this file...')
        try_strip_newlines(output_file_name, **env)

    contents = read_from_file(output_file_name)
    original_line_count = len(contents.split('\n'))
    env['header_dict']['original_line_count'] = original_line_count

    if env['verbose'] >= 1: env['log']('\nNow, I will attempt to strip the comments from this file...')
    try_strip_comments(output_file_name, **env)



    contents = read_from_file(output_file_name)
    if env['verbose'] >= 1:
        env['log']('\nIn order to efficiently manipulate the file, I have to break it into statements.  I will attempt to do this by matching on periods.')
        strings = re.findall(r'"[^"\n\r]+"', contents)
        bad_strings = [i for i in strings if re.search(r'(?<=[^\.]\.\.\.)\s|(?<=[^\.]\.)\s', i)]
        if bad_strings:
            env['log']('If you have periods in strings, and these periods are essential to generating the error, then this process will fail.  Consider replacing the string with some hack to get around having a period and then a space, like ["a. b"%string] with [("a." ++ " b")%string].')
            env['log']('You have the following strings with periods in them:\n%s' % '\n'.join(bad_strings))
    statements = split_coq_file_contents(contents)
    if not check_change_and_write_to_file('', '\n'.join(statements), output_file_name,
                                          unchanged_message='Invalid empty file!',
                                          success_message='Splitting successful.',
                                          failure_description='split file to statements',
                                          changed_description='Split',
                                          **env):
        if env['verbose'] >= 1: env['log']('I will not be able to proceed.')
        if env['verbose'] >= 2: env['log']('re.search(' + repr(env['error_reg_string']) + ', <output above>)')
        return die(None)

    if env['verbose'] >= 1: env['log']('\nI will now attempt to remove any lines after the line which generates the error.')
    output, cmds = diagnose_error.get_coq_output(env['coqc'], env['coqc_args'], '\n'.join(statements), env['timeout'], is_coqtop=env['coqc_is_coqtop'], verbose_base=2, **env)
    line_num = diagnose_error.get_error_line_number(output, env['error_reg_string'])
    try_strip_extra_lines(output_file_name, line_num, **env)


    if env['verbose'] >= 1: env['log']('\nIn order to efficiently manipulate the file, I have to break it into definitions.  I will now attempt to do this.')
    contents = read_from_file(output_file_name)
    statements = split_coq_file_contents(contents)
    if env['verbose'] >= 3: env['log']('I am using the following file: %s' % '\n'.join(statements))
    definitions = split_statements_to_definitions(statements, **env)
    if not check_change_and_write_to_file('', join_definitions(definitions), output_file_name,
                                          unchanged_message='Invalid empty file!',
                                          success_message='Splitting to definitions successful.',
                                          failure_description='split file to definitions',
                                          changed_description='Split',
                                          **env):
        if env['verbose'] >= 1: env['log']('I will not be able to proceed.')
        if env['verbose'] >= 2: env['log']('re.search(' + repr(env['error_reg_string']) + ', <output above>)')
        return die(None)

    recursive_tasks = (('remove goals ending in [Abort.]', try_remove_aborted),
                       ('remove unused Ltacs', try_remove_ltac),
                       ('remove unused definitions', try_remove_definitions),
                       ('remove unused non-instance, non-canonical structure definitions', try_remove_non_instance_definitions),
                       ('remove unused variables', try_remove_variables),
                       ('remove unused contexts', try_remove_contexts))

    tasks = recursive_tasks
    if admit_opaque:
        tasks += ((('replace Qeds with Admitteds', try_admit_qeds),) +
                  # we've probably just removed a lot, so try to remove definitions again
                  recursive_tasks +
                  (('admit [abstract ...]s', try_admit_abstracts),) +
                  # we've probably just removed a lot, so try to remove definitions again
                  recursive_tasks)

    if not aggressive:
        tasks += (('remove unused definitions, one at a time', try_remove_each_definition),)

    if admit_transparent:
        tasks += (('admit lemmas', try_admit_lemmas),
                  ('admit definitions', try_admit_definitions))

    if not aggressive:
        tasks += (('remove hints', try_remove_hints),)

    tasks += (('export modules', try_export_modules),
              ('split imports and exports', try_split_imports),
              ('split := definitions', try_split_oneline_definitions))

    if aggressive:
        tasks += ((('remove all lines, one at a time', try_remove_each_and_every_line),) +
                  # we've probably just removed a lot, so try to remove definitions again
                  recursive_tasks)


    old_definitions = ''
    while old_definitions != join_definitions(definitions):
        old_definitions = join_definitions(definitions)
        if env['verbose'] >= 2: env['log']('Definitions:')
        if env['verbose'] >= 2: env['log'](definitions)

        for description, task in tasks:
            if env['verbose'] >= 1: env['log']('\nI will now attempt to %s' % description)
            definitions = task(definitions, output_file_name, **env)


    if env['verbose'] >= 1: env['log']('\nI will now attempt to remove empty sections')
    try_strip_empty_sections(output_file_name, **env)

    if env['max_consecutive_newlines'] >= 0 or env['strip_trailing_space']:
        if env['verbose'] >= 1: env['log']('\nNow, I will attempt to strip repeated newlines and trailing spaces from this file...')
        try_strip_newlines(output_file_name, **env)

    return True

HELP_REG = re.compile(r'^  ([^\n]*?)(?:\t|  )', re.MULTILINE)

def all_tags(coqc_help):
    return HELP_REG.findall(coqc_help)

def get_single_tags(coqc_help):
    return tuple(i for i in all_tags(coqc_help) if ' ' not in i)

def get_multiple_tags(coqc_help):
    return dict((i.split(' ')[0], len(i.split(' ')))
                for i in all_tags(coqc_help)
                if ' ' in i)

def topname_of_filename(file_name):
    return os.path.splitext(os.path.basename(file_name))[0]

def args_to_bindings(args, coqc_help, file_name):
    args = list(args)
    bindings = []
    single_tags = get_single_tags(coqc_help)
    multiple_tags = get_multiple_tags(coqc_help)
    while len(args) > 0:
        if args[0] in multiple_tags.keys() and len(args) >= multiple_tags[args[0]]:
            cur_binding, args = tuple(args[:multiple_tags[args[0]]]), args[multiple_tags[args[0]]:]
            if cur_binding not in bindings:
                bindings.append(cur_binding)
        else:
            cur = tuple([args.pop(0)])
            if cur[0] not in single_tags or cur not in bindings:
                bindings.append(cur)
    if '-top' not in [i[0] for i in bindings] and '-top' in multiple_tags.keys():
        bindings.append(('-top', topname_of_filename(file_name)))
    return bindings

def deduplicate_trailing_dir_bindings(args, coqc_help, file_name, coq_accepts_top):
    bindings = args_to_bindings(args, coqc_help, file_name)
    ret = []
    for binding in bindings:
        if coq_accepts_top or binding[0] != '-top':
            ret.extend(binding)
    return tuple(ret)

def has_dir_binding(args, coqc_help, file_name):
    bindings = args_to_bindings(args, coqc_help, file_name)
    return any(i[0] in ('-R', '-Q') for i in bindings)

if __name__ == '__main__':
    try:
        args = parser.parse_args()
    except argparse.ArgumentError as exc:
        if exc.message == 'expected one argument':
            exc.reraise('\nNote that argparse does not accept arguments with leading dashes.\nTry --foo=bar or --foo " -bar", if this was your intent.\nSee Python issue 9334.')
        else:
            exc.reraise()
    def prepend_coqbin(prog):
        if args.coqbin != '':
            return os.path.join(args.coqbin, prog)
        else:
            return prog
    bug_file_name = args.bug_file.name
    output_file_name = args.output_file
    log = make_logger(args.log_files)
    admit_opaque = args.admit_opaque
    aggressive = args.aggressive
    admit_transparent = args.admit_transparent
    if args.verbose is None: args.verbose = DEFAULT_VERBOSITY
    if args.quiet is None: args.quiet = 0
    verbose = args.verbose - args.quiet
    env = {
        'verbose': verbose,
        'fast_merge_imports': args.fast_merge_imports,
        'log': log,
        'coqc': prepend_coqbin(args.coqc),
        'coqtop': prepend_coqbin(args.coqtop),
        'as_modules': args.wrap_modules,
        'max_consecutive_newlines': args.max_consecutive_newlines,
        'header': args.header,
        'dynamic_header': args.dynamic_header,
        'strip_trailing_space': args.strip_trailing_space,
        'timeout': args.timeout,
        'absolutize': args.absolutize,
        'minimize_before_inlining': args.minimize_before_inlining,
        'save_typeclasses': args.save_typeclasses,
        'coqc_args': tuple(i.strip()
                           for i in (list(process_maybe_list(args.nonpassing_coqc_args, log=log, verbose=verbose))
                                     + list(process_maybe_list(args.coq_args, log=log, verbose=verbose)))),
        'coqtop_args': tuple(i.strip()
                             for i in (list(process_maybe_list(args.coqtop_args, log=log, verbose=verbose))
                                       + list(process_maybe_list(args.nonpassing_coqc_args, log=log, verbose=verbose))
                                       + list(process_maybe_list(args.coq_args, log=log, verbose=verbose)))),
        'coq_makefile': args.coq_makefile,
        'passing_coqc_args': tuple(i.strip()
                                   for i in (list(process_maybe_list(args.passing_coqc_args, log=log, verbose=verbose))
                                             + list(process_maybe_list(args.coq_args, log=log, verbose=verbose)))),
        'passing_coqc' : (prepend_coqbin(args.passing_coqc)
                          if args.passing_coqc != ''
                          else (prepend_coqbin(args.coqc)
                                if args.passing_coqc_args is not None
                                else None)),
        'walk_tree': args.walk_tree,
        'temp_file_name': args.temp_file,
        'coqc_is_coqtop': args.coqc_is_coqtop,
        'passing_coqc_is_coqtop': args.passing_coqc_is_coqtop
        }

    if bug_file_name[-2:] != '.v':
        print('\nError: BUGGY_FILE must end in .v (value: %s)' % bug_file_name)
        #log('\nError: BUGGY_FILE must end in .v (value: %s)' % bug_file_name)
        sys.exit(1)
    if output_file_name[-2:] != '.v':
        print('\nError: OUT_FILE must end in .v (value: %s)' % output_file_name)
        #log('\nError: OUT_FILE must end in .v (value: %s)' % output_file_name)
        sys.exit(1)
    if os.path.exists(output_file_name):
        print('\nWarning: OUT_FILE (%s) already exists.  Would you like to overwrite?' % output_file_name)
        #log('\nWarning: OUT_FILE (%s) already exists.  Would you like to overwrite?' % output_file_name)
        if not yes_no_prompt():
            sys.exit(1)

    env['remove_temp_file'] = False
    if env['temp_file_name'] == '':
        temp_file = tempfile.NamedTemporaryFile(suffix='.v', dir='.', delete=False)
        env['temp_file_name'] = temp_file.name
        temp_file.close()
        env['remove_temp_file'] = True

    if env['coqc_is_coqtop']:
        if env['coqc'] == 'coqc': env['coqc'] = env['coqtop']
        env['make_coqc'] = os.path.join(SCRIPT_DIRECTORY, 'coqtop-as-coqc.sh') + ' ' + env['coqc']
    if env['passing_coqc_is_coqtop']:
        if env['passing_coqc'] == 'coqc': env['passing_coqc'] = env['coqtop']

    coqc_help = get_coqc_help(env['coqc'], **env)

    if has_dir_binding(env['coqc_args'], coqc_help=coqc_help, file_name=bug_file_name):
        update_env_with_libnames(env, args, default=tuple([]))
    else:
        update_env_with_libnames(env, args)

    try:

        if env['temp_file_name'][-2:] != '.v':
            print('\nError: TEMP_FILE must end in .v (value: %s)' % env['temp_file_name'])
            log('\nError: TEMP_FILE must end in .v (value: %s)' % env['temp_file_name'])
            sys.exit(1)

        if env['minimize_before_inlining']:
            if env['verbose'] >= 1: log('\nFirst, I will attempt to factor out all of the [Require]s %s, and store the result in %s...' % (bug_file_name, output_file_name))
            inlined_contents = normalize_requires(bug_file_name, **env)
            args.bug_file.close()
            inlined_contents = add_admit_tactic(inlined_contents)
            write_to_file(output_file_name, inlined_contents)
        else:
            if env['verbose'] >= 1: log('\nFirst, I will attempt to inline all of the inputs in %s, and store the result in %s...' % (bug_file_name, output_file_name))
            inlined_contents = include_imports(bug_file_name, **env)
            args.bug_file.close()
            if inlined_contents:
                inlined_contents = add_admit_tactic(inlined_contents)
                if env['verbose'] >= 1: log('Stripping trailing ends')
                while re.search(r'End [^ \.]*\.\s*$', inlined_contents):
                    inlined_contents = re.sub(r'End [^ \.]*\.\s*$', '', inlined_contents)
                write_to_file(output_file_name, inlined_contents)
            else:
                if env['verbose'] >= 1: log('Failed to inline inputs.')
                sys.exit(1)

        extra_args = get_coq_prog_args(inlined_contents)
        for args_name, coq_prog in (('coqc_args', env['coqc']), ('coqtop_args', env['coqtop']), ('passing_coqc_args', env['passing_coqc'] if env['passing_coqc'] else env['coqc'])):
            env[args_name] = tuple(list(env[args_name]) + list(extra_args))
            for dirname, libname in env['libnames']:
                env[args_name] = tuple(list(env[args_name]) + ['-R', dirname, libname])
            for dirname, libname in env['non_recursive_libnames']:
                env[args_name] = tuple(list(env[args_name]) + ['-Q', dirname, libname])
            env[args_name] = deduplicate_trailing_dir_bindings(env[args_name], coqc_help=coqc_help, file_name=bug_file_name, coq_accepts_top=get_coq_accepts_top(coq_prog))

        if env['verbose'] >= 1: log('\nNow, I will attempt to coq the file, and find the error...')
        env['error_reg_string'] = get_error_reg_string(output_file_name, **env)

        # initial run before we (potentially) do fancy things with the requires
        minimize_file(output_file_name, **env)

        if env['minimize_before_inlining']: # if we've not already inlined everything
            # so long as we keep changing, we will pull all the
            # requires to the top, then try to replace them in reverse
            # order.  As soon as we succeed, we reset the list
            last_output = ''
            clear_libimport_cache(lib_of_filename(output_file_name, libnames=tuple(env['libnames']), non_recursive_libnames=tuple(env['non_recursive_libnames'])))
            old_header = get_old_header(get_file(output_file_name, **env), env['dynamic_header'])
            cur_output = add_admit_tactic(normalize_requires(output_file_name, **env)).strip() + '\n'
            # keep a list of libraries we've already tried to inline, and don't try them again
            libname_blacklist = []
            while cur_output != last_output:
                last_output = cur_output
                requires = recursively_get_requires_from_file(output_file_name, update_globs=True, **env)
                if os.path.exists(output_file_name + '.require-bak'):
                    os.remove(output_file_name + '.require-bak')
                write_to_file(output_file_name, cur_output, do_backup=True, backup_ext='.require-bak')

                try:
                    for req_module in reversed(requires):
                        if req_module in libname_blacklist:
                            continue
                        else:
                            libname_blacklist.append(req_module)
                        rep = '\nRequire %s.\n' % req_module
                        if rep not in '\n' + cur_output:
                            if env['verbose'] >= 1: log('\nWarning: I cannot find Require %s.' % req_module)
                            if env['verbose'] >= 3: log('in contents:\n' + cur_output)
                            continue
                        try:
                            test_output = ('\n' + cur_output).replace(rep, '\n' + get_required_contents(req_module, **env).strip() + '\n').strip() + '\n'
                        except IOError:
                            if env['verbose'] >= 1: log('\nWarning: Cannot inline %s' % req_module)
                            continue
                        write_to_file(output_file_name, test_output)
                        diagnose_error.reset_timeout()
                        if minimize_file(output_file_name, die=(lambda x: False), old_header=old_header, **env):
                            if os.path.exists(output_file_name + '.require-bak'):
                                os.remove(output_file_name + '.require-bak')
                            break
                        else: # just in case this is the last iteration
                            write_to_file(output_file_name, cur_output)
                            if os.path.exists(output_file_name + '.require-bak'):
                                os.remove(output_file_name + '.require-bak')

                except BaseException:
                    restore_file(output_file_name, backup_ext='.require-bak', backup_backup_ext=None)
                    raise

                clear_libimport_cache(lib_of_filename(output_file_name, libnames=tuple(env['libnames']), non_recursive_libnames=tuple(env['non_recursive_libnames'])))
                old_header = get_old_header(get_file(output_file_name, **env), env['dynamic_header'])
                cur_output = add_admit_tactic(normalize_requires(output_file_name, update_globs=True, **env)).strip() + '\n'

            # and we make one final run, or, in case there are no requires, one run
            minimize_file(output_file_name, old_header=old_header, **env)

    finally:
        if env['remove_temp_file']:
            clean_v_file(env['temp_file_name'])
        if os.path.exists(output_file_name + '.require-bak'):
            os.remove(output_file_name + '.require-bak')
