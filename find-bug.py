#!/usr/bin/env python
import argparse, tempfile, sys, os, re
from OrderedSet import OrderedSet
from replace_imports import include_imports
from strip_comments import strip_comments
from strip_newlines import strip_newlines
from split_file import split_coq_file_contents
from split_definitions import split_statements_to_definitions, join_definitions
from admit_abstract import transform_abstract_to_admit
from memoize import memoize
import diagnose_error

# {Windows,Python,coqtop} is terrible; we fail to write to (or read
# from?) coqtop.  But we can wrap it in a batch scrip, and it works
# fine.
SCRIPT_DIRECTORY = os.path.dirname(os.path.realpath(__file__))
DEFAULT_COQTOP = 'coqtop' if os.name != 'nt' else os.path.join(SCRIPT_DIRECTORY, 'coqtop.bat')

parser = argparse.ArgumentParser(description='Attempt to create a small file which reproduces a bug found in a large development.')
parser.add_argument('--directory', '-d', metavar='DIRECTORY', dest='directory', type=str, default='.',
                    help='The directory in which to execute')
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
parser.add_argument('--header', dest='header', nargs='?', type=str,
                    default='(* File reduced by coq-bug-finder from %(old_header)s, then from %(original_line_count)d lines to %(final_line_count)d lines *)',
                    help=("A line to be placed at the top of the " +
                          "output file, followed by a newline.  The " +
                          "variables original_line_count and " +
                          "final_line_count will be available for " +
                          "substitution.  The default is " +
                          "`(* File reduced by coq-bug-finder from %%(old_header)s, then from %%(original_line_count)d lines to %%(final_line_count)d lines *)'"))
parser.add_argument('--no-strip-trailing-space', dest='strip_trailing_space',
                    action='store_const', const=False, default=True,
                    help=("Don't strip trailing spaces.  By default, " +
                          "trailing spaces on each line are removed."))
parser.add_argument('--timeout', dest='timeout', metavar='SECONDS', type=int, default=-1,
                    help=("Use a timeout; make sure Coq is " +
                          "killed after running for this many seconds. " +
                          "If 0, there is no timeout.  If negative, then " +
                          "twice the initial run of the script is used.\n\n" +
                          "Default: -1"))
parser.add_argument('--coqc', metavar='COQC', dest='coqc', type=str, default='coqc',
                    help='The path to the coqc program.')
parser.add_argument('--coqtop', metavar='COQTOP', dest='coqtop', type=str, default=DEFAULT_COQTOP,
                    help=('The path to the coqtop program (default: %s).' % DEFAULT_COQTOP))
parser.add_argument('--coqc-args', metavar='ARG', dest='coqc_args', type=str, nargs='?',
                    help='Arguments to pass to coqc.')
parser.add_argument('--coqtop-args', metavar='ARG', dest='coqtop_args', type=str, nargs='?',
                    help='Arguments to pass to coqtop.')
parser.add_argument('--topname', metavar='TOPNAME', dest='topname', type=str, default='__TOP__',
                    help='The name to bind to the current directory using -R .')

def DEFAULT_LOG(text):
    print(text)

DEFAULT_VERBOSITY=1

def make_logger(log_files):
    def log(text):
        for i in log_files:
            i.write(str(text) + '\n')
            i.flush()
            if i.fileno() > 1:
                os.fsync(i.fileno())
    return log

def backup(file_name, ext='.bak'):
    if not ext:
        raise ValueError
    if os.path.exists(file_name):
        backup(file_name + ext)
        os.rename(file_name, file_name + ext)

def write_to_file(file_name, contents, do_backup=False):
    if do_backup:
        backup(file_name)
    try:
        with open(file_name, 'w', encoding='UTF-8') as f:
            f.write(contents)
    except TypeError:
        with open(file_name, 'w') as f:
            f.write(contents)

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

def get_error_reg_string(output_file_name, verbose=DEFAULT_VERBOSITY, log=DEFAULT_LOG, **kwargs):
    error_reg_string = ''
    while error_reg_string == '':
        if verbose: log('\nCoqing the file (%s)...' % output_file_name)
        contents = read_from_file(output_file_name)
        diagnose_error.reset_timeout()
        output = diagnose_error.get_coq_output(kwargs['coqc'], kwargs['coqc_args'], contents, kwargs['timeout'])
        if kwargs['timeout'] < 0:
            log('The timeout has been set to: %d' % diagnose_error.get_timeout())
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
            print("\nI think the error is '%s'.\nThe corresponding regular expression is '%s'." % (error_string, error_reg_string))
            result = ''
            while result not in ('y', 'n', 'yes', 'no'):
                result = raw_input('Is this correct? [(y)es/(n)o] ').lower().strip()
            if result in ('no', 'n'):
                error_reg_string = ''
        else:
            log('\nThe current state of the file does not have a recognizable error.')

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

def get_old_header(contents, header=''):
    if header[:2] == '(*' and header[-2:] == '*)' and '*)' not in header[2:-2]:
        pre_header = header[:header.index('%')]
        if pre_header in contents and contents.index('*)') > contents.index(pre_header):
            return contents[contents.index(pre_header)+len(pre_header):contents.index('*)')].strip()
    return 'original input'

def prepend_header(contents, header='', header_dict={}, **kwargs):
    """Fills in the variables in the header for output files"""
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
    use_header = header % header_dict
    ## de-duplicate things in a list
    ## XXX This is a hack to deal with things like "from x lines to y lines, from x lines to y lines"
    #if use_header[-3:] == ' *)':
    #    use_header = ','.join(OrderedSet(use_header[:-3].split(','))) + ' *)'
    return '%s\n%s' % (use_header, contents)

def try_transform_each(definitions, output_file_name, error_reg_string, temp_file_name, transformer, description, skip_n=1,
                       verbose=DEFAULT_VERBOSITY, log=DEFAULT_LOG, **kwargs):
    """Tries to apply transformer to each definition in definitions,
    additionally passing in the list of subsequent definitions.  If
    the returned value of the 'statement' key is not equal to the old
    value, or if the return value is a false-y value (indicating that
    we should remove the line) then we see if the error is still
    present.  If it is, we keep the change; otherwise, we discard it.
    The order in which definitions are passed in is guaranteed to be
    reverse-order.

    Returns updated definitions."""
    if verbose >= 3: log('try_transform_each')
    original_definitions = [dict(i) for i in definitions]
    # TODO(jgross): Use coqtop and [BackTo] to do incremental checking
    success = False
    i = len(definitions) - 1 - skip_n
    while i >= 0:
        old_definition = definitions[i]
        new_definition = transformer(old_definition, definitions[i + 1:])
        if not new_definition or \
                re.sub(r'\s+', ' ', old_definition['statement']) != re.sub(r'\s+', ' ', new_definition['statement']):
            if not new_definition or not new_definition['statement'].strip():
                if verbose >= 3: log('Attempting to remove %s' % repr(old_definition['statement']))
                try_definitions = definitions[:i] + definitions[i + 1:]
            else:
                if verbose >= 3: log('Attempting to transform %s into %s' % (old_definition['statement'], new_definition['statement']))
                try_definitions = definitions[:i] + [new_definition] + definitions[i + 1:]
            output = diagnose_error.get_coq_output(kwargs['coqc'], kwargs['coqc_args'], join_definitions(try_definitions), kwargs['timeout'])
            if diagnose_error.has_error(output, error_reg_string):
                if verbose >= 3: log('Change succeeded')
                success = True
                contents = prepend_header(join_definitions(try_definitions), **kwargs)
                write_to_file(output_file_name, contents)
                definitions = try_definitions
                # make a copy for saving
                save_definitions = [dict(defn) for defn in try_definitions]
            else:
                if verbose >= 3: log('Change failed.  Output:\n%s' % output)
        else:
            if verbose >= 3: log('No change to %s' % old_definition['statement'])
        i -= 1
    if success:
        if verbose >= 1 : log(description + ' successful')
        if join_definitions(save_definitions) != join_definitions(definitions):
            log('Probably fatal error: definitions != save_definitions')
        else:
            contents = prepend_header(join_definitions(definitions), **kwargs)
            write_to_file(output_file_name, contents)
        return definitions
    else:
        if verbose >= 1: log(description + ' unsuccessful.')
        return original_definitions


def try_transform_reversed(definitions, output_file_name, error_reg_string, temp_file_name, transformer, description, skip_n=1,
                           verbose=DEFAULT_VERBOSITY, log=DEFAULT_LOG, **kwargs):
    """Replaces each definition in definitions, with transformer
    applied to that definition and the subsequent (transformed)
    definitions.  If transformer returns a false-y value, the
    definition is removed.  After transforming the entire list, we see
    if the error is still present.  If it is, we keep the change;
    otherwise, we discard it.  The order in which definitions are
    passed in is guaranteed to be reverse-order.

    Returns updated definitions."""
    if verbose >= 3: log('try_transform_reversed')
    definitions = list(definitions) # clone the list of definitions
    original_definitions = list(definitions)
    if verbose >= 3: log(len(definitions))
    if verbose >= 3: log(definitions)
    for i in reversed(list(range(len(definitions) - skip_n))):
        new_definition = transformer(definitions[i], definitions[i + 1:])
        if new_definition:
            if definitions[i] != new_definition:
                if verbose >= 3: log('Transforming %s into %s' % (definitions[i]['statement'], new_definition['statement']))
            else:
                if verbose >= 3: log('No change to %s' % new_definition['statement'])
            definitions[i] = new_definition
        else:
            if verbose >= 3: log('Removing %s' % definitions[i]['statement'])
            definitions = definitions[:i] + definitions[i + 1:]
    output = diagnose_error.get_coq_output(kwargs['coqc'], kwargs['coqc_args'], join_definitions(definitions), kwargs['timeout'])
    if diagnose_error.has_error(output, error_reg_string):
        if verbose >= 1: log(description + ' successful')
        contents = prepend_header(join_definitions(definitions), **kwargs)
        write_to_file(output_file_name, contents)
        return definitions
    else:
        if verbose >= 1: log(description + ' unsuccessful.  Writing intermediate code to %s.' % temp_file_name)
        if verbose >= 3: log('The output was:\n%s' % output)
        contents = prepend_header(join_definitions(definitions), **kwargs)
        write_to_file(temp_file_name, contents)
        return original_definitions

def try_remove_if_not_matches_transformer(definition_found_in, verbose=DEFAULT_VERBOSITY, log=DEFAULT_LOG, **kwargs):
    def transformer(cur_definition, rest_definitions):
        if any(definition_found_in(cur_definition, future_definition)
               for future_definition in rest_definitions):
            if verbose >= 2: log('Definition found; found:\n%s\nin\n%s'
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


def try_remove_if_name_not_found_in_section_transformer(get_names, verbose=DEFAULT_VERBOSITY, log=DEFAULT_LOG, **kwargs):
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


INSTANCE_REG = re.compile(r"(?<![\w'])Instance\s")
CANONICAL_STRUCTURE_REG = re.compile(r"(?<![\w'])Canonical\s+Structure\s")
def try_remove_non_instance_definitions(definitions, output_file_name, error_reg_string, temp_file_name,
                                        **kwargs):
    def get_names(definition):
        if INSTANCE_REG.search(definition['statements'][0]):
            return tuple()
        elif CANONICAL_STRUCTURE_REG.search(definition['statements'][0]):
            return tuple()
        else:
            return definition.get('terms_defined', tuple())
    return try_transform_reversed(definitions, output_file_name, error_reg_string, temp_file_name,
                                  try_remove_if_name_not_found_in_transformer(get_names, **kwargs),
                                  'Non-instance definition removal',
                                  **kwargs)

def try_remove_definitions(definitions, output_file_name, error_reg_string, temp_file_name,
                           **kwargs):
    return try_transform_reversed(definitions, output_file_name, error_reg_string, temp_file_name,
                                  try_remove_if_name_not_found_in_transformer(lambda definition: definition.get('terms_defined', tuple()), **kwargs),
                                  'Definition removal',
                                  **kwargs)

def try_remove_each_definition(definitions, output_file_name, error_reg_string, temp_file_name,
                               **kwargs):
    return try_transform_each(definitions, output_file_name, error_reg_string, temp_file_name,
                              try_remove_if_name_not_found_in_transformer(lambda definition: definition.get('terms_defined', tuple()), **kwargs),
                              'Definition removal',
                              **kwargs)

def try_remove_each_and_every_line(definitions, output_file_name, error_reg_string, temp_file_name,
                               **kwargs):
    return try_transform_each(definitions, output_file_name, error_reg_string, temp_file_name,
                              (lambda cur_definition, rest_definitions: False),
                              'Line removal',
                              **kwargs)

ABORT_REG = re.compile(r'\sAbort\s*\.\s*$')
def try_remove_aborted(definitions, output_file_name, error_reg_string, temp_file_name,
                       **kwargs):
    return try_transform_reversed(definitions, output_file_name, error_reg_string, temp_file_name,
                                  (lambda definition, rest:
                                       None if ABORT_REG.search(definition['statement']) else definition),
                                  'Aborted removal',
                                  **kwargs)

LTAC_REG = re.compile(r'^\s*(?:Local\s+|Global\s+)?Ltac\s+([^\s]+)', flags=re.MULTILINE)
def try_remove_ltac(definitions, output_file_name, error_reg_string, temp_file_name,
                    **kwargs):
    return try_transform_reversed(definitions, output_file_name, error_reg_string, temp_file_name,
                                  try_remove_if_name_not_found_in_transformer(lambda definition: LTAC_REG.findall(definition['statement'].replace(':', '\
 : ')),
                                                                              **kwargs),
                                  'Ltac removal',
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
def try_remove_hints(definitions, output_file_name, error_reg_string, temp_file_name,
                     **kwargs):
    return try_transform_each(definitions, output_file_name, error_reg_string, temp_file_name,
                              (lambda definition, rest:
                                   (None
                                    if len(definition['statements']) == 1 and \
                                        not HINT_REG.match(definition['statement'])
                                    else definition)),
                              'Hint removal',
                              **kwargs)

VARIABLE_REG = re.compile(r'^\s*' +
                          r'(?:Local\s+|Global\s+|Polymorphic\s+|Monomorphic\s+)*' +
                          r'(?:' + DEFINITION_ISH + r')\s+' +
                          r'([^\.:]+)',
                          flags=re.MULTILINE)
def try_remove_variables(definitions, output_file_name, error_reg_string, temp_file_name,
                         **kwargs):
    def get_names(definition):
        terms = VARIABLE_REG.findall(definition['statement'])
        return [i for i in sorted(set(j
                                      for term in terms
                                      for j in term.split(' ')))]

    return try_transform_reversed(definitions, output_file_name, error_reg_string, temp_file_name,
                                  try_remove_if_name_not_found_in_section_transformer(get_names, **kwargs),
                                  'Variable removal',
                                  **kwargs)


CONTEXT_REG = re.compile(r'^\s*' +
                         r'(?:Local\s+|Global\s+|Polymorphic\s+|Monomorphic\s+)*' +
                         r'Context\s*`\s*[\({]\s*([^:\s]+)\s*:',
                         flags=re.MULTILINE)
def try_remove_contexts(definitions, output_file_name, error_reg_string, temp_file_name,
                        **kwargs):
    return try_transform_reversed(definitions, output_file_name, error_reg_string, temp_file_name,
                                  try_remove_if_name_not_found_in_section_transformer(lambda definition: CONTEXT_REG.findall(definition['statement'].replace(':', ' : ')), **kwargs),
                                  'Context removal',
                                  **kwargs)


def try_admit_abstracts(definitions, output_file_name, error_reg_string, temp_file_name,
                        verbose=DEFAULT_VERBOSITY, log=DEFAULT_LOG, **kwargs):
    def do_call(method, definitions, agressive):
        return method(definitions, output_file_name, error_reg_string, temp_file_name,
                      (lambda definition, rest_definitions:
                           transform_abstract_to_admit(definition, rest_definitions, agressive=agressive, verbose=verbose, log=log)),
                      '[abstract ...] admits',
                      verbose=verbose,
                      log=log,
                      **kwargs)

    old_definitions = join_definitions(definitions)
    # for comparison, to see if things have changed first, try to do
    # everything at once; python cycles are assumed to be cheap in
    # comparison to coq cycles
    definitions = do_call(try_transform_reversed, definitions, True)
    new_definitions = join_definitions(definitions)
    if new_definitions != old_definitions:
        if verbose >= 3: log('Success with [abstract ...] admits on try_transform_reversed, agressive: True, definitions:\n%s'
                             % new_definitions)
        return definitions

    # try the other options, each less agressive than the last
    definitions = do_call(try_transform_reversed, definitions, False)
    new_definitions = join_definitions(definitions)
    if new_definitions != old_definitions:
        if verbose >= 3: log('Success with [abstract ...] admits on try_transform_reversed, agressive: False, definitions:\n%s'
                             % new_definitions)
        return definitions

    definitions = do_call(try_transform_each, definitions, True)
    new_definitions = join_definitions(definitions)
    if new_definitions != old_definitions:
        if verbose >= 3: log('Success with [abstract ...] admits on try_transform_each, agressive: True, definitions:\n%s'
                             % new_definitions)
        return definitions

    definitions = do_call(try_transform_each, definitions, False)
    new_definitions = join_definitions(definitions)
    if new_definitions != old_definitions:
        if verbose >= 3: log('Success with [abstract ...] admits on try_transform_each, agressive: False, definitions:\n%s'
                             % new_definitions)
    else:
        if verbose >= 3: log('Failure with [abstract ...] admits.')
    return definitions


def try_admit_matching_definitions(definitions, output_file_name, error_reg_string, temp_file_name, matcher, description,
                                   verbose=DEFAULT_VERBOSITY, log=DEFAULT_LOG, **kwargs):
    def transformer(cur_definition, rest_definitions):
        if len(cur_definition['statements']) > 2 and matcher(cur_definition):
            statements = (cur_definition['statements'][0], 'admit.', 'Defined.')
            return {'statements':statements,
                    'statement':'\n'.join(statements),
                    'terms_defined':cur_definition['terms_defined']}
        else:
            return cur_definition

    def do_call(method, definitions):
        return method(definitions, output_file_name, error_reg_string, temp_file_name,
                      transformer, description,
                      verbse=verbose,
                      log=log,
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
        if verbose >= 1: log('Failed to do everything at once; trying one at a time.')
        definitions = do_call(try_transform_each, definitions)
    new_definitions = join_definitions(definitions)
    if new_definitions == old_definitions:
        if verbose >= 1: log('No successful changes.')
    else:
        if verbose >= 1: log('Success!')
    return definitions

def try_admit_qeds(definitions, output_file_name, error_reg_string, temp_file_name,
                   **kwargs):
    QED_REG = re.compile(r"(?<![\w'])Qed\s*\.\s*$", flags=re.MULTILINE)
    return try_admit_matching_definitions(definitions, output_file_name, error_reg_string, temp_file_name,
                                          (lambda definition: QED_REG.search(definition['statement'])),
                                          'Admitting Qeds',
                                          **kwargs)

def try_admit_lemmas(definitions, output_file_name, error_reg_string, temp_file_name,
                     **kwargs):
    LEMMA_REG = re.compile(r'^\s*' +
                           r'(?:Local\s+|Global\s+|Polymorphic\s+|Monomorphic\s+)*' +
                           r'(?:Lemma|Remark|Fact|Corollary|Proposition)\s*', flags=re.MULTILINE)
    return try_admit_matching_definitions(definitions, output_file_name, error_reg_string, temp_file_name,
                                          (lambda definition: LEMMA_REG.search(definition['statement'])),
                                          'Admitting lemmas',
                                          **kwargs)

def try_admit_definitions(definitions, output_file_name, error_reg_string, temp_file_name,
                          **kwargs):
    return try_admit_matching_definitions(definitions, output_file_name, error_reg_string, temp_file_name,
                                          (lambda definition: True),
                                          'Admitting definitions',
                                          **kwargs)


MODULE_REG = re.compile(r'^(\s*Module)(\s+[^\s\.]+\s*\.\s*)$')
def try_export_modules(definitions, output_file_name, error_reg_string, temp_file_name,
                       **kwargs):
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
    return try_transform_each(definitions, output_file_name, error_reg_string, temp_file_name,
                              transformer,
                              'Module exportation',
                              **kwargs)




def try_strip_comments(output_file_name, error_reg_string,
                       verbose=DEFAULT_VERBOSITY, log=DEFAULT_LOG, **kwargs):
    contents = read_from_file(output_file_name)
    old_contents = contents
    contents = strip_comments(contents)
    if contents == old_contents:
        if verbose >= 1: log('\nNo strippable comments.')
        return
    output = diagnose_error.get_coq_output(kwargs['coqc'], kwargs['coqc_args'], contents, kwargs['timeout'])
    if diagnose_error.has_error(output, error_reg_string):
        if verbose >= 1: log('\nSucceeded in stripping comments.')
        contents = prepend_header(contents, **kwargs)
        write_to_file(output_file_name, contents)
    else:
        if verbose >= 1:
            log('\nNon-fatal error: Failed to strip comments and preserve the error.')
            log('The new error was:')
            log(output)
            log('Stripped comments file not saved.')




def try_strip_newlines(output_file_name, error_reg_string, max_consecutive_newlines, strip_trailing_space,
                       verbose=DEFAULT_VERBOSITY, log=DEFAULT_LOG, **kwargs):
    contents = read_from_file(output_file_name)
    old_contents = contents
    if strip_trailing_space:
        contents = '\n'.join(map(str.rstrip, contents.split('\n')))
    contents = strip_newlines(contents, max_consecutive_newlines)
    if contents == old_contents:
        if verbose >= 1: log('\nNo strippable newlines or spaces.')
        return
    output = diagnose_error.get_coq_output(kwargs['coqc'], kwargs['coqc_args'], contents, kwargs['timeout'])
    if diagnose_error.has_error(output, error_reg_string):
        if verbose >= 1: log('\nSucceeded in stripping newlines and spaces.')
        contents = prepend_header(contents, **kwargs)
        write_to_file(output_file_name, contents)
    else:
        if verbose >= 1:
            log('\nNon-fatal error: Failed to strip newlines and spaces and preserve the error.')
            log('The new error was:')
            log(output)
            log('Stripped comments file not saved.')



def try_strip_extra_lines(output_file_name, line_num, error_reg_string, temp_file_name,
                          verbose=DEFAULT_VERBOSITY, log=DEFAULT_LOG, **kwargs):
    contents = read_from_file(output_file_name)
    statements = split_coq_file_contents(contents)
    cur_line_num = 0
    new_statements = statements
    for statement_num, statement in enumerate(statements):
        cur_line_num += statement.count('\n') + 1 # +1 for the extra newline between each statement
        if cur_line_num >= line_num:
            new_statements = statements[:statement_num + 1]
            break
    if new_statements == statements:
        if verbose: log('No lines to trim')
        return
    output = diagnose_error.get_coq_output(kwargs['coqc'], kwargs['coqc_args'], '\n'.join(new_statements), kwargs['timeout'])
    if diagnose_error.has_error(output, error_reg_string):
        if verbose: log('Trimming successful.  We removed all lines after %d; the error was on line %d.' % (cur_line_num, line_num))
        new_contents = prepend_header('\n'.join(new_statements), **kwargs)
        write_to_file(output_file_name, new_contents)
        if verbose >= 2: log('Trimmed file:\n%s' % read_from_file(output_file_name))
    else:
        if verbose:
            log('Trimming unsuccessful.  Writing trimmed file to %s.  The output was:' % temp_file_name)
            log(output)
        new_contents = prepend_header('\n'.join(new_statements), **kwargs)
        write_to_file(temp_file_name, new_contents)



EMPTY_SECTION_REG = re.compile(r'(\.\s+|^\s*)(?:Section|Module\s+Export|Module)\s+([^\.]+)\.' +
                               r'(?:\s' +
                               r'|Global\s|Local\s'
                               r'|Set\s+Universe\s+Polymorphism\s*\.\s' +
                               r'|Unset\s+Universe\s+Polymorphism\s*\.\s)+End\s+([^\.]+)\.(\s+|$)', flags=re.MULTILINE)
def try_strip_empty_sections(output_file_name, error_reg_string, temp_file_name, verbose=DEFAULT_VERBOSITY, log=DEFAULT_LOG, **kwargs):
    contents = read_from_file(output_file_name)
    old_contents = contents
    new_contents = EMPTY_SECTION_REG.sub(r'\1', old_contents)
    while new_contents != old_contents:
        old_contents, new_contents = new_contents, EMPTY_SECTION_REG.sub(r'\1', new_contents)

    if new_contents == contents:
        if verbose: log('No empty sections to remove')
        return
    output = diagnose_error.get_coq_output(kwargs['coqc'], kwargs['coqc_args'], new_contents, kwargs['timeout'])
    if diagnose_error.has_error(output, error_reg_string):
        if verbose: log('Empty section removal successful.')
        new_contents = prepend_header(new_contents, **kwargs)
        write_to_file(output_file_name, new_contents)
    else:
        if verbose:
            log('Empty section removal unsuccessful.  Writing trimmed file to %s.  The output was:' % temp_file_name)
            log(output)
        new_contents = prepend_header(new_contents, **kwargs)
        write_to_file(temp_file_name, new_contents)



if __name__ == '__main__':
    args = parser.parse_args()
    os.chdir(args.directory)
    bug_file_name = args.bug_file.name
    output_file_name = args.output_file
    temp_file_name = args.temp_file
    log = make_logger(args.log_files)
    coqc = args.coqc
    admit_opaque = args.admit_opaque
    aggressive = args.aggressive
    admit_transparent = args.admit_transparent
    if args.verbose is None: args.verbose = DEFAULT_VERBOSITY
    if args.quiet is None: args.quiet = 0
    env = {
        'topname': args.topname,
        'verbose': args.verbose - args.quiet,
        'fast_merge_imports': args.fast_merge_imports,
        'log': log,
        'coqc': args.coqc,
        'coqtop': args.coqtop,
        'as_modules': args.wrap_modules,
        'max_consecutive_newlines': args.max_consecutive_newlines,
        'header': args.header,
        'strip_trailing_space': args.strip_trailing_space,
        'timeout': args.timeout,
        'coqc_args': args.coqc_args,
        'coqtop_args': args.coqtop_args
        }
    if bug_file_name[-2:] != '.v':
        print('\nError: BUGGY_FILE must end in .v (value: %s)' % bug_file_name)
        log('\nError: BUGGY_FILE must end in .v (value: %s)' % bug_file_name)
        sys.exit(1)
    if output_file_name[-2:] != '.v':
        print('\nError: OUT_FILE must end in .v (value: %s)' % output_file_name)
        log('\nError: OUT_FILE must end in .v (value: %s)' % output_file_name)
        sys.exit(1)
    remove_temp_file = False
    if temp_file_name == '':
        temp_file = tempfile.NamedTemporaryFile(suffix='.v', dir='.', delete=False)
        temp_file_name = temp_file.name
        temp_file.close()
        remove_temp_file = True
    if temp_file_name[-2:] != '.v':
        print('\nError: TEMP_FILE must end in .v (value: %s)' % temp_file_name)
        log('\nError: TEMP_FILE must end in .v (value: %s)' % temp_file_name)
        sys.exit(1)


    if env['verbose'] >= 1: log('\nFirst, I will attempt to inline all of the inputs in %s, and store the result in %s...' % (bug_file_name, output_file_name))
    inlined_contents = include_imports(bug_file_name, **env)
    if inlined_contents:
        write_to_file(output_file_name, inlined_contents)
    else:
        if env['verbose'] >= 1: log('Failed to inline inputs.')
        sys.exit(1)

    old_header = get_old_header(inlined_contents, env['header'])
    env['header_dict'] = {'original_line_count':0,
                          'old_header':old_header}

    if env['verbose'] >= 1: log('\nNow, I will attempt to coq the file, and find the error...')
    error_reg_string = get_error_reg_string(output_file_name, **env)

    if env['max_consecutive_newlines'] >= 0 or env['strip_trailing_space']:
        if env['verbose'] >= 1: log('\nNow, I will attempt to strip repeated newlines and trailing spaces from this file...')
        try_strip_newlines(output_file_name, error_reg_string, **env)

    contents = read_from_file(output_file_name)
    original_line_count = len(contents.split('\n'))
    env['header_dict']['original_line_count'] = original_line_count

    if env['verbose'] >= 1: log('\nNow, I will attempt to strip the comments from this file...')
    try_strip_comments(output_file_name, error_reg_string, **env)



    contents = read_from_file(output_file_name)
    if env['verbose'] >= 1:
        log('\nIn order to efficiently manipulate the file, I have to break it into statements.  I will attempt to do this by matching on periods.')
        strings = re.findall(r'"[^"]+"', contents)
        bad_strings = [i for i in strings if re.search(r'\.\s', i)]
        if bad_strings:
            log('If you have periods in strings, and these periods are essential to generating the error, then this process will fail.  Consider replacing the string with some hack to get around having a period and then a space, like ["a. b"%string] with [("a." ++ " b")%string].')
            log('You have the following strings with periods in them:\n%s' % '\n'.join(bad_strings))
    statements = split_coq_file_contents(contents)
    output = diagnose_error.get_coq_output(coqc, env['coqc_args'], '\n'.join(statements), env['timeout'])
    if diagnose_error.has_error(output, error_reg_string):
        if env['verbose'] >= 1: log('Splitting successful.')
        contents = prepend_header('\n'.join(statements), env['header'], env['header_dict'])
        write_to_file(output_file_name, contents)
    else:
        if env['verbose'] >= 1: log('Splitting unsuccessful.  I will not be able to proceed.  Writing split file to %s.' % temp_file_name)
        contents = prepend_header('\n'.join(statements), env['header'], env['header_dict'])
        write_to_file(temp_file_name, contents)
        if env['verbose'] >= 1: log('The output given was:')
        if env['verbose'] >= 1: log(output)
        sys.exit(1)

    if env['verbose'] >= 1: log('\nI will now attempt to remove any lines after the line which generates the error.')
    line_num = diagnose_error.get_error_line_number(output, error_reg_string)
    try_strip_extra_lines(output_file_name, line_num, error_reg_string, temp_file_name, **env)


    if env['verbose'] >= 1: log('\nIn order to efficiently manipulate the file, I have to break it into definitions.  I will now attempt to do this.')
    contents = read_from_file(output_file_name)
    statements = split_coq_file_contents(contents)
    if env['verbose'] >= 3: log('I am using the following file: %s' % '\n'.join(statements))
    definitions = split_statements_to_definitions(statements, **env)
    output = diagnose_error.get_coq_output(coqc, env['coqc_args'], join_definitions(definitions), env['timeout'])
    if diagnose_error.has_error(output, error_reg_string):
        if env['verbose'] >= 1: log('Splitting to definitions successful.')
        contents = prepend_header(join_definitions(definitions), env['header'], env['header_dict'])
        write_to_file(output_file_name, contents)
    else:
        if env['verbose'] >= 1: log('Splitting to definitions unsuccessful.  I will not be able to proceed.  Writing split file to %s.' % temp_file_name)
        contents = prepend_header(join_definitions(definitions), env['header'], env['header_dict'])
        write_to_file(temp_file_name, contents)
        if env['verbose'] >= 1: log('The output given was:')
        if env['verbose'] >= 1: log(output)
        sys.exit(1)

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

    tasks += (('remove unused definitions, one at a time', try_remove_each_definition),)

    if admit_transparent:
        tasks += (('admit lemmas', try_admit_lemmas),
                  ('admit definitions', try_admit_definitions))

    tasks += (('remove hints', try_remove_hints),
              ('export modules', try_export_modules))

    if aggressive:
        tasks += ((('remove all lines, one at a time', try_remove_each_and_every_line),) +
                  # we've probably just removed a lot, so try to remove definitions again
                  recursive_tasks)


    old_definitions = ''
    while old_definitions != join_definitions(definitions):
        old_definitions = join_definitions(definitions)
        if env['verbose'] >= 2: log('Definitions:')
        if env['verbose'] >= 2: log(definitions)

        for description, task in tasks:
            if env['verbose'] >= 1: log('\nI will now attempt to %s' % description)
            definitions = task(definitions, output_file_name, error_reg_string, temp_file_name, **env)


    if env['verbose'] >= 1: log('\nI will now attempt to remove empty sections')
    try_strip_empty_sections(output_file_name, error_reg_string, temp_file_name, **env)

    if env['max_consecutive_newlines'] >= 0 or env['strip_trailing_space']:
        if env['verbose'] >= 1: log('\nNow, I will attempt to strip repeated newlines and trailing spaces from this file...')
        try_strip_newlines(output_file_name, error_reg_string, **env)

    if os.path.exists(temp_file_name) and remove_temp_file:
        os.remove(temp_file_name)
