#!/usr/bin/env python
import argparse, tempfile, sys, os, re
from replace_imports import include_imports
from strip_comments import strip_comments
from split_file import split_coq_file_contents
from split_definitions import split_statements_to_definitions, join_definitions
from admit_abstract import transform_abstract_to_admit
import diagnose_error

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
parser.add_argument('--fast', dest='fast',
                    action='store_const', const=True, default=False,
                    help='Use a faster method for combining imports')
parser.add_argument('--log-file', '-l', dest='log_files', nargs='*', type=argparse.FileType('w'),
                    default=sys.stdout,
                    help='The files to log output to.  Use - for stdout.')

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

def get_error_reg_string(output_file_name, verbose=DEFAULT_VERBOSITY, log=DEFAULT_LOG):
    error_reg_string = ''
    while error_reg_string == '':
        if verbose: log('\nCoqing the file...')
        contents = read_from_file(output_file_name)
        output = diagnose_error.get_coq_output(contents)
        result = ''
        log("\nThis file produces the following output when Coq'ed:\n%s" % output)
        while result not in ('y', 'n', 'yes', 'no'):
            result = raw_input('Does this output display the correct error? [(y)es/(n)o] ').lower().strip()
        if result in ('n', 'no'):
            raw_input('Please modify the file (%s) so that it errors correctly, and then press ENTER to continue, or ^C to break.' % output_file_name)
            continue

        if diagnose_error.has_error(output):
            error_string = diagnose_error.get_error_string(output)
            error_reg_string = diagnose_error.make_reg_string(output)
            log("\nI think the error is '%s'.\nThe corresponding regular expression is %s." % (error_string, repr(error_reg_string)))
            result = ''
            while result not in ('y', 'n', 'yes', 'no'):
                result = raw_input('Is this correct? [(y)es/(n)o] ').lower().strip()
            if result in ('no', 'n'):
                error_reg_string = ''
        else:
            log('\nThe current state of the file does not have a recognizable error.')

        if error_reg_string == '':
            error_reg_string = raw_input('\nPlease enter a regular expression which matches on the output.  Leave blank to re-coq the file. ')

        while (error_reg_string != ''
               and (not re.search(error_reg_string, output)
                    or len(re.search(error_reg_string, output).groups()) != 2)):
            if not re.search(error_reg_string, output):
                log('\nThe given regular expression does not match the output.')
            elif len(re.search(error_reg_string, output).groups()) != 2:
                log('\nThe given regular expression does not have two groups.')
                log('It must have one integer group which matches on the line number,')
                log('and another group which matches on the error string.')
            error_reg_string = raw_input('Please enter a valid regular expression which matches on the output.  Leave blank to re-coq the file. ')

        if error_reg_string == '':
            continue

    return error_reg_string

def try_transform_each(definitions, output_file_name, error_reg_string, temp_file_name, transformer, description, skip_n=1,
                       verbose=DEFAULT_VERBOSITY, log=DEFAULT_LOG):
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
        if not new_definition or old_definition['statement'] != new_definition['statement']:
            if not new_definition or not new_definition['statement'].strip():
                if verbose >= 3: log('Attempting to remove %s' % repr(old_definition['statement']))
                try_definitions = definitions[:i] + definitions[i + 1:]
            else:
                if verbose >= 3: log('Attempting to transform %s into %s' % (old_definition['statement'], new_definition['statement']))
                try_definitions = definitions[:i] + [new_definition] + definitions[i + 1:]
            output = diagnose_error.get_coq_output(join_definitions(try_definitions))
            if diagnose_error.has_error(output, error_reg_string):
                if verbose >= 3: log('Change succeeded')
                success = True
                write_to_file(output_file_name, join_definitions(try_definitions))
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
            write_to_file(output_file_name, join_definitions(definitions))
        return definitions
    else:
        if verbose >= 1: log(description + ' unsuccessful.')
        return original_definitions


def try_transform_reversed(definitions, output_file_name, error_reg_string, temp_file_name, transformer, description, skip_n=3,
                           verbose=DEFAULT_VERBOSITY, log=DEFAULT_LOG):
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
    output = diagnose_error.get_coq_output(join_definitions(definitions))
    if diagnose_error.has_error(output, error_reg_string):
        if verbose >= 3: log(description + ' successful')
        write_to_file(output_file_name, join_definitions(definitions))
        return definitions
    else:
        if verbose >= 3: log(description + ' unsuccessful.  Writing intermediate code to %s.' % temp_file_name)
        if verbose >= 3: log('The output was:\n%s' % output)
        write_to_file(temp_file_name, join_definitions(definitions))
        return original_definitions

def try_remove_if_not_matches_transformer(definition_found_in):
    def transformer(cur_definition, rest_definitions):
        if any(definition_found_in(cur_definition, future_definition)
               for future_definition in rest_definitions):
            return cur_definition
        else:
            return None
    return transformer

# don't count things like [Section ...], [End ...]
EXCLUSION_REG = re.compile(r"^\s*Section\s+[^\.]+\.\s*$" +
                           r"|^\s*End\s+[^\.]+\.\s*$")
def try_remove_if_name_not_found_in_transformer(get_names):
    def definition_found_in(cur_definition, future_definition):
        names = get_names(cur_definition)
        if len(names) == 0 or EXCLUSION_REG.search(future_definition['statement']):
            return True
        return any(re.search(r"(?<![\w'])%s(?![\w'])" % name, future_definition['statement'])
                   for name in names)
    return try_remove_if_not_matches_transformer(definition_found_in)


def try_remove_non_instance_definitions(definitions, output_file_name, error_reg_string, temp_file_name, verbose=DEFAULT_VERBOSITY, log=DEFAULT_LOG):
    def get_names(definition):
        if re.search(r"(?<![\w'])Instance\s", definition['statements'][0]):
            return tuple()
        elif re.search(r"(?<![\w'])Canonical\s+Structure\s", definition['statements'][0]):
            return tuple()
        else:
            return definition.get('terms_defined', tuple())
    return try_transform_reversed(definitions, output_file_name, error_reg_string, temp_file_name,
                                  try_remove_if_name_not_found_in_transformer(get_names),
                                  'Non-instance definition removal',
                                  verbose=verbose, log=log)

def try_remove_definitions(definitions, output_file_name, error_reg_string, temp_file_name, verbose=DEFAULT_VERBOSITY, log=DEFAULT_LOG):
    return try_transform_reversed(definitions, output_file_name, error_reg_string, temp_file_name,
                                  try_remove_if_name_not_found_in_transformer(lambda definition: definition.get('terms_defined', tuple())),
                                  'Definition removal',
                                  verbose=verbose, log=log)

def try_remove_each_definition(definitions, output_file_name, error_reg_string, temp_file_name, verbose=DEFAULT_VERBOSITY, log=DEFAULT_LOG):
    return try_transform_each(definitions, output_file_name, error_reg_string, temp_file_name,
                              try_remove_if_name_not_found_in_transformer(lambda definition: definition.get('terms_defined', tuple())),
                              'Definition removal',
                              verbose=verbose, log=log)

def try_remove_aborted(definitions, output_file_name, error_reg_string, temp_file_name, verbose=DEFAULT_VERBOSITY, log=DEFAULT_LOG):
    ABORT_REG = re.compile(r'\sAbort\s*\.\s*$')
    return try_transform_reversed(definitions, output_file_name, error_reg_string, temp_file_name,
                                  (lambda definition, rest:
                                       None if ABORT_REG.search(definition['statement']) else definition),
                                  'Aborted removal',
                                  verbose=verbose,
                                  log=log)

def try_remove_ltac(definitions, output_file_name, error_reg_string, temp_file_name, verbose=DEFAULT_VERBOSITY, log=DEFAULT_LOG):
    LTAC_REG = re.compile(r'^\s*(?:Local\s+|Global\s+)?Ltac\s+([^\s]+)', re.MULTILINE)
    return try_transform_reversed(definitions, output_file_name, error_reg_string, temp_file_name,
                                  try_remove_if_name_not_found_in_transformer(lambda definition: LTAC_REG.findall(definition['statement'].replace(':', '\
 : '))),
                                  'Ltac removal',
                                  verbose=verbose,
                                  log=log)

def try_remove_hints(definitions, output_file_name, error_reg_string, temp_file_name, verbose=DEFAULT_VERBOSITY, log=DEFAULT_LOG):
    HINT_REG = re.compile(r'^\s*' +
                          r'(?:Local\s+|Global\s+|Polymorphic\s+|Monomorphic\s+)*' +
                          r'(?:Hint|Obligation\s+Tactic|Arguments|Implicit\s+Arguments' +
                          r'|Notation|Tactic\s+Notation|Infix|Transparent|Opaque|Coercion' +
                          r'|Identity\s+Coercion|Delimit\s+Scope|Set|Unset|Generalizable' +
                          r'|Bind\s+Scope|Create\s+HintDb|Existing\s+Instance|Context)\s+',
                          re.MULTILINE)
    return try_transform_each(definitions, output_file_name, error_reg_string, temp_file_name,
                              (lambda definition, rest: (None if HINT_REG.search(definition['statement'])
                                                         else definition)),
                              'Hint removal',
                              verbose=verbose,
                              log=log)

def try_remove_variables(definitions, output_file_name, error_reg_string, temp_file_name, verbose=DEFAULT_VERBOSITY, log=DEFAULT_LOG):
    VARIABLE_REG = re.compile(r'^\s*' +
                              r'(?:Local\s+|Global\s+|Polymorphic\s+|Monomorphic\s+)*' +
                              r'(?:Variables|Variable|Hypotheses|Hypothesis|Parameters|Parameter|Axioms|Axiom|Conjectures|Conjecture)\s+' +
                              r'([^\s]+)',
                              re.MULTILINE)
    return try_transform_reversed(definitions, output_file_name, error_reg_string, temp_file_name,
                                  try_remove_if_name_not_found_in_transformer(lambda definition: VARIABLE_REG.findall(definition['statement'].replace(':', ' : '))),
                                  'Variable removal',
                                  verbose=verbose,
                                  log=log)


def try_remove_contexts(definitions, output_file_name, error_reg_string, temp_file_name, verbose=DEFAULT_VERBOSITY, log=DEFAULT_LOG):
    CONTEXT_REG = re.compile(r'^\s*' +
                              r'(?:Local\s+|Global\s+|Polymorphic\s+|Monomorphic\s+)*' +
                              r'Context\s*`\s*[\({]\s*([^:\s]+)\s*:',
                              re.MULTILINE)
    return try_transform_reversed(definitions, output_file_name, error_reg_string, temp_file_name,
                                  try_remove_if_name_not_found_in_transformer(lambda definition: CONTEXT_REG.findall(definition['statement'].replace(':', ' : '))),
                                  'Context removal',
                                  verbose=verbose,
                                  log=log)


def try_admit_abstracts(definitions, output_file_name, error_reg_string, temp_file_name, verbose=DEFAULT_VERBOSITY, log=DEFAULT_LOG):
    def do_call(method, definitions, agressive):
        return method(definitions, output_file_name, error_reg_string, temp_file_name,
                      (lambda definition, rest_definitions:
                           transform_abstract_to_admit(definition, rest_definitions, agressive=agressive, verbose=verbose, log=log)),
                      '[abstract ...] admits',
                      verbose=verbose,
                      log=log)

    old_definitions = join_definitions(definitions)
    # for comparison, to see if things have changed first, try to do
    # everything at once; python cycles are assumed to be cheap in
    # comparison to coq cycles
    definitions = do_call(try_transform_reversed, definitions, True)
    new_definitions = join_definitions(definitions)
    if new_definitions != old_definitions: return definitions

    # try the other options, each less agressive than the last
    definitions = do_call(try_transform_reversed, definitions, False)
    new_definitions = join_definitions(definitions)
    if new_definitions != old_definitions: return definitions

    definitions = do_call(try_transform_each, definitions, True)
    new_definitions = join_definitions(definitions)
    if new_definitions != old_definitions: return definitions

    definitions = do_call(try_transform_each, definitions, False)
    new_definitions = join_definitions(definitions)
    return definitions


def try_admit_matching_definitions(definitions, output_file_name, error_reg_string, temp_file_name, matcher, description, verbose=DEFAULT_VERBOSITY, log=DEFAULT_LOG):
    def transformer(cur_definition, rest_definitions):
        if len(cur_definition['statements']) > 1 and matcher(cur_definition):
            statements = (cur_definition['statements'][0], 'Admitted.')
            return {'statements':statements,
                    'statement':'\n'.join(statements),
                    'terms_defined':cur_definition['terms_defined']}
        else:
            return cur_definition

    def do_call(method, definitions):
        return method(definitions, output_file_name, error_reg_string, temp_file_name,
                      transformer, description,
                      verbose=verbose,
                      log=log)

    old_definitions = join_definitions(definitions) # for comparison,
    # to see if things have changed first, try to do everything at
    # once; python cycles are assumed to be cheap in comparison to coq
    # cycles
    definitions = do_call(try_transform_reversed, definitions)
    new_definitions = join_definitions(definitions)
    if new_definitions == old_definitions:
        # we failed to do everything at once, try the simple thing and
        # try to admit each individually
         definitions = do_call(try_transform_each, definitions)
    return definitions

def try_admit_qeds(definitions, output_file_name, error_reg_string, temp_file_name, verbose=DEFAULT_VERBOSITY, log=DEFAULT_LOG):
    QED_REG = re.compile(r"(?<![\w'])Qed\s*\.\s*$", re.MULTILINE)
    return try_admit_matching_definitions(definitions, output_file_name, error_reg_string, temp_file_name,
                                          (lambda definition: QED_REG.search(definition['statement'])),
                                          'Admitting Qeds',
                                          verbose=verbose,
                                          log=log)

def try_admit_lemmas(definitions, output_file_name, error_reg_string, temp_file_name, verbose=DEFAULT_VERBOSITY, log=DEFAULT_LOG):
    LEMMA_REG = re.compile(r'^\s*' +
                           r'(?:Local\s+|Global\s+|Polymorphic\s+|Monomorphic\s+)*' +
                           r'(?:Lemma|Remark|Fact|Corollary|Proposition)\s*', re.MULTILINE)
    return try_admit_matching_definitions(definitions, output_file_name, error_reg_string, temp_file_name,
                                          (lambda definition: LEMMA_REG.search(definition['statement'])),
                                          'Admitting lemmas',
                                          verbose=verbose,
                                          log=log)

def try_admit_definitions(definitions, output_file_name, error_reg_string, temp_file_name, verbose=DEFAULT_VERBOSITY, log=DEFAULT_LOG):
    return try_admit_matching_definitions(definitions, output_file_name, error_reg_string, temp_file_name,
                                          (lambda definition: True),
                                          'Admitting definitions',
                                          verbose=verbose,
                                          log=log)






def try_strip_comments(output_file_name, error_reg_string, verbose=DEFAULT_VERBOSITY, log=DEFAULT_LOG):
    contents = read_from_file(output_file_name)
    old_contents = contents
    contents = strip_comments(contents)
    if contents == old_contents:
        if verbose >= 1: log('\nNo strippable comments.')
        return
    output = diagnose_error.get_coq_output(contents)
    if diagnose_error.has_error(output, error_reg_string):
        if verbose >= 1: log('\nSucceeded in stripping comments.')
        write_to_file(output_file_name, contents)
    else:
        if verbose >= 1:
            log('\nNon-fatal error: Failed to strip comments and preserve the error.')
            log('The new error was:')
            log(output)
            log('Stripped comments file not saved.')


def try_strip_extra_lines(output_file_name, line_num, error_reg_string, temp_file_name, verbose=DEFAULT_VERBOSITY, log=DEFAULT_LOG):
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
    output = diagnose_error.get_coq_output('\n'.join(new_statements))
    if diagnose_error.has_error(output, error_reg_string):
        if verbose: log('Trimming successful.  We removed all lines after %d; the error was on line %d.' % (cur_line_num, line_num))
        write_to_file(output_file_name, '\n'.join(new_statements))
        if verbose >= 2: log('Trimmed file:\n%s' % read_from_file(output_file_name))
    else:
        if verbose:
            log('Trimming unsuccessful.  Writing trimmed file to %s.  The output was:' % temp_file_name)
            log(output)
        write_to_file(temp_file_name, '\n'.join(new_statements))



if __name__ == '__main__':
    args = parser.parse_args()
    os.chdir(args.directory)
    bug_file_name = args.bug_file.name
    output_file_name = args.output_file
    temp_file_name = args.temp_file
    verbose = args.verbose
    fast = args.fast
    log = make_logger(args.log_files)
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


    if verbose >= 1: log('\nFirst, I will attempt to inline all of the inputs in %s, and store the result in %s...' % (bug_file_name, output_file_name))
    inlined_contents = include_imports(bug_file_name, verbose=verbose, fast=fast, log=log)
    if inlined_contents:
        write_to_file(output_file_name, inlined_contents)
    else:
        if verbose >= 1: log('Failed to inline inputs.')
        sys.exit(1)

    if verbose >= 1: log('\nNow, I will attempt to coq the file, and find the error...')
    error_reg_string = get_error_reg_string(output_file_name, verbose=verbose, log=log)

    if verbose >= 1: log('\nNow, I will try to strip the comments from this file...')
    try_strip_comments(output_file_name, error_reg_string, verbose=verbose, log=log)



    # TODO(jgross): Only display the warning if there seem to be periods in strings.
    if verbose >= 1: log('\nIn order to efficiently manipulate the file, I have to break it into statements.  I will attempt to do this by matching on periods.  If you have periods in strings, and these periods are essential to generating the error, then this process will fail.  Consider replacing the string with some hack to get around having a period and then a space, like ["a. b"%string] with [("a." ++ " b")%string].')
    contents = read_from_file(output_file_name)
    statements = split_coq_file_contents(contents)
    output = diagnose_error.get_coq_output('\n'.join(statements))
    if diagnose_error.has_error(output, error_reg_string):
        if verbose >= 1: log('Splitting successful.')
        write_to_file(output_file_name, '\n'.join(statements))
    else:
        if verbose >= 1: log('Splitting unsuccessful.  I will not be able to proceed.  Writing split file to %s.' % temp_file_name)
        write_to_file(temp_file_name, '\n'.join(statements))
        if verbose >= 1: log('The output given was:')
        if verbose >= 1: log(output)
        sys.exit(1)

    if verbose >= 1: log('\nI will now attempt to remove any lines after the line which generates the error.')
    line_num = diagnose_error.get_error_line_number(output, error_reg_string)
    try_strip_extra_lines(output_file_name, line_num, error_reg_string, temp_file_name, verbose=verbose, log=log)


    if verbose >= 1: log('\nIn order to efficiently manipulate the file, I have to break it into definitions.  I will now attempt to do this.')
    contents = read_from_file(output_file_name)
    statements = split_coq_file_contents(contents)
    if verbose >= 3: log('I am using the following file: %s' % '\n'.join(statements))
    definitions = split_statements_to_definitions(statements, verbose=verbose, log=log)
    output = diagnose_error.get_coq_output(join_definitions(definitions))
    if diagnose_error.has_error(output, error_reg_string):
        if verbose >= 1: log('Splitting to definitions successful.')
        write_to_file(output_file_name, join_definitions(definitions))
    else:
        if verbose >= 1: log('Splitting to definitions unsuccessful.  I will not be able to proceed.  Writing split file to %s.' % temp_file_name)
        write_to_file(temp_file_name, join_definitions(definitions))
        if verbose >= 1: log('The output given was:')
        if verbose >= 1: log(output)
        sys.exit(1)

    def try_recursive_remove(definitions):
        if verbose >= 1: log('\nI will now attempt to remove goals ending in [Abort.]')
        definitions = try_remove_aborted(definitions, output_file_name, error_reg_string, temp_file_name, verbose=verbose, log=log)

        if verbose >= 1: log('\nI will now attempt to remove unused Ltacs')
        definitions = try_remove_ltac(definitions, output_file_name, error_reg_string, temp_file_name, verbose=verbose, log=log)

        if verbose >= 1: log('\nI will now attempt to remove unused definitions')
        definitions = try_remove_definitions(definitions, output_file_name, error_reg_string, temp_file_name, verbose=verbose, log=log)

        if verbose >= 1: log('\nI will now attempt to remove unused non-instance, non-canonical structures')
        definitions = try_remove_non_instance_definitions(definitions, output_file_name, error_reg_string, temp_file_name, verbose=verbose, log=log)

        if verbose >= 1: log('\nI will now attempt to remove unused variables')
        definitions = try_remove_variables(definitions, output_file_name, error_reg_string, temp_file_name, verbose=verbose, log=log)

        if verbose >= 1: log('\nI will now attempt to remove unused contexts')
        definitions = try_remove_contexts(definitions, output_file_name, error_reg_string, temp_file_name, verbose=verbose, log=log)

        return definitions


    old_definitions = []
    while join_definitions(old_definitions) != join_definitions(definitions):
        old_definitions = list(definitions)
        if verbose >= 1: log('Definitions:')
        if verbose >= 1: log(definitions)

        definitions = try_recursive_remove(definitions)

        if verbose >= 1: log('\nI will now attempt to replace Qeds with Admitteds')
        try_admit_qeds(definitions, output_file_name, error_reg_string, temp_file_name, verbose=verbose, log=log)

        # we've probably just removed a lot, so try to remove definitions again
        definitions = try_recursive_remove(definitions)

        if verbose >= 1: log('\nI will now attempt to admit [abstract ...]s')
        try_admit_abstracts(definitions, output_file_name, error_reg_string, temp_file_name, verbose=verbose, log=log)

        # we've probably just removed a lot, so try to remove definitions again
        definitions = try_recursive_remove(definitions)

        if verbose >= 1: log('\nI will now attempt to remove unused definitions, one at a time')
        definitions = try_remove_each_definition(definitions, output_file_name, error_reg_string, temp_file_name, verbose=verbose, log=log)

        if verbose >= 1: log('\nI will now attempt to admit lemmas')
        try_admit_lemmas(definitions, output_file_name, error_reg_string, temp_file_name, verbose=verbose, log=log)

        if verbose >= 1: log('\nI will now attempt to admit definitions')
        try_admit_definitions(definitions, output_file_name, error_reg_string, temp_file_name, verbose=verbose, log=log)

        if verbose >= 1: log('\nI will now attempt to remove hints')
        try_remove_hints(definitions, output_file_name, error_reg_string, temp_file_name, verbose=verbose, log=log)


    if os.path.exists(temp_file_name) and remove_temp_file:
        os.remove(temp_file_name)
