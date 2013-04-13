#!/usr/bin/env python
import argparse, tempfile, sys, os, re
from replace_imports import include_imports
from strip_comments import strip_comments
from split_file import split_coq_file_contents
from split_definitions import split_statements_to_definitions, join_definitions
from recursive_remove_ltac import recursively_remove_ltac
from recursive_remove_definitions import recursively_remove_definitions
from admit_definitions import admit_definitions
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
                    action='store_const', const=True, default=False,
                    help='display some extra information')
parser.add_argument('--fast', dest='fast',
                    action='store_const', const=True, default=False,
                    help='Use a faster method for combining imports')

def write_to_file(file_name, contents):
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

def get_error_reg_string(output_file_name):
    error_reg_string = ''
    while error_reg_string == '':
        print('\nCoqing the file...')
        contents = read_from_file(output_file_name)
        output = diagnose_error.get_coq_output(contents)
        result = ''
        print("\nThis file produces the following output when Coq'ed:")
        print(output)
        while result not in ('y', 'n', 'yes', 'no'):
            result = raw_input('Does this output display the correct error? [(y)es/(n)o] ').lower().strip()
        if result in ('n', 'no'):
            raw_input('Please modify the file (%s) so that it errors correctly, and then press ENTER to continue, or ^C to break.' % output_file_name)
            continue

        if diagnose_error.has_error(output):
            error_string = diagnose_error.get_error_string(output)
            error_reg_string = diagnose_error.make_reg_string(output)
            print("\nI think the error is '%s'." % error_string)
            print("The corresponding regular expression is %s." % repr(error_reg_string))
            result = ''
            while result not in ('y', 'n', 'yes', 'no'):
                result = raw_input('Is this correct? [(y)es/(n)o] ').lower().strip()
            if result in ('no', 'n'):
                error_reg_string = ''
        else:
            print('\nThe current state of the file does not have a recognizable error.')

        if error_reg_string == '':
            error_reg_string = raw_input('\nPlease enter a regular expression which matches on the output.  Leave blank to re-coq the file. ')

        while (error_reg_string != ''
               and (not re.search(error_reg_string, output)
                    or len(re.search(error_reg_string, output).groups()) != 2)):
            if not re.search(error_reg_string, output):
                print('\nThe given regular expression does not match the output.')
            elif len(re.search(error_reg_string, output).groups()) != 2:
                print('\nThe given regular expression does not have two groups.')
                print('It must have one integer group which matches on the line number,')
                print('and another group which matches on the error string.')
            error_reg_string = raw_input('Please enter a valid regular expression which matches on the output.  Leave blank to re-coq the file. ')

        if error_reg_string == '':
            continue

    return error_reg_string

def try_transform_each(definitions, output_file_name, error_reg_string, temp_file_name, transformer, description, skip_n=3):
    """Tries to apply transformer to each definition in definitions,
    additionally passing in the list of subsequent definitions.  If
    the returned value of the 'statement' key is not equal to the old
    value, or if the return value is a false-y value (indicating that
    we should remove the line) then we see if the error is still
    present.  If it is, we keep the change; otherwise, we discard it.
    The order in which definitions are passed in is guaranteed to be
    reverse-order.

    Returns updated definitions."""
    # TODO(jgross): Use coqtop and [BackTo] to do incremental checking
    success = False
    i = len(definitions) - 1 - skip_n
    while i >= 0:
        old_definition = definitions[i]
        new_definition = transformer(old_definition, definitions[i + 1:])
        if not new_definition or old_definition['statement'] != new_definition['statement']:
            if not new_definition or not new_definition['statement'].strip():
                print('Attempting to remove %s' % repr(old_definition['statement']))
                try_definitions = definitions[:i] + definitions[i + 1:]
            else:
                print('Attempting to transform %s into %s' % (old_definition['statement'], new_definition['statement']))
                try_definitions = definitions[:i] + [new_definition] + definitions[i + 1:]
            output = diagnose_error.get_coq_output(join_definitions(try_definitions))
            if diagnose_error.has_error(output, error_reg_string):
                print('Change succeeded')
                success = True
                write_to_file(output_file_name, join_definitions(try_definitions))
                definitions = try_definitions
            else:
                print('Change failed.  Output:\n%s' % output)
        i -= 1
    if success:
        print(desciption + ' successful')
        write_to_file(output_file_name, join_definitions(definitions))
        return definitions
    else:
        print(description + ' unsuccessful.')
        return definitions


def try_transform_reversed(definitions, output_file_name, error_reg_string, temp_file_name, transformer, description, skip_n=3):
    """Replaces each definition in definitions, with transformer
    applied to that definition and the subsequent (transformed)
    definitions.  If transformer returns a false-y value, the
    definition is removed.  After transforming the entire list, we see
    if the error is still present.  If it is, we keep the change;
    otherwise, we discard it.  The order in which definitions are
    passed in is guaranteed to be reverse-order.

    Returns updated definitions."""
    definitions = list(definitions) # clone the list of definitions
    for i in reversed(list(range(len(definitions) - skip_n))):
        new_definition = transformer(definitions[i], definitions[i + 1:])
        if new_definition:
            definitions[i] = new_definition
        else:
            definitions = definitions[:i] + definitions[i + 1:]
    output = diagnose_error.get_coq_output(join_definitions(definitions))
    if diagnose_error.has_error(output, error_reg_string):
        print(desciption + ' successful')
        write_to_file(output_file_name, join_definitions(definitions))
        return definitions
    else:
        print(description + ' unsuccessful.  Writing intermediate code to %s.' % temp_file_name)
        print('The output was:\n%s' % output)
        write_to_file(temp_file_name, join_definitions(definitions))
        return definitions

def try_remove_if_not_matches_transformer(definition_found_in):
    def transformer(cur_definition, rest_definitions):
        if any(definition_found_in(cur_definition, future_definition)
               for future_definition in rest_definitions):
            return None
        else:
            return cur_definition
    return transformer

def try_remove_if_name_not_found_in_transformer(get_names):
    def definition_found_in(cur_definition, future_definition):
        names = get_names(cur_definition)
        if len(names) == 0:
            return True
        return any(re.search(r"(?<![\w'])%s(?![\w'])" % name, future_definition['statement'])
                   for name in names)
    return try_remove_if_not_matches_transformer(definition_found_in)


def try_remove_definitions(definitions, output_file_name, error_reg_string, temp_file_name):
    return try_transform_reversed(definitions, output_file_name, error_reg_string, temp_file_name,
                                  try_remove_if_name_not_found_in_transformer(lambda definition: definition['terms_defined']),
                                  'Description removal')

def try_remove_ltac(definitions, output_file_name, error_reg_string, temp_file_name):
    LTAC_REG = re.compile(r'^\s*(?:Local\s+|Global\s+)?Ltac\s+([^\s]+)', re.MULTILINE)
    return try_transform_reversed(definitions, output_file_name, error_reg_string, temp_file_name,
                                  try_remove_if_name_not_found_in_transformer(lambda definition: LTAC_REG.findall(definition['statement'].replace(':', '\
 : '))),
                                  'Ltac removal')

def try_remove_hints(definitions, output_file_name, error_reg_string, temp_file_name):
    HINT_REG = re.compile(r'^\s*' +
                          r'(?:Local\s+|Global\s+|Polymorphic\s+|Monomorphic\s+)*' +
                          r'(?:Hint|Obligation\s+Tactic|Arguments|Notation|Tactic\s+Notation|Transparent|Opaque)\s+',
                          re.MULTILINE)
    return try_transform_each(definitions, output_file_name, error_reg_string, temp_file_name,
                              (lambda definition: (None if HINT_REG.search(definition['statement'])
                                                   else definition)),
                              'Hint removal')

def try_remove_variables(definitions, output_file_name, error_reg_string, temp_file_name):
    VARIABLE_REG = re.compile(r'^\s*' +
                              r'(?:Local\s+|Global\s+|Polymorphic\s+|Monomorphic\s+)*' +
                              r'(?:Variables|Variable|Hypotheses|Hypothesis|Parameters|Parameter|Axioms|Axiom|Conjectures|Conjecture)\s+' +
                              r'([^\s]+)',
                              re.MULTILINE)
    return try_transform_reversed(definitions, output_file_name, error_reg_string, temp_file_name,
                                  try_remove_if_name_not_found_in_transformer(lambda definition: VARIABLE_REG.findall(definition['statement'].replace(':', ' : '))),
                                  'Variable removal')

def try_admit_matching_definitions(definitions, output_file_name, error_reg_string, temp_file_name, matcher, description):
    def transformer(cur_definition, rest_definitions):
        if len(cur_definition['statements']) > 1 and matcher(cur_definition):
            statements = (cur_definition['statements'][0], 'Admitted.')
            return {'statements':statements,
                    'statement':'\n'.join(statements),
                    'terms_defined':cur_definition['terms_defined']}
        else:
            return cur_definition

    return try_transform_each(definitions, output_file_name, error_reg_string, temp_file_name,
                              transformer, description)

def try_admit_qeds(definitions, output_file_name, error_reg_string, temp_file_name):
    QED_REG = re.compile(r"(?<![\w'])Qed\s*\.\s*$", re.MULTILINE)
    return try_admit_matching_definitions(definitions, output_file_name, error_reg_string, temp_file_name,
                                          (lambda definition: QED_REG.search(definition['statement'])),
                                          'Admitting Qeds')

def try_admit_lemmas(definitions, output_file_name, error_reg_string, temp_file_name):
    LEMMA_REG = re.compile(r'^\s*' +
                           r'(?:Local\s+|Global\s+|Polymorphic\s+|Monomorphic\s+)*' +
                           r'(?:Lemma|Remark|Fact|Corollary|Proposition)\s*', re.MULTILINE)
    return try_admit_matching_definitions(definitions, output_file_name, error_reg_string, temp_file_name,
                                          (lambda definition: LEMMA_REG.search(definition['statement'])),
                                          'Admitting lemmas')

def try_admit_definitions(definitions, output_file_name, error_reg_string, temp_file_name):
    return try_admit_matching_definitions(definitions, output_file_name, error_reg_string, temp_file_name,
                                          (lambda definition: True),
                                          'Admitting definitions')






def try_strip_comments(output_file_name, error_reg_string):
    contents = read_from_file(output_file_name)
    contents = strip_comments(contents)
    output = diagnose_error.get_coq_output(contents)
    if diagnose_error.has_error(output, error_reg_string):
        print('\nSucceeded in stripping comments.')
        write_to_file(output_file_name, contents)
    else:
        print('\nNon-fatal error: Failed to strip comments and preserve the error.')
        print('The new error was:')
        print(output)
        print('Stripped comments file not saved.')


def try_strip_extra_lines(output_file_name, line_num, error_reg_string, temp_file_name):
    contents = read_from_file(output_file_name)
    statements = split_coq_file_contents(contents)
    cur_line_num = 0
    new_statements = statements
    for statement_num, statement in enumerate(statements):
        cur_line_num += statement.count('\n')
        if cur_line_num > line_num:
            new_statements = statements[:statement_num + 1]
            break
    output = diagnose_error.get_coq_output('\n'.join(new_statements))
    if diagnose_error.has_error(output, error_reg_string):
        print('Trimming successful.')
        write_to_file(output_file_name, '\n'.join(new_statements))
    else:
        print('Trimming unsuccessful.  Writing trimmed file to %s.  The output was:' % temp_file_name)
        print(output)
        write_to_file(temp_file_name, '\n'.join(new_statements))



if __name__ == '__main__':
    args = parser.parse_args()
    os.chdir(args.directory)
    bug_file_name = args.bug_file.name
    output_file_name = args.output_file
    temp_file_name = args.temp_file
    verbose = args.verbose
    fast = args.fast
    if bug_file_name[-2:] != '.v':
        print('\nError: BUGGY_FILE must end in .v (value: %s)' % bug_file_name)
        sys.exit(1)
    if output_file_name[-2:] != '.v':
        print('\nError: OUT_FILE must end in .v (value: %s)' % output_file_name)
        sys.exit(1)
    remove_temp_file = False
    if temp_file_name == '':
        temp_file = tempfile.NamedTemporaryFile(suffix='.v', dir='.', delete=False)
        temp_file_name = temp_file.name
        temp_file.close()
        remove_temp_file = True
    if temp_file_name[-2:] != '.v':
        print('\nError: TEMP_FILE must end in .v (value: %s)' % temp_file_name)
        sys.exit(1)


    print('\nFirst, I will attempt to inline all of the inputs in %s, and store the result in %s...' % (bug_file_name, output_file_name))
    inlined_contents = include_imports(bug_file_name, verbose=verbose, fast=fast)
    if inlined_contents:
        write_to_file(output_file_name, inlined_contents)
    else:
        print('Failed to inline inputs.')
        sys.exit(1)

    print('\nNow, I will attempt to coq the file, and find the error...')
    error_reg_string = get_error_reg_string(output_file_name)

    print('\nNow, I will try to strip the comments from this file...')
    try_strip_comments(output_file_name, error_reg_string)



    # TODO(jgross): Only display the warning if there seem to be periods in strings.
    print('\nIn order to efficiently manipulate the file, I have to break it into statements.  I will attempt to do this by matching on periods.  If you have periods in strings, and these periods are essential to generating the error, then this process will fail.  Consider replacing the string with some hack to get around having a period and then a space, like ["a. b"%string] with [("a." ++ " b")%string].')
    contents = read_from_file(output_file_name)
    statements = split_coq_file_contents(contents)
    output = diagnose_error.get_coq_output('\n'.join(statements))
    if diagnose_error.has_error(output, error_reg_string):
        print('Splitting successful.')
        write_to_file(output_file_name, '\n'.join(statements))
    else:
        print('Splitting unsuccessful.  I will not be able to proceed.  Writing split file to %s.' % temp_file_name)
        write_to_file(temp_file_name, '\n'.join(statements))
        print('The output given was:')
        print(output)
        sys.exit(1)

    print('\nI will now attempt to remove any lines after the line which generates the error.')
    line_num = diagnose_error.get_error_line_number(output, error_reg_string)
    try_strip_extra_lines(output_file_name, line_num, error_reg_string, temp_file_name)


    print('\nIn order to efficiently manipulate the file, I have to break it into definitions.  I will now attempt to do this.')
    contents = read_from_file(output_file_name)
    statements = split_coq_file_contents(contents)
    definitions = split_statements_to_definitions(statements)
    output = diagnose_error.get_coq_output(join_definitions(definitions))
    if diagnose_error.has_error(output, error_reg_string):
        print('Splitting to definitions successful.')
        write_to_file(output_file_name, join_definitions(definitions))
    else:
        print('Splitting to definitions unsuccessful.  I will not be able to proceed.  Writing split file to %s.' % temp_file_name)
        write_to_file(temp_file_name, join_definitions(definitions))
        print('The output given was:')
        print(output)
        sys.exit(1)



    old_definitions = []
    while join_definitions(old_definitions) != join_definitions(definitions):
        old_definitions = list(definitions)

        print('\nI will now attempt to remove unused Ltacs')
        definitions = try_remove_ltac(definitions, output_file_name, error_reg_string, temp_file_name)

        print('\nI will now attempt to remove unused definitions')
        definitions = try_remove_definitions(definitions, output_file_name, error_reg_string, temp_file_name)

        print('\nI will now attempt to remove unused variables')
        try_remove_variables(definitions, output_file_name, error_reg_string, temp_file_name)

        print('\nI will now attempt to replace Qeds with Admitteds')
        try_admit_qeds(definitions, output_file_name, error_reg_string, temp_file_name)

        print('\nI will now attempt to admit lemmas')
        try_admit_lemmas(definitions, output_file_name, error_reg_string, temp_file_name)

        print('\nI will now attempt to admit definitions')
        try_admit_definitions(definitions, output_file_name, error_reg_string, temp_file_name)

        print('\nI will now attempt to remove hints')
        try_remove_hints(definitions, output_file_name, error_reg_string, temp_file_name)


    if os.path.exists(temp_file_name) and remove_temp_file:
        os.remove(temp_file_name)
