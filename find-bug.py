#!/usr/bin/env python
import argparse, tempfile, sys, os, re
from replace_imports import include_imports
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
        print('Coqing the file...')
        contents = read_from_file(output_file_name)
        output = diagnose_error.get_coq_output(contents)
        result = ''
        print("This file produces the following output when Coq'ed:")
        print(output)
        while result not in ('y', 'n', 'yes', 'no'):
            result = raw_input('Does this output display the correct error? [(y)es/(n)o] ').lower().strip()
        if result in ('n', 'no'):
            raw_input('Please modify the file so that it errors correctly, and then press ENTER to continue, or ^C to break.')
            continue

        if diagnose_error.has_error(output):
            error_string = diagnose_error.get_error_string(output)
            error_reg_string = diagnose_error.make_reg_string(output)
            print("I think the error is '%s'." % error_string)
            print("The corresponding regular expression is %s." % repr(error_reg_string))
            result = ''
            while result not in ('y', 'n', 'yes', 'no'):
                result = raw_input('Is this correct? [(y)es/(n)o] ').lower().strip()
            if result in ('no', 'n'):
                error_reg_string = ''
        else:
            print('The current state of the file does not have a recognizable error.')

        if error_reg_string == '':
            error_reg_string = raw_input('Please enter a regular expression which matches on the output.  Leave blank to re-coq the file. ')

        while (error_reg_string != ''
               and (not re.search(error_reg_string, output)
                    or len(re.search(error_reg_string, output).groups()) != 2)):
            if not re.search(error_reg_string, output):
                print('The given regular expression does not match the output.')
            elif len(re.search(error_reg_string, output).groups()) != 2:
                print('The given regular expression does not have two groups.')
                print('It must have one integer group which matches on the line number,')
                print('and another group which matches on the error string.')
            error_reg_string = raw_input('Please enter a valid regular expression which matches on the output.  Leave blank to re-coq the file. ')

        if error_reg_string == '':
            continue

    return error_reg_string



if __name__ == '__main__':
    args = parser.parse_args()
    os.chdir(args.directory)
    bug_file_name = args.bug_file.name
    output_file_name = args.output_file
    temp_file_name = args.temp_file
    verbose = args.verbose
    fast = args.fast
    if bug_file_name[-2:] != '.v':
        print('Error: BUGGY_FILE must end in .v (value: %s)' % bug_file_name)
        sys.exit(1)
    if output_file_name[-2:] != '.v':
        print('Error: OUT_FILE must end in .v (value: %s)' % output_file_name)
        sys.exit(1)
    if temp_file_name == '':
        temp_file = tempfile.NamedTemporaryFile(suffix='.v', dir='.', delete=False)
        temp_file_name = temp_file.name
        temp_file.close()
    if temp_file_name[-2:] != '.v':
        print('Error: TEMP_FILE must end in .v (value: %s)' % temp_file_name)
        sys.exit(1)


    print('First, I will attempt to inline all of the inputs in %s, and store the result in %s...' % (bug_file_name, output_file_name))
    inlined_contents = include_imports(bug_file_name, verbose=verbose, fast=fast)
    if inlined_contents:
        write_to_file(output_file_name, inlined_contents)
    else:
        print('Failed to inline inputs.')
        sys.exit(1)

    print('Now, I will attempt to coq the file, and find the error...')
    error_reg_string = get_error_reg_string(output_file_name)



    if os.path.exists(temp_file_name):
        os.remove(temp_file_name)
