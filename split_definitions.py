import re, time
from subprocess import Popen, PIPE, STDOUT
import split_definitions_old

__all__ = ["join_definitions", "split_statements_to_definitions"]

DEFAULT_VERBOSITY=1

def DEFAULT_LOG(text):
    print(text)

def get_definitions_diff(previous_definition_string, new_definition_string):
    """Returns a triple of lists (definitions_removed,
    definitions_shared, definitions_added)"""
    old_definitions = [i for i in previous_definition_string.split('|') if i]
    new_definitions = [i for i in new_definition_string.split('|') if i]
    return (tuple(i for i in old_definitions if i not in new_definitions),
            tuple(i for i in old_definitions if i in new_definitions),
            tuple(i for i in new_definitions if i not in old_definitions))

def strip_newlines(string):
    if not string: return string
    if string[0] == '\n': return string[1:]
    if string[-1] == '\n': return string[:-1]
    return string

def split_statements_to_definitions(statements, verbose=DEFAULT_VERBOSITY, log=DEFAULT_LOG, coqtop='coqtop', coqtop_args=tuple(), **kwargs):
    """Splits a list of statements into chunks which make up
    independent definitions/hints/etc."""
    def fallback():
        if verbose: log("Your version of coqtop doesn't support -time.  Falling back to more error-prone method.")
        return split_definitions_old.split_statements_to_definitions(statements, verbose=verbose, log=log, coqtop=coqtop, coqtop_args=coqtop_args)
    # check for -time
    p = Popen([coqtop, '-help'], stdout=PIPE, stderr=STDOUT, stdin=PIPE)
    (stdout, stderr) = p.communicate()
    if '-time' not in stdout:
        return fallback()
    p = Popen([coqtop, '-emacs', '-q', '-time'] + list(coqtop_args), stdout=PIPE, stderr=STDOUT, stdin=PIPE)
    split_reg = re.compile(r'Chars ([0-9]+) - ([0-9]+) [^\s]+ (.*?)<prompt>([^<]*?) < ([0-9]+) ([^<]*?) ([0-9]+) < ([^<]*?)</prompt>'.replace(' ', r'\s*'),
                           flags=re.DOTALL)
    defined_reg = re.compile(r'^([^\s]+) is (?:defined|assumed)$', re.MULTILINE)
    # goals and definitions are on stdout, prompts are on stderr
    statements_string = '\n'.join(statements) + '\n\n'
    if verbose: log('Sending statements to coqtop...')
    if verbose >= 3: log(statements_string)
    (stdout, stderr) = p.communicate(input=statements_string)
    if 'know what to do with -time' in stdout.strip().split('\n')[0]:
        # we're using a version of coqtop that doesn't support -time
        return fallback()
    if verbose: log('Done.  Splitting to definitions...')

    rtn = []
    cur_definition = {}
    last_definitions = '||'
    cur_definition_names = '||'
    last_char_end = 0

    #if verbose >= 3: log('re.findall(' + repr(r'Chars ([0-9]+) - ([0-9]+) [^\s]+ (.*?)<prompt>([^<]*?) < ([0-9]+) ([^<]*?) ([0-9]+) < ([^<]*?)</prompt>'.replace(' ', r'\s*')) + ', ' + repr(stdout) + ', ' + 'flags=re.DOTALL)')
    responses = split_reg.findall(stdout)
    for char_start, char_end, response_text, cur_name, line_num1, cur_definition_names, line_num2, unknown in responses:
        char_start, char_end = int(char_start), int(char_end)
        statement = strip_newlines(statements_string[last_char_end:char_end])
        last_char_end = char_end

        terms_defined = defined_reg.findall(response_text)

        definitions_removed, definitions_shared, definitions_added = get_definitions_diff(last_definitions, cur_definition_names)

        # first, to be on the safe side, we add the new
        # definitions key to the dict, if it wasn't already there.
        if cur_definition_names.strip('|') and cur_definition_names not in cur_definition:
            cur_definition[cur_definition_names] = {'statements':[], 'terms_defined':[]}


        if verbose >= 2: log((statement, (char_start, char_end), terms_defined, last_definitions, cur_definition_names, cur_definition.get(last_definitions, []), cur_definition.get(cur_definition_names, []), response_text))


        # first, we handle the case where we have just finished
        # defining something.  This should correspond to
        # len(definitions_removed) > 0 and len(terms_defined) > 0.
        # If only len(definitions_removed) > 0, then we have
        # aborted something.  If only len(terms_defined) > 0, then
        # we have defined something with a one-liner.
        if definitions_removed:
            cur_definition[last_definitions]['statements'].append(statement)
            cur_definition[last_definitions]['terms_defined'] += terms_defined
            if cur_definition_names.strip('|'):
                # we are still inside a definition.  For now, we
                # flatten all definitions.
                #
                # TODO(jgross): Come up with a better story for
                # nested definitions.
                cur_definition[cur_definition_names]['statements'] += cur_definition[last_definitions]['statements']
                cur_definition[cur_definition_names]['terms_defined'] += cur_definition[last_definitions]['terms_defined']
                del cur_definition[last_definitions]
            else:
                # we're at top-level, so add this as a new
                # definition
                rtn.append({'statements':tuple(cur_definition[last_definitions]['statements']),
                            'statement':'\n'.join(cur_definition[last_definitions]['statements']),
                            'terms_defined':tuple(cur_definition[last_definitions]['terms_defined'])})
                del cur_definition[last_definitions]
                # print('Adding:')
                # print(rtn[-1])
        elif terms_defined:
            if cur_definition_names.strip('|'):
                # we are still inside a definition.  For now, we
                # flatten all definitions.
                #
                # TODO(jgross): Come up with a better story for
                # nested definitions.
                cur_definition[cur_definition_names]['statements'].append(statement)
                cur_definition[cur_definition_names]['terms_defined'] += terms_defined
            else:
                # we're at top level, so add this as a new
                # definition
                rtn.append({'statements':(statement,),
                            'statement':statement,
                            'terms_defined':tuple(terms_defined)})

        # now we handle the case where we have just opened a fresh
        # definition.  We've already added the key to the
        # dictionary.
        elif definitions_added:
            # print(definitions_added)
            cur_definition[cur_definition_names]['statements'].append(statement)
        else:
            # if we're in a definition, append the statement to
            # the queue, otherwise, just add it as it's own
            # statement
            if cur_definition_names.strip('|'):
                cur_definition[cur_definition_names]['statements'].append(statement)
            else:
                rtn.append({'statements':(statement,),
                            'statement':statement,
                            'terms_defined':tuple()})

        last_definitions = cur_definition_names

    if verbose >= 2: log((last_definitions, cur_definition_names))
    if last_definitions.strip('||'):
        rtn.append({'statements':tuple(cur_definition[cur_definition_names]['statements']),
                    'statement':'\n'.join(cur_definition[cur_definition_names]['statements']),
                    'terms_defined':tuple(cur_definition[cur_definition_names]['terms_defined'])})
        del cur_definition[last_definitions]

    if last_char_end + 1 < len(statements_string):
        if verbose >= 2: log('Appending end of code from %d to %d: %s' % (last_char_end, len(statements_string), statements_string[last_char_end:]))
        last_statement = strip_newlines(statements_string[last_char_end:])
        rtn.append({'statements':tuple(last_statement,),
                    'statement':last_statement,
                    'terms_defined':tuple()})

    return rtn

def join_definitions(definitions):
    return '\n'.join(i['statement'] for i in definitions)
