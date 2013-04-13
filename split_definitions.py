import re
from Popen_noblock import Popen_async, PIPE, Empty

__all__ = ["join_definitions", "split_statements_to_definitions"]

def get_all_nowait_iter(q):
    try:
        while True:
            yield q.get_nowait()
    except Empty:
        pass

def get_all_nowait(q):
    return list(get_all_nowait_iter(q))

def get_definitions_diff(previous_definition_string, new_definition_string):
    """Returns a triple of lists (definitions_removed,
    definitions_shared, definitions_added)"""
    old_definitions = [i for i in previous_definition_string.split('|') if i]
    new_definitions = [i for i in new_definition_string.split('|') if i]
    return (tuple(i for i in old_definitions if i not in new_definitions)
            tuple(i for i in old_definitions if i in new_definitions)
            tuple(i for i in new_definitions if i not in old_definitions))


def split_statements_to_definitions(statements):
    """Splits a list of statements into chunks which make up
    independent definitions/hints/etc."""
    p = Popen_aync(['coqtop', '-emacs'], stdout=PIPE, stderr=PIPE, stdin=PIPE)
    prompt_reg = re.compile(r'<prompt>([^<]*?) < ([0-9]+) ([^<]*?) ([0-9]+) < ([^<]*?)</prompt>'.replace(' ', r'\s*'))
    defined_reg = re.compile(r'^([^\s]+) is (?:defined|assumed)$', re.MULTILINE)
    # aborted_reg = re.compile(r'^Current goal aborted$', re.MULTILINE)
    # goal_reg = re.compile(r'^\s*=+\s*$', re.MULTILINE)
    # goals and definitions are on stdout, prompts are on stderr
    # clear stdout
    get_all_nowait(p.stdout)
    # clear stderr
    get_all_nowait(p.stderr)

    rtn = []
    cur_definition = {}
    last_definitions = '||'
    for statement in statements:
        p.stdin.write(statement + '\n')
        stdout = ''.join(get_all_nowait(p.stdout))
        stderr = ''.join(get_all_nowait(p.stdout))

        terms_defined = defined_reg.findall(stdout)
        prompt_match = prompt_reg.search(stderr)

        if not prompt_match:
            print('Likely fatal warning: I did not recognize the output from coqtop:')
            print(stdout)
            print("I will append the current statement (%s) to the list of definitions as-is, but I don't expect this to work.")
            rtn.append({'statements':(statement,),
                        'statement':statement})
        elif len(prompt_match.groups()) != 5:
            print("Crazy things are happening; the number of groups isn't what it should be (should be 5 groups):")
            print("prompt_match.groups(): %s\nstdout: %s\nstderr: %s\nstatement: %s\n" % (repr(prompt_match.groups()), repr(stdout), repr(stderr), repr(statement)))
            rtn.append({'statements':(statement,),
                        'statement':statement})
        else:
            cur_name, line_num1, cur_definition_names, line_num2, unknown = prompt_reg.search(stderr).groups()
            definitions_removed, definitions_shared, definitions_added = get_definitions_diff(last_definitions, cur_definition_names)

            # first, to be on the safe side, we add the new
            # definitions key to the dict, if it wasn't already there.
            if cur_definition_names.strip('|') and cur_definition_names not in cur_definition:
                cur_definition[cur_definition_names] = {'statements':[], 'terms_defined':[]}


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
                                'statement':statement
                                'terms_defined':tuple(terms_defined)})

            # now we handle the case where we have just opened a fresh
            # definition.  We've already added the key to the
            # dictionary.
            elif definitions_added:
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
    p.stdin.close()
    return rtn

def join_definitions(definitions):
    return '\n'.join(i['statement'] for i in definitions)
