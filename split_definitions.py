import re
from Popen_noblock import Popen_async, PIPE, Empty

def get_all_nowait_iter(q):
    try:
        while True:
            yield q.get_nowait()
    except Empty:
        pass

def get_all_nowait(q):
    return list(get_all_nowait_iter(q))

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
            if len(terms_defined) > 0:
                if cur_definition_names == last_definitions: # one-line definitions
                    rtn.append({'statements':(statement,),
                                'statement':statement,
                                'terms_defined':tuple(terms_defined)})
                else:
                    new_terms = cur_definition_names[1:] # should be shorter, since we just defined some things
                    old_terms = last_definitions[1:-len(new_terms)] # should be longer
                    if new_terms + old_terms != last_definitions[1:]:
                        print("Likely fatal error: I could not parse the terms being defined")
                        print("last_definitions: %s\ncur_definition_names: %s\nnew_terms: %s\nold_terms: %s" % (last_definitions, cur_definition_names, new_terms, old_terms))
                        print("Some statements will likely be lost")
                    elif cur_definition_names.strip('|'): # we've nested definitions
                        # just drop down a level
                        cur_definition[cur_definition_names]['statements'] += cur_definition[last_definitions]['statements'] + [statement]
                        cur_definition[cur_definition_names]['terms_defined'] += cur_definition[last_definitions]['terms_defined'] + list(terms_defined)
                        del cur_definition[last_definitions]
                    else: # we just ended a top-level definition
                        cur_definition[last_definitions]['statements'].append(statement)
                        cur_definition[last_definitions]['terms_defined'] += list(terms_defined)
                        rtn.append({'statements':tuple(cur_definition[last_definitions]['statements']),
                                    'statement':'\n'.join(cur_definition[last_definitions]['statements']),
                                    'terms_defined':tuple(cur_definition[last_definitions]['terms_defined'])})
                        del cur_definition[last_definitions]
            else: # we've not defined any terms here
                if not cur_definition_names.strip('|'):
                    # we're at top level, and haven't opened a
                    # definition, so just append the statement
                    rtn.append({'statements':(statement,),
                                'statement':statement})
                elif cur_definition_names == last_definitions:
                    # we're not at top level, but we haven't changed
                    # definitions, so append the statement to the
                    # currently open definition
                    cur_definition[cur_definition_names]['statements'].append(statement)
                elif len(cur_definition_names) > len(last_definitions):
                    # we've just opened a new definition term
                    old_terms = last_definitions[1:] # should be shorter
                    new_terms = cur_definition_names[1:-len(old_terms)] # should be longer, since we just added something
                    if new_terms + old_terms != cur_definition_names[1:]
                        print("Likely fatal error: I could not parse the terms being defined")
                        print("last_definitions: %s\ncur_definition_names: %s\nnew_terms: %s\nold_terms: %s" % (last_definitions, cur_definition_names, new_terms, old_terms))
                        print("Some statements will likely be lost")
                    elif
                    elif cur_definition_names.strip('|'): # we've nested definitions
                        # just drop down a level
                        cur_definition[cur_definition_names]['statements'] += cur_definition[last_definitions]['statements'] + [statement]
                        cur_definition[cur_definition_names]['terms_defined'] += cur_definition[last_definitions]['terms_defined'] + list(terms_defined)
                        del cur_definition[last_definitions]
                    else: # we just ended a top-level definition
                        cur_definition[last_definitions]['statements'].append(statement)
                        cur_definition[last_definitions]['terms_defined'] += list(terms_defined)
                        rtn.append({'statements':tuple(cur_definition[last_definitions]['statements']),
                                    'statement':'\n'.join(cur_definition[last_definitions]['statements']),
                                    'terms_defined':tuple(cur_definition[last_definitions]['terms_defined'])})
                        del cur_definition[last_definitions]


                if cur_definition_names == last_definitions:



        if terms_defined:
            if


        if is_defining and len(terms_defined) > 0: # we were defining something, but now we're done
            cur.append(statement)
            rtn.append({'statement':'\n'.join(cur),
                        'statements':tuple(cur),
                        'terms_defined':tuple(terms_defined)})
            cur = []
            is_defining = False
        elif is_defining and goal_aborted
