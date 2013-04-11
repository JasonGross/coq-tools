import re

__all__ = ["admit_definitions", "LEMMAS", "DEFINITIONS", "ALL"]

PREFIXES = '(?:Polymorphic\s+|Monomorphic\s+|Local\s+|Global\s+)?'
LEMMAS = 'Lemma|Remark|Fact|Corollary|Proposition'
DEFINITIONS = 'Definition|Example|Fixpoint|CoFixpoint'
ALL = '%s|%s' % (LEMMAS, DEFINITIONS)
END_REG = re.compile(r'\b(?:Qed|Defined|Admitted)\s*\.\s*$', re.MULTILINE)

def has_colon_equals(statement):
    """Returns True if the statment is of the form [Definition foo :
    bar := baz.] or [Definition foo := baz.], etc.  Returns False if
    the statement is of the form [Definition foo : bar.].

    Precondition: statement has no comments in it; statement is a
    definition/lemma/etc; statement does not use any notations with
    unbalanced parens or curly braces."""
    # first, remove any strings
    statement = re.sub('"[^"]+"', '', statement)
    # now, repeatedly remove parens
    old_statement = ''
    while old_statement != statement:
        old_statement = statement
        statement = re.sub(r'\([^()]+\)', ' ', statement)
    # now, repeatedly remove curlies
    old_statement = ''
    while old_statement != statement:
        old_statement = statement
        statement = re.sub(r'{[^()]+}', ' ', statement)
    # now, we need to remove let ... in.  We already removed parens, so there may not be anything
    statement = re.sub(r"\blet\b\s*[\w']*\s*:=", '', statement)
    return ':=' in statement

def admit_definitions(statements, check_statements, type_reg=ALL, exclude_n=3, debug=False):
    """Attempts to [Admitted] each definition (anything matching
       type_reg), and keeps the admits which pass check_statements.
       Does not remove any code in the last exclude_n statements."""
    rtn = list(reversed(statements))[:exclude_n]
    reg = re.compile(r'^\s*%s(?:%s)\s+([^\s]+)' % (PREFIXES, type_reg), re.MULTILINE)
    definition_level = 0
    most_recent_definition_statements = []
    for statement_n, statement in list(reversed(list(enumerate(statements))))[exclude_n:]:
        if debug: print('Statement: %s' % statement)
        if END_REG.search(statement):
            definition_level += 1
            if debug: print('matches end, new_level: %d' % definition_level)
            if len(most_recent_definition_statements) < definition_level:
                most_recent_definition_statements.append([])
            most_recent_definition_statements[definition_level - 1].append(statement)
            if debug: print('list: %s' % str(most_recent_definition_statements[definition_level - 1]))
        else:
            if debug: print('does not match end')
            if definition_level > 0:
                if debug: print('in definition')
                match = reg.search(statement)
                if match:
                    name = match.groups()[0]
                    if debug: print('matches begin, name: %s' % name)
                    # search for the name, by itself
                    name_reg = re.compile(r"(?<![\w'])%s(?![\w'])" % name, re.MULTILINE)
                    if has_colon_equals(statement):
                        if debug: print('has :=')
                        if any(name_reg.search(other_statement) for other_statement in rtn):
                            if debug: print('name found')
                            rtn.append(statement)
                        else:
                            if debug: print('name not found')
                    else:
                        if any(name_reg.search(other_statement) for other_statement in rtn):
                            if debug: print('name found')
                            if definition_level > 2:
                                most_recent_definition_statements[definition_level - 2] += most_recent_definition_statements[definition_level - 1]
                                most_recent_definition_statements[definition_level - 2].append(statement)
                            else:
                                try_statements = statements[:statement_n] + \
                                    list(reversed(rtn +
                                                  [most_recent_definition_statements[definition_level - 1][0],
                                                   '\nAdmitted.\n']))
                                if check_statements(try_statements):
                                    rtn += [most_recent_definition_statements[definition_level - 1][0],
                                            '\nAdmitted.\n']
                                else:
                                    rtn += most_recent_definition_statements[definition_level - 1]
                                    rtn.append(statement)
                            most_recent_definition_statements[definition_level - 1] = []
                        else:
                            if debug: print('name not found')
                        definition_level -= 1
                        if debug: print('new definition level: %d' % definition_level)
                else:
                    if debug: print('no match')
                    most_recent_definition_statements[definition_level - 1].append(statement)
            else:
                if debug: print('not in definition')
                match = reg.search(statement)
                if match:
                    name = match.groups()[0]
                    if debug: print('matches begin, name: %s' % name)
                    # search for the name, by itself
                    name_reg = re.compile(r"(?<![\w'])%s(?![\w'])" % name, re.MULTILINE)
                    if has_colon_equals(statement):
                        if debug: print('has :=')
                        if any(name_reg.search(other_statement) for other_statement in rtn):
                            if debug: print('name found')
                            rtn.append(statement)
                        else:
                            if debug: print('name not found')
                    else:
                        if debug: print('wtf?')
                else:
                    if debug: print('no match')
                    rtn.append(statement)
    return list(reversed(rtn))
