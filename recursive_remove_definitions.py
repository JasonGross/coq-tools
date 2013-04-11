import re

__all__ = ["recursively_remove_definitions", "LEMMAS", "DEFINITIONS", "ALL"]

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

def recursively_remove_definitions(statements, type_reg=ALL, exclude_n=3, debug=False):
    """Removes any definition (anything matching type_reg) which is not
    used later in statements.  Does not remove any code in the last
    exclude_n statements."""
    rtn = list(reversed(statements))[:exclude_n]
    reg = re.compile(r'^\s*%s(?:%s)\s+([^\s]+)' % (PREFIXES, type_reg), re.MULTILINE)
    definition_level = 0
    for statement in list(reversed(statements))[exclude_n:]:
        if debug: print('Statement: %s' % statement)
        match = reg.search(statement)
        if match:
            if debug: print('matches')
            name = match.groups()[0]
            # search for the name, by itself
            name_reg = re.compile(r"(?<![\w'])%s(?![\w'])" % name, re.MULTILINE)
            if debug: print('name: %s' % name)
            if any(name_reg.search(other_statement) for other_statement in rtn):
                if debug: print('name found')
                if debug: print('appending statement')
                rtn.append(statement)
            elif not has_colon_equals(statement):
                if debug: print('name not found, not has :=')
                definition_level += 1
            else:
                if debug:
                    for other_statement in rtn:
                        print(r're.search(r"(?<![\w\'])%s(?![\w\'])", %s, re.MULTILINE)' % (name, repr(other_statement)))
                        print(re.search(r"(?<![\w'])%s(?![\w'])" % name, other_statement, re.MULTILINE))
                        print(name_reg.search(other_statement, re.MULTILINE))
                    print('name not found, has :=')
        elif definition_level > 0:
            if END_REG.search(statement):
                if debug: print('end of definition')
                definition_level -= 1
        else:
            if debug: print('appending statement')
            rtn.append(statement)
    return list(reversed(rtn))
