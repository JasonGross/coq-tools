import re

__all__ = ["transform_abstract_to_admit"]

def DEFAULT_LOG(text):
    print(text)

TERM_CHAR = r"[\w']"
ABSTRACT_NO_PARENS_DOT = re.compile(r"(\.\s+|;\s*)abstract\s+(?:[^\(\);\.]|\.%s)+(?=\.\s)" % TERM_CHAR, re.MULTILINE)

def transform_abstract_to_admit_statement(statement, agressive=False, verbose=1, log=DEFAULT_LOG):
    # remove the unparenthesized ones
    statement = ABSTRACT_NO_PARENS_DOT.sub('\1admit', statement)

    # now look at the parenthesized abstracts
    ready_for_abstract = True
    in_abstract = False
    abstract_paren_level = 0
    rtn = []
    cur = []
    for term in re.split('([;\.\(\)])', statement):
        if verbose >= 3:
            log('in_abstract: %d; abstract_paren_level: %d; agressive: %d; ready_for_abstract: %d;\n^term: %s' %
                (in_abstract, abstract_paren_level, agressive, ready_for_abstract, term))
        if in_abstract:
            if abstract_paren_level == 0 and term in ';.':
                if term == ';':
                    if agressive:
                        rtn.append(' admit;')
                        if verbose >= 3: log("Appending ' admit;' to rtn")
                    else:
                        cur.append(term)
                        rtn.append(''.join(cur))
                        if verbose >= 3: log("Appending %s to rtn" % repr(''.join(cur)))
                else:
                    if verbose >= 3: log("Appending ' admit.' to rtn")
                    rtn.append(' admit.')
                in_abstract = False
                cur = []
                if verbose >= 3: log("Setting in_abstract to false and emptying cur")
            elif abstract_paren_level < 0:
                log('Warning: abstract_paren_level messed up on statement %s' % repr(statement))
                in_abstract = False
                cur.append(term)
                rtn.append(''.join(cur))
                cur = []
                abstract_paren_level = 0
                if verbose >= 3: log("Setting in_abstract to false, abstract_paren_level to 0, emptying cur, and\nappending %s to rtn" %
                                     repr(''.join(cur)))
            else:
                if term == '(':
                    abstract_paren_level += 1
                elif term == ')':
                    abstract_paren_level -= 1
                cur.append(term)
                if verbose >= 3: log("Setting abstract_paren_level to %d and\nappending %s to cur" % repr(term))
        else:
            if ready_for_abstract and term.strip() == 'abstract':
                cur.append(term)
                in_abstract = True
                if verbose >= 3: log("Found %s (appending to cur), now in_abstract" % repr(term))
                if abstract_paren_level != 0:
                    log('Warning: abstract_paren_level messed up before abstract on statement %s' % repr(statement))
                    abstract_paren_level = 0
            else:
                if term in '.;':
                    if verbose >= 3: log("Found %s (appending to rtn), ready for abstract" % repr(term))
                    ready_for_abstract = True
                elif term.strip():
                    if verbose >= 3: log("Found %s (appending to rtn), not ready for abstract" % repr(term))
                    ready_for_abstract = False
                rtn.append(term)
    if verbose >= 3: log("Done.  Appending %s to rtn." % repr(''.join(cur)))
    rtn.append(''.join(cur))

    return ''.join(rtn)

def transform_abstract_to_admit(cur_definition, rest_definitions, agressive=False, verbose=1, log=DEFAULT_LOG):
    # shallow copy
    cur_definition = dict(cur_definition)
    cur_definition['statements'] = tuple(transform_abstract_to_admit_statement(i, agressive=agressive, verbose=verbose, log=log)
                                         for i in cur_definition['statements'])
    cur_definition['statement'] = '\n'.join(cur_definition['statements'])
    return cur_definition
