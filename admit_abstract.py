import re

__all__ = ["transform_abstract_to_admit"]

TERM_CHAR = r"[\w']"
ABSTRACT = re.compile(r"(<=\.\s+|;\s*)abstract[\s\(]", re.MULTILINE)
ABSTRACT_PARENS = re.compile(r"(<=\.\s+|;\s*)abstract\s*(\(.+\))\s*(?=\.\s)", re.MULTILINE)
ABSTRACT_NO_PARENS_DOT = re.compile(r"(?<=\.\s+|;\s*)abstract\s+(?:[^\(\);\.]|\.%s)+(?=\.\s)" % TERM_CHAR, re.MULTILINE)

def transform_abstract_to_admit_statement(statement, agressive=False):
    # remove the unparenthesized ones
    statement = ABSTRACT_NO_PARENS_DOT.sub('admit', statement)

    # now look at the parenthesized abstracts
    ready_for_abstract = True
    in_abstract = False
    abstract_paren_level = 0
    rtn = []
    cur = []
    for term in re.split('([;\.\(\)])', statement):
        if in_abstract:
            if abstract_paren_level == 0 and term in ';.':
                if term == ';':
                    if agressive:
                        rtn.append('admit;')
                    else:
                        cur.append(term)
                        rtn.append(''.join(cur))
                else:
                    rtn.append('admit.')
                in_abstract = False
                cur = []
            elif abstract_paren_level < 0:
                print('Warning: abstract_paren_level messed up on statement %s' % repr(statement))
                in_abstract = False
                cur.append(term)
                rtn.append(''.join(cur))
                cur = []
                abstract_paren_level = 0
            else:
                if term == '(':
                    abstract_paren_level += 1
                elif term == ')':
                    abstract_paren_level -= 1
                cur.append(term)
        else:
            if ready_for_abstract and term.strip() == 'abstract':
                cur.append(term)
                in_abstract = True
                if abstract_paren_level != 0:
                    print('Warning: abstract_paren_level messed up before abstract on statement %s' % repr(statement))
                    abstract_paren_level = 0
            else:
                rtn.append(term)
    rtn.append(''.join(cur))

    return rtn

def transform_abstract_to_admit(cur_definition, rest_definitions, agressive=False):
    # shallow copy
    cur_definition = dict(cur_definition)
    cur_definition['statements'] = tuple(transform_abstract_to_admit_statement(i) for i in cur_definition['statements'])
    cur_definition['statement'] = '\n'.join(cur_definition['statements'])
    return cur_definition
