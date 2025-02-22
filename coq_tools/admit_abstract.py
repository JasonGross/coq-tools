import re

__all__ = ["transform_abstract_to_admit"]


def DEFAULT_LOG(text, level=1):
    if level <= 1:
        print(text)


TERM_CHAR = r"[\w']"
ABSTRACT_NO_PARENS_DOT = re.compile(
    r"(^\s*|\.\s+|;\s*)abstract\s+(?:[^\(\);\.]|\.%s)+(?=\.\s|\.$)" % TERM_CHAR, re.MULTILINE
)


def transform_abstract_to_admit_statement(statement, aggressive=False, log=DEFAULT_LOG):
    # remove the unparenthesized ones
    statement = ABSTRACT_NO_PARENS_DOT.sub(r"\1admit", statement)

    if "abstract" not in statement:
        return statement

    # now look at the parenthesized abstracts
    ready_for_abstract = True
    in_abstract = False
    abstract_paren_level = 0
    rtn = []
    cur = []
    for term in re.split("([;\.\(\)])", statement):
        log(
            "in_abstract: %d; abstract_paren_level: %d; aggressive: %d; ready_for_abstract: %d;\n^term: %s"
            % (in_abstract, abstract_paren_level, aggressive, ready_for_abstract, term),
            level=3,
        )
        if in_abstract:
            if abstract_paren_level == 0 and term in tuple(";."):
                if term == ";":
                    if aggressive:
                        rtn.append(" admit;")
                        log("Appending ' admit;' to rtn", level=3)
                    else:
                        cur.append(term)
                        rtn.append("".join(cur))
                        log("Appending %s to rtn" % repr("".join(cur)), level=3)
                else:
                    log("Appending ' admit.' to rtn", level=3)
                    rtn.append(" admit.")
                in_abstract = False
                cur = []
                log("Setting in_abstract to false and emptying cur", level=3)
            elif abstract_paren_level < 0:
                log("Warning: abstract_paren_level messed up on statement %s" % repr(statement))
                in_abstract = False
                cur.append(term)
                rtn.append("".join(cur))
                cur = []
                abstract_paren_level = 0
                log(
                    "Setting in_abstract to false, abstract_paren_level to 0, emptying cur, and\nappending %s to rtn"
                    % repr("".join(cur)),
                    level=3,
                )
            else:
                if term == "(":
                    abstract_paren_level += 1
                elif term == ")":
                    abstract_paren_level -= 1
                cur.append(term)
                log(
                    "Setting abstract_paren_level to %d and\nappending %s to cur" % (abstract_paren_level, repr(term)),
                    level=3,
                )
        else:
            if ready_for_abstract and term.strip() == "abstract":
                cur.append(term)
                in_abstract = True
                log("Found %s (appending to cur), now in_abstract" % repr(term), level=3)
                if abstract_paren_level != 0:
                    log("Warning: abstract_paren_level messed up before abstract on statement %s" % repr(statement))
                    abstract_paren_level = 0
            else:
                if term in tuple(".;"):
                    log("Found %s (appending to rtn), ready for abstract" % repr(term), level=3)
                    ready_for_abstract = True
                elif term.strip():
                    log("Found %s (appending to rtn), not ready for abstract" % repr(term), level=3)
                    ready_for_abstract = False
                rtn.append(term)
    log("Done.  Appending %s to rtn." % repr("".join(cur)), level=3)
    rtn.append("".join(cur))

    return "".join(rtn)


def transform_abstract_to_admit(cur_definition, rest_definitions, **kwargs):
    # shallow copy
    cur_definition = dict(cur_definition)
    cur_definition["statements"] = tuple(
        transform_abstract_to_admit_statement(i, **kwargs) for i in cur_definition["statements"]
    )
    cur_definition["statement"] = "\n".join(cur_definition["statements"])
    return cur_definition
