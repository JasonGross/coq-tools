import re

__all__ = ["recursively_remove_ltac"]

LTAC_REG = re.compile(r'^\s*(?:Local\s+|Global\s+)?Ltac\s+([^\s]+)', re.MULTILINE)

def recursively_remove_ltac(statements, exclude_n=3):
    """Removes any Ltac statement which is not used later in
    statements.  Does not remove any code in the last exclude_n
    statements."""
    # TODO(jgross): Figure out what the optimal exclude_n is.  It's
    # probably 1 or 2, but I don't want to accidentally exclude the
    # line generating the bug, so I'm trying to be a bit safer
    rtn = list(reversed(statements))[:exclude_n]
    for statement in list(reversed(statements))[exclude_n:]:
        match = LTAC_REG.search(statement.replace(':=', ' := '))
        if match:
            ltac_name = match.groups()[0]
            # search for the name of the tactic, by itself
            reg = re.compile(r"(?<![\w'])%s(?![\w'])" % ltac_name, re.MULTILINE)
            if any(reg.search(other_statement) for other_statement in rtn):
                rtn.append(statement)
        else:
            rtn.append(statement)
    return list(reversed(rtn))
