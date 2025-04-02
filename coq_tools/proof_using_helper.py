#!/usr/bin/env python
from __future__ import with_statement
import os, sys, re
from .argparse_compat import argparse
from .custom_arguments import (
    add_libname_arguments,
    update_env_with_libnames,
    add_logging_arguments,
    process_logging_arguments,
    get_parser_name_mapping,
    LOG_ALWAYS,
)
from .file_util import read_from_file, write_to_file

__all__ = ["main"]

# TODO:
# - handle fake ambiguities from [Definition foo] in a comment
# - handle theorems inside proof blocks
# - do the right thing for [Theorem foo. Theorem bar. Proof. Qed. Qed.] (we do the wrong thing right now)
# - make use of glob file?

parser = argparse.ArgumentParser(description="Implement the suggestions of [Set Suggest Proof Using.]")
parser.add_argument(
    "source",
    metavar="SOURCE_FILE",
    type=argparse.FileType("r"),
    nargs="?",
    default=sys.stdin,
    help="the source of set suggest proof using messages; use - for stdin.",
)
parser.add_argument(
    "--hide",
    dest="hide_reg",
    nargs="*",
    type=str,
    default=[".*_subproof[0-9]*$"],  # , '.*_Proper$'],
    help=(
        "Regular expressions to not display warnings about on low verbosity.  "
        + "[Set Suggest Proof Using] can give suggestions about hard-to-find "
        + "identifiers, and we might want to surpress them."
    ),
)
parser.add_argument("--no-hide", dest="hide_reg", action="store_const", const=[])
add_libname_arguments(parser)
add_logging_arguments(parser)


def mwrite_to_file(file_name, contents, do_backup=False):
    return write_to_file(file_name, contents, do_backup=do_backup, memoize=True)


REG_PROOF_USING = re.compile(
    r"The proof of ([^\s]+)\s*should start with(?: one of the following commands)?:((?:\s*Proof using[^\.]+\.)+)",
    re.MULTILINE,
)
REG_SUB_PROOF_USING = re.compile(r"Proof using[^\.]+\.", re.MULTILINE)

# def all_matches(reg, source, start='', **env):
#    source_text = ''
#    for i in source:
#        if source_text[:len(start)] != start:
#            source_text = ''
#        source_text += i
#        cur_match = reg.search(source_text)
#        while cur_match:
#            ignoring = source_text[:cur_match.start()].strip()
#            if ignoring:
#                env['log']('Ignoring: ' + repr(ignoring), level=3)
#            yield cur_match.groups()
#            source_text = source_text[cur_match.end():]
#            cur_match = reg.search(source_text)


def pick_suggestion(suggestions):
    for i in ("Proof using Type.", "Proof using.", "Proof using .", "Proof using Type*."):
        if i in suggestions:
            return i
    return suggestions[0]


def lib_to_dir_map(libnames):
    return dict((lib, dirname) for dirname, lib in libnames)


def split_to_file_and_rest(theorem_id, **kwargs):
    module_part, rest_part = theorem_id.split("#", 1)
    module_parts = module_part.split(".")
    ret = []
    rest_parts = []
    while len(module_parts) > 0:
        rest_parts.insert(0, module_parts.pop())
        if ".".join(module_parts) in kwargs["lib_to_dir"].keys():
            dirname = kwargs["lib_to_dir"][".".join(module_parts)]
        elif ".".join(module_parts) == "":
            dirname = "."
        else:
            continue
        for split_i in range(0, len(rest_parts)):
            filename = os.path.join(dirname, *(rest_parts[:split_i] + [rest_parts[split_i] + ".v"]))
            if os.path.exists(filename):
                ret.append((filename, (".".join(rest_parts[split_i + 1 :]) + "#" + rest_part).strip("#")))
    return tuple(ret)


ALL_DEFINITIONS = (
    "Theorem",
    "Lemma",
    "Fact",
    "Remark",
    "Corollary",
    "Proposition",
    "Property",
    "Definition",
    "Example",
    "SubClass",
    "Let",
    "Fixpoint",
    "CoFixpoint",
    "Structure",
    "Coercion",
    "Instance",
    "Existing Instance",
)
ALL_DEFINITIONS_STR = r"[ \t]*(?:" + "|".join(ALL_DEFINITIONS) + r")\s+%s(?=[\s\(:{\.]|$)"

ALL_DEFINITIONS_LESS_PROPER_STR = (
    r"[ \t]*(?:Global\s+|Local\s+)?(?:"
    + r"Add\s+(?:Parametric\s+)?Morphism"
    + r")\s+(?:[^\.]+|\.[A-Za-z\(\)])+\.(?:\n|$)"
)

ALL_DEFINITIONS_QUICK = (
    r"Theorem",
    "Lemma",
    "Fact",
    "Remark",
    "Corollary",
    "Proposition",
    "Property",
    "Definition",
    "Example",
    "SubClass",
    "Let",
    "Fixpoint",
    "CoFixpoint" "Structure",
    "Coercion",
    "Instance",
    "Add Parametric Morphism",
)
ALL_DEFINITIONS_STR_QUICK = r"(?:" + "|".join(ALL_DEFINITIONS_QUICK) + r")\s+%s"


ALL_DEFINITIONS_FULL_STRS = (
    r"^([ \t]*)(" + ALL_DEFINITIONS_STR_QUICK + r"[^\.]+\.\n)",
    r"^([ \t]*)(" + ALL_DEFINITIONS_STR_QUICK + r"(?:[^\.]+|\.[A-Za-z\(\)])+\.\n)",
)

ALL_DEFINITIONS_FULL_STRS_LESS_PROPER = (
    r"^([ \t]*)((?:Global\s+|Local\s+)?Add\s+(?:Parametric\s+)?Morphism\s+(?:[^\.]+|\.[A-Za-z\(\)])+?\s+as\s+%s\s*\.\n)",
)

ALL_ENDINGS = r"(?:Qed|Defined|Save|Admitted|Abort)\s*\."

FOUND_BUT_UNCHANGED = object()


def get_indent(term):
    return re.findall("^\s*", term)[0]


COMMENT = "comment"
STRING = "string"


def get_end_of_first_line_location(term, **env):
    stack = []
    i = 0
    while i < len(term):
        env["log"]("DEBUG: stack: %s, pre: %s" % (str(stack), repr(term[:i])), level=3)
        if len(stack) == 0:
            if term[i] == "." and (len(term) == i + 1 or (term[i + 1] in " \t\r\n")):
                return i + 1
            if term[i] == ".":
                while i < len(term) and term[i] == ".":
                    i += 1
            else:
                i += 1
        elif stack[-1] == STRING:
            if term[i] == '"':
                stack.pop()
            i += 1
        elif stack[-1] == COMMENT:
            if term[i : i + 2] == "(*":
                stack.extend(COMMENT)
                i += 2
            elif term[i : i + 2] == "*)":
                stack.pop()
                i += 2
            elif term[i] == '"':
                stack.extend(STRING)
                i += 1
            else:
                i += 1
        else:  # len(stack) == 0
            assert False
    return len(term) - 1


def update_proof(name, before_match, match, after_match, filename, rest_id, suggestion, **env):
    ending = re.search(ALL_ENDINGS, after_match, re.MULTILINE)
    if ending:
        proof_part = after_match[: ending.start()]
        env["log"]("Inspecting proof: %s" % proof_part, level=2)
        if proof_part.count("Proof") == 1:
            proof_match = re.search("Proof(?: using[^\.]*)?\.", proof_part)
            if proof_match:
                if proof_match.group() == suggestion:
                    return FOUND_BUT_UNCHANGED  # already correct
                elif proof_match.group() == "Proof.":
                    return (
                        before_match
                        + match.group()
                        + after_match[: proof_match.start()]
                        + suggestion
                        + after_match[proof_match.end() :]
                    )
                else:
                    env["log"]("Warning: Mismatch between existing Proof using and suggested Proof using:", level=0)
                    env["log"](
                        "In %s, id %s, found %s, expected %s" % (filename, rest_id, proof_match.group(), suggestion),
                        level=0,
                    )
                    return FOUND_BUT_UNCHANGED
            else:
                env["log"]("Warning: Mismatched Proofs found in %s for %s" % (filename, rest_id), level=0)
                return FOUND_BUT_UNCHANGED
        elif proof_part.count("Proof") == 0:
            loc = get_end_of_first_line_location(proof_part, **env)
            indent = get_indent(match.group())
            env["log"]("Before proof: %s\nAfter proof: %s" % (proof_part[:loc], proof_part[loc:]), level=3)
            return "%s%s%s\n%s%s\n%s%s" % (
                before_match,
                match.group(),
                proof_part[:loc],
                indent,
                suggestion,
                proof_part[loc:],
                after_match[ending.start() :],
            )
        else:
            env["log"]("Warning: Too many Proofs found in %s for %s" % (filename, rest_id), level=0)
    else:
        env["log"]("Warning: No %s found in %s for %s" % (ALL_ENDINGS, filename, rest_id), level=0)
    return None


def unsafe_update_definitions(name, contents, filename, rest_id, suggestion, **env):
    match = re.search(ALL_DEFINITIONS_STR % name, contents, re.MULTILINE)
    if match:
        return update_proof(
            name, contents[: match.start()], match, contents[match.end() :], filename, rest_id, suggestion, **env
        )
    elif name[-len("_Proper") :] == "_Proper":
        for match in re.finditer(ALL_DEFINITIONS_LESS_PROPER_STR, contents, re.MULTILINE | re.DOTALL):
            if match.group().strip("\n\t .").split(" ")[-1] + "_Proper" == name:
                return update_proof(
                    name,
                    contents[: match.start()],
                    match,
                    contents[match.end() :],
                    filename,
                    rest_id,
                    suggestion,
                    **env,
                )
    env["log"](
        "Warning: No %s found in %s" % (rest_id, filename),
        level=(2 if re.search("|".join(env["hide_reg"]), rest_id) else 0),
    )
    return None


def update_definitions(contents, filename, rest_id, suggestion, **env):
    name = rest_id.split("#")[-1]
    if len(re.findall(ALL_DEFINITIONS_STR % name, contents, re.MULTILINE)) <= 1:
        ret = unsafe_update_definitions(name, contents, filename, rest_id, suggestion, **env)
        if ret is None:
            return None
        elif ret is FOUND_BUT_UNCHANGED:
            return contents
        else:
            return ret
    else:
        modules = rest_id.split("#")[0].split(".")
        pre, mod_body, post = "", contents, ""
        while len(modules) > 0:
            mod_name = modules.pop(0)
            cur_mod = "Module " + mod_name
            cur_end = "End " + mod_name + "."
            if mod_body.count(cur_mod) == 1:
                pre += mod_body[: mod_body.index(cur_mod) + len(cur_mod)]
                mod_body = mod_body[mod_body.index(cur_mod) + len(cur_mod) :]
                if mod_body.count(cur_end) == 1:
                    post = mod_body[mod_body.index(cur_end) :] + post
                    mod_body = mod_body[: mod_body.index(cur_end)]
                    if len(re.findall(ALL_DEFINITIONS_STR % name, mod_body, re.MULTILINE)) <= 1:
                        ret = unsafe_update_definitions(name, mod_body, filename, rest_id, suggestion, **env)
                        if ret is None:
                            return None
                        elif ret is FOUND_BUT_UNCHANGED:
                            return contents
                        else:
                            return pre + ret + post
                else:
                    env["log"]("Warning: Too many %s found for %s in %s" % (cur_end, rest_id, filename), level=0)
                    break
            else:
                env["log"]("Warning: Too many %s found for %s in %s" % (cur_mod, rest_id, filename), level=0)
                break
        env["log"](
            "Warning: Module disambiguation was insufficient to uniqueize %s in %s" % (rest_id, filename), level=0
        )
        env["log"]("Found: %s" % repr(re.findall(ALL_DEFINITIONS_STR % name, contents, re.MULTILINE)), level=2)
    return contents


def main():
    args = process_logging_arguments(parser.parse_args())
    source = args.source
    env = {
        "lib_to_dir": lib_to_dir_map(args.libnames + args.non_recursive_libnames),
        "log": args.log,
        "hide_reg": args.hide_reg,
        "cli_mapping": get_parser_name_mapping(parser),
    }
    update_env_with_libnames(env, args)
    for theorem_id, suggestions in REG_PROOF_USING.findall("\n".join(source)):
        all_suggestions = REG_SUB_PROOF_USING.findall(suggestions)
        suggestion = pick_suggestion(all_suggestions)
        filenames = list(reversed(split_to_file_and_rest(theorem_id, **env)))
        if filenames:
            is_first = True
            for filename, rest_id in filenames:
                orig = read_from_file(filename)
                updated = update_definitions(orig, filename, rest_id, suggestion, **env)
                if updated is not None:
                    if updated != orig:
                        env["log"]("Updating %s in %s" % (rest_id, filename), level=1)
                        mwrite_to_file(filename, updated, do_backup=True)
                    elif len(filenames) > 1 and not is_first:
                        env["log"]("Found %s in %s" % (rest_id, filename), level=1)
                    break
                is_first = False
        else:
            env["log"]("Warning: Could not find theorem %s" % theorem_id, level=LOG_ALWAYS)


if __name__ == "__main__":
    main()
