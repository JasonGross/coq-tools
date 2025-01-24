from __future__ import with_statement
import re
from .diagnose_error import get_coq_output
from .coq_version import get_coq_native_compiler_ondemand_fragment, get_boot_noinputstate_args, coqlib_args_of_coq_args
from .coq_full_grammar import COQ_GRAMMAR_TOKENS

# Like coq_version.py, except for things that use get_coq_output (or
# perhaps a bit more generally for things that need to run coqc on a
# file)

__all__ = ["get_proof_term_works_with_time", "get_ltac_support_snippet", "get_reserved_modnames"]


def get_proof_term_works_with_time(coqc_prog, **kwargs):
    contents = r"""Lemma foo : forall _ : Type, Type.
Proof (fun x => x)."""
    output, cmds, retcode, runtime = get_coq_output(
        coqc_prog,
        ("-time", "-q", *get_boot_noinputstate_args(coqc_prog, **kwargs)),
        contents,
        timeout_val=1,
        verbose_base=3,
        **kwargs,
    )
    return "Error: Attempt to save an incomplete proof" not in output


LTAC_SUPPORT_SNIPPET = {}


def get_ltac_support_snippet(coqc, coqc_args=(), **kwargs):
    if coqc in LTAC_SUPPORT_SNIPPET.keys():
        return LTAC_SUPPORT_SNIPPET[coqc]
    test = r"""Inductive False : Prop := .
Axiom proof_admitted : False.
Tactic Notation "admit" := abstract case proof_admitted.
Goal False. admit. Qed."""
    errinfo = {}
    native_ondemand_args = list(get_coq_native_compiler_ondemand_fragment(coqc, coq_args=coqc_args, **kwargs))
    for before, after in (
        ("Require Coq.Init.Ltac.\n", "Import Coq.Init.Ltac.\n"),
        ("Require Coq.Init.Notations.\n", "Import Coq.Init.Notations.\n"),
        ("Require Stdlib.Init.Ltac.\n", "Import Stdlib.Init.Ltac.\n"),
        ("Require Stdlib.Init.Notations.\n", "Import Stdlib.Init.Notations.\n"),
        ('Declare ML Module "coq-core.plugins.ltac".\n', ""),
        ('Declare ML Module "coq-core.plugins.ltac".\n', 'Global Set Default Proof Mode "Classic".\n'),
        ('Declare ML Module "ltac_plugin".\n', ""),
        ('Declare ML Module "ltac_plugin".\n', 'Global Set Default Proof Mode "Classic".\n'),
    ):
        contents = "%s\n%s\n%s" % (before, after, test)
        output, cmds, retcode, runtime = get_coq_output(
            coqc,
            tuple(["-q", "-nois", *coqlib_args_of_coq_args(coqc, coqc_args, **kwargs)] + native_ondemand_args),
            contents,
            timeout_val=None,
            verbose_base=3,
            is_coqtop=kwargs["coqc_is_coqtop"],
            **kwargs,
        )
        if retcode == 0:
            LTAC_SUPPORT_SNIPPET[coqc] = (before, after)
            return (before, after)
        else:
            errinfo[contents] = {"output": output, "cmds": cmds, "retcode": retcode, "runtime": runtime}
    raise Exception("No valid ltac support snipped found.  Debugging info: %s" % repr(errinfo))


def get_is_modname_valid(coqc_prog, modname, **kwargs):
    contents = "Module %s. End %s." % (modname, modname)
    if " " in modname:
        return False
    output, cmds, retcode, runtime = get_coq_output(
        coqc_prog,
        ("-q", *get_boot_noinputstate_args(coqc_prog, **kwargs)),
        contents,
        timeout_val=1,
        verbose_base=3,
        **kwargs,
    )
    return "Syntax error:" not in output


def get_reserved_modnames(coqtop_prog, **kwargs):
    grammars_contents = "Print Grammar tactic. Print Grammar constr. Print Grammar vernac."
    grammars_output, cmds, retcode, runtime = get_coq_output(
        coqtop_prog,
        ("-q", *get_boot_noinputstate_args(coqtop_prog, **kwargs)),
        grammars_contents,
        is_coqtop=True,
        pass_on_stdin=True,
        timeout_val=1,
        verbose_base=3,
        **kwargs,
    )
    tokens = sorted(set([i.strip('"') for i in re.findall(r'"[a-zA-Z_][^"]*"', grammars_output)] + COQ_GRAMMAR_TOKENS))
    contents = "\n".join("Module %s. End %s." % (modname, modname) for modname in tokens)
    output, cmds, retcode, runtime = get_coq_output(
        coqtop_prog,
        ("-q", *get_boot_noinputstate_args(coqtop_prog, **kwargs)),
        contents,
        is_coqtop=True,
        pass_on_stdin=True,
        timeout_val=10,
        verbose_base=3,
        **kwargs,
    )
    success = re.findall(r"Module ([^ ]+) is defined", output)
    return tuple(modname for modname in tokens if modname not in success)
