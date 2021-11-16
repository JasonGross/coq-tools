from __future__ import with_statement
from diagnose_error import get_coq_output
from coq_version import get_coq_native_compiler_ondemand_fragment

# Like coq_version.py, except for things that use get_coq_output (or
# perhaps a bit more generally for things that need to run coqc on a
# file)

__all__ = ["get_proof_term_works_with_time", "get_ltac_support_snippet"]

def get_proof_term_works_with_time(coqc_prog, **kwargs):
    contents = r"""Lemma foo : forall _ : Type, Type.
Proof (fun x => x)."""
    output, cmds, retcode, runtime = get_coq_output(coqc_prog, ('-time', '-q'), contents, 1, verbose_base=3, **kwargs)
    return 'Error: Attempt to save an incomplete proof' not in output

LTAC_SUPPORT_SNIPPET = {}
def get_ltac_support_snippet(coqc, **kwargs):
    if coqc in LTAC_SUPPORT_SNIPPET.keys():
        return LTAC_SUPPORT_SNIPPET[coqc]
    test = r'''Inductive False : Prop := .
Axiom proof_admitted : False.
Tactic Notation "admit" := abstract case proof_admitted.
Goal False. admit. Qed.'''
    errinfo = {}
    native_ondemand_args = list(get_coq_native_compiler_ondemand_fragment(coqc, **kwargs))
    for before, after in (('Declare ML Module "ltac_plugin".\n', ''),
                          ('Declare ML Module "ltac_plugin".\n', 'Global Set Default Proof Mode "Classic".\n'),
                          ('Require Coq.Init.Ltac.\n', 'Import Coq.Init.Ltac.\n'),
                          ('Require Coq.Init.Notations.\n', 'Import Coq.Init.Notations.\n')):
        contents = '%s\n%s\n%s' % (before, after, test)
        output, cmds, retcode, runtime = get_coq_output(coqc, tuple(['-q', '-nois'] + native_ondemand_args), contents, timeout_val=None, verbose_base=3, is_coqtop=kwargs['coqc_is_coqtop'], **kwargs)
        if retcode == 0:
            LTAC_SUPPORT_SNIPPET[coqc] = (before, after)
            return (before, after)
        else:
            errinfo[contents] = {'output': output, 'cmds': cmds, 'retcode': retcode, 'runtime': runtime}
    raise Exception('No valid ltac support snipped found.  Debugging info: %s' % repr(errinfo))
