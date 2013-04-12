Require Import Eqdep Eqdep_dec FunctionalExtensionality JMeq ProofIrrelevance Setoid.

Set Implicit Arguments.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Local Infix "==" := JMeq (at level 70).

 
Section sig.
  Definition sigT_of_sigT2 A P Q (x : @sigT2 A P Q) := let (a, h, _) := x in existT _ a h.
  Global Coercion sigT_of_sigT2 : sigT2 >-> sigT.
  Definition projT3 A P Q (x : @sigT2 A P Q) :=
    let (x0, _, h) as x0 return (Q (projT1 x0)) := x in h.

  Definition sig_of_sig2 A P Q (x : @sig2 A P Q) := let (a, h, _) := x in exist _ a h.
  Global Coercion sig_of_sig2 : sig2 >-> sig.
  Definition proj3_sig A P Q (x : @sig2 A P Q) :=
    let (x0, _, h) as x0 return (Q (proj1_sig x0)) := x in h.
End sig.

 
Tactic Notation "not_tac" tactic(tac) := (tac; fail 1) || idtac.

 
Tactic Notation "test_tac" tactic(tac) := not_tac (not_tac tac).

 
Ltac unique_pose defn :=
  let T := type of defn in
    match goal with
      | [ H : T |- _ ] => fail 1
      | _ => pose proof defn
    end.

 
Tactic Notation "has_no_body" hyp(H) :=
  not_tac (let H' := fresh in pose H as H'; unfold H in H').

Tactic Notation "has_body" hyp(H) :=
  not_tac (has_no_body H).

 
Ltac head expr :=
  match expr with
    | ?f _ => head f
    | _ => expr
  end.

Ltac head_hnf expr := let expr' := eval hnf in expr in head expr'.

Ltac do_with_hyp tac :=
  match goal with
    | [ H : _ |- _ ] => tac H
  end.

Ltac rewrite_hyp' := do_with_hyp ltac:(fun H => rewrite H).
Ltac rewrite_hyp := repeat rewrite_hyp'.

 
Ltac t' := repeat progress (simpl in *; intros; try split; trivial).
Ltac t'_long := repeat progress (simpl in *; intuition).

Ltac t_con_with con tac := tac;
  repeat (match goal with
            | [ H : context[con] |- _ ] => rewrite H
            | _ => progress autorewrite with core in *
          end; tac).

Ltac t_con_rev_with con tac := tac;
  repeat (match goal with
            | [ H : context[con] |- _ ] => rewrite <- H
            | _ => progress autorewrite with core in *
          end; tac).

Ltac t_with tac := t_con_with @eq tac.

Ltac t_rev_with tac := t_con_rev_with @eq tac.

Ltac t := t_with t'; t_with t'_long.

 
Ltac simpl_transitivity :=
  try solve [ match goal with
                | [ _ : ?Rel ?a ?b, _ : ?Rel ?b ?c |- ?Rel ?a ?c ] => transitivity b; assumption
              end ].

 
Ltac destruct_all_matches_then matcher tac :=
  repeat match goal with
           | [ H : ?T |- _ ] => matcher T; destruct H; tac
         end.

Ltac destruct_all_matches matcher := destruct_all_matches_then matcher ltac:(simpl in    *)   .
Ltac destruct_all_matches' matcher := destruct_all_matches_then matcher idtac.

 
Ltac destruct_type_matcher T HT :=
  match HT with
    | context[T] => idtac
  end.
Ltac destruct_type T := destruct_all_matches ltac:(destruct_type_matcher T).
Ltac destruct_type' T := destruct_all_matches' ltac:(destruct_type_matcher T).

Ltac destruct_head_matcher T HT :=
  match head HT with
    | T => idtac
  end.
Ltac destruct_head T := destruct_all_matches ltac:(destruct_head_matcher T).

Ltac destruct_head_hnf_matcher T HT :=
  match head_hnf HT with
    | T => idtac
  end.
Ltac destruct_head_hnf T := destruct_all_matches ltac:(destruct_head_hnf_matcher T).

Ltac destruct_hypotheses_matcher HT :=
  let HT' := eval hnf in HT in
    match HT' with
      | ex _ => idtac
      | and _ _ => idtac
      | prod _ _ => idtac
    end.
Ltac destruct_hypotheses := destruct_all_matches destruct_hypotheses_matcher.

Ltac destruct_sig_matcher HT :=
  let HT' := eval hnf in HT in
    match HT' with
      | @sig _ _ => idtac
      | @sigT _ _ => idtac
      | @sig2 _ _ _ => idtac
      | @sigT2 _ _ _ => idtac
    end.
Ltac destruct_sig := destruct_all_matches destruct_sig_matcher.

Ltac destruct_all_hypotheses := destruct_all_matches ltac:(fun HT =>
  destruct_hypotheses_matcher HT || destruct_sig_matcher HT
).

 
Ltac destruct_exists' T := cut T; try (let H := fresh in intro H; exists H).
Ltac destruct_exists := destruct_head_hnf @ex;
  match goal with
    | [ |- @ex ?T _ ] => destruct_exists' T
    | [ |- @sig ?T _ ] => destruct_exists' T
    | [ |- @sigT ?T _ ] => destruct_exists' T
    | [ |- @sig2 ?T _ _ ] => destruct_exists' T
    | [ |- @sigT2 ?T _ _ ] => destruct_exists' T
  end.

 
Ltac specialize_all_ways :=
  repeat match goal with
           | [ x : ?T, H : _ |- _ ] => unique_pose (H x)
         end.

Ltac try_rewrite_by rew_H by_tac tac :=
  (repeat rewrite rew_H by by_tac; tac) ||
    (repeat rewrite <- rew_H by by_tac; tac).

Lemma sig_eq A P (s s' : @sig A P) : proj1_sig s = proj1_sig s' -> s = s'.
  destruct s, s'; simpl; intro; subst; f_equal; apply proof_irrelevance.
Qed.

Lemma sig2_eq A P Q (s s' : @sig2 A P Q) : proj1_sig s = proj1_sig s' -> s = s'.
  destruct s, s'; simpl; intro; subst; f_equal; apply proof_irrelevance.
Qed.

Lemma sigT_eq A P (s s' : @sigT A P) : projT1 s = projT1 s' -> projT2 s == projT2 s' -> s = s'.
  destruct s, s'; simpl; intros; firstorder; repeat subst; reflexivity.
Qed.

Lemma sigT2_eq A P Q (s s' : @sigT2 A P Q) :
  projT1 s = projT1 s'
  -> projT2 s == projT2 s'
  -> projT3 s == projT3 s'
  -> s = s'.
  destruct s, s'; simpl; intros; firstorder; repeat subst; reflexivity.
Qed.

Lemma injective_projections_JMeq (A B A' B' : Type) (p1 : A * B) (p2 : A' * B') :
  fst p1 == fst p2 -> snd p1 == snd p2 -> p1 == p2.
Proof.
  destruct p1, p2; simpl; intros H0 H1; subst;
    rewrite H0; rewrite H1; reflexivity.
Qed.

Ltac clear_refl_eq :=
  repeat match goal with
           | [ H : ?x = ?x |- _ ] => clear H
         end.

 
Ltac simpl_eq' :=
  apply sig_eq
        || apply sig2_eq
        || ((apply sigT_eq || apply sigT2_eq); intros; clear_refl_eq)
        || apply injective_projections
        || apply injective_projections_JMeq.

Ltac simpl_eq := intros; repeat (
  simpl_eq'; simpl in *
).

Ltac subst_body :=
  repeat match goal with
           | [ H := _ |- _ ] => subst H
         end.

 
Inductive Common_sigT (A : Type) (P : A -> Type) : Type :=
    Common_existT : forall x : A, P x -> Common_sigT P.
Definition Common_projT1 (A : Type) (P : A -> Type) (x : @Common_sigT A P) := let (a, _) := x in a.
Definition Common_projT2 (A : Type) (P : A -> Type) (x : @Common_sigT A P) := let (x0, h) as x0 return (P (Common_projT1 x0)) := x in h.

Lemma fg_equal A B (f g : A -> B) : f = g -> forall x, f x = g x.
  intros; repeat subst; reflexivity.
Qed.

Section telescope.
  Inductive telescope :=
  | Base : forall (A : Type) (B : A -> Type), (forall a, B a) -> (forall a, B a) -> telescope
  | Quant : forall A : Type, (A -> telescope) -> telescope.

  Fixpoint telescopeOut (t : telescope) :=
    match t with
      | Base _ _ x y => x = y
      | Quant _ f => forall x, telescopeOut (f x)
    end.

  Fixpoint telescopeOut' (t : telescope) :=
    match t with
      | Base _ _ f g => forall x, f x = g x
      | Quant _ f => forall x, telescopeOut' (f x)
    end.

  Theorem generalized_fg_equal : forall (t : telescope),
    telescopeOut t
    -> telescopeOut' t.
    induction t; simpl; intuition; subst; auto.
  Qed.
End telescope.

Lemma f_equal_helper A0 (A B : A0 -> Type) (f : forall a0, A a0 -> B a0) (x y : forall a0, A a0) :
  (forall a0, x a0 = y a0) -> (forall a0, f a0 (x a0) = f a0 (y a0)).
  intros H a0; specialize (H a0); rewrite H; reflexivity.
Qed.

Ltac eta_red :=
  repeat match goal with
           | [ H : appcontext[fun x => ?f x] |- _ ] => change (fun x => f x) with f in H
           | [ |- appcontext[fun x => ?f x] ] => change (fun x => f x) with f
         end.

Lemma sigT_eta : forall A (P : A -> Type) (x : sigT P),
  x = existT _ (projT1 x) (projT2 x).
  destruct x; reflexivity.
Qed.

Lemma sigT2_eta : forall A (P Q : A -> Type) (x : sigT2 P Q),
  x = existT2 _ _ (projT1 x) (projT2 x) (projT3 x).
  destruct x; reflexivity.
Qed.

Lemma sig_eta : forall A (P : A -> Prop) (x : sig P),
  x = exist _ (proj1_sig x) (proj2_sig x).
  destruct x; reflexivity.
Qed.

Lemma sig2_eta : forall A (P Q : A -> Prop) (x : sig2 P Q),
  x = exist2 _ _ (proj1_sig x) (proj2_sig x) (proj3_sig x).
  destruct x; reflexivity.
Qed.

Lemma prod_eta : forall (A B : Type) (x : A * B),
  x = pair (fst x) (snd x).
  destruct x; reflexivity.
Qed.

Ltac rewrite_eta_in Hf :=
  repeat match type of Hf with
           | context[match ?E with existT2 _ _ _ => _ end] => rewrite (sigT2_eta E) in Hf; simpl in Hf
           | context[match ?E with exist2 _ _ _ => _ end] => rewrite (sig2_eta E) in Hf; simpl in Hf
           | context[match ?E with existT _ _ => _ end] => rewrite (sigT_eta E) in Hf; simpl in Hf
           | context[match ?E with exist _ _ => _ end] => rewrite (sig_eta E) in Hf; simpl in Hf
           | context[match ?E with pair _ _ => _ end] => rewrite (prod_eta E) in Hf; simpl in Hf
         end.

Definition is_unique (A : Type) (x : A) := forall x' : A, x' = x.
Implicit Arguments is_unique [A].

 
Ltac existential_to_evar x :=
  is_evar x;
  let x' := fresh in
  set (x' := x) in *.

 
Ltac existentials_to_evars_in_goal :=
  repeat match goal with
           | [ |- context[?x] ] => existential_to_evar x
         end.

 
Ltac existentials_to_evars_in_hyps :=
  repeat match goal with
           | [ H : context[?x] |- _ ] => existential_to_evar x
         end.

 
Ltac existentials_to_evars_in H :=
  repeat match type of H with
           | context[?x] => existential_to_evar x
         end.

Tactic Notation "existentials_to_evars" := existentials_to_evars_in_goal.
Tactic Notation "existentials_to_evars" "in" "|-" "*" := existentials_to_evars_in_goal.
Tactic Notation "existentials_to_evars" "in" "*" := existentials_to_evars_in_goal; existentials_to_evars_in_hyps.
Tactic Notation "existentials_to_evars" "in" "*" "|-" := existentials_to_evars_in_hyps.
Tactic Notation "existentials_to_evars" "in" hyp(H) "|-" "*" := existentials_to_evars_in H; existentials_to_evars_in_goal.
Tactic Notation "existentials_to_evars" "in" hyp(H) := existentials_to_evars_in H.
Tactic Notation "existentials_to_evars" "in" hyp(H) "|-" := existentials_to_evars_in H.

Ltac do_for_each_hyp' tac fail_if_seen :=
  match goal with
    | [ H : _ |- _ ] => fail_if_seen H; tac H; try do_for_each_hyp' tac ltac:(fun H' => fail_if_seen H'; match H' with | H => fail 1 | _ => idtac end)
  end.
Ltac do_for_each_hyp tac := do_for_each_hyp' tac ltac:(fun H => idtac).

 
Tactic Notation "change_in_all" constr(from) "with" constr(to) :=
  change from with to; do_for_each_hyp ltac:(fun H => change from with to in H).

 
Ltac expand :=
  match goal with
    | [ |- ?X = ?Y ] =>
      let X' := eval hnf in X in let Y' := eval hnf in Y in change (X' = Y')
    | [ |- ?X == ?Y ] =>
      let X' := eval hnf in X in let Y' := eval hnf in Y in change (X' == Y')
  end; simpl.

 
Ltac hideProof' pf :=
  match goal with
    | [ x : _ |- _ ] => match x with
                          | pf => fail 2
                        end
    | _ => generalize pf; intro
  end.

 
Tactic Notation "hideProofs" constr(pf)
  := hideProof' pf.
Tactic Notation "hideProofs" constr(pf0) constr(pf1)
  := progress (try hideProof' pf0; try hideProof' pf1).
Tactic Notation "hideProofs" constr(pf0) constr(pf1) constr(pf2)
  := progress (try hideProof' pf0; try hideProof' pf1; try hideProof' pf2).
Tactic Notation "hideProofs" constr(pf0) constr(pf1) constr(pf2) constr(pf3)
  := progress (try hideProof' pf0; try hideProof' pf1; try hideProof' pf2; try hideProof' pf3).
Tactic Notation "hideProofs" constr(pf0) constr(pf1) constr(pf2) constr(pf3) constr(pf4)
  := progress (try hideProof' pf0; try hideProof' pf1; try hideProof' pf2; try hideProof' pf3; try hideProof' pf4).
Tactic Notation "hideProofs" constr(pf0) constr(pf1) constr(pf2) constr(pf3) constr(pf4) constr(pf5)
  := progress (try hideProof' pf0; try hideProof' pf1; try hideProof' pf2; try hideProof' pf3; try hideProof' pf4; try hideProof' pf5).

Section unique.
  Definition uniqueT (A : Type) (P : A -> Type) (x : A)
    := P x + {forall x' : A, P x' -> x = x'}.
End unique.

Ltac destruct_to_empty_set :=
  match goal with
    | [ H : Empty_set |- _ ] => destruct H
    | [ H : ?T -> Empty_set, a : ?T |- _ ] => destruct (H a)
    | [ H : context[Empty_set] |- _ ] => solve [ destruct H; trivial; assumption ]
  end.

Section True.
  Lemma True_singleton (u : True) : u = I.
    case u; reflexivity.
  Qed.

  Lemma True_eq (u u' : True) : u = u'.
    case u; case u'; reflexivity.
  Defined.

  Lemma True_eq_singleton (u u' : True) (H : u = u') : H = True_eq _ _.
    destruct u; destruct H; reflexivity.
  Defined.

  Lemma True_eq_eq (u u' : True) (H H' : u = u') : H = H'.
    transitivity (@True_eq u u');
    destruct_head @eq; subst_body; destruct_head True; reflexivity.
  Defined.

  Lemma True_JMeq (u u' : True) : u == u'.
    case u; case u'; reflexivity.
  Defined.

  Lemma True_eqT_eq (u u' v v' : True) : @eq Type (u = u') (v = v').
    destruct_head True; reflexivity.
  Qed.

  Lemma True_eqS_eq (u u' v v' : True) : @eq Set (u = u') (v = v').
    destruct_head True; reflexivity.
  Qed.

  Lemma True_eqP_eq (u u' v v' : True) : @eq Prop (u = u') (v = v').
    destruct_head True; reflexivity.
  Qed.

  Lemma True_eq_JMeq (u u' v v' : True) (H : u = u') (H' : v = v') : H == H'.
    subst; destruct_head True; reflexivity.
  Qed.

  Lemma False_eq (a b : False) : a = b.
    destruct a.
  Defined.

  Lemma False_JMeql (a : False) T (b : T) : a == b.
    destruct a.
  Defined.

  Lemma False_JMeqr T (a : T) (b : False) : a == b.
    destruct b.
  Defined.
End True.

Section unit.
  Lemma unit_singleton (u : unit) : u = tt.
    case u; reflexivity.
  Qed.

  Lemma unit_eq (u u' : unit) : u = u'.
    case u; case u'; reflexivity.
  Defined.

  Lemma unit_eq_singleton (u u' : unit) (H : u = u') : H = unit_eq _ _.
    destruct u; destruct H; reflexivity.
  Defined.

  Lemma unit_eq_eq (u u' : unit) (H H' : u = u') : H = H'.
    transitivity (@unit_eq u u');
    destruct_head @eq; subst_body; destruct_head unit; reflexivity.
  Defined.

  Lemma unit_JMeq (u u' : unit) : u == u'.
    case u; case u'; reflexivity.
  Defined.

  Lemma unit_eqT_eq (u u' v v' : unit) : @eq Type (u = u') (v = v').
    destruct_head unit; reflexivity.
  Qed.

  Lemma unit_eqS_eq (u u' v v' : unit) : @eq Set (u = u') (v = v').
    destruct_head unit; reflexivity.
  Qed.

  Lemma unit_eqP_eq (u u' v v' : unit) : @eq Prop (u = u') (v = v').
    destruct_head unit; reflexivity.
  Qed.

  Lemma unit_eq_JMeq (u u' v v' : unit) (H : u = u') (H' : v = v') : H == H'.
    subst; destruct_head unit; reflexivity.
  Qed.

  Lemma Empty_set_eq (a b : Empty_set) : a = b.
    destruct a.
  Defined.

  Lemma Empty_set_JMeql (a : Empty_set) T (b : T) : a == b.
    destruct a.
  Defined.

  Lemma Empty_set_JMeqr T (a : T) (b : Empty_set) : a == b.
    destruct b.
  Defined.
End unit.

Hint Rewrite True_singleton.
Hint Extern 0 (@eq True _ _) => apply True_eq.
Hint Extern 0 (@eq (@eq True _ _) _ _) => apply True_eq_eq.
Hint Extern 0 (@JMeq True _ True _) => apply True_JMeq.
Hint Extern 0 (@JMeq (@eq True _ _) _ (@eq True _ _) _) => apply True_eq_JMeq.
Hint Extern 0 (@eq Set (@eq True _ _) (@eq True _ _)) => apply True_eqS_eq.
Hint Extern 0 (@eq Prop (@eq True _ _) (@eq True _ _)) => apply True_eqP_eq.
Hint Extern 0 (@eq Type (@eq True _ _) (@eq True _ _)) => apply True_eqT_eq.
Hint Extern 0 True => constructor.
Hint Extern 0 (@eq False _ _) => apply False_eq.
Hint Extern 0 (@JMeq False _ _ _) => apply False_JMeql.
Hint Extern 0 (@JMeq _ _ False _) => apply False_JMeqr.

Hint Rewrite unit_singleton.
Hint Extern 0 (@eq unit _ _) => apply unit_eq.
Hint Extern 0 (@eq (@eq unit _ _) _ _) => apply unit_eq_eq.
Hint Extern 0 (@JMeq unit _ unit _) => apply unit_JMeq.
Hint Extern 0 (@JMeq (@eq unit _ _) _ (@eq unit _ _) _) => apply unit_eq_JMeq.
Hint Extern 0 (@eq Set (@eq unit _ _) (@eq unit _ _)) => apply unit_eqS_eq.
Hint Extern 0 (@eq Prop (@eq unit _ _) (@eq unit _ _)) => apply unit_eqP_eq.
Hint Extern 0 (@eq Type (@eq unit _ _) (@eq unit _ _)) => apply unit_eqT_eq.
Hint Extern 0 unit => constructor.
Hint Extern 0 (@eq Empty_set _ _) => apply Empty_set_eq.
Hint Extern 0 (@JMeq Empty_set _ _ _) => apply Empty_set_JMeql.
Hint Extern 0 (@JMeq _ _ Empty_set _) => apply Empty_set_JMeqr.


Set Implicit Arguments.

Set Universe Polymorphism.

 
Definition focus A (_ : A) := True.

 
Ltac simpl_definition_by_tac_and_exact defn tac :=
  assert (Hf : focus defn) by constructor;
    let defnH := head defn in try unfold defnH in Hf; try tac; simpl in Hf;
      rewrite_eta_in Hf;
      match type of Hf with
        | focus ?V => exact V
      end.

 

Reserved Notation "x == y" (at level 70, no associativity).
Reserved Notation "x == y == z" (at level 70, no associativity, y at next level).

Reserved Notation "x ~= y" (at level 70, no associativity).
Reserved Notation "x ~= y ~= z" (at level 70, no associativity, y at next level).

Reserved Notation "i ⁻¹" (at level 10).
Reserved Notation "C ᵒᵖ" (at level 10).

Reserved Notation "C ★^ M D" (at level 70, no associativity).
Reserved Notation "C ★^{ M } D" (at level 70, no associativity).

Reserved Notation "S ↓ T" (at level 70, no associativity).

Reserved Notation "S ⇑ T" (at level 70, no associativity).
Reserved Notation "S ⇓ T" (at level 70, no associativity).
Reserved Notation "'CAT' ⇑ D" (at level 70, no associativity).
Reserved Notation "'CAT' ⇓ D" (at level 70, no associativity).

Reserved Notation "x ⊗ y" (at level 40, left associativity).
Reserved Notation "x ⊗m y" (at level 40, left associativity).

Reserved Notation "f ○ g" (at level 70, right associativity).

Reserved Notation "x ~> y" (at level 99, right associativity, y at level 200).

Reserved Notation "x ∏ y" (at level 40, left associativity).
Reserved Notation "x ∐ y" (at level 50, left associativity).

Reserved Notation "∏_{ x } f" (at level 0, x at level 99).
Reserved Notation "∏_{ x : A } f" (at level 0, x at level 99).
Reserved Notation "∐_{ x } f" (at level 0, x at level 99).
Reserved Notation "∐_{ x : A } f" (at level 0, x at level 99).

 
Reserved Notation "F ⟨ c , - ⟩" (at level 70, no associativity).
Reserved Notation "F ⟨ - , d ⟩" (at level 70, no associativity).

 
Reserved Notation "[ x ]" (at level 0, x at level 200).

Reserved Notation "∫ F" (at level 0).

Delimit Scope object_scope with object.
Delimit Scope morphism_scope with morphism.
Delimit Scope category_scope with category.
Delimit Scope functor_scope with functor.
Delimit Scope natural_transformation_scope with natural_transformation.

Delimit Scope graph_scope with graph.
Delimit Scope group_elements_scope with group.
Delimit Scope groups_scope with groups.
Delimit Scope vertex_scope with vertex.
Delimit Scope edge_scope with edge.


Set Implicit Arguments.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Local Infix "==" := JMeq.

Section f_equal_dep.
  Theorem f_type_equal {A B A' B'} : A = A' -> B = B' -> (A -> B) = (A' -> B').
    intros; repeat subst; reflexivity.
  Qed.

  Theorem forall_extensionality_dep : forall {A}
    (f g : A -> Type),
    (forall x, f x = g x) -> (forall x, f x) = (forall x, g x).
    intros.
    replace f with g; auto.
    apply functional_extensionality_dep; auto.
  Qed.

  Theorem forall_extensionality_dep_JMeq : forall {A B}
    (f : A -> Type) (g : B -> Type),
    A = B -> (A = B -> forall x y, x == y -> f x == g y) -> (forall x, f x) = (forall x, g x).
    intros; firstorder; intuition; repeat subst.
    apply forall_extensionality_dep.
    intro.
    apply JMeq_eq.
    eauto.
  Qed.


  Lemma JMeq_eqT A B (x : A) (y : B) : x == y -> A = B.
    intro H; destruct H; reflexivity.
  Qed.

  Lemma fg_equal_JMeq A B B' (f : forall a : A, B a) (g : forall a : A, B' a) x :
    f == g -> (f == g -> B = B') -> f x == g x.
    intros.
    repeat (firstorder; repeat subst).
  Qed.

  Lemma f_equal_JMeq A A' B B' a b (f : forall a : A, A' a) (g : forall b : B, B' b) :
    f == g -> (f == g -> A' == B') -> (f == g -> a == b) -> f a == g b.
    intros.
    firstorder.
    repeat destruct_type @JMeq.
    repeat subst; reflexivity.
  Qed.

  Lemma f_equal1_JMeq A0 B a0 b0 (f : forall (a0 : A0), B a0) :
    a0 = b0
    -> f a0 == f b0.
    intros.
    repeat (firstorder; repeat subst).
  Qed.

  Lemma f_equal2_JMeq A0 A1 B a0 b0 a1 b1 (f : forall (a0 : A0) (a1 : A1 a0), B a0 a1) :
    a0 = b0
    -> (a0 = b0 -> a1 == b1)
    -> f a0 a1 == f b0 b1.
    intros.
    repeat (firstorder; repeat subst).
  Qed.

  Lemma f_equal3_JMeq A0 A1 A2 B a0 b0 a1 b1 a2 b2 (f : forall (a0 : A0) (a1 : A1 a0) (a2 : A2 a0 a1), B a0 a1 a2) :
    a0 = b0
    -> (a0 = b0 -> a1 == b1)
    -> (a0 = b0 -> a1 == b1 -> a2 == b2)
    -> f a0 a1 a2 == f b0 b1 b2.
    intros.
    repeat (firstorder; repeat subst).
  Qed.

  Lemma f_equal4_JMeq A0 A1 A2 A3 B a0 b0 a1 b1 a2 b2 a3 b3 (f : forall (a0 : A0) (a1 : A1 a0) (a2 : A2 a0 a1) (a3 : A3 a0 a1 a2), B a0 a1 a2 a3) :
    a0 = b0
    -> (a0 = b0 -> a1 == b1)
    -> (a0 = b0 -> a1 == b1 -> a2 == b2)
    -> (a0 = b0 -> a1 == b1 -> a2 == b2 -> a3 == b3)
    -> f a0 a1 a2 a3 == f b0 b1 b2 b3.
    intros.
    repeat (firstorder; repeat subst).
  Qed.

  Lemma f_equal5_JMeq A0 A1 A2 A3 A4 B a0 b0 a1 b1 a2 b2 a3 b3 a4 b4 (f : forall (a0 : A0) (a1 : A1 a0) (a2 : A2 a0 a1) (a3 : A3 a0 a1 a2) (a4 : A4 a0 a1 a2 a3), B a0 a1 a2 a3 a4) :
    a0 = b0
    -> (a0 = b0 -> a1 == b1)
    -> (a0 = b0 -> a1 == b1 -> a2 == b2)
    -> (a0 = b0 -> a1 == b1 -> a2 == b2 -> a3 == b3)
    -> (a0 = b0 -> a1 == b1 -> a2 == b2 -> a3 == b3 -> a4 == b4)
    -> f a0 a1 a2 a3 a4 == f b0 b1 b2 b3 b4.
    intros.
    repeat (firstorder; repeat subst).
  Qed.

  Lemma eq_JMeq T (A B : T) : A = B -> A == B.
    intro; subst; reflexivity.
  Qed.

  Theorem functional_extensionality_dep_JMeq : forall {A} {B1 B2 : A -> Type},
    forall (f : forall x : A, B1 x) (g : forall x : A, B2 x),
      (forall x, B1 x = B2 x)
      -> (forall x, f x == g x) -> f == g.
    intros.
    assert (B1 = B2) by (extensionality x; auto); subst.
    assert (f = g) by (extensionality x; apply JMeq_eq; auto).
    subst; reflexivity.
  Qed.

  Theorem functional_extensionality_dep_JMeq' : forall {A1 A2} {B1 : A1 -> Type} {B2 : A2 -> Type},
    forall (f : forall x : A1, B1 x) (g : forall x : A2, B2 x),
      A1 = A2
      -> (A1 = A2 -> forall x y, x == y -> B1 x = B2 y)
      -> (A1 = A2 -> forall x y, x == y -> f x == g y) -> f == g.
    intros.
    intuition; repeat subst.
    apply functional_extensionality_dep_JMeq; intros;
      intuition.
  Qed.
End f_equal_dep.

Inductive identity_dep (A : Type) (a : A) : forall B : Type, B -> Type :=
  identity_dep_refl : identity_dep a a.

Section f_identity_dep.
  Local Infix "~" := identity (at level 50).
  Local Infix "~~" := identity_dep (at level 50).
  Definition f_identity (A B : Type) (f : A -> B) (x y : A) (H : x ~ y) : f x ~ f y
    := match H in (_ ~ y0) return (f x ~ f y0) with
         | identity_refl => identity_refl (f x)
       end.

  Definition f_type_identity {A B A' B'} : A ~ A' -> B ~ B' -> (A -> B) ~ (A' -> B').
    intros; destruct_head identity; reflexivity.
  Defined.

  Axiom functional_extensionality_dep_identity : forall {A : Type} {B : A -> Type} (f g : forall x : A, B x),
                                                   (forall x : A, f x ~ g x) -> f ~ g.

  Axiom identity_dep_identity : forall A (x y : A), x ~~ y -> x ~ y.

  Definition functional_extensionality_identity {A B : Type} := fun (f g : A -> B) (H : forall x : A, f x ~ g x) => functional_extensionality_dep_identity f g H.

  Theorem forall_extensionality_dep_identity : forall {A}
                                                      (f g : A -> Type),
                                                 (forall x, f x ~ g x) -> (forall x, f x) ~ (forall x, g x).
    intros.
    cut (f ~ g); [ let H := fresh in intro H; destruct H; reflexivity | ].
    apply functional_extensionality_dep_identity; assumption.
  Qed.

  Theorem forall_extensionality_dep_identity_dep : forall {A B}
                                                          (f : A -> Type) (g : B -> Type),
                                                     A ~ B -> (A ~ B -> forall x y, x ~~ y -> f x ~~ g y) -> (forall x, f x) ~ (forall x, g x).
    intros; intuition; destruct_head identity.
    apply forall_extensionality_dep_identity.
    intro.
    apply identity_dep_identity.
    match goal with | [ H : _ |- _ ] => apply H; reflexivity end.
  Qed.

  Definition identity_dep_identityT A B (x : A) (y : B) : x ~~ y -> A ~ B
    := fun H => match H in (_ ~~ b) return _ with
                  | identity_dep_refl => identity_refl A
                end.
End f_identity_dep.

Ltac JMeq_eq :=
  repeat match goal with
           | [ |- _ == _ ] => apply eq_JMeq
           | [ H : _ == _ |- _ ] => apply JMeq_eq in H
         end.

Section misc.
  Lemma sig_JMeq A0 A1 B0 B1 (a : @sig A0 A1) (b : @sig B0 B1) : A1 == B1 -> proj1_sig a == proj1_sig b -> a == b.
    intros.
    destruct_sig.
    repeat destruct_type @JMeq.
    JMeq_eq; subst.
    JMeq_eq.
    simpl_eq.
    trivial.
  Qed.
End misc.


Set Implicit Arguments.

Set Universe Polymorphism.

Local Infix "==" := JMeq.

Ltac structures_eq_simpl_step_with tac := intros; simpl in *;
  match goal with
    | _ => reflexivity
    | [ |- (fun _ : ?A => _) = _ ] => apply functional_extensionality_dep; intro
    | [ |- (fun _ : ?A => _) == _ ] => apply (@functional_extensionality_dep_JMeq A); intro
    | [ |- (forall _ : ?A, _) = _ ] => apply (@forall_extensionality_dep A); intro
    | _ => tac
  end; simpl; JMeq_eq.

Ltac structures_eq_step_with_tac structures_equal_tac tac := intros; simpl in *;
  match goal with
    | _ => reflexivity
    | [ |- _ = _ ] => expand; structures_equal_tac
    | [ |- _ == _ ] => expand; structures_equal_tac
    | _ => structures_eq_simpl_step_with tac
  end.


Set Implicit Arguments.

Generalizable All Variables.

Set Universe Polymorphism.

Local Infix "==" := JMeq.

Record ComputationalCategory (obj : Type) :=
  Build_ComputationalCategory {
      Object :> _ := obj;
      Morphism : obj -> obj -> Type;

      Identity : forall x, Morphism x x;
      Compose : forall s d d', Morphism d d' -> Morphism s d -> Morphism s d'
    }.

Bind Scope category_scope with ComputationalCategory.
Bind Scope object_scope with Object.
Bind Scope morphism_scope with Morphism.

Arguments Object {obj%type} C%category / : rename.
Arguments Morphism {obj%type} !C%category s d : rename.
 
Arguments Identity {obj%type} [!C%category] x%object : rename.
Arguments Compose {obj%type} [!C%category s%object d%object d'%object] m1%morphism m2%morphism : rename.

Class IsSpecializedCategory (obj : Type) (C : ComputationalCategory obj) : Prop :=
  {
    Associativity : forall o1 o2 o3 o4
                           (m1 : Morphism C o1 o2)
                           (m2 : Morphism C o2 o3)
                           (m3 : Morphism C o3 o4),
                      Compose (Compose m3 m2) m1 = Compose m3 (Compose m2 m1);
     
    Associativity_sym : forall o1 o2 o3 o4
                               (m1 : Morphism C o1 o2)
                               (m2 : Morphism C o2 o3)
                               (m3 : Morphism C o3 o4),
                          Compose m3 (Compose m2 m1) = Compose (Compose m3 m2) m1;
    LeftIdentity : forall a b (f : Morphism C a b), Compose (Identity b) f = f;
    RightIdentity : forall a b (f : Morphism C a b), Compose f (Identity a) = f
  }.

Record > SpecializedCategory (obj : Type) :=
  Build_SpecializedCategory' {
      UnderlyingCCategory :> ComputationalCategory obj;
      UnderlyingCCategory_IsSpecializedCategory :> IsSpecializedCategory UnderlyingCCategory
    }.

Hint Extern 0 (IsSpecializedCategory _) => solve [ apply UnderlyingCCategory_IsSpecializedCategory ].

Existing Instance UnderlyingCCategory_IsSpecializedCategory.

Ltac specialized_category_is_specialized :=
  solve [ apply UnderlyingCCategory_IsSpecializedCategory ].

Bind Scope category_scope with SpecializedCategory.

Section SpecializedCategoryInterface.
  Definition Build_SpecializedCategory (obj : Type)
    (Morphism : obj -> obj -> Type)
    (Identity' : forall o : obj, Morphism o o)
    (Compose' : forall s d d' : obj, Morphism d d' -> Morphism s d -> Morphism s d')
    (Associativity' : forall (o1 o2 o3 o4 : obj) (m1 : Morphism o1 o2) (m2 : Morphism o2 o3) (m3 : Morphism o3 o4),
      Compose' o1 o2 o4 (Compose' o2 o3 o4 m3 m2) m1 = Compose' o1 o3 o4 m3 (Compose' o1 o2 o3 m2 m1))
    (LeftIdentity' : forall (a b : obj) (f : Morphism a b), Compose' a b b (Identity' b) f = f)
    (RightIdentity' : forall (a b : obj) (f : Morphism a b), Compose' a a b f (Identity' a) = f) :
    @SpecializedCategory obj
    := Eval hnf in
        let C := (@Build_ComputationalCategory obj
                                               Morphism
                                               Identity' Compose') in
        @Build_SpecializedCategory' obj
                                    C
                                    (@Build_IsSpecializedCategory obj C
                                                                  Associativity'
                                                                  (fun _ _ _ _ _ _ _ => eq_sym (Associativity' _ _ _ _ _ _ _))
                                                                  LeftIdentity'
                                                                  RightIdentity').
End SpecializedCategoryInterface.

 
Create HintDb category discriminated.
 
Create HintDb morphism discriminated.

Hint Extern 1 => symmetry : category morphism.
 

Hint Immediate UnderlyingCCategory_IsSpecializedCategory : category morphism.

Ltac spcategory_hideProofs :=
  repeat match goal with
             | [ |- context[{|
                               Associativity := ?pf0;
                               Associativity_sym := ?pf1;
                               LeftIdentity := ?pf2;
                               RightIdentity := ?pf3
                             |}] ] =>
               hideProofs pf0 pf1 pf2 pf3
         end.

Hint Resolve @LeftIdentity @RightIdentity @Associativity : category morphism.
Hint Rewrite @LeftIdentity @RightIdentity using try specialized_category_is_specialized : category.
Hint Rewrite @LeftIdentity @RightIdentity using try specialized_category_is_specialized : morphism.

 
Definition LocallySmallSpecializedCategory (obj : Type)   := SpecializedCategory obj.
Definition SmallSpecializedCategory (obj : Set)   := SpecializedCategory obj.
Identity Coercion LocallySmallSpecializedCategory_SpecializedCategory_Id : LocallySmallSpecializedCategory >-> SpecializedCategory.
Identity Coercion SmallSpecializedCategory_LocallySmallSpecializedCategory_Id : SmallSpecializedCategory >-> SpecializedCategory.

Section Categories_Equal.
  Lemma SpecializedCategory_eq `(C : @SpecializedCategory objC) `(D : @SpecializedCategory objC) :
    @Morphism _ C = @Morphism _ D
    -> @Identity _ C == @Identity _ D
    -> @Compose _ C == @Compose _ D
    -> C = D.
    intros.
    destruct_head @SpecializedCategory; destruct_head @ComputationalCategory;
    simpl in *; repeat subst;
    f_equal; apply proof_irrelevance.
  Qed.

  Lemma SpecializedCategory_JMeq `(C : @SpecializedCategory objC) `(D : @SpecializedCategory objD) :
    objC = objD
    -> @Morphism _ C == @Morphism _ D
    -> @Identity _ C == @Identity _ D
    -> @Compose _ C == @Compose _ D
    -> C == D.
    intros; destruct_head @SpecializedCategory; destruct_head @ComputationalCategory;
    simpl in *; repeat subst; JMeq_eq;
    f_equal; apply proof_irrelevance.
  Qed.
End Categories_Equal.

Ltac spcat_eq_step_with tac :=
  structures_eq_step_with_tac ltac:(apply SpecializedCategory_eq || apply SpecializedCategory_JMeq) tac.

Ltac spcat_eq_with tac := repeat spcat_eq_step_with tac.
Ltac spcat_eq := spcategory_hideProofs; spcat_eq_with idtac.

 

Definition NoEvar T (_ : T) := True.

Lemma AssociativityNoEvar `(C : @SpecializedCategory obj) : forall (o1 o2 o3 o4 : C) (m1 : C.(Morphism) o1 o2)
  (m2 : C.(Morphism) o2 o3) (m3 : C.(Morphism) o3 o4),
  NoEvar (m1, m2) \/ NoEvar (m2, m3) \/ NoEvar (m1, m3)
  -> Compose (Compose m3 m2) m1 = Compose m3 (Compose m2 m1).
  intros; apply Associativity.
Qed.

Ltac noEvar := try specialized_category_is_specialized;
              match goal with
                | [ |- context[NoEvar ?X] ] => (has_evar X; fail 1)
                                                 || cut (NoEvar X); [ intro; tauto | constructor ]
              end.

Hint Rewrite @AssociativityNoEvar using noEvar : category.
Hint Rewrite @AssociativityNoEvar using noEvar : morphism.
Ltac try_associativity tac := try_rewrite_by AssociativityNoEvar ltac:(idtac; noEvar) tac.

 

Section Category.
  Context `(@IsSpecializedCategory obj C).

   
  Definition IsEpimorphism x y (m : C.(Morphism) x y) : Prop :=
    forall z (m1 m2 : C.(Morphism) y z), Compose m1 m = Compose m2 m ->
      m1 = m2.
  Definition IsMonomorphism x y (m : C.(Morphism) x y) : Prop :=
    forall z (m1 m2 : C.(Morphism) z x), Compose m m1 = Compose m m2 ->
      m1 = m2.

  Section properties.
    Lemma IdentityIsEpimorphism x : IsEpimorphism _ _ (Identity x).
      repeat intro; autorewrite with category in *; trivial.
    Qed.

    Lemma IdentityIsMonomorphism x : IsMonomorphism _ _ (Identity x).
      repeat intro; autorewrite with category in *; trivial.
    Qed.

    Lemma EpimorphismComposition s d d' m0 m1 :
      IsEpimorphism _ _ m0
      -> IsEpimorphism _ _ m1
      -> IsEpimorphism _ _ (Compose (C := C) (s := s) (d := d) (d' := d') m0 m1).
      repeat intro.
      repeat match goal with | [ H : _ |- _ ] => rewrite <- Associativity in H end.
      intuition.
    Qed.

    Lemma MonomorphismComposition s d d' m0 m1 :
      IsMonomorphism _ _ m0
      -> IsMonomorphism _ _ m1
      -> IsMonomorphism _ _ (Compose (C := C) (s := s) (d := d) (d' := d') m0 m1).
      repeat intro.
      repeat match goal with | [ H : _ |- _ ] => rewrite Associativity in H end.
      intuition.
    Qed.
  End properties.
End Category.

Hint Immediate @IdentityIsEpimorphism @IdentityIsMonomorphism @MonomorphismComposition @EpimorphismComposition : category morphism.

Arguments IsEpimorphism {obj} [C x y] m.
Arguments IsMonomorphism {obj} [C x y] m.

Section AssociativityComposition.
  Context `(C : @SpecializedCategory obj).
  Variables o0 o1 o2 o3 o4 : C.

  Lemma compose4associativity_helper
    (a : Morphism C o3 o4) (b : Morphism C o2 o3)
    (c : Morphism C o1 o2) (d : Morphism C o0 o1) :
    Compose (Compose a b) (Compose c d) = (Compose a (Compose (Compose b c) d)).
    repeat rewrite Associativity; reflexivity.
  Qed.
End AssociativityComposition.

Ltac compose4associativity' a b c d := transitivity (Compose a (Compose (Compose b c) d)); try solve [ apply compose4associativity_helper ].
Ltac compose4associativity :=
  match goal with
    | [ |- Compose (Compose ?a ?b) (Compose ?c ?d) = _ ] => compose4associativity' a b c d
    | [ |- _ = Compose (Compose ?a ?b) (Compose ?c ?d) ] => compose4associativity' a b c d
  end.


Set Implicit Arguments.

Set Universe Polymorphism.

Section DCategory.
  Variable O : Type.

  Local Ltac simpl_eq := subst_body; hnf in *; simpl in *; intros; destruct_type @inhabited; simpl in *;
    repeat constructor;
      repeat subst;
        auto;
          simpl_transitivity.

  Let DiscreteCategory_Morphism (s d : O) := s = d.

  Definition DiscreteCategory_Compose (s d d' : O) (m : DiscreteCategory_Morphism d d') (m' : DiscreteCategory_Morphism s d) :
    DiscreteCategory_Morphism s d'.
    simpl_eq.
  Defined.

  Definition DiscreteCategory_Identity o : DiscreteCategory_Morphism o o.
    simpl_eq.
  Defined.

  Global Arguments DiscreteCategory_Compose [s d d'] m m' /.
  Global Arguments DiscreteCategory_Identity o /.

  Definition DiscreteCategory : @SpecializedCategory O.
    refine (@Build_SpecializedCategory _
                                       DiscreteCategory_Morphism
                                       DiscreteCategory_Identity
                                       DiscreteCategory_Compose
                                       _
                                       _
                                       _);
    abstract (
        unfold DiscreteCategory_Compose, DiscreteCategory_Identity;
        simpl_eq
      ).
  Defined.
End DCategory.


Set Implicit Arguments.

Generalizable All Variables.

Set Universe Polymorphism.

Section Category'.
  Context `{C : @SpecializedCategory obj}.

   
   
  Definition IsInverseOf1 (s d : C) (m : C.(Morphism) s d) (m' : C.(Morphism) d s) : Prop :=
    Compose m' m = Identity s.
  Definition IsInverseOf2 (s d : C) (m : C.(Morphism) s d) (m' : C.(Morphism) d s) : Prop :=
    Compose m m' = Identity d.

  Global Arguments IsInverseOf1 / _ _ _ _.
  Global Arguments IsInverseOf2 / _ _ _ _.

  Definition IsInverseOf {s d : C} (m : C.(Morphism) s d) (m' : C.(Morphism) d s) : Prop := Eval simpl in
    @IsInverseOf1 s d m m' /\ @IsInverseOf2 s d m m'.

  Lemma IsInverseOf_sym s d m m' : @IsInverseOf s d m m' -> @IsInverseOf d s m' m.
    firstorder.
  Qed.

   
   
  Section IsomorphismOf.
     
    Record IsomorphismOf {s d : C} (m : C.(Morphism) s d) := {
      IsomorphismOf_Morphism :> C.(Morphism) s d := m;
      Inverse : C.(Morphism) d s;
      LeftInverse : Compose Inverse m = Identity s;
      RightInverse : Compose m Inverse = Identity d
    }.

    Hint Resolve RightInverse LeftInverse : category.
    Hint Resolve RightInverse LeftInverse : morphism.

    Definition IsomorphismOf_sig2 {s d : C} (m : C.(Morphism) s d) (i : @IsomorphismOf s d m) :
      { m' | Compose m' m = Identity s & Compose m m' = Identity d }.
      exists (Inverse i);
        [ apply LeftInverse | apply RightInverse ].
    Defined.

    Definition IsomorphismOf_sig {s d : C} (m : C.(Morphism) s d) := { m' | Compose m' m = Identity s & Compose m m' = Identity d }.

    Global Identity Coercion Isomorphism_sig : IsomorphismOf_sig >-> sig2.

    Definition sig2_IsomorphismOf {s d : C} (m : C.(Morphism) s d) (i : @IsomorphismOf_sig s d m) :
      @IsomorphismOf s d m.
      exists (proj1_sig i);
        [ apply (proj2_sig i) | apply (proj3_sig i) ].
    Defined.

    Global Coercion IsomorphismOf_sig2 : IsomorphismOf >-> sig2.
    Global Coercion sig2_IsomorphismOf : IsomorphismOf_sig >-> IsomorphismOf.

    Definition IsomorphismOf_Identity (c : C) : IsomorphismOf (Identity c).
      exists (Identity _); auto with morphism.
    Defined.

    Definition InverseOf {s d : C} (m : C.(Morphism) s d) (i : IsomorphismOf m) : IsomorphismOf (Inverse i).
      exists (i : Morphism C _ _); auto with morphism.
    Defined.

    Definition ComposeIsomorphismOf {s d d' : C} {m1 : C.(Morphism) d d'} {m2 : C.(Morphism) s d} (i1 : IsomorphismOf m1) (i2 : IsomorphismOf m2) :
      IsomorphismOf (Compose m1 m2).
      exists (Compose (Inverse i2) (Inverse i1));
      abstract (
          simpl; compose4associativity;
          destruct i1, i2; simpl;
          repeat (rewrite_hyp; autorewrite with morphism);
          trivial
        ).
    Defined.
  End IsomorphismOf.

  Section Isomorphism.
    Record Isomorphism (s d : C) := {
      Isomorphism_Morphism : C.(Morphism) s d;
      Isomorphism_Of :> IsomorphismOf Isomorphism_Morphism
    }.

    Global Coercion Build_Isomorphism : IsomorphismOf >-> Isomorphism.
  End Isomorphism.

  Section IsIsomorphism.
    Definition IsIsomorphism {s d : C} (m : C.(Morphism) s d) : Prop :=
      exists m', IsInverseOf m m'.

    Lemma IsomrphismOf_IsIsomorphism {s d : C} (m : C.(Morphism) s d) : IsomorphismOf m -> IsIsomorphism m.
      intro i; hnf.
      exists (Inverse i);
        destruct i; simpl;
        split;
        assumption.
    Qed.

    Lemma IsIsomorphism_IsomrphismOf {s d : C} (m : C.(Morphism) s d) : IsIsomorphism m -> exists _ : IsomorphismOf m, True.
      intro i; destruct_hypotheses.
      destruct_exists; trivial.
      eexists; eassumption.
    Qed.
  End IsIsomorphism.

  Section Isomorphic.
    Definition Isomorphic (s d : C) : Prop :=
      exists (m : C.(Morphism) s d) (m' : C.(Morphism) d s), IsInverseOf m m'.

    Lemma Isomrphism_Isomorphic s d : Isomorphism s d -> Isomorphic s d.
      intro i; destruct i as [ m i ].
      exists m.
      apply IsomrphismOf_IsIsomorphism; assumption.
    Qed.

    Lemma Isomorphic_Isomorphism s d : Isomorphic s d -> exists _ : Isomorphism s d, True.
      intro i; destruct_hypotheses.
      destruct_exists; trivial.
      repeat esplit; eassumption.
    Qed.

    Local Ltac t_iso' := intros;
      repeat match goal with
               | [ i : Isomorphic _ _ |- _ ] => destruct (Isomorphic_Isomorphism i) as [ ? [] ] ; clear i
               | [ |- Isomorphic _ _ ] => apply Isomrphism_Isomorphic
             end.

    Local Ltac t_iso:= t_iso';
      repeat match goal with
               | [ i : Isomorphism _ _ |- _ ] => unique_pose (Isomorphism_Of i); try clear i
               | [ |- Isomorphism _ _ ] => eapply Build_Isomorphism
             end.

    Hint Resolve @IsomorphismOf_Identity @InverseOf @ComposeIsomorphismOf : category morphism.

    Lemma Isomorphic_refl c : Isomorphic c c.
      t_iso.
      apply IsomorphismOf_Identity.
    Qed.

    Lemma Isomorphic_sym s d : Isomorphic s d -> Isomorphic d s.
      t_iso.
      eauto with morphism.
      Grab Existential Variables.
      eauto with morphism.
    Qed.

    Lemma Isomorphic_trans s d d' : Isomorphic s d -> Isomorphic d d' -> Isomorphic s d'.
      t_iso.
      apply @ComposeIsomorphismOf;
        eauto with morphism.
    Qed.

    Global Add Parametric Relation : _ Isomorphic
      reflexivity proved by Isomorphic_refl
      symmetry proved by Isomorphic_sym
      transitivity proved by Isomorphic_trans
        as Isomorphic_rel.
  End Isomorphic.

   
  Lemma iso_is_epi s d (m : _ s d) : IsIsomorphism m -> IsEpimorphism (C := C) m.
    destruct 1 as [ x [ i0 i1 ] ]; intros z m1 m2 e.
    transitivity (Compose m1 (Compose m x)); [ rewrite_hyp; autorewrite with morphism | ]; trivial.
    transitivity (Compose m2 (Compose m x)); [ repeat rewrite <- Associativity | ]; rewrite_hyp; autorewrite with morphism; trivial.
  Qed.

   
  Lemma iso_is_mono s d (m : _ s d) : IsIsomorphism m -> IsMonomorphism (C := C) m.
    destruct 1 as [ x [ i0 i1 ] ]; intros z m1 m2 e.
    transitivity (Compose (Compose x m) m1); [ rewrite_hyp; autorewrite with morphism | ]; trivial.
    transitivity (Compose (Compose x m) m2); [ repeat rewrite Associativity | ]; rewrite_hyp; autorewrite with morphism; trivial.
  Qed.
End Category'.

Hint Resolve @RightInverse @LeftInverse @IsomorphismOf_Identity @ComposeIsomorphismOf : category morphism.

Section CategoryObjects1.
  Context `(C : @SpecializedCategory obj).

  Definition UniqueUpToUniqueIsomorphism' (P : C.(Object) -> Prop) : Prop :=
    forall o, P o -> forall o', P o' -> exists m : C.(Morphism) o o', IsIsomorphism m /\ is_unique m.

  Definition UniqueUpToUniqueIsomorphism (P : C.(Object) -> Type) :=
    forall o, P o -> forall o', P o' -> { m : C.(Morphism) o o' | IsIsomorphism m & is_unique m }.

  Section terminal.
     
    Definition IsTerminalObject' (o : C) : Prop :=
      forall o', exists! m : C.(Morphism) o' o, True.

    Definition IsTerminalObject (o : C) :=
      forall o', { m : C.(Morphism) o' o | is_unique m }.

    Record TerminalObject :=
      {
        TerminalObject_Object' : obj;
        TerminalObject_Morphism : forall o, Morphism C o TerminalObject_Object';
        TerminalObject_Property : forall o, is_unique (TerminalObject_Morphism o)
      }.

    Definition TerminalObject_Object : TerminalObject -> C := TerminalObject_Object'.

    Global Coercion TerminalObject_Object : TerminalObject >-> Object.

    Definition TerminalObject_IsTerminalObject (o : TerminalObject) : IsTerminalObject o
      := fun o' => exist _ (TerminalObject_Morphism o o') (TerminalObject_Property o o').

    Definition IsTerminalObject_TerminalObject o : IsTerminalObject o -> TerminalObject
      := fun H => @Build_TerminalObject o (fun o' => proj1_sig (H o')) (fun o' => proj2_sig (H o')).

    Global Coercion TerminalObject_IsTerminalObject : TerminalObject >-> IsTerminalObject.
    Global Coercion IsTerminalObject_TerminalObject : IsTerminalObject >-> TerminalObject.
  End terminal.

  Section initial.
     
    Definition IsInitialObject' (o : C) : Prop :=
      forall o', exists! m : C.(Morphism) o o', True.

    Definition IsInitialObject (o : C) :=
      forall o', { m : C.(Morphism) o o' | is_unique m }.

    Record InitialObject :=
      {
        InitialObject_Object' :> obj;
        InitialObject_Morphism : forall o, Morphism C InitialObject_Object' o;
        InitialObject_Property : forall o, is_unique (InitialObject_Morphism o)
      }.

    Definition InitialObject_Object : InitialObject -> C := InitialObject_Object'.

    Global Coercion InitialObject_Object : InitialObject >-> Object.

    Definition InitialObject_IsInitialObject (o : InitialObject) : IsInitialObject o
      := fun o' => exist _ (InitialObject_Morphism o o') (InitialObject_Property o o').

    Definition IsInitialObject_InitialObject o : IsInitialObject o -> InitialObject
      := fun H => @Build_InitialObject o (fun o' => proj1_sig (H o')) (fun o' => proj2_sig (H o')).

    Global Coercion InitialObject_IsInitialObject : InitialObject >-> IsInitialObject.
    Global Coercion IsInitialObject_InitialObject : IsInitialObject >-> InitialObject.
  End initial.
End CategoryObjects1.

Arguments UniqueUpToUniqueIsomorphism {_ C} P.
Arguments IsInitialObject' {_ C} o.
Arguments IsInitialObject {_ C} o.
Arguments IsTerminalObject' {_ C} o.
Arguments IsTerminalObject {_ C} o.

Section CategoryObjects2.
  Context `(C : @SpecializedCategory obj).

  Ltac unique := hnf; intros; specialize_all_ways; destruct_sig;
    unfold is_unique, unique, uniqueness in *;
      repeat (destruct 1);
      repeat match goal with
               | [ x : _ |- _ ] => exists x
             end; eauto with category; try split; try solve [ etransitivity; eauto with category ].

   
  Theorem TerminalObjectUnique : UniqueUpToUniqueIsomorphism (IsTerminalObject (C := C)).
    unique.
  Qed.

   
  Theorem InitialObjectUnique : UniqueUpToUniqueIsomorphism (IsInitialObject (C := C)).
    unique.
  Qed.
End CategoryObjects2.


Set Implicit Arguments.

Generalizable All Variables.

Set Universe Polymorphism.

Record > Category := {
  CObject : Type;

  UnderlyingCategory :> @SpecializedCategory CObject
}.

Record > SmallCategory := {
  SObject : Set;

  SUnderlyingCategory :> @SmallSpecializedCategory SObject
}.

Record > LocallySmallCategory := {
  LSObject : Type;

  LSUnderlyingCategory :> @LocallySmallSpecializedCategory LSObject
}.

Bind Scope category_scope with Category.
Bind Scope category_scope with SmallCategory.
Bind Scope category_scope with LocallySmallCategory.



 

 

Ltac saturate := repeat match goal with
                          | [ H : @eq (Morphism _ _ _) ?M ?N |- _ ] =>
                            let tryIt G :=
                              match goal with
                                | [ _ : G |- _ ] => fail 1
                                | [ |- context[G] ] => fail 1
                                | _ => let H' := fresh "H" in assert (H' : G) by eauto; generalize dependent H'
                              end in
                              repeat match goal with
                                       | [ m : Morphism _ _ _ |- _ ] =>
                                         tryIt (Compose M m = Compose N m)
                                       | [ m : Morphism _ _ _ |- _ ] =>
                                         tryIt (Compose m M = Compose m N)
                                     end; generalize dependent H
                        end; intros; autorewrite with core in *.

 

Ltac extractMorphisms G :=
  match G with
    | Compose ?G1 ?G2 =>
      extractMorphisms G1;
      extractMorphisms G2
    | _ =>
      match goal with
        | [ x := G |- _ ] => idtac
        | [ x : _ |- _ ] =>
          match x with
            | G => idtac
          end
        | _ => pose G
      end
  end.

 

Ltac createVariables :=
  match goal with
    | [ |- @eq (Morphism _ _ _) ?X ?Y ] =>
      extractMorphisms X;
      extractMorphisms Y
  end.

 

Ltac removeVariables :=
  repeat match goal with
           | [ x := _ |- _ ] => subst x
         end.

 

Tactic Notation "morphisms" integer(numSaturations) :=
  t; createVariables; do numSaturations saturate; removeVariables; eauto 3.


Set Implicit Arguments.

Generalizable All Variables.

Set Universe Polymorphism.

Local Infix "==" := JMeq.

Section SpecializedFunctor.
  Context `(C : @SpecializedCategory objC).
  Context `(D : @SpecializedCategory objD).

   
  Record SpecializedFunctor :=
    {
      ObjectOf :> objC -> objD;
      MorphismOf : forall s d, C.(Morphism) s d -> D.(Morphism) (ObjectOf s) (ObjectOf d);
      FCompositionOf : forall s d d' (m1 : C.(Morphism) s d) (m2: C.(Morphism) d d'),
                          MorphismOf _ _ (Compose m2 m1) = Compose (MorphismOf _ _ m2) (MorphismOf _ _ m1);
      FIdentityOf : forall x, MorphismOf _ _ (Identity x) = Identity (ObjectOf x)
    }.
End SpecializedFunctor.

Section Functor.
  Variable C D : Category.

  Definition Functor := SpecializedFunctor C D.
End Functor.

Bind Scope functor_scope with SpecializedFunctor.
Bind Scope functor_scope with Functor.

Create HintDb functor discriminated.

Identity Coercion Functor_SpecializedFunctor_Id : Functor >-> SpecializedFunctor.
Definition GeneralizeFunctor objC C objD D (F : @SpecializedFunctor objC C objD D) : Functor C D := F.
Coercion GeneralizeFunctor : SpecializedFunctor >-> Functor.

 
Arguments GeneralizeFunctor [objC C objD D] F /.
Hint Extern 0 => unfold GeneralizeFunctor : category functor.

Arguments SpecializedFunctor {objC} C {objD} D.
Arguments Functor C D.
Arguments ObjectOf {objC%type C%category objD%type D%category} F%functor c%object : rename, simpl nomatch.
Arguments MorphismOf {objC%type} [C%category] {objD%type} [D%category] F%functor [s%object d%object] m%morphism : rename, simpl nomatch.

Arguments FCompositionOf [objC C objD D] F _ _ _ _ _ : rename.
Arguments FIdentityOf [objC C objD D] F _ : rename.

Hint Resolve @FCompositionOf @FIdentityOf : category functor.
Hint Rewrite @FIdentityOf : category.
Hint Rewrite @FIdentityOf : functor.

Ltac functor_hideProofs :=
  repeat match goal with
             | [ |- context[{|
                               ObjectOf := _;
                               MorphismOf := _;
                               FCompositionOf := ?pf0;
                               FIdentityOf := ?pf1
                             |}] ] =>
               hideProofs pf0 pf1
         end.

Ltac functor_tac_abstract_trailing_props F tac :=
  let F' := (eval hnf in F) in
  let F'' := (tac F') in
  let H := fresh in
  pose F'' as H;
    hnf in H;
    revert H; clear; intro H; clear H;
    match F'' with
      | @Build_SpecializedFunctor ?objC ?C
                                  ?objD ?D
                                  ?OO
                                  ?MO
                                  ?FCO
                                  ?FIO =>
        refine (@Build_SpecializedFunctor objC C objD D
                                          OO
                                          MO
                                          _
                                          _);
          [ abstract exact FCO | abstract exact FIO ]
    end.
Ltac functor_abstract_trailing_props F := functor_tac_abstract_trailing_props F ltac:(fun F' => F').
Ltac functor_simpl_abstract_trailing_props F := functor_tac_abstract_trailing_props F ltac:(fun F' => let F'' := eval simpl in F' in F'').

Section Functors_Equal.
  Lemma Functor_eq' objC C objD D : forall (F G : @SpecializedFunctor objC C objD D),
    ObjectOf F = ObjectOf G
    -> MorphismOf F == MorphismOf G
    -> F = G.
    destruct F, G; simpl; intros; specialize_all_ways; repeat subst;
      f_equal; apply proof_irrelevance.
  Qed.

  Lemma Functor_eq objC C objD D :
    forall (F G : @SpecializedFunctor objC C objD D),
      (forall x, ObjectOf F x = ObjectOf G x)
      -> (forall s d m, MorphismOf F (s := s) (d := d) m == MorphismOf G (s := s) (d := d) m)
      -> F = G.
    intros; cut (ObjectOf F = ObjectOf G); intros; try apply Functor_eq'; destruct F, G; simpl in *; repeat subst;
    try apply eq_JMeq;
    repeat (apply functional_extensionality_dep; intro); trivial;
    try apply JMeq_eq; trivial.
  Qed.

  Lemma Functor_JMeq objC C objD D objC' C' objD' D' :
    forall (F : @SpecializedFunctor objC C objD D) (G : @SpecializedFunctor objC' C' objD' D'),
      objC = objC'
      -> objD = objD'
      -> C == C'
      -> D == D'
      -> ObjectOf F == ObjectOf G
      -> MorphismOf F == MorphismOf G
      -> F == G.
    simpl; intros; intuition; repeat subst; destruct F, G; simpl in *;
      repeat subst; JMeq_eq.
    f_equal; apply proof_irrelevance.
  Qed.
End Functors_Equal.

Ltac functor_eq_step_with tac :=
  structures_eq_step_with_tac ltac:(apply Functor_eq || apply Functor_JMeq) tac.

Ltac functor_eq_with tac := repeat functor_eq_step_with tac.
Ltac functor_eq := functor_hideProofs; functor_eq_with idtac.

Section FunctorComposition.
  Context `(B : @SpecializedCategory objB).
  Context `(C : @SpecializedCategory objC).
  Context `(D : @SpecializedCategory objD).
  Context `(E : @SpecializedCategory objE).

  Hint Rewrite @FCompositionOf : functor.

  Definition ComposeFunctors (G : SpecializedFunctor D E) (F : SpecializedFunctor C D) : SpecializedFunctor C E.
    refine (Build_SpecializedFunctor C E
                                     (fun c => G (F c))
                                     (fun _ _ m => G.(MorphismOf) (F.(MorphismOf) m))
                                     _
                                     _);
    abstract (
        intros; autorewrite with functor; reflexivity
      ).
  Defined.
End FunctorComposition.

Section IdentityFunctor.
  Context `(C : @SpecializedCategory objC).

   
  Definition IdentityFunctor : SpecializedFunctor C C.
    refine {| ObjectOf := (fun x => x);
              MorphismOf := (fun _ _ x => x)
           |};
    abstract t.
  Defined.
End IdentityFunctor.

Section IdentityFunctorLemmas.
  Context `(C : @SpecializedCategory objC).
  Context `(D : @SpecializedCategory objD).

  Lemma LeftIdentityFunctor (F : SpecializedFunctor D C) : ComposeFunctors (IdentityFunctor _) F = F.
    functor_eq.
  Qed.

  Lemma RightIdentityFunctor (F : SpecializedFunctor C D) : ComposeFunctors F (IdentityFunctor _) = F.
    functor_eq.
  Qed.
End IdentityFunctorLemmas.

Hint Rewrite @LeftIdentityFunctor @RightIdentityFunctor : category.
Hint Rewrite @LeftIdentityFunctor @RightIdentityFunctor : functor.
Hint Immediate @LeftIdentityFunctor @RightIdentityFunctor : category functor.

Section FunctorCompositionLemmas.
  Context `(B : @SpecializedCategory objB).
  Context `(C : @SpecializedCategory objC).
  Context `(D : @SpecializedCategory objD).
  Context `(E : @SpecializedCategory objE).

  Lemma ComposeFunctorsAssociativity (F : SpecializedFunctor B C) (G : SpecializedFunctor C D) (H : SpecializedFunctor D E) :
    ComposeFunctors (ComposeFunctors H G) F = ComposeFunctors H (ComposeFunctors G F).
    functor_eq.
  Qed.
End FunctorCompositionLemmas.

Hint Resolve @ComposeFunctorsAssociativity : category functor.


Set Implicit Arguments.

Generalizable All Variables.

Set Universe Polymorphism.

Local Infix "==" := JMeq.

Section SpecializedNaturalTransformation.
  Context `(C : @SpecializedCategory objC).
  Context `(D : @SpecializedCategory objD).
  Variables F G : SpecializedFunctor C D.

   
  Record SpecializedNaturalTransformation :=
    {
      ComponentsOf :> forall c, D.(Morphism) (F c) (G c);
      Commutes : forall s d (m : C.(Morphism) s d),
                   Compose (ComponentsOf d) (F.(MorphismOf) m) = Compose (G.(MorphismOf) m) (ComponentsOf s)
    }.
End SpecializedNaturalTransformation.

Section NaturalTransformation.
  Variable C D : Category.
  Variable F G : Functor C D.

  Definition NaturalTransformation := SpecializedNaturalTransformation F G.
End NaturalTransformation.

Bind Scope natural_transformation_scope with SpecializedNaturalTransformation.
Bind Scope natural_transformation_scope with NaturalTransformation.

Create HintDb natural_transformation discriminated.

Arguments ComponentsOf {objC%type C%category objD%type D%category F%functor G%functor} T%natural_transformation c%object : rename, simpl nomatch.
Arguments Commutes [objC C objD D F G] T _ _ _ : rename.

Identity Coercion NaturalTransformation_SpecializedNaturalTransformation_Id : NaturalTransformation >-> SpecializedNaturalTransformation.
Definition GeneralizeNaturalTransformation `(T : @SpecializedNaturalTransformation objC C objD D F G) :
  NaturalTransformation F G := T.
Global Coercion GeneralizeNaturalTransformation : SpecializedNaturalTransformation >-> NaturalTransformation.

Arguments GeneralizeNaturalTransformation [objC C objD D F G] T /.
Hint Extern 0 => unfold GeneralizeNaturalTransformation : category natural_transformation.

Hint Resolve @Commutes : category natural_transformation.

Ltac nt_hideProofs :=
  repeat match goal with
             | [ |- context[{|
                               ComponentsOf := _;
                               Commutes := ?pf
                             |}] ] =>
               hideProofs pf
         end.

Section NaturalTransformations_Equal.
  Lemma NaturalTransformation_eq' objC C objD D F G :
    forall (T U : @SpecializedNaturalTransformation objC C objD D F G),
    ComponentsOf T = ComponentsOf U
    -> T = U.
    destruct T, U; simpl; intros; repeat subst;
      f_equal; apply proof_irrelevance.
  Qed.

  Lemma NaturalTransformation_eq objC C objD D F G :
    forall (T U : @SpecializedNaturalTransformation objC C objD D F G),
    (forall x, ComponentsOf T x = ComponentsOf U x)
    -> T = U.
    intros; apply NaturalTransformation_eq'; destruct T, U; simpl in *; repeat subst;
    apply functional_extensionality_dep; trivial.
  Qed.

  Lemma NaturalTransformation_JMeq' objC C objD D objC' C' objD' D' :
    forall F G F' G'
      (T : @SpecializedNaturalTransformation objC C objD D F G) (U : @SpecializedNaturalTransformation objC' C' objD' D' F' G'),
      objC = objC'
      -> objD = objD'
      -> C == C'
      -> D == D'
      -> F == F'
      -> G == G'
      -> ComponentsOf T == ComponentsOf U
      -> T == U.
    simpl; intros; intuition; destruct T, U; simpl in *; repeat subst;
      JMeq_eq.
    f_equal; apply proof_irrelevance.
  Qed.
  Lemma NaturalTransformation_JMeq objC C objD D objC' C' objD' D' :
    forall F G F' G'
      (T : @SpecializedNaturalTransformation objC C objD D F G) (U : @SpecializedNaturalTransformation objC' C' objD' D' F' G'),
      objC = objC'
      -> objD = objD'
      -> C == C'
      -> D == D'
      -> F == F'
      -> G == G'
      -> (forall x x', x == x' -> ComponentsOf T x == ComponentsOf U x')
      -> T == U.
    intros; apply NaturalTransformation_JMeq'; trivial;
    destruct T, U; simpl in *; repeat subst.
    apply functional_extensionality_dep_JMeq; trivial.
    intuition.
  Qed.
End NaturalTransformations_Equal.

Ltac nt_eq_step_with tac :=
  structures_eq_step_with_tac ltac:(apply NaturalTransformation_eq || apply NaturalTransformation_JMeq) tac.

Ltac nt_eq_with tac := repeat nt_eq_step_with tac.
Ltac nt_eq := nt_hideProofs; nt_eq_with idtac.

Section NaturalTransformationComposition.
  Context `(C : @SpecializedCategory objC).
  Context `(D : @SpecializedCategory objD).
  Context `(E : @SpecializedCategory objE).
  Variables F F' F'' : SpecializedFunctor C D.
  Variables G G' : SpecializedFunctor D E.

  Hint Resolve @Commutes f_equal f_equal2 : natural_transformation.
  Hint Rewrite @Associativity : natural_transformation.

   

  Definition NTComposeT (T' : SpecializedNaturalTransformation F' F'') (T : SpecializedNaturalTransformation F F') :
    SpecializedNaturalTransformation F F''.
    exists (fun c => Compose (T' c) (T c));
     
    abstract (
        intros;
        transitivity (Compose (T' _) (Compose (MorphismOf F' m) (T _)));
        try_associativity ltac:(eauto with natural_transformation)
      ).
  Defined.

   
   

  Hint Rewrite @Commutes : natural_transformation.
  Hint Resolve f_equal2 : natural_transformation.
  Hint Extern 1 (_ = _) => apply @FCompositionOf : natural_transformation.

  Lemma FCompositionOf2 : forall `(C : @SpecializedCategory objC) `(D : @SpecializedCategory objD)
    (F : SpecializedFunctor C D) x y z u (m1 : C.(Morphism) x z) (m2 : C.(Morphism) y x) (m3 : D.(Morphism) u _),
    Compose (MorphismOf F m1) (Compose (MorphismOf F m2) m3) = Compose (MorphismOf F (Compose m1 m2)) m3.
    intros; symmetry; try_associativity ltac:(eauto with natural_transformation).
  Qed.

  Hint Rewrite @FCompositionOf2 : natural_transformation.

  Definition NTComposeF (U : SpecializedNaturalTransformation G G') (T : SpecializedNaturalTransformation F F'):
    SpecializedNaturalTransformation (ComposeFunctors G F) (ComposeFunctors G' F').
    exists (fun c => Compose (G'.(MorphismOf) (T c)) (U (F c)));
    abstract (
        simpl; intros; autorewrite with category;
        repeat try_associativity ltac:(repeat rewrite <- @Commutes; repeat rewrite <- @FCompositionOf);
        reflexivity
      ).
  Defined.
End NaturalTransformationComposition.

Section IdentityNaturalTransformation.
  Context `(C : @SpecializedCategory objC).
  Context `(D : @SpecializedCategory objD).
  Variable F : SpecializedFunctor C D.

   
  Definition IdentityNaturalTransformation : SpecializedNaturalTransformation F F.
    exists (fun c => Identity (F c));
    abstract (intros; autorewrite with morphism; reflexivity).
  Defined.

  Lemma LeftIdentityNaturalTransformation (F' : SpecializedFunctor C D) (T : SpecializedNaturalTransformation F' F) :
    NTComposeT IdentityNaturalTransformation T = T.
    nt_eq; auto with morphism.
  Qed.

  Lemma RightIdentityNaturalTransformation (F' : SpecializedFunctor C D) (T : SpecializedNaturalTransformation F F') :
    NTComposeT T IdentityNaturalTransformation = T.
    nt_eq; auto with morphism.
  Qed.
End IdentityNaturalTransformation.

Hint Rewrite @LeftIdentityNaturalTransformation @RightIdentityNaturalTransformation : category.
Hint Rewrite @LeftIdentityNaturalTransformation @RightIdentityNaturalTransformation : natural_transformation.

Section IdentityNaturalTransformationF.
  Context `(C : @SpecializedCategory objC).
  Context `(D : @SpecializedCategory objD).
  Context `(E : @SpecializedCategory objE).
  Variable G : SpecializedFunctor D E.
  Variable F : SpecializedFunctor C D.

  Lemma NTComposeFIdentityNaturalTransformation :
    NTComposeF (IdentityNaturalTransformation G) (IdentityNaturalTransformation F) = IdentityNaturalTransformation (ComposeFunctors G F).
  Proof.
    nt_eq; repeat rewrite FIdentityOf; auto with morphism.
  Qed.
End IdentityNaturalTransformationF.

Hint Rewrite @NTComposeFIdentityNaturalTransformation : category.
Hint Rewrite @NTComposeFIdentityNaturalTransformation : natural_transformation.

Section Associativity.
  Context `(B : @SpecializedCategory objB).
  Context `(C : @SpecializedCategory objC).
  Context `(D : @SpecializedCategory objD).
  Context `(E : @SpecializedCategory objE).
  Variable F : SpecializedFunctor D E.
  Variable G : SpecializedFunctor C D.
  Variable H : SpecializedFunctor B C.

  Let F0 := ComposeFunctors (ComposeFunctors F G) H.
  Let F1 := ComposeFunctors F (ComposeFunctors G H).

  Definition ComposeFunctorsAssociator1 : SpecializedNaturalTransformation F0 F1.
    refine (Build_SpecializedNaturalTransformation F0 F1
                                                   (fun _ => Identity (C := E) _)
                                                   _
           );
    abstract (
        simpl; intros;
        autorewrite with morphism; reflexivity
      ).
  Defined.

  Definition ComposeFunctorsAssociator2 : SpecializedNaturalTransformation F1 F0.
    refine (Build_SpecializedNaturalTransformation F1 F0
                                                   (fun _ => Identity (C := E) _)
                                                   _
           );
    abstract (
        simpl; intros;
        autorewrite with morphism; reflexivity
      ).
  Defined.
End Associativity.

Section IdentityFunctor'.
  Context `(C : @SpecializedCategory objC).
  Context `(D : @SpecializedCategory objD).

  Local Ltac t :=
    repeat match goal with
             | [ |- SpecializedNaturalTransformation ?F ?G ] =>
               refine (Build_SpecializedNaturalTransformation F G
                                                              (fun _ => Identity _)
                                                              _)
             | _ => abstract (simpl; intros; autorewrite with morphism; reflexivity)
             | _ => split; nt_eq
           end.

  Section left.
    Variable F : SpecializedFunctor D C.

    Definition LeftIdentityFunctorNaturalTransformation1 : SpecializedNaturalTransformation (ComposeFunctors (IdentityFunctor _) F) F.
t.
Defined.
    Definition LeftIdentityFunctorNaturalTransformation2 : SpecializedNaturalTransformation F (ComposeFunctors (IdentityFunctor _) F).
t.
Defined.

    Theorem LeftIdentityFunctorNT_Isomorphism
    : NTComposeT LeftIdentityFunctorNaturalTransformation1 LeftIdentityFunctorNaturalTransformation2 = IdentityNaturalTransformation _
      /\ NTComposeT LeftIdentityFunctorNaturalTransformation2 LeftIdentityFunctorNaturalTransformation1 = IdentityNaturalTransformation _.
      t.
    Qed.
  End left.

  Section right.
    Variable F : SpecializedFunctor C D.

    Definition RightIdentityFunctorNaturalTransformation1 : SpecializedNaturalTransformation (ComposeFunctors F (IdentityFunctor _)) F.
t.
Defined.
    Definition RightIdentityFunctorNaturalTransformation2 : SpecializedNaturalTransformation F (ComposeFunctors F (IdentityFunctor _)).
t.
Defined.

    Theorem RightIdentityFunctorNT_Isomorphism
    : NTComposeT RightIdentityFunctorNaturalTransformation1 RightIdentityFunctorNaturalTransformation2 = IdentityNaturalTransformation _
      /\ NTComposeT RightIdentityFunctorNaturalTransformation2 RightIdentityFunctorNaturalTransformation1 = IdentityNaturalTransformation _.
      t.
    Qed.
  End right.
End IdentityFunctor'.

Section NaturalTransformationExchangeLaw.
  Context `(C : SpecializedCategory objC).
  Context `(D : SpecializedCategory objD).
  Context `(E : SpecializedCategory objE).

  Variables F G H : SpecializedFunctor C D.
  Variables F' G' H' : SpecializedFunctor D E.

  Variable T : SpecializedNaturalTransformation F G.
  Variable U : SpecializedNaturalTransformation G H.

  Variable T' : SpecializedNaturalTransformation F' G'.
  Variable U' : SpecializedNaturalTransformation G' H'.

  Local Ltac t_progress := progress repeat
    match goal with
      | _ => apply f_equal
      | _ => apply f_equal2; try reflexivity; []
      | _ => apply Commutes
      | _ => symmetry; apply Commutes
    end.

  Local Ltac t_exch := repeat
    match goal with
      | _ => repeat rewrite FCompositionOf; repeat rewrite Associativity;
        t_progress
      | _ => repeat rewrite <- FCompositionOf; repeat rewrite <- Associativity;
        t_progress
    end.

  Theorem NaturalTransformationExchangeLaw :
    NTComposeF (NTComposeT U' T') (NTComposeT U T) =
    NTComposeT (NTComposeF U' U) (NTComposeF T' T).
  Proof.
    nt_eq;
    t_exch.
  Qed.
End NaturalTransformationExchangeLaw.

Hint Resolve @NaturalTransformationExchangeLaw : category.
Hint Resolve @NaturalTransformationExchangeLaw : natural_transformation.


Set Implicit Arguments.

Generalizable All Variables.

Set Universe Polymorphism.

Section ProductCategory.
  Context `(C : @SpecializedCategory objC).
  Context `(D : @SpecializedCategory objD).

  Definition ProductCategory : @SpecializedCategory (objC * objD)%type.
    refine (@Build_SpecializedCategory _
                                       (fun s d => (C.(Morphism) (fst s) (fst d) * D.(Morphism) (snd s) (snd d))%type)
                                       (fun o => (Identity (fst o), Identity (snd o)))
                                       (fun s d d' m2 m1 => (Compose (fst m2) (fst m1), Compose (snd m2) (snd m1)))
                                       _
                                       _
                                       _);
    abstract (intros; simpl_eq; auto with morphism).
  Defined.
End ProductCategory.

Infix "*" := ProductCategory : category_scope.

Section ProductCategoryFunctors.
  Context `{C : @SpecializedCategory objC}.
  Context `{D : @SpecializedCategory objD}.

  Definition fst_Functor : SpecializedFunctor (C * D) C.
    refine (Build_SpecializedFunctor (C * D) C
      (@fst _ _)
      (fun _ _ => @fst _ _)
      _
      _
    );
    abstract eauto.
  Defined.

  Definition snd_Functor : SpecializedFunctor (C * D) D.
    refine (Build_SpecializedFunctor (C * D) D
      (@snd _ _)
      (fun _ _ => @snd _ _)
      _
      _
    );
    abstract eauto.
  Defined.
End ProductCategoryFunctors.


Set Implicit Arguments.

Generalizable All Variables.

Set Universe Polymorphism.

Local Infix "==" := JMeq.

Local Open Scope category_scope.

Section OppositeCategory.
  Definition OppositeComputationalCategory `(C : @ComputationalCategory objC) : ComputationalCategory objC :=
    @Build_ComputationalCategory objC
                                 (fun s d => Morphism C d s)
                                 (Identity (C := C))
                                 (fun _ _ _ m1 m2 => Compose m2 m1).

  Instance OppositeIsSpecializedCategory `(H : @IsSpecializedCategory objC C) : IsSpecializedCategory (OppositeComputationalCategory C) :=
    @Build_IsSpecializedCategory objC (OppositeComputationalCategory C)
                                 (fun _ _ _ _ _ _ _ => @Associativity_sym _ _ _ _ _ _ _ _ _ _)
                                 (fun _ _ _ _ _ _ _ => @Associativity _ _ _ _ _ _ _ _ _ _)
                                 (fun _ _ => @RightIdentity _ _ _ _ _)
                                 (fun _ _ => @LeftIdentity _ _ _ _ _).

  Definition OppositeCategory `(C : @SpecializedCategory objC) : @SpecializedCategory objC :=
    @Build_SpecializedCategory' objC
                                (OppositeComputationalCategory (UnderlyingCCategory C))
                                _.

End OppositeCategory.

 

Section DualCategories.
  Context `(C : @SpecializedCategory objC).
  Context `(D : @SpecializedCategory objD).

  Lemma op_op_id : OppositeCategory (OppositeCategory C) = C.
    clear D objD.
    unfold OppositeCategory, OppositeComputationalCategory; simpl.
    repeat change (fun a => ?f a) with f.
    destruct C as [ C' [ ] ]; destruct C'; intros; simpl; reflexivity.
  Qed.

  Lemma op_distribute_prod : OppositeCategory (C * D) = (OppositeCategory C) * (OppositeCategory D).
    spcat_eq.
  Qed.
End DualCategories.

Hint Rewrite @op_op_id @op_distribute_prod : category.

Section DualObjects.
  Context `(C : @SpecializedCategory objC).

  Definition terminal_opposite_initial (o : C) : IsTerminalObject o -> IsInitialObject (C := OppositeCategory C) o
    := fun H o' => H o'.

  Definition initial_opposite_terminal (o : C) : IsInitialObject o -> IsTerminalObject (C := OppositeCategory C) o
    := fun H o' => H o'.

  Definition terminal_to_opposite_initial : TerminalObject C -> InitialObject (OppositeCategory C)
    := Eval cbv beta iota zeta delta [terminal_opposite_initial TerminalObject_IsTerminalObject IsInitialObject_InitialObject proj1_sig proj2_sig] in
        fun x => terminal_opposite_initial x.

  Definition initial_to_opposite_terminal : InitialObject C -> TerminalObject (OppositeCategory C)
    := Eval cbv beta iota zeta delta [initial_opposite_terminal IsTerminalObject_TerminalObject InitialObject_IsInitialObject proj1_sig proj2_sig] in
        fun x => initial_opposite_terminal x.
End DualObjects.

Section OppositeFunctor.
  Context `(C : @SpecializedCategory objC).
  Context `(D : @SpecializedCategory objD).
  Variable F : SpecializedFunctor C D.
  Let COp := OppositeCategory C.
  Let DOp := OppositeCategory D.

  Definition OppositeFunctor : SpecializedFunctor COp DOp.
    refine (Build_SpecializedFunctor COp DOp
      (fun c : COp => F c : DOp)
      (fun (s d : COp) (m : C.(Morphism) d s) => MorphismOf F (s := d) (d := s) m)
      (fun d' d s m1 m2 => FCompositionOf F s d d' m2 m1)
      (FIdentityOf F)
    ).
  Defined.
End OppositeFunctor.

 

Section OppositeFunctor_Id.
  Context `(C : @SpecializedCategory objC).
  Context `(D : @SpecializedCategory objD).
  Variable F : SpecializedFunctor C D.

  Lemma op_op_functor_id : OppositeFunctor (OppositeFunctor F) == F.
    functor_eq; autorewrite with category; trivial.
  Qed.
End OppositeFunctor_Id.

 
 

Section OppositeNaturalTransformation.
  Context `(C : @SpecializedCategory objC).
  Context `(D : @SpecializedCategory objD).
  Variables F G : SpecializedFunctor C D.
  Variable T : SpecializedNaturalTransformation F G.
  Let COp := OppositeCategory C.
  Let DOp := OppositeCategory D.
  Let FOp := OppositeFunctor F.
  Let GOp := OppositeFunctor G.

  Definition OppositeNaturalTransformation : SpecializedNaturalTransformation GOp FOp.
    refine (Build_SpecializedNaturalTransformation GOp FOp
      (fun c : COp => T.(ComponentsOf) c : DOp.(Morphism) (GOp c) (FOp c))
      (fun s d m => eq_sym (Commutes T d s m))
    ).
  Defined.
End OppositeNaturalTransformation.

 

Section OppositeNaturalTransformation_Id.
  Context `(C : @SpecializedCategory objC).
  Context `(D : @SpecializedCategory objD).
  Variables F G : SpecializedFunctor C D.
  Variable T : SpecializedNaturalTransformation F G.

  Lemma op_op_nt_id : OppositeNaturalTransformation (OppositeNaturalTransformation T) == T.
    nt_eq; intros; try functor_eq; autorewrite with category; subst; trivial.
  Qed.
End OppositeNaturalTransformation_Id.

 
 


Set Implicit Arguments.

Generalizable All Variables.

Set Universe Polymorphism.

Section SumCategory.
  Context `(C : @SpecializedCategory objC).
  Context `(D : @SpecializedCategory objD).

  Definition SumCategory_Morphism (s d : objC + objD) : Type
    := match (s, d) with
         | (inl s, inl d) => C.(Morphism) s d
         | (inr s, inr d) => D.(Morphism) s d
         | _ => Empty_set
       end.

  Global Arguments SumCategory_Morphism _ _ /.

  Definition SumCategory_Identity (x : C + D) : SumCategory_Morphism x x
    := match x with
         | inl x => Identity x
         | inr x => Identity x
       end.

  Global Arguments SumCategory_Identity _ /.

  Definition SumCategory_Compose (s d d' : C + D) (m1 : SumCategory_Morphism d d') (m2 : SumCategory_Morphism s d) : SumCategory_Morphism s d'.
     
    case s, d, d'; simpl in *; try destruct_to_empty_set;
    eapply Compose; eassumption.
  Defined.

  Global Arguments SumCategory_Compose [_ _ _] _ _ /.

  Definition SumCategory : @SpecializedCategory (objC + objD)%type.
    refine (@Build_SpecializedCategory _
                                       SumCategory_Morphism
                                       SumCategory_Identity
                                       SumCategory_Compose
                                       _
                                       _
                                       _);
    abstract (
        repeat match goal with
                 | [ H : Empty_set |- _ ] => case H
                 | _ => let H := fresh in intro H; try (case H; clear H); simpl in *
               end;
        auto with morphism
      ).
  Defined.
End SumCategory.

Infix "+" := SumCategory : category_scope.

Section SumCategoryFunctors.
  Context `(C : @SpecializedCategory objC).
  Context `(D : @SpecializedCategory objD).

  Definition inl_Functor : SpecializedFunctor C (C + D).
    match goal with
      | [ |- SpecializedFunctor ?C ?D ] =>
        refine (Build_SpecializedFunctor C D
          (@inl _ _)
          (fun _ _ m => m)
          _
          _
        )
    end;
    abstract eauto.
  Defined.

  Definition inr_Functor : SpecializedFunctor D (C + D).
    match goal with
      | [ |- SpecializedFunctor ?C ?D ] =>
        refine (Build_SpecializedFunctor C D
          (@inr _ _)
          (fun _ _ m => m)
          _
          _
        )
    end;
    abstract eauto.
  Defined.
End SumCategoryFunctors.


Set Implicit Arguments.

Generalizable All Variables.

Set Asymmetric Patterns.

Set Universe Polymorphism.

Section SimplifiedMorphism.
  Inductive ReifiedMorphism : forall objC (C : SpecializedCategory objC), C -> C -> Type :=
  | ReifiedIdentityMorphism : forall objC C x, @ReifiedMorphism objC C x x
  | ReifiedComposedMorphism : forall objC C s d d', ReifiedMorphism C d d' -> ReifiedMorphism C s d -> @ReifiedMorphism objC C s d'
  | ReifiedNaturalTransformationMorphism : forall objB (B : SpecializedCategory objB)
                                                  objC (C : SpecializedCategory objC)
                                                  (F G : SpecializedFunctor B C)
                                                  (T : SpecializedNaturalTransformation F G)
                                                  x,
                                             ReifiedMorphism C (F x) (G x)
  | ReifiedFunctorMorphism : forall objB (B : SpecializedCategory objB)
                                    objC (C : SpecializedCategory objC)
                                    (F : SpecializedFunctor B C)
                                    s d,
                               @ReifiedMorphism objB B s d -> @ReifiedMorphism objC C (F s) (F d)
  | ReifiedGenericMorphism : forall objC (C : SpecializedCategory objC) s d, Morphism C s d -> @ReifiedMorphism objC C s d.

  Fixpoint ReifiedMorphismSimplify objC C s d (m : @ReifiedMorphism objC C s d) : ReifiedMorphism C s d
    := match
        m in (ReifiedMorphism C s d) return (ReifiedMorphism C s d)
      with
        | ReifiedComposedMorphism _ _ _ _ _ m1 m2 =>
          match
            ReifiedMorphismSimplify m1
            in (ReifiedMorphism C d d')
            return
            (forall s,
               ReifiedMorphism C s d -> ReifiedMorphism C s d')
          with
            | ReifiedIdentityMorphism _ _ _ => fun _ m2' => m2'
            | m1' => fun _ m2' => match m2'
                                        in (ReifiedMorphism C s d)
                                        return (forall d',
                                                  ReifiedMorphism C d d' -> ReifiedMorphism C s d')
                                  with
                                    | ReifiedIdentityMorphism _ _ _ => fun _ m1'' => m1''
                                    | m2'' => fun _ m1'' => ReifiedComposedMorphism m1'' m2''
                                  end _ m1'
          end _ (ReifiedMorphismSimplify m2)
        | ReifiedFunctorMorphism objB B objC0 C0 F s0 d0 m0 =>
          match
            ReifiedMorphismSimplify m0
            in (ReifiedMorphism C1 o o0)
            return
            (forall F0 : SpecializedFunctor C1 C0,
               ReifiedMorphism C0 (F0 o) (F0 o0))
          with
            | ReifiedIdentityMorphism _ _ x =>
              fun F0 => ReifiedIdentityMorphism _ (F0 x)
            | ReifiedComposedMorphism _ _ _ _ _ m11 m12 =>
              fun F0 =>
                ReifiedComposedMorphism (ReifiedFunctorMorphism F0 m11)
                                        (ReifiedFunctorMorphism F0 m12)
            | m' =>
              fun F0 =>
                ReifiedFunctorMorphism F0 m'
          end F
        | m' => m'
  end.

  Fixpoint ReifiedMorphismDenote objC C s d (m : @ReifiedMorphism objC C s d) : Morphism C s d :=
    match m in @ReifiedMorphism objC C s d return Morphism C s d with
      | ReifiedIdentityMorphism _ _ x => Identity x
      | ReifiedComposedMorphism _ _ _ _ _ m1 m2 => Compose (@ReifiedMorphismDenote _ _ _ _ m1)
                                                           (@ReifiedMorphismDenote _ _ _ _ m2)
      | ReifiedNaturalTransformationMorphism _ _ _ _ _ _ T x => T x
      | ReifiedFunctorMorphism _ _ _ _ F _ _ m => MorphismOf F (@ReifiedMorphismDenote _ _ _ _ m)
      | ReifiedGenericMorphism _ _ _ _ m => m
    end.

  Local Ltac ok_fin_t :=
    simpl;
    repeat rewrite Associativity;
    repeat rewrite FCompositionOf;
    autorewrite with category;
    try reflexivity.

  Lemma ReifiedMorphismSimplifyOk objC C s d (m : @ReifiedMorphism objC C s d)
  : ReifiedMorphismDenote m =
    ReifiedMorphismDenote (ReifiedMorphismSimplify m).
    induction m;
    repeat match goal with
             | _ => progress ok_fin_t
             | [ IH : ReifiedMorphismDenote _ = _ |- _ ] => rewrite IH; clear IH
             | [ |- context[ReifiedMorphismSimplify ?m] ] =>
               let H := fresh in
               set (H := ReifiedMorphismSimplify m);
                 clearbody H;
                 destruct H
             | [ |- context[match ReifiedMorphismSimplify ?m with _ => _ end _ ?m'] ] =>
                
               let H := fresh in
               set (H := ReifiedMorphismSimplify m);
                 clearbody H;
                 match type of H with
                   | ReifiedMorphism _ ?A ?B =>
                     let FH := fresh in
                     let H2 := fresh in
                      
                     set (FH := m');
                       let FH' := (eval simpl in (ReifiedMorphismDenote FH)) in
                        
                       assert (H2 : ReifiedMorphismDenote FH = FH') by reflexivity;
                          
                         rewrite <- H2;
                         clear H2;
                         clearbody FH;
                         simpl in *;
                         set (A' := A) in *;
                         set (B' := B) in *;
                         clearbody A' B';
                         destruct H
                 end
           end.
  Qed.

  Section single_category.
    Context `{C : SpecializedCategory objC}.

     

    Structure TaggedMorphism s d := Tag { untag :> Morphism C s d }.

    Structure SimplifiedMorphism s d :=
      ReifyMorphism
        {
          morphism_of : TaggedMorphism s d;
          reified_morphism_of : ReifiedMorphism C s d;
          reified_morphism_ok : untag morphism_of = ReifiedMorphismDenote reified_morphism_of
        }.
    Global Arguments ReifyMorphism [s d] morphism_of _ _.

     

    Lemma rsimplify_morphisms `(r : SimplifiedMorphism s d)
    : untag (morphism_of r) = ReifiedMorphismDenote (ReifiedMorphismSimplify (reified_morphism_of r)).
      rewrite <- ReifiedMorphismSimplifyOk.
      destruct r; assumption.
    Qed.

     


    Definition generic_tag {s d} := Tag s d.
    Definition compose_tag {s d} := @generic_tag s d.
    Definition functor_tag {s d} := @compose_tag s d.
    Definition nt_tag {s d} := @functor_tag s d.
    Canonical Structure identity_tag {s d} m := @nt_tag s d m.
  End single_category.

   
   

  Local Ltac t := simpl;
                 repeat rewrite <- reified_morphism_ok;
                 reflexivity.

  Section more_single_category.
    Context `{C : SpecializedCategory objC}.

    Lemma reifyIdentity x : Identity x = ReifiedMorphismDenote (ReifiedIdentityMorphism C x).
reflexivity.
Qed.
    Canonical Structure reify_identity_morphism x := ReifyMorphism (identity_tag _) _ (reifyIdentity x).

    Lemma reifyCompose s d d'
          `(m1' : @SimplifiedMorphism objC C d d') `(m2' : @SimplifiedMorphism objC C s d)
    : Compose (untag (morphism_of m1')) (untag (morphism_of m2'))
      = ReifiedMorphismDenote (ReifiedComposedMorphism (reified_morphism_of m1') (reified_morphism_of m2')).
      t.
    Qed.
    Canonical Structure reify_composition_morphism s d d' m1' m2' := ReifyMorphism (compose_tag _) _ (@reifyCompose s d d' m1' m2').
  End more_single_category.

  Section functor.
    Context `{C : SpecializedCategory objC}.
    Context `{D : SpecializedCategory objD}.
    Variable F : SpecializedFunctor C D.

    Lemma reifyFunctor `(m' : @SimplifiedMorphism objC C s d)
    : MorphismOf F (untag (morphism_of m')) = ReifiedMorphismDenote (ReifiedFunctorMorphism F (reified_morphism_of m')).
      t.
    Qed.
    Canonical Structure reify_functor_morphism s d m' := ReifyMorphism (functor_tag _) _ (@reifyFunctor s d m').
  End functor.

  Section natural_transformation.
    Context `{C : SpecializedCategory objC}.
    Context `{D : SpecializedCategory objD}.
    Variables F G : SpecializedFunctor C D.
    Variable T : SpecializedNaturalTransformation F G.

    Lemma reifyNT (x : C) : T x = ReifiedMorphismDenote (ReifiedNaturalTransformationMorphism T x).
reflexivity.
Qed.
    Canonical Structure reify_nt_morphism x := ReifyMorphism (nt_tag _) _ (@reifyNT x).
  End natural_transformation.
  Section generic.
    Context `{C : SpecializedCategory objC}.

    Lemma reifyGeneric s d (m : Morphism C s d) : m = ReifiedMorphismDenote (ReifiedGenericMorphism C s d m).
reflexivity.
Qed.
    Canonical Structure reify_generic_morphism s d m := ReifyMorphism (generic_tag m) _ (@reifyGeneric s d m).
  End generic.

End SimplifiedMorphism.

Ltac rsimplify_morphisms :=
  simpl;
   
  etransitivity; [ refine (rsimplify_morphisms _) | ];
  etransitivity; [ | symmetry; refine (rsimplify_morphisms _) ];
  instantiate;
  simpl.

 
 
Section bad_examples.
  Context `(C0 : SpecializedCategory objC0).
  Context `(C1 : SpecializedCategory objC1).
  Context `(D : SpecializedCategory objD).

  Variables s d d' : C0.
  Variable m1 : Morphism C0 s d.
  Variable m2 : Morphism C0 d d'.
  Variable F : SpecializedFunctor (C0 + C1) D.

  Goal MorphismOf F (s := inl _) (d := inl _) (Compose m2 m1) = Compose (MorphismOf F (s := inl _) (d := inl _) m2) (MorphismOf F (s := inl _) (d := inl _) m1).
  simpl in *.
  etransitivity; [ refine (rsimplify_morphisms _) | ].
  Abort.
End bad_examples.


Set Implicit Arguments.

Generalizable All Variables.

Set Universe Polymorphism.

Section FunctorCategory.
  Context `(C : @SpecializedCategory objC).
  Context `(D : @SpecializedCategory objD).

   
  Definition FunctorCategory : @SpecializedCategory (SpecializedFunctor C D).
    refine (@Build_SpecializedCategory _
                                       (SpecializedNaturalTransformation (C := C) (D := D))
                                       (IdentityNaturalTransformation (C := C) (D := D))
                                       (NTComposeT (C := C) (D := D))
                                       _
                                       _
                                       _);
    abstract (nt_eq; auto with morphism).
  Defined.
End FunctorCategory.

Notation "C ^ D" := (FunctorCategory D C) : category_scope.


Set Implicit Arguments.

Generalizable All Variables.

Set Universe Polymorphism.

Section SimplifiedMorphism'.
  Section single_category_definition.
    Context `{C : SpecializedCategory objC}.

    Class > MorphismSimplifiesTo {s d} (m_orig m_simpl : Morphism C s d) :=
      simplified_morphism_ok :> m_orig = m_simpl.
  End single_category_definition.

  Local Ltac t :=
    hnf in *; subst;
    repeat rewrite <- FCompositionOf;
    repeat match goal with
             | [ H : _ |- _ ] => rewrite H
           end;
    repeat rewrite FIdentityOf;
    autorewrite with category;
    auto with category;
    trivial.

  Section single_category_instances.
    Context `{C : SpecializedCategory objC}.

    Global Instance LeftIdentitySimplify
           `(@MorphismSimplifiesTo _ C s d m1_orig m1_simpl)
           `(@MorphismSimplifiesTo _ C _ _ m2_orig (Identity _))
    : MorphismSimplifiesTo (Compose m2_orig m1_orig) m1_simpl | 10.
    t.
    Qed.

    Global Instance RightIdentitySimplify
           `(@MorphismSimplifiesTo _ C s d m1_orig m1_simpl)
           `(@MorphismSimplifiesTo _ C _ _ m2_orig (Identity _))
    : MorphismSimplifiesTo (Compose m1_orig m2_orig) m1_simpl | 10.
    t.
    Qed.

    Global Instance ComposeToIdentitySimplify
           `(@MorphismSimplifiesTo _ C s d m1_orig m1_simpl)
           `(@MorphismSimplifiesTo _ C d s m2_orig m2_simpl)
           `(Compose m2_simpl m1_simpl = Identity _)
    : MorphismSimplifiesTo (Compose m2_orig m1_orig) (Identity _) | 20.
    t.
    Qed.

    Global Instance AssociativitySimplify `(@MorphismSimplifiesTo _ C _ _ (@Compose _ C _ c d m3 (@Compose _ C a b c m2 m1)) m_simpl)
    : MorphismSimplifiesTo (Compose (Compose m3 m2) m1) m_simpl | 1000.
    t.
    Qed.

    Global Instance ComposeSimplify
           `(@MorphismSimplifiesTo _ C s d m1_orig m1_simpl)
           `(@MorphismSimplifiesTo _ C d d' m2_orig m2_simpl)
    : MorphismSimplifiesTo (Compose m2_orig m1_orig) (Compose m2_simpl m1_simpl) | 5000.
    t.
    Qed.

    Global Instance NoSimplify {s d} (m : Morphism C s d)
    : MorphismSimplifiesTo m m | 10000
      := eq_refl.
  End single_category_instances.

  Section sum_prod_category_instances.
    Context `{C : SpecializedCategory objC}.
    Context `{D : SpecializedCategory objD}.

    Global Instance SumCategorySimplify_inl
           `(@MorphismSimplifiesTo _ C s d m_orig m_simpl)
    : @MorphismSimplifiesTo _ (C + D) (inl s) (inl d) m_orig m_simpl | 100.
    t.
    Qed.

    Global Instance SumCategorySimplify_inr
           `(@MorphismSimplifiesTo _ D s d m_orig m_simpl)
    : @MorphismSimplifiesTo _ (C + D) (inr s) (inr d) m_orig m_simpl | 100.
    t.
    Qed.

    Global Instance SumComposeSimplify_inl
           `(@MorphismSimplifiesTo _ C s d m1_orig m1_simpl)
           `(@MorphismSimplifiesTo _ C d d' m2_orig m2_simpl)
    : MorphismSimplifiesTo (@Compose _ (C + D) (inl s) (inl d) (inl d') m2_orig m1_orig)
                           (@Compose _ (C + D) (inl s) (inl d) (inl d') m2_simpl m1_simpl) | 50.
    t.
    Qed.

    Global Instance SumComposeSimplify_inr
           `(@MorphismSimplifiesTo _ D s d m1_orig m1_simpl)
           `(@MorphismSimplifiesTo _ D d d' m2_orig m2_simpl)
    : MorphismSimplifiesTo (@Compose _ (C + D) (inr s) (inr d) (inr d') m2_orig m1_orig)
                           (@Compose _ (C + D) (inr s) (inr d) (inr d') m2_simpl m1_simpl) | 50.
    t.
    Qed.

     
  End sum_prod_category_instances.


  Section functor_instances.
    Context `{C : SpecializedCategory objC}.
    Context `{D : SpecializedCategory objD}.
    Variable F : SpecializedFunctor C D.

    Global Instance FIdentityOfSimplify `(@MorphismSimplifiesTo _ C x x m_orig (Identity _))
    : MorphismSimplifiesTo (MorphismOf F m_orig) (Identity _) | 30.
    t.
    Qed.

    Global Instance FCompositionOfSimplify
           `(@MorphismSimplifiesTo _ C s d m1_orig m1_simpl)
           `(@MorphismSimplifiesTo _ C d d' m2_orig m2_simpl)
           `(@MorphismSimplifiesTo _ _ _ _ (Compose m2_simpl m1_simpl) m_comp)
           `(@MorphismSimplifiesTo _ _ _ _ (MorphismOf F m_comp) m_Fcomp)
    : MorphismSimplifiesTo (Compose (MorphismOf F m2_orig) (MorphismOf F m1_orig))
                           m_Fcomp | 30.
    t.
    Qed.

     
    Global Instance FunctorComposeToIdentitySimplify
           `(@MorphismSimplifiesTo _ D (F s) (F d) m1_orig (MorphismOf F m1_simpl))
           `(@MorphismSimplifiesTo _ D (F d) (F s) m2_orig (MorphismOf F m2_simpl))
           `(Compose m2_simpl m1_simpl = Identity _)
    : MorphismSimplifiesTo (Compose m2_orig m1_orig) (Identity _) | 20.
    t.
    Qed.

    Global Instance FunctorNoSimplify
           `(@MorphismSimplifiesTo _ C s d m_orig m_simpl)
    : MorphismSimplifiesTo (MorphismOf F m_orig) (MorphismOf F m_simpl) | 5000.
    t.
    Qed.
  End functor_instances.
End SimplifiedMorphism'.

Hint Extern 0 (_ = _) => eassumption : typeclass_instances.

Ltac rsimplify_morphisms' :=
  unfold Object in *;
  simpl in *;
  match goal with
    | [ |- @eq (Morphism _ _ _) ?A ?B ] =>
      progress (
          try erewrite (simplified_morphism_ok (m_orig := A));
          try erewrite (simplified_morphism_ok (m_orig := B));
          []
        )
    | [ |- context[?m] ] =>
          match type of m with
            | Morphism _ _ _ => progress (erewrite (simplified_morphism_ok (m_orig := m)); [])
          end
    | _ => erewrite simplified_morphism_ok; []
  end;
  simpl.


 
 
 
Section bad1.
  Context `(C : SpecializedCategory objC).
  Context `(D : SpecializedCategory objD).
  Context `(E : SpecializedCategory objE).
  Variable s : SpecializedFunctor D E.
  Variable s8 : SpecializedFunctor C D.
  Variable s6 : SpecializedFunctor D E.
  Variable s7 : SpecializedFunctor C D.
  Variable s4 : SpecializedFunctor D E.
  Variable s5 : SpecializedFunctor C D.
  Variable s2 : SpecializedNaturalTransformation s s6.
  Variable s3 : SpecializedNaturalTransformation s8 s7.
  Variable s0 : SpecializedNaturalTransformation s6 s4.
  Variable s1 : SpecializedNaturalTransformation s7 s5.
  Variable x : objC.

  Goal
    (Compose (MorphismOf s4 (Compose (s1 x) (s3 x)))
             (Compose (s0 (s8 x)) (s2 (s8 x)))) =
  (Compose (MorphismOf s4 (s1 x))
           (Compose (s0 (s7 x)) (Compose (MorphismOf s6 (s3 x)) (s2 (s8 x))))).
  Fail (rsimplify_morphisms; reflexivity).
  repeat erewrite @FCompositionOf by typeclasses eauto;
    repeat try_associativity ltac:(repeat rewrite Commutes;
                                   ((apply f_equal2; reflexivity)
                                      || (apply f_equal2; try reflexivity; [])));
    reflexivity.
  Qed.
End bad1.


Section bad2.
  Context `(C : SpecializedCategory objC).
  Context `(D : SpecializedCategory objD).
  Variable F : SpecializedFunctor C D.
  Variable o1 : objC.
  Variable o2 : objC.
  Variable o : objC.
  Variable o0 : objC.
  Variable m : Morphism C o o1.
  Variable m0 : Morphism C o2 o0.
  Variable x : Morphism C o1 o2.
  Goal MorphismOf F (Compose m0 (Compose x m)) =
  Compose (MorphismOf F m0) (Compose (MorphismOf F x) (MorphismOf F m)).
  Fail (rsimplify_morphisms; reflexivity).
  rsimplify_morphisms; rsimplify_morphisms; reflexivity.
  Qed.
End bad2.


Set Implicit Arguments.

Generalizable All Variables.

Set Universe Polymorphism.

Section FunctorProduct.
  Context `(C : @SpecializedCategory objC).
  Context `(D : @SpecializedCategory objD).
  Context `(D' : @SpecializedCategory objD').

  Definition FunctorProduct (F : Functor C D) (F' : Functor C D') : SpecializedFunctor C (D * D').
    match goal with
      | [ |- SpecializedFunctor ?C0 ?D0 ] =>
        refine (Build_SpecializedFunctor
                  C0 D0
                  (fun c => (F c, F' c))
                  (fun s d m => (MorphismOf F m, MorphismOf F' m))
                  _
                  _)
    end;
    abstract (intros; expand; apply f_equal2; rsimplify_morphisms; reflexivity).
  Defined.

  Definition FunctorProductFunctorial
             (F G : Functor C D)
             (F' G' : Functor C D')
             (T : SpecializedNaturalTransformation F G)
             (T' : SpecializedNaturalTransformation F' G')
  : SpecializedNaturalTransformation (FunctorProduct F F') (FunctorProduct G G').
    match goal with
      | [ |- SpecializedNaturalTransformation ?F ?G ] =>
        refine (Build_SpecializedNaturalTransformation F G
                                                       (fun x => (T x, T' x))
                                                       _)
    end.
    abstract (simpl; intros; repeat rewrite Commutes; reflexivity).
  Defined.
End FunctorProduct.

Section FunctorProduct'.
  Context `(C : @SpecializedCategory objC).
  Context `(D : @SpecializedCategory objD).
  Context `(C' : @SpecializedCategory objC').
  Context `(D' : @SpecializedCategory objD').
  Variable F : Functor C D.
  Variable F' : Functor C' D'.

  Definition FunctorProduct' : SpecializedFunctor  (C * C') (D * D')
    := FunctorProduct (ComposeFunctors F fst_Functor) (ComposeFunctors F' snd_Functor).
End FunctorProduct'.

 
Infix "*" := FunctorProduct' : functor_scope.


Set Implicit Arguments.

Generalizable All Variables.

Set Universe Polymorphism.

Section FunctorialComposition.
  Context `(C : SpecializedCategory objC).
  Context `(D : SpecializedCategory objD).
  Context `(E : SpecializedCategory objE).

  Definition FunctorialComposition : SpecializedFunctor ((E ^ D) * (D ^ C)) (E ^ C).
  Proof.
    match goal with
      | [ |- SpecializedFunctor ?C ?D ] =>
        refine (Build_SpecializedFunctor C D
          (fun fg => ComposeFunctors (fst fg) (snd fg))
          (fun _ _ tu => NTComposeF (fst tu) (snd tu))
          _
          _
        )
    end;
    abstract (
      intros;
        destruct_hypotheses;
        auto with category;
          nt_eq;
          repeat rewrite FIdentityOf;
            auto with category
    ).
  Defined.
End FunctorialComposition.


Fixpoint CardinalityRepresentative (n : nat) : Set :=
  match n with
    | O => Empty_set
    | 1 => unit
    | S n' => (CardinalityRepresentative n' + unit)%type
  end.

Coercion CardinalityRepresentative : nat >-> Sortclass.

Definition NatCategory (n : nat) := Eval unfold DiscreteCategory, DiscreteCategory_Identity in DiscreteCategory n.

Coercion NatCategory : nat >-> SpecializedCategory.


Set Implicit Arguments.

Generalizable All Variables.

Set Universe Polymorphism.

Section InitialTerminal.
   Definition InitialCategory : SmallSpecializedCategory _ := 0.
   Definition TerminalCategory : SmallSpecializedCategory _ := 1.
End InitialTerminal.

Section Functors.
  Context `(C : SpecializedCategory objC).

  Definition FunctorTo1 : SpecializedFunctor C 1
    := Build_SpecializedFunctor C 1 (fun _ => tt) (fun _ _ _ => eq_refl) (fun _ _ _ _ _ => eq_refl) (fun _ => eq_refl).
  Definition FunctorToTerminal : SpecializedFunctor C TerminalCategory := FunctorTo1.

  Definition FunctorFrom1 (c : C) : SpecializedFunctor 1 C
    := Build_SpecializedFunctor 1 C (fun _ => c) (fun _ _ _ => Identity c) (fun _ _ _ _ _ => eq_sym (@RightIdentity _ _ _ _ _ _)) (fun _ => eq_refl).
  Definition FunctorFromTerminal (c : C) : SpecializedFunctor TerminalCategory C := FunctorFrom1 c.

  Definition FunctorFrom0 : SpecializedFunctor 0 C
    := Build_SpecializedFunctor 0 C (fun x => match x with end) (fun x _ _ => match x with end) (fun x _ _ _ _ => match x with end) (fun x => match x with end).
  Definition FunctorFromInitial : SpecializedFunctor InitialCategory C := FunctorFrom0.
End Functors.

Section FunctorsUnique.
  Context `(C : @SpecializedCategory objC).

  Lemma InitialCategoryFunctorUnique
  : forall F F' : SpecializedFunctor InitialCategory C,
      F = F'.
  Proof.
    functor_eq; destruct_head_hnf @Empty_set.
  Qed.

  Lemma InitialCategoryFunctor'Unique
  : forall F F' : SpecializedFunctor C InitialCategory,
      F = F'.
  Proof.
    intros F F'.
    functor_eq; auto.
    match goal with
      | [ x : _ |- _ ] => solve [ let H := fresh in assert (H := F x); destruct H ]
    end.
  Qed.

  Lemma InitialCategoryInitial
  : forall F, F = FunctorFromInitial C.
  Proof.
    intros; apply InitialCategoryFunctorUnique.
  Qed.

  Lemma TerminalCategoryFunctorUnique
  : forall F F' : SpecializedFunctor C TerminalCategory,
      F = F'.
  Proof.
    functor_eq; auto.
  Qed.

  Lemma TerminalCategoryTerminal
  : forall F, F = FunctorToTerminal C.
  Proof.
    intros; apply TerminalCategoryFunctorUnique.
  Qed.
End FunctorsUnique.


Set Implicit Arguments.

Generalizable All Variables.

Set Universe Polymorphism.

Local Ltac t_prod :=
  intros; simpl; repeat (rewrite <- FCompositionOf || rewrite <- FIdentityOf);
  apply f_equal; expand; autorewrite with morphism;
  reflexivity.

Section ProductInducedFunctors.
  Context `(C : @SpecializedCategory objC).
  Context `(D : @SpecializedCategory objD).
  Context `(E : @SpecializedCategory objE).

  Variable F : SpecializedFunctor (C * D) E.

  Definition InducedProductFstFunctor (d : D) : SpecializedFunctor C E.
    refine {| ObjectOf := (fun c => F (c, d));
      MorphismOf := (fun _ _ m => MorphismOf F (s := (_, d)) (d := (_, d)) (m, Identity d))
    |};
    abstract t_prod.
  Defined.

  Definition InducedProductSndFunctor (c : C) : SpecializedFunctor D E.
    refine {| ObjectOf := (fun d => F (c, d));
      MorphismOf := (fun _ _ m => MorphismOf F (s := (c, _)) (d := (c, _)) (Identity c, m))
    |};
    abstract t_prod.
  Defined.
End ProductInducedFunctors.

Notation "F ⟨ c , - ⟩" := (InducedProductSndFunctor F c) : functor_scope.
Notation "F ⟨ - , d ⟩" := (InducedProductFstFunctor F d) : functor_scope.

Section ProductInducedNaturalTransformations.
  Context `(C : @SpecializedCategory objC).
  Context `(D : @SpecializedCategory objD).
  Context `(E : @SpecializedCategory objE).

  Variable F : SpecializedFunctor (C * D) E.

  Definition InducedProductFstNaturalTransformation {s d} (m : Morphism C s d) : SpecializedNaturalTransformation (F ⟨ s, - ⟩) (F ⟨ d, - ⟩).
    match goal with
      | [ |- SpecializedNaturalTransformation ?F0 ?G0 ] =>
        refine (Build_SpecializedNaturalTransformation F0 G0
          (fun d => MorphismOf F (s := (_, d)) (d := (_, d)) (m, Identity (C := D) d))
          _
        )
    end;
    abstract t_prod.
  Defined.

  Definition InducedProductSndNaturalTransformation {s d} (m : Morphism D s d) : SpecializedNaturalTransformation (F ⟨ -, s ⟩) (F ⟨ - , d ⟩).
    match goal with
      | [ |- SpecializedNaturalTransformation ?F0 ?G0 ] =>
        refine (Build_SpecializedNaturalTransformation F0 G0
          (fun c => MorphismOf F (s := (c, _)) (d := (c, _)) (Identity (C := C) c, m))
          _
        )
    end;
    abstract t_prod.
  Defined.
End ProductInducedNaturalTransformations.

Notation "F ⟨ f , - ⟩" := (InducedProductSndNaturalTransformation F f) : natural_transformation_scope.
Notation "F ⟨ - , f ⟩" := (InducedProductFstNaturalTransformation F f) : natural_transformation_scope.


Set Implicit Arguments.

Generalizable All Variables.

Set Universe Polymorphism.

Section SumCategoryFunctors'.
  Section sum_functor.
    Context `(C : @SpecializedCategory objC).
    Context `(C' : @SpecializedCategory objC').
    Context `(D : @SpecializedCategory objD).

    Definition sum_Functor (F : SpecializedFunctor C D) (F' : SpecializedFunctor C' D)
    : SpecializedFunctor (C + C') D.
      match goal with
        | [ |- SpecializedFunctor ?C ?D ] =>
          refine (Build_SpecializedFunctor C D
                                           (fun cc' => match cc' with
                                                         | inl c => F c
                                                         | inr c' => F' c'
                                                       end)
                                           (fun s d => match s, d with
                                                         | inl cs, inl cd => MorphismOf F (s := cs) (d := cd)
                                                         | inr c's, inr c'd => MorphismOf F' (s := c's) (d := c'd)
                                                         | _, _ => fun m => match m with end
                                                       end)
                                           _
                                           _)
      end;
      abstract (
          repeat intros [?|?];
          intros;
          simpl in *;
            destruct_head_hnf Empty_set;
          repeat rewrite FIdentityOf;
          repeat rewrite FCompositionOf;
          reflexivity
        ).
    Defined.

    Definition sum_Functor_Functorial (F G : SpecializedFunctor C D) (F' G' : SpecializedFunctor C' D)
               (T : SpecializedNaturalTransformation F G)
               (T' : SpecializedNaturalTransformation F' G')
    : SpecializedNaturalTransformation (sum_Functor F F') (sum_Functor G G').
      match goal with
        | [ |- SpecializedNaturalTransformation ?A ?B ] =>
          refine (Build_SpecializedNaturalTransformation
                    A B
                    (fun x => match x with
                                | inl c => T c
                                | inr c' => T' c'
                              end)
                    _)
      end;
      abstract (
          repeat intros [?|?]; simpl; intros; destruct_head_hnf Empty_set; apply Commutes
        ).
    Defined.
  End sum_functor.

  Section swap_functor.
    Definition sum_swap_Functor
               `(C : @SpecializedCategory objC)
               `(D : @SpecializedCategory objD)
    : SpecializedFunctor (C + D) (D + C)
      := sum_Functor (inr_Functor _ _) (inl_Functor _ _).

    Lemma sum_swap_swap_id
          `(C : @SpecializedCategory objC)
          `(D : @SpecializedCategory objD)
    : ComposeFunctors (sum_swap_Functor C D) (sum_swap_Functor D C) = IdentityFunctor _.
      apply Functor_eq; repeat intros [?|?]; simpl; trivial.
    Qed.
  End swap_functor.
End SumCategoryFunctors'.

Notation "F + G" := (sum_Functor F G) : functor_scope.
Notation "T + U" := (sum_Functor_Functorial T U) : natural_transformation_scope.


Set Implicit Arguments.

Generalizable All Variables.

Set Universe Polymorphism.

Local Hint Immediate
      TerminalCategoryFunctorUnique InitialCategoryFunctorUnique
      InitialCategoryFunctor'Unique.

Section Law0.
  Context `(C : @SpecializedCategory objC).

  Definition ExponentialLaw0Functor : SpecializedFunctor (C ^ 0) 1
    := FunctorTo1 _.
  Definition ExponentialLaw0Functor_Inverse : SpecializedFunctor 1 (C ^ 0)
    := FunctorFrom1 _ (FunctorFrom0 _).

  Lemma ExponentialLaw0
  : ComposeFunctors ExponentialLaw0Functor ExponentialLaw0Functor_Inverse
    = IdentityFunctor _
    /\ ComposeFunctors ExponentialLaw0Functor_Inverse ExponentialLaw0Functor
       = IdentityFunctor _.
  Proof.
    split; auto.
    apply Functor_eq; auto.
    nt_eq; auto;
    destruct_head_hnf Empty_set.
  Qed.
End Law0.

Section Law0'.
  Context `(C : @SpecializedCategory objC).
  Variable c : objC.

  Definition ExponentialLaw0'Functor : SpecializedFunctor (0 ^ C) 0
    := Build_SpecializedFunctor (0 ^ C) 0
                                (fun F => F c)
                                (fun s d m => match (s c) with end)
                                (fun x _ _ _ _ => match (x c) with end)
                                (fun x => match (x c) with end).

  Definition ExponentialLaw0'Functor_Inverse : SpecializedFunctor 0 (0 ^ C)
    := FunctorFrom0 _.

  Lemma ExponentialLaw0'
  : ComposeFunctors ExponentialLaw0'Functor ExponentialLaw0'Functor_Inverse
    = IdentityFunctor _
    /\
    ComposeFunctors ExponentialLaw0'Functor_Inverse ExponentialLaw0'Functor
    = IdentityFunctor _.
  Proof.
    split; auto;
    apply Functor_eq; simpl; intros; expand; auto.
    match goal with
        [ |- context[match ?E with end] ] => solve [ case E ]
    end.
  Qed.
End Law0'.

Section Law1.
  Context `(C : @SpecializedCategory objC).

  Definition ExponentialLaw1Functor : SpecializedFunctor (C ^ 1) C
    := Build_SpecializedFunctor (C ^ 1) C
                                (fun F => F tt)
                                (fun s d m => m tt)
                                (fun _ _ _ _ _ => eq_refl)
                                (fun _ => eq_refl).

  Definition ExponentialLaw1Functor_Inverse_MorphismOf
             s d (m : Morphism C s d)
  : Morphism (C ^ 1)
             (FunctorFrom1 _ s)
             (FunctorFrom1 _ d).
  Proof.
    hnf.
    match goal with
      | [ |- SpecializedNaturalTransformation ?F ?G ] =>
        refine (Build_SpecializedNaturalTransformation F G
                                                       (fun _ => m)
                                                       _
               )
    end;
      simpl;
      abstract (
          intros; autorewrite with morphism;
          reflexivity
        ).
  Defined.

  Global Arguments ExponentialLaw1Functor_Inverse_MorphismOf / _ _ _.

  Definition ExponentialLaw1Functor_Inverse : SpecializedFunctor C (C ^ 1).
  Proof.
    refine (Build_SpecializedFunctor
              C (C ^ 1)
              (@FunctorFrom1 _ _)
              ExponentialLaw1Functor_Inverse_MorphismOf
              _
              _
           );
    abstract nt_eq.
  Defined.

  Lemma ExponentialLaw1
  : ComposeFunctors ExponentialLaw1Functor ExponentialLaw1Functor_Inverse
    = IdentityFunctor _ /\
    ComposeFunctors ExponentialLaw1Functor_Inverse ExponentialLaw1Functor
    = IdentityFunctor _.
  Proof.
    abstract (
        split; repeat (functor_eq || nt_eq);
        destruct_head_hnf @eq;
        destruct_head_hnf unit;
        trivial;
        rewrite FIdentityOf;
        trivial
      ).
  Qed.
End Law1.

Section Law1'.
  Context `(C : @SpecializedCategory objC).

  Definition ExponentialLaw1'Functor : SpecializedFunctor (1 ^ C) 1
    := FunctorTo1 _.

  Definition ExponentialLaw1'Functor_Inverse : SpecializedFunctor 1 (1 ^ C).
  Proof.
    refine (Build_SpecializedFunctor
              1 (1 ^ C)
              (fun _ => FunctorTo1 _)
              (fun s d m => Build_SpecializedNaturalTransformation
                              (FunctorTo1 C) (FunctorTo1 C)
                              (fun _ => Identity (C := 1) tt)
                              (fun _ _ _ => eq_refl))
              _
              _
           );
    abstract nt_eq.
  Defined.

  Lemma ExponentialLaw1'
  : ComposeFunctors ExponentialLaw1'Functor ExponentialLaw1'Functor_Inverse
    = IdentityFunctor _ /\
    ComposeFunctors ExponentialLaw1'Functor_Inverse ExponentialLaw1'Functor
    = IdentityFunctor _.
  Proof.
    split; auto.
    apply Functor_eq; auto.
    nt_eq; auto.
  Qed.
End Law1'.

Section Law2.
  Context `(D : @SpecializedCategory objD).
  Context `(C1 : @SpecializedCategory objC1).
  Context `(C2 : @SpecializedCategory objC2).

  Definition ExponentialLaw2Functor
  : SpecializedFunctor (D ^ (C1 + C2)) ((D ^ C1) * (D ^ C2))
    := FunctorProduct (FunctorialComposition C1 (C1 + C2) D ⟨ - , inl_Functor _ _ ⟩)
                      (FunctorialComposition C2 (C1 + C2) D ⟨ - , inr_Functor _ _ ⟩).

  Definition ExponentialLaw2Functor_Inverse
  : SpecializedFunctor ((D ^ C1) * (D ^ C2)) (D ^ (C1 + C2)).
  Proof.
    match goal with
      | [ |- SpecializedFunctor ?C ?D ] =>
        refine (Build_SpecializedFunctor
                  C D
                  (fun FG => sum_Functor (fst FG) (snd FG))
                  (fun _ _ m => sum_Functor_Functorial (fst m) (snd m))
                  _
                  _)
    end;
    simpl in *;
    abstract (
        nt_eq; intros;
        destruct_head_hnf @prod;
        destruct_head_hnf @sum;
        reflexivity
      ).
  Defined.


  Lemma ExponentialLaw2
  : ComposeFunctors ExponentialLaw2Functor ExponentialLaw2Functor_Inverse
    = IdentityFunctor _ /\
    ComposeFunctors ExponentialLaw2Functor_Inverse ExponentialLaw2Functor
    = IdentityFunctor _.
  Proof.
    abstract (repeat
                match goal with
                  | _ => reflexivity
                  | _ => split
                  | _ => progress (simpl in *; intros; trivial)
                  | _ => progress repeat subst
                  | _ => progress destruct_head_hnf @Empty_set
                  | _ => progress simpl_eq
                  | _ => progress apply Functor_eq
                  | _ => progress nt_eq
                  | _ => progress rsimplify_morphisms'
                  | _ => progress destruct_head_hnf @sum
                  | _ => progress rewrite FIdentityOf
                end).
  Qed.
End Law2.

Section Law3.
  Context `(C1 : @SpecializedCategory objC1).
  Context `(C2 : @SpecializedCategory objC2).
  Context `(D : @SpecializedCategory objD).

  Definition ExponentialLaw3Functor
  : SpecializedFunctor ((C1 * C2) ^ D) (C1 ^ D * C2 ^ D).
    match goal with
      | [ |- SpecializedFunctor ?F ?G ] =>
        refine (Build_SpecializedFunctor
                  F G
                  (fun H => (ComposeFunctors fst_Functor H,
                             ComposeFunctors snd_Functor H))
                  (fun s d m =>
                     (MorphismOf (FunctorialComposition D (C1 * C2) C1)
                                 (s := (_, _))
                                 (d := (_, _))
                                 (Identity fst_Functor, m),
                      MorphismOf (FunctorialComposition D (C1 * C2) C2)
                                 (s := (_, _))
                                 (d := (_, _))
                                 (Identity snd_Functor, m)))
                  _
                  _
               )
    end;
    abstract (
        intros;
        simpl;
        simpl_eq;
        apply NaturalTransformation_eq;
        simpl; intros;
        rsimplify_morphisms;
        reflexivity
      ).
  Defined.

  Definition ExponentialLaw3Functor_Inverse
  : SpecializedFunctor (C1 ^ D * C2 ^ D) ((C1 * C2) ^ D).
    let FG := (match goal with
                   [ |- SpecializedFunctor ?F ?G ] => constr:(F, G)
               end) in
    refine (Build_SpecializedFunctor
              (fst FG) (snd FG)
              (fun H => FunctorProduct
                          (@fst_Functor _ (C1 ^ D) _ (C2 ^ D) H)
                          (@snd_Functor _ (C1 ^ D) _ (C2 ^ D) H))
              (fun _ _ m => FunctorProductFunctorial (fst m) (snd m))
              _
              _);
      abstract (
          simpl; intros;
          simpl_eq;
          nt_eq
        ).
  Defined.


  Lemma ExponentialLaw3
  : ComposeFunctors ExponentialLaw3Functor ExponentialLaw3Functor_Inverse
    = IdentityFunctor _ /\
    ComposeFunctors ExponentialLaw3Functor_Inverse ExponentialLaw3Functor
    = IdentityFunctor _.
  Proof.
    abstract (
        repeat
          match goal with
            | _ => reflexivity
            | _ => split
            | _ => progress (simpl; intros; trivial)
            | _ => progress repeat subst
            | _ => progress JMeq_eq
            | _ => progress simpl_eq
            | _ => progress apply Functor_eq
            | _ => progress apply NaturalTransformation_JMeq
            | _ => rsimplify_morphisms
          end
      ).
  Qed.
End Law3.

Section Law4.
  Context `(C1 : @SpecializedCategory objC1).
  Context `(C2 : @SpecializedCategory objC2).
  Context `(D : @SpecializedCategory objD).

  Section functor.
    Local Ltac do_exponential4 := intros; simpl;
      repeat (simpl;
        match goal with
          | _ => reflexivity
          | _ => rewrite FCompositionOf
          | _ => rewrite FIdentityOf
          | _ => rewrite LeftIdentity
          | _ => rewrite RightIdentity
          | _ => try_associativity ltac:(rewrite Commutes)
          | _ => repeat rewrite Associativity; apply f_equal
          | _ => repeat rewrite <- Associativity; apply f_equal2; try reflexivity; []
        end).

    Definition ExponentialLaw4Functor_ObjectOf : ((D ^ C1) ^ C2)%category -> (D ^ (C1 * C2))%category.
    Proof.
      intro F; hnf in F |- *.
      match goal with
        | [ |- SpecializedFunctor ?C ?D ] =>
          refine (Build_SpecializedFunctor C D
            (fun c1c2 => F (snd c1c2) (fst c1c2))
            (fun s1s2 d1d2 m1m2 => Compose ((F (snd d1d2)).(MorphismOf) (fst m1m2)) ((F.(MorphismOf) (snd m1m2)) (fst s1s2)))
            _
            _
          )
      end;
      abstract do_exponential4.
    Defined.

    Definition ExponentialLaw4Functor_MorphismOf s d (m : Morphism ((D ^ C1) ^ C2) s d) :
      Morphism (D ^ (C1 * C2)) (ExponentialLaw4Functor_ObjectOf s) (ExponentialLaw4Functor_ObjectOf d).
    Proof.
      exists (fun c => (m (snd c)) (fst c));
        abstract (
          do_exponential4;
          match goal with
            | [ |- Compose (ComponentsOf ?T ?x) (ComponentsOf ?U _) = Compose (ComponentsOf ?T' _) (ComponentsOf ?U' _) ] =>
              cut (Compose T U = Compose T' U');
                [ let H := fresh in intro H; simpl in H;
                  exact (f_equal (fun T => ComponentsOf T (fst s0)) H)
                  | rewrite Commutes; reflexivity
                ]
          end
        ).
    Defined.

    Definition ExponentialLaw4Functor : SpecializedFunctor ((D ^ C1) ^ C2) (D ^ (C1 * C2)).
    Proof.
      match goal with
        | [ |- SpecializedFunctor ?C ?D ] =>
          refine (Build_SpecializedFunctor C D
            ExponentialLaw4Functor_ObjectOf
            ExponentialLaw4Functor_MorphismOf
            _
            _
          )
      end;
      abstract nt_eq.
    Defined.
  End functor.

  Section inverse.
    Local Ltac do_exponential4_inverse := intros; simpl;
      repeat (simpl;
        match goal with
          | _ => reflexivity
          | _ => rewrite <- FCompositionOf
          | _ => rewrite FIdentityOf
          | _ => rewrite LeftIdentity
          | _ => rewrite RightIdentity
          | _ => try_associativity ltac:(rewrite Commutes)
          | _ => repeat rewrite Associativity; apply f_equal
          | _ => repeat rewrite <- Associativity; apply f_equal2; try reflexivity; []
        end).


    Section ObjectOf.
      Variable F : SpecializedFunctor (C1 * C2) D.

      Definition ExponentialLaw4Functor_Inverse_ObjectOf_ObjectOf : C2 -> (D ^ C1)%category.
      Proof.
        intro c2.
        hnf.
        match goal with
          | [ |- SpecializedFunctor ?C ?D ] =>
            refine (Build_SpecializedFunctor C D
              (fun c1 => F (c1, c2))
              (fun s1 d1 m1 => F.(MorphismOf) (s := (s1, c2)) (d := (d1, c2)) (m1, Identity c2))
              _
              _
            )
        end;
        abstract do_exponential4_inverse.
      Defined.

      Definition ExponentialLaw4Functor_Inverse_ObjectOf_MorphismOf s d (m : Morphism C2 s d) :
        Morphism (D ^ C1) (ExponentialLaw4Functor_Inverse_ObjectOf_ObjectOf s) (ExponentialLaw4Functor_Inverse_ObjectOf_ObjectOf d).
      Proof.
        exists (fun c => F.(MorphismOf) (s := (c, s)) (d := (c, d)) (Identity c, m));
          abstract do_exponential4_inverse.
      Defined.

      Definition ExponentialLaw4Functor_Inverse_ObjectOf : ((D ^ C1) ^ C2)%category.
      Proof.
        hnf.
        match goal with
          | [ |- SpecializedFunctor ?C ?D ] =>
            refine (Build_SpecializedFunctor C D
              ExponentialLaw4Functor_Inverse_ObjectOf_ObjectOf
              ExponentialLaw4Functor_Inverse_ObjectOf_MorphismOf
              _
              _
            )
        end;
        abstract (nt_eq; do_exponential4_inverse).
      Defined.
    End ObjectOf.

    Section MorphismOf.
      Definition ExponentialLaw4Functor_Inverse_MorphismOf_ComponentsOf s d (m : Morphism (D ^ (C1 * C2)) s d) :
        forall c, Morphism (D ^ C1) ((ExponentialLaw4Functor_Inverse_ObjectOf s) c) ((ExponentialLaw4Functor_Inverse_ObjectOf d) c).
      Proof.
        intro c;
          exists (fun c' => m (c', c));
            abstract do_exponential4_inverse.
      Defined.

      Definition ExponentialLaw4Functor_Inverse_MorphismOf s d (m : Morphism (D ^ (C1 * C2)) s d) :
        Morphism ((D ^ C1) ^ C2) (ExponentialLaw4Functor_Inverse_ObjectOf s) (ExponentialLaw4Functor_Inverse_ObjectOf d).
      Proof.
        exists (ExponentialLaw4Functor_Inverse_MorphismOf_ComponentsOf m);
          abstract (nt_eq; do_exponential4_inverse).
      Defined.
    End MorphismOf.

    Arguments ExponentialLaw4Functor_Inverse_MorphismOf_ComponentsOf / _ _ _ _.

    Definition ExponentialLaw4Functor_Inverse : SpecializedFunctor (D ^ (C1 * C2)) ((D ^ C1) ^ C2).
    Proof.
      match goal with
        | [ |- SpecializedFunctor ?C ?D ] =>
          refine (Build_SpecializedFunctor C D
            ExponentialLaw4Functor_Inverse_ObjectOf
            ExponentialLaw4Functor_Inverse_MorphismOf
            _
            _
          )
      end;
      abstract nt_eq.
    Defined.
  End inverse.

  Lemma ExponentialLaw4
  : ComposeFunctors ExponentialLaw4Functor ExponentialLaw4Functor_Inverse
    = IdentityFunctor _ /\
    ComposeFunctors ExponentialLaw4Functor_Inverse ExponentialLaw4Functor
    = IdentityFunctor _.
  Proof.
    abstract (repeat match goal with
                       | _ => reflexivity
                       | _ => split
                       | _ => progress (simpl; intros; trivial)
                       | _ => progress repeat subst
                       | _ => progress destruct_head_hnf @prod
                       | _ => progress JMeq_eq
                       | _ => progress simpl_eq
                       | _ => progress apply Functor_eq
                       | _ => progress apply NaturalTransformation_JMeq
                       | _ => progress apply f_equal
                       | _ => rewrite <- FCompositionOf
                       | _ => rewrite FIdentityOf
                       | _ => rsimplify_morphisms
                     end).
  Qed.
End Law4.


Set Implicit Arguments.

Generalizable All Variables.

Set Universe Polymorphism.

Local Open Scope category_scope.

Section swap.
  Definition SwapFunctor `(C : @SpecializedCategory objC) `(D : @SpecializedCategory objD)
  : SpecializedFunctor (C * D) (D * C)
    := Build_SpecializedFunctor (C * D) (D * C)
                                (fun cd => (snd cd, fst cd))
                                (fun _ _ m => (snd m, fst m))
                                (fun _ _ _ _ _ => eq_refl)
                                (fun _ => eq_refl).

  Lemma ProductLawSwap `(C : @SpecializedCategory objC) `(D : @SpecializedCategory objD)
  : ComposeFunctors (SwapFunctor C D) (SwapFunctor D C) = IdentityFunctor _.
    functor_eq; intuition.
  Qed.
End swap.

Section Law0_.
  Context `(C : @SpecializedCategory objC).

  Definition ProductLaw0Functor : SpecializedFunctor (C * 0) 0.
    refine (Build_SpecializedFunctor (C * 0) 0
                                     (@snd _ _)
                                     (fun _ _ => @snd _ _)
                                     _
                                     _);
    abstract (
        intros;
        destruct_head_hnf @prod;
        destruct_head Empty_set
      ).
  Defined.

  Definition ProductLaw0Functor_Inverse : SpecializedFunctor 0 (C * 0).
    repeat esplit;
    intros; destruct_head_hnf Empty_set.
    Grab Existential Variables.
    intros; destruct_head_hnf Empty_set.
    intros; destruct_head_hnf Empty_set.
  Defined.

  Lemma ProductLaw0 : ComposeFunctors ProductLaw0Functor ProductLaw0Functor_Inverse = IdentityFunctor _ /\
    ComposeFunctors ProductLaw0Functor_Inverse ProductLaw0Functor = IdentityFunctor _.
  Proof.
    split; functor_eq;
    destruct_head_hnf @prod;
    destruct_head_hnf Empty_set.
  Qed.
End Law0_.

Section Law0'_.
  Context `(C : @SpecializedCategory objC).

  Let ProductLaw0'Functor' : SpecializedFunctor (0 * C) 0.
    functor_simpl_abstract_trailing_props (ComposeFunctors (ProductLaw0Functor C) (SwapFunctor _ _)).
  Defined.
  Definition ProductLaw0'Functor : SpecializedFunctor (0 * C) 0 := Eval hnf in ProductLaw0'Functor'.

  Let ProductLaw0'Functor_Inverse' : SpecializedFunctor 0 (0 * C).
    functor_simpl_abstract_trailing_props (ComposeFunctors (SwapFunctor _ _) (ProductLaw0Functor_Inverse C)).
  Defined.
  Definition ProductLaw0'Functor_Inverse : SpecializedFunctor 0 (0 * C) := Eval hnf in ProductLaw0'Functor_Inverse'.

  Lemma ProductLaw0' : ComposeFunctors ProductLaw0'Functor ProductLaw0'Functor_Inverse = IdentityFunctor _ /\
    ComposeFunctors ProductLaw0'Functor_Inverse ProductLaw0'Functor = IdentityFunctor _.
  Proof.
    split; functor_eq;
    destruct_head_hnf @prod;
    destruct_head_hnf Empty_set.
  Qed.
End Law0'_.

Section Law1_.
  Context `(C : @SpecializedCategory objC).

  Let ProductLaw1Functor' : SpecializedFunctor (C * 1) C.
    functor_simpl_abstract_trailing_props (fst_Functor (C := C) (D := 1)).
  Defined.
  Definition ProductLaw1Functor : SpecializedFunctor (C * 1) C
    := Eval hnf in ProductLaw1Functor'.

  Definition ProductLaw1Functor_Inverse : SpecializedFunctor C (C * 1).
    refine (Build_SpecializedFunctor C (C * 1)
                                     (fun c => (c, tt))
                                     (fun s d m => (m, eq_refl))
                                     _
                                     _);
    abstract (
        intros; simpl in *; simpl_eq; reflexivity
      ).
  Defined.

  Lemma ProductLaw1 : ComposeFunctors ProductLaw1Functor ProductLaw1Functor_Inverse = IdentityFunctor _ /\
    ComposeFunctors ProductLaw1Functor_Inverse ProductLaw1Functor = IdentityFunctor _.
  Proof.
    split; functor_eq;
    destruct_head_hnf @prod;
    destruct_head_hnf @eq;
    destruct_head_hnf unit;
    reflexivity.
  Qed.
End Law1_.

Section Law1'_.
  Context `(C : @SpecializedCategory objC).

  Definition ProductLaw1'Functor' : SpecializedFunctor (1 * C) C.
    functor_simpl_abstract_trailing_props (ComposeFunctors (ProductLaw1Functor C) (SwapFunctor _ _)).
  Defined.
  Definition ProductLaw1'Functor : SpecializedFunctor (1 * C) C := Eval hnf in ProductLaw1'Functor'.

  Let ProductLaw1'Functor_Inverse' : SpecializedFunctor C (1 * C).
    functor_simpl_abstract_trailing_props (ComposeFunctors (SwapFunctor _ _) (ProductLaw1Functor_Inverse C)).
  Defined.
  Definition ProductLaw1'Functor_Inverse : SpecializedFunctor C (1 * C) := Eval hnf in ProductLaw1'Functor_Inverse'.

  Lemma ProductLaw1' : ComposeFunctors ProductLaw1'Functor ProductLaw1'Functor_Inverse = IdentityFunctor _ /\
    ComposeFunctors ProductLaw1'Functor_Inverse ProductLaw1'Functor = IdentityFunctor _.
  Proof.
    split; functor_eq;
    destruct_head_hnf @prod;
    destruct_head_hnf @eq;
    destruct_head_hnf unit;
    reflexivity.
  Qed.
End Law1'_.


Set Implicit Arguments.

Set Universe Polymorphism.

Section ComputableCategory.
  Variable I : Type.
  Variable Index2Object : I -> Type.
  Variable Index2Cat : forall i : I, @SpecializedCategory (@Index2Object i).

  Local Coercion Index2Cat : I >-> SpecializedCategory.

  Definition ComputableCategory : @SpecializedCategory I.
    refine (@Build_SpecializedCategory _
                                       (fun C D : I => SpecializedFunctor C D)
                                       (fun o : I => IdentityFunctor o)
                                       (fun C D E : I => ComposeFunctors (C := C) (D := D) (E := E))
                                       _
                                       _
                                       _);
    abstract functor_eq.
  Defined.
End ComputableCategory.


Set Implicit Arguments.

Set Universe Polymorphism.

Section SmallCat.
  Definition SmallCat := ComputableCategory _ SUnderlyingCategory.
  Definition LocallySmallCat := ComputableCategory _ LSUnderlyingCategory.
End SmallCat.

Local Ltac destruct_simple_types :=
  repeat match goal with
           | [ |- context[?T] ] => let T' := type of T in
                                   let T'' := fresh in
                                   match eval hnf in T' with
                                     | unit => set (T'' := T); destruct T''
                                     | _ = _ => set (T'' := T); destruct T''
                                   end
         end.

Section Objects.
  Hint Unfold Morphism Object.

  Local Arguments Object / {obj} C : rename.
  Local Arguments Morphism / {obj} _ _ _ : rename.

  Hint Extern 1 => destruct_simple_types.
  Hint Extern 3 => destruct_to_empty_set.

  Lemma TerminalCategory_Terminal : IsTerminalObject (C := SmallCat) TerminalCategory.
    repeat intro;
    exists (FunctorToTerminal _).
    abstract (
        repeat intro; functor_eq; eauto
      ).
  Defined.

  Lemma InitialCategory_Initial : IsInitialObject (C := SmallCat) InitialCategory.
    repeat intro;
    exists (FunctorFromInitial _).
    abstract (
        repeat intro; functor_eq; eauto
      ).
  Qed.
End Objects.


Set Implicit Arguments.

Generalizable All Variables.

Set Universe Polymorphism.

Local Infix "==" := JMeq.

Local Open Scope category_scope.

Section CommaSpecializedCategory.
   
  Context `(A : @SpecializedCategory objA).
  Context `(B : @SpecializedCategory objB).
  Context `(C : @SpecializedCategory objC).
  Variable S : SpecializedFunctor A C.
  Variable T : SpecializedFunctor B C.

   

   
   
  Record CommaSpecializedCategory_Object := { CommaSpecializedCategory_Object_Member :> { αβ : objA * objB & C.(Morphism) (S (fst αβ)) (T (snd αβ)) } }.

  Let SortPolymorphic_Helper (A T : Type) (Build_T : A -> T) := A.

  Definition CommaSpecializedCategory_ObjectT := Eval hnf in SortPolymorphic_Helper Build_CommaSpecializedCategory_Object.
  Global Identity Coercion CommaSpecializedCategory_Object_Id : CommaSpecializedCategory_ObjectT >-> sigT.
  Definition Build_CommaSpecializedCategory_Object' (mem : CommaSpecializedCategory_ObjectT) := Build_CommaSpecializedCategory_Object mem.
  Global Coercion Build_CommaSpecializedCategory_Object' : CommaSpecializedCategory_ObjectT >-> CommaSpecializedCategory_Object.

  Record CommaSpecializedCategory_Morphism (αβf α'β'f' : CommaSpecializedCategory_ObjectT) := { CommaSpecializedCategory_Morphism_Member :>
    { gh : (A.(Morphism) (fst (projT1 αβf)) (fst (projT1 α'β'f'))) * (B.(Morphism) (snd (projT1 αβf)) (snd (projT1 α'β'f')))  |
      Compose (T.(MorphismOf) (snd gh)) (projT2 αβf) = Compose (projT2 α'β'f') (S.(MorphismOf) (fst gh))
    }
  }.

  Definition CommaSpecializedCategory_MorphismT (αβf α'β'f' : CommaSpecializedCategory_ObjectT) :=
    Eval hnf in SortPolymorphic_Helper (@Build_CommaSpecializedCategory_Morphism αβf α'β'f').
  Global Identity Coercion CommaSpecializedCategory_Morphism_Id : CommaSpecializedCategory_MorphismT >-> sig.
  Definition Build_CommaSpecializedCategory_Morphism' αβf α'β'f' (mem : @CommaSpecializedCategory_MorphismT αβf α'β'f') :=
    @Build_CommaSpecializedCategory_Morphism _ _ mem.
  Global Coercion Build_CommaSpecializedCategory_Morphism' : CommaSpecializedCategory_MorphismT >-> CommaSpecializedCategory_Morphism.

  Lemma CommaSpecializedCategory_Morphism_eq αβf α'β'f' αβf2 α'β'f'2
        (M : CommaSpecializedCategory_Morphism αβf α'β'f')
        (N : CommaSpecializedCategory_Morphism αβf2 α'β'f'2) :
    αβf = αβf2
    -> α'β'f' = α'β'f'2
    -> proj1_sig M == proj1_sig N
    -> M == N.
    clear; intros; subst.
    destruct N as [ [ ] ], M as [ [ ] ]; simpl in *.
    subst.
    apply eq_JMeq.
    f_equal; simpl_eq; reflexivity.
  Qed.

  Global Arguments CommaSpecializedCategory_Object_Member _ : simpl nomatch.
  Global Arguments CommaSpecializedCategory_Morphism_Member _ _ _ : simpl nomatch.

  Definition CommaSpecializedCategory_Compose s d d'
    (gh : CommaSpecializedCategory_MorphismT d d') (g'h' : CommaSpecializedCategory_MorphismT s d) :
    CommaSpecializedCategory_MorphismT s d'.
    exists (Compose (C := A * B) (proj1_sig gh) (proj1_sig g'h')).
    hnf in *; simpl in *.
    abstract (
        destruct_all_hypotheses;
        unfold Morphism in *;
          destruct_hypotheses;
        repeat rewrite FCompositionOf;
        repeat try_associativity ltac:(t_rev_with t')
      ).
  Defined.

  Global Arguments CommaSpecializedCategory_Compose _ _ _ _ _ /.

  Definition CommaSpecializedCategory_Identity o : CommaSpecializedCategory_MorphismT o o.
    exists (Identity (C := A * B) (projT1 o)).
    abstract (
        simpl; autorewrite with category; reflexivity
      ).
  Defined.

  Global Arguments CommaSpecializedCategory_Identity _ /.

  Local Ltac comma_t :=
    repeat (
      let H:= fresh in intro H; destruct H as [ [ ] ]
    );
    destruct_hypotheses;
    simpl in *;
    simpl_eq;
    autorewrite with category;
    f_equal;
    try reflexivity.

  Lemma CommaSpecializedCategory_Associativity : forall o1 o2 o3 o4 (m1 : CommaSpecializedCategory_MorphismT o1 o2) (m2 : CommaSpecializedCategory_MorphismT o2 o3) (m3 : CommaSpecializedCategory_MorphismT o3 o4),
    CommaSpecializedCategory_Compose (CommaSpecializedCategory_Compose m3 m2) m1 =
    CommaSpecializedCategory_Compose m3 (CommaSpecializedCategory_Compose m2 m1).
  Proof.
    abstract (
        simpl_eq;
        repeat rewrite Associativity;
        reflexivity
      ).
  Qed.

  Lemma CommaSpecializedCategory_LeftIdentity : forall a b (f : CommaSpecializedCategory_MorphismT a b),
    CommaSpecializedCategory_Compose (CommaSpecializedCategory_Identity b) f = f.
  Proof.
    abstract comma_t.
  Qed.

  Lemma CommaSpecializedCategory_RightIdentity : forall a b (f : CommaSpecializedCategory_MorphismT a b),
    CommaSpecializedCategory_Compose f (CommaSpecializedCategory_Identity a) = f.
  Proof.
    abstract comma_t.
  Qed.

  Definition CommaSpecializedCategory : @SpecializedCategory CommaSpecializedCategory_Object.
    match goal with
      | [ |- @SpecializedCategory ?obj ] =>
        refine (@Build_SpecializedCategory obj
          CommaSpecializedCategory_Morphism
          CommaSpecializedCategory_Identity
          CommaSpecializedCategory_Compose
          _ _ _
        )
    end;
    abstract (
      intros;
        destruct_type' @CommaSpecializedCategory_Morphism;
        unfold CommaSpecializedCategory_Morphism_Member, Build_CommaSpecializedCategory_Morphism';
          try apply f_equal;
            apply CommaSpecializedCategory_Associativity ||
              apply CommaSpecializedCategory_LeftIdentity ||
                apply CommaSpecializedCategory_RightIdentity
    ).
  Defined.
End CommaSpecializedCategory.

Hint Unfold CommaSpecializedCategory_Compose CommaSpecializedCategory_Identity : category.
Hint Constructors CommaSpecializedCategory_Morphism CommaSpecializedCategory_Object : category.

Local Notation "S ↓ T" := (CommaSpecializedCategory S T).

Section SliceSpecializedCategory.
  Context `(A : @SpecializedCategory objA).
  Context `(C : @SpecializedCategory objC).
  Variable a : C.
  Variable S : SpecializedFunctor A C.
  Let B := TerminalCategory.

  Definition SliceSpecializedCategory_Functor : SpecializedFunctor B C.
    refine {| ObjectOf := (fun _ => a);
      MorphismOf := (fun _ _ _ => Identity a)
    |}; abstract (intros; auto with morphism).
  Defined.

  Definition SliceSpecializedCategory := CommaSpecializedCategory S SliceSpecializedCategory_Functor.
  Definition CosliceSpecializedCategory := CommaSpecializedCategory SliceSpecializedCategory_Functor S.

   
End SliceSpecializedCategory.

Section SliceSpecializedCategoryOver.
  Context `(C : @SpecializedCategory objC).
  Variable a : C.

  Definition SliceSpecializedCategoryOver := SliceSpecializedCategory a (IdentityFunctor C).
  Definition CosliceSpecializedCategoryOver := CosliceSpecializedCategory a (IdentityFunctor C).
End SliceSpecializedCategoryOver.

Section ArrowSpecializedCategory.
  Context `(C : @SpecializedCategory objC).

  Definition ArrowSpecializedCategory := CommaSpecializedCategory (IdentityFunctor C) (IdentityFunctor C).
End ArrowSpecializedCategory.


Set Implicit Arguments.

Generalizable All Variables.

Set Universe Polymorphism.

Local Notation "C / a" := (@SliceSpecializedCategoryOver _ C a) : category_scope.
Local Notation "a \ C" := (@CosliceSpecializedCategoryOver _ C a) (at level 70) : category_scope.

Local Open Scope category_scope.

Local Ltac rewrite_step :=
  (progress repeat rewrite LeftIdentity in * )
    || (progress repeat rewrite RightIdentity in * )
    || (progress repeat rewrite @LeftIdentityFunctor in * )
    || (progress repeat rewrite @RightIdentityFunctor in * )
    || (progress (repeat rewrite Associativity; (reflexivity || apply f_equal)))
    || (progress (repeat rewrite <- Associativity; apply f_equal2; trivial; [])).

Local Ltac quick_step :=
  ((progress repeat subst)
     || (apply sig_eq; simpl)
     || apply f_equal
     || (apply f_equal2; trivial; []));
  trivial.

Local Ltac pre_anihilate :=
  subst_body;
  repeat intro; simpl in *;
  repeat quick_step;
  simpl in *;
  destruct_head_hnf @CommaSpecializedCategory_Morphism;
  destruct_head_hnf @CommaSpecializedCategory_Object;
  destruct_sig;
  subst_body;
  unfold Object in *;
  simpl in *;
  trivial.

Local Ltac slice_step :=
  match goal with
    | _ => apply Functor_eq; simpl; intros; pre_anihilate
    | [ |- @JMeq (sig _) _ (sig _) _ ] => apply sig_JMeq; pre_anihilate
    | [ |- JMeq (?f ?x) (?f ?y) ] =>
      apply (@f_equal1_JMeq _ _ x y f); pre_anihilate
    | [ |- JMeq (?f ?x) (?g ?y) ] =>
      apply (@f_equal_JMeq _ _ _ _ x y f g); pre_anihilate
  end.

Local Ltac step :=
  (quick_step
     || rewrite_step
     || (progress auto 1 with category)
     || slice_step);
  trivial.

Local Ltac anihilate := pre_anihilate; repeat step.

Local Ltac induced_step :=
  reflexivity
    || (try_associativity ltac:(rewrite <- Commutes))
    || (try_associativity ltac:(apply f_equal))
    || (match goal with
          | [ H : _ = _ |- _ = _ ] => try_associativity ltac:(rewrite H)
        end).

Local Ltac induced_anihilate :=
  unfold Object in *;
  simpl in *;
  destruct_head @prod;
  simpl in *;
  pre_anihilate;
  repeat induced_step.

Section CommaCategory.
  Context `(A : @SpecializedCategory objA).
  Context `(B : @SpecializedCategory objB).
  Context `(C : @SpecializedCategory objC).
  Variable S : SpecializedFunctor A C.
  Variable T : SpecializedFunctor B C.

  Let AOp := OppositeCategory A.

  Local Notation "S ↓ T" := (CommaSpecializedCategory S T).

  Definition CommaCategoryProjection : SpecializedFunctor (S ↓ T) (A * B).
    refine (Build_SpecializedFunctor (S ↓ T) (A * B)
      (@projT1 _ _)
      (fun _ _ m => (proj1_sig m))
      _
      _
    ); abstract trivial.
  Defined.
End CommaCategory.

Section SliceCategory.
  Context `(A : @SpecializedCategory objA).

  Local Arguments fst_Functor / .
  Local Arguments snd_Functor / .
  Local Arguments CommaCategoryProjection / .
  Local Arguments SliceSpecializedCategory_Functor / .

  Let ArrowCategoryProjection' : SpecializedFunctor (ArrowSpecializedCategory A) A
    := ComposeFunctors fst_Functor (CommaCategoryProjection _ (IdentityFunctor A)).
  Let ArrowCategoryProjection'' : SpecializedFunctor (ArrowSpecializedCategory A) A.
functor_simpl_abstract_trailing_props ArrowCategoryProjection'.
Defined.
  Definition ArrowCategoryProjection : SpecializedFunctor (ArrowSpecializedCategory A) A := Eval hnf in ArrowCategoryProjection''.

  Let SliceCategoryOverProjection' (a : A) : SpecializedFunctor (A / a) A
    := ComposeFunctors fst_Functor (CommaCategoryProjection (IdentityFunctor A) _).
  Let SliceCategoryOverProjection'' (a : A) : SpecializedFunctor (A / a) A.
functor_simpl_abstract_trailing_props (SliceCategoryOverProjection' a).
Defined.
  Definition SliceCategoryOverProjection (a : A) : SpecializedFunctor (A / a) A := Eval hnf in SliceCategoryOverProjection'' a.

  Let CosliceCategoryOverProjection' (a : A) : SpecializedFunctor (a \ A) A
    := ComposeFunctors snd_Functor (CommaCategoryProjection _ (IdentityFunctor A)).
  Let CosliceCategoryOverProjection'' (a : A) : SpecializedFunctor (a \ A) A.
functor_simpl_abstract_trailing_props (CosliceCategoryOverProjection' a).
Defined.
  Definition CosliceCategoryOverProjection (a : A) : SpecializedFunctor (a \ A) A := Eval hnf in CosliceCategoryOverProjection'' a.

  Section Slice_Coslice.
    Context `(C : @SpecializedCategory objC).
    Variable a : C.
    Variable S : SpecializedFunctor A C.

    Section Slice.
      Local Notation "F ↓ A" := (SliceSpecializedCategory A F).

      Let SliceCategoryProjection' : SpecializedFunctor (S ↓ a) A.
        functor_simpl_abstract_trailing_props (ComposeFunctors fst_Functor (CommaCategoryProjection S (SliceSpecializedCategory_Functor C a))).
      Defined.
      Definition SliceCategoryProjection : SpecializedFunctor (S ↓ a) A := Eval hnf in SliceCategoryProjection'.
    End Slice.

    Section Coslice.
      Local Notation "A ↓ F" := (CosliceSpecializedCategory A F).

      Let CosliceCategoryProjection' : SpecializedFunctor (a ↓ S) A.
        functor_simpl_abstract_trailing_props (ComposeFunctors snd_Functor (CommaCategoryProjection (SliceSpecializedCategory_Functor C a) S)).
      Defined.
      Definition CosliceCategoryProjection : SpecializedFunctor (a ↓ S) A := Eval hnf in CosliceCategoryProjection'.
    End Coslice.
  End Slice_Coslice.
End SliceCategory.


Section CommaCategoryInducedFunctor.
  Context `(A : @SpecializedCategory objA).
  Context `(B : @SpecializedCategory objB).
  Context `(C : @SpecializedCategory objC).

  Local Notation "S ↓ T" := (CommaSpecializedCategory S T).

  Let CommaCategoryInducedFunctor_ObjectOf s d (m : Morphism ((OppositeCategory (C ^ A)) * (C ^ B)) s d)
      (x : fst s ↓ snd s) : (fst d ↓ snd d)
    := existT _
              (projT1 x)
              (Compose ((snd m) (snd (projT1 x))) (Compose (projT2 x) ((fst m) (fst (projT1 x))))) :
         CommaSpecializedCategory_ObjectT (fst d) (snd d).

  Let CommaCategoryInducedFunctor_MorphismOf s d m s0 d0 (m0 : Morphism (fst s ↓ snd s) s0 d0) :
    Morphism (fst d ↓ snd d)
             (@CommaCategoryInducedFunctor_ObjectOf s d m s0)
             (@CommaCategoryInducedFunctor_ObjectOf s d m d0).
    refine (_ : CommaSpecializedCategory_MorphismT _ _); subst_body; simpl in *.
    exists (projT1 m0);
      simpl in *; clear.
    abstract induced_anihilate.
  Defined.

  Let CommaCategoryInducedFunctor' s d (m : Morphism ((OppositeCategory (C ^ A)) * (C ^ B)) s d) :
    SpecializedFunctor (fst s ↓ snd s) (fst d ↓ snd d).
    refine (Build_SpecializedFunctor (fst s ↓ snd s) (fst d ↓ snd d)
                                     (@CommaCategoryInducedFunctor_ObjectOf s d m)
                                     (@CommaCategoryInducedFunctor_MorphismOf s d m)
                                     _
                                     _
           );
    subst_body; simpl; clear;
     
    abstract pre_anihilate.
 
  Defined.

  Let CommaCategoryInducedFunctor'' s d (m : Morphism ((OppositeCategory (C ^ A)) * (C ^ B)) s d) :
    SpecializedFunctor (fst s ↓ snd s) (fst d ↓ snd d).
    simpl_definition_by_tac_and_exact (@CommaCategoryInducedFunctor' s d m) ltac:(subst_body; eta_red).
  Defined.

  Definition CommaCategoryInducedFunctor s d (m : Morphism ((OppositeCategory (C ^ A)) * (C ^ B)) s d) :
    SpecializedFunctor (fst s ↓ snd s) (fst d ↓ snd d)
    := Eval cbv beta iota zeta delta [CommaCategoryInducedFunctor''] in @CommaCategoryInducedFunctor'' s d m.
End CommaCategoryInducedFunctor.

Section SliceCategoryInducedFunctor.
  Context `(C : @SpecializedCategory objC).

  Section Slice_Coslice.
    Context `(D : @SpecializedCategory objD).

     
    Definition SliceCategoryInducedFunctor_NT s d (m : Morphism D s d) :
      SpecializedNaturalTransformation (SliceSpecializedCategory_Functor D s)
                                       (SliceSpecializedCategory_Functor D d).
      exists (fun _ : unit => m).
      simpl; intros; clear;
      abstract (autorewrite with category; reflexivity).
    Defined.

    Variable F : SpecializedFunctor C D.
    Variable a : D.

    Section Slice.
      Local Notation "F ↓ A" := (SliceSpecializedCategory A F).

      Let SliceCategoryInducedFunctor' F' a' (m : Morphism D a a') (T : SpecializedNaturalTransformation F' F) :
        SpecializedFunctor (F ↓ a) (F' ↓ a').
        functor_simpl_abstract_trailing_props (CommaCategoryInducedFunctor (s := (F, SliceSpecializedCategory_Functor D a))
                                                                       (d := (F', SliceSpecializedCategory_Functor D a'))
                                                                       (T, @SliceCategoryInducedFunctor_NT a a' m)).
      Defined.
      Definition SliceCategoryInducedFunctor F' a' (m : Morphism D a a') (T : SpecializedNaturalTransformation F' F) :
        SpecializedFunctor (F ↓ a) (F' ↓ a')
        := Eval hnf in @SliceCategoryInducedFunctor' F' a' m T.

      Definition SliceCategoryNTInducedFunctor F' T := @SliceCategoryInducedFunctor F' a (Identity _) T.
      Definition SliceCategoryMorphismInducedFunctor a' m := @SliceCategoryInducedFunctor F a' m (IdentityNaturalTransformation _).
    End Slice.

    Section Coslice.
      Local Notation "A ↓ F" := (CosliceSpecializedCategory A F).

      Let CosliceCategoryInducedFunctor' F' a' (m : Morphism D a' a) (T : SpecializedNaturalTransformation F F') :
        SpecializedFunctor (a ↓ F) (a' ↓ F').
        functor_simpl_abstract_trailing_props (CommaCategoryInducedFunctor (s := (SliceSpecializedCategory_Functor D a, F))
                                                                       (d := (SliceSpecializedCategory_Functor D a', F'))
                                                                       (@SliceCategoryInducedFunctor_NT a' a m, T)).
      Defined.
      Definition CosliceCategoryInducedFunctor F' a' (m : Morphism D a' a) (T : SpecializedNaturalTransformation F F') :
        SpecializedFunctor (a ↓ F) (a' ↓ F')
        := Eval hnf in @CosliceCategoryInducedFunctor' F' a' m T.

      Definition CosliceCategoryNTInducedFunctor F' T := @CosliceCategoryInducedFunctor F' a (Identity _) T.
      Definition CosliceCategoryMorphismInducedFunctor a' m := @CosliceCategoryInducedFunctor F a' m (IdentityNaturalTransformation _).
    End Coslice.
  End Slice_Coslice.

  Definition SliceCategoryOverInducedFunctor a a' (m : Morphism C a a') : SpecializedFunctor (C / a) (C / a')
    := Eval hnf in SliceCategoryMorphismInducedFunctor _ _ _ m.
  Definition CosliceCategoryOverInducedFunctor a a' (m : Morphism C a' a) : SpecializedFunctor (a \ C) (a' \ C)
    := Eval hnf in CosliceCategoryMorphismInducedFunctor _ _ _ m.
End SliceCategoryInducedFunctor.

Section LocallySmallCatOverInducedFunctor.
   
  Let C := LocallySmallCat.
   

  Let LocallySmallCatOverInducedFunctor_ObjectOf a a' (m : Morphism C a a') : C / a -> C / a'.
    refine (fun x => existT (fun αβ : _ * unit => Morphism C (fst αβ) a')
                            (projT1 x)
                            _ :
                       CommaSpecializedCategory_ObjectT (IdentityFunctor C) (SliceSpecializedCategory_Functor C a')).
    functor_simpl_abstract_trailing_props (Compose m (projT2 x)).
  Defined.
  Let OverLocallySmallCatInducedFunctor_ObjectOf a a' (m : Morphism C a' a) : a \ C -> a' \ C.
    refine (fun x => existT (fun αβ : unit * _ => Morphism C a' (snd αβ))
                            (projT1 x)
                            _ :
                       CommaSpecializedCategory_ObjectT (SliceSpecializedCategory_Functor C a') (IdentityFunctor C)).
    functor_simpl_abstract_trailing_props (Compose (projT2 x) m).
  Defined.

  Let LocallySmallCatOverInducedFunctor_MorphismOf a a' (m : Morphism C a a') s d (m0 : Morphism (C / a) s d) :
    Morphism (C / a') (@LocallySmallCatOverInducedFunctor_ObjectOf _ _ m s) (@LocallySmallCatOverInducedFunctor_ObjectOf _ _ m d).
    refine (_ : CommaSpecializedCategory_MorphismT _ _).
    exists (projT1 m0).
      subst_body; simpl in *; clear.
    abstract anihilate.
  Defined.
  Let OverLocallySmallCatInducedFunctor_MorphismOf a a' (m : Morphism C a' a) s d (m0 : Morphism (a \ C) s d) :
    Morphism (a' \ C) (@OverLocallySmallCatInducedFunctor_ObjectOf _ _ m s) (@OverLocallySmallCatInducedFunctor_ObjectOf _ _ m d).
    refine (_ : CommaSpecializedCategory_MorphismT _ _).
    exists (projT1 m0);
      subst_body; simpl in *; clear.
    abstract anihilate.
  Defined.

  Local Opaque LocallySmallCat.
  Let LocallySmallCatOverInducedFunctor'' a a' (m : Morphism C a a') : SpecializedFunctor (C / a) (C / a').
    refine (Build_SpecializedFunctor (C / a) (C / a')
                                     (@LocallySmallCatOverInducedFunctor_ObjectOf _ _ m)
                                     (@LocallySmallCatOverInducedFunctor_MorphismOf _ _ m)
                                     _
                                     _
           );
    subst_body; simpl; clear;
     
    abstract anihilate.
  Defined.
  Let OverLocallySmallCatInducedFunctor'' a a' (m : Morphism C a' a) : SpecializedFunctor (a \ C) (a' \ C).
    refine (Build_SpecializedFunctor (a \ C) (a' \ C)
                                     (@OverLocallySmallCatInducedFunctor_ObjectOf _ _ m)
                                     (@OverLocallySmallCatInducedFunctor_MorphismOf _ _ m)
                                     _
                                     _
           );
    subst_body; simpl; clear;
      abstract anihilate.
  Defined.

  Let LocallySmallCatOverInducedFunctor''' a a' (m : Morphism C a a') : SpecializedFunctor (C / a) (C / a').
    simpl_definition_by_tac_and_exact (@LocallySmallCatOverInducedFunctor'' _ _ m) ltac:(subst_body; eta_red).
  Defined.
  Let OverLocallySmallCatInducedFunctor''' a a' (m : Morphism C a' a) : SpecializedFunctor (a \ C) (a' \ C).
    simpl_definition_by_tac_and_exact (@OverLocallySmallCatInducedFunctor'' _ _ m) ltac:(subst_body; eta_red).
  Defined.

  Definition LocallySmallCatOverInducedFunctor a a' (m : Morphism C a a') : SpecializedFunctor (C / a) (C / a')
    := Eval cbv beta iota zeta delta [LocallySmallCatOverInducedFunctor'''] in @LocallySmallCatOverInducedFunctor''' _ _ m.
  Definition OverLocallySmallCatInducedFunctor a a' (m : Morphism C a' a) : SpecializedFunctor (a \ C) (a' \ C)
    := Eval cbv beta iota zeta delta [OverLocallySmallCatInducedFunctor'''] in @OverLocallySmallCatInducedFunctor''' _ _ m.
  Local Transparent LocallySmallCat.
End LocallySmallCatOverInducedFunctor.


Section CommaCategoryProjectionFunctor.
  Context `(A : LocallySmallSpecializedCategory objA).
  Context `(B : LocallySmallSpecializedCategory objB).
  Context `(C : SpecializedCategory objC).

  Local Notation "S ↓ T" := (CommaSpecializedCategory S T).

  Definition CommaCategoryProjectionFunctor_ObjectOf (ST : (OppositeCategory (C ^ A)) * (C ^ B)) :
    LocallySmallCat / (A * B : LocallySmallSpecializedCategory _)
    := let S := (fst ST) in
       let T := (snd ST) in
       existT _
              ((S ↓ T : LocallySmallSpecializedCategory _) : LocallySmallCategory, tt)
              (CommaCategoryProjection S T) :
         CommaSpecializedCategory_ObjectT (IdentityFunctor _)
                                          (SliceSpecializedCategory_Functor LocallySmallCat
                                                                            (A * B : LocallySmallSpecializedCategory _)).

  Definition CommaCategoryProjectionFunctor_MorphismOf s d (m : Morphism ((OppositeCategory (C ^ A)) * (C ^ B)) s d) :
    Morphism (LocallySmallCat / (A * B : LocallySmallSpecializedCategory _))
             (CommaCategoryProjectionFunctor_ObjectOf s)
             (CommaCategoryProjectionFunctor_ObjectOf d).
    hnf in *; constructor; simpl in *.
    exists (CommaCategoryInducedFunctor m, @unit_eq _ _).
    abstract (
        simpl;
        functor_eq;
        destruct_head_hnf @CommaSpecializedCategory_Morphism;
        destruct_sig;
        reflexivity
      ).
  Defined.

  Lemma CommaCategoryProjectionFunctor_FIdentityOf x :
    CommaCategoryProjectionFunctor_MorphismOf (Identity x) = Identity _.
      Time (expand; anihilate).
 
  Qed.

  Lemma CommaCategoryProjectionFunctor_FCompositionOf s d d' m m' :
    CommaCategoryProjectionFunctor_MorphismOf (@Compose _ _ s d d' m m')
    = Compose (CommaCategoryProjectionFunctor_MorphismOf m)
              (CommaCategoryProjectionFunctor_MorphismOf m').
      Time (expand; anihilate).
 
  Qed.

  Definition CommaCategoryProjectionFunctor :
    SpecializedFunctor ((OppositeCategory (C ^ A)) * (C ^ B))
                       (LocallySmallCat / (A * B : LocallySmallSpecializedCategory _)).
    refine (Build_SpecializedFunctor ((OppositeCategory (C ^ A)) * (C ^ B))
                                     (LocallySmallCat / (A * B : LocallySmallSpecializedCategory _))
                                     CommaCategoryProjectionFunctor_ObjectOf
                                     CommaCategoryProjectionFunctor_MorphismOf
                                     _
                                     _);
    intros;
    [ apply CommaCategoryProjectionFunctor_FCompositionOf
    | apply CommaCategoryProjectionFunctor_FIdentityOf ].
  Defined.
End CommaCategoryProjectionFunctor.

Section SliceCategoryProjectionFunctor.
  Context `(C : LocallySmallSpecializedCategory objC).
  Context `(D : SpecializedCategory objD).

  Local Arguments ExponentialLaw4Functor_Inverse_ObjectOf_ObjectOf / .
  Local Arguments ComposeFunctors / .
  Local Arguments LocallySmallCatOverInducedFunctor / .
   
  Local Arguments CommaCategoryProjectionFunctor / .
  Local Arguments SwapFunctor / .
  Local Arguments ExponentialLaw1Functor_Inverse / .
  Local Arguments IdentityFunctor / .
 

  Definition SliceCategoryProjectionFunctor_pre_pre'
    := Eval hnf in (LocallySmallCatOverInducedFunctor (ProductLaw1Functor C : Morphism LocallySmallCat (C * 1 : LocallySmallSpecializedCategory _) C)).

  Definition SliceCategoryProjectionFunctor_pre_pre : SpecializedFunctor (LocallySmallCat / (C * 1 : LocallySmallSpecializedCategory _)) (LocallySmallCat / C).
    functor_abstract_trailing_props SliceCategoryProjectionFunctor_pre_pre'.
  Defined.

  Arguments SliceCategoryProjectionFunctor_pre_pre / .

 
   

  Definition SliceCategoryProjectionFunctor_pre' : ((LocallySmallCat / C) ^ (D * (OppositeCategory (D ^ C)))).
    refine (ComposeFunctors _ ((ExponentialLaw1Functor_Inverse D) * IdentityFunctor (OppositeCategory (D ^ C)))).
    refine (ComposeFunctors _ (SwapFunctor _ _)).
    refine (ComposeFunctors _ (CommaCategoryProjectionFunctor (C : LocallySmallSpecializedCategory _) (1 : LocallySmallSpecializedCategory _) D)).
     
    let F := (eval hnf in SliceCategoryProjectionFunctor_pre_pre) in
    exact F.
 
  Defined.

  Definition SliceCategoryProjectionFunctor_pre'' : ((LocallySmallCat / C) ^ (D * (OppositeCategory (D ^ C)))).
    functor_abstract_trailing_props SliceCategoryProjectionFunctor_pre'.
  Defined.

  Definition SliceCategoryProjectionFunctor_pre := Eval hnf in SliceCategoryProjectionFunctor_pre''.

  Definition SliceCategoryProjectionFunctor' : (((LocallySmallCat / C) ^ D) ^ (OppositeCategory (D ^ C))).
    refine ((ExponentialLaw4Functor_Inverse _ _ _) _).
    let F := (eval hnf in SliceCategoryProjectionFunctor_pre) in
    exact F.
  Defined.

  Definition SliceCategoryProjectionFunctor'' : (((LocallySmallCat / C) ^ D) ^ (OppositeCategory (D ^ C))).
    functor_abstract_trailing_props SliceCategoryProjectionFunctor'.
  Defined.

  Definition SliceCategoryProjectionFunctor : ((LocallySmallCat / C) ^ D) ^ (OppositeCategory (D ^ C))
    := Eval cbv beta iota zeta delta [SliceCategoryProjectionFunctor''] in SliceCategoryProjectionFunctor''.

  Definition CosliceCategoryProjectionFunctor : ((LocallySmallCat / C) ^ (OppositeCategory D)) ^ (D ^ C).
    refine ((ExponentialLaw4Functor_Inverse _ _ _) _).
    refine (ComposeFunctors _ ((OppositeFunctor (ExponentialLaw1Functor_Inverse D)) * IdentityFunctor (D ^ C))).
    refine (ComposeFunctors _ (CommaCategoryProjectionFunctor (1 : LocallySmallSpecializedCategory _) (C : LocallySmallSpecializedCategory _) D)).
    refine (LocallySmallCatOverInducedFunctor _).
    refine (ComposeFunctors _ (SwapFunctor _ _)).
    exact (ProductLaw1Functor _).
  Defined.
End SliceCategoryProjectionFunctor.



