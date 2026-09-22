From Stdlib Require Import Lists.List Strings.String Arith.Arith Lia.
From Lex Require Import Syntax DeBruijn Typing.
From P04Substitution Require Import SimultaneousArgs.
From P04ArgsSubstitution Require Import ArgsSubstitution.
From P04Source Require Import TypeReduction.
From P04Products Require Import Parallel ParallelSubstitution.
Import ListNotations.

Lemma pars_refl : forall xs, pars xs xs.
Proof. intro xs; induction xs; constructor; auto using par_refl. Qed.
Lemma parbs_refl : forall bs, parbs bs bs.
Proof.
  intro bs; induction bs as [|[pat body] rest IH]; constructor;
    auto using par_refl.
Qed.
Lemma pares_refl : forall es, pares es es.
Proof.
  intro es; induction es as [|[guard body prio] rest IH]; constructor;
    auto using par_refl.
Qed.

Lemma pars_context : forall pre post a a', par a a' ->
  pars (pre ++ a :: post) (pre ++ a' :: post).
Proof.
  intros pre post a a' H. apply pars_app; [apply pars_refl |].
  constructor; auto using pars_refl.
Qed.

Lemma parbs_context : forall pre post pat b b', par b b' ->
  parbs (pre ++ MkBranch pat b :: post) (pre ++ MkBranch pat b' :: post).
Proof.
  intros pre post pat b b' H; induction pre as [|[p t] rest IH]; simpl;
    constructor; auto using par_refl, parbs_refl.
Qed.

Lemma pares_guard_context : forall pre post g g' b prio, par g g' ->
  pares (pre ++ MkException g b prio :: post)
        (pre ++ MkException g' b prio :: post).
Proof.
  intros pre post g g' b prio H; induction pre as [|[q t p] rest IH]; simpl;
    constructor; auto using par_refl, pares_refl.
Qed.

Lemma pares_body_context : forall pre post g b b' prio, par b b' ->
  pares (pre ++ MkException g b prio :: post)
        (pre ++ MkException g b' prio :: post).
Proof.
  intros pre post g b b' prio H; induction pre as [|[q t p] rest IH]; simpl;
    constructor; auto using par_refl, pares_refl.
Qed.

Theorem step_parallel : forall t u, Conversion.step t u -> par t u.
Proof.
  intros t u H; induction H;
    try solve [econstructor; eauto using par_refl, pars_refl, parbs_refl,
      pares_refl, pars_context, parbs_context, pares_guard_context, pares_body_context].
Qed.

Print Assumptions step_parallel.
