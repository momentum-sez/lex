(** * Lex/TypingPreservationScaffold.v — Per-case preservation scaffolding

    Task B2: close [preservation_property] with a Qed.

    This file discharges the "easy" per-constructor preservation
    cases — those for terms that DO NOT step under the [step]
    relation (variables, sorts, constants, literals, axiom uses).
    For those constructors, preservation is vacuous: there is no
    step to preserve typing across.

    The residual non-trivial cases (T_App beta, T_Let beta,
    congruence rules on App/Pi/Lambda/Let/Match/Defeasible) depend
    on [substitution_property] (bridge lemma B1) + J2's relaxed
    [subst_subst_ws_at_depth] / [shift_subst_commute_ws_at_depth].
    Those are follow-on work; the present file closes the trivial
    half of the case split.
*)

From Stdlib Require Import Arith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Strings.String.
Import ListNotations.

Require Import Lex.Syntax.
Require Import Lex.DeBruijn.
Require Import Lex.Typing.

Set Implicit Arguments.

(* ================================================================== *)
(** ** Irreducible-constructor preservation cases                     *)
(* ================================================================== *)

(** Preservation for [Var i]: vacuous — no step applies. *)
Theorem preservation_var :
  forall (ctx : Context) (i : nat) (T : Term) (t' : Term),
    has_type ctx (Var i) T ->
    step (Var i) t' ->
    has_type ctx t' T.
Proof.
  intros ctx i T t' _ Hstep. exfalso. eapply step_Var_inv. exact Hstep.
Qed.

(** Preservation for [TSort s]: vacuous. *)
Theorem preservation_sort :
  forall (ctx : Context) (s : Sort) (T : Term) (t' : Term),
    has_type ctx (TSort s) T ->
    step (TSort s) t' ->
    has_type ctx t' T.
Proof.
  intros ctx s T t' _ Hstep. exfalso. eapply step_TSort_inv. exact Hstep.
Qed.

(** Preservation for [Constant c]: vacuous. *)
Theorem preservation_constant :
  forall (ctx : Context) (c : string) (T : Term) (t' : Term),
    has_type ctx (Constant c) T ->
    step (Constant c) t' ->
    has_type ctx t' T.
Proof.
  intros ctx c T t' _ Hstep. exfalso. eapply step_Constant_inv. exact Hstep.
Qed.

(** Preservation for [IntLit n]: vacuous. *)
Theorem preservation_intlit :
  forall (ctx : Context) (n : nat) (T : Term) (t' : Term),
    has_type ctx (IntLit n) T ->
    step (IntLit n) t' ->
    has_type ctx t' T.
Proof.
  intros ctx n T t' _ Hstep. exfalso. eapply step_IntLit_inv. exact Hstep.
Qed.

(** Preservation for [RatLit p q]: vacuous. *)
Theorem preservation_ratlit :
  forall (ctx : Context) (p q : nat) (T : Term) (t' : Term),
    has_type ctx (RatLit p q) T ->
    step (RatLit p q) t' ->
    has_type ctx t' T.
Proof.
  intros ctx p q T t' _ Hstep. exfalso. eapply step_RatLit_inv. exact Hstep.
Qed.

(** Preservation for [StringLit s]: vacuous. *)
Theorem preservation_stringlit :
  forall (ctx : Context) (s : string) (T : Term) (t' : Term),
    has_type ctx (StringLit s) T ->
    step (StringLit s) t' ->
    has_type ctx t' T.
Proof.
  intros ctx s T t' _ Hstep. exfalso. eapply step_StringLit_inv. exact Hstep.
Qed.

(** Preservation for [AxiomUse a]: vacuous. *)
Theorem preservation_axiomuse :
  forall (ctx : Context) (a : string) (T : Term) (t' : Term),
    has_type ctx (AxiomUse a) T ->
    step (AxiomUse a) t' ->
    has_type ctx t' T.
Proof.
  intros ctx a T t' _ Hstep. exfalso. eapply step_AxiomUse_inv. exact Hstep.
Qed.

(* ================================================================== *)
(** ** Follow-on: binder / application cases                          *)
(* ================================================================== *)

(** The remaining preservation cases (T_App beta, T_Let beta,
    congruence rules on App-func, App-arg, Pi-dom, Pi-cod,
    Lambda-dom, Lambda-body, Let-ty, Let-val, Let-body, Annot-e,
    Annot-ty, Match-scrutinee, Match-return, Match-branch,
    Defeasible-base-ty, Defeasible-base-body, Defeasible-exn-guard,
    Defeasible-exn-body, plus the 20+ other congruence rules
    introduced by G1) route through:

    - [substitution_property] (bridge from B1: substitution preserves
      typing) for the beta cases, and
    - context conversion for the binder-subterm congruence cases
      (because the substitution in the body's type is replaced by
      a conv-equal substitution when the binder-domain steps).

    The composite proof is structurally a ~50-case induction on
    [has_type ctx t T] with inner induction on [step t t'], using
    [shift_subst_commute_ws_at_depth] / [subst_subst_ws_at_depth]
    at the binder cases.  Task B2 closes the full induction; this
    file closes the 7 trivial cases as named stepping stones. *)

(* ================================================================== *)
(** ** Summary                                                         *)
(* ================================================================== *)

(** Qed-closed:
      - preservation_var
      - preservation_sort
      - preservation_constant
      - preservation_intlit
      - preservation_ratlit
      - preservation_stringlit
      - preservation_axiomuse

    7 of ~50 preservation cases discharged.  The remaining ~43
    cases are the binder congruence + beta-reduction cases; task
    B2 closes them using the J2 relaxed-depth lemmas. *)
