(** * Lex/Requirements.v - Requirements index for [progress] and [preservation]

    This file enumerates the auxiliary lemmas that must be proven
    before [preservation_property] and [progress_property] in
    [Typing.v] can close as full theorems.

    Each entry below is either:

    (a) a real citation of a Qed-closed upstream lemma (no
        tautological P → P shape), OR

    (b) a forward reference to a [Prop]-level specification
        Definition in [DeBruijn.v] (e.g.
        [shift_subst_commute_ws_spec], [subst_subst_ws_spec])
        whose Qed-closed structural-induction proof is explicit
        follow-on work (~200 lines of mechanical case-analysis
        per lemma over the 30-constructor [Term] AST).

    (c) a forward reference to [confluence_property],
        [preservation_property], or [progress_property]
        Definitions in [Typing.v] (the canonical statement
        forms; Qed-closed proofs are follow-on).

    Previous versions of this file contained P → P tautologies of
    the form [Lemma req_X : P → P. Proof. intros ... H. exact H. Qed.]
    - these have been removed.  A tautology does not record an
    obligation any better than a named [Prop] Definition does, and
    gives a false impression of progress by inflating the Qed
    count.  This file now only names the real specifications and
    cites their upstream Qed-closed forms when available.

    Precondition for compiling this file:
      - [Lex.Syntax] compiles.
      - [Lex.DeBruijn] compiles.
      - [Lex.Typing] compiles.
      - [Lex.Typing_progress_skeleton] compiles.
*)

From Stdlib Require Import Arith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Strings.String.
Import ListNotations.

Require Import Lex.Syntax.
Require Import Lex.DeBruijn.
Require Import Lex.Typing.
Require Import Lex.Typing_progress_skeleton.

(* ================================================================== *)
(** ** Depth 0: DeBruijn-level substitution calculus                   *)
(* ================================================================== *)

(** [subst_var_identity]: identity substitution for well-scoped
    terms.  Already Qed-closed in [DeBruijn.v] at line ~893 via
    mutual structural induction on Term / Branch / Exception.
    Re-exported here under the [req_] prefix as a forwarding
    citation. *)
Lemma req_subst_var_identity : forall (i : nat) (t : Term),
  well_scoped (S i) t ->
  subst i (Var i) t = t.
Proof.
  apply subst_var_identity.
Qed.

(** [shift_subst_commute_ws]: substitution commutes with shifting
    under the [well_scoped (S i) t] premise.

    The naive unconditional form is FALSE - refuted by
    [shift_subst_commute_not_unconditional] in [DeBruijn.v]
    (concrete 4-term counterexample).

    The corrected statement is captured as the [Prop] specification
    [shift_subst_commute_ws_spec] in [DeBruijn.v] and is now
    Qed-closed there as [shift_subst_commute_ws_spec_proof] via
    full mutual structural induction over the 30-constructor Term
    AST (plus Branch and Exception companions).

    This file records the obligation by naming the specification
    directly, and the companion Theorem discharges it
    unconditionally. *)
Definition req_shift_subst_commute_ws : Prop :=
  shift_subst_commute_ws_spec.

Theorem req_shift_subst_commute_ws_proof : req_shift_subst_commute_ws.
Proof.
  unfold req_shift_subst_commute_ws.
  exact shift_subst_commute_ws_spec_proof.
Qed.

(** [subst_subst_ws]: substitution composes under the
    [well_scoped (S i) t] premise.

    The naive form with [subst (i - j) s r] is FALSE - refuted by
    [subst_subst_not_unconditional] in [DeBruijn.v].  The corrected
    form uses [subst i s r] and is captured as
    [subst_subst_ws_spec] in [DeBruijn.v], now Qed-closed there as
    [subst_subst_ws_spec_proof] via full mutual structural induction.
    The companion Theorem below discharges the obligation
    unconditionally. *)
Definition req_subst_subst_ws : Prop :=
  subst_subst_ws_spec.

Theorem req_subst_subst_ws_proof : req_subst_subst_ws.
Proof.
  unfold req_subst_subst_ws.
  exact subst_subst_ws_spec_proof.
Qed.

(* ================================================================== *)
(** ** Depth 1-4: typing metatheory                                    *)
(* ================================================================== *)

(** [canonical_forms_pi]: values of Pi type are lambdas.  Already
    Qed-closed in [Typing_progress_skeleton.v] conditionally on
    [confluence_property] (threaded through the Section wrapper
    because its proof uses [conv_eq_trans], which itself requires
    confluence).  We re-export the conditional form here. *)
Lemma req_canonical_forms_pi :
  confluence_property ->
  forall (v A B : Term) (eff : option EffectRow),
    value v ->
    has_type nil v (Pi A eff B) ->
    exists dom body, v = Lambda dom body.
Proof.
  intro Hconf. exact (canonical_forms_pi Hconf).
Qed.

(** [confluence]: Church-Rosser for [step].  Captured as the
    [confluence_property] Definition in [Typing.v].  G1's
    [Lex.Confluence] file provides the parallel-reduction
    scaffolding ([par] inductive, [par_refl] Qed,
    [step_implies_par] Qed, [par_implies_steps] Qed).  The
    remaining [par_diamond] / [par_star_diamond] /
    [confluence_theorem] closure is follow-on work (named
    specifications: [Confluence.par_diamond_spec],
    [Confluence.par_star_diamond_spec],
    [Confluence.confluence_spec]). *)
Definition req_confluence : Prop := confluence_property.

(** [preservation]: typing preserved by [step].  Captured as
    [preservation_property] in [Typing.v].  Follow-on: induction
    on typing derivation using substitution_preserves_typing
    (which depends on the DeBruijn _ws specs above). *)
Definition req_preservation : Prop := preservation_property.

(** [progress]: closed well-typed terms are values or can step.
    Captured as [progress_property] in [Typing.v].

    B3 closed the conditional form [progress :
    confluence_property -> progress_property] in [Typing.v] via
    full case analysis on the typing derivation, including
    operational step rules for Defeasible and Match.  The
    unconditional form becomes Qed-closable once confluence is
    repaired and proved (G1 follow-on).  The conditional
    discharge is cited below. *)
Definition req_progress : Prop := progress_property.

Theorem req_progress_conditional :
  confluence_property -> match_exhaustiveness_property -> req_progress.
Proof.
  unfold req_progress.
  exact progress.
Qed.

(** Stronger progress route: a checker-produced
    [match_coverage_property] certificate implies the older
    [match_exhaustiveness_property] premise and therefore suffices
    for progress. *)
Theorem req_progress_from_match_coverage :
  confluence_property -> match_coverage_property -> req_progress.
Proof.
  unfold req_progress.
  exact progress_from_match_coverage.
Qed.

(** Constructive certificate route: a checker-produced
    [match_coverage_certificate_property] either supplies wildcard coverage
    or a finite constructor environment for each well-typed match.  This
    implies [match_coverage_property] and therefore suffices for progress. *)
Theorem req_progress_from_match_coverage_certificate :
  confluence_property -> match_coverage_certificate_property -> req_progress.
Proof.
  unfold req_progress.
  exact progress_from_match_coverage_certificate.
Qed.

(** [has_type_well_scoped]: if [has_type ctx t T] then [t] is
    well-scoped at [length ctx].  Qed-closed in [Typing.v] via
    Gallina [Fixpoint] structural recursion on the [has_type]
    derivation, using two nested [fix] helpers for the
    [T_Defeasible] and [T_Match] list premises (whose [has_type]
    sub-derivations inside [Forall]/[Forall2] are structural
    sub-terms of the outer [has_type] proof).  Re-exported as a
    forwarding citation. *)
Lemma req_has_type_well_scoped :
  forall (ctx : Context) (t T : Term),
    has_type ctx t T ->
    well_scoped (Datatypes.length ctx) t.
Proof.
  apply has_type_well_scoped.
Qed.

(** [substitution_preserves_typing]: the bridge lemma for
    preservation's beta-reduction case.  Stated here as a
    [Prop]-level obligation; Qed-closed proof is follow-on
    (depends on [req_shift_subst_commute_ws] +
    [req_subst_subst_ws]). *)
Definition req_substitution_preserves_typing : Prop :=
  forall (ctx : Context) (A B t s : Term),
    has_type (ctx_extend ctx A) t B ->
    has_type ctx s A ->
    has_type ctx (subst 0 s t) (subst 0 s B).

(** [weakening]: typing is preserved by context extension.
    Stated here as a [Prop]-level obligation; Qed-closed proof is
    follow-on. *)
Definition req_weakening : Prop :=
  forall (ctx : Context) (t T A : Term),
    has_type ctx t T ->
    has_type (ctx_extend ctx A) (shift 0 1 t) (shift 0 1 T).

(* ================================================================== *)
(** ** Defeasible/Match progress - definitional gap                    *)
(* ================================================================== *)

(** Defeasible and Match now have operational [step] rules in [Typing.v].
    The remaining progress frontier is the global premise package needed
    to rule out stuck matches: confluence and match exhaustiveness for
    well-typed admissible scrutinees.

    These are captured as [Prop]-level obligations so the executable
    checker can name the exact frontier without importing unfinished
    metatheory as an admitted theorem. *)
Definition req_defeasible_progress_decision : Prop :=
  forall (base_ty base_body : Term) (exns : list Exception) (T : Term),
    has_type nil (Defeasible base_ty base_body exns) T ->
    value (Defeasible base_ty base_body exns) \/
    exists t', step (Defeasible base_ty base_body exns) t'.

(** B3 resolved the Defeasible progress decision via operational step
    rules ([step_defeasible_empty], [step_defeasible_peel]).  Under
    the confluence-property premise, the full progress theorem covers
    every [Term] constructor, including [Defeasible], so the
    conditional form of the decision obligation is discharged. *)
Theorem req_defeasible_progress_conditional :
  confluence_property -> match_exhaustiveness_property ->
  req_defeasible_progress_decision.
Proof.
  intros Hconf Hexhaust base_ty base_body exns T Hty.
  exact (progress Hconf Hexhaust _ _ Hty).
Qed.

Definition req_match_progress_decision : Prop :=
  forall (scr ret : Term) (branches : list Branch) (T : Term),
    has_type nil (Match scr ret branches) T ->
    value (Match scr ret branches) \/
    exists t', step (Match scr ret branches) t'.

(** B3 resolved the Match progress decision via operational step
    rules ([step_match_scrutinee], [step_match_wild],
    [step_match_ctor_fire], [step_match_ctor_skip]); the empty-branch
    case is excluded by [T_Match]'s nonempty premise.
    Same discharge as [req_defeasible_progress_conditional]. *)
Theorem req_match_progress_conditional :
  confluence_property -> match_exhaustiveness_property ->
  req_match_progress_decision.
Proof.
  intros Hconf Hexhaust scr ret branches T Hty.
  exact (progress Hconf Hexhaust _ _ Hty).
Qed.

Theorem req_match_progress_from_match_coverage_certificate :
  confluence_property -> match_coverage_certificate_property ->
  req_match_progress_decision.
Proof.
  intros Hconf Hcert scr ret branches T Hty.
  exact (progress_from_match_coverage_certificate Hconf Hcert _ _ Hty).
Qed.
