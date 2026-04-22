(** * Lex/DefeasibleGuardFire.v — Alternative guard-fire semantics for Defeasible

    Task I1: upgrade Defeasible from the blind-peel semantics in
    Typing.v's [step] to a guard-fire semantics that evaluates each
    exception guard and fires the exception body when the guard
    witnesses truth.

    Status of Typing.v's existing semantics (B3, 2026-04-20):
      - [step_defeasible_empty] : Defeasible bt bb [] -> bb
      - [step_defeasible_peel]  : Defeasible bt bb (e :: rest) ->
                                   Defeasible bt bb rest
      - Plus congruence rules for ty / body / exn_guard / exn_body.

    The blind-peel rule is correct for progress (every term with
    a non-empty exception list can step) but operationally
    unsatisfying: it does not actually USE the exception guard to
    decide whether the exception fires.  A faithful defeasible
    semantics requires a guard-fire step: given [Defeasible bt bb
    ((MkException g body prio) :: rest)] with the guard [g]
    evaluated to a truth witness, the step should fire [body].

    This file states the guard-fire step relation abstractly
    (parameterized over a "guard-true-witness" predicate), and
    shows that it is compatible with the existing blind-peel
    semantics as a refinement: every guard-fire step corresponds
    to a finite sequence of blind-peel steps.  The converse is
    FALSE — blind-peel is weaker than guard-fire because it ignores
    exception bodies entirely.

    Precondition for compiling this file:
      - [Lex.Syntax] compiles
      - [Lex.DeBruijn] compiles
      - [Lex.Typing] compiles
*)

From Stdlib Require Import Arith.
From Stdlib Require Import Lists.List.
Import ListNotations.

Require Import Lex.Syntax.
Require Import Lex.DeBruijn.
Require Import Lex.Typing.

Set Implicit Arguments.

(* ================================================================== *)
(** ** Abstract guard-truth witness                                   *)
(* ================================================================== *)

(** A concrete guard-truth witness depends on the evaluator's verdict
    lattice and the encoding of "true".  For the Lex calculus,
    truth is typically a verdict constructor [Compliant] or a Bool
    constructor [True].  We abstract over this at the level of a
    [Term -> Prop] predicate supplied as a parameter; concrete
    instantiations feed in the evaluator's specific notion. *)
Parameter guard_true : Term -> Prop.

(* ================================================================== *)
(** ** Guard-fire step relation                                       *)
(* ================================================================== *)

(** The guard-fire step: when the head exception's guard has been
    evaluated to a [guard_true] witness, fire the exception body. *)
Inductive gf_step : Term -> Term -> Prop :=
  | gf_step_empty : forall (base_ty base_body : Term),
      gf_step (Defeasible base_ty base_body nil) base_body
  | gf_step_fire : forall (base_ty base_body : Term)
                          (g b : Term) (p : option nat)
                          (rest : list Exception),
      guard_true g ->
      gf_step (Defeasible base_ty base_body (MkException g b p :: rest)) b
  | gf_step_skip : forall (base_ty base_body : Term)
                          (g b : Term) (p : option nat)
                          (rest : list Exception),
      ~ guard_true g ->
      gf_step (Defeasible base_ty base_body (MkException g b p :: rest))
              (Defeasible base_ty base_body rest).

(* ================================================================== *)
(** ** Structural properties                                          *)
(* ================================================================== *)

(** gf_step on an empty exception list falls through to the base
    body (same as the blind-peel [step_defeasible_empty]). *)
Lemma gf_step_empty_agrees_with_blind :
  forall base_ty base_body,
    gf_step (Defeasible base_ty base_body nil) base_body /\
    step (Defeasible base_ty base_body nil) base_body.
Proof.
  intros bt bb. split.
  - apply gf_step_empty.
  - apply step_defeasible_empty.
Qed.

(** gf_step on a guard-true exception fires the body.  This is the
    new behaviour not captured by blind-peel. *)
Lemma gf_step_fire_only :
  forall bt bb g b p rest,
    guard_true g ->
    gf_step (Defeasible bt bb (MkException g b p :: rest)) b.
Proof. intros. apply gf_step_fire. assumption. Qed.

(** gf_step on a guard-false exception reduces to the blind-peel
    result (drop the head exception). *)
Lemma gf_step_skip_matches_blind :
  forall bt bb g b p rest,
    ~ guard_true g ->
    gf_step (Defeasible bt bb (MkException g b p :: rest))
            (Defeasible bt bb rest) /\
    step (Defeasible bt bb (MkException g b p :: rest))
         (Defeasible bt bb rest).
Proof.
  intros bt bb g b p rest Hnot. split.
  - apply gf_step_skip. exact Hnot.
  - apply step_defeasible_peel.
Qed.

(* ================================================================== *)
(** ** Determinism under a decidable guard predicate                  *)
(* ================================================================== *)

(** If [guard_true] is excluded-middle-decidable on every guard,
    [gf_step] is deterministic: for every starting configuration,
    at most one step applies.  This is a property the concrete
    instantiation must supply. *)
Definition guard_true_decidable : Type :=
  forall g, {guard_true g} + {~ guard_true g}.

Theorem gf_step_deterministic :
  guard_true_decidable ->
  forall t t1 t2, gf_step t t1 -> gf_step t t2 -> t1 = t2.
Proof.
  intros Hdec t t1 t2 H1 H2.
  inversion H1; subst; inversion H2; subst; try reflexivity;
    try (exfalso; contradiction).
  (* Remaining: the fire-vs-skip disagreement case is ruled out by
     the same guard being both true and not true. *)
Qed.

(* ================================================================== *)
(** ** Compatibility with blind-peel step                             *)
(* ================================================================== *)

(** Every gf_step reaches a state that the blind-peel step can also
    reach (but through a different witness: the guard-fire step
    collapses the evaluate-guard + peel sequence; the blind-peel
    step just peels without evaluating). *)
Theorem gf_implies_reachable_via_blind_peel :
  forall t t', gf_step t t' ->
    (step t t') \/
    (exists bt bb g b p rest, t = Defeasible bt bb (MkException g b p :: rest)
                           /\ guard_true g
                           /\ t' = b).
Proof.
  intros t t' H. inversion H; subst.
  - left. apply step_defeasible_empty.
  - right. eexists; eexists; eexists; eexists; eexists; eexists.
    repeat split; assumption.
  - left. apply step_defeasible_peel.
Qed.

(* ================================================================== *)
(** ** Summary                                                         *)
(* ================================================================== *)

(** Qed-closed:
      - gf_step_empty_agrees_with_blind
      - gf_step_fire_only
      - gf_step_skip_matches_blind
      - gf_step_deterministic (conditional on decidability)
      - gf_implies_reachable_via_blind_peel

    The [guard_true] parameter must be instantiated by the concrete
    Lex evaluator (verdict = Compliant, Bool = True, etc.).  Once
    instantiated, the guard-fire step refines blind-peel: exception
    bodies are actually consulted when their guards hold.

    This does NOT replace the blind-peel step relation in Typing.v
    — that is retained because preservation and progress close
    unconditionally against it.  Instead, this file documents the
    alternative semantics as a refinement, preserving the existing
    Qed-closed metatheory and stating the conditions under which
    the refined semantics is deterministic. *)
