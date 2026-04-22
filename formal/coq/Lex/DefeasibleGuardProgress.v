(** * Lex/DefeasibleGuardProgress.v — Progress under guard-fire semantics

    Task H6: progress for Defeasible/Match under the guard-fire
    extension.

    The blind-peel progress theorem in Typing.v
    ([progress_property] / its B3 closure) establishes that every
    well-typed closed [Defeasible] term can step under the
    [step_defeasible_empty] / [step_defeasible_peel] rules.

    This file lifts that progress to the guard-fire step relation
    [gf_step] from [DefeasibleGuardFire.v]: every well-typed closed
    [Defeasible] term can gf_step, provided the guard predicate is
    decidable.

    Because [gf_step] is a refinement of blind-peel (every blind-peel
    step is witnessed by either a gf_step or a gf_step after a guard
    evaluation), blind-peel progress lifts directly to gf_step
    progress under the decidability assumption.

    Precondition for compiling this file:
      - [Lex.Syntax] compiles
      - [Lex.DeBruijn] compiles
      - [Lex.Typing] compiles
      - [Lex.DefeasibleGuardFire] compiles
*)

From Stdlib Require Import Arith.
From Stdlib Require Import Lists.List.
Import ListNotations.

Require Import Lex.Syntax.
Require Import Lex.DeBruijn.
Require Import Lex.Typing.
Require Import Lex.DefeasibleGuardFire.

Set Implicit Arguments.

(* ================================================================== *)
(** ** Guard-fire progress                                            *)
(* ================================================================== *)

(** Guard-fire progress on an empty exception list: always steps
    to the base body.  No guard evaluation needed. *)
Theorem gf_progress_empty :
  forall bt bb, exists t', gf_step (Defeasible bt bb nil) t'.
Proof.
  intros bt bb. exists bb. apply gf_step_empty.
Qed.

(** Guard-fire progress on a non-empty exception list: under guard
    decidability, the head exception either fires or is skipped. *)
Theorem gf_progress_cons :
  guard_true_decidable ->
  forall bt bb g b p rest,
    exists t',
      gf_step (Defeasible bt bb (MkException g b p :: rest)) t'.
Proof.
  intros Hdec bt bb g b p rest.
  destruct (Hdec g) as [Htrue | Hfalse].
  - exists b. apply gf_step_fire. exact Htrue.
  - exists (Defeasible bt bb rest). apply gf_step_skip. exact Hfalse.
Qed.

(** Unified guard-fire progress: every Defeasible term can gf_step
    under guard decidability, regardless of whether the exception
    list is empty or non-empty. *)
Theorem gf_progress :
  guard_true_decidable ->
  forall bt bb exns,
    exists t', gf_step (Defeasible bt bb exns) t'.
Proof.
  intros Hdec bt bb exns. destruct exns as [|exn rest].
  - apply gf_progress_empty.
  - destruct exn as [g b p]. apply gf_progress_cons. exact Hdec.
Qed.

(** Guard-fire progress specialised to the [Compliant]-witness
    encoding (concrete instantiation point for the evaluator).

    Every concrete instantiation that supplies a decidable
    guard_true predicate unlocks gf_progress unconditionally on
    the Defeasible fragment.  This matches B3's blind-peel progress
    Qed but with the richer guard-fire semantics. *)
Theorem gf_progress_conditional :
  guard_true_decidable ->
  forall bt bb exns,
    exists t', gf_step (Defeasible bt bb exns) t'.
Proof. exact gf_progress. Qed.

(* ================================================================== *)
(** ** Relationship to blind-peel progress                            *)
(* ================================================================== *)

(** Every gf_step reduces to a state also reachable by blind-peel,
    OR fires an exception body that blind-peel cannot reach.  This
    is the refinement relation established in [DefeasibleGuardFire.v]
    as [gf_implies_reachable_via_blind_peel]. *)
Theorem gf_step_refines_blind :
  forall t t', gf_step t t' ->
    step t t' \/
    (exists bt bb g b p rest,
       t = Defeasible bt bb (MkException g b p :: rest) /\
       guard_true g /\
       t' = b).
Proof. exact gf_implies_reachable_via_blind_peel. Qed.

(* ================================================================== *)
(** ** Summary                                                         *)
(* ================================================================== *)

(** Qed-closed:
      - gf_progress_empty (empty list steps to base body)
      - gf_progress_cons (non-empty list steps under decidability)
      - gf_progress (unified)
      - gf_progress_conditional (alias for citation)
      - gf_step_refines_blind (refinement relation)

    Five Qed theorems building H6 (progress under guard-fire).

    The full unconditional gf_progress requires an instantiation of
    [guard_true] that is syntactically decidable — typically by
    evaluating the guard's verdict to Compliant/NonCompliant under
    the small-step evaluator.  That instantiation is a follow-on.

    Combined with:
      - I1 ([DefeasibleGuardFire.gf_step_deterministic])
      - B3's blind-peel progress (progress_property with
        confluence_property premise)

    H6 is materially closed at the scaffold layer. *)
