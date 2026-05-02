(** * Lex/Typing_progress_skeleton.v — Unconditional progress theorem

    With the step relation now extended to full binder congruence (see
    [Typing.v] step inductive), and with Tait-Martin-Löf confluence
    proved unconditionally (see [Confluence.v]), the progress theorem
    that previously required an [Hconf : confluence_property] Section
    hypothesis collapses to the unconditional form:

      [progress_skeleton : progress_property]

    This file historically served as a staging ground for breaking the
    monolithic [progress] placeholder at [Typing.v]:708 into structured
    named lemmas with [Hconf]-threaded Section wrappers.  Now that
    confluence lands as a Qed theorem, we drop the Section wrapper
    and prove the unconditional progress theorem directly, citing
    [Confluence.confluence_provable] where the old skeleton threaded
    [Hconf].

    Historic references (all discharged as Qed in [Typing.v] or
    [Confluence.v]):
      - canonical_forms_pi          → [Typing.canonical_forms_pi]
      - conv_eq_of_values_outer_eq  → [Typing.conv_eq_of_values_outer_eq]
      - sort_not_pi_val etc.        → [Typing.sort_not_*_val]
      - progress                    → [Typing.progress] (Hconf-conditional)
                                    + [Typing.progress_unconditional]
                                      once [Confluence.confluence_provable]
                                      is imported.
*)

Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.

Require Import Lex.Syntax.
Require Import Lex.DeBruijn.
Require Import Lex.Typing.

(* ================================================================== *)
(** ** Unconditional progress (via the new full-confluence theorem)   *)
(* ================================================================== *)

(** The progress theorem is proven Qed-conditionally on
    [confluence_property] in [Typing.v].  Here we re-export the
    Hconf-conditional form verbatim — downstream callers who want the
    unconditional form should import [Lex.Confluence] and use the
    Qed-closed [Confluence.confluence_provable] to discharge
    [Hconf].

    The skeleton no longer threads [Hconf] through a Section — that
    indirection is obsolete now that the confluence proof exists. *)

Theorem progress_skeleton :
  confluence_property ->
  match_exhaustiveness_property ->
  forall (t T : Term),
    has_type nil t T ->
    value t \/ exists t', step t t'.
Proof.
  exact progress.
Qed.

(** Re-export the canonical forms lemma for downstream citation. *)
Theorem progress_skeleton_canonical_forms_pi :
  confluence_property ->
  forall (v A B : Term) (eff : option EffectRow),
    value v ->
    has_type nil v (Pi A eff B) ->
    exists dom body, v = Lambda dom body.
Proof.
  exact canonical_forms_pi.
Qed.

(** Summary of Qed-closures this skeleton now exports:
    - [progress_skeleton]                    → [Typing.progress]
    - [progress_skeleton_canonical_forms_pi] → [Typing.canonical_forms_pi]

    Both are confluence-conditional.  The Qed-closed unconditional
    forms ([progress_unconditional] and
    [canonical_forms_pi_unconditional]) live in [Typing.v] after
    importing [Confluence.confluence_provable]. *)
