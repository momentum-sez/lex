(** * Lex/Typing_progress_skeleton.v — CONDITIONAL progress theorem
                                        (confluence-conditional; NOT unconditional safety)

    HONEST STATUS (read before citing this file as a safety result):

    Progress for the full Lex calculus is NOT proved unconditionally
    here or anywhere in this tree.  The progress theorem in [Typing.v]
    ([Typing.progress]) takes [confluence_property] and
    [match_exhaustiveness_property] as SECTION/THEOREM HYPOTHESES; it
    is a conditional (Qed-closed-modulo-hypotheses) result, not a
    delivered type-safety theorem.

    Confluence is OPEN.  The step relation now carries full binder
    congruence (see [Typing.v]'s [step] inductive), which repairs the
    pre-G1 [step] relation under which confluence was provably FALSE
    (the Qed-closed refutation [confluence_property_refuted] in
    [ConfluenceCounterexampleArchive.v]).  But repairing the relation
    is not the same as proving confluence: [Confluence.v] proves only
    the parallel-reduction embeddings ([par_refl], [step_implies_par],
    [par_implies_steps]) and the COMPOSITION theorem
    [confluence_from_par_star_diamond : par_star_diamond_spec ->
    confluence_spec].  The substantive diamond lemma
    [par_diamond_spec] (and hence [par_star_diamond_spec]) is left as
    an OPEN [Prop] specification — the Tait-Martin-Löf double induction
    is not mechanized.  Therefore [confluence_property] is an
    UNDISCHARGED hypothesis, and progress is conditional on it.

    This file historically served as a staging ground for breaking the
    monolithic [progress] placeholder at [Typing.v]:708 into structured
    named lemmas.  It re-exports the conditional progress and
    canonical-forms theorems verbatim, preserving the
    [confluence_property] hypothesis (it cannot be dropped — the
    hypothesis is undischarged).

    Historic references (each discharged as Qed in [Typing.v] or
    [Confluence.v] EXCEPT where noted):
      - canonical_forms_pi          → [Typing.canonical_forms_pi]
                                      (confluence-conditional: takes
                                       [confluence_property])
      - conv_eq_of_values_outer_eq  → [Typing.conv_eq_of_values_outer_eq]
      - sort_not_pi_val etc.        → [Typing.sort_not_*_val]
      - progress                    → [Typing.progress] (confluence- and
                                       match-exhaustiveness-conditional)

    NOTE: there is NO [Confluence.confluence_provable],
    [Typing.progress_unconditional], or
    [Typing.canonical_forms_pi_unconditional] artifact.  Earlier
    revisions of this header referred to such "unconditional" forms as
    if they existed; they do not, because confluence is not proved.
    The only honest forms are the confluence-conditional theorems below.
*)

Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.

Require Import Lex.Syntax.
Require Import Lex.DeBruijn.
Require Import Lex.Typing.

(* ================================================================== *)
(** ** Conditional progress (re-export; confluence hypothesis OPEN)    *)
(* ================================================================== *)

(** The progress theorem is proven Qed-conditionally on
    [confluence_property] and [match_exhaustiveness_property] in
    [Typing.v].  Here we re-export that conditional form verbatim — the
    [confluence_property] hypothesis CANNOT be discharged, because
    confluence is not proved ([par_diamond_spec] in [Confluence.v] is
    an open [Prop] spec).  There is no unconditional form to fall back
    to.  Any caller wanting an unconditional progress theorem must
    first close the open diamond lemma and instantiate
    [Confluence.confluence_from_par_star_diamond]. *)

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

(** Summary of Qed-closures this skeleton exports (each
    confluence-conditional — i.e. takes [confluence_property] as an
    undischarged hypothesis):
    - [progress_skeleton]                    → [Typing.progress]
    - [progress_skeleton_canonical_forms_pi] → [Typing.canonical_forms_pi]

    There are NO unconditional forms.  [progress_unconditional] and
    [canonical_forms_pi_unconditional] do not exist, and
    [Confluence.confluence_provable] does not exist, because confluence
    is open at the diamond-lemma level.  Closing the open
    [par_diamond_spec] would let
    [Confluence.confluence_from_par_star_diamond] discharge the
    [confluence_property] hypothesis and yield unconditional forms;
    until then these theorems are conditional. *)
