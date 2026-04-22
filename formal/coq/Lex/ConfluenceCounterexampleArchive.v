(** * Lex/ConfluenceCounterexampleArchive.v — Archived B4 refutation content
 *
 * ARCHIVE STATUS: G1 supplanted this file with a positive parallel-
 * reduction scaffold (Confluence.v in trunk).  This archive preserves
 * the concrete 4-term counterexample [CE_t / CE_u1 / CE_u2] that
 * witnessed [confluence_property is FALSE] under the pre-G1 step
 * relation, because the counterexample is Qed-closed evidence of why
 * the step relation needed repairing.
 *
 * NOT in _CoqProject: compiled alongside Confluence.v it would collide
 * on shared lemma names (par, par_refl, step_implies_par, etc.).
 * Preserved as reference source only.
 *
 * Original file header follows.
 *)

(** * Lex/Confluence.v — Confluence analysis for the Lex step relation

    STATUS SUMMARY (read before any "why wasn't this closed" question):

    The [confluence_property] in [Typing.v] is the classical
    Church-Rosser statement:

        forall t u1 u2, steps t u1 -> steps t u2 ->
                        exists v, steps u1 v /\ steps u2 v.

    For the [step] inductive in [Typing.v] this statement is
    DEMONSTRABLY FALSE.  The calculus has a congruence rule
    [step_app_arg] that permits argument reduction BEFORE a
    [step_beta], but it has NO congruence under binders (no
    reduction under [Lambda], [Pi], [Let], etc.).  This asymmetry
    creates genuinely non-joinable divergences inside well-typed
    terms.

    A concrete counterexample is proven below as
    [confluence_property_refuted]:

      starting term
        t = App (Lambda T (Lambda T' (App (Var 1) (Var 0))))
                (Annot (Var 0) T)

      Path 1 (step_beta first, then stuck under the inner Lambda):
        t → Lambda T' (App (Annot (Var 1) T') (Var 0))

      Path 2 (step_app_arg via step_annot, then step_beta):
        t → Lambda T' (App (Var 1) (Var 0))

      Both results are values (Lambda _ _), so neither steps further,
      and they are syntactically distinct — no joint reduct exists.

    Hence [confluence_property] cannot be closed with [Qed].  Any
    claim of a full Qed-closed confluence would be a bug.

    STRUCTURE OF THIS FILE:

    Section 1: [confluence_property_refuted] — a Qed-closed proof
               that the full Church-Rosser property is false for the
               current [step] relation.  This forecloses any
               well-intentioned later attempt to mechanically close
               the false statement.

    Section 2: One-sided conv_eq inversion lemmas (Qed-closed, no
               hypotheses).  If [conv_eq v T] with [v] a value, then
               [T →* v].  Specialisations for TSort, Pi, Lambda, Var,
               Constant.

    Section 3: Value-shape disjointness (Qed-closed, pigeon-hole on
               value constructors).  [~ conv_eq (TSort s) (Pi _ _ _)]
               and friends.

    Section 4: Degenerate [confluence_values_only] corollary —
               Qed-trivial, documents the restricted form we can close.

    Section 5: Untypability of [Var] / [Constant] in the empty context
               (Qed-closed, copied from the skeleton for a
               self-contained Confluence.v).

    Section 6: The downstream target — [canonical_forms_pi_under_confluence_at_values].
               This is the canonical-forms lemma stated under the
               STRICTLY WEAKER hypothesis [confluence_at_values]
               instead of full [confluence_property].  Going from
               full confluence to "confluence-at-values" is a real
               strengthening of the development: the full
               confluence statement is false, but
               confluence-at-values may still be true for this
               calculus (we conjecture it holds, though the
               counterexample above refutes full confluence).

               The downstream skeleton can be refactored to thread
               [confluence_at_values] instead of [confluence_property]
               through [canonical_forms_pi] / [progress] / etc.,
               giving a cleaner (and actually-provable) dependency.

    What this file does NOT do:
      - It does NOT close [confluence_property] itself.  That
        statement is false; no Qed-closed proof is possible.
      - It does NOT admit any proof.  Every [Theorem] / [Lemma]
        below ends in [Qed].
      - It does NOT introduce any new [Axiom] at the top level.
        (The weaker [confluence_at_values] is expressed as a
        [Prop]-level [Definition] that downstream callers take as a
        [Hypothesis].)
*)

From Stdlib Require Import Arith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Strings.String.
Import ListNotations.

Require Import Lex.Syntax.
Require Import Lex.DeBruijn.
Require Import Lex.Typing.

(* ================================================================== *)
(** ** Section 1: The counterexample — why confluence_property fails   *)
(* ================================================================== *)

(** We exhibit a concrete term [CE_t] and two step-paths that
    cannot be joined.  The [step_beta] / [step_app_arg] choice,
    combined with the absence of a congruence rule under [Lambda],
    makes the two resulting Lambdas structurally distinct and
    irreducible.

    Pedagogically, this also tells any future maintainer exactly
    which extension to [step] would make confluence provable: add
    congruence under [Lambda] (and [Pi] / [Let] / etc.) so that
    the two Lambdas above can continue to reduce.  Alternatively,
    remove [step_app_arg] so that reduction is fully head-directed
    and hence deterministic. *)

(** The outer Lambda body, under one binder.  Its body is an inner
    Lambda that references [Var 1] (the outer binding) — giving a
    free occurrence of the outer argument under a binder. *)
Definition CE_outer_body : Term :=
  Lambda (Var 0) (App (Var 1) (Var 0)).

(** The outer Lambda itself.  The domain is irrelevant for the
    counterexample — we use [Var 0] as a placeholder. *)
Definition CE_outer : Term :=
  Lambda (Var 0) CE_outer_body.

(** The argument: an [Annot] so it step-reduces via [step_annot].
    Inner is [Var 0], annotation type is arbitrary ([Var 0] again). *)
Definition CE_arg : Term := Annot (Var 0) (Var 0).
Definition CE_arg' : Term := Var 0.  (* reduct of CE_arg via step_annot *)

(** The starting term. *)
Definition CE_t : Term := App CE_outer CE_arg.

(** Path 1: direct [step_beta] on the outer App. *)
Definition CE_u1 : Term := subst 0 CE_arg CE_outer_body.

(** Path 2: first [step_app_arg] (reducing the Annot to its inner),
    then [step_beta]. *)
Definition CE_u2 : Term := subst 0 CE_arg' CE_outer_body.

Lemma CE_path1_step : step CE_t CE_u1.
Proof.
  unfold CE_t, CE_outer, CE_u1.
  apply step_beta.
Qed.

Lemma CE_path1_full : steps CE_t CE_u1.
Proof.
  eapply steps_trans.
  - apply CE_path1_step.
  - apply steps_refl.
Qed.

Lemma CE_path2_step1 : step CE_t (App CE_outer CE_arg').
Proof.
  unfold CE_t, CE_arg, CE_arg'.
  apply step_app_arg. apply step_annot.
Qed.

Lemma CE_path2_step2 : step (App CE_outer CE_arg') CE_u2.
Proof.
  unfold CE_outer, CE_u2. apply step_beta.
Qed.

Lemma CE_path2 : steps CE_t CE_u2.
Proof.
  eapply steps_trans.
  - apply CE_path2_step1.
  - eapply steps_trans.
    + apply CE_path2_step2.
    + apply steps_refl.
Qed.

(** Both reducts are values (Lambdas). *)

Lemma CE_u1_is_value : value CE_u1.
Proof.
  unfold CE_u1, CE_outer_body. simpl. constructor.
Qed.

Lemma CE_u2_is_value : value CE_u2.
Proof.
  unfold CE_u2, CE_outer_body. simpl. constructor.
Qed.

(** The two reducts are syntactically distinct — their Lambda
    bodies embed different substituted arguments (Annot-wrapped vs
    stripped).  We prove this by exhibiting [CE_u1] and [CE_u2] in
    a form that [simpl] reduces and then discriminating. *)
Lemma CE_u1_neq_u2 : CE_u1 <> CE_u2.
Proof.
  unfold CE_u1, CE_u2, CE_outer_body, CE_arg, CE_arg'.
  simpl. intro H. inversion H.
Qed.

(** The counterexample theorem.  Combined with [value_no_step] and
    [value_steps_eq] this rules out the existence of any common
    reduct of [CE_u1] and [CE_u2]. *)
Theorem confluence_property_refuted :
  ~ confluence_property.
Proof.
  intro Hconf.
  specialize (Hconf CE_t CE_u1 CE_u2 CE_path1_full CE_path2) as [v [H1 H2]].
  (* CE_u1 is a value so steps CE_u1 v gives v = CE_u1 *)
  assert (Hv1 : v = CE_u1).
  { eapply value_steps_eq.
    - apply CE_u1_is_value.
    - exact H1. }
  (* CE_u2 is a value so steps CE_u2 v gives v = CE_u2 *)
  assert (Hv2 : v = CE_u2).
  { eapply value_steps_eq.
    - apply CE_u2_is_value.
    - exact H2. }
  (* But then CE_u1 = CE_u2, contradicting CE_u1_neq_u2 *)
  apply CE_u1_neq_u2. rewrite <- Hv1. exact Hv2.
Qed.

(* ================================================================== *)
(** ** Section 2: Conv-eq inversion lemmas (no confluence needed)      *)
(* ================================================================== *)

(** The [conv_eq] definition in [Typing.v] bakes in that the common
    reduct of the two sides must be a VALUE.  That value constraint
    is why one-sided inversions (when one of the sides is already a
    value) can be closed without any confluence result: the common
    reduct is forced to equal the value side. *)

(** Generic form: if the left side is a value, the right side
    multi-steps to that exact value. *)
Lemma conv_eq_value_right_reduces :
  forall (v T : Term),
    value v ->
    conv_eq v T ->
    steps T v.
Proof.
  intros v T Hval [w [HvW [HTw _]]].
  assert (HvW_eq : w = v) by (eapply value_steps_eq; eassumption).
  subst w. exact HTw.
Qed.

(** The companion lemma, with the value on the right instead of
    the left. *)
Lemma conv_eq_value_left_reduces :
  forall (T v : Term),
    value v ->
    conv_eq T v ->
    steps T v.
Proof.
  intros T v Hval Hconv.
  apply conv_eq_sym in Hconv.
  eapply conv_eq_value_right_reduces; eassumption.
Qed.

(** Specialization: TSort. *)
Lemma conv_eq_TSort_right_reduces :
  forall (s : Sort) (T : Term),
    conv_eq (TSort s) T ->
    steps T (TSort s).
Proof.
  intros s T Hconv.
  eapply conv_eq_value_right_reduces.
  - constructor.
  - exact Hconv.
Qed.

(** Specialization: Pi. *)
Lemma conv_eq_Pi_right_reduces :
  forall (A : Term) (eff : option EffectRow) (B T : Term),
    conv_eq (Pi A eff B) T ->
    steps T (Pi A eff B).
Proof.
  intros A eff B T Hconv.
  eapply conv_eq_value_right_reduces.
  - constructor.
  - exact Hconv.
Qed.

(** Specialization: Lambda. *)
Lemma conv_eq_Lambda_right_reduces :
  forall (dom body T : Term),
    conv_eq (Lambda dom body) T ->
    steps T (Lambda dom body).
Proof.
  intros dom body T Hconv.
  eapply conv_eq_value_right_reduces.
  - constructor.
  - exact Hconv.
Qed.

(** Specialization: Var. *)
Lemma conv_eq_Var_right_reduces :
  forall (i : nat) (T : Term),
    conv_eq (Var i) T ->
    steps T (Var i).
Proof.
  intros i T Hconv.
  eapply conv_eq_value_right_reduces.
  - constructor.
  - exact Hconv.
Qed.

(** Specialization: Constant. *)
Lemma conv_eq_Constant_right_reduces :
  forall (c : string) (T : Term),
    conv_eq (Constant c) T ->
    steps T (Constant c).
Proof.
  intros c T Hconv.
  eapply conv_eq_value_right_reduces.
  - constructor.
  - exact Hconv.
Qed.

(** Left-side specialisations.  Proof is by [conv_eq_sym] then the
    right-reducing form. *)

Lemma conv_eq_TSort_left_reduces :
  forall (T : Term) (s : Sort),
    conv_eq T (TSort s) ->
    steps T (TSort s).
Proof.
  intros T s Hconv.
  apply conv_eq_value_left_reduces; [constructor | exact Hconv].
Qed.

Lemma conv_eq_Pi_left_reduces :
  forall (T A : Term) (eff : option EffectRow) (B : Term),
    conv_eq T (Pi A eff B) ->
    steps T (Pi A eff B).
Proof.
  intros T A eff B Hconv.
  apply conv_eq_value_left_reduces; [constructor | exact Hconv].
Qed.

Lemma conv_eq_Lambda_left_reduces :
  forall (T dom body : Term),
    conv_eq T (Lambda dom body) ->
    steps T (Lambda dom body).
Proof.
  intros T dom body Hconv.
  apply conv_eq_value_left_reduces; [constructor | exact Hconv].
Qed.

(** If both sides of [conv_eq] are values, they are syntactically
    equal.  (Re-proven here so Confluence.v is self-contained.) *)
Lemma conv_eq_values_eq :
  forall (v1 v2 : Term),
    value v1 -> value v2 -> conv_eq v1 v2 -> v1 = v2.
Proof.
  intros v1 v2 Hv1 Hv2 [w [Hs1 [Hs2 _]]].
  assert (Hw1 : w = v1) by (eapply value_steps_eq; eassumption).
  assert (Hw2 : w = v2) by (eapply value_steps_eq; eassumption).
  rewrite <- Hw1. rewrite <- Hw2. reflexivity.
Qed.

(* ================================================================== *)
(** ** Section 3: Value-shape pigeon lemmas                            *)
(* ================================================================== *)

(** These "pigeon" lemmas rule out two distinct value constructors
    standing in a [conv_eq] relation.  They do NOT require
    confluence — both sides are already values, so [conv_eq] forces
    equality, and equality rules out cross-constructor cases by
    simple discrimination. *)

Lemma conv_eq_TSort_Pi_impossible :
  forall (s : Sort) (A : Term) (eff : option EffectRow) (B : Term),
    ~ conv_eq (TSort s) (Pi A eff B).
Proof.
  intros s A eff B Hconv.
  pose proof (conv_eq_values_eq (TSort s) (Pi A eff B)
              (value_sort s) (value_pi A eff B) Hconv) as Heq.
  discriminate.
Qed.

Lemma conv_eq_TSort_Lambda_impossible :
  forall (s : Sort) (dom body : Term),
    ~ conv_eq (TSort s) (Lambda dom body).
Proof.
  intros s dom body Hconv.
  pose proof (conv_eq_values_eq (TSort s) (Lambda dom body)
              (value_sort s) (value_lambda dom body) Hconv) as Heq.
  discriminate.
Qed.

Lemma conv_eq_Pi_Lambda_impossible :
  forall (A : Term) (eff : option EffectRow) (B dom body : Term),
    ~ conv_eq (Pi A eff B) (Lambda dom body).
Proof.
  intros A eff B dom body Hconv.
  pose proof (conv_eq_values_eq (Pi A eff B) (Lambda dom body)
              (value_pi A eff B) (value_lambda dom body) Hconv) as Heq.
  discriminate.
Qed.

(** Symmetric forms. *)
Lemma conv_eq_Pi_TSort_impossible :
  forall (A : Term) (eff : option EffectRow) (B : Term) (s : Sort),
    ~ conv_eq (Pi A eff B) (TSort s).
Proof.
  intros A eff B s Hconv.
  apply (conv_eq_TSort_Pi_impossible s A eff B).
  apply conv_eq_sym. exact Hconv.
Qed.

Lemma conv_eq_Lambda_TSort_impossible :
  forall (dom body : Term) (s : Sort),
    ~ conv_eq (Lambda dom body) (TSort s).
Proof.
  intros dom body s Hconv.
  apply (conv_eq_TSort_Lambda_impossible s dom body).
  apply conv_eq_sym. exact Hconv.
Qed.

Lemma conv_eq_Lambda_Pi_impossible :
  forall (dom body A : Term) (eff : option EffectRow) (B : Term),
    ~ conv_eq (Lambda dom body) (Pi A eff B).
Proof.
  intros dom body A eff B Hconv.
  apply (conv_eq_Pi_Lambda_impossible A eff B dom body).
  apply conv_eq_sym. exact Hconv.
Qed.

(* ================================================================== *)
(** ** Section 4: Confluence for values (degenerate — Qed-trivial)     *)
(* ================================================================== *)

(** The "types only" fallback from the task prompt, specialised to
    [is_type T := value T].  Since a value only steps to itself,
    confluence starting from a value is trivially joinable at the
    value itself. *)

Theorem confluence_values_only :
  forall (t u1 u2 : Term),
    value t ->
    steps t u1 ->
    steps t u2 ->
    exists v, steps u1 v /\ steps u2 v.
Proof.
  intros t u1 u2 Hval Hs1 Hs2.
  assert (Hu1 : u1 = t) by (eapply value_steps_eq; eassumption).
  assert (Hu2 : u2 = t) by (eapply value_steps_eq; eassumption).
  subst u1 u2.
  exists t. split; apply steps_refl.
Qed.

(* ================================================================== *)
(** ** Section 5: Untypability helpers (self-contained copies)         *)
(* ================================================================== *)

Lemma var_nil_untypable_unconditional : forall (i : nat) (T : Term),
  has_type nil (Var i) T -> False.
Proof.
  intros i T Hty.
  remember nil as ctx eqn:Hctx in Hty.
  remember (Var i) as t eqn:Ht in Hty.
  induction Hty; inversion Ht; subst; try discriminate.
  all: try (eapply IHHty; reflexivity).
Qed.

Lemma constant_nil_untypable_unconditional : forall (c : string) (T : Term),
  has_type nil (Constant c) T -> False.
Proof.
  intros c T Hty.
  remember nil as ctx eqn:Hctx in Hty.
  remember (Constant c) as t eqn:Ht in Hty.
  induction Hty; inversion Ht; subst; try discriminate.
  all: try (eapply IHHty; reflexivity).
Qed.

(* ================================================================== *)
(** ** Section 6: Confluence-at-values — a WEAKER, SEPARATELY TRACKED  *)
(** **            hypothesis that suffices for canonical_forms_pi      *)
(* ================================================================== *)

(** The full [confluence_property] is false (Section 1).  But the
    uses of [Hconf] in [Typing_progress_skeleton.v] only need a
    strictly weaker form: given two value reducts of the same term,
    are they equal?  We call this [confluence_at_values] and track
    it as a separate [Prop]-level hypothesis. *)

(** Formal statement.  Strictly weaker than [confluence_property]:
    instead of demanding a common reduct for any two paths, we only
    demand EQUALITY of reducts when both paths terminate at
    values.  Since values do not step, the value constraint is
    where the confluence reasoning bottoms out. *)
Definition confluence_at_values : Prop :=
  forall (t v1 v2 : Term),
    value v1 -> value v2 ->
    steps t v1 -> steps t v2 ->
    v1 = v2.

(** Is [confluence_at_values] consistent with our counterexample?

    Yes — the counterexample [CE_t] terminates at TWO distinct
    values [CE_u1] and [CE_u2].  So [confluence_at_values] is ALSO
    FALSE for this [step] relation.  We prove this below, for
    symmetry with [confluence_property_refuted]. *)

Theorem confluence_at_values_refuted :
  ~ confluence_at_values.
Proof.
  intros Hconf.
  specialize (Hconf CE_t CE_u1 CE_u2
                CE_u1_is_value CE_u2_is_value
                CE_path1_full CE_path2) as Heq.
  apply CE_u1_neq_u2. exact Heq.
Qed.

(** Corollary: even the weaker [confluence_at_values] is not
    Qed-closable for this calculus.  Both [confluence_property] and
    [confluence_at_values] can only be recovered by changing the
    [step] relation — either by adding congruence rules under
    binders (closing the joinability of the divergent paths) or by
    removing [step_app_arg] (making reduction strictly head-directed
    and hence deterministic). *)

(* ================================================================== *)
(** ** Section 7: Confluence-at-value-reducts as a MODULE-TYPE         *)
(** **            hypothesis threaded through downstream proofs        *)
(* ================================================================== *)

(** Since full confluence is false and "confluence at values" is
    also false for the current [step] relation, we cannot close
    [canonical_forms_pi] as an unconditional [Theorem].  What we
    CAN do is:

      (a) Document the exact hypothesis the downstream needs
          ([confluence_at_values] above).

      (b) Provide a Section-local proof of
          [canonical_forms_pi_under_confluence_at_values] that
          closes with [Qed] under the explicit hypothesis.  This
          shows the downstream is dischargeable once confluence is
          restored (e.g., by adding congruence under binders to
          [step]).

      (c) Prove the specific conv_eq inversions that the
          downstream uses, so the only remaining dependency is the
          confluence-at-values hypothesis itself.

    The Section wrapper makes the hypothesis explicit — anyone
    importing the theorem must either supply the hypothesis or
    accept that the theorem is conditional. *)

Section CanonicalFormsPiUnderConfluenceAtValues.

  Hypothesis Hconf_values : confluence_at_values.

  (** Intermediate: if A →* type_level n (a value) and conv_eq A T,
      then T →* type_level n. *)
  Lemma steps_to_sort_through_conv_eq :
    forall (n : nat) (A T : Term),
      steps A (type_level n) ->
      conv_eq A T ->
      steps T (type_level n).
  Proof.
    intros n A T HAsort [w [HAw [HTw Hw]]].
    (* We have A →* type_level n (a value) and A →* w (a value). *)
    (* By confluence_at_values, type_level n = w. *)
    pose proof (Hconf_values A (type_level n) w
                  (value_sort (SType (LNat n)))
                  Hw
                  HAsort HAw) as Heq.
    rewrite <- Heq in HTw. exact HTw.
  Qed.

  (** Under [confluence_at_values], [has_type nil (TSort s) T]
      implies T multi-steps to some type_level. *)
  Lemma has_type_nil_TSort_T_steps_type_level :
    forall (s : Sort) (T : Term),
      has_type nil (TSort s) T ->
      exists n, steps T (type_level n).
  Proof.
    intros s T Hty.
    remember nil as ctx eqn:Hctx in Hty.
    remember (TSort s) as t eqn:Ht in Hty.
    induction Hty; inversion Ht; subst; try discriminate.
    - (* T_Type *) exists (S n). unfold type_level. apply steps_refl.
    - (* T_Prop *) exists 1. unfold type_level. apply steps_refl.
    - (* T_Rule *) exists (S n). unfold type_level. apply steps_refl.
    - (* T_Time0 *) exists 0. unfold type_level. apply steps_refl.
    - (* T_Time1 *) exists 0. unfold type_level. apply steps_refl.
    - (* T_Conv *)
      specialize (IHHty eq_refl eq_refl) as [n IH].
      (* IH: steps A (type_level n).  H: conv_eq A T. *)
      exists n. eapply steps_to_sort_through_conv_eq; eassumption.
  Qed.

  (** Under [confluence_at_values], [has_type nil (Pi _ _ _) T]
      implies T multi-steps to some type_level. *)
  Lemma has_type_nil_Pi_T_steps_type_level :
    forall (dom : Term) (eff_dom : option EffectRow) (cod T : Term),
      has_type nil (Pi dom eff_dom cod) T ->
      exists n, steps T (type_level n).
  Proof.
    intros dom eff_dom cod T Hty.
    remember nil as ctx eqn:Hctx in Hty.
    remember (Pi dom eff_dom cod) as t eqn:Ht in Hty.
    induction Hty; inversion Ht; subst; try discriminate.
    - (* T_Pi *) exists (Nat.max i j).
      unfold type_level. apply steps_refl.
    - (* T_Conv *)
      specialize (IHHty eq_refl eq_refl) as [n IH].
      exists n. eapply steps_to_sort_through_conv_eq; eassumption.
  Qed.

  (** Canonical forms at Pi: any value typed as [Pi A eff B] in the
      empty context must be a [Lambda].

      This is the downstream target.  It closes with [Qed] under
      the [confluence_at_values] hypothesis. *)
  Theorem canonical_forms_pi_under_confluence_at_values :
    forall (v A B : Term) (eff : option EffectRow),
      value v ->
      has_type nil v (Pi A eff B) ->
      exists dom body, v = Lambda dom body.
  Proof.
    intros v A B eff Hval Hty.
    inversion Hval; subst.
    - (* v = TSort s *)
      exfalso.
      destruct (has_type_nil_TSort_T_steps_type_level s (Pi A eff B) Hty)
        as [n Hsteps].
      (* steps (Pi A eff B) (type_level n), but Pi is a value. *)
      assert (Heq : type_level n = Pi A eff B).
      { eapply value_steps_eq;
        [exact (value_pi A eff B) | exact Hsteps]. }
      unfold type_level in Heq. discriminate.
    - (* v = Lambda *) exists dom, body. reflexivity.
    - (* v = Pi _ _ _ *)
      exfalso.
      destruct (has_type_nil_Pi_T_steps_type_level dom eff0 cod
                  (Pi A eff B) Hty) as [n Hsteps].
      assert (Heq : type_level n = Pi A eff B).
      { eapply value_steps_eq;
        [exact (value_pi A eff B) | exact Hsteps]. }
      unfold type_level in Heq. discriminate.
    - (* v = Var *) exfalso.
      eapply var_nil_untypable_unconditional. exact Hty.
    - (* v = Constant *) exfalso.
      eapply constant_nil_untypable_unconditional. exact Hty.
  Qed.

End CanonicalFormsPiUnderConfluenceAtValues.

(* ================================================================== *)
(** ** Section 8: Downstream summary                                   *)
(* ================================================================== *)

(** What downstream callers get from this file, and under what
    conditions:

    UNCONDITIONAL (no hypothesis needed):
      - [confluence_property_refuted]
          The full Church-Rosser property is false for Lex's [step].
      - [confluence_at_values_refuted]
          The weaker confluence-at-values is ALSO false.
      - [conv_eq_value_right_reduces] / _left_reduces
          and specialisations for TSort / Pi / Lambda / Var / Constant.
      - [conv_eq_values_eq]
          Two values that are conv_eq are syntactically equal.
      - [conv_eq_TSort_Pi_impossible] and similar disjointness
          lemmas.
      - [confluence_values_only]
          Trivial confluence when the starting term is already a value.
      - [var_nil_untypable_unconditional] / [constant_nil_untypable_unconditional]
          Empty-context untypability of free variables / constants.

    CONDITIONAL on [Hconf_values : confluence_at_values] (strictly
    weaker than full [confluence_property]):
      - [canonical_forms_pi_under_confluence_at_values]
          The canonical-forms lemma for Pi types.

    MIGRATION PATH to an unconditional [canonical_forms_pi]:
      1. Modify [step] in Typing.v to add congruence rules under
         [Lambda] / [Pi] / [Sigma] / [Let] / [Rec] / [Match] /
         [Defeasible] / [Modal*] / etc.  (Alternatively: remove
         [step_app_arg] so reduction is strictly head-directed.)
      2. Re-verify that [confluence_property_refuted] still holds.
         If the counterexample is closed by the new congruence
         rules, the counterexample proof will fail — that is the
         signal to delete it and prove [confluence_property]
         directly via Tait–Martin-Löf parallel reduction.
      3. Discharge [Hconf_values] from
         [canonical_forms_pi_under_confluence_at_values] and make
         the theorem unconditional.
*)
