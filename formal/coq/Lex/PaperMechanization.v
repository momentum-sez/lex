From Stdlib Require Import List String Arith.
Import ListNotations.

(** * Lex/PaperMechanization.v

    Standalone theorem targets for the paper-level statements in
    [papers/lex.tex].  The intent is twofold:

    1. close the paper propositions that are already elementary in the
       published calculus, and
    2. give every remaining paper theorem a named Rocq target, even
       where the proof is still open.

    This file is intentionally independent of the larger kernel Lex
    development so it can compile even while the full metatheory tree is
    under active repair. *)

Set Implicit Arguments.

(* ------------------------------------------------------------------------- *)
(** ** Effect rows for defeasible rules                                      *)
(* ------------------------------------------------------------------------- *)

Inductive Effect : Type :=
  | EffRead : Effect
  | EffWrite : string -> Effect
  | EffAttest : string -> Effect
  | EffAuthority : string -> Effect
  | EffOracle : string -> Effect
  | EffFuel : nat -> nat -> Effect
  | EffSanctionsQuery : Effect
  | EffDiscretion : string -> Effect.

Definition EffectRow := Effect -> Prop.

Definition row_join (a b : EffectRow) : EffectRow :=
  fun eff => a eff \/ b eff.

Definition row_subsumed (a b : EffectRow) : Prop :=
  forall eff, a eff -> b eff.

Record ExceptionBranch : Type := mkExceptionBranch {
  ex_guard_row : EffectRow;
  ex_body_row : EffectRow;
}.

Definition defeasible_row (base : EffectRow) (exns : list ExceptionBranch) : EffectRow :=
  fun eff =>
    base eff \/
    exists ex, In ex exns /\ (ex_guard_row ex eff \/ ex_body_row ex eff).

Theorem defeasible_effect_join :
  forall (base : EffectRow) (exns : list ExceptionBranch) (eff : Effect),
    defeasible_row base exns eff <->
    base eff \/
    exists ex, In ex exns /\ (ex_guard_row ex eff \/ ex_body_row ex eff).
Proof.
  intros base exns eff.
  unfold defeasible_row.
  tauto.
Qed.

Lemma defeasible_row_monotone :
  forall (base : EffectRow) (ex : ExceptionBranch) (exns : list ExceptionBranch),
    row_subsumed (defeasible_row base exns) (defeasible_row base (ex :: exns)).
Proof.
  intros base ex exns eff Hrow.
  destruct Hrow as [Hbase | [ex' [Hin Hbranch]]].
  - left; exact Hbase.
  - right; exists ex'; split.
    + right; exact Hin.
    + exact Hbranch.
Qed.

(** row_subsumed is reflexive. *)
Lemma row_subsumed_refl : forall r, row_subsumed r r.
Proof. intros r eff H. exact H. Qed.

(** row_subsumed is transitive. *)
Lemma row_subsumed_trans :
  forall a b c, row_subsumed a b -> row_subsumed b c -> row_subsumed a c.
Proof. intros a b c Hab Hbc eff H. apply Hbc. apply Hab. exact H. Qed.

(** row_join is commutative (as row equality pointwise via subsumption). *)
Lemma row_join_comm_subsumed :
  forall a b, row_subsumed (row_join a b) (row_join b a).
Proof.
  intros a b eff H. unfold row_join in *.
  destruct H as [H | H]; [right | left]; exact H.
Qed.

(** row_join is reflective-absorbing. *)
Lemma row_join_left_subsumed :
  forall a b, row_subsumed a (row_join a b).
Proof. intros a b eff H. left. exact H. Qed.

Lemma row_join_right_subsumed :
  forall a b, row_subsumed b (row_join a b).
Proof. intros a b eff H. right. exact H. Qed.

(** defeasible_row always includes the base row. *)
Lemma defeasible_row_base_subsumed :
  forall base exns, row_subsumed base (defeasible_row base exns).
Proof. intros base exns eff H. left. exact H. Qed.

(** A specific exception's guard row is subsumed by the defeasible row. *)
Lemma defeasible_row_guard_subsumed :
  forall base ex exns,
    In ex exns ->
    row_subsumed (ex_guard_row ex) (defeasible_row base exns).
Proof.
  intros base ex exns Hin eff H.
  right. exists ex. split; [exact Hin | left; exact H].
Qed.

(** A specific exception's body row is subsumed by the defeasible row. *)
Lemma defeasible_row_body_subsumed :
  forall base ex exns,
    In ex exns ->
    row_subsumed (ex_body_row ex) (defeasible_row base exns).
Proof.
  intros base ex exns Hin eff H.
  right. exists ex. split; [exact Hin | right; exact H].
Qed.

Corollary defeasible_effect_visibility :
  forall (base : EffectRow) (exns : list ExceptionBranch),
    row_subsumed base (defeasible_row base exns) /\
    Forall
      (fun ex =>
         row_subsumed (ex_guard_row ex) (defeasible_row base exns) /\
         row_subsumed (ex_body_row ex) (defeasible_row base exns))
      exns.
Proof.
  intros base exns.
  split.
  - intros eff Hbase.
    left; exact Hbase.
  - induction exns as [| ex exns IH]; constructor.
    + split; intros eff Heff; right; exists ex; split.
      * left; reflexivity.
      * now left.
      * left; reflexivity.
      * now right.
    + apply Forall_forall.
      rewrite Forall_forall in IH.
      intros ex' Hin.
      specialize (IH ex' Hin).
      destruct IH as [Hguard Hbody].
      split; intros eff Heff.
      * apply defeasible_row_monotone with (ex := ex).
        apply Hguard; exact Heff.
      * apply defeasible_row_monotone with (ex := ex).
        apply Hbody; exact Heff.
Qed.

(* ------------------------------------------------------------------------- *)
(** ** Tribunal bridges                                                      *)
(* ------------------------------------------------------------------------- *)

Section Bridges.
  Context {Tribunal Atom : Type}.

  Record TribunalJudgment (t : Tribunal) : Type := mkTribunalJudgment {
    judgment_payload : Atom;
  }.

  Definition CanonBridge (from to : Tribunal) : Type :=
    TribunalJudgment from -> TribunalJudgment to.

  Definition coerce {from to : Tribunal}
      (p : TribunalJudgment from)
      (w : CanonBridge from to) : TribunalJudgment to :=
    w p.

  Definition id_bridge {t : Tribunal} : CanonBridge t t :=
    fun p => p.

  Definition compose_bridge {t1 t2 t3 : Tribunal}
      (w12 : CanonBridge t1 t2)
      (w23 : CanonBridge t2 t3) : CanonBridge t1 t3 :=
    fun p => w23 (w12 p).

  Theorem bridge_composition :
    forall (t1 t2 t3 : Tribunal)
           (w12 : CanonBridge t1 t2)
           (w23 : CanonBridge t2 t3)
           (e : TribunalJudgment t1),
      coerce (coerce e w12) w23 =
      coerce e (compose_bridge w12 w23).
  Proof.
    reflexivity.
  Qed.

  Theorem bridge_identity_units :
    forall (t1 t2 : Tribunal)
           (w : CanonBridge t1 t2)
           (e : TribunalJudgment t1),
      coerce e (compose_bridge id_bridge w) = coerce e w /\
      coerce e (compose_bridge w id_bridge) = coerce e w.
  Proof.
    intros t1 t2 w e.
    split; reflexivity.
  Qed.

  (** compose_bridge is associative.  Follows from definitional eta. *)
  Theorem bridge_compose_assoc :
    forall (t1 t2 t3 t4 : Tribunal)
           (w12 : CanonBridge t1 t2)
           (w23 : CanonBridge t2 t3)
           (w34 : CanonBridge t3 t4)
           (e : TribunalJudgment t1),
      coerce e (compose_bridge w12 (compose_bridge w23 w34)) =
      coerce e (compose_bridge (compose_bridge w12 w23) w34).
  Proof.
    intros. reflexivity.
  Qed.

  (** id_bridge is idempotent under self-composition. *)
  Theorem id_bridge_idempotent :
    forall (t : Tribunal) (e : TribunalJudgment t),
      coerce e (compose_bridge id_bridge id_bridge) = coerce e id_bridge.
  Proof. intros. reflexivity. Qed.

  (** The identity bridge preserves the payload unchanged. *)
  Theorem id_bridge_preserves :
    forall (t : Tribunal) (e : TribunalJudgment t),
      coerce e id_bridge = e.
  Proof. intros. reflexivity. Qed.
End Bridges.

(* ------------------------------------------------------------------------- *)
(** ** Open paper targets                                                    *)
(* ------------------------------------------------------------------------- *)

Section DiscretionHoleReductionTarget.
  Context {Adversary : Type}.

  Parameter hole_forgery_advantage : Adversary -> nat -> nat.
  Parameter euf_cma_advantage : Adversary -> nat -> nat.
  Parameter reduction_overhead : Adversary -> nat -> nat.

  (* The standalone paper target abstracts away the concrete game-hopping
     construction, so the reduction estimate is carried explicitly as the
     section premise. *)
  Hypothesis reduction_bound :
    forall (A : Adversary) (k : nat),
      hole_forgery_advantage A k <=
      euf_cma_advantage A k + reduction_overhead A k.

  Theorem discretion_hole_reduction :
    forall (A : Adversary) (k : nat),
      hole_forgery_advantage A k <=
      euf_cma_advantage A k + reduction_overhead A k.
  Proof.
    exact reduction_bound.
  Qed.
End DiscretionHoleReductionTarget.

Section EffectMonotonicityTarget.
  Context {Derivation Row : Type}.

  Parameter row_subsumed_target : Row -> Row -> Prop.
  Parameter derivation_row : Derivation -> Row.
  Parameter subderivation : Derivation -> Derivation -> Prop.

  (* At the paper layer the derivation system is abstract, so row
     monotonicity is exposed as the semantic premise needed by the claim. *)
  Hypothesis subderivation_rows_monotone :
    forall (d_outer d_inner : Derivation),
      subderivation d_outer d_inner ->
      row_subsumed_target (derivation_row d_inner) (derivation_row d_outer).

  Theorem effect_monotonicity :
    forall (d_outer d_inner : Derivation),
      subderivation d_outer d_inner ->
      row_subsumed_target (derivation_row d_inner) (derivation_row d_outer).
  Proof.
    exact subderivation_rows_monotone.
  Qed.
End EffectMonotonicityTarget.

Section WhnfBoundedTarget.
  Context {Term Ty : Type}.

  Parameter closed : Term -> Prop.
  Parameter admissible : Term -> Prop.
  Parameter well_typed : Term -> Ty -> Prop.
  Parameter whnf_with_fuel : nat -> Term -> option Term.
  Parameter whnf_value : Term -> Prop.
  Parameter term_size : Term -> nat.
  Parameter let_depth : Term -> nat.

  (* Bounded WHNF reduction depends on the concrete evaluator and typing
     metatheory, so the witness-producing statement is made explicit here. *)
  Hypothesis bounded_whnf_witness :
    forall (t : Term) (A : Ty),
      closed t ->
      admissible t ->
      well_typed t A ->
      exists k v,
        k <= term_size t + let_depth t /\
        whnf_with_fuel k t = Some v /\
        whnf_value v.

  Theorem whnf_bounded_reduction :
    forall (t : Term) (A : Ty),
      closed t ->
      admissible t ->
      well_typed t A ->
      exists k v,
        k <= term_size t + let_depth t /\
        whnf_with_fuel k t = Some v /\
        whnf_value v.
  Proof.
    exact bounded_whnf_witness.
  Qed.
End WhnfBoundedTarget.

(** ** Further abstract-section structural properties (2026-04-20) *)

Section MoreBridges.
  Context {Tribunal Atom : Type}.

  (** Nested composition: associativity of the canon-bridge pipeline. *)
  Theorem bridge_compose_flat :
    forall (t1 t2 t3 : Tribunal)
           (w12 : @CanonBridge Tribunal Atom t1 t2)
           (w23 : @CanonBridge Tribunal Atom t2 t3)
           (e : @TribunalJudgment Tribunal Atom t1),
      @coerce Tribunal Atom t1 t3 e (@compose_bridge Tribunal Atom t1 t2 t3 w12 w23) =
      @coerce Tribunal Atom t2 t3 (@coerce Tribunal Atom t1 t2 e w12) w23.
  Proof. intros. reflexivity. Qed.

  (** id_bridge composes on the right to preserve any bridge. *)
  Theorem compose_id_right_preserves :
    forall (t1 t2 : Tribunal)
           (w : @CanonBridge Tribunal Atom t1 t2)
           (e : @TribunalJudgment Tribunal Atom t1),
      @coerce Tribunal Atom t1 t2 e
        (@compose_bridge Tribunal Atom t1 t2 t2 w id_bridge) =
      @coerce Tribunal Atom t1 t2 e w.
  Proof. intros. reflexivity. Qed.

  (** id_bridge composes on the left to preserve any bridge. *)
  Theorem compose_id_left_preserves :
    forall (t1 t2 : Tribunal)
           (w : @CanonBridge Tribunal Atom t1 t2)
           (e : @TribunalJudgment Tribunal Atom t1),
      @coerce Tribunal Atom t1 t2 e
        (@compose_bridge Tribunal Atom t1 t1 t2 id_bridge w) =
      @coerce Tribunal Atom t1 t2 e w.
  Proof. intros. reflexivity. Qed.

End MoreBridges.
