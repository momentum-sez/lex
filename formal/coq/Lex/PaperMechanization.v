From Stdlib Require Import List String Arith Lia.
Import ListNotations.

(** * Lex/PaperMechanization.v

    Standalone theorem targets for the paper-level statements in
    [papers/lex.tex].  The intent is twofold:

    1. close the paper propositions that are already elementary in the
       published calculus, and
    2. give every remaining paper theorem a named Rocq target, even
       where the proof is still open.

    This file is intentionally independent of the larger Lex
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
(** ** Open paper targets and repaired effect monotonicity                   *)
(* ------------------------------------------------------------------------- *)

(** Earlier revisions of this file wrapped open conclusions in Sections that
    introduced the conclusion itself as a Hypothesis (over uninterpreted
    Parameters) and then closed the Theorem with [exact <that_hypothesis>].
    That is formally [Qed]-closed but circular: a reader running
    [grep Admitted] sees nothing, yet no actual content is proved.

    The security and WHNF support kernels below are now represented with their
    exact proof objects exposed.  The security kernel is a finite-observation
    event-union bound; the WHNF kernel is a typed administrative weak-head
    calculus with an explicit head-step measure.  The full cryptographic
    reduction and full admissible-calculus WHNF theorem are intentionally not
    hidden behind these support lemmas.
    Effect monotonicity is elementary once derivations are represented as
    finite row-labelled trees: the row of an enclosing derivation is the join
    of its local row and the rows of its immediate subderivations. *)

Section DiscretionHoleReductionTarget.
  Context {Adversary Observation : Type}.

  Fixpoint count_observations
      (P : Observation -> Prop)
      (dec : forall obs, {P obs} + {~ P obs})
      (xs : list Observation) : nat :=
    match xs with
    | [] => 0
    | obs :: rest =>
        if dec obs
        then S (count_observations P dec rest)
        else count_observations P dec rest
    end.

  Lemma count_observations_subset_union :
    forall (P Q R : Observation -> Prop)
           (decP : forall obs, {P obs} + {~ P obs})
           (decQ : forall obs, {Q obs} + {~ Q obs})
           (decR : forall obs, {R obs} + {~ R obs})
           (xs : list Observation),
      (forall obs, P obs -> Q obs \/ R obs) ->
      count_observations P decP xs <=
      count_observations Q decQ xs + count_observations R decR xs.
  Proof.
    intros P Q R decP decQ decR xs Hsub.
    induction xs as [| obs rest IH].
    - simpl. lia.
    - simpl.
      destruct (decP obs) as [HP | HnotP];
        destruct (decQ obs) as [HQ | HnotQ];
        destruct (decR obs) as [HR | HnotR];
        simpl; try lia.
      exfalso.
      destruct (Hsub obs HP) as [HQ' | HR']; contradiction.
  Qed.

  Record discretion_hole_reduction_game : Type := mkDiscretionHoleReductionGame {
    game_observations : Adversary -> nat -> list Observation;
    hole_forgery_event : Adversary -> nat -> Observation -> Prop;
    euf_cma_event : Adversary -> nat -> Observation -> Prop;
    reduction_overhead_event : Adversary -> nat -> Observation -> Prop;
    hole_forgery_dec :
      forall A k obs, {hole_forgery_event A k obs} + {~ hole_forgery_event A k obs};
    euf_cma_dec :
      forall A k obs, {euf_cma_event A k obs} + {~ euf_cma_event A k obs};
    reduction_overhead_dec :
      forall A k obs,
        {reduction_overhead_event A k obs} + {~ reduction_overhead_event A k obs};
    reduction_maps_hole_forgery :
      forall A k obs,
        hole_forgery_event A k obs ->
        euf_cma_event A k obs \/ reduction_overhead_event A k obs
  }.

  Definition hole_forgery_advantage
      (G : discretion_hole_reduction_game) (A : Adversary) (k : nat) : nat :=
    count_observations
      (hole_forgery_event G A k)
      (hole_forgery_dec G A k)
      (game_observations G A k).

  Definition euf_cma_advantage
      (G : discretion_hole_reduction_game) (A : Adversary) (k : nat) : nat :=
    count_observations
      (euf_cma_event G A k)
      (euf_cma_dec G A k)
      (game_observations G A k).

  Definition reduction_overhead
      (G : discretion_hole_reduction_game) (A : Adversary) (k : nat) : nat :=
    count_observations
      (reduction_overhead_event G A k)
      (reduction_overhead_dec G A k)
      (game_observations G A k).

  Theorem finite_observation_event_union_bound :
    forall (G : discretion_hole_reduction_game) (A : Adversary) (k : nat),
      hole_forgery_advantage G A k <=
      euf_cma_advantage G A k + reduction_overhead G A k.
  Proof.
    intros G A k.
    unfold hole_forgery_advantage, euf_cma_advantage, reduction_overhead.
    apply count_observations_subset_union.
    apply reduction_maps_hole_forgery.
  Qed.
End DiscretionHoleReductionTarget.

(** A finite effect derivation tree.  [ED_Local row] is a leaf whose local
    computation has row [row].  [ED_Node row left right] has its own local row
    plus two subderivations; n-ary syntax trees are encoded by reassociation. *)
Inductive EffectDerivation : Type :=
  | ED_Local : EffectRow -> EffectDerivation
  | ED_Node : EffectRow -> EffectDerivation -> EffectDerivation -> EffectDerivation.

Fixpoint derivation_row (d : EffectDerivation) : EffectRow :=
  match d with
  | ED_Local row => row
  | ED_Node row lft rgt =>
      row_join row (row_join (derivation_row lft) (derivation_row rgt))
  end.

(** [subderivation outer inner] means [inner] occurs inside [outer], allowing
    reflexivity because a derivation is a subderivation of itself. *)
Inductive subderivation : EffectDerivation -> EffectDerivation -> Prop :=
  | subderivation_refl :
      forall d,
        subderivation d d
  | subderivation_left :
      forall row lft rgt inner,
        subderivation lft inner ->
        subderivation (ED_Node row lft rgt) inner
  | subderivation_right :
      forall row lft rgt inner,
        subderivation rgt inner ->
        subderivation (ED_Node row lft rgt) inner.

Lemma row_join_inner_left_subsumed :
  forall row lft rgt,
    row_subsumed
      (derivation_row lft)
      (derivation_row (ED_Node row lft rgt)).
Proof.
  intros row lft rgt.
  unfold row_subsumed.
  intros eff Hleft.
  simpl.
  right. left. exact Hleft.
Qed.

Lemma row_join_inner_right_subsumed :
  forall row lft rgt,
    row_subsumed
      (derivation_row rgt)
      (derivation_row (ED_Node row lft rgt)).
Proof.
  intros row lft rgt.
  unfold row_subsumed.
  intros eff Hright.
  simpl.
  right. right. exact Hright.
Qed.

(** Paper-level effect monotonicity.  Any subderivation's effects are visible
    in the enclosing derivation row; adding context can only add effects. *)
Theorem effect_monotonicity :
  forall (d_outer d_inner : EffectDerivation),
    subderivation d_outer d_inner ->
    row_subsumed (derivation_row d_inner) (derivation_row d_outer).
Proof.
  intros d_outer d_inner Hsub.
  induction Hsub.
  - apply row_subsumed_refl.
  - apply row_subsumed_trans with (b := derivation_row lft).
    + exact IHHsub.
    + apply row_join_inner_left_subsumed.
  - apply row_subsumed_trans with (b := derivation_row rgt).
    + exact IHHsub.
    + apply row_join_inner_right_subsumed.
Qed.

(** ** Bounded administrative WHNF

    Weak-head normalization in the executable checker is fuel-bounded.  The
    paper-level target needed a first closed kernel for that statement, not a
    theorem over arbitrary black-box functions.  The following calculus is the
    administrative fragment that carries the fuel argument: values are already
    WHNF, annotations erase at the head, and lets continue with their body.
    The measure [whnf_head_steps] counts exactly those head eliminations. *)

Inductive WhnfTy : Type :=
  | WhnfBase : WhnfTy
  | WhnfArrow : WhnfTy -> WhnfTy -> WhnfTy.

Inductive WhnfTerm : Type :=
  | WHead : nat -> WhnfTerm
  | WLam : WhnfTy -> WhnfTerm -> WhnfTerm
  | WAnnot : WhnfTerm -> WhnfTy -> WhnfTerm
  | WLet : WhnfTerm -> WhnfTerm -> WhnfTerm.

Inductive whnf_value : WhnfTerm -> Prop :=
  | WV_Head : forall n, whnf_value (WHead n)
  | WV_Lam : forall A body, whnf_value (WLam A body).

Definition whnf_value_dec :
  forall t, {whnf_value t} + {~ whnf_value t}.
Proof.
  destruct t.
  - left. constructor.
  - left. constructor.
  - right. intros H. inversion H.
  - right. intros H. inversion H.
Defined.

Inductive well_typed : WhnfTerm -> WhnfTy -> Prop :=
  | WT_Head : forall n A,
      well_typed (WHead n) A
  | WT_Lam : forall A body B,
      well_typed body B ->
      well_typed (WLam A body) (WhnfArrow A B)
  | WT_Annot : forall t A,
      well_typed t A ->
      well_typed (WAnnot t A) A
  | WT_Let : forall v body A B,
      well_typed v A ->
      well_typed body B ->
      well_typed (WLet v body) B.

Fixpoint term_size (t : WhnfTerm) : nat :=
  match t with
  | WHead _ => 1
  | WLam _ body => S (term_size body)
  | WAnnot inner _ => S (term_size inner)
  | WLet v body => S (term_size v + term_size body)
  end.

Fixpoint let_depth (t : WhnfTerm) : nat :=
  match t with
  | WHead _ => 0
  | WLam _ _ => 0
  | WAnnot inner _ => let_depth inner
  | WLet _ body => S (let_depth body)
  end.

Fixpoint whnf_head_steps (t : WhnfTerm) : nat :=
  match t with
  | WHead _ => 0
  | WLam _ _ => 0
  | WAnnot inner _ => S (whnf_head_steps inner)
  | WLet _ body => S (whnf_head_steps body)
  end.

Fixpoint whnf_result (t : WhnfTerm) : WhnfTerm :=
  match t with
  | WHead _ => t
  | WLam _ _ => t
  | WAnnot inner _ => whnf_result inner
  | WLet _ body => whnf_result body
  end.

Fixpoint whnf_with_fuel (fuel : nat) (t : WhnfTerm) : option WhnfTerm :=
  match fuel with
  | 0 =>
      if whnf_value_dec t then Some t else None
  | S fuel' =>
      match t with
      | WAnnot inner _ => whnf_with_fuel fuel' inner
      | WLet _ body => whnf_with_fuel fuel' body
      | _ => Some t
      end
  end.

Definition closed (_ : WhnfTerm) : Prop := True.
Definition admissible (_ : WhnfTerm) : Prop := True.

Lemma whnf_result_value :
  forall t, whnf_value (whnf_result t).
Proof.
  induction t; simpl; try constructor; assumption.
Qed.

Lemma whnf_with_fuel_head_steps :
  forall t,
    whnf_with_fuel (whnf_head_steps t) t = Some (whnf_result t).
Proof.
  induction t; simpl; try reflexivity; assumption.
Qed.

Lemma whnf_with_fuel_sufficient :
  forall t fuel,
    whnf_head_steps t <= fuel ->
    whnf_with_fuel fuel t = Some (whnf_result t).
Proof.
  induction t; intros fuel Hfuel; simpl in *.
  - destruct fuel; reflexivity.
  - destruct fuel; reflexivity.
  - destruct fuel as [| fuel']; [lia|].
    simpl. apply IHt. lia.
  - destruct fuel as [| fuel']; [lia|].
    simpl. apply IHt2. lia.
Qed.

Lemma whnf_head_steps_bound :
  forall t,
    whnf_head_steps t <= term_size t + let_depth t.
Proof.
  induction t; simpl; lia.
Qed.

Lemma whnf_value_fuel_stable :
  forall v fuel,
    whnf_value v ->
    whnf_with_fuel fuel v = Some v.
Proof.
  intros v fuel Hval.
  destruct fuel as [| fuel']; simpl.
  - destruct (whnf_value_dec v) as [_ | Hnot]; [reflexivity|].
    contradiction.
  - inversion Hval; reflexivity.
Qed.

Lemma whnf_result_stable :
  forall t fuel,
    whnf_with_fuel fuel (whnf_result t) = Some (whnf_result t).
Proof.
  intros t fuel.
  apply whnf_value_fuel_stable.
  apply whnf_result_value.
Qed.

Theorem administrative_whnf_bounded_reduction :
  forall (t : WhnfTerm) (A : WhnfTy),
    closed t ->
    admissible t ->
    well_typed t A ->
    exists k v,
      k <= term_size t + let_depth t /\
      whnf_with_fuel k t = Some v /\
      whnf_value v.
Proof.
  intros t A _ _ _.
  exists (whnf_head_steps t), (whnf_result t).
  split.
  - apply whnf_head_steps_bound.
  - split.
    + apply whnf_with_fuel_head_steps.
    + apply whnf_result_value.
Qed.

Theorem administrative_whnf_sufficient_fuel :
  forall (t : WhnfTerm) (A : WhnfTy) (fuel : nat),
    closed t ->
    admissible t ->
    well_typed t A ->
    whnf_head_steps t <= fuel ->
    exists v,
      whnf_with_fuel fuel t = Some v /\
      whnf_value v.
Proof.
  intros t A fuel _ _ _ Hfuel.
  exists (whnf_result t).
  split.
  - apply whnf_with_fuel_sufficient. exact Hfuel.
  - apply whnf_result_value.
Qed.

Theorem administrative_whnf_canonical_bound_reduction :
  forall (t : WhnfTerm) (A : WhnfTy),
    closed t ->
    admissible t ->
    well_typed t A ->
    exists v,
      whnf_with_fuel (term_size t + let_depth t) t = Some v /\
      whnf_value v.
Proof.
  intros t A Hclosed Hadm Htyped.
  eapply administrative_whnf_sufficient_fuel; eauto.
  apply whnf_head_steps_bound.
Qed.

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
