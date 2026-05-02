(** * Lex/ReceiptAlgebra.v -- compositional Lex receipts

    A Lex receipt is the small object that an execution host needs after
    evaluating a rule: the verdict, the declared obligations, the obligations
    not yet discharged, and the discretion frontier still awaiting authority.

    This file proves the algebra that makes receipts safe to hand to an
    admission host.  Receipt composition meets verdicts and unions the two
    observable frontiers.  Therefore a composed receipt is accepted iff each
    component receipt is accepted, and a composed receipt is Compliant iff each
    component receipt is Compliant.  No unresolved obligation or discretion
    hole can be hidden by composition.
*)

Require Import Stdlib.Lists.List.
Require Import Stdlib.micromega.Lia.
Require Import Lex.VerdictHeyting.
Import ListNotations.

Definition ObligationId := nat.
Definition HoleId := nat.

Record receipt : Type := mkReceipt {
  rc_verdict : verdict;
  rc_obligations : list ObligationId;
  rc_unresolved : list ObligationId;
  rc_frontier : list HoleId;
}.

Definition compose_receipt (a b : receipt) : receipt :=
  mkReceipt
    (meet (rc_verdict a) (rc_verdict b))
    (rc_obligations a ++ rc_obligations b)
    (rc_unresolved a ++ rc_unresolved b)
    (rc_frontier a ++ rc_frontier b).

Definition accepted (r : receipt) : Prop :=
  rc_unresolved r = [] /\ rc_frontier r = [].

Definition compliant (r : receipt) : Prop :=
  accepted r /\ rc_verdict r = Compliant.

Definition same_members {A : Type} (xs ys : list A) : Prop :=
  forall x, In x xs <-> In x ys.

Definition receipt_equiv (a b : receipt) : Prop :=
  rc_verdict a = rc_verdict b /\
  same_members (rc_obligations a) (rc_obligations b) /\
  same_members (rc_unresolved a) (rc_unresolved b) /\
  same_members (rc_frontier a) (rc_frontier b).

Lemma app_nil_inv :
  forall {A : Type} (xs ys : list A),
    xs ++ ys = [] -> xs = [] /\ ys = [].
Proof.
  intros A xs ys H.
  destruct xs as [| x xs].
  - simpl in H. split; [reflexivity | exact H].
  - simpl in H. discriminate H.
Qed.

Lemma app_nil_iff :
  forall {A : Type} (xs ys : list A),
    xs ++ ys = [] <-> xs = [] /\ ys = [].
Proof.
  intros A xs ys.
  split.
  - apply app_nil_inv.
  - intros [Hxs Hys]. subst. reflexivity.
Qed.

Theorem receipt_compose_verdict :
  forall a b,
    rc_verdict (compose_receipt a b) =
    meet (rc_verdict a) (rc_verdict b).
Proof. reflexivity. Qed.

Theorem receipt_compose_obligations :
  forall a b o,
    In o (rc_obligations (compose_receipt a b)) <->
    In o (rc_obligations a) \/ In o (rc_obligations b).
Proof.
  intros a b o. unfold compose_receipt. simpl. apply in_app_iff.
Qed.

Theorem receipt_compose_unresolved :
  forall a b o,
    In o (rc_unresolved (compose_receipt a b)) <->
    In o (rc_unresolved a) \/ In o (rc_unresolved b).
Proof.
  intros a b o. unfold compose_receipt. simpl. apply in_app_iff.
Qed.

Theorem receipt_compose_frontier :
  forall a b h,
    In h (rc_frontier (compose_receipt a b)) <->
    In h (rc_frontier a) \/ In h (rc_frontier b).
Proof.
  intros a b h. unfold compose_receipt. simpl. apply in_app_iff.
Qed.

Theorem accepted_compose_iff :
  forall a b,
    accepted (compose_receipt a b) <-> accepted a /\ accepted b.
Proof.
  intros a b.
  unfold accepted, compose_receipt. simpl.
  split.
  - intros [Hunresolved Hfrontier].
    apply app_nil_inv in Hunresolved as [Ha_un Hb_un].
    apply app_nil_inv in Hfrontier as [Ha_fr Hb_fr].
    split; split; assumption.
  - intros [[Ha_un Ha_fr] [Hb_un Hb_fr]].
    split; rewrite ?Ha_un, ?Hb_un, ?Ha_fr, ?Hb_fr; reflexivity.
Qed.

Lemma meet_compliant_iff :
  forall a b,
    meet a b = Compliant <-> a = Compliant /\ b = Compliant.
Proof.
  destruct a, b; simpl; split; intro H;
    try discriminate H;
    try (inversion H; subst; split; reflexivity);
    try (destruct H as [Ha Hb]; discriminate).
Qed.

Theorem compliant_compose_iff :
  forall a b,
    compliant (compose_receipt a b) <-> compliant a /\ compliant b.
Proof.
  intros a b.
  unfold compliant.
  split.
  - intros [Hacc Hverdict].
    apply accepted_compose_iff in Hacc.
    apply meet_compliant_iff in Hverdict.
    destruct Hacc as [Hacc_a Hacc_b].
    destruct Hverdict as [Hverdict_a Hverdict_b].
    split; split; assumption.
  - intros [[Hacc_a Hverdict_a] [Hacc_b Hverdict_b]].
    split.
    + apply accepted_compose_iff. split; assumption.
    + simpl. rewrite Hverdict_a, Hverdict_b. reflexivity.
Qed.

Lemma meet_lower_left :
  forall a b,
    leq (meet a b) a.
Proof.
  destruct a, b; unfold leq, meet; simpl; lia.
Qed.

Lemma meet_lower_right :
  forall a b,
    leq (meet a b) b.
Proof.
  destruct a, b; unfold leq, meet; simpl; lia.
Qed.

Lemma meet_greatest_lower_bound :
  forall x a b,
    leq x a -> leq x b -> leq x (meet a b).
Proof.
  destruct x, a, b; unfold leq, meet; simpl; intros; lia.
Qed.

Theorem composed_verdict_lower_bounds :
  forall a b,
    leq (rc_verdict (compose_receipt a b)) (rc_verdict a) /\
    leq (rc_verdict (compose_receipt a b)) (rc_verdict b).
Proof.
  intros a b. split.
  - apply meet_lower_left.
  - apply meet_lower_right.
Qed.

Theorem composed_verdict_is_glb :
  forall x a b,
    leq x (rc_verdict a) ->
    leq x (rc_verdict b) ->
    leq x (rc_verdict (compose_receipt a b)).
Proof.
  intros x a b Ha Hb.
  apply meet_greatest_lower_bound; assumption.
Qed.

Theorem compose_receipt_assoc :
  forall a b c,
    compose_receipt (compose_receipt a b) c =
    compose_receipt a (compose_receipt b c).
Proof.
  destruct a as [av ao au af].
  destruct b as [bv bo bu bf].
  destruct c as [cv co cu cf].
  unfold compose_receipt; simpl.
  rewrite meet_assoc.
  repeat rewrite app_assoc.
  reflexivity.
Qed.

Theorem compose_receipt_comm_equiv :
  forall a b,
    receipt_equiv (compose_receipt a b) (compose_receipt b a).
Proof.
  intros a b.
  unfold receipt_equiv.
  split.
  - simpl. apply meet_comm.
  - split.
    + unfold same_members. intro y. simpl. rewrite !in_app_iff.
      split; intros [H | H]; [right | left | right | left]; exact H.
    + split.
      * unfold same_members. intro y. simpl. rewrite !in_app_iff.
        split; intros [H | H]; [right | left | right | left]; exact H.
      * unfold same_members. intro y. simpl. rewrite !in_app_iff.
        split; intros [H | H]; [right | left | right | left]; exact H.
Qed.

(** Corollary for admission hosts: acceptance and compliance are local.
    To accept a composed program receipt, it is enough and necessary to accept
    each Lex component receipt.  To treat the composed verdict as Compliant,
    each component verdict must itself be Compliant. *)
Corollary admission_locality :
  forall a b,
    accepted (compose_receipt a b) /\ compliant (compose_receipt a b) <->
    (accepted a /\ compliant a) /\ (accepted b /\ compliant b).
Proof.
  intros a b.
  rewrite accepted_compose_iff.
  rewrite compliant_compose_iff.
  tauto.
Qed.
