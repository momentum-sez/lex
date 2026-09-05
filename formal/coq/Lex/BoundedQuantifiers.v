(** * Bounded quantifiers over finite collections (Qed-closed) *)

(** Mechanizes the bounded forall/exists/exists! of lex.tex
    Quantification section, over finite lists of elements of a
    decidable-equality type.  Classical logic is avoided; the
    bounded quantifiers are decidable by construction. *)

Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Import ListNotations.

Set Implicit Arguments.

(** Bounded forall: all elements of [xs] satisfy [P]. *)
Fixpoint bforall {A : Type} (P : A -> bool) (xs : list A) : bool :=
  match xs with
  | [] => true
  | x :: xs' => andb (P x) (bforall P xs')
  end.

(** Bounded exists: some element of [xs] satisfies [P]. *)
Fixpoint bexists {A : Type} (P : A -> bool) (xs : list A) : bool :=
  match xs with
  | [] => false
  | x :: xs' => orb (P x) (bexists P xs')
  end.

(** Bounded unique existence: exactly one element satisfies [P]. *)
Fixpoint bcount {A : Type} (P : A -> bool) (xs : list A) : nat :=
  match xs with
  | [] => 0
  | x :: xs' => if P x then S (bcount P xs') else bcount P xs'
  end.

Definition bexists_unique {A : Type} (P : A -> bool) (xs : list A) : bool :=
  Nat.eqb (bcount P xs) 1.

(** Sanity: bforall on empty list is true. *)
Lemma bforall_nil : forall A (P : A -> bool), bforall P [] = true.
Proof. reflexivity. Qed.

(** Sanity: bexists on empty list is false. *)
Lemma bexists_nil : forall A (P : A -> bool), bexists P [] = false.
Proof. reflexivity. Qed.

(** Correspondence with In and forall/exists. *)
Lemma bforall_correct : forall A (P : A -> bool) xs,
  bforall P xs = true <-> (forall x, In x xs -> P x = true).
Proof.
  induction xs as [|x xs IH]; simpl; split; intro H.
  - intros x0 [].
  - reflexivity.
  - intros x0 [Heq | Hin].
    + subst. apply andb_true_iff in H. destruct H. exact H.
    + apply andb_true_iff in H. destruct H as [_ H2].
      apply (proj1 IH H2). exact Hin.
  - apply andb_true_iff. split.
    + apply H. left. reflexivity.
    + apply IH. intros x0 Hin. apply H. right. exact Hin.
Qed.

Lemma bexists_correct : forall A (P : A -> bool) xs,
  bexists P xs = true <-> (exists x, In x xs /\ P x = true).
Proof.
  induction xs as [|x xs IH]; simpl; split; intro H.
  - discriminate.
  - destruct H as [x0 [[] _]].
  - apply orb_true_iff in H. destruct H as [Hx | Hxs].
    + exists x. split; [left; reflexivity | exact Hx].
    + apply IH in Hxs. destruct Hxs as [x0 [Hin HP]].
      exists x0. split; [right; exact Hin | exact HP].
  - apply orb_true_iff. destruct H as [x0 [[Heq | Hin] HP]].
    + subst. left. exact HP.
    + right. apply IH. exists x0. split; assumption.
Qed.

(** bexists_unique correspondence with the Prop-level predicate. *)
Lemma bcount_zero_none : forall A (P : A -> bool) xs,
  bcount P xs = 0 <-> (forall x, In x xs -> P x = false).
Proof.
  induction xs as [|x xs IH]; simpl; split; intro H.
  - intros x0 [].
  - reflexivity.
  - destruct (P x) eqn:Hx.
    + discriminate.
    + intros x0 [Heq | Hin].
      * subst. exact Hx.
      * apply (proj1 IH H). exact Hin.
  - assert (Hx : P x = false) by (apply H; left; reflexivity).
    rewrite Hx. apply IH. intros x0 Hin. apply H. right. exact Hin.
Qed.

(** Sanity laws on the admissible sub-grammar.  These are exactly
    the "bounded quantification" laws of the paper.  Since they are
    decidable, forall and exists also compose: *)

Lemma bforall_cons : forall A (P : A -> bool) x xs,
  bforall P (x :: xs) = andb (P x) (bforall P xs).
Proof. reflexivity. Qed.

Lemma bexists_cons : forall A (P : A -> bool) x xs,
  bexists P (x :: xs) = orb (P x) (bexists P xs).
Proof. reflexivity. Qed.

(** bforall_app: quantification distributes over append. *)
Lemma bforall_app : forall A (P : A -> bool) xs ys,
  bforall P (xs ++ ys) = andb (bforall P xs) (bforall P ys).
Proof.
  induction xs as [|x xs IH]; simpl; intro ys.
  - reflexivity.
  - rewrite IH. rewrite andb_assoc. reflexivity.
Qed.

Lemma bexists_app : forall A (P : A -> bool) xs ys,
  bexists P (xs ++ ys) = orb (bexists P xs) (bexists P ys).
Proof.
  induction xs as [|x xs IH]; simpl; intro ys.
  - reflexivity.
  - rewrite IH. rewrite orb_assoc. reflexivity.
Qed.

(** Negation duality: ~bforall (not P) iff bexists P. *)
Lemma bforall_not_bexists : forall A (P : A -> bool) xs,
  bforall (fun x => negb (P x)) xs = negb (bexists P xs).
Proof.
  induction xs as [|x xs IH]; simpl.
  - reflexivity.
  - rewrite IH. destruct (P x); reflexivity.
Qed.

(** Pointwise implication on predicates lifts to bforall. *)
Lemma bforall_impl :
  forall A (P Q : A -> bool) xs,
    (forall x, In x xs -> P x = true -> Q x = true) ->
    bforall P xs = true ->
    bforall Q xs = true.
Proof.
  intros A P Q xs Himpl Hforall.
  induction xs as [|x xs IH]; simpl.
  - reflexivity.
  - simpl in Hforall. apply andb_true_iff in Hforall.
    destruct Hforall as [Hx Hrest].
    apply andb_true_iff. split.
    + apply Himpl; [left; reflexivity | exact Hx].
    + apply IH.
      * intros x0 Hin HP. apply Himpl; [right; exact Hin | exact HP].
      * exact Hrest.
Qed.

(** Pointwise implication on predicates lifts to bexists. *)
Lemma bexists_impl :
  forall A (P Q : A -> bool) xs,
    (forall x, In x xs -> P x = true -> Q x = true) ->
    bexists P xs = true ->
    bexists Q xs = true.
Proof.
  intros A P Q xs Himpl Hexists.
  induction xs as [|x xs IH]; simpl.
  - simpl in Hexists. discriminate.
  - simpl in Hexists. apply orb_true_iff in Hexists.
    apply orb_true_iff.
    destruct Hexists as [Hx | Hrest].
    + left. apply Himpl; [left; reflexivity | exact Hx].
    + right. apply IH.
      * intros x0 Hin HP. apply Himpl; [right; exact Hin | exact HP].
      * exact Hrest.
Qed.

(** Conjunction distributes over [bforall]. *)
Lemma bforall_and_distrib :
  forall A (P Q : A -> bool) xs,
    bforall (fun x => andb (P x) (Q x)) xs =
    andb (bforall P xs) (bforall Q xs).
Proof.
  intros A P Q xs. induction xs as [|x xs IH]; simpl.
  - reflexivity.
  - rewrite IH. destruct (P x), (Q x), (bforall P xs), (bforall Q xs); reflexivity.
Qed.

(** Disjunction distributes over [bexists]. *)
Lemma bexists_or_distrib :
  forall A (P Q : A -> bool) xs,
    bexists (fun x => orb (P x) (Q x)) xs =
    orb (bexists P xs) (bexists Q xs).
Proof.
  intros A P Q xs. induction xs as [|x xs IH]; simpl.
  - reflexivity.
  - rewrite IH. destruct (P x), (Q x), (bexists P xs), (bexists Q xs); reflexivity.
Qed.

(** Second De Morgan duality: [~bexists (not P)] iff [bforall P]. *)
Lemma bexists_not_bforall :
  forall A (P : A -> bool) xs,
    bexists (fun x => negb (P x)) xs = negb (bforall P xs).
Proof.
  intros A P xs. induction xs as [|x xs IH]; simpl.
  - reflexivity.
  - rewrite IH. destruct (P x); reflexivity.
Qed.

(** [bforall] on a subset: appending preserves truth. *)
Lemma bforall_weaken_suffix :
  forall A (P : A -> bool) xs ys,
    bforall P (xs ++ ys) = true ->
    bforall P xs = true.
Proof.
  intros A P xs ys H.
  rewrite bforall_app in H.
  apply andb_true_iff in H.
  destruct H as [H1 _].
  exact H1.
Qed.

Lemma bforall_weaken_prefix :
  forall A (P : A -> bool) xs ys,
    bforall P (xs ++ ys) = true ->
    bforall P ys = true.
Proof.
  intros A P xs ys H.
  rewrite bforall_app in H.
  apply andb_true_iff in H.
  destruct H as [_ H2].
  exact H2.
Qed.

(** ** Further quantifier laws (2026-04-20) *)

(** bforall on a singleton reduces to the predicate. *)
Lemma bforall_singleton :
  forall A (P : A -> bool) x,
    bforall P [x] = P x.
Proof.
  intros A P x. simpl. destruct (P x); reflexivity.
Qed.

(** bexists on a singleton reduces to the predicate. *)
Lemma bexists_singleton :
  forall A (P : A -> bool) x,
    bexists P [x] = P x.
Proof.
  intros A P x. simpl. destruct (P x); reflexivity.
Qed.

(** bcount on empty is 0. *)
Lemma bcount_nil :
  forall A (P : A -> bool), bcount P [] = 0.
Proof. reflexivity. Qed.

(** bcount on cons: a case on the head predicate. *)
Lemma bcount_cons_true :
  forall A (P : A -> bool) x xs,
    P x = true ->
    bcount P (x :: xs) = S (bcount P xs).
Proof. intros A P x xs H. simpl. rewrite H. reflexivity. Qed.

Lemma bcount_cons_false :
  forall A (P : A -> bool) x xs,
    P x = false ->
    bcount P (x :: xs) = bcount P xs.
Proof. intros A P x xs H. simpl. rewrite H. reflexivity. Qed.

(** bcount is bounded above by the list length. *)
Lemma bcount_leq_length :
  forall A (P : A -> bool) xs,
    bcount P xs <= length xs.
Proof.
  intros A P xs. induction xs as [|x xs IH]; simpl.
  - lia.
  - destruct (P x); lia.
Qed.

(** bcount over append distributes additively. *)
Lemma bcount_app :
  forall A (P : A -> bool) xs ys,
    bcount P (xs ++ ys) = bcount P xs + bcount P ys.
Proof.
  intros A P xs ys. induction xs as [|x xs IH]; simpl.
  - reflexivity.
  - rewrite IH. destruct (P x); reflexivity.
Qed.

(** Implication on bcount: pointwise P -> Q gives bcount P <= bcount Q. *)
Lemma bcount_le_impl :
  forall A (P Q : A -> bool) xs,
    (forall x, In x xs -> P x = true -> Q x = true) ->
    bcount P xs <= bcount Q xs.
Proof.
  intros A P Q xs Himpl. induction xs as [|x xs IH]; simpl.
  - lia.
  - destruct (P x) eqn:HPx.
    + rewrite (Himpl x (or_introl eq_refl) HPx).
      assert (H : bcount P xs <= bcount Q xs).
      { apply IH. intros x0 Hin HP. apply Himpl; [right; exact Hin | exact HP]. }
      lia.
    + assert (H : bcount P xs <= bcount Q xs).
      { apply IH. intros x0 Hin HP. apply Himpl; [right; exact Hin | exact HP]. }
      destruct (Q x); lia.
Qed.

(** If every element fires, bcount equals list length. *)
Lemma bcount_all_true :
  forall A (P : A -> bool) xs,
    (forall x, In x xs -> P x = true) ->
    bcount P xs = length xs.
Proof.
  intros A P xs H. induction xs as [|x xs IH]; simpl.
  - reflexivity.
  - assert (Hx : P x = true) by (apply H; left; reflexivity).
    rewrite Hx. f_equal. apply IH. intros x0 Hin.
    apply H. right. exact Hin.
Qed.

(** Worked example: Seychelles IBC Act 2016 s.130(1) requires a
    company at all times to have at least one director appointed in
    accordance with the Act.  We model directors as a list and
    appointment under the Act as a decidable check; the statutory
    predicate is exactly a bounded existential.  (The input model, with
    the s.130(2) window and the other-written-law carve-out, is
    mechanized in Examples/SeychellesS130.v.) *)
Section WorkedExample.
  Variable director : Type.
  Variable appointed_under_act : director -> bool.

  Definition seychelles_s130_satisfied (directors : list director) : bool :=
    bexists appointed_under_act directors.

  Theorem seychelles_s130_correct :
    forall directors,
      seychelles_s130_satisfied directors = true <->
      (exists d, In d directors /\ appointed_under_act d = true).
  Proof.
    intros directors. apply bexists_correct.
  Qed.
End WorkedExample.

(** ** Further quantifier / bcount lemmas (2026-04-20) *)

(** bforall of a tautology (the always-true predicate) is always true. *)
Lemma bforall_true :
  forall A (xs : list A), bforall (fun _ => true) xs = true.
Proof.
  intros A xs. induction xs as [|x xs IH]; simpl; [reflexivity | exact IH].
Qed.

(** bexists of a tautology on a non-empty list is always true. *)
Lemma bexists_true_cons :
  forall A (x : A) (xs : list A),
    bexists (fun _ => true) (x :: xs) = true.
Proof. intros A x xs. reflexivity. Qed.

(** bforall is preserved by list permutation-via-append-commutativity
    at the "and" level. *)
Lemma bforall_app_comm :
  forall A (P : A -> bool) xs ys,
    bforall P (xs ++ ys) = bforall P (ys ++ xs).
Proof.
  intros A P xs ys. rewrite !bforall_app, andb_comm. reflexivity.
Qed.

(** bexists is preserved by list permutation-via-append. *)
Lemma bexists_app_comm :
  forall A (P : A -> bool) xs ys,
    bexists P (xs ++ ys) = bexists P (ys ++ xs).
Proof.
  intros A P xs ys. rewrite !bexists_app, orb_comm. reflexivity.
Qed.

(** bcount_app is order-insensitive. *)
Lemma bcount_app_comm :
  forall A (P : A -> bool) xs ys,
    bcount P (xs ++ ys) = bcount P (ys ++ xs).
Proof.
  intros A P xs ys. rewrite !bcount_app. lia.
Qed.
