(** * Lex/BoundedQuantifierAdmissibility.v

    Integration lemma for bounded quantifiers.

    [BoundedQuantifiers.v] proves the finite-list boolean algebra.  This file
    supplies the missing bridge to the executable admissible fragment: a
    bounded quantifier over an enumerated finite collection elaborates to a
    finite fold using ordinary constants and applications, and that elaborated
    term is admissible whenever every predicate instance is admissible.
*)

Require Import Stdlib.Lists.List.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Strings.String.

Require Import Lex.Syntax.
Require Import Lex.Admissibility.
Require Import Lex.BoundedQuantifiers.

Import ListNotations.
Open Scope string_scope.

Definition bool_true_term : Term := Constant "True".
Definition bool_false_term : Term := Constant "False".

Definition bool_and_term (a b : Term) : Term :=
  App (App (Constant "Bool.and") a) b.

Definition bool_or_term (a b : Term) : Term :=
  App (App (Constant "Bool.or") a) b.

Fixpoint bounded_forall_term {A : Type} (P : A -> Term) (xs : list A)
  : Term :=
  match xs with
  | [] => bool_true_term
  | x :: rest => bool_and_term (P x) (bounded_forall_term P rest)
  end.

Fixpoint bounded_exists_term {A : Type} (P : A -> Term) (xs : list A)
  : Term :=
  match xs with
  | [] => bool_false_term
  | x :: rest => bool_or_term (P x) (bounded_exists_term P rest)
  end.

Lemma bool_and_admissible :
  forall a b,
    admissible a ->
    admissible b ->
    admissible (bool_and_term a b).
Proof.
  intros a b Ha Hb.
  unfold admissible, bool_and_term in *.
  simpl. rewrite Ha, Hb. reflexivity.
Qed.

Lemma bool_or_admissible :
  forall a b,
    admissible a ->
    admissible b ->
    admissible (bool_or_term a b).
Proof.
  intros a b Ha Hb.
  unfold admissible, bool_or_term in *.
  simpl. rewrite Ha, Hb. reflexivity.
Qed.

Theorem bounded_forall_term_admissible :
  forall (A : Type) (P : A -> Term) (xs : list A),
    (forall x, In x xs -> admissible (P x)) ->
    admissible (bounded_forall_term P xs).
Proof.
  intros A P xs.
  induction xs as [| x rest IH]; intro Hall.
  - unfold admissible, bool_true_term. simpl. reflexivity.
  - simpl. apply bool_and_admissible.
    + apply Hall. left. reflexivity.
    + apply IH. intros y Hin. apply Hall. right. exact Hin.
Qed.

Theorem bounded_exists_term_admissible :
  forall (A : Type) (P : A -> Term) (xs : list A),
    (forall x, In x xs -> admissible (P x)) ->
    admissible (bounded_exists_term P xs).
Proof.
  intros A P xs.
  induction xs as [| x rest IH]; intro Hall.
  - unfold admissible, bool_false_term. simpl. reflexivity.
  - simpl. apply bool_or_admissible.
    + apply Hall. left. reflexivity.
    + apply IH. intros y Hin. apply Hall. right. exact Hin.
Qed.
