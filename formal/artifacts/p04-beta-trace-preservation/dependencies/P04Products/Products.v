From Stdlib Require Import Lists.List.
From Lex Require Import Syntax DeBruijn Typing.
From P04Source Require Import TypeReduction.
Import ListNotations.
Import Conversion.

Lemma steps_append : forall a b c, steps a b -> steps b c -> steps a c.
Proof. intros a b c H; induction H; intros Hbc; eauto using steps. Qed.

Lemma steps_convertible : forall a b, steps a b -> convertible a b.
Proof. intros a b H; induction H; eauto using convertible. Qed.

(** Directional Pi reduction has exact static-row preservation. *)
Lemma pi_step : forall A e B u, step (Pi A e B) u ->
  exists A' B', u = Pi A' e B' /\
    ((step A A' /\ B' = B) \/ (A' = A /\ step B B')).
Proof. intros A e B u H; inversion H; subst; eauto 8. Qed.

Lemma pi_steps : forall t u, steps t u -> forall A e B,
  t = Pi A e B -> exists A' B',
    u = Pi A' e B' /\ steps A A' /\ steps B B'.
Proof.
  intros t u H; induction H; intros A e B E; subst.
  - exists A, B; repeat split; constructor.
  - destruct (pi_step _ _ _ _ H) as [A' [B' [Ev Cases]]]. subst.
    destruct (IHsteps A' e B' eq_refl) as [A'' [B'' [Eu [HA HB]]]].
    exists A'', B''; split; [exact Eu |].
    destruct Cases as [[Ha Eb] | [Ea Hb]]; subst;
      split; eauto using steps.
Qed.

Definition joinable (a b : Term) : Prop := exists c, steps a c /\ steps b c.

(** This theorem has no confluence premise: a common reduct is evidence,
    stronger than an arbitrary conversion zigzag. *)
Theorem pi_joinable_decomposition : forall A e B A' e' B',
  joinable (Pi A e B) (Pi A' e' B') ->
  e = e' /\ joinable A A' /\ joinable B B'.
Proof.
  intros A e B A' e' B' [u [H H']].
  destruct (pi_steps _ _ H A e B eq_refl) as [a [b [Eu [Ha Hb]]]].
  destruct (pi_steps _ _ H' A' e' B' eq_refl) as [a' [b' [Eu' [Ha' Hb']]]].
  rewrite Eu in Eu'; inversion Eu'; subst.
  split; [reflexivity |]. split; [exists a' | exists b']; split; assumption.
Qed.

Theorem pi_joinable_convertible_components : forall A e B A' e' B',
  joinable (Pi A e B) (Pi A' e' B') ->
  e = e' /\ convertible A A' /\ convertible B B'.
Proof.
  intros A e B A' e' B' H.
  destruct (pi_joinable_decomposition _ _ _ _ _ _ H) as [He [[a [Ha Ha']] [b [Hb Hb']]]].
  repeat split; eauto using convertible, steps_convertible.
Qed.

Definition delta : Term := Lambda prop (App (Var 0) (Var 0)).
Definition omega : Term := App delta delta.
Lemma raw_omega_self_step : step omega omega.
Proof. unfold omega, delta; apply step_beta. Qed.

Print Assumptions pi_step.
Print Assumptions pi_steps.
Print Assumptions pi_joinable_decomposition.
Print Assumptions pi_joinable_convertible_components.
Print Assumptions raw_omega_self_step.
