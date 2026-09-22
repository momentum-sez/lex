From Stdlib Require Import Lists.List Arith.Arith.
From Lex Require Import Syntax DeBruijn Typing.
From P04Source Require Import TypeReduction FormedTyping.
From P04RegularityDesign Require Import FormedWeakening.
From P04TypedSubstitution Require Import FormedSubstitution.
Import ListNotations.
Import Formed FormedStructural FormedSubstitution.FormedSubstitution.

(** Every derived type has a universe in a generated, well-formed context.
    Application and let use the proved dependent substitution theorem. *)
Theorem source_regularity : forall ctx t T,
  has_type ctx t T -> wf_context ctx ->
  exists i, has_type ctx T (type_level i).
Proof.
  intros ctx t T H. induction H; intros Hwf.
  - eapply lookup_formation; eassumption.
  - exists (S (S n)). apply T_Type. reflexivity.
  - exists 2. apply T_Type. reflexivity.
  - exists (S (S n)). apply T_Type. reflexivity.
  - exists 1. apply T_Type. reflexivity.
  - exists 1. apply T_Type. reflexivity.
  - exists (S (Nat.max i j)). apply T_Type. reflexivity.
  - destruct (IHhas_type2 (wf_extend ctx A i Hwf H)) as [j HB].
    exists (Nat.max i j). eapply T_Pi; eassumption.
  - destruct (IHhas_type1 Hwf) as [i Hpi].
    destruct (pi_formation ctx (Pi A eff B) (type_level i) Hpi A eff B eq_refl)
      as [j [k [HA HB]]].
    exists k. exact (body_substitution ctx A a B (type_level k) H0 HB).
  - exists i. assumption.
  - destruct (IHhas_type3 (wf_extend ctx A i Hwf H)) as [j HB].
    exists j. exact (body_substitution ctx A v B (type_level j) H0 HB).
  - exists i. assumption.
  - exists i. assumption.
  - exists i. assumption.
Qed.

Print Assumptions source_regularity.
