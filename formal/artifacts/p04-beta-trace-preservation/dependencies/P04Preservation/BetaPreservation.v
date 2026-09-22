From Lex Require Import Syntax DeBruijn Typing.
From P04Source Require Import TypeReduction FormedTyping RepairedReduction.
From P04Products Require Import ProductCompatibility.
From P04Preservation Require Import ConditionalBeta.

(** The independent source-conversion theorem discharges the exact product
    compatibility dependency of the previously checked beta proof. *)
Module BetaPreservation.

Theorem source_product_compatibility : ConditionalBeta.product_compatibility.
Proof.
  intros A B A' B' eff eff' H.
  destruct (pi_convertible_decomposition A eff B A' eff' B' H)
    as [_ [Hdomain Hcodomain]].
  split; assumption.
Qed.

Theorem beta_preservation : forall ctx dom body arg T,
  Formed.wf_context ctx ->
  Formed.has_type ctx (App (Lambda dom body) arg) T ->
  Formed.has_type ctx (subst 0 arg body) T.
Proof.
  exact (ConditionalBeta.beta_preservation_from_product_compatibility
    source_product_compatibility).
Qed.

Theorem beta_reduction_preservation : forall ctx dom body arg T,
  Formed.wf_context ctx ->
  Formed.has_type ctx (App (Lambda dom body) arg) T ->
  Repaired.step (App (Lambda dom body) arg) (subst 0 arg body) /\
  Formed.has_type ctx (subst 0 arg body) T.
Proof.
  intros ctx dom body arg T Hwf Hty.
  split. apply Repaired.step_beta.
  eapply beta_preservation; eassumption.
Qed.

Print Assumptions source_product_compatibility.
Print Assumptions beta_preservation.
Print Assumptions beta_reduction_preservation.
End BetaPreservation.
