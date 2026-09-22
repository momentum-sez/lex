From Stdlib Require Import Lists.List Strings.String.
From Lex Require Import Syntax DeBruijn Typing.
From P04Source Require Import FormedTyping RepairedReduction.
From P04Preservation Require Import CorePreservation.
Import ListNotations.
Import Formed CorePreservation.CorePreservation.

Module AdministrativeReduction.

(** An explicit subset of the captured operational relation. These rules
    have no typing premises. The inclusion theorem connects every step to
    Repaired.step. Beta is supplied separately by ConditionalBeta. *)
Inductive step : Term -> Term -> Prop :=
  | zeta : forall A v body, step (Let A v body) (subst 0 v body)
  | annotation : forall e A, step (Annot e A) e
  | empty_defeasible : forall A body, step (Defeasible A body []) body
  | peel : forall A body ex rest,
      step (Defeasible A body (ex::rest)) (Defeasible A body rest)
  | wildcard : forall scr ret body rest,
      value scr -> step (Match scr ret (MkBranch PWild body::rest)) body
  | skip : forall scr ret body c n rest,
      value scr -> branch_head_matches scr c n = false -> rest <> [] ->
      step (Match scr ret (MkBranch (PCtor c n) body::rest)) (Match scr ret rest)
  | app_function : forall f f' arg,
      step f f' -> step (App f arg) (App f' arg)
  | annotation_expression : forall e e' A,
      step e e' -> step (Annot e A) (Annot e' A)
  | lambda_body : forall A body body',
      step body body' -> step (Lambda A body) (Lambda A body')
  | let_body : forall A v body body',
      step body body' -> step (Let A v body) (Let A v body')
  | defeasible_body : forall A body body' exns,
      step body body' -> step (Defeasible A body exns) (Defeasible A body' exns)
  | match_scrutinee : forall scr scr' ret branches,
      step scr scr' -> step (Match scr ret branches) (Match scr' ret branches)
  | pi_codomain : forall A eff B B',
      step B B' -> step (Pi A eff B) (Pi A eff B').

Theorem captured_step : forall t u, step t u -> Repaired.step t u.
Proof.
  intros t u H. induction H; econstructor; eauto.
Qed.

Theorem preservation : forall t u, step t u -> forall ctx T,
  has_type ctx t T -> has_type ctx u T.
Proof.
  intros t u H. induction H; intros ctx T Hty.
  - eapply zeta_preservation; eauto.
  - eapply annotation_preservation; eauto.
  - eapply empty_defeasible_preservation; eauto.
  - eapply peel_preservation; eauto.
  - eapply wildcard_preservation; eauto.
  - eapply branch_skip_preservation; eauto.
  - eapply app_function_compatibility. exact Hty. reflexivity. intros U HU. eauto.
  - eapply annotation_expression_compatibility. exact Hty. reflexivity. intros U HU. eauto.
  - eapply lambda_body_compatibility. exact Hty. reflexivity. intros U HU. eauto.
  - eapply let_body_compatibility. exact Hty. reflexivity. intros U HU. eauto.
  - eapply defeasible_body_compatibility. exact Hty. reflexivity. intros U HU. eauto.
  - eapply match_scrutinee_compatibility. exact Hty. reflexivity. intros U HU. eauto.
  - eapply pi_codomain_compatibility. exact Hty. reflexivity. intros U HU. eauto.
Qed.

Inductive steps : Term -> Term -> Prop :=
  | reflexive : forall t, steps t t
  | next : forall t u v, step t u -> steps u v -> steps t v.

Theorem captured_steps : forall t u, steps t u -> Repaired.steps t u.
Proof.
  intros t u H. induction H.
  - apply Repaired.steps_refl.
  - eapply Repaired.steps_trans. apply captured_step. exact H. exact IHsteps.
Qed.

Theorem trace_preservation : forall t u, steps t u -> forall ctx T,
  has_type ctx t T -> has_type ctx u T.
Proof.
  intros t u H. induction H; intros ctx T Hty; auto.
  apply IHsteps. eapply preservation; eassumption.
Qed.

Print Assumptions captured_step.
Print Assumptions preservation.
Print Assumptions captured_steps.
Print Assumptions trace_preservation.
End AdministrativeReduction.
