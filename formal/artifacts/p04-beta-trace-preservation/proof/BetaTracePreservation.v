From Stdlib Require Import Lists.List Strings.String.
From Lex Require Import Syntax DeBruijn Typing.
From P04Source Require Import FormedTyping RepairedReduction.
From P04RegularityDesign Require Import FormedWeakening.
From P04Preservation Require Import CorePreservation AdministrativeReduction
  ConditionalBeta BetaPreservation.
Import ListNotations.
Import Formed FormedStructural CorePreservation.CorePreservation.

Module BetaTracePreservation.

(** Exactly the thirteen administrative/contextual constructors, with
    actual beta added. Recursive premises use this same extended relation,
    so beta may occur at any depth in the seven supported contexts.
    No typing or preservation proposition is a step premise. *)
Inductive step : Term -> Term -> Prop :=
  | beta : forall A body arg,
      step (App (Lambda A body) arg) (subst 0 arg body)
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

Theorem administrative_step_included : forall t u,
  AdministrativeReduction.step t u -> step t u.
Proof.
  intros t u H. induction H; econstructor; eauto.
Qed.

Theorem captured_step : forall t u, step t u -> Repaired.step t u.
Proof.
  intros t u H. induction H; econstructor; eauto.
Qed.

(** Formation must be recovered from the enclosing derivation, including
    arbitrary outer conversions. A body's typing alone need not certify
    that its local context was formed. *)
Lemma let_domain_formation : forall ctx t T,
  has_type ctx t T -> forall A v body,
  t = Let A v body -> exists i, has_type ctx A (type_level i).
Proof.
  intros ctx t T H. induction H; intros A0 v0 body0 Heq; inversion Heq; subst.
  - eexists; eassumption.
  - eapply IHhas_type1. reflexivity.
Qed.

Lemma lambda_body_context : forall ctx A body T,
  wf_context ctx -> has_type ctx (Lambda A body) T ->
  wf_context (ctx_extend ctx A).
Proof.
  intros ctx A body T Hwf Hty.
  destruct (ConditionalBeta.lambda_generation _ _ _ Hty _ _ eq_refl)
    as [B [eff [i [HA [Hbody Hconv]]]]].
  eapply wf_extend; eassumption.
Qed.

Lemma let_body_context : forall ctx A v body T,
  wf_context ctx -> has_type ctx (Let A v body) T ->
  wf_context (ctx_extend ctx A).
Proof.
  intros ctx A v body T Hwf Hty.
  destruct (let_domain_formation _ _ _ Hty _ _ _ eq_refl) as [i HA].
  eapply wf_extend; eassumption.
Qed.

Lemma pi_codomain_context : forall ctx A eff B T,
  wf_context ctx -> has_type ctx (Pi A eff B) T ->
  wf_context (ctx_extend ctx A).
Proof.
  intros ctx A eff B T Hwf Hty.
  destruct (pi_formation _ _ _ Hty _ _ _ eq_refl) as [i [j [HA HB]]].
  eapply wf_extend; eassumption.
Qed.

Theorem preservation : forall t u, step t u -> forall ctx T,
  wf_context ctx -> has_type ctx t T -> has_type ctx u T.
Proof.
  intros t u H. induction H; intros ctx T Hwf Hty.
  - eapply BetaPreservation.beta_preservation; eassumption.
  - eapply zeta_preservation; eauto.
  - eapply annotation_preservation; eauto.
  - eapply empty_defeasible_preservation; eauto.
  - eapply peel_preservation; eauto.
  - eapply wildcard_preservation; eauto.
  - eapply branch_skip_preservation; eauto.
  - eapply app_function_compatibility. exact Hty. reflexivity.
    intros U HU. eapply IHstep; eassumption.
  - eapply annotation_expression_compatibility. exact Hty. reflexivity.
    intros U HU. eapply IHstep; eassumption.
  - assert (Hlocal : wf_context (ctx_extend ctx A)).
    { eapply lambda_body_context; eassumption. }
    eapply lambda_body_compatibility. exact Hty. reflexivity.
    intros U HU. eapply IHstep; eassumption.
  - assert (Hlocal : wf_context (ctx_extend ctx A)).
    { eapply let_body_context; eassumption. }
    eapply let_body_compatibility. exact Hty. reflexivity.
    intros U HU. eapply IHstep; eassumption.
  - eapply defeasible_body_compatibility. exact Hty. reflexivity.
    intros U HU. eapply IHstep; eassumption.
  - eapply match_scrutinee_compatibility. exact Hty. reflexivity.
    intros U HU. eapply IHstep; eassumption.
  - assert (Hlocal : wf_context (ctx_extend ctx A)).
    { eapply pi_codomain_context; eassumption. }
    eapply pi_codomain_compatibility. exact Hty. reflexivity.
    intros U HU. eapply IHstep; eassumption.
Qed.

Inductive steps : Term -> Term -> Prop :=
  | reflexive : forall t, steps t t
  | next : forall t u v, step t u -> steps u v -> steps t v.

Theorem administrative_steps_included : forall t u,
  AdministrativeReduction.steps t u -> steps t u.
Proof.
  intros t u H. induction H.
  - apply reflexive.
  - eapply next. apply administrative_step_included. exact H. exact IHsteps.
Qed.

Theorem captured_steps : forall t u, steps t u -> Repaired.steps t u.
Proof.
  intros t u H. induction H.
  - apply Repaired.steps_refl.
  - eapply Repaired.steps_trans. apply captured_step. exact H. exact IHsteps.
Qed.

Theorem trace_preservation : forall t u, steps t u -> forall ctx T,
  wf_context ctx -> has_type ctx t T -> has_type ctx u T.
Proof.
  intros t u H. induction H; intros ctx T Hwf Hty; auto.
  apply IHsteps; [exact Hwf |]. eapply preservation; eassumption.
Qed.

Theorem typed_captured_trace : forall ctx t u T,
  wf_context ctx -> has_type ctx t T -> steps t u ->
  Repaired.steps t u /\ has_type ctx u T.
Proof.
  intros ctx t u T Hwf Hty Hsteps. split.
  - apply captured_steps. exact Hsteps.
  - eapply trace_preservation; eassumption.
Qed.

Check administrative_step_included.
Print Assumptions administrative_step_included.
Check captured_step.
Print Assumptions captured_step.
Check let_domain_formation.
Print Assumptions let_domain_formation.
Check lambda_body_context.
Print Assumptions lambda_body_context.
Check let_body_context.
Print Assumptions let_body_context.
Check pi_codomain_context.
Print Assumptions pi_codomain_context.
Check preservation.
Print Assumptions preservation.
Check administrative_steps_included.
Print Assumptions administrative_steps_included.
Check captured_steps.
Print Assumptions captured_steps.
Check trace_preservation.
Print Assumptions trace_preservation.
Check typed_captured_trace.
Print Assumptions typed_captured_trace.
End BetaTracePreservation.
