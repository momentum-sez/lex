From Stdlib Require Import Lists.List Arith.Arith Lia.
From Lex Require Import Syntax DeBruijn Typing.
From P04Source Require Import TypeReduction FormedTyping FormedRegularity RepairedReduction.
From P04RegularityDesign Require Import FormedWeakening.
From P04TypedSubstitution Require Import FormedSubstitution.
Import ListNotations.
Import Formed FormedStructural FormedSubstitution.FormedSubstitution.

Module CorePreservation.

(** These eliminations admit arbitrary outer conversion derivations. *)
Theorem annotation_preservation : forall ctx t T,
  has_type ctx t T -> forall e A, t = Annot e A -> has_type ctx e T.
Proof.
  intros ctx t T H. induction H; intros e0 A0 Heq; inversion Heq; subst.
  - assumption.
  - eapply T_Conv.
    + eapply IHhas_type1. reflexivity.
    + exact H0.
    + exact H1.
Qed.

Theorem zeta_preservation : forall ctx t T,
  has_type ctx t T -> forall A v body,
  t = Let A v body -> has_type ctx (subst 0 v body) T.
Proof.
  intros ctx t T H. induction H; intros A0 v0 body0 Heq; inversion Heq; subst.
  - eapply body_substitution; eassumption.
  - eapply T_Conv.
    + eapply IHhas_type1. reflexivity.
    + exact H0.
    + exact H1.
Qed.

Theorem empty_defeasible_preservation : forall ctx t T,
  has_type ctx t T -> forall A body,
  t = Defeasible A body [] -> has_type ctx body T.
Proof.
  intros ctx t T H. induction H; intros A0 body0 Heq; inversion Heq; subst.
  - assumption.
  - eapply T_Conv.
    + eapply IHhas_type1. reflexivity.
    + exact H0.
    + exact H1.
Qed.

(** This theorem concerns the captured peel rule's type only. It does not
    justify dropping a live exception in institutional execution. *)
Theorem peel_preservation : forall ctx t T,
  has_type ctx t T -> forall A body e rest,
  t = Defeasible A body (e :: rest) ->
  has_type ctx (Defeasible A body rest) T.
Proof.
  intros ctx t T H. induction H; intros A0 body0 e0 rest0 Heq; inversion Heq; subst.
  - eapply T_Defeasible; try eassumption.
    + inversion H1. assumption.
    + inversion H2. assumption.
  - eapply T_Conv.
    + eapply IHhas_type1. reflexivity.
    + exact H0.
    + exact H1.
Qed.

Theorem principal_beta_preservation : forall ctx A body B arg,
  has_type (ctx_extend ctx A) body B ->
  has_type ctx arg A ->
  has_type ctx (subst 0 arg body) (subst 0 arg B).
Proof. intros. eapply body_substitution; eassumption. Qed.

Theorem principal_beta_step : forall ctx A body B arg (eff : option EffectRow) i,
  has_type ctx A (type_level i) ->
  has_type (ctx_extend ctx A) body B ->
  has_type ctx arg A ->
  Repaired.step (App (Lambda A body) arg) (subst 0 arg body) /\
  has_type ctx (App (Lambda A body) arg) (subst 0 arg B) /\
  has_type ctx (subst 0 arg body) (subst 0 arg B).
Proof.
  intros ctx A body B arg eff i HA Hbody Harg.
  split. apply Repaired.step_beta.
  split.
  - eapply T_App with (eff:=eff). eapply T_Lambda; eassumption. exact Harg.
  - eapply principal_beta_preservation; eassumption.
Qed.

Print Assumptions annotation_preservation.
Print Assumptions zeta_preservation.
Print Assumptions empty_defeasible_preservation.
Print Assumptions peel_preservation.
Print Assumptions principal_beta_preservation.
Print Assumptions principal_beta_step.

Theorem wildcard_preservation : forall ctx t T,
  has_type ctx t T -> forall scr ret body rest,
  t = Match scr ret (MkBranch PWild body :: rest) -> has_type ctx body T.
Proof.
  intros ctx t T H. induction H; intros scr0 ret0 body0 rest0 Heq;
    inversion Heq; subst.
  - inversion H5; subst.
    match goal with
    | HB : has_type (ctx_extend_pattern _ (branch_pat _) _) _ _ |- _ =>
      cbn [branch_pat branch_body pattern_arity ctx_extend_pattern] in HB;
      rewrite shift_zero in HB; exact HB
    end.
  - eapply T_Conv.
    + eapply IHhas_type1. reflexivity.
    + exact H0.
    + exact H1.
Qed.

Theorem branch_skip_preservation : forall ctx t T,
  has_type ctx t T -> forall scr ret br rest,
  t = Match scr ret (br :: rest) -> rest <> [] ->
  has_type ctx (Match scr ret rest) T.
Proof.
  intros ctx t T H. induction H; intros scr0 ret0 br0 rest0 Heq Hrest;
    inversion Heq; subst.
  - destruct binder_tys_list as [|types tail]; simpl in H3; try discriminate.
    inversion H; subst. inversion H4; subst. inversion H5; subst.
    eapply T_Match with (binder_tys_list:=tail); eauto.
  - eapply T_Conv.
    + eapply IHhas_type1. reflexivity. exact Hrest.
    + exact H0.
    + exact H1.
Qed.

Theorem app_function_compatibility : forall ctx t T,
  has_type ctx t T -> forall f f' arg,
  t = App f arg ->
  (forall U, has_type ctx f U -> has_type ctx f' U) ->
  has_type ctx (App f' arg) T.
Proof.
  intros ctx t T H. induction H; intros f0 f' arg0 Heq Hreplace;
    inversion Heq; subst.
  - eapply T_App. apply Hreplace. exact H. exact H0.
  - eapply T_Conv.
    + eapply IHhas_type1. reflexivity. exact Hreplace.
    + exact H0.
    + exact H1.
Qed.

Theorem annotation_expression_compatibility : forall ctx t T,
  has_type ctx t T -> forall e e' A,
  t = Annot e A ->
  (forall U, has_type ctx e U -> has_type ctx e' U) ->
  has_type ctx (Annot e' A) T.
Proof.
  intros ctx t T H. induction H; intros e0 e' A0 Heq Hreplace;
    inversion Heq; subst.
  - eapply T_Annot. apply Hreplace. exact H. exact H0.
  - eapply T_Conv.
    + eapply IHhas_type1. reflexivity. exact Hreplace.
    + exact H0.
    + exact H1.
Qed.

Print Assumptions wildcard_preservation.
Print Assumptions branch_skip_preservation.
Print Assumptions app_function_compatibility.
Print Assumptions annotation_expression_compatibility.

Theorem lambda_body_compatibility : forall ctx t T,
  has_type ctx t T -> forall A body body',
  t = Lambda A body ->
  (forall U, has_type (ctx_extend ctx A) body U ->
    has_type (ctx_extend ctx A) body' U) ->
  has_type ctx (Lambda A body') T.
Proof.
  intros ctx t T H. induction H; intros A0 body0 body' Heq Hreplace;
    inversion Heq; subst.
  - eapply T_Lambda. exact H. apply Hreplace. exact H0.
  - eapply T_Conv.
    + eapply IHhas_type1. reflexivity. exact Hreplace.
    + exact H0.
    + exact H1.
Qed.

Theorem let_body_compatibility : forall ctx t T,
  has_type ctx t T -> forall A v body body',
  t = Let A v body ->
  (forall U, has_type (ctx_extend ctx A) body U ->
    has_type (ctx_extend ctx A) body' U) ->
  has_type ctx (Let A v body') T.
Proof.
  intros ctx t T H. induction H; intros A0 v0 body0 body' Heq Hreplace;
    inversion Heq; subst.
  - eapply T_Let. exact H. exact H0. apply Hreplace. exact H1.
  - eapply T_Conv.
    + eapply IHhas_type1. reflexivity. exact Hreplace.
    + exact H0.
    + exact H1.
Qed.

Theorem defeasible_body_compatibility : forall ctx t T,
  has_type ctx t T -> forall A body body' exns,
  t = Defeasible A body exns ->
  (forall U, has_type ctx body U -> has_type ctx body' U) ->
  has_type ctx (Defeasible A body' exns) T.
Proof.
  intros ctx t T H. induction H; intros A0 body0 body' exns0 Heq Hreplace;
    inversion Heq; subst.
  - eapply T_Defeasible. exact H. apply Hreplace. exact H0. exact H1. exact H2.
  - eapply T_Conv.
    + eapply IHhas_type1. reflexivity. exact Hreplace.
    + exact H0.
    + exact H1.
Qed.

Theorem match_scrutinee_compatibility : forall ctx t T,
  has_type ctx t T -> forall scr scr' ret branches,
  t = Match scr ret branches ->
  (forall U, has_type ctx scr U -> has_type ctx scr' U) ->
  has_type ctx (Match scr' ret branches) T.
Proof.
  intros ctx t T H. induction H; intros scr0 scr' ret0 branches0 Heq Hreplace;
    inversion Heq; subst.
  - eapply T_Match with (binder_tys_list:=binder_tys_list); try eassumption.
    apply Hreplace. exact H0.
  - eapply T_Conv.
    + eapply IHhas_type1. reflexivity. exact Hreplace.
    + exact H0.
    + exact H1.
Qed.

Theorem pi_codomain_compatibility : forall ctx t T,
  has_type ctx t T -> forall A eff B B',
  t = Pi A eff B ->
  (forall U, has_type (ctx_extend ctx A) B U ->
    has_type (ctx_extend ctx A) B' U) ->
  has_type ctx (Pi A eff B') T.
Proof.
  intros ctx t T H. induction H; intros A0 eff0 B0 B' Heq Hreplace;
    inversion Heq; subst.
  - eapply T_Pi. exact H. apply Hreplace. exact H0.
  - eapply T_Conv.
    + eapply IHhas_type1. reflexivity. exact Hreplace.
    + exact H0.
    + exact H1.
Qed.

Print Assumptions lambda_body_compatibility.
Print Assumptions let_body_compatibility.
Print Assumptions defeasible_body_compatibility.
Print Assumptions match_scrutinee_compatibility.
Print Assumptions pi_codomain_compatibility.

End CorePreservation.
