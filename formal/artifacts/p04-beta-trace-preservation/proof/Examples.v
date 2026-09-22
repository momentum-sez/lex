From Stdlib Require Import Lists.List.
From Lex Require Import Syntax DeBruijn Typing.
From P04Source Require Import TypeReduction FormedTyping RepairedReduction.
From P04Preservation Require Import AdministrativeReduction.
From P04BetaTrace Require Import BetaTracePreservation.
Import ListNotations.
Import Formed BetaTracePreservation.BetaTracePreservation.

(** The first beta is inside two lambda bodies and the function side of
    an application. The second beta is inside the outer lambda body. *)
Definition nested_source : Term :=
  Lambda (type_level 0)
    (App (Lambda (type_level 0)
      (App (Lambda (type_level 0) (Var 0)) (Var 0))) (TSort STime0)).

Definition nested_middle : Term :=
  Lambda (type_level 0)
    (App (Lambda (type_level 0) (Var 0)) (TSort STime0)).

Definition nested_target : Term := Lambda (type_level 0) (TSort STime0).
Definition nested_type : Term := Pi (type_level 0) None (type_level 0).

Example nested_source_typed : has_type [] nested_source nested_type.
Proof.
  unfold nested_source, nested_type.
  eapply T_Lambda with (i:=1).
  - apply T_Type. reflexivity.
  - eapply T_App with (A:=type_level 0) (B:=type_level 0) (eff:=None).
    + eapply T_Lambda with (i:=1).
      * apply T_Type. reflexivity.
      * eapply T_App with (A:=type_level 0) (B:=type_level 0) (eff:=None).
        -- eapply T_Lambda with (i:=1).
           ++ apply T_Type. reflexivity.
           ++ apply T_Var. reflexivity.
        -- apply T_Var. reflexivity.
    + apply T_Time0.
Qed.

Example nested_first_beta : step nested_source nested_middle.
Proof.
  unfold nested_source, nested_middle.
  apply lambda_body. apply app_function. apply lambda_body.
  change (step (App (Lambda (type_level 0) (Var 0)) (Var 0))
    (subst 0 (Var 0) (Var 0))).
  apply beta.
Qed.

Example nested_second_beta : step nested_middle nested_target.
Proof.
  unfold nested_middle, nested_target. apply lambda_body.
  change (step (App (Lambda (type_level 0) (Var 0)) (TSort STime0))
    (subst 0 (TSort STime0) (Var 0))).
  apply beta.
Qed.

Example nested_beta_trace : steps nested_source nested_target.
Proof.
  eapply next. exact nested_first_beta.
  eapply next. exact nested_second_beta.
  apply reflexive.
Qed.

Example nested_beta_trace_nonempty : nested_source <> nested_target.
Proof. discriminate. Qed.

Example nested_beta_typed_execution :
  Repaired.step nested_source nested_middle /\
  Repaired.step nested_middle nested_target /\
  has_type [] nested_middle nested_type /\
  has_type [] nested_target nested_type.
Proof.
  repeat split.
  - apply captured_step. exact nested_first_beta.
  - apply captured_step. exact nested_second_beta.
  - eapply preservation. exact nested_first_beta. apply wf_empty.
    exact nested_source_typed.
  - eapply trace_preservation. exact nested_beta_trace. apply wf_empty.
    exact nested_source_typed.
Qed.

(** An actual converted assigned result type is retained along the same
    nonempty execution; preservation is not limited to principal types. *)
Definition converted_nested_type : Term := Annot nested_type (type_level 1).

Lemma nested_type_formed : has_type [] nested_type (type_level 1).
Proof.
  unfold nested_type.
  change (has_type [] (Pi (type_level 0) None (type_level 0))
    (type_level (Nat.max 1 1))).
  eapply T_Pi; apply T_Type; reflexivity.
Qed.

Example nested_converted_source_typed :
  has_type [] nested_source converted_nested_type.
Proof.
  eapply T_Conv with (A:=nested_type) (i:=1).
  - exact nested_source_typed.
  - apply Conversion.convertible_sym.
    apply Conversion.convertible_step. apply Conversion.step_annot.
  - unfold converted_nested_type. eapply T_Annot with (i:=2).
    + exact nested_type_formed.
    + apply T_Type. reflexivity.
Qed.

Example nested_converted_trace :
  Repaired.steps nested_source nested_target /\
  has_type [] nested_target converted_nested_type.
Proof.
  eapply typed_captured_trace. apply wf_empty.
  exact nested_converted_source_typed. exact nested_beta_trace.
Qed.

(** The inner context depends on its predecessor: x : Type_0, y : x.
    Beta below both binders retains the dependent Pi result. *)
Definition dependent_nested_source : Term :=
  Lambda (type_level 0)
    (Lambda (Var 0) (App (Lambda (Var 1) (Var 0)) (Var 0))).

Definition dependent_nested_target : Term :=
  Lambda (type_level 0) (Lambda (Var 0) (Var 0)).

Definition dependent_nested_type : Term :=
  Pi (type_level 0) None (Pi (Var 0) None (Var 1)).

Example dependent_nested_source_typed :
  has_type [] dependent_nested_source dependent_nested_type.
Proof.
  unfold dependent_nested_source, dependent_nested_type.
  eapply T_Lambda with (i:=1).
  - apply T_Type. reflexivity.
  - eapply T_Lambda with (i:=0).
    + apply T_Var. reflexivity.
    + change (has_type (ctx_extend (ctx_extend [] (type_level 0)) (Var 0))
        (App (Lambda (Var 1) (Var 0)) (Var 0)) (subst 0 (Var 0) (Var 2))).
      eapply T_App with (A:=Var 1) (eff:=None).
      * eapply T_Lambda with (i:=0).
        -- apply T_Var. reflexivity.
        -- apply T_Var. reflexivity.
      * apply T_Var. reflexivity.
Qed.

Example dependent_nested_beta :
  step dependent_nested_source dependent_nested_target.
Proof.
  unfold dependent_nested_source, dependent_nested_target.
  apply lambda_body. apply lambda_body.
  change (step (App (Lambda (Var 1) (Var 0)) (Var 0))
    (subst 0 (Var 0) (Var 0))).
  apply beta.
Qed.

Example dependent_nested_typed_execution :
  Repaired.step dependent_nested_source dependent_nested_target /\
  has_type [] dependent_nested_target dependent_nested_type.
Proof.
  split.
  - apply captured_step. exact dependent_nested_beta.
  - eapply preservation. exact dependent_nested_beta. apply wf_empty.
    exact dependent_nested_source_typed.
Qed.

(** These two executions exercise the other extended-context cases. *)
Example beta_under_let :
  step (Let (type_level 0) (TSort STime0)
          (App (Lambda (type_level 0) (Var 0)) (Var 0)))
       (Let (type_level 0) (TSort STime0) (Var 0)).
Proof.
  apply let_body.
  change (step (App (Lambda (type_level 0) (Var 0)) (Var 0))
    (subst 0 (Var 0) (Var 0))). apply beta.
Qed.

Example beta_under_let_typed :
  has_type [] (Let (type_level 0) (TSort STime0) (Var 0)) (type_level 0).
Proof.
  eapply preservation. exact beta_under_let. apply wf_empty.
  change (has_type []
    (Let (type_level 0) (TSort STime0)
      (App (Lambda (type_level 0) (Var 0)) (Var 0)))
    (subst 0 (TSort STime0) (type_level 0))).
  eapply T_Let with (i:=1).
  - apply T_Type. reflexivity.
  - apply T_Time0.
  - eapply T_App with (A:=type_level 0) (B:=type_level 0) (eff:=None).
    + eapply T_Lambda with (i:=1).
      * apply T_Type. reflexivity.
      * apply T_Var. reflexivity.
    + apply T_Var. reflexivity.
Qed.

Example beta_under_pi :
  step (Pi (type_level 0) None
          (App (Lambda (type_level 0) (Var 0)) (TSort STime0)))
       (Pi (type_level 0) None (TSort STime0)).
Proof.
  apply pi_codomain.
  change (step (App (Lambda (type_level 0) (Var 0)) (TSort STime0))
    (subst 0 (TSort STime0) (Var 0))). apply beta.
Qed.

Example beta_under_pi_typed :
  has_type [] (Pi (type_level 0) None (TSort STime0)) (type_level 1).
Proof.
  eapply preservation. exact beta_under_pi. apply wf_empty.
  change (has_type []
    (Pi (type_level 0) None
      (App (Lambda (type_level 0) (Var 0)) (TSort STime0)))
    (type_level (Nat.max 1 0))).
  eapply T_Pi.
  - apply T_Type. reflexivity.
  - eapply T_App with (A:=type_level 0) (B:=type_level 0) (eff:=None).
    + eapply T_Lambda with (i:=1).
      * apply T_Type. reflexivity.
      * apply T_Var. reflexivity.
    + apply T_Time0.
Qed.

Check nested_source_typed.
Print Assumptions nested_source_typed.
Check nested_first_beta.
Print Assumptions nested_first_beta.
Check nested_second_beta.
Print Assumptions nested_second_beta.
Check nested_beta_trace.
Print Assumptions nested_beta_trace.
Check nested_beta_trace_nonempty.
Print Assumptions nested_beta_trace_nonempty.
Check nested_beta_typed_execution.
Print Assumptions nested_beta_typed_execution.
Check nested_converted_trace.
Print Assumptions nested_converted_trace.
Check dependent_nested_typed_execution.
Print Assumptions dependent_nested_typed_execution.
Check beta_under_let_typed.
Print Assumptions beta_under_let_typed.
Check beta_under_pi_typed.
Print Assumptions beta_under_pi_typed.
