From Stdlib Require Import Bool List.
Import ListNotations.

(** Seychelles International Business Companies Act, s.66:
    at least one director must be a natural person. *)

Inductive ComplianceVerdict : Type :=
  | Compliant
  | NonCompliant.

Record Director : Type := {
  is_natural_person : bool;
}.

Record CompanyContext : Type := {
  directors : list Director;
}.

Definition has_natural_person_director (ctx : CompanyContext) : bool :=
  existsb is_natural_person ctx.(directors).

Definition seychelles_s66_rule (ctx : CompanyContext) : ComplianceVerdict :=
  if has_natural_person_director ctx then Compliant else NonCompliant.

Definition seychelles_s66_rule_typechecks :
  CompanyContext -> ComplianceVerdict :=
  seychelles_s66_rule.

Definition empty_board_ctx : CompanyContext :=
  {| directors := [] |}.

Definition all_corporate_ctx : CompanyContext :=
  {| directors := [{| is_natural_person := false |};
                   {| is_natural_person := false |}] |}.

Definition mixed_board_ctx : CompanyContext :=
  {| directors := [{| is_natural_person := false |};
                   {| is_natural_person := true |}] |}.

Example empty_board_is_noncompliant :
  seychelles_s66_rule empty_board_ctx = NonCompliant.
Proof. reflexivity. Qed.

Example corporate_only_board_is_noncompliant :
  seychelles_s66_rule all_corporate_ctx = NonCompliant.
Proof. reflexivity. Qed.

Example mixed_board_is_compliant :
  seychelles_s66_rule mixed_board_ctx = Compliant.
Proof. reflexivity. Qed.

(** ** Additional worked examples (2026-04-20) *)

Definition all_natural_ctx : CompanyContext :=
  {| directors := [{| is_natural_person := true |};
                   {| is_natural_person := true |}] |}.

Example all_natural_board_is_compliant :
  seychelles_s66_rule all_natural_ctx = Compliant.
Proof. reflexivity. Qed.

Definition single_natural_ctx : CompanyContext :=
  {| directors := [{| is_natural_person := true |}] |}.

Example single_natural_board_is_compliant :
  seychelles_s66_rule single_natural_ctx = Compliant.
Proof. reflexivity. Qed.

(** Adding a natural person director to a compliant company preserves
    compliance. *)
Theorem add_natural_preserves_compliance :
  forall (ctx : CompanyContext),
    seychelles_s66_rule ctx = Compliant ->
    seychelles_s66_rule
      {| directors := {| is_natural_person := true |} :: ctx.(directors) |}
      = Compliant.
Proof.
  intros ctx H. unfold seychelles_s66_rule, has_natural_person_director in *.
  simpl. reflexivity.
Qed.

(** A corporate-only director cannot make an all-corporate board
    compliant. *)
Theorem add_corporate_does_not_create_compliance :
  forall (ctx : CompanyContext),
    seychelles_s66_rule ctx = NonCompliant ->
    seychelles_s66_rule
      {| directors := {| is_natural_person := false |} :: ctx.(directors) |}
      = NonCompliant.
Proof.
  intros ctx H. unfold seychelles_s66_rule, has_natural_person_director in *.
  simpl. exact H.
Qed.

Eval cbv in (seychelles_s66_rule empty_board_ctx).
Eval cbv in (seychelles_s66_rule all_corporate_ctx).
Eval cbv in (seychelles_s66_rule mixed_board_ctx).
