From Stdlib Require Import Arith Bool.

(** Pakistan Companies Act 2017 directors' report example with
    stacked tolling witnesses. *)

Inductive ComplianceVerdict : Type :=
  | Compliant
  | NonCompliant.

Definition Time0 := nat.
Definition Time1 := nat.

Inductive RewriteWitness : Type :=
  | BaseDeadline : nat -> RewriteWitness
  | Toll : nat -> RewriteWitness -> RewriteWitness.

Fixpoint derive_1 (t0 : Time0) (witness : RewriteWitness) : Time1 :=
  match witness with
  | BaseDeadline days => t0 + days
  | Toll excluded inner => derive_1 t0 inner + excluded
  end.

Record DirectorsReportContext : Type := {
  cause_of_action_date : Time0;
  filed_on : Time1;
  first_toll_days : nat;
  second_toll_days : nat;
}.

Definition stacked_toll_witness (ctx : DirectorsReportContext) : RewriteWitness :=
  Toll ctx.(first_toll_days)
    (Toll ctx.(second_toll_days) (BaseDeadline 30)).

Definition directors_report_deadline (ctx : DirectorsReportContext) : Time1 :=
  derive_1 ctx.(cause_of_action_date) (stacked_toll_witness ctx).

Definition pakistan_directors_report_rule
    (ctx : DirectorsReportContext) : ComplianceVerdict :=
  if Nat.leb ctx.(filed_on) (directors_report_deadline ctx)
  then Compliant
  else NonCompliant.

Definition pakistan_directors_report_rule_typechecks :
  DirectorsReportContext -> ComplianceVerdict :=
  pakistan_directors_report_rule.

Definition timely_ctx : DirectorsReportContext :=
  {| cause_of_action_date := 100;
     filed_on := 149;
     first_toll_days := 7;
     second_toll_days := 14 |}.

Definition late_ctx : DirectorsReportContext :=
  {| cause_of_action_date := 100;
     filed_on := 152;
     first_toll_days := 7;
     second_toll_days := 14 |}.

Example stacked_toll_produces_expected_time_1 :
  directors_report_deadline timely_ctx = 151.
Proof. reflexivity. Qed.

Example timely_filing_is_compliant :
  pakistan_directors_report_rule timely_ctx = Compliant.
Proof. reflexivity. Qed.

Example late_filing_is_noncompliant :
  pakistan_directors_report_rule late_ctx = NonCompliant.
Proof. reflexivity. Qed.

(** ** Additional tolling properties (2026-04-20) *)

(** Each Toll constructor adds [excluded] days to the Time1
    deadline, regardless of any inner witness.  Tolls compose
    additively. *)
Theorem toll_adds_days :
  forall t0 excluded inner,
    derive_1 t0 (Toll excluded inner) = derive_1 t0 inner + excluded.
Proof. intros t0 excluded inner. reflexivity. Qed.

(** Base deadline at t0 adds exactly [days] to the cause-of-action
    date. *)
Theorem base_deadline_adds_days :
  forall t0 days,
    derive_1 t0 (BaseDeadline days) = t0 + days.
Proof. intros t0 days. reflexivity. Qed.

(** Stacked toll produces the expected Time1 deadline: base 30 +
    second_toll + first_toll + cause_of_action_date. *)
Theorem stacked_toll_formula :
  forall ctx,
    directors_report_deadline ctx =
    ctx.(cause_of_action_date) + 30 +
    ctx.(second_toll_days) + ctx.(first_toll_days).
Proof. intros ctx. reflexivity. Qed.

(** Filing on exactly the deadline is Compliant. *)
Example filing_on_deadline_is_compliant :
  pakistan_directors_report_rule
    {| cause_of_action_date := 100;
       filed_on := 151;
       first_toll_days := 7;
       second_toll_days := 14 |} = Compliant.
Proof. reflexivity. Qed.

Eval cbv in (stacked_toll_witness timely_ctx).
Eval cbv in (directors_report_deadline timely_ctx).
Eval cbv in (pakistan_directors_report_rule timely_ctx).
Eval cbv in (pakistan_directors_report_rule late_ctx).
