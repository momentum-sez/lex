From Stdlib Require Import Bool String.
Open Scope string_scope.

(** Sanctions checks are non-defeasible: a sanctioned subject
    produces a non-compliant verdict and a bottom-like hard block. *)

Inductive ComplianceVerdict : Type :=
  | Compliant
  | NonCompliant
  | Pending.

Inductive SanctionsOracleResult : Type :=
  | Clear
  | Sanctioned : string -> SanctionsOracleResult.

Definition SanctionsOracle := string -> SanctionsOracleResult.

Record IncorporationContext : Type := {
  applicant_name : string;
}.

Inductive ComplianceOutcome : Type :=
  | Final : ComplianceVerdict -> ComplianceOutcome
  | BottomPropagated : ComplianceVerdict -> ComplianceOutcome.

Definition sanctions_rule
    (oracle : SanctionsOracle)
    (ctx : IncorporationContext) : ComplianceOutcome :=
  match oracle ctx.(applicant_name) with
  | Clear => Final Compliant
  | Sanctioned _ => BottomPropagated NonCompliant
  end.

Definition sanctions_rule_typechecks :
  SanctionsOracle -> IncorporationContext -> ComplianceOutcome :=
  sanctions_rule.

Definition downstream_override_attempt
    (outcome : ComplianceOutcome) : ComplianceOutcome :=
  match outcome with
  | Final _ => Final Pending
  | BottomPropagated verdict => BottomPropagated verdict
  end.

Definition clear_oracle (_ : string) : SanctionsOracleResult := Clear.

Definition blocked_oracle (company : string) : SanctionsOracleResult :=
  if String.eqb company "blocked-co" then Sanctioned company else Clear.

Definition clear_ctx : IncorporationContext :=
  {| applicant_name := "clear-co" |}.

Definition blocked_ctx : IncorporationContext :=
  {| applicant_name := "blocked-co" |}.

Example clear_subject_passes :
  sanctions_rule clear_oracle clear_ctx = Final Compliant.
Proof. reflexivity. Qed.

Example sanctioned_subject_is_noncompliant_and_bottom_propagates :
  sanctions_rule blocked_oracle blocked_ctx = BottomPropagated NonCompliant.
Proof. reflexivity. Qed.

Example bottom_propagates_through_downstream_override_attempt :
  downstream_override_attempt (sanctions_rule blocked_oracle blocked_ctx) =
  BottomPropagated NonCompliant.
Proof. reflexivity. Qed.

(** ** Additional worked examples (2026-04-20) *)

(** A clear subject, even if run through an override attempt,
    becomes Pending (since Final Compliant gets overridden). *)
Example clear_subject_override_becomes_pending :
  downstream_override_attempt (sanctions_rule clear_oracle clear_ctx) =
  Final Pending.
Proof. reflexivity. Qed.

(** A BottomPropagated result is always preserved under the override
    attempt — for any verdict. *)
Theorem bottom_always_preserved :
  forall v,
    downstream_override_attempt (BottomPropagated v) = BottomPropagated v.
Proof. intros v. reflexivity. Qed.

(** A Final result is always degraded to Final Pending under the
    override attempt. *)
Theorem final_always_becomes_pending :
  forall v,
    downstream_override_attempt (Final v) = Final Pending.
Proof. intros v. reflexivity. Qed.

(** sanctions_rule with the clear oracle on any context yields
    Final Compliant. *)
Theorem clear_oracle_is_compliant :
  forall ctx,
    sanctions_rule clear_oracle ctx = Final Compliant.
Proof. intros ctx. reflexivity. Qed.

Eval cbv in (sanctions_rule clear_oracle clear_ctx).
Eval cbv in (sanctions_rule blocked_oracle blocked_ctx).
Eval cbv in
  (downstream_override_attempt (sanctions_rule blocked_oracle blocked_ctx)).
