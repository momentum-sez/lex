From Stdlib Require Import Bool String.
Open Scope string_scope.

(** ADGM FSRA fit-and-proper example with a typed discretion hole
    discharged by a matching PCAuth witness. *)

Inductive ComplianceVerdict : Type :=
  | Compliant
  | NonCompliant
  | Pending.

Inductive FitAndProperStatus : Type :=
  | FitAndProperSatisfied
  | FitAndProperUnderReview
  | FitAndProperPending.

Record AuthorizedFirmContext : Type := {
  fit_and_proper_status : FitAndProperStatus;
}.

Record DiscretionHole : Type := {
  hole_id : string;
  hole_authority : string;
}.

Definition fp_h : DiscretionHole :=
  {| hole_id := "fp_h"; hole_authority := "ADGM_FSRA" |}.

Inductive Evaluation : Type :=
  | Resolved : ComplianceVerdict -> Evaluation
  | NeedsDiscretion : DiscretionHole -> Evaluation.

Definition adgm_fit_and_proper_rule (ctx : AuthorizedFirmContext) : Evaluation :=
  match ctx.(fit_and_proper_status) with
  | FitAndProperSatisfied => Resolved Compliant
  | FitAndProperUnderReview => Resolved Pending
  | FitAndProperPending => NeedsDiscretion fp_h
  end.

Definition adgm_fit_and_proper_rule_typechecks :
  AuthorizedFirmContext -> Evaluation :=
  adgm_fit_and_proper_rule.

Record PCAuth : Type := {
  pcauth_authority : string;
  pcauth_hole_id : string;
  pcauth_signer : string;
}.

Definition fill_discretion
    (result : Evaluation)
    (judgment : ComplianceVerdict)
    (witness : PCAuth) : option ComplianceVerdict :=
  match result with
  | Resolved verdict => Some verdict
  | NeedsDiscretion hole =>
      if andb (String.eqb hole.(hole_authority) witness.(pcauth_authority))
              (String.eqb hole.(hole_id) witness.(pcauth_hole_id))
      then Some judgment
      else None
  end.

Definition satisfied_ctx : AuthorizedFirmContext :=
  {| fit_and_proper_status := FitAndProperSatisfied |}.

Definition under_review_ctx : AuthorizedFirmContext :=
  {| fit_and_proper_status := FitAndProperUnderReview |}.

Definition pending_ctx : AuthorizedFirmContext :=
  {| fit_and_proper_status := FitAndProperPending |}.

Definition valid_pcauth : PCAuth :=
  {| pcauth_authority := "ADGM_FSRA";
     pcauth_hole_id := "fp_h";
     pcauth_signer := "did:example:officer-9b2c" |}.

Definition invalid_pcauth : PCAuth :=
  {| pcauth_authority := "DIFC_DFSA";
     pcauth_hole_id := "fp_h";
     pcauth_signer := "did:example:outsider-77" |}.

Example satisfied_ctx_resolves_immediately :
  adgm_fit_and_proper_rule satisfied_ctx = Resolved Compliant.
Proof. reflexivity. Qed.

Example under_review_ctx_is_pending :
  adgm_fit_and_proper_rule under_review_ctx = Resolved Pending.
Proof. reflexivity. Qed.

Example pending_ctx_requests_fsra_discretion :
  adgm_fit_and_proper_rule pending_ctx = NeedsDiscretion fp_h.
Proof. reflexivity. Qed.

Example valid_fill_discharges_the_hole :
  fill_discretion (adgm_fit_and_proper_rule pending_ctx) Compliant valid_pcauth =
  Some Compliant.
Proof. reflexivity. Qed.

Example invalid_fill_is_rejected :
  fill_discretion (adgm_fit_and_proper_rule pending_ctx) Compliant invalid_pcauth =
  None.
Proof. reflexivity. Qed.

(** ** Additional fit-and-proper properties (2026-04-20) *)

(** Fill on a Resolved evaluation never needs a witness and never
    rejects: it returns the same verdict the rule resolved to,
    regardless of the candidate judgment or witness. *)
Theorem fill_resolved_ignores_witness :
  forall v j w,
    fill_discretion (Resolved v) j w = Some v.
Proof. intros v j w. reflexivity. Qed.

(** Wrong-hole-id rejection: a witness with the right authority but
    wrong hole_id is rejected. *)
Example wrong_hole_id_is_rejected :
  fill_discretion (adgm_fit_and_proper_rule pending_ctx) Compliant
    {| pcauth_authority := "ADGM_FSRA";
       pcauth_hole_id := "other_hole";
       pcauth_signer := "did:example:officer-9b2c" |} = None.
Proof. reflexivity. Qed.

(** A valid fill with NonCompliant as the candidate judgment emits
    NonCompliant — the rule does not substantively vet the filler's
    decision, only the authority / hole-id binding. *)
Example valid_fill_noncompliant :
  fill_discretion (adgm_fit_and_proper_rule pending_ctx) NonCompliant
    valid_pcauth = Some NonCompliant.
Proof. reflexivity. Qed.

(** The satisfied and under-review contexts never need discretion;
    the pending context does need it. *)
Theorem no_discretion_when_resolved :
  adgm_fit_and_proper_rule satisfied_ctx = Resolved Compliant /\
  adgm_fit_and_proper_rule under_review_ctx = Resolved Pending /\
  (exists h, adgm_fit_and_proper_rule pending_ctx = NeedsDiscretion h).
Proof. repeat split. exists fp_h. reflexivity. Qed.

Eval cbv in (adgm_fit_and_proper_rule satisfied_ctx).
Eval cbv in (adgm_fit_and_proper_rule under_review_ctx).
Eval cbv in (adgm_fit_and_proper_rule pending_ctx).
Eval cbv in
  (fill_discretion (adgm_fit_and_proper_rule pending_ctx) Compliant valid_pcauth).
