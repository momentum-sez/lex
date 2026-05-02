(** * Lex/AdmissionEnvelope.v -- Lex-to-Op admission carrier

    The admission boundary is the object an execution host checks before it
    treats a compiled Op payload as the activity authorized by Lex.  The
    carrier binds the exact Op payload digest to the Lex source, rule pack,
    context, compiler, primitive registry, gas schedule, receipts, and
    PCAuth-filled holes.

    This file proves the structural fail-closed facts.  It is not a proof of
    full Lex-to-Op adequacy or of cryptographic unforgeability.
*)

Require Import Stdlib.Lists.List.
Require Import Lex.ReceiptAlgebra.
Require Import Lex.PCAuthQuorum.

Import ListNotations.

Definition Digest := nat.
Definition EffectId := nat.
Definition PredicateId := nat.

Record observed_environment : Type := mkObservedEnvironment {
  oe_op_payload_digest : Digest;
  oe_lex_source_digest : Digest;
  oe_pack_digest : Digest;
  oe_context_digest : Digest;
  oe_compiler_digest : Digest;
  oe_registry_digest : Digest;
  oe_gas_schedule_digest : Digest
}.

Record admission_program : Type := mkAdmissionProgram {
  ap_op_payload_digest : Digest;
  ap_lex_source_digest : Digest;
  ap_pack_digest : Digest;
  ap_context_digest : Digest;
  ap_compiler_digest : Digest;
  ap_registry_digest : Digest;
  ap_gas_schedule_digest : Digest;
  ap_effect_row : list EffectId;
  ap_required_receipts : list ReceiptAlgebra.receipt;
  ap_pcauth_entries : list PCAuthQuorum.accepted_filled_hole;
  ap_failed_predicates : list PredicateId;
  ap_deferred_predicates : list PredicateId
}.

Definition empty_receipt : ReceiptAlgebra.receipt :=
  ReceiptAlgebra.mkReceipt
    VerdictHeyting.Compliant
    []
    []
    [].

Fixpoint fold_receipts (rs : list ReceiptAlgebra.receipt)
  : ReceiptAlgebra.receipt :=
  match rs with
  | [] => empty_receipt
  | r :: rest => ReceiptAlgebra.compose_receipt r (fold_receipts rest)
  end.

Theorem empty_receipt_accepted :
  ReceiptAlgebra.accepted empty_receipt.
Proof. unfold ReceiptAlgebra.accepted, empty_receipt; simpl; auto. Qed.

Theorem empty_receipt_compliant :
  ReceiptAlgebra.compliant empty_receipt.
Proof.
  unfold ReceiptAlgebra.compliant.
  split.
  - apply empty_receipt_accepted.
  - reflexivity.
Qed.

Theorem fold_receipts_accepted_iff :
  forall rs,
    ReceiptAlgebra.accepted (fold_receipts rs) <->
    Forall ReceiptAlgebra.accepted rs.
Proof.
  induction rs as [| r rest IH].
  - simpl. split; intros _.
    + constructor.
    + apply empty_receipt_accepted.
  - simpl. rewrite ReceiptAlgebra.accepted_compose_iff.
    rewrite IH.
    split.
    + intros [Hr Hrest]. constructor; assumption.
    + intros Hforall. inversion Hforall; subst. split; assumption.
Qed.

Theorem fold_receipts_compliant_iff :
  forall rs,
    ReceiptAlgebra.compliant (fold_receipts rs) <->
    Forall ReceiptAlgebra.compliant rs.
Proof.
  induction rs as [| r rest IH].
  - simpl. split; intros _.
    + constructor.
    + apply empty_receipt_compliant.
  - simpl. rewrite ReceiptAlgebra.compliant_compose_iff.
    rewrite IH.
    split.
    + intros [Hr Hrest]. constructor; assumption.
    + intros Hforall. inversion Hforall; subst. split; assumption.
Qed.

Definition exact_environment
    (p : admission_program) (env : observed_environment) : Prop :=
  oe_op_payload_digest env = ap_op_payload_digest p /\
  oe_lex_source_digest env = ap_lex_source_digest p /\
  oe_pack_digest env = ap_pack_digest p /\
  oe_context_digest env = ap_context_digest p /\
  oe_compiler_digest env = ap_compiler_digest p /\
  oe_registry_digest env = ap_registry_digest p /\
  oe_gas_schedule_digest env = ap_gas_schedule_digest p.

Definition all_pcauth_entries_verified
    (fills : list PCAuthQuorum.accepted_filled_hole) : Prop :=
  Forall
    (fun fill =>
       PCAuthQuorum.verify_pcauth
         (PCAuthQuorum.fill_witness fill)
         (PCAuthQuorum.fill_check fill))
    fills.

Theorem accepted_fills_are_verified :
  forall fills,
    all_pcauth_entries_verified fills.
Proof.
  induction fills as [| fill rest IH].
  - constructor.
  - constructor.
    + apply PCAuthQuorum.fill_verified.
    + exact IH.
Qed.

Definition admission_typechecks
    (p : admission_program) (env : observed_environment) : Prop :=
  exact_environment p env /\
  ReceiptAlgebra.accepted (fold_receipts (ap_required_receipts p)) /\
  ap_failed_predicates p = [] /\
  ap_deferred_predicates p = [] /\
  all_pcauth_entries_verified (ap_pcauth_entries p).

Theorem admission_exact_environment :
  forall p env,
    admission_typechecks p env ->
    exact_environment p env.
Proof.
  intros p env H.
  unfold admission_typechecks in H.
  tauto.
Qed.

Theorem admission_receipts_accepted :
  forall p env,
    admission_typechecks p env ->
    Forall ReceiptAlgebra.accepted (ap_required_receipts p).
Proof.
  intros p env H.
  unfold admission_typechecks in H.
  destruct H as [_ [Haccepted _]].
  apply fold_receipts_accepted_iff.
  exact Haccepted.
Qed.

Theorem receipt_to_bundle_preservation :
  forall p env r,
    admission_typechecks p env ->
    In r (ap_required_receipts p) ->
    ReceiptAlgebra.accepted r.
Proof.
  intros p env r Hadm Hin.
  pose proof (admission_receipts_accepted p env Hadm) as Hforall.
  induction Hforall as [| r' rest Hr Hrest IH].
  - contradiction.
  - simpl in Hin. destruct Hin as [Heq | Hin].
    + subst. exact Hr.
    + apply IH. exact Hin.
Qed.

Theorem admission_no_failed_or_deferred_predicates :
  forall p env,
    admission_typechecks p env ->
    ap_failed_predicates p = [] /\
    ap_deferred_predicates p = [].
Proof.
  intros p env H.
  unfold admission_typechecks in H.
  tauto.
Qed.

Theorem admission_pcauth_entries_verified :
  forall p env,
    admission_typechecks p env ->
    all_pcauth_entries_verified (ap_pcauth_entries p).
Proof.
  intros p env H.
  unfold admission_typechecks in H.
  tauto.
Qed.

Theorem admission_fails_closed_on_unaccepted_receipts :
  forall p env,
    ~ ReceiptAlgebra.accepted (fold_receipts (ap_required_receipts p)) ->
    ~ admission_typechecks p env.
Proof.
  intros p env Hnot Hadm.
  unfold admission_typechecks in Hadm.
  destruct Hadm as [_ [Haccepted _]].
  exact (Hnot Haccepted).
Qed.

Theorem admission_fails_closed_on_failed_predicates :
  forall p env,
    ap_failed_predicates p <> [] ->
    ~ admission_typechecks p env.
Proof.
  intros p env Hnot Hadm.
  unfold admission_typechecks in Hadm.
  destruct Hadm as [_ [_ [Hfailed _]]].
  exact (Hnot Hfailed).
Qed.

Theorem admission_fails_closed_on_payload_mismatch :
  forall p env,
    oe_op_payload_digest env <> ap_op_payload_digest p ->
    ~ admission_typechecks p env.
Proof.
  intros p env Hmismatch Hadm.
  pose proof (admission_exact_environment p env Hadm) as Hexact.
  unfold exact_environment in Hexact.
  destruct Hexact as [Hpayload _].
  exact (Hmismatch Hpayload).
Qed.
