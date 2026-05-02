(** * Lex/PCAuthQuorum.v

    Structural quorum extraction for proof-carrying authorization witnesses.

    This file deliberately proves only the verifier-unfolding fact: if the
    finite PCAuth verifier accepts a quorum bundle, then the bundle exposes at
    least the policy-required number of distinct signer attestations, all drawn
    from the policy committee, bound to the exact canonical payload, and valid
    at the admission snapshot.  It does not prove adversarial unforgeability of
    the signature scheme, credential issuance, or bulletin availability.
 *)

Require Import Stdlib.Lists.List.
Require Import Stdlib.micromega.Lia.

Import ListNotations.

Definition SignerId := nat.
Definition AuthorityId := nat.
Definition HoleId := nat.
Definition ValueDigest := nat.
Definition ChainDigest := nat.
Definition ScopeDigest := nat.
Definition AnchorDigest := nat.
Definition RequestDigest := nat.
Definition FillModeDigest := nat.
Definition LedgerDigest := nat.
Definition PackDigest := nat.
Definition ContextDigest := nat.
Definition Time := nat.
Definition ProtocolTag := nat.
Definition CanonVersion := nat.
Definition HashSuite := nat.
Definition SigAlg := nat.
Definition CommitteeDigest := nat.

Record hole_policy : Type := mkHolePolicy {
  hp_authority : AuthorityId;
  hp_hole : HoleId;
  hp_required : nat;
  hp_committee : list SignerId;
  hp_committee_digest : CommitteeDigest;
  hp_max_quorum_width : nat;
  hp_depth_bound : nat;
  hp_scope : ScopeDigest;
  hp_pack : PackDigest;
  hp_context : ContextDigest
}.

Record admission_check : Type := mkAdmissionCheck {
  ac_stamp : Time;
  ac_bulletin_position : Time;
  ac_stamp_visible : ac_stamp <= ac_bulletin_position
}.

Record signed_payload : Type := mkSignedPayload {
  sp_protocol : ProtocolTag;
  sp_canon_version : CanonVersion;
  sp_hash_suite : HashSuite;
  sp_sig_alg : SigAlg;
  sp_signer : SignerId;
  sp_authority : AuthorityId;
  sp_hole : HoleId;
  sp_value : ValueDigest;
  sp_chain : ChainDigest;
  sp_scope : ScopeDigest;
  sp_timestamp : Time;
  sp_anchor : AnchorDigest;
  sp_request : RequestDigest;
  sp_mode : FillModeDigest;
  sp_ledger : LedgerDigest;
  sp_pack : PackDigest;
  sp_context : ContextDigest
}.

Record signer_attestation : Type := mkSignerAttestation {
  att_signer : SignerId;
  att_chain : ChainDigest;
  att_scope : ScopeDigest;
  att_timestamp : Time;
  att_anchor : AnchorDigest;
  att_depth : nat;
  att_depth_bound : nat;
  att_payload : signed_payload;
  att_signature_valid : Prop;
  att_anchor_valid : Prop;
  att_chain_valid : Prop;
  att_chain_root : AuthorityId;
  att_chain_leaf : SignerId;
  att_chain_scope : ScopeDigest;
  att_not_revoked_at_check : Time -> Prop
}.

Record raw_pcauth_quorum : Type := mkRawPCAuthQuorum {
  pq_protocol : ProtocolTag;
  pq_canon_version : CanonVersion;
  pq_hash_suite : HashSuite;
  pq_sig_alg : SigAlg;
  pq_authority : AuthorityId;
  pq_hole : HoleId;
  pq_value : ValueDigest;
  pq_request : RequestDigest;
  pq_mode : FillModeDigest;
  pq_ledger : LedgerDigest;
  pq_pack : PackDigest;
  pq_context : ContextDigest;
  pq_required : nat;
  pq_policy : hole_policy;
  pq_attestations : list signer_attestation
}.

Definition expected_payload
    (w : raw_pcauth_quorum) (a : signer_attestation) : signed_payload :=
  mkSignedPayload
    (pq_protocol w)
    (pq_canon_version w)
    (pq_hash_suite w)
    (pq_sig_alg w)
    (att_signer a)
    (pq_authority w)
    (pq_hole w)
    (pq_value w)
    (att_chain a)
    (att_scope a)
    (att_timestamp a)
    (att_anchor a)
    (pq_request w)
    (pq_mode w)
    (pq_ledger w)
    (pq_pack w)
    (pq_context w).

Definition signer_valid_for
    (w : raw_pcauth_quorum) (check : admission_check)
    (a : signer_attestation) : Prop :=
  att_payload a = expected_payload w a /\
  In (att_signer a) (hp_committee (pq_policy w)) /\
  att_depth a <= att_depth_bound a /\
  att_depth a <= hp_depth_bound (pq_policy w) /\
  att_signature_valid a /\
  att_anchor_valid a /\
  att_chain_valid a /\
  att_chain_root a = pq_authority w /\
  att_chain_leaf a = att_signer a /\
  att_chain_scope a = hp_scope (pq_policy w) /\
  att_timestamp a <= ac_stamp check /\
  ac_stamp check <= ac_bulletin_position check /\
  att_not_revoked_at_check a (ac_stamp check).

Definition quorum_policy_bound (w : raw_pcauth_quorum) : Prop :=
  pq_authority w = hp_authority (pq_policy w) /\
  pq_hole w = hp_hole (pq_policy w) /\
  pq_required w = hp_required (pq_policy w) /\
  pq_required w <= hp_max_quorum_width (pq_policy w) /\
  length (hp_committee (pq_policy w)) <= hp_max_quorum_width (pq_policy w) /\
  pq_pack w = hp_pack (pq_policy w) /\
  pq_context w = hp_context (pq_policy w).

Definition verify_pcauth (w : raw_pcauth_quorum) (check : admission_check) : Prop :=
  quorum_policy_bound w /\
  pq_required w <= length (pq_attestations w) /\
  NoDup (map att_signer (pq_attestations w)) /\
  forall a,
    In a (pq_attestations w) ->
    signer_valid_for w check a.

Definition quorum_signers (w : raw_pcauth_quorum) : list SignerId :=
  map att_signer (pq_attestations w).

(** Paper-level theorem: accepted quorum witnesses expose the concrete quorum
    list whose signer identities are distinct and whose attestations all check
    against the exact payload. *)
Theorem quorum_acceptance_unfolding :
  forall (w : raw_pcauth_quorum) (check : admission_check),
    verify_pcauth w check ->
    exists Q : list signer_attestation,
      Q = pq_attestations w /\
      quorum_policy_bound w /\
      pq_required w <= length Q /\
      NoDup (map att_signer Q) /\
      forall a,
        In a Q ->
        signer_valid_for w check a.
Proof.
  intros w check Hverify.
  unfold verify_pcauth in Hverify.
  destruct Hverify as [Hpolicy [Hlen [Hdistinct Hall]]].
  exists (pq_attestations w).
  split; [reflexivity|].
  split; [exact Hpolicy|].
  split; [exact Hlen|].
  split; [exact Hdistinct|].
  exact Hall.
Qed.

Theorem quorum_has_required_distinct_signers :
  forall (w : raw_pcauth_quorum) (check : admission_check),
    verify_pcauth w check ->
    pq_required w <= length (pq_attestations w) /\
    NoDup (quorum_signers w).
Proof.
  intros w check Hverify.
  unfold verify_pcauth in Hverify.
  destruct Hverify as [_ [Hlen [Hdistinct _]]].
  split; [exact Hlen|exact Hdistinct].
Qed.

Theorem quorum_attestation_sound :
  forall (w : raw_pcauth_quorum) (check : admission_check)
         (a : signer_attestation),
    verify_pcauth w check ->
    In a (pq_attestations w) ->
    signer_valid_for w check a.
Proof.
  intros w check a Hverify Hin.
  unfold verify_pcauth in Hverify.
  destruct Hverify as [_ [_ [_ Hall]]].
  apply Hall.
  exact Hin.
Qed.

Theorem quorum_policy_binding :
  forall (w : raw_pcauth_quorum) (check : admission_check),
    verify_pcauth w check ->
    pq_authority w = hp_authority (pq_policy w) /\
    pq_hole w = hp_hole (pq_policy w) /\
    pq_required w = hp_required (pq_policy w) /\
    pq_required w <= hp_max_quorum_width (pq_policy w) /\
    length (hp_committee (pq_policy w)) <=
      hp_max_quorum_width (pq_policy w) /\
    pq_pack w = hp_pack (pq_policy w) /\
    pq_context w = hp_context (pq_policy w) /\
    Forall (fun s => In s (hp_committee (pq_policy w))) (quorum_signers w).
Proof.
  intros w check Hverify.
  unfold verify_pcauth in Hverify.
  destruct Hverify as [Hpolicy [_ [_ Hall]]].
  unfold quorum_policy_bound in Hpolicy.
  destruct Hpolicy as
      [Hauth [Hhole [Hrequired [Hmax [Hcommittee [Hpack Hcontext]]]]]].
  repeat split; try assumption.
  unfold quorum_signers.
  induction (pq_attestations w) as [| a rest IH].
  - constructor.
  - constructor.
    + apply Hall.
      simpl. left. reflexivity.
    + apply IH.
      intros a' Hin.
      apply Hall.
      simpl. right. exact Hin.
Qed.

Theorem quorum_exact_payload :
  forall (w : raw_pcauth_quorum) (check : admission_check)
         (a : signer_attestation),
    verify_pcauth w check ->
    In a (pq_attestations w) ->
    sp_protocol (att_payload a) = pq_protocol w /\
    sp_canon_version (att_payload a) = pq_canon_version w /\
    sp_hash_suite (att_payload a) = pq_hash_suite w /\
    sp_sig_alg (att_payload a) = pq_sig_alg w /\
    sp_authority (att_payload a) = pq_authority w /\
    sp_hole (att_payload a) = pq_hole w /\
    sp_value (att_payload a) = pq_value w /\
    sp_chain (att_payload a) = att_chain a /\
    sp_scope (att_payload a) = att_scope a /\
    sp_timestamp (att_payload a) = att_timestamp a /\
    sp_anchor (att_payload a) = att_anchor a /\
    sp_request (att_payload a) = pq_request w /\
    sp_mode (att_payload a) = pq_mode w /\
    sp_ledger (att_payload a) = pq_ledger w /\
    sp_pack (att_payload a) = pq_pack w /\
    sp_context (att_payload a) = pq_context w.
Proof.
  intros w check a Hverify Hin.
  pose proof (quorum_attestation_sound w check a Hverify Hin) as Hsound.
  unfold signer_valid_for in Hsound.
  destruct Hsound as [Hpayload _].
  rewrite Hpayload.
  repeat split.
Qed.

Theorem quorum_depth_bound :
  forall (w : raw_pcauth_quorum) (check : admission_check)
         (a : signer_attestation),
    verify_pcauth w check ->
    In a (pq_attestations w) ->
    att_depth a <= att_depth_bound a /\
    att_depth a <= hp_depth_bound (pq_policy w).
Proof.
  intros w check a Hverify Hin.
  pose proof (quorum_attestation_sound w check a Hverify Hin) as Hsound.
  unfold signer_valid_for in Hsound.
  tauto.
Qed.

Theorem quorum_signature_payload_binding :
  forall (w : raw_pcauth_quorum) (check : admission_check)
         (a : signer_attestation),
    verify_pcauth w check ->
    In a (pq_attestations w) ->
    att_signature_valid a /\
    att_payload a = expected_payload w a.
Proof.
  intros w check a Hverify Hin.
  pose proof (quorum_attestation_sound w check a Hverify Hin) as Hsound.
  unfold signer_valid_for in Hsound.
  tauto.
Qed.

Theorem quorum_anchor_chain_not_revoked :
  forall (w : raw_pcauth_quorum) (check : admission_check)
         (a : signer_attestation),
    verify_pcauth w check ->
    In a (pq_attestations w) ->
    att_anchor_valid a /\
    att_chain_valid a /\
    att_chain_root a = pq_authority w /\
    att_chain_leaf a = att_signer a /\
    att_chain_scope a = hp_scope (pq_policy w) /\
    att_not_revoked_at_check a (ac_stamp check).
Proof.
  intros w check a Hverify Hin.
  pose proof (quorum_attestation_sound w check a Hverify Hin) as Hsound.
  unfold signer_valid_for in Hsound.
  tauto.
Qed.

Theorem quorum_admission_time_bound :
  forall (w : raw_pcauth_quorum) (check : admission_check)
         (a : signer_attestation),
    verify_pcauth w check ->
    In a (pq_attestations w) ->
    att_timestamp a <= ac_stamp check /\
    ac_stamp check <= ac_bulletin_position check.
Proof.
  intros w check a Hverify Hin.
  pose proof (quorum_attestation_sound w check a Hverify Hin) as Hsound.
  unfold signer_valid_for in Hsound.
  tauto.
Qed.

Record accepted_filled_hole : Type := mkAcceptedFilledHole {
  fill_required : nat;
  fill_policy : hole_policy;
  fill_witness : raw_pcauth_quorum;
  fill_check : admission_check;
  fill_required_matches_witness :
    pq_required fill_witness = fill_required;
  fill_policy_matches_witness :
    pq_policy fill_witness = fill_policy;
  fill_verified :
    verify_pcauth fill_witness fill_check
}.

Theorem accepted_filled_hole_quorum :
  forall fill : accepted_filled_hole,
    exists Q : list signer_attestation,
      Q = pq_attestations (fill_witness fill) /\
      fill_required fill <= length Q /\
      fill_required fill = hp_required (fill_policy fill) /\
      NoDup (map att_signer Q) /\
      forall a,
        In a Q ->
        signer_valid_for (fill_witness fill) (fill_check fill) a.
Proof.
  intros fill.
  pose proof
    (quorum_acceptance_unfolding
       (fill_witness fill)
       (fill_check fill)
       (fill_verified fill)) as Hq.
  destruct Hq as [Q [HQ [Hpolicy [Hlen [Hdistinct Hall]]]]].
  unfold quorum_policy_bound in Hpolicy.
  destruct Hpolicy as [_ [_ [Hrequired _]]].
  exists Q.
  split; [exact HQ|].
  split.
  - rewrite <- fill_required_matches_witness.
    exact Hlen.
  - split.
    + rewrite <- fill_required_matches_witness.
      rewrite <- fill_policy_matches_witness.
      exact Hrequired.
    + split; [exact Hdistinct|exact Hall].
Qed.

Theorem accepted_filled_hole_payload_binding :
  forall (fill : accepted_filled_hole) (a : signer_attestation),
    In a (pq_attestations (fill_witness fill)) ->
    att_signature_valid a /\
    att_payload a = expected_payload (fill_witness fill) a /\
    sp_authority (att_payload a) = hp_authority (fill_policy fill) /\
    sp_hole (att_payload a) = hp_hole (fill_policy fill) /\
    sp_value (att_payload a) = pq_value (fill_witness fill) /\
    sp_request (att_payload a) = pq_request (fill_witness fill) /\
    sp_mode (att_payload a) = pq_mode (fill_witness fill) /\
    sp_pack (att_payload a) = hp_pack (fill_policy fill) /\
    sp_context (att_payload a) = hp_context (fill_policy fill).
Proof.
  intros fill a Hin.
  pose proof
    (quorum_signature_payload_binding
       (fill_witness fill)
       (fill_check fill)
       a
       (fill_verified fill)
       Hin) as [Hsig Hpayload].
  pose proof
    (quorum_policy_binding
       (fill_witness fill)
       (fill_check fill)
       (fill_verified fill)) as Hpolicy.
  destruct Hpolicy as
      [Hauth [Hhole [_ [_ [_ [Hpack [Hcontext _]]]]]]].
  repeat split; try exact Hsig; try exact Hpayload;
    rewrite Hpayload; simpl; try reflexivity.
  - rewrite Hauth. rewrite fill_policy_matches_witness. reflexivity.
  - rewrite Hhole. rewrite fill_policy_matches_witness. reflexivity.
  - rewrite Hpack. rewrite fill_policy_matches_witness. reflexivity.
  - rewrite Hcontext. rewrite fill_policy_matches_witness. reflexivity.
Qed.
