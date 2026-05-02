From Stdlib Require Import Bool String.
Open Scope string_scope.

(** Cross-jurisdictional ADGM/DIFC mutual-recognition example using
    tribunal-indexed judgments and an explicit bridge witness. *)

Inductive ComplianceVerdict : Type :=
  | Compliant
  | NonCompliant
  | Pending.

Inductive Tribunal : Type :=
  | ADGM_FSRA
  | DIFC_DFSA.

Record TribunalModal (tribunal : Tribunal) : Type := {
  tribunal_verdict : ComplianceVerdict;
}.

Record BridgeWitness (from to : Tribunal) : Type := {
  bridge_name : string;
}.

Definition coerce_modal
    {from to : Tribunal}
    (bridge : BridgeWitness from to)
    (judgment : TribunalModal from) : TribunalModal to :=
  match bridge with
  | {| bridge_name := _ |} =>
      match judgment with
      | {| tribunal_verdict := verdict |} =>
          {| tribunal_verdict := verdict |}
      end
  end.

Definition apply_bridge
    {from to : Tribunal}
    (recognition_enabled : bool)
    (bridge : BridgeWitness from to)
    (judgment : TribunalModal from) : option (TribunalModal to) :=
  if recognition_enabled then Some (coerce_modal bridge judgment) else None.

Definition adgm_difc_mutual_recognition_rule_typechecks :
  bool ->
  BridgeWitness ADGM_FSRA DIFC_DFSA ->
  TribunalModal ADGM_FSRA ->
  option (TribunalModal DIFC_DFSA) :=
  apply_bridge.

Definition adgm_authorization_verdict : TribunalModal ADGM_FSRA :=
  {| tribunal_verdict := Compliant |}.

Definition adgm_to_difc_bridge : BridgeWitness ADGM_FSRA DIFC_DFSA :=
  {| bridge_name := "ADGM-DIFC-mutual-recognition" |}.

Example enabled_bridge_preserves_the_verdict :
  apply_bridge true adgm_to_difc_bridge adgm_authorization_verdict =
  Some {| tribunal_verdict := Compliant |}.
Proof. reflexivity. Qed.

Example disabled_bridge_blocks_the_coercion :
  apply_bridge false adgm_to_difc_bridge adgm_authorization_verdict = None.
Proof. reflexivity. Qed.

(** ** Further bridge-semantics properties (2026-04-20) *)

(** coerce_modal preserves the verdict (identity on the payload). *)
Theorem coerce_modal_preserves_verdict :
  forall from to (bridge : BridgeWitness from to) (j : TribunalModal from),
    tribunal_verdict to (coerce_modal bridge j) = tribunal_verdict from j.
Proof.
  intros from to bridge j. destruct bridge, j. reflexivity.
Qed.

(** Enabled-bridge preserves the verdict from ADGM to DIFC for
    any input verdict. *)
Theorem enabled_bridge_preserves_any_verdict :
  forall v,
    apply_bridge true adgm_to_difc_bridge
      {| tribunal_verdict := v |} =
    Some {| tribunal_verdict := v |}.
Proof. intros v. reflexivity. Qed.

(** Disabled-bridge blocks regardless of the input verdict. *)
Theorem disabled_bridge_blocks_any_verdict :
  forall v,
    apply_bridge false adgm_to_difc_bridge
      {| tribunal_verdict := v |} = None.
Proof. intros v. reflexivity. Qed.

(** The recognition toggle is the exact gate between Some and None. *)
Theorem recognition_toggle_dichotomy :
  forall v,
    (apply_bridge true adgm_to_difc_bridge
      {| tribunal_verdict := v |} <>
     apply_bridge false adgm_to_difc_bridge
      {| tribunal_verdict := v |}).
Proof. intros v. discriminate. Qed.

Eval cbv in (apply_bridge true adgm_to_difc_bridge adgm_authorization_verdict).
Eval cbv in (apply_bridge false adgm_to_difc_bridge adgm_authorization_verdict).
