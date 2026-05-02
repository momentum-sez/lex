(** * Lex/PackReevaluation.v

    Pack-relative re-evaluation for derived legal time.

    A pack-derived legal time is represented as a closure over the frozen
    [Time0] fact that generated it, the pack under which it was derived, and
    the pack-relative witness for that derivation.  Re-evaluation transports
    the witness along a typed rewrite from the old pack to the new pack; it
    does not alter the frozen source fact.
 *)

Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.micromega.Lia.

Import ListNotations.

Definition Time0 := nat.
Definition PackId := nat.
Definition RuleDigest := nat.
Definition RewriteDigest := nat.

Record pack : Type := mkPack {
  pack_id : PackId;
  pack_effective_date : Time0
}.

Record legal_witness (P : pack) : Type := mkLegalWitness {
  witness_digest : nat;
  witness_rule_digests : list RuleDigest
}.

Record rewrite_witness (P P' : pack) : Type := mkRewriteWitness {
  rewrite_digest : RewriteDigest;
  rewrite_effective_date_monotone :
    pack_effective_date P <= pack_effective_date P';
  rewrite_conservativity : Prop;
  rewrite_type_preservation : Prop;
  replay_witness : legal_witness P -> legal_witness P'
}.

Record derived_time : Type := derive_1 {
  src_0 : Time0;
  derivation_pack : pack;
  derivation_witness : legal_witness derivation_pack
}.

Definition reevaluate
    (t1 : derived_time) (P' : pack)
    (omega : rewrite_witness (derivation_pack t1) P') : derived_time :=
  derive_1
    (src_0 t1)
    P'
    (replay_witness _ _ omega (derivation_witness t1)).

Definition id_rewrite (P : pack) : rewrite_witness P P :=
  mkRewriteWitness P P 0 (le_n (pack_effective_date P)) True True (fun w => w).

Definition compose_rewrite
    {P Q R : pack}
    (omega_pq : rewrite_witness P Q)
    (omega_qr : rewrite_witness Q R) : rewrite_witness P R :=
  mkRewriteWitness
    P R
    (rewrite_digest P Q omega_pq + rewrite_digest Q R omega_qr)
    (Nat.le_trans
       (pack_effective_date P)
       (pack_effective_date Q)
       (pack_effective_date R)
       (rewrite_effective_date_monotone P Q omega_pq)
       (rewrite_effective_date_monotone Q R omega_qr))
    (rewrite_conservativity P Q omega_pq /\
     rewrite_conservativity Q R omega_qr)
    (rewrite_type_preservation P Q omega_pq /\
     rewrite_type_preservation Q R omega_qr)
    (fun w =>
       replay_witness _ _ omega_qr
         (replay_witness _ _ omega_pq w)).

(** Paper-level proposition: re-evaluation is exactly replay of the same
    frozen source through the transported pack witness. *)
Theorem re_evaluation_soundness :
  forall (t0 : Time0) (P P' : pack)
         (w : legal_witness P)
         (omega : rewrite_witness P P'),
    reevaluate (derive_1 t0 P w) P' omega =
    derive_1 t0 P' (replay_witness P P' omega w).
Proof.
  reflexivity.
Qed.

Theorem rewrite_effective_date_preserved :
  forall (P P' : pack) (omega : rewrite_witness P P'),
    pack_effective_date P <= pack_effective_date P'.
Proof.
  intros P P' omega.
  exact (rewrite_effective_date_monotone P P' omega).
Qed.

Theorem src_0_reevaluate :
  forall (t1 : derived_time) (P' : pack)
         (omega : rewrite_witness (derivation_pack t1) P'),
    src_0 (reevaluate t1 P' omega) = src_0 t1.
Proof.
  reflexivity.
Qed.

Theorem reevaluate_derivation_pack :
  forall (t1 : derived_time) (P' : pack)
         (omega : rewrite_witness (derivation_pack t1) P'),
    derivation_pack (reevaluate t1 P' omega) = P'.
Proof.
  reflexivity.
Qed.

Theorem reevaluate_id :
  forall t1 : derived_time,
    reevaluate t1 (derivation_pack t1) (id_rewrite (derivation_pack t1)) =
    t1.
Proof.
  intros [t0 P w].
  reflexivity.
Qed.

Theorem reevaluate_compose :
  forall (t1 : derived_time) (Q R : pack)
         (omega_pq : rewrite_witness (derivation_pack t1) Q)
         (omega_qr : rewrite_witness Q R),
    reevaluate (reevaluate t1 Q omega_pq) R omega_qr =
    reevaluate t1 R (compose_rewrite omega_pq omega_qr).
Proof.
  reflexivity.
Qed.

Inductive Time1 : Type :=
  | lift_0 : Time0 -> Time1
  | from_derived : derived_time -> Time1
  | toll : Time1 -> Time0 -> Time1.

Inductive source_event_kind : Type :=
  | SE_lift
  | SE_derive
  | SE_toll.

Record source_event : Type := mkSourceEvent {
  se_source : Time0;
  se_kind : source_event_kind;
  se_pack : option PackId;
  se_witness : option nat;
  se_rules : list RuleDigest
}.

Definition derive_event (d : derived_time) : source_event :=
  mkSourceEvent
    (src_0 d)
    SE_derive
    (Some (pack_id (derivation_pack d)))
    (Some (witness_digest _ (derivation_witness d)))
    (witness_rule_digests _ (derivation_witness d)).

Fixpoint source_history (t1 : Time1) : list source_event :=
  match t1 with
  | lift_0 t0 => [mkSourceEvent t0 SE_lift None None []]
  | from_derived d => [derive_event d]
  | toll d t_tol =>
      source_history d ++ [mkSourceEvent t_tol SE_toll None None []]
  end.

Definition source_times (events : list source_event) : list Time0 :=
  map se_source events.

Definition reevaluate_time1_derived
    (t1 : derived_time) (P' : pack)
    (omega : rewrite_witness (derivation_pack t1) P') : Time1 :=
  from_derived (reevaluate t1 P' omega).

Theorem source_history_reevaluate_derived :
  forall (t1 : derived_time) (P' : pack)
         (omega : rewrite_witness (derivation_pack t1) P'),
    source_times (source_history (reevaluate_time1_derived t1 P' omega)) =
    source_times (source_history (from_derived t1)).
Proof.
  reflexivity.
Qed.

Theorem source_history_reevaluate_pack :
  forall (t1 : derived_time) (P' : pack)
         (omega : rewrite_witness (derivation_pack t1) P'),
    se_pack (derive_event (reevaluate t1 P' omega)) =
    Some (pack_id P').
Proof.
  reflexivity.
Qed.

Theorem source_history_toll :
  forall (t1 : Time1) (t_tol : Time0),
    source_history (toll t1 t_tol) =
    source_history t1 ++ [mkSourceEvent t_tol SE_toll None None []].
Proof.
  reflexivity.
Qed.
