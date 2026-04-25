(** * Lex/TemporalStratification.v

    The object-language temporal stratum graph is directional.  Historical
    time [Time0] may be lifted into derived legal time [Time1], but the Lex
    temporal constructors expose no rule, and no generated path, from [Time1]
    back to [Time0].

    The result is intentionally syntactic: it is about the typing rules and
    generated coercion paths of Lex, not about arbitrary Coq functions between
    semantic carrier types.
 *)

Require Import Stdlib.Lists.List.

Import ListNotations.

Inductive TimeGrade : Type :=
  | Time0 : TimeGrade
  | Time1 : TimeGrade.

Inductive temporal_rule : list TimeGrade -> TimeGrade -> Type :=
  | TR_Date :
      temporal_rule [] Time0
  | TR_EffectiveDate :
      temporal_rule [Time0] Time0
  | TR_BulletinStamp :
      temporal_rule [Time0] Time0
  | TR_PCAuthTimestamp :
      temporal_rule [Time0] Time0
  | TR_Lift0 :
      temporal_rule [Time0] Time1
  | TR_Derive1 :
      temporal_rule [Time0] Time1
  | TR_Toll :
      temporal_rule [Time1; Time0] Time1
  | TR_Reevaluate :
      temporal_rule [Time1] Time1.

Theorem time0_rule_premises_are_time0 :
  forall (premises : list TimeGrade)
         (r : temporal_rule premises Time0),
    Forall (fun g => g = Time0) premises.
Proof.
  intros premises r.
  inversion r; subst; repeat constructor.
Qed.

Theorem no_time1_premise_to_time0_rule :
  forall (premises : list TimeGrade)
         (r : temporal_rule premises Time0),
    ~ In Time1 premises.
Proof.
  intros premises r Hin.
  pose proof (time0_rule_premises_are_time0 premises r) as Hall.
  rewrite Forall_forall in Hall.
  pose proof (Hall Time1 Hin) as Hbad.
  discriminate Hbad.
Qed.

Inductive temporal_derivation : TimeGrade -> Type :=
  | TD_Date :
      temporal_derivation Time0
  | TD_EffectiveDate :
      temporal_derivation Time0 -> temporal_derivation Time0
  | TD_BulletinStamp :
      temporal_derivation Time0 -> temporal_derivation Time0
  | TD_PCAuthTimestamp :
      temporal_derivation Time0 -> temporal_derivation Time0
  | TD_Lift0 :
      temporal_derivation Time0 -> temporal_derivation Time1
  | TD_Derive1 :
      temporal_derivation Time0 -> temporal_derivation Time1
  | TD_Toll :
      temporal_derivation Time1 ->
      temporal_derivation Time0 ->
      temporal_derivation Time1
  | TD_Reevaluate :
      temporal_derivation Time1 -> temporal_derivation Time1.

Fixpoint contains_time1_to_time0_step
    {g : TimeGrade} (d : temporal_derivation g) : Prop :=
  match d with
  | TD_Date => False
  | TD_EffectiveDate d0 => contains_time1_to_time0_step d0
  | TD_BulletinStamp d0 => contains_time1_to_time0_step d0
  | TD_PCAuthTimestamp d0 => contains_time1_to_time0_step d0
  | TD_Lift0 d0 => contains_time1_to_time0_step d0
  | TD_Derive1 d0 => contains_time1_to_time0_step d0
  | TD_Toll d1 d0 =>
      contains_time1_to_time0_step d1 \/
      contains_time1_to_time0_step d0
  | TD_Reevaluate d1 => contains_time1_to_time0_step d1
  end.

(** Paper-level theorem: a derivation of [Time0] cannot contain a temporal
    constructor step whose conclusion is [Time0] and whose premise is [Time1]. *)
Theorem temporal_non_regression :
  forall d : temporal_derivation Time0,
    ~ contains_time1_to_time0_step d.
Proof.
  intros d.
  induction d; simpl; tauto.
Qed.

Definition grade_le (g h : TimeGrade) : Prop :=
  match g, h with
  | Time0, Time0 => True
  | Time0, Time1 => True
  | Time1, Time0 => False
  | Time1, Time1 => True
  end.

Lemma grade_le_trans :
  forall a b c : TimeGrade,
    grade_le a b ->
    grade_le b c ->
    grade_le a c.
Proof.
  destruct a, b, c; simpl; tauto.
Qed.

Inductive temporal_path : TimeGrade -> TimeGrade -> Prop :=
  | TP_Refl :
      forall g, temporal_path g g
  | TP_Lift0 :
      temporal_path Time0 Time1
  | TP_Trans :
      forall a b c,
        temporal_path a b ->
        temporal_path b c ->
        temporal_path a c.

Theorem temporal_path_sound :
  forall a b : TimeGrade,
    temporal_path a b ->
    grade_le a b.
Proof.
  intros a b Hpath.
  induction Hpath.
  - destruct g; simpl; exact I.
  - simpl; exact I.
  - eapply grade_le_trans; eauto.
Qed.

Theorem no_temporal_retract :
  ~ temporal_path Time1 Time0.
Proof.
  intros Hpath.
  exact (temporal_path_sound Time1 Time0 Hpath).
Qed.
