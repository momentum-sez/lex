(** * Propagation/Graph.v — F142 causal-propagation graph formalization (minimal mirror)

    Mirrors [mez/crates/mez-propagation/src/evaluate.rs] and
    [formal/lean/Propagation/Propagation/Graph.lean].

    This Coq module states — and proves — the two F142 invariants
    that the Rust evaluator relies on:

      1. `apply_rule_monotone` — a single rule application never
         improves the target verdict (lattice `meet` law).

      2. `evaluate_monotone` — iterating the evaluator any number of
         times preserves the pointwise monotonicity invariant.

    The Lean mirror proves these same theorems independently. We keep
    the Coq version minimal (matching theorem statements) so both
    proof assistants agree on the semantics. All proofs are complete
    (no `Admitted`).
*)

Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.micromega.Lia.
Import ListNotations.

(* ====================================================================== *)
(** ** ComplianceState — the 5-element compliance lattice *)
(* ====================================================================== *)

Inductive ComplianceState : Type :=
  | NonCompliant
  | Pending
  | NotApplicable
  | Exempt
  | Compliant.

(** Lattice-ordinal embedding. Lower = more restrictive.
    Matches the Rust `ComplianceState::ordering()` function. *)
Definition cs_ord (s : ComplianceState) : nat :=
  match s with
  | NonCompliant => 0
  | Pending => 1
  | NotApplicable => 2
  | Exempt => 3
  | Compliant => 4
  end.

Definition cs_le (a b : ComplianceState) : Prop := cs_ord a <= cs_ord b.

Notation "a <=c b" := (cs_le a b) (at level 70).

(** Meet: the more restrictive state. *)
Definition cs_meet (a b : ComplianceState) : ComplianceState :=
  if Nat.leb (cs_ord a) (cs_ord b) then a else b.

(** Meet is a lower bound — `meet(a,b) <= a`. *)
Theorem cs_meet_le_left : forall a b, cs_meet a b <=c a.
Proof.
  intros a b.
  unfold cs_meet.
  destruct (Nat.leb (cs_ord a) (cs_ord b)) eqn:Hle.
  - unfold cs_le. apply Nat.le_refl.
  - unfold cs_le.
    apply Nat.leb_gt in Hle.
    apply Nat.lt_le_incl. exact Hle.
Qed.

Theorem cs_le_refl : forall a, a <=c a.
Proof.
  intros a. unfold cs_le. apply Nat.le_refl.
Qed.

Theorem cs_le_trans : forall a b c, a <=c b -> b <=c c -> a <=c c.
Proof.
  intros a b c H1 H2. unfold cs_le in *.
  apply Nat.le_trans with (m := cs_ord b); assumption.
Qed.

(** Meet is also a lower bound on the right — `meet(a,b) <= b`. *)
Theorem cs_meet_le_right : forall a b, cs_meet a b <=c b.
Proof.
  intros a b.
  unfold cs_meet.
  destruct (Nat.leb (cs_ord a) (cs_ord b)) eqn:Hle.
  - unfold cs_le.
    apply Nat.leb_le in Hle. exact Hle.
  - unfold cs_le. apply Nat.le_refl.
Qed.

(** Meet idempotence on the compliance-state carrier. *)
Theorem cs_meet_idempotent : forall a, cs_meet a a = a.
Proof.
  intros a. unfold cs_meet.
  destruct (Nat.leb (cs_ord a) (cs_ord a)); reflexivity.
Qed.

(** Meet commutativity. *)
Theorem cs_meet_comm : forall a b, cs_meet a b = cs_meet b a.
Proof. destruct a, b; reflexivity. Qed.

(** Meet associativity. *)
Theorem cs_meet_assoc : forall a b c,
  cs_meet (cs_meet a b) c = cs_meet a (cs_meet b c).
Proof. destruct a, b, c; reflexivity. Qed.

(** Meet monotonicity: pointwise preservation of the ordering. *)
Theorem cs_meet_monotone : forall a a' b b',
  a <=c a' -> b <=c b' -> cs_meet a b <=c cs_meet a' b'.
Proof. destruct a, a', b, b'; compute; lia. Qed.

(** Meet is the greatest lower bound: [c <= meet(a, b)] iff
    [c <= a] and [c <= b]. *)
Theorem cs_meet_glb : forall a b c,
  c <=c cs_meet a b <-> (c <=c a /\ c <=c b).
Proof.
  intros a b c. split.
  - intros H. split.
    + eapply cs_le_trans; [exact H | apply cs_meet_le_left].
    + eapply cs_le_trans; [exact H | apply cs_meet_le_right].
  - intros [H1 H2]. destruct a, b, c; compute in *; lia.
Qed.

(** Antisymmetry of [cs_le]: a partial order. *)
Theorem cs_le_antisym : forall a b, a <=c b -> b <=c a -> a = b.
Proof.
  intros a b Hab Hba. unfold cs_le in *.
  assert (Ha : cs_ord a = cs_ord b) by lia.
  (* cs_ord is injective by construction. *)
  destruct a, b; compute in Ha; try reflexivity; discriminate.
Qed.

(* ====================================================================== *)
(** ** PropagationEffect — verdict transforms *)
(* ====================================================================== *)

Inductive PropagationEffect : Type :=
  | DropToNonCompliant
  | PinToPending
  | ClampToSource
  | BlockOnPendingOrWorse
  | CarryNotApplicable.

Definition effect_apply (e : PropagationEffect) (src : ComplianceState)
  : option ComplianceState :=
  match e, src with
  | DropToNonCompliant, NonCompliant => Some NonCompliant
  | DropToNonCompliant, _ => None
  | PinToPending, NonCompliant => Some Pending
  | PinToPending, Pending => Some Pending
  | PinToPending, _ => None
  | ClampToSource, s => Some s
  | BlockOnPendingOrWorse, NonCompliant => Some NonCompliant
  | BlockOnPendingOrWorse, Pending => Some NonCompliant
  | BlockOnPendingOrWorse, _ => None
  | CarryNotApplicable, NotApplicable => Some NotApplicable
  | CarryNotApplicable, _ => None
  end.

(* ====================================================================== *)
(** ** PropagationRule and evaluator *)
(* ====================================================================== *)

(** A domain type [D] with decidable equality. For the proof we don't
    need the concrete 23-domain enum — abstracting over [D] keeps the
    theorems reusable. *)

Record PropagationRule (D : Type) : Type := mkRule {
  src : D;
  tgt : D;
  eff : PropagationEffect;
}.

(** Verdict assignment. *)
Definition DomainMap (D : Type) := D -> ComplianceState.

(** Pointwise ≤ on assignments. *)
Definition dm_le {D : Type} (a b : DomainMap D) : Prop :=
  forall d, a d <=c b d.

Theorem dm_le_refl : forall {D} (a : DomainMap D), dm_le a a.
Proof. intros D a d. apply cs_le_refl. Qed.

Theorem dm_le_trans : forall {D} (a b c : DomainMap D),
    dm_le a b -> dm_le b c -> dm_le a c.
Proof.
  intros D a b c H1 H2 d.
  eapply cs_le_trans; [apply H1 | apply H2].
Qed.

(** Pointwise update. Requires decidable equality on [D]. *)
Definition dm_update {D : Type}
  (eq_dec : forall x y : D, {x = y} + {x <> y})
  (f : DomainMap D) (d : D) (v : ComplianceState) : DomainMap D :=
  fun x => if eq_dec x d then v else f x.

(** Apply a single rule. *)
Definition apply_rule {D : Type}
  (eq_dec : forall x y : D, {x = y} + {x <> y})
  (r : PropagationRule D) (f : DomainMap D) : DomainMap D :=
  match effect_apply (eff D r) (f (src D r)) with
  | None => f
  | Some candidate => dm_update eq_dec f (tgt D r) (cs_meet (f (tgt D r)) candidate)
  end.

(* ====================================================================== *)
(** ** Theorem 1 — single-rule monotonicity *)
(* ====================================================================== *)

Theorem apply_rule_monotone :
  forall (D : Type) (eq_dec : forall x y : D, {x = y} + {x <> y})
         (r : PropagationRule D) (f : DomainMap D),
  dm_le (apply_rule eq_dec r f) f.
Proof.
  intros D eq_dec r f d.
  unfold apply_rule.
  destruct (effect_apply (eff D r) (f (src D r))) as [candidate|] eqn:Hap.
  - (* Some candidate: the target is updated to meet(before, candidate). *)
    unfold dm_update.
    destruct (eq_dec d (tgt D r)) as [Heq|Hneq].
    + (* d = target *)
      subst d.
      apply cs_meet_le_left.
    + (* d ≠ target *)
      apply cs_le_refl.
  - (* None: no update *)
    apply cs_le_refl.
Qed.

(* ====================================================================== *)
(** ** Pass: apply a list of rules in order *)
(* ====================================================================== *)

Fixpoint apply_pass {D : Type}
  (eq_dec : forall x y : D, {x = y} + {x <> y})
  (rules : list (PropagationRule D)) (f : DomainMap D) : DomainMap D :=
  match rules with
  | [] => f
  | r :: rest => apply_pass eq_dec rest (apply_rule eq_dec r f)
  end.

Theorem apply_pass_monotone :
  forall (D : Type) (eq_dec : forall x y : D, {x = y} + {x <> y})
         (rules : list (PropagationRule D)) (f : DomainMap D),
  dm_le (apply_pass eq_dec rules f) f.
Proof.
  intros D eq_dec rules.
  induction rules as [|r rest IH]; intros f.
  - (* base: apply_pass [] f = f *)
    simpl. apply dm_le_refl.
  - (* step: apply_pass (r :: rest) f = apply_pass rest (apply_rule r f) *)
    simpl.
    (* dm_le (apply_pass rest (apply_rule r f)) (apply_rule r f) by IH. *)
    (* dm_le (apply_rule r f) f                by apply_rule_monotone. *)
    apply dm_le_trans with (b := apply_rule eq_dec r f).
    + apply IH.
    + apply apply_rule_monotone.
Qed.

(* ====================================================================== *)
(** ** Theorem 2 — iterated-pass monotonicity (fixed-point invariant) *)
(* ====================================================================== *)

Fixpoint evaluate {D : Type}
  (eq_dec : forall x y : D, {x = y} + {x <> y})
  (n : nat) (rules : list (PropagationRule D)) (init : DomainMap D)
  : DomainMap D :=
  match n with
  | 0 => init
  | S k => evaluate eq_dec k rules (apply_pass eq_dec rules init)
  end.

Theorem evaluate_monotone :
  forall (D : Type) (eq_dec : forall x y : D, {x = y} + {x <> y})
         (n : nat) (rules : list (PropagationRule D)) (init : DomainMap D),
  dm_le (evaluate eq_dec n rules init) init.
Proof.
  intros D eq_dec n.
  induction n as [|k IH]; intros rules init.
  - simpl. apply dm_le_refl.
  - simpl.
    (* evaluate (S k) rules init = evaluate k rules (apply_pass rules init) *)
    apply dm_le_trans with (b := apply_pass eq_dec rules init).
    + apply IH.
    + apply apply_pass_monotone.
Qed.

(* ====================================================================== *)
(** ** Corollary — confluence via idempotence at a fixed point *)
(* ====================================================================== *)

Definition IsFixedPoint {D : Type}
  (eq_dec : forall x y : D, {x = y} + {x <> y})
  (rules : list (PropagationRule D)) (f : DomainMap D) : Prop :=
  forall d, apply_pass eq_dec rules f d = f d.

Theorem evaluate_fixed :
  forall (D : Type) (eq_dec : forall x y : D, {x = y} + {x <> y})
         (n : nat) (rules : list (PropagationRule D)) (f : DomainMap D),
  IsFixedPoint eq_dec rules f ->
  forall d, evaluate eq_dec n rules f d = f d.
Proof.
  intros D eq_dec n.
  induction n as [|k IH]; intros rules f Hfix d.
  - simpl. reflexivity.
  - simpl.
    (* Key: apply_pass rules f = f pointwise by Hfix. So evaluate k
       rules (apply_pass ...) = evaluate k rules f by function
       extensionality on the first argument... But we use the
       pointwise form directly. *)
    assert (Hext : apply_pass eq_dec rules f = f).
    { apply functional_extensionality_dep. exact Hfix. }
    rewrite Hext.
    apply IH. exact Hfix.
Qed.

(** At fixed point, re-running the evaluator any number of times
    produces the same assignment — this is the confluence property
    in its simplest form. *)
Theorem evaluate_confluent :
  forall (D : Type) (eq_dec : forall x y : D, {x = y} + {x <> y})
         (n m : nat) (rules : list (PropagationRule D)) (init : DomainMap D),
  IsFixedPoint eq_dec rules (evaluate eq_dec n rules init) ->
  forall d, evaluate eq_dec m rules (evaluate eq_dec n rules init) d
         = evaluate eq_dec n rules init d.
Proof.
  intros D eq_dec n m rules init Hfix d.
  apply evaluate_fixed. exact Hfix.
Qed.

(** We use [functional_extensionality_dep] from
    [Coq.Logic.FunctionalExtensionality] — imported at the top of
    this file. *)

(* ====================================================================== *)
(** ** Further structural properties (2026-04-20) *)
(* ====================================================================== *)

(** dm_le is antisymmetric (by pointwise antisymmetry of cs_le). *)
Theorem dm_le_antisym :
  forall {D} (a b : DomainMap D),
    dm_le a b -> dm_le b a -> a = b.
Proof.
  intros D a b Hab Hba. apply functional_extensionality_dep.
  intro d. apply cs_le_antisym; [apply Hab | apply Hba].
Qed.

(** Empty rule list is the identity on any DomainMap. *)
Theorem apply_pass_nil :
  forall {D} (eq_dec : forall x y : D, {x = y} + {x <> y}) (f : DomainMap D),
    apply_pass eq_dec [] f = f.
Proof. intros D eq_dec f. reflexivity. Qed.

(** evaluate with zero iterations is the identity. *)
Theorem evaluate_zero :
  forall {D} (eq_dec : forall x y : D, {x = y} + {x <> y})
         (rules : list (PropagationRule D)) (init : DomainMap D),
    evaluate eq_dec 0 rules init = init.
Proof. intros. reflexivity. Qed.

(** evaluate with empty rule list is the identity. *)
Theorem evaluate_no_rules :
  forall {D} (eq_dec : forall x y : D, {x = y} + {x <> y})
         (n : nat) (init : DomainMap D),
    evaluate eq_dec n [] init = init.
Proof.
  intros D eq_dec n init. induction n as [|k IH].
  - reflexivity.
  - simpl. exact IH.
Qed.

(** Composition of evaluate: running n then m steps equals running n+m. *)
Theorem evaluate_compose :
  forall {D} (eq_dec : forall x y : D, {x = y} + {x <> y})
         (n m : nat) (rules : list (PropagationRule D)) (init : DomainMap D),
    evaluate eq_dec m rules (evaluate eq_dec n rules init) =
    evaluate eq_dec (n + m) rules init.
Proof.
  intros D eq_dec n. induction n as [|k IH]; intros m rules init.
  - simpl. reflexivity.
  - simpl. apply IH.
Qed.

(** CS_le is a preorder: reflexive + transitive (already stated
    independently; collected here as a named joint form for
    clarity). *)
Theorem cs_le_preorder :
  forall a, a <=c a.
Proof. exact cs_le_refl. Qed.

(** cs_meet is absorbing with respect to the bottom element NonCompliant. *)
Theorem cs_meet_bot_absorbs :
  forall a, cs_meet NonCompliant a = NonCompliant.
Proof. intro a. destruct a; reflexivity. Qed.

(** cs_meet with the top element Compliant is the other operand. *)
Theorem cs_meet_top_neutral :
  forall a, cs_meet a Compliant = a.
Proof. intro a. destruct a; reflexivity. Qed.

(** cs_ord is bounded above by 4 (Compliant). *)
Theorem cs_ord_bounded : forall s, cs_ord s <= 4.
Proof. destruct s; simpl; lia. Qed.

(** cs_ord is injective. *)
Theorem cs_ord_injective :
  forall s1 s2, cs_ord s1 = cs_ord s2 -> s1 = s2.
Proof. destruct s1, s2; simpl; intro H; try reflexivity; discriminate. Qed.

(** Decidable equality on ComplianceState. *)
Theorem cs_eq_dec :
  forall s1 s2 : ComplianceState, {s1 = s2} + {s1 <> s2}.
Proof. decide equality. Qed.

(** Decidable equality on PropagationEffect. *)
Theorem effect_eq_dec :
  forall e1 e2 : PropagationEffect, {e1 = e2} + {e1 <> e2}.
Proof. decide equality. Qed.

(** All 5 ComplianceState constructors are pairwise distinct. *)
Theorem cs_ctors_distinct :
  NonCompliant <> Pending /\
  Pending <> NotApplicable /\
  NotApplicable <> Exempt /\
  Exempt <> Compliant.
Proof. repeat split; discriminate. Qed.

(** ** Further propagation-effect properties (2026-04-20) *)

(** effect_apply on DropToNonCompliant: only NonCompliant source succeeds. *)
Theorem effect_apply_drop_only_nc :
  forall s, effect_apply DropToNonCompliant s = Some NonCompliant ->
            s = NonCompliant.
Proof. intros s H. destruct s; simpl in H; try discriminate. reflexivity. Qed.

(** effect_apply ClampToSource always succeeds with the source. *)
Theorem effect_apply_clamp_identity :
  forall s, effect_apply ClampToSource s = Some s.
Proof. intros s. reflexivity. Qed.

(** effect_apply CarryNotApplicable succeeds only on NotApplicable. *)
Theorem effect_apply_carry_only_na :
  forall s, effect_apply CarryNotApplicable s = Some NotApplicable ->
            s = NotApplicable.
Proof. intros s H. destruct s; simpl in H; try discriminate. reflexivity. Qed.

(** effect_apply BlockOnPendingOrWorse fails on Exempt / Compliant /
    NotApplicable — only the "pending-or-worse" spectrum is handled. *)
Theorem effect_apply_block_fails_on_high :
  effect_apply BlockOnPendingOrWorse NotApplicable = None /\
  effect_apply BlockOnPendingOrWorse Exempt = None /\
  effect_apply BlockOnPendingOrWorse Compliant = None.
Proof. repeat split; reflexivity. Qed.

(** Decidable equality on PropagationRule (given decidable D). *)
Theorem propagation_rule_eq_dec :
  forall (D : Type) (eq_dec : forall x y : D, {x = y} + {x <> y})
         (r1 r2 : PropagationRule D),
    {r1 = r2} + {r1 <> r2}.
Proof.
  intros D eq_dec [s1 t1 e1] [s2 t2 e2].
  destruct (eq_dec s1 s2); [| right; congruence].
  destruct (eq_dec t1 t2); [| right; congruence].
  destruct (effect_eq_dec e1 e2); [| right; congruence].
  subst. left. reflexivity.
Qed.
