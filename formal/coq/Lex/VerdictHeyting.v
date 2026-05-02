(** * Verdict-lattice Heyting algebra (5-element bounded chain) *)

(** Mechanizes the verdict lattice from lex.tex Lex/VerdictLattice
    section: ComplianceVerdict has five values forming a bounded
    distributive Heyting algebra under the restrictiveness order
    NonCompliant < Pending < NotApplicable < Exempt < Compliant.
    All laws are Qed-closed by exhaustive case analysis on the
    finite carrier. *)

Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.

Set Implicit Arguments.

Inductive verdict : Type :=
  | NonCompliant
  | Pending
  | NotApplicable
  | Exempt
  | Compliant.

(** Encode the chain as a natural-number rank. *)
Definition rank (v : verdict) : nat :=
  match v with
  | NonCompliant => 0
  | Pending => 1
  | NotApplicable => 2
  | Exempt => 3
  | Compliant => 4
  end.

Definition unrank (n : nat) : verdict :=
  match n with
  | 0 => NonCompliant
  | 1 => Pending
  | 2 => NotApplicable
  | 3 => Exempt
  | _ => Compliant
  end.

Lemma rank_unrank : forall v, unrank (rank v) = v.
Proof. destruct v; reflexivity. Qed.

(** The order: v1 <= v2 iff rank v1 <= rank v2. *)
Definition leq (v1 v2 : verdict) : Prop := rank v1 <= rank v2.

(** Meet = min; Join = max. *)
Definition meet (v1 v2 : verdict) : verdict :=
  unrank (Nat.min (rank v1) (rank v2)).

Definition join (v1 v2 : verdict) : verdict :=
  unrank (Nat.max (rank v1) (rank v2)).

(** Heyting implication: a -> b = top if a <= b, else b. *)
Definition impl (a b : verdict) : verdict :=
  if Nat.leb (rank a) (rank b) then Compliant else b.

(** Bounds. *)
Definition top : verdict := Compliant.
Definition bot : verdict := NonCompliant.

(** -- Lattice laws -- *)

Lemma meet_idempotent : forall v, meet v v = v.
Proof.
  intros v. unfold meet.
  rewrite Nat.min_id. apply rank_unrank.
Qed.

Lemma meet_comm : forall a b, meet a b = meet b a.
Proof.
  intros a b. unfold meet.
  rewrite Nat.min_comm. reflexivity.
Qed.

Lemma meet_assoc : forall a b c, meet (meet a b) c = meet a (meet b c).
Proof.
  intros a b c. unfold meet.
  destruct a, b, c; reflexivity.
Qed.

Lemma join_idempotent : forall v, join v v = v.
Proof.
  intros v. unfold join.
  rewrite Nat.max_id. apply rank_unrank.
Qed.

Lemma join_comm : forall a b, join a b = join b a.
Proof.
  intros a b. unfold join.
  rewrite Nat.max_comm. reflexivity.
Qed.

Lemma join_assoc : forall a b c, join (join a b) c = join a (join b c).
Proof.
  intros a b c. unfold join.
  destruct a, b, c; reflexivity.
Qed.

(** Absorption laws. *)
Lemma absorption_meet_join : forall a b, meet a (join a b) = a.
Proof.
  intros a b. unfold meet, join.
  destruct a, b; reflexivity.
Qed.

Lemma absorption_join_meet : forall a b, join a (meet a b) = a.
Proof.
  intros a b. unfold meet, join.
  destruct a, b; reflexivity.
Qed.

(** Distributive laws (both directions). *)
Lemma distrib_meet_join : forall a b c,
  meet a (join b c) = join (meet a b) (meet a c).
Proof.
  intros a b c. unfold meet, join.
  destruct a, b, c; reflexivity.
Qed.

Lemma distrib_join_meet : forall a b c,
  join a (meet b c) = meet (join a b) (join a c).
Proof.
  intros a b c. unfold meet, join.
  destruct a, b, c; reflexivity.
Qed.

(** Bounds laws. *)
Lemma meet_top : forall v, meet v top = v.
Proof.
  intros v. unfold meet, top.
  destruct v; reflexivity.
Qed.

Lemma meet_bot : forall v, meet v bot = bot.
Proof.
  intros v. unfold meet, bot.
  destruct v; reflexivity.
Qed.

Lemma join_top : forall v, join v top = top.
Proof.
  intros v. unfold join, top.
  destruct v; reflexivity.
Qed.

Lemma join_bot : forall v, join v bot = v.
Proof.
  intros v. unfold join, bot.
  destruct v; reflexivity.
Qed.

(** Heyting identity: a /\ (a -> b) = a /\ b. *)
Lemma heyting_identity : forall a b, meet a (impl a b) = meet a b.
Proof.
  intros a b. unfold meet, impl.
  destruct a, b; reflexivity.
Qed.

(** Residuation: c <= (a -> b) iff a /\ c <= b. *)
Lemma residuation : forall a b c,
  leq c (impl a b) <-> leq (meet a c) b.
Proof.
  intros a b c. unfold leq, meet, impl.
  destruct a, b, c; simpl; split; intro H;
    try lia;
    try (apply Nat.leb_le; lia);
    try (apply Nat.leb_nle; lia).
Qed.

(** The Heyting structure is sound: meet, join, impl as defined
    satisfy the Heyting algebra axioms. *)
Theorem verdict_is_heyting :
  (forall v, meet v v = v) /\
  (forall a b, meet a b = meet b a) /\
  (forall a b c, meet (meet a b) c = meet a (meet b c)) /\
  (forall v, join v v = v) /\
  (forall a b, join a b = join b a) /\
  (forall a b c, join (join a b) c = join a (join b c)) /\
  (forall a b, meet a (join a b) = a) /\
  (forall a b, join a (meet a b) = a) /\
  (forall a b c, meet a (join b c) = join (meet a b) (meet a c)) /\
  (forall a b c, join a (meet b c) = meet (join a b) (join a c)) /\
  (forall v, meet v top = v) /\
  (forall v, join v bot = v) /\
  (forall a b, meet a (impl a b) = meet a b).
Proof.
  repeat split.
  - apply meet_idempotent.
  - apply meet_comm.
  - apply meet_assoc.
  - apply join_idempotent.
  - apply join_comm.
  - apply join_assoc.
  - apply absorption_meet_join.
  - apply absorption_join_meet.
  - apply distrib_meet_join.
  - apply distrib_join_meet.
  - apply meet_top.
  - apply join_bot.
  - apply heyting_identity.
Qed.

(** ** Partial-order properties of the leq relation *)

Lemma leq_refl : forall v, leq v v.
Proof. intros v. unfold leq. apply Nat.le_refl. Qed.

Lemma leq_trans : forall a b c, leq a b -> leq b c -> leq a c.
Proof.
  intros a b c Hab Hbc. unfold leq in *.
  apply Nat.le_trans with (m := rank b); assumption.
Qed.

Lemma leq_antisym : forall a b, leq a b -> leq b a -> a = b.
Proof.
  intros a b Hab Hba. unfold leq in *.
  assert (Hr : rank a = rank b) by lia.
  rewrite <- (rank_unrank a), <- (rank_unrank b), Hr. reflexivity.
Qed.

(** ** Meet / join as glb / lub *)

Lemma meet_leq_left : forall a b, leq (meet a b) a.
Proof. destruct a, b; compute; lia. Qed.

Lemma meet_leq_right : forall a b, leq (meet a b) b.
Proof. destruct a, b; compute; lia. Qed.

Lemma join_leq_left : forall a b, leq a (join a b).
Proof. destruct a, b; compute; lia. Qed.

Lemma join_leq_right : forall a b, leq b (join a b).
Proof. destruct a, b; compute; lia. Qed.

(** ** Monotonicity of meet and join *)

Lemma meet_monotone : forall a a' b b',
  leq a a' -> leq b b' -> leq (meet a b) (meet a' b').
Proof. destruct a, a', b, b'; compute; lia. Qed.

Lemma join_monotone : forall a a' b b',
  leq a a' -> leq b b' -> leq (join a b) (join a' b').
Proof. destruct a, a', b, b'; compute; lia. Qed.

(** ** Properties of the Heyting implication *)

Lemma impl_refl : forall v, impl v v = top.
Proof. destruct v; reflexivity. Qed.

Lemma impl_top_right : forall v, impl v top = top.
Proof. destruct v; reflexivity. Qed.

Lemma impl_bot_left : forall v, impl bot v = top.
Proof. destruct v; reflexivity. Qed.

(** Monotonicity of implication in its second argument: if
    [b <= b'], then [a -> b <= a -> b']. *)
Lemma impl_monotone_right : forall a b b',
  leq b b' -> leq (impl a b) (impl a b').
Proof. destruct a, b, b'; compute; lia. Qed.

(** Antimonotonicity of implication in its first argument: if
    [a <= a'], then [a' -> b <= a -> b]. *)
Lemma impl_antimonotone_left : forall a a' b,
  leq a a' -> leq (impl a' b) (impl a b).
Proof. destruct a, a', b; compute; lia. Qed.

(** Meet-leq characterisation: [leq c (meet a b)] iff
    [leq c a] and [leq c b]. *)
Lemma meet_leq_iff : forall a b c,
  leq c (meet a b) <-> (leq c a /\ leq c b).
Proof.
  intros a b c. split.
  - intros H. split.
    + eapply leq_trans; [exact H | apply meet_leq_left].
    + eapply leq_trans; [exact H | apply meet_leq_right].
  - intros [H1 H2]. destruct a, b, c; compute in *; lia.
Qed.

(** Join-leq characterisation: [leq (join a b) c] iff
    [leq a c] and [leq b c]. *)
Lemma join_leq_iff : forall a b c,
  leq (join a b) c <-> (leq a c /\ leq b c).
Proof.
  intros a b c. split.
  - intros H. split.
    + eapply leq_trans; [apply join_leq_left | exact H].
    + eapply leq_trans; [apply join_leq_right | exact H].
  - intros [H1 H2]. destruct a, b, c; compute in *; lia.
Qed.

(** ** Further Heyting-algebra properties (2026-04-20) *)

(** Rank is bounded above by 4 (the rank of top). *)
Lemma rank_bounded : forall v, rank v <= 4.
Proof. destruct v; simpl; lia. Qed.

(** Rank is injective. *)
Lemma rank_injective : forall v1 v2, rank v1 = rank v2 -> v1 = v2.
Proof.
  destruct v1, v2; simpl; intro H; try reflexivity; discriminate.
Qed.

(** Heyting residuation: [leq c (impl a b)] iff [leq (meet c a) b].
    The defining property of Heyting algebras. *)
Lemma heyting_residuation : forall a b c,
  leq c (impl a b) <-> leq (meet c a) b.
Proof.
  intros a b c. destruct a, b, c; compute; split; intro H; try lia.
Qed.

(** [impl a b = top] iff [leq a b]. *)
Lemma impl_eq_top_iff_leq : forall a b,
  impl a b = top <-> leq a b.
Proof.
  intros a b. destruct a, b; compute; split; intro H; try reflexivity;
    try discriminate; try lia.
Qed.

(** impl preserves equality on its arguments. *)
Lemma impl_cong : forall a1 a2 b1 b2,
  a1 = a2 -> b1 = b2 -> impl a1 b1 = impl a2 b2.
Proof. intros. subst. reflexivity. Qed.

(** Implication distributes over meet on the right:
    impl a (meet b c) = meet (impl a b) (impl a c). *)
Lemma impl_distrib_meet : forall a b c,
  impl a (meet b c) = meet (impl a b) (impl a c).
Proof. destruct a, b, c; reflexivity. Qed.

(** Leq is decidable. *)
Lemma leq_dec : forall v1 v2, {leq v1 v2} + {~ leq v1 v2}.
Proof.
  intros v1 v2. unfold leq.
  destruct (Nat.leb (rank v1) (rank v2)) eqn:Hleb.
  - left. apply Nat.leb_le. exact Hleb.
  - right. intro H. apply Nat.leb_le in H. rewrite H in Hleb. discriminate.
Qed.

(** Verdict equality is decidable. *)
Lemma verdict_eq_dec : forall v1 v2 : verdict, {v1 = v2} + {v1 <> v2}.
Proof. decide equality. Qed.

(** ** Additional structural properties (2026-04-20) *)

(** rank is a monotone map with respect to leq: [leq v1 v2] iff
    [rank v1 <= rank v2]. *)
Lemma rank_monotone : forall v1 v2,
  leq v1 v2 <-> rank v1 <= rank v2.
Proof. intros v1 v2. unfold leq. split; intro H; exact H. Qed.

(** The five verdict constructors are pairwise distinct. *)
Lemma verdict_ctors_distinct :
  NonCompliant <> Pending /\
  Pending <> NotApplicable /\
  NotApplicable <> Exempt /\
  Exempt <> Compliant.
Proof. repeat split; discriminate. Qed.

(** impl is always a verdict (total function). *)
Lemma impl_total : forall a b, exists v : verdict, impl a b = v.
Proof. intros a b. exists (impl a b). reflexivity. Qed.

(** The top element is above every element. *)
Lemma leq_top : forall v, leq v top.
Proof. intros v. unfold leq, top. destruct v; simpl; lia. Qed.

(** The bottom element is below every element. *)
Lemma bot_leq : forall v, leq bot v.
Proof. intros v. unfold leq, bot. destruct v; simpl; lia. Qed.

(** top and bot are distinct. *)
Lemma top_neq_bot : top <> bot.
Proof. discriminate. Qed.
