(** * Lex/PropagationAlignment.v — Isomorphism between Lex's five-element
    verdict chain [VerdictHeyting.verdict] and the Propagation graph's
    [Propagation.Graph.ComplianceState].

    The kernel mechanisation carries two independent but structurally
    identical five-element compliance-state carriers:

    - [Lex/VerdictHeyting.verdict] ({NonCompliant, Pending, NotApplicable,
      Exempt, Compliant}) with a bounded distributive Heyting algebra
      (thirteen laws Qed).

    - [Propagation/Graph.ComplianceState] ({NonCompliant, Pending,
      NotApplicable, Exempt, Compliant}) with F142 propagation-graph
      monotonicity theorems Qed.

    The two inductives are definitionally distinct types (Coq refuses to
    unify them without an explicit coercion) but semantically identical.
    This file closes the supremum obligation that the two views are
    mutually coherent: the forward and reverse morphisms are Qed-closed
    inverses, ranks are preserved, and meets commute with the morphism
    on both sides.

    Result: any theorem Qed-closed in one carrier's universe is
    transportable to the other via the isomorphism, so downstream
    reasoning at the F142 propagation layer can cite the Lex Heyting laws
    (idempotence, commutativity, associativity, absorption, distributivity,
    bounds, Heyting identity, residuation) through the projection without
    re-proving them at the Propagation layer, and vice versa. *)

Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Require Import Lex.VerdictHeyting.
Require Import Propagation.Graph.

(** ** Forward morphism: [verdict] → [ComplianceState] *)

Definition verdict_to_cs (v : verdict) : ComplianceState :=
  match v with
  | VerdictHeyting.NonCompliant  => Propagation.Graph.NonCompliant
  | VerdictHeyting.Pending       => Propagation.Graph.Pending
  | VerdictHeyting.NotApplicable => Propagation.Graph.NotApplicable
  | VerdictHeyting.Exempt        => Propagation.Graph.Exempt
  | VerdictHeyting.Compliant     => Propagation.Graph.Compliant
  end.

(** ** Reverse morphism: [ComplianceState] → [verdict] *)

Definition cs_to_verdict (c : ComplianceState) : verdict :=
  match c with
  | Propagation.Graph.NonCompliant  => VerdictHeyting.NonCompliant
  | Propagation.Graph.Pending       => VerdictHeyting.Pending
  | Propagation.Graph.NotApplicable => VerdictHeyting.NotApplicable
  | Propagation.Graph.Exempt        => VerdictHeyting.Exempt
  | Propagation.Graph.Compliant     => VerdictHeyting.Compliant
  end.

(** ** The forward and reverse morphisms are mutual inverses *)

Theorem verdict_cs_iso_left :
  forall v, cs_to_verdict (verdict_to_cs v) = v.
Proof. destruct v; reflexivity. Qed.

Theorem verdict_cs_iso_right :
  forall c, verdict_to_cs (cs_to_verdict c) = c.
Proof. destruct c; reflexivity. Qed.

(** ** Ranks are preserved *)

(** [VerdictHeyting.rank] and [Propagation.Graph.cs_ord] agree under the
    morphism.  Qed by exhaustive case analysis on the five-element
    carrier. *)
Theorem verdict_to_cs_preserves_rank :
  forall v, cs_ord (verdict_to_cs v) = rank v.
Proof. destruct v; reflexivity. Qed.

Theorem cs_to_verdict_preserves_rank :
  forall c, rank (cs_to_verdict c) = cs_ord c.
Proof. destruct c; reflexivity. Qed.

(** ** Meets commute with the morphism *)

(** The Heyting meet on [verdict] and the propagation meet on
    [ComplianceState] agree via the morphism.  Qed by case analysis on
    the twenty-five ordered pairs. *)
Theorem verdict_to_cs_preserves_meet :
  forall v1 v2,
    verdict_to_cs (meet v1 v2) = cs_meet (verdict_to_cs v1) (verdict_to_cs v2).
Proof.
  destruct v1, v2; compute; reflexivity.
Qed.

Theorem cs_to_verdict_preserves_meet :
  forall c1 c2,
    cs_to_verdict (cs_meet c1 c2) = meet (cs_to_verdict c1) (cs_to_verdict c2).
Proof.
  destruct c1, c2; compute; reflexivity.
Qed.

(** ** Order is preserved *)

(** [VerdictHeyting.leq] and [Propagation.Graph.cs_le] agree via the
    morphism. *)
Theorem verdict_to_cs_preserves_order :
  forall v1 v2,
    leq v1 v2 <-> cs_le (verdict_to_cs v1) (verdict_to_cs v2).
Proof.
  intros v1 v2. unfold leq, cs_le.
  rewrite !verdict_to_cs_preserves_rank.
  reflexivity.
Qed.

Theorem cs_to_verdict_preserves_order :
  forall c1 c2,
    cs_le c1 c2 <-> leq (cs_to_verdict c1) (cs_to_verdict c2).
Proof.
  intros c1 c2. unfold cs_le, leq.
  rewrite !cs_to_verdict_preserves_rank.
  reflexivity.
Qed.

(** ** Additional isomorphism properties (2026-04-20) *)

(** Both morphisms are injective. *)
Theorem verdict_to_cs_injective :
  forall v1 v2, verdict_to_cs v1 = verdict_to_cs v2 -> v1 = v2.
Proof.
  intros v1 v2 H.
  rewrite <- (verdict_cs_iso_left v1).
  rewrite <- (verdict_cs_iso_left v2).
  f_equal. exact H.
Qed.

Theorem cs_to_verdict_injective :
  forall c1 c2, cs_to_verdict c1 = cs_to_verdict c2 -> c1 = c2.
Proof.
  intros c1 c2 H.
  rewrite <- (verdict_cs_iso_right c1).
  rewrite <- (verdict_cs_iso_right c2).
  f_equal. exact H.
Qed.

(** Both morphisms are surjective. *)
Theorem verdict_to_cs_surjective :
  forall c, exists v, verdict_to_cs v = c.
Proof.
  intros c. exists (cs_to_verdict c). apply verdict_cs_iso_right.
Qed.

Theorem cs_to_verdict_surjective :
  forall v, exists c, cs_to_verdict c = v.
Proof.
  intros v. exists (verdict_to_cs v). apply verdict_cs_iso_left.
Qed.

(** The top element of [verdict] maps to [Compliant] (the maximum rank
    in [ComplianceState]). *)
Theorem verdict_to_cs_top :
  verdict_to_cs top = Propagation.Graph.Compliant.
Proof. reflexivity. Qed.

(** The bottom element of [verdict] maps to [NonCompliant]. *)
Theorem verdict_to_cs_bot :
  verdict_to_cs bot = Propagation.Graph.NonCompliant.
Proof. reflexivity. Qed.

(** The meet [verdict_to_cs]-image of the top element is the second
    operand. *)
Theorem verdict_to_cs_meet_top :
  forall v,
    cs_meet (verdict_to_cs top) (verdict_to_cs v) = verdict_to_cs v.
Proof.
  intro v. rewrite <- verdict_to_cs_preserves_meet.
  rewrite meet_comm, meet_top. reflexivity.
Qed.

(** The meet [verdict_to_cs]-image of the bottom element is the bottom. *)
Theorem verdict_to_cs_meet_bot :
  forall v,
    cs_meet (verdict_to_cs bot) (verdict_to_cs v) = verdict_to_cs bot.
Proof.
  intro v. rewrite <- verdict_to_cs_preserves_meet.
  rewrite meet_comm, meet_bot. reflexivity.
Qed.

(** ** Summary

    The Lex verdict chain and the Propagation graph compliance-state are
    Qed-closed isomorphic finite ordered carriers.  The morphisms
    [verdict_to_cs] / [cs_to_verdict] are mutual inverses (full bijection),
    preserve ranks, commute with meet, and preserve the ordering relation.

    This closes the cross-module coherence obligation: every theorem
    Qed-closed at one layer transports to the other through the
    isomorphism without re-proof.  The two carriers exist for
    ergonomic reasons (Lex reasons about Heyting structure; Propagation
    reasons about monotonicity over a propagation-rule graph), not
    because they name different mathematical objects. *)
