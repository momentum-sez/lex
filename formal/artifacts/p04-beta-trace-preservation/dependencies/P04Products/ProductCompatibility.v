From Stdlib Require Import Lists.List.
From Lex Require Import Syntax.
From P04Source Require Import TypeReduction.
From P04Products Require Import Parallel ParallelTriangle ParallelEmbedding ParallelClosure Products.
Import Conversion.

(** Reflexive transitive parallel contraction. Its confluence follows from
    the checked complete-development triangle; it is not an assumption. *)
Inductive parallel_star : Term -> Term -> Prop :=
| parallel_star_refl : forall t, parallel_star t t
| parallel_star_cons : forall t u v,
    par t u -> parallel_star u v -> parallel_star t v.

Lemma parallel_star_append : forall t u v,
  parallel_star t u -> parallel_star u v -> parallel_star t v.
Proof.
  intros t u v H; induction H; intro Huv;
    eauto using parallel_star.
Qed.

Lemma parallel_strip : forall t v, parallel_star t v ->
  forall u, par t u -> exists w, parallel_star u w /\ par v w.
Proof.
  intros t v H; induction H; intros z Hz.
  - exists z; split; [constructor | exact Hz].
  - destruct (parallel_diamond _ _ _ H Hz) as [d [Hud Hzd]].
    destruct (IHparallel_star d Hud) as [w [Hdw Hvw]].
    exists w; split; [eapply parallel_star_cons; eassumption | exact Hvw].
Qed.

Theorem parallel_star_confluent : forall t u,
  parallel_star t u -> forall v, parallel_star t v ->
  exists w, parallel_star u w /\ parallel_star v w.
Proof.
  intros t u H; induction H; intros z Hz.
  - exists z; split; [exact Hz | constructor].
  - destruct (parallel_strip _ _ Hz _ H) as [d [Hud Hzd]].
    destruct (IHparallel_star d Hud) as [w [Hvw Hdw]].
    exists w; split; [exact Hvw | eapply parallel_star_cons; eassumption].
Qed.

Lemma steps_parallel_star : forall t u,
  steps t u -> parallel_star t u.
Proof.
  intros t u H; induction H; [constructor |].
  eapply parallel_star_cons; [apply step_parallel; exact H | exact IHsteps].
Qed.

Lemma parallel_star_steps : forall t u,
  parallel_star t u -> steps t u.
Proof.
  intros t u H; induction H; [constructor |].
  eapply steps_append; [apply parallel_steps; exact H | exact IHparallel_star].
Qed.

(** Source reduction is confluent on all actual syntax terms. This does not
    assert termination: the preserved [raw_omega_self_step] is compatible
    with confluence. *)
Theorem source_steps_confluent : forall t u v,
  steps t u -> steps t v -> exists w, steps u w /\ steps v w.
Proof.
  intros t u v Hu Hv.
  destruct (parallel_star_confluent _ _ (steps_parallel_star _ _ Hu)
    _ (steps_parallel_star _ _ Hv)) as [w [Huw Hvw]].
  exists w; split; now apply parallel_star_steps.
Qed.

(** Every finite conversion zigzag has an actual common reduct. *)
Theorem convertible_joinable : forall t u, convertible t u -> joinable t u.
Proof.
  intros t u H; induction H.
  - exists t; split; constructor.
  - exists u; split; [eapply steps_trans; [exact H | constructor] | constructor].
  - destruct IHconvertible as [v [Htv Huv]]. exists v; split; assumption.
  - destruct IHconvertible1 as [x [Htx Hux]].
    destruct IHconvertible2 as [y [Huy Hvy]].
    destruct (source_steps_confluent _ _ _ Hux Huy) as [z [Hxz Hyz]].
    exists z; split; eapply steps_append; eassumption.
Qed.

(** Product compatibility for the actual conversion relation: effect rows
    agree exactly, and both raw components are convertible. *)
Theorem pi_convertible_decomposition : forall A e B A' e' B',
  convertible (Pi A e B) (Pi A' e' B') ->
  e = e' /\ convertible A A' /\ convertible B B'.
Proof.
  intros A e B A' e' B' H.
  apply pi_joinable_convertible_components.
  apply convertible_joinable; exact H.
Qed.

Print Assumptions parallel_star_confluent.
Print Assumptions source_steps_confluent.
Print Assumptions convertible_joinable.
Print Assumptions pi_convertible_decomposition.
