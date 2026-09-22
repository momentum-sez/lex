From Stdlib Require Import Lists.List Strings.String Arith.Arith Lia.
From Lex Require Import Syntax DeBruijn Typing.
From P04Substitution Require Import SimultaneousArgs.
From P04ArgsSubstitution Require Import ArgsSubstitution.
From P04Source Require Import TypeReduction.
From P04Products Require Import Parallel.
Import ListNotations.

Lemma parallel_shift_mutual :
  (forall t t', par t t' -> forall cut d,
     par (shift cut d t) (shift cut d t')) /\
  (forall ts ts', pars ts ts' -> forall cut d,
     pars (map (shift cut d) ts) (map (shift cut d) ts')) /\
  (forall bs bs', parbs bs bs' -> forall cut d,
     parbs (map (shift_branch cut d) bs) (map (shift_branch cut d) bs')) /\
  (forall es es', pares es es' -> forall cut d,
     pares (map (shift_exception cut d) es) (map (shift_exception cut d) es')).
Proof.
  apply parallel_ind; intros; simpl;
    try solve [econstructor; eauto].
  - destruct (Nat.leb cut x); constructor.
  - rewrite shift_subst_commute_above by lia. apply par_beta; eauto.
  - rewrite shift_subst_commute_above by lia. apply par_zeta; eauto.
  - rewrite Nat.add_0_r. apply par_match_wild; eauto.
  - rewrite instantiate_args_shift.
    match goal with Hargs : pars ?args ?args' |- _ =>
      pose proof (pars_length _ _ Hargs) as Hlen
    end.
    rewrite <- Hlen, e0.
    eapply par_match_ctor_fire; eauto. rewrite length_map; assumption.
  - eapply par_match_ctor_skip; eauto.
    + simpl in *. rewrite length_map. assumption.
    + destruct rest; simpl in *; congruence.
Qed.

Definition par_shift := proj1 parallel_shift_mutual.
Definition pars_shift := proj1 (proj2 parallel_shift_mutual).
Definition parbs_shift := proj1 (proj2 (proj2 parallel_shift_mutual)).
Definition pares_shift := proj2 (proj2 (proj2 parallel_shift_mutual)).

Print Assumptions par_shift.

Lemma parallel_subst_mutual :
  (forall t t', par t t' -> forall k u u', par u u' ->
     par (subst k u t) (subst k u' t')) /\
  (forall ts ts', pars ts ts' -> forall k u u', par u u' ->
     pars (map (subst k u) ts) (map (subst k u') ts')) /\
  (forall bs bs', parbs bs bs' -> forall k u u', par u u' ->
     parbs (map (subst_branch k u) bs) (map (subst_branch k u') bs')) /\
  (forall es es', pares es es' -> forall k u u', par u u' ->
     pares (map (subst_exception k u) es) (map (subst_exception k u') es')).
Proof.
  apply parallel_ind; intros; simpl;
    try solve [econstructor; eauto using par_shift].
  - destruct (Nat.eqb x k); [assumption |].
    destruct (Nat.ltb k x); constructor.
  - rewrite subst_beta_commute. apply par_beta; eauto using par_shift.
  - rewrite subst_beta_commute. apply par_zeta; eauto using par_shift.
  - rewrite Nat.add_0_r, shift_zero. apply par_match_wild; eauto.
  - rewrite instantiate_args_subst.
    match goal with Hargs : pars ?args ?args' |- _ =>
      pose proof (pars_length _ _ Hargs) as Hlen
    end.
    rewrite <- Hlen, e0.
    eapply par_match_ctor_fire; eauto using par_shift.
    rewrite length_map; assumption.
  - eapply par_match_ctor_skip; eauto.
    + simpl in *. rewrite length_map. assumption.
    + destruct rest; simpl in *; congruence.
Qed.

Definition par_subst := proj1 parallel_subst_mutual.
Definition pars_subst := proj1 (proj2 parallel_subst_mutual).
Definition parbs_subst := proj1 (proj2 (proj2 parallel_subst_mutual)).
Definition pares_subst := proj2 (proj2 (proj2 parallel_subst_mutual)).

Print Assumptions par_subst.

Lemma pars_app : forall xs xs' ys ys',
  pars xs xs' -> pars ys ys' -> pars (xs ++ ys) (xs' ++ ys').
Proof.
  intros xs xs' ys ys' H; induction H; intros Hys; simpl.
  - exact Hys.
  - constructor; auto.
Qed.

Lemma pars_rev : forall xs xs', pars xs xs' -> pars (rev xs) (rev xs').
Proof.
  intros xs xs' H; induction H; simpl.
  - constructor.
  - apply pars_app; [assumption | repeat constructor; assumption].
Qed.

Lemma pars_protect_args : forall xs xs',
  pars xs xs' -> pars (protect_args xs) (protect_args xs').
Proof.
  intros xs xs' H; induction H; simpl.
  - constructor.
  - rewrite <- (pars_length _ _ H0). constructor; [apply par_shift; assumption | assumption].
Qed.

Lemma par_subst_args : forall args args', pars args args' ->
  forall body body', par body body' ->
  par (subst_args args body) (subst_args args' body').
Proof.
  intros args args' H; induction H; intros body body' Hb; simpl.
  - exact Hb.
  - apply IHpars. apply par_subst; assumption.
Qed.

Theorem par_instantiate_args : forall args args' body body',
  pars args args' -> par body body' ->
  par (instantiate_args args body) (instantiate_args args' body').
Proof.
  intros args args' body body' Ha Hb. unfold instantiate_args.
  apply par_subst_args; [apply pars_protect_args; apply pars_rev; exact Ha | exact Hb].
Qed.

Print Assumptions pars_shift.
Print Assumptions parbs_shift.
Print Assumptions pares_shift.
Print Assumptions pars_subst.
Print Assumptions parbs_subst.
Print Assumptions pares_subst.
Print Assumptions par_instantiate_args.
