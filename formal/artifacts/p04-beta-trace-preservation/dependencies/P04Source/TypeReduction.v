From Stdlib Require Import Lists.List Strings.String Arith.Arith Lia.
From Lex Require Import Syntax DeBruijn Typing.
From P04Substitution Require Import SimultaneousArgs.
From P04ArgsSubstitution Require Import ArgsSubstitution.
Import ListNotations.

(** Pure type-level reduction uses the captured Term syntax. Constructor
    branches wait for a constructor head. Nonempty exception lists retain
    their meaning until the separate execution semantics selects a branch. *)
Module Conversion.
Inductive step : Term -> Term -> Prop :=

  | step_beta : forall (dom body arg : Term),
      step (App (Lambda dom body) arg)
           (subst 0 arg body)

  | step_zeta : forall (ty val body : Term),
      step (Let ty val body)
           (subst 0 val body)

  | step_annot : forall (e ty : Term),
      step (Annot e ty) e

  | step_defeasible_empty : forall (base_ty base_body : Term),
      step (Defeasible base_ty base_body nil) base_body

  | step_match_wild : forall (scrut ret body : Term)
                             (rest : list Branch),
      step (Match scrut ret (MkBranch PWild body :: rest)) body

  | step_match_ctor_fire : forall (c c' : string) (args : list Term)
                                   (ret body : Term) (n : nat)
                                   (rest : list Branch),
      String.eqb c c' = true ->
      List.length args = n ->
      step (Match (InductiveIntro c args) ret
                  (MkBranch (PCtor c' n) body :: rest))
           (instantiate_args args body)

  | step_match_ctor_skip : forall (c c' : string) (args : list Term)
                                   (ret body : Term) (n : nat)
                                   (rest : list Branch),
      branch_head_matches (InductiveIntro c args) c' n = false ->
      rest <> nil ->
      step (Match (InductiveIntro c args) ret (MkBranch (PCtor c' n) body :: rest))
           (Match (InductiveIntro c args) ret rest)

  | step_app_func : forall (f f' a : Term),
      step f f' -> step (App f a) (App f' a)
  | step_app_arg : forall (f a a' : Term),
      step a a' -> step (App f a) (App f a')

  | step_pair_fst : forall (a a' b : Term),
      step a a' -> step (Pair a b) (Pair a' b)
  | step_pair_snd : forall (a b b' : Term),
      step b b' -> step (Pair a b) (Pair a b')
  | step_proj : forall (f : bool) (t t' : Term),
      step t t' -> step (Proj f t) (Proj f t')

  | step_inductive_args : forall (c : string) (pre : list Term)
                                 (a a' : Term) (post : list Term),
      step a a' ->
      step (InductiveIntro c (pre ++ a :: post))
           (InductiveIntro c (pre ++ a' :: post))

  | step_sanctions_dominance : forall (p p' : Term),
      step p p' -> step (SanctionsDominance p) (SanctionsDominance p')
  | step_defeat_elim : forall (r r' : Term),
      step r r' -> step (DefeatElim r) (DefeatElim r')
  | step_lift0 : forall (t t' : Term),
      step t t' -> step (Lift0 t) (Lift0 t')
  | step_derive1_time : forall (ti ti' w : Term),
      step ti ti' -> step (Derive1 ti w) (Derive1 ti' w)
  | step_derive1_wit : forall (ti w w' : Term),
      step w w' -> step (Derive1 ti w) (Derive1 ti w')

  | step_lambda_dom : forall (dom dom' body : Term),
      step dom dom' -> step (Lambda dom body) (Lambda dom' body)
  | step_lambda_body : forall (dom body body' : Term),
      step body body' -> step (Lambda dom body) (Lambda dom body')

  | step_pi_dom : forall (dom dom' : Term) (eff : option EffectRow) (cod : Term),
      step dom dom' -> step (Pi dom eff cod) (Pi dom' eff cod)
  | step_pi_cod : forall (dom : Term) (eff : option EffectRow) (cod cod' : Term),
      step cod cod' -> step (Pi dom eff cod) (Pi dom eff cod')

  | step_sigma_fst : forall (ft ft' st : Term),
      step ft ft' -> step (Sigma ft st) (Sigma ft' st)
  | step_sigma_snd : forall (ft st st' : Term),
      step st st' -> step (Sigma ft st) (Sigma ft st')

  | step_rec_ty : forall (ty ty' body : Term),
      step ty ty' -> step (Rec ty body) (Rec ty' body)
  | step_rec_body : forall (ty body body' : Term),
      step body body' -> step (Rec ty body) (Rec ty body')

  | step_annot_e : forall (e e' ty : Term),
      step e e' -> step (Annot e ty) (Annot e' ty)
  | step_annot_ty : forall (e ty ty' : Term),
      step ty ty' -> step (Annot e ty) (Annot e ty')

  | step_let_ty : forall (ty ty' val body : Term),
      step ty ty' -> step (Let ty val body) (Let ty' val body)
  | step_let_val : forall (ty val val' body : Term),
      step val val' -> step (Let ty val body) (Let ty val' body)
  | step_let_body : forall (ty val body body' : Term),
      step body body' -> step (Let ty val body) (Let ty val body')

  | step_match_scrutinee : forall (scrut scrut' ret : Term)
                                   (brs : list Branch),
      step scrut scrut' ->
      step (Match scrut ret brs) (Match scrut' ret brs)
  | step_match_ret : forall (scrut ret ret' : Term) (brs : list Branch),
      step ret ret' ->
      step (Match scrut ret brs) (Match scrut ret' brs)
  | step_match_branch : forall (scrut ret : Term) (pre : list Branch)
                               (pat : Pattern) (b b' : Term) (post : list Branch),
      step b b' ->
      step (Match scrut ret (pre ++ MkBranch pat b :: post))
           (Match scrut ret (pre ++ MkBranch pat b' :: post))

  | step_modal_at_time : forall (ti ti' body : Term),
      step ti ti' -> step (ModalAt ti body) (ModalAt ti' body)
  | step_modal_at_body : forall (ti body body' : Term),
      step body body' -> step (ModalAt ti body) (ModalAt ti body')

  | step_modal_eventually_time : forall (ti ti' body : Term),
      step ti ti' -> step (ModalEventually ti body) (ModalEventually ti' body)
  | step_modal_eventually_body : forall (ti body body' : Term),
      step body body' -> step (ModalEventually ti body) (ModalEventually ti body')

  | step_modal_always_from : forall (from from' to body : Term),
      step from from' ->
      step (ModalAlways from to body) (ModalAlways from' to body)
  | step_modal_always_to : forall (from to to' body : Term),
      step to to' ->
      step (ModalAlways from to body) (ModalAlways from to' body)
  | step_modal_always_body : forall (from to body body' : Term),
      step body body' ->
      step (ModalAlways from to body) (ModalAlways from to body')

  | step_modal_intro : forall (tr : string) (body body' : Term),
      step body body' -> step (ModalIntro tr body) (ModalIntro tr body')
  | step_modal_elim_e : forall (t1 t2 : string) (e e' w : Term),
      step e e' -> step (ModalElim t1 t2 e w) (ModalElim t1 t2 e' w)
  | step_modal_elim_w : forall (t1 t2 : string) (e w w' : Term),
      step w w' -> step (ModalElim t1 t2 e w) (ModalElim t1 t2 e w')

  | step_defeasible_ty : forall (bt bt' bb : Term) (exns : list Exception),
      step bt bt' -> step (Defeasible bt bb exns) (Defeasible bt' bb exns)
  | step_defeasible_body : forall (bt bb bb' : Term) (exns : list Exception),
      step bb bb' -> step (Defeasible bt bb exns) (Defeasible bt bb' exns)
  | step_defeasible_exn_guard : forall (bt bb : Term) (pre : list Exception)
                                       (g g' b : Term) (prio : option nat)
                                       (post : list Exception),
      step g g' ->
      step (Defeasible bt bb (pre ++ MkException g b prio :: post))
           (Defeasible bt bb (pre ++ MkException g' b prio :: post))
  | step_defeasible_exn_body : forall (bt bb : Term) (pre : list Exception)
                                      (g b b' : Term) (prio : option nat)
                                      (post : list Exception),
      step b b' ->
      step (Defeasible bt bb (pre ++ MkException g b prio :: post))
           (Defeasible bt bb (pre ++ MkException g b' prio :: post))

  | step_hole : forall (ty ty' : Term),
      step ty ty' -> step (Hole ty) (Hole ty')
  | step_hole_fill_filler : forall (f f' pc : Term),
      step f f' -> step (HoleFill f pc) (HoleFill f' pc)
  | step_hole_fill_pc : forall (f pc pc' : Term),
      step pc pc' -> step (HoleFill f pc) (HoleFill f pc')
  | step_principle_balance_verdict : forall (v v' r : Term),
      step v v' -> step (PrincipleBalance v r) (PrincipleBalance v' r)
  | step_principle_balance_rationale : forall (v r r' : Term),
      step r r' -> step (PrincipleBalance v r) (PrincipleBalance v r')
  | step_unlock_row : forall (row row' body : Term),
      step row row' -> step (Unlock row body) (Unlock row' body)
  | step_unlock_body : forall (row body body' : Term),
      step body body' -> step (Unlock row body) (Unlock row body').

Inductive steps : Term -> Term -> Prop :=
  | steps_refl : forall t, steps t t
  | steps_trans : forall t1 t2 t3,
      step t1 t2 -> steps t2 t3 -> steps t1 t3.



(** Equality includes reflexivity for neutral and suspended type terms. *)
Inductive convertible : Term -> Term -> Prop :=
  | convertible_refl : forall t, convertible t t
  | convertible_step : forall t u, step t u -> convertible t u
  | convertible_sym : forall t u, convertible t u -> convertible u t
  | convertible_trans : forall t u v,
      convertible t u -> convertible u v -> convertible t v.

Theorem step_shift : forall t u, step t u -> forall cut d,
  step (shift cut d t) (shift cut d u).
Proof.
  intros t u H. induction H; intros cut d; simpl;
    try solve [econstructor; eauto].
  - rewrite shift_subst_commute_above by lia. apply step_beta.
  - rewrite shift_subst_commute_above by lia. apply step_zeta.
  - rewrite Nat.add_0_r. apply step_match_wild.
  - rewrite instantiate_args_shift, H0. apply step_match_ctor_fire.
    + assumption.
    + rewrite length_map. assumption.
  - apply step_match_ctor_skip.
    + simpl in *. rewrite length_map. assumption.
    + destruct rest; simpl in *; congruence.
  - rewrite !map_app. simpl. apply step_inductive_args. apply IHstep.
  - rewrite !map_app. simpl. apply step_match_branch. apply IHstep.
  - rewrite !map_app. simpl. apply step_defeasible_exn_guard. apply IHstep.
  - rewrite !map_app. simpl. apply step_defeasible_exn_body. apply IHstep.
Qed.

Theorem steps_shift : forall t u, steps t u -> forall cut d,
  steps (shift cut d t) (shift cut d u).
Proof.
  intros t u H. induction H; intros cut d.
  - apply steps_refl.
  - eapply steps_trans; [apply step_shift; exact H | apply IHsteps].
Qed.

Theorem convertible_shift : forall t u, convertible t u -> forall cut d,
  convertible (shift cut d t) (shift cut d u).
Proof.
  intros t u H. induction H; intros cut d.
  - apply convertible_refl.
  - apply convertible_step. apply step_shift. assumption.
  - apply convertible_sym. apply IHconvertible.
  - eapply convertible_trans; [apply IHconvertible1 | apply IHconvertible2].
Qed.

Theorem step_subst : forall t v, step t v -> forall k u,
  step (subst k u t) (subst k u v).
Proof.
  intros t v H. induction H; intros k u; simpl;
    try solve [econstructor; eauto].
  - rewrite subst_beta_commute. apply step_beta.
  - rewrite subst_beta_commute. apply step_zeta.
  - rewrite Nat.add_0_r, shift_zero. apply step_match_wild.
  - rewrite instantiate_args_subst, H0. apply step_match_ctor_fire.
    + assumption.
    + rewrite length_map. assumption.
  - apply step_match_ctor_skip.
    + simpl in *. rewrite length_map. assumption.
    + destruct rest; simpl in *; congruence.
  - rewrite !map_app. simpl. apply step_inductive_args. apply IHstep.
  - rewrite !map_app. simpl. apply step_match_branch. apply IHstep.
  - rewrite !map_app. simpl. apply step_defeasible_exn_guard. apply IHstep.
  - rewrite !map_app. simpl. apply step_defeasible_exn_body. apply IHstep.
Qed.

Theorem steps_subst : forall t v, steps t v -> forall k u,
  steps (subst k u t) (subst k u v).
Proof.
  intros t v H. induction H; intros k replacement.
  - apply steps_refl.
  - eapply steps_trans; [apply step_subst; exact H | apply IHsteps].
Qed.

Theorem convertible_subst : forall t v, convertible t v -> forall k u,
  convertible (subst k u t) (subst k u v).
Proof.
  intros t v H. induction H; intros k replacement.
  - apply convertible_refl.
  - apply convertible_step. apply step_subst. assumption.
  - apply convertible_sym. apply IHconvertible.
  - eapply convertible_trans; [apply IHconvertible1 | apply IHconvertible2].
Qed.

Print Assumptions step_subst.
Print Assumptions steps_subst.
Print Assumptions convertible_subst.

Example neutral_reflexivity : forall f a,
  convertible (App f a) (App f a).
Proof. intros. apply convertible_refl. Qed.

Example lazy_wildcard : forall scrut ret body rest,
  step (Match scrut ret (MkBranch PWild body :: rest)) body.
Proof. intros. apply step_match_wild. Qed.

Print Assumptions step_shift.
Print Assumptions steps_shift.
Print Assumptions convertible_shift.
Print Assumptions neutral_reflexivity.
Print Assumptions lazy_wildcard.
End Conversion.
