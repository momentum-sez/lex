From Stdlib Require Import Lists.List Strings.String Arith.Arith Lia.
From Lex Require Import Syntax DeBruijn Typing.
From P04Substitution Require Import SimultaneousArgs.
From P04Source Require Import TypeReduction.
From P04Products Require Import Parallel Products.
Import ListNotations.
Import Conversion.

Lemma steps_map : forall F, (forall x y, step x y -> step (F x) (F y)) ->
 forall x y, steps x y -> steps (F x) (F y).
Proof. intros F HF x y H; induction H; eauto using steps. Qed.

Lemma steps_cong2 : forall F,
 (forall x y z, step x y -> step (F x z) (F y z)) ->
 (forall x y z, step x y -> step (F z x) (F z y)) ->
 forall a a' b b', steps a a' -> steps b b' -> steps (F a b) (F a' b').
Proof.
 intros F H1 H2 a a' b b' Ha Hb.
 eapply steps_append; [eapply steps_map with (F := fun x => F x b); [intros; apply H1; assumption | exact Ha] |].
 eapply steps_map with (F := fun x => F a' x); [intros; apply H2; assumption | exact Hb].
Qed.

Lemma steps_cong3 : forall F,
 (forall x y a b, step x y -> step (F x a b) (F y a b)) ->
 (forall x y a b, step x y -> step (F a x b) (F a y b)) ->
 (forall x y a b, step x y -> step (F a b x) (F a b y)) ->
 forall a a' b b' c c', steps a a' -> steps b b' -> steps c c' ->
 steps (F a b c) (F a' b' c').
Proof.
 intros F H1 H2 H3 a a' b b' c c' Ha Hb Hc.
 eapply steps_append; [eapply steps_map with (F := fun x => F x b c); [intros; apply H1; assumption | exact Ha] |].
 eapply steps_append; [eapply steps_map with (F := fun x => F a' x c); [intros; apply H2; assumption | exact Hb] |].
 eapply steps_map with (F := fun x => F a' b' x); [intros; apply H3; assumption | exact Hc].
Qed.

Lemma steps_list_context : forall (F : list Term -> Term),
 (forall pre a a' post, step a a' -> step (F (pre ++ a :: post)) (F (pre ++ a' :: post))) ->
 forall xs ys, Forall2 steps xs ys -> forall pre,
 steps (F (pre ++ xs)) (F (pre ++ ys)).
Proof.
 intros F HF xs ys H. induction H; intros pre; [constructor |].
 eapply steps_append.
 - eapply steps_map with (F := fun t => F (pre ++ t :: l)); [intros; apply HF; assumption | exact H].
 - specialize (IHForall2 (pre ++ [y])). rewrite <- !app_assoc in IHForall2; simpl in IHForall2. exact IHForall2.
Qed.

Definition branch_steps (b b' : Branch) : Prop :=
 exists pat t t', b = MkBranch pat t /\ b' = MkBranch pat t' /\ steps t t'.
Definition exception_steps (e e' : Exception) : Prop :=
 exists prio g g' b b', e = MkException g b prio /\ e' = MkException g' b' prio /\ steps g g' /\ steps b b'.

Lemma steps_branches : forall bs bs', Forall2 branch_steps bs bs' ->
 forall scrut ret pre, steps (Match scrut ret (pre ++ bs)) (Match scrut ret (pre ++ bs')).
Proof.
 intros bs bs' H; induction H; intros s r pre; [constructor |].
 destruct H as [pat [t [t' [E [E' Ht]]]]]; subst.
 eapply steps_append.
 - eapply steps_map with (F := fun z => Match s r (pre ++ MkBranch pat z :: l));
   [intros; apply step_match_branch; assumption | exact Ht].
 - specialize (IHForall2 s r (pre ++ [MkBranch pat t'])).
   rewrite <- !app_assoc in IHForall2; simpl in IHForall2. exact IHForall2.
Qed.

Lemma steps_exceptions : forall es es', Forall2 exception_steps es es' ->
 forall ty body pre, steps (Defeasible ty body (pre ++ es)) (Defeasible ty body (pre ++ es')).
Proof.
 intros es es' H; induction H; intros ty body pre; [constructor |].
 destruct H as [prio [g [g' [b [b' [E [E' [Hg Hb]]]]]]]]; subst.
 eapply steps_append.
 - eapply steps_map with (F := fun z => Defeasible ty body (pre ++ MkException z b prio :: l));
   [intros; apply step_defeasible_exn_guard; assumption | exact Hg].
 - eapply steps_append.
   + eapply steps_map with (F := fun z => Defeasible ty body (pre ++ MkException g' z prio :: l));
     [intros; apply step_defeasible_exn_body; assumption | exact Hb].
   + specialize (IHForall2 ty body (pre ++ [MkException g' b' prio])).
     rewrite <- !app_assoc in IHForall2; simpl in IHForall2. exact IHForall2.
Qed.

Lemma steps_intro : forall name args args', Forall2 steps args args' ->
 steps (InductiveIntro name args) (InductiveIntro name args').
Proof.
 intros name args args' H.
 change (steps (InductiveIntro name ([] ++ args)) (InductiveIntro name ([] ++ args'))).
 eapply steps_list_context; [intros; apply step_inductive_args; assumption | exact H].
Qed.

Lemma steps_match : forall s s' r r' bs bs',
 steps s s' -> steps r r' -> Forall2 branch_steps bs bs' ->
 steps (Match s r bs) (Match s' r' bs').
Proof.
 intros s s' r r' bs bs' Hs Hr Hbs.
 eapply steps_append; [eapply steps_cong2 with (F := fun s r => Match s r bs);
   eauto using step_match_scrutinee, step_match_ret |].
 apply (steps_branches _ _ Hbs s' r' []).
Qed.

Lemma steps_defeasible : forall ty ty' b b' es es',
 steps ty ty' -> steps b b' -> Forall2 exception_steps es es' ->
 steps (Defeasible ty b es) (Defeasible ty' b' es').
Proof.
 intros ty ty' b b' es es' Hty Hb Hes.
 eapply steps_append; [eapply steps_cong2 with (F := fun ty b => Defeasible ty b es);
   eauto using step_defeasible_ty, step_defeasible_body |].
 apply (steps_exceptions _ _ Hes ty' b' []).
Qed.

Lemma branch_steps_refl : forall b, branch_steps b b.
Proof. intros [p t]; exists p, t, t; repeat split; constructor. Qed.
Lemma branches_steps_refl : forall bs, Forall2 branch_steps bs bs.
Proof. induction bs; constructor; auto using branch_steps_refl. Qed.
Lemma exception_steps_refl : forall e, exception_steps e e.
Proof. intros [g b prio]; exists prio, g, g, b, b; repeat split; constructor. Qed.
Lemma exceptions_steps_refl : forall es, Forall2 exception_steps es es.
Proof. induction es; constructor; auto using exception_steps_refl. Qed.

Theorem parallel_steps_all :
 (forall t u, par t u -> steps t u) /\
 (forall xs ys, pars xs ys -> Forall2 steps xs ys) /\
 (forall bs bs', parbs bs bs' -> Forall2 branch_steps bs bs') /\
 (forall es es', pares es es' -> Forall2 exception_steps es es').
Proof.
 apply parallel_ind.
 - intros; constructor.
 - intros; constructor.
 - intros; constructor.
 - intros; constructor.
 - intros; constructor.
 - intros; constructor.
 - intros; constructor.
 - intros; constructor.
 -  intros; eapply steps_cong2 with (F := Pair); eauto using step_pair_fst, step_pair_snd.
 - intros f; intros; eapply steps_map with (F := fun a => Proj f a); eauto using step_proj.
 -  intros; eapply steps_cong2 with (F := App); eauto using step_app_func, step_app_arg.
 -  intros; eapply steps_map with (F := SanctionsDominance); eauto using step_sanctions_dominance.
 -  intros; eapply steps_map with (F := DefeatElim); eauto using step_defeat_elim.
 -  intros; eapply steps_map with (F := Lift0); eauto using step_lift0.
 -  intros; eapply steps_cong2 with (F := Derive1); eauto using step_derive1_time, step_derive1_wit.
 -  intros; eapply steps_cong2 with (F := Lambda); eauto using step_lambda_dom, step_lambda_body.
 - intros eff; intros; eapply steps_cong2 with (F := fun a b => Pi a eff b); eauto using step_pi_dom, step_pi_cod.
 -  intros; eapply steps_cong2 with (F := Sigma); eauto using step_sigma_fst, step_sigma_snd.
 -  intros; eapply steps_cong2 with (F := Annot); eauto using step_annot_e, step_annot_ty.
 -  intros; eapply steps_cong3 with (F := Let); eauto using step_let_ty, step_let_val, step_let_body.
 -  intros; eapply steps_cong2 with (F := Rec); eauto using step_rec_ty, step_rec_body.
 -  intros; eapply steps_cong2 with (F := ModalAt); eauto using step_modal_at_time, step_modal_at_body.
 -  intros; eapply steps_cong2 with (F := ModalEventually); eauto using step_modal_eventually_time, step_modal_eventually_body.
 -  intros; eapply steps_cong3 with (F := ModalAlways); eauto using step_modal_always_from, step_modal_always_to, step_modal_always_body.
 - intros tr; intros; eapply steps_map with (F := fun a => ModalIntro tr a); eauto using step_modal_intro.
 - intros t1 t2; intros; eapply steps_cong2 with (F := fun a b => ModalElim t1 t2 a b); eauto using step_modal_elim_e, step_modal_elim_w.
 -  intros; eapply steps_map with (F := Hole); eauto using step_hole.
 -  intros; eapply steps_cong2 with (F := HoleFill); eauto using step_hole_fill_filler, step_hole_fill_pc.
 -  intros; eapply steps_cong2 with (F := PrincipleBalance); eauto using step_principle_balance_verdict, step_principle_balance_rationale.
 -  intros; eapply steps_cong2 with (F := Unlock); eauto using step_unlock_row, step_unlock_body.
 - intros; apply steps_intro; assumption.
 - intros; apply steps_match; assumption.
 - intros; apply steps_defeasible; assumption.
 - intros dom body body' arg arg' Hb IHb Ha IHa.
   eapply steps_append with (b := App (Lambda dom body') arg').
   + eapply steps_cong2 with (F := App); eauto using step_app_func, step_app_arg.
     eapply steps_map with (F := Lambda dom); eauto using step_lambda_body.
   + eapply steps_trans; [apply step_beta | constructor].
 - intros ty val val' body body' Hv IHv Hb IHb.
   eapply steps_append with (b := Let ty val' body').
   + eapply steps_cong3 with (F := Let); eauto using step_let_ty, step_let_val, step_let_body, steps_refl.
   + eapply steps_trans; [apply step_zeta | constructor].
 - intros; eapply steps_trans; [apply step_annot | assumption].
 - intros; eapply steps_trans; [apply step_defeasible_empty | assumption].
 - intros; eapply steps_trans; [apply step_match_wild | assumption].
 - intros name name' args args' ret body body' n rest He Hn Ha IHa Hb IHb.
   eapply steps_append with (b := Match (InductiveIntro name args') ret (MkBranch (PCtor name' n) body' :: rest)).
   + apply steps_match; [apply steps_intro; exact IHa | constructor |].
     constructor; [exists (PCtor name' n), body, body'; repeat split; auto | apply branches_steps_refl].
   + eapply steps_trans; [apply step_match_ctor_fire; [exact He | rewrite <- (pars_length _ _ Ha); exact Hn] | constructor].
 - intros name name' args args' ret ret' body n rest rest' Hg Hne Ha IHa Hr IHr Hbs IHbs.
   eapply steps_append with (b := Match (InductiveIntro name args') ret' (MkBranch (PCtor name' n) body :: rest')).
   + apply steps_match; [apply steps_intro; exact IHa | exact IHr |].
     constructor; [apply branch_steps_refl | exact IHbs].
   + eapply steps_trans; [apply step_match_ctor_skip | constructor].
     * simpl in *. rewrite <- (pars_length _ _ Ha). exact Hg.
     * intro E. apply Hne. apply length_zero_iff_nil. rewrite (parbs_length _ _ Hbs), E. reflexivity.
 - constructor.
 - intros; constructor; assumption.
 - constructor.
 - intros pat b b' rest rest' Hb IHb Hrest IHrest. constructor; [exists pat, b, b'; repeat split; auto | exact IHrest].
 - constructor.
 - intros g g' b b' prio rest rest' Hg IHg Hb IHb Hr IHr. constructor; [exists prio, g, g', b, b'; repeat split; auto | exact IHr].
Qed.

Theorem parallel_steps : forall t u, par t u -> steps t u.
Proof. exact (proj1 parallel_steps_all). Qed.
Print Assumptions parallel_steps.
