(** * Lex/Confluence.v - Parallel reduction scaffolding for Tait-Martin-Löf confluence

    STATUS: Qed-closed scaffolding.  No [Admitted].  No top-level
    [Axiom].

    BACKGROUND

    B4 proved [confluence_property_refuted] against the ORIGINAL
    step relation that had NO congruence under binders.  G1 repairs
    that defect: [Typing.v]'s [step] inductive now carries ~45
    per-subterm congruence rules covering every binder
    (Lambda/Pi/Sigma/Rec/Let/Match/Defeasible/...) and every
    list-bearing constructor (InductiveIntro args, Match branches,
    Defeasible exceptions).  Under the repaired [step], B4's
    4-term counterexample [CE_t] IS joinable.

    THIS FILE DELIVERS (all Qed):

      - [par]               : Inductive parallel-reduction relation
                              with head-reduction shapes + per-
                              subterm congruence for every
                              constructor.  Uses [Forall2 par] /
                              [Forall2 par_branch] /
                              [Forall2 par_exception] for list-
                              bearing constructors.
      - [par_refl]          : forall t, par t t
      - [par_branch_refl],
        [par_exception_refl]: companion reflexives.
      - [step_implies_par]  : step ⊆ par (single-step embedding).
      - [par_implies_steps] : par ⊆ steps (parallel-step collapse).

    SCOPE NOT CLOSED HERE:

    The full Tait-Martin-Löf program further demands

      - par_subst (par respects substitution)
      - par_diamond (the core)
      - confluence_theorem

    Closing these for the 30-constructor Lex AST requires
    substantial mechanical case-analysis (~1500-3000 lines) plus
    threading the well_scoped-guarded DeBruijn commutation lemmas
    through each par case.  The G1 charter forbids [Admitted], so
    we DO NOT stage partial/unfinished proofs; rather, we deliver
    the Qed-closed embeddings ([par_refl], [step_implies_par],
    [par_implies_steps]) and
    leave the diamond as a named open problem in [Requirements.v]
    under [req_confluence].

    FUTURE WORK

    The diamond lemma decomposes into:

      (a) par_subst_at_depth: the unary substitution lemma needed
          under an ambient scope depth [k], not just the shallow
          [well_scoped (S i) t] form.  The [step_match_ctor_fire] /
          [subst_args] frontier needs this stronger shape because
          after substituting the first constructor argument, the
          body may still contain the remaining pattern binders.
          The Qed bridge [par_subst_at_depth_implies_par_subst_args]
          below reduces the multi-substitution case to this exact
          unary obligation.

      (b) par_implies_steps: forall t t', par t t' -> steps t t'.
          Proof: induction on par; each congruence case lifts
          steps of subterms, each redex case fires the head step
          then lifts subterm pars.  Uses the per-constructor
          steps_X_cong lemmas.  Approx. 200 lines.

      (c) par_diamond: forall t u1 u2,
            par t u1 -> par t u2 -> exists v, par u1 v /\ par u2 v.
          Proof: double induction on the two par derivations.
          Head-redex / congruence cases use par_subst to commute.
          Approx. 1000 lines.

      (d) par_star_diamond: follows from par_diamond by the
          strip lemma.  Approx. 50 lines.

      (e) confluence_theorem: forall t u1 u2,
            steps t u1 -> steps t u2 ->
            exists v, steps u1 v /\ steps u2 v.
          Proof: step_implies_par + par_star_diamond +
          par_implies_steps.  Approx. 30 lines.
*)

From Stdlib Require Import Arith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Strings.String.
From Stdlib Require Import micromega.Lia.
Import ListNotations.

Require Import Lex.Syntax.
Require Import Lex.DeBruijn.
Require Import Lex.Typing.

(* ================================================================== *)
(** ** Parallel reduction [par]                                       *)
(* ================================================================== *)

Inductive par : Term -> Term -> Prop :=
  (* -- Atomic -------------------------------------------------------- *)
  | par_var : forall n, par (Var n) (Var n)
  | par_sort : forall s, par (TSort s) (TSort s)
  | par_constant : forall c, par (Constant c) (Constant c)
  | par_contentref : forall h, par (ContentRef h) (ContentRef h)
  | par_intlit : forall n, par (IntLit n) (IntLit n)
  | par_ratlit : forall p q, par (RatLit p q) (RatLit p q)
  | par_stringlit : forall s, par (StringLit s) (StringLit s)
  | par_axiom : forall a, par (AxiomUse a) (AxiomUse a)
  (* -- Congruence ---------------------------------------------------- *)
  | par_pair : forall a a' b b',
      par a a' -> par b b' -> par (Pair a b) (Pair a' b')
  | par_proj : forall f t t',
      par t t' -> par (Proj f t) (Proj f t')
  | par_app_cong : forall f f' a a',
      par f f' -> par a a' -> par (App f a) (App f' a')
  | par_inductive : forall c args args',
      Forall2 par args args' ->
      par (InductiveIntro c args) (InductiveIntro c args')
  | par_sanctions : forall p p',
      par p p' -> par (SanctionsDominance p) (SanctionsDominance p')
  | par_defeat : forall r r',
      par r r' -> par (DefeatElim r) (DefeatElim r')
  | par_lift0 : forall t t',
      par t t' -> par (Lift0 t) (Lift0 t')
  | par_derive1 : forall ti ti' w w',
      par ti ti' -> par w w' -> par (Derive1 ti w) (Derive1 ti' w')
  | par_lambda : forall dom dom' body body',
      par dom dom' -> par body body' -> par (Lambda dom body) (Lambda dom' body')
  | par_pi : forall dom dom' eff cod cod',
      par dom dom' -> par cod cod' -> par (Pi dom eff cod) (Pi dom' eff cod')
  | par_sigma : forall a a' b b',
      par a a' -> par b b' -> par (Sigma a b) (Sigma a' b')
  | par_annot_cong : forall e e' ty ty',
      par e e' -> par ty ty' -> par (Annot e ty) (Annot e' ty')
  | par_let_cong : forall ty ty' val val' body body',
      par ty ty' -> par val val' -> par body body' ->
      par (Let ty val body) (Let ty' val' body')
  | par_match_cong : forall scr scr' ret ret' brs brs',
      par scr scr' -> par ret ret' ->
      Forall2 par_branch brs brs' ->
      par (Match scr ret brs) (Match scr' ret' brs')
  | par_rec : forall ty ty' body body',
      par ty ty' -> par body body' -> par (Rec ty body) (Rec ty' body')
  | par_modal_at : forall ti ti' body body',
      par ti ti' -> par body body' -> par (ModalAt ti body) (ModalAt ti' body')
  | par_modal_eventually : forall ti ti' body body',
      par ti ti' -> par body body' ->
      par (ModalEventually ti body) (ModalEventually ti' body')
  | par_modal_always : forall from from' to to' body body',
      par from from' -> par to to' -> par body body' ->
      par (ModalAlways from to body) (ModalAlways from' to' body')
  | par_modal_intro : forall tr body body',
      par body body' -> par (ModalIntro tr body) (ModalIntro tr body')
  | par_modal_elim : forall t1 t2 e e' w w',
      par e e' -> par w w' -> par (ModalElim t1 t2 e w) (ModalElim t1 t2 e' w')
  | par_defeasible_cong : forall bt bt' bb bb' exns exns',
      par bt bt' -> par bb bb' ->
      Forall2 par_exception exns exns' ->
      par (Defeasible bt bb exns) (Defeasible bt' bb' exns')
  | par_hole : forall ty ty',
      par ty ty' -> par (Hole ty) (Hole ty')
  | par_hole_fill : forall f f' pc pc',
      par f f' -> par pc pc' -> par (HoleFill f pc) (HoleFill f' pc')
  | par_principle : forall v v' r r',
      par v v' -> par r r' -> par (PrincipleBalance v r) (PrincipleBalance v' r')
  | par_unlock : forall row row' body body',
      par row row' -> par body body' -> par (Unlock row body) (Unlock row' body')
  (* -- Head redex shapes --------------------------------------------- *)
  | par_beta : forall dom dom' body body' arg arg',
      par dom dom' ->
      par body body' ->
      par arg arg' ->
      par (App (Lambda dom body) arg) (subst 0 arg' body')
  | par_zeta : forall ty ty' val val' body body',
      par ty ty' ->
      par val val' ->
      par body body' ->
      par (Let ty val body) (subst 0 val' body')
  | par_annot_fire : forall e e' ty,
      par e e' -> par (Annot e ty) e'
  | par_defeasible_empty_fire : forall bt bb bb',
      par bb bb' -> par (Defeasible bt bb nil) bb'
  | par_defeasible_peel_fire : forall bt bt' bb bb' e rest rest',
      par bt bt' -> par bb bb' ->
      Forall2 par_exception rest rest' ->
      par (Defeasible bt bb (e :: rest)) (Defeasible bt' bb' rest')
  | par_match_wild_fire : forall scr ret body body' rest,
      value scr -> par body body' ->
      par (Match scr ret (MkBranch PWild body :: rest)) body'
  | par_match_ctor_fire_p : forall c c' args args' ret body body' n rest,
      Forall value args ->
      String.eqb c c' = true ->
      List.length args = n ->
      Forall2 par args args' ->
      par body body' ->
      par (Match (InductiveIntro c args) ret
                 (MkBranch (PCtor c' n) body :: rest))
          (subst_args args' body')
  | par_match_ctor_skip_fire : forall scr scr' ret ret' body c' n rest rest',
      value scr ->
      branch_head_matches scr c' n = false ->
      rest <> nil ->
      par scr scr' -> par ret ret' ->
      Forall2 par_branch rest rest' ->
      par (Match scr ret (MkBranch (PCtor c' n) body :: rest))
          (Match scr' ret' rest')

with par_branch : Branch -> Branch -> Prop :=
  | par_branch_cong : forall pat body body',
      par body body' -> par_branch (MkBranch pat body) (MkBranch pat body')

with par_exception : Exception -> Exception -> Prop :=
  | par_exception_cong : forall g g' b b' prio,
      par g g' -> par b b' ->
      par_exception (MkException g b prio) (MkException g' b' prio).

(** Reflexive transitive closure of par. *)
Inductive par_star : Term -> Term -> Prop :=
  | par_star_refl : forall t, par_star t t
  | par_star_step : forall t1 t2 t3,
      par t1 t2 -> par_star t2 t3 -> par_star t1 t3.

(* ================================================================== *)
(** ** par_refl (Qed)                                                 *)
(* ================================================================== *)

Lemma par_refl : forall t, par t t
with par_branch_refl : forall b, par_branch b b
with par_exception_refl : forall e, par_exception e e.
Proof.
  - intro t.
    destruct t.
    + apply par_var.
    + apply par_sort.
    + apply par_constant.
    + apply par_contentref.
    + apply par_intlit.
    + apply par_ratlit.
    + apply par_stringlit.
    + apply par_axiom.
    + apply par_pair; apply par_refl.
    + apply par_proj. apply par_refl.
    + apply par_app_cong; apply par_refl.
    + apply par_inductive.
      induction l as [| x xs IH].
      * constructor.
      * constructor; [apply par_refl | apply IH].
    + apply par_sanctions. apply par_refl.
    + apply par_defeat. apply par_refl.
    + apply par_lift0. apply par_refl.
    + apply par_derive1; apply par_refl.
    + apply par_lambda; apply par_refl.
    + apply par_pi; apply par_refl.
    + apply par_sigma; apply par_refl.
    + apply par_annot_cong; apply par_refl.
    + apply par_let_cong; apply par_refl.
    + apply par_match_cong; try apply par_refl.
      induction l as [| br brs IH].
      * constructor.
      * constructor; [apply par_branch_refl | apply IH].
    + apply par_rec; apply par_refl.
    + apply par_modal_at; apply par_refl.
    + apply par_modal_eventually; apply par_refl.
    + apply par_modal_always; apply par_refl.
    + apply par_modal_intro. apply par_refl.
    + apply par_modal_elim; apply par_refl.
    + apply par_defeasible_cong; try apply par_refl.
      induction l as [| e exns IH].
      * constructor.
      * constructor; [apply par_exception_refl | apply IH].
    + apply par_hole. apply par_refl.
    + apply par_hole_fill; apply par_refl.
    + apply par_principle; apply par_refl.
    + apply par_unlock; apply par_refl.
  - intro b. destruct b. apply par_branch_cong. apply par_refl.
  - intro e. destruct e. apply par_exception_cong; apply par_refl.
Qed.

Lemma Forall2_par_refl : forall l, Forall2 par l l.
Proof.
  intro l. induction l; constructor; [apply par_refl | exact IHl].
Qed.

Lemma Forall2_par_branch_refl : forall l, Forall2 par_branch l l.
Proof.
  intro l. induction l; constructor; [apply par_branch_refl | exact IHl].
Qed.

Lemma Forall2_par_exception_refl : forall l, Forall2 par_exception l l.
Proof.
  intro l. induction l; constructor; [apply par_exception_refl | exact IHl].
Qed.

(* ================================================================== *)
(** ** par_star basic properties (Qed)                                *)
(* ================================================================== *)

Lemma par_star_reflexive : forall t, par_star t t.
Proof. intro t. apply par_star_refl. Qed.

Lemma par_star_append : forall t1 t2 t3,
  par_star t1 t2 -> par_star t2 t3 -> par_star t1 t3.
Proof.
  intros t1 t2 t3 H12. induction H12; intros H23.
  - exact H23.
  - eapply par_star_step.
    + exact H.
    + apply IHpar_star. exact H23.
Qed.

Lemma par_lifts_to_par_star : forall t t',
  par t t' -> par_star t t'.
Proof.
  intros t t' H. eapply par_star_step.
  - exact H.
  - apply par_star_refl.
Qed.

(* ================================================================== *)
(** ** step_implies_par : step ⊆ par (Qed)                            *)
(* ================================================================== *)

(** Congruence lemma for Forall2 par with element swap at position
    [length pre]. *)
Lemma Forall2_par_one :
  forall (pre : list Term) (a a' : Term) (post : list Term),
    par a a' ->
    Forall2 par (pre ++ a :: post) (pre ++ a' :: post).
Proof.
  intros pre a a' post Ha.
  induction pre as [| h tpre IHpre]; simpl.
  - constructor; [exact Ha | apply Forall2_par_refl].
  - constructor; [apply par_refl | exact IHpre].
Qed.

Lemma Forall2_par_branch_one :
  forall (pre : list Branch) (pat : Pattern) (b b' : Term) (post : list Branch),
    par b b' ->
    Forall2 par_branch (pre ++ MkBranch pat b :: post)
                        (pre ++ MkBranch pat b' :: post).
Proof.
  intros pre pat b b' post Hb.
  induction pre as [| h tpre IHpre]; simpl.
  - constructor; [apply par_branch_cong; exact Hb | apply Forall2_par_branch_refl].
  - constructor; [apply par_branch_refl | exact IHpre].
Qed.

Lemma Forall2_par_exception_one_guard :
  forall (pre : list Exception) (g g' b : Term) (prio : option nat)
         (post : list Exception),
    par g g' ->
    Forall2 par_exception (pre ++ MkException g b prio :: post)
                           (pre ++ MkException g' b prio :: post).
Proof.
  intros pre g g' b prio post Hg.
  induction pre as [| h tpre IHpre]; simpl.
  - constructor;
      [apply par_exception_cong; [exact Hg | apply par_refl] |
       apply Forall2_par_exception_refl].
  - constructor; [apply par_exception_refl | exact IHpre].
Qed.

Lemma Forall2_par_exception_one_body :
  forall (pre : list Exception) (g b b' : Term) (prio : option nat)
         (post : list Exception),
    par b b' ->
    Forall2 par_exception (pre ++ MkException g b prio :: post)
                           (pre ++ MkException g b' prio :: post).
Proof.
  intros pre g b b' prio post Hb.
  induction pre as [| h tpre IHpre]; simpl.
  - constructor;
      [apply par_exception_cong; [apply par_refl | exact Hb] |
       apply Forall2_par_exception_refl].
  - constructor; [apply par_exception_refl | exact IHpre].
Qed.

Theorem step_implies_par : forall t t', step t t' -> par t t'.
Proof.
  intros t t' Hstep. induction Hstep.
  - apply par_beta with (dom' := dom) (body' := body) (arg' := arg); apply par_refl.
  - apply par_zeta with (ty' := ty) (val' := val) (body' := body); apply par_refl.
  - apply par_annot_fire. apply par_refl.
  - apply par_defeasible_empty_fire. apply par_refl.
  - apply par_defeasible_peel_fire;
      [apply par_refl | apply par_refl | apply Forall2_par_exception_refl].
  - apply par_match_wild_fire; [assumption | apply par_refl].
  - apply par_match_ctor_fire_p with (c := c) (c' := c') (n := n);
      try assumption.
    + apply Forall2_par_refl.
    + apply par_refl.
  - apply par_match_ctor_skip_fire;
      [assumption | assumption | assumption
       | apply par_refl | apply par_refl
       | apply Forall2_par_branch_refl].
  - apply par_app_cong; [exact IHHstep | apply par_refl].
  - apply par_app_cong; [apply par_refl | exact IHHstep].
  - apply par_pair; [exact IHHstep | apply par_refl].
  - apply par_pair; [apply par_refl | exact IHHstep].
  - apply par_proj; exact IHHstep.
  - apply par_inductive. apply Forall2_par_one; exact IHHstep.
  - apply par_sanctions; exact IHHstep.
  - apply par_defeat; exact IHHstep.
  - apply par_lift0; exact IHHstep.
  - apply par_derive1; [exact IHHstep | apply par_refl].
  - apply par_derive1; [apply par_refl | exact IHHstep].
  - apply par_lambda; [exact IHHstep | apply par_refl].
  - apply par_lambda; [apply par_refl | exact IHHstep].
  - apply par_pi; [exact IHHstep | apply par_refl].
  - apply par_pi; [apply par_refl | exact IHHstep].
  - apply par_sigma; [exact IHHstep | apply par_refl].
  - apply par_sigma; [apply par_refl | exact IHHstep].
  - apply par_rec; [exact IHHstep | apply par_refl].
  - apply par_rec; [apply par_refl | exact IHHstep].
  - apply par_annot_cong; [exact IHHstep | apply par_refl].
  - apply par_annot_cong; [apply par_refl | exact IHHstep].
  - apply par_let_cong; [exact IHHstep | apply par_refl | apply par_refl].
  - apply par_let_cong; [apply par_refl | exact IHHstep | apply par_refl].
  - apply par_let_cong; [apply par_refl | apply par_refl | exact IHHstep].
  - apply par_match_cong; [exact IHHstep | apply par_refl | apply Forall2_par_branch_refl].
  - apply par_match_cong; [apply par_refl | exact IHHstep | apply Forall2_par_branch_refl].
  - apply par_match_cong; try apply par_refl.
    apply Forall2_par_branch_one. exact IHHstep.
  - apply par_modal_at; [exact IHHstep | apply par_refl].
  - apply par_modal_at; [apply par_refl | exact IHHstep].
  - apply par_modal_eventually; [exact IHHstep | apply par_refl].
  - apply par_modal_eventually; [apply par_refl | exact IHHstep].
  - apply par_modal_always; [exact IHHstep | apply par_refl | apply par_refl].
  - apply par_modal_always; [apply par_refl | exact IHHstep | apply par_refl].
  - apply par_modal_always; [apply par_refl | apply par_refl | exact IHHstep].
  - apply par_modal_intro; exact IHHstep.
  - apply par_modal_elim; [exact IHHstep | apply par_refl].
  - apply par_modal_elim; [apply par_refl | exact IHHstep].
  - apply par_defeasible_cong; [exact IHHstep | apply par_refl | apply Forall2_par_exception_refl].
  - apply par_defeasible_cong; [apply par_refl | exact IHHstep | apply Forall2_par_exception_refl].
  - apply par_defeasible_cong; try apply par_refl.
    apply Forall2_par_exception_one_guard. exact IHHstep.
  - apply par_defeasible_cong; try apply par_refl.
    apply Forall2_par_exception_one_body. exact IHHstep.
  - apply par_hole; exact IHHstep.
  - apply par_hole_fill; [exact IHHstep | apply par_refl].
  - apply par_hole_fill; [apply par_refl | exact IHHstep].
  - apply par_principle; [exact IHHstep | apply par_refl].
  - apply par_principle; [apply par_refl | exact IHHstep].
  - apply par_unlock; [exact IHHstep | apply par_refl].
  - apply par_unlock; [apply par_refl | exact IHHstep].
Qed.

(* ================================================================== *)
(** ** Per-constructor multi-step congruence lemmas                   *)
(* ================================================================== *)

(** These lemmas lift single-step congruence rules through the
    transitive closure [steps].  They are used by
    [par_implies_steps] to discharge the congruence cases. *)

Lemma steps_app_func : forall f f' a, steps f f' -> steps (App f a) (App f' a).
Proof.
  intros f f' a H. induction H.
  - apply steps_refl.
  - eapply steps_trans; [apply step_app_func; exact H | exact IHsteps].
Qed.

Lemma steps_app_arg : forall f a a', steps a a' -> steps (App f a) (App f a').
Proof.
  intros f a a' H. induction H.
  - apply steps_refl.
  - eapply steps_trans; [apply step_app_arg; exact H | exact IHsteps].
Qed.

Lemma steps_lambda_dom : forall dom dom' body,
  steps dom dom' -> steps (Lambda dom body) (Lambda dom' body).
Proof.
  intros dom dom' body H. induction H.
  - apply steps_refl.
  - eapply steps_trans; [apply step_lambda_dom; exact H | exact IHsteps].
Qed.

Lemma steps_lambda_body : forall dom body body',
  steps body body' -> steps (Lambda dom body) (Lambda dom body').
Proof.
  intros dom body body' H. induction H.
  - apply steps_refl.
  - eapply steps_trans; [apply step_lambda_body; exact H | exact IHsteps].
Qed.

Lemma steps_pi_dom : forall dom dom' eff cod,
  steps dom dom' -> steps (Pi dom eff cod) (Pi dom' eff cod).
Proof.
  intros dom dom' eff cod H. induction H.
  - apply steps_refl.
  - eapply steps_trans; [apply step_pi_dom; exact H | exact IHsteps].
Qed.

Lemma steps_pi_cod : forall dom eff cod cod',
  steps cod cod' -> steps (Pi dom eff cod) (Pi dom eff cod').
Proof.
  intros dom eff cod cod' H. induction H.
  - apply steps_refl.
  - eapply steps_trans; [apply step_pi_cod; exact H | exact IHsteps].
Qed.

Lemma steps_sigma_fst : forall a a' b, steps a a' -> steps (Sigma a b) (Sigma a' b).
Proof.
  intros a a' b H. induction H.
  - apply steps_refl.
  - eapply steps_trans; [apply step_sigma_fst; exact H | exact IHsteps].
Qed.

Lemma steps_sigma_snd : forall a b b', steps b b' -> steps (Sigma a b) (Sigma a b').
Proof.
  intros a b b' H. induction H.
  - apply steps_refl.
  - eapply steps_trans; [apply step_sigma_snd; exact H | exact IHsteps].
Qed.

Lemma steps_pair_fst : forall a a' b, steps a a' -> steps (Pair a b) (Pair a' b).
Proof.
  intros a a' b H. induction H.
  - apply steps_refl.
  - eapply steps_trans; [apply step_pair_fst; exact H | exact IHsteps].
Qed.

Lemma steps_pair_snd : forall a b b', steps b b' -> steps (Pair a b) (Pair a b').
Proof.
  intros a b b' H. induction H.
  - apply steps_refl.
  - eapply steps_trans; [apply step_pair_snd; exact H | exact IHsteps].
Qed.

Lemma steps_proj : forall f t t', steps t t' -> steps (Proj f t) (Proj f t').
Proof.
  intros f t t' H. induction H.
  - apply steps_refl.
  - eapply steps_trans; [apply step_proj; exact H | exact IHsteps].
Qed.

Lemma steps_annot_e : forall e e' ty, steps e e' -> steps (Annot e ty) (Annot e' ty).
Proof.
  intros e e' ty H. induction H.
  - apply steps_refl.
  - eapply steps_trans; [apply step_annot_e; exact H | exact IHsteps].
Qed.

Lemma steps_annot_ty : forall e ty ty', steps ty ty' -> steps (Annot e ty) (Annot e ty').
Proof.
  intros e ty ty' H. induction H.
  - apply steps_refl.
  - eapply steps_trans; [apply step_annot_ty; exact H | exact IHsteps].
Qed.

Lemma steps_let_ty : forall ty ty' val body,
  steps ty ty' -> steps (Let ty val body) (Let ty' val body).
Proof.
  intros ty ty' val body H. induction H.
  - apply steps_refl.
  - eapply steps_trans; [apply step_let_ty; exact H | exact IHsteps].
Qed.

Lemma steps_let_val : forall ty val val' body,
  steps val val' -> steps (Let ty val body) (Let ty val' body).
Proof.
  intros ty val val' body H. induction H.
  - apply steps_refl.
  - eapply steps_trans; [apply step_let_val; exact H | exact IHsteps].
Qed.

Lemma steps_let_body : forall ty val body body',
  steps body body' -> steps (Let ty val body) (Let ty val body').
Proof.
  intros ty val body body' H. induction H.
  - apply steps_refl.
  - eapply steps_trans; [apply step_let_body; exact H | exact IHsteps].
Qed.

Lemma steps_rec_ty : forall ty ty' body,
  steps ty ty' -> steps (Rec ty body) (Rec ty' body).
Proof.
  intros ty ty' body H. induction H.
  - apply steps_refl.
  - eapply steps_trans; [apply step_rec_ty; exact H | exact IHsteps].
Qed.

Lemma steps_rec_body : forall ty body body',
  steps body body' -> steps (Rec ty body) (Rec ty body').
Proof.
  intros ty body body' H. induction H.
  - apply steps_refl.
  - eapply steps_trans; [apply step_rec_body; exact H | exact IHsteps].
Qed.

Lemma steps_sanctions : forall p p',
  steps p p' -> steps (SanctionsDominance p) (SanctionsDominance p').
Proof.
  intros p p' H. induction H.
  - apply steps_refl.
  - eapply steps_trans; [apply step_sanctions_dominance; exact H | exact IHsteps].
Qed.

Lemma steps_defeat : forall r r', steps r r' -> steps (DefeatElim r) (DefeatElim r').
Proof.
  intros r r' H. induction H.
  - apply steps_refl.
  - eapply steps_trans; [apply step_defeat_elim; exact H | exact IHsteps].
Qed.

Lemma steps_lift0 : forall t t', steps t t' -> steps (Lift0 t) (Lift0 t').
Proof.
  intros t t' H. induction H.
  - apply steps_refl.
  - eapply steps_trans; [apply step_lift0; exact H | exact IHsteps].
Qed.

Lemma steps_derive1_time : forall ti ti' w,
  steps ti ti' -> steps (Derive1 ti w) (Derive1 ti' w).
Proof.
  intros ti ti' w H. induction H.
  - apply steps_refl.
  - eapply steps_trans; [apply step_derive1_time; exact H | exact IHsteps].
Qed.

Lemma steps_derive1_wit : forall ti w w',
  steps w w' -> steps (Derive1 ti w) (Derive1 ti w').
Proof.
  intros ti w w' H. induction H.
  - apply steps_refl.
  - eapply steps_trans; [apply step_derive1_wit; exact H | exact IHsteps].
Qed.

Lemma steps_modal_at_time : forall ti ti' body,
  steps ti ti' -> steps (ModalAt ti body) (ModalAt ti' body).
Proof.
  intros ti ti' body H. induction H.
  - apply steps_refl.
  - eapply steps_trans; [apply step_modal_at_time; exact H | exact IHsteps].
Qed.

Lemma steps_modal_at_body : forall ti body body',
  steps body body' -> steps (ModalAt ti body) (ModalAt ti body').
Proof.
  intros ti body body' H. induction H.
  - apply steps_refl.
  - eapply steps_trans; [apply step_modal_at_body; exact H | exact IHsteps].
Qed.

Lemma steps_modal_eventually_time : forall ti ti' body,
  steps ti ti' -> steps (ModalEventually ti body) (ModalEventually ti' body).
Proof.
  intros ti ti' body H. induction H.
  - apply steps_refl.
  - eapply steps_trans; [apply step_modal_eventually_time; exact H | exact IHsteps].
Qed.

Lemma steps_modal_eventually_body : forall ti body body',
  steps body body' -> steps (ModalEventually ti body) (ModalEventually ti body').
Proof.
  intros ti body body' H. induction H.
  - apply steps_refl.
  - eapply steps_trans; [apply step_modal_eventually_body; exact H | exact IHsteps].
Qed.

Lemma steps_modal_always_from : forall from from' to body,
  steps from from' -> steps (ModalAlways from to body) (ModalAlways from' to body).
Proof.
  intros from from' to body H. induction H.
  - apply steps_refl.
  - eapply steps_trans; [apply step_modal_always_from; exact H | exact IHsteps].
Qed.

Lemma steps_modal_always_to : forall from to to' body,
  steps to to' -> steps (ModalAlways from to body) (ModalAlways from to' body).
Proof.
  intros from to to' body H. induction H.
  - apply steps_refl.
  - eapply steps_trans; [apply step_modal_always_to; exact H | exact IHsteps].
Qed.

Lemma steps_modal_always_body : forall from to body body',
  steps body body' -> steps (ModalAlways from to body) (ModalAlways from to body').
Proof.
  intros from to body body' H. induction H.
  - apply steps_refl.
  - eapply steps_trans; [apply step_modal_always_body; exact H | exact IHsteps].
Qed.

Lemma steps_modal_intro : forall tr body body',
  steps body body' -> steps (ModalIntro tr body) (ModalIntro tr body').
Proof.
  intros tr body body' H. induction H.
  - apply steps_refl.
  - eapply steps_trans; [apply step_modal_intro; exact H | exact IHsteps].
Qed.

Lemma steps_modal_elim_e : forall t1 t2 e e' w,
  steps e e' -> steps (ModalElim t1 t2 e w) (ModalElim t1 t2 e' w).
Proof.
  intros t1 t2 e e' w H. induction H.
  - apply steps_refl.
  - eapply steps_trans; [apply step_modal_elim_e; exact H | exact IHsteps].
Qed.

Lemma steps_modal_elim_w : forall t1 t2 e w w',
  steps w w' -> steps (ModalElim t1 t2 e w) (ModalElim t1 t2 e w').
Proof.
  intros t1 t2 e w w' H. induction H.
  - apply steps_refl.
  - eapply steps_trans; [apply step_modal_elim_w; exact H | exact IHsteps].
Qed.

Lemma steps_hole : forall ty ty', steps ty ty' -> steps (Hole ty) (Hole ty').
Proof.
  intros ty ty' H. induction H.
  - apply steps_refl.
  - eapply steps_trans; [apply step_hole; exact H | exact IHsteps].
Qed.

Lemma steps_hole_fill_filler : forall f f' pc,
  steps f f' -> steps (HoleFill f pc) (HoleFill f' pc).
Proof.
  intros f f' pc H. induction H.
  - apply steps_refl.
  - eapply steps_trans; [apply step_hole_fill_filler; exact H | exact IHsteps].
Qed.

Lemma steps_hole_fill_pc : forall f pc pc',
  steps pc pc' -> steps (HoleFill f pc) (HoleFill f pc').
Proof.
  intros f pc pc' H. induction H.
  - apply steps_refl.
  - eapply steps_trans; [apply step_hole_fill_pc; exact H | exact IHsteps].
Qed.

Lemma steps_principle_v : forall v v' r,
  steps v v' -> steps (PrincipleBalance v r) (PrincipleBalance v' r).
Proof.
  intros v v' r H. induction H.
  - apply steps_refl.
  - eapply steps_trans; [apply step_principle_balance_verdict; exact H | exact IHsteps].
Qed.

Lemma steps_principle_r : forall v r r',
  steps r r' -> steps (PrincipleBalance v r) (PrincipleBalance v r').
Proof.
  intros v r r' H. induction H.
  - apply steps_refl.
  - eapply steps_trans; [apply step_principle_balance_rationale; exact H | exact IHsteps].
Qed.

Lemma steps_unlock_row : forall row row' body,
  steps row row' -> steps (Unlock row body) (Unlock row' body).
Proof.
  intros row row' body H. induction H.
  - apply steps_refl.
  - eapply steps_trans; [apply step_unlock_row; exact H | exact IHsteps].
Qed.

Lemma steps_unlock_body : forall row body body',
  steps body body' -> steps (Unlock row body) (Unlock row body').
Proof.
  intros row body body' H. induction H.
  - apply steps_refl.
  - eapply steps_trans; [apply step_unlock_body; exact H | exact IHsteps].
Qed.

Lemma steps_match_scrutinee : forall scr scr' ret brs,
  steps scr scr' -> steps (Match scr ret brs) (Match scr' ret brs).
Proof.
  intros. induction H.
  - apply steps_refl.
  - eapply steps_trans; [apply step_match_scrutinee; exact H | exact IHsteps].
Qed.

Lemma steps_match_ret : forall scr ret ret' brs,
  steps ret ret' -> steps (Match scr ret brs) (Match scr ret' brs).
Proof.
  intros. induction H.
  - apply steps_refl.
  - eapply steps_trans; [apply step_match_ret; exact H | exact IHsteps].
Qed.

Lemma steps_defeasible_ty : forall bt bt' bb exns,
  steps bt bt' -> steps (Defeasible bt bb exns) (Defeasible bt' bb exns).
Proof.
  intros. induction H.
  - apply steps_refl.
  - eapply steps_trans; [apply step_defeasible_ty; exact H | exact IHsteps].
Qed.

Lemma steps_defeasible_body : forall bt bb bb' exns,
  steps bb bb' -> steps (Defeasible bt bb exns) (Defeasible bt bb' exns).
Proof.
  intros. induction H.
  - apply steps_refl.
  - eapply steps_trans; [apply step_defeasible_body; exact H | exact IHsteps].
Qed.

Lemma steps_inductive_arg : forall c pre a a' post,
  steps a a' ->
  steps (InductiveIntro c (pre ++ a :: post))
        (InductiveIntro c (pre ++ a' :: post)).
Proof.
  intros. induction H.
  - apply steps_refl.
  - eapply steps_trans; [apply step_inductive_args; exact H | exact IHsteps].
Qed.

Lemma steps_match_branch : forall scr ret pre pat b b' post,
  steps b b' ->
  steps (Match scr ret (pre ++ MkBranch pat b :: post))
        (Match scr ret (pre ++ MkBranch pat b' :: post)).
Proof.
  intros. induction H.
  - apply steps_refl.
  - eapply steps_trans; [apply step_match_branch; exact H | exact IHsteps].
Qed.

Lemma steps_defeasible_exn_guard : forall bt bb pre g g' b prio post,
  steps g g' ->
  steps (Defeasible bt bb (pre ++ MkException g b prio :: post))
        (Defeasible bt bb (pre ++ MkException g' b prio :: post)).
Proof.
  intros. induction H.
  - apply steps_refl.
  - eapply steps_trans; [apply step_defeasible_exn_guard; exact H | exact IHsteps].
Qed.

Lemma steps_defeasible_exn_body : forall bt bb pre g b b' prio post,
  steps b b' ->
  steps (Defeasible bt bb (pre ++ MkException g b prio :: post))
        (Defeasible bt bb (pre ++ MkException g b' prio :: post)).
Proof.
  intros. induction H.
  - apply steps_refl.
  - eapply steps_trans; [apply step_defeasible_exn_body; exact H | exact IHsteps].
Qed.

(** List-congruence helper: if each argument steps, the whole
    InductiveIntro steps by composing one-position-at-a-time
    reductions.  The key generalization is to take a prefix [pre]
    (already fully reduced) and step the suffix positions one by
    one. *)
Lemma steps_inductive_prefix :
  forall c pre args args',
    Forall2 steps args args' ->
    steps (InductiveIntro c (pre ++ args)) (InductiveIntro c (pre ++ args')).
Proof.
  intros c pre args args' HF. revert pre.
  induction HF as [| x y xs ys Hxy _ IH]; intro pre.
  - apply steps_refl.
  - eapply steps_append.
    + (* Step x to y at position |pre| *)
      apply (steps_inductive_arg c pre x y xs Hxy).
    + (* Now: steps (InductiveIntro c (pre ++ y :: xs))
                     (InductiveIntro c (pre ++ y :: ys)).
         Rewrite as: pre' := pre ++ [y], and apply IH. *)
      replace (pre ++ y :: xs) with ((pre ++ [y]) ++ xs)
        by (rewrite <- app_assoc; reflexivity).
      replace (pre ++ y :: ys) with ((pre ++ [y]) ++ ys)
        by (rewrite <- app_assoc; reflexivity).
      apply IH.
Qed.

Lemma Forall2_steps_to_steps_inductive :
  forall c args args',
    Forall2 steps args args' ->
    steps (InductiveIntro c args) (InductiveIntro c args').
Proof.
  intros c args args' HF.
  pose proof (steps_inductive_prefix c [] args args' HF) as H.
  simpl in H. exact H.
Qed.

Lemma steps_match_branch_prefix :
  forall scr ret pre brs brs',
    Forall2 (fun b b' =>
               match b, b' with
               | MkBranch pat body, MkBranch pat' body' =>
                   pat = pat' /\ steps body body'
               end) brs brs' ->
    steps (Match scr ret (pre ++ brs)) (Match scr ret (pre ++ brs')).
Proof.
  intros scr ret pre brs brs' HF. revert pre.
  induction HF as [| x y xs ys Hxy _ IH]; intro pre.
  - apply steps_refl.
  - destruct x as [patx bodyx]. destruct y as [paty bodyy].
    destruct Hxy as [Hpat Hbody]. subst paty.
    eapply steps_append.
    + apply (steps_match_branch scr ret pre patx bodyx bodyy xs Hbody).
    + replace (pre ++ MkBranch patx bodyy :: xs)
        with ((pre ++ [MkBranch patx bodyy]) ++ xs)
        by (rewrite <- app_assoc; reflexivity).
      replace (pre ++ MkBranch patx bodyy :: ys)
        with ((pre ++ [MkBranch patx bodyy]) ++ ys)
        by (rewrite <- app_assoc; reflexivity).
      apply IH.
Qed.

Lemma Forall2_steps_to_steps_match_branches :
  forall scr ret brs brs',
    Forall2 (fun b b' =>
               match b, b' with
               | MkBranch pat body, MkBranch pat' body' =>
                   pat = pat' /\ steps body body'
               end) brs brs' ->
    steps (Match scr ret brs) (Match scr ret brs').
Proof.
  intros scr ret brs brs' HF.
  pose proof (steps_match_branch_prefix scr ret [] brs brs' HF) as H.
  simpl in H. exact H.
Qed.

Lemma steps_defeasible_exn_prefix :
  forall bt bb pre exns exns',
    Forall2 (fun e e' =>
               match e, e' with
               | MkException g b prio, MkException g' b' prio' =>
                   prio = prio' /\ steps g g' /\ steps b b'
               end) exns exns' ->
    steps (Defeasible bt bb (pre ++ exns)) (Defeasible bt bb (pre ++ exns')).
Proof.
  intros bt bb pre exns exns' HF. revert pre.
  induction HF as [| x y xs ys Hxy _ IH]; intro pre.
  - apply steps_refl.
  - destruct x as [gx bx priox]. destruct y as [gy byy priy].
    destruct Hxy as [Hprio [Hg Hb]]. subst priy.
    eapply steps_append.
    + apply (steps_defeasible_exn_guard bt bb pre gx gy bx priox xs Hg).
    + eapply steps_append.
      * apply (steps_defeasible_exn_body bt bb pre gy bx byy priox xs Hb).
      * replace (pre ++ MkException gy byy priox :: xs)
          with ((pre ++ [MkException gy byy priox]) ++ xs)
          by (rewrite <- app_assoc; reflexivity).
        replace (pre ++ MkException gy byy priox :: ys)
          with ((pre ++ [MkException gy byy priox]) ++ ys)
          by (rewrite <- app_assoc; reflexivity).
        apply IH.
Qed.

Lemma Forall2_steps_to_steps_defeasible_exns :
  forall bt bb exns exns',
    Forall2 (fun e e' =>
               match e, e' with
               | MkException g b prio, MkException g' b' prio' =>
                   prio = prio' /\ steps g g' /\ steps b b'
               end) exns exns' ->
    steps (Defeasible bt bb exns) (Defeasible bt bb exns').
Proof.
  intros bt bb exns exns' HF.
  pose proof (steps_defeasible_exn_prefix bt bb [] exns exns' HF) as H.
  simpl in H. exact H.
Qed.

(* ================================================================== *)
(** ** Helper lemmas for par_implies_steps                            *)
(* ================================================================== *)

(** If each arg steps to an arg' and originals are values, then
    each arg' is a value.  Used in match_ctor_fire_p. *)
Lemma Forall2_steps_preserves_values :
  forall (args args' : list Term),
    Forall value args ->
    Forall2 steps args args' ->
    Forall value args'.
Proof.
  intros args args' Hval. revert args'.
  induction Hval as [| x xs Hvx Hvxs IH]; intros args' HF.
  - inversion HF; subst. constructor.
  - inversion HF; subst. constructor.
    + eapply steps_preserves_value; eassumption.
    + apply IH. assumption.
Qed.

(* ================================================================== *)
(** ** par_implies_steps : par ⊆ steps (Qed)                          *)
(* ================================================================== *)

(** Lift [Forall2 par] to [Forall2 steps] via pointwise
    [par_implies_steps]. *)

(** This is the core theorem: every parallel reduction decomposes
    into a chain of single steps. *)

Theorem par_implies_steps : forall t t', par t t' -> steps t t'
with par_branch_implies_steps :
  forall pat body body',
    par_branch (MkBranch pat body) (MkBranch pat body') ->
    steps body body'
with par_exception_implies_steps :
  forall g b prio g' b',
    par_exception (MkException g b prio) (MkException g' b' prio) ->
    steps g g' /\ steps b b'.
Proof.
  - intros t t' H. induction H; try (apply steps_refl).
    + (* par_pair *)
      eapply steps_append.
      * apply steps_pair_fst. exact IHpar1.
      * apply steps_pair_snd. exact IHpar2.
    + (* par_proj *) apply steps_proj. exact IHpar.
    + (* par_app_cong *)
      eapply steps_append.
      * apply steps_app_func. exact IHpar1.
      * apply steps_app_arg. exact IHpar2.
    + (* par_inductive *)
      apply Forall2_steps_to_steps_inductive.
      induction H as [| x y xs ys Hxy HF IH].
      * constructor.
      * constructor.
        -- apply par_implies_steps. exact Hxy.
        -- exact IH.
    + (* par_sanctions *) apply steps_sanctions. exact IHpar.
    + (* par_defeat *) apply steps_defeat. exact IHpar.
    + (* par_lift0 *) apply steps_lift0. exact IHpar.
    + (* par_derive1 *)
      eapply steps_append.
      * apply steps_derive1_time. exact IHpar1.
      * apply steps_derive1_wit. exact IHpar2.
    + (* par_lambda *)
      eapply steps_append.
      * apply steps_lambda_dom. exact IHpar1.
      * apply steps_lambda_body. exact IHpar2.
    + (* par_pi *)
      eapply steps_append.
      * apply steps_pi_dom. exact IHpar1.
      * apply steps_pi_cod. exact IHpar2.
    + (* par_sigma *)
      eapply steps_append.
      * apply steps_sigma_fst. exact IHpar1.
      * apply steps_sigma_snd. exact IHpar2.
    + (* par_annot_cong *)
      eapply steps_append.
      * apply steps_annot_e. exact IHpar1.
      * apply steps_annot_ty. exact IHpar2.
    + (* par_let_cong *)
      eapply steps_append.
      * apply steps_let_ty. exact IHpar1.
      * eapply steps_append.
        -- apply steps_let_val. exact IHpar2.
        -- apply steps_let_body. exact IHpar3.
    + (* par_match_cong *)
      eapply steps_append.
      * apply steps_match_scrutinee. exact IHpar1.
      * eapply steps_append.
        -- apply steps_match_ret. exact IHpar2.
        -- apply Forall2_steps_to_steps_match_branches.
           induction H1 as [| x y xs ys Hxy HF IH].
           ++ constructor.
           ++ destruct x as [patx bodyx]. destruct y as [paty bodyy].
              inversion Hxy; subst. constructor.
              ** split; [reflexivity |].
                 apply par_implies_steps. assumption.
              ** exact IH.
    + (* par_rec *)
      eapply steps_append.
      * apply steps_rec_ty. exact IHpar1.
      * apply steps_rec_body. exact IHpar2.
    + (* par_modal_at *)
      eapply steps_append.
      * apply steps_modal_at_time. exact IHpar1.
      * apply steps_modal_at_body. exact IHpar2.
    + (* par_modal_eventually *)
      eapply steps_append.
      * apply steps_modal_eventually_time. exact IHpar1.
      * apply steps_modal_eventually_body. exact IHpar2.
    + (* par_modal_always *)
      eapply steps_append.
      * apply steps_modal_always_from. exact IHpar1.
      * eapply steps_append.
        -- apply steps_modal_always_to. exact IHpar2.
        -- apply steps_modal_always_body. exact IHpar3.
    + (* par_modal_intro *) apply steps_modal_intro. exact IHpar.
    + (* par_modal_elim *)
      eapply steps_append.
      * apply steps_modal_elim_e. exact IHpar1.
      * apply steps_modal_elim_w. exact IHpar2.
    + (* par_defeasible_cong *)
      eapply steps_append.
      * apply steps_defeasible_ty. exact IHpar1.
      * eapply steps_append.
        -- apply steps_defeasible_body. exact IHpar2.
        -- apply Forall2_steps_to_steps_defeasible_exns.
           induction H1 as [| x y xs ys Hxy HF IH].
           ++ constructor.
           ++ destruct x as [gx bx priox]. destruct y as [gy byy priy].
              inversion Hxy; subst. constructor.
              ** split; [reflexivity |].
                 split; apply par_implies_steps; assumption.
              ** exact IH.
    + (* par_hole *) apply steps_hole. exact IHpar.
    + (* par_hole_fill *)
      eapply steps_append.
      * apply steps_hole_fill_filler. exact IHpar1.
      * apply steps_hole_fill_pc. exact IHpar2.
    + (* par_principle *)
      eapply steps_append.
      * apply steps_principle_v. exact IHpar1.
      * apply steps_principle_r. exact IHpar2.
    + (* par_unlock *)
      eapply steps_append.
      * apply steps_unlock_row. exact IHpar1.
      * apply steps_unlock_body. exact IHpar2.
    + (* par_beta: App (Lambda dom body) arg -> subst 0 arg' body'.
         Reduce: first reduce subterms to (Lambda dom' body') and arg',
         then fire beta to get subst 0 arg' body'. *)
      eapply steps_append.
      * apply steps_app_func. apply steps_lambda_dom. exact IHpar1.
      * eapply steps_append.
        -- apply steps_app_func. apply steps_lambda_body. exact IHpar2.
        -- eapply steps_append.
           ++ apply steps_app_arg. exact IHpar3.
           ++ eapply steps_trans.
              ** apply step_beta.
              ** apply steps_refl.
    + (* par_zeta: Let ty val body -> subst 0 val' body'. *)
      eapply steps_append.
      * apply steps_let_ty. exact IHpar1.
      * eapply steps_append.
        -- apply steps_let_val. exact IHpar2.
        -- eapply steps_append.
           ++ apply steps_let_body. exact IHpar3.
           ++ eapply steps_trans.
              ** apply step_zeta.
              ** apply steps_refl.
    + (* par_annot_fire: Annot e ty -> e'. *)
      eapply steps_append.
      * apply steps_annot_e. exact IHpar.
      * eapply steps_trans; [apply step_annot | apply steps_refl].
    + (* par_defeasible_empty_fire: Defeasible bt bb [] -> bb'. *)
      eapply steps_append.
      * apply steps_defeasible_body. exact IHpar.
      * eapply steps_trans; [apply step_defeasible_empty | apply steps_refl].
    + (* par_defeasible_peel_fire: Defeasible bt bb (e :: rest) ->
         Defeasible bt' bb' rest' *)
      (* Step: first reduce bt, bb, rest within the Defeasible(e :: rest),
         then peel. *)
      eapply steps_append.
      * apply steps_defeasible_ty. exact IHpar1.
      * eapply steps_append.
        -- apply steps_defeasible_body. exact IHpar2.
        -- eapply steps_trans.
           ++ apply step_defeasible_peel.
           ++ (* Now: steps (Defeasible bt' bb' rest) (Defeasible bt' bb' rest').
                 Use Forall2_steps_to_steps_defeasible_exns. *)
              apply Forall2_steps_to_steps_defeasible_exns.
              induction H1 as [| x y xs ys Hxy HF IH].
              ** constructor.
              ** destruct x as [gx bx priox]. destruct y as [gy byy priy].
                 inversion Hxy; subst. constructor.
                 --- split; [reflexivity |]. split; apply par_implies_steps; assumption.
                 --- exact IH.
    + (* par_match_wild_fire *)
      eapply steps_trans.
      * apply step_match_wild. exact H.
      * apply IHpar.
    + (* par_match_ctor_fire_p *)
      (* Step: first reduce args via congruence, reducing scr to
         InductiveIntro c args', then fire match_ctor. *)
      assert (HFsteps : Forall2 steps args args').
      { clear - H2 par_implies_steps.
        induction H2 as [| x y xs ys Hxy HFrest IH].
        - constructor.
        - constructor; [apply par_implies_steps; assumption | exact IH]. }
      assert (Hlen : List.length args' = List.length args).
      { apply Forall2_length in HFsteps. lia. }
      eapply steps_append.
      * apply steps_match_scrutinee.
        apply Forall2_steps_to_steps_inductive. exact HFsteps.
      * eapply steps_append.
        -- apply steps_match_branch with (pre := []).
           apply par_implies_steps. exact H3.
        -- eapply steps_trans.
           ++ apply step_match_ctor_fire with (c := c) (c' := c') (n := n);
                try assumption.
              ** (* Forall value args' *)
                 eapply Forall2_steps_preserves_values; eassumption.
              ** (* List.length args' = n *)
                 rewrite Hlen. assumption.
           ++ apply steps_refl.
    + (* par_match_ctor_skip_fire *)
      (* Fire step_match_ctor_skip first (requires value scr, branch
         head mismatch, and rest <> nil), then reduce subterms.
         The rest <> nil premise (H1) is discharged at step_match_ctor_skip
         and irrelevant to the downstream reduction chain; clear it
         before the Forall2 induction to keep IH premise-free. *)
      eapply steps_trans.
      * apply step_match_ctor_skip; assumption.
      * (* Now: steps (Match scr ret rest) (Match scr' ret' rest'). *)
        eapply steps_append.
        -- apply steps_match_scrutinee. apply par_implies_steps. exact H2.
        -- eapply steps_append.
           ++ apply steps_match_ret. apply par_implies_steps. exact H3.
           ++ apply Forall2_steps_to_steps_match_branches.
              clear H1.
              induction H4 as [| x y xs ys Hxy HF IH].
              ** constructor.
              ** destruct x as [patx bodyx]. destruct y as [paty bodyy].
                 inversion Hxy; subst. constructor.
                 --- split; [reflexivity |]. apply par_implies_steps. assumption.
                 --- exact IH.
  - (* par_branch_implies_steps *)
    intros pat body body' H. inversion H; subst.
    apply par_implies_steps. assumption.
  - (* par_exception_implies_steps *)
    intros g b prio g' b' H. inversion H; subst.
    split; apply par_implies_steps; assumption.
Qed.

(* ================================================================== *)
(** ** Explicit specifications of remaining obligations               *)
(* ================================================================== *)


(** These are [Prop]-level specifications, not Coq [Axiom]s.  They
    name the precise obligations for a future proof to discharge.
    None of the code below introduces a [Hypothesis] or [Axiom]; a
    caller citing [par_subst_spec] must bring their own proof. *)

(** [subst_args_preserves_ws]: substituting [n] closed constructor
    arguments into a body scoped by those [n] binders preserves the
    ambient scope [k].  This is the scoping invariant used by the
    multi-substitution bridge below. *)
Lemma subst_args_preserves_ws : forall args body k,
  well_scoped (k + List.length args) body ->
  Forall (fun t => well_scoped k t) args ->
  well_scoped k (subst_args args body).
Proof.
  induction args as [|a rest IH]; intros body k Hbody Hargs; simpl in *.
  - replace (k + 0) with k in Hbody by lia. exact Hbody.
  - inversion Hargs as [|? ? Ha Hrest]; subst.
    apply IH.
    + eapply subst_preserves_ws.
      * replace (k + S (List.length rest))
          with (S (k + List.length rest)) in Hbody by lia.
        exact Hbody.
      * eapply well_scoped_mono; [| exact Ha]. lia.
      * lia.
    + exact Hrest.
Qed.

(** [par_subst_spec]: par respects substitution.  Structural
    induction on [par t t'] with [shift_subst_commute_ws] at every
    binder case and [subst_subst_ws] at every redex case.

    This shallow form is not by itself enough for [subst_args]: a
    constructor branch body scoped by [n] pattern binders satisfies
    [well_scoped n body], not [well_scoped 1 body].  The at-depth
    form below is the exact frontier needed for constructor firing. *)
Definition par_subst_spec : Prop :=
  forall (t t' s s' : Term) (i : nat),
    well_scoped (S i) t ->
    par t t' ->
    par s s' ->
    par (subst i s t) (subst i s' t').

(** [par_subst_at_depth_spec]: par respects substitution at target
    [i] inside an ambient well-scoped depth [k].  The replacement
    terms are also scoped at [k] so the binder cases can shift them
    without leaving the ambient scope invariant. *)
Definition par_subst_at_depth_spec : Prop :=
  forall (t t' s s' : Term) (i k : nat),
    i < k ->
    well_scoped k t ->
    well_scoped k s ->
    well_scoped k s' ->
    par t t' ->
    par s s' ->
    par (subst i s t) (subst i s' t').

(** [par_subst_args_spec]: the multi-substitution case needed by
    [par_match_ctor_fire_p].  The body is scoped by exactly the
    constructor-argument binders, and both argument vectors are
    closed at ambient depth 0. *)
Definition par_subst_args_spec : Prop :=
  forall args args' body body',
    well_scoped (List.length args) body ->
    Forall (fun t => well_scoped 0 t) args ->
    Forall (fun t => well_scoped 0 t) args' ->
    Forall2 par args args' ->
    par body body' ->
    par (subst_args args body) (subst_args args' body').

(** The constructor-fire multi-substitution obligation reduces to the
    at-depth unary substitution theorem.  This closes the list/fold
    bookkeeping around [subst_args]; the remaining mathematical
    obligation is now precisely [par_subst_at_depth_spec]. *)
Theorem par_subst_at_depth_implies_par_subst_args :
  par_subst_at_depth_spec -> par_subst_args_spec.
Proof.
  unfold par_subst_at_depth_spec, par_subst_args_spec.
  intros Hsubst args args' body body' Hws Hargs Hargs' Hpars Hbody.
  revert body body' Hws Hargs Hargs' Hbody.
  induction Hpars as [|a a' rest rest' Ha _ IH];
    intros body body' Hws Hargs Hargs' Hbody; simpl in *.
  - exact Hbody.
  - inversion Hargs as [|? ? Hwa Hwrest]; subst.
    inversion Hargs' as [|? ? Hwa' Hwrest']; subst.
    apply IH.
    + eapply subst_preserves_ws.
      * exact Hws.
      * eapply well_scoped_mono; [| exact Hwa]. lia.
      * lia.
    + exact Hwrest.
    + exact Hwrest'.
    + eapply (Hsubst body body' a a' 0 (S (List.length rest))).
      * lia.
      * exact Hws.
      * eapply well_scoped_mono; [| exact Hwa]. lia.
      * eapply well_scoped_mono; [| exact Hwa']. lia.
      * exact Hbody.
      * exact Ha.
Qed.

(** [par_shift_spec]: par is closed under shift.  Structural
    induction on [par t t'] - each congruence case commutes par
    through shift, each redex case uses [shift_subst_commute_ws]
    from DeBruijn.v.  The well_scoped-guarded form in DeBruijn.v
    is what's needed (shift doesn't produce nested subst's without
    well_scoped invariants when interacting with par_beta's
    `subst 0 arg' body'` result).  Captured here as a Prop
    specification; closing it requires threading well_scoped
    through par. *)
Definition par_shift_spec : Prop :=
  forall t t' c d,
    well_scoped c t ->
    par t t' ->
    par (shift c d t) (shift c d t').

(** [par_implies_steps_spec]: par ⊆ steps.  Structural induction
    on [par t t']; each congruence case lifts steps of subterms,
    each redex case fires the head step then lifts subterm pars. *)
Definition par_implies_steps_spec : Prop :=
  forall (t t' : Term), par t t' -> steps t t'.

(** [par_diamond_spec]: the diamond property for par.  Follows from
    [par_subst_spec] by double induction on the two par
    derivations. *)
Definition par_diamond_spec : Prop :=
  forall (t u1 u2 : Term),
    par t u1 -> par t u2 ->
    exists v, par u1 v /\ par u2 v.

(** [par_star_diamond_spec]: diamond for par*.  Follows from
    [par_diamond_spec] by the strip lemma. *)
Definition par_star_diamond_spec : Prop :=
  forall (t u1 u2 : Term),
    par_star t u1 -> par_star t u2 ->
    exists v, par_star u1 v /\ par_star u2 v.

(** [confluence_spec] - matches [confluence_property] in Typing.v.
    Follows from [par_star_diamond_spec] +
    [par_implies_steps_spec] + [step_implies_par]. *)
Definition confluence_spec : Prop := confluence_property.

(** The parallel-reduction closure route needs one small bridge that is
    easy to lose in prose: once [par_star_diamond_spec] is proved, the
    single-step confluence property follows from the already-Qed
    embeddings [step_implies_par] and [par_implies_steps]. *)

Theorem par_implies_steps_spec_closed : par_implies_steps_spec.
Proof.
  exact par_implies_steps.
Qed.

Lemma steps_implies_par_star : forall t t',
  steps t t' -> par_star t t'.
Proof.
  intros t t' Hsteps.
  induction Hsteps as [t | t1 t2 t3 Hstep _ IH].
  - apply par_star_refl.
  - eapply par_star_step.
    + apply step_implies_par. exact Hstep.
    + exact IH.
Qed.

Lemma par_star_implies_steps : forall t t',
  par_star t t' -> steps t t'.
Proof.
  intros t t' Hstar.
  induction Hstar as [t | t1 t2 t3 Hpar _ IH].
  - apply steps_refl.
  - eapply steps_append.
    + apply par_implies_steps. exact Hpar.
    + exact IH.
Qed.

Theorem confluence_from_par_star_diamond :
  par_star_diamond_spec -> confluence_spec.
Proof.
  unfold par_star_diamond_spec, confluence_spec, confluence_property.
  intros Hdiamond t u1 u2 Htu1 Htu2.
  destruct (Hdiamond t u1 u2
              (steps_implies_par_star t u1 Htu1)
              (steps_implies_par_star t u2 Htu2))
    as [v [Hu1v Hu2v]].
  exists v. split; apply par_star_implies_steps; assumption.
Qed.
