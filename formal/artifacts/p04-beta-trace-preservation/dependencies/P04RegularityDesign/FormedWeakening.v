From Stdlib Require Import Lists.List Arith.Arith Lia.
From Lex Require Import Syntax DeBruijn Typing.
From P04Source Require Import TypeReduction FormedTyping.
Import ListNotations.
Module FormedStructural.
Import Formed.

(** This proof adapts the captured source's structural weakening recursion.
    It uses the corrected relation, including formed branch telescopes. *)
Lemma growing_decompose : forall xs k pre' B' post',
  shift_at_growing_cutoff k xs = pre' ++ B' :: post' ->
  exists pre B post,
    xs = pre ++ B :: post /\
    pre' = shift_at_growing_cutoff k pre /\
    B' = shift (k + List.length pre) 1 B.
Proof.
  induction xs as [|x xs IH]; intros k pre' B' post' Heq.
  - destruct pre'; discriminate.
  - destruct pre' as [|p pre'].
    + simpl in Heq. inversion Heq; subst.
      exists [], x, xs. simpl. rewrite Nat.add_0_r. auto.
    + simpl in Heq. inversion Heq; subst p.
      destruct (IH (S k) pre' B' post' H1)
        as [pre [B [post [Hxs [Hpre HB]]]]].
      exists (x :: pre), B, post. subst xs pre'. simpl.
      split. reflexivity. split. reflexivity.
      replace (k + S (List.length pre)) with (S k + List.length pre) by lia.
      exact HB.
Qed.

Lemma weakening_at_var : forall (k : nat) (ctx : Context) (i : nat) (T A : Term),
  ctx_lookup ctx i = Some T ->
  has_type (insert_at k A ctx) (shift k 1 (Var i)) (shift k 1 T).
Proof.
  intros k ctx i T A Hlook.
  simpl.
  destruct (Nat.leb_spec k i) as [Hki | Hik].
  - (* k <= i: shifted term is [Var (i + 1)] *)
    replace (i + 1) with (S i) by lia.
    apply T_Var.
    eapply insert_at_lookup_gt; [exact Hki | exact Hlook].
  - (* i < k: shifted term stays [Var i] *)
    apply T_Var.
    eapply insert_at_lookup_lt; [exact Hik | exact Hlook].
Qed.

(** Sort and time cases: all source terms are [TSort _] (closed), and
    their types are [type_level _] (closed).  Both are reduced
    directly by [simpl] on the shift (the shift [match] fans out on
    the term head).  Dispatch to the matching [has_type] constructor. *)

Lemma weakening_at_type : forall (k : nat) (ctx : Context) (A : Term)
                                 (l : Level) (n : nat),
  eval_level l = Some n ->
  has_type (insert_at k A ctx)
           (shift k 1 (TSort (SType l)))
           (shift k 1 (type_level (S n))).
Proof.
  intros. unfold type_level. simpl. apply T_Type. assumption.
Qed.

Lemma weakening_at_prop : forall (k : nat) (ctx : Context) (A : Term),
  has_type (insert_at k A ctx)
           (shift k 1 (TSort SLProp))
           (shift k 1 (type_level 1)).
Proof.
  intros. unfold type_level. simpl. apply T_Prop.
Qed.

Lemma weakening_at_rule : forall (k : nat) (ctx : Context) (A : Term)
                                 (l : Level) (n : nat),
  eval_level l = Some n ->
  has_type (insert_at k A ctx)
           (shift k 1 (TSort (SRule l)))
           (shift k 1 (type_level (S n))).
Proof.
  intros. unfold type_level. simpl. apply T_Rule. assumption.
Qed.

Lemma weakening_at_time0 : forall (k : nat) (ctx : Context) (A : Term),
  has_type (insert_at k A ctx)
           (shift k 1 (TSort STime0))
           (shift k 1 (type_level 0)).
Proof.
  intros. unfold type_level. simpl. apply T_Time0.
Qed.

Lemma weakening_at_time1 : forall (k : nat) (ctx : Context) (A : Term),
  has_type (insert_at k A ctx)
           (shift k 1 (TSort STime1))
           (shift k 1 (type_level 0)).
Proof.
  intros. unfold type_level. simpl. apply T_Time1.
Qed.

(** T_Pi / T_Lambda / T_Let binder cases: shift distributes over
    [Pi]/[Lambda]/[Let] with the body's cutoff incremented to [S k].
    The inner-context premise was typed under [ctx_extend ctx A];
    weakening-at-depth-[S k] inside equals extending the outer
    weakened context with [shift k 1 A], by
    [insert_at_ctx_extend_commute].  The case lemmas here take the
    IH-shaped premises directly. *)

Lemma weakening_at_pi : forall (k : nat) (ctx : Context)
                              (A' A B : Term) (eff : option EffectRow)
                              (i j : nat),
  has_type (insert_at k A' ctx) (shift k 1 A) (type_level i) ->
  has_type (ctx_extend (insert_at k A' ctx) (shift k 1 A))
           (shift (S k) 1 B) (type_level j) ->
  has_type (insert_at k A' ctx)
           (shift k 1 (Pi A eff B))
           (shift k 1 (type_level (Nat.max i j))).
Proof.
  intros. unfold type_level. simpl.
  eapply T_Pi; eassumption.
Qed.

Lemma weakening_at_lambda : forall (k : nat) (ctx : Context)
                                   (A' A B body : Term)
                                   (eff : option EffectRow) (i : nat),
  has_type (insert_at k A' ctx) (shift k 1 A) (type_level i) ->
  has_type (ctx_extend (insert_at k A' ctx) (shift k 1 A))
           (shift (S k) 1 body) (shift (S k) 1 B) ->
  has_type (insert_at k A' ctx)
           (shift k 1 (Lambda A body))
           (shift k 1 (Pi A eff B)).
Proof.
  intros. simpl.
  eapply T_Lambda; eassumption.
Qed.

Lemma weakening_at_annot : forall (k : nat) (ctx : Context)
                                  (A' e T : Term) (i : nat),
  has_type (insert_at k A' ctx) (shift k 1 e) (shift k 1 T) ->
  has_type (insert_at k A' ctx) (shift k 1 T) (type_level i) ->
  has_type (insert_at k A' ctx)
           (shift k 1 (Annot e T)) (shift k 1 T).
Proof.
  intros. simpl.
  eapply T_Annot; eassumption.
Qed.

(** T_Defeasible case: [shift k 1] pushes through [Defeasible] by
    mapping [shift_exception k 1] over the exception list; the
    projections [exn_guard] / [exn_body] commute with this
    pointwise, so the [Forall] premises for guards and bodies are
    preserved in the natural form.  The proposition type ([prop] =
    [TSort SLProp]) is closed, hence shift-invariant. *)
Lemma weakening_at_defeasible : forall (k : nat) (ctx : Context)
                                       (A' base_ty base_body : Term)
                                       (exns : list Exception)
                                       (i : nat),
  has_type (insert_at k A' ctx) (shift k 1 base_ty) (type_level i) ->
  has_type (insert_at k A' ctx) (shift k 1 base_body) (shift k 1 base_ty) ->
  Forall (fun e => has_type (insert_at k A' ctx) (exn_guard e) prop)
         (map (shift_exception k 1) exns) ->
  Forall (fun e => has_type (insert_at k A' ctx) (exn_body e) (shift k 1 base_ty))
         (map (shift_exception k 1) exns) ->
  has_type (insert_at k A' ctx)
           (shift k 1 (Defeasible base_ty base_body exns))
           (shift k 1 base_ty).
Proof.
  intros. simpl.
  eapply T_Defeasible; eassumption.
Qed.

Lemma weakening_at_match :
  forall (k : nat) (ctx : Context)
         (A' scrutinee return_ty scrut_ty : Term)
         (branches : list Branch) (i : nat)
         (binder_tys_list : list (list Term)),
    Forall (fun bt =>
      forall pre B post, bt = pre ++ B :: post ->
        exists j, has_type (fold_left ctx_extend pre (insert_at k A' ctx))
          B (type_level j))
      (map (shift_at_growing_cutoff k) binder_tys_list) ->
    has_type (insert_at k A' ctx) (shift k 1 scrutinee) (shift k 1 scrut_ty) ->
    has_type (insert_at k A' ctx) (shift k 1 return_ty) (type_level i) ->
    branches <> nil ->
    List.length branches = List.length binder_tys_list ->
    Forall2 (fun br binder_tys =>
               List.length binder_tys = pattern_arity (branch_pat br))
            branches binder_tys_list ->
    Forall2 (fun br binder_tys =>
               has_type
                 (ctx_extend_pattern (insert_at k A' ctx) (branch_pat br) binder_tys)
                 (branch_body br)
                 (shift 0 (pattern_arity (branch_pat br)) (shift k 1 return_ty)))
            (map (shift_branch k 1) branches)
            (map (shift_at_growing_cutoff k) binder_tys_list) ->
    has_type (insert_at k A' ctx)
             (shift k 1 (Match scrutinee return_ty branches))
             (shift k 1 return_ty).
Proof.
  intros k ctx A' scr ret scrut_ty brs i btl Hform Hscr Hret Hne Hlen Harity Hbody.
  simpl.
  eapply T_Match with
    (scrut_ty := shift k 1 scrut_ty)
    (i := i)
    (binder_tys_list := map (shift_at_growing_cutoff k) btl).
  - exact Hform.
  - exact Hscr.
  - exact Hret.
  - intros Hcontra. apply map_eq_nil in Hcontra. contradiction.
  - rewrite !length_map. exact Hlen.
  - (* Forall2 of arities for the shifted branches *)
    clear Hform Hscr Hret Hne Hlen Hbody.
    revert btl Harity. induction brs as [| br rest IH]; intros btl Harity.
    + inversion Harity. constructor.
    + inversion Harity as [| br0 bt0 rest_brs rest_btl Hahd Hatl Hbrs Hbtl];
        subst.
      simpl. constructor.
      * rewrite shift_at_growing_cutoff_length.
        rewrite branch_pat_shift_branch. exact Hahd.
      * apply IH. exact Hatl.
  - (* Forall2 of body typings - already in shifted form *)
    exact Hbody.
Qed.

Lemma weakening_at_app :
  shift_subst_commute_above_spec ->
  forall (k : nat) (ctx : Context)
         (A' f a A B : Term) (eff : option EffectRow),
    has_type (insert_at k A' ctx) (shift k 1 f)
             (shift k 1 (Pi A eff B)) ->
    has_type (insert_at k A' ctx) (shift k 1 a) (shift k 1 A) ->
    has_type (insert_at k A' ctx)
             (shift k 1 (App f a))
             (shift k 1 (subst 0 a B)).
Proof.
  intros Hcomm k ctx A' f a A B eff Hf Ha.
  simpl.
  rewrite Hcomm by lia.
  simpl in Hf.
  eapply T_App; eassumption.
Qed.

(** T_Let case: analogous to T_App, with the bound-type annotation
    [A] typed at [type_level i] in the outer context, the value [v]
    inhabiting [A], and the body [body] typed in [ctx_extend ctx A]
    with cutoff [S k] after weakening-at-[k]. *)
Lemma weakening_at_let :
  shift_subst_commute_above_spec ->
  forall (k : nat) (ctx : Context)
         (A' A v B body : Term) (i : nat),
    has_type (insert_at k A' ctx) (shift k 1 A) (type_level i) ->
    has_type (insert_at k A' ctx) (shift k 1 v) (shift k 1 A) ->
    has_type (ctx_extend (insert_at k A' ctx) (shift k 1 A))
             (shift (S k) 1 body) (shift (S k) 1 B) ->
    has_type (insert_at k A' ctx)
             (shift k 1 (Let A v body))
             (shift k 1 (subst 0 v B)).
Proof.
  intros Hcomm k ctx A' A v B body i HA Hv Hbody.
  simpl.
  rewrite Hcomm by lia.
  eapply T_Let; eassumption.
Qed.

Fixpoint weakening_at_fix
  (k : nat) (ctx : Context) (A' : Term)
  (t T : Term) (Hty : has_type ctx t T)
  (Hk : k <= List.length ctx)
  {struct Hty} :
  has_type (insert_at k A' ctx) (shift k 1 t) (shift k 1 T).
Proof.
  destruct Hty as
    [ ctx' i T0 Hlook                                                      (* T_Var *)
    | ctx' l n Hlev                                                       (* T_Type *)
    | ctx'                                                                (* T_Prop *)
    | ctx' l n Hlev                                                       (* T_Rule *)
    | ctx'                                                                (* T_Time0 *)
    | ctx'                                                                (* T_Time1 *)
    | ctx' A B eff i j HA HB                                              (* T_Pi *)
    | ctx' A B body eff i HA Hbody                                        (* T_Lambda *)
    | ctx' f a A B eff Hf Ha                                              (* T_App *)
    | ctx' e T0 i He HT                                                   (* T_Annot *)
    | ctx' A v B body i HA Hv Hbody                                       (* T_Let *)
    | ctx' base_ty base_body exns i Hbt Hbb Hguards Hbodies               (* T_Defeasible *)
    | ctx' scr ret scrut_ty brs i btl Hform Hscr Hret Hbrs_ne Hlen Harity Htyping (* T_Match *)
    | ctx' t0 A B i Ht Hconv HB                                                (* T_Conv *)
    ].
  - (* T_Var *) apply weakening_at_var. assumption.
  - (* T_Type *) apply weakening_at_type. assumption.
  - (* T_Prop *) apply weakening_at_prop.
  - (* T_Rule *) apply weakening_at_rule. assumption.
  - (* T_Time0 *) apply weakening_at_time0.
  - (* T_Time1 *) apply weakening_at_time1.
  - (* T_Pi *)
    apply weakening_at_pi with (i := i) (j := j).
    + exact (weakening_at_fix k ctx' A' _ _ HA Hk).
    + assert (Hk2 : S k <= List.length (ctx_extend ctx' A))
        by (rewrite ctx_extend_length; lia).
      rewrite <- insert_at_ctx_extend_commute.
      exact (weakening_at_fix
               (S k) (ctx_extend ctx' A) A' _ _ HB Hk2).
  - (* T_Lambda *)
    apply weakening_at_lambda with (i := i).
    + exact (weakening_at_fix k ctx' A' _ _ HA Hk).
    + assert (Hk2 : S k <= List.length (ctx_extend ctx' A))
        by (rewrite ctx_extend_length; lia).
      rewrite <- insert_at_ctx_extend_commute.
      exact (weakening_at_fix
               (S k) (ctx_extend ctx' A) A' _ _ Hbody Hk2).
  - (* T_App *)
    eapply weakening_at_app.
    + exact shift_subst_commute_above_holds.
    + exact (weakening_at_fix k ctx' A' _ _ Hf Hk).
    + exact (weakening_at_fix k ctx' A' _ _ Ha Hk).
  - (* T_Annot *)
    eapply weakening_at_annot.
    + exact (weakening_at_fix k ctx' A' _ _ He Hk).
    + assert (Hred : shift k 1 (type_level i) = type_level i)
        by (unfold type_level; simpl; reflexivity).
      rewrite <- Hred.
      exact (weakening_at_fix k ctx' A' _ _ HT Hk).
  - (* T_Let *)
    eapply weakening_at_let with (i := i).
    + exact shift_subst_commute_above_holds.
    + exact (weakening_at_fix k ctx' A' _ _ HA Hk).
    + exact (weakening_at_fix k ctx' A' _ _ Hv Hk).
    + assert (Hk2 : S k <= List.length (ctx_extend ctx' A))
        by (rewrite ctx_extend_length; lia).
      rewrite <- insert_at_ctx_extend_commute.
      exact (weakening_at_fix
               (S k) (ctx_extend ctx' A) A' _ _ Hbody Hk2).
  - (* T_Defeasible - inner fixes on Hguards / Hbodies *)
    apply weakening_at_defeasible with (i := i).
    + exact (weakening_at_fix k ctx' A' _ _ Hbt Hk).
    + exact (weakening_at_fix k ctx' A' _ _ Hbb Hk).
    + (* Weakened Forall over exception guards *)
      refine ((fix inner_g
                (exns' : list Exception)
                (Hg : Forall (fun e => has_type ctx' (exn_guard e) prop) exns')
                {struct Hg} :
                Forall (fun e => has_type (insert_at k A' ctx') (exn_guard e) prop)
                       (map (shift_exception k 1) exns') := _) exns Hguards).
      destruct Hg as [|exn exns'' Hg_hd Hg_tl].
      * constructor.
      * simpl. constructor.
        -- destruct exn as [g b p]. simpl in Hg_hd |- *.
           pose proof (weakening_at_fix k ctx' A' _ _ Hg_hd Hk) as Hw.
           replace (shift k 1 prop) with prop in Hw
             by (unfold prop; simpl; reflexivity).
           exact Hw.
        -- exact (inner_g exns'' Hg_tl).
    + (* Weakened Forall over exception bodies *)
      refine ((fix inner_b
                (exns' : list Exception)
                (Hb : Forall (fun e => has_type ctx' (exn_body e) base_ty) exns')
                {struct Hb} :
                Forall (fun e => has_type (insert_at k A' ctx') (exn_body e) (shift k 1 base_ty))
                       (map (shift_exception k 1) exns') := _) exns Hbodies).
      destruct Hb as [|exn exns'' Hb_hd Hb_tl].
      * constructor.
      * simpl. constructor.
        -- destruct exn as [g b p]. simpl in Hb_hd |- *.
           exact (weakening_at_fix k ctx' A' _ _ Hb_hd Hk).
        -- exact (inner_b exns'' Hb_tl).
  - (* T_Match - Qed-discharged via [weakening_at_match] +
       parallel inner fix on Harity / Htyping. *)
    apply weakening_at_match with
      (i := i) (scrut_ty := scrut_ty)
      (binder_tys_list := btl).
    + refine ((fix inner_f (btl0 : list (list Term))
        (HF : Forall (fun bt =>
          forall pre B post, bt = pre ++ B :: post ->
            exists j, has_type (fold_left ctx_extend pre ctx') B (type_level j))
          btl0) {struct HF} :
        Forall (fun bt =>
          forall pre B post, bt = pre ++ B :: post ->
            exists j, has_type
              (fold_left ctx_extend pre (insert_at k A' ctx')) B (type_level j))
          (map (shift_at_growing_cutoff k) btl0) := _) btl Hform).
      destruct HF as [|bt btl0 Hhead Htail].
      * constructor.
      * simpl. constructor.
        -- intros pre' B' post' Heq.
           destruct (growing_decompose bt k pre' B' post' Heq)
             as [pre [B [post [Hbt [Hpre HB']]]]].
           subst pre' B'.
           destruct (Hhead pre B post Hbt) as [j Htyped].
           exists j.
           rewrite <- insert_at_fold_left_ctx_extend_commute.
           exact (weakening_at_fix (k + List.length pre)
             (fold_left ctx_extend pre ctx') A' _ _ Htyped
             (ltac:(rewrite fold_left_ctx_extend_length; lia))).
        -- exact (inner_f btl0 Htail).
    + exact (weakening_at_fix k ctx' A' _ _ Hscr Hk).
    + (* return_ty : type_level i; type_level i is closed so shift is a no-op. *)
      assert (Hred : shift k 1 (type_level i) = type_level i)
        by (unfold type_level; simpl; reflexivity).
      rewrite <- Hred.
      exact (weakening_at_fix k ctx' A' _ _ Hret Hk).
    + exact Hbrs_ne.
    + exact Hlen.
    + exact Harity.
    + (* Forall2 over body typings - inner fix in lockstep on Harity,
         pat-case-splitting on each branch to lift IH at depth k+arity
         and apply [insert_at_ctx_extend_pattern_commute] to align
         contexts. *)
      clear Hscr Hret Hbrs_ne Hlen.
      refine ((fix inner_m
                (brs0 : list Branch)
                (btl0 : list (list Term))
                (Harity0 :
                   Forall2 (fun br bt =>
                     List.length bt = pattern_arity (branch_pat br)) brs0 btl0)
                (Htyping0 :
                   Forall2 (fun br bt =>
                     has_type
                       (ctx_extend_pattern ctx' (branch_pat br) bt)
                       (branch_body br)
                       (shift 0 (pattern_arity (branch_pat br)) ret)) brs0 btl0)
                {struct Htyping0} :
                Forall2 (fun br bt =>
                  has_type
                    (ctx_extend_pattern (insert_at k A' ctx') (branch_pat br) bt)
                    (branch_body br)
                    (shift 0 (pattern_arity (branch_pat br)) (shift k 1 ret)))
                  (map (shift_branch k 1) brs0)
                  (map (shift_at_growing_cutoff k) btl0)
                := _) brs btl Harity Htyping).
      destruct Htyping0 as [| br bt rest_brs rest_btl Hthd Httl].
      * inversion Harity0. constructor.
      * (* Forall2_cons inversion on Harity0: the relation must hold at
           the head and recursively on the tail. *)
        assert (Hahd : List.length bt = pattern_arity (branch_pat br))
          by (inversion Harity0; assumption).
        assert (Hatl : Forall2 (fun br0 bt0 =>
                         List.length bt0 = pattern_arity (branch_pat br0))
                       rest_brs rest_btl)
          by (inversion Harity0; assumption).
        (* Get body well-scoped at depth k+arity of the body's context.
           Hahd : length bt = pattern_arity (branch_pat br); compute. *)
        assert (Hk_arity : k + pattern_arity (branch_pat br)
                            <= List.length (ctx_extend_pattern ctx' (branch_pat br) bt)).
        { destruct br as [pat body]. simpl in *.
          destruct pat as [name n |]; simpl in *.
          - (* PCtor n *) unfold ctx_extend_pattern.
            rewrite fold_left_ctx_extend_length. rewrite Hahd. simpl. lia.
          - (* PWild *) lia. }
        pose proof (weakening_at_fix
                       (k + pattern_arity (branch_pat br))
                       (ctx_extend_pattern ctx' (branch_pat br) bt)
                       A' _ _ Hthd Hk_arity) as Hw.
        rewrite shift_shift_swap_0_arity in Hw.
        rewrite (insert_at_ctx_extend_pattern_commute
                   k (pattern_arity (branch_pat br)) A' ctx'
                   (branch_pat br) bt Hahd eq_refl) in Hw.
        change (map (shift_branch k 1) (br :: rest_brs))
          with (shift_branch k 1 br :: map (shift_branch k 1) rest_brs).
        change (map (shift_at_growing_cutoff k) (bt :: rest_btl))
          with (shift_at_growing_cutoff k bt :: map (shift_at_growing_cutoff k) rest_btl).
        constructor.
        -- rewrite branch_pat_shift_branch.
           rewrite branch_body_shift_branch.
           exact Hw.
        -- exact (inner_m rest_brs rest_btl Hatl Httl).
  - (* T_Conv *)
    eapply T_Conv with (i := i).
    + exact (weakening_at_fix k ctx' A' _ _ Ht Hk).
    + apply Conversion.convertible_shift. exact Hconv.
    + exact (weakening_at_fix k ctx' A' _ _ HB Hk).
Qed.


Theorem weakening : forall ctx t T A,
  has_type ctx t T ->
  has_type (ctx_extend ctx A) (shift 0 1 t) (shift 0 1 T).
Proof.
  intros ctx t T A H.
  rewrite <- insert_at_0.
  exact (weakening_at_fix 0 ctx A t T H (Nat.le_0_l _)).
Qed.

Print Assumptions weakening_at_fix.
Print Assumptions weakening.

Theorem lookup_formation : forall ctx,
  wf_context ctx -> forall index T,
  ctx_lookup ctx index = Some T ->
  exists i, has_type ctx T (type_level i).
Proof.
  intros ctx Hwf. induction Hwf as [|ctx A i Hwf IH HA];
    intros index T Hlookup.
  - destruct index; discriminate.
  - destruct index as [|index].
    + simpl in Hlookup. inversion Hlookup; subst T.
      exists i. exact (weakening ctx A (type_level i) A HA).
    + unfold ctx_extend in Hlookup. simpl in Hlookup.
      rewrite ctx_lookup_shift_ctx in Hlookup.
      destruct (ctx_lookup ctx index) as [B|] eqn:HB; try discriminate.
      inversion Hlookup; subst T.
      destruct (IH index B HB) as [j Hj].
      exists j. exact (weakening ctx B (type_level j) A Hj).
Qed.

Lemma pi_formation : forall ctx t T,
  has_type ctx t T -> forall A effects B,
  t = Pi A effects B -> exists i j,
    has_type ctx A (type_level i) /\
    has_type (ctx_extend ctx A) B (type_level j).
Proof.
  intros ctx t T H. induction H; intros A0 effects B0 Heq;
    inversion Heq; subst.
  - exists i, j. auto.
  - eapply IHhas_type1. reflexivity.
Qed.

Lemma formed_telescope_context : forall binder_tys ctx,
  wf_context ctx ->
  (forall pre A post, binder_tys = pre ++ A :: post ->
    exists j, has_type (fold_left ctx_extend pre ctx) A (type_level j)) ->
  wf_context (fold_left ctx_extend binder_tys ctx).
Proof.
  induction binder_tys as [|A rest IH]; intros ctx Hwf Hform; simpl.
  - exact Hwf.
  - apply IH.
    + destruct (Hform [] A rest eq_refl) as [j HA].
      eapply wf_extend. exact Hwf. exact HA.
    + intros pre B post Hrest.
      exact (Hform (A :: pre) B post (f_equal (cons A) Hrest)).
Qed.

Print Assumptions lookup_formation.
Print Assumptions pi_formation.
Print Assumptions formed_telescope_context.
End FormedStructural.
