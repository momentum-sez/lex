From Stdlib Require Import Lists.List Arith.Arith Lia.
From Lex Require Import Syntax DeBruijn Typing.
From P04ArgsSubstitution Require Import ArgsSubstitution.
From P04Source Require Import TypeReduction FormedTyping.
From P04RegularityDesign Require Import FormedWeakening.
Import ListNotations.
Module FormedSubstitution.
Import Formed FormedStructural.

(** A variable substitution relates the stored types in two contexts.
    Its condition concerns variables only, not arbitrary derivations. *)
Definition variable_substitution k u (ctx target : Context) :=
  forall index T, ctx_lookup ctx index = Some T ->
    has_type target (subst k u (Var index)) (subst k u T).

Lemma variable_substitution_extend : forall k u ctx target A,
  variable_substitution k u ctx target ->
  variable_substitution (S k) (shift 0 1 u)
    (ctx_extend ctx A) (ctx_extend target (subst k u A)).
Proof.
  intros k u ctx target A H index T Hlookup.
  destruct index as [|index].
  - simpl in Hlookup. inversion Hlookup; subst T.
    change (has_type (ctx_extend target (subst k u A)) (Var 0)
      (subst (S k) (shift 0 1 u) (shift 0 1 A))).
    replace (S k) with (k+1) by lia.
    rewrite <- shift_subst_below by lia.
    simpl. apply T_Var. reflexivity.
  - unfold ctx_extend in Hlookup. simpl in Hlookup.
    rewrite ctx_lookup_shift_ctx in Hlookup.
    destruct (ctx_lookup ctx index) as [B|] eqn:HB; try discriminate.
    inversion Hlookup; subst T.
    replace (Var (S index)) with (shift 0 1 (Var index))
      by (simpl; f_equal; lia).
    replace (S k) with (k+1) by lia.
    rewrite <- !shift_subst_below by lia.
    apply weakening. apply H. exact HB.
Qed.

Fixpoint subst_telescope k u (types : list Term) :=
  match types with
  | [] => []
  | A::rest => subst k u A :: subst_telescope (S k) (shift 0 1 u) rest
  end.

Lemma subst_telescope_length : forall types k u,
  List.length (subst_telescope k u types) = List.length types.
Proof. induction types; intros; simpl; auto. Qed.

Lemma variable_substitution_telescope : forall types k u ctx target,
  variable_substitution k u ctx target ->
  variable_substitution (k+List.length types) (shift 0 (List.length types) u)
    (fold_left ctx_extend types ctx)
    (fold_left ctx_extend (subst_telescope k u types) target).
Proof.
  induction types as [|A rest IH]; intros k u ctx target H; simpl.
  - rewrite Nat.add_0_r, shift_zero. exact H.
  - pose proof (IH (S k) (shift 0 1 u) (ctx_extend ctx A)
      (ctx_extend target (subst k u A))
      (variable_substitution_extend k u ctx target A H)) as HR.
    rewrite shift_shift in HR.
    replace (S k + List.length rest) with (k + S (List.length rest)) in HR by lia.
    exact HR.
Qed.

Lemma subst_telescope_decompose : forall types k u pre' A' post',
  subst_telescope k u types = pre' ++ A' :: post' ->
  exists pre A post,
    types = pre ++ A :: post /\
    pre' = subst_telescope k u pre /\
    A' = subst (k+List.length pre) (shift 0 (List.length pre) u) A.
Proof.
  induction types as [|A rest IH]; intros k u pre' A' post' Heq.
  - destruct pre'; discriminate.
  - destruct pre' as [|p pre'].
    + simpl in Heq. inversion Heq; subst.
      exists [], A, rest. simpl. rewrite Nat.add_0_r, shift_zero. auto.
    + simpl in Heq. inversion Heq; subst p.
      destruct (IH (S k) (shift 0 1 u) pre' A' post' H1)
        as [pre [B [post [Hrest [Hpre HB]]]]].
      exists (A::pre), B, post. subst rest pre'. simpl.
      split. reflexivity. split. reflexivity.
      rewrite shift_shift in HB.
      replace (S k + List.length pre) with (k + S (List.length pre)) in HB by lia.
      exact HB.
Qed.

Lemma branch_pat_subst : forall br k u,
  branch_pat (subst_branch k u br) = branch_pat br.
Proof. intros [pat body]; reflexivity. Qed.

Lemma branch_body_subst : forall br k u,
  branch_body (subst_branch k u br) =
  subst (k + pattern_arity (branch_pat br))
    (shift 0 (pattern_arity (branch_pat br)) u) (branch_body br).
Proof. intros [pat body]; reflexivity. Qed.

Lemma variable_substitution_pattern : forall k u ctx target pat types,
  List.length types = pattern_arity pat ->
  variable_substitution k u ctx target ->
  variable_substitution (k + pattern_arity pat) (shift 0 (pattern_arity pat) u)
    (ctx_extend_pattern ctx pat types)
    (ctx_extend_pattern target pat (subst_telescope k u types)).
Proof.
  intros k u ctx target pat types Hlen Hrel. destruct pat; simpl in *.
  - unfold ctx_extend_pattern. rewrite <- Hlen.
    apply variable_substitution_telescope. exact Hrel.
  - rewrite Nat.add_0_r, shift_zero. exact Hrel.
Qed.

Fixpoint typed_substitution
  (ctx : Context) (t T : Term) (Hty : has_type ctx t T)
  (k : nat) (u : Term) (target : Context)
  (Hrel : variable_substitution k u ctx target)
  {struct Hty} : has_type target (subst k u t) (subst k u T).
Proof.
  destruct Hty as
    [ ctx' index T0 Hlookup
    | ctx' l n Hlevel
    | ctx'
    | ctx' l n Hlevel
    | ctx'
    | ctx'
    | ctx' A B eff i j HA HB
    | ctx' A B body eff i HA Hbody
    | ctx' f a A B eff Hf Ha
    | ctx' e T0 i He HT
    | ctx' A v B body i HA Hv Hbody
    | ctx' base_ty base_body exns i Hbt Hbb Hguards Hbodies
    | ctx' scr ret scrut_ty brs i btl Hform Hscr Hret Hne Hlen Harity Htyping
    | ctx' t0 A B i Ht Hconv HB ].
  - apply Hrel. exact Hlookup.
  - apply T_Type. exact Hlevel.
  - apply T_Prop.
  - apply T_Rule. exact Hlevel.
  - apply T_Time0.
  - apply T_Time1.
  - simpl. eapply T_Pi with (i:=i) (j:=j).
    + exact (typed_substitution _ _ _ HA k u target Hrel).
    + exact (typed_substitution _ _ _ HB (S k) (shift 0 1 u) _
        (variable_substitution_extend k u ctx' target A Hrel)).
  - simpl. eapply T_Lambda with (i:=i).
    + exact (typed_substitution _ _ _ HA k u target Hrel).
    + exact (typed_substitution _ _ _ Hbody (S k) (shift 0 1 u) _
        (variable_substitution_extend k u ctx' target A Hrel)).
  - rewrite subst_beta_commute. simpl. eapply T_App.
    + exact (typed_substitution _ _ _ Hf k u target Hrel).
    + exact (typed_substitution _ _ _ Ha k u target Hrel).
  - simpl. eapply T_Annot with (i:=i).
    + exact (typed_substitution _ _ _ He k u target Hrel).
    + exact (typed_substitution _ _ _ HT k u target Hrel).
  - rewrite subst_beta_commute. simpl. eapply T_Let with (i:=i).
    + exact (typed_substitution _ _ _ HA k u target Hrel).
    + exact (typed_substitution _ _ _ Hv k u target Hrel).
    + exact (typed_substitution _ _ _ Hbody (S k) (shift 0 1 u) _
        (variable_substitution_extend k u ctx' target A Hrel)).
  - simpl. eapply T_Defeasible with (i:=i).
    + exact (typed_substitution _ _ _ Hbt k u target Hrel).
    + exact (typed_substitution _ _ _ Hbb k u target Hrel).
    + refine ((fix inner_g (xs : list Exception)
        (H : Forall (fun e => has_type ctx' (exn_guard e) prop) xs)
        {struct H} :
        Forall (fun e => has_type target (exn_guard e) prop)
          (map (subst_exception k u) xs) := _) exns Hguards).
      destruct H as [|[guard body priority] xs Hhead Htail].
      * constructor.
      * constructor.
        -- exact (typed_substitution _ _ _ Hhead k u target Hrel).
        -- exact (inner_g xs Htail).
    + refine ((fix inner_b (xs : list Exception)
        (H : Forall (fun e => has_type ctx' (exn_body e) base_ty) xs)
        {struct H} :
        Forall (fun e => has_type target (exn_body e) (subst k u base_ty))
          (map (subst_exception k u) xs) := _) exns Hbodies).
      destruct H as [|[guard body priority] xs Hhead Htail].
      * constructor.
      * constructor.
        -- exact (typed_substitution _ _ _ Hhead k u target Hrel).
        -- exact (inner_b xs Htail).
  - simpl. eapply T_Match with (i:=i)
      (scrut_ty:=subst k u scrut_ty)
      (binder_tys_list:=map (subst_telescope k u) btl).
    + refine ((fix inner_f (btl0 : list (list Term))
        (HF : Forall (fun bt =>
          forall pre A post, bt = pre ++ A :: post ->
            exists j, has_type (fold_left ctx_extend pre ctx') A (type_level j))
          btl0) {struct HF} :
        Forall (fun bt =>
          forall pre A post, bt = pre ++ A :: post ->
            exists j, has_type (fold_left ctx_extend pre target) A (type_level j))
          (map (subst_telescope k u) btl0) := _) btl Hform).
      destruct HF as [|bt btl0 Hhead Htail].
      * constructor.
      * constructor.
        -- intros pre' A' post' Heq.
           destruct (subst_telescope_decompose bt k u pre' A' post' Heq)
             as [pre [A [post [Hbt [Hpre HA']]]]].
           subst pre' A'.
           destruct (Hhead pre A post Hbt) as [j Htyped].
           exists j.
           exact (typed_substitution _ _ _ Htyped
             (k + List.length pre) (shift 0 (List.length pre) u) _
             (variable_substitution_telescope pre k u ctx' target Hrel)).
        -- exact (inner_f btl0 Htail).
    + exact (typed_substitution _ _ _ Hscr k u target Hrel).
    + exact (typed_substitution _ _ _ Hret k u target Hrel).
    + intro Heq. apply map_eq_nil in Heq. contradiction.
    + rewrite !length_map. exact Hlen.
    + clear Hform Hscr Hret Htyping Hne Hlen.
      induction Harity as [|br bt brs bts Hhead Htail IH]; simpl; constructor.
      * rewrite subst_telescope_length, branch_pat_subst. exact Hhead.
      * exact IH.
    + refine ((fix inner_m (brs0 : list Branch) (btl0 : list (list Term))
        (HA : Forall2 (fun br bt =>
          List.length bt = pattern_arity (branch_pat br)) brs0 btl0)
        (HT : Forall2 (fun br bt =>
          has_type (ctx_extend_pattern ctx' (branch_pat br) bt)
            (branch_body br)
            (shift 0 (pattern_arity (branch_pat br)) ret)) brs0 btl0)
        {struct HT} :
        Forall2 (fun br bt =>
          has_type (ctx_extend_pattern target (branch_pat br) bt)
            (branch_body br)
            (shift 0 (pattern_arity (branch_pat br)) (subst k u ret)))
          (map (subst_branch k u) brs0) (map (subst_telescope k u) btl0)
        := _) brs btl Harity Htyping).
      destruct HT as [|br bt rest_brs rest_btl Hhead Htail].
      * inversion HA. constructor.
      * assert (Harity_head : List.length bt = pattern_arity (branch_pat br))
          by (inversion HA; assumption).
        assert (Harity_tail : Forall2 (fun br bt =>
          List.length bt = pattern_arity (branch_pat br)) rest_brs rest_btl)
          by (inversion HA; assumption).
        pose proof (typed_substitution _ _ _ Hhead
          (k + pattern_arity (branch_pat br))
          (shift 0 (pattern_arity (branch_pat br)) u) _
          (variable_substitution_pattern k u ctx' target (branch_pat br) bt
            Harity_head Hrel)) as Hsub.
        rewrite <- shift_subst_below in Hsub by lia.
        constructor.
        -- rewrite branch_pat_subst, branch_body_subst. exact Hsub.
        -- exact (inner_m rest_brs rest_btl Harity_tail Htail).
  - eapply T_Conv with (i:=i).
    + exact (typed_substitution _ _ _ Ht k u target Hrel).
    + apply Conversion.convertible_subst. exact Hconv.
    + exact (typed_substitution _ _ _ HB k u target Hrel).
Qed.

Theorem body_substitution : forall ctx A u t T,
  has_type ctx u A ->
  has_type (ctx_extend ctx A) t T ->
  has_type ctx (subst 0 u t) (subst 0 u T).
Proof.
  intros ctx A u t T Hu Hbody.
  apply (typed_substitution _ _ _ Hbody 0 u ctx).
  intros index B Hlookup. destruct index as [|index].
  - simpl in Hlookup. inversion Hlookup; subst B.
    rewrite subst_shift_cancel. exact Hu.
  - unfold ctx_extend in Hlookup. simpl in Hlookup.
    rewrite ctx_lookup_shift_ctx in Hlookup.
    destruct (ctx_lookup ctx index) as [C|] eqn:HC; try discriminate.
    inversion Hlookup; subst B.
    rewrite subst_shift_cancel. simpl. apply T_Var. exact HC.
Qed.

Print Assumptions typed_substitution.
Print Assumptions body_substitution.

Example open_dependent_body :
  has_type (ctx_extend [] (type_level 0))
    (Lambda (Var 0) (Var 0)) (Pi (Var 0) None (Var 1)).
Proof.
  change (has_type (ctx_extend [] (type_level 0))
    (subst 0 (Var 0) (Lambda (Var 0) (Var 0)))
    (subst 0 (Var 0) (Pi (Var 0) None (Var 1)))).
  eapply body_substitution with (A:=type_level 0).
  - apply T_Var. reflexivity.
  - eapply T_Lambda with (i:=0).
    + apply T_Var. reflexivity.
    + apply T_Var. reflexivity.
Qed.

Example dependent_let_via_body_substitution :
  has_type [] (Lambda (TSort STime0) (Var 0))
    (Pi (TSort STime0) None (TSort STime0)).
Proof.
  change (has_type []
    (subst 0 (TSort STime0) (Lambda (Var 0) (Var 0)))
    (subst 0 (TSort STime0) (Pi (Var 0) None (Var 1)))).
  eapply body_substitution with (A:=type_level 0).
  - apply T_Time0.
  - eapply T_Lambda with (i:=0).
    + apply T_Var. reflexivity.
    + apply T_Var. reflexivity.
Qed.

Example dependent_telescope_substitution :
  variable_substitution 2 (Var 2)
    (fold_left ctx_extend [type_level 0; Var 0]
      (ctx_extend (ctx_extend [] (type_level 0)) (type_level 0)))
    (fold_left ctx_extend [type_level 0; Var 0]
      (ctx_extend [] (type_level 0))).
Proof.
  change (variable_substitution (0+List.length [type_level 0; Var 0])
    (shift 0 (List.length [type_level 0; Var 0]) (Var 0))
    (fold_left ctx_extend [type_level 0; Var 0]
      (ctx_extend (ctx_extend [] (type_level 0)) (type_level 0)))
    (fold_left ctx_extend (subst_telescope 0 (Var 0) [type_level 0; Var 0])
      (ctx_extend [] (type_level 0)))).
  apply variable_substitution_telescope.
  intros index T Hlookup. destruct index as [|[|index]];
    simpl in Hlookup; try discriminate; inversion Hlookup; subst;
    apply T_Var; reflexivity.
Qed.

Print Assumptions open_dependent_body.
Print Assumptions dependent_let_via_body_substitution.
Print Assumptions dependent_telescope_substitution.
End FormedSubstitution.
