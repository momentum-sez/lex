From Stdlib Require Import Lists.List Arith.Arith Lia.
From Lex Require Import Syntax DeBruijn Typing.
From P04Source Require Import TypeReduction FormedTyping.
From P04RegularityDesign Require Import FormedWeakening.
Import ListNotations.
Import Formed FormedStructural.

Module ContextTransport.

Definition variable_transport (ctx target : Context) :=
  forall index A, ctx_lookup ctx index = Some A -> has_type target (Var index) A.

Lemma variable_transport_extend : forall ctx target A,
  variable_transport ctx target ->
  variable_transport (ctx_extend ctx A) (ctx_extend target A).
Proof.
  intros ctx target A H index T Hlookup. destruct index as [|index].
  - simpl in Hlookup. inversion Hlookup; subst. apply T_Var. reflexivity.
  - unfold ctx_extend in Hlookup. simpl in Hlookup.
    rewrite ctx_lookup_shift_ctx in Hlookup.
    destruct (ctx_lookup ctx index) as [B|] eqn:HB; try discriminate.
    inversion Hlookup; subst T.
    replace (S index) with (index+1) by lia.
    change (has_type (ctx_extend target A)
      (shift 0 1 (Var index)) (shift 0 1 B)).
    apply weakening. apply H. exact HB.
Qed.

Lemma variable_transport_telescope : forall types ctx target,
  variable_transport ctx target ->
  variable_transport (fold_left ctx_extend types ctx)
    (fold_left ctx_extend types target).
Proof.
  induction types as [|A rest IH]; intros ctx target H; simpl; auto.
  apply IH. apply variable_transport_extend. exact H.
Qed.

Lemma variable_transport_pattern : forall pat types ctx target,
  variable_transport ctx target ->
  variable_transport (ctx_extend_pattern ctx pat types)
    (ctx_extend_pattern target pat types).
Proof.
  intros pat types ctx target H. destruct pat; simpl; auto.
  apply variable_transport_telescope. exact H.
Qed.

Fixpoint transport_typing
  (ctx : Context) (t T : Term) (Hty : has_type ctx t T)
  (target : Context) (Hrel : variable_transport ctx target)
  {struct Hty} : has_type target t T.
Proof.
  destruct Hty as
    [ctx' index T0 Hlookup | ctx' l n Hlevel | ctx' | ctx' l n Hlevel
    |ctx'|ctx'|ctx' A B eff i j HA HB
    |ctx' A B body eff i HA Hbody|ctx' f a A B eff Hf Ha
    |ctx' e T0 i He HT|ctx' A v B body i HA Hv Hbody
    |ctx' bt bb exns i Hbt Hbb Hguards Hbodies
    |ctx' scr ret scrut_ty brs i btl Hform Hscr Hret Hne Hlen Harity Htyping
    |ctx' t0 A B i Ht Hconv HB].
  - apply Hrel. exact Hlookup.
  - apply T_Type. exact Hlevel.
  - apply T_Prop.
  - apply T_Rule. exact Hlevel.
  - apply T_Time0.
  - apply T_Time1.
  - eapply T_Pi.
    + exact (transport_typing _ _ _ HA target Hrel).
    + exact (transport_typing _ _ _ HB _ (variable_transport_extend _ _ A Hrel)).
  - eapply T_Lambda.
    + exact (transport_typing _ _ _ HA target Hrel).
    + exact (transport_typing _ _ _ Hbody _ (variable_transport_extend _ _ A Hrel)).
  - eapply T_App.
    + exact (transport_typing _ _ _ Hf target Hrel).
    + exact (transport_typing _ _ _ Ha target Hrel).
  - eapply T_Annot.
    + exact (transport_typing _ _ _ He target Hrel).
    + exact (transport_typing _ _ _ HT target Hrel).
  - eapply T_Let.
    + exact (transport_typing _ _ _ HA target Hrel).
    + exact (transport_typing _ _ _ Hv target Hrel).
    + exact (transport_typing _ _ _ Hbody _ (variable_transport_extend _ _ A Hrel)).
  - eapply T_Defeasible.
    + exact (transport_typing _ _ _ Hbt target Hrel).
    + exact (transport_typing _ _ _ Hbb target Hrel).
    + refine ((fix inner_g xs (H : Forall (fun e => has_type ctx' (exn_guard e) prop) xs)
        {struct H} : Forall (fun e => has_type target (exn_guard e) prop) xs := _) exns Hguards).
      destruct H as [|e rest He Hr]. constructor. constructor.
      exact (transport_typing _ _ _ He target Hrel). exact (inner_g _ Hr).
    + refine ((fix inner_b xs (H : Forall (fun e => has_type ctx' (exn_body e) bt) xs)
        {struct H} : Forall (fun e => has_type target (exn_body e) bt) xs := _) exns Hbodies).
      destruct H as [|e rest He Hr]. constructor. constructor.
      exact (transport_typing _ _ _ He target Hrel). exact (inner_b _ Hr).
  - eapply T_Match with (binder_tys_list:=btl).
    + refine ((fix inner_f xs (H : Forall (fun types => forall pre A post,
          types = pre ++ A :: post -> exists j,
          has_type (fold_left ctx_extend pre ctx') A (type_level j)) xs)
        {struct H} : Forall (fun types => forall pre A post,
          types = pre ++ A :: post -> exists j,
          has_type (fold_left ctx_extend pre target) A (type_level j)) xs := _) btl Hform).
      destruct H as [|types rest Hhead Htail]. constructor. constructor.
      * intros pre A post Heq. destruct (Hhead pre A post Heq) as [j Htyped].
        exists j. exact (transport_typing _ _ _ Htyped _
          (variable_transport_telescope pre ctx' target Hrel)).
      * exact (inner_f _ Htail).
    + exact (transport_typing _ _ _ Hscr target Hrel).
    + exact (transport_typing _ _ _ Hret target Hrel).
    + exact Hne.
    + exact Hlen.
    + exact Harity.
    + refine ((fix inner_b rs ts (H : Forall2 (fun br types =>
          has_type (ctx_extend_pattern ctx' (branch_pat br) types)
            (branch_body br) (shift 0 (pattern_arity (branch_pat br)) ret)) rs ts)
        {struct H} : Forall2 (fun br types =>
          has_type (ctx_extend_pattern target (branch_pat br) types)
            (branch_body br) (shift 0 (pattern_arity (branch_pat br)) ret)) rs ts := _)
        brs btl Htyping).
      destruct H as [|br types rs ts Hhead Htail]. constructor. constructor.
      * exact (transport_typing _ _ _ Hhead _
          (variable_transport_pattern (branch_pat br) types ctx' target Hrel)).
      * exact (inner_b _ _ Htail).
  - eapply T_Conv.
    + exact (transport_typing _ _ _ Ht target Hrel).
    + exact Hconv.
    + exact (transport_typing _ _ _ HB target Hrel).
Qed.

Lemma convertible_head_transport : forall ctx A A' i,
  has_type ctx A (type_level i) -> Conversion.convertible A' A ->
  variable_transport (ctx_extend ctx A) (ctx_extend ctx A').
Proof.
  intros ctx A A' i HA Hconv index T Hlookup. destruct index as [|index].
  - simpl in Hlookup. inversion Hlookup; subst T.
    eapply T_Conv with (A:=shift 0 1 A') (i:=i).
    + apply T_Var. reflexivity.
    + apply Conversion.convertible_shift. exact Hconv.
    + change (has_type (ctx_extend ctx A') (shift 0 1 A)
        (shift 0 1 (type_level i))). apply weakening. exact HA.
  - unfold ctx_extend in Hlookup. simpl in Hlookup.
    rewrite ctx_lookup_shift_ctx in Hlookup.
    destruct (ctx_lookup ctx index) as [B|] eqn:HB; try discriminate.
    inversion Hlookup; subst T. apply T_Var. unfold ctx_extend. simpl.
    rewrite ctx_lookup_shift_ctx, HB. reflexivity.
Qed.

Theorem context_conversion : forall ctx A A' i t T,
  has_type ctx A (type_level i) -> Conversion.convertible A A' ->
  has_type (ctx_extend ctx A) t T -> has_type (ctx_extend ctx A') t T.
Proof.
  intros ctx A A' i t T HA Hconv Hty.
  apply (transport_typing _ _ _ Hty _).
  eapply convertible_head_transport. exact HA.
  apply Conversion.convertible_sym. exact Hconv.
Qed.

Print Assumptions transport_typing.
Print Assumptions context_conversion.
End ContextTransport.
