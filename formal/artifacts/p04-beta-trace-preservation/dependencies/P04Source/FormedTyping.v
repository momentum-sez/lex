From Stdlib Require Import Lists.List Arith.Arith.
From Lex Require Import Syntax DeBruijn Typing.
From P04Source Require Import TypeReduction.
Import ListNotations.

(** This relation retains the captured fourteen typing constructors.
    Conversion requires a formed target. Each branch telescope is formed
    sequentially. Application and let retain their dependent result rules. *)
Module Formed.
Inductive has_type : Context -> Term -> Term -> Prop :=

  | T_Var : forall (ctx : Context) (i : nat) (T : Term),
      ctx_lookup ctx i = Some T ->
      has_type ctx (Var i) T

  | T_Type : forall (ctx : Context) (l : Level) (n : nat),
      eval_level l = Some n ->
      has_type ctx (TSort (SType l)) (type_level (S n))

  | T_Prop : forall (ctx : Context),
      has_type ctx (TSort SLProp) (type_level 1)

  | T_Rule : forall (ctx : Context) (l : Level) (n : nat),
      eval_level l = Some n ->
      has_type ctx (TSort (SRule l)) (type_level (S n))

  | T_Time0 : forall (ctx : Context),
      has_type ctx (TSort STime0) (type_level 0)

  | T_Time1 : forall (ctx : Context),
      has_type ctx (TSort STime1) (type_level 0)

  | T_Pi : forall (ctx : Context) (A B : Term) (eff : option EffectRow)
                   (i j : nat),
      has_type ctx A (type_level i) ->
      has_type (ctx_extend ctx A) B (type_level j) ->
      has_type ctx (Pi A eff B) (type_level (Nat.max i j))

  | T_Lambda : forall (ctx : Context) (A B body : Term) (eff : option EffectRow)
                      (i : nat),
      has_type ctx A (type_level i) ->
      has_type (ctx_extend ctx A) body B ->
      has_type ctx (Lambda A body) (Pi A eff B)

  | T_App : forall (ctx : Context) (f a A B : Term) (eff : option EffectRow),
      has_type ctx f (Pi A eff B) ->
      has_type ctx a A ->
      has_type ctx (App f a) (subst 0 a B)

  | T_Annot : forall (ctx : Context) (e T : Term) (i : nat),
      has_type ctx e T ->
      has_type ctx T (type_level i) ->
      has_type ctx (Annot e T) T

  | T_Let : forall (ctx : Context) (A v B body : Term) (i : nat),
      has_type ctx A (type_level i) ->
      has_type ctx v A ->
      has_type (ctx_extend ctx A) body B ->
      has_type ctx (Let A v body) (subst 0 v B)

  | T_Defeasible : forall (ctx : Context) (base_ty base_body : Term)
                          (exns : list Exception) (i : nat),
      has_type ctx base_ty (type_level i) ->
      has_type ctx base_body base_ty ->
      Forall (fun e => has_type ctx (exn_guard e) prop) exns ->
      Forall (fun e => has_type ctx (exn_body e) base_ty) exns ->
      has_type ctx (Defeasible base_ty base_body exns) base_ty

  | T_Match : forall (ctx : Context) (scrutinee return_ty scrut_ty : Term)
                     (branches : list Branch) (i : nat)
                     (binder_tys_list : list (list Term)),
      Forall (fun binder_tys =>
        forall pre A post, binder_tys = pre ++ A :: post ->
          exists j, has_type (fold_left ctx_extend pre ctx) A (type_level j))
        binder_tys_list ->
      has_type ctx scrutinee scrut_ty ->
      has_type ctx return_ty (type_level i) ->
      branches <> nil ->
      List.length branches = List.length binder_tys_list ->
      Forall2 (fun br binder_tys =>
                 List.length binder_tys = pattern_arity (branch_pat br))
              branches binder_tys_list ->
      Forall2 (fun br binder_tys =>
                 has_type
                   (ctx_extend_pattern ctx (branch_pat br) binder_tys)
                   (branch_body br)
                   (shift 0 (pattern_arity (branch_pat br)) return_ty))
              branches binder_tys_list ->
      has_type ctx (Match scrutinee return_ty branches) return_ty

  | T_Conv : forall (ctx : Context) (t A B : Term) (i : nat),
      has_type ctx t A ->
      Conversion.convertible A B ->
      has_type ctx B (type_level i) ->
      has_type ctx t B.


Inductive wf_context : Context -> Prop :=
  | wf_empty : wf_context []
  | wf_extend : forall ctx A i,
      wf_context ctx -> has_type ctx A (type_level i) ->
      wf_context (ctx_extend ctx A).

Lemma intlit_untypable : forall ctx t T,
  has_type ctx t T -> forall n, t <> IntLit n.
Proof.
  intros ctx t T H. induction H; intros lit Heq; inversion Heq.
  eapply IHhas_type1; eauto.
Qed.

Lemma annotation_formation : forall ctx t T,
  has_type ctx t T -> forall e A, t = Annot e A ->
  exists i, has_type ctx A (type_level i).
Proof.
  intros ctx t T H. induction H; intros e0 A0 Heq; inversion Heq; subst.
  - eexists. eassumption.
  - eapply IHhas_type1. reflexivity.
Qed.

Definition malformed_type : Term := Annot (type_level 1) (IntLit 0).

Theorem malformed_type_has_no_formation : forall ctx T,
  ~ has_type ctx malformed_type T.
Proof.
  intros ctx T H.
  destruct (annotation_formation ctx malformed_type T H
    (type_level 1) (IntLit 0) eq_refl) as [i Hi].
  exact (intlit_untypable ctx (IntLit 0) (type_level i) Hi 0 eq_refl).
Qed.

Theorem malformed_conversion_rejected :
  ~ has_type [] prop malformed_type.
Proof.
  intros H. remember (@nil Term) as ctx eqn:Hctx.
  remember prop as t eqn:Ht. remember malformed_type as T eqn:HT.
  induction H; inversion Ht; subst; try discriminate.
  eapply malformed_type_has_no_formation. eassumption.
Qed.

Example proposition_identity :
  has_type [] (Lambda prop (Var 0)) (Pi prop None prop).
Proof.
  eapply T_Lambda.
  - apply T_Prop.
  - apply T_Var. reflexivity.
Qed.

Example universe_polymorphic_identity_body :
  has_type [] (Lambda (type_level 0) (Lambda (Var 0) (Var 0)))
    (Pi (type_level 0) None (Pi (Var 0) None (Var 1))).
Proof.
  eapply T_Lambda.
  - apply T_Type. reflexivity.
  - eapply T_Lambda.
    + apply T_Var. reflexivity.
    + apply T_Var. reflexivity.
Qed.

Example dependent_application :
  has_type []
    (App (Lambda (type_level 0) (Lambda (Var 0) (Var 0))) (TSort STime0))
    (Pi (TSort STime0) None (TSort STime0)).
Proof.
  change (has_type []
    (App (Lambda (type_level 0) (Lambda (Var 0) (Var 0))) (TSort STime0))
    (subst 0 (TSort STime0) (Pi (Var 0) None (Var 1)))).
  eapply T_App.
  - exact universe_polymorphic_identity_body.
  - apply T_Time0.
Qed.

Example dependent_let :
  has_type []
    (Let (type_level 0) (TSort STime0) (Lambda (Var 0) (Var 0)))
    (Pi (TSort STime0) None (TSort STime0)).
Proof.
  change (has_type []
    (Let (type_level 0) (TSort STime0) (Lambda (Var 0) (Var 0)))
    (subst 0 (TSort STime0) (Pi (Var 0) None (Var 1)))).
  eapply T_Let.
  - apply T_Type. reflexivity.
  - apply T_Time0.
  - eapply T_Lambda.
    + apply T_Var. reflexivity.
    + apply T_Var. reflexivity.
Qed.

Example formed_dependent_context :
  wf_context (ctx_extend (ctx_extend [] (type_level 0)) (Var 0)).
Proof.
  eapply wf_extend.
  - eapply wf_extend.
    + apply wf_empty.
    + apply T_Type. reflexivity.
  - apply T_Var. reflexivity.
Qed.

Print Assumptions dependent_let.
Print Assumptions formed_dependent_context.
Print Assumptions malformed_type_has_no_formation.
Print Assumptions malformed_conversion_rejected.
Print Assumptions proposition_identity.
Print Assumptions universe_polymorphic_identity_body.
Print Assumptions dependent_application.
End Formed.
