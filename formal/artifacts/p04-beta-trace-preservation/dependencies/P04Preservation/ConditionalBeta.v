From Stdlib Require Import Lists.List Arith.Arith.
From Lex Require Import Syntax DeBruijn Typing.
From P04Source Require Import TypeReduction FormedTyping FormedRegularity RepairedReduction.
From P04TypedSubstitution Require Import FormedSubstitution.
Import ListNotations.
Import Formed FormedSubstitution.FormedSubstitution.

Module ConditionalBeta.

(** This is the independent missing property of the frozen pure equality.
    It is an explicit hypothesis, not an axiom or a preservation assumption. *)
Definition product_compatibility :=
  forall A B A' B' (eff eff' : option EffectRow),
    Conversion.convertible (Pi A eff B) (Pi A' eff' B') ->
    Conversion.convertible A A' /\ Conversion.convertible B B'.

Lemma lambda_generation : forall ctx t T,
  has_type ctx t T -> forall A body, t = Lambda A body ->
  exists B eff i,
    has_type ctx A (type_level i) /\
    has_type (ctx_extend ctx A) body B /\
    Conversion.convertible (Pi A eff B) T.
Proof.
  intros ctx t T H. induction H; intros A0 body0 Heq; inversion Heq; subst.
  - exists B, eff, i. repeat split; auto. apply Conversion.convertible_refl.
  - destruct (IHhas_type1 A0 body0 eq_refl) as [C [eff [j [HA [Hb HC]]]]].
    exists C, eff, j. repeat split; auto.
    eapply Conversion.convertible_trans; eassumption.
Qed.

Lemma application_generation : forall ctx t T,
  has_type ctx t T -> forall f arg, t = App f arg ->
  exists A B eff,
    has_type ctx f (Pi A eff B) /\ has_type ctx arg A /\
    Conversion.convertible (subst 0 arg B) T.
Proof.
  intros ctx t T H. induction H; intros f0 arg0 Heq; inversion Heq; subst.
  - exists A, B, eff. repeat split; auto. apply Conversion.convertible_refl.
  - destruct (IHhas_type1 f0 arg0 eq_refl) as [D [C [eff [Hf [Ha HC]]]]].
    exists D, C, eff. repeat split; auto.
    eapply Conversion.convertible_trans; eassumption.
Qed.

Theorem beta_preservation_from_product_compatibility :
  product_compatibility -> forall ctx dom body arg T,
  wf_context ctx -> has_type ctx (App (Lambda dom body) arg) T ->
  has_type ctx (subst 0 arg body) T.
Proof.
  intros Hproducts ctx dom body arg T Hwf Hty.
  destruct (application_generation _ _ _ Hty _ _ eq_refl)
    as [A [B [eff [Hfun [Harg Hout]]]]].
  destruct (lambda_generation _ _ _ Hfun _ _ eq_refl)
    as [B0 [eff0 [i [Hdom [Hbody Hpi]]]]].
  destruct (Hproducts _ _ _ _ _ _ Hpi) as [Hdomain Hcodomain].
  assert (Hargdom : has_type ctx arg dom).
  { eapply T_Conv. exact Harg.
    apply Conversion.convertible_sym. exact Hdomain. exact Hdom. }
  pose proof (body_substitution ctx dom arg body B0 Hargdom Hbody) as Hreduct.
  destruct (source_regularity _ _ _ Hty Hwf) as [j Htarget].
  eapply T_Conv. exact Hreduct.
  - eapply Conversion.convertible_trans.
    + apply Conversion.convertible_subst. exact Hcodomain.
    + exact Hout.
  - exact Htarget.
Qed.

Print Assumptions lambda_generation.
Print Assumptions application_generation.
Print Assumptions beta_preservation_from_product_compatibility.
End ConditionalBeta.
