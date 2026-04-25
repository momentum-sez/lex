(** * Lex/BridgeSemantics.v -- proof-relevant bridge target

    Tribunal transport in Lex is proof-relevant.  A bridge witness is not only
    a function between modal carriers; it is a legal/canonical instrument whose
    provenance must survive certificate extraction.  This file names the
    bicategorical target and the modal-action laws as typed propositions.  It
    does not assert the laws globally.
*)

Require Import Stdlib.Classes.RelationClasses.

Set Universe Polymorphism.

Record bridge_signature : Type := mkBridgeSignature {
  Tribunal : Type;
  Interface : Type;
  ModalCarrier : Tribunal -> Interface -> Type;
  CanonBridge : Tribunal -> Tribunal -> Interface -> Type;
  BridgeEq :
    forall {A : Interface} {T1 T2 : Tribunal},
      CanonBridge T1 T2 A -> CanonBridge T1 T2 A -> Prop;
  id_bridge :
    forall (A : Interface) (T : Tribunal),
      CanonBridge T T A;
  compose_bridge :
    forall (A : Interface) (T1 T2 T3 : Tribunal),
      CanonBridge T1 T2 A ->
      CanonBridge T2 T3 A ->
      CanonBridge T1 T3 A;
  coerce_bridge :
    forall (A : Interface) (T1 T2 : Tribunal),
      CanonBridge T1 T2 A ->
      ModalCarrier T1 A ->
      ModalCarrier T2 A
}.

Arguments Tribunal _ : clear implicits, assert.
Arguments Interface _ : clear implicits, assert.
Arguments ModalCarrier _ _ _ : assert.
Arguments CanonBridge _ _ _ _ : assert.
Arguments BridgeEq _ {_ _ _} _ _ : assert.
Arguments id_bridge _ _ _ : assert.
Arguments compose_bridge _ _ _ _ _ _ _ : assert.
Arguments coerce_bridge _ _ _ _ _ _ : assert.

Definition bridge_identity_laws (S : bridge_signature) : Prop :=
  forall (A : Interface S) (T1 T2 : Tribunal S)
         (b : CanonBridge S T1 T2 A),
    BridgeEq S (compose_bridge S A T1 T1 T2 (id_bridge S A T1) b) b /\
    BridgeEq S (compose_bridge S A T1 T2 T2 b (id_bridge S A T2)) b.

Definition bridge_associativity_law (S : bridge_signature) : Prop :=
  forall (A : Interface S) (T1 T2 T3 T4 : Tribunal S)
         (b12 : CanonBridge S T1 T2 A)
         (b23 : CanonBridge S T2 T3 A)
         (b34 : CanonBridge S T3 T4 A),
    BridgeEq S
      (compose_bridge S A T1 T3 T4
         (compose_bridge S A T1 T2 T3 b12 b23)
         b34)
      (compose_bridge S A T1 T2 T4
         b12
         (compose_bridge S A T2 T3 T4 b23 b34)).

Definition bridge_eq_equivalence (S : bridge_signature) : Prop :=
  forall (A : Interface S) (T1 T2 : Tribunal S),
    Equivalence (@BridgeEq S A T1 T2).

Definition bridge_whiskering_laws (S : bridge_signature) : Prop :=
  forall (A : Interface S) (T1 T2 T3 : Tribunal S)
         (b b' : CanonBridge S T1 T2 A)
         (c c' : CanonBridge S T2 T3 A),
    BridgeEq S b b' ->
    BridgeEq S c c' ->
    BridgeEq S
      (compose_bridge S A T1 T2 T3 b c)
      (compose_bridge S A T1 T2 T3 b' c').

Record bridge_bicategory_laws (S : bridge_signature) : Prop := {
  bridge_eq_is_equivalence : bridge_eq_equivalence S;
  bridge_identity : bridge_identity_laws S;
  bridge_associative : bridge_associativity_law S;
  bridge_whiskering : bridge_whiskering_laws S
}.

Definition modal_action_identity_law (S : bridge_signature) : Prop :=
  forall (A : Interface S) (T : Tribunal S)
         (x : ModalCarrier S T A),
    coerce_bridge S A T T (id_bridge S A T) x = x.

Definition modal_action_composition_law (S : bridge_signature) : Prop :=
  forall (A : Interface S) (T1 T2 T3 : Tribunal S)
         (b12 : CanonBridge S T1 T2 A)
         (b23 : CanonBridge S T2 T3 A)
         (x : ModalCarrier S T1 A),
    coerce_bridge S A T1 T3
      (compose_bridge S A T1 T2 T3 b12 b23) x =
    coerce_bridge S A T2 T3 b23
      (coerce_bridge S A T1 T2 b12 x).

Definition modal_action_respects_2cells (S : bridge_signature) : Prop :=
  forall (A : Interface S) (T1 T2 : Tribunal S)
         (b b' : CanonBridge S T1 T2 A),
    BridgeEq S b b' ->
    forall x : ModalCarrier S T1 A,
      coerce_bridge S A T1 T2 b x =
      coerce_bridge S A T1 T2 b' x.

Record bridge_modal_action_laws (S : bridge_signature) : Prop := {
  modal_action_identity : modal_action_identity_law S;
  modal_action_composition : modal_action_composition_law S;
  modal_action_2cell_congruence : modal_action_respects_2cells S
}.

(** The certificate layer must keep [CanonBridge] witnesses.  Extensional
    equality of coercion functions is only a projection, not the certificate
    identity relation. *)
Definition bridge_extensional_projection (S : bridge_signature) : Prop :=
  forall (A : Interface S) (T1 T2 : Tribunal S)
         (b b' : CanonBridge S T1 T2 A),
    BridgeEq S b b' ->
    forall x : ModalCarrier S T1 A,
      coerce_bridge S A T1 T2 b x =
      coerce_bridge S A T1 T2 b' x.

Definition strict_2functor_coherence (S : bridge_signature) : Prop :=
  bridge_bicategory_laws S /\ bridge_modal_action_laws S.

(** Proof-relevant bridges retain certificate provenance.  The semantic
    projection below deliberately forgets that provenance; it is the target
    used by the strict function model, not the extracted certificate itself. *)
Record proof_relevant_bridge_signature : Type := mkProofRelevantBridgeSignature {
  PRTribunal : Type;
  PRInterface : Type;
  PRModalCarrier : PRTribunal -> PRInterface -> Type;
  PRProvenance : Type;
  PRCanonBridge : PRTribunal -> PRTribunal -> PRInterface -> Type;
  PRBridgeEq :
    forall {A : PRInterface} {T1 T2 : PRTribunal},
      PRCanonBridge T1 T2 A -> PRCanonBridge T1 T2 A -> Prop;
  PRBridgeProvenance :
    forall {A : PRInterface} {T1 T2 : PRTribunal},
      PRCanonBridge T1 T2 A -> PRProvenance;
  PRIdBridge :
    forall (A : PRInterface) (T : PRTribunal),
      PRCanonBridge T T A;
  PRComposeBridge :
    forall (A : PRInterface) (T1 T2 T3 : PRTribunal),
      PRCanonBridge T1 T2 A ->
      PRCanonBridge T2 T3 A ->
      PRCanonBridge T1 T3 A;
  PRCoerceBridge :
    forall (A : PRInterface) (T1 T2 : PRTribunal),
      PRCanonBridge T1 T2 A ->
      PRModalCarrier T1 A ->
      PRModalCarrier T2 A
}.

Definition erase_provenance_signature
    (S : proof_relevant_bridge_signature) : bridge_signature :=
  mkBridgeSignature
    (PRTribunal S)
    (PRInterface S)
    (PRModalCarrier S)
    (PRCanonBridge S)
    (fun A T1 T2 => @PRBridgeEq S A T1 T2)
    (PRIdBridge S)
    (PRComposeBridge S)
    (PRCoerceBridge S).

Definition proof_relevant_strict_2functor_coherence
    (S : proof_relevant_bridge_signature) : Prop :=
  strict_2functor_coherence (erase_provenance_signature S).

Definition bridge_provenance_preserved
    (S : proof_relevant_bridge_signature) : Prop :=
  forall (A : PRInterface S) (T1 T2 : PRTribunal S)
         (b : PRCanonBridge S T1 T2 A),
    exists p : PRProvenance S,
      p = PRBridgeProvenance S b.

(** Bridge admission is partial.  The total [coerce_bridge] action starts
    only after an admission layer has returned an actual [CanonBridge]. *)
Record bridge_admission_layer (S : bridge_signature) : Type := {
  BridgeRequest :
    Tribunal S -> Tribunal S -> Interface S -> Type;
  admit_bridge :
    forall (A : Interface S) (T1 T2 : Tribunal S),
      BridgeRequest T1 T2 A -> option (CanonBridge S T1 T2 A)
}.

Definition admitted_coerce {S : bridge_signature}
    (L : bridge_admission_layer S)
    (A : Interface S) (T1 T2 : Tribunal S)
    (r : BridgeRequest S L T1 T2 A)
    (x : ModalCarrier S T1 A) : option (ModalCarrier S T2 A) :=
  match admit_bridge S L A T1 T2 r with
  | Some b => Some (coerce_bridge S A T1 T2 b x)
  | None => None
  end.

Theorem admitted_coerce_some :
  forall {S : bridge_signature} (L : bridge_admission_layer S)
         (A : Interface S) (T1 T2 : Tribunal S)
         (r : BridgeRequest S L T1 T2 A)
         (b : CanonBridge S T1 T2 A)
         (x : ModalCarrier S T1 A),
    admit_bridge S L A T1 T2 r = Some b ->
    admitted_coerce L A T1 T2 r x =
    Some (coerce_bridge S A T1 T2 b x).
Proof.
  intros S L A T1 T2 r b x Hadmit.
  unfold admitted_coerce.
  rewrite Hadmit.
  reflexivity.
Qed.

Theorem admitted_coerce_none :
  forall {S : bridge_signature} (L : bridge_admission_layer S)
         (A : Interface S) (T1 T2 : Tribunal S)
         (r : BridgeRequest S L T1 T2 A)
         (x : ModalCarrier S T1 A),
    admit_bridge S L A T1 T2 r = None ->
    admitted_coerce L A T1 T2 r x = None.
Proof.
  intros S L A T1 T2 r x Hadmit.
  unfold admitted_coerce.
  rewrite Hadmit.
  reflexivity.
Qed.

(** ** Canonical strict function-bridge model

    The abstract [bridge_signature] above deliberately does not assume the
    bicategory and modal-action laws.  The canonical target needed by the paper
    is the strict model in which a bridge is an ordinary function between modal
    carriers and a 2-cell is pointwise equality of such functions.  This model
    carries no hidden proof irrelevance or functional-extensionality axiom: all
    coherence laws reduce pointwise by computation. *)
Section StrictFunctionBridgeModel.
  Context {T A : Type}.
  Variable Carrier : T -> A -> Type.

  Definition function_bridge_signature : bridge_signature :=
    mkBridgeSignature
      T
      A
      Carrier
      (fun t1 t2 a => Carrier t1 a -> Carrier t2 a)
      (fun a t1 t2 f g => forall x, f x = g x)
      (fun a t x => x)
      (fun a t1 t2 t3 f g x => g (f x))
      (fun a t1 t2 f x => f x).

  Theorem function_bridge_eq_equivalence :
    bridge_eq_equivalence function_bridge_signature.
  Proof.
    unfold bridge_eq_equivalence, function_bridge_signature.
    intros a t1 t2.
    constructor.
    - intros f x. reflexivity.
    - intros f g Hfg x. symmetry. apply Hfg.
    - intros f g h Hfg Hgh x. transitivity (g x); [apply Hfg | apply Hgh].
  Qed.

  Theorem function_bridge_identity_laws :
    bridge_identity_laws function_bridge_signature.
  Proof.
    unfold bridge_identity_laws, function_bridge_signature.
    intros a t1 t2 b.
    split; intros x; reflexivity.
  Qed.

  Theorem function_bridge_associativity_law :
    bridge_associativity_law function_bridge_signature.
  Proof.
    unfold bridge_associativity_law, function_bridge_signature.
    intros a t1 t2 t3 t4 b12 b23 b34 x.
    reflexivity.
  Qed.

  Theorem function_bridge_whiskering_laws :
    bridge_whiskering_laws function_bridge_signature.
  Proof.
    unfold bridge_whiskering_laws, function_bridge_signature.
    intros a t1 t2 t3 b b' c c' Hbb' Hcc' x.
    cbn in *.
    transitivity (c (b' x)).
    - f_equal. apply Hbb'.
    - apply Hcc'.
  Qed.

  Theorem function_bridge_bicategory_laws :
    bridge_bicategory_laws function_bridge_signature.
  Proof.
    constructor.
    - exact function_bridge_eq_equivalence.
    - exact function_bridge_identity_laws.
    - exact function_bridge_associativity_law.
    - exact function_bridge_whiskering_laws.
  Qed.

  Theorem function_modal_action_identity_law :
    modal_action_identity_law function_bridge_signature.
  Proof.
    unfold modal_action_identity_law, function_bridge_signature.
    intros a t x. reflexivity.
  Qed.

  Theorem function_modal_action_composition_law :
    modal_action_composition_law function_bridge_signature.
  Proof.
    unfold modal_action_composition_law, function_bridge_signature.
    intros a t1 t2 t3 b12 b23 x. reflexivity.
  Qed.

  Theorem function_modal_action_respects_2cells :
    modal_action_respects_2cells function_bridge_signature.
  Proof.
    unfold modal_action_respects_2cells, function_bridge_signature.
    intros a t1 t2 b b' Hbb' x. cbn in *. apply Hbb'.
  Qed.

  Theorem function_bridge_modal_action_laws :
    bridge_modal_action_laws function_bridge_signature.
  Proof.
    constructor.
    - exact function_modal_action_identity_law.
    - exact function_modal_action_composition_law.
    - exact function_modal_action_respects_2cells.
  Qed.

  Theorem function_bridge_strict_2functor_coherence :
    strict_2functor_coherence function_bridge_signature.
  Proof.
    split.
    - exact function_bridge_bicategory_laws.
    - exact function_bridge_modal_action_laws.
  Qed.

  Theorem function_bridge_extensional_projection :
    bridge_extensional_projection function_bridge_signature.
  Proof.
    unfold bridge_extensional_projection, function_bridge_signature.
    intros a t1 t2 b b' Hbb' x. cbn in *. apply Hbb'.
  Qed.
End StrictFunctionBridgeModel.
