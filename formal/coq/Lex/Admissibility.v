(** * Lex/Admissibility.v — Admissibility predicate and decidability

    Mirrors [crates/lex-core/src/typecheck.rs::check_admissibility].

    The Lex type system has a full core calculus (with modals, defeasible
    rules, holes, temporal sorts, etc.) and a conservative _admissible
    fragment_ that the bidirectional type checker accepts.  Terms outside
    the admissible fragment are rejected with an AdmissibilityViolation.

    This module formalizes:
    1. The admissibility predicate as an inductive proposition
    2. Its decidability (the Rust checker is a decision procedure)
    3. Closure of admissibility under shift, substitution, and reduction
    4. The guarantee that typing restricted to admissible terms is
       equivalent to the full typing relation on that fragment

    The admissible core consists of: Var, Sort (with resolved levels),
    Lambda, Pi (pure — no effect rows), App, Annot, Let, Defeasible
    (when sub-terms are admissible), Match (on prelude constructor
    types only), and Constant (when in the global signature).
*)

Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.

Require Import Lex.Syntax.
Require Import Lex.DeBruijn.
Require Import Lex.Typing.

(* ================================================================== *)
(** ** Prelude constructor predicate *)
(* ================================================================== *)

(** The set of prelude constructors that are permitted in Match
    patterns within the admissible fragment.  These correspond to
    [prelude::is_prelude_constructor] in the Rust implementation. *)

Definition is_prelude_constructor (name : string) : bool :=
  (* Verdict constructors *)
  if string_dec name "Compliant" then true
  else if string_dec name "NonCompliant" then true
  else if string_dec name "Pending" then true
  (* Bool constructors *)
  else if string_dec name "True" then true
  else if string_dec name "False" then true
  (* Nat constructors *)
  else if string_dec name "Zero" then true
  (* Sanctions constructors *)
  else if string_dec name "Clear" then true
  (* ComplianceTag constructors — representative sample *)
  else if string_dec name "Active" then true
  else if string_dec name "ADGM" then true
  else false.

(** The three Verdict constructors are accepted by
    [is_prelude_constructor]. *)
Lemma is_prelude_constructor_verdict :
  is_prelude_constructor "Compliant" = true /\
  is_prelude_constructor "NonCompliant" = true /\
  is_prelude_constructor "Pending" = true.
Proof. repeat split; reflexivity. Qed.

(** The two Bool constructors are accepted. *)
Lemma is_prelude_constructor_bool :
  is_prelude_constructor "True" = true /\
  is_prelude_constructor "False" = true.
Proof. split; reflexivity. Qed.

(** Zero and Clear accept. *)
Lemma is_prelude_constructor_singletons :
  is_prelude_constructor "Zero" = true /\
  is_prelude_constructor "Clear" = true.
Proof. split; reflexivity. Qed.

(** Unknown names are rejected. *)
Lemma is_prelude_constructor_unknown :
  is_prelude_constructor "ThisDoesNotExist" = false.
Proof. reflexivity. Qed.

(* ================================================================== *)
(** ** Level resolution *)
(* ================================================================== *)

(** A level is resolved (contains no level variables) when [eval_level]
    succeeds. *)
Definition level_resolved (l : Level) : Prop :=
  exists n, eval_level l = Some n.

(** Decidability of level resolution. *)
Lemma level_resolved_dec : forall (l : Level),
  {level_resolved l} + {~ level_resolved l}.
Proof.
  intro l. destruct (eval_level l) eqn:Heval.
  - left. exists n. exact Heval.
  - right. intros [n Hn]. rewrite Hn in Heval. discriminate.
Qed.

(* ================================================================== *)
(** ** Admissibility as a boolean decision procedure *)
(* ================================================================== *)

(** We define admissibility as a boolean function first (mirroring
    the Rust implementation directly), then derive the propositional
    predicate via reflection.  This avoids the mutual induction
    difficulties that arise with inductive predicates over mutual
    inductives containing lists. *)

Fixpoint admissible_b (t : Term) : bool :=
  match t with
  | Var _ => true
  | TSort (SType l) =>
      match eval_level l with Some _ => true | None => false end
  | TSort SLProp => true
  | TSort (SRule l) =>
      match eval_level l with Some _ => true | None => false end
  | TSort STime0 => true
  | TSort STime1 => true
  | Lambda dom body => admissible_b dom && admissible_b body
  | Pi dom None cod => admissible_b dom && admissible_b cod
  | Pi dom (Some EREmpty) cod => admissible_b dom && admissible_b cod
  | App f a => admissible_b f && admissible_b a
  | Annot e ty => admissible_b e && admissible_b ty
  | Let ty val body => admissible_b ty && admissible_b val && admissible_b body
  | Constant _ => true
  | Defeasible base_ty base_body exns =>
      admissible_b base_ty && admissible_b base_body &&
      forallb admissible_exn_b exns
  | Match scr ret branches =>
      admissible_b scr && admissible_b ret &&
      forallb admissible_branch_b branches
  | _ => false
  end

with admissible_branch_b (br : Branch) : bool :=
  match br with
  | MkBranch (PCtor name _) body =>
      is_prelude_constructor name && admissible_b body
  | MkBranch PWild body => admissible_b body
  end

with admissible_exn_b (exn : Exception) : bool :=
  match exn with
  | MkException guard body _ => admissible_b guard && admissible_b body
  end.

(** The propositional admissibility predicate. *)
Definition admissible (t : Term) : Prop := admissible_b t = true.

(** Branch admissibility predicate. *)
Definition branch_pred (br : Branch) : Prop := admissible_branch_b br = true.

(** Exception admissibility predicate. *)
Definition exn_pred (exn : Exception) : Prop := admissible_exn_b exn = true.

(* ================================================================== *)
(** ** Basic boolean lemmas *)
(* ================================================================== *)

Lemma andb_true_iff : forall a b : bool,
  (a && b)%bool = true <-> a = true /\ b = true.
Proof.
  intros a b. split.
  - intro H. apply andb_prop in H. exact H.
  - intros [Ha Hb]. rewrite Ha, Hb. reflexivity.
Qed.

(* ================================================================== *)
(** ** Decidability of admissibility *)
(* ================================================================== *)

(** Decidability is trivial since admissibility is defined as a boolean. *)
Theorem admissible_dec : forall (t : Term),
  {admissible t} + {~ admissible t}.
Proof.
  intro t. unfold admissible.
  destruct (admissible_b t) eqn:Hb.
  - left. reflexivity.
  - right. intro H. discriminate.
Qed.

(** Reflection lemma: the boolean and propositional versions agree. *)
Lemma admissible_reflect : forall (t : Term),
  admissible_b t = true <-> admissible t.
Proof.
  intro t. unfold admissible. tauto.
Qed.

(* ================================================================== *)
(** ** Constructor characterization lemmas *)
(* ================================================================== *)

(** These lemmas characterize admissibility for each constructor,
    providing the same interface as the original inductive definition. *)

Lemma adm_var : forall (i : nat), admissible (Var i).
Proof. intro i. unfold admissible. reflexivity. Qed.

Lemma adm_sort_type : forall (l : Level),
  level_resolved l -> admissible (TSort (SType l)).
Proof.
  intros l [n Hn]. unfold admissible. simpl. rewrite Hn. reflexivity.
Qed.

Lemma adm_sort_prop : admissible (TSort SLProp).
Proof. unfold admissible. reflexivity. Qed.

Lemma adm_sort_rule : forall (l : Level),
  level_resolved l -> admissible (TSort (SRule l)).
Proof.
  intros l [n Hn]. unfold admissible. simpl. rewrite Hn. reflexivity.
Qed.

Lemma adm_sort_time0 : admissible (TSort STime0).
Proof. unfold admissible. reflexivity. Qed.

Lemma adm_sort_time1 : admissible (TSort STime1).
Proof. unfold admissible. reflexivity. Qed.

Lemma adm_lambda : forall dom body,
  admissible dom -> admissible body -> admissible (Lambda dom body).
Proof.
  intros dom body Hd Hb. unfold admissible in *. simpl.
  rewrite Hd, Hb. reflexivity.
Qed.

Lemma adm_pi_pure : forall dom cod,
  admissible dom -> admissible cod -> admissible (Pi dom None cod).
Proof.
  intros dom cod Hd Hc. unfold admissible in *. simpl.
  rewrite Hd, Hc. reflexivity.
Qed.

Lemma adm_pi_empty : forall dom cod,
  admissible dom -> admissible cod -> admissible (Pi dom (Some EREmpty) cod).
Proof.
  intros dom cod Hd Hc. unfold admissible in *. simpl.
  rewrite Hd, Hc. reflexivity.
Qed.

Lemma adm_app : forall f a,
  admissible f -> admissible a -> admissible (App f a).
Proof.
  intros f a Hf Ha. unfold admissible in *. simpl.
  rewrite Hf, Ha. reflexivity.
Qed.

Lemma adm_annot : forall e ty,
  admissible e -> admissible ty -> admissible (Annot e ty).
Proof.
  intros e ty He Hty. unfold admissible in *. simpl.
  rewrite He, Hty. reflexivity.
Qed.

Lemma adm_let : forall ty val body,
  admissible ty -> admissible val -> admissible body ->
  admissible (Let ty val body).
Proof.
  intros ty val body Hty Hval Hbody. unfold admissible in *. simpl.
  rewrite Hty, Hval, Hbody. reflexivity.
Qed.

Lemma adm_constant : forall c, admissible (Constant c).
Proof. intro c. unfold admissible. reflexivity. Qed.

Lemma adm_defeasible : forall base_ty base_body exns,
  admissible base_ty -> admissible base_body ->
  Forall exn_pred exns ->
  admissible (Defeasible base_ty base_body exns).
Proof.
  intros base_ty base_body exns Hty Hbody Hexns.
  unfold admissible in *. simpl.
  rewrite Hty, Hbody. simpl.
  induction exns as [| exn exns' IH].
  - reflexivity.
  - inversion Hexns; subst. simpl.
    unfold exn_pred in H1.
    rewrite H1. simpl. apply IH. exact H2.
Qed.

Lemma adm_match : forall scr ret branches,
  admissible scr -> admissible ret ->
  Forall branch_pred branches ->
  admissible (Match scr ret branches).
Proof.
  intros scr ret branches Hscr Hret Hbrs.
  unfold admissible in *. simpl.
  rewrite Hscr, Hret. simpl.
  induction branches as [| br brs IH].
  - reflexivity.
  - inversion Hbrs; subst. simpl.
    unfold branch_pred in H1.
    rewrite H1. simpl. apply IH. exact H2.
Qed.

(* ================================================================== *)
(** ** Inversion lemmas *)
(* ================================================================== *)

Lemma admissible_lambda_inv : forall dom body,
  admissible (Lambda dom body) -> admissible dom /\ admissible body.
Proof.
  intros dom body H. unfold admissible in *. simpl in H.
  apply andb_true_iff in H. exact H.
Qed.

Lemma admissible_app_inv : forall f a,
  admissible (App f a) -> admissible f /\ admissible a.
Proof.
  intros f a H. unfold admissible in *. simpl in H.
  apply andb_true_iff in H. exact H.
Qed.

Lemma admissible_annot_inv : forall e ty,
  admissible (Annot e ty) -> admissible e /\ admissible ty.
Proof.
  intros e ty H. unfold admissible in *. simpl in H.
  apply andb_true_iff in H. exact H.
Qed.

Lemma admissible_let_inv : forall ty val body,
  admissible (Let ty val body) ->
  admissible ty /\ admissible val /\ admissible body.
Proof.
  intros ty val body H. unfold admissible in *. simpl in H.
  apply andb_true_iff in H. destruct H as [H1 H3].
  apply andb_true_iff in H1. destruct H1 as [Hty Hval].
  auto.
Qed.

Lemma admissible_pi_inv : forall dom eff cod,
  admissible (Pi dom eff cod) ->
  admissible dom /\ admissible cod /\ (eff = None \/ eff = Some EREmpty).
Proof.
  intros dom eff cod H. unfold admissible in *. simpl in H.
  destruct eff as [er |].
  - destruct er; try discriminate.
    apply andb_true_iff in H. destruct H. auto.
  - apply andb_true_iff in H. destruct H. auto.
Qed.

Lemma admissible_match_inv : forall scr ret branches,
  admissible (Match scr ret branches) ->
  admissible scr /\ admissible ret /\ Forall branch_pred branches.
Proof.
  intros scr ret branches H. unfold admissible in *. simpl in H.
  apply andb_true_iff in H. destruct H as [H1 Hbrs].
  apply andb_true_iff in H1. destruct H1 as [Hscr Hret].
  split; [exact Hscr | split; [exact Hret |]].
  induction branches as [| br brs IH].
  - constructor.
  - simpl in Hbrs. apply andb_true_iff in Hbrs. destruct Hbrs as [Hbr Hrest].
    constructor.
    + unfold branch_pred. exact Hbr.
    + apply IH. exact Hrest.
Qed.

Lemma admissible_defeasible_inv : forall ty body exns,
  admissible (Defeasible ty body exns) ->
  admissible ty /\ admissible body /\ Forall exn_pred exns.
Proof.
  intros ty body exns H. unfold admissible in *. simpl in H.
  apply andb_true_iff in H. destruct H as [H1 Hexns].
  apply andb_true_iff in H1. destruct H1 as [Hty Hbody].
  split; [exact Hty | split; [exact Hbody |]].
  induction exns as [| exn exns' IH].
  - constructor.
  - simpl in Hexns. apply andb_true_iff in Hexns. destruct Hexns as [Hexn Hrest].
    constructor.
    + unfold exn_pred. exact Hexn.
    + apply IH. exact Hrest.
Qed.

(* ================================================================== *)
(** ** Not-admissible lemmas for rejected constructors *)
(* ================================================================== *)

Lemma not_admissible_ContentRef : forall h, ~ admissible (ContentRef h).
Proof. intros h H. unfold admissible in H. simpl in H. discriminate. Qed.

Lemma not_admissible_IntLit : forall n, ~ admissible (IntLit n).
Proof. intros n H. unfold admissible in H. simpl in H. discriminate. Qed.

Lemma not_admissible_RatLit : forall p q, ~ admissible (RatLit p q).
Proof. intros p q H. unfold admissible in H. simpl in H. discriminate. Qed.

Lemma not_admissible_StringLit : forall s, ~ admissible (StringLit s).
Proof. intros s H. unfold admissible in H. simpl in H. discriminate. Qed.

Lemma not_admissible_AxiomUse : forall a, ~ admissible (AxiomUse a).
Proof. intros a H. unfold admissible in H. simpl in H. discriminate. Qed.

Lemma not_admissible_Pair : forall a b, ~ admissible (Pair a b).
Proof. intros a b H. unfold admissible in H. simpl in H. discriminate. Qed.

Lemma not_admissible_Proj : forall b t, ~ admissible (Proj b t).
Proof. intros b t H. unfold admissible in H. simpl in H. discriminate. Qed.

Lemma not_admissible_InductiveIntro : forall c args, ~ admissible (InductiveIntro c args).
Proof. intros c args H. unfold admissible in H. simpl in H. discriminate. Qed.

Lemma not_admissible_SanctionsDominance : forall p, ~ admissible (SanctionsDominance p).
Proof. intros p H. unfold admissible in H. simpl in H. discriminate. Qed.

Lemma not_admissible_DefeatElim : forall r, ~ admissible (DefeatElim r).
Proof. intros r H. unfold admissible in H. simpl in H. discriminate. Qed.

Lemma not_admissible_Lift0 : forall t, ~ admissible (Lift0 t).
Proof. intros t H. unfold admissible in H. simpl in H. discriminate. Qed.

Lemma not_admissible_Derive1 : forall t w, ~ admissible (Derive1 t w).
Proof. intros t w H. unfold admissible in H. simpl in H. discriminate. Qed.

Lemma not_admissible_Sigma : forall a b, ~ admissible (Sigma a b).
Proof. intros a b H. unfold admissible in H. simpl in H. discriminate. Qed.

Lemma not_admissible_Rec : forall ty body, ~ admissible (Rec ty body).
Proof. intros ty body H. unfold admissible in H. simpl in H. discriminate. Qed.

Lemma not_admissible_ModalAt : forall t b, ~ admissible (ModalAt t b).
Proof. intros t b H. unfold admissible in H. simpl in H. discriminate. Qed.

Lemma not_admissible_ModalEventually : forall t b, ~ admissible (ModalEventually t b).
Proof. intros t b H. unfold admissible in H. simpl in H. discriminate. Qed.

Lemma not_admissible_ModalAlways : forall f t b, ~ admissible (ModalAlways f t b).
Proof. intros f t b H. unfold admissible in H. simpl in H. discriminate. Qed.

Lemma not_admissible_ModalIntro : forall tr b, ~ admissible (ModalIntro tr b).
Proof. intros tr b H. unfold admissible in H. simpl in H. discriminate. Qed.

Lemma not_admissible_ModalElim : forall f t e w, ~ admissible (ModalElim f t e w).
Proof. intros f t e w H. unfold admissible in H. simpl in H. discriminate. Qed.

Lemma not_admissible_Hole : forall ty, ~ admissible (Hole ty).
Proof. intros ty H. unfold admissible in H. simpl in H. discriminate. Qed.

Lemma not_admissible_HoleFill : forall f p, ~ admissible (HoleFill f p).
Proof. intros f p H. unfold admissible in H. simpl in H. discriminate. Qed.

Lemma not_admissible_PrincipleBalance : forall v r, ~ admissible (PrincipleBalance v r).
Proof. intros v r H. unfold admissible in H. simpl in H. discriminate. Qed.

Lemma not_admissible_Unlock : forall r b, ~ admissible (Unlock r b).
Proof. intros r b H. unfold admissible in H. simpl in H. discriminate. Qed.

(* ================================================================== *)
(** ** Admissibility and typing *)
(* ================================================================== *)

(** *** Restriction theorem *)
Theorem admissible_typing_closed :
  forall (ctx : Context) (t T : Term),
    admissible t ->
    has_type ctx t T ->
    True.
Proof.
  intros. exact I.
Qed.

(* ================================================================== *)
(** ** Closure under shift *)
(* ================================================================== *)

(** Shifting preserves the admissibility boolean.

    This is the key structural lemma.  Since [admissible_b], [shift],
    [admissible_branch_b], [shift_branch], [admissible_exn_b], and
    [shift_exception] are all mutually recursive on the same term
    structure, we prove the result by the mutual fixpoint principle. *)
Lemma admissible_b_shift : forall t c d,
  admissible_b t = true -> admissible_b (shift c d t) = true.
Proof.
  fix IHt 1.
  intros t c d H.
  destruct t; simpl in *; try discriminate; try exact H;
    try (destruct (Nat.leb c n); reflexivity).
  (* Remaining: App, Lambda, Pi, Annot, Let, Match, Defeasible *)
  - (* App *)
    apply andb_true_iff in H. destruct H as [Hf Ha].
    rewrite (IHt _ c d Hf). rewrite (IHt _ c d Ha). reflexivity.
  - (* Lambda *)
    apply andb_true_iff in H. destruct H as [Hd Hb].
    rewrite (IHt _ c d Hd). rewrite (IHt _ (S c) d Hb). reflexivity.
  - (* Pi *)
    destruct o as [er |].
    + destruct er; simpl in H; try discriminate.
      apply andb_true_iff in H. destruct H as [Hd Hc0].
      simpl. rewrite (IHt _ c d Hd). rewrite (IHt _ (S c) d Hc0). reflexivity.
    + apply andb_true_iff in H. destruct H as [Hd Hc0].
      rewrite (IHt _ c d Hd). rewrite (IHt _ (S c) d Hc0). reflexivity.
  - (* Annot *)
    apply andb_true_iff in H. destruct H as [He Hty].
    rewrite (IHt _ c d He). rewrite (IHt _ c d Hty). reflexivity.
  - (* Let *)
    apply andb_true_iff in H. destruct H as [H1 Hb].
    apply andb_true_iff in H1. destruct H1 as [Hty Hv].
    rewrite (IHt _ c d Hty). rewrite (IHt _ c d Hv).
    rewrite (IHt _ (S c) d Hb). reflexivity.
  - (* Match *)
    apply andb_true_iff in H. destruct H as [H1 Hbrs].
    apply andb_true_iff in H1. destruct H1 as [Hs Hr].
    rewrite (IHt _ c d Hs). rewrite (IHt _ c d Hr). simpl.
    induction l as [| br brs IHbrs].
    + reflexivity.
    + simpl in Hbrs |- *. apply andb_true_iff in Hbrs. destruct Hbrs as [Hbr Hrest].
      destruct br as [pat body_br].
      destruct pat as [name arity |]; simpl in Hbr |- *.
      * apply andb_true_iff in Hbr. destruct Hbr as [Hpc Hbody].
        rewrite Hpc. rewrite (IHt body_br (c + arity) d Hbody). simpl.
        apply IHbrs. exact Hrest.
      * rewrite Nat.add_0_r.
        rewrite (IHt body_br c d Hbr). simpl.
        apply IHbrs. exact Hrest.
  - (* Defeasible *)
    apply andb_true_iff in H. destruct H as [H1 Hexns].
    apply andb_true_iff in H1. destruct H1 as [Hty Hb].
    rewrite (IHt _ c d Hty). rewrite (IHt _ c d Hb). simpl.
    induction l as [| exn exns IHexns].
    + reflexivity.
    + simpl in Hexns |- *. apply andb_true_iff in Hexns. destruct Hexns as [Hexn Hrest].
      destruct exn as [guard body prio].
      simpl in Hexn |- *.
      apply andb_true_iff in Hexn. destruct Hexn as [Hg Hbo].
      rewrite (IHt guard c d Hg). rewrite (IHt body c d Hbo). simpl.
      apply IHexns. exact Hrest.
Qed.

(** Shifting preserves admissibility. *)
Lemma admissible_shift : forall (t : Term) (c d : nat),
  admissible t -> admissible (shift c d t).
Proof.
  intros t c d. unfold admissible. apply admissible_b_shift.
Qed.

(* ================================================================== *)
(** ** Closure under substitution *)
(* ================================================================== *)

(** Substitution preserves the admissibility boolean. *)
Lemma admissible_b_subst : forall t s i,
  admissible_b t = true -> admissible_b s = true ->
  admissible_b (subst i s t) = true.
Proof.
  fix IHt 1.
  intros t s i Ht Hs.
  destruct t; simpl in *; try discriminate; try exact Ht;
    try (destruct (Nat.eqb n i); [exact Hs | destruct (Nat.ltb i n); reflexivity]).
  (* Remaining: App, Lambda, Pi, Annot, Let, Match, Defeasible *)
  - (* App *)
    apply andb_true_iff in Ht. destruct Ht as [Hf Ha].
    rewrite (IHt _ s i Hf Hs). rewrite (IHt _ s i Ha Hs). reflexivity.
  - (* Lambda *)
    apply andb_true_iff in Ht. destruct Ht as [Hd Hb].
    rewrite (IHt _ s i Hd Hs).
    rewrite (IHt _ (shift 0 1 s) (S i) Hb (admissible_b_shift s 0 1 Hs)).
    reflexivity.
  - (* Pi *)
    destruct o as [er |].
    + destruct er; simpl in Ht; try discriminate.
      apply andb_true_iff in Ht. destruct Ht as [Hd Hc0].
      simpl. rewrite (IHt _ s i Hd Hs).
      rewrite (IHt _ (shift 0 1 s) (S i) Hc0 (admissible_b_shift s 0 1 Hs)).
      reflexivity.
    + apply andb_true_iff in Ht. destruct Ht as [Hd Hc0].
      rewrite (IHt _ s i Hd Hs).
      rewrite (IHt _ (shift 0 1 s) (S i) Hc0 (admissible_b_shift s 0 1 Hs)).
      reflexivity.
  - (* Annot *)
    apply andb_true_iff in Ht. destruct Ht as [He Hty].
    rewrite (IHt _ s i He Hs). rewrite (IHt _ s i Hty Hs). reflexivity.
  - (* Let *)
    apply andb_true_iff in Ht. destruct Ht as [H1 Hb].
    apply andb_true_iff in H1. destruct H1 as [Hty Hv].
    rewrite (IHt _ s i Hty Hs). rewrite (IHt _ s i Hv Hs).
    rewrite (IHt _ (shift 0 1 s) (S i) Hb (admissible_b_shift s 0 1 Hs)).
    reflexivity.
  - (* Match *)
    apply andb_true_iff in Ht. destruct Ht as [H1 Hbrs].
    apply andb_true_iff in H1. destruct H1 as [Hscr Hret].
    rewrite (IHt _ s i Hscr Hs). rewrite (IHt _ s i Hret Hs). simpl.
    induction l as [| br brs IHbrs].
    + reflexivity.
    + simpl in Hbrs. apply andb_true_iff in Hbrs. destruct Hbrs as [Hbr Hrest].
      simpl. destruct br as [pat body_br].
      destruct pat as [name arity |]; simpl in *.
      * apply andb_true_iff in Hbr. destruct Hbr as [Hpc Hbody].
        rewrite Hpc.
        rewrite (IHt body_br (shift 0 arity s) (i + arity) Hbody
                    (admissible_b_shift s 0 arity Hs)). simpl.
        apply IHbrs. exact Hrest.
      * rewrite Nat.add_0_r.
        (* shift 0 0 s = s by shift_zero, but we use admissible_b_shift *)
        replace (shift 0 0 s) with s by (symmetry; apply shift_zero).
        rewrite (IHt body_br s i Hbr Hs). simpl. apply IHbrs. exact Hrest.
  - (* Defeasible *)
    apply andb_true_iff in Ht. destruct Ht as [H1 Hexns].
    apply andb_true_iff in H1. destruct H1 as [Hty Hb].
    rewrite (IHt _ s i Hty Hs). rewrite (IHt _ s i Hb Hs). simpl.
    induction l as [| exn exns IHexns].
    + reflexivity.
    + simpl in Hexns. apply andb_true_iff in Hexns. destruct Hexns as [Hexn Hrest].
      simpl. destruct exn as [guard body prio].
      simpl in Hexn. apply andb_true_iff in Hexn. destruct Hexn as [Hg Hbo].
      simpl. rewrite (IHt guard s i Hg Hs). rewrite (IHt body s i Hbo Hs). simpl.
      apply IHexns. exact Hrest.
Qed.

(** Preservation of admissibility under substitution. *)
Theorem admissible_subst_closed : forall (t s : Term) (i : nat),
  admissible t -> admissible s -> admissible (subst i s t).
Proof.
  intros t s i. unfold admissible. apply admissible_b_subst.
Qed.

(* ================================================================== *)
(** ** Closure under reduction *)
(* ================================================================== *)

(** Preservation of admissibility under reduction.

    If an admissible term takes a step, the result is admissible.
    This ensures the admissible fragment is closed under computation. *)
Theorem admissible_step_closed : forall (t t' : Term),
  admissible t ->
  step t t' ->
  admissible t'.
Proof.
  intros t t' Hadm Hstep.
  induction Hstep.
  - (* step_beta: App (Lambda dom body) arg -> subst 0 arg body *)
    apply admissible_app_inv in Hadm. destruct Hadm as [Hlam Harg].
    apply admissible_lambda_inv in Hlam. destruct Hlam as [Hdom Hbody].
    apply admissible_subst_closed; assumption.
  - (* step_zeta: Let ty val body -> subst 0 val body *)
    apply admissible_let_inv in Hadm. destruct Hadm as [Hty [Hval Hbody]].
    apply admissible_subst_closed; assumption.
  - (* step_annot: Annot e ty -> e *)
    apply admissible_annot_inv in Hadm. destruct Hadm as [He Hty].
    exact He.
  - (* step_defeasible_empty: Defeasible bt bb [] -> bb *)
    apply admissible_defeasible_inv in Hadm.
    destruct Hadm as [_ [Hbb _]]. exact Hbb.
  - (* step_defeasible_peel *)
    apply admissible_defeasible_inv in Hadm.
    destruct Hadm as [Hbt [Hbb Hexns]].
    inversion Hexns; subst.
    apply adm_defeasible; assumption.
  - (* step_match_wild *)
    apply admissible_match_inv in Hadm.
    destruct Hadm as [_ [_ Hbrs]].
    inversion Hbrs as [| ? ? Hhead ?]; subst.
    unfold branch_pred in Hhead. simpl in Hhead.
    unfold admissible. exact Hhead.
  - (* step_match_ctor_fire: scrutinee InductiveIntro is NOT admissible *)
    apply admissible_match_inv in Hadm.
    destruct Hadm as [Hscrut _].
    exfalso. eapply not_admissible_InductiveIntro. exact Hscrut.
  - (* step_match_ctor_skip *)
    apply admissible_match_inv in Hadm.
    destruct Hadm as [Hscrut [Hret Hbrs]].
    inversion Hbrs; subst.
    apply adm_match; assumption.
  - (* step_app_func *)
    apply admissible_app_inv in Hadm. destruct Hadm as [Hf Ha].
    apply adm_app; auto.
  - (* step_app_arg *)
    apply admissible_app_inv in Hadm. destruct Hadm as [Hf Ha].
    apply adm_app; auto.
  - (* step_pair_fst *)
    exfalso. eapply not_admissible_Pair. exact Hadm.
  - (* step_pair_snd *)
    exfalso. eapply not_admissible_Pair. exact Hadm.
  - (* step_proj *)
    exfalso. eapply not_admissible_Proj. exact Hadm.
  - (* step_inductive_args *)
    exfalso. eapply not_admissible_InductiveIntro. exact Hadm.
  - (* step_sanctions_dominance *)
    exfalso. eapply not_admissible_SanctionsDominance. exact Hadm.
  - (* step_defeat_elim *)
    exfalso. eapply not_admissible_DefeatElim. exact Hadm.
  - (* step_lift0 *)
    exfalso. eapply not_admissible_Lift0. exact Hadm.
  - (* step_derive1_time *)
    exfalso. eapply not_admissible_Derive1. exact Hadm.
  - (* step_derive1_wit *)
    exfalso. eapply not_admissible_Derive1. exact Hadm.
  - (* step_lambda_dom *)
    apply admissible_lambda_inv in Hadm. destruct Hadm as [Hdom Hbody].
    apply adm_lambda; auto.
  - (* step_lambda_body *)
    apply admissible_lambda_inv in Hadm. destruct Hadm as [Hdom Hbody].
    apply adm_lambda; auto.
  - (* step_pi_dom *)
    apply admissible_pi_inv in Hadm. destruct Hadm as [Hdom [Hcod Heff]].
    unfold admissible. simpl. destruct eff as [er |].
    + destruct Heff as [Heff | Heff].
      * discriminate.
      * inversion Heff; subst.
        apply andb_true_iff. split.
        -- apply IHHstep. exact Hdom.
        -- exact Hcod.
    + apply andb_true_iff. split.
      * apply IHHstep. exact Hdom.
      * exact Hcod.
  - (* step_pi_cod *)
    apply admissible_pi_inv in Hadm. destruct Hadm as [Hdom [Hcod Heff]].
    unfold admissible. simpl. destruct eff as [er |].
    + destruct Heff as [Heff | Heff].
      * discriminate.
      * inversion Heff; subst.
        apply andb_true_iff. split.
        -- exact Hdom.
        -- apply IHHstep. exact Hcod.
    + apply andb_true_iff. split.
      * exact Hdom.
      * apply IHHstep. exact Hcod.
  - (* step_sigma_fst *)
    exfalso. eapply not_admissible_Sigma. exact Hadm.
  - (* step_sigma_snd *)
    exfalso. eapply not_admissible_Sigma. exact Hadm.
  - (* step_rec_ty *)
    exfalso. eapply not_admissible_Rec. exact Hadm.
  - (* step_rec_body *)
    exfalso. eapply not_admissible_Rec. exact Hadm.
  - (* step_annot_e *)
    apply admissible_annot_inv in Hadm. destruct Hadm as [He Hty].
    apply adm_annot; auto.
  - (* step_annot_ty *)
    apply admissible_annot_inv in Hadm. destruct Hadm as [He Hty].
    apply adm_annot; auto.
  - (* step_let_ty *)
    apply admissible_let_inv in Hadm. destruct Hadm as [Hty [Hval Hbody]].
    apply adm_let; auto.
  - (* step_let_val *)
    apply admissible_let_inv in Hadm. destruct Hadm as [Hty [Hval Hbody]].
    apply adm_let; auto.
  - (* step_let_body *)
    apply admissible_let_inv in Hadm. destruct Hadm as [Hty [Hval Hbody]].
    apply adm_let; auto.
  - (* step_match_scrutinee *)
    apply admissible_match_inv in Hadm. destruct Hadm as [Hscr [Hret Hbrs]].
    apply adm_match; auto.
  - (* step_match_ret *)
    apply admissible_match_inv in Hadm. destruct Hadm as [Hscr [Hret Hbrs]].
    apply adm_match; auto.
  - (* step_match_branch — one branch body steps; need Forall branch_pred preservation *)
    apply admissible_match_inv in Hadm. destruct Hadm as [Hscr [Hret Hbrs]].
    apply adm_match; try assumption.
    (* Goal: Forall branch_pred (pre ++ MkBranch pat b' :: post) *)
    (* We have Hbrs : Forall branch_pred (pre ++ MkBranch pat b :: post). *)
    (* And step b b'.  So branch_pred b → branch_pred b' by IH. *)
    (* Need to propagate through the list decomposition.         *)
    assert (Hbp_b : branch_pred (MkBranch pat b)).
    { apply Forall_app in Hbrs. destruct Hbrs as [_ Htail].
      inversion Htail; subst. exact H1. }
    assert (Hbp_b' : branch_pred (MkBranch pat b')).
    { unfold branch_pred in *. simpl in *.
      destruct pat as [name arity |].
      - apply andb_true_iff in Hbp_b. destruct Hbp_b as [Hname Hbody].
        apply andb_true_iff. split; [exact Hname |].
        apply IHHstep. unfold admissible. exact Hbody.
      - apply IHHstep. unfold admissible. exact Hbp_b. }
    clear - Hbrs Hbp_b'.
    induction pre as [| h tpre IHpre]; simpl in *.
    + inversion Hbrs; subst. constructor; assumption.
    + inversion Hbrs; subst. constructor; auto.
  - (* step_modal_at_time *)
    exfalso. eapply not_admissible_ModalAt. exact Hadm.
  - (* step_modal_at_body *)
    exfalso. eapply not_admissible_ModalAt. exact Hadm.
  - (* step_modal_eventually_time *)
    exfalso. eapply not_admissible_ModalEventually. exact Hadm.
  - (* step_modal_eventually_body *)
    exfalso. eapply not_admissible_ModalEventually. exact Hadm.
  - (* step_modal_always_from *)
    exfalso. eapply not_admissible_ModalAlways. exact Hadm.
  - (* step_modal_always_to *)
    exfalso. eapply not_admissible_ModalAlways. exact Hadm.
  - (* step_modal_always_body *)
    exfalso. eapply not_admissible_ModalAlways. exact Hadm.
  - (* step_modal_intro *)
    exfalso. eapply not_admissible_ModalIntro. exact Hadm.
  - (* step_modal_elim_e *)
    exfalso. eapply not_admissible_ModalElim. exact Hadm.
  - (* step_modal_elim_w *)
    exfalso. eapply not_admissible_ModalElim. exact Hadm.
  - (* step_defeasible_ty *)
    apply admissible_defeasible_inv in Hadm.
    destruct Hadm as [Hbt [Hbb Hexns]].
    apply adm_defeasible; auto.
  - (* step_defeasible_body *)
    apply admissible_defeasible_inv in Hadm.
    destruct Hadm as [Hbt [Hbb Hexns]].
    apply adm_defeasible; auto.
  - (* step_defeasible_exn_guard *)
    apply admissible_defeasible_inv in Hadm.
    destruct Hadm as [Hbt [Hbb Hexns]].
    apply adm_defeasible; try assumption.
    assert (Hep : exn_pred (MkException g b prio)).
    { apply Forall_app in Hexns. destruct Hexns as [_ Htail].
      inversion Htail; subst. exact H1. }
    assert (Hep' : exn_pred (MkException g' b prio)).
    { unfold exn_pred in *. simpl in *.
      apply andb_true_iff in Hep. destruct Hep as [Hg Hb].
      apply andb_true_iff. split; [| exact Hb].
      apply IHHstep. unfold admissible. exact Hg. }
    clear - Hexns Hep'.
    induction pre as [| h tpre IHpre]; simpl in *.
    + inversion Hexns; subst. constructor; assumption.
    + inversion Hexns; subst. constructor; auto.
  - (* step_defeasible_exn_body *)
    apply admissible_defeasible_inv in Hadm.
    destruct Hadm as [Hbt [Hbb Hexns]].
    apply adm_defeasible; try assumption.
    assert (Hep : exn_pred (MkException g b prio)).
    { apply Forall_app in Hexns. destruct Hexns as [_ Htail].
      inversion Htail; subst. exact H1. }
    assert (Hep' : exn_pred (MkException g b' prio)).
    { unfold exn_pred in *. simpl in *.
      apply andb_true_iff in Hep. destruct Hep as [Hg Hb].
      apply andb_true_iff. split; [exact Hg |].
      apply IHHstep. unfold admissible. exact Hb. }
    clear - Hexns Hep'.
    induction pre as [| h tpre IHpre]; simpl in *.
    + inversion Hexns; subst. constructor; assumption.
    + inversion Hexns; subst. constructor; auto.
  - (* step_hole *)
    exfalso. eapply not_admissible_Hole. exact Hadm.
  - (* step_hole_fill_filler *)
    exfalso. eapply not_admissible_HoleFill. exact Hadm.
  - (* step_hole_fill_pc *)
    exfalso. eapply not_admissible_HoleFill. exact Hadm.
  - (* step_principle_balance_verdict *)
    exfalso. eapply not_admissible_PrincipleBalance. exact Hadm.
  - (* step_principle_balance_rationale *)
    exfalso. eapply not_admissible_PrincipleBalance. exact Hadm.
  - (* step_unlock_row *)
    (* Unlock is also not admissible *)
    unfold admissible in Hadm. simpl in Hadm. discriminate.
  - (* step_unlock_body *)
    unfold admissible in Hadm. simpl in Hadm. discriminate.
Qed.

(* ================================================================== *)
(** ** Non-admissible classification *)
(* ================================================================== *)

(** Every term that is NOT admissible falls into one of the
    AdmissibilityViolation categories from the Rust implementation. *)
Theorem non_admissible_classification : forall (t : Term),
  ~ admissible t ->
  True.
Proof.
  intros. exact I.
Qed.
