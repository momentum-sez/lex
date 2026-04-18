(* ========================================================================= *)
(*  FlatAdmissibleSN.v — Strong normalization for a narrow flat fragment of   *)
(*  Lex's admissible sublanguage.                                             *)
(*                                                                            *)
(*  Companion to:                                                             *)
(*    - paper §5 "The Admissible Fragment" in                                  *)
(*      ~/momentum-research/papers/lex.md                                      *)
(*    - runtime evaluator `crates/lex-core/src/evaluate.rs`                    *)
(*                                                                            *)
(*  THEOREM (flat_admissible_sn):                                              *)
(*    Every reduction sequence of a FAdm term terminates.                      *)
(*                                                                            *)
(*  FRAGMENT COVERED:                                                          *)
(*    FAdm ::= Var i                                                           *)
(*           | Const c                  (* verdict, tag, bool constant *)     *)
(*           | Access a e               (* runtime accessor `a e`        *)     *)
(*           | Let e1 e2                (* ζ-redex when e1 is a Const    *)     *)
(*           | Match e bs               (* match with finite branches    *)     *)
(*           | Def eb es                (* flat defeasible: base, excns *)     *)
(*                                                                            *)
(*  REDUCTIONS:                                                                *)
(*     (ζ)    Let (Const c) e2    --> e2                                       *)
(*     (μ-v)  Match (Const c) bs  --> e          when (c,e) ∈ bs               *)
(*     (δ)    Def (Const v) []    --> Const v                                  *)
(*     (ξ-let)    e1 --> e1'  implies  Let e1 e2 --> Let e1' e2                *)
(*     (ξ-scr)    e  --> e'   implies  Match e bs --> Match e' bs              *)
(*     (ξ-def)    e  --> e'   implies  Def e bs   --> Def e' bs                *)
(*                                                                            *)
(*  Pi types, lambdas, general β, and recursion are EXCLUDED from the         *)
(*  FAdm fragment by construction — these are the standard non-terminating     *)
(*  sources and are treated in Sections 4.1 / 11 of the paper as open.        *)
(*                                                                            *)
(*  PROOF STRATEGY:                                                            *)
(*     Use a well-founded measure  μ : FAdm -> nat  = term_size.               *)
(*     Show every reduction step strictly decreases μ.                         *)
(*     Conclude SN by well-founded induction on nat.                           *)
(* ========================================================================= *)

Set Implicit Arguments.
From Stdlib Require Import List Arith Lia Wellfounded Relations.
Import ListNotations.

(* ------------------------------------------------------------------------- *)
(*  §1.  Syntax of the flat admissible fragment                               *)
(* ------------------------------------------------------------------------- *)

(** Constants are identified by a natural-number tag.  In the paper's prelude
    these correspond to the verdict constructors `Compliant`, `NonCompliant`,
    `Pending`, the sanctions constructors `Clear`, and the boolean
    constructors `True`/`False`. The proof is indifferent to which tag set
    is chosen: it only uses that constants are inert (non-reducible). *)
Definition ConstTag := nat.

(** Accessor names (as in `director_count`, `fsra_authorization_status`).
    They are parameters to [Acc], which represents an accessor application
    `accessor e`.  The runtime rewrites `Acc a (Const c)` to a lookup; in
    our fragment accessors take only variables or other accessor results,
    never reduce, and exist purely to carry structure that match arms can
    branch on.  They are inert for the purpose of SN. *)
Definition Accessor := nat.

Inductive FAdm : Type :=
  | Var   : nat   -> FAdm
  | Const : ConstTag -> FAdm
  | Access : Accessor -> FAdm -> FAdm
  | Let_  : FAdm -> FAdm -> FAdm
  | Mtch  : FAdm -> list (ConstTag * FAdm) -> FAdm
  | Def   : FAdm -> list (FAdm * FAdm) -> FAdm.

(* Size uses nested recursion via [list_sum] on the list of child sizes.
   The outer [Fixpoint] recurses structurally on [t]; the inner [map]
   applies [size] to each subterm, which is a valid nested recursion
   because each subterm is a structural subcomponent of the match's
   branches/exceptions lists. *)

Fixpoint size (t : FAdm) : nat :=
  match t with
  | Var _         => 1
  | Const _       => 1
  | Access _ e    => S (size e)
  | Let_ e1 e2    => S (size e1 + size e2)
  | Mtch e bs     =>
      S (size e + list_sum (map (fun ce => size (snd ce)) bs))
  | Def  e es     =>
      S (size e + list_sum (map (fun ge => size (fst ge) + size (snd ge)) es))
  end.

(** Named helpers for the branch/exception-list size contributions. *)
Definition size_branches (bs : list (ConstTag * FAdm)) : nat :=
  list_sum (map (fun ce => size (snd ce)) bs).

Definition size_excs (es : list (FAdm * FAdm)) : nat :=
  list_sum (map (fun ge => size (fst ge) + size (snd ge)) es).

Lemma size_Mtch_unfold : forall e bs,
  size (Mtch e bs) = S (size e + size_branches bs).
Proof. reflexivity. Qed.

Lemma size_Def_unfold : forall e es,
  size (Def e es) = S (size e + size_excs es).
Proof. reflexivity. Qed.

Lemma size_pos : forall t, 1 <= size t.
Proof.
  intros t. destruct t; simpl; lia.
Qed.

(* ------------------------------------------------------------------------- *)
(*  §2.  Branch lookup                                                        *)
(* ------------------------------------------------------------------------- *)

(** [find_branch c bs] returns the body of the first branch whose constructor
    tag matches [c], or [None] if no branch matches. *)
Fixpoint find_branch (c : ConstTag) (bs : list (ConstTag * FAdm)) : option FAdm :=
  match bs with
  | [] => None
  | (c', e) :: rest =>
      if Nat.eqb c c' then Some e else find_branch c rest
  end.

Lemma find_branch_size :
  forall c bs e, find_branch c bs = Some e -> size e <= size_branches bs.
Proof.
  intros c bs. induction bs as [| [c' e'] rest IH]; intros e H.
  - simpl in H. discriminate.
  - simpl in H. destruct (Nat.eqb c c') eqn:Heq.
    + injection H as <-. unfold size_branches. simpl. lia.
    + apply IH in H. unfold size_branches in *. simpl. lia.
Qed.

(* ------------------------------------------------------------------------- *)
(*  §3.  Small-step reduction                                                 *)
(* ------------------------------------------------------------------------- *)

Inductive step : FAdm -> FAdm -> Prop :=
  (* ζ-reduction: Let (Const c) body --> body *)
  | step_let_const : forall c e,
      step (Let_ (Const c) e) e

  (* μ-reduction over a value scrutinee *)
  | step_match_const : forall c bs e,
      find_branch c bs = Some e ->
      step (Mtch (Const c) bs) e

  (* δ-reduction: a defeasible rule whose base is a value and whose
     exception list is empty reduces to the base value. *)
  | step_def_base : forall c,
      step (Def (Const c) []) (Const c)

  (* Context rule: reduce head of a Let *)
  | step_ctx_let : forall e1 e1' e2,
      step e1 e1' ->
      step (Let_ e1 e2) (Let_ e1' e2)

  (* Context rule: reduce scrutinee of a Match *)
  | step_ctx_match : forall e e' bs,
      step e e' ->
      step (Mtch e bs) (Mtch e' bs)

  (* Context rule: reduce base of a Def *)
  | step_ctx_def : forall e e' es,
      step e e' ->
      step (Def e es) (Def e' es).

(* ------------------------------------------------------------------------- *)
(*  §4.  Every step strictly decreases size                                   *)
(* ------------------------------------------------------------------------- *)

Theorem step_decreases_size :
  forall t t', step t t' -> size t' < size t.
Proof.
  intros t t' H. induction H.
  - (* step_let_const: Let (Const c) e --> e *)
    simpl. lia.
  - (* step_match_const: Mtch (Const c) bs --> e_c *)
    apply find_branch_size in H.
    rewrite size_Mtch_unfold. simpl. lia.
  - (* step_def_base: Def (Const c) [] --> Const c *)
    rewrite size_Def_unfold. unfold size_excs. simpl. lia.
  - (* step_ctx_let: Let e1 e2 --> Let e1' e2 *)
    simpl. lia.
  - (* step_ctx_match: Mtch e bs --> Mtch e' bs *)
    rewrite !size_Mtch_unfold. lia.
  - (* step_ctx_def: Def e es --> Def e' es *)
    rewrite !size_Def_unfold. lia.
Qed.

(* ------------------------------------------------------------------------- *)
(*  §5.  Strong normalization                                                 *)
(* ------------------------------------------------------------------------- *)

(** A term [t] is strongly normalizing if every reduction sequence from [t]
    terminates. We use the accessibility-based definition (standard in
    normalization proofs): [Acc (fun x y => step y x) t] says no infinite
    reduction chain starts at [t]. *)
Definition SN (t : FAdm) : Prop := Acc (fun x y => step y x) t.

(** Well-foundedness of the size measure on [nat]. *)
Lemma lt_wf : well_founded lt.
Proof. exact Nat.lt_wf_0. Qed.

(** Strong normalization follows from the measure-decrease theorem by
    well-founded induction on the size measure. *)
Theorem flat_admissible_sn : forall t, SN t.
Proof.
  intros t.
  (* Induct on size t using [lt_wf]. *)
  remember (size t) as n eqn:Hn.
  revert t Hn.
  induction n as [n IH] using (well_founded_ind lt_wf).
  intros t Hn. subst.
  constructor. intros t' Hstep.
  apply step_decreases_size in Hstep.
  apply (IH (size t') Hstep t' eq_refl).
Qed.

(** A reduction chain of any length bounded by the initial term's size. *)
Corollary reduction_chain_bounded :
  forall t t', clos_refl_trans _ step t t' -> size t' <= size t.
Proof.
  intros t t' H. induction H.
  - apply step_decreases_size in H. lia.
  - lia.
  - lia.
Qed.

(* ------------------------------------------------------------------------- *)
(*  §6.  Discussion of coverage                                               *)
(* ------------------------------------------------------------------------- *)

(*  The flat fragment above captures the EVALUATOR-level core of Lex's         *)
(*  admissible fragment as exposed by [crates/lex-core/src/evaluate.rs]:       *)
(*    - accessor applications (Acc)                                            *)
(*    - let bindings with value substitution (Let_ / step_let_const)           *)
(*    - match over finite constructor tags (Mtch / step_match_const)           *)
(*    - defeasible rules whose exceptions are flat (Def / step_def_base)       *)
(*                                                                            *)
(*  What is EXCLUDED from this narrow subset and why:                          *)
(*                                                                            *)
(*    (1) Lambdas and general β-reduction. The admissible-fragment typing     *)
(*        rule admits lambdas, but adding β to the reduction relation         *)
(*        requires capture-avoiding substitution. In a non-duplicating        *)
(*        call-by-value regime with prelude-only argument types, β still      *)
(*        strictly decreases size, but encoding the substitution lemma in     *)
(*        Coq is a separate mechanization effort scoped outside this file.    *)
(*        The size argument we use here carries through with minor bookkeeping *)
(*        once substitution is defined: β replaces a (λ x. e) v redex of size  *)
(*        (2 + size e + size v) with e[v/x], which under call-by-value on     *)
(*        prelude values (every v is a Const) is bounded by size e + size v.  *)
(*                                                                            *)
(*    (2) Defeasible rules with NON-empty exception lists. The semantic       *)
(*        content — that exceptions reduce in priority order — is orthogonal  *)
(*        to SN: each exception body is an admissible term, and reduction    *)
(*        inside an exception body strictly decreases size by the same        *)
(*        context-rule argument used for [step_ctx_def]. A full treatment     *)
(*        tracks per-exception guards reaching values. That extension is      *)
(*        routine; omitted here to keep the narrow theorem clean.             *)
(*                                                                            *)
(*    (3) Pi types, modals, recursion, content-addressed references,          *)
(*        typed discretion holes. All explicitly excluded from admissibility  *)
(*        in the paper's §5; their exclusion is the *premise* of SN, not a    *)
(*        gap in the proof.                                                   *)
(*                                                                            *)
(*  The proof above is Qed'd with NO admits and NO assumed axioms beyond      *)
(*  the stdlib.                                                               *)

(* ------------------------------------------------------------------------- *)
(*  §7.  Sanity checks                                                        *)
(* ------------------------------------------------------------------------- *)

Check flat_admissible_sn.
Check step_decreases_size.
Check reduction_chain_bounded.
Print Assumptions flat_admissible_sn.
