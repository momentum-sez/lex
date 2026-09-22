From Stdlib Require Import Lists.List Strings.String Arith.Arith Lia.
From Lex Require Import Syntax DeBruijn Typing.
From P04Substitution Require Import SimultaneousArgs.
From P04ArgsSubstitution Require Import ArgsSubstitution.
From P04Source Require Import TypeReduction.
Import ListNotations.

(** Actual-syntax parallel contraction. Static syntax, including effect rows,
    constructor names and branch patterns, is preserved. No normalization or
    confluence premise is included in this definition. *)
Inductive par : Term -> Term -> Prop :=
| par_Var : forall (x : nat), par (Var x) (Var x)
| par_TSort : forall (x : Sort), par (TSort x) (TSort x)
| par_Constant : forall (x : string), par (Constant x) (Constant x)
| par_ContentRef : forall (x : string), par (ContentRef x) (ContentRef x)
| par_IntLit : forall (x : nat), par (IntLit x) (IntLit x)
| par_RatLit : forall (x y : nat), par (RatLit x y) (RatLit x y)
| par_StringLit : forall (x : string), par (StringLit x) (StringLit x)
| par_AxiomUse : forall (x : string), par (AxiomUse x) (AxiomUse x)
| par_Pair : forall  (a b a' b' : Term), par a a' -> par b b' -> par (Pair a b) (Pair a' b')
| par_Proj : forall (f : bool) (a a' : Term), par a a' -> par (Proj f a) (Proj f a')
| par_App : forall  (a b a' b' : Term), par a a' -> par b b' -> par (App a b) (App a' b')
| par_SanctionsDominance : forall  (a a' : Term), par a a' -> par (SanctionsDominance a) (SanctionsDominance a')
| par_DefeatElim : forall  (a a' : Term), par a a' -> par (DefeatElim a) (DefeatElim a')
| par_Lift0 : forall  (a a' : Term), par a a' -> par (Lift0 a) (Lift0 a')
| par_Derive1 : forall  (a b a' b' : Term), par a a' -> par b b' -> par (Derive1 a b) (Derive1 a' b')
| par_Lambda : forall  (a b a' b' : Term), par a a' -> par b b' -> par (Lambda a b) (Lambda a' b')
| par_Pi : forall (eff : option EffectRow) (a b a' b' : Term), par a a' -> par b b' -> par (Pi a eff b) (Pi a' eff b')
| par_Sigma : forall  (a b a' b' : Term), par a a' -> par b b' -> par (Sigma a b) (Sigma a' b')
| par_Annot : forall  (a b a' b' : Term), par a a' -> par b b' -> par (Annot a b) (Annot a' b')
| par_Let : forall  (a b c a' b' c' : Term), par a a' -> par b b' -> par c c' -> par (Let a b c) (Let a' b' c')
| par_Rec : forall  (a b a' b' : Term), par a a' -> par b b' -> par (Rec a b) (Rec a' b')
| par_ModalAt : forall  (a b a' b' : Term), par a a' -> par b b' -> par (ModalAt a b) (ModalAt a' b')
| par_ModalEventually : forall  (a b a' b' : Term), par a a' -> par b b' -> par (ModalEventually a b) (ModalEventually a' b')
| par_ModalAlways : forall  (a b c a' b' c' : Term), par a a' -> par b b' -> par c c' -> par (ModalAlways a b c) (ModalAlways a' b' c')
| par_ModalIntro : forall (tr : string) (a a' : Term), par a a' -> par (ModalIntro tr a) (ModalIntro tr a')
| par_ModalElim : forall (t1 t2 : string) (a b a' b' : Term), par a a' -> par b b' -> par (ModalElim t1 t2 a b) (ModalElim t1 t2 a' b')
| par_Hole : forall  (a a' : Term), par a a' -> par (Hole a) (Hole a')
| par_HoleFill : forall  (a b a' b' : Term), par a a' -> par b b' -> par (HoleFill a b) (HoleFill a' b')
| par_PrincipleBalance : forall  (a b a' b' : Term), par a a' -> par b b' -> par (PrincipleBalance a b) (PrincipleBalance a' b')
| par_Unlock : forall  (a b a' b' : Term), par a a' -> par b b' -> par (Unlock a b) (Unlock a' b')
| par_InductiveIntro : forall name args args',
    pars args args' -> par (InductiveIntro name args) (InductiveIntro name args')
| par_Match : forall s s' r r' bs bs',
    par s s' -> par r r' -> parbs bs bs' ->
    par (Match s r bs) (Match s' r' bs')
| par_Defeasible : forall ty ty' b b' es es',
    par ty ty' -> par b b' -> pares es es' ->
    par (Defeasible ty b es) (Defeasible ty' b' es')
| par_beta : forall dom body body' arg arg',
    par body body' -> par arg arg' ->
    par (App (Lambda dom body) arg) (subst 0 arg' body')
| par_zeta : forall ty val val' body body',
    par val val' -> par body body' ->
    par (Let ty val body) (subst 0 val' body')
| par_annot : forall e e' ty,
    par e e' -> par (Annot e ty) e'
| par_defeasible_empty : forall ty b b',
    par b b' -> par (Defeasible ty b []) b'
| par_match_wild : forall scrut ret body body' rest,
    par body body' -> par (Match scrut ret (MkBranch PWild body :: rest)) body'
| par_match_ctor_fire : forall name name' args args' ret body body' n rest,
    String.eqb name name' = true -> List.length args = n ->
    pars args args' -> par body body' ->
    par (Match (InductiveIntro name args) ret (MkBranch (PCtor name' n) body :: rest))
        (instantiate_args args' body')
| par_match_ctor_skip : forall name name' args args' ret ret' body n rest rest',
    branch_head_matches (InductiveIntro name args) name' n = false -> rest <> [] ->
    pars args args' -> par ret ret' -> parbs rest rest' ->
    par (Match (InductiveIntro name args) ret (MkBranch (PCtor name' n) body :: rest))
        (Match (InductiveIntro name args') ret' rest')
with pars : list Term -> list Term -> Prop :=
| pars_nil : pars [] []
| pars_cons : forall a a' rest rest', par a a' -> pars rest rest' -> pars (a :: rest) (a' :: rest')
with parbs : list Branch -> list Branch -> Prop :=
| parbs_nil : parbs [] []
| parbs_cons : forall pat b b' rest rest', par b b' -> parbs rest rest' ->
    parbs (MkBranch pat b :: rest) (MkBranch pat b' :: rest')
with pares : list Exception -> list Exception -> Prop :=
| pares_nil : pares [] []
| pares_cons : forall g g' b b' prio rest rest', par g g' -> par b b' -> pares rest rest' ->
    pares (MkException g b prio :: rest) (MkException g' b' prio :: rest').

Scheme par_ind' := Induction for par Sort Prop
with pars_ind' := Induction for pars Sort Prop
with parbs_ind' := Induction for parbs Sort Prop
with pares_ind' := Induction for pares Sort Prop.
Combined Scheme parallel_ind from par_ind', pars_ind', parbs_ind', pares_ind'.

Lemma pars_length : forall xs ys, pars xs ys -> List.length xs = List.length ys.
Proof. intros xs ys H; induction H; simpl; congruence. Qed.
Lemma parbs_length : forall xs ys, parbs xs ys -> List.length xs = List.length ys.
Proof. intros xs ys H; induction H; simpl; congruence. Qed.

Lemma par_refl : forall t, par t t.
Proof.
  fix IH 1. intro t; destruct t; try solve [constructor; auto].
  - apply par_InductiveIntro. induction l; constructor; auto.
  - apply par_Match; try apply IH. induction l as [|[pat b] rest Hr]; [apply parbs_nil | apply parbs_cons; auto].
  - apply par_Defeasible; try apply IH. induction l as [|[g b prio] rest Hr]; [apply pares_nil | apply pares_cons; auto].
Qed.
