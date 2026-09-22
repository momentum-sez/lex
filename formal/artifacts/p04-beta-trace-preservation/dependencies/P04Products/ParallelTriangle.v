From Stdlib Require Import Lists.List Strings.String Arith.Arith Bool.Bool Lia.
From Lex Require Import Syntax DeBruijn Typing.
From P04Substitution Require Import SimultaneousArgs.
From P04ArgsSubstitution Require Import ArgsSubstitution.
From P04Source Require Import TypeReduction.
From P04Products Require Import Parallel.
Import ListNotations.

Fixpoint dev (t : Term) : Term :=
  match t with
  | Var n => Var n | TSort s => TSort s | Constant s => Constant s
  | ContentRef s => ContentRef s | IntLit n => IntLit n
  | RatLit n d => RatLit n d | StringLit s => StringLit s | AxiomUse s => AxiomUse s
  | Pair a b => Pair (dev a) (dev b)
  | Proj f a => Proj f (dev a)
  | App a b => match a with
      | Lambda dom body => subst 0 (dev b) (dev body)
      | _ => App (dev a) (dev b) end
  | InductiveIntro c args => InductiveIntro c (map dev args)
  | SanctionsDominance a => SanctionsDominance (dev a)
  | DefeatElim a => DefeatElim (dev a)
  | Lift0 a => Lift0 (dev a)
  | Derive1 a b => Derive1 (dev a) (dev b)
  | Lambda a b => Lambda (dev a) (dev b)
  | Pi a e b => Pi (dev a) e (dev b)
  | Sigma a b => Sigma (dev a) (dev b)
  | Annot a b => dev a
  | Let a b c => subst 0 (dev b) (dev c)
  | Match s r bs =>
      let dbs := map (fun b => match b with MkBranch p e => MkBranch p (dev e) end) bs in
      match bs with
      | [] => Match (dev s) (dev r) []
      | MkBranch PWild body :: rest => dev body
      | MkBranch (PCtor name n) body :: rest =>
          match s with
          | InductiveIntro c args =>
              if branch_head_matches s name n then instantiate_args (map dev args) (dev body)
              else match rest with
                   | [] => Match (dev s) (dev r) dbs
                   | _ :: _ => Match (dev s) (dev r)
                       (map (fun b => match b with MkBranch p e => MkBranch p (dev e) end) rest)
                   end
          | _ => Match (dev s) (dev r) dbs
          end
      end
  | Rec a b => Rec (dev a) (dev b)
  | ModalAt a b => ModalAt (dev a) (dev b)
  | ModalEventually a b => ModalEventually (dev a) (dev b)
  | ModalAlways a b c => ModalAlways (dev a) (dev b) (dev c)
  | ModalIntro s a => ModalIntro s (dev a)
  | ModalElim s s' a b => ModalElim s s' (dev a) (dev b)
  | Defeasible a b es =>
      match es with
      | [] => dev b
      | _ :: _ => Defeasible (dev a) (dev b)
          (map (fun e => match e with MkException g b p => MkException (dev g) (dev b) p end) es)
      end
  | Hole a => Hole (dev a)
  | HoleFill a b => HoleFill (dev a) (dev b)
  | PrincipleBalance a b => PrincipleBalance (dev a) (dev b)
  | Unlock a b => Unlock (dev a) (dev b)
  end.
Definition devs := map dev.
Definition devbs := map (fun b => match b with MkBranch p e => MkBranch p (dev e) end).
Definition deves := map (fun e => match e with MkException g b p => MkException (dev g) (dev b) p end).

Lemma dev_app_cong : forall a a' b b',
  par a a' -> par a' (dev a) -> par b' (dev b) ->
  par (App a' b') (dev (App a b)).
Proof.
  intros a a' b b' Haa Hda Hdb.
  destruct a; simpl; try (apply par_App; assumption).
  inversion Haa; subst. inversion Hda; subst.
  apply par_beta; assumption.
Qed.

Lemma dev_defeasible_cong : forall a a' b b' es es',
  par a' (dev a) -> par b' (dev b) ->
  pares es es' -> pares es' (deves es) ->
  par (Defeasible a' b' es') (dev (Defeasible a b es)).
Proof.
  intros a a' b b' es es' Ha Hb Hs Hds.
  destruct es as [|[g e p] rest]; simpl.
  - inversion Hs; subst. now apply par_defeasible_empty.
  - apply par_Defeasible; assumption.
Qed.

Lemma dev_match_cong : forall s s' r r' bs bs',
  par s s' -> par s' (dev s) -> par r' (dev r) ->
  parbs bs bs' -> parbs bs' (devbs bs) ->
  par (Match s' r' bs') (dev (Match s r bs)).
Proof.
  intros s s' r r' bs bs' Hs Hds Hr Hb Hdb.
  destruct bs as [|[pat body] rest].
  - inversion Hb; subst. simpl. apply par_Match; auto; constructor.
  - inversion Hb; subst. unfold devbs in Hdb; simpl in Hdb.
    inversion Hdb; subst.
    destruct pat as [name n|].
    2: { simpl. apply par_match_wild; assumption. }
    destruct s; simpl; try (apply par_Match; auto; constructor; assumption).
    destruct (String.eqb name s && Nat.eqb n (List.length l)) eqn:Hmatch.
    + inversion Hs; subst. simpl in Hds. inversion Hds; subst.
      unfold branch_head_matches in Hmatch.
      apply andb_true_iff in Hmatch as [Hname Hlen].
      apply Nat.eqb_eq in Hlen.
      apply par_match_ctor_fire; try assumption.
      * rewrite String.eqb_sym; exact Hname.
      * pose proof (pars_length _ _ H5). congruence.
    + destruct rest as [|br rest].
      * apply par_Match; auto; constructor; assumption.
      * inversion Hs; subst. simpl in Hds. inversion Hds; subst.
        eapply par_match_ctor_skip; try eassumption.
        -- unfold branch_head_matches in *. rewrite <- (pars_length _ _ H5). exact Hmatch.
        -- intro E. subst. inversion H4.
Qed.

From P04Products Require Import ParallelSubstitution.

Theorem parallel_triangle_mutual :
  (forall t u, par t u -> par u (dev t)) /\
  (forall ts us, pars ts us -> pars us (devs ts)) /\
  (forall bs cs, parbs bs cs -> parbs cs (devbs bs)) /\
  (forall es fs, pares es fs -> pares fs (deves es)).
Proof.
  apply parallel_ind; intros; try solve [simpl; constructor; assumption];
    try solve [simpl; constructor].
  - eapply dev_app_cong; eassumption.
  - eapply dev_match_cong; eassumption.
  - eapply dev_defeasible_cong; eassumption.
  - simpl. apply par_subst; assumption.
  - simpl. apply par_subst; assumption.
  - assumption.
  - assumption.
  - assumption.
  - simpl. unfold branch_head_matches. rewrite String.eqb_sym, e, e0, Nat.eqb_refl.
    apply par_instantiate_args; assumption.
  - simpl. unfold branch_head_matches in e. rewrite e.
    destruct rest; [contradiction|].
    apply par_Match; [apply par_InductiveIntro | | ]; assumption.
Qed.

Theorem parallel_triangle : forall t u, par t u -> par u (dev t).
Proof. exact (proj1 parallel_triangle_mutual). Qed.

Theorem parallel_diamond : forall t u v, par t u -> par t v ->
  exists w, par u w /\ par v w.
Proof.
  intros t u v Hu Hv. exists (dev t). split; now apply parallel_triangle.
Qed.

Print Assumptions parallel_triangle.
Print Assumptions parallel_diamond.
