From Stdlib Require Import Lists.List Arith.Arith Lia.
From Lex Require Import Syntax DeBruijn Typing.
Import ListNotations.

(** Constructor arguments are in source order: the rightmost argument
    occupies De Bruijn position zero in the branch body. Each substitution
    removes one binder. Protect earlier inserted free variables from later
    substitutions before opening the remaining binders. *)
Fixpoint protect_args (args : list Term) : list Term :=
  match args with
  | [] => []
  | a :: rest => shift 0 (List.length rest) a :: protect_args rest
  end.

Definition instantiate_args (args : list Term) (body : Term) : Term :=
  subst_args (protect_args (rev args)) body.

Lemma protect_args_length : forall args,
  List.length (protect_args args) = List.length args.
Proof. induction args; simpl; congruence. Qed.

Lemma protected_args_shift : forall args c d,
  shift_args_at c d (protect_args args) =
  protect_args (map (shift c d) args).
Proof.
  induction args as [|a rest IH]; intros c d; simpl.
  - reflexivity.
  - rewrite protect_args_length, map_length.
    rewrite shift_shift_swap_0_arity, IH. reflexivity.
Qed.

Theorem instantiate_args_shift : forall args body c d,
  shift c d (instantiate_args args body) =
  instantiate_args (map (shift c d) args)
    (shift (c + List.length args) d body).
Proof.
  intros args body c d. unfold instantiate_args.
  rewrite shift_subst_args_commute.
  rewrite protect_args_length, rev_length, protected_args_shift.
  rewrite map_rev. reflexivity.
Qed.

Theorem instantiate_args_empty : forall body,
  instantiate_args [] body = body.
Proof. reflexivity. Qed.

Theorem instantiate_args_single : forall a body,
  instantiate_args [a] body = subst 0 a body.
Proof.
  intros. unfold instantiate_args; simpl.
  rewrite shift_zero. reflexivity.
Qed.

(** These are raw syntax equalities. They claim neither typing nor
    operational preservation for the entire captured relation. *)
Example two_arguments_respect_innermost_binder :
  instantiate_args [IntLit 1; IntLit 2] (Var 0) = IntLit 2.
Proof. reflexivity. Qed.

Example two_arguments_respect_outer_binder :
  instantiate_args [IntLit 1; IntLit 2] (Var 1) = IntLit 1.
Proof. reflexivity. Qed.

Example two_open_arguments_preserve_last_argument :
  instantiate_args [Var 0; Var 1] (Var 0) = Var 1.
Proof. reflexivity. Qed.

Example two_open_arguments_preserve_first_argument :
  instantiate_args [Var 0; Var 1] (Var 1) = Var 0.
Proof. reflexivity. Qed.

Example captured_fold_reverses_constructor_position :
  subst_args [IntLit 1; IntLit 2] (Var 0) = IntLit 1.
Proof. reflexivity. Qed.

Example captured_fold_captures_an_inserted_variable :
  subst_args [Var 0; Var 1] (Var 0) = Var 1 /\
  subst_args [Var 0; Var 1] (Var 1) = Var 1.
Proof. split; reflexivity. Qed.

Example captured_uniform_shift_equivariance_fails :
  shift 0 1 (subst_args [Var 0; Var 1] (Var 0)) <>
  subst_args (map (shift 0 1) [Var 0; Var 1])
    (shift (0 + List.length [Var 0; Var 1]) 1 (Var 0)).
Proof. discriminate. Qed.

Print Assumptions instantiate_args_shift.
Print Assumptions instantiate_args_empty.
Print Assumptions instantiate_args_single.
Print Assumptions two_arguments_respect_innermost_binder.
Print Assumptions two_arguments_respect_outer_binder.
Print Assumptions two_open_arguments_preserve_last_argument.
Print Assumptions two_open_arguments_preserve_first_argument.
Print Assumptions captured_fold_reverses_constructor_position.
Print Assumptions captured_fold_captures_an_inserted_variable.
Print Assumptions captured_uniform_shift_equivariance_fails.
