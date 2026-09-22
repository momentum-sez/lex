From Stdlib Require Import Lists.List Arith.Arith Lia Strings.String.
From Lex Require Import Syntax DeBruijn Typing.
From P04Substitution Require Import SimultaneousArgs.
Import ListNotations.
Open Scope string_scope.

Example unlifted_body_replacement_is_false :
  subst 0 (Var 0) (instantiate_args [IntLit 1] (Var 1)) <>
  instantiate_args [subst 0 (Var 0) (IntLit 1)]
    (subst 1 (Var 0) (Var 1)).
Proof. discriminate. Qed.

Ltac decide_nat :=
  repeat match goal with
  | |- context [Nat.eqb ?x ?y] => destruct (Nat.eqb_spec x y)
  | |- context [Nat.ltb ?x ?y] => destruct (Nat.ltb_spec x y)
  | |- context [Nat.leb ?x ?y] => destruct (Nat.leb_spec x y)
  end; try congruence; try lia.

Lemma subst_shift_cancel : forall t j r,
  subst j r (shift j 1 t) = t
with subst_shift_cancel_branch : forall b j r,
  subst_branch j r (shift_branch j 1 b) = b
with subst_shift_cancel_exception : forall e j r,
  subst_exception j r (shift_exception j 1 e) = e.
Proof.
  - intros t j r. destruct t; simpl; try reflexivity;
      try (rewrite !subst_shift_cancel; reflexivity).
    + decide_nat; simpl; decide_nat; f_equal; lia.
    + f_equal. induction l; simpl; [reflexivity|].
      rewrite subst_shift_cancel, IHl. reflexivity.
    + rewrite !subst_shift_cancel. f_equal.
      induction l; simpl; [reflexivity|].
      rewrite subst_shift_cancel_branch, IHl. reflexivity.
    + rewrite !subst_shift_cancel. f_equal.
      induction l; simpl; [reflexivity|].
      rewrite subst_shift_cancel_exception, IHl. reflexivity.
  - intros [pat body] j r. simpl. rewrite subst_shift_cancel. reflexivity.
  - intros [guard body prio] j r. simpl.
    rewrite !subst_shift_cancel. reflexivity.
Qed.

Lemma shift_subst_below : forall t s i c d,
  c <= i ->
  shift c d (subst i s t) =
  subst (i+d) (shift c d s) (shift c d t)
with shift_subst_below_branch : forall b s i c d,
  c <= i ->
  shift_branch c d (subst_branch i s b) =
  subst_branch (i+d) (shift c d s) (shift_branch c d b)
with shift_subst_below_exception : forall e s i c d,
  c <= i ->
  shift_exception c d (subst_exception i s e) =
  subst_exception (i+d) (shift c d s) (shift_exception c d e).
Proof.
  - intros t s i c d Hci. destruct t; simpl; try reflexivity;
      try (rewrite !shift_subst_below by lia; reflexivity);
      try (rewrite !shift_subst_below by lia;
           rewrite shift_shift_swap_0_1; reflexivity).
    + apply shift_subst_commute_ws_at_depth_var with (k:=S (n+i)); lia.
    + f_equal. induction l; simpl; [reflexivity|].
      rewrite shift_subst_below by lia. rewrite IHl. reflexivity.
    + rewrite !shift_subst_below by lia. f_equal.
      induction l; simpl; [reflexivity|].
      rewrite shift_subst_below_branch by lia. rewrite IHl. reflexivity.
    + rewrite !shift_subst_below by lia. f_equal.
      induction l; simpl; [reflexivity|].
      rewrite shift_subst_below_exception by lia. rewrite IHl. reflexivity.
  - intros [pat body] s i c d Hci. simpl.
    rewrite shift_subst_below by lia.
    rewrite shift_shift_swap_0_arity. f_equal. f_equal. lia.
  - intros [guard body prio] s i c d Hci. simpl.
    rewrite !shift_subst_below by lia. reflexivity.
Qed.

Lemma subst_composition_var : forall n r s i j,
  j <= i ->
  subst i s (subst j r (Var n)) =
  subst j (subst i s r) (subst (S i) (shift j 1 s) (Var n)).
Proof.
  intros n r s i j Hji. simpl.
  decide_nat; simpl; decide_nat;
    try rewrite subst_shift_cancel; try reflexivity;
    f_equal; lia.
Qed.

Lemma subst_composition : forall t r s i j,
  j <= i ->
  subst i s (subst j r t) =
  subst j (subst i s r) (subst (S i) (shift j 1 s) t)
with subst_composition_branch : forall b r s i j,
  j <= i ->
  subst_branch i s (subst_branch j r b) =
  subst_branch j (subst i s r)
    (subst_branch (S i) (shift j 1 s) b)
with subst_composition_exception : forall e r s i j,
  j <= i ->
  subst_exception i s (subst_exception j r e) =
  subst_exception j (subst i s r)
    (subst_exception (S i) (shift j 1 s) e).
Proof.
  - intros t r s i j Hji. destruct t; simpl; try reflexivity;
      try solve [f_equal; apply subst_composition; lia];
      try solve [f_equal;
        first [apply subst_composition; lia |
          rewrite (subst_composition _ _ _ (S i) (S j)) by lia;
          rewrite shift_shift_swap_0_1;
          rewrite (shift_subst_below r s i 0 1) by lia;
          replace (i+1) with (S i) by lia; reflexivity]].
    + apply subst_composition_var. exact Hji.
    + f_equal. induction l; simpl; [reflexivity|].
      rewrite (subst_composition a r s i j) by lia. rewrite IHl. reflexivity.
    + f_equal; try (apply subst_composition; lia).
      induction l; simpl; [reflexivity|].
      rewrite (subst_composition_branch a r s i j) by lia. rewrite IHl. reflexivity.
    + f_equal; try (apply subst_composition; lia).
      induction l; simpl; [reflexivity|].
      rewrite (subst_composition_exception a r s i j) by lia. rewrite IHl. reflexivity.
  - intros [pat body] r s i j Hji. simpl.
    rewrite (subst_composition body) by lia.
    rewrite shift_shift_swap_0_arity.
    rewrite (shift_subst_below r s i 0 _) by lia.
    replace (S i + match pat with PCtor _ n => n | PWild => 0 end)
      with (S (i + match pat with PCtor _ n => n | PWild => 0 end)) by lia.
    reflexivity.
  - intros [guard body prio] r s i j Hji. simpl.
    f_equal; apply subst_composition; lia.
Qed.

Lemma protected_args_subst : forall args body k u,
  subst k u (subst_args (protect_args args) body) =
  subst_args (protect_args (map (subst k u) args))
    (subst (k + List.length args) (shift 0 (List.length args) u) body).
Proof.
  induction args as [|a rest IH]; intros body k u; simpl.
  - rewrite Nat.add_0_r, shift_zero. reflexivity.
  - rewrite IH.
    rewrite (subst_composition body) by lia.
    rewrite <- (shift_subst_below a u k 0 (List.length rest)) by lia.
    rewrite shift_shift, length_map.
    replace (List.length rest + 1) with (S (List.length rest)) by lia.
    replace (S (k + List.length rest)) with (k + S (List.length rest)) by lia.
    reflexivity.
Qed.

(** The replacement is lifted through every constructor binder.
    There is no scope, typing, value, or closedness premise. *)
Theorem instantiate_args_subst : forall args body k u,
  subst k u (instantiate_args args body) =
  instantiate_args (map (subst k u) args)
    (subst (k + List.length args) (shift 0 (List.length args) u) body).
Proof.
  intros args body k u. unfold instantiate_args.
  rewrite protected_args_subst, length_rev, map_rev. reflexivity.
Qed.

Corollary subst_beta_commute : forall body a k u,
  subst k u (subst 0 a body) =
  subst 0 (subst k u a) (subst (S k) (shift 0 1 u) body).
Proof.
  intros. apply subst_composition. lia.
Qed.

Example substitute_open_argument_and_external_variable :
  subst 0 (Var 2)
    (instantiate_args [Var 0; Var 1] (Pair (Var 1) (Var 2))) =
  Pair (Var 2) (Var 2).
Proof. reflexivity. Qed.

Example substitute_through_nested_lambda :
  subst 0 (Var 2)
    (instantiate_args [Var 0; Var 1]
      (Lambda (Var 2) (Pair (Var 1) (Pair (Var 2) (Var 3))))) =
  Lambda (Var 2) (Pair (Var 1) (Pair (Var 3) (Var 3))).
Proof. reflexivity. Qed.

Example substitute_through_nested_constructor_branch :
  subst 0 (Var 2)
    (instantiate_args [Var 0; Var 1]
      (Match (Var 2) (Var 2)
        [MkBranch (PCtor "nested" 2)
          (Pair (Var 2) (Pair (Var 3) (Var 4)))])) =
  Match (Var 2) (Var 2)
    [MkBranch (PCtor "nested" 2)
      (Pair (Var 2) (Pair (Var 4) (Var 4)))].
Proof. reflexivity. Qed.

Print Assumptions unlifted_body_replacement_is_false.
Print Assumptions subst_shift_cancel.
Print Assumptions shift_subst_below.
Print Assumptions subst_composition.
Print Assumptions protected_args_subst.
Print Assumptions instantiate_args_subst.
Print Assumptions subst_beta_commute.
Print Assumptions substitute_open_argument_and_external_variable.
Print Assumptions substitute_through_nested_lambda.
Print Assumptions substitute_through_nested_constructor_branch.
