(** * Defeasibility priority evaluator (Qed-closed) *)

(** Mechanizes the defeasibility evaluator of lex.tex:
    given a base verdict and a list of priority-tagged exceptions,
    the evaluator selects the highest-priority fired exception;
    if none fires, the base verdict stands.

    Priorities are natural numbers with higher numeric priority
    taking precedence (lex specialis). *)

Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Import ListNotations.

Set Implicit Arguments.

(** Reuse the verdict lattice. *)
Require Import Lex.VerdictHeyting.

(** An exception is a triple of a guard (boolean result), a body
    (the verdict to emit if the guard fires), and a numeric
    priority. *)
Record exception_triple : Type := mk_exc {
  guard : bool;
  body : verdict;
  priority : nat
}.

Definition exceptions : Type := list exception_triple.

(** Select the highest-priority fired exception. *)
Fixpoint best_fired (xs : exceptions) : option exception_triple :=
  match xs with
  | [] => None
  | x :: rest =>
      match best_fired rest with
      | None => if guard x then Some x else None
      | Some y =>
          if guard x then
            if Nat.ltb (priority y) (priority x)
            then Some x
            else Some y
          else Some y
      end
  end.

(** Evaluator: base verdict overridden by best-fired exception. *)
Definition eval_defeasible (base : verdict) (xs : exceptions) : verdict :=
  match best_fired xs with
  | None => base
  | Some x => body x
  end.

(** Sanity: no exceptions fires -> base. *)
Lemma eval_no_exceptions : forall base, eval_defeasible base [] = base.
Proof. reflexivity. Qed.

(** Sanity: a single fired exception with empty rest overrides. *)
Lemma eval_single_fired : forall base b v p,
  b = true ->
  eval_defeasible base [mk_exc b v p] = v.
Proof.
  intros base b v p Hb. unfold eval_defeasible. simpl.
  rewrite Hb. reflexivity.
Qed.

(** Sanity: a single non-fired exception leaves base. *)
Lemma eval_single_unfired : forall base v p,
  eval_defeasible base [mk_exc false v p] = base.
Proof.
  intros base v p. unfold eval_defeasible. simpl. reflexivity.
Qed.

(** Highest-priority-wins: if two exceptions both fire and one has
    strictly higher priority, the higher-priority body is the
    result of [best_fired]. *)
Lemma best_two_fired_high_wins : forall b1 b2 v1 v2 p1 p2,
  b1 = true -> b2 = true -> p1 < p2 ->
  best_fired [mk_exc b1 v1 p1; mk_exc b2 v2 p2] = Some (mk_exc b2 v2 p2).
Proof.
  intros. subst. simpl.
  destruct (Nat.ltb p2 p1) eqn:Hlt.
  - apply Nat.ltb_lt in Hlt. lia.
  - reflexivity.
Qed.

Lemma best_two_fired_low_first_wins : forall b1 b2 v1 v2 p1 p2,
  b1 = true -> b2 = true -> p2 < p1 ->
  best_fired [mk_exc b1 v1 p1; mk_exc b2 v2 p2] = Some (mk_exc b1 v1 p1).
Proof.
  intros. subst. simpl.
  destruct (Nat.ltb p2 p1) eqn:Hlt.
  - reflexivity.
  - apply Nat.ltb_nlt in Hlt. lia.
Qed.

(** Priority monotonicity: adding a non-firing exception doesn't
    change the result. *)
Lemma add_unfired : forall base xs v p,
  eval_defeasible base (mk_exc false v p :: xs) =
  eval_defeasible base xs.
Proof.
  intros base xs v p. unfold eval_defeasible. simpl.
  destruct (best_fired xs); reflexivity.
Qed.

(** Helper: best_fired returns an element of the input list. *)
Lemma best_fired_in : forall xs y,
  best_fired xs = Some y -> In y xs.
Proof.
  induction xs as [|z zs IH]; intros y H; simpl in *.
  - discriminate.
  - destruct (best_fired zs) as [u|] eqn:Hzs.
    + destruct (guard z) eqn:Hgz.
      * destruct (Nat.ltb (priority u) (priority z)) eqn:Hlt;
          inversion H; subst.
        -- left. reflexivity.
        -- right. apply IH. reflexivity.
      * inversion H; subst. right. apply IH. reflexivity.
    + destruct (guard z) eqn:Hgz.
      * inversion H; subst. left. reflexivity.
      * discriminate.
Qed.

(** Helper: best_fired returns an element with guard = true. *)
Lemma best_fired_guard : forall xs y,
  best_fired xs = Some y -> guard y = true.
Proof.
  induction xs as [|z zs IH]; intros y H; simpl in *.
  - discriminate.
  - destruct (best_fired zs) as [u|] eqn:Hzs.
    + destruct (guard z) eqn:Hgz.
      * destruct (Nat.ltb (priority u) (priority z)) eqn:Hlt;
          inversion H; subst.
        -- exact Hgz.
        -- apply IH. reflexivity.
      * inversion H; subst. apply IH. reflexivity.
    + destruct (guard z) eqn:Hgz.
      * inversion H; subst. exact Hgz.
      * discriminate.
Qed.

(** Correctness: result of eval_defeasible is either the base
    verdict or the body of some exception with guard = true. *)
Theorem eval_sound :
  forall base xs,
    eval_defeasible base xs = base \/
    exists x, In x xs /\ guard x = true /\
              body x = eval_defeasible base xs.
Proof.
  intros base xs. unfold eval_defeasible.
  destruct (best_fired xs) as [y|] eqn:Hbest.
  - right. exists y. repeat split.
    + apply best_fired_in. exact Hbest.
    + apply best_fired_guard with (xs := xs). exact Hbest.
  - left. reflexivity.
Qed.

(** Adding a strictly lower-priority fired exception is inert
    relative to an existing higher-priority best_fired: since
    the best_fired function selects the maximal priority, a
    new exception at lower priority cannot displace it.  This
    is the "defeasibility stability under lower-priority
    extension" property that makes the paper's
    specialibet-generalibus override principle monotonic. *)
Theorem eval_stable_under_lower_priority :
  forall base xs v p_new,
    (exists y, best_fired xs = Some y /\ priority y > p_new) ->
    eval_defeasible base (mk_exc true v p_new :: xs) =
    eval_defeasible base xs.
Proof.
  intros base xs v p_new [y [Hbest Hlt]].
  unfold eval_defeasible.
  assert (Hbf : best_fired (mk_exc true v p_new :: xs) = Some y).
  { simpl. rewrite Hbest.
    assert (Hge : priority y >= p_new) by lia.
    destruct (Nat.ltb (priority y) p_new) eqn:Hltb.
    - apply Nat.ltb_lt in Hltb. lia.
    - reflexivity. }
  rewrite Hbf. rewrite Hbest. reflexivity.
Qed.

(** Dually: a fresh exception that fires with strictly higher
    priority than the existing best replaces the result. *)
Theorem eval_higher_priority_overrides :
  forall base xs v p_new,
    (forall y, best_fired xs = Some y -> priority y < p_new) ->
    eval_defeasible base (mk_exc true v p_new :: xs) = v.
Proof.
  intros base xs v p_new Hlower.
  unfold eval_defeasible.
  assert (Hbf : best_fired (mk_exc true v p_new :: xs)
             = Some (mk_exc true v p_new)).
  { simpl. destruct (best_fired xs) as [y|] eqn:Hbest.
    - specialize (Hlower y eq_refl).
      assert (Hltb : Nat.ltb (priority y) p_new = true).
      { apply Nat.ltb_lt. exact Hlower. }
      rewrite Hltb. reflexivity.
    - reflexivity. }
  rewrite Hbf. reflexivity.
Qed.

(** Adding a fired exception with the same priority as the
    current best leaves the result at the current best (the
    tie-breaking rule is "earlier wins", i.e., the later
    element is not strictly higher). *)
Theorem eval_tie_breaking_earlier_wins :
  forall base xs v p,
    (exists y, best_fired xs = Some y /\ priority y = p) ->
    eval_defeasible base (mk_exc true v p :: xs) =
    eval_defeasible base xs.
Proof.
  intros base xs v p [y [Hbest Heq]].
  unfold eval_defeasible.
  assert (Hbf : best_fired (mk_exc true v p :: xs) = Some y).
  { simpl. rewrite Hbest.
    assert (Hge : Nat.ltb (priority y) p = false).
    { apply Nat.ltb_ge. lia. }
    rewrite Hge. reflexivity. }
  rewrite Hbf. rewrite Hbest. reflexivity.
Qed.

(** ** Further properties of the priority evaluator *)

(** When the best-fired returns [Some y], the evaluator yields
    [body y].  Immediate from the definition, but exposed as a
    named theorem for downstream citation. *)
Theorem eval_fires_body_of_best :
  forall base xs y,
    best_fired xs = Some y ->
    eval_defeasible base xs = body y.
Proof.
  intros base xs y H. unfold eval_defeasible. rewrite H. reflexivity.
Qed.

(** When the best-fired returns [None], the evaluator yields the
    base verdict. *)
Theorem eval_no_fired_is_base :
  forall base xs,
    best_fired xs = None ->
    eval_defeasible base xs = base.
Proof.
  intros base xs H. unfold eval_defeasible. rewrite H. reflexivity.
Qed.

(** If every exception in the list has [guard = false], then
    [best_fired] returns [None].  Backward direction of the iff
    characterisation — used by [eval_all_unfired_is_base]. *)
Lemma best_fired_none_of_all_unfired :
  forall xs,
    (forall x, In x xs -> guard x = false) ->
    best_fired xs = None.
Proof.
  induction xs as [|x xs IH]; intro H.
  - reflexivity.
  - simpl.
    assert (Hx : guard x = false) by (apply H; simpl; left; reflexivity).
    assert (Hrest : best_fired xs = None).
    { apply IH. intros x0 Hin. apply H. simpl. right. exact Hin. }
    rewrite Hrest. rewrite Hx. reflexivity.
Qed.

(** If every exception in the list has [guard = false], the
    evaluator returns the base verdict. *)
Theorem eval_all_unfired_is_base :
  forall base xs,
    (forall x, In x xs -> guard x = false) ->
    eval_defeasible base xs = base.
Proof.
  intros base xs Hunfired.
  apply eval_no_fired_is_base.
  apply best_fired_none_of_all_unfired.
  exact Hunfired.
Qed.

(** Forward direction of the none-iff-all-unfired characterisation:
    if [best_fired xs = None], every element of [xs] has
    [guard = false]. *)
Lemma best_fired_none_implies_all_unfired :
  forall xs,
    best_fired xs = None ->
    forall x, In x xs -> guard x = false.
Proof.
  induction xs as [|y ys IH]; intros Hnone x Hin.
  - simpl in Hin. contradiction.
  - simpl in Hnone.
    destruct (best_fired ys) as [u|] eqn:Hbf.
    + destruct (guard y) eqn:Hgy.
      * destruct (Nat.ltb (priority u) (priority y)); discriminate.
      * discriminate.
    + destruct (guard y) eqn:Hgy; try discriminate.
      simpl in Hin. destruct Hin as [Heq | Hin'].
      * subst x. exact Hgy.
      * apply IH; [exact Hnone | exact Hin'].
Qed.

(** Full characterisation as an iff. *)
Theorem best_fired_none_iff :
  forall xs,
    best_fired xs = None <->
    (forall x, In x xs -> guard x = false).
Proof.
  intros xs. split.
  - apply best_fired_none_implies_all_unfired.
  - apply best_fired_none_of_all_unfired.
Qed.

(** Adding a fired exception with a higher priority than the current
    best causes [best_fired] to emit the new exception.  Combined
    with [eval_fires_body_of_best], this is the override lemma. *)
Lemma best_fired_higher_priority_overrides :
  forall xs v p_new,
    (forall y, best_fired xs = Some y -> priority y < p_new) ->
    best_fired (mk_exc true v p_new :: xs) = Some (mk_exc true v p_new).
Proof.
  intros xs v p_new Hlower.
  simpl. destruct (best_fired xs) as [y|] eqn:Hbest.
  - specialize (Hlower y eq_refl).
    assert (Hltb : Nat.ltb (priority y) p_new = true)
      by (apply Nat.ltb_lt; exact Hlower).
    rewrite Hltb. reflexivity.
  - reflexivity.
Qed.

(** Uniqueness of best_fired's result: [best_fired] is a deterministic
    function, so two successful calls on the same list return the same
    exception.  Trivial from functionality but useful as a named lemma. *)
Theorem best_fired_deterministic :
  forall xs y1 y2,
    best_fired xs = Some y1 ->
    best_fired xs = Some y2 ->
    y1 = y2.
Proof.
  intros xs y1 y2 H1 H2. rewrite H1 in H2. injection H2. auto.
Qed.

(** The evaluator is deterministic. *)
Theorem eval_defeasible_deterministic :
  forall base xs v1 v2,
    eval_defeasible base xs = v1 ->
    eval_defeasible base xs = v2 ->
    v1 = v2.
Proof. intros base xs v1 v2 H1 H2. rewrite <- H1, <- H2. reflexivity. Qed.

(** ** Further evaluator properties (2026-04-20) *)

(** A fired exception's body is always the result when it's the
    only firing exception in the list. *)
Theorem eval_single_fire_result :
  forall base v p,
    eval_defeasible base [mk_exc true v p] = v.
Proof. intros base v p. apply eval_single_fired. reflexivity. Qed.

(** eval_defeasible on the empty list always returns the base. *)
Theorem eval_empty_base :
  forall base, eval_defeasible base [] = base.
Proof. apply eval_no_exceptions. Qed.

(** Adding an unfired exception to an empty list leaves the result
    as the base. *)
Theorem eval_unfired_cons_empty :
  forall base v p,
    eval_defeasible base [mk_exc false v p] = base.
Proof. apply eval_single_unfired. Qed.

(** best_fired commutes with filtering to the fired-only subset:
    if all exceptions are fired, best_fired returns [Some] of a
    highest-priority exception.  Lightweight form here: if the list
    has exactly one fired exception, that's the result. *)
Theorem best_fired_exactly_one_fire :
  forall v p,
    best_fired [mk_exc true v p] = Some (mk_exc true v p).
Proof. intros v p. reflexivity. Qed.
