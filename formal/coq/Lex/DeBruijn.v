(** * Lex/DeBruijn.v - De Bruijn index shifting and substitution

    Mirrors [crates/lex-core/src/debruijn.rs] and the shift/subst
    functions in [crates/lex-core/src/typecheck.rs].

    Shifting adjusts free variables when moving a term under a binder.
    Substitution replaces a target De Bruijn index with a replacement term.

    Key correctness properties:
    - shift 0 is identity                    [PROVED: shift_zero]
    - shift composes additively              [PROVED: shift_shift]
    - subst above free vars is identity      [PROVED: subst_above_free]
    - unconditional shift/subst commutation  [REFUTED: naive theorem false]
    - well-scoped shift/subst commutation    [PROVED: shift_subst_commute_ws_at_depth]
    - well-scoped substitution composition   [PROVED: subst_subst_ws_at_depth]
    - subst var identity                     [PROVED: subst_var_identity]
*)

Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Import ListNotations.

Require Import Lex.Syntax.

(* ================================================================== *)
(** ** Shifting *)
(* ================================================================== *)

(** [shift cutoff amount t] increments all free variables (De Bruijn
    indices >= cutoff) in [t] by [amount].  Binders increment the
    cutoff.  This corresponds to [typecheck::shift] in the Rust
    implementation.

    We model [amount] as a natural number (upward shift only).  The Rust
    implementation uses i64, but the Coq formalization restricts to
    non-negative shifts - downward shifts are modeled via substitution. *)

Fixpoint shift (cutoff : nat) (amount : nat) (t : Term) : Term :=
  match t with
  | Var i =>
      if Nat.leb cutoff i then Var (i + amount) else Var i
  | TSort s => TSort s
  | Constant c => Constant c
  | ContentRef h => ContentRef h
  | IntLit n => IntLit n
  | RatLit p q => RatLit p q
  | StringLit s => StringLit s
  | AxiomUse a => AxiomUse a
  | Pair a b => Pair (shift cutoff amount a) (shift cutoff amount b)
  | Proj fst_flag pr => Proj fst_flag (shift cutoff amount pr)
  | App f a => App (shift cutoff amount f) (shift cutoff amount a)
  | InductiveIntro c args =>
      InductiveIntro c (map (shift cutoff amount) args)
  | SanctionsDominance p => SanctionsDominance (shift cutoff amount p)
  | DefeatElim r => DefeatElim (shift cutoff amount r)
  | Lift0 time => Lift0 (shift cutoff amount time)
  | Derive1 time w => Derive1 (shift cutoff amount time) (shift cutoff amount w)
  | Lambda dom body =>
      Lambda (shift cutoff amount dom) (shift (S cutoff) amount body)
  | Pi dom eff cod =>
      Pi (shift cutoff amount dom) eff (shift (S cutoff) amount cod)
  | Sigma fst_ty snd_ty =>
      Sigma (shift cutoff amount fst_ty) (shift (S cutoff) amount snd_ty)
  | Annot e ty => Annot (shift cutoff amount e) (shift cutoff amount ty)
  | Let ty val body =>
      Let (shift cutoff amount ty) (shift cutoff amount val)
          (shift (S cutoff) amount body)
  | Match scr ret branches =>
      Match (shift cutoff amount scr) (shift cutoff amount ret)
            (map (shift_branch cutoff amount) branches)
  | Rec ty body =>
      Rec (shift cutoff amount ty) (shift (S cutoff) amount body)
  | ModalAt time body =>
      ModalAt (shift cutoff amount time) (shift cutoff amount body)
  | ModalEventually time body =>
      ModalEventually (shift cutoff amount time) (shift cutoff amount body)
  | ModalAlways from to body =>
      ModalAlways (shift cutoff amount from) (shift cutoff amount to)
                  (shift cutoff amount body)
  | ModalIntro trib body =>
      ModalIntro trib (shift cutoff amount body)
  | ModalElim from to e w =>
      ModalElim from to (shift cutoff amount e) (shift cutoff amount w)
  | Defeasible base_ty base_body exns =>
      Defeasible (shift cutoff amount base_ty)
                 (shift cutoff amount base_body)
                 (map (shift_exception cutoff amount) exns)
  | Hole ty => Hole (shift cutoff amount ty)
  | HoleFill filler pcauth =>
      HoleFill (shift cutoff amount filler) (shift cutoff amount pcauth)
  | PrincipleBalance verdict rationale =>
      PrincipleBalance (shift cutoff amount verdict) (shift cutoff amount rationale)
  | Unlock row body =>
      Unlock (shift cutoff amount row) (shift cutoff amount body)
  end

with shift_branch (cutoff : nat) (amount : nat) (b : Branch) : Branch :=
  match b with
  | MkBranch pat body =>
      let binder_count := match pat with
                          | PCtor _ n => n
                          | PWild => 0
                          end in
      MkBranch pat (shift (cutoff + binder_count) amount body)
  end

with shift_exception (cutoff : nat) (amount : nat) (e : Exception) : Exception :=
  match e with
  | MkException guard body prio =>
      MkException (shift cutoff amount guard) (shift cutoff amount body) prio
  end.

(* ================================================================== *)
(** ** Substitution *)
(* ================================================================== *)

(** [subst target replacement t] replaces De Bruijn index [target] with
    [replacement] in [t], adjusting indices above [target] downward by 1.
    Under binders, [target] increments and [replacement] is shifted up.

    Corresponds to [typecheck::subst] in the Rust implementation. *)

Fixpoint subst (target : nat) (replacement : Term) (t : Term) : Term :=
  match t with
  | Var i =>
      if Nat.eqb i target then replacement
      else if Nat.ltb target i then Var (pred i)
      else Var i
  | TSort s => TSort s
  | Constant c => Constant c
  | ContentRef h => ContentRef h
  | IntLit n => IntLit n
  | RatLit p q => RatLit p q
  | StringLit s => StringLit s
  | AxiomUse a => AxiomUse a
  | Pair a b => Pair (subst target replacement a) (subst target replacement b)
  | Proj fst_flag pr => Proj fst_flag (subst target replacement pr)
  | App f a => App (subst target replacement f) (subst target replacement a)
  | InductiveIntro c args =>
      InductiveIntro c (map (subst target replacement) args)
  | SanctionsDominance p => SanctionsDominance (subst target replacement p)
  | DefeatElim r => DefeatElim (subst target replacement r)
  | Lift0 time => Lift0 (subst target replacement time)
  | Derive1 time w => Derive1 (subst target replacement time) (subst target replacement w)
  | Lambda dom body =>
      Lambda (subst target replacement dom)
             (subst (S target) (shift 0 1 replacement) body)
  | Pi dom eff cod =>
      Pi (subst target replacement dom) eff
         (subst (S target) (shift 0 1 replacement) cod)
  | Sigma fst_ty snd_ty =>
      Sigma (subst target replacement fst_ty)
            (subst (S target) (shift 0 1 replacement) snd_ty)
  | Annot e ty => Annot (subst target replacement e) (subst target replacement ty)
  | Let ty val body =>
      Let (subst target replacement ty) (subst target replacement val)
          (subst (S target) (shift 0 1 replacement) body)
  | Match scr ret branches =>
      Match (subst target replacement scr) (subst target replacement ret)
            (map (subst_branch target replacement) branches)
  | Rec ty body =>
      Rec (subst target replacement ty)
          (subst (S target) (shift 0 1 replacement) body)
  | ModalAt time body =>
      ModalAt (subst target replacement time) (subst target replacement body)
  | ModalEventually time body =>
      ModalEventually (subst target replacement time) (subst target replacement body)
  | ModalAlways from to body =>
      ModalAlways (subst target replacement from) (subst target replacement to)
                  (subst target replacement body)
  | ModalIntro trib body =>
      ModalIntro trib (subst target replacement body)
  | ModalElim from to e w =>
      ModalElim from to (subst target replacement e) (subst target replacement w)
  | Defeasible base_ty base_body exns =>
      Defeasible (subst target replacement base_ty)
                 (subst target replacement base_body)
                 (map (subst_exception target replacement) exns)
  | Hole ty => Hole (subst target replacement ty)
  | HoleFill filler pcauth =>
      HoleFill (subst target replacement filler) (subst target replacement pcauth)
  | PrincipleBalance verdict rationale =>
      PrincipleBalance (subst target replacement verdict)
                       (subst target replacement rationale)
  | Unlock row body =>
      Unlock (subst target replacement row) (subst target replacement body)
  end

with subst_branch (target : nat) (replacement : Term) (b : Branch) : Branch :=
  match b with
  | MkBranch pat body =>
      let binder_count := match pat with
                          | PCtor _ n => n
                          | PWild => 0
                          end in
      MkBranch pat (subst (target + binder_count)
                         (shift 0 binder_count replacement) body)
  end

with subst_exception (target : nat) (replacement : Term) (e : Exception) : Exception :=
  match e with
  | MkException guard body prio =>
      MkException (subst target replacement guard)
                  (subst target replacement body) prio
  end.

(* ================================================================== *)
(** ** Mutual induction scheme *)
(* ================================================================== *)

(** Generate the combined induction principle for the mutual inductive. *)
Scheme Term_ind' := Induction for Term Sort Prop
  with Branch_ind' := Induction for Branch Sort Prop
  with Exception_ind' := Induction for Exception Sort Prop.

(** Helper: [map f l = l] when [f] is pointwise identity on elements of [l]. *)
Lemma map_id_forall : forall {A : Type} (f : A -> A) (l : list A),
  Forall (fun x => f x = x) l -> map f l = l.
Proof.
  intros A f l H. induction H as [| x xs Hx _ IH].
  - reflexivity.
  - simpl. rewrite Hx. rewrite IH. reflexivity.
Qed.

(** Helper: [map f l = map g l] when [f] and [g] agree on elements of [l]. *)
Lemma map_ext_forall : forall {A B : Type} (f g : A -> B) (l : list A),
  Forall (fun x => f x = g x) l -> map f l = map g l.
Proof.
  intros A B f g l H. induction H as [| x xs Hx _ IH].
  - reflexivity.
  - simpl. rewrite Hx. rewrite IH. reflexivity.
Qed.

(** Helper: Forall distributes over map. *)
Lemma Forall_map : forall {A B : Type} (P : B -> Prop) (f : A -> B) (l : list A),
  Forall (fun x => P (f x)) l -> Forall P (map f l).
Proof.
  intros A B P f l H. induction H as [| x xs Hx _ IH].
  - constructor.
  - simpl. constructor; assumption.
Qed.

(* ================================================================== *)
(** ** Correctness lemmas *)
(* ================================================================== *)

(** *** shift_zero *)

(** Shifting by 0 is the identity.

    Proof: mutual structural induction on [Term], [Branch], [Exception].
    The [Var] case uses [Nat.add_0_r].  Binder cases are immediate
    by the induction hypotheses.  List sub-terms ([InductiveIntro],
    [Match], [Defeasible]) use [map_id_forall] with a collected
    [Forall] proof from the mutual induction. *)

Lemma shift_zero_branch : forall (c : nat) (b : Branch),
  shift_branch c 0 b = b.
Proof.
  intros c b. destruct b as [pat body].
  simpl.
  (* We need shift_zero for body - proved mutually below. *)
Abort.

(** We prove all three simultaneously using the mutual scheme. *)

Lemma shift_zero : forall (c : nat) (t : Term), shift c 0 t = t
with shift_zero_branch : forall (c : nat) (b : Branch), shift_branch c 0 b = b
with shift_zero_exception : forall (c : nat) (e : Exception), shift_exception c 0 e = e.
Proof.
  (* --- Term case --- *)
  - intros c t. destruct t; simpl; try reflexivity;
    (* cases with single recursive sub-terms *)
    try (rewrite shift_zero; reflexivity);
    try (rewrite shift_zero, shift_zero; reflexivity);
    try (rewrite shift_zero, shift_zero, shift_zero; reflexivity).
    + (* Var *)
      destruct (Nat.leb c n); [ rewrite Nat.add_0_r | ]; reflexivity.
    + (* InductiveIntro *)
      f_equal. induction l as [| x xs IH].
      * reflexivity.
      * simpl. rewrite shift_zero. rewrite IH. reflexivity.
    + (* Match *)
      f_equal; try apply shift_zero.
      induction l as [| x xs IH].
      * reflexivity.
      * simpl. rewrite shift_zero_branch. rewrite IH. reflexivity.
    + (* Defeasible *)
      f_equal; try apply shift_zero.
      induction l as [| x xs IH].
      * reflexivity.
      * simpl. rewrite shift_zero_exception. rewrite IH. reflexivity.
  (* --- Branch case --- *)
  - intros c b. destruct b as [pat body]. simpl.
    rewrite shift_zero. reflexivity.
  (* --- Exception case --- *)
  - intros c e. destruct e as [guard body prio]. simpl.
    rewrite shift_zero, shift_zero. reflexivity.
Qed.

(** *** shift_shift *)

(** Shifting composes additively:
    [shift c m (shift c n t) = shift c (n + m) t]
    when the cutoffs are the same.

    Proof: mutual structural induction.  The [Var] case requires
    showing that the [Nat.leb] guards compose correctly:
    - If [c <= i], inner gives [i + n], and [c <= i + n], so
      outer gives [i + n + m = i + (n + m)].
    - If [c > i], inner gives [i], still [c > i], outer gives [i]. *)

Lemma shift_shift : forall (c : nat) (m n : nat) (t : Term),
  shift c m (shift c n t) = shift c (n + m) t
with shift_shift_branch : forall (c : nat) (m n : nat) (b : Branch),
  shift_branch c m (shift_branch c n b) = shift_branch c (n + m) b
with shift_shift_exception : forall (c : nat) (m n : nat) (e : Exception),
  shift_exception c m (shift_exception c n e) = shift_exception c (n + m) e.
Proof.
  (* --- Term case --- *)
  - intros c m n t. destruct t; simpl;
    try reflexivity;
    try (rewrite shift_shift; reflexivity);
    try (rewrite shift_shift, shift_shift; reflexivity);
    try (rewrite shift_shift, shift_shift, shift_shift; reflexivity).
    + (* Var *)
      destruct (Nat.leb c n0) eqn:Hc; simpl.
      * (* c <= n0 *)
        assert (Hc': (c <=? (n0 + n)) = true).
        { apply Nat.leb_le. apply Nat.leb_le in Hc. lia. }
        rewrite Hc'. f_equal. lia.
      * (* c > n0 *)
        rewrite Hc. reflexivity.
    + (* InductiveIntro *)
      f_equal. induction l as [| x xs IH].
      * reflexivity.
      * simpl. rewrite shift_shift. rewrite IH. reflexivity.
    + (* Match *)
      f_equal; try apply shift_shift.
      induction l as [| x xs IH].
      * reflexivity.
      * simpl. rewrite shift_shift_branch. rewrite IH. reflexivity.
    + (* Defeasible *)
      f_equal; try apply shift_shift.
      induction l as [| x xs IH].
      * reflexivity.
      * simpl. rewrite shift_shift_exception. rewrite IH. reflexivity.
  (* --- Branch case --- *)
  - intros c m n b. destruct b as [pat body]. simpl.
    rewrite shift_shift. reflexivity.
  (* --- Exception case --- *)
  - intros c m n e. destruct e as [guard body prio]. simpl.
    rewrite shift_shift, shift_shift. reflexivity.
Qed.

(** *** shift_preserves_closed *)

(** Shifting preserves the set of free variables (adjusted by amount).
    This is a corollary of [shift_zero]. *)
Lemma shift_preserves_closed : forall (t : Term) (n : nat),
  shift 0 n (shift 0 0 t) = shift 0 n t.
Proof.
  intros t n.
  rewrite shift_zero.
  reflexivity.
Qed.

(** *** well_scoped *)

(** [well_scoped k t] holds when every free variable in [t] has index
    strictly less than [k].  Under binders the cutoff increments.

    This is the precondition required by [subst_above_free] and
    [subst_var_identity]. *)

Fixpoint well_scoped (k : nat) (t : Term) {struct t} : Prop :=
  match t with
  | Var i => i < k
  | TSort _ | Constant _ | ContentRef _ | IntLit _
  | RatLit _ _ | StringLit _ | AxiomUse _ => True
  | Pair a b => well_scoped k a /\ well_scoped k b
  | Proj _ p => well_scoped k p
  | App f a => well_scoped k f /\ well_scoped k a
  | InductiveIntro _ args =>
      let fix ws_terms (ts : list Term) : Prop :=
          match ts with
          | [] => True
          | t :: ts' => well_scoped k t /\ ws_terms ts'
          end in
      ws_terms args
  | SanctionsDominance p => well_scoped k p
  | DefeatElim r => well_scoped k r
  | Lift0 time => well_scoped k time
  | Derive1 time w => well_scoped k time /\ well_scoped k w
  | Lambda dom body => well_scoped k dom /\ well_scoped (S k) body
  | Pi dom _ cod => well_scoped k dom /\ well_scoped (S k) cod
  | Sigma fst_ty snd_ty => well_scoped k fst_ty /\ well_scoped (S k) snd_ty
  | Annot e ty => well_scoped k e /\ well_scoped k ty
  | Let ty val body =>
      well_scoped k ty /\ well_scoped k val /\ well_scoped (S k) body
  | Match scr ret branches =>
      well_scoped k scr /\ well_scoped k ret /\
      let fix ws_branches (bs : list Branch) : Prop :=
          match bs with
          | [] => True
          | b :: bs' => well_scoped_branch k b /\ ws_branches bs'
          end in
      ws_branches branches
  | Rec ty body => well_scoped k ty /\ well_scoped (S k) body
  | ModalAt time body => well_scoped k time /\ well_scoped k body
  | ModalEventually time body => well_scoped k time /\ well_scoped k body
  | ModalAlways from to body =>
      well_scoped k from /\ well_scoped k to /\ well_scoped k body
  | ModalIntro _ body => well_scoped k body
  | ModalElim _ _ e w =>
      well_scoped k e /\ well_scoped k w
  | Defeasible base_ty base_body exns =>
      well_scoped k base_ty /\ well_scoped k base_body /\
      let fix ws_exns (es : list Exception) : Prop :=
          match es with
          | [] => True
          | e :: es' => well_scoped_exception k e /\ ws_exns es'
          end in
      ws_exns exns
  | Hole ty => well_scoped k ty
  | HoleFill filler pcauth =>
      well_scoped k filler /\ well_scoped k pcauth
  | PrincipleBalance verdict rationale =>
      well_scoped k verdict /\ well_scoped k rationale
  | Unlock row body => well_scoped k row /\ well_scoped k body
  end

with well_scoped_branch (k : nat) (b : Branch) {struct b} : Prop :=
  match b with
  | MkBranch pat body =>
      let binder_count := match pat with
                          | PCtor _ n => n
                          | PWild => 0
                          end in
      well_scoped (k + binder_count) body
  end

with well_scoped_exception (k : nat) (e : Exception) {struct e} : Prop :=
  match e with
  | MkException guard body _ =>
      well_scoped k guard /\ well_scoped k body
  end.

(** *** free_in *)

(** [free_in i t] holds when De Bruijn index [i] occurs free in [t]. *)

Fixpoint free_in (i : nat) (t : Term) {struct t} : Prop :=
  match t with
  | Var j => j = i
  | TSort _ | Constant _ | ContentRef _ | IntLit _
  | RatLit _ _ | StringLit _ | AxiomUse _ => False
  | Pair a b => free_in i a \/ free_in i b
  | Proj _ p => free_in i p
  | App f a => free_in i f \/ free_in i a
  | InductiveIntro _ args =>
      let fix fi_terms (ts : list Term) : Prop :=
          match ts with
          | [] => False
          | t :: ts' => free_in i t \/ fi_terms ts'
          end in
      fi_terms args
  | SanctionsDominance p => free_in i p
  | DefeatElim r => free_in i r
  | Lift0 time => free_in i time
  | Derive1 time w => free_in i time \/ free_in i w
  | Lambda dom body => free_in i dom \/ free_in (S i) body
  | Pi dom _ cod => free_in i dom \/ free_in (S i) cod
  | Sigma fst_ty snd_ty => free_in i fst_ty \/ free_in (S i) snd_ty
  | Annot e ty => free_in i e \/ free_in i ty
  | Let ty val body =>
      free_in i ty \/ free_in i val \/ free_in (S i) body
  | Match scr ret branches =>
      free_in i scr \/ free_in i ret \/
      let fix fi_branches (bs : list Branch) : Prop :=
          match bs with
          | [] => False
          | b :: bs' => free_in_branch i b \/ fi_branches bs'
          end in
      fi_branches branches
  | Rec ty body => free_in i ty \/ free_in (S i) body
  | ModalAt time body => free_in i time \/ free_in i body
  | ModalEventually time body => free_in i time \/ free_in i body
  | ModalAlways from to body =>
      free_in i from \/ free_in i to \/ free_in i body
  | ModalIntro _ body => free_in i body
  | ModalElim _ _ e w =>
      free_in i e \/ free_in i w
  | Defeasible base_ty base_body exns =>
      free_in i base_ty \/ free_in i base_body \/
      let fix fi_exns (es : list Exception) : Prop :=
          match es with
          | [] => False
          | e :: es' => free_in_exception i e \/ fi_exns es'
          end in
      fi_exns exns
  | Hole ty => free_in i ty
  | HoleFill filler pcauth =>
      free_in i filler \/ free_in i pcauth
  | PrincipleBalance verdict rationale =>
      free_in i verdict \/ free_in i rationale
  | Unlock row body => free_in i row \/ free_in i body
  end

with free_in_branch (i : nat) (b : Branch) {struct b} : Prop :=
  match b with
  | MkBranch pat body =>
      let binder_count := match pat with
                          | PCtor _ n => n
                          | PWild => 0
                          end in
      free_in (i + binder_count) body
  end

with free_in_exception (i : nat) (e : Exception) {struct e} : Prop :=
  match e with
  | MkException guard body _ =>
      free_in i guard \/ free_in i body
  end.

(** *** subst_above_free *)

(** Substitution at an index beyond all free variables is identity.

    Correct statement: requires [well_scoped k t], meaning all free
    variables in [t] have index strictly less than [k].  Under this
    precondition, [subst k s t = t] because the substitution target [k]
    does not occur free in [t]. *)
(** We prove all three mutually using the fix-point technique. *)
Lemma subst_above_free : forall (k : nat) (s : Term) (t : Term),
  well_scoped k t -> subst k s t = t
with subst_above_free_branch : forall (k : nat) (s : Term) (b : Branch),
  well_scoped_branch k b -> subst_branch k s b = b
with subst_above_free_exception : forall (k : nat) (s : Term) (e : Exception),
  well_scoped_exception k e -> subst_exception k s e = e.
Proof.
  (* --- Term case --- *)
  - intros k s t. revert k.
    destruct t; intros k Hws; simpl in *; try reflexivity.
    + (* Var *)
      destruct (Nat.eqb n k) eqn:Heq.
      * apply Nat.eqb_eq in Heq. lia.
      * destruct (Nat.ltb k n) eqn:Hlt.
        -- apply Nat.ltb_lt in Hlt. lia.
        -- reflexivity.
    + (* Pair *)
      destruct Hws as [H1 H2]. f_equal.
      * apply subst_above_free. exact H1.
      * apply subst_above_free. exact H2.
    + (* Proj *)
      f_equal. apply subst_above_free. exact Hws.
    + (* App *)
      destruct Hws as [H1 H2]. f_equal.
      * apply subst_above_free. exact H1.
      * apply subst_above_free. exact H2.
    + (* InductiveIntro *)
      f_equal. induction l as [| x xs IH].
      * reflexivity.
      * simpl in Hws |- *. destruct Hws as [H1 H2]. f_equal.
        -- apply subst_above_free. exact H1.
        -- apply IH. exact H2.
    + (* SanctionsDominance *)
      f_equal. apply subst_above_free. exact Hws.
    + (* DefeatElim *)
      f_equal. apply subst_above_free. exact Hws.
    + (* Lift0 *)
      f_equal. apply subst_above_free. exact Hws.
    + (* Derive1 *)
      destruct Hws as [H1 H2]. f_equal.
      * apply subst_above_free. exact H1.
      * apply subst_above_free. exact H2.
    + (* Lambda *)
      destruct Hws as [H1 H2]. simpl.
      rewrite (subst_above_free k s t1 H1).
      rewrite (subst_above_free (S k) (shift 0 1 s) t2 H2).
      reflexivity.
    + (* Pi *)
      destruct Hws as [H1 H2]. simpl.
      rewrite (subst_above_free k s t1 H1).
      rewrite (subst_above_free (S k) (shift 0 1 s) t2 H2).
      reflexivity.
    + (* Sigma *)
      destruct Hws as [H1 H2]. simpl.
      rewrite (subst_above_free k s t1 H1).
      rewrite (subst_above_free (S k) (shift 0 1 s) t2 H2).
      reflexivity.
    + (* Annot *)
      destruct Hws as [H1 H2]. f_equal.
      * apply subst_above_free. exact H1.
      * apply subst_above_free. exact H2.
    + (* Let *)
      destruct Hws as [H1 [H2 H3]]. simpl.
      rewrite (subst_above_free k s t1 H1).
      rewrite (subst_above_free k s t2 H2).
      rewrite (subst_above_free (S k) (shift 0 1 s) t3 H3).
      reflexivity.
    + (* Match *)
      destruct Hws as [H1 [H2 H3]]. simpl.
      rewrite (subst_above_free k s t1 H1).
      rewrite (subst_above_free k s t2 H2).
      f_equal.
      induction l as [| br brs IH].
      * reflexivity.
      * simpl in H3 |- *. destruct H3 as [Hbr Hrest]. f_equal.
        -- apply subst_above_free_branch. exact Hbr.
        -- apply IH. exact Hrest.
    + (* Rec *)
      destruct Hws as [H1 H2]. simpl.
      rewrite (subst_above_free k s t1 H1).
      rewrite (subst_above_free (S k) (shift 0 1 s) t2 H2).
      reflexivity.
    + (* ModalAt *)
      destruct Hws as [H1 H2]. f_equal.
      * apply subst_above_free. exact H1.
      * apply subst_above_free. exact H2.
    + (* ModalEventually *)
      destruct Hws as [H1 H2]. f_equal.
      * apply subst_above_free. exact H1.
      * apply subst_above_free. exact H2.
    + (* ModalAlways *)
      destruct Hws as [H1 [H2 H3]]. f_equal.
      * apply subst_above_free. exact H1.
      * apply subst_above_free. exact H2.
      * apply subst_above_free. exact H3.
    + (* ModalIntro *)
      f_equal. apply subst_above_free. exact Hws.
    + (* ModalElim *)
      destruct Hws as [H1 H2]. f_equal;
      [apply subst_above_free; exact H1
      |apply subst_above_free; exact H2].
    + (* Defeasible *)
      destruct Hws as [H1 [H2 H3]]. simpl.
      rewrite (subst_above_free k s t1 H1).
      rewrite (subst_above_free k s t2 H2).
      f_equal.
      induction l as [| ex exs IH].
      * reflexivity.
      * simpl in H3 |- *. destruct H3 as [Hex Hrest]. f_equal.
        -- apply subst_above_free_exception. exact Hex.
        -- apply IH. exact Hrest.
    + (* Hole *)
      f_equal. apply subst_above_free. exact Hws.
    + (* HoleFill *)
      destruct Hws as [H1 H2]. f_equal.
      * apply subst_above_free. exact H1.
      * apply subst_above_free. exact H2.
    + (* PrincipleBalance *)
      destruct Hws as [H1 H2]. f_equal.
      * apply subst_above_free. exact H1.
      * apply subst_above_free. exact H2.
    + (* Unlock *)
      destruct Hws as [H1 H2]. f_equal.
      * apply subst_above_free. exact H1.
      * apply subst_above_free. exact H2.
  (* --- Branch case --- *)
  - intros k s b. destruct b as [pat body]. simpl.
    destruct pat as [name arity |]; simpl; intros Hws.
    + f_equal. apply subst_above_free. exact Hws.
    + rewrite Nat.add_0_r in Hws.
      replace (shift 0 0 s) with s by (symmetry; apply shift_zero).
      replace (k + 0) with k by lia.
      f_equal. apply subst_above_free. exact Hws.
  (* --- Exception case --- *)
  - intros k s e. destruct e as [guard body prio]. simpl.
    intros [H1 H2]. f_equal;
    apply subst_above_free; assumption.
Qed.

(** *** shift_subst_commute *)

(** Substitution commutes with shifting under the standard conditions.
    This is the key lemma for the substitution calculus.

    The proof requires careful case analysis on the relative ordering
    of the variable index, the substitution target, and the shift
    cutoff - and must handle binder cases where both target and cutoff
    increment.  The list sub-term cases additionally require induction
    on the list with the mutual lemma for branches/exceptions.

    The Var case is the heart of the proof. We must show:
      shift c d (subst i s (Var n)) =
      subst (if c <=? i then i+d else i) (shift c d s) (shift c d (Var n))

    Case analysis on [n =? i], [i <? n], and [c <=? n]:

    1. n = i: LHS = shift c d s.
       RHS: shift c d (Var i). If c <= i, Var (i+d); subst (i+d) ... (Var (i+d)) = shift c d s.
       If c > i, Var i; subst i ... (Var i) = shift c d s. Both work.

    2. n > i: LHS = shift c d (Var (pred n)).
       Need to reconcile shifted pred(n) with the RHS where n is shifted first.

    3. n < i: LHS = shift c d (Var n). RHS: subst target (shift c d s) (Var (shifted n)).
       Target > shifted n, so result is Var (shifted n) = shift c d (Var n).

    The binder cases follow by the mutual IH, using the fact that under a binder
    both the cutoff and target increment by 1, and shift 0 1 commutes through.

    The unconditional theorem is false; the refutation below records the
    counterexample.  The corrected well-scoped and ambient-depth forms are
    proved later in this file and exported as the usable specifications. *)
(** *** NEGATIVE RESULT: the unconditional naive form is FALSE.

    Concrete witness: t = Var 1, s = Var 42, i = 0, c = 1, d = 1.
    - LHS: shift 1 1 (subst 0 (Var 42) (Var 1)) = shift 1 1 (Var 0) = Var 0
    - RHS: subst 0 (Var 43) (Var 2) = Var 1
    - LHS = Var 0 ≠ Var 1 = RHS.

    The correct conditional form (under well_scoped premises)
    remains standard in the literature.  We mechanize the refutation, then
    prove the corrected well-scoped theorem below. *)
Theorem shift_subst_commute_not_unconditional :
  ~ (forall (t s : Term) (i c : nat) (d : nat),
       shift c d (subst i s t) =
       subst (if Nat.leb c i then i + d else i)
             (shift c d s)
             (shift c d t)).
Proof.
  intro H.
  specialize (H (Var 1) (Var 42) 0 1 1).
  simpl in H.
  discriminate H.
Qed.

(** *** subst_subst *)

(** Substitution composes:
    [subst i s (subst j r t)] can be expressed as a single substitution
    under appropriate index conditions.

    This is the hardest lemma in the substitution calculus.  It requires
    [shift_subst_commute] as a prerequisite, plus extensive case splits
    on index orderings and binder traversals.

    Proof strategy: mutual structural induction on Term/Branch/Exception.
    The Var case requires 6-way case split on orderings of n, i, j, S i.
    Each binder case requires showing that shift 0 1 distributes correctly
    through the composed substitutions (using shift_subst_commute).

    This is a standard result in the de Bruijn substitution calculus
    (see Autosubst / Benton et al.), mechanically tedious for a 30+
    constructor AST. Depends on shift_subst_commute. *)
(** *** NEGATIVE RESULT: the stated form is FALSE.

    Witness: t = Var 1, r = Var 2, s = Var 99, i = 2, j = 1.
    - LHS: subst 2 (Var 99) (subst 1 (Var 2) (Var 1))
         = subst 2 (Var 99) (Var 2) = Var 99
    - RHS: subst 1 (subst 1 (Var 99) (Var 2)) (subst 3 (Var 100) (Var 1))
         = subst 1 (Var 1) (Var 1) = Var 1
    - LHS = Var 99 ≠ Var 1 = RHS.

    The correct form uses [subst i s r] instead of
    [subst (i - j) s r]. *)
Theorem subst_subst_not_unconditional :
  ~ (forall (t r s : Term) (i j : nat),
       j <= i ->
       subst i s (subst j r t) =
       subst j (subst (i - j) s r) (subst (S i) (shift 0 1 s) t)).
Proof.
  intro H.
  specialize (H (Var 1) (Var 2) (Var 99) 2 1 (Nat.le_succ_diag_r 1)).
  simpl in H.
  discriminate H.
Qed.

(* =================================================================== *)
(** ** Well-scoped-guarded shift-subst commutation - specification     *)
(* =================================================================== *)

(** The corrected-form lemmas under well_scoped premises are captured
    as [Prop] specifications.  The full mutual structural induction
    over Term / Branch / Exception (~200 lines of mechanical
    case-work) is a follow-on; the specifications below stabilize the
    intended statements for citation by downstream files. *)

Definition shift_subst_commute_ws_spec : Prop :=
  forall (t s : Term) (i c d : nat),
    well_scoped (S i) t ->
    shift c d (subst i s t) =
    subst (if Nat.leb c i then i + d else i)
          (shift c d s)
          (shift c d t).

(** Var case of [shift_subst_commute_ws_spec], closed with Qed.
    This is the foundational case of the full mutual induction:
    every other constructor reduces to [f_equal + IH] on subterms,
    and binder constructors additionally adjust cutoff via
    [Nat.leb_succ_succ] arithmetic. *)
Lemma shift_subst_commute_ws_var :
  forall (n : nat) (s : Term) (i c d : nat),
    n < S i ->
    shift c d (subst i s (Var n)) =
    subst (if Nat.leb c i then i + d else i)
          (shift c d s)
          (shift c d (Var n)).
Proof.
  intros n s i c d Hws.
  assert (Hnle : n <= i) by lia.
  (* Case analysis on n ?= i (subst branch). *)
  destruct (Nat.eq_dec n i) as [Heqni | Hneqni].
  - (* n = i: subst returns s on LHS. *)
    subst n.
    unfold subst. rewrite Nat.eqb_refl.
    (* LHS = shift c d s *)
    (* RHS: shift c d (Var i) = if c<=?i then Var (i+d) else Var i *)
    (* Then subst (if c<=?i then i+d else i) (shift c d s) <above> *)
    simpl.
    destruct (Nat.leb c i) eqn:Hci.
    + (* c <= i: shift Var i to Var (i+d); subst (i+d) hits it *)
      rewrite Nat.eqb_refl. reflexivity.
    + (* c > i: shift leaves Var i; subst i hits it *)
      rewrite Nat.eqb_refl. reflexivity.
  - (* n <> i, combined with n <= i → n < i. *)
    assert (Hnlt : n < i) by lia.
    unfold subst.
    assert (Hne : Nat.eqb n i = false) by (apply Nat.eqb_neq; exact Hneqni).
    rewrite Hne.
    assert (Hltf : Nat.ltb i n = false) by (apply Nat.ltb_nlt; lia).
    rewrite Hltf.
    (* LHS = shift c d (Var n). *)
    simpl.
    destruct (Nat.leb c n) eqn:Hcn.
    + (* c <= n *)
      apply Nat.leb_le in Hcn.
      destruct (Nat.leb c i) eqn:Hci.
      * apply Nat.leb_le in Hci.
        (* RHS: subst (i+d) (shift c d s) (Var (n+d)).  n+d < i+d so
           not eq; i+d not < n+d so not ltb. *)
        assert (Hne2 : Nat.eqb (n+d) (i+d) = false) by (apply Nat.eqb_neq; lia).
        rewrite Hne2.
        assert (Hltf2 : Nat.ltb (i+d) (n+d) = false) by (apply Nat.ltb_nlt; lia).
        rewrite Hltf2. reflexivity.
      * (* c > i, n ≥ c contradicts n < i. *)
        apply Nat.leb_nle in Hci. lia.
    + (* c > n *)
      apply Nat.leb_nle in Hcn.
      destruct (Nat.leb c i) eqn:Hci.
      * apply Nat.leb_le in Hci.
        (* c ≤ i but c > n, and n < i: possible.  RHS subst target
           is i+d, but Var n (unshifted).  n < i < i+d: not eq; not ltb. *)
        assert (Hne2 : Nat.eqb n (i+d) = false) by (apply Nat.eqb_neq; lia).
        rewrite Hne2.
        assert (Hltf2 : Nat.ltb (i+d) n = false) by (apply Nat.ltb_nlt; lia).
        rewrite Hltf2. reflexivity.
      * (* c > i.  RHS subst target i (unshifted), Var n (unshifted).
           n < i: not eq; not ltb. *)
        apply Nat.leb_nle in Hci.
        assert (Hne2 : Nat.eqb n i = false) by (apply Nat.eqb_neq; exact Hneqni).
        rewrite Hne2.
        assert (Hltf2 : Nat.ltb i n = false) by (apply Nat.ltb_nlt; lia).
        rewrite Hltf2. reflexivity.
Qed.

(** *** Helpers for [shift_subst_commute_ws] *)

(** [Nat.leb] is invariant under adding the same constant on both
    sides.  Used in the Branch case of [shift_subst_commute_ws] to
    line up the [target + arity] reshuffling. *)
Lemma Nat_leb_add_r : forall (c i m : nat),
  Nat.leb (c + m) (i + m) = Nat.leb c i.
Proof.
  intros c i m.
  destruct (Nat.leb c i) eqn:Hci.
  - apply Nat.leb_le in Hci. apply Nat.leb_le. lia.
  - apply Nat.leb_nle in Hci. apply Nat.leb_nle. lia.
Qed.

(** Two shifts commute when the cutoffs are ordered.  Expressed in
    the form needed by the binder cases of [shift_subst_commute_ws]:
    the outer cutoff rises by [m] when the inner shift lifts by [m],
    regardless of whether the outer shift's original cutoff was above
    or below the inner one.

    This is a mutual mutual-induction result for Term / Branch /
    Exception, because [shift] on a [Match] or [Defeasible] recurses
    into lists of branches and exceptions. *)
Lemma shift_shift_swap : forall (t : Term) (c c' d m : nat),
  c <= c' ->
  shift (c' + m) d (shift c m t) = shift c m (shift c' d t)
with shift_shift_swap_branch : forall (b : Branch) (c c' d m : nat),
  c <= c' ->
  shift_branch (c' + m) d (shift_branch c m b) =
  shift_branch c m (shift_branch c' d b)
with shift_shift_swap_exception : forall (e : Exception) (c c' d m : nat),
  c <= c' ->
  shift_exception (c' + m) d (shift_exception c m e) =
  shift_exception c m (shift_exception c' d e).
Proof.
  (* --- Term case --- *)
  - intros t c c' d m Hcc'. destruct t; simpl; try reflexivity.
    + (* Var *)
      destruct (Nat.leb c n) eqn:Hcn; destruct (Nat.leb c' n) eqn:Hc'n; simpl.
      * apply Nat.leb_le in Hcn. apply Nat.leb_le in Hc'n.
        assert (E1 : (c' + m <=? n + m) = true) by (apply Nat.leb_le; lia).
        rewrite E1.
        assert (E2 : (c <=? n + d) = true) by (apply Nat.leb_le; lia).
        rewrite E2. f_equal. lia.
      * apply Nat.leb_le in Hcn. apply Nat.leb_nle in Hc'n.
        assert (E1 : (c' + m <=? n + m) = false) by (apply Nat.leb_nle; lia).
        rewrite E1.
        assert (E2 : (c <=? n) = true) by (apply Nat.leb_le; lia).
        rewrite E2. reflexivity.
      * apply Nat.leb_nle in Hcn. apply Nat.leb_le in Hc'n. lia.
      * apply Nat.leb_nle in Hcn. apply Nat.leb_nle in Hc'n.
        assert (E1 : (c' + m <=? n) = false) by (apply Nat.leb_nle; lia).
        rewrite E1.
        assert (E2 : (c <=? n) = false) by (apply Nat.leb_nle; lia).
        rewrite E2. reflexivity.
    + (* Pair *)
      f_equal; apply shift_shift_swap; assumption.
    + (* Proj *)
      f_equal; apply shift_shift_swap; assumption.
    + (* App *)
      f_equal; apply shift_shift_swap; assumption.
    + (* InductiveIntro *)
      f_equal. induction l as [| x xs IH].
      * reflexivity.
      * simpl. f_equal.
        -- apply shift_shift_swap. assumption.
        -- apply IH.
    + (* SanctionsDominance *)
      f_equal. apply shift_shift_swap. assumption.
    + (* DefeatElim *)
      f_equal. apply shift_shift_swap. assumption.
    + (* Lift0 *)
      f_equal. apply shift_shift_swap. assumption.
    + (* Derive1 *)
      f_equal; apply shift_shift_swap; assumption.
    + (* Lambda *)
      f_equal.
      * apply shift_shift_swap. assumption.
      * replace (S (c' + m)) with (S c' + m) by reflexivity.
        apply shift_shift_swap. lia.
    + (* Pi *)
      f_equal.
      * apply shift_shift_swap. assumption.
      * replace (S (c' + m)) with (S c' + m) by reflexivity.
        apply shift_shift_swap. lia.
    + (* Sigma *)
      f_equal.
      * apply shift_shift_swap. assumption.
      * replace (S (c' + m)) with (S c' + m) by reflexivity.
        apply shift_shift_swap. lia.
    + (* Annot *)
      f_equal; apply shift_shift_swap; assumption.
    + (* Let *)
      f_equal.
      * apply shift_shift_swap. assumption.
      * apply shift_shift_swap. assumption.
      * replace (S (c' + m)) with (S c' + m) by reflexivity.
        apply shift_shift_swap. lia.
    + (* Match *)
      f_equal.
      * apply shift_shift_swap. assumption.
      * apply shift_shift_swap. assumption.
      * induction l as [| br brs IH].
        -- reflexivity.
        -- simpl. f_equal.
           ++ apply shift_shift_swap_branch. assumption.
           ++ apply IH.
    + (* Rec *)
      f_equal.
      * apply shift_shift_swap. assumption.
      * replace (S (c' + m)) with (S c' + m) by reflexivity.
        apply shift_shift_swap. lia.
    + (* ModalAt *)
      f_equal; apply shift_shift_swap; assumption.
    + (* ModalEventually *)
      f_equal; apply shift_shift_swap; assumption.
    + (* ModalAlways *)
      f_equal.
      * apply shift_shift_swap. assumption.
      * apply shift_shift_swap. assumption.
      * apply shift_shift_swap. assumption.
    + (* ModalIntro *)
      f_equal. apply shift_shift_swap. assumption.
    + (* ModalElim *)
      f_equal; apply shift_shift_swap; assumption.
    + (* Defeasible *)
      f_equal.
      * apply shift_shift_swap. assumption.
      * apply shift_shift_swap. assumption.
      * induction l as [| ex exs IH].
        -- reflexivity.
        -- simpl. f_equal.
           ++ apply shift_shift_swap_exception. assumption.
           ++ apply IH.
    + (* Hole *)
      f_equal. apply shift_shift_swap. assumption.
    + (* HoleFill *)
      f_equal; apply shift_shift_swap; assumption.
    + (* PrincipleBalance *)
      f_equal; apply shift_shift_swap; assumption.
    + (* Unlock *)
      f_equal; apply shift_shift_swap; assumption.
  (* --- Branch case --- *)
  - intros b c c' d m Hcc'. destruct b as [pat body]. simpl.
    destruct pat as [name arity |].
    + (* PCtor *)
      f_equal.
      replace (c' + m + arity) with ((c' + arity) + m) by lia.
      apply shift_shift_swap. lia.
    + (* PWild *)
      f_equal.
      rewrite Nat.add_0_r, Nat.add_0_r, Nat.add_0_r.
      apply shift_shift_swap. assumption.
  (* --- Exception case --- *)
  - intros e c c' d m Hcc'. destruct e as [guard body prio]. simpl.
    f_equal; apply shift_shift_swap; assumption.
Qed.

(** Specialization used by the binder cases of
    [shift_subst_commute_ws]: inner cutoff [0], lift [1]. *)
Lemma shift_shift_swap_0_1 : forall (s : Term) (c d : nat),
  shift (S c) d (shift 0 1 s) = shift 0 1 (shift c d s).
Proof.
  intros s c d.
  replace (S c) with (c + 1) by lia.
  apply shift_shift_swap. lia.
Qed.

(** Specialization used by the Branch case of
    [shift_subst_commute_ws]: inner cutoff [0], lift [arity]. *)
Lemma shift_shift_swap_0_arity : forall (s : Term) (c d arity : nat),
  shift (c + arity) d (shift 0 arity s) = shift 0 arity (shift c d s).
Proof.
  intros s c d arity.
  apply shift_shift_swap. lia.
Qed.

(** *** shift_subst_commute_ws - concrete Qed-closed mutual proof *)

(** The corrected-form lemma under the [well_scoped (S i) t] premise,
    proved by mutual structural induction on Term / Branch /
    Exception.  The Var case delegates to
    [shift_subst_commute_ws_var] above.  Non-binder constructors
    reduce to [f_equal] + IH on each subterm.  Binder constructors
    (Lambda / Pi / Sigma / Rec / Let) additionally use
    [shift_shift_swap_0_1] to commute the binder-lift through the
    substitute [s].  The Branch case uses [shift_shift_swap_0_arity]
    and [Nat_leb_add_r] to absorb the arity into the cutoff/target.
    The Match and Defeasible cases traverse their list subterms with
    an inner list induction dispatching to the Branch / Exception
    mutual partner. *)
Lemma shift_subst_commute_ws : forall (t s : Term) (i c d : nat),
  well_scoped (S i) t ->
  shift c d (subst i s t) =
  subst (if Nat.leb c i then i + d else i)
        (shift c d s)
        (shift c d t)
with shift_subst_commute_ws_branch : forall (b : Branch) (s : Term) (i c d : nat),
  well_scoped_branch (S i) b ->
  shift_branch c d (subst_branch i s b) =
  subst_branch (if Nat.leb c i then i + d else i)
               (shift c d s)
               (shift_branch c d b)
with shift_subst_commute_ws_exception : forall (e : Exception) (s : Term) (i c d : nat),
  well_scoped_exception (S i) e ->
  shift_exception c d (subst_exception i s e) =
  subst_exception (if Nat.leb c i then i + d else i)
                  (shift c d s)
                  (shift_exception c d e).
Proof.
  (* --- Term case --- *)
  - intros t s i c d Hws. destruct t; simpl in Hws.
    + (* Var *)
      apply shift_subst_commute_ws_var. exact Hws.
    + (* TSort *) simpl; reflexivity.
    + (* Constant *) simpl; reflexivity.
    + (* ContentRef *) simpl; reflexivity.
    + (* IntLit *) simpl; reflexivity.
    + (* RatLit *) simpl; reflexivity.
    + (* StringLit *) simpl; reflexivity.
    + (* AxiomUse *) simpl; reflexivity.
    + (* Pair *)
      destruct Hws as [H1 H2]. simpl. f_equal.
      * apply shift_subst_commute_ws. exact H1.
      * apply shift_subst_commute_ws. exact H2.
    + (* Proj *)
      simpl. f_equal. apply shift_subst_commute_ws. exact Hws.
    + (* App *)
      destruct Hws as [H1 H2]. simpl. f_equal.
      * apply shift_subst_commute_ws. exact H1.
      * apply shift_subst_commute_ws. exact H2.
    + (* InductiveIntro *)
      simpl. f_equal.
      induction l as [| x xs IH].
      * reflexivity.
      * simpl in Hws |- *. destruct Hws as [Hx Hrest]. f_equal.
        -- apply shift_subst_commute_ws. exact Hx.
        -- apply IH. exact Hrest.
    + (* SanctionsDominance *)
      simpl. f_equal. apply shift_subst_commute_ws. exact Hws.
    + (* DefeatElim *)
      simpl. f_equal. apply shift_subst_commute_ws. exact Hws.
    + (* Lift0 *)
      simpl. f_equal. apply shift_subst_commute_ws. exact Hws.
    + (* Derive1 *)
      destruct Hws as [H1 H2]. simpl. f_equal.
      * apply shift_subst_commute_ws. exact H1.
      * apply shift_subst_commute_ws. exact H2.
    + (* Lambda *)
      destruct Hws as [H1 H2]. simpl. f_equal.
      * apply shift_subst_commute_ws. exact H1.
      * (* body under binder *)
        rewrite (shift_subst_commute_ws t2 (shift 0 1 s) (S i) (S c) d H2).
        (* Goal: subst (if S c <=? S i then S i + d else S i) (shift (S c) d (shift 0 1 s)) (shift (S c) d t2)
                = subst (S (if c <=? i then i + d else i)) (shift 0 1 (shift c d s)) (shift (S c) d t2) *)
        rewrite shift_shift_swap_0_1.
        (* Goal: subst (if S c <=? S i then S i + d else S i) (shift 0 1 (shift c d s)) (shift (S c) d t2)
                = subst (S (if c <=? i then i + d else i)) (shift 0 1 (shift c d s)) (shift (S c) d t2) *)
        simpl. f_equal.
        destruct (Nat.leb c i) eqn:Hci; reflexivity.
    + (* Pi *)
      destruct Hws as [H1 H2]. simpl. f_equal.
      * apply shift_subst_commute_ws. exact H1.
      * rewrite (shift_subst_commute_ws t2 (shift 0 1 s) (S i) (S c) d H2).
        rewrite shift_shift_swap_0_1.
        simpl. f_equal.
        destruct (Nat.leb c i) eqn:Hci; reflexivity.
    + (* Sigma *)
      destruct Hws as [H1 H2]. simpl. f_equal.
      * apply shift_subst_commute_ws. exact H1.
      * rewrite (shift_subst_commute_ws t2 (shift 0 1 s) (S i) (S c) d H2).
        rewrite shift_shift_swap_0_1.
        simpl. f_equal.
        destruct (Nat.leb c i) eqn:Hci; reflexivity.
    + (* Annot *)
      destruct Hws as [H1 H2]. simpl. f_equal.
      * apply shift_subst_commute_ws. exact H1.
      * apply shift_subst_commute_ws. exact H2.
    + (* Let *)
      destruct Hws as [H1 [H2 H3]]. simpl. f_equal.
      * apply shift_subst_commute_ws. exact H1.
      * apply shift_subst_commute_ws. exact H2.
      * rewrite (shift_subst_commute_ws t3 (shift 0 1 s) (S i) (S c) d H3).
        rewrite shift_shift_swap_0_1.
        simpl. f_equal.
        destruct (Nat.leb c i) eqn:Hci; reflexivity.
    + (* Match *)
      destruct Hws as [H1 [H2 H3]]. simpl. f_equal.
      * apply shift_subst_commute_ws. exact H1.
      * apply shift_subst_commute_ws. exact H2.
      * induction l as [| br brs IH].
        -- reflexivity.
        -- simpl in H3 |- *. destruct H3 as [Hbr Hrest]. f_equal.
           ++ apply shift_subst_commute_ws_branch. exact Hbr.
           ++ apply IH. exact Hrest.
    + (* Rec *)
      destruct Hws as [H1 H2]. simpl. f_equal.
      * apply shift_subst_commute_ws. exact H1.
      * rewrite (shift_subst_commute_ws t2 (shift 0 1 s) (S i) (S c) d H2).
        rewrite shift_shift_swap_0_1.
        simpl. f_equal.
        destruct (Nat.leb c i) eqn:Hci; reflexivity.
    + (* ModalAt *)
      destruct Hws as [H1 H2]. simpl. f_equal.
      * apply shift_subst_commute_ws. exact H1.
      * apply shift_subst_commute_ws. exact H2.
    + (* ModalEventually *)
      destruct Hws as [H1 H2]. simpl. f_equal.
      * apply shift_subst_commute_ws. exact H1.
      * apply shift_subst_commute_ws. exact H2.
    + (* ModalAlways *)
      destruct Hws as [H1 [H2 H3]]. simpl. f_equal.
      * apply shift_subst_commute_ws. exact H1.
      * apply shift_subst_commute_ws. exact H2.
      * apply shift_subst_commute_ws. exact H3.
    + (* ModalIntro *)
      simpl. f_equal. apply shift_subst_commute_ws. exact Hws.
    + (* ModalElim *)
      destruct Hws as [H1 H2]. simpl. f_equal.
      * apply shift_subst_commute_ws. exact H1.
      * apply shift_subst_commute_ws. exact H2.
    + (* Defeasible *)
      destruct Hws as [H1 [H2 H3]]. simpl. f_equal.
      * apply shift_subst_commute_ws. exact H1.
      * apply shift_subst_commute_ws. exact H2.
      * induction l as [| ex exs IH].
        -- reflexivity.
        -- simpl in H3 |- *. destruct H3 as [Hex Hrest]. f_equal.
           ++ apply shift_subst_commute_ws_exception. exact Hex.
           ++ apply IH. exact Hrest.
    + (* Hole *)
      simpl. f_equal. apply shift_subst_commute_ws. exact Hws.
    + (* HoleFill *)
      destruct Hws as [H1 H2]. simpl. f_equal.
      * apply shift_subst_commute_ws. exact H1.
      * apply shift_subst_commute_ws. exact H2.
    + (* PrincipleBalance *)
      destruct Hws as [H1 H2]. simpl. f_equal.
      * apply shift_subst_commute_ws. exact H1.
      * apply shift_subst_commute_ws. exact H2.
    + (* Unlock *)
      destruct Hws as [H1 H2]. simpl. f_equal.
      * apply shift_subst_commute_ws. exact H1.
      * apply shift_subst_commute_ws. exact H2.
  (* --- Branch case --- *)
  - intros b s i c d Hws. destruct b as [pat body]. simpl.
    destruct pat as [name arity |]; simpl in Hws.
    + (* PCtor *)
      f_equal.
      (* Goal: shift (c + arity) d (subst (i + arity) (shift 0 arity s) body) =
               subst ((if c <=? i then i + d else i) + arity) (shift 0 arity (shift c d s)) (shift (c + arity) d body) *)
      (* well_scoped_branch (S i) (MkBranch (PCtor name arity) body) = well_scoped (S i + arity) body *)
      (* Note: S i + arity = S (i + arity) by reduction. *)
      assert (Hws' : well_scoped (S (i + arity)) body).
      { replace (S (i + arity)) with (S i + arity) by lia. exact Hws. }
      rewrite (shift_subst_commute_ws body (shift 0 arity s) (i + arity) (c + arity) d Hws').
      (* Goal: subst (if (c+arity) <=? (i+arity) then (i+arity) + d else (i+arity)) (shift (c+arity) d (shift 0 arity s)) (shift (c+arity) d body) =
               subst ((if c <=? i then i + d else i) + arity) (shift 0 arity (shift c d s)) (shift (c + arity) d body) *)
      rewrite shift_shift_swap_0_arity.
      (* Goal: subst (if (c+arity) <=? (i+arity) then (i+arity)+d else (i+arity)) (shift 0 arity (shift c d s)) (shift (c+arity) d body) =
               subst ((if c <=? i then i+d else i) + arity) (shift 0 arity (shift c d s)) (shift (c + arity) d body) *)
      f_equal.
      rewrite Nat_leb_add_r.
      destruct (Nat.leb c i) eqn:Hci; lia.
    + (* PWild *)
      f_equal.
      (* Goal: shift (c + 0) d (subst (i + 0) (shift 0 0 s) body) =
               subst ((if c <=? i then i + d else i) + 0) (shift 0 0 (shift c d s)) (shift (c + 0) d body) *)
      rewrite Nat.add_0_r in Hws.
      rewrite Nat.add_0_r, Nat.add_0_r, Nat.add_0_r.
      rewrite !shift_zero.
      apply shift_subst_commute_ws. exact Hws.
  (* --- Exception case --- *)
  - intros e s i c d Hws. destruct e as [guard body prio]. simpl in Hws.
    destruct Hws as [Hg Hb]. simpl. f_equal.
    + apply shift_subst_commute_ws. exact Hg.
    + apply shift_subst_commute_ws. exact Hb.
Qed.

(** [shift_subst_commute_ws_spec] is discharged by the concrete
    [shift_subst_commute_ws] Lemma above.  We expose both names so
    that downstream files that cite the [Prop] specification
    (e.g. [Lex.Requirements.req_shift_subst_commute_ws]) and files
    that want the concrete Lemma both compile cleanly. *)
Theorem shift_subst_commute_ws_spec_proof : shift_subst_commute_ws_spec.
Proof.
  unfold shift_subst_commute_ws_spec.
  exact shift_subst_commute_ws.
Qed.

Definition subst_subst_ws_spec : Prop :=
  forall (t r s : Term) (i j : nat),
    j <= i ->
    well_scoped (S i) t ->
    well_scoped (S i) r ->
    well_scoped (S i) s ->
    subst i s (subst j r t) =
    subst j (subst i s r) (subst (S i) (shift 0 1 s) t).

(** *** Well-scoped is preserved under shifting

    Auxiliary lemma used by the binder cases of [subst_subst_ws]:
    applying [shift c d] to a term well-scoped at [k] yields a term
    well-scoped at [k + d], because free variables above the cutoff
    are bumped by [d] and therefore stay strictly below [k + d], and
    free variables below the cutoff were already below [k <= k + d].

    Proved by mutual structural induction over Term / Branch /
    Exception.  List sub-term cases ([InductiveIntro], [Match],
    [Defeasible]) traverse their element list with an inner list
    induction dispatching to the Branch / Exception mutual
    partner. *)

Lemma well_scoped_shift : forall (t : Term) (k c d : nat),
  well_scoped k t -> well_scoped (k + d) (shift c d t)
with well_scoped_shift_branch : forall (b : Branch) (k c d : nat),
  well_scoped_branch k b -> well_scoped_branch (k + d) (shift_branch c d b)
with well_scoped_shift_exception : forall (e : Exception) (k c d : nat),
  well_scoped_exception k e -> well_scoped_exception (k + d) (shift_exception c d e).
Proof.
  (* --- Term case --- *)
  - intros t k c d Hws. destruct t; simpl in Hws; simpl.
    + (* Var *)
      destruct (Nat.leb c n) eqn:Hcn.
      * apply Nat.leb_le in Hcn. simpl. lia.
      * apply Nat.leb_nle in Hcn. simpl. lia.
    + (* TSort *) exact I.
    + (* Constant *) exact I.
    + (* ContentRef *) exact I.
    + (* IntLit *) exact I.
    + (* RatLit *) exact I.
    + (* StringLit *) exact I.
    + (* AxiomUse *) exact I.
    + (* Pair *)
      destruct Hws as [H1 H2]. split.
      * apply well_scoped_shift. exact H1.
      * apply well_scoped_shift. exact H2.
    + (* Proj *)
      apply well_scoped_shift. exact Hws.
    + (* App *)
      destruct Hws as [H1 H2]. split.
      * apply well_scoped_shift. exact H1.
      * apply well_scoped_shift. exact H2.
    + (* InductiveIntro *)
      induction l as [| x xs IH].
      * exact I.
      * simpl in Hws |- *. destruct Hws as [Hx Hrest]. split.
        -- apply well_scoped_shift. exact Hx.
        -- apply IH. exact Hrest.
    + (* SanctionsDominance *)
      apply well_scoped_shift. exact Hws.
    + (* DefeatElim *)
      apply well_scoped_shift. exact Hws.
    + (* Lift0 *)
      apply well_scoped_shift. exact Hws.
    + (* Derive1 *)
      destruct Hws as [H1 H2]. split.
      * apply well_scoped_shift. exact H1.
      * apply well_scoped_shift. exact H2.
    + (* Lambda *)
      destruct Hws as [H1 H2]. split.
      * apply well_scoped_shift. exact H1.
      * replace (S (k + d)) with (S k + d) by lia.
        apply well_scoped_shift. exact H2.
    + (* Pi *)
      destruct Hws as [H1 H2]. split.
      * apply well_scoped_shift. exact H1.
      * replace (S (k + d)) with (S k + d) by lia.
        apply well_scoped_shift. exact H2.
    + (* Sigma *)
      destruct Hws as [H1 H2]. split.
      * apply well_scoped_shift. exact H1.
      * replace (S (k + d)) with (S k + d) by lia.
        apply well_scoped_shift. exact H2.
    + (* Annot *)
      destruct Hws as [H1 H2]. split.
      * apply well_scoped_shift. exact H1.
      * apply well_scoped_shift. exact H2.
    + (* Let *)
      destruct Hws as [H1 [H2 H3]]. split; [| split].
      * apply well_scoped_shift. exact H1.
      * apply well_scoped_shift. exact H2.
      * replace (S (k + d)) with (S k + d) by lia.
        apply well_scoped_shift. exact H3.
    + (* Match *)
      destruct Hws as [H1 [H2 H3]]. split; [| split].
      * apply well_scoped_shift. exact H1.
      * apply well_scoped_shift. exact H2.
      * induction l as [| br brs IH].
        -- exact I.
        -- simpl in H3 |- *. destruct H3 as [Hbr Hrest]. split.
           ++ apply well_scoped_shift_branch. exact Hbr.
           ++ apply IH. exact Hrest.
    + (* Rec *)
      destruct Hws as [H1 H2]. split.
      * apply well_scoped_shift. exact H1.
      * replace (S (k + d)) with (S k + d) by lia.
        apply well_scoped_shift. exact H2.
    + (* ModalAt *)
      destruct Hws as [H1 H2]. split.
      * apply well_scoped_shift. exact H1.
      * apply well_scoped_shift. exact H2.
    + (* ModalEventually *)
      destruct Hws as [H1 H2]. split.
      * apply well_scoped_shift. exact H1.
      * apply well_scoped_shift. exact H2.
    + (* ModalAlways *)
      destruct Hws as [H1 [H2 H3]]. split; [| split].
      * apply well_scoped_shift. exact H1.
      * apply well_scoped_shift. exact H2.
      * apply well_scoped_shift. exact H3.
    + (* ModalIntro *)
      apply well_scoped_shift. exact Hws.
    + (* ModalElim *)
      destruct Hws as [H1 H2]. split.
      * apply well_scoped_shift. exact H1.
      * apply well_scoped_shift. exact H2.
    + (* Defeasible *)
      destruct Hws as [H1 [H2 H3]]. split; [| split].
      * apply well_scoped_shift. exact H1.
      * apply well_scoped_shift. exact H2.
      * induction l as [| ex exs IH].
        -- exact I.
        -- simpl in H3 |- *. destruct H3 as [Hex Hrest]. split.
           ++ apply well_scoped_shift_exception. exact Hex.
           ++ apply IH. exact Hrest.
    + (* Hole *)
      apply well_scoped_shift. exact Hws.
    + (* HoleFill *)
      destruct Hws as [H1 H2]. split.
      * apply well_scoped_shift. exact H1.
      * apply well_scoped_shift. exact H2.
    + (* PrincipleBalance *)
      destruct Hws as [H1 H2]. split.
      * apply well_scoped_shift. exact H1.
      * apply well_scoped_shift. exact H2.
    + (* Unlock *)
      destruct Hws as [H1 H2]. split.
      * apply well_scoped_shift. exact H1.
      * apply well_scoped_shift. exact H2.
  (* --- Branch case --- *)
  - intros b k c d Hws. destruct b as [pat body]. simpl.
    destruct pat as [name arity |]; simpl in Hws; simpl.
    + (* PCtor *)
      replace (k + d + arity) with ((k + arity) + d) by lia.
      apply well_scoped_shift. exact Hws.
    + (* PWild *)
      rewrite Nat.add_0_r in Hws |- *.
      rewrite Nat.add_0_r.
      apply well_scoped_shift. exact Hws.
  (* --- Exception case --- *)
  - intros e k c d Hws. destruct e as [guard body prio]. simpl in Hws.
    destruct Hws as [Hg Hb]. simpl. split.
    + apply well_scoped_shift. exact Hg.
    + apply well_scoped_shift. exact Hb.
Qed.

(** Specialization: [shift 0 1] bumps the well-scoped level by 1. *)
Lemma well_scoped_shift_0_1 : forall (t : Term) (k : nat),
  well_scoped k t -> well_scoped (S k) (shift 0 1 t).
Proof.
  intros t k Hws.
  replace (S k) with (k + 1) by lia.
  apply well_scoped_shift. exact Hws.
Qed.

(** Specialization: [shift 0 arity] bumps the well-scoped level by arity. *)
Lemma well_scoped_shift_0_arity : forall (t : Term) (k arity : nat),
  well_scoped k t -> well_scoped (k + arity) (shift 0 arity t).
Proof.
  intros t k arity Hws.
  apply well_scoped_shift. exact Hws.
Qed.

(** *** subst_subst_ws - concrete Qed-closed mutual proof

    Substitution composes under [well_scoped] premises.  The naive
    unconditional form is FALSE - refuted by
    [subst_subst_not_unconditional] above.  The corrected form,
    requiring [well_scoped (S i) t], [well_scoped (S i) r], and
    [well_scoped (S i) s], is the standard de Bruijn composition
    law (Autosubst / Benton et al.).

    Proved by mutual structural induction on Term / Branch /
    Exception.  The [Var] case enumerates the orderings of [n],
    [i], [j], [S i] - cases that would require [n > i] are ruled
    out by the [well_scoped] premise and closed by [lia].
    Non-binder constructors reduce to [f_equal] + IH on each
    subterm.  Binder constructors (Lambda / Pi / Sigma / Rec / Let)
    additionally use [shift_subst_commute_ws] to commute [shift 0 1]
    through [subst i s r], plus [well_scoped_shift_0_1] to
    propagate the well-scoped premise on [r] and [s] under the
    binder.  The Branch case uses [shift_subst_commute_ws] at
    [c := 0, d := arity] and [well_scoped_shift_0_arity]
    (plus [shift_shift] to reconcile iterated shifts).
    The Match and Defeasible cases traverse their list subterms
    with an inner list induction dispatching to the Branch /
    Exception mutual partner. *)

Lemma subst_subst_ws :
  forall (t r s : Term) (i j : nat),
    j <= i ->
    well_scoped (S i) t ->
    well_scoped (S i) r ->
    well_scoped (S i) s ->
    subst i s (subst j r t) =
    subst j (subst i s r) (subst (S i) (shift 0 1 s) t)
with subst_subst_ws_branch :
  forall (b : Branch) (r s : Term) (i j : nat),
    j <= i ->
    well_scoped_branch (S i) b ->
    well_scoped (S i) r ->
    well_scoped (S i) s ->
    subst_branch i s (subst_branch j r b) =
    subst_branch j (subst i s r) (subst_branch (S i) (shift 0 1 s) b)
with subst_subst_ws_exception :
  forall (e : Exception) (r s : Term) (i j : nat),
    j <= i ->
    well_scoped_exception (S i) e ->
    well_scoped (S i) r ->
    well_scoped (S i) s ->
    subst_exception i s (subst_exception j r e) =
    subst_exception j (subst i s r) (subst_exception (S i) (shift 0 1 s) e).
Proof.
  (* --- Term case --- *)
  - intros t r s i j Hji Hws Hr Hs. destruct t; simpl in Hws.
    + (* Var *)
      (* well_scoped (S i) (Var n) means n < S i, i.e. n <= i. *)
      assert (Hnle : n <= i) by lia.
      (* LHS: subst i s (subst j r (Var n)) *)
      simpl.
      destruct (Nat.eqb n j) eqn:Hnj.
      * (* n = j: inner subst returns r; outer returns subst i s r. *)
        apply Nat.eqb_eq in Hnj. subst n.
        (* RHS: subst j (subst i s r) (subst (S i) (shift 0 1 s) (Var j)) *)
        simpl.
        assert (HjSi : Nat.eqb j (S i) = false) by (apply Nat.eqb_neq; lia).
        rewrite HjSi.
        assert (HltSij : Nat.ltb (S i) j = false) by (apply Nat.ltb_nlt; lia).
        rewrite HltSij.
        simpl. rewrite Nat.eqb_refl. reflexivity.
      * (* n <> j *)
        destruct (Nat.ltb j n) eqn:Hjn.
        -- (* j < n.  With n <= i, we have j < n <= i.
              Inner returns Var (pred n). *)
           apply Nat.ltb_lt in Hjn. apply Nat.eqb_neq in Hnj.
           simpl.
           (* Outer: subst i s (Var (pred n)). *)
           destruct (Nat.eqb (pred n) i) eqn:Hpni.
           ++ (* pred n = i -> n = S i.  Contradicts n <= i. *)
              apply Nat.eqb_eq in Hpni.
              assert (n = S i) by lia. lia.
           ++ destruct (Nat.ltb i (pred n)) eqn:Hipn.
              ** (* i < pred n -> n > S i.  Contradicts n <= i. *)
                 apply Nat.ltb_lt in Hipn. lia.
              ** (* Otherwise: result is Var (pred n). *)
                 (* RHS: subst j (subst i s r) (subst (S i) (shift 0 1 s) (Var n)) *)
                 simpl.
                 assert (HnSi : Nat.eqb n (S i) = false) by (apply Nat.eqb_neq; lia).
                 rewrite HnSi.
                 assert (HltSin : Nat.ltb (S i) n = false) by (apply Nat.ltb_nlt; lia).
                 rewrite HltSin.
                 simpl.
                 assert (Hnj' : Nat.eqb n j = false) by (apply Nat.eqb_neq; assumption).
                 rewrite Hnj'.
                 assert (Hjn' : Nat.ltb j n = true) by (apply Nat.ltb_lt; exact Hjn).
                 rewrite Hjn'. reflexivity.
        -- (* n < j.  With j <= i, we have n < j <= i, so n < i, so n <> i. *)
           apply Nat.ltb_nlt in Hjn. apply Nat.eqb_neq in Hnj.
           assert (Hnltj : n < j) by lia.
           (* Inner returns Var n (unchanged). *)
           simpl.
           (* Outer: subst i s (Var n). *)
           destruct (Nat.eqb n i) eqn:Hni.
           ++ apply Nat.eqb_eq in Hni. lia.
           ++ destruct (Nat.ltb i n) eqn:Hin.
              ** apply Nat.ltb_lt in Hin. lia.
              ** (* Result: Var n. *)
                 (* RHS: subst j (subst i s r) (subst (S i) (shift 0 1 s) (Var n)) *)
                 simpl.
                 assert (HnSi : Nat.eqb n (S i) = false) by (apply Nat.eqb_neq; lia).
                 rewrite HnSi.
                 assert (HltSin : Nat.ltb (S i) n = false) by (apply Nat.ltb_nlt; lia).
                 rewrite HltSin.
                 simpl.
                 assert (Hnj' : Nat.eqb n j = false) by (apply Nat.eqb_neq; assumption).
                 rewrite Hnj'.
                 assert (Hjn'' : Nat.ltb j n = false) by (apply Nat.ltb_nlt; lia).
                 rewrite Hjn''. reflexivity.
    + (* TSort *) reflexivity.
    + (* Constant *) reflexivity.
    + (* ContentRef *) reflexivity.
    + (* IntLit *) reflexivity.
    + (* RatLit *) reflexivity.
    + (* StringLit *) reflexivity.
    + (* AxiomUse *) reflexivity.
    + (* Pair *)
      destruct Hws as [H1 H2]. simpl. f_equal.
      * apply subst_subst_ws; assumption.
      * apply subst_subst_ws; assumption.
    + (* Proj *)
      simpl. f_equal. apply subst_subst_ws; assumption.
    + (* App *)
      destruct Hws as [H1 H2]. simpl. f_equal.
      * apply subst_subst_ws; assumption.
      * apply subst_subst_ws; assumption.
    + (* InductiveIntro *)
      simpl. f_equal.
      induction l as [| x xs IH].
      * reflexivity.
      * simpl in Hws |- *. destruct Hws as [Hx Hrest]. f_equal.
        -- apply subst_subst_ws; assumption.
        -- apply IH. exact Hrest.
    + (* SanctionsDominance *)
      simpl. f_equal. apply subst_subst_ws; assumption.
    + (* DefeatElim *)
      simpl. f_equal. apply subst_subst_ws; assumption.
    + (* Lift0 *)
      simpl. f_equal. apply subst_subst_ws; assumption.
    + (* Derive1 *)
      destruct Hws as [H1 H2]. simpl. f_equal.
      * apply subst_subst_ws; assumption.
      * apply subst_subst_ws; assumption.
    + (* Lambda *)
      destruct Hws as [H1 H2]. simpl. f_equal.
      * apply subst_subst_ws; assumption.
      * (* body under binder.  Apply IH at (S i, S j, shift 0 1 r, shift 0 1 s). *)
        assert (HSji : S j <= S i) by lia.
        assert (Hr' : well_scoped (S (S i)) (shift 0 1 r)) by (apply well_scoped_shift_0_1; exact Hr).
        assert (Hs' : well_scoped (S (S i)) (shift 0 1 s)) by (apply well_scoped_shift_0_1; exact Hs).
        rewrite (subst_subst_ws t2 (shift 0 1 r) (shift 0 1 s) (S i) (S j) HSji H2 Hr' Hs').
        (* Goal: subst (S j) (subst (S i) (shift 0 1 s) (shift 0 1 r)) (subst (S (S i)) (shift 0 1 (shift 0 1 s)) t2)
                = subst (S j) (shift 0 1 (subst i s r)) (subst (S (S i)) (shift 0 1 (shift 0 1 s)) t2) *)
        f_equal.
        (* Goal: subst (S i) (shift 0 1 s) (shift 0 1 r) = shift 0 1 (subst i s r) *)
        rewrite (shift_subst_commute_ws r s i 0 1 Hr).
        (* RHS becomes subst (if 0 <=? i then i + 1 else i) (shift 0 1 s) (shift 0 1 r)
                     = subst (i + 1) (shift 0 1 s) (shift 0 1 r) *)
        simpl.
        replace (i + 1) with (S i) by lia.
        reflexivity.
    + (* Pi *)
      destruct Hws as [H1 H2]. simpl. f_equal.
      * apply subst_subst_ws; assumption.
      * assert (HSji : S j <= S i) by lia.
        assert (Hr' : well_scoped (S (S i)) (shift 0 1 r)) by (apply well_scoped_shift_0_1; exact Hr).
        assert (Hs' : well_scoped (S (S i)) (shift 0 1 s)) by (apply well_scoped_shift_0_1; exact Hs).
        rewrite (subst_subst_ws t2 (shift 0 1 r) (shift 0 1 s) (S i) (S j) HSji H2 Hr' Hs').
        f_equal.
        rewrite (shift_subst_commute_ws r s i 0 1 Hr).
        simpl.
        replace (i + 1) with (S i) by lia.
        reflexivity.
    + (* Sigma *)
      destruct Hws as [H1 H2]. simpl. f_equal.
      * apply subst_subst_ws; assumption.
      * assert (HSji : S j <= S i) by lia.
        assert (Hr' : well_scoped (S (S i)) (shift 0 1 r)) by (apply well_scoped_shift_0_1; exact Hr).
        assert (Hs' : well_scoped (S (S i)) (shift 0 1 s)) by (apply well_scoped_shift_0_1; exact Hs).
        rewrite (subst_subst_ws t2 (shift 0 1 r) (shift 0 1 s) (S i) (S j) HSji H2 Hr' Hs').
        f_equal.
        rewrite (shift_subst_commute_ws r s i 0 1 Hr).
        simpl.
        replace (i + 1) with (S i) by lia.
        reflexivity.
    + (* Annot *)
      destruct Hws as [H1 H2]. simpl. f_equal.
      * apply subst_subst_ws; assumption.
      * apply subst_subst_ws; assumption.
    + (* Let *)
      destruct Hws as [H1 [H2 H3]]. simpl. f_equal.
      * apply subst_subst_ws; assumption.
      * apply subst_subst_ws; assumption.
      * assert (HSji : S j <= S i) by lia.
        assert (Hr' : well_scoped (S (S i)) (shift 0 1 r)) by (apply well_scoped_shift_0_1; exact Hr).
        assert (Hs' : well_scoped (S (S i)) (shift 0 1 s)) by (apply well_scoped_shift_0_1; exact Hs).
        rewrite (subst_subst_ws t3 (shift 0 1 r) (shift 0 1 s) (S i) (S j) HSji H3 Hr' Hs').
        f_equal.
        rewrite (shift_subst_commute_ws r s i 0 1 Hr).
        simpl.
        replace (i + 1) with (S i) by lia.
        reflexivity.
    + (* Match *)
      destruct Hws as [H1 [H2 H3]]. simpl. f_equal.
      * apply subst_subst_ws; assumption.
      * apply subst_subst_ws; assumption.
      * induction l as [| br brs IH].
        -- reflexivity.
        -- simpl in H3 |- *. destruct H3 as [Hbr Hrest]. f_equal.
           ++ apply subst_subst_ws_branch; assumption.
           ++ apply IH. exact Hrest.
    + (* Rec *)
      destruct Hws as [H1 H2]. simpl. f_equal.
      * apply subst_subst_ws; assumption.
      * assert (HSji : S j <= S i) by lia.
        assert (Hr' : well_scoped (S (S i)) (shift 0 1 r)) by (apply well_scoped_shift_0_1; exact Hr).
        assert (Hs' : well_scoped (S (S i)) (shift 0 1 s)) by (apply well_scoped_shift_0_1; exact Hs).
        rewrite (subst_subst_ws t2 (shift 0 1 r) (shift 0 1 s) (S i) (S j) HSji H2 Hr' Hs').
        f_equal.
        rewrite (shift_subst_commute_ws r s i 0 1 Hr).
        simpl.
        replace (i + 1) with (S i) by lia.
        reflexivity.
    + (* ModalAt *)
      destruct Hws as [H1 H2]. simpl. f_equal.
      * apply subst_subst_ws; assumption.
      * apply subst_subst_ws; assumption.
    + (* ModalEventually *)
      destruct Hws as [H1 H2]. simpl. f_equal.
      * apply subst_subst_ws; assumption.
      * apply subst_subst_ws; assumption.
    + (* ModalAlways *)
      destruct Hws as [H1 [H2 H3]]. simpl. f_equal.
      * apply subst_subst_ws; assumption.
      * apply subst_subst_ws; assumption.
      * apply subst_subst_ws; assumption.
    + (* ModalIntro *)
      simpl. f_equal. apply subst_subst_ws; assumption.
    + (* ModalElim *)
      destruct Hws as [H1 H2]. simpl. f_equal.
      * apply subst_subst_ws; assumption.
      * apply subst_subst_ws; assumption.
    + (* Defeasible *)
      destruct Hws as [H1 [H2 H3]]. simpl. f_equal.
      * apply subst_subst_ws; assumption.
      * apply subst_subst_ws; assumption.
      * induction l as [| ex exs IH].
        -- reflexivity.
        -- simpl in H3 |- *. destruct H3 as [Hex Hrest]. f_equal.
           ++ apply subst_subst_ws_exception; assumption.
           ++ apply IH. exact Hrest.
    + (* Hole *)
      simpl. f_equal. apply subst_subst_ws; assumption.
    + (* HoleFill *)
      destruct Hws as [H1 H2]. simpl. f_equal.
      * apply subst_subst_ws; assumption.
      * apply subst_subst_ws; assumption.
    + (* PrincipleBalance *)
      destruct Hws as [H1 H2]. simpl. f_equal.
      * apply subst_subst_ws; assumption.
      * apply subst_subst_ws; assumption.
    + (* Unlock *)
      destruct Hws as [H1 H2]. simpl. f_equal.
      * apply subst_subst_ws; assumption.
      * apply subst_subst_ws; assumption.
  (* --- Branch case --- *)
  - intros b r s i j Hji Hws Hr Hs. destruct b as [pat body]. simpl.
    destruct pat as [name arity |]; simpl in Hws.
    + (* PCtor *)
      f_equal.
      (* Goal: subst (i + arity) (shift 0 arity s) (subst (j + arity) (shift 0 arity r) body)
               = subst (j + arity) (shift 0 arity (subst i s r)) (subst (S i + arity) (shift 0 arity (shift 0 1 s)) body) *)
      (* well_scoped_branch (S i) (MkBranch (PCtor name arity) body) = well_scoped (S i + arity) body *)
      assert (Hws' : well_scoped (S (i + arity)) body).
      { replace (S (i + arity)) with (S i + arity) by lia. exact Hws. }
      assert (Hjarity : j + arity <= i + arity) by lia.
      assert (Hr' : well_scoped (S (i + arity)) (shift 0 arity r)).
      { replace (S (i + arity)) with (S i + arity) by lia.
        apply well_scoped_shift_0_arity. exact Hr. }
      assert (Hs' : well_scoped (S (i + arity)) (shift 0 arity s)).
      { replace (S (i + arity)) with (S i + arity) by lia.
        apply well_scoped_shift_0_arity. exact Hs. }
      rewrite (subst_subst_ws body (shift 0 arity r) (shift 0 arity s) (i + arity) (j + arity) Hjarity Hws' Hr' Hs').
      (* Goal: subst (j + arity) (subst (i + arity) (shift 0 arity s) (shift 0 arity r)) (subst (S (i + arity)) (shift 0 1 (shift 0 arity s)) body)
               = subst (j + arity) (shift 0 arity (subst i s r)) (subst (S i + arity) (shift 0 arity (shift 0 1 s)) body) *)
      (* First, show the two bodies are equal: subst (S (i + arity)) (shift 0 1 (shift 0 arity s)) body
                                               = subst (S i + arity) (shift 0 arity (shift 0 1 s)) body *)
      (* Note: S (i + arity) = S i + arity.  And shift 0 1 (shift 0 arity s) = shift 0 (arity + 1) s = shift 0 arity (shift 0 1 s). *)
      rewrite (shift_shift 0 1 arity s).
      rewrite (shift_shift 0 arity 1 s).
      (* Now both sides have shift 0 (arity + 1) s / shift 0 (1 + arity) s. *)
      replace (S (i + arity)) with (S i + arity) by lia.
      replace (arity + 1) with (1 + arity) by lia.
      f_equal.
      (* Goal: subst (i + arity) (shift 0 arity s) (shift 0 arity r) = shift 0 arity (subst i s r) *)
      rewrite (shift_subst_commute_ws r s i 0 arity Hr).
      simpl. reflexivity.
    + (* PWild *)
      f_equal.
      rewrite Nat.add_0_r in Hws.
      (* Goal: subst (i + 0) (shift 0 0 s) (subst (j + 0) (shift 0 0 r) body)
               = subst (j + 0) (shift 0 0 (subst i s r)) (subst (S i + 0) (shift 0 0 (shift 0 1 s)) body) *)
      rewrite !Nat.add_0_r.
      rewrite !shift_zero.
      apply subst_subst_ws; assumption.
  (* --- Exception case --- *)
  - intros e r s i j Hji Hws Hr Hs. destruct e as [guard body prio]. simpl in Hws.
    destruct Hws as [Hg Hb]. simpl. f_equal.
    + apply subst_subst_ws; assumption.
    + apply subst_subst_ws; assumption.
Qed.

(** [subst_subst_ws_spec] is discharged by the concrete
    [subst_subst_ws] Lemma above.  We expose both names so that
    downstream files that cite the [Prop] specification
    (e.g. [Lex.Requirements.req_subst_subst_ws]) and files that
    want the concrete Lemma both compile cleanly. *)
Theorem subst_subst_ws_spec_proof : subst_subst_ws_spec.
Proof.
  unfold subst_subst_ws_spec.
  exact subst_subst_ws.
Qed.

(** *** subst_var_identity *)

(** Identity substitution: substituting a variable for itself is identity
    when every free variable is at most that index.

    This is the standard de Bruijn side condition used in Streicher- and
    Werner-style presentations: [well_scoped (S i) t] forbids the only
    problematic case, namely free variables strictly above [i], which would
    be decremented by substitution. *)
(** We prove the mutual variants simultaneously. *)
Lemma subst_var_identity : forall (i : nat) (t : Term),
  well_scoped (S i) t -> subst i (Var i) t = t
with subst_var_identity_branch : forall (i : nat) (b : Branch),
  well_scoped_branch (S i) b -> subst_branch i (Var i) b = b
with subst_var_identity_exception : forall (i : nat) (e : Exception),
  well_scoped_exception (S i) e -> subst_exception i (Var i) e = e.
Proof.
  (* --- Term case --- *)
  - intros i t. revert i.
    destruct t; intros i Hws; simpl in *; try reflexivity.
    + (* Var *)
      destruct (Nat.eqb n i) eqn:Heq.
      * apply Nat.eqb_eq in Heq. subst. reflexivity.
      * destruct (Nat.ltb i n) eqn:Hlt.
        -- apply Nat.ltb_lt in Hlt. lia.
        -- reflexivity.
    + (* Pair *)
      destruct Hws as [H1 H2]. f_equal.
      * apply subst_var_identity. exact H1.
      * apply subst_var_identity. exact H2.
    + (* Proj *)
      f_equal. apply subst_var_identity. exact Hws.
    + (* App *)
      destruct Hws as [H1 H2]. f_equal.
      * apply subst_var_identity. exact H1.
      * apply subst_var_identity. exact H2.
    + (* InductiveIntro *)
      f_equal. induction l as [| x xs IH].
      * reflexivity.
      * simpl in Hws |- *. destruct Hws as [H1 H2]. f_equal.
        -- apply subst_var_identity. exact H1.
        -- apply IH. exact H2.
    + (* SanctionsDominance *)
      f_equal. apply subst_var_identity. exact Hws.
    + (* DefeatElim *)
      f_equal. apply subst_var_identity. exact Hws.
    + (* Lift0 *)
      f_equal. apply subst_var_identity. exact Hws.
    + (* Derive1 *)
      destruct Hws as [H1 H2]. f_equal.
      * apply subst_var_identity. exact H1.
      * apply subst_var_identity. exact H2.
    + (* Lambda *)
      destruct Hws as [H1 H2]. simpl.
      rewrite (subst_var_identity i t1 H1).
      replace (Var (i + 1)) with (Var (S i)) by (f_equal; lia).
      rewrite (subst_var_identity (S i) t2 H2).
      reflexivity.
    + (* Pi *)
      destruct Hws as [H1 H2]. simpl.
      rewrite (subst_var_identity i t1 H1).
      replace (Var (i + 1)) with (Var (S i)) by (f_equal; lia).
      rewrite (subst_var_identity (S i) t2 H2).
      reflexivity.
    + (* Sigma *)
      destruct Hws as [H1 H2]. simpl.
      rewrite (subst_var_identity i t1 H1).
      replace (Var (i + 1)) with (Var (S i)) by (f_equal; lia).
      rewrite (subst_var_identity (S i) t2 H2).
      reflexivity.
    + (* Annot *)
      destruct Hws as [H1 H2]. f_equal.
      * apply subst_var_identity. exact H1.
      * apply subst_var_identity. exact H2.
    + (* Let *)
      destruct Hws as [H1 [H2 H3]]. simpl.
      rewrite (subst_var_identity i t1 H1).
      rewrite (subst_var_identity i t2 H2).
      replace (Var (i + 1)) with (Var (S i)) by (f_equal; lia).
      rewrite (subst_var_identity (S i) t3 H3).
      reflexivity.
    + (* Match *)
      destruct Hws as [H1 [H2 H3]]. simpl.
      rewrite (subst_var_identity i t1 H1).
      rewrite (subst_var_identity i t2 H2).
      f_equal.
      induction l as [| br brs IH].
      * reflexivity.
      * simpl in H3 |- *. destruct H3 as [Hbr Hrest]. f_equal.
        -- apply subst_var_identity_branch. exact Hbr.
        -- apply IH. exact Hrest.
    + (* Rec *)
      destruct Hws as [H1 H2]. simpl.
      rewrite (subst_var_identity i t1 H1).
      replace (Var (i + 1)) with (Var (S i)) by (f_equal; lia).
      rewrite (subst_var_identity (S i) t2 H2).
      reflexivity.
    + (* ModalAt *)
      destruct Hws as [H1 H2]. f_equal.
      * apply subst_var_identity. exact H1.
      * apply subst_var_identity. exact H2.
    + (* ModalEventually *)
      destruct Hws as [H1 H2]. f_equal.
      * apply subst_var_identity. exact H1.
      * apply subst_var_identity. exact H2.
    + (* ModalAlways *)
      destruct Hws as [H1 [H2 H3]]. f_equal.
      * apply subst_var_identity. exact H1.
      * apply subst_var_identity. exact H2.
      * apply subst_var_identity. exact H3.
    + (* ModalIntro *)
      f_equal. apply subst_var_identity. exact Hws.
    + (* ModalElim *)
      destruct Hws as [H1 H2]. f_equal;
      [apply subst_var_identity; exact H1
      |apply subst_var_identity; exact H2].
    + (* Defeasible *)
      destruct Hws as [H1 [H2 H3]]. simpl.
      rewrite (subst_var_identity i t1 H1).
      rewrite (subst_var_identity i t2 H2).
      f_equal.
      induction l as [| ex exs IH].
      * reflexivity.
      * simpl in H3 |- *. destruct H3 as [Hex Hrest]. f_equal.
        -- apply subst_var_identity_exception. exact Hex.
        -- apply IH. exact Hrest.
    + (* Hole *)
      f_equal. apply subst_var_identity. exact Hws.
    + (* HoleFill *)
      destruct Hws as [H1 H2]. f_equal.
      * apply subst_var_identity. exact H1.
      * apply subst_var_identity. exact H2.
    + (* PrincipleBalance *)
      destruct Hws as [H1 H2]. f_equal.
      * apply subst_var_identity. exact H1.
      * apply subst_var_identity. exact H2.
    + (* Unlock *)
      destruct Hws as [H1 H2]. f_equal.
      * apply subst_var_identity. exact H1.
      * apply subst_var_identity. exact H2.
  (* --- Branch case --- *)
  - intros i b. destruct b as [pat body]. simpl.
    destruct pat as [name arity |]; simpl; intros Hws.
    + f_equal. apply subst_var_identity. exact Hws.
    + rewrite Nat.add_0_r in Hws.
      replace (Var (i + 0)) with (Var i) by (f_equal; lia).
      replace (i + 0) with i by lia.
      f_equal. apply subst_var_identity. exact Hws.
  (* --- Exception case --- *)
  - intros i e. destruct e as [guard body prio]. simpl.
    intros [H1 H2]. f_equal;
    apply subst_var_identity; assumption.
Qed.

(* ================================================================== *)
(** ** Relaxed-depth commutation lemmas (task J2) *)
(* ================================================================== *)

(** The previous well_scoped-guarded commutation lemmas
    [shift_subst_commute_ws] and [subst_subst_ws] hardcode
    [well_scoped (S i) t] on the term.  Under binders
    (Lambda body, Let body, Pi codomain, Match branch body,
    Defeasible exception body), the substitution index [i]
    advances but the ambient well-scoped depth [k] advances
    with the surrounding typing context, which is typically
    larger than [S i].  The [_at_depth] variants below decouple
    the ambient scope depth [k] from the substitution index [i],
    thereby supporting the [substitution_preserves_typing] lemma
    where the typing context supplies [k] independent of [i].

    The generalization is NOT free - the Var case imposes
    conditions on [c] and [i] that were automatically satisfied
    by the tighter [well_scoped (S i) t] premise.  We mechanize
    both the negative results (naive relaxations that fail)
    and the Qed-closed positive results (the correct relaxed
    forms under the minimal sufficient side conditions).
*)

(* ------------------------------------------------------------------ *)
(** *** Refutation: naive [well_scoped k t]-only relaxation of         *)
(** *** [shift_subst_commute_ws] is false.                             *)
(* ------------------------------------------------------------------ *)

(** Witness: [t = Var 2], [s = Var 0], [i = 0], [c = 2], [d = 1],
    [k = 3].

    [well_scoped 3 (Var 2)] holds (Var 2 has index 2 < 3).
    [i = 0 < k = 3].  No constraint on [c] vs [i].

    - LHS: [shift 2 1 (subst 0 (Var 0) (Var 2))]
         = [shift 2 1 (Var 1)]   (subst: 2 > 0 → Var (pred 2))
         = [Var 1]               (shift: 2 > 1, no bump)
    - RHS: [subst (if 2 <=? 0 then 0+1 else 0) (shift 2 1 (Var 0))
              (shift 2 1 (Var 2))]
         = [subst 0 (Var 0) (Var 3)]   (2 <= 2 so bumped)
         = [Var 2]                      (0 < 3 → Var (pred 3))

    LHS = [Var 1] ≠ [Var 2] = RHS.  The naive relaxation fails
    in the boundary regime [n = c > i].  This exactly matches
    the Case 2b obstruction: when the shift cutoff lands on
    [n > i], the shift on [t] (after subst) hits a decremented
    index while the shift-then-subst sequence on the RHS fires
    at a different offset.
*)

Theorem shift_subst_commute_ws_at_depth_naive_false :
  ~ (forall (t s : Term) (i c d k : nat),
        well_scoped k t ->
        shift c d (subst i s t) =
        subst (if Nat.leb c i then i + d else i)
              (shift c d s)
              (shift c d t)).
Proof.
  intro H.
  specialize (H (Var 2) (Var 0) 0 2 1 3).
  simpl in H.
  assert (Hws : 2 < 3) by lia.
  specialize (H Hws).
  discriminate H.
Qed.

(* ------------------------------------------------------------------ *)
(** *** Refutation: the [shift (S c) d t] variant is also false.       *)
(* ------------------------------------------------------------------ *)

(** A natural attempt to salvage the Case 2b obstruction is to
    bump the cutoff on [t] by one: replace [shift c d t] with
    [shift (S c) d t] on the RHS.  This repairs the [n = c > i]
    boundary but breaks the [n = i = c] boundary when [c = i]
    (the shift no longer fires on the subst target variable,
    but the subst on the RHS still expects [Var (i + d)]).

    Witness: [t = Var 0], [s = Var 0], [i = 0], [c = 0], [d = 1],
    [k = 1].

    [well_scoped 1 (Var 0)] holds.  [i = 0 < k = 1].

    - LHS: [shift 0 1 (subst 0 (Var 0) (Var 0))]
         = [shift 0 1 (Var 0)]   (subst: 0 = 0 → s = Var 0)
         = [Var 1]               (shift: 0 <= 0, bump)
    - RHS: [subst (if 0 <=? 0 then 0+1 else 0) (shift 0 1 (Var 0))
              (shift (S 0) 1 (Var 0))]
         = [subst 1 (Var 1) (Var 0)]   (S 0 = 1 > 0, no bump on t)
         = [Var 0]                      (0 < 1: subst target higher, Var 0)

    LHS = [Var 1] ≠ [Var 0] = RHS.

    The correct relaxation imposes [c <= i] as a side condition
    (see [shift_subst_commute_ws_at_depth] below), making the
    boundary case impossible because [c = i] with [c <= i] is
    fine only when the shift still fires on the subst target.
*)

Theorem shift_subst_commute_ws_at_depth_Sc_false :
  ~ (forall (t s : Term) (i c d k : nat),
        well_scoped k t ->
        shift c d (subst i s t) =
        subst (if Nat.leb c i then i + d else i)
              (shift c d s)
              (shift (S c) d t)).
Proof.
  intro H.
  specialize (H (Var 0) (Var 0) 0 0 1 1).
  simpl in H.
  assert (Hws : 0 < 1) by lia.
  specialize (H Hws).
  discriminate H.
Qed.

(* ------------------------------------------------------------------ *)
(** *** Positive: relaxed-depth shift_subst_commute under [c <= i].    *)
(* ------------------------------------------------------------------ *)

(** The correct relaxation carries a side condition [c <= i]
    (shift cutoff at or below the substitution target), which is
    exactly the regime where the shift-subst commutation law
    holds unconditionally on scope depth.  In the preservation
    proof, substitutions happen at index 0 on beta-reduction,
    so [c = 0 <= i = 0] always, and this is the natural premise.

    Under [c <= i], [if c <=? i then i + d else i] simplifies to
    [i + d], which we expose in the statement. *)

Lemma shift_subst_commute_ws_at_depth_var :
  forall (n : nat) (s : Term) (i c d k : nat),
    n < k ->
    i < k ->
    c <= i ->
    shift c d (subst i s (Var n)) =
    subst (i + d)
          (shift c d s)
          (shift c d (Var n)).
Proof.
  intros n s i c d k Hnk Hik Hci.
  (* Case analysis on n ?= i, then on n ?< i. *)
  destruct (Nat.eq_dec n i) as [Heqni | Hneqni].
  - (* n = i.  LHS: subst i s (Var i) = s, then shift c d s. *)
    subst n.
    unfold subst. rewrite Nat.eqb_refl.
    (* RHS: shift c d (Var i) = Var (i + d) (c <= i so bumped),
            then subst (i+d) (shift c d s) hits it, yielding shift c d s. *)
    simpl.
    assert (Hleb : Nat.leb c i = true) by (apply Nat.leb_le; exact Hci).
    rewrite Hleb.
    rewrite Nat.eqb_refl.
    reflexivity.
  - (* n <> i. *)
    destruct (Nat.ltb i n) eqn:Hin.
    + (* n > i. *)
      apply Nat.ltb_lt in Hin.
      unfold subst.
      assert (Hne : Nat.eqb n i = false) by (apply Nat.eqb_neq; exact Hneqni).
      rewrite Hne.
      assert (Hltf : Nat.ltb i n = true) by (apply Nat.ltb_lt; exact Hin).
      rewrite Hltf.
      (* LHS: shift c d (Var (pred n)).  pred n >= i >= c, so c <= pred n,
              shift bumps to Var (pred n + d). *)
      simpl.
      assert (Hcpn : Nat.leb c (pred n) = true).
      { apply Nat.leb_le. destruct n; [lia | simpl; lia]. }
      rewrite Hcpn.
      (* RHS: shift c d (Var n) = Var (n + d) (c <= pred n < n, so c < n,
              i.e., c <= n). *)
      assert (Hcn : Nat.leb c n = true).
      { apply Nat.leb_le. lia. }
      rewrite Hcn.
      (* Then subst (i + d) ... (Var (n + d)): n + d > i + d, decrements. *)
      assert (Hne2 : Nat.eqb (n + d) (i + d) = false) by (apply Nat.eqb_neq; lia).
      rewrite Hne2.
      assert (Hltf2 : Nat.ltb (i + d) (n + d) = true) by (apply Nat.ltb_lt; lia).
      rewrite Hltf2.
      f_equal. destruct n; [lia | simpl; lia].
    + (* n < i. *)
      apply Nat.ltb_nlt in Hin.
      assert (Hnlti : n < i) by lia.
      unfold subst.
      assert (Hne : Nat.eqb n i = false) by (apply Nat.eqb_neq; exact Hneqni).
      rewrite Hne.
      assert (Hltf : Nat.ltb i n = false) by (apply Nat.ltb_nlt; lia).
      rewrite Hltf.
      (* LHS: shift c d (Var n).  Depends on c <= n. *)
      simpl.
      destruct (Nat.leb c n) eqn:Hcn.
      * apply Nat.leb_le in Hcn.
        (* RHS: shift c d (Var n) = Var (n + d) (c <= n).
                Then subst (i+d) (shift c d s) (Var (n+d)): n+d < i+d, Var (n+d). *)
        assert (Hne2 : Nat.eqb (n + d) (i + d) = false) by (apply Nat.eqb_neq; lia).
        rewrite Hne2.
        assert (Hltf2 : Nat.ltb (i + d) (n + d) = false) by (apply Nat.ltb_nlt; lia).
        rewrite Hltf2. reflexivity.
      * apply Nat.leb_nle in Hcn.
        (* RHS: shift c d (Var n) = Var n (c > n).
                subst (i+d) (shift c d s) (Var n): n < i < i+d, Var n. *)
        assert (Hne2 : Nat.eqb n (i + d) = false) by (apply Nat.eqb_neq; lia).
        rewrite Hne2.
        assert (Hltf2 : Nat.ltb (i + d) n = false) by (apply Nat.ltb_nlt; lia).
        rewrite Hltf2. reflexivity.
Qed.

(** [shift_subst_commute_ws_at_depth]: the full relaxed-depth form,
    by mutual structural induction on Term / Branch / Exception.
    Under the [c <= i] side condition, every Var case works,
    non-binder constructors reduce to [f_equal + IH] on subterms,
    and binder cases preserve the invariant [c <= i] under [S c, S i]
    via [shift_shift_swap_0_1] and trivial arithmetic.

    The [i + d] conclusion uses the fact that [c <= i] implies
    [if c <=? i then i + d else i = i + d]. *)

Lemma shift_subst_commute_ws_at_depth :
  forall (t s : Term) (i c d k : nat),
    well_scoped k t ->
    i < k ->
    c <= i ->
    shift c d (subst i s t) =
    subst (i + d)
          (shift c d s)
          (shift c d t)
with shift_subst_commute_ws_at_depth_branch :
  forall (b : Branch) (s : Term) (i c d k : nat),
    well_scoped_branch k b ->
    i < k ->
    c <= i ->
    shift_branch c d (subst_branch i s b) =
    subst_branch (i + d)
                 (shift c d s)
                 (shift_branch c d b)
with shift_subst_commute_ws_at_depth_exception :
  forall (e : Exception) (s : Term) (i c d k : nat),
    well_scoped_exception k e ->
    i < k ->
    c <= i ->
    shift_exception c d (subst_exception i s e) =
    subst_exception (i + d)
                    (shift c d s)
                    (shift_exception c d e).
Proof.
  (* --- Term case --- *)
  - intros t s i c d k Hws Hik Hci. destruct t; simpl in Hws.
    + (* Var *)
      eapply shift_subst_commute_ws_at_depth_var; eassumption.
    + (* TSort *) simpl; reflexivity.
    + (* Constant *) simpl; reflexivity.
    + (* ContentRef *) simpl; reflexivity.
    + (* IntLit *) simpl; reflexivity.
    + (* RatLit *) simpl; reflexivity.
    + (* StringLit *) simpl; reflexivity.
    + (* AxiomUse *) simpl; reflexivity.
    + (* Pair *)
      destruct Hws as [H1 H2]. simpl. f_equal.
      * eapply shift_subst_commute_ws_at_depth; eassumption.
      * eapply shift_subst_commute_ws_at_depth; eassumption.
    + (* Proj *)
      simpl. f_equal. eapply shift_subst_commute_ws_at_depth; eassumption.
    + (* App *)
      destruct Hws as [H1 H2]. simpl. f_equal.
      * eapply shift_subst_commute_ws_at_depth; eassumption.
      * eapply shift_subst_commute_ws_at_depth; eassumption.
    + (* InductiveIntro *)
      simpl. f_equal.
      induction l as [| x xs IH].
      * reflexivity.
      * simpl in Hws |- *. destruct Hws as [Hx Hrest]. f_equal.
        -- eapply shift_subst_commute_ws_at_depth; eassumption.
        -- apply IH. exact Hrest.
    + (* SanctionsDominance *)
      simpl. f_equal. eapply shift_subst_commute_ws_at_depth; eassumption.
    + (* DefeatElim *)
      simpl. f_equal. eapply shift_subst_commute_ws_at_depth; eassumption.
    + (* Lift0 *)
      simpl. f_equal. eapply shift_subst_commute_ws_at_depth; eassumption.
    + (* Derive1 *)
      destruct Hws as [H1 H2]. simpl. f_equal.
      * eapply shift_subst_commute_ws_at_depth; eassumption.
      * eapply shift_subst_commute_ws_at_depth; eassumption.
    + (* Lambda *)
      destruct Hws as [H1 H2]. simpl. f_equal.
      * eapply shift_subst_commute_ws_at_depth; eassumption.
      * (* body under binder: IH at (t2, shift 0 1 s, S i, S c, d, S k). *)
        assert (HSik : S i < S k) by lia.
        assert (HSci : S c <= S i) by lia.
        rewrite (shift_subst_commute_ws_at_depth
                   t2 (shift 0 1 s) (S i) (S c) d (S k) H2 HSik HSci).
        (* Goal: subst (S i + d) (shift (S c) d (shift 0 1 s)) (shift (S c) d t2)
                = subst (i + d + 1) (shift 0 1 (shift c d s)) (shift (S c) d t2).
           The right side comes from the outer lemma: its substitution
           index is [i+d] under one binder, and simplification under
           [Lambda] gives [S (i+d)]. *)
        rewrite shift_shift_swap_0_1.
        simpl. reflexivity.
    + (* Pi *)
      destruct Hws as [H1 H2]. simpl. f_equal.
      * eapply shift_subst_commute_ws_at_depth; eassumption.
      * assert (HSik : S i < S k) by lia.
        assert (HSci : S c <= S i) by lia.
        rewrite (shift_subst_commute_ws_at_depth
                   t2 (shift 0 1 s) (S i) (S c) d (S k) H2 HSik HSci).
        rewrite shift_shift_swap_0_1.
        simpl. reflexivity.
    + (* Sigma *)
      destruct Hws as [H1 H2]. simpl. f_equal.
      * eapply shift_subst_commute_ws_at_depth; eassumption.
      * assert (HSik : S i < S k) by lia.
        assert (HSci : S c <= S i) by lia.
        rewrite (shift_subst_commute_ws_at_depth
                   t2 (shift 0 1 s) (S i) (S c) d (S k) H2 HSik HSci).
        rewrite shift_shift_swap_0_1.
        simpl. reflexivity.
    + (* Annot *)
      destruct Hws as [H1 H2]. simpl. f_equal.
      * eapply shift_subst_commute_ws_at_depth; eassumption.
      * eapply shift_subst_commute_ws_at_depth; eassumption.
    + (* Let *)
      destruct Hws as [H1 [H2 H3]]. simpl. f_equal.
      * eapply shift_subst_commute_ws_at_depth; eassumption.
      * eapply shift_subst_commute_ws_at_depth; eassumption.
      * assert (HSik : S i < S k) by lia.
        assert (HSci : S c <= S i) by lia.
        rewrite (shift_subst_commute_ws_at_depth
                   t3 (shift 0 1 s) (S i) (S c) d (S k) H3 HSik HSci).
        rewrite shift_shift_swap_0_1.
        simpl. reflexivity.
    + (* Match *)
      destruct Hws as [H1 [H2 H3]]. simpl. f_equal.
      * eapply shift_subst_commute_ws_at_depth; eassumption.
      * eapply shift_subst_commute_ws_at_depth; eassumption.
      * induction l as [| br brs IH].
        -- reflexivity.
        -- simpl in H3 |- *. destruct H3 as [Hbr Hrest]. f_equal.
           ++ eapply shift_subst_commute_ws_at_depth_branch; eassumption.
           ++ apply IH. exact Hrest.
    + (* Rec *)
      destruct Hws as [H1 H2]. simpl. f_equal.
      * eapply shift_subst_commute_ws_at_depth; eassumption.
      * assert (HSik : S i < S k) by lia.
        assert (HSci : S c <= S i) by lia.
        rewrite (shift_subst_commute_ws_at_depth
                   t2 (shift 0 1 s) (S i) (S c) d (S k) H2 HSik HSci).
        rewrite shift_shift_swap_0_1.
        simpl. reflexivity.
    + (* ModalAt *)
      destruct Hws as [H1 H2]. simpl. f_equal.
      * eapply shift_subst_commute_ws_at_depth; eassumption.
      * eapply shift_subst_commute_ws_at_depth; eassumption.
    + (* ModalEventually *)
      destruct Hws as [H1 H2]. simpl. f_equal.
      * eapply shift_subst_commute_ws_at_depth; eassumption.
      * eapply shift_subst_commute_ws_at_depth; eassumption.
    + (* ModalAlways *)
      destruct Hws as [H1 [H2 H3]]. simpl. f_equal.
      * eapply shift_subst_commute_ws_at_depth; eassumption.
      * eapply shift_subst_commute_ws_at_depth; eassumption.
      * eapply shift_subst_commute_ws_at_depth; eassumption.
    + (* ModalIntro *)
      simpl. f_equal. eapply shift_subst_commute_ws_at_depth; eassumption.
    + (* ModalElim *)
      destruct Hws as [H1 H2]. simpl. f_equal.
      * eapply shift_subst_commute_ws_at_depth; eassumption.
      * eapply shift_subst_commute_ws_at_depth; eassumption.
    + (* Defeasible *)
      destruct Hws as [H1 [H2 H3]]. simpl. f_equal.
      * eapply shift_subst_commute_ws_at_depth; eassumption.
      * eapply shift_subst_commute_ws_at_depth; eassumption.
      * induction l as [| ex exs IH].
        -- reflexivity.
        -- simpl in H3 |- *. destruct H3 as [Hex Hrest]. f_equal.
           ++ eapply shift_subst_commute_ws_at_depth_exception; eassumption.
           ++ apply IH. exact Hrest.
    + (* Hole *)
      simpl. f_equal. eapply shift_subst_commute_ws_at_depth; eassumption.
    + (* HoleFill *)
      destruct Hws as [H1 H2]. simpl. f_equal.
      * eapply shift_subst_commute_ws_at_depth; eassumption.
      * eapply shift_subst_commute_ws_at_depth; eassumption.
    + (* PrincipleBalance *)
      destruct Hws as [H1 H2]. simpl. f_equal.
      * eapply shift_subst_commute_ws_at_depth; eassumption.
      * eapply shift_subst_commute_ws_at_depth; eassumption.
    + (* Unlock *)
      destruct Hws as [H1 H2]. simpl. f_equal.
      * eapply shift_subst_commute_ws_at_depth; eassumption.
      * eapply shift_subst_commute_ws_at_depth; eassumption.
  (* --- Branch case --- *)
  - intros b s i c d k Hws Hik Hci. destruct b as [pat body]. simpl.
    destruct pat as [name arity |]; simpl in Hws.
    + (* PCtor *)
      f_equal.
      (* IH at (body, shift 0 arity s, i + arity, c + arity, d, k + arity). *)
      assert (Hiarity : i + arity < k + arity) by lia.
      assert (Hcarity : c + arity <= i + arity) by lia.
      rewrite (shift_subst_commute_ws_at_depth
                 body (shift 0 arity s) (i + arity) (c + arity) d (k + arity)
                 Hws Hiarity Hcarity).
      rewrite shift_shift_swap_0_arity.
      f_equal. lia.
    + (* PWild *)
      f_equal.
      rewrite Nat.add_0_r in Hws.
      rewrite Nat.add_0_r, Nat.add_0_r, Nat.add_0_r.
      rewrite !shift_zero.
      eapply shift_subst_commute_ws_at_depth; eassumption.
  (* --- Exception case --- *)
  - intros e s i c d k Hws Hik Hci. destruct e as [guard body prio]. simpl in Hws.
    destruct Hws as [Hg Hb]. simpl. f_equal.
    + eapply shift_subst_commute_ws_at_depth; eassumption.
    + eapply shift_subst_commute_ws_at_depth; eassumption.
Qed.

(* ------------------------------------------------------------------ *)
(** *** Refutation: naive [well_scoped k t]-only relaxation of         *)
(** *** [subst_subst_ws] is false.                                     *)
(* ------------------------------------------------------------------ *)

(** Witness: [t = Var 2], [r = Var 2], [s = Var 0], [i = 1], [j = 1],
    [k = 3].  All of [t, r, s] are well-scoped at [k = 3].
    [j = 1 <= i = 1].

    - LHS: [subst 1 (Var 0) (subst 1 (Var 2) (Var 2))]
         = [subst 1 (Var 0) (Var 2)]  (subst: 1 = 2? no; 1 < 2 gives Var 1)
         with [subst 1 (Var 2) (Var 2) = Var 1]
         = [subst 1 (Var 0) (Var 1)] = [Var 0]   (1 = 1 gives replacement)
    - RHS: [subst 1 (subst 1 (Var 0) (Var 2)) (subst 2 (shift 0 1 (Var 0)) (Var 2))]
         = [subst 1 (Var 1) (subst 2 (Var 1) (Var 2))]
               (subst 1 (Var 0) (Var 2) = Var 1; shift 0 1 (Var 0) = Var 1)
         = [subst 1 (Var 1) (shift 0 1 (Var 0))]
               where [subst 2 (Var 1) (Var 2) = Var 1]
         = [subst 1 (Var 1) (Var 1)] = [Var 1]

    LHS = [Var 0] ≠ [Var 1] = RHS.

    The obstruction is the case [n = S i] (here n = 2, i = 1),
    which the [well_scoped (S i) t] premise forbids but the
    relaxed [well_scoped k t] permits.  In this case, the LHS's
    inner subst decrements [n] to [pred n = i], which the outer
    subst at [i] then replaces with [s].  On the RHS, [subst
    (S i)] hits the exact index, replacing with [shift 0 1 s],
    which is NOT equal to [s] in general (it's shifted up by 1).
*)

Theorem subst_subst_ws_at_depth_naive_false :
  ~ (forall (t r s : Term) (i j k : nat),
        j <= i ->
        well_scoped k t ->
        well_scoped k r ->
        well_scoped k s ->
        i < k ->
        subst i s (subst j r t) =
        subst j (subst i s r) (subst (S i) (shift 0 1 s) t)).
Proof.
  intro H.
  specialize (H (Var 2) (Var 2) (Var 0) 1 1 3).
  simpl in H.
  assert (Hji : 1 <= 1) by lia.
  assert (Hwst : 2 < 3) by lia.
  assert (Hwsr : 2 < 3) by lia.
  assert (Hwss : 0 < 3) by lia.
  assert (Hik : 1 < 3) by lia.
  specialize (H Hji Hwst Hwsr Hwss Hik).
  discriminate H.
Qed.

(* ------------------------------------------------------------------ *)
(** *** Positive: relaxed-depth [subst_subst_ws] for [r] and [s] only. *)
(* ------------------------------------------------------------------ *)

(** The obstruction above (case [n = S i] in [t]) forces us to
    retain [well_scoped (S i) t] as a premise on [t].  The
    relaxation we CAN perform is on [r] and [s]: these can live
    at an arbitrary ambient depth [k >= S i].  In the
    preservation proof, this matches the fact that the argument
    [r] and the substituted value [s] come from a typing
    context larger than the immediate binder depth.

    Premise shape (task J2): [well_scoped (S i) t] on the term
    being substituted into, but [well_scoped k r] and
    [well_scoped k s] at arbitrary [k >= S i] (expressed as
    [S i <= k]).

    The binder case uses [well_scoped_shift_0_1] to propagate
    [well_scoped k r/s] to [well_scoped (S k) (shift 0 1 r/s)],
    preserving the invariant [S (S i) <= S k] for the IH.
    The shift-subst reconciliation uses
    [shift_subst_commute_ws_at_depth] at [c = 0], [d = 1],
    which requires [0 <= i] (always true) and [i < k].
*)

Lemma subst_subst_ws_at_depth :
  forall (t r s : Term) (i j k : nat),
    j <= i ->
    well_scoped (S i) t ->
    S i <= k ->
    well_scoped k r ->
    well_scoped k s ->
    subst i s (subst j r t) =
    subst j (subst i s r) (subst (S i) (shift 0 1 s) t)
with subst_subst_ws_at_depth_branch :
  forall (b : Branch) (r s : Term) (i j k : nat),
    j <= i ->
    well_scoped_branch (S i) b ->
    S i <= k ->
    well_scoped k r ->
    well_scoped k s ->
    subst_branch i s (subst_branch j r b) =
    subst_branch j (subst i s r) (subst_branch (S i) (shift 0 1 s) b)
with subst_subst_ws_at_depth_exception :
  forall (e : Exception) (r s : Term) (i j k : nat),
    j <= i ->
    well_scoped_exception (S i) e ->
    S i <= k ->
    well_scoped k r ->
    well_scoped k s ->
    subst_exception i s (subst_exception j r e) =
    subst_exception j (subst i s r) (subst_exception (S i) (shift 0 1 s) e).
Proof.
  (* --- Term case --- *)
  - intros t r s i j k Hji Hws Hik Hr Hs. destruct t; simpl in Hws.
    + (* Var *)
      (* well_scoped (S i) (Var n) means n < S i, i.e. n <= i.
         The Var case is identical to subst_subst_ws: the premise
         on t (tight bound) is unchanged.  We reproduce the
         case analysis. *)
      assert (Hnle : n <= i) by lia.
      simpl.
      destruct (Nat.eqb n j) eqn:Hnj.
      * apply Nat.eqb_eq in Hnj. subst n.
        simpl.
        assert (HjSi : Nat.eqb j (S i) = false) by (apply Nat.eqb_neq; lia).
        rewrite HjSi.
        assert (HltSij : Nat.ltb (S i) j = false) by (apply Nat.ltb_nlt; lia).
        rewrite HltSij.
        simpl. rewrite Nat.eqb_refl. reflexivity.
      * destruct (Nat.ltb j n) eqn:Hjn.
        -- apply Nat.ltb_lt in Hjn. apply Nat.eqb_neq in Hnj.
           simpl.
           destruct (Nat.eqb (pred n) i) eqn:Hpni.
           ++ apply Nat.eqb_eq in Hpni.
              assert (n = S i) by lia. lia.
           ++ destruct (Nat.ltb i (pred n)) eqn:Hipn.
              ** apply Nat.ltb_lt in Hipn. lia.
              ** simpl.
                 assert (HnSi : Nat.eqb n (S i) = false) by (apply Nat.eqb_neq; lia).
                 rewrite HnSi.
                 assert (HltSin : Nat.ltb (S i) n = false) by (apply Nat.ltb_nlt; lia).
                 rewrite HltSin.
                 simpl.
                 assert (Hnj' : Nat.eqb n j = false) by (apply Nat.eqb_neq; assumption).
                 rewrite Hnj'.
                 assert (Hjn' : Nat.ltb j n = true) by (apply Nat.ltb_lt; exact Hjn).
                 rewrite Hjn'. reflexivity.
        -- apply Nat.ltb_nlt in Hjn. apply Nat.eqb_neq in Hnj.
           assert (Hnltj : n < j) by lia.
           simpl.
           destruct (Nat.eqb n i) eqn:Hni.
           ++ apply Nat.eqb_eq in Hni. lia.
           ++ destruct (Nat.ltb i n) eqn:Hin.
              ** apply Nat.ltb_lt in Hin. lia.
              ** simpl.
                 assert (HnSi : Nat.eqb n (S i) = false) by (apply Nat.eqb_neq; lia).
                 rewrite HnSi.
                 assert (HltSin : Nat.ltb (S i) n = false) by (apply Nat.ltb_nlt; lia).
                 rewrite HltSin.
                 simpl.
                 assert (Hnj' : Nat.eqb n j = false) by (apply Nat.eqb_neq; assumption).
                 rewrite Hnj'.
                 assert (Hjn'' : Nat.ltb j n = false) by (apply Nat.ltb_nlt; lia).
                 rewrite Hjn''. reflexivity.
    + (* TSort *) reflexivity.
    + (* Constant *) reflexivity.
    + (* ContentRef *) reflexivity.
    + (* IntLit *) reflexivity.
    + (* RatLit *) reflexivity.
    + (* StringLit *) reflexivity.
    + (* AxiomUse *) reflexivity.
    + (* Pair *)
      destruct Hws as [H1 H2]. simpl. f_equal.
      * eapply subst_subst_ws_at_depth; eassumption.
      * eapply subst_subst_ws_at_depth; eassumption.
    + (* Proj *)
      simpl. f_equal. eapply subst_subst_ws_at_depth; eassumption.
    + (* App *)
      destruct Hws as [H1 H2]. simpl. f_equal.
      * eapply subst_subst_ws_at_depth; eassumption.
      * eapply subst_subst_ws_at_depth; eassumption.
    + (* InductiveIntro *)
      simpl. f_equal.
      induction l as [| x xs IH].
      * reflexivity.
      * simpl in Hws |- *. destruct Hws as [Hx Hrest]. f_equal.
        -- eapply subst_subst_ws_at_depth; eassumption.
        -- apply IH. exact Hrest.
    + (* SanctionsDominance *)
      simpl. f_equal. eapply subst_subst_ws_at_depth; eassumption.
    + (* DefeatElim *)
      simpl. f_equal. eapply subst_subst_ws_at_depth; eassumption.
    + (* Lift0 *)
      simpl. f_equal. eapply subst_subst_ws_at_depth; eassumption.
    + (* Derive1 *)
      destruct Hws as [H1 H2]. simpl. f_equal.
      * eapply subst_subst_ws_at_depth; eassumption.
      * eapply subst_subst_ws_at_depth; eassumption.
    + (* Lambda *)
      destruct Hws as [H1 H2]. simpl. f_equal.
      * eapply subst_subst_ws_at_depth; eassumption.
      * (* body under binder.
           IH at (t2, shift 0 1 r, shift 0 1 s, S i, S j, S k). *)
        assert (HSji : S j <= S i) by lia.
        assert (HSik : S (S i) <= S k) by lia.
        assert (Hr' : well_scoped (S k) (shift 0 1 r))
          by (apply well_scoped_shift_0_1; exact Hr).
        assert (Hs' : well_scoped (S k) (shift 0 1 s))
          by (apply well_scoped_shift_0_1; exact Hs).
        rewrite (subst_subst_ws_at_depth
                   t2 (shift 0 1 r) (shift 0 1 s) (S i) (S j) (S k)
                   HSji H2 HSik Hr' Hs').
        f_equal.
        (* Reconcile shift 0 1 (subst i s r) with subst (S i) (shift 0 1 s) (shift 0 1 r)
           via shift_subst_commute_ws_at_depth at (r, s, i, 0, 1, k). *)
        assert (Hci : 0 <= i) by lia.
        rewrite (shift_subst_commute_ws_at_depth
                   r s i 0 1 k Hr Hik Hci).
        simpl. replace (i + 1) with (S i) by lia. reflexivity.
    + (* Pi *)
      destruct Hws as [H1 H2]. simpl. f_equal.
      * eapply subst_subst_ws_at_depth; eassumption.
      * assert (HSji : S j <= S i) by lia.
        assert (HSik : S (S i) <= S k) by lia.
        assert (Hr' : well_scoped (S k) (shift 0 1 r))
          by (apply well_scoped_shift_0_1; exact Hr).
        assert (Hs' : well_scoped (S k) (shift 0 1 s))
          by (apply well_scoped_shift_0_1; exact Hs).
        rewrite (subst_subst_ws_at_depth
                   t2 (shift 0 1 r) (shift 0 1 s) (S i) (S j) (S k)
                   HSji H2 HSik Hr' Hs').
        f_equal.
        assert (Hci : 0 <= i) by lia.
        rewrite (shift_subst_commute_ws_at_depth
                   r s i 0 1 k Hr Hik Hci).
        simpl. replace (i + 1) with (S i) by lia. reflexivity.
    + (* Sigma *)
      destruct Hws as [H1 H2]. simpl. f_equal.
      * eapply subst_subst_ws_at_depth; eassumption.
      * assert (HSji : S j <= S i) by lia.
        assert (HSik : S (S i) <= S k) by lia.
        assert (Hr' : well_scoped (S k) (shift 0 1 r))
          by (apply well_scoped_shift_0_1; exact Hr).
        assert (Hs' : well_scoped (S k) (shift 0 1 s))
          by (apply well_scoped_shift_0_1; exact Hs).
        rewrite (subst_subst_ws_at_depth
                   t2 (shift 0 1 r) (shift 0 1 s) (S i) (S j) (S k)
                   HSji H2 HSik Hr' Hs').
        f_equal.
        assert (Hci : 0 <= i) by lia.
        rewrite (shift_subst_commute_ws_at_depth
                   r s i 0 1 k Hr Hik Hci).
        simpl. replace (i + 1) with (S i) by lia. reflexivity.
    + (* Annot *)
      destruct Hws as [H1 H2]. simpl. f_equal.
      * eapply subst_subst_ws_at_depth; eassumption.
      * eapply subst_subst_ws_at_depth; eassumption.
    + (* Let *)
      destruct Hws as [H1 [H2 H3]]. simpl. f_equal.
      * eapply subst_subst_ws_at_depth; eassumption.
      * eapply subst_subst_ws_at_depth; eassumption.
      * assert (HSji : S j <= S i) by lia.
        assert (HSik : S (S i) <= S k) by lia.
        assert (Hr' : well_scoped (S k) (shift 0 1 r))
          by (apply well_scoped_shift_0_1; exact Hr).
        assert (Hs' : well_scoped (S k) (shift 0 1 s))
          by (apply well_scoped_shift_0_1; exact Hs).
        rewrite (subst_subst_ws_at_depth
                   t3 (shift 0 1 r) (shift 0 1 s) (S i) (S j) (S k)
                   HSji H3 HSik Hr' Hs').
        f_equal.
        assert (Hci : 0 <= i) by lia.
        rewrite (shift_subst_commute_ws_at_depth
                   r s i 0 1 k Hr Hik Hci).
        simpl. replace (i + 1) with (S i) by lia. reflexivity.
    + (* Match *)
      destruct Hws as [H1 [H2 H3]]. simpl. f_equal.
      * eapply subst_subst_ws_at_depth; eassumption.
      * eapply subst_subst_ws_at_depth; eassumption.
      * induction l as [| br brs IH].
        -- reflexivity.
        -- simpl in H3 |- *. destruct H3 as [Hbr Hrest]. f_equal.
           ++ eapply subst_subst_ws_at_depth_branch; eassumption.
           ++ apply IH. exact Hrest.
    + (* Rec *)
      destruct Hws as [H1 H2]. simpl. f_equal.
      * eapply subst_subst_ws_at_depth; eassumption.
      * assert (HSji : S j <= S i) by lia.
        assert (HSik : S (S i) <= S k) by lia.
        assert (Hr' : well_scoped (S k) (shift 0 1 r))
          by (apply well_scoped_shift_0_1; exact Hr).
        assert (Hs' : well_scoped (S k) (shift 0 1 s))
          by (apply well_scoped_shift_0_1; exact Hs).
        rewrite (subst_subst_ws_at_depth
                   t2 (shift 0 1 r) (shift 0 1 s) (S i) (S j) (S k)
                   HSji H2 HSik Hr' Hs').
        f_equal.
        assert (Hci : 0 <= i) by lia.
        rewrite (shift_subst_commute_ws_at_depth
                   r s i 0 1 k Hr Hik Hci).
        simpl. replace (i + 1) with (S i) by lia. reflexivity.
    + (* ModalAt *)
      destruct Hws as [H1 H2]. simpl. f_equal.
      * eapply subst_subst_ws_at_depth; eassumption.
      * eapply subst_subst_ws_at_depth; eassumption.
    + (* ModalEventually *)
      destruct Hws as [H1 H2]. simpl. f_equal.
      * eapply subst_subst_ws_at_depth; eassumption.
      * eapply subst_subst_ws_at_depth; eassumption.
    + (* ModalAlways *)
      destruct Hws as [H1 [H2 H3]]. simpl. f_equal.
      * eapply subst_subst_ws_at_depth; eassumption.
      * eapply subst_subst_ws_at_depth; eassumption.
      * eapply subst_subst_ws_at_depth; eassumption.
    + (* ModalIntro *)
      simpl. f_equal. eapply subst_subst_ws_at_depth; eassumption.
    + (* ModalElim *)
      destruct Hws as [H1 H2]. simpl. f_equal.
      * eapply subst_subst_ws_at_depth; eassumption.
      * eapply subst_subst_ws_at_depth; eassumption.
    + (* Defeasible *)
      destruct Hws as [H1 [H2 H3]]. simpl. f_equal.
      * eapply subst_subst_ws_at_depth; eassumption.
      * eapply subst_subst_ws_at_depth; eassumption.
      * induction l as [| ex exs IH].
        -- reflexivity.
        -- simpl in H3 |- *. destruct H3 as [Hex Hrest]. f_equal.
           ++ eapply subst_subst_ws_at_depth_exception; eassumption.
           ++ apply IH. exact Hrest.
    + (* Hole *)
      simpl. f_equal. eapply subst_subst_ws_at_depth; eassumption.
    + (* HoleFill *)
      destruct Hws as [H1 H2]. simpl. f_equal.
      * eapply subst_subst_ws_at_depth; eassumption.
      * eapply subst_subst_ws_at_depth; eassumption.
    + (* PrincipleBalance *)
      destruct Hws as [H1 H2]. simpl. f_equal.
      * eapply subst_subst_ws_at_depth; eassumption.
      * eapply subst_subst_ws_at_depth; eassumption.
    + (* Unlock *)
      destruct Hws as [H1 H2]. simpl. f_equal.
      * eapply subst_subst_ws_at_depth; eassumption.
      * eapply subst_subst_ws_at_depth; eassumption.
  (* --- Branch case --- *)
  - intros b r s i j k Hji Hws Hik Hr Hs. destruct b as [pat body]. simpl.
    destruct pat as [name arity |]; simpl in Hws.
    + (* PCtor *)
      f_equal.
      assert (Hws' : well_scoped (S (i + arity)) body).
      { replace (S (i + arity)) with (S i + arity) by lia. exact Hws. }
      assert (Hjarity : j + arity <= i + arity) by lia.
      assert (Hiarityk : S (i + arity) <= k + arity) by lia.
      assert (Hr' : well_scoped (k + arity) (shift 0 arity r)).
      { apply well_scoped_shift_0_arity. exact Hr. }
      assert (Hs' : well_scoped (k + arity) (shift 0 arity s)).
      { apply well_scoped_shift_0_arity. exact Hs. }
      rewrite (subst_subst_ws_at_depth
                 body (shift 0 arity r) (shift 0 arity s)
                 (i + arity) (j + arity) (k + arity)
                 Hjarity Hws' Hiarityk Hr' Hs').
      rewrite (shift_shift 0 1 arity s).
      rewrite (shift_shift 0 arity 1 s).
      replace (S (i + arity)) with (S i + arity) by lia.
      replace (arity + 1) with (1 + arity) by lia.
      f_equal.
      (* Goal: subst (i + arity) (shift 0 arity s) (shift 0 arity r)
               = shift 0 arity (subst i s r) *)
      assert (Hci : 0 <= i) by lia.
      rewrite (shift_subst_commute_ws_at_depth
                 r s i 0 arity k Hr Hik Hci).
      simpl. reflexivity.
    + (* PWild *)
      f_equal.
      rewrite Nat.add_0_r in Hws.
      rewrite !Nat.add_0_r.
      rewrite !shift_zero.
      eapply subst_subst_ws_at_depth; eassumption.
  (* --- Exception case --- *)
  - intros e r s i j k Hji Hws Hik Hr Hs.
    destruct e as [guard body prio]. simpl in Hws.
    destruct Hws as [Hg Hb]. simpl. f_equal.
    + eapply subst_subst_ws_at_depth; eassumption.
    + eapply subst_subst_ws_at_depth; eassumption.
Qed.

(* ------------------------------------------------------------------ *)
(** *** Prop-level specifications for downstream citation.             *)
(* ------------------------------------------------------------------ *)

(** Analogues of [shift_subst_commute_ws_spec] / [subst_subst_ws_spec]
    at the relaxed ambient depth [k], for downstream files
    (e.g. [Lex.Requirements] or the forthcoming preservation
    development in [Lex.Typing]) to cite.

    [shift_subst_commute_ws_at_depth_spec]: the relaxed
    commutation under [i < k] and [c <= i].

    [subst_subst_ws_at_depth_spec]: the relaxed composition
    under [j <= i], [S i <= k], with [well_scoped (S i) t] still
    required on [t] (the obstruction witness
    [subst_subst_ws_at_depth_naive_false] rules out relaxing [t]).
*)

Definition shift_subst_commute_ws_at_depth_spec : Prop :=
  forall (t s : Term) (i c d k : nat),
    well_scoped k t ->
    i < k ->
    c <= i ->
    shift c d (subst i s t) =
    subst (i + d)
          (shift c d s)
          (shift c d t).

Theorem shift_subst_commute_ws_at_depth_spec_proof :
  shift_subst_commute_ws_at_depth_spec.
Proof.
  unfold shift_subst_commute_ws_at_depth_spec.
  exact shift_subst_commute_ws_at_depth.
Qed.

Definition subst_subst_ws_at_depth_spec : Prop :=
  forall (t r s : Term) (i j k : nat),
    j <= i ->
    well_scoped (S i) t ->
    S i <= k ->
    well_scoped k r ->
    well_scoped k s ->
    subst i s (subst j r t) =
    subst j (subst i s r) (subst (S i) (shift 0 1 s) t).

Theorem subst_subst_ws_at_depth_spec_proof :
  subst_subst_ws_at_depth_spec.
Proof.
  unfold subst_subst_ws_at_depth_spec.
  exact subst_subst_ws_at_depth.
Qed.

(* ================================================================== *)
(** ** Context shifting                                                *)
(* ================================================================== *)

(** [shift_ctx c d ctx] applies [shift c d] pointwise to every stored
    type in [ctx].  This is the operation used by [ctx_extend] (see
    [Lex.Typing]) to keep stored types self-consistent when the
    ambient scope grows by one binding.

    Under the option-(a) storage invariant - "position [i] stores a
    type whose free variables already refer to positions of the
    current context" - extending with a new binding at position [0]
    requires every existing entry to be shifted by [1] at cutoff [0]
    so its old references to [0 .. n-1] shift to [1 .. n] in the new
    context. *)

Fixpoint shift_ctx (c d : nat) (ctx : list Term) : list Term :=
  match ctx with
  | nil => nil
  | ty :: rest => shift c d ty :: shift_ctx c d rest
  end.

Lemma shift_ctx_nil : forall (c d : nat),
  shift_ctx c d nil = nil.
Proof. reflexivity. Qed.

Lemma shift_ctx_cons : forall (c d : nat) (ty : Term) (rest : list Term),
  shift_ctx c d (ty :: rest) = shift c d ty :: shift_ctx c d rest.
Proof. reflexivity. Qed.

Lemma shift_ctx_length : forall (c d : nat) (ctx : list Term),
  List.length (shift_ctx c d ctx) = List.length ctx.
Proof.
  intros c d ctx. induction ctx as [|ty rest IH]; simpl.
  - reflexivity.
  - f_equal. exact IH.
Qed.

(** Lookup-through-shift: [nth_error] on a shifted context returns
    the shifted stored type.  The core bridge lemma that makes
    weakening's T_Var case reduce to a single rewrite. *)
Lemma shift_ctx_nth_error : forall (c d : nat) (ctx : list Term) (i : nat),
  nth_error (shift_ctx c d ctx) i =
    match nth_error ctx i with
    | Some t => Some (shift c d t)
    | None => None
    end.
Proof.
  intros c d ctx. induction ctx as [|ty rest IH]; intros i.
  - destruct i; reflexivity.
  - destruct i as [|i']; simpl.
    + reflexivity.
    + apply IH.
Qed.

(** [shift_ctx] distributes over list concatenation. *)
Lemma shift_ctx_app : forall (c d : nat) (xs ys : list Term),
  shift_ctx c d (xs ++ ys) = shift_ctx c d xs ++ shift_ctx c d ys.
Proof.
  intros c d xs ys. induction xs as [|ty rest IH]; simpl.
  - reflexivity.
  - f_equal. exact IH.
Qed.

(** [firstn] commutes with [shift_ctx] - truncation is pointwise. *)
Lemma shift_ctx_firstn : forall (c d n : nat) (ctx : list Term),
  firstn n (shift_ctx c d ctx) = shift_ctx c d (firstn n ctx).
Proof.
  intros c d n ctx. revert n.
  induction ctx as [|ty rest IH]; intros n.
  - destruct n; reflexivity.
  - destruct n as [|n']; simpl.
    + reflexivity.
    + f_equal. apply IH.
Qed.

(** [skipn] commutes with [shift_ctx] - the suffix shifts pointwise. *)
Lemma shift_ctx_skipn : forall (c d n : nat) (ctx : list Term),
  skipn n (shift_ctx c d ctx) = shift_ctx c d (skipn n ctx).
Proof.
  intros c d n ctx. revert n.
  induction ctx as [|ty rest IH]; intros n.
  - destruct n; reflexivity.
  - destruct n as [|n']; simpl.
    + reflexivity.
    + apply IH.
Qed.

(** Shift composition on [shift_ctx] at the same cutoff - the amounts
    add.  Analogue of [shift_shift] at the context level. *)
Lemma shift_ctx_shift_ctx : forall (c m n : nat) (ctx : list Term),
  shift_ctx c m (shift_ctx c n ctx) = shift_ctx c (n + m) ctx.
Proof.
  intros c m n ctx. induction ctx as [|ty rest IH]; simpl.
  - reflexivity.
  - f_equal.
    + apply shift_shift.
    + exact IH.
Qed.

(** [shift_ctx]-level version of [shift_shift_swap_0_1]: commuting a
    universal [shift_ctx 0 1] with a deeper [shift_ctx k 1]. *)
Lemma shift_ctx_shift_ctx_swap_0_1 : forall (k : nat) (ctx : list Term),
  shift_ctx (S k) 1 (shift_ctx 0 1 ctx) =
  shift_ctx 0 1 (shift_ctx k 1 ctx).
Proof.
  intros k ctx. induction ctx as [|ty rest IH]; simpl.
  - reflexivity.
  - f_equal.
    + apply shift_shift_swap_0_1.
    + exact IH.
Qed.

(* ================================================================== *)
(** ** shift_subst_commute_above : shift ABOVE the subst point         *)
(* ================================================================== *)

(** [shift_subst_commute_above]: when the shift cutoff [c] is at or
    above the substitution target [i], the shift commutes through the
    substitution with the substitution target preserved and the
    inner [t]'s cutoff bumped to [S c] (to account for the fact that
    substitution at [i] decrements indices above [i], so a free var
    at [c] in the original [t] becomes a free var at [c-1] after
    [subst]; to cancel that decrement on the RHS, the shift
    on [t] must start at [S c]).

    Distinct from [shift_subst_commute_ws_at_depth] which requires
    [c <= i] (shift BELOW the subst point).  Needed by the T_App /
    T_Let cases of weakening where [c = k > 0 = i].

    No [well_scoped] hypothesis needed: the lemma holds
    unconditionally for [i <= c]. *)

(** Var case. *)
Lemma shift_subst_commute_above_var :
  forall (n : nat) (s : Term) (i c d : nat),
    i <= c ->
    shift c d (subst i s (Var n)) =
    subst i (shift c d s) (shift (S c) d (Var n)).
Proof.
  intros n s i c d Hic.
  destruct (Nat.eq_dec n i) as [Heqni | Hneqni].
  - (* n = i.  LHS: subst i s (Var i) = s, then shift c d s. *)
    subst n.
    (* Reduce LHS's subst first via cbn on subst. *)
    cbn [subst].
    rewrite Nat.eqb_refl.
    (* Goal: shift c d s = subst i (shift c d s) (shift (S c) d (Var i)). *)
    (* Reduce RHS's inner shift: since S c > i, Var i is kept. *)
    cbn [shift].
    assert (Hleb : Nat.leb (S c) i = false) by (apply Nat.leb_nle; lia).
    rewrite Hleb.
    (* Goal: shift c d s = subst i (shift c d s) (Var i). *)
    cbn [subst].
    rewrite Nat.eqb_refl.
    reflexivity.
  - (* n <> i. *)
    destruct (Nat.ltb i n) eqn:Hin.
    + (* n > i. *)
      apply Nat.ltb_lt in Hin.
      cbn [subst].
      assert (Hne : Nat.eqb n i = false) by (apply Nat.eqb_neq; exact Hneqni).
      rewrite Hne.
      assert (Hltf : Nat.ltb i n = true) by (apply Nat.ltb_lt; exact Hin).
      rewrite Hltf.
      (* LHS: shift c d (Var (pred n)).  pred n vs c depends on c vs n - 1. *)
      cbn [shift].
      destruct (Nat.leb c (pred n)) eqn:Hcpn.
      * apply Nat.leb_le in Hcpn.
        (* LHS = Var (pred n + d).
           RHS: shift (S c) d (Var n).  S c <= n iff c <= n - 1 = pred n.
                So shift bumps to Var (n + d).
                subst i (Var (n + d)): n + d > i → Var (pred (n + d)). *)
        assert (HScn : Nat.leb (S c) n = true).
        { apply Nat.leb_le. destruct n; [lia | simpl; lia]. }
        rewrite HScn.
        cbn [subst].
        assert (Hne2 : Nat.eqb (n + d) i = false) by (apply Nat.eqb_neq; lia).
        rewrite Hne2.
        assert (Hltf2 : Nat.ltb i (n + d) = true) by (apply Nat.ltb_lt; lia).
        rewrite Hltf2.
        f_equal. destruct n; [lia | simpl; lia].
      * apply Nat.leb_nle in Hcpn.
        (* LHS = Var (pred n) unchanged.
           RHS: shift (S c) d (Var n).  S c <= n iff c <= n - 1 = pred n.
                Here c > pred n, so S c > n, shift keeps Var n.
                subst i (Var n): n > i → Var (pred n). *)
        assert (HScn : Nat.leb (S c) n = false).
        { apply Nat.leb_nle. destruct n; [lia | simpl in Hcpn |- *; lia]. }
        rewrite HScn.
        cbn [subst].
        rewrite Hne.
        assert (Hltf2 : Nat.ltb i n = true) by (apply Nat.ltb_lt; lia).
        rewrite Hltf2.
        reflexivity.
    + (* n < i. *)
      apply Nat.ltb_nlt in Hin.
      assert (Hnlti : n < i) by lia.
      cbn [subst].
      assert (Hne : Nat.eqb n i = false) by (apply Nat.eqb_neq; exact Hneqni).
      rewrite Hne.
      assert (Hltf : Nat.ltb i n = false) by (apply Nat.ltb_nlt; lia).
      rewrite Hltf.
      (* LHS: shift c d (Var n).  n < i <= c, so c > n; shift keeps Var n. *)
      cbn [shift].
      assert (Hcn : Nat.leb c n = false) by (apply Nat.leb_nle; lia).
      rewrite Hcn.
      (* RHS: shift (S c) d (Var n). n < i <= c < S c; keep Var n.
              subst i (Var n): n < i → Var n. *)
      assert (HScn : Nat.leb (S c) n = false) by (apply Nat.leb_nle; lia).
      rewrite HScn.
      cbn [subst].
      rewrite Hne.
      rewrite Hltf.
      reflexivity.
Qed.

(** Full mutual induction for [shift_subst_commute_above] across
    Term / Branch / Exception.  Structure mirrors
    [shift_subst_commute_ws_at_depth]: non-binder constructors close
    via [f_equal + IH], binder cases use the IH at [(S i, S c)] plus
    [shift_shift_swap_0_1] to reconcile the inner [shift 0 1 s]
    against the outer-shifted [shift c d s].  Branch uses
    [shift_shift_swap_0_arity] for the multi-binder case. *)

Lemma shift_subst_commute_above :
  forall (t s : Term) (i c d : nat),
    i <= c ->
    shift c d (subst i s t) =
    subst i (shift c d s) (shift (S c) d t)
with shift_subst_commute_above_branch :
  forall (b : Branch) (s : Term) (i c d : nat),
    i <= c ->
    shift_branch c d (subst_branch i s b) =
    subst_branch i (shift c d s) (shift_branch (S c) d b)
with shift_subst_commute_above_exception :
  forall (e : Exception) (s : Term) (i c d : nat),
    i <= c ->
    shift_exception c d (subst_exception i s e) =
    subst_exception i (shift c d s) (shift_exception (S c) d e).
Proof.
  (* --- Term case --- *)
  - intros t s i c d Hic. destruct t.
    + (* Var *) apply shift_subst_commute_above_var. exact Hic.
    + (* TSort *) simpl; reflexivity.
    + (* Constant *) simpl; reflexivity.
    + (* ContentRef *) simpl; reflexivity.
    + (* IntLit *) simpl; reflexivity.
    + (* RatLit *) simpl; reflexivity.
    + (* StringLit *) simpl; reflexivity.
    + (* AxiomUse *) simpl; reflexivity.
    + (* Pair *)
      simpl. f_equal.
      * apply shift_subst_commute_above. exact Hic.
      * apply shift_subst_commute_above. exact Hic.
    + (* Proj *)
      simpl. f_equal. apply shift_subst_commute_above. exact Hic.
    + (* App *)
      simpl. f_equal.
      * apply shift_subst_commute_above. exact Hic.
      * apply shift_subst_commute_above. exact Hic.
    + (* InductiveIntro *)
      simpl. f_equal.
      induction l as [| x xs IH]; simpl.
      * reflexivity.
      * f_equal.
        -- apply shift_subst_commute_above. exact Hic.
        -- exact IH.
    + (* SanctionsDominance *)
      simpl. f_equal. apply shift_subst_commute_above. exact Hic.
    + (* DefeatElim *)
      simpl. f_equal. apply shift_subst_commute_above. exact Hic.
    + (* Lift0 *)
      simpl. f_equal. apply shift_subst_commute_above. exact Hic.
    + (* Derive1 *)
      simpl. f_equal.
      * apply shift_subst_commute_above. exact Hic.
      * apply shift_subst_commute_above. exact Hic.
    + (* Lambda *)
      simpl. f_equal.
      * apply shift_subst_commute_above. exact Hic.
      * assert (HSic : S i <= S c) by lia.
        rewrite (shift_subst_commute_above t2 (shift 0 1 s) (S i) (S c) d HSic).
        rewrite shift_shift_swap_0_1. reflexivity.
    + (* Pi *)
      simpl. f_equal.
      * apply shift_subst_commute_above. exact Hic.
      * assert (HSic : S i <= S c) by lia.
        rewrite (shift_subst_commute_above t2 (shift 0 1 s) (S i) (S c) d HSic).
        rewrite shift_shift_swap_0_1. reflexivity.
    + (* Sigma *)
      simpl. f_equal.
      * apply shift_subst_commute_above. exact Hic.
      * assert (HSic : S i <= S c) by lia.
        rewrite (shift_subst_commute_above t2 (shift 0 1 s) (S i) (S c) d HSic).
        rewrite shift_shift_swap_0_1. reflexivity.
    + (* Annot *)
      simpl. f_equal.
      * apply shift_subst_commute_above. exact Hic.
      * apply shift_subst_commute_above. exact Hic.
    + (* Let *)
      simpl. f_equal.
      * apply shift_subst_commute_above. exact Hic.
      * apply shift_subst_commute_above. exact Hic.
      * assert (HSic : S i <= S c) by lia.
        rewrite (shift_subst_commute_above t3 (shift 0 1 s) (S i) (S c) d HSic).
        rewrite shift_shift_swap_0_1. reflexivity.
    + (* Match *)
      simpl. f_equal.
      * apply shift_subst_commute_above. exact Hic.
      * apply shift_subst_commute_above. exact Hic.
      * induction l as [| br brs IH]; simpl.
        -- reflexivity.
        -- f_equal.
           ++ apply shift_subst_commute_above_branch. exact Hic.
           ++ exact IH.
    + (* Rec *)
      simpl. f_equal.
      * apply shift_subst_commute_above. exact Hic.
      * assert (HSic : S i <= S c) by lia.
        rewrite (shift_subst_commute_above t2 (shift 0 1 s) (S i) (S c) d HSic).
        rewrite shift_shift_swap_0_1. reflexivity.
    + (* ModalAt *)
      simpl. f_equal.
      * apply shift_subst_commute_above. exact Hic.
      * apply shift_subst_commute_above. exact Hic.
    + (* ModalEventually *)
      simpl. f_equal.
      * apply shift_subst_commute_above. exact Hic.
      * apply shift_subst_commute_above. exact Hic.
    + (* ModalAlways *)
      simpl. f_equal.
      * apply shift_subst_commute_above. exact Hic.
      * apply shift_subst_commute_above. exact Hic.
      * apply shift_subst_commute_above. exact Hic.
    + (* ModalIntro *)
      simpl. f_equal. apply shift_subst_commute_above. exact Hic.
    + (* ModalElim *)
      simpl. f_equal.
      * apply shift_subst_commute_above. exact Hic.
      * apply shift_subst_commute_above. exact Hic.
    + (* Defeasible *)
      simpl. f_equal.
      * apply shift_subst_commute_above. exact Hic.
      * apply shift_subst_commute_above. exact Hic.
      * induction l as [| ex exs IH]; simpl.
        -- reflexivity.
        -- f_equal.
           ++ apply shift_subst_commute_above_exception. exact Hic.
           ++ exact IH.
    + (* Hole *)
      simpl. f_equal. apply shift_subst_commute_above. exact Hic.
    + (* HoleFill *)
      simpl. f_equal.
      * apply shift_subst_commute_above. exact Hic.
      * apply shift_subst_commute_above. exact Hic.
    + (* PrincipleBalance *)
      simpl. f_equal.
      * apply shift_subst_commute_above. exact Hic.
      * apply shift_subst_commute_above. exact Hic.
    + (* Unlock *)
      simpl. f_equal.
      * apply shift_subst_commute_above. exact Hic.
      * apply shift_subst_commute_above. exact Hic.
  (* --- Branch case --- *)
  - intros b s i c d Hic. destruct b as [pat body]. simpl.
    destruct pat as [name arity |]; simpl.
    + (* PCtor *)
      f_equal.
      assert (Hiarity : i + arity <= c + arity) by lia.
      rewrite (shift_subst_commute_above
                 body (shift 0 arity s) (i + arity) (c + arity) d Hiarity).
      rewrite shift_shift_swap_0_arity.
      reflexivity.
    + (* PWild *)
      f_equal.
      rewrite !Nat.add_0_r, !shift_zero.
      apply shift_subst_commute_above. exact Hic.
  (* --- Exception case --- *)
  - intros e s i c d Hic. destruct e as [guard body prio]. simpl. f_equal.
    + apply shift_subst_commute_above. exact Hic.
    + apply shift_subst_commute_above. exact Hic.
Qed.

(** Prop-level spec for citation by downstream files. *)
Definition shift_subst_commute_above_spec_de_bruijn : Prop :=
  forall (t s : Term) (i c d : nat),
    i <= c ->
    shift c d (subst i s t) =
    subst i (shift c d s) (shift (S c) d t).

Theorem shift_subst_commute_above_spec_proof :
  shift_subst_commute_above_spec_de_bruijn.
Proof.
  unfold shift_subst_commute_above_spec_de_bruijn.
  exact shift_subst_commute_above.
Qed.
