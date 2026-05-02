(** * Lex/Syntax.v - Core Lex syntax in Coq

    Mirrors [crates/lex-core/src/ast.rs].

    This formalization captures the core calculus of the Lex type system:
    a dependently-typed lambda calculus with universe polymorphism, defeasible
    rules, effects, temporal modalities, and an admissible fragment for
    mechanized type checking.

    Variables use De Bruijn indices (nat).  All binders carry explicit domain
    annotations - there are no implicit arguments in core form.
*)

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.

(* ================================================================== *)
(** ** Universe levels (grammar §2) *)
(* ================================================================== *)

(** Level expressions.  [Nat n] is a concrete level, [LVar i] is a level
    variable, [Succ l n] is l + n, and [Max l1 l2] is max(l1, l2). *)
Inductive Level : Type :=
  | LNat : nat -> Level
  | LVar : nat -> Level            (* level variable index *)
  | LSucc : Level -> nat -> Level  (* l + n *)
  | LMax : Level -> Level -> Level.

(* ================================================================== *)
(** ** Sorts (grammar §2) *)
(* ================================================================== *)

(** Sort classifiers.  [Type_l] is the universe at level l, [Prop] is the
    proof-irrelevant universe (at Type_0), [Rule_l] is the rule universe,
    and [Time0]/[Time1] are the temporal sorts. *)
Inductive Sort : Type :=
  | SType : Level -> Sort   (* Type_l *)
  | SLProp : Sort             (* Prop - proof-irrelevant sort *)
  | SRule : Level -> Sort    (* Rule_l *)
  | STime0 : Sort            (* Time_0 - frozen at transition commit *)
  | STime1 : Sort.           (* Time_1 - derived via rewrite *)

(* ================================================================== *)
(** ** Effect rows (grammar §3.1) *)
(* ================================================================== *)

(** Individual effects.  This is a simplified representation - the full
    AST carries scoping terms and authority references inside effects. *)
Inductive Effect : Type :=
  | ERead : Effect
  | EWrite : Effect           (* write(scope) - scope elided *)
  | EAttest : Effect          (* attest(authority) *)
  | EAuthority : Effect       (* authority(ref) *)
  | EOracle : Effect          (* oracle(ref) *)
  | EFuel : Level -> nat -> Effect  (* fuel(level, amount) *)
  | ESanctionsQuery : Effect  (* sanctions_query - distinguished *)
  | EDiscretion : Effect.     (* discretion(authority) *)

(** Effect rows: empty, concrete list, row variable, join, or
    branch-sensitive wrapper. *)
Inductive EffectRow : Type :=
  | EREmpty : EffectRow
  | EREffects : list Effect -> EffectRow
  | ERVar : nat -> EffectRow                  (* row variable *)
  | ERJoin : EffectRow -> EffectRow -> EffectRow
  | ERBranchSensitive : EffectRow -> EffectRow.

(* ================================================================== *)
(** ** Patterns and branches *)
(* ================================================================== *)

(** Match-branch patterns (§3).  [PCtor name arity] is a constructor
    pattern binding [arity] new variables.  [PWild] is the wildcard. *)
Inductive Pattern : Type :=
  | PCtor : string -> nat -> Pattern  (* constructor name, binder count *)
  | PWild : Pattern.

(* ================================================================== *)
(** ** Exceptions (§6) *)
(* ================================================================== *)

(** Forward declaration - Exception references Term, which references
    Exception via DefeasibleRule.  We use a mutual inductive. *)

(* ================================================================== *)
(** ** Core term AST (§3) *)
(* ================================================================== *)

(** The core Lex term type, mirroring [ast::Term] from the Rust
    implementation.  Types are terms.  Variables are De Bruijn indices.

    We model the admissible fragment (the subset the bidirectional
    type checker accepts) plus the full calculus forms that are
    rejected by the admissibility predicate.

    The mutual inductive includes [Exception] and [Branch] which
    contain [Term] sub-expressions. *)

Inductive Term : Type :=
  (* ── Variables / constants / sorts ──────────────────────── *)
  | Var : nat -> Term                          (* De Bruijn index *)
  | TSort : Sort -> Term                       (* universe sort *)
  | Constant : string -> Term                  (* qualified constant *)
  | ContentRef : string -> Term                (* lex://blake3:<hash> *)
  | IntLit : nat -> Term                       (* integer literal *)
  | RatLit : nat -> nat -> Term                (* rational p/q *)
  | StringLit : string -> Term                 (* string literal *)
  | AxiomUse : string -> Term                  (* axiom <name> *)

  (* ── Pairs / projections ────────────────────────────────── *)
  | Pair : Term -> Term -> Term                (* <a, b> *)
  | Proj : bool -> Term -> Term                (* pi_1 / pi_2 *)

  (* ── Application / introduction ─────────────────────────── *)
  | App : Term -> Term -> Term                 (* f a *)
  | InductiveIntro : string -> list Term -> Term  (* C a1 a2 ... *)

  (* ── Temporal (application level) ───────────────────────── *)
  | SanctionsDominance : Term -> Term          (* sanctions-dominance(proof) *)
  | DefeatElim : Term -> Term                  (* defeat rule *)
  | Lift0 : Term -> Term                       (* lift_0(time) *)
  | Derive1 : Term -> Term -> Term             (* derive_1(time, witness) *)

  (* ── Binders ────────────────────────────────────────────── *)
  | Lambda : Term -> Term -> Term              (* lam(domain, body) *)
  | Pi : Term -> option EffectRow -> Term -> Term  (* Pi(domain, effects, codomain) *)
  | Sigma : Term -> Term -> Term               (* Sigma(fst_ty, snd_ty) *)
  | Annot : Term -> Term -> Term               (* (e : T) *)
  | Let : Term -> Term -> Term -> Term         (* let _ : T = v in body *)
  | Match : Term -> Term -> list Branch -> Term  (* match scrutinee return T with branches *)
  | Rec : Term -> Term -> Term                 (* fix f : T := body *)

  (* ── Temporal modals ────────────────────────────────────── *)
  | ModalAt : Term -> Term -> Term             (* @ time body *)
  | ModalEventually : Term -> Term -> Term     (* diamond time body *)
  | ModalAlways : Term -> Term -> Term -> Term (* box [from, to] body *)

  (* ── Tribunal modal ─────────────────────────────────────── *)
  | ModalIntro : string -> Term -> Term        (* [[T]] body *)
  | ModalElim : string -> string -> Term -> Term -> Term  (* coerce[T1 => T2](e, w) *)

  (* ── Defeasible / Holes / Balance ───────────────────────── *)
  | Defeasible : Term -> Term -> list Exception -> Term  (* base_ty, base_body, exceptions *)
  | Hole : Term -> Term                        (* typed discretion hole: ?name : T *)
  | HoleFill : Term -> Term -> Term            (* fill(filler, pcauth) *)
  | PrincipleBalance : Term -> Term -> Term    (* verdict, rationale *)
  | Unlock : Term -> Term -> Term              (* unlock row in body *)

with Branch : Type :=
  | MkBranch : Pattern -> Term -> Branch

with Exception : Type :=
  | MkException : Term -> Term -> option nat -> Exception.
    (* guard, body, optional priority *)

(* ================================================================== *)
(** ** Derived notions *)
(* ================================================================== *)

(** Convenience: Type at a concrete level. *)
Definition type_level (n : nat) : Term :=
  TSort (SType (LNat n)).

(** Convenience: Prop sort. *)
Definition prop : Term := TSort SLProp.

(** Convenience: simple non-dependent function type (A -> B), pure. *)
Definition arrow (A B : Term) : Term :=
  Pi A None B.

(** ** Decidable equality *)

Lemma level_eq_dec : forall (l1 l2 : Level), {l1 = l2} + {l1 <> l2}.
Proof. decide equality; apply Nat.eq_dec. Qed.

Lemma sort_eq_dec : forall (s1 s2 : Sort), {s1 = s2} + {s1 <> s2}.
Proof. decide equality; apply level_eq_dec. Qed.

Lemma effect_eq_dec : forall (e1 e2 : Effect), {e1 = e2} + {e1 <> e2}.
Proof. decide equality; try apply level_eq_dec; try apply Nat.eq_dec. Qed.

Lemma pattern_eq_dec : forall (p1 p2 : Pattern), {p1 = p2} + {p1 <> p2}.
Proof. decide equality; try apply string_dec; try apply Nat.eq_dec. Qed.

(** List-of-Effect equality is constructive via the effect_eq_dec. *)
Lemma list_effect_eq_dec :
  forall (l1 l2 : list Effect), {l1 = l2} + {l1 <> l2}.
Proof. apply list_eq_dec. apply effect_eq_dec. Qed.

(** EffectRow is recursive but not mutually recursive; Qed via
    structural induction. *)
Lemma effect_row_eq_dec :
  forall (r1 r2 : EffectRow), {r1 = r2} + {r1 <> r2}.
Proof.
  induction r1; destruct r2; try (right; discriminate);
    try (left; reflexivity).
  - destruct (list_effect_eq_dec l l0) as [Heq|Hne].
    + subst. left. reflexivity.
    + right. intro H. inversion H. contradiction.
  - destruct (Nat.eq_dec n n0) as [Heq|Hne].
    + subst. left. reflexivity.
    + right. intro H. inversion H. contradiction.
  - destruct (IHr1_1 r2_1) as [Heq1|Hne1]; [subst|].
    + destruct (IHr1_2 r2_2) as [Heq2|Hne2]; [subst|].
      * left. reflexivity.
      * right. intro H. inversion H. contradiction.
    + right. intro H. inversion H. contradiction.
  - destruct (IHr1 r2) as [Heq|Hne]; [subst|].
    + left. reflexivity.
    + right. intro H. inversion H. contradiction.
Qed.

(** The mutually recursive syntax admits structural decidable equality.
    Keeping this proof closed removes the former equality axioms from the
    trusted base of the paper-level development. *)
Fixpoint term_eq_dec (t1 t2 : Term) {struct t1}
  : {t1 = t2} + {t1 <> t2}
with branch_eq_dec (b1 b2 : Branch) {struct b1}
  : {b1 = b2} + {b1 <> b2}
with exception_eq_dec (e1 e2 : Exception) {struct e1}
  : {e1 = e2} + {e1 <> e2}.
Proof.
  - decide equality;
      try apply string_dec;
      try apply Nat.eq_dec;
      try apply bool_dec;
      try apply sort_eq_dec;
      try apply effect_row_eq_dec;
      try (apply list_eq_dec; apply term_eq_dec);
      try (apply list_eq_dec; apply branch_eq_dec);
      try (decide equality; try apply effect_row_eq_dec; try apply Nat.eq_dec).
  - decide equality; try apply pattern_eq_dec; try apply term_eq_dec.
  - decide equality;
      try apply term_eq_dec;
      try apply Nat.eq_dec;
      try (decide equality; apply Nat.eq_dec).
Defined.
