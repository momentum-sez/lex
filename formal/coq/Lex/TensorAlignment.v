(** * Lex/TensorAlignment.v - Alignment between Lex's per-coordinate 5-chain
    verdict and the SJN tensor-factor (three-chain compliance grade plus
    orthogonal applicability marker) under F144.

    This file closes the E2 alignment obligation identified by the 2026-04-20
    platonic-ideal kickstart: the Lex paper's [ComplianceVerdict] is a bounded
    five-element Heyting chain {NonCompliant, Pending, NotApplicable, Exempt,
    Compliant} (see [VerdictHeyting.v]), while the Sovereign Jurisdiction
    Network paper's tensor-factor is structurally richer: a three-chain
    compliance grade {NonCompliant, Pending, Compliant} orthogonal to a
    three-valued applicability marker {Applicable, NotApplicable, Exempt},
    with a [MeetResult]-valued cross-jurisdictional meet that preserves
    provenance.

    F144 (the companion paper's impossibility dichotomy) states that no
    total Heyting algebra exists on the full tensor-factor type that
    preserves applicability provenance under meet.  We therefore cannot
    simply lift Lex's 5-chain meet to the tensor; the tensor meet must be
    MeetResult-valued.

    This file proves three facts, all Qed-closed by exhaustive case analysis:

    - [lex_to_tensor] is an injective projection from the 5-chain to the
      tensor-factor type.  Each Lex verdict maps to a unique tensor-factor.

    - Within the [Applicable] fragment (both inputs project to [TF_App]),
      the Lex 5-chain meet commutes with the tensor meet via [lex_to_tensor].
      This is the compatibility lemma between the two algebras on the sublattice
      where they agree.

    - Outside the Applicable fragment, the Lex 5-chain meet FAILS to preserve
      provenance: we exhibit a concrete witness where [meet v1 v2] under the
      Lex chain collapses two tensor-factors that the MeetResult-valued meet
      would distinguish.  This is the mechanization of (one direction of) F144:
      the Lex 5-chain cannot be the cross-jurisdictional algebra.

    Together with the paper's analytic F144 proof in "The Algebra of
    Institutional Compliance", this file witnesses that the two Coq
    mechanizations - [VerdictHeyting.v] (per-coordinate, one harbor) and
    the SJN tensor algebra (cross-jurisdictional aggregation) - are not
    in conflict: they are views at different compositional levels, related
    by a projection that is meet-preserving on exactly the sub-lattice where
    both are applicable. *)

Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Lex.VerdictHeyting.
Import ListNotations.

(** ** Tensor-factor type (SJN §4.2) *)

(** Per-domain compliance grade: three-chain NonCompliant < Pending < Compliant. *)
Inductive compliance_grade : Type :=
  | GNonCompliant
  | GPending
  | GCompliant.

(** Applicability axis (orthogonal to the grade): whether the domain
    governs the entity in the jurisdiction at all. *)
Inductive applicability : Type :=
  | Applicable
  | NotApp
  | IsExempt.

(** Tensor-factor value: either [Applicable] carrying a three-chain grade,
    or a bare [NotApp] / [IsExempt] singleton where the compliance grade
    is vacuous. *)
Inductive tensor_factor : Type :=
  | TF_App    : compliance_grade -> tensor_factor
  | TF_NotApp : tensor_factor
  | TF_Exempt : tensor_factor.

(** Three-chain rank (for the grade axis). *)
Definition grade_rank (g : compliance_grade) : nat :=
  match g with
  | GNonCompliant => 0
  | GPending      => 1
  | GCompliant    => 2
  end.

(** Three-chain meet on the grade axis: minimum-rank. *)
Definition grade_meet (g1 g2 : compliance_grade) : compliance_grade :=
  match g1, g2 with
  | GNonCompliant, _ | _, GNonCompliant => GNonCompliant
  | GPending, _      | _, GPending      => GPending
  | GCompliant, GCompliant              => GCompliant
  end.

Lemma grade_meet_idempotent : forall g, grade_meet g g = g.
Proof. destruct g; reflexivity. Qed.

Lemma grade_meet_comm : forall a b, grade_meet a b = grade_meet b a.
Proof. destruct a, b; reflexivity. Qed.

Lemma grade_meet_assoc : forall a b c,
  grade_meet (grade_meet a b) c = grade_meet a (grade_meet b c).
Proof. destruct a, b, c; reflexivity. Qed.

(** ** The three-chain is a bounded distributive Heyting algebra *)

(** The SJN paper's claim at §4.2: the per-domain three-chain
    $\mathsf{NonCompliant} < \mathsf{Pending} < \mathsf{Compliant}$
    is a finite distributive lattice and therefore a Heyting algebra.
    Mechanised below by exhaustive case analysis on the three-element
    carrier. *)

(** Ordering on the three-chain by rank. *)
Definition grade_leq (g1 g2 : compliance_grade) : Prop :=
  grade_rank g1 <= grade_rank g2.

(** Join: max-rank (the dual of [grade_meet]). *)
Definition grade_join (g1 g2 : compliance_grade) : compliance_grade :=
  match g1, g2 with
  | GCompliant, _ | _, GCompliant => GCompliant
  | GPending, _   | _, GPending   => GPending
  | GNonCompliant, GNonCompliant  => GNonCompliant
  end.

(** Heyting implication: [a -> b = top] if [a <= b], else [b]. *)
Definition grade_impl (a b : compliance_grade) : compliance_grade :=
  if Nat.leb (grade_rank a) (grade_rank b) then GCompliant else b.

(** Bounds. *)
Definition grade_top : compliance_grade := GCompliant.
Definition grade_bot : compliance_grade := GNonCompliant.

(** Join laws. *)
Lemma grade_join_idempotent : forall g, grade_join g g = g.
Proof. destruct g; reflexivity. Qed.

Lemma grade_join_comm : forall a b, grade_join a b = grade_join b a.
Proof. destruct a, b; reflexivity. Qed.

Lemma grade_join_assoc : forall a b c,
  grade_join (grade_join a b) c = grade_join a (grade_join b c).
Proof. destruct a, b, c; reflexivity. Qed.

(** Absorption. *)
Lemma grade_absorption_meet_join : forall a b,
  grade_meet a (grade_join a b) = a.
Proof. destruct a, b; reflexivity. Qed.

Lemma grade_absorption_join_meet : forall a b,
  grade_join a (grade_meet a b) = a.
Proof. destruct a, b; reflexivity. Qed.

(** Distributivity (both directions). *)
Lemma grade_distrib_meet_join : forall a b c,
  grade_meet a (grade_join b c) =
  grade_join (grade_meet a b) (grade_meet a c).
Proof. destruct a, b, c; reflexivity. Qed.

Lemma grade_distrib_join_meet : forall a b c,
  grade_join a (grade_meet b c) =
  grade_meet (grade_join a b) (grade_join a c).
Proof. destruct a, b, c; reflexivity. Qed.

(** Bounds laws. *)
Lemma grade_meet_top : forall g, grade_meet g grade_top = g.
Proof. destruct g; reflexivity. Qed.

Lemma grade_meet_bot : forall g, grade_meet g grade_bot = grade_bot.
Proof. destruct g; reflexivity. Qed.

Lemma grade_join_top : forall g, grade_join g grade_top = grade_top.
Proof. destruct g; reflexivity. Qed.

Lemma grade_join_bot : forall g, grade_join g grade_bot = g.
Proof. destruct g; reflexivity. Qed.

(** Heyting identity: [a /\ (a -> b) = a /\ b]. *)
Lemma grade_heyting_identity : forall a b,
  grade_meet a (grade_impl a b) = grade_meet a b.
Proof. destruct a, b; reflexivity. Qed.

(** Residuation: [c <= (a -> b) iff a /\ c <= b]. *)
Lemma grade_residuation : forall a b c,
  grade_leq c (grade_impl a b) <-> grade_leq (grade_meet a c) b.
Proof.
  intros a b c.
  unfold grade_leq, grade_meet, grade_impl, grade_rank.
  destruct a, b, c; simpl; split; intro H;
    try lia;
    try (apply Nat.leb_le; lia);
    try (apply Nat.leb_nle; lia).
Qed.

(** Compiled theorem: the three-chain satisfies the bounded
    distributive Heyting algebra laws.  Qed by bundling the individual
    lemmas above, matching the [verdict_is_heyting] pattern in
    [VerdictHeyting.v]. *)
Theorem grade_is_bounded_distributive_heyting :
  (forall g, grade_meet g g = g) /\
  (forall a b, grade_meet a b = grade_meet b a) /\
  (forall a b c, grade_meet (grade_meet a b) c = grade_meet a (grade_meet b c)) /\
  (forall g, grade_join g g = g) /\
  (forall a b, grade_join a b = grade_join b a) /\
  (forall a b c, grade_join (grade_join a b) c = grade_join a (grade_join b c)) /\
  (forall a b, grade_meet a (grade_join a b) = a) /\
  (forall a b, grade_join a (grade_meet a b) = a) /\
  (forall a b c, grade_meet a (grade_join b c) =
                 grade_join (grade_meet a b) (grade_meet a c)) /\
  (forall a b c, grade_join a (grade_meet b c) =
                 grade_meet (grade_join a b) (grade_join a c)) /\
  (forall g, grade_meet g grade_top = g) /\
  (forall g, grade_join g grade_bot = g) /\
  (forall a b, grade_meet a (grade_impl a b) = grade_meet a b).
Proof.
  repeat split.
  - apply grade_meet_idempotent.
  - apply grade_meet_comm.
  - apply grade_meet_assoc.
  - apply grade_join_idempotent.
  - apply grade_join_comm.
  - apply grade_join_assoc.
  - apply grade_absorption_meet_join.
  - apply grade_absorption_join_meet.
  - apply grade_distrib_meet_join.
  - apply grade_distrib_join_meet.
  - apply grade_meet_top.
  - apply grade_join_bot.
  - apply grade_heyting_identity.
Qed.

(** ** MeetResult for cross-jurisdictional composition *)

(** When aggregating two tensor-factors across jurisdictions, the meet is
    [MeetResult]-valued so it can preserve provenance across mixed-axis
    outcomes (F144).  On coordinates where both inputs are Applicable, the
    result is the three-chain meet.  On homogeneous NotApp/IsExempt pairs,
    the result is that singleton.  On mixed-axis coordinates, the result
    records the provenance explicitly.

    The constructors:
    - [MR_Grade g]         : both inputs Applicable, grade = g.
    - [MR_NotApp]          : both inputs NotApp.
    - [MR_Exempt]          : both inputs IsExempt.
    - [MR_AppVsNotApp g]   : one Applicable (grade g) and one NotApp;
                             records grade from the Applicable side.
    - [MR_AppVsExempt g]   : one Applicable (grade g) and one IsExempt;
                             records grade from the Applicable side.
    - [MR_NotAppVsExempt]  : one NotApp and one IsExempt.
    - [MR_AppVsNotAppVsExempt g] : an n-ary production meet saw at least
                             one Applicable input (with aggregate grade g),
                             at least one NotApp input, and at least one
                             IsExempt input.
    - [MR_Empty]           : the n-ary production meet was asked to compose
                             an empty harbor set. *)
Inductive meet_result : Type :=
  | MR_Grade          : compliance_grade -> meet_result
  | MR_NotApp         : meet_result
  | MR_Exempt         : meet_result
  | MR_AppVsNotApp    : compliance_grade -> meet_result
  | MR_AppVsExempt    : compliance_grade -> meet_result
  | MR_NotAppVsExempt : meet_result
  | MR_AppVsNotAppVsExempt : compliance_grade -> meet_result
  | MR_Empty          : meet_result.

(** The MeetResult-valued tensor meet. *)
Definition tensor_meet (t1 t2 : tensor_factor) : meet_result :=
  match t1, t2 with
  | TF_App g1, TF_App g2   => MR_Grade (grade_meet g1 g2)
  | TF_NotApp, TF_NotApp   => MR_NotApp
  | TF_Exempt, TF_Exempt   => MR_Exempt
  | TF_App g, TF_NotApp
  | TF_NotApp, TF_App g    => MR_AppVsNotApp g
  | TF_App g, TF_Exempt
  | TF_Exempt, TF_App g    => MR_AppVsExempt g
  | TF_NotApp, TF_Exempt
  | TF_Exempt, TF_NotApp   => MR_NotAppVsExempt
  end.

(** Idempotence of [tensor_meet] on every tensor-factor shape.  On
    Applicable, the result is the three-chain idempotent
    [MR_Grade g]; on the two singletons [TF_NotApp] and [TF_Exempt],
    the result is the corresponding [MR_NotApp] / [MR_Exempt]. *)
Lemma tensor_meet_idempotent : forall t,
  tensor_meet t t =
  match t with
  | TF_App g  => MR_Grade g
  | TF_NotApp => MR_NotApp
  | TF_Exempt => MR_Exempt
  end.
Proof.
  destruct t; simpl; try reflexivity.
  rewrite grade_meet_idempotent. reflexivity.
Qed.

(** On the Applicable fragment (both inputs of the form [TF_App g]),
    the tensor meet reduces to the three-chain meet lifted into
    [MR_Grade], so associativity follows from [grade_meet_assoc]. *)
Lemma tensor_meet_applicable_assoc : forall g1 g2 g3,
  tensor_meet (TF_App g1) (TF_App (grade_meet g2 g3)) =
  tensor_meet (TF_App (grade_meet g1 g2)) (TF_App g3).
Proof.
  intros g1 g2 g3. simpl.
  rewrite grade_meet_assoc. reflexivity.
Qed.

(** Pinning the shared Applicable fragment: if all three inputs are
    Applicable, the composed [tensor_meet] yields the grade-meet of
    all three grades - independent of bracketing. *)
Theorem tensor_meet_applicable_full_assoc : forall g1 g2 g3,
  tensor_meet (TF_App (grade_meet g1 g2)) (TF_App g3) =
  tensor_meet (TF_App g1) (TF_App (grade_meet g2 g3)).
Proof.
  intros g1 g2 g3.
  destruct g1, g2, g3; reflexivity.
Qed.

Lemma tensor_meet_comm : forall a b, tensor_meet a b = tensor_meet b a.
Proof. destruct a, b; simpl; try rewrite grade_meet_comm; reflexivity. Qed.

(** ** Projection from Lex's 5-chain to the tensor-factor *)

(** Lex-paper verdict → SJN tensor-factor.  The three Applicable-fragment
    values (NonCompliant, Pending, Compliant) carry grades on the three-chain;
    the two applicability-marker values (NotApplicable, Exempt) become the
    bare singletons. *)
Definition lex_to_tensor (v : verdict) : tensor_factor :=
  match v with
  | NonCompliant  => TF_App GNonCompliant
  | Pending       => TF_App GPending
  | NotApplicable => TF_NotApp
  | Exempt        => TF_Exempt
  | Compliant     => TF_App GCompliant
  end.

(** Projection is injective. *)
Theorem lex_to_tensor_injective :
  forall v1 v2, lex_to_tensor v1 = lex_to_tensor v2 -> v1 = v2.
Proof.
  intros v1 v2 H. destruct v1, v2; inversion H; reflexivity.
Qed.

(** ** Compatibility on the Applicable fragment *)

(** Within the Applicable fragment - where both inputs project to [TF_App] -
    the Lex 5-chain meet commutes with the tensor meet via [lex_to_tensor].
    That is, the diagram

        verdict × verdict  ──meet──►  verdict
                │                         │
       lex_to_tensor²              lex_to_tensor
                ▼                         ▼
        TF × TF            ─tensor_meet─► meet_result

    commutes on the Applicable sub-lattice, where [tensor_meet] returns
    [MR_Grade] (the grade-axis three-chain meet). *)

Theorem lex_meet_preserves_applicable_fragment :
  forall v1 v2 g1 g2,
    lex_to_tensor v1 = TF_App g1 ->
    lex_to_tensor v2 = TF_App g2 ->
    tensor_meet (lex_to_tensor v1) (lex_to_tensor v2) =
    MR_Grade (grade_meet g1 g2) /\
    lex_to_tensor (meet v1 v2) = TF_App (grade_meet g1 g2).
Proof.
  intros v1 v2 g1 g2 H1 H2.
  split.
  - rewrite H1, H2. reflexivity.
  - destruct v1, v2; inversion H1; inversion H2; subst;
      unfold meet, unrank; simpl; reflexivity.
Qed.

(** Corollary: on the Applicable fragment, the Lex 5-chain meet can be
    computed either by the 5-chain [meet] (Lex layer) or by the three-chain
    [grade_meet] after projection (tensor layer), and the two paths agree. *)
Corollary lex_tensor_diagram_commutes_on_applicable :
  forall v1 v2 g1 g2,
    lex_to_tensor v1 = TF_App g1 ->
    lex_to_tensor v2 = TF_App g2 ->
    lex_to_tensor (meet v1 v2) =
    match tensor_meet (lex_to_tensor v1) (lex_to_tensor v2) with
    | MR_Grade g => TF_App g
    | _ => TF_NotApp  (* unreachable on the Applicable fragment *)
    end.
Proof.
  intros v1 v2 g1 g2 H1 H2.
  destruct (lex_meet_preserves_applicable_fragment _ _ _ _ H1 H2) as [Ht Hm].
  rewrite Ht, Hm. reflexivity.
Qed.

(** ** Provenance loss outside the Applicable fragment (mechanized F144) *)

(** Lex's 5-chain meet, applied outside the Applicable fragment, collapses
    provenance-distinct tensor-factors into a single chain value.  We witness
    one instance: [meet NotApplicable Compliant] under the Lex 5-chain is
    [NotApplicable] (by min-rank on the chain), but the tensor-level meet
    of [TF_NotApp] and [TF_App GCompliant] is [MR_AppVsNotApp GCompliant],
    which preserves the fact that one jurisdiction reported Compliant while
    another reported NotApplicable.

    The Lex-layer meet loses this distinction.  This is the mechanized
    witness of (one direction of) F144: no chain-based total Heyting meet
    can preserve the mixed-axis provenance required by SJN §4.2. *)

Theorem lex_meet_loses_provenance_on_mixed_axis :
  lex_to_tensor (meet NotApplicable Compliant) = TF_NotApp /\
  tensor_meet (lex_to_tensor NotApplicable) (lex_to_tensor Compliant)
    = MR_AppVsNotApp GCompliant /\
  TF_NotApp <> TF_App GCompliant.
Proof.
  split; [| split].
  - unfold meet, lex_to_tensor. simpl. reflexivity.
  - simpl. reflexivity.
  - discriminate.
Qed.

(** A second concrete witness: [meet Exempt Pending] collapses to [Pending]
    on the chain, but the tensor view preserves the Applicable-vs-Exempt
    provenance. *)
Theorem lex_meet_loses_provenance_exempt_vs_pending :
  lex_to_tensor (meet Exempt Pending) = TF_App GPending /\
  tensor_meet (lex_to_tensor Exempt) (lex_to_tensor Pending)
    = MR_AppVsExempt GPending /\
  MR_AppVsExempt GPending <> MR_Grade GPending.
Proof.
  split; [| split].
  - unfold meet, lex_to_tensor. simpl. reflexivity.
  - simpl. reflexivity.
  - discriminate.
Qed.

(** ** Further structural properties (2026-04-20) *)

(** grade_rank is bounded above by 2 (the rank of GCompliant). *)
Lemma grade_rank_bounded : forall g, grade_rank g <= 2.
Proof. destruct g; simpl; lia. Qed.

(** grade_rank is injective. *)
Lemma grade_rank_injective : forall g1 g2,
  grade_rank g1 = grade_rank g2 -> g1 = g2.
Proof. destruct g1, g2; simpl; intro H; try reflexivity; discriminate. Qed.

(** compliance_grade equality is decidable. *)
Lemma compliance_grade_eq_dec :
  forall g1 g2 : compliance_grade, {g1 = g2} + {g1 <> g2}.
Proof. decide equality. Qed.

(** applicability equality is decidable. *)
Lemma applicability_eq_dec :
  forall a1 a2 : applicability, {a1 = a2} + {a1 <> a2}.
Proof. decide equality. Qed.

(** tensor_factor equality is decidable. *)
Lemma tensor_factor_eq_dec :
  forall t1 t2 : tensor_factor, {t1 = t2} + {t1 <> t2}.
Proof. decide equality. apply compliance_grade_eq_dec. Qed.

(** grade_meet is absorbing at grade_bot on both sides. *)
Lemma grade_meet_bot_left : forall g, grade_meet grade_bot g = grade_bot.
Proof. destruct g; reflexivity. Qed.

(** The three tensor_factor constructors are pairwise distinct. *)
Lemma tensor_factor_ctors_distinct :
  TF_NotApp <> TF_Exempt /\
  (forall g, TF_App g <> TF_NotApp) /\
  (forall g, TF_App g <> TF_Exempt).
Proof. repeat split; discriminate. Qed.

(** ** Production n-ary MeetResult *)

(** Production cross-harbor composition is direct n-ary reduction over the
    participating harbors.  Binary [tensor_meet] is the two-harbor case; it
    is not used as an arbitrary fold over the full mixed-axis state space.

    The summary records the aggregate Applicable grade, whether any NotApp
    input occurred, and whether any Exempt input occurred. *)
Definition meet_summary : Type := (option compliance_grade * bool * bool)%type.

Fixpoint grade_meet_list (g : compliance_grade) (gs : list compliance_grade)
  : compliance_grade :=
  match gs with
  | nil => g
  | h :: rest => grade_meet g (grade_meet_list h rest)
  end.

Definition combine_app_grade
  (acc : option compliance_grade) (g : compliance_grade)
  : option compliance_grade :=
  match acc with
  | None => Some g
  | Some h => Some (grade_meet g h)
  end.

Fixpoint summarize_factors (xs : list tensor_factor) : meet_summary :=
  match xs with
  | nil => (None, false, false)
  | TF_App g :: rest =>
      let '(app, saw_notapp, saw_exempt) := summarize_factors rest in
      (combine_app_grade app g, saw_notapp, saw_exempt)
  | TF_NotApp :: rest =>
      let '(app, _saw_notapp, saw_exempt) := summarize_factors rest in
      (app, true, saw_exempt)
  | TF_Exempt :: rest =>
      let '(app, saw_notapp, _saw_exempt) := summarize_factors rest in
      (app, saw_notapp, true)
  end.

Definition classify_summary (s : meet_summary) : meet_result :=
  match s with
  | (None, false, false) => MR_Empty
  | (None, true, false) => MR_NotApp
  | (None, false, true) => MR_Exempt
  | (None, true, true) => MR_NotAppVsExempt
  | (Some g, false, false) => MR_Grade g
  | (Some g, true, false) => MR_AppVsNotApp g
  | (Some g, false, true) => MR_AppVsExempt g
  | (Some g, true, true) => MR_AppVsNotAppVsExempt g
  end.

Definition tensor_meet_all (xs : list tensor_factor) : meet_result :=
  classify_summary (summarize_factors xs).

Lemma summarize_factors_map_applicable : forall gs,
  summarize_factors (map TF_App gs) =
  match gs with
  | nil => (None, false, false)
  | g :: rest => (Some (grade_meet_list g rest), false, false)
  end.
Proof.
  induction gs as [|g rest IH]; simpl.
  - reflexivity.
  - rewrite IH. destruct rest; reflexivity.
Qed.

Lemma summarize_factors_all_applicable : forall g gs,
  summarize_factors (TF_App g :: map TF_App gs) =
  (Some (grade_meet_list g gs), false, false).
Proof.
  intros g gs. simpl.
  rewrite summarize_factors_map_applicable.
  destruct gs; reflexivity.
Qed.

Theorem tensor_meet_all_applicable_fragment : forall g gs,
  tensor_meet_all (TF_App g :: map TF_App gs) =
  MR_Grade (grade_meet_list g gs).
Proof.
  intros g gs.
  unfold tensor_meet_all.
  rewrite summarize_factors_all_applicable.
  reflexivity.
Qed.

Theorem tensor_meet_all_binary_agrees : forall a b,
  tensor_meet_all (a :: b :: nil) = tensor_meet a b.
Proof.
  destruct a, b; simpl; reflexivity.
Qed.

Theorem tensor_meet_all_three_way_provenance : forall g,
  tensor_meet_all (TF_App g :: TF_NotApp :: TF_Exempt :: nil) =
  MR_AppVsNotAppVsExempt g.
Proof. destruct g; reflexivity. Qed.

(** Result-shape predicates used by downstream extraction/diagnostics.  They
    are intentionally not a compliance order and are not used to define
    residuals, joins, or admission. *)
Definition result_mentions_applicable (r : meet_result) : Prop :=
  match r with
  | MR_Grade _ | MR_AppVsNotApp _ | MR_AppVsExempt _
  | MR_AppVsNotAppVsExempt _ => True
  | _ => False
  end.

Definition result_mentions_notapp (r : meet_result) : Prop :=
  match r with
  | MR_NotApp | MR_AppVsNotApp _ | MR_NotAppVsExempt
  | MR_AppVsNotAppVsExempt _ => True
  | _ => False
  end.

Definition result_mentions_exempt (r : meet_result) : Prop :=
  match r with
  | MR_Exempt | MR_AppVsExempt _ | MR_NotAppVsExempt
  | MR_AppVsNotAppVsExempt _ => True
  | _ => False
  end.

Theorem tensor_meet_all_reports_three_axes : forall g,
  result_mentions_applicable
    (tensor_meet_all (TF_App g :: TF_NotApp :: TF_Exempt :: nil)) /\
  result_mentions_notapp
    (tensor_meet_all (TF_App g :: TF_NotApp :: TF_Exempt :: nil)) /\
  result_mentions_exempt
    (tensor_meet_all (TF_App g :: TF_NotApp :: TF_Exempt :: nil)).
Proof. destruct g; repeat split. Qed.

(** Boolean flag exactness for the production n-ary core.  This is the
    mechanized core of the audit statement: the result shape records exactly
    which applicability axes appeared in the composed harbor list. *)
Definition factor_has_applicable_b (t : tensor_factor) : bool :=
  match t with
  | TF_App _ => true
  | _ => false
  end.

Definition factor_has_notapp_b (t : tensor_factor) : bool :=
  match t with
  | TF_NotApp => true
  | _ => false
  end.

Definition factor_has_exempt_b (t : tensor_factor) : bool :=
  match t with
  | TF_Exempt => true
  | _ => false
  end.

Fixpoint any_applicable_b (xs : list tensor_factor) : bool :=
  match xs with
  | nil => false
  | x :: rest => factor_has_applicable_b x || any_applicable_b rest
  end.

Fixpoint any_notapp_b (xs : list tensor_factor) : bool :=
  match xs with
  | nil => false
  | x :: rest => factor_has_notapp_b x || any_notapp_b rest
  end.

Fixpoint any_exempt_b (xs : list tensor_factor) : bool :=
  match xs with
  | nil => false
  | x :: rest => factor_has_exempt_b x || any_exempt_b rest
  end.

Definition option_grade_present_b (app : option compliance_grade) : bool :=
  match app with
  | Some _ => true
  | None => false
  end.

Definition result_mentions_applicable_b (r : meet_result) : bool :=
  match r with
  | MR_Grade _ | MR_AppVsNotApp _ | MR_AppVsExempt _
  | MR_AppVsNotAppVsExempt _ => true
  | _ => false
  end.

Definition result_mentions_notapp_b (r : meet_result) : bool :=
  match r with
  | MR_NotApp | MR_AppVsNotApp _ | MR_NotAppVsExempt
  | MR_AppVsNotAppVsExempt _ => true
  | _ => false
  end.

Definition result_mentions_exempt_b (r : meet_result) : bool :=
  match r with
  | MR_Exempt | MR_AppVsExempt _ | MR_NotAppVsExempt
  | MR_AppVsNotAppVsExempt _ => true
  | _ => false
  end.

Lemma summarize_factors_flags_exact : forall xs app saw_notapp saw_exempt,
  summarize_factors xs = (app, saw_notapp, saw_exempt) ->
  option_grade_present_b app = any_applicable_b xs /\
  saw_notapp = any_notapp_b xs /\
  saw_exempt = any_exempt_b xs.
Proof.
  induction xs as [|x rest IH]; simpl; intros app saw_notapp saw_exempt Hsum.
  - inversion Hsum. repeat split; reflexivity.
  - destruct x as [g| |];
      destruct (summarize_factors rest) as [[rest_app rest_notapp] rest_exempt] eqn:Hrest;
      specialize (IH rest_app rest_notapp rest_exempt eq_refl)
        as [Happ [Hnotapp Hexempt]];
      inversion Hsum; subst; simpl in *.
    + destruct rest_app; simpl; repeat split; try reflexivity; assumption.
    + repeat split; try reflexivity; assumption.
    + repeat split; try reflexivity; assumption.
Qed.

Lemma classify_summary_flags_exact : forall app saw_notapp saw_exempt,
  result_mentions_applicable_b (classify_summary (app, saw_notapp, saw_exempt)) =
    option_grade_present_b app /\
  result_mentions_notapp_b (classify_summary (app, saw_notapp, saw_exempt)) =
    saw_notapp /\
  result_mentions_exempt_b (classify_summary (app, saw_notapp, saw_exempt)) =
    saw_exempt.
Proof.
  intros app saw_notapp saw_exempt.
  destruct app as [g|]; destruct saw_notapp, saw_exempt; simpl; repeat split; reflexivity.
Qed.

Theorem tensor_meet_all_flags_exact : forall xs,
  result_mentions_applicable_b (tensor_meet_all xs) = any_applicable_b xs /\
  result_mentions_notapp_b (tensor_meet_all xs) = any_notapp_b xs /\
  result_mentions_exempt_b (tensor_meet_all xs) = any_exempt_b xs.
Proof.
  intros xs.
  unfold tensor_meet_all.
  destruct (summarize_factors xs) as [[app saw_notapp] saw_exempt] eqn:Hsum.
  destruct (classify_summary_flags_exact app saw_notapp saw_exempt)
    as [Hclass_app [Hclass_notapp Hclass_exempt]].
  destruct (summarize_factors_flags_exact xs app saw_notapp saw_exempt Hsum)
    as [Hsum_app [Hsum_notapp Hsum_exempt]].
  repeat split.
  - rewrite Hclass_app. exact Hsum_app.
  - rewrite Hclass_notapp. exact Hsum_notapp.
  - rewrite Hclass_exempt. exact Hsum_exempt.
Qed.

(** ** A formal mixed-axis impossibility core *)

(** A total [tensor_factor]-valued meet would have to choose either an
    Applicable value or a non-applicability singleton on mixed
    Applicable-vs-NotApp inputs.  The two desired requirements contradict:
    preserving the Applicable compliance signal requires an Applicable
    output, while keeping NotApp orthogonal to Applicable grades forbids one.
    [MeetResult] is the structured escape hatch. *)
Definition preserves_app_signal_on_notapp
  (op : tensor_factor -> tensor_factor -> tensor_factor) : Prop :=
  forall g, exists h, op (TF_App g) TF_NotApp = TF_App h.

Definition keeps_notapp_orthogonal_to_app
  (op : tensor_factor -> tensor_factor -> tensor_factor) : Prop :=
  forall g h, op (TF_App g) TF_NotApp <> TF_App h.

Theorem no_total_tensor_factor_meet_preserves_signal_and_orthogonality :
  forall op,
    preserves_app_signal_on_notapp op ->
    keeps_notapp_orthogonal_to_app op ->
    False.
Proof.
  intros op Hsignal Horth.
  destruct (Hsignal GCompliant) as [h Heq].
  exact (Horth GCompliant h Heq).
Qed.

(** ** Summary

    [lex_to_tensor] is the projection from the Lex per-coordinate 5-chain
    to the SJN tensor-factor.  It is injective and, on the Applicable
    fragment, commutes with meet.  Outside the Applicable fragment, it
    witnesses F144's impossibility dichotomy: the Lex 5-chain meet loses
    provenance that the MeetResult-valued tensor meet preserves.

    This file is the Coq witness that the two Coq mechanizations of verdict
    algebra (VerdictHeyting.v and the SJN tensor-factor defined here) are
    not in conflict: they are compositional-level views, related by a meet-
    preserving projection on their common sub-lattice and separated by F144
    outside it. *)
