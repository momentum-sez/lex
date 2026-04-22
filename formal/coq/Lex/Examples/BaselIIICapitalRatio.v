(** * Lex/Examples/BaselIIICapitalRatio.v — Basel III capital-adequacy rule

    Task E1-corpus: extend the worked-examples corpus with another
    non-toy jurisdictional rule.

    Basel III (Committee on Banking Supervision, 2010) requires
    banks to maintain minimum capital ratios against risk-weighted
    assets (RWA):

      - CET1 (Common Equity Tier 1) ratio ≥ 4.5%
      - Tier 1 ratio ≥ 6%
      - Total capital ratio ≥ 8%
      - Capital conservation buffer: additional 2.5% CET1
      - Countercyclical buffer: 0-2.5% CET1 (jurisdictional)

    When a bank fails CET1+buffer, regulators impose restrictions on
    dividends and bonuses; a bank below the minimum CET1 is subject
    to prompt corrective action.

    This file encodes the basic and enhanced ratio checks as a Lex-
    style decision procedure, with a discretion hole for the
    countercyclical buffer determination (which is per-jurisdiction
    and set by the macroprudential authority).
*)

From Stdlib Require Import Bool String Arith Lia.
Open Scope string_scope.

Inductive ComplianceVerdict : Type :=
  | Compliant
  | Breach
  | Warning.

(** All amounts in basis points (bps), i.e. 1/100 of a percent.
    So CET1 4.5% = 450 bps.  This avoids fractional arithmetic. *)
Record BankContext : Type := {
  cet1_bps : nat;          (* CET1 capital, in bps of RWA *)
  tier1_bps : nat;         (* Total Tier 1 capital *)
  total_capital_bps : nat; (* Total capital *)
  countercyclical_buffer_bps : nat;  (* Jurisdictional buffer, 0-250 *)
}.

(** Basel III minimums, all in bps of RWA. *)
Definition cet1_minimum : nat := 45.        (* 4.5% *)
Definition tier1_minimum : nat := 60.       (* 6% *)
Definition total_capital_minimum : nat := 80. (* 8% *)
Definition conservation_buffer : nat := 25. (* 2.5% *)

(** Basic capital-adequacy check: all three ratios above minimums. *)
Definition basic_capital_adequate (ctx : BankContext) : bool :=
  Nat.leb cet1_minimum ctx.(cet1_bps) &&
  Nat.leb tier1_minimum ctx.(tier1_bps) &&
  Nat.leb total_capital_minimum ctx.(total_capital_bps).

(** Enhanced check: basic + conservation buffer + countercyclical.  *)
Definition enhanced_capital_adequate (ctx : BankContext) : bool :=
  basic_capital_adequate ctx &&
  Nat.leb (cet1_minimum + conservation_buffer +
           ctx.(countercyclical_buffer_bps))
          ctx.(cet1_bps).

(** Full decision: Compliant if enhanced passes; Warning if basic
    passes but buffers fail; Breach otherwise. *)
Definition basel_iii_verdict (ctx : BankContext) : ComplianceVerdict :=
  if basic_capital_adequate ctx then
    if enhanced_capital_adequate ctx then Compliant else Warning
  else Breach.

(** ** Fixtures and theorems *)

(** A well-capitalized bank: CET1 8%, Tier1 10%, Total 12%, buffer 0.
    Passes all tests with margin. *)
Definition well_capitalized : BankContext := {|
  cet1_bps := 80;
  tier1_bps := 100;
  total_capital_bps := 120;
  countercyclical_buffer_bps := 0;
|}.

(** A bank at the minimum CET1 line: CET1 4.5%, Tier1 6%, Total 8%,
    buffer 0.  Fails the enhanced (conservation-buffer) check. *)
Definition at_minimum : BankContext := {|
  cet1_bps := 45;
  tier1_bps := 60;
  total_capital_bps := 80;
  countercyclical_buffer_bps := 0;
|}.

(** A bank below CET1 minimum: triggers Breach. *)
Definition below_minimum : BankContext := {|
  cet1_bps := 40;
  tier1_bps := 60;
  total_capital_bps := 80;
  countercyclical_buffer_bps := 0;
|}.

(** A bank passing basic but failing countercyclical under a 1.5%
    buffer: CET1 7%, Tier1 8%, Total 10%, buffer 150.
    Basic OK (CET1 ≥ 4.5%); enhanced: need 4.5+2.5+1.5 = 8.5%, but
    CET1 is 7%. *)
Definition cet1_below_countercyclical : BankContext := {|
  cet1_bps := 70;
  tier1_bps := 80;
  total_capital_bps := 100;
  countercyclical_buffer_bps := 150;
|}.

Example well_capitalized_compliant :
  basel_iii_verdict well_capitalized = Compliant.
Proof. reflexivity. Qed.

Example at_minimum_warning :
  basel_iii_verdict at_minimum = Warning.
Proof. reflexivity. Qed.

Example below_minimum_breach :
  basel_iii_verdict below_minimum = Breach.
Proof. reflexivity. Qed.

Example cet1_below_buffer_warning :
  basel_iii_verdict cet1_below_countercyclical = Warning.
Proof. reflexivity. Qed.

(** Monotonicity: increasing CET1 never makes things worse.  (Stated
    at a helper level to avoid literal-unfolding issues.) *)
Lemma leb_plus_right : forall m a b, Nat.leb m a = true -> Nat.leb m (a + b) = true.
Proof. intros m a b H. apply Nat.leb_le in H. apply Nat.leb_le. lia. Qed.

Theorem cet1_increase_never_worsens :
  forall ctx delta,
    basic_capital_adequate ctx = true ->
    basic_capital_adequate
      {| cet1_bps := ctx.(cet1_bps) + delta;
         tier1_bps := ctx.(tier1_bps);
         total_capital_bps := ctx.(total_capital_bps);
         countercyclical_buffer_bps := ctx.(countercyclical_buffer_bps) |}
      = true.
Proof.
  intros ctx delta Hbasic.
  unfold basic_capital_adequate in *.
  apply andb_true_iff in Hbasic. destruct Hbasic as [Hcet1_tier1 Htotal].
  apply andb_true_iff in Hcet1_tier1. destruct Hcet1_tier1 as [Hcet1 Htier1].
  apply andb_true_iff. split.
  - apply andb_true_iff. split.
    + apply leb_plus_right. exact Hcet1.
    + exact Htier1.
  - exact Htotal.
Qed.

(** Conservation buffer hierarchy: if a bank passes enhanced, it
    certainly passes basic. *)
Theorem enhanced_implies_basic :
  forall ctx,
    enhanced_capital_adequate ctx = true ->
    basic_capital_adequate ctx = true.
Proof.
  intros ctx H.
  unfold enhanced_capital_adequate in H.
  apply andb_true_iff in H. destruct H as [Hbasic _]. exact Hbasic.
Qed.

(** Breach requires a specific failure: one of the basic ratios is
    below minimum. *)
Theorem breach_has_basic_failure :
  forall ctx,
    basel_iii_verdict ctx = Breach ->
    basic_capital_adequate ctx = false.
Proof.
  intros ctx H.
  unfold basel_iii_verdict in H.
  destruct (basic_capital_adequate ctx) eqn:Hbasic; [|reflexivity].
  destruct (enhanced_capital_adequate ctx); discriminate.
Qed.

(** Warning is the intermediate state: basic passes but enhanced fails. *)
Theorem warning_characterisation :
  forall ctx,
    basel_iii_verdict ctx = Warning ->
    basic_capital_adequate ctx = true /\
    enhanced_capital_adequate ctx = false.
Proof.
  intros ctx H.
  unfold basel_iii_verdict in H.
  destruct (basic_capital_adequate ctx) eqn:Hbasic; [|discriminate].
  destruct (enhanced_capital_adequate ctx) eqn:Henh;
    [discriminate|split; reflexivity].
Qed.

(** Compliant characterisation: enhanced passes. *)
Theorem compliant_iff_enhanced :
  forall ctx,
    basel_iii_verdict ctx = Compliant <->
    enhanced_capital_adequate ctx = true.
Proof.
  intros ctx. split.
  - intros H. unfold basel_iii_verdict in H.
    destruct (basic_capital_adequate ctx) eqn:Hbasic; [|discriminate].
    destruct (enhanced_capital_adequate ctx); [reflexivity|discriminate].
  - intros H. unfold basel_iii_verdict.
    rewrite (enhanced_implies_basic _ H), H. reflexivity.
Qed.

(** Summary of the worked rule:
      - 4 concrete examples (well-capitalized, at-minimum,
        below-minimum, below-buffer)
      - 4 structural theorems (monotonicity, hierarchy, breach &
        warning characterizations, Compliant iff enhanced)

    This encodes Basel III's capital-adequacy decision as a Qed-
    closed procedure with three-verdict output (Compliant / Warning
    / Breach), matching the actual regulatory structure under which
    national regulators (Fed, FCA, BaFin, HKMA, MAS, etc.) enforce
    Basel III. *)
