From Stdlib Require Import Bool List.
Import ListNotations.

(** Seychelles International Business Companies Act 2016, s.130(1):

    "A company shall at all times have at least one director appointed
    in accordance with this Act, except where otherwise provided by
    another written law of Seychelles."

    The statutory predicate is a bounded existential over the
    directors collection: at least one director holds an appointment
    made under the Act.  Section 133(1) provides that a director shall
    be an individual or a body corporate, so s.130(1) imposes no
    natural-person test and this encoding contains none.  The s.2
    definition of "director" reaches de facto occupants of the office,
    and s.131, as substituted by the International Business Companies
    (Amendment) Act 2021 (Act 32 of 2021) s.21, provides that whenever
    a company does not have a director, any person who manages, or
    directs or supervises the management of, its business and affairs
    is deemed a director for the purposes of the Act; the deeming
    presupposes that the company has no director. The model does not
    infer appointment under the Act from deemed directorship. This is
    an input-model assumption, not a proved interpretation of the Act.
    The record carries the appointment fact rather than a head count.

    Subsection (1) is disapplied in two ways: by its own closing
    words, where another written law of Seychelles provides otherwise,
    and by s.130(2), between incorporation and the appointment of the
    first directors.  Disapplication is encoded as the distinct
    verdict [NotApplicable]: the rule reports that the requirement
    does not bind, which is not the same as reporting that it is
    satisfied.  Because both disapplications yield the same verdict,
    the order in which the rule tests them is immaterial.

    The rule evaluates three facts of record.
    [appointed_under_act] states that the appointment is valid under
    the Act, folding in s.133 eligibility - s.133(1) admits an
    individual or a body corporate subject to the s.133(2) bars, the
    company's memorandum and articles, and the International Corporate
    Service Providers Act (Cap 275) - and s.134 procedure; the rule
    does not re-derive that validity.  [displaced_by_other_written_law]
    resolves the carve-out, a reference out of this rule into the rest
    of Seychelles law.  [first_directors_appointed] is false only
    between incorporation and the first appointment and never reverts,
    so a later vacancy falls under subsection (1) and reads
    NonCompliant.  The s.134(1) duty to appoint the first directors
    within 30 days of incorporation, as amended by Act 13 of 2026 s.2,
    is a temporal obligation this
    rule does not carry, and s.130(3) is permissive - the articles may
    fix the number of directors, subject to subsection (1) - so it adds
    no requirement to encode.

    Statutory sources:
    International Business Companies Act 2016, ss.130-134:
    https://www.a-mla.org/en/country/pdf/1808
    International Business Companies (Amendment) Act 2021, Act 32, s.21:
    https://www.gazette.sc/sites/default/files/2021-08/Act%2032%20-%20International%20Business%20Companies%20(Amendment)%20Act%202021.pdf
    Seychelles Official Gazette, 24 August 2026,
    International Business Companies (Amendment) Act 2026, Act 13, s.2:
    https://www.gazette.sc/sites/default/files/2026-08/Act%2013%202026%20-%20International%20Business%20Companies%20(Amendment)%20Act%202026.pdf *)

Inductive ComplianceVerdict : Type :=
  | Compliant
  | NonCompliant
  | NotApplicable.

Record Director : Type := {
  appointed_under_act : bool;
  is_body_corporate   : bool;
}.

Record CompanyContext : Type := {
  directors                      : list Director;
  first_directors_appointed      : bool;
  displaced_by_other_written_law : bool;
}.

Definition has_director_appointed_under_act (ctx : CompanyContext) : bool :=
  existsb appointed_under_act ctx.(directors).

Definition seychelles_s130_rule (ctx : CompanyContext) : ComplianceVerdict :=
  if ctx.(displaced_by_other_written_law) then NotApplicable
  else if negb ctx.(first_directors_appointed) then NotApplicable
  else if has_director_appointed_under_act ctx then Compliant
  else NonCompliant.

(** ** Test vectors *)

Definition pre_appointment_ctx : CompanyContext :=
  {| directors := [];
     first_directors_appointed := false;
     displaced_by_other_written_law := false |}.

Definition displaced_ctx : CompanyContext :=
  {| directors := [];
     first_directors_appointed := true;
     displaced_by_other_written_law := true |}.

Definition empty_board_ctx : CompanyContext :=
  {| directors := [];
     first_directors_appointed := true;
     displaced_by_other_written_law := false |}.

Definition unappointed_board_ctx : CompanyContext :=
  {| directors := [{| appointed_under_act := false; is_body_corporate := false |}];
     first_directors_appointed := true;
     displaced_by_other_written_law := false |}.

Definition corporate_only_board_ctx : CompanyContext :=
  {| directors := [{| appointed_under_act := true; is_body_corporate := true |}];
     first_directors_appointed := true;
     displaced_by_other_written_law := false |}.

Definition natural_board_ctx : CompanyContext :=
  {| directors := [{| appointed_under_act := true; is_body_corporate := false |}];
     first_directors_appointed := true;
     displaced_by_other_written_law := false |}.

(** Inside the s.130(2) window the requirement does not apply. *)
Example pre_appointment_is_not_applicable :
  seychelles_s130_rule pre_appointment_ctx = NotApplicable.
Proof. reflexivity. Qed.

(** Where another written law provides otherwise, the requirement does
    not apply - here to a board that would otherwise be NonCompliant. *)
Example displaced_is_not_applicable :
  seychelles_s130_rule displaced_ctx = NotApplicable.
Proof. reflexivity. Qed.

Example empty_board_is_noncompliant :
  seychelles_s130_rule empty_board_ctx = NonCompliant.
Proof. reflexivity. Qed.

(** An occupant whose supplied [appointed_under_act] fact is false
    receives [NonCompliant] in this model.
    Section 131 applies only while the company has no director, and it
    does not set [appointed_under_act] in this input model. The result
    follows from that supplied fact, not from a legal-validity proof. *)
Example unappointed_board_is_noncompliant :
  seychelles_s130_rule unappointed_board_ctx = NonCompliant.
Proof. reflexivity. Qed.

(** A board consisting solely of a body corporate satisfies s.130(1):
    the section tests appointment under the Act, and s.133(1) admits a
    body corporate as a director subject to the s.133(2) bars, the
    memorandum and articles, and the International Corporate Service
    Providers Act, provisos that [appointed_under_act] absorbs. *)
Example corporate_only_board_is_compliant :
  seychelles_s130_rule corporate_only_board_ctx = Compliant.
Proof. reflexivity. Qed.

Example natural_board_is_compliant :
  seychelles_s130_rule natural_board_ctx = Compliant.
Proof. reflexivity. Qed.

(** ** Results

    The three lemmas restate the branches of the definition and hold
    by computation, one after a case split on the free carve-out flag.
    They quantify over the rule's entire input space, which includes
    contexts a conforming registry never produces; they are statements
    about the rule, not about reachable registry states.  The theorem
    is the formal witness for the personality claim: the verdict is
    invariant under repainting [is_body_corporate] with an arbitrary
    function of the director, so the rule reads no personality
    information at all. The appointment-validity fact remains fixed.
    The theorem does not establish that a real change of legal personality
    preserves appointment validity. *)

Lemma carve_out_dominates :
  forall ds w,
    seychelles_s130_rule
      {| directors := ds;
         first_directors_appointed := w;
         displaced_by_other_written_law := true |} = NotApplicable.
Proof. intros ds w. reflexivity. Qed.

Lemma s130_2_dominates :
  forall ds b,
    seychelles_s130_rule
      {| directors := ds;
         first_directors_appointed := false;
         displaced_by_other_written_law := b |} = NotApplicable.
Proof. intros ds b. destruct b; reflexivity. Qed.

Lemma s130_1_is_the_bounded_existential :
  forall ds,
    seychelles_s130_rule
      {| directors := ds;
         first_directors_appointed := true;
         displaced_by_other_written_law := false |}
    = (if existsb appointed_under_act ds then Compliant else NonCompliant).
Proof. intros ds. reflexivity. Qed.

Definition set_personality (f : Director -> bool) (d : Director) : Director :=
  {| appointed_under_act := d.(appointed_under_act);
     is_body_corporate   := f d |}.

Lemma existsb_appointed_set_personality :
  forall f ds,
    existsb appointed_under_act (map (set_personality f) ds)
    = existsb appointed_under_act ds.
Proof.
  intros f ds. induction ds as [|d ds IH]; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Theorem verdict_ignores_personality :
  forall (f : Director -> bool) (ctx : CompanyContext),
    seychelles_s130_rule
      {| directors := map (set_personality f) ctx.(directors);
         first_directors_appointed := ctx.(first_directors_appointed);
         displaced_by_other_written_law := ctx.(displaced_by_other_written_law) |}
    = seychelles_s130_rule ctx.
Proof.
  intros f ctx.
  unfold seychelles_s130_rule, has_director_appointed_under_act; simpl.
  rewrite existsb_appointed_set_personality. reflexivity.
Qed.
