//! Fill rule — effect-row flow-through.
//!
//! Paper reference: "Lex: A Logic for Jurisdictional Rules" §4.7 "Fill" rule.
//!
//! The Fill rule, in paper form, is
//!
//! ```text
//!   G |- e : A [ρ]                (filler judgment with effect row ρ)
//!   ───────────────────────────── (Fill)
//!   G |- fill(h, e, w) : A [ρ]    (filled hole inherits ρ)
//! ```
//!
//! Two consequences follow:
//!
//! - **Flow-through.** When the filler term is typed with effect row `ρ`,
//!   the fill-expression propagates that same row to the enclosing term.
//!   A fill does not mint a new effect; it exposes the filler's effect at
//!   the hole site.
//!
//! - **Admissibility gate.** The executable admissibility fragment requires
//!   `ρ = ∅`. A filler with residual effect (e.g., an oracle query, a
//!   write, or an authority gate) is NOT admissible as a hole filling.
//!   The check rides at the pre-admissibility layer — the effect row is
//!   observed at the filler's root and rejected before the admissibility
//!   predicate admits the term.
//!
//! The main `lex-core` checker currently rejects `HoleFill` outright at
//! the admissibility boundary — cycle-3 fix — so this test runs at the
//! pre-admissibility layer. It exercises the `EffectRow` algebra the way
//! the Fill rule composes it: construct a filler's row, ask whether it
//! would flow through the hole, and assert the admissibility gate kicks
//! in exactly when `ρ ≠ ∅`.

use lex_core::effects::{effect_join, is_pure, Effect, EffectRow};

/// The Fill rule composes the filler's effect row into the filled-hole
/// position. We model that composition here with the same `effect_join`
/// primitive the typechecker uses for effect composition. For pure
/// fillers (`ρ = ∅`), the row remains empty. For an effectful filler,
/// the non-empty row surfaces at the fill site.
fn flow_through_fill(filler_row: &EffectRow, hole_context_row: &EffectRow) -> EffectRow {
    // The paper writes `[ρ]` on the conclusion, which is the join of the
    // filler's row into whatever row the enclosing context already has.
    // Join with ∅ is identity; join with a non-empty row materializes
    // every filler effect at the site.
    effect_join(filler_row, hole_context_row)
}

/// The admissibility gate — the filler must be PURE for the admissible
/// fragment to accept a `HoleFill`. Any residual effect disqualifies the
/// filler at pre-admissibility.
fn filler_admissible_for_hole_fill(filler_row: &EffectRow) -> bool {
    is_pure(filler_row)
}

fn oracle_effect() -> Effect {
    Effect::Oracle("ComplianceOracle".to_string())
}

fn authority_effect() -> Effect {
    Effect::Authority("ADGM-FSRA".to_string())
}

fn write_effect() -> Effect {
    Effect::Write("EntityRegistry".to_string())
}

#[test]
fn pure_filler_flows_through_as_empty_row() {
    // ρ = ∅ → the filled hole carries ∅. The paper's Fill rule reads:
    // "if the filler types pure, so does the fill-expression." This
    // test exercises that branch.
    let filler_row = EffectRow::empty();
    let hole_context = EffectRow::empty();
    let resulting = flow_through_fill(&filler_row, &hole_context);

    assert!(
        is_pure(&resulting),
        "pure filler into pure context should remain pure; got {resulting:?}"
    );
    assert!(
        filler_admissible_for_hole_fill(&filler_row),
        "the admissibility gate must admit a pure filler"
    );
}

#[test]
fn effectful_filler_carries_its_row_through_the_fill_site() {
    // ρ = {oracle(...)} → the filled hole carries {oracle(...)}. The
    // effect does NOT get hidden behind the fill: a downstream
    // subsumption check will see the oracle effect and must decide
    // whether the enclosing context admits it.
    let oracle_row = EffectRow::from_effects([oracle_effect()]);
    let hole_context = EffectRow::empty();
    let resulting = flow_through_fill(&oracle_row, &hole_context);

    assert!(
        !is_pure(&resulting),
        "oracle-effect filler should propagate its effect to the fill site; got {resulting:?}"
    );
    assert!(
        resulting.contains(&oracle_effect()),
        "the fill site's row must contain oracle(ComplianceOracle)"
    );
}

#[test]
fn admissibility_gate_rejects_effectful_fillers() {
    // Post-substitution, a filler with ρ ≠ ∅ is rejected by the
    // pre-admissibility layer. Test every effect kind the filler can
    // carry — read, write, attest, authority, oracle, sanctions,
    // discretion, fuel — and assert the gate kicks in in every case.
    let effects = [
        Effect::Read,
        oracle_effect(),
        authority_effect(),
        Effect::SanctionsQuery,
        Effect::Attest("ADGM-FSRA".to_string()),
        Effect::Discretion("ADGM-FSRA".to_string()),
        write_effect(),
        Effect::Fuel(0, 1),
    ];
    for e in effects {
        let row = EffectRow::from_effects([e.clone()]);
        assert!(
            !filler_admissible_for_hole_fill(&row),
            "admissibility must reject filler with effect {e:?}"
        );
    }
}

#[test]
fn fill_effect_row_composition_is_monotone_in_filler_row() {
    // Adding an effect to the filler's row never shrinks the row that
    // flows through the fill site. This is the weakening direction of
    // the Fill rule: growing ρ cannot reduce the fill's visible row.
    let base_row = EffectRow::empty();
    let one_effect = EffectRow::from_effects([Effect::Read]);
    let two_effects = EffectRow::from_effects([Effect::Read, oracle_effect()]);

    let hole_context = EffectRow::empty();
    let r0 = flow_through_fill(&base_row, &hole_context);
    let r1 = flow_through_fill(&one_effect, &hole_context);
    let r2 = flow_through_fill(&two_effects, &hole_context);

    assert!(r0.len() <= r1.len(), "adding a filler effect shrank the row: {r0:?} vs {r1:?}");
    assert!(r1.len() <= r2.len(), "adding another filler effect shrank the row: {r1:?} vs {r2:?}");

    // Spot check each effect appears at the fill site.
    assert!(r1.contains(&Effect::Read));
    assert!(r2.contains(&Effect::Read));
    assert!(r2.contains(&oracle_effect()));
}

#[test]
fn pre_admissibility_layer_is_observable_independently_of_main_checker() {
    // The main `lex-core::typecheck::check_admissibility` rejects
    // `Term::HoleFill` with `HoleFillNotSupported` — the cycle-3 fix.
    // The pre-admissibility layer — the effect row analysis — still
    // runs over the filler subterm. This test witnesses that the
    // admissibility gate is ALREADY OBSERVABLE at the effect-row layer
    // even though the main checker stops before emitting a verdict
    // for the fill site itself.
    //
    // Construct one admissible pair (pure filler) and one inadmissible
    // pair (effectful filler) and assert the effect-row layer
    // discriminates them correctly — i.e., the gate is a function of
    // the filler's row alone, not of whether the main checker accepts
    // the whole term.
    let admissible_filler_row = EffectRow::empty();
    let inadmissible_filler_row = EffectRow::from_effects([write_effect()]);

    assert!(filler_admissible_for_hole_fill(&admissible_filler_row));
    assert!(!filler_admissible_for_hole_fill(&inadmissible_filler_row));

    // The fill-rule flow-through is UNCHANGED by admissibility: even for
    // an inadmissible filler, the effect row that would flow through is
    // exactly the filler's row. Admissibility is a gate, not a rewrite.
    let hole_context = EffectRow::empty();
    let flowed = flow_through_fill(&inadmissible_filler_row, &hole_context);
    assert_eq!(flowed.len(), 1);
}

#[test]
fn reference_ast_shape_for_holefill_is_stable() {
    // A minimal smoke-check that the ast::Term::HoleFill constructor
    // has the shape the Fill rule relies on: a hole name, a filler
    // term, and a pcauth witness term. This guards the test against
    // the AST drifting out from under the Fill rule.
    use lex_core::ast::{Ident, QualIdent, Term};
    let hole_name = Some(Ident::new("fit_check"));
    let filler = Term::Constant(QualIdent::simple("Pending"));
    let pcauth = Term::Constant(QualIdent::simple("True"));
    let t = Term::HoleFill {
        hole_name: hole_name.clone(),
        filler: Box::new(filler.clone()),
        pcauth: Box::new(pcauth.clone()),
    };
    match t {
        Term::HoleFill {
            hole_name: hn,
            filler: f,
            pcauth: p,
        } => {
            assert_eq!(hn, hole_name);
            assert_eq!(*f, filler);
            assert_eq!(*p, pcauth);
        }
        _ => panic!("Term::HoleFill did not round-trip through pattern match"),
    }
}

#[test]
fn fill_flow_through_respects_pre_existing_hole_context() {
    // When the enclosing context already carries its own effects, the
    // fill site UNIONS the filler's row with the context's row. This
    // matches the paper's Fill rule composing the filler's judgment
    // into the enclosing term's judgment — neither side is dropped,
    // neither side masks the other.
    let context_row = EffectRow::from_effects([Effect::Read]);
    let filler_row = EffectRow::from_effects([oracle_effect()]);
    let joined = flow_through_fill(&filler_row, &context_row);

    assert_eq!(joined.len(), 2, "context effect + filler effect must both be visible");
    assert!(joined.contains(&Effect::Read));
    assert!(joined.contains(&oracle_effect()));
}
