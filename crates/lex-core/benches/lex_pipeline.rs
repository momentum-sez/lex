use criterion::{black_box, criterion_group, criterion_main, Criterion, Throughput};
use mez_lex::{
    ast::{Branch, Constructor, DefeasibleRule, Ident, Pattern, QualIdent, Term},
    debruijn, elaborate, lexer, obligations, parser, prelude, typecheck,
};

const IBC_S66_RULE_BODY_SOURCE: &str = r#"lambda(ctx : IncorporationContext).
  match director_count ctx return ComplianceVerdict with
  | Zero => NonCompliant
  | _ => Compliant
end"#;

const IBC_S66_ACCESSOR_SOURCE: &str =
    "lambda(ctx : IncorporationContext). director_count ctx";

fn parse_source(source: &str) -> Term {
    let tokens = lexer::lex(source).expect("benchmark source should lex");
    parser::parse(&tokens).expect("benchmark source should parse")
}

fn constructor_branch(name: &str, body: Term) -> Branch {
    Branch {
        pattern: Pattern::Constructor {
            constructor: Constructor::new(QualIdent::simple(name)),
            binders: Vec::new(),
        },
        body,
    }
}

fn wildcard_branch(body: Term) -> Branch {
    Branch {
        pattern: Pattern::Wildcard,
        body,
    }
}

fn ibc_s66_minimum_directors_rule() -> Term {
    Term::Defeasible(DefeasibleRule {
        name: Ident::new("min_directors"),
        base_ty: Box::new(Term::pi(
            "ctx",
            Term::constant("IncorporationContext"),
            Term::constant("ComplianceVerdict"),
        )),
        base_body: Box::new(Term::lam(
            "ctx",
            Term::constant("IncorporationContext"),
            Term::match_expr(
                Term::app(Term::constant("director_count"), Term::var("ctx", 0)),
                Term::constant("ComplianceVerdict"),
                vec![
                    constructor_branch("Zero", Term::constant("NonCompliant")),
                    wildcard_branch(Term::constant("Compliant")),
                ],
            ),
        )),
        exceptions: Vec::new(),
        lattice: None,
    })
}

fn lex_pipeline_benchmark(c: &mut Criterion) {
    let source = IBC_S66_RULE_BODY_SOURCE;
    let lexed_tokens = lexer::lex(source).expect("benchmark source should lex");
    let token_count = lexed_tokens.len() as u64;
    let prelude_ctx = prelude::compliance_prelude();

    let core_rule = ibc_s66_minimum_directors_rule();
    let indexed_rule = debruijn::assign_indices(&core_rule).expect("rule should index");
    let obligation_count = obligations::extract_obligations(&indexed_rule).len() as u64;

    // The full s.66 rule body uses Match/Defeasible, which the current
    // admissible checker rejects. Benchmark the admissible accessor subterm.
    let accessor_surface = parse_source(IBC_S66_ACCESSOR_SOURCE);
    let accessor_core =
        elaborate::elaborate(&accessor_surface, &prelude_ctx).expect("accessor should elaborate");
    let accessor_type = Term::pi(
        "ctx",
        Term::constant("IncorporationContext"),
        Term::constant("Nat"),
    );

    let mut group = c.benchmark_group("lex_pipeline");

    group.throughput(Throughput::Elements(token_count));
    group.bench_function("lexing", |b| {
        b.iter(|| lexer::lex(black_box(source)).expect("benchmark source should lex"))
    });

    group.throughput(Throughput::Elements(1));
    group.bench_function("parsing", |b| {
        b.iter(|| parser::parse(black_box(&lexed_tokens)).expect("benchmark tokens should parse"))
    });

    group.bench_function("debruijn_index_assignment", |b| {
        b.iter(|| debruijn::assign_indices(black_box(&core_rule)).expect("rule should index"))
    });

    group.bench_function("typechecking_with_prelude", |b| {
        b.iter(|| {
            typecheck::check(
                black_box(&prelude_ctx),
                black_box(&accessor_core),
                black_box(&accessor_type),
            )
            .expect("accessor lambda should typecheck")
        })
    });

    group.throughput(Throughput::Elements(obligation_count));
    group.bench_function("obligation_extraction", |b| {
        b.iter(|| obligations::extract_obligations(black_box(&indexed_rule)))
    });

    group.throughput(Throughput::Elements(1));
    group.bench_function("full_pipeline_source_to_obligations", |b| {
        b.iter(|| {
            let tokens = lexer::lex(black_box(source)).expect("benchmark source should lex");
            let term = parser::parse(black_box(&tokens)).expect("benchmark tokens should parse");
            let elaborated =
                elaborate::elaborate(black_box(&term), black_box(&prelude_ctx))
                    .expect("benchmark term should elaborate");
            obligations::extract_obligations(black_box(&elaborated))
        })
    });

    group.finish();
}

criterion_group!(benches, lex_pipeline_benchmark);
criterion_main!(benches);
