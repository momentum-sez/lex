# Lex Language Reference

This document is the canonical public reference for Lex. It describes the
surface syntax, the executable admissible fragment, the frontier discretion-hole
boundary, the small-step operational model used by the checker, and the parse
through compose pipeline.

## 1. Language At A Glance

Lex is a typed rule language with:

- dependent core terms and sorts
- explicit effect rows
- defeasible rules and exceptions
- temporal terms
- authority-relative forms
- frontier syntax for typed discretion holes

The parser accepts a wider surface than the executable admissible checker. The
main checker accepts the admissible fragment described in section 4. Typed
discretion holes are modeled in the frontier core calculus and formal
scaffolds, not in the shipped admissible checker.

## 2. Execution Boundary

| Stage | Entry point | Hole syntax | Notes |
| --- | --- | --- | --- |
| Lexing | `lexer::lex` | Accepted | Produces `Token::Question` and `Token::Fill` |
| Parsing | `parser::parse` | Accepted | Builds `Term::Hole` and `Term::HoleFill` |
| Elaboration | `elaborate::elaborate` | Preserved | Resolves names and assigns De Bruijn indices |
| Temporal check | `temporal::check_temporal_stratification` | Traversed | Checks nested terms only |
| Strict checker | `typecheck::{infer, check}` | Rejected | `Hole` and `HoleFill` are outside the executable admissible fragment |
| Residualized checker | `typecheck::check_admissibility_mode(_, HoleExtension)` | Accepted with residuals | Emits `R-HOLE`, `R-HOLEFILL`, modal, temporal, and unlock residuals |
| Frontier core calculus | `core_calculus::*` | Supported | Typed hole model, certificates, summaries |
| Fiber composition | `compose::evaluate_all_fibers` | Not wired | Current implementation is a `Pending` stub |
| Lex-to-Op compile | Not shipped in this repository | Boundary only | Companion Op compiler covers its own admitted skeleton |

The public claim set for this repository is:

- The parser and elaborator preserve discretion-hole syntax.
- The frontier core calculus provides the typed model for holes, fills,
  summaries, and certificates.
- The strict admissible checker rejects `Hole` and `HoleFill`.
- The residualized public checker admits them only with explicit residuals.
- `compose::evaluate_all_fibers` is not the production semantics of the
  frontier core calculus.
- Lex states the source-side compile contract for Op, but this repository does
  not currently expose a production compiler entry point.

## 3. Lexical Conventions

Identifiers are ASCII letter, digit, underscore, and dot sequences. Qualified
identifiers use dot-separated segments such as `regulator.fsra` or
`compliance.Pending`.

The lexer recognizes:

- keywords such as `lambda`, `let`, `match`, `defeasible`, `fill`, `balance`
- sort keywords such as `Type`, `Prop`, `Rule`, `Time0`, and `Time1`
- punctuation such as `(`, `)`, `[`, `]`, `{`, `}`, `:`, `:=`, `=>`, `->`,
  `@`, `,`, `.`, and `*`
- integer, rational, and string literals
- content references of the form `lex://blake3:<hash>`

Comments use line comments `-- ...` and block comments `{- ... -}`.

## 4. Concrete Syntax

The parser accepts the following surface grammar.

```text
term        ::= arrow
arrow       ::= product
              | product "->" arrow
product     ::= application
              | product "*" application
application ::= atom
              | application atom
atom        ::= ident
              | qualident
              | sort
              | "(" term ")"
              | "lambda" ident ":" term "=>" term
              | "Pi" ident ":" term effect_ann "->" term
              | "Sigma" ident ":" term "*" term
              | "let" ident ":" term ":=" term "in" term
              | "match" atom "return" atom "with" branch+ "end"
              | "fix" ident ":" term ":=" term
              | "defeasible" ident ":" term "with" exception* "end"
              | "?" hole_name ":" term "@" authority scope_opt
              | "fill(" hole_name "," term "," term ")"
              | "coerce" "[" tribunal "=>" tribunal "]" "(" term "," term ")"
              | "coerce" "[" tribunal "=>" tribunal "]" term "with" "witness" atom
              | "axiom" qualident
              | "balance" "{" balance_fields "}"
              | "unlock" term "in" term
              | "asof0(" term "," time_term ")"
              | "asof1(" term "," time_term "," term ")"
              | "lift0(" term ")"
              | "derive1(" term "," term ")"
              | "pi_1" atom
              | "pi_2" atom
              | "<" term "," term ">"
              | literal
              | content_ref

sort        ::= "Type" "_" level
              | "Prop"
              | "Rule" "_" level
              | "Time0"
              | "Time1"

effect_ann  ::= ""
              | "[" effect_row "]"

effect_row  ::= effect
              | effect "," effect_row

effect      ::= "read"
              | "write(" term ")"
              | "attest(" authority ")"
              | "authority(" authority ")"
              | "oracle(" oracle_ref ")"
              | "fuel(" level "," nat ")"
              | "sanctions_query"
              | "discretion(" authority ")"

branch      ::= "|" pattern "=>" term
pattern     ::= "_"
              | constructor ident*

exception   ::= "unless" atom "=>" term priority_opt authority_opt
priority_opt ::= ""
              | "priority" nat
authority_opt ::= ""
               | "authority" authority

hole_name   ::= ident
              | "_"

scope_opt   ::= ""
              | "scope" scope_constraint

scope_constraint ::= "{" scope_field ("," scope_field)* "}"
scope_field ::= "corridor" ":" qualident
              | "jurisdiction" ":" qualident
              | "entity" ":" qualident
              | "from" ":" time_term
              | "to" ":" time_term
              | "tag" ":" qualident
```

Notes:

- The parser accepts surface hole forms and fill forms.
- The strict checker does not admit them.
- `HoleExtension` admission admits them only with structured residuals, not as
  fully discharged mechanical proof.
- The frontier core calculus models the typed hole and typed fill semantics.

## 5. Types And Sorts

Lex uses terms as types. The important sort forms are:

- `Type_l` - ordinary type universe at level `l`
- `Prop` - proof-irrelevant propositions
- `Rule_l` - rule universe at level `l`
- `Time0` - frozen time terms
- `Time1` - derived time terms

The executable checker supports:

- variables
- pure `Pi` types
- lambda terms in checking mode
- application
- annotation
- `let`
- named constants from the compliance prelude
- `Defeasible` rules
- `match` over prelude constructors

The strict executable checker rejects:

- `Rec`
- `Sigma`, pairs, and projections
- unresolved level variables
- effectful `Pi` rows other than the empty row
- modal terms
- `Hole` and `HoleFill`
- literals
- unresolved content references

The public residualized mode
`typecheck::check_admissibility_mode(_, HoleExtension)` accepts the same
executable fragment plus typed holes, hole fills, modals, temporal coercions,
defeat elimination, unlocks, sanctions dominance, and principle balancing
only by emitting residuals. A residualized acceptance is admissible evidence,
not proof discharge.

The compliance prelude provides the public checker with core tags such as
`ComplianceVerdict`, `ComplianceTag`, `Bool`, `Nat`, and `SanctionsResult`
along with the constructor vocabulary used in the rule suites.

## 6. Discretion Holes

### 6.1 Surface syntax

An unfilled discretion hole has the form:

```text
? hole_name : ExpectedType @ authority [scope ...]
```

A filled discretion hole has the form:

```text
fill(hole_name, filler_term, witness_term)
```

### 6.2 Shipped boundary

The repository ships three distinct layers for discretion holes:

1. The surface AST, parser, pretty-printer, elaborator, De Bruijn pass,
   temporal check, and obligation extractor preserve hole syntax.
2. The strict admissible checker rejects `Hole` with
   `AdmissibilityViolation::UnfilledHole` and rejects `HoleFill` with
   `AdmissibilityViolation::HoleFillNotSupported`.
3. The public residualized checker admits `Hole` / `HoleFill` with
   `R-HOLE` / `R-HOLEFILL` residuals for proof-envelope transport.
4. The frontier core calculus in `crates/lex-core/src/core_calculus/hole.rs`
   carries the typed hole model, authorized fills, discretion frontiers, and
   certificate records.

### 6.3 Frontier semantics

The frontier core calculus treats a hole as a typed request for judgment from a
named authority under a scope constraint. A fill couples:

- the hole identifier
- a filler of the requested type
- a PCAuth witness for the authorized party
- a four-tuple recording time, jurisdiction, text snapshot, and tribunal

The frontier summary and certificate layers preserve the discretion frontier and
differentiate mechanical derivation from human judgment.

### 6.4 Main-checker future work

Making holes load-bearing in the main checker requires:

- an executable hole environment that ties `fill(h, e, witness)` back to the
  declared hole type and authority
- a surface representation of the PCAuth witness with a checker-visible type
- a checker rule that validates filled holes instead of rejecting them at the
  admissibility boundary

Those pieces do not ship as fully discharged mechanical proof today; until
they do, `HoleExtension` residuals must remain visible in admission envelopes.

## 7. Small-Step Operational Semantics

The executable checker uses fuel-bounded weak-head reduction for definitional
equality. The administrative Coq kernel closes this shape as
`administrative_whnf_bounded_reduction`,
`administrative_whnf_sufficient_fuel`, and
`administrative_whnf_canonical_bound_reduction`; the full admissible-calculus
WHNF theorem remains part of the paper-level metatheory frontier. The core
reduction rules are:

```text
(beta)  ((lambda x : A => b) a)          -> b[a/x]
(zeta)  (let x : A := v in b)            -> b[v/x]
(annot) (t : A)                          -> t
(app1)  t1 -> t1'                        => t1 t2 -> t1' t2
(app2)  f value, t2 -> t2'               => f t2 -> f t2'
(let1)  t1 -> t1'                        => let x : A := t1 in b -> let x : A := t1' in b
```

The shipped checker uses these reductions inside type equality, not as a full
evaluator for the entire surface language.

For discretion holes:

- `? h : T @ A` is preserved by the surface pipeline but rejected by the
  executable admissibility checker before evaluation.
- `fill(h, e, w)` is preserved by the surface pipeline but rejected by the
  executable admissibility checker before evaluation.
- The frontier core calculus defines the typed hole and fill behavior.

## 8. Pipeline

The repository exposes the following pipeline:

```text
source
  -> lexer::lex
  -> parser::parse
  -> elaborate::elaborate
  -> temporal::check_temporal_stratification
  -> typecheck::{infer, check}
  -> obligations::extract_obligations
  -> certificate / compose
```

### `elaborate`

`elaborate::elaborate` resolves names against the compliance prelude and assigns
De Bruijn indices. Hole syntax survives elaboration unchanged except for name
resolution inside the type, scope, filler, and witness subterms.

### `check`

`typecheck::infer` and `typecheck::check` implement the executable admissible
fragment. They reject any term outside that fragment at the admissibility
boundary.

### `compose`

`compose::compose_results` merges fiber verdicts per compliance domain.
`compose::evaluate_all_fibers` is currently a structural stub that emits
`Pending` results. It is not the production semantics of the frontier core
calculus.

### Runtime caveat primitive

`predicate_runtime` is the public first-order caveat fragment. A
`LexProposition` is a closed proposition over named request attributes;
`EvalContext` binds those attributes to `LexValue` values; `evaluate` returns a
boolean decision or a structural error.

`predicate_narrowing::caveats_narrow(parent, child)` checks attenuation. It
accepts a child caveat set only when every context satisfying the child also
satisfies the parent. Dedicated structural rules cover monetary, temporal,
rate, operation, domain, resource, counterparty, subject, MCP, jurisdiction,
and discretion caveats; custom caveats fall back to finite-context
propositional enumeration.

### Lex-to-Op boundary

Lex authorization of an Op payload requires an admission envelope, not merely a
successful source parse. The envelope must bind:

- the elaborated Lex source digest, rule-pack digest, and certificate or
  proof-summary digest;
- the compiled Op payload digest;
- the typed input-context and payload-schema digests;
- the four-tuple authority, compiler digest, Op primitive-registry digest, and
  gas-schedule digest;
- the effect row and subject-indexed capability row;
- PCAuth-filled hole entries, when any frontier hole-fill lowering is admitted;
- failed, deferred, receipt-required, and host-required predicate lists.

Admission fails closed when any bound digest differs, the Op payload does not
typecheck, a primitive is absent from the bound registry, a capability or
freshness premise is missing, a required receipt is not accepted, a filled hole
does not verify against its exact payload, or a failed/deferred predicate
remains.

The public companion Op compiler covers its own finite admitted skeleton:
constants, prelude-scoped variables and calls, pattern matches with a
materialized fail-closed fallback, defeasible priority lowering, sanctions
dominance lowering, and filled-hole attestation append lowering. That coverage
is not a claim that every `lex-core::ast::Term` compiles to Op. The Lex-side
frontier is to align the executable admissible checker, certificate builder,
and formal envelope so the compiler domain is a checked source property.

## 9. Examples

### 9.1 Executable admissible fragment

```lex
lambda ctx : IncorporationContext => Pending
```

Expected outcome:

- parse: success
- elaborate: success
- check against `Pi ctx : IncorporationContext -> ComplianceVerdict`: success

### 9.2 Surface discretion hole

```lex
? fit_and_proper : Prop @ regulator scope { jurisdiction : ADGM }
```

Expected outcome:

- parse: success
- elaborate: success
- main checker: `admissibility violation: unfilled discretion hole`
- frontier core calculus: use `core_calculus::hole` to model the typed hole

### 9.3 Surface fill form

```lex
fill(fit_and_proper, Pending, True)
```

Expected outcome:

- parse: success
- elaborate: success
- main checker: `admissibility violation: hole filling not yet supported`

## 10. Formal Relation

The frontier design note and formal scaffolds track the same typed-hole story:

- `docs/frontier-work/08-lex-core-calculus.md`
- `formal/coq/LexCore.v`
- `formal/lean/LexCore.lean`
- `formal/coq/Lex/AdmissionEnvelope.v`
- `formal/coq/Lex/PCAuthQuorum.v`

Those artifacts describe the typed discretion-hole model that the executable
admissible checker has not yet integrated, and the structural payload-binding
conditions needed before a compiled Op payload can be treated as Lex-authorized.
