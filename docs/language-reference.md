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
| Main type checker | `typecheck::{infer, check}` | Rejected | `Hole` and `HoleFill` are outside the executable admissible fragment |
| Frontier core calculus | `core_calculus::*` | Supported | Typed hole model, certificates, summaries |
| Fiber composition | `compose::evaluate_all_fibers` | Not wired | Current implementation is a `Pending` stub |

The public claim set for this repository is:

- The parser and elaborator preserve discretion-hole syntax.
- The frontier core calculus provides the typed model for holes, fills,
  summaries, and certificates.
- The main admissible checker rejects `Hole` and `HoleFill`.
- `compose::evaluate_all_fibers` is not the production semantics of the
  frontier core calculus.

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
              | "coerce" tribunal "->" tribunal term "with" term
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
- The main checker does not admit them.
- The frontier core calculus models the typed hole and typed fill semantics.

## 5. Types And Sorts

Lex uses terms as types. The important sort forms are:

- `Type_l` — ordinary type universe at level `l`
- `Prop` — proof-irrelevant propositions
- `Rule_l` — rule universe at level `l`
- `Time0` — frozen time terms
- `Time1` — derived time terms

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

The executable checker rejects:

- `Rec`
- `Sigma`, pairs, and projections
- unresolved level variables
- effectful `Pi` rows other than the empty row
- modal terms
- `Hole` and `HoleFill`
- literals
- unresolved content references

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
2. The main admissible checker rejects `Hole` with
   `AdmissibilityViolation::UnfilledHole` and rejects `HoleFill` with
   `AdmissibilityViolation::HoleFillNotSupported`.
3. The frontier core calculus in `crates/lex-core/src/core_calculus/hole.rs`
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

Those pieces do not ship in the admissible checker today.

## 7. Small-Step Operational Semantics

The executable checker uses weak-head reduction for definitional equality. The
core reduction rules are:

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

Those artifacts describe the typed discretion-hole model that the executable
admissible checker has not yet integrated.
