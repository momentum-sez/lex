# F164 Lex Coq Closure Pass

## Scope actually present in this worktree

The task brief referenced a split Coq tree under `formal/coq/Lex/`
(`Syntax.v`, `DeBruijn.v`, `Typing.v`, `Admissibility.v`) with 14
`Admitted.` sites and a confluence spine rooted at `Typing.v:470`.

That tree is not present on any branch available in the local `~/lex` clone.
The only remote branches visible here are:

- `origin/master`
- `origin/frontier/core-calculus`
- `origin/claudemd/compress-lex-w1e`

`origin/master` has no `formal/coq/` formalization at all. The only branch
with Coq content is `origin/frontier/core-calculus`, and its formalization is
a single file: `formal/coq/LexCore.v`.

The brief also referenced
`origin/agent/f136-lex-equivalence:docs/architecture/frontier-work/F136-LEX-SEMANTIC-EQUIVALENCE.md`,
but that ref is not present in the local repository, so it could not be read.

## Admitted count

- Before this pass: `2`
- After this pass: `0`

Unchanged residual assumption:

- `Axiom oracle_terminates` in `formal/coq/LexCore.v`

## Theorem classification and outcomes

### Actual `Admitted` sites on `origin/frontier/core-calculus`

1. `principle_balancing_terminates`
   - Classification: moderate
   - Reason: the theorem only asks for an existential boolean decision
     witness, so classical excluded middle is sufficient even without
     implementing Tarjan's algorithm.
   - Outcome: closed
   - Closure: proved by case analysis on
     `excluded_middle_informative (acyclic g)`.

2. `mechanical_bit_correct`
   - Classification: hard as originally stated
   - Reason: the theorem was false for the original record shape. A
     `DerivationCertificate` could carry `dc_mechanical_check = true` and a
     non-empty discretion frontier because no invariant tied those fields
     together.
   - Outcome: closed after specification repair
   - Closure: refined `DerivationCertificate` with
     `dc_mechanical_sound :
       dc_mechanical_check = true -> dc_discretion_frontier = []`,
     then proved the theorem by projection.

## Confluence scaffold state

Not applicable on this branch.

There is no `Typing.v`, no `confluence` theorem, and no reduction relation in
the checked-out Coq development. Because the branch does not contain the
30-constructor AST or the split typing/de Bruijn files described in the brief,
there is nothing concrete here to scaffold for Takahashi-style parallel
reduction.

If the intended target is the 14-row ledger branch, the next step is not a
Coq proof but branch recovery:

1. Obtain the Lex branch that actually contains `formal/coq/Lex/`.
2. Re-run the closure pass there.
3. Then evaluate parallel reduction versus an alternative confluence proof on
   the real AST and step relation.

## Verification

Verified locally in this worktree:

- `coqc formal/coq/LexCore.v`
- `rg -n '\bAdmitted\.' formal/coq` returns no matches

## Files changed

- `formal/coq/LexCore.v`
- `formal/README.md`
- `docs/architecture/frontier-work/F164-LEX-COQ-CLOSURES.md`

## Worktree details

The requested `git worktree add` flow could not be used from this sandbox
because it requires writes into `~/lex/.git`, which is outside the writable
roots. To preserve isolation, this pass used a clone at:

- Path: `/tmp/agent-f164-lex-coq`
- Branch: `agent/f164-lex-coq-closures`
