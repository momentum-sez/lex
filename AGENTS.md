# AGENTS.md — lex

Lex: A Logic for Jurisdictional Rules. An Apache-2.0 dependently-typed, effect-typed,
defeasible logic with temporal stratification, authority-relative interpretation,
and typed discretion holes — published independently at github.com/momentum-sez/lex
(pending publication). 3 crates, 567 tests.

**Paper:** "Lex: A Logic for Jurisdictional Rules" — research.momentum.inc (paper
#3 in the Momentum research corpus).

This file is the Codex / OpenAI-optimized agent contract. Its factual content
mirrors `CLAUDE.md` in this repository; its format is engineered for Codex 5.x
token economy and failure-mode mitigation. Both files are authoritative; if they
diverge, reconcile by reading the code and updating both.

---

<!-- BEGIN NO-DESTRUCTIVE-GIT (canonical rule — do not remove or edit) -->

## NON-NEGOTIABLE: No destructive git — ever

Applies across every Mass / Momentum / Moxie repo
(moxie, moxie-whitepaper, moxie/web, kernel, kernel worktrees, centcom, stack, lex,
gstore, momentum, momentum-dev, momentum-research, momentum-docs, mass-webapp,
mass-bom, api-gateway, attestation-engine, templating-engine, starters,
organization-info, investment-info, treasury-info, identity-info, consent-info,
governance-info, institutional-world-model-whitepaper,
programmable-institutions-whitepaper, and every other Mass/Momentum/Moxie repo).

**Forbidden commands (non-exhaustive):**

- `git commit` from a subagent (main thread commits only — subagents stage only)
- `git push` in any form, any branch (main thread pushes only)
- `git reset --hard`, `git reset --keep`, or any `git reset` that moves HEAD
- `git checkout` of a shared checkout, `git switch`, `git restore`
- `git stash` in any form (including `pop`, `drop`, `apply`, `clear`)
- `git clean` in any form (`-f`, `-fd`, `-x`, …)
- `git rebase` in any form (including interactive)
- `git branch -D`, `git branch --delete --force`
- `git worktree remove --force`
- `git update-ref`, `git filter-branch`, `git filter-repo`
- `rm -rf` on anything git-tracked

**Required:**

- Agents stage changes only (`git add <path>`). The main thread alone commits and pushes.
- Parallel work uses `git worktree add <unique-path> -b <unique-branch> origin/<base>` and operates inside that isolated path. Never mutate the shared checkout's HEAD.
- Merge conflicts are resolved via merge commits — never via `reset`, `stash`, or `checkout`.
- If a destructive op seems necessary, STOP and escalate to the user. Do not proceed.

**Additive alternatives (always safe):** `git worktree add`, `git revert <commit>`,
`git diff > patch.diff`, `git merge` (no-ff or default), `git fetch`.

This rule survives context compression. Every agent spawned in this repo inherits it.

**Incident reference:** 2026-04-16, Agent 5 (conservation invariants) ran
`git reset --hard --no-recurse-submodules` inside its isolated worktree despite a
"DO NOT commit. Stage only." instruction. The prompt failed to enumerate the
forbidden-command list verbatim. Lesson: the list above must be pasted into every
agent prompt — no paraphrasing, no abbreviation.

<!-- END NO-DESTRUCTIVE-GIT -->

<!-- BEGIN MULTI-AGENT-CONCURRENCY (canonical rule — do not remove or edit) -->

## NON-NEGOTIABLE: Multi-agent concurrency via worktrees

Many local agents run against this repo simultaneously from a single main thread.
They MUST share the repo without destructive interaction. The only safe model:

**Every non-trivial agent operates in its own git worktree:**

```
git worktree add <unique-path> -b <unique-branch> origin/<base-branch>
cd <unique-path>
# ... do work, stage changes ...
# main thread reviews, merges (merge commit only), pushes
```

- `<unique-path>` must be unique per agent (e.g. `/tmp/agent-<id>` or a path that embeds a UUID/task-id). Never reuse paths across agents.
- `<unique-branch>` must be unique per agent (e.g. `agent/<task-id>` or `frontier/<name>-<short-sha>`). Never reuse branch names.
- `<base-branch>` is whatever the user has checked out on main thread (typically `develop` or `main`).

**Rules for concurrent agents:**

1. An agent operates ONLY inside its own worktree path. Never `cd` out of it into the shared checkout. Never read/write files in the shared checkout (that path belongs to the main thread and possibly other agents).
2. An agent never touches HEAD of the shared checkout. No `git checkout`, `git switch`, `git reset`, `git rebase` anywhere.
3. An agent never mutates another agent's worktree or branch.
4. An agent stages changes inside its worktree (`git add`). It does NOT commit. The main thread commits after reviewing the staged changes (agents cannot reliably write good commit messages under a shared history, and commits from parallel agents race on the branch ref).
5. An agent never pushes. Only the main thread pushes.
6. When an agent finishes, its worktree and branch stay until the main thread merges or the user explicitly authorizes cleanup. Do NOT `git worktree remove` your own worktree on exit — the harness cleans up when appropriate.
7. If an agent hits a conflict with another agent's work, it reports the conflict to the main thread and stops. It does NOT resolve the conflict via reset/checkout/stash.
8. If an agent needs to read another repo (cross-repo context), it reads files directly (Read tool) — it does NOT `git checkout` or `git worktree add` in a repo it is not assigned to.

**Read-only agents** (audit, explore, documentation search) may operate in the shared checkout without worktree isolation, because they do not write. They still never run any git command that mutates state.

**File-locking guidance for agents sharing the main checkout (read-only only):**

- Use Read, Grep, Glob freely.
- Do NOT use Edit, Write, or Bash commands that write files in the shared checkout.
- If you find something that needs a write, report it — don't write.

**If any of the above becomes infeasible, STOP and escalate to the user.**
Never silently break the concurrency invariant.

<!-- END MULTI-AGENT-CONCURRENCY -->

---

## License invariant (LOAD-BEARING)

Every file in this repository is Apache-2.0. Every contribution must remain
Apache-2.0. **If a change would introduce proprietary content — code, spec fragments,
partner-specific compliance rules, non-Apache licensed dependencies — STOP and
escalate to the user.**

Lex is a contribution to human knowledge about legal logic — not a proprietary
implementation detail. The whole point of publishing it independently is that
the logic can be cited, audited, and extended by the research community without
being entangled with Mass's commercial deployment.

- **READS allowed:** sibling Apache-2.0 repos `~/stack`, `~/gstore`; any peer-reviewed
  type theory / legal-logic literature.
- **WRITES allowed:** only Apache-2.0 artifacts inside this repo.
- **NEVER:** import proprietary `~/kernel` source; encode a specific jurisdiction's
  live compliance ruleset in-tree (jurisdiction-specific `.lex` files live in the
  proprietary repo that consumes this language); add non-Apache dependencies.

---

## Ecosystem

- `~/lex` — this repo, Apache-2.0 Lex language (3 crates, 567 tests)
- `~/kernel` — proprietary consumer; depends on `mez-core` which lex co-depends on
- `~/stack` — Apache-2.0 zone-operator kit (peer)
- `~/gstore` — Apache-2.0 Merkle-authenticated temporal graph store (peer)
- `~/momentum-research` — paper corpus; paper #3 is this language's spec

Ecosystem map: `~/centcom/metacognition/ecosystem-map.md` (canonical).

---

## Build & verify

```bash
# Compile check across workspace
cargo check --workspace

# All 567 tests
cargo test --workspace

# Zero clippy warnings
cargo clippy --workspace -- -D warnings
```

Run all three after any Rust change.

---

## lex-cli commands

```bash
lex check <file.lex>            # Type-check a fiber
lex parse <file.lex>            # Parse and pretty-print AST
lex elaborate <file.lex>        # Surface to core elaboration
lex sign <file.lex> --key <k>   # Sign for air-gapped submission
lex verify <file.lex.signed>    # Verify signed fiber
lex check-principles <file>     # Check priority DAG acyclicity
```

lex-cli is the air-gapped authoring tool. It has no network dependencies and can
run offline.

---

## Repository structure

```
lex/
├── CLAUDE.md       # Mirrored to this AGENTS.md
├── AGENTS.md       # This file (Codex-optimized)
├── Cargo.toml      # Workspace root (3 members)
└── crates/
    ├── lex-core/   # The Lex language — 22 modules, 470+ unit tests
    │   └── src/
    │       ├── ast.rs             # Term, Sort, Level, Ident, QualIdent
    │       ├── certificate.rs     # Proof certificate issuance
    │       ├── compose.rs         # Fiber composition
    │       ├── debruijn.rs        # De Bruijn index assignment / substitution
    │       ├── decide.rs          # Decision procedures
    │       ├── decision_table.rs  # Decision table compilation
    │       ├── effects.rs         # Effect row algebra
    │       ├── elaborate.rs       # Surface to core elaboration
    │       ├── evaluate.rs        # Term evaluation
    │       ├── fuel.rs            # Fuel-typed fibers (bounded budgets)
    │       ├── levels.rs          # Universe level management
    │       ├── lexer.rs           # Tokenizer
    │       ├── obligations.rs     # Proof obligation tracking
    │       ├── parser.rs          # Parser
    │       ├── prelude.rs         # 363-symbol compliance prelude
    │       ├── pretty.rs          # Pretty-printer
    │       ├── principles.rs      # Principle conflict calculus
    │       ├── smt.rs             # SMT integration
    │       ├── temporal.rs        # Temporal stratification
    │       ├── token.rs           # Token types
    │       ├── tty.rs             # Accessibility (screen-reader) text projection
    │       └── typecheck.rs       # Bidirectional type checker
    ├── lex-diag/   # Structured diagnostic ontology — 41 categories, 20 tests
    └── lex-cli/    # Air-gapped command-line authoring tool
```

---

## Key design properties

| # | Property | Detail |
|---|----------|--------|
| 1 | Defeasibility | Rules override other rules by priority (lex specialis, lex posterior) |
| 2 | Temporal stratification | Stratum-0 (frozen historical time) vs stratum-1 (derived legal time) |
| 3 | Authority-relative interpretation | Same rule text, different meaning per tribunal |
| 4 | Typed discretion holes | `? : T @ Authority` marks where computation stops and human judgment begins |
| 5 | Principle conflict calculus | Acyclic priority DAG on `PrincipleId x CaseCategory` product graph |
| 6 | Fuel-typed fibers | Bounded evaluation with `Indeterminate` verdict on exhaustion |
| 7 | Effect typing | Path-indexed effect rows prevent privilege creep |

---

## Prelude inventory (363 symbols — verified stable)

- 6 core types
- 215 tag constructors
- 96 tag accessors
- 30 bool accessors
- 3 nat accessors
- 2 sanctions accessors
- Remaining: explicit combinators

Tested by `prelude_context_size_is_stable` which asserts `ctx.global_len() == 363`.
If you add prelude symbols, update the test and both CLAUDE.md / AGENTS.md.

---

## Test suite (567 total)

- `lex-core` unit tests: 470+
- `lex-core` integration tests: 5 suites (ADGM rules, adversarial attacks, proof
  pipeline, proptest, Seychelles IBC)
- `lex-diag`: 20 tests
- Property-based testing via proptest (10 proptest tests verifying type
  soundness and effect subsumption)

---

## Dependency on `mez-core`

Lex depends on `mez-core` for foundational types (`ComplianceDomain`, `EntityId`,
etc.). This is currently a path dependency to `../kernel/mez/crates/mez-core`.
When Lex is published as a crate, `mez-core` will be published first.

---

## Hard rules

- **No LLM credit in git commits.** NEVER include `Co-Authored-By` lines
  referencing Claude, Opus, GPT, Codex, or any LLM in commit messages. The
  author is the human operator.
- **No destructive git** — see sentinel block above.
- **License invariant** — Apache-2.0 only, no exceptions.
- **No proprietary imports** — type-theoretic code only. Jurisdiction-specific
  `.lex` files live in consumer repos.
- **Deployment model** — `develop` is dev staging, `main` is prod staging.
  Never push `main` / `master`. Agents push nothing; only the main thread pushes.

---

## Common tasks

| Task | Protocol |
|------|----------|
| New `lex-core` module | (1) Add module to `lex-core/src/lib.rs`. (2) Add unit tests in same file. (3) If it introduces a diagnostic, add category in `lex-diag`. (4) `cargo test --workspace` + `cargo clippy --workspace -- -D warnings`. |
| New prelude symbol | (1) Add in `prelude.rs`. (2) Update the `ctx.global_len()` assertion if it fires. (3) Update the 363-symbol inventory in both `CLAUDE.md` and `AGENTS.md`. |
| New diagnostic category | (1) Add variant in `lex-diag` (currently 41 categories). (2) Add controlled-English rendering. (3) Add coverage test. |
| New CLI command | (1) Add in `lex-cli`. (2) Command must have no network dependencies (air-gapped invariant). (3) Add CLI integration test. |
| Publishing | `~/lex` is ready for publication at `github.com/momentum-sez/lex`. Publication event requires: `mez-core` published first (dependency), final CLAUDE.md/AGENTS.md review, CI green across all three crates. |

---

## Codex cognitive calibration

- Lex is **type-theoretic research code**. Concrete algorithms matter; generic
  abstraction does not. Prefer bidirectional typing, explicit de Bruijn, and
  structural pattern matching over traits.
- **Do not copy a typing rule without reading its adjacent tests.** Test files
  encode expected behavior more precisely than prose comments.
- **Defeasibility and temporal stratification are cross-cutting.** If you touch
  elaboration or decision procedures, re-read `temporal.rs` and `principles.rs`
  before editing.
- Never generate Co-Authored-By lines for LLMs in commit messages.
- When in doubt between "mirror proprietary kernel behavior" vs "keep Lex
  standalone", the standalone path wins. Lex must be publishable independently.
