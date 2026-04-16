# CLAUDE.md — Lex

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

## Ecosystem

This repo is one lane in Mass / Momentum / Moxie. Lane: Lex language — typed discretion holes; 567 tests; independent Apache-2.0 repo.

Ecosystem map: `~/centcom/metacognition/ecosystem-map.md` (canonical).

**Cross-repo boundaries:**

Reads: mez-core types from kernel (path dependency).
Writes: Lex language crates; diagnostic emitter; CLI.
Never touches: kernel internals beyond mez-core public surface.

## Purpose

Lex: A Logic for Jurisdictional Rules. Dependently-typed, effect-typed, defeasible logic with temporal stratification, authority-relative interpretation, and typed discretion holes.

**Paper:** "Lex: A Logic for Jurisdictional Rules" — research.momentum.inc

## Repository Structure

```
lex/
├── crates/
│   ├── lex-core/     # The Lex language — 22 modules, 470+ unit tests
│   │   ├── src/
│   │   │   ├── ast.rs           # Core AST types (Term, Sort, Level, Ident, QualIdent)
│   │   │   ├── certificate.rs   # Lex proof certificate issuance
│   │   │   ├── compose.rs       # Fiber composition
│   │   │   ├── debruijn.rs      # De Bruijn index assignment and substitution
│   │   │   ├── decide.rs        # Decision procedures
│   │   │   ├── decision_table.rs # Decision table compilation
│   │   │   ├── effects.rs       # Effect row algebra
│   │   │   ├── elaborate.rs     # Surface → core elaboration
│   │   │   ├── evaluate.rs      # Term evaluation
│   │   │   ├── fuel.rs          # Fuel-typed fibers (bounded evaluation budgets)
│   │   │   ├── levels.rs        # Universe level management
│   │   │   ├── lexer.rs         # Tokenizer
│   │   │   ├── obligations.rs   # Proof obligation tracking
│   │   │   ├── parser.rs        # Parser
│   │   │   ├── prelude.rs       # 363-symbol compliance prelude
│   │   │   ├── pretty.rs        # Pretty-printer
│   │   │   ├── principles.rs    # Principle conflict calculus
│   │   │   ├── smt.rs           # SMT integration
│   │   │   ├── temporal.rs      # Temporal stratification
│   │   │   ├── token.rs         # Token types
│   │   │   ├── tty.rs           # Accessibility text projection (screen readers)
│   │   │   └── typecheck.rs     # Bidirectional type checker
│   │   ├── tests/               # 5 integration test suites
│   │   └── benches/             # Criterion benchmarks
│   ├── lex-diag/     # Structured diagnostic ontology — 41 categories, 20 tests
│   └── lex-cli/      # Air-gapped command-line authoring tool
├── Cargo.toml        # Workspace root
└── CLAUDE.md         # This file
```

## Key Design Properties

1. **Defeasibility** — rules override other rules by priority (lex specialis, lex posterior)
2. **Temporal stratification** — stratum-0 (frozen historical) vs stratum-1 (derived legal)
3. **Authority-relative interpretation** — same rule text, different meaning per tribunal
4. **Typed discretion holes** — `? : T @ Authority` marks where computation stops and human judgment begins
5. **Principle conflict calculus** — acyclic priority DAG on PrincipleId × CaseCategory product graph
6. **Fuel-typed fibers** — bounded evaluation with Indeterminate verdict on exhaustion
7. **Effect typing** — path-indexed effect rows prevent privilege creep

## Dependency on mez-core

Path dependency to `../kernel/mez/crates/mez-core` for foundational types (`ComplianceDomain`, `EntityId`, etc.). When Lex is published as a crate, `mez-core` publishes first.

## Test Suite

567 tests total:
- lex-core unit tests: 470+
- lex-core integration tests: 5 suites (ADGM rules, adversarial attacks, proof pipeline, proptest, Seychelles IBC)
- lex-diag: 20 tests
- Property-based testing via proptest (10 proptest tests verifying type soundness)

## Build

```bash
cargo check --workspace
cargo test --workspace
cargo clippy --workspace -- -D warnings
```

## lex-cli Commands

```bash
lex check <file.lex>           # Type-check a fiber
lex parse <file.lex>           # Parse and pretty-print AST
lex elaborate <file.lex>       # Surface → core elaboration
lex sign <file.lex> --key <k>  # Sign for air-gapped submission
lex verify <file.lex.signed>   # Verify signed fiber
lex check-principles <file>    # Check priority DAG acyclicity
```

## License

Apache-2.0. Lex is a contribution to human knowledge about legal logic — not a proprietary implementation detail. Published as part of the Momentum research programme at research.momentum.inc.

## Git Commit Rules

- **No LLM credit in git commits.** NEVER include `Co-Authored-By` lines referencing Claude, Opus, GPT, Codex, or any LLM in commit messages. The author is the human operator.
