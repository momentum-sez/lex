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

## What Lex is

Lex is a dependently-typed, effect-typed, defeasible logic for jurisdictional
rules. It supports temporal stratification, authority-relative interpretation,
and typed discretion holes. The headline primitive is the hole: `? : T @ A`
marks the frontier between mechanical derivation and human judgment, and is
part of the calculus rather than an afterthought.

This repo is Apache-2.0 and public at `github.com/momentum-sez/lex`. The
canonical paper lives at research.momentum.inc as part of the Momentum
research programme.

## Repository structure

```
lex/
├── crates/
│   ├── lex-core/           # Parser, type checker, evaluator, obligations, core calculus
│   │   ├── src/
│   │   │   ├── ast.rs             # Core AST (Term, Sort, Level, Ident, QualIdent)
│   │   │   ├── certificate.rs     # Lex proof certificate issuance
│   │   │   ├── compose.rs         # Fiber composition
│   │   │   ├── core_calculus/     # Narrow API for the nine design commitments
│   │   │   ├── debruijn.rs        # De Bruijn index assignment and substitution
│   │   │   ├── decide.rs          # Decision procedures
│   │   │   ├── decision_table.rs  # Decision table compilation
│   │   │   ├── effects.rs         # Effect row algebra
│   │   │   ├── elaborate.rs       # Surface → core elaboration
│   │   │   ├── elaboration_cert.rs # Elaboration certificate
│   │   │   ├── evaluate.rs        # Term evaluation
│   │   │   ├── fuel.rs            # Fuel-typed fibers (bounded evaluation budgets)
│   │   │   ├── level_check.rs     # Universe level well-formedness check
│   │   │   ├── levels.rs          # Universe level management
│   │   │   ├── lexer.rs           # Tokenizer
│   │   │   ├── obligations.rs     # Proof obligation tracking
│   │   │   ├── open_world.rs      # Open-world closure with oracle
│   │   │   ├── oracle_termination.rs # Witness-supply oracle boundedness
│   │   │   ├── parser.rs          # Parser
│   │   │   ├── prelude.rs         # Compliance prelude symbols
│   │   │   ├── pretty.rs          # Pretty-printer
│   │   │   ├── principles.rs      # Principle conflict calculus
│   │   │   ├── smt.rs             # SMT integration
│   │   │   ├── temporal.rs        # Temporal stratification
│   │   │   ├── token.rs           # Token types
│   │   │   ├── tty.rs             # Accessibility text projection (screen readers)
│   │   │   └── typecheck.rs       # Bidirectional type checker
│   │   ├── tests/                 # Integration test suites (ADGM, Seychelles IBC,
│   │   │                          #   adversarial attacks, proof pipeline, proptest)
│   │   └── benches/               # Criterion benchmarks
│   ├── lex-diag/           # Structured diagnostic ontology, controlled-English messages
│   └── lex-cli/            # Air-gapped command-line authoring tool
├── formal/
│   ├── coq/                # Coq mechanisation of the nine design commitments
│   ├── lean/               # Lean 4 mirror
│   └── README.md           # Admitted theorems with declared proof strategies
├── docs/
│   └── frontier-work/      # Design notes for in-progress calculus extensions
├── Cargo.toml              # Workspace root
├── CLAUDE.md               # This file
├── README.md               # Public entry point for external contributors
└── LICENSE                 # Apache-2.0
```

## Key design properties

1. **Defeasibility** — rules override other rules by priority (lex specialis, lex posterior).
2. **Temporal stratification** — stratum-0 (frozen historical) vs stratum-1 (derived legal); lift is total, demotion is not expressible.
3. **Authority-relative interpretation** — same rule text, different meaning per tribunal; composition requires matching `(Time, Jurisdiction, Version, Tribunal)` or an explicit `TribunalCoercion`.
4. **Typed discretion holes** — `? : T @ Authority` marks where computation stops and human judgment begins; filled only by a `HoleFill` whose signer matches the hole's authority.
5. **Principle conflict calculus** — acyclic priority DAG on `PrincipleId × CaseCategory`; cycles detected at load time.
6. **Fuel-typed fibers** — bounded evaluation; `Indeterminate` on fuel exhaustion is a proper verdict, not a timeout exception.
7. **Effect typing** — path-indexed effect rows prevent privilege creep under composition.

## Dependency on mez-core

Lex uses `mez-core` for foundational identifier and domain types
(`EntityId`, `ComplianceDomain`). The workspace declares `mez-core` as a
path dependency at `../kernel/mez/crates/mez-core` for in-tree development.
When Lex ships as a crate, `mez-core` is published first and the path
dependency is replaced by a version dependency.

The calculus itself — parser, type checker, evaluator, obligations, proof
pipeline — is defined entirely in this repository. `mez-core` supplies only
shared types, not logic.

## Test suite

Run `cargo test --workspace` to execute all tests. Layers:

- `lex-core` unit tests — inline per-module.
- `lex-core` integration suites under `crates/lex-core/tests/` — ADGM rules,
  Seychelles IBC rules, proof-pipeline end-to-end, adversarial attacks,
  proptest type soundness.
- `lex-diag` unit tests.
- Criterion benchmarks under `crates/lex-core/benches/` (run with
  `cargo bench`).

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

Apache-2.0. See `LICENSE`. Lex is a contribution to the public record on
legal logic, not a proprietary implementation detail. Published as part of
the Momentum research programme at research.momentum.inc.

## Git commit rules

- **No LLM credit in git commits.** NEVER include `Co-Authored-By` lines
  referencing Claude, Opus, GPT, Codex, or any LLM in commit messages. The
  author is the human operator.

