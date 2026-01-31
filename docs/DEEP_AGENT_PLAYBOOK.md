# Deep-theorem scaffolding: how we run agents without “making the work disappear”

## Goal

Turn the remaining **deep mathematical inputs** (GAGA/Chow, spine bridge, SYR defect estimates, Stokes/integration, etc.)
into **concrete Lean targets** that:

- compile (so agents can iterate safely),
- contain explicit obligations (`sorry`/axioms) in well-named theorems, and
- can’t be “completed” by weakening statements or swapping in trivial instances unnoticed.

## The core mechanism

### 1) Deep track build target

We added an import hub:

- `Hodge/Deep.lean` (`Hodge.Deep`)

Build it explicitly:

```bash
lake exe cache get
lake build Hodge.Deep
```

This keeps deep work **off the proof track**, while still making it easy to run a fleet against a single target.

### 2) Statement lock (anti-stub guard rail)

We added:

- `Hodge/Deep/StatementLock.lean` (`Hodge.Deep.StatementLock`)

It contains type-ascriptions (`#check … : …`) that **lock the statements** of deep targets.
If an agent tries to “solve” a target by weakening/changing its type, the lock file will fail to compile.

Build it explicitly:

```bash
lake exe cache get
lake build Hodge.Deep.StatementLock
```

**Rule for agents**: do not edit `Hodge/Deep/StatementLock.lean` unless we are intentionally revising the spec.

## What went wrong previously (and how this prevents it)

### Failure mode A: “Solved” by changing the spec

Example: replace a hard statement with a weaker one, or redefine a target so it becomes `rfl`.

**Protection**: statement lock file fails if the target type changes.

### Failure mode B: “Solved” by swapping in a trivial instance

Example: discharge a deep interface via a stub `universal` instance (zero integral, zero current, `Set.univ` support).

**Protection (partial)**:
- we keep deep-track obligations as explicit `sorry` theorems (not only typeclass fields),
- and we build `Hodge.Deep`/`Hodge.Deep.StatementLock` in CI/agent runs so the obligations remain visible.

**Note**: truly preventing trivial-instance “solutions” requires tightening specs (i.e. strengthening the statements so trivial
models can’t satisfy them). That is an ongoing part of Stage 2–6 work.

## Current deep-track targets (high-signal)

See `docs/DEEP_TASK_INDEX.md` for the curated list (files + theorem names).

