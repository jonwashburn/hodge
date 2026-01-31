# Deep Track: Full Mathematical Formalization

This directory contains the **deep formalization** work required to make the Hodge Conjecture
proof *mathematically complete* (not just kernel-clean via stubs).

## Current State (Proof Track vs Deep Track)

The **proof track** (`hodge_conjecture`) is "kernel-unconditional" — it only depends on
`propext`, `Classical.choice`, `Quot.sound`. However, this is achieved via **stub instances**
that don't do real mathematical work:

| Stub Instance | What It Should Be | Location |
|---------------|-------------------|----------|
| `AutomaticSYRData.universal` | Real microstructure: sheets, gluing, defect→0 | `Hodge/Kahler/Main.lean:210` |
| `ChowGAGAData.universal` | Real Chow/GAGA: analytic→algebraic | `Hodge/Classical/GAGA.lean:141` |
| `SpineBridgeData.universal` | Real spine: fundamental class = representing form | `Hodge/Classical/GAGA.lean:555` |
| `SubmanifoldIntegration.universal` | Real Hausdorff integration | `Hodge/Analytic/Integration/HausdorffMeasure.lean:83` |
| `CubulationExists.universal` | Real cubulation with mesh bounds | `Hodge/Kahler/Microstructure.lean:117` |

Additionally, the **definitions** are too weak:
- `IsAnalyticSet := IsClosed` (should be local holomorphic zero locus)
- `IsAlgebraicSet := IsClosed` (should be polynomial zero locus)
- `poincareDualForm` uses placeholder construction

## Goal

Replace ALL stub instances with real mathematical content so that:
1. Every typeclass field is proved from genuine geometric/analytic facts
2. No `sorry` remains in the deep track
3. The proof is *TeX-faithful* (matches the mathematical literature)

## Module Structure

```
Hodge/Deep/
├── README.md               # This file
├── StatementLock.lean      # Type-check guards that lock statement types
├── Pillars/
│   ├── GAGA.lean           # Deep: analytic sets, Chow theorem, GAGA
│   ├── HarveyLawson.lean   # Deep: calibrated currents → varieties
│   ├── FedererFleming.lean # Deep: flat compactness for integral currents
│   ├── PoincareDuality.lean# Deep: fundamental class, integration current
│   ├── Microstructure.lean # Deep: cubulation, sheets, gluing, defect bounds
│   └── Stokes.lean         # Deep: Stokes theorem for submanifolds
└── Audit.lean              # Build-time audit that fails if stubs remain
```

## Build Targets

```bash
# Build deep track (shows sorry count)
lake build Hodge.Deep

# Verify statement locks
lake build Hodge.Deep.StatementLock

# Full audit (fails if any deep sorry remains - for CI)
lake build Hodge.Deep.Audit
```

## Agent Rules

1. **Never weaken a locked statement** — the types in `StatementLock.lean` are sacred
2. **Never provide trivial instances** — if your proof uses `simp only []` or `rfl` for a deep fact, you're doing it wrong
3. **Replace stubs, don't add parallel versions** — the goal is to fix the `.universal` instances
4. **Document which TeX proposition you're proving** — every deep lemma should cite its TeX source

## Priority Order

1. **Submanifold Integration** — needed by everything else
2. **Microstructure (sheets + gluing)** — the geometric core
3. **Stokes** — needed for calibration defect bounds
4. **Harvey-Lawson** — calibrated → analytic variety
5. **GAGA/Chow** — analytic → algebraic
6. **Poincaré Duality** — fundamental class construction
