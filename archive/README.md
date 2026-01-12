# Archived Off-Track Code

This directory contains Lean files that are **NOT on the proof track** for `hodge_conjecture'`.

## Why These Were Archived

These files contain axioms and infrastructure that:
1. Were developed for alternative proof approaches
2. Are not imported by `Hodge/Kahler/Main.lean`
3. Do not contribute to `#print axioms hodge_conjecture'`

## Archived Files

### Classical/ (21 axioms total)
- `KahlerIdentities.lean` - Kähler identities [Λ,d], [L,δ], etc. (9 axioms)
- `PrimitiveDecomposition.lean` - Lefschetz decomposition (9 axioms)
- `HardLefschetz.lean` - Hard Lefschetz from sl₂ (3 axioms)

### Cohomology/
- `HodgeDecomposition.lean` - Dolbeault decomposition (9 axioms)
- `ModelDeRham.lean` - Model space de Rham

### CategoryTheory/
- `Filtration/` - Filtered derived categories (not used)

### Other
- `All.lean`, `Classical.lean`, `OffTrack.lean` - Umbrella files
- `Test/` - Test files
- `Utils/` - Audit scripts (except DependencyCheck.lean)

## Restoration

To restore a file:
```bash
mv archive/Hodge/Classical/KahlerIdentities.lean Hodge/Classical/
```

Then update the relevant import statements.

## Current Proof Track Status

After archiving, the proof track has:
- **2 custom axioms** to prove
- **1 sorryAx** to fix (from sorry statements)
- **3 standard Lean axioms** (always present)

Run `./scripts/verify_proof_track.sh` to check current status.
