# Build Performance Baseline (Round 6)

This is a lightweight, environment-dependent baseline for build performance.

## Notes

- Always use Mathlib’s cache before building:

```bash
cd /Users/jonathanwashburn/Projects/hodge
lake exe cache get
```

## Suggested timing commands

Run one of:

```bash
cd /Users/jonathanwashburn/Projects/hodge
/usr/bin/time -p lake build Hodge.Tests.MasterTests
```

```bash
cd /Users/jonathanwashburn/Projects/hodge
/usr/bin/time -p lake build
```

## Observations

- `Hodge.Tests.MasterTests` is intended as a “single entry point” to compile all test files.
- If a particular module is slow, use `lake build <ModuleName>` to isolate it.

