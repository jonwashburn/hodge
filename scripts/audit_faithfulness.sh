#!/usr/bin/env bash
set -euo pipefail

# Audit script for “Clay-standard” blockers:
# - project-level axioms
# - opaque constants
# - sorrys (outside the explicitly quarantined Advanced sandbox)
# - known semantic stubs (e.g. extDerivLinearMap := 0)
#
# Usage:
#   scripts/audit_faithfulness.sh            # report only (exit 0)
#   scripts/audit_faithfulness.sh --strict   # fail if any blockers are found

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
STRICT=0
if [[ "${1:-}" == "--strict" ]]; then
  STRICT=1
fi

cd "$ROOT"

say() { printf "%s\n" "$*"; }

fail_count=0

report_grep() {
  local title="$1"
  local pattern="$2"
  local path="$3"
  shift 3

  say ""
  say "### ${title}"
  # shellcheck disable=SC2086
  local out
  out="$(grep -RIn --include="*.lean" "$@" -E "${pattern}" "${path}" 2>/dev/null || true)"
  if [[ -z "${out}" ]]; then
    say "(none)"
    return 0
  fi
  say "${out}"
  fail_count=$((fail_count + 1))
  return 0
}

say "## Hodge faithfulness audit"
say "- repo: ${ROOT}"
say "- mode: $([[ $STRICT -eq 1 ]] && echo strict || echo report)"

# 1) Project axioms (Clay blocker if reachable from Main)
report_grep "Project axioms (Lean axiom declarations)" '^axiom\b' "Hodge" \
  --exclude-dir="Analytic/Advanced"

# 2) Opaques (hidden assumptions; not reported by #print axioms)
report_grep "Opaque constants (opaque declarations)" '^opaque\b' "Hodge"

# 3) Sorries (outside Advanced sandbox)
report_grep "Sorries outside Hodge/Analytic/Advanced/" '^[[:space:]]*sorry([[:space:]]|$)' "Hodge" \
  --exclude-dir="Advanced"

# 3b) Sorries inside Advanced sandbox (tracked, but currently quarantined)
report_grep "Sorries inside Hodge/Analytic/Advanced/ (quarantined)" '^[[:space:]]*sorry([[:space:]]|$)' "Hodge/Analytic/Advanced"

# 4) Known semantic stubs: exterior derivative placeholder (show defining snippet)
say ""
say "### Exterior derivative stub (showing extDerivLinearMap definition snippet)"
ext_snip="$(grep -n -A 10 -B 0 "def extDerivLinearMap" Hodge/Analytic/Forms.lean 2>/dev/null || true)"
if [[ -z "${ext_snip}" ]]; then
  say "(definition not found)"
else
  say "${ext_snip}"
  # Heuristic: the current stub ends with a line like `NNN:  0` (the body is the zero map).
  if echo "${ext_snip}" | grep -qE ':[[:space:]]*0[[:space:]]*$|:=[[:space:]]*0[[:space:]]*$'; then
    fail_count=$((fail_count + 1))
  fi
fi

# 4b) FundamentalClassSet stub (cycle class placeholder)
say ""
say "### FundamentalClassSet stub (showing FundamentalClassSet_impl snippet)"
fc_snip="$(grep -n -A 12 -B 2 "def FundamentalClassSet_impl" Hodge/Classical/GAGA.lean 2>/dev/null || true)"
if [[ -z "${fc_snip}" ]]; then
  say "(definition not found)"
else
  say "${fc_snip}"
  if echo "${fc_snip}" | grep -qE '=>[[:space:]]*0[[:space:]]*$'; then
    fail_count=$((fail_count + 1))
  fi
fi

# 4b2) integration_current stub (current integration placeholder)
say ""
say "### integration_current stub (showing integration_current definition snippet)"
ic_snip="$(grep -n -A 8 -B 1 "def integration_current" Hodge/Analytic/Currents.lean 2>/dev/null || true)"
if [[ -z "${ic_snip}" ]]; then
  say "(definition not found)"
else
  say "${ic_snip}"
  if echo "${ic_snip}" | grep -qE ':[[:space:]]*=[[:space:]]*0[[:space:]]*$|:[[:space:]]*:= *0[[:space:]]*$|^[0-9]+:[[:space:]]*0[[:space:]]*$'; then
    fail_count=$((fail_count + 1))
  fi
fi

# 4b3) isRationalClass stub (constructor base case is `zero` only)
say ""
say "### isRationalClass stub (showing inductive definition snippet)"
rat_snip="$(grep -n -A 20 -B 2 "inductive isRationalClass" Hodge/Cohomology/Basic.lean 2>/dev/null || true)"
if [[ -z "${rat_snip}" ]]; then
  say "(definition not found)"
else
  say "${rat_snip}"
  # Heuristic: the presence of a `| zero` base constructor (and no reference to an actual ℚ-subspace map)
  # indicates the current proof-first stub.
  if echo "${rat_snip}" | grep -qF "| zero"; then
    fail_count=$((fail_count + 1))
  fi
fi

# 4c) Kähler power stub(s)
say ""
say "### Kähler power stub (showing kahlerPow base case snippet)"
kp_snip="$(grep -n -A 12 -B 2 "def kahlerPow" Hodge/Kahler/TypeDecomposition.lean 2>/dev/null || true)"
if [[ -z "${kp_snip}" ]]; then
  say "(definition not found)"
else
  say "${kp_snip}"
  if echo "${kp_snip}" | grep -qF "| 0 => 0"; then
    fail_count=$((fail_count + 1))
  fi
fi

# 4d) Unit form stub (unit 0-form is currently `0`)
say ""
say "### Unit form stub (showing unitForm definition snippet)"
unit_snip="$(grep -n -A 3 -B 1 "def unitForm" Hodge/Analytic/Forms.lean 2>/dev/null || true)"
if [[ -z "${unit_snip}" ]]; then
  say "(definition not found)"
else
  say "${unit_snip}"
  if echo "${unit_snip}" | grep -qE 'def unitForm[^=]*:=[[:space:]]*0[[:space:]]*$'; then
    fail_count=$((fail_count + 1))
  fi
fi

# 5) Known semantic stubs: major Kähler/Hodge operators set to 0 (show defining snippets)
say ""
say "### Kähler/Hodge operator stubs (key definitions in Hodge/Kahler/Manifolds.lean)"
kahler_snip="$(
  { grep -n -A 3 -B 0 "def lefschetzLambdaLinearMap" Hodge/Kahler/Manifolds.lean || true; echo ""; } ;
  { grep -n -A 3 -B 0 "def hodgeStar" Hodge/Kahler/Manifolds.lean || true; echo ""; } ;
  { grep -n -A 1 -B 0 "def adjointDeriv" Hodge/Kahler/Manifolds.lean || true; echo ""; } ;
  { grep -n -A 1 -B 0 "def laplacian" Hodge/Kahler/Manifolds.lean || true; }
)"
if [[ -z "${kahler_snip//$'\n'/}" ]]; then
  say "(no matching definitions found)"
else
  say "${kahler_snip}"
  if echo "${kahler_snip}" | grep -qE ':=[[:space:]]*0([[:space:]]|$)|^[0-9]+:[[:space:]]*0[[:space:]]*$'; then
    fail_count=$((fail_count + 1))
  fi
fi

say ""
say "### Summary"
if [[ $fail_count -eq 0 ]]; then
  say "No blockers detected by grep-level audit."
else
  say "Detected ${fail_count} blocker category(ies)."
  if [[ $STRICT -eq 1 ]]; then
    say "Failing due to --strict."
    exit 1
  fi
fi

exit 0


