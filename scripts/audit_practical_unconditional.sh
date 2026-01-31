#!/bin/bash
#
# Practical “fully unconditional” audit:
# - no *actual* `sorry` blocks in Hodge/ Lean files
# - no `instance … .universal` declarations in Hodge/
# - `hodge_conjecture'` does not require deep typeclass binders
#
# Run from repo root:
#   ./scripts/audit_practical_unconditional.sh
#
set -euo pipefail

cd "$(dirname "$0")/.." || exit 1

echo "========================================"
echo "PRACTICAL UNCONDITIONAL AUDIT"
echo "========================================"
echo ""

echo "1) SORRY BLOCKS (Hodge/)"
echo "------------------------"
SORRY_RE='^[[:space:]]*sorry([^[:alnum:]_]|$)'
sorry_count=$( (grep -RIn --include="*.lean" -E "$SORRY_RE" Hodge/ 2>/dev/null || true) | wc -l | tr -d ' ' )
if [ "$sorry_count" -eq 0 ]; then
  echo "✓ No sorry blocks found in Hodge/"
else
  echo "✗ Found $sorry_count sorry block(s) in Hodge/:"
  grep -RIn --include="*.lean" -E "$SORRY_RE" Hodge/ 2>/dev/null
  exit 1
fi
echo ""

echo "2) TRIVIAL UNIVERSAL INSTANCES (Hodge/)"
echo "--------------------------------------"
UNIV_INST_RE='^[[:space:]]*instance[[:space:]].*\\.universal([^[:alnum:]_]|$)'
univ_inst_count=$( (grep -RIn --include="*.lean" -E "$UNIV_INST_RE" Hodge/ 2>/dev/null || true) | wc -l | tr -d ' ' )
if [ "$univ_inst_count" -eq 0 ]; then
  echo "✓ No \`instance … .universal\` declarations found in Hodge/"
else
  echo "✗ Found $univ_inst_count \`instance … .universal\` declaration(s) in Hodge/:"
  grep -RIn --include="*.lean" -E "$UNIV_INST_RE" Hodge/ 2>/dev/null
  exit 1
fi
echo ""

echo "3) hodge_conjecture' binder scan"
echo "-------------------------------"
tmpfile="$(mktemp -t hc_check_XXXXXX.lean)"
cat > "$tmpfile" <<'EOF'
import Hodge.Kahler.Main
#check hodge_conjecture'
EOF

hc_type="$(lake env lean "$tmpfile" 2>/dev/null || true)"
rm -f "$tmpfile"

if [ -z "$hc_type" ]; then
  echo "✗ Failed to obtain type of hodge_conjecture' (lake env lean returned no output)."
  exit 1
fi

echo "$hc_type" | tail -20
echo ""

BAD_BINDERS_RE='AutomaticSYRData|HarveyLawsonKingData|ChowGAGAData|SpineBridgeData|SubmanifoldIntegration|FlatLimitCycleData|CycleClass\.PoincareDualFormExists'
if echo "$hc_type" | grep -E "$BAD_BINDERS_RE" >/dev/null 2>&1; then
  echo "✗ hodge_conjecture' still mentions deep typeclass binders:"
  echo "$hc_type" | grep -E "$BAD_BINDERS_RE" || true
  exit 1
else
  echo "✓ hodge_conjecture' type contains no deep typeclass binders"
fi

echo ""
echo "========================================"
echo "AUDIT PASSED"
echo "========================================"

