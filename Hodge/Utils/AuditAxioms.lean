import Hodge.Kahler.Main

/-!
# Axiom Audit Utilities

This file is **not** part of the main development; it exists to make it easy to extract
Lean's computed axiom-dependency information for the final theorem(s), without running
full builds.

Usage (lightweight):
- `lake env lean Hodge/Utils/AuditAxioms.lean`

Note: This prints to stdout during elaboration.
-/

set_option pp.universes true

-- Axiom dependency report for the main theorem.
#print axioms hodge_conjecture'
