import Hodge.Main

/-!
# Dependency Check Utility

This file prints the axioms used by the main theorem `hodge_conjecture`
and its variant `hodge_conjecture'`.

## Usage

Run with `lake env lean Hodge/Utils/DependencyCheck.lean` to verify
the proof track only depends on standard Lean axioms:
- `propext` (propositional extensionality)
- `Classical.choice` (axiom of choice)
- `Quot.sound` (quotient soundness)
-/

#print axioms hodge_conjecture
#print axioms hodge_conjecture'
