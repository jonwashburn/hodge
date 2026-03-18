# Standalone Proof Package

This folder is a standalone snapshot of the revised proof package assembled on
`2026-03-17`.

## Structure

- `manuscripts/`
  - `SERIES_ABSTRACT.txt`
  - `flagship_skeleton.tex`
  - `flagship_skeleton.pdf`
  - `local_holomorphic_microstructures.tex`
  - `local_holomorphic_microstructures.pdf`
  - `coherent_assembly_packets_from_cone_forms.tex`
  - `coherent_assembly_packets_from_cone_forms.pdf`
  - `global_gluing_exact_periods_and_fixed_class_realization.tex`
  - `global_gluing_exact_periods_and_fixed_class_realization.pdf`
  - `final_synthesis_calibrated_holomorphic_limits_and_hodge_conclusion.tex`
  - `final_synthesis_calibrated_holomorphic_limits_and_hodge_conclusion.pdf`

## What is included

- A revised flagship proof-spine manuscript in `manuscripts/flagship_skeleton.tex`
  with a compiled PDF.
- Revised Papers I--III with updated referee-facing framing, exact export
  citations, and clearer scope statements.
- The current capstone manuscript from the four-paper package.
- The series abstract as a compact overview of the four-paper program.

## Current status

- `flagship_skeleton.tex` compiles successfully.
- `local_holomorphic_microstructures.tex` compiles successfully.
- `coherent_assembly_packets_from_cone_forms.tex` compiles successfully.
- `global_gluing_exact_periods_and_fixed_class_realization.tex` compiles successfully.
- `final_synthesis_calibrated_holomorphic_limits_and_hodge_conclusion.tex` is
  included as the current capstone manuscript.

## Notes

- The flagship paper now cites the exported theorem numbers from Papers I--III
  as `Theorem 1.1` in each companion paper.
- Paper III is now the precise downstream interface that should be imported by
  the capstone paper.
- The capstone paper has been aligned to Paper III's full exported contract,
  including the marginal-period condition `(A3)` and the modulo-torsion class
  language.
- Internal planning and referee notes have been removed from this standalone
  package so that the folder is handoff-ready.
