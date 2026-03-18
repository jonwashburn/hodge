# Review and updates for Papers I–III

## Paper I
File: `local_holomorphic_microstructures.tex`

### Main issues found
- The title and export language overstated the face-trace claim: the paper proves template-controlled face traces, not arbitrary prescribed face data.
- The scope limits were present but not sharp enough for downstream citation.
- The downstream export was distributed across the main theorem and the final summary, rather than isolated as one interface contract.

### Updates made
- Retitled the paper to say `template-controlled face traces`.
- Tightened the abstract and introduction so the non-claims are explicit:
  no arbitrary face-data realization, no boundary closing, no global transport,
  no cohomological matching.
- Added a clear `What this paper does not prove` paragraph in the introduction.
- Clarified the notation in the main theorem around `R_{j,F}` and `\tau_{t_{j,a}}`.
- Added `Corollary [Paper I interface theorem]` as a downstream-safe export.
- Added `HL82` to the bibliography and cited calibrated geometry explicitly.

## Paper II
File: `coherent_assembly_packets_from_cone_forms.tex`

### Main issues found
- The paper referred to Papers I, III, and IV without exact bibliographic identification.
- The export role was clear in spirit but not sharp enough in theorem-level prose.
- The abstract used the scale condition `\alpha > 2n/k` without defining `k`.
- The scope limits were not stated early enough.

### Updates made
- Added exact series citations and theorem-number references for Papers I, III, and IV.
- Tightened the abstract so it now states this paper does not construct closed cycles,
  does not perform exact-class locking, and does not prove the Hodge conjecture.
- Replaced `\alpha > 2n/k` in the abstract by the explicit expression
  `\alpha > 2n/(2n-2p)`.
- Added an explicit non-claims paragraph and theorem-notation paragraph before the main theorem.
- Tightened the theorem/export wording so it now says the packet is the object imported
  as `Paper II, Theorem 1.1` in Paper III.
- Added bibliography entries for Papers I, III, and IV.

## Paper III
File: `global_gluing_exact_periods_and_fixed_class_realization.tex`

### Main issues found
- The paper had essentially no bibliography despite relying on standard results and the companion papers.
- The abstract and introduction did not sharply separate what Paper III proves from what Papers I, II, and IV do.
- The phrase `exact prescribed homology class` was stronger than the actual modulo-torsion conclusion.
- The export section was not explicit enough that downstream papers should import Theorem 1.1 verbatim, including `(A3)`.

### Updates made
- Added exact citations to Papers I, II, and IV in the abstract and introduction.
- Tightened the abstract to say the output class is the prescribed class modulo torsion.
- Added a `What this paper does not prove` paragraph and a notation paragraph before the main theorem.
- Added standard references for discrepancy, integral pairings, and Federer–Fleming filling.
- Tightened the export section to say the downstream import is Theorem 1.1 itself, including `(A3)`.
- Added a full bibliography with entries for Papers I, II, IV and the classical references used.

## Verification
- `local_holomorphic_microstructures.tex` compiles successfully.
- `coherent_assembly_packets_from_cone_forms.tex` compiles successfully.
- `global_gluing_exact_periods_and_fixed_class_realization.tex` compiles successfully.
