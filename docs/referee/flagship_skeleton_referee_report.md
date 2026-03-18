# Referee Report on `flagship_skeleton.tex`

## Summary

This manuscript presents a concise proof spine for a larger four-paper program.
Its strongest feature is architectural clarity: the paper isolates the
signed-decomposition reduction, the closure chain from almost-calibrated cycles
to holomorphic chains, and the final implication to the Hodge conjecture.

In its current form, however, the manuscript overstates what is proved inside
this paper alone and underspecifies the dependency on the companion papers.
The main issue is not the mathematical direction of the argument, but the
presentation of scope, assumptions, and imported interfaces.

I would recommend revision before circulation or submission.

## Major Concerns

1. Scope is overstated relative to the paper's own content.

The title, abstract, and main theorem presently read as though the paper gives
a standalone proof of the Hodge conjecture, while Section 2 explicitly treats
the companion-paper outputs as black-box inputs. A referee will view this as a
serious framing problem.

The manuscript should make clear, from the title onward, that it is the proof
spine of a series and that the final theorem is proved under the interface
results established in the companion papers.

2. The interface theorems are not cited precisely enough.

The current `H1` and `H2` interface propositions say only “companion local
paper” and “companion assembly paper.” A referee will want exact titles and
bibliographic entries, and ideally an indication of which main exported result
from each companion paper is being used.

3. `Proposition~\\ref{prop:cohomology-match}` has incomplete notation.

The statement uses `I_\\ell` without defining it, and the current wording
mentions `T_\\eps` before the corrected cycle is fully specified. This makes
the proposition formally incomplete even at the statement level.

4. The proof-label “Reference” is too weak in journal style.

The interface propositions have proof environments that say only “Reference.”
This looks provisional. The paper should either:

- replace those with a short “Source in the series” paragraph, or
- keep a proof environment but explicitly cite the companion preprints by title.

5. The dependence of the main theorem on the interface results should be made
explicit at theorem level.

Even if the series context is clear in the introduction, the main closure
theorems should be stated under the interface assumptions, rather than leaving
that dependence implicit.

## Minor Concerns

1. `Theorem~\\ref{thm:automatic-syr}` ends with “Consequently, $[\\gamma]$ is
algebraic,” which compresses the use of `Theorem~\\ref{thm:syr}` too much.
The wording should explicitly say that algebraicity follows by combining the
SYR conclusion with the closure theorem.

2. The introduction would benefit from one short “series convention” paragraph
stating that Sections 3--6 are proved from the interface propositions in
Section 2.

3. The bibliography should include entries for the companion manuscripts, since
they are structurally essential to the paper.

## Recommendation

Revise the manuscript so that it reads as an honest flagship paper in a series:

- title and abstract should identify it as the proof spine of the program,
- companion inputs should be cited precisely,
- theorem statements should make their interface dependence explicit,
- incomplete notation in the cohomology-matching proposition should be fixed.

With those revisions, the paper would be significantly stronger and much more
credible to a referee.
