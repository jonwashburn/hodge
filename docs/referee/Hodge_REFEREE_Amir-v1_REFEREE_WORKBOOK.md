## Referee Workbook — *Calibration–Coercivity and the Hodge Conjecture*

**Source**: `Hodge_REFEREE_Amir-v1.tex`
**Generated**: 2026-01-05 18:39:28

This workbook is designed to support **line-by-line verification** of every labeled result, and a **holistic audit** of the full argument, at a standard suitable for an Annals submission.

### How to use this workbook (recommended workflow)

- **Pass 0 — Compile & hygiene**: ensure the TeX compiles cleanly and resolve duplicate labels/cross-references before deep checking.
- **Pass 1 — Holistic read**: read the Introduction + the Referee Packet appendix and write a 1–2 page “proof in your own words” summary.
- **Pass 2 — Dependency chain audit**: verify that every arrow in the main chain is logically correct and that all hypotheses are available at the invocation site.
- **Pass 3 — Local verification**: for each lemma/proposition/theorem below, rewrite the proof (or annotate it) and check every nontrivial estimate, quantifier order, and hidden regularity assumption.
- **Pass 4 — Consistency sweep**: check notation consistency, constants, normalization factors, and that all “small-o/\(\ll\)” requirements are simultaneously satisfiable.

### Holistic verification checklist (Annals-ready)

- [ ] **Main statement**: Theorem `thm:main-hodge` matches the intended claim (rational Hodge classes on smooth complex projective manifolds are algebraic).
- [ ] **Scope clarity**: every time projectivity (vs. compact Kähler) is required, it is stated and used correctly (especially for Chow/GAGA and line bundle inputs).
- [ ] **Quantifier/parameter schedule**: global choices (\(m\), mesh \(h_j\), tolerances \(\varepsilon_j,\delta_j\), Bergman scale \(M_j\), etc.) are chosen in a valid order with compatible asymptotics.
- [ ] **No circularity**: no lemma/proposition relies (directly or indirectly) on the main theorem or on results proved later without explicit forward references.
- [ ] **Normalization checks**: factors like \(p!\), \((n-p)!\), \(2\pi\), orientation conventions, and Poincaré duality conventions are consistent throughout.
- [ ] **GMT correctness**: integrality/rectifiability/compactness/LSC inputs match the cited versions (Federer–Fleming / Federer / Simon / Allard) and are invoked with correct hypotheses.
- [ ] **Complex-analytic endgame**: the step “\(\psi\)-calibrated integral current ⇒ positive holomorphic chain” matches the precise Harvey–Lawson/King/Demailly statements being cited.
- [ ] **Algebraicity endgame**: analytic subvarieties on projective \(X\) are shown algebraic via Chow + GAGA with hypotheses clearly satisfied.
- [ ] **Edge cases**: \(p=1\), \(p=n-1\), and the borderline \(p=n/2\) regime are handled with no hidden assumptions.
- [ ] **Presentation**: references resolve, labels are unique, and the proof is readable as a standalone argument.

### Extracted inventory (for tracking)

Environment counts extracted from the TeX source (statements + labeled equations):

- **conjecture**: 1
- **corollary**: 10
- **definition**: 7
- **equation**: 15
- **lemma**: 60
- **proposition**: 29
- **remark**: 47
- **theorem**: 14

### Duplicate label audit (must resolve before submission)

As of the latest automated scan, **no duplicate `\label{...}` identifiers** were detected in `Hodge_REFEREE_Amir-v1.tex`.

- [ ] Re-run the duplicate-label scan after large edits (especially when re-enabling `\iffalse` blocks or pasting older draft fragments).

### Hygiene status (2026-01-06)

- [x] **Duplicate labels**: automated scan found 0 duplicates (post-edit).
- [x] **Duplicate proof blocks**: removed stray back-to-back proof environments (notably after `lem:radial-min` and in the calibrated-cone preliminaries, plus the earlier duplicates around `lem:limit_is_calibrated` and `prop:almost-calibration`).
- [x] **Terminology**: added TeX remark `rem:algebraic-class-convention` clarifying what “algebraic class” means (\(\mathbb Q\)-span of cycle classes).
- [x] **Transport/gluing interface clarity**: made explicit in TeX Proposition `prop:transport-flat-glue` that (after edge trimming) the face slices are cycles on the interior face, so the Step 1 homotopy/Lipschitz estimate drops the boundary-slice term (aligned with Lemma `lem:face-slice-cycle-mass`).
- [x] **Parameter/notation collisions**: separated the cohomology multiplier \(m\) (fixed in SYR) from the Bergman/holomorphic tensor-power parameter (denoted \(N\) when both appear together), and removed misleading “\(h\downarrow 0\iff m\to\infty\)” phrasing in fixed-\(m\) statements.
- [x] **Period-locking proof hygiene**: removed a duplicated internal “Step 5” construction inside `prop:cohomology-match` (the boundary correction is now handled once, in the following dedicated subsection).
- [x] **Filling lemma correctness**: in `lem:FF-filling-X`, made explicit that the Euclidean filling used is supported in the tubular neighborhood where the nearest-point projection is defined (relative filling in the tubular domain).
- [x] **Combinatorics/typos**: fixed a constant mismatch in `lem:prefix-discrepancy` and a stray TeX typo in `prop:global-coherence-all-labels` (`\\emph{...}` → `\emph{...}`).
- **See also**:
  - `docs/referee/AI_NOTES_PROOF_WALKTHROUGH.md`
  - `docs/referee/REFEREE_PATCH_REPORT.tex`

### Main dependency chain (from the TeX “Referee packet”)

Use this as the *spine* of the holistic verification. For each arrow, record exactly where the dependency is proved and what hypotheses are used.

- [ ] **Theorem `thm:main-hodge`**
  - [ ] Hard Lefschetz reduction (Remark `rem:lefschetz-reduction`)
  - [ ] Signed decomposition (Lemma `lem:signed-decomp`)
  - [ ] Algebraicity of \(\gamma^-\) (Lemma `lem:gamma-minus-alg`)
  - [ ] Cone–positive ⇒ algebraic (Theorem `thm:effective-algebraic`)
    - [ ] Automatic SYR (Theorem `thm:automatic-syr`)
      - [ ] Spine theorem / quantitative almost-mass-minimizing cycles (Theorem `thm:spine-quantitative`)
        - [ ] (H1) local holomorphic sheet manufacturing (Theorem `thm:local-sheets`, packaged in Proposition `prop:h1-package`)
        - [ ] (H2) global coherence + corner-exit gluing (Proposition `prop:h2-package` and its downstream chain)
        - [ ] Exact class enforcement (Proposition `prop:cohomology-match` using Lemmas `lem:integral-periods`, `lem:lattice-discreteness`)
        - [ ] Vanishing defect (Proposition `prop:almost-calibration`)
      - [ ] Closure: realization from almost-calibrated sequences (Theorem `thm:realization-from-almost`)
        - [ ] Harvey–Lawson holomorphic-chain conclusion
        - [ ] Chow/GAGA ⇒ algebraic on projective \(X\) (Remark `rem:chow-gaga`)

### External results / citation checklist

For each external pillar, fill in the exact statement used and check hypotheses at every invocation site:

- [ ] Hard Lefschetz + Hodge decomposition (Voisin/Huybrechts/Griffiths–Harris)
- [ ] Federer–Fleming: compactness, deformation theorem, isoperimetric filling
- [ ] Mass lower semicontinuity
- [ ] Harvey–Lawson: calibrated currents ⇒ holomorphic chains
- [ ] Chow + Serre GAGA: analytic ⇒ algebraic on projective \(X\)
- [ ] Hörmander \(L^2\ \bar\partial\) methods
- [ ] Bergman kernel asymptotics / peak sections (Tian/Catlin/Zelditch/Ma–Marinescu)
- [ ] Bárány–Grinberg discrepancy rounding
- [ ] Optimal transport / Kantorovich–Rubinstein duality (for any \(W_1\) steps)

### Quantifier / parameter schedule audit

Record the *order of choices* and verify each later choice depends only on earlier ones:

- [ ] Choose \(m\ge 1\) so that \(m[\gamma]\in H^{2p}(X,\mathbb Z)\) and all period constraints become integral.
- [ ] Choose mesh sequence \(h_j\downarrow 0\) and cubulations.
- [ ] Choose accuracy scales \(\varepsilon_{\mathrm{net},j}\ll h_j\), \(\delta_j=o(h_j)\), \(\varepsilon_j=o(1)\).
- [ ] Choose holomorphic scale \(M_j\to\infty\) sufficient for the Bergman-scale manufacturing at tolerance \(\varepsilon_j\).
- [ ] Choose discrete integer data at each \(j\) meeting local budgets + slow-variation + global period constraints.
- [ ] Verify target inequalities: \(\mathcal F(\partial T^{\mathrm{raw}}_j)\to 0\) ⇒ small correction fillings ⇒ defect \(\to 0\).

### Statement-by-statement referee checklist

For each item below, rewrite/annotate the proof. Recommended minimum deliverable per item:

- [ ] **Statement verified** (all hypotheses/notation correct)
- [ ] **Proof verified** (every nontrivial step justified or cited)
- [ ] **Downstream use verified** (later uses match the proved statement)

#### Section: Front matter / unsectioned

##### Definition `def:flat-norm` — Flat norm on integral currents
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 248
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

#### Section: Introduction

##### Theorem `thm:cal-coercivity-intro` — Calibration--coercivity (cone-valued harmonic classes)
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 353
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

#### Section: Calibrated Grassmannian and Pointwise Cone Geometry

##### Lemma `lem:calibrated-cone-closed` — Closure of the calibrated cone
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 739
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Lemma `lem:radial-min` — Explicit minimization in the radial parameter
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 905
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Equation `eq:ray-defect-formula`
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 933
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Lemma `lem:radial-min` — Explicit minimization along a calibrated ray
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 946
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Equation `eq:ray-defect-formula`
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 959
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Lemma `lem:trace-L2` — Trace $L^{2}$ control
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 1069
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Equation `eq:trace-L2-bound`
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 1090
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Proposition `prop:dist-cal-properties` — Well-posedness and basic properties
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 1152
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Proposition `prop:dist-cal-properties` — Well-posedness and basic properties
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 1203
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Lemma `lem:kahler-angle` — Quadratic control for small Jordan angles (principal angles)
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 1364
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Equation `eq:kahler-angle-est`
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 1373
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Remark `line-1420` — Geometric meaning of Lemma~\ref{lem:kahler-angle}
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 1420
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

#### Section: Energy Gap and Primitive/Off--Type Controls

##### Equation `eq:energy-split`
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 1499
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Equation `eq:type-split`
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 1514
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Equation `eq:primitive-control`
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 1525
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Lemma `lem:elliptic-coulomb` — Elliptic estimate on the Coulomb slice
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 1538
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Lemma `lem:coulomb` — Coulomb decomposition and energy identity
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 1559
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

#### Section: The Calibrated Grassmannian and an Explicit \texorpdfstring{$\varepsilon$

##### Lemma `lem:covering-number` — Covering number
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 1695
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Equation `eq:grass-cover`
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 1699
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

#### Section: Pointwise Linear Algebra: Controlling the Net Distance

##### Equation `eq:typesplit-orth`
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 1818
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Lemma `lem:typesplit` — Off--type separation for $D_{\mathrm{net}}$
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 1843
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Equation `eq:Dnet-typesplit`
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 1846
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Lemma `lem:hermitian-model` — Hermitian model for $(p,p)$
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 1880
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Remark `rem:cone-not-full-psd` — Calibrated cone in the Hermitian model; not the full PSD cone for $1<p<n-1$
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 1945
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Lemma `lem:rankone` — Rank--one approximation controls the traceless part
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 1964
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Proposition `prop:pp-projection` — PSD surrogate for the $(p,p)$ projection
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 1995
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Equation `eq:pp-projection`
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 2000
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Corollary `cor:Dpsd-pointwise` — Pointwise rank--one PSD surrogate
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 2030
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Equation `eq:Dpsd-pointwise`
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 2040
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

#### Section: Calibration--Coercivity (Explicit) and Its Proof

##### Theorem `thm:cal-coercivity` — Calibration--coercivity (cone-valued harmonic classes, explicit)
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 2100
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Equation `eq:global-coercivity`
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 2104
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Remark `rem:coercivity-hypothesis` — On the coercivity hypothesis
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 2124
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Equation `eq:projection-identity`
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 2150
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Remark `line-2155` — Limitation of pointwise projection
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 2155
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

#### Section: From Cone–Valued Minimizers to Calibrated Currents

##### Theorem `thm:spine-quantitative` — Quantitative almost--mass--minimizing cycles (referee-checkable spine)
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 2180
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Remark `line-2251` — Where to look for (H1)--(H2) in this manuscript
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 2251
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Lemma `lem:borderline-p-half` — Borderline ($p=n/2$): closure via a refined displacement schedule
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 2313
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Proposition `prop:h1-package` — H1 package: local holomorphic multi-sheet manufacturing
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 2404
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Proposition `prop:h2-package` — H2 package: global face coherence and gluing (corner-exit route)
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 2434
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Theorem `thm:realization-from-almost` — Realization from almost--calibrated sequences
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 2450
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Lemma `lem:flat_limit_of_cycles_is_cycle` — Flat limits of cycles are cycles
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 2524
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Lemma `lem:limit_is_calibrated` — Almost--calibrated limits are calibrated
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 2539
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Remark `line-2595` — How to use Theorem~\ref{thm:realization-from-almost}
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 2595
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Theorem `thm:codim1` — Codimension one (Lefschetz $(1,1)$)
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 2608
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Remark `line-2624` — Mass equality in the effective codimension-one case
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 2624
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Proposition `prop:complete-intersection` — Complete intersections
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 2637
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Definition `def:syr` — Stationary Young--measure realizability (SYR)
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 2657
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Theorem `thm:syr` — Calibrated realization under SYR
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 2685
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Remark `line-2723`
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 2723
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Definition `line-2737` — Locally integrable calibrated decomposition (LICD)
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 2737
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Theorem `thm:classical-syr-licd` — Classical SYR under LICD
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 2751
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Corollary `cor:closure-licd` — Closure of the program under LICD
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 2816
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Lemma `lem:caratheodory-general` — Uniform Carath\'eodory decomposition
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 2867
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Lemma `lem:caratheodory-general` — Uniform Carath\'eodory decomposition
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 2903
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Lemma `lem:lipschitz-qp-weights` — Lipschitz weights from a strongly convex simplex fit
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 2944
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Remark `rem:direction-net-qp` — Stable direction labeling via a growing net
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 2992
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Lemma `lem:jet-surjectivity` — Jet surjectivity for ample powers (pointwise and for finite sets)
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 3015
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Lemma `lem:bergman-control` — Uniform $C^1$ control on $m^{-1/2}$-balls via Bergman kernels
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 3063
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Lemma `lem:graph-from-grad` — Graph control from uniform gradient control
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 3169
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Proposition `prop:tangent-approx-full` — Projective tangential approximation with $C^1$ control
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 3217
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Proposition `prop:dense-holo` — Holomorphic density of calibrated directions
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 3284
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Theorem `thm:local-sheets` — Local multi-sheet construction
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 3317
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Lemma `lem:local-bary` — Local barycenter and mass matching
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 3499
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - The current TeX statement has been strengthened/clarified to include a **local mass target** \(M_Q:=m\int_Q\beta\wedge\psi\) and a quantitative bound \(|\Mass(S_Q)-M_Q|\le \delta M_Q\), not just barycenter matching.
  - The key issue to verify here is that the construction supplies **many equal-mass pieces** per direction label on a cube while keeping the total mass budget fixed. The intended mechanism is the **corner-exit template family**: within each label, all footprints are identical (hence equal \(\psi\)-mass) and the per-piece mass scales like \(A_{Q,j}\asymp s^{k}\) with \(k=2n-2p\) and a tunable scale \(s\ll h\).
  - This replaces the false “translation-independence for generic planes in a cube” heuristic by an explicit *template box* statement (cf. Lemma `lem:complex-corner-exit-template` / `lem:corner-exit-mass-scale` / Proposition `prop:corner-exit-template-net`).
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - The discretization accuracy for barycenter weights is \(\sim 1/N_Q\) when masses are equal within each family, so to get error \(<\delta\) one needs \(N_Q\gtrsim 1/\delta\). The manuscript claims this can be achieved by shrinking the corner-exit scale \(s\) (hence shrinking \(A_{Q,j}\asymp s^k\)) rather than by sending the cohomology multiplier \(m\to\infty\). Verify the parameter schedule supports this while preserving holomorphic manufacturability and face parameterization assumptions used later.
  - Check whether any step implicitly requires **uniform lower bounds** on template conditioning constants (the \(\alpha_*(h),A_*(h),\Lambda(h)\) package) as the direction net is refined.

##### Theorem `thm:global-cohom` — Global cohomology quantization
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 3542
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - This is the locus of the main “per-cube matching” obstruction from the hostile-referee audit. As originally written, the proof used a constant per-sheet mass \(A_{Q,j}\asymp h^{k}\) (with \(k=2n-2p\)) and then tried to match the cube budget \(M_Q=m\int_Q\beta\wedge\psi\asymp m h^{2n}\) by integer rounding. That produces the scaling contradiction \(M_Q/A_{Q,j}\sim m h^{2p}\to 0\) as \(h\downarrow 0\) (for fixed \(m\), \(p\ge 1\)).
  - The manuscript now explicitly routes this step through **corner-exit templates**: per-piece mass is \(A_{Q,j}\asymp s^{k}\) for a tunable scale \(s\ll h\), and within each label the footprints are identical (hence equal slice masses). The intended fix is that shrinking \(s\) (equivalently shrinking the transverse radius factor \(\varrho\sim s/h\)) increases the available integer resolution \(M_Q/A_{Q,j}\) without changing \(m\).
  - Verify that the proof no longer relies on the false claim “all affine sheets of a fixed tangent plane have equal mass in a cube”; equal-mass is instead a **design feature** of the template box.
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - Confirm the quantifier order: SYR needs a **fixed** \(m\), while meshes/tolerances shrink. The fix strategy is to let the *template scale* \(s(h,\delta)\) shrink with the mesh, not \(m\) grow with the mesh.
  - Check that shrinking \(s\) is compatible with later gluing/transport assumptions (face measures supported in \(B(0,C\varrho h)\), displacement \(\Delta_F\lesssim \varrho h^2\), etc.) and with the holomorphic/Bergman manufacturing scale.
  - If the statement also asserts “local tangent-plane mass proportions match those of \(\beta\) up to \(o(1)\)”, verify that the number of pieces per cube \(N_Q\) actually grows fast enough (via shrinking \(s\)) to make the barycenter discretization error vanish.

##### Proposition `prop:transport-flat-glue` — Transport control $\Rightarrow$ flat-norm gluing
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 3642
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Remark `rem:transport-hypotheses` — Why hypotheses (a)--(b) hold for the local sheet model
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 3778
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Lemma `lem:w1-auto` — Automatic $W_1$-matching from smooth dependence of face maps
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 3810
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Lemma `lem:face-displacement` — Pointwise displacement bound under nearby face maps
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 3842
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Lemma `lem:w1-template-edit` — Template stability under small multiset edits
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 3865
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Remark `rem:w1-auto` — How Lemma~\ref{lem:w1-auto} reduces the remaining matching task
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 3885
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Remark `rem:sliver-vs-template` — Sliver regime: what changes in the global counting estimate
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 3908
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Proposition `prop:transport-flat-glue-weighted` — Weighted transport $\Rightarrow$ flat-norm face control (sliver-compatible)
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 3929
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Proposition `prop:integer-transport` — Integer transverse matching from the master prefix template (constructed here)
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 3976
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Remark `line-4036` — Exact geometric inequality needed for slivers
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 4036
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Lemma `lem:uniformly-convex-slice-boundary` — Boundary shrinkage for plane slices in smooth uniformly convex cells
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 4050
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Remark `line-4096` — References for the geometric inputs
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 4096
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Lemma `lem:flat-translate` — Flat-norm stability under translation
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 4105
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Lemma `lem:flat-C0-deform` — Flat-norm stability under small $C^0$ deformations
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 4146
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Lemma `lem:face-slice-cycle-mass` — {\color{blue}Interface face-slices are cycles with controlled mass}
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 4187
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Corollary `cor:global-flat-weighted` — Global flat-norm bound from weighted face control (sliver-compatible)
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 4244
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Remark `rem:weighted-scaling` — Consistency with the constant-mass-per-sheet template regime
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 4320
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Remark `rem:weighted-scaling` — Scaling consequence: weighted gluing + packing
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 4327
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Remark `rem:no-vanishing-piece-mass` — On vanishing per-piece masses (no hidden lower bound)
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 4372
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Remark `rem:sliver-bergman-scaling` — Model scaling at the Bergman cell size
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 4392
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Remark `rem:w1-multiplicity` — Handling slowly varying multiplicities
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 4426
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Lemma `lem:flat-diameter` — Flat norm of a cycle supported in diameter $\lesssim h$
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 4437
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Lemma `lem:template-displacement` — Template displacement $\Rightarrow$ per-face flat-norm mismatch
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 4469
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Lemma `lem:template-displacement-edits` — Template displacement with insertions/deletions
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 4525
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Lemma `lem:template-edits-oh` — If edits are an $O(h)$ fraction, they are $h^2$ in flat norm
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 4567
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Remark `rem:bounded-corrections` — Bounded global corrections do not spoil the $O(h)$ edit regime
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 4591
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Remark `rem:nested-template-scheme` — Nested prefix-template scheme
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 4601
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Proposition `prop:prefix-template-coherence` — Prefix templates $\Rightarrow$ interface coherence up to $O(h)$ edits
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 4614
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Theorem `thm:sliver-mass-matching-on-template` — Global prefix-template activation / mass matching (template bookkeeping)
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 4651
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Remark `rem:activation-hypotheses-status` — Status of the activation hypotheses in the corner-exit route
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 4715
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Proposition `prop:prefix-activation-flat-ball` — Flat-ball model: prefix activation is feasible
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 4731
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - **Hygiene fix applied**: the TeX previously wrote an “ordered \(\delta\)-separated template \((t_a)_{a\ge 1}\)” on a compact sphere, which cannot exist for fixed \(\delta>0\).
    It now correctly uses a finite \(\delta\)-separated list \((t_a)_{a=1}^N\), and notes that one can make \(N\) large by taking \(\delta\) smaller.
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Corollary `cor:prefix-activation-holo` — Holomorphic prefix activation on a Bergman-scale ball cell
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 4768
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Lemma `lem:oh-face-edit-regime` — A sufficient condition for the $O(h)$ face-edit regime
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 4800
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Remark `rem:iv-what-remains` — Item \textnormal{(iv)}: tail-heaviness and how it is enforced
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 4839
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Remark `rem:param-tension` — Parameter tension and the chosen regime
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 4853
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Remark `rem:lefschetz-reduction` — Hard Lefschetz reduction to $p\le n/2$
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 4868
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Lemma `lem:mass-tunable` — Mass tunability of plane slices in the flat model
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 4882
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Remark `rem:sliver` — Sliver pieces and fixed-$m$ microstructure
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 4910
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Lemma `lem:sphere-quantize` — Quantizing a Lipschitz density on a sphere
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 4920
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Lemma `lem:sphere-quantize-nested` — Nested equal-weight quantization of the uniform sphere
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 4968
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Proposition `prop:flat-sliver-local` — Flat ball model slivers achieve $W_1$ transverse approximation
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 4995
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Corollary `cor:holomorphic-flat-sliver-local` — Holomorphic upgrade on a ball cell
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 5029
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Remark `line-5084` — Interpretation
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 5084
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Conjecture `conj:sliver-local` — Local sliver-sheet realizability (quantitative target)
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 5096
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Remark `rem:sliver-cell-shape` — Why we ask for a smooth convex cell
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 5123
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Remark `line-5136` — Why templates should live at vertices (pan-vertex distribution)
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 5136
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Definition `def:vertex-template` — Global vertex template (flat cubical model)
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 5148
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Lemma `lem:complex-corner-exit-template` — A concrete \emph{complex} corner-exit translation template in a cube
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 5184
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - **Hygiene fix applied**: the TeX now states the correct packing fact: for fixed separation \(\delta>0\) one gets a *finite* \(\delta\)-separated list of translations inside the bounded admissible parameter box, with length \(N(\delta)\to\infty\) as \(\delta\downarrow 0\) (with the footprint scale fixed).
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Lemma `lem:corner-exit-mass-scale` — Corner-exit simplex mass scale and no-heavy-tail uniformity
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 5251
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Lemma `lem:corner-exit-template-open` — Corner-exit translation templates for a quantitative family of complex planes
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 5281
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - Same packing-language hygiene fix as in `lem:complex-corner-exit-template`: for fixed \(\delta>0\), only finitely many \(\delta\)-separated translations fit in the bounded template box; length grows as \(\delta\downarrow 0\).
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Proposition `prop:corner-exit-template-net` — Robust corner-exit templates for a finite direction net
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 5184
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - Verified that the net is taken inside the dense “nondegenerate” open set \(\mathcal U\), so each net direction admits a corner-exit template via Lemma `lem:corner-exit-template-open`.
  - **Small bookkeeping fix applied in TeX**: the proof now explicitly defines the uniform upper bound \(\alpha^*:=\max_i\alpha^*(i)\) (hence a finite \(\Lambda=\alpha^*/\alpha_*\)) before invoking `lem:corner-exit-template-open`.
  - **Packing-language fix applied in TeX**: the statement no longer claims an “arbitrarily long \(\delta\)-separated list for any fixed \(\delta>0\)”; it now states the correct form “length \(N(\delta)\to\infty\) as \(\delta\downarrow 0\)”.
  - The proof correctly notes that no uniform-in-\(h\) lower bound for \(\alpha_*(h)\) is claimed; instead the later schedule keeps dependence on \((1+A_*(h))\Lambda(h)\) explicit and enforces the corner-exit scale restriction.
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Remark `rem:corner-exit-direction-net` — Supplying corner-exit template families for the direction net
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 5408
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Lemma `lem:cube-vertex-slice-boundary` — Corner-exit simplex slices have optimal boundary scaling
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 5433
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Proposition `prop:vertex-template-mass-matching` — Vertex-template prefix lengths match local mass budgets (L2, cube model)
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 5471
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Proposition `prop:vertex-template-face-edits` — Vertex templates $\Rightarrow$ face-level $O(h)$ edit regime (hypothesis \textnormal{(iv)})
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 5542
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Corollary `cor:corner-exit-iii-iv` — Corner-exit vertex templates verify the activation hypotheses (iii)–(iv)
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 5605
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Remark `rem:L1-downstream-map` — {\color{blue}Referee map: downstream invocations of Proposition~\ref{prop:holomorphic-corner-exit-L1}}
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 5662
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Proposition `prop:global-coherence-all-labels` — Global coherence across all direction labels (B1, packaged)
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 5680
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Corollary `cor:raw-boundary-flat-small` — Flat boundary of the raw current in the weighted scaling regime
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 5769
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Remark `line-5823` — Making the ``prefix-balanced face population'' explicit
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 5823
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Definition `def:checkerboard-anchoring` — Cubical grid parity and checkerboard vertex anchoring
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 5831
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Definition `def:block-uniform-codes` — Block-uniform vertex-code sequence
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 5844
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Lemma `lem:prefix-discrepancy` — Prefix discrepancy for block-uniform codes
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 5852
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Lemma `lem:two-sided-face-pop` — Two-sided face population is automatic under checkerboarding
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 5896
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Proposition `prop:checkerboard-face-oh-edit` — Checkerboard corner assignment implies a face-level $O(h)$ edit regime
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 5924
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Remark `rem:smooth-cells` — Rounded cubes
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 6007
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Remark `rem:bergman-not-enough` — Where the remaining analytic difficulty really lives
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 6014
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Lemma `lem:global-graph-contraction` — Global quantitative graph lemma (contraction criterion)
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 6026
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Remark `rem:graph-whole-cell` — Memorializing the new checkpoint: ``graph on the whole cell''
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 6106
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Lemma `lem:bergman-affine-approx-hormander` — Bergman-scale affine model approximation via $\bar\partial$-solving
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 6148
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Proposition `prop:cell-scale-linear-model-graph` — \editamir{Cell-scale linear-model complete intersections are single-sheet graphs}
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 6178
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Lemma `lem:ball-excludes-faces` — Vertex-ball locality excludes nonincident faces
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 6259
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Lemma `lem:corner-simplex-hits-designated-faces` — {\color{blue}Fat corner simplices force ``if'' on the designated exit faces}
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 6275
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Lemma `lem:corner-simplex-face-mass` — {\color{blue}Uniform per--face boundary mass for fat corner simplices}
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 6317
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Lemma `lem:small-graph-distortion` — Small-slope graph distortion on $k$-- and $(k\!-\!1)$--areas
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 6369
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Proposition `prop:holomorphic-corner-exit-g1g2-old1` — {\color{blue}Corner--exit footprint geometry is preserved under small--slope holomorphic graphs}
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 6216
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - This is an older/draft variant kept for traceability; the main live statement used downstream is `prop:holomorphic-corner-exit-g1g2`.
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Proposition `prop:holomorphic-corner-exit-g1g2-old2` — {\color{blue}Corner--exit footprint geometry for small--slope graphs}
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 6257
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - This is an older/draft variant kept for traceability; the main live statement used downstream is `prop:holomorphic-corner-exit-g1g2`.
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Proposition `prop:holomorphic-corner-exit-g1g2` — {\color{blue}Corner--exit footprint geometry for small--slope graphs}
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 6320
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - **Hygiene fix applied**: the TeX had multiple back-to-back proof environments here (draft variants). It has been cleaned to a single proof plus a short “referee cleanup” note.
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Corollary `cor:holomorphic-corner-exit-inherits` — {\color{blue}Corner--exit faces persist uniformly across a finite template family}
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 6660
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Remark `rem:rs-interpretation` — Recognition Science interpretation (updated)
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 6697
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Lemma `lem:sliver-stability` — Sliver stability under $C^1$-graph perturbations
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 6716
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Lemma `lem:sliver-packing` — Packing bound for disjoint sliver graphs
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 6777
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Proposition `prop:finite-template` — Realizing a finite translation template locally
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 6800
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Proposition `prop:holomorphic-corner-exit-L1` — {\color{blue}Corner--exit: $L^1$ interface mass control on boundary faces}
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 6840
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Proposition `prop:holomorphic-corner-exit-L1` — {\color{blue}Corner--exit: $L^1$ interface mass control on boundary faces}
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 6899
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Remark `rem:vertex-star-coherence` — Vertex-star coherence (how to make the same template live across adjacent cubes)
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 6965
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Lemma `lem:slow-variation-rounding` — Slow variation under rounding of Lipschitz targets
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 6980
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Lemma `lem:slow-variation-discrepancy` — Slow variation persists under $0$--$1$ discrepancy rounding
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 7013
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Lemma `lem:flatnorm-gluing-mismatch` — Flat-norm control of the gluing mismatch
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 7057
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Remark `rem:lean-bottleneck-flatnorm` — Referee note: this is the quantitative bottleneck
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 7080
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Lemma `lem:FF-filling-X` — Federer--Fleming filling on $X$ for bounding cycles
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 7090
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Proposition `prop:glue-gap` — Microstructure/gluing estimate
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 7133
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Remark `rem:glue-scaling` — Choosing the glue scale to make the correction negligible
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 7173
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Lemma `lem:barany-grinberg` — Fixed-dimension discrepancy rounding (B\'ar\'any--Grinberg)
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 7219
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Remark `line-7266`
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 7266
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Lemma `lem:integral-periods` — Integral periods of integral cycles
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 7322
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Lemma `lem:lattice-discreteness` — Lattice discreteness
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 7342
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Proposition `prop:cohomology-match` — Integral cohomology constraints
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 7354
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - The internal “Step 5” construction of the tiny-mass boundary correction inside the proposition proof was **removed** (it duplicated the immediately-following subsection “Step 5: Boundary correction with vanishing mass”). The proposition now cleanly points to that subsection for existence/estimates of \(U_\epsilon\).
  - The intended \(\tfrac14+\tfrac14<\tfrac12\) budget is explicit:
    - mesh refinement makes each marginal vector \(v_{Q,j}=(\int_{Z_{Q,j}}\Theta_\ell)_\ell\) uniformly tiny so B\'ar\'any--Grinberg gives a \(\le 1/8\) rounding error in each period;
    - the filling \(U_\epsilon\) is chosen so \(\Mass(U_\epsilon)\cdot\max_\ell\|\Theta_\ell\|_{C^0}<1/4\), hence \(|\int_{U_\epsilon}\Theta_\ell|<1/4\) for all \(\ell\);
    - integrality + “within \(1/2\)” locks the periods exactly.
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Proposition `prop:almost-calibration` — Almost--calibration and global mass convergence for the glued cycles
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 7569
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Remark `rem:correction-not-positive` — The correction current need not be positive
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 7672
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Theorem `thm:syr-realization` — SYR Realization
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 7687
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Equation `eq:mass-lsc`
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 7750
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Corollary `cor:syr-limit-holomorphic-chain` — SYR limit is a holomorphic (hence algebraic) cycle
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 7812
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Remark `rem:density-mass` — The ``density vs.\ mass'' objection
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 7829
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Remark `rem:hl-applicable` — Harvey--Lawson applicability
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 7845
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Remark `rem:gluing` — The gluing/non-integrability objection
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 7873
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Remark `rem:why-success` — Why the construction succeeds
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 7919
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Theorem `thm:automatic-syr` — Automatic SYR for cone-valued forms
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 7948
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Definition `lem:kahler-positive` — Cone--positive class (smooth $K_p$--positive)
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 8009
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Lemma `lem:kahler-positive` — Strict interior positivity of the K\"ahler power
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 8016
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Lemma `lem:signed-decomp` — Signed Decomposition
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 8042
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Lemma `lem:gamma-minus-alg` — $\omega^p$ is algebraic
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 8080
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Theorem `thm:effective-algebraic` — Cone--positive classes are algebraic
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 8110
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Remark `rem:chow-gaga` — Chow/GAGA for analytic subvarieties
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 8132
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Theorem `thm:main-hodge` — Hodge Conjecture for rational $(p,p)$ classes
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 8143
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Corollary `cor:full-hodge` — Full Hodge conjecture
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 8192
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

##### Remark `line-8205` — Why signed decomposition is the key
- **TeX location**: `Hodge_REFEREE_Amir-v1.tex` line 8205
- **Referee status**:
  - [ ] Statement verified
  - [ ] Proof verified
  - [ ] Downstream use verified
- **Proof rewrite / verification notes**:
  - 
- **Dependencies / citations**:
  - 
- **Questions / potential gaps**:
  - 

