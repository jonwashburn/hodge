## AI Referee Notes — *Calibration–Coercivity and the Hodge Conjecture* (Amir v1)

**Scope**: This document is an **AI-assisted referee pass** over the proof spine as organized in
`docs/referee/Hodge_REFEREE_Amir-v1_REFEREE_WORKBOOK.md`.

**Important limitation**: This is **not** a certification of correctness. It is a structured set of
checks, risk areas, and “where the real work is,” intended to accelerate a human referee-team audit.

---

### Proof spine (what the paper is claiming, mechanically)

The logical chain used in the manuscript (also recorded in the TeX “Referee packet”) is:

1. **Main theorem** `thm:main-hodge`
2. Hard Lefschetz reduction `rem:lefschetz-reduction`
3. Signed decomposition `lem:signed-decomp` + algebraicity of `γ⁻` via `lem:gamma-minus-alg`
4. Cone–positive ⇒ algebraic `thm:effective-algebraic`
5. Automatic SYR `thm:automatic-syr`
6. Spine theorem (quantitative almost-mass-minimizing cycles) `thm:spine-quantitative`
7. Closure from almost-calibrated sequences `thm:realization-from-almost`
8. Harvey–Lawson + King ⇒ holomorphic chain; Chow/GAGA ⇒ algebraic subvarieties (`rem:chow-gaga`)

My review below follows this order.

---

### (A) Main theorem `thm:main-hodge` (TeX ~8143)

**What the proof does**: Reduces to `p ≤ n/2` (Hard Lefschetz), writes
\(\gamma = \gamma^+ - \gamma^-\) with \(\gamma^-=N[\omega^p]\), then uses:

- `lem:gamma-minus-alg` to make \([\omega^p]\) algebraic
- `thm:effective-algebraic` to make \(\gamma^+\) algebraic
- algebraic classes form a \(\mathbb Q\)-vector space ⇒ difference is algebraic

**Checks**:
- Confirm that “algebraic classes form a \(\mathbb Q\)-vector subspace” is stated with the right conventions
  (cycle class map linearity; rational coefficients).
- Confirm that the manuscript’s definition of “algebraic class” matches the Annals-standard one:
  image of cycle class map with \(\mathbb Q\)-coefficients.

---

### (B) Hard Lefschetz reduction `rem:lefschetz-reduction` (TeX ~4868)

**What it claims**: For \(p>n/2\), any rational \((p,p)\) class \(\gamma\) can be written as
\(\gamma=[\omega]^{2p-n}\wedge \eta\) where \(\eta\) is a rational \((n-p,n-p)\) class; if \(\eta\) is algebraic then so is \(\gamma\)
by intersecting with hyperplanes.

**Checks**:
- Ensure the invoked Hard Lefschetz statement preserves **rationality** and **Hodge type** under the inverse map.
- Ensure the “intersection with generic hyperplanes” argument is written with correct codimension counts:
  codim\((Z)\)=\(n-p\) then intersect with \(2p-n\) hyperplanes ⇒ codim \(p\).
- Ensure the dependence on projectivity is correctly placed (hyperplane class is algebraic; generic hyperplanes exist).

---

### (C) Signed decomposition `lem:signed-decomp` (TeX ~8042)

**What it does**: Given a smooth closed \((p,p)\) representative \(\alpha\) of \(\gamma\),
choose a **uniform interior radius** \(r_0\) with \(B(\omega^p(x),r_0)\subset K_p(x)\),
then choose rational \(N>M/r_0\) where \(M=\sup_x\|\alpha(x)\|\). Conclude
\(\alpha+N\omega^p\) is pointwise in \(K_p\).

**Checks**:
- Verify `lem:kahler-positive` really proves the *uniform* interior radius across compact \(X\).
- Verify the chosen norm \(\|\cdot\|\) on \(\Lambda^{p,p}T_x^*X\) is fixed and consistent with the cone-ball statement.
- Confirm “cone–positive” requires **closedness** of the representative (it is, since \(\alpha\) closed and \(\omega\) Kähler).

---

### (D) Algebraicity of \([\omega^p]\): `lem:gamma-minus-alg` (TeX ~8080)

**What it does**: Uses very ample powers \(L^{\otimes m}\) and Bertini to produce a smooth complete intersection
of codimension \(p\) with class \(c_1(L^{\otimes m})^p = m^p c_1(L)^p\).

**Checks**:
- Confirm the precise Bertini hypothesis needed for *iterated* generic intersections is satisfied.
- Confirm the Poincaré duality / cycle class normalization:
  \(\mathrm{PD}([Z]) = c_1(\mathcal O(D_1))\smile\cdots\smile c_1(\mathcal O(D_p))\).
- Confirm all coefficients are in \(\mathbb Q\) exactly as used downstream.

---

### (E) Closure principle: `thm:realization-from-almost` (TeX ~2450)

This is one of the cleanest, most “standard GMT + calibration” steps.

**What it does**:
- Fixes class \(A=\mathrm{PD}(m[\gamma])\) and assumes cycles \(T_k\) with fixed class and defect
  \(\Mass(T_k)-\langle T_k,\psi\rangle\to 0\).
- Uses Federer–Fleming compactness (flat convergence subsequence).
- Uses lower semicontinuity of mass + comass inequality to get
  \(\Mass(T)=\langle T,\psi\rangle\).
- Uses Harvey–Lawson/Wirtinger equality ⇒ complex tangent planes ⇒ positivity of bidimension \((p,p)\).
- Uses King (or equivalent) ⇒ holomorphic chain.

**Checks**:
- Confirm the **exact** version of mass lower semicontinuity used (flat or weak convergence) matches the convergence mode asserted.
- Confirm the comass inequality is stated for the current pairing conventions used.
- Confirm the King/HL hypotheses: “positive \(d\)-closed *locally integral* \((p,p)\)-current ⇒ analytic cycle.”

**Editorial risk**:
- In the TeX source, `lem:limit_is_calibrated` appears to have an additional proof block that looks specialized
  (fixed homology class) and may not match the lemma’s stated hypotheses. This should be cleaned before submission
  to avoid confusion.

---

### (F) SYR definition + theorem: `def:syr`, `thm:syr` (TeX ~2657, ~2685)

**What SYR is**: A *black-box stationarity/compactness* condition:
existence of a fixed-class integral cycle sequence \(T_k\) with calibration defect → 0.

**What `thm:syr` does**: Applies `thm:realization-from-almost` to obtain an actual calibrated limit \(T\),
then invokes HL/King/Chow-GAGA to conclude algebraicity (on projective \(X\)).

**Checks**:
- Ensure the passage “\(\psi\) closed + fixed homology class ⇒ \(\langle T_k,\psi\rangle\) constant” is correct
  in the torsion-quotiented setting actually used.
- Ensure torsion-handling is explicit where needed (the manuscript often works in \(H_\*(X;\mathbb Z)/\mathrm{Tor}\)).

---

### (G) Automatic SYR: `thm:automatic-syr` (TeX ~7948)

This is the “big theorem” that the microstructure/gluing construction exists and supplies SYR.

**What the proof relies on (as written)**:
- A raw integral current \(S_\epsilon\) built from locally calibrated holomorphic sheets
  (so locally \(\Mass=\langle\cdot,\psi\rangle\)).
- A gluing correction \(U_\epsilon\) with \(\partial U_\epsilon=\partial S_\epsilon\) and \(\Mass(U_\epsilon)\to 0\).
  (This comes from `prop:glue-gap` fed by small flat boundary.)
- Exact cohomology class enforcement via `thm:global-cohom` + `prop:cohomology-match`.
- Almost-calibration estimate `prop:almost-calibration` giving
  \(\Def_{\mathrm{cal}}(T_\epsilon)\le 2\Mass(U_\epsilon)\to 0\).
- Then `thm:syr` converts SYR to a calibrated holomorphic chain.

**High-risk zones (where most referee time will go)**:
- The face-mismatch ⇒ flat-norm control mechanism (transport estimates; \(W_1\) coupling; “template edits”)
- The period/rounding scheme that enforces global homology constraints while preserving local budgets and keeping corrections small
- Uniformity and quantifier order in the parameter schedule

---

### (G.1) Transport ⇒ flat norm: `prop:transport-flat-glue`, `prop:transport-flat-glue-weighted`, `lem:uniformly-convex-slice-boundary`

This is the **quantitative hinge** that makes the “glue correction has vanishing mass” step work.

**What the manuscript’s interface is**:

- `prop:transport-flat-glue` (unweighted) turns a facewise \(W_1\) coupling bound into a flat-norm mismatch bound,
  *plus* an explicit “small-angle model error” term.
- `prop:transport-flat-glue-weighted` is the sliver-compatible version: it bounds mismatch by
  displacement \(\times\big(\Mass(\Sigma)+\Mass(\partial\Sigma)\big)\) and then uses geometric inequalities to relate slice-boundary mass to interior mass.
- `lem:uniformly-convex-slice-boundary` is the key convex-geometry inequality used to convert “boundary size” into a power of “volume”.

**Referee checks worth doing explicitly**:

- **Homotopy formula constants** (in `prop:transport-flat-glue`):
  - Re-derive the estimate
    \(|f_\eta(y')-f_\eta(y)|\le \|y'-y\|(\Mass(\Sigma_y)+\Mass(\partial\Sigma_y))\)
    from the Federer/Fleming–style homotopy formula, and check exactly what regularity of the homotopy is required.
  - Confirm the scaling \(\Mass(\Sigma_y)\sim h^{k-1}\), \(\Mass(\partial\Sigma_y)\sim h^{k-2}\) in the relevant product chart.
    (The boundary term is larger pointwise, but is multiplied by a translation distance \(\|y'-y\|\sim h\), giving overall \(h^{k-1}\).)
- **Kantorovich–Rubinstein duality conditions**:
  - Verify the “same total mass” condition on the two face transverse measures is truly satisfied at the point of use
    (this is exactly where the “prefix balancing / integer transport” machinery is invoked).
  - Confirm the metric used in \(W_1\) matches the Lipschitz constant computed for \(f_\eta\).
- **Small-angle/model error term**:
  - Check the invocation of the flat-norm stability lemma under small \(C^0\) deformations (`lem:flat-C0-deform`) and the dependence on \(\varepsilon h\).
  - Verify the global summation in the final estimate matches the chosen schedule so this term is \(o(1)\) (or \(o(m)\) in the scaled regime).
- **Weighted (sliver) regime**:
  - In `prop:transport-flat-glue-weighted`, verify the decomposition \(B_F=R+\partial Q\) produced by `lem:flat-translate` is integral and that the mass bound is sharp enough for later summations.
  - Check exactly how \(b_F\) (uniform upper bound on \(\Mass(\Sigma)+\Mass(\partial\Sigma)\)) is produced from the corner-exit geometry + graph distortion.
- **Uniformly convex slice-boundary inequality** (`lem:uniformly-convex-slice-boundary`):
  - Confirm the precise convexity hypotheses (uniform curvature bounds scaled like \(1/h\)) are met by the chosen “rounded cubes/cells”.
  - Verify the reduction to a \(k\)-dimensional convex body \(K_t\subset\mathbb R^k\) and the use of the isoperimetric inequality
    giving \(a(t)\lesssim v(t)^{(k-1)/k}\), with constants uniform in \(t\).

---

### (H) Gluing correction bound: `prop:glue-gap` + isoperimetric lemma (TeX ~7090–7169)

**What it does**:
From \(\delta=\mathcal F(\partial T^{\mathrm{raw}})\), decomposes \(\partial T^{\mathrm{raw}} = R_0 + \partial Q\),
fills \(R_0\) via a Federer–Fleming / Euclidean isoperimetric inequality, and obtains
\(\Mass(R_{\mathrm{glue}})\le \delta + C_X\delta^{k/(k-1)}\).

**Checks**:
- Confirm the **integral flat norm** definition used is correct and matches later use.
- Confirm the Nash embedding + tubular projection argument does not lose integrality and keeps constants controlled.

---

### (I) Period locking / exact class: `prop:cohomology-match` (TeX ~7354)

**What it does**:
- Uses a fixed integral cohomology basis \(\{\Theta_\ell\}\).
- Makes each marginal “one extra sheet” contribution vector \(v_{Q,j}\) small by taking mesh small.
- Uses Bánary–Grinberg discrepancy rounding to choose \(\varepsilon_{Q,j}\in\{0,1\}\) so that all periods are close to targets.
- Uses a small-mass boundary correction \(U_\epsilon\) to make the current closed without spoiling period accuracy.
- Uses integrality of \(\int_{T_\epsilon}\Theta_\ell\) + “within 1/2 of an integer” to lock it exactly.

**Checks**:
- Verify the scaling/mesh argument that makes \(\|v_{Q,j}\|_{\ell^\infty}\) uniformly tiny is complete and uniform in all indices.
- Verify the “targets” \(\int_{S^{\mathrm{frac}}}\Theta_\ell\) are within \(1/8\) of \(mI_\ell\) simultaneously (this uses earlier bookkeeping accuracy).
- Verify existence of \(U_\epsilon\) with the claimed small mass is actually available under the schedule
  (this depends on small \(\delta=\mathcal F(\partial S)\), then `prop:glue-gap`).

---

### (J) Almost-calibration: `prop:almost-calibration` (TeX ~7569)

This is clean once the gluing mass tends to zero and the class is fixed.

**What it proves**: If \(T_\epsilon=S-U_\epsilon\) and \(\Mass(U_\epsilon)\to 0\), then
\(0\le \Def_{\mathrm{cal}}(T_\epsilon)\le 2\Mass(U_\epsilon)\to 0\).

**Editorial risk**:
- The TeX includes what looks like **two proofs** of this proposition back-to-back; that should be cleaned for submission.

---

### Immediate editorial/hygiene issues to fix before a serious referee pass

1. **Duplicate LaTeX labels**: earlier drafts contained duplicate `\label{...}` identifiers (often inside deprecated `\iffalse` blocks).
   These should be renamed/standardized before submission so the source is unambiguous to referees and to `hyperref`.
2. **Multiple proof blocks** for some results (notably around `lem:limit_is_calibrated` and `prop:almost-calibration`).
   Even if logically harmless, this is a referee-readability problem.
3. Ensure the “referee patch” blocks (`editamirblock*`) don’t accidentally leave contradictory or obsolete text visible in the final compiled PDF.

---

### Suggested next human referee moves (highest ROI)

If you want the fastest path to “Annals-ready confidence,” I’d prioritize:

1. **Transport ⇒ flat norm estimate**: the quantitative heart (look for `prop:transport-flat-glue*` and its weighted variants).
2. **Global coherence across labels**: `prop:global-coherence-all-labels` and the “simultaneous matching hinge.”
3. **Holomorphic manufacturing**: ensure the Bergman/peak-section inputs are precisely stated with constants and domains.
   - Update from this audit: `lem:bergman-control` had a scaling typo in the kernel-differentiation normalization; it was corrected in the TeX from \(N^{-(n+1)/2}\) to \(N^{-(n+1/2)}\) so that the produced \(1\)-jets are \(O(1)\) on \(N^{-1/2}\)-balls.
4. **Exact-class enforcement**: read `thm:global-cohom` and `prop:cohomology-match` end-to-end and redo the rounding argument.
5. **Parameter schedule sanity**: verify quantifier order and compatibility of all \(o(\cdot)\), \(\ll\), and “choose \(j\) large enough” steps.



