# MG / Global template coherence: multistep proof plan

**Goal.** Prove the remaining “microstructure/gluing” obstruction in the manuscript:

> Construct local holomorphic sheet/sliver families so that for every interior interface
> \(F = Q\cap Q'\) in the chosen cell decomposition, the induced face slices are **template-coherent** (or coherent up to tiny edits) *simultaneously across the full adjacency graph*, while still meeting the **barycenter** constraints (matching \(m\beta\)) and the **cohomology** constraints (correct periods after rounding).

This is exactly the global input needed to convert the local constructions into a raw current \(T_m^{\mathrm{raw}}\) with \(\mathcal F(\partial T_m^{\mathrm{raw}})=o(m)\), hence (by Federer–Fleming filling) a closed calibrated cycle with \(o(m)\) correction.

---

## Update (Dec 2025): corner-exit vertex templates collapse the “multi-face consistency” headache

The master manuscript now contains a cubical \*\*corner-exit / vertex-template\*\* route in which face matching is \*\*purely prefix-count bookkeeping at shared vertices\*\* (not a discrete tomography problem).

Concretely:

- **Local holomorphic manufacturing (L1)** is packaged as `prop:holomorphic-corner-exit-L1` + `rem:vertex-star-coherence` (the latter explains how to realize a single vertex template coherently across the entire vertex star).
- **Local mass matching (L2)** is packaged as `prop:vertex-template-mass-matching`.
- **Per-label activation (iii)–(iv)** is recorded as `cor:corner-exit-iii-iv`.
- **All-label B1 packaging** is recorded as `prop:global-coherence-all-labels` (direction-net restricted to corner-exit-admissible planes + Lipschitz weights + slow-variation rounding + cohomology rounding).

So the remaining “global coherence” work is now essentially: choose a direction dictionary/net and integer counts in a way compatible with the global cohomology rounding, and then verify the chosen parameter regime indeed drives \(\mathcal F(\partial T^{\mathrm{raw}})=o(m)\) (this is Target C in the proof plan).

---

## Status in `hodge-dec-6-handoff-sliverpath.tex` (what is already “done”)

As of the current sliverpath manuscript, the following components are essentially treated as established:

- **Ball-like/rounded cells at scale \(h\)**: `lem:rounded-cells` (\(C^2\) cells with curvature \(|\kappa_i|\le C/h\), in normal charts with \(1+O(h^2)\) distortion). The manuscript now treats this as “reduced to standard smoothing” rather than fully resolving the strict convexity requirement for the *strong* sliver boundary budget (which remains a technical part of B1).
- **Per-face displacement control**: `lem:face-map-variation` + `lem:template-displacement` (and the “small edits” variant `lem:template-displacement-edits`).
- **Local sliver realizability on one cell**: `prop:sliver-local` (built from the flat shell quantization `prop:flat-sliver-local-ball` plus the Bergman/finite-template holomorphic upgrade).
- **Global sliver bookkeeping once coherence holds**: `prop:weighted-sliver-glue`.
- **Discrete feasibility insight**: `lem:toy-marginals` (shows that matching marginals is trivial; the hardness of B1 is the linear mixing of templates by face maps).

So the remaining work is genuinely **Blocker B1**: enforce template coherence / simultaneous matching across the *entire* adjacency graph, while meeting barycenter + cohomology constraints.

## 0. What “success” must produce (checklist)

Fix \(m\to\infty\) and auxiliary parameters

- \(h=h(m)\downarrow 0\) (cell scale; typically \(h\asymp m^{-1/2}\) in the Bergman/sliver route),
- \(\delta=\delta(m)\downarrow 0\) (local barycenter / quantization tolerance),
- \(\varepsilon=\varepsilon(m)\downarrow 0\) (small-angle / \(C^1\) graph parameter for the holomorphic pieces),

and (implicitly) an error fraction \(\varepsilon_{\mathrm{glue}}(m;h,\delta,\varepsilon)\to 0\).

Success means we can build:

- A raw current \(T_m^{\mathrm{raw}}=\sum_Q S_{Q,m}\) built cellwise from holomorphic pieces (dense sheets or slivers).
- For each interior face \(F=Q\cap Q'\), a pairing of the face slices so that one of the following holds:
  - **Dense-sheet route (T1–T2)**: the induced transverse measures on \(F\) admit template representations satisfying Proposition `prop:template-flat-glue` hypotheses `(T1)–(T2)`.
  - **Sliver route (displacement + boundary budget)**: after pairing, the interface mismatch is controlled by Lemma `lem:template-displacement` (or `lem:template-displacement-edits`) and the per-cell boundary budget is controlled by Proposition `prop:sliver-boundary-budget`, so Proposition `prop:weighted-sliver-glue` applies.
- **Barycenter constraint**: \(\langle T_m^{\mathrm{raw}},\eta\rangle\approx m\int_X \beta\wedge\eta\) for all test forms \(\eta\) at the precision required for the later cohomology rounding step.
- **Cohomology constraint**: after adding the gluing correction \(R_{\mathrm{glue},m}\), the resulting closed current has periods equal to \(m[\gamma]\) (or is within \(<1\) of each integral period so the integer conclusion follows).

---

## 1. Fix the geometric “plumbing” once and for all

**Deliverables.** A uniform family of charts and face-tubular identifications so the face-slice maps \(\Phi_{Q,F}\) are defined and stable.

1. Choose a decomposition by **smoothly rounded** cells at diameter \(h\) (using `lem:rounded-cells` to get \(C^2\) regularity with curvature \(O(1/h)\)). *Note: If strict convexity is needed for the sharpest boundary budget, one must ensure the rounding preserves it or adapt the budget estimate to \(C^2\) domains.*
2. For each interior face \(F\), choose a tubular product chart of radius \(\asymp h\) compatible for the two neighboring cells.
3. Prove (or invoke) the geometric lemma giving
   \[\|\Phi_{Q,F}-\Phi_{Q',F}\|_{\mathrm{op}} = O(h)\]
   once the two sides use paired plane directions (cf. `lem:face-map-variation`).

**Why this matters.** It turns the global problem from “geometry” into “discrete combinatorics + holomorphic realization”.

---

## 2. Make the *direction field* globally consistent (pairing planes across the graph)

Even before translations/templates, we need a **globally compatible labeling** of the calibrated directions used in each cell.

**Objective.** For each cell \(Q\), choose a small list of calibrated directions \(\{P_{Q,j}\}_{j\le N(h)}\) and coefficients so that:

- \(\beta(x_Q)\) is approximated by the convex combination of \(\{P_{Q,j}\}\), with error \(o(1)\) as \(h\to 0\).
- For each neighbor \(Q'\) across \(F\), there is a pairing \(j\leftrightarrow j'\) such that
  \[\angle(P_{Q,j},P_{Q',j'}) = O(h).\]

**Plan.** Use a two-scale “stabilized discretization”:

- **(2.1) A fine direction net depending on \(h\).** Choose an \(\varepsilon_h\)-net \(\mathcal N_h\) in the calibrated Grassmannian with \(\varepsilon_h\ll h\). This avoids the finite-direction rigidity (the net size grows as \(h\to 0\)).
- **(2.2) Quantize \(\beta\) into \(\mathcal N_h\).** For each \(Q\), represent \(\beta(x_Q)\) as a convex combination of net directions (Carathéodory on the convex cone + nearest-net projection).
- **(2.3) Enforce neighbor stability.** Because \(\beta\) is smooth, \(\beta(x_Q)\) varies by \(O(h)\) across adjacent cells. Choose the convex decomposition by a *stable selection rule* (e.g. minimize an energy functional among decompositions) so the support directions vary only by \(O(h)\), yielding the desired pairing.

**What you need to prove.** A “stable Carathéodory selection” lemma: smooth variation in the target cone element implies existence of decompositions whose supporting extremals vary in a Lipschitz way across cells (possibly after enlarging support by a controlled amount).

**Alternative (preferred) route: fixed direction net + strongly convex coefficient selection.**

- Choose an \(\varepsilon_h\)-net \(\{P_1,\dots,P_M\}\) in the complex Grassmannian (so labels are global inside a chart).
- For each cell basepoint \(x_Q\), define the normalized dictionary \(\xi_i(x_Q)\) (generator of the ray corresponding to \(P_i\), normalized by \(\langle\xi_i,\psi\rangle=1\)).
- Choose weights by a **unique** strongly convex quadratic program on the simplex:
  \[
  w(x_Q)=\arg\min_{w\in\Delta_M}\ \frac12\Bigl\|\widehat\beta(x_Q)-\sum_i w_i\,\xi_i(x_Q)\Bigr\|^2+\frac{\lambda}{2}\|w\|^2.
  \]
- By `lem:lipschitz-qp-weights` + smoothness of \(\widehat\beta\), the weights vary Lipschitzly across adjacent cells, so neighbor pairing is **trivial** (same index \(i\)).

This route avoids the combinatorial instability of Carathéodory supports and converts Step 2 into a standard “dictionary approximation + Lipschitz weights” statement.

---

## 3. Reduce global face matching to a **discrete integer feasibility problem**

This is the right abstraction of “simultaneous face matching”: the face measures are not independent; each face sees a pushforward of the same cellwise template.

### 3A. Warmup: The "Toy Marginals" case

The manuscript now includes `lem:toy-marginals`, which shows that if the problem were just to match *coordinate projections* (marginals), it would be purely combinatorial and always solvable.
The difficulty in the real problem (Blocker B1) is that the face maps \(\Phi_{Q,F}\) are **nontrivial linear maps** that mix coordinates, turning the matching problem into a form of "discrete tomography" or "simultaneous pushforward" consistency.

### 3B. Fix discrete transverse grids

For each face \(F\) and each relevant direction family \((Q,j)\), fix:

- A transverse parameter domain \(\Omega_F\cong B^{2p}(0,c h)\).
- A grid of spacing \(\delta\ll h\) on \(\Omega_F\).

Define the **target density** \(\rho_F\) induced by \(m\beta\) on the face (the continuum “sheet-count density”).

### 3B. Desired output at the discrete level

For each oriented half-face (cell \(Q\) incident to \(F\)) we want an integer-weighted measure \(\mu_{Q\to F}\) on the transverse grid such that:

- \(W_1(\mu_{Q\to F}, \rho_F\,dy) \le C\,\delta\,\int \rho_F\).
- **Mass conservation:** \(\mu_{Q\to F}(\Omega_F)=\mu_{Q'\to F}(\Omega_F)\).
- (Dense regime) They come from a common template up to small edits; (Sliver regime) they come from common template after pairing most pieces.

This is the content of `prop:integer-transport` as a target reduction.

### 3C. Why this is still not enough

Even if we build \(\mu_{Q\to F}\) on every face, we still must realize them by **actual holomorphic pieces inside each cell**.
This forces a *multi-face consistency constraint*:

- For a fixed cell \(Q\) and direction \(j\), the measures \(\{\mu_{Q\to F}\}_{F\subset\partial Q}\) must be the pushforwards of a **single** discrete measure \(\nu_{Q,j}\) in \(P_{Q,j}^\perp\) by the face maps \(\Phi_{Q,F}\).

So the core combinatorial problem is:

> Given target face measures on all faces of \(Q\), find an integer measure \(\nu_{Q,j}\) whose pushforwards approximately match them.

### 3D. Practical construction strategy: choose cell templates first, then inherit face measures

The most robust way to avoid “incompatible face-by-face choices” is to **never choose the face measures \(\mu_{Q\to F}\) directly**.
Instead:

- Fix, for each (globally labeled) direction family \(j\), a **master translation template**
  \(\{t^{(j)}_a\}_{a\ge 1}\subset \R^{2p}\) (low-discrepancy / well-spread, supported in \(B_{C h}(0)\)).
- For each cell \(Q\), choose **only the integer multiplicities** \(N_{Q,j}\) (or per-shell multiplicities in the sliver regime).
- Define the cellwise template measures \(\nu_{Q,j}\) as truncations/edits of the master template, and define the face measures by pushforward:
  \[
  \mu^{(j)}_{Q\to F}:=(\Phi_{Q,F})_\#\nu_{Q,j}.
  \]

Then multi-face consistency inside each cell is automatic. Across a face \(F=Q\cap Q'\), the mismatch is controlled by:

- **face-map variation** \(\|\Phi_{Q,F}-\Phi_{Q',F}\|=O(h)\), and
- **small edits** in \(\nu_{Q,j}\leftrightarrow \nu_{Q',j}\) (insertions/deletions) coming only from slow variation of \(N_{Q,j}\).

So B1 reduces to: construct globally labeled directions \(j\) (Step 2) and choose integer multiplicities \(N_{Q,j}\) satisfying
(i) barycenter constraints, (ii) cohomology constraints, and (iii) Lipschitz/slow-variation constraints on the adjacency graph.

---

## 4. Prove global coherence in the **dense-sheet (fixed template) route**

This route aims to verify `(T1)–(T2)` in `prop:template-flat-glue`.

### 4A. Use global “master templates” and only vary *how many points you take*

For each direction label \(j\) (now globally stabilized from Step 2), fix once and for all a master low-discrepancy sequence
\(\{t^{(j)}_a\}_{a\ge 1}\subset \R^{2p}\) supported in a ball of radius \(O(h)\).

For each cell \(Q\), define
\[\nu_{Q,F}^{(j)} := \sum_{a=1}^{N_{Q,j}} \delta_{t^{(j)}_a}\]
independently of \(F\). Then define the face measures by
\[\mu_{Q\to F}^{(j)} := (\Phi_{Q,F})_\#\nu_{Q,F}^{(j)}.\]

This automatically builds **same-template structure** across all faces of a given \(Q\).

**Concrete nested template source.** If you want a single ordered template with good “prefix” behavior, the master manuscript now contains
`lem:sphere-quantize-nested`, which builds an infinite sequence on a sphere whose every prefix approximates the uniform sphere measure in \(W_1\);
after scaling this gives a canonical nested ordered template inside \(B_{Ch}(0)\subset\R^{2p}\).

### 4B. Show `(T2)` (slowly varying multiplicities) is forced by smoothness

Prove that
\[|N_{Q,j}-N_{Q',j}| \le C\,h\,N_F\]
for neighbors \(Q,Q'\) across \(F\), because the target densities derived from \(m\beta\) vary Lipschitzly at scale \(h\).

This gives `(T2)` (insert/delete only \(r_F=O(hN_F)\) atoms).

**Note (now packaged in the master).** The “edits are harmless” bookkeeping is now explicit in `hodge-SAVE-dec-12-handoff.tex`:
`rem:nested-template-scheme`, `rem:bounded-corrections`, and `prop:prefix-template-coherence` show that once $N_{Q,j}\gtrsim h^{-1}$,
bounded cohomology corrections and the $O(h)$ relative neighbor variation only create an $O(h)$ fraction of edits, hence an $O(h^2)$ flat-norm contribution.

### 4C. Show `(T1)` (same template up to face-map variation)

Using Step 1, ensure the face maps satisfy
\(\|\Phi_{Q,F}-\Phi_{Q',F}\|=O(h)\).
Then `lem:w1-auto` gives automatic face matching at scale \(h^2 N_F\).

**Note (now packaged in the master).** The per-face conversion from “same template + face-map variation” to an explicit flat-norm mismatch bound is
recorded as `lem:template-displacement` (and the edits version `lem:template-displacement-edits` + `lem:template-edits-oh`) in `hodge-SAVE-dec-12-handoff.tex`.

### 4D. Integrate with barycenter + cohomology constraints

- **Barycenter:** Choose the integer counts \(N_{Q,j}\) so that the sum of the associated calibrated directions matches \(m\beta\) at scale \(o(1)\) per cell.
- **Cohomology rounding:** Use the fixed-dimensional discrepancy lemma (Bárány–Grinberg) to adjust the \(N_{Q,j}\) by \(O(1)\) per direction family while keeping the total cohomology periods within \(<1/2\).

**Key compatibility lemma (now essentially done in the master).**
The rounding adjustments can be implemented so that adjacent-cell count differences remain \(O(hN_F)\):

- The global period constraints are handled by fixed-dimensional discrepancy rounding (Bárány–Grinberg), as in `prop:cohomology-match`.
- The local slow-variation bound survives *any* $0$–$1$ rounding by `lem:slow-variation-discrepancy` (blue) in `hodge-SAVE-dec-12-handoff.tex`,
  since \(|N_{Q,j}-N_{Q',j}|\le |n_{Q,j}-n_{Q',j}|+2\) for neighbors.

So the remaining work in Step 4D is bookkeeping/integration with the template scheme, not a new graph-discrepancy theorem.

- Input: real targets \(a_{Q,j}\) with Lipschitz variation in \(Q\).
- Output: integers \(N_{Q,j}\) such that (i) \(N_{Q,j}\approx a_{Q,j}\), (ii) global linear constraints (periods) are met up to \(O(1)\), and (iii) \(|N_{Q,j}-N_{Q',j}|\le C h a_{F,j}\).

(\emph{Historical note:}) A two-stage “round then correct by circulations” proof is another viable route, but is no longer necessary given the lemma above.

---

## 5. Prove global coherence in the **sliver (Bergman-scale) route**

This route aims to verify the hypotheses of `prop:weighted-sliver-glue`.

### 5A. Local existence: realize any transverse density by many tiny pieces

On each Bergman-scale cell \(Q\) (diameter \(\asymp m^{-1/2}\)), use the packaged local result `prop:sliver-local` (which subsumes the flat shell
quantization and its holomorphic upgrade). This gives many holomorphic pieces with individually tiny mass and an induced transverse measure
approximating the target density.

### 5B. Global matching: enforce face coherence by “pair most, edit the rest”

Across each face \(F=Q\cap Q'\), implement:

- **Matched bulk:** Pair the majority of slivers so that the matched parts use the same template and differ only by the \(O(h)\) face-map variation.
  Then Lemma `lem:template-displacement` controls the flat-norm mismatch at scale \(h^2\times(\text{boundary mass})\).
- **Unmatched remainder:** Allow a small number of unpaired slivers whose boundary slices are tiny; use Lemma `lem:template-displacement-edits` + `rem:template-edits` to show their flat-norm cost is still of the same order and can be absorbed.

### 5C. Keep cohomology/barycenter constraints by reallocating **tiny** slivers

Because slivers can be made arbitrarily small, you can correct global periods by adding/removing a very small set of slivers whose total mass is \(o(m)\), without materially affecting the face mismatch estimate.

**Key lemma to prove.** A “cohomology correction by negligible slivers” statement:

- Construct a library of “basis slivers” supported in controlled locations whose pairings against the harmonic basis \(\{\eta_\ell\}\) span \(\Z^b\) (or approximate it up to bounded error).
- Adjust periods by adding/removing \(O(1)\) such basis slivers per period constraint.
- Show the induced extra boundary mismatch remains \(o(m)\) because each correction sliver is tiny and the mismatch is controlled by `lem:flat-diameter`.

This is the main advantage of the sliver regime: it decouples “degrees of freedom for rounding” from “mass budget”.

---

## 6. Close the loop: from global coherence to MG

Once Step 4 (dense route) or Step 5 (sliver route) is achieved:

1. Apply `prop:template-flat-glue` (dense) or `prop:weighted-sliver-glue` (sliver) to obtain
   \[\mathcal F(\partial T_m^{\mathrm{raw}})=o(m).\]
2. Apply the flat-norm decomposition + Federer–Fleming isoperimetry to build
   \(R_{\mathrm{glue},m}\) with \(\Mass(R_{\mathrm{glue},m})=o(m)\).
3. Set \(T_m=T_m^{\mathrm{raw}}+R_{\mathrm{glue},m}\). Then \(T_m\) is closed, calibrated, integral, with correct mass scale.
4. Use the existing cohomology rounding section to ensure \([T_m]=\mathrm{PD}(m[\gamma])\).

---

## 7. Suggested “minimal theorem package” to target next

To make progress fast, aim to prove (or formalize as explicit hypotheses) these three intermediate statements.

1. **Stable direction discretization lemma (Step 2):** existence of decompositions with neighbor-pairable directions.
2. **Graph-Lipschitz discrepancy rounding lemma (Step 4D):** enforce period constraints without breaking slow variation.
3. **Global face matching construction lemma (Step 4A–4C or Step 5B):** build templates/edits so that *all* faces satisfy coherence simultaneously.

If you can land these, MG becomes a theorem rather than a hypothesis.
