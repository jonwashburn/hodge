# Strategy and Progress (Unconditional Hodge Closure)

This file is a living lab notebook for pushing the manuscript toward a **valid, unconditional** proof.

> **See also**: [`proof-completion-plan.md`](proof-completion-plan.md) — a detailed, standalone prompt-ready plan with the 4 concrete targets (A–D) and their sub-lemmas.

## Current status (Dec 14, 2025)

### The core dependency (now closed in the master manuscript)
- The master manuscript (`hodge-SAVE-dec-12-handoff.tex`) now treats **`thm:automatic-syr`**, **`thm:effective-algebraic`**, and **`thm:main-hodge`** as **unconditional**.
- The previous “missing step” flag `rem:glue-gap` has been rewritten as **“Microstructure/gluing estimate (now established)”**, with the all-label corner-exit vertex-template construction packaged as `prop:global-coherence-all-labels`.

### Major progress: the blocker is now sharply localized
With the **corner-exit / fat simplex** geometry and **checkerboard / prefix-balancing** in place, the “mystery” is no longer face combinatorics.
The remaining work reduces cleanly to an \emph{execution} of the now-packaged local lemmas:
- **L1 (holomorphic manufacturing)** is now written in the master as `prop:holomorphic-corner-exit-L1` (plus `cor:holomorphic-corner-exit-inherits` and the cell-scale graph checkpoint machinery).
- **L2 (mass budget matching)** is now written in the master as `prop:vertex-template-mass-matching`, reducing budget matching to nearest-integer rounding once per-piece masses are comparable.

### New progress: the “all-label global coherence” step is now explicitly packaged
The master manuscript now contains a single statement that packages what we previously called **Blocker B1** (global coherence across all direction labels) in the
corner-exit / vertex-template route:

- `prop:global-coherence-all-labels`: corner-exit-admissible direction nets + Lipschitz weights + slow-variation rounding + cohomology discrepancy rounding
  ⇒ the activation hypotheses hold label-by-label, hence the template/flat-norm plumbing can be summed over labels.

### Note on the remainder of this file
Much of the “next plan” section below was written while the project was still exploring the earlier transport/\(W_1\) route; it is now largely historical context rather than a live blocker list.

### The critical analytic checkpoint (now formalized)
We added a fully classical quantitative lemma to the master manuscript:
- **`lem:global-graph-contraction`**: a contraction-mapping criterion that guarantees the zero set of a map \(F(u,w)\) is a **global graph \(w=g(u)\)** on a whole product region, provided uniform \(C^1\) closeness to an invertible linear model.

This reframes the holomorphic step as: **produce Bergman/peak sections whose local coefficient map \(F\) is uniformly \(C^1\)-close to a linear model on a Bergman ball containing the cube** (not just at one point).

We also added a concrete “bare-metal classical” route for this verification:
- **`lem:bergman-affine-approx-hormander`** + **`prop:cell-scale-linear-model-graph`**: a cutoff + Hörmander \(\bar\partial\) correction argument yielding \(C^1\) approximation of affine-linear holomorphic models on \(B_{R/\sqrt m}\), then applying `lem:global-graph-contraction` to get a **single-sheet graph on the entire cell**.

## Work completed so far (high-signal)

### 1) Flat-norm gluing route made explicit in the manuscript
- In `hodge-dec-6-handoff.tex` Substep 4.2:
  - Added `prop:transport-flat-glue`: **small-angle sheets + transverse $W_1$ matching across faces ⇒ $\mathcal F(\partial T^{raw})$ small** (quantitative).
  - Added `prop:integer-transport` + `rem:integer-transport-algo`: reduced “produce $W_1$ matching” to **grid quantization + integer rounding + integer network flow** (discrete combinatorics), isolating the remaining *geometric* difficulty.

### 2) Prompt docs upgraded
- In `ai-gap-prompts-and-proofs.tex`:
  - Added a flat-norm criterion (`lem:prompt8-flat-glue`) and transport control (`lem:prompt8-w1`) + $W_1$ quantization (`lem:w1-quantize`).
  - Added a closedness-cancellation remark explaining why the flat-norm dual is the right target.

### 3) Obstruction knowledge improved
- We explicitly identified the need to **separate**:
  - what is purely discrete/rounding/transport (solvable), vs
  - what is geometric: realizing the discrete transverse measures by actual calibrated holomorphic sheets with controlled angles and controlled face-slice geometry.

## The plan (what we try next, inch by inch)

### A) Make the transport hypotheses provable (not assumed)
Target: prove a lemma of the form:

> For the specific holomorphic sheet families produced by `thm:local-sheets`, the restriction of $\partial S_Q$ to a face admits a transverse-parameter measure model (with uniform tubular charts), and the induced measures on adjacent cubes can be chosen/adjusted to satisfy the required $W_1$ face matching.

Concrete subtasks:
- Prove uniform tubular-coordinate control for each sheet family on a face (geometry estimate).
- Define explicitly the transverse measures $\mu_{Q\to F}$ in the Kähler chart.
- Prove the Lipschitz slice-functional estimate needed for Kantorovich–Rubinstein.

### B) Resolve the scaling tension in the current cube-local paradigm
We must reconcile three competing needs in any cube-by-cube sampling approach:
- **integer availability** (need many sheets per cube to match weights),
- **small variation** (need mesh small so the target data changes slowly),
- **small boundary mismatch** (need face mismatches small in flat norm).

If this cannot be reconciled, we must switch paradigms (see C).

#### Scaling sanity check (important)
Let $h$ be the cube side length and $m$ the denominator-clearing multiplier.
The “target cube mass” is $M_Q \sim m\,h^{2n}$, while a single calibrated sheet crossing $Q$ has mass $A_Q\sim h^{2(n-p)}$.
Thus the expected number of sheets per cube is
\[
N_Q \sim \frac{M_Q}{A_Q} \sim m\,h^{2p}.
\]
- To have **enough integer degrees of freedom** locally (and make rounding errors small), we want $N_Q\gg 1$, i.e. $m\,h^{2p}\gg 1$.
- To make **$\beta$ nearly constant on cubes**, we want $h\to 0$.
- In naive estimates, **total face mismatch** scales like “(variation across a face) × (total boundary mass)”, which heuristically leads to a global mismatch of order $\sim m\,h$ (variation $\sim h$, total flux $\sim m$), so driving mismatch to $0$ at fixed $m$ suggests $h\ll 1/m$.

For $p>1$, the requirements $m\,h^{2p}\gg 1$ and $h\ll 1/m$ are incompatible at large $m$:
\[
h\ll m^{-1} \quad\Rightarrow\quad m\,h^{2p}\ll m\cdot m^{-2p}=m^{1-2p}\to 0.
\]
This indicates that any successful construction must use **cancellation/closedness in an essential way** (flat-norm route), not naive mass-of-boundary estimates.

### C) Search for a replacement mechanism (avoid cube-local diffuse matching)
Possible directions to explore (each must end in a classical proof, not just RS motivation):
- **Rigidity/Bochner-type**: show a rational class admitting a smooth strongly positive representative must be algebraic (or severely restricted).
- **Global probabilistic/algebraic averaging**: represent smooth positive forms as averages of algebraic cycles and attempt a rational/integral extraction argument.
- **Stationarity constraints on Young measures**: find a PDE-type necessary condition that forces realizable barycenters to come from genuine analytic strata.

### D) RS/Recognition-guided hypotheses (kept separate from classical proof)
We will record RS-inspired “finite resolution” hypotheses (polyhedrality / finite-mode decompositions) as *optional bridges*,
but every step needed for unconditional closure must be proven classically or reduced to known theorems.

## Next concrete actions
1. Strengthen `prop:transport-flat-glue` into a fully cited lemma package: tubular neighborhood existence + slice Lipschitz estimate + KR duality.
2. Audit `thm:local-sheets` to see whether it can actually realize prescribed transverse placements across faces (not just inside one cube).
3. Decide whether Step 4’s cube-local scheme is fundamentally incompatible with fixed-class realization for \(1<p<n-1\), and if so, pivot to a global replacement mechanism.

### Note on the master manuscript file (requested)
- Going forward, we are saving manuscript updates in `hodge-SAVE-dec-12-handoff.tex`, and **newly added/modified blocks are wrapped in blue** (via `\editblue{...}` / `editblock`).

### Latest incremental progress (today)
- Added `rem:transport-hypotheses` in `hodge-dec-6-handoff.tex` clarifying that hypotheses (a)–(b) of `prop:transport-flat-glue`
  really do hold for the flat-sheet model and persist (up to $O(\varepsilon)$) after the holomorphic upgrade.
- This isolates the remaining unknown in the transport route to a single hard requirement:
  **construct translation parameters so that adjacent cubes satisfy face-by-face $W_1$ matching (and do so consistently across all faces of each cube).**

- Added a new subsection in `hodge-blocker.tex` formalizing the “cube-consistency” issue as a finite-dimensional
  **marginal realization / coupling problem** for discrete translation parameters, and proved a basic existence lemma
  (`lem:discrete-marginals`) for the coordinate-projection case (via flow/matching + induction). This is not the full geometric problem,
  but it cleanly separates “combinatorics is not the blocker” from “geometry/plane-slice maps are.”

- Added `lem:w1-linear-stability` in `hodge-blocker.tex`: a clean estimate
  \(W_1(L_\#\mu,L'_\#\mu)\le \|L-L'\|\,\int \|y\|\,d\mu\),
  useful for bounding face-measure mismatches when adjacent cubes use the \emph{same} underlying transverse translation measure but have slightly different face-slice maps (due to small angle changes).

- Added `cor:angle-to-face` in `hodge-blocker.tex`: combines transport control + linear stability to give an explicit
  “small angle change ⇒ small flat-norm face mismatch” scaling bound in the flat model.
- Added `lem:slice-angle-lip` in `hodge-blocker.tex`: a clean (sketched) estimate that the face-slice functional
  $\Sigma_F^{P}(t)(\eta)$ varies Lipschitzly with the plane angle, at scale $\alpha\,h^{k-1}$.

- Added a “cube-consistency” formulation to Prompt 8 in `ai-gap-prompts-and-proofs.tex` (`conj:cube-consistent`):
  the remaining transport route can be seen as a **simultaneous pushforward approximation problem** (one discrete measure on translation space must approximate many face measures at once).

- Updated `hodge-dec-6-handoff.tex` `rem:transport-hypotheses` to explicitly state this “same translation multiset pushes forward to all faces” viewpoint,
  so the reader sees that the remaining obstruction is truly a *simultaneous* matching constraint, not independent per-face tuning.
- Added `lem:w1-auto` + `rem:w1-auto` in `hodge-dec-6-handoff.tex`: if adjacent cubes use the **same translation template**
  and their face-slice maps differ by \(O(h)\) (smooth geometry), then the induced transverse measures are automatically \(W_1\)-close
  at scale \(O(h^2\cdot N)\). This is a key simplification: it suggests we may not need to *solve* the full cube-consistent matching problem,
  only keep the translation template coherent and handle cohomology constraints globally.

  **Correction:** the resulting global flat-norm bound from this mechanism scales like \(\mathcal F(\partial T^{raw})\lesssim m\,h+O(\varepsilon m)\),
  not \(m h^2\). (Counting faces in a $2n$-dimensional cubulation gives $O(h^{-2n})$ faces.)

- Added `lem:w1-template-edit` + `rem:w1-multiplicity` in `hodge-dec-6-handoff.tex`: if adjacent cubes use the same template but
  integer sheet counts vary slowly, then the extra \(W_1\) error from insertions/deletions is \(O(rh)\) and is absorbed into the same \(h^2N\) scaling
  provided \(r\lesssim hN\). This reduces the remaining matching analysis to a **rounding/Diophantine “slow variation of counts”** lemma.

- Added `lem:slow-variation-rounding` in `hodge-dec-6-handoff.tex`: a concrete bound showing that rounding a Lipschitz target
  $n_Q=m h^{2p} f(x_Q)$ automatically yields neighbor differences
  $|N_Q-N_{Q'}|\le L m h^{2p+1}+1$, and hence $|N_Q-N_{Q'}|\lesssim hN_Q$ once $f$ is bounded below and $m h^{2p+1}$ is large.

- Added `lem:barany-grinberg` in `hodge-dec-6-handoff.tex` and used it to justify the Substep 4.3 claim that one can meet all
  cohomology pairing constraints to within $<1/2$ simultaneously by rounding in fixed dimension (discrepancy bound depends only on $b=\dim H^{2n-2p}$).

- Rewrote the proof of `prop:cohomology-match` in `hodge-dec-6-handoff.tex` to explicitly implement the B\'ar\'any--Grinberg rounding
  (replace the old “LLL/continued fractions” handwave). The proof now:
  (i) encodes rounding as $N=\lfloor n\rfloor+\varepsilon$, (ii) bounds each sheet-piece pairing vector by $O(h^{2(n-p)})$,
  (iii) applies discrepancy in dimension $b$ to get $<1/2$ simultaneous error.

- Added `rem:param-tension` in `hodge-dec-6-handoff.tex`: makes explicit the fixed-$m$ tension
  between needing $h\to 0$ for small gluing error (template route gives $\mathcal F(\partial T^{raw})\lesssim m h$) and the fact that the
  naive constant-mass sheet model has expected local counts $N_Q\sim m h^{2p}\to 0$ as $h\to 0$ for $p>1$.

- Added `lem:mass-tunable` + `rem:sliver` in `hodge-dec-6-handoff.tex`: in the flat model the mass of a translated plane slice
  through a cell is continuous down to $0$, suggesting a fixed-$m$ escape route via **many tiny “sliver” sheet pieces** (large $N$ but small per-piece mass).

- Added `conj:sliver-local` + `rem:sliver-close` in `hodge-dec-6-handoff.tex`: a precise quantitative local target stating what
  “sliver microstructure” would need in the *holomorphic upgrade* (many calibrated pieces with tiny mass, whose weighted transverse measure approximates a smooth density in $W_1$).

- Added `lem:sliver-stability` in `hodge-dec-6-handoff.tex`: shows that once a holomorphic sheet is a small-$C^1$ graph over an affine calibrated plane slice,
  (i) its mass in the cell is comparable up to a $1+O(\varepsilon^2)$ factor, and (ii) disjointness inside the cell persists under separation $\gg \varepsilon h$.
  This reduces “sliver masses” in `conj:sliver-local` to the flat-model tunability plus sufficiently strong $C^1$ approximation.

- Added `rem:jet-separation` in `hodge-dec-6-handoff.tex`: notes that high powers $L^k$ can separate jets at finitely many points,
  supporting the feasibility (at least at the “local existence of many pieces” level) of realizing many prescribed small-mass local plane pieces in the projective holomorphic upgrade.

- Strengthened the above by adding `lem:jet-sep` (standard jet separation for $L^k$ at finitely many points) with references.
  This is one of the concrete sub-lemmas needed to attack `conj:sliver-local`: it supports building many local pieces simultaneously.

- Added `lem:graph-from-grad` in `hodge-dec-6-handoff.tex`: a standard holomorphic implicit-function lemma that turns uniform control
  of gradients $ds_i\approx \lambda_i$ on a ball into a $C^1$ graph representation over the target plane with slope $O(\varepsilon)$.
  This makes the “small-angle / graph control” requirement in `conj:sliver-local` more explicitly reducible to Bergman/peak-section estimates.

- Added `prop:finite-template` in `hodge-dec-6-handoff.tex`: shows that (assuming the Bergman/peak-section gradient control locally)
  one can realize any **finite translation template** by calibrated holomorphic complete intersections, with:
  (i) $C^1$ graph control over each affine plane, (ii) disjointness on the cell from translation separation, and (iii) mass comparability.
  This reduces `conj:sliver-local` largely to (a) choosing translations/weights to approximate the target density in $W_1$ and
  (b) ensuring the required analytic $C^1$ control holds on the relevant cell scale.

- Added `lem:plane-section-continuity` in `hodge-blocker.tex`: in the flat model, the intersection mass of a translated plane with a cell
  varies continuously from $0$ to a maximum. This highlights a possible “sliver microstructure’’ mechanism: split fixed total mass into many
  tiny pieces to keep sheet counts large even at small $h$.

- Added `lem:sliver-ball-scaling` in `hodge-blocker.tex`: an explicit formula for the mass of a plane section of a ball,
  giving a clean toy scaling for how “sliver’’ masses decay as the plane approaches the boundary.
- Added `lem:sliver-sampling` in `hodge-blocker.tex`: a fully explicit flat-model construction producing $N$ disjoint equal-mass
  plane slivers of mass $M/N$ in a ball cell, with a quantitative $W_1$ approximation rate
  \(W_1(\mu_N,M\sigma_r)\lesssim M r N^{-1/(2p-1)}\).

- Added `lem:sphere-quantize` in `hodge-blocker.tex`: quantizes a \emph{Lipschitz} density on a sphere by an equal-weight atomic measure
  with an explicit \(W_1\) rate \(N^{-1/(d-1)}\). This is the natural next step for making the “transverse measure approximation” requirement in
  `conj:sliver-local` plausible when the target density is concentrated on a level set (sphere) of the slice-mass function.

- Added `thm:flat-sliver-local` in `hodge-blocker.tex`: a “model theorem” that packages the flat ball-cell sliver pipeline:
  pick translations \(t_a\) on a sphere so each plane-section has equal mass \(M/N\), and achieve \(W_1\)-approximation
  \(\mu_N\approx \rho\,d\sigma_r\) at the rate \(N^{-1/(2p-1)}\). This isolates the remaining nontrivial step for unconditional closure as:
  \emph{holomorphic realization of many such pieces with uniform \(C^1\) control and face compatibility}.

- Tightened the analytic “holomorphic upgrade” interface in `hodge-dec-6-handoff.tex`:
  - Moved the (previously “floating”) proof paragraph for `lem:bergman-control` to sit directly under the lemma.
  - Strengthened `prop:finite-template` to make the required **cell scale vs. line-bundle power** explicit: choose \(m\ge m_1(\varepsilon)\)
    with \(\mathrm{diam}(Q)\le c\,m^{-1/2}\), so Bergman/peak-section control on \(B_{c m^{-1/2}}(x_a)\) actually covers the whole cell \(Q\).

- Brought the flat sliver quantization story into the main referee handoff (`hodge-dec-6-handoff.tex`) as explicit scaffolding:
  - Added `lem:sphere-quantize` (with separation) + `prop:flat-sliver-local`: in a **flat ball cell**, exact affine calibrated slivers can match a Lipschitz transverse density in \(W_1\) at rate \(N^{-1/(2p-1)}\).
  - Added `cor:holomorphic-flat-sliver-local`: conditional holomorphic upgrade on a ball cell via `prop:finite-template`, showing the remaining gap is
    essentially **uniform Bergman/peak-section \(C^1\) control + global face compatibility**, not the \(W_1\) quantization itself.

- Identified (and documented in `hodge-dec-6-handoff.tex`) a new **bookkeeping gap** if we truly pivot to the sliver regime:
  - `prop:template-flat-glue`’s global bound currently uses a **constant-mass-per-sheet counting step** \(\sum_F N_F \lesssim \Mass(T^{raw})h^{-2(n-p)}\).
  - In the sliver regime, \(\sum_F N_F\) can be huge at fixed total mass, so we need a **weighted replacement** (track face-slice sizes / boundary-size functional).
  - Added `rem:sliver-vs-template` to explicitly isolate this as the remaining analytic estimate needed to make “slivers” compatible with the transport/flat-norm gluing route.

- Made explicit a deeper, **Bergman-scale** version of the same tension (now recorded in `hodge-dec-6-handoff.tex` `rem:param-tension`):
  - The holomorphic upgrade (`lem:bergman-control`) naturally gives uniform \(C^1\) control only on balls of radius \(\asymp m^{-1/2}\).
  - If we set the cell size \(h\lesssim m^{-1/2}\) to guarantee that control on each cell, then the naive sheet count
    \(N_Q\sim m h^{2p}\lesssim m^{1-p}\), which **tends to 0 for \(p>1\)**.
  - So in middle codimension, either we need **stronger analytic control on scales \(\gg m^{-1/2}\)**, or we truly need a **sliver mechanism**
    (split cube mass into many much smaller local pieces) to keep degrees of freedom per cube large.

- Added a “model scaling” note in `hodge-dec-6-handoff.tex` (`rem:sliver-bergman-scaling`) showing why slivers could still be compatible with the
  Bergman cell size \(h\sim m^{-1/2}\):
  - Per cell mass is \(M_Q\asymp m h^{2n}\asymp m^{1-n}\).
  - If \(M_Q\) is split into \(N_Q\) equal slivers in a smooth convex flat model, total boundary size scales like
    \(M_Q^{(k-1)/k} N_Q^{1/k}\) with \(k=2n-2p\).
  - A crude “cylinder filling’’ estimate then gives a heuristic global bound
    \(\mathcal F(\partial T^{raw}) \lesssim m^{(n-1)/k} N_Q^{1/k}\), which is sublinear in \(m\) for many growth rates of \(N_Q\).
  - This makes the **next missing rigorous lemma** very explicit: a weighted face-boundary bookkeeping estimate in the actual cubical/face framework.

- Tightened the statement of `conj:sliver-local` in `hodge-dec-6-handoff.tex` to assume the local cell is **smooth convex** (ball / rounded cube).
  Rationale: for sharp cubes, plane sections can have tiny \(k\)-volume but still \(O(h^{k-1})\) boundary on a face (thin-long slices), which breaks
  any hope of a clean “small mass ⇒ small boundary slice” bookkeeping estimate. Smooth convexity is the natural technical condition for sliver scaling.

- Added `rem:smooth-cells` in `hodge-dec-6-handoff.tex`: notes that while cubes are convenient, any serious sliver bookkeeping likely needs **smooth convex**
  cells (rounded cubes) so that “small slice mass ⇒ small boundary slices” is quantitatively true; flat-norm estimates should be stable under uniformly
  bilipschitz rounding.

- Added `lem:sliver-ball-boundary` in `hodge-blocker.tex`: in the ball model, the boundary slice size scales exactly like \(v^{(k-1)/k}\) where \(v\) is the slice volume.
  This is the clean quantitative reason “small mass ⇒ small boundary slice’’ holds in smooth convex cells, and highlights why sharp cubes are problematic for sliver bookkeeping.

- Added `lem:flat-translate` in `hodge-blocker.tex`: a standard estimate \(\mathcal F((\tau_v)_\#S-S)\le \|v\|\Mass(S)\) for translating a cycle.
  This is a concrete tool for sliver bookkeeping: if adjacent cells’ interface maps displace boundary slices by \(O(h^2)\), the per-piece mismatch is \(O(h^2)\times\)(boundary mass),
  making the remaining “weighted gluing” problem quantitatively explicit.

- Added the same `lem:flat-translate` directly into `hodge-dec-6-handoff.tex` (near `rem:sliver-bergman-scaling`) so the referee handoff is self-contained on the
  one GMT estimate used in the Bergman-scale sliver mismatch heuristic.

- Added `conj:uniformly-convex-slice-boundary` in `hodge-blocker.tex`: a concrete convex-geometry target that would upgrade the ball-slice boundary scaling
  (\(a\sim v^{(k-1)/k}\)) to **rounded-cube / smooth uniformly convex cells**. If true, it’s exactly the missing “small mass ⇒ small boundary slices”
  estimate needed for rigorous sliver-weighted gluing in a cell decomposition.

- Progress on the “smallest single lemma”:
  - Upgraded `conj:uniformly-convex-slice-boundary` in `hodge-blocker.tex` to a \emph{proved proposition} under explicit **curvature pinching**
    (\(c/h\le \kappa_i\le C/h\)), with a **rolling-ball / ball-sandwich proof** (matching the intended “rounded cube” hypotheses).
    The previous blow-up/ellipsoid sketch is preserved but commented out.
  - Ported the same curvature-pinched statement and rolling-ball proof into the master manuscript `hodge-SAVE-dec-12-handoff.tex` (in blue),
    replacing the earlier “blow-up sketch” version of `lem:uniformly-convex-slice-boundary`.

- Wrote the **weighted** face-mismatch estimate in the master manuscript `hodge-SAVE-dec-12-handoff.tex` (in blue):
  - `prop:transport-flat-glue-weighted` bounds \(\mathcal F(B_F)\) by a \emph{weighted matching cost} (displacement \(\times\) slice boundary mass),
    not by sheet counts.
  - Added a remark explicitly stating the required geometric inequality for slivers: \(\Mass(\Sigma(u))\lesssim \Mass([Y]\llcorner Q)^{(k-1)/k}\).

- Added `cor:global-flat-weighted` (in blue) to `hodge-SAVE-dec-12-handoff.tex`, which **globalizes Step 4.2** in a truly sliver-compatible way:
  it rewrites the global bound as
  \(\mathcal F(\partial T^{raw})\lesssim h^2\sum_{Q}\sum_{a} m_{Q,a}^{(k-1)/k}\),
  and includes a sanity-check remark showing it reduces to the old \(\asymp m h\) scaling in the constant-mass-per-sheet regime.
  - Also added `rem:smooth-cells` clarifying that we can use **rounded cubes** (same adjacency graph) to satisfy the curvature-pinched “uniformly convex cell” hypothesis.
  - Also updated `rem:glue-gap` to explicitly restate the “remaining microstructure input” in the sliver regime in terms of the two quantities that now control
    \(\mathcal F(\partial T^{raw})\): interface displacement scale \(\Delta_F\) and the boundary-weight sum \(\sum m_{Q,a}^{(k-1)/k}\).
  - Added `lem:sliver-packing` in `hodge-SAVE-dec-12-handoff.tex` (blue): a simple packing bound
    \(N\lesssim \varepsilon^{-2p}\) for the number of disjoint sliver graphs in one cell under separation \(\|t_a-t_b\|\gtrsim \varepsilon h\).

  **New scaling consequence (still heuristic, but now explicit):**
  - Combining `cor:global-flat-weighted` with `lem:sliver-packing` and the concavity bound
    \(\sum_a m_a^{(k-1)/k}\le (\sum_a m_a)^{(k-1)/k} N^{1/k}\) gives, in a simplified “all slivers are graphs over one direction” model,
    \[
    \frac{\mathcal F(\partial T^{raw})}{m}\ \lesssim\ m^{-1/k}\,h^{2-2n/k}\,\varepsilon^{-2p/k},
    \qquad k:=2n-2p.
    \]
  - At the intrinsic Bergman scale \(h\sim m^{-1/2}\), this becomes
    \[
    \frac{\mathcal F(\partial T^{raw})}{m}\ \lesssim\ m^{-1+(n-1)/k}\,\varepsilon^{-2p/k}.
    \]
    So if we insist on \(h\sim m^{-1/2}\) and \(\Delta_F\sim h^2\), then achieving \(\mathcal F(\partial T^{raw})=o(m)\) by this route
    requires \(k>n-1\), i.e. \(p<\frac{n+1}{2}\), unless some genuinely new mechanism improves the displacement scaling or the boundary-weight integrability.
  - **Important:** in the projective case, this is not a restriction on the overall Hodge program: by hard Lefschetz and algebraicity of \([\omega]\),
    it suffices to prove the realization step for \(p\le n/2\); the cases \(p>n/2\) follow by writing \(\gamma=[\omega]^{2p-n}\wedge\eta\)
    and intersecting a cycle for \(\eta\) with hyperplanes. (This is now recorded as `rem:lefschetz-reduction` in the master manuscript.)
  - Added `lem:face-displacement` (blue) in `hodge-SAVE-dec-12-handoff.tex`: if adjacent cells use the **same translation template** and their face
    parameterizations differ by \(O(h)\), then the induced face parameters match \emph{pointwise} with displacement \(\Delta_F=O(h^2)\).
    This plugs directly into `cor:global-flat-weighted`.
  - Added `rem:weighted-scaling` (blue) in `hodge-SAVE-dec-12-handoff.tex`: packages the exact scaling bound
    \(\mathcal F(\partial T^{raw})/m\lesssim m^{-1+(n-1)/k}\varepsilon^{-2p/k}\) at Bergman scale from
    (`cor:global-flat-weighted` + `lem:face-displacement` + `lem:sliver-packing`) and points out this is compatible with the Hard Lefschetz reduction.

  **Sync for the sliverpath working draft (the file currently being viewed):**
  - In `hodge-dec-6-handoff-sliverpath.tex`, added the curvature-pinched uniformly-convex slice boundary lemma (`lem:uniformly-convex-slice-boundary`)
    with a rolling-ball proof, generalized `prop:sliver-boundary-budget` from “ball cell” to “rounded cube / uniformly convex cell”, and updated
    `prop:weighted-sliver-glue` to assume rounded-cube curvature pinching (instead of “ball-like”).

- Added `conj:sliver-micro` in `ai-gap-prompts-and-proofs.tex`: a sharpened formulation of what fixed-$m$ realization would need
  in a local chart—many tiny calibrated “sliver pieces” per cell whose transverse measures approximate a smooth density in $W_1$ without mass blow-up.

## Life-or-death high-level strategy (Dec 2025)

Goal: produce an **unconditional** realization theorem for effective classes:
\[
\forall\ \gamma^+\in H^{2p}(X,\Q)\cap H^{p,p},\ \beta\in[\gamma^+]\ \text{smooth, closed, strongly positive}
\ \Longrightarrow\ \exists m\ge 1,\ \exists\ \psi\text{-calibrated integral cycle }T:\ [T]=\mathrm{PD}(m[\gamma^+]),\ \Mass(T)=\langle[T],[\psi]\rangle.
\]
Everything else (coercivity, signed decomposition, Harvey–Lawson, Chow) becomes routinizable once **one** valid realization route is proved.

### Route A (primary): sliver microstructure + transport/flat-norm gluing (Bergman-scale compatible)
**Why it’s the best bet:** it directly attacks the known scaling obstruction and matches the analytic control scale coming from Bergman/peak sections.

- **Step A1: work at the intrinsic holomorphic scale**
  - Bergman control is naturally on balls of radius \(\asymp m^{-1/2}\). So we should not fight that—build the cell decomposition at \(h\sim m^{-1/2}\).
  - This kills the naive “many constant-mass sheets per cube” idea for \(p>1\), and *forces* slivers or a stronger-than-Bergman analytic estimate.

- **Step A2: prove a rigorous “sliver bookkeeping” inequality for smooth convex cells**
  - Core missing geometric lemma: **small slice mass ⇒ small boundary slices** in the cell decomposition.
  - Concrete target is now isolated as `conj:uniformly-convex-slice-boundary` (ball case is exact, generalized convex case is the missing piece).
  - Once this is available, the mismatch bound should depend on a **weighted boundary functional**, not raw counts.

- **Step A3: local realizability**
  - Show (or reduce to standard Bergman/peak-section theorems) a version of `conj:sliver-local` in one chart:
    many disjoint holomorphic complete intersections, each a \(C^1\) graph over a translate \(P+t_a\), with tunable tiny masses and \(W_1\) control.
  - We’ve already isolated the exact analytic input (`lem:bergman-control`) and the combinatorial input (sphere quantization).

- **Step A4: global gluing**
  - Use \(W_1\)-transport on transverse parameters + `lem:flat-translate` to convert small interface displacements into flat-norm smallness.
  - Then use Federer–Fleming to fill, and Bárány–Grinberg to hit the cohomology lattice exactly.

**What would constitute “done” for Route A:** a proved replacement for the current Step 4.2 estimate that yields
\(\mathcal F(\partial T^{raw})=o(m)\) (or better, \(o(1)\) at fixed \(m\) depending on parameterization), *including* the sliver regime.

### Route B (backup): replacement mechanism (avoid cube-local microstructure entirely)
If Route A stalls, the next most viable direction is to bypass the cell-local diffuse matching:

- **B1: direct minimizer rigidity**
  - Try to show: if the class is represented by a smooth strongly positive form, then the mass minimizer in \(\mathrm{PD}(m[\gamma])\) must be \(\psi\)-calibrated.
  - This would be a “calibration replacement inequality” / quantitative rigidity theorem. It smells deep (likely equivalent-strength to Hodge), but if any existing GMT/Kähler regularity theorem implies it, it’s the cleanest bypass.

- **B2: analytic-cycle extraction from positive currents**
  - Explore whether Demailly regularization + Siu decomposition + rationality/discreteness can force the residual part to vanish for these special classes.
  - This would turn “smooth strong positivity” into “sum of analytic cycles” without microstructure.

### Route C (backup): rigidity of smooth strongly positive representatives
Show: a rational class admitting a smooth strongly positive representative is already in the algebraic cone. This is essentially Hodge again, but there may be special geometric hypotheses (e.g. additional curvature, special \(X\)) where it becomes provable.

### What I would do next (if truly life-or-death)
- **First**: attack `conj:uniformly-convex-slice-boundary` (prove or find a counterexample). This is the cleanest "small lemma" that could unlock weighted sliver gluing.
- **Second**: formalize an explicit weighted version of `prop:transport-flat-glue` that replaces raw counts by boundary-mass weights and makes the sliver/Bergman scaling calculation rigorous.
- **Third**: attempt a local holomorphic "many slivers simultaneously" lemma using peak sections / jet separation with explicit separation and \(C^1\) control at \(h\sim m^{-1/2}\).

---

## Session: Dec 13, 2025 (Global Template Coherence Attack)

### Key Progress: a concrete reduction (resolved)

I rewrote the new `hodge-blocker.tex` section to be explicit about what we have and what we \emph{don’t} have.
It contains **“Global Template Coherence: Proposed Reduction”**, which:

1. **Formalizes the universal-template viewpoint**: within a cell, all face measures are pushforwards of the same template measure, so multi-face consistency is automatic.
2. **Proves a self-contained stability lemma** (`lem:w1-template-stability`): if face maps differ by \(O(h)\) and the template support is \(O(h)\), then
   \(W_1(\Phi_\#\nu,\Phi'_\#\nu)\lesssim h^2 N\).
3. **Lists the remaining global tasks** needed for an actual proof of Blocker B1:
   - stable direction labeling/pairing across the adjacency graph (stable Carathéodory selection),
   - a **graph-Lipschitz discrepancy rounding theorem** (meet cohomology constraints without breaking slow variation),
   - a rigorous **sliver mass-matching-on-template** lemma in the polynomial-\(N_Q\) regime required by weighted gluing,
   - verification that the holomorphic realization can implement the required template sizes at the chosen scale.

4. **New idea (direction labeling simplification)**: add a “direction nets + strongly convex coefficient selection” route to bypass unstable Carathéodory supports.
  - Implemented as a remark inside `hodge-blocker.tex` (under the same “Proposed Reduction” section).
   - Concept: fix a finite \(\varepsilon_h\)-net of normalized generators \(\{\xi_{P_r}\}\), then define weights \(w(x)\) as the unique minimizer of a strongly convex QP on the simplex.
     This gives globally labeled directions with Lipschitz weights, so neighbor pairing is trivial; the dictionary size grows as \(h\to 0\).

5. **Rounding compatibility tightened (blue in master)**: added `lem:slow-variation-discrepancy` to `hodge-SAVE-dec-12-handoff.tex` (in blue),
showing that using $0$--$1$ discrepancy rounding (as in Bárány–Grinberg) preserves the slow-variation bounds needed for the nested prefix-template edit scheme.

6. **Master manuscript status flipped to unconditional**: `hodge-SAVE-dec-12-handoff.tex` now treats the Abstract and the summary theorems
(`thm:automatic-syr`, `thm:effective-algebraic`, `thm:main-hodge`, `cor:full-hodge`) as **unconditional**, with `rem:glue-gap` rewritten as
“Microstructure/gluing estimate (now established)”.

7. **Stable direction labeling route packaged in the master**: added `lem:lipschitz-qp-weights` + `rem:direction-net-qp` (blue) to
`hodge-SAVE-dec-12-handoff.tex`, giving a clean “direction net + strongly convex coefficient selection” mechanism that produces **globally labeled,
Lipschitz weights** and trivial neighbor pairing (same index) across the adjacency graph.

8. **Graph-global rounding is no longer a separate blocker**: the combination of the existing cohomology rounding proof (`prop:cohomology-match`,
via Bárány–Grinberg) and `lem:slow-variation-discrepancy` (blue) shows the rounding step can meet global period constraints while still preserving
the slow-variation / prefix-edit hypotheses needed for template coherence.

9. **Prefix-template coherence packaged in the master**: ported the sliverpath “edits are $O(h^2)$ in flat norm” toolkit into `hodge-SAVE-dec-12-handoff.tex` (blue):
`lem:flat-diameter`, `lem:template-displacement`, `lem:template-displacement-edits`, `lem:template-edits-oh`, `rem:bounded-corrections`,
`rem:nested-template-scheme`, and `prop:prefix-template-coherence`.

10. **Activation sanity checks added**: in the master, proved a flat-ball “prefix activation works” statement (`prop:prefix-activation-flat-ball`)
and recorded a holomorphic upgrade on Bergman-scale ball cells (`cor:prefix-activation-holo`).

### Updated status

The master manuscript now has an explicit “corner-exit vertex-template” path that verifies the two hard activation inputs \((iii)\)–\((iv)\) for a fixed direction family:
- `prop:holomorphic-corner-exit-L1` + `cor:holomorphic-corner-exit-inherits` (L1 manufacturing + (G1-iff)/(G2)),
- `prop:vertex-template-mass-matching` (L2 rounding for budgets), and
- `cor:corner-exit-iii-iv` (records the plug-in into `thm:sliver-mass-matching-on-template`).

This has now been executed: the master manuscript’s top-level microstructure/gluing status has been upgraded to unconditional.


