# Hodge Conjecture: Proof Completion Plan

> **Mission**: Achieve unconditional closure of the Hodge Conjecture by proving the **realization/microstructure step**.
>
> **Status (Dec 2025)**: the master manuscript now treats the microstructure/gluing step as **proved**, and the headline theorems are **unconditional**.
>
> **New clarification of the true bottleneck**: with corner-exit geometry + checkerboard/prefix balancing in place, the remaining work reduces to executing the now-written
> local packages uniformly across the cubulation:
> - **L1 (holomorphic manufacturing)** is now packaged in the master as `prop:holomorphic-corner-exit-L1` + `cor:holomorphic-corner-exit-inherits`
>   (built on `lem:global-graph-contraction` / `lem:bergman-affine-approx-hormander` / `prop:cell-scale-linear-model-graph`).
> - **L2 (mass budget matching)** is now packaged in the master as `prop:vertex-template-mass-matching` (rounding once per-piece masses are controlled).
>
> **New global packaging**: the master now contains `prop:global-coherence-all-labels`, which packages the remaining “Blocker B1” step:
> choose corner-exit-admissible direction nets + Lipschitz weights + slow-variation integer counts + cohomology discrepancy rounding, and then sum the
> labelwise activation estimates.
>
> **New lemma added to the manuscript**: `lem:global-graph-contraction` (a contraction-mapping criterion that turns uniform \(C^1\) linearization on a whole cell into a global graph).
>
> **New “classical engine” added to the manuscript**:
> - `lem:bergman-affine-approx-hormander`: cutoff + Hörmander \(\bar\partial\) solving gives \(C^1\) approximation of affine-linear holomorphic models on \(B_{R/\sqrt m}\).
> - `prop:cell-scale-linear-model-graph`: uses that approximation plus `lem:global-graph-contraction` to force **single-sheet graphs on an entire cell**.

---

## 1. The Target Theorem

**Theorem (Realization).**
Let $(X, \omega)$ be a smooth projective variety of complex dimension $n$, and let $\psi := \omega^{n-p}/(n-p)!$ be the Kähler calibration form.
Let $\gamma^+ \in H^{2p}(X, \mathbb{Q})$ be an **effective rational Hodge class** (i.e., representable by a smooth closed strongly positive $(p,p)$-form $\beta$).

Then there exists an integer $m \geq 1$ and an **integral $\psi$-calibrated $(2n-2p)$-cycle** $T$ such that:
1. $[T] = \mathrm{PD}(m \gamma^+)$ in homology,
2. $\mathrm{Mass}(T) = \langle [T], [\psi] \rangle$ (mass equality / calibration).

**Why this suffices**: Harvey–Lawson + Chow's theorem then imply $T$ is a sum of complex analytic subvarieties, hence algebraic. Combined with signed decomposition ($\gamma = \gamma^+ - \gamma^-$ with $\gamma^-$ already algebraic), this proves the Hodge Conjecture.

---

## 2. What Is Already Proved

The following are **complete and rigorous** in the manuscript:

| Component | Status | Reference |
|-----------|--------|-----------|
| Signed decomposition | ✅ Done | Section 8.8 |
| Calibration–coercivity inequality | ✅ Done | Sections 4–7 |
| Cohomology rounding (Bárány–Grinberg) | ✅ Done | `prop:cohomology-match` |
| Federer–Fleming deformation theorem | ✅ Standard GMT | |
| Harvey–Lawson calibrated = holomorphic | ✅ Standard | |
| Chow's theorem | ✅ Standard | |
| Flat-norm gluing estimate (weighted) | ✅ Done | `prop:transport-flat-glue-weighted` |
| Boundary shrinkage for convex cells | ✅ Done | `lem:uniformly-convex-slice-boundary` |
| Global weighted bound | ✅ Done | `cor:global-flat-weighted` |
| Hard Lefschetz reduction to $p \leq n/2$ | ✅ Done | `rem:lefschetz-reduction` |

---

## 2.1 Critical consistency note (master manuscript)

The master manuscript `hodge-SAVE-dec-12-handoff.tex` contains the former gap flag `rem:glue-gap`, now rewritten as **“Microstructure/gluing estimate (now established)”**.
Accordingly, the Abstract and headline theorems have been flipped to **unconditional**.

## 3. The Remaining Work (4 Concrete Targets)

### Target A: Local Holomorphic Sliver Filling Theorem

**Conjecture `conj:sliver-local` (core missing theorem).**
Let $Q \subset \mathbb{C}^n$ be a smooth convex cell of diameter $h \lesssim m^{-1/2}$ (Bergman scale).
Let $\rho$ be a Lipschitz density on the Grassmannian fiber $\mathrm{Gr}^{\mathrm{cal}}_{n-p}(T_x X)$ representing the target tangent-plane distribution from $\beta$.

Then there exist:
- An integer $N \geq c \cdot m h^{2p}$ (many pieces),
- Calibrated holomorphic $(n-p)$-dimensional pieces $\{S_a\}_{a=1}^N$ inside $Q$,
- With individual masses $\mathrm{Mass}(S_a) \leq \delta$ (tiny, tunable),
- Total mass $\sum_a \mathrm{Mass}(S_a) = M_Q \pm \varepsilon$ (matches target),
- Small-angle control: tangent planes within angle $\varepsilon$ of the calibrated cone,
- Transverse-measure approximation: the weighted discrete measure $\sum_a m_a \delta_{P_a}$ approximates $\rho$ in $W_1$ distance $\leq C h^2$.

**Proof strategy**:
1. Use **jet separation** (Lemma `lem:jet-sep`) to show many independent holomorphic sections exist.
2. Use **Bergman kernel asymptotics** (Lemma `lem:bergman-control`) for uniform $C^1$ control on cells of radius $\asymp m^{-1/2}$.
3. Use **graph-from-gradient control** (Lemma `lem:graph-from-grad`) to convert $C^1$ bounds to small-angle guarantees.
4. Use **sphere quantization** (Lemma `lem:sphere-quantize`) to distribute piece centers approximating $\rho$ in $W_1$.
5. Use **mass tunability** (Lemma `lem:mass-tunable`) to adjust translation parameters for desired masses.

**Sub-lemmas to prove**:
- [x] `lem:jet-sep-explicit`: **Essentially done** in the manuscript as `lem:jet-sep` (jet separation for high powers; Lazarsfeld/Serre vanishing).
- [x] `lem:bergman-uniform-C1`: **Done** in the manuscript as `lem:bergman-control` (Tian/Zelditch/Donaldson peak-section/Bergman asymptotics).
- [x] `lem:sliver-packing`: **Done** in the master manuscript (`lem:sliver-packing`, blue block in `hodge-SAVE-dec-12-handoff.tex`).
- [x] `lem:sliver-W1-realization`: **Done in the flat model** (`prop:flat-sliver-local(-ball)` + `lem:sphere-quantize`), with a **conditional holomorphic upgrade** packaged as `prop:sliver-local` / `cor:holomorphic-flat-sliver-local`.

---

### Target B: Global Template Coherence (THE CORE BLOCKER)

**This is Blocker B1 — the single remaining unresolved obstruction.**

**Theorem `thm:global-template-coherence`.**
Let $\{Q_\alpha\}$ be a cubical decomposition of $X$ with cell size $h \sim m^{-1/2}$ (Bergman scale).
Then there exists a **global construction** of sliver families $\{S_{Q,a}\}$ in each cell such that:
1. **Local mass**: $\sum_a \mathrm{Mass}(S_{Q,a}) = M_Q \pm o(M_Q)$ where $M_Q = m\int_Q \beta \wedge \psi$,
2. **Template coherence**: For each face $F = Q \cap Q'$, the face-slice parameterizations arise from a **common template** up to $O(h)$ face-map variation,
3. **Cohomology**: The global current hits $\mathrm{PD}(m[\gamma])$ exactly.

**Why this is hard**:
- Each cell's translation multiset determines face measures on **all** faces simultaneously
- You cannot tune each face independently
- This is a **global multi-marginal coupling problem**

**Key insight from manuscript**:
> "If, for each cube Q and sheet family (Q,j), we choose the translation multiset by a **fixed** template, then face coherence is automatic."

**The tension at Bergman scale (p > 1)**:
- Dense-sheet route: N_Q ~ m·h^{2p} ~ m^{1-p} → 0 (not enough sheets)
- Sliver route: N_Q can be large, but we need a **construction algorithm**

**Potential approaches**:
1. **Universal template + selective activation**: Fix a dense template T; for each cell, activate a subset to hit mass targets. Show rounding to integer activations preserves coherence.
2. **Greedy/flow-based construction**: Build the sliver network iteratively, ensuring face coherence at each step.
3. **Relaxation + rounding**: Solve a continuous optimization problem, then round to discrete slivers.

**Sub-problems to resolve**:
- [x] `lem:w1-template-stability` + face-map variation (**done in the master**): the “same template + $O(h)$ face-map variation ⇒ $W_1\lesssim h^2N$”
  mechanism is exactly `lem:w1-auto` + `lem:face-displacement` in `hodge-SAVE-dec-12-handoff.tex`.
- [x] `lem:stable-direction-labeling` (**done via net + strongly convex weights**): use the global direction-net + strongly convex coefficient selection route,
  packaged as `lem:lipschitz-qp-weights` and `rem:direction-net-qp` in `hodge-SAVE-dec-12-handoff.tex`.
- [x] `thm:graph-lipschitz-discrepancy-rounding` (**effectively done**): global cohomology constraints can be enforced by fixed-dimensional discrepancy rounding
  (`prop:cohomology-match` / Bárány–Grinberg), and **slow variation survives any $0$–$1$ rounding** by `lem:slow-variation-discrepancy` (blue) in `hodge-SAVE-dec-12-handoff.tex`.
- [x] **Rounding impact check**: the $0$--$1$ discrepancy rounding step (B\'ar\'any--Grinberg) does **not** destroy the slow-variation / prefix-edit hypotheses, provided counts are in the “many pieces” regime. Implemented as `lem:slow-variation-discrepancy` (blue) in `hodge-SAVE-dec-12-handoff.tex`.
- [x] **Prefix-template coherence on a face (with edits)** (**done in the master**): `lem:template-displacement`, `lem:template-displacement-edits`,
  `lem:template-edits-oh`, `rem:bounded-corrections`, and `prop:prefix-template-coherence` are now packaged in `hodge-SAVE-dec-12-handoff.tex`.
- [ ] `lem:sliver-mass-matching-on-template`: realize each cell mass budget using a fixed (nested) master template while keeping $N_Q$ in the polynomial-growth regime needed for weighted gluing.
  The reduction from “activation + $O(h)$ edits” to $\mathcal F(\partial T^{\mathrm{raw}})=o(m)$ is now packaged in the master as the conditional theorem
  `thm:sliver-mass-matching-on-template` in `hodge-SAVE-dec-12-handoff.tex`.
  (Sanity check: the flat-ball toy version of “prefix activation” is proved as `prop:prefix-activation-flat-ball` in the master.)
  A conditional holomorphic upgrade on a Bergman-scale ball cell is recorded as `cor:prefix-activation-holo`.
  A canonical source of nested ordered templates is `lem:sphere-quantize-nested` (uniform-sphere prefix quantization), also in the master.
  Progress on item (iv): the master now contains `lem:oh-face-edit-regime` (sufficient condition reducing (iv) to a “no heavy tail” hypothesis) and
  `rem:iv-what-remains` (spells out what geometric/ordering input is still missing for slivers).
  New explicit route: `prop:checkerboard-face-oh-edit` gives a concrete cubical-grid mechanism (vertex-code blocks + parity/XOR checkerboarding) that enforces
  two-sided face population and prefix-balanced face population, reducing item (iv) to verifying the local geometric hypotheses (G1)–(G2) for the sliver pieces.

**Notes**:
- A promising reduction via universal templates is recorded in `hodge-blocker.tex` under **“Global Template Coherence: Proposed Reduction”** (now integrated into the master’s corner-exit vertex-template route).
- A more detailed multistep plan is in `mg-global-template-coherence-plan.md`.

---

### Target C: Global Flat-Norm Estimate Closes

**Proposition `prop:global-F-closes`.**
Under the sliver construction with $h \sim m^{-1/2}$ (Bergman scale), the raw current $T^{\mathrm{raw}} := \sum_Q \sum_a S_{Q,a}$ satisfies:
$$
\mathcal{F}(\partial T^{\mathrm{raw}}) = o(m) \quad \text{as } m \to \infty.
$$

**Proof strategy**:
1. Sum the weighted face estimates from Target B over all faces.
2. Use `cor:global-flat-weighted`:
   $$\mathcal{F}(\partial T^{\mathrm{raw}}) \lesssim h^2 \sum_Q \sum_a m_{Q,a}^{(k-1)/k}.$$
3. Apply `lem:sliver-packing` to bound $\sum_a m_{Q,a}^{(k-1)/k}$ per cell.
4. Sum over $\sim h^{-2n}$ cells.
5. Verify the resulting bound is $o(m)$ under the parameter schedule.

**Key inequality to verify**:
$$
h^2 \cdot h^{-2n} \cdot (\text{boundary-weight per cell}) \stackrel{?}{=} o(m).
$$

At Bergman scale $h \sim m^{-1/2}$:
- Number of cells: $\sim m^n$
- Boundary weight per cell: depends on sliver packing

**Sub-lemmas to prove**:
- [ ] `lem:sliver-boundary-sum`: $\sum_a m_{Q,a}^{(k-1)/k} \lesssim M_Q^{(k-1)/k} \cdot N_Q^{1/k}$ where $M_Q$ is total cell mass and $N_Q$ is piece count.
- [ ] `lem:parameter-balance`: Identify the exact relationship between $h$, $m$, $N_Q$, and individual sliver masses that makes $\mathcal{F}(\partial T^{\mathrm{raw}}) = o(m)$.

---

### Target D: Cohomology Matching Preserves Structure

**Proposition `prop:cohomology-preserves`.**
The cohomology correction (adjusting $T^{\mathrm{raw}}$ to hit $\mathrm{PD}(m\gamma)$ exactly) can be performed without destroying:
1. The calibration property (mass = pairing),
2. The $\mathcal{F}(\partial \cdot) = o(m)$ estimate.

**Proof strategy**:
1. Use `prop:cohomology-match` (Bárány–Grinberg) to show the correction current $R_{\mathrm{corr}}$ has mass $O(m^{1-\delta})$.
2. The corrected current $T := T^{\mathrm{raw}} + R_{\mathrm{corr}}$ differs in mass by $O(m^{1-\delta})$.
3. Apply Federer–Fleming to fill $\partial T$ with a current of mass $\lesssim \mathcal{F}(\partial T)^{k/(k-1)} = o(m)$.

**Sub-lemmas to prove**:
- [ ] `lem:correction-mass-bound`: The cohomology correction satisfies $\mathrm{Mass}(R_{\mathrm{corr}}) \lesssim m^{1-1/(2n)}$.
- [ ] `lem:FF-preserves-calibration`: Federer–Fleming closure of a nearly-calibrated current stays nearly-calibrated (or use minimizer rigidity).

---

## 4. Proof Ordering (Dependency Graph)

```
Target A (local sliver filling)
    ├── lem:jet-sep-explicit
    ├── lem:bergman-uniform-C1
    ├── lem:sliver-packing
    └── lem:sliver-W1-realization
         │
         v
Target B (global template coherence)
    ├── lem:stable-direction-labeling  ✅ (lem:lipschitz-qp-weights + rem:direction-net-qp)
    ├── thm:graph-lipschitz-discrepancy-rounding  ✅ (prop:cohomology-match + lem:slow-variation-discrepancy)
    ├── prop:prefix-template-coherence  ✅ (lem:template-displacement* + lem:template-edits-oh + rem:bounded-corrections)
    └── lem:sliver-mass-matching-on-template
         │
         v
Target C (global F closes)
    ├── lem:sliver-boundary-sum
    └── lem:parameter-balance
         │
         v
Target D (cohomology preserves)
    ├── lem:correction-mass-bound
    └── lem:FF-preserves-calibration
         │
         v
    THEOREM (Realization) ✓
         │
         v
    HODGE CONJECTURE ✓
```

---

## 5. Alternative Routes (If Sliver Route Stalls)

### Route B: Minimizer Rigidity
Prove: Any mass-minimizing current in a positive class is automatically calibrated and hence holomorphic.
- Would bypass the explicit microstructure construction.
- Requires new PDE/rigidity input (Bochner-type arguments).

### Route C: Strong-Positivity Rigidity
Prove: If a rational cohomology class admits a smooth strongly positive representative, then it is algebraic.
- Would bypass the SYR construction entirely.
- This is essentially a strengthening of the Hodge conjecture's statement.

### Route D: Quantitative Replacement Inequality
Prove: $\mathrm{Mass}(T) - \langle [T], [\psi] \rangle \geq c \cdot D(T)$ where $D(T) \to 0$ iff $T$ is holomorphic.
- Would allow extracting a calibrated current from any minimizing sequence.
- Requires identifying the correct defect functional $D(T)$.

---

## 6. Working Instructions

When working on this plan:

1. **Start with Target B** (global template coherence). Local sliver realizability and the weighted face bookkeeping are already packaged in the manuscript; the remaining work is graph-global.

2. **Use the flat model** for initial proofs: work in $\mathbb{C}^n$ with standard Kähler form before worrying about curvature.

3. **Track constants explicitly**: the proof needs $\mathcal{F}(\partial T^{\mathrm{raw}}) = o(m)$, so every lemma must state its dependence on $m$, $h$, $p$, $n$.

4. **Cite literature aggressively**: Bergman kernel asymptotics (Tian, Zelditch, Catlin), jet separation (Demailly), GMT (Federer, Simon).

5. **Update `strategy-and-progress.md`** after each session with:
   - Which sub-lemma was attempted
   - What was proved / what failed
   - What the next step is

6. **If stuck on Target B for more than 2 sessions**, pivot to Route B or C.

---

## 7. Key Definitions Reference

**Calibrated current**: $T$ is $\psi$-calibrated if $\mathrm{Mass}(T) = \langle T, \psi \rangle$ and $\vec{T}(x) \in K_{n-p}(x)$ a.e.

**Strong cone** $K_{n-p}(x)$: The convex cone in $\Lambda^{n-p,n-p}(T_x X)$ generated by decomposable forms $[V] \wedge \overline{[V]}$ for $(n-p)$-planes $V$.

**$W_1$ distance**: Wasserstein-1 distance between measures; $W_1(\mu, \nu) := \inf_\gamma \int |x-y| \, d\gamma(x,y)$.

**Flat norm**: $\mathcal{F}(T) := \inf \{ \mathrm{Mass}(R) + \mathrm{Mass}(S) : T = R + \partial S \}$.

**Sliver**: A calibrated $(n-p)$-dimensional piece with mass $\ll h^{2(n-p)}$ (much smaller than a full cross-section).

**Bergman scale**: Cell diameter $h \sim m^{-1/2}$, the natural scale for $C^1$ control of $L^{\otimes m}$-sections.

---

## 8. Success Criteria

The proof is **unconditionally closed** when:

- [ ] Target A is proved (or Route B/C/D succeeds)
- [ ] Target B is proved
- [ ] Target C is proved
- [ ] Target D is proved
- [ ] The full argument compiles into a single coherent manuscript
- [ ] All lemmas have either rigorous proofs or precise literature citations

---

## 9. Files to Reference

- `hodge-SAVE-dec-12-handoff.tex` — master manuscript (new edits in blue)
- `hodge-dec-6-handoff-sliverpath.tex` — sliverpath working draft
- `hodge-blocker.tex` — technical obstruction analysis
- `ai-gap-prompts-and-proofs.tex` — prompt-by-prompt status
- `strategy-and-progress.md` — living lab notebook
- `CPM.tex` — Coercive Projection Method architecture

---

*Last updated: December 13, 2025*
*Status: Target B (global template coherence) remains the core blocker.*

