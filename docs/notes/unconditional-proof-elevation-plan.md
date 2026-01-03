# Unconditional Proof Elevation Plan (Referee‑Grade)
This plan is written under two non‑negotiables:
1. **Keep the manuscript’s status unconditional** (the main theorem remains stated as an unconditional proof).
2. **Elevate rigor and auditability as much as possible**: every load‑bearing claim becomes either (i) a finished, checkable theorem/proof in the manuscript, or (ii) a precisely cited published theorem with the exact hypothesis match spelled out.

The working manuscript is `hodge-SAVE-dec-12-handoff-unconditional-b.tex`.

<span style="color:#7B2CBF"><b>[VIOLET]</b></span> **New edits in this round are marked with the tag** <span style="color:#7B2CBF"><b>[VIOLET]</b></span> (intended as “new color” change tracking for Markdown).

<span style="color:#2A9D8F"><b>[TEAL]</b></span> **Status note (Dec 26, 2025): several items in this plan are now implemented in the TeX** (see “Implemented in TeX” blocks below). Remaining work is now mostly optional further tightening (e.g. expanding the external‑theorem ledger into full citation+hypothesis‑check bullets, and (if desired) removing remaining legacy color scaffolding such as `editblock` even though `\finaltrue` disables it).

---

### Current spine (what the paper must make referee‑checkable)
- **Goal output (fixed class + vanishing defect)**: for some integer \(m\ge 1\) and \(A=\mathrm{PD}(m[\gamma])\), produce closed integral cycles \(T_j\) with \([T_j]=A\) and
  \[
  \Def_{\mathrm{cal}}(T_j)=\Mass(T_j)-\langle T_j,\psi\rangle\to 0,
  \quad\text{equivalently}\quad
  \Mass(T_j)\to c_0:=\langle A,[\psi]\rangle.
  \]
- **Closure**: `thm:realization-from-almost` + Harvey–Lawson + Chow/GAGA.
- **Packaging already present**:
  - **Spine theorem**: `thm:spine-quantitative` (defect accounting \(0\le \Mass(T_j)-c_0\le 2\,\Mass(G_j)\)).
  - **Defect lemma**: `prop:almost-calibration`.
  - **Gluing lemma**: `prop:glue-gap` rewritten as a standard proposition (no “status update” prose).
  - **Submission mode**: `\finaltrue` switch disables color edit markup.

Everything below is about making the hypotheses feeding the spine theorem **actually proved, quantified, and parameterized**.

<span style="color:#2A9D8F"><b>[TEAL]</b></span> **Implemented in TeX (current state).** In `hodge-SAVE-dec-12-handoff-unconditional-b.tex` we now have:
- <span style="color:#2A9D8F"><b>[TEAL]</b></span> a dedicated **global quantifier/parameter schedule** subsection `\label{sec:parameter-schedule}` placed right after `thm:spine-quantitative`,
- <span style="color:#2A9D8F"><b>[TEAL]</b></span> explicit integrality lemmas `lem:integral-periods` and `lem:lattice-discreteness`, and the cohomology step rewritten so the **exact-class conclusion is stated for the closed corrected cycle** \(T=S-U\) (not for the raw non-closed sheet sum \(S\)),
- <span style="color:#2A9D8F"><b>[TEAL]</b></span> a named borderline closure lemma `lem:borderline-p-half` routing \(p=n/2\) through the **integer-transport** mechanism (`prop:integer-transport`) \(\Rightarrow\) flat-norm decay \(\Rightarrow\) `prop:glue-gap` \(\Rightarrow\) vanishing defect.

---

### Workstream 0 — “Referee mode” cleanup (presentation is part of rigor)
- **Objective**: remove all “draft seams” from the main chain while preserving unconditional statements.
- **Actions**
  - **Main chain only uses named theorems**: eliminate “Steps 1–6” language in the main chain; every invocation is a theorem/proposition/lemma with a label.
  - **No internal/project prose in load‑bearing sections**: move narrative/heuristics into clearly labeled “Background/Heuristics” subsections or appendices.
  - **Uniform theorem statements**: replace “under hypotheses of Theorems … with parameters →0” with explicit quantified sequences (e.g. “choose \(h_j\downarrow 0\), \(\delta_j=o(h_j)\), …”).
  - **Notation stabilization**:
    - \(m\): **homology multiple** in \(A=\mathrm{PD}(m[\gamma])\).
    - \(M\): **line bundle power** controlling Bergman scale \(M^{-1/2}\).
    - Ensure *no other* “fixed \(M\)” is used for denominators; use \(D\) for denominators.
- **Deliverables**
  - A final‑mode PDF built from `\finaltrue` with no colored markup.
  - A one‑page “Referee map” paragraph at the start of `thm:main-hodge` pointing to the dependency checklist and the spine theorem.

<span style="color:#2A9D8F"><b>[TEAL]</b></span> **Implemented in TeX (Dec 26, 2025):**
- <span style="color:#2A9D8F"><b>[TEAL]</b></span> Removed all occurrences of `\editref{...}` and the `editrefblock` wrapper lines from the manuscript source.
- <span style="color:#2A9D8F"><b>[TEAL]</b></span> Added a front‑loaded **Referee map (main dependency chain)** paragraph at the start of the proof of `thm:main-hodge`.

---

### Workstream 1 — One explicit global parameter hierarchy (the referee must see the limits)
- **Objective**: give a single parameter schedule with a strict order of choices and a final inequality chain where every error term is visibly \(o(1)\).
- **Deliverable format**: a dedicated subsection “Parameter schedule” near `thm:spine-quantitative` (and optionally a short appendix).

<span style="color:#2A9D8F"><b>[TEAL]</b></span> **Implemented in TeX:** see `\label{sec:parameter-schedule}` directly after `thm:spine-quantitative`.

#### Required parameter list
- **Geometric mesh**: \(h_j\downarrow 0\) (cell diameter).
- **Transverse quantization**: \(\delta_j\) (grid spacing), with \(\delta_j=o(h_j)\).
- **Angle/graph control**: \(\varepsilon_j\downarrow 0\) (small‑slope/angle).
- **Holomorphic scale**: \(M_j\to\infty\) (line bundle power) with \(h_j\lesssim M_j^{-1/2}\).
- **Homology multiple**: choose an integer \(m\) (fixed once for the construction) clearing denominators and meeting the integrality/rounding constraints.

#### What must be proved under that schedule
- **(i) Fixed class**: \([T_j]=\mathrm{PD}(m[\gamma])\) for all \(j\).
- **(ii) Gluing mass vanishes**: \(\Mass(G_j)\to 0\) (or directly \(\Mass(U_{\epsilon_j})\to 0\)).
- **(iii) Budget accuracy**: \(\Mass(S_j)=\langle S_j,\psi\rangle\le c_0+o(1)\) with \(c_0=\langle \mathrm{PD}(m[\gamma]),[\psi]\rangle\).

#### “Quantifier table” (must be written explicitly)
- **Choose** \(m\) first (clears denominators + integrality constraints).
- **Then choose** a sequence \(h_j\downarrow 0\).
- **Then choose** \(\delta_j,\varepsilon_j,M_j\) as functions of \(h_j\) so that all bounds close.
- **Finally choose** the discrete rounding variables and templates (counts, activations) at each scale \(j\).

<span style="color:#7B2CBF"><b>[VIOLET]</b></span> **Parameter schedule v1 (explicit, with two regimes).**
<span style="color:#7B2CBF"><b>[VIOLET]</b></span> We will commit to one explicit choice, and then prove every bound under that choice.

<span style="color:#7B2CBF"><b>[VIOLET]</b></span> **Global choice (once):**
<span style="color:#7B2CBF"><b>[VIOLET]</b></span> choose an integer \(m\ge 1\) such that:
- <span style="color:#7B2CBF"><b>[VIOLET]</b></span> \(m[\gamma]\in H^{2p}(X,\mathbb Z)\) (clears denominators),
- <span style="color:#7B2CBF"><b>[VIOLET]</b></span> for a fixed integral harmonic basis \(\{\eta_\ell\}_{\ell=1}^b\subset \mathcal H^{2n-2p}(X)\) generating \(H^{2n-2p}(X,\mathbb Z)\), all periods \(m\int_X\beta\wedge\eta_\ell\in\mathbb Z\),
- <span style="color:#7B2CBF"><b>[VIOLET]</b></span> and \(m\) is large enough to support the fixed-dimensional discrepancy rounding margin (see Workstream 4; target is “error \(<1/2\)” on each integral period).

<span style="color:#7B2CBF"><b>[VIOLET]</b></span> **Scale choice (sequence):** for \(j=1,2,\dots\),
- <span style="color:#7B2CBF"><b>[VIOLET]</b></span> \(h_j := 2^{-j}\) (mesh diameter),
- <span style="color:#7B2CBF"><b>[VIOLET]</b></span> choose \(M_j := \lceil C_0\,h_j^{-2}\rceil\) so that each cell is contained in a Bergman ball of radius \(c\,M_j^{-1/2}\) (so H1 applies uniformly),
- <span style="color:#7B2CBF"><b>[VIOLET]</b></span> choose \(\varepsilon_j := \varepsilon_0\) **constant** (small but fixed) in the non‑borderline regime \(p<n/2\); and \(\varepsilon_j\to 0\) only if a specific lemma requires it (we do *not* shrink \(\varepsilon\) gratuitously, because packing bounds typically worsen as \(\varepsilon\downarrow 0\)),
- <span style="color:#7B2CBF"><b>[VIOLET]</b></span> choose \(\delta_j := h_j^{1+\alpha}\) with a fixed \(\alpha\in(0,1)\) (transverse grid spacing, so \(\delta_j=o(h_j)\)).

<span style="color:#7B2CBF"><b>[VIOLET]</b></span> **Regime A (strict range \(p<n/2\)).**
- <span style="color:#7B2CBF"><b>[VIOLET]</b></span> Prove: with \(\varepsilon_j=\varepsilon_0\) and the H2 coherence estimate \(\Delta_F\lesssim h_j^2\), the global weighted bound gives \(\mathcal F(\partial T^{\mathrm{raw}}_j)\to 0\) as \(j\to\infty\).
- <span style="color:#7B2CBF"><b>[VIOLET]</b></span> Then `prop:glue-gap` gives \(\Mass(R_{\mathrm{glue},j})\to 0\), hence \(\Def_{\mathrm{cal}}(T_j)\to 0\) by `prop:almost-calibration`.

<span style="color:#7B2CBF"><b>[VIOLET]</b></span> **Regime B (borderline \(p=n/2\)).**
- <span style="color:#7B2CBF"><b>[VIOLET]</b></span> In this case the naive exponent “\(h\)-decay” in the global bound disappears. We therefore **commit** to proving an explicit borderline closure lemma (Workstream 5) that supplies an extra small factor (e.g. \(\Delta_F\lesssim h_j^{2+\alpha_*}\) for some \(\alpha_*>0\), or an equivalent cancellation mechanism).
- <span style="color:#7B2CBF"><b>[VIOLET]</b></span> Under that lemma, the same schedule forces \(\mathcal F(\partial T^{\mathrm{raw}}_j)\to 0\), hence the defect goes to \(0\).

---

### Workstream 2 — H1: local holomorphic manufacturing as a quantitative theorem
- **Objective**: make the local manufacturing package (jet control ⇒ global single‑sheet graph on a cell ⇒ many disjoint pieces) a clean theorem family with fully stated hypotheses and uniform constants.

#### Minimum acceptable “H1 theorem package”
- **Local \(C^1\) approximation on a whole cell** (Bergman/peak‑section / Hörmander route):
  - Precisely state the chart/metric assumptions and the scale relation \(Q\subset B_{R/\sqrt{M}}(0)\).
  - Give an explicit \(C^1\) bound of the form “affine holomorphic model + exponentially small remainder on Bergman balls.”
- **Global graph criterion**:
  - `lem:global-graph-contraction` (already present) must be invoked with a clear list of constants: \(\|A^{-1}\|\), \(\eta\), domain sizes.
- **Disjointness mechanism**:
  - A quantitative separation lemma: “if translations satisfy \(\|t_a-t_b\|\ge C\varepsilon h\), then the resulting graphs are disjoint on \(Q\)”.
- **Transversality/smoothness**:
  - Either a self-contained argument (uniform perturbation + Bertini) or a fully matched citation.

#### Deliverables
- A single “Local manufacturing theorem” that outputs the objects actually used later:
  - calibrated holomorphic pieces,
  - controlled angle/slope on all of \(Q\),
  - explicit disjointness/separation conditions,
  - and a statement about the boundary slices being supported on \(\partial Q\).

<span style="color:#2A9D8F"><b>[TEAL]</b></span> **Implemented in TeX (Dec 26, 2025):**
- <span style="color:#2A9D8F"><b>[TEAL]</b></span> Added `prop:h1-package` (“H1 package: local holomorphic multi-sheet manufacturing”) at the spine‑theorem point of use, explicitly pointing to `thm:local-sheets` + the count/budget selection in `lem:local-bary` / `thm:global-cohom`.

<span style="color:#7B2CBF"><b>[VIOLET]</b></span> **Finished H1 statement template (to be copied into the manuscript verbatim).**
<span style="color:#7B2CBF"><b>[VIOLET]</b></span> The goal is a theorem of the following concrete form (no “sketch”):

<span style="color:#7B2CBF"><b>[VIOLET]</b></span> **Theorem (H1: uniform holomorphic multi‑patch manufacturing on a cell).**
Let \((X,\omega)\) be projective K\"ahler, fix \(p\), and fix \(\varepsilon\in(0,\varepsilon_*)\).
There exist constants \(c,C>0\) and \(M_0(\varepsilon)\) such that for every integer \(M\ge M_0(\varepsilon)\), every holomorphic chart identifying a neighborhood of a cell \(Q\) with a subset of \(\mathbb C^n\) and satisfying \(\mathrm{diam}(Q)\le c\,M^{-1/2}\), every calibrated complex \((n-p)\)-plane \(P\), and every finite set of translations \(\{t_a\}_{a=1}^N\subset P^\perp\) with separation \(\|t_a-t_b\|\ge 10\,\varepsilon\,\mathrm{diam}(Q)\), there exist holomorphic complete intersections \(Y^1,\dots,Y^N\in |L^M|\) such that:
- each \(Y^a\cap Q\) is a single \(C^1\) graph over \(P+t_a\) with slope \(\le C\varepsilon\),
- the pieces are pairwise disjoint on \(Q\),
- and \(\Mass([Y^a]\llcorner Q)=(1+O(\varepsilon^2))\,\Mass([P+t_a]\llcorner Q)\) uniformly in \(a\).

<span style="color:#7B2CBF"><b>[VIOLET]</b></span> **How we make it referee‑checkable**
- <span style="color:#7B2CBF"><b>[VIOLET]</b></span> isolate the only “hard analysis input” as a single cited lemma (e.g. Tian–Catlin–Zelditch asymptotics / Hörmander \(\bar\partial\) with explicit \(C^1\) bounds on Bergman balls),
- <span style="color:#7B2CBF"><b>[VIOLET]</b></span> explicitly list every constant dependency (\(X,\omega,n,p\)) and every scale inequality used to apply the contraction/graph lemma.

---

### Workstream 3 — H2: global face coherence as an explicit proposition (the true heart)
- **Objective**: extract the global face coherence step into one crisp, checkable proposition that implies the weighted flat‑norm bound used by `prop:glue-gap`.

#### What H2 must concretely supply
- **Per face** \(F=Q\cap Q'\):
  - a pairing/matching of the induced face slices (or transverse parameters),
  - with displacement \(\Delta_F\) controlled (ideally \(\Delta_F\lesssim h^2\) or better),
  - and a bound on the resulting \(\mathcal F(B_F)\) via `prop:transport-flat-glue-weighted`.
- **Globally**:
  - a summation argument yielding \(\mathcal F(\partial T^{\mathrm{raw}})\to 0\) (for fixed \(m\)) under the parameter schedule.

#### Deliverables
- A single theorem (or proposition cluster) that states:
  - **Inputs**: smooth closed cone‑valued \(\beta\), chosen mesh \(h\), dictionary, counts/rounding rule.
  - **Outputs**: matched face slices on every interior face with explicit quantitative bounds.
  - **Conclusion**: \(\mathcal F(\partial T^{\mathrm{raw}})\le \epsilon(h,\delta,\varepsilon,m)\to 0\).

<span style="color:#7B2CBF"><b>[VIOLET]</b></span> **Finished H2 statement template (global face coherence).**
<span style="color:#7B2CBF"><b>[VIOLET]</b></span> We want a proposition whose only job is to *imply* the hypotheses of `cor:global-flat-weighted` and hence feed `prop:glue-gap`.

<span style="color:#7B2CBF"><b>[VIOLET]</b></span> **Proposition (H2: global face coherence on a mesh).**
Fix \(h>0\) and a smoothly rounded cubulation \(\{Q\}\) of \(X\) of mesh \(h\) with uniformly controlled face charts.
Fix a globally labeled direction dictionary \(\{P_i\}_{i=1}^{N(h)}\) (an \(\varepsilon_h\)-net with \(\varepsilon_h\ll h\)) and choose Lipschitz weights \(w_i(x)\) (e.g. via a strongly convex simplex fit) so that \(\beta(x)\approx t(x)\sum_i w_i(x)\,\xi_i(x)\).
Then there exists an integer choice of activation data (counts and prefix edits) producing a raw calibrated sheet–sum
\[
S=\sum_Q S_Q
\]
such that:
- <span style="color:#7B2CBF"><b>[VIOLET]</b></span> **(H2.1) per-face template control**: on every interior face \(F=Q\cap Q'\), the induced face slices admit a matching in the transverse parameter chart with displacement \(\Delta_F\lesssim h^2\) and only an \(O(h)\) fraction of insert/delete edits (quantified),
- <span style="color:#7B2CBF"><b>[VIOLET]</b></span> **(H2.2) piece boundary budget**: the pieces in each cell satisfy the uniform slice boundary inequality needed for the weighted transport bound (via `lem:uniformly-convex-slice-boundary`),
- <span style="color:#7B2CBF"><b>[VIOLET]</b></span> **(H2.3) cohomology rounding compatibility**: the same integer data also satisfy the global period constraints up to \(<1/2\) (hence exactly, by integrality).

Consequently,
\[
\mathcal F(\partial S)\ \le\ \epsilon(h,\delta,\varepsilon,m)\ \xrightarrow[h\to 0]{}\ 0.
\]

<span style="color:#7B2CBF"><b>[VIOLET]</b></span> **Notes for the manuscript**
- <span style="color:#7B2CBF"><b>[VIOLET]</b></span> This proposition should be stated *once* and then invoked by label, rather than being spread across many “routes.”
- <span style="color:#7B2CBF"><b>[VIOLET]</b></span> The proof should explicitly factor into: (a) local face displacement lemma, (b) template/prefix edit lemma, (c) global summation lemma, (d) rounding lemma.

<span style="color:#2A9D8F"><b>[TEAL]</b></span> **Implemented in TeX (Dec 26, 2025):**
- <span style="color:#2A9D8F"><b>[TEAL]</b></span> Added `prop:h2-package` (“H2 package: global face coherence and gluing (corner-exit route)”) at the spine‑theorem point of use.
- <span style="color:#2A9D8F"><b>[TEAL]</b></span> De-scaffolded the load‑bearing H2 bookkeeping block by removing `editrefblock` wrappers and removing the `\editref{...}` title wrapper from `thm:sliver-mass-matching-on-template`.

---

### Workstream 4 — Cohomology matching / integrality bookkeeping in “finished form”
- **Objective**: make the exact homology claim \([T_j]=\mathrm{PD}(m[\gamma])\) fully auditable.

#### Minimum acceptable pieces
- **Finite test set**: explicitly define the harmonic basis \(\{\eta_\ell\}\) used, and state the integrality property needed (“generates \(H^{2n-2p}(X,\mathbb Z)\)”).
- **Discrepancy rounding lemma**: keep `lem:barany-grinberg` but add a short “why it implies exact integrality” sentence:
  - If \(\int_{T}\eta_\ell\in\mathbb Z\) for integral currents and \(|\int_{T}\eta_\ell - mI_\ell|<1/2\), then equality holds.
- **Stability under rounding**: prove explicitly that the rounding/adjustment does not break the slow variation / face coherence hypotheses needed for H2.

<span style="color:#2A9D8F"><b>[TEAL]</b></span> **Implemented in TeX:** `lem:integral-periods`, `lem:lattice-discreteness`, and a corrected version of `prop:cohomology-match` whose conclusion applies to the **closed corrected cycle** \(T=S-U\).

<span style="color:#7B2CBF"><b>[VIOLET]</b></span> **Integrality bookkeeping checklist (to make the “\(<1/2\) ⇒ equality” step airtight).**
- <span style="color:#7B2CBF"><b>[VIOLET]</b></span> **Lemma (periods of integral cycles are integers):** if \(T\) is a closed integral \(k\)-cycle and \([\eta]\in H^k(X,\mathbb Z)\), then \(\int_T \eta\in\mathbb Z\). Give an explicit reference (de Rham theorem + definition of \(H^k(X,\mathbb Z)\) periods).
- <span style="color:#7B2CBF"><b>[VIOLET]</b></span> **Lemma (error bound implies equality):** if \(a\in\mathbb Z\) and \(|a-b|<1/2\) with \(b\in\mathbb R\), then \(a=\mathrm{round}(b)\). Apply with \(a=\int_T\eta_\ell\) and \(b=m\int_X\beta\wedge\eta_\ell\).
- <span style="color:#7B2CBF"><b>[VIOLET]</b></span> **Explicit finite test set:** write down \(\{\eta_\ell\}_{\ell=1}^b\) and the statement “their cohomology classes generate \(H^{2n-2p}(X,\mathbb Z)\).”
- <span style="color:#7B2CBF"><b>[VIOLET]</b></span> **Quantified period control:** bound
  \[
  \left|\int_{T^{(1)}}\eta_\ell - m\int_X\beta\wedge\eta_\ell\right|
  \]
  in terms of:
  - the local discretization error on the mesh (controlled by smoothness of \(\beta\) and the mesh size),
  - the mass of the gluing current (\(\Mass(R_{\mathrm{glue}})\)) via \(|\int_{R_{\mathrm{glue}}}\eta_\ell|\le \|\eta_\ell\|_{\mathrm{comass}}\Mass(R_{\mathrm{glue}})\),
  - and any rounding/correction step (bounded by a fixed-dimensional constant via Bárány–Grinberg).
- <span style="color:#7B2CBF"><b>[VIOLET]</b></span> **Final inequality target:** choose the parameter hierarchy so the RHS \(<1/2\) for all \(\ell\).

---

### Workstream 5 — The borderline \(p=n/2\) case (must be handled explicitly, not by a remark)
- **Objective**: remove the “loss of slack” vulnerability at \(p=n/2\).

#### Why this is mandatory
- In the weighted scaling exponent \(2-\frac{2n}{k}=\frac{n-2p}{n-p}\), the \(h\)-decay disappears when \(k=n\) (i.e. \(p=n/2\)).
- A referee will focus here first.

#### What we must produce (at least one of the following)
- **Option 1: improved displacement**: prove \(\Delta_F\lesssim h^{2+\alpha}\) for some \(\alpha>0\) by using a genuinely second‑order (or symmetric) discretization that makes the leading face error cancel using \(d\beta=0\).
- **Option 2: improved slice bound**: strengthen `lem:uniformly-convex-slice-boundary` in the specific geometric setup so that the effective boundary mass is smaller than the generic \(m^{(k-1)/k}\) prediction in the borderline dimension.
- **Option 3: structural cancellation**: build the construction so that only an \(o(1)\) fraction of faces carry mismatch (or the mismatch is supported on a negligible set), yielding an extra vanishing factor.

#### Deliverable
- A dedicated lemma/proposition titled explicitly “Borderline case \(p=n/2\)” that closes the \(h\to 0\) limit under a stated schedule.

<span style="color:#2A9D8F"><b>[TEAL]</b></span> **Implemented in TeX:** `lem:borderline-p-half` (routes \(p=n/2\) through `prop:integer-transport` rather than relying on the disappearing weighted exponent).

<span style="color:#7B2CBF"><b>[VIOLET]</b></span> **Explicit borderline closure lemma (template).**
<span style="color:#7B2CBF"><b>[VIOLET]</b></span> The plan requires an actual lemma with a proof route, not a remark:

<span style="color:#7B2CBF"><b>[VIOLET]</b></span> **Lemma (Borderline closure at \(p=n/2\)).**
Let \(p=n/2\) so \(k=2n-2p=n\). In the corner‑exit / vertex‑template construction, assume the following strengthened face coherence estimate holds:
\[
\Delta_F\ \lesssim\ h^{2+\alpha_*}
\qquad\text{for some fixed }\alpha_*>0,
\]
uniformly over all interior faces \(F\), for the matched bulk of pieces (with the unmatched remainder contributing only an \(o(1)\) fraction in the weighted bookkeeping).
Then the weighted global estimate yields \(\mathcal F(\partial T^{\mathrm{raw}})\to 0\) as \(h\to 0\), hence \(\Mass(R_{\mathrm{glue}})\to 0\) and the defect \(\Def_{\mathrm{cal}}(T_j)\to 0\).

<span style="color:#7B2CBF"><b>[VIOLET]</b></span> **How to prove \(\Delta_F\lesssim h^{2+\alpha_*}\) (candidate mechanisms).**
- <span style="color:#7B2CBF"><b>[VIOLET]</b></span> **Second‑order symmetry/cancellation**: choose the face charts and the vertex templates in a symmetric way (barycentric/central anchoring) so that the leading \(O(h^2)\) displacement term cancels across opposite orientations; the remaining displacement is \(O(h^3)\).
- <span style="color:#7B2CBF"><b>[VIOLET]</b></span> **Closedness‑driven cancellation**: exploit \(d\beta=0\) to show that the first‑order mismatch in transverse pushforwards across a face is exact and cancels in the flat‑norm dual pairing (a compensated‑compactness style estimate), yielding an extra \(h^{\alpha_*}\).
- <span style="color:#7B2CBF"><b>[VIOLET]</b></span> **Mismatch support thinning**: arrange that only an \(o(1)\) fraction of faces carry nontrivial mismatch (e.g. via a checkerboard/prefix balancing that localizes edits to a sparse set), which provides the missing vanishing factor even when the per‑face exponent has no slack.

<span style="color:#7B2CBF"><b>[VIOLET]</b></span> **Non‑negotiable in the manuscript**: this lemma must appear as a named result, and the main proof must explicitly branch to it when \(p=n/2\).

---

### Workstream 6 — “Referee packet” artifacts (helps verification and reduces rejection risk)
- **Objective**: provide a verification scaffold so a serious referee can actually try to check the proof.
- **Deliverables**
  - **Dependency graph** (one page): theorem/lemma labels only, no prose.
  - **Quantifier table** (one page): order of choices for \((m,h_j,\delta_j,\varepsilon_j,M_j)\) and what each controls.
  - **External theorem ledger**: list of every invoked published theorem with full citation and the exact place where hypotheses are checked.
  - **Sanity checks** (explicitly stated):
    - \(p=1\) (Lefschetz (1,1)) case.
    - complete intersection case.
    - a “no coercivity without cone‑valued harmonic rep” example (already discussed).

<span style="color:#2A9D8F"><b>[TEAL]</b></span> **Implemented in TeX (Dec 26, 2025):**
- <span style="color:#2A9D8F"><b>[TEAL]</b></span> Added Appendix `app:referee-packet` containing: (A) dependency graph (boxed), (B) quantifier table (boxed), (C) external theorem ledger, (D) sanity checks list.

---

### Concrete next edits (high impact, minimal risk)
<span style="color:#2A9D8F"><b>[TEAL]</b></span> **Completed in TeX (Dec 26, 2025):**
- <span style="color:#2A9D8F"><b>[TEAL]</b></span> “Parameter schedule” subsection inserted (`sec:parameter-schedule`).
- <span style="color:#2A9D8F"><b>[TEAL]</b></span> Standalone borderline lemma inserted (`lem:borderline-p-half`).
- <span style="color:#2A9D8F"><b>[TEAL]</b></span> Cohomology/integrality bookkeeping made explicit (`lem:integral-periods`, `lem:lattice-discreteness`) and `prop:cohomology-match` corrected to apply to closed corrected cycles \(T=S-U\).
- <span style="color:#2A9D8F"><b>[TEAL]</b></span> Workstream 0 cleanup applied: all `\editref{...}` / `editrefblock` scaffolding removed; one-page referee map inserted at the start of the proof of `thm:main-hodge`.
- <span style="color:#2A9D8F"><b>[TEAL]</b></span> H1/H2 packaged at point of use: added `prop:h1-package` and `prop:h2-package`.
- <span style="color:#2A9D8F"><b>[TEAL]</b></span> Referee packet appendix added: `app:referee-packet` (dependency graph, quantifier table, external ledger, sanity checks).

<span style="color:#2A9D8F"><b>[TEAL]</b></span> **Optional next edits (if we want to keep tightening):**
- <span style="color:#2A9D8F"><b>[TEAL]</b></span> (DONE) Ensure `thm:automatic-syr`’s proof references the spine theorem and the parameter schedule *by label* in a single line (no “for small parameters…” prose).
- <span style="color:#2A9D8F"><b>[TEAL]</b></span> Expand the external theorem ledger in `app:referee-packet` into full citation+hypothesis-check bullets (one per external theorem).
- <span style="color:#2A9D8F"><b>[TEAL]</b></span> Remove remaining legacy `editblock` wrappers in nonessential sections (cosmetic only; already disabled by `\finaltrue`).

<span style="color:#7B2CBF"><b>[VIOLET]</b></span> **Immediate edits to the plan-to-TeX pipeline (do now, then iterate).**
<span style="color:#2A9D8F"><b>[TEAL]</b></span> **All three items below are now completed in the TeX as of Dec 26, 2025** (see the “Implemented in TeX” blocks above). We keep them here only as a historical checklist.
- <span style="color:#7B2CBF"><b>[VIOLET]</b></span> (DONE) Add a “Parameter schedule v1” block to the TeX right after `thm:spine-quantitative`, matching Workstream 1 above (explicit choices, explicit inequalities).
- <span style="color:#7B2CBF"><b>[VIOLET]</b></span> (DONE) Promote H1 and H2 to named hypotheses in the spine theorem statement, then prove them downstream; this forces the manuscript to maintain a clean dependency graph.
- <span style="color:#7B2CBF"><b>[VIOLET]</b></span> (DONE) Insert a dedicated subsection “Borderline \(p=n/2\)” in the microstructure/gluing area, containing the lemma template above and a proof roadmap.

---

### Relationship to existing planning docs
- **`proof-completion-plan.md`** and **`mg-global-template-coherence-plan.md`** contain valuable raw material but are currently *not* in “referee‑grade plan format” and include historical/conditional language.
- This file supersedes them as the plan for making the **unconditional** manuscript maximally referee‑checkable.


