## Proof Walkthrough — working through `Hodge_REFEREE_Amir-v1_AI_REFEREE_NOTES.md`

This note is a **worked pass** through the proof spine listed in
`docs/referee/Hodge_REFEREE_Amir-v1_AI_REFEREE_NOTES.md`, cross-checking against
the actual TeX source `Hodge_REFEREE_Amir-v1.tex` by **label**.

It is **not** a certification of correctness; it records what was verified at the level of
*logical interfaces + hygiene*, and highlights the **remaining high-risk math** that a human referee
still needs to audit.

---

### A. Main theorem `thm:main-hodge`

- **Location**: Theorem `thm:main-hodge`.
- **Claim**: Every rational Hodge class \(\gamma\in H^{2p}(X,\mathbb Q)\cap H^{p,p}(X)\) on smooth projective \(X\) is algebraic.
- **Mechanism in the TeX**:
  - Reduce to \(p\le n/2\) via Remark `rem:lefschetz-reduction`.
  - Signed decomposition Lemma `lem:signed-decomp`: \(\gamma=\gamma^+-\gamma^-\) with \(\gamma^-=N[\omega^p]\).
  - Lemma `lem:gamma-minus-alg`: \([\omega^p]\) (hence \(\gamma^-\)) is algebraic.
  - Theorem `thm:effective-algebraic`: cone–positive \(\gamma^+\) is algebraic.
  - Algebraic classes are a \(\mathbb Q\)-subspace \(\Rightarrow\) difference is algebraic.

- **Interface check added**:
  - Added Remark `rem:algebraic-class-convention` clarifying what “algebraic class” means and why these form a \(\mathbb Q\)-vector subspace.

---

### B. Hard Lefschetz reduction `rem:lefschetz-reduction`

- **Location**: Remark `rem:lefschetz-reduction`.
- **Core point**: For \(p>n/2\), write \(\gamma=[\omega]^{2p-n}\wedge\eta\) with \(\eta\in H^{2(n-p)}(X,\mathbb Q)\cap H^{n-p,n-p}(X)\).
- **Check** (rationality + Hodge type):
  - A clarifying sentence was added: since \([\omega]\in H^2(X,\mathbb Q)\cap H^{1,1}\), the Hard Lefschetz isomorphism is a **\(\mathbb Q\)-linear morphism of Hodge structures**, so its inverse preserves rationality and Hodge type.
- **Check** (hyperplane intersection count):
  - If \(Z\) has codimension \(n-p\), intersect with \(2p-n\) hyperplanes to reach codimension \(p\).

---

### C. Signed decomposition `lem:signed-decomp`

- **Locations**: Lemma `lem:kahler-positive`, Lemma `lem:signed-decomp`.
- **Role**: Reduce an arbitrary Hodge class to the “cone–positive” case by adding a large multiple of \([\omega^p]\).
- **Key uniformity check**:
  - Lemma `lem:kahler-positive` now includes an explicit **compactness argument** to produce a **uniform interior radius** \(r_0>0\) so that
    \(B(\omega^p(x),r_0)\subset K_p(x)\) for all \(x\).
- **Mechanism**:
  - Given a closed representative \(\alpha\) of \(\gamma\), let \(M=\sup_x\|\alpha(x)\|\).
  - Pick \(N\in\mathbb Q_{>0}\) with \(N>M/r_0\), then \(\alpha+N\omega^p\) is pointwise \(K_p\)-valued.

---

### D. Algebraicity of \([\omega^p]\): `lem:gamma-minus-alg`

- **Location**: Lemma `lem:gamma-minus-alg`.
- **Mechanism**:
  - Choose \(m\gg 0\) with \(L^{\otimes m}\) very ample.
  - Take \(p\) generic divisors \(D_1,\dots,D_p\in |L^{\otimes m}|\); set \(Z=D_1\cap\cdots\cap D_p\).
  - Then \(\mathrm{PD}([Z])=c_1(L^{\otimes m})^p=m^p[\omega^p]\), so \([\omega^p]\) is a \(\mathbb Q\)-linear combination of cycle classes.

---

### E. Closure principle: `thm:realization-from-almost`

- **Location**: Theorem `thm:realization-from-almost`.
- **Mechanism**:
  - Fixed class \(A=\mathrm{PD}(m[\gamma])\), integral cycles \(T_k\) with \([T_k]=A\) (mod torsion), and defect \(\Def_{\mathrm{cal}}(T_k)\to 0\).
  - Federer–Fleming \(\Rightarrow\) subsequence converges (flat) to an integral cycle \(T\).
  - Lower semicontinuity of mass + comass inequality \(\Rightarrow\) \(\Mass(T)=\langle T,\psi\rangle\), i.e. \(T\) is calibrated.
  - Calibrated (Kähler/Wirtinger) \(\Rightarrow\) positivity/type \((p,p)\) (Harvey–Lawson) + \(d\)-closed (since integral cycle).
  - King \(\Rightarrow\) holomorphic chain.

- **Hygiene fix applied**:
  - Removed an extra duplicated proof block that followed Lemma `lem:limit_is_calibrated`.

---

### F. SYR definition + theorem: `def:syr`, `thm:syr`

- **Locations**: Definition `def:syr`, Theorem `thm:syr`.
- **Role**: SYR packages the existence of a fixed-class integral cycle sequence with defect \(\to 0\).
- **Check** (torsion conventions):
  - The TeX consistently phrases the class constraint as \([T_k]=\mathrm{PD}(m[\gamma])\) in \(H_\*(X;\mathbb Z)/\mathrm{Tor}\) (equivalently in \(H_\*(X;\mathbb Q)\)).

---

### G. Automatic SYR: `thm:automatic-syr`

- **Location**: Theorem `thm:automatic-syr`.
- **Interface**:
  - Build a raw sheet current \(S_\epsilon\) as a sum of locally \(\psi\)-calibrated holomorphic pieces.
  - Use the gluing estimate Proposition `prop:glue-gap` to get a correction \(U_\epsilon\) with \(\partial U_\epsilon=\partial S_\epsilon\) and \(\Mass(U_\epsilon)\to 0\).
  - Use Proposition `prop:cohomology-match` (fed by `thm:global-cohom`) to force \([T_\epsilon]=\mathrm{PD}(m[\gamma])\) (mod torsion).
  - Use Proposition `prop:almost-calibration` to bound defect by \(2\Mass(U_\epsilon)\to 0\).
  - Apply Theorem `thm:syr` \(\Rightarrow\) holomorphic chain; projective \(\Rightarrow\) algebraic via Remark `rem:chow-gaga`.

- **High-risk (math) still to audit**:
  - The quantitative “transport \(\Rightarrow\) flat norm” machinery and its summations (`prop:transport-flat-glue*` etc.), which the TeX itself flags as the bottleneck (see Remark `rem:lean-bottleneck-flatnorm`).
  - Primary local statements to re-derive: Proposition `prop:transport-flat-glue`, Proposition `prop:transport-flat-glue-weighted`,
    and the geometric inequality Lemma `lem:uniformly-convex-slice-boundary` (used to control slice boundary mass in the sliver regime).
  - Note for `prop:transport-flat-glue`: the proof’s Step 1 is cleanest on an **interior face patch after edge-trimming**, where each face slice is a **cycle**
    (this is packaged later as Lemma `lem:face-slice-cycle-mass`). The TeX now states this explicitly in hypothesis (b).

#### G.1 Transport \(\Rightarrow\) flat norm (the quantitative hinge)

- **Unweighted transport-to-flat interface**: Proposition `prop:transport-flat-glue`.
  - Step 1 (homotopy/Lipschitz): once the per-slice boundary vanishes on the interior face patch (\(\partial\Sigma_y=0\)), the homotopy formula reduces to
    \(\Sigma_{y'}-\Sigma_y=\partial Q_{y\to y'}\) and the evaluation map \(y\mapsto \Sigma_y(\eta)\) has Lipschitz constant \(\lesssim h^{k-1}\) for \(k=2n-2p\).
  - Step 2 (Kantorovich–Rubinstein): the equal-total-mass hypothesis is used exactly to apply KR duality without a basepoint.
  - Step 3 (model error): `lem:flat-C0-deform` turns the \(C^0\) graph deviation \(\delta\sim \varepsilon h\) into a flat-norm error \(O(\varepsilon)\) per slice (summable across faces).

- **Weighted/sliver-compatible interface**: Proposition `prop:transport-flat-glue-weighted` + Corollary `cor:global-flat-weighted`.
  - The matching bound is written directly in terms of the equal-weight matching cost \(\tau_F=\inf_\sigma\sum_a\|u_a-u'_{\sigma(a)}\|\) times a per-slice weight \(\Mass(\Sigma(u_a))+\Mass(\partial\Sigma(u_a))\).
  - In the holomorphic corner-exit regime the slices are cycles and satisfy \(\Mass(\Sigma_F(u_a))\lesssim m_{Q,a}^{(k-1)/k}\) by Lemma `lem:face-slice-cycle-mass`, which is what makes the global summation in `cor:global-flat-weighted` workable.

#### G.1(bis) Borderline case \(p=n/2\)

- **Key point**: the naive scaling from `cor:global-flat-weighted` is not automatically enough at \(k=n\).
- **Patch in the TeX**: `lem:borderline-p-half` supplies a sufficient refined schedule (notably \(\varrho=o(\varepsilon)\)) to force
  \(\mathcal F(\partial T^{\mathrm{raw}})\to 0\) in the middle-dimensional regime.
- **Important consistency fix (disjointness at the footprint scale)**:
  - The corner-exit/sliver pieces live on **footprints of diameter** \(D_Q\asymp s\asymp \varrho h\) (not the full cube diameter \(h\)).
  - The TeX now phrases the within-direction separation needed for disjointness at the **footprint** scale: \(\|t_a-t_b\|\gtrsim \varepsilon D_Q\),
    via updates to `lem:sliver-stability`, `lem:sliver-packing`, `prop:finite-template`, and the schedule remarks. This prevents a hidden contradiction
    in the borderline regime \(\varrho=o(\varepsilon)\).

#### G.2 Local holomorphic direction manufacturing (where “finite nets” appear)

- **Projective tangential approximation**: Proposition `prop:tangent-approx-full` (built from Bergman/peak-section control, via `lem:bergman-control`).
  - **Audit fix**: `lem:bergman-control` had a scaling typo in the Bergman-kernel differentiation normalization; the TeX now uses \(N^{-(n+1/2)}\) (not \(N^{-(n+1)/2}\)) so the constructed \(1\)-jets are \(O(1)\) on \(N^{-1/2}\)-balls.
- **Finite nets at sample points**: Proposition `prop:dense-holo` should be read as a **finite net of calibrated directions at finitely many centers** covering a compact \(K\) at scale \(\varepsilon\), *not* as a finite family of submanifolds containing every point of \(K\) (which is impossible). The TeX statement now matches the proof’s construction (centers + direction nets at each center).

---

### H. Gluing correction: `prop:glue-gap`

- **Location**: Proposition `prop:glue-gap` + Lemma `lem:FF-filling-X`.
- **Mechanism**:
  - Start with \(\delta=\mathcal F(\partial T^{\mathrm{raw}})\) (integral flat norm).
  - Decompose \(\partial T^{\mathrm{raw}}=R_0+\partial Q\) with \(\Mass(R_0)+\Mass(Q)\le \delta+\eta\).
  - Fill \(R_0\) using a Federer–Fleming/Nash-embedding argument on \(X\), giving \(\Mass(Q_0)\le C_X\Mass(R_0)^{k/(k-1)}\).
  - Set \(R_{\mathrm{glue}}:=-(Q+Q_0)\), so \(\partial R_{\mathrm{glue}}=-\partial T^{\mathrm{raw}}\) and \(\Mass(R_{\mathrm{glue}})\le \delta + C_X\delta^{k/(k-1)}\).

---

### I. Exact class / period locking: `prop:cohomology-match`

- **Location**: Proposition `prop:cohomology-match`, Lemmas `lem:integral-periods`, `lem:lattice-discreteness`.
- **Mechanism**:
  - Use fixed-dimension discrepancy rounding (Lemma `lem:barany-grinberg`) on the “marginal sheet” period vectors \(v_{Q,j}\) to make all periods simultaneously close to targets.
  - Choose the gluing correction \(U_\epsilon\) with \(\Mass(U_\epsilon)\) small enough that \(|\int_{U_\epsilon}\Theta_\ell|<1/4\) for all \(\ell\).
  - Use integrality of periods for closed integral cycles + lattice discreteness to lock periods exactly.

---

### J. Almost-calibration: `prop:almost-calibration`

- **Location**: Proposition `prop:almost-calibration`.
- **Mechanism**:
  - For \(T_\epsilon=S-U_\epsilon\) with \(\Mass(S)=\int_S\psi\) and \(\Mass(U_\epsilon)\to 0\), show
    \(0\le \Def_{\mathrm{cal}}(T_\epsilon)\le 2\Mass(U_\epsilon)\to 0\).

- **Hygiene fix applied**:
  - Removed a duplicated second proof so the proposition has a single proof block in the TeX.

---

### Hygiene fixes applied while working through the proof spine

- Removed stray duplicated proof blocks after:
  - Lemma `lem:radial-min`
  - the distance-to-cone proposition in the calibrated-cone preliminaries
  - Lemma `lem:limit_is_calibrated`
  - Proposition `prop:almost-calibration`
- Removed a duplicated “correction current” remark header.
- Corrected impossible “infinite / arbitrarily long \(\delta\)-separated list in a bounded box” phrasing in the corner-exit template section:
  for fixed \(\delta>0\) the list is finite, with length \(N(\delta)\to\infty\) only as \(\delta\downarrow 0\).
- Corrected the master **grid** template quantifiers in `prop:integer-transport`:
  for fixed \((h,\delta_\perp)\), \(B_{C_0\varrho h}(0)\cap \delta_\perp\mathbb Z^{2p}\) is finite, so the TeX now uses a finite list \((y_a)_{a=1}^{N_*}\)
  and requires prefix lengths \(N_F\le N_*\).
- Fixed a small quantization-proof slip in `lem:sphere-quantize` (“duplicate points” would break separation); the TeX now selects \(N\) points from a sufficiently large maximal separated set.
- Confirmed by automated scan: **no duplicate `\label{...}`** identifiers in `Hodge_REFEREE_Amir-v1.tex`.


