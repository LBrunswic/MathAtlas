# BBS, *Collisions of particles I*: a review against the gx library, with a roadmap to 3+1

*2026-11-02, node1. The review is read-only: no Lean was written and no register was touched. The
source is arXiv:1010.3602 v1 (`sources/README.md`). `TeX l.N` refers to `sources/1010.3602/eprint/colI_v1.tex`.
Every Lean declaration cited below was located by name on 2026-11-02, with paths relative to the hub
root. A tag **[r]** marks this review's own derivation, which the paper does not state.*

**Rulings in force (the author, 2026-11-02).**
- **Flat first.** The link layer is model-free. The only suspension built is Sing HS^n → Sing E^{1,n}.
- **The full 3+1 stratification** is in scope: codimensions 2, 3 and 4.
- **Architecture:**
  - lean-gx carries the *general theory of suspensions* and the *link theory in locally affine
    spaces*.
  - Above that comes the *link by signature*.
  - That then splits into a **Riemannian** branch (spherical, Euclidean, hyperbolic) and a
    **Lorentzian** branch, which inherits the ETT causal structure from lean-causal.

---

## 0. The paper in one paragraph

BBS study 2+1 spacetimes of constant curvature (AdS in the paper) with cone singularities along a
graph.

- **Links.** A neighbourhood of a singular point x is the *suspension* e(Σ_x) of its link Σ_x
  (TeX l.520–523). The link is a topological 2-sphere carrying a **singular HS²-structure**. HS² is
  the sphere of rays of R^{1,2} under SO₀(1,2), and it splits into five pieces: ℍ²_±, ∂ℍ²_± and dS²
  (l.581–596).
- **Singularities of the link.** A singular point p of Σ_x is in turn the suspension 𝔢(L) of a
  (Γ_p, ℓ(p))-circle L. Here Γ_p is the **pointwise** stabiliser of the ray p, and ℓ(p) is the circle
  of rays of T_pHS² (l.762–783).
- **Singular lines.** The (Γ_p, ℓ(p))-circles are classified through ℝP¹-circles (§3.3.1,
  l.673–760). That classification gives the singular lines (Prop `pro:classising`, l.531):
  - massive particles, photons and tachyons;
  - BTZ-like lines, extreme or not;
  - Misner lines;
  - lines of degree k ≥ 4.
- **Causality** (§3.6) excludes Misner lines and degree ≥ 4 (Def `def:Hcausal`, l.1114).
- **Interactions** are the points whose link is not a single suspension. For positive causal
  interactions the link is one of four types (Thm `tm:thierry`, l.2175), proved by Poincaré–Hopf and
  Poincaré–Bendixson on the de Sitter regions (§5).
- **Polyhedra.** Convex polyhedra in HS³ produce interactions (§4), and the converse holds in a
  special case (Thm `tm:converse`, l.1832, via Schlenker 2001, Thm 1.3).
- **Global hyperbolicity and examples.** §6 extends global hyperbolicity to the singular setting
  (time functions, Cauchy splitting, maximal extensions). §7 builds AdS examples.

**The structural fact this review rests on.** The whole local theory of §3 depends on the ambient
model **only through the suspension e(·)**. Everything else lives on HS² and its point-links. RamcovGX
already names this (l.734–741: the BBS functor Sing HS² → Sing E^{1,2}, as a lift of `susp`). So
does the author's thesis: `papers/gx/sources/thesis/these.tex` l.960–1007 describes the celestial
vault (SO(1,n), HS^n) with its five orbits, and l.3569–3640 (commented out) is a draft of the
(G,X)-celestial suspension. Neither is formalised. **That draft is the blueprint for layer L0
below.**

---

## A. Paper map

The tags in the last column mean:
- **link**: lives on HS² or ℓ(p), the same in every model and the same in 3+1 at the right
  codimension;
- **flat**: AdS-stated but transfers to E^{1,2} with the cone suspension;
- **AdS**: depends on conjugate points or on AdS planes;
- **2D**: depends on surface topology.

| # | TeX l. | statement | content | tag |
|---|---|---|---|---|
| 1 | 531 | Prop `pro:classising` | list of singular-line types | link (types), flat (causal behaviour) |
| 2 | 573–609 | §3.1 | HS², its five pieces, and fixed points of elliptic, parabolic and hyperbolic g ∈ SO₀(1,2) | link; n-dimensional at l.1563 (HS³) |
| 3 | 615 | Def | HS-surface = (SO₀(1,2), HS²)-surface; canonically oriented, dS parts time-oriented | link |
| 4 | 625–657 | §3.2 | suspension e(Σ): AdS rays, truncated at the conjugate points p^± in ℍ²_± | **AdS**; flat analogue is the cone |
| 5 | 658–659 | claim | "every HS-structure on S² is HS²", so e(HS²) = E(p) is regular | link; proof not given (§F, Q4) |
| 6 | 673–760 | §3.3.1 | ℝP¹-circles: elliptic (angle), degree k ≥ 1 (k, [g]), degree 0; ± parabolic classes; proof by the developing map | link, **every dimension** (§D) |
| 7 | 762–768 | Def | (Γ_p, ℓ(p))-circle, Γ_p **pointwise** stabiliser | link |
| 8 | 775–783 | constr. | 𝔢(L): the two-apex suspension inside HS², singular at p and −p | link |
| 9 | 785–802 | list | time-like (p ∈ ℍ²_±), space-like (p ∈ dS²) and light-like (p ∈ ∂ℍ²_±) singularities | link |
| 10 | 819, 828, 842 | Defs | i^±(ℓ(p)) and i^±(L): future and past arcs | link |
| 11 | 850–853 | claim | the ℝP¹-structure plus i^±(L) determine the singularity | link; **left to the reader**, owed |
| 12 | 860–924 | enum. 1–5 | timelike; spacelike deg 0 (past/future BTZ-like, Misner); lightlike deg 0 (cuspidal, extreme BTZ-like); spacelike and lightlike deg k ≥ 1, k **even**, ± | link |
| 13 | 926 | Remark | positive ≇ negative hyperbolic (Γ_p, ℓ(p))-circles | link |
| 14 | 934 | Rem `rk:p-p` | the antipodal pairing p̄ ↔ −p̄; cuspidal ↔ extreme BTZ-like | link |
| 15 | 948 | Def | singular HS-surface (discrete singular set) | link |
| 16 | 957 | Def | singular AdS spacetime: locally e(Σ) | flat |
| 17 | 963 | obs. | manifold ⇒ every Σ_x ≅ S² | link |
| 18 | 969 | Def `def:singline` | singular line versus interaction | flat |
| 19 | 978–994 | claim | interactions are discrete and closed; the type is constant along a line | flat |
| 20 | 1018–1062 | §3.6 | local future = e(ℍ⁺_x); BTZ has no future; deg k gives k/2 future components; Misner has CTCs | flat |
| 21 | 1066 | Lemma `le.CTC` | e(Σ) has a CCC ⇔ the dS region of Σ does; short CCCs | flat, any dim **[r]** |
| 22 | 1114 | Def `def:Hcausal` | causal = no degree ≥ 4, no CCC (no Misner) | link |
| 23 | 1142–1163 | §3.7.1 | massive particle by wedge gluing; θ > 2π allowed | flat |
| 24 | 1166 | Rem | mass m = 1 − θ/2π | link |
| 25 | 1193–1237 | §3.7.2 | tachyon pair (c, c₊) by the conjugate-point construction; c positive, c₊ negative | **AdS** |
| 26 | 1268–1293 | §3.7.2 | two alternative tachyon recipes: remove or insert the wedge V between spacelike half-planes S₁, S₂; or cut along the null half-plane L₁⁺ and reglue by a boost, positive iff γ maps L₁⁺ into its causal past | **flat** (no conjugate points used) |
| 27 | 1299 | Rem `rk.cuttachyon2` | HS-version: cut dS² along a light-like ray, reglue | link |
| 28 | 1332 | Rem `rk:degk` | degree 2k = k-branched cover of degree 2 | link (ties to gx `Branched/*`) |
| 29 | 1349 | §3.7.3 | Misner by gluing the kept wedge V | flat |
| 30 | 1368–1391 | §3.7.4 | BTZ-like lines via (c, c₊), regular part E/⟨γ₀⟩ | **AdS** construction; flat analogue below |
| 31 | 1404–1455 | §3.7.5 | photon via (c, c₊) [AdS]; alternative: cut along the null half-plane L⁺ [flat]; extreme BTZ "left to the reader" | mixed |
| 32 | 1457–1501 | Rems | photon naming; positive photons attract; no ± for BTZ; deformation elliptic → light-like → space-like | link |
| 33 | 1508 | Def | positive: cone angles < 2π, every deg ≥ 2 singularity positive | link |
| 34 | 1563–1588 | §4.1 | HS³: five components, a projective model in the double cover of ℝP³ | link (n-dimensional) |
| 35 | 1590–1726 | §4.2–4.3 | convex polyhedra in HS³ (bi-hyperbolic, hyperbolic, compact) and their induced HS-structures (Schlenker 1998, 2001) | 2D links, a 3-dim ambient |
| 36 | 1797, 1821 | Rem, Def | positive mass: closed spacelike geodesics in dS are < 2π | link |
| 37 | 1832 | Thm `tm:converse` | positive causal HS-sphere (two discs, no escape) is induced by a polyhedron ⇔ positive mass; unique, bi-hyperbolic | **external** (Schlenker 2001) |
| 38 | 1860–1930 | §5, §5.1 | decomposition into photons, hyperbolic and dS regions; two ℝP¹-structures on a photon circle (Mess Prop 17) | link + 2D |
| 39 | 1938 | Prop `pro.hypdegree0` | a non-disc hyperbolic region ⇒ the adjacent photon circle is hyperbolic of degree 0 | **2D** |
| 40 | 2035 | Cor | dS region is an annulus, disc or sphere, with ≤ 2 BTZ (**Poincaré–Hopf**) | **2D** |
| 41 | 2046 | Cor `cor.Lclosed` | limit sets of isotropic leaves (**Poincaré–Bendixson**) | **2D** |
| 42 | 2056 | Prop `pro.hyphyp` | the dS region next to a non-disc hyperbolic region | **2D** |
| 43 | 2175 | Thm `tm:thierry` | positive causal HS-spheres: causally regular / black-or-white-hole interaction / Big Bang–Crunch / white-hole + black-hole | **2D** |
| 44 | 2318–2367 | §6.2 | achronal, edgeless and spacelike sets in singular spacetimes | flat (ETT) |
| 45 | 2394–2422 | Thm, Lemma | time function ⇔ stable causality ([BEE96]); singular ⇔ regular part | flat (ETT) |
| 46 | 2476, 2552 | Prop `pro.ghtime`, Cor `cor.splitting` | GH ⇒ Cauchy time function, M ≅ S × ℝ | flat (ETT) |
| 47 | 2582–2686 | §6.5 | Cauchy embeddings; maximal extension exists and is unique; uniqueness fails with new interactions (l.2766) | flat (ETT / CBG) |
| 48 | 2782– | §7 | AdS global examples, surgery | **AdS**, out of scope |

**Reading.** Rows 2–15, 22, 24, 27–28 and 32–34 make up the **link layer**: about two thirds of §3,
and none of it depends on the model. Rows 4, 25, 30 and the (c, c₊) half of 31 are the *only*
AdS-specific parts of §3. Each has a flat substitute: the cone suspension, and the alternative
recipes of rows 26 and 31. All of §6 is causal theory that ETT already carries in the flat
topological setting.

---

## B. The layered architecture, and what each layer finds in the libraries

### L0 — the general suspension (lean-gx)

**Target.** The *structure conique* and *(G,X)-suspension céleste* of a **discarded draft**:
`these.tex` l.3560–3677 is commented out and is **not part of the thesis** ("commented out for a
reason", the author, 2026-11-03). The target is RamcovGX l.734's lift of `susp`; L0 is new theory
built from that draft:
- A **conical structure** at p ∈ X: a neighbourhood U_p, a link X_p, and a homeomorphism
  φ_p : U_p → susp(X_p) with φ_p(p) = O, compatible with the radial structure under the stabiliser.
- From these data, an induced action of the stabiliser on X_p (the draft argues it is well-defined).
- A functor susp_{(G,X)} from Sing(G_p, X_p) to Sing(G, X): charts are φ_p⁻¹ ∘ susp*(φ_i) on
  susp*(Reg Σ).
- Regularity at O iff Σ is the model link (for sphere links).

**What exists:**
- `GX.Susp` — `lean-gx/GX/Singular/Suspension.lean:108`. Topological, one apex, ℝ₊ radius.
- `susp_portly` — Suspension.lean:549. If U is portly, so is susp*(U). **This is exactly the
  support condition the a.e. atlas needs**, as in the draft's argument.
- `dInftyHomeomorphSusp` — :868. 𝔻_∞ = susp(ℝ).
- The singular layer:
  - `SingularGXStructure` — `GX/Singular/Atlas.lean:1509`;
  - `IsAEAtlas` — :181;
  - `IsPortly` — `GX/Topology/Portly.lean:89`;
  - `singular_developing_theorem` — `GX/SingularII/Developing.lean:769`;
  - `IsTame` — `GX/SingularII/Tame.lean:137`.
- Analyticity hypotheses: `IsRigidAction` and `IsAnalyticAction` — `GX/Structure/Basic.lean:113,118`.

**Gaps:**
- The geometric suspension itself. gx records it as missing. `TroyanovSuspensionTheorem`
  (`lean-gx/scaffold/GXScaffold/SingularII/Models.lean:885`) is a **named external** (DEC-69)
  precisely because "`GX.Singular.Suspension` is topological" (Models.lean, docstring near l.187).
  L0 would discharge the suspension half of that external; Troyanov's angle condition stays external.
- Which stabiliser to use (§F, Q2). The commented-out draft (l.3569) uses the full stabiliser G_p. BBS use the pointwise
  stabiliser Γ_p of the ray, which excludes "spin" (RamcovGX l.691, "without spin").

**Correction to the plan.** A two-apex suspension is *not* needed for the definitions. BBS Def
(l.948) only asks for a neighbourhood isomorphic to an *open subset* of 𝔢(L), and a neighbourhood of
p is one-apex. The two-apex 𝔢(L) is needed only for global statements: Rem `rk:p-p` and the fact that
a singular line's points all share one link (l.978–983).

### L1 — links in locally affine spaces (lean-gx)

**Target.** X = V affine, G ≤ Aff(V):
- The link of any point is (L, S(V)), with L the linear part of the stabiliser and
  S(V) = (V∖0)/ℝ₊*.
- The suspension of a singular (L, S(V))-manifold is a cone, and every chart change is **linear**.
- The flat Lorentzian case is the instance V = R^{1,n}, L = SO₀(1,n).

**What exists:**
- `LorentzIsom0` — `GX/Singular/Quotient.lean:2625`. Isom₀ of any form, on any V.
- `quotientBase` / `quotientBase_ruled` — Quotient.lean:1431, 7387. Γ\(𝔻_∞ × Z) models with a free
  factor Z, so products "transverse cone × ℝ^k" come for free.
- `conical` — :1987, any dimension.
- `ConicalSpace` — :5151.
- `isRigidAction_affineEquiv` — :2371, scoped.

**Gaps:**
- S(V) as a type with its L-action.
- The theorem that the cone of an (L, S(V))-chart is an (Aff, V)-chart.
- A **bridge between the suspension models and the quotientBase models**: e(𝔢(L)) ≅ (line) ×
  (transverse cone). gx builds its line models as D(r, θ, z) = g_θ · (x₀ + r v + z u). BBS build
  them as suspensions. Both should be proved to agree.

### L2 — links by signature

**Target [r].** Let V carry a form of signature (p, q). Then:
- S(V) splits by the sign of Q.
- For a ray [v] ∈ S(V), the point-link is ℓ([v]) = S(V/ℝv) under the pointwise stabiliser Γ_v.
- A stratum with tangent subspace W has normal link S(V/W) under the pointwise stabiliser of W.

For V = R^{1,n} the three cases are:

| [v] | Γ_v (pointwise) | ℓ([v]) = S(V/ℝv) | recursion |
|---|---|---|---|
| timelike, Q(v) < 0 | SO(n) | S^{n−1}, round | the Riemannian spherical branch (Thurston) |
| spacelike, Q(v) > 0 | SO₀(1, n−1) | HS^{n−1} | **the same layer, one dimension down** |
| null, Q(v) = 0 | E(n−1) = SO(n−1) ⋉ ℝ^{n−1} (null rotations) | E^{n−1}₊ ⊔ S^{n−2} ⊔ E^{n−1}₋ | the Riemannian Euclidean branch |

For the null case: the hemisphere {B(u, v) < 0}/ℝv is the horospherical affine (n−1)-plane, carrying
Euclidean isometries. The equator S(v^⊥/ℝv) is the set of directions tangent to the light cone.

**Check at n = 2:** these give (SO(2), S¹), then (SO(1,1), HS¹) with four light-like directions, then
(ℝ, two affine arcs + two points). That is exactly BBS l.788–802 and the arcs i^±(ℓ(p)) of l.828–838.

The thesis (l.1002) writes (Aff(ℝ), ℝP¹) for the null case. That is the **full** ray stabiliser,
including the boost along v; see §F, Q2.

**What exists** (lean-causal, generic in d):
- `Minkowski n` — `lean-causal/Causal/Minkowski.lean:72`;
- `minkQ`, `minkB` — `Causal/Flat/Form.lean:60,63`;
- `lorentz d` (SO₀(1,d)) — Form.lean:132;
- `isom d` — :198;
- `linearPart` — :202;
- `IsElliptic`, `IsHyperbolic`, `IsUnipotent`, `IsLoxodromic`, `IsParabolic` —
  `Causal/Flat/Isometries.lean:344–369`;
- `PenroseSphere d` (= ∂ℍ^d), `nullVec`, `isomPenrose` — `Causal/Flat/Penrose.lean:137,140,458`;
- `hyperboloid` — `Causal/Flat/Achronal.lean:437`.

**Gaps:**
- **HS^n is not a type anywhere.** Only its null part exists, as `PenroseSphere`.
- No dS^n, no ℍ^n as a type (the hyperboloid appears only in proofs).
- No point-link S(V/ℝv) and no pointwise stabilisers.
- `lorentz d` is *not* proved to be the identity component (disclosed in Form.lean).

### L3a — the Riemannian branch: spherical, Euclidean, hyperbolic

**Target:**
- The Thurston iteration Sing S^{n−1} → Sing S^n (sin² r), Sing S^{n−1} → Sing E^n (r²), and
  Sing S^{n−1} → Sing ℍ^n (sinh² r).
- For L2's null case, Sing E^{n−1}-links.

**What exists:**
- `conical` and `conical_isomPlus` — Quotient.lean:1987, 5399. Euclidean cones C_α × ℝ^{n−2}.
- `Cone` — :3736.
- `PoincareDisc`, `HypIsom` — `GX/Hyperbolic/Plane.lean:430,527`. The Poincaré disc, with an
  analytic action.
- In lean-causal: `Cone α` — `Causal/Model/Cone.lean:409`. A metric 2-cone; `apex_not_euclidean` —
  :732.
- `TroyanovSuspensionTheorem` (named external).

**Gaps:**
- No round S^n with SO(n+1).
- **HS gluing needs the Klein model, and gx has only the Poincaré disc** (conformal). Either a
  Klein↔Poincaré bridge, or ℍ^n defined directly as the timelike part of HS^n, which is what BBS do
  (l.593).

### L3b — the Lorentzian branch, inheriting ETT

**Target:**
- HS^n = S(R^{1,n}) under `lorentz n`, with five orbits.
- The flat suspension Sing HS^n → Sing E^{1,n} over `(isom n, Minkowski n)`.
- The singular line models.
- The causal statements of rows 20–22, read through ETT's `flatCausality`.

**What exists:**
- `flatCausality` — `Causal/Flat/IsomCausal.lean:440`.
- `FlatSpacetime` — `Causal/Flat/FlatSpacetime.lean:604`.
- The bridge `isAnalyticAction_flatIsom` — `lean-gx/scaffold/GXScaffold/Lorentz/Bridge.lean:342`.
- In 2+1 only, over `MinkIsom0` on ℝ×ℂ (Quotient.lean:2670):
  - `massive_particle`, `massive_particle_intended` (:2823, :5741);
  - `btz_whitehole_isom0`, `btz_blackhole_past_isom0` (:5675, :5918);
  - `misner_isom0_general`, `misner_variations_ruled` (:6778, :7364).
- The static massive model `Massive α` — `Causal/Model/Massive.lean:125`.
- `staticCausality` — `Causal/Static.lean:648`.
- `BTZAxioms`, `SingularFlatAxioms` — `Causal/SingularFlat.lean:150,173`.
- `existsUnique_causality_singularGX` — `Causal/GXSingular.lean:215`.

**Gaps:**
- The cone suspension over `Minkowski n`.
- Tachyon and photon models.
- Every model in every dimension other than 2+1.
- A singular-locus axiom that is not 1-dimensional.

**Flat Lemma 3.12 [r].**
- On the future cone e(ℍ⁺), the metric is −dt² + t² g_hyp, so t is a time function.
- A homothety r ↦ εr is a conformal map with constant factor, so it shrinks CCCs.

The argument of l.1073–1101 therefore transfers to E^{1,n} for every n, more simply than in AdS.

---

## C. Item by item: what BBS would bring to the libraries, and what blocks it

| BBS concept | layer | existing anchor | gap | owner |
|---|---|---|---|---|
| HS^n, five orbits, fixed-point classification (rows 2, 34) | L2 | `lorentz d`, `PenroseSphere d`, `IsElliptic`/`IsHyperbolic`/`IsParabolic` | HS^n as a type; orbits; the action is analytic (`IsAnalyticAction`) | new |
| HS-surface, singular HS-surface (rows 3, 15) | L0 + L2 | `SingularGXStructure`, `IsAEAtlas` | instance at (`lorentz n`, HS^n) | new |
| suspension e(Σ) (row 4, flat) | L0 + L1 | `Susp`, `susp_portly` | the geometric lift; linear chart changes; regular at O iff Σ = HS^n | gx (L0, L1) |
| ℝP¹-circles (row 6) | L2 (n = 1) | `developing_theorem` (`GX/Structure/Developing.lean:454`), `DInfty` = susp(ℝ) | universal cover of PSL(2,ℝ) acting on the θ-line; the case analysis | new |
| (Γ_p, ℓ(p))-circles, i^± (rows 7–14) | L2 | — | everything | new |
| degree 2k = k-branched cover (row 28) | L0 | `IsBranchedCovering` (`GX/Branched/Basic.lean:118`), `MaxBranchedCover` (`GX/Branched/Universality.lean:757`) | the statement is a direct instance **[r]** | gx machinery |
| massive particle (row 23) | L3b | `massive_particle_intended`, `Massive α` | suspension model ≅ quotient model (the L1 bridge) | — |
| **tachyon, photon** (rows 25–27, 31) | L3b | — (`Quotient.lean:187–200` explains why gx did not state them) | see below | new |
| BTZ-like (non-extreme) and Misner (rows 29–30) | L3b | `misner_isom0_general`, `misner_variations_ruled` ("Misner / BTZ variations with boosts") | match against BBS's degree-0 hyperbolic circles: I = i⁺ / i⁻ / spacelike arc | — |
| **extreme BTZ-like (row 31) = E₀** | L3b | gx `btz_whitehole_isom0` is the *extreme* one (parabolic `parabAff`, null `u`); ETT `BTZAxioms` | the suspension of a light-like degree-0 circle **constructs E₀** | report to the gx and Barbot sessions |
| causality of lines, Lemma 3.12, causal / positive (rows 20–22, 33) | L3b | `flatCausality`, `staticCausality` (static case only) | the non-static causality of e(Σ) | — |
| interactions, Theorem 5.6 (rows 38–43) | L2 + 2D | — | Poincaré–Hopf and Poincaré–Bendixson are not in mathlib | new, heavy |
| polyhedra (rows 35–37) | external | — | Schlenker 2001 as a named external | new |
| global hyperbolicity (rows 44–47) | ETT | Geroch splitting / CBG in lean-causal, `barbot_A` / `barbot_B` (`Causal/Flat/Classification.lean:2530,2695`), `LocalModel` (`Causal/CBG/Geometry.lean:441`) | `SingularFlatAxioms` takes each singular component to be a curve | Barbot / ETT |

**Three payoffs.**

1. **BBS supply the tachyon and photon models gx deliberately left unstated.**
   `GX/Singular/Quotient.lean:187–200` refuses RamcovGX l.682 because "the paper gives no developing
   map, no element of PSL(2,ℝ) nor which of its lifts to ℝP¹~ generates Γ".
   - BBS §3.3.1 gives exactly that datum: the holonomy δ^k g with k = 2, g hyperbolic (tachyon) or
     parabolic (photon), its sign fixed by repelling or attracting at the left end of i⁺ (l.893–922).
   - BBS l.1268–1293 and l.1443–1447 give flat cut-and-paste recipes.
   - Lean-side reason this is not a one-line instance [r]: `GammaA α` (Quotient.lean:1310) acts by the
     *translation* θ ↦ θ + kα. Every current model develops through a **one-parameter group** g_θ, and
     such an orbit never leaves one arc between fixed points, which gives degree 0. A degree-2 line
     needs a ℤ-action on the θ-line by a lift of δ²g. So either `quotientBase` is generalised from
     `GammaA` to an arbitrary free, proper ℤ-action on the θ-line, or the model is built as a
     suspension.
2. **Terminology bridge: Brunswic's "BTZ" is BBS's *extreme* BTZ-like.** gx's BTZ white and black
   holes are light-like with parabolic holonomy (`btzDev`, Quotient.lean:2975, `parabAff`), and so is
   the thesis/ETT E₀. BBS's unqualified "BTZ-like" is space-like with hyperbolic holonomy (degree 0,
   I = i^±). On the flat side that one is gx's boost family, `misner_btz` and its variations. The
   names must be aligned before any shared statement is made.
3. **E₀ by construction.** ETT never constructs E₀ (`defi:causal_E0` is a bucket-D row, and its facts
   are `BTZAxioms` fields), and gx's `scaffold/GXScaffold/BTZ/LocalModel.lean` has five open
   obligations. The flat suspension of a light-like degree-0 circle with I = i⁻(ℓ(p)) (l.887–888) is an
   explicit model, with its developing map. **Not acted on here**; to be offered to both sessions.

---

## D. 3+1: the stratification

Let M⁴ be a singular flat spacetime, locally the suspension of singular HS³-spheres. A point x of the
singular set has a link Σ_x ⊂ HS³ (up to structure). The **codimension** of x is 4 minus the
dimension of the stratum through it.

### Codimension 2: sheets

The tangent plane P of the sheet is a 2-plane. Its pointwise stabiliser acts on the circle of normal
rays S(V/P):

| P | normal geometry | Γ_P | sheet types |
|---|---|---|---|
| Lorentzian (timelike sheet) | Euclidean ℝ² | SO(2) | **massive cosmic string**, angle θ, mass 1 − θ/2π |
| Riemannian (spacelike sheet) | Minkowski ℝ^{1,1} | SO₀(1,1) | **tachyonic sheet** (deg 2, ±), **BTZ-like** past/future, **Misner**, deg 2k |
| degenerate (null sheet) | degenerate ℝ² | null rotations ≅ ℝ | **photon sheet** (deg 2, ±), **extreme BTZ-like**, cuspidal, deg 2k |

**[r]** The (Γ_P, S(V/P))-circles are BBS's (Γ_p, ℓ(p))-circles *verbatim*: same groups, same
circle, same i^± arcs. So **§3.3 holds in every dimension at codimension 2**, and the ℝP¹-circle
classification (row 6) is dimension-generic infrastructure rather than a 2+1 artefact. Locally the
model is (2+1 BBS line model) × ℝ, which `quotientBase`'s free factor Z already accommodates.

### Codimension 3: lines where sheets meet

The tangent line is ℝv. The link of the corresponding point p ∈ Σ_x is ℓ(p) = S(V/ℝv), a 2-sphere
(the L2 table at n = 3):

| v | link of the junction | what classifies it |
|---|---|---|
| timelike | a **spherical cone 2-sphere** (SO(3), S²); k ≥ 3 cone points = k timelike sheets meeting | Troyanov / Luo–Tian (spherical cone metrics); already a named external in gx (`TroyanovSuspensionTheorem`) |
| spacelike | a **singular HS²-sphere** | **BBS Theorem 5.6 applies whole**: causally regular / black-or-white-hole / Big Bang–Crunch / white + black hole, and the §4 polyhedra give examples |
| null | a singular (E(2), E²₊ ⊔ S¹ ⊔ E²₋)-sphere: two Euclidean cone half-spheres glued along the circle of light-cone directions | new — no classification known to this review |

So BBS's *interaction points* in 2+1 reappear in 3+1 as **spacelike junction lines**, and their
whole §4–§5 theory transfers with no change.

### Codimension 4: points

The link Σ_x is a **singular HS³-sphere** whose singular set is a graph:
- each edge is a sheet direction, carrying a (Γ, ℓ)-circle from codimension 2;
- each vertex is a junction direction, carrying a spherical, HS² or horospherical sphere from
  codimension 3.

The analogue of §5's decomposition:
- **hyperbolic regions**: ℍ³_± parts, which are hyperbolic cone 3-manifolds with graph singular locus;
- **de Sitter regions**: dS³ parts;
- **photon surfaces**: ∂ℍ³_± parts.

**[r]** On a photon surface, BBS's two ℝP¹-structures on a photon circle (l.1894–1930) become **two
flat conformal (Möbius, ℂP¹) structures**: one from the hyperbolic side as the conformal boundary,
one from the de Sitter side.

**What does not lift.** §5 runs on Poincaré–Hopf for the two isotropic line fields of a dS² region
and on Poincaré–Bendixson for their leaves (rows 40–41). In dS³ the isotropic directions form a
*cone field*, not two line fields, and there is no Poincaré–Bendixson. **The codimension-4
classification is research, not formalisation.**
- Examples come from convex polyhedra in HS⁴, generalising §4 (and BBS's own §4.5.3 speculation).
- Whether Schlenker's HS³ results extend to HS⁴ is not checked here.

---

## E. Proposed waves (not scheduled; sizes are guesses, not measurements)

| wave | content | depends on | size |
|---|---|---|---|
| **W0** | HS^n = S(R^{1,n}) under `lorentz n`; five orbits; analytic action; point-links S(V/ℝv) and pointwise stabilisers (L2 table) | lean-causal `Form`, `Penrose` | 2–4k lines |
| **W1** | L0 (conical structure, geometric suspension functor, regularity at O for sphere links) + L1 (affine cone, linear chart changes); the bridge suspension ≅ quotientBase | gx `Susp`, `Atlas`, `Quotient` | 3–6k |
| **W2** | ℝP¹-circles (row 6) and (Γ_p, ℓ(p))-circles with i^± (rows 7–14); codimension-2 models in **every** dimension: massive, tachyon, photon, BTZ-like, extreme BTZ (= E₀), Misner, deg 2k via branched covers | W0, W1 | 6–10k |
| **W3** | causality of e(Σ): local future = e(ℍ⁺), Lemma 3.12 (flat, any n), causal and positive (Defs l.1114, l.1508), through ETT | W2, lean-causal | 2–4k |
| **W4** | codim 3: the spherical junction (Troyanov stays external) and the **HS² interaction classification** (§5, Thm 5.6), with Poincaré–Hopf and Poincaré–Bendixson either built or named external | W2, W3 | 10k+, or externals |
| **W5** | codim 4: singular HS³-spheres, photon surfaces with conformal structures, HS⁴ polyhedra | W4 | research |

W0–W3 are pure formalisation of material whose mathematics is settled. W4 is settled mathematics with
expensive 2D topology. W5 is open.

---

## F. Open questions for rulings

These are numbered **BBS-Q1…Q8** locally. They get `OQ-` ids only when ruled, from the then-current
maximum in `registers/` (ids race with the gx and Barbot sessions; the last DEC seen was DEC-93).

1. **Where L2–L3 live.** The ruling puts L0–L1 in lean-gx. L2–L3 could also go into lean-gx, which
   already requires lean-causal, or into a downstream package (`lean-bbs` requiring lean-gx).
   lean-causal must not import lean-gx (DEC-33).
2. **Full or pointwise stabiliser.** BBS use the pointwise stabiliser Γ_p of the ray (no spin). The
   thesis (l.1002) and the commented-out draft's conical structure (l.3569) use the full stabiliser, which for a null ray
   adds the boost along it (Aff(ℝ) rather than ℝ). That changes which light-like singularities exist.
   Does the general L0 take the stabiliser as a parameter, with BBS as the pointwise instance?
3. **The representation of HS^n.** The options are the quotient (V∖0)/ℝ₊*, or the Euclidean unit
   sphere with the normalised action v ↦ gv/|gv|. The second reuses `Metric.sphere` and
   `PenroseSphere`; the first makes the link S(V/W) uniform.
4. **"Every HS^n-structure on S^n is HS^n" (row 5).** Proposed proof [r], for n ≥ 2: S^n is simply
   connected, so the developing map is a local homeomorphism between compact spheres, hence a covering,
   hence a homeomorphism. Is this the intended reading? Is it to be proved here (it gives regularity
   at O)?
5. **Row 11, which BBS leave to the reader.** The ℝP¹-structure plus i^±(L) determine the
   (Γ_p, ℓ(p))-circle. Prove it, or record it as an external?
6. **`lorentz d` as the identity component.** It is defined by preserving Q, preserving the future
   cone, and det = 1, and is not proved connected. Nothing in W0–W3 seems to need connectedness, but
   the HS^n orbit count (five) is stated for SO₀.
7. **3+1 obstructions in lean-causal.** These belong to the Barbot and ETT sessions, not to this
   campaign:
   - `SingularFlatAxioms` requires 1-dimensional singular components (`line`, `massive_line`).
   - The static `Massive` uses mathlib's sup metric on products, which gives wrong light cones in
     ℝ × (C_α × ℝ).
8. **AdS and dS later.** Should the suspension be written with a curvature parameter κ ∈ {−1, 0, 1}
   from W1 on (cos², r², cosh²), or should flat stay hard-wired until a ruling?

---

## G. Coordination

- **The gx session** owns `lean-gx/` and `papers/gx/`. It **agreed on 2026-11-02**, by
  cross-session message, to the following:
  - **Modules.** `GX.Suspension.*`:
    - `Conic.lean`: the "structure conique", these.tex l.3569ff;
    - `Celestial.lean`: the "(G,X)-suspension céleste", RamcovGX l.734;
    - `Affine.lean`: L1, plus the bridge to `GX.quotientBase`.

    They reuse `GX.Singular.Suspension` and the Atlas/Quotient API, and never redefine them.
  - **What this session may write.** It may author **new** files under
    `lean-gx/scaffold/GXScaffold/Suspension/` and a campaign directory `lean-gx/campaign/BBS-*/`.
    It may not edit any existing lean-gx file, the gx ledger, the curation, or the lakefile.
  - **No git writes** from this side under `lean-gx/`. The gx master session graduates the files
    (git mv to `GX/Suspension/`) after a read-only audit, and commits by pathspec.
  - **Builds** only as `lake build GXScaffold.Suspension.<M>`, under `taskset -c 0-11`, and never
    while a gx workflow is running. Wave 5 is running now; gx will message when it closes.
  - **Namespace** `GX`; grep for clashes first.
  - **Importing `Causal.*`** is allowed only under `{GX,scaffold/GXScaffold}/{BTZ,Lorentz}/`
    (`scripts/causal_import_gate.py`). If Suspension needs Causal, ask gx first, and it will widen
    the gate deliberately.
  - **Rulings** on gx files are DEC rows recorded by the gx master session.
  - **Terminology.** gx will add the BTZ terminology bridge (§C, payoff 2) to `lean-gx/kb`.
- **The Barbot / ETT session** owns `lean-causal/` (`Causal.Flat`, `SingularFlat`, `CBG`) and
  `papers/barbot`. The E₀ observation (payoff 3) and Q7 are for that session.
- This file and `sources/` are the only things written. `papers/bbs` has no `ledger/ledger.toml`, so
  `tools/papers_check.py` does not pick it up. A ledger needs a ruling, as `papers/barbot` got
  DEC-34.

---

## H. Answers to the gx session (2026-11-02)

### H.1 Which part of `TroyanovSuspensionTheorem` L0 discharges

The theorem is at `lean-gx/scaffold/GXScaffold/SingularII/Models.lean:885`. It is a single `∃`, not a
structure, so "a field" means one of three bundled claims:

1. **(T) Troyanov.** For s ≥ 3 pairwise distinct angles θ satisfying `TroyanovAngleCondition` (:838),
   a spherical cone metric on S² with those angles exists.
2. **(S) Suspension.** Its Thurston suspension M is a singular (G,X)-manifold with a centre O.
3. **(F) The facts.** `SuspensionCexFacts G X M O` (:812), with fields `connected`, `mem_sing`,
   `exists_ne`, `rigid` and `rot`.

**L0 alone discharges none of them**, because the statement is over an arbitrary (G,X) and the
angle-dependent content lives at (SO(4), S³), which is not in the library (Models.lean:881). With L0
**and** the spherical L3a instance (S³ under SO(4), point-links S² under SO(3)), the split becomes:

| claim | status with L0 + L3a |
|---|---|
| (T) | stays a named external, narrowed to its true content: "a singular (SO(3), S²)-surface homeomorphic to S² with cone angles θ exists" |
| (S) | **discharged.** M := `susp_{(SO(4),S³)}(Σ)` by `Celestial`; local connectedness from `Susp` |
| (F) `connected` | **discharged** (a suspension is connected) |
| (F) `mem_sing` | **discharged**, from the L0 theorem "O is regular iff Σ is the model link". Σ is not round, since some θᵢ ≠ 2π, which `TroyanovAngleCondition` with s ≥ 3 forces **[r]** |
| (F) `exists_ne` | **discharged**, from the L0 lemma "the ray over a singular point of Σ is singular" |
| (F) `rigid`, `rot` | **not discharged.** Both are angle-dependent (a generic Σ has no non-trivial local automorphisms). L0 reduces them to statements about Σ, which stay external with (T) unless proved |

So the DEC-69 external shrinks from (T) + (S) + (F) to (T) plus the two automorphism facts about Σ.

### H.2 The tachyon and photon statement (draft for a gx package, or for `Suspension/Affine`)

The setting is flat 2+1, x₀ ∈ E^{1,2}, and there is no AdS pair (c, c₊).

- **Tachyon:** v spacelike, and g ∈ Isom₀ a boost fixing x₀ + ℝv pointwise.
- **Photon:** v null, and g a null rotation fixing x₀ + ℝv pointwise.

**The ray circle.** Choose a complement plane P of ℝv and a Euclidean unit-speed parametrisation
w : ℝ → P∖0 of its rays, so that w(θ + 2π) = w(θ), oriented as at BBS l.729–731. The linear part of g
acts on V/ℝv ≅ P and induces a circle homeomorphism. Let ĝ : ℝ → ℝ be its lift **that fixes the
lifts of g's fixed rays**:
- four fixed rays in the tachyon case (the light-like directions of P);
- two fixed rays in the photon case (the directions tangent to the light cone);
- in both cases, the endpoints of the i^± arcs (BBS l.840).

**The action.** For m ∈ ℤ, let ℤ act on `DInfty × ℝ` by

  1 · (r, θ, z) = (r · ‖g w(θ)‖ / ‖w(ĝθ + 2πm)‖, ĝ(θ) + 2πm, z),

fixing the axis {r = 0} pointwise. The norm is the one used to normalise w. Develop by

  D(r, θ, z) = x₀ + z v + r w(θ).

Then D is a local homeomorphism on `cylPos ℝ` and D(1 · x) = g · D(x).

**The statement:**

> For m ≠ 0, the action is free on {r > 0} and satisfies `hdisc`. **[r]** In each arc ĝ(θ) − θ
> lies in (−π/2, π/2) for the tachyon and in (−π, π) for the photon, so ĝ(θ) + 2πm − θ has the
> sign of m and never vanishes.
>
> Hence, by `existsUnique_aeGXQuotient` (Quotient.lean:833, which is generic in Γ), the quotient
> M = ℤ\(𝔻_∞ × ℝ) carries a unique maximal a.e. (Isom₀, E^{1,2})-structure whose projection is an
> a.e. morphism. Its singular locus lies in π{r = 0}, and its holonomy around the axis is g.
>
> The axis is a **space-like** (respectively **light-like**) singular line of BBS degree k = 2|m|.
> Each turn of the ray circle is δ² in the universal cover of PSL(2,ℝ), which is why BBS degrees
> are even (l.905). It is **positive** iff ĝ(θ) ≥ θ on the lifted arcs I⁺, i.e. iff the left
> endpoint of each I⁺ component is repelling (BBS l.908–915, l.918–922).
>
> m = ±1 gives the tachyon and the photon (degree 2). |m| ≥ 2 gives the degree-2|m| lines of
> `rk:degk`, the |m|-fold branched covers.
>
> **For m = 0**, the action is not free on the whole circle. Restricting θ to one open arc I between
> consecutive fixed points gives BBS's degree-0 lines:
> - I = i⁺ gives the past BTZ-like line, and I = i⁻ the future BTZ-like line (tachyon setting);
> - a spacelike arc gives a Misner line;
> - in the photon setting, I = i⁻ gives the extreme BTZ-like line (= E₀) and I = i⁺ gives the
>   cuspidal case.
>
> These should agree with gx's existing `misner_btz` / `btz_*` families. Proving that agreement is
> the `Affine` bridge.

**Three caveats**, to be pinned before this goes to an author:
- **Sign convention.** The orientation of w must match BBS's canonical orientation, in which the
  developing map is increasing. The "positive iff repelling" criterion flips with it. Check it
  against the tachyon example at l.1229–1233, where L₁ is the left end of i⁺ and is repelling.
- **The radial factor.** It keeps D equivariant, because a Lorentz map does not preserve Euclidean
  norms. An author may prefer the action on the cone C(P) directly over the (r, θ) chart.
- **Where `hdisc` needs care.** At axis points the condition is immediate, since every γ fixes them.
  On {r > 0}, the radial factor is bounded on compact θ-sets, which is the point that needs it.

### H.3 What gx decided (2026-11-02)

gx recorded both answers in `lean-gx/campaign/POSTWAVE5/BBS-NOTES.md`.

- **H.2 becomes a gx package after wave 5:** the tachyon and photon variations of `ex:quotient_base`
  with Γ = ℤ in `existsUnique_aeGXQuotient`. It is seeded with the statement above and carries the
  orientation caveat on w.
- **The m = 0 case stays here.** Matching it against `misner_btz` / `btz_*` is this campaign's
  `Suspension/Affine` bridge.
- **The H.1 shrink is a ruling for the author.** gx will put it to them once `Conic`, `Celestial`
  and the spherical instance exist.

### H.4 What the Barbot session said (2026-11-02)

- **Stable names.** `lorentz d`, `isom d`, `PenroseSphere d` and the `IsElliptic` / `IsHyperbolic` /
  `IsParabolic` classes are strict `Causal.Flat.*`. They graduated at `ba5ed22`, their names are
  stable, and the Barbot session will announce any rename.
- **BTZAxioms changed.** It now carries `Iplus_of_lt` in place of the old `Iplus_eq` (DEC-64,
  `f84b69e`). An E₀ witness built from the suspension must satisfy that form.
- **Who owns E₀.** E₀, `LocalModel` and the BTZ obligations belong to the gx session, so payoff 3
  (§C) is routed there.
- **No change to the 2+1 axioms from that side.** The Barbot session will not touch
  `SingularFlatAxioms` or `Massive`. Codimension-2 strata for 3+1 are an interface change for the
  ETT and gx owners and need **the author's ruling**. This is BBS-Q7 (§F), which is now the
  author's question, not a request to the Barbot session.

---

## I. Lean status: L0/L1 first pass (2026-11-03)

Three new scaffold modules, untracked and handed to gx for audit and graduation:

| file | lines | contents |
|---|---|---|
| `lean-gx/scaffold/GXScaffold/Suspension/Conic.lean` | 586 | 0 sorry |
| `lean-gx/scaffold/GXScaffold/Suspension/Celestial.lean` | 601 | 1 tagged sorry, `celestial_sing_ray` |
| `lean-gx/scaffold/GXScaffold/Suspension/Affine.lean` | 431 | 0 sorry |

Each was built alone and is green. No strict module was recompiled. Reports are in
`lean-gx/campaign/BBS-{Conic,Celestial,Affine}/REPORT.json`.

**Two results change the architecture of §B.** Neither is a finding against the thesis: the
material they bear on (`these.tex` l.3560–3677) is commented-out draft, not a claim of the thesis
(correction by the author, 2026-11-03). They are the **motivation for the corrected definitions**.

- **F1 (design motivation).** The draft's suspension proposition (these.tex:3645, commented out),
  read literally with the draft's definition of a conic structure, fails: the step at these.tex:3667
  assumes the stabiliser preserves the radius. The
  counterexample is `GX.celestial_counterexample` (Celestial.lean:502), and its hypotheses are
  checked at :559. The corrected notion is `GX.ConicStructure`, which requires φ(h·x) = susp(h·)(φ x).
- **F2.** Radius preservation is **incompatible with boosts**. `GX.not_conicStructure_of_contraction`
  (Affine.lean:290): if H contains a linear map with an eigenvalue in ]0,1[, no conic structure at 0
  exists, for any link. So L0 as built covers the Riemannian branch (Thurston's iteration, and the
  Troyanov shrink of H.1) but **not the Lorentzian branch**.
  - BBS's flat suspension needs a **scale-equivariant suspension**: H acts on Susp L by
    (σ, r) ↦ (h·σ, c(h,σ)·r), with c a positive continuous cocycle. For the linear case on the unit
    sphere, c(h,σ) = ‖hσ‖.
  - This is the same radial factor that already appears in the tachyon/photon statement (H.2).

**Decisions for the author** (they sharpen BBS-Q2 and Q3):
1. The default stabiliser in L0: full or pointwise.
2. Keep the unit-sphere model of S(V).
3. The shape of the scale-equivariant suspension: a cocycle on Susp L, or the ℝ₊*-bundle cone.

**The author's rulings (2026-11-03)** on the three decisions above:
1. **Default stabiliser: pointwise (BBS).** H stays a parameter. The spinless BBS classification is
   built first; the full stabiliser (the thesis's Aff(ℝ) at null rays) and spin come later as
   further instances.
2. The S(V) model was not ruled on explicitly, so the unit sphere stays (`GX.RaySphere`) until
   someone objects.
3. **The Lorentzian suspension is a cocycle on `Susp L`**: H acts by (σ, r) ↦ (h·σ, c(h,σ)·r). The
   author's pointer is **"look at Andrea Seppi's work"**. The candidates being read are:
   - Fillastre–Seppi, *Spherical, hyperbolic and other projective geometries: convexity, duality,
     transitions*, arXiv:1611.01065. This is a projective treatment of the HS-type models and their
     transitions.
   - Riolo–Seppi, *Geometric transition from hyperbolic to Anti-de Sitter structures in dimension
     four*, arXiv:1908.05112, and *Character varieties of a transitioning Coxeter 4-orbifold*,
     arXiv:2006.15847. These are 4-dimensional Lorentzian cone-manifolds, i.e. our 3+1
     stratification.
   - Bonsante–Seppi, *On Codazzi tensors on a surface and flat Lorentzian geometry*, arXiv:1501.04922.
     This treats flat spacetimes with particles.
   - Nie–Seppi on affine deformations of convex cones and regular domains, arXiv:2009.12311 and
     arXiv:2111.04532.

   Also noted: Barbot–Meusburger, *Particles with spin in stationary flat spacetimes*,
   arXiv:1108.1005, for the spin instances.

**Seppi reading (2026-11-03)**: `SEPPI-READING.md`, summarised in NOTES-3+1 N6. Four consequences
for the design of L0/L1:
- equivariance on germs;
- a radial cocycle valued in germs of homeomorphisms of [0,∞), with trivial, linear-scalar and
  projective instances;
- **spin moves from the point suspension to the line model** (a translation cocycle in `Affine`);
- the κ-family is one suspension with domains D_κ.

Riolo–Seppi's 4D foams give the first codimension-3 and codimension-4 examples (theta-graph edges,
K₄ vertices, all tachyonic).

**Correction (2026-11-03, the author, via gx).** `these.tex` l.3560–3677 — the structure conique,
the «propri», `lem_analytique` (l.3606), the suspension céleste and its proposition (l.3645) with
its proof (l.3667) — is **commented out and not part of the thesis**. Earlier wording in this file
and in the Lean files that called F1 and the `lem_analytique` counterexample "findings against the
thesis" is withdrawn. The counterexamples stay, as motivation for `ConicStructure`'s hypotheses.
L0 is new theory certified on its own terms.
