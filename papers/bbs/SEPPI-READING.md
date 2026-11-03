# Reading Seppi (and Barbot–Meusburger) for the cocycle suspension and 3+1

*2026-11-03, `node1`. Reading and notes only: no Lean, no git. Context: `REVIEW.md` §B (L0–L3), §D
(3+1 stratification), §F Q8, §I (F1, F2 and the author's ruling that the Lorentzian suspension is a
**cocycle on `Susp L`**: H acts by (σ, r) ↦ (h·σ, c(h,σ)·r)), and `NOTES-3+1.md` N1–N4.*

**Conventions.**
- **[q]** marks a verbatim quote. Every quote contains a **grep phrase** (in `code`) that is
  reproducible as `pdftotext -q sources/seppi/<id>/pdf/<id>.pdf - | grep -n '<phrase>'` (each was
  checked to match exactly one line unless stated). Formulas inside quotes are transcribed from the
  e-print TeX, because `pdftotext` flattens them; the grep phrase is always prose.
- "p." is the PDF page index (from the form feeds of that `pdftotext` output); "§" and statement
  numbers are the paper's own; "TeX l." is a line of the extracted e-print.
- **[r]** marks this session's own inference. Nothing marked [r] is in any of the papers, and none of
  it has been checked by anyone else.
- Sources, versions and sha256: `sources/seppi/README.md`. Two titles in the task differ from arXiv:
  1501.04922 is *On Codazzi tensors on a **hyperbolic** surface…*, and the TSG 35 note is arXiv
  **2004.03776**, *Examples of geometric transition in low dimensions*.

---

## 0. Findings in one screen

1. **Seppi's framework is projective, and its only normalisation is on the q < 0 region.** The model
   spaces live in the projective sphere S^n = (ℝ^{n+1}∖0)/ℝ_{>0}; the metric is pulled back by the
   section "unique positive multiple with q = −1"; the null locus (the *absolute*) is handled with
   **no normalisation at all**, purely projectively (§1, §2).
2. **BBS's own suspension is a gluing construction, not a product.** `e(Σ)` (BBS TeX l.626–650) is
   built chart by chart from the radial rays and glued by the coordinate changes; `𝔢(L)` (l.776–778)
   uses projective segments [−p, p]. Riolo–Seppi adopt exactly this "AdS suspension [BBS]" for their
   4-dimensional cone-manifolds (§2).
3. **Proposal [r]** (§8.1): the canonical object is the **radial bundle** — the pull-back of the
   ℝ_{>0}-bundle V∖0 → S(V) along the developing map. The author's cocycle on `Susp L` is its
   trivialisation by the unit-sphere section (`GX.RaySphere`), c(h,σ) = ‖hσ‖. Changing the section
   changes c by a coboundary; the class of c is canonical, c itself is not.
4. **No canonical global section exists, and the obstruction sits exactly on the light cone [r]**
   (§8.2). The hyperboloid / de Sitter normalisation |Q| = 1 is H-invariant (so c ≡ 1) on every
   non-null ray, and blows up on null rays. Sharper than F2: c is cohomologically trivial on a
   subgroup iff every element acts with eigenvalue 1 on each of its fixed null rays — and this fails
   for any boost, even with discontinuous sections. On the photon sphere ∂ℍ^n, c is the conformal
   factor of the Möbius action, so a section there is a conformal metric.
5. **The scalar cocycle c·r is not enough in two places [r]** (§8.3): at **null points of an
   HS-link** (BBS's photon / extreme-BTZ / cuspidal HS-singularities) the pointwise stabiliser acts on
   the radial segment by r ↦ c r/(1 + a r), with no invariant complement to linearise it; and on
   **null singular lines**, "line × transverse cone" is a product *twisted* by an additive cocycle a,
   acting as (σ, r, z) ↦ (h̄σ, c r, z + a r) — the shape of Danciger's half-pipe matrices.
6. **Spin is not an instance of the suspension [r]** (§8.4). Barbot–Meusburger: with spin the
   singular line's quotient "is a circle and not a line"; the holonomy fixes no point of the line, so
   no point of it has a conical neighbourhood. Spin lives only in the line model, as a constant term
   τ in z ↦ z + a r + τ. Bonsante–Seppi and Nie–Seppi state the no-spin condition as "the translation
   cocycle is trivial on peripheral loops" (elliptic case) and "admissible" (parabolic case).
7. **The curvature parameter κ ∈ {−1, 0, 1} does not touch the link or the cocycle [r]** (§8.5). In
   the Klein chart at p, the κ-model is the H-invariant star domain D_κ = {w : −κ Q(w) < 1} ⊂ T_p, H
   acts linearly with the same cocycle, and κ → 0 is Fillastre–Seppi's "blow-up of a point", which
   maps D_κ to D_{κt²}. So: one suspension, a family of invariant domains.
8. **Riolo–Seppi's 4-dimensional singularities are a foam of tachyons** (§8.6): generic (simple)
   strata only — sheets, triple-junction edges (theta-graph link), 4-valent vertices (K₄ link) — all
   spacelike, in the de Sitter region of the HS³ link. No massive, no photon, no ≥ 4-sheet junction,
   and an open question whether embedded-surface singular loci deform at all. Their links are
   κ-independent, so they are also links of **flat** 3+1 vertices [r].

---

## 1. Fillastre–Seppi, *Spherical, hyperbolic and other projective geometries* (arXiv:1611.01065)

**What it offers us.** The projective dictionary in one place: model spaces as projective quotients
of pseudo-spheres, the absolute, the line types, Minkowski space as projective space minus a
hyperbolic–de Sitter hyperplane, convex duality via support functions (1-homogeneous, normalised on
the hyperboloid), co-Minkowski = half-pipe, and the geometric transitions as rescaled ("conjugacy")
limits. It works in ℝP^n (quotient by ±Id), and uses the double cover only for pictures and local
computations. It does **not** treat HS^n or cone-manifolds, and contains no cocycle on a cone.

| # | quote [q] | grep phrase | where |
|---|---|---|---|
| FS1 | "The projective quotient P𝓘(b) of the isotropic cone is called the *absolute*." | `of the isotropic cone is called the absolute` | Def 2.6, §2.2, p.5 |
| FS2 | "Parabolic and light-like lines coincide." | `Parabolic and light-like lines coincide` | Lemma 2.8, p.5 |
| FS3 | "The Minkowski space is the projective space minus a hyperbolic-de Sitter hyperplane." | `The Minkowski space is the projective space minus a hyperbolic-de Sitter hyperplane` | Fact 3.12, §3.4, p.17 |
| FS4 | "any future time-like ray from the origin meets the boundary of K exactly once, hence" int 𝓕 ⊂ dom H̃ ⊂ 𝓕 | `meets the boundary of K exactly once, hence` | §3.4 "Support function", p.19 |
| FS5 | "Note that by homogeneity, H is determined by its restriction h to 𝓗^{n−1}_+: H(x) = ‖x‖_− h(x/‖x‖_−), with ‖x‖_− = √(−b_{n−1,1}(x,x))." | `Note that by homogeneity, H is determined by its restriction h to` | §3.5, p.20 |
| FS6 | "The support function provides a bijection between the space of admissible convex subsets of M^n and the space of negative convex 1-homogenous functions on the cone int 𝓕." | `provides a bijection between the space of admissible convex subsets` | Fact 3.19, p.19 |
| FS7 | "The dual of H_r, the future convex side of a branch of hyperboloid with radius r, is H_{1/r}." | `future convex side of a branch of hyperboloid with radius` | §3.4, p.18 |
| FS8 | "The co-Minkowski space *M^n is the space of (unoriented) space-like hyperplanes of M^n." | `is the space of (unoriented) space-like hyperplanes` | Fact 3.23, p.20 |
| FS9 | "Elliptic and hyperbolic lines converge — in the sense of geometric transition — to a parabolic line." | `Elliptic and hyperbolic lines converge` | Fact 4.1, p.23 |
| FS10 | "Heuristically, this rescaling procedure is a *blow-up of a point*, in the sense that the point (0,0,1) is preserved, and the transverse directions are 'blown-up'." | `this rescaling procedure is a blow-up of a point` | §4.1, p.24 (g_t = diag(1/t, 1/t, 1)) |
| FS11 | "the right model spaces which have a limit in Minkowski space (by blowing-up a point) are de Sitter and Anti-de Sitter space" | `the right model spaces which have a limit in Minkowski space` | §4.2, p.28 (diagram dS³ → M³ ← AdS³) |
| FS12 | "We will indeed call this transition the *blow-up of a line*." | `We will indeed call this transition the blow-up of a line` | §4.1, p.25 |

**For (a).** FS4–FS6 are the closest thing in the corpus to a "canonical way to build the cone":
a future convex set is the same as a **1-homogeneous** function on the open future cone, and
FS5 normalises it by the hyperboloid ‖x‖_− = 1. That is a choice of section of the ℝ_{>0}-bundle
**over timelike rays only**; FS4 says the radial graph is a section over *timelike* rays, and the
paragraph after it shows that on light-like rays the extended function is forced to 0 (the section
degenerates). This is the same pattern as §8.2 below: the |Q| = 1 normalisation is canonical off the
light cone and fails on it. FS7 is the scaling behaviour of the hyperboloid "radius" under duality.

**For (d).** FS10–FS11 give the curvature transitions as conjugacy limits by
g_t = diag(1/t, …, 1/t, 1) fixing a point: Ell, ℍ → 𝔼 and dS, AdS → M ("blow-up of a point"), and
dually ℍ, AdS → co-Minkowski (= half-pipe) ("blow-up of a plane"). The κ-parameter family of §8.5
is the point-blow-up column.

---

## 2. Riolo–Seppi, *Geometric transition from hyperbolic to AdS structures in dimension four* (arXiv:1908.05112)

**What it offers us.** (i) The cleanest set-up of HS geometry inside the projective sphere, with the
normalising section stated explicitly. (ii) A working definition of **simple** projective
cone-manifolds in dimension 4 and their **links** (cone 3-spheres), with the identification "link of
an AdS point = HS^{n−1}" and "simple AdS cone-manifolds are locally modelled on the AdS suspension"
of BBS. (iii) Explicit 4-dimensional singular strata and their links. (iv) Half-pipe geometry as the
dual of Minkowski space, so HP holonomy = Minkowski isometries (linear part + translation cocycle).

| # | quote [q] | grep phrase | where |
|---|---|---|---|
| RS1 | "Since in ℝP^n there is no notion of half-space, we will work with its double cover, namely the *projective sphere* S^n = {x ∈ ℝ^{n+1}∖{0}}/ℝ_{>0}, where the group ℝ_{>0} acts by multiplication." | `its double cover, namely the projective sphere` | §2.2, p.6 |
| RS2 | "…via the immersion σ: ℍ^n → ℝ^{n+1} which maps the class [x] to the unique positive multiple of x such that q₁(x) = −1." | `to the unique positive multiple of` (2 hits: p.7 for ℍ^n; p.14 for the family X_t) | §2.3, p.7 |
| RS3 | "…the condition that e_n is eigenvector with eigenvalue ±1 implies that A cannot 'stretch' in the degenerate direction." | `in the degenerate direction. Moreover` | Remark in §2.5, p.9 |
| RS4 | "In conclusion, HP^n parameterises the spacelike hyperplanes in ℝ^{1,n−1}." | `In conclusion, HPn parameterises the spacelike hyperplanes in` | §2.6, p.9 (then Lemma 2.9: Isom(ℝ^{1,n−1}) ≅ G_{HP^n}) |
| RS5 | "A *foam* is a 2-complex locally modelled on the cone over the 1-skeleton of the tetrahedron" | `A foam is a 2-complex locally modelled on the cone` | §1, p.3 |
| RS6 | "To the best of our knowledge, it is not known whether there can even exist deformations of 4-dimensional, finite-volume, hyperbolic cone-manifolds with singular locus an embedded surface." | `it is not known whether there` | §1, p.3 |
| RS7 | "The holonomy of a meridian … of a 2-stratum of Σ … We have a rotation in ℍ⁴ of angle α_t when t > 0, and a Lorentz boost in AdS⁴ of magnitude β_t as t < 0." | `boost in AdS4 of magnitude` | §1, p.3 |
| RS8 | Σ "is locally modelled on the cone over the (n − 3)-skeleton of an (n − 1)-simplex if n ≥ 3. In particular, Σ is a trivalent graph if n = 3, and a so called *foam* if n = 4." | `is locally modelled on the cone over the (n − 3)-skeleton` | §5.2, p.25 |
| RS9 | "we define its *link* 𝓛_p to be the sphere of directions at p of the projective manifold X∖Σ, that is, the projective sphere S^{n−1} over the tangent space at p. If instead p ∈ Σ, we define its link 𝓛_p to be the double of the link … of a corresponding point in ∂𝓟 through a chart." | `sphere of directions at p of the` / `the double of the link` | §5.2, p.25 |
| RS10 | "If n = 3, then 𝓛_p is a cone 2-sphere with 0, 2, or 3 singular points … If n = 4, the singular locus of the cone 3-sphere 𝓛_p is empty, an unknotted cicle [sic], an unknotted theta graph, or the 1-skeleton of a tetrahedron, depending whether p belongs to a 4-, 2-, 1-, or 0-stratum" | `is a cone 2-sphere with 0, 2, or 3` / `is empty, an unknotted cicle, an unknotted` | §5.2, p.25 |
| RS11 | "The holonomy ρ(γ) of a meridian γ … of an (n−2)-stratum is conjugated to a product of reflections r_i r_j ∈ Aut(S^n) that fix a common (n−2)-subspace" | `is conjugated to a product of reflections` | §5.2, p.25 |
| RS12 | "The analogous geometry for AdS^n has been introduced in [BBS11], where it is called *HS geometry*. By identifying T_xAdS^n with ℝ^{1,n−1}, the link of a point x ∈ AdS^n is called HS^{n−1}, and is a projective (n−1)-sphere identified with the space of rays in ℝ^{1,n−1}." | `where it is called HS geometry` | §5.3.2, p.26 |
| RS13 | the three strata of HS^{n−1}: "the region of timelike rays, which corresponds to two copies of ℍ^{n−1}; the region of spacelike rays, which is a copy of de Sitter space dS^{n−1}; the set of lightlike rays, which is the common boundary of the two latter regions and is topologically the disjoint union of two (n−2)-spheres." | `the region of timelike rays, which corresponds to two copies of` / `the region of spacelike rays, which is a copy of de Sitter space` / `the set of lightlike rays, which is the common boundary` | §5.3.2, p.26 |
| RS14 | "In analogy with the hyperboic [sic] case, simple AdS cone-manifolds are locally modelled on the AdS suspension [BBS11] over the double of an HS simplex of one dimension less. In the AdS case with spacelike singularities, the facets of the HS simplex are contained in the de Sitter region of HS^{n−1} and are spacelike." | `simple AdS cone-manifolds are locally modelled on the AdS suspension` / `the facets of the HS simplex are contained in the de Sitter region` | §5.3.2, p.26 |
| RS15 | "In the HP case (centre), we have just a sphere with two marked antipodal points, corresponding to the degenerate direction. In the transition from AdS to hyperbolic geometry the two timelike regions shrink to points and then disappear." | `we have just a sphere with two marked antipodal points` / `the two timelike regions shrink to points and then disappear` | Fig. caption, p.27 |
| RS16 | HP link: "Note that such a (G,X)-structure has some distinguished points, which correspond to the degenerate rays exiting from x." | `correspond to the degenerate rays exiting from` | §5.3.3, p.27 |
| RS17 | "it can be seen directly that the rescaled limits of the point stabilisers Stab_{ℍ^n}(x) and Stab_{AdS^n}(x) are point stabilisers in half-pipe geometry. Hence a geometric transition from hyperbolic to AdS geometry on simple projective cone-manifolds induces a geometric transition from spherical to HS cone structures" | `rescaled limits of the point stabilisers` | Remark 5.6, p.27 |
| RS18 | infinitesimal rotation: "Observe that r also fixes pointwise an entire degenerate hyperplane in HP^n … This is a qualitative difference with respect to hyperbolic and AdS geometries." | `also fixes pointwise an entire degenerate hyperplane` | Remark in §4.4, p.22 |
| RS19 | vertex link: "an HS cone-sphere with singular locus a spacelike unknotted complete graph with four vertices in the de Sitter region. This is the link of a vertex of 𝓓" | `locus a spacelike unknotted complete graph with four vertices in the de Sitter region` | proof of Prop 7.28, p.46 |

**For (a).** RS1–RS2 is the set-up we want: one projective sphere for all strata, and the metric
recovered by a **section of the radial bundle normalised by the quadratic form**, defined only where
q < 0. On ∂ℍ^n / ∂AdS^n (q = 0) nothing is normalised: those points are boundary, handled
projectively. RS12–RS14 confirm that the point-link of an AdS point is HS^{n−1} exactly as for a
flat point (the stabiliser is O(1, n−1) acting on T_x), and that Seppi uses BBS's suspension, not a
new one. RS9 is the projective version of our L2 row: the link of a point [v] is the projective sphere
of ℝ^{n+1}/⟨v⟩ (in §5.1, TeX l.1151: "a half-space of the projective sphere S^{n−1} over the
quotient vector space ℝ^{n+1}/⟨v⟩").

**For (b).** See §8.6. Their singular loci are **simple** (generic): the local model is the double of
a simple polytope, so a k-stratum lies in exactly n−k bounding hyperplanes (RS8, RS10). Only
spacelike ("tachyonic") strata appear on the AdS side (RS14, RS19, and Prop 7.28: "a simple anti-de
Sitter cone-manifold with spacelike singularity along Σ_t, whose 2-strata have all the same
magnitude β_t = −2·φ_t").

**For (d).** §2.7 builds the one-parameter family X^n_t = {q_t < 0} with
q_t(x) = −x₀² + x₁² + … + x_{n−1}² + sign(t) t² x_n² (TeX l.565–571): ℍ^n for t > 0, HP^n at t = 0,
AdS^n for t < 0. This is the *plane* blow-up (a codimension-1 collapse), not the *point* blow-up
that varies the curvature of a cone (§8.5).

---

## 3. Riolo–Seppi, *Character varieties of a transitioning Coxeter 4-orbifold* (arXiv:2006.15847)

**What it offers us.** The deformation theory around the 4-dimensional example: smoothness of the
hyperbolic and AdS character varieties near the path, rigidity of 4-dimensional cusp groups, and —
the part that matters to us — the **HP character variety as an H¹ with coefficients in Minkowski
space**, i.e. a translation cocycle over a fixed linear part.

| # | quote [q] | grep phrase | where |
|---|---|---|---|
| CV1 | "In presence of a collapse of hyperbolic or AdS structures of dimension n, the holonomy representations of a rescaled HP structure naturally provide elements of the cohomology group H¹_{ρ₀}(π₁(X∖Σ), ℝ^{1,n−1})." | `naturally provide elements of the cohomology group` | §1.5, p.7 |
| CV2 | "the correct generalisation of Danciger's condition … to any dimension n would be: H¹_{ρ₀}(π₁(X∖Σ), ℝ^{1,n−1}) ≅ ℝ" | `the correct generalisation of Danciger` | §1.5, p.7 |
| CV3 | "a cusp group in AdS⁴ will be generated by 4 reflections in timelike hyperplanes and 2 reflections in spacelike hyperplanes." | `will be generated by 4 reflections in timelike hyperplanes` | §1.4, p.5 |
| CV4 | "An HP structure is never rigid, because one can always conjugate with a transformation which 'stretches' the degenerate direction" | `is never rigid, because one can always conjugate` | §1.2, p.4 |
| CV5 | "confirming the usual feeling that 'the rigidity increases with the dimension'." | `the rigidity increases with the dimension` | §1.3, p.5 |

**For (c).** CV1 is the same structure as Bonsante–Seppi's Theorem A (§5): an HP (equivalently,
Minkowski) holonomy is a pair (linear representation ρ₀, translation cocycle in Z¹_{ρ₀}(·, ℝ^{1,n−1})),
and deformations up to conjugacy are H¹. For a singular structure the relevant group is π₁ of the
complement of the singular locus — for us, π₁(Σ_x ∖ singular graph) at a vertex (N3's "knot or graph
group" momentum law, one level up).

**For (b).** CV5 and the cusp-rigidity of §1.4 are the paper's evidence that 4-dimensional singular
structures are far more rigid than 3-dimensional ones; it supports treating the codimension-4
classification (REVIEW §D, "research, not formalisation") as genuinely hard.

---

## 4. Seppi, *Examples of geometric transition in low dimensions* (TSG 35; arXiv:2004.03776)

**What it offers us.** A short, explicit introduction to the same machinery (it says of itself
"No new results appear here", `No new results appear here`, p.1), with the hyperbolic–Euclidean–
spherical transition stated **inside one projective sphere** — the cleanest quote for §8.5.

| # | quote [q] | grep phrase | where |
|---|---|---|---|
| T1 | "We will use these transformations γ_t to 'zoom in' hyperbolic space ℍ^n (or the n-sphere S^n) around the point e₀." | `zoom in` | §2.1, p.6 (γ_t = diag(1, 1/t, …, 1/t)) |
| T2 | "it is more convenient to work with the real projective sphere ℝS^n = ℝ^{n+1}/ℝ_{>0}, which is the 2-to-1 cover of ℝP^n, so that we can see ℍ^n, 𝔼^n and S^n simultaneously as subsets of ℝS^n: ℍ^n is defined by the conditions q_{1,n}(x) < 0 and x₀ > 0, 𝔼^n simply by x₀ > 0 (all these conditions are preserved by multiplication by a positive number) and S^n is the whole ℝS^n." | `more convenient to work with the real projective sphere` / `are preserved by multiplication by a positive number` | §2.1, p.7 |
| T3 | "In short, x̄ = (x₀, …, x_{n−1}) ∈ ℍ^n determines the future unit normal vector of 𝓕(x), while the last coordinate x_n is the signed distance of 𝓕(x) to the origin along the normal direction." | `determines the future unit normal vector of` | §3.2, p.15 |
| T4 | "half-pipe reflections in degenerate hyperplanes are not unique, but they constitute one-parameter groups." | `half-pipe reflections in degenerate hyperplanes are not unique` (2 hits) | §3.2, p.16 |

**For (d).** T2 is exactly the shape §8.5 needs: the three curvatures are three **subsets of one
projective sphere**, cut out by conditions invariant under positive scaling, with the isometry
groups as subgroups of GL(n+1)/ℝ_{>0}. T1 is the curvature-changing rescaling at a point.

---

## 5. Bonsante–Seppi, *On Codazzi tensors on a hyperbolic surface and flat Lorentzian geometry* (arXiv:1501.04922)

**What it offers us.** The cleanest account of the **translation part of a flat holonomy as an H¹
cocycle**, its geometric meaning (Codazzi tensors, support functions), and the precise "no spin"
condition at a particle. It also gives the local model of a flat (2+1) particle and the radial
(Klein) projection used to build it.

| # | quote [q] | grep phrase | where |
|---|---|---|---|
| BS1 | "Mathematically speaking particles are cone singularities along time-like lines with angle in (0, 2π)." | `Mathematically speaking particles are cone singularities along time-like lines` | §1, p.4 |
| BS2 | "the first cohomology group H¹_ρ(π₁(S), ℝ^{2,1}) is the vector space obtained as a quotient of cocycles over coboundaries. A cocycle is a map t: π₁(S) → ℝ^{2,1} satisfying t_{αβ} = ρ(α)t_β + t_α." | `is the vector space obtained as a quotient of cocycles over coboundaries` | §2.1, p.8 |
| BS3 | Theorem A: "the linear holonomy of M coincides with the holonomy of h; the translation part of the holonomy of M coincides with δb." | `the linear holonomy of M coincides with the holonomy of` / `the translation part of the holonomy of M coincides with` (each 2 hits: p.3 and p.12) | Thm A, p.3 |
| BS4 | "The first point is to prove that the translation part of the holonomy of M is trivial for peripheral loops, preventing singularities with spin as those studied in [BM12]." | `the translation part of the holonomy of M is trivial for` / `peripheral loops, preventing singularities with spin as those studied in` | §1, p.5 |
| BS5 | "As hol(α) is an elliptic transformation, proving that δb is trivial around α is equivalent to proving that the vector (δb)_α is orthogonal to the axis of hol(α)." | `is orthogonal to the axis of hol` | Remark in §4.2, p.29 |
| BS6 | Def (particle): "each s_i has a neighborhood isometric to a slice in ℝ^{2,1} of angle θ_i < 2π around a timelike geodesic, whose edges are glued by a rotation around this timelike geodesic." | `edges are glued by a rotation around this timelike geodesic` | §4.3, p.31 |
| BS7 | "such a metric is obtained by composing the developing map of U with the radial projection of the hyperboloid ℍ² onto the affine plane tangent in ℝ^{2,1} at the fixed point of the holonomy of U." | `radial projection of the hyperboloid` | §1, p.5 |

**For (c).** BS2–BS5 are the formalism the 3+1 holonomy layer will need: flat holonomy = (linear part,
translation cocycle); **"no spin" = the cocycle restricted to a peripheral loop is a coboundary =
the peripheral holonomy fixes a point = (elliptic case) the translation is orthogonal to the
rotation axis**. That is precisely the condition under which a singular line has a *conical*
(suspension) neighbourhood at each of its points (§8.4). BS7 is the radial (Klein) projection — the
same chart as §8.5 — used to turn a hyperbolic cone point into a Euclidean one.

**For (a).** §2's "support function" (the remark on p.13 of the PDF, TeX l.1331: "The function
û∘G⁻¹: ℍ² → ℝ coincides with the support function of F") is again a function on the timelike-ray
hyperboloid, i.e. the |Q| = 1 section.

---

## 6. Barbot–Meusburger, *Particles with spin in stationary flat spacetimes* (arXiv:1108.1005)

**What it offers us.** The explicit local model of a spinning massive particle, and the decisive
fact that with spin the singular line is **not** a line of cone points.

| # | quote [q] | grep phrase | where |
|---|---|---|---|
| BM1 | "We glue P₀ to P₁ by the map (r, 0, t) ↦ (r, θ₀, t + σ), which is a restriction of the elliptic isometry g: (r, θ, t) ↦ (r, θ + θ₀, t + σ)." | `is a restriction of the elliptic isometry` | §2.1, p.3 |
| BM2 | "This is possible if σ = 0 and in that case yields a singular flat spacetime M_{θ₀,0} that contains a singular line characterised by the condition r = 0." | `This is possible if` | §2.1, p.4 |
| BM3 | "However, this procedure does not work in the case σ ≠ 0. For non-vanishing spin σ, the quotient of Δ by this isometry is a circle and not a line." | `this procedure does not work in the case` / `is a circle and not a line` | §2.1, p.4 |
| BM4 | "In particular, the limit case θ₀ = 2π yields a massless particle with non-vanishing spin σ." | `massless particle with non-vanishing spin` | §2.1, p.4 |
| BM5 | "The developing maps for these spacetimes are not one-to-one." | `spacetimes are not one-to-one` | §2.5, p.6 |

**For (c).** BM1–BM3 settle what spin does to the suspension picture (§8.4): the holonomy g is a
screw motion, it fixes **no** point of the axis Δ, so no point of the singular line has a
neighbourhood isomorphic to a suspension. BM4 is the pure-translation ("dislocation") case, which
reappears as the HP meridian holonomy in §8.6 [r].

---

## 7. Nie–Seppi, *Affine deformations of quasi-divisible convex cones* (arXiv:2009.12311)

**What it offers us.** The affine-deformation formalism over a general proper convex cone C (the
light cone C₀ being the Minkowski case), and the **admissibility** condition on a cocycle at
**parabolic** elements — the null-type analogue of BS4's "no spin at a particle". It cites the
author: "Brunswic [Bru16a, Bru16b] has obtained results in the quasi-divisible case for C₀"
(`has obtained results in the quasi-divisible case`, p.2).

| # | quote [q] | grep phrase | where |
|---|---|---|---|
| NS1 | "is called an *affine deformation* of Γ. The group relation forces τ to be an element in the space Z¹(Γ, ℝ³) of cocycles." | `The group relation forces` | §1, p.2 |
| NS2 | "We call τ *admissible* if for every parabolic element A ∈ Γ, τ(A) is contained in the 2-dimensional subspace of ℝ³ preserved by A." | `admissible if for every parabolic element` (2 hits) | §1, p.2 |
| NS3 | Prop 4.4, for (A, X) with A parabolic, equivalent: "(a) the vector X lies in P₀; (b) (A, X) is conjugate to A through a translation; (c) (A, X) preserves an affine plane in 𝔸³." … "the set of fixed points of (A, X) in 𝔸³ is an affine line lying on P₁ parallel to L₀." | `is conjugate to A through a translation` / `preserves an affine plane in` / `an affine line lying on` | Prop 4.4, §4.2, p.22 |

**For (c).** NS3 is the parabolic version of BS5: for a null-rotation linear part, the translation
part is a local coboundary **iff** it lies in the invariant null plane **iff** the element has a line
of fixed points. That line is the photon line; a translation part outside P₀ is "spin" for a photon,
and then no point is fixed. NS1 also says the cone C itself is presented as C = {t(x,1) | x ∈ Ω*,
t > 0} (TeX l.521), i.e. a cone over a section — the same "radial bundle over a base" as §8.1.

---

## 8. Synthesis

### 8.1 The cocycle suspension: a canonical object, and its trivialisation **[r]**

Fix a finite-dimensional real vector space V, a group H ≤ GL(V), and S(V) = (V∖0)/ℝ_{>0} (RS1, T2).
The map π: V∖0 → S(V) is an **H-equivariant principal ℝ_{>0}-bundle** — the *radial bundle*.

**Canonical construction (no choices).** Let L be an (H, S(V))-manifold (for a singular link, its
regular part plus the singular charts) with developing map dev: L̃ → S(V) and holonomy hol. Define

  C(L) := { (x̃, v) ∈ L̃ × (V∖0) : π(v) = dev(x̃) } / π₁(L),  γ·(x̃, v) = (γx̃, hol(γ)v),

and Ĉ(L) := C(L) ⊔ {O}, with the cone topology at O. C(L) is an (H, V∖0)-manifold with developing map
(x̃, v) ↦ v; it is an ℝ_{>0}-bundle over L. This is exactly BBS's `e(Σ)` (TeX l.626–650: the union of
radial rays e(U_i) over the charts, "quotiented by the relation identifying q in e(U_ij) with g_ij(q)
in e(U_ji)"), stated without charts. Nothing in it needs a radius.

**The author's cocycle is the trivialisation.** A section s: S(V) → V∖0 of the radial bundle gives
C(S(V)) ≅ S(V) × ℝ_{>0}, (σ, r) ↦ r·s(σ), and H acts by

  h·(σ, r) = (h·σ, c_s(h, σ)·r),  where h·s(σ) = c_s(h, σ)·s(h·σ).

- c_s is a multiplicative cocycle: c_s(hk, σ) = c_s(h, kσ)·c_s(k, σ).
- With `GX.RaySphere` (Euclidean unit sphere, s(σ) = σ): **c(h, σ) = ‖hσ‖** — the formula of
  REVIEW §I F2.
- Changing the section to s' = f·s gives c_{s'}(h, σ) = c_s(h, σ)·f(σ)/f(hσ): a **coboundary**. The
  class [c] ∈ H¹(H; C(S(V), ℝ_{>0})) is canonical; c is not.
- For a singular link L the trivialisation is global as soon as one section of C(L) → L exists; a
  principal ℝ_{>0}-bundle always has one (ℝ_{>0} is contractible), so `GX.Susp L` is the right
  topological space. For a **compact** L (all BBS links are spheres), any two sections differ by a
  function bounded above and below, so the cone topology at O does not depend on the choice.

**What to put in the library.**
- Keep `GX.Susp` topological, as now.
- Make the geometric suspension a structure on `Susp L` whose charts are r·s(φ_i(σ)) and whose
  transitions are (σ, r) ↦ (g_ij σ, c(g_ij, σ) r). This is literally BBS's gluing.
- State the **conic structure at p as a germ / pseudogroup condition**, not as equivariance on a fixed
  neighbourhood U_p (see the next point).

**No H-invariant bounded neighbourhood of the apex exists when H contains a boost.** An H-invariant
star-shaped neighbourhood {r < R(σ)} with R continuous, positive and finite would need
R(hσ) = c(h, σ)R(σ), i.e. it would make c a coboundary, which §8.2 excludes. The full cone (R ≡ ∞)
is invariant, and that is what BBS use (TeX l.626–650). So either the model is the whole cone, or the
equivariance is required only on h⁻¹U ∩ U. This is the same phenomenon as F2
(`GX.not_conicStructure_of_contraction`, Affine.lean:290), seen from the domain side; it suggests
the corrected `GX.ConicStructure` should be **germ-equivariant**.

### 8.2 Is there a canonical c? The hyperboloid normalisation, and the null rays **[r]**

Take V = ℝ^{1,n} with form Q and H ≤ O(Q).

- **Off the light cone there is a canonical H-invariant section**: s_Q(σ) = v/√|Q(v)| for σ = [v],
  Q(v) ≠ 0. It is the normalisation of FS5 and RS2 (ℍ^n and dS^n as unit pseudo-spheres). Since
  Q(hv) = Q(v), **c_{s_Q} ≡ 1 on timelike and spacelike rays**: there the suspension is a genuine
  radius-preserving product, as in the Riemannian branch. The Euclidean cocycle ‖hσ‖ is a
  coboundary on S(V) ∖ {null rays}, with f(σ) = 1/(‖v‖·√|Q(v)|).
- **On null rays s_Q is undefined** (√|Q| → 0), and **no section repairs it**, even a discontinuous
  one. If hσ₀ = σ₀, then any coboundary gives c(h, σ₀) = f(σ₀)/f(σ₀) = 1, while in fact c(h, σ₀) is
  the eigenvalue λ of h on that ray. On a non-null fixed ray λ² = 1 is forced by Q(hv) = Q(v); on a
  null ray a boost has λ = e^{±t} ≠ 1. So:

  > **c restricted to a subgroup H' is a coboundary iff every element of H' acts with eigenvalue 1 on
  > each of its fixed null rays.**

  This is F2 with the hypothesis located exactly: an eigenvalue in ]0,1[ on a fixed vector of a
  linear map preserving Q can only occur on a null vector.
- **This is where BBS's pointwise stabiliser enters.** At a null ray p, the full stabiliser (the
  thesis's Aff(ℝ), REVIEW §B L2) contains the boost along p, with λ ≠ 1; the pointwise stabiliser
  Γ_p (BBS TeX l.762–764) is precisely the subgroup with λ = 1 on p. The pointwise choice makes c
  trivial *along the apex direction p itself*; it does not make c trivial on the link
  ℓ(p) = S(V/ℝp), where the null rotations still act by Euclidean similarities (L2's
  𝔼^{n−1}_± ⊔ S^{n−2} row).
- **On the photon sphere the cocycle is conformal geometry.** Restricted to the null rays
  ∂ℍ^n ≅ S^{n−1} with the section v = (1, ξ), c(h, ξ) is the first coordinate of h(1, ξ), which is
  (up to inversion) the conformal factor of the Möbius action of SO₀(1, n) on S^{n−1}. A section of
  the radial bundle over the photon sphere is therefore the same as a **conformal metric** in the
  round conformal class (pull back Q, which is degenerate exactly along the radial direction), and
  changing the section is a conformal change. This is the standard null-cone model of the conformal
  sphere, not something in Seppi's papers.
- **How Seppi's framework handles null rays: it doesn't normalise them.** FS1 ("the absolute"), RS1
  and RS13 treat the lightlike rays as the projective boundary of the q < 0 region, with only
  projective (hence, on ∂ℍ^n, conformal/Möbius) structure. Two consequences for us:
  1. REVIEW §D's "two flat conformal (Möbius, ℂP¹) structures" on a photon surface are the natural
     structure there, and the radial cocycle on a photon surface is a conformal density, not a
     radius.
  2. **There is no canonical c on all of HS^n; there is a canonical c on the complement of the photon
     locus (c ≡ 1), and a canonical cohomology class on all of HS^n.** For Lean the practical choice
     stands: use the Euclidean unit sphere (`GX.RaySphere`), c = ‖hσ‖, and prove separately that c
     is cohomologous to 1 on the non-null part.

### 8.3 Where the scalar cocycle c·r is not enough **[r]**

**(i) The suspension at a null point of an HS-link.** BBS build the HS-singularity 𝔢(L) at p ∈ HS²
from "the closed segment [−p, p] contained in the projective ray defined by v" (TeX l.776–778), glued
by Γ_p. Γ_p fixes the vector p, so on the 2-plane span(p, w) an element acts by a matrix
[[1, a], [0, b]] in the bases (p, w), (p, w'). In the radial coordinate ρ near p (chart [p + ρw]) this is

  ρ ↦ b ρ / (1 + a ρ),

a projective map of the segment fixing both endpoints. It is a pure scaling (a = 0) iff Γ_p preserves
a complement of ℝp:
- for non-null p, take p^⊥: a ≡ 0, and the author's scalar cocycle is exact;
- for **null** p, Γ_p is unipotent with a single invariant hyperplane, p^⊥, which contains p. So
  **no affine chart around p is Γ_p-invariant**, and a ≢ 0. Checked by hand on the parabolic
  generator of SO₀(1,2): v ↦ v, e ↦ e + a v, u ↦ u + a e + (a²/2) v.

So at photon, extreme-BTZ and cuspidal HS-singularities (BBS's light-like cases, TeX l.799 ff.), the
radial action is a cocycle with values in the projective transformations of [p, −p] fixing both ends,
≅ Aff⁺(ℝ) in the coordinate s = 1/ρ; only its derivative at the apex is the scalar c. The scalar
cocycle covers the point-suspension in V (flat spacetime points, the author's main case) and the
non-null HS points. **Proposal:** define the HS-level suspension with radial group Aff⁺(ℝ), and
recover the author's ruling as the case a = 0.

**(ii) The line model at a null singular line.** For a point y on a singular line of direction v, the
local model is "transverse cone × line" (REVIEW §B L1 gap: e(𝔢(L)) ≅ line × transverse cone). Choose a
complement W of ℝv. An element h of the pointwise stabiliser Γ_v acts as h(w + z v) = A w + (z + α(w)) v,
with A the induced map on V/ℝv ≅ W and α ∈ W*. In coordinates (σ, r, z), w = r s(σ):

  h·(σ, r, z) = (Aσ, c(h,σ) r, z + a(h,σ) r),  a(h, σ) = α_h(s(σ)),
  a(hk, σ) = a(h, kσ)·c(k, σ) + a(k, σ).

(c, a) is a cocycle into the lower-triangular group {[[c, 0], [a, 1]]} acting linearly on the (r, z)
half-plane. For non-null v take W = v^⊥ and a ≡ 0: the model is an honest product. For **null** v,
no invariant complement exists, so **the bridge to `quotientBase` is a twisted product, not a
product**. Note the shape: it is Danciger's half-pipe matrix [[Â, 0], [v, ±1]] (RS3; T4), with the
degenerate direction played by the null line. The analogy is suggestive (degenerate geometry appears
exactly where Q restricted to v^⊥ degenerates); it is not a theorem.

### 8.4 Spin, and the H¹ translation cocycle **[r] on quoted ground**

- Bonsante–Seppi (BS2–BS5) and Riolo–Seppi (CV1) write flat holonomy as (linear part, translation
  cocycle t ∈ Z¹(π₁, V)). Nie–Seppi (NS1–NS3) do the same over any proper convex cone.
- **No spin ⇔ the peripheral cocycle is a local coboundary ⇔ the peripheral holonomy fixes a point**
  (BS4–BS5 for elliptic; NS3 for parabolic, where the fixed set is a line). This is exactly the
  condition for each point of the singular line to have a **conical** neighbourhood, and exactly the
  content of BBS's "pointwise stabiliser".
- With spin (BM1–BM3), the peripheral holonomy is a screw motion, it fixes **no** point, and
  BM3 says the would-be singular line becomes "a circle and not a line". So:

  > **Spin is not an instance of the suspension.** The suspension needs a fixed apex; a spinning
  > particle's holonomy has none.

  In the line model of §8.3(ii) spin is a constant term τ: (σ, r, z) ↦ (Aσ, c r, z + a r + τ), with
  τ ≠ 0 exactly when the line is not pointwise fixed. gx's `massive_particle_intended` (screw motion,
  REVIEW §B L3b) lives here, not in L0.
- **Consequence for REVIEW §I ruling 1** ("spin come[s] later as further instances"): spin can come
  later as an instance of the **line model** (H = full stabiliser of the line acting on
  transverse cone × ℝ), but not of the point suspension. The thesis's full stabiliser at a null ray
  (with the boost along p) *is* a suspension instance, with a non-trivial c along p (§8.2).

### 8.5 The curvature-parameter suspension, κ ∈ {−1, 0, 1} (REVIEW §F Q8) **[r]**

**Claim.** Let X_κ be the Lorentzian space form of curvature κ (dS^{n+1}, M^{n+1}, AdS^{n+1}) or the
Riemannian one (S^{n+1}, 𝔼^{n+1}, ℍ^{n+1}), p ∈ X_κ, and V = T_pX_κ with its form Q. In the
projective (Klein) chart [p + w], w ∈ V:

1. X_κ ∩ chart = **D_κ := { w ∈ V : −κ Q(w) < 1 }**.
   Checks: AdS (κ = −1, Q(p) = −1, p^⊥ of signature (1, n)): Q(p + w) = −1 + Q(w) < 0 ⇔ Q(w) < 1.
   dS (κ = 1, Q(p) = 1): 1 + Q(w) > 0 ⇔ −Q(w) < 1. ℍ: |w| < 1. S, 𝔼: all w.
2. Geodesics from p are the rays w = ρv, and the arclength r is related to ρ by ρ = tn_{κε}(r), where
   ε = Q(v) ∈ {−1, 0, 1} for normalised v and tn₁ = tan, tn₋₁ = tanh, tn₀ = id. Along null rays ρ is
   already an affine parameter, defined only up to scale — consistent with §8.2.
3. **Stab_p(X_κ) acts linearly** on the chart (it preserves p^⊥), and it is the same H ≤ O(Q) for every
   κ. Hence the link (H, S(V)) and **the cocycle c are κ-independent**; D_κ is H-invariant because Q is.
4. **κ → 0 is Fillastre–Seppi's blow-up of a point** (FS10–FS11, T1): g_t = diag(1, 1/t, …, 1/t) fixes
   p, multiplies the chart by 1/t, commutes with H, and maps D_κ onto D_{κt²}. The stabiliser is
   unchanged along the whole transition; only the isometries that move p degenerate.

**Proposal.** One cocycle suspension Ĉ(L) (§8.1), and the κ-suspension is the **sub-cone-manifold
cut out by D_κ**, i.e. the points r·s(σ) with −κ Q(r s(σ)) < 1. This condition is invariant under the
cocycle action, since Q(c r s(hσ)) = Q(h·r s(σ)) = Q(r s(σ)), so it is well defined chart by chart on
an abstract L. For compact L it contains a neighbourhood of O. As a germ at p this is the curvature-κ
suspension; Thurston's sin²/r²/sinh² iteration (REVIEW §B L3a) is its Riemannian case, written
in arclength instead of the Klein parameter.

**Caveat.** BBS's AdS suspension e(HS²) = E(p) runs timelike rays to the first conjugate point
(TeX l.629–633), i.e. to −p, which leaves the affine chart. So the global object for κ = −1 is larger
than D_κ; the claim is about germs. For the classification of singular points, germs are what is
needed.

### 8.6 What Riolo–Seppi's 4-dimensional examples say about the 3+1 strata **[q] + [r]**

What occurs [q]:
- Σ is a **foam**: locally the cone over the 1-skeleton of a tetrahedron (RS5, RS8). The strata are
  the **generic (simple)** ones: a k-stratum lies in exactly 4−k bounding hyperplanes.
- Links (RS10, RS19): a point on a **2-stratum** has an HS³ cone-sphere link with singular locus an
  unknotted circle; on a **1-stratum**, an unknotted **theta graph**; at a **0-stratum**, the
  1-skeleton of a tetrahedron (**K₄**).
- On the AdS side **every** singular stratum is spacelike, inside the **de Sitter region** of the link
  (RS14, RS19); the meridian holonomy of a 2-stratum is a **boost** (RS7) — tachyonic sheets.
- At the transition the HS links degenerate to HP links: "the two timelike regions shrink to points
  and then disappear" (RS15, RS17).

Reading against REVIEW §D [r]:

| REVIEW §D stratum | Riolo–Seppi | comment |
|---|---|---|
| codim 2, Riemannian (spacelike) sheet, Γ_P = SO₀(1,1), tachyonic | **yes**, every 2-stratum, boost of magnitude β_t | link of a sheet point = HS³ with a spacelike unknotted circle; the transverse (Γ_P, S(V/P)) circle is BBS's hyperbolic circle |
| codim 2, timelike sheet (massive string) | no | their AdS polytopes have spacelike facets at Σ |
| codim 2, null sheet (photon) | no | |
| codim 3, spacelike junction line | **yes**, every 1-stratum: 3 sheets (theta graph) | the theta graph's two vertices are the ± directions of the edge; its point-link is an HS² sphere with three tachyons — REVIEW §D's "BBS Theorem 5.6 applies whole" row, in its simplest case |
| codim 3, timelike / null junction | no | |
| codim 4 vertex | **yes**: 4 edges, 6 sheets, link = HS³ cone-sphere with spacelike K₄ in the dS region | the generic vertex; examples arise as doubles of HS simplices (RS14), the "polyhedra in HS⁴" route of REVIEW §D |

Inferences [r]:
1. **These are also flat vertices.** By §8.5 the link of a point is the same (H, HS³)-object for κ = −1
   and κ = 0. So the flat cone Ĉ over Riolo–Seppi's K₄ cone-sphere is a flat 3+1 singular spacetime
   germ with a tachyonic foam vertex — a concrete codimension-4 example for REVIEW §D, available today.
2. **Generic singular loci in dimension 4 are foams, not surfaces.** RS6 says it is unknown whether
   finite-volume hyperbolic cone-manifolds with an embedded-surface singular locus can even deform.
   That supports NOTES N1's picture: strings bend and interact **only at junctions**.
3. **The HP meridians are dislocations.** On the HP side the meridian holonomy is an "infinitesimal
   rotation", which under the duality of RS4 / T3 is a **translation** of Minkowski space
   (§4.4 of 1908.05112, TeX l.1059–1062; RS18). In flat-spacetime language a translation holonomy around a
   codimension-2 locus is a dislocation — Barbot–Meusburger's θ₀ = 2π spinning particle (BM4) one
   dimension up. So the HP structures sit **outside** BBS's spinless (pointwise-stabiliser) world:
   their holonomy is the H¹ cocycle of CV1 with peripheral values that are **not** coboundaries.
4. **What does not appear.** No massive (timelike) or photon (null) strata, no junctions with ≥ 4
   sheets at a line, no knotted singular locus. N1's knotted strings and REVIEW §D's null junctions
   (a singular (E(2), 𝔼²₊ ⊔ S¹ ⊔ 𝔼²₋)-sphere) get **no examples** from these papers.

### 8.7 What this changes in REVIEW §B / §I, and what to check next

1. **L0 / `GX.ConicStructure`.** Make equivariance germ-wise (§8.1). Under ruling 3, the scalar
   cocycle is exact for flat points and non-null HS points, and is the first-order part at null HS
   points (§8.3). Recommend adding the Aff⁺(ℝ)-valued radial cocycle for the HS-level suspension
   𝔢(L) before formalising BBS's light-like singularities.
2. **L1 bridge.** "line × transverse cone" is a twisted product at null lines (§8.3(ii)). The
   `quotientBase` free factor Z must allow the shear z ↦ z + a r.
3. **Ruling 1 (spin later).** Spin enters through the line model, not the point suspension (§8.4).
4. **Q8.** κ lives in the domain D_κ, not in the cocycle (§8.5). A Lean statement: `D κ` is
   `H`-invariant, and `g_t '' D κ = D (κ * t^2)`.
5. **To check.**
   - The conformal-factor identification on ∂ℍ^n (§8.2) against a reference before citing it.
   - Whether BBS's own light-like HS-singularities (TeX l.799 ff.) use the projective segment action
     explicitly, as §8.3(i) predicts.
   - Nie–Seppi arXiv:2111.04532 (not fetched): regular domains for general cones.
   - Danciger's half-pipe papers (cited by Riolo–Seppi as [Dan11], [Dan13]), for the half-pipe /
     null-line analogy of §8.3(ii).
