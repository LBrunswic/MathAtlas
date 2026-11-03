# WP-45 — planning note for Chapter 1 (wave 0, 2026-11-03)

A plan, not a ruling: every choice below marked **[choice]** is the author's to confirm (DEC-112
fixed the layout and the scope, not these). Labels and line numbers are those of
`papers/benzecri/legacy/labeled/benzecri1960_ch1.tex` (ledger: 37 rows, 35 in the closure target,
`bzthm:intro_B`/`_C` terminal). Mathlib names are at the hub's pin `fabf563a` (v4.31.0), checked in
`lean-benzecri/.lake/packages/mathlib/`. The core imports Mathlib only.

## 1. Foundational choices

**F1. The sphere S(E) [choice].** Benzécri's S(E) is `(E ∖ 0)/ℝ₊*` (Déf. 3), the sphere of rays —
not ℝPⁿ, which is his P(E) and Mathlib's `Projectivization` (`ℙ K V`, `LinearAlgebra/Projectivization/
Basic.lean`); `Projectivization` is used for nothing but P(E). Three models exist:

| model | in Mathlib | for | against |
|---|---|---|---|
| (a) `Module.Ray ℝ E` = `RayVector ℝ E` (`{v // v ≠ 0}`) modulo `SameRay` (`LinearAlgebra/Ray.lean`) | the type, `rayOfNeZero`, `Module.Ray.map` for linear equivalences; **no topology** | it IS Déf. 3, for any `E`, with no norm | the quotient topology and its API are to be built |
| (b) the orbit quotient `MulAction.orbitRel.Quotient {x : ℝ // 0 < x} {v : E // v ≠ 0}` | `{x : ℝ // 0 < x}` is a `CommGroup` (`Algebra/Order/Positive/Field.lean`); orbit quotients and their topology exist | Déf. 3 literally, quotient topology for free | must be identified with (a) to reuse `SameRay` |
| (c) `Metric.sphere (0 : E) 1` for normed `E` | `homeomorphUnitSphereProd : {0}ᶜ ≃ₜ sphere 0 1 × Ioi 0`; `EuclideanSpace` spheres carry a `ChartedSpace`/manifold structure (`Geometry/Manifold/Instances/Sphere.lean`); compactness | topology, compactness and charts for free | needs a norm; the `GL` action must be renormalised, `g·σ = gσ/‖gσ‖` (this is lean-gx's `GX.RaySphere`, `GX/Suspension/Affine.lean`, which the core may not import) |

Proposal: define `Benzecri.Sphere E` as (a) with the quotient topology of `{v // v ≠ 0}` (so the
statement is the paper's), prove `Sphere E ≃ₜ Metric.sphere (0 : E) 1` for finite-dimensional
normed `E`, and transport compactness and the manifold structure along it. Finite dimension is a
**reading** of Déf. 3's « topologie localement convexe la plus fine » (which on a finite-dimensional
space is the usual topology): every result of Ch. 1 is about `S(n)`; disclose it in SCOPE. Index
shift: `S(n−1) = S(ℝⁿ)` (p. 236), so the model of an n-manifold is `S(n) = Sphere (Fin (n+1) → ℝ)`.

**F2. (G,X)-structures [choice].** A locally projective (resp. affine) n-manifold is
`[ChartedSpace X V] [HasGroupoid V (gxGroupoid G X)]` with `(G, X) = (GS(n,ℝ), S(n))` (resp.
`(GA(n,ℝ), ℝⁿ)`), over the maximal atlas, exactly as lean-gx does it (DEC-16 there). Mathlib:
`StructureGroupoid`, `Pregroupoid`, `Pregroupoid.groupoid`, `ChartedSpace`, `HasGroupoid`,
`StructureGroupoid.maximalAtlas` (`Geometry/Manifold/{StructureGroupoid,ChartedSpace,HasGroupoid}.lean`),
`OpenPartialHomeomorph` (the renamed `PartialHomeomorph`). The groupoid of a group action — "near
each point the restriction of some `g ∈ G`" — is `GX.gxGroupoid` (`lean-gx/GX/Structure/Basic.lean`,
`gxPregroupoid`/`gxGroupoid`/`mem_gxGroupoid_iff`/`closedUnderRestriction_gxGroupoid`, ~150 lines
of its 911). It must NOT be imported (DEC-112): port a minimal `Benzecri.gxGroupoid` (definition,
membership lemma, `ClosedUnderRestriction`, transition = locally an element of `G`, monotonicity in
`G` and in an open `X' ⊆ X`), citing the gx original; the generalisation layer later proves
`Benzecri.gxGroupoid G X = GX.gxGroupoid G X` (definitional by construction) as its bridge.

**F3. Jets [choice].** Déf. 12 defines a structure by an open set `J(V)` of « jets d'isomorphismes »
(germs of local homeomorphisms into the model) on whose fibres `G` acts transitively; Prop. 3 says
an atlas with transitions in `G` gives one. Proposal: take the atlas form (F2) as the definition and
prove Déf. 12's form as a theorem (`bzdef:c1s1d12_…` certified by the equivalence: germs of
maximal-atlas charts form a set `J(V)` satisfying 1° and 2°, and conversely). `Filter.Germ` gives
germs; the topology of `J(V)` (needed by Prop. 2's proof and § 2's `FJ(B)`) is the étalé topology,
which Mathlib does not have for germs of maps — so wherever the paper uses `J(V)` as a space,
replace a germ by a (maximal-atlas chart, point) pair modulo agreement near the point, which is
what § 2's construction needs (F5). « Isomorphisme » is read as homeomorphism: the paper never
mentions differentiability, and transitions in `G` are analytic anyway.

**F4. Affine geometry.** Déf. 1 is Mathlib's `AddTorsor (T A) A` exactly (`V →ᵥ`, `-ᵥ`, `+ᵥ`);
`MN` is `N -ᵥ M`. Déf. 2 is `AffineMap` — with one reading: the printed definition does not ask `l'`
to be linear (only `l(M+m) = l(M) + l'(m)`), which makes `l'` additive; over ℝ, linearity needs
continuity or is assumed. Record it under `questions`. `GA(n, ℝ)` = `(Fin n → ℝ) ≃ᵃ[ℝ] (Fin n → ℝ)`
(`AffineEquiv`), `GL(n, ℝ)` = `GL (Fin n) ℝ` or `(Fin n → ℝ) ≃ₗ[ℝ] _`.

**F5. Categories [choice].** § 2 claims an « isomorphisme fonctoriel » between affine cones of
dimension n and locally projective manifolds of dimension n−1 (`bzthm:c1s2_isomorphisme_fonctoriel`).
On the nose it is not an isomorphism of categories (`F⁻¹(F(B))` is canonically isomorphic, not
equal, to `B`): the formal target is a `CategoryTheory.Equivalence` (functors both ways, natural
isomorphisms), which is how the statement should be read; record it as a reading, not a finding.
Morphisms (p. 238, the paragraph after Prop. 3) are maps whose germs pull projective jets back to
projective jets, i.e. local `(G,X)`-isomorphisms (`φ'` in the proof is « un isomorphisme local »),
between manifolds of the same dimension. Objects should be bundled
(`structure LocProj (n) where carrier : Type, [top, charted, groupoid]`), with `Type` universe 0.

**F6. Implicit hypotheses.** *Variété* = connected (Déf. 12 prints « convexe », read « connexe »),
Hausdorff, second countable (needed: § 2's section of `F(B) → B` uses paracompactness, p. 241).
Carry them as hypotheses where used, not in the definition; each is a `questions` entry.

## 2. Statement by statement

`size` is a rough count of Lean lines, statement and proof, for the planned module.

### § 1 Géométrie affine et géométrie projective

| label | Mathlib / construction | module | size |
|---|---|---|---|
| `bzdef:c1s1d1_espace_affin` | `AddTorsor`; the example (E acting on itself) is the instance `addGroupIsAddTorsor` | `Affine/Basic` | 40 |
| `bzdef:c1s1d2_application_affine` | `AffineMap`, plus the printed form with `l'` merely additive, equivalent under continuity (F4); the example (affine functions to ℝ) is `AffineMap _ _ ℝ` | `Affine/Basic` | 80 |
| `bzdef:c1s1d3_sphere` | `Benzecri.Sphere E` (F1): `s : {v // v ≠ 0} → Sphere E`, `F : Set (Sphere E) → Set E` (preimage), quotient topology, `≃ₜ` unit sphere; `P(E)` is `ℙ ℝ E`, with the 2-to-1 map `Sphere E → ℙ ℝ E` | `Projective/Sphere` | 300 |
| `bzdef:c1s1d4_sous_variete_lineaire` | image `s(L ∖ 0)` of a `Submodule`; the examples: antipodal pairs, lines, half-lines, hyperplanes (printed « S(T) », read S(E)) | `Projective/Subvariety` | 150 |
| `bzdef:c1s1d5_hemisphere` | `{x | 0 < l x}` for `l : E →L[ℝ] ℝ` (finite dim: `Module.Dual`), equation unique up to `ℝ₊*`; boundary hyperplane `l⁻¹ 0`; closed hemisphere; the converse paragraph (complement of a hyperplane = two open hemispheres `l`, `−l`) proved beside it | `Projective/Subvariety` | 200 |
| `bzdef:c1s1d6_structure_affine_hemisphere` | `AddTorsor (E/N →ₗ N) H` by `m + u = s(M + u(q M))` (`q = Submodule.mkQ N`); independence of `M ∈ F(m)` (printed « de m »); isomorphism with the affine hyperplane `l = 1` (`AffineSubspace`), hence with `ℝⁿ` (the p. 236 sentence) | `Projective/Hemisphere` | 300 |
| `bzdef:c1s1d7_segment` | closed/open segment `s(segment ℝ M M')`, independence of the lifts (`SameRay`) | `Projective/Convex` | 120 |
| `bzdef:c1s1d8_partie_convexe` | `Convex ℝ (F k ∪ {0})` (printed « F(k) + {O} »), i.e. `F k ∪ {0}` a convex cone (`ConvexCone`, `PointedCone`); equivalence with the segment form | `Projective/Convex` | 200 |
| `bzdef:c1s1d9_convexe_strict` | no antipodal pair, i.e. the cone is salient (`ConvexCone.Salient`) | `Projective/Convex` | 60 |
| `bzdef:c1s1d10_quotient` | `S(E)/l := Sphere (E ⧸ L)`, the identification of convex sets containing `l` with convex sets of the quotient | `Projective/Subvariety` | 200 |
| `bzdef:c1s1d11_corps_convexe` | compact, convex, nonempty interior in `ℝⁿ`; in `S(n)`: compact strict convex with nonempty interior; `EA(n)`, `E(n)`, `CA(n)` as sets (Mathlib `ConvexBody` lacks the interior condition) | `Projective/Convex` | 120 |
| (prose p. 236) | `GS(n−1, ℝ) = GL(n)/ℝ₊*` acting on `S(n−1)`, `GP`, `GU(n) = {g | |det g| = 1}`, `GL = ℝ₊* × GU` and the isomorphism `i : GS(n−1) ≃* GU(n)`, `g ↦ |det g|^(−1/n) g` | `Projective/Groups` | 300 |
| `bzdef:c1s1d12_variete_localement_projective` | F2 + F3: atlas definition, Déf. 12's jet form as a theorem; `J(V) → V` a covering | `Structure/Basic` | 300 |
| `bzrem:c1s1r1_affine_vers_projective` | an affine structure induces a projective one through a hemisphere chart `ℝⁿ ≃ H ⊂ S(n)`: `GA(n)` embeds in `GS(n)` as the stabiliser of `H` (`HasGroupoid` monotone along an inclusion of `(G,X)`) | `Structure/Basic` | 150 |
| `bzdef:c1s1d13_carte_compatible` | `e ∈ (gxGroupoid G X).maximalAtlas V` | `Structure/Basic` | 20 |
| `bzprop:c1s1p1_cartes_compatibles` | two compatible charts of a CONNECTED `U` differ by a unique `g` (needs rigidity: an element of `GS`/`GA` agreeing with the identity on an open set is the identity — lean-gx's `IsRigidAction`, to port) and existence of a chart with a given germ | `Structure/Basic` | 200 |
| `bzprop:c1s1p2_developpement` | the developing map of a simply connected manifold, unique up to `G`, a local homeomorphism (`IsLocalHomeomorph`): « ouvert étalé » (kb/0001). Template: lean-gx `GX/Structure/Developing.lean` (581 lines, `developing_theorem`), by path lifting (`Topology/Homotopy/Lifting.lean`, `IsCoveringMap.liftPath`, `monodromy_theorem`) and `SimplyConnectedSpace` | `Structure/Developing` | 700 |
| `bzprop:c1s1p3_atlas` | an atlas with transitions in `G` generates a `HasGroupoid` structure: `ChartedSpace` from the atlas + `hasGroupoid_of_pregroupoid`; uniqueness = equality of maximal atlases | `Structure/Basic` | 150 |
| (prose p. 238) | the category; `V/G` for `G` properly discontinuous and free (`ProperlyDiscontinuousSMul`, `isCoveringMap` of the quotient, `Topology/Covering/Quotient.lean`); étalé pull-back; coverings and the universal cover | `Structure/Quotient` | 400 |
| `bzdef:c1s1d14_segment_variete` | a set mapped onto a segment by a compatible chart defined near it | `Structure/Classes` | 60 |
| `bzdef:c1s1d15_homogene_balayable_divisible` | homogeneous (transitive automorphism group), sweepable (`∃ K compact, ⋃ g, g • K = univ`), divisible (a free properly discontinuous subgroup with compact quotient); the prose facts « divisible ⇒ balayable », « homogène ⇒ balayable » | `Structure/Classes` | 150 |
| `bzdef:c1s1d16_maximale` | maximal; « compact ⇒ maximal » (an open embedding of a compact connected manifold into a connected one of the same dimension is onto: clopen image) | `Structure/Classes` | 120 |

### § 2 Variétés coniques affines

| label | Mathlib / construction | module | size |
|---|---|---|---|
| `bzdef:c1s2d1_cone_ouvert` | `IsOpen C`, `C ⊆ {0}ᶜ`, `∀ x ∈ C, ∀ t > 0, t • x ∈ C` | `Cone/Basic` | 40 |
| `bzdef:c1s2d2_variete_conique_affine` | `(GU(n), ℝⁿ ∖ 0)`-structure (F2) with charts onto open cones (3°; printed « définition 2 », read Déf. 13) | `Cone/Basic` | 150 |
| `bzprop:c1s2p1_atlas_conique` | the conical analogue of `bzprop:c1s1p3_atlas` (printed `{V_i}`, `f_i = g_ij ∘ f_i`: read `{U_i}`, `f_j`); plus the canonical affine structure (`GU(n) ⊆ GA(n)`, monotonicity) and the category | `Cone/Basic` | 200 |
| `bzdef:c1s2d3_homotheties_positives` | the `ℝ₊*`-action `λm = f⁻¹(λ f(m))`, well defined because `GU(n)` commutes with homotheties; a free action by affine (not conical) automorphisms; principal bundle | `Cone/Basic` | 300 |
| `bzprop:c1s2p2_base_cone` | `B = V/ℝ₊*` (orbit quotient) with the `(GS(n−1), S(n−1))`-structure whose charts are the quotients of cone charts, `GU(n) → GS(n−1)` the inverse of `i`; Hausdorffness of `B` needs properness of the action (state it) | `Cone/Base` | 400 |
| (prose p. 241) | a section of `V → B` (contractible fibre, paracompact base): build it as a homogeneous « norm » `N : V → ℝ₊*`, `N(λx) = λN(x)`, glued from chart norms by a partition of unity (`PartitionOfUnity`, `BumpCovering`), the section being `N = 1` | `Cone/Section` | 350 |
| `bzthm:c1s2_isomorphisme_fonctoriel` | `F(B) = FJ(B)/ℛ`, with a jet replaced by a pair (maximal-atlas chart `e` at `b`, point) (F3): `{(e, b, m) | b ∈ e.source, m ∈ ℝⁿ∖0, s m = e b}` modulo `(e,b,m) ~ (e',b,i(g)m)` when `e = g ∘ e'` near `b`; its conical structure, `F` on morphisms (local isomorphisms), the base functor `F⁻¹`, and the equivalence (F5) | `Cone/Functor` | 1000 |

### § 3 Applications

| label | Mathlib / construction | module | size |
|---|---|---|---|
| `bzprop:c1s3p1_F_homogene` | `F(φ)` and homotheties generate the needed automorphisms; sweepable through a compact section `K₁` over `K` (printed « § 1, déf. 2 », read déf. 15); divisible through `F(G) × λ^ℤ` | `Applications/Circle` | 300 |
| `bzcor:c1s3p1c_produit_cercle` | `F(B)/λ^ℤ ≃ₜ B × S¹` by the section (S¹ = `AddCircle (log λ)` or `Circle`), affine as the quotient of a locally affine manifold by a free properly discontinuous group of affine automorphisms. No compactness is printed and none is needed | `Applications/Circle` | 300 |
| `bzdef:c1s3d1_produit_cones` | product cone `F(B₁) × … × F(B_p)`: a conical structure on `∏ (ℝ^{n_i} ∖ 0) ⊂ ℝ^{Σ n_i} ∖ 0` with `∏ GU(n_i) ↪ GU(Σ n_i)` block-diagonally (det multiplies); the `ℝ₊*^p`-action | `Applications/Products` | 300 |
| `bzprop:c1s3p2_fibre_produit` | `ℝ₊*^p/ℝ₊*` acts on `F⁻¹(∏ F(B_i))` with base `∏ B_i`, through the lift « product = 1 » | `Applications/Products` | 250 |
| `bzprop:c1s3p3_produit_homogene` | `F_i(φ_i)` and the torus action; the proof given is the divisible case (with a lattice `H ≅ ℤ^{p−1}`, printed `R^{+p}/R^p`, read `/R^+`) | `Applications/Products` | 300 |
| `bzcor:c1s3p3c_produit_projectif` | `∏ B_i × (S¹)^{p−1}` projective | `Applications/Products` | 150 |
| `bzdef:c1s3d2_automorphisme_compatible` | permutation `σ ∈ Equiv.Perm (Fin p)`, conical isomorphisms `F(B_{σ i}) ≃ F(B_i)`, `f ∈ {F⁻¹(φ)} × (ℝ₊*^p/ℝ₊*)` | `Applications/Converse` | 150 |
| `bzprop:c1s3p4_reciproque` | `G_I` of index ≤ p! (the map `G → Perm (Fin p)`); the composite of `h` isomorphisms along the cycle of 1 | `Applications/Converse` | 300 |
| `bzthm:intro_A` | the assembly of the two corollaries, for compact manifolds | `Applications/TheoremA` | 60 |
| `bzthm:intro_B`, `bzthm:intro_C` | terminal here (Ch. 2 § 3, Ch. 5 § 3) | — | — |

The § 3 example (genus-p surface × circle affine, via Fuchsian groups acting on the Klein disc) is
an EXEMPLE, not a ledger row; it needs uniformisation and is off the spine.

## 3. Module split and dependency order

```
L0  Affine/Basic            (~150)   Defs 1-2
L0  Projective/Sphere       (~350)   Def 3, F1
L0  Structure/Groupoid      (~250)   F2: local gxGroupoid port, rigidity of GS/GA/GU
L1  Projective/Groups       (~300)   GL, GA, GS, GP, GU, i            ← Sphere
L1  Projective/Subvariety   (~550)   Defs 4, 5, 10                    ← Sphere
L2  Projective/Hemisphere   (~300)   Def 6                            ← Subvariety, Affine/Basic
L2  Projective/Convex       (~500)   Defs 7-9, 11                     ← Subvariety
L3  Structure/Basic         (~800)   Defs 12-13, Rem, Props 1, 3      ← Groupoid, Groups, Hemisphere
L3  Structure/Quotient      (~400)   prose p. 238: category, V/G, étalé pull-back
L4  Structure/Developing    (~700)   Prop 2                           ← Basic
L4  Structure/Classes       (~330)   Defs 14-16                       ← Basic, Quotient, Convex
L4  Cone/Basic              (~690)   §2 Defs 1-3, Prop 1              ← Basic, Groups
L5  Cone/Base               (~400)   §2 Prop 2                        ← Cone/Basic
L5  Cone/Section            (~350)   section of V → B                 ← Cone/Basic
L6  Cone/Functor            (~1000)  the functorial isomorphism       ← Cone/Base
L7  Applications/Circle     (~600)   §3 Prop 1 + Cor                  ← Functor, Section, Quotient, Classes
L7  Applications/Products   (~1000)  §3 Def 1, Props 2-3 + Cor        ← Functor, Section, Quotient
L8  Applications/Converse   (~450)   §3 Def 2, Prop 4                 ← Products
L8  Applications/TheoremA   (~60)    intro A                          ← Circle, Products
```

About 9,000 lines, 19 modules, nine layers; each layer's files are disjoint and can be authored in
parallel (DEC-38 waves). Suggested waves: **W1** = L0 + L1 (five files), **W2** = L2 + L3, **W3** =
L4 + L5, **W4** = L6 (the functor, one author, the hardest file), **W5** = L7 + L8. The spine to
Theorem A is Sphere → Groups → Groupoid → Structure/Basic → Quotient → Cone/Basic → Cone/Base →
Cone/Section → Cone/Functor → Circle/Products → TheoremA; Developing, Convex, Classes (except the
sweepable/divisible definitions § 3 uses) and Converse are off it and may lag.

## 4. Relation to lean-gx (later layers, not now)

The generalisation layer requires `lean-gx` at a gated commit and proves the bridges: `Benzecri.
gxGroupoid = GX.gxGroupoid`; `Benzecri.Sphere E ≃ₜ GX.RaySphere E` (gx's unit-sphere model,
`GX/Suspension/Affine.lean`, whose own docstring leaves this homeomorphism unformalized); Prop. 2 ↔
`GX.developing_theorem`; the affine cone `F(B)` ↔ gx's celestial suspension (`GX.Suspension.
Celestial`), the singular (BBS) version being the planned `RadiantCone`/`ProjectiveCone` modules
that DEC-112 moves here (papers/bbs NOTES-3+1 N7).
