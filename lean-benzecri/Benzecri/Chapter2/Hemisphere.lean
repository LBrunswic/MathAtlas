import Benzecri.Chapter2.PseudoBoules
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.Convex.Contractible
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-!
# Chapter 2 § 3, Prop. 2 — a connected sweepable locally projective manifold spread over `S(n)`, with the closure of `p(V)` in an open hemisphere, is the interior of a convex body

J.-P. Benzécri, *Sur les variétés localement affines et localement projectives*, Bull. SMF 88
(1960) 229–332, Chapter 2 § 3, journal pp. 257–259; transcription
`papers/benzecri/legacy/labeled/benzecri1960_ch2.tex` (l.718–800 read against the scan, PDF
pp. 30–32). Target T-bz-c2-hemisphere (DEC-137).

* **`bzprop:c2s3p2_hemisphere_corps_convexe`** — `benzecri1960_ch2.tex:718` (Prop. 2, l.718–724,
  proof l.726–800): `Benzecri.hemisphere_corps_convexe`, every dimension, sorry-free. `p` is a
  compatible chart (Déf. 13) with source `V`, target `int K` and underlying map `p`, where `K` is a
  convex body (Déf. 11). Besides, `int K` is the proof's `W`, the convex hull of `p(V)`
  (`enveloppeConvexe`: the least convex part containing `p(V)`, `enveloppeConvexe_isLeast`, and it
  lies in `H̊`, `enveloppeConvexe_subset_hemisphere`). The printed form over the paper's manifolds
  is `hemisphereCorpsConvexePrinted n`, for every `n`.

> **Proposition 2.** Soit $V$ une variété localement projective connexe balayable munie d'une
> projection $p$ sur $S(n)$ compatible avec la structure projective [$V$ est un ouvert étalé sur
> $S(n)$]. Supposons de plus qu'il existe un hémisphère ouvert $\mathring{H}$ de $S(n)$ tel que
> $\overline{p(V)}\subset\mathring{H}$. Alors $p$ est une carte de $V$ sur l'intérieur d'un corps
> convexe de $S(n)$.
>
> L'enveloppe convexe de $p(V)$ [i. e. le plus petit convexe de $\mathring{H}$ contenant $p(V)$]
> est un convexe $W$, intérieur d'un corps convexe : nous allons montrer que $p$ est une carte de
> $V$ sur $W$. […] 1° Soit $g$ un automorphisme projectif de $V$, il existe un élément unique
> $\gamma\in GS(n, \R)$ tel que $p\circ g=\gamma\circ p$. $\gamma$ est un automorphisme
> projectif de $W$. […] 2° Tout point $M\in V$ possède un voisinage $O_M$ tel que la restriction de
> $p$ à $O_M$ soit une carte sur une pseudo-boule (*cf.* § 2, déf. 5) de centre $p(M)$ et de rayon
> $r$ convenable. […] 3° Il existe un nombre $r$ positif, tel que tout point $M$ de $V$ possède un
> voisinage $O_M$ pseudo-boule de centre $M$ et de rayon $r$. Remarquons d'abord que, si $E$ est un
> compact de $V$, il existe $r(E)$ tel que tout point de $E$ soit centre d'une pseudo-boule de rayon
> $r(E)$ : cela résulte de 2°, de la continuité de la pseudo-longueur sur $W$, et de la compacité
> de $E$. […] 4° $p(V)=W$. […] Donc $p(V)=W$ (*cf.* § 2, prop. 5). 5° $V$ est un revêtement de
> $W$. […] deux sections d'un ouvert étalé (ici $V$) au-dessus d'une même partie connexe de la base
> (ici la pseudo-boule de centre $m$ et de rayon $r$) sont identiques ou d'intersection vide. […]
> (une telle pseudo-boule existe dans $V$ d'après 4°) […] Le point 5° une fois établi, la
> proposition résulte trivialement de ce que $V$ est connexe, et $W$ simplement connexe.

## The proof formalized (the paper's five points)

*`W`.* `enveloppeConvexe A` is the set of rays of the convex hull of the cone `F(A)`; it contains
`A`, is open when `A` is, and is the least convex part (Déf. 8) containing `A`. For `A = p(V)`, its
closure `K` is a convex body (`isCorpsConvexeS_closure_enveloppeConvexe`): the compact
`closure p(V) ⊆ H̊ = {l > 0}` gives `c ‖v‖ ≤ l v` on its cone, and the closed convex cone
`{c ‖v‖ ≤ l v}` contains the closure of the hull, so `F(K)` is convex and `K ⊆ H̊`.
*1°.* `γ` is `IsDeveloping.existsUnique_smul_eq` applied to `p` and `p ∘ g` (no pocket is needed).
It maps `p(V)` onto itself, hence its hull (`smul_enveloppeConvexe_subset`: a linear map commutes
with convex hulls), hence `K` and `int K`. As a projective automorphism of `W = int K`
(`autInterior`) it maps pseudo-balls onto pseudo-balls of the same radius
(`image_pseudoBoule_autInterior`, through `IsMajoreSeg.smul`).
*2°.* A *sheet* of centre `M` and radius `r` (`HasFeuille`) is an open `O ∋ M` on which `p` is
injective with image the pseudo-ball of `W` of centre `p(M)` and radius `r` (`IsFeuille`). One
exists for some `r > 0` (`exists_hasFeuille`, from `hasBasis_pseudoBoule`, `n ≥ 1`).
*3°.* Near a point of `W`, the pseudo-balls of one radius `s > 0` all lie in a given neighbourhood
(`exists_pos_eventually_pseudoBoule_subset`: by the continuity of `l_W` on `W × W`, `l_W ≥ s` on
`D × frontier C` for compact neighbourhoods `D ⊆ int C`, and a connected pseudo-ball centred in `D`
cannot cross `frontier C`). Hence one radius serves a compact set (`exists_hasFeuille_of_isCompact`);
automorphisms carry sheets to sheets of the same radius (`HasFeuille.smul`, by 1°), so one radius
`r > 0` serves all of the sweepable `V` (`exists_hasFeuille_uniform`).
*4°.* Prop. 5 (`ouvert_plein`) in `W` with this `r > 0`: `p(V) = int K` (`range_eq_interior`).
*5°.* Over the pseudo-ball of centre `m` and radius `r`, the sheets centred at the points of
`p⁻¹(m)` are pairwise disjoint and cover its preimage. Both follow from the section lemma
`mem_of_injOn_of_isPreconnected`: it is applied to the pseudo-ball for disjointness, and to a
segment majorised by `r` from `m` to `p(N)` for the covering. Mathlib's
`IsOpen.trivializationDiscrete` then gives `IsCoveringMapOn p (int K)` (`isCoveringMapOn_interior`).
*Final step.* `int K` is homeomorphic to the convex set `F(int K) ∩ {ℓ = 1}`, hence contractible,
hence simply connected (`simplyConnectedSpace_corpsInterior`). The inclusion of `int K` lifts
through `p` (Mathlib's `IsCoveringMapOn.existsUnique_continuousMap_lifts`) to a section `F`. The set
`{M | F(p(M)) = M}` is clopen (`V` Hausdorff, `p` a local homeomorphism), so it is `V`, and `p` is
injective (`injective_of_isCoveringMapOn`). An injective developing map is a compatible chart onto
its image (`exists_chart_of_injective`).
*Dimension 0.* A connected `V` is a point (`subsingleton_dim_zero`), and `{p(M)}` is a convex body
of `S(0)` equal to its interior.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| « $V$ une variété localement projective » | ✓ carried: `[ChartedSpace (S n) V] [HasGroupoid V (projGroupoid n)]`, « variété » read Hausdorff (`[T2Space V]`, the standing reading: docs/CAMPAIGN.md, plan F6, DEC-122; the statement fails without it, SCOPE); second countability never used |
| « connexe » | ✓ carried: `[ConnectedSpace V]` (Mathlib's: nonempty, since a « variété » is nonempty, DEC-128; for `V = ∅` the conclusion fails, `int K` being nonempty) |
| « balayable » | ✓ carried: `IsBalayable (GSR n) (S n) V` (Déf. 15, for the whole group of projective automorphisms) |
| « munie d'une projection $p$ sur $S(n)$ compatible avec la structure projective [$V$ est un ouvert étalé sur $S(n)$] » | ✓ carried: `IsDeveloping (GSR n) p` (every jet of `p` in `J(V)`, Ch. 1 Prop. 2), as in Prop. 1 (`Benzecri.Chapter2.Projection`); « sur » not read as « onto » |
| « un hémisphère ouvert $\mathring{H}$ de $S(n)$ » | ✓ carried: `Sphere.IsOpenHemisphere H` (Déf. 5 as printed; its `l = 0` gives `H = ∅`, excluded by the next row since `V ≠ ∅`) |
| « $\overline{p(V)}\subset\mathring{H}$ » | ✓ carried: `closure (range p) ⊆ H` |
| « $p$ est une carte de $V$ sur l'intérieur d'un corps convexe de $S(n)$ » | ✓ carried: `∃ K, IsCorpsConvexeS n K ∧ ∃ φ, IsCompatibleChart (GSR n) φ ∧ φ.source = univ ∧ φ.target = interior K ∧ ⇑φ = p`; ✓ carried, and more (Lean ≥ paper), by `interior K = enveloppeConvexe (range p)`, the proof's `W` |
| the dimension `n` | ✓ carried: every `n`, `n = 0` included (no `NeZero n`) |

## SCOPE (disclosed)

* **Misprints flagged `[sic]` in the transcription, formalized as read** (not findings): « *cf.*
  § 2, déf. 5 » (l.750) is read déf. 6, the pseudo-ball; « d'après 4° » (l.796) is read 3°, the
  uniform radius.
* **« variété » is read Hausdorff** (the standing reading, DEC-122 and plan F6; the reading of every Benzécri file). The proof uses
  it in 2° (the lift of `(m, n)` is the only segment from `M`) and in 5° (« deux sections … sont
  identiques ou d'intersection vide »: on the line with two origins over `ℝ`, two sections over `ℝ`
  agree off one point). The statement needs it too (argued, not formalized). Let `W` be an open
  segment of `S(1)` whose closure lies in an open hemisphere, `h` a hyperbolic projective
  transformation preserving `W`, and `D = {hᵏ(m₀) : k ∈ ℤ}`. Doubling every point of `D` gives a
  connected non-Hausdorff locally projective `V` (two copies of `W` glued along `W ∖ D`) with the
  developing map `p : V → W`. It is swept by `h`, acting on both copies, and by the exchange of the
  copies, with the compact generating domain made of one copy of `[m₀, h(m₀)]` and the other `m₀`.
  The closure of `p(V)` lies in the hemisphere, and `p` is not injective.
* **Prop. 5's radius (OQ-62) does not matter here.** Prop. 5 is applied (4°) with the radius of 3°,
  which is `> 0` by construction (a radius-`0` pseudo-ball is empty, so it could not be the
  neighbourhood of 2°), and `ouvert_plein` is proved for every `r > 0`. Either answer to OQ-62
  leaves this row unchanged.
* **OQ-45 does not reach this row.** `hasBasis_pseudoBoule` (`n ≥ 1`) is used only for `n ≥ 1`; for
  `n = 0` the statement holds trivially, so Prop. 2 holds as printed in every dimension
  (`hemisphereCorpsConvexePrinted`).
* **Finding in the proof, 3° (l.759–762), statement unaffected**: « cela résulte de 2°, de la
  continuité de la pseudo-longueur sur $W$, et de la compacité de $E$ ». Continuity and compactness
  alone do not give `r(E)`. One needs, for the points `M'` near `M`, the pseudo-balls of a fixed
  radius centred at `p(M')` inside the pseudo-ball of 2° at `p(M)`. A triangle inequality for
  `l_W` would give this, but it is not among properties 1°–7° (l.229–259). Continuity controls
  `l_W(p(M'), ·)` near `p(M)` but not uniformly towards the frontier of `W`. The formalization adds
  the connectedness of the pseudo-balls and the local compactness of `W`
  (`exists_pos_eventually_pseudoBoule_subset`, the argument of `hasBasis_pseudoBoule` made uniform).
* **The sheets are not the paper's intrinsic `O_M`.** The description « $O_M$ est le lieu des points
  $N$ … » (l.746–748) is not formalized. A sheet is any open set on which `p` is injective with
  image the pseudo-ball, and the sheets used in 5° are compared through the section lemma.
* **The covering is a covering over `int K`** (`IsCoveringMapOn p (interior K)`, Mathlib's notion,
  with fibres `p⁻¹(m)` as the discrete index of the trivialisation). Its lifting theorem replaces
  « $W$ simplement connexe ».
* General lemmas proved here, candidates to move upstream: `mem_of_injOn_of_isPreconnected` (the
  section lemma, any open map into any space from a Hausdorff space),
  `simplyConnectedSpace_corpsInterior`, `exists_pos_eventually_pseudoBoule_subset`,
  `isOpen_image_pseudoBoule`, `isPreconnected_image_pseudoBoule`, `autInterior` and
  `image_pseudoBoule_autInterior`, `exists_chart_of_injective`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

noncomputable section

open Set Filter Topology
open scoped Pointwise

namespace Benzecri

universe u

/-! ### Two sections of a spread space over a connected set agree or are disjoint (5°) -/

section Sections

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- **« Deux sections d'un ouvert étalé au-dessus d'une même partie connexe de la base sont
identiques ou d'intersection vide »** (5°, l.786–789), for a Hausdorff `X`: let `O`, `O'` be open
sets on which the open map `p` is injective, and `B` a preconnected set lying under both; if the
two sections over `B` meet, then every point of `O` over `B` lies in `O'`. -/
theorem mem_of_injOn_of_isPreconnected [T2Space X] {p : X → Y} (hp : IsOpenMap p) {O O' : Set X}
    (hO : IsOpen O) (hO' : IsOpen O') (hi : InjOn p O) (hi' : InjOn p O') {B : Set Y}
    (hB : IsPreconnected B) (hBO : B ⊆ p '' O) (hBO' : B ⊆ p '' O') {x : X} (hx : x ∈ O)
    (hx' : x ∈ O') (hxB : p x ∈ B) {y : X} (hy : y ∈ O) (hyB : p y ∈ B) : y ∈ O' := by
  have hTo : IsOpen (p '' (O ∩ O')) := hp _ (hO.inter hO')
  have hBT : B ⊆ p '' (O ∩ O') := by
    refine hB.subset_of_closure_inter_subset hTo ⟨p x, hxB, x, ⟨hx, hx'⟩, rfl⟩ ?_
    rintro b ⟨hbcl, hbB⟩
    obtain ⟨z, hz, rfl⟩ := hBO hbB
    obtain ⟨z', hz', hzz'⟩ := hBO' hbB
    by_contra hbT
    have hne : z ≠ z' := by
      rintro rfl
      exact hbT ⟨z, ⟨hz, hz'⟩, rfl⟩
    obtain ⟨u, u', hu, hu', hzu, hzu', huu'⟩ := t2_separation hne
    have hN : p '' (u ∩ O) ∩ p '' (u' ∩ O') ∈ 𝓝 (p z) :=
      inter_mem ((hp _ (hu.inter hO)).mem_nhds ⟨z, ⟨hzu, hz⟩, rfl⟩)
        ((hp _ (hu'.inter hO')).mem_nhds ⟨z', ⟨hzu', hz'⟩, hzz'⟩)
    obtain ⟨t, ⟨⟨w, ⟨hwu, hwO⟩, hwt⟩, ⟨w', ⟨hw'u, hw'O⟩, hw't⟩⟩, y₀, ⟨hy₀O, hy₀O'⟩, hy₀t⟩ :=
      mem_closure_iff_nhds.1 hbcl _ hN
    have h1 : w = y₀ := hi hwO hy₀O (hwt.trans hy₀t.symm)
    have h2 : w' = y₀ := hi' hw'O hy₀O' (hw't.trans hy₀t.symm)
    subst h1 h2
    exact Set.disjoint_left.1 huu' hwu hw'u
  obtain ⟨z, ⟨hzO, hzO'⟩, hz⟩ := hBT hyB
  rw [hi hy hzO hz.symm]
  exact hzO'

end Sections

/-! ### The interior of a convex body is simply connected -/

section SimplyConnected

variable {n : ℕ} {K : Set (S n)}

/-- **The interior of a convex body of `S(n)` is simply connected** (« $W$ simplement connexe »,
l.799): it is homeomorphic to the convex set `F(int K) ∩ {ℓ = 1}` of `ℝⁿ⁺¹`, for a form `ℓ`
positive on `F(K)`. -/
theorem simplyConnectedSpace_corpsInterior (hK : IsCorpsConvexeS n K) :
    SimplyConnectedSpace (corpsInterior K) := by
  obtain ⟨ℓ, hℓ⟩ := hK.exists_forall_pos
  set Y : Set (Fin (n + 1) → ℝ) := Sphere.F (interior K) ∩ {v | ℓ v = 1} with hYdef
  have hYc : Convex ℝ Y := hK.convex_F_interior.inter (convex_hyperplane ℓ.isLinear 1)
  have hmem : ∀ P : corpsInterior K, nrm ℓ (P : S n) ∈ Y := by
    intro P
    obtain ⟨hrep, h1⟩ := nrm_spec hℓ (interior_subset P.2)
    exact ⟨⟨hrep.ne_zero, by rw [hrep.2]; exact P.2⟩, h1⟩
  have hYne : Y.Nonempty := by
    obtain ⟨x, hx⟩ := hK.2.2
    exact ⟨_, hmem ⟨x, hx⟩⟩
  let e : corpsInterior K ≃ₜ Y :=
    { toFun := fun P => ⟨nrm ℓ (P : S n), hmem P⟩
      invFun := fun v => ⟨Sphere.mk v.1 v.2.1.1, v.2.1.2⟩
      left_inv := fun P => by
        apply Subtype.ext
        exact (nrm_spec hℓ (interior_subset P.2)).1.2
      right_inv := fun v => by
        apply Subtype.ext
        obtain ⟨⟨hv0, -⟩, hv1⟩ := v.2
        have hv1' : ℓ v.1 = 1 := hv1
        have hn : ‖v.1‖ ≠ 0 := norm_ne_zero_iff.2 hv0
        change nrm ℓ (Sphere.mk v.1 _) = v.1
        simp only [nrm, Sphere.homeomorphUnitSphere_mk, map_smul, smul_eq_mul, hv1', mul_one,
          inv_inv, smul_smul, mul_inv_cancel₀ hn, one_smul]
      continuous_toFun := (continuous_nrm_corpsInterior hℓ).subtype_mk _
      continuous_invFun := (Sphere.continuous_mk_comp (f := fun v : Y => (v : Fin (n + 1) → ℝ))
        continuous_subtype_val fun v => v.2.1.1).subtype_mk _ }
  haveI : ContractibleSpace Y := hYc.contractibleSpace hYne
  haveI : ContractibleSpace (corpsInterior K) := e.contractibleSpace
  infer_instance

end SimplyConnected

/-! ### The convex hull of `p(V)` (the proof's first paragraph and 1°) -/

section Hull

variable {n : ℕ}

/-- **The convex hull of a part `A` of `S(n)`** (l.728, « le plus petit convexe de $\mathring{H}$
contenant $p(V)$ »): the rays of the convex hull of the cone `F(A)`. -/
def enveloppeConvexe (A : Set (S n)) : Set (S n) :=
  Sphere.ofCone (convexHull ℝ (Sphere.F A))

theorem subset_enveloppeConvexe (A : Set (S n)) : A ⊆ enveloppeConvexe A := by
  intro x hx
  obtain ⟨v, hv, rfl⟩ := Sphere.exists_isRep x
  exact Sphere.mk_mem_ofCone hv (subset_convexHull ℝ _ ⟨hv, hx⟩)

/-- The convex hull of the cone `F(A)` is stable under the positive homotheties. -/
theorem smul_mem_convexHull_F (A : Set (S n)) {c : ℝ} (hc : 0 < c) {v : Fin (n + 1) → ℝ}
    (hv : v ∈ convexHull ℝ (Sphere.F A)) : c • v ∈ convexHull ℝ (Sphere.F A) := by
  have : convexHull ℝ (Sphere.F A) ⊆ (fun w => c • w) ⁻¹' convexHull ℝ (Sphere.F A) :=
    convexHull_min (fun w hw => subset_convexHull ℝ _ (Sphere.smul_mem_F hw hc))
      ((convex_convexHull ℝ _).smul_preimage c)
  exact this hv

theorem isOpen_enveloppeConvexe {A : Set (S n)} (hA : IsOpen A) :
    IsOpen (enveloppeConvexe A) := by
  have hF : IsOpen (Sphere.F A) := Sphere.isOpen_iff_F.1 hA
  exact Sphere.isOpen_ofCone (fun c hc v hv => smul_mem_convexHull_F A hc hv) hF.convexHull

/-- The convex hull of a part of an open hemisphere `H̊` lies in `H̊`: it is « le plus petit convexe
de $\mathring{H}$ contenant » `A` (with `enveloppeConvexe_isLeast`). -/
theorem enveloppeConvexe_subset_hemisphere {A H : Set (S n)} (hH : Sphere.IsOpenHemisphere H)
    (hAH : A ⊆ H) : enveloppeConvexe A ⊆ H := by
  obtain ⟨l, rfl⟩ := Sphere.isOpenHemisphere_iff.1 hH
  have hC : convexHull ℝ (Sphere.F A) ⊆ {v | 0 < l v} := convexHull_min
    (fun v ⟨hv0, hvA⟩ => (Sphere.mk_mem_openHemisphere hv0).1 (hAH hvA))
    (convex_halfSpace_gt l.isLinear 0)
  intro x hx
  obtain ⟨v, hv0, hvC, rfl⟩ := Sphere.mem_ofCone.1 hx
  exact (Sphere.mk_mem_openHemisphere hv0).2 (hC hvC)

/-- **The closure of the convex hull is a convex body** (l.728–729, « un convexe $W$, intérieur
d'un corps convexe »), when `A` is open, nonempty, and its closure lies in an open hemisphere. -/
theorem isCorpsConvexeS_closure_enveloppeConvexe {A : Set (S n)} (hA : IsOpen A)
    (hne : A.Nonempty) {H : Set (S n)} (hH : Sphere.IsOpenHemisphere H) (hcl : closure A ⊆ H) :
    IsCorpsConvexeS n (closure (enveloppeConvexe A)) := by
  obtain ⟨l, rfl⟩ := Sphere.isOpenHemisphere_iff.1 hH
  have hlc : Continuous l := LinearMap.continuous_of_finiteDimensional l
  set C := convexHull ℝ (Sphere.F A) with hCdef
  -- `l > 0` on `C`
  have hpos : ∀ v ∈ C, 0 < l v := by
    have : C ⊆ {v | 0 < l v} := convexHull_min
      (fun v ⟨hv0, hvA⟩ => (Sphere.mk_mem_openHemisphere hv0).1 (hcl (subset_closure hvA)))
      (convex_halfSpace_gt l.isLinear 0)
    exact fun v hv => this hv
  have h0C : (0 : Fin (n + 1) → ℝ) ∉ C := fun h => by
    have := hpos 0 h
    rw [map_zero] at this
    exact lt_irrefl _ this
  -- a constant `c > 0` with `c ‖v‖ ≤ l v` on `F(closure A)`
  obtain ⟨c, hc, hcA⟩ : ∃ c > 0, ∀ v ∈ Sphere.F (closure A), c * ‖v‖ ≤ l v := by
    let g : S n → ℝ := fun X => l (Sphere.homeomorphUnitSphere X : Fin (n + 1) → ℝ)
    have hg : Continuous g :=
      hlc.comp (continuous_subtype_val.comp Sphere.homeomorphUnitSphere.continuous)
    have hgA : ∀ X ∈ closure A, 0 < g X := by
      intro X hX
      obtain ⟨x, hx0, rfl⟩ := Sphere.exists_isRep X
      have := (Sphere.mk_mem_openHemisphere hx0).1 (hcl hX)
      simp only [g, Sphere.homeomorphUnitSphere_mk, map_smul, smul_eq_mul]
      exact mul_pos (inv_pos.2 (norm_pos_iff.2 hx0)) this
    obtain ⟨X₀, hX₀, hmin⟩ := isClosed_closure.isCompact.exists_isMinOn
      (hne.mono subset_closure) hg.continuousOn
    refine ⟨g X₀, hgA X₀ hX₀, fun v hv => ?_⟩
    obtain ⟨hv0, hvA⟩ := hv
    have h1 : g X₀ ≤ g (Sphere.mk v hv0) := hmin hvA
    simp only [g, Sphere.homeomorphUnitSphere_mk, map_smul, smul_eq_mul] at h1
    have hn : 0 < ‖v‖ := norm_pos_iff.2 hv0
    rwa [le_inv_mul_iff₀ hn, mul_comm] at h1
  -- the closed convex cone `Q = {c ‖v‖ ≤ l v}` contains `closure C`
  set Q : Set (Fin (n + 1) → ℝ) := {v | c * ‖v‖ ≤ l v} with hQdef
  have hQc : Convex ℝ Q := by
    intro x hx y hy a b ha hb hab
    simp only [hQdef, mem_setOf_eq, map_add, map_smul, smul_eq_mul] at hx hy ⊢
    have hn : ‖a • x + b • y‖ ≤ a * ‖x‖ + b * ‖y‖ := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
    calc c * ‖a • x + b • y‖ ≤ c * (a * ‖x‖ + b * ‖y‖) := by gcongr
      _ = a * (c * ‖x‖) + b * (c * ‖y‖) := by ring
      _ ≤ a * l x + b * l y := by gcongr
  have hQcl : IsClosed Q := isClosed_le (continuous_const.mul continuous_norm) hlc
  have hCQ : closure C ⊆ Q := closure_minimal (convexHull_min
    (fun v hv => hcA v (Sphere.F_mono subset_closure hv)) hQc) hQcl
  -- `F(K) = closure C - {0}`
  have hFW : Sphere.F (enveloppeConvexe A) = C := by
    rw [enveloppeConvexe, Sphere.F_ofCone (fun c hc v hv => smul_mem_convexHull_F A hc hv),
      sdiff_singleton_eq_self h0C]
  have hFK : Sphere.F (closure (enveloppeConvexe A)) = closure C \ {0} := by
    rw [Sphere.F_closure, hFW]
  rw [isCorpsConvexeS_iff]
  refine ⟨?_, isClosed_closure.isCompact, ?_⟩
  · rw [hFK]
    intro x hx y hy a b ha hb hab
    refine ⟨(convex_convexHull ℝ _).closure hx.1 hy.1 ha hb hab, ?_⟩
    have hx' : 0 < l x := lt_of_lt_of_le (mul_pos hc (norm_pos_iff.2 hx.2)) (hCQ hx.1)
    have hy' : 0 < l y := lt_of_lt_of_le (mul_pos hc (norm_pos_iff.2 hy.2)) (hCQ hy.1)
    intro h0
    have h0' : l (a • x + b • y) = 0 := by rw [mem_singleton_iff.1 h0, map_zero]
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at h0'
    rcases ha.lt_or_eq with ha' | ha'
    · have := mul_pos ha' hx'
      have := mul_nonneg hb hy'.le
      linarith
    · subst ha'
      rw [zero_add] at hab
      subst hab
      linarith
  · obtain ⟨x, hx⟩ := hne
    exact ⟨x, interior_maximal (subset_closure.trans' (subset_enveloppeConvexe A)) hA hx⟩

/-- **The convex hull is « le plus petit convexe … contenant $p(V)$ »** (l.728): it is a convex part
of `S(n)` (Déf. 8), it contains `A`, and it lies in every convex part containing `A`. -/
theorem enveloppeConvexe_isLeast (A : Set (S n)) :
    Sphere.IsConvexPart (enveloppeConvexe A) ∧ A ⊆ enveloppeConvexe A ∧
      ∀ k : Set (S n), Sphere.IsConvexPart k → A ⊆ k → enveloppeConvexe A ⊆ k := by
  have hFW : Sphere.F (enveloppeConvexe A) = convexHull ℝ (Sphere.F A) \ {0} := by
    rw [enveloppeConvexe, Sphere.F_ofCone (fun c hc v hv => smul_mem_convexHull_F A hc hv)]
  refine ⟨?_, subset_enveloppeConvexe A, fun k hk hAk => ?_⟩
  · have e : insert (0 : Fin (n + 1) → ℝ) (Sphere.F (enveloppeConvexe A)) =
        insert 0 (convexHull ℝ (Sphere.F A)) := by
      rw [hFW]
      ext v
      by_cases hv : v = 0 <;> simp [hv]
    rw [Sphere.IsConvexPart, e]
    have hC := convex_convexHull ℝ (Sphere.F A)
    have hsm : ∀ {c : ℝ}, 0 ≤ c → ∀ {v}, v ∈ insert 0 (convexHull ℝ (Sphere.F A)) →
        c • v ∈ insert (0 : Fin (n + 1) → ℝ) (convexHull ℝ (Sphere.F A)) := by
      intro c hc v hv
      rcases hc.lt_or_eq with hc | rfl
      · rcases hv with rfl | hv
        · simp
        · exact mem_insert_of_mem _ (smul_mem_convexHull_F A hc hv)
      · simp
    intro x hx y hy a b ha hb hab
    rcases hx with rfl | hx
    · rw [smul_zero, zero_add]
      exact hsm hb hy
    rcases hy with rfl | hy
    · rw [smul_zero, add_zero]
      exact hsm ha (mem_insert_of_mem _ hx)
    exact mem_insert_of_mem _ (hC hx hy ha hb hab)
  · intro x hx
    obtain ⟨v, hv0, hvC, rfl⟩ := Sphere.mem_ofCone.1 hx
    have hsub : convexHull ℝ (Sphere.F A) ⊆ insert 0 (Sphere.F k) :=
      convexHull_min (fun w hw => mem_insert_of_mem _ (Sphere.F_mono hAk hw)) hk
    rcases hsub hvC with h | h
    · exact absurd h hv0
    · exact h.2

/-- **1°, « que $\gamma$ soit un automorphisme de $W$ résulte immédiatement de ce que $\gamma$ est
un automorphisme de $p(V)$ dont $W$ est l'enveloppe convexe »**: a projective transformation
mapping `A` into itself maps its convex hull into itself. -/
theorem smul_enveloppeConvexe_subset {A : Set (S n)} {γ : GSR n} (h : γ • A ⊆ A) :
    γ • enveloppeConvexe A ⊆ enveloppeConvexe A := by
  induction γ using QuotientGroup.induction_on with
  | H g =>
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨v, hv0, hvC, rfl⟩ := Sphere.mem_ofCone.1 hx
  show (QuotientGroup.mk g : GSR n) • Sphere.mk v hv0 ∈ _
  rw [GSE.mk_smul, Sphere.smul_mk]
  refine Sphere.mk_mem_ofCone _ ?_
  have hsub : (g : (Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin (n + 1) → ℝ)) '' convexHull ℝ (Sphere.F A) ⊆
      convexHull ℝ (Sphere.F A) := by
    rw [LinearMap.image_convexHull]
    refine convexHull_min ?_ (convex_convexHull ℝ _)
    rintro _ ⟨w, ⟨hw0, hwA⟩, rfl⟩
    refine subset_convexHull ℝ _ ⟨g.map_ne_zero_iff.2 hw0, ?_⟩
    have := h (smul_mem_smul_set (a := (QuotientGroup.mk g : GSR n)) hwA)
    rwa [GSE.mk_smul, Sphere.smul_mk] at this
  exact hsub ⟨v, hvC, rfl⟩

end Hull

/-! ### A projective transformation preserving a convex body preserves its pseudo-balls -/

section Aut

variable {n : ℕ} {K : Set (S n)} {γ : GSR n}

theorem smul_mem_interior_of_smul_eq (hγ : γ • interior K = interior K) {x : S n}
    (hx : x ∈ interior K) : γ • x ∈ interior K :=
  hγ ▸ smul_mem_smul_set hx

theorem inv_smul_interior_of_smul_eq (hγ : γ • interior K = interior K) :
    γ⁻¹ • interior K = interior K := by
  rw [inv_smul_eq_iff, hγ]

/-- `γ` restricted to `W = int K`, as a homeomorphism of `W`. -/
def homeomorphInterior (hγ : γ • interior K = interior K) : corpsInterior K ≃ₜ corpsInterior K where
  toFun m := ⟨γ • (m : S n), smul_mem_interior_of_smul_eq hγ m.2⟩
  invFun m := ⟨γ⁻¹ • (m : S n), smul_mem_interior_of_smul_eq (inv_smul_interior_of_smul_eq hγ) m.2⟩
  left_inv m := Subtype.ext (inv_smul_smul γ (m : S n))
  right_inv m := Subtype.ext (smul_inv_smul γ (m : S n))
  continuous_toFun := ((continuous_const_smul γ).comp continuous_subtype_val).subtype_mk _
  continuous_invFun := ((continuous_const_smul γ⁻¹).comp continuous_subtype_val).subtype_mk _

theorem isGXMorphism_homeomorphInterior (hγ : γ • interior K = interior K) :
    IsGXMorphism (GSR n) (S n) (homeomorphInterior hγ) := by
  refine ⟨(homeomorphInterior hγ).continuous, fun x => ⟨γ, Eventually.of_forall fun y => ?_⟩⟩
  simp [TopologicalSpace.Opens.chartAt_eq, homeomorphInterior]

/-- **`γ` as a projective automorphism of the interior `W` of `K`** (1°, « $\gamma$ est un
automorphisme projectif de $W$ »). -/
def autInterior (hγ : γ • interior K = interior K) : GXAut (GSR n) (S n) (corpsInterior K) :=
  GXAut.ofBijective (isGXMorphism_homeomorphInterior hγ) (homeomorphInterior hγ).bijective

theorem coe_autInterior_smul (hγ : γ • interior K = interior K) (m : corpsInterior K) :
    ((autInterior hγ • m : corpsInterior K) : S n) = γ • (m : S n) :=
  rfl

/-- `γ` maps the pseudo-ball of `W` of centre `m` and radius `r` onto that of centre `γ m`. -/
theorem image_pseudoBoule_autInterior (hγ : γ • interior K = interior K) (m : corpsInterior K)
    (r : ℝ) :
    Subtype.val '' pseudoBoule n (autInterior hγ • m) r =
      γ • (Subtype.val '' pseudoBoule n m r : Set (S n)) := by
  set a := autInterior hγ
  ext y
  constructor
  · rintro ⟨N, ⟨Sg, hN⟩, rfl⟩
    have h1 := hN.smul a⁻¹
    rw [inv_smul_smul] at h1
    refine ⟨((a⁻¹ • N : corpsInterior K) : S n), ⟨_, ⟨_, h1⟩, rfl⟩, ?_⟩
    change ((a • (a⁻¹ • N) : corpsInterior K) : S n) = N
    rw [smul_inv_smul]
  · intro hy
    obtain ⟨_, ⟨N, ⟨Sg, hN⟩, rfl⟩, rfl⟩ := Set.mem_smul_set.1 hy
    exact ⟨a • N, ⟨_, hN.smul a⟩, coe_autInterior_smul hγ N⟩

end Aut

/-! ### Uniformly small pseudo-balls near a point of a convex body -/

section Uniform

variable {n : ℕ} {K : Set (S n)}

/-- Near `m`, the pseudo-balls of one radius `s > 0` all lie in a given neighbourhood of `m` (the
argument of `hasBasis_pseudoBoule`, made uniform by the continuity of `l_W` on `W × W`). -/
theorem exists_pos_eventually_pseudoBoule_subset [NeZero n] (hK : IsCorpsConvexeS n K)
    (m : corpsInterior K) {U : Set (corpsInterior K)} (hU : U ∈ 𝓝 m) :
    ∃ s : ℝ, 0 < s ∧ ∀ᶠ a in 𝓝 m, pseudoBoule n a s ⊆ U := by
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.2 (NeZero.ne n)
  haveI : LocallyCompactSpace (corpsInterior K) := (corpsInterior K).isOpen.locallyCompactSpace
  obtain ⟨C, hC, hCU, hCc⟩ := local_compact_nhds hU
  obtain ⟨D, hD, hDC, hDc⟩ := local_compact_nhds (interior_mem_nhds.2 hC)
  have hCcl : IsClosed C := hCc.isClosed
  have hfr : IsCompact (frontier C) :=
    hCc.of_isClosed_subset isClosed_frontier (frontier_subset_closure.trans hCcl.closure_eq.le)
  have hf : Continuous fun q : corpsInterior K × corpsInterior K => hilbertLength K q.1 q.2 :=
    continuous_hilbertLength hK
  -- a positive lower bound of `l_W` on `D × frontier C`
  obtain ⟨s, hs, hsfr⟩ : ∃ s : ℝ, 0 < s ∧ ∀ a ∈ D, ∀ P ∈ frontier C,
      (s : EReal) ≤ hilbertLength K a P := by
    rcases (D ×ˢ frontier C).eq_empty_or_nonempty with h | h
    · refine ⟨1, one_pos, fun a ha P hP => ?_⟩
      have : (a, P) ∈ D ×ˢ frontier C := mk_mem_prod ha hP
      rw [h] at this
      exact absurd this (notMem_empty _)
    obtain ⟨q₀, hq₀, hmin⟩ := (hDc.prod hfr).exists_isMinOn h hf.continuousOn
    have hne : q₀.1 ≠ q₀.2 := fun e => hq₀.2.2 (e ▸ hDC hq₀.1)
    have hpos : 0 < hilbertLength K q₀.1 q₀.2 :=
      lt_of_le_of_ne (pseudoLength_nonneg _ _ _) (Ne.symm (hilbertLength_ne_zero hK hne))
    obtain ⟨s, hs0, hs⟩ := EReal.lt_iff_exists_real_btwn.1 hpos
    exact ⟨s, EReal.coe_pos.1 hs0, fun a ha P hP =>
      hs.le.trans (isMinOn_iff.1 hmin (a, P) ⟨ha, hP⟩)⟩
  refine ⟨s, hs, ?_⟩
  filter_upwards [hD] with a ha
  have hai : a ∈ interior C := hDC ha
  have hsub : pseudoBoule n a s ⊆ interior C := by
    refine (isPreconnected_pseudoBoule a s).subset_left_of_subset_union isOpen_interior
      hCcl.isOpen_compl (disjoint_compl_right.mono_left interior_subset) ?_
      ⟨a, self_mem_pseudoBoule hn a hs, hai⟩
    intro P hP
    by_cases hPC : P ∈ C
    · left
      by_contra hPi
      have hPfr : P ∈ frontier C := ⟨subset_closure hPC, hPi⟩
      exact absurd ((mem_pseudoBoule_corpsInterior_iff hK).1 hP) (not_lt.2 (hsfr a ha P hPfr))
    · exact Or.inr hPC
  exact hsub.trans (interior_subset.trans hCU)

end Uniform

/-! ### Sheets over pseudo-balls (2°, 3°) -/

section Feuilles

variable {n : ℕ} {V : Type u} [TopologicalSpace V] [ChartedSpace (S n) V]
  [HasGroupoid V (projGroupoid n)] {K : Set (S n)} {p : V → S n}

/-- `O` is a sheet of `p` over the pseudo-ball of `W = int K` of centre `m` and radius `r`: an open
set on which `p` is injective, with image that pseudo-ball (2°, « la restriction de $p$ à $O_M$
soit une carte sur une pseudo-boule »). -/
def IsFeuille (p : V → S n) (K : Set (S n)) (m : corpsInterior K) (r : ℝ) (O : Set V) : Prop :=
  IsOpen O ∧ InjOn p O ∧ p '' O = Subtype.val '' pseudoBoule n m r

/-- `M` is the centre of a sheet of radius `r` (2°, « $O_M$ … pseudo-boule de centre $M$ et de
rayon $r$ »). -/
def HasFeuille (p : V → S n) (K : Set (S n)) (M : V) (r : ℝ) : Prop :=
  ∃ hM : p M ∈ interior K, ∃ O : Set V, M ∈ O ∧ IsFeuille p K ⟨p M, hM⟩ r O

omit [ChartedSpace (S n) V] [HasGroupoid V (projGroupoid n)] in
/-- The image in `S(n)` of a pseudo-ball of `W` is open. -/
theorem isOpen_image_pseudoBoule (m : corpsInterior K) (r : ℝ) :
    IsOpen (Subtype.val '' pseudoBoule n m r : Set (S n)) :=
  (corpsInterior K).isOpen.isOpenMap_subtype_val _ (isOpen_pseudoBoule m r)

omit [ChartedSpace (S n) V] [HasGroupoid V (projGroupoid n)] in
/-- The image in `S(n)` of a pseudo-ball of `W` is connected. -/
theorem isPreconnected_image_pseudoBoule (m : corpsInterior K) (r : ℝ) :
    IsPreconnected (Subtype.val '' pseudoBoule n m r : Set (S n)) :=
  (isPreconnected_pseudoBoule m r).image _ continuous_subtype_val.continuousOn

omit [ChartedSpace (S n) V] [HasGroupoid V (projGroupoid n)] in
/-- **Shrinking a sheet**: the part of a sheet over a smaller pseudo-ball is a sheet over it. -/
theorem IsFeuille.shrink {m m' : corpsInterior K} {r s : ℝ} {O : Set V}
    (h : IsFeuille p K m r O) (hp : Continuous p) (hsub : pseudoBoule n m' s ⊆ pseudoBoule n m r) :
    IsFeuille p K m' s (O ∩ p ⁻¹' (Subtype.val '' pseudoBoule n m' s)) := by
  obtain ⟨hO, hi, himg⟩ := h
  refine ⟨hO.inter ((isOpen_image_pseudoBoule m' s).preimage hp), hi.mono inter_subset_left, ?_⟩
  apply Subset.antisymm
  · rintro _ ⟨x, ⟨-, hx⟩, rfl⟩
    exact hx
  · intro y hy
    have : y ∈ p '' O := himg ▸ image_mono hsub hy
    obtain ⟨x, hx, rfl⟩ := this
    exact ⟨x, ⟨hx, hy⟩, rfl⟩

omit [ChartedSpace (S n) V] [HasGroupoid V (projGroupoid n)] in
/-- A sheet of radius `r` contains a sheet of every radius `0 < s ≤ r` (`n ≥ 1`). -/
theorem HasFeuille.mono [NeZero n] {M : V} {r s : ℝ} (h : HasFeuille p K M r) (hp : Continuous p)
    (hs : 0 < s) (hsr : s ≤ r) : HasFeuille p K M s := by
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.2 (NeZero.ne n)
  obtain ⟨hM, O, hMO, hO⟩ := h
  exact ⟨hM, O ∩ p ⁻¹' (Subtype.val '' pseudoBoule n (⟨p M, hM⟩ : corpsInterior K) s),
    ⟨hMO, _, self_mem_pseudoBoule hn _ hs, rfl⟩, hO.shrink hp (pseudoBoule_mono _ hsr)⟩

/-- **2°**: every point is the centre of a sheet of some radius `r > 0`. -/
theorem exists_hasFeuille [NeZero n] (hK : IsCorpsConvexeS n K) (hp : IsDeveloping (GSR n) p)
    {M : V} (hM : p M ∈ interior K) : ∃ r : ℝ, 0 < r ∧ HasFeuille p K M r := by
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.2 (NeZero.ne n)
  obtain ⟨e, hMe, hpe⟩ := hp.isLocalHomeomorph M
  set m : corpsInterior K := ⟨p M, hM⟩ with hmdef
  have hpMe : p M ∈ e.target := by rw [hpe]; exact e.map_source hMe
  have hT : (Subtype.val ⁻¹' e.target : Set (corpsInterior K)) ∈ 𝓝 m :=
    (e.open_target.preimage continuous_subtype_val).mem_nhds hpMe
  obtain ⟨r, hr, hrT⟩ := (hasBasis_pseudoBoule hK m).mem_iff.1 hT
  refine ⟨r, hr, hM, e.source ∩ p ⁻¹' (Subtype.val '' pseudoBoule n m r),
    ⟨hMe, m, self_mem_pseudoBoule hn m hr, rfl⟩, ?_, ?_, ?_⟩
  · rw [hpe]
    exact e.isOpen_inter_preimage (isOpen_image_pseudoBoule m r)
  · rw [hpe]
    exact e.injOn.mono inter_subset_left
  · apply Subset.antisymm
    · rintro _ ⟨x, ⟨-, hx⟩, rfl⟩
      exact hx
    · rintro _ ⟨N, hN, rfl⟩
      have hy' : (N : S n) ∈ e.target := hrT hN
      refine ⟨e.symm N, ⟨e.map_target hy', ?_⟩, ?_⟩
      · show p (e.symm N) ∈ Subtype.val '' pseudoBoule n m r
        rw [hpe, e.right_inv hy']
        exact ⟨N, hN, rfl⟩
      · rw [hpe, e.right_inv hy']

/-- **3°, first paragraph** (l.759–762): on a compact `E`, one radius `r(E) > 0` serves every
point. -/
theorem exists_hasFeuille_of_isCompact [NeZero n] (hK : IsCorpsConvexeS n K)
    (hp : IsDeveloping (GSR n) p) (hpK : ∀ M, p M ∈ interior K) {E : Set V} (hE : IsCompact E) :
    ∃ r : ℝ, 0 < r ∧ ∀ M ∈ E, HasFeuille p K M r := by
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.2 (NeZero.ne n)
  have hq : Continuous (fun M => (⟨p M, hpK M⟩ : corpsInterior K)) :=
    hp.continuous.subtype_mk _
  -- near each point, one radius serves (2° and the continuity of `l_W`)
  have key : ∀ M : V, ∃ s : ℝ, 0 < s ∧ ∀ᶠ M' in 𝓝 M, HasFeuille p K M' s := by
    intro M
    obtain ⟨r, hr, hM, O, hMO, hO⟩ := exists_hasFeuille hK hp (hpK M)
    obtain ⟨s, hs, hev⟩ := exists_pos_eventually_pseudoBoule_subset hK
      (⟨p M, hM⟩ : corpsInterior K)
      ((isOpen_pseudoBoule _ r).mem_nhds (self_mem_pseudoBoule hn _ hr))
    refine ⟨s, hs, ?_⟩
    filter_upwards [hO.1.mem_nhds hMO, hq.continuousAt.eventually hev] with M' hM'O hM'ev
    exact ⟨hpK M', O ∩ p ⁻¹' (Subtype.val '' pseudoBoule n (⟨p M', hpK M'⟩ : corpsInterior K) s),
      ⟨hM'O, _, self_mem_pseudoBoule hn _ hs, rfl⟩, hO.shrink hp.continuous hM'ev⟩
  choose s hs hG using key
  obtain ⟨t, -, htcov⟩ := hE.elim_nhds_subcover (fun M => {M' | HasFeuille p K M' (s M)})
    (fun M _ => hG M)
  have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ M ∈ t, r < s M :=
    (Filter.eventually_all_finset t).2 fun M _ =>
      nhdsWithin_le_nhds (eventually_lt_nhds (hs M))
  obtain ⟨r, hr, hrpos⟩ := (hev.and self_mem_nhdsWithin).exists
  refine ⟨r, hrpos, fun M hM => ?_⟩
  obtain ⟨M₀, hM₀t, hMM₀⟩ := mem_iUnion₂.1 (htcov hM)
  exact HasFeuille.mono hMM₀ hp.continuous hrpos (hr M₀ hM₀t).le

omit [HasGroupoid V (projGroupoid n)] in
/-- **3°, second paragraph** (l.764–769): an automorphism `g` of `V` with `p ∘ g = γ ∘ p`, `γ`
preserving `W`, carries a sheet of centre `M` to a sheet of centre `gM`, of the same radius. -/
theorem HasFeuille.smul {M : V} {r : ℝ} (h : HasFeuille p K M r) (g : GXAut (GSR n) (S n) V)
    {γ : GSR n} (hgγ : ∀ y, p (g • y) = γ • p y) (hγ : γ • interior K = interior K) :
    HasFeuille p K (g • M) r := by
  obtain ⟨hM, O, hMO, hO, hi, himg⟩ := h
  have hgM : p (g • M) ∈ interior K := by
    rw [hgγ]
    exact smul_mem_interior_of_smul_eq hγ hM
  refine ⟨hgM, (g • ·) '' O, ⟨M, hMO, rfl⟩, g.toHomeomorph.isOpenMap _ hO, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy
    simp only [hgγ] at hxy
    rw [hi hx hy (MulAction.injective γ hxy)]
  · have e1 : p '' ((g • ·) '' O) = γ • (p '' O) := by
      rw [image_image, ← Set.image_smul, image_image]
      simp_rw [hgγ]
    have e2 : (autInterior hγ • (⟨p M, hM⟩ : corpsInterior K)) = ⟨p (g • M), hgM⟩ :=
      Subtype.ext (by
        rw [coe_autInterior_smul]
        exact (hgγ M).symm)
    rw [e1, himg, ← image_pseudoBoule_autInterior hγ, e2]

/-- **3°**: one radius `r > 0` serves every point of a sweepable `V`. -/
theorem exists_hasFeuille_uniform [NeZero n] (hK : IsCorpsConvexeS n K)
    (hp : IsDeveloping (GSR n) p) (hpK : ∀ M, p M ∈ interior K)
    (hbal : IsBalayable (GSR n) (S n) V)
    (hinv : ∀ g : GXAut (GSR n) (S n) V, ∃ γ : GSR n, (∀ y, p (g • y) = γ • p y) ∧
      γ • interior K = interior K) :
    ∃ r : ℝ, 0 < r ∧ ∀ M, HasFeuille p K M r := by
  obtain ⟨E, hEc, hEU⟩ := hbal
  obtain ⟨r, hr, hrE⟩ := exists_hasFeuille_of_isCompact hK hp hpK hEc
  refine ⟨r, hr, fun M => ?_⟩
  have hM : M ∈ ⋃ g ∈ (⊤ : Subgroup (GXAut (GSR n) (S n) V)), g • E := hEU ▸ mem_univ M
  obtain ⟨g, -, hMg⟩ := mem_iUnion₂.1 hM
  obtain ⟨M₀, hM₀, rfl⟩ := Set.mem_smul_set.1 hMg
  obtain ⟨γ, hgγ, hγ⟩ := hinv g
  exact (hrE M₀ hM₀).smul g hgγ hγ

end Feuilles

/-! ### 4° and 5°: `p(V) = W`, and `V` is a covering of `W`; the final step -/

section Covering

variable {n : ℕ} {V : Type u} [TopologicalSpace V] [ChartedSpace (S n) V]
  [HasGroupoid V (projGroupoid n)] {K : Set (S n)} {p : V → S n}

/-- **4°, `p(V) = W`** (l.775–779, through Prop. 5, `ouvert_plein`, with the radius `r > 0` of
3°). -/
theorem range_eq_interior [NeZero n] [Nonempty V] (hK : IsCorpsConvexeS n K)
    (hp : IsDeveloping (GSR n) p) (hpK : ∀ M, p M ∈ interior K) {r : ℝ} (hr : 0 < r)
    (hr' : ∀ M, HasFeuille p K M r) : range p = interior K := by
  set q : V → corpsInterior K := fun M => ⟨p M, hpK M⟩ with hqdef
  have hrq : range q = Subtype.val ⁻¹' range p := by
    ext m
    constructor
    · rintro ⟨M, rfl⟩
      exact ⟨M, rfl⟩
    · rintro ⟨M, hM⟩
      exact ⟨M, Subtype.ext hM⟩
  have hU : IsOpen (range q) := by
    rw [hrq]
    exact hp.isLocalHomeomorph.isOpenMap.isOpen_range.preimage continuous_subtype_val
  haveI := simplyConnectedSpace_corpsInterior hK
  have hfull : range q = univ := by
    refine ouvert_plein (n := n) hU (range_nonempty q) hr fun m hm => ?_
    obtain ⟨M, rfl⟩ := hm
    obtain ⟨hM, O, -, -, -, himg⟩ := hr' M
    intro N hN
    have : (N : S n) ∈ p '' O := himg ▸ ⟨N, hN, rfl⟩
    obtain ⟨x, -, hx⟩ := this
    exact ⟨x, Subtype.ext hx⟩
  apply Subset.antisymm (range_subset_iff.2 hpK)
  intro y hy
  have : (⟨y, hy⟩ : corpsInterior K) ∈ range q := hfull ▸ mem_univ _
  obtain ⟨M, hM⟩ := this
  exact ⟨M, congrArg Subtype.val hM⟩

/-- **5°, `V` is a covering of `W`** (l.781–796). -/
theorem isCoveringMapOn_interior [NeZero n] [T2Space V] (hp : IsDeveloping (GSR n) p)
    (hpK : range p = interior K) {r : ℝ} (hr : 0 < r)
    (hr' : ∀ M, HasFeuille p K M r) : IsCoveringMapOn p (interior K) := by
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.2 (NeZero.ne n)
  have hpo : IsOpenMap p := hp.isLocalHomeomorph.isOpenMap
  intro x hx
  set m : corpsInterior K := ⟨x, hx⟩ with hmdef
  haveI : DiscreteTopology (p ⁻¹' {x}) :=
    (IsDiscrete.of_openPartialHomeomorph p subset_rfl fun e _ => by
      obtain ⟨φ, h1, h2⟩ := hp.isLocalHomeomorph e
      exact ⟨φ, h1, h2.symm⟩).1
  have hne : (p ⁻¹' {x}).Nonempty := by
    rw [← hpK] at hx
    obtain ⟨M, hM⟩ := hx
    exact ⟨M, hM⟩
  haveI : Nonempty (p ⁻¹' {x}) := hne.to_subtype
  haveI : Nonempty (S n → V) := ⟨fun _ => hne.some⟩
  unfold HasFeuille at hr'
  choose hc O hMO hO using hr'
  have himg : ∀ i : p ⁻¹' {x}, p '' O i = Subtype.val '' pseudoBoule n m r := by
    intro i
    have e : (⟨p i, hc i⟩ : corpsInterior K) = m := Subtype.ext i.2
    rw [(hO i).2.2, e]
  have hxB : x ∈ Subtype.val '' pseudoBoule n m r := ⟨m, self_mem_pseudoBoule hn m hr, rfl⟩
  refine IsEvenlyCovered.of_trivialization
    (t := (isOpen_image_pseudoBoule m r).trivializationDiscrete
      (f := p) (fun i : p ⁻¹' {x} => O i) _ ?_ ?_ ?_ ?_ ?_) hxB
  · -- open sets of the base set are read in each sheet
    intro i W hW
    constructor
    · intro hWo
      exact (hWo.preimage hp.continuous).inter (hO i).1
    · intro h
      have e : W = p '' (p ⁻¹' W ∩ O i) := by
        apply Subset.antisymm
        · intro y hy
          have : y ∈ p '' O i := (himg i).symm ▸ hW hy
          obtain ⟨z, hz, rfl⟩ := this
          exact ⟨z, ⟨hy, hz⟩, rfl⟩
        · rintro _ ⟨z, ⟨hz, -⟩, rfl⟩
          exact hz
      rw [e]
      exact hpo _ h
  · exact fun i => (hO i).2.1
  · intro i
    rw [SurjOn, himg i]
  · -- the sheets over the pseudo-ball of centre `m` are pairwise disjoint
    intro i j hij
    rw [Function.onFun, Set.disjoint_left]
    intro z hzi hzj
    apply hij
    have hpj : p j = x := j.2
    have hpi : p i = x := i.2
    have hjOi : (j : V) ∈ O i :=
      mem_of_injOn_of_isPreconnected hpo (hO j).1 (hO i).1 (hO j).2.1 (hO i).2.1
        (isPreconnected_image_pseudoBoule m r) (himg j).ge (himg i).ge hzj hzi
        (by rw [← himg j]; exact ⟨z, hzj, rfl⟩) (hMO j) (by rw [hpj]; exact hxB)
    exact Subtype.ext ((hO i).2.1 (hMO i) hjOi (by rw [hpi, hpj]))
  · -- every point over the pseudo-ball lies in one of the sheets
    intro N hN
    obtain ⟨N', hN', hN'eq⟩ := hN
    have hqN : N' = ⟨p N, hc N⟩ := Subtype.ext hN'eq
    obtain ⟨Sg, hmaj⟩ := hN'
    have hmN : m ∈ pseudoBoule n N' r := mem_pseudoBoule_comm.1 ⟨Sg, hmaj⟩
    have hx' : x ∈ p '' O N := by
      rw [(hO N).2.2, ← hqN]
      exact ⟨m, hmN, rfl⟩
    obtain ⟨i, hiO, hix⟩ := hx'
    refine mem_iUnion.2 ⟨⟨i, hix⟩, ?_⟩
    have hB : IsPreconnected (Subtype.val '' Sg : Set (S n)) :=
      hmaj.1.isPreconnected.image _ continuous_subtype_val.continuousOn
    have hSg1 : Sg ⊆ pseudoBoule n m r := hmaj.subset_pseudoBoule
    have hSg2 : Sg ⊆ pseudoBoule n N' r := hmaj.symm.subset_pseudoBoule
    refine mem_of_injOn_of_isPreconnected hpo (hO N).1 (hO i).1 (hO N).2.1 (hO i).2.1 hB
      ?_ ?_ hiO (hMO i) ?_ (hMO N) ?_
    · rw [(hO N).2.2, ← hqN]
      exact image_mono hSg2
    · rw [himg ⟨i, hix⟩]
      exact image_mono hSg1
    · rw [hix]
      exact ⟨m, hmaj.1.left_mem, rfl⟩
    · rw [← hN'eq]
      exact ⟨N', hmaj.1.right_mem, rfl⟩

/-- **The final step** (l.798–799, « la proposition résulte trivialement de ce que $V$ est connexe,
et $W$ simplement connexe »): a covering of the simply connected `W` by the connected Hausdorff
`V` is injective. -/
theorem injective_of_isCoveringMapOn [T2Space V] [ConnectedSpace V] (hK : IsCorpsConvexeS n K)
    (hp : IsDeveloping (GSR n) p) (hpK : range p = interior K)
    (hcov : IsCoveringMapOn p (interior K)) : Function.Injective p := by
  haveI := simplyConnectedSpace_corpsInterior hK
  haveI : LocPathConnectedSpace (corpsInterior K) := by
    haveI := locPathConnectedSpace_S n
    exact (corpsInterior K).isOpen.locPathConnectedSpace
  have hpK' : ∀ M, p M ∈ interior K := fun M => hpK ▸ mem_range_self M
  obtain ⟨M₀⟩ := (inferInstance : Nonempty V)
  set q : V → corpsInterior K := fun M => ⟨p M, hpK' M⟩ with hqdef
  have hq : Continuous q := hp.continuous.subtype_mk _
  obtain ⟨F, ⟨hF₀, hF⟩, -⟩ := hcov.existsUnique_continuousMap_lifts (A := corpsInterior K)
    ⟨Subtype.val, continuous_subtype_val⟩ (a₀ := q M₀) (e₀ := M₀) rfl (fun a => a.2)
  have hpF : ∀ a : corpsInterior K, p (F a) = a := fun a => congrFun hF a
  -- the points `M` with `F(p(M)) = M` form a clopen set
  set T : Set V := {M | F (q M) = M} with hTdef
  have hTc : IsClosed T := isClosed_eq (F.continuous.comp hq) continuous_id
  have hTo : IsOpen T := by
    rw [isOpen_iff_mem_nhds]
    intro M hM
    obtain ⟨e, hMe, hpe⟩ := hp.isLocalHomeomorph M
    have hFM : F (q M) = M := hM
    have h1 : ∀ᶠ M' in 𝓝 M, F (q M') ∈ e.source :=
      (F.continuous.comp hq).continuousAt.preimage_mem_nhds
        (by rw [Function.comp_apply, hFM]; exact e.open_source.mem_nhds hMe)
    filter_upwards [h1, e.open_source.mem_nhds hMe] with M' h1 h2
    refine e.injOn h1 h2 ?_
    rw [← hpe, hpF]
  have hT : T = univ := IsClopen.eq_univ ⟨hTc, hTo⟩ ⟨M₀, hF₀⟩
  intro x y hxy
  have hx : F (q x) = x := (hT ▸ mem_univ x : x ∈ T)
  have hy : F (q y) = y := (hT ▸ mem_univ y : y ∈ T)
  have : q x = q y := Subtype.ext hxy
  rw [← hx, ← hy, this]

end Covering

/-! ### Prop. 2 -/

section Prop2

variable {n : ℕ} {V : Type u} [TopologicalSpace V] [ChartedSpace (S n) V]
  [HasGroupoid V (projGroupoid n)]

/-- An injective developing map is a compatible chart of `V` onto its image. -/
theorem exists_chart_of_injective [Nonempty V] {p : V → S n} (hp : IsDeveloping (GSR n) p)
    (hinj : Function.Injective p) :
    ∃ φ : OpenPartialHomeomorph V (S n), IsCompatibleChart (GSR n) φ ∧ φ.source = univ ∧
      φ.target = range p ∧ ⇑φ = p := by
  have he := hp.isLocalHomeomorph.isOpenEmbedding_of_injective hinj
  refine ⟨he.toOpenPartialHomeomorph p, fun x _ => ?_, he.toOpenPartialHomeomorph_source _,
    he.toOpenPartialHomeomorph_target _, he.toOpenPartialHomeomorph_apply _⟩
  rw [he.toOpenPartialHomeomorph_apply]
  exact hp x

/-- **Chapter 2 § 3, Prop. 2** (`bzprop:c2s3p2_hemisphere_corps_convexe`), every dimension: let
`V` be a connected (Hausdorff) sweepable locally projective manifold with a projection
`p : V → S(n)` compatible with the projective structure (a developing map), and `H̊` an open
hemisphere with `closure p(V) ⊆ H̊`. Then `p` is a chart of `V` onto the interior of a convex body
`K` of `S(n)`: a compatible chart with source `V`, target `int K`, equal to `p`. Moreover `int K`
is the proof's `W`, the convex hull of `p(V)`. -/
theorem hemisphere_corps_convexe [T2Space V] [ConnectedSpace V] {p : V → S n}
    (hp : IsDeveloping (GSR n) p) (hbal : IsBalayable (GSR n) (S n) V) {H : Set (S n)}
    (hH : Sphere.IsOpenHemisphere H) (hcl : closure (range p) ⊆ H) :
    ∃ K : Set (S n), IsCorpsConvexeS n K ∧ interior K = enveloppeConvexe (range p) ∧
      ∃ φ : OpenPartialHomeomorph V (S n), IsCompatibleChart (GSR n) φ ∧ φ.source = univ ∧
        φ.target = interior K ∧ ⇑φ = p := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- dimension `0`: `V` is a point, and so is the convex body
    haveI := subsingleton_dim_zero (V := V)
    obtain ⟨M₀⟩ := (inferInstance : Nonempty V)
    have hK := isCorpsConvexeS_singleton_S0 (p M₀)
    have hint : interior {p M₀} = ({p M₀} : Set (S 0)) := (isOpen_singleton_S0 _).interior_eq
    have hrange : range p = {p M₀} := by
      ext y
      constructor
      · rintro ⟨M, rfl⟩
        rw [Subsingleton.elim M M₀]
        exact mem_singleton _
      · intro hy
        rw [mem_singleton_iff.1 hy]
        exact mem_range_self M₀
    refine ⟨{p M₀}, hK, ?_, ?_⟩
    · rw [hint, hrange, enveloppeConvexe, hK.convex_F.convexHull_eq, Sphere.ofCone_F]
    · obtain ⟨φ, hφ, hs, ht, he⟩ := exists_chart_of_injective hp
        (fun x y _ => Subsingleton.elim x y)
      exact ⟨φ, hφ, hs, by rw [ht, hrange, hint], he⟩
  · haveI : NeZero n := ⟨hn.ne'⟩
    set A := range p with hAdef
    have hAo : IsOpen A := hp.isLocalHomeomorph.isOpenMap.isOpen_range
    set K := closure (enveloppeConvexe A) with hKdef
    have hK : IsCorpsConvexeS n K :=
      isCorpsConvexeS_closure_enveloppeConvexe hAo (range_nonempty p) hH hcl
    have hpK : ∀ M, p M ∈ interior K := fun M =>
      interior_maximal ((subset_enveloppeConvexe A).trans subset_closure) hAo (mem_range_self M)
    -- 1°: the `γ` of an automorphism, and the invariance of `W`
    have hinv : ∀ g : GXAut (GSR n) (S n) V, ∃ γ : GSR n, (∀ y, p (g • y) = γ • p y) ∧
        γ • interior K = interior K := by
      intro g
      have hpg : IsDeveloping (GSR n) (fun y => p (g • y)) :=
        isDeveloping_iff_isGXMorphism.2
          ((isDeveloping_iff_isGXMorphism.1 hp).comp g.isGXMorphism)
      obtain ⟨γ, hγ, -⟩ := hp.existsUnique_smul_eq hpg
      refine ⟨γ, hγ, ?_⟩
      have h1 : γ • A ⊆ A := by
        intro z hz
        obtain ⟨_, ⟨y, rfl⟩, rfl⟩ := Set.mem_smul_set.1 hz
        exact ⟨g • y, hγ y⟩
      have h2 : γ⁻¹ • A ⊆ A := by
        intro z hz
        obtain ⟨_, ⟨y, rfl⟩, rfl⟩ := Set.mem_smul_set.1 hz
        refine ⟨g⁻¹ • y, ?_⟩
        rw [eq_inv_smul_iff, ← hγ, smul_inv_smul]
      have h3 : γ • enveloppeConvexe A = enveloppeConvexe A :=
        Subset.antisymm (smul_enveloppeConvexe_subset h1)
          (Set.subset_smul_set_iff.2 (smul_enveloppeConvexe_subset h2))
      rw [hKdef, ← interior_smul, ← closure_smul, h3]
    obtain ⟨r, hr, hr'⟩ := exists_hasFeuille_uniform hK hp hpK hbal hinv
    have hrange := range_eq_interior hK hp hpK hr hr'
    have hcov := isCoveringMapOn_interior hp hrange hr hr'
    have hinj := injective_of_isCoveringMapOn hK hp hrange hcov
    refine ⟨K, hK, ?_, ?_⟩
    · apply Subset.antisymm
      · rw [← hrange]
        exact subset_enveloppeConvexe A
      · exact interior_maximal subset_closure (isOpen_enveloppeConvexe hAo)
    · obtain ⟨φ, hφ, hs, ht, he⟩ := exists_chart_of_injective hp hinj
      exact ⟨φ, hφ, hs, by rw [ht, hrange], he⟩

/-- **Prop. 2 as printed**, over the paper's manifolds (Hausdorff, connected, second countable;
`V : Type`): a sweepable locally projective `n`-manifold with a developing map `p` whose image has
its closure in an open hemisphere is mapped by `p`, as a compatible chart, onto the interior of a
convex body of `S(n)`. -/
def HemisphereCorpsConvexePrinted (n : ℕ) : Prop :=
  ∀ (V : Type) [TopologicalSpace V] [ChartedSpace (S n) V] [HasGroupoid V (projGroupoid n)]
    [T2Space V] [ConnectedSpace V] [SecondCountableTopology V] (p : V → S n),
    IsDeveloping (GSR n) p → IsBalayable (GSR n) (S n) V → ∀ H : Set (S n),
    Sphere.IsOpenHemisphere H → closure (range p) ⊆ H →
    ∃ K : Set (S n), IsCorpsConvexeS n K ∧ ∃ φ : OpenPartialHomeomorph V (S n),
      IsCompatibleChart (GSR n) φ ∧ φ.source = univ ∧ φ.target = interior K ∧ ⇑φ = p

/-- **Prop. 2 holds as printed in every dimension**, `n = 0` included. -/
theorem hemisphereCorpsConvexePrinted (n : ℕ) : HemisphereCorpsConvexePrinted n := by
  intro V _ _ _ _ _ _ p hp hbal H hH hcl
  obtain ⟨K, hK, -, hφ⟩ := hemisphere_corps_convexe hp hbal hH hcl
  exact ⟨K, hK, hφ⟩

end Prop2

end Benzecri
