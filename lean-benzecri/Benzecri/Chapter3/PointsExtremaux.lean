import Benzecri.Chapter3.FacettesSphere
import Benzecri.Chapter3.Simplexe
import Benzecri.Chapter2.Hilbert
import Benzecri.Chapter2.PseudoBoules

/-!
# Chapter 3 § 6, Prop. 4 — two facettes of a convex body of S(n) reduced to a point (Krein–Milman)

J.-P. Benzécri, *Sur les variétés localement affines et localement projectives*, Bull. SMF 88
(1960) 229–332, Chapter 3 § 6, journal p. 283; transcription
`papers/benzecri/legacy/labeled/benzecri1960_ch3.tex`. Target T-bz-c3-points-extremaux.

* **`bzprop:c3s6p4_deux_points_extremaux`** — `benzecri1960_ch3.tex:1570` (Prop. 4,
  l.1570–1586) — `deux_points_extremaux`: every convex body `W` of `S(n)`, `n ≥ 1`, has two
  distinct `W`-facettes (`IsFacetteK W`, Chapter 3 § 1 Déf. 4) each reduced to a point; the proof's
  remark « facette réduite à un point = point extrémal »,
  `Sphere.facetteK_eq_singleton_iff_mem_extremePoints`; the bound `n ≥ 1` is needed,
  `deux_points_extremaux_iff`, `S0_lacks_two_singleton_facettes`.

> **Proposition 4.** Sur tout corps convexe $W$ de $S(n)$ ($n\geqq 1$), on peut trouver deux
> facettes distinctes dont chacune est réduite à un point.
>
> Remarquons que la notion de facette réduite à un point s'identifie à celle de point extrémal.
> La proposition va résulter du théorème de Krein-Milman […]. Soit $\mathring{H}$ un hémisphère
> ouvert de $S(n)$ contenant $W$, $\mathring{H}$ est muni canoniquement d'une structure d'espace
> affin, il peut être muni d'une structure d'espace vectoriel à $n$ dimensions $E$. Il suffit
> d'appliquer au convexe compact $W$ de $E$ le théorème de Krein-Milman.

## The proof formalized

The open hemisphere `ℓ > 0` containing `W` (`IsCorpsConvexeS.exists_forall_pos`) is read in its
affine chart `ℓ = 1`: the section `coneSection W ℓ = {v ∈ F(W) | ℓ v = 1}` is the image of `W` in
that chart (each point of `W` has exactly one representative there, `mk_injOn_coneSection`). It is
compact (closed, `isClosed_insert_zero_F`, and bounded, `exists_mul_norm_le`) and convex.

*The remark* « facette réduite à un point = point extrémal » is
`facetteK_eq_singleton_iff_mem_extremePoints`, over any real vector space: for a convex part `k`
and a form `ℓ > 0` on `F(k)`, the facette of `mk p` (`ℓ p = 1`) is `{mk p}` iff `p` is an extreme
point of the section.

*Krein–Milman* is Mathlib's (`IsCompact.extremePoints_nonempty`,
`closure_convexHull_extremePoints`), not assumed. If the section had a single extreme point `p`
it would be `{p}`, so `W = {mk p}` would be an open point of `S(n)`, impossible for `n ≥ 1`
(`S(n)` is connected, `connectedSpace_S`, and has two points `x ≠ −x`).

*Dimension 0* (`deux_points_extremaux_iff`): the printed `n ≥ 1` is needed: a point of `S(0)` is
a convex body (`isCorpsConvexeS_singleton_S0`) with a single facette
(`S0_lacks_two_singleton_facettes`).

*Instance* (`TriangleInstance`): the closed triangle of `S(2)`, the rays of the positive octant,
is a convex body whose three vertices are three pairwise distinct facettes reduced to a point.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| « corps convexe $W$ de $S(n)$ » (Ch. 1 Déf. 11) | ✓ carried: `IsCorpsConvexeS n W` (strict convex, compact, nonempty interior) |
| « $n\geqq 1$ » | ✓ carried: `0 < n`; needed (`deux_points_extremaux_iff`) |
| « facettes » (Ch. 3 § 1 Déf. 4, transferred to $S(E)$) | ✓ carried: `IsFacetteK W` of the strict `Chapter3/FacettesSphere` |
| « réduite à un point » | ✓ carried: `f = {a}` |
| « distinctes » | ✓ carried: `f ≠ g` |
| Krein–Milman (Bourbaki EVT II § 4 th. 1), cited | ✓ formalized: Mathlib's, applied to the compact convex section |
| « $\mathring{H}$ un hémisphère ouvert contenant $W$ » | ✓ proved: `IsCorpsConvexeS.exists_forall_pos` |

## SCOPE (disclosed)

* The affine chart of the hemisphere is taken as the hyperplane section `ℓ = 1` of the cone
  rather than through `instAddTorsorHemi`: the same chart (each ray of `ℓ > 0` meets it once),
  with the vector-space structure of `ℝⁿ⁺¹` at hand for Mathlib's Krein–Milman.
* Nothing is omitted; no `sorry`, no added hypothesis.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

open Set

namespace Benzecri

namespace Sphere

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-! ### The section of the cone in the affine chart `ℓ = 1` -/

/-- The section `{v ∈ F(k) | ℓ v = 1}` of the cone of `k` by the hyperplane `ℓ = 1`: the image of
`k` in the affine chart of the open hemisphere `ℓ > 0`. -/
def coneSection (k : Set (Sphere E)) (ℓ : Module.Dual ℝ E) : Set E := {v | v ∈ F k ∧ ℓ v = 1}

/-- **The remark of the proof**: « la notion de facette réduite à un point s'identifie à celle de
point extrémal ». For a convex part `k` of `S(E)` and a form `ℓ` positive on `F(k)`, the
`k`-facette of `mk p` (`p` in the section `ℓ = 1`) is `{mk p}` iff `p` is an extreme point of the
section. -/
theorem facetteK_eq_singleton_iff_mem_extremePoints {k : Set (Sphere E)} (hk : IsConvexPart k)
    {ℓ : Module.Dual ℝ E} (hℓ : ∀ v ∈ F k, 0 < ℓ v) {p : E} (hp : p ∈ coneSection k ℓ) :
    facetteK k (mk p hp.1.1) = {mk p hp.1.1} ↔ p ∈ (coneSection k ℓ).extremePoints ℝ := by
  obtain ⟨⟨hp0, hpk⟩, hℓp⟩ := hp
  have hpK : p ∈ kPrime k := mem_insert_of_mem _ ⟨hp0, hpk⟩
  have hrep : IsRep p (mk p hp0) := ⟨hp0, rfl⟩
  constructor
  · intro hf
    refine mem_extremePoints_iff_left.2 ⟨⟨⟨hp0, hpk⟩, hℓp⟩, fun a ha b hb hab => ?_⟩
    obtain ⟨s, t, hs, ht, hst, hpe⟩ := hab
    set Q : E := (1 / 2 : ℝ) • p + (1 / 2 : ℝ) • a with hQ
    have haK : a ∈ kPrime k := mem_insert_of_mem _ ha.1
    have hbK : b ∈ kPrime k := mem_insert_of_mem _ hb.1
    have hℓQ : ℓ Q = 1 := by
      simp only [hQ, map_add, map_smul, smul_eq_mul, hℓp, ha.2]; norm_num
    have hQ0 : Q ≠ 0 := fun h => by rw [h, map_zero] at hℓQ; exact zero_ne_one hℓQ
    have hQK : Q ∈ kPrime k :=
      convex_kPrime hk hpK haK (by norm_num) (by norm_num) (by norm_num)
    have h1 : AlphaW (kPrime k) p Q := by
      refine (alphaW_iff_extend (convex_kPrime hk)).2 ⟨hpK, hQK, 2 * s / t, by positivity, ?_⟩
      convert hbK using 1
      rw [hQ, ← hpe]
      obtain rfl : s = 1 - t := by linarith
      match_scalars <;> field_simp <;> ring
    have h2 : AlphaW (kPrime k) Q p := by
      refine (alphaW_iff_extend (convex_kPrime hk)).2 ⟨hQK, hpK, 1, one_pos, ?_⟩
      convert haK using 1
      rw [hQ]
      module
    have hQrep : IsRep Q (mk Q hQ0) := ⟨hQ0, rfl⟩
    have hmem : mk Q hQ0 ∈ facetteK k (mk p hp0) :=
      ⟨(alphaK_iff hk hrep hQrep).2 h1, (alphaK_iff hk hQrep hrep).2 h2⟩
    rw [hf, mem_singleton_iff, mk_eq_mk_iff_exists_pos] at hmem
    obtain ⟨c, hc, hcQ⟩ := hmem
    have : c = 1 := by
      have := congrArg ℓ hcQ
      rwa [map_smul, smul_eq_mul, hℓQ, hℓp, mul_one] at this
    subst this
    rw [one_smul] at hcQ
    have : a = 2 • Q - p := by rw [hQ]; module
    rw [this, ← hcQ]
    module
  · intro hext
    refine Subset.antisymm (fun y hy => ?_) (singleton_subset_iff.2 (mem_facetteK_self hpk))
    obtain ⟨hxy, -⟩ := hy
    have hyk : y ∈ k := hxy.mem_right
    obtain ⟨Y, hY⟩ := exists_isRep y
    have hYF : Y ∈ F k := by obtain ⟨hY0, rfl⟩ := hY; exact ⟨hY0, hyk⟩
    have hYK : Y ∈ kPrime k := mem_insert_of_mem _ hYF
    obtain ⟨-, -, ε, hε, hP⟩ := (alphaW_iff_extend (convex_kPrime hk)).1
      ((alphaK_iff hk hrep hY).1 hxy)
    set P : E := p + ε • (p - Y) with hPdef
    obtain ⟨hY0, rfl⟩ := hY
    rw [mem_singleton_iff, mk_eq_mk_iff_exists_pos]
    -- `p = (1/(1+ε)) P + (ε/(1+ε)) Y`
    have hpe : p = (1 / (1 + ε)) • P + (ε / (1 + ε)) • Y := by
      rw [hPdef]
      have : (1 + ε) ≠ 0 := by positivity
      match_scalars
      · field_simp
      · field_simp; ring
    rcases mem_insert_iff.1 hP with hP0 | hPF
    · rw [hP0, smul_zero, zero_add] at hpe
      exact ⟨ε / (1 + ε), by positivity, hpe.symm⟩
    have hℓP := hℓ P hPF
    have hℓY := hℓ Y hYF
    have hPs : (ℓ P)⁻¹ • P ∈ coneSection k ℓ :=
      ⟨smul_mem_F hPF (inv_pos.2 hℓP), by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hℓP.ne']⟩
    have hYs : (ℓ Y)⁻¹ • Y ∈ coneSection k ℓ :=
      ⟨smul_mem_F hYF (inv_pos.2 hℓY), by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hℓY.ne']⟩
    have hsum : ℓ P / (1 + ε) + ε * ℓ Y / (1 + ε) = 1 := by
      have := congrArg ℓ hpe
      rw [hℓp, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at this
      linarith [this, show ℓ P / (1 + ε) + ε * ℓ Y / (1 + ε) =
        1 / (1 + ε) * ℓ P + ε / (1 + ε) * ℓ Y by ring]
    have hseg : p ∈ openSegment ℝ ((ℓ P)⁻¹ • P) ((ℓ Y)⁻¹ • Y) := by
      refine ⟨ℓ P / (1 + ε), ε * ℓ Y / (1 + ε), by positivity, by positivity, hsum, ?_⟩
      rw [hpe, smul_smul, smul_smul]
      congr 1 <;> congr 1 <;> field_simp
    have hYp := ((mem_extremePoints_iff_left.1 hext).2 _ hYs _ hPs (by rwa [openSegment_symm]))
    refine ⟨(ℓ Y)⁻¹, inv_pos.2 hℓY, hYp⟩

/-- Two points of the section on the same ray are equal. -/
theorem eq_of_mk_eq_of_mem_coneSection {k : Set (Sphere E)} {ℓ : Module.Dual ℝ E} {p q : E}
    (hp : p ∈ coneSection k ℓ) (hq : q ∈ coneSection k ℓ)
    (h : mk p hp.1.1 = mk q hq.1.1) : p = q := by
  obtain ⟨c, -, hc⟩ := (mk_eq_mk_iff_exists_pos _ _).1 h
  have := congrArg ℓ hc
  rw [map_smul, smul_eq_mul, hp.2, hq.2, mul_one] at this
  rw [← hc, this, one_smul]

/-- Every ray of `F(k)` meets the section: `(ℓ v)⁻¹ • v`. -/
theorem inv_smul_mem_coneSection {k : Set (Sphere E)} {ℓ : Module.Dual ℝ E} {v : E}
    (hv : v ∈ F k) (hℓv : 0 < ℓ v) : (ℓ v)⁻¹ • v ∈ coneSection k ℓ :=
  ⟨smul_mem_F hv (inv_pos.2 hℓv), by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hℓv.ne']⟩

end Sphere

open Sphere

/-- **Prop. 4** (`bzprop:c3s6p4_deux_points_extremaux`): on every convex body `W` of `S(n)`,
`n ≥ 1`, there are two distinct facettes each reduced to a point. -/
theorem deux_points_extremaux {n : ℕ} (hn : 0 < n) {W : Set (S n)} (hW : IsCorpsConvexeS n W) :
    ∃ f g : Set (S n), IsFacetteK W f ∧ IsFacetteK W g ∧ f ≠ g ∧
      (∃ a, f = {a}) ∧ (∃ b, g = {b}) := by
  obtain ⟨ℓ, hℓ⟩ := hW.exists_forall_pos
  obtain ⟨c, hc, hcn⟩ := hW.exists_mul_norm_le hℓ
  set L : Module.Dual ℝ (Fin (n + 1) → ℝ) := (ℓ : (Fin (n + 1) → ℝ) →ₗ[ℝ] ℝ) with hL
  have hL' : ∀ v ∈ F W, 0 < L v := hℓ
  have hk : IsConvexPart W := hW.1.1
  set B := coneSection W L with hBdef
  have hBeq : B = insert 0 (F W) ∩ ℓ ⁻¹' {1} := by
    ext v
    simp only [hBdef, coneSection, mem_setOf_eq, mem_inter_iff, mem_insert_iff, mem_preimage,
      mem_singleton_iff, hL, ContinuousLinearMap.coe_coe]
    constructor
    · rintro ⟨hv, h1⟩; exact ⟨Or.inr hv, h1⟩
    · rintro ⟨rfl | hv, h1⟩
      · rw [map_zero] at h1; exact absurd h1 zero_ne_one
      · exact ⟨hv, h1⟩
  have hBcl : IsClosed B := by
    rw [hBeq]
    exact hW.isClosed_insert_zero_F.inter (isClosed_singleton.preimage ℓ.continuous)
  have hBbd : Bornology.IsBounded B := by
    refine (Metric.isBounded_closedBall (x := (0 : Fin (n + 1) → ℝ)) (r := 1 / c)).subset ?_
    rintro v ⟨hv, h1⟩
    rw [Metric.mem_closedBall, dist_zero_right, le_div_iff₀ hc, mul_comm]
    have := hcn v hv
    rw [hL, ContinuousLinearMap.coe_coe] at h1
    linarith
  have hBc : IsCompact B := Metric.isCompact_of_isClosed_isBounded hBcl hBbd
  have hBconv : Convex ℝ B := by
    intro x hx y hy a b ha hb hab
    refine ⟨hW.convex_F hx.1 hy.1 ha hb hab, ?_⟩
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, hx.2, hy.2, mul_one, mul_one, hab]
  have hrep : ∀ x ∈ W, ∃ v ∈ B, ∃ h : v ≠ 0, mk v h = x := by
    intro x hx
    obtain ⟨v, hv0, rfl⟩ := exists_isRep x
    have hvF : v ∈ F W := ⟨hv0, hx⟩
    have hvB := inv_smul_mem_coneSection hvF (hL' v hvF)
    exact ⟨_, hvB, hvB.1.1, mk_smul hv0 (inv_pos.2 (hL' v hvF)) _⟩
  obtain ⟨x₀, hx₀⟩ := hW.2.2
  obtain ⟨v₀, hv₀B, -⟩ := hrep x₀ (interior_subset hx₀)
  obtain ⟨p, hp⟩ := hBc.extremePoints_nonempty ⟨v₀, hv₀B⟩
  have hpB : p ∈ B := hp.1
  obtain ⟨q, hq, hqp⟩ : ∃ q ∈ B.extremePoints ℝ, q ≠ p := by
    by_contra hne
    have hsub : B.extremePoints ℝ ⊆ {p} := fun q hq =>
      mem_singleton_iff.2 (by_contra fun h => hne ⟨q, hq, h⟩)
    have hB1 : B ⊆ {p} := by
      rw [← closure_convexHull_extremePoints hBc hBconv]
      refine (closure_mono (convexHull_mono hsub)).trans ?_
      rw [convexHull_singleton, closure_singleton]
    have hWsub : W ⊆ {mk p hpB.1.1} := by
      intro x hx
      obtain ⟨v, hvB, hv0, rfl⟩ := hrep x hx
      obtain rfl := mem_singleton_iff.1 (hB1 hvB)
      exact mem_singleton _
    have hint : interior W = {mk p hpB.1.1} :=
      Subset.antisymm (interior_subset.trans hWsub)
        (singleton_subset_iff.2 (by
          obtain rfl := mem_singleton_iff.1 (hWsub (interior_subset hx₀))
          exact hx₀))
    haveI := connectedSpace_S hn
    have hclo : IsClopen ({mk p hpB.1.1} : Set (S n)) := ⟨isClosed_singleton, hint ▸ isOpen_interior⟩
    rcases isClopen_iff.1 hclo with h | h
    · exact singleton_ne_empty _ h
    · have : -mk p hpB.1.1 ∈ ({mk p hpB.1.1} : Set (S n)) := h ▸ mem_univ _
      exact Sphere.neg_ne_self _ (mem_singleton_iff.1 this)
  have hqB : q ∈ B := hq.1
  refine ⟨{mk p hpB.1.1}, {mk q hqB.1.1}, ⟨_, hpB.1.2,
    ((facetteK_eq_singleton_iff_mem_extremePoints hk hL' hpB).2 hp).symm⟩,
    ⟨_, hqB.1.2, ((facetteK_eq_singleton_iff_mem_extremePoints hk hL' hqB).2 hq).symm⟩,
    fun h => hqp (eq_of_mk_eq_of_mem_coneSection hpB hqB (singleton_eq_singleton_iff.1 h)).symm,
    ⟨_, rfl⟩, ⟨_, rfl⟩⟩

/-- **Dimension 0**: a convex body of `S(0)` never has two distinct facettes reduced to a point. -/
theorem S0_lacks_two_singleton_facettes {W : Set (S 0)} (hW : IsCorpsConvexeS 0 W) :
    ¬ ∃ f g : Set (S 0), IsFacetteK W f ∧ IsFacetteK W g ∧ f ≠ g ∧
      (∃ a, f = {a}) ∧ (∃ b, g = {b}) := by
  rintro ⟨f, g, hf, hg, hfg, ⟨a, rfl⟩, ⟨b, rfl⟩⟩
  have ha : a ∈ W := hf.subset (mem_singleton a)
  have hb : b ∈ W := hg.subset (mem_singleton b)
  rcases S0_eq_or_eq_neg a b with h | h
  · exact hfg (by rw [h])
  · exact hW.neg_notMem ha (h ▸ hb)

/-- **The printed bound `n ≥ 1` is needed**: Prop. 4's conclusion holds for every convex body of
`S(n)` iff `0 < n`. -/
theorem deux_points_extremaux_iff (n : ℕ) :
    (∀ W : Set (S n), IsCorpsConvexeS n W → ∃ f g : Set (S n), IsFacetteK W f ∧ IsFacetteK W g ∧
      f ≠ g ∧ (∃ a, f = {a}) ∧ (∃ b, g = {b})) ↔ 0 < n := by
  refine ⟨fun h => Nat.pos_of_ne_zero fun hn => ?_, fun hn W hW => deux_points_extremaux hn hW⟩
  subst hn
  obtain ⟨x⟩ := (inferInstance : Nonempty (S 0))
  exact S0_lacks_two_singleton_facettes (isCorpsConvexeS_singleton_S0 x)
    (h _ (isCorpsConvexeS_singleton_S0 x))

/-! ### Instance: the closed simplex of `S(m)`, the triangle of `S(2)` -/

namespace TriangleInstance

variable {m : ℕ}

/-- The sum of the coordinates. -/
def sumForm (m : ℕ) : Module.Dual ℝ (Fin (m + 1) → ℝ) := ∑ i, LinearMap.proj i

theorem sumForm_apply (v : Fin (m + 1) → ℝ) : sumForm m v = ∑ i, v i := by
  simp [sumForm, LinearMap.sum_apply]

/-- The vertex `eᵢ` of the simplex. -/
def vertex (i : Fin (m + 1)) : S m := mk (Pi.single i 1) (by simp)

theorem orthant_smul {c : ℝ} (hc : 0 < c) {v : Fin (m + 1) → ℝ} (hv : v ∈ orthant m) :
    c • v ∈ orthant m := fun i => by simpa using mul_nonneg hc.le (hv i)

theorem F_simplexS : F (simplexS m) = orthant m \ {0} :=
  F_ofCone fun _ hc _ hv => orthant_smul hc hv

theorem sumForm_pos {v : Fin (m + 1) → ℝ} (hv : v ∈ F (simplexS m)) : 0 < sumForm m v := by
  rw [F_simplexS] at hv
  obtain ⟨hv, hv0⟩ := hv
  rw [sumForm_apply]
  refine lt_of_le_of_ne (Finset.sum_nonneg fun i _ => hv i) fun h => hv0 ?_
  have := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hv i).1 h.symm
  exact funext fun i => this i (Finset.mem_univ i)

/-- **The simplex is a convex body of `S(m)`.** -/
theorem isCorpsConvexeS_simplexS : IsCorpsConvexeS m (simplexS m) := by
  rw [isCorpsConvexeS_iff]
  refine ⟨?_, ?_, ?_⟩
  · intro x hx y hy a b ha hb hab
    have hxs := sumForm_pos hx
    have hys := sumForm_pos hy
    rw [F_simplexS] at hx hy ⊢
    refine ⟨fun i => ?_, fun h => ?_⟩
    · simpa using add_nonneg (mul_nonneg ha (hx.1 i)) (mul_nonneg hb (hy.1 i))
    · have h0 := congrArg (sumForm m) (mem_singleton_iff.1 h)
      rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, map_zero] at h0
      rcases ha.eq_or_lt with rfl | ha'
      · rw [zero_add] at hab; subst hab; linarith
      · nlinarith [mul_pos ha' hxs, mul_nonneg hb hys.le]
  · refine IsClosed.isCompact ?_
    rw [← isOpen_compl_iff, isOpen_iff_F, F_compl, F_simplexS]
    have hcl : IsClosed (orthant m) := by
      simp only [orthant, Set.setOf_forall]
      exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
    convert hcl.isOpen_compl using 1
    ext v
    have h0 : (0 : Fin (m + 1) → ℝ) ∈ orthant m := fun i => le_rfl
    simp only [mem_sdiff, mem_compl_iff, mem_singleton_iff, not_and, not_not]
    constructor
    · rintro ⟨hv, h⟩ hC
      exact hv (h hC)
    · intro hC
      exact ⟨fun hv => hC (hv ▸ h0), fun h => absurd h hC⟩
  · have hopen : IsOpen (ofCone {v : Fin (m + 1) → ℝ | ∀ i, 0 < v i}) := by
      refine isOpen_ofCone (fun c hc v hv i => by simpa using mul_pos hc (hv i)) ?_
      simp only [Set.setOf_forall]
      exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (continuous_apply i)
    have hne : (fun _ => (1 : ℝ) : Fin (m + 1) → ℝ) ≠ 0 := fun h => by
      simpa using congrFun h 0
    refine ⟨mk _ hne, interior_maximal (image_mono (preimage_mono fun v hv i => (hv i).le))
      hopen (mk_mem_ofCone hne fun i => one_pos)⟩

theorem single_mem_coneSection (i : Fin (m + 1)) :
    (Pi.single i 1 : Fin (m + 1) → ℝ) ∈ coneSection (simplexS m) (sumForm m) := by
  refine ⟨?_, by rw [sumForm_apply]; simp⟩
  rw [F_simplexS]
  refine ⟨fun j => ?_, by simp⟩
  by_cases h : j = i
  · subst h; simp
  · simp [h]

/-- The vertex `eᵢ` is an extreme point of the section `∑ vⱼ = 1` (the standard simplex). -/
theorem single_mem_extremePoints (i : Fin (m + 1)) :
    (Pi.single i 1 : Fin (m + 1) → ℝ) ∈
      (coneSection (simplexS m) (sumForm m)).extremePoints ℝ := by
  refine mem_extremePoints_iff_left.2 ⟨single_mem_coneSection i, fun a ha b hb hab => ?_⟩
  obtain ⟨s, t, hs, ht, hst, he⟩ := hab
  have haO : a ∈ orthant m := (F_simplexS ▸ ha.1).1
  have hbO : b ∈ orthant m := (F_simplexS ▸ hb.1).1
  have hj : ∀ j, j ≠ i → a j = 0 := by
    intro j hji
    have := congrFun he j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, hji, if_false] at this
    nlinarith [haO j, hbO j, mul_nonneg hs.le (haO j), mul_nonneg ht.le (hbO j)]
  have hsum := ha.2
  rw [sumForm_apply, Finset.sum_eq_single i (fun j _ h => hj j h) (by simp)] at hsum
  funext j
  by_cases h : j = i
  · subst h; simp [hsum]
  · simp [h, hj j h]

/-- **Every vertex of the simplex is a facette reduced to a point.** -/
theorem facetteK_vertex (i : Fin (m + 1)) : facetteK (simplexS m) (vertex i) = {vertex i} :=
  (facetteK_eq_singleton_iff_mem_extremePoints isCorpsConvexeS_simplexS.1.1
    (fun _ hv => sumForm_pos hv) (single_mem_coneSection i)).2 (single_mem_extremePoints i)

theorem isFacetteK_vertex (i : Fin (m + 1)) : IsFacetteK (simplexS m) {vertex i} :=
  ⟨vertex i, (single_mem_coneSection i).1.2, (facetteK_vertex i).symm⟩

theorem vertex_injective : Function.Injective (vertex (m := m)) := by
  intro i j h
  have := eq_of_mk_eq_of_mem_coneSection (single_mem_coneSection i) (single_mem_coneSection j) h
  by_contra hij
  simpa [hij] using congrFun this i

/-- **Instance**: the closed triangle of `S(2)` is a convex body with three pairwise distinct
facettes reduced to a point, its vertices. -/
theorem triangle_three_facettes :
    IsCorpsConvexeS 2 (simplexS 2) ∧ (∀ i : Fin 3, IsFacetteK (simplexS 2) {vertex i}) ∧
      Function.Injective (fun i : Fin 3 => ({vertex i} : Set (S 2))) :=
  ⟨isCorpsConvexeS_simplexS, isFacetteK_vertex, fun _ _ h =>
    vertex_injective (singleton_eq_singleton_iff.1 h)⟩

end TriangleInstance

end Benzecri
