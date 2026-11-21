import GX.Spherical.TroyanovTwoPi

/-!
# Troyanov's theorem for angles all below `2π`: the double of a convex spherical polygon

Target `T-gx-troyanov-polygon` (`roadmap/roadmap.toml`; DEC-136, Troyanov's theorem proved, not
assumed). `papers/gx`, 0 `sorry`, standard axioms only. **No label is marked here.**

* `cex:start_singular_manifold_homeomorphic` — `RamcovGX.tex:1930` — partial, not marked: the row
  needs Troyanov's theorem for every angle (some `θ_i > 2π` remains, `T-gx-troyanov`) and the
  Thurston suspension facts (`GX.thurstonSuspensionFacts`), both outside this module. Here the
  cited theorem (`MR1005085`), in the shape of `GX.TroyanovTheorem`
  (`GXScaffold.Spherical.TroyanovAngles`, restated inline), is proved for every `s` when all
  angles are below `2π`: **`GX.troyanovTheorem_of_lt_two_pi`**; the target's statement, `s ≥ 4`,
  is `GX.troyanovTheorem_four_le_of_lt_two_pi`. With `GX.Spherical.TroyanovTwoPi`, it holds for
  all angles `≤ 2π` (`GX.troyanovTheorem_of_le_two_pi`), and `GX.TroyanovTheorem` reduces to its
  case `s ≥ 4`, all `θ_i ≠ 2π`, some `θ_i > 2π` (`GX.troyanovTheorem_of_exists_gt_two_pi`).
* Under the weaker **subcritical** hypothesis (`0 < χ'`, `χ' < 2θ_i`, `χ' = ∑ (θ_i − 2π) + 4π`),
  all `θ_i ∈ ]0, 2π[`, `s ≥ 3`: `GX.exists_isConeSphere_of_subcritical`.
* The polygon: `GX.SphPolygon` (by the normals of its sides), `GX.exists_sphPolygon` (angles
  `α_i ∈ ]0, π[` with `∑ (π − α_i) < 2π` and `2(π − α_k) < ∑ (π − α_i)`), through its polar
  polygon inscribed in a circle: `GX.exists_polar_radius` (the intermediate value theorem in the
  radius), `GX.exists_polar_polygon`, `GX.SphPolygon.ofCyclic` (a cyclically ordered polar polygon
  gives a convex polygon: `GX.cyc_adjacent`, `GX.cyc_cover`).
* The double: `GX.SphPolygon.PolyDouble` (`𝕊²` as a space), `GX.SphPolygon.singularGXStructure`,
  the cone points `GX.SphPolygon.isConePoint_vertex`, **`GX.SphPolygon.isConeSphere`**: the
  machinery of `GX.Spherical.TroyanovTriangle` (the gauge rescale, the polar fold, the comparison
  through the developing maps) for `s` vertices.
* Remarks: `GX.troyanovAngleCondition_four_lt_two_pi` (the case is not vacuous: four pairwise
  distinct angles below `2π`), `GX.exists_isConeSphere_four_not_troyanovAngleCondition` (for
  `s = 4` too the printed condition is sufficient, not necessary).

> Start from $\Sigma$ a singular $\SS^2$-manifold homeomorphic to a sphere with $s\geq 3$
> conical singularities of respective angles $(\theta_i)_{i\in \lsem 1,s\rsem}$. We know from
> Troyanov \cite{MR1005085}  that one can construct such a surface for arbitrary
> $(\theta_i)_{i\in \lsem 1,s\rsem}$ as long as
> $$0<\sum_{i=1}^s( \theta_i -2\pi) + 4\pi\leq \min(4\pi, \theta_i : i\in \lsem 1,s\rsem).$$
> (l.1930)

## The construction

With `α_i = θ_i / 2 ∈ ]0, π[` and `β_i = π − α_i`, the condition gives `∑ β_i < 2π` (`χ' > 0`)
and `β_k < ∑_{j ≠ k} β_j` (`χ' < 2θ_k`). Put the longest `β` last. On the circle of radius `r`
about the north pole, a chord of length `β` spans the azimuth `gap(β, r) = arccos((cos β −
cos² r)/sin² r)`, defined for `r ≥ β/2`. Let `G(r)` be the sum of the gaps of the first `s − 1`
chords and `H(r)` the gap of the last, on `[β_max/2, π/2]`: `H(β_max/2) = π`, and at `r = π/2`
the gaps are the `β_i`. If `G(β_max/2) ≤ π`, then `G − H` changes sign (`G = H`: the centre of the
circle is outside the polygon); otherwise `G + H − 2π` does (`G = 2π − H`: inside). Either way
the vertices `n_k` at the partial sums of the gaps close up into a polar polygon with sides
`β_i`, cyclically ordered (`n_i · (n_j × n_k) = cos r sin² r · 4 ∏ sin(half-gaps) > 0`), whose
dual `{x : ⟨n_k, x⟩ ≥ 0}` is the convex polygon with angles `α_i`: two sides meet only at a
vertex (a diagonal of the polar polygon separates two of its vertices) and no point lies on three
sides. Its double, glued along the boundary, is `𝕊²` (the gauge rescale of the polygon in the
stereographic chart at `v_0`, convex since its angles are `< π`); at `v_i` the polar fold onto
the sector of angle `α_i` gives an `X_{2α_i}`-chart, and two cone charts differ near every common
point by one element of `SO(3)` (`fold`, `ρ ∘ fold`, `refEdge k`).

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `s ≥ 3` conical singularities (l.1930) | every `s` (in the condition); the target is `s ≥ 4` |
| Troyanov's condition (l.1930) | ✓ carried: `TroyanovAngleCondition θ`, verbatim (DEC-69's) |
| the angles `θ_i` arbitrary | ⚠ restricted: all `θ_i < 2π` (`> 2π`: `T-gx-troyanov`) |
| `Σ` ≅ sphere, conical singularities of angles `θ_i` | ✓ `GX.IsConeSphere` (OQ-37 (b)) |
| Troyanov's theorem (`MR1005085`), cited | ✓ proved for angles `< 2π`, not assumed (DEC-136) |

## SCOPE (disclosed)

* **(a)** Angles all `< 2π` only (`≤ 2π` with the reduction of `GX.Spherical.TroyanovTwoPi`);
  the row stays partial (see above).
* **(b)** The metric is not formalized (as in `GX.Spherical.ConeSurface`): a cone point is an
  `X_θ`-chart onto a neighbourhood of the apex of `C_θ`; the regular part carries the a.e.
  `(SO(3), 𝕊²)`-atlas.
* **(c)** The surface is the doubled polygon, not Troyanov's variational solution; it exists
  under the subcritical hypothesis, weaker than the printed one (the remark above). Only
  sufficiency is proved; that a convex polygon with these angles exists ONLY under it (the
  planner's "iff") is not.
* **(d)** `GX.TroyanovTheorem` is restated inline (its body): the scaffold `TroyanovAngles` is not
  imported. `M : Type`, as there.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Builds on
`GX.Spherical.TroyanovTriangle` (`frameSO3`, `polarFold`, `isOpenMap_restrict_of_isCompact`,
`symm_trans_mem_aeAtlas_of_opens`, `isPortly_compl_singleton_sph2`, the generic lemmas of
`GX.SphTriangle`), `GX.Spherical.TroyanovTwoPi` (`IsConeSphere.insertNth`,
`troyanovTheorem_of_four_le_of_ne_two_pi`), `GX.Spherical.ConeSurface`, mathlib's
`intermediate_value_Icc`.
-/

noncomputable section

open Set Filter Topology Function TopologicalSpace Matrix

open scoped Real

namespace GX

set_option linter.unusedSectionVars false

/-! ### Relabelling the cone points -/

section Relabel

variable {M : Type*} [TopologicalSpace M] [SingularGXStructure SO3 Sph2 M]

/-- **A cone sphere, relabelled**: permuting the indices of the cone points and of their angles
together leaves a cone sphere. -/
theorem IsConeSphere.comp_equiv {s : ℕ} {θ : Fin s → ℝ} {p : Fin s → M} (h : IsConeSphere M θ p)
    (σ : Fin s ≃ Fin s) : IsConeSphere M (θ ∘ σ) (p ∘ σ) where
  homeomorphic := h.homeomorphic
  injective := h.injective.comp σ.injective
  pos i := h.pos (σ i)
  isConePoint i := h.isConePoint (σ i)
  sing_subset x hx := by
    obtain ⟨j, rfl⟩ := h.sing_subset hx
    exact ⟨σ.symm j, by simp only [Function.comp_apply, Equiv.apply_symm_apply]⟩

end Relabel

/-! ### The polar polygon, inscribed in a circle about the north pole -/

section PolarPolygon

/-- The cosine of the azimuth gap of a chord of length `b` on the circle of radius `r`. -/
def chordCos (b r : ℝ) : ℝ := (Real.cos b - Real.cos r ^ 2) / Real.sin r ^ 2

/-- The azimuth gap. -/
def chordGap (b r : ℝ) : ℝ := Real.arccos (chordCos b r)

/-- A point of the circle of radius `r` about the north pole, at longitude `φ`. -/
def polVec (r φ : ℝ) : Fin 3 → ℝ := ![Real.cos r, Real.sin r * Real.cos φ, Real.sin r * Real.sin φ]

theorem polVec_dot (r φ ψ : ℝ) :
    polVec r φ ⬝ᵥ polVec r ψ = Real.cos r ^ 2 + Real.sin r ^ 2 * Real.cos (ψ - φ) := by
  simp [polVec, dotProduct, Fin.sum_univ_three, Real.cos_sub]; ring

theorem polVec_dot_self (r φ : ℝ) : polVec r φ ⬝ᵥ polVec r φ = 1 := by
  rw [polVec_dot, sub_self, Real.cos_zero, mul_one, add_comm, Real.sin_sq_add_cos_sq]

/-- `sin 2A + sin 2B − sin 2(A + B) = 4 sin A sin B sin(A + B)`. -/
theorem sin_add_sin_sub_sin (A B : ℝ) :
    Real.sin (2 * A) + Real.sin (2 * B) - Real.sin (2 * A + 2 * B) =
      4 * Real.sin A * Real.sin B * Real.sin (A + B) := by
  rw [Real.sin_add, Real.sin_add, Real.sin_two_mul, Real.sin_two_mul, Real.cos_two_mul,
    Real.cos_two_mul]
  linear_combination (-4 * Real.sin A * Real.cos A) * Real.sin_sq_add_cos_sq B +
    (-4 * Real.sin B * Real.cos B) * Real.sin_sq_add_cos_sq A

/-- **The triple product of three points of the circle**, in the half-gaps of their longitudes. -/
theorem polVec_triple (r a b c : ℝ) :
    polVec r a ⬝ᵥ polVec r b ⨯₃ polVec r c = Real.cos r * Real.sin r ^ 2 *
      (4 * Real.sin ((b - a) / 2) * Real.sin ((c - b) / 2) * Real.sin ((c - a) / 2)) := by
  have h := sin_add_sin_sub_sin ((b - a) / 2) ((c - b) / 2)
  have e1 : 2 * ((b - a) / 2) = b - a := by ring
  have e2 : 2 * ((c - b) / 2) = c - b := by ring
  have e3 : (b - a) / 2 + (c - b) / 2 = (c - a) / 2 := by ring
  have e4 : b - a + (c - b) = c - a := by ring
  rw [e1, e2, e3, e4] at h
  rw [← h]
  simp [polVec, cross_apply, dotProduct, Fin.sum_univ_three, Real.sin_sub]
  ring

/-- Three points of a circle of radius `< π/2`, at increasing longitudes within one turn, are
positively oriented. -/
theorem polVec_triple_pos {r a b c : ℝ} (hr0 : 0 < r) (hr1 : r < π / 2) (hab : a < b)
    (hbc : b < c) (hca : c < a + 2 * π) : 0 < polVec r a ⬝ᵥ polVec r b ⨯₃ polVec r c := by
  rw [polVec_triple]
  have hc : 0 < Real.cos r := Real.cos_pos_of_mem_Ioo ⟨by linarith, hr1⟩
  have hs : 0 < Real.sin r := Real.sin_pos_of_pos_of_lt_pi hr0 (by linarith)
  have h1 : 0 < Real.sin ((b - a) / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have h2 : 0 < Real.sin ((c - b) / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have h3 : 0 < Real.sin ((c - a) / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  positivity

/-- Bounds on `chordCos` for a chord no longer than the diameter `2r`. -/
theorem chordCos_mem {b r : ℝ} (hb0 : 0 < b) (hbr : b ≤ 2 * r) (hr0 : 0 < r) (hr1 : r ≤ π / 2) :
    -1 ≤ chordCos b r ∧ chordCos b r < 1 := by
  have hs : 0 < Real.sin r := Real.sin_pos_of_pos_of_lt_pi hr0 (by linarith [Real.pi_pos])
  have hs2 : 0 < Real.sin r ^ 2 := by positivity
  have hsc := Real.sin_sq_add_cos_sq r
  have hcos : Real.cos (2 * r) ≤ Real.cos b :=
    Real.cos_le_cos_of_nonneg_of_le_pi hb0.le (by linarith) hbr
  have hc1 : Real.cos b < 1 := by
    rw [← Real.cos_zero]
    exact Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl (by linarith) hb0
  rw [Real.cos_two_mul] at hcos
  unfold chordCos
  constructor
  · rw [le_div_iff₀ hs2]; nlinarith
  · rw [div_lt_one hs2]; nlinarith

theorem chordGap_pos {b r : ℝ} (hb0 : 0 < b) (hbr : b ≤ 2 * r) (hr0 : 0 < r) (hr1 : r ≤ π / 2) :
    0 < chordGap b r :=
  Real.arccos_pos.2 (chordCos_mem hb0 hbr hr0 hr1).2

theorem cos_chordGap {b r : ℝ} (hb0 : 0 < b) (hbr : b ≤ 2 * r) (hr0 : 0 < r) (hr1 : r ≤ π / 2) :
    Real.cos (chordGap b r) = chordCos b r :=
  Real.cos_arccos (chordCos_mem hb0 hbr hr0 hr1).1 (chordCos_mem hb0 hbr hr0 hr1).2.le

theorem chordGap_pi_div_two {b : ℝ} (hb0 : 0 ≤ b) (hbπ : b ≤ π) : chordGap b (π / 2) = b := by
  unfold chordGap chordCos
  rw [Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero, one_pow, div_one]
  exact Real.arccos_cos hb0 hbπ

theorem chordGap_half {b : ℝ} (hb0 : 0 < b) (hbπ : b < π) : chordGap b (b / 2) = π := by
  unfold chordGap chordCos
  have hs : 0 < Real.sin (b / 2) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have e : Real.cos b = Real.cos (2 * (b / 2)) := by ring_nf
  rw [e, Real.cos_two_mul]
  have hsc := Real.sin_sq_add_cos_sq (b / 2)
  have : (2 * Real.cos (b / 2) ^ 2 - 1 - Real.cos (b / 2) ^ 2) / Real.sin (b / 2) ^ 2 = -1 := by
    rw [div_eq_iff (by positivity)]; linarith
  rw [this, Real.arccos_neg_one]

theorem continuousOn_chordGap (b : ℝ) {r₀ : ℝ} (hr₀ : 0 < r₀) :
    ContinuousOn (chordGap b) (Icc r₀ (π / 2)) := by
  refine Real.continuous_arccos.comp_continuousOn ?_
  refine ContinuousOn.div (by fun_prop) (by fun_prop) fun r hr => ?_
  have : 0 < Real.sin r := Real.sin_pos_of_pos_of_lt_pi (by linarith [hr.1])
    (by linarith [hr.2, Real.pi_pos])
  positivity


/-- **The radius of the polar polygon** (the continuity argument): for chord lengths
`β_k ∈ ]0, π[`, `k ≤ m`, the last one the longest, with `∑ β_k < 2π` and `β_m < ∑_{k<m} β_k`,
there is a radius `r ∈ [β_m/2, π/2[` at which the azimuth gaps `G` of the first `m` chords sum to
less than `2π` and close the polygon: `cos G = chordCos β_m r`. Either `G = gap(β_m)` (the centre
of the circle outside the polygon) or `G = 2π − gap(β_m)` (inside), by the intermediate value
theorem on `[β_m/2, π/2]`. -/
theorem exists_polar_radius {m : ℕ} (β : Fin (m + 1) → ℝ) (hpos : ∀ k, 0 < β k)
    (hlt : ∀ k, β k < π) (hsum : ∑ k, β k < 2 * π)
    (hlast : β (Fin.last m) < ∑ j : Fin m, β (Fin.castSucc j)) :
    ∃ r, β (Fin.last m) / 2 ≤ r ∧ r < π / 2 ∧
      ∑ j : Fin m, chordGap (β (Fin.castSucc j)) r < 2 * π ∧
      Real.cos (∑ j : Fin m, chordGap (β (Fin.castSucc j)) r) =
        chordCos (β (Fin.last m)) r := by
  set L := β (Fin.last m) with hL
  set r₀ := L / 2 with hr₀def
  set G : ℝ → ℝ := fun r => ∑ j : Fin m, chordGap (β (Fin.castSucc j)) r with hGdef
  set H : ℝ → ℝ := fun r => chordGap L r with hHdef
  have hL0 : 0 < L := hpos _
  have hLπ : L < π := hlt _
  have hr₀ : 0 < r₀ := by positivity
  have hr₀1 : r₀ < π / 2 := by rw [hr₀def]; linarith
  have hGc : ContinuousOn G (Icc r₀ (π / 2)) :=
    continuousOn_finsetSum _ fun j _ => continuousOn_chordGap _ hr₀
  have hHc : ContinuousOn H (Icc r₀ (π / 2)) := continuousOn_chordGap _ hr₀
  have hGπ : G (π / 2) = ∑ j : Fin m, β (Fin.castSucc j) :=
    Finset.sum_congr rfl fun j _ => chordGap_pi_div_two (hpos _).le (hlt _).le
  have hHπ : H (π / 2) = L := chordGap_pi_div_two hL0.le hLπ.le
  have hH₀ : H r₀ = π := chordGap_half hL0 hLπ
  have hsplit : ∑ k, β k = ∑ j : Fin m, β (Fin.castSucc j) + L := Fin.sum_univ_castSucc β
  have hmem : ∀ r ∈ Icc r₀ (π / 2), -1 ≤ chordCos L r ∧ chordCos L r < 1 := fun r hr =>
    chordCos_mem hL0 (by linarith [hr.1]) (by linarith [hr.1]) hr.2
  have hHpos : ∀ r ∈ Icc r₀ (π / 2), 0 < H r := fun r hr => Real.arccos_pos.2 (hmem r hr).2
  have hHle : ∀ r, H r ≤ π := fun r => Real.arccos_le_pi _
  have hcosH : ∀ r ∈ Icc r₀ (π / 2), Real.cos (H r) = chordCos L r := fun r hr =>
    Real.cos_arccos (hmem r hr).1 (hmem r hr).2.le
  rcases le_or_gt (G r₀) π with hA | hB
  · -- the centre of the circle outside the polygon: `G = H`
    obtain ⟨r, hr, hFr⟩ : (0 : ℝ) ∈ (fun r => G r - H r) '' Icc r₀ (π / 2) :=
      intermediate_value_Icc hr₀1.le (hGc.sub hHc)
        ⟨by show G r₀ - H r₀ ≤ 0; linarith,
          by show 0 ≤ G (π / 2) - H (π / 2); rw [hGπ, hHπ]; linarith⟩
    have hGH : G r = H r := by
      have : G r - H r = 0 := hFr
      linarith
    refine ⟨r, hr.1, lt_of_le_of_ne hr.2 fun e => ?_, ?_, ?_⟩
    · rw [e, hGπ, hHπ] at hGH; linarith
    · show G r < 2 * π
      rw [hGH]; linarith [hHle r, Real.pi_pos]
    · show Real.cos (G r) = _
      rw [hGH]; exact hcosH r hr
  · -- the centre inside: `G = 2π − H`
    obtain ⟨r, hr, hFr⟩ : (0 : ℝ) ∈ (fun r => G r + H r - 2 * π) '' Icc r₀ (π / 2) :=
      intermediate_value_Icc' hr₀1.le ((hGc.add hHc).sub continuousOn_const)
        ⟨by show G (π / 2) + H (π / 2) - 2 * π ≤ 0; rw [hGπ, hHπ]; linarith,
          by show 0 ≤ G r₀ + H r₀ - 2 * π; linarith⟩
    have hGH : G r = 2 * π - H r := by
      have : G r + H r - 2 * π = 0 := hFr
      linarith
    refine ⟨r, hr.1, lt_of_le_of_ne hr.2 fun e => ?_, ?_, ?_⟩
    · rw [e, hGπ, hHπ] at hGH; linarith
    · show G r < 2 * π
      rw [hGH]; linarith [hHpos r hr]
    · show Real.cos (G r) = _
      rw [hGH, Real.cos_two_pi_sub]; exact hcosH r hr

/-- The cyclic successor on `Fin (m + 1)`. -/
def succMod {m : ℕ} (i : Fin (m + 1)) : Fin (m + 1) :=
  if h : i.val < m then ⟨i.val + 1, by omega⟩ else ⟨0, by omega⟩

theorem val_succMod {m : ℕ} (i : Fin (m + 1)) :
    (succMod i).val = if i.val < m then i.val + 1 else 0 := by
  unfold succMod; split_ifs <;> rfl

/-- The triple-product identity behind the convexity arguments. -/
theorem triple_identity (u v w x : Fin 3 → ℝ) :
    (x ⬝ᵥ u) * ((v ⨯₃ w) ⬝ᵥ x) + (x ⬝ᵥ v) * ((w ⨯₃ u) ⬝ᵥ x) + (x ⬝ᵥ w) * ((u ⨯₃ v) ⬝ᵥ x) =
      (u ⬝ᵥ v ⨯₃ w) * (x ⬝ᵥ x) := by
  simp [cross_apply, dotProduct, Fin.sum_univ_three]; ring

section Cyclic

variable {m : ℕ} {n : Fin (m + 1) → Fin 3 → ℝ}
  (hcyc : ∀ i j k : Fin (m + 1), i.val < j.val → j.val < k.val → 0 < n i ⬝ᵥ n j ⨯₃ n k)
include hcyc

theorem cyc_pos (i k : Fin (m + 1)) (h1 : k ≠ succMod i) (h2 : k ≠ i) :
    0 < n k ⬝ᵥ n i ⨯₃ n (succMod i) := by
  have hs := val_succMod i
  have h1' : k.val ≠ (succMod i).val := fun e => h1 (Fin.ext e)
  have h2' : k.val ≠ i.val := fun e => h2 (Fin.ext e)
  split_ifs at hs with hi
  · rcases lt_or_gt_of_ne h2' with hk | hk
    · exact hcyc k i _ hk (by omega)
    · rw [triple_product_permutation]
      exact hcyc i _ k (by omega) (by omega)
  · rw [triple_product_permutation, triple_product_permutation]
    exact hcyc _ k i (by omega) (by omega)

theorem cyc_triple_ne_zero {k l j : Fin (m + 1)} (hkl : k ≠ l) (hlj : l ≠ j) (hkj : k ≠ j) :
    n k ⬝ᵥ n l ⨯₃ n j ≠ 0 := by
  have hkl' : k.val ≠ l.val := fun e => hkl (Fin.ext e)
  have hlj' : l.val ≠ j.val := fun e => hlj (Fin.ext e)
  have hkj' : k.val ≠ j.val := fun e => hkj (Fin.ext e)
  have anti : ∀ u v w : Fin 3 → ℝ, u ⬝ᵥ v ⨯₃ w = -(u ⬝ᵥ w ⨯₃ v) := fun u v w => by
    rw [← dotProduct_neg, cross_anticomm]
  rcases lt_or_gt_of_ne hkl' with h1 | h1 <;> rcases lt_or_gt_of_ne hlj' with h2 | h2 <;>
    rcases lt_or_gt_of_ne hkj' with h3 | h3
  · exact (hcyc k l j h1 h2).ne'
  · omega
  · -- `k < j < l`
    rw [anti]; exact neg_ne_zero.2 (hcyc k j l h3 h2).ne'
  · -- `j < k < l`
    rw [triple_product_permutation, triple_product_permutation]
    exact (hcyc j k l h3 h1).ne'
  · -- `l < k < j`
    rw [anti, triple_product_permutation, triple_product_permutation]
    exact neg_ne_zero.2 (hcyc l k j h1 h3).ne'
  · -- `l < j < k`
    rw [triple_product_permutation]
    exact (hcyc l j k h2 h3).ne'
  · omega
  · -- `j < l < k`
    rw [anti, triple_product_permutation]
    exact neg_ne_zero.2 (hcyc j l k h2 h1).ne'

variable {x : Fin 3 → ℝ} (hx : x ⬝ᵥ x = 1) (hP : ∀ k, 0 ≤ n k ⬝ᵥ x)
include hx hP

/-- **Two sides of the polygon meet only at a vertex**: if `x` lies on the sides `k < l`, they
are consecutive (`l = k + 1`, or `k = 0` and `l = m`). Otherwise the great circle through
`n_k, n_l` separates two polar vertices `n_j`, `n_{j'}`, and `x ∈ P` cannot pair nonnegatively
with both. -/
theorem cyc_adjacent {k l : Fin (m + 1)} (hkl : k.val < l.val) (hk : n k ⬝ᵥ x = 0)
    (hl : n l ⬝ᵥ x = 0) : l.val = k.val + 1 ∨ (k.val = 0 ∧ l.val = m) := by
  by_contra hne
  push Not at hne
  obtain ⟨hne1, hne2⟩ := hne
  set j : Fin (m + 1) := ⟨k.val + 1, by omega⟩
  have hId : ∀ w : Fin 3 → ℝ, (x ⬝ᵥ w) * ((n k ⨯₃ n l) ⬝ᵥ x) = n k ⬝ᵥ n l ⨯₃ w := fun w => by
    have := triple_identity (n k) (n l) w x
    rw [dotProduct_comm x (n k), hk, dotProduct_comm x (n l), hl, hx] at this
    linarith
  have hDj : n k ⬝ᵥ n l ⨯₃ n j < 0 := by
    have := hcyc k j l (by show k.val < k.val + 1; omega) (by show k.val + 1 < l.val; omega)
    rw [← cross_anticomm, dotProduct_neg]; linarith
  obtain ⟨j', hj'⟩ : ∃ j' : Fin (m + 1), 0 < n k ⬝ᵥ n l ⨯₃ n j' := by
    rcases Nat.eq_zero_or_pos k.val with hk0 | hk0
    · refine ⟨Fin.last m, hcyc k l _ hkl ?_⟩
      have := hne2 hk0; have := l.2; simp only [Fin.val_last]; omega
    · refine ⟨⟨0, by omega⟩, ?_⟩
      rw [triple_product_permutation, triple_product_permutation]
      exact hcyc _ k l hk0 hkl
  have e1 := hId (n j)
  have e2 := hId (n j')
  have p1 := hP j
  have p2 := hP j'
  rw [dotProduct_comm] at p1 p2
  have hneg : (x ⬝ᵥ n j * ((n k ⨯₃ n l) ⬝ᵥ x)) * (x ⬝ᵥ n j' * ((n k ⨯₃ n l) ⬝ᵥ x)) < 0 := by
    rw [e1, e2]; exact mul_neg_of_neg_of_pos hDj hj'
  nlinarith [mul_nonneg (mul_nonneg p1 p2) (sq_nonneg ((n k ⨯₃ n l) ⬝ᵥ x))]

/-- No point of the polygon lies on three sides. -/
theorem cyc_not_three {k l j : Fin (m + 1)} (hkl : k ≠ l) (hlj : l ≠ j) (hkj : k ≠ j)
    (hk : n k ⬝ᵥ x = 0) (hl : n l ⬝ᵥ x = 0) (hj : n j ⬝ᵥ x = 0) : False := by
  have := triple_identity (n k) (n l) (n j) x
  rw [dotProduct_comm x (n k), hk, dotProduct_comm x (n l), hl, dotProduct_comm x (n j), hj,
    hx] at this
  exact cyc_triple_ne_zero hcyc hkl hlj hkj (by linarith)

/-- **Every point of the polygon is off the sides not through some vertex.** -/
theorem cyc_cover : ∃ i, ∀ k, k ≠ succMod i → k ≠ i → 0 < n k ⬝ᵥ x := by
  by_cases hZ : ∃ k, n k ⬝ᵥ x = 0
  · obtain ⟨k, hk⟩ := hZ
    by_cases hZ2 : ∃ l, l ≠ k ∧ n l ⬝ᵥ x = 0
    · obtain ⟨l, hlk, hl⟩ := hZ2
      -- the vertex with sides `k` and `l`
      obtain ⟨i, hi⟩ : ∃ i, (k = i ∧ l = succMod i) ∨ (l = i ∧ k = succMod i) := by
        have hlk' : l.val ≠ k.val := fun e => hlk (Fin.ext e)
        rcases lt_or_gt_of_ne hlk' with h | h
        · rcases cyc_adjacent hcyc hx hP h hl hk with e | ⟨e1, e2⟩
          · refine ⟨l, Or.inr ⟨rfl, Fin.ext ?_⟩⟩
            rw [val_succMod, if_pos (by have := k.2; omega)]; omega
          · refine ⟨k, Or.inl ⟨rfl, Fin.ext ?_⟩⟩
            rw [val_succMod, if_neg (by omega)]; omega
        · rcases cyc_adjacent hcyc hx hP h hk hl with e | ⟨e1, e2⟩
          · refine ⟨k, Or.inl ⟨rfl, Fin.ext ?_⟩⟩
            rw [val_succMod, if_pos (by have := l.2; omega)]; omega
          · refine ⟨l, Or.inr ⟨rfl, Fin.ext ?_⟩⟩
            rw [val_succMod, if_neg (by omega)]; omega
      refine ⟨i, fun k' h1 h2 => lt_of_le_of_ne (hP k') fun e => ?_⟩
      have hk'k : k' ≠ k := by rcases hi with ⟨rfl, -⟩ | ⟨-, rfl⟩ <;> assumption
      have hk'l : k' ≠ l := by rcases hi with ⟨-, rfl⟩ | ⟨rfl, -⟩ <;> assumption
      exact cyc_not_three hcyc hx hP hlk.symm hk'l.symm hk'k.symm hk hl e.symm
    · push Not at hZ2
      refine ⟨k, fun k' _ h2 => lt_of_le_of_ne (hP k') fun e => hZ2 k' h2 e.symm⟩
  · push Not at hZ
    exact ⟨0, fun k _ _ => lt_of_le_of_ne (hP k) (hZ k).symm⟩

end Cyclic

theorem cos_sq_add_sin_sq_mul_chordCos (b : ℝ) {r : ℝ} (hr : Real.sin r ≠ 0) :
    Real.cos r ^ 2 + Real.sin r ^ 2 * chordCos b r = Real.cos b := by
  unfold chordCos; field_simp; ring

/-- **The polar polygon** (the construction): for angles `α_i ∈ ]0, π[`, `i ≤ m`, `m ≥ 2`, the
last one the smallest, with `∑ (π − α_i) < 2π` and `2(π − α_m) < ∑ (π − α_i)`, there are unit
vectors `n_0, …, n_m` on a circle about the north pole, in this cyclic order
(`n_i · (n_j × n_k) > 0` for `i < j < k`), with `⟨n_i, n_{i+1}⟩ = −cos α_i` (indices mod
`m + 1`):
the vertices of the polar polygon, of sides `π − α_i`. -/
theorem exists_polar_polygon {m : ℕ} (α : Fin (m + 1) → ℝ) (hpos : ∀ i, 0 < α i)
    (hlt : ∀ i, α i < π) (hmin : ∀ k, α (Fin.last m) ≤ α k) (hsum : ∑ i, (π - α i) < 2 * π)
    (hlast : 2 * (π - α (Fin.last m)) < ∑ i, (π - α i)) :
    ∃ n : Fin (m + 1) → Fin 3 → ℝ, (∀ k, n k ⬝ᵥ n k = 1) ∧
      (∀ i, n i ⬝ᵥ n (succMod i) = -Real.cos (α i)) ∧
      (∀ i j k : Fin (m + 1), i.val < j.val → j.val < k.val → 0 < n i ⬝ᵥ n j ⨯₃ n k) := by
  set β : Fin (m + 1) → ℝ := fun k => π - α k with hβ
  have hβpos : ∀ k, 0 < β k := fun k => by simp only [hβ]; linarith [hlt k]
  have hβlt : ∀ k, β k < π := fun k => by simp only [hβ]; linarith [hpos k]
  have hsplit : ∑ k, β k = ∑ j : Fin m, β (Fin.castSucc j) + β (Fin.last m) :=
    Fin.sum_univ_castSucc β
  obtain ⟨r, hr0, hr1, hG, hcos⟩ := exists_polar_radius β hβpos hβlt hsum
    (by have : 2 * β (Fin.last m) < ∑ k, β k := hlast
        linarith)
  have hr0' : 0 < r := lt_of_lt_of_le (by have := hβpos (Fin.last m); positivity) hr0
  have hsr : Real.sin r ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi hr0' (by linarith [Real.pi_pos])).ne'
  have hβr : ∀ k, β k ≤ 2 * r := fun k => by
    have : β k ≤ β (Fin.last m) := by simp only [hβ]; linarith [hmin k]
    linarith
  set d : ℕ → ℝ := fun j => if hj : j < m then chordGap (β ⟨j, by omega⟩) r else 0 with hd
  set φ : ℕ → ℝ := fun k => ∑ j ∈ Finset.range k, d j with hφ
  have hd_pos : ∀ j, j < m → 0 < d j := fun j hj => by
    simp only [hd, dif_pos hj]
    exact chordGap_pos (hβpos _) (hβr _) hr0' hr1.le
  have hd_nonneg : ∀ j, 0 ≤ d j := fun j => by
    by_cases hj : j < m
    · exact (hd_pos j hj).le
    · simp only [hd, dif_neg hj, le_refl]
  have hφ_mono : ∀ p q, p ≤ q → φ p ≤ φ q := fun p q h =>
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono h) fun j _ _ => hd_nonneg j
  have hφ_strict : ∀ p q, p < q → q ≤ m → φ p < φ q := fun p q h hq => by
    have e := Finset.sum_range_add_sum_Ico d h.le
    have : 0 < ∑ j ∈ Finset.Ico p q, d j :=
      Finset.sum_pos (fun j hj => hd_pos j (by have := (Finset.mem_Ico.1 hj).2; omega))
        (Finset.nonempty_Ico.2 h)
    show ∑ j ∈ Finset.range p, d j < ∑ j ∈ Finset.range q, d j
    linarith
  have hφ0 : φ 0 = 0 := Finset.sum_range_zero _
  have hφm : φ m = ∑ j : Fin m, chordGap (β (Fin.castSucc j)) r := by
    show ∑ j ∈ Finset.range m, d j = _
    rw [← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hd, dif_pos j.2]; rfl
  have hφsucc : ∀ j, φ (j + 1) = φ j + d j := fun j => Finset.sum_range_succ _ _
  refine ⟨fun k => polVec r (φ k.val), fun k => polVec_dot_self _ _, fun i => ?_,
    fun i j k hij hjk => ?_⟩
  · show polVec r (φ i.val) ⬝ᵥ polVec r (φ (succMod i).val) = _
    rw [polVec_dot]
    have hs := val_succMod i
    by_cases hi : i.val < m
    · rw [if_pos hi] at hs
      rw [hs, hφsucc, add_sub_cancel_left]
      have hdi : d i.val = chordGap (β i) r := by simp only [hd, dif_pos hi]
      rw [hdi, cos_chordGap (hβpos _) (hβr _) hr0' hr1.le, cos_sq_add_sin_sq_mul_chordCos _ hsr]
      simp only [hβ, Real.cos_pi_sub]
    · rw [if_neg hi] at hs
      have hil : i = Fin.last m := Fin.ext (by have := i.2; simp only [Fin.val_last]; omega)
      have him : i.val = m := by rw [hil]; rfl
      rw [hs, him, hφ0, zero_sub, Real.cos_neg, hφm, hcos, cos_sq_add_sin_sq_mul_chordCos _ hsr,
        hil]
      simp only [hβ, Real.cos_pi_sub]
  · have hk := k.2
    refine polVec_triple_pos hr0' hr1 (hφ_strict _ _ hij (by omega))
      (hφ_strict _ _ hjk (by omega)) ?_
    have h1 : φ k.val ≤ φ m := hφ_mono _ _ (by omega)
    have h2 : 0 ≤ φ i.val := hφ0 ▸ hφ_mono _ _ (Nat.zero_le _)
    rw [hφm] at h1
    linarith

end PolarPolygon

/-! ### Convex spherical polygons, by the normals of their sides -/

section Polygon

/-- **A convex spherical polygon with angles `α_i`**, given by the inward unit normals `n_k` of its
sides `e_k`. The polygon is `P = {x ∈ 𝕊² : ⟨n_k, x⟩ ≥ 0 for all k}` (`SphPolygon.T`). Its vertex
`v_i` is the meeting point of the sides `e_{a i}` and `e_{b i}`, at the angle `α_i`
(`⟨n_{b i}, n_{a i}⟩ = −cos α_i`), and lies strictly inside the other half-spheres (`pos`:
`v_i` is the direction of `n_{b i} × n_{a i}`). Distinct vertices have distinct pairs of sides
(`vertex_sep`), and every point of `P` lies off the sides not through some vertex (`cover`): the
sides meet only at the vertices, two at a time. (It generalizes `GX.SphTriangle`, whose vertex
`v_i` has `a i = i + 2`, `b i = i + 1`; no conversion between the two is built.) -/
structure SphPolygon (s : ℕ) where
  /-- The angles. -/
  α : Fin s → ℝ
  /-- The inward unit normals of the sides. -/
  n : Fin s → Fin 3 → ℝ
  /-- The side through `v_i` read along the meridian `ψ = 0` of the chart at `v_i`. -/
  a : Fin s → Fin s
  /-- The side through `v_i` read along the meridian `ψ = α_i`. -/
  b : Fin s → Fin s
  three_le : 3 ≤ s
  α_pos : ∀ i, 0 < α i
  α_lt_pi : ∀ i, α i < π
  unit : ∀ k, n k ⬝ᵥ n k = 1
  gram : ∀ i, n (b i) ⬝ᵥ n (a i) = -Real.cos (α i)
  pos : ∀ i k, k ≠ a i → k ≠ b i → 0 < n k ⬝ᵥ n (b i) ⨯₃ n (a i)
  exists_other : ∀ i, ∃ k, k ≠ a i ∧ k ≠ b i
  vertex_sep : ∀ i j, i ≠ j → (a j ≠ a i ∧ a j ≠ b i) ∨ (b j ≠ a i ∧ b j ≠ b i)
  cover : ∀ x : Fin 3 → ℝ, x ⬝ᵥ x = 1 → (∀ k, 0 ≤ n k ⬝ᵥ x) →
    ∃ i, ∀ k, k ≠ a i → k ≠ b i → 0 < n k ⬝ᵥ x

/-- **Relabelling the vertices** of a polygon (its sides unchanged). -/
def SphPolygon.comp {s : ℕ} (t : SphPolygon s) (σ : Equiv.Perm (Fin s)) : SphPolygon s where
  α := t.α ∘ σ
  n := t.n
  a := t.a ∘ σ
  b := t.b ∘ σ
  three_le := t.three_le
  α_pos i := t.α_pos _
  α_lt_pi i := t.α_lt_pi _
  unit := t.unit
  gram i := t.gram _
  pos i := t.pos _
  exists_other i := t.exists_other _
  vertex_sep i j hij := t.vertex_sep _ _ (σ.injective.ne hij)
  cover x hx hP := by
    obtain ⟨i, hi⟩ := t.cover x hx hP
    exact ⟨σ.symm i, by simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hi⟩

theorem cyc_exists_other {m : ℕ} (hm : 2 ≤ m) (i : Fin (m + 1)) :
    ∃ k, k ≠ succMod i ∧ k ≠ id i := by
  by_contra hne
  push Not at hne
  have hs := val_succMod i
  have key : ∀ c : ℕ, c < m + 1 → c = (succMod i).val ∨ c = i.val := fun c hc => by
    by_contra h
    push Not at h
    exact h.2 (congrArg Fin.val (hne ⟨c, hc⟩ fun e => h.1 (congrArg Fin.val e)))
  have h0 := key 0 (by omega)
  have h1 := key 1 (by omega)
  have h2 := key 2 (by omega)
  have := i.2
  split_ifs at hs <;> omega

theorem cyc_vertex_sep {m : ℕ} (hm : 2 ≤ m) (i j : Fin (m + 1)) (hij : i ≠ j) :
    (succMod j ≠ succMod i ∧ succMod j ≠ id i) ∨ (id j ≠ succMod i ∧ id j ≠ id i) := by
  have hi := val_succMod i
  have hj := val_succMod j
  have hij' : i.val ≠ j.val := fun e => hij (Fin.ext e)
  simp only [id, ne_eq, Fin.ext_iff]
  have := i.2; have := j.2
  split_ifs at hi hj <;> omega

/-- **A polygon from a cyclically ordered polar polygon**: unit vectors `n_0, …, n_m` (`m ≥ 2`)
with `n_i · (n_j × n_k) > 0` for `i < j < k` and `⟨n_i, n_{i+1}⟩ = −cos α_i` are the normals of
a convex spherical polygon with angles `α_i`, its vertex `v_i` on the sides `e_i` and `e_{i+1}`. -/
def SphPolygon.ofCyclic {m : ℕ} (hm : 2 ≤ m) (α : Fin (m + 1) → ℝ) (n : Fin (m + 1) → Fin 3 → ℝ)
    (hpos : ∀ i, 0 < α i) (hlt : ∀ i, α i < π) (hunit : ∀ k, n k ⬝ᵥ n k = 1)
    (hgram : ∀ i, n i ⬝ᵥ n (succMod i) = -Real.cos (α i))
    (hcyc : ∀ i j k : Fin (m + 1), i.val < j.val → j.val < k.val → 0 < n i ⬝ᵥ n j ⨯₃ n k) :
    SphPolygon (m + 1) where
  α := α
  n := n
  a := succMod
  b := id
  three_le := by omega
  α_pos := hpos
  α_lt_pi := hlt
  unit := hunit
  gram := hgram
  pos i k h1 h2 := cyc_pos hcyc i k h1 h2
  exists_other := cyc_exists_other hm
  vertex_sep := cyc_vertex_sep hm
  cover x hx hP := cyc_cover hcyc hx hP

/-- **A convex spherical polygon with prescribed angles `α_i ∈ ]0, π[` exists** as soon as
`∑ (π − α_i) < 2π` and `2(π − α_k) < ∑ (π − α_i)` for every `k` (its polar polygon, of sides
`π − α_i`, inscribed in a circle: `GX.exists_polar_polygon`; the smallest angle is put last by a
relabelling). -/
theorem exists_sphPolygon {s : ℕ} (hs : 3 ≤ s) (α : Fin s → ℝ) (hpos : ∀ i, 0 < α i)
    (hlt : ∀ i, α i < π) (hsum : ∑ i, (π - α i) < 2 * π)
    (hk : ∀ k, 2 * (π - α k) < ∑ i, (π - α i)) : ∃ t : SphPolygon s, t.α = α := by
  obtain ⟨m, rfl⟩ : ∃ m, s = m + 1 := ⟨s - 1, by omega⟩
  have hm : 2 ≤ m := by omega
  obtain ⟨k₀, -, hk₀⟩ := Finset.exists_min_image Finset.univ α Finset.univ_nonempty
  set σ : Equiv.Perm (Fin (m + 1)) := Equiv.swap k₀ (Fin.last m)
  have hσσ : ∀ i, σ (σ i) = i := fun i => Equiv.swap_apply_self _ _ _
  have hsumσ : ∑ i, (π - (α ∘ σ) i) = ∑ i, (π - α i) :=
    Equiv.sum_comp σ (fun i => π - α i)
  have hlastσ : (α ∘ σ) (Fin.last m) = α k₀ := by
    rw [Function.comp_apply, Equiv.swap_apply_right]
  obtain ⟨n, hunit, hgram, hcyc⟩ := exists_polar_polygon (α ∘ σ) (fun i => hpos _)
    (fun i => hlt _) (fun k => by rw [hlastσ]; exact hk₀ _ (Finset.mem_univ _))
    (by rw [hsumσ]; exact hsum) (by rw [hsumσ, hlastσ]; exact hk k₀)
  refine ⟨(SphPolygon.ofCyclic hm (α ∘ σ) n (fun i => hpos _) (fun i => hlt _) hunit hgram
    hcyc).comp σ, ?_⟩
  funext i
  show α (σ (σ i)) = α i
  rw [hσσ]

end Polygon

/-! ### Finite conditions are open, or closed -/

theorem isOpen_setOf_forall_imp_imp_pos {X ι : Type*} [TopologicalSpace X] [Finite ι]
    (P Q : ι → Prop) {f : ι → X → ℝ} (hf : ∀ k, Continuous (f k)) :
    IsOpen {x | ∀ k, P k → Q k → 0 < f k x} := by
  have : {x | ∀ k, P k → Q k → 0 < f k x} = ⋂ k, {x | P k → Q k → 0 < f k x} := by
    ext x; simp only [mem_setOf_eq, mem_iInter]
  rw [this]
  refine isOpen_iInter_of_finite fun k => ?_
  by_cases hk : P k ∧ Q k
  · have : {x | P k → Q k → 0 < f k x} = {x | 0 < f k x} := by
      ext x; simp only [mem_setOf_eq, hk.1, hk.2, forall_true_left]
    rw [this]; exact isOpen_lt continuous_const (hf k)
  · have : {x | P k → Q k → 0 < f k x} = univ := by
      ext x; simp only [mem_setOf_eq, mem_univ, iff_true]
      intro h1 h2; exact absurd ⟨h1, h2⟩ hk
    rw [this]; exact isOpen_univ

theorem isClosed_setOf_forall_imp_imp_nonneg {X ι : Type*} [TopologicalSpace X] [Finite ι]
    (P Q : ι → Prop) {f : ι → X → ℝ} (hf : ∀ k, Continuous (f k)) :
    IsClosed {x | ∀ k, P k → Q k → 0 ≤ f k x} := by
  have : {x | ∀ k, P k → Q k → 0 ≤ f k x} = ⋂ k, {x | P k → Q k → 0 ≤ f k x} := by
    ext x; simp only [mem_setOf_eq, mem_iInter]
  rw [this]
  refine isClosed_iInter fun k => ?_
  by_cases hk : P k ∧ Q k
  · have : {x | P k → Q k → 0 ≤ f k x} = {x | 0 ≤ f k x} := by
      ext x; simp only [mem_setOf_eq, hk.1, hk.2, forall_true_left]
    rw [this]; exact isClosed_le continuous_const (hf k)
  · have : {x | P k → Q k → 0 ≤ f k x} = univ := by
      ext x; simp only [mem_setOf_eq, mem_univ, iff_true]
      intro h1 h2; exact absurd ⟨h1, h2⟩ hk
    rw [this]; exact isClosed_univ

/-! ### The polygon: its frames at the vertices -/

section Frames

namespace SphPolygon

variable {s : ℕ} (t : SphPolygon s)

/-- The closed polygon. -/
def T : Set Sph2 := {y | ∀ k, 0 ≤ t.n k ⬝ᵥ vec y}

theorem isClosed_T : IsClosed t.T := by
  simp only [T, setOf_forall]
  exact isClosed_iInter fun k => isClosed_le continuous_const (continuous_dot_vec _)

theorem sin_pos (i : Fin s) : 0 < Real.sin (t.α i) :=
  Real.sin_pos_of_pos_of_lt_pi (t.α_pos i) (t.α_lt_pi i)

/-- The base vertex `v_0`, where the polygon is read in a stereographic chart. -/
def o : Fin s := ⟨0, by have := t.three_le; omega⟩

/-- A side not through `v_i`. -/
def ko (i : Fin s) : Fin s := (t.exists_other i).choose

theorem ko_ne_a (i : Fin s) : t.ko i ≠ t.a i := (t.exists_other i).choose_spec.1

theorem ko_ne_b (i : Fin s) : t.ko i ≠ t.b i := (t.exists_other i).choose_spec.2

/-- The second vector of the frame at `v_i`: the unit tangent of `e_{a i}` at `v_i`, inside. -/
def m (i : Fin s) : Fin 3 → ℝ :=
  (Real.sin (t.α i))⁻¹ • (t.n (t.b i) + Real.cos (t.α i) • t.n (t.a i))

theorem m_dot_n (i : Fin s) : t.m i ⬝ᵥ t.n (t.a i) = 0 := by
  rw [m, smul_dotProduct, add_dotProduct, smul_dotProduct, t.gram, t.unit]
  simp

theorem m_dot_m (i : Fin s) : t.m i ⬝ᵥ t.m i = 1 := by
  have hs := t.sin_pos i
  have h1 := t.gram i
  have h2 := t.unit (t.b i)
  have h3 := t.unit (t.a i)
  rw [m]
  simp only [smul_dotProduct, dotProduct_smul, add_dotProduct, dotProduct_add, smul_eq_mul]
  rw [dotProduct_comm (t.n (t.a i)) (t.n (t.b i)), h1, h2, h3]
  have hsc := Real.sin_sq_add_cos_sq (t.α i)
  field_simp
  nlinarith

theorem n_b_eq (i : Fin s) :
    t.n (t.b i) = Real.sin (t.α i) • t.m i - Real.cos (t.α i) • t.n (t.a i) := by
  have hs := (t.sin_pos i).ne'
  rw [m, smul_smul, mul_inv_cancel₀ hs, one_smul]
  abel

/-- **The rotation `R_i` putting the vertex `v_i` at the north pole**, the side `e_{a i}` along
the meridian `ψ = 0` and the side `e_{b i}` along the meridian `ψ = α_i`. -/
def R (i : Fin s) : SO3 := frameSO3 (t.m i) (t.n (t.a i)) (t.m_dot_m i) (t.unit _) (t.m_dot_n i)

/-- Its matrix. -/
def A (i : Fin s) : Matrix (Fin 3) (Fin 3) ℝ := frameMat (t.m i) (t.n (t.a i))

theorem A_mulVec (i : Fin s) (x : Fin 3 → ℝ) :
    t.A i *ᵥ x = ![(t.m i ⨯₃ t.n (t.a i)) ⬝ᵥ x, t.m i ⬝ᵥ x, t.n (t.a i) ⬝ᵥ x] :=
  frameMat_mulVec _ _ _

theorem A_mulVec_n_a (i : Fin s) : t.A i *ᵥ t.n (t.a i) = ![0, 0, 1] := by
  rw [A_mulVec, t.unit, t.m_dot_n, dotProduct_comm, dot_cross_self]

theorem A_mulVec_n_b (i : Fin s) :
    t.A i *ᵥ t.n (t.b i) = ![0, Real.sin (t.α i), -Real.cos (t.α i)] := by
  rw [t.n_b_eq i, A_mulVec]
  have h1 : (t.m i ⨯₃ t.n (t.a i)) ⬝ᵥ (Real.sin (t.α i) • t.m i - Real.cos (t.α i) • t.n (t.a i))
      = 0 := by
    rw [dotProduct_sub, dotProduct_smul, dotProduct_smul, dotProduct_comm, dot_self_cross,
      dotProduct_comm, dot_cross_self]
    simp
  rw [h1]
  simp only [dotProduct_sub, dotProduct_smul, smul_eq_mul, t.m_dot_m, t.m_dot_n, t.unit,
    dotProduct_comm (t.n (t.a i)) (t.m i)]
  ext j; fin_cases j <;> simp

/-- The first coordinate of `R_i n_k` is positive for a side `e_k` not through `v_i`:
`⟨n_k, v_i⟩ > 0`. -/
theorem A_mulVec_n_other_pos (i k : Fin s) (h1 : k ≠ t.a i) (h2 : k ≠ t.b i) :
    0 < (t.A i *ᵥ t.n k) 0 := by
  rw [A_mulVec]
  show 0 < (t.m i ⨯₃ t.n (t.a i)) ⬝ᵥ t.n k
  rw [dotProduct_comm, m, LinearMap.map_smul, LinearMap.smul_apply, map_add, LinearMap.add_apply,
    LinearMap.map_smul, LinearMap.smul_apply, cross_self, smul_zero, add_zero, dotProduct_smul]
  exact smul_pos (inv_pos.2 (t.sin_pos i)) (t.pos i k h1 h2)

theorem A_transpose_mul (i : Fin s) : (t.A i)ᵀ * t.A i = 1 :=
  frameMat_transpose_mul (t.m_dot_m i) (t.unit _) (t.m_dot_n i)

theorem vec_R_smul (i : Fin s) (y : Sph2) : vec (t.R i • y) = t.A i *ᵥ vec y :=
  vec_frameSO3_smul _ _ _ y ▸ (t.A_mulVec i (vec y)).symm ▸ rfl

theorem dot_vec_R_inv_smul (i : Fin s) (c : Fin 3 → ℝ) (y : Sph2) :
    c ⬝ᵥ vec ((t.R i)⁻¹ • y) = (t.A i *ᵥ c) ⬝ᵥ vec y :=
  dot_vec_frameSO3_inv_smul _ _ _ c y

/-- The pairing with a point read in the stereographic chart at `v_i`. -/
theorem dot_vec_R_inv_stereoInv (i : Fin s) (c : Fin 3 → ℝ) (v : ℂ) :
    c ⬝ᵥ vec ((t.R i)⁻¹ • stereoInv v) = gfun (t.A i *ᵥ c) v / (1 + ‖v‖ ^ 2) := by
  rw [dot_vec_R_inv_smul, dot_vec_stereoInv]

/-- The reflection `σ_k` of `𝕊²` in the great circle of the side `e_k`. -/
def σ (k : Fin s) : Sph2 → Sph2 := reflSph (t.n k) (t.unit k)

theorem vec_R_σ_R_inv (i k : Fin s) (y : Sph2) :
    vec (t.R i • t.σ k ((t.R i)⁻¹ • y)) =
      vec y - (2 * ((t.A i *ᵥ t.n k) ⬝ᵥ vec y)) • (t.A i *ᵥ t.n k) := by
  rw [t.vec_R_smul, σ, vec_reflSph, mulVec_sub, mulVec_smul, t.dot_vec_R_inv_smul]
  congr 1
  have h := t.vec_R_smul i ((t.R i)⁻¹ • y)
  rw [smul_inv_smul] at h
  exact h.symm

/-- **The reflection in `e_{a i}` is `ρ` at `v_i`**: `R_i σ_{a i} R_i⁻¹ = ρ`. -/
theorem R_σ_a (i : Fin s) (y : Sph2) :
    t.R i • t.σ (t.a i) ((t.R i)⁻¹ • y) = conjSph y := by
  apply vec_injective
  rw [t.vec_R_σ_R_inv, t.A_mulVec_n_a, vec_conjSph]
  ext j; fin_cases j <;> simp [dotProduct, Fin.sum_univ_three]; ring

/-- **The reflection in `e_{b i}` is the rotation of angle `2α_i` after `ρ` at `v_i`**:
`R_i σ_{b i} R_i⁻¹ (stereoInv v) = stereoInv (e^{2iα_i} v̄)`. -/
theorem R_σ_b_stereoInv (i : Fin s) (v : ℂ) :
    t.R i • t.σ (t.b i) ((t.R i)⁻¹ • stereoInv v) =
      stereoInv (Complex.exp (((2 * t.α i : ℝ) : ℂ) * Complex.I) * (starRingEnd ℂ) v) := by
  apply vec_injective
  rw [t.vec_R_σ_R_inv, t.A_mulVec_n_b, vec_stereoInv, vec_stereoInv]
  have hn : ‖Complex.exp (((2 * t.α i : ℝ) : ℂ) * Complex.I) * (starRingEnd ℂ) v‖ = ‖v‖ := by
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_conj]
  rw [hn]
  have hre : (Complex.exp (((2 * t.α i : ℝ) : ℂ) * Complex.I) * (starRingEnd ℂ) v).re =
      Real.cos (2 * t.α i) * v.re + Real.sin (2 * t.α i) * v.im := by
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    ring
  have him : (Complex.exp (((2 * t.α i : ℝ) : ℂ) * Complex.I) * (starRingEnd ℂ) v).im =
      Real.sin (2 * t.α i) * v.re - Real.cos (2 * t.α i) * v.im := by
    simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    ring
  rw [hre, him, Real.cos_two_mul, Real.sin_two_mul]
  have hsc := Real.sin_sq_add_cos_sq (t.α i)
  have hs2 : Real.sin (t.α i) ^ 2 = 1 - Real.cos (t.α i) ^ 2 := by linarith
  have hD : (0 : ℝ) < 1 + ‖v‖ ^ 2 := by positivity
  ext j; fin_cases j
  · simp
  · simp only [dotProduct, Fin.sum_univ_three]
    simp
    field_simp
    linear_combination (-2 * v.re) * hsc
  · simp only [dotProduct, Fin.sum_univ_three]
    simp
    field_simp
    ring

/-- The `R_i`-stereographic coordinate of a point with `⟨n_k, x⟩ ≥ 0`, `e_k` a side not through
`v_i`, is defined: such a point is not the antipode `−v_i`. -/
theorem fst_ne_of_dot_nonneg (i k : Fin s) (h1 : k ≠ t.a i) (h2 : k ≠ t.b i) {x : Sph2}
    (hx : 0 ≤ t.n k ⬝ᵥ vec x) : ((t.R i • x : Sph2) : Euc3).fst ≠ -1 := by
  intro h
  have hv := vec_dot_self (t.R i • x)
  have hvec : vec (t.R i • x) = ![-1, 0, 0] := by
    rw [vec_apply] at hv ⊢
    simp only [dotProduct, Fin.sum_univ_three, h] at hv
    simp at hv
    have h1 : ((t.R i • x : Sph2) : Euc3).snd.re = 0 := by nlinarith
    have h2 : ((t.R i • x : Sph2) : Euc3).snd.im = 0 := by nlinarith
    rw [h, h1, h2]
  have e : x = (t.R i)⁻¹ • (t.R i • x) := (inv_smul_smul _ _).symm
  rw [e, t.dot_vec_R_inv_smul, hvec] at hx
  have := t.A_mulVec_n_other_pos i k h1 h2
  simp [dotProduct, Fin.sum_univ_three] at hx
  linarith

end SphPolygon

end Frames

open SphTriangle (gfun_add convex_gfun_nonneg sheet sheet_sq homeoComplex_apex homeoComplex_mk_lift
  sphConeDev_lift qOf cplx_qOf qOf_snd isOpenMap_cplx_posEmb continuous_cplx_posEmb
  im_cplx_one_posEmb continuous_q_snd eventually_snd_mem sin_nonneg_of_mem sin_neg_of_mem
  sin_neg_of_mem' arg_div_mem_up arg_div_mem_down re_pos_of_polarFold_im
  re_neg_of_polarFold_sector)

/-! ### The topological model: the double of the polygon is the round sphere -/

section Model

namespace SphPolygon

variable {s : ℕ} (t : SphPolygon s)

/-- The half-spheres bounding the polygon, read in the stereographic chart at `v_0`:
`⟨n_k, R_0⁻¹ stereoInv v⟩ = G_k(v) / (1 + |v|²)`, `G_k = gfun (cK k)`. -/
def cK (k : Fin s) : Fin 3 → ℝ := t.A t.o *ᵥ t.n k

theorem cK_dot_self (k : Fin s) : t.cK k ⬝ᵥ t.cK k = 1 := by
  rw [cK, dot_mulVec_self (t.A_transpose_mul t.o), t.unit]

theorem cK_a : t.cK (t.a t.o) = ![0, 0, 1] := t.A_mulVec_n_a t.o

theorem cK_b : t.cK (t.b t.o) = ![0, Real.sin (t.α t.o), -Real.cos (t.α t.o)] :=
  t.A_mulVec_n_b t.o

theorem cK_zero_nonneg (k : Fin s) : 0 ≤ t.cK k 0 := by
  by_cases h1 : k = t.a t.o
  · rw [h1, cK_a]; simp
  by_cases h2 : k = t.b t.o
  · rw [h2, cK_b]; simp
  exact (t.A_mulVec_n_other_pos t.o k h1 h2).le

/-- **The polygon in the stereographic chart at `v_0`**, `K = {v : G_k(v) ≥ 0 for all k}`: two
half-planes through `0` (the sides at `v_0`) and discs (the other sides). -/
def K : Set ℂ := {v | ∀ k, 0 ≤ gfun (t.cK k) v}

theorem mem_T_iff (v : ℂ) : (t.R t.o)⁻¹ • stereoInv v ∈ t.T ↔ v ∈ t.K := by
  have hD : (0 : ℝ) < 1 + ‖v‖ ^ 2 := by positivity
  simp only [T, K, mem_setOf_eq, t.dot_vec_R_inv_stereoInv, cK]
  exact forall_congr' fun k => by rw [le_div_iff₀ hD, zero_mul]

theorem convex_K : Convex ℝ t.K := by
  have : t.K = ⋂ k, {v : ℂ | 0 ≤ gfun (t.cK k) v} := by ext v; simp [K]
  rw [this]
  exact convex_iInter fun k => convex_gfun_nonneg (t.cK_zero_nonneg k)

theorem isClosed_K : IsClosed t.K := by
  have : t.K = ⋂ k, {v : ℂ | 0 ≤ gfun (t.cK k) v} := by ext v; simp [K]
  rw [this]
  exact isClosed_iInter fun k => isClosed_le continuous_const (continuous_gfun _)

/-- A disc `{G_c ≥ 0}`, `c` a unit vector with `c 0 > 0`, is bounded. -/
theorem norm_le_of_gfun_nonneg {c : Fin 3 → ℝ} (hc : c ⬝ᵥ c = 1) (ha : 0 < c 0) {v : ℂ}
    (hv : 0 ≤ gfun c v) : ‖v‖ ≤ 3 / c 0 := by
  have h1 := hc
  simp only [dotProduct, Fin.sum_univ_three] at h1
  have ha1 : c 0 ≤ 1 := by nlinarith [sq_nonneg (c 1), sq_nonneg (c 2)]
  simp only [gfun] at hv
  have hsq : ‖v‖ ^ 2 = v.re ^ 2 + v.im ^ 2 := by rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hcs : (c 1 * v.re + c 2 * v.im) ^ 2 ≤ ‖v‖ ^ 2 := by
    rw [hsq]
    nlinarith [sq_nonneg (c 1 * v.im - c 2 * v.re), sq_nonneg (c 1), sq_nonneg (c 2),
      sq_nonneg v.re, sq_nonneg v.im]
  have hcs' : c 1 * v.re + c 2 * v.im ≤ ‖v‖ := by
    nlinarith [norm_nonneg v, sq_nonneg (c 1 * v.re + c 2 * v.im - ‖v‖)]
  rw [le_div_iff₀ ha]
  by_contra hlt
  rw [not_le] at hlt
  nlinarith [norm_nonneg v]

theorem isBounded_K : Bornology.IsBounded t.K := by
  have ha : 0 < t.cK (t.ko t.o) 0 :=
    t.A_mulVec_n_other_pos t.o _ (t.ko_ne_a t.o) (t.ko_ne_b t.o)
  refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := 3 / t.cK (t.ko t.o) 0)).subset
    fun v hv => ?_
  rw [Metric.mem_closedBall, dist_zero_right]
  exact norm_le_of_gfun_nonneg (t.cK_dot_self _) ha (hv _)

/-- The open polygon in the chart, `G_k > 0`. -/
theorem gfun_pos_mem_interior_K {v : ℂ} (hv : ∀ k, 0 < gfun (t.cK k) v) : v ∈ interior t.K := by
  set U : Set ℂ := ⋂ k, {v : ℂ | 0 < gfun (t.cK k) v}
  have hUo : IsOpen U :=
    isOpen_iInter_of_finite fun k => isOpen_lt continuous_const (continuous_gfun _)
  have hUK : U ⊆ t.K := fun w hw k => (mem_iInter.1 hw k).le
  exact interior_maximal hUK hUo (mem_iInter.2 hv)

/-- **The polygon has interior points**: on the bisector at `v_0`, near `v_0`. -/
theorem interior_K_nonempty : (interior t.K).Nonempty := by
  set β := t.α t.o / 2
  have hβ0 : 0 < β := by have := t.α_pos t.o; positivity
  have hβπ : β < π := by have := t.α_lt_pi t.o; show t.α t.o / 2 < π; linarith [Real.pi_pos]
  have hsβ : 0 < Real.sin β := Real.sin_pos_of_pos_of_lt_pi hβ0 hβπ
  set f : ℝ → ℂ := fun ε => (ε : ℂ) * Complex.exp ((β : ℂ) * Complex.I)
  have hfre : ∀ ε, (f ε).re = ε * Real.cos β := fun ε => by
    simp only [f]; rw [Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  have hfim : ∀ ε, (f ε).im = ε * Real.sin β := fun ε => by
    simp only [f]; rw [Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]
  have hev : ∀ k, ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < gfun (t.cK k) (f ε) := by
    intro k
    by_cases h1 : k = t.a t.o
    · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
      rw [h1, cK_a]
      simp only [gfun, hfre, hfim]
      simp
      positivity
    by_cases h2 : k = t.b t.o
    · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
      rw [h2, cK_b]
      simp only [gfun, hfre, hfim]
      simp
      have : Real.sin (t.α t.o) * Real.cos β - Real.cos (t.α t.o) * Real.sin β =
          Real.sin β := by
        rw [← Real.sin_sub]; congr 1; ring
      nlinarith
    · have hc : 0 < gfun (t.cK k) (f 0) := by
        simp only [f, Complex.ofReal_zero, zero_mul, gfun, norm_zero, Complex.zero_re,
          Complex.zero_im]
        simp
        exact t.A_mulVec_n_other_pos t.o k h1 h2
      have hcont : Continuous fun ε => gfun (t.cK k) (f ε) :=
        (continuous_gfun _).comp (by fun_prop)
      exact (hcont.tendsto 0 |>.eventually (lt_mem_nhds hc)).filter_mono nhdsWithin_le_nhds
  obtain ⟨ε, hε⟩ := (Filter.eventually_all.2 hev).exists
  exact ⟨f ε, t.gfun_pos_mem_interior_K hε⟩

/-- The homeomorphism of the plane taking the polygon `K` onto the closed unit disc
(`gaugeRescaleHomeomorph`, through mathlib's
`exists_homeomorph_image_interior_closure_frontier_eq_unitBall`). -/
def eK : ℂ ≃ₜ ℂ :=
  (exists_homeomorph_image_interior_closure_frontier_eq_unitBall t.convex_K t.interior_K_nonempty
    t.isBounded_K).choose

theorem eK_spec : t.eK '' interior t.K = Metric.ball 0 1 ∧
    t.eK '' closure t.K = Metric.closedBall 0 1 ∧
    t.eK '' frontier t.K = Metric.sphere 0 1 :=
  (exists_homeomorph_image_interior_closure_frontier_eq_unitBall t.convex_K t.interior_K_nonempty
    t.isBounded_K).choose_spec

theorem eK_image_K : t.eK '' t.K = Metric.closedBall 0 1 := by
  rw [← t.isClosed_K.closure_eq]; exact t.eK_spec.2.1

theorem mem_interior_K_iff (v : ℂ) : v ∈ interior t.K ↔ ‖t.eK v‖ < 1 := by
  rw [← mem_ball_zero_iff, ← t.eK_spec.1, t.eK.injective.mem_set_image]

/-- **A point of the chart where some `G_k ≤ 0` is not interior to `K`**: if `G_k(v) = 0`, moving
from `v` against the gradient of `G_k` leaves `K` at once. -/
theorem notMem_interior_K {v : ℂ} {k : Fin s} (hk : gfun (t.cK k) v ≤ 0) : v ∉ interior t.K := by
  intro hv
  have hvK : v ∈ t.K := interior_subset hv
  have h0 : gfun (t.cK k) v = 0 := le_antisymm hk (hvK k)
  set c := t.cK k
  have hc0 : 0 ≤ c 0 := t.cK_zero_nonneg k
  have hc1 : c 0 * c 0 + c 1 * c 1 + c 2 * c 2 = 1 := by
    have := t.cK_dot_self k; simpa [dotProduct, Fin.sum_univ_three] using this
  set g : ℂ := ⟨c 1 - c 0 * v.re, c 2 - c 0 * v.im⟩
  have hg : 0 < ‖g‖ := by
    rw [norm_pos_iff]
    intro hg0
    have e1 : c 1 = c 0 * v.re := by have := congrArg Complex.re hg0; simp [g] at this; linarith
    have e2 : c 2 = c 0 * v.im := by have := congrArg Complex.im hg0; simp [g] at this; linarith
    have : gfun c v = c 0 * (1 + ‖v‖ ^ 2) := by
      simp only [gfun, e1, e2, Complex.sq_norm, Complex.normSq_apply]; ring
    rw [h0] at this
    have hc00 : c 0 = 0 := by
      have hD : (0 : ℝ) < 1 + ‖v‖ ^ 2 := by positivity
      nlinarith
    rw [hc00, zero_mul] at e1 e2
    rw [hc00, e1, e2] at hc1; norm_num at hc1
  have ht : Tendsto (fun δ : ℝ => v + (-(δ : ℂ)) * g) (𝓝[>] 0) (𝓝 v) := by
    have : Continuous fun δ : ℝ => v + (-(δ : ℂ)) * g := by fun_prop
    have h := this.tendsto 0
    simp only [Complex.ofReal_zero, neg_zero, zero_mul, add_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  obtain ⟨δ, h1, h2⟩ := ((ht.eventually (isOpen_interior.mem_nhds hv)).and
    (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] 0)).exists
  have hK := interior_subset h1 k
  rw [gfun_add, h0] at hK
  have hgn : ‖g‖ ^ 2 = g.re ^ 2 + g.im ^ 2 := by rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hu : ‖(-(δ : ℂ)) * g‖ ^ 2 = δ ^ 2 * ‖g‖ ^ 2 := by
    rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg (le_of_lt h2), mul_pow]
  rw [hu] at hK
  have hre : ((-(δ : ℂ)) * g).re = -δ * g.re := by simp
  have him : ((-(δ : ℂ)) * g).im = -δ * g.im := by simp
  rw [hre, him] at hK
  have hgre : g.re = c 1 - c 0 * v.re := rfl
  have hgim : g.im = c 2 - c 0 * v.im := rfl
  rw [← hgre, ← hgim] at hK
  have hδ : (0 : ℝ) < δ := h2
  have : 0 < δ * ‖g‖ ^ 2 := by positivity
  nlinarith [mul_nonneg hc0 (mul_nonneg (sq_nonneg δ) (sq_nonneg ‖g‖))]

end SphPolygon

end Model

/-! ### The double of the polygon -/

section Double

namespace SphPolygon

variable {s : ℕ} (t : SphPolygon s)

/-- **The double of the polygon**, as a space: the round sphere `𝕊²` (as for the triangle,
`GX.SphTriangle.TriDouble`). A point `(u, w)` (`u ∈ ℝ`, `|w| ≤ 1`) lies over the point
`R_0⁻¹ stereoInv (e_K⁻¹ w)` of the polygon (`SphPolygon.fold`), on the upper copy if `u ≥ 0`,
on the lower copy if `u ≤ 0`: the closed unit disc is the polygon (`e_K`), and `𝕊²` is the
double of the closed disc along its boundary circle `u = 0`. -/
def PolyDouble {s : ℕ} (_t : SphPolygon s) : Type := Sph2

instance : TopologicalSpace (PolyDouble t) := inferInstanceAs (TopologicalSpace Sph2)

instance : T2Space (PolyDouble t) := inferInstanceAs (T2Space Sph2)

instance : LocallyConnectedSpace (PolyDouble t) := inferInstanceAs (LocallyConnectedSpace Sph2)

instance : SecondCountableTopology (PolyDouble t) := inferInstanceAs (SecondCountableTopology Sph2)

instance : ConnectedSpace (PolyDouble t) := inferInstanceAs (ConnectedSpace Sph2)

/-- The underlying point of `𝕊²`. -/
def toSph2 (y : t.PolyDouble) : Sph2 := y

/-- A point of `𝕊²` as a point of the double. -/
def ofSph2 (y : Sph2) : t.PolyDouble := y

/-- The double is `𝕊²` as a space. -/
def homeoSph2 : t.PolyDouble ≃ₜ Sph2 := Homeomorph.refl Sph2

theorem continuous_toSph2 : Continuous t.toSph2 := continuous_id

theorem continuous_ofSph2 : Continuous t.ofSph2 := continuous_id

/-- The height `s` of a point of the double: `≥ 0` on the upper copy, `≤ 0` on the lower. -/
def height (y : t.PolyDouble) : ℝ := ((t.toSph2 y : Sph2) : Euc3).fst

/-- The disc coordinate `w` of a point of the double. -/
def disc (y : t.PolyDouble) : ℂ := ((t.toSph2 y : Sph2) : Euc3).snd

theorem height_sq_add (y : t.PolyDouble) : t.height y ^ 2 + ‖t.disc y‖ ^ 2 = 1 := by
  rw [height, disc, ← norm_polarSum_sq, norm_raySphere, one_pow]

theorem continuous_height : Continuous t.height :=
  (WithLp.prod_continuous_ofLp 2 ℝ ℂ |>.fst).comp continuous_subtype_val

theorem continuous_disc : Continuous t.disc :=
  (WithLp.prod_continuous_ofLp 2 ℝ ℂ |>.snd).comp continuous_subtype_val

/-- **The folding map of the double onto the polygon.** -/
def fold (y : t.PolyDouble) : Sph2 := (t.R t.o)⁻¹ • stereoInv (t.eK.symm (t.disc y))

theorem continuous_fold : Continuous t.fold :=
  (continuous_const_smul _).comp
    (continuous_stereoInv.comp (t.eK.symm.continuous.comp t.continuous_disc))

/-- The disc coordinate of a point of the sphere. -/
def wK (x : Sph2) : ℂ := t.eK (stereoFun (t.R t.o • x))

theorem eK_symm_disc_mem_K (y : t.PolyDouble) : t.eK.symm (t.disc y) ∈ t.K := by
  have h : t.disc y ∈ Metric.closedBall (0 : ℂ) 1 := by
    rw [mem_closedBall_zero_iff]
    have := t.height_sq_add y
    nlinarith [norm_nonneg (t.disc y), sq_nonneg (t.height y)]
  rw [← t.eK_image_K] at h
  obtain ⟨v, hv, hve⟩ := h
  rw [← hve, Homeomorph.symm_apply_apply]; exact hv

theorem fold_mem_T (y : t.PolyDouble) : t.fold y ∈ t.T :=
  (t.mem_T_iff _).2 (t.eK_symm_disc_mem_K y)

theorem fst_ne_of_mem_T {x : Sph2} (hx : x ∈ t.T) : ((t.R t.o • x : Sph2) : Euc3).fst ≠ -1 :=
  t.fst_ne_of_dot_nonneg t.o (t.ko t.o) (t.ko_ne_a t.o) (t.ko_ne_b t.o) (hx _)

theorem stereoInv_stereoFun_R {x : Sph2} (hx : x ∈ t.T) :
    stereoInv (stereoFun (t.R t.o • x)) = t.R t.o • x :=
  stereoInv_stereoFun _ (t.fst_ne_of_mem_T hx)

theorem stereoFun_mem_K {x : Sph2} (hx : x ∈ t.T) : stereoFun (t.R t.o • x) ∈ t.K := by
  rw [← t.mem_T_iff, t.stereoInv_stereoFun_R hx, inv_smul_smul]; exact hx

theorem wK_fold (y : t.PolyDouble) : t.wK (t.fold y) = t.disc y := by
  rw [wK, fold, smul_inv_smul, stereoFun_stereoInv, Homeomorph.apply_symm_apply]

theorem norm_wK_le {x : Sph2} (hx : x ∈ t.T) : ‖t.wK x‖ ≤ 1 := by
  have : t.wK x ∈ t.eK '' t.K := ⟨_, t.stereoFun_mem_K hx, rfl⟩
  rw [t.eK_image_K, mem_closedBall_zero_iff] at this
  exact this

/-- The pairings with the normals, in the chart at `v_0`. -/
theorem dot_vec_eq_gfun {x : Sph2} (hS : ((t.R t.o • x : Sph2) : Euc3).fst ≠ -1) (k : Fin s) :
    t.n k ⬝ᵥ vec x = gfun (t.cK k) (stereoFun (t.R t.o • x)) /
      (1 + ‖stereoFun (t.R t.o • x)‖ ^ 2) := by
  conv_lhs => rw [← inv_smul_smul (t.R t.o) x, ← stereoInv_stereoFun _ hS]
  rw [t.dot_vec_R_inv_stereoInv]; rfl

/-- **Interior points of the polygon have disc coordinate in the open disc.** -/
theorem norm_wK_lt {x : Sph2} (hx : x ∈ t.T) (hpos : ∀ k, 0 < t.n k ⬝ᵥ vec x) : ‖t.wK x‖ < 1 := by
  rw [wK, ← t.mem_interior_K_iff]
  refine t.gfun_pos_mem_interior_K fun k => ?_
  have h := hpos k
  rw [t.dot_vec_eq_gfun (t.fst_ne_of_mem_T hx)] at h
  have hD : (0 : ℝ) < 1 + ‖stereoFun (t.R t.o • x)‖ ^ 2 := by positivity
  exact (div_pos_iff_of_pos_right hD).1 h

/-- **Points outside the open polygon have disc coordinate outside the open disc.** -/
theorem one_le_norm_wK {x : Sph2} (hS : ((t.R t.o • x : Sph2) : Euc3).fst ≠ -1) {k : Fin s}
    (hk : t.n k ⬝ᵥ vec x ≤ 0) : 1 ≤ ‖t.wK x‖ := by
  rw [wK]
  by_contra hlt
  rw [not_le, ← t.mem_interior_K_iff] at hlt
  rw [t.dot_vec_eq_gfun hS] at hk
  have hD : (0 : ℝ) < 1 + ‖stereoFun (t.R t.o • x)‖ ^ 2 := by positivity
  have hg : gfun (t.cK k) (stereoFun (t.R t.o • x)) ≤ 0 := by
    by_contra h; rw [not_le] at h; exact absurd (div_pos h hD) (not_lt.2 hk)
  exact t.notMem_interior_K hg hlt

theorem norm_wK_eq_one_iff {x : Sph2} (hx : x ∈ t.T) : ‖t.wK x‖ = 1 ↔ ∃ k, t.n k ⬝ᵥ vec x = 0 := by
  constructor
  · intro h
    by_contra hne
    push Not at hne
    have := t.norm_wK_lt hx fun k => lt_of_le_of_ne (hx k) (hne k).symm
    linarith
  · rintro ⟨k, hk⟩
    exact le_antisymm (t.norm_wK_le hx) (t.one_le_norm_wK (t.fst_ne_of_mem_T hx) hk.le)

end SphPolygon

end Double

/-! ### The charts of the double at the vertices -/

section VertexCharts

namespace SphPolygon

variable {s : ℕ} (t : SphPolygon s)

/-- **The point of the polygon with polar coordinates `h` at `v_i`**: `h = r e^{iφ}` goes to the
point at stereographic radius `r` from `v_i` in the direction of angle `α_i |φ| / π` from the side
`e_{a i}`. -/
def xv (i : Fin s) (h : ℂ) : Sph2 := (t.R i)⁻¹ • stereoInv (polarFold (t.α i) h)

theorem continuous_xv (i : Fin s) : Continuous (t.xv i) :=
  (continuous_const_smul _).comp (continuous_stereoInv.comp continuous_polarFold)

theorem dot_xv (i k : Fin s) (h : ℂ) :
    t.n k ⬝ᵥ vec (t.xv i h) = gfun (t.A i *ᵥ t.n k) (polarFold (t.α i) h) / (1 + ‖h‖ ^ 2) := by
  rw [xv, t.dot_vec_R_inv_stereoInv, norm_polarFold]

theorem dot_xv_a (i : Fin s) (h : ℂ) :
    t.n (t.a i) ⬝ᵥ vec (t.xv i h) = 2 * (polarFold (t.α i) h).im / (1 + ‖h‖ ^ 2) := by
  rw [dot_xv, t.A_mulVec_n_a]; simp [gfun]

theorem dot_xv_b (i : Fin s) (h : ℂ) :
    t.n (t.b i) ⬝ᵥ vec (t.xv i h) = 2 * (Real.sin (t.α i) * (polarFold (t.α i) h).re -
      Real.cos (t.α i) * (polarFold (t.α i) h).im) / (1 + ‖h‖ ^ 2) := by
  rw [dot_xv, t.A_mulVec_n_b]; simp [gfun]; ring

theorem dot_xv_a_nonneg (i : Fin s) (h : ℂ) : 0 ≤ t.n (t.a i) ⬝ᵥ vec (t.xv i h) := by
  rw [dot_xv_a]
  have := (polarFold_mem_sector (t.α_pos i) (t.α_lt_pi i) h).1
  positivity

theorem dot_xv_b_nonneg (i : Fin s) (h : ℂ) : 0 ≤ t.n (t.b i) ⬝ᵥ vec (t.xv i h) := by
  rw [dot_xv_b]
  have := (polarFold_mem_sector (t.α_pos i) (t.α_lt_pi i) h).2
  positivity

theorem xv_mem_T_iff (i : Fin s) (h : ℂ) :
    t.xv i h ∈ t.T ↔ ∀ k, k ≠ t.a i → k ≠ t.b i → 0 ≤ t.n k ⬝ᵥ vec (t.xv i h) := by
  refine ⟨fun hx k _ _ => hx k, fun hx k => ?_⟩
  by_cases h1 : k = t.a i
  · rw [h1]; exact t.dot_xv_a_nonneg i h
  by_cases h2 : k = t.b i
  · rw [h2]; exact t.dot_xv_b_nonneg i h
  exact hx k h1 h2

theorem dot_xv_pos_of_im_ne_zero (i : Fin s) {h : ℂ} (hh : h.im ≠ 0) :
    0 < t.n (t.b i) ⬝ᵥ vec (t.xv i h) ∧ 0 < t.n (t.a i) ⬝ᵥ vec (t.xv i h) := by
  rw [dot_xv_b, dot_xv_a]
  have := polarFold_mem_sector_strict (t.α_pos i) (t.α_lt_pi i) hh
  exact ⟨by have := this.2; positivity, by have := this.1; positivity⟩

theorem im_eq_zero_of_dot_xv (i : Fin s) {h : ℂ}
    (hb : t.n (t.b i) ⬝ᵥ vec (t.xv i h) = 0 ∨ t.n (t.a i) ⬝ᵥ vec (t.xv i h) = 0) : h.im = 0 := by
  by_contra hh
  have := t.dot_xv_pos_of_im_ne_zero i hh
  rcases hb with hb | hb <;> linarith [this.1, this.2]

theorem dot_xv_boundary (i : Fin s) {h : ℂ} (hh : h.im = 0) :
    t.n (t.b i) ⬝ᵥ vec (t.xv i h) = 0 ∨ t.n (t.a i) ⬝ᵥ vec (t.xv i h) = 0 := by
  rw [dot_xv_b, dot_xv_a]
  rcases polarFold_boundary (α := t.α i) hh with h1 | h1
  · right; rw [h1]; simp
  · left; rw [h1]; simp

/-- The domain `V_i ⊆ ℂ` of the chart at `v_i`: the points away from the sides not through
`v_i`. -/
def Vv (i : Fin s) : Set ℂ := {h | ∀ k, k ≠ t.a i → k ≠ t.b i → 0 < t.n k ⬝ᵥ vec (t.xv i h)}

/-- Its compact closure `K_i`, the preimage of the polygon. -/
def Kv (i : Fin s) : Set ℂ := {h | ∀ k, k ≠ t.a i → k ≠ t.b i → 0 ≤ t.n k ⬝ᵥ vec (t.xv i h)}

theorem isOpen_Vv (i : Fin s) : IsOpen (t.Vv i) :=
  isOpen_setOf_forall_imp_imp_pos _ _ fun _ => (continuous_dot_vec _).comp (t.continuous_xv i)

theorem isClosed_Kv (i : Fin s) : IsClosed (t.Kv i) :=
  isClosed_setOf_forall_imp_imp_nonneg _ _ fun _ => (continuous_dot_vec _).comp (t.continuous_xv i)

theorem Vv_subset_Kv (i : Fin s) : t.Vv i ⊆ t.Kv i := fun _ hx k h1 h2 => (hx k h1 h2).le

theorem xv_mem_T {i : Fin s} {h : ℂ} (hh : h ∈ t.Kv i) : t.xv i h ∈ t.T :=
  (t.xv_mem_T_iff i h).2 hh

theorem isCompact_Kv (i : Fin s) : IsCompact (t.Kv i) := by
  refine Metric.isCompact_of_isClosed_isBounded (t.isClosed_Kv i) ?_
  set c := t.A i *ᵥ t.n (t.ko i)
  have ha : 0 < c 0 := t.A_mulVec_n_other_pos i _ (t.ko_ne_a i) (t.ko_ne_b i)
  have h1 : c ⬝ᵥ c = 1 := by rw [dot_mulVec_self (t.A_transpose_mul i), t.unit]
  refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := 3 / c 0)).subset fun h hh => ?_
  rw [Metric.mem_closedBall, dist_zero_right]
  have hh' : 0 ≤ gfun c (polarFold (t.α i) h) := by
    have := hh (t.ko i) (t.ko_ne_a i) (t.ko_ne_b i)
    rw [dot_xv] at this
    have hD : (0 : ℝ) < 1 + ‖h‖ ^ 2 := by positivity
    rwa [le_div_iff₀ hD, zero_mul] at this
  rw [← norm_polarFold (α := t.α i) h]
  exact norm_le_of_gfun_nonneg h1 ha hh'

theorem xv_zero (i : Fin s) : t.xv i 0 = (t.R i)⁻¹ • northPole := by
  rw [xv, polarFold_zero, stereoInv_zero]

theorem zero_mem_Vv (i : Fin s) : (0 : ℂ) ∈ t.Vv i := by
  intro k h1 h2
  rw [dot_xv, polarFold_zero]
  simp [gfun]
  exact t.A_mulVec_n_other_pos i k h1 h2

/-- The point of the double, as a vector of `ℝ ⊕ ℂ`. -/
def chartVec (i : Fin s) (h : ℂ) : Euc3 :=
  WithLp.toLp 2 (sheet h * √(1 - ‖t.wK (t.xv i h)‖ ^ 2), t.wK (t.xv i h))

/-- On the real axis of the chart, the point is on a side through `v_i`, so it is on the circle
`u = 0` of the double. -/
theorem sqrt_eq_zero_of_im_eq_zero (i : Fin s) {h : ℂ}
    (hS : ((t.R t.o • t.xv i h : Sph2) : Euc3).fst ≠ -1) (hh : h.im = 0) :
    √(1 - ‖t.wK (t.xv i h)‖ ^ 2) = 0 := by
  rw [Real.sqrt_eq_zero']
  rcases t.dot_xv_boundary i hh with hb | hb
  · have := t.one_le_norm_wK hS hb.le; nlinarith
  · have := t.one_le_norm_wK hS hb.le; nlinarith

theorem norm_chartVec (i : Fin s) {h : ℂ} (hh : h ∈ t.Kv i) : ‖t.chartVec i h‖ = 1 := by
  have hx := t.xv_mem_T hh
  have hle := t.norm_wK_le hx
  have hsq : ‖t.chartVec i h‖ ^ 2 = 1 := by
    rw [chartVec, norm_polarSum_sq]
    simp only [WithLp.fst, WithLp.snd]
    by_cases him : h.im = 0
    · rw [t.sqrt_eq_zero_of_im_eq_zero i (t.fst_ne_of_mem_T hx) him, mul_zero]
      have : ‖t.wK (t.xv i h)‖ = 1 := by
        have h0 := Real.sqrt_eq_zero'.1 (t.sqrt_eq_zero_of_im_eq_zero i (t.fst_ne_of_mem_T hx) him)
        nlinarith [norm_nonneg (t.wK (t.xv i h))]
      rw [this]; norm_num
    · rw [mul_pow, sheet_sq, one_mul, Real.sq_sqrt (by nlinarith [norm_nonneg (t.wK (t.xv i h))])]
      ring
  nlinarith [norm_nonneg (t.chartVec i h)]

/-- **The chart map at `v_i`**, `ℂ → PolyDouble`: `h` goes to the point over `x_i(h)`, on the
sheet of `h` (the upper copy of the polygon for `Im h ≥ 0`). -/
def chartMap (i : Fin s) (h : ℂ) : t.PolyDouble :=
  if hh : ‖t.chartVec i h‖ = 1 then t.ofSph2 ⟨t.chartVec i h, mem_sphere_zero_iff_norm.2 hh⟩
  else t.ofSph2 northPole

theorem coe_chartMap (i : Fin s) {h : ℂ} (hh : h ∈ t.Kv i) :
    ((t.toSph2 (t.chartMap i h) : Sph2) : Euc3) = t.chartVec i h := by
  rw [chartMap, dif_pos (t.norm_chartVec i hh)]; rfl

theorem disc_chartMap (i : Fin s) {h : ℂ} (hh : h ∈ t.Kv i) :
    t.disc (t.chartMap i h) = t.wK (t.xv i h) := by
  rw [disc, t.coe_chartMap i hh]; rfl

theorem height_chartMap (i : Fin s) {h : ℂ} (hh : h ∈ t.Kv i) :
    t.height (t.chartMap i h) = sheet h * √(1 - ‖t.wK (t.xv i h)‖ ^ 2) := by
  rw [height, t.coe_chartMap i hh]; rfl

theorem fold_chartMap (i : Fin s) {h : ℂ} (hh : h ∈ t.Kv i) :
    t.fold (t.chartMap i h) = t.xv i h := by
  have hx := t.xv_mem_T hh
  rw [fold, t.disc_chartMap i hh, wK, Homeomorph.symm_apply_apply, t.stereoInv_stereoFun_R hx,
    inv_smul_smul]

/-- The open set where the chart at `v_0` of the points `x_i(h)` is defined. -/
def Ov (i : Fin s) : Set ℂ := {h | ((t.R t.o • t.xv i h : Sph2) : Euc3).fst ≠ -1}

theorem isOpen_Ov (i : Fin s) : IsOpen (t.Ov i) :=
  isOpen_ne_fun (((WithLp.prod_continuous_ofLp 2 ℝ ℂ).fst.comp continuous_subtype_val).comp
    ((continuous_const_smul _).comp (t.continuous_xv i))) continuous_const

theorem Kv_subset_Ov (i : Fin s) : t.Kv i ⊆ t.Ov i := fun _ hh => t.fst_ne_of_mem_T (t.xv_mem_T hh)

theorem continuousOn_wK_xv (i : Fin s) : ContinuousOn (fun h => t.wK (t.xv i h)) (t.Ov i) := by
  refine t.eK.continuous.comp_continuousOn ?_
  refine continuousOn_stereoFun.comp
    ((continuous_const_smul _).comp (t.continuous_xv i)).continuousOn
    fun h hh => hh

theorem continuousOn_chartVec (i : Fin s) : ContinuousOn (t.chartVec i) (t.Ov i) := by
  set f : ℂ → ℝ := fun h => √(1 - ‖t.wK (t.xv i h)‖ ^ 2)
  have hf : ContinuousOn f (t.Ov i) :=
    (Real.continuous_sqrt.comp_continuousOn (continuousOn_const.sub
      ((continuous_norm.comp_continuousOn (t.continuousOn_wK_xv i)).pow 2)))
  have hfs : ContinuousOn (fun h => sheet h * f h) (t.Ov i) := by
    rw [continuousOn_iff_continuous_restrict]
    have heq : (t.Ov i).restrict (fun h => sheet h * f h) =
        fun h : t.Ov i => if (0 : ℝ) ≤ (h : ℂ).im then f h else -f h := by
      funext h; simp only [Set.restrict, sheet]; split_ifs <;> ring
    rw [heq]
    have hfr : Continuous fun h : t.Ov i => f h := continuousOn_iff_continuous_restrict.1 hf
    refine continuous_if_le continuous_const (Complex.continuous_im.comp continuous_subtype_val)
      hfr.continuousOn hfr.neg.continuousOn fun h heq => ?_
    have h0 : f h = 0 := t.sqrt_eq_zero_of_im_eq_zero i h.2 heq.symm
    show f h = -f h
    rw [h0, neg_zero]
  exact (WithLp.prod_continuous_toLp 2 ℝ ℂ).comp_continuousOn (hfs.prodMk (t.continuousOn_wK_xv i))

theorem continuousOn_chartMap (i : Fin s) : ContinuousOn (t.chartMap i) (t.Kv i) := by
  rw [continuousOn_iff_continuous_restrict]
  have heq : (t.Kv i).restrict (t.chartMap i) = fun h : t.Kv i =>
      t.ofSph2 ⟨t.chartVec i h, mem_sphere_zero_iff_norm.2 (t.norm_chartVec i h.2)⟩ := by
    funext h; simp only [Set.restrict, chartMap, dif_pos (t.norm_chartVec i h.2)]
  rw [heq]
  exact t.continuous_ofSph2.comp
    ((continuousOn_iff_continuous_restrict.1 ((t.continuousOn_chartVec i).mono
      (t.Kv_subset_Ov i))).subtype_mk _)

/-- A point of the double is determined by its height and its disc coordinate. -/
theorem ext_height_disc {y y' : t.PolyDouble} (h1 : t.height y = t.height y')
    (h2 : t.disc y = t.disc y') : y = y' := by
  have : ((t.toSph2 y : Sph2) : Euc3) = ((t.toSph2 y' : Sph2) : Euc3) := by
    have e : ∀ z : t.PolyDouble,
        ((t.toSph2 z : Sph2) : Euc3) = WithLp.toLp 2 (t.height z, t.disc z) :=
      fun z => rfl
    rw [e, e, h1, h2]
  exact Subtype.ext this

/-- **The chart map is injective on `V_i`.** -/
theorem injOn_chartMap (i : Fin s) : InjOn (t.chartMap i) (t.Vv i) := by
  intro h hh h' hh' he
  have hK := t.Vv_subset_Kv i hh
  have hK' := t.Vv_subset_Kv i hh'
  have hx : t.xv i h = t.xv i h' := by
    rw [← t.fold_chartMap i hK, ← t.fold_chartMap i hK', he]
  have hF : polarFold (t.α i) h = polarFold (t.α i) h' := by
    have := congrArg (fun y => stereoFun (t.R i • y)) hx
    simp only [xv, smul_inv_smul, stereoFun_stereoInv] at this
    exact this
  rcases polarFold_eq_iff (t.α_pos i) (t.α_lt_pi i) hF with rfl | hc
  · rfl
  · -- `h' = h̄`: then `h` is real
    have hheight := congrArg t.height he
    rw [t.height_chartMap i hK, t.height_chartMap i hK', ← hx] at hheight
    have him : h.im = 0 := by
      by_cases h0 : √(1 - ‖t.wK (t.xv i h)‖ ^ 2) = 0
      · have hT := t.xv_mem_T hK
        have h1 : ‖t.wK (t.xv i h)‖ = 1 := by
          have := Real.sqrt_eq_zero'.1 h0
          nlinarith [t.norm_wK_le hT, norm_nonneg (t.wK (t.xv i h))]
        obtain ⟨k, hk⟩ := (t.norm_wK_eq_one_iff hT).1 h1
        by_cases h1 : k = t.a i
        · rw [h1] at hk; exact t.im_eq_zero_of_dot_xv i (Or.inr hk)
        by_cases h2 : k = t.b i
        · rw [h2] at hk; exact t.im_eq_zero_of_dot_xv i (Or.inl hk)
        exact absurd hk (ne_of_gt (hh k h1 h2))
      · have hs : sheet h = sheet h' := mul_right_cancel₀ h0 hheight
        rw [hc] at hs
        unfold sheet at hs
        rw [Complex.conj_im] at hs
        split_ifs at hs with h1 h2 h2 <;> linarith
    rw [hc]; exact Complex.ext rfl (by simp [him])

/-- The image of `V_i`: the points of the double over the polygon minus the sides not through
`v_i`. -/
def Uv (i : Fin s) : Set t.PolyDouble :=
  {y | ∀ k, k ≠ t.a i → k ≠ t.b i → 0 < t.n k ⬝ᵥ vec (t.fold y)}

theorem isOpen_Uv (i : Fin s) : IsOpen (t.Uv i) :=
  isOpen_setOf_forall_imp_imp_pos _ _ fun _ => (continuous_dot_vec _).comp t.continuous_fold

/-- **The image of `V_i` under the chart map is `U_i`**: polar coordinates at `v_i`. -/
theorem chartMap_image_Vv (i : Fin s) : t.chartMap i '' t.Vv i = t.Uv i := by
  ext y
  constructor
  · rintro ⟨h, hh, rfl⟩
    intro k h1 h2
    rw [t.fold_chartMap i (t.Vv_subset_Kv i hh)]; exact hh k h1 h2
  · intro hy
    set x := t.fold y with hxdef
    have hxT : x ∈ t.T := t.fold_mem_T y
    have hS := t.fst_ne_of_dot_nonneg i (t.ko i) (t.ko_ne_a i) (t.ko_ne_b i) (hxT _)
    set z := stereoFun (t.R i • x) with hz
    have hxz : x = (t.R i)⁻¹ • stereoInv z := by rw [hz, stereoInv_stereoFun _ hS, inv_smul_smul]
    have hD : (0 : ℝ) < 1 + ‖z‖ ^ 2 := by positivity
    have hdot : ∀ k, t.n k ⬝ᵥ vec x = gfun (t.A i *ᵥ t.n k) z / (1 + ‖z‖ ^ 2) := fun k => by
      rw [hxz, t.dot_vec_R_inv_stereoInv]
    have hz2 : t.n (t.a i) ⬝ᵥ vec x = 2 * z.im / (1 + ‖z‖ ^ 2) := by
      rw [hdot, t.A_mulVec_n_a]; simp [gfun]
    have hz1 : t.n (t.b i) ⬝ᵥ vec x = 2 * (Real.sin (t.α i) * z.re - Real.cos (t.α i) * z.im) /
        (1 + ‖z‖ ^ 2) := by
      rw [hdot, t.A_mulVec_n_b]; simp [gfun]; ring
    have hzi : 0 ≤ z.im := by
      have := hxT (t.a i); rw [hz2] at this
      have := (div_nonneg_iff.1 this); rcases this with ⟨h1, -⟩ | ⟨-, h2⟩ <;> linarith
    have hzr : 0 ≤ Real.sin (t.α i) * z.re - Real.cos (t.α i) * z.im := by
      have := hxT (t.b i); rw [hz1] at this
      have := (div_nonneg_iff.1 this); rcases this with ⟨h1, -⟩ | ⟨-, h2⟩ <;> linarith
    -- the preimage `h`, on the sheet of `y`
    have hpre : ∃ h : ℂ, polarFold (t.α i) h = z ∧ (0 ≤ t.height y → 0 ≤ h.im) ∧
        (t.height y < 0 → h.im < 0) := by
      rcases le_or_gt 0 (t.height y) with hy0 | hy0
      · obtain ⟨h, h1, h2⟩ := exists_polarFold_eq (t.α_pos i) (t.α_lt_pi i) hzi hzr
        exact ⟨h, h1, fun _ => h2, fun h' => absurd hy0 (not_le.2 h')⟩
      · -- on the lower sheet the point is interior
        have hlt : ‖t.disc y‖ < 1 := by
          have := t.height_sq_add y
          nlinarith [norm_nonneg (t.disc y)]
        have hint : ∀ k, t.n k ⬝ᵥ vec x ≠ 0 := by
          intro k hk
          have := (t.norm_wK_eq_one_iff hxT).2 ⟨k, hk⟩
          rw [hxdef, t.wK_fold] at this
          linarith
        have hzi' : 0 < z.im := by
          have := lt_of_le_of_ne (hxT (t.a i)) (hint (t.a i)).symm
          rw [hz2] at this
          exact (div_pos_iff_of_pos_right hD).1 this |> fun h => by linarith
        have hzr' : 0 < Real.sin (t.α i) * z.re - Real.cos (t.α i) * z.im := by
          have := lt_of_le_of_ne (hxT (t.b i)) (hint (t.b i)).symm
          rw [hz1] at this
          have := (div_pos_iff_of_pos_right hD).1 this
          linarith
        obtain ⟨h, h1, h2⟩ := exists_polarFold_eq_neg (t.α_pos i) (t.α_lt_pi i) hzi' hzr'
        exact ⟨h, h1, fun h' => absurd h' (not_le.2 hy0), fun _ => h2⟩
    obtain ⟨h, hF, hup, hdown⟩ := hpre
    have hxv : t.xv i h = x := by rw [xv, hF, hxz]
    have hhV : h ∈ t.Vv i := fun k h1 h2 => by rw [hxv]; exact hy k h1 h2
    refine ⟨h, hhV, ?_⟩
    have hK := t.Vv_subset_Kv i hhV
    refine t.ext_height_disc ?_ ?_
    · rw [t.height_chartMap i hK, hxv, hxdef, t.wK_fold]
      have hsq : 1 - ‖t.disc y‖ ^ 2 = t.height y ^ 2 := by
        have := t.height_sq_add y; linarith
      rw [hsq, Real.sqrt_sq_eq_abs]
      rcases le_or_gt 0 (t.height y) with hy0 | hy0
      · rw [sheet, if_pos (hup hy0), one_mul, abs_of_nonneg hy0]
      · rw [sheet, if_neg (not_le.2 (hdown hy0)), abs_of_neg hy0]; ring
    · rw [t.disc_chartMap i hK, hxv, hxdef, t.wK_fold]

theorem chartMap_mem_Uv_of_mem_Kv {i : Fin s} {h : ℂ} (hh : h ∈ t.Kv i) :
    t.chartMap i h ∈ t.Uv i ↔ h ∈ t.Vv i := by
  show (∀ k, k ≠ t.a i → k ≠ t.b i → 0 < t.n k ⬝ᵥ vec (t.fold (t.chartMap i h))) ↔ _
  rw [t.fold_chartMap i hh]; rfl

theorem isOpenMap_chartMap (i : Fin s) : IsOpenMap ((t.Vv i).restrict (t.chartMap i)) :=
  isOpenMap_restrict_of_isCompact (t.isCompact_Kv i) (t.isOpen_Vv i) (t.Vv_subset_Kv i)
    (t.continuousOn_chartMap i) (t.injOn_chartMap i)
    (by rw [t.chartMap_image_Vv]; exact t.isOpen_Uv i)
    (fun h hK hV hU => by
      rw [t.chartMap_image_Vv] at hU
      exact hV ((t.chartMap_mem_Uv_of_mem_Kv hK).1 hU))

/-- **The chart of the double at `v_i`**, an open partial homeomorphism `ℂ → PolyDouble` with
source `V_i` and target `U_i` (`isOpenMap_restrict_of_isCompact`, through `K_i`). -/
def chartPH (i : Fin s) : OpenPartialHomeomorph ℂ t.PolyDouble :=
  OpenPartialHomeomorph.ofContinuousOpenRestrict ((t.injOn_chartMap i).toPartialEquiv _ _)
    ((t.continuousOn_chartMap i).mono (t.Vv_subset_Kv i)) (t.isOpenMap_chartMap i)
    (t.isOpen_Vv i)

theorem chartPH_source (i : Fin s) : (t.chartPH i).source = t.Vv i := rfl

theorem chartPH_target (i : Fin s) : (t.chartPH i).target = t.Uv i := by
  show t.chartMap i '' t.Vv i = _
  exact t.chartMap_image_Vv i

theorem chartPH_apply (i : Fin s) (h : ℂ) : t.chartPH i h = t.chartMap i h := rfl

end SphPolygon

end VertexCharts

/-! ### The cone charts and the comparison with the developing maps -/

section ConeCharts

namespace SphPolygon

variable {s : ℕ} (t : SphPolygon s)

/-- The cone angle `θ_i = 2α_i` at `v_i`. -/
def θc (i : Fin s) : ConeAngle := ⟨2 * t.α i, by have := t.α_pos i; positivity⟩

theorem θc_ne (i : Fin s) : (t.θc i).1 ≠ 2 * π := by
  have := t.α_lt_pi i
  show 2 * t.α i ≠ 2 * π
  intro h; linarith

/-- **The chart of the double at `v_i`, from the cone `C_{θ_i}`**: an open partial homeomorphism
`C_{θ_i} → PolyDouble`, the apex to `v_i`. -/
def Φ (i : Fin s) : OpenPartialHomeomorph (SphCone (t.θc i)) t.PolyDouble :=
  (SphCone.homeoComplex (t.θc i)).toOpenPartialHomeomorph.trans (t.chartPH i)

theorem Φ_apply (i : Fin s) (c : SphCone (t.θc i)) :
    t.Φ i c = t.chartMap i (SphCone.homeoComplex (t.θc i) c) := rfl

theorem Φ_symm_apply (i : Fin s) (y : t.PolyDouble) :
    (t.Φ i).symm y = (SphCone.homeoComplex (t.θc i)).symm ((t.chartPH i).symm y) := rfl

theorem Φ_source (i : Fin s) :
    (t.Φ i).source = SphCone.homeoComplex (t.θc i) ⁻¹' t.Vv i := by
  rw [Φ, OpenPartialHomeomorph.trans_source, Homeomorph.toOpenPartialHomeomorph_source,
    univ_inter]; rfl

theorem Φ_target (i : Fin s) : (t.Φ i).target = t.Uv i := by
  rw [Φ, OpenPartialHomeomorph.trans_target, Homeomorph.toOpenPartialHomeomorph_target,
    preimage_univ, inter_univ, chartPH_target]

/-- **Reading a cone chart through the developing map**: if, near the polar coordinates of the
point, the developing map of `C_{θ_i}` is `g • Ref` of the image in the double, then near the point
the chart `a ∘ Φ_i⁻¹` is a translate of `Ref`. -/
theorem eventually_chart_eq (i : Fin s) {a : OpenPartialHomeomorph (SphCone (t.θc i)) Sph2}
    (ha : a ∈ aeAtlas SO3 Sph2 (SphCone (t.θc i))) {y : t.PolyDouble}
    (hy : y ∈ ((t.Φ i).symm.trans a).source) (h0 : (t.chartPH i).symm y ≠ 0)
    {Ref : t.PolyDouble → Sph2} {g : SO3}
    (hform : ∀ᶠ q in 𝓝 (qOf _ h0), sphConeDev (t.θc i).1 (polarHalfPlaneLift q) =
      g • Ref (t.chartMap i (DInfty.cplx 1 (DInfty.posEmb q)))) :
    ∃ g' : SO3, ∀ᶠ y' in 𝓝 y, ((t.Φ i).symm.trans a) y' = g' • Ref y' := by
  set h₀ := (t.chartPH i).symm y with hh₀
  set q₀ := qOf h₀ h0
  rw [OpenPartialHomeomorph.trans_source] at hy
  have hyU : y ∈ (t.chartPH i).target := by
    have := hy.1; rw [OpenPartialHomeomorph.symm_source, Φ_target] at this
    rw [chartPH_target]; exact this
  have hh₀V : h₀ ∈ t.Vv i := (t.chartPH i).map_target hyU
  have hy₀ : t.chartPH i h₀ = y := (t.chartPH i).right_inv hyU
  have hc : SphCone.mk (t.θc i) (polarHalfPlaneLift q₀) = (t.Φ i).symm y := by
    apply (SphCone.homeoComplex (t.θc i)).injective
    rw [homeoComplex_mk_lift, cplx_qOf, Φ_symm_apply, Homeomorph.apply_symm_apply]
  have hca : SphCone.mk (t.θc i) (polarHalfPlaneLift q₀) ∈ a.source := by rw [hc]; exact hy.2
  obtain ⟨k, hk⟩ := sphCone_chart_dev (t.θc i) (y := polarHalfPlaneLift q₀) q₀.2 ha hca
  have hk' := (continuous_polarHalfPlaneLift.continuousAt (x := q₀)).eventually hk
  have hV : ∀ᶠ q in 𝓝 q₀, DInfty.cplx 1 (DInfty.posEmb q) ∈ t.Vv i :=
    continuous_cplx_posEmb.continuousAt.eventually ((t.isOpen_Vv i).mem_nhds (by
      show DInfty.cplx 1 (DInfty.posEmb q₀) ∈ t.Vv i; rw [cplx_qOf]; exact hh₀V))
  have hall : ∀ᶠ q in 𝓝 q₀, ((t.Φ i).symm.trans a) (t.chartMap i (DInfty.cplx 1 (DInfty.posEmb q)))
      = (k * g) • Ref (t.chartMap i (DInfty.cplx 1 (DInfty.posEmb q))) := by
    filter_upwards [hk', hV, hform] with q e1 e2 e3
    have hsym : (t.Φ i).symm (t.chartMap i (DInfty.cplx 1 (DInfty.posEmb q))) =
        SphCone.mk (t.θc i) (polarHalfPlaneLift q) := by
      rw [Φ_symm_apply, ← chartPH_apply, (t.chartPH i).left_inv e2]
      apply (SphCone.homeoComplex (t.θc i)).injective
      rw [Homeomorph.apply_symm_apply, homeoComplex_mk_lift]
    rw [OpenPartialHomeomorph.coe_trans, Function.comp_apply, hsym, mul_smul, ← e3]
    exact e1
  -- transport along the open map `q ↦ Φ_i (polar q)`
  obtain ⟨S, hS, hSall⟩ := hall.exists_mem
  refine ⟨k * g, Filter.mem_of_superset
    (x := (t.chartPH i) '' ((fun q : PolarHalfPlane => DInfty.cplx 1 (DInfty.posEmb q)) '' S ∩
      t.Vv i)) ?_ ?_⟩
  · have h1 : (fun q : PolarHalfPlane => DInfty.cplx 1 (DInfty.posEmb q)) '' S ∈ 𝓝 h₀ := by
      have := isOpenMap_cplx_posEmb.image_mem_nhds hS
      rwa [cplx_qOf] at this
    have := (t.chartPH i).image_mem_nhds hh₀V (inter_mem h1 ((t.isOpen_Vv i).mem_nhds hh₀V))
    rwa [hy₀] at this
  · rintro _ ⟨_, ⟨⟨q, hq, rfl⟩, -⟩, rfl⟩
    exact hSall q hq

/-- The reference map near a point of the side `e_k`: the fold on the upper copy, the fold
followed by the reflection `σ_k` on the lower copy. -/
def refEdge (k : Fin s) (y : t.PolyDouble) : Sph2 :=
  if 0 ≤ t.height y then t.fold y else t.σ k (t.fold y)

theorem height_chartMap_nonneg (i : Fin s) {h : ℂ} (hK : h ∈ t.Kv i) (him : 0 ≤ h.im) :
    0 ≤ t.height (t.chartMap i h) := by
  rw [t.height_chartMap i hK, sheet, if_pos him, one_mul]; exact Real.sqrt_nonneg _

theorem sqrt_pos_of_im_ne_zero (i : Fin s) {h : ℂ} (hV : h ∈ t.Vv i) (him : h.im ≠ 0) :
    0 < √(1 - ‖t.wK (t.xv i h)‖ ^ 2) := by
  have hK := t.Vv_subset_Kv i hV
  have hpos : ∀ k, 0 < t.n k ⬝ᵥ vec (t.xv i h) := by
    intro k
    have h12 := t.dot_xv_pos_of_im_ne_zero i him
    by_cases h1 : k = t.a i
    · rw [h1]; exact h12.2
    by_cases h2 : k = t.b i
    · rw [h2]; exact h12.1
    exact hV k h1 h2
  have := t.norm_wK_lt (t.xv_mem_T hK) hpos
  apply Real.sqrt_pos.2
  nlinarith [norm_nonneg (t.wK (t.xv i h))]

theorem height_chartMap_neg (i : Fin s) {h : ℂ} (hV : h ∈ t.Vv i) (him : h.im < 0) :
    t.height (t.chartMap i h) < 0 := by
  rw [t.height_chartMap i (t.Vv_subset_Kv i hV), sheet, if_neg (not_le.2 him)]
  have := t.sqrt_pos_of_im_ne_zero i hV him.ne
  linarith

theorem im_pos_of_height_pos (i : Fin s) {h : ℂ} (hK : h ∈ t.Kv i)
    (hy : 0 < t.height (t.chartMap i h)) : 0 < h.im := by
  rw [t.height_chartMap i hK] at hy
  have hS := t.fst_ne_of_mem_T (t.xv_mem_T hK)
  rcases lt_trichotomy h.im 0 with h1 | h1 | h1
  · rw [sheet, if_neg (not_le.2 h1)] at hy
    nlinarith [Real.sqrt_nonneg (1 - ‖t.wK (t.xv i h)‖ ^ 2)]
  · rw [t.sqrt_eq_zero_of_im_eq_zero i hS h1, mul_zero] at hy; exact absurd hy (lt_irrefl 0)
  · exact h1

theorem im_neg_of_height_neg (i : Fin s) {h : ℂ} (hK : h ∈ t.Kv i)
    (hy : t.height (t.chartMap i h) < 0) : h.im < 0 := by
  by_contra h1
  exact absurd (t.height_chartMap_nonneg i hK (not_lt.1 h1)) (not_le.2 hy)

/-- The point of `x_i` on the cover, through `polarFold_cover`. -/
theorem xv_cover (i : Fin s) (q : PolarHalfPlane) :
    t.xv i (DInfty.cplx 1 (DInfty.posEmb q)) = (t.R i)⁻¹ • stereoInv ((q.1.1 : ℂ) *
      Complex.exp ((foldAngle (t.α i) (DInfty.cplx 1 (DInfty.posEmb q)) : ℂ) * Complex.I)) := by
  rw [xv, polarFold_cover]

/-- **The upper sheet, read on the cover**: for `φ ∈ [0, 1/2]`, `D(r, φ) = R_i x_i`. -/
theorem dev_eq_up (i : Fin s) (q : PolarHalfPlane) (h1 : 0 ≤ q.1.2) (h2 : q.1.2 ≤ 1 / 2) :
    sphConeDev (t.θc i).1 (polarHalfPlaneLift q) =
      t.R i • t.xv i (DInfty.cplx 1 (DInfty.posEmb q)) := by
  rw [t.xv_cover, smul_inv_smul, sphConeDev_lift,
    foldAngle_cover_up (n := 0) q (by simpa using h1) (by simpa using h2)]
  congr 3
  push_cast; simp [θc]

/-- **The lower sheet, read on the cover**: for `φ ∈ [−1/2, 0]`, `D(r, φ) = ρ R_i x_i`. -/
theorem dev_eq_down (i : Fin s) (q : PolarHalfPlane) (h1 : -(1 / 2) ≤ q.1.2) (h2 : q.1.2 ≤ 0) :
    sphConeDev (t.θc i).1 (polarHalfPlaneLift q) =
      conjSph (t.R i • t.xv i (DInfty.cplx 1 (DInfty.posEmb q))) := by
  rw [t.xv_cover, smul_inv_smul, sphConeDev_lift, conjSph_stereoInv,
    foldAngle_cover_down (n := 0) q (by simpa using h1) (by simpa using h2)]
  congr 1
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_mul, Complex.conj_ofReal,
    Complex.conj_I]
  congr 2
  push_cast; simp [θc]

/-- **The lower sheet past the side `e_{b i}`, read on the cover**: for `φ ∈ [1/2, 1]`,
`D(r, φ) = R_i σ_{b i} x_i`. -/
theorem dev_eq_down_one (i : Fin s) (q : PolarHalfPlane) (h1 : 1 / 2 ≤ q.1.2) (h2 : q.1.2 ≤ 1) :
    sphConeDev (t.θc i).1 (polarHalfPlaneLift q) =
      t.R i • t.σ (t.b i) (t.xv i (DInfty.cplx 1 (DInfty.posEmb q))) := by
  rw [t.xv_cover, t.R_σ_b_stereoInv, sphConeDev_lift,
    foldAngle_cover_down (n := 1) q (by push_cast; linarith) (by push_cast; linarith)]
  congr 1
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_mul, Complex.conj_ofReal,
    Complex.conj_I, ← mul_assoc, mul_comm (Complex.exp _) (q.1.1 : ℂ), mul_assoc,
    ← Complex.exp_add]
  congr 2
  push_cast; simp [θc]; ring

theorem eventually_Vv (i : Fin s) {h₀ : ℂ} (h0 : h₀ ≠ 0) (hV : h₀ ∈ t.Vv i) :
    ∀ᶠ q in 𝓝 (qOf h₀ h0), DInfty.cplx 1 (DInfty.posEmb q) ∈ t.Vv i :=
  continuous_cplx_posEmb.continuousAt.eventually ((t.isOpen_Vv i).mem_nhds (by
    show DInfty.cplx 1 (DInfty.posEmb (qOf h₀ h0)) ∈ t.Vv i
    rw [cplx_qOf]; exact hV))

/-- The upper sheet: `D = R_i ∘ fold` near a point with `Im h₀ > 0`. -/
theorem hform_up (i : Fin s) {h₀ : ℂ} (h0 : h₀ ≠ 0) (hV : h₀ ∈ t.Vv i) (him : 0 < h₀.im) :
    ∀ᶠ q in 𝓝 (qOf h₀ h0), sphConeDev (t.θc i).1 (polarHalfPlaneLift q) =
      t.R i • t.fold (t.chartMap i (DInfty.cplx 1 (DInfty.posEmb q))) := by
  filter_upwards [t.eventually_Vv i h0 hV, eventually_snd_mem h0 (arg_div_mem_up him)] with q hq hφ
  rw [t.fold_chartMap i (t.Vv_subset_Kv i hq), t.dev_eq_up i q hφ.1.le hφ.2.le]

/-- The lower sheet: `D = (ρ R_i ρ) ∘ ρ ∘ fold` near a point with `Im h₀ < 0`. -/
theorem hform_down (i : Fin s) {h₀ : ℂ} (h0 : h₀ ≠ 0) (hV : h₀ ∈ t.Vv i) (him : h₀.im < 0) :
    ∀ᶠ q in 𝓝 (qOf h₀ h0), sphConeDev (t.θc i).1 (polarHalfPlaneLift q) =
      conjSO3 (t.R i) • conjSph (t.fold (t.chartMap i (DInfty.cplx 1 (DInfty.posEmb q)))) := by
  filter_upwards [t.eventually_Vv i h0 hV, eventually_snd_mem h0 (arg_div_mem_down him)]
    with q hq hφ
  rw [t.fold_chartMap i (t.Vv_subset_Kv i hq), t.dev_eq_down i q hφ.1.le hφ.2.le, conjSph_smul]

/-- The side `e_{a i}` (`φ = 0`): `D = R_i ∘ refEdge (a i)`. -/
theorem hform_edge_a (i : Fin s) {h₀ : ℂ} (h0 : h₀ ≠ 0) (hV : h₀ ∈ t.Vv i) (him : h₀.im = 0)
    (hre : 0 < h₀.re) :
    ∀ᶠ q in 𝓝 (qOf h₀ h0), sphConeDev (t.θc i).1 (polarHalfPlaneLift q) =
      t.R i • t.refEdge (t.a i) (t.chartMap i (DInfty.cplx 1 (DInfty.posEmb q))) := by
  have harg : Complex.arg h₀ / (2 * π) ∈ Ioo (-(1 / 2)) (1 / 2) := by
    rw [Complex.arg_eq_zero_iff.2 ⟨hre.le, him⟩, zero_div]; constructor <;> norm_num
  filter_upwards [t.eventually_Vv i h0 hV, eventually_snd_mem h0 harg] with q hq hφ
  have hK := t.Vv_subset_Kv i hq
  rcases le_or_gt 0 q.1.2 with h1 | h1
  · have hh : 0 ≤ t.height (t.chartMap i (DInfty.cplx 1 (DInfty.posEmb q))) := by
      refine t.height_chartMap_nonneg i hK ?_
      rw [im_cplx_one_posEmb]; exact mul_nonneg q.2.le (sin_nonneg_of_mem _ h1 hφ.2.le)
    rw [refEdge, if_pos hh, t.fold_chartMap i hK, t.dev_eq_up i q h1 hφ.2.le]
  · have hh : t.height (t.chartMap i (DInfty.cplx 1 (DInfty.posEmb q))) < 0 := by
      refine t.height_chartMap_neg i hq ?_
      rw [im_cplx_one_posEmb]; exact mul_neg_of_pos_of_neg q.2 (sin_neg_of_mem _ hφ.1 h1)
    rw [refEdge, if_neg (not_le.2 hh), t.fold_chartMap i hK, t.dev_eq_down i q hφ.1.le h1.le]
    conv_lhs => rw [← t.R_σ_a i (t.R i • t.xv i _), inv_smul_smul]

/-- The side `e_{b i}` (`φ = 1/2`): `D = R_i ∘ refEdge (b i)`. -/
theorem hform_edge_b (i : Fin s) {h₀ : ℂ} (h0 : h₀ ≠ 0) (hV : h₀ ∈ t.Vv i) (him : h₀.im = 0)
    (hre : h₀.re < 0) :
    ∀ᶠ q in 𝓝 (qOf h₀ h0), sphConeDev (t.θc i).1 (polarHalfPlaneLift q) =
      t.R i • t.refEdge (t.b i) (t.chartMap i (DInfty.cplx 1 (DInfty.posEmb q))) := by
  have harg : Complex.arg h₀ / (2 * π) ∈ Ioo 0 1 := by
    rw [Complex.arg_eq_pi_iff.2 ⟨hre, him⟩]
    have hπ := Real.pi_pos
    constructor
    · positivity
    · rw [div_lt_one (by positivity)]; linarith
  filter_upwards [t.eventually_Vv i h0 hV, eventually_snd_mem h0 harg] with q hq hφ
  have hK := t.Vv_subset_Kv i hq
  rcases le_or_gt q.1.2 (1 / 2) with h1 | h1
  · have hh : 0 ≤ t.height (t.chartMap i (DInfty.cplx 1 (DInfty.posEmb q))) := by
      refine t.height_chartMap_nonneg i hK ?_
      rw [im_cplx_one_posEmb]; exact mul_nonneg q.2.le (sin_nonneg_of_mem _ hφ.1.le h1)
    rw [refEdge, if_pos hh, t.fold_chartMap i hK, t.dev_eq_up i q hφ.1.le h1]
  · have hh : t.height (t.chartMap i (DInfty.cplx 1 (DInfty.posEmb q))) < 0 := by
      refine t.height_chartMap_neg i hq ?_
      rw [im_cplx_one_posEmb]; exact mul_neg_of_pos_of_neg q.2 (sin_neg_of_mem' _ h1 hφ.2)
    rw [refEdge, if_neg (not_le.2 hh), t.fold_chartMap i hK, t.dev_eq_down_one i q h1.le hφ.2.le]

/-- A chart of the cone family at `v_i` never contains `v_i`: the apex of `C_{θ_i}` is singular. -/
theorem chartPH_symm_ne_zero (i : Fin s) {a : OpenPartialHomeomorph (SphCone (t.θc i)) Sph2}
    (ha : a ∈ aeAtlas SO3 Sph2 (SphCone (t.θc i))) {y : t.PolyDouble}
    (hy : y ∈ ((t.Φ i).symm.trans a).source) : (t.chartPH i).symm y ≠ 0 := by
  intro h0
  rw [OpenPartialHomeomorph.trans_source] at hy
  have hap : (t.Φ i).symm y = SphCone.apex (t.θc i) := by
    rw [Φ_symm_apply, h0]
    apply (SphCone.homeoComplex (t.θc i)).injective
    rw [Homeomorph.apply_symm_apply, homeoComplex_apex]
  have hreg : SphCone.apex (t.θc i) ∈ Reg SO3 Sph2 (SphCone (t.θc i)) :=
    mem_support.2 ⟨a, ha, hap ▸ hy.2⟩
  exact (SphCone.apex_mem_sing_iff _).2 (t.θc_ne i) hreg

theorem mem_target_of_mem_source (i : Fin s) {a : OpenPartialHomeomorph (SphCone (t.θc i)) Sph2}
    {y : t.PolyDouble} (hy : y ∈ ((t.Φ i).symm.trans a).source) : y ∈ (t.chartPH i).target := by
  rw [OpenPartialHomeomorph.trans_source] at hy
  have := hy.1; rw [OpenPartialHomeomorph.symm_source, Φ_target] at this
  rw [chartPH_target]; exact this

/-- **On the upper copy, the cone charts are translates of the fold.** -/
theorem loc_up (i : Fin s) {a : OpenPartialHomeomorph (SphCone (t.θc i)) Sph2}
    (ha : a ∈ aeAtlas SO3 Sph2 (SphCone (t.θc i))) {y : t.PolyDouble}
    (hy : y ∈ ((t.Φ i).symm.trans a).source) (hpos : 0 < t.height y) :
    ∃ g : SO3, ∀ᶠ y' in 𝓝 y, ((t.Φ i).symm.trans a) y' = g • t.fold y' := by
  have h0 := t.chartPH_symm_ne_zero i ha hy
  have hyU := t.mem_target_of_mem_source i hy
  have hV : (t.chartPH i).symm y ∈ t.Vv i := (t.chartPH i).map_target hyU
  have hyc : t.chartMap i ((t.chartPH i).symm y) = y := (t.chartPH i).right_inv hyU
  have him := t.im_pos_of_height_pos i (t.Vv_subset_Kv i hV) (by rw [hyc]; exact hpos)
  exact t.eventually_chart_eq i ha hy h0 (t.hform_up i h0 hV him)

/-- **On the lower copy, the cone charts are translates of `ρ ∘ fold`.** -/
theorem loc_down (i : Fin s) {a : OpenPartialHomeomorph (SphCone (t.θc i)) Sph2}
    (ha : a ∈ aeAtlas SO3 Sph2 (SphCone (t.θc i))) {y : t.PolyDouble}
    (hy : y ∈ ((t.Φ i).symm.trans a).source) (hneg : t.height y < 0) :
    ∃ g : SO3, ∀ᶠ y' in 𝓝 y, ((t.Φ i).symm.trans a) y' = g • conjSph (t.fold y') := by
  have h0 := t.chartPH_symm_ne_zero i ha hy
  have hyU := t.mem_target_of_mem_source i hy
  have hV : (t.chartPH i).symm y ∈ t.Vv i := (t.chartPH i).map_target hyU
  have hyc : t.chartMap i ((t.chartPH i).symm y) = y := (t.chartPH i).right_inv hyU
  have him := t.im_neg_of_height_neg i (t.Vv_subset_Kv i hV) (by rw [hyc]; exact hneg)
  exact t.eventually_chart_eq i ha hy h0 (Ref := fun y => conjSph (t.fold y))
    (t.hform_down i h0 hV him)

/-- **Near a point of the side `e_k`, the cone charts are translates of `refEdge k`.** -/
theorem loc_edge (i : Fin s) {a : OpenPartialHomeomorph (SphCone (t.θc i)) Sph2}
    (ha : a ∈ aeAtlas SO3 Sph2 (SphCone (t.θc i))) {y : t.PolyDouble}
    (hy : y ∈ ((t.Φ i).symm.trans a).source) {k : Fin s} (hk : t.n k ⬝ᵥ vec (t.fold y) = 0) :
    ∃ g : SO3, ∀ᶠ y' in 𝓝 y, ((t.Φ i).symm.trans a) y' = g • t.refEdge k y' := by
  have h0 := t.chartPH_symm_ne_zero i ha hy
  have hyU := t.mem_target_of_mem_source i hy
  have hV : (t.chartPH i).symm y ∈ t.Vv i := (t.chartPH i).map_target hyU
  have hyc : t.chartMap i ((t.chartPH i).symm y) = y := (t.chartPH i).right_inv hyU
  set h₀ := (t.chartPH i).symm y
  have hfold : t.fold y = t.xv i h₀ := by rw [← hyc, t.fold_chartMap i (t.Vv_subset_Kv i hV)]
  rw [hfold] at hk
  have hD : (0 : ℝ) < 1 + ‖h₀‖ ^ 2 := by positivity
  by_cases hka : k = t.a i
  · subst hka
    rw [dot_xv_a, div_eq_zero_iff, mul_eq_zero] at hk
    have hF : (polarFold (t.α i) h₀).im = 0 := by
      rcases hk with (hk | hk) | hk
      · norm_num at hk
      · exact hk
      · linarith
    obtain ⟨him, hre⟩ := re_pos_of_polarFold_im (t.α_pos i) (t.α_lt_pi i) h0 hF
    exact t.eventually_chart_eq i ha hy h0 (t.hform_edge_a i h0 hV him hre)
  by_cases hkb : k = t.b i
  · subst hkb
    rw [dot_xv_b, div_eq_zero_iff, mul_eq_zero] at hk
    have hF : Real.sin (t.α i) * (polarFold (t.α i) h₀).re -
        Real.cos (t.α i) * (polarFold (t.α i) h₀).im = 0 := by
      rcases hk with (hk | hk) | hk
      · norm_num at hk
      · exact hk
      · linarith
    obtain ⟨him, hre⟩ := re_neg_of_polarFold_sector (t.α_pos i) (t.α_lt_pi i) h0 hF
    exact t.eventually_chart_eq i ha hy h0 (t.hform_edge_b i h0 hV him hre)
  exact absurd hk (ne_of_gt (hV k hka hkb))

/-- On the circle `u = 0` of the double, the fold lies on a side. -/
theorem exists_side_of_height_eq_zero {y : t.PolyDouble} (hy : t.height y = 0) :
    ∃ k, t.n k ⬝ᵥ vec (t.fold y) = 0 := by
  have h1 : ‖t.disc y‖ = 1 := by
    have := t.height_sq_add y
    rw [hy] at this
    nlinarith [norm_nonneg (t.disc y)]
  rw [← t.wK_fold] at h1
  exact (t.norm_wK_eq_one_iff (t.fold_mem_T y)).1 h1

/-- The cone charts at `v_i`. -/
def coneAtlas (i : Fin s) : Set (OpenPartialHomeomorph t.PolyDouble Sph2) :=
  (fun a => (t.Φ i).symm.trans a) '' aeAtlas SO3 Sph2 (SphCone (t.θc i))

/-- **The generating atlas of the double**: the charts of the `s` cones `C_{θ_i}`, read through
the charts `Φ_i`. -/
def atlas : Set (OpenPartialHomeomorph t.PolyDouble Sph2) := ⋃ i, t.coneAtlas i

/-- **The generating atlas is a `(SO(3), 𝕊²)`-atlas**: near every common point, two cone charts are
translates of the same reference map (`fold` on the upper copy, `ρ ∘ fold` on the lower copy,
`refEdge k` on the side `e_k`). -/
theorem isGXAtlas_atlas : IsGXAtlas SO3 t.atlas := by
  refine isGXAtlas_of_eventually ?_
  rintro e he e' he' y ⟨hye, hye'⟩
  obtain ⟨i, a, ha, rfl⟩ := mem_iUnion.1 he
  obtain ⟨j, b, hb, rfl⟩ := mem_iUnion.1 he'
  have key : ∀ {Ref : t.PolyDouble → Sph2},
      (∃ g : SO3, ∀ᶠ y' in 𝓝 y, ((t.Φ i).symm.trans a) y' = g • Ref y') →
      (∃ g : SO3, ∀ᶠ y' in 𝓝 y, ((t.Φ j).symm.trans b) y' = g • Ref y') →
      ∃ g : SO3, ∀ᶠ y' in 𝓝 y, ((t.Φ j).symm.trans b) y' = g • ((t.Φ i).symm.trans a) y' := by
    rintro Ref ⟨g₁, h₁⟩ ⟨g₂, h₂⟩
    refine ⟨g₂ * g₁⁻¹, ?_⟩
    filter_upwards [h₁, h₂] with y' e1 e2
    rw [e2, e1, mul_smul, inv_smul_smul]
  rcases lt_trichotomy 0 (t.height y) with hp | h0 | hn
  · exact key (t.loc_up i ha hye hp) (t.loc_up j hb hye' hp)
  · obtain ⟨k, hk⟩ := t.exists_side_of_height_eq_zero h0.symm
    exact key (t.loc_edge i ha hye hk) (t.loc_edge j hb hye' hk)
  · exact key (Ref := fun y => conjSph (t.fold y)) (t.loc_down i ha hye hn)
      (t.loc_down j hb hye' hn)

end SphPolygon

end ConeCharts

/-! ### The singular `(SO(3), 𝕊²)`-structure of the double, and its cone points -/

section Structure

namespace SphPolygon

variable {s : ℕ} (t : SphPolygon s)

/-- **The vertex `v_i` of the double**, the image of the apex of `C_{θ_i}`. -/
def vertex (i : Fin s) : t.PolyDouble := t.chartMap i 0

theorem fold_vertex (i : Fin s) : t.fold (t.vertex i) = t.xv i 0 :=
  t.fold_chartMap i (t.Vv_subset_Kv i (t.zero_mem_Vv i))

theorem vertex_injective : Injective t.vertex := by
  intro i j hij
  by_contra hne
  have h1 : ∀ k, k ≠ t.a i → k ≠ t.b i → 0 < t.n k ⬝ᵥ vec (t.fold (t.vertex i)) := by
    rw [t.fold_vertex]; exact t.zero_mem_Vv i
  rw [hij, t.fold_vertex] at h1
  have ha : t.n (t.a j) ⬝ᵥ vec (t.xv j 0) = 0 := by rw [dot_xv_a, polarFold_zero]; simp
  have hb : t.n (t.b j) ⬝ᵥ vec (t.xv j 0) = 0 := by rw [dot_xv_b, polarFold_zero]; simp
  rcases t.vertex_sep i j hne with ⟨h2, h3⟩ | ⟨h2, h3⟩
  · exact absurd ha (h1 _ h2 h3).ne'
  · exact absurd hb (h1 _ h2 h3).ne'

theorem vertex_eq_Φ (i : Fin s) : t.vertex i = t.Φ i (SphCone.apex (t.θc i)) := by
  rw [Φ_apply, homeoComplex_apex]; rfl

theorem apex_mem_Φ_source (i : Fin s) : SphCone.apex (t.θc i) ∈ (t.Φ i).source := by
  rw [Φ_source, mem_preimage, homeoComplex_apex]; exact t.zero_mem_Vv i

/-- **Off the vertices, the double is covered by the cone charts.** -/
theorem mem_support_atlas {y : t.PolyDouble} (hy : ∀ i, y ≠ t.vertex i) : y ∈ support t.atlas := by
  have hT := t.fold_mem_T y
  obtain ⟨i, hi⟩ := t.cover (vec (t.fold y)) (vec_dot_self _) hT
  have hyU : y ∈ (t.chartPH i).target := by rw [chartPH_target]; exact hi
  set h := (t.chartPH i).symm y
  have hV : h ∈ t.Vv i := (t.chartPH i).map_target hyU
  have hyc : t.chartMap i h = y := (t.chartPH i).right_inv hyU
  have h0 : h ≠ 0 := fun e => hy i (by rw [← hyc, e]; rfl)
  set c := (SphCone.homeoComplex (t.θc i)).symm h
  have hc : c ≠ SphCone.apex (t.θc i) := fun e => h0 (by
    have := congrArg (SphCone.homeoComplex (t.θc i)) e
    rwa [Homeomorph.apply_symm_apply, homeoComplex_apex] at this)
  have hcreg : c ∈ Reg SO3 Sph2 (SphCone (t.θc i)) := by
    by_contra hcs
    have : c ∈ Sing SO3 Sph2 (SphCone (t.θc i)) := hcs
    rw [SphCone.sing_eq _ (t.θc_ne i)] at this
    exact hc this
  obtain ⟨a, ha, hca⟩ := mem_support.1 hcreg
  refine mem_support.2 ⟨_, mem_iUnion.2 ⟨i, a, ha, rfl⟩, ?_⟩
  rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source, Φ_target]
  exact ⟨hi, hca⟩

/-- **The generating atlas is an a.e. `(SO(3), 𝕊²)`-atlas**: its support contains the complement
of the `s` vertices, portly. -/
theorem isAEAtlas_atlas : IsAEAtlas SO3 t.atlas := by
  refine ⟨t.isGXAtlas_atlas, ?_⟩
  have hP : IsPortly (⋂ i, {t.vertex i}ᶜ : Set t.PolyDouble) :=
    isPortly_iInter fun i => isPortly_compl_singleton_sph2 (t.toSph2 (t.vertex i))
  refine hP.mono (fun y hy => t.mem_support_atlas fun i => ?_) (isOpen_support _)
  exact mem_iInter.1 hy i

/-- **The singular `(SO(3), 𝕊²)`-structure of the doubled polygon**: the maximal a.e. atlas
generated by the cone charts (`cor:maximal_atlas`). -/
instance singularGXStructure : SingularGXStructure SO3 Sph2 t.PolyDouble :=
  ⟨maximalAEAtlas SO3 t.atlas, t.isAEAtlas_atlas.isMaximalAEAtlas_maximalAEAtlas⟩

theorem aeAtlas_eq : aeAtlas SO3 Sph2 t.PolyDouble = maximalAEAtlas SO3 t.atlas := rfl

/-- **The singular points of the double are among its vertices.** -/
theorem sing_subset_range_vertex : Sing SO3 Sph2 t.PolyDouble ⊆ range t.vertex := by
  intro y hy
  by_contra hr
  have hy' : ∀ i, y ≠ t.vertex i := fun i e => hr ⟨i, e.symm⟩
  exact hy (support_mono t.isAEAtlas_atlas.subset_maximalAEAtlas (t.mem_support_atlas hy'))

/-- The domain of `Φ_i`, an open subset of `C_{θ_i}`. -/
def ΦV (i : Fin s) : Opens (SphCone (t.θc i)) := ⟨(t.Φ i).source, (t.Φ i).open_source⟩

instance (i : Fin s) : Nonempty (t.ΦV i) := ⟨⟨_, t.apex_mem_Φ_source i⟩⟩

/-- **`Φ_i` is an a.e. `(SO(3), 𝕊²)`-morphism** on its domain: the charts of the domain, pushed to
`C_{θ_i}` (`symm_trans_mem_aeAtlas_of_opens`), are read through `Φ_i` as charts of the generating
atlas. -/
theorem isAEMorphism_Φ (i : Fin s) :
    IsAEMorphism SO3 Sph2 (fun v : t.ΦV i => t.Φ i (v : SphCone (t.θc i))) := by
  set V := t.ΦV i
  haveI : Nonempty V := ⟨⟨_, t.apex_mem_Φ_source i⟩⟩
  set ι := V.isOpen.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph Subtype.val
  have hιs : ι.source = univ := IsOpenEmbedding.toOpenPartialHomeomorph_source _ _
  have hB := isMaximalAEAtlas_aeAtlas SO3 Sph2 V
  have hcont : Continuous fun v : V => t.Φ i (v : SphCone (t.θc i)) :=
    (t.Φ i).continuousOn.comp_continuous continuous_subtype_val fun v => v.2
  have h := isAEMorphismOf_maximalAEAtlas_of_forall hB.1 t.isAEAtlas_atlas hcont fun b hb => by
    refine ⟨(t.Φ i).symm.trans (ι.symm.trans b),
      mem_iUnion.2 ⟨i, _, symm_trans_mem_aeAtlas_of_opens V hb, rfl⟩, fun v hv => ?_,
      fun v hv => ?_⟩
    · have hl : (t.Φ i).symm (t.Φ i (v : SphCone (t.θc i))) = v := (t.Φ i).left_inv v.2
      have hι : ι.symm (v : SphCone (t.θc i)) = v := ι.left_inv (by rw [hιs]; exact mem_univ _)
      rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source]
      refine ⟨(t.Φ i).map_source v.2, ?_⟩
      rw [mem_preimage, hl, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source]
      refine ⟨?_, ?_⟩
      · rw [IsOpenEmbedding.toOpenPartialHomeomorph_target]; exact mem_range_self _
      · rw [mem_preimage, hι]; exact hv
    · have hl : (t.Φ i).symm (t.Φ i (v : SphCone (t.θc i))) = v := (t.Φ i).left_inv v.2
      have hι : ι.symm (v : SphCone (t.θc i)) = v := ι.left_inv (by rw [hιs]; exact mem_univ _)
      simp only [OpenPartialHomeomorph.coe_trans, Function.comp_apply]
      rw [hl, hι]
  rwa [hB.maximalAEAtlas_eq] at h

theorem starConvex_Vv (i : Fin s) : StarConvex ℝ 0 (t.Vv i) := by
  intro h hh a b ha hb hab
  rw [smul_zero, zero_add]
  intro k h1 h2
  have hh' : 0 < t.n k ⬝ᵥ vec (t.xv i h) := hh k h1 h2
  rw [dot_xv] at hh' ⊢
  have hD : (0 : ℝ) < 1 + ‖b • h‖ ^ 2 := by positivity
  have hD' : (0 : ℝ) < 1 + ‖h‖ ^ 2 := by positivity
  apply div_pos _ hD
  have hg := (div_pos_iff_of_pos_right hD').1 hh'
  rw [Complex.real_smul, polarFold_ofReal_mul hb]
  set c := t.A i *ᵥ t.n k
  set v := polarFold (t.α i) h
  have hc0 : 0 < c 0 := t.A_mulVec_n_other_pos i k h1 h2
  have key : gfun c ((b : ℂ) * v) = b * gfun c v + c 0 * (1 - b) + c 0 * b * (1 - b) * ‖v‖ ^ 2 := by
    simp only [gfun, norm_mul, Complex.norm_real, Real.norm_of_nonneg hb, Complex.re_ofReal_mul,
      Complex.im_ofReal_mul]
    ring
  rw [key]
  have hb1 : b ≤ 1 := by linarith
  rcases hb.lt_or_eq with hb0 | hb0
  · have := mul_pos hb0 hg
    have := mul_nonneg (mul_nonneg hc0.le hb0.le) (mul_nonneg (sub_nonneg.2 hb1) (sq_nonneg ‖v‖))
    nlinarith [mul_nonneg hc0.le (sub_nonneg.2 hb1)]
  · subst hb0; simp; exact hc0

theorem isConnected_ΦV (i : Fin s) : IsConnected ((t.ΦV i : Set (SphCone (t.θc i)))) := by
  have hc : IsConnected (t.Vv i) :=
    ((t.starConvex_Vv i).isPathConnected (t.zero_mem_Vv i)).isConnected
  have : ((t.ΦV i : Set (SphCone (t.θc i)))) = (SphCone.homeoComplex (t.θc i)).symm '' t.Vv i := by
    show (t.Φ i).source = _
    rw [Φ_source, Homeomorph.image_symm]
  rw [this]
  exact hc.image _ (SphCone.homeoComplex (t.θc i)).symm.continuous.continuousOn

/-- **The `X_{θ_i}`-chart of the double at `v_i`** (`def:atlas`): `Φ_i⁻¹` from the image of `Φ_i`
onto its domain, a connected open neighbourhood of the apex of `C_{θ_i}`. -/
def coneXAChart (i : Fin s) : XAChart SO3 Sph2 SphCone sphConeS (t.θc i) (t.vertex i) where
  U := ⟨(t.Φ i).target, (t.Φ i).open_target⟩
  V := t.ΦV i
  φ := (t.Φ i).toHomeomorphSourceTarget.symm
  mem := by rw [t.vertex_eq_Φ]; exact (t.Φ i).map_source (t.apex_mem_Φ_source i)
  isConnected_V := t.isConnected_ΦV i
  isAEMorphism := by
    refine IsAEMorphism.symm_of_homeomorph ?_
    refine isAEMorphism_of_val_comp ⟨(t.Φ i).target, (t.Φ i).open_target⟩ ?_
    exact t.isAEMorphism_Φ i
  mem_S := by
    show (t.Φ i).symm (t.vertex i) ∈ sphConeS (t.θc i)
    rw [t.vertex_eq_Φ, (t.Φ i).left_inv (t.apex_mem_Φ_source i)]
    exact mem_singleton _

/-- **The vertex `v_i` is a cone point of angle `θ_i = 2α_i`.** -/
theorem isConePoint_vertex (i : Fin s) : IsConePoint (t.θc i) (t.vertex i) := ⟨t.coneXAChart i⟩

/-- **The doubled polygon is a cone sphere with the `s` cone points `v_i` of angles `2α_i`.** -/
theorem isConeSphere : IsConeSphere t.PolyDouble (fun i => 2 * t.α i) t.vertex where
  homeomorphic := ⟨t.homeoSph2⟩
  injective := t.vertex_injective
  pos i := by have := t.α_pos i; positivity
  isConePoint i := t.isConePoint_vertex i
  sing_subset := t.sing_subset_range_vertex

end SphPolygon

end Structure

/-! ### Troyanov's theorem for angles all below `2π` -/

section Main

/-- **The double of a convex spherical polygon is a cone sphere** with the cone angles `2α_i`
(`GX.SphPolygon.isConeSphere`), in the shape of `GX.TroyanovTheorem`'s conclusion. -/
theorem SphPolygon.exists_isConeSphere {s : ℕ} (t : SphPolygon s) :
    ∃ (M : Type) (_ : TopologicalSpace M) (_ : SingularGXStructure SO3 Sph2 M) (p : Fin s → M),
      IsConeSphere M (fun i => 2 * t.α i) p :=
  ⟨t.PolyDouble, inferInstance, inferInstance, t.vertex, t.isConeSphere⟩

/-- **Spherical cone spheres with prescribed angles below `2π`, under the subcritical
condition.** -/
theorem exists_isConeSphere_of_subcritical {s : ℕ} (hs : 3 ≤ s) (θ : Fin s → ℝ)
    (hpos : ∀ i, 0 < θ i) (hlt : ∀ i, θ i < 2 * π) (hχ : 0 < ∑ i, (θ i - 2 * π) + 4 * π)
    (hχθ : ∀ j, ∑ i, (θ i - 2 * π) + 4 * π < 2 * θ j) :
    ∃ (M : Type) (_ : TopologicalSpace M) (_ : SingularGXStructure SO3 Sph2 M) (p : Fin s → M),
      IsConeSphere M θ p := by
  have hS : ∑ i, (θ i - 2 * π) = -2 * ∑ i, (π - θ i / 2) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  obtain ⟨t, ht⟩ := exists_sphPolygon hs (fun i => θ i / 2) (fun i => by have := hpos i; positivity)
    (fun i => by have := hlt i; linarith) (by rw [hS] at hχ; linarith)
    (fun k => by have := hχθ k; rw [hS] at this; linarith)
  obtain ⟨M, _, _, p, hp⟩ := t.exists_isConeSphere
  have hθ : (fun i => 2 * t.α i) = θ := by funext i; rw [ht]; ring
  exact ⟨M, _, _, p, hθ ▸ hp⟩

/-- **Troyanov's theorem for angles all below `2π`.** -/
theorem troyanovTheorem_of_lt_two_pi {s : ℕ} (θ : Fin s → ℝ) (hθ : TroyanovAngleCondition θ)
    (hlt : ∀ i, θ i < 2 * π) :
    ∃ (M : Type) (_ : TopologicalSpace M) (_ : SingularGXStructure SO3 Sph2 M) (p : Fin s → M),
      IsConeSphere M θ p :=
  exists_isConeSphere_of_subcritical hθ.1 θ hθ.pos hlt hθ.2.1
    fun j => (hθ.2.2.2 j).trans_lt (by linarith [hθ.pos j])

/-- **The target's statement**: Troyanov's theorem for `s ≥ 4` angles all in `]0, 2π[`. -/
theorem troyanovTheorem_four_le_of_lt_two_pi {s : ℕ} (_hs : 4 ≤ s) (θ : Fin s → ℝ)
    (hθ : TroyanovAngleCondition θ) (hlt : ∀ i, θ i < 2 * π) :
    ∃ (M : Type) (_ : TopologicalSpace M) (_ : SingularGXStructure SO3 Sph2 M) (p : Fin s → M),
      IsConeSphere M θ p :=
  troyanovTheorem_of_lt_two_pi θ hθ hlt

/-- **Troyanov's theorem for angles all at most `2π`.** -/
theorem troyanovTheorem_of_le_two_pi :
    ∀ {s : ℕ} (θ : Fin s → ℝ), TroyanovAngleCondition θ → (∀ i, θ i ≤ 2 * π) →
    ∃ (M : Type) (_ : TopologicalSpace M) (_ : SingularGXStructure SO3 Sph2 M) (p : Fin s → M),
      IsConeSphere M θ p := by
  intro s
  induction s with
  | zero => intro θ hθ; exact absurd hθ.1 (by norm_num)
  | succ n ih =>
    intro θ hθ hle
    by_cases hne : ∀ i, θ i ≠ 2 * π
    · exact troyanovTheorem_of_lt_two_pi θ hθ fun i => lt_of_le_of_ne (hle i) (hne i)
    obtain ⟨k, hk⟩ : ∃ k, θ k = 2 * π := by
      by_contra hc
      exact hne fun i hi => hc ⟨i, hi⟩
    obtain ⟨M, _, _, p, hp⟩ := ih (k.removeNth θ) (hθ.removeNth hk) fun i => hle _
    obtain ⟨q, hq⟩ := hp.exists_notMem_range
    exact ⟨M, _, _, _, hp.insertNth hk hq⟩

/-- **What remains of Troyanov's theorem**: its case `s ≥ 4`, every angle `≠ 2π`, some angle
`> 2π`. -/
theorem troyanovTheorem_of_exists_gt_two_pi
    (h : ∀ {s : ℕ}, 4 ≤ s → ∀ θ : Fin s → ℝ, TroyanovAngleCondition θ → (∀ i, θ i ≠ 2 * π) →
      (∃ i, 2 * π < θ i) →
      ∃ (M : Type) (_ : TopologicalSpace M) (_ : SingularGXStructure SO3 Sph2 M) (p : Fin s → M),
        IsConeSphere M θ p) :
    ∀ {s : ℕ} (θ : Fin s → ℝ), TroyanovAngleCondition θ →
      ∃ (M : Type) (_ : TopologicalSpace M) (_ : SingularGXStructure SO3 Sph2 M) (p : Fin s → M),
        IsConeSphere M θ p :=
  troyanovTheorem_of_four_le_of_ne_two_pi fun {s} hs θ hθ hne => by
    by_cases hgt : ∃ i, 2 * π < θ i
    · exact h hs θ hθ hne hgt
    · push Not at hgt
      exact troyanovTheorem_of_le_two_pi θ hθ hgt

/-- **The case of this module is not vacuous, and meets the cex's genericity**: `s = 4` pairwise
distinct angles `(6π/5, 5π/4, 4π/3, 7π/5)`, all below `2π`, satisfy the condition of l.1930
(`∑ (θ_i − 2π) + 4π = 71π/60 ≤ 6π/5`), and a cone sphere with these angles exists. -/
theorem troyanovAngleCondition_four_lt_two_pi :
    TroyanovAngleCondition ![6 * π / 5, 5 * π / 4, 4 * π / 3, 7 * π / 5] ∧
      Pairwise (fun i j => ![6 * π / 5, 5 * π / 4, 4 * π / 3, 7 * π / 5] i ≠
        ![6 * π / 5, 5 * π / 4, 4 * π / 3, 7 * π / 5] j) ∧
      (∀ i, ![6 * π / 5, 5 * π / 4, 4 * π / 3, 7 * π / 5] i < 2 * π) ∧
      ∃ (M : Type) (_ : TopologicalSpace M) (_ : SingularGXStructure SO3 Sph2 M) (p : Fin 4 → M),
        IsConeSphere M ![6 * π / 5, 5 * π / 4, 4 * π / 3, 7 * π / 5] p := by
  have hπ := Real.pi_pos
  have hc : TroyanovAngleCondition ![6 * π / 5, 5 * π / 4, 4 * π / 3, 7 * π / 5] := by
    refine ⟨by norm_num, ?_, ?_, fun j => ?_⟩
    · simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
      linarith
    · simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
      linarith
    · simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
      fin_cases j <;> simp <;> linarith
  have hlt : ∀ i, ![6 * π / 5, 5 * π / 4, 4 * π / 3, 7 * π / 5] i < 2 * π := fun i => by
    fin_cases i <;> simp <;> linarith
  refine ⟨hc, fun i j hij => ?_, hlt, troyanovTheorem_of_lt_two_pi _ hc hlt⟩
  fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> intro h <;> linarith

/-- **For `s = 4` too, the condition of l.1930 is sufficient, not necessary**: the double of the
spherical quadrilateral with angles `(3π/4, 3π/4, 3π/4, 3π/10)` is a cone sphere with angles
`(3π/2, 3π/2, 3π/2, 3π/5)`, which violate the printed bound (`∑ (θ_i − 2π) + 4π = 11π/10 >
3π/5 = θ_3`) while satisfying the subcritical one (`11π/10 < 2θ_i`,
`GX.exists_isConeSphere_of_subcritical`). (The paper claims only sufficiency.) -/
theorem exists_isConeSphere_four_not_troyanovAngleCondition :
    ∃ (θ : Fin 4 → ℝ) (M : Type) (_ : TopologicalSpace M) (_ : SingularGXStructure SO3 Sph2 M)
      (p : Fin 4 → M), IsConeSphere M θ p ∧ ¬ TroyanovAngleCondition θ := by
  have hπ := Real.pi_pos
  set θ : Fin 4 → ℝ := ![3 * π / 2, 3 * π / 2, 3 * π / 2, 3 * π / 5] with hθ
  have hsum : ∑ i, (θ i - 2 * π) + 4 * π = 11 * π / 10 := by
    simp only [hθ, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    ring
  obtain ⟨M, _, _, p, hp⟩ := exists_isConeSphere_of_subcritical (by norm_num) θ
    (fun i => by fin_cases i <;> simp [hθ] <;> positivity)
    (fun i => by fin_cases i <;> simp [hθ] <;> linarith)
    (by rw [hsum]; positivity)
    (fun j => by rw [hsum]; fin_cases j <;> simp [hθ] <;> linarith)
  refine ⟨θ, M, _, _, p, hp, fun h => ?_⟩
  have h3 := h.2.2.2 3
  rw [hsum] at h3
  simp [hθ] at h3
  linarith

end Main

end GX
