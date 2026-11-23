import GX.BBS.RP1Circles

/-!
# The arcs `i^±(ℓ(p))` of a link, and their pull-backs `i^±(L)` to a `(Γ_p, ℓ(p))`-circle

Target `T-bbs-i-pm` (`roadmap/roadmap.toml`; BBS § 3.3.2, layer L2 in lean-gx, DEC-192).
`papers/bbs/legacy/labeled/colI_v1.tex`. 0 `sorry`.

* `bbsdef:lies_denote_respectively_set` — `colI_v1.tex:819` — partial (unmarked: a reading):
  `GX.dsFutureDirs`, `GX.dsPastDirs` (through `GX.dsProj : T_p HS² → p^⊥`), and `GX.iPlus`,
  `GX.iMinus` at `p ∈ dS²`. "Future oriented directions" is read *future timelike* (SCOPE (a)).
* **`bbsdef:lies_domain_respectively_set`** — `colI_v1.tex:828` — `GX.lightDomain` (with `c_v`,
  `GX.cv`), and `GX.iPlus`, `GX.iMinus` at `p ∈ ∂ℍ²±`; the germ does not depend on the lift
  (`GX.mem_lightDomain_iff_forall_lift`), and it is `{B(p,·) < 0}` resp. `{B(p,·) ≥ 0}`.
* `bbsdef:circle_developing_map_preimages` — `colI_v1.tex:842` — partial (unmarked: l.844 is false
  for one arc at a lightlike `p`): `GX.GammaLinkCircle.iPlusL`, `iMinusL`, the developing map
  (`GX.GammaLinkCircle.exists_isDevAlong`, `GX.isAnalyticAction_link`), assembled in
  `GX.GammaLinkCircle.devPreimages`.

> If $p$ lies in $\dS^2$, we denote by $i^+(\ell(p))$ (respectively $i^-(\ell(p))$) the set of
> future oriented (resp. past oriented) directions. (l.820–821)
>
> If $p$ lies in $\partial\HH^2_+$, the domain $i^+(\ell(p))$ (respectively $i^-(\ell(p))$) is the
> set of directions $v$ such that $c_v(s)$ lies in $\HH^2_+$ (respectively $\dS^2$) for $s$
> sufficiently small. Similarly, if $p$ lies in $\partial\HH^2_-$, the domain $i^-(\ell(p))$
> (respectively $i^+(\ell(p))$) is the set of directions $v$ such that $c_v(s)$ lies in $\HH^2_-$
> (respectively $\dS^2$) for $s$ sufficiently small. (l.829–832)
>
> Let $L$ be a $(\Gamma_p, \ell(p))$-circle. Let $d: \tilde{L} \to \ell(p)$ the developing map.
> The preimages $d^{-1}(i^+(\ell(p)))$ and $d^{-1}(i^-(\ell(p)))$ are open domain in $\tilde{L}$,
> preserved by the deck transformations. Their projections in $L$ are denoted respectively by
> $i^+(L)$ and $i^-(L)$. (l.843–845)

The facts printed beside them, without proof, all formalized:

> Observe that $i^+(\ell(p))$ and $i^-(\ell(p))$ are connected, and that their complement in
> $\ell(p)$ has two connected components. (l.824) [...] In this situation, $i^+(\ell(p))$ and
> $i^-(\ell(p))$ are the connected components of the complement of the two points in $\ell(p)$
> which are directions tangent to $\partial\HH^2_\pm$. (l.835–836) For time-like singularities,
> we simply define $i^+(\ell(p)) = i^-(\ell(p)) = \emptyset$. (l.838) Finally, observe that the
> extremities of the arcs $i^\pm(\ell(p))$ are precisely the fixed points of $\Gamma_p$. (l.840)

## Main declarations

* **`(Γ_p, ℓ(p))` is analytic** (`GX.isAnalyticAction_link`: faithful and rigid, through
  `GX.det_tangent`), so a `(Γ_p, ℓ(p))`-circle has a developing map on its universal covering
  `ℝ → L` with a holonomy in `Γ_p` (`GX.GammaLinkCircle.exists_isDevAlong`), unique up to a unique
  element of `Γ_p` (`GX.GammaLinkCircle.IsDevAlong.existsUnique_eq_smul`) — RP1Circles SCOPE (d).
* **l.824**: `GX.isConnected_dsFutureDirs`, `GX.isConnected_dsPastDirs`;
  `GX.ncard_components_compl_ds` (the complement of `i⁺ ∪ i⁻` has exactly two components);
  `GX.isConnected_compl_dsFutureDirs` (the complement of `i⁺` alone is connected).
* **l.835–836**: `GX.ncard_tangentDirs` (two tangent directions, `GX.tangentDirs_eq`),
  `GX.components_compl_tangentDirs` (its complement has the components `{B(p,·) < 0}`,
  `{B(p,·) > 0}`); **false as printed** (`GX.components_compl_tangentDirs_ne_of_bdPlus`,
  `…_of_bdMinus`), true for `i⁻ ∖ T` at `∂ℍ²₊` (`GX.components_compl_tangentDirs_of_bdPlus`),
  resp. `i⁺ ∖ T` at `∂ℍ²₋` (`GX.components_compl_tangentDirs_of_bdMinus`).
* **l.838**: `GX.iPlus_iMinus_of_timelike`. **l.840**, every `p`:
  `GX.frontier_iPlus_union_frontier_iMinus` (`GX.fixedPoints_eq_of_deSitter`,
  `GX.fixedPoints_eq_of_null`, `GX.fixedPoints_eq_empty_of_timelike`).
* **l.844**: deck invariance for every `p` (`GX.GammaLinkCircle.IsDevAlong.deck_iPlus`, `…_iMinus`),
  openness wherever the arc is open (`…isOpen_preimage_iPlus`, `…_iMinus`), projections
  (`…image_preimage_iPlus`, `…_iMinus`); the counterexample `GX.not_isOpen_preimage_iMinus_regular`.

## Hypothesis checklist

| BBS | here |
|---|---|
| `p ∈ dS²` (l.820) | ✓ `p ∈ HS.piece 2 .deSitter` |
| "future oriented (resp. past oriented) directions" (l.820–821) | ⚠ reading: future (past) **timelike** directions of `T_p dS² = p^⊥` (SCOPE (a)) |
| `p ∈ ∂ℍ²₊`, `∂ℍ²₋` (l.829, 831) | ✓ `HS.piece 2 .bdPlus`, `.bdMinus` |
| `c_v(s)` "for `s` sufficiently small" (l.830) | ✓ `∀ᶠ s in 𝓝[>] 0, cv p σ s ∈ HS.piece 2 k`; lift-free (`mem_lightDomain_iff_forall_lift`) |
| timelike `p`: `i^± = ∅` (l.838) | ✓ `iPlus`, `iMinus` |
| `L` a `(Γ_p, ℓ(p))`-circle, `d : L̃ → ℓ(p)` the developing map (l.843) | ✓ `GammaLinkCircle`, `IsDevAlong`; `L̃ = ℝ` (`IsPeriodicCover`); the l.844 results hold along every `E : M → L` |
| "open domain" (l.844) | ⚠ open wherever the arc is open; `i⁻` at `∂ℍ²₊` (`i⁺` at `∂ℍ²₋`) is not open, and for the regular link neither is its preimage (finding); "domain" read "open set" (SCOPE (c)) |
| "preserved by the deck transformations" (l.844) | ✓ every `φ` with `E ∘ φ = E` |
| "their projections in `L`" (l.845) | ✓ `E '' d⁻¹(i^±(ℓ(p))) = i^±(L)` for `E` onto |

## SCOPE (disclosed)

* **(a) Reading of l.820.** `T_p dS²` is `p^⊥ ⊂ ℝ^{1,2}` (the Klein model's Lorentzian metric is
  the hyperboloid's), identified with `T_p HS² = ℝ^{1,2}/ℝp` by the orthogonal projection
  (`GX.dsProj`, `Q(p)` times it), time-oriented by `ℝ^{1,2}`. "Future oriented" is read *future
  timelike* (open arcs). Against it, l.815 ("in the two first cases [time-like, light-like], it
  can be future oriented or past oriented") suggests the causal reading (closed arcs); but that
  reading contradicts l.844's openness: the closed arc is not open
  (`GX.not_isOpen_dsFutureCausalDirs`), nor is its preimage under the regular link's developing
  map (`GX.not_isOpen_preimage_dsFutureCausal_regular`). A question.
* **(b) The slips.** l.826 announces an extension "to time-like singularities"; l.828 is about
  `p ∈ ∂ℍ²±`, light-like (the time-like case is l.838). At `p ∈ ∂ℍ²₊`, the tangent line of the
  conic is `c_v` for the two tangent directions, and it lies in `dS²` but for `p`; so the printed
  `i⁻(ℓ(p))` contains them (`GX.lightDomain_deSitter_eq`): it is a closed arc, not open
  (`GX.not_isOpen_iMinus_of_bdPlus`), not a component of the complement of the tangent
  directions (l.835–836), and its preimage under the regular link's developing map is not open
  (l.844, `GX.not_isOpen_preimage_iMinus_regular`). Symmetrically for `i⁺` at `∂ℍ²₋`. The
  corrected arc is `i⁻ ∖ T = {B(p,·) > 0}`, open, a component, `Γ_p`-invariant.
* **(c) "Domain"** (l.844) is read "open set": `d⁻¹(i^±)` is invariant under `s ↦ s + 1`, and
  for the regular link at `p ∈ dS²` it is not connected
  (`GX.not_isPreconnected_preimage_iPlus_regular`). At l.829 and l.831 "the domain" is not read as
  asserting openness (l.844 writes "open domain"); read so, the label is false for the `dS²` side.
  "Their complement" (l.824) is read as the complement of `i⁺ ∪ i⁻`: the complement of each
  arc alone is connected (`GX.isConnected_compl_dsFutureDirs`). "Extremities" (l.840) are the
  frontier points in `ℓ(p)`. The tangent directions to `∂ℍ²±` are `p^⊥/ℝp` (`GX.tangentDirs`).
* **(d)** `c_v(s) = [p + s w]`, `s ≥ 0`, a lift `w` of `v`: the half of the oriented projective
  line from `p` through `[w]`; only its germ at `0⁺` is used. `L̃` is `ℝ` with a periodic
  covering, as in `GX.HasLiftedHolonomy`; gx's universal cover is not used.
* **(e) Not formalized**: l.850–852 ("the `ℝP¹`-structure and `i^±(L)` determine the
  `(Γ_p, ℓ(p))`-structure", an invitation to the reader, no label) and `𝔢(L)`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`; lean-causal `ca2ad78`
(`Causal.Flat.Form`, `Isometries`: `boost`, `nullRot`), through `GX.BBS.RP1Circles`.
-/

noncomputable section

open Set Filter Topology ComplexConjugate
open scoped MatrixGroups

namespace GX

set_option linter.unusedSectionVars false

/-- `ℝ^{1,2}`. -/
local notation "𝕄" => Causal.Minkowski 2

/-! ### Two components -/

section Components

variable {X : Type*} [TopologicalSpace X]

/-- If `S = S₁ ∪ S₂`, with `S₁, S₂` disjoint, closed and preconnected, then `S₁` is the
connected component in `S` of each of its points. -/
theorem connectedComponentIn_eq_of_closed {S S₁ S₂ : Set X} (hS : S = S₁ ∪ S₂)
    (h₁ : IsPreconnected S₁) (hc₁ : IsClosed S₁) (hc₂ : IsClosed S₂) (hd : Disjoint S₁ S₂)
    {x : X} (hx : x ∈ S₁) : connectedComponentIn S x = S₁ := by
  have hxS : x ∈ S := hS ▸ Or.inl hx
  refine Subset.antisymm ?_ (h₁.subset_connectedComponentIn hx (hS ▸ subset_union_left))
  have hsub : connectedComponentIn S x ⊆ S₁ ∪ S₂ := hS ▸ connectedComponentIn_subset S x
  rcases isPreconnected_iff_subset_of_disjoint_closed.1 isPreconnected_connectedComponentIn
    S₁ S₂ hc₁ hc₂ hsub (by rw [hd.inter_eq, inter_empty]) with h | h
  · exact h
  · exact absurd (h (mem_connectedComponentIn hxS)) (Set.disjoint_left.1 hd hx)
/-- The same, with `S₁, S₂` open. -/
theorem connectedComponentIn_eq_of_open {S S₁ S₂ : Set X} (hS : S = S₁ ∪ S₂)
    (h₁ : IsPreconnected S₁) (ho₁ : IsOpen S₁) (ho₂ : IsOpen S₂) (hd : Disjoint S₁ S₂)
    {x : X} (hx : x ∈ S₁) : connectedComponentIn S x = S₁ := by
  have hxS : x ∈ S := hS ▸ Or.inl hx
  refine Subset.antisymm ?_ (h₁.subset_connectedComponentIn hx (hS ▸ subset_union_left))
  have hsub : connectedComponentIn S x ⊆ S₁ ∪ S₂ := hS ▸ connectedComponentIn_subset S x
  rcases isPreconnected_iff_subset_of_disjoint.1 isPreconnected_connectedComponentIn
    S₁ S₂ ho₁ ho₂ hsub (by rw [hd.inter_eq, inter_empty]) with h | h
  · exact h
  · exact absurd (h (mem_connectedComponentIn hxS)) (Set.disjoint_left.1 hd hx)
/-- The set of connected components of `S`, when `S` splits into two nonempty pieces each of
which is the component of its points. -/
theorem components_eq_pair {S S₁ S₂ : Set X} (hS : S = S₁ ∪ S₂)
    (h₁ : ∀ x ∈ S₁, connectedComponentIn S x = S₁) (h₂ : ∀ x ∈ S₂, connectedComponentIn S x = S₂)
    (hn₁ : S₁.Nonempty) (hn₂ : S₂.Nonempty) :
    {K | ∃ x ∈ S, connectedComponentIn S x = K} = {S₁, S₂} := by
  ext K
  simp only [mem_setOf_eq, mem_insert_iff, mem_singleton_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [hS] at hx
    rcases hx with hx | hx
    · exact Or.inl (h₁ x hx)
    · exact Or.inr (h₂ x hx)
  · rintro (rfl | rfl)
    · obtain ⟨x, hx⟩ := hn₁; exact ⟨x, hS ▸ Or.inl hx, h₁ x hx⟩
    · obtain ⟨x, hx⟩ := hn₂; exact ⟨x, hS ▸ Or.inr hx, h₂ x hx⟩

end Components

/-! ### `T_p HS²`, directions, and the area form -/

section Tangent

variable (p : HS 2)

/-- The class of `w ∈ ℝ^{1,2}` in `T_p HS² = ℝ^{1,2}/ℝp`. -/
abbrev tpMk (w : 𝕄) : TpHS p := Submodule.Quotient.mk w
theorem tpMk_eq_zero_iff {w : 𝕄} : tpMk p w = 0 ↔ ∃ c : ℝ, w = c • (p : 𝕄) := by
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_span_singleton]
  exact ⟨fun ⟨c, hc⟩ => ⟨c, hc.symm⟩, fun ⟨c, hc⟩ => ⟨c, hc.symm⟩⟩
theorem tpMk_eq_tpMk_iff {v w : 𝕄} : tpMk p v = tpMk p w ↔ ∃ c : ℝ, v = w + c • (p : 𝕄) := by
  rw [Submodule.Quotient.eq, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨c, hc⟩; exact ⟨c, by rw [hc]; abel⟩
  · rintro ⟨c, hc⟩; exact ⟨c, by rw [hc]; abel⟩
theorem continuous_tpMk : Continuous (tpMk p) :=
  LinearMap.continuous_of_finiteDimensional (ℝ ∙ (p : 𝕄)).mkQ
instance nonempty_link : Nonempty (Link p) := by
  obtain ⟨φ⟩ := isCircle_link p
  exact ⟨φ.symm 1⟩
/-- A lift of `σ ∈ ℓ(p)` to `ℝ^{1,2}` (a choice; nothing below depends on it). -/
def liftT (σ : Link p) : 𝕄 := (Submodule.Quotient.mk_surjective _ (σ : TpHS p)).choose
theorem tpMk_liftT (σ : Link p) : tpMk p (liftT p σ) = σ :=
  (Submodule.Quotient.mk_surjective _ (σ : TpHS p)).choose_spec
/-- The direction `[w] ∈ ℓ(p)` of `w ∉ ℝp` (a junk value on `ℝp`). -/
def dirOf (w : 𝕄) : Link p := rayNormalize (Classical.arbitrary _) (tpMk p w)
theorem coe_dirOf {w : 𝕄} (hw : tpMk p w ≠ 0) :
    (dirOf p w : TpHS p) = ‖tpMk p w‖⁻¹ • tpMk p w := by
  rw [dirOf, coe_rayNormalize _ hw]
theorem dirOf_eq {w : 𝕄} {σ : Link p} (h : tpMk p w = σ) : dirOf p w = σ := by
  rw [dirOf, h, rayNormalize_raySphere]
theorem continuousOn_dirOf : ContinuousOn (dirOf p) {w | tpMk p w ≠ 0} := fun _ hw =>
  ((continuousAt_rayNormalize _ hw).comp (continuous_tpMk p).continuousAt).continuousWithinAt
/-- **A set of directions cut out by a condition on `T_p HS²` invariant under positive scaling
is the image of the corresponding cone of `ℝ^{1,2}`.** -/
theorem image_dirOf_eq {P : TpHS p → Prop} (hP : ∀ c : ℝ, 0 < c → ∀ z, P (c • z) ↔ P z) :
    dirOf p '' {w | tpMk p w ≠ 0 ∧ P (tpMk p w)} = {σ : Link p | P σ} := by
  ext σ
  constructor
  · rintro ⟨w, ⟨hw, hPw⟩, rfl⟩
    show P (dirOf p w : TpHS p)
    rw [coe_dirOf p hw]
    exact (hP _ (inv_pos.2 (norm_pos_iff.2 hw)) _).2 hPw
  · intro hσ
    refine ⟨liftT p σ, ⟨?_, ?_⟩, dirOf_eq p (tpMk_liftT p σ)⟩
    · rw [tpMk_liftT]; exact raySphere_ne_zero σ
    · rw [tpMk_liftT]; exact hσ
/-- The area form of `T_p HS²`, read through `tpHSEquiv p : T_p HS² ≃ ℂ` (its sign is
immaterial). -/
def linkArea (u v : TpHS p) : ℝ :=
  ((starRingEnd ℂ) (tpHSEquiv p u) * tpHSEquiv p v).im
theorem linkArea_eq (u v : TpHS p) : linkArea p u v =
    (tpHSEquiv p u).re * (tpHSEquiv p v).im - (tpHSEquiv p u).im * (tpHSEquiv p v).re := by
  simp only [linkArea, Complex.mul_im, Complex.conj_re, Complex.conj_im]; ring
/-- `SL(2,ℝ)` preserves the area form of `ℂ = ℝ²`. -/
theorem slLin_area (g : SL(2, ℝ)) (a b : ℂ) :
    (slLin g a).re * (slLin g b).im - (slLin g a).im * (slLin g b).re = a.re * b.im - a.im * b.re := by
  have hdet := g.2
  rw [Matrix.det_fin_two] at hdet
  simp only [slLin_apply]
  linear_combination (a.re * b.im - a.im * b.re) * hdet
/-- **`Γ_p` preserves the area of `T_p HS²`**: its tangent action has determinant `1`
(`GX.det_tangent`, through `GX.gammaToSL`). -/
theorem linkArea_tangent (A : GammaP p) (u v : TpHS p) :
    linkArea p (GammaP.tangent A u) (GammaP.tangent A v) = linkArea p u v := by
  have h : ∀ z, tpHSEquiv p (GammaP.tangent A z) = slLin (gammaToSL p (tpHSEquiv p) A) (tpHSEquiv p z) :=
    fun z => by rw [slLin_gammaToSL, LinearEquiv.symm_apply_apply]
  rw [linkArea_eq, linkArea_eq, h, h, slLin_area]
theorem linkArea_swap (u v : TpHS p) : linkArea p v u = -linkArea p u v := by
  rw [linkArea_eq, linkArea_eq]; ring
theorem linkArea_self (u : TpHS p) : linkArea p u u = 0 := by
  rw [linkArea_eq]; ring
theorem linkArea_add_smul (u v w : TpHS p) (a b : ℝ) :
    linkArea p u (a • v + b • w) = a * linkArea p u v + b * linkArea p u w := by
  simp only [linkArea_eq, map_add, map_smul, Complex.add_re, Complex.add_im, Complex.smul_re,
    Complex.smul_im, smul_eq_mul]; ring
theorem linkArea_smul_left (u v : TpHS p) (a : ℝ) :
    linkArea p (a • u) v = a * linkArea p u v := by
  simp only [linkArea_eq, map_smul, Complex.smul_re, Complex.smul_im, smul_eq_mul]; ring
theorem linkArea_smul_right (u v : TpHS p) (a : ℝ) :
    linkArea p u (a • v) = a * linkArea p u v := by
  simp only [linkArea_eq, map_smul, Complex.smul_re, Complex.smul_im, smul_eq_mul]; ring

theorem eq_smul_of_linkArea_eq_zero {u v : TpHS p} (hu : u ≠ 0) (h : linkArea p u v = 0) :
    ∃ r : ℝ, v = r • u := by
  set a := tpHSEquiv p u
  set b := tpHSEquiv p v
  have ha : a ≠ 0 := (LinearEquiv.map_ne_zero_iff _).2 hu
  have hn : a.re ^ 2 + a.im ^ 2 ≠ 0 := by
    intro h0
    apply ha
    apply Complex.ext <;> simp <;> nlinarith [sq_nonneg a.re, sq_nonneg a.im]
  rw [linkArea_eq] at h
  refine ⟨(a.re * b.re + a.im * b.im) / (a.re ^ 2 + a.im ^ 2), (tpHSEquiv p).injective ?_⟩
  rw [map_smul]
  apply Complex.ext
  · simp only [Complex.smul_re, smul_eq_mul]
    field_simp
    linear_combination (-a.im) * h
  · simp only [Complex.smul_im, smul_eq_mul]
    field_simp
    linear_combination a.re * h
/-- Cramer's rule in `T_p HS²`. -/
theorem eq_add_of_linkArea_ne_zero {u v : TpHS p} (h : linkArea p u v ≠ 0) (z : TpHS p) :
    z = (linkArea p z v / linkArea p u v) • u + (linkArea p u z / linkArea p u v) • v := by
  apply (tpHSEquiv p).injective
  rw [map_add, map_smul, map_smul]
  apply Complex.ext
  · rw [Complex.add_re, Complex.smul_re, Complex.smul_re, smul_eq_mul, smul_eq_mul,
      div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, eq_div_iff h]
    simp only [linkArea_eq]; ring
  · rw [Complex.add_im, Complex.smul_im, Complex.smul_im, smul_eq_mul, smul_eq_mul,
      div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, eq_div_iff h]
    simp only [linkArea_eq]; ring
end Tangent

/-! ### `(Γ_p, ℓ(p))` is analytic, and the developing map of a `(Γ_p, ℓ(p))`-circle -/

section Analytic

variable (p : HS 2)

/-- An element of `Γ_p` acting trivially on `T_p HS²` is the identity. -/
theorem gammaP_eq_one_of_tangent {A : GammaP p} (h : ∀ z, GammaP.tangent A z = z) : A = 1 := by
  set A' : 𝕄 ≃ₗ[ℝ] 𝕄 := ((A : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄) with hA'
  have hAp : A' p = p := A.2
  have hL : A' ∈ Causal.Flat.lorentz 2 := (A : Causal.Flat.lorentz 2).2
  have hc : ∀ v, ∃ c : ℝ, A' v = v + c • (p : 𝕄) := fun v => (tpMk_eq_tpMk_iff p).1 (h (tpMk p v))
  have key : ∀ v (c : ℝ), A' v = v + c • (p : 𝕄) →
      c * Causal.Flat.minkB (p : 𝕄) v = 0 ∧ c * Causal.Flat.minkQ (p : 𝕄) = 0 := by
    intro v c hv
    have h1 := Causal.Flat.lorentz.minkQ_apply hL v
    have h2 := Causal.Flat.lorentz.minkB_apply hL v p
    rw [hv] at h1
    rw [hv, hAp] at h2
    rw [Causal.Flat.minkQ_add, Causal.Flat.minkQ_smul, Causal.Flat.minkB_smul_right] at h1
    rw [Causal.Flat.minkB_add_left, Causal.Flat.minkB_smul_left, ← Causal.Flat.minkQ_eq_minkB] at h2
    have hcQ : c * Causal.Flat.minkQ (p : 𝕄) = 0 := by linarith
    refine ⟨?_, hcQ⟩
    rw [Causal.Flat.minkB_comm]
    linear_combination (h1 - c * hcQ) / 2
  have hfix : ∀ v, A' v = v := by
    by_cases hQ : Causal.Flat.minkQ (p : 𝕄) = 0
    · have hp0 : (p : 𝕄).1 ≠ 0 := HS.fst_ne_zero_of_minkQ_nonpos p hQ.le
      set w₀ := Causal.Flat.timeUnit 2
      have hBw : Causal.Flat.minkB (p : 𝕄) w₀ ≠ 0 := by
        simp only [w₀, Causal.Flat.minkB, Causal.Flat.timeUnit, mul_one, inner_zero_right, add_zero,
          neg_ne_zero]
        exact hp0
      obtain ⟨c₀, hc₀⟩ := hc w₀
      have hc₀0 : c₀ = 0 := (mul_eq_zero.1 (key w₀ c₀ hc₀).1).resolve_right hBw
      intro v
      obtain ⟨c, hcv⟩ := hc v
      by_contra hne
      have hc0 : c ≠ 0 := by
        rintro rfl
        rw [zero_smul, add_zero] at hcv
        exact hne hcv
      have hBv : Causal.Flat.minkB (p : 𝕄) v = 0 := (mul_eq_zero.1 (key v c hcv).1).resolve_left hc0
      have hsum : A' (v + w₀) = (v + w₀) + c • (p : 𝕄) := by
        rw [map_add, hcv, hc₀, hc₀0, zero_smul, add_zero]; abel
      have := (key _ c hsum).1
      rw [Causal.Flat.minkB_add_right, hBv, zero_add] at this
      exact hBw ((mul_eq_zero.1 this).resolve_left hc0)
    · intro v
      obtain ⟨c, hcv⟩ := hc v
      have hc0 : c = 0 := (mul_eq_zero.1 (key v c hcv).2).resolve_right hQ
      rw [hcv, hc0, zero_smul, add_zero]
  exact Subtype.ext (Subtype.ext (LinearEquiv.ext hfix))

/-- **Rigidity of `(Γ_p, ℓ(p))`**: two elements of `Γ_p` agreeing on a nonempty open subset of
`ℓ(p)` are equal. -/
theorem gammaP_eq_of_eqOn {A B : GammaP p} {U : Set (Link p)} (hU : IsOpen U) (hne : U.Nonempty)
    (heq : EqOn (fun σ : Link p => A • σ) (fun σ => B • σ) U) : A = B := by
  obtain ⟨σ₀, hσ₀⟩ := hne
  set TA := GammaP.tangent A
  set TB := GammaP.tangent B
  have heq' : EqOn (linRaySmul TA) (linRaySmul TB) U := heq
  obtain ⟨c₀, hc₀, h₀⟩ := linRaySmul_eq_linRaySmul_iff.1 (heq' hσ₀)
  have hT := eventually_eigen_of_eqOn hU hσ₀ heq'
  set T : TpHS p →ₗ[ℝ] TpHS p := (TA.trans TB.symm).toLinearMap
  have hT0 : T σ₀ = c₀ • (σ₀ : TpHS p) := by
    show TB.symm (TA σ₀) = _
    rw [h₀, map_smul, LinearEquiv.symm_apply_apply]
  have hall := eq_smul_of_eventually_eigen (T := T) (raySphere_ne_zero σ₀) hT0 hT
  have hAB : ∀ w, TA w = c₀ • TB w := fun w => by
    have := hall w
    change TB.symm (TA w) = c₀ • w at this
    have h2 := congrArg TB this
    rwa [LinearEquiv.apply_symm_apply, map_smul] at h2
  have hinv : ∀ z, GammaP.tangent B⁻¹ (TB z) = z := fun z => by
    have := congrArg (fun T : TpHS p ≃ₗ[ℝ] TpHS p => T z) (GammaP.tangent_mul B⁻¹ B)
    simp only [inv_mul_cancel, GammaP.tangent_one] at this
    exact this.symm
  have hC : ∀ z, GammaP.tangent (B⁻¹ * A) z = c₀ • z := fun z => by
    rw [GammaP.tangent_mul]
    show GammaP.tangent B⁻¹ (TA z) = _
    rw [hAB, map_smul, hinv]
  have hdet := det_tangent (B⁻¹ * A)
  have hlin : (GammaP.tangent (B⁻¹ * A) : TpHS p →ₗ[ℝ] TpHS p) = c₀ • LinearMap.id :=
    LinearMap.ext fun z => by
      rw [LinearMap.smul_apply, LinearMap.id_apply]
      exact hC z
  rw [hlin, LinearMap.det_smul, LinearMap.det_id, finrank_tpHS, mul_one] at hdet
  have hc1 : c₀ = 1 := by nlinarith
  have h1 : B⁻¹ * A = 1 := gammaP_eq_one_of_tangent p fun z => by rw [hC, hc1, one_smul]
  exact (inv_mul_eq_one.1 h1).symm

/-- **`(Γ_p, ℓ(p))` is analytic** in gx's sense (faithful and rigid; `RamcovGX.tex:341`). -/
instance isAnalyticAction_link : IsAnalyticAction (GammaP p) (Link p) :=
  IsAnalyticAction.of_eq_of_eqOn fun hU hne heq => gammaP_eq_of_eqOn p hU hne heq

end Analytic

section Developing

variable {L : Type*} [TopologicalSpace L]

/-- `d : M → ℓ(p)` is **a developing map of the `(Γ_p, ℓ(p))`-circle `C` along `E : M → L`**:
near every point, `d` is a `Γ_p`-translate of the chart of `L`, read through `E`. For a covering
`E` this is gx's developing map of the structure pulled back along `E`
(`GX.GammaLinkCircle.isDevAlong_iff_isGXMorphism`). -/
def GammaLinkCircle.IsDevAlong (C : GammaLinkCircle L) {M : Type*} [TopologicalSpace M]
    (E : M → L) (d : M → Link C.pt) : Prop :=
  ∀ s, ∃ A : GammaP C.pt, ∀ᶠ s' in 𝓝 s, d s' = A • @chartAt (Link C.pt) _ L _ C.atlas (E s) (E s')

theorem GammaLinkCircle.isDevAlong_iff_isGXMorphism (C : GammaLinkCircle L) {M : Type*}
    [TopologicalSpace M] {E : M → L} (hE : IsLocalHomeomorph E) {d : M → Link C.pt} :
    C.IsDevAlong E d ↔
      letI := C.atlas
      letI := pullbackChartedSpace (X := Link C.pt) hE
      IsGXMorphism (GammaP C.pt) (Link C.pt) d := by
  letI := C.atlas
  letI := pullbackChartedSpace (X := Link C.pt) hE
  show _ ↔ IsGXMorphism (GammaP C.pt) (Link C.pt) d
  have hch : ∀ s s', chartAt (Link C.pt) s s' = chartAt (Link C.pt) (E s) (E s') :=
    pullback_chartAt_apply hE
  constructor
  · intro h
    refine isGXMorphism_of_eventually fun s => ?_
    obtain ⟨g, hg⟩ := h s
    exact ⟨g, by filter_upwards [hg] with s' hs' using by rw [hs', hch]⟩
  · intro h s
    obtain ⟨g, hg⟩ := (isGXMorphism_iff_model.1 h).2 s
    exact ⟨g, by filter_upwards [hg] with s' hs' using by rw [hs', hch]⟩

/-- **Uniqueness of the developing map** up to a unique element of `Γ_p`. -/
theorem GammaLinkCircle.IsDevAlong.existsUnique_eq_smul {C : GammaLinkCircle L} {M : Type*}
    [TopologicalSpace M] [PreconnectedSpace M] [Nonempty M] {E : M → L}
    (hE : IsLocalHomeomorph E) {d d' : M → Link C.pt} (hd : C.IsDevAlong E d)
    (hd' : C.IsDevAlong E d') : ∃! A : GammaP C.pt, ∀ s, d' s = A • d s := by
  letI := C.atlas
  haveI := C.hasGroupoid
  letI := pullbackChartedSpace (X := Link C.pt) hE
  haveI : HasGroupoid M (gxGroupoid (GammaP C.pt) (Link C.pt)) := hasGroupoid_pullback hE
  exact developing_unique_of_preconnected ((C.isDevAlong_iff_isGXMorphism hE).1 hd)
    ((C.isDevAlong_iff_isGXMorphism hE).1 hd')

/-- **The developing map of a `(Γ_p, ℓ(p))`-circle** (l.843, "Let `d : L̃ → ℓ(p)` the developing
map"): the universal covering `L̃ = ℝ → L` (a periodic covering) carries a developing map, with a
holonomy `ρ ∈ Γ_p` (`d (s + 1) = ρ d s`). -/
theorem GammaLinkCircle.exists_isDevAlong (C : GammaLinkCircle L) :
    ∃ E : ℝ → L, IsPeriodicCover E ∧ ∃ d : ℝ → Link C.pt, C.IsDevAlong E d ∧
      ∃ ρ : GammaP C.pt, ∀ s, d (s + 1) = ρ • d s := by
  letI := C.atlas
  haveI := C.hasGroupoid
  obtain ⟨E, hE⟩ := exists_isPeriodicCover C.isCircle
  have hEl := hE.isCoveringMap.isLocalHomeomorph
  obtain ⟨d, hd⟩ : ∃ d : ℝ → Link C.pt, C.IsDevAlong E d := by
    letI := pullbackChartedSpace (X := Link C.pt) hEl
    haveI : HasGroupoid ℝ (gxGroupoid (GammaP C.pt) (Link C.pt)) := hasGroupoid_pullback hEl
    obtain ⟨d, hd⟩ := exists_developingMap (G := GammaP C.pt) (X := Link C.pt) (N := ℝ)
    exact ⟨d, (C.isDevAlong_iff_isGXMorphism hEl).2 hd⟩
  refine ⟨E, hE, d, hd, ?_⟩
  have hd1 : C.IsDevAlong E fun s => d (s + 1) := fun s => by
    obtain ⟨A, hA⟩ := hd (s + 1)
    refine ⟨A, ?_⟩
    have hc : Tendsto (fun s' : ℝ => s' + 1) (𝓝 s) (𝓝 (s + 1)) :=
      (continuous_add_const (1 : ℝ)).tendsto s
    filter_upwards [hc.eventually hA] with s' hs'
    rw [hs', hE.add_one, hE.add_one]
  obtain ⟨ρ, hρ, -⟩ := hd.existsUnique_eq_smul hEl hd1
  exact ⟨ρ, hρ⟩

end Developing

/-! ### Cones, coordinates and the right angle of `ℝ²` -/

section Cones

/-- The rotation by a right angle of `ℝ²`, `(x₀, x₁) ↦ (−x₁, x₀)`. -/
def jRot (x : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![-(x 1), x 0]

@[simp] theorem jRot_zero (x : EuclideanSpace ℝ (Fin 2)) : jRot x 0 = -(x 1) := rfl

@[simp] theorem jRot_one (x : EuclideanSpace ℝ (Fin 2)) : jRot x 1 = x 0 := rfl

theorem inner_two (x y : EuclideanSpace ℝ (Fin 2)) :
    inner ℝ x y = x 0 * y 0 + x 1 * y 1 := by
  simp only [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, conj_trivial]; ring

theorem norm_sq_two (x : EuclideanSpace ℝ (Fin 2)) : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]

/-- `minkQ` in coordinates. -/
theorem minkQ_two (v : 𝕄) : Causal.Flat.minkQ v = -v.1 ^ 2 + v.2 0 ^ 2 + v.2 1 ^ 2 := by
  rw [Causal.Flat.minkQ, norm_sq_two]; ring

/-- `minkB` in coordinates. -/
theorem minkB_two (v w : 𝕄) :
    Causal.Flat.minkB v w = -(v.1 * w.1) + v.2 0 * w.2 0 + v.2 1 * w.2 1 := by
  rw [Causal.Flat.minkB, inner_two]; ring

theorem isOpen_isFutureTimelike : IsOpen {v : 𝕄 | Causal.Flat.IsFutureTimelike v} :=
  (isOpen_lt continuous_const continuous_fst).inter
    (isOpen_lt Causal.Flat.continuous_minkQ continuous_const)

theorem isClosed_isFutureCausal : IsClosed {v : 𝕄 | Causal.Flat.IsFutureCausal v} :=
  (isClosed_le continuous_const continuous_fst).inter
    (isClosed_le Causal.Flat.continuous_minkQ continuous_const)

theorem isFutureTimelike_iff_norm {v : 𝕄} :
    Causal.Flat.IsFutureTimelike v ↔ ‖v.2‖ < v.1 := by
  rw [Causal.Flat.IsFutureTimelike, Causal.Flat.minkQ_lt_zero_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact abs_lt_of_sq_lt_sq' h2 h1.le |>.2
  · intro h
    have h0 : 0 < v.1 := lt_of_le_of_lt (norm_nonneg _) h
    exact ⟨h0, pow_lt_pow_left₀ h (norm_nonneg _) two_ne_zero⟩

/-- The open future timelike cone is convex. -/
theorem convex_isFutureTimelike : Convex ℝ {v : 𝕄 | Causal.Flat.IsFutureTimelike v} := by
  intro x hx y hy a b ha hb hab
  simp only [mem_setOf_eq, isFutureTimelike_iff_norm] at hx hy ⊢
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  calc ‖a • x.2 + b • y.2‖ ≤ a * ‖x.2‖ + b * ‖y.2‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
    _ < a * x.1 + b * y.1 := by
        rcases ha.lt_or_eq with ha' | ha'
        · nlinarith [mul_le_mul_of_nonneg_left hy.le hb]
        · subst ha'
          have hb1 : b = 1 := by linarith
          subst hb1
          simpa using hy

/-- A nonzero future causal vector plus a positive multiple of a future timelike one is future
timelike. -/
theorem isFutureTimelike_add_smul {x y : 𝕄} (hx : Causal.Flat.IsFutureCausal x) (hx0 : x ≠ 0)
    (hy : Causal.Flat.IsFutureTimelike y) {ε : ℝ} (hε : 0 < ε) :
    Causal.Flat.IsFutureTimelike (x + ε • y) := by
  have hB := Causal.Flat.minkB_neg_of_future hx hx0 hy
  refine ⟨?_, ?_⟩
  · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
    nlinarith [hx.1, hy.1]
  · rw [Causal.Flat.minkQ_add, Causal.Flat.minkQ_smul, Causal.Flat.minkB_smul_right]
    nlinarith [hx.2, hy.2, sq_nonneg ε]

/-- A timelike vector with `minkB` negative against a nonzero future causal one is future. -/
theorem isFutureTimelike_of_minkB_neg {v u : 𝕄} (hv : Causal.Flat.minkQ v < 0)
    (hu : Causal.Flat.IsFutureCausal u) (hu0 : u ≠ 0) (hB : Causal.Flat.minkB u v < 0) :
    Causal.Flat.IsFutureTimelike v := by
  rcases Causal.Flat.isFutureTimelike_or_neg hv with h | h
  · exact h
  · have := Causal.Flat.minkB_neg_of_future hu hu0 h
    rw [Causal.Flat.minkB_neg_right] at this
    linarith

/-- **A `minkQ`-preserving automorphism of determinant `1` fixing a nonzero causal vector lies in
`SO₀(1,2)`.** -/
theorem mem_lorentz_of_fix {A : 𝕄 ≃ₗ[ℝ] 𝕄}
    (hQ : ∀ v, Causal.Flat.minkQ (A v) = Causal.Flat.minkQ v)
    (hdet : LinearMap.det (A : 𝕄 →ₗ[ℝ] 𝕄) = 1) {u : 𝕄} (hu : Causal.Flat.minkQ u ≤ 0)
    (hu0 : u ≠ 0) (hAu : A u = u) : A ∈ Causal.Flat.lorentz 2 := by
  have hB : ∀ v w, Causal.Flat.minkB (A v) (A w) = Causal.Flat.minkB v w :=
    Causal.Flat.minkB_map_of_minkQ (A := (A : 𝕄 →ₗ[ℝ] 𝕄)) hQ
  set e := Causal.Flat.timeUnit 2
  have he : Causal.Flat.IsFutureTimelike e := ⟨by simp [e, Causal.Flat.timeUnit], by simp [e]⟩
  have hu1 : u.1 ≠ 0 := fun h => hu0 (Causal.Flat.eq_zero_of_fst_eq_zero h hu)
  obtain ⟨u', hu', hu'0, hAu'⟩ : ∃ u' : 𝕄, Causal.Flat.IsFutureCausal u' ∧ u' ≠ 0 ∧ A u' = u' := by
    rcases lt_or_gt_of_ne hu1 with h | h
    · exact ⟨-u, ⟨by simp; linarith, by simpa using hu⟩, neg_ne_zero.2 hu0, by rw [map_neg, hAu]⟩
    · exact ⟨u, ⟨h.le, hu⟩, hu0, hAu⟩
  have h1 := Causal.Flat.minkB_neg_of_future hu' hu'0 he
  refine Causal.Flat.mem_lorentz_of_future hQ he ?_ hdet
  refine isFutureTimelike_of_minkB_neg (by rw [hQ]; exact he.2) hu' hu'0 ?_
  rw [← hAu', hB]
  exact h1

end Cones

/-! ### `p ∈ dS²`: the future and past directions (`bbsdef:lies_denote_respectively_set`) -/

section DeSitter

variable (p : HS 2)

/-- `w ↦ Q(p) w − B(p, w) p`, `Q(p)` times the `minkB`-orthogonal projection onto `p^⊥`; it kills
`ℝ p`. -/
def perpLin : 𝕄 →ₗ[ℝ] 𝕄 where
  toFun w := Causal.Flat.minkQ (p : 𝕄) • w - Causal.Flat.minkB (p : 𝕄) w • (p : 𝕄)
  map_add' v w := by rw [Causal.Flat.minkB_add_right]; module
  map_smul' c w := by rw [Causal.Flat.minkB_smul_right]; simp only [RingHom.id_apply]; module

theorem perpLin_apply (w : 𝕄) :
    perpLin p w = Causal.Flat.minkQ (p : 𝕄) • w - Causal.Flat.minkB (p : 𝕄) w • (p : 𝕄) := rfl

theorem perpLin_self : perpLin p (p : 𝕄) = 0 := by
  rw [perpLin_apply, ← Causal.Flat.minkQ_eq_minkB, sub_self]

/-- **`T_p HS² → p^⊥`**: for `p ∈ dS²`, the tangent plane of de Sitter space at `p` is `p^⊥`, and
`T_p HS² = ℝ^{1,2}/ℝp ≅ p^⊥` by the orthogonal projection (up to the factor `Q(p) > 0`). -/
def dsProj : TpHS p →ₗ[ℝ] 𝕄 :=
  (ℝ ∙ (p : 𝕄)).liftQ (perpLin p) (by
    rw [Submodule.span_le]
    rintro _ rfl
    exact perpLin_self p)

theorem dsProj_mk (w : 𝕄) : dsProj p (tpMk p w) = perpLin p w := rfl

theorem continuous_dsProj : Continuous fun σ : Link p => dsProj p σ :=
  (LinearMap.continuous_of_finiteDimensional (dsProj p)).comp continuous_subtype_val

theorem minkB_perpLin (w : 𝕄) : Causal.Flat.minkB (p : 𝕄) (perpLin p w) = 0 := by
  rw [perpLin_apply, Causal.Flat.minkB_sub_right, Causal.Flat.minkB_smul_right,
    Causal.Flat.minkB_smul_right, ← Causal.Flat.minkQ_eq_minkB]; ring

theorem minkB_dsProj (z : TpHS p) : Causal.Flat.minkB (p : 𝕄) (dsProj p z) = 0 := by
  induction z using Submodule.Quotient.induction_on with
  | H w => exact minkB_perpLin p w

/-- `B(p, A w) = B(p, w)` for `A ∈ Γ_p`. -/
theorem minkB_gammaP (A : GammaP p) (w : 𝕄) :
    Causal.Flat.minkB (p : 𝕄) (((A : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄) w) =
      Causal.Flat.minkB (p : 𝕄) w := by
  have h := Causal.Flat.lorentz.minkB_apply (A : Causal.Flat.lorentz 2).2 (p : 𝕄) w
  rwa [show ((A : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄) (p : 𝕄) = p from A.2] at h

theorem perpLin_gammaP (A : GammaP p) (w : 𝕄) :
    perpLin p (((A : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄) w) =
      ((A : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄) (perpLin p w) := by
  rw [perpLin_apply, perpLin_apply, minkB_gammaP, map_sub, map_smul, map_smul,
    show ((A : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄) (p : 𝕄) = p from A.2]

theorem dsProj_tangent (A : GammaP p) (z : TpHS p) :
    dsProj p (GammaP.tangent A z) =
      ((A : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄) (dsProj p z) := by
  induction z using Submodule.Quotient.induction_on with
  | H w => exact perpLin_gammaP p A w

theorem perpLin_eq_zero_iff (hp : Causal.Flat.minkQ (p : 𝕄) ≠ 0) {w : 𝕄} :
    perpLin p w = 0 ↔ tpMk p w = 0 := by
  rw [tpMk_eq_zero_iff]
  constructor
  · intro h
    refine ⟨Causal.Flat.minkB (p : 𝕄) w / Causal.Flat.minkQ (p : 𝕄), ?_⟩
    rw [perpLin_apply, sub_eq_zero] at h
    rw [div_eq_inv_mul, mul_smul, ← h, smul_smul, inv_mul_cancel₀ hp, one_smul]
  · rintro ⟨c, rfl⟩
    rw [map_smul, perpLin_self, smul_zero]

theorem dsProj_injective (hp : Causal.Flat.minkQ (p : 𝕄) ≠ 0) : Function.Injective (dsProj p) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro z hz
  induction z using Submodule.Quotient.induction_on with
  | H w => exact (perpLin_eq_zero_iff p hp).1 hz

theorem dsProj_ne_zero (hp : Causal.Flat.minkQ (p : 𝕄) ≠ 0) (σ : Link p) : dsProj p σ ≠ 0 :=
  fun h => raySphere_ne_zero σ (dsProj_injective p hp (h.trans (map_zero _).symm))

theorem dsProj_dirOf {w : 𝕄} (hw : tpMk p w ≠ 0) :
    dsProj p (dirOf p w) = ‖tpMk p w‖⁻¹ • perpLin p w := by
  rw [coe_dirOf p hw, map_smul, dsProj_mk]

theorem tangent_ne_zero (A : GammaP p) (σ : Link p) : GammaP.tangent A σ ≠ 0 :=
  (LinearEquiv.map_ne_zero_iff _).2 (raySphere_ne_zero σ)

theorem dsProj_smul (A : GammaP p) (σ : Link p) :
    dsProj p (A • σ : Link p) =
      ‖GammaP.tangent A σ‖⁻¹ • ((A : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄) (dsProj p σ) := by
  rw [gammaP_smul_def, coe_linRaySmul, map_smul, dsProj_tangent]

/-- `bbsdef:lies_denote_respectively_set` (`colI_v1.tex:819–822`), `i⁺(ℓ(p))` for `p ∈ dS²`:
the future oriented directions of the Lorentzian plane `T_p dS² = p^⊥`, read as the future
**timelike** directions (SCOPE). -/
def dsFutureDirs : Set (Link p) := {σ | Causal.Flat.IsFutureTimelike (dsProj p σ)}

/-- `i⁻(ℓ(p))` for `p ∈ dS²`: the past (timelike) directions. -/
def dsPastDirs : Set (Link p) := {σ | Causal.Flat.IsFutureTimelike (-dsProj p σ)}

theorem isOpen_dsFutureDirs : IsOpen (dsFutureDirs p) :=
  isOpen_isFutureTimelike.preimage (continuous_dsProj p)

theorem isOpen_dsPastDirs : IsOpen (dsPastDirs p) :=
  isOpen_isFutureTimelike.preimage (continuous_dsProj p).neg

theorem smul_mem_dsFutureDirs_iff (A : GammaP p) {σ : Link p} :
    A • σ ∈ dsFutureDirs p ↔ σ ∈ dsFutureDirs p := by
  show Causal.Flat.IsFutureTimelike (dsProj p (A • σ : Link p)) ↔
    Causal.Flat.IsFutureTimelike (dsProj p σ)
  rw [dsProj_smul, HS.isFutureTimelike_smul_iff (inv_pos.2 (norm_pos_iff.2 (tangent_ne_zero p A σ))),
    Causal.Flat.lorentz.isFutureTimelike_apply_iff (A : Causal.Flat.lorentz 2).2]

theorem smul_mem_dsPastDirs_iff (A : GammaP p) {σ : Link p} :
    A • σ ∈ dsPastDirs p ↔ σ ∈ dsPastDirs p := by
  show Causal.Flat.IsFutureTimelike (-dsProj p (A • σ : Link p)) ↔
    Causal.Flat.IsFutureTimelike (-dsProj p σ)
  rw [dsProj_smul, ← smul_neg, ← map_neg,
    HS.isFutureTimelike_smul_iff (inv_pos.2 (norm_pos_iff.2 (tangent_ne_zero p A σ))),
    Causal.Flat.lorentz.isFutureTimelike_apply_iff (A : Causal.Flat.lorentz 2).2]

/-- The complement of `i⁺ ∪ i⁻` is the set of non-timelike directions. -/
theorem compl_dsFutureDirs_union :
    (dsFutureDirs p ∪ dsPastDirs p)ᶜ = {σ : Link p | 0 ≤ Causal.Flat.minkQ (dsProj p σ)} := by
  ext σ
  simp only [mem_compl_iff, mem_union, not_or, mem_setOf_eq, dsFutureDirs, dsPastDirs]
  constructor
  · rintro ⟨h1, h2⟩
    by_contra hlt
    rcases Causal.Flat.isFutureTimelike_or_neg (not_le.1 hlt) with h | h
    · exact h1 h
    · exact h2 h
  · intro h
    refine ⟨fun h' => absurd h'.2 (not_lt.2 h), fun h' => ?_⟩
    have h2 := h'.2
    rw [Causal.Flat.minkQ_neg] at h2
    exact absurd h2 (not_lt.2 h)

/-- The time unit projects to a future timelike vector of `p^⊥` when `Q(p) > 0`. -/
theorem isFutureTimelike_perpLin_timeUnit (hp : 0 < Causal.Flat.minkQ (p : 𝕄)) :
    Causal.Flat.IsFutureTimelike (perpLin p (Causal.Flat.timeUnit 2)) := by
  have hB : Causal.Flat.minkB (p : 𝕄) (Causal.Flat.timeUnit 2) = -(p : 𝕄).1 := by
    simp [Causal.Flat.minkB, Causal.Flat.timeUnit]
  have hB' : Causal.Flat.minkB (Causal.Flat.timeUnit 2) (p : 𝕄) = -(p : 𝕄).1 := by
    rw [Causal.Flat.minkB_comm, hB]
  have he : perpLin p (Causal.Flat.timeUnit 2) =
      Causal.Flat.minkQ (p : 𝕄) • Causal.Flat.timeUnit 2 + (p : 𝕄).1 • (p : 𝕄) := by
    rw [perpLin_apply, hB, neg_smul, sub_neg_eq_add]
  rw [he]
  refine ⟨?_, ?_⟩
  · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul, Causal.Flat.timeUnit, mul_one]
    nlinarith [sq_nonneg (p : 𝕄).1]
  · rw [Causal.Flat.minkQ_add, Causal.Flat.minkQ_smul, Causal.Flat.minkQ_smul,
      Causal.Flat.minkB_smul_left, Causal.Flat.minkB_smul_right, hB', Causal.Flat.minkQ_timeUnit]
    nlinarith [sq_nonneg (p : 𝕄).1]

theorem tpMk_timeUnit_ne_zero (hp : 0 < Causal.Flat.minkQ (p : 𝕄)) :
    tpMk p (Causal.Flat.timeUnit 2) ≠ 0 := fun h => by
  have h1 := isFutureTimelike_perpLin_timeUnit p hp
  rw [(perpLin_eq_zero_iff p hp.ne').2 h] at h1
  exact lt_irrefl _ h1.1

/-- `(0, J p₁)`: a spacelike vector orthogonal to `p`, of norm `‖p₁‖`. -/
def jVec : 𝕄 := ((0 : ℝ), jRot (p : 𝕄).2)

theorem minkB_jVec : Causal.Flat.minkB (jVec p) (p : 𝕄) = 0 := by
  rw [minkB_two]; simp only [jVec, jRot_zero, jRot_one]; ring

theorem minkQ_jVec : Causal.Flat.minkQ (jVec p) = ‖(p : 𝕄).2‖ ^ 2 := by
  rw [minkQ_two, norm_sq_two]; simp only [jVec, jRot_zero, jRot_one]; ring

/-- The pairing with `jVec p`, on `T_p HS²`. -/
def jPairing : TpHS p →ₗ[ℝ] ℝ :=
  (ℝ ∙ (p : 𝕄)).liftQ (Causal.Flat.minkForm 2 (jVec p)) (by
    rw [Submodule.span_le]
    rintro _ rfl
    exact minkB_jVec p)

theorem jPairing_mk (w : 𝕄) : jPairing p (tpMk p w) = Causal.Flat.minkB (jVec p) w := rfl

theorem continuous_jPairing : Continuous fun σ : Link p => jPairing p σ :=
  (LinearMap.continuous_of_finiteDimensional (jPairing p)).comp continuous_subtype_val

/-- **The coordinate identity** at a ray `v` with `‖v₁‖ = 1`:
`Q(Q(v) w − B(v,w) v) = Q(v) (−t² + Q(v) β²)`, `t` the time component, `β = B((0, J v₁), w)`. -/
theorem minkQ_perp_eq {v : 𝕄} (hv : ‖v.2‖ = 1) (w : 𝕄) :
    Causal.Flat.minkQ (Causal.Flat.minkQ v • w - Causal.Flat.minkB v w • v) =
      Causal.Flat.minkQ v * (-(Causal.Flat.minkQ v • w - Causal.Flat.minkB v w • v).1 ^ 2 +
        Causal.Flat.minkQ v * Causal.Flat.minkB ((0 : ℝ), jRot v.2) w ^ 2) := by
  obtain ⟨t, x⟩ := v
  obtain ⟨w0, y⟩ := w
  have hx : x 0 ^ 2 + x 1 ^ 2 = 1 := by rw [← norm_sq_two, show ‖x‖ = 1 from hv, one_pow]
  simp only [minkQ_two, minkB_two, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd,
    PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, jRot_zero, jRot_one]
  linear_combination (-(-t ^ 2 + x 0 ^ 2 + x 1 ^ 2) * (-t ^ 2 * y 0 ^ 2 - t ^ 2 * y 1 ^ 2 +
    2 * t * w0 * x 0 * y 0 + 2 * t * w0 * x 1 * y 1 - w0 ^ 2 * x 0 ^ 2 - w0 ^ 2 * x 1 ^ 2 +
    x 0 ^ 2 * y 1 ^ 2 - 2 * x 0 * x 1 * y 0 * y 1 + x 1 ^ 2 * y 0 ^ 2)) * hx

theorem norm_snd_of_deSitter {p : HS 2} (hp : p ∈ HS.piece 2 .deSitter) : ‖(p : 𝕄).2‖ = 1 :=
  (HS.mem_deSitter_iff.1 hp).2

theorem jPairing_dirOf {w : 𝕄} (hw : tpMk p w ≠ 0) :
    jPairing p (dirOf p w) = ‖tpMk p w‖⁻¹ * Causal.Flat.minkB (jVec p) w := by
  rw [coe_dirOf p hw, map_smul, jPairing_mk, smul_eq_mul]

theorem dsProj_neg (σ : Link p) : dsProj p ((-σ : Link p) : TpHS p) = -dsProj p σ := by
  rw [coe_neg_sphere, map_neg]

theorem jPairing_neg (σ : Link p) : jPairing p ((-σ : Link p) : TpHS p) = -jPairing p σ := by
  rw [coe_neg_sphere, map_neg]

theorem tpMk_jVec_ne_zero (hp1 : ‖(p : 𝕄).2‖ = 1) : tpMk p (jVec p) ≠ 0 := fun h => by
  obtain ⟨c, hc⟩ := (tpMk_eq_zero_iff p).1 h
  have h2 : Causal.Flat.minkQ (jVec p) = 0 := by
    rw [Causal.Flat.minkQ_eq_minkB]
    nth_rewrite 2 [hc]
    rw [Causal.Flat.minkB_smul_right, minkB_jVec, mul_zero]
  rw [minkQ_jVec, hp1] at h2
  norm_num at h2

/-- Moving a direction `σ` towards the time unit: `[w + ε e] → σ` as `ε → 0⁺`. -/
theorem tendsto_dirOf_add (σ : Link p) (e : 𝕄) :
    Tendsto (fun ε : ℝ => dirOf p (liftT p σ + ε • e)) (𝓝[>] 0) (𝓝 σ) := by
  have hw : tpMk p (liftT p σ) = σ := tpMk_liftT p σ
  have hcont : ContinuousAt (dirOf p) (liftT p σ) :=
    (continuousAt_rayNormalize _ (by rw [hw]; exact raySphere_ne_zero σ)).comp
      (continuous_tpMk p).continuousAt
  have h1 : Tendsto (fun ε : ℝ => liftT p σ + ε • e) (𝓝 0) (𝓝 (liftT p σ)) := by
    have : Continuous fun ε : ℝ => liftT p σ + ε • e := by fun_prop
    simpa using this.tendsto 0
  have := (hcont.tendsto.comp h1).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  rwa [Function.comp_def, dirOf_eq p hw] at this

variable {p} in
/-- A future lightlike direction at `p ∈ dS²` is a limit of future timelike ones. -/
theorem mem_closure_dsFutureDirs (hQ : 0 < Causal.Flat.minkQ (p : 𝕄)) {σ : Link p}
    (hx : Causal.Flat.IsFutureCausal (dsProj p σ)) : σ ∈ closure (dsFutureDirs p) := by
  set w := liftT p σ
  set e := Causal.Flat.timeUnit 2
  have hw : tpMk p w = σ := tpMk_liftT p σ
  have hy := isFutureTimelike_perpLin_timeUnit p hQ
  have hx0 : dsProj p σ ≠ 0 := dsProj_ne_zero p hQ.ne' σ
  have hperp : ∀ ε : ℝ, perpLin p (w + ε • e) = dsProj p σ + ε • perpLin p e := fun ε => by
    rw [map_add, map_smul, ← dsProj_mk, hw]
  refine mem_closure_of_tendsto (tendsto_dirOf_add p σ e) ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  have hFT := isFutureTimelike_add_smul hx hx0 hy hε
  have hne : tpMk p (w + ε • e) ≠ 0 := fun h0 => by
    rw [← perpLin_eq_zero_iff p hQ.ne', hperp] at h0
    rw [h0] at hFT
    exact lt_irrefl _ hFT.1
  show Causal.Flat.IsFutureTimelike (dsProj p (dirOf p (w + ε • e)))
  rw [dsProj_dirOf p hne, HS.isFutureTimelike_smul_iff (inv_pos.2 (norm_pos_iff.2 hne)), hperp]
  exact hFT

variable {p} in
/-- A past lightlike direction at `p ∈ dS²` is a limit of past timelike ones. -/
theorem mem_closure_dsPastDirs (hQ : 0 < Causal.Flat.minkQ (p : 𝕄)) {σ : Link p}
    (hx : Causal.Flat.IsFutureCausal (-dsProj p σ)) : σ ∈ closure (dsPastDirs p) := by
  set w := liftT p σ
  set e := -Causal.Flat.timeUnit 2
  have hw : tpMk p w = σ := tpMk_liftT p σ
  have hy := isFutureTimelike_perpLin_timeUnit p hQ
  have hx0 : -dsProj p σ ≠ 0 := neg_ne_zero.2 (dsProj_ne_zero p hQ.ne' σ)
  have hperp : ∀ ε : ℝ, -perpLin p (w + ε • e) =
      -dsProj p σ + ε • perpLin p (Causal.Flat.timeUnit 2) := fun ε => by
    rw [map_add, map_smul, ← dsProj_mk, hw, map_neg, neg_add, smul_neg, neg_neg]
  refine mem_closure_of_tendsto (tendsto_dirOf_add p σ e) ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  have hFT := isFutureTimelike_add_smul hx hx0 hy hε
  have hne : tpMk p (w + ε • e) ≠ 0 := fun h0 => by
    rw [← perpLin_eq_zero_iff p hQ.ne'] at h0
    rw [← hperp, h0, neg_zero] at hFT
    exact lt_irrefl _ hFT.1
  show Causal.Flat.IsFutureTimelike (-dsProj p (dirOf p (w + ε • e)))
  rw [dsProj_dirOf p hne, ← smul_neg, HS.isFutureTimelike_smul_iff (inv_pos.2 (norm_pos_iff.2 hne)),
    hperp]
  exact hFT

variable {p} in
/-- The extremities of `i^±(ℓ(p))`, `p ∈ dS²`, are the four lightlike directions. -/
theorem frontier_ds (hp : p ∈ HS.piece 2 .deSitter) :
    frontier (dsFutureDirs p) ∪ frontier (dsPastDirs p) =
      {σ : Link p | Causal.Flat.minkQ (dsProj p σ) = 0} := by
  have hQ : 0 < Causal.Flat.minkQ (p : 𝕄) := hp
  ext σ
  rw [(isOpen_dsFutureDirs p).frontier_eq, (isOpen_dsPastDirs p).frontier_eq]
  simp only [mem_union, Set.mem_sdiff, mem_setOf_eq]
  have hx0 := dsProj_ne_zero p hQ.ne' σ
  constructor
  · rintro (⟨hc, hn⟩ | ⟨hc, hn⟩)
    · have hsub : dsFutureDirs p ⊆ (fun τ : Link p => dsProj p τ) ⁻¹'
          {v | Causal.Flat.IsFutureCausal v} := fun τ hτ => ⟨hτ.1.le, hτ.2.le⟩
      have hFC : Causal.Flat.IsFutureCausal (dsProj p σ) :=
        closure_minimal hsub (isClosed_isFutureCausal.preimage (continuous_dsProj p)) hc
      by_contra hne
      have hlt : Causal.Flat.minkQ (dsProj p σ) < 0 := lt_of_le_of_ne hFC.2 hne
      refine hn ⟨lt_of_le_of_ne hFC.1 fun h0 => ?_, hlt⟩
      exact hx0 (Causal.Flat.eq_zero_of_fst_eq_zero h0.symm hFC.2)
    · have hsub : dsPastDirs p ⊆ (fun τ : Link p => -dsProj p τ) ⁻¹'
          {v | Causal.Flat.IsFutureCausal v} := fun τ hτ => ⟨hτ.1.le, hτ.2.le⟩
      have hFC : Causal.Flat.IsFutureCausal (-dsProj p σ) :=
        closure_minimal hsub (isClosed_isFutureCausal.preimage (continuous_dsProj p).neg) hc
      by_contra hne
      have h2 : Causal.Flat.minkQ (dsProj p σ) ≤ 0 := by
        have := hFC.2; rwa [Causal.Flat.minkQ_neg] at this
      have hlt : Causal.Flat.minkQ (-dsProj p σ) < 0 := by
        rw [Causal.Flat.minkQ_neg]; exact lt_of_le_of_ne h2 hne
      refine hn ⟨lt_of_le_of_ne hFC.1 fun h0 => ?_, hlt⟩
      exact hx0 (neg_eq_zero.1 (Causal.Flat.eq_zero_of_fst_eq_zero h0.symm hFC.2))
  · intro h0
    have h1 : (dsProj p σ).1 ≠ 0 := fun h => hx0 (Causal.Flat.eq_zero_of_fst_eq_zero h h0.le)
    rcases lt_or_gt_of_ne h1 with hneg | hpos
    · refine Or.inr ⟨mem_closure_dsPastDirs hQ ⟨by simp; linarith, by simp [h0]⟩, fun h => ?_⟩
      have := h.2
      rw [Causal.Flat.minkQ_neg, h0] at this
      exact lt_irrefl _ this
    · refine Or.inl ⟨mem_closure_dsFutureDirs hQ ⟨hpos.le, h0.le⟩, fun h => ?_⟩
      have := h.2
      rw [h0] at this
      exact lt_irrefl _ this

variable {p}

/-- **l.824**: `i⁺(ℓ(p))` is connected. -/
theorem isConnected_dsFutureDirs (hp : p ∈ HS.piece 2 .deSitter) : IsConnected (dsFutureDirs p) := by
  have hQ : 0 < Causal.Flat.minkQ (p : 𝕄) := hp
  refine ⟨⟨dirOf p (Causal.Flat.timeUnit 2), ?_⟩, ?_⟩
  · show Causal.Flat.IsFutureTimelike (dsProj p (dirOf p _))
    rw [dsProj_dirOf p (tpMk_timeUnit_ne_zero p hQ), HS.isFutureTimelike_smul_iff
      (inv_pos.2 (norm_pos_iff.2 (tpMk_timeUnit_ne_zero p hQ)))]
    exact isFutureTimelike_perpLin_timeUnit p hQ
  · have himg := image_dirOf_eq p (P := fun z => Causal.Flat.IsFutureTimelike (dsProj p z))
      (fun c hc z => by rw [map_smul, HS.isFutureTimelike_smul_iff hc])
    have hset : {w | tpMk p w ≠ 0 ∧ Causal.Flat.IsFutureTimelike (dsProj p (tpMk p w))} =
        perpLin p ⁻¹' {v | Causal.Flat.IsFutureTimelike v} := by
      ext w
      simp only [mem_setOf_eq, mem_preimage, dsProj_mk]
      refine ⟨fun h => h.2, fun h => ⟨fun h0 => ?_, h⟩⟩
      rw [(perpLin_eq_zero_iff p hQ.ne').2 h0] at h
      exact lt_irrefl _ h.1
    rw [hset] at himg
    show IsPreconnected {σ : Link p | Causal.Flat.IsFutureTimelike (dsProj p σ)}
    rw [← himg]
    refine (convex_isFutureTimelike.linear_preimage (perpLin p)).isPreconnected.image _
      ((continuousOn_dirOf p).mono fun w hw => ?_)
    show tpMk p w ≠ 0
    intro h0
    have h : Causal.Flat.IsFutureTimelike (perpLin p w) := hw
    rw [(perpLin_eq_zero_iff p hQ.ne').2 h0] at h
    exact lt_irrefl _ h.1

/-- **l.824**: `i⁻(ℓ(p))` is connected. -/
theorem isConnected_dsPastDirs (hp : p ∈ HS.piece 2 .deSitter) : IsConnected (dsPastDirs p) := by
  have hQ : 0 < Causal.Flat.minkQ (p : 𝕄) := hp
  have hne : tpMk p (-Causal.Flat.timeUnit 2) ≠ 0 := by
    have : tpMk p (-Causal.Flat.timeUnit 2) = -tpMk p (Causal.Flat.timeUnit 2) :=
      Submodule.Quotient.mk_neg _
    rw [this, neg_ne_zero]; exact tpMk_timeUnit_ne_zero p hQ
  refine ⟨⟨dirOf p (-Causal.Flat.timeUnit 2), ?_⟩, ?_⟩
  · show Causal.Flat.IsFutureTimelike (-dsProj p (dirOf p _))
    rw [dsProj_dirOf p hne, map_neg, smul_neg, neg_neg,
      HS.isFutureTimelike_smul_iff (inv_pos.2 (norm_pos_iff.2 hne))]
    exact isFutureTimelike_perpLin_timeUnit p hQ
  · have himg := image_dirOf_eq p (P := fun z => Causal.Flat.IsFutureTimelike (-dsProj p z))
      (fun c hc z => by rw [map_smul, ← smul_neg, HS.isFutureTimelike_smul_iff hc])
    have hset : {w | tpMk p w ≠ 0 ∧ Causal.Flat.IsFutureTimelike (-dsProj p (tpMk p w))} =
        (-perpLin p) ⁻¹' {v | Causal.Flat.IsFutureTimelike v} := by
      ext w
      simp only [mem_setOf_eq, mem_preimage, dsProj_mk, LinearMap.neg_apply]
      refine ⟨fun h => h.2, fun h => ⟨fun h0 => ?_, h⟩⟩
      rw [(perpLin_eq_zero_iff p hQ.ne').2 h0, neg_zero] at h
      exact lt_irrefl _ h.1
    rw [hset] at himg
    show IsPreconnected {σ : Link p | Causal.Flat.IsFutureTimelike (-dsProj p σ)}
    rw [← himg]
    refine (convex_isFutureTimelike.linear_preimage (-perpLin p)).isPreconnected.image _
      ((continuousOn_dirOf p).mono fun w hw => ?_)
    show tpMk p w ≠ 0
    intro h0
    have h : Causal.Flat.IsFutureTimelike ((-perpLin p) w) := hw
    rw [LinearMap.neg_apply, (perpLin_eq_zero_iff p hQ.ne').2 h0, neg_zero] at h
    exact lt_irrefl _ h.1

/-- On the non-timelike directions at `p ∈ dS²`, the pairing with `jVec p` does not vanish. -/
theorem jPairing_ne_zero_of_deSitter (hp : p ∈ HS.piece 2 .deSitter) {σ : Link p}
    (hσ : 0 ≤ Causal.Flat.minkQ (dsProj p σ)) : jPairing p σ ≠ 0 := by
  intro h0
  have hQ : 0 < Causal.Flat.minkQ (p : 𝕄) := hp
  set w := liftT p σ
  have hw : tpMk p w = σ := tpMk_liftT p σ
  have hid := minkQ_perp_eq (norm_snd_of_deSitter hp) w
  change Causal.Flat.minkQ (perpLin p w) = Causal.Flat.minkQ (p : 𝕄) *
    (-(perpLin p w).1 ^ 2 + Causal.Flat.minkQ (p : 𝕄) * Causal.Flat.minkB (jVec p) w ^ 2) at hid
  have hd : dsProj p σ = perpLin p w := by rw [← hw]; rfl
  have hβ : Causal.Flat.minkB (jVec p) w = 0 := by rw [← jPairing_mk, hw]; exact h0
  rw [hd] at hσ
  rw [hβ] at hid
  have h1 : (perpLin p w).1 ^ 2 = 0 := by nlinarith [sq_nonneg (perpLin p w).1]
  have h1' : (perpLin p w).1 = 0 := pow_eq_zero_iff two_ne_zero |>.1 h1
  have h2 : Causal.Flat.minkQ (perpLin p w) = 0 := by rw [hid, h1']; ring
  exact dsProj_ne_zero p hQ.ne' σ (hd.trans (Causal.Flat.eq_zero_of_fst_eq_zero h1' h2.le))

/-- The non-timelike directions on the side `jPairing ≥ 0` are the image of a convex cone. -/
theorem image_dsSide (hp : p ∈ HS.piece 2 .deSitter) :
    {σ : Link p | 0 ≤ Causal.Flat.minkQ (dsProj p σ) ∧ 0 ≤ jPairing p σ} =
      dirOf p '' {w | |(perpLin p w).1| ≤ Real.sqrt (Causal.Flat.minkQ (p : 𝕄)) *
        Causal.Flat.minkB (jVec p) w ∧ 0 < Causal.Flat.minkB (jVec p) w} := by
  have hQ : 0 < Causal.Flat.minkQ (p : 𝕄) := hp
  set k := Real.sqrt (Causal.Flat.minkQ (p : 𝕄))
  have hk : k ^ 2 = Causal.Flat.minkQ (p : 𝕄) := Real.sq_sqrt hQ.le
  have hk0 : 0 ≤ k := Real.sqrt_nonneg _
  have himg := image_dirOf_eq p
    (P := fun z => 0 ≤ Causal.Flat.minkQ (dsProj p z) ∧ 0 ≤ jPairing p z) (fun c hc z => by
      simp only [map_smul, Causal.Flat.minkQ_smul, smul_eq_mul]
      rw [mul_nonneg_iff_of_pos_left (pow_pos hc 2), mul_nonneg_iff_of_pos_left hc])
  rw [← himg]
  congr 1
  ext w
  have hid := minkQ_perp_eq (norm_snd_of_deSitter hp) w
  change Causal.Flat.minkQ (perpLin p w) = Causal.Flat.minkQ (p : 𝕄) *
    (-(perpLin p w).1 ^ 2 + Causal.Flat.minkQ (p : 𝕄) * Causal.Flat.minkB (jVec p) w ^ 2) at hid
  simp only [mem_setOf_eq, dsProj_mk, jPairing_mk]
  constructor
  · rintro ⟨hw, hq, hb⟩
    have hsq : (perpLin p w).1 ^ 2 ≤ (k * Causal.Flat.minkB (jVec p) w) ^ 2 := by
      rw [mul_pow, hk]; nlinarith
    have habs : |(perpLin p w).1| ≤ k * Causal.Flat.minkB (jVec p) w :=
      abs_le_of_sq_le_sq' hsq (mul_nonneg hk0 hb) |> fun h => abs_le.2 h
    refine ⟨habs, lt_of_le_of_ne hb fun h0 => hw ?_⟩
    rw [← h0, mul_zero] at habs
    have h1' : (perpLin p w).1 = 0 := abs_nonpos_iff.1 habs
    have h2 : Causal.Flat.minkQ (perpLin p w) = 0 := by rw [hid, h1', ← h0]; ring
    exact (perpLin_eq_zero_iff p hQ.ne').1 (Causal.Flat.eq_zero_of_fst_eq_zero h1' h2.le)
  · rintro ⟨habs, hb⟩
    refine ⟨fun h0 => ?_, ?_, hb.le⟩
    · obtain ⟨c, hc⟩ := (tpMk_eq_zero_iff p).1 h0
      rw [hc, Causal.Flat.minkB_smul_right, minkB_jVec, mul_zero] at hb
      exact lt_irrefl _ hb
    · have hsq : (perpLin p w).1 ^ 2 ≤ (k * Causal.Flat.minkB (jVec p) w) ^ 2 :=
        sq_le_sq' (by linarith [neg_abs_le (perpLin p w).1]) (le_trans (le_abs_self _) habs)
      rw [hid, mul_pow, hk] at *
      nlinarith

theorem convex_dsSide (p : HS 2) (k : ℝ) :
    Convex ℝ {w : 𝕄 | |(perpLin p w).1| ≤ k * Causal.Flat.minkB (jVec p) w ∧
      0 < Causal.Flat.minkB (jVec p) w} := by
  intro x hx y hy a b ha hb hab
  have hα : (perpLin p (a • x + b • y)).1 = a * (perpLin p x).1 + b * (perpLin p y).1 := by
    simp only [map_add, map_smul, Prod.fst_add, Prod.smul_fst, smul_eq_mul]
  have hβ : Causal.Flat.minkB (jVec p) (a • x + b • y) =
      a * Causal.Flat.minkB (jVec p) x + b * Causal.Flat.minkB (jVec p) y := by
    rw [Causal.Flat.minkB_add_right, Causal.Flat.minkB_smul_right, Causal.Flat.minkB_smul_right]
  simp only [mem_setOf_eq] at hx hy ⊢
  rw [hα, hβ]
  refine ⟨?_, ?_⟩
  · calc |a * (perpLin p x).1 + b * (perpLin p y).1|
        ≤ a * |(perpLin p x).1| + b * |(perpLin p y).1| := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
      _ ≤ a * (k * Causal.Flat.minkB (jVec p) x) + b * (k * Causal.Flat.minkB (jVec p) y) := by
          gcongr
          · exact hx.1
          · exact hy.1
      _ = k * (a * Causal.Flat.minkB (jVec p) x + b * Causal.Flat.minkB (jVec p) y) := by ring
  · rcases ha.lt_or_eq with ha' | ha'
    · nlinarith [mul_pos ha' hx.2, mul_nonneg hb hy.2.le]
    · subst ha'
      have hb1 : b = 1 := by linarith
      subst hb1
      simpa using hy.2

/-- **l.824**: the complement of `i⁺(ℓ(p)) ∪ i⁻(ℓ(p))` (the spacelike and lightlike directions)
has exactly two connected components. -/
theorem ncard_components_compl_ds (hp : p ∈ HS.piece 2 .deSitter) :
    {K | ∃ σ ∈ (dsFutureDirs p ∪ dsPastDirs p)ᶜ,
      connectedComponentIn (dsFutureDirs p ∪ dsPastDirs p)ᶜ σ = K}.ncard = 2 := by
  have hQ : 0 < Causal.Flat.minkQ (p : 𝕄) := hp
  have hp1 := norm_snd_of_deSitter hp
  set S₁ : Set (Link p) := {σ | 0 ≤ Causal.Flat.minkQ (dsProj p σ) ∧ 0 ≤ jPairing p σ}
  set S₂ : Set (Link p) := {σ | 0 ≤ Causal.Flat.minkQ (dsProj p σ) ∧ jPairing p σ ≤ 0}
  have hS : (dsFutureDirs p ∪ dsPastDirs p)ᶜ = S₁ ∪ S₂ := by
    rw [compl_dsFutureDirs_union]
    ext σ
    simp only [mem_setOf_eq, mem_union, S₁, S₂]
    constructor
    · intro h
      rcases le_total 0 (jPairing p σ) with h' | h'
      exacts [Or.inl ⟨h, h'⟩, Or.inr ⟨h, h'⟩]
    · rintro (h | h)
      exacts [h.1, h.1]
  have hneg : S₂ = (fun σ : Link p => -σ) '' S₁ := by
    ext σ
    simp only [mem_image, mem_setOf_eq, S₁, S₂]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨-σ, ⟨?_, ?_⟩, neg_neg σ⟩
      · rwa [dsProj_neg, Causal.Flat.minkQ_neg]
      · rw [jPairing_neg]; linarith
    · rintro ⟨τ, ⟨h1, h2⟩, rfl⟩
      refine ⟨?_, ?_⟩
      · rwa [dsProj_neg, Causal.Flat.minkQ_neg]
      · rw [jPairing_neg]; linarith
  have hc₁ : IsClosed S₁ :=
    (isClosed_le continuous_const (Causal.Flat.continuous_minkQ.comp (continuous_dsProj p))).inter
      (isClosed_le continuous_const (continuous_jPairing p))
  have hc₂ : IsClosed S₂ :=
    (isClosed_le continuous_const (Causal.Flat.continuous_minkQ.comp (continuous_dsProj p))).inter
      (isClosed_le (continuous_jPairing p) continuous_const)
  have hd : Disjoint S₁ S₂ := Set.disjoint_left.2 fun σ h1 h2 =>
    jPairing_ne_zero_of_deSitter hp h1.1 (le_antisymm h2.2 h1.2)
  have h₁ : IsPreconnected S₁ := by
    show IsPreconnected {σ : Link p | _}
    rw [image_dsSide hp]
    refine (convex_dsSide p _).isPreconnected.image _
      ((continuousOn_dirOf p).mono fun w hw => ?_)
    show tpMk p w ≠ 0
    intro h0
    obtain ⟨c, hc⟩ := (tpMk_eq_zero_iff p).1 h0
    have hb := hw.2
    rw [hc, Causal.Flat.minkB_smul_right, minkB_jVec, mul_zero] at hb
    exact lt_irrefl _ hb
  have h₂ : IsPreconnected S₂ := by
    rw [hneg]; exact h₁.image _ continuous_neg.continuousOn
  have hj := tpMk_jVec_ne_zero p hp1
  have hmem : dirOf p (jVec p) ∈ S₁ := by
    refine ⟨?_, ?_⟩
    · rw [dsProj_dirOf p hj, Causal.Flat.minkQ_smul, perpLin_apply,
        show Causal.Flat.minkB (p : 𝕄) (jVec p) = 0 by rw [Causal.Flat.minkB_comm]; exact minkB_jVec p,
        zero_smul, sub_zero, Causal.Flat.minkQ_smul, minkQ_jVec]
      positivity
    · rw [jPairing_dirOf p hj, ← Causal.Flat.minkQ_eq_minkB, minkQ_jVec]
      positivity
  have hn₁ : S₁.Nonempty := ⟨_, hmem⟩
  have hn₂ : S₂.Nonempty := ⟨_, hneg ▸ mem_image_of_mem _ hmem⟩
  rw [components_eq_pair hS (fun x hx => connectedComponentIn_eq_of_closed hS h₁ hc₁ hc₂ hd hx)
    (fun x hx => connectedComponentIn_eq_of_closed (hS.trans (union_comm _ _)) h₂ hc₂ hc₁ hd.symm hx)
    hn₁ hn₂]
  refine ncard_pair fun h => ?_
  obtain ⟨σ, hσ⟩ := hn₁
  exact Set.disjoint_left.1 hd hσ (h ▸ hσ)

variable (p) in
/-- `(1, t p₁)`: with `jVec p`, it spans `p^⊥` at `p ∈ dS²`. -/
def dsU : 𝕄 := ((1 : ℝ), (p : 𝕄).1 • (p : 𝕄).2)

theorem sum_sq_of_norm (hp1 : ‖(p : 𝕄).2‖ = 1) : (p : 𝕄).2 0 ^ 2 + (p : 𝕄).2 1 ^ 2 = 1 := by
  rw [← norm_sq_two, hp1, one_pow]

theorem minkB_dsU_self (hp1 : ‖(p : 𝕄).2‖ = 1) : Causal.Flat.minkB (dsU p) (p : 𝕄) = 0 := by
  have hx := sum_sq_of_norm hp1
  rw [minkB_two]
  simp only [dsU, PiLp.smul_apply, smul_eq_mul, one_mul]
  linear_combination (p : 𝕄).1 * hx

theorem minkQ_dsU (hp1 : ‖(p : 𝕄).2‖ = 1) :
    Causal.Flat.minkQ (dsU p) = -Causal.Flat.minkQ (p : 𝕄) := by
  have hx := sum_sq_of_norm hp1
  rw [minkQ_two, minkQ_two]
  simp only [dsU, PiLp.smul_apply, smul_eq_mul]
  linear_combination ((p : 𝕄).1 ^ 2 + 1) * hx

theorem minkB_dsU_jVec : Causal.Flat.minkB (dsU p) (jVec p) = 0 := by
  rw [minkB_two]
  simp only [dsU, jVec, PiLp.smul_apply, smul_eq_mul, jRot_zero, jRot_one]
  ring

theorem perpLin_fst (hp1 : ‖(p : 𝕄).2‖ = 1) (w : 𝕄) :
    (perpLin p w).1 = -Causal.Flat.minkB w (dsU p) := by
  have hx := sum_sq_of_norm hp1
  rw [perpLin_apply, minkQ_two, minkB_two, minkB_two]
  simp only [dsU, Prod.fst_sub, Prod.smul_fst, smul_eq_mul, PiLp.smul_apply]
  linear_combination w.1 * hx

theorem isFutureCausal_iff_norm {v : 𝕄} :
    Causal.Flat.IsFutureCausal v ↔ ‖v.2‖ ≤ v.1 := by
  rw [Causal.Flat.IsFutureCausal, Causal.Flat.minkQ_le_zero_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact abs_le_of_sq_le_sq' h2 h1 |>.2
  · intro h
    have h0 : 0 ≤ v.1 := le_trans (norm_nonneg _) h
    exact ⟨h0, pow_le_pow_left₀ (norm_nonneg _) h 2⟩

/-- The nonzero future causal vectors form a convex set. -/
theorem convex_isFutureCausal_ne_zero :
    Convex ℝ {v : 𝕄 | Causal.Flat.IsFutureCausal v ∧ 0 < v.1} := by
  intro x hx y hy a b ha hb hab
  simp only [mem_setOf_eq, isFutureCausal_iff_norm] at hx hy ⊢
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  refine ⟨?_, ?_⟩
  · calc ‖a • x.2 + b • y.2‖ ≤ a * ‖x.2‖ + b * ‖y.2‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
      _ ≤ a * x.1 + b * y.1 := by gcongr; exacts [hx.1, hy.1]
  · rcases ha.lt_or_eq with ha' | ha'
    · nlinarith [mul_pos ha' hx.2, mul_nonneg hb hy.2.le]
    · subst ha'
      have hb1 : b = 1 := by linarith
      subst hb1
      simpa using hy.2

/-- The complement of `i⁺(ℓ(p))` alone is connected (so l.824's "their complement" can only be
the complement of the union `i⁺(ℓ(p)) ∪ i⁻(ℓ(p))`). -/
theorem isConnected_compl_dsFutureDirs (hp : p ∈ HS.piece 2 .deSitter) :
    IsConnected (dsFutureDirs p)ᶜ := by
  have hQ : 0 < Causal.Flat.minkQ (p : 𝕄) := hp
  have hp1 := norm_snd_of_deSitter hp
  set S₁ : Set (Link p) := {σ | 0 ≤ Causal.Flat.minkQ (dsProj p σ) ∧ 0 ≤ jPairing p σ}
  set S₂ : Set (Link p) := {σ | 0 ≤ Causal.Flat.minkQ (dsProj p σ) ∧ jPairing p σ ≤ 0}
  set P : Set (Link p) := {σ | Causal.Flat.IsFutureCausal (-dsProj p σ)}
  have hS : (dsFutureDirs p)ᶜ = (S₁ ∪ P) ∪ S₂ := by
    ext σ
    simp only [mem_compl_iff, mem_union, mem_setOf_eq, dsFutureDirs, S₁, S₂, P]
    constructor
    · intro h
      by_cases hq : 0 ≤ Causal.Flat.minkQ (dsProj p σ)
      · rcases le_total 0 (jPairing p σ) with h' | h'
        exacts [Or.inl (Or.inl ⟨hq, h'⟩), Or.inr ⟨hq, h'⟩]
      · rcases Causal.Flat.isFutureTimelike_or_neg (not_le.1 hq) with h' | h'
        · exact absurd h' h
        · exact Or.inl (Or.inr ⟨h'.1.le, h'.2.le⟩)
    · rintro ((h | h) | h) hFT
      · exact absurd hFT.2 (not_lt.2 h.1)
      · have := h.1; simp only [Prod.fst_neg] at this; linarith [hFT.1]
      · exact absurd hFT.2 (not_lt.2 h.1)
  -- the three arcs are preconnected
  have h₁ : IsPreconnected S₁ := by
    show IsPreconnected {σ : Link p | _}
    rw [image_dsSide hp]
    refine (convex_dsSide p _).isPreconnected.image _ ((continuousOn_dirOf p).mono fun w hw => ?_)
    show tpMk p w ≠ 0
    intro h0
    obtain ⟨c, hc⟩ := (tpMk_eq_zero_iff p).1 h0
    have hb := hw.2
    rw [hc, Causal.Flat.minkB_smul_right, minkB_jVec, mul_zero] at hb
    exact lt_irrefl _ hb
  have hneg : S₂ = (fun σ : Link p => -σ) '' S₁ := by
    ext σ
    simp only [mem_image, mem_setOf_eq, S₁, S₂]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨-σ, ⟨?_, ?_⟩, neg_neg σ⟩
      · rwa [dsProj_neg, Causal.Flat.minkQ_neg]
      · rw [jPairing_neg]; linarith
    · rintro ⟨τ, ⟨h1, h2⟩, rfl⟩
      refine ⟨?_, ?_⟩
      · rwa [dsProj_neg, Causal.Flat.minkQ_neg]
      · rw [jPairing_neg]; linarith
  have h₂ : IsPreconnected S₂ := by rw [hneg]; exact h₁.image _ continuous_neg.continuousOn
  have hP : IsPreconnected P := by
    have himg := image_dirOf_eq p (P := fun z => Causal.Flat.IsFutureCausal (-dsProj p z))
      (fun c hc z => by rw [map_smul, ← smul_neg, HS.isFutureCausal_smul_iff hc])
    have hset : {w | tpMk p w ≠ 0 ∧ Causal.Flat.IsFutureCausal (-dsProj p (tpMk p w))} =
        (-perpLin p) ⁻¹' {v | Causal.Flat.IsFutureCausal v ∧ 0 < v.1} := by
      ext w
      simp only [mem_setOf_eq, mem_preimage, dsProj_mk, LinearMap.neg_apply]
      constructor
      · rintro ⟨hw, h⟩
        refine ⟨h, lt_of_le_of_ne h.1 fun h0 => hw ?_⟩
        rw [← perpLin_eq_zero_iff p hQ.ne', ← neg_eq_zero]
        exact Causal.Flat.eq_zero_of_fst_eq_zero h0.symm h.2
      · rintro ⟨h, h1⟩
        refine ⟨fun h0 => ?_, h⟩
        rw [(perpLin_eq_zero_iff p hQ.ne').2 h0, neg_zero] at h1
        exact lt_irrefl _ h1
    rw [hset] at himg
    show IsPreconnected {σ : Link p | _}
    rw [← himg]
    refine (convex_isFutureCausal_ne_zero.linear_preimage (-perpLin p)).isPreconnected.image _
      ((continuousOn_dirOf p).mono fun w hw => ?_)
    show tpMk p w ≠ 0
    intro h0
    have h : 0 < ((-perpLin p) w).1 := hw.2
    rw [LinearMap.neg_apply, (perpLin_eq_zero_iff p hQ.ne').2 h0, neg_zero] at h
    exact lt_irrefl _ h
  -- the past lightlike directions `[−u ± k jVec]` link the three arcs
  set k := Real.sqrt (Causal.Flat.minkQ (p : 𝕄))
  have hk : 0 < k := Real.sqrt_pos.2 hQ
  have hk2 : k ^ 2 = Causal.Flat.minkQ (p : 𝕄) := Real.sq_sqrt hQ.le
  have hpu : Causal.Flat.minkB (p : 𝕄) (dsU p) = 0 := by
    rw [Causal.Flat.minkB_comm]; exact minkB_dsU_self hp1
  have hpj : Causal.Flat.minkB (p : 𝕄) (jVec p) = 0 := by
    rw [Causal.Flat.minkB_comm]; exact minkB_jVec p
  have hjj : Causal.Flat.minkB (jVec p) (jVec p) = 1 := by
    rw [← Causal.Flat.minkQ_eq_minkB, minkQ_jVec, hp1, one_pow]
  have hju : Causal.Flat.minkB (jVec p) (dsU p) = 0 := by
    rw [Causal.Flat.minkB_comm]; exact minkB_dsU_jVec
  have link : ∀ ε : ℝ, ε ^ 2 = 1 → ∃ σ : Link p, σ ∈ P ∧ 0 ≤ Causal.Flat.minkQ (dsProj p σ) ∧
      0 < ε * jPairing p σ := by
    intro ε hε
    set w := -dsU p + (ε * k) • jVec p
    have hjw : Causal.Flat.minkB (jVec p) w = ε * k := by
      rw [Causal.Flat.minkB_add_right, Causal.Flat.minkB_neg_right, hju,
        Causal.Flat.minkB_smul_right, hjj]; ring
    have hw : tpMk p w ≠ 0 := fun h0 => by
      have := jPairing_mk p w
      rw [h0, map_zero, hjw] at this
      have : ε = 0 ∨ k = 0 := mul_eq_zero.1 this.symm
      rcases this with h | h
      · rw [h] at hε; norm_num at hε
      · exact hk.ne' h
    have hpw : Causal.Flat.minkB (p : 𝕄) w = 0 := by
      rw [Causal.Flat.minkB_add_right, Causal.Flat.minkB_neg_right, hpu,
        Causal.Flat.minkB_smul_right, hpj]; ring
    have hperp : perpLin p w = Causal.Flat.minkQ (p : 𝕄) • w := by
      rw [perpLin_apply, hpw, zero_smul, sub_zero]
    have hQw : Causal.Flat.minkQ w = 0 := by
      rw [Causal.Flat.minkQ_add, Causal.Flat.minkQ_neg, Causal.Flat.minkQ_smul, minkQ_dsU hp1,
        Causal.Flat.minkB_neg_left, Causal.Flat.minkB_smul_right, Causal.Flat.minkB_comm,
        hju, minkQ_jVec, hp1]
      rw [mul_pow, hε, hk2]; ring
    have hc : 0 < ‖tpMk p w‖⁻¹ := inv_pos.2 (norm_pos_iff.2 hw)
    refine ⟨dirOf p w, ?_, ?_, ?_⟩
    · show Causal.Flat.IsFutureCausal (-dsProj p (dirOf p w))
      rw [dsProj_dirOf p hw, hperp, smul_smul, ← smul_neg, HS.isFutureCausal_smul_iff
        (mul_pos hc hQ)]
      refine ⟨?_, by rw [Causal.Flat.minkQ_neg, hQw]⟩
      simp only [w, dsU, jVec, Prod.fst_neg, Prod.fst_add, Prod.smul_fst, smul_eq_mul, mul_zero,
        add_zero, neg_neg, zero_le_one]
    · rw [dsProj_dirOf p hw, hperp, smul_smul, Causal.Flat.minkQ_smul, hQw, mul_zero]
    · rw [jPairing_dirOf p hw, hjw]
      have : ε * (‖tpMk p w‖⁻¹ * (ε * k)) = ‖tpMk p w‖⁻¹ * k * ε ^ 2 := by ring
      rw [this, hε, mul_one]
      exact mul_pos hc hk
  obtain ⟨σ₁, hσ₁P, hσ₁q, hσ₁j⟩ := link 1 (by norm_num)
  obtain ⟨σ₂, hσ₂P, hσ₂q, hσ₂j⟩ := link (-1) (by norm_num)
  rw [one_mul] at hσ₁j
  have h1P : IsPreconnected (S₁ ∪ P) := h₁.union σ₁ ⟨hσ₁q, hσ₁j.le⟩ hσ₁P hP
  have hall : IsPreconnected ((S₁ ∪ P) ∪ S₂) :=
    h1P.union σ₂ (Or.inr hσ₂P) ⟨hσ₂q, by linarith⟩ h₂
  rw [hS]
  exact ⟨⟨σ₁, Or.inl (Or.inr hσ₁P)⟩, hall⟩

end DeSitter

/-! ### `p ∈ ∂ℍ²±`: the domains of directions entering `ℍ²±` or `dS²`
(`bbsdef:lies_domain_respectively_set`) -/

section Light

variable (p : HS 2)

/-- **`c_v`** (l.762–763): the oriented projective line of `HS²` starting from `p` in the direction
`v = σ ∈ ℓ(p)`, `s ↦ [p + s w]` (`s ≥ 0`, `w` a lift of `σ`). Only its germ at `s = 0⁺` is used,
and that germ does not depend on the lift (`GX.mem_lightDomain_iff_forall_lift`). -/
def cv (σ : Link p) (s : ℝ) : HS 2 := rayNormalize p ((p : 𝕄) + s • liftT p σ)

theorem cv_zero (σ : Link p) : cv p σ 0 = p := by
  rw [cv, zero_smul, add_zero, rayNormalize_raySphere]

/-- **`bbsdef:lies_domain_respectively_set`** (`colI_v1.tex:828–833`): the directions `v` such
that `c_v(s)` lies in the piece `k` of `HS²` for `s > 0` sufficiently small. -/
def lightDomain (k : HSPiece) : Set (Link p) :=
  {σ | ∀ᶠ s in 𝓝[>] (0 : ℝ), cv p σ s ∈ HS.piece 2 k}

/-- The pairing `B(p, ·)` on `T_p HS²`, at a lightlike `p` (zero otherwise). -/
def nullPairing : TpHS p →ₗ[ℝ] ℝ :=
  if h : Causal.Flat.minkQ (p : 𝕄) = 0 then
    (ℝ ∙ (p : 𝕄)).liftQ (Causal.Flat.minkForm 2 (p : 𝕄)) (by
      rw [Submodule.span_le]
      rintro _ rfl
      show Causal.Flat.minkB (p : 𝕄) (p : 𝕄) = 0
      rw [← Causal.Flat.minkQ_eq_minkB, h])
  else 0

theorem nullPairing_mk (hp : Causal.Flat.minkQ (p : 𝕄) = 0) (w : 𝕄) :
    nullPairing p (tpMk p w) = Causal.Flat.minkB (p : 𝕄) w := by
  rw [nullPairing, dif_pos hp]; rfl

theorem continuous_nullPairing : Continuous fun σ : Link p => nullPairing p σ :=
  (LinearMap.continuous_of_finiteDimensional (nullPairing p)).comp continuous_subtype_val

theorem nullPairing_tangent (A : GammaP p) (z : TpHS p) :
    nullPairing p (GammaP.tangent A z) = nullPairing p z := by
  by_cases hp : Causal.Flat.minkQ (p : 𝕄) = 0
  · induction z using Submodule.Quotient.induction_on with
    | H w =>
      rw [GammaP.tangent_mk]
      show nullPairing p (tpMk p _) = nullPairing p (tpMk p w)
      rw [nullPairing_mk p hp, nullPairing_mk p hp, minkB_gammaP]
  · rw [nullPairing, dif_neg hp]; rfl

theorem nullPairing_dirOf (hp : Causal.Flat.minkQ (p : 𝕄) = 0) {w : 𝕄} (hw : tpMk p w ≠ 0) :
    nullPairing p (dirOf p w) = ‖tpMk p w‖⁻¹ * Causal.Flat.minkB (p : 𝕄) w := by
  rw [coe_dirOf p hw, map_smul, nullPairing_mk p hp, smul_eq_mul]

theorem nullPairing_smul (A : GammaP p) (σ : Link p) :
    nullPairing p (A • σ : Link p) = ‖GammaP.tangent A σ‖⁻¹ * nullPairing p σ := by
  rw [gammaP_smul_def, coe_linRaySmul, map_smul, nullPairing_tangent, smul_eq_mul]

theorem nullPairing_liftT (hp : Causal.Flat.minkQ (p : 𝕄) = 0) (σ : Link p) :
    nullPairing p σ = Causal.Flat.minkB (p : 𝕄) (liftT p σ) := by
  rw [← nullPairing_mk p hp, tpMk_liftT]

/-- **The two directions tangent to `∂ℍ²±` at `p`** (l.835–836): `T_p ∂ℍ²± = p^⊥/ℝp`. -/
def tangentDirs : Set (Link p) := {σ | nullPairing p σ = 0}

theorem tpMk_liftT_ne_zero (σ : Link p) : tpMk p (liftT p σ) ≠ 0 := by
  rw [tpMk_liftT]; exact raySphere_ne_zero σ

theorem add_smul_ne_zero {w : 𝕄} (hw : tpMk p w ≠ 0) (s : ℝ) : (p : 𝕄) + s • w ≠ 0 := by
  intro h
  have hs : s ≠ 0 := by
    rintro rfl
    rw [zero_smul, add_zero] at h
    exact raySphere_ne_zero p h
  have h' : s • w = -(p : 𝕄) := by
    rw [← sub_eq_zero, sub_neg_eq_add, add_comm]; exact h
  have hw' : w = (-s⁻¹) • (p : 𝕄) := by
    calc w = s⁻¹ • (s • w) := by rw [smul_smul, inv_mul_cancel₀ hs, one_smul]
      _ = (-s⁻¹) • (p : 𝕄) := by rw [h', smul_neg, neg_smul]
  exact hw ((tpMk_eq_zero_iff p).2 ⟨_, hw'⟩)

theorem rayNormalize_mem_hypPlus_iff {v : 𝕄} (hv : v ≠ 0) :
    rayNormalize p v ∈ HS.piece 2 .hypPlus ↔ Causal.Flat.IsFutureTimelike v := by
  show Causal.Flat.IsFutureTimelike ((rayNormalize p v : HS 2) : 𝕄) ↔ _
  rw [coe_rayNormalize p hv, HS.isFutureTimelike_smul_iff (inv_pos.2 (norm_pos_iff.2 hv))]

theorem rayNormalize_mem_hypMinus_iff {v : 𝕄} (hv : v ≠ 0) :
    rayNormalize p v ∈ HS.piece 2 .hypMinus ↔ Causal.Flat.IsFutureTimelike (-v) := by
  show Causal.Flat.IsFutureTimelike (-((rayNormalize p v : HS 2) : 𝕄)) ↔ _
  rw [coe_rayNormalize p hv, ← smul_neg,
    HS.isFutureTimelike_smul_iff (inv_pos.2 (norm_pos_iff.2 hv))]

theorem rayNormalize_mem_deSitter_iff {v : 𝕄} (hv : v ≠ 0) :
    rayNormalize p v ∈ HS.piece 2 .deSitter ↔ 0 < Causal.Flat.minkQ v := by
  show 0 < Causal.Flat.minkQ ((rayNormalize p v : HS 2) : 𝕄) ↔ _
  rw [coe_rayNormalize p hv, HS.minkQ_smul_pos_iff (inv_pos.2 (norm_pos_iff.2 hv))]

/-- **The germ of `s ↦ [p + s w]` at `0⁺` depends only on the class of `w`**: changing the lift
reparametrises the germ (`s ↦ s / (1 + s c)`). -/
theorem eventually_rayNormalize_congr {w w' : 𝕄} (hw : tpMk p w ≠ 0)
    (h : tpMk p w' = tpMk p w) (P : HS 2 → Prop)
    (hP : ∀ᶠ s in 𝓝[>] (0 : ℝ), P (rayNormalize p ((p : 𝕄) + s • w))) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), P (rayNormalize p ((p : 𝕄) + s • w')) := by
  obtain ⟨c, hc⟩ := (tpMk_eq_tpMk_iff p).1 h
  set φ : ℝ → ℝ := fun s => s / (1 + s * c)
  have hlin : Tendsto (fun s : ℝ => 1 + s * c) (𝓝[>] 0) (𝓝 1) := by
    have : Continuous fun s : ℝ => 1 + s * c := by fun_prop
    have := this.tendsto 0
    rw [zero_mul, add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hpos : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < 1 + s * c := hlin.eventually (lt_mem_nhds one_pos)
  have hφ : Tendsto φ (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have h1 : Tendsto (fun s : ℝ => s) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
      have := h1.div hlin one_ne_zero
      rwa [zero_div] at this
    · filter_upwards [hpos, self_mem_nhdsWithin] with s h1 (hs : 0 < s)
      exact div_pos hs h1
  filter_upwards [hφ.eventually hP, hpos] with s hs h1
  have hmul : (1 + s * c) * φ s = s := by
    simp only [φ]; field_simp
  have heq : (p : 𝕄) + s • w' = (1 + s * c) • ((p : 𝕄) + φ s • w) := by
    rw [show (1 + s * c) • ((p : 𝕄) + φ s • w) = (1 + s * c) • (p : 𝕄) + ((1 + s * c) * φ s) • w
      by rw [smul_add, smul_smul], hmul, hc]
    module
  rw [heq, rayNormalize_smul_of_pos p (add_smul_ne_zero p hw _) h1]
  exact hs

variable {p}

/-- The definition does not depend on the lift: any lift `w` of `σ` gives the same germ. -/
theorem mem_lightDomain_iff_forall_lift {k : HSPiece} {σ : Link p} {w : 𝕄} (hw : tpMk p w = σ) :
    σ ∈ lightDomain p k ↔
      ∀ᶠ s in 𝓝[>] (0 : ℝ), rayNormalize p ((p : 𝕄) + s • w) ∈ HS.piece 2 k := by
  have h0' : tpMk p w ≠ 0 := by rw [hw]; exact raySphere_ne_zero σ
  have hl : tpMk p w = tpMk p (liftT p σ) := by rw [hw, tpMk_liftT]
  exact ⟨eventually_rayNormalize_congr p (tpMk_liftT_ne_zero p σ) hl _,
    eventually_rayNormalize_congr p h0' hl.symm _⟩

theorem minkQ_add_smul_of_null (hp : Causal.Flat.minkQ (p : 𝕄) = 0) (w : 𝕄) (s : ℝ) :
    Causal.Flat.minkQ ((p : 𝕄) + s • w) =
      s * (2 * Causal.Flat.minkB (p : 𝕄) w + s * Causal.Flat.minkQ w) := by
  rw [Causal.Flat.minkQ_add, hp, Causal.Flat.minkQ_smul, Causal.Flat.minkB_smul_right]; ring

theorem tendsto_affine (a b : ℝ) : Tendsto (fun s : ℝ => a + s * b) (𝓝[>] 0) (𝓝 a) := by
  have : Continuous fun s : ℝ => a + s * b := by fun_prop
  have := this.tendsto 0
  rw [zero_mul, add_zero] at this
  exact this.mono_left nhdsWithin_le_nhds

/-- At a lightlike `p`, `[p + s w] ∈ dS²` for small `s > 0` iff `B(p, w) ≥ 0`. -/
theorem eventually_minkQ_pos_iff (hp : Causal.Flat.minkQ (p : 𝕄) = 0) {w : 𝕄}
    (hw : tpMk p w ≠ 0) :
    (∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < Causal.Flat.minkQ ((p : 𝕄) + s • w)) ↔
      0 ≤ Causal.Flat.minkB (p : 𝕄) w := by
  have hlim := tendsto_affine (2 * Causal.Flat.minkB (p : 𝕄) w) (Causal.Flat.minkQ w)
  constructor
  · intro h
    by_contra hB
    push Not at hB
    have h2 := hlim.eventually (gt_mem_nhds (by linarith : 2 * Causal.Flat.minkB (p : 𝕄) w < 0))
    obtain ⟨s, hs1, hs2, hs3⟩ := (h.and (h2.and self_mem_nhdsWithin)).exists
    rw [minkQ_add_smul_of_null hp] at hs1
    have hs3' : (0 : ℝ) < s := hs3
    nlinarith
  · intro hB
    rcases hB.lt_or_eq with hB | hB
    · have h2 := hlim.eventually (lt_mem_nhds (by linarith : (0 : ℝ) < 2 * Causal.Flat.minkB (p : 𝕄) w))
      filter_upwards [h2, self_mem_nhdsWithin] with s h2 (hs : 0 < s)
      rw [minkQ_add_smul_of_null hp]; exact mul_pos hs h2
    · have hQw : 0 < Causal.Flat.minkQ w := by
        obtain ⟨h1, h2⟩ := Causal.Flat.minkQ_nonneg_of_null_orth hp (raySphere_ne_zero p) hB.symm
        exact lt_of_le_of_ne h1 fun h => hw ((tpMk_eq_zero_iff p).2 (h2 h.symm))
      filter_upwards [self_mem_nhdsWithin] with s (hs : 0 < s)
      rw [minkQ_add_smul_of_null hp, ← hB]
      nlinarith [mul_pos (mul_pos hs hs) hQw]

/-- At `p ∈ ∂ℍ²₊`, `[p + s w] ∈ ℍ²₊` for small `s > 0` iff `B(p, w) < 0`. -/
theorem eventually_isFutureTimelike_iff (hp : Causal.Flat.minkQ (p : 𝕄) = 0)
    (hp1 : 0 < (p : 𝕄).1) {w : 𝕄} (hw : tpMk p w ≠ 0) :
    (∀ᶠ s in 𝓝[>] (0 : ℝ), Causal.Flat.IsFutureTimelike ((p : 𝕄) + s • w)) ↔
      Causal.Flat.minkB (p : 𝕄) w < 0 := by
  constructor
  · intro h
    by_contra hB
    push Not at hB
    obtain ⟨s, hs1, hs2⟩ := (h.and ((eventually_minkQ_pos_iff hp hw).2 hB)).exists
    exact lt_asymm hs1.2 hs2
  · intro hB
    have h2 := (tendsto_affine (2 * Causal.Flat.minkB (p : 𝕄) w) (Causal.Flat.minkQ w)).eventually
      (gt_mem_nhds (by linarith : 2 * Causal.Flat.minkB (p : 𝕄) w < 0))
    have h3 := (tendsto_affine (p : 𝕄).1 w.1).eventually (lt_mem_nhds hp1)
    filter_upwards [h2, h3, self_mem_nhdsWithin] with s h2 h3 (hs : 0 < s)
    refine ⟨?_, ?_⟩
    · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]; linarith
    · rw [minkQ_add_smul_of_null hp]; exact mul_neg_of_pos_of_neg hs h2

/-- At `p ∈ ∂ℍ²₋`, `[p + s w] ∈ ℍ²₋` for small `s > 0` iff `B(p, w) < 0`. -/
theorem eventually_isPastTimelike_iff (hp : Causal.Flat.minkQ (p : 𝕄) = 0)
    (hp1 : (p : 𝕄).1 < 0) {w : 𝕄} (hw : tpMk p w ≠ 0) :
    (∀ᶠ s in 𝓝[>] (0 : ℝ), Causal.Flat.IsFutureTimelike (-((p : 𝕄) + s • w))) ↔
      Causal.Flat.minkB (p : 𝕄) w < 0 := by
  constructor
  · intro h
    by_contra hB
    push Not at hB
    obtain ⟨s, hs1, hs2⟩ := (h.and ((eventually_minkQ_pos_iff hp hw).2 hB)).exists
    have := hs1.2
    rw [Causal.Flat.minkQ_neg] at this
    exact lt_asymm this hs2
  · intro hB
    have h2 := (tendsto_affine (2 * Causal.Flat.minkB (p : 𝕄) w) (Causal.Flat.minkQ w)).eventually
      (gt_mem_nhds (by linarith : 2 * Causal.Flat.minkB (p : 𝕄) w < 0))
    have h3 := (tendsto_affine (p : 𝕄).1 w.1).eventually (gt_mem_nhds hp1)
    filter_upwards [h2, h3, self_mem_nhdsWithin] with s h2 h3 (hs : 0 < s)
    refine ⟨?_, ?_⟩
    · simp only [Prod.fst_neg, Prod.fst_add, Prod.smul_fst, smul_eq_mul]; linarith
    · rw [Causal.Flat.minkQ_neg, minkQ_add_smul_of_null hp]; exact mul_neg_of_pos_of_neg hs h2

/-- `c_v` enters `ℍ²₊` iff `B(p, v) < 0`, at `p ∈ ∂ℍ²₊`. -/
theorem lightDomain_hypPlus_eq (hp : p ∈ HS.piece 2 .bdPlus) :
    lightDomain p .hypPlus = {σ : Link p | nullPairing p σ < 0} := by
  have hQ : Causal.Flat.minkQ (p : 𝕄) = 0 := hp.1
  ext σ
  have hw0 := tpMk_liftT_ne_zero p σ
  simp only [lightDomain, mem_setOf_eq, cv, nullPairing_liftT p hQ]
  rw [← eventually_isFutureTimelike_iff hQ hp.2 hw0]
  exact Filter.eventually_congr (Eventually.of_forall fun s =>
    rayNormalize_mem_hypPlus_iff p (add_smul_ne_zero p hw0 s))

/-- `c_v` enters `ℍ²₋` iff `B(p, v) < 0`, at `p ∈ ∂ℍ²₋`. -/
theorem lightDomain_hypMinus_eq (hp : p ∈ HS.piece 2 .bdMinus) :
    lightDomain p .hypMinus = {σ : Link p | nullPairing p σ < 0} := by
  have hQ : Causal.Flat.minkQ (p : 𝕄) = 0 := hp.1
  ext σ
  have hw0 := tpMk_liftT_ne_zero p σ
  simp only [lightDomain, mem_setOf_eq, cv, nullPairing_liftT p hQ]
  rw [← eventually_isPastTimelike_iff hQ hp.2 hw0]
  exact Filter.eventually_congr (Eventually.of_forall fun s =>
    rayNormalize_mem_hypMinus_iff p (add_smul_ne_zero p hw0 s))

/-- **`c_v` enters `dS²` iff `B(p, v) ≥ 0`**, at a lightlike `p`: the two tangent directions are
included (`c_v` is then the tangent line of the conic, which lies in `dS²` but for `p`). -/
theorem lightDomain_deSitter_eq (hp : Causal.Flat.minkQ (p : 𝕄) = 0) :
    lightDomain p .deSitter = {σ : Link p | 0 ≤ nullPairing p σ} := by
  ext σ
  have hw0 := tpMk_liftT_ne_zero p σ
  simp only [lightDomain, mem_setOf_eq, cv, nullPairing_liftT p hp]
  rw [← eventually_minkQ_pos_iff hp hw0]
  exact Filter.eventually_congr (Eventually.of_forall fun s =>
    rayNormalize_mem_deSitter_iff p (add_smul_ne_zero p hw0 s))

/-- At a lightlike `p`, `‖p₁‖ = 1`. -/
theorem norm_snd_of_null (hp : Causal.Flat.minkQ (p : 𝕄) = 0) : ‖(p : 𝕄).2‖ = 1 := by
  have h1 := HS.max_abs_fst_norm_snd p
  have h2 := HS.minkQ_eq_zero_iff_norm.1 hp
  rw [← h2, max_self] at h1
  exact h1

variable (p) in
theorem neg_ne_self_link (σ : Link p) : -σ ≠ σ := fun h => by
  have h1 := congrArg Subtype.val h
  rw [coe_neg_sphere] at h1
  have h2 : (2 : ℝ) • (σ : TpHS p) = 0 := by rw [two_smul]; nth_rewrite 1 [← h1]; exact neg_add_cancel _
  exact raySphere_ne_zero σ ((smul_eq_zero.1 h2).resolve_left two_ne_zero)

variable (p) in
theorem dirOf_neg {w : 𝕄} (hw : tpMk p w ≠ 0) : dirOf p (-w) = -dirOf p w := by
  have hneg : tpMk p (-w) = -tpMk p w := Submodule.Quotient.mk_neg _
  refine Subtype.ext ?_
  rw [coe_neg_sphere, coe_dirOf p (by rw [hneg]; exact neg_ne_zero.2 hw), coe_dirOf p hw, hneg,
    norm_neg, smul_neg]

variable (p) in
theorem dirOf_smul_of_pos {w : 𝕄} (hw : tpMk p w ≠ 0) {c : ℝ} (hc : 0 < c) :
    dirOf p (c • w) = dirOf p w := by
  rw [dirOf, dirOf, show tpMk p (c • w) = c • tpMk p w from Submodule.Quotient.mk_smul _ _ _,
    rayNormalize_smul_of_pos _ hw hc]

variable (p) in
theorem dirOf_congr {v w : 𝕄} (h : tpMk p v = tpMk p w) : dirOf p v = dirOf p w := by
  rw [dirOf, dirOf, h]

theorem exists_minkB_neg (hp : Causal.Flat.minkQ (p : 𝕄) = 0) :
    ∃ w : 𝕄, tpMk p w ≠ 0 ∧ Causal.Flat.minkB (p : 𝕄) w < 0 := by
  have hp0 := HS.fst_ne_zero_of_minkQ_nonpos p hp.le
  refine ⟨(p : 𝕄).1 • Causal.Flat.timeUnit 2, fun h0 => ?_, ?_⟩
  · have := nullPairing_mk p hp ((p : 𝕄).1 • Causal.Flat.timeUnit 2)
    rw [h0, map_zero, Causal.Flat.minkB_smul_right] at this
    simp [Causal.Flat.minkB, Causal.Flat.timeUnit] at this
    exact hp0 this
  · rw [Causal.Flat.minkB_smul_right]
    simp only [Causal.Flat.minkB, Causal.Flat.timeUnit, mul_one, inner_zero_right, add_zero]
    nlinarith [sq_pos_of_ne_zero hp0]

/-- There are exactly two directions tangent to `∂ℍ²±` at a lightlike `p`. -/
theorem tangentDirs_eq (hp : Causal.Flat.minkQ (p : 𝕄) = 0) :
    tangentDirs p = {dirOf p (jVec p), -dirOf p (jVec p)} := by
  have hp1 := norm_snd_of_null hp
  have hf := tpMk_jVec_ne_zero p hp1
  have hpf : Causal.Flat.minkB (p : 𝕄) (jVec p) = 0 := by
    rw [Causal.Flat.minkB_comm]; exact minkB_jVec p
  ext σ
  simp only [tangentDirs, mem_setOf_eq, mem_insert_iff, mem_singleton_iff]
  constructor
  · intro h0
    set w := liftT p σ
    have hw : tpMk p w = σ := tpMk_liftT p σ
    have hB : Causal.Flat.minkB (p : 𝕄) w = 0 := by rw [← nullPairing_liftT p hp]; exact h0
    set β := Causal.Flat.minkB (jVec p) w
    have hx : (p : 𝕄).2 0 ^ 2 + (p : 𝕄).2 1 ^ 2 = 1 := by rw [← norm_sq_two, hp1, one_pow]
    have ht : (p : 𝕄).1 ^ 2 = 1 := by
      have := hp; rw [minkQ_two] at this; linarith
    have hB' := hB
    rw [minkB_two] at hB'
    have hmk : tpMk p w = tpMk p (β • jVec p) := by
      rw [tpMk_eq_tpMk_iff]
      refine ⟨(p : 𝕄).1 * w.1, ?_⟩
      refine Prod.ext ?_ ?_
      · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul, jVec, mul_zero, zero_add]
        linear_combination (-(w.1)) * ht
      · ext i
        fin_cases i
        · simp only [β, minkB_two, Prod.snd_add, Prod.smul_snd, PiLp.add_apply, PiLp.smul_apply,
            smul_eq_mul, jVec, jRot_zero, jRot_one, Fin.zero_eta, Fin.isValue, zero_mul, neg_zero,
            zero_add]
          linear_combination ((p : 𝕄).2 0) * hB' - (w.2 0) * hx
        · simp only [β, minkB_two, Prod.snd_add, Prod.smul_snd, PiLp.add_apply, PiLp.smul_apply,
            smul_eq_mul, jVec, jRot_zero, jRot_one, Fin.mk_one, Fin.isValue, zero_mul, neg_zero,
            zero_add]
          linear_combination ((p : 𝕄).2 1) * hB' - (w.2 1) * hx
    have hβ : β ≠ 0 := by
      intro h
      rw [h, zero_smul] at hmk
      exact tpMk_liftT_ne_zero p σ (hmk.trans (Submodule.Quotient.mk_zero _))
    have hσ : σ = dirOf p (β • jVec p) := by rw [← dirOf_congr p hmk, dirOf_eq p hw]
    rcases lt_or_gt_of_ne hβ with hβ | hβ
    · right
      rw [hσ, show β • jVec p = (-β) • (-jVec p) by rw [smul_neg, neg_smul, neg_neg],
        dirOf_smul_of_pos p (by
          rw [show tpMk p (-jVec p) = -tpMk p (jVec p) from Submodule.Quotient.mk_neg _];
          exact neg_ne_zero.2 hf) (neg_pos.2 hβ), dirOf_neg p hf]
    · left
      rw [hσ, dirOf_smul_of_pos p hf hβ]
  · rintro (rfl | rfl)
    · rw [nullPairing_dirOf p hp hf, hpf, mul_zero]
    · rw [coe_neg_sphere, map_neg, nullPairing_dirOf p hp hf, hpf, mul_zero, neg_zero]

theorem ncard_tangentDirs (hp : Causal.Flat.minkQ (p : 𝕄) = 0) : (tangentDirs p).ncard = 2 := by
  rw [tangentDirs_eq hp]
  exact ncard_pair (neg_ne_self_link p _).symm

/-- The directions on which `B(p, ·)` takes values in a convex cone `T ∌ 0` form a preconnected
set (an arc). -/
theorem isPreconnected_nullPairing_mem (hp : Causal.Flat.minkQ (p : 𝕄) = 0) {T : Set ℝ}
    (hT : Convex ℝ T) (h0 : (0 : ℝ) ∉ T) (hsc : ∀ c : ℝ, 0 < c → ∀ x, c * x ∈ T ↔ x ∈ T) :
    IsPreconnected {σ : Link p | nullPairing p σ ∈ T} := by
  have himg := image_dirOf_eq p (P := fun z => nullPairing p z ∈ T) (fun c hc z => by
    rw [map_smul, smul_eq_mul]; exact hsc c hc _)
  have hset : {w | tpMk p w ≠ 0 ∧ nullPairing p (tpMk p w) ∈ T} =
      (Causal.Flat.minkForm 2 (p : 𝕄)) ⁻¹' T := by
    ext w
    simp only [mem_setOf_eq, mem_preimage, nullPairing_mk p hp, Causal.Flat.minkForm_apply]
    refine ⟨fun h => h.2, fun h => ⟨fun hw0 => ?_, h⟩⟩
    rw [← nullPairing_mk p hp, hw0, map_zero] at h
    exact h0 h
  rw [hset] at himg
  rw [← himg]
  refine (hT.linear_preimage _).isPreconnected.image _ ((continuousOn_dirOf p).mono fun w hw => ?_)
  show tpMk p w ≠ 0
  intro hw0
  have h : Causal.Flat.minkB (p : 𝕄) w ∈ T := hw
  rw [← nullPairing_mk p hp, hw0, map_zero] at h
  exact h0 h

/-- **The components of the complement of the two tangent directions** are
`{B(p, ·) < 0}` and `{B(p, ·) > 0}`. -/
theorem components_compl_tangentDirs (hp : Causal.Flat.minkQ (p : 𝕄) = 0) :
    {K | ∃ σ ∈ (tangentDirs p)ᶜ, connectedComponentIn (tangentDirs p)ᶜ σ = K} =
      {{σ : Link p | nullPairing p σ < 0}, {σ : Link p | 0 < nullPairing p σ}} := by
  set N : Set (Link p) := {σ | nullPairing p σ < 0}
  set P' : Set (Link p) := {σ | 0 < nullPairing p σ}
  have hS : (tangentDirs p)ᶜ = N ∪ P' := by
    ext σ
    simp only [tangentDirs, mem_compl_iff, mem_setOf_eq, mem_union, N, P']
    constructor
    · exact fun h => lt_or_gt_of_ne h
    · rintro (h | h)
      exacts [h.ne, h.ne']
  have ho₁ : IsOpen N := isOpen_lt (continuous_nullPairing p) continuous_const
  have ho₂ : IsOpen P' := isOpen_lt continuous_const (continuous_nullPairing p)
  have hd : Disjoint N P' := Set.disjoint_left.2 fun σ (h1 : nullPairing p σ < 0)
    (h2 : 0 < nullPairing p σ) => lt_asymm h1 h2
  have h₁ : IsPreconnected N := isPreconnected_nullPairing_mem hp (T := Iio 0) (convex_Iio 0)
    (by simp) fun c hc x => by
      simp only [mem_Iio]
      exact ⟨fun h => by by_contra h'; push Not at h'; nlinarith, fun h => mul_neg_of_pos_of_neg hc h⟩
  have h₂ : IsPreconnected P' := isPreconnected_nullPairing_mem hp (T := Ioi 0) (convex_Ioi 0)
    (by simp) fun c hc x => by simp only [mem_Ioi]; exact mul_pos_iff_of_pos_left hc
  obtain ⟨w, hw, hB⟩ := exists_minkB_neg hp
  have hw' : tpMk p (-w) ≠ 0 := by
    rw [show tpMk p (-w) = -tpMk p w from Submodule.Quotient.mk_neg _]; exact neg_ne_zero.2 hw
  have hn₁ : N.Nonempty := ⟨dirOf p w, by
    show nullPairing p (dirOf p w) < 0
    rw [nullPairing_dirOf p hp hw]
    exact mul_neg_of_pos_of_neg (inv_pos.2 (norm_pos_iff.2 hw)) hB⟩
  have hn₂ : P'.Nonempty := ⟨dirOf p (-w), by
    show 0 < nullPairing p (dirOf p (-w))
    rw [nullPairing_dirOf p hp hw', Causal.Flat.minkB_neg_right]
    exact mul_pos (inv_pos.2 (norm_pos_iff.2 hw')) (neg_pos.2 hB)⟩
  exact components_eq_pair hS (fun x hx => connectedComponentIn_eq_of_open hS h₁ ho₁ ho₂ hd hx)
    (fun x hx => connectedComponentIn_eq_of_open (hS.trans (union_comm _ _)) h₂ ho₂ ho₁ hd.symm hx)
    hn₁ hn₂

end Light

/-! ### The fixed points of `Γ_p` -/

section Fixed

variable {p : HS 2}

/-- `A • σ = σ` iff the tangent action of `A` maps `σ` to a positive multiple of itself. -/
theorem gammaP_smul_eq_iff (A : GammaP p) (σ : Link p) :
    A • σ = σ ↔ ∃ c : ℝ, 0 < c ∧ GammaP.tangent A σ = c • (σ : TpHS p) := by
  rw [gammaP_smul_def, linRaySmul_eq_iff]

/-- A fixed direction of `A ∈ Γ_p`, read on a lift: `A w = c w + m p`. -/
theorem exists_apply_eq_of_smul_eq {A : GammaP p} {σ : Link p} (h : A • σ = σ) :
    ∃ c m : ℝ, 0 < c ∧ ((A : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄) (liftT p σ) =
      c • liftT p σ + m • (p : 𝕄) := by
  obtain ⟨c, hc, hT⟩ := (gammaP_smul_eq_iff A σ).1 h
  have h1 : tpMk p (((A : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄) (liftT p σ)) =
      tpMk p (c • liftT p σ) := by
    rw [show tpMk p (c • liftT p σ) = c • tpMk p (liftT p σ) from Submodule.Quotient.mk_smul _ _ _,
      tpMk_liftT, ← hT, ← tpMk_liftT p σ]
    rfl
  obtain ⟨m, hm⟩ := (tpMk_eq_tpMk_iff p).1 h1
  exact ⟨c, m, hc, hm⟩

/-! #### A timelike `p`: the half-turn about `p` has no fixed direction -/

variable (p) in
/-- The half-turn `v ↦ −v + 2 B(p,v)/Q(p) p` about `p`. -/
def halfTurnLin : 𝕄 →ₗ[ℝ] 𝕄 where
  toFun v := -v + (2 * Causal.Flat.minkB (p : 𝕄) v / Causal.Flat.minkQ (p : 𝕄)) • (p : 𝕄)
  map_add' v w := by
    rw [Causal.Flat.minkB_add_right, mul_add, add_div, add_smul]; abel
  map_smul' c v := by
    rw [Causal.Flat.minkB_smul_right, RingHom.id_apply, smul_add, smul_smul, smul_neg]
    congr 2; ring

theorem halfTurnLin_apply (v : 𝕄) : halfTurnLin p v =
    -v + (2 * Causal.Flat.minkB (p : 𝕄) v / Causal.Flat.minkQ (p : 𝕄)) • (p : 𝕄) := rfl

theorem halfTurnLin_self (hp : Causal.Flat.minkQ (p : 𝕄) ≠ 0) : halfTurnLin p (p : 𝕄) = p := by
  rw [halfTurnLin_apply, ← Causal.Flat.minkQ_eq_minkB, mul_div_assoc, div_self hp, mul_one,
    two_smul]; abel

theorem halfTurnLin_involutive (hp : Causal.Flat.minkQ (p : 𝕄) ≠ 0) :
    Function.Involutive (halfTurnLin p) := fun v => by
  rw [halfTurnLin_apply v, map_add, map_smul, halfTurnLin_self hp, map_neg, halfTurnLin_apply v]
  module

theorem minkQ_halfTurnLin (hp : Causal.Flat.minkQ (p : 𝕄) ≠ 0) (v : 𝕄) :
    Causal.Flat.minkQ (halfTurnLin p v) = Causal.Flat.minkQ v := by
  rw [halfTurnLin_apply, Causal.Flat.minkQ_add, Causal.Flat.minkQ_neg, Causal.Flat.minkQ_smul,
    Causal.Flat.minkB_smul_right, Causal.Flat.minkB_neg_left, Causal.Flat.minkB_comm v]
  field_simp
  ring

theorem det_halfTurnLin (hp : Causal.Flat.minkQ (p : 𝕄) ≠ 0) :
    LinearMap.det (halfTurnLin p) = 1 := by
  set W := (ℝ ∙ (p : 𝕄))
  have he : W ≤ W.comap (halfTurnLin p) := by
    intro v hv
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hv
    rw [Submodule.mem_comap, map_smul, halfTurnLin_self hp]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  have hres : (halfTurnLin p).restrict he = LinearMap.id := by
    refine LinearMap.ext fun ⟨v, hv⟩ => Subtype.ext ?_
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hv
    show halfTurnLin p (c • (p : 𝕄)) = c • (p : 𝕄)
    rw [map_smul, halfTurnLin_self hp]
  have hq : W.mapQ W (halfTurnLin p) he = (-1 : ℝ) • LinearMap.id := by
    refine LinearMap.ext fun x => ?_
    induction x using Submodule.Quotient.induction_on with
    | H v =>
      show tpMk p (halfTurnLin p v) = (-1 : ℝ) • tpMk p v
      rw [neg_one_smul, ← Submodule.Quotient.mk_neg, tpMk_eq_tpMk_iff, halfTurnLin_apply]
      exact ⟨_, rfl⟩
  rw [LinearMap.det_eq_det_mul_det W _ he, hres, hq, LinearMap.det_id, one_mul, LinearMap.det_smul,
    LinearMap.det_id, mul_one]
  have : Module.finrank ℝ (𝕄 ⧸ W) = 2 := finrank_tpHS p
  rw [this]; norm_num

/-- The half-turn about a timelike `p`, as an element of `Γ_p`. -/
def gammaHalfTurn (hp : Causal.Flat.minkQ (p : 𝕄) < 0) : GammaP p :=
  ⟨⟨LinearEquiv.ofInvolutive (halfTurnLin p) (halfTurnLin_involutive hp.ne),
    mem_lorentz_of_fix (minkQ_halfTurnLin hp.ne) (det_halfTurnLin hp.ne) hp.le
      (raySphere_ne_zero p) (halfTurnLin_self hp.ne)⟩, halfTurnLin_self hp.ne⟩

/-- **At a timelike `p`, `Γ_p` has no fixed point on `ℓ(p)`**: the half-turn acts as `σ ↦ −σ`. -/
theorem fixedPoints_eq_empty_of_timelike (hp : Causal.Flat.minkQ (p : 𝕄) < 0) :
    {σ : Link p | ∀ A : GammaP p, A • σ = σ} = ∅ := by
  refine eq_empty_of_forall_notMem fun σ hσ => ?_
  obtain ⟨c, hc, hT⟩ := (gammaP_smul_eq_iff _ σ).1 (hσ (gammaHalfTurn hp))
  have hneg : GammaP.tangent (gammaHalfTurn hp) σ = -(σ : TpHS p) := by
    rw [← tpMk_liftT p σ]
    show tpMk p (halfTurnLin p (liftT p σ)) = -tpMk p (liftT p σ)
    rw [← Submodule.Quotient.mk_neg, tpMk_eq_tpMk_iff, halfTurnLin_apply]
    exact ⟨_, rfl⟩
  rw [hneg] at hT
  have h2 : (1 + c) • (σ : TpHS p) = 0 := by rw [add_smul, one_smul, ← hT, add_neg_cancel]
  exact raySphere_ne_zero σ ((smul_eq_zero.1 h2).resolve_left (by linarith))

/-! #### `p ∈ dS²`: `Γ_p` fixes exactly the four lightlike directions -/

/-- `Γ_p` fixes only lightlike directions, at `p ∈ dS²`: a boost of the Lorentzian plane `p^⊥`
moves every other direction. -/
theorem fixedPoints_subset_of_deSitter (hp : p ∈ HS.piece 2 .deSitter) :
    {σ : Link p | ∀ A : GammaP p, A • σ = σ} ⊆
      {σ : Link p | Causal.Flat.minkQ (dsProj p σ) = 0} := by
  intro σ hσ
  have hQ : 0 < Causal.Flat.minkQ (p : 𝕄) := hp
  have hp1 := norm_snd_of_deSitter hp
  set k := Real.sqrt (Causal.Flat.minkQ (p : 𝕄))
  have hk : 0 < k := Real.sqrt_pos.2 hQ
  have hk2 : k ^ 2 = Causal.Flat.minkQ (p : 𝕄) := Real.sq_sqrt hQ.le
  set e₀ := k⁻¹ • dsU p
  set e₁ := jVec p
  have h0 : Causal.Flat.minkQ e₀ = -1 := by
    rw [Causal.Flat.minkQ_smul, minkQ_dsU hp1, inv_pow, hk2]; field_simp
  have h1 : Causal.Flat.minkQ e₁ = 1 := by rw [minkQ_jVec, hp1, one_pow]
  have h01 : Causal.Flat.minkB e₀ e₁ = 0 := by
    rw [Causal.Flat.minkB_smul_left, minkB_dsU_jVec, mul_zero]
  have hpe₀ : Causal.Flat.minkB (p : 𝕄) e₀ = 0 := by
    rw [Causal.Flat.minkB_smul_right, Causal.Flat.minkB_comm, minkB_dsU_self hp1, mul_zero]
  have hpe₁ : Causal.Flat.minkB (p : 𝕄) e₁ = 0 := by
    rw [Causal.Flat.minkB_comm]; exact minkB_jVec p
  set Bt := Causal.Flat.boost h0 h1 h01 1
  have hQB : ∀ v, Causal.Flat.minkQ (Bt v) = Causal.Flat.minkQ v :=
    Causal.Flat.minkQ_boostLin h0 h1 h01 1
  have hdet : LinearMap.det (Bt : 𝕄 →ₗ[ℝ] 𝕄) = 1 :=
    Causal.Flat.det_eq_one_of_eq_sq hQB (B := Causal.Flat.boostLin e₀ e₁ (1 / 2)) (by
      rw [Causal.Flat.boostLin_comp h0 h1 h01, add_halves]; rfl)
  have hfe : Causal.Flat.IsFutureTimelike e₀ := by
    refine ⟨?_, by rw [h0]; norm_num⟩
    simp only [e₀, dsU, Prod.smul_fst, smul_eq_mul, mul_one]
    exact inv_pos.2 hk
  have hfe0 : e₀ ≠ 0 := fun h => by rw [h] at hfe; exact lt_irrefl _ hfe.1
  have hBt0 : Causal.Flat.IsFutureTimelike (Bt e₀) := by
    refine isFutureTimelike_of_minkB_neg (by rw [hQB, h0]; norm_num) ⟨hfe.1.le, hfe.2.le⟩ hfe0 ?_
    rw [Causal.Flat.minkB_comm, Causal.Flat.boost_apply, Causal.Flat.minkB_boostLin_e₀ h0 h01,
      ← Causal.Flat.minkQ_eq_minkB, h0, h01]
    nlinarith [Real.cosh_pos (1 : ℝ)]
  have hmem : Bt ∈ Causal.Flat.lorentz 2 := Causal.Flat.mem_lorentz_of_future hQB hfe hBt0 hdet
  have hfix : Bt (p : 𝕄) = p := by
    rw [Causal.Flat.boost_apply, Causal.Flat.boostLin_apply, hpe₀, hpe₁]; simp
  set A : GammaP p := ⟨⟨Bt, hmem⟩, hfix⟩
  obtain ⟨c, m, hc, hA⟩ := exists_apply_eq_of_smul_eq (hσ A)
  set w := liftT p σ
  have ha := Causal.Flat.minkB_boostLin_e₀ h0 h01 1 w
  have hb := Causal.Flat.minkB_boostLin_e₁ h1 h01 1 w
  change Causal.Flat.minkB (Bt w) e₀ = _ at ha
  change Causal.Flat.minkB (Bt w) e₁ = _ at hb
  rw [show Bt w = c • w + m • (p : 𝕄) from hA, Causal.Flat.minkB_add_left,
    Causal.Flat.minkB_smul_left, Causal.Flat.minkB_smul_left] at ha hb
  rw [hpe₀] at ha
  rw [hpe₁] at hb
  have hs : Real.sinh 1 ≠ 0 := (Real.sinh_pos_iff.2 one_pos).ne'
  have hab : Real.sinh 1 * (Causal.Flat.minkB w e₁ ^ 2 - Causal.Flat.minkB w e₀ ^ 2) = 0 := by
    linear_combination Causal.Flat.minkB w e₁ * ha - Causal.Flat.minkB w e₀ * hb
  have hab' : Causal.Flat.minkB w e₁ ^ 2 = Causal.Flat.minkB w e₀ ^ 2 := by
    have := (mul_eq_zero.1 hab).resolve_left hs
    linarith
  show Causal.Flat.minkQ (dsProj p σ) = 0
  rw [← tpMk_liftT p σ, dsProj_mk]
  have hid := minkQ_perp_eq hp1 w
  change Causal.Flat.minkQ (perpLin p w) = Causal.Flat.minkQ (p : 𝕄) *
    (-(perpLin p w).1 ^ 2 + Causal.Flat.minkQ (p : 𝕄) * Causal.Flat.minkB (jVec p) w ^ 2) at hid
  have hu : Causal.Flat.minkB w (dsU p) = k * Causal.Flat.minkB w e₀ := by
    rw [Causal.Flat.minkB_smul_right, ← mul_assoc, mul_inv_cancel₀ hk.ne', one_mul]
  rw [hid, perpLin_fst hp1, hu, Causal.Flat.minkB_comm (jVec p) w]
  change _ * (-(-(k * Causal.Flat.minkB w e₀)) ^ 2 + _ * Causal.Flat.minkB w e₁ ^ 2) = 0
  rw [hab', ← hk2]
  ring

/-- `Γ_p` fixes every lightlike direction, at `p ∈ dS²`: it acts on `T_p HS²` with determinant
`1`, so it cannot exchange the two lightlike lines of `p^⊥`. -/
theorem smul_eq_of_deSitter (hp : p ∈ HS.piece 2 .deSitter) {σ : Link p}
    (h0 : Causal.Flat.minkQ (dsProj p σ) = 0) (A : GammaP p) : A • σ = σ := by
  have hQ : 0 < Causal.Flat.minkQ (p : 𝕄) := hp
  rw [gammaP_smul_eq_iff]
  set T := GammaP.tangent A
  set A' : 𝕄 ≃ₗ[ℝ] 𝕄 := ((A : Causal.Flat.lorentz 2) : 𝕄 ≃ₗ[ℝ] 𝕄)
  have hL : A' ∈ Causal.Flat.lorentz 2 := (A : Causal.Flat.lorentz 2).2
  set x := dsProj p σ
  have hx0 : x ≠ 0 := dsProj_ne_zero p hQ.ne' σ
  have hx1 : x.1 ≠ 0 := fun h => hx0 (Causal.Flat.eq_zero_of_fst_eq_zero h h0.le)
  obtain ⟨s, hs, hsx⟩ : ∃ s : ℝ, s ≠ 0 ∧ Causal.Flat.IsFutureCausal (s • x) := by
    rcases lt_or_gt_of_ne hx1 with h | h
    · refine ⟨-1, by norm_num, ⟨?_, ?_⟩⟩
      · simp only [Prod.smul_fst, smul_eq_mul]; linarith
      · rw [Causal.Flat.minkQ_smul, h0, mul_zero]
    · refine ⟨1, one_ne_zero, ⟨?_, ?_⟩⟩
      · simp only [Prod.smul_fst, smul_eq_mul, one_mul]; exact h.le
      · rw [one_smul]; exact h0.le
  have hsx0 : s • x ≠ 0 := smul_ne_zero hs hx0
  have hTx : dsProj p (T σ) = A' x := dsProj_tangent p A σ
  by_cases harea : linkArea p σ (T σ) = 0
  · obtain ⟨r, hr⟩ := eq_smul_of_linkArea_eq_zero p (raySphere_ne_zero σ) harea
    refine ⟨r, ?_, hr⟩
    have h1 : A' (s • x) = r • (s • x) := by
      rw [map_smul, ← hTx, hr, map_smul, smul_comm]
    have h2 : Causal.Flat.IsFutureCausal (A' (s • x)) := Causal.Flat.lorentz.isFutureCausal_apply hL hsx
    rw [h1] at h2
    have hpos : 0 < (s • x).1 := lt_of_le_of_ne hsx.1 fun h =>
      hsx0 (Causal.Flat.eq_zero_of_fst_eq_zero h.symm hsx.2)
    have hr0 : r ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hr
      exact tangent_ne_zero p A σ hr
    have h3 : 0 ≤ r * (s • x).1 := by simpa only [Prod.smul_fst, smul_eq_mul] using h2.1
    exact lt_of_le_of_ne (nonneg_of_mul_nonneg_left h3 hpos) hr0.symm
  · exfalso
    have hy := eq_add_of_linkArea_ne_zero p harea (T (T σ))
    have hα : linkArea p (T (T σ)) (T σ) / linkArea p σ (T σ) = -1 := by
      rw [linkArea_swap, linkArea_tangent, div_eq_iff harea]; ring
    rw [hα] at hy
    set β := linkArea p σ (T (T σ)) / linkArea p σ (T σ)
    have hd := congrArg (dsProj p) hy
    rw [dsProj_tangent, hTx, map_add, map_smul, map_smul, hTx] at hd
    have hQ1 : Causal.Flat.minkQ (A' (A' x)) = 0 := by
      rw [Causal.Flat.lorentz.minkQ_apply hL, Causal.Flat.lorentz.minkQ_apply hL]; exact h0
    rw [hd, Causal.Flat.minkQ_add, Causal.Flat.minkQ_smul, Causal.Flat.minkQ_smul,
      Causal.Flat.minkB_smul_left, Causal.Flat.minkB_smul_right, Causal.Flat.lorentz.minkQ_apply hL,
      h0] at hQ1
    have hB : Causal.Flat.minkB x (A' x) ≠ 0 := by
      intro hB
      obtain ⟨c, hc⟩ := Causal.Flat.eq_smul_of_null_orth h0 hx0
        (by rw [Causal.Flat.lorentz.minkQ_apply hL]; exact h0) hB
      have hTc : T σ = c • (σ : TpHS p) :=
        dsProj_injective p hQ.ne' (by rw [hTx, hc, map_smul])
      apply harea
      rw [hTc, linkArea_smul_right, linkArea_self, mul_zero]
    have hβ : β = 0 := by
      have : β * Causal.Flat.minkB x (A' x) = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_right hB
    rw [hβ, zero_smul, add_zero, neg_one_smul] at hd
    have h3 : Causal.Flat.IsFutureCausal (A' (A' (s • x))) :=
      Causal.Flat.lorentz.isFutureCausal_apply hL (Causal.Flat.lorentz.isFutureCausal_apply hL hsx)
    rw [map_smul, map_smul, hd, smul_neg] at h3
    have h4 : (s • x).1 ≤ 0 := by
      have := h3.1; simp only [Prod.fst_neg] at this; linarith
    exact hsx0 (Causal.Flat.eq_zero_of_fst_eq_zero (le_antisymm h4 hsx.1) hsx.2)

/-- **The fixed points of `Γ_p` at `p ∈ dS²`** are the four lightlike directions. -/
theorem fixedPoints_eq_of_deSitter (hp : p ∈ HS.piece 2 .deSitter) :
    {σ : Link p | ∀ A : GammaP p, A • σ = σ} =
      {σ : Link p | Causal.Flat.minkQ (dsProj p σ) = 0} :=
  (fixedPoints_subset_of_deSitter hp).antisymm fun _ h0 A => smul_eq_of_deSitter hp h0 A

/-! #### `p ∈ ∂ℍ²±`: `Γ_p` fixes exactly the two tangent directions -/

/-- `Γ_p` fixes only the tangent directions, at a lightlike `p`: a null rotation about `p`. -/
theorem fixedPoints_subset_of_null (hp : Causal.Flat.minkQ (p : 𝕄) = 0) :
    {σ : Link p | ∀ A : GammaP p, A • σ = σ} ⊆ tangentDirs p := by
  intro σ hσ
  have hp1 := norm_snd_of_null hp
  have he : Causal.Flat.minkQ (jVec p) = 1 := by rw [minkQ_jVec, hp1, one_pow]
  have hue : Causal.Flat.minkB (p : 𝕄) (jVec p) = 0 := by
    rw [Causal.Flat.minkB_comm]; exact minkB_jVec p
  set N := Causal.Flat.nullRot hp he hue 1
  have hQN : ∀ v, Causal.Flat.minkQ (N v) = Causal.Flat.minkQ v :=
    Causal.Flat.minkQ_nullRotLin hp he hue 1
  have hdet : LinearMap.det (N : 𝕄 →ₗ[ℝ] 𝕄) = 1 :=
    Causal.Flat.det_eq_one_of_eq_sq hQN (B := Causal.Flat.nullRotLin (p : 𝕄) (jVec p) (1 / 2)) (by
      rw [Causal.Flat.nullRotLin_comp hp he hue, add_halves]; rfl)
  have hfix : N (p : 𝕄) = p := by
    rw [Causal.Flat.nullRot_apply, Causal.Flat.nullRotLin_apply, ← Causal.Flat.minkQ_eq_minkB, hp,
      hue]
    simp
  have hmem := mem_lorentz_of_fix hQN hdet hp.le (raySphere_ne_zero p) hfix
  set A : GammaP p := ⟨⟨N, hmem⟩, hfix⟩
  obtain ⟨c, m, hc, hA⟩ := exists_apply_eq_of_smul_eq (hσ A)
  set w := liftT p σ
  have h1 := Causal.Flat.minkB_nullRotLin_u hp hue 1 w
  have h2 := Causal.Flat.minkB_nullRotLin_e he hue 1 w
  change Causal.Flat.minkB (N w) (p : 𝕄) = _ at h1
  change Causal.Flat.minkB (N w) (jVec p) = _ at h2
  rw [show N w = c • w + m • (p : 𝕄) from hA, Causal.Flat.minkB_add_left,
    Causal.Flat.minkB_smul_left, Causal.Flat.minkB_smul_left] at h1 h2
  rw [← Causal.Flat.minkQ_eq_minkB, hp] at h1
  rw [hue] at h2
  show nullPairing p σ = 0
  rw [nullPairing_liftT p hp, Causal.Flat.minkB_comm]
  by_contra hne
  have hc1 : c = 1 := by
    have : (c - 1) * Causal.Flat.minkB w (p : 𝕄) = 0 := by linarith
    linarith [(mul_eq_zero.1 this).resolve_right hne]
  rw [hc1] at h2
  exact hne (by linarith)

/-- `Γ_p` fixes the two tangent directions, at a lightlike `p`. -/
theorem smul_eq_of_null (hp : Causal.Flat.minkQ (p : 𝕄) = 0) {σ : Link p}
    (h0 : nullPairing p σ = 0) (A : GammaP p) : A • σ = σ := by
  rw [gammaP_smul_eq_iff]
  set T := GammaP.tangent A
  have hσ0 : (σ : TpHS p) ≠ 0 := raySphere_ne_zero σ
  obtain ⟨w₀, -, hB₀⟩ := exists_minkB_neg hp
  set e := tpMk p w₀
  have hφe : nullPairing p e ≠ 0 := by rw [nullPairing_mk p hp]; exact hB₀.ne
  have harea : linkArea p σ e ≠ 0 := by
    intro h
    obtain ⟨r, hr⟩ := eq_smul_of_linkArea_eq_zero p hσ0 h
    apply hφe
    rw [hr, map_smul, h0, smul_zero]
  have hy := eq_add_of_linkArea_ne_zero p harea (T σ)
  have he' := eq_add_of_linkArea_ne_zero p harea (T e)
  set a := linkArea p (T σ) e / linkArea p σ e
  set b := linkArea p σ (T σ) / linkArea p σ e
  set c := linkArea p (T e) e / linkArea p σ e
  set d := linkArea p σ (T e) / linkArea p σ e
  have hb : b = 0 := by
    have := congrArg (nullPairing p) hy
    rw [nullPairing_tangent, h0, map_add, map_smul, map_smul, h0, smul_eq_mul, smul_eq_mul,
      mul_zero, zero_add] at this
    exact (mul_eq_zero.1 this.symm).resolve_right hφe
  have hd : d = 1 := by
    have := congrArg (nullPairing p) he'
    rw [nullPairing_tangent, map_add, map_smul, map_smul, h0, smul_eq_mul, smul_eq_mul, mul_zero,
      zero_add] at this
    have h' : (d - 1) * nullPairing p e = 0 := by linarith
    linarith [(mul_eq_zero.1 h').resolve_right hφe]
  have hTσ : T σ = a • (σ : TpHS p) := by rw [hy, hb, zero_smul, add_zero]
  have hTe : T e = c • (σ : TpHS p) + (1 : ℝ) • e := by rw [he', hd]
  have ha : a = 1 := by
    have := linkArea_tangent p A σ e
    change linkArea p (T σ) (T e) = _ at this
    rw [hTσ, hTe, linkArea_smul_left, linkArea_add_smul, linkArea_self] at this
    have h' : (a - 1) * linkArea p σ e = 0 := by linarith
    linarith [(mul_eq_zero.1 h').resolve_right harea]
  exact ⟨1, one_pos, by rw [hTσ, ha]⟩

/-- **The fixed points of `Γ_p` at a lightlike `p`** are the two tangent directions. -/
theorem fixedPoints_eq_of_null (hp : Causal.Flat.minkQ (p : 𝕄) = 0) :
    {σ : Link p | ∀ A : GammaP p, A • σ = σ} = tangentDirs p :=
  (fixedPoints_subset_of_null hp).antisymm fun _ h0 A => smul_eq_of_null hp h0 A

end Fixed

/-! ### `i^±(ℓ(p))` for every `p ∈ HS²` -/

section IPm

/-- **`i⁺(ℓ(p))`** (l.819–838): the future timelike directions at `p ∈ dS²`; at `p ∈ ∂ℍ²₊` the
directions entering `ℍ²₊`, at `p ∈ ∂ℍ²₋` those entering `dS²`; `∅` at a timelike `p`. -/
def iPlus (p : HS 2) : Set (Link p) :=
  match HS.region p with
  | .deSitter => dsFutureDirs p
  | .bdPlus => lightDomain p .hypPlus
  | .bdMinus => lightDomain p .deSitter
  | .hypPlus => ∅
  | .hypMinus => ∅

/-- **`i⁻(ℓ(p))`** (l.819–838): the past timelike directions at `p ∈ dS²`; at `p ∈ ∂ℍ²₊` the
directions entering `dS²`, at `p ∈ ∂ℍ²₋` those entering `ℍ²₋`; `∅` at a timelike `p`. -/
def iMinus (p : HS 2) : Set (Link p) :=
  match HS.region p with
  | .deSitter => dsPastDirs p
  | .bdPlus => lightDomain p .deSitter
  | .bdMinus => lightDomain p .hypMinus
  | .hypPlus => ∅
  | .hypMinus => ∅

variable {p : HS 2}

theorem iPlus_of_deSitter (hp : p ∈ HS.piece 2 .deSitter) : iPlus p = dsFutureDirs p := by
  simp only [iPlus, HS.region_eq_of_mem hp]

theorem iMinus_of_deSitter (hp : p ∈ HS.piece 2 .deSitter) : iMinus p = dsPastDirs p := by
  simp only [iMinus, HS.region_eq_of_mem hp]

theorem iPlus_of_bdPlus (hp : p ∈ HS.piece 2 .bdPlus) : iPlus p = lightDomain p .hypPlus := by
  simp only [iPlus, HS.region_eq_of_mem hp]

theorem iMinus_of_bdPlus (hp : p ∈ HS.piece 2 .bdPlus) : iMinus p = lightDomain p .deSitter := by
  simp only [iMinus, HS.region_eq_of_mem hp]

theorem iPlus_of_bdMinus (hp : p ∈ HS.piece 2 .bdMinus) : iPlus p = lightDomain p .deSitter := by
  simp only [iPlus, HS.region_eq_of_mem hp]

theorem iMinus_of_bdMinus (hp : p ∈ HS.piece 2 .bdMinus) : iMinus p = lightDomain p .hypMinus := by
  simp only [iMinus, HS.region_eq_of_mem hp]

/-- **l.838**: `i⁺(ℓ(p)) = i⁻(ℓ(p)) = ∅` at a timelike `p`. -/
theorem iPlus_iMinus_of_timelike (hp : Causal.Flat.minkQ (p : 𝕄) < 0) :
    iPlus p = ∅ ∧ iMinus p = ∅ := by
  rcases Causal.Flat.isFutureTimelike_or_neg hp with h | h
  · have hr : HS.region p = .hypPlus := HS.region_eq_of_mem (k := .hypPlus) h
    simp only [iPlus, iMinus, hr, and_self]
  · have hr : HS.region p = .hypMinus := HS.region_eq_of_mem (k := .hypMinus) h
    simp only [iPlus, iMinus, hr, and_self]

theorem smul_mem_nullNeg_iff (A : GammaP p) {σ : Link p} :
    nullPairing p (A • σ : Link p) < 0 ↔ nullPairing p σ < 0 := by
  rw [nullPairing_smul]
  have hc : 0 < ‖GammaP.tangent A σ‖⁻¹ := inv_pos.2 (norm_pos_iff.2 (tangent_ne_zero p A σ))
  exact ⟨fun h => by by_contra h'; push Not at h'; nlinarith, fun h => mul_neg_of_pos_of_neg hc h⟩

theorem smul_mem_nullNonneg_iff (A : GammaP p) {σ : Link p} :
    0 ≤ nullPairing p (A • σ : Link p) ↔ 0 ≤ nullPairing p σ := by
  rw [nullPairing_smul]
  have hc : 0 < ‖GammaP.tangent A σ‖⁻¹ := inv_pos.2 (norm_pos_iff.2 (tangent_ne_zero p A σ))
  exact mul_nonneg_iff_of_pos_left hc

/-- `Γ_p` preserves `i⁺(ℓ(p))`. -/
theorem smul_mem_iPlus_iff (A : GammaP p) {σ : Link p} : A • σ ∈ iPlus p ↔ σ ∈ iPlus p := by
  rcases hk : HS.region p with _ | _ | _ | _ | _
  · simp only [iPlus, hk, mem_empty_iff_false]
  · simp only [iPlus, hk, mem_empty_iff_false]
  · simp only [iPlus, hk]; exact smul_mem_dsFutureDirs_iff p A
  · have hp : p ∈ HS.piece 2 .bdPlus := HS.mem_piece_iff_region.2 hk
    simp only [iPlus, hk, lightDomain_hypPlus_eq hp, mem_setOf_eq]
    exact smul_mem_nullNeg_iff A
  · have hp : p ∈ HS.piece 2 .bdMinus := HS.mem_piece_iff_region.2 hk
    simp only [iPlus, hk, lightDomain_deSitter_eq hp.1, mem_setOf_eq]
    exact smul_mem_nullNonneg_iff A

/-- `Γ_p` preserves `i⁻(ℓ(p))`. -/
theorem smul_mem_iMinus_iff (A : GammaP p) {σ : Link p} : A • σ ∈ iMinus p ↔ σ ∈ iMinus p := by
  rcases hk : HS.region p with _ | _ | _ | _ | _
  · simp only [iMinus, hk, mem_empty_iff_false]
  · simp only [iMinus, hk, mem_empty_iff_false]
  · simp only [iMinus, hk]; exact smul_mem_dsPastDirs_iff p A
  · have hp : p ∈ HS.piece 2 .bdPlus := HS.mem_piece_iff_region.2 hk
    simp only [iMinus, hk, lightDomain_deSitter_eq hp.1, mem_setOf_eq]
    exact smul_mem_nullNonneg_iff A
  · have hp : p ∈ HS.piece 2 .bdMinus := HS.mem_piece_iff_region.2 hk
    simp only [iMinus, hk, lightDomain_hypMinus_eq hp, mem_setOf_eq]
    exact smul_mem_nullNeg_iff A

/-- `i⁺(ℓ(p))` is open, except at `p ∈ ∂ℍ²₋`. -/
theorem isOpen_iPlus (hp : p ∉ HS.piece 2 .bdMinus) : IsOpen (iPlus p) := by
  rcases hk : HS.region p with _ | _ | _ | _ | _
  · simp only [iPlus, hk, isOpen_empty]
  · simp only [iPlus, hk, isOpen_empty]
  · simp only [iPlus, hk]; exact isOpen_dsFutureDirs p
  · have hp' : p ∈ HS.piece 2 .bdPlus := HS.mem_piece_iff_region.2 hk
    simp only [iPlus, hk, lightDomain_hypPlus_eq hp']
    exact isOpen_lt (continuous_nullPairing p) continuous_const
  · exact absurd (HS.mem_piece_iff_region.2 hk) hp

/-- `i⁻(ℓ(p))` is open, except at `p ∈ ∂ℍ²₊`. -/
theorem isOpen_iMinus (hp : p ∉ HS.piece 2 .bdPlus) : IsOpen (iMinus p) := by
  rcases hk : HS.region p with _ | _ | _ | _ | _
  · simp only [iMinus, hk, isOpen_empty]
  · simp only [iMinus, hk, isOpen_empty]
  · simp only [iMinus, hk]; exact isOpen_dsPastDirs p
  · exact absurd (HS.mem_piece_iff_region.2 hk) hp
  · have hp' : p ∈ HS.piece 2 .bdMinus := HS.mem_piece_iff_region.2 hk
    simp only [iMinus, hk, lightDomain_hypMinus_eq hp']
    exact isOpen_lt (continuous_nullPairing p) continuous_const

/-- A tangent direction is a limit of directions with `B(p, ·) < 0`, and of directions with
`B(p, ·) > 0`. -/
theorem mem_closure_nullPairing (hp : Causal.Flat.minkQ (p : 𝕄) = 0) {σ : Link p}
    (h0 : nullPairing p σ = 0) :
    σ ∈ closure {τ : Link p | nullPairing p τ < 0} ∧
      σ ∈ closure {τ : Link p | 0 < nullPairing p τ} := by
  obtain ⟨n, -, hn⟩ := exists_minkB_neg hp
  have hB0 : Causal.Flat.minkB (p : 𝕄) (liftT p σ) = 0 := by rw [← nullPairing_liftT p hp]; exact h0
  have key : ∀ (e : 𝕄) (s : ℝ), s * Causal.Flat.minkB (p : 𝕄) e < 0 →
      σ ∈ closure {τ : Link p | s * nullPairing p τ < 0} := by
    intro e s hse
    refine mem_closure_of_tendsto (tendsto_dirOf_add p σ e) ?_
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    have hB : Causal.Flat.minkB (p : 𝕄) (liftT p σ + ε • e) =
        ε * Causal.Flat.minkB (p : 𝕄) e := by
      rw [Causal.Flat.minkB_add_right, hB0, zero_add, Causal.Flat.minkB_smul_right]
    have hne : tpMk p (liftT p σ + ε • e) ≠ 0 := fun h => by
      have := nullPairing_mk p hp (liftT p σ + ε • e)
      rw [h, map_zero, hB] at this
      have : s * (ε * Causal.Flat.minkB (p : 𝕄) e) = 0 := by rw [← this, mul_zero]
      nlinarith
    show s * nullPairing p (dirOf p (liftT p σ + ε • e)) < 0
    rw [nullPairing_dirOf p hp hne, hB]
    have hc : 0 < ‖tpMk p (liftT p σ + ε • e)‖⁻¹ := inv_pos.2 (norm_pos_iff.2 hne)
    nlinarith [mul_pos hc hε]
  refine ⟨?_, ?_⟩
  · have := key n 1 (by rw [one_mul]; exact hn)
    simpa only [one_mul] using this
  · have := key (-n) (-1) (by rw [Causal.Flat.minkB_neg_right]; linarith)
    simpa only [neg_one_mul, neg_lt_zero] using this

theorem frontier_nullNeg (hp : Causal.Flat.minkQ (p : 𝕄) = 0) :
    frontier {σ : Link p | nullPairing p σ < 0} = tangentDirs p := by
  ext σ
  rw [frontier_eq_closure_inter_closure]
  constructor
  · rintro ⟨h1, h2⟩
    have h1' : nullPairing p σ ≤ 0 :=
      closure_minimal (t := {τ : Link p | nullPairing p τ ≤ 0})
        (fun τ (hτ : nullPairing p τ < 0) => hτ.le)
        (isClosed_le (continuous_nullPairing p) continuous_const) h1
    have h2' : 0 ≤ nullPairing p σ :=
      closure_minimal (t := {τ : Link p | 0 ≤ nullPairing p τ})
        (fun τ (hτ : ¬ (nullPairing p τ < 0)) => not_lt.1 hτ)
        (isClosed_le continuous_const (continuous_nullPairing p)) h2
    exact le_antisymm h1' h2'
  · intro h0
    exact ⟨(mem_closure_nullPairing hp h0).1, subset_closure (by
      show ¬ (nullPairing p σ < 0); rw [show nullPairing p σ = 0 from h0]; exact lt_irrefl 0)⟩

theorem frontier_nullNonneg (hp : Causal.Flat.minkQ (p : 𝕄) = 0) :
    frontier {σ : Link p | 0 ≤ nullPairing p σ} = tangentDirs p := by
  have : {σ : Link p | 0 ≤ nullPairing p σ} = {σ : Link p | nullPairing p σ < 0}ᶜ := by
    ext σ; simp only [mem_setOf_eq, mem_compl_iff, not_lt]
  rw [this, frontier_compl, frontier_nullNeg hp]

/-- **A slip in l.828–833**: at `p ∈ ∂ℍ²₊`, `i⁻(ℓ(p))` contains the two tangent directions, so it
is not open. -/
theorem not_isOpen_iMinus_of_bdPlus (hp : p ∈ HS.piece 2 .bdPlus) : ¬ IsOpen (iMinus p) := by
  intro ho
  rw [iMinus_of_bdPlus hp, lightDomain_deSitter_eq hp.1] at ho
  have h := ho.frontier_eq
  rw [frontier_nullNonneg hp.1] at h
  have hne : (tangentDirs p).Nonempty := by
    rw [tangentDirs_eq hp.1]; exact ⟨_, mem_insert _ _⟩
  obtain ⟨σ, hσ⟩ := hne
  have := h ▸ hσ
  exact this.2 (show 0 ≤ nullPairing p σ from le_of_eq hσ.symm)

/-- The same at `p ∈ ∂ℍ²₋`, for `i⁺(ℓ(p))`. -/
theorem not_isOpen_iPlus_of_bdMinus (hp : p ∈ HS.piece 2 .bdMinus) : ¬ IsOpen (iPlus p) := by
  intro ho
  rw [iPlus_of_bdMinus hp, lightDomain_deSitter_eq hp.1] at ho
  have h := ho.frontier_eq
  rw [frontier_nullNonneg hp.1] at h
  have hne : (tangentDirs p).Nonempty := by
    rw [tangentDirs_eq hp.1]; exact ⟨_, mem_insert _ _⟩
  obtain ⟨σ, hσ⟩ := hne
  have := h ▸ hσ
  exact this.2 (show 0 ≤ nullPairing p σ from le_of_eq hσ.symm)

theorem nullNonneg_sdiff (p : HS 2) :
    {σ : Link p | 0 ≤ nullPairing p σ} \ tangentDirs p = {σ : Link p | 0 < nullPairing p σ} := by
  ext σ
  simp only [Set.mem_sdiff, mem_setOf_eq, tangentDirs]
  exact ⟨fun h => lt_of_le_of_ne h.1 (Ne.symm h.2), fun h => ⟨h.le, h.ne'⟩⟩

/-- **l.835–836, corrected**: at `p ∈ ∂ℍ²₊` the components of the complement of the two tangent
directions are `i⁺(ℓ(p))` and `i⁻(ℓ(p))` minus the tangent directions (its interior). -/
theorem components_compl_tangentDirs_of_bdPlus (hp : p ∈ HS.piece 2 .bdPlus) :
    {K | ∃ σ ∈ (tangentDirs p)ᶜ, connectedComponentIn (tangentDirs p)ᶜ σ = K} =
      {iPlus p, iMinus p \ tangentDirs p} := by
  rw [components_compl_tangentDirs hp.1, iPlus_of_bdPlus hp, iMinus_of_bdPlus hp,
    lightDomain_hypPlus_eq hp, lightDomain_deSitter_eq hp.1, nullNonneg_sdiff]

theorem tangentDirs_subset_lightDomain_deSitter (hp : Causal.Flat.minkQ (p : 𝕄) = 0) :
    tangentDirs p ⊆ lightDomain p .deSitter := by
  rw [lightDomain_deSitter_eq hp]
  intro σ (hσ : nullPairing p σ = 0)
  show 0 ≤ nullPairing p σ
  rw [hσ]

theorem not_mem_components_of_tangent (hp : Causal.Flat.minkQ (p : 𝕄) = 0) {S : Set (Link p)}
    (hS : tangentDirs p ⊆ S) :
    S ∉ {K | ∃ σ ∈ (tangentDirs p)ᶜ, connectedComponentIn (tangentDirs p)ᶜ σ = K} := by
  rintro ⟨σ, -, hK⟩
  obtain ⟨τ, hτ⟩ : (tangentDirs p).Nonempty := by
    rw [tangentDirs_eq hp]; exact ⟨_, mem_insert _ _⟩
  have h1 := connectedComponentIn_subset (tangentDirs p)ᶜ σ
  rw [hK] at h1
  exact h1 (hS hτ) hτ

/-- **l.835–836 as printed is false** at `p ∈ ∂ℍ²₊`: `i⁻(ℓ(p))` is not a component of the
complement of the tangent directions. -/
theorem components_compl_tangentDirs_ne_of_bdPlus (hp : p ∈ HS.piece 2 .bdPlus) :
    {K | ∃ σ ∈ (tangentDirs p)ᶜ, connectedComponentIn (tangentDirs p)ᶜ σ = K} ≠
      {iPlus p, iMinus p} := by
  intro h
  refine not_mem_components_of_tangent hp.1 (S := iMinus p) ?_ (h ▸ Or.inr rfl)
  rw [iMinus_of_bdPlus hp]
  exact tangentDirs_subset_lightDomain_deSitter hp.1

/-- **l.835–836, corrected**, at `p ∈ ∂ℍ²₋`. -/
theorem components_compl_tangentDirs_of_bdMinus (hp : p ∈ HS.piece 2 .bdMinus) :
    {K | ∃ σ ∈ (tangentDirs p)ᶜ, connectedComponentIn (tangentDirs p)ᶜ σ = K} =
      {iPlus p \ tangentDirs p, iMinus p} := by
  rw [components_compl_tangentDirs hp.1, iPlus_of_bdMinus hp, iMinus_of_bdMinus hp,
    lightDomain_hypMinus_eq hp, lightDomain_deSitter_eq hp.1, nullNonneg_sdiff, Set.pair_comm]

theorem components_compl_tangentDirs_ne_of_bdMinus (hp : p ∈ HS.piece 2 .bdMinus) :
    {K | ∃ σ ∈ (tangentDirs p)ᶜ, connectedComponentIn (tangentDirs p)ᶜ σ = K} ≠
      {iPlus p, iMinus p} := by
  intro h
  refine not_mem_components_of_tangent hp.1 (S := iPlus p) ?_ (h ▸ Or.inl rfl)
  rw [iPlus_of_bdMinus hp]
  exact tangentDirs_subset_lightDomain_deSitter hp.1

/-- **l.840: the extremities of the arcs `i^±(ℓ(p))` are precisely the fixed points of `Γ_p`**,
for every `p ∈ HS²` (four at `p ∈ dS²`, two at `p ∈ ∂ℍ²±`, none at a timelike `p`). -/
theorem frontier_iPlus_union_frontier_iMinus (p : HS 2) :
    frontier (iPlus p) ∪ frontier (iMinus p) = {σ : Link p | ∀ A : GammaP p, A • σ = σ} := by
  rcases hk : HS.region p with _ | _ | _ | _ | _
  · have hp : p ∈ HS.piece 2 .hypPlus := HS.mem_piece_iff_region.2 hk
    simp only [iPlus, iMinus, hk, frontier_empty, union_self]
    exact (fixedPoints_eq_empty_of_timelike hp.2).symm
  · have hp : p ∈ HS.piece 2 .hypMinus := HS.mem_piece_iff_region.2 hk
    have hq : Causal.Flat.minkQ (p : 𝕄) < 0 := by
      have := hp.2; rwa [Causal.Flat.minkQ_neg] at this
    simp only [iPlus, iMinus, hk, frontier_empty, union_self]
    exact (fixedPoints_eq_empty_of_timelike hq).symm
  · have hp : p ∈ HS.piece 2 .deSitter := HS.mem_piece_iff_region.2 hk
    simp only [iPlus, iMinus, hk]
    rw [frontier_ds hp, fixedPoints_eq_of_deSitter hp]
  · have hp : p ∈ HS.piece 2 .bdPlus := HS.mem_piece_iff_region.2 hk
    simp only [iPlus, iMinus, hk]
    rw [lightDomain_hypPlus_eq hp, lightDomain_deSitter_eq hp.1, frontier_nullNeg hp.1,
      frontier_nullNonneg hp.1, union_self, fixedPoints_eq_of_null hp.1]
  · have hp : p ∈ HS.piece 2 .bdMinus := HS.mem_piece_iff_region.2 hk
    simp only [iPlus, iMinus, hk]
    rw [lightDomain_hypMinus_eq hp, lightDomain_deSitter_eq hp.1, frontier_nullNeg hp.1,
      frontier_nullNonneg hp.1, union_self, fixedPoints_eq_of_null hp.1]

end IPm

/-! ### `i^±(L)` (`bbsdef:circle_developing_map_preimages`) -/

section Circle

variable {L : Type*} [TopologicalSpace L]

/-- **`i⁺(L)`** (l.845): the points of `L` whose chart value lies in `i⁺(ℓ(p))`
(chart-independent: `GX.GammaLinkCircle.mem_iPlusL_iff_of_mem_maximalAtlas`); it is the projection
of `d⁻¹(i⁺(ℓ(p)))` for every developing map `d`
(`GX.GammaLinkCircle.IsDevAlong.image_preimage_iPlus`). -/
def GammaLinkCircle.iPlusL (C : GammaLinkCircle L) : Set L :=
  {x | @chartAt (Link C.pt) _ L _ C.atlas x x ∈ GX.iPlus C.pt}

/-- **`i⁻(L)`** (l.845). -/
def GammaLinkCircle.iMinusL (C : GammaLinkCircle L) : Set L :=
  {x | @chartAt (Link C.pt) _ L _ C.atlas x x ∈ GX.iMinus C.pt}

/-- A `Γ_p`-invariant set of directions read in two charts of the maximal atlas. -/
theorem GammaLinkCircle.chart_mem_iff_of_mem_maximalAtlas (C : GammaLinkCircle L)
    {S : Set (Link C.pt)} (hS : ∀ (A : GammaP C.pt) σ, A • σ ∈ S ↔ σ ∈ S)
    {e : OpenPartialHomeomorph L (Link C.pt)}
    (he : e ∈ @StructureGroupoid.maximalAtlas (Link C.pt) L _ _ C.atlas
      (gxGroupoid (GammaP C.pt) (Link C.pt))) {x : L} (hx : x ∈ e.source) :
    @chartAt (Link C.pt) _ L _ C.atlas x x ∈ S ↔ e x ∈ S := by
  letI := C.atlas
  haveI := C.hasGroupoid
  obtain ⟨g, hg⟩ := eventually_smul_eq_of_mem_maximalAtlas
    ((gxGroupoid (GammaP C.pt) (Link C.pt)).chart_mem_maximalAtlas x) he
    (mem_chart_source (Link C.pt) x) hx
  rw [hg.self_of_nhds, hS]

theorem GammaLinkCircle.mem_iPlusL_iff_of_mem_maximalAtlas (C : GammaLinkCircle L)
    {e : OpenPartialHomeomorph L (Link C.pt)}
    (he : e ∈ @StructureGroupoid.maximalAtlas (Link C.pt) L _ _ C.atlas
      (gxGroupoid (GammaP C.pt) (Link C.pt))) {x : L} (hx : x ∈ e.source) :
    x ∈ C.iPlusL ↔ e x ∈ GX.iPlus C.pt :=
  C.chart_mem_iff_of_mem_maximalAtlas (fun A _ => smul_mem_iPlus_iff A) he hx

theorem GammaLinkCircle.mem_iMinusL_iff_of_mem_maximalAtlas (C : GammaLinkCircle L)
    {e : OpenPartialHomeomorph L (Link C.pt)}
    (he : e ∈ @StructureGroupoid.maximalAtlas (Link C.pt) L _ _ C.atlas
      (gxGroupoid (GammaP C.pt) (Link C.pt))) {x : L} (hx : x ∈ e.source) :
    x ∈ C.iMinusL ↔ e x ∈ GX.iMinus C.pt :=
  C.chart_mem_iff_of_mem_maximalAtlas (fun A _ => smul_mem_iMinus_iff A) he hx

variable {C : GammaLinkCircle L} {M : Type*} [TopologicalSpace M] {E : M → L}
  {d : M → Link C.pt}

/-- A developing map, read at a point: `d s` is a `Γ_p`-translate of the chart value of `E s`. -/
theorem GammaLinkCircle.IsDevAlong.exists_eq_smul_chart (hd : C.IsDevAlong E d) (s : M) :
    ∃ A : GammaP C.pt, d s = A • @chartAt (Link C.pt) _ L _ C.atlas (E s) (E s) := by
  obtain ⟨A, hA⟩ := hd s
  exact ⟨A, hA.self_of_nhds⟩

theorem GammaLinkCircle.IsDevAlong.preimage_eq {S : Set (Link C.pt)}
    (hS : ∀ (A : GammaP C.pt) σ, A • σ ∈ S ↔ σ ∈ S) (hd : C.IsDevAlong E d) :
    d ⁻¹' S = E ⁻¹' {x | @chartAt (Link C.pt) _ L _ C.atlas x x ∈ S} := by
  ext s
  obtain ⟨A, hA⟩ := hd.exists_eq_smul_chart s
  simp only [mem_preimage, mem_setOf_eq, hA, hS]

theorem GammaLinkCircle.IsDevAlong.preimage_iPlus (hd : C.IsDevAlong E d) :
    d ⁻¹' GX.iPlus C.pt = E ⁻¹' C.iPlusL :=
  hd.preimage_eq fun A _ => smul_mem_iPlus_iff A

theorem GammaLinkCircle.IsDevAlong.preimage_iMinus (hd : C.IsDevAlong E d) :
    d ⁻¹' GX.iMinus C.pt = E ⁻¹' C.iMinusL :=
  hd.preimage_eq fun A _ => smul_mem_iMinus_iff A

/-- A developing map along a continuous `E` is continuous. -/
theorem GammaLinkCircle.IsDevAlong.continuous (hE : Continuous E) (hd : C.IsDevAlong E d) :
    Continuous d := by
  letI := C.atlas
  refine continuous_iff_continuousAt.2 fun s => ?_
  obtain ⟨A, hA⟩ := hd s
  have hc : ContinuousAt (fun s' => A • chartAt (Link C.pt) (E s) (E s')) s :=
    (continuous_const_smul A).continuousAt.comp
      (((chartAt (Link C.pt) (E s)).continuousAt (mem_chart_source _ _)).comp hE.continuousAt)
  exact hc.congr (hA.mono fun s' h => h.symm)

/-- **l.844, deck invariance**: `d⁻¹(i^±(ℓ(p)))` is preserved by every deck transformation. -/
theorem GammaLinkCircle.IsDevAlong.deck_iPlus (hd : C.IsDevAlong E d) {φ : M → M}
    (hφ : E ∘ φ = E) : φ ⁻¹' (d ⁻¹' GX.iPlus C.pt) = d ⁻¹' GX.iPlus C.pt := by
  rw [hd.preimage_iPlus, ← preimage_comp, hφ]

theorem GammaLinkCircle.IsDevAlong.deck_iMinus (hd : C.IsDevAlong E d) {φ : M → M}
    (hφ : E ∘ φ = E) : φ ⁻¹' (d ⁻¹' GX.iMinus C.pt) = d ⁻¹' GX.iMinus C.pt := by
  rw [hd.preimage_iMinus, ← preimage_comp, hφ]

/-- **l.845**: the projection of `d⁻¹(i⁺(ℓ(p)))` to `L` is `i⁺(L)`. -/
theorem GammaLinkCircle.IsDevAlong.image_preimage_iPlus (hd : C.IsDevAlong E d)
    (hE : Function.Surjective E) : E '' (d ⁻¹' GX.iPlus C.pt) = C.iPlusL := by
  rw [hd.preimage_iPlus, image_preimage_eq _ hE]

theorem GammaLinkCircle.IsDevAlong.image_preimage_iMinus (hd : C.IsDevAlong E d)
    (hE : Function.Surjective E) : E '' (d ⁻¹' GX.iMinus C.pt) = C.iMinusL := by
  rw [hd.preimage_iMinus, image_preimage_eq _ hE]

/-- **l.844, openness**, wherever the arc is open: `d⁻¹(i⁺(ℓ(p)))` is open unless `p ∈ ∂ℍ²₋`. -/
theorem GammaLinkCircle.IsDevAlong.isOpen_preimage_iPlus (hE : Continuous E)
    (hd : C.IsDevAlong E d) (hp : C.pt ∉ HS.piece 2 .bdMinus) :
    IsOpen (d ⁻¹' GX.iPlus C.pt) :=
  (isOpen_iPlus hp).preimage (hd.continuous hE)

theorem GammaLinkCircle.IsDevAlong.isOpen_preimage_iMinus (hE : Continuous E)
    (hd : C.IsDevAlong E d) (hp : C.pt ∉ HS.piece 2 .bdPlus) :
    IsOpen (d ⁻¹' GX.iMinus C.pt) :=
  (isOpen_iMinus hp).preimage (hd.continuous hE)

/-- **l.844 as printed fails at a lightlike `p`**: for the link of a regular point of `∂ℍ²₊` and
its developing map, `d⁻¹(i⁻(ℓ(p)))` is not open. -/
theorem not_isOpen_preimage_iMinus_regular {p : HS 2} (hp : p ∈ HS.piece 2 .bdPlus) :
    ∃ E : ℝ → Link p, IsPeriodicCover E ∧ ∃ d : ℝ → Link p,
      (GammaLinkCircle.regular p).IsDevAlong E d ∧ ¬ IsOpen (d ⁻¹' GX.iMinus p) := by
  obtain ⟨E, hE⟩ := exists_isPeriodicCover (isCircle_link p)
  refine ⟨E, hE, E, fun s => ⟨1, Eventually.of_forall fun s' => ?_⟩, fun ho => ?_⟩
  · show E s' = (1 : GammaP p) • (chartAt (Link p) (E s)) (E s')
    rw [one_smul, chartAt_self_eq, OpenPartialHomeomorph.refl_apply, id]
  · have h := hE.isCoveringMap.isOpenMap _ ho
    rw [image_preimage_eq _ hE.surjective] at h
    exact not_isOpen_iMinus_of_bdPlus hp h

/-- `bbsdef:circle_developing_map_preimages`, assembled (l.842–846): every `(Γ_p, ℓ(p))`-circle
has a developing map `d : L̃ = ℝ → ℓ(p)` along its universal covering; the preimages
`d⁻¹(i^±(ℓ(p)))` are preserved by the deck transformations, open wherever the arc is open, and
project onto `i^±(L)`. -/
theorem GammaLinkCircle.devPreimages (C : GammaLinkCircle L) :
    ∃ E : ℝ → L, IsPeriodicCover E ∧ ∃ d : ℝ → Link C.pt, C.IsDevAlong E d ∧
      (∀ φ : ℝ → ℝ, E ∘ φ = E → φ ⁻¹' (d ⁻¹' GX.iPlus C.pt) = d ⁻¹' GX.iPlus C.pt ∧
        φ ⁻¹' (d ⁻¹' GX.iMinus C.pt) = d ⁻¹' GX.iMinus C.pt) ∧
      (C.pt ∉ HS.piece 2 .bdMinus → IsOpen (d ⁻¹' GX.iPlus C.pt)) ∧
      (C.pt ∉ HS.piece 2 .bdPlus → IsOpen (d ⁻¹' GX.iMinus C.pt)) ∧
      E '' (d ⁻¹' GX.iPlus C.pt) = C.iPlusL ∧ E '' (d ⁻¹' GX.iMinus C.pt) = C.iMinusL := by
  obtain ⟨E, hE, d, hd, -⟩ := C.exists_isDevAlong
  have hEc := hE.isCoveringMap.continuous
  exact ⟨E, hE, d, hd, fun φ hφ => ⟨hd.deck_iPlus hφ, hd.deck_iMinus hφ⟩,
    hd.isOpen_preimage_iPlus hEc, hd.isOpen_preimage_iMinus hEc,
    hd.image_preimage_iPlus hE.surjective, hd.image_preimage_iMinus hE.surjective⟩

end Circle

/-! ### The two readings, tested against l.844 -/

section Readings

variable {p : HS 2}

/-- `ℓ(p)` is connected. -/
theorem preconnectedSpace_link (p : HS 2) : PreconnectedSpace (Link p) := by
  refine preconnectedSpace_raySphere ?_
  rw [← Module.finrank_eq_rank, finrank_tpHS]
  norm_num

/-- **The causal reading of l.820 contradicts l.844**: at `p ∈ dS²`, the future *causal*
directions form a nonempty proper closed subset of the circle `ℓ(p)`, hence not an open one; its
preimage under the developing map of the regular link is not open. So "future oriented" is read
"future timelike" (`GX.dsFutureDirs`). -/
theorem not_isOpen_dsFutureCausalDirs (hp : p ∈ HS.piece 2 .deSitter) :
    ¬ IsOpen {σ : Link p | Causal.Flat.IsFutureCausal (dsProj p σ)} := by
  intro ho
  haveI := preconnectedSpace_link p
  have hc : IsClosed {σ : Link p | Causal.Flat.IsFutureCausal (dsProj p σ)} :=
    isClosed_isFutureCausal.preimage (continuous_dsProj p)
  rcases isClopen_iff.1 ⟨hc, ho⟩ with h | h
  · obtain ⟨σ, hσ⟩ := (isConnected_dsFutureDirs hp).nonempty
    have : σ ∈ {σ : Link p | Causal.Flat.IsFutureCausal (dsProj p σ)} := ⟨hσ.1.le, hσ.2.le⟩
    rw [h] at this; exact this
  · obtain ⟨σ, hσ⟩ := (isConnected_dsPastDirs hp).nonempty
    have : σ ∈ {σ : Link p | Causal.Flat.IsFutureCausal (dsProj p σ)} := h ▸ mem_univ σ
    have h1 := this.1
    have h2 := hσ.1
    simp only [Prod.fst_neg] at h2
    linarith

/-- Under the causal reading, l.844 fails at every `p ∈ dS²`: for the regular link, the preimage
of the closed arc of future causal directions under its developing map is not open. -/
theorem not_isOpen_preimage_dsFutureCausal_regular (hp : p ∈ HS.piece 2 .deSitter) :
    ∃ E : ℝ → Link p, IsPeriodicCover E ∧ ∃ d : ℝ → Link p,
      (GammaLinkCircle.regular p).IsDevAlong E d ∧
        ¬ IsOpen (d ⁻¹' {σ : Link p | Causal.Flat.IsFutureCausal (dsProj p σ)}) := by
  obtain ⟨E, hE⟩ := exists_isPeriodicCover (isCircle_link p)
  refine ⟨E, hE, E, fun s => ⟨1, Eventually.of_forall fun s' => ?_⟩, fun ho => ?_⟩
  · show E s' = (1 : GammaP p) • (chartAt (Link p) (E s)) (E s')
    rw [one_smul, chartAt_self_eq, OpenPartialHomeomorph.refl_apply, id]
  · have h := hE.isCoveringMap.isOpenMap _ ho
    rw [image_preimage_eq _ hE.surjective] at h
    exact not_isOpen_dsFutureCausalDirs hp h

/-- **"Open domain" (l.844) cannot mean "open and connected"**: for the regular link at
`p ∈ dS²`, `d⁻¹(i⁺(ℓ(p)))` is invariant under `s ↦ s + 1` and proper, so it is not connected. -/
theorem not_isPreconnected_preimage_iPlus_regular (hp : p ∈ HS.piece 2 .deSitter) :
    ∃ E : ℝ → Link p, IsPeriodicCover E ∧ ∃ d : ℝ → Link p,
      (GammaLinkCircle.regular p).IsDevAlong E d ∧ ¬ IsPreconnected (d ⁻¹' iPlus p) := by
  obtain ⟨E, hE⟩ := exists_isPeriodicCover (isCircle_link p)
  refine ⟨E, hE, E, fun s => ⟨1, Eventually.of_forall fun s' => ?_⟩, fun hc => ?_⟩
  · show E s' = (1 : GammaP p) • (chartAt (Link p) (E s)) (E s')
    rw [one_smul, chartAt_self_eq, OpenPartialHomeomorph.refl_apply, id]
  · rw [iPlus_of_deSitter hp] at hc
    obtain ⟨σ₀, hσ₀⟩ := (isConnected_dsFutureDirs hp).nonempty
    obtain ⟨s₀, rfl⟩ := hE.surjective σ₀
    have hall : E ⁻¹' dsFutureDirs p = univ := by
      refine eq_univ_of_forall fun t => ?_
      obtain ⟨n, hn⟩ := exists_nat_ge |t - s₀|
      have hmem : ∀ m : ℤ, s₀ + m ∈ E ⁻¹' dsFutureDirs p := fun m => by
        show E (s₀ + m) ∈ dsFutureDirs p
        rw [hE.add_int]; exact hσ₀
      have := hc.Icc_subset (hmem (-n)) (hmem n)
      refine this ⟨?_, ?_⟩
      · push_cast; linarith [neg_abs_le (t - s₀)]
      · push_cast; linarith [le_abs_self (t - s₀)]
    obtain ⟨τ, hτ⟩ := (isConnected_dsPastDirs hp).nonempty
    obtain ⟨t, rfl⟩ := hE.surjective τ
    have h1 : E t ∈ dsFutureDirs p := (hall.symm ▸ mem_univ t : t ∈ E ⁻¹' dsFutureDirs p)
    have h2 := h1.1
    have h3 := hτ.1
    simp only [Prod.fst_neg] at h3
    linarith

end Readings

end GX
