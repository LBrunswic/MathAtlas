import Causal.Flat.Nonloxodromic
import Causal.Flat.TitsNull
import Causal.Flat.Loxodromic
import Causal.CompactCauchy
import Causal.CurvesExtend

/-!
# `Causal.Flat.Cla.FiniteCover` — the finite cover `Γ\𝒟(M̃) → M` of Theorem A's proof

T. Barbot, *Globally hyperbolic flat space-times* (`papers/barbot`, arXiv math/0402257), §11
"Proof of Theorem A" (`GHFspace.tex` l.3484–3492 of the labelled file
`papers/barbot/legacy/labeled/GHFspace.tex`), with Rem `remplacefini` (l.2403) and reading R1 of
Theorem A's "up to finite coverings" (DEC-43, l.338–347). **No label is marked**: this file proves
one step ("the cover half") of `bthm:caucomp`'s proof, not the theorem.

* `bthm:caucomp` — `GHFspace.tex:338`, **one step proved, no `sorry`**:
  `exists_finiteCover_quotient_range`. For a developing pair `(𝒟, ρ)` of a flat spacetime `M`
  with `𝒟` injective, and a subgroup `Γ` of finite index in `ρ(π₁ M)`, the open set
  `W = 𝒟(M̃)` is simply connected and `Γ`-invariant, `Γ` acts on it freely and properly
  discontinuously, and `M' = Γ\W` (a flat spacetime) finitely covers `M`: the covering
  `p : Γ\W → M`, `p[w] = proj(𝒟⁻¹ w)`, is a local isometry with fibres `≅ Γ\ρ(π₁ M)`.
  It serves `Classification.exists_finiteCover_tameEmbedding` (its cover half).

> In \S \ref{spapa}, we proved that the developping map ${\mathcal D}: \widetilde{M}
> \rightarrow {\bf M}^{n}$ is injective, identifying $\widetilde{M}$ with an open domain
> contained in a open convex domain $\Omega(\widetilde{S})$, this last domain being
> $\rho(\Gamma)$-invariant, where $\rho: \Gamma \rightarrow \mbox{Isom}({\bf M})^{n}$ is the
> holonomy morphism. Moreover, it is proved that $\rho$ is injective: $\Gamma$ is then identified
> with its image $\rho(\Gamma)$. (l.3485–3492)

> Therefore, if $\Gamma'$ is a finite index subgroup of $\Gamma$, the equality
> $U(\Gamma') = U(\Gamma)$ holds. Thanks to this remark, we can replace
> $\Gamma$ by any finite index subgroup. (l.2404–2407)

> Up to finite coverings and linear twisted products, every Cauchy-complete
> globally hyperbolic flat spacetime can be tamely embedded
> in an absolutely maximal globally hyperbolic spacetime [...] (l.340–342)

**Dimension (kb/0024).** Barbot's `𝐌ⁿ` has total dimension `n`; `Minkowski d` has `d` spatial
dimensions: Barbot's `n` is `d + 1`.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `𝒟` injective (l.3487, from Prop 8.12) | ✓ carried: `hinj : Injective D` |
| `(𝒟, ρ)` the developing pair (l.3486–3490) | ✓ carried: `IsDevelopingPair x₀ D ρ` |
| `ρ` injective (l.3491) | ⚠ weakened: not assumed, **proved** from `hinj` (a deck transformation `δ` with `ρ δ = 1` fixes a point of the injective `𝒟`, hence `δ = 1`) |
| `Γ'` of finite index in `ρ(Γ)` (Rem `remplacefini`, l.2405) | ✓ carried: `hle : Γ ≤ ρ.range`, `hidx : Γ.relIndex ρ.range ≠ 0` |
| `𝒟(M̃) ⊆ Ω(S̃)`, `Ω` convex, `M(S) = Γ\Ω` (l.3488–3493) | ⚠ weakened: `hΩ : range D ⊆ Ω` and `hB : IsQuotientOf B Γ Ω` are carried in the statement (the consumer's interface) but **not used**: freeness and proper discontinuity on `W` are read off the deck group of `M̃` through the homeomorphism `𝒟 : M̃ ≃ W`, not off `B`; convexity is not assumed at all |
| `M` Hausdorff, connected | ✓ carried by `FlatSpacetime` (`T2Space M` gives proper discontinuity through `finite_deck_of_isCompact`) |

## SCOPE (disclosed)

* Only the cover half of `exists_finiteCover_tameEmbedding` is here: `W = range 𝒟`, its simple
  connectedness, and the finite cover `Γ\W → M` with `IsQuotientOf (Γ\W) Γ W`. The tame embedding
  `Γ\W → B` (π₁ of a quotient of a simply connected space by a free properly discontinuous
  action, `Ω` convex hence contractible) is not here.
* The fibre of `p` over `proj z₀` is covered by the image of the finite coset space
  `ρ.range ⧸ Γ` (`q ↦ [q.out⁻¹ • 𝒟 z₀]`); the identification `p⁻¹{y} ≅ Γ\ρ.range` itself (the
  bijection) is not stated, only the finiteness the statement asks.
* The local copies of Classification's `IsLocalIsometry.of_comp_left` / `of_comp_right` and of
  `UniversalCover.exists_deck_apply_eq` are `private` (Classification imports this module, so
  the public names cannot be redeclared).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal.Flat.Cla

open Set Function Filter Topology TopologicalSpace

universe u

variable {d : ℕ}

/-! ### Local isometries: cancellation and descent (private copies of Classification's) -/

section LocalIsometry

variable {X M N : Type*} [TopologicalSpace X] [ChartedSpace (Minkowski d) X]
  [TopologicalSpace M] [ChartedSpace (Minkowski d) M]
  [TopologicalSpace N] [ChartedSpace (Minkowski d) N]

/-- Cancelling an isometric embedding on the left. -/
private theorem isLocalIsometry_of_comp_left {f : X → M} {h : M → N}
    (hh : IsIsometricEmbedding d h) (hhf : IsLocalIsometry d (h ∘ f)) : IsLocalIsometry d f := by
  have hfc : Continuous f := hh.isOpenEmbedding.isEmbedding.continuous_iff.2 hhf.1
  obtain ⟨-, hhf'⟩ := isLocalIsometry_iff_eventually.1 hhf
  obtain ⟨-, hh'⟩ := isLocalIsometry_iff_eventually.1 hh.1
  refine isLocalIsometry_iff_eventually.2 ⟨hfc, fun x => ?_⟩
  obtain ⟨g₁, hg₁⟩ := hhf' x
  obtain ⟨g₂, hg₂⟩ := hh' (f x)
  refine ⟨g₂⁻¹ * g₁, ?_⟩
  filter_upwards [hg₁, hfc.continuousAt.eventually hg₂] with y h1 h2
  simp only [comp_apply] at h1
  rw [mul_smul, ← h1, h2, inv_smul_smul]

/-- Descending a local isometry along a surjective local isometry. -/
private theorem isLocalIsometry_of_comp_right {q : X → M} {f : M → N}
    (hq : IsLocalIsometry d q) (hqs : Surjective q) (hfq : IsLocalIsometry d (f ∘ q)) :
    IsLocalIsometry d f := by
  have hfc : Continuous f :=
    (hq.isOpenMap.isQuotientMap hq.continuous hqs).continuous_iff.2 hfq.1
  obtain ⟨-, hfq'⟩ := isLocalIsometry_iff_eventually.1 hfq
  obtain ⟨-, hq'⟩ := isLocalIsometry_iff_eventually.1 hq
  refine isLocalIsometry_iff_eventually.2 ⟨hfc, fun x => ?_⟩
  obtain ⟨z, rfl⟩ := hqs x
  obtain ⟨g₁, hg₁⟩ := hfq' z
  obtain ⟨g₂, hg₂⟩ := hq' z
  refine ⟨g₁ * g₂⁻¹, ?_⟩
  have hA : {w | chartAt (Minkowski d) (f (q z)) (f (q w)) =
      (g₁ * g₂⁻¹) • chartAt (Minkowski d) (q z) (q w)} ∈ 𝓝 z := by
    filter_upwards [hg₁, hg₂] with w h1 h2
    simp only [comp_apply] at h1
    rw [h1, h2, mul_smul, inv_smul_smul]
  filter_upwards [hq.isOpenMap.image_mem_nhds hA] with y hy
  obtain ⟨w, hw, rfl⟩ := hy
  exact hw

end LocalIsometry

/-- The deck group of the universal cover acts transitively on the fibres. -/
private theorem exists_deck_apply_eq' {Y : Type*} [TopologicalSpace Y] {y₀ : Y}
    (c c' : UniversalCover Y y₀) (h : UniversalCover.proj Y y₀ c = UniversalCover.proj Y y₀ c') :
    ∃ γ : Deck (UniversalCover.proj Y y₀), γ.1 c = c' := by
  obtain ⟨a, ca⟩ := c
  obtain ⟨b, cb⟩ := c'
  change a = b at h
  subst h
  refine ⟨⟨UniversalCover.leftMulHomeomorph (cb.trans ca.symm), rfl⟩, ?_⟩
  change (⟨a, (cb.trans ca.symm).trans ca⟩ : UniversalCover Y y₀) = ⟨a, cb⟩
  rw [Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.symm_trans,
    Path.Homotopic.Quotient.trans_refl]

/-! ### The covering criterion for an intermediate quotient -/

section Sheets

variable {Γ G : Subgroup (isom d)} {W : Opens (Minkowski d)} [FlatQuotient.Invariant Γ W]
  [FlatQuotient.Invariant G W]

variable (Γ) in
/-- The sheet `[g V] ⊆ Γ\W` of a set `V ⊆ W` and `g ∈ G`. -/
private noncomputable def sheet (V : Set W) (g : G) : Set (FlatQuotient Γ W) :=
  FlatQuotient.proj Γ W '' ((fun a : W => g⁻¹ • a) ⁻¹' V)

/-- An element of `Γ`, read in `G`, acts on `W` as it does in `Γ`. -/
private theorem smul_coe_eq (hle : Γ ≤ G) (γ : Γ) (a : W) :
    γ • a = (⟨γ, hle γ.2⟩ : G) • a := rfl

/-- Left translation by `Γ` does not move a sheet (one inclusion). -/
private theorem sheet_mul_subset (hle : Γ ≤ G) (V : Set W) (γ : Γ) (g : G) :
    sheet Γ V (⟨γ, hle γ.2⟩ * g) ⊆ sheet Γ V g := by
  rintro _ ⟨c, hc, rfl⟩
  refine ⟨γ⁻¹ • c, ?_, ?_⟩
  · show g⁻¹ • (γ⁻¹ • c) ∈ V
    have : g⁻¹ • (γ⁻¹ • c) = (⟨γ, hle γ.2⟩ * g)⁻¹ • c := by
      rw [smul_coe_eq hle, mul_inv_rev, mul_smul]
      rfl
    rw [this]
    exact hc
  · exact (FlatQuotient.proj_eq_proj_iff.2 ⟨γ⁻¹, rfl⟩).symm.symm

/-- Left translation by `Γ` does not move a sheet. -/
private theorem sheet_mul (hle : Γ ≤ G) (V : Set W) (γ : Γ) (g : G) :
    sheet Γ V (⟨γ, hle γ.2⟩ * g) = sheet Γ V g := by
  refine (sheet_mul_subset hle V γ g).antisymm ?_
  have := sheet_mul_subset hle V γ⁻¹ (⟨γ, hle γ.2⟩ * g)
  rwa [← mul_assoc, show (⟨((γ⁻¹ : Γ) : isom d), hle (γ⁻¹).2⟩ : G) * ⟨γ, hle γ.2⟩ = 1 from
    Subtype.ext (by simp), one_mul] at this

/-- **Two sheets which meet are equal**, when `π` is injective on `V` with fibres the
`G`-orbits and `G` acts freely. -/
private theorem sheet_eq_of_meet (hle : Γ ≤ G) {Y : Type*} {π : W → Y}
    (hπg : ∀ (g : G) (a : W), π (g • a) = π a) (hfree : ∀ (g : G) (a : W), g • a = a → g = 1)
    {V : Set W} (hVi : InjOn π V) {g g' : G} {a b : W} (ha : g⁻¹ • a ∈ V) (hb : g'⁻¹ • b ∈ V)
    (hba : FlatQuotient.proj Γ W b = FlatQuotient.proj Γ W a) :
    sheet Γ V g = sheet Γ V g' := by
  obtain ⟨γ, hγ⟩ := FlatQuotient.proj_eq_proj_iff.1 hba
  have hab : g'⁻¹ • b = g⁻¹ • a := by
    refine hVi hb ha ?_
    rw [hπg, hπg, ← hγ, smul_coe_eq hle, hπg]
  have hfix : (g'⁻¹ * ⟨γ, hle γ.2⟩ * g : G) • (g⁻¹ • a) = g⁻¹ • a := by
    rw [mul_smul, mul_smul, smul_inv_smul, ← smul_coe_eq hle, hγ, hab]
  have hg' : g' = ⟨γ, hle γ.2⟩ * g := by
    have := hfree _ _ hfix
    rwa [mul_assoc, inv_mul_eq_one] at this
  rw [hg', sheet_mul hle]

end Sheets

/-- **An intermediate quotient covers.** If `π : W → Y` is continuous, open, onto, locally
injective, with fibres the orbits of a group `G` acting freely on `W`, then for `Γ ≤ G` the
induced `p : Γ\W → Y` is a covering map: over `U = π(V)`, `V` a neighbourhood on which `π` is
injective, the sheets are the sets `[g V]`, `g ∈ G`, two of which are equal or disjoint
(freeness, `sheet_eq_of_meet`), each mapped bijectively onto `U`. -/
private theorem isCoveringMap_of_factor {Γ G : Subgroup (isom d)} (hle : Γ ≤ G)
    {W : Opens (Minkowski d)} [FlatQuotient.Invariant Γ W] [FlatQuotient.Invariant G W]
    {Y : Type*} [TopologicalSpace Y] {π : W → Y} (hπc : Continuous π) (hπo : IsOpenMap π)
    (hπs : Surjective π) (hfib : ∀ a b : W, π a = π b ↔ ∃ g : G, g • a = b)
    (hfree : ∀ (g : G) (a : W), g • a = a → g = 1)
    (hloc : ∀ w : W, ∃ V : Set W, IsOpen V ∧ w ∈ V ∧ InjOn π V)
    {p : FlatQuotient Γ W → Y} (hp : ∀ a, p (FlatQuotient.proj Γ W a) = π a) :
    IsCoveringMap p := by
  have hπg : ∀ (g : G) (a : W), π (g • a) = π a := fun g a => ((hfib a (g • a)).2 ⟨g, rfl⟩).symm
  have hpπ : p ∘ FlatQuotient.proj Γ W = π := funext hp
  have hpc : Continuous p :=
    ((FlatQuotient.isOpenMap_proj Γ W).isQuotientMap (FlatQuotient.continuous_proj Γ W)
      (FlatQuotient.proj_surjective Γ W)).continuous_iff.2 (hpπ ▸ hπc)
  have hpo : IsOpenMap p := by
    intro O hO
    have : p '' O = π '' (FlatQuotient.proj Γ W ⁻¹' O) := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        obtain ⟨a, rfl⟩ := FlatQuotient.proj_surjective Γ W x
        exact ⟨a, hx, (hp a).symm⟩
      · rintro ⟨a, ha, rfl⟩
        exact ⟨_, ha, hp a⟩
    rw [this]
    exact hπo _ (hO.preimage (FlatQuotient.continuous_proj Γ W))
  intro y
  obtain ⟨w, rfl⟩ := hπs y
  obtain ⟨V, hVo, hwV, hVi⟩ := hloc w
  refine isEvenlyCovered_of_sheets hpc hpo (hπo V hVo) ⟨w, hwV, rfl⟩
    (ι := {T : Set (FlatQuotient Γ W) // ∃ g : G, T = sheet Γ V g}) (fun T => T.1)
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨_, g, rfl⟩
    exact FlatQuotient.isOpenMap_proj Γ W _ (hVo.preimage (continuous_const_smul _))
  · rintro ⟨_, g, rfl⟩ _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab
    simp only [hp] at hab
    have h1 : g⁻¹ • a = g⁻¹ • b := hVi ha hb (by rw [hπg, hπg, hab])
    rw [smul_left_cancel_iff] at h1
    rw [h1]
  · rintro ⟨_, g, rfl⟩ _ ⟨v, hv, rfl⟩
    refine ⟨FlatQuotient.proj Γ W (g • v), ⟨g • v, ?_, rfl⟩, ?_⟩
    · show g⁻¹ • g • v ∈ V
      rw [inv_smul_smul]
      exact hv
    · rw [hp, hπg]
  · rintro ⟨_, g, rfl⟩ ⟨_, g', rfl⟩ hne
    rw [Function.onFun, disjoint_left]
    rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, hba⟩
    exact hne (Subtype.ext (sheet_eq_of_meet hle hπg hfree hVi ha hb hba))
  · intro x hx
    obtain ⟨b, hbx⟩ := FlatQuotient.proj_surjective Γ W x
    obtain ⟨v, hv, hvb⟩ := hx
    rw [← hbx, hp] at hvb
    rw [← hbx]
    obtain ⟨g, hg⟩ := (hfib v b).1 hvb
    refine mem_iUnion.2 ⟨⟨sheet Γ V g, g, rfl⟩, b, ?_, rfl⟩
    show g⁻¹ • b ∈ V
    rw [← hg, inv_smul_smul]
    exact hv

/-! ### The finite cover -/

/-- **The finite cover `M' = Γ\𝒟(M̃)` of `M`** (l.3484–3492, Rem `remplacefini` l.2403, R1's
"up to finite coverings", DEC-43). For a developing pair `(𝒟, ρ)` with `𝒟` injective and
`Γ ≤ ρ(Deck)` of finite index: `W = 𝒟(M̃)` is open (`𝒟` is a local homeomorphism) and simply
connected (homeomorphic to `M̃` through `𝒟`); `ρ(Deck)` preserves `W` and acts on it freely and
properly discontinuously (transport of the deck action along `𝒟`, equivariance, and
`finite_deck_of_isCompact`), so `M' = Γ\W` is a flat spacetime with `IsQuotientOf M' Γ W`; the map
`p [w] = proj (𝒟⁻¹ w)` is well defined (`Γ ≤ ρ(Deck)`), a local isometry (it descends the local
isometry `proj ∘ 𝒟⁻¹`), a covering (`isCoveringMap_of_factor`) and has finite fibres (each is
covered by the image of the finite coset space `ρ(Deck) ⧸ Γ`). The hypotheses `hΩ`, `hB` are not
used (module SCOPE). -/
theorem exists_finiteCover_quotient_range (M : FlatSpacetime.{u} d) {x₀ : M}
    {D : UniversalCover M x₀ → Minkowski d} {ρ : Deck (UniversalCover.proj M x₀) →* isom d}
    (hpair : IsDevelopingPair x₀ D ρ) (hinj : Injective D) {Γ : Subgroup (isom d)}
    (hle : Γ ≤ ρ.range) (hidx : Γ.relIndex ρ.range ≠ 0) {Ω : Opens (Minkowski d)}
    (hΩ : range D ⊆ Ω) {B : FlatSpacetime.{0} d} (hB : IsQuotientOf B Γ Ω) :
    ∃ W : Opens (Minkowski d), (W : Set (Minkowski d)) = range D ∧ SimplyConnectedSpace W ∧
      ∃ (M' : FlatSpacetime.{0} d) (p : M' → M), IsFiniteCover d p ∧ IsQuotientOf M' Γ W := by
  -- `Ω` and `B` (the consumer's interface) are not needed: the action on `W` is the deck action
  have _ := hΩ
  have _ := hB
  letI := flatCoverChartedSpace d M x₀
  haveI := locPathConnectedSpace_of_flat d M
  have hsl := semilocallySimplyConnected_of_flat d M
  have hcov := isCoveringMap_flatCover_proj d M x₀
  have hloc : IsLocalIsometry d D := isLocalIsometry_iff_eventually.2 ⟨hpair.gx.1, hpair.gx.2⟩
  have hemb : IsOpenEmbedding D := hloc.isLocalHomeomorph.isOpenEmbedding_of_injective hinj
  set W : Opens (Minkowski d) := ⟨range D, hemb.isOpen_range⟩ with hWdef
  let Dw : UniversalCover M x₀ ≃ₜ W := hemb.isEmbedding.toHomeomorph
  have hDw : ∀ z, (Dw z : Minkowski d) = D z := fun _ => rfl
  refine ⟨W, rfl, ?_, ?_⟩
  · haveI := UniversalCover.simplyConnectedSpace (y₀ := x₀) hsl
    exact Dw.symm.toHomotopyEquiv.simplyConnectedSpace
  -- the deck action is free, so `ρ` is injective
  have hfreeD : ∀ (δ : Deck (UniversalCover.proj M x₀)) (z : UniversalCover M x₀),
      D (δ.1 z) = D z → δ = 1 := fun δ _ h => deck_eq_one_of_apply_eq d δ (hinj h)
  set G : Subgroup (isom d) := ρ.range with hGdef
  haveI hGinv : FlatQuotient.Invariant G W := ⟨by
    rintro ⟨_, δ, rfl⟩ _ ⟨z, rfl⟩
    exact ⟨δ.1 z, hpair.equiv δ z⟩⟩
  haveI hΓinv : FlatQuotient.Invariant Γ W := ⟨fun γ q hq => hGinv.smul_mem ⟨γ, hle γ.2⟩ q hq⟩
  -- the action of `ρ δ` on `W` is `δ` on `M̃`
  have hDwδ : ∀ (δ : Deck (UniversalCover.proj M x₀)) (a : W),
      Dw.symm ((⟨ρ δ, δ, rfl⟩ : G) • a) = δ.1 (Dw.symm a) := by
    intro δ a
    rw [Homeomorph.symm_apply_eq]
    apply Subtype.ext
    rw [hDw, hpair.equiv, ← hDw, Homeomorph.apply_symm_apply]
    rfl
  have hfreeG : ∀ (g : G) (a : W), g • a = a → g = 1 := by
    rintro ⟨_, δ, rfl⟩ a h
    have h1 := hDwδ δ a
    rw [h] at h1
    obtain rfl := deck_eq_one_of_apply_eq d δ h1.symm
    exact Subtype.ext (map_one ρ)
  have hcancel : IsCancelSMul Γ W := by
    rw [isCancelSMul_iff_eq_one_of_smul_eq]
    intro γ a h
    have := congrArg Subtype.val (hfreeG ⟨γ, hle γ.2⟩ a h)
    exact Subtype.ext this
  have hproper : ProperlyDiscontinuousSMul Γ W := by
    refine ⟨fun {K L} hK hL => ?_⟩
    have hK' : IsCompact (Dw.symm '' (K ∪ L)) := (hK.union hL).image Dw.symm.continuous
    have hF := finite_deck_of_isCompact hcov hK'
    refine ((hF.image ρ).preimage Subtype.val_injective.injOn).subset ?_
    rintro γ ⟨_, ⟨k, hk, rfl⟩, hkL⟩
    obtain ⟨δ, hδ⟩ := hle γ.2
    refine ⟨δ, ⟨Dw.symm (γ • k), ⟨Dw.symm k, ⟨k, Or.inl hk, rfl⟩, ?_⟩,
      ⟨γ • k, Or.inr hkL, rfl⟩⟩, hδ⟩
    rw [smul_coe_eq hle, show (⟨γ, hle γ.2⟩ : G) = ⟨ρ δ, δ, rfl⟩ from Subtype.ext hδ.symm, hDwδ]
  have hconn : IsConnected (W : Set (Minkowski d)) := isConnected_range hpair.gx.1
  -- the map `π = proj ∘ 𝒟⁻¹ : W → M` and its fibres
  set π : W → M := UniversalCover.proj M x₀ ∘ Dw.symm with hπdef
  have hπG : ∀ (g : G) (a : W), π (g • a) = π a := by
    rintro ⟨_, δ, rfl⟩ a
    simp only [hπdef, comp_apply, hDwδ]
    exact congrFun δ.2 _
  have hfib : ∀ a b : W, π a = π b ↔ ∃ g : G, g • a = b := by
    intro a b
    constructor
    · intro h
      obtain ⟨δ, hδ⟩ := exists_deck_apply_eq' (Dw.symm a) (Dw.symm b) h
      refine ⟨⟨ρ δ, δ, rfl⟩, Dw.symm.injective ?_⟩
      rw [hDwδ, hδ]
    · rintro ⟨g, rfl⟩
      exact (hπG g a).symm
  haveI : PathConnectedSpace M := pathConnectedSpace_iff_connectedSpace.2 inferInstance
  have hπs : Surjective π := UniversalCover.proj_surjective.comp Dw.symm.surjective
  have hπc : Continuous π := hcov.continuous.comp Dw.symm.continuous
  have hπo : IsOpenMap π := hcov.isOpenMap.comp Dw.symm.isOpenMap
  have hπinj : ∀ w : W, ∃ V : Set W, IsOpen V ∧ w ∈ V ∧ InjOn π V := by
    intro w
    obtain ⟨e, he, hee⟩ := hcov.isLocalHomeomorph (Dw.symm w)
    refine ⟨Dw.symm ⁻¹' e.source, e.open_source.preimage Dw.symm.continuous, he, ?_⟩
    intro a ha b hb hab
    have : e (Dw.symm a) = e (Dw.symm b) := by rw [← hee]; exact hab
    exact Dw.symm.injective (e.injOn ha hb this)
  -- the map `p : Γ\W → M`
  have hrel : ∀ a b : W, (MulAction.orbitRel Γ W) a b → π a = π b := by
    intro a b hab
    obtain ⟨γ, hγ⟩ := MulAction.mem_orbit_iff.1 (MulAction.orbitRel_apply.1 hab)
    rw [← hγ, smul_coe_eq hle, hπG]
  let p : FlatQuotient Γ W → M := Quotient.lift π hrel
  have hp : ∀ a, p (FlatQuotient.proj Γ W a) = π a := fun _ => rfl
  have hpcov : IsCoveringMap p := isCoveringMap_of_factor hle hπc hπo hπs hfib hfreeG hπinj hp
  -- `p` is a local isometry: it descends `π = proj ∘ 𝒟⁻¹`
  have hπloc : IsLocalIsometry d π := by
    have hDwl : IsLocalIsometry d (Dw : UniversalCover M x₀ → W) :=
      isLocalIsometry_of_comp_left (isIsometricEmbedding_subtype_val W)
        (show IsLocalIsometry d (Subtype.val ∘ Dw) from hloc)
    have hDwsl : IsLocalIsometry d (Dw.symm : W → UniversalCover M x₀) :=
      isLocalIsometry_of_comp_right hDwl Dw.surjective (by
        rw [show (Dw.symm ∘ Dw : UniversalCover M x₀ → UniversalCover M x₀) = id from
          funext Dw.symm_apply_apply]
        exact isLocalIsometry_id)
    exact (isLocalIsometry_flatCover_proj x₀).comp hDwsl
  have hplocal : IsLocalIsometry d p :=
    isLocalIsometry_of_comp_right (FlatQuotient.isLocalIsometry_proj Γ W)
      (FlatQuotient.proj_surjective Γ W) hπloc
  -- the fibres of `p` are covered by the image of the finite `ρ(Deck) ⧸ Γ`
  have hfin : ∀ y : M, (p ⁻¹' {y}).Finite := by
    intro y
    obtain ⟨w₀, rfl⟩ := hπs y
    haveI : (Γ.subgroupOf G).FiniteIndex := ⟨hidx⟩
    refine (Set.finite_range fun q : G ⧸ Γ.subgroupOf G =>
      FlatQuotient.proj Γ W (q.out⁻¹ • w₀)).subset ?_
    intro x hx
    obtain ⟨a, rfl⟩ := FlatQuotient.proj_surjective Γ W x
    have hx' : π a = π w₀ := hx
    obtain ⟨g, hg⟩ := (hfib w₀ a).1 hx'.symm
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (Γ.subgroupOf G) g⁻¹
    refine ⟨(g⁻¹ : G), ?_⟩
    show FlatQuotient.proj Γ W ((QuotientGroup.mk (s := Γ.subgroupOf G) g⁻¹).out⁻¹ • w₀) =
      FlatQuotient.proj Γ W a
    rw [hh, mul_inv_rev, inv_inv, ← hg, FlatQuotient.proj_eq_proj_iff']
    refine ⟨((h : G) : isom d), Subgroup.mem_subgroupOf.1 h.2, ?_⟩
    simp only [FlatQuotient.coe_smul, mul_smul, Subgroup.coe_inv, smul_inv_smul]
  exact ⟨FlatQuotient.toFlatSpacetime Γ W hconn, p, ⟨hpcov, hplocal, hfin⟩,
    FlatQuotient.isQuotientOf_toFlatSpacetime Γ W hconn⟩

end Causal.Flat.Cla
