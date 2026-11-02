import CausalScaffold.Flat.Loxodromic
import CausalScaffold.Flat.Cla.G9PairLin

/-!
# `CausalScaffold.Flat.Cla.G9Pair` — a Cauchy-compact central extension has no finite-index subgroup fixing an invariant pair of `𝒮`

T. Barbot, *Globally hyperbolic flat space-times* (`papers/barbot`, arXiv math/0402257), proof of
Theorem B (`bthm:cauclo`, l.353–359; proof l.3536–3548), the residual pair case of gap G9d (NE)
(`docs/BARBOT-THEOREMS.md` §6; `Flat/Cla/G9.lean`, `false_of_cauchyCompact_of_fixed_pair`). **No
label is certified here** (`bthm:cauclo` is assembled in `Flat/Classification.lean`). Line numbers
are those of the **labelled** `papers/barbot/legacy/labeled/GHFspace.tex`. Barbot's `𝐌ⁿ` has total
dimension `n`; the library's `Minkowski d` has `d` spatial dimensions, so `n = d + 1`.

> It follows that nontrivial linear twisted products
> destroy Cauchy-compactness, thus the ``up to linear twisted
> products'' appearing in Theorem \ref{caucomp} can be erased
> in the Cauchy-compact version \ref{cauclo}. (l.3542–3545)

> In other words, there is another  isotropic direction $\Delta_{1}$
> preserved by the entire group $L(\Gamma)$. (l.3298–3299)

## What is proved (no `sorry`)

* `false_of_cauchyCompact_of_fixed_pair_of_scale` — **the pair case of G9d (NE)**: for a GH
  Cauchy-compact central extension `B = Γ\Ω^±(Λ(Γ))` (family (b), `IsCHCentralExtensionOf`), no
  finite-index `N ≤ Γ` fixes (in `L`) two distinct points `u₁ ≠ u₂` of `𝒮` whose pair `L(Γ)`
  preserves, as soon as some element of `N` has boost parameter `c ≠ 1` on `n₁ = (1, u₁)` (which
  `Flat/Cla/G9.lean` derives from "no global fixed point"). The proof:
  1. **(discreteness)** the boost parameters `log c` of `N` form `ℤ a₀`, and `Γ` is a finite union
     `⋃ H g`, `H = ⟨γ₀, translations of Γ⟩` (`exists_pow_mul_translation_mul`, `G9PairLin`);
  2. **(the limit set)** `Λ(Γ) ⊆ {u₁, u₂} × ℝ` (`fst_mem_pair_of_mem_limitSetJ`: a repulsive point of
     a loxodromic `γ` is one of `γᵏ ∈ N`, whose only null eigenlines are `n₁, n₂`), so `Ω` is
     invariant under `P^⊥ = n₁^⊥ ∩ n₂^⊥`;
  3. **(the swap)** some `σ ∈ Γ` exchanges `u₁, u₂` (no global fixed point); it cannot fix `P^⊥`
     pointwise (`false_of_swap_fix_perp`: determinant `−1`), so `f = L(σ)v − v ≠ 0` for some
     `v ∈ P^⊥`, with `f ∈ P^⊥` orthogonal to `E` (`L(σ)` fixes `E`) — this is Barbot's
     `E ≠ P^⊥`;
  4. **(the obstruction)** `bddAbove_image_of_cauchyCompact`: a function continuous on `Ω`,
     `H`-invariant and constant along the null `n₁` is bounded on `Ω` (every `n₁`-line meets the
     lifted compact Cauchy surface, which is `Γ C = ⋃ H g C` for a compact `C`). Two functions
     contradict it: if `L(γ₀) f ≠ f`, the displacement `minkQ(π_{P^⊥}(γ₀ p − p))`, unbounded along
     `p + s f`; if `L(γ₀) f = f`, the mixed coordinate
     `a₀ ⟨f | p⟩ − ⟨f | τ₀⟩ log |⟨n₁ | p⟩ − s₁|` (`s₁` the `γ₀`-invariant level of `n₁`, off `Ω`
     since `(u₁, s₁) ∈ Λ(Γ)`), affine of nonzero slope along `p + s f`.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `M` Cauchy-compact GH (Theorem B) | ✓ carried (`hGH`, `hC`) |
| `M` of family (b), `L(Γ)` discrete without global fixed point (Def 4.18, l.1212–1214) | ✓ carried (`hB : IsCHCentralExtensionOf B Γ`) |
| `N` of finite index fixing the pair, `L(Γ)` preserving it (the elementary case, l.3298–3299) | ✓ carried (`hle`, `hidx`, `hfix`, `hpair`) |
| some element of `N` loxodromic | ⚠ strengthened: carried as `hne1` (`c ≠ 1`); `Flat/Cla/G9.lean` discharges it from no global fixed point |
| `M` maximal | ⚠ weakened: not assumed |

## SCOPE (disclosed)

The contradiction is the cocompactness obstruction of `Flat/Cla/G9.lean`'s
`isCompact_image_of_isQuotientOf`, generalised to functions continuous on `Ω` only and invariant
under a subgroup `H` with `Γ = ⋃_{g ∈ T} H g`, `T` finite. Barbot's own route (`L(Γ)` cocompact on
a totally geodesic `𝐇ᵏ`, `k ≥ 2`) and the cohomological-dimension count (`Γ` virtually
`ℤ^{1 + dim E}`, `dim E ≤ d − 2`) are not used.

`false_of_cauchyCompact_of_fixed_pair_of_scale` is one long assembly and is elaborated under
`set_option maxHeartbeats 1000000` (as `Flat/Nonlox/UnipotentLTP.lean`'s main theorem).

**What the hypothesis buys: impossible in family (b), not in general.** The pair-with-swap
configuration is excluded here **because `B` is of family (b)**: centrality (`L(γ)|_E = id` for
every `γ ∈ Γ`, `hEcen`) makes the swap `σ` fix `E` pointwise, which together with
`false_of_swap_fix_perp` forces `E ≠ P^⊥` and yields the obstruction `f ⊥ E` (`hfE`). Outside
family (b) the configuration **does** occur among Cauchy-compact GH spacetimes, as finite quotients
of Misner spacetimes. Example, `d = 3`, coordinates `(x, z₁, z₂, y)`, `q = 2xy + z₁² + z₂²`,
`Ω = {x > 0, y < 0} × ℝ²`: `Γ' = {(x, z, y) ↦ (eᵏ x, z + w, e⁻ᵏ y) : k ∈ ℤ, w ∈ 2u₁ℤ ⊕ ℤ}`
(`u₁ ≠ 0`) and `σ(x, z₁, z₂, y) = (−y, z₁ + u₁, −z₂, −x)` (determinant `+1`, time-orientation and
`Ω` preserved, `σ² ∈ Γ'`, `σΓ'σ⁻¹ = Γ'`). `Γ = ⟨Γ', σ⟩` acts freely (the `z₁`-coordinate of every
`σg` moves by `u₁ + 2u₁ℤ ∌ 0`) and properly, the Cauchy surface `({xy = −1} × ℝ²)/Γ` is compact,
`L(Γ) = ⟨boost, swap⟩` is discrete without global fixed point and `Λ(Γ)` lies over the pair; it is
not of family (b) because there `E = P^⊥` and `L(σ)|_E = diag(1, −1) ≠ id`. Barbot covers it:
[10.M] opens "Here, we consider the case where, up to finite index, `L(Γ)` preserves some
isotropic direction `Δ₀`" (l.3237–3239), which reaches the swap through the index-2 subgroup, and
Theorem B is stated "Up to finite coverings" (l.355). **No defect in the paper.** Example of what
*is* excluded (inside family (b)), `d = 2`: `Γ = ⟨γ₀, σ⟩` with `γ₀` a boost along `x` composed with
the translation `∂_y`, `σ` the half-turn `(t, x, y) ↦ (t, −x, −y)`; `σγ₀σ⁻¹ = γ₀⁻¹`, `E = 0`, and
the Cauchy surface of `Γ\Ω` is a quotient of the cylinder `ℝ²/⟨(a, 1)⟩` by an involution, not
compact; here `f = −2∂_y` is fixed by `L(γ₀)` and the mixed coordinate
`a₀⟨f|·⟩ − ⟨f|∂_y⟩ log|⟨n₁|·⟩ − s₁|` sees it.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal.Flat.Cla

open Set Function Filter Topology TopologicalSpace Causal Causal.Flat

universe u

variable {d : ℕ}

section PairObstruction

/-- **The obstruction to Cauchy-compactness, up to finitely many cosets** (the common core of
l.3542–3543 and l.744–746, as `Flat/Cla/G9.lean`'s `isCompact_image_of_isQuotientOf`): let
`M = Γ\Ω` be causal and Cauchy-compact, `Γ = ⋃_{g ∈ T} H g` with `T ⊆ Γ` finite, and `F`
continuous on `Ω`, `H`-invariant on `Ω` and constant along a nonzero future causal direction `v`.
Then `F` is bounded above on `Ω`: every `v`-line through `Ω` meets the lift of the compact Cauchy
surface `K`, which lies in `Γ C` for a compact `C ⊆ Ω`, and `F(Γ C) = F(⋃_{g ∈ T} g C)`. -/
theorem bddAbove_image_of_cauchyCompact {B : FlatSpacetime.{u} d}
    (hcaus : (flatCausality d B).IsCausal) (hC : CauchyCompact B) {Γ : Subgroup (isom d)}
    {Ω : Opens (Minkowski d)} (hq : IsQuotientOf B Γ Ω) {H : Subgroup (isom d)}
    {T : Set (isom d)} (hT : T.Finite) (hTΓ : T ⊆ Γ)
    (hdec : ∀ γ ∈ Γ, ∃ h ∈ H, ∃ g ∈ T, γ = h * g) {F : Minkowski d → ℝ}
    (hF : ContinuousOn F (Ω : Set (Minkowski d)))
    (hinv : ∀ h ∈ H, ∀ p ∈ (Ω : Set (Minkowski d)), F (h • p) = F p) {v : Minkowski d}
    (hv : IsFutureCausal v) (hv0 : v ≠ 0) (hline : ∀ (p : Minkowski d) (s : ℝ), F (p + s • v) = F p) :
    BddAbove (F '' (Ω : Set (Minkowski d))) := by
  obtain ⟨K, hK, hKc, -⟩ := hC
  obtain ⟨π, hcov, hloc, hsurj, hfib⟩ := hq.quot
  have hΓΩ : ∀ γ ∈ Γ, ∀ p ∈ (Ω : Set (Minkowski d)), γ • p ∈ (Ω : Set (Minkowski d)) :=
    fun γ hγ p hp => by rw [← hq.inv γ hγ]; exact ⟨p, hp, rfl⟩
  -- a compact `C ⊆ Ω` whose image covers `K`
  have hnhds : ∀ e : Ω, ∃ C : Set Ω, IsCompact C ∧ C ∈ 𝓝 e := fun e => exists_compact_mem_nhds e
  choose Cf hCf hCn using hnhds
  obtain ⟨t, ht⟩ := hKc.elim_finite_subcover (fun e : Ω => π '' interior (Cf e))
    (fun e => hloc.isOpenMap _ isOpen_interior) (fun s _ => by
      obtain ⟨e, rfl⟩ := hsurj s
      exact mem_iUnion.2 ⟨e, e, mem_interior_iff_mem_nhds.2 (hCn e), rfl⟩)
  have hCc : IsCompact (⋃ e ∈ t, Cf e) := t.isCompact_biUnion fun e _ => hCf e
  have hSC' : ∀ s ∈ K, ∃ c ∈ ⋃ e ∈ t, Cf e, π c = s := by
    intro s hs
    obtain ⟨e, he, c, hc, rfl⟩ := mem_iUnion₂.1 (ht hs)
    exact ⟨c, mem_biUnion he (interior_subset hc), rfl⟩
  -- its finitely many translates, a compact subset of `Ω`
  set Kc : Set (Minkowski d) := ⋃ g ∈ T, (fun p => g • p) '' (Subtype.val '' ⋃ e ∈ t, Cf e)
  have hKc' : IsCompact Kc :=
    hT.isCompact_biUnion fun g _ => (hCc.image continuous_subtype_val).image (continuous_const_smul g)
  have hKcΩ : Kc ⊆ (Ω : Set (Minkowski d)) := by
    intro x hx
    obtain ⟨g, hg, c, ⟨c', -, rfl⟩, rfl⟩ := mem_iUnion₂.1 hx
    exact hΓΩ g (hTΓ hg) _ c'.2
  refine (hKc'.image_of_continuousOn (hF.mono hKcΩ)).bddAbove.mono ?_
  -- the lifted Cauchy surface, read in `𝐌ⁿ`
  have hpre := isCauchySurface_preimage hcov hloc hcaus hK
  have hSΩ : Subtype.val '' (π ⁻¹' K) ⊆ (Ω : Set (Minkowski d)) := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hSC : (minkowski d).IsCauchySurfaceOn Ω (Subtype.val '' (π ⁻¹' K)) := by
    rw [FlatQuotient.isCauchySurfaceOn_iff Ω hSΩ, preimage_image_eq _ Subtype.val_injective]
    exact hpre
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨s, x, hxK, hx⟩ := exists_mem_line_of_isCauchySurfaceOn hSC hz hv hv0
  obtain ⟨c, hcC, hcx⟩ := hSC' (π x) hxK
  obtain ⟨γ, hγ, hγc⟩ := (hfib c x).1 hcx
  obtain ⟨h, hh, g, hg, rfl⟩ := hdec γ hγ
  have hgc : g • (c : Minkowski d) ∈ (Ω : Set (Minkowski d)) := hΓΩ g (hTΓ hg) _ c.2
  refine ⟨g • (c : Minkowski d), mem_biUnion hg ⟨c, ⟨c, hcC, rfl⟩, rfl⟩, ?_⟩
  rw [← hinv h hh _ hgc, ← mul_smul, hγc, hx, hline]

/-- **Invariance passes to the generated subgroup**: if `Γ` preserves `Ω` and `F` is invariant on
`Ω` under a generating set `S ⊆ Γ`, it is invariant on `Ω` under `closure S`. -/
theorem invariant_closure_of_subset {Γ : Subgroup (isom d)} {Ω : Set (Minkowski d)}
    (hΩ : ∀ γ ∈ Γ, ∀ p ∈ Ω, γ • p ∈ Ω) {S : Set (isom d)} (hS : S ⊆ Γ) {F : Minkowski d → ℝ}
    (hF : ∀ s ∈ S, ∀ p ∈ Ω, F (s • p) = F p) :
    ∀ h ∈ Subgroup.closure S, ∀ p ∈ Ω, F (h • p) = F p := by
  intro h hh
  suffices h ∈ Γ ∧ ∀ p ∈ Ω, F (h • p) = F p from this.2
  induction hh using Subgroup.closure_induction with
  | mem x hx => exact ⟨hS hx, hF x hx⟩
  | one => exact ⟨Γ.one_mem, fun p _ => by rw [one_smul]⟩
  | mul x y _ _ hx hy =>
    exact ⟨Γ.mul_mem hx.1 hy.1, fun p hp => by rw [mul_smul, hx.2 _ (hΩ y hy.1 p hp), hy.2 p hp]⟩
  | inv x _ hx =>
    refine ⟨Γ.inv_mem hx.1, fun p hp => ?_⟩
    have hq := hΩ _ (Γ.inv_mem hx.1) p hp
    rw [← hx.2 _ hq, smul_inv_smul]

end PairObstruction

section PairLimit

variable {u₁ u₂ : PenroseSphere d}

/-- Two null eigenvectors `x, y` of a Lorentz map with `⟨x | y⟩ ≠ 0` have inverse eigenvalues. -/
theorem mul_eq_one_of_eigen_of_minkB_ne_zero {A : Minkowski d ≃ₗ[ℝ] Minkowski d}
    (hA : A ∈ lorentz d) {x y : Minkowski d} {a b : ℝ} (hx : A x = a • x) (hy : A y = b • y)
    (hxy : minkB x y ≠ 0) : a * b = 1 := by
  have h := lorentz.minkB_apply hA x y
  rw [hx, hy, minkB_smul_left, minkB_smul_right, ← mul_assoc] at h
  have h' : (a * b - 1) * minkB x y = 0 := by linarith
  rcases mul_eq_zero.1 h' with h'' | h''
  · linarith
  · exact absurd h'' hxy

/-- **The limit set lies over the pair** (`Λ(Γ) ⊆ {u₁, u₂} × ℝ`): if a finite-index `N ≤ Γ` fixes
`u₁ ≠ u₂ ∈ 𝒮`, a repulsive fixed point `(u, s)` of a loxodromic `γ ∈ Γ` has `u ∈ {u₁, u₂}` — it is
a repulsive point of `γᵏ ∈ N`, and three null eigenlines of one Lorentz map force all three
eigenvalues to `1`. The closure keeps the property. -/
theorem fst_mem_pair_of_mem_limitSetJ (hne : u₁ ≠ u₂) {Γ N : Subgroup (isom d)}
    (hidx : N.relIndex Γ ≠ 0)
    (hfix : ∀ γ ∈ N, lorentzSphere (linearPart γ) u₁ = u₁ ∧ lorentzSphere (linearPart γ) u₂ = u₂) :
    ∀ w ∈ limitSetJ Γ, w.1 = u₁ ∨ w.1 = u₂ := by
  have hcl : IsClosed {w : PenroseSphere d × ℝ | w.1 = u₁ ∨ w.1 = u₂} :=
    (isClosed_singleton.preimage continuous_fst).union (isClosed_singleton.preimage continuous_fst)
  refine fun w hw => closure_minimal (fun w hw => ?_) hcl hw
  obtain ⟨γ, hγ, -, l, hl0, hl1, heig, -⟩ := hw
  obtain ⟨k, hk, -, hkmem⟩ := Subgroup.exists_pow_mem_of_relIndex_ne_zero hidx hγ
  obtain ⟨h1, h2⟩ := hfix _ hkmem.1
  obtain ⟨e₁, e₂⟩ := pairScale_eigen hne h1 h2
  set c := lorentzScale (linearPart (γ ^ k)) u₁
  have hc : 0 < c := lorentzScale_pos _ _
  have hA : ((linearPart (γ ^ k) : lorentz d) : Minkowski d ≃ₗ[ℝ] Minkowski d) = linOf γ ^ k := by
    rw [← linOf_eq_linearPart, linOf_pow]
  have hpow : ∀ m : ℕ, (linOf γ ^ m) (nullVec w.1) = l ^ m • nullVec w.1 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ, LinearEquiv.mul_apply, heig, map_smul, ih, smul_smul, pow_succ, mul_comm]
  by_contra hcon
  simp only [mem_setOf_eq, not_or] at hcon
  have hmem : (linOf γ ^ k) ∈ lorentz d := by rw [← hA]; exact (linearPart (γ ^ k)).2
  rw [hA] at e₁ e₂
  have p1 := mul_eq_one_of_eigen_of_minkB_ne_zero hmem (hpow k) e₁
    (minkB_nullVec_ne_zero_of_ne hcon.1)
  have p2 := mul_eq_one_of_eigen_of_minkB_ne_zero hmem (hpow k) e₂
    (minkB_nullVec_ne_zero_of_ne hcon.2)
  have hlk : l ^ k < 1 := pow_lt_one₀ hl0.le hl1 hk.ne'
  have hlk0 : 0 < l ^ k := pow_pos hl0 k
  have hcc : c = c⁻¹ := by
    have := p1.trans p2.symm
    exact mul_left_cancel₀ hlk0.ne' this
  have hc1 : c = 1 := by
    have h := mul_inv_cancel₀ hc.ne'
    rw [← hcc] at h
    nlinarith
  rw [hc1, mul_one] at p1
  linarith

/-- **`Ω^±(Λ)` is invariant under `P^⊥`** when `Λ` lies over `{u₁, u₂}`. -/
theorem add_mem_omegaPlus_of_perp {Λ : Set (PenroseSphere d × ℝ)}
    (hΛ : ∀ w ∈ Λ, w.1 = u₁ ∨ w.1 = u₂) {p e : Minkowski d} (hp : p ∈ omegaPlus Λ)
    (h1 : minkB e (nullVec u₁) = 0) (h2 : minkB e (nullVec u₂) = 0) : p + e ∈ omegaPlus Λ := by
  rw [mem_omegaPlus] at hp ⊢
  intro w hw
  have he : minkB (nullVec w.1) e = 0 := by
    rcases hΛ w hw with h | h <;> rw [h, minkB_comm] <;> assumption
  rw [minkB_add_right, he, add_zero]
  exact hp w hw

theorem add_mem_omegaMinus_of_perp {Λ : Set (PenroseSphere d × ℝ)}
    (hΛ : ∀ w ∈ Λ, w.1 = u₁ ∨ w.1 = u₂) {p e : Minkowski d} (hp : p ∈ omegaMinus Λ)
    (h1 : minkB e (nullVec u₁) = 0) (h2 : minkB e (nullVec u₂) = 0) : p + e ∈ omegaMinus Λ := by
  rw [mem_omegaMinus] at hp ⊢
  intro w hw
  have he : minkB (nullVec w.1) e = 0 := by
    rcases hΛ w hw with h | h <;> rw [h, minkB_comm] <;> assumption
  rw [minkB_add_right, he, add_zero]
  exact hp w hw

/-- The action of a Lorentz map on `𝒮` is injective. -/
theorem lorentzSphere_injective (A : lorentz d) : Injective (lorentzSphere A) := by
  intro u u' h
  have e := nullVec_lorentzSphere A u
  have e' := nullVec_lorentzSphere A u'
  rw [h] at e
  have hc := (lorentzScale_pos A u).ne'
  have hc' := (lorentzScale_pos A u').ne'
  refine nullVec_injective_smul (c := lorentzScale A u * (lorentzScale A u')⁻¹) ?_
  apply (A : Minkowski d ≃ₗ[ℝ] Minkowski d).injective
  rw [map_smul]
  have h1 : (A : Minkowski d ≃ₗ[ℝ] Minkowski d) (nullVec u) =
      lorentzScale A u • nullVec (lorentzSphere A u') := by
    rw [e, smul_smul, mul_inv_cancel₀ hc, one_smul]
  have h2 : (A : Minkowski d ≃ₗ[ℝ] Minkowski d) (nullVec u') =
      lorentzScale A u' • nullVec (lorentzSphere A u') := by
    rw [e', smul_smul, mul_inv_cancel₀ hc', one_smul]
  rw [h1, h2, smul_smul, mul_assoc, inv_mul_cancel₀ hc', mul_one]

/-- The transverse part of a null frame kills the first frame vector. -/
theorem nullV_add_smul_left {u u' : Minkowski d} (hu : minkQ u = 0) (hB : minkB u u' ≠ 0)
    (z : Minkowski d) (r : ℝ) : nullV u u' (z + r • u) = nullV u u' z := by
  have hu0 : minkB u u = 0 := by rw [← minkQ_eq_minkB, hu]
  simp only [nullV, minkB_add_left, minkB_smul_left, hu0, mul_zero, add_zero]
  rw [add_div, mul_div_assoc, div_self hB, mul_one, add_smul]
  abel

/-- The transverse part of a null frame fixes the vectors orthogonal to it. -/
theorem nullV_of_orth {u u' z : Minkowski d} (h1 : minkB z u = 0) (h2 : minkB z u' = 0) :
    nullV u u' z = z := by
  simp [nullV, h1, h2]

theorem nullV_smul (u u' : Minkowski d) (r : ℝ) (z : Minkowski d) :
    nullV u u' (r • z) = r • nullV u u' z := by
  simp only [nullV, minkB_smul_left, smul_sub, smul_smul, mul_div_assoc]

theorem continuous_nullV' (u u' : Minkowski d) : Continuous (nullV u u') := by
  unfold nullV minkB; fun_prop

theorem continuous_minkB_left' (w : Minkowski d) : Continuous fun p : Minkowski d => minkB w p := by
  unfold minkB; fun_prop

/-- A point of `𝒮` sent to `u'`: `A (1, u) = c (1, u')`, `c = lorentzScale A u`. -/
theorem apply_nullVec_of_lorentzSphere_eq {A : lorentz d} {u u' : PenroseSphere d}
    (h : lorentzSphere A u = u') :
    (A : Minkowski d ≃ₗ[ℝ] Minkowski d) (nullVec u) = lorentzScale A u • nullVec u' := by
  have e := nullVec_lorentzSphere A u
  rw [h] at e
  rw [e, smul_smul, mul_inv_cancel₀ (lorentzScale_pos A u).ne', one_smul]

/-- If `A y = a x` (`a ≠ 0`) and `v ⊥ y`, then `A v ⊥ x`. -/
theorem minkB_apply_eq_zero_of_image {A : Minkowski d ≃ₗ[ℝ] Minkowski d} (hA : A ∈ lorentz d)
    {x y v : Minkowski d} {a : ℝ} (ha : a ≠ 0) (hy : A y = a • x) (hv : minkB v y = 0) :
    minkB (A v) x = 0 := by
  have hx : x = a⁻¹ • A y := by rw [hy, smul_smul, inv_mul_cancel₀ ha, one_smul]
  rw [hx, minkB_smul_right, lorentz.minkB_apply hA, hv, mul_zero]

end PairLimit

section PairMain

set_option maxHeartbeats 1000000 in
/-- **G9d (NE), the pair case** (DEC-44; l.3298–3299; l.3536–3548): for a GH Cauchy-compact
central extension `B = Γ\Ω^±(Λ(Γ))` (family (b)), no finite-index `N ≤ Γ` has linear parts fixing
two distinct points `u₁ ≠ u₂` of `𝒮` whose pair `L(Γ)` preserves, once some element of `N` has
boost parameter `c ≠ 1` (`hne1`). Module docstring for the proof: the boost `γ₀` generating the
boost parameters of `N` (discreteness), `Λ(Γ)` over the pair, the swap `σ` (not the identity on
`P^⊥`: determinant), and the bounded-image obstruction applied to the displacement of `γ₀` (if
`L(γ₀)` moves `f = L(σ)v − v`) or to the mixed coordinate `a₀⟨f|·⟩ − ⟨f|τ₀⟩ log|⟨n₁|·⟩ − s₁|`
(if it fixes `f`). -/
theorem false_of_cauchyCompact_of_fixed_pair_of_scale {B : FlatSpacetime.{u} d} (hGH : GH B)
    (hC : CauchyCompact B) {Γ : Subgroup (isom d)} (hB : IsCHCentralExtensionOf B Γ)
    {N : Subgroup (isom d)} (hle : N ≤ Γ) (hidx : N.relIndex Γ ≠ 0) {u₁ u₂ : PenroseSphere d}
    (hne : u₁ ≠ u₂)
    (hfix : ∀ γ ∈ N, lorentzSphere (linearPart γ) u₁ = u₁ ∧ lorentzSphere (linearPart γ) u₂ = u₂)
    (hpair : ∀ γ ∈ Γ, ∀ u ∈ ({u₁, u₂} : Set (PenroseSphere d)),
      lorentzSphere (linearPart γ) u ∈ ({u₁, u₂} : Set (PenroseSphere d)))
    (hne1 : ∃ γ ∈ N, lorentzScale (linearPart γ) u₁ ≠ 1) : False := by
  obtain ⟨E, -, hEspan, -, hEcen, hD, hnf, hcase⟩ := hB
  have hBn : minkB (nullVec u₁) (nullVec u₂) ≠ 0 := minkB_nullVec_ne_zero_of_ne hne
  -- `Ω`, its quotient presentation, and its side
  obtain ⟨Ω, hq, hside⟩ : ∃ Ω : Opens (Minkowski d), IsQuotientOf B Γ Ω ∧
      ((Ω : Set (Minkowski d)) = omegaPlus (limitSetJ Γ) ∨
        (Ω : Set (Minkowski d)) = omegaMinus (limitSetJ Γ)) := by
    rcases hcase with ⟨hq, -⟩ | ⟨hq, -⟩
    · exact ⟨_, hq, Or.inl rfl⟩
    · exact ⟨_, hq, Or.inr rfl⟩
  have hΛ := fst_mem_pair_of_mem_limitSetJ hne hidx hfix
  have hΩP : ∀ p ∈ (Ω : Set (Minkowski d)), ∀ e : Minkowski d, minkB e (nullVec u₁) = 0 →
      minkB e (nullVec u₂) = 0 → p + e ∈ (Ω : Set (Minkowski d)) := by
    intro p hp e h1 h2
    rcases hside with h | h <;> rw [h] at hp ⊢
    · exact add_mem_omegaPlus_of_perp hΛ hp h1 h2
    · exact add_mem_omegaMinus_of_perp hΛ hp h1 h2
  have hΩx : ∀ w ∈ limitSetJ Γ, ∀ p ∈ (Ω : Set (Minkowski d)),
      minkB (nullVec w.1) p - w.2 ≠ 0 := by
    intro w hw p hp
    rcases hside with h | h <;> rw [h] at hp
    · exact (sub_neg.2 (mem_omegaPlus.1 hp w hw)).ne
    · exact (sub_pos.2 (mem_omegaMinus.1 hp w hw)).ne'
  have hΓΩ : ∀ γ ∈ Γ, ∀ p ∈ (Ω : Set (Minkowski d)), γ • p ∈ (Ω : Set (Minkowski d)) :=
    fun γ hγ p hp => by rw [← hq.inv γ hγ]; exact ⟨p, hp, rfl⟩
  obtain ⟨p₀, hp₀⟩ : (Ω : Set (Minkowski d)).Nonempty := by
    obtain ⟨π, -, -, hπs, -⟩ := hq.quot
    obtain ⟨p, -⟩ := hπs (Classical.arbitrary B)
    exact ⟨p, p.2⟩
  -- the boost `γ₀` and the decomposition `Γ = ⋃ H g`
  obtain ⟨γ₀, hγ₀N, hc₀1, T, hT, hTΓ, hdec⟩ :=
    exists_pow_mul_translation_mul hne hD hle hidx hfix hne1
  have hγ₀Γ : γ₀ ∈ Γ := hle hγ₀N
  obtain ⟨S, hSdef⟩ : ∃ S : Set (isom d), S = insert γ₀ {τ | τ ∈ Γ ∧ linearPart τ = 1} :=
    ⟨_, rfl⟩
  have hSΓ : S ⊆ Γ := by
    rw [hSdef]; rintro x (rfl | ⟨hx, -⟩)
    · exact hγ₀Γ
    · exact hx
  have hdecH : ∀ γ ∈ Γ, ∃ h ∈ Subgroup.closure S, ∃ g ∈ T, γ = h * g := by
    intro γ hγ
    obtain ⟨k, τ, hτ, hτ1, g, hg, rfl⟩ := hdec γ hγ
    refine ⟨γ₀ ^ k * τ, Subgroup.mul_mem _ (Subgroup.zpow_mem _ (Subgroup.subset_closure ?_) _)
      (Subgroup.subset_closure ?_), g, hg, rfl⟩
    · rw [hSdef]; exact mem_insert _ _
    · rw [hSdef]; exact mem_insert_of_mem _ ⟨hτ, hτ1⟩
  -- the eigenvalues of `L(γ₀)`
  obtain ⟨c₀, hc₀def⟩ : ∃ c₀, c₀ = lorentzScale (linearPart γ₀) u₁ := ⟨_, rfl⟩
  have hc₀pos : 0 < c₀ := by rw [hc₀def]; exact lorentzScale_pos _ _
  rw [← hc₀def] at hc₀1
  obtain ⟨e₁, e₂⟩ := pairScale_eigen hne (hfix γ₀ hγ₀N).1 (hfix γ₀ hγ₀N).2
  rw [← linOf_eq_linearPart, ← hc₀def] at e₁ e₂
  -- the pure translations, along `E ⊆ P^⊥`
  have htr : ∀ τ ∈ Γ, linearPart τ = 1 → (∀ p, τ • p = p + trOf τ) ∧ trOf τ ∈ E := by
    intro τ hτ hτ1
    have hlin : linOf τ = 1 := by rw [linOf_eq_linearPart, hτ1]; rfl
    refine ⟨fun p => by rw [smul_eq_lin_add, hlin]; rfl, ?_⟩
    rw [← hEspan]
    exact Submodule.subset_span ⟨τ, hτ, hlin, rfl⟩
  have hEn : ∀ e ∈ E, ∀ (x : Minkowski d) (a : ℝ), a ≠ 1 → linOf γ₀ x = a • x →
      minkB e x = 0 := by
    intro e he x a ha hx
    have h := minkB_linOf γ₀ e x
    rw [hEcen γ₀ hγ₀Γ e he, hx, minkB_smul_right] at h
    have h' : (a - 1) * minkB e x = 0 := by linarith
    exact (mul_eq_zero.1 h').resolve_left (sub_ne_zero.2 ha)
  have hc₀inv1 : c₀⁻¹ ≠ 1 := fun h => hc₀1 (by rw [← inv_inv c₀, h, inv_one])
  have hE1 : ∀ e ∈ E, minkB e (nullVec u₁) = 0 := fun e he => hEn e he _ _ hc₀1 e₁
  -- the swap `σ`
  obtain ⟨σ, hσΓ, hσ1⟩ : ∃ σ ∈ Γ, lorentzSphere (linearPart σ) u₁ ≠ u₁ := by
    by_contra h
    push Not at h
    exact hnf (Or.inr ⟨u₁, by rintro _ ⟨γ, hγ, rfl⟩; exact h γ hγ⟩)
  have hσ12 : lorentzSphere (linearPart σ) u₁ = u₂ := by
    rcases hpair σ hσΓ u₁ (mem_insert _ _) with h | h
    · exact absurd h hσ1
    · exact h
  have hσ21 : lorentzSphere (linearPart σ) u₂ = u₁ := by
    rcases hpair σ hσΓ u₂ (mem_insert_of_mem _ rfl) with h | h
    · exact h
    · exact absurd (lorentzSphere_injective _ (h.trans hσ12.symm)) hne.symm
  have hσn₁ := apply_nullVec_of_lorentzSphere_eq hσ12
  have hσn₂ := apply_nullVec_of_lorentzSphere_eq hσ21
  rw [← linOf_eq_linearPart] at hσn₁ hσn₂
  have hα₁ := (lorentzScale_pos (linearPart σ) u₁).ne'
  have hα₂ := (lorentzScale_pos (linearPart σ) u₂).ne'
  by_cases hσP : ∀ v, minkB v (nullVec u₁) = 0 → minkB v (nullVec u₂) = 0 → linOf σ v = v
  · exact false_of_swap_fix_perp hne (linOf_mem σ) hα₁ hσn₁ hσn₂ hσP
  push Not at hσP
  obtain ⟨v, hv1, hv2, hvne⟩ := hσP
  obtain ⟨f, hfdef⟩ : ∃ f, f = linOf σ v - v := ⟨_, rfl⟩
  have hf0 : f ≠ 0 := by rw [hfdef]; exact sub_ne_zero.2 hvne
  have hf1 : minkB f (nullVec u₁) = 0 := by
    rw [hfdef, minkB_sub_left, hv1, sub_zero]
    exact minkB_apply_eq_zero_of_image (linOf_mem σ) hα₂ hσn₂ hv2
  have hf2 : minkB f (nullVec u₂) = 0 := by
    rw [hfdef, minkB_sub_left, hv2, sub_zero]
    exact minkB_apply_eq_zero_of_image (linOf_mem σ) hα₁ hσn₁ hv1
  have hfE : ∀ e ∈ E, minkB f e = 0 := by
    intro e he
    rw [hfdef, minkB_sub_left, sub_eq_zero]
    conv_lhs => rw [← hEcen σ hσΓ e he]
    rw [minkB_linOf]
  have hQf : 0 < minkQ f := by
    obtain ⟨h0, h00⟩ := minkQ_nonneg_of_orth_frame (minkQ_nullVec u₁) (minkQ_nullVec u₂) hBn
      (y := f) hf1 hf2
    exact lt_of_le_of_ne h0 fun h => hf0 (h00 h.symm)
  have hpΩ : ∀ s : ℝ, p₀ + s • f ∈ (Ω : Set (Minkowski d)) := fun s =>
    hΩP p₀ hp₀ _ (by rw [minkB_smul_left, hf1, mul_zero]) (by rw [minkB_smul_left, hf2, mul_zero])
  have hinvS : ∀ {F : Minkowski d → ℝ}, (∀ p ∈ (Ω : Set (Minkowski d)), F (γ₀ • p) = F p) →
      (∀ τ ∈ Γ, linearPart τ = 1 → ∀ p, F (τ • p) = F p) →
      ∀ h ∈ Subgroup.closure S, ∀ p ∈ (Ω : Set (Minkowski d)), F (h • p) = F p := by
    intro F hF0 hFτ
    refine invariant_closure_of_subset hΓΩ hSΓ fun x hx p hp => ?_
    rw [hSdef] at hx
    rcases hx with rfl | ⟨hτ, hτ1⟩
    · exact hF0 p hp
    · exact hFτ x hτ hτ1 p
  by_cases hL₀f : linOf γ₀ f = f
  · -- **the mixed coordinate**: `L(γ₀)` fixes `f`
    obtain ⟨s₁, hs₁⟩ : ∃ s₁ : ℝ, s₁ = minkB (nullVec u₁) (trOf γ₀) / (1 - c₀⁻¹) := ⟨_, rfl⟩
    have h1c : 1 - c₀⁻¹ ≠ 0 := sub_ne_zero.2 hc₀inv1.symm
    have hn₁L : ∀ p, minkB (nullVec u₁) (linOf γ₀ p) = c₀⁻¹ * minkB (nullVec u₁) p := by
      intro p
      have hx : nullVec u₁ = c₀⁻¹ • linOf γ₀ (nullVec u₁) := by
        rw [e₁, smul_smul, inv_mul_cancel₀ hc₀pos.ne', one_smul]
      conv_lhs => rw [hx]
      rw [minkB_smul_left, minkB_linOf]
    have hkey : ∀ p, minkB (nullVec u₁) (γ₀ • p) - s₁ =
        c₀⁻¹ * (minkB (nullVec u₁) p - s₁) := by
      intro p
      rw [smul_eq_lin_add, minkB_add_right, hn₁L, hs₁]
      field_simp
      ring
    have hs₁Λ : ((u₁, s₁) : PenroseSphere d × ℝ) ∈ limitSetJ Γ := by
      refine subset_closure ?_
      rcases lt_or_gt_of_ne hc₀1 with h | h
      · refine ⟨γ₀, hγ₀Γ, isLoxodromic_of_null_eigen (linOf_mem γ₀) (nullVec_ne_zero u₁)
          (minkQ_nullVec u₁) hc₀pos hc₀1 e₁, c₀, hc₀pos, h, e₁, hkey⟩
      · have hi : linOf γ₀⁻¹ (nullVec u₁) = c₀⁻¹ • nullVec u₁ := by
          rw [linOf_inv]
          show (linOf γ₀).symm (nullVec u₁) = _
          rw [LinearEquiv.symm_apply_eq, map_smul, e₁, smul_smul, inv_mul_cancel₀ hc₀pos.ne',
            one_smul]
        refine ⟨γ₀⁻¹, Γ.inv_mem hγ₀Γ, isLoxodromic_of_null_eigen (linOf_mem _)
          (nullVec_ne_zero u₁) (minkQ_nullVec u₁) (inv_pos.2 hc₀pos) hc₀inv1 hi, c₀⁻¹,
          inv_pos.2 hc₀pos, inv_lt_one_of_one_lt₀ h, hi, fun p => ?_⟩
        have := hkey (γ₀⁻¹ • p)
        rw [smul_inv_smul] at this
        rw [inv_inv, this, ← mul_assoc, mul_inv_cancel₀ hc₀pos.ne', one_mul]
    have hx : ∀ p ∈ (Ω : Set (Minkowski d)), minkB (nullVec u₁) p - s₁ ≠ 0 :=
      fun p hp => hΩx (u₁, s₁) hs₁Λ p hp
    obtain ⟨a₀, ha₀⟩ : ∃ a₀ : ℝ, a₀ = -Real.log c₀ := ⟨_, rfl⟩
    have ha₀0 : a₀ ≠ 0 := by
      rw [ha₀, neg_ne_zero]
      exact Real.log_ne_zero_of_pos_of_ne_one hc₀pos hc₀1
    obtain ⟨m, hm⟩ : ∃ m : ℝ, m = minkB f (trOf γ₀) := ⟨_, rfl⟩
    set F : Minkowski d → ℝ := fun p =>
      a₀ * minkB f p - m * Real.log |minkB (nullVec u₁) p - s₁| with hFdef
    have hFc : ContinuousOn F (Ω : Set (Minkowski d)) := by
      refine ((continuous_const.mul (continuous_minkB_left' f)).continuousOn).sub
        (continuousOn_const.mul (ContinuousOn.log ?_ fun p hp => abs_ne_zero.2 (hx p hp)))
      exact ((continuous_minkB_left' _).sub continuous_const).abs.continuousOn
    have hFγ₀ : ∀ p ∈ (Ω : Set (Minkowski d)), F (γ₀ • p) = F p := by
      intro p hp
      have hg : minkB f (γ₀ • p) = minkB f p + m := by
        rw [smul_eq_lin_add, minkB_add_right, hm, add_left_inj]
        conv_lhs => rw [← hL₀f]
        rw [minkB_linOf]
      have hl : Real.log |minkB (nullVec u₁) (γ₀ • p) - s₁| =
          -Real.log c₀ + Real.log |minkB (nullVec u₁) p - s₁| := by
        rw [hkey, abs_mul, abs_of_pos (inv_pos.2 hc₀pos),
          Real.log_mul (inv_pos.2 hc₀pos).ne' (abs_ne_zero.2 (hx p hp)), Real.log_inv]
      simp only [hFdef]
      rw [hg, hl, ← ha₀]
      ring
    have hFτ : ∀ τ ∈ Γ, linearPart τ = 1 → ∀ p, F (τ • p) = F p := by
      intro τ hτ hτ1 p
      obtain ⟨hτp, htE⟩ := htr τ hτ hτ1
      have h1' : minkB f (trOf τ) = 0 := hfE _ htE
      have h2' : minkB (nullVec u₁) (trOf τ) = 0 := by rw [minkB_comm]; exact hE1 _ htE
      simp only [hFdef, hτp, minkB_add_right, h1', h2', add_zero]
    have hline : ∀ (p : Minkowski d) (s : ℝ), F (p + s • nullVec u₁) = F p := by
      intro p s
      have hq₁ : minkB (nullVec u₁) (nullVec u₁) = 0 := by rw [← minkQ_eq_minkB, minkQ_nullVec]
      simp only [hFdef]
      rw [minkB_add_right, minkB_add_right, minkB_smul_right, minkB_smul_right, hf1, hq₁,
        mul_zero, add_zero, add_zero]
    obtain ⟨M, hM⟩ := bddAbove_image_of_cauchyCompact hGH.1 hC hq hT hTΓ hdecH hFc
      (hinvS hFγ₀ hFτ) (isFutureCausal_nullVec u₁) (nullVec_ne_zero u₁) hline
    have hval : ∀ s : ℝ, F (p₀ + s • f) = F p₀ + a₀ * s * minkQ f := by
      intro s
      simp only [hFdef]
      rw [minkB_add_right, minkB_add_right, minkB_smul_right, minkB_smul_right,
        minkB_comm (nullVec u₁) f, hf1, mul_zero, add_zero, ← minkQ_eq_minkB]
      ring
    have hpos : 0 < (|M| + |F p₀| + 1) := by positivity
    set s : ℝ := (|M| + |F p₀| + 1) / (a₀ * minkQ f) with hsdef
    have hle' := hM ⟨_, hpΩ s, rfl⟩
    rw [hval] at hle'
    have : a₀ * s * minkQ f = |M| + |F p₀| + 1 := by
      rw [hsdef]; field_simp
    rw [this] at hle'
    linarith [le_abs_self M, neg_abs_le (F p₀)]
  · -- **the displacement of `γ₀`**: `L(γ₀)` moves `f`
    obtain ⟨F, hFdef⟩ : ∃ F : Minkowski d → ℝ, F = fun p =>
      minkQ (nullV (nullVec u₁) (nullVec u₂) (γ₀ • p - p)) := ⟨_, rfl⟩
    have hFc : Continuous F := hFdef ▸
      continuous_minkQ.comp ((continuous_nullV' _ _).comp
        ((continuous_const_smul γ₀).sub continuous_id))
    have hsub : ∀ p q : Minkowski d, γ₀ • q - γ₀ • p = linOf γ₀ (q - p) := by
      intro p q; rw [smul_eq_lin_add, smul_eq_lin_add, map_sub]; abel
    have hFγ₀ : ∀ p ∈ (Ω : Set (Minkowski d)), F (γ₀ • p) = F p := by
      intro p _
      simp only [hFdef]
      rw [hsub, nullV_map (linOf_mem γ₀) hc₀pos.ne' e₁ e₂, lorentz.minkQ_apply (linOf_mem γ₀)]
    have hFτ : ∀ τ ∈ Γ, linearPart τ = 1 → ∀ p, F (τ • p) = F p := by
      intro τ hτ hτ1 p
      obtain ⟨hτp, htE⟩ := htr τ hτ hτ1
      simp only [hFdef]
      rw [hτp, smul_eq_lin_add, smul_eq_lin_add γ₀ p, map_add, hEcen γ₀ hγ₀Γ _ htE]
      congr 2
      abel
    have hline : ∀ (p : Minkowski d) (s : ℝ), F (p + s • nullVec u₁) = F p := by
      intro p s
      simp only [hFdef]
      rw [isom_smul_add_smul, e₁,
        show γ₀ • p + s • c₀ • nullVec u₁ - (p + s • nullVec u₁) =
          (γ₀ • p - p) + (s * c₀ - s) • nullVec u₁ by rw [sub_smul, mul_smul]; abel,
        nullV_add_smul_left (minkQ_nullVec u₁) hBn]
    obtain ⟨M, hM⟩ := bddAbove_image_of_cauchyCompact hGH.1 hC hq hT hTΓ hdecH hFc.continuousOn
      (hinvS hFγ₀ hFτ) (isFutureCausal_nullVec u₁) (nullVec_ne_zero u₁) hline
    obtain ⟨w, hw⟩ : ∃ w : Minkowski d, w = nullV (nullVec u₁) (nullVec u₂) (γ₀ • p₀ - p₀) := ⟨_, rfl⟩
    obtain ⟨uu, huu⟩ : ∃ uu : Minkowski d, uu = linOf γ₀ f - f := ⟨_, rfl⟩
    have huu0 : uu ≠ 0 := by rw [huu]; exact sub_ne_zero.2 hL₀f
    have huu1 : minkB uu (nullVec u₁) = 0 := by
      rw [huu, minkB_sub_left, hf1, sub_zero]
      exact minkB_apply_eq_zero_of_image (linOf_mem γ₀) hc₀pos.ne' e₁ hf1
    have huu2 : minkB uu (nullVec u₂) = 0 := by
      rw [huu, minkB_sub_left, hf2, sub_zero]
      exact minkB_apply_eq_zero_of_image (linOf_mem γ₀) (inv_pos.2 hc₀pos).ne' e₂ hf2
    have hQu : 0 < minkQ uu := by
      obtain ⟨h0, h00⟩ := minkQ_nonneg_of_orth_frame (minkQ_nullVec u₁) (minkQ_nullVec u₂) hBn
        (y := uu) huu1 huu2
      exact lt_of_le_of_ne h0 fun h => huu0 (h00 h.symm)
    have hval : ∀ s : ℝ, F (p₀ + s • f) = minkQ w + 2 * (s * minkB w uu) + s ^ 2 * minkQ uu := by
      intro s
      simp only [hFdef]
      rw [isom_smul_add_smul,
        show γ₀ • p₀ + s • linOf γ₀ f - (p₀ + s • f) = (γ₀ • p₀ - p₀) + s • uu by
          rw [huu, smul_sub]; abel,
        nullV_add, nullV_smul, nullV_of_orth huu1 huu2, ← hw, minkQ_add, minkB_smul_right,
        minkQ_smul]
    set X : ℝ := |M| + |minkQ w| + 2 * |minkB w uu| + 1 with hX
    have hX0 : 0 < X := by positivity
    set s : ℝ := X / minkQ uu + 1 with hsdef
    have hs1 : 1 ≤ s := by
      rw [hsdef]; have := div_pos hX0 hQu; linarith
    have hsQ : X ≤ s * minkQ uu := by
      rw [hsdef, add_mul, div_mul_cancel₀ _ hQu.ne']; linarith
    have hle' := hM ⟨_, hpΩ s, rfl⟩
    rw [hval] at hle'
    have hb : -(s * |minkB w uu|) ≤ s * minkB w uu := by
      rw [neg_le, ← mul_neg]
      exact mul_le_mul_of_nonneg_left (neg_le_abs _) (by linarith)
    have h2 : s * X ≤ s ^ 2 * minkQ uu := by
      rw [sq, mul_assoc]; exact mul_le_mul_of_nonneg_left hsQ (by linarith)
    have h3 : X + 2 * (s - 1) * |minkB w uu| ≤ s * X := by
      have : 0 ≤ (s - 1) * (|M| + |minkQ w| + 1) := mul_nonneg (by linarith) (by positivity)
      rw [hX]; nlinarith [abs_nonneg (minkB w uu)]
    linarith [le_abs_self M, neg_abs_le (minkQ w), abs_nonneg (minkB w uu)]

end PairMain

end Causal.Flat.Cla
