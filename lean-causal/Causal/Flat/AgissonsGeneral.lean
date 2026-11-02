import Causal.Flat.Classification

/-!
# `Causal.Flat.AgissonsGeneral` — Barbot Prop 4.16 for an arbitrary discrete `Γ` preserving `Ω`

T. Barbot, *Globally hyperbolic flat space-times* (`papers/barbot`, arXiv math/0402257), §4.3;
line numbers are those of the labelled `papers/barbot/legacy/labeled/GHFspace.tex`. Barbot's
`𝐌ⁿ` has total dimension `n`; the library's `Minkowski d` has `d` spatial dimensions, so Barbot's
`n` is `d + 1` (kb/0024).

* `bprop:agissons` — `GHFspace.tex:1174` (Prop 4.16), unmarked (the marks are the author's; see
  SCOPE for the readings): `agissons_properlyDiscontinuous` (a discrete `Γ ≤ Isom(𝐌ⁿ)` preserving
  a future complete regular convex domain `Ω = Ω⁺(Λ)` acts properly discontinuously on it),
  `isOfFinOrder_of_smul_eq` (an element of `Γ` with a fixed point in `Ω` has finite order),
  `agissons_free` (torsion-free ⇒ free), `agissons_actsFreelyProperlyOn`, and
  `bprop_agissons_general` (the statement: properly discontinuous, and for torsion-free `Γ` free
  with quotient `Γ\Ω` a flat spacetime, globally hyperbolic in ETT's sense, Cauchy-complete, with
  an acausal Cauchy surface); **no `sorry`**. This supplies the clauses `Causal.Flat.Lox`'s
  `isCauchyComplete_flatQuotient_cosmo` took as instances (`ProperlyDiscontinuousSMul`,
  `IsCancelSMul`), for every discrete `Γ` rather than only the loxodromic `CCAction` groups of
  `bcor:loxo_proper`.

> In the first part of this section, $\Gamma$ is a discrete subgroup of $\mbox{Isom}(M^{n})$.
> (l.1170–1171)

> If $\Gamma$ preserves a future complete regular convex domain $\Omega$, then, the action of
> $\rho(\Gamma)$ on $\Omega$ is properly discontinuous. If moreover $\Gamma$ is torsionfree, then
> this action is free, and the quotient $\Gamma\backslash\Omega$ is a Cauchy-complete semicomplete
> GH spacetime. (l.1176–1180)

> This function is $\Gamma$-invariant. The action of $\Gamma$ on every level set $S_{t}$ is
> isometric for the induced riemanian metric. It follows that the action on $\Omega$ is properly
> discontinuous. (l.1187–1190)

> Assume now that $\gamma$ admits a fixed point $x$ in $\Omega$. Then, since its action on
> $S_{t}$ with $t = T(x)$ is isometric, and since $\Gamma$ is discrete, it follows that $\gamma$
> has finite order when restricted to $S_{t}$. According to the above, $\gamma$ itself has then
> finite order. Hence, if $\Gamma$ is torsionfree, the action is free. (l.1198–1204)

## How it is proved

Not through the Riemannian metric of `S_t` (absent here), but through the **Gauss map**
`n(p) = (p − r(p))/T(p)` of `Ω⁺(Λ)` into the unit future hyperboloid, the route `Loxodromic`'s
`loxo_properlyDiscontinuous` takes for `bcor:loxo_proper`: `n` is `L(Γ)`-equivariant
(`gaussMap_smul`) and bounded on compact subsets of `Ω` (`exists_norm_gaussMap_le`). If
`γK ∩ K ≠ ∅` for a compact `K ⊆ Ω`, then `L(γ)` maps the bounded point `n(k)` of `ℍᵈ` to the
bounded point `n(γk)`, so `‖L(γ)‖ ≤ c` (`norm_linOf_le_of_gauss`), and the translation part
`γk − L(γ)k` is bounded too; the same holds for `γ⁻¹` (`γ⁻¹(γK) ∩ K ≠ ∅`). So the affine
extensions `γ̂` and `γ̂⁻¹` (`TitsNull`'s `affExt`) of all such `γ` lie in a ball of the
finite-dimensional `End(𝐌ⁿ × ℝ)` (`norm_affExt_le`). Where `Loxodromic` then used a closed
`Γ`-invariant set on which `Γ` already acts properly, here the **discreteness** of `Γ` closes the
argument (`finite_of_norm_affExt_le`): a totally bounded image and pigeonhole give `γ ≠ γ'` with
`γ̂, γ̂'` close, so `‖(γ⁻¹γ')^ − 1‖ ≤ ‖γ̂⁻¹‖ ‖γ̂' − γ̂‖` is small, and `γ⁻¹γ' = 1` by
`TitsNull`'s `exists_affExt_isolated`. A fixed point `x` puts every `γᵏ` in the finite set of
`K = {x}`, so `γ` has finite order (`isOfFinOrder_of_smul_eq`); torsion-freeness gives freeness.
The quotient clauses are `Examples`' `gh_quotient_omegaPlus`, `isCauchySurface_quotient_cosmoLevel`
and `Cla`'s `isCauchyComplete_of_isQuotientOf_regular`, with the two instances now derived.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `Γ` a discrete subgroup of `Isom(𝐌ⁿ)` (l.1170) | ✓ carried: `DiscreteTopology Γ` in `Externals`' `isomTopology` (linear part, translation part) |
| `Γ` preserves `Ω` | ✓ carried: `PreservesOmega Λ Γ` (`γ⁻¹ Ω = Ω`) |
| `Ω` a future complete regular convex domain | ✓ in DEC-88's reading: `Ω = Ω⁺(Λ)`, `CosmoRegular Λ` |
| "properly discontinuous" | ✓ in `ActsFreelyProperlyOn`'s form: `{γ : γK ∩ K ≠ ∅}` finite for compact `K ⊆ Ω` (mathlib's `ProperlyDiscontinuousSMul` on the subtype follows, `properlyDiscontinuousSMul_of_finite`) |
| `Γ` torsion-free | ✓ carried: `IsTorsionFreeSubgroup Γ` (`Externals`); used only for freeness |
| "Cauchy-complete" | ✓ in DEC-35's reading (`IsCauchyComplete`, the induced length) |
| "GH spacetime" | ✓ both ETT's `GH` and Barbot's (an acausal Cauchy surface, the image of `S₁`) |
| "semicomplete" | not formalized (see SCOPE) |

## SCOPE (disclosed)

* The Riemannian argument of l.1187–1190 ("isometric on `S_t` … it follows") is replaced by the
  equivariant Gauss map; the step "an element trivial on `S_t` is trivial" (l.1191–1196) is not
  needed and not formalized.
* "semicomplete" in the conclusion is not formalized (no definition in the library); the other
  conclusions are proved.
* `ρ(Γ)` of l.1177 is read as `Γ` itself (the statement is about a subgroup of `Isom(𝐌ⁿ)`).
* Non-vacuity: `bprop_agissons_general_cone` (the trivial group on the future cone, `d ≥ 1`).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Barbot campaign.
-/

namespace Causal.Flat

open Set Function TopologicalSpace Topology Filter
open scoped Pointwise

universe u

variable {d : ℕ}

section AgissonsGeneral

/-- **The affine extension is bounded by the linear and translation parts**: `‖ĝ‖ ≤ c + τ + 1`
when `‖L(g) x‖ ≤ c ‖x‖` and `‖τ(g)‖ ≤ τ`. -/
theorem norm_affExt_le (g : isom d) {c τ : ℝ} (hc : 0 ≤ c) (hτ : 0 ≤ τ)
    (hL : ∀ x, ‖linOf g x‖ ≤ c * ‖x‖) (ht : ‖trOf g‖ ≤ τ) : ‖affExt g‖ ≤ c + τ + 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun p => ?_
  obtain ⟨y, s⟩ := p
  simp only [affExt_apply, Prod.norm_mk]
  have hy : ‖y‖ ≤ max ‖y‖ ‖s‖ := le_max_left _ _
  have hs : ‖s‖ ≤ max ‖y‖ ‖s‖ := le_max_right _ _
  have hm : 0 ≤ max ‖y‖ ‖s‖ := (norm_nonneg y).trans hy
  refine max_le ?_ ?_
  · calc ‖linOf g y + s • trOf g‖ ≤ ‖linOf g y‖ + ‖s‖ * ‖trOf g‖ := by
          rw [← norm_smul]; exact norm_add_le _ _
      _ ≤ c * max ‖y‖ ‖s‖ + max ‖y‖ ‖s‖ * τ := by
          gcongr
          exact (hL y).trans (mul_le_mul_of_nonneg_left hy hc)
      _ ≤ (c + τ + 1) * max ‖y‖ ‖s‖ := by nlinarith
  · nlinarith

/-- **Discreteness, as finiteness of bounded sets**: in a discrete `Γ ≤ Isom(𝐌ⁿ)`, a set of
elements whose affine extensions and those of their inverses are bounded is finite. -/
theorem finite_of_norm_affExt_le {Γ : Subgroup (isom d)} (hdisc : DiscreteTopology Γ)
    {E : Set (isom d)} (hE : E ⊆ Γ) {M : ℝ}
    (hM : ∀ γ ∈ E, ‖affExt γ‖ ≤ M ∧ ‖affExt γ⁻¹‖ ≤ M) : E.Finite := by
  obtain ⟨η, hη, hiso⟩ := exists_affExt_isolated hdisc
  by_contra hinf
  have hTB : TotallyBounded (affExt '' E) :=
    (isCompact_closedBall (0 : Minkowski d × ℝ →L[ℝ] Minkowski d × ℝ) M).totallyBounded.subset
      (by rintro _ ⟨γ, hγ, rfl⟩; simpa using (hM γ hγ).1)
  set C := |M| + 1 with hC
  have hC0 : 0 < C := by positivity
  set ε := η / (2 * C) with hεdef
  have hε : 0 < ε := by positivity
  obtain ⟨t, -, htf, hcov⟩ := Metric.finite_approx_of_totallyBounded hTB ε hε
  have hcen : ∀ γ ∈ E, ∃ y ∈ t, affExt γ ∈ Metric.ball y ε := fun γ hγ => by
    have := hcov ⟨γ, hγ, rfl⟩
    simpa only [mem_iUnion, exists_prop] using this
  choose! f hft hfb using hcen
  obtain ⟨γ, hγ, γ', hγ', hne, hfeq⟩ := Set.Infinite.exists_ne_map_eq_of_mapsTo hinf hft htf
  have hdist : ‖affExt γ' - affExt γ‖ < 2 * ε := by
    have h1 := hfb γ hγ
    have h2 := hfb γ' hγ'
    rw [hfeq] at h1
    rw [Metric.mem_ball, dist_eq_norm] at h1 h2
    calc ‖affExt γ' - affExt γ‖ = ‖(affExt γ' - f γ') - (affExt γ - f γ')‖ := by
          congr 1; abel
      _ ≤ ‖affExt γ' - f γ'‖ + ‖affExt γ - f γ'‖ := norm_sub_le _ _
      _ < ε + ε := add_lt_add h2 h1
      _ = 2 * ε := by ring
  have hmem : γ⁻¹ * γ' ∈ Γ := Γ.mul_mem (Γ.inv_mem (hE hγ)) (hE hγ')
  have hkey : affExt (γ⁻¹ * γ') - 1 = affExt γ⁻¹ * (affExt γ' - affExt γ) := by
    rw [affExt_mul, mul_sub, ← affExt_mul γ⁻¹ γ, inv_mul_cancel, affExt_one]
  have hinvM : ‖affExt γ⁻¹‖ ≤ C := (hM γ hγ).2.trans (by rw [hC]; linarith [le_abs_self M])
  have hlt : ‖affExt (γ⁻¹ * γ') - 1‖ < η := by
    rw [hkey]
    calc ‖affExt γ⁻¹ * (affExt γ' - affExt γ)‖
        ≤ ‖affExt γ⁻¹‖ * ‖affExt γ' - affExt γ‖ := norm_mul_le _ _
      _ ≤ C * ‖affExt γ' - affExt γ‖ := mul_le_mul_of_nonneg_right hinvM (norm_nonneg _)
      _ < C * (2 * ε) := mul_lt_mul_of_pos_left hdist hC0
      _ = η := by rw [hεdef]; field_simp
  have h1 := hiso _ hmem hlt
  exact hne (inv_mul_eq_one.1 h1)

variable {Λ : Set (PenroseSphere d × ℝ)} {Γ : Subgroup (isom d)}

/-- `γK ∩ K ≠ ∅` is symmetric under `γ ↦ γ⁻¹`. -/
theorem inv_mem_returnSet {K : Set (Minkowski d)} {γ : isom d}
    (h : γ ∈ Γ ∧ (γ • K ∩ K).Nonempty) : γ⁻¹ ∈ Γ ∧ (γ⁻¹ • K ∩ K).Nonempty := by
  obtain ⟨hγ, y, hyK, hy⟩ := h
  obtain ⟨k, hk, rfl⟩ := Set.mem_smul_set.1 hyK
  exact ⟨Γ.inv_mem hγ, k, Set.mem_smul_set.2 ⟨γ • k, hy, inv_smul_smul γ k⟩, hk⟩

/-- **Prop 4.16, proper discontinuity** (`bprop:agissons`, l.1176–1177, 1187–1190): a discrete
`Γ ≤ Isom(𝐌ⁿ)` preserving `Ω⁺(Λ)`, `Λ` Bonsante-regular, acts properly discontinuously on it.
By the equivariant Gauss map and discreteness (`finite_of_norm_affExt_le`). -/
theorem agissons_properlyDiscontinuous (hc : CosmoRegular Λ) (hdisc : DiscreteTopology Γ)
    (hP : PreservesOmega Λ Γ) :
    ∀ K ⊆ omegaPlus Λ, IsCompact K → {γ : isom d | γ ∈ Γ ∧ (γ • K ∩ K).Nonempty}.Finite := by
  intro K hKΩ hK
  obtain ⟨R, hR⟩ := exists_norm_gaussMap_le hc hKΩ hK
  obtain ⟨B, hB⟩ := isBounded_iff_forall_norm_le.1 hK.isBounded
  set c := 2 * R ^ 2 * (8 * R ^ 2 + 1) + 1 with hcdef
  have hc0 : 0 ≤ c := by positivity
  have hbd : ∀ γ ∈ {γ : isom d | γ ∈ Γ ∧ (γ • K ∩ K).Nonempty},
      ‖affExt γ‖ ≤ c + (|B| + c * |B|) + 1 := by
    rintro γ ⟨hγ, y, hyK, hy⟩
    obtain ⟨k, hk, rfl⟩ := Set.mem_smul_set.1 hyK
    have hkΩ := hKΩ hk
    have hL := norm_linOf_le_of_gauss (g := γ) (isFutureTimelike_gaussMap hc hkΩ)
      (minkQ_gaussMap hc hkΩ) (hR k hk)
      (by rw [← gaussMap_smul hc (hP γ hγ) hkΩ]; exact hR _ hy)
    refine norm_affExt_le γ hc0 (by positivity) hL ?_
    have htr : trOf γ = γ • k - linOf γ k := by rw [smul_eq_lin_add]; abel
    have hk' : ‖k‖ ≤ |B| := (hB k hk).trans (le_abs_self B)
    have hγk : ‖γ • k‖ ≤ |B| := (hB _ hy).trans (le_abs_self B)
    rw [htr]
    calc ‖γ • k - linOf γ k‖ ≤ ‖γ • k‖ + ‖linOf γ k‖ := norm_sub_le _ _
      _ ≤ |B| + c * |B| := add_le_add hγk ((hL k).trans (mul_le_mul_of_nonneg_left hk' hc0))
  exact finite_of_norm_affExt_le hdisc (fun γ hγ => hγ.1)
    fun γ hγ => ⟨hbd γ hγ, hbd _ (inv_mem_returnSet hγ)⟩

/-- **An element with a fixed point in `Ω⁺(Λ)` has finite order** (l.1198–1203): every power
`γᵏ` returns the compact `{x}` to itself, and that set of elements is finite. -/
theorem isOfFinOrder_of_smul_eq (hc : CosmoRegular Λ) (hdisc : DiscreteTopology Γ)
    (hP : PreservesOmega Λ Γ) {γ : isom d} (hγ : γ ∈ Γ) {x : Minkowski d}
    (hx : x ∈ omegaPlus Λ) (hfix : γ • x = x) : IsOfFinOrder γ := by
  have hfin := agissons_properlyDiscontinuous hc hdisc hP {x} (singleton_subset_iff.2 hx)
    isCompact_singleton
  have hpow : ∀ n : ℕ, γ ^ n • x = x := by
    intro n
    induction n with
    | zero => rw [pow_zero, one_smul]
    | succ n ih => rw [pow_succ, mul_smul, hfix, ih]
  have hmaps : MapsTo (fun n : ℕ => γ ^ n) univ
      {γ : isom d | γ ∈ Γ ∧ (γ • ({x} : Set (Minkowski d)) ∩ {x}).Nonempty} := by
    intro n _
    refine ⟨Γ.pow_mem hγ n, x, ?_, rfl⟩
    rw [Set.smul_set_singleton, hpow n]
    rfl
  by_contra hfo
  obtain ⟨m, -, n, -, hmn, he⟩ := Set.infinite_univ.exists_ne_map_eq_of_mapsTo hmaps hfin
  exact hmn ((injective_pow_iff_not_isOfFinOrder.2 hfo) he)

/-- **Prop 4.16, freeness** (l.1178–1179, 1198–1204): a torsion-free discrete `Γ` preserving
`Ω⁺(Λ)` acts freely on it. -/
theorem agissons_free (hc : CosmoRegular Λ) (hdisc : DiscreteTopology Γ)
    (hP : PreservesOmega Λ Γ) (htf : IsTorsionFreeSubgroup Γ) :
    ∀ γ ∈ Γ, γ ≠ 1 → ∀ x ∈ omegaPlus Λ, γ • x ≠ x :=
  fun γ hγ h1 _ hx hfix => h1 (htf γ hγ (isOfFinOrder_of_smul_eq hc hdisc hP hγ hx hfix))

/-- **Prop 4.16, the action**: free and properly discontinuous, for torsion-free discrete `Γ`. -/
theorem agissons_actsFreelyProperlyOn (hc : CosmoRegular Λ) (hdisc : DiscreteTopology Γ)
    (hP : PreservesOmega Λ Γ) (htf : IsTorsionFreeSubgroup Γ) :
    ActsFreelyProperlyOn Γ (omegaPlus Λ) :=
  ⟨agissons_free hc hdisc hP htf, agissons_properlyDiscontinuous hc hdisc hP⟩

/-- **Prop 4.16** (`bprop:agissons`, l.1176–1180), for an arbitrary discrete `Γ ≤ Isom(𝐌ⁿ)`
preserving a future complete regular convex domain `Ω = Ω⁺(Λ)` (`CosmoRegular Λ`, DEC-88): the
action is properly discontinuous; if moreover `Γ` is torsion-free, it is free, and `Γ\Ω` is a
flat spacetime, globally hyperbolic (ETT's `GH`), Cauchy-complete (DEC-35), with an acausal
Cauchy surface (the image of `S₁`). "Semicomplete" is not formalized. -/
theorem bprop_agissons_general (hc : CosmoRegular Λ) (hdisc : DiscreteTopology Γ)
    (hP : PreservesOmega Λ Γ) :
    (∀ K ⊆ omegaPlus Λ, IsCompact K → {γ : isom d | γ ∈ Γ ∧ (γ • K ∩ K).Nonempty}.Finite) ∧
      (IsTorsionFreeSubgroup Γ →
        ActsFreelyProperlyOn Γ (omegaPlus Λ) ∧
          ∃ M : FlatSpacetime.{0} d, IsQuotientOf M Γ hc.regular.opens ∧ GH M ∧
            IsCauchyComplete d M ∧
            ∃ Sc : Set M, (flatCausality d M).IsCauchySurface Sc ∧
              (flatCausality d M).IsAcausal Sc) := by
  refine ⟨agissons_properlyDiscontinuous hc hdisc hP, fun htf => ?_⟩
  have hfp := agissons_actsFreelyProperlyOn hc hdisc hP htf
  refine ⟨hfp, ?_⟩
  haveI : FlatQuotient.Invariant Γ hc.regular.opens := hP.invariant (h := hc)
  haveI : IsCancelSMul Γ hc.regular.opens := isCancelSMul_of_free fun γ hγ h1 x hx => hfp.1 γ hγ h1 x hx
  haveI : ProperlyDiscontinuousSMul Γ hc.regular.opens :=
    properlyDiscontinuousSMul_of_finite fun K hK hKc => hfp.2 K hK hKc
  have hq := FlatQuotient.isQuotientOf_toFlatSpacetime Γ hc.regular.opens (isConnected_omegaPlus hc)
  refine ⟨FlatQuotient.toFlatSpacetime Γ hc.regular.opens (isConnected_omegaPlus hc), hq,
    gh_quotient_omegaPlus (h := hc) hP, ?_, _,
    (isCauchySurface_quotient_cosmoLevel (h := hc) hP one_pos).1,
    (isCauchySurface_quotient_cosmoLevel (h := hc) hP one_pos).2⟩
  refine Cla.isCauchyComplete_of_isQuotientOf_regular (Λ := Λ) (Γ := Γ) (Ω := hc.regular.opens)
    (Or.inl ⟨hc, fun p => Iff.rfl⟩) 1 ?_
  rw [frameConj_one, isomImage_one]; exact hq

/-- **Non-vacuity**: the trivial group on the future cone (`d ≥ 1`) satisfies every hypothesis of
`bprop_agissons_general`, including torsion-freeness. -/
theorem bprop_agissons_general_cone (hd : 0 < d) :
    let Λ : Set (PenroseSphere d × ℝ) := univ ×ˢ {0}
    CosmoRegular Λ ∧ DiscreteTopology (⊥ : Subgroup (isom d)) ∧ PreservesOmega Λ ⊥ ∧
      IsTorsionFreeSubgroup (⊥ : Subgroup (isom d)) := by
  refine ⟨cosmoRegular_cone hd, inferInstance, fun γ hγ => ?_, fun g hg _ => hg⟩
  rw [Subgroup.mem_bot] at hγ
  subst hγ
  ext p; simp

end AgissonsGeneral

end Causal.Flat
