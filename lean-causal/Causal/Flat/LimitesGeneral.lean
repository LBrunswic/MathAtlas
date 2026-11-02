import Causal.Flat.Nonloxodromic

/-!
# `Causal.Flat.LimitesGeneral` — Prop 9.3 without the normalisation `y₋ = −y₊`

* **`bprop:limites`** — `GHFspace.tex:2941` (Prop 9.3, l.2940–2989), marked (DEC-103: arbitrary
  endpoints, the fixed null frame `nolToMink` disclosed; **no `sorry`**) —
  `bprop_limites_of_isAchronal` (the three cases and "at least one extremity is finite") with
  `bprop_limites_general` (the bounded case for any `y₋ < y₊`). In detail: the bounded case without the normalisation
  `y₋ = −y₊`: `bprop_limites_bounded_model` (the reduction by the change of origin, in Barbot's
  coordinates), `bprop_limites_general_model` (its inequality read back in the original
  coordinates), `bprop_limites_general` (in `𝐌ⁿ`, `S̃` achronal), `bprop_limites_general_of_ccPrime`
  (under (CC′)); and `bprop_limites_of_isAchronal`, the normalised statement of
  `Flat/Nonloxodromic`'s `bprop_limites` with acausal weakened to achronal. Proved, no `sorry`.
  The two infinite cases need no normalisation and are `Flat/Nonloxodromic`'s.

> Denote by $y_{-}$, $y_{+}$ the extremities (maybe infinite) of the intervall
> $I = \pi_{1}(\widetilde{S})$. Remember that we assume here $y_{-} < 0 < y_{+}$. When $y_{\pm}$
> are both finite, we change the coordinates so that $y_{-} = -y_{+}$. (l.2933–2936)

> At least one of the extremities $y_{\pm}$ is finite. If they are both finite then, reducing as
> above to the case $y_{-} = -y_{+}$, for every $u$ in $E$ we have: $\mid y_{+}T(u) \mid \leq
> \mid u \mid$ (l.2943–2946)

> Since no $\gamma$-iterate of $X$ can be in the causal future of $X'$, this term must be
> positive for every $y$, $y'$ in $I$. (l.2978–2979)

**The change of coordinates.** It is the translation by `−c vₙ`, `c = (y₋ + y₊)/2`
(`NolParam.shiftY c`, an element of `𝒰(v₀)`; in `𝐌ⁿ` the isometry `isomTrans (−c vₙ)`,
`nolToMink_shiftY_act`); no boost is needed and the null frame `(v₀, vₙ)` is unchanged. It
conjugates `g ∈ 𝒜(v₀)` with data `(u, v, μ)` to `(u + c v, v, μ − (c/2)|v|²)`
(`shiftConj`, `shiftConj_eq`, `shiftConj_act`), so it changes `E` and `T`, not only `y`: the
new `u`-vectors are `u + c T u` and the new `T'` must satisfy `T'(u + c T u) = T u`. Such a
linear `T'` exists because `u ↦ u + c T u` is injective on `span L` (`limitesShift_injOn`: a
kernel vector would make the leading term `(y − c)(y' − c)|T u|²` negative for `y < c < y'` in
`I`), which the paper does not say. In the reduced coordinates Barbot's `|y₊ T'(u')| ≤ |u'|`
holds (`y₊ = a = (y₊ − y₋)/2` there); read back, it is `|a T u| ≤ |u + c T u|`, equivalently
`|u|² + (y₋ + y₊)⟨u | T u⟩ + y₋ y₊ |T u|² ≥ 0`, on `E = span L`.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| 9.3: `y₋ < 0 < y₊`, both finite | ⚠ weakened: `ylo < yhi` real (`0 ∈ I` unused) |
| 9.3: "reducing as above to `y₋ = −y₊`" | ✓ carried: proved, the translation `shiftY c` and the linear `T'` (`bprop_limites_bounded_model`) |
| 9.3: `I = π₁(S̃)` with extremities `y±` | ⚠ weakened: `π₁(S̃) ⊇ ]y₋, y₊[` |
| 9.3: `S̃` "no `γ`-iterate of `X` in the causal future of `X'`" | ⚠ weakened: `S̃` achronal (`IsAchronal`, `|X − X'|² ≥ 0`); acausal not used; supplied by (CC′) (`bprop_limites_general_of_ccPrime`) |
| 9.3: `Γ ⊆ 𝒜(v₀)`, `v = T u`, `Γ`-invariant | ✓ carried (as in `bprop_limites`) |
| 9.3: "`u(Γ)` is a lattice of `E`" | ⚠ weakened: `L` an additive subgroup, `E = span L` |
| 9.3: one element parabolic | ✓ carried (`hpar`) |
| 9.3: coordinates for the `v₀` of `Γ` | ⚠ strengthened (as in `bprop_limites`): the fixed frame `nolToMink` — **disclosed by ruling** (DEC-103), the same reading as the marked `bprop:extension`; Rem 9.2's frame changes are not used (its changes of `vₙ` are not frame changes: finding, `Flat/Nonloxodromic`) |
| `bprop:limites` (**marked**, DEC-103) | the printed statement: three cases and "at least one extremity is finite" (`bprop_limites_of_isAchronal`, `S̃` achronal, `y₋ < 0 < y₊` in `EReal` as the paper assumes, l.2934); the bounded case "reducing as above to `y₋ = −y₊`" for **arbitrary** real `y₋ < y₊` (`bprop_limites_general`); readings and weakenings as in the rows above |

## SCOPE (disclosed)

* **Ruled DEC-103 (2026-11-02):** `bprop:limites` is marked, for arbitrary endpoints, with the
  fixed null frame `nolToMink` disclosed; the findings below and Rem 9.2's (the changes of `vₙ`
  are not changes of null frame) are kept.
* **The reading of `S̃`.** The proof uses only achronality of `S̃` (the leading coefficient of
  `|γᵖX − X'|²` is `≥ 0`), not acausality, and the paper's "positive" is "nonnegative".
  Achronality follows from the standing hypotheses in DEC-35's reading: (CC′)(a) makes `Σ = S̃`
  an entire acausal graph (`CCPrime.entire.acausal`), and acausal implies achronal in `𝐌ⁿ`
  (`minkowski_isAchronal_of_isAcausal`). No added hypothesis on `S̃`.
* **Findings.** (1) The normalisation changes `E` and `T`, not only the coordinate `y`; it needs
  `1 + c T` injective on `E`, true by the leading term, unstated (l.2935–2936, l.2944).
  (2) The paper's inequality in the original coordinates is `|((y₊ − y₋)/2) T u| ≤
  |u + ((y₋ + y₊)/2) T u|`; the printed `|y₊ T(u)| ≤ |u|` is its form for `T'` only.
* Non-vacuity: the paraboloid `{x = −|z|²/(2(1 + y)), y > −1}` with `T = id`, `L = ⊤` on
  `E = ℝ`, un-normalised `ylo = −1/2 < yhi = 1` (`bprop_limites_general_model_hypotheses`).
* Prop 9.5 (`bprop:extension`) is not re-stated for un-normalised `y±` here.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Barbot campaign,
`bprop:limites` blocked_on (change of origin in `y`).
-/

namespace Causal.Flat

open Set Function Filter Topology Submodule
open scoped RealInnerProductSpace

/-! ## §1 The change of origin in `y`, an element of `𝒰(v₀)` -/

section Shift

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace NolParam

/-- **The change of origin in `y`** ("we change the coordinates so that `y₋ = −y₊`",
l.2935–2936): the translation by `−c vₙ`, `(x, z, y) ↦ (x, z, y − c)`, an element of `𝒰(v₀)`
(`R = id`, `u = v = 0`, `μ = 0`, `b = −c`). -/
noncomputable def shiftY (c : ℝ) : NolParam E := ⟨LinearIsometryEquiv.refl ℝ E, 0, 0, 0, -c⟩

theorem shiftY_act (c : ℝ) (X : ℝ × E × ℝ) : (shiftY c).act X = (X.1, X.2.1, X.2.2 - c) := by
  obtain ⟨x, z, y⟩ := X
  simp [act, shiftY, sub_eq_add_neg]

theorem shiftY_isU (c : ℝ) : (shiftY c : NolParam E).IsU := rfl

theorem shiftY_act_shiftY_neg (c : ℝ) (X : ℝ × E × ℝ) : (shiftY c).act ((shiftY (-c)).act X) = X := by
  obtain ⟨x, z, y⟩ := X
  simp [shiftY_act]

theorem shiftY_neg_act_shiftY (c : ℝ) (X : ℝ × E × ℝ) : (shiftY (-c)).act ((shiftY c).act X) = X := by
  obtain ⟨x, z, y⟩ := X
  simp [shiftY_act]

/-- **`g ∈ 𝒜(v₀)` in the shifted coordinates**: `u' = u + c v`, `v' = v`, `μ' = μ − (c/2)|v|²`,
`b' = 0`. -/
noncomputable def shiftConj (c : ℝ) (g : NolParam E) : NolParam E :=
  ⟨LinearIsometryEquiv.refl ℝ E, g.u + c • g.v, g.v, g.μ - c / 2 * ‖g.v‖ ^ 2, 0⟩

theorem shiftConj_isA (c : ℝ) (g : NolParam E) : (shiftConj c g).IsA := ⟨rfl, rfl⟩

/-- `shiftConj c g` is the conjugate `τ g τ⁻¹` of `g ∈ 𝒜(v₀)` by the change of origin
`τ = shiftY c`. -/
theorem shiftConj_eq {g : NolParam E} (hg : g.IsA) (c : ℝ) :
    shiftConj c g = (shiftY c).mul (g.mul (shiftY (-c))) := by
  have hR : g.R = LinearIsometryEquiv.refl ℝ E := hg.1
  ext x
  · simp [NolParam.mul, shiftY, shiftConj, hR]
  · simp [NolParam.mul, shiftY, shiftConj, hR]
  · simp [NolParam.mul, shiftY, shiftConj, hR]
  · simp [NolParam.mul, shiftY, shiftConj, hR]
  · simp [NolParam.mul, shiftY, shiftConj, hg.2]

/-- **The conjugation identity** `τ ∘ g = g' ∘ τ`, `g' = shiftConj c g`. -/
theorem shiftConj_act {g : NolParam E} (hg : g.IsA) (c : ℝ) (X : ℝ × E × ℝ) :
    (shiftConj c g).act ((shiftY c).act X) = (shiftY c).act (g.act X) := by
  rw [shiftConj_eq hg, act_mul, act_mul, shiftY_neg_act_shiftY]

end NolParam

/-- The linear map `u ↦ u + c T u`: in the shifted coordinates the `u`-vector of the element
with data `(u, T u)` is `u + c T u`. -/
noncomputable def limitesShift (c : ℝ) (T : E →ₗ[ℝ] E) : E →ₗ[ℝ] E := LinearMap.id + c • T

@[simp] theorem limitesShift_apply (c : ℝ) (T : E →ₗ[ℝ] E) (u : E) :
    limitesShift c T u = u + c • T u := rfl

end Shift

/-! ## §2 Prop 9.3, the bounded case, in Barbot's coordinates, for any `y₋ < y₊` -/

section General

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

open NolParam

/-- The leading coefficient `⟨u + y T u | u + y' T u⟩`, nonnegative on an additive subgroup `L`,
is nonnegative on its span. -/
theorem leading_nonneg_span {L : AddSubgroup E} {T : E →ₗ[ℝ] E} {y y' : ℝ}
    (h : ∀ u ∈ L, 0 ≤ ⟪u + y • T u, u + y' • T u⟫) :
    ∀ x ∈ span ℝ (L : Set E), 0 ≤ ⟪x + y • T x, x + y' • T x⟫ := by
  have hTc : Continuous T := LinearMap.continuous_of_finiteDimensional T
  refine nonneg_on_span_of_addSubgroup (q := fun u => ⟪u + y • T u, u + y' • T u⟫)
    (by fun_prop) (fun c x => ?_) h
  simp only [map_smul]
  rw [smul_comm y c, smul_comm y' c, ← smul_add, ← smul_add, inner_smul_left, inner_smul_right]
  simp only [conj_trivial]; ring

/-- **No pole at the midpoint** (what makes the change of origin a change of coordinates for
`T`): if the leading coefficient is nonnegative on `L` for every `y, y'` in `]ylo, yhi[`, then
`u ↦ u + c T u` is injective on `span L` for every `c` in `]ylo, yhi[`. -/
theorem limitesShift_injOn {L : AddSubgroup E} {T : E →ₗ[ℝ] E} {ylo yhi : ℝ}
    (hlead : ∀ u ∈ L, ∀ y y' : ℝ, ylo < y → y < yhi → ylo < y' → y' < yhi →
      0 ≤ ⟪u + y • T u, u + y' • T u⟫)
    {c : ℝ} (hc : ylo < c) (hc' : c < yhi) {u : E} (hu : u ∈ span ℝ (L : Set E))
    (h0 : u + c • T u = 0) : u = 0 := by
  set ε := min (c - ylo) (yhi - c) / 2 with hε
  have hε0 : 0 < ε := by
    have : 0 < min (c - ylo) (yhi - c) := lt_min (by linarith) (by linarith)
    linarith
  have hε1 : ε < c - ylo := by
    have := min_le_left (c - ylo) (yhi - c); linarith
  have hε2 : ε < yhi - c := by
    have := min_le_right (c - ylo) (yhi - c); linarith
  have hq := leading_nonneg_span (L := L) (T := T) (y := c - ε) (y' := c + ε)
    (fun v hv => hlead v hv _ _ (by linarith) (by linarith) (by linarith) (by linarith)) u hu
  have e : ∀ y : ℝ, u + y • T u = (y - c) • T u := fun y => by
    calc u + y • T u = (u + c • T u) + (y - c) • T u := by rw [sub_smul]; abel
      _ = (y - c) • T u := by rw [h0, zero_add]
  rw [e, e, inner_smul_left, inner_smul_right, real_inner_self_eq_norm_sq] at hq
  simp only [conj_trivial] at hq
  have hT : ‖T u‖ ^ 2 ≤ 0 := by
    have : (c - ε - c) * ((c + ε - c) * ‖T u‖ ^ 2) = -(ε ^ 2 * ‖T u‖ ^ 2) := by ring
    rw [this] at hq
    have : 0 ≤ ε ^ 2 * ‖T u‖ ^ 2 := by positivity
    nlinarith [sq_pos_of_pos hε0]
  have hTu : T u = 0 := by
    have := le_antisymm hT (sq_nonneg _)
    exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 this)
  rw [hTu, smul_zero, add_zero] at h0
  exact h0

omit [FiniteDimensional ℝ E] in
/-- **A linear `T'` on the shifted vectors**: if `u ↦ u + c T u` is injective on `span L`, there
is a linear `T'` with `T'(u + c T u) = T u` on `span L`. -/
theorem exists_limitesShift_inv {L : AddSubgroup E} {T : E →ₗ[ℝ] E} {c : ℝ}
    (hinj : ∀ u ∈ span ℝ (L : Set E), u + c • T u = 0 → u = 0) :
    ∃ T' : E →ₗ[ℝ] E, ∀ u ∈ span ℝ (L : Set E), T' (u + c • T u) = T u := by
  set E₀ := span ℝ (L : Set E)
  set S₀ : E₀ →ₗ[ℝ] E := limitesShift c T ∘ₗ E₀.subtype
  have hS₀ : Injective S₀ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    exact Subtype.ext (hinj x x.2 hx)
  set e := LinearEquiv.ofInjective S₀ hS₀
  obtain ⟨g, hg⟩ := LinearMap.exists_extend (T ∘ₗ E₀.subtype ∘ₗ e.symm.toLinearMap)
  refine ⟨g, fun u hu => ?_⟩
  have h1 : g (u + c • T u) = (g ∘ₗ (LinearMap.range S₀).subtype) ⟨S₀ ⟨u, hu⟩, ⟨_, rfl⟩⟩ := rfl
  rw [h1, hg]
  have h2 : e.symm ⟨S₀ ⟨u, hu⟩, ⟨_, rfl⟩⟩ = ⟨u, hu⟩ :=
    e.symm_apply_eq.2 (Subtype.ext rfl)
  simp [h2]

/-- **Prop 9.3, the bounded case, by the change of origin** (`bprop:limites`, l.2933–2946): for
the data of `bprop_limites_model` with `π₁(St) ⊇ ]ylo, yhi[`, `ylo < yhi` real (not normalised),
put `c = (ylo + yhi)/2` and `a = (yhi − ylo)/2`. The change of origin `shiftY c` (an element of
`𝒰(v₀)`, an isometry) carries the data to normalised ones: the same group, conjugated
(`shiftConj`), now has `u`-vectors `u + c T u` (`u ∈ L`) and `v = T' (u + c T u)` for a linear
`T'`, and `π₁` of the shifted `St` contains `]−a, a[`. Barbot's normalised inequality then holds
for `T'`: `|a T'(u')| ≤ |u'|` on the span of the shifted `u`-vectors. -/
theorem bprop_limites_bounded_model {St : Set (ℝ × E × ℝ)}
    (hach : ∀ X ∈ St, ∀ X' ∈ St, 0 ≤ nolQ (X - X')) {T : E →ₗ[ℝ] E} {L : AddSubgroup E}
    (hΓ : ∀ u ∈ L, ∃ g : NolParam E, g.IsA ∧ g.u = u ∧ g.v = T u ∧ ∀ X ∈ St, g.act X ∈ St)
    {ylo yhi : ℝ} (hlt : ylo < yhi)
    (hI : ∀ y : ℝ, ylo < y → y < yhi → ∃ X ∈ St, X.2.2 = y)
    (hpar : ∃ u ∈ L, T u ≠ 0) :
    ∃ T' : E →ₗ[ℝ] E,
      (∀ u ∈ span ℝ (L : Set E), T' (u + ((ylo + yhi) / 2) • T u) = T u) ∧
      (∀ u ∈ L, ∃ g : NolParam E, g.IsA ∧ g.u = u ∧ g.v = T u ∧ (∀ X ∈ St, g.act X ∈ St) ∧
        (shiftConj ((ylo + yhi) / 2) g).u = u + ((ylo + yhi) / 2) • T u ∧
        (shiftConj ((ylo + yhi) / 2) g).v = T' (u + ((ylo + yhi) / 2) • T u) ∧
        ∀ X ∈ (shiftY ((ylo + yhi) / 2)).act '' St,
          (shiftConj ((ylo + yhi) / 2) g).act X ∈ (shiftY ((ylo + yhi) / 2)).act '' St) ∧
      (∀ y : ℝ, -((yhi - ylo) / 2) < y → y < (yhi - ylo) / 2 →
        ∃ X ∈ (shiftY ((ylo + yhi) / 2)).act '' St, X.2.2 = y) ∧
      LimitesIneq (span ℝ ((L.map (limitesShift ((ylo + yhi) / 2) T).toAddMonoidHom :
        AddSubgroup E) : Set E)) T' (((-((yhi - ylo) / 2)) : ℝ) : EReal) (((yhi - ylo) / 2 : ℝ) : EReal) := by
  set c := (ylo + yhi) / 2 with hc
  set a := (yhi - ylo) / 2 with ha
  have ha0 : 0 < a := by rw [ha]; linarith
  have hlead : ∀ u ∈ L, ∀ y y' : ℝ, ylo < y → y < yhi → ylo < y' → y' < yhi →
      0 ≤ ⟪u + y • T u, u + y' • T u⟫ := by
    intro u hu y y' hy hy' hy₂ hy₂'
    obtain ⟨g, hg, rfl, hv, hinv⟩ := hΓ u hu
    obtain ⟨X, hX, rfl⟩ := hI y hy hy'
    obtain ⟨X', hX', rfl⟩ := hI y' hy₂ hy₂'
    rw [← hv]
    exact leading_nonneg_of_achronal hach hg hinv hX hX'
  obtain ⟨T', hT'⟩ := exists_limitesShift_inv (L := L) (T := T) (c := c)
    (fun u hu h0 => limitesShift_injOn hlead (by rw [hc]; linarith) (by rw [hc]; linarith) hu h0)
  set St' := (shiftY c).act '' St with hSt'
  have hΓ' : ∀ u ∈ L, ∃ g : NolParam E, g.IsA ∧ g.u = u ∧ g.v = T u ∧ (∀ X ∈ St, g.act X ∈ St) ∧
      (shiftConj c g).u = u + c • T u ∧ (shiftConj c g).v = T' (u + c • T u) ∧
      ∀ X ∈ St', (shiftConj c g).act X ∈ St' := by
    intro u hu
    obtain ⟨g, hg, hgu, hgv, hinv⟩ := hΓ u hu
    refine ⟨g, hg, hgu, hgv, hinv, by simp [shiftConj, hgu, hgv], ?_, ?_⟩
    · rw [hT' u (subset_span hu)]; exact hgv
    · rintro _ ⟨X, hX, rfl⟩
      exact ⟨g.act X, hinv X hX, (shiftConj_act hg c X).symm⟩
  have hI' : ∀ y : ℝ, -a < y → y < a → ∃ X ∈ St', X.2.2 = y := by
    intro y hy hy'
    obtain ⟨X, hX, hXy⟩ := hI (y + c) (by rw [hc]; rw [ha] at hy; linarith)
      (by rw [hc]; rw [ha] at hy'; linarith)
    exact ⟨_, ⟨X, hX, rfl⟩, by rw [shiftY_act, hXy]; ring⟩
  refine ⟨T', hT', hΓ', hI', ?_⟩
  refine (bprop_limites_model (St := St') ?_ ?_ (ylo := ((-a : ℝ) : EReal)) (yhi := (a : EReal))
    (by exact_mod_cast (by linarith : -a < 0)) (by exact_mod_cast ha0) ?_ ?_).2
  · rintro _ ⟨X, hX, rfl⟩ _ ⟨X', hX', rfl⟩
    rw [nolQ_act_sub]
    exact hach _ hX _ hX'
  · rintro _ ⟨u, hu, rfl⟩
    obtain ⟨g, hg, -, -, -, hu', hv', hinv'⟩ := hΓ' u hu
    exact ⟨shiftConj c g, shiftConj_isA c g, hu', hv', hinv'⟩
  · intro y hy hy'
    exact hI' y (by exact_mod_cast hy) (by exact_mod_cast hy')
  · obtain ⟨u, hu, hTu⟩ := hpar
    exact ⟨_, ⟨u, hu, rfl⟩, by
      show T' (u + c • T u) ≠ 0
      rw [hT' u (subset_span hu)]; exact hTu⟩

/-- **Prop 9.3, the bounded case, in the original coordinates** (`bprop:limites`, l.2943–2946):
for any `ylo < yhi` real (`ylo < 0 < yhi` in the paper, not normalised), Barbot's inequality
`|y₊ T(u)| ≤ |u|` of the reduced coordinates reads, for every `u ∈ E = span L`,
`|((y₊ − y₋)/2) T u| ≤ |u + ((y₋ + y₊)/2) T u|`, equivalently
`|u|² + (y₋ + y₊)⟨u | T u⟩ + y₋ y₊ |T u|² ≥ 0`. It is obtained from the normalised case
through the change of origin (`bprop_limites_bounded_model`). -/
theorem bprop_limites_general_model {St : Set (ℝ × E × ℝ)}
    (hach : ∀ X ∈ St, ∀ X' ∈ St, 0 ≤ nolQ (X - X')) {T : E →ₗ[ℝ] E} {L : AddSubgroup E}
    (hΓ : ∀ u ∈ L, ∃ g : NolParam E, g.IsA ∧ g.u = u ∧ g.v = T u ∧ ∀ X ∈ St, g.act X ∈ St)
    {ylo yhi : ℝ} (hlt : ylo < yhi)
    (hI : ∀ y : ℝ, ylo < y → y < yhi → ∃ X ∈ St, X.2.2 = y)
    (hpar : ∃ u ∈ L, T u ≠ 0) :
    ∀ u ∈ span ℝ (L : Set E), ‖((yhi - ylo) / 2) • T u‖ ≤ ‖u + ((ylo + yhi) / 2) • T u‖ ∧
      0 ≤ ‖u‖ ^ 2 + (ylo + yhi) * ⟪u, T u⟫ + ylo * yhi * ‖T u‖ ^ 2 := by
  obtain ⟨T', hT', -, -, hineq⟩ := bprop_limites_bounded_model hach hΓ hlt hI hpar
  intro u hu
  have hmem : u + ((ylo + yhi) / 2) • T u ∈ span ℝ ((L.map (limitesShift ((ylo + yhi) / 2)
      T).toAddMonoidHom : AddSubgroup E) : Set E) := by
    rw [AddSubgroup.coe_map]
    have : (⇑(limitesShift ((ylo + yhi) / 2) T).toAddMonoidHom) =
        ⇑(limitesShift ((ylo + yhi) / 2) T) := rfl
    rw [this, Submodule.span_image]
    exact Submodule.mem_map_of_mem hu
  have h1 := hineq.1 ((yhi - ylo) / 2) rfl rfl _ hmem
  rw [hT' u hu] at h1
  refine ⟨h1, ?_⟩
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, @norm_add_sq_real, norm_smul, mul_pow,
    Real.norm_eq_abs, sq_abs, inner_smul_right] at h2
  nlinarith [h2]

end General

/-! ## §2b Non-vacuity: a paraboloid preserved by `A_{id, 0}` -/

section Witness

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

open NolParam

/-- **The paraboloid** `{x = −|z|²/(2(1 + y)), y > −1}`, the orbit-closed achronal hypersurface
of the unipotent slab `{y > −1}` for `T = id` (Barbot's `S_f` with `f = 0`, cf. §3 [3.U]). -/
def limitesParaboloid (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    Set (ℝ × E × ℝ) :=
  {X | 0 < 1 + X.2.2 ∧ X.1 = -(‖X.2.1‖ ^ 2 / (2 * (1 + X.2.2)))}

/-- The element of `𝒜(v₀)` with `u = v = t`, `μ = −|t|²/2` (the group `A_{id, 0}`). -/
noncomputable def limitesWitnessElt (t : E) : NolParam E :=
  ⟨LinearIsometryEquiv.refl ℝ E, t, t, -(‖t‖ ^ 2 / 2), 0⟩

/-- The paraboloid is achronal: `(1 + y)(1 + y') |X − X'|² = |(1 + y) z' − (1 + y') z|²`. -/
theorem limitesParaboloid_achronal :
    ∀ X ∈ limitesParaboloid E, ∀ X' ∈ limitesParaboloid E, 0 ≤ nolQ (X - X') := by
  rintro ⟨x, z, y⟩ ⟨hs, hx⟩ ⟨x', z', y'⟩ ⟨hs', hx'⟩
  simp only at hs hx hs' hx'
  simp only [nolQ, Prod.mk_sub_mk]
  set s := 1 + y
  set s' := 1 + y'
  have key : s * s' * (2 * (x - x') * (y - y') + ‖z - z'‖ ^ 2) = ‖s • z' - s' • z‖ ^ 2 := by
    rw [hx, hx', @norm_sub_sq_real, @norm_sub_sq_real, norm_smul, norm_smul, inner_smul_left,
      inner_smul_right, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hs, abs_of_pos hs']
    simp only [conj_trivial]
    have hys : y - y' = s - s' := by simp only [s, s']; ring
    rw [hys, real_inner_comm z' z]
    field_simp
    ring
  have hss : 0 < s * s' := mul_pos hs hs'
  have : 0 ≤ s * s' * (2 * (x - x') * (y - y') + ‖z - z'‖ ^ 2) := by rw [key]; positivity
  exact (mul_nonneg_iff_of_pos_left hss).1 this

/-- The paraboloid is preserved by `A_{id, 0}`. -/
theorem limitesWitnessElt_mem (t : E) {X : ℝ × E × ℝ} (hX : X ∈ limitesParaboloid E) :
    (limitesWitnessElt t).act X ∈ limitesParaboloid E := by
  obtain ⟨x, z, y⟩ := X
  obtain ⟨hs, hx⟩ := hX
  simp only at hs hx
  refine ⟨by simpa [act, limitesWitnessElt] using hs, ?_⟩
  simp only [act, limitesWitnessElt, LinearIsometryEquiv.coe_refl, id, add_zero]
  have e : z + y • t + t = z + (1 + y) • t := by rw [add_smul, one_smul]; abel
  rw [e, @norm_add_sq_real, norm_smul, inner_smul_right, Real.norm_eq_abs, abs_of_pos hs, hx,
    real_inner_comm t z]
  field_simp
  ring

/-- **Non-vacuity of `bprop_limites_general_model`**, on `E = ℝ` with the un-normalised
`ylo = −1/2 < yhi = 1` (`c = 1/4`): the paraboloid, `T = id`, `L = ⊤` satisfy every hypothesis. -/
theorem bprop_limites_general_model_hypotheses :
    (∀ X ∈ limitesParaboloid ℝ, ∀ X' ∈ limitesParaboloid ℝ, 0 ≤ nolQ (X - X')) ∧
    (∀ u ∈ (⊤ : AddSubgroup ℝ), ∃ g : NolParam ℝ, g.IsA ∧ g.u = u ∧ g.v = (LinearMap.id : ℝ →ₗ[ℝ] ℝ) u ∧
      ∀ X ∈ limitesParaboloid ℝ, g.act X ∈ limitesParaboloid ℝ) ∧
    ((-1 / 2 : ℝ) < 1) ∧
    (∀ y : ℝ, -1 / 2 < y → y < 1 → ∃ X ∈ limitesParaboloid ℝ, X.2.2 = y) ∧
    (∃ u ∈ (⊤ : AddSubgroup ℝ), (LinearMap.id : ℝ →ₗ[ℝ] ℝ) u ≠ 0) := by
  refine ⟨limitesParaboloid_achronal, fun u _ => ⟨limitesWitnessElt u, ⟨rfl, rfl⟩, rfl, rfl,
    fun X hX => limitesWitnessElt_mem u hX⟩, by norm_num, fun y hy _ => ⟨(0, 0, y), ⟨?_, ?_⟩, rfl⟩,
    ⟨1, trivial, one_ne_zero⟩⟩
  · show 0 < 1 + y; linarith
  · simp

end Witness

/-! ## §3 In `𝐌ⁿ`: the change of origin is the translation by `−c vₙ` -/

section Minkowski

variable {d : ℕ}

/-- **The change of origin is an isometry of `𝐌ⁿ`**: in Barbot's coordinates (`nolToMink`),
`shiftY c` is the translation by `−c vₙ`, `vₙ = ofNull 0 1 0`. -/
theorem nolToMink_shiftY_act (c : ℝ) (X : ℝ × EuclideanSpace ℝ (Fin d) × ℝ) :
    nolToMink ((NolParam.shiftY c).act X) =
      isomTrans (d := d + 1) (nolToMink (0, 0, -c)) • nolToMink X := by
  rw [isom_smul_def]
  show _ = nolToMink (d := d) (0, 0, -c) +ᵥ nolToMink X
  rw [vadd_eq_add, NolParam.shiftY_act]
  have h := nolToMink_sub (d := d) (X.1, X.2.1, X.2.2 - c) (0, 0, -c)
  have e : ((X.1, X.2.1, X.2.2 - c) : ℝ × EuclideanSpace ℝ (Fin d) × ℝ) - (0, 0, -c) = X := by
    obtain ⟨x, z, y⟩ := X
    simp
  rw [e] at h
  rw [h]; abel

/-- **Prop 9.3 in `𝐌ⁿ`, achronal reading** (`bprop:limites`, all three cases of the
normalised statement): `bprop_limites` with `S̃` only achronal (`|X − X'|² ≥ 0`), which is all
its proof uses. -/
theorem bprop_limites_of_isAchronal {St : Set (Minkowski (d + 1))}
    (hach : (minkowski (d + 1)).IsAchronal St)
    {T : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)}
    {L : AddSubgroup (EuclideanSpace ℝ (Fin d))}
    (hΓ : ∀ u ∈ L, ∃ γ : isom (d + 1), (∀ p ∈ St, γ • p ∈ St) ∧ ∃ μ : ℝ, ∀ X,
      γ • nolToMink X =
        nolToMink ((⟨LinearIsometryEquiv.refl ℝ _, u, T u, μ, 0⟩ : NolParam _).act X))
    {ylo yhi : EReal} (hlo : ylo < 0) (hhi : 0 < yhi)
    (hI : ∀ y : ℝ, ylo < y → (y : EReal) < yhi → ∃ p ∈ St, nullY p = y)
    (hpar : ∃ u ∈ L, T u ≠ 0) :
    ¬(ylo = ⊥ ∧ yhi = ⊤) ∧ LimitesIneq (span ℝ (L : Set (EuclideanSpace ℝ (Fin d)))) T ylo yhi := by
  refine bprop_limites_model (St := nolToMink ⁻¹' St)
    (fun X hX X' hX' => ?_) (fun u hu => ?_) hlo hhi (fun y hy hy' => ?_) hpar
  · rw [← minkQ_nolToMink, nolToMink_sub]
    exact isAchronal_iff_minkQ.1 hach _ hX' _ hX
  · obtain ⟨γ, hinv, μ, hγ⟩ := hΓ u hu
    exact ⟨⟨LinearIsometryEquiv.refl ℝ _, u, T u, μ, 0⟩, ⟨rfl, rfl⟩, rfl, rfl, fun X hX => by
      show nolToMink _ ∈ St
      rw [← hγ]; exact hinv _ hX⟩
  · obtain ⟨p, hp, rfl⟩ := hI y hy hy'
    exact ⟨minkToNol p, by show nolToMink _ ∈ St; rw [nolToMink_minkToNol]; exact hp, rfl⟩

/-- **Prop 9.3, the bounded case, in `𝐌ⁿ`, without the normalisation** (`bprop:limites`,
l.2933–2946): `S̃ ⊆ 𝐌ⁿ` achronal, preserved by `Γ` acting through `𝒜(v₀)` with `v = T u`
(`u ∈ L`), `π₁(S̃) = nullY(S̃) ⊇ ]ylo, yhi[` for any real `ylo < yhi`, some element parabolic.
Then the reduced coordinates exist (the translation by `−c vₙ`, `c = (ylo + yhi)/2`,
`nolToMink_shiftY_act`, and a linear `T'` with `T'(u + c T u) = T u`) in which Barbot's
`|y₊ T'(u')| ≤ |u'|` holds with `y₊ = a = (yhi − ylo)/2`; in the original coordinates,
`|a T u| ≤ |u + c T u|` and `|u|² + (ylo + yhi)⟨u | T u⟩ + ylo yhi |T u|² ≥ 0` on `span L`. -/
theorem bprop_limites_general {St : Set (Minkowski (d + 1))}
    (hach : (minkowski (d + 1)).IsAchronal St)
    {T : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)}
    {L : AddSubgroup (EuclideanSpace ℝ (Fin d))}
    (hΓ : ∀ u ∈ L, ∃ γ : isom (d + 1), (∀ p ∈ St, γ • p ∈ St) ∧ ∃ μ : ℝ, ∀ X,
      γ • nolToMink X =
        nolToMink ((⟨LinearIsometryEquiv.refl ℝ _, u, T u, μ, 0⟩ : NolParam _).act X))
    {ylo yhi : ℝ} (hlt : ylo < yhi)
    (hI : ∀ y : ℝ, ylo < y → y < yhi → ∃ p ∈ St, nullY p = y)
    (hpar : ∃ u ∈ L, T u ≠ 0) :
    (∃ T' : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d),
      (∀ u ∈ span ℝ (L : Set (EuclideanSpace ℝ (Fin d))),
        T' (u + ((ylo + yhi) / 2) • T u) = T u) ∧
      LimitesIneq (span ℝ ((L.map (limitesShift ((ylo + yhi) / 2) T).toAddMonoidHom :
        AddSubgroup (EuclideanSpace ℝ (Fin d))) : Set (EuclideanSpace ℝ (Fin d)))) T'
        (((-((yhi - ylo) / 2)) : ℝ) : EReal) (((yhi - ylo) / 2 : ℝ) : EReal)) ∧
    ∀ u ∈ span ℝ (L : Set (EuclideanSpace ℝ (Fin d))),
      ‖((yhi - ylo) / 2) • T u‖ ≤ ‖u + ((ylo + yhi) / 2) • T u‖ ∧
      0 ≤ ‖u‖ ^ 2 + (ylo + yhi) * ⟪u, T u⟫ + ylo * yhi * ‖T u‖ ^ 2 := by
  have hach' : ∀ X ∈ nolToMink ⁻¹' St, ∀ X' ∈ nolToMink ⁻¹' St, 0 ≤ nolQ (X - X') := by
    intro X hX X' hX'
    rw [← minkQ_nolToMink, nolToMink_sub]
    exact isAchronal_iff_minkQ.1 hach _ hX' _ hX
  have hΓ' : ∀ u ∈ L, ∃ g : NolParam (EuclideanSpace ℝ (Fin d)), g.IsA ∧ g.u = u ∧ g.v = T u ∧
      ∀ X ∈ nolToMink ⁻¹' St, g.act X ∈ nolToMink ⁻¹' St := by
    intro u hu
    obtain ⟨γ, hinv, μ, hγ⟩ := hΓ u hu
    exact ⟨⟨LinearIsometryEquiv.refl ℝ _, u, T u, μ, 0⟩, ⟨rfl, rfl⟩, rfl, rfl, fun X hX => by
      show nolToMink _ ∈ St
      rw [← hγ]; exact hinv _ hX⟩
  have hI' : ∀ y : ℝ, ylo < y → y < yhi → ∃ X ∈ nolToMink ⁻¹' St, X.2.2 = y := by
    intro y hy hy'
    obtain ⟨p, hp, rfl⟩ := hI y hy hy'
    exact ⟨minkToNol p, by show nolToMink _ ∈ St; rw [nolToMink_minkToNol]; exact hp, rfl⟩
  obtain ⟨T', hT', -, -, hineq⟩ := bprop_limites_bounded_model hach' hΓ' hlt hI' hpar
  exact ⟨⟨T', hT', hineq⟩, bprop_limites_general_model hach' hΓ' hlt hI' hpar⟩

/-- **The standing hypothesis supplies the reading.** Under (CC′) (`CCPrime`, the DEC-35 reading
of §8's standing hypotheses, which every §9 call site carries through `CCAction`), `S̃ = Σ` is
acausal, hence achronal: `bprop_limites_general` applies with no added hypothesis on `S̃`. -/
theorem bprop_limites_general_of_ccPrime {St : Set (Minkowski (d + 1))} (hcc : CCPrime St)
    {T : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)}
    {L : AddSubgroup (EuclideanSpace ℝ (Fin d))}
    (hΓ : ∀ u ∈ L, ∃ γ : isom (d + 1), (∀ p ∈ St, γ • p ∈ St) ∧ ∃ μ : ℝ, ∀ X,
      γ • nolToMink X =
        nolToMink ((⟨LinearIsometryEquiv.refl ℝ _, u, T u, μ, 0⟩ : NolParam _).act X))
    {ylo yhi : ℝ} (hlt : ylo < yhi)
    (hI : ∀ y : ℝ, ylo < y → y < yhi → ∃ p ∈ St, nullY p = y)
    (hpar : ∃ u ∈ L, T u ≠ 0) :
    ∀ u ∈ span ℝ (L : Set (EuclideanSpace ℝ (Fin d))),
      ‖((yhi - ylo) / 2) • T u‖ ≤ ‖u + ((ylo + yhi) / 2) • T u‖ ∧
      0 ≤ ‖u‖ ^ 2 + (ylo + yhi) * ⟪u, T u⟫ + ylo * yhi * ‖T u‖ ^ 2 :=
  (bprop_limites_general (minkowski_isAchronal_of_isAcausal hcc.entire.acausal) hΓ hlt hI
    hpar).2

end Minkowski

end Causal.Flat
