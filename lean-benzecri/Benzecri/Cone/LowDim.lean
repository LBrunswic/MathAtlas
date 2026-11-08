import Benzecri.Cone.Base

/-!
# `Benzecri.Cone.LowDim` — in dimension `n ≤ 2` the base of an affine conical manifold is Hausdorff (DEC-122)

J.-P. Benzécri, *Sur les variétés localement affines et localement projectives*, Bull. SMF 88
(1960) 229–332, Chapter 1 § 2, journal p. 240; transcription
`papers/benzecri/legacy/labeled/benzecri1960_ch1.tex`. Package WP-45q (wave-3 fix round). The
theorem DEC-122 asks to formalize; its argument is the wave-3 audit's
(`campaign/WP-45n/AUDIT-1.json`, check `theorem_n_le_2`), recast through the properness
criterion of `Cone/Base`.

* `bzprop:c1s2p2_base_cone` — `benzecri1960_ch1.tex:540` (§ 2 Prop. 2, l.540–546, p. 240), **not
  marked here** (the mark is on its corrected form, `Cone/Base`): in Benzécri's dimension `n ≤ 2`
  the corrected form needs no extra hypothesis. **The `n ≤ 2` theorem**:
  `LowDim.properSMul_of_le_one` — for a Hausdorff affine conical manifold of dimension `n ≤ 2`
  (Lean's base index `n ≤ 1`, `V` charted on `RnO (n + 1)`), the action of `ℝ₊*` is proper — and
  `LowDim.t2Space_coneBase_of_le_one` — its base `B = V/ℝ⁺` is Hausdorff. It fails for every `n ≥ 3`
  (`Cone/Counterexample`).

The proof, dimension by dimension (Mathlib's ultrafilter criterion for properness,
`ConeBase.properSMul_of_tendsto`: if `(λ_i m_i, m_i) → (m', m)`, the `λ_i` converge as soon as the
radii `‖f'(m_i)‖` do, in a cone chart `f'` at `m'`, `ConeBase.tendsto_fst_of_tendsto_radius`):

* `n = 1` (`LowDim.properSMul_dim_one`): the transitions lie in `GU(1) = {±1}`, which preserves the
  norm (`LowDim.norm_smul_GU_one`), so `‖f'(m_i)‖ = ‖f(m_i)‖ → ‖f(m)‖`.
* `n = 2` (`LowDim.properSMul_dim_two`): along the ultrafilter, the transition `f' = G ∘ f` at
  `m_i` is eventually CONSTANT, `G₀`, so `‖f'(m_i)‖ → ‖G₀ f(m)‖`. The rays near `f(m)` are
  parametrised by a projective coordinate `s ∈ (-δ, δ)` (`LowDim.rv`, `LowDim.lf`, `LowDim.kf`), and
  those near `f'(m')` by `κ/ℓ ∈ (-δ', δ')`; the overlap is cut into components on which the
  transition is constant (`LowDim.exists_endpoint`). Either a component reaches the ray of `f(m)`
  (one transition), or its endpoint toward it is an interior point of the parameter interval which,
  `V` being Hausdorff (closedness of the relation, `H3`), the transition sends to one of the TWO
  boundary rays `κ/ℓ = ±δ'` of the target cone; two components sent to the same boundary ray have
  overlapping images (intermediate value theorem), hence coincide (the target chart is injective,
  `H5`). So at most three transitions occur near `f(m)`, and the ultrafilter picks one
  (`LowDim.eventually_eq_of_left`, `_of_right`). This is the audit's « each overlap component …
  carries a single transition; Hausdorffness of `V` allows at most two components; so `λ` stays
  bounded », localised at the ray of `f(m)`.

> **Prop. 2.** Sur le quotient $B=V/\R^+$, appelé *base* de l'espace fibré $V$, est définie
> canoniquement une structure localement projective […]

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `V` an affine conical manifold (Déf. 2) of dimension `n ≤ 2` | ✓ carried: `[ChartedSpace (RnO (n + 1)) V] [HasGroupoid V (coneGroupoid (n + 1))] [HasConeCharts (n + 1) V]`, `n ≤ 1` (Lean's index) |
| `V` a « variété »: Hausdorff | ✓ carried: `[T2Space V]` (used: Déf. 3's action, and the closedness step) |
| `V` second countable, connected | not needed (`⚠ weakened`) |
| conclusion: `B` a « variété » (Hausdorff) | ✓ proved: `T2Space (ConeBase n V)`, and the action is proper |

## SCOPE (disclosed)

* The statement is proved in full for `n ≤ 2`, no `sorry`. The audit's global count (« at most two
  components ») is not formalized as such: the proof only needs that the components meeting a
  neighbourhood of the ray of `f(m)` carry at most three transitions, which is what the boundary
  argument gives locally.
* Benzécri's `n = 0` (`ℝ⁰ − {O}` empty) is outside Lean's indexing (`RnO (n + 1)`) and trivial.
* `uniqueFinZeroAddOne` is a LOCAL instance (`Fin (0 + 1)` is a Mathlib type); no global instance is
  added.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

noncomputable section

open Set Filter Topology

namespace Benzecri

namespace LowDim

section Core

variable {Γ P : Type*} [Group Γ] [TopologicalSpace P] [MulAction Γ P] [ContinuousConstSMul Γ P]

/-- `|κ/ℓ| < δ'` inside the cone `|κ| < δ' ℓ`. -/
theorem abs_div_lt_of {a l δ' : ℝ} (h : |a| < δ' * l) (hδ' : 0 < δ') : 0 < l ∧ |a / l| < δ' := by
  have hl : 0 < l := by
    have : 0 < δ' * l := lt_of_le_of_lt (abs_nonneg a) h
    exact pos_of_mul_pos_right this hδ'.le
  refine ⟨hl, ?_⟩
  rw [abs_div, abs_of_pos hl, div_lt_iff₀ hl]
  linarith [mul_comm δ' l]

/-- **The endpoint of a component**: starting from `R g s` with `-δ < s < 0`, let `b` be the
supremum of the `t ≤ 0` such that `R g` holds on `[s, t]`. Then `R g` holds on `[s, b)`, and either
`R g 0`, or `b` is an interior endpoint at which `g • ρ` leaves the cone `|κ| < δ' ℓ` through its
boundary: `κ/ℓ = ±δ'` at `b`, `κ/ℓ` continuous on `[s, b]`. -/
theorem exists_endpoint (ρ : ℝ → P) (hρ : Continuous ρ) (ℓ κ : P → ℝ) (hℓ : Continuous ℓ)
    (hκ : Continuous κ) (hne : ∀ w, ℓ w = 0 → κ w = 0 → False) {δ δ' : ℝ} (hδ' : 0 < δ')
    (R : Γ → ℝ → Prop)
    (H2 : ∀ g s, R g s → ∀ᶠ t in 𝓝 s, R g t)
    (H3 : ∀ g s, -δ < s → s ≤ 0 → (∀ᶠ t in 𝓝[<] s, R g t) →
      |κ (g • ρ s)| < δ' * ℓ (g • ρ s) → R g s)
    (H4 : ∀ g s, R g s → |κ (g • ρ s)| < δ' * ℓ (g • ρ s))
    (g : Γ) {s : ℝ} (hs1 : -δ < s) (hs2 : s < 0) (hR : R g s) :
    ∃ b, s < b ∧ (∀ w, s ≤ w → w < b → R g w) ∧
      (R g 0 ∨ (ContinuousOn (fun t => κ (g • ρ t) / ℓ (g • ρ t)) (Icc s b) ∧
        (κ (g • ρ b) / ℓ (g • ρ b) = δ' ∨ κ (g • ρ b) / ℓ (g • ρ b) = -δ'))) := by
  set S : Set ℝ := {t | s ≤ t ∧ t ≤ 0 ∧ ∀ w, s ≤ w → w ≤ t → R g w} with hSdef
  have hSne : S.Nonempty := ⟨s, le_rfl, hs2.le, fun w h1 h2 => le_antisymm h2 h1 ▸ hR⟩
  have hSbdd : BddAbove S := ⟨0, fun t ht => ht.2.1⟩
  set b := sSup S with hbdef
  have hb0 : b ≤ 0 := csSup_le hSne fun t ht => ht.2.1
  have hbelow : ∀ w, s ≤ w → w < b → R g w := by
    intro w hsw hwb
    obtain ⟨t, ht, hwt⟩ := exists_lt_of_lt_csSup hSne hwb
    exact ht.2.2 w hsw hwt.le
  -- extending past a point where `R g` holds
  have hext : ∀ a, s ≤ a → a < 0 → (∀ w, s ≤ w → w < a → R g w) → R g a → a < b := by
    intro a hsa ha0 hbel hRa
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 (H2 g a hRa)
    set t₁ := min (a + ε / 2) 0
    have hat₁ : a < t₁ := lt_min (by linarith) ha0
    have ht₁ : t₁ ∈ S := by
      refine ⟨hsa.trans hat₁.le, min_le_right _ _, fun w hsw hwt => ?_⟩
      rcases lt_or_ge w a with hw | hw
      · exact hbel w hsw hw
      · refine hball ?_
        rw [Real.dist_eq, abs_of_nonneg (by linarith)]
        have : w ≤ a + ε / 2 := hwt.trans (min_le_left _ _)
        linarith
    exact lt_of_lt_of_le hat₁ (le_csSup hSbdd ht₁)
  have hsb : s < b := hext s le_rfl hs2 (fun w h1 h2 => absurd h1 (not_le.2 h2)) hR
  refine ⟨b, hsb, hbelow, ?_⟩
  by_cases hRb : R g b
  · left
    rcases lt_or_eq_of_le hb0 with hb | hb
    · exact absurd (hext b (hsb.le) hb hbelow hRb) (lt_irrefl b)
    · rwa [hb] at hRb
  right
  have hcl : Continuous fun t => ℓ (g • ρ t) := hℓ.comp ((continuous_const_smul g).comp hρ)
  have hck : Continuous fun t => κ (g • ρ t) := hκ.comp ((continuous_const_smul g).comp hρ)
  have hleft : ∀ᶠ t in 𝓝[<] b, R g t := by
    filter_upwards [Ioo_mem_nhdsLT hsb] with t ht
    exact hbelow t ht.1.le ht.2
  set F : ℝ → ℝ := fun t => δ' * ℓ (g • ρ t) - |κ (g • ρ t)|
  have hF : Continuous F := (continuous_const.mul hcl).sub hck.abs
  have hFle : F b ≤ 0 := by
    by_contra h
    push Not at h
    exact hRb (H3 g b (hs1.trans hsb) hb0 hleft (by simp only [F] at h; linarith))
  have hFge : 0 ≤ F b := by
    refine ge_of_tendsto ((hF.continuousAt (x := b)).tendsto.mono_left
      (nhdsWithin_le_nhds (s := Iio b))) ?_
    filter_upwards [hleft] with t ht
    have := H4 g t ht
    simp only [F]
    linarith
  have hEq : |κ (g • ρ b)| = δ' * ℓ (g • ρ b) := by simp only [F] at hFle hFge; linarith
  have hlb : 0 < ℓ (g • ρ b) := by
    rcases lt_trichotomy (ℓ (g • ρ b)) 0 with h | h | h
    · have := abs_nonneg (κ (g • ρ b))
      nlinarith
    · exfalso
      refine hne _ h ?_
      rw [h, mul_zero, abs_eq_zero] at hEq
      exact hEq
    · exact h
  refine ⟨?_, ?_⟩
  · refine hck.continuousOn.div hcl.continuousOn fun t ht => ?_
    rcases lt_or_eq_of_le ht.2 with h | h
    · exact (abs_div_lt_of (H4 g t (hbelow t ht.1 h)) hδ').1.ne'
    · rw [h]; exact hlb.ne'
  · rcases abs_eq (by positivity : 0 ≤ δ' * ℓ (g • ρ b)) |>.1 hEq with h | h
    · left; rw [h, mul_div_assoc, div_self hlb.ne', mul_one]
    · right; rw [h, neg_div, mul_div_assoc, div_self hlb.ne', mul_one]

/-- **The core of the dimension-2 theorem** (left side). Along an ultrafilter of parameters
`s ∈ (-δ, 0)` at which some transition `g` holds (`R g s`), the transition is eventually constant:
each `s` lies in a component `[s, b)` of `R g`; either it reaches `0` (one transition), or its
endpoint `b` is sent by `g` to one of the two boundary rays `κ/ℓ = ±δ'` of the target cone, and two
components sent to the same boundary ray have overlapping images (intermediate value theorem), so
they coincide (`H5`: the target chart is injective). -/
theorem eventually_eq_of_left (ρ : ℝ → P) (hρ : Continuous ρ) (ℓ κ : P → ℝ) (hℓ : Continuous ℓ)
    (hκ : Continuous κ) (hne : ∀ w, ℓ w = 0 → κ w = 0 → False) {δ δ' : ℝ} (hδ' : 0 < δ')
    (R : Γ → ℝ → Prop)
    (H1 : ∀ g h s, R g s → R h s → g = h)
    (H2 : ∀ g s, R g s → ∀ᶠ t in 𝓝 s, R g t)
    (H3 : ∀ g s, -δ < s → s ≤ 0 → (∀ᶠ t in 𝓝[<] s, R g t) →
      |κ (g • ρ s)| < δ' * ℓ (g • ρ s) → R g s)
    (H4 : ∀ g s, R g s → |κ (g • ρ s)| < δ' * ℓ (g • ρ s))
    (H5 : ∀ g h s t, R g s → R h t →
      κ (g • ρ s) / ℓ (g • ρ s) = κ (h • ρ t) / ℓ (h • ρ t) → s = t)
    (𝒱 : Ultrafilter ℝ) (hV : ∀ᶠ s in (𝒱 : Filter ℝ), -δ < s ∧ s < 0 ∧ ∃ g, R g s) :
    ∃ g₀, ∀ᶠ s in (𝒱 : Filter ℝ), R g₀ s := by
  classical
  set gs : ℝ → Γ := fun s => if h : ∃ g, R g s then h.choose else 1 with hgsdef
  have hgs : ∀ s, (∃ g, R g s) → R (gs s) s := fun s h => by
    simp only [hgsdef, dif_pos h]; exact h.choose_spec
  set ψ : Γ → ℝ → ℝ := fun g t => κ (g • ρ t) / ℓ (g • ρ t) with hψ
  have hψlt : ∀ g t, R g t → |ψ g t| < δ' := fun g t h => (abs_div_lt_of (H4 g t h) hδ').2
  -- the three cases
  have hcases : ∀ᶠ s in (𝒱 : Filter ℝ), R (gs s) 0 ∨
      (∃ b, s < b ∧ (∀ w, s ≤ w → w < b → R (gs s) w) ∧
        ContinuousOn (ψ (gs s)) (Icc s b) ∧ ψ (gs s) b = δ') ∨
      (∃ b, s < b ∧ (∀ w, s ≤ w → w < b → R (gs s) w) ∧
        ContinuousOn (ψ (gs s)) (Icc s b) ∧ ψ (gs s) b = -δ') := by
    filter_upwards [hV] with s ⟨hs1, hs2, hex⟩
    obtain ⟨b, hsb, hbel, h⟩ := exists_endpoint ρ hρ ℓ κ hℓ hκ hne hδ' R H2 H3 H4 (gs s) hs1 hs2
      (hgs s hex)
    rcases h with h | ⟨hc, h | h⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨b, hsb, hbel, hc, h⟩)
    · exact Or.inr (Or.inr ⟨b, hsb, hbel, hc, h⟩)
  have hR : ∀ᶠ s in (𝒱 : Filter ℝ), R (gs s) s := by
    filter_upwards [hV] with s hs
    exact hgs s hs.2.2
  rcases Ultrafilter.eventually_or.1 hcases with h0 | h
  · obtain ⟨s₁, hs₁⟩ := (h0.and hR).exists
    refine ⟨gs s₁, ?_⟩
    filter_upwards [h0, hR] with s h0s hRs
    rwa [H1 _ _ 0 h0s hs₁.1] at hRs
  -- two components ending on the same boundary ray carry the same transition
  have hsame : ∀ (σ : ℝ), (σ = δ' ∨ σ = -δ') → ∀ s₁ s₂ b₁ b₂, s₁ < b₁ → s₂ < b₂ →
      (∀ w, s₁ ≤ w → w < b₁ → R (gs s₁) w) → (∀ w, s₂ ≤ w → w < b₂ → R (gs s₂) w) →
      ContinuousOn (ψ (gs s₁)) (Icc s₁ b₁) → ContinuousOn (ψ (gs s₂)) (Icc s₂ b₂) →
      ψ (gs s₁) b₁ = σ → ψ (gs s₂) b₂ = σ → gs s₁ = gs s₂ := by
    intro σ hσ s₁ s₂ b₁ b₂ h1 h2 hb1 hb2 hc1 hc2 he1 he2
    have l1 := hψlt _ _ (hb1 s₁ le_rfl h1)
    have l2 := hψlt _ _ (hb2 s₂ le_rfl h2)
    rw [abs_lt] at l1 l2
    -- a common value `τ` strictly inside, reached on `[s₁, b₁)` and on `[s₂, b₂)`
    have key : ∃ w₁ w₂, s₁ ≤ w₁ ∧ w₁ < b₁ ∧ s₂ ≤ w₂ ∧ w₂ < b₂ ∧
        ψ (gs s₁) w₁ = ψ (gs s₂) w₂ := by
      rcases hσ with hσ | hσ <;> rw [hσ] at he1 he2
      · set τ := max (ψ (gs s₁) s₁) (ψ (gs s₂) s₂)
        have hτ : τ < δ' := max_lt l1.2 l2.2
        obtain ⟨w₁, hw₁, hψ₁⟩ := intermediate_value_Icc h1.le hc1
          ⟨le_max_left _ _, he1 ▸ hτ.le⟩
        obtain ⟨w₂, hw₂, hψ₂⟩ := intermediate_value_Icc h2.le hc2
          ⟨le_max_right _ _, he2 ▸ hτ.le⟩
        refine ⟨w₁, w₂, hw₁.1, lt_of_le_of_ne hw₁.2 ?_, hw₂.1, lt_of_le_of_ne hw₂.2 ?_,
          hψ₁.trans hψ₂.symm⟩
        · rintro rfl; rw [he1] at hψ₁; exact absurd hψ₁ hτ.ne'
        · rintro rfl; rw [he2] at hψ₂; exact absurd hψ₂ hτ.ne'
      · set τ := min (ψ (gs s₁) s₁) (ψ (gs s₂) s₂)
        have hτ : -δ' < τ := lt_min l1.1 l2.1
        obtain ⟨w₁, hw₁, hψ₁⟩ := intermediate_value_Icc' h1.le hc1
          ⟨he1 ▸ hτ.le, min_le_left _ _⟩
        obtain ⟨w₂, hw₂, hψ₂⟩ := intermediate_value_Icc' h2.le hc2
          ⟨he2 ▸ hτ.le, min_le_right _ _⟩
        refine ⟨w₁, w₂, hw₁.1, lt_of_le_of_ne hw₁.2 ?_, hw₂.1, lt_of_le_of_ne hw₂.2 ?_,
          hψ₁.trans hψ₂.symm⟩
        · rintro rfl; rw [he1] at hψ₁; exact absurd hψ₁ hτ.ne
        · rintro rfl; rw [he2] at hψ₂; exact absurd hψ₂ hτ.ne
    obtain ⟨w₁, w₂, a1, a2, a3, a4, heq⟩ := key
    have r1 := hb1 w₁ a1 a2
    have r2 := hb2 w₂ a3 a4
    have hw := H5 _ _ _ _ r1 r2 heq
    subst hw
    exact H1 _ _ _ r1 r2
  have hfin : ∀ σ, (σ = δ' ∨ σ = -δ') →
      (∀ᶠ s in (𝒱 : Filter ℝ), ∃ b, s < b ∧ (∀ w, s ≤ w → w < b → R (gs s) w) ∧
        ContinuousOn (ψ (gs s)) (Icc s b) ∧ ψ (gs s) b = σ) →
      ∃ g₀, ∀ᶠ s in (𝒱 : Filter ℝ), R g₀ s := by
    intro σ hσ hev
    obtain ⟨s₁, ⟨b₁, h1, hb1, hc1, he1⟩, -⟩ := (hev.and hR).exists
    refine ⟨gs s₁, ?_⟩
    filter_upwards [hev, hR] with s ⟨b, h2, hb2, hc2, he2⟩ hRs
    rwa [← hsame σ hσ s₁ s b₁ b h1 h2 hb1 hb2 hc1 hc2 he1 he2] at hRs
  rcases Ultrafilter.eventually_or.1 h with h | h
  · exact hfin δ' (Or.inl rfl) h
  · exact hfin (-δ') (Or.inr rfl) h

/-- The right-hand side, by the reflection `s ↦ -s`. -/
theorem eventually_eq_of_right (ρ : ℝ → P) (hρ : Continuous ρ) (ℓ κ : P → ℝ) (hℓ : Continuous ℓ)
    (hκ : Continuous κ) (hne : ∀ w, ℓ w = 0 → κ w = 0 → False) {δ δ' : ℝ} (hδ' : 0 < δ')
    (R : Γ → ℝ → Prop)
    (H1 : ∀ g h s, R g s → R h s → g = h)
    (H2 : ∀ g s, R g s → ∀ᶠ t in 𝓝 s, R g t)
    (H3 : ∀ g s, 0 ≤ s → s < δ → (∀ᶠ t in 𝓝[>] s, R g t) →
      |κ (g • ρ s)| < δ' * ℓ (g • ρ s) → R g s)
    (H4 : ∀ g s, R g s → |κ (g • ρ s)| < δ' * ℓ (g • ρ s))
    (H5 : ∀ g h s t, R g s → R h t →
      κ (g • ρ s) / ℓ (g • ρ s) = κ (h • ρ t) / ℓ (h • ρ t) → s = t)
    (𝒱 : Ultrafilter ℝ) (hV : ∀ᶠ s in (𝒱 : Filter ℝ), 0 < s ∧ s < δ ∧ ∃ g, R g s) :
    ∃ g₀, ∀ᶠ s in (𝒱 : Filter ℝ), R g₀ s := by
  obtain ⟨g₀, hg₀⟩ := eventually_eq_of_left (δ := δ) (δ' := δ') (fun s => ρ (-s))
    (hρ.comp continuous_neg) ℓ κ hℓ hκ hne hδ' (fun g s => R g (-s)) (fun g h s => H1 g h (-s))
    (fun g s h => (continuous_neg.tendsto s).eventually (H2 g (-s) h))
    (fun g s hs1 hs2 hl hlt => by
      refine H3 g (-s) (by linarith) (by linarith) ?_ hlt
      have ht : Tendsto Neg.neg (𝓝[>] (-s)) (𝓝[<] s) := by
        refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
        · have := (continuous_neg (G := ℝ)).tendsto (-s)
          rw [neg_neg] at this
          exact this.mono_left nhdsWithin_le_nhds
        · filter_upwards [self_mem_nhdsWithin] with t ht
          exact neg_lt.1 (show -s < t from ht)
      filter_upwards [ht.eventually hl] with t ht
      rwa [neg_neg] at ht)
    (fun g s h => H4 g (-s) h) (fun g h s t hs ht he => neg_inj.1 (H5 g h (-s) (-t) hs ht he))
    (𝒱.map Neg.neg) (by
      rw [Ultrafilter.coe_map, eventually_map]
      filter_upwards [hV] with s ⟨h1, h2, h3⟩
      refine ⟨by linarith, by linarith, ?_⟩
      rwa [neg_neg])
  refine ⟨g₀, ?_⟩
  rw [Ultrafilter.coe_map, eventually_map] at hg₀
  filter_upwards [hg₀] with s hs
  rwa [neg_neg] at hs

end Core

/-! ### Projective coordinates on a half-plane of `ℝ²` -/

section Coordinates

variable (v : Fin (1 + 1) → ℝ)

/-- `⟨v, w⟩`. -/
def lf (w : Fin (1 + 1) → ℝ) : ℝ := w 0 * v 0 + w 1 * v 1

/-- `det(v, w)`. -/
def kf (w : Fin (1 + 1) → ℝ) : ℝ := v 0 * w 1 - v 1 * w 0

/-- The affine line `s ↦ v + s v^⊥` (its ray has projective coordinate `κ/ℓ = s`). -/
def rv (s : ℝ) : Fin (1 + 1) → ℝ := ![v 0 - s * v 1, v 1 + s * v 0]

/-- `|v|²`. -/
def qf : ℝ := v 0 ^ 2 + v 1 ^ 2

variable {v}

theorem qf_pos (hv : v ≠ 0) : 0 < qf v := by
  by_contra h
  push Not at h
  simp only [qf] at h
  have h0 : v 0 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
  have h1 : v 1 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
  exact hv (funext fun i => by fin_cases i <;> simp [h0, h1])

theorem lf_rv (s : ℝ) : lf v (rv v s) = qf v := by
  simp [lf, rv, qf]; ring

theorem kf_rv (s : ℝ) : kf v (rv v s) = s * qf v := by
  simp [kf, rv, qf]; ring

theorem lf_self : lf v v = qf v := by simp [lf, qf]; ring

theorem kf_self : kf v v = 0 := by simp [kf]; ring

theorem lf_smul (c : ℝ) (w : Fin (1 + 1) → ℝ) : lf v (c • w) = c * lf v w := by
  simp [lf]; ring

theorem kf_smul (c : ℝ) (w : Fin (1 + 1) → ℝ) : kf v (c • w) = c * kf v w := by
  simp [kf]; ring

/-- A vector is determined by `⟨v, w⟩` and `det(v, w)`. -/
theorem eq_of_lf_kf (hv : v ≠ 0) {w w' : Fin (1 + 1) → ℝ} (hl : lf v w = lf v w')
    (hk : kf v w = kf v w') : w = w' := by
  have hq := (qf_pos hv).ne'
  have e0 : ∀ u : Fin (1 + 1) → ℝ, u 0 * qf v = lf v u * v 0 - kf v u * v 1 := fun u => by
    simp [lf, kf, qf]; ring
  have e1 : ∀ u : Fin (1 + 1) → ℝ, u 1 * qf v = lf v u * v 1 + kf v u * v 0 := fun u => by
    simp [lf, kf, qf]; ring
  have h0 : w 0 = w' 0 := mul_right_cancel₀ hq (by rw [e0, e0, hl, hk])
  have h1 : w 1 = w' 1 := mul_right_cancel₀ hq (by rw [e1, e1, hl, hk])
  funext i
  fin_cases i
  · exact h0
  · exact h1

theorem eq_zero_of_lf_kf (hv : v ≠ 0) {w : Fin (1 + 1) → ℝ} (hl : lf v w = 0) (hk : kf v w = 0) :
    w = 0 :=
  eq_of_lf_kf hv (by rw [hl]; simp [lf]) (by rw [hk]; simp [kf])

theorem rv_ne_zero (hv : v ≠ 0) (s : ℝ) : rv v s ≠ 0 := fun h => by
  have := lf_rv (v := v) s
  rw [h] at this
  simp [lf] at this
  exact (qf_pos hv).ne this

theorem rv_zero : rv v 0 = v := funext fun i => by fin_cases i <;> simp [rv]

/-- On the half-plane `⟨v, w⟩ > 0`, `w = (⟨v, w⟩/|v|²) · (v + s v^⊥)` with
`s = det(v, w)/⟨v, w⟩`. -/
theorem eq_smul_rv (hv : v ≠ 0) {w : Fin (1 + 1) → ℝ} (hw : lf v w ≠ 0) :
    w = (lf v w / qf v) • rv v (kf v w / lf v w) := by
  have hq := (qf_pos hv).ne'
  refine eq_of_lf_kf hv ?_ ?_
  · rw [lf_smul, lf_rv]; field_simp
  · rw [kf_smul, kf_rv]; field_simp

/-- Two vectors of the half-plane with the same projective coordinate are positively
proportional. -/
theorem eq_smul_of_div_eq (hv : v ≠ 0) {w w' : Fin (1 + 1) → ℝ} (hw : lf v w ≠ 0)
    (h : kf v w / lf v w = kf v w' / lf v w') (hw' : lf v w' ≠ 0) :
    w' = (lf v w' / lf v w) • w := by
  refine eq_of_lf_kf hv ?_ ?_
  · rw [lf_smul]; field_simp
  · rw [kf_smul]
    field_simp at h ⊢
    linarith

theorem div_rv (hv : v ≠ 0) (s : ℝ) : kf v (rv v s) / lf v (rv v s) = s := by
  rw [lf_rv, kf_rv, mul_div_assoc, div_self (qf_pos hv).ne', mul_one]

theorem continuous_lf : Continuous (lf v) := by unfold lf; fun_prop

theorem continuous_kf : Continuous (kf v) := by unfold kf; fun_prop

theorem continuous_rv : Continuous (rv v) := by
  refine continuous_pi fun i => ?_
  fin_cases i
  · simp only [rv, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]; fun_prop
  · simp only [rv, Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]; fun_prop

end Coordinates


/-! ### Rigidity at a point -/

/-- Two transitions holding near the same point are equal (the action is analytic). -/
theorem eq_of_eventually_smul_eq {G X M : Type*} [TopologicalSpace X] [Group G] [MulAction G X]
    [IsAnalyticAction G X] [TopologicalSpace M] {e e' : OpenPartialHomeomorph M X} {x : M}
    (hx : x ∈ e.source) {g h : G} (hg : ∀ᶠ z in 𝓝 x, e' z = g • e z)
    (hh : ∀ᶠ z in 𝓝 x, e' z = h • e z) : g = h := by
  obtain ⟨t, ht, hto, hxt⟩ := mem_nhds_iff.1 (hg.and (hh.and (e.open_source.mem_nhds hx)))
  refine eq_of_eqOn (e.isOpen_image_of_subset_source hto fun z hz => (ht hz).2.2)
    ⟨e x, mem_image_of_mem _ hxt⟩ ?_
  rintro _ ⟨z, hz, rfl⟩
  show g • e z = h • e z
  rw [← (ht hz).1, (ht hz).2.1]

/-! ### Cones of dimension 2: the theorem -/

/-- **Benzécri's dimension 2** (Lean's `ConeBase 1 V`, `V` charted on `ℝ² − {O}`): **the action of
`ℝ₊*` on a Hausdorff affine conical 2-manifold is proper.** -/
theorem properSMul_dim_two {V : Type u} [TopologicalSpace V] [ChartedSpace (RnO (1 + 1)) V]
    [HasGroupoid V (coneGroupoid (1 + 1))] [HasConeCharts (1 + 1) V] [T2Space V] :
    @ProperSMul RPos V _ _ _ (coneMulAction (1 + 1) V) := by
  refine ConeBase.properSMul_of_tendsto (n := 1) fun 𝒰 m' m h => ?_
  have h1 : Tendsto (fun x : RPos × V => posSMul (1 + 1) x.1 x.2) 𝒰 (𝓝 m') :=
    (continuous_fst.tendsto _).comp h
  have h2 : Tendsto (fun x : RPos × V => x.2) 𝒰 (𝓝 m) := (continuous_snd.tendsto _).comp h
  set e := coneChartAt (1 + 1) m with he_def
  set e' := coneChartAt (1 + 1) m' with he'_def
  have he : IsConeChart (1 + 1) e := isConeChart_coneChartAt m
  have hm : m ∈ e.source := mem_coneChartAt_source m
  have he' : IsConeChart (1 + 1) e' := isConeChart_coneChartAt m'
  have hm' : m' ∈ e'.source := mem_coneChartAt_source m'
  set v₀ : Fin (1 + 1) → ℝ := (e m).val with hv₀_def
  set w₀ : Fin (1 + 1) → ℝ := (e' m').val with hw₀_def
  have hv₀ : v₀ ≠ 0 := (e m).val_ne_zero
  have hw₀ : w₀ ≠ 0 := (e' m').val_ne_zero
  -- the parametrisations of the rays through `f(m)` and `f'(m')`
  set ρ : ℝ → RnO (1 + 1) := fun s => Punctured.mk (rv v₀ s) (rv_ne_zero hv₀ s) with hρ_def
  have hρ : Continuous ρ := continuous_induced_rng.2 continuous_rv
  have hρ0 : ρ 0 = e m := Punctured.ext rv_zero
  set ρ' : ℝ → RnO (1 + 1) := fun s => Punctured.mk (rv w₀ s) (rv_ne_zero hw₀ s) with hρ'_def
  have hρ' : Continuous ρ' := continuous_induced_rng.2 continuous_rv
  have hρ'0 : ρ' 0 = e' m' := Punctured.ext rv_zero
  obtain ⟨δ, hδ, hδρ⟩ : ∃ δ > 0, ∀ s, |s| < δ → ρ s ∈ e.target := by
    have hmem : ρ 0 ∈ e.target := by rw [hρ0]; exact e.map_source hm
    obtain ⟨δ, hδ, h⟩ := Metric.eventually_nhds_iff.1
      (hρ.continuousAt.eventually (e.open_target.mem_nhds hmem))
    exact ⟨δ, hδ, fun s hs => h (by rwa [Real.dist_eq, sub_zero])⟩
  obtain ⟨δ', hδ', hδρ'⟩ : ∃ δ' > 0, ∀ s, |s| < δ' → ρ' s ∈ e'.target := by
    have hmem : ρ' 0 ∈ e'.target := by rw [hρ'0]; exact e'.map_source hm'
    obtain ⟨δ', hδ', h⟩ := Metric.eventually_nhds_iff.1
      (hρ'.continuousAt.eventually (e'.open_target.mem_nhds hmem))
    exact ⟨δ', hδ', fun s hs => h (by rwa [Real.dist_eq, sub_zero])⟩
  -- the projective coordinate `κ/ℓ` of the target chart, and the cone `K'` around `f'(m')`
  set ℓ : RnO (1 + 1) → ℝ := fun w => lf w₀ w.val with hℓ_def
  set κ : RnO (1 + 1) → ℝ := fun w => kf w₀ w.val with hκ_def
  have hℓ : Continuous ℓ := continuous_lf.comp Punctured.continuous_val
  have hκ : Continuous κ := continuous_kf.comp Punctured.continuous_val
  have hne : ∀ w, ℓ w = 0 → κ w = 0 → False := fun w h1 h2 =>
    w.val_ne_zero (eq_zero_of_lf_kf hw₀ h1 h2)
  set K' : Set (RnO (1 + 1)) := {w | |κ w| < δ' * ℓ w} with hK'_def
  have hK'open : IsOpen K' := isOpen_lt (continuous_abs.comp hκ) (continuous_const.mul hℓ)
  have hK'smul : ∀ (c : RPos) (w : RnO (1 + 1)), c • w ∈ K' ↔ w ∈ K' := by
    intro c w
    have hc := Punctured.pos c
    simp only [hK'_def, mem_setOf_eq, hκ_def, hℓ_def, Punctured.val_smul_pos, kf_smul, lf_smul,
      abs_mul, abs_of_pos hc]
    constructor
    · intro h'; nlinarith
    · intro h'; nlinarith
  have hK'tgt : K' ⊆ e'.target := by
    intro w hw
    obtain ⟨hl, hs⟩ := abs_div_lt_of hw hδ'
    have hq := qf_pos hw₀
    have hwv := eq_smul_rv hw₀ hl.ne'
    have : w = Punctured.posUnit (ℓ w / qf w₀) (div_pos hl hq) • ρ' (κ w / ℓ w) :=
      Punctured.ext (by rw [Punctured.val_smul_pos, Punctured.coe_posUnit]; exact hwv)
    rw [this]
    exact he'.smul_mem_target (hδρ' _ hs) _
  have hm'K : e' m' ∈ K' := by
    show |kf w₀ w₀| < δ' * lf w₀ w₀
    rw [kf_self, lf_self, abs_zero]
    exact mul_pos hδ' (qf_pos hw₀)
  -- the points `p(s) = f⁻¹(ρ(s))` and the relation « near `p(s)`, `f' = G ∘ f`, `f'(p(s)) ∈ K'` »
  set p : ℝ → V := fun s => e.symm (ρ s) with hp_def
  set R : GUR (1 + 1) → ℝ → Prop := fun G s =>
    |s| < δ ∧ p s ∈ e'.source ∧ e' (p s) ∈ K' ∧ ∀ᶠ z in 𝓝 (p s), e' z = G • e z with hR_def
  have hp_src : ∀ s, |s| < δ → p s ∈ e.source := fun s hs => e.map_target (hδρ s hs)
  have hep : ∀ s, |s| < δ → e (p s) = ρ s := fun s hs => e.right_inv (hδρ s hs)
  have hpcont : ∀ s, |s| < δ → ContinuousAt p s := fun s hs =>
    (e.continuousAt_symm (hδρ s hs)).comp hρ.continuousAt
  have H1 : ∀ G G' s, R G s → R G' s → G = G' := fun G G' s hG hG' =>
    eq_of_eventually_smul_eq (hp_src s hG.1) hG.2.2.2 hG'.2.2.2
  have H4' : ∀ G s, R G s → e' (p s) = G • ρ s := fun G s hG => by
    rw [hG.2.2.2.self_of_nhds, hep s hG.1]
  have H4 : ∀ G s, R G s → |κ (G • ρ s)| < δ' * ℓ (G • ρ s) := fun G s hG => by
    rw [← H4' G s hG]; exact hG.2.2.1
  have H2 : ∀ G s, R G s → ∀ᶠ t in 𝓝 s, R G t := by
    rintro G s ⟨hs, hps, hK, hG⟩
    have hQ : {x : V | x ∈ e'.source ∧ e' x ∈ K' ∧ ∀ᶠ z in 𝓝 x, e' z = G • e z} ∈ 𝓝 (p s) := by
      filter_upwards [e'.open_source.mem_nhds hps,
        (e'.continuousAt hps).preimage_mem_nhds (hK'open.mem_nhds hK),
        eventually_eventually_nhds.2 hG] with x hx1 hx2 hx3
      exact ⟨hx1, hx2, hx3⟩
    filter_upwards [(isOpen_lt continuous_abs continuous_const).mem_nhds hs,
      (hpcont s hs).preimage_mem_nhds hQ] with t ht1 ht2
    exact ⟨ht1, ht2⟩
  have H3 : ∀ G s, |s| < δ → ∀ l : Filter ℝ, l.NeBot → l ≤ 𝓝 s → (∀ᶠ t in l, R G t) →
      |κ (G • ρ s)| < δ' * ℓ (G • ρ s) → R G s := by
    intro G s hs l hl hls hRl hK
    have hT : G • ρ s ∈ e'.target := hK'tgt hK
    have hpl : Tendsto p l (𝓝 (p s)) := (hpcont s hs).tendsto.mono_left hls
    have hq : Tendsto p l (𝓝 (e'.symm (G • ρ s))) := by
      have hc : ContinuousAt (fun t => e'.symm (G • ρ t)) s :=
        ContinuousAt.comp (f := fun t => G • ρ t) (e'.continuousAt_symm hT)
          ((continuous_const_smul G).comp hρ).continuousAt
      refine Tendsto.congr' ?_ (hc.tendsto.mono_left hls)
      filter_upwards [hRl] with t ht
      show e'.symm (G • ρ t) = p t
      rw [← H4' G t ht]
      exact e'.left_inv ht.2.1
    have hps : p s = e'.symm (G • ρ s) := tendsto_nhds_unique hpl hq
    have hps' : p s ∈ e'.source := hps ▸ e'.map_target hT
    have hep' : e' (p s) = G • ρ s := by rw [hps, e'.right_inv hT]
    obtain ⟨G₁, hG₁⟩ := eventually_smul_eq_of_mem_maximalAtlas he.1 he'.1 (hp_src s hs) hps'
    obtain ⟨t, hRt, hG₁t⟩ := (hRl.and (hpl.eventually (eventually_eventually_nhds.2 hG₁))).exists
    have hGG : G = G₁ := eq_of_eventually_smul_eq (hp_src t hRt.1) hRt.2.2.2 hG₁t
    refine ⟨hs, hps', ?_, hGG ▸ hG₁⟩
    show e' (p s) ∈ K'
    rw [hep']
    exact hK
  have H5 : ∀ G G' s t, R G s → R G' t →
      κ (G • ρ s) / ℓ (G • ρ s) = κ (G' • ρ t) / ℓ (G' • ρ t) → s = t := by
    intro G G' s t hs ht heq
    rw [← H4' G s hs, ← H4' G' t ht] at heq
    have ha := (abs_div_lt_of hs.2.2.1 hδ').1
    have hb := (abs_div_lt_of ht.2.2.1 hδ').1
    have hba := eq_smul_of_div_eq hw₀ ha.ne' heq hb.ne'
    set c := Punctured.posUnit (ℓ (e' (p t)) / ℓ (e' (p s))) (div_pos hb ha) with hc_def
    have hbc : e' (p t) = c • e' (p s) :=
      Punctured.ext (by rw [Punctured.val_smul_pos, Punctured.coe_posUnit]; exact hba)
    have hpt : p t = posSMul (1 + 1) c (p s) := by
      calc p t = e'.symm (e' (p t)) := (e'.left_inv ht.2.1).symm
        _ = e'.symm (c • e' (p s)) := by rw [hbc]
        _ = posSMul (1 + 1) c (e'.symm (e' (p s))) := he'.symm_smul (e'.map_source hs.2.1) c
        _ = posSMul (1 + 1) c (p s) := by rw [e'.left_inv hs.2.1]
    have hρt : ρ t = c • ρ s := by
      rw [← hep t ht.1, hpt, he.map_smul (hp_src s hs.1), hep s hs.1]
    have key := congrArg (fun w : RnO (1 + 1) => kf v₀ w.val / lf v₀ w.val) hρt
    have hc0 : ((c : ℝˣ) : ℝ) ≠ 0 := (Punctured.pos c).ne'
    simp only [hρ_def, Punctured.val_mk, Punctured.val_smul_pos, kf_smul, lf_smul] at key
    rw [mul_div_mul_left _ _ hc0, div_rv hv₀, div_rv hv₀] at key
    exact key.symm
  -- along `𝒰`: the points `m_i` in the domain of both charts, with coordinate `u(m_i)`
  set D : Set (RnO (1 + 1)) := {v | |kf v₀ v.val| < δ * lf v₀ v.val} with hD_def
  have hDopen : IsOpen D := isOpen_lt (continuous_abs.comp (continuous_kf.comp
    Punctured.continuous_val)) (continuous_const.mul (continuous_lf.comp Punctured.continuous_val))
  have hmD : e m ∈ D := by
    show |kf v₀ v₀| < δ * lf v₀ v₀
    rw [kf_self, lf_self, abs_zero]
    exact mul_pos hδ (qf_pos hv₀)
  set u : V → ℝ := fun y => kf v₀ (e y).val / lf v₀ (e y).val with hu_def
  have hgood : ∀ᶠ x in (𝒰 : Filter (RPos × V)),
      x.2 ∈ e.source ∧ x.2 ∈ e'.source ∧ e' x.2 ∈ K' ∧ e x.2 ∈ D := by
    filter_upwards [h2.eventually (e.open_source.mem_nhds hm),
      h1.eventually (e'.open_source.mem_nhds hm'),
      h1.eventually ((e'.continuousAt hm').preimage_mem_nhds (hK'open.mem_nhds hm'K)),
      h2.eventually ((e.continuousAt hm).preimage_mem_nhds (hDopen.mem_nhds hmD))]
      with x hx1 hx2 hx3 hx4
    have hy' : x.2 ∈ e'.source := (he'.smul_mem_source_iff x.1).1 hx2
    refine ⟨hx1, hy', ?_, hx4⟩
    have h3 : e' (posSMul (1 + 1) x.1 x.2) ∈ K' := hx3
    rwa [he'.map_smul hy' x.1, hK'smul] at h3
  -- a point `y` is the homothetic `c_y · p(u(y))` of a point of the parametrised ray
  have hdecomp : ∀ y, y ∈ e.source → e y ∈ D → ∃ c : RPos, (|u y| < δ) ∧
      y = posSMul (1 + 1) c (p (u y)) ∧ e y = c • ρ (u y) := by
    intro y hy hD
    obtain ⟨hl, hs⟩ := abs_div_lt_of hD hδ
    refine ⟨Punctured.posUnit (lf v₀ (e y).val / qf v₀) (div_pos hl (qf_pos hv₀)), hs, ?_, ?_⟩
    · calc y = e.symm (e y) := (e.left_inv hy).symm
        _ = e.symm (Punctured.posUnit (lf v₀ (e y).val / qf v₀) (div_pos hl (qf_pos hv₀)) •
              ρ (u y)) := by
          congr 1
          exact Punctured.ext (by
            rw [Punctured.val_smul_pos, Punctured.coe_posUnit]; exact eq_smul_rv hv₀ hl.ne')
        _ = _ := he.symm_smul (hδρ _ hs) _
    · exact Punctured.ext (by
        rw [Punctured.val_smul_pos, Punctured.coe_posUnit]; exact eq_smul_rv hv₀ hl.ne')
  have hRex : ∀ᶠ x in (𝒰 : Filter (RPos × V)), |u x.2| < δ ∧ ∃ G, R G (u x.2) := by
    filter_upwards [hgood] with x ⟨hx1, hx2, hx3, hx4⟩
    obtain ⟨c, hs, hy, -⟩ := hdecomp x.2 hx1 hx4
    have hpu : p (u x.2) = posSMul (1 + 1) c⁻¹ x.2 := by
      conv_rhs => rw [hy]
      rw [← posSMul_mul, inv_mul_cancel, posSMul_one]
    have hps' : p (u x.2) ∈ e'.source := by rw [hpu]; exact he'.smul_mem_source hx2 _
    obtain ⟨G, hG⟩ := eventually_smul_eq_of_mem_maximalAtlas he.1 he'.1 (hp_src _ hs) hps'
    refine ⟨hs, G, hs, hps', ?_, hG⟩
    rw [hpu, he'.map_smul hx2, hK'smul]
    exact hx3
  -- the ultrafilter of the coordinates, and the constant transition
  set 𝒱 : Ultrafilter ℝ := 𝒰.map fun x => u x.2 with h𝒱
  have hev : ∀ {P : ℝ → Prop}, (∀ᶠ s in (𝒱 : Filter ℝ), P s) ↔
      ∀ᶠ x in (𝒰 : Filter (RPos × V)), P (u x.2) := by
    intro P
    rw [h𝒱, Ultrafilter.coe_map, eventually_map]
  have hV : ∀ᶠ s in (𝒱 : Filter ℝ), |s| < δ ∧ ∃ G, R G s := hev.2 hRex
  obtain ⟨G₀, hG₀⟩ : ∃ G₀, ∀ᶠ s in (𝒱 : Filter ℝ), R G₀ s := by
    have htri : ∀ᶠ s in (𝒱 : Filter ℝ), s < 0 ∨ s = 0 ∨ 0 < s :=
      Eventually.of_forall fun s => lt_trichotomy s 0
    rcases Ultrafilter.eventually_or.1 htri with hlt | h'
    · refine eventually_eq_of_left (δ := δ) ρ hρ ℓ κ hℓ hκ hne hδ' R H1 H2
        (fun G s hs1 hs2 hl hK => H3 G s (abs_lt.2 ⟨hs1, by linarith⟩) _ inferInstance
          nhdsWithin_le_nhds hl hK) H4 H5 𝒱 ?_
      filter_upwards [hV, hlt] with s ⟨hs, hex⟩ hs0
      exact ⟨(abs_lt.1 hs).1, hs0, hex⟩
    rcases Ultrafilter.eventually_or.1 h' with heq | hgt
    · obtain ⟨s₀, hs₀, ⟨-, G₀, hG₀⟩⟩ := (heq.and hV).exists
      refine ⟨G₀, ?_⟩
      filter_upwards [heq] with s hs
      rw [hs, ← hs₀]
      exact hG₀
    · refine eventually_eq_of_right (δ := δ) ρ hρ ℓ κ hℓ hκ hne hδ' R H1 H2
        (fun G s hs1 hs2 hl hK => H3 G s (abs_lt.2 ⟨by linarith, hs2⟩) _ inferInstance
          nhdsWithin_le_nhds hl hK) H4 H5 𝒱 ?_
      filter_upwards [hV, hgt] with s ⟨hs, hex⟩ hs0
      exact ⟨hs0, (abs_lt.1 hs).2, hex⟩
  -- along `𝒰`, `f'(m_i) = G₀ f(m_i)`, so `‖f'(m_i)‖ → ‖G₀ f(m)‖`
  have hrad : Tendsto (fun x : RPos × V => Punctured.radius (e' x.2)) 𝒰
      (𝓝 (Punctured.radius (G₀ • e m))) := by
    have hc : ContinuousAt (fun y => Punctured.radius (G₀ • e y)) m :=
      (Punctured.continuous_radius.continuousAt.comp
        (continuous_const_smul G₀).continuousAt).comp (e.continuousAt hm)
    refine Tendsto.congr' ?_ (hc.tendsto.comp h2)
    filter_upwards [hgood, hev.1 hG₀] with x ⟨hx1, hx2, _, hx4⟩ hR₀
    obtain ⟨c, -, hy, hey⟩ := hdecomp x.2 hx1 hx4
    show Punctured.radius (G₀ • e x.2) = Punctured.radius (e' x.2)
    congr 1
    calc G₀ • e x.2 = G₀ • (c • ρ (u x.2)) := by rw [hey]
      _ = c • (G₀ • ρ (u x.2)) := smul_comm _ _ _
      _ = c • e' (p (u x.2)) := by rw [H4' G₀ _ hR₀]
      _ = e' (posSMul (1 + 1) c (p (u x.2))) := (he'.map_smul hR₀.2.1 c).symm
      _ = e' x.2 := by rw [← hy]
  exact ⟨_, ConeBase.tendsto_fst_of_tendsto_radius (n := 1) he' hm' h1 hrad⟩


/-! ### Cones of dimension 1 -/

/-- `Fin (0 + 1)` has a unique element (a local instance: `Fin 1`'s, which instance search does not
find through `0 + 1`). -/
abbrev uniqueFinZeroAddOne : Unique (Fin (0 + 1)) := inferInstanceAs (Unique (Fin 1))

attribute [local instance] uniqueFinZeroAddOne

/-- The sup norm on `ℝ¹` is the absolute value of the coordinate. -/
theorem norm_fin_one (w : Fin (0 + 1) → ℝ) (d : Fin (0 + 1)) : ‖w‖ = |w d| := by
  refine le_antisymm ((pi_norm_le_iff_of_nonneg (abs_nonneg _)).2 fun i => ?_) ?_
  · rw [Subsingleton.elim i d, Real.norm_eq_abs]
  · rw [← Real.norm_eq_abs]; exact norm_le_pi_norm w d

/-- **`GU(1) = {±1}` acts by isometries** of `ℝ¹ − {O}`. -/
theorem norm_smul_GU_one (g : GUR (0 + 1)) (v : RnO (0 + 1)) : ‖(g • v).val‖ = ‖v.val‖ := by
  set f : (Fin (0 + 1) → ℝ) ≃ₗ[ℝ] (Fin (0 + 1) → ℝ) := (g : GLR (0 + 1))
  obtain ⟨d, hdet⟩ : ∃ d : Fin (0 + 1), |f (Pi.single d 1) d| = 1 := by
    have := g.2
    rw [mem_GU, LinearEquiv.coe_det, ← LinearMap.det_toMatrix', Matrix.det_unique,
      LinearMap.toMatrix'_apply] at this
    exact ⟨_, this⟩
  have hv : v.val = v.val d • Pi.single d 1 := funext fun i => by
    rw [Subsingleton.elim i d, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
  rw [Punctured.val_smul_sub, norm_fin_one _ d, norm_fin_one _ d]
  show |f v.val d| = |v.val d|
  rw [hv, map_smul, Pi.smul_apply, smul_eq_mul, abs_mul, hdet, mul_one]
  simp

/-- **Benzécri's dimension 1** (Lean's `ConeBase 0 V`): **the action of `ℝ₊*` on a Hausdorff affine
conical 1-manifold is proper** (the transitions, in `GU(1) = {±1}`, preserve `‖·‖`). -/
theorem properSMul_dim_one {V : Type u} [TopologicalSpace V] [ChartedSpace (RnO (0 + 1)) V]
    [HasGroupoid V (coneGroupoid (0 + 1))] [HasConeCharts (0 + 1) V] [T2Space V] :
    @ProperSMul RPos V _ _ _ (coneMulAction (0 + 1) V) := by
  refine ConeBase.properSMul_of_tendsto (n := 0) fun 𝒰 m' m h => ?_
  have h1 : Tendsto (fun x : RPos × V => posSMul (0 + 1) x.1 x.2) 𝒰 (𝓝 m') :=
    (continuous_fst.tendsto _).comp h
  have h2 : Tendsto (fun x : RPos × V => x.2) 𝒰 (𝓝 m) := (continuous_snd.tendsto _).comp h
  set e := coneChartAt (0 + 1) m
  set e' := coneChartAt (0 + 1) m'
  have he : IsConeChart (0 + 1) e := isConeChart_coneChartAt m
  have hm : m ∈ e.source := mem_coneChartAt_source m
  have he' : IsConeChart (0 + 1) e' := isConeChart_coneChartAt m'
  have hm' : m' ∈ e'.source := mem_coneChartAt_source m'
  have hr : Tendsto (fun x : RPos × V => Punctured.radius (e' x.2)) 𝒰
      (𝓝 (Punctured.radius (e m))) := by
    refine Tendsto.congr' ?_
      (((Punctured.continuous_radius.continuousAt).comp (e.continuousAt hm)).tendsto.comp h2)
    filter_upwards [h2.eventually (e.open_source.mem_nhds hm),
      h1.eventually (e'.open_source.mem_nhds hm')] with x hx1 hx2
    have hy' : x.2 ∈ e'.source := (he'.smul_mem_source_iff x.1).1 hx2
    obtain ⟨g, hg⟩ := eventually_smul_eq_of_mem_maximalAtlas he.1 he'.1 hx1 hy'
    show Punctured.radius (e x.2) = Punctured.radius (e' x.2)
    rw [hg.self_of_nhds]
    exact Subtype.ext (Units.ext (by
      simp only [Punctured.coe_radius]; exact (norm_smul_GU_one g _).symm))
  exact ⟨_, ConeBase.tendsto_fst_of_tendsto_radius (n := 0) he' hm' h1 hr⟩

/-! ### The theorem: `n ≤ 2` -/

/-- **DEC-122, the `n ≤ 2` theorem: in Benzécri's dimension `n ≤ 2`, the action of `ℝ₊*` on a
Hausdorff affine conical manifold is proper** (Lean's base dimension `n ≤ 1`; for Benzécri's
`n = 0`, `ℝ⁰ − {O}` is empty and there is nothing to prove). -/
theorem properSMul_of_le_one {n : ℕ} (hn : n ≤ 1) {V : Type u} [TopologicalSpace V]
    [ChartedSpace (RnO (n + 1)) V] [HasGroupoid V (coneGroupoid (n + 1))]
    [HasConeCharts (n + 1) V] [T2Space V] :
    @ProperSMul RPos V _ _ _ (coneMulAction (n + 1) V) := by
  obtain rfl | rfl : n = 0 ∨ n = 1 := by omega
  · exact properSMul_dim_one
  · exact properSMul_dim_two

/-- **DEC-122, the `n ≤ 2` theorem: for an affine conical manifold of dimension `n ≤ 2`, `V`
Hausdorff implies the base `B = V/ℝ⁺` Hausdorff.** False for every `n ≥ 3`
(`Cone/Counterexample`). -/
theorem t2Space_coneBase_of_le_one {n : ℕ} (hn : n ≤ 1) {V : Type u} [TopologicalSpace V]
    [ChartedSpace (RnO (n + 1)) V] [HasGroupoid V (coneGroupoid (n + 1))]
    [HasConeCharts (n + 1) V] [T2Space V] : T2Space (ConeBase n V) :=
  ConeBase.t2Space_of_properSMul (properSMul_of_le_one hn)

end LowDim
end Benzecri
