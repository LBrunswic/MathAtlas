import CausalScaffold.Flat.Develop
import CausalScaffold.Flat.Bieberbach
import CausalScaffold.Flat.Examples
import Mathlib.Analysis.Normed.Affine.MazurUlam

/-!
# `CausalScaffold.Flat.Abel` — Barbot's Corollary 8.4 (`bcor:abel`): false as printed, and repaired

T. Barbot, *Globally hyperbolic flat space-times* (`papers/barbot`, arXiv math/0402257), §8,
lines of the **labelled** `papers/barbot/legacy/labeled/GHFspace.tex`. Package WP-35a-Abel.
**No label is marked**: the printed statement is false (DEC-27's rule, adopted in
`docs/BARBOT.md`), so the row is `partial`.

* `bcor:abel` — `GHFspace.tex:2295` (Cor 8.4, l.2292–2305), partial:
  - **refuted as printed**, with no `sorry`, in every dimension `d ≥ 3` (Barbot's `n ≥ 4`)
    unconditionally (`U` a line or larger), and at `d = 2` (Barbot's `n = 3`) under the reading
    of a point as a spacelike affine subspace:
    `not_bcorAbelPrinted` (the printed statement, kept as the `Prop` `BcorAbelPrinted`, kb/0022),
    `not_bcorAbelStepPrinted` (the proof's step "the action on `U` is free"), the witness
    packaged in `bcor_abel_counterexample`;
  - **a true repaired form**, `bcor_abel`: the printed hypotheses **plus a `Γ`-invariant
    timelike direction `Δ`** (the hypothesis the printed proof silently uses), conclusion
    "virtually `ℤᵐ`, `m ≤ dim U`", conditional only on the external `BieberbachI` in dimension
    `dim U` (DEC-36); the proof's first step under that hypothesis, unconditional:
    `abel_free_of_fix`, `abel_proper_of_fix` (`Γ` acts freely and properly on all of `𝐌ⁿ`);
    its virtual form `bcor_abel_virtual` (only a finite-index `Γ₀ ≤ Γ` preserves `Δ`);
  - **the form its use at [10.M] needs**, `bcor_abel_twoNull`: `U` plus **two distinct null
    directions** preserved; `Γ ↪ Isom(ℝ × U)` discretely, virtually `ℤᵐ`, `m ≤ dim U + 1`
    (external `BieberbachI (ℝ × ℝ^{dim U})`); its virtual form `bcor_abel_twoNull_virtual`;
  - **the unified form**, `bcor_abel_unified`: a finite-index `Γ₀ ≤ Γ` preserves a timelike
    direction **or** two distinct null directions; virtually `ℤᵐ`, `m ≤ dim U + 1`. No claim is
    made that this is the strongest true form.

> If $\Gamma$ preserves a spacelike affine subspace ${\bf U}$, then
> $\Gamma$ contains as a finite index subgroup a free abelian group of finite rank. (l.2295–2296)
>
> Apply proposition \ref{project} with $\Delta \subset {\bf U}^{\perp}$.
> The action of $\Gamma$ on $\pi({\bf U})$ has to be free and properly
> discontinuous, and the same is true for the
> action on ${\bf U}$. But this action
> is isometric for the induced euclidean metric on ${\bf U}$;
> the lemma then follows from Bieberbach's Theorem. (l.2300–2305)

**The counterexample** (`bcor_abel_counterexample`, `d = n + 2`): `Γ₄ = gamma4 n`, the image of
the level-4 congruence subgroup `Γ(4) ⊂ SL(2, ℤ)` acting on `(t, x₀, x₁)` through
`X = [[t + x₀, x₁], [x₁, t − x₀]] ↦ M X Mᵀ` (`sl2Lin`) and trivially on the other coordinates.
With `Σ` the hyperboloid, `CCAction Γ₄ Σ` holds — (CC′), invariance, freeness (`gamma4_free`:
a fixed point in `ℍ²` forces `|tr M| < 2`, and `tr M ≡ 2 mod 4`), proper discontinuity
(`gamma4_proper`: integer entries bounded on a compact set) — so `Γ₄` meets §8's standing
hypotheses in the DEC-35 reading; the spacetime `Γ₄ \ {t > ‖x‖}` itself is not constructed
(DEC-35's bridge runs from the paper's hypotheses to `CCAction`, not back). `Γ₄` fixes **pointwise** the
spacelike `U = {t = x₀ = x₁ = 0}` (a point for `d = 2`, a line for `d = 3`, …), and no
finite-index subgroup of it is commutative (`gamma4_not_virtually_comm`: `uᵏ lˡ ≠ lˡ uᵏ` for the
two unipotent generators). The failing step is "the action of Γ on π(U) has to be free and
properly discontinuous" (l.2300–2301): `π` is `Γ`-equivariant only if `Δ` is `Γ`-invariant, and
no nontrivial element of `Γ₄` preserves a timelike direction (`gamma4_not_fix_timelike`).

**Dimension (kb/0024).** Barbot's `𝐌ⁿ` has total dimension `n`; `Minkowski d` has `d` spatial
dimensions: Barbot's `n` is `d + 1`. The counterexample lives in `Minkowski (n + 2)`.

## Hypothesis checklist (`bcor_abel`)

| paper hypothesis | here |
|---|---|
| §8's setting: `S` complete, `Γ = π₁(S)` acting on `S̃` (l.2212–2275) | ✓ carried in the DEC-35 reading `CCAction Γ S` (as `Flat/Develop`, `Flat/Loxodromic`) |
| `Γ` preserves a spacelike affine subspace `U` (l.2295) | ✓ carried: `IsSpacelikeAffine U` (every nonzero direction vector spacelike; a point qualifies), `U` nonempty and `Γ`-invariant |
| `Δ ⊂ U^⊥` timelike (l.2300) | ⚠ **strengthened**: `Δ = ℝv` is asked `Γ`-invariant (`∀ γ, L(γ) v ∈ ℝ v`). Some strengthening is necessary (`not_bcorAbelPrinted`); `Γ`-invariance of a timelike `Δ` is one sufficient strengthening (virtually: `bcor_abel_virtual`), two invariant null directions another (`bcor_abel_twoNull`, `bcor_abel_unified`). ⚠ weakened: `Δ ⊥ U` is not used |
| Bieberbach's Theorem (l.2305) | carried as the external `BieberbachI (ℝ^{dim U})` (DEC-36) |

## SCOPE (disclosed)

* **No `sorry`.** `bcor_abel` rests on `BieberbachI`, a named `Prop` (not an axiom), which is
  proved in dimension `≤ 1` (`bieberbachI_of_finrank_le_one`, `Flat/Bieberbach`).
* The counterexample is stated in the DEC-35 reading `CCAction` (the standing hypotheses of §8 in
  `𝐌ⁿ`); the flat spacetime `Γ₄ \ {t > ‖x‖}` itself and its `DevelopsCC` are not built.
  `Γ₄ \ Σ` is a complete hyperbolic surface of finite area (times `ℝⁿ`), not compact: the
  counterexample is Cauchy-complete, not Cauchy-compact. Whether Cor 8.4 holds for Cauchy-compact
  `M` is not examined (a cocompact Fuchsian group gives the same failure; not formalized).
* `d ≤ 1` (Barbot's `n ≤ 2`) is not examined.
* Non-vacuity of `bcor_abel`'s hypotheses with a nontrivial group: `bcor_abel_hypotheses_witness`
  (`ℤᵈ` by horizontal translations on `{t = 0}`, `U = {t = 0}`, `Δ = ℝ(1, 0)`).
* The use at [10.M] (l.3326, "As in corollary \ref{abel}, we see that the action on
  `π_P^{-1}(0)` is free and properly discontinuous") has `L(Γ)` preserving two null directions,
  not a timelike one; there the claim is false too (a pure boost fixes `P` pointwise; not
  formalized) and `bcor_abel` does not apply: `bcor_abel_twoNull` is the replacement, the boost
  parameter `log λ(γ)` restoring injectivity. The use at Prop 10.4 (l.3355–3356) is not served by
  either form (there `L(Γ)` is non-elementary); `Flat/Loxodromic` routes around it.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Barbot campaign,
WP-35a-Abel (2026-11-01).
-/

namespace Causal.Flat

open Module Set Metric
open scoped Pointwise

/-! ### 1. `SL(2, ℝ)` acting on the first two spatial coordinates -/

section SL2

variable {n : ℕ}

/-- The time coordinate `t = −⟨x | T⟩`. -/
noncomputable abbrev abelCoordT (x : Minkowski (n + 2)) : ℝ := -minkB x (timeUnit (n + 2))
/-- The first spatial coordinate `x₀ = ⟨x | S₀⟩`. -/
noncomputable abbrev abelCoord0 (x : Minkowski (n + 2)) : ℝ := minkB x (spaceUnit (0 : Fin (n + 2)))
/-- The second spatial coordinate `x₁ = ⟨x | S₁⟩`. -/
noncomputable abbrev abelCoord1 (x : Minkowski (n + 2)) : ℝ := minkB x (spaceUnit (1 : Fin (n + 2)))

/-- New time coordinate under `M = [[p, q], [r, s]]` acting on `X = [[t + x₀, x₁], [x₁, t − x₀]]`
by `X ↦ M X Mᵀ`: half the trace. -/
noncomputable def sl2T (p q r s t x0 x1 : ℝ) : ℝ :=
  ((p ^ 2 + r ^ 2) * (t + x0) + 2 * (p * q + r * s) * x1 + (q ^ 2 + s ^ 2) * (t - x0)) / 2

/-- New `x₀`: half the difference of the diagonal entries of `M X Mᵀ`. -/
noncomputable def sl2X0 (p q r s t x0 x1 : ℝ) : ℝ :=
  ((p ^ 2 - r ^ 2) * (t + x0) + 2 * (p * q - r * s) * x1 + (q ^ 2 - s ^ 2) * (t - x0)) / 2

/-- New `x₁`: the off-diagonal entry of `M X Mᵀ`. -/
noncomputable def sl2X1 (p q r s t x0 x1 : ℝ) : ℝ :=
  p * r * (t + x0) + (p * s + q * r) * x1 + q * s * (t - x0)

private theorem minkB_T_T : minkB (timeUnit (n + 2)) (timeUnit (n + 2)) = -1 := by
  rw [← minkQ_eq_minkB, minkQ_timeUnit]

private theorem minkB_S_S (i : Fin (n + 2)) : minkB (spaceUnit i) (spaceUnit i) = 1 := by
  rw [← minkQ_eq_minkB, minkQ_spaceUnit]

private theorem minkB_S_T (i : Fin (n + 2)) : minkB (spaceUnit i) (timeUnit (n + 2)) = 0 := by
  rw [minkB_comm, minkB_timeUnit_spaceUnit]

private theorem minkB_T_S (i : Fin (n + 2)) : minkB (timeUnit (n + 2)) (spaceUnit i) = 0 :=
  minkB_timeUnit_spaceUnit i

private theorem minkB_S0_S1 :
    minkB (spaceUnit (0 : Fin (n + 2))) (spaceUnit (1 : Fin (n + 2))) = 0 :=
  minkB_spaceUnit_spaceUnit (by simp)

private theorem minkB_S1_S0 :
    minkB (spaceUnit (1 : Fin (n + 2))) (spaceUnit (0 : Fin (n + 2))) = 0 :=
  minkB_spaceUnit_spaceUnit (by simp)

/-- **`M = [[p, q], [r, s]]` acting on `𝐌ⁿ`** through the first two spatial coordinates: the
point `(t, x₀, x₁, …)` is read as the symmetric matrix `X = [[t + x₀, x₁], [x₁, t − x₀]]`
(`det X = t² − x₀² − x₁²`), sent to `M X Mᵀ`; the other coordinates are fixed. -/
noncomputable def sl2Lin (p q r s : ℝ) : Minkowski (n + 2) →ₗ[ℝ] Minkowski (n + 2) where
  toFun x := x + (sl2T p q r s (abelCoordT x) (abelCoord0 x) (abelCoord1 x) - abelCoordT x) • timeUnit (n + 2) +
    (sl2X0 p q r s (abelCoordT x) (abelCoord0 x) (abelCoord1 x) - abelCoord0 x) • spaceUnit (0 : Fin (n + 2)) +
    (sl2X1 p q r s (abelCoordT x) (abelCoord0 x) (abelCoord1 x) - abelCoord1 x) • spaceUnit (1 : Fin (n + 2))
  map_add' x y := by
    simp only [abelCoordT, abelCoord0, abelCoord1, minkB_add_left, sl2T, sl2X0, sl2X1]; module
  map_smul' c x := by
    simp only [abelCoordT, abelCoord0, abelCoord1, minkB_smul_left, sl2T, sl2X0, sl2X1, RingHom.id_apply]; module

theorem sl2Lin_apply (p q r s : ℝ) (x : Minkowski (n + 2)) : sl2Lin p q r s x =
    x + (sl2T p q r s (abelCoordT x) (abelCoord0 x) (abelCoord1 x) - abelCoordT x) • timeUnit (n + 2) +
    (sl2X0 p q r s (abelCoordT x) (abelCoord0 x) (abelCoord1 x) - abelCoord0 x) • spaceUnit (0 : Fin (n + 2)) +
    (sl2X1 p q r s (abelCoordT x) (abelCoord0 x) (abelCoord1 x) - abelCoord1 x) • spaceUnit (1 : Fin (n + 2)) := rfl

theorem cT_sl2Lin (p q r s : ℝ) (x : Minkowski (n + 2)) :
    abelCoordT (sl2Lin p q r s x) = sl2T p q r s (abelCoordT x) (abelCoord0 x) (abelCoord1 x) := by
  simp only [sl2Lin_apply, abelCoordT, minkB_add_left, minkB_smul_left, minkB_T_T, minkB_S_T]; ring

theorem c0_sl2Lin (p q r s : ℝ) (x : Minkowski (n + 2)) :
    abelCoord0 (sl2Lin p q r s x) = sl2X0 p q r s (abelCoordT x) (abelCoord0 x) (abelCoord1 x) := by
  simp only [sl2Lin_apply, abelCoord0, abelCoordT, minkB_add_left, minkB_smul_left, minkB_timeUnit_spaceUnit,
    minkB_S_S, minkB_S1_S0]; ring

theorem c1_sl2Lin (p q r s : ℝ) (x : Minkowski (n + 2)) :
    abelCoord1 (sl2Lin p q r s x) = sl2X1 p q r s (abelCoordT x) (abelCoord0 x) (abelCoord1 x) := by
  simp only [sl2Lin_apply, abelCoord1, abelCoordT, minkB_add_left, minkB_smul_left, minkB_timeUnit_spaceUnit,
    minkB_S_S, minkB_S0_S1]; ring

/-- `M ↦ (X ↦ M X Mᵀ)` is multiplicative. -/
theorem sl2Lin_comp (p q r s p' q' r' s' : ℝ) :
    sl2Lin (n := n) p q r s ∘ₗ sl2Lin p' q' r' s' =
      sl2Lin (p * p' + q * r') (p * q' + q * s') (r * p' + s * r') (r * q' + s * s') := by
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.comp_apply, sl2Lin_apply p q r s, cT_sl2Lin, c0_sl2Lin, c1_sl2Lin,
    sl2Lin_apply p' q' r' s', sl2Lin_apply]
  simp only [sl2T, sl2X0, sl2X1]
  module

theorem sl2Lin_one : sl2Lin (n := n) 1 0 0 1 = LinearMap.id := by
  refine LinearMap.ext fun x => ?_
  rw [sl2Lin_apply]
  simp only [sl2T, sl2X0, sl2X1, LinearMap.id_apply]
  module

/-- **`det (M X Mᵀ) = det X` when `det M = 1`**: the action preserves `minkQ`. -/
theorem minkQ_sl2Lin {p q r s : ℝ} (h : p * s - q * r = 1) (x : Minkowski (n + 2)) :
    minkQ (sl2Lin p q r s x) = minkQ x := by
  rw [sl2Lin_apply, minkQ_add, minkQ_add, minkQ_add]
  simp only [minkB_add_left, minkB_smul_left, minkB_smul_right, minkQ_smul,
    minkQ_timeUnit, minkQ_spaceUnit, minkB_timeUnit_spaceUnit, minkB_S0_S1, sl2T, sl2X0, sl2X1]
  linear_combination (-(p * s - q * r + 1) *
    (minkB x (timeUnit (n + 2)) ^ 2 - abelCoord0 x ^ 2 - abelCoord1 x ^ 2)) * h

theorem abelCoordT_eq (x : Minkowski (n + 2)) : abelCoordT x = x.1 := by
  simp [abelCoordT, minkB, timeUnit]

/-- `sl2Lin M` with inverse `sl2Lin M⁻¹`, for `det M = 1`. -/
noncomputable def sl2Equiv {p q r s : ℝ} (h : p * s - q * r = 1) :
    Minkowski (n + 2) ≃ₗ[ℝ] Minkowski (n + 2) :=
  LinearEquiv.ofLinear (sl2Lin p q r s) (sl2Lin s (-q) (-r) p)
    (by
      rw [sl2Lin_comp, show p * s + q * -r = 1 by linarith, show p * -q + q * p = 0 by ring,
        show r * s + s * -r = 0 by ring, show r * -q + s * p = 1 by linarith, sl2Lin_one])
    (by
      rw [sl2Lin_comp, show s * p + -q * r = 1 by linarith, show s * q + -q * s = 0 by ring,
        show -r * p + p * r = 0 by ring, show -r * q + p * s = 1 by linarith, sl2Lin_one])

theorem sl2Equiv_apply {p q r s : ℝ} (h : p * s - q * r = 1) (x : Minkowski (n + 2)) :
    sl2Equiv h x = sl2Lin p q r s x := rfl

/-- The time unit is sent into the future. -/
theorem fst_sl2Lin_timeUnit {p q r s : ℝ} (h : p * s - q * r = 1) :
    0 < (sl2Lin (n := n) p q r s (timeUnit (n + 2))).1 := by
  rw [← abelCoordT_eq, cT_sl2Lin]
  have h1 : abelCoordT (timeUnit (n + 2)) = 1 := by rw [abelCoordT_eq]; rfl
  have h2 : abelCoord0 (timeUnit (n + 2)) = 0 := minkB_T_S 0
  have h3 : abelCoord1 (timeUnit (n + 2)) = 0 := minkB_T_S 1
  rw [h1, h2, h3, sl2T]
  nlinarith [sq_nonneg (p - s), sq_nonneg (q + r), sq_nonneg p, sq_nonneg q, sq_nonneg r,
    sq_nonneg s]

/-- **A unipotent `[[1, σ], [0, 1]]` acts by an element of `SO₀(1, d)`.** -/
theorem sl2Equiv_upper_mem (σ : ℝ) :
    sl2Equiv (n := n) (show (1 : ℝ) * 1 - σ * 0 = 1 by ring) ∈ lorentz (n + 2) := by
  refine mem_lorentz_of (minkQ_sl2Lin (by ring)) (fst_sl2Lin_timeUnit (by ring)) ?_
  refine det_eq_one_of_eq_sq (B := sl2Lin 1 (σ / 2) 0 1) (minkQ_sl2Lin (by ring)) ?_
  show sl2Lin 1 σ 0 1 = _
  rw [sl2Lin_comp]
  congr 1 <;> ring

/-- **A unipotent `[[1, 0], [σ, 1]]` acts by an element of `SO₀(1, d)`.** -/
theorem sl2Equiv_lower_mem (σ : ℝ) :
    sl2Equiv (n := n) (show (1 : ℝ) * 1 - 0 * σ = 1 by ring) ∈ lorentz (n + 2) := by
  refine mem_lorentz_of (minkQ_sl2Lin (by ring)) (fst_sl2Lin_timeUnit (by ring)) ?_
  refine det_eq_one_of_eq_sq (B := sl2Lin 1 0 (σ / 2) 1) (minkQ_sl2Lin (by ring)) ?_
  show sl2Lin 1 0 σ 1 = _
  rw [sl2Lin_comp]
  congr 1 <;> ring

/-- The isometry `x ↦ [[1, σ], [0, 1]] · x`. -/
noncomputable def upperIsom (σ : ℝ) : isom (n + 2) :=
  ⟨(sl2Equiv (n := n) (show (1 : ℝ) * 1 - σ * 0 = 1 by ring)).toAffineEquiv,
    mem_isom_iff.2 (sl2Equiv_upper_mem σ)⟩

/-- The isometry `x ↦ [[1, 0], [σ, 1]] · x`. -/
noncomputable def lowerIsom (σ : ℝ) : isom (n + 2) :=
  ⟨(sl2Equiv (n := n) (show (1 : ℝ) * 1 - 0 * σ = 1 by ring)).toAffineEquiv,
    mem_isom_iff.2 (sl2Equiv_lower_mem σ)⟩

theorem upperIsom_smul (σ : ℝ) (x : Minkowski (n + 2)) :
    upperIsom (n := n) σ • x = sl2Lin 1 σ 0 1 x := rfl

theorem lowerIsom_smul (σ : ℝ) (x : Minkowski (n + 2)) :
    lowerIsom (n := n) σ • x = sl2Lin 1 0 σ 1 x := rfl

/-! ### 2. The level-4 congruence group `Γ₄` -/

/-- The integer matrix `[[1 + 4a, 4b], [4c, 1 + 4e]]` has determinant `1`. -/
def IsCong4 (a b c e : ℤ) : Prop := (1 + 4 * a) * (1 + 4 * e) - (4 * b) * (4 * c) = 1

/-- The action of `[[1 + 4a, 4b], [4c, 1 + 4e]]`. -/
noncomputable def cong4Lin (a b c e : ℤ) : Minkowski (n + 2) →ₗ[ℝ] Minkowski (n + 2) :=
  sl2Lin (1 + 4 * (a : ℝ)) (4 * (b : ℝ)) (4 * (c : ℝ)) (1 + 4 * (e : ℝ))

theorem IsCong4.real {a b c e : ℤ} (h : IsCong4 a b c e) :
    (1 + 4 * (a : ℝ)) * (1 + 4 * (e : ℝ)) - (4 * (b : ℝ)) * (4 * (c : ℝ)) = 1 := by
  have := congrArg (fun z : ℤ => (z : ℝ)) h
  push_cast at this
  exact this

theorem cong4Lin_comp (a b c e a' b' c' e' : ℤ) (x : Minkowski (n + 2)) :
    cong4Lin a b c e (cong4Lin a' b' c' e' x) =
      cong4Lin (a + a' + 4 * a * a' + 4 * b * c') (b + b' + 4 * a * b' + 4 * b * e')
        (c + c' + 4 * c * a' + 4 * e * c') (e + e' + 4 * c * b' + 4 * e * e') x := by
  rw [cong4Lin, cong4Lin, ← LinearMap.comp_apply, sl2Lin_comp, cong4Lin]
  congr 2 <;> push_cast <;> ring

theorem IsCong4.mul {a b c e a' b' c' e' : ℤ} (h : IsCong4 a b c e) (h' : IsCong4 a' b' c' e') :
    IsCong4 (a + a' + 4 * a * a' + 4 * b * c') (b + b' + 4 * a * b' + 4 * b * e')
      (c + c' + 4 * c * a' + 4 * e * c') (e + e' + 4 * c * b' + 4 * e * e') := by
  unfold IsCong4 at *
  linear_combination ((1 + 4 * a') * (1 + 4 * e') - (4 * b') * (4 * c')) * h + h'

theorem IsCong4.inv {a b c e : ℤ} (h : IsCong4 a b c e) : IsCong4 e (-b) (-c) a := by
  unfold IsCong4 at *; linear_combination h

theorem cong4Lin_inv {a b c e : ℤ} (h : IsCong4 a b c e) (x : Minkowski (n + 2)) :
    cong4Lin a b c e (cong4Lin e (-b) (-c) a x) = x := by
  rw [cong4Lin_comp]
  have hr := h.real
  have e1 : cong4Lin (n := n) (a + e + 4 * a * e + 4 * b * -c) (b + -b + 4 * a * -b + 4 * b * a)
      (c + -c + 4 * c * e + 4 * e * -c) (e + a + 4 * c * -b + 4 * e * a) = LinearMap.id := by
    rw [cong4Lin, ← sl2Lin_one]
    congr 1
    · push_cast; linear_combination hr
    · push_cast; ring
    · push_cast; ring
    · push_cast; linear_combination hr
  rw [e1, LinearMap.id_apply]

theorem cong4Lin_zero : cong4Lin (n := n) 0 0 0 0 = LinearMap.id := by
  rw [cong4Lin, ← sl2Lin_one]; norm_num

/-- **`Γ₄`**: the isometries of `𝐌ⁿ` acting as an integer matrix `≡ 1 mod 4` of `SL(2, ℤ)` on
the first two spatial coordinates (the image of the principal congruence subgroup `Γ(4)`). -/
noncomputable def gamma4 (m : ℕ) : Subgroup (isom (m + 2)) where
  carrier := {g | ∃ a b c e : ℤ, IsCong4 a b c e ∧
    ∀ x : Minkowski (m + 2), g • x = cong4Lin a b c e x}
  one_mem' := ⟨0, 0, 0, 0, by unfold IsCong4; norm_num, fun x => by
    rw [cong4Lin_zero, one_smul, LinearMap.id_apply]⟩
  mul_mem' := by
    rintro g g' ⟨a, b, c, e, h, hg⟩ ⟨a', b', c', e', h', hg'⟩
    exact ⟨_, _, _, _, h.mul h', fun x => by rw [mul_smul, hg', hg, cong4Lin_comp]⟩
  inv_mem' := by
    rintro g ⟨a, b, c, e, h, hg⟩
    refine ⟨e, -b, -c, a, h.inv, fun x => ?_⟩
    rw [inv_smul_eq_iff, hg, cong4Lin_inv h]

theorem upperIsom_mem : upperIsom (n := n) 4 ∈ gamma4 n :=
  ⟨0, 1, 0, 0, by unfold IsCong4; norm_num, fun x => by
    rw [upperIsom_smul, cong4Lin]; norm_num⟩

theorem lowerIsom_mem : lowerIsom (n := n) 4 ∈ gamma4 n :=
  ⟨0, 0, 1, 0, by unfold IsCong4; norm_num, fun x => by
    rw [lowerIsom_smul, cong4Lin]; norm_num⟩

/-! ### 3. `Γ₄` acts freely and properly on the hyperboloid -/

/-- Two isometries acting alike are equal. -/
theorem isom_ext_smul {d : ℕ} {g g' : isom d} (h : ∀ x : Minkowski d, g • x = g' • x) : g = g' :=
  Subtype.ext (AffineEquiv.ext h)

/-- **A linear isometry preserves the hyperboloid** `{minkQ = −1, t > 0}`. -/
theorem smul_graph_hyperboloid {d : ℕ} {g : isom d} (h0 : g • (0 : Minkowski d) = 0) :
    g • graph (hyperboloid d) = graph (hyperboloid d) := by
  have hlin : ∀ (g : isom d), g • (0 : Minkowski d) = 0 → ∀ x, g • x = linOf g x := by
    intro g hg x
    rw [smul_eq_lin_add]
    have : trOf g = g • (0 : Minkowski d) := rfl
    rw [this, hg, add_zero]
  have hsub : ∀ (g : isom d), g • (0 : Minkowski d) = 0 → ∀ x ∈ graph (hyperboloid d),
      g • x ∈ graph (hyperboloid d) := by
    intro g hg x hx
    rw [graph_hyperboloid] at hx ⊢
    have ht : IsFutureTimelike x := ⟨hx.2, by rw [hx.1]; norm_num⟩
    have := lorentz.isFutureTimelike_apply (linOf_mem g) ht
    rw [hlin g hg]
    exact ⟨by rw [lorentz.minkQ_apply (linOf_mem g)]; exact hx.1, this.1⟩
  have hinv0 : g⁻¹ • (0 : Minkowski d) = 0 := by rw [inv_smul_eq_iff, h0]
  ext x
  rw [Set.mem_smul_set_iff_inv_smul_mem]
  refine ⟨fun hx => ?_, fun hx => hsub _ hinv0 x hx⟩
  have := hsub g h0 _ hx
  rwa [smul_inv_smul] at this

/-- On `Γ₄`, an element fixing the origin. -/
theorem gamma4_smul_zero {m : ℕ} {g : isom (m + 2)} (hg : g ∈ gamma4 m) :
    g • (0 : Minkowski (m + 2)) = 0 := by
  obtain ⟨a, b, c, e, -, h⟩ := hg
  rw [h, map_zero]

/-- The coordinates of a point of the hyperboloid: `t ± x₀ > 0` and `t² − x₀² − x₁² ≥ 1`. -/
theorem coords_of_mem_hyperboloid {x : Minkowski (n + 2)} (hx : x ∈ graph (hyperboloid (n + 2))) :
    0 < abelCoordT x + abelCoord0 x ∧ 0 < abelCoordT x - abelCoord0 x ∧ 1 ≤ abelCoordT x ^ 2 - abelCoord0 x ^ 2 - abelCoord1 x ^ 2 ∧ 0 < abelCoordT x := by
  rw [graph_hyperboloid] at hx
  set r := x - abelCoordT x • timeUnit (n + 2) - abelCoord0 x • spaceUnit (0 : Fin (n + 2)) -
    abelCoord1 x • spaceUnit (1 : Fin (n + 2)) with hr
  have hr1 : r.1 = 0 := by
    have := abelCoordT_eq x
    simp [hr, timeUnit, spaceUnit, this]
  have hQr := minkQ_nonneg_of_fst_eq_zero hr1
  have hQ : minkQ r = minkQ x + abelCoordT x ^ 2 - abelCoord0 x ^ 2 - abelCoord1 x ^ 2 := by
    rw [hr, sub_eq_add_neg, sub_eq_add_neg, sub_eq_add_neg, minkQ_add, minkQ_add, minkQ_add]
    simp only [minkB_add_left, minkB_neg_left, minkB_neg_right, minkB_smul_left,
      minkB_smul_right, minkQ_neg, minkQ_smul, minkQ_timeUnit, minkQ_spaceUnit, minkB_T_S,
      minkB_S0_S1, abelCoordT, abelCoord0, abelCoord1]
    ring
  have ht : 0 < abelCoordT x := by rw [abelCoordT_eq]; exact hx.2
  have hδ : 1 ≤ abelCoordT x ^ 2 - abelCoord0 x ^ 2 - abelCoord1 x ^ 2 := by rw [hx.1] at hQ; linarith
  have h0 : abelCoord0 x ^ 2 < abelCoordT x ^ 2 := by nlinarith [sq_nonneg (abelCoord1 x)]
  have habs : |abelCoord0 x| < abelCoordT x := by
    rw [← abs_of_pos ht]; exact sq_lt_sq.1 h0
  refine ⟨by linarith [neg_abs_le (abelCoord0 x)], by linarith [le_abs_self (abelCoord0 x)], hδ, ht⟩

/-- The integer fact behind torsion-freeness: `(2 + 4k)² ≥ 4`. -/
private theorem four_le_sq_two_add_four_mul (k : ℤ) : (4 : ℝ) ≤ (2 + 4 * (k : ℝ)) ^ 2 := by
  have : (0 : ℤ) ≤ k * (k + 1) := by
    rcases le_or_gt 0 k with hk | hk
    · positivity
    · have : k + 1 ≤ 0 := by omega
      nlinarith
  have h' : (0 : ℝ) ≤ (k : ℝ) * ((k : ℝ) + 1) := by exact_mod_cast this
  nlinarith

/-- **The algebraic core of torsion-freeness**: a matrix of `Γ(4)` fixing a positive definite
`X = [[α, β], [β, γ]]` is the identity. In `SL(2, ℝ)` such a fixed point forces `|tr M| < 2`
unless `M = ±1`, and `tr M ≡ 2 mod 4` forbids it. -/
theorem cong4_eq_zero_of_fixed {a b c e : ℤ} (h : IsCong4 a b c e) {t x0 x1 : ℝ}
    (hγ : 0 < t - x0) (hδ : 0 < t ^ 2 - x0 ^ 2 - x1 ^ 2)
    (e1 : sl2T (1 + 4 * (a : ℝ)) (4 * (b : ℝ)) (4 * (c : ℝ)) (1 + 4 * (e : ℝ)) t x0 x1 = t)
    (e2 : sl2X0 (1 + 4 * (a : ℝ)) (4 * (b : ℝ)) (4 * (c : ℝ)) (1 + 4 * (e : ℝ)) t x0 x1 = x0)
    (e3 : sl2X1 (1 + 4 * (a : ℝ)) (4 * (b : ℝ)) (4 * (c : ℝ)) (1 + 4 * (e : ℝ)) t x0 x1 = x1) :
    a = 0 ∧ b = 0 ∧ c = 0 ∧ e = 0 := by
  have hD := h.real
  set P : ℝ := 1 + 4 * (a : ℝ)
  set Q : ℝ := 4 * (b : ℝ)
  set R : ℝ := 4 * (c : ℝ)
  set S : ℝ := 1 + 4 * (e : ℝ)
  set α := t + x0
  set β := x1
  set γ := t - x0
  unfold sl2T at e1; unfold sl2X0 at e2; unfold sl2X1 at e3
  have E1 : P ^ 2 * α + 2 * P * Q * β + Q ^ 2 * γ = α := by linear_combination e1 + e2
  have E2 : P * R * α + (P * S + Q * R) * β + Q * S * γ = β := e3
  have E3 : R ^ 2 * α + 2 * R * S * β + S ^ 2 * γ = γ := by linear_combination e1 - e2
  have G2 : Q * γ + R * α = 0 := by
    linear_combination (-R) * E1 + P * E2 - (P * β + Q * γ) * hD
  have G4 : 2 * R * β + (S - P) * γ = 0 := by
    linear_combination (-R) * E2 + P * E3 - (R * β + S * γ) * hD
  have hδ' : α * γ - β ^ 2 = t ^ 2 - x0 ^ 2 - x1 ^ 2 := by ring
  have key : γ ^ 2 * ((P + S) ^ 2 - 4) + 4 * R ^ 2 * (α * γ - β ^ 2) = 0 := by
    linear_combination ((S - P) * γ - 2 * R * β) * G4 + 4 * γ * R * G2 + 4 * γ ^ 2 * hD
  have htr : 4 ≤ (P + S) ^ 2 := by
    have := four_le_sq_two_add_four_mul (a + e)
    push_cast at this
    have hPS : P + S = 2 + 4 * ((a : ℝ) + (e : ℝ)) := by ring
    rw [hPS]; exact this
  have hR : R = 0 := by
    have h1 : 0 ≤ γ ^ 2 * ((P + S) ^ 2 - 4) := mul_nonneg (sq_nonneg _) (by linarith)
    have h2 : R ^ 2 * (α * γ - β ^ 2) ≤ 0 := by nlinarith
    rw [hδ'] at h2
    have : R ^ 2 ≤ 0 := by
      by_contra hc
      push Not at hc
      nlinarith
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (le_antisymm this (sq_nonneg _))
  have hQ : Q = 0 := by
    rw [hR, zero_mul, add_zero] at G2
    exact (mul_eq_zero.1 G2).resolve_right hγ.ne'
  have hc : c = 0 := by
    have : (c : ℝ) = 0 := by simpa [R] using hR
    exact_mod_cast this
  have hb : b = 0 := by
    have : (b : ℝ) = 0 := by simpa [Q] using hQ
    exact_mod_cast this
  have hu : (1 + 4 * a) * (1 + 4 * e) = 1 := by
    have := h; unfold IsCong4 at this; rw [hb, hc] at this; linarith
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hu with h1 | h1
  · have ha : a = 0 := by omega
    rw [ha] at hu
    exact ⟨ha, hb, hc, by omega⟩
  · omega

/-- **`Γ₄` acts freely on the hyperboloid.** -/
theorem gamma4_free {g : isom (n + 2)} (hg : g ∈ gamma4 n) (h1 : g ≠ 1)
    {x : Minkowski (n + 2)} (hx : x ∈ graph (hyperboloid (n + 2))) : g • x ≠ x := by
  intro hfix
  obtain ⟨a, b, c, e, h, hgx⟩ := hg
  obtain ⟨-, hγ, hδ, -⟩ := coords_of_mem_hyperboloid hx
  have hx' : cong4Lin a b c e x = x := (hgx x).symm.trans hfix
  have e1 := cT_sl2Lin (n := n) (1 + 4 * (a : ℝ)) (4 * (b : ℝ)) (4 * (c : ℝ)) (1 + 4 * (e : ℝ)) x
  have e2 := c0_sl2Lin (n := n) (1 + 4 * (a : ℝ)) (4 * (b : ℝ)) (4 * (c : ℝ)) (1 + 4 * (e : ℝ)) x
  have e3 := c1_sl2Lin (n := n) (1 + 4 * (a : ℝ)) (4 * (b : ℝ)) (4 * (c : ℝ)) (1 + 4 * (e : ℝ)) x
  rw [show sl2Lin (1 + 4 * (a : ℝ)) (4 * (b : ℝ)) (4 * (c : ℝ)) (1 + 4 * (e : ℝ)) x = x from hx']
    at e1 e2 e3
  obtain ⟨rfl, rfl, rfl, rfl⟩ :=
    cong4_eq_zero_of_fixed h hγ (by linarith) e1.symm e2.symm e3.symm
  refine h1 (isom_ext_smul fun y => ?_)
  rw [hgx, cong4Lin_zero, LinearMap.id_apply, one_smul]

/-- `(t + x₀)·α' = (Pα + Qβ)² + (Pβ + Qγ)² + δ (P² + Q²)`: the bound behind properness. -/
theorem sq_add_sq_le_of_hyperboloid {p q r s t x0 x1 : ℝ} (hδ : 1 ≤ t ^ 2 - x0 ^ 2 - x1 ^ 2) :
    p ^ 2 + q ^ 2 ≤ 2 * t * (sl2T p q r s t x0 x1 + sl2X0 p q r s t x0 x1) ∧
      r ^ 2 + s ^ 2 ≤ 2 * t * (sl2T p q r s t x0 x1 - sl2X0 p q r s t x0 x1) := by
  unfold sl2T sl2X0
  constructor
  · nlinarith [sq_nonneg (p * (t + x0) + q * x1), sq_nonneg (p * x1 + q * (t - x0)),
      sq_nonneg p, sq_nonneg q]
  · nlinarith [sq_nonneg (r * (t + x0) + s * x1), sq_nonneg (r * x1 + s * (t - x0)),
      sq_nonneg r, sq_nonneg s]

/-- `|k| ≤ k²` for an integer. -/
private theorem int_abs_le_sq (k : ℤ) : |(k : ℝ)| ≤ (k : ℝ) ^ 2 := by
  have : |k| ≤ k ^ 2 := by
    rcases eq_or_ne k 0 with rfl | hk
    · simp
    · have h1 : 1 ≤ |k| := Int.one_le_abs hk
      rw [← sq_abs]; nlinarith
  exact_mod_cast this

/-- **`Γ₄` acts properly discontinuously on the hyperboloid.** -/
theorem gamma4_proper {K : Set (Minkowski (n + 2))} (hKS : K ⊆ graph (hyperboloid (n + 2)))
    (hK : IsCompact K) :
    {γ : isom (n + 2) | γ ∈ gamma4 n ∧ (γ • K ∩ K).Nonempty}.Finite := by
  obtain ⟨C, hC⟩ := hK.bddAbove_image continuous_fst.continuousOn
  set B : ℝ := 4 * C ^ 2 + 1
  set N : ℕ := ⌈B⌉₊
  set F : Set (ℤ × ℤ × ℤ × ℤ) := Icc (-(N : ℤ)) N ×ˢ Icc (-(N : ℤ)) N ×ˢ
    Icc (-(N : ℤ)) N ×ˢ Icc (-(N : ℤ)) N
  have hF : F.Finite := (finite_Icc _ _).prod ((finite_Icc _ _).prod
    ((finite_Icc _ _).prod (finite_Icc _ _)))
  have hsub : {γ : isom (n + 2) | γ ∈ gamma4 n ∧ (γ • K ∩ K).Nonempty} ⊆
      ⋃ q ∈ F, {γ : isom (n + 2) | ∀ x : Minkowski (n + 2), γ • x = cong4Lin q.1 q.2.1 q.2.2.1 q.2.2.2 x} := by
    rintro γ ⟨⟨a, b, c, e, h, hγ⟩, ⟨y, ⟨k, hk, rfl⟩, hyK⟩⟩
    simp only [mem_iUnion, mem_setOf_eq]
    refine ⟨(a, b, c, e), ?_, hγ⟩
    have hkS := hKS hk
    have hyS : γ • k ∈ graph (hyperboloid (n + 2)) := hKS hyK
    obtain ⟨-, -, hδ, ht⟩ := coords_of_mem_hyperboloid hkS
    obtain ⟨hα', hγ', -, -⟩ := coords_of_mem_hyperboloid hyS
    have htC : abelCoordT k ≤ C := by rw [abelCoordT_eq]; exact hC ⟨k, hk, rfl⟩
    have htC' : abelCoordT (γ • k) ≤ C := by rw [abelCoordT_eq]; exact hC ⟨_, hyK, rfl⟩
    rw [hγ] at hα' hγ' htC'
    unfold cong4Lin at hα' hγ' htC'
    rw [cT_sl2Lin] at hα' hγ' htC'
    rw [c0_sl2Lin] at hα' hγ'
    obtain ⟨h1, h2⟩ := sq_add_sq_le_of_hyperboloid (p := 1 + 4 * (a : ℝ)) (q := 4 * (b : ℝ))
      (r := 4 * (c : ℝ)) (s := 1 + 4 * (e : ℝ)) hδ
    set T' := sl2T (1 + 4 * (a : ℝ)) (4 * (b : ℝ)) (4 * (c : ℝ)) (1 + 4 * (e : ℝ))
      (abelCoordT k) (abelCoord0 k) (abelCoord1 k)
    set X' := sl2X0 (1 + 4 * (a : ℝ)) (4 * (b : ℝ)) (4 * (c : ℝ)) (1 + 4 * (e : ℝ))
      (abelCoordT k) (abelCoord0 k) (abelCoord1 k)
    have hC0 : 0 < C := lt_of_lt_of_le ht htC
    have hb1 : 2 * abelCoordT k * (T' + X') ≤ 4 * C ^ 2 := by nlinarith
    have hb2 : 2 * abelCoordT k * (T' - X') ≤ 4 * C ^ 2 := by nlinarith
    have hNB : B ≤ N := Nat.le_ceil B
    have bnd : ∀ z : ℤ, (z : ℝ) ^ 2 ≤ B → z ∈ Icc (-(N : ℤ)) N := by
      intro z hz
      have h3 := int_abs_le_sq z
      have h4 : |(z : ℝ)| ≤ (N : ℝ) := by linarith
      have h5 : |z| ≤ (N : ℤ) := by exact_mod_cast h4
      exact ⟨by linarith [neg_abs_le z], by linarith [le_abs_self z]⟩
    refine ⟨bnd a ?_, bnd b ?_, bnd c ?_, bnd e ?_⟩
    · nlinarith [sq_nonneg (4 * (b : ℝ)), sq_nonneg (1 + 4 * (a : ℝ) + 1)]
    · nlinarith [sq_nonneg (1 + 4 * (a : ℝ))]
    · nlinarith [sq_nonneg (1 + 4 * (e : ℝ))]
    · nlinarith [sq_nonneg (4 * (c : ℝ)), sq_nonneg (1 + 4 * (e : ℝ) + 1)]
  refine (hF.biUnion fun q _ => ?_).subset hsub
  refine Set.Subsingleton.finite fun g hg g' hg' => isom_ext_smul fun x => ?_
  rw [hg x, hg' x]

/-- **`Γ₄` acting on the hyperboloid satisfies §8's standing hypotheses** `CCAction` (DEC-35):
(CC′), invariance, freeness, properness. -/
theorem ccAction_gamma4 : CCAction (gamma4 n) (graph (hyperboloid (n + 2))) where
  cc := ccPrime_graph_hyperboloid
  inv _ hγ := smul_graph_hyperboloid (gamma4_smul_zero hγ)
  free _ hγ h1 _ hx := gamma4_free hγ h1 hx
  proper _ hKS hK := gamma4_proper hKS hK

/-! ### 4. `Γ₄` is not virtually abelian -/

theorem upperIsom_pow_smul (k : ℕ) (x : Minkowski (n + 2)) :
    (upperIsom (n := n) 4 ^ k) • x = sl2Lin 1 (4 * k) 0 1 x := by
  induction k generalizing x with
  | zero => simp [sl2Lin_one]
  | succ k ih =>
    rw [pow_succ, mul_smul, upperIsom_smul, ih, ← LinearMap.comp_apply, sl2Lin_comp]
    congr 2 <;> push_cast <;> ring

theorem lowerIsom_pow_smul (k : ℕ) (x : Minkowski (n + 2)) :
    (lowerIsom (n := n) 4 ^ k) • x = sl2Lin 1 0 (4 * k) 1 x := by
  induction k generalizing x with
  | zero => simp [sl2Lin_one]
  | succ k ih =>
    rw [pow_succ, mul_smul, lowerIsom_smul, ih, ← LinearMap.comp_apply, sl2Lin_comp]
    congr 2 <;> push_cast <;> ring

/-- **No positive powers of the two generators commute**: on the time unit, the `x₀`-coordinates
of `uᵏ lˡ T` and `lˡ uᵏ T` differ by `(1 + 16kl)² − 1`. -/
theorem upper_lower_pow_not_commute {k l : ℕ} (hk : 0 < k) (hl : 0 < l) :
    upperIsom (n := n) 4 ^ k * lowerIsom 4 ^ l ≠ lowerIsom 4 ^ l * upperIsom 4 ^ k := by
  intro h
  have h1 := congrArg (fun g : isom (n + 2) => abelCoord0 (g • timeUnit (n + 2))) h
  simp only [mul_smul, upperIsom_pow_smul, lowerIsom_pow_smul] at h1
  rw [← LinearMap.comp_apply, sl2Lin_comp, ← LinearMap.comp_apply, sl2Lin_comp, c0_sl2Lin,
    c0_sl2Lin] at h1
  have t1 : abelCoordT (timeUnit (n + 2)) = 1 := by rw [abelCoordT_eq]; rfl
  have t2 : abelCoord0 (timeUnit (n + 2)) = 0 := minkB_T_S 0
  have t3 : abelCoord1 (timeUnit (n + 2)) = 0 := minkB_T_S 1
  rw [t1, t2, t3] at h1
  unfold sl2X0 at h1
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hl' : (1 : ℝ) ≤ l := by exact_mod_cast hl
  nlinarith [mul_le_mul hk' hl' zero_le_one (by linarith)]

/-- A finite-index subgroup of `Γ` contains a positive power of every element of `Γ`. -/
theorem exists_pow_mem_of_finiteIndex {d : ℕ} {Γ Γ' : Subgroup (isom d)}
    (hfi : (Γ'.subgroupOf Γ).FiniteIndex) {g : isom d} (hg : g ∈ Γ) :
    ∃ k, 0 < k ∧ g ^ k ∈ Γ' := by
  obtain ⟨k, hk, -, hmem⟩ :=
    Subgroup.exists_pow_mem_of_index_ne_zero (Subgroup.FiniteIndex.index_ne_zero (H :=
      Γ'.subgroupOf Γ)) ⟨g, hg⟩
  exact ⟨k, hk, by simpa [Subgroup.mem_subgroupOf] using hmem⟩

/-- A group additively isomorphic to `ℤᵏ` is commutative. -/
theorem commute_of_addEquiv_finsupp {G : Type*} [Group G] {k : ℕ}
    (e : Additive G ≃+ (Fin k →₀ ℤ)) (x y : G) : x * y = y * x := by
  have : e (Additive.ofMul x + Additive.ofMul y) = e (Additive.ofMul y + Additive.ofMul x) := by
    rw [map_add, map_add, add_comm]
  have := e.injective this
  exact Additive.ofMul.injective (by simpa [← ofMul_mul] using this)

/-- **"Virtually `ℤᵏ`"**: a finite-index subgroup isomorphic to a free abelian group of finite
rank (Barbot l.2296, "contains as a finite index subgroup a free abelian group of finite rank"). -/
def IsVirtuallyFreeAbelian {d : ℕ} (Γ : Subgroup (isom d)) : Prop :=
  ∃ Γ' : Subgroup (isom d), Γ' ≤ Γ ∧ (Γ'.subgroupOf Γ).FiniteIndex ∧
    ∃ k : ℕ, Nonempty (Additive Γ' ≃+ (Fin k →₀ ℤ))

/-- **`Γ₄` is not virtually abelian**, a fortiori not virtually `ℤᵏ`: no finite-index subgroup is
commutative. -/
theorem gamma4_not_virtually_comm {Γ' : Subgroup (isom (n + 2))}
    (hfi : (Γ'.subgroupOf (gamma4 n)).FiniteIndex) :
    ∃ x ∈ Γ', ∃ y ∈ Γ', x * y ≠ y * x := by
  obtain ⟨k, hk, hku⟩ := exists_pow_mem_of_finiteIndex hfi (upperIsom_mem (n := n))
  obtain ⟨l, hl, hll⟩ := exists_pow_mem_of_finiteIndex hfi (lowerIsom_mem (n := n))
  exact ⟨_, hku, _, hll, upper_lower_pow_not_commute hk hl⟩

theorem not_isVirtuallyFreeAbelian_gamma4 : ¬IsVirtuallyFreeAbelian (gamma4 n) := by
  rintro ⟨Γ', -, hfi, k, ⟨e⟩⟩
  obtain ⟨x, hx, y, hy, hxy⟩ := gamma4_not_virtually_comm hfi
  exact hxy (congrArg Subtype.val (commute_of_addEquiv_finsupp e ⟨x, hx⟩ ⟨y, hy⟩))

/-! ### 5. The spacelike subspace `U` fixed pointwise -/

/-- An affine subspace of `𝐌ⁿ` is **spacelike** when every nonzero vector of its direction is
spacelike (a point is a spacelike affine subspace). -/
def IsSpacelikeAffine {d : ℕ} (U : AffineSubspace ℝ (Minkowski d)) : Prop :=
  ∀ v ∈ U.direction, v ≠ 0 → 0 < minkQ v

/-- `{t = x₀ = x₁ = 0}`, a linear subspace of dimension `n` (a point for `n = 0`, a line for
`n = 1`). -/
noncomputable def axisSub (n : ℕ) : Submodule ℝ (Minkowski (n + 2)) where
  carrier := {v | abelCoordT v = 0 ∧ abelCoord0 v = 0 ∧ abelCoord1 v = 0}
  add_mem' := by
    rintro v w ⟨h1, h2, h3⟩ ⟨h1', h2', h3'⟩
    refine ⟨?_, ?_, ?_⟩
    · show -minkB (v + w) _ = 0
      have : -minkB v (timeUnit (n + 2)) = 0 := h1
      have : -minkB w (timeUnit (n + 2)) = 0 := h1'
      rw [minkB_add_left]; linarith
    · show minkB (v + w) _ = 0
      rw [minkB_add_left, show minkB v _ = 0 from h2, show minkB w _ = 0 from h2', add_zero]
    · show minkB (v + w) _ = 0
      rw [minkB_add_left, show minkB v _ = 0 from h3, show minkB w _ = 0 from h3', add_zero]
  zero_mem' := by simp [abelCoordT, abelCoord0, abelCoord1]
  smul_mem' := by
    rintro a v ⟨h1, h2, h3⟩
    refine ⟨?_, ?_, ?_⟩
    · show -minkB (a • v) _ = 0
      have : minkB v (timeUnit (n + 2)) = 0 := by have := h1; simp only [abelCoordT] at this; linarith
      rw [minkB_smul_left, this, mul_zero, neg_zero]
    · show minkB (a • v) _ = 0
      rw [minkB_smul_left, show minkB v _ = 0 from h2, mul_zero]
    · show minkB (a • v) _ = 0
      rw [minkB_smul_left, show minkB v _ = 0 from h3, mul_zero]

/-- The affine subspace `U = {t = x₀ = x₁ = 0}`. -/
noncomputable def axisU (n : ℕ) : AffineSubspace ℝ (Minkowski (n + 2)) := (axisSub n).toAffineSubspace

theorem mem_axisU {x : Minkowski (n + 2)} : x ∈ axisU n ↔ abelCoordT x = 0 ∧ abelCoord0 x = 0 ∧ abelCoord1 x = 0 :=
  Iff.rfl

theorem axisU_direction : (axisU n).direction = axisSub n := Submodule.toAffineSubspace_direction _

theorem isSpacelikeAffine_axisU : IsSpacelikeAffine (axisU n) := by
  intro v hv hv0
  rw [axisU_direction] at hv
  obtain ⟨h1, -, -⟩ := hv
  rw [abelCoordT_eq] at h1
  have h2 : v.2 ≠ 0 := fun h => hv0 (Prod.ext h1 h)
  simp only [minkQ, h1]
  have := norm_pos_iff.2 h2
  positivity

/-- For `n ≥ 1`, `U` is at least a line: it contains the spatial units `eᵢ`, `i ≥ 2`. -/
theorem spaceUnit_mem_axisU {i : Fin (n + 2)} (hi : 2 ≤ i.val) : spaceUnit i ∈ axisU n := by
  have h0 : (0 : Fin (n + 2)) ≠ i := fun h => by rw [← h] at hi; simp at hi
  have h1 : (1 : Fin (n + 2)) ≠ i := fun h => by
    rw [← h] at hi; simp at hi
  refine mem_axisU.2 ⟨by rw [abelCoordT, minkB_S_T]; simp, ?_, ?_⟩
  · rw [abelCoord0, minkB_comm]; exact minkB_spaceUnit_spaceUnit h0
  · rw [abelCoord1, minkB_comm]; exact minkB_spaceUnit_spaceUnit h1

/-- **`Γ₄` fixes `U` pointwise.** -/
theorem gamma4_fixes_axisU {g : isom (n + 2)} (hg : g ∈ gamma4 n) {x : Minkowski (n + 2)}
    (hx : x ∈ axisU n) : g • x = x := by
  obtain ⟨a, b, c, e, -, h⟩ := hg
  obtain ⟨h1, h2, h3⟩ := mem_axisU.1 hx
  rw [h, cong4Lin, sl2Lin_apply, h1, h2, h3]
  simp [sl2T, sl2X0, sl2X1]

theorem gamma4_invariant_axisU {g : isom (n + 2)} (hg : g ∈ gamma4 n) (x : Minkowski (n + 2)) :
    g • x ∈ axisU n ↔ x ∈ axisU n := by
  refine ⟨fun h => ?_, fun h => by rw [gamma4_fixes_axisU hg h]; exact h⟩
  have := gamma4_fixes_axisU ((gamma4 n).inv_mem hg) h
  rw [inv_smul_smul] at this
  rw [this]; exact h

theorem upperIsom_ne_one : upperIsom (n := n) 4 ≠ 1 := by
  intro h
  have h1 := congrArg (fun g : isom (n + 2) => abelCoord0 (g • timeUnit (n + 2))) h
  simp only [upperIsom_smul, one_smul, c0_sl2Lin] at h1
  have t1 : abelCoordT (timeUnit (n + 2)) = 1 := by rw [abelCoordT_eq]; rfl
  have t2 : abelCoord0 (timeUnit (n + 2)) = 0 := minkB_T_S 0
  have t3 : abelCoord1 (timeUnit (n + 2)) = 0 := minkB_T_S 1
  rw [t1, t2, t3] at h1
  unfold sl2X0 at h1
  norm_num at h1

/-- **Which hypothesis the counterexample violates**: no nontrivial element of `Γ₄` preserves a
timelike direction (it would fix a point of the hyperboloid, against freeness). -/
theorem gamma4_not_fix_timelike {g : isom (n + 2)} (hg : g ∈ gamma4 n) (h1 : g ≠ 1)
    {v : Minkowski (n + 2)} (hv : IsFutureTimelike v) : linOf g v ≠ v := by
  intro hfix
  have hq : 0 < -minkQ v := by linarith [hv.2]
  set c := 1 / √(-minkQ v)
  have hc : 0 < c := by positivity
  have hw : c • v ∈ graph (hyperboloid (n + 2)) := by
    rw [graph_hyperboloid]
    refine ⟨?_, ?_⟩
    · rw [minkQ_smul]
      have : c ^ 2 = 1 / -minkQ v := by
        rw [div_pow, Real.sq_sqrt hq.le, one_pow]
      rw [this, one_div, inv_mul_eq_div, div_neg, div_self hv.2.ne]
    · simp only [Prod.smul_fst, smul_eq_mul]; exact mul_pos hc hv.1
  refine gamma4_free hg h1 hw ?_
  rw [smul_eq_lin_add, map_smul, hfix]
  have : trOf g = g • (0 : Minkowski (n + 2)) := rfl
  rw [this, gamma4_smul_zero hg, add_zero]

end SL2

/-! ### 6. The printed statement, and its refutation -/

/-- **Cor 8.4 as printed** (l.2295–2296), in the DEC-35 reading of §8's setting (`CCAction`):
if `Γ` preserves a spacelike affine subspace `U`, then `Γ` is virtually `ℤᵏ`. **False** for
`d ≥ 3`, and for `d = 2` under the point reading of `U` (`not_bcorAbelPrinted`); kept as a
`Prop` (kb/0022). -/
def BcorAbelPrinted (d : ℕ) : Prop :=
  ∀ (Γ : Subgroup (isom d)) (S : Set (Minkowski d)) (U : AffineSubspace ℝ (Minkowski d)),
    CCAction Γ S → (U : Set (Minkowski d)).Nonempty → IsSpacelikeAffine U →
      (∀ γ ∈ Γ, ∀ x : Minkowski d, γ • x ∈ U ↔ x ∈ U) → IsVirtuallyFreeAbelian Γ

/-- **The first step of the printed proof** (l.2300–2301): "the action of `Γ` on `π(U)` has to be
free and properly discontinuous, and the same is true for the action on `U`" — here its
freeness half on `U`. **False** for `d ≥ 3`, and for `d = 2` under the point reading
(`not_bcorAbelStepPrinted`). -/
def BcorAbelStepPrinted (d : ℕ) : Prop :=
  ∀ (Γ : Subgroup (isom d)) (S : Set (Minkowski d)) (U : AffineSubspace ℝ (Minkowski d)),
    CCAction Γ S → (U : Set (Minkowski d)).Nonempty → IsSpacelikeAffine U →
      (∀ γ ∈ Γ, ∀ x : Minkowski d, γ • x ∈ U ↔ x ∈ U) →
        ∀ γ ∈ Γ, γ ≠ 1 → ∀ u ∈ U, γ • u ≠ u

/-- **The counterexample, packaged** (`d = n + 2 ≥ 2`, Barbot's `n + 3 ≥ 3`): `Γ₄` — the image of
the level-4 congruence subgroup of `SL(2, ℤ)`, acting on `(t, x₀, x₁)` as `SO₀(1, 2)` and
trivially on the other coordinates — with `Σ` the hyperboloid satisfies `CCAction` (Σ (CC′),
`Γ₄`-invariant, free, properly discontinuous: Σ is a Cauchy-complete spacelike hypersurface and
`Γ₄ \ Σ` the closed-up quotient of §8), fixes the spacelike subspace `U = {t = x₀ = x₁ = 0}`
pointwise (a point for `n = 0`; it contains the spatial units `eᵢ`, `i ≥ 2`), and is not
virtually `ℤᵏ`: no finite-index subgroup of it is even commutative. -/
theorem bcor_abel_counterexample (n : ℕ) :
    CCAction (gamma4 n) (graph (hyperboloid (n + 2))) ∧ IsSpacelikeAffine (axisU n) ∧
      (0 : Minkowski (n + 2)) ∈ axisU n ∧
      (∀ i : Fin (n + 2), 2 ≤ i.val → spaceUnit i ∈ axisU n) ∧
      (∀ γ ∈ gamma4 n, ∀ x ∈ axisU n, γ • x = x) ∧
      upperIsom 4 ∈ gamma4 n ∧ upperIsom (n := n) 4 ≠ 1 ∧
      (∀ Γ' : Subgroup (isom (n + 2)), (Γ'.subgroupOf (gamma4 n)).FiniteIndex →
        ∃ x ∈ Γ', ∃ y ∈ Γ', x * y ≠ y * x) ∧
      ¬IsVirtuallyFreeAbelian (gamma4 n) :=
  ⟨ccAction_gamma4, isSpacelikeAffine_axisU, (axisSub n).zero_mem,
    fun _ hi => spaceUnit_mem_axisU hi, fun _ hγ _ hx => gamma4_fixes_axisU hγ hx,
    upperIsom_mem, upperIsom_ne_one, fun _ hfi => gamma4_not_virtually_comm hfi,
    not_isVirtuallyFreeAbelian_gamma4⟩

/-- **Cor 8.4 is false as printed**: in every dimension `d ≥ 3` (Barbot's `n ≥ 4`)
unconditionally, `U` being then at least a line; at `d = 2` (`n = 0` here, Barbot's `n = 3`) `U`
is a point, and the refutation reads a point as a spacelike affine subspace. -/
theorem not_bcorAbelPrinted (n : ℕ) : ¬BcorAbelPrinted (n + 2) := fun h =>
  not_isVirtuallyFreeAbelian_gamma4 (h _ _ (axisU n) ccAction_gamma4 ⟨0, (axisSub n).zero_mem⟩
    isSpacelikeAffine_axisU fun _ hγ x => gamma4_invariant_axisU hγ x)

/-- **The printed proof's first step is false** too: `Γ₄` fixes `U` pointwise. -/
theorem not_bcorAbelStepPrinted (n : ℕ) : ¬BcorAbelStepPrinted (n + 2) := fun h =>
  h _ _ (axisU n) ccAction_gamma4 ⟨0, (axisSub n).zero_mem⟩ isSpacelikeAffine_axisU
    (fun _ hγ x => gamma4_invariant_axisU hγ x) _ upperIsom_mem upperIsom_ne_one 0
    (axisSub n).zero_mem (gamma4_fixes_axisU upperIsom_mem (axisSub n).zero_mem)

/-! ### 7. Repaired forms: a `Γ`-invariant timelike `Δ`, or two invariant null directions -/

section TrueForm

variable {d : ℕ} {Γ : Subgroup (isom d)} {S : Set (Minkowski d)}

/-- An isometry preserving a timelike direction `ℝ v` (`L(γ) v = λ v`) fixes `v`: `λ² = 1` by
`minkQ`, `λ > 0` by time orientation. So "`Δ` is `Γ`-invariant" is "`L(Γ)` fixes `v`". -/
theorem linOf_eq_self_of_smul {γ : isom d} {v : Minkowski d} (hv : IsFutureTimelike v) {c : ℝ}
    (hc : linOf γ v = c • v) : linOf γ v = v := by
  have hQ := lorentz.minkQ_apply (linOf_mem γ) v
  rw [hc, minkQ_smul] at hQ
  have hc2 : c ^ 2 = 1 := by
    have := hv.2.ne
    exact (mul_eq_right₀ this).1 hQ
  have hpos := (lorentz.isFutureTimelike_apply (linOf_mem γ) hv).1
  rw [hc] at hpos
  simp only [Prod.smul_fst, smul_eq_mul] at hpos
  have hc0 : 0 < c := pos_of_mul_pos_left hpos hv.1.le
  have : c = 1 := by nlinarith
  rw [hc, this, one_smul]

theorem isClosed_of_ccPrime (h : CCPrime S) : IsClosed S := by
  obtain ⟨g, hg, rfl⟩ := isEntireAcausalGraph_iff.1 h.entire
  exact isClosed_graph hg.lipschitzWith.continuous

/-- **The repaired step, freeness** (l.2300–2301 under `Δ` `Γ`-invariant): if `L(Γ)` fixes a
future timelike `v`, then `Γ` acts freely on all of `𝐌ⁿ` (a fortiori on `U`). The line `x + ℝv`
meets `Σ` at a point `s` with `γ s − s = γ x − x`. -/
theorem abel_free_of_fix (h : CCAction Γ S) {v : Minkowski d} (hv : IsFutureTimelike v)
    (hfix : ∀ γ ∈ Γ, linOf γ v = v) {γ : isom d} (hγ : γ ∈ Γ) (h1 : γ ≠ 1) (x : Minkowski d) :
    γ • x ≠ x := by
  intro hx
  obtain ⟨s, hs⟩ := h.cc.entire.meets x v hv
  exact h.free γ hγ h1 _ hs (by rw [isom_smul_add_smul, hfix γ hγ, hx])

/-- **The repaired step, proper discontinuity** (l.2300–2301 under `Δ` `Γ`-invariant): if `L(Γ)`
fixes a future timelike `v`, then for every point `x` of `𝐌ⁿ` and every `R`, only finitely many
`γ ∈ Γ` move `x` by at most `R`. -/
theorem abel_proper_of_fix (h : CCAction Γ S) {v : Minkowski d} (hv : IsFutureTimelike v)
    (hfix : ∀ γ ∈ Γ, linOf γ v = v) (x : Minkowski d) (R : ℝ) :
    {γ : isom d | γ ∈ Γ ∧ dist (γ • x) x ≤ R}.Finite := by
  obtain ⟨s, hs⟩ := h.cc.entire.meets x v hv
  set p := x + s • v
  set K := closedBall p R ∩ S
  have hK : IsCompact K := (isCompact_closedBall p R).inter_right (isClosed_of_ccPrime h.cc)
  refine (h.proper K inter_subset_right hK).subset ?_
  rintro γ ⟨hγ, hd⟩
  have hR : 0 ≤ R := dist_nonneg.trans hd
  have hγp : γ • p = γ • x + s • v := by rw [isom_smul_add_smul, hfix γ hγ]
  refine ⟨hγ, γ • p, ⟨p, ⟨mem_closedBall_self hR, hs⟩, rfl⟩, ?_, h.smul_mem hγ hs⟩
  rw [mem_closedBall, hγp, dist_add_right]
  exact hd

/-! #### A Euclidean frame of a spacelike subspace -/

/-- A type synonym of a submodule, to carry the Euclidean structure of `minkB`. -/
def AbelSpSub {d : ℕ} (W : Submodule ℝ (Minkowski d)) : Type := W

noncomputable instance (W : Submodule ℝ (Minkowski d)) : AddCommGroup (AbelSpSub W) :=
  inferInstanceAs (AddCommGroup W)
noncomputable instance (W : Submodule ℝ (Minkowski d)) : Module ℝ (AbelSpSub W) :=
  inferInstanceAs (Module ℝ W)

/-- **An orthonormal frame of a spacelike subspace**: a linear `j : ℝᵏ → 𝐌ⁿ`, `k = dim W`,
with `minkQ (j y) = ‖y‖²` and image `W`. -/
theorem exists_spacelike_frame (W : Submodule ℝ (Minkowski d))
    (hW : ∀ v ∈ W, v ≠ 0 → 0 < minkQ v) :
    ∃ j : EuclideanSpace ℝ (Fin (finrank ℝ W)) →ₗ[ℝ] Minkowski d,
      (∀ y, minkQ (j y) = ‖y‖ ^ 2) ∧ ∀ w, w ∈ W ↔ ∃ y, j y = w := by
  have hnn : ∀ x : W, 0 ≤ minkB (x : Minkowski d) x := fun x => by
    rcases eq_or_ne (x : Minkowski d) 0 with h0 | h0
    · rw [h0, minkB_zero_left]
    · rw [← minkQ_eq_minkB]; exact (hW _ x.2 h0).le
  let i : W ≃ₗ[ℝ] AbelSpSub W := LinearEquiv.refl ℝ W
  letI core : InnerProductSpace.Core ℝ (AbelSpSub W) :=
    { inner := fun x y => minkB ((i.symm x : W) : Minkowski d) ((i.symm y : W) : Minkowski d)
      conj_inner_symm := fun x y => by
        simp only [starRingEnd_apply, star_trivial]; exact minkB_comm _ _
      re_inner_nonneg := fun x => by simp only [RCLike.re_to_real]; exact hnn _
      add_left := fun x y z => by
        simp only [map_add, Submodule.coe_add, minkB_add_left]
      smul_left := fun x y r => by
        simp only [map_smul, Submodule.coe_smul, minkB_smul_left, conj_trivial]
      definite := fun x hx => by
        by_contra hne
        have h0 : ((i.symm x : W) : Minkowski d) ≠ 0 := fun h =>
          hne (i.symm.injective (Subtype.ext (by rw [h, map_zero]; rfl)))
        have := hW _ (i.symm x).2 h0
        rw [minkQ_eq_minkB] at this
        exact this.ne' hx }
  letI : NormedAddCommGroup (AbelSpSub W) :=
    @InnerProductSpace.Core.toNormedAddCommGroup ℝ (AbelSpSub W) _ _ _ core
  letI : InnerProductSpace ℝ (AbelSpSub W) := InnerProductSpace.ofCore core.toCore
  haveI : FiniteDimensional ℝ (AbelSpSub W) := inferInstanceAs (FiniteDimensional ℝ W)
  have hrank : finrank ℝ (AbelSpSub W) = finrank ℝ W := i.symm.finrank_eq
  let b := (stdOrthonormalBasis ℝ (AbelSpSub W)).reindex (finCongr hrank)
  let j : EuclideanSpace ℝ (Fin (finrank ℝ W)) →ₗ[ℝ] Minkowski d :=
    W.subtype ∘ₗ (i.symm : AbelSpSub W →ₗ[ℝ] W) ∘ₗ
      (b.repr.symm.toLinearEquiv : EuclideanSpace ℝ (Fin (finrank ℝ W)) →ₗ[ℝ] AbelSpSub W)
  refine ⟨j, fun y => ?_, fun w => ⟨fun hw => ?_, ?_⟩⟩
  · have h1 : minkQ (j y) = inner ℝ (b.repr.symm y) (b.repr.symm y) := by
      rw [minkQ_eq_minkB]; rfl
    rw [h1, LinearIsometryEquiv.inner_map_map, real_inner_self_eq_norm_sq]
  · refine ⟨b.repr (i ⟨w, hw⟩), ?_⟩
    show ((i.symm (b.repr.symm (b.repr (i ⟨w, hw⟩))) : W) : Minkowski d) = w
    rw [LinearIsometryEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
  · rintro ⟨y, rfl⟩
    exact (i.symm (b.repr.symm y) : W).2

/-! #### `Γ` acting on `U`, read in the frame: a group of Euclidean isometries -/

section Frame

variable {k : ℕ} (j : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] Minkowski d) (u₀ : Minkowski d)

/-- `γ` read on `U = u₀ + j(ℝᵏ)`: `y ↦ j⁻¹(γ(u₀ + j y) − u₀)`. -/
noncomputable def uFrameConj (γ : isom d) (y : EuclideanSpace ℝ (Fin k)) :
    EuclideanSpace ℝ (Fin k) :=
  Function.invFun j (γ • (u₀ + j y) - u₀)

variable {j}

private theorem injective_of_minkQ (hjQ : ∀ y, minkQ (j y) = ‖y‖ ^ 2) : Function.Injective j := by
  intro y y' h
  have := hjQ (y - y')
  rw [map_sub, h, sub_self, minkQ_eq_minkB, minkB_zero_left] at this
  exact sub_eq_zero.1 (norm_eq_zero.1 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this.symm))

theorem apply_uFrameConj {γ : isom d} {y : EuclideanSpace ℝ (Fin k)}
    (hr : ∃ y', j y' = γ • (u₀ + j y) - u₀) : j (uFrameConj j u₀ γ y) = γ • (u₀ + j y) - u₀ :=
  Function.invFun_eq hr

variable (hjQ : ∀ y, minkQ (j y) = ‖y‖ ^ 2)
  (hstab : ∀ γ ∈ Γ, ∀ y, ∃ y', j y' = γ • (u₀ + j y) - u₀)
include hjQ hstab

theorem uFrameConj_mul (γ γ' : Γ) (y : EuclideanSpace ℝ (Fin k)) :
    uFrameConj j u₀ ((γ * γ' : Γ) : isom d) y =
      uFrameConj j u₀ (γ : isom d) (uFrameConj j u₀ (γ' : isom d) y) := by
  refine injective_of_minkQ hjQ ?_
  rw [apply_uFrameConj u₀ (hstab _ (γ * γ').2 y), apply_uFrameConj u₀ (hstab _ γ.2 _),
    apply_uFrameConj u₀ (hstab _ γ'.2 y), add_sub_cancel, Subgroup.coe_mul, mul_smul]

theorem uFrameConj_one (y : EuclideanSpace ℝ (Fin k)) :
    uFrameConj j u₀ ((1 : Γ) : isom d) y = y := by
  refine injective_of_minkQ hjQ ?_
  rw [apply_uFrameConj u₀ (hstab _ (1 : Γ).2 y), OneMemClass.coe_one, one_smul, add_sub_cancel_left]

theorem dist_uFrameConj (γ : Γ) (y y' : EuclideanSpace ℝ (Fin k)) :
    dist (uFrameConj j u₀ (γ : isom d) y) (uFrameConj j u₀ (γ : isom d) y') = dist y y' := by
  rw [dist_eq_norm, dist_eq_norm]
  have h1 : j (uFrameConj j u₀ (γ : isom d) y - uFrameConj j u₀ (γ : isom d) y') =
      linOf (γ : isom d) (j (y - y')) := by
    rw [map_sub, apply_uFrameConj u₀ (hstab _ γ.2 y), apply_uFrameConj u₀ (hstab _ γ.2 y'),
      sub_sub_sub_cancel_right, smul_sub_smul, add_sub_add_left_eq_sub, map_sub j]
  have h2 := hjQ (uFrameConj j u₀ (γ : isom d) y - uFrameConj j u₀ (γ : isom d) y')
  rw [h1, lorentz.minkQ_apply (linOf_mem _), hjQ] at h2
  exact ((sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h2).symm

/-- `γ` read on `U`, as an isometry of `ℝᵏ` (an affine one, by Mazur–Ulam). -/
noncomputable def uFrameIso (γ : Γ) : EuclideanSpace ℝ (Fin k) ≃ᵢ EuclideanSpace ℝ (Fin k) where
  toFun := uFrameConj j u₀ (γ : isom d)
  invFun := uFrameConj j u₀ ((γ⁻¹ : Γ) : isom d)
  left_inv y := by
    rw [← uFrameConj_mul u₀ hjQ hstab, inv_mul_cancel, uFrameConj_one u₀ hjQ hstab]
  right_inv y := by
    rw [← uFrameConj_mul u₀ hjQ hstab, mul_inv_cancel, uFrameConj_one u₀ hjQ hstab]
  isometry_toFun := Isometry.of_dist_eq fun y y' => dist_uFrameConj u₀ hjQ hstab γ y y'

/-- **`Γ → Isom(ℝᵏ)`**, `γ ↦ γ|_U` read in the frame. -/
noncomputable def uFrameHom :
    Γ →* (EuclideanSpace ℝ (Fin k) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin k)) where
  toFun γ := (uFrameIso u₀ hjQ hstab γ).toRealAffineIsometryEquiv
  map_one' := by
    refine AffineIsometryEquiv.ext fun y => ?_
    rw [IsometryEquiv.coeFn_toRealAffineIsometryEquiv]
    exact uFrameConj_one u₀ hjQ hstab y
  map_mul' γ γ' := by
    refine AffineIsometryEquiv.ext fun y => ?_
    rw [AffineIsometryEquiv.coe_mul, Function.comp_apply,
      IsometryEquiv.coeFn_toRealAffineIsometryEquiv, IsometryEquiv.coeFn_toRealAffineIsometryEquiv,
      IsometryEquiv.coeFn_toRealAffineIsometryEquiv]
    exact uFrameConj_mul u₀ hjQ hstab γ γ' y

theorem uFrameHom_apply (γ : Γ) (y : EuclideanSpace ℝ (Fin k)) :
    uFrameHom u₀ hjQ hstab γ y = uFrameConj j u₀ (γ : isom d) y := rfl

end Frame

/-- **Pulling Bieberbach back along an injective morphism** `Φ : Γ → Isom(E)` with discrete image:
`Γ` has a finite-index subgroup isomorphic to `ℤᵐ`, `m ≤ dim E`. -/
theorem virtuallyFree_of_injective_hom {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (hB : BieberbachI E) (Φ : Γ →* (E ≃ᵃⁱ[ℝ] E))
    (hinj : Function.Injective Φ) (hdisc : IsDiscreteEucl Φ.range) :
    ∃ Γ' : Subgroup (isom d), Γ' ≤ Γ ∧ (Γ'.subgroupOf Γ).FiniteIndex ∧
      ∃ m ≤ finrank ℝ E, Nonempty (Additive Γ' ≃+ (Fin m →₀ ℤ)) := by
  obtain ⟨Γ'', hle, hfi, m, hm, ⟨e⟩⟩ := virtuallyFree_of_bieberbachI hB hdisc
  set H₀ : Subgroup Γ := Γ''.comap Φ
  have hH₀ : H₀.index ≠ 0 := by
    rw [Subgroup.index_comap]
    exact hfi.index_ne_zero
  have hsub : (H₀.map Γ.subtype).subgroupOf Γ = H₀ :=
    Subgroup.comap_map_eq_self_of_injective Γ.subtype_injective H₀
  refine ⟨H₀.map Γ.subtype, Subgroup.map_subtype_le _, ⟨by rw [hsub]; exact hH₀⟩, m, hm, ⟨?_⟩⟩
  let e₁ : H₀ ≃* H₀.map Γ.subtype := H₀.equivMapOfInjective Γ.subtype Γ.subtype_injective
  let e₂ : H₀ ≃* H₀.map Φ := H₀.equivMapOfInjective Φ hinj
  let e₃ : H₀.map Φ ≃* Γ'' := MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self hle)
  exact (MulEquiv.toAdditive (e₁.symm.trans (e₂.trans e₃))).trans e

/-- Properness at a point of `Σ`: finitely many `γ` move `s ∈ Σ` by at most `R`. -/
theorem abel_finite_dist_le (h : CCAction Γ S) {s : Minkowski d} (hs : s ∈ S) (R : ℝ) :
    {γ : isom d | γ ∈ Γ ∧ dist (γ • s) s ≤ R}.Finite := by
  set K := closedBall s R ∩ S
  have hK : IsCompact K := (isCompact_closedBall s R).inter_right (isClosed_of_ccPrime h.cc)
  refine (h.proper K inter_subset_right hK).subset ?_
  rintro γ ⟨hγ, hd⟩
  have hR : 0 ≤ R := dist_nonneg.trans hd
  exact ⟨hγ, γ • s, ⟨s, ⟨mem_closedBall_self hR, hs⟩, rfl⟩, mem_closedBall.2 hd, h.smul_mem hγ hs⟩

/-- **Cor 8.4, a true repaired form** (`bcor:abel` repaired; unmarked): in §8's setting
(`CCAction`, DEC-35), if `Γ` preserves a nonempty spacelike affine subspace `U` **and a timelike
direction `Δ = ℝv`** — the hypothesis the printed proof uses without stating it, when it projects
along `Δ` (Prop 8.1) and lets `Γ` act on `π(U)` — then `Γ` has a finite-index subgroup
isomorphic to `ℤᵐ`, `m ≤ dim U`. Conditional on Bieberbach's first theorem in dimension `dim U`
(the external `BieberbachI`, DEC-36, `Flat/Bieberbach`). The orthogonality `Δ ⊂ U^⊥` of the
printed proof is not needed. The step "free and properly discontinuous on `U`" is
`abel_free_of_fix` / `abel_proper_of_fix`, proved outright. -/
theorem bcor_abel {U : AffineSubspace ℝ (Minkowski d)}
    (hB : BieberbachI (EuclideanSpace ℝ (Fin (finrank ℝ U.direction)))) (h : CCAction Γ S)
    (hU : (U : Set (Minkowski d)).Nonempty) (hsp : IsSpacelikeAffine U)
    (hinv : ∀ γ ∈ Γ, ∀ x : Minkowski d, γ • x ∈ U ↔ x ∈ U) {v : Minkowski d}
    (hv : IsFutureTimelike v) (hΔ : ∀ γ ∈ Γ, ∃ c : ℝ, linOf γ v = c • v) :
    ∃ Γ' : Subgroup (isom d), Γ' ≤ Γ ∧ (Γ'.subgroupOf Γ).FiniteIndex ∧
      ∃ m ≤ finrank ℝ U.direction, Nonempty (Additive Γ' ≃+ (Fin m →₀ ℤ)) := by
  have hfix : ∀ γ ∈ Γ, linOf γ v = v := fun γ hγ => by
    obtain ⟨c, hc⟩ := hΔ γ hγ
    exact linOf_eq_self_of_smul hv hc
  obtain ⟨u₀, hu₀⟩ := hU
  obtain ⟨j, hjQ, hjW⟩ := exists_spacelike_frame U.direction hsp
  have hstab : ∀ γ ∈ Γ, ∀ y, ∃ y', j y' = γ • (u₀ + j y) - u₀ := by
    intro γ hγ y
    have hmem : u₀ + j y ∈ U := by
      have := AffineSubspace.vadd_mem_of_mem_direction ((hjW _).2 ⟨y, rfl⟩) hu₀
      rwa [vadd_eq_add, add_comm] at this
    exact (hjW _).1 (AffineSubspace.vsub_mem_direction ((hinv γ hγ _).2 hmem) hu₀)
  set Φ := uFrameHom u₀ hjQ hstab
  have hΦ0 : ∀ γ : Γ, j (Φ γ 0) = (γ : isom d) • u₀ - u₀ := fun γ => by
    rw [uFrameHom_apply, apply_uFrameConj u₀ (hstab _ γ.2 0), map_zero, add_zero]
  have hinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_one]
    intro γ hγ
    have h0 := hΦ0 γ
    rw [hγ] at h0
    have h0' : (γ : isom d) • u₀ = u₀ := by
      rw [← sub_eq_zero, ← h0]
      exact map_zero j
    by_contra hne
    exact abel_free_of_fix h hv hfix γ.2 (fun e => hne (Subtype.ext e)) u₀ h0'
  have hdisc : IsDiscreteEucl Φ.range := by
    rw [isDiscreteEucl_iff_exists]
    refine ⟨0, fun R => ?_⟩
    let jc := LinearMap.toContinuousLinearMap j
    have hfin := abel_proper_of_fix h hv hfix u₀ (‖jc‖ * R)
    have hfin' : {γ : Γ | dist ((γ : isom d) • u₀) u₀ ≤ ‖jc‖ * R}.Finite :=
      (hfin.preimage Subtype.val_injective.injOn).subset fun γ hγ => ⟨γ.2, hγ⟩
    refine (hfin'.image Φ).subset ?_
    rintro g ⟨hg, hd⟩
    obtain ⟨γ, rfl⟩ := MonoidHom.mem_range.1 hg
    refine ⟨γ, ?_, rfl⟩
    show dist ((γ : isom d) • u₀) u₀ ≤ ‖jc‖ * R
    rw [dist_eq_norm, ← hΦ0 γ]
    rw [dist_zero_right] at hd
    calc ‖j (Φ γ 0)‖ = ‖jc (Φ γ 0)‖ := rfl
      _ ≤ ‖jc‖ * ‖Φ γ 0‖ := jc.le_opNorm _
      _ ≤ ‖jc‖ * R := mul_le_mul_of_nonneg_left hd (norm_nonneg _)
  have := virtuallyFree_of_injective_hom hB Φ hinj hdisc
  rwa [finrank_euclideanSpace_fin] at this

/-! #### Non-vacuity (kb/0011): a group satisfying every hypothesis of `bcor_abel` -/

/-- The spatial hyperplane `{t = 0}` as a linear subspace. -/
noncomputable def horizSub (d : ℕ) : Submodule ℝ (Minkowski d) :=
  LinearMap.ker (LinearMap.fst ℝ ℝ (EuclideanSpace ℝ (Fin d)))

theorem mem_horizSub {x : Minkowski d} : x ∈ horizSub d ↔ x.1 = 0 := Iff.rfl

theorem isSpacelikeAffine_horiz : IsSpacelikeAffine (horizSub d).toAffineSubspace := by
  intro v hv hv0
  rw [Submodule.toAffineSubspace_direction] at hv
  have h1 : v.1 = 0 := hv
  have h2 : v.2 ≠ 0 := fun h => hv0 (Prod.ext h1 h)
  simp only [minkQ, h1]
  have := norm_pos_iff.2 h2
  positivity

theorem fst_smul_of_mem_horizGroup {γ : isom d} (hγ : γ ∈ horizGroup (intLattice d))
    (x : Minkowski d) : (γ • x).1 = x.1 := by
  obtain ⟨v, -, rfl⟩ := mem_horizGroup.1 hγ
  exact fst_horizTranslation_smul _ _

/-- **The translation spacetimes `ℤᵈ \ 𝐌ⁿ` satisfy §8's standing hypotheses** on `Σ = {t = 0}`. -/
theorem ccAction_horizGroup :
    CCAction (horizGroup (intLattice d)) (graph fun _ : EuclideanSpace ℝ (Fin d) => (0 : ℝ)) where
  cc := ccPrime_graph_const 0
  inv γ hγ := by
    ext x
    rw [Set.mem_smul_set_iff_inv_smul_mem, mem_graph, mem_graph,
      fst_smul_of_mem_horizGroup ((horizGroup (intLattice d)).inv_mem hγ)]
  free γ hγ h1 x _ hx := by
    obtain ⟨v, -, rfl⟩ := mem_horizGroup.1 hγ
    have h2 := congrArg Prod.snd hx
    simp only [snd_horizTranslation_smul, toAdd_ofAdd, add_eq_right] at h2
    exact h1 (by rw [h2, ofAdd_zero, map_one])
  proper K _ hK := by
    have hf : Continuous fun q : Minkowski d => ‖q.2‖ := continuous_snd.norm
    obtain ⟨R, hR⟩ := hK.exists_bound_of_continuousOn hf.continuousOn
    refine ((finite_horiz_of_bound (intLattice d) (R + R)).image Subtype.val).subset ?_
    rintro γ ⟨hγ, ⟨_, ⟨k, hk, rfl⟩, hl⟩⟩
    obtain ⟨v, hvΛ, rfl⟩ := mem_horizGroup.1 hγ
    refine ⟨⟨_, hγ⟩, ⟨v, ?_, rfl⟩, rfl⟩
    have h1 := hR k hk
    have h2 := hR _ hl
    simp only [Real.norm_eq_abs, abs_norm] at h1 h2
    have := norm_le_of_horiz (v := v) (p := k) rfl
    linarith

theorem linOf_horizGroup {γ : isom d} (hγ : γ ∈ horizGroup (intLattice d)) (w : Minkowski d) :
    linOf γ w = w := by
  obtain ⟨v, -, rfl⟩ := mem_horizGroup.1 hγ
  rfl

/-- **The hypotheses of `bcor_abel` are jointly satisfiable by a nontrivial group**: `ℤᵈ` acting
by horizontal translations, `Σ = {t = 0}`, `U = {t = 0}` (spacelike, invariant), `Δ = ℝ·(1, 0)`
fixed. -/
theorem bcor_abel_hypotheses_witness :
    CCAction (horizGroup (intLattice d)) (graph fun _ : EuclideanSpace ℝ (Fin d) => (0 : ℝ)) ∧
      ((horizSub d).toAffineSubspace : Set (Minkowski d)).Nonempty ∧
      IsSpacelikeAffine (horizSub d).toAffineSubspace ∧
      (∀ γ ∈ horizGroup (intLattice d), ∀ x : Minkowski d,
        γ • x ∈ (horizSub d).toAffineSubspace ↔ x ∈ (horizSub d).toAffineSubspace) ∧
      IsFutureTimelike (timeUnit d) ∧
      ∀ γ ∈ horizGroup (intLattice d), ∃ c : ℝ, linOf γ (timeUnit d) = c • timeUnit d :=
  ⟨ccAction_horizGroup, ⟨0, (horizSub d).zero_mem⟩, isSpacelikeAffine_horiz,
    fun γ hγ x => by
      show (γ • x).1 = 0 ↔ x.1 = 0
      rw [fst_smul_of_mem_horizGroup hγ],
    ⟨by simp [timeUnit], by simp [minkQ, timeUnit]⟩,
    fun γ hγ => ⟨1, by rw [linOf_horizGroup hγ, one_smul]⟩⟩

/-! #### The two-null form, for the use at [10.M] (l.3326) -/

theorem abel_fst_pos_of_ne {v : Minkowski d} (hv : IsFutureCausal v) (hv0 : v ≠ 0) : 0 < v.1 :=
  lt_of_le_of_ne hv.1 fun h => hv0 (eq_zero_of_fst_eq_zero h.symm hv.2)

section TwoNull

variable (ℓ₀ ℓ₁ : Minkowski d)

/-- The eigenvalue of `L(γ)` on `ℓ₁` (read through `⟨· | ℓ₀⟩`). -/
noncomputable def eigOne (γ : isom d) : ℝ := minkB (linOf γ ℓ₁) ℓ₀ / minkB ℓ₁ ℓ₀

variable {ℓ₀ ℓ₁}

theorem linOf_eq_eigOne (hB : minkB ℓ₁ ℓ₀ ≠ 0) {γ : isom d} (h : ∃ c : ℝ, linOf γ ℓ₁ = c • ℓ₁) :
    linOf γ ℓ₁ = eigOne ℓ₀ ℓ₁ γ • ℓ₁ := by
  obtain ⟨c, hc⟩ := h
  rw [eigOne, hc, minkB_smul_left, mul_div_assoc, div_self hB, mul_one]

theorem eigOne_mul (hB : minkB ℓ₁ ℓ₀ ≠ 0) {γ γ' : isom d} (h : ∃ c : ℝ, linOf γ ℓ₁ = c • ℓ₁)
    (h' : ∃ c : ℝ, linOf γ' ℓ₁ = c • ℓ₁) :
    eigOne ℓ₀ ℓ₁ (γ * γ') = eigOne ℓ₀ ℓ₁ γ * eigOne ℓ₀ ℓ₁ γ' := by
  have e : linOf (γ * γ') ℓ₁ = (eigOne ℓ₀ ℓ₁ γ * eigOne ℓ₀ ℓ₁ γ') • ℓ₁ := by
    rw [linOf_mul, LinearEquiv.mul_apply, linOf_eq_eigOne hB h', map_smul, linOf_eq_eigOne hB h,
      smul_smul, mul_comm]
  rw [eigOne, e, minkB_smul_left, mul_div_assoc, div_self hB, mul_one]

theorem eigOne_one (hB : minkB ℓ₁ ℓ₀ ≠ 0) : eigOne ℓ₀ ℓ₁ (1 : isom d) = 1 := by
  rw [eigOne]; exact div_self hB

theorem eigOne_pos (hB : minkB ℓ₁ ℓ₀ ≠ 0) (hℓ : IsFutureCausal ℓ₁) (hℓ0 : ℓ₁ ≠ 0) {γ : isom d}
    (h : ∃ c : ℝ, linOf γ ℓ₁ = c • ℓ₁) : 0 < eigOne ℓ₀ ℓ₁ γ := by
  have e := linOf_eq_eigOne hB h
  have hf := lorentz.isFutureCausal_apply (linOf_mem γ) hℓ
  rw [e] at hf
  have h1 : 0 < ℓ₁.1 := abel_fst_pos_of_ne hℓ hℓ0
  have h2 : 0 ≤ eigOne ℓ₀ ℓ₁ γ * ℓ₁.1 := by simpa using hf.1
  have h3 : eigOne ℓ₀ ℓ₁ γ ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at e
    exact hℓ0 ((linOf γ).injective (e.trans (map_zero _).symm))
  exact lt_of_le_of_ne (nonneg_of_mul_nonneg_left h2 h1) (Ne.symm h3)

/-- The other eigenvalue is the inverse: `⟨L ℓ₀ | L ℓ₁⟩ = ⟨ℓ₀ | ℓ₁⟩`. -/
theorem linOf_eq_inv_eigOne (hB : minkB ℓ₁ ℓ₀ ≠ 0) {γ : isom d}
    (h0 : ∃ c : ℝ, linOf γ ℓ₀ = c • ℓ₀) (h1 : ∃ c : ℝ, linOf γ ℓ₁ = c • ℓ₁) :
    linOf γ ℓ₀ = (eigOne ℓ₀ ℓ₁ γ)⁻¹ • ℓ₀ := by
  obtain ⟨c, hc⟩ := h0
  have e1 := linOf_eq_eigOne hB h1
  have hm := minkB_linOf γ ℓ₁ ℓ₀
  rw [hc, e1, minkB_smul_left, minkB_smul_right] at hm
  have hcc : eigOne ℓ₀ ℓ₁ γ * c = 1 := by
    have : (eigOne ℓ₀ ℓ₁ γ * c - 1) * minkB ℓ₁ ℓ₀ = 0 := by linear_combination hm
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hB)
  rw [hc, eq_inv_of_mul_eq_one_right hcc]

variable {k : ℕ} {j : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] Minkowski d} (u₀ : Minkowski d)
  (hjQ : ∀ y, minkQ (j y) = ‖y‖ ^ 2)
  (hstab : ∀ γ ∈ Γ, ∀ y, ∃ y', j y' = γ • (u₀ + j y) - u₀)
  (hB : minkB ℓ₁ ℓ₀ ≠ 0) (hℓ : IsFutureCausal ℓ₁) (hℓ0 : ℓ₁ ≠ 0)
  (h1 : ∀ γ ∈ Γ, ∃ c : ℝ, linOf γ ℓ₁ = c • ℓ₁)

/-- `γ` read on `ℝ × U`: the boost parameter `log λ(γ)` on the first factor, `γ|_U` on the
second. -/
noncomputable def tnConj (ℓ₀ ℓ₁ : Minkowski d) (j : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] Minkowski d)
    (u₀ : Minkowski d) (γ : isom d) (p : WithLp 2 (ℝ × EuclideanSpace ℝ (Fin k))) :
    WithLp 2 (ℝ × EuclideanSpace ℝ (Fin k)) :=
  WithLp.toLp 2 (p.fst + Real.log (eigOne ℓ₀ ℓ₁ γ), uFrameConj j u₀ γ p.snd)

include hjQ hstab hB hℓ hℓ0 h1

theorem tnConj_mul (γ γ' : Γ) (p : WithLp 2 (ℝ × EuclideanSpace ℝ (Fin k))) :
    tnConj ℓ₀ ℓ₁ j u₀ ((γ * γ' : Γ) : isom d) p =
      tnConj ℓ₀ ℓ₁ j u₀ (γ : isom d) (tnConj ℓ₀ ℓ₁ j u₀ (γ' : isom d) p) := by
  have hp := eigOne_pos hB hℓ hℓ0 (h1 _ γ.2)
  have hp' := eigOne_pos hB hℓ hℓ0 (h1 _ γ'.2)
  unfold tnConj
  congr 1
  refine Prod.ext ?_ ?_
  · show p.fst + Real.log (eigOne ℓ₀ ℓ₁ ((γ : isom d) * γ')) =
      (p.fst + Real.log (eigOne ℓ₀ ℓ₁ γ')) + Real.log (eigOne ℓ₀ ℓ₁ γ)
    rw [eigOne_mul hB (h1 _ γ.2) (h1 _ γ'.2), Real.log_mul hp.ne' hp'.ne']; ring
  · exact uFrameConj_mul u₀ hjQ hstab γ γ' p.snd

omit hℓ hℓ0 h1 in
theorem tnConj_one (p : WithLp 2 (ℝ × EuclideanSpace ℝ (Fin k))) :
    tnConj ℓ₀ ℓ₁ j u₀ ((1 : Γ) : isom d) p = p := by
  unfold tnConj
  rw [OneMemClass.coe_one, eigOne_one hB, Real.log_one, add_zero]
  have := uFrameConj_one u₀ hjQ hstab p.snd
  rw [OneMemClass.coe_one] at this
  rw [this]
  rfl

omit hB hℓ hℓ0 h1 in
theorem dist_tnConj (γ : Γ) (p p' : WithLp 2 (ℝ × EuclideanSpace ℝ (Fin k))) :
    dist (tnConj ℓ₀ ℓ₁ j u₀ (γ : isom d) p) (tnConj ℓ₀ ℓ₁ j u₀ (γ : isom d) p') =
      dist p p' := by
  rw [WithLp.prod_dist_eq_of_L2, WithLp.prod_dist_eq_of_L2]
  unfold tnConj
  show √(dist (p.fst + _) (p'.fst + _) ^ 2 + dist (uFrameConj j u₀ (γ : isom d) p.snd)
    (uFrameConj j u₀ (γ : isom d) p'.snd) ^ 2) = _
  rw [dist_add_right, dist_uFrameConj u₀ hjQ hstab]

/-- `γ` on `ℝ × U`, as an isometry. -/
noncomputable def tnIso (γ : Γ) :
    WithLp 2 (ℝ × EuclideanSpace ℝ (Fin k)) ≃ᵢ WithLp 2 (ℝ × EuclideanSpace ℝ (Fin k)) where
  toFun := tnConj ℓ₀ ℓ₁ j u₀ (γ : isom d)
  invFun := tnConj ℓ₀ ℓ₁ j u₀ ((γ⁻¹ : Γ) : isom d)
  left_inv p := by
    rw [← tnConj_mul u₀ hjQ hstab hB hℓ hℓ0 h1, inv_mul_cancel,
      tnConj_one u₀ hjQ hstab hB]
  right_inv p := by
    rw [← tnConj_mul u₀ hjQ hstab hB hℓ hℓ0 h1, mul_inv_cancel,
      tnConj_one u₀ hjQ hstab hB]
  isometry_toFun := Isometry.of_dist_eq fun p p' => dist_tnConj u₀ hjQ hstab γ p p'

/-- **`Γ → Isom(ℝ × ℝᵏ)`**, `γ ↦ (log λ(γ), γ|_U)`. -/
noncomputable def tnHom :
    Γ →* (WithLp 2 (ℝ × EuclideanSpace ℝ (Fin k)) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × EuclideanSpace ℝ (Fin k)))
    where
  toFun γ := (tnIso u₀ hjQ hstab hB hℓ hℓ0 h1 γ).toRealAffineIsometryEquiv
  map_one' := by
    refine AffineIsometryEquiv.ext fun p => ?_
    rw [IsometryEquiv.coeFn_toRealAffineIsometryEquiv]
    exact tnConj_one u₀ hjQ hstab hB p
  map_mul' γ γ' := by
    refine AffineIsometryEquiv.ext fun p => ?_
    rw [AffineIsometryEquiv.coe_mul, Function.comp_apply,
      IsometryEquiv.coeFn_toRealAffineIsometryEquiv, IsometryEquiv.coeFn_toRealAffineIsometryEquiv,
      IsometryEquiv.coeFn_toRealAffineIsometryEquiv]
    exact tnConj_mul u₀ hjQ hstab hB hℓ hℓ0 h1 γ γ' p

theorem tnHom_apply (γ : Γ) (p : WithLp 2 (ℝ × EuclideanSpace ℝ (Fin k))) :
    tnHom u₀ hjQ hstab hB hℓ hℓ0 h1 γ p = tnConj ℓ₀ ℓ₁ j u₀ (γ : isom d) p := rfl

end TwoNull

/-- The displacement bound of the two-null case: with `|log c| ≤ R`,
`‖w + t((c⁻¹ − 1)ℓ₀ + (c − 1)ℓ₁)‖ ≤ ‖w‖-bound + |t|((eᴿ + 1)‖ℓ₀‖ + (eᴿ + 1)‖ℓ₁‖)`. -/
theorem twoNull_disp_bound {w ℓ₀ ℓ₁ : Minkowski d} {t₀ c R C : ℝ} (hpos : 0 < c)
    (hd1 : |Real.log c| ≤ R) (hw : ‖w‖ ≤ C) :
    ‖w + t₀ • ((c⁻¹ - 1) • ℓ₀ + (c - 1) • ℓ₁)‖ ≤
      C + |t₀| * ((Real.exp R + 1) * ‖ℓ₀‖ + (Real.exp R + 1) * ‖ℓ₁‖) := by
  have hc1 : c ≤ Real.exp R := by
    rw [← Real.exp_log hpos]; exact Real.exp_le_exp.2 (abs_le.1 hd1).2
  have hc0 : c⁻¹ ≤ Real.exp R := by
    rw [← Real.exp_log hpos, ← Real.exp_neg]
    exact Real.exp_le_exp.2 (by linarith [(abs_le.1 hd1).1])
  have hcinv : 0 < c⁻¹ := inv_pos.2 hpos
  have hb0 : |c⁻¹ - 1| ≤ Real.exp R + 1 := by
    rw [abs_le]; constructor <;> linarith [Real.exp_pos R]
  have hb1 : |c - 1| ≤ Real.exp R + 1 := by
    rw [abs_le]; constructor <;> linarith [Real.exp_pos R]
  calc ‖w + t₀ • ((c⁻¹ - 1) • ℓ₀ + (c - 1) • ℓ₁)‖
      ≤ ‖w‖ + ‖t₀ • ((c⁻¹ - 1) • ℓ₀ + (c - 1) • ℓ₁)‖ := norm_add_le _ _
    _ ≤ C + |t₀| * ((Real.exp R + 1) * ‖ℓ₀‖ + (Real.exp R + 1) * ‖ℓ₁‖) := by
      gcongr
      rw [norm_smul, Real.norm_eq_abs]
      gcongr
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
      gcongr

theorem abel_dist_L2_bound {k : ℕ} (x : WithLp 2 (ℝ × EuclideanSpace ℝ (Fin k))) (R : ℝ)
    (h : dist x 0 ≤ R) : |x.fst| ≤ R ∧ ‖x.snd‖ ≤ R := by
  rw [WithLp.prod_dist_eq_of_L2, WithLp.zero_fst, WithLp.zero_snd, Real.dist_eq, sub_zero,
    dist_zero_right, sq_abs] at h
  have hR : 0 ≤ R := (Real.sqrt_nonneg _).trans h
  have hsq := (Real.sqrt_le_left hR).1 h
  refine ⟨abs_le.2 (abs_le_of_sq_le_sq' (by nlinarith [sq_nonneg ‖x.snd‖]) hR),
    (sq_le_sq₀ (norm_nonneg _) hR).1 (by nlinarith [sq_nonneg x.fst])⟩

/-- **Cor 8.4 in the two-null case** (the shape of its use at [10.M], l.3313–3328): in §8's setting,
if `Γ` preserves a nonempty spacelike affine subspace `U` and **two distinct null directions**
`ℝℓ₀`, `ℝℓ₁` (`L(γ)` acts on them by `λ(γ)^{−1}`, `λ(γ)`), then `Γ` embeds as a discrete group of
isometries of `ℝ × U` (`γ ↦ (log λ(γ), γ|_U)`), hence has a finite-index subgroup isomorphic to
`ℤᵐ`, `m ≤ dim U + 1`. Conditional on `BieberbachI (ℝ × ℝ^{dim U})` (DEC-36). Here the printed
proof's "the action on `U` is free" is false (a pure boost fixes `U` pointwise); the boost
parameter is what restores injectivity. Neither `ℓᵢ ⊥ U` nor `dim U = d − 1` is needed. -/
theorem bcor_abel_twoNull {U : AffineSubspace ℝ (Minkowski d)}
    (hBi : BieberbachI (WithLp 2 (ℝ × EuclideanSpace ℝ (Fin (finrank ℝ U.direction)))))
    (h : CCAction Γ S) (hU : (U : Set (Minkowski d)).Nonempty) (hsp : IsSpacelikeAffine U)
    (hinv : ∀ γ ∈ Γ, ∀ x : Minkowski d, γ • x ∈ U ↔ x ∈ U) {ℓ₀ ℓ₁ : Minkowski d}
    (hℓ₀ : IsFutureCausal ℓ₀) (hℓ₁ : IsFutureCausal ℓ₁) (hq₀ : minkQ ℓ₀ = 0)
    (hq₁ : minkQ ℓ₁ = 0) (hB : minkB ℓ₁ ℓ₀ ≠ 0)
    (h0 : ∀ γ ∈ Γ, ∃ c : ℝ, linOf γ ℓ₀ = c • ℓ₀) (h1 : ∀ γ ∈ Γ, ∃ c : ℝ, linOf γ ℓ₁ = c • ℓ₁) :
    ∃ Γ' : Subgroup (isom d), Γ' ≤ Γ ∧ (Γ'.subgroupOf Γ).FiniteIndex ∧
      ∃ m ≤ finrank ℝ U.direction + 1, Nonempty (Additive Γ' ≃+ (Fin m →₀ ℤ)) := by
  have hℓ₀0 : ℓ₀ ≠ 0 := by rintro rfl; simp [minkB] at hB
  have hℓ₁0 : ℓ₁ ≠ 0 := by rintro rfl; simp [minkB] at hB
  -- the timelike line `u₀ + ℝ(ℓ₀ + ℓ₁)`
  have hBneg : minkB ℓ₁ ℓ₀ < 0 :=
    lt_of_le_of_ne (minkB_le_zero_of_isFutureCausal hℓ₁ hℓ₀) hB
  have hw : IsFutureTimelike (ℓ₀ + ℓ₁) := by
    refine ⟨?_, ?_⟩
    · have := abel_fst_pos_of_ne hℓ₀ hℓ₀0
      simp only [Prod.fst_add]; linarith [hℓ₁.1]
    · rw [minkQ_add, hq₀, hq₁, minkB_comm]; linarith
  obtain ⟨u₀, hu₀⟩ := hU
  obtain ⟨j, hjQ, hjW⟩ := exists_spacelike_frame U.direction hsp
  have hstab : ∀ γ ∈ Γ, ∀ y, ∃ y', j y' = γ • (u₀ + j y) - u₀ := by
    intro γ hγ y
    have hmem : u₀ + j y ∈ U := by
      have := AffineSubspace.vadd_mem_of_mem_direction ((hjW _).2 ⟨y, rfl⟩) hu₀
      rwa [vadd_eq_add, add_comm] at this
    exact (hjW _).1 (AffineSubspace.vsub_mem_direction ((hinv γ hγ _).2 hmem) hu₀)
  obtain ⟨t₀, ht₀⟩ := h.cc.entire.meets u₀ (ℓ₀ + ℓ₁) hw
  set s₀ := u₀ + t₀ • (ℓ₀ + ℓ₁)
  set Φ := tnHom u₀ hjQ hstab hB hℓ₁ hℓ₁0 h1
  have hΦ : ∀ γ : Γ, (Φ γ 0).fst = Real.log (eigOne ℓ₀ ℓ₁ (γ : isom d)) ∧
      j (Φ γ 0).snd = (γ : isom d) • u₀ - u₀ := fun γ => by
    refine ⟨by rw [tnHom_apply]; show (0 : ℝ) + _ = _; rw [zero_add], ?_⟩
    rw [tnHom_apply]
    show j (uFrameConj j u₀ (γ : isom d) 0) = _
    rw [apply_uFrameConj u₀ (hstab _ γ.2 0), map_zero, add_zero]
  have hγs : ∀ γ : Γ, (γ : isom d) • s₀ = (γ : isom d) • u₀ +
      t₀ • ((eigOne ℓ₀ ℓ₁ (γ : isom d))⁻¹ • ℓ₀ + eigOne ℓ₀ ℓ₁ (γ : isom d) • ℓ₁) := fun γ => by
    rw [isom_smul_add_smul, map_add, linOf_eq_inv_eigOne hB (h0 _ γ.2) (h1 _ γ.2),
      linOf_eq_eigOne hB (h1 _ γ.2)]
  have hinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_one]
    intro γ hγ
    obtain ⟨ha, hu⟩ := hΦ γ
    rw [hγ] at ha hu
    have hpos := eigOne_pos hB hℓ₁ hℓ₁0 (h1 _ γ.2)
    have hc : eigOne ℓ₀ ℓ₁ (γ : isom d) = 1 :=
      Real.eq_one_of_pos_of_log_eq_zero hpos (by rw [← ha]; rfl)
    have hu' : (γ : isom d) • u₀ = u₀ := by
      rw [← sub_eq_zero, ← hu]
      exact map_zero j
    by_contra hne
    refine h.free _ γ.2 (fun e => hne (Subtype.ext e)) s₀ ht₀ ?_
    rw [hγs, hc, inv_one, one_smul, one_smul, hu']
  have hdisc : IsDiscreteEucl Φ.range := by
    rw [isDiscreteEucl_iff_exists]
    refine ⟨0, fun R => ?_⟩
    let jc := LinearMap.toContinuousLinearMap j
    set R' := ‖jc‖ * R + |t₀| * ((Real.exp R + 1) * ‖ℓ₀‖ + (Real.exp R + 1) * ‖ℓ₁‖)
    have hfin := abel_finite_dist_le h ht₀ R'
    have hfin' : {γ : Γ | dist ((γ : isom d) • s₀) s₀ ≤ R'}.Finite :=
      (hfin.preimage Subtype.val_injective.injOn).subset fun γ hγ => ⟨γ.2, hγ⟩
    refine (hfin'.image Φ).subset ?_
    rintro g ⟨hg, hd⟩
    obtain ⟨γ, rfl⟩ := MonoidHom.mem_range.1 hg
    refine ⟨γ, ?_, rfl⟩
    obtain ⟨ha, hu⟩ := hΦ γ
    obtain ⟨hd1', hd2⟩ := abel_dist_L2_bound _ R hd
    have hd1 : |Real.log (eigOne ℓ₀ ℓ₁ (γ : isom d))| ≤ R := by rw [← ha]; exact hd1'
    have hR : 0 ≤ R := (abs_nonneg _).trans hd1
    have hpos := eigOne_pos hB hℓ₁ hℓ₁0 (h1 _ γ.2)
    have hdisp : (γ : isom d) • s₀ - s₀ = ((γ : isom d) • u₀ - u₀) +
        t₀ • (((eigOne ℓ₀ ℓ₁ (γ : isom d))⁻¹ - 1) • ℓ₀ + (eigOne ℓ₀ ℓ₁ (γ : isom d) - 1) • ℓ₁) := by
      rw [hγs]; simp only [s₀, sub_smul, one_smul, smul_add, smul_sub]; abel
    have hj : ‖(γ : isom d) • u₀ - u₀‖ ≤ ‖jc‖ * R := by
      rw [← hu]
      calc ‖j (Φ γ 0).snd‖ = ‖jc (Φ γ 0).snd‖ := rfl
        _ ≤ ‖jc‖ * ‖(Φ γ 0).snd‖ := jc.le_opNorm _
        _ ≤ ‖jc‖ * R := mul_le_mul_of_nonneg_left hd2 (norm_nonneg _)
    show dist ((γ : isom d) • s₀) s₀ ≤ R'
    rw [dist_eq_norm, hdisp]
    exact twoNull_disp_bound hpos hd1 hj
  have := virtuallyFree_of_injective_hom hBi Φ hinj hdisc
  have hrk : finrank ℝ (WithLp 2 (ℝ × EuclideanSpace ℝ (Fin (finrank ℝ U.direction)))) =
      finrank ℝ U.direction + 1 := by
    rw [(WithLp.linearEquiv 2 ℝ (ℝ × EuclideanSpace ℝ (Fin _))).finrank_eq, Module.finrank_prod,
      finrank_euclideanSpace_fin, Module.finrank_self, add_comm]
  rwa [hrk] at this

/-! #### The virtual and unified forms -/

/-- The standing hypotheses pass to subgroups (a private copy: `Flat/Nonloxodromic`'s public
`CCAction.mono` is not imported here). -/
private theorem abel_ccAction_mono {Γ₀ : Subgroup (isom d)} (h : CCAction Γ S) (hle : Γ₀ ≤ Γ) :
    CCAction Γ₀ S where
  cc := h.cc
  inv γ hγ := h.inv γ (hle hγ)
  free γ hγ := h.free γ (hle hγ)
  proper K hK hKc := (h.proper K hK hKc).subset fun _ hγ => ⟨hle hγ.1, hγ.2⟩

/-- Virtually `ℤᵐ` lifts through a finite-index subgroup. -/
private theorem abel_virtual_lift {Γ₀ : Subgroup (isom d)} (hle : Γ₀ ≤ Γ)
    (hfi : (Γ₀.subgroupOf Γ).FiniteIndex) {N : ℕ}
    (h : ∃ Γ' : Subgroup (isom d), Γ' ≤ Γ₀ ∧ (Γ'.subgroupOf Γ₀).FiniteIndex ∧
      ∃ m ≤ N, Nonempty (Additive Γ' ≃+ (Fin m →₀ ℤ))) :
    ∃ Γ' : Subgroup (isom d), Γ' ≤ Γ ∧ (Γ'.subgroupOf Γ).FiniteIndex ∧
      ∃ m ≤ N, Nonempty (Additive Γ' ≃+ (Fin m →₀ ℤ)) := by
  obtain ⟨Γ', hle', hfi', m, hm, e⟩ := h
  exact ⟨Γ', hle'.trans hle,
    ⟨Subgroup.relIndex_ne_zero_trans hfi'.index_ne_zero hfi.index_ne_zero⟩, m, hm, e⟩

/-- **Cor 8.4 repaired, virtual form** (unmarked): as `bcor_abel`, but only a **finite-index**
subgroup `Γ₀ ≤ Γ` is asked to preserve the timelike direction `Δ = ℝv`. Strictly more general
than `bcor_abel` (take `Γ₀ = Γ`). -/
theorem bcor_abel_virtual {U : AffineSubspace ℝ (Minkowski d)}
    (hB : BieberbachI (EuclideanSpace ℝ (Fin (finrank ℝ U.direction)))) (h : CCAction Γ S)
    (hU : (U : Set (Minkowski d)).Nonempty) (hsp : IsSpacelikeAffine U)
    (hinv : ∀ γ ∈ Γ, ∀ x : Minkowski d, γ • x ∈ U ↔ x ∈ U) {Γ₀ : Subgroup (isom d)}
    (hle : Γ₀ ≤ Γ) (hfi : (Γ₀.subgroupOf Γ).FiniteIndex) {v : Minkowski d}
    (hv : IsFutureTimelike v) (hΔ : ∀ γ ∈ Γ₀, ∃ c : ℝ, linOf γ v = c • v) :
    ∃ Γ' : Subgroup (isom d), Γ' ≤ Γ ∧ (Γ'.subgroupOf Γ).FiniteIndex ∧
      ∃ m ≤ finrank ℝ U.direction, Nonempty (Additive Γ' ≃+ (Fin m →₀ ℤ)) :=
  abel_virtual_lift hle hfi (bcor_abel hB (abel_ccAction_mono h hle) hU hsp
    (fun γ hγ => hinv γ (hle hγ)) hv hΔ)

/-- **Cor 8.4 in the two-null case, virtual form** (unmarked): as `bcor_abel_twoNull`, but only
a finite-index subgroup `Γ₀ ≤ Γ` is asked to preserve the two null directions. -/
theorem bcor_abel_twoNull_virtual {U : AffineSubspace ℝ (Minkowski d)}
    (hBi : BieberbachI (WithLp 2 (ℝ × EuclideanSpace ℝ (Fin (finrank ℝ U.direction)))))
    (h : CCAction Γ S) (hU : (U : Set (Minkowski d)).Nonempty) (hsp : IsSpacelikeAffine U)
    (hinv : ∀ γ ∈ Γ, ∀ x : Minkowski d, γ • x ∈ U ↔ x ∈ U) {Γ₀ : Subgroup (isom d)}
    (hle : Γ₀ ≤ Γ) (hfi : (Γ₀.subgroupOf Γ).FiniteIndex) {ℓ₀ ℓ₁ : Minkowski d}
    (hℓ₀ : IsFutureCausal ℓ₀) (hℓ₁ : IsFutureCausal ℓ₁) (hq₀ : minkQ ℓ₀ = 0)
    (hq₁ : minkQ ℓ₁ = 0) (hB : minkB ℓ₁ ℓ₀ ≠ 0)
    (h0 : ∀ γ ∈ Γ₀, ∃ c : ℝ, linOf γ ℓ₀ = c • ℓ₀) (h1 : ∀ γ ∈ Γ₀, ∃ c : ℝ, linOf γ ℓ₁ = c • ℓ₁) :
    ∃ Γ' : Subgroup (isom d), Γ' ≤ Γ ∧ (Γ'.subgroupOf Γ).FiniteIndex ∧
      ∃ m ≤ finrank ℝ U.direction + 1, Nonempty (Additive Γ' ≃+ (Fin m →₀ ℤ)) :=
  abel_virtual_lift hle hfi (bcor_abel_twoNull hBi (abel_ccAction_mono h hle) hU hsp
    (fun γ hγ => hinv γ (hle hγ)) hℓ₀ hℓ₁ hq₀ hq₁ hB h0 h1)

/-- **Cor 8.4 repaired, unified form** (unmarked; the REPORT's open question): in §8's setting,
if `Γ` preserves a nonempty spacelike affine subspace `U` and some finite-index `Γ₀ ≤ Γ` preserves
**either** a timelike direction **or** two distinct null directions, then `Γ` has a finite-index
subgroup isomorphic to `ℤᵐ`, `m ≤ dim U + 1`. Conditional on `BieberbachI` in dimensions `dim U`
and `dim U + 1` (DEC-36). This covers both shapes Barbot's uses need ([10.M] is the null case);
it does not cover Prop 10.4 (non-elementary `L(Γ)`, where the conclusion fails: `Γ₄`). -/
theorem bcor_abel_unified {U : AffineSubspace ℝ (Minkowski d)}
    (hB : BieberbachI (EuclideanSpace ℝ (Fin (finrank ℝ U.direction))))
    (hBi : BieberbachI (WithLp 2 (ℝ × EuclideanSpace ℝ (Fin (finrank ℝ U.direction)))))
    (h : CCAction Γ S) (hU : (U : Set (Minkowski d)).Nonempty) (hsp : IsSpacelikeAffine U)
    (hinv : ∀ γ ∈ Γ, ∀ x : Minkowski d, γ • x ∈ U ↔ x ∈ U) {Γ₀ : Subgroup (isom d)}
    (hle : Γ₀ ≤ Γ) (hfi : (Γ₀.subgroupOf Γ).FiniteIndex)
    (hdir : (∃ v : Minkowski d, IsFutureTimelike v ∧ ∀ γ ∈ Γ₀, ∃ c : ℝ, linOf γ v = c • v) ∨
      ∃ ℓ₀ ℓ₁ : Minkowski d, IsFutureCausal ℓ₀ ∧ IsFutureCausal ℓ₁ ∧ minkQ ℓ₀ = 0 ∧
        minkQ ℓ₁ = 0 ∧ minkB ℓ₁ ℓ₀ ≠ 0 ∧ (∀ γ ∈ Γ₀, ∃ c : ℝ, linOf γ ℓ₀ = c • ℓ₀) ∧
        ∀ γ ∈ Γ₀, ∃ c : ℝ, linOf γ ℓ₁ = c • ℓ₁) :
    ∃ Γ' : Subgroup (isom d), Γ' ≤ Γ ∧ (Γ'.subgroupOf Γ).FiniteIndex ∧
      ∃ m ≤ finrank ℝ U.direction + 1, Nonempty (Additive Γ' ≃+ (Fin m →₀ ℤ)) := by
  rcases hdir with ⟨v, hv, hΔ⟩ | ⟨ℓ₀, ℓ₁, hℓ₀, hℓ₁, hq₀, hq₁, hBℓ, h0, h1⟩
  · obtain ⟨Γ', hle', hfi', m, hm, e⟩ := bcor_abel_virtual hB h hU hsp hinv hle hfi hv hΔ
    exact ⟨Γ', hle', hfi', m, hm.trans (Nat.le_succ _), e⟩
  · exact bcor_abel_twoNull_virtual hBi h hU hsp hinv hle hfi hℓ₀ hℓ₁ hq₀ hq₁ hBℓ h0 h1

end TrueForm

end Causal.Flat
