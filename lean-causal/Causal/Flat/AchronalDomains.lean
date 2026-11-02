import Causal.Flat.Isometries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# `Causal.Flat.AchronalDomains` — Barbot §7, the achronal domains of isometries

T. Barbot, *Globally hyperbolic flat space-times* (`papers/barbot`, arXiv math/0402257), §7
(`GHFspace.tex` l.2019–2210 of the labelled file). The one ledger label:

* **`blem:paranongh`** — `GHFspace.tex:2174` (Lemma 7.1, l.2173–2180), marked in its
  **class-by-class corrected form** (DEC-98; **no `sorry`**) — `paranongh_corrected`. The printed
  statement is **false** for `n ≥ 4` (with `R = id` parabolic) and for `n ≥ 6` (with `R ≠ id`
  required); the counterexamples and the exact range of dimensions are proved and kept as
  findings (SCOPE).

The prose items are cited unmarked: [7.0] the definition (l.2022–2028), [7.E] (l.2029–2053), [7.L] (l.2055–2082), [7.P]
(l.2084–2163).

> For any isometry `g`, we define its achronal domain `Ω_g` by:
> `Ω_g = { x ∈ 𝐌ⁿ / ∀ q ∈ ℤ, |gᵠ(x) − x|² > 0 }`. It is the open set formed by the elements
> which are not causally related to any `g`-iterates of themselves. (l.2022–2027)

> `τ` is timelike: Then, `Ω_g = ∅` […]. `τ` is spacelike: Then, `Ω_g = 𝐌ⁿ`. `τ` is lightlike:
> Then, the complement of `Ω_g` is the subspace formed by `R`-periodic points, i.e., the
> `Rⁿ`-fixed points. (l.2041–2049)

> where `λ = e^{ζ/2}` […] `= q²|τ|² − 4 sh²(qζ) xy + ‖(R^q − id)(v)‖²`. The leading term
> `− 4 sh²(qζ) xy` ensures: `Ω_g = { (x,y,v) / xy < 0 }` (l.2068–2081)

> the complement of `Ω_g` is the set of `Rⁿ`-fixed points in the hyperplane `J^⊥` (l.2119–2120)
> […] in the tangent case, `Ω_g` is the entire `𝐌ⁿ` (l.2137–2138) […] Conclusion: `Ω_g` is
> empty. (l.2163)

> **Lemma 7.1** Let `g` be a parabolic isometry. Let `x₀` be any point of `𝐌ⁿ`. Then, there
> exist at least one point `x` in `𝐌ⁿ` admitting infinitely many `g`-iterates in the future or
> in the past of `x₀`. (l.2173–2180)

> with `p` nilpotent and `R` a non-trivial elliptic element of `SO₀(1,n−1)`. (l.1973–1974)

**Dimension (kb/0024).** Barbot's `𝐌ⁿ` has total dimension `n`; `Minkowski d` has `d` spatial
dimensions, so Barbot's `n` is `d + 1`. "Causally related" is the ETT causality
`(minkowski d).le ⊤` in either direction (`CausallyRelated`, read through `le_top_iff_minkQ`).
`linOf g` is `Form`'s `linearPart g` (`linOf_eq_linearPart`), `trOf g` is `τ`.

* [7.0] `achronalDomain` (`q ≠ 0`; as printed it is empty: `achronalDomainPrinted_eq_empty`),
  `mem_achronalDomain_iff`, `mem_achronalDomain_conj` (`Ω_{hgh⁻¹} = h Ω_g`), `IsAperiodic`.
* [7.E] `achronalDomain_elliptic_timelike` (`∅`), `_spacelike` (`𝐌ⁿ`), `_lightlike`,
  `_lightlike_eq_compl_ker` (`exists_periodic_iff`), `_lightlike_of_pow_eq_one`;
  `isOpen_achronalDomain_elliptic`. Witnesses `achronalDomain_isomTrans_timeUnit`, `_spaceUnit`,
  `_null`.
* [7.L] (`nullXY` = `xy`, `nullV` = `v`): `mem_achronalDomain_lox_iff`,
  `achronalDomain_lox_of_ne_zero` (`{xy ≤ 0}`), `achronalDomain_lox_of_eq_zero`,
  `interior_achronalDomain_lox` (`{xy < 0}`), `isOpen_achronalDomain_lox_iff`,
  `lox_exists_fixed_iff`, `achronalDomain_isLoxodromic`; witnesses `boostShift_not_isOpen`,
  `boostIsom_isOpen`.
* [7.P] `pow_smul_parabolic`, `achronalDomain_parabolic_linear`, `_tangent` (`𝐌ⁿ`),
  `_transverse` (`∅`), `isOpen_achronalDomain_parabolic`; witnesses `achronalDomain_nullRotIsom`,
  `achronalDomain_nullRotTime`, `achronalDomain_nullRotShift`.
* `blem:paranongh`: `Paranongh`/`ParanonghPts` (counting `q` / points), **`paranongh_iff`,
  `paranonghPts_iff` (`↔ d ≤ 2`)**; `paranongh_transverse`, `paranongh_linear` (any `x₀`),
  `paranongh_tangent` (`x₀ ∉ c + J^⊥`, fails at `c`); counterexamples `nullRotShift` (`R = id`,
  `not_paranongh`, `d ≥ 3`), `halfTurnShift` (`R ≠ id`, `not_paranonghStrict`, `d ≥ 5`).

## Hypothesis checklist
| paper hypothesis | here |
|---|---|
| `Ω_g`: `∀ q ∈ ℤ` (l.2024) | ⚠ strengthened (reading): `q ≠ 0`; as printed `Ω_g = ∅` (finding, question) |
| `Ω_g` "is the open set" (l.2026) | ⚠ strengthened (finding): open for every elliptic and parabolic `g`; loxodromic in normal form: open iff `τ = 0` and `L(g)` of finite order on the frame's orthogonal |
| [7.E] `g x = R x + τ`, `R` fixing `τ` (l.2031) | ✓ carried (`IsElliptic.exists_transConj_fixed`); "`Rⁿ`-fixed" (l.2049) read `R^N`, one `N > 0` |
| [7.L] `L(g)(x,y,v) = (λx, λ⁻¹y, Rv)`, `τ ∈ ℝⁿ⁻²` (l.2063–2069) | ⚠ weakened: null eigenvectors `u, u'` (`λ, λ⁻¹`, `0 < λ ≠ 1`), `L(g) τ = τ` |
| [7.L] `Ω_g = {xy < 0}` (l.2081) | ⚠ strengthened (finding): true of `int Ω_g`; `Ω_g = {xy ≤ 0}` when `τ ≠ 0` (no fixed point) |
| [7.P] `R ∘ p = p`, `τ` fixed by `R`, `τ ⊥ v₁` (l.2091–2093) | ⚠ weakened: `R τ = τ` only |
| parabolic: `R` non-trivial (l.1974) | ⚠ weakened (reading of `Flat/Isometries`): `R = id` admitted, as §9's purely unipotent case (l.2865) needs; the strict reading is `IsParabolicNontrivR` |
| parabolic: `U ≠ id` | ⚠ strengthened (reading of `Flat/Isometries`) |
| `blem:paranongh` (**marked**, DEC-98): `g` parabolic, any `x₀` | ⚠ statement change, the corrected form of record (DEC-98): `paranongh_corrected` — transverse and linear parabolic `g`: every `x₀`; tangent parabolic `g`: every `x₀ ∉ c + J^⊥`, and it fails at `x₀ = c`. The printed form (`Paranongh`, `ParanonghPts`) is false for `d ≥ 3` (`R = id`, `not_paranongh`), for `d ≥ 5` (`R ≠ id`, `not_paranonghStrict`), true exactly for `d ≤ 2` (`paranongh_iff`): **findings** |
| `blem:paranongh`: "parabolic" | ⚠ reading: a decomposition `L(g) = R U` (`R` elliptic, `U ≠ id` unipotent, commuting), `R = id` admitted (as §9's purely unipotent case l.2865 needs); the class (linear / tangent / transverse) is relative to it (`linear_or_tangent_or_transverse`), and `J^⊥` does not depend on it (`mem_nullHyperplanes_iff`, `Flat/Develop`) |
| "infinitely many `g`-iterates" (l.2177) | ⚠ strengthened (reading, question): both counts proved; positive results give distinct points |
| "in the future or in the past of `x₀`" | ✓ carried: `CausallyRelated` (causal, either direction) |

## SCOPE (disclosed)
* **Ruled DEC-98 (2026-11-02):** the class-by-class corrected form `paranongh_corrected` is the
  formalization of record and `blem:paranongh` is marked; the counterexamples stay as findings.
* No `sorry`. **Finding:** `blem:paranongh` as printed is refuted for `d ≥ 3` (`not_paranongh`,
  `not_paranonghPts`; counterexample `nullRotShift`, `R = id`, which `IsParabolic` admits) and,
  with "parabolic" read as in §6.2 (`R ≠ id`, l.1974), for `d ≥ 5` (`not_paranonghStrict`,
  `halfTurnShift`). In the strict reading `d = 3, 4` is NOT decided here: a tangent `g` needs
  `R` to fix the 4-dimensional `I + ⟨vₙ⟩ + ⟨τ⟩`, which with `det R = 1` forces `R = id` for
  `d ≤ 4`, so the lemma would hold there (dimension count, not formalized).
* Readings: `q ≠ 0` in `Ω_g`; "`Rⁿ`-fixed" as `R^N` (`exists_periodic_iff`); "infinitely many
  `g`-iterates" both as infinitely many exponents (`Paranongh`) and as infinitely many distinct
  points (`ParanonghPts`); "causally related" as causal (`≤ 0`), not timelike.
* [7.E], [7.L], [7.P] are stated in Barbot's normal forms; conjugation by a translation moves `Ω_g`
  (`mem_achronalDomain_isomConj`) and the visibility sets (`visibility_isomConj`), which carries
  openness and `paranongh_linear`, `_transverse`, `_tangent` to the whole class. The
  [7.L] statements are relative to a given null frame; `achronalDomain_isLoxodromic` supplies one.
* Tangent case: the lemma holds for every `x₀ ∉ c + J^⊥` and fails at `x₀ = c`; whether it fails
  on all of `c + J^⊥` is not proved. A loxodromic witness with `τ = 0` and non-open `Ω_g` (an
  irrational rotation, `d ≥ 3`) is not formalized; the open one is `boostIsom_isOpen`.
* The classes are those of `Flat/Isometries`, whose trichotomy (`lorentz_trichotomy`) was a
  `sorry` there when this file was written and is proved since (no `sorry`); no statement
  here uses it (axioms: `propext`, `Classical.choice`, `Quot.sound`).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. WP-30e (wave 1b of the
Barbot campaign, DEC-34).
-/

namespace Causal.Flat

open Module Submodule Filter Topology

variable {d : ℕ}

/-! ### Notation for an isometry: `L(g)` and `τ` -/

/-- Barbot's `L(g)`, as a linear equivalence. -/
noncomputable abbrev linOf (g : isom d) : Minkowski d ≃ₗ[ℝ] Minkowski d :=
  (g : Minkowski d ≃ᵃ[ℝ] Minkowski d).linear

/-- Barbot's translation part `τ` of `g`, read in the origin chart. -/
noncomputable abbrev trOf (g : isom d) : Minkowski d :=
  transPart (g : Minkowski d ≃ᵃ[ℝ] Minkowski d)

theorem linOf_mem (g : isom d) : linOf g ∈ lorentz d := g.2

/-- `linOf g` is `Form`'s `linearPart g` (Barbot's `L`), read as a linear equivalence; the abbrev
only saves the coercion. -/
theorem linOf_eq_linearPart (g : isom d) :
    linOf g = (linearPart g : Minkowski d ≃ₗ[ℝ] Minkowski d) :=
  LinearEquiv.ext fun v => (linearPart_apply g v).symm

theorem smul_eq_lin_add (g : isom d) (x : Minkowski d) : g • x = linOf g x + trOf g := by
  rw [isom_smul_def]; exact apply_eq_linear_add_transPart _ x

/-! ### Powers of a `minkQ`-preserving linear map -/

section pow

variable {A : Minkowski d ≃ₗ[ℝ] Minkowski d}

theorem linEquiv_pow_succ_apply (A : Minkowski d ≃ₗ[ℝ] Minkowski d) (n : ℕ) (x : Minkowski d) :
    (A ^ (n + 1)) x = A ((A ^ n) x) := by
  rw [pow_succ', LinearEquiv.mul_apply]

theorem minkQ_pow_apply (hA : ∀ v, minkQ (A v) = minkQ v) (n : ℕ) (v : Minkowski d) :
    minkQ ((A ^ n) v) = minkQ v := by
  induction n with
  | zero => rfl
  | succ n ih => rw [linEquiv_pow_succ_apply, hA, ih]

theorem minkB_pow_apply (hA : ∀ v, minkQ (A v) = minkQ v) (n : ℕ) (v w : Minkowski d) :
    minkB ((A ^ n) v) ((A ^ n) w) = minkB v w :=
  minkB_map (minkQ_pow_apply hA n) v w

theorem pow_apply_eq_self {u : Minkowski d} (h : A u = u) (n : ℕ) : (A ^ n) u = u := by
  induction n with
  | zero => rfl
  | succ n ih => rw [linEquiv_pow_succ_apply, ih, h]

/-- `Aⁿ x − x` is orthogonal to every vector fixed by `A`. -/
theorem minkB_pow_sub_fixed (hA : ∀ v, minkQ (A v) = minkQ v) {f : Minkowski d} (hf : A f = f)
    (n : ℕ) (x : Minkowski d) : minkB ((A ^ n) x - x) f = 0 := by
  rw [minkB_sub_left, ← minkB_pow_apply hA n x f, pow_apply_eq_self hf n, sub_self]

end pow

/-! ### Elementary facts on the form -/

theorem minkQ_nonneg_of_orth_timelike {u y : Minkowski d} (hu : minkQ u < 0)
    (h : minkB u y = 0) : 0 ≤ minkQ y := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  · exact (minkQ_pos_of_orth_timelike hu h hy).le

theorem minkQ_parallelogram (a b : Minkowski d) :
    minkQ (a - b) + minkQ (a + b) = 2 * minkQ a + 2 * minkQ b := by
  rw [sub_eq_add_neg, minkQ_add, minkQ_add, minkQ_neg, minkB_neg_right]; ring

/-- `minkQ` of a combination of three vectors. -/
theorem minkQ_smul_add3 (a b c : ℝ) (P Q T : Minkowski d) :
    minkQ (a • P + b • Q + c • T) = a ^ 2 * minkQ P + b ^ 2 * minkQ Q + c ^ 2 * minkQ T +
      2 * a * b * minkB P Q + 2 * a * c * minkB P T + 2 * b * c * minkB Q T := by
  simp only [minkQ_add, minkQ_smul, minkB_add_left, minkB_smul_left, minkB_smul_right]; ring

/-- A vector with `minkQ v ≤ 0` joins two causally related points, in one direction or the
other. -/
theorem le_top_or_of_minkQ_nonpos {x y : Minkowski d} (h : minkQ (y - x) ≤ 0) :
    (minkowski d).le ⊤ x y ∨ (minkowski d).le ⊤ y x := by
  rw [le_top_iff_minkQ, le_top_iff_minkQ]
  rcases le_total 0 (y - x).1 with h0 | h0
  · exact Or.inl ⟨h0, h⟩
  · refine Or.inr ⟨?_, ?_⟩
    · have : (x - y).1 = -(y - x).1 := by simp
      rw [this]; linarith
    · rw [show x - y = -(y - x) by abel, minkQ_neg]; exact h

/-! ### Elliptic linear parts: the bounded part `(Aⁿ − id) x` -/

section ellipticBound

variable {A : Minkowski d ≃ₗ[ℝ] Minkowski d} (hA : ∀ v, minkQ (A v) = minkQ v)
  {u : Minkowski d} (hu : minkQ u < 0) (hAu : A u = u)
include hA hAu

theorem minkB_fixed_pow_sub (n : ℕ) (x : Minkowski d) : minkB u ((A ^ n) x - x) = 0 := by
  rw [minkB_comm]; exact minkB_pow_sub_fixed hA hAu n x

include hu

/-- `minkQ ((Aⁿ − id) x) ≥ 0` when `A` fixes a timelike vector. -/
theorem minkQ_pow_sub_nonneg (n : ℕ) (x : Minkowski d) : 0 ≤ minkQ ((A ^ n) x - x) :=
  minkQ_nonneg_of_orth_timelike hu (minkB_fixed_pow_sub hA hAu n x)

/-- … with equality only at the fixed points of `Aⁿ`. -/
theorem pow_apply_eq_of_minkQ_eq_zero {n : ℕ} {x : Minkowski d}
    (h : minkQ ((A ^ n) x - x) = 0) : (A ^ n) x = x := by
  by_contra hne
  have := minkQ_pos_of_orth_timelike hu (minkB_fixed_pow_sub hA hAu n x) (sub_ne_zero.2 hne)
  linarith

/-- **`(Aⁿ − id) x` is bounded** (l.2043: "`(R^q − id)(x)` is uniformly bounded"): measured by
`minkQ`, which is a euclidean norm on `u^⊥`. -/
theorem minkQ_pow_sub_le (x : Minkowski d) : ∃ C, ∀ n : ℕ, minkQ ((A ^ n) x - x) ≤ C := by
  set w := x - (minkB u x / minkQ u) • u with hwdef
  have hw : minkB u w = 0 := by
    rw [hwdef, minkB_sub_right, minkB_smul_right, ← minkQ_eq_minkB, div_mul_cancel₀ _ hu.ne,
      sub_self]
  refine ⟨4 * minkQ w, fun n => ?_⟩
  have e : (A ^ n) x - x = (A ^ n) w - w := by
    rw [hwdef, map_sub, map_smul, pow_apply_eq_self hAu n]; abel
  have hwn : minkB u ((A ^ n) w) = 0 := by
    have h1 := minkB_pow_apply hA n u w
    rw [pow_apply_eq_self hAu n] at h1
    rw [h1, hw]
  have hsum : 0 ≤ minkQ ((A ^ n) w + w) :=
    minkQ_nonneg_of_orth_timelike hu (by rw [minkB_add_right, hwn, hw, add_zero])
  have hpar := minkQ_parallelogram ((A ^ n) w) w
  rw [minkQ_pow_apply hA] at hpar
  rw [e]; linarith

end ellipticBound

/-! ### The periodic points of a linear map form a subspace -/

/-- **The periodic points of `A` are the fixed points of one power `A^N`** (`N > 0`): the
subspaces `ker (A^{k!} − id)` increase and stabilise. This is l.2049's "the subspace formed by
`R`-periodic points, i.e. the `Rⁿ`-fixed points", with `n` read as this `N`. -/
theorem exists_periodic_iff (A : Minkowski d ≃ₗ[ℝ] Minkowski d) :
    ∃ N : ℕ, 0 < N ∧ ∀ x, (∃ n : ℕ, 0 < n ∧ (A ^ n) x = x) ↔ (A ^ N) x = x := by
  have hmul : ∀ a b : ℕ, ∀ x, (A ^ a) x = x → (A ^ (a * b)) x = x := fun a b x h => by
    rw [pow_mul]; exact pow_apply_eq_self h b
  let f : ℕ →o Submodule ℝ (Minkowski d) :=
    ⟨fun k => LinearMap.ker (pOf (A ^ k.factorial)), fun k m hkm x hx => by
      simp only [LinearMap.mem_ker, pOf_apply, sub_eq_zero] at hx ⊢
      obtain ⟨j, hj⟩ := Nat.factorial_dvd_factorial hkm
      rw [hj]; exact hmul _ _ _ hx⟩
  obtain ⟨n, hn⟩ := (monotone_stabilizes_iff_noetherian (R := ℝ) (M := Minkowski d)).2
    inferInstance f
  have mem_f : ∀ k x, x ∈ f k ↔ (A ^ k.factorial) x = x := fun k x => by
    show x ∈ LinearMap.ker (pOf (A ^ k.factorial)) ↔ _
    rw [LinearMap.mem_ker, pOf_apply, sub_eq_zero]
  refine ⟨n.factorial, Nat.factorial_pos n, fun x => ⟨?_, fun h => ⟨_, Nat.factorial_pos n, h⟩⟩⟩
  rintro ⟨q, hq, hx⟩
  have h1 : x ∈ f q := by
    rw [mem_f]
    obtain ⟨j, hj⟩ := Nat.dvd_factorial hq le_rfl
    rw [hj]; exact hmul _ _ _ hx
  have h2 : x ∈ f (max n q) := f.monotone (le_max_right n q) h1
  rw [← hn (max n q) (le_max_left n q), mem_f] at h2
  exact h2

/-! ### The achronal domain -/

/-- **The achronal domain** `Ω_g` (l.2022–2025), read with `q ≠ 0`: the points not causally
related to any of their nontrivial `g`-iterates. -/
def achronalDomain (g : isom d) : Set (Minkowski d) :=
  {x | ∀ q : ℤ, q ≠ 0 → 0 < minkQ ((g ^ q) • x - x)}

/-- The set as printed (l.2024: `∀ q ∈ ℤ`, the term `q = 0` included). -/
def achronalDomainPrinted (g : isom d) : Set (Minkowski d) :=
  {x | ∀ q : ℤ, 0 < minkQ ((g ^ q) • x - x)}

/-- **As printed, `Ω_g` is empty** (`q = 0` gives `|x − x|² = 0`): the reading `q ≠ 0` is
forced. -/
theorem achronalDomainPrinted_eq_empty (g : isom d) : achronalDomainPrinted g = ∅ := by
  ext x
  simp only [achronalDomainPrinted, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  intro h
  have := h 0
  simp at this

/-- `Ω_g` is read on positive iterates (`g^{−n}` is `g^n` seen from the other end). -/
theorem mem_achronalDomain_iff {g : isom d} {x : Minkowski d} :
    x ∈ achronalDomain g ↔ ∀ n : ℕ, 0 < n → 0 < minkQ ((g ^ n) • x - x) := by
  refine ⟨fun h n hn => by simpa using h n (by exact_mod_cast hn.ne'), fun h q hq => ?_⟩
  rcases Int.eq_nat_or_neg q with ⟨n, rfl | rfl⟩
  · have hn : 0 < n := by omega
    simpa using h n hn
  · have hn : 0 < n := by omega
    have e := isom_minkQ_sub (g ^ n) x ((g ^ n)⁻¹ • x)
    rw [smul_inv_smul, show x - (g ^ n) • x = -((g ^ n) • x - x) by abel, minkQ_neg] at e
    rw [zpow_neg, zpow_natCast, ← e]
    exact h n hn

/-- **Conjugation moves `Ω_g`**: `Ω_{h g h⁻¹} = h(Ω_g)`. -/
theorem mem_achronalDomain_conj (h g : isom d) (x : Minkowski d) :
    x ∈ achronalDomain (h * g * h⁻¹) ↔ h⁻¹ • x ∈ achronalDomain g := by
  have key : ∀ q : ℤ, minkQ (((h * g * h⁻¹) ^ q) • x - x) =
      minkQ ((g ^ q) • (h⁻¹ • x) - h⁻¹ • x) := fun q => by
    rw [conj_zpow, mul_smul, mul_smul]
    conv_lhs => rw [show x = h • (h⁻¹ • x) from (smul_inv_smul h x).symm]
    rw [inv_smul_smul, isom_minkQ_sub]
  simp only [achronalDomain, Set.mem_setOf_eq, key]

/-- The translation of vector `v`, as an isometry. -/
noncomputable def isomTrans (v : Minkowski d) : isom d :=
  ⟨AffineEquiv.constVAdd ℝ (Minkowski d) v, constVAdd_mem_isom v⟩

/-- `g` conjugated by the translation of vector `v` (Isometries' `transConj`), as an isometry. -/
noncomputable def isomConj (v : Minkowski d) (g : isom d) : isom d :=
  ⟨transConj v g, transConj_mem_isom g.2⟩

theorem isomConj_eq (v : Minkowski d) (g : isom d) :
    isomConj v g = isomTrans v * g * (isomTrans v)⁻¹ := rfl

@[simp] theorem linOf_isomConj (v : Minkowski d) (g : isom d) :
    linOf (isomConj v g) = linOf g := linear_transConj v _

theorem trOf_isomConj (v : Minkowski d) (g : isom d) :
    trOf (isomConj v g) = trOf g - pOf (linOf g) v := transPart_transConj v _

theorem mem_achronalDomain_isomConj (v : Minkowski d) (g : isom d) (x : Minkowski d) :
    x ∈ achronalDomain (isomConj v g) ↔ -v + x ∈ achronalDomain g := by
  rw [isomConj_eq, mem_achronalDomain_conj]; rfl

theorem achronalDomain_eq_preimage_isomConj (v : Minkowski d) (g : isom d) :
    achronalDomain g = (fun x => v + x) ⁻¹' achronalDomain (isomConj v g) := by
  ext x
  rw [Set.mem_preimage, mem_achronalDomain_isomConj, neg_add_cancel_left]

theorem isOpen_achronalDomain_of_isomConj {v : Minkowski d} {g : isom d}
    (h : IsOpen (achronalDomain (isomConj v g))) : IsOpen (achronalDomain g) := by
  rw [achronalDomain_eq_preimage_isomConj v g]
  exact h.preimage (continuous_const.add continuous_id)

/-- `x` is **not periodic** under `g`: its nontrivial iterates are other points. This is what
separates "infinitely many `q`" from "infinitely many iterates" in `blem:paranongh`. -/
def IsAperiodic (g : isom d) (x : Minkowski d) : Prop := ∀ q : ℤ, q ≠ 0 → (g ^ q) • x ≠ x

/-- A point of `Ω_g` is not periodic. -/
theorem isAperiodic_of_mem_achronalDomain {g : isom d} {x : Minkowski d}
    (h : x ∈ achronalDomain g) : IsAperiodic g x := fun q hq he => by
  have := h q hq
  rw [he, sub_self, minkQ_zero] at this
  exact lt_irrefl _ this

/-- A point whose large positive iterates all differ from it is not periodic. -/
theorem isAperiodic_of_eventually {g : isom d} {x : Minkowski d} {N : ℕ}
    (h : ∀ n : ℕ, N ≤ n → (g ^ n) • x ≠ x) : IsAperiodic g x := by
  intro q hq he
  have hst : g ^ q ∈ MulAction.stabilizer (isom d) x := he
  have hm : g ^ q.natAbs ∈ MulAction.stabilizer (isom d) x := by
    rw [← zpow_natCast]
    rcases Int.natAbs_eq q with h' | h'
    · rw [h'] at hst; exact hst
    · rw [h', zpow_neg] at hst; exact inv_mem_iff.1 hst
  have hpos : 0 < q.natAbs := Int.natAbs_pos.2 hq
  have h2 : g ^ (q.natAbs * (N + 1)) ∈ MulAction.stabilizer (isom d) x := by
    rw [pow_mul]; exact (MulAction.stabilizer (isom d) x).pow_mem hm (N + 1)
  exact h (q.natAbs * (N + 1)) (by nlinarith) h2

/-- **Distinct iterates**: for a non-periodic `x`, `q ↦ gᵠ x` is injective, so infinitely many
exponents give infinitely many points. -/
theorem infinite_image_of_isAperiodic {g : isom d} {x : Minkowski d} (hx : IsAperiodic g x)
    {S : Set ℤ} (hS : S.Infinite) : ((fun q : ℤ => (g ^ q) • x) '' S).Infinite := by
  refine (Set.infinite_image_iff fun a _ b _ hab => ?_).2 hS
  by_contra hne
  apply hx (a - b) (sub_ne_zero.2 hne)
  have e : g ^ (a - b) = (g ^ b)⁻¹ * g ^ a := by
    rw [← zpow_neg, ← zpow_add]; congr 1; ring
  have hab' : (g ^ a) • x = (g ^ b) • x := hab
  rw [e, mul_smul, hab', inv_smul_smul]

/-- Non-periodicity moves along a conjugation by a translation. -/
theorem isAperiodic_isomConj (v : Minkowski d) (g : isom d) (x : Minkowski d) :
    IsAperiodic (isomConj v g) x ↔ IsAperiodic g (-v + x) := by
  have key : ∀ q : ℤ, (isomConj v g ^ q) • x = x ↔ (g ^ q) • (-v + x) = -v + x := fun q => by
    rw [isomConj_eq, conj_zpow, mul_smul, mul_smul, smul_eq_iff_eq_inv_smul]
    rfl
  unfold IsAperiodic
  exact forall₂_congr fun q _ => not_congr (key q)

/-! ### Iterates when `τ` is fixed by `L(g)` -/

section fixedTau

variable {g : isom d} (hτ : linOf g (trOf g) = trOf g)
include hτ

/-- `gⁿ x = L(g)ⁿ x + n τ` when `L(g) τ = τ`. -/
theorem pow_smul_of_fixed (n : ℕ) (x : Minkowski d) :
    (g ^ n) • x = (linOf g ^ n) x + (n : ℝ) • trOf g := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', mul_smul, ih, smul_eq_lin_add, map_add, map_smul, hτ,
      linEquiv_pow_succ_apply]
    push_cast; module

/-- **`|gⁿx − x|² = |(L(g)ⁿ − id) x|² + n² |τ|²`** when `L(g) τ = τ` (l.2033–2035, l.2072). -/
theorem minkQ_pow_smul_sub_of_fixed (n : ℕ) (x : Minkowski d) :
    minkQ ((g ^ n) • x - x) = minkQ ((linOf g ^ n) x - x) + (n : ℝ) ^ 2 * minkQ (trOf g) := by
  rw [pow_smul_of_fixed hτ, show (linOf g ^ n) x + (n : ℝ) • trOf g - x =
    ((linOf g ^ n) x - x) + (n : ℝ) • trOf g by abel, minkQ_add, minkQ_smul, minkB_smul_right,
    minkB_pow_sub_fixed (linOf_mem g).1 hτ]
  ring

end fixedTau

/-! ### [7.E] The elliptic case (l.2029–2053) -/

section elliptic

variable {g : isom d} (hE : IsElliptic (linOf g)) (hτ : linOf g (trOf g) = trOf g)
include hE hτ

/-- **[7.E], `τ` timelike: `Ω_g = ∅`** (l.2041–2043): `q² |τ|²` dominates the bounded term. -/
theorem achronalDomain_elliptic_timelike (h : minkQ (trOf g) < 0) : achronalDomain g = ∅ := by
  obtain ⟨u, hu, hAu⟩ := hE.exists_fixed_timelike (linOf_mem g)
  refine Set.eq_empty_iff_forall_notMem.2 fun x hx => ?_
  obtain ⟨C, hC⟩ := minkQ_pow_sub_le (linOf_mem g).1 hu.2 hAu x
  set n : ℕ := ⌈C / (-minkQ (trOf g))⌉₊ + 1
  have hn : 0 < n := Nat.succ_pos _
  have h1 := mem_achronalDomain_iff.1 hx n hn
  rw [minkQ_pow_smul_sub_of_fixed hτ] at h1
  have hC' := hC n
  have hnr : C / (-minkQ (trOf g)) < n := by
    have := Nat.le_ceil (C / (-minkQ (trOf g)))
    simp only [n]; push_cast; linarith
  have hpos : 0 < -minkQ (trOf g) := by linarith
  have h2 : C < (n : ℝ) * (-minkQ (trOf g)) := by rwa [div_lt_iff₀ hpos] at hnr
  have h3 : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  nlinarith

/-- **[7.E], `τ` spacelike: `Ω_g = 𝐌ⁿ`** (l.2045). -/
theorem achronalDomain_elliptic_spacelike (h : 0 < minkQ (trOf g)) :
    achronalDomain g = Set.univ := by
  obtain ⟨u, hu, hAu⟩ := hE.exists_fixed_timelike (linOf_mem g)
  refine Set.eq_univ_iff_forall.2 fun x => mem_achronalDomain_iff.2 fun n hn => ?_
  rw [minkQ_pow_smul_sub_of_fixed hτ]
  have := minkQ_pow_sub_nonneg (linOf_mem g).1 hu.2 hAu n x
  have hn' : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
  nlinarith

/-- **[7.E], `τ` lightlike (`τ = 0` allowed, l.2050–2051): the complement of `Ω_g` is the set
of `L(g)`-periodic points** (l.2047–2049). -/
theorem achronalDomain_elliptic_lightlike (h : minkQ (trOf g) = 0) :
    achronalDomain g = {x | ∀ n : ℕ, 0 < n → (linOf g ^ n) x ≠ x} := by
  obtain ⟨u, hu, hAu⟩ := hE.exists_fixed_timelike (linOf_mem g)
  ext x
  rw [mem_achronalDomain_iff, Set.mem_setOf_eq]
  refine forall₂_congr fun n _ => ?_
  rw [minkQ_pow_smul_sub_of_fixed hτ, h, mul_zero, add_zero]
  refine ⟨fun h1 h2 => by rw [h2, sub_self, minkQ_zero] at h1; exact lt_irrefl _ h1,
    fun h1 => ?_⟩
  rcases (minkQ_pow_sub_nonneg (linOf_mem g).1 hu.2 hAu n x).lt_or_eq with h2 | h2
  · exact h2
  · exact absurd (pow_apply_eq_of_minkQ_eq_zero (linOf_mem g).1 hu.2 hAu h2.symm) h1

/-- … and that set is the subspace `ker (L(g)^N − id)` for one `N > 0` (l.2048: "the subspace
formed by `R`-periodic points, i.e. the `Rⁿ`-fixed points"). -/
theorem achronalDomain_elliptic_lightlike_eq_compl_ker (h : minkQ (trOf g) = 0) :
    ∃ N : ℕ, 0 < N ∧
      achronalDomain g = ((LinearMap.ker (pOf (linOf g ^ N)) : Submodule ℝ (Minkowski d)) :
        Set (Minkowski d))ᶜ := by
  obtain ⟨N, hN, hper⟩ := exists_periodic_iff (linOf g)
  refine ⟨N, hN, ?_⟩
  rw [achronalDomain_elliptic_lightlike hE hτ h]
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_compl_iff, SetLike.mem_coe, LinearMap.mem_ker,
    pOf_apply, sub_eq_zero, ← hper x]
  push Not
  exact Iff.rfl

/-- **The survey's caveat, which is the lightlike case of [7.E]**: if moreover `L(g)` has finite
order, every point is periodic and `Ω_g = ∅`, `τ ≠ 0` included (a null translation is the
simplest instance). -/
theorem achronalDomain_elliptic_lightlike_of_pow_eq_one (h : minkQ (trOf g) = 0) {N : ℕ}
    (hN : 0 < N) (h1 : linOf g ^ N = 1) : achronalDomain g = ∅ := by
  rw [achronalDomain_elliptic_lightlike hE hτ h]
  refine Set.eq_empty_iff_forall_notMem.2 fun x hx => hx N hN ?_
  rw [h1]; rfl

omit hτ in
/-- **`Ω_g` is open for every elliptic `g`** (l.2026's "open set", confirmed in the elliptic
class): conjugate `τ` into `Fix L(g)` (`IsElliptic.exists_transConj_fixed`), then `Ω_g` is
`∅`, `𝐌ⁿ` or the complement of a subspace. -/
theorem isOpen_achronalDomain_elliptic : IsOpen (achronalDomain g) := by
  obtain ⟨v, hv⟩ := IsElliptic.exists_transConj_fixed g.2 hE
  set g' := isomConj v g
  have hE' : IsElliptic (linOf g') := by rw [linOf_isomConj]; exact hE
  have hτ' : linOf g' (trOf g') = trOf g' := by
    show (transConj v (g : Minkowski d ≃ᵃ[ℝ] Minkowski d)).linear _ = _
    rw [linear_transConj]; exact hv
  refine isOpen_achronalDomain_of_isomConj (v := v) ?_
  rcases lt_trichotomy (minkQ (trOf g')) 0 with h | h | h
  · rw [achronalDomain_elliptic_timelike hE' hτ' h]; exact isOpen_empty
  · obtain ⟨N, -, hN⟩ := achronalDomain_elliptic_lightlike_eq_compl_ker hE' hτ' h
    rw [hN]
    exact (Submodule.closed_of_finiteDimensional _).isOpen_compl
  · rw [achronalDomain_elliptic_spacelike hE' hτ' h]; exact isOpen_univ

end elliptic

/-- **Non-vacuity of the three elliptic cases** (`L(g) = id`): a translation by a timelike vector
has `Ω = ∅`, by a spacelike one `Ω = 𝐌ⁿ`, by a nonzero null one `Ω = ∅` (finite order). -/
theorem achronalDomain_isomTrans_timeUnit : achronalDomain (isomTrans (timeUnit d)) = ∅ := by
  have htr : trOf (isomTrans (timeUnit d)) = timeUnit d := by
    show timeUnit d +ᵥ (0 : Minkowski d) = timeUnit d; rw [vadd_eq_add, add_zero]
  refine achronalDomain_elliptic_timelike isElliptic_one (by rw [htr]; rfl) ?_
  rw [htr, minkQ_timeUnit]; norm_num

theorem achronalDomain_isomTrans_spaceUnit (i : Fin d) :
    achronalDomain (isomTrans (spaceUnit i)) = Set.univ := by
  have htr : trOf (isomTrans (spaceUnit i)) = spaceUnit i := by
    show spaceUnit i +ᵥ (0 : Minkowski d) = spaceUnit i; rw [vadd_eq_add, add_zero]
  refine achronalDomain_elliptic_spacelike isElliptic_one (by rw [htr]; rfl) ?_
  rw [htr, minkQ_spaceUnit]; norm_num

theorem achronalDomain_isomTrans_null (i : Fin d) :
    achronalDomain (isomTrans (timeUnit d + spaceUnit i)) = ∅ := by
  have htr : trOf (isomTrans (timeUnit d + spaceUnit i)) = timeUnit d + spaceUnit i := by
    show (timeUnit d + spaceUnit i) +ᵥ (0 : Minkowski d) = _; rw [vadd_eq_add, add_zero]
  refine achronalDomain_elliptic_lightlike_of_pow_eq_one isElliptic_one (by rw [htr]; rfl) ?_
    one_pos (by rw [pow_one]; rfl)
  rw [htr, minkQ_add, minkQ_timeUnit, minkQ_spaceUnit, minkB_timeUnit_spaceUnit]; ring

/-! ### [7.L] The loxodromic case (l.2055–2082) -/

/-- **Barbot's `xy`** (l.2059–2063, `Q = xy + ‖v‖²`) in the null frame `(u, u')`:
`z = a u + b u' + v` with `v ⊥ u, u'` gives `minkQ z = 2ab ⟨u|u'⟩ + minkQ v`, and
`nullXY u u' z = 2ab ⟨u|u'⟩` (`minkQ_eq_nullXY_add`). -/
noncomputable def nullXY (u u' z : Minkowski d) : ℝ := 2 * minkB z u * minkB z u' / minkB u u'

/-- **Barbot's `v`** (l.2059): the component of `z` orthogonal to the null frame `(u, u')`. -/
noncomputable def nullV (u u' z : Minkowski d) : Minkowski d :=
  z - (minkB z u' / minkB u u') • u - (minkB z u / minkB u u') • u'

section nullFrame

variable {u u' : Minkowski d} (hu : minkQ u = 0) (hu' : minkQ u' = 0) (hB : minkB u u' ≠ 0)
include hu hu' hB

omit hu' in
theorem minkB_nullV_left (z : Minkowski d) : minkB (nullV u u' z) u = 0 := by
  have hu0 : minkB u u = 0 := by rw [← minkQ_eq_minkB, hu]
  rw [nullV, minkB_sub_left, minkB_sub_left, minkB_smul_left, minkB_smul_left, hu0,
    minkB_comm u' u, div_mul_cancel₀ _ hB]; ring

omit hu in
theorem minkB_nullV_right (z : Minkowski d) : minkB (nullV u u' z) u' = 0 := by
  have hu0 : minkB u' u' = 0 := by rw [← minkQ_eq_minkB, hu']
  rw [nullV, minkB_sub_left, minkB_sub_left, minkB_smul_left, minkB_smul_left, hu0,
    div_mul_cancel₀ _ hB]; ring

omit hu hu' hB in
theorem eq_nullV_add (z : Minkowski d) :
    z = (minkB z u' / minkB u u') • u + (minkB z u / minkB u u') • u' + nullV u u' z := by
  rw [nullV]; abel

/-- **`Q = xy + ‖v‖²`** (l.2062). -/
theorem minkQ_eq_nullXY_add (z : Minkowski d) :
    minkQ z = nullXY u u' z + minkQ (nullV u u' z) := by
  conv_lhs => rw [eq_nullV_add (u := u) (u' := u') z]
  rw [show ∀ a b : ℝ, ∀ w : Minkowski d, a • u + b • u' + w = a • u + b • u' + (1 : ℝ) • w from
    fun a b w => by rw [one_smul], minkQ_smul_add3, hu, hu', minkB_comm u (nullV u u' z),
    minkB_comm u' (nullV u u' z), minkB_nullV_left hu hB, minkB_nullV_right hu' hB, nullXY]
  field_simp; ring

/-- The orthogonal of a null frame is spacelike: `t₀ = u − ⟨u|u'⟩ u'` is timelike. -/
theorem minkQ_nonneg_of_orth_frame {y : Minkowski d} (h1 : minkB y u = 0) (h2 : minkB y u' = 0) :
    0 ≤ minkQ y ∧ (minkQ y = 0 → y = 0) := by
  set t₀ := u - minkB u u' • u'
  have ht : minkQ t₀ < 0 := by
    have : minkQ t₀ = -(2 * minkB u u' ^ 2) := by
      rw [show t₀ = (1 : ℝ) • u + (-minkB u u') • u' + (0 : ℝ) • (0 : Minkowski d) by
        simp [t₀, sub_eq_add_neg, neg_smul], minkQ_smul_add3, hu, hu']; simp; ring
    rw [this]; have := pow_pos (abs_pos.2 hB) 2; rw [sq_abs] at this; linarith
  have hty : minkB t₀ y = 0 := by
    rw [minkB_sub_left, minkB_smul_left, minkB_comm u y, minkB_comm u' y, h1, h2]; ring
  refine ⟨minkQ_nonneg_of_orth_timelike ht hty, fun h0 => ?_⟩
  by_contra hy
  have := minkQ_pos_of_orth_timelike ht hty hy
  linarith

end nullFrame

theorem continuous_nullXY (u u' : Minkowski d) : Continuous (nullXY u u') := by
  unfold nullXY minkB; fun_prop

/-- **The leading factor** `(λⁿ − 1)(λ⁻ⁿ − 1) = −(λⁿ − 1)²/λⁿ < 0` (l.2073–2075, where Barbot's
`λ = e^{ζ/2}` and `−4 sh²(qζ)` are normalised inconsistently; only the sign is used). -/
theorem lox_factor_neg {l : ℝ} (hl : 0 < l) (hl1 : l ≠ 1) {n : ℕ} (hn : 0 < n) :
    (l ^ n - 1) * ((l ^ n)⁻¹ - 1) < 0 := by
  have hx : 0 < l ^ n := pow_pos hl n
  have hx1 : l ^ n ≠ 1 := fun h => hl1 ((pow_eq_one_iff_of_nonneg hl.le hn.ne').1 h)
  have e : (l ^ n - 1) * ((l ^ n)⁻¹ - 1) = -((l ^ n - 1) ^ 2 / l ^ n) := by
    field_simp; ring
  rw [e, neg_lt_zero]
  exact div_pos (pow_pos (abs_pos.2 (sub_ne_zero.2 hx1)) 2 |>.trans_eq (sq_abs _)) hx

/-- Exponential growth beats any quadratic: the loxodromic leading term wins. -/
theorem exists_lox_dominates {l X C D : ℝ} (hl : 0 < l) (hl1 : l ≠ 1) (hX : 0 < X) :
    ∃ n : ℕ, 0 < n ∧ (l ^ n - 1) * ((l ^ n)⁻¹ - 1) * X + C + (n : ℝ) ^ 2 * D < 0 := by
  -- `r = max (l, l⁻¹) > 1` and the factor is `≤ 2 − rⁿ`
  obtain ⟨r, hr, hfac⟩ : ∃ r : ℝ, 1 < r ∧ ∀ n : ℕ,
      (l ^ n - 1) * ((l ^ n)⁻¹ - 1) ≤ 2 - r ^ n := by
    rcases lt_or_gt_of_ne hl1 with h | h
    · refine ⟨l⁻¹, one_lt_inv₀ hl |>.2 h, fun n => ?_⟩
      have hx : 0 < l ^ n := pow_pos hl n
      have e : (l ^ n - 1) * ((l ^ n)⁻¹ - 1) = 2 - l ^ n - (l ^ n)⁻¹ := by field_simp; ring
      rw [e, inv_pow]; linarith
    · refine ⟨l, h, fun n => ?_⟩
      have hx : 0 < l ^ n := pow_pos hl n
      have e : (l ^ n - 1) * ((l ^ n)⁻¹ - 1) = 2 - l ^ n - (l ^ n)⁻¹ := by field_simp; ring
      rw [e]; have := inv_pos.2 hx; linarith
  have hD1 : 0 < |D| + 1 := by positivity
  have h1 : ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ 2 / r ^ n < X / (2 * (|D| + 1)) :=
    (tendsto_order.1 (tendsto_pow_const_div_const_pow_of_one_lt 2 hr)).2 _ (by positivity)
  have h2 : ∀ᶠ n : ℕ in atTop, 2 * (2 * X + |C| + 1) / X ≤ r ^ n :=
    (tendsto_pow_atTop_atTop_of_one_lt hr).eventually_ge_atTop _
  obtain ⟨n, hn1, hn2, hn3⟩ := (h1.and (h2.and (eventually_ge_atTop 1))).exists
  refine ⟨n, hn3, ?_⟩
  have hrn : 0 < r ^ n := pow_pos (by linarith) n
  have e1 : (n : ℝ) ^ 2 * (2 * (|D| + 1)) < X * r ^ n := by
    rw [div_lt_div_iff₀ hrn (by positivity)] at hn1; linarith
  have e2 : 2 * (2 * X + |C| + 1) ≤ X * r ^ n := by
    rw [div_le_iff₀ hX] at hn2; linarith
  have e3 : (l ^ n - 1) * ((l ^ n)⁻¹ - 1) * X ≤ (2 - r ^ n) * X :=
    mul_le_mul_of_nonneg_right (hfac n) hX.le
  have e4 : (n : ℝ) ^ 2 * D ≤ (n : ℝ) ^ 2 * (|D| + 1) :=
    mul_le_mul_of_nonneg_left (by linarith [le_abs_self D]) (by positivity)
  have e5 : C ≤ |C| := le_abs_self C
  nlinarith

/-- A vector fixed by a `minkQ`-preserving map is orthogonal to its eigenvectors of eigenvalue
`c ≠ 1`. -/
theorem minkB_fixed_eigen {A : Minkowski d ≃ₗ[ℝ] Minkowski d} (hA : ∀ v, minkQ (A v) = minkQ v)
    {c : ℝ} (hc : c ≠ 1) {τ w : Minkowski d} (hτ : A τ = τ) (hw : A w = c • w) :
    minkB τ w = 0 := by
  have h := minkB_map hA τ w
  rw [hτ, hw, minkB_smul_right] at h
  have : (c - 1) * minkB τ w = 0 := by linarith
  exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hc)

section loxodromic

variable {g : isom d} {u u' : Minkowski d} {l : ℝ}
  (hu : minkQ u = 0) (hu' : minkQ u' = 0) (hB : minkB u u' ≠ 0) (hl : 0 < l) (hl1 : l ≠ 1)
  (hAu : linOf g u = l • u) (hAu' : linOf g u' = l⁻¹ • u') (hτ : linOf g (trOf g) = trOf g)

omit hu hu' hB hl1 hAu' hτ in
theorem pow_eigen {c : ℝ} {w : Minkowski d} (h : linOf g w = c • w) (n : ℕ) :
    (linOf g ^ n) w = c ^ n • w := by
  induction n with
  | zero => simp
  | succ n ih => rw [linEquiv_pow_succ_apply, ih, map_smul, h, smul_smul, pow_succ]

omit hu hu' hB hl hl1 hAu hAu' hτ in
theorem minkB_pow_eigen_orth {c : ℝ} (hc : c ≠ 0) {w y : Minkowski d} (h : linOf g w = c • w)
    (hy : minkB y w = 0) (n : ℕ) : minkB ((linOf g ^ n) y) w = 0 := by
  have h1 := minkB_pow_apply (linOf_mem g).1 n y w
  rw [pow_eigen h, minkB_smul_right, hy] at h1
  exact (mul_eq_zero.1 h1).resolve_left (pow_ne_zero n hc)

include hu hu' hB hl hl1 hAu hAu' hτ

omit hl1 in
/-- **The loxodromic formula** (l.2071–2075): with `xy = nullXY u u' z` and `v = nullV u u' z`,
`|gⁿz − z|² = (λⁿ − 1)(λ⁻ⁿ − 1) xy + |(L(g)ⁿ − id) v|² + n² |τ|²`. -/
theorem minkQ_pow_smul_sub_lox (n : ℕ) (z : Minkowski d) :
    minkQ ((g ^ n) • z - z) = (l ^ n - 1) * ((l ^ n)⁻¹ - 1) * nullXY u u' z +
      minkQ ((linOf g ^ n) (nullV u u' z) - nullV u u' z) + (n : ℝ) ^ 2 * minkQ (trOf g) := by
  rw [minkQ_pow_smul_sub_of_fixed hτ]
  congr 1
  set v := nullV u u' z
  set a := minkB z u' / minkB u u'
  set b := minkB z u / minkB u u'
  have hz := eq_nullV_add (u := u) (u' := u') z
  have hlinv : l⁻¹ ≠ 0 := inv_ne_zero hl.ne'
  have hv1 := minkB_nullV_left hu hB z
  have hv2 := minkB_nullV_right hu' hB z
  have e : (linOf g ^ n) z - z = (a * (l ^ n - 1)) • u + (b * ((l ^ n)⁻¹ - 1)) • u' +
      (1 : ℝ) • ((linOf g ^ n) v - v) := by
    conv_lhs => rw [hz]
    rw [map_add, map_add, map_smul, map_smul, pow_eigen hAu, pow_eigen hAu', inv_pow]
    module
  have t1 : minkB u ((linOf g ^ n) v - v) = 0 := by
    rw [minkB_comm, minkB_sub_left, minkB_pow_eigen_orth hl.ne' hAu hv1, hv1, sub_self]
  have t2 : minkB u' ((linOf g ^ n) v - v) = 0 := by
    rw [minkB_comm, minkB_sub_left, minkB_pow_eigen_orth hlinv hAu' hv2, hv2, sub_self]
  rw [e, minkQ_smul_add3, hu, hu', t1, t2, nullXY]
  simp only [a, b]
  field_simp; ring

omit hl in
theorem minkQ_tr_lox : 0 ≤ minkQ (trOf g) ∧ (minkQ (trOf g) = 0 → trOf g = 0) := by
  have hl1' : l⁻¹ ≠ 1 := fun h => hl1 (by rw [← inv_inv l, h, inv_one])
  exact minkQ_nonneg_of_orth_frame hu hu' hB
    (minkB_fixed_eigen (linOf_mem g).1 hl1 hτ hAu) (minkB_fixed_eigen (linOf_mem g).1 hl1' hτ hAu')

omit hl1 hτ in
theorem minkQ_pow_nullV_lox (n : ℕ) (z : Minkowski d) :
    0 ≤ minkQ ((linOf g ^ n) (nullV u u' z) - nullV u u' z) ∧
      (minkQ ((linOf g ^ n) (nullV u u' z) - nullV u u' z) = 0 →
        (linOf g ^ n) (nullV u u' z) = nullV u u' z) ∧
      minkQ ((linOf g ^ n) (nullV u u' z) - nullV u u' z) ≤ 4 * minkQ (nullV u u' z) := by
  set v := nullV u u' z
  have hlinv : l⁻¹ ≠ 0 := inv_ne_zero hl.ne'
  have hv1 := minkB_nullV_left hu hB z
  have hv2 := minkB_nullV_right hu' hB z
  have a1 := minkB_pow_eigen_orth hl.ne' hAu hv1 n
  have a2 := minkB_pow_eigen_orth hlinv hAu' hv2 n
  have d := minkQ_nonneg_of_orth_frame hu hu' hB (y := (linOf g ^ n) v - v)
    (by rw [minkB_sub_left, a1, hv1, sub_self]) (by rw [minkB_sub_left, a2, hv2, sub_self])
  have s := (minkQ_nonneg_of_orth_frame hu hu' hB (y := (linOf g ^ n) v + v)
    (by rw [minkB_add_left, a1, hv1, add_zero]) (by rw [minkB_add_left, a2, hv2, add_zero])).1
  have hpar := minkQ_parallelogram ((linOf g ^ n) v) v
  rw [minkQ_pow_apply (linOf_mem g).1] at hpar
  exact ⟨d.1, fun h0 => sub_eq_zero.1 (d.2 h0), by linarith⟩

/-- **[7.L], corrected (DEC-27)**: the exact achronal domain of a loxodromic `g` in normal form.
`z ∈ Ω_g` iff `xy < 0`, or `xy = 0` and either `τ ≠ 0` or `v` is not `L(g)`-periodic.
Barbot's `Ω_g = {xy < 0}` (l.2081) omits the second alternative. -/
theorem mem_achronalDomain_lox_iff (z : Minkowski d) :
    z ∈ achronalDomain g ↔ nullXY u u' z < 0 ∨ (nullXY u u' z = 0 ∧
      (trOf g ≠ 0 ∨ ∀ n : ℕ, 0 < n → (linOf g ^ n) (nullV u u' z) ≠ nullV u u' z)) := by
  have hτQ := minkQ_tr_lox hu hu' hB hl1 hAu hAu' hτ
  rw [mem_achronalDomain_iff]
  simp only [minkQ_pow_smul_sub_lox hu hu' hB hl hAu hAu' hτ]
  constructor
  · intro h
    rcases lt_trichotomy (nullXY u u' z) 0 with h0 | h0 | h0
    · exact Or.inl h0
    · refine Or.inr ⟨h0, ?_⟩
      by_contra hc
      push Not at hc
      obtain ⟨hτ0, ⟨n, hn, hper⟩⟩ := hc
      have := h n hn
      simp [h0, hτ0, hper] at this
    · exfalso
      obtain ⟨n, hn, hneg⟩ := exists_lox_dominates (C := 4 * minkQ (nullV u u' z))
        (D := minkQ (trOf g)) hl hl1 h0
      have h1 := h n hn
      have h2 := (minkQ_pow_nullV_lox hu hu' hB hl hAu hAu' n z).2.2
      linarith
  · intro h n hn
    have hf := lox_factor_neg hl hl1 hn
    obtain ⟨hv0, hv1, -⟩ := minkQ_pow_nullV_lox hu hu' hB hl hAu hAu' n z
    have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
    rcases h with h | ⟨h0, h | h⟩
    · have := mul_pos_of_neg_of_neg hf h
      nlinarith [hτQ.1]
    · have : 0 < minkQ (trOf g) := lt_of_le_of_ne hτQ.1 fun e => h (hτQ.2 e.symm)
      rw [h0, mul_zero, zero_add]; nlinarith
    · have : 0 < minkQ ((linOf g ^ n) (nullV u u' z) - nullV u u' z) :=
        lt_of_le_of_ne hv0 fun e => h n hn (hv1 e.symm)
      rw [h0, mul_zero, zero_add]; nlinarith [hτQ.1]

/-- **[7.L], `τ ≠ 0`: `Ω_g = {xy ≤ 0}`** — the inaccuracy the survey reported, confirmed. -/
theorem achronalDomain_lox_of_ne_zero (h : trOf g ≠ 0) :
    achronalDomain g = {z | nullXY u u' z ≤ 0} := by
  ext z
  rw [mem_achronalDomain_lox_iff hu hu' hB hl hl1 hAu hAu' hτ, Set.mem_setOf_eq]
  constructor
  · rintro (h0 | ⟨h0, -⟩)
    · exact h0.le
    · exact h0.le
  · intro h0
    rcases h0.lt_or_eq with h0 | h0
    · exact Or.inl h0
    · exact Or.inr ⟨h0, Or.inl h⟩

/-- **[7.L], `τ = 0`**: `Ω_g = {xy < 0} ∪ {xy = 0, v not L(g)-periodic}`. It is `{xy < 0}`
exactly when no such `v` exists, e.g. when `L(g)` has finite order on the orthogonal of the
frame; an irrational rotation gives `xy = 0` points in `Ω_g`. -/
theorem achronalDomain_lox_of_eq_zero (h : trOf g = 0) :
    achronalDomain g = {z | nullXY u u' z < 0} ∪
      {z | nullXY u u' z = 0 ∧ ∀ n : ℕ, 0 < n → (linOf g ^ n) (nullV u u' z) ≠ nullV u u' z} := by
  ext z
  rw [mem_achronalDomain_lox_iff hu hu' hB hl hl1 hAu hAu' hτ, h]
  simp

/-- **[7.L]: the interior of `Ω_g` is `{xy < 0}`**, in every case — the set the later use of
[7.L] (§8–§10) actually needs. -/
theorem interior_achronalDomain_lox : interior (achronalDomain g) = {z | nullXY u u' z < 0} := by
  have hsub : {z | nullXY u u' z < 0} ⊆ achronalDomain g := fun z hz =>
    (mem_achronalDomain_lox_iff hu hu' hB hl hl1 hAu hAu' hτ z).2 (Or.inl hz)
  have hopen : IsOpen {z | nullXY u u' z < 0} :=
    isOpen_lt (continuous_nullXY u u') continuous_const
  refine Set.Subset.antisymm (fun z hz => ?_) (interior_maximal hsub hopen)
  have hzΩ := interior_subset hz
  have hle : nullXY u u' z ≤ 0 := by
    rcases (mem_achronalDomain_lox_iff hu hu' hB hl hl1 hAu hAu' hτ z).1 hzΩ with h | ⟨h, -⟩
    · exact h.le
    · exact h.le
  rcases hle.lt_or_eq with h | h0
  · exact h
  exfalso
  -- a direction `δ` along which `xy` becomes positive
  set α := minkB z u'
  set β := minkB z u
  have hαβ : β * α = 0 := by
    have : 2 * β * α / minkB u u' = 0 := h0
    rw [mul_assoc, mul_div_assoc] at this
    have := (mul_eq_zero.1 this).resolve_left two_ne_zero
    exact (div_eq_zero_iff.1 this).resolve_right hB
  have huu : minkB u u = 0 := by rw [← minkQ_eq_minkB, hu]
  have hu'u' : minkB u' u' = 0 := by rw [← minkQ_eq_minkB, hu']
  obtain ⟨δ, hδ⟩ : ∃ δ : Minkowski d, ∀ ε : ℝ, 0 < ε → 0 < nullXY u u' (z + ε • δ) := by
    by_cases hz0 : α = 0 ∧ β = 0
    · refine ⟨minkB u u' • u + u', fun ε hε => ?_⟩
      have e : nullXY u u' (z + ε • (minkB u u' • u + u')) = 2 * ε ^ 2 * minkB u u' ^ 2 := by
        simp only [nullXY, minkB_add_left, minkB_smul_left, huu, hu'u', minkB_comm u' u]
        rw [show minkB z u = β from rfl, show minkB z u' = α from rfl, hz0.1, hz0.2]
        field_simp; ring
      rw [e]; have : 0 < minkB u u' ^ 2 := by positivity
      positivity
    · refine ⟨β • u + α • u', fun ε hε => ?_⟩
      have hpos : 0 < α ^ 2 + β ^ 2 := by
        by_contra hn
        push Not at hn
        apply hz0
        constructor <;> nlinarith [sq_nonneg α, sq_nonneg β]
      have e : nullXY u u' (z + ε • (β • u + α • u')) =
          2 * ε * (α ^ 2 + β ^ 2) + 2 * (β * α) * (1 + ε ^ 2 * minkB u u' ^ 2) / minkB u u' := by
        simp only [nullXY, minkB_add_left, minkB_smul_left, huu, hu'u', minkB_comm u' u]
        rw [show minkB z u = β from rfl, show minkB z u' = α from rfl]
        field_simp; ring
      rw [e, hαβ]; simp only [mul_zero, zero_mul, zero_div, add_zero]; positivity
  have ht : Tendsto (fun ε : ℝ => z + ε • δ) (𝓝[>] 0) (𝓝 z) := by
    have : Tendsto (fun ε : ℝ => z + ε • δ) (𝓝 0) (𝓝 (z + (0 : ℝ) • δ)) :=
      (continuous_const.add (continuous_id.smul continuous_const)).tendsto 0
    rw [zero_smul, add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  obtain ⟨ε, hmem, hε⟩ :=
    ((ht.eventually (mem_interior_iff_mem_nhds.1 hz)).and self_mem_nhdsWithin).exists
  have h1 := (mem_achronalDomain_lox_iff hu hu' hB hl hl1 hAu hAu' hτ _).1 hmem
  have h2 := hδ ε hε
  rcases h1 with h1 | ⟨h1, -⟩ <;> linarith

/-- **[7.L]: for `τ ≠ 0`, `Ω_g` is not open** (l.2026's "open set" fails): the null vector `u`
has `xy = 0`, so it lies in `Ω_g`, not in its interior. -/
theorem not_isOpen_achronalDomain_lox (h : trOf g ≠ 0) : ¬IsOpen (achronalDomain g) := by
  intro ho
  have hxy : nullXY u u' u = 0 := by
    simp only [nullXY, ← minkQ_eq_minkB, hu, mul_zero, zero_mul, zero_div]
  have hmem : u ∈ achronalDomain g :=
    (mem_achronalDomain_lox_iff hu hu' hB hl hl1 hAu hAu' hτ u).2 (Or.inr ⟨hxy, Or.inl h⟩)
  have := interior_achronalDomain_lox hu hu' hB hl hl1 hAu hAu' hτ
  rw [ho.interior_eq] at this
  rw [this] at hmem
  have h2 : nullXY u u' u < 0 := hmem
  rw [hxy] at h2
  exact lt_irrefl _ h2

/-- **[7.L]: `Ω_g` is open exactly when `τ = 0` and `L(g)` has finite order on the orthogonal of
the frame** — l.2026's "open set", decided in the loxodromic class. For `τ ≠ 0` the null vector
`u` lies in `Ω_g` but not in its interior; for `τ = 0` so does every `w ⊥ u, u'` that is not
`L(g)`-periodic (an irrational rotation part, `d ≥ 3`). -/
theorem isOpen_achronalDomain_lox_iff : IsOpen (achronalDomain g) ↔ trOf g = 0 ∧
    ∃ N : ℕ, 0 < N ∧ ∀ w, minkB w u = 0 → minkB w u' = 0 → (linOf g ^ N) w = w := by
  have hint := interior_achronalDomain_lox hu hu' hB hl hl1 hAu hAu' hτ
  have hV : ∀ w, minkB w u = 0 → minkB w u' = 0 → nullXY u u' w = 0 ∧ nullV u u' w = w :=
    fun w h1 h2 => ⟨by simp [nullXY, h1], by simp [nullV, h1, h2]⟩
  constructor
  · intro ho
    have h0 : trOf g = 0 := by
      by_contra h
      exact not_isOpen_achronalDomain_lox hu hu' hB hl hl1 hAu hAu' hτ h ho
    obtain ⟨N, hN, hper⟩ := exists_periodic_iff (linOf g)
    refine ⟨h0, N, hN, fun w h1 h2 => (hper w).1 ?_⟩
    by_contra hc
    push Not at hc
    obtain ⟨hxy, hv⟩ := hV w h1 h2
    have hmem : w ∈ achronalDomain g :=
      (mem_achronalDomain_lox_iff hu hu' hB hl hl1 hAu hAu' hτ w).2
        (Or.inr ⟨hxy, Or.inr (by rw [hv]; exact hc)⟩)
    rw [← ho.interior_eq, hint] at hmem
    have h3 : nullXY u u' w < 0 := hmem
    rw [hxy] at h3
    exact lt_irrefl _ h3
  · rintro ⟨h0, N, hN, hfin⟩
    have e : achronalDomain g = {z | nullXY u u' z < 0} := by
      rw [achronalDomain_lox_of_eq_zero hu hu' hB hl hl1 hAu hAu' hτ h0]
      exact Set.union_eq_left.2 fun z hz =>
        absurd (hfin _ (minkB_nullV_left hu hB z) (minkB_nullV_right hu' hB z)) (hz.2 N hN)
    rw [e]
    exact isOpen_lt (continuous_nullXY u u') continuous_const

end loxodromic

/-- **"`τ ≠ 0`" in [7.L] means "`g` has no fixed point"**: for a loxodromic `g` in normal form
(`L(g) τ = τ`) the normal-form `τ` vanishes iff `g` fixes a point, since `Im p ∩ ker p = 0`. -/
theorem lox_exists_fixed_iff {g : isom d} (h : IsLoxodromic (linOf g))
    (hτ : linOf g (trOf g) = trOf g) : (∃ x : Minkowski d, g • x = x) ↔ trOf g = 0 := by
  have e : (∃ x : Minkowski d, g • x = x) ↔ ∃ x, (g : Minkowski d ≃ᵃ[ℝ] Minkowski d) x = x := by
    simp only [isom_smul_def]
  rw [e, exists_fixed_iff]
  constructor
  · intro hr
    have hk : trOf g ∈ LinearMap.ker (pOf (linOf g)) := by
      rw [LinearMap.mem_ker, pOf_apply, hτ, sub_self]
    have hbot := h.range_inf_ker
    rw [eq_bot_iff] at hbot
    exact (mem_bot ℝ).1 (hbot ⟨hr, hk⟩)
  · intro h0
    show trOf g ∈ _
    rw [h0]; exact zero_mem _

/-- **[7.L] for every loxodromic `g` in normal form** (`L(g) τ = τ`, reachable by
`IsLoxodromic.exists_transConj_fixed`): in the null frame of `IsLoxodromic.frame`, the interior
of `Ω_g` is `{xy < 0}`; if `τ ≠ 0`, `Ω_g = {xy ≤ 0}` and is not open. -/
theorem achronalDomain_isLoxodromic {g : isom d} (h : IsLoxodromic (linOf g))
    (hτ : linOf g (trOf g) = trOf g) :
    ∃ u u' : Minkowski d, minkQ u = 0 ∧ minkQ u' = 0 ∧ minkB u u' ≠ 0 ∧
      interior (achronalDomain g) = {z | nullXY u u' z < 0} ∧
      (trOf g ≠ 0 → achronalDomain g = {z | nullXY u u' z ≤ 0} ∧
        ¬IsOpen (achronalDomain g)) := by
  obtain ⟨-, u, u', l, -, -, -, -, -, hu, hu', hB, hl, hl1, hAu, hAu', -⟩ := h.frame
  exact ⟨u, u', hu, hu', hB, interior_achronalDomain_lox hu hu' hB hl hl1 hAu hAu' hτ,
    fun h0 => ⟨achronalDomain_lox_of_ne_zero hu hu' hB hl hl1 hAu hAu' hτ h0,
      not_isOpen_achronalDomain_lox hu hu' hB hl hl1 hAu hAu' hτ h0⟩⟩

/-- The boost `stdBoost i ζ` itself, as an isometry (`τ = 0`). -/
noncomputable def boostIsom (i : Fin d) (ζ : ℝ) : isom d :=
  ⟨(stdBoost i ζ).toAffineEquiv, mem_isom_iff.2 (stdBoost_mem_lorentz i ζ)⟩

/-- **Non-vacuity of the open loxodromic case** (`d ≥ 1`): for a pure boost, `τ = 0` and `L(g)`
is the identity on the orthogonal of its null frame `(t + eᵢ, t − eᵢ)`, so `Ω_g = {xy < 0}` is
open (`isOpen_achronalDomain_lox_iff`). -/
theorem boostIsom_isOpen (i : Fin d) {ζ : ℝ} (hζ : ζ ≠ 0) :
    IsLoxodromic (linOf (boostIsom i ζ)) ∧ IsOpen (achronalDomain (boostIsom i ζ)) ∧
      achronalDomain (boostIsom i ζ) =
        {z | nullXY (timeUnit d + spaceUnit i) (timeUnit d - spaceUnit i) z < 0} := by
  have htt : minkB (timeUnit d) (timeUnit d) = -1 := by rw [← minkQ_eq_minkB, minkQ_timeUnit]
  have hii : minkB (spaceUnit i) (spaceUnit i) = 1 := by rw [← minkQ_eq_minkB, minkQ_spaceUnit]
  have hti : minkB (timeUnit d) (spaceUnit i) = 0 := minkB_timeUnit_spaceUnit i
  have hit : minkB (spaceUnit i) (timeUnit d) = 0 := by rw [minkB_comm, hti]
  set u := timeUnit d + spaceUnit i with hudef
  set u' := timeUnit d - spaceUnit i with hu'def
  have hlin : linOf (boostIsom i ζ) = stdBoost i ζ := rfl
  have htr : trOf (boostIsom i ζ) = 0 := map_zero (stdBoost i ζ)
  have hap : ∀ x, linOf (boostIsom i ζ) x = boostLin (timeUnit d) (spaceUnit i) ζ x :=
    fun _ => rfl
  have hu : minkQ u = 0 := by
    rw [minkQ_eq_minkB, hudef, minkB_add_left, minkB_add_right, minkB_add_right, htt, hii, hti,
      hit]; ring
  have hu' : minkQ u' = 0 := by
    rw [minkQ_eq_minkB, hu'def, minkB_sub_left, minkB_sub_right, minkB_sub_right, htt, hii, hti,
      hit]; ring
  have hB : minkB u u' ≠ 0 := by
    rw [hudef, hu'def, minkB_add_left, minkB_sub_right, minkB_sub_right, htt, hii, hti, hit]
    norm_num
  have hl : 0 < Real.exp ζ := Real.exp_pos ζ
  have hl1 : Real.exp ζ ≠ 1 := fun h => hζ (Real.exp_eq_one_iff ζ |>.1 h)
  have hAu : linOf (boostIsom i ζ) u = Real.exp ζ • u := by
    rw [hap, boostLin_apply, hudef, minkB_add_left, minkB_add_left, htt, hii, hti, hit,
      ← Real.cosh_add_sinh]
    module
  have hAu' : linOf (boostIsom i ζ) u' = (Real.exp ζ)⁻¹ • u' := by
    rw [hap, boostLin_apply, hu'def, minkB_sub_left, minkB_sub_left, htt, hii, hti, hit,
      ← Real.exp_neg, ← Real.cosh_sub_sinh]
    module
  have hτ : linOf (boostIsom i ζ) (trOf (boostIsom i ζ)) = trOf (boostIsom i ζ) := by
    rw [htr, map_zero]
  have ho : IsOpen (achronalDomain (boostIsom i ζ)) := by
    refine (isOpen_achronalDomain_lox_iff hu hu' hB hl hl1 hAu hAu' hτ).2
      ⟨htr, 1, one_pos, fun w h1 h2 => ?_⟩
    have ht : minkB w (timeUnit d) = 0 := by
      rw [hudef, minkB_add_right] at h1; rw [hu'def, minkB_sub_right] at h2; linarith
    have hi : minkB w (spaceUnit i) = 0 := by
      rw [hudef, minkB_add_right] at h1; rw [hu'def, minkB_sub_right] at h2; linarith
    rw [pow_one, hap, boostLin_apply, ht, hi]
    simp
  refine ⟨by rw [hlin]; exact stdBoost_isLoxodromic i hζ, ho, ?_⟩
  rw [← ho.interior_eq]
  exact interior_achronalDomain_lox hu hu' hB hl hl1 hAu hAu' hτ

/-- **Non-vacuity of the non-open case** (`d ≥ 2`, Barbot's `n ≥ 3`): the boost along `xᵢ`
followed by the unit translation along `xⱼ`, `j ≠ i`. -/
noncomputable def boostShift {i j : Fin d} (ζ : ℝ) (_hij : i ≠ j) : isom d :=
  ⟨AffineEquiv.constVAdd ℝ (Minkowski d) (spaceUnit j) * (stdBoost i ζ).toAffineEquiv,
    (isom d).mul_mem (constVAdd_mem_isom _) (mem_isom_iff.2 (stdBoost_mem_lorentz i ζ))⟩

theorem boostShift_not_isOpen {i j : Fin d} {ζ : ℝ} (hζ : ζ ≠ 0) (hij : i ≠ j) :
    IsLoxodromic (linOf (boostShift ζ hij)) ∧
      linOf (boostShift ζ hij) (trOf (boostShift ζ hij)) = trOf (boostShift ζ hij) ∧
      trOf (boostShift ζ hij) ≠ 0 ∧ ¬IsOpen (achronalDomain (boostShift ζ hij)) := by
  have hlin : linOf (boostShift ζ hij) = stdBoost i ζ := by
    show AffineEquiv.linearHom (AffineEquiv.constVAdd ℝ (Minkowski d) (spaceUnit j) *
      (stdBoost i ζ).toAffineEquiv) = _
    rw [map_mul]; rfl
  have htr : trOf (boostShift ζ hij) = spaceUnit j := by
    show spaceUnit j +ᵥ (stdBoost i ζ) 0 = spaceUnit j
    rw [map_zero, vadd_eq_add, add_zero]
  have hfix : linOf (boostShift ζ hij) (trOf (boostShift ζ hij)) = trOf (boostShift ζ hij) := by
    rw [hlin, htr]
    show boostLin (timeUnit d) (spaceUnit i) ζ (spaceUnit j) = spaceUnit j
    rw [boostLin_apply, minkB_comm, minkB_timeUnit_spaceUnit, minkB_spaceUnit_spaceUnit hij.symm]
    simp
  have hne : trOf (boostShift ζ hij) ≠ 0 := by
    rw [htr]; intro h
    have := congrArg minkQ h
    rw [minkQ_spaceUnit, minkQ_zero] at this
    exact one_ne_zero this
  have hlox : IsLoxodromic (linOf (boostShift ζ hij)) := by
    rw [hlin]; exact stdBoost_isLoxodromic i hζ
  obtain ⟨u, u', -, -, -, -, hno⟩ := achronalDomain_isLoxodromic hlox hfix
  exact ⟨hlox, hfix, hne, (hno hne).2⟩

/-! ### [7.P] The parabolic case (l.2084–2163) -/

/-- `t(t−1)/2`, the coefficient of `p²` in `(id + p)^t` (l.2089). -/
noncomputable def ch2 (t : ℝ) : ℝ := t * (t - 1) / 2

/-- `t(t−1)(t−2)/6` (l.2100). -/
noncomputable def ch3 (t : ℝ) : ℝ := t * (t - 1) * (t - 2) / 6

/-- **A quartic with negative leading coefficient is eventually negative** — the shape of
l.2154–2161: `T(q) ~ (q−1)(5−q)/12 · |p τ|²`. -/
theorem exists_quartic_neg (C K0 K1 : ℝ) {m : ℝ} (hm : 0 < m) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      C + (n : ℝ) ^ 2 * (K0 + (n - 1) * K1 + (n - 1) * (5 - n) * m / 12) < 0 := by
  set M := |C| + |K0| + |K1| + m + 1 with hM
  refine ⟨⌈12 * M / m⌉₊ + 2, fun n hn => ?_⟩
  have hn' : 12 * M / m + 2 ≤ (n : ℝ) := by
    have h1 := Nat.le_ceil (12 * M / m)
    have h2 : ((⌈12 * M / m⌉₊ + 2 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
    push_cast at h2; linarith
  set s := (n : ℝ) - 1 with hs
  have hM0 : 0 ≤ 12 * M / m := by positivity
  have hs1 : 1 ≤ s := by linarith
  have hsM : 12 * M ≤ s * m := by
    have : 12 * M / m ≤ s := by linarith
    rwa [div_le_iff₀ hm] at this
  have a2 : s * K1 ≤ s * |K1| := mul_le_mul_of_nonneg_left (le_abs_self _) (by linarith)
  have a3 : s * M ≤ s * (s * m) / 12 := by nlinarith
  have b1 : |C| ≤ s * |C| := by nlinarith [abs_nonneg C]
  have b2 : |K0| ≤ s * |K0| := by nlinarith [abs_nonneg K0]
  have b3 : s * m / 3 ≤ s * m := by nlinarith
  have a4 : |C| + 1 + |K0| + s * |K1| + s * m / 3 ≤ s * M := by
    rw [hM]; nlinarith
  have hX : K0 + s * K1 + s * (4 - s) * m / 12 ≤ -(|C| + 1) := by
    nlinarith [le_abs_self K0]
  have e2 : (5 - (n : ℝ)) = 4 - s := by rw [hs]; ring
  rw [e2]
  have hn1 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have hXneg : K0 + s * K1 + s * (4 - s) * m / 12 < 0 := by linarith [abs_nonneg C]
  have h3 : (n : ℝ) ^ 2 * (K0 + s * K1 + s * (4 - s) * m / 12) ≤
      K0 + s * K1 + s * (4 - s) * m / 12 := by nlinarith
  linarith [le_abs_self C]

/-- `x` and `y` are causally related, in one direction or the other, by the ETT causality
`minkowski d` of `𝐌ⁿ` (`le_top_iff_minkQ`). -/
def CausallyRelated (x y : Minkowski d) : Prop :=
  (minkowski d).le ⊤ x y ∨ (minkowski d).le ⊤ y x

theorem causallyRelated_of_minkQ_nonpos {x y : Minkowski d} (h : minkQ (y - x) ≤ 0) :
    CausallyRelated x y := le_top_or_of_minkQ_nonpos h

theorem minkQ_nonpos_of_causallyRelated {x y : Minkowski d} (h : CausallyRelated x y) :
    minkQ (y - x) ≤ 0 := by
  rcases h with h | h
  · exact (le_top_iff_minkQ.1 h).2
  · have := (le_top_iff_minkQ.1 h).2
    rwa [show x - y = -(y - x) by abel, minkQ_neg] at this

/-- An isometry preserves causal relatedness. -/
theorem causallyRelated_smul_iff (h : isom d) {x y : Minkowski d} :
    CausallyRelated (h • x) (h • y) ↔ CausallyRelated x y := by
  unfold CausallyRelated; rw [isom_le_top_iff, isom_le_top_iff]

/-- The visibility set of `blem:paranongh` moves under conjugation. -/
theorem causallyRelated_conj_iff (h g : isom d) (x₀ x : Minkowski d) (q : ℤ) :
    CausallyRelated x₀ (((h * g * h⁻¹) ^ q) • x) ↔
      CausallyRelated (h⁻¹ • x₀) ((g ^ q) • (h⁻¹ • x)) := by
  rw [conj_zpow, mul_smul, mul_smul]
  conv_lhs => rw [show x₀ = h • (h⁻¹ • x₀) from (smul_inv_smul h x₀).symm]
  exact causallyRelated_smul_iff h

/-- **`blem:paranongh` as printed** (l.2173–2180), for every dimension `d`: for parabolic `g` and
any `x₀` there is `x` with infinitely many iterates `gᵠ x` causally related to `x₀`. False for
`d ≥ 3` (`not_paranongh`). -/
def Paranongh (d : ℕ) : Prop :=
  ∀ g : isom d, IsParabolic (linOf g) → ∀ x₀ : Minkowski d, ∃ x : Minkowski d,
    Set.Infinite {q : ℤ | CausallyRelated x₀ ((g ^ q) • x)}

/-- An integer quadratic with positive leading coefficient is nonpositive only finitely often. -/
theorem finite_int_quadratic_nonpos {a b c : ℝ} (hc : 0 < c) :
    Set.Finite {q : ℤ | a + 2 * q * b + (q : ℝ) ^ 2 * c ≤ 0} := by
  set K := (|a| + 2 * |b|) / c + 1 with hK
  have hK1 : 1 ≤ K := by have : 0 ≤ (|a| + 2 * |b|) / c := by positivity
                         linarith
  have hKc : K * c = |a| + 2 * |b| + c := by rw [hK]; field_simp
  refine (Set.finite_Icc (-(⌈K⌉₊ : ℤ)) ⌈K⌉₊).subset fun q hq => ?_
  have hq' : a + 2 * q * b + (q : ℝ) ^ 2 * c ≤ 0 := hq
  have hab : |(q : ℝ)| ≤ K := by
    by_contra hlt
    push Not at hlt
    have h1 : -(2 * (q : ℝ) * b) ≤ 2 * |(q : ℝ)| * |b| := by
      have := neg_abs_le (2 * (q : ℝ) * b)
      rw [abs_mul, abs_mul, abs_two] at this; linarith
    have h2 : (q : ℝ) ^ 2 = |(q : ℝ)| * |(q : ℝ)| := by rw [← sq, sq_abs]
    have h3 : |(q : ℝ)| * (K * c) < |(q : ℝ)| * |(q : ℝ)| * c := by
      have hq0 : 0 < |(q : ℝ)| := by linarith
      have := mul_lt_mul_of_pos_right hlt hc
      nlinarith
    rw [hKc] at h3
    have h4 : |(q : ℝ)| * (|a| + 2 * |b| + c) ≥ |a| + 2 * |(q : ℝ)| * |b| := by
      nlinarith [abs_nonneg a, abs_nonneg b, abs_nonneg (q : ℝ), mul_nonneg (abs_nonneg (q:ℝ))
        (abs_nonneg b)]
    nlinarith [neg_abs_le a]
  have hc' := Nat.le_ceil K
  rw [abs_le] at hab
  constructor
  · have : (-(⌈K⌉₊ : ℤ) : ℝ) ≤ q := by push_cast; linarith
    exact_mod_cast this
  · have : (q : ℝ) ≤ ((⌈K⌉₊ : ℤ) : ℝ) := by push_cast; linarith
    exact_mod_cast this

section fixedTauZ

variable {g : isom d} (hτ : linOf g (trOf g) = trOf g)
include hτ

/-- `gᵠ x = L(g)ᵠ x + q τ` for every `q ∈ ℤ`, when `L(g) τ = τ`. -/
theorem zpow_smul_of_fixed (q : ℤ) (x : Minkowski d) :
    (g ^ q) • x = (linOf g ^ q) x + (q : ℝ) • trOf g := by
  rcases Int.eq_nat_or_neg q with ⟨n, rfl | rfl⟩
  · rw [zpow_natCast, zpow_natCast, pow_smul_of_fixed hτ]; push_cast; rfl
  · rw [zpow_neg, zpow_natCast, zpow_neg, zpow_natCast, inv_smul_eq_iff, pow_smul_of_fixed hτ,
      map_add, map_smul, pow_apply_eq_self hτ n, LinearEquiv.coe_inv,
      LinearEquiv.apply_symm_apply]
    push_cast; module

theorem zpow_apply_tr (q : ℤ) : (linOf g ^ q) (trOf g) = trOf g := by
  rcases Int.eq_nat_or_neg q with ⟨n, rfl | rfl⟩
  · rw [zpow_natCast]; exact pow_apply_eq_self hτ n
  · rw [zpow_neg, zpow_natCast, LinearEquiv.coe_inv, LinearEquiv.symm_apply_eq,
      pow_apply_eq_self hτ n]

/-- **No point sees infinitely many iterates from the origin** when `L(g) τ = τ` is spacelike:
`|gᵠ x|² = |x|² + 2q ⟨x|τ⟩ + q² |τ|²`. -/
theorem finite_causallyRelated_zero_of_fixed_spacelike (hs : 0 < minkQ (trOf g))
    (x : Minkowski d) : Set.Finite {q : ℤ | CausallyRelated 0 ((g ^ q) • x)} := by
  refine (finite_int_quadratic_nonpos (a := minkQ x) (b := minkB x (trOf g)) hs).subset
    fun q hq => ?_
  have h := minkQ_nonpos_of_causallyRelated hq
  have hL : ∀ v, minkQ ((linOf g ^ q) v) = minkQ v := ((lorentz d).zpow_mem (linOf_mem g) q).1
  have hB : minkB ((linOf g ^ q) x) (trOf g) = minkB x (trOf g) := by
    conv_lhs => rw [← zpow_apply_tr hτ q]
    exact minkB_map hL x (trOf g)
  rw [sub_zero, zpow_smul_of_fixed hτ, minkQ_add, minkQ_smul, minkB_smul_right, hL, hB] at h
  show minkQ x + 2 * q * minkB x (trOf g) + (q : ℝ) ^ 2 * minkQ (trOf g) ≤ 0
  linarith

end fixedTauZ

section unipotentFacts

variable {U : Minkowski d ≃ₗ[ℝ] Minkowski d} (hU : ∀ v, minkQ (U v) = minkQ v)
  (hn : IsNilpotent (pOf U)) (hp : pOf U ≠ 0)
include hU hn hp

/-- On `J^⊥` the form is nonnegative, and null exactly on `J`. -/
theorem minkQ_nonneg_of_mem_minkOrth_nullPart {w : Minkowski d}
    (hw : w ∈ minkOrth (nullPart U)) : 0 ≤ minkQ w ∧ (minkQ w = 0 → w ∈ nullPart U) := by
  obtain ⟨v₀, hv, hv0⟩ := exists_mem_nullPart_ne_zero hU hn hp
  obtain ⟨h1, h2⟩ := minkQ_nonneg_of_null_orth (minkQ_eq_zero_of_mem_nullPart hv) hv0 (hw v₀ hv)
  refine ⟨h1, fun h0 => ?_⟩
  obtain ⟨c, rfl⟩ := h2 h0
  exact smul_mem _ _ hv

/-- **`p x ∈ J` iff `x ∈ J^⊥`** (l.2115–2116: "`|p(x)|² = 0`, i.e. `x ∈ J^⊥`"). -/
theorem pOf_mem_nullPart_iff {y : Minkowski d} :
    pOf U y ∈ nullPart U ↔ y ∈ minkOrth (nullPart U) := by
  refine ⟨fun h => ?_, pOf_mem_nullPart hU hn hp⟩
  obtain ⟨vₙ, v₁, v₀, -, h0, -, hq0, hJ, -, hb10, -⟩ := unipotent_frame hU hn hp
  rw [hJ] at h
  obtain ⟨c, hc⟩ := mem_span_singleton.1 h
  have hs := star_identity hU v₁ y
  rw [← hc, h0, minkB_smul_right, minkB_smul_right, hb10, ← minkQ_eq_minkB, hq0] at hs
  have hv0y : minkB v₀ y = 0 := by linarith
  rw [hJ]
  intro j hj
  obtain ⟨a, rfl⟩ := mem_span_singleton.1 hj
  show minkB (a • v₀) y = 0
  rw [minkB_smul_left, hv0y, mul_zero]

/-- `|p x|² ≥ 0`, null exactly for `x ∈ J^⊥`. -/
theorem minkQ_pOf_nonneg (y : Minkowski d) :
    0 ≤ minkQ (pOf U y) ∧ (minkQ (pOf U y) = 0 ↔ y ∈ minkOrth (nullPart U)) := by
  obtain ⟨h1, h2⟩ := minkQ_nonneg_of_mem_minkOrth_nullPart hU hn hp
    (pOf_apply_mem_minkOrth_nullPart U y)
  refine ⟨h1, fun h0 => (pOf_mem_nullPart_iff hU hn hp).1 (h2 h0), fun h => ?_⟩
  exact minkQ_eq_zero_of_mem_nullPart (pOf_mem_nullPart hU hn hp h)

end unipotentFacts

section parabolic

variable {R U : Minkowski d ≃ₗ[ℝ] Minkowski d} (hR : R ∈ lorentz d) (hU : U ∈ lorentz d)
  (hRe : IsElliptic R) (hn : IsNilpotent (pOf U)) (hU1 : U ≠ 1) (hc : R * U = U * R)

include hR hU hRe hn hU1 hc

theorem pOf_pow_R (k : ℕ) (y : Minkowski d) : pOf U ((R ^ k) y) = pOf U y := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [linEquiv_pow_succ_apply, ← pOf_comm_of_comm hc, parabolic_R_pOf hR hU hRe hn hU1 hc, ih]

variable {g : isom d} (hg : linOf g = R * U) (hτR : R (trOf g) = trOf g)
include hg hτR

/-- **The parabolic iterates** (l.2096–2101): `gⁿ x = Rⁿ x + n (p x + τ) + C(n,2) (p² x + p τ)
+ C(n,3) p² τ`, for `τ` fixed by `R`. -/
theorem pow_smul_parabolic (n : ℕ) (x : Minkowski d) :
    (g ^ n) • x = (R ^ n) x + (n : ℝ) • (pOf U x + trOf g) +
      ch2 n • (pOf U (pOf U x) + pOf U (trOf g)) + ch3 n • pOf U (pOf U (trOf g)) := by
  have hRp := parabolic_R_pOf hR hU hRe hn hU1 hc
  have hp3 := pOf_pOf_pOf hU.1 hn (pOf_ne_zero hU1)
  induction n with
  | zero => simp [ch2, ch3]
  | succ n ih =>
    rw [pow_succ', mul_smul, ih, smul_eq_lin_add, hg, LinearEquiv.mul_apply,
      apply_eq_add_pOf U]
    simp only [map_add, map_smul, hRp, pOf_pow_R hR hU hRe hn hU1 hc, hp3, hτR, smul_zero,
      add_zero, zero_add, ← linEquiv_pow_succ_apply]
    simp only [ch2, ch3]
    push_cast
    module

/-- The iterate splits orthogonally into the elliptic part and the `R`-fixed part. -/
theorem minkQ_pow_smul_sub_parabolic (n : ℕ) (x : Minkowski d) :
    minkQ ((g ^ n) • x - x) = minkQ ((R ^ n) x - x) +
      minkQ ((n : ℝ) • (pOf U x + trOf g) + ch2 n • (pOf U (pOf U x) + pOf U (trOf g)) +
        ch3 n • pOf U (pOf U (trOf g))) := by
  have hRp := parabolic_R_pOf hR hU hRe hn hU1 hc
  set s := (n : ℝ) • (pOf U x + trOf g) + ch2 n • (pOf U (pOf U x) + pOf U (trOf g)) +
    ch3 n • pOf U (pOf U (trOf g)) with hsdef
  have hs : R s = s := by
    simp only [hsdef, map_add, map_smul, hRp, hτR]
  rw [pow_smul_parabolic hR hU hRe hn hU1 hc hg hτR,
    show (R ^ n) x + (n : ℝ) • (pOf U x + trOf g) + ch2 n • (pOf U (pOf U x) + pOf U (trOf g)) +
      ch3 n • pOf U (pOf U (trOf g)) - x = ((R ^ n) x - x) + s by rw [hsdef]; abel,
    minkQ_add, minkB_pow_sub_fixed hR.1 hs]
  ring

omit hτR in
/-- **[7.P], linear case `τ = 0`: the complement of `Ω_g` is the set of `R`-periodic points of
the hyperplane `J^⊥`** (l.2109–2120). -/
theorem achronalDomain_parabolic_linear (h0 : trOf g = 0) :
    achronalDomain g = {x | ¬(x ∈ minkOrth (nullPart U) ∧ ∃ n : ℕ, 0 < n ∧ (R ^ n) x = x)} := by
  have hτR : R (trOf g) = trOf g := by rw [h0, map_zero]
  obtain ⟨u, hu, hAu⟩ := hRe.exists_fixed_timelike hR
  have hp0 := pOf_ne_zero hU1
  have key : ∀ n : ℕ, ∀ x, minkQ ((g ^ n) • x - x) =
      minkQ ((R ^ n) x - x) + (n : ℝ) ^ 2 * minkQ (pOf U x) := fun n x => by
    rw [minkQ_pow_smul_sub_parabolic hR hU hRe hn hU1 hc hg hτR, h0]
    simp only [map_zero, add_zero, smul_zero]
    have h2 := pOf_pOf_mem_nullPart hU.1 hn hp0 x
    rw [minkQ_add, minkQ_smul, minkQ_smul, minkQ_eq_zero_of_mem_nullPart h2, minkB_smul_left,
      minkB_smul_right, mem_minkOrth.1 h2.2 _ ⟨x, rfl⟩]
    ring
  ext x
  rw [mem_achronalDomain_iff, Set.mem_setOf_eq]
  obtain ⟨hq0, hq1⟩ := minkQ_pOf_nonneg hU.1 hn hp0 x
  constructor
  · rintro h ⟨hxJ, n, hn', hper⟩
    have := h n hn'
    rw [key, hper, sub_self, minkQ_zero, (hq1.2 hxJ), mul_zero, add_zero] at this
    exact lt_irrefl _ this
  · intro hx n hn'
    rw [key]
    have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
    have hA := minkQ_pow_sub_nonneg hR.1 hu.2 hAu n x
    by_cases hper : (R ^ n) x = x
    · have hxJ : x ∉ minkOrth (nullPart U) := fun hxJ => hx ⟨hxJ, n, hn', hper⟩
      have : 0 < minkQ (pOf U x) := lt_of_le_of_ne hq0 fun e => hxJ (hq1.1 e.symm)
      nlinarith
    · have : 0 < minkQ ((R ^ n) x - x) :=
        lt_of_le_of_ne hA fun e => hper (pow_apply_eq_of_minkQ_eq_zero hR.1 hu.2 hAu e.symm)
      nlinarith

omit hτR in
/-- In the linear case `Ω_g` is open: its complement is `J^⊥ ∩ ker (R^N − id)`. -/
theorem isOpen_achronalDomain_parabolic_linear (h0 : trOf g = 0) :
    IsOpen (achronalDomain g) := by
  obtain ⟨N, -, hN⟩ := exists_periodic_iff R
  rw [achronalDomain_parabolic_linear hR hU hRe hn hU1 hc hg h0]
  have : {x | ¬(x ∈ minkOrth (nullPart U) ∧ ∃ n : ℕ, 0 < n ∧ (R ^ n) x = x)} =
      ((minkOrth (nullPart U) : Set (Minkowski d)) ∩
        (LinearMap.ker (pOf (R ^ N)) : Set (Minkowski d)))ᶜ := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_inter_iff, SetLike.mem_coe,
      LinearMap.mem_ker, pOf_apply, sub_eq_zero, hN x]
  rw [this]
  exact ((Submodule.closed_of_finiteDimensional _).inter
    (Submodule.closed_of_finiteDimensional _)).isOpen_compl

/-- **[7.P], tangent case: `Ω_g = 𝐌ⁿ`** (l.2122–2138). Barbot's normalisation `τ ⊥ v₁` is not
needed, only `R τ = τ`. -/
theorem achronalDomain_parabolic_tangent
    (ht : IsTangentCase U (g : Minkowski d ≃ᵃ[ℝ] Minkowski d)) : achronalDomain g = Set.univ := by
  obtain ⟨u, hu, hAu⟩ := hRe.exists_fixed_timelike hR
  have hp0 := pOf_ne_zero hU1
  have hτJ : trOf g ∈ minkOrth (nullPart U) := ht.1
  have hτI : trOf g ∉ LinearMap.range (pOf U) := fun h =>
    ht.2 ((parabolic_mem_range_iff hR hU hRe hn hU1 hc hg hτR).2 h)
  have hpτ := pOf_mem_nullPart hU.1 hn hp0 hτJ
  have hp2τ : pOf U (pOf U (trOf g)) = 0 := pOf_eq_zero_of_mem_nullPart hU.1 hpτ
  refine Set.eq_univ_iff_forall.2 fun x => mem_achronalDomain_iff.2 fun n hn' => ?_
  rw [minkQ_pow_smul_sub_parabolic hR hU hRe hn hU1 hc hg hτR, hp2τ, smul_zero, add_zero]
  set P := pOf U x + trOf g
  set Q := pOf U (pOf U x) + pOf U (trOf g)
  have hP : P ∈ minkOrth (nullPart U) := add_mem (pOf_apply_mem_minkOrth_nullPart U x) hτJ
  have hQ : Q ∈ nullPart U := add_mem (pOf_pOf_mem_nullPart hU.1 hn hp0 x) hpτ
  have hPQ : minkB P Q = 0 := by rw [minkB_comm]; exact hP Q hQ
  rw [minkQ_add, minkQ_smul, minkQ_smul, minkQ_eq_zero_of_mem_nullPart hQ, minkB_smul_left,
    minkB_smul_right, hPQ]
  obtain ⟨hP0, hP1⟩ := minkQ_nonneg_of_mem_minkOrth_nullPart hU.1 hn hp0 hP
  have hPpos : 0 < minkQ P := lt_of_le_of_ne hP0 fun e => hτI (by
    have h1 := nullPart_le_range U (hP1 e.symm)
    have h2 : trOf g = P - pOf U x := by simp [P]
    rw [h2]; exact sub_mem h1 ⟨x, rfl⟩)
  have hA := minkQ_pow_sub_nonneg hR.1 hu.2 hAu n x
  have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
  nlinarith

/-- **[7.P], transverse case: `|gⁿ x − x|² → −∞`** (l.2140–2161): it is eventually negative, the
leading term being `(q−1)(5−q)/12 · |p τ|²` after division by `q²`. -/
theorem eventually_minkQ_neg_parabolic_transverse
    (ht : IsTransverseCase U (g : Minkowski d ≃ᵃ[ℝ] Minkowski d)) (x : Minkowski d) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → minkQ ((g ^ n) • x - x) < 0 := by
  obtain ⟨u, hu, hAu⟩ := hRe.exists_fixed_timelike hR
  obtain ⟨C, hC⟩ := minkQ_pow_sub_le hR.1 hu.2 hAu x
  have hp0 := pOf_ne_zero hU1
  set τ := trOf g
  set m := minkQ (pOf U τ)
  have hm : 0 < m := by
    obtain ⟨h1, h2⟩ := minkQ_nonneg_of_mem_minkOrth_nullPart hU.1 hn hp0
      (pOf_apply_mem_minkOrth_nullPart U τ)
    exact lt_of_le_of_ne h1 fun e => ht ((pOf_mem_nullPart_iff hU.1 hn hp0).1 (h2 e.symm))
  set P := pOf U x + τ
  set Q := pOf U (pOf U x) + pOf U τ
  set T := pOf U (pOf U τ)
  have hx2 := pOf_pOf_mem_nullPart hU.1 hn hp0 x
  have hT := pOf_pOf_mem_nullPart hU.1 hn hp0 τ
  have hQQ : minkQ Q = m := by
    rw [minkQ_add, minkQ_eq_zero_of_mem_nullPart hx2, minkB_comm,
      mem_minkOrth.1 hx2.2 _ ⟨τ, rfl⟩]; ring
  have hTT : minkQ T = 0 := minkQ_eq_zero_of_mem_nullPart hT
  have hQT : minkB Q T = 0 := by
    rw [minkB_add_left, mem_minkOrth.1 hT.2 _ ⟨pOf U x, rfl⟩,
      mem_minkOrth.1 hT.2 _ ⟨τ, rfl⟩, add_zero]
  have hPT : minkB P T = -m := by
    have hs := star_identity hU.1 τ (pOf U τ)
    rw [mem_minkOrth.1 hT.2 _ ⟨τ, rfl⟩, add_zero, ← minkQ_eq_minkB] at hs
    rw [minkB_add_left, mem_minkOrth.1 hT.2 _ ⟨x, rfl⟩, zero_add]; linarith
  obtain ⟨N, hN⟩ := exists_quartic_neg C (minkQ P) (minkB P Q) hm
  refine ⟨N, fun n hn' => ?_⟩
  rw [minkQ_pow_smul_sub_parabolic hR hU hRe hn hU1 hc hg hτR, minkQ_smul_add3, hQQ, hTT, hQT,
    hPT]
  have e : (n : ℝ) ^ 2 * minkQ P + ch2 n ^ 2 * m + ch3 n ^ 2 * 0 + 2 * n * ch2 n * minkB P Q +
      2 * n * ch3 n * -m + 2 * ch2 n * ch3 n * 0 =
      (n : ℝ) ^ 2 * (minkQ P + (n - 1) * minkB P Q + (n - 1) * (5 - n) * m / 12) := by
    simp only [ch2, ch3]; ring
  rw [e]
  linarith [hC n, hN n hn']

/-- **[7.P], transverse case: `Ω_g = ∅`** (l.2163). -/
theorem achronalDomain_parabolic_transverse
    (ht : IsTransverseCase U (g : Minkowski d ≃ᵃ[ℝ] Minkowski d)) : achronalDomain g = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.2 fun x hx => ?_
  obtain ⟨N, hN⟩ := eventually_minkQ_neg_parabolic_transverse hR hU hRe hn hU1 hc hg hτR ht x
  have := mem_achronalDomain_iff.1 hx (N + 1) (Nat.succ_pos N)
  linarith [hN (N + 1) (Nat.le_succ N)]

omit hτR in
/-- **`Ω_g` is open for every parabolic `g`** (l.2026's "open set", confirmed in the parabolic
class): after conjugation by a translation it is `𝐌ⁿ ∖ (J^⊥ ∩ Per R)`, `𝐌ⁿ` or `∅`. -/
theorem isOpen_achronalDomain_parabolic : IsOpen (achronalDomain g) := by
  have hrange := parabolic_range_le_minkOrth_nullPart hR hU hRe hn hU1 hc
  rcases linear_or_tangent_or_transverse U (g : Minkowski d ≃ᵃ[ℝ] Minkowski d) with hL | hT | hT
  · obtain ⟨v, hv⟩ := IsLinearCase.exists_transConj_eq_zero hL
    refine isOpen_achronalDomain_of_isomConj (v := v) ?_
    exact isOpen_achronalDomain_parabolic_linear hR hU hRe hn hU1 hc
      (by rw [linOf_isomConj]; exact hg) hv
  · obtain ⟨vₙ, v₁, -, h1, -, -, -, -, hq1, -⟩ := unipotent_frame hU.1 hn (pOf_ne_zero hU1)
    obtain ⟨v, hv, -⟩ := parabolic_exists_transConj_normal hR hU hRe hn hU1 hc hg
      (v₁ := v₁) ⟨vₙ, h1⟩ hq1.ne'
    refine isOpen_achronalDomain_of_isomConj (v := v) ?_
    have hT' : IsTangentCase U (transConj v (g : Minkowski d ≃ᵃ[ℝ] Minkowski d)) := by
      refine ⟨?_, fun h => hT.2 ((isLinearCase_transConj_iff v _).1 h)⟩
      have hr : LinearMap.range (pOf (linOf g)) ≤ minkOrth (nullPart U) := by
        rw [hg]; exact hrange
      rw [transPart_transConj_mem_iff hr v]; exact hT.1
    rw [achronalDomain_parabolic_tangent hR hU hRe hn hU1 hc
      (g := isomConj v g) (by rw [linOf_isomConj]; exact hg) hv hT']
    exact isOpen_univ
  · obtain ⟨vₙ, v₁, -, h1, -, -, -, -, hq1, -⟩ := unipotent_frame hU.1 hn (pOf_ne_zero hU1)
    obtain ⟨v, hv, -⟩ := parabolic_exists_transConj_normal hR hU hRe hn hU1 hc hg
      (v₁ := v₁) ⟨vₙ, h1⟩ hq1.ne'
    refine isOpen_achronalDomain_of_isomConj (v := v) ?_
    have hT' : IsTransverseCase U (transConj v (g : Minkowski d ≃ᵃ[ℝ] Minkowski d)) :=
      (parabolic_isTransverseCase_transConj_iff hR hU hRe hn hU1 hc hg v).2 hT
    rw [achronalDomain_parabolic_transverse hR hU hRe hn hU1 hc
      (g := isomConj v g) (by rw [linOf_isomConj]; exact hg) hv hT']
    exact isOpen_empty

end parabolic

/-! ### Non-vacuity of the parabolic linear and transverse cases (`d ≥ 2`) -/

section parabolicWitness

variable {i j : Fin d} (hij : i ≠ j)

/-- The null direction `t + eᵢ` of `stdNullRot hij 1` spans its `J`. -/
theorem stdNullRot_u_mem_nullPart :
    timeUnit d + spaceUnit i ∈ nullPart (stdNullRot hij 1) := by
  have huu : minkB (timeUnit d + spaceUnit i) (timeUnit d + spaceUnit i) = 0 := by
    rw [← minkQ_eq_minkB, minkQ_add, minkQ_timeUnit, minkQ_spaceUnit, minkB_timeUnit_spaceUnit]
    ring
  have hue : minkB (spaceUnit j) (timeUnit d + spaceUnit i) = 0 := by
    rw [minkB_add_right, minkB_comm, minkB_timeUnit_spaceUnit,
      minkB_spaceUnit_spaceUnit hij.symm, add_zero]
  have hp : ∀ x, pOf (stdNullRot hij 1) x = (1 * minkB x (timeUnit d + spaceUnit i)) •
      spaceUnit j + (-(1 * minkB x (spaceUnit j)) - 1 ^ 2 / 2 *
        minkB x (timeUnit d + spaceUnit i)) • (timeUnit d + spaceUnit i) := fun x => by
    rw [pOf_apply]; show nullRotLin _ _ 1 x - x = _; rw [nullRotLin_apply]; abel
  refine ⟨⟨-spaceUnit j, ?_⟩, ?_⟩
  · rw [hp, minkB_neg_left, minkB_neg_left, hue, ← minkQ_eq_minkB, minkQ_spaceUnit]
    module
  · rintro w ⟨x, rfl⟩
    show minkB (pOf (stdNullRot hij 1) x) (timeUnit d + spaceUnit i) = 0
    rw [hp, minkB_add_left, minkB_smul_left, minkB_smul_left, hue, huu]; ring

/-- The null rotation `stdNullRot hij 1` itself, as an isometry: `τ = 0`, `R = id`. -/
noncomputable def nullRotIsom : isom d :=
  ⟨(stdNullRot hij 1).toAffineEquiv, mem_isom_iff.2 (stdNullRot_mem_lorentz hij 1)⟩

/-- The null rotation `stdNullRot hij 1` followed by the unit time translation. -/
noncomputable def nullRotTime : isom d :=
  ⟨AffineEquiv.constVAdd ℝ (Minkowski d) (timeUnit d) * (stdNullRot hij 1).toAffineEquiv,
    (isom d).mul_mem (constVAdd_mem_isom _) (mem_isom_iff.2 (stdNullRot_mem_lorentz hij 1))⟩

theorem stdNullRot_hyps :
    stdNullRot hij 1 ∈ lorentz d ∧ IsNilpotent (pOf (stdNullRot hij 1)) ∧ stdNullRot hij 1 ≠ 1 := by
  have hu0 : timeUnit d + spaceUnit i ≠ 0 := by
    intro h; have := congrArg Prod.fst h; simp [timeUnit, spaceUnit] at this
  exact ⟨stdNullRot_mem_lorentz hij 1, isUnipotent_nullRot _ _ _ 1,
    nullRot_ne_one _ _ _ hu0 one_ne_zero⟩

/-- **Witness of [7.P], linear case** (`achronalDomain_parabolic_linear`, with `R = id`):
`Ω = 𝐌ⁿ ∖ J^⊥` for the null rotation. -/
theorem achronalDomain_nullRotIsom :
    achronalDomain (nullRotIsom hij) = {x | x ∉ minkOrth (nullPart (stdNullRot hij 1))} := by
  obtain ⟨hU, hn, hU1⟩ := stdNullRot_hyps hij
  rw [achronalDomain_parabolic_linear (lorentz d).one_mem hU isElliptic_one hn hU1
    (by rw [one_mul, mul_one]) (g := nullRotIsom hij) (by rw [one_mul]; rfl)
    (show (stdNullRot hij 1) 0 = 0 from map_zero _)]
  ext x
  simp only [Set.mem_setOf_eq, one_pow, LinearEquiv.coe_one, id_eq, and_true]
  exact ⟨fun h hx => h ⟨hx, 1, one_pos⟩, fun h hx => h hx.1⟩

/-- **Witness of [7.P], transverse case** (`achronalDomain_parabolic_transverse`, with `R = id`):
`τ = t` is not in `J^⊥`, since `⟨t + eᵢ | t⟩ = −1`; so `Ω = ∅`. -/
theorem achronalDomain_nullRotTime : IsParabolic (linOf (nullRotTime hij)) ∧
    IsTransverseCase (stdNullRot hij 1) (nullRotTime hij : Minkowski d ≃ᵃ[ℝ] Minkowski d) ∧
    achronalDomain (nullRotTime hij) = ∅ := by
  obtain ⟨hU, hn, hU1⟩ := stdNullRot_hyps hij
  have hlin : linOf (nullRotTime hij) = stdNullRot hij 1 := by
    show AffineEquiv.linearHom (AffineEquiv.constVAdd ℝ (Minkowski d) (timeUnit d) *
      (stdNullRot hij 1).toAffineEquiv) = _
    rw [map_mul]; rfl
  have htr : trOf (nullRotTime hij) = timeUnit d := by
    show timeUnit d +ᵥ (stdNullRot hij 1) 0 = timeUnit d
    rw [map_zero, vadd_eq_add, add_zero]
  have ht : IsTransverseCase (stdNullRot hij 1)
      (nullRotTime hij : Minkowski d ≃ᵃ[ℝ] Minkowski d) := by
    intro h
    have h1 := mem_minkOrth.1 h _ (stdNullRot_u_mem_nullPart hij)
    have h2 : minkB (timeUnit d + spaceUnit i) (timeUnit d) = -1 := by
      rw [minkB_add_left, ← minkQ_eq_minkB, minkQ_timeUnit, minkB_comm,
        minkB_timeUnit_spaceUnit, add_zero]
    have h3 : minkB (timeUnit d + spaceUnit i) (trOf (nullRotTime hij)) = 0 := h1
    rw [htr, h2] at h3
    norm_num at h3
  refine ⟨by rw [hlin]; exact stdNullRot_isParabolic hij one_ne_zero, ht, ?_⟩
  exact achronalDomain_parabolic_transverse (lorentz d).one_mem hU isElliptic_one hn hU1
    (by rw [one_mul, mul_one]) (by rw [hlin, one_mul]) rfl ht

end parabolicWitness

/-! ### `blem:paranongh` — visibility of one point from another (l.2165–2209) -/

section paranongh

variable {R U : Minkowski d ≃ₗ[ℝ] Minkowski d} (hR : R ∈ lorentz d) (hU : U ∈ lorentz d)
  (hRe : IsElliptic R) (hn : IsNilpotent (pOf U)) (hU1 : U ≠ 1) (hc : R * U = U * R)
  {g : isom d} (hg : linOf g = R * U)
include hR hU hRe hn hU1 hc hg

/-- **`blem:paranongh`, transverse case, normal form**: `x = x₀` itself has all its large iterates
causally related to `x₀` (from `eventually_minkQ_neg_parabolic_transverse`), and they are pairwise
distinct points (`x₀` is not periodic). -/
theorem paranongh_transverse_normal (hτR : R (trOf g) = trOf g)
    (ht : IsTransverseCase U (g : Minkowski d ≃ᵃ[ℝ] Minkowski d)) (x₀ : Minkowski d) :
    IsAperiodic g x₀ ∧ Set.Infinite {q : ℤ | CausallyRelated x₀ ((g ^ q) • x₀)} := by
  obtain ⟨N, hN⟩ := eventually_minkQ_neg_parabolic_transverse hR hU hRe hn hU1 hc hg hτR ht x₀
  refine ⟨isAperiodic_of_eventually (N := N) fun n hn' he => ?_, ?_⟩
  · have := hN n hn'
    rw [he, sub_self, minkQ_zero] at this
    exact lt_irrefl _ this
  refine Set.infinite_of_injective_forall_mem (f := fun k : ℕ => ((N + k : ℕ) : ℤ))
    (fun a b h => by simpa using h) fun k => ?_
  show CausallyRelated x₀ ((g ^ ((N + k : ℕ) : ℤ)) • x₀)
  rw [zpow_natCast]
  exact causallyRelated_of_minkQ_nonpos (hN (N + k) (Nat.le_add_right N k)).le

/-- **`blem:paranongh`, transverse case** (l.2190–2200), for every transverse parabolic `g`:
`x = x₀` works, with infinitely many distinct iterates. -/
theorem paranongh_transverse (ht : IsTransverseCase U (g : Minkowski d ≃ᵃ[ℝ] Minkowski d))
    (x₀ : Minkowski d) :
    IsAperiodic g x₀ ∧ Set.Infinite {q : ℤ | CausallyRelated x₀ ((g ^ q) • x₀)} := by
  obtain ⟨vₙ, v₁, -, h1, -, -, -, -, hq1, -⟩ := unipotent_frame hU.1 hn (pOf_ne_zero hU1)
  obtain ⟨v, hv, -⟩ := parabolic_exists_transConj_normal hR hU hRe hn hU1 hc hg
    (v₁ := v₁) ⟨vₙ, h1⟩ hq1.ne'
  have hT' : IsTransverseCase U (transConj v (g : Minkowski d ≃ᵃ[ℝ] Minkowski d)) :=
    (parabolic_isTransverseCase_transConj_iff hR hU hRe hn hU1 hc hg v).2 ht
  obtain ⟨hap, hinf⟩ := paranongh_transverse_normal hR hU hRe hn hU1 hc (g := isomConj v g)
    (by rw [linOf_isomConj]; exact hg) hv hT' (v + x₀)
  have e : (isomTrans v)⁻¹ • (v + x₀) = x₀ := by
    show -v + (v + x₀) = x₀
    rw [neg_add_cancel_left]
  have hset : {q : ℤ | CausallyRelated x₀ ((g ^ q) • x₀)} =
      {q : ℤ | CausallyRelated (v + x₀) ((isomConj v g ^ q) • (v + x₀))} := by
    ext q
    simp only [Set.mem_setOf_eq]
    rw [isomConj_eq, causallyRelated_conj_iff, e]
  refine ⟨?_, by rw [hset]; exact hinf⟩
  have := (isAperiodic_isomConj v g (v + x₀)).1 hap
  rwa [neg_add_cancel_left] at this

omit hR hU hRe hn hU1 hc hg in
/-- Transport of the visibility set along a conjugation by a translation. -/
theorem visibility_isomConj (v : Minkowski d) (x₀ x : Minkowski d) :
    {q : ℤ | CausallyRelated (v + x₀) ((isomConj v g ^ q) • x)} =
      {q : ℤ | CausallyRelated x₀ ((g ^ q) • (-v + x))} := by
  ext q
  simp only [Set.mem_setOf_eq]
  rw [isomConj_eq, causallyRelated_conj_iff]
  have e : (isomTrans v)⁻¹ • (v + x₀) = x₀ := by
    show -v + (v + x₀) = x₀
    rw [neg_add_cancel_left]
  rw [e]; rfl

omit hR hU hRe hn hU1 hc hg in
/-- A set of integers containing all large naturals is infinite. -/
theorem infinite_of_forall_ge {S : Set ℤ} (N : ℕ) (h : ∀ n : ℕ, N ≤ n → (n : ℤ) ∈ S) :
    S.Infinite :=
  Set.infinite_of_injective_forall_mem (f := fun k : ℕ => ((N + k : ℕ) : ℤ))
    (fun a b h => by simpa using h) fun k => h (N + k) (Nat.le_add_right N k)

omit hR hU hRe hn hU1 hc hg in
theorem exists_quadratic_neg (β γ : ℝ) : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → γ + β * n - (n : ℝ) ^ 2 < 0 := by
  refine ⟨⌈|β| + |γ|⌉₊ + 1, fun n hn => ?_⟩
  have h1 := Nat.le_ceil (|β| + |γ|)
  have h2 : ((⌈|β| + |γ|⌉₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
  push_cast at h2
  have h3 : |β| + |γ| + 1 ≤ (n : ℝ) := by linarith
  nlinarith [le_abs_self β, le_abs_self γ, abs_nonneg β, abs_nonneg γ]

/-- **The visibility construction off `J^⊥`** — Barbot's choice "`⟨p²(x) + p(τ) | x₀⟩ > 0`"
(l.2202–2209), made with an `R`-fixed `x = s vₙ`. In the normal form `R τ = τ`, `p τ = 0` (which
covers the linear case `τ = 0` and the tangent normal form), for every `x₀ ∉ J^⊥` the
`q²`-coefficient of `|gᵠ x − x₀|²` is `|τ|² − ⟨x₀ | p² x⟩ = −1`. The point `x` is off `J^⊥`. -/
theorem paranongh_normal_of_not_mem (hτR : R (trOf g) = trOf g) (hpτ : pOf U (trOf g) = 0)
    {x₀ : Minkowski d} (hx₀ : x₀ ∉ minkOrth (nullPart U)) :
    ∃ x, x ∉ minkOrth (nullPart U) ∧
      Set.Infinite {q : ℤ | CausallyRelated x₀ ((g ^ q) • x)} := by
  have hp0 := pOf_ne_zero hU1
  set τ := trOf g
  have hτI : τ ∈ minkOrth (LinearMap.range (pOf U)) := by
    rw [← ker_pOf_eq_minkOrth hU.1, LinearMap.mem_ker]; exact hpτ
  have hτJ : τ ∈ minkOrth (nullPart U) := minkOrth_range_le_minkOrth_nullPart U hτI
  obtain ⟨vₙ, hRvₙ, hvₙ⟩ := parabolic_exists_fixed_not_mem hR hU hRe hn hU1 hc
  have hw := pOf_pOf_mem_nullPart hU.1 hn hp0 vₙ
  have hw0 : pOf U (pOf U vₙ) ≠ 0 := by
    intro h
    apply hvₙ
    rw [← pOf_mem_nullPart_iff hU.1 hn hp0]
    refine ⟨⟨vₙ, rfl⟩, ?_⟩
    show pOf U vₙ ∈ minkOrth (LinearMap.range (pOf U))
    rw [← ker_pOf_eq_minkOrth hU.1]; exact LinearMap.mem_ker.2 h
  have hJ := nullPart_eq_span_of_mem hw hw0
  have hκ : minkB (pOf U (pOf U vₙ)) x₀ ≠ 0 := by
    intro h; apply hx₀; rw [hJ]; intro j hj
    obtain ⟨a, rfl⟩ := mem_span_singleton.1 hj
    show minkB (a • _) x₀ = 0
    rw [minkB_smul_left, h, mul_zero]
  set s := (minkQ τ + 1) / minkB (pOf U (pOf U vₙ)) x₀
  have hs : s ≠ 0 := div_ne_zero
    (by linarith [(minkQ_nonneg_of_mem_minkOrth_nullPart hU.1 hn hp0 hτJ).1]) hκ
  set x := s • vₙ
  have hRx : R x = x := by rw [map_smul, hRvₙ]
  have hκx : minkB x₀ (pOf U (pOf U x)) = minkQ τ + 1 := by
    rw [show x = s • vₙ from rfl, map_smul, map_smul, minkB_smul_right,
      minkB_comm x₀ (pOf U (pOf U vₙ))]
    simp only [s]; field_simp
  have hx2 := pOf_pOf_mem_nullPart hU.1 hn hp0 x
  set P := pOf U x + τ
  have hP : P ∈ minkOrth (nullPart U) := add_mem (pOf_apply_mem_minkOrth_nullPart U x) hτJ
  have e1 : minkB P (pOf U (pOf U x)) = 0 := by rw [minkB_comm]; exact hP _ hx2
  have e2 : minkB (pOf U x) τ = 0 := mem_minkOrth.1 hτI _ ⟨x, rfl⟩
  have s1 := star_identity hU.1 x x
  have s2 := star_identity hU.1 x (pOf U x)
  have e3 : minkB (pOf U x) (pOf U (pOf U x)) = 0 := mem_minkOrth.1 hx2.2 _ ⟨x, rfl⟩
  rw [e3, add_zero, ← minkQ_eq_minkB] at s2
  rw [minkB_comm (pOf U x) x, ← minkQ_eq_minkB] at s1
  have key : ∀ n : ℕ, minkQ ((g ^ n) • x - x₀) = minkQ (x - x₀) +
      n * (2 * minkB (x - x₀) P + minkQ (pOf U x) + (minkQ τ + 1)) - (n : ℝ) ^ 2 := by
    intro n
    rw [pow_smul_parabolic hR hU hRe hn hU1 hc hg hτR, hpτ, pow_apply_eq_self hRx]
    simp only [map_zero, add_zero, smul_zero]
    rw [show x + (n : ℝ) • P + ch2 n • pOf U (pOf U x) - x₀ =
      (1 : ℝ) • (x - x₀) + (n : ℝ) • P + ch2 n • pOf U (pOf U x) by module,
      minkQ_smul_add3, minkQ_eq_zero_of_mem_nullPart hx2, e1,
      minkB_sub_left x x₀ (pOf U (pOf U x)), hκx]
    have hQP : minkQ P = minkQ (pOf U x) + minkQ τ := by
      simp only [P]; rw [minkQ_add, e2]; ring
    rw [hQP]
    simp only [ch2]; linear_combination (n : ℝ) * ((n : ℝ) - 1) * s2
  obtain ⟨N, hN⟩ := exists_quadratic_neg (2 * minkB (x - x₀) P + minkQ (pOf U x) + (minkQ τ + 1))
    (minkQ (x - x₀))
  refine ⟨x, fun hxJ => hvₙ ?_, infinite_of_forall_ge N fun n hn' => ?_⟩
  · have : vₙ = s⁻¹ • x := by
      rw [show x = s • vₙ from rfl, smul_smul, inv_mul_cancel₀ hs, one_smul]
    rw [this]; exact smul_mem _ _ hxJ
  show CausallyRelated x₀ ((g ^ (n : ℤ)) • x)
  rw [zpow_natCast]
  refine causallyRelated_of_minkQ_nonpos ?_
  rw [key n]; linarith [hN n hn']

/-- **`blem:paranongh`, linear case, normal form `τ = 0`** — true for every `x₀`, with infinitely
many distinct iterates. Barbot's proof (l.2202–2209: take `x` with `⟨p²(x) | x₀⟩ > 0`) covers
`x₀ ∉ J^⊥` only, and is `paranongh_normal_of_not_mem`. For `x₀ ∈ J^⊥` the `q²`-term vanishes:
`|gᵠ x − x₀|² = |x − x₀|² − 2q ⟨x₀ | p x⟩` for `R`-fixed `x`, and `x = t u` (`u` an `R`-fixed
timelike vector, `|t|` large, the sign of `t` that of `⟨x₀ | p u⟩`) works for every `q ≥ 0`.
Either `x` is off `J^⊥`, hence in `Ω_g` (`achronalDomain_parabolic_linear`), hence not periodic. -/
theorem paranongh_linear_normal (h0 : trOf g = 0) (x₀ : Minkowski d) :
    ∃ x, IsAperiodic g x ∧ Set.Infinite {q : ℤ | CausallyRelated x₀ ((g ^ q) • x)} := by
  have hp0 := pOf_ne_zero hU1
  have hτR : R (trOf g) = trOf g := by rw [h0, map_zero]
  have hap : ∀ x, x ∉ minkOrth (nullPart U) → IsAperiodic g x := fun x hx =>
    isAperiodic_of_mem_achronalDomain (by
      rw [achronalDomain_parabolic_linear hR hU hRe hn hU1 hc hg h0]
      exact fun h => hx h.1)
  by_cases hx₀J : x₀ ∉ minkOrth (nullPart U)
  · obtain ⟨x, hx, hinf⟩ := paranongh_normal_of_not_mem hR hU hRe hn hU1 hc hg hτR
      (by rw [h0, map_zero]) hx₀J
    exact ⟨x, hap x hx, hinf⟩
  push Not at hx₀J
  obtain ⟨-, -, v₀, -, -, hv00, hq0, hJ, -⟩ := unipotent_frame hU.1 hn hp0
  have hv0J : v₀ ∈ nullPart U := hJ ▸ mem_span_singleton_self v₀
  -- for an `R`-fixed `x`: `|gⁿ x − x₀|² = |x − x₀|² − 2n ⟨x₀ | p x⟩`
  have key : ∀ x, R x = x → ∀ n : ℕ,
      minkQ ((g ^ n) • x - x₀) = minkQ (x - x₀) - 2 * n * minkB x₀ (pOf U x) := by
    intro x hRx n
    have hx2 := pOf_pOf_mem_nullPart hU.1 hn hp0 x
    have s1 := star_identity hU.1 x x
    have s2 := star_identity hU.1 x (pOf U x)
    have e1 : minkB (pOf U x) (pOf U (pOf U x)) = 0 := mem_minkOrth.1 hx2.2 _ ⟨x, rfl⟩
    have e2 : minkB x₀ (pOf U (pOf U x)) = 0 := by
      rw [minkB_comm]; exact mem_minkOrth.1 hx₀J _ hx2
    rw [e1, add_zero, ← minkQ_eq_minkB] at s2
    rw [minkB_comm (pOf U x) x, ← minkQ_eq_minkB] at s1
    rw [pow_smul_parabolic hR hU hRe hn hU1 hc hg hτR, h0, pow_apply_eq_self hRx]
    simp only [map_zero, add_zero, smul_zero]
    rw [show x + (n : ℝ) • pOf U x + ch2 n • pOf U (pOf U x) - x₀ =
      (1 : ℝ) • (x - x₀) + (n : ℝ) • pOf U x + ch2 n • pOf U (pOf U x) by module,
      minkQ_smul_add3, minkQ_eq_zero_of_mem_nullPart hx2, e1, minkB_sub_left, minkB_sub_left,
      e2, minkB_comm x₀ (pOf U x)]
    simp only [ch2]; linear_combination (n : ℝ) * s1 + (n : ℝ) * ((n : ℝ) - 1) * s2
  obtain ⟨u, hu, hAu⟩ := hRe.exists_fixed_timelike hR
  have hQu : 0 < -minkQ u := by linarith [hu.2]
  have hv0u : minkB u v₀ ≠ 0 := fun h => by
    have := minkQ_pos_of_orth_timelike hu.2 h hv00
    linarith
  set β := minkB x₀ (pOf U u)
  set T := (2 * |minkB u x₀| + |minkQ x₀|) / (-minkQ u) + 1 with hT
  have hT1 : 1 ≤ T := by
    have : 0 ≤ (2 * |minkB u x₀| + |minkQ x₀|) / (-minkQ u) := by positivity
    linarith
  have hTu : 2 * |minkB u x₀| + |minkQ x₀| ≤ T * (-minkQ u) := by
    rw [hT, add_mul, div_mul_cancel₀ _ hQu.ne']; linarith
  have hQ : ∀ t : ℝ, |t| = T → minkQ (t • u - x₀) ≤ 0 := fun t ht => by
    have e : minkQ (t • u - x₀) = t ^ 2 * minkQ u - 2 * t * minkB u x₀ + minkQ x₀ := by
      rw [sub_eq_add_neg, minkQ_add, minkQ_smul, minkQ_neg, minkB_smul_left, minkB_neg_right]
      ring
    have h1 : t ^ 2 = T ^ 2 := by rw [← sq_abs, ht]
    have h2 : -(2 * t * minkB u x₀) ≤ 2 * T * |minkB u x₀| := by
      have := neg_abs_le (t * minkB u x₀)
      rw [abs_mul, ht] at this; linarith
    have h3 : |minkQ x₀| ≤ T * |minkQ x₀| := le_mul_of_one_le_left (abs_nonneg _) hT1
    have h4 : T * (2 * |minkB u x₀| + |minkQ x₀|) ≤ T * (T * (-minkQ u)) :=
      mul_le_mul_of_nonneg_left hTu (by linarith)
    rw [e, h1]; nlinarith [le_abs_self (minkQ x₀)]
  obtain ⟨t, ht0, htβ, htT⟩ : ∃ t : ℝ, t ≠ 0 ∧ 0 ≤ t * β ∧ |t| = T := by
    have hT0 : 0 < T := by linarith
    rcases le_or_gt 0 β with hβ | hβ
    · exact ⟨T, hT0.ne', mul_nonneg hT0.le hβ, abs_of_pos hT0⟩
    · exact ⟨-T, neg_ne_zero.2 hT0.ne', by nlinarith, by rw [abs_neg, abs_of_pos hT0]⟩
  have hRx : R (t • u) = t • u := by rw [map_smul, hAu]
  have hxJ : t • u ∉ minkOrth (nullPart U) := fun h => by
    have h1 := mem_minkOrth.1 h v₀ hv0J
    rw [minkB_smul_right, minkB_comm] at h1
    exact mul_ne_zero ht0 hv0u h1
  refine ⟨t • u, hap _ hxJ, infinite_of_forall_ge 0 fun n _ => ?_⟩
  show CausallyRelated x₀ ((g ^ (n : ℤ)) • (t • u))
  rw [zpow_natCast]
  refine causallyRelated_of_minkQ_nonpos ?_
  rw [key _ hRx n, map_smul, minkB_smul_right]
  have := hQ t htT
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith [mul_nonneg hn0 htβ]

/-- **`blem:paranongh`, linear case** (l.2202–2209), for every parabolic `g` with a fixed point:
true for every `x₀`, with infinitely many distinct iterates. -/
theorem paranongh_linear (hL : IsLinearCase (g : Minkowski d ≃ᵃ[ℝ] Minkowski d))
    (x₀ : Minkowski d) :
    ∃ x, IsAperiodic g x ∧ Set.Infinite {q : ℤ | CausallyRelated x₀ ((g ^ q) • x)} := by
  obtain ⟨v, hv⟩ := IsLinearCase.exists_transConj_eq_zero hL
  obtain ⟨x, hxa, hx⟩ := paranongh_linear_normal hR hU hRe hn hU1 hc (g := isomConj v g)
    (by rw [linOf_isomConj]; exact hg) hv (v + x₀)
  refine ⟨-v + x, (isAperiodic_isomConj v g x).1 hxa, ?_⟩
  rwa [visibility_isomConj] at hx

/-- **`blem:paranongh`, tangent case, normal form (`R τ = τ`, `τ ∈ I^⊥`), `x₀ ∉ J^⊥`** — true,
with infinitely many distinct iterates (`Ω_g = 𝐌ⁿ`, so no point is periodic). -/
theorem paranongh_tangent_normal (hτR : R (trOf g) = trOf g) (hpτ : pOf U (trOf g) = 0)
    (ht : IsTangentCase U (g : Minkowski d ≃ᵃ[ℝ] Minkowski d)) {x₀ : Minkowski d}
    (hx₀ : x₀ ∉ minkOrth (nullPart U)) :
    ∃ x, IsAperiodic g x ∧ Set.Infinite {q : ℤ | CausallyRelated x₀ ((g ^ q) • x)} := by
  obtain ⟨x, -, hx⟩ := paranongh_normal_of_not_mem hR hU hRe hn hU1 hc hg hτR hpτ hx₀
  refine ⟨x, isAperiodic_of_mem_achronalDomain ?_, hx⟩
  rw [achronalDomain_parabolic_tangent hR hU hRe hn hU1 hc hg hτR ht]
  exact Set.mem_univ x

omit hRe hn in
/-- **… and false at `x₀ = 0` in the same normal form**: `L(g) τ = τ` is spacelike, so
`finite_causallyRelated_zero_of_fixed_spacelike` applies. Since `0 ∈ J^⊥`, the hypothesis
`x₀ ∉ J^⊥` of `paranongh_tangent_normal` cannot be dropped. -/
theorem not_paranongh_tangent_normal (hRe : IsElliptic R) (hn : IsNilpotent (pOf U))
    (hτR : R (trOf g) = trOf g) (hpτ : pOf U (trOf g) = 0)
    (ht : IsTangentCase U (g : Minkowski d ≃ᵃ[ℝ] Minkowski d)) (x : Minkowski d) :
    Set.Finite {q : ℤ | CausallyRelated 0 ((g ^ q) • x)} := by
  have hp0 := pOf_ne_zero hU1
  have hfix : linOf g (trOf g) = trOf g := by
    rw [hg, LinearEquiv.mul_apply, apply_eq_add_pOf U, hpτ, add_zero, hτR]
  have hτI : trOf g ∉ LinearMap.range (pOf U) := fun h =>
    ht.2 ((parabolic_mem_range_iff hR hU hRe hn hU1 hc hg hτR).2 h)
  obtain ⟨h1, h2⟩ := minkQ_nonneg_of_mem_minkOrth_nullPart hU.1 hn hp0 ht.1
  refine finite_causallyRelated_zero_of_fixed_spacelike hfix
    (lt_of_le_of_ne h1 fun e => hτI (nullPart_le_range U (h2 e.symm))) x

/-- **`blem:paranongh`, tangent case, for every tangent parabolic `g`** (the normal form
transported): there is a point `c` such that the lemma holds for every `x₀` off the affine
hyperplane `c + J^⊥`, with infinitely many distinct iterates, and fails at `x₀ = c`. The normal
form is `parabolic_exists_transConj_normal` (`R τ = τ`, `τ ⊥ v₁`); since also `τ ∈ J^⊥ ⊂ v₀^⊥`,
`τ ∈ span {v₀, v₁}^⊥ = I^⊥ = ker p`. -/
theorem paranongh_tangent (ht : IsTangentCase U (g : Minkowski d ≃ᵃ[ℝ] Minkowski d)) :
    ∃ c : Minkowski d,
      (∀ x₀, x₀ - c ∉ minkOrth (nullPart U) →
        ∃ x, IsAperiodic g x ∧ Set.Infinite {q : ℤ | CausallyRelated x₀ ((g ^ q) • x)}) ∧
      ∀ x, Set.Finite {q : ℤ | CausallyRelated c ((g ^ q) • x)} := by
  have hp0 := pOf_ne_zero hU1
  obtain ⟨vₙ, v₁, v₀, h1, -, -, -, hJ, hq1, -, -, -, hI⟩ := unipotent_frame hU.1 hn hp0
  obtain ⟨v, hv, hv1⟩ := parabolic_exists_transConj_normal hR hU hRe hn hU1 hc hg
    (v₁ := v₁) ⟨vₙ, h1⟩ hq1.ne'
  have hg' : linOf (isomConj v g) = R * U := by rw [linOf_isomConj]; exact hg
  have hT' : IsTangentCase U (transConj v (g : Minkowski d ≃ᵃ[ℝ] Minkowski d)) := by
    refine ⟨?_, fun h => ht.2 ((isLinearCase_transConj_iff v _).1 h)⟩
    have hr : LinearMap.range (pOf (linOf g)) ≤ minkOrth (nullPart U) := by
      rw [hg]; exact parabolic_range_le_minkOrth_nullPart hR hU hRe hn hU1 hc
    rw [transPart_transConj_mem_iff hr v]; exact ht.1
  have hpτ : pOf U (trOf (isomConj v g)) = 0 := by
    have hτJ : trOf (isomConj v g) ∈ minkOrth (nullPart U) := hT'.1
    have hv0 : minkB v₀ (trOf (isomConj v g)) = 0 :=
      mem_minkOrth.1 hτJ v₀ (hJ ▸ mem_span_singleton_self v₀)
    have hv1' : minkB (trOf (isomConj v g)) v₁ = 0 := hv1
    rw [← LinearMap.mem_ker, ker_pOf_eq_minkOrth hU.1, hI, mem_minkOrth]
    intro w hw
    obtain ⟨a, b, rfl⟩ := mem_span_pair.1 hw
    rw [minkB_add_left, minkB_smul_left, minkB_smul_left, hv0, minkB_comm v₁, hv1']
    ring
  refine ⟨-v, fun x₀ hx₀ => ?_, fun x => ?_⟩
  · have hx₀' : v + x₀ ∉ minkOrth (nullPart U) := by
      rwa [sub_neg_eq_add, add_comm] at hx₀
    obtain ⟨x, hxa, hx⟩ := paranongh_tangent_normal hR hU hRe hn hU1 hc (g := isomConj v g) hg'
      hv hpτ hT' hx₀'
    refine ⟨-v + x, (isAperiodic_isomConj v g x).1 hxa, ?_⟩
    rwa [visibility_isomConj] at hx
  · have hfin := not_paranongh_tangent_normal hR hU hU1 hc (g := isomConj v g) hg' hRe hn hv hpτ
      hT' (v + x)
    have e := visibility_isomConj (g := g) v (-v) (v + x)
    rw [add_neg_cancel, neg_add_cancel_left] at e
    rw [← e]; exact hfin

/-- **`blem:paranongh`, the class-by-class corrected form** (Lemma 7.1, l.2173–2180; DEC-98: the
formalization of record): for a parabolic `g` with decomposition `L(g) = R U`, there is a point
`c` such that for every `x₀` — unless `g` is tangent parabolic and `x₀ ∈ c + J^⊥` — some `x` has
infinitely many (distinct) `g`-iterates causally related to `x₀`; and in the tangent case the
exception is real, the conclusion failing at `x₀ = c`. Transverse and linear parabolic: every `x₀`
(`paranongh_transverse`, `paranongh_linear`); tangent: `x₀` off `c + J^⊥`
(`paranongh_tangent`). -/
theorem paranongh_corrected :
    ∃ c : Minkowski d,
      (∀ x₀ : Minkowski d,
        (IsTangentCase U (g : Minkowski d ≃ᵃ[ℝ] Minkowski d) → x₀ - c ∉ minkOrth (nullPart U)) →
          ∃ x, IsAperiodic g x ∧ Set.Infinite {q : ℤ | CausallyRelated x₀ ((g ^ q) • x)}) ∧
      (IsTangentCase U (g : Minkowski d ≃ᵃ[ℝ] Minkowski d) →
        ∀ x, Set.Finite {q : ℤ | CausallyRelated c ((g ^ q) • x)}) := by
  rcases linear_or_tangent_or_transverse U (g : Minkowski d ≃ᵃ[ℝ] Minkowski d) with
    hL | hT | hT
  · exact ⟨0, fun x₀ _ => paranongh_linear hR hU hRe hn hU1 hc hg hL x₀,
      fun ht => absurd hL ht.2⟩
  · obtain ⟨c, h1, h2⟩ := paranongh_tangent hR hU hRe hn hU1 hc hg hT
    exact ⟨c, fun x₀ hx₀ => h1 x₀ (hx₀ hT), fun _ => h2⟩
  · refine ⟨0, fun x₀ _ => ?_, fun ht => absurd ht.1 hT⟩
    obtain ⟨hap, hinf⟩ := paranongh_transverse hR hU hRe hn hU1 hc hg hT x₀
    exact ⟨x₀, hap, hinf⟩

end paranongh

/-! ### The counterexample to `blem:paranongh` (tangent case, `d ≥ 3`) -/

section counterexample

variable {i j k : Fin d} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)

/-- **The counterexample**: the null rotation `stdNullRot hij 1` (in the plane of `t, xᵢ, xⱼ`)
followed by the unit translation along `x_k`. Its translation part is spacelike and fixed by its
linear part, which is parabolic; it is in Barbot's tangent case. -/
noncomputable def nullRotShift : isom d :=
  ⟨AffineEquiv.constVAdd ℝ (Minkowski d) (spaceUnit k) * (stdNullRot hij 1).toAffineEquiv,
    (isom d).mul_mem (constVAdd_mem_isom _) (mem_isom_iff.2 (stdNullRot_mem_lorentz hij 1))⟩

theorem linOf_nullRotShift : linOf (nullRotShift (k := k) hij) = stdNullRot hij 1 := by
  show AffineEquiv.linearHom (AffineEquiv.constVAdd ℝ (Minkowski d) (spaceUnit k) *
    (stdNullRot hij 1).toAffineEquiv) = _
  rw [map_mul]
  rfl

theorem trOf_nullRotShift : trOf (nullRotShift (k := k) hij) = spaceUnit k := by
  show spaceUnit k +ᵥ (stdNullRot hij 1) 0 = spaceUnit k
  rw [map_zero, vadd_eq_add, add_zero]

include hik hjk in
theorem nullRotShift_fixed :
    linOf (nullRotShift (k := k) hij) (trOf (nullRotShift (k := k) hij)) =
      trOf (nullRotShift (k := k) hij) := by
  rw [linOf_nullRotShift, trOf_nullRotShift]
  show nullRotLin _ _ 1 (spaceUnit k) = spaceUnit k
  have h1 : minkB (spaceUnit k) (timeUnit d + spaceUnit i) = 0 := by
    rw [minkB_add_right, minkB_comm, minkB_timeUnit_spaceUnit, minkB_spaceUnit_spaceUnit hik.symm,
      add_zero]
  have h2 : minkB (spaceUnit k) (spaceUnit j) = 0 := minkB_spaceUnit_spaceUnit hjk.symm
  rw [nullRotLin_apply, h1, h2]
  simp

include hik hjk in
/-- **`blem:paranongh` fails** (DEC-27 counterexample): for `g = nullRotShift`, parabolic, and
`x₀ = 0`, every `x` has only finitely many iterates causally related to `x₀`. -/
theorem nullRotShift_counterexample :
    IsParabolic (linOf (nullRotShift (k := k) hij)) ∧ ∀ x : Minkowski d,
      Set.Finite {q : ℤ | CausallyRelated 0 ((nullRotShift (k := k) hij ^ q) • x)} := by
  refine ⟨by rw [linOf_nullRotShift]; exact stdNullRot_isParabolic hij one_ne_zero, fun x => ?_⟩
  refine finite_causallyRelated_zero_of_fixed_spacelike (nullRotShift_fixed hij hik hjk) ?_ x
  rw [trOf_nullRotShift, minkQ_spaceUnit]; exact one_pos

include hik hjk in
/-- **`nullRotShift` is in Barbot's tangent case** (`R = id`): `τ = e_k` lies in `I^⊥ ⊂ J^⊥` and
not in `I ⊂ span (e_j, t + eᵢ)`. -/
theorem nullRotShift_isTangentCase :
    IsTangentCase (stdNullRot hij 1)
      ((nullRotShift (k := k) hij : isom d) : Minkowski d ≃ᵃ[ℝ] Minkowski d) := by
  have hfix := nullRotShift_fixed hij hik hjk
  rw [linOf_nullRotShift, trOf_nullRotShift] at hfix
  have hU : stdNullRot hij 1 ∈ lorentz d := stdNullRot_mem_lorentz hij 1
  refine ⟨?_, ?_⟩
  · show trOf (nullRotShift (k := k) hij) ∈ _
    rw [trOf_nullRotShift]
    refine minkOrth_range_le_minkOrth_nullPart _ ?_
    rw [← ker_pOf_eq_minkOrth hU.1, LinearMap.mem_ker, pOf_apply, hfix, sub_self]
  · rintro ⟨x, hx⟩
    have hx' : pOf (stdNullRot hij 1) x = spaceUnit k := by
      rw [show (nullRotShift (k := k) hij : Minkowski d ≃ᵃ[ℝ] Minkowski d).linear =
        stdNullRot hij 1 from linOf_nullRotShift hij] at hx
      rw [hx]; exact trOf_nullRotShift hij
    obtain ⟨a, b, hab⟩ : ∃ a b : ℝ,
        pOf (stdNullRot hij 1) x = a • spaceUnit j + b • (timeUnit d + spaceUnit i) :=
      ⟨_, _, by
        rw [pOf_apply]; show nullRotLin _ _ 1 x - x = _; rw [nullRotLin_apply]; abel⟩
    rw [hab] at hx'
    have := congrArg (fun y : Minkowski d => y.2 k) hx'
    simp [spaceUnit, timeUnit, hjk.symm, hik.symm] at this

include hik hjk in
/-- … hence `Ω_g = 𝐌ⁿ` for it ([7.P] tangent), while no point sees infinitely many iterates from
`0`: every point is achronal to its orbit, and `blem:paranongh` fails at `x₀ = 0`. -/
theorem achronalDomain_nullRotShift : achronalDomain (nullRotShift (k := k) hij) = Set.univ := by
  have hU : stdNullRot hij 1 ∈ lorentz d := stdNullRot_mem_lorentz hij 1
  have hu0 : timeUnit d + spaceUnit i ≠ 0 := by
    intro h; have := congrArg Prod.fst h; simp [timeUnit, spaceUnit] at this
  exact achronalDomain_parabolic_tangent (lorentz d).one_mem hU isElliptic_one
    (isUnipotent_nullRot _ _ _ 1) (nullRot_ne_one _ _ _ hu0 one_ne_zero) (by rw [one_mul, mul_one])
    (by rw [linOf_nullRotShift, one_mul]) (by rfl) (nullRotShift_isTangentCase hij hik hjk)

end counterexample

/-! ### The counterexample with a non-trivial elliptic factor (`d ≥ 5`) -/

section halfTurn

variable (a b : Fin d)

/-- The **half-turn** in the plane `(x_a, x_b)`: `x ↦ x − 2⟨x|e_a⟩ e_a − 2⟨x|e_b⟩ e_b`. -/
noncomputable def halfTurnLin : Minkowski d →ₗ[ℝ] Minkowski d where
  toFun x := x - (2 * minkB x (spaceUnit a)) • spaceUnit a -
    (2 * minkB x (spaceUnit b)) • spaceUnit b
  map_add' x y := by simp only [minkB_add_left]; module
  map_smul' c x := by simp only [minkB_smul_left, RingHom.id_apply]; module

/-- The quarter-turn in the same plane, whose square is the half-turn. -/
noncomputable def quarterTurnLin : Minkowski d →ₗ[ℝ] Minkowski d where
  toFun x := x + (-minkB x (spaceUnit a) - minkB x (spaceUnit b)) • spaceUnit a +
    (minkB x (spaceUnit a) - minkB x (spaceUnit b)) • spaceUnit b
  map_add' x y := by simp only [minkB_add_left]; module
  map_smul' c x := by simp only [minkB_smul_left, RingHom.id_apply]; module

variable {a b} (hab : a ≠ b)
include hab

theorem halfTurn_facts :
    minkB (spaceUnit a) (spaceUnit a) = 1 ∧ minkB (spaceUnit b) (spaceUnit b) = 1 ∧
      minkB (spaceUnit a) (spaceUnit b) = 0 ∧ minkB (spaceUnit b) (spaceUnit a) = 0 :=
  ⟨by rw [← minkQ_eq_minkB, minkQ_spaceUnit], by rw [← minkQ_eq_minkB, minkQ_spaceUnit],
    minkB_spaceUnit_spaceUnit hab, minkB_spaceUnit_spaceUnit hab.symm⟩

theorem halfTurnLin_involutive : Function.Involutive (halfTurnLin a b) := fun x => by
  obtain ⟨h1, h2, h3, h4⟩ := halfTurn_facts hab
  simp only [halfTurnLin, LinearMap.coe_mk, AddHom.coe_mk, minkB_sub_left, minkB_smul_left,
    h1, h2, h3, h4]
  module

theorem minkQ_halfTurnLin (x : Minkowski d) : minkQ (halfTurnLin a b x) = minkQ x := by
  obtain ⟨-, -, h3, -⟩ := halfTurn_facts hab
  simp only [halfTurnLin, LinearMap.coe_mk, AddHom.coe_mk, sub_eq_add_neg, minkQ_add, minkQ_neg,
    minkQ_smul, minkB_add_left, minkB_neg_right, minkB_neg_left, minkB_smul_left,
    minkB_smul_right, minkQ_spaceUnit, h3]
  ring

theorem minkQ_quarterTurnLin (x : Minkowski d) : minkQ (quarterTurnLin a b x) = minkQ x := by
  obtain ⟨-, -, h3, -⟩ := halfTurn_facts hab
  simp only [quarterTurnLin, LinearMap.coe_mk, AddHom.coe_mk, minkQ_add, minkQ_smul,
    minkB_add_left, minkB_smul_left, minkB_smul_right, minkQ_spaceUnit, h3]
  ring

theorem halfTurnLin_eq_sq : halfTurnLin a b = quarterTurnLin a b ∘ₗ quarterTurnLin a b := by
  obtain ⟨h1, h2, h3, h4⟩ := halfTurn_facts hab
  refine LinearMap.ext fun x => ?_
  simp only [halfTurnLin, quarterTurnLin, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.coe_mk, AddHom.coe_mk, minkB_add_left, minkB_smul_left, h1, h2, h3, h4]
  module

/-- The half-turn as a linear automorphism (it is its own inverse). -/
noncomputable def halfTurn : Minkowski d ≃ₗ[ℝ] Minkowski d :=
  LinearEquiv.ofInvolutive (halfTurnLin a b) (halfTurnLin_involutive hab)

theorem halfTurn_apply (x : Minkowski d) : halfTurn hab x = halfTurnLin a b x := rfl

/-- `halfTurn` fixes every vector orthogonal to `e_a` and `e_b`. -/
theorem halfTurn_fix {w : Minkowski d} (ha : minkB w (spaceUnit a) = 0)
    (hb : minkB w (spaceUnit b) = 0) : halfTurn hab w = w := by
  rw [halfTurn_apply]
  simp only [halfTurnLin, LinearMap.coe_mk, AddHom.coe_mk, ha, hb, mul_zero, zero_smul, sub_zero]

/-- **The half-turn is a non-trivial elliptic element of `SO₀(1, d)`.** -/
theorem halfTurn_props :
    halfTurn hab ∈ lorentz d ∧ IsElliptic (halfTurn hab) ∧ halfTurn hab ≠ 1 := by
  have hQ : ∀ v, minkQ (halfTurn hab v) = minkQ v := minkQ_halfTurnLin hab
  have ht : halfTurn hab (timeUnit d) = timeUnit d :=
    halfTurn_fix hab (minkB_timeUnit_spaceUnit a) (minkB_timeUnit_spaceUnit b)
  refine ⟨mem_lorentz_of hQ (by rw [ht]; show (0 : ℝ) < 1; exact one_pos) ?_,
    isElliptic_of_fixed_timelike hQ (by rw [minkQ_timeUnit]; norm_num) ht, fun h => ?_⟩
  · exact det_eq_one_of_eq_sq (B := quarterTurnLin a b) hQ (halfTurnLin_eq_sq hab)
  · obtain ⟨h1, -, h3, h4⟩ := halfTurn_facts hab
    have e := congrArg (fun y => minkB y (spaceUnit a)) (LinearEquiv.congr_fun h (spaceUnit a))
    simp only [halfTurn_apply, LinearEquiv.coe_one, id, halfTurnLin, LinearMap.coe_mk,
      AddHom.coe_mk, minkB_sub_left, minkB_smul_left, h1, h3, h4] at e
    norm_num at e

end halfTurn

section counterexampleR

variable {i j k a b : Fin d} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (hab : a ≠ b)
  (hai : a ≠ i) (haj : a ≠ j) (hak : a ≠ k) (hbi : b ≠ i) (hbj : b ≠ j) (hbk : b ≠ k)

/-- **The counterexample with `R ≠ id`**: the half-turn in the `(x_a, x_b)` plane, composed with
the null rotation in `(t, xᵢ, xⱼ)`, then the unit translation along `x_k` (`d ≥ 5`). -/
noncomputable def halfTurnShift : isom d :=
  ⟨AffineEquiv.constVAdd ℝ (Minkowski d) (spaceUnit k) *
      (halfTurn hab * stdNullRot hij 1).toAffineEquiv,
    (isom d).mul_mem (constVAdd_mem_isom _) (mem_isom_iff.2
      ((lorentz d).mul_mem (halfTurn_props hab).1 (stdNullRot_mem_lorentz hij 1)))⟩

include hik hjk hai haj hak hbi hbj hbk in
/-- **`blem:paranongh` fails for `d ≥ 5` even when "parabolic" requires a non-trivial elliptic
factor** (§6.2, l.1974): `halfTurnShift` is `R ∘ U` with `R` the half-turn (`≠ id`), `U` the
null rotation, commuting, and from `x₀ = 0` every point sees only finitely many iterates. -/
theorem halfTurnShift_counterexample :
    (∃ R U : Minkowski d ≃ₗ[ℝ] Minkowski d, R ∈ lorentz d ∧ U ∈ lorentz d ∧ IsElliptic R ∧
      R ≠ 1 ∧ IsUnipotent U ∧ U ≠ 1 ∧ linOf (halfTurnShift (k := k) hij hab) = R * U ∧
      R * U = U * R) ∧
    ∀ x : Minkowski d,
      Set.Finite {q : ℤ | CausallyRelated 0 ((halfTurnShift (k := k) hij hab ^ q) • x)} := by
  obtain ⟨hR, hRe, hR1⟩ := halfTurn_props hab
  obtain ⟨hU, hn, hU1⟩ := stdNullRot_hyps hij
  have hlin : linOf (halfTurnShift (k := k) hij hab) = halfTurn hab * stdNullRot hij 1 := by
    show AffineEquiv.linearHom (AffineEquiv.constVAdd ℝ (Minkowski d) (spaceUnit k) *
      (halfTurn hab * stdNullRot hij 1).toAffineEquiv) = _
    rw [map_mul]; rfl
  have htr : trOf (halfTurnShift (k := k) hij hab) = spaceUnit k := by
    show spaceUnit k +ᵥ (halfTurn hab * stdNullRot hij 1) 0 = spaceUnit k
    rw [map_zero, vadd_eq_add, add_zero]
  -- `halfTurn` fixes the vectors of the null rotation
  have hfa : ∀ c : Fin d, c ≠ a → c ≠ b → halfTurn hab (spaceUnit c) = spaceUnit c :=
    fun c hca hcb => halfTurn_fix hab (minkB_spaceUnit_spaceUnit hca)
      (minkB_spaceUnit_spaceUnit hcb)
  have hft : halfTurn hab (timeUnit d) = timeUnit d :=
    halfTurn_fix hab (minkB_timeUnit_spaceUnit a) (minkB_timeUnit_spaceUnit b)
  have hQH : ∀ v, minkQ (halfTurn hab v) = minkQ v := minkQ_halfTurnLin hab
  have hBu : ∀ x, minkB (halfTurn hab x) (timeUnit d + spaceUnit i) =
      minkB x (timeUnit d + spaceUnit i) := fun x => by
    rw [← minkB_map hQH x (timeUnit d + spaceUnit i)]
    show _ = minkB (halfTurn hab x) (halfTurn hab (timeUnit d + spaceUnit i))
    rw [map_add, hft, hfa i hai.symm hbi.symm]
  have hBe : ∀ x, minkB (halfTurn hab x) (spaceUnit j) = minkB x (spaceUnit j) := fun x => by
    rw [← minkB_map hQH x (spaceUnit j)]
    show _ = minkB (halfTurn hab x) (halfTurn hab (spaceUnit j))
    rw [hfa j haj.symm hbj.symm]
  have hc : halfTurn hab * stdNullRot hij 1 = stdNullRot hij 1 * halfTurn hab := by
    refine LinearEquiv.ext fun x => ?_
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    show halfTurn hab (nullRotLin _ _ 1 x) = nullRotLin _ _ 1 (halfTurn hab x)
    rw [nullRotLin_apply, nullRotLin_apply, map_add, map_add, map_smul, map_smul, hBu, hBe,
      map_add, hft, hfa i hai.symm hbi.symm, hfa j haj.symm hbj.symm]
  have hUk : stdNullRot hij 1 (spaceUnit k) = spaceUnit k := by
    have hfix := nullRotShift_fixed hij hik hjk
    rwa [linOf_nullRotShift, trOf_nullRotShift] at hfix
  have hfix : linOf (halfTurnShift (k := k) hij hab) (trOf (halfTurnShift (k := k) hij hab)) =
      trOf (halfTurnShift (k := k) hij hab) := by
    rw [hlin, htr, LinearEquiv.mul_apply, hUk, hfa k hak.symm hbk.symm]
  refine ⟨⟨halfTurn hab, stdNullRot hij 1, hR, hU, hRe, hR1, hn, hU1, hlin, hc⟩, fun x => ?_⟩
  refine finite_causallyRelated_zero_of_fixed_spacelike hfix ?_ x
  rw [htr, minkQ_spaceUnit]; exact one_pos

end counterexampleR

/-- **`blem:paranongh` as printed, "infinitely many `g`-iterates" read as infinitely many
distinct POINTS `gᵠ x`** (the other reading of l.2177–2178; `Paranongh` counts exponents `q`). It
is the stronger of the two (`paranongh_of_paranonghPts`); both hold exactly for `d ≤ 2`. -/
def ParanonghPts (d : ℕ) : Prop :=
  ∀ g : isom d, IsParabolic (linOf g) → ∀ x₀ : Minkowski d, ∃ x : Minkowski d,
    ((fun q : ℤ => (g ^ q) • x) '' {q : ℤ | CausallyRelated x₀ ((g ^ q) • x)}).Infinite

theorem paranongh_of_paranonghPts (h : ParanonghPts d) : Paranongh d := fun g hg x₀ => by
  obtain ⟨x, hx⟩ := h g hg x₀
  exact ⟨x, Set.Infinite.of_image _ hx⟩

/-- **`blem:paranongh` holds for `d ≤ 2`** (Barbot's `n ≤ 3`), in the distinct-points reading,
hence in both: there the tangent case does not occur (Rem 6.1: `I = J^⊥`), and the linear and
transverse cases are `paranongh_linear`, `paranongh_transverse`; for `d ≤ 1` there is no
parabolic element (`two_le_of_unipotent`). -/
theorem paranonghPts_of_le_two (hd : d ≤ 2) : ParanonghPts d := by
  intro g hpar x₀
  obtain ⟨R, U, hR, hU, hRe, hn, hU1, hg, hc⟩ := hpar
  have hp0 := pOf_ne_zero hU1
  rcases linear_or_tangent_or_transverse U (g : Minkowski d ≃ᵃ[ℝ] Minkowski d) with hL | hT | hT
  · obtain ⟨x, hxa, hx⟩ := paranongh_linear hR hU hRe hn hU1 hc hg hL x₀
    exact ⟨x, infinite_image_of_isAperiodic hxa hx⟩
  · exfalso
    have hd2 : d = 2 := le_antisymm hd (two_le_of_unipotent hU.1 hn hp0)
    apply hT.2
    have h1 : trOf g ∈ LinearMap.range (pOf U) := by
      rw [range_eq_minkOrth_nullPart_of_dim_three hU.1 hd2 hn hp0]; exact hT.1
    show trOf g ∈ LinearMap.range (pOf (linOf g))
    rw [hg, range_pOf_mul_parabolic hR hU hRe hn hU1 hc]
    exact mem_sup_left h1
  · obtain ⟨hxa, hx⟩ := paranongh_transverse hR hU hRe hn hU1 hc hg hT x₀
    exact ⟨x₀, infinite_image_of_isAperiodic hxa hx⟩

theorem paranongh_of_le_two (hd : d ≤ 2) : Paranongh d :=
  paranongh_of_paranonghPts (paranonghPts_of_le_two hd)

/-- **`blem:paranongh` is false as printed for `d ≥ 3`** (Barbot's `n ≥ 4`), in the weaker
reading, hence in both. The counterexample has `R = id` (`IsParabolic` admits it, as Barbot's
"purely unipotent case" l.2865 does). -/
theorem not_paranongh (hd : 3 ≤ d) : ¬Paranongh d := by
  intro h
  have h01 : (⟨0, by omega⟩ : Fin d) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  have h02 : (⟨0, by omega⟩ : Fin d) ≠ ⟨2, by omega⟩ := by simp [Fin.ext_iff]
  have h12 : (⟨1, by omega⟩ : Fin d) ≠ ⟨2, by omega⟩ := by simp [Fin.ext_iff]
  obtain ⟨hpar, hfin⟩ := nullRotShift_counterexample h01 h02 h12
  obtain ⟨x, hx⟩ := h _ hpar 0
  exact hx (hfin x)

theorem not_paranonghPts (hd : 3 ≤ d) : ¬ParanonghPts d := fun h =>
  not_paranongh hd (paranongh_of_paranonghPts h)

/-- **`blem:paranongh` holds exactly in dimension `n ≤ 3`** (`d ≤ 2`), counting exponents… -/
theorem paranongh_iff : Paranongh d ↔ d ≤ 2 :=
  ⟨fun h => by by_contra hd; exact not_paranongh (by omega) h, paranongh_of_le_two⟩

/-- … and counting points. -/
theorem paranonghPts_iff : ParanonghPts d ↔ d ≤ 2 :=
  ⟨fun h => by by_contra hd; exact not_paranonghPts (by omega) h, paranonghPts_of_le_two⟩

/-- **Parabolic in §6.2's strict sense** (l.1973–1974: "`R` a non-trivial elliptic element"):
`IsParabolic` with `R ≠ id` added. `IsParabolic` admits `R = id`, as §9's "purely unipotent
case" (l.2865) requires. -/
def IsParabolicNontrivR (A : Minkowski d ≃ₗ[ℝ] Minkowski d) : Prop :=
  ∃ R U : Minkowski d ≃ₗ[ℝ] Minkowski d, R ∈ lorentz d ∧ U ∈ lorentz d ∧ IsElliptic R ∧
    R ≠ 1 ∧ IsUnipotent U ∧ U ≠ 1 ∧ A = R * U ∧ R * U = U * R

/-- `blem:paranongh` with "parabolic" read in §6.2's strict sense. -/
def ParanonghStrict (d : ℕ) : Prop :=
  ∀ g : isom d, IsParabolicNontrivR (linOf g) → ∀ x₀ : Minkowski d, ∃ x : Minkowski d,
    Set.Infinite {q : ℤ | CausallyRelated x₀ ((g ^ q) • x)}

/-- **`blem:paranongh` is false for `d ≥ 5` (Barbot's `n ≥ 6`) in the strict reading too**
(`halfTurnShift_counterexample`). Whether it holds for `d = 3, 4` in that reading is not
formalized (the tangent case would need `R` to fix `I + ⟨vₙ⟩ + ⟨τ⟩`, of dimension 4). -/
theorem not_paranonghStrict (hd : 5 ≤ d) : ¬ParanonghStrict d := by
  intro h
  have ne : ∀ m n : ℕ, (hm : m < d) → (hn : n < d) → m ≠ n →
      (⟨m, hm⟩ : Fin d) ≠ ⟨n, hn⟩ := fun m n _ _ hmn h => hmn (Fin.ext_iff.1 h)
  obtain ⟨hpar, hfin⟩ := halfTurnShift_counterexample
    (i := ⟨0, by omega⟩) (j := ⟨1, by omega⟩) (k := ⟨2, by omega⟩) (a := ⟨3, by omega⟩)
    (b := ⟨4, by omega⟩) (ne _ _ _ _ (by omega)) (ne _ _ _ _ (by omega))
    (ne _ _ _ _ (by omega)) (ne _ _ _ _ (by omega)) (ne _ _ _ _ (by omega))
    (ne _ _ _ _ (by omega)) (ne _ _ _ _ (by omega)) (ne _ _ _ _ (by omega))
    (ne _ _ _ _ (by omega)) (ne _ _ _ _ (by omega))
  obtain ⟨x, hx⟩ := h _ hpar 0
  exact hx (hfin x)

end Causal.Flat
