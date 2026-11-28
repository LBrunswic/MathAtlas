import GX.BTZ.Uniformization
import GX.BTZ.IsomE0
import GX.BTZ.AdmissibleLinear

/-!
# btz § 4.1: tangent translation parts, admissible representations, and the holonomy of `Reg M` around a BTZ line

Target `T-btz-admissible` (`roadmap/roadmap.toml`). `papers/btz/legacy/labeled/BTZ_1.tex`, § 4.1.

* **`btzdef:tangent_translation_part`** — `BTZ_1.tex:1135–1138`: `GX.BTZAdm.IsTangentTranslation`
  (with the origin-free form `GX.BTZAdm.IsTangentAt`, the independence of the origin
  `GX.BTZAdm.isTangentAt_iff`, and the line of fixed points of a parabolic linear part
  `GX.BTZAdm.exists_fixedLine_of_isParabolic`, `GX.BTZAdm.isTangentTranslation_iff_of_isParabolic`).
* **`btzdef:admissible_representation`** — `BTZ_1.tex:1139–1147`: the marked surface group
  `GX.BTZAdm.SurfaceGroup g s` (mathlib's `PresentedGroup` of `∏[aᵢ, bᵢ] ∏ cⱼ`) and
  `GX.BTZAdm.IsAdmissible`.
* `btzprop:holonomy_globally_hyperbolic_cauchy_compact` — `BTZ_1.tex:1153–1155` (proof
  l.1148–1151), **partial, unmarked**. Proved, 0 `sorry`, standard axioms, for `𝔼₀`-manifolds:
  for every developing pair `(𝒟, ρ)` of `Reg M`, the holonomy of a loop once around a BTZ line is
  **explicitly** a conjugate of the model's `btzHol 0 (2π)` (`GX.BTZAdm.holonomy_circleLoop`,
  `GX.BTZAdm.holonomy_btzLoop`), hence parabolic (`GX.BTZAdm.isParabolic_holonomy_btzLoop`) with
  tangent translation part (`GX.BTZAdm.isTangent_holonomy_btzLoop`), and such loops exist around
  every BTZ point (`GX.BTZAdm.exists_btzCircle`, `GX.BTZAdm.exists_isBTZLoop`). The marked
  conclusion `GX.BTZAdm.btzprop_holonomy_e0` (`ρ ∘ μ` admissible for a marking `μ`) is sorry-free:
  its Barbot input, the faithfulness and discreteness of the linear part
  (`GX.BTZAdm.e0RegM_linearPart_faithful_discrete`, l.1148–1149), is proved from lean-causal's
  Barbot (DEC-34) in `GX/BTZ/AdmissibleLinear.lean` (SCOPE (a)). The row stays unmarked
  on SCOPE (b) (`𝔼₀` only) and (d) (the marking is a hypothesis).

> Let $\phi$ be an affine parabolic isometry of $\mass{}$, we note $\phi_L$ its linear part and
> $\tau_\phi$ its translation part. We say $\tau_\phi$ is tangent if $\tau_\phi$ is normal to the
> direction of line of fixed points of $\phi_L$. (l.1135–1137)

> Let $\Gamma = \left\langle a_1,b_1,\cdots,a_g,b_g, c_1,\cdots,c_s \left |  \prod_{i=1}^g
> [a_i,b_i] \prod_{j=1}^s c_j=1\right.\right\rangle$ be a marked surface group. A marked
> representation $\rho:\Gamma \rightarrow \isom(\E^{1,2})$ is admissible if its linear part
> $\rho_L: \Gamma \rightarrow \GG$ is discrete and faithful; $\rho_L(c_i)$ is parabolic for all
> $i\in \lsem 1,s\rsem$; its translation part $\tau_\rho(c_i)$ is tangent for every
> $i\in \lsem 1,s\rsem$. (l.1140–1146)

> Since $M$ admits exactly $s$ BTZ lines, the holonomy of the peripheral generators is given by
> the holonomy around the BTZ lines which is parabolic. Furthermore, Barbot also shows (see
> \cite{barbot_globally_2004} section 7.3) that if the holonomy of some loop is parabolic, then
> the translation part is tangent. (l.1150)

> The holonomy of a globally hyperbolic Cauchy-compact $\mass{0}$-mani\-fold is admissible.
> (l.1154)

## Hypothesis checklist

| paper | here |
|---|---|
| `φ` an affine parabolic isometry of `E^{1,2}` (l.1135) | weakened: `φ : Causal.Flat.isom 2` (`Isom₀ = SO₀(1,2) ⋉ ℝ³`); parabolicity `Causal.Flat.IsParabolic (linOf φ)` is not assumed: the definition itself is stated for every `φ` and is independent of the origin for every `φ` (`isTangentAt_iff`, no parabolicity used) |
| "the line of fixed points of `φ_L`" (l.1137) | ✓ for `φ_L` parabolic it is a null line `ℝu` (`exists_fixedLine_of_isParabolic`); tangency is `⟨τ_φ, v⟩ = 0` for every fixed `v`, i.e. `⟨τ_φ, u⟩ = 0` (`isTangentTranslation_iff_of_isParabolic`) |
| "normal" (l.1137) | ✓ Minkowski-orthogonal (`Causal.Flat.minkB`) |
| `Γ` the marked surface group (l.1140) | ✓ `PresentedGroup {∏ᵢ ⁅aᵢ, bᵢ⁆ * ∏ⱼ cⱼ}` over generators `a, b : Fin g`, `c : Fin s` (mathlib's `⁅a, b⁆ = a b a⁻¹ b⁻¹`) |
| `ρ_L` discrete and faithful (l.1143) | ✓ `linearPart ∘ ρ` injective, its image a discrete subgroup of `SO₀(1,2)` (`Causal.Flat.lorentzTopology`, the operator-norm topology) |
| `ρ_L(cᵢ)` parabolic, `τ_ρ(cᵢ)` tangent (l.1144–1145) | ✓ `IsParabolic (linOf (ρ (c i)))`, `IsTangentTranslation (ρ (c i))` |
| the proposition: `M` GH Cauchy-compact (and Cauchy-maximal, the section's standing notation l.1127) | ⚠ `𝔼₀` only (T-btz-scope); Cauchy-compact read as DEC-107 (a compact `C¹` spacelike Cauchy surface); `π₁(Reg M)` not metabelian carried, as in `GX.e0RegM_holonomy` (the paper's `2g − 2 + s > 0` with anabelian `π₁`) |
| "the holonomy of the peripheral generators" (l.1150) | ⚠ read through loops: a peripheral generator is sent to the class of `σ · C · σ⁻¹`, `C` a small circle around a BTZ point in a chart (`IsBTZLoop`); the marking `Γ ≅ π₁(Reg M)` itself is T-btz-headline-repr's (needs-ruling), so the marked statement takes a homomorphism `μ` from `Γ` into the deck group sending each `cⱼ` to such a loop |
| Barbot § 7.3, parabolic ⇒ tangent (l.1150) | ✓ not used: around a BTZ line the holonomy is explicit (`holonomy_btzLoop`), conjugate to `btzHol 0 (2π)`, which fixes the origin of `𝐌³` |
| Barbot: `ρ_L` discrete and faithful (l.1148) | ✓ proved (`e0RegM_linearPart_faithful_discrete`, from `GX.BTZAdm.linearPart_comp_faithful_discrete`), SCOPE (a) |

## SCOPE (disclosed)

* (a) (closed) `e0RegM_linearPart_faithful_discrete` is proved (T-btz-linear-part-faithful), not by
  Barbot's route: Barbot reads the faithfulness off his classification (« `L` might be
  noninjective! », `barbot_globally_2004` l.3405–3440), whose family-(b) group in lean-causal is the
  restriction `Γ'_U` to the maximal unipotent subspace `U`, not `Γ'`. Here (`AdmissibleLinear`):
  the kernel of `L` on `ρ(π₁)` is trivial because otherwise every `L(γ)` maps a unit spacelike `e`
  to `± e` and `ρ(π₁)` is metabelian; the same argument shows `ρ(π₁)` nonelementary
  (`Causal.Flat.Lox.fix_second_null`) and `U = 𝐌³` (a `Γ`-invariant timelike line or plane is
  excluded); then `Causal.Flat.bprop_LU_discrete` (Prop 10.5, with the proved
  `auslanderCarriereDalbo`, `maxUnipotentSubspace`) gives `L(ρ(π₁))` discrete up to conjugation by
  an isometry of `𝐌³`. Inputs from the strict library: `GX.e0RegM_holonomy` (`ρ` faithful,
  `ρ(π₁)` torsion-free with a loxodromic element) and `GX.E0AbsMax.cor_abs_max_C1` (`Reg M` GH and
  Cauchy-complete). Cauchy-maximality enters only through the latter.
* (b) `𝔼₀` only: the rows wait on T-btz-scope; the definitions do not depend on it.
* (c) "parabolic" is lean-causal's `Causal.Flat.IsParabolic` (an elliptic part commuting with a
  non-trivial unipotent part, its D-1 reading); in `SO₀(1, 2)` such an element fixes exactly a null
  line (`exists_fixedLine_of_isParabolic`), so the paper's "line of fixed points" exists.
* (d) The marked form (`btzprop_holonomy_e0`) takes the marking as a hypothesis (an injective `μ`
  from `Γ` into the deck group of `Reg M̃`, each `cⱼ` sent to a BTZ loop); that every marking of
  `π₁(Σ*) ≅ π₁(Reg M)` is of this form is T-btz-headline-repr's.
* (e) The relator `∏[aᵢ,bᵢ]∏cⱼ` uses mathlib's commutator `⁅a, b⁆ = a * b * a⁻¹ * b⁻¹`; the paper
  does not fix a convention, so this is a reading (the other convention gives an isomorphic group).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GX

namespace BTZAdm

open Set Function Filter Topology Complex
open Causal.Flat
open scoped Real commutatorElement

/-! ## `btzdef:tangent_translation_part` -/

section Tangent

/-- `τ_φ` read at an origin `O`: `φ(O) − O` is Minkowski-orthogonal to every vector fixed by the
linear part. -/
def IsTangentAt (φ : isom 2) (O : Causal.Minkowski 2) : Prop :=
  ∀ v : Causal.Minkowski 2, linOf φ v = v → minkB (φ • O - O) v = 0

/-- **`btzdef:tangent_translation_part`**: the translation part `τ_φ = φ(0)` of `φ` is
Minkowski-normal to the fixed vectors of `φ_L` (for `φ_L` parabolic, to its line of fixed points,
`isTangentTranslation_iff_of_isParabolic`). -/
def IsTangentTranslation (φ : isom 2) : Prop :=
  ∀ v : Causal.Minkowski 2, linOf φ v = v → minkB (trOf φ) v = 0

theorem isTangentTranslation_iff_isTangentAt_zero (φ : isom 2) :
    IsTangentTranslation φ ↔ IsTangentAt φ 0 := by
  have h0 : φ • (0 : Causal.Minkowski 2) - 0 = trOf φ := by
    rw [smul_eq_lin_add, map_zero, zero_add, sub_zero]
  simp only [IsTangentTranslation, IsTangentAt, h0]

/-- An isometry `A` of `minkB` and a vector `v` it fixes: `⟨A w − w, v⟩ = 0`. -/
theorem minkB_sub_fixed {A : Causal.Minkowski 2 ≃ₗ[ℝ] Causal.Minkowski 2} (hA : A ∈ lorentz 2)
    {v : Causal.Minkowski 2} (hv : A v = v) (w : Causal.Minkowski 2) :
    minkB (A w - w) v = 0 := by
  have h := minkB_map (lorentz.minkQ_apply hA) w v
  rw [hv] at h
  rw [minkB_sub_left, h, sub_self]

/-- **Tangency does not depend on the origin**: `B((φ_L − 1) v, u) = 0` for `u` fixed by the
isometry `φ_L`. -/
theorem isTangentAt_iff (φ : isom 2) (O O' : Causal.Minkowski 2) :
    IsTangentAt φ O ↔ IsTangentAt φ O' := by
  have key : ∀ P P' : Causal.Minkowski 2, IsTangentAt φ P → IsTangentAt φ P' := by
    intro P P' hP v hv
    have hdec : φ • P' - P' = (φ • P - P) + (linOf φ (P' - P) - (P' - P)) := by
      rw [smul_eq_lin_add, smul_eq_lin_add, map_sub]; abel
    rw [hdec, minkB_add_left, hP v hv, minkB_sub_fixed (linOf_mem φ) hv, add_zero]
  exact ⟨key O O', key O' O⟩

/-- **The line of fixed points**: a parabolic element of `SO₀(1, 2)` fixes exactly a null line. -/
theorem exists_fixedLine_of_isParabolic {A : Causal.Minkowski 2 ≃ₗ[ℝ] Causal.Minkowski 2}
    (hA : A ∈ lorentz 2) (h : IsParabolic A) :
    ∃ u : Causal.Minkowski 2, u ≠ 0 ∧ Causal.Flat.minkQ u = 0 ∧ ∀ v, A v = v ↔ ∃ t : ℝ, v = t • u := by
  obtain ⟨hA1, u, hu0, hq, hAu⟩ := exists_fixed_null_of_isParabolic hA h
  obtain ⟨e, w, F⟩ := exists_isNullFrame2 hu0 hq
  have N := F.isNullRot2_of_fix hA hAu
  set a := -minkB (A e) w with ha
  have ha0 : a ≠ 0 := by
    intro h0
    rw [h0] at N
    exact hA1 (N.eq_one F)
  refine ⟨u, hu0, hq, fun v => ⟨fun hv => ?_, ?_⟩⟩
  · set α := -minkB v w
    set β := minkB v e
    set γ := -minkB v u
    have hexp : v = α • u + β • e + γ • w := F.expand v
    have hAv : A v = α • u + β • (a • u + e) + γ • ((a ^ 2 / 2) • u + a • e + w) := by
      conv_lhs => rw [hexp]
      rw [map_add, map_add, map_smul, map_smul, map_smul, N.hu, N.he, N.hw]
    have E : α • u + β • (a • u + e) + γ • ((a ^ 2 / 2) • u + a • e + w) =
        α • u + β • e + γ • w := by rw [← hAv, hv, ← hexp]
    have Ee := congrArg (fun z => minkB z e) E
    have Ew := congrArg (fun z => minkB z w) E
    simp only [minkB_add_left, minkB_smul_left, F.ue, F.ee, F.we, F.uw, F.ww] at Ee Ew
    have hγ : γ = 0 := by
      have : γ * a = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_right ha0
    have hβ : β = 0 := by
      rw [hγ] at Ew
      have : β * a = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_right ha0
    refine ⟨α, ?_⟩
    rw [hexp, hβ, hγ, zero_smul, zero_smul, add_zero, add_zero]
  · rintro ⟨t, rfl⟩
    rw [map_smul, hAu]

/-- For `φ_L` parabolic with line of fixed points `ℝu`, `τ_φ` is tangent iff `⟨τ_φ, u⟩ = 0`. -/
theorem isTangentTranslation_iff_of_isParabolic {φ : isom 2} {u : Causal.Minkowski 2}
    (hu : ∀ v, linOf φ v = v ↔ ∃ t : ℝ, v = t • u) :
    IsTangentTranslation φ ↔ minkB (trOf φ) u = 0 := by
  refine ⟨fun h => h u ((hu u).2 ⟨1, (one_smul ℝ u).symm⟩), fun h v hv => ?_⟩
  obtain ⟨t, rfl⟩ := (hu v).1 hv
  rw [minkB_smul_right, h, mul_zero]

/-- Conjugation moves the origin: `h φ h⁻¹` at `h O` is `φ` at `O`. -/
theorem isTangentAt_conj (h φ : isom 2) (O : Causal.Minkowski 2) :
    IsTangentAt (h * φ * h⁻¹) (h • O) ↔ IsTangentAt φ O := by
  have hlin : linOf (h * φ * h⁻¹) = linOf h * linOf φ * (linOf h)⁻¹ := by
    rw [linOf_mul, linOf_mul, linOf_inv]
  have hpt : (h * φ * h⁻¹) • (h • O) - h • O = linOf h (φ • O - O) := by
    rw [mul_smul, mul_smul, inv_smul_smul, smul_eq_lin_add h (φ • O), smul_eq_lin_add h O,
      map_sub]
    abel
  have hB : ∀ x y : Causal.Minkowski 2, minkB (linOf h x) (linOf h y) = minkB x y :=
    minkB_map (lorentz.minkQ_apply (linOf_mem h))
  constructor
  · intro H v hv
    have hv' : linOf (h * φ * h⁻¹) (linOf h v) = linOf h v := by
      rw [hlin]
      show linOf h (linOf φ ((linOf h).symm (linOf h v))) = linOf h v
      rw [LinearEquiv.symm_apply_apply, hv]
    have := H _ hv'
    rwa [hpt, hB] at this
  · intro H v hv
    have hv' : linOf φ ((linOf h).symm v) = (linOf h).symm v := by
      rw [hlin] at hv
      have := congrArg (linOf h).symm hv
      simpa using this
    have := H _ hv'
    rw [hpt, ← (linOf h).apply_symm_apply v, hB]
    exact this

/-- Tangency is invariant under conjugation in `Isom(𝐌³)`. -/
theorem isTangentTranslation_conj (h φ : isom 2) :
    IsTangentTranslation (h * φ * h⁻¹) ↔ IsTangentTranslation φ := by
  rw [isTangentTranslation_iff_isTangentAt_zero, isTangentTranslation_iff_isTangentAt_zero,
    isTangentAt_iff _ 0 (h • 0), isTangentAt_conj]

/-- The model's holonomy `btzHol 0 α` fixes the origin, so its translation part is tangent. -/
theorem isTangentTranslation_btzHol (α : ℝ) : IsTangentTranslation (btzHol 0 α) := by
  have h0 : trOf (btzHol 0 α) = 0 := by
    have h := btzHol_zpow_smul 0 α 1 0
    rw [parabAff_zpow, zpow_one, map_zero] at h
    have h' : btzHol 0 α • (0 : Causal.Minkowski 2) = 0 := by simpa using h
    rw [smul_eq_lin_add, map_zero, zero_add] at h'
    exact h'
  intro v _
  rw [h0]; simp [minkB]

end Tangent

/-! ## `btzdef:admissible_representation` -/

section Admissible

/-- The generators `a₁, b₁, …, a_g, b_g, c₁, …, c_s` of the marked surface group. -/
inductive SurfGen (g s : ℕ) : Type
  | a : Fin g → SurfGen g s
  | b : Fin g → SurfGen g s
  | c : Fin s → SurfGen g s

/-- The relator `∏ᵢ [aᵢ, bᵢ] ∏ⱼ cⱼ`. -/
def surfaceRel (g s : ℕ) : FreeGroup (SurfGen g s) :=
  (List.ofFn fun i : Fin g => ⁅FreeGroup.of (SurfGen.a (s := s) i), FreeGroup.of (SurfGen.b (s := s) i)⁆).prod *
    (List.ofFn fun j : Fin s => FreeGroup.of (SurfGen.c (g := g) j)).prod

/-- **The marked surface group** `Γ = ⟨a, b, c | ∏[aᵢ, bᵢ] ∏ cⱼ = 1⟩`. -/
abbrev SurfaceGroup (g s : ℕ) : Type := PresentedGroup ({surfaceRel g s} : Set (FreeGroup (SurfGen g s)))

/-- The peripheral generator `cⱼ`. -/
def SurfaceGroup.c {g s : ℕ} (j : Fin s) : SurfaceGroup g s := PresentedGroup.of (SurfGen.c j)

/-- The interior generator `aᵢ`. -/
def SurfaceGroup.a {g s : ℕ} (i : Fin g) : SurfaceGroup g s := PresentedGroup.of (SurfGen.a i)

/-- The interior generator `bᵢ`. -/
def SurfaceGroup.b {g s : ℕ} (i : Fin g) : SurfaceGroup g s := PresentedGroup.of (SurfGen.b i)

/-- The relation holds in `Γ`. -/
theorem SurfaceGroup.rel (g s : ℕ) :
    (List.ofFn fun i : Fin g => ⁅SurfaceGroup.a (s := s) i, SurfaceGroup.b i⁆).prod *
      (List.ofFn fun j : Fin s => SurfaceGroup.c (g := g) j).prod = 1 := by
  have h := PresentedGroup.one_of_mem (rels := ({surfaceRel g s} : Set (FreeGroup (SurfGen g s))))
    (Set.mem_singleton _)
  have key : ∀ R : Set (FreeGroup (SurfGen g s)), PresentedGroup.mk R (surfaceRel g s) =
      (List.ofFn fun i : Fin g => ⁅(PresentedGroup.of (SurfGen.a (s := s) i) : PresentedGroup R),
        PresentedGroup.of (SurfGen.b (s := s) i)⁆).prod *
      (List.ofFn fun j : Fin s => (PresentedGroup.of (SurfGen.c (g := g) j) : PresentedGroup R)).prod := by
    intro R
    simp only [surfaceRel, map_mul, map_list_prod, List.map_ofFn, Function.comp_def,
      map_commutatorElement]
    rfl
  rw [← h, key]
  rfl

/-- **`btzdef:admissible_representation`**: a marked representation `ρ : Γ → Isom(𝐌³)` is
admissible when its linear part is faithful with discrete image in `SO₀(1, 2)`, each `ρ_L(cⱼ)` is
parabolic and each translation part `τ_ρ(cⱼ)` is tangent. -/
structure IsAdmissible {g s : ℕ} (ρ : SurfaceGroup g s →* isom 2) : Prop where
  faithful : Function.Injective (linearPart.comp ρ)
  discrete : DiscreteTopology (linearPart.comp ρ).range
  parabolic : ∀ j : Fin s, IsParabolic (linOf (ρ (SurfaceGroup.c j)))
  tangent : ∀ j : Fin s, IsTangentTranslation (ρ (SurfaceGroup.c j))

end Admissible

/-! ## The holonomy of `Reg M` around a BTZ line -/

section Holonomy

/-- The point `(τ, r e^{iθ})` of `𝔼₀` in the paper's coordinates, for `p = (τ, r, θ)`. -/
noncomputable def paperPt (p : ℝ × ℝ × ℝ) : E0 := (p.1, (p.2.1 : ℂ) * cexp (p.2.2 * I))

variable {M : Type} [TopologicalSpace M] [ChartedSpace E0Y M] [HasGroupoid M e0Groupoid]

variable (M) in
/-- **A circle around the axis in a chart of `M`**: the chart `chartAt E0Y x`, a height `τ` and a
radius `r > 0` such that the whole circle `{(τ, r e^{iθ})}` lies in the chart's target. -/
structure BTZCircle where
  /-- The centre of the chart. -/
  x : M
  /-- The height of the circle. -/
  τ : ℝ
  /-- The radius of the circle. -/
  r : ℝ
  r_pos : 0 < r
  mem : ∀ θ : ℝ, E0.paperInY (paperPt (τ, r, θ)) ∈ (chartAt E0Y x).target

theorem paperPt_snd_ne_zero {r : ℝ} (hr : r ≠ 0) (τ θ : ℝ) : (paperPt (τ, r, θ)).2 ≠ 0 :=
  mul_ne_zero (Complex.ofReal_ne_zero.2 hr) (Complex.exp_ne_zero _)

theorem continuous_paperPt : Continuous paperPt := by
  unfold paperPt; fun_prop

theorem continuous_paperInY : Continuous (E0.paperInY : E0 → E0Y) := by
  have : (E0.paperInY : E0 → E0Y) = fun w => Sum.inr (E0.toPaper.symm w) :=
    funext E0.paperInY_apply
  rw [this]; exact continuous_inr.comp E0.toPaper.symm.continuous

theorem paperOfY_paperInY (w : E0) : E0.paperOfY (E0.paperInY w) = w := by
  rw [E0.paperInY_apply, E0.paperOfY_inr, Homeomorph.apply_symm_apply]

/-- A point of a chart's target off the axis is regular. -/
theorem mem_reg_of_mem {x : M} {w : E0} (hw : E0.paperInY w ∈ (chartAt E0Y x).target)
    (hw0 : w.2 ≠ 0) : (chartAt E0Y x).symm (E0.paperInY w) ∈ E0LM.e0RegM M := by
  have hs := (chartAt E0Y x).map_target hw
  rw [E0LM.mem_e0RegM_iff hs, (chartAt E0Y x).right_inv hw, E0.paperInY_apply,
    E0.inr_mem_e0Reg_iff_toPaper, Homeomorph.apply_symm_apply]
  exact hw0

namespace BTZCircle

theorem mem_reg (C : BTZCircle M) (θ : ℝ) :
    (chartAt E0Y C.x).symm (E0.paperInY (paperPt (C.τ, C.r, θ))) ∈ E0LM.e0RegM M :=
  mem_reg_of_mem (C.mem θ) (paperPt_snd_ne_zero C.r_pos.ne' C.τ θ)

/-- The point of angle `θ` of the circle, in `Reg M`. -/
noncomputable def pt (C : BTZCircle M) (θ : ℝ) : E0LM.e0RegM M :=
  ⟨(chartAt E0Y C.x).symm (E0.paperInY (paperPt (C.τ, C.r, θ))), C.mem_reg θ⟩

theorem continuous_pt (C : BTZCircle M) : Continuous C.pt := by
  refine Continuous.subtype_mk ?_ _
  refine (chartAt E0Y C.x).continuousOn_symm.comp_continuous ?_ C.mem
  exact continuous_paperInY.comp (continuous_paperPt.comp (by fun_prop))

theorem paperPt_add_two_pi (τ r θ : ℝ) : paperPt (τ, r, θ + 2 * π) = paperPt (τ, r, θ) := by
  simp only [paperPt]
  congr 2
  push_cast
  rw [add_mul, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

theorem pt_two_pi (C : BTZCircle M) : C.pt (2 * π * 1) = C.pt 0 := by
  have h := paperPt_add_two_pi C.τ C.r 0
  rw [zero_add] at h
  refine Subtype.ext ?_
  simp only [pt, mul_one]
  rw [h]

end BTZCircle

theorem paperPt_snd_ne_zero' {p : ℝ × ℝ × ℝ} (hp : p.2.1 ≠ 0) : (paperPt p).2 ≠ 0 :=
  mul_ne_zero (Complex.ofReal_ne_zero.2 hp) (Complex.exp_ne_zero _)

theorem paperPt_add_int_mul (τ r θ : ℝ) (n : ℤ) :
    paperPt (τ, r, θ + n * (2 * π)) = paperPt (τ, r, θ) := by
  simp only [paperPt]
  congr 2
  push_cast
  rw [show ((θ : ℂ) + n * (2 * π)) * I = θ * I + n * (2 * π * I) by ring, Complex.exp_add,
    Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem rad_paperPt {p : ℝ × ℝ × ℝ} (hp : 0 ≤ p.2.1) : E0.rad (paperPt p) = p.2.1 := by
  simp only [E0.rad, paperPt, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hp]

/-- The sector angle of `(τ', r' e^{iθ'})` from `(τ, r e^{iθ})` is `arg (r e^{iθ}) + (θ' − θ)` for
`|θ' − θ| < π`. -/
theorem angle_paperPt {p p' : ℝ × ℝ × ℝ} (hr : 0 < p.2.1) (hr' : 0 < p'.2.1)
    (h : p'.2.2 - p.2.2 ∈ Ioo (-π) π) :
    E0.angle (paperPt p) (paperPt p') = arg (paperPt p).2 + (p'.2.2 - p.2.2) := by
  simp only [E0.angle]
  congr 1
  have hdiv : (paperPt p').2 / (paperPt p).2 =
      ((p'.2.1 / p.2.1 : ℝ) : ℂ) * cexp ((p'.2.2 - p.2.2 : ℝ) * I) := by
    simp only [paperPt]
    have hr0 : (p.2.1 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr.ne'
    push_cast
    rw [sub_mul, Complex.exp_sub]
    field_simp
  rw [hdiv, Complex.arg_real_mul _ (div_pos hr' hr), Complex.arg_exp_mul_I, toIocMod_eq_self]
  exact ⟨h.1, by linarith [h.2]⟩

omit [HasGroupoid M e0Groupoid] in
/-- **The tube around a circle**: a whole neighbourhood `{dist ((τ', r'), (τ, r)) < ε} × ℝ` of the
circle's parameters lies in the chart (`ε < r`). -/
theorem BTZCircle.exists_tube (C : BTZCircle M) : ∃ ε : ℝ, 0 < ε ∧ ε < C.r ∧
    ∀ p : ℝ × ℝ × ℝ, dist (p.1, p.2.1) (C.τ, C.r) < ε →
      E0.paperInY (paperPt p) ∈ (chartAt E0Y C.x).target := by
  set e := chartAt E0Y C.x
  let Φ : (ℝ × ℝ) × ℝ → E0Y := fun q => E0.paperInY (paperPt (q.1.1, q.1.2, q.2))
  have hΦ : Continuous Φ := continuous_paperInY.comp (continuous_paperPt.comp (by fun_prop))
  have hn : IsOpen (Φ ⁻¹' e.target) := e.open_target.preimage hΦ
  have hsub : ({(C.τ, C.r)} : Set (ℝ × ℝ)) ×ˢ Icc 0 (2 * π) ⊆ Φ ⁻¹' e.target := by
    rintro ⟨q, θ⟩ ⟨hq, -⟩
    rw [Set.mem_singleton_iff] at hq
    subst hq
    exact C.mem θ
  obtain ⟨u, v, hu, -, hsu, htv, huv⟩ :=
    generalized_tube_lemma isCompact_singleton isCompact_Icc hn hsub
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hu (C.τ, C.r) (hsu rfl)
  refine ⟨min δ (C.r / 2), lt_min hδ (half_pos C.r_pos),
    lt_of_le_of_lt (min_le_right _ _) (half_lt_self C.r_pos), fun p hp => ?_⟩
  have hpu : (p.1, p.2.1) ∈ u := hball (lt_of_lt_of_le hp (min_le_left _ _))
  set θ' := toIcoMod Real.two_pi_pos 0 p.2.2
  have hθ' : θ' ∈ Icc 0 (2 * π) := by
    have := toIcoMod_mem_Ico Real.two_pi_pos 0 p.2.2
    rw [zero_add] at this
    exact Ico_subset_Icc_self this
  have hmem : Φ ((p.1, p.2.1), θ') ∈ e.target := huv ⟨hpu, htv hθ'⟩
  have hp' : paperPt p = paperPt (p.1, p.2.1, θ') := by
    have h := paperPt_add_int_mul p.1 p.2.1 θ' (toIcoDiv Real.two_pi_pos 0 p.2.2)
    have h2 := toIcoMod_add_toIcoDiv_zsmul Real.two_pi_pos 0 p.2.2
    rw [zsmul_eq_mul] at h2
    rw [h2] at h
    rw [← h]
  rw [hp']
  exact hmem

/-- **`btzPaperDev` is open on `{r > 0}`**: there `btzPaperNull (τ, r, θ) = (2τ + rθ² − r, r, −rθ)`
has the continuous inverse `(A, B, C) ↦ ((A − C²/B + B)/2, B, −C/B)`. -/
theorem isOpen_image_btzPaperNull {V : Set (ℝ × ℝ × ℝ)} (hV : IsOpen V)
    (hpos : ∀ p ∈ V, 0 < p.2.1) : IsOpen (btzPaperNull '' V) := by
  let ψ : ℝ × ℝ × ℝ → ℝ × ℝ × ℝ := fun q =>
    ((q.1 - q.2.2 ^ 2 / q.2.1 + q.2.1) / 2, q.2.1, -q.2.2 / q.2.1)
  have hψN : ∀ p : ℝ × ℝ × ℝ, 0 < p.2.1 → ψ (btzPaperNull p) = p := by
    rintro ⟨τ, r, θ⟩ hr
    have : r ≠ 0 := hr.ne'
    simp only [ψ, btzPaperNull]
    refine Prod.ext ?_ (Prod.ext rfl ?_)
    · simp only; field_simp; ring
    · simp only; field_simp
  have hNψ : ∀ q : ℝ × ℝ × ℝ, 0 < q.2.1 → btzPaperNull (ψ q) = q := by
    rintro ⟨A, B, Cc⟩ hB
    have : B ≠ 0 := hB.ne'
    simp only [ψ, btzPaperNull]
    refine Prod.ext ?_ (Prod.ext rfl ?_)
    · simp only; field_simp; ring
    · simp only; field_simp
  have heq : btzPaperNull '' V = {q | 0 < q.2.1} ∩ ψ ⁻¹' V := by
    ext q
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨hpos p hp, by simp only [mem_preimage]; rw [hψN p (hpos p hp)]; exact hp⟩
    · rintro ⟨hq, hψ⟩
      exact ⟨ψ q, hψ, hNψ q hq⟩
  have hcont : ContinuousOn ψ {q | 0 < q.2.1} := by
    intro q hq
    have h0 : q.2.1 ≠ 0 := ne_of_gt hq
    apply ContinuousAt.continuousWithinAt
    fun_prop (disch := assumption)
  rw [heq]
  exact hcont.isOpen_inter_preimage (isOpen_lt continuous_const (by fun_prop)) hV

theorem isOpenMap_btzPaperDev_restrict {U : Set (ℝ × ℝ × ℝ)} (hU : IsOpen U)
    (hpos : ∀ p ∈ U, 0 < p.2.1) : IsOpenMap (fun p : U => btzPaperDev p.1) := by
  intro O hO
  have hO' : IsOpen ((↑) '' O : Set (ℝ × ℝ × ℝ)) := hU.isOpenMap_subtype_val O hO
  have himg : (fun p : U => btzPaperDev p.1) '' O =
      nullToMinkHomeomorph '' (btzPaperNull '' ((↑) '' O)) := by
    simp only [Set.image_image, coe_nullToMinkHomeomorph, btzPaperDev_eq_nullToMink]
  rw [himg]
  exact nullToMinkHomeomorph.isOpenMap _
    (isOpen_image_btzPaperNull hO' (by rintro _ ⟨p, -, rfl⟩; exact hpos _ p.2))

/-- Two isometries of `𝐌³` agreeing on a non-empty open set are equal. -/
theorem isom_eq_of_eqOn {g g' : isom 2} {U : Set (Causal.Minkowski 2)} (hU : IsOpen U)
    (hne : U.Nonempty) (h : ∀ q ∈ U, g • q = g' • q) : g = g' := by
  have hA : (g : Causal.Minkowski 2 ≃ᵃ[ℝ] Causal.Minkowski 2).toAffineMap =
      (g' : Causal.Minkowski 2 ≃ᵃ[ℝ] Causal.Minkowski 2).toAffineMap :=
    AffineMap.ext_on (hU.affineSpan_eq_top hne) fun q hq => by
      have := h q hq
      rw [isom_smul_def, isom_smul_def] at this
      exact this
  exact Subtype.ext (AffineEquiv.toAffineMap_injective hA)

/-- `gShift 0 c` (the angle shift by `c` read in `𝐌³`) is the inverse of the model's `btzHol 0 c`. -/
theorem gShift_zero_inv (c : ℝ) : (BTZIsom.gShift 0 c)⁻¹ = btzHol 0 c := by
  rw [inv_eq_iff_mul_eq_one]
  refine isom_eq_of_eqOn isOpen_univ univ_nonempty fun q _ => ?_
  obtain ⟨y, rfl⟩ := nullToMinkHomeomorph.surjective q
  rw [coe_nullToMinkHomeomorph, one_smul, mul_smul, BTZIsom.gShift, mul_smul]
  have h1 := btzHol_zpow_smul 0 c 1 y
  rw [zpow_one, parabAff_zpow] at h1
  rw [h1]
  have h2 := btzHol_zpow_smul 0 (-c) 1 (0 + (parab ((1 : ℤ) * c)) (y - 0))
  rw [zpow_one, parabAff_zpow] at h2
  rw [h2]
  rw [isom_smul_def]
  change AffineEquiv.constVAdd ℝ (Causal.Minkowski 2) (nullToMink ((2 * 0 : ℝ), (0 : ℝ), (0 : ℝ)))
    (nullToMink _) = _
  rw [AffineEquiv.constVAdd_apply, vadd_eq_add,
    show (((2 * 0 : ℝ), (0 : ℝ), (0 : ℝ)) : ℝ × ℝ × ℝ) = 0 by simp, map_zero, zero_add]
  congr 1
  simp only [zero_add, sub_zero, Int.cast_one, one_mul]
  rw [show (-c : ℝ) = -c from rfl, parab_neg_parab]

variable [T2Space M] [ConnectedSpace M]

/-- The point of angle `θ` of the circle, in the flat spacetime `Reg M`. -/
noncomputable def BTZCircle.ptF (C : BTZCircle M) (θ : ℝ) : e0RegMFlat M := C.pt θ

theorem BTZCircle.continuous_ptF (C : BTZCircle M) : Continuous C.ptF := C.continuous_pt

/-- **The loop once around the axis**, `t ↦ (τ, r e^{2πit})`, in `Reg M`. -/
noncomputable def BTZCircle.loop (C : BTZCircle M) : Path (C.ptF 0) (C.ptF 0) where
  toFun t := C.ptF (2 * π * t)
  continuous_toFun := C.continuous_ptF.comp (continuous_const.mul continuous_subtype_val)
  source' := by simp
  target' := by
    show C.pt (2 * π * ((1 : unitInterval) : ℝ)) = C.pt 0
    rw [Set.Icc.coe_one]
    exact C.pt_two_pi

/-- **A BTZ loop**: the deck transformation of `Reg M̃ → Reg M` of the class of `σ · C · σ⁻¹`,
`C` a circle around the BTZ point `x` in the chart at `x` (centred at `x`, the closed disc in the
chart's target), `σ` any path from the base point. -/
def IsBTZLoop (x₀ : e0RegMFlat M)
    (γ : Causal.Deck (Causal.UniversalCover.proj (e0RegMFlat M) x₀)) : Prop :=
  ∃ (C : BTZCircle M) (σ : Path x₀ (C.ptF 0)), C.x ∉ E0LM.e0RegM M ∧
    E0.paperOfY (chartAt E0Y C.x C.x) = (C.τ, 0) ∧
    (∀ r' ∈ Icc 0 C.r, ∀ θ : ℝ, E0.paperInY (paperPt (C.τ, r', θ)) ∈ (chartAt E0Y C.x).target) ∧
    γ = Causal.UniversalCover.deckHom
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (σ.trans (C.loop.trans σ.symm))))

/-- **The holonomy once around a circle of a chart** (the computation behind l.1150): for every
developing pair `(𝒟, ρ)` of `Reg M`, every circle `C` around the axis of a chart and every path
`σ` from the base point, the holonomy of `σ · C · σ⁻¹` is conjugate in `Isom(𝐌³)` to the model's
parabolic `btzHol 0 (2π)`. -/
theorem holonomy_circleLoop {x₀ : e0RegMFlat M}
    {D : Causal.UniversalCover (e0RegMFlat M) x₀ → Causal.Minkowski 2}
    {ρ : Causal.Deck (Causal.UniversalCover.proj (e0RegMFlat M) x₀) →* isom 2}
    (hpair : IsDevelopingPair x₀ D ρ) (C : BTZCircle M) (σ : Path x₀ (C.ptF 0)) :
    ∃ g : isom 2, ρ (Causal.UniversalCover.deckHom (FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (σ.trans (C.loop.trans σ.symm))))) =
        g * btzHol 0 (2 * π) * g⁻¹ := by
  obtain ⟨ε, hε0, hεr, hε⟩ := C.exists_tube
  set e := chartAt E0Y C.x with he_def
  set B : Set (ℝ × ℝ × ℝ) := (fun p : ℝ × ℝ × ℝ => (p.1, p.2.1)) ⁻¹' Metric.ball (C.τ, C.r) ε
    with hB
  have hBo : IsOpen B := Metric.isOpen_ball.preimage (by fun_prop)
  have hBc : Convex ℝ B := by
    have := (convex_ball (C.τ, C.r) ε).linear_preimage
      ((LinearMap.fst ℝ ℝ (ℝ × ℝ)).prod ((LinearMap.fst ℝ ℝ ℝ).comp (LinearMap.snd ℝ ℝ (ℝ × ℝ))))
    exact this
  have hBpos : ∀ p ∈ B, 0 < p.2.1 := by
    intro p hp
    have h1 : dist p.2.1 C.r < ε :=
      lt_of_le_of_lt (le_max_right _ _) (show dist (p.1, p.2.1) (C.τ, C.r) < ε from hp)
    rw [Real.dist_eq] at h1
    have := (abs_lt.1 h1).1
    linarith
  have hBt : ∀ p ∈ B, E0.paperInY (paperPt p) ∈ e.target := fun p hp => hε p hp
  have hp₀ : ((C.τ, C.r, (0 : ℝ)) : ℝ × ℝ × ℝ) ∈ B := by
    show dist (C.τ, C.r) (C.τ, C.r) < ε
    rw [dist_self]; exact hε0
  have hshift : ∀ p ∈ B, ((p.1, p.2.1, p.2.2 + 2 * π) : ℝ × ℝ × ℝ) ∈ B := fun p hp => hp
  haveI : Nonempty B := ⟨⟨_, hp₀⟩⟩
  haveI : ContractibleSpace B := hBc.contractibleSpace ⟨_, hp₀⟩
  haveI : LocPathConnectedSpace B := hBo.locPathConnectedSpace
  haveI : PreconnectedSpace B := Subtype.preconnectedSpace hBc.isPreconnected
  -- the parametrisation of the tube in `Reg M`
  let Fv : B → E0LM.e0RegM M := fun p =>
    ⟨e.symm (E0.paperInY (paperPt p.1)),
      mem_reg_of_mem (hBt p.1 p.2) (paperPt_snd_ne_zero' (hBpos p.1 p.2).ne')⟩
  have hFv : Continuous Fv := by
    refine Continuous.subtype_mk ?_ _
    exact e.continuousOn_symm.comp_continuous
      (continuous_paperInY.comp (continuous_paperPt.comp continuous_subtype_val))
      fun p => hBt p.1 p.2
  let F : C(B, e0RegMFlat M) := ⟨Fv, hFv⟩
  have hcov := Causal.Flat.isCoveringMap_flatCover_proj 2 (e0RegMFlat M) x₀
  let p₀ : B := ⟨_, hp₀⟩
  obtain ⟨Ft, ⟨hFt0, hFtp⟩, -⟩ := hcov.existsUnique_continuousMap_lifts F p₀
    (⟨C.ptF 0, Path.Homotopic.Quotient.mk σ⟩ : Causal.UniversalCover (e0RegMFlat M) x₀) rfl
  have hprojFt : ∀ p : B, Causal.UniversalCover.proj (e0RegMFlat M) x₀ (Ft p) = F p :=
    fun p => congrFun hFtp p
  have hbase : ∀ p : B, regCoverBase (Ft p) = e.symm (E0.paperInY (paperPt p.1)) := by
    intro p
    show (show E0LM.e0RegM M from Causal.UniversalCover.proj (e0RegMFlat M) x₀ (Ft p)).1 = _
    rw [hprojFt p]
    rfl
  have hchart : ∀ p : B, e (regCoverBase (Ft p)) = E0.paperInY (paperPt p.1) := fun p => by
    rw [hbase, e.right_inv (hBt p.1 p.2)]
  -- the local form of the developing map along the tube
  have hloc : ∀ p : B, ∃ g : isom 2, ∀ᶠ p' in 𝓝 p, D (Ft p') = g • btzPaperDev p'.1 := by
    intro p
    set y₀ := paperPt p.1 with hy₀_def
    have hy₀ : y₀.2 ≠ 0 := paperPt_snd_ne_zero' (hBpos p.1 p.2).ne'
    obtain ⟨g, hg⟩ := dev_eventually_chartMap_sector hpair C.x hy₀ (Ft p)
      (by rw [hbase]; exact e.map_target (hBt p.1 p.2))
      (by rw [hchart, E0.paperInY_apply]; exact ⟨_, rfl⟩)
      (by rw [hchart, paperOfY_paperInY]; exact E0.mem_sector_self hy₀)
    have h1 := (Ft.continuous.tendsto p).eventually hg
    have h2 : ∀ᶠ p' in 𝓝 p, p'.1.2.2 - p.1.2.2 ∈ Ioo (-π) π := by
      have hc : Continuous fun p' : B => p'.1.2.2 - p.1.2.2 := by fun_prop
      have hmem : (fun p' : B => p'.1.2.2 - p.1.2.2) p ∈ Ioo (-π) π := by
        simp only [sub_self]; exact ⟨neg_lt_zero.2 Real.pi_pos, Real.pi_pos⟩
      exact hc.continuousAt.eventually (isOpen_Ioo.mem_nhds hmem)
    refine ⟨g * BTZIsom.gShift 0 (arg y₀.2 - p.1.2.2), ?_⟩
    filter_upwards [h1, h2] with p' h1 h2
    rw [h1, hchart, paperOfY_paperInY, E0.chartMap_eq, mul_smul,
      ← BTZIsom.btzPaperDev_shift_angle]
    congr 2
    refine Prod.ext (by simp [paperPt]) (Prod.ext ?_ ?_)
    · exact rad_paperPt (hBpos p'.1 p'.2).le
    · show E0.angle y₀ (paperPt p'.1) = _
      rw [hy₀_def, angle_paperPt (hBpos p.1 p.2) (hBpos p'.1 p'.2) h2]
      ring
  -- one isometry along the whole tube
  have hopen := isOpenMap_btzPaperDev_restrict hBo hBpos
  obtain ⟨g₀, hg₀⟩ := exists_isom_eq_of_locally (X := B) (D := fun p => btzPaperDev p.1)
    (F := fun p => D (Ft p)) hopen fun p => by
      obtain ⟨g, hg⟩ := hloc p
      exact ⟨g⁻¹, hg.mono fun p' h => by rw [h, inv_smul_smul]⟩
  have hglob : ∀ p : B, D (Ft p) = g₀⁻¹ • btzPaperDev p.1 := fun p => by
    rw [hg₀ p, inv_smul_smul]
  -- the deck transformation of the loop shifts the angle by `2π`
  set γ := Causal.UniversalCover.deckHom (FundamentalGroup.fromPath
    (Path.Homotopic.Quotient.mk (σ.trans (C.loop.trans σ.symm)))) with hγ
  let sh : B → B := fun p => ⟨(p.1.1, p.1.2.1, p.1.2.2 + 2 * π), hshift p.1 p.2⟩
  have hsh : Continuous sh := Continuous.subtype_mk (by fun_prop) _
  let seg : unitInterval → B := fun t => ⟨(C.τ, C.r, 2 * π * t), hp₀⟩
  have hseg : Continuous seg := Continuous.subtype_mk (by fun_prop) _
  have hlift : (fun t => Ft (seg t)) =
      fun t => Causal.UniversalCover.liftFrom (Path.Homotopic.Quotient.mk σ) C.loop t := by
    refine hcov.eq_of_comp_eq (Ft.continuous.comp hseg)
      (Causal.UniversalCover.liftFrom (Path.Homotopic.Quotient.mk σ) C.loop).continuous ?_ 0 ?_
    · funext t
      simp only [Function.comp]
      rw [hprojFt]
      exact (Causal.UniversalCover.proj_liftFrom (Path.Homotopic.Quotient.mk σ) C.loop t).symm
    · have hs0 : seg 0 = p₀ := Subtype.ext (by simp [seg, p₀])
      show Ft (seg 0) = _
      rw [Path.source, hs0, hFt0]
  have h1 : Ft (sh p₀) = ⟨C.ptF 0, (Path.Homotopic.Quotient.mk σ).trans
      (Path.Homotopic.Quotient.mk C.loop)⟩ := by
    have := congrFun hlift 1
    rw [Path.target] at this
    have hs : seg 1 = sh p₀ := Subtype.ext (by simp [seg, sh, p₀])
    rw [← hs]
    exact this
  have h2 : γ.1 (Ft (sh p₀)) = Ft p₀ := by
    rw [h1, hFt0, hγ, Causal.UniversalCover.deckHom_apply]
    simp only [Causal.UniversalCover.leftMul]
    congr 1
    have hX : Path.Homotopic.Quotient.mk (σ.trans (C.loop.trans σ.symm)) =
        (Path.Homotopic.Quotient.mk σ).trans ((Path.Homotopic.Quotient.mk C.loop).trans
          (Path.Homotopic.Quotient.mk σ).symm) := by
      rw [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_trans,
        Path.Homotopic.Quotient.mk_symm]
    have hXA : (Path.Homotopic.Quotient.mk (σ.trans (C.loop.trans σ.symm))).trans
        (Path.Homotopic.Quotient.mk σ) =
        (Path.Homotopic.Quotient.mk σ).trans (Path.Homotopic.Quotient.mk C.loop) := by
      rw [hX, Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.trans_assoc,
        Path.Homotopic.Quotient.symm_trans, Path.Homotopic.Quotient.trans_refl]
    show (Path.Homotopic.Quotient.mk (σ.trans (C.loop.trans σ.symm))).symm.trans
      ((Path.Homotopic.Quotient.mk σ).trans (Path.Homotopic.Quotient.mk C.loop)) =
        Path.Homotopic.Quotient.mk σ
    rw [← hXA, ← Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.symm_trans,
      Path.Homotopic.Quotient.refl_trans]
  have h3 : (fun p => γ.1 (Ft (sh p))) = fun p => Ft p := by
    refine hcov.eq_of_comp_eq (γ.1.continuous.comp (Ft.continuous.comp hsh)) Ft.continuous ?_ p₀ h2
    funext p
    simp only [Function.comp]
    rw [show Causal.UniversalCover.proj (e0RegMFlat M) x₀ (γ.1 (Ft (sh p))) =
      Causal.UniversalCover.proj (e0RegMFlat M) x₀ (Ft (sh p)) from congrFun γ.2 (Ft (sh p)),
      hprojFt, hprojFt]
    show Fv (sh p) = Fv p
    refine Subtype.ext ?_
    show e.symm (E0.paperInY (paperPt (p.1.1, p.1.2.1, p.1.2.2 + 2 * π))) =
      e.symm (E0.paperInY (paperPt p.1))
    rw [BTZCircle.paperPt_add_two_pi]
  -- conclusion
  have hfinal : ∀ q ∈ Set.range (fun p : B => btzPaperDev p.1),
      (ρ γ * g₀⁻¹ * BTZIsom.gShift 0 (2 * π)) • q = g₀⁻¹ • q := by
    rintro _ ⟨p, rfl⟩
    have e1 : D (Ft p) = ρ γ • D (Ft (sh p)) := by
      rw [← hpair.equiv]
      exact (congrFun h3 p).symm ▸ rfl
    rw [hglob, hglob] at e1
    have e2 : btzPaperDev (sh p).1 = BTZIsom.gShift 0 (2 * π) • btzPaperDev p.1 := by
      rw [← BTZIsom.btzPaperDev_shift_angle, add_zero]
    rw [e2] at e1
    simp only
    rw [mul_smul, mul_smul, ← e1]
  have heq := isom_eq_of_eqOn hopen.isOpen_range (Set.range_nonempty _) hfinal
  refine ⟨g₀⁻¹, ?_⟩
  rw [← gShift_zero_inv]
  calc ρ γ = (ρ γ * g₀⁻¹ * BTZIsom.gShift 0 (2 * π)) * (BTZIsom.gShift 0 (2 * π))⁻¹ * g₀ := by
        group
    _ = g₀⁻¹ * (BTZIsom.gShift 0 (2 * π))⁻¹ * g₀⁻¹⁻¹ := by rw [heq, inv_inv]

/-- **The holonomy around a BTZ line is conjugate to `btzHol 0 (2π)`.** -/
theorem holonomy_btzLoop {x₀ : e0RegMFlat M}
    {D : Causal.UniversalCover (e0RegMFlat M) x₀ → Causal.Minkowski 2}
    {ρ : Causal.Deck (Causal.UniversalCover.proj (e0RegMFlat M) x₀) →* isom 2}
    (hpair : IsDevelopingPair x₀ D ρ)
    {γ : Causal.Deck (Causal.UniversalCover.proj (e0RegMFlat M) x₀)} (hγ : IsBTZLoop x₀ γ) :
    ∃ g : isom 2, ρ γ = g * btzHol 0 (2 * π) * g⁻¹ := by
  obtain ⟨C, σ, -, -, -, rfl⟩ := hγ
  exact holonomy_circleLoop hpair C σ

/-- **The holonomy around a BTZ line is parabolic** (l.1150). -/
theorem isParabolic_holonomy_btzLoop {x₀ : e0RegMFlat M}
    {D : Causal.UniversalCover (e0RegMFlat M) x₀ → Causal.Minkowski 2}
    {ρ : Causal.Deck (Causal.UniversalCover.proj (e0RegMFlat M) x₀) →* isom 2}
    (hpair : IsDevelopingPair x₀ D ρ)
    {γ : Causal.Deck (Causal.UniversalCover.proj (e0RegMFlat M) x₀)} (hγ : IsBTZLoop x₀ γ) :
    IsParabolic (linOf (ρ γ)) := by
  obtain ⟨g, hg⟩ := holonomy_btzLoop hpair hγ
  have h := btzHol_isParabolic 0 (by positivity : (2 * π : ℝ) ≠ 0)
  rw [← linOf_eq_linearPart] at h
  rw [hg, linOf_mul, linOf_mul, linOf_inv]
  exact h.conj (linOf_mem g)

/-- **The translation part of the holonomy around a BTZ line is tangent** (l.1150, with no
appeal to Barbot § 7.3). -/
theorem isTangent_holonomy_btzLoop {x₀ : e0RegMFlat M}
    {D : Causal.UniversalCover (e0RegMFlat M) x₀ → Causal.Minkowski 2}
    {ρ : Causal.Deck (Causal.UniversalCover.proj (e0RegMFlat M) x₀) →* isom 2}
    (hpair : IsDevelopingPair x₀ D ρ)
    {γ : Causal.Deck (Causal.UniversalCover.proj (e0RegMFlat M) x₀)} (hγ : IsBTZLoop x₀ γ) :
    IsTangentTranslation (ρ γ) := by
  obtain ⟨g, hg⟩ := holonomy_btzLoop hpair hγ
  rw [hg]
  exact (isTangentTranslation_conj g _).2 (isTangentTranslation_btzHol _)

omit [T2Space M] [ConnectedSpace M] in
/-- **Every BTZ point has BTZ loops around it**: a circle data centred at `x`, with its closed
disc in the chart. -/
theorem exists_btzCircle (x : M) (hx : x ∉ E0LM.e0RegM M) :
    ∃ C : BTZCircle M, C.x = x ∧ E0.paperOfY (chartAt E0Y C.x C.x) = (C.τ, 0) ∧
      ∀ r' ∈ Icc 0 C.r, ∀ θ : ℝ, E0.paperInY (paperPt (C.τ, r', θ)) ∈ (chartAt E0Y C.x).target := by
  set e := chartAt E0Y x with he
  have hxs := mem_chart_source E0Y x
  have hreg : e x ∉ e0Reg := fun h => hx ((E0LM.mem_e0RegM_iff hxs).2 h)
  obtain ⟨u, hu⟩ : ∃ u, e x = Sum.inr u := by
    rcases h : e x with m | u
    · exact absurd (h ▸ inl_mem_e0Reg m) hreg
    · exact ⟨u, rfl⟩
  have hax : (E0.toPaper u).2 = 0 := by
    by_contra h
    exact hreg (hu ▸ E0.inr_mem_e0Reg_iff_toPaper.2 h)
  set τ := (E0.toPaper u).1
  have hpt : E0.paperInY (τ, 0) = e x := by
    rw [E0.paperInY_apply, hu]
    congr 1
    rw [Homeomorph.symm_apply_eq]
    exact Prod.ext rfl hax.symm
  have hW : IsOpen (E0.paperInY ⁻¹' e.target) := e.open_target.preimage continuous_paperInY
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hW (τ, 0)
    (by show E0.paperInY (τ, 0) ∈ e.target; rw [hpt]; exact e.map_source hxs)
  have hdisc : ∀ r' ∈ Icc 0 (δ / 2), ∀ θ : ℝ, E0.paperInY (paperPt (τ, r', θ)) ∈ e.target := by
    intro r' hr' θ
    refine hball ?_
    rw [Metric.mem_ball, Prod.dist_eq]
    show max (dist τ τ) (dist ((r' : ℂ) * cexp (θ * I)) 0) < δ
    rw [dist_self, dist_zero_right, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr'.1]
    exact max_lt hδ (lt_of_le_of_lt hr'.2 (half_lt_self hδ))
  refine ⟨⟨x, τ, δ / 2, half_pos hδ, fun θ => hdisc _ ⟨(half_pos hδ).le, le_rfl⟩ θ⟩, rfl, ?_, hdisc⟩
  show E0.paperOfY (e x) = (τ, 0)
  rw [← hpt, paperOfY_paperInY]

/-- Around every BTZ point there is a BTZ loop (for any base point of `Reg M`). -/
theorem exists_isBTZLoop (x₀ : e0RegMFlat M) (x : M) (hx : x ∉ E0LM.e0RegM M) :
    ∃ γ, IsBTZLoop x₀ γ ∧ ∃ C : BTZCircle M, C.x = x := by
  obtain ⟨C, hCx, hC0, hCd⟩ := exists_btzCircle x hx
  haveI : LocPathConnectedSpace (e0RegMFlat M) := Causal.Flat.locPathConnectedSpace_of_flat 2 _
  haveI : PathConnectedSpace (e0RegMFlat M) := pathConnectedSpace_iff_connectedSpace.2 inferInstance
  let σ : Path x₀ (C.ptF 0) := PathConnectedSpace.somePath x₀ (C.ptF 0)
  exact ⟨_, ⟨C, σ, hCx ▸ hx, hC0, hCd, rfl⟩, C, hCx⟩

end Holonomy

/-! ## `btzprop:holonomy_globally_hyperbolic_cauchy_compact`, the marked form -/

section Marked

variable {M : Type} [TopologicalSpace M] [T2Space M] [ConnectedSpace M] [SecondCountableTopology M]
  [ChartedSpace E0Y M] [HasGroupoid M e0Groupoid]

/-- **Barbot's input** (l.1148): the linear part of the holonomy of `Reg M` is faithful and
discrete. Proved from `GX.BTZAdm.linearPart_comp_faithful_discrete` (`AdmissibleLinear`, lean-causal's
Barbot, DEC-34), fed by the strict `GX.e0RegM_holonomy` and `GX.E0AbsMax.cor_abs_max_C1`. -/
theorem e0RegM_linearPart_faithful_discrete (hGH : (E0CBG.CE M).GloballyHyperbolic)
    (hCC : ∃ S : Set M, E0Surgery.IsE0C1SpacelikeCauchy M S) (hmax : E0Spear.IsE0CauchyMaximal M)
    (x₀ : e0RegMFlat M)
    (hnm : ¬IsMetabelianGroup (Causal.Deck (Causal.UniversalCover.proj (e0RegMFlat M) x₀)))
    (D : Causal.UniversalCover (e0RegMFlat M) x₀ → Causal.Minkowski 2)
    (ρ : Causal.Deck (Causal.UniversalCover.proj (e0RegMFlat M) x₀) →* isom 2)
    (hpair : IsDevelopingPair x₀ D ρ) :
    Function.Injective (linearPart.comp ρ) ∧ DiscreteTopology (linearPart.comp ρ).range := by
  -- `Reg M` is GH and Cauchy-complete (`E0AbsMax.cor_abs_max_C1`, DEC-107/117)
  obtain ⟨hGH', hCC', -⟩ := E0AbsMax.cor_abs_max_C1 hGH hCC hmax
  -- the strict holonomy package: `ρ` faithful, `ρ(π₁)` torsion-free with a loxodromic element
  obtain ⟨hlox, -, hρ, -, htf, -⟩ := e0RegM_holonomy M hGH' hCC' x₀ hnm D ρ hpair
  -- §8's data for `ρ(π₁)`
  obtain ⟨S, hS⟩ := Causal.Flat.exists_developsCC_of_isCauchyComplete' (e0RegMFlat M) hGH' hCC' hpair
  exact linearPart_comp_faithful_discrete (Causal.Flat.ccAction_of_developsCC hpair hS) hρ hlox
    (not_isMetabelianOn_range hρ hnm) htf

/-- **`btzprop:holonomy_globally_hyperbolic_cauchy_compact`, marked form, for `𝔼₀`**: for `M` a
globally hyperbolic, Cauchy-compact, Cauchy-maximal `𝔼₀`-manifold with `π₁(Reg M)` not
metabelian, every developing pair `(𝒟, ρ)` of `Reg M` and every marking `μ : Γ → π₁(Reg M)`
(injective, each `cⱼ` a loop around a BTZ line), `ρ ∘ μ` is admissible. -/
theorem btzprop_holonomy_e0 (hGH : (E0CBG.CE M).GloballyHyperbolic)
    (hCC : ∃ S : Set M, E0Surgery.IsE0C1SpacelikeCauchy M S) (hmax : E0Spear.IsE0CauchyMaximal M)
    (x₀ : e0RegMFlat M)
    (hnm : ¬IsMetabelianGroup (Causal.Deck (Causal.UniversalCover.proj (e0RegMFlat M) x₀)))
    (D : Causal.UniversalCover (e0RegMFlat M) x₀ → Causal.Minkowski 2)
    (ρ : Causal.Deck (Causal.UniversalCover.proj (e0RegMFlat M) x₀) →* isom 2)
    (hpair : IsDevelopingPair x₀ D ρ) {g s : ℕ}
    (μ : SurfaceGroup g s →* Causal.Deck (Causal.UniversalCover.proj (e0RegMFlat M) x₀))
    (hμ : Function.Injective μ) (hc : ∀ j, IsBTZLoop x₀ (μ (SurfaceGroup.c j))) :
    IsAdmissible (ρ.comp μ) := by
  obtain ⟨hinj, hdisc⟩ := e0RegM_linearPart_faithful_discrete hGH hCC hmax x₀ hnm D ρ hpair
  have hle : (linearPart.comp (ρ.comp μ)).range ≤ (linearPart.comp ρ).range := by
    rintro _ ⟨a, rfl⟩
    exact ⟨μ a, rfl⟩
  refine ⟨fun a b h => hμ (hinj h), ?_, fun j => isParabolic_holonomy_btzLoop hpair (hc j),
    fun j => isTangent_holonomy_btzLoop hpair (hc j)⟩
  haveI := hdisc
  exact DiscreteTopology.of_continuous_injective (f := Subgroup.inclusion hle)
    (Continuous.subtype_mk continuous_subtype_val _) (Subgroup.inclusion_injective hle)

end Marked


end BTZAdm

end GX
