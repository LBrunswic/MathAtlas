import Causal.Inextensible
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-!
# Cauchy surfaces and Cauchy time functions

**`def:cauchy_surface`** — `ETT.tex:999`. **`def:cauchy_time_function`** — `ETT.tex:1251`.
Both as the author ruled: a Cauchy surface is met exactly once by every **inextensible** causal
curve (DEC-14); "inextensible" is the strict-extension notion of `Causal.Inextensible`
(DEC-11, made precise by DEC-13); a time function is a strong morphism to the timelike line
(DEC-10, DEC-12).

DEC-14: a Cauchy surface (`def:cauchy_surface`) is met exactly once by every inextensible causal
curve; the literal "every causal curve" admits no Cauchy surface.

> A Cauchy surface in $M$ is a subset $S\subset M$ such that every causal curve of $M$ meets $S$
> exactly once.

> Let $M$ be a topological spacetime. A time function $T$ is a Cauchy time function if for every
> inextensible causal curve $c:\RR\rightarrow M$,
> $$-\lim_{-\infty} (T\circ c) = \lim_{+\infty}(T\circ c) = +\infty.$$

## Hypothesis checklist

| paper | here |
|---|---|
| `def:cauchy_surface`: every inextensible causal curve (DEC-14) | ✓ carried: `IsCauchySurface`, as the paper uses it at `ETT.tex:1875`, `2175`, `2226`; the sentence as printed ("every causal curve") admits no Cauchy surface (`not_isCauchySurfaceLiteral`), which is why DEC-14 was ruled |
| "meets `S` exactly once" | ✓ on the image: `c(I) ∩ S` is a single point, as the paper counts it (`ETT.tex:1878`, `#(c ∩ Σ)`) |
| `def:cauchy_time_function`: a time function | ✓ `IsTimeFunction`, a strong morphism to the timelike line (DEC-10, DEC-12) |
| — every inextensible `c : ℝ → M` | ✓ carried: `Inextensible ⊤ univ c` (DEC-11, DEC-13) |

## SCOPE (disclosed)

* **`def:cauchy_surface` read literally is unsatisfiable** (a finding): constant curves are causal
  curves (DEC-6), so a subset met exactly once by every causal curve contains every point, and
  is then met twice by any non-constant causal curve (`not_isCauchySurfaceLiteral`; on the
  timelike line, `timelikeLine_not_isCauchySurfaceLiteral`). The definition is the one the paper
  uses elsewhere and the author ruled (DEC-14): every *inextensible* causal curve. The printed one
  is kept as `IsCauchySurfaceLiteral` for the finding only.
* "Meets exactly once" is read on the image, and it is the only satisfiable reading: with DEC-6 a
  surjective inextensible curve of the timelike line can pause at a point of `S`, so counting
  parameters admits no Cauchy surface at all. It is how the paper counts at `ETT.tex:1878`
  (`#(c ∩ Σ)`); in a causal spacetime `c⁻¹(x)` is an interval, one dwell at one point.
* A Cauchy surface is defined for the open subset `W` seen as a spacetime (`IsCauchySurfaceOn`),
  as `ETT.tex:2175` needs (`S` is a Cauchy surface of `Int D(S)`); the Cauchy time function only
  for `M`, as a time function is.
* `Inextensible.reparam`: in a causally arc-connected causal spacetime with `J^±(p) ≠ {p}`, every
  inextensible curve is, after a strictly increasing reparametrisation, an inextensible curve
  over `ℝ`. This is what lets `def:cauchy_time_function` (curves over `ℝ`) speak of the curves of
  `def:cauchy_surface` (curves over intervals). Without those hypotheses an inextensible curve
  may have a closed end, and the two definitions do not see the same curves.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Filter

universe u

variable {M : Type u} [TopologicalSpace M]

namespace Causality

variable (C : Causality M)

/-- `def:cauchy_surface` (DEC-14): every inextensible causal curve of
the open set `W` meets `S` in exactly one point. -/
def IsCauchySurfaceOn (W : Opens M) (S : Set M) : Prop :=
  ∀ (I : Set ℝ) (c : ℝ → M), C.Inextensible W I c → ∃! x, x ∈ c '' I ∩ S

/-- `def:cauchy_surface` (DEC-14), for `M`. -/
def IsCauchySurface (S : Set M) : Prop := C.IsCauchySurfaceOn ⊤ S

/-- `def:cauchy_surface` as printed: every causal curve meets `S` exactly once. Kept for the
finding `not_isCauchySurfaceLiteral` only. -/
def IsCauchySurfaceLiteral (S : Set M) : Prop :=
  ∀ (I : Set ℝ) (c : ℝ → M), C.CausalCurveIn ⊤ I c → ∃! x, x ∈ c '' I ∩ S

/-- `def:cauchy_time_function`: a time function (DEC-10) tending to `-∞` and `+∞` at the ends of
every inextensible causal curve over `ℝ`. -/
def IsCauchyTimeFunction (T : M → ℝ) : Prop :=
  C.IsTimeFunction T ∧ ∀ c : ℝ → M, C.Inextensible ⊤ univ c →
    Tendsto (T ∘ c) atBot atBot ∧ Tendsto (T ∘ c) atTop atTop

variable {C}

/-- **Finding: `def:cauchy_surface` read literally admits no Cauchy surface** as soon as some
causal curve is not constant. Constant curves force `S = M`, and a non-constant curve then meets
`S` at two points. -/
theorem not_isCauchySurfaceLiteral {I : Set ℝ} {c : ℝ → M} (hc : C.CausalCurveIn ⊤ I c)
    {s t : ℝ} (hs : s ∈ I) (ht : t ∈ I) (hst : c s ≠ c t) (S : Set M) :
    ¬ C.IsCauchySurfaceLiteral S := by
  intro hS
  have hall : ∀ p : M, p ∈ S := by
    intro p
    have hconst : C.CausalCurveIn ⊤ (Icc 0 1) (fun _ => p) :=
      ⟨⟨0, by norm_num, by norm_num⟩, ordConnected_Icc, fun _ _ _ _ =>
        causalCurveOn_const (show p ∈ (⊤ : Opens M) from trivial)⟩
    obtain ⟨x, ⟨⟨_, _, rfl⟩, hx⟩, _⟩ := hS _ _ hconst
    exact hx
  obtain ⟨_, _, huniq⟩ := hS I c hc
  exact hst ((huniq (c s) ⟨⟨s, hs, rfl⟩, hall _⟩).trans (huniq (c t) ⟨⟨t, ht, rfl⟩, hall _⟩).symm)

/-- On the timelike line no subset is a Cauchy surface in the literal reading. -/
theorem _root_.Causal.timelikeLine_not_isCauchySurfaceLiteral (S : Set ℝ) :
    ¬ timelikeLine.IsCauchySurfaceLiteral S :=
  not_isCauchySurfaceLiteral
    (timelikeLine_causalCurveIn_id (I := univ) ⟨0, trivial⟩ ordConnected_univ)
    (s := 0) (t := 1) trivial trivial (by norm_num) S

theorem isCauchySurfaceOn_top {S : Set M} : C.IsCauchySurfaceOn ⊤ S ↔ C.IsCauchySurface S :=
  Iff.rfl

end Causality

/-! ### Reparametrising an open interval by `ℝ` -/

/-- The map `t ↦ arctan t / π + 1/2`, an increasing homeomorphism of `ℝ` onto `]0, 1[`. -/
theorem range_arctan_unit :
    range (fun t : ℝ => Real.arctan t / Real.pi + 1 / 2) = Ioo 0 1 := by
  have hπ := Real.pi_pos
  ext y
  constructor
  · rintro ⟨t, rfl⟩
    have h1 := Real.neg_pi_div_two_lt_arctan t
    have h2 := Real.arctan_lt_pi_div_two t
    have h3 : -(1 / 2 : ℝ) < Real.arctan t / Real.pi := by rw [lt_div_iff₀ hπ]; linarith
    have h4 : Real.arctan t / Real.pi < 1 / 2 := by rw [div_lt_iff₀ hπ]; linarith
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨h0, h1⟩
    have hu : (y - 1 / 2) * Real.pi ∈ range Real.arctan := by
      rw [Real.range_arctan]; constructor <;> nlinarith
    obtain ⟨t, ht⟩ := hu
    exact ⟨t, by simp only; rw [ht]; field_simp; ring⟩

/-- An interval of `ℝ` with neither a least nor a greatest point is the set of points strictly
between its infimum and its supremum (each when it exists). -/
theorem eq_setOf_of_ordConnected {I : Set ℝ} (hne : I.Nonempty) (hoc : I.OrdConnected)
    (hmin : ∀ t ∈ I, ∃ s ∈ I, s < t) (hmax : ∀ t ∈ I, ∃ s ∈ I, t < s) :
    I = {x | (BddBelow I → sInf I < x) ∧ (BddAbove I → x < sSup I)} := by
  ext x
  constructor
  · intro hx
    refine ⟨fun hb => lt_of_le_of_ne (csInf_le hb hx) fun h => ?_,
      fun ha => lt_of_le_of_ne (le_csSup ha hx) fun h => ?_⟩
    · obtain ⟨s, hs, hsx⟩ := hmin x hx
      exact absurd (csInf_le hb hs) (not_le.2 (h ▸ hsx))
    · obtain ⟨s, hs, hsx⟩ := hmax x hx
      exact absurd (le_csSup ha hs) (not_le.2 (h ▸ hsx))
  · rintro ⟨hb, ha⟩
    obtain ⟨y, hy, hyx⟩ : ∃ y ∈ I, y < x := by
      by_cases h : BddBelow I
      · exact exists_lt_of_csInf_lt hne (hb h)
      · exact not_bddBelow_iff.1 h x
    obtain ⟨z, hz, hxz⟩ : ∃ z ∈ I, x < z := by
      by_cases h : BddAbove I
      · exact exists_lt_of_lt_csSup hne (ha h)
      · exact not_bddAbove_iff.1 h x
    exact hoc.out hy hz ⟨hyx.le, hxz.le⟩

/-- **Every open interval of `ℝ` is the image of `ℝ` by a continuous strictly increasing map.** -/
theorem exists_strictMono_range {I : Set ℝ} (hne : I.Nonempty) (hoc : I.OrdConnected)
    (hmin : ∀ t ∈ I, ∃ s ∈ I, s < t) (hmax : ∀ t ∈ I, ∃ s ∈ I, t < s) :
    ∃ ψ : ℝ → ℝ, StrictMono ψ ∧ Continuous ψ ∧ range ψ = I := by
  have hI := eq_setOf_of_ordConnected hne hoc hmin hmax
  set α := sInf I
  set β := sSup I
  by_cases hb : BddBelow I <;> by_cases ha : BddAbove I
  · -- `I = ]α, β[`
    obtain ⟨t₀, ht₀⟩ := hne
    have hαt : α < t₀ := by rw [hI] at ht₀; exact ht₀.1 hb
    have htβ : t₀ < β := by rw [hI] at ht₀; exact ht₀.2 ha
    have hαβ : 0 < β - α := by linarith
    set σ : ℝ → ℝ := fun t => Real.arctan t / Real.pi + 1 / 2 with hσ
    have hσmono : StrictMono σ := fun s t h => by
      have := div_lt_div_of_pos_right (Real.arctan_strictMono h) Real.pi_pos
      simp only [hσ]; linarith
    refine ⟨fun t => α + (β - α) * σ t, fun s t h => by
      have := mul_lt_mul_of_pos_left (hσmono h) hαβ; linarith, by
      simp only [hσ]; fun_prop, ?_⟩
    rw [hI]
    ext y
    simp only [mem_range, mem_setOf_eq, hb, ha, true_implies]
    constructor
    · rintro ⟨t, rfl⟩
      have hσt : σ t ∈ Ioo 0 1 := by rw [← range_arctan_unit]; exact ⟨t, rfl⟩
      exact ⟨by nlinarith [hσt.1], by nlinarith [hσt.2]⟩
    · rintro ⟨h1, h2⟩
      have hu : (y - α) / (β - α) ∈ range σ := by
        rw [hσ, range_arctan_unit]
        exact ⟨div_pos (by linarith) hαβ, (div_lt_one hαβ).2 (by linarith)⟩
      obtain ⟨t, ht⟩ := hu
      exact ⟨t, by rw [ht]; field_simp; ring⟩
  · -- `I = ]α, +∞[`
    refine ⟨fun t => α + Real.exp t, fun s t h => by
      have := Real.exp_strictMono h; linarith, by fun_prop, ?_⟩
    rw [hI]
    ext y
    simp only [mem_range, mem_setOf_eq, hb, ha, true_implies, false_implies, and_true]
    constructor
    · rintro ⟨t, rfl⟩
      have := Real.exp_pos t; linarith
    · intro h
      exact ⟨Real.log (y - α), by rw [Real.exp_log (by linarith)]; ring⟩
  · -- `I = ]-∞, β[`
    refine ⟨fun t => β - Real.exp (-t), fun s t h => by
      have := Real.exp_strictMono (neg_lt_neg h); linarith, by fun_prop, ?_⟩
    rw [hI]
    ext y
    simp only [mem_range, mem_setOf_eq, hb, ha, true_implies, false_implies, true_and]
    constructor
    · rintro ⟨t, rfl⟩
      have := Real.exp_pos (-t); linarith
    · intro h
      exact ⟨-Real.log (β - y), by rw [neg_neg, Real.exp_log (by linarith)]; ring⟩
  · -- `I = ℝ`
    refine ⟨id, strictMono_id, continuous_id, ?_⟩
    rw [hI, range_id]
    ext y
    simp [hb, ha]

namespace Causality

variable {C : Causality M} {I : Set ℝ} {c : ℝ → M}

/-- In a causally arc-connected causal spacetime with `J^±(p) ≠ {p}`, an inextensible curve has
neither a first nor a last parameter. -/
theorem Inextensible.no_least (hC : C.CausallyArcConnected) (hcaus : C.IsCausal)
    (hJm : ∀ p : M, C.Jminus ⊤ {p} ≠ {p}) (hc : C.Inextensible ⊤ I c) :
    ∀ t ∈ I, ∃ s ∈ I, s < t := by
  intro t ht
  by_contra h
  refine hc.2 (extensible_of_isLeast hC hcaus hc.1 ⟨ht, fun s hs => ?_⟩ (hJm _))
  by_contra hst
  exact h ⟨s, hs, not_le.1 hst⟩

theorem Inextensible.no_greatest (hC : C.CausallyArcConnected) (hcaus : C.IsCausal)
    (hJp : ∀ p : M, C.Jplus ⊤ {p} ≠ {p}) (hc : C.Inextensible ⊤ I c) :
    ∀ t ∈ I, ∃ s ∈ I, t < s := by
  intro t ht
  by_contra h
  refine hc.2 (extensible_of_isGreatest hC hcaus hc.1 ⟨ht, fun s hs => ?_⟩ (hJp _))
  by_contra hst
  exact h ⟨s, hs, not_le.1 hst⟩

/-- **Inextensible curves are curves over `ℝ`**: in a causally arc-connected causal spacetime
with `J^±(p) ≠ {p}`, an inextensible curve over `I` is, after a continuous strictly increasing
reparametrisation `ψ : ℝ → I` onto `I`, an inextensible curve over `ℝ`. -/
theorem Inextensible.reparam (hC : C.CausallyArcConnected) (hcaus : C.IsCausal)
    (hJm : ∀ p : M, C.Jminus ⊤ {p} ≠ {p}) (hJp : ∀ p : M, C.Jplus ⊤ {p} ≠ {p})
    (hc : C.Inextensible ⊤ I c) :
    ∃ ψ : ℝ → ℝ, StrictMono ψ ∧ Continuous ψ ∧ range ψ = I ∧ C.Inextensible ⊤ univ (c ∘ ψ) := by
  obtain ⟨ψ, hψ, hψc, hψr⟩ := exists_strictMono_range hc.1.nonempty hc.1.ordConnected
    (hc.no_least hC hcaus hJm) (hc.no_greatest hC hcaus hJp)
  have hmaps : ∀ t, ψ t ∈ I := fun t => hψr ▸ mem_range_self t
  refine ⟨ψ, hψ, hψc, hψr, hc.1.comp ⟨0, trivial⟩ ordConnected_univ (hψ.strictMonoOn univ)
    hψc.continuousOn fun t _ => hmaps t, fun hext => hc.2 ?_⟩
  -- the inverse of `ψ` on `I`
  set g : ℝ → ℝ := Function.invFun ψ
  have hψg : ∀ t ∈ I, ψ (g t) = t := fun t ht =>
    Function.invFun_eq (show ∃ s, ψ s = t by rw [← mem_range, hψr]; exact ht)
  refine hext.of_comp (ψ := g) (fun s hs t ht h => ?_) (fun _ _ => trivial)
    (fun s _ => ⟨ψ s, hmaps s, Function.leftInverse_invFun hψ.injective s⟩)
    (fun t ht => by simp only [Function.comp]; rw [hψg t ht])
  rw [← hψ.lt_iff_lt, hψg s hs, hψg t ht]
  exact h

end Causality

end Causal
