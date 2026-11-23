import GX.BBS.IPm
import GX.Singular.Quotient

/-!
# BBS § 3.3.1: the quotient circles `J/⟨f⟩`, and their `(G,X)`-structures

Target `T-bbs-quotient-circle` (`roadmap/roadmap.toml`; kind `research`, BBS layer L2 in lean-gx,
DEC-192). `papers/bbs/legacy/labeled/colI_v1.tex`, the unlabeled prose of § 3.3.1 (l.688–722) and
the quotients that § 3.3.2's remark `bbsrem:previous_section_observed_only` (l.926–932) needs. No
label of its own. 0 `sorry`. For `GXScaffold.BBS.HSSingularities`: `GX.exists_rp1Circle_quotient`
is the statement of `GX.exists_rp1Circle_of_ne_one`; `GX.exists_gammaLinkCircle_quotient_of_forall_lt`
builds the `(Γ_p, ℓ(p))`-circles `ℝ/⟨δ² g̃^{±1}⟩` of `GX.exists_positive_negative`.

> Observe that non-trivial elliptic elements acts on $\widetilde{\R\PP}^1$ as translations,
> \textit{i.e.} freely and properly discontinuously. Hence the quotient space of their action is
> naturally a real projective structure on the circle. (l.690–692)
>
> Observe that if $k \neq 0$, the action of $\tilde{g}$ on $\widetilde{\R\PP}^1$ is free and
> properly discontinuous. Hence the associated quotient space, which is naturally equipped with a
> real projective structure, is homeomorphic to the circle. (l.698–701)
>
> Then the action of $g$ on $]x_0, x_1[$ is free and properly discontinuous, the quotient space
> is a \textit{parabolic} or \textit{hyperbolic circle of degree $0$.} (l.709–710)
>
> It follows that every cyclic subgroup of $\tilde{G}$ is the holonomy group of a real projective
> circle (l.721–722)

## Main declarations

* **The fundamental domain `[x₀, f x₀[`** (`GX.exists_reparam_conj_add_one`): an increasing
  homeomorphism `f` of an interval `J ⊆ ℝ` with `x < f x` is conjugate to `s ↦ s + 1` by an
  increasing homeomorphism `ψ : ℝ → J`, `ψ 0 = x₀`, `ψ (s + 1) = f (ψ s)`.
* **`ℝ/ℤ` with a `(G,X)`-structure** (`GX.exists_gxQuotient_add_one`): for a local homeomorphism
  `D : ℝ → X` with `D (s + 1) = γ • D s`, the orbit space of `ℤ` acting by translations carries
  `GX.gxQuotient` of the structure pulled back along `D`; it is the circle, its projection
  `E : ℝ → L` is a periodic covering along which `D` is a developing map, and this property
  determines the maximal atlas.
* **The quotient circles** (`GX.exists_gxQuotientCircle`, the target's statement): for an interval
  `J ⊆ ℝ`, an increasing homeomorphism `f` of `J` with `x < f x` and a local homeomorphism
  `D : J → X` with `D ∘ f = γ • D`, the quotient `J/⟨f⟩` is a circle with a `(G,X)`-structure of
  developing map `D` and holonomy `γ`: `π : J → L` is continuous, open, onto, its fibres the
  `⟨f⟩`-orbits, and `D` develops along it; `E = π ∘ ψ` is a periodic covering along which `D ∘ ψ`
  develops with holonomy `γ`; the structure is unique up to maximal atlas.
* **`G̃` on `ℝP̃¹`** (l.690–701): an element without fixed point is conjugate to `s ↦ s ± 1`
  (`GX.GTilde.exists_conj_translation`); `f` permutes each component of `{x | x < f x}`
  (`GX.GTilde.bijOn_connectedComponentIn`).
* **`ℝP¹`-circles** (l.690–722): for `f ∈ G̃` and `x₀ < f x₀`, the quotient of the component of
  `{x | x < f x}` through `x₀` is an `ℝP¹`-circle of lifted holonomy `f` with developed image that
  component (`GX.exists_hasLiftedHolonomy_of_lt_apply`; all of `ℝP̃¹` when `x < f x` everywhere,
  `GX.exists_hasLiftedHolonomy_of_forall_lt`). Hence **every non-trivial cyclic subgroup of `G̃`
  is the holonomy group of an `ℝP¹`-circle** (`GX.exists_rp1Circle_quotient`; group form
  `GX.exists_rp1Circle_zpowers`). The trivial subgroup is not (`GX.not_hasLiftedHolonomy_one`,
  `GX.not_every_cyclic_subgroup_is_holonomy`): l.721 as printed is false for it.
* **`(Γ_p, ℓ(p))`-circles** (`GX.exists_gammaLinkCircle_quotient`, `…_of_lt_apply`,
  `…_of_forall_lt`): from a local homeomorphism `D : J → ℓ(p)` with `D ∘ f = ρ • D`, `ρ ∈ Γ_p`, the
  `(Γ_p, ℓ(p))`-circle `⟨p, cs, hcs, hL⟩` on `J/⟨f⟩`, along whose periodic covering `E` the map
  `D ∘ ψ` is a developing map (`GX.GammaLinkCircle.IsDevAlong`).

## Hypothesis checklist

| BBS | here |
|---|---|
| "an increasing homeomorphism `f` of `J`" (the block; `g` on `]x₀, x₁[`, l.709) | ✓ `BijOn f J J`, `StrictMonoOn f J`, `ContinuousOn f J` |
| `J` an open interval (`]x₀, x₁[`, or `ℝP̃¹`) | ⚠ weakened: `J.OrdConnected` with a point `x₀`; openness follows |
| `x < f x` on `J` (the canonical orientation, l.731–737) | ✓ carried; for `f x < x` use `f⁻¹` (`GX.exists_rp1Circle_quotient`) |
| "free and properly discontinuous" (l.691, l.699, l.709) | ⚠ read: not stated for `⟨f⟩` on `J` (SCOPE (a)); what is proved is the conjugacy `ψ` to `s ↦ s + 1`, from `x < f x` |
| `D : J → X` a local homeomorphism, `D ∘ f = γ • D` | ✓ `IsLocalHomeomorphOn D J`, `∀ x ∈ J` |
| "non-trivial elliptic" (l.690), "`k ≠ 0`" (l.698) | ⚠ weakened: no fixed point (`GX.GTilde.exists_conj_translation`) |
| "every cyclic subgroup" (l.721) | ⚠ false for `{1}` (`GX.not_every_cyclic_subgroup_is_holonomy`); proved for the non-trivial ones |

## SCOPE (disclosed)

* **(a) Realisation of `J/⟨f⟩`.** The quotient is built as `ℝ/ℤ` through the fundamental domain
  `ψ`, which conjugates `f` to `s ↦ s + 1`; `GX.exists_gxQuotientCircle` states that it is
  `J/⟨f⟩` (an open continuous surjection `π` of `J` whose fibres are the `⟨f⟩`-orbits). The
  `⟨f⟩`-action on `J` is not formalized as a `MulAction`, so "free and properly discontinuous"
  is not a separate declaration: it holds for the conjugate translation action (the `hfree`,
  `hdisc` of `GX.gxQuotient` in the proof of `GX.exists_gxQuotient_add_one`).
* **(b) "naturally"** (l.692, l.700) is read as: the projection is a `(G,X)`-morphism from the
  structure pulled back along `D`, and the structure is the unique one up to maximal atlas.
* **(c) "as translations"** (l.691) is read topologically: conjugate to `s ↦ s ± 1` by an
  increasing homeomorphism of `ℝ`, not by an element of `G̃`.
* **(d) l.721** is read for the oriented lifted holonomies, as in `GXScaffold.BBS.HSSingularities`
  SCOPE (a): `H ≤ G̃` is the holonomy group of `L` when `H = ⟨f⟩` for a lifted holonomy `f` of `L`
  (`GX.HasLiftedHolonomy`, defined up to conjugacy). The orientation of l.709–710 (`g` or `g⁻¹`
  on `]x₀, x₁[`) is that of `GX.exists_rp1Circle_quotient`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`; lean-causal `ca2ad78`
through `GX.BBS.IPm`.
-/

noncomputable section

open Set Filter Topology
open scoped MatrixGroups

namespace GX

/-! ## 1. A fundamental domain `[x₀, f x₀[` -/

section FundamentalDomain

/-- A strictly increasing map `ℝ → ℝ` with an order-connected range maps `]a, b[` onto
`]ψ a, ψ b[` (mathlib's `OrderEmbedding.image_Ioo`). -/
theorem image_Ioo_of_strictMono {ψ : ℝ → ℝ} (hψ : StrictMono ψ) (hr : (range ψ).OrdConnected)
    (a b : ℝ) : ψ '' Ioo a b = Ioo (ψ a) (ψ b) :=
  (OrderEmbedding.ofStrictMono ψ hψ).image_Ioo hr a b

/-- A continuous strictly increasing map `ℝ → ℝ` with an order-connected range is an open
embedding. -/
theorem isOpenEmbedding_of_strictMono {ψ : ℝ → ℝ} (hψ : StrictMono ψ) (hc : Continuous ψ)
    (hr : (range ψ).OrdConnected) : IsOpenEmbedding ψ := by
  refine IsOpenEmbedding.of_continuous_injective_isOpenMap hc hψ.injective fun U hU => ?_
  refine isOpen_iff_mem_nhds.2 ?_
  rintro _ ⟨s, hs, rfl⟩
  obtain ⟨a, b, hab, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.1 (hU.mem_nhds hs)
  refine mem_of_superset (Ioo_mem_nhds (hψ hab.1) (hψ hab.2)) ?_
  rw [← image_Ioo_of_strictMono hψ hr]
  exact image_mono hsub

/-- **The fundamental domain `[x₀, f x₀[`**: an increasing homeomorphism `f` of an interval `J`
with `x < f x` is conjugate to the translation `s ↦ s + 1` by an increasing homeomorphism
`ψ : ℝ → J` with `ψ 0 = x₀`. -/
theorem exists_reparam_conj_add_one {J : Set ℝ} (hJ : J.OrdConnected) {x₀ : ℝ} (hx₀ : x₀ ∈ J)
    {f : ℝ → ℝ} (hfJ : BijOn f J J) (hfm : StrictMonoOn f J) (hfc : ContinuousOn f J)
    (hlt : ∀ x ∈ J, x < f x) :
    ∃ ψ : ℝ → ℝ, Continuous ψ ∧ StrictMono ψ ∧ range ψ = J ∧ ψ 0 = x₀ ∧
      ∀ s, ψ (s + 1) = f (ψ s) := by
  -- `f` as an increasing permutation `F` of `J`
  set F : Equiv.Perm J := hfJ.equiv f with hFdef
  have hFapp : ∀ y : J, (F y : ℝ) = f y := fun _ => rfl
  have hinv : ∀ (σ : Equiv.Perm J) (y : J), σ (σ⁻¹ y) = y := fun σ y => σ.apply_symm_apply y
  have hinv' : ∀ (σ : Equiv.Perm J) (y : J), σ⁻¹ (σ y) = y := fun σ y => σ.symm_apply_apply y
  have hFm : StrictMono F := fun a b hab => by
    show (F a : ℝ) < F b
    rw [hFapp, hFapp]; exact hfm a.2 b.2 hab
  have hFi : StrictMono ⇑(F⁻¹) := fun a b hab => by
    by_contra h
    have h' := hFm.monotone (not_lt.1 h)
    rw [hinv, hinv] at h'
    exact absurd hab (not_lt.2 h')
  have hFn : ∀ n : ℤ, StrictMono ⇑(F ^ n) := by
    intro n
    induction n using Int.induction_on with
    | zero => rw [zpow_zero, Equiv.Perm.coe_one]; exact strictMono_id
    | succ m ih => rw [zpow_add_one, Equiv.Perm.coe_mul]; exact ih.comp hFm
    | pred m ih => rw [zpow_sub_one, Equiv.Perm.coe_mul]; exact ih.comp hFi
  have hpow : ∀ (n : ℤ) (y : J), (F ^ (n + 1)) y = F ((F ^ n) y) := fun n y => by
    rw [add_comm, zpow_one_add, Equiv.Perm.mul_apply]
  have hpow' : ∀ (n : ℤ) (y : J), (F ^ (n + 1)) y = (F ^ n) (F y) := fun n y => by
    rw [zpow_add_one, Equiv.Perm.mul_apply]
  -- the orbit `c n = fⁿ x₀`
  set a₀ : J := ⟨x₀, hx₀⟩ with ha₀
  set c : ℤ → ℝ := fun n => ((F ^ n) a₀ : ℝ) with hcdef
  have hc1 : ∀ n, c (n + 1) = f (c n) := fun n => by
    simp only [hcdef]; rw [hpow, hFapp]
  have hcJ : ∀ n, c n ∈ J := fun n => ((F ^ n) a₀).2
  have hcm : StrictMono c := strictMono_int_of_lt_succ fun n => by
    rw [hc1]; exact hlt _ (hcJ n)
  have hc0 : c 0 = x₀ := by simp only [hcdef, zpow_zero, Equiv.Perm.one_apply, ha₀]
  -- a convergent orbit would converge to a fixed point
  have nofix : ∀ (u : ℕ → ℝ) (L : ℝ), L ∈ J → (∀ k, u k ∈ J) → Tendsto u atTop (𝓝 L) →
      Tendsto (fun k => f (u k)) atTop (𝓝 L) → False := by
    intro u L hL hu h1 h2
    have h3 : Tendsto (fun k => f (u k)) atTop (𝓝 (f L)) :=
      (hfc L hL).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨h1, Eventually.of_forall hu⟩)
    exact (hlt L hL).ne (tendsto_nhds_unique h2 h3)
  -- every `y ∈ J` lies in some `[cₙ, cₙ₊₁[`
  have hbr : ∀ y ∈ J, ∃ n : ℤ, c n ≤ y ∧ y < c (n + 1) := by
    intro y hy
    have hne : ∃ z : ℤ, c z ≤ y := by
      by_contra hcon
      push Not at hcon
      set u : ℕ → ℝ := fun k => c (-(k : ℤ)) with hudef
      have hu : Antitone u := fun i j hij => hcm.monotone (by
        simp only [neg_le_neg_iff, Nat.cast_le]; exact hij)
      have hbdd : BddBelow (range u) := ⟨y, by rintro _ ⟨k, rfl⟩; exact (hcon _).le⟩
      have hlim := tendsto_atTop_ciInf hu hbdd
      have hu0 : u 0 = x₀ := by simp only [hudef, Nat.cast_zero, neg_zero, hc0]
      have hLJ : (⨅ k, u k) ∈ J := hJ.out hy hx₀
        ⟨le_ciInf fun k => (hcon _).le, hu0 ▸ ciInf_le hbdd 0⟩
      refine nofix (fun k => u (k + 1)) _ hLJ (fun k => hcJ _)
        (hlim.comp (tendsto_add_atTop_nat 1)) ?_
      convert hlim using 1
      funext k
      simp only [hudef]
      rw [← hc1]; congr 1; push_cast; ring
    have hbdd : ∃ b : ℤ, ∀ z : ℤ, c z ≤ y → z ≤ b := by
      by_contra hcon
      push Not at hcon
      have hall : ∀ k : ℕ, c k ≤ y := fun k => by
        obtain ⟨z, hz, hkz⟩ := hcon k
        exact (hcm hkz).le.trans hz
      set u : ℕ → ℝ := fun k => c k with hudef
      have hu : Monotone u := fun i j hij => hcm.monotone (by exact_mod_cast hij)
      have hbdd : BddAbove (range u) := ⟨y, by rintro _ ⟨k, rfl⟩; exact hall k⟩
      have hlim := tendsto_atTop_ciSup hu hbdd
      have hu0 : u 0 = x₀ := by simp only [hudef, Nat.cast_zero, hc0]
      have hLJ : (⨆ k, u k) ∈ J := hJ.out hx₀ hy ⟨hu0 ▸ le_ciSup hbdd 0, ciSup_le hall⟩
      refine nofix u _ hLJ (fun k => hcJ _) hlim ?_
      convert hlim.comp (tendsto_add_atTop_nat 1) using 1
      funext k
      simp only [hudef, Function.comp_apply]
      rw [← hc1]; push_cast; rfl
    obtain ⟨n, hn, hmax⟩ := Int.exists_greatest_of_bdd hbdd hne
    refine ⟨n, hn, ?_⟩
    by_contra h
    have := hmax (n + 1) (not_lt.1 h)
    omega
  -- the parametrisation of the fundamental domain `[x₀, f x₀[`
  have hb : x₀ < f x₀ := hlt x₀ hx₀
  have hd : 0 < f x₀ - x₀ := by linarith
  have hfx₀ : f x₀ ∈ J := hfJ.mapsTo hx₀
  set φ : ℝ → ℝ := fun t => x₀ + t * (f x₀ - x₀) with hφdef
  have hφJ : ∀ s, φ (Int.fract s) ∈ J := fun s => hJ.out hx₀ hfx₀
    ⟨by simp only [hφdef]; nlinarith [Int.fract_nonneg s],
      by simp only [hφdef]; nlinarith [Int.fract_lt_one s]⟩
  set w : ℝ → J := fun s => ⟨φ (Int.fract s), hφJ s⟩ with hwdef
  have hw1 : ∀ s, w (s + 1) = w s := fun s =>
    Subtype.ext (by simp only [hwdef, Int.fract_add_one])
  have hwm : ∀ s t, Int.fract s < Int.fract t → w s < w t := fun s t h => by
    show φ (Int.fract s) < φ (Int.fract t)
    simp only [hφdef]; nlinarith
  have hw_lt : ∀ s, w s < F a₀ := fun s => by
    show φ (Int.fract s) < f x₀
    simp only [hφdef]; nlinarith [Int.fract_lt_one s]
  have hw_ge : ∀ s, a₀ ≤ w s := fun s => by
    show x₀ ≤ φ (Int.fract s)
    simp only [hφdef]; nlinarith [Int.fract_nonneg s]
  set ψ : ℝ → ℝ := fun s => ((F ^ ⌊s⌋) (w s) : ℝ) with hψdef
  have hψf : ∀ s, ψ (s + 1) = f (ψ s) := fun s => by
    simp only [hψdef]; rw [Int.floor_add_one, hw1, hpow, hFapp]
  have hψ0 : ψ 0 = x₀ := by
    simp only [hψdef, hwdef, hφdef, Int.floor_zero, zpow_zero, Equiv.Perm.one_apply,
      Int.fract_zero, zero_mul, add_zero]
  have hψm : StrictMono ψ := by
    intro s t hst
    rcases (Int.floor_mono hst.le).lt_or_eq with hlt' | heq
    · calc ψ s < c (⌊s⌋ + 1) := by
            show ((F ^ ⌊s⌋) (w s) : ℝ) < ((F ^ (⌊s⌋ + 1)) a₀ : ℝ)
            rw [hpow']; exact Subtype.coe_lt_coe.2 (hFn _ (hw_lt s))
        _ ≤ c ⌊t⌋ := hcm.monotone (by omega)
        _ ≤ ψ t := Subtype.coe_le_coe.2 ((hFn ⌊t⌋).monotone (hw_ge t))
    · have hfr : Int.fract s < Int.fract t := by
        rw [Int.fract, Int.fract, heq]; linarith
      show ((F ^ ⌊s⌋) (w s) : ℝ) < ((F ^ ⌊t⌋) (w t) : ℝ)
      rw [heq]; exact Subtype.coe_lt_coe.2 (hFn _ (hwm s t hfr))
  have hψr : range ψ = J := by
    refine Subset.antisymm (by rintro _ ⟨s, rfl⟩; exact ((F ^ ⌊s⌋) (w s)).2) fun y hy => ?_
    obtain ⟨n, hn1, hn2⟩ := hbr y hy
    have hFn' : StrictMono ⇑((F ^ n)⁻¹) := by rw [← zpow_neg]; exact hFn (-n)
    set z : J := (F ^ n)⁻¹ ⟨y, hy⟩ with hz
    have hz1 : a₀ ≤ z := by
      have h := hFn'.monotone (show (F ^ n) a₀ ≤ ⟨y, hy⟩ from Subtype.coe_le_coe.1 hn1)
      rwa [hinv'] at h
    have hz2 : z < F a₀ := by
      have h := hFn' (show (⟨y, hy⟩ : J) < (F ^ n) (F a₀) from Subtype.coe_lt_coe.1 (by
        rw [← hpow']; exact hn2))
      rwa [hinv'] at h
    have hz1' : x₀ ≤ (z : ℝ) := Subtype.coe_le_coe.2 hz1
    have hz2' : (z : ℝ) < f x₀ := Subtype.coe_lt_coe.2 hz2
    set t : ℝ := ((z : ℝ) - x₀) / (f x₀ - x₀) with htdef
    have ht0 : 0 ≤ t := div_nonneg (by linarith) hd.le
    have ht1 : t < 1 := (div_lt_one hd).2 (by linarith)
    have hfl : ⌊(n : ℝ) + t⌋ = n := by
      rw [Int.floor_intCast_add, Int.floor_eq_zero_iff.2 ⟨ht0, ht1⟩, add_zero]
    have hfr : Int.fract ((n : ℝ) + t) = t := by
      rw [Int.fract_intCast_add, Int.fract_eq_self.2 ⟨ht0, ht1⟩]
    have hwz : w ((n : ℝ) + t) = z := Subtype.ext (by
      show φ (Int.fract ((n : ℝ) + t)) = z
      rw [hfr]; simp only [hφdef, htdef]; field_simp; ring)
    refine ⟨(n : ℝ) + t, ?_⟩
    show ((F ^ ⌊(n : ℝ) + t⌋) (w ((n : ℝ) + t)) : ℝ) = y
    rw [hfl, hwz, hz, hinv]
  have hψc : Continuous ψ := continuous_iff_continuousAt.2 fun s =>
    continuousAt_of_monotoneOn_of_image_mem_nhds (hψm.monotone.monotoneOn _)
      (Ioo_mem_nhds (by linarith : s - 1 < s) (by linarith : s < s + 1))
      (by rw [image_Ioo_of_strictMono hψm (hψr ▸ hJ)]
          exact Ioo_mem_nhds (hψm (by linarith)) (hψm (by linarith)))
  exact ⟨ψ, hψc, hψm, hψr, hψ0, hψf⟩

end FundamentalDomain

/-! ## 2. `ℝ/ℤ` with the structure of a `ℤ`-equivariant local homeomorphism -/

section Translation

variable {G X : Type*} [Group G] [TopologicalSpace X] [MulAction G X] [ContinuousConstSMul G X]

/-- `ℤ` acting on `ℝ` by the translations `s ↦ s + n`, written multiplicatively (used through
`letI` only: it is not an instance). -/
@[reducible] def addIntAction : MulAction (Multiplicative ℤ) ℝ where
  smul n s := s + ((Multiplicative.toAdd n : ℤ) : ℝ)
  one_smul s := by
    show s + ((Multiplicative.toAdd (1 : Multiplicative ℤ) : ℤ) : ℝ) = s
    simp
  mul_smul m n s := by
    show s + ((Multiplicative.toAdd (m * n) : ℤ) : ℝ) =
      s + ((Multiplicative.toAdd n : ℤ) : ℝ) + ((Multiplicative.toAdd m : ℤ) : ℝ)
    rw [toAdd_mul]; push_cast; ring

omit [TopologicalSpace X] [ContinuousConstSMul G X] in
/-- The holonomy of a translation by `n`: from `D (s + 1) = γ • D s`, `D (s + n) = γⁿ • D s`. -/
theorem zpow_smul_of_add_one {D : ℝ → X} {γ : G} (h : ∀ s, D (s + 1) = γ • D s) (n : ℤ)
    (s : ℝ) : D (s + n) = γ ^ n • D s := by
  induction n using Int.induction_on generalizing s with
  | zero => simp
  | succ m ih =>
    rw [show s + ((m + 1 : ℤ) : ℝ) = (s + ((m : ℤ) : ℝ)) + 1 by push_cast; ring, h, ih,
      ← mul_smul, ← zpow_one_add, add_comm]
  | pred m ih =>
    have h1 := h (s + ((-(m : ℤ) - 1 : ℤ) : ℝ))
    rw [show s + ((-(m : ℤ) - 1 : ℤ) : ℝ) + 1 = s + ((-(m : ℤ) : ℤ) : ℝ) by push_cast; ring,
      ih] at h1
    rw [show γ ^ (-(m : ℤ) - 1) = γ⁻¹ * γ ^ (-(m : ℤ)) by
      rw [sub_eq_add_neg, add_comm, zpow_add, zpow_neg_one], mul_smul, h1, inv_smul_smul]

/-- **The quotient of `ℝ` by `s ↦ s + 1` as a `(G,X)`-circle**: for a local homeomorphism
`D : ℝ → X` with `D (s + 1) = γ • D s`, the orbit space `L` of `ℤ` acting by translations carries a
`(G,X)`-structure (`GX.gxQuotient` of the structure pulled back along `D`); `L` is the circle, its
projection `E` is a periodic covering, `D` is a developing map along `E`, and any
`(G,X)`-structure on `L` along which `D` is a developing map has the same maximal atlas. -/
theorem exists_gxQuotient_add_one {D : ℝ → X} (hD : IsLocalHomeomorph D) {γ : G}
    (hDγ : ∀ s, D (s + 1) = γ • D s) :
    ∃ (L : Type) (_ : TopologicalSpace L) (cs : ChartedSpace X L),
      HasGroupoid L (gxGroupoid G X) ∧ IsCircle L ∧ ∃ E : ℝ → L, IsPeriodicCover E ∧
        (∀ s, ∃ g : G, ∀ᶠ s' in 𝓝 s, D s' = g • chartAt X (E s) (E s')) ∧
        ∀ cs' : ChartedSpace X L, @HasGroupoid X _ L _ cs' (gxGroupoid G X) →
          (∀ s, ∃ g : G, ∀ᶠ s' in 𝓝 s, D s' = g • @chartAt X _ L _ cs' (E s) (E s')) →
          @StructureGroupoid.maximalAtlas X L _ _ cs' (gxGroupoid G X) =
            @StructureGroupoid.maximalAtlas X L _ _ cs (gxGroupoid G X) := by
  letI : MulAction (Multiplicative ℤ) ℝ := addIntAction
  have hsmul : ∀ (n : Multiplicative ℤ) (s : ℝ), n • s = s + ((Multiplicative.toAdd n : ℤ) : ℝ) :=
    fun _ _ => rfl
  letI cs₀ : ChartedSpace X ℝ := pullbackChartedSpace hD
  haveI : HasGroupoid ℝ (gxGroupoid G X) := hasGroupoid_pullback hD
  have hch : ∀ s s' : ℝ, chartAt X s s' = D s' := fun s s' => by
    rw [pullback_chartAt_apply hD, chartAt_self_eq]; rfl
  -- `ℤ` acts by `(G,X)`-morphisms, freely and properly discontinuously
  have hΓ : ∀ n : Multiplicative ℤ, IsGXMorphism G X fun p : ℝ => n • p := fun n =>
    ⟨continuous_add_const _, fun x => ⟨γ ^ (Multiplicative.toAdd n), Eventually.of_forall
      fun y => by rw [hch, hch, hsmul]; exact zpow_smul_of_add_one hDγ _ y⟩⟩
  have hfree : ∀ (n : Multiplicative ℤ) (x : ℝ), n • x = x → n = 1 := fun n x h => by
    rw [hsmul] at h
    have h1 : ((Multiplicative.toAdd n : ℤ) : ℝ) = 0 := by linarith
    exact toAdd_eq_zero.1 (by exact_mod_cast h1)
  have hdisc : ∀ x : ℝ, ∃ U ∈ 𝓝 x, ∀ n : Multiplicative ℤ,
      ((n • ·) '' U ∩ U).Nonempty → n • x = x := fun x => by
    refine ⟨Ioo (x - 1 / 2) (x + 1 / 2), Ioo_mem_nhds (by linarith) (by linarith),
      fun n hn => ?_⟩
    obtain ⟨_, ⟨y, hy, rfl⟩, hy'⟩ := hn
    have hy'' : y + ((Multiplicative.toAdd n : ℤ) : ℝ) ∈ Ioo (x - 1 / 2) (x + 1 / 2) := hy'
    have h1 : (-1 : ℤ) < Multiplicative.toAdd n := by
      have : (-1 : ℝ) < ((Multiplicative.toAdd n : ℤ) : ℝ) := by linarith [hy.1, hy.2, hy''.1, hy''.2]
      exact_mod_cast this
    have h2 : Multiplicative.toAdd n < 1 := by
      have : ((Multiplicative.toAdd n : ℤ) : ℝ) < 1 := by linarith [hy.1, hy.2, hy''.1, hy''.2]
      exact_mod_cast this
    have h3 : Multiplicative.toAdd n = 0 := by omega
    rw [hsmul, h3, Int.cast_zero, add_zero]
  obtain ⟨cs, hcs, hmor, huniq⟩ := gxQuotient hΓ hfree hdisc
  -- the orbit space is the circle
  letI : Setoid ℝ := MulAction.orbitRel (Multiplicative ℤ) ℝ
  have hwd : ∀ a b : ℝ, a ≈ b → RP1.proj a = RP1.proj b := fun a b h => by
    obtain ⟨n, hn⟩ := exists_smul_eq_of_orbitMk_eq (Γ := Multiplicative ℤ) (Quotient.sound h)
    rw [← hn, hsmul, RP1.proj_add_int]
  set Φ : Orbits (Multiplicative ℤ) ℝ → Circle := Quotient.lift RP1.proj hwd with hΦdef
  have hΦc : Continuous Φ := RP1.continuous_proj.quotient_lift hwd
  have hΦi : Function.Injective Φ := by
    intro a b hab
    induction a using Quotient.inductionOn with | h a => ?_
    induction b using Quotient.inductionOn with | h b => ?_
    obtain ⟨n, hn⟩ := RP1.proj_eq_proj_iff.1 (hab : RP1.proj a = RP1.proj b)
    rw [hn]
    exact orbitMk_smul (Γ := Multiplicative ℤ) (Multiplicative.ofAdd n) b
  have hΦs : Function.Surjective Φ := fun z => by
    obtain ⟨t, ht⟩ := RP1.proj_surjective z
    exact ⟨orbitMk _ t, ht⟩
  have hΦo : IsOpenMap Φ := fun U hU => by
    have h : Φ '' U = RP1.proj '' (orbitMk (Multiplicative ℤ) ⁻¹' U) := by
      ext z
      constructor
      · rintro ⟨q, hq, rfl⟩
        induction q using Quotient.inductionOn with | h a => exact ⟨a, hq, rfl⟩
      · rintro ⟨a, ha, rfl⟩
        exact ⟨orbitMk _ a, ha, rfl⟩
    rw [h]
    exact RP1.isOpenMap_proj _ (hU.preimage continuous_quot_mk)
  set φ : Orbits (Multiplicative ℤ) ℝ ≃ₜ Circle :=
    (Equiv.ofBijective Φ ⟨hΦi, hΦs⟩).toHomeomorphOfContinuousOpen hΦc hΦo with hφdef
  have hE : φ.symm ∘ RP1.proj = orbitMk (Multiplicative ℤ) := funext fun s => by
    simp only [Function.comp_apply]
    rw [Homeomorph.symm_apply_eq]
    rfl
  refine ⟨Orbits (Multiplicative ℤ) ℝ, inferInstance, cs, hcs, ⟨φ⟩, orbitMk _,
    by rw [← hE]; exact isPeriodicCover_of_homeomorph φ, fun s => ?_, fun cs' hcs' hdev' => ?_⟩
  · obtain ⟨g, hg⟩ := hmor.exists_smul_eq s
    refine ⟨g⁻¹, hg.mono fun s' hs' => ?_⟩
    rw [hch] at hs'
    rw [hs', inv_smul_smul]
  · refine huniq cs' hcs' ⟨continuous_quot_mk, fun s => ?_⟩
    obtain ⟨g, hg⟩ := hdev' s
    refine ⟨g⁻¹, hg.mono fun s' hs' => ?_⟩
    rw [hch, hs', inv_smul_smul]

end Translation

/-! ## 3. The quotient circles `J/⟨f⟩` -/

section QuotientCircle

variable {G X : Type*} [Group G] [TopologicalSpace X] [MulAction G X] [ContinuousConstSMul G X]

/-- **The quotient circle `J/⟨f⟩`** (BBS § 3.3.1, l.689–711): for an interval `J ⊆ ℝ`, an
increasing homeomorphism `f` of `J` with `x < f x`, and a local homeomorphism `D : J → X` with
`D ∘ f = γ • D`, the quotient `J/⟨f⟩` is homeomorphic to the circle and carries a
`(G,X)`-structure with developing map `D` and holonomy `γ`.

Read: `π : ℝ → L` restricted to `J` is the quotient map `J → J/⟨f⟩` (continuous, open, onto, its
fibres the `⟨f⟩`-orbits) and `D` is a developing map along it; through the fundamental domain
`ψ : ℝ → J` (`ψ (s + 1) = f (ψ s)`), `E = π ∘ ψ` is a periodic covering along which `D ∘ ψ` is a
developing map of holonomy `γ`; and the structure is the only one, up to maximal atlas, along
which `D ∘ ψ` develops. -/
theorem exists_gxQuotientCircle {J : Set ℝ} (hJ : J.OrdConnected) {x₀ : ℝ} (hx₀ : x₀ ∈ J)
    {f : ℝ → ℝ} (hfJ : BijOn f J J) (hfm : StrictMonoOn f J) (hfc : ContinuousOn f J)
    (hlt : ∀ x ∈ J, x < f x) {D : ℝ → X} (hD : IsLocalHomeomorphOn D J) {γ : G}
    (hDγ : ∀ x ∈ J, D (f x) = γ • D x) :
    ∃ (L : Type) (_ : TopologicalSpace L) (cs : ChartedSpace X L),
      HasGroupoid L (gxGroupoid G X) ∧ IsCircle L ∧ ∃ (π : ℝ → L) (E : ℝ → L) (ψ : ℝ → ℝ),
        -- `π` on `J` is the quotient map `J → J/⟨f⟩`
        ContinuousOn π J ∧ (∀ U, IsOpen U → U ⊆ J → IsOpen (π '' U)) ∧ π '' J = univ ∧
        (∀ x ∈ J, ∀ y ∈ J, π x = π y ↔ ∃ n : ℕ, f^[n] x = y ∨ f^[n] y = x) ∧
        -- `D` is a developing map along `π`
        (∀ x ∈ J, ∃ g : G, ∀ᶠ y in 𝓝 x, D y = g • chartAt X (π x) (π y)) ∧
        -- the fundamental domain `ψ`, the periodic covering `E = π ∘ ψ`, the holonomy `γ`
        Continuous ψ ∧ StrictMono ψ ∧ range ψ = J ∧ ψ 0 = x₀ ∧ (∀ s, ψ (s + 1) = f (ψ s)) ∧
        (∀ s, π (ψ s) = E s) ∧ IsPeriodicCover E ∧
        (∀ s, ∃ g : G, ∀ᶠ s' in 𝓝 s, D (ψ s') = g • chartAt X (E s) (E s')) ∧
        (∀ s, D (ψ (s + 1)) = γ • D (ψ s)) ∧
        -- uniqueness of the structure
        ∀ cs' : ChartedSpace X L, @HasGroupoid X _ L _ cs' (gxGroupoid G X) →
          (∀ s, ∃ g : G, ∀ᶠ s' in 𝓝 s, D (ψ s') = g • @chartAt X _ L _ cs' (E s) (E s')) →
          @StructureGroupoid.maximalAtlas X L _ _ cs' (gxGroupoid G X) =
            @StructureGroupoid.maximalAtlas X L _ _ cs (gxGroupoid G X) := by
  -- the fundamental domain
  obtain ⟨ψ, hψc, hψm, hψr, hψ0, hψf⟩ := exists_reparam_conj_add_one hJ hx₀ hfJ hfm hfc hlt
  have hψe : IsOpenEmbedding ψ := isOpenEmbedding_of_strictMono hψm hψc (hψr ▸ hJ)
  have hψJ : ∀ s, ψ s ∈ J := fun s => hψr ▸ mem_range_self s
  have hJo : IsOpen J := hψr ▸ hψe.isOpen_range
  -- `D ∘ ψ` is a local homeomorphism of holonomy `γ` for `s ↦ s + 1`
  have hD' : IsLocalHomeomorph (D ∘ ψ) := isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.2
    (hD.comp hψe.isLocalHomeomorph.isLocalHomeomorphOn fun s _ => hψJ s)
  have hDγ' : ∀ s, (D ∘ ψ) (s + 1) = γ • (D ∘ ψ) s := fun s => by
    simp only [Function.comp_apply]; rw [hψf]; exact hDγ _ (hψJ s)
  obtain ⟨L, _, cs, hcs, hL, E, hE, hdev, huniq⟩ := exists_gxQuotient_add_one hD' hDγ'
  -- the inverse of `ψ` on `J`
  set ψi : ℝ → ℝ := ⇑(hψe.toOpenPartialHomeomorph ψ).symm with hψidef
  have hleft : ∀ s, ψi (ψ s) = s := fun s =>
    IsOpenEmbedding.toOpenPartialHomeomorph_left_inv ψ hψe
  have hright : ∀ y ∈ J, ψ (ψi y) = y := fun y hy =>
    IsOpenEmbedding.toOpenPartialHomeomorph_right_inv ψ hψe (hψr.symm ▸ hy)
  have hψic : ∀ y ∈ J, ContinuousAt ψi y := fun y hy =>
    (hψe.toOpenPartialHomeomorph ψ).continuousAt_symm (by
      rw [IsOpenEmbedding.toOpenPartialHomeomorph_target, hψr]; exact hy)
  set π : ℝ → L := E ∘ ψi with hπdef
  have hπψ : ∀ s, π (ψ s) = E s := fun s => by simp only [hπdef, Function.comp_apply, hleft]
  -- `ψ (s + n) = fⁿ (ψ s)`
  have hiter : ∀ (n : ℕ) (s : ℝ), ψ (s + n) = f^[n] (ψ s) := by
    intro n
    induction n with
    | zero => intro s; simp
    | succ m ih =>
      intro s
      rw [Function.iterate_succ_apply', ← ih, Nat.cast_succ, ← add_assoc, hψf]
  have hEZ : ∀ (s : ℝ) (n : ℤ), E (s + n) = E s := hE.add_int
  refine ⟨L, inferInstance, cs, hcs, hL, π, E, ψ, ?_, ?_, ?_, ?_, ?_, hψc, hψm, hψr, hψ0, hψf, hπψ,
    hE, hdev, hDγ', huniq⟩
  · -- continuity of `π` on `J`
    exact fun y hy => (hE.isCoveringMap.continuous.continuousAt.comp (hψic y hy)).continuousWithinAt
  · -- `π` is open on `J`
    intro U hU hUJ
    have h : π '' U = E '' (ψ ⁻¹' U) := by
      ext z
      constructor
      · rintro ⟨y, hy, rfl⟩
        obtain ⟨s, rfl⟩ := hψr.symm ▸ hUJ hy
        exact ⟨s, hy, (hπψ s).symm⟩
      · rintro ⟨s, hs, rfl⟩
        exact ⟨ψ s, hs, hπψ s⟩
    rw [h]
    exact hE.isCoveringMap.isLocalHomeomorph.isOpenMap _ (hU.preimage hψc)
  · -- `π` maps `J` onto `L`
    refine eq_univ_of_forall fun z => ?_
    obtain ⟨s, rfl⟩ := hE.surjective z
    exact ⟨ψ s, hψJ s, hπψ s⟩
  · -- the fibres of `π` on `J` are the `⟨f⟩`-orbits
    intro x hx y hy
    obtain ⟨s, rfl⟩ := hψr.symm ▸ hx
    obtain ⟨t, rfl⟩ := hψr.symm ▸ hy
    rw [hπψ, hπψ]
    constructor
    · intro hst
      obtain ⟨m, hm⟩ := hE.fiber s t hst
      rcases le_or_gt 0 m with h0 | h0
      · refine ⟨m.toNat, Or.inl ?_⟩
        rw [← hiter, hm]
        congr 2
        exact_mod_cast (Int.toNat_of_nonneg h0)
      · refine ⟨(-m).toNat, Or.inr ?_⟩
        rw [← hiter, hm]
        congr 1
        have : (((-m).toNat : ℤ) : ℝ) = -(m : ℝ) := by
          rw [Int.toNat_of_nonneg (by omega)]; push_cast; ring
        push_cast at this ⊢
        rw [this]; ring
    · rintro ⟨n, hn | hn⟩
      · have h1 : t = s + n := hψm.injective (by rw [hiter, hn])
        have h2 := hEZ s n
        push_cast at h2
        rw [h1, h2]
      · have h1 : s = t + n := hψm.injective (by rw [hiter, hn])
        have h2 := hEZ t n
        push_cast at h2
        rw [h1, h2]
  · -- `D` is a developing map along `π`
    intro x hx
    obtain ⟨s, rfl⟩ := hψr.symm ▸ hx
    obtain ⟨g, hg⟩ := hdev s
    refine ⟨g, ?_⟩
    have h1 : ∀ᶠ y in 𝓝 (ψ s), (D ∘ ψ) (ψi y) = g • chartAt X (E s) (E (ψi y)) := by
      have := (hψic (ψ s) hx).eventually (f := ψi) (by rw [hleft]; exact hg)
      exact this
    filter_upwards [h1, hJo.mem_nhds hx] with y hy1 hy2
    rw [Function.comp_apply, hright y hy2] at hy1
    rw [hy1, hπψ]
    rfl

end QuotientCircle

/-! ## 4. `ℝP¹`-circles: every non-trivial cyclic subgroup of `G̃` is a holonomy group -/

section RP1Instance

/-- For `f ∈ G̃` and `w < f w`, the whole segment `[w, f w]` lies in `{x | x < f x}`. -/
theorem GTilde.Icc_subset_setOf_lt_apply (f : GTilde) {w : ℝ} (hw : w < f w) :
    Icc w (f w) ⊆ {x | x < f x} := by
  intro z hz
  by_contra hcon
  have hzf : f z ≤ z := not_lt.1 hcon
  -- a fixed point `c ∈ [w, z]`, by the intermediate value theorem
  have hcont : ContinuousOn (fun x => f x - x) (Icc w z) :=
    ((GTilde.continuous f).sub continuous_id).continuousOn
  obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc' hz.1 hcont
    (show (0 : ℝ) ∈ Icc (f z - z) (f w - w) from ⟨by linarith, by linarith⟩)
  have hfc : f c = c := by simp only at hc0; linarith
  have hwc : w < c := lt_of_le_of_ne hc.1 (by rintro rfl; linarith)
  have h1 := GTilde.strictMono f hwc
  rw [hfc] at h1
  linarith [hc.2, hz.2]

/-- **`f ∈ G̃` permutes the component of `{x | x < f x}` through `x₀`** (the interval
`]x₀', x₁[` between successive fixed points of l.705–711, or all of `ℝP̃¹`; empty when
`f x₀ ≤ x₀`). -/
theorem GTilde.bijOn_connectedComponentIn (f : GTilde) (x₀ : ℝ) :
    BijOn f (connectedComponentIn {x | x < f x} x₀) (connectedComponentIn {x | x < f x} x₀) := by
  set F := {x : ℝ | x < f x} with hFdef
  set J := connectedComponentIn F x₀ with hJdef
  have hJF : J ⊆ F := connectedComponentIn_subset F x₀
  -- a segment `[w, f w]` meeting `J` lies in `J`
  have hseg : ∀ w, w < f w → ∀ y ∈ Icc w (f w), y ∈ J → Icc w (f w) ⊆ J :=
    fun w hw y hy hyJ => by
      rw [hJdef, connectedComponentIn_eq hyJ]
      exact isPreconnected_Icc.subset_connectedComponentIn hy
        (GTilde.Icc_subset_setOf_lt_apply f hw)
  have hmaps : MapsTo f J J := fun y hy =>
    hseg y (hJF hy) y ⟨le_rfl, (hJF hy).le⟩ hy ⟨(hJF hy).le, le_rfl⟩
  have hsurj : SurjOn f J J := fun y hy => by
    have hfw : f (f⁻¹ y) = y := GTilde.apply_inv_apply f y
    have hw : f⁻¹ y < f (f⁻¹ y) := by
      rw [hfw]
      have h1 := GTilde.strictMono f⁻¹ (show y < f y from hJF hy)
      rwa [GTilde.inv_apply_apply] at h1
    exact ⟨f⁻¹ y, hseg (f⁻¹ y) hw y ⟨(hw.trans_eq hfw).le, hfw.ge⟩ hy ⟨le_rfl, hw.le⟩, hfw⟩
  exact ⟨hmaps, (GTilde.strictMono f).injective.injOn, hsurj⟩

/-- **l.690–691, "non-trivial elliptic elements act on `ℝP̃¹` as translations"**, in the
topological reading: an element of `G̃` without fixed point (a non-trivial elliptic one,
`GX.GTilde.IsElliptic.apply_ne`, or `δᵏ g` with `k ≠ 0`) moves every point the same way, and is
conjugate by an increasing homeomorphism `ψ` of `ℝ` to `s ↦ s + 1` or to `s ↦ s - 1`. -/
theorem GTilde.exists_conj_translation {f : GTilde} (hf : ∀ x, f x ≠ x) :
    ((∀ x, x < f x) ∨ ∀ x, f x < x) ∧
      ∃ ψ : ℝ → ℝ, Continuous ψ ∧ StrictMono ψ ∧ range ψ = univ ∧
        ((∀ s, f (ψ s) = ψ (s + 1)) ∨ ∀ s, f (ψ s) = ψ (s - 1)) := by
  have hdir : (∀ x, x < f x) ∨ ∀ x, f x < x := by
    by_contra h
    push Not at h
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := h
    obtain ⟨c, -, hc⟩ := intermediate_value_uIcc (a := a) (b := b) (f := fun x => f x - x)
      ((GTilde.continuous f).sub continuous_id).continuousOn
      (show (0 : ℝ) ∈ uIcc (f a - a) (f b - b) from
        mem_uIcc.2 (Or.inl ⟨by linarith, by linarith⟩))
    exact hf c (by simp only at hc; linarith)
  refine ⟨hdir, ?_⟩
  have hsurj : SurjOn f univ univ := surjOn_univ.2 fun y => ⟨f⁻¹ y, GTilde.apply_inv_apply f y⟩
  rcases hdir with hlt | hgt
  · obtain ⟨ψ, hψc, hψm, hψr, -, hψf⟩ := exists_reparam_conj_add_one ordConnected_univ
      (mem_univ 0) ⟨mapsTo_univ _ univ, (GTilde.strictMono f).injective.injOn, hsurj⟩
      ((GTilde.strictMono f).strictMonoOn univ) (GTilde.continuous f).continuousOn
      (fun x _ => hlt x)
    exact ⟨ψ, hψc, hψm, hψr, Or.inl fun s => (hψf s).symm⟩
  · have hlt' : ∀ x, x < f⁻¹ x := fun x => by
      have h1 := GTilde.strictMono f⁻¹ (hgt x)
      rwa [GTilde.inv_apply_apply] at h1
    obtain ⟨ψ, hψc, hψm, hψr, -, hψf⟩ := exists_reparam_conj_add_one ordConnected_univ
      (mem_univ 0) ⟨mapsTo_univ _ univ, (GTilde.strictMono f⁻¹).injective.injOn,
        surjOn_univ.2 fun y => ⟨f y, GTilde.inv_apply_apply f y⟩⟩
      ((GTilde.strictMono f⁻¹).strictMonoOn univ) (GTilde.continuous f⁻¹).continuousOn
      (fun x _ => hlt' x)
    refine ⟨ψ, hψc, hψm, hψr, Or.inr fun s => ?_⟩
    have h1 := hψf (s - 1)
    rw [sub_add_cancel] at h1
    rw [h1, GTilde.apply_inv_apply]

/-- **l.689–711**: for `f ∈ G̃` and `x₀ < f x₀`, the quotient by `⟨f⟩` of the component `J` of
`{x | x < f x}` containing `x₀` (all of `ℝP̃¹` when `f` has no fixed point: elliptic, or of degree
`k ≠ 0`, `GX.exists_hasLiftedHolonomy_of_forall_lt`; an interval `]x₀', x₁[` between successive
fixed points otherwise, degree `0`) is an `ℝP¹`-circle of lifted holonomy `f`, whose lifted
developing map has image `J`. -/
theorem exists_hasLiftedHolonomy_of_lt_apply {f : GTilde} {x₀ : ℝ} (hx₀ : x₀ < f x₀) :
    ∃ (L : Type) (_ : TopologicalSpace L) (_ : ChartedSpace RP1 L),
      HasGroupoid L (gxGroupoid PSL(2, ℝ) RP1) ∧ IsCircle L ∧
        ∃ (E : ℝ → L) (D : ℝ → ℝ), IsPeriodicCover E ∧ Continuous D ∧ StrictMono D ∧
          IsDevAlong E (RP1.proj ∘ D) ∧ (∀ s, D (s + 1) = f (D s)) ∧
            range D = connectedComponentIn {x | x < f x} x₀ := by
  obtain ⟨L, _, cs, hcs, hL, -, E, ψ, -, -, -, -, -, hψc, hψm, hψr, -, hψf, -, hE, hdev, -, -⟩ :=
    exists_gxQuotientCircle (G := PSL(2, ℝ)) (X := RP1)
      (J := connectedComponentIn {x | x < f x} x₀)
      isPreconnected_connectedComponentIn.ordConnected
      (mem_connectedComponentIn (show x₀ ∈ {x | x < f x} from hx₀))
      (GTilde.bijOn_connectedComponentIn f x₀) ((GTilde.strictMono f).strictMonoOn _)
      (GTilde.continuous f).continuousOn (fun x hx => (connectedComponentIn_subset {x | x < f x} x₀ hx : x < f x))
      RP1.isLocalHomeomorph_proj.isLocalHomeomorphOn (γ := GTilde.toPSL f)
      (fun x _ => GTilde.proj_apply f x)
  exact ⟨L, inferInstance, cs, hcs, hL, E, ψ, hE, hψc, hψm, hdev, hψf, hψr⟩

/-- **l.689–701**: for `f ∈ G̃` with `x < f x` everywhere (a non-trivial elliptic element moving
the points up, or `δᵏ g` with `k ≥ 1` and `g` with a fixed point), the quotient `ℝP̃¹/⟨f⟩` is an
`ℝP¹`-circle of lifted holonomy `f` whose lifted developing map is onto. -/
theorem exists_hasLiftedHolonomy_of_forall_lt {f : GTilde} (hf : ∀ x, x < f x) :
    ∃ (L : Type) (_ : TopologicalSpace L) (_ : ChartedSpace RP1 L),
      HasGroupoid L (gxGroupoid PSL(2, ℝ) RP1) ∧ IsCircle L ∧
        ∃ (E : ℝ → L) (D : ℝ → ℝ), IsPeriodicCover E ∧ Continuous D ∧ StrictMono D ∧
          IsDevAlong E (RP1.proj ∘ D) ∧ (∀ s, D (s + 1) = f (D s)) ∧ range D = univ := by
  obtain ⟨L, _, cs, hcs, hL, E, D, hE, hDc, hDm, hD, hDf, hDr⟩ :=
    exists_hasLiftedHolonomy_of_lt_apply (hf 0)
  have hF : {x : ℝ | x < f x} = univ := eq_univ_of_forall hf
  rw [hF, connectedComponentIn_univ, PreconnectedSpace.connectedComponent_eq_univ] at hDr
  exact ⟨L, inferInstance, cs, hcs, hL, E, D, hE, hDc, hDm, hD, hDf, hDr⟩

/-- **l.721, corrected**: every non-trivial cyclic subgroup `⟨f⟩` of `G̃` is the holonomy group of
an `ℝP¹`-circle (of lifted holonomy `f` or `f⁻¹`). The statement of
`GX.exists_rp1Circle_of_ne_one` (`GXScaffold.BBS.HSSingularities`), proved here. -/
theorem exists_rp1Circle_quotient {f : GTilde} (hf : f ≠ 1) :
    ∃ (L : Type) (_ : TopologicalSpace L) (_ : ChartedSpace RP1 L),
      HasGroupoid L (gxGroupoid PSL(2, ℝ) RP1) ∧ IsCircle L ∧
        (HasLiftedHolonomy L f ∨ HasLiftedHolonomy L f⁻¹) := by
  obtain ⟨x, hx⟩ : ∃ x, f x ≠ x := by
    by_contra h
    push Not at h
    exact hf (GTilde.ext' fun x => (h x).trans (GTilde.one_apply x).symm)
  rcases lt_or_gt_of_ne hx with h | h
  · have h' : x < f⁻¹ x := by
      have h1 := GTilde.strictMono f⁻¹ h
      rwa [GTilde.inv_apply_apply] at h1
    obtain ⟨L, _, cs, hcs, hL, E, D, hE, hDc, hDm, hD, hDf, -⟩ :=
      exists_hasLiftedHolonomy_of_lt_apply h'
    exact ⟨L, inferInstance, cs, hcs, hL, Or.inr ⟨E, D, hE, hDc, hDm, hD, hDf⟩⟩
  · obtain ⟨L, _, cs, hcs, hL, E, D, hE, hDc, hDm, hD, hDf, -⟩ :=
      exists_hasLiftedHolonomy_of_lt_apply h
    exact ⟨L, inferInstance, cs, hcs, hL, Or.inl ⟨E, D, hE, hDc, hDm, hD, hDf⟩⟩

/-- **l.721, the group form**: every non-trivial cyclic subgroup `H` of `G̃` is `⟨f⟩` for a lifted
holonomy `f` of an `ℝP¹`-circle. -/
theorem exists_rp1Circle_zpowers {H : Subgroup GTilde} (hH : IsCyclic H) (hne : H ≠ ⊥) :
    ∃ (L : Type) (_ : TopologicalSpace L) (_ : ChartedSpace RP1 L),
      HasGroupoid L (gxGroupoid PSL(2, ℝ) RP1) ∧ IsCircle L ∧
        ∃ f : GTilde, HasLiftedHolonomy L f ∧ Subgroup.zpowers f = H := by
  obtain ⟨g, rfl⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top H).1 hH
  have hg : g ≠ 1 := fun h => hne (by rw [h, Subgroup.zpowers_one_eq_bot])
  obtain ⟨L, _, cs, hcs, hL, h | h⟩ := exists_rp1Circle_quotient hg
  · exact ⟨L, inferInstance, cs, hcs, hL, g, h, rfl⟩
  · exact ⟨L, inferInstance, cs, hcs, hL, g⁻¹, h, Subgroup.zpowers_inv⟩

/-- **No `ℝP¹`-circle has trivial lifted holonomy**: the lifted developing map is increasing and
`D (s + 1) = f (D s)`, so `f ≠ 1` (l.718, "`ρ(1)` is non-trivial"). -/
theorem not_hasLiftedHolonomy_one {L : Type*} [TopologicalSpace L] [ChartedSpace RP1 L] :
    ¬ HasLiftedHolonomy L 1 := by
  rintro ⟨E, D, -, -, hD, -, hDf⟩
  have h1 := hD (lt_add_one (0 : ℝ))
  rw [hDf, GTilde.one_apply] at h1
  exact lt_irrefl _ h1

/-- **l.721 as printed is false**: the trivial subgroup of `G̃` is cyclic and is the holonomy
group of no `ℝP¹`-circle. -/
theorem not_every_cyclic_subgroup_is_holonomy :
    ¬ ∀ H : Subgroup GTilde, IsCyclic H →
      ∃ (L : Type) (_ : TopologicalSpace L) (_ : ChartedSpace RP1 L),
        HasGroupoid L (gxGroupoid PSL(2, ℝ) RP1) ∧ IsCircle L ∧
          ∃ f : GTilde, HasLiftedHolonomy L f ∧ Subgroup.zpowers f = H := by
  intro h
  obtain ⟨L, _, _, -, -, f, hf, hfH⟩ :=
    h ⊥ ((Subgroup.isCyclic_iff_exists_zpowers_eq_top ⊥).2 ⟨1, Subgroup.zpowers_one_eq_bot⟩)
  rw [Subgroup.zpowers_eq_bot] at hfH
  subst hfH
  exact not_hasLiftedHolonomy_one hf

end RP1Instance

/-! ## 5. `(Γ_p, ℓ(p))`-circles as quotients -/

section GammaInstance

/-- **`(Γ_p, ℓ(p))`-circles as quotients** (the quotients of § 3.3.2, l.880–931): for an interval
`J ⊆ ℝ`, an increasing homeomorphism `f` of `J` with `x < f x`, a local homeomorphism
`D : J → ℓ(p)` and `ρ ∈ Γ_p` with `D ∘ f = ρ • D`, the quotient `J/⟨f⟩` is a
`(Γ_p, ℓ(p))`-circle `C = ⟨p, cs, hcs, hL⟩` (so `C.pt = p` by definition) along whose periodic
covering `E` the map `D ∘ ψ` is a developing map, `ψ : ℝ → J` increasing and onto with
`ψ (s + 1) = f (ψ s)`. -/
theorem exists_gammaLinkCircle_quotient (p : HS 2) {J : Set ℝ} (hJ : J.OrdConnected) {x₀ : ℝ}
    (hx₀ : x₀ ∈ J) {f : ℝ → ℝ} (hfJ : BijOn f J J) (hfm : StrictMonoOn f J)
    (hfc : ContinuousOn f J) (hlt : ∀ x ∈ J, x < f x) {D : ℝ → Link p}
    (hD : IsLocalHomeomorphOn D J) {ρ : GammaP p} (hDf : ∀ x ∈ J, D (f x) = ρ • D x) :
    ∃ (L : Type) (_ : TopologicalSpace L) (cs : ChartedSpace (Link p) L)
      (hcs : HasGroupoid L (gxGroupoid (GammaP p) (Link p))) (hL : IsCircle L)
      (E : ℝ → L) (ψ : ℝ → ℝ), IsPeriodicCover E ∧ Continuous ψ ∧ StrictMono ψ ∧
        range ψ = J ∧ (∀ s, ψ (s + 1) = f (ψ s)) ∧
          (GammaLinkCircle.mk p cs hcs hL).IsDevAlong E (D ∘ ψ) := by
  obtain ⟨L, _, cs, hcs, hL, -, E, ψ, -, -, -, -, -, hψc, hψm, hψr, -, hψf, -, hE, hdev, -, -⟩ :=
    exists_gxQuotientCircle (G := GammaP p) (X := Link p) hJ hx₀ hfJ hfm hfc hlt hD (γ := ρ) hDf
  exact ⟨L, inferInstance, cs, hcs, hL, E, ψ, hE, hψc, hψm, hψr, hψf, hdev⟩

/-- **`(Γ_p, ℓ(p))`-circles of degree `0`**: for `f ∈ G̃`, `x₀ < f x₀`, and a local homeomorphism
`D : ℝ → ℓ(p)` with `D ∘ f = ρ • D` (e.g. `GX.linkCover` and a lift of `ρ`), the quotient of the
component of `{x | x < f x}` through `x₀`. -/
theorem exists_gammaLinkCircle_quotient_of_lt_apply (p : HS 2) {D : ℝ → Link p}
    (hD : IsLocalHomeomorph D) {f : GTilde} {x₀ : ℝ} (hx₀ : x₀ < f x₀) {ρ : GammaP p}
    (hDf : ∀ x, D (f x) = ρ • D x) :
    ∃ (L : Type) (_ : TopologicalSpace L) (cs : ChartedSpace (Link p) L)
      (hcs : HasGroupoid L (gxGroupoid (GammaP p) (Link p))) (hL : IsCircle L)
      (E : ℝ → L) (ψ : ℝ → ℝ), IsPeriodicCover E ∧ Continuous ψ ∧ StrictMono ψ ∧
        range ψ = connectedComponentIn {x | x < f x} x₀ ∧ (∀ s, ψ (s + 1) = f (ψ s)) ∧
          (GammaLinkCircle.mk p cs hcs hL).IsDevAlong E (D ∘ ψ) :=
  exists_gammaLinkCircle_quotient p (J := connectedComponentIn {x | x < f x} x₀)
    isPreconnected_connectedComponentIn.ordConnected
    (mem_connectedComponentIn (show x₀ ∈ {x | x < f x} from hx₀))
    (GTilde.bijOn_connectedComponentIn f x₀)
    ((GTilde.strictMono f).strictMonoOn _) (GTilde.continuous f).continuousOn
    (fun x hx => (connectedComponentIn_subset {x | x < f x} x₀ hx : x < f x)) hD.isLocalHomeomorphOn (fun x _ => hDf x)

/-- **`(Γ_p, ℓ(p))`-circles as quotients of `ℝ`** (the examples of l.928, `ℝ/⟨δ² g̃^{±1}⟩`): for
`f ∈ G̃` with `x < f x` everywhere (e.g. `f = δᵏ g`, `k ≥ 1`, `g` with a fixed point) and a local
homeomorphism `D : ℝ → ℓ(p)` with `D ∘ f = ρ • D`, the quotient `ℝ/⟨f⟩` is a
`(Γ_p, ℓ(p))`-circle. With `D = GX.linkCover p θ` the conclusion is
`(GammaLinkCircle.mk p cs hcs hL).IsLiftedDev θ E ψ f` (`GXScaffold.BBS.HSSingularities`). -/
theorem exists_gammaLinkCircle_quotient_of_forall_lt (p : HS 2) {D : ℝ → Link p}
    (hD : IsLocalHomeomorph D) {f : GTilde} (hlt : ∀ x, x < f x) {ρ : GammaP p}
    (hDf : ∀ x, D (f x) = ρ • D x) :
    ∃ (L : Type) (_ : TopologicalSpace L) (cs : ChartedSpace (Link p) L)
      (hcs : HasGroupoid L (gxGroupoid (GammaP p) (Link p))) (hL : IsCircle L)
      (E : ℝ → L) (ψ : ℝ → ℝ), IsPeriodicCover E ∧ Continuous ψ ∧ StrictMono ψ ∧
        (∀ s, ψ (s + 1) = f (ψ s)) ∧ (GammaLinkCircle.mk p cs hcs hL).IsDevAlong E (D ∘ ψ) := by
  obtain ⟨L, _, cs, hcs, hL, E, ψ, hE, hψc, hψm, -, hψf, hdev⟩ :=
    exists_gammaLinkCircle_quotient p ordConnected_univ (mem_univ 0)
      ⟨mapsTo_univ _ univ, (GTilde.strictMono f).injective.injOn,
        surjOn_univ.2 fun y => ⟨f⁻¹ y, GTilde.apply_inv_apply f y⟩⟩
      ((GTilde.strictMono f).strictMonoOn univ) (GTilde.continuous f).continuousOn
      (fun x _ => hlt x) hD.isLocalHomeomorphOn (fun x _ => hDf x)
  exact ⟨L, inferInstance, cs, hcs, hL, E, ψ, hE, hψc, hψm, hψf, hdev⟩

end GammaInstance

end GX
