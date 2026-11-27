import GXScaffold.BTZ.Admissible

/-!
# btz § 4.1: the marked surface group is not metabelian when `2g − 2 + s > 0`, and the marked holonomy without a non-metabelian hypothesis

Target `T-btz-surface-group-nonmetabelian` (`roadmap/roadmap.toml`).
`papers/btz/legacy/labeled/BTZ_1.tex`, § 4 (l.1124) and § 4.1 (l.1148–1155).

* `btzprop:holonomy_globally_hyperbolic_cauchy_compact` — `BTZ_1.tex:1153–1155` (proof
  l.1148–1151), **partial, unmarked** (SCOPE (b), (c)). This file removes the hypothesis
  `hnm : ¬IsMetabelianGroup π₁(Reg M)` of `GX.BTZAdm.btzprop_holonomy_e0`: the new form
  `GX.BTZAdm.btzprop_holonomy_e0_of_euler` assumes instead the paper's standing
  `2g − 2 + s > 0` (l.1124) and derives `hnm` from the injective marking `μ`.
* The algebra: `GX.BTZAdm.SurfaceGroup.not_isMetabelianGroup` — for `2g − 2 + s > 0` the marked
  surface group `⟨a, b, c | ∏[aᵢ, bᵢ] ∏ cⱼ⟩` is not metabelian, by a surjection onto the free
  group `F₂` (itself not metabelian, the strict `GX.freeGroup_not_isMetabelianGroup`); and its
  converse `GX.BTZAdm.SurfaceGroup.isMetabelianGroup_iff`: the bound is sharp, for
  `2g − 2 + s ≤ 0` the group is abelian.

> Let $\Sigma$ be a genus $g$ closed surface, $S\subset \Sigma$ be a marking of $\Sigma$ with
> $\#S=s$ and $2g-2+s>0$. (l.1124)

> By Proposition \ref{prop:abs_max}, $M^*$ is a globally hyperbolic Cauchy-complete
> $\mass{}$-maximal $\mass{}$-manifold with anabelian fundamental group (l.1148)

> The holonomy of a globally hyperbolic Cauchy-compact $\mass{0}$-mani\-fold is admissible.
> (l.1154)

## Hypothesis checklist

| paper | here |
|---|---|
| `2g − 2 + s > 0` (l.1124) | ✓ carried, `0 < 2 * (g : ℤ) - 2 + s` |
| `Γ` the marked surface group (l.1140) | ✓ `GX.BTZAdm.SurfaceGroup g s` (Admissible.lean) |
| « anabelian fundamental group » of `M* = Reg M` (l.1148) | ✓ no longer assumed: read as « not metabelian » (the hypothesis Barbot's theorem uses in the strict library) and derived from `2g − 2 + s > 0` and the injective marking `μ : Γ → π₁(Reg M)` |
| the rest of `btzprop:holonomy_globally_hyperbolic_cauchy_compact` | as in `GX.BTZAdm.btzprop_holonomy_e0` (Admissible.lean's checklist) |

## SCOPE (disclosed)

* (a) The cases of `2g − 2 + s > 0`: `g ≥ 2` (any `s`), `g = 1` with `s ≥ 1`, `g = 0` with
  `s ≥ 3`. Each has an explicit surjection `Γ → F₂ = ⟨x, y⟩`: for `g ≥ 2`,
  `a₁, b₁, a₂, b₂ ↦ x, y, y, x` and every other generator to `1` (`[x,y][y,x] = 1`); for
  `g ≥ 1, s ≥ 1`, `a₁, b₁, c₁ ↦ x, y, [x, y]⁻¹`; for `g = 0, s ≥ 3`, `c₁, c₂, c₃ ↦ x, y, (xy)⁻¹`.
  The converse (`2g − 2 + s ≤ 0`: `(g, s) ∈ {(0,0), (0,1), (0,2), (1,0)}`, abelian groups) is
  proved too, so `2g − 2 + s > 0` is exactly the non-metabelian range.
* (b) As in `GX.BTZAdm.btzprop_holonomy_e0`: `𝔼₀` only (T-btz-scope), and the marking `μ` is a
  hypothesis (an injective homomorphism into the deck group with each `cⱼ` a BTZ loop); that the
  marking of `π₁(Σ*) ≅ π₁(Reg M)` is of this form is T-btz-headline-repr's.
* (c) The genus `g` and `s` of the theorem are those of the marking `μ`; that they are the genus of
  a Cauchy surface and the number of BTZ lines of `M` is again T-btz-headline-repr's.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace GX

namespace BTZAdm

open scoped commutatorElement

section NonMetabelian

/-- A quotient of a metabelian group is metabelian: a surjection onto a non-metabelian group has a
non-metabelian source. -/
theorem not_isMetabelianGroup_of_surjective {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Surjective f) (hH : ¬IsMetabelianGroup H) : ¬IsMetabelianGroup G := by
  intro hG
  apply hH
  intro a b c e
  obtain ⟨a, rfl⟩ := hf a
  obtain ⟨b, rfl⟩ := hf b
  obtain ⟨c, rfl⟩ := hf c
  obtain ⟨e, rfl⟩ := hf e
  simp only [← map_commutatorElement, hG a b c e, map_one]

/-- A subgroup of a metabelian group is metabelian: an injection from a non-metabelian group has a
non-metabelian target. -/
theorem not_isMetabelianGroup_of_injective {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Injective f) (hG : ¬IsMetabelianGroup G) : ¬IsMetabelianGroup H := by
  intro hH
  apply hG
  intro a b c e
  apply hf
  rw [map_commutatorElement, map_commutatorElement, map_commutatorElement, map_one]
  exact hH _ _ _ _

/-- A commutative group is metabelian. -/
theorem isMetabelianGroup_of_comm {G : Type*} [Group G] (h : ∀ x y : G, x * y = y * x) :
    IsMetabelianGroup G := fun _ _ _ _ =>
  commutatorElement_eq_one_iff_mul_comm.2 (h _ _)

/-- The lift of the relator `∏[aᵢ, bᵢ] ∏ cⱼ` along a map of the generators. -/
theorem lift_surfaceRel {g s : ℕ} {G : Type*} [Group G] (f : SurfGen g s → G) :
    FreeGroup.lift f (surfaceRel g s) =
      (List.ofFn fun i : Fin g => ⁅f (SurfGen.a i), f (SurfGen.b i)⁆).prod *
        (List.ofFn fun j : Fin s => f (SurfGen.c j)).prod := by
  simp only [surfaceRel, map_mul, map_list_prod, List.map_ofFn, Function.comp_def,
    map_commutatorElement, FreeGroup.lift_apply_of]

-- The free group on two generators `x = of 0`, `y = of 1`.
local notation "F₂" => FreeGroup (Fin 2)

/-- A homomorphism to `F₂` whose range contains both generators is onto. -/
theorem surjective_of_mem_range {G : Type*} [Group G] (f : G →* F₂)
    (h0 : FreeGroup.of 0 ∈ f.range) (h1 : FreeGroup.of 1 ∈ f.range) : Function.Surjective f := by
  rw [← MonoidHom.range_eq_top, eq_top_iff, ← FreeGroup.closure_range_of, Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  fin_cases i
  · exact h0
  · exact h1

theorem fin_succ_succ_ne_one {n : ℕ} (i : Fin n) : (i.succ.succ : Fin (n + 2)) ≠ 1 := by
  intro h
  have := congrArg Fin.val h
  simp at this

theorem fin_succ3_ne_two {n : ℕ} (i : Fin n) : (i.succ.succ.succ : Fin (n + 3)) ≠ 2 := by
  intro h
  have := congrArg Fin.val h
  have h2 : ((2 : Fin (n + 3)) : ℕ) = 2 := rfl
  simp only [Fin.val_succ, h2] at this
  omega

/-- Genus `g ≥ 2`: `a₁, b₁, a₂, b₂ ↦ x, y, y, x`, the rest to `1`. -/
def genA (n s : ℕ) : SurfGen (n + 2) s → F₂
  | .a i => if i = 0 then FreeGroup.of 0 else if i = 1 then FreeGroup.of 1 else 1
  | .b i => if i = 0 then FreeGroup.of 1 else if i = 1 then FreeGroup.of 0 else 1
  | .c _ => 1

/-- The two generators of `F₂` lie in the range of the lift of a map of the generators of `Γ`
that hits them. -/
theorem of_mem_range_toGroup {g s : ℕ} {f : SurfGen g s → F₂}
    (h : ∀ r ∈ ({surfaceRel g s} : Set (FreeGroup (SurfGen g s))), FreeGroup.lift f r = 1)
    {u : SurfGen g s} {w : F₂} (hu : f u = w) : w ∈ (PresentedGroup.toGroup h).range :=
  ⟨PresentedGroup.of u, by rw [PresentedGroup.toGroup.of, hu]⟩

theorem surjA (n s : ℕ) : ∃ f : SurfaceGroup (n + 2) s →* F₂, Function.Surjective f := by
  have hrel : ∀ r ∈ ({surfaceRel (n + 2) s} : Set (FreeGroup (SurfGen (n + 2) s))),
      FreeGroup.lift (genA n s) r = 1 := by
    rintro r rfl
    rw [lift_surfaceRel]
    simp [List.ofFn_succ, genA, Fin.succ_ne_zero, fin_succ_succ_ne_one]
    simp only [commutatorElement_def]
    group
  exact ⟨_, surjective_of_mem_range _ (of_mem_range_toGroup hrel (u := .a 0) (by simp [genA]))
    (of_mem_range_toGroup hrel (u := .b 0) (by simp [genA]))⟩

/-- Genus `g ≥ 1`, `s ≥ 1`: `a₁, b₁, c₁ ↦ x, y, [x, y]⁻¹`, the rest to `1`. -/
def genB (n m : ℕ) : SurfGen (n + 1) (m + 1) → F₂
  | .a i => if i = 0 then FreeGroup.of 0 else 1
  | .b i => if i = 0 then FreeGroup.of 1 else 1
  | .c j => if j = 0 then ⁅(FreeGroup.of 0 : F₂), FreeGroup.of 1⁆⁻¹ else 1

theorem surjB (n m : ℕ) : ∃ f : SurfaceGroup (n + 1) (m + 1) →* F₂, Function.Surjective f := by
  have hrel : ∀ r ∈ ({surfaceRel (n + 1) (m + 1)} : Set (FreeGroup (SurfGen (n + 1) (m + 1)))),
      FreeGroup.lift (genB n m) r = 1 := by
    rintro r rfl
    rw [lift_surfaceRel]
    simp [List.ofFn_succ, genB]
    simp only [commutatorElement_def]
    group
  exact ⟨_, surjective_of_mem_range _ (of_mem_range_toGroup hrel (u := .a 0) (by simp [genB]))
    (of_mem_range_toGroup hrel (u := .b 0) (by simp [genB]))⟩

/-- Genus `0`, `s ≥ 3`: `c₁, c₂, c₃ ↦ x, y, (x y)⁻¹`, the rest to `1`. -/
def genC (m : ℕ) : SurfGen 0 (m + 3) → F₂
  | .a i => i.elim0
  | .b i => i.elim0
  | .c j => if j = 0 then FreeGroup.of 0 else if j = 1 then FreeGroup.of 1 else
      if j = 2 then (FreeGroup.of 0 * FreeGroup.of 1)⁻¹ else 1

theorem surjC (m : ℕ) : ∃ f : SurfaceGroup 0 (m + 3) →* F₂, Function.Surjective f := by
  have hrel : ∀ r ∈ ({surfaceRel 0 (m + 3)} : Set (FreeGroup (SurfGen 0 (m + 3)))),
      FreeGroup.lift (genC m) r = 1 := by
    rintro r rfl
    rw [lift_surfaceRel]
    simp [List.ofFn_succ, genC, fin_succ_succ_ne_one, fin_succ3_ne_two]
  exact ⟨_, surjective_of_mem_range _ (of_mem_range_toGroup hrel (u := .c 0) (by simp [genC]))
    (of_mem_range_toGroup hrel (u := .c 1) (by simp [genC]))⟩

/-- **The marked surface group is not metabelian when `2g − 2 + s > 0`** (l.1124): it maps onto
the free group `F₂` (SCOPE (a)). -/
theorem SurfaceGroup.not_isMetabelianGroup {g s : ℕ} (h : 0 < 2 * (g : ℤ) - 2 + s) :
    ¬IsMetabelianGroup (SurfaceGroup g s) := by
  have hF : ¬IsMetabelianGroup F₂ := freeGroup_not_isMetabelianGroup (show (0 : Fin 2) ≠ 1 by decide)
  obtain ⟨f, hf⟩ : ∃ f : SurfaceGroup g s →* F₂, Function.Surjective f := by
    rcases g with _ | _ | n
    · obtain ⟨m, rfl⟩ : ∃ m, s = m + 3 := ⟨s - 3, by omega⟩
      exact surjC m
    · obtain ⟨m, rfl⟩ : ∃ m, s = m + 1 := ⟨s - 1, by omega⟩
      exact surjB 0 m
    · exact surjA n s
  exact not_isMetabelianGroup_of_surjective f hf hF

/-- A group generated by pairwise commuting generators of a presentation is commutative. -/
theorem PresentedGroup.comm_of_gen {α : Type*} {rels : Set (FreeGroup α)}
    (h : ∀ u v : α, Commute (PresentedGroup.of (rels := rels) u) (PresentedGroup.of v))
    (x y : PresentedGroup rels) : x * y = y * x := by
  have hS : ∀ u ∈ Set.range (PresentedGroup.of (rels := rels)),
      ∀ v ∈ Set.range (PresentedGroup.of (rels := rels)), u * v = v * u := by
    rintro _ ⟨u, rfl⟩ _ ⟨v, rfl⟩
    exact (h u v).eq
  have hc := Subgroup.isMulCommutative_closure hS
  rw [PresentedGroup.closure_range_of] at hc
  exact Subtype.ext_iff.1 (hc.is_comm.comm ⟨x, trivial⟩ ⟨y, trivial⟩)

/-- For `2g − 2 + s ≤ 0`, i.e. `(g, s) ∈ {(0,0), (0,1), (0,2), (1,0)}`, the marked surface group
is commutative (trivial, trivial, `ℤ`, `ℤ²`). -/
theorem SurfaceGroup.comm_of_euler_nonpos {g s : ℕ} (h : 2 * (g : ℤ) - 2 + s ≤ 0)
    (x y : SurfaceGroup g s) : x * y = y * x := by
  apply PresentedGroup.comm_of_gen
  have hrel := SurfaceGroup.rel g s
  rcases g with _ | _ | n
  · rcases s with _ | _ | _ | m
    · rintro (i | i | i) <;> exact i.elim0
    · rintro (i | i | i) (j | j | j)
      all_goals first | exact i.elim0 | exact j.elim0 | skip
      fin_cases i; fin_cases j; exact Commute.refl _
    · simp [List.ofFn_succ] at hrel
      have hinv := eq_inv_of_mul_eq_one_right hrel
      have hc : Commute (SurfaceGroup.c (g := 0) (0 : Fin 2)) (SurfaceGroup.c 1) := by
        rw [hinv]; exact Commute.inv_right (Commute.refl _)
      rintro (i | i | i) (j | j | j)
      all_goals first | exact i.elim0 | exact j.elim0 | skip
      fin_cases i <;> fin_cases j
      · exact Commute.refl _
      · exact hc
      · exact hc.symm
      · exact Commute.refl _
    · push_cast at h; omega
  · rcases s with _ | m
    · simp [List.ofFn_succ] at hrel
      have hc : Commute (SurfaceGroup.a (s := 0) (0 : Fin 1)) (SurfaceGroup.b 0) :=
        commutatorElement_eq_one_iff_commute.1 hrel
      rintro (i | i | i) (j | j | j)
      all_goals first | exact i.elim0 | exact j.elim0 | skip
      all_goals fin_cases i; fin_cases j
      · exact Commute.refl _
      · exact hc
      · exact hc.symm
      · exact Commute.refl _
    · push_cast at h; omega
  · push_cast at h; omega

/-- **The bound is sharp**: the marked surface group is metabelian iff `2g − 2 + s ≤ 0`. -/
theorem SurfaceGroup.isMetabelianGroup_iff {g s : ℕ} :
    IsMetabelianGroup (SurfaceGroup g s) ↔ 2 * (g : ℤ) - 2 + s ≤ 0 :=
  ⟨fun hm => not_lt.1 fun h => SurfaceGroup.not_isMetabelianGroup h hm,
    fun h => isMetabelianGroup_of_comm (SurfaceGroup.comm_of_euler_nonpos h)⟩

end NonMetabelian

section Marked

open Causal.Flat

variable {M : Type} [TopologicalSpace M] [T2Space M] [ConnectedSpace M] [SecondCountableTopology M]
  [ChartedSpace E0Y M] [HasGroupoid M e0Groupoid]

/-- **`btzprop:holonomy_globally_hyperbolic_cauchy_compact`, marked form, for `𝔼₀`, from
`2g − 2 + s > 0`**: for `M` a globally hyperbolic, Cauchy-compact, Cauchy-maximal `𝔼₀`-manifold,
every developing pair `(𝒟, ρ)` of `Reg M` and every injective marking `μ : Γ → π₁(Reg M)` of a
marked surface group with `2g − 2 + s > 0` (each `cⱼ` a loop around a BTZ line), `ρ ∘ μ` is
admissible. The non-metabelianity of `π₁(Reg M)` is derived, not assumed. -/
theorem btzprop_holonomy_e0_of_euler (hGH : (E0CBG.CE M).GloballyHyperbolic)
    (hCC : ∃ S : Set M, E0Surgery.IsE0C1SpacelikeCauchy M S) (hmax : E0Spear.IsE0CauchyMaximal M)
    (x₀ : e0RegMFlat M)
    (D : Causal.UniversalCover (e0RegMFlat M) x₀ → Causal.Minkowski 2)
    (ρ : Causal.Deck (Causal.UniversalCover.proj (e0RegMFlat M) x₀) →* Causal.Flat.isom 2)
    (hpair : IsDevelopingPair x₀ D ρ) {g s : ℕ} (hgs : 0 < 2 * (g : ℤ) - 2 + s)
    (μ : SurfaceGroup g s →* Causal.Deck (Causal.UniversalCover.proj (e0RegMFlat M) x₀))
    (hμ : Function.Injective μ) (hc : ∀ j, IsBTZLoop x₀ (μ (SurfaceGroup.c j))) :
    IsAdmissible (ρ.comp μ) :=
  btzprop_holonomy_e0 hGH hCC hmax x₀
    (not_isMetabelianGroup_of_injective μ hμ (SurfaceGroup.not_isMetabelianGroup hgs))
    D ρ hpair μ hμ hc

end Marked

end BTZAdm

end GX
