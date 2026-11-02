import CausalScaffold.CBG.CausalConvex
import CausalScaffold.CBG.FromModel
import Causal.Flat.Geroch.Reach
import Causal.Flat.CauchyComplete
import Causal.Flat.SecondCountable
import Causal.Flat.LipschitzGraph

/-!
# A4 for the flat local model: slices through a boundary point, both time directions

CBG campaign, flat instance (design `docs/CBG-DESIGN.md` §4 "Flat instance", A4; package 12's
input `hA4f`, `hA4p` of `flat_cbg_of`, `Flat/CBG.lean`). **No label is marked** (design l.5–6:
marking ETT labels is the ETT campaign's). Cited, unmarked: `theo:CBG` — `ETT.tex:1884`; Sbierski
1309.7591, Thm 3.6 (geometric half), (3.12), Lemma 3.11.

> Proof of Theorem 3.6: […] we can find a p ∈ C which satisfies J⁻(p) ∩ ∂U ∩ J⁺ι(M) = {p}. […]
> Also note that U ∪ N is globally hyperbolic with Cauchy hypersurface ι(M): consider a point r on
> an inextendible timelike curve γ in U ∪ N. If r is in N \ U, the curve γ must intersect S, since
> S is a Cauchy hypersurface in N. The choice of τ₀ then implies that γ must also enter U. […]
> Moreover, γ cannot intersect ι(M) more than once, since ι(M) is also a Cauchy hypersurface for M.
> (Sbierski 1309.7591, pp. 18–20)

> (Isom, 𝐌)-manifolds: […] A4 hyperboloid level sets of τ_q(r) = √(−Q(q−r)) in a chart.
> (design §4)

The library's Minkowski space `Minkowski d` has `d` spatial dimensions (Barbot's `𝐌ⁿ` is
`n = d + 1`, kb/0024).

## What is proved (no `sorry`)

* **`flat_slice_future`, `flat_slice_past`** — A4 for flat spacetimes, in the Level-A form of
  `LocalModel.SliceFuture` / `SlicePast` (`CBG/FromModel`) read on `flatCausality d M`: for `M` a
  Hausdorff connected `(Isom, 𝐌)`-manifold, globally hyperbolic with Cauchy surface `S`, `U` open
  with `S ⊆ U` a Cauchy surface of `U`, `p ∈ ∂U ∩ J⁺(S)` (resp. `J⁻(S)`) with
  `J⁻(p) ∩ ∂U ∩ J⁺(S) = {p}` (resp. `J⁺(p) ∩ ∂U ∩ J⁻(S) = {p}`), and every open `O ∋ p`, there is
  an open `U' ⊋ U`, `U' ⊆ U ∪ O`, globally hyperbolic, with `S` a Cauchy surface of `U'`.
  The global hyperbolicity of `U` is **not used** (it is implied).
* **The construction is not Sbierski's hyperboloid and needs no compactness (R1)**. The corner
  condition puts the punctured causal past cone of `p` (near `p`) inside `U`
  (`mem_of_le_of_mem_interior_Jplus`: a point of it outside `closure U` has a chronological past
  point outside `closure U`, which is in `I⁻(p) ∩ J⁺(S) ⊆ U`, `mem_of_lt_of_mem_closure`). In the
  chart at `p` (`y₀ = e p`), the closed slice ball `{t = y₀.t − δ, ‖x − x₀‖ ≤ δ}` lies on that cone,
  hence in the chart image of `U`, hence (compactness of a closed ball of `ℝ^d`,
  `thickening_closedBall`) so does the open slice ball of radius `ρ = δ + ε'`. The diamond `N` of
  radius `ρ` over that slice ball contains `p` (as `ρ > δ`) and its equatorial slice `Γ` is a
  Cauchy surface of it with `Γ ⊆ U` (`flat_exists_cauchy_nbhd`). Then `U' = U ∪ N`: an inextensible
  curve of `U'` through `N` meets `Γ ⊆ U` by its component in `N`, then `S` by its component in `U`;
  uniqueness by acausality of `S` (`isCauchySurfaceOn_sup_of_slice`); `U'` is causally convex
  (`causallyConvexIn_of_isCauchySurfaceOn`), hence globally hyperbolic
  (`GloballyHyperbolicOn.of_causallyConvexIn`).
* **What resolves the previous agent's caution** (`Flat/CBG` SCOPE, "B4 carries no localisation
  to `J⁻(q)`"; `CBG/FromModel`'s `sliceFuture` SORRY: "nothing ties N to the side of τ⁻¹(c) that
  U ∪ N must add"): the slice `Γ` is taken **inside `U`**, strictly below `p`, rather than through
  `p` at the maximum of a time function; `N`'s added part is then on the correct side of `Γ`
  automatically, because every curve of `N` crosses `Γ` and `Γ ⊆ U`. The piece of `N` below `Γ` is
  harmless (curves there meet `Γ` too). The 1+1 example of `Flat/CBG`'s SCOPE (`U = {t < −|x|/2}`,
  `p = 0`) is handled: the slice `t = −δ` is in `U` for `|x| < 2δ`, so any `ρ ∈ (δ, 2δ)` works.
* General (any causality; **moved to `CBG/FromModel` on 2026-11-02**, interface round 3, where
  the generic A4 from a cone-slice B4, `slice_future_of_cone`/`slice_past_of_cone`, uses it —
  names unchanged, used here through the import): `isCauchySurfaceOn_sup_of_slice` (a union
  `A ⊔ N` keeps the Cauchy surface `S` of `A` when `N` has a Cauchy surface inside `A`),
  `extend_of_cauchy_nbhd` (the assembly of A4 from such an `N ∋ p`), `mem_of_lt_of_mem_closure` /
  `mem_of_le_of_mem_interior_Jplus` and their past forms (the corner condition's consequence).
* Minkowski: the diamonds `sliceDiamond` with their equatorial slices as Cauchy surfaces
  (`isCauchySurfaceOn_sliceDiamond`, a copy of `Flat/CBG`'s `isCauchySurfaceOn_mdiamond`, which
  this module may not import); the chart morphism `flatChart_isEMorphismOn` (a copy of
  `Flat/Cla/LocallyCauchy`'s `isEMorphismOn_chartSource`, not imported to keep the module light).

## Hypothesis checklist

| Level-A field (`LocalModel.SliceFuture`/`SlicePast`) / Sbierski Thm 3.6 | here |
|---|---|
| `M` T2, connected, a flat structure (`flatModelOf`) | ✓ carried (`[ChartedSpace (Minkowski d) M]`, `[HasGroupoid M (gxGroupoid …)]`); second countability derived (`flat_secondCountableTopology`, DEC-49) |
| `M` GH, `S` Cauchy in `M` | ✓ carried, used |
| `U` GH | ⚠ weakened: not used (`_hGHU`); `U` is causally convex as a Cauchy inclusion |
| `S ⊆ U`, `S` Cauchy in `U` | ✓ carried, used |
| `p ∈ ∂U`, `p ∈ J^±(S)`, corner `J^∓(p) ∩ ∂U ∩ J^±(S) = {p}` | ✓ carried, used |
| Lemma 3.11 (`q`, `J⁻(q) ∩ Uᶜ ∩ J⁺(Σ) ⊆ W`), `isCompact_Jplus_inter_Jminus` (R1) | ⚠ weakened: not needed |
| design §4 "hyperboloid level sets of `τ_q`" | ⚠ replaced: a flat slice strictly inside `U` below (above) `p`, and its diamond |

## SCOPE (disclosed)

* **Statement form.** The theorems are stated for `flatCausality d M` with the instances of a flat
  structure, not literally as `(flatModelOf d hJ₁ hJ₂).SliceFuture`: `Flat/CBG` (where `flatModelOf`
  lives) imports this module. The integrator's wrapper (checked, axioms `propext`,
  `Classical.choice`, `Quot.sound`, for every `hJ₁ hJ₂`) is:
  `intro M _ _ _ _ s U S hGH hGHU hSU hS hSU' p hp hpS hc O hpO;`
  `letI : ChartedSpace (Minkowski d) M := s.1;`
  `haveI : HasGroupoid M (gxGroupoid (isom d) (Minkowski d)) := s.2;`
  `have h : LocalModel.causality s = flatCausality d M := chartedCausality_eq_flatCausality;`
  `rw [h] at hGH hGHU hS hSU' hpS hc ⊢; exact flat_slice_future U S hGH hGHU hSU hS hSU' p hp hpS hc O hpO`
  (`flat_slice_past` likewise), giving `(flatModelOf d hJ₁ hJ₂).SliceFuture` / `.SlicePast`.
* **A4 as the interface states it is purely geometric**, and that is all this file proves: the
  extension of `ψ` to `U'` (Sbierski's use of Lemma 3.8 on `S`) is A3's, not A4's. A slice inside
  `U` serves A4; whether the consumer (`NoCorresponding`) needs `U' ∖ U` to be reachable by A3's
  extension is that package's concern (A3 extends at every point of `∂U` it is given).
* Universe: `M : Type u` (the flat model is `LocalModel.{0}`, so the integrator uses `u = 0`).
* Not imported by the scaffold root `CausalScaffold.lean` (kb/0025): registration is the master's.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set Topology Filter TopologicalSpace ChartedSpace Flat Metric

namespace CBG

universe u

variable {d : ℕ}

/-! ### §1 General (moved)

`isCauchySurfaceOn_sup_of_slice`, `extend_of_cauchy_nbhd`, `mem_of_lt_of_mem_closure`,
`mem_of_gt_of_mem_closure`, `mem_of_le_of_mem_interior_Jplus`, `mem_of_ge_of_mem_interior_Jminus`
moved to `CBG/FromModel` on 2026-11-02 (interface round 3), where the generic A4 uses them; names
unchanged. -/

/-! ### §2 Minkowski: diamonds sliced at their equator -/

section Diamond

variable (y : Minkowski d) (ε : ℝ)

theorem isOpen_sliceDiamond :
    IsOpen {r : Minkowski d | ‖r.2 - y.2‖ < r.1 - (y.1 - ε) ∧ ‖r.2 - y.2‖ < y.1 + ε - r.1} := by
  rw [setOf_and]
  exact (isOpen_lt (by fun_prop) (by fun_prop)).inter (isOpen_lt (by fun_prop) (by fun_prop))

/-- **The open diamond** `I⁺(y − ε e₀) ∩ I⁻(y + ε e₀)` of Minkowski space, written out (the same
set as `Flat/CBG`'s `mdiamond`, which this module may not import). -/
def sliceDiamond : Opens (Minkowski d) :=
  ⟨{r | ‖r.2 - y.2‖ < r.1 - (y.1 - ε) ∧ ‖r.2 - y.2‖ < y.1 + ε - r.1}, isOpen_sliceDiamond y ε⟩

variable {y ε}

theorem mem_sliceDiamond {r : Minkowski d} :
    r ∈ sliceDiamond y ε ↔ ‖r.2 - y.2‖ < r.1 - (y.1 - ε) ∧ ‖r.2 - y.2‖ < y.1 + ε - r.1 := Iff.rfl

/-- A Cauchy surface of `W` may be changed outside `W`. -/
theorem isCauchySurfaceOn_congr' {M : Type*} [TopologicalSpace M] {C : Causality M}
    {W : Opens M} {S S' : Set M} (h : C.IsCauchySurfaceOn W S) (hS : ∀ x ∈ W, x ∈ S ↔ x ∈ S') :
    C.IsCauchySurfaceOn W S' := by
  intro I c hc
  obtain ⟨x, ⟨hxI, hxS⟩, hu⟩ := h I c hc
  have hW : ∀ y ∈ c '' I, y ∈ W := by rintro _ ⟨t, ht, rfl⟩; exact hc.1.mem ht
  exact ⟨x, ⟨hxI, (hS x (hW x hxI)).1 hxS⟩,
    fun y ⟨hyI, hyS⟩ => hu y ⟨hyI, (hS y (hW y hyI)).2 hyS⟩⟩

/-- **The equatorial slice `t = c` is a Cauchy surface of the diamond centred at time `c`**
(`isCauchySurfaceOn_graph_of_saturated`, `Flat/LipschitzGraph`, for the constant graph). -/
theorem isCauchySurfaceOn_sliceDiamond (c : ℝ) (x₀ : EuclideanSpace ℝ (Fin d)) (ρ : ℝ) :
    (minkowski d).IsCauchySurfaceOn (sliceDiamond (c, x₀) ρ)
      (graph fun _ : EuclideanSpace ℝ (Fin d) => c) := by
  have hf : IsStrictContraction fun _ : EuclideanSpace ℝ (Fin d) => c := by
    intro x y hxy
    simpa using sub_ne_zero.2 hxy
  refine isCauchySurfaceOn_graph_of_saturated hf ?_ ?_ ?_
  · intro z _ v hv hv0
    have hn := isFutureCausal_iff_norm_le.1 hv
    have hv1 : 0 < v.1 := by
      rcases (norm_nonneg v.2).trans hn |>.lt_or_eq with h | h
      · exact h
      · exfalso
        have h2 : v.2 = 0 := norm_eq_zero.1 (le_antisymm (h ▸ hn) (norm_nonneg _))
        exact hv0 (Prod.ext h.symm h2)
    refine ⟨(c - z.1) / v.1, ?_⟩
    show (z + ((c - z.1) / v.1) • v).1 = c
    rw [Prod.fst_add, Prod.smul_fst, smul_eq_mul, div_mul_cancel₀ _ hv1.ne']
    ring
  · intro z hz q hqz hq
    rw [minkowski_le_top_iff] at hqz
    rw [timeSub_apply] at hq
    rw [mem_sliceDiamond] at hz ⊢
    simp only at hz ⊢
    have h1 := norm_sub_le_norm_sub_add_norm_sub q.2 z.2 x₀
    rw [norm_sub_rev q.2 z.2] at h1
    constructor <;> linarith [hz.1, hz.2]
  · intro z hz q hzq hq
    rw [minkowski_le_top_iff] at hzq
    rw [timeSub_apply] at hq
    rw [mem_sliceDiamond] at hz ⊢
    simp only at hz ⊢
    have h1 := norm_sub_le_norm_sub_add_norm_sub q.2 z.2 x₀
    constructor <;> linarith [hz.1, hz.2]

end Diamond

/-! ### §3 The chart: a sliced neighbourhood of `p` whose slice lies in `U` -/

section Chart

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Minkowski d) M]
  [HasGroupoid M (gxGroupoid (isom d) (Minkowski d))]

/-- **A chart is an abstract `𝕄≥0`-morphism on its source** (the proof of `Flat/Cla/LocallyCauchy`'s
`isEMorphismOn_chartSource`, not imported here). -/
theorem flatChart_isEMorphismOn {e : OpenPartialHomeomorph M (Minkowski d)}
    (hiso : ChartIso (flatCausality d M) (minkowski d) e) :
    IsEMorphismOn (flatCausality d M) (minkowski d) (chartSource e) e := by
  have himg : ∀ V : Opens M, V ≤ chartSource e → ((chartImage e V : Opens _) : Set _) = e '' V :=
    fun V hV => coe_chartImage_of_le hV
  have hsub : ∀ (V : Opens M) (U : Opens (Minkowski d)), V ≤ chartSource e → MapsTo e V U →
      chartImage e V ≤ U := fun V U hV hmaps p hp => by
    rw [← SetLike.mem_coe, himg V hV] at hp
    obtain ⟨z, hz, rfl⟩ := hp
    exact hmaps hz
  exact
  { continuousOn := e.continuousOn
    isOpen_image := fun V hV => by rw [← himg V hV]; exact (chartImage e V).isOpen
    map_le := fun V U hV hmaps y z hyz =>
      (minkowski d).le_mono (hsub V U hV hmaps)
        (((hiso V hV y ((flatCausality d M).le_mem_left hyz) z
          ((flatCausality d M).le_mem_right hyz)).1).1 hyz)
    map_lt := fun V U hV hmaps y z hyz =>
      (minkowski d).lt_mono (hsub V U hV hmaps)
        (((hiso V hV y ((flatCausality d M).lt_mem_left hyz) z
          ((flatCausality d M).lt_mem_right hyz)).2).1 hyz)
    locally := fun z hz => ⟨chartSource e, le_rfl, hz, e.injOn, fun V' hV' U hU y hy w hw => by
      have hU' : chartImage e V' = U := SetLike.coe_injective (by rw [himg V' hV', hU])
      rw [← hU']; exact hiso V' hV' y hy w hw⟩ }

/-- **The sliced neighbourhood** (the flat core of A4). Let `s = ±1`, `P ∈ 𝓝 p` and suppose every
`z ∈ P`, `z ≠ p`, causally below `p` (if `s = 1`) or above `p` (if `s = −1`), lies in `U`. Then for
every `O ∈ 𝓝 p` there are an open `N ∋ p`, `N ⊆ O`, and a Cauchy surface `Γ` of `N` with
`Γ ⊆ U`: in the chart `e` at `p`, `y₀ = e p`, `N` is the diamond of radius `ρ = δ + ε'` centred at
`(y₀.t − sδ, y₀.x)` and `Γ` its equatorial slice, inside `U` because the closed slice ball of
radius `δ` lies on the cone of `y₀` and an open neighbourhood of a compact ball contains a larger
ball (`thickening_closedBall`). -/
theorem flat_exists_cauchy_nbhd (U : Opens M) {p : M} {O : Set M} (hO : O ∈ 𝓝 p) {s : ℝ}
    (hs : s = 1 ∨ s = -1) {P : Set M} (hP : P ∈ 𝓝 p)
    (hR : ∀ z ∈ P, z ≠ p → (s = 1 → (flatCausality d M).le ⊤ z p) →
      (s = -1 → (flatCausality d M).le ⊤ p z) → z ∈ U) :
    ∃ (N : Opens M) (Γ : Set M), (flatCausality d M).IsCauchySurfaceOn N Γ ∧ Γ ⊆ U ∧ p ∈ N ∧
      (N : Set M) ⊆ O := by
  set e := chartAt (Minkowski d) p with he
  have hiso : ChartIso (flatCausality d M) (minkowski d) e := flatCausality_chartIso_chartAt p
  have hps : p ∈ e.source := mem_chart_source _ p
  let W₀ : Opens M := ⟨interior (O ∩ P) ∩ e.source, isOpen_interior.inter e.open_source⟩
  have hpW₀ : p ∈ W₀ := ⟨mem_interior_iff_mem_nhds.2 (inter_mem hO hP), hps⟩
  have hW₀e : W₀ ≤ chartSource e := fun z hz => hz.2
  set y₀ := e p with hy₀
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 (chartImage e W₀).isOpen y₀
    (mem_chartImage_of_mem hps hpW₀)
  set δ := r / 4 with hδ
  have hδ0 : 0 < δ := by positivity
  have hs0 : |s| = 1 := by rcases hs with rfl | rfl <;> norm_num
  set t₀ := y₀.1 - s * δ with ht₀
  -- the chart image of `W₀` contains the ball of radius `r`, and the points of the slice ball
  have hballW : ∀ w : Minkowski d, dist w y₀ < r → ∃ z, z ∈ e.source ∧ z ∈ W₀ ∧ e z = w ∧
      e.symm w = z := fun w hw => exists_of_mem_chartImage (hball hw)
  -- the closed slice ball lies in `U`
  have hrel : ∀ x : EuclideanSpace ℝ (Fin d), ‖x - y₀.2‖ ≤ δ →
      ∃ z, z ∈ e.source ∧ z ∈ W₀ ∧ z ∈ U ∧ e z = (t₀, x) := by
    intro x hx
    have hdist : dist ((t₀, x) : Minkowski d) y₀ ≤ δ := by
      rw [Prod.dist_eq, Real.dist_eq, dist_eq_norm]
      refine max_le ?_ hx
      rw [ht₀, show y₀.1 - s * δ - y₀.1 = -(s * δ) by ring, abs_neg, abs_mul, hs0,
        abs_of_pos hδ0, one_mul]
    obtain ⟨z, hz, hzW, hez, hsymm⟩ := hballW (t₀, x) (by linarith)
    refine ⟨z, hz, hzW, ?_, hez⟩
    have hzP : z ∈ P := (interior_subset hzW.1).2
    have hne : z ≠ p := by
      rintro rfl
      have h1 : (t₀, x).1 = y₀.1 := by rw [← hez]
      simp only at h1
      rw [ht₀] at h1
      have : s * δ = 0 := by linarith
      rcases mul_eq_zero.1 this with h | h
      · rcases hs with rfl | rfl <;> norm_num at h
      · exact hδ0.ne' h
    -- the Minkowski relation in a ball inside the chart image of `W₀`
    have hkey : ∀ w : Minkowski d, dist w y₀ < 3 * δ → w ∈ chartImage e W₀ := fun w hw =>
      hball (by rw [mem_ball]; linarith)
    refine hR z hzP hne (fun h1 => ?_) (fun h1 => ?_)
    · subst h1
      refine (flatCausality d M).le_mono le_top ((hiso W₀ hW₀e z hzW p hpW₀).1.2 ?_)
      rw [hez]
      refine staticCausality.le_iff.2 (staticLe_of_ball (ρ := 2 * δ) (fun w hw => hkey w
        ((dist_triangle w _ y₀).trans_lt (by linarith))) ?_ ?_ ?_)
      · show t₀ ≤ y₀.1
        rw [ht₀]; linarith
      · show dist x y₀.2 ≤ y₀.1 - t₀
        rw [ht₀, dist_eq_norm]; linarith
      · show y₀.1 - t₀ < 2 * δ
        rw [ht₀]; linarith
    · subst h1
      refine (flatCausality d M).le_mono le_top ((hiso W₀ hW₀e p hpW₀ z hzW).1.2 ?_)
      rw [hez]
      refine staticCausality.le_iff.2 (staticLe_of_ball (ρ := 2 * δ) (fun w hw => hkey w
        (by linarith)) ?_ ?_ ?_)
      · show y₀.1 ≤ t₀
        rw [ht₀]; linarith
      · show dist y₀.2 x ≤ t₀ - y₀.1
        rw [ht₀, dist_comm, dist_eq_norm]; linarith
      · show t₀ - y₀.1 < 2 * δ
        rw [ht₀]; linarith
  -- the open set `T` of chart points of `W₀ ∩ U`, and its slice
  let T : Opens (Minkowski d) := chartImage e (W₀ ⊓ U)
  let f : EuclideanSpace ℝ (Fin d) → Minkowski d := fun x => (t₀, x)
  have hf : Continuous f := by fun_prop
  have hT' : IsOpen (f ⁻¹' T) := T.isOpen.preimage hf
  have hKT : closedBall y₀.2 δ ⊆ f ⁻¹' T := by
    intro x hx
    obtain ⟨z, hz, hzW, hzU, hez⟩ := hrel x (by rwa [mem_closedBall, dist_eq_norm] at hx)
    exact ⟨z, ⟨hz, hzW, hzU⟩, hez⟩
  obtain ⟨ε, hε, hεT⟩ := (isCompact_closedBall y₀.2 δ).exists_thickening_subset_open hT' hKT
  rw [thickening_closedBall hε hδ0.le] at hεT
  set ε' := min (ε / 2) δ with hε'
  have hε'0 : 0 < ε' := lt_min (by positivity) hδ0
  have hε'ε : ε' < ε := (min_le_left _ _).trans_lt (by linarith)
  have hε'δ : ε' ≤ δ := min_le_right _ _
  set ρ := δ + ε' with hρ
  set Nd : Opens (Minkowski d) := sliceDiamond (t₀, y₀.2) ρ with hNd
  -- the diamond lies in the ball of radius `r`
  have hNdball : ∀ w ∈ Nd, dist w y₀ < r := by
    intro w hw
    rw [mem_sliceDiamond] at hw
    simp only at hw
    have h0 := norm_nonneg (w.2 - y₀.2)
    have hst : |s * δ| = δ := by rw [abs_mul, hs0, abs_of_pos hδ0, one_mul]
    have h1 := neg_abs_le (s * δ)
    have h2 := le_abs_self (s * δ)
    rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, dist_eq_norm, abs_lt]
    rw [ht₀] at hw
    refine ⟨⟨by linarith [hw.1, hw.2], by linarith [hw.1, hw.2]⟩, by linarith [hw.1, hw.2]⟩
  have hNdT : ∀ w ∈ Nd, ∃ z, z ∈ e.source ∧ z ∈ W₀ ∧ e z = w ∧ e.symm w = z :=
    fun w hw => hballW w (hNdball w hw)
  let N : Opens M := ⟨e.source ∩ e ⁻¹' Nd, e.continuousOn.isOpen_inter_preimage e.open_source
    Nd.isOpen⟩
  have hNe : N ≤ chartSource e := fun z hz => hz.1
  have hNimg : ((Nd : Opens (Minkowski d)) : Set (Minkowski d)) = e '' N := by
    ext w
    constructor
    · intro hw
      obtain ⟨z, hz, -, hez, -⟩ := hNdT w hw
      exact ⟨z, ⟨hz, by show e z ∈ Nd; rw [hez]; exact hw⟩, hez⟩
    · rintro ⟨z, hz, rfl⟩
      exact hz.2
  set Γ : Set M := N ∩ e ⁻¹' (graph fun _ : EuclideanSpace ℝ (Fin d) => t₀) with hΓ
  have hΓN : Γ ⊆ N := inter_subset_left
  have hΓimg : e '' Γ = (Nd : Set (Minkowski d)) ∩ graph fun _ : EuclideanSpace ℝ (Fin d) => t₀ := by
    ext w
    constructor
    · rintro ⟨z, ⟨hzN, hzg⟩, rfl⟩
      exact ⟨hzN.2, hzg⟩
    · rintro ⟨hw, hwg⟩
      obtain ⟨z, hz, -, hez, -⟩ := hNdT w hw
      exact ⟨z, ⟨⟨hz, by show e z ∈ Nd; rw [hez]; exact hw⟩, by
        rw [mem_preimage, hez]; exact hwg⟩, hez⟩
  refine ⟨N, Γ, ?_, ?_, ⟨hps, ?_⟩, ?_⟩
  · -- `Γ` is a Cauchy surface of `N`, through the chart
    refine ((flatChart_isEMorphismOn hiso).isCauchySurfaceOn_image_iff e.injOn hNe hNimg hΓN).2 ?_
    rw [hΓimg]
    exact isCauchySurfaceOn_congr' (isCauchySurfaceOn_sliceDiamond t₀ y₀.2 ρ)
      fun w hw => ⟨fun h => ⟨hw, h⟩, fun h => h.2⟩
  · -- `Γ ⊆ U`
    rintro z ⟨⟨hz, hzNd⟩, hzg⟩
    have hzNd' : e z ∈ Nd := hzNd
    have hzg' : (e z).1 = t₀ := hzg
    rw [mem_sliceDiamond] at hzNd'
    simp only at hzNd'
    have hx : (e z).2 ∈ f ⁻¹' T := hεT (by
      rw [mem_ball, dist_eq_norm, add_comm]
      have := hzNd'.1
      rw [hzg'] at this
      linarith)
    obtain ⟨z', ⟨hz', -, hz'U⟩, hez'⟩ := hx
    have hfz : f (e z).2 = e z := Prod.ext hzg'.symm rfl
    rw [hfz] at hez'
    rw [← e.injOn hz' hz hez']
    exact hz'U
  · -- `p ∈ N`
    show y₀ ∈ Nd
    rw [mem_sliceDiamond]
    simp only [sub_self, norm_zero]
    rw [ht₀]
    rcases hs with rfl | rfl <;> constructor <;> linarith
  · -- `N ⊆ O`
    rintro z ⟨hz, hzNd⟩
    obtain ⟨z', hz', hz'W, hez', -⟩ := hNdT (e z) hzNd
    rw [← e.injOn hz' hz hez']
    exact (interior_subset hz'W.1).1

end Chart

/-! ### §4 A4 for flat spacetimes -/

section Slices

variable {M : Type u} [TopologicalSpace M] [T2Space M] [ConnectedSpace M]
  [ChartedSpace (Minkowski d) M] [HasGroupoid M (gxGroupoid (isom d) (Minkowski d))]

/-- **A4, future side, for flat spacetimes** (`LocalModel.SliceFuture` read on `flatCausality`;
Sbierski Thm 3.6, geometric half). -/
theorem flat_slice_future (U : Opens M) (S : Set M)
    (hGH : (flatCausality d M).GloballyHyperbolic)
    (_hGHU : (flatCausality d M).GloballyHyperbolicOn U) (hSU : S ⊆ U)
    (hS : (flatCausality d M).IsCauchySurface S) (hSU' : (flatCausality d M).IsCauchySurfaceOn U S)
    (p : M) (hp : p ∈ frontier (U : Set M)) (hpS : p ∈ (flatCausality d M).Jplus ⊤ S)
    (hcorner : (flatCausality d M).Jminus ⊤ {p} ∩ frontier (U : Set M) ∩
      (flatCausality d M).Jplus ⊤ S = {p})
    (O : Opens M) (hpO : p ∈ O) :
    ∃ U' : Opens M, U < U' ∧ (U' : Set M) ⊆ U ∪ O ∧
      (flatCausality d M).GloballyHyperbolicOn U' ∧ (flatCausality d M).IsCauchySurfaceOn U' S := by
  haveI : SecondCountableTopology M := flat_secondCountableTopology (d := d) M
  set C := flatCausality d M
  have harc : C.CausallyArcConnected := flatCausality_causallyArcConnected d M
  obtain ⟨φ, hφ, -⟩ := (flat_hasChronalCausalFlow : C.HasChronalCausalFlow)
  have hext : C.CurvesExtend := curvesExtend_of_isCausalFlow hφ
  have hac : C.IsAcausal S := hS.isAcausal harc hext
  obtain ⟨ψ, hψ⟩ := flat_exists_isCauchySplitting flat_hasChronalCausalFlow hGH.1 hS hac
  obtain ⟨-, -, -, -, -, hJnhds⟩ := Causality.sigma_separe hGH.1 hac hψ
  have hpU : p ∉ U := fun h => hp.2 (by rwa [U.isOpen.interior_eq])
  have hpcl : p ∈ closure (U : Set M) := hp.1
  have hpJ : interior (C.Jplus ⊤ S) ∈ 𝓝 p :=
    interior_mem_nhds.2 (hJnhds p ⟨hpS, fun h => hpU (hSU h)⟩)
  have hconv : C.CausallyConvexIn (U : Set M) ⊤ :=
    Causality.causallyConvexIn_of_isCauchySurfaceOn hGH.1 harc hext le_top hSU hSU' hS
  let N₀ : FlatSpacetime.{u} d := FlatSpacetime.of M
  have hpush : C.PushUp := flatCausality_pushUp (N := N₀)
  have hZ : ∀ z : M, z ∈ C.Zminus := fun z => flatCausality_mem_Zminus (N := N₀) z
  obtain ⟨N, Γ, hN, hΓ, hpN, hNO⟩ := flat_exists_cauchy_nbhd U (O.isOpen.mem_nhds hpO)
    (Or.inl rfl) hpJ fun z hz hne h1 _ =>
      mem_of_le_of_mem_interior_Jplus hconv hSU hpcl hpush hZ hcorner hz (h1 rfl) hne
  exact extend_of_cauchy_nbhd hGH harc hext hSU hS hSU' hN hΓ hpN hpU hNO

/-- **A4, past side, for flat spacetimes** (`LocalModel.SlicePast` read on `flatCausality`; no
time reversal, gx D-12(e): the slice is taken above `p`). -/
theorem flat_slice_past (U : Opens M) (S : Set M)
    (hGH : (flatCausality d M).GloballyHyperbolic)
    (_hGHU : (flatCausality d M).GloballyHyperbolicOn U) (hSU : S ⊆ U)
    (hS : (flatCausality d M).IsCauchySurface S) (hSU' : (flatCausality d M).IsCauchySurfaceOn U S)
    (p : M) (hp : p ∈ frontier (U : Set M)) (hpS : p ∈ (flatCausality d M).Jminus ⊤ S)
    (hcorner : (flatCausality d M).Jplus ⊤ {p} ∩ frontier (U : Set M) ∩
      (flatCausality d M).Jminus ⊤ S = {p})
    (O : Opens M) (hpO : p ∈ O) :
    ∃ U' : Opens M, U < U' ∧ (U' : Set M) ⊆ U ∪ O ∧
      (flatCausality d M).GloballyHyperbolicOn U' ∧ (flatCausality d M).IsCauchySurfaceOn U' S := by
  haveI : SecondCountableTopology M := flat_secondCountableTopology (d := d) M
  set C := flatCausality d M
  have harc : C.CausallyArcConnected := flatCausality_causallyArcConnected d M
  obtain ⟨φ, hφ, -⟩ := (flat_hasChronalCausalFlow : C.HasChronalCausalFlow)
  have hext : C.CurvesExtend := curvesExtend_of_isCausalFlow hφ
  have hac : C.IsAcausal S := hS.isAcausal harc hext
  obtain ⟨ψ, hψ⟩ := flat_exists_isCauchySplitting flat_hasChronalCausalFlow hGH.1 hS hac
  -- `J⁻(S) ∖ S` is open: its complement is `J⁺(S)`, closed (the two cover `M`)
  obtain ⟨hJp, hJm, hJpc, -, hJint, -⟩ := Causality.sigma_separe hGH.1 hac hψ
  have hpU : p ∉ U := fun h => hp.2 (by rwa [U.isOpen.interior_eq])
  have hpcl : p ∈ closure (U : Set M) := hp.1
  have hcov : ∀ m : M, m ∈ C.Jplus ⊤ S ∨ m ∈ C.Jminus ⊤ S := by
    intro m
    rw [hJp, hJm]
    rcases le_total 0 (ψ.symm m).2 with h | h
    · exact Or.inl ⟨ψ.symm m, ⟨trivial, h⟩, ψ.apply_symm_apply m⟩
    · exact Or.inr ⟨ψ.symm m, ⟨trivial, h⟩, ψ.apply_symm_apply m⟩
  have hpJp : p ∉ C.Jplus ⊤ S := fun h => hpU (hSU (hJint ▸ ⟨h, hpS⟩))
  have hpJ : interior (C.Jminus ⊤ S) ∈ 𝓝 p := by
    refine interior_mem_nhds.2 (Filter.mem_of_superset (hJpc.isOpen_compl.mem_nhds hpJp) ?_)
    intro m hm
    exact (hcov m).resolve_left hm
  have hconv : C.CausallyConvexIn (U : Set M) ⊤ :=
    Causality.causallyConvexIn_of_isCauchySurfaceOn hGH.1 harc hext le_top hSU hSU' hS
  let N₀ : FlatSpacetime.{u} d := FlatSpacetime.of M
  have hpush : C.PushUp := flatCausality_pushUp (N := N₀)
  have hZ : ∀ z : M, z ∈ C.Zplus := fun z => flatCausality_mem_Zplus (N := N₀) z
  obtain ⟨N, Γ, hN, hΓ, hpN, hNO⟩ := flat_exists_cauchy_nbhd U (O.isOpen.mem_nhds hpO)
    (Or.inr rfl) hpJ fun z hz hne _ h2 =>
      mem_of_ge_of_mem_interior_Jminus hconv hSU hpcl hpush hZ hcorner hz (h2 rfl) hne
  exact extend_of_cauchy_nbhd hGH harc hext hSU hS hSU' hN hΓ hpN hpU hNO

end Slices

end CBG

end Causal
