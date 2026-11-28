import Causal.ErsMughd
import Causal.ErsUniqueness
import Causal.ErsWitnesses
import Causal.MaximalZorn

/-!
# ERS19 Theorem 4.82 over a solution predicate: the restart is geometric

Programme target `T-abs-ers-4-82-solution-form` (`programme/roadmap.toml`; layer 1: ETT-layer
imports only, no model, no metric). Source: Eperon–Reall–Sbierski, arXiv 1802.03020,
`papers/ers-predictability` (`legacy/labeled/ghd_02_19.tex`). Theorem 4.82 over the developments
of an abstract initial value problem `sol`, `cau`, as Theorems 4.79 and 4.80 are
(`Causal.ErsMughd`), its restart a `slice_restart` whose conclusion is geometric (an open set
across which the glued solution has `S` as Cauchy surface), not "a strictly larger development".
**No label is marked**:

* `ersthm:ThmNotBlocking` — `ghd_02_19.tex:1100` (proof 1114–1139). Forms of record: the
  uniform ones, whose restart is asked of every pair of developments and names no maximal
  development, `ers_theorem_4_82_solution_of_restarts` (each development globally hyperbolic and
  tarentin) and `ers_theorem_4_82_solution_of_restarts_isCausal` (`is_causal` on each); the restart
  step at any development `ers_theorem_4_82_restart`; its witness at the non-maximal
  `]-1/2, 1/2[` in `]-1, 1[` (`Causal.Ers482Witness`). The paper's shape, the restart of the
  maximal `U₁` alone: `ers_theorem_4_82_solution` (every development lies in the maximal one and
  agrees with it there), `_unique` (the unique MGHD), `_of_globallyHyperbolicOn`,
  `_of_ers_theorem_4_64` and `_secondCountable` (the agreement on `A` derived, Remark 4.67's
  variation); given the rest its `hstep` is equivalent to its conclusion
  (`ers_theorem_4_82_solution_hstep_iff`, `_hstep_of_le`).

> Let S ⊆ R^{d+1} be a connected hypersurface of R^{d+1}. (`ghd_02_19.tex:814`)

> Recall that a GHD u1 : U1 → R of given initial data posed on a hypersurface S is called a
> maximal globally hyperbolic development (MGHD) iff there does not exist a GHD u2 : U2 → R of
> the same initial data with U1 ⊊ U2. Note that by Theorem 4.64 any such GHD u2 : U2 → R would
> agree with u1 on U1, and thus it would correspond to an extension of u1 : U1 → R. In other
> words, a MGHD is a GHD that cannot be extended as a GHD. (`:1094`)

> Theorem 4.82. Let u1 : U1 → R be a MGHD of given initial data for a quasilinear wave equation
> of the form (4.61) and assume that (4.83) for every p ∈ (∂U1 ∖ ∂S) there exists a
> neighbourhood V of p together with a chart ψ : V → (−ε, ε)^{d+1}, ε > 0, and a continuous
> function f : (−ε, ε)^d → (−ε, ε) such that ψ^{−1}(graph f) = ∂U1 ∩ V, all points below graph f
> in (−ε, ε)^{d+1} are mapped into U1 and all points above graph f in (−ε, ε)^{d+1} are mapped
> into R^{d+1} ∖ U1. Then u1 : U1 → R is the unique MGHD, i.e., any other GHD u : U → R
> satisfies U ⊆ U1 and thus also u1|U = u. (`:1101–1106`)

> A slight variation of Remark 4.67 shows that the set A is the MCGHD of u1 : U1 → R and
> u2 : U2 → R. (`:1128`) […] We consider now the domain of dependence DΣV of ΣV in V ⊆ U2.
> Clearly, DΣV contains points that lie above the graph of f in the chart ψ. We can now define
> u3 : U3 → R, U3 := U1 ∪ DΣV, u3(x) := u1(x) for x ∈ U1 and u3(x) := u2(x) for x ∈ DΣV. This
> is well defined since the region below the graph of f in the chart ψ lies in A, where u1 and
> u2 agree. It is easy to see that u3 : U3 → R is a GHD the domain of which contains that of the
> MGHD u1 : U1 → R. This is a contradiction. (`:1138`)

## The reading

* **The equation is abstract**, as in `Causal.ErsMughd`: `sol U u` ("`u` solves (4.61) on `U`
  with the data on `S`") with `SolutionLocal`, `SolutionsGlue` and, new here,
  `SolutionRestricts` (a solution on `U` solves on every open `V ⊆ U`: ERS's `u₃` solves on
  `DΣ_V` because `u₂` does on `U₂ ⊇ DΣ_V`); `cau u` the causality of `g(u, du)`.
  `CausalityFollows` is not used: the restart names the glued solution's causality itself.
* **A GHD** is `IsDevelopment` (`S` Cauchy for `cau u`, GH not asked: DEC-162, OQ-57 (c)). **The
  MGHD** is `IsMaximalDevelopment` (`Causal.MaximalZorn`, ERS l. 117: no development *extending*
  it has a larger domain). l. 1094 (no development with a larger domain, agreeing or not) implies
  it; it is formally weaker only in the abstract reading, where Thm 4.64 is not available, and
  ERS identify the two at `:1094` through Thm 4.64. ERS's `u₃` extends `u₁`, so the proof uses
  l. 117 only.
* **`A`** is the component of `U₁ ∩ U₂` through a point `s₀ ∈ S`, and **`u₃`** is
  `glueSolutions U₁ u₁ u₂` (`u₁` on `U₁`, `u₂` off it), which is `u₂` on `O` when
  `O ∩ U₁ ⊆ A` and `u₁ = u₂` on `A` (`hagree`, Remark 4.67's variation).
* **The restart** keeps its id, `slice_restart` (`Causal.Causality.SliceRestart (cau u₂) U₂ S A
  U₂ Q`, DEC-162), with the new conclusion `Q = GluedRestartAt cau S U₁ U₂ u₁ u₂ A`: for every
  neighbourhood `V ⊆ U₂` of `p` with `V ∩ U₁ ⊆ A`, an open `O ⊆ V`, not inside `U₁`, with `S` a
  Cauchy surface of `U₁ ∪ O` for `cau u₃`. "Not inside `U₁`" is ERS's "DΣ_V contains points that
  lie above the graph of f"; the form "`p ∈ O`" implies it (`GluedRestartAt.of_mem`,
  `sliceRestart_gluedRestartAt_of_mem`), so the hypothesis taken is the weaker one.
* **(4.83)** is `one_sided_boundary`, `Causal.Causality.OneSidedBoundary U₁ (closure S)`, its
  topological content (DEC-166 (b)); the chart condition gives it (`Causal.BoundaryGraph`).

## Hypothesis checklist

| paper | here |
|---|---|
| (4.61), the same initial data | ⚠ abstract: `sol` with `SolutionLocal`, `SolutionsGlue`, `SolutionRestricts` (⚠ new, the equation is local); `cau` |
| `u₁` a MGHD (l. 1094) | ⚠ weakened: `IsMaximalDevelopment` (l. 117), formally weaker in the abstract reading (ERS identify the two at `:1094` through Thm 4.64), read with `IsDevelopment` (DEC-162) |
| (4.83) | ⚠ named, through its topological content: `one_sided_boundary` (DEC-166 (b)) |
| `S` connected (§4's standing hypothesis, `:814`) | ⚠ weakened: `s₀ ∈ S`; `IsPreconnected S` in `_secondCountable` only |
| each GHD globally hyperbolic | ⚠ named on each development, as `ers_theorem_4_82_of_sliceRestart`: `hconn`, `hcaus` (`is_causal` on `U`), `hsplit`, `hJm`, `hJp`, `hK`, `hSclosed`; `hG`, `hT` (`globally_hyperbolic`, `tarentin` on `U`) for `hcaus`, `hJm`, `hJp`; `hconn`, `hsplit` from `S` Cauchy on a second countable `M` |
| (4.84) | ✓ proved (`Causality.frontier_connectedComponentIn_inter`) |
| Remark 4.67's variation, `u₁ = u₂` on `A` | ⚠ named `hagree`; derived from Thm 4.64 for `U₁` and `A` (its `hlocal`, `hstay`, `hstep`) in `_of_ers_theorem_4_64` (with `hacausal`) and `_secondCountable` |
| (4.85), "analogous to Step 2" | ✓ proved in `U₂` for `g(u₂)` (`Causality.exists_spacelike_boundary_point`), no null geodesic |
| Steps 3–4, `Σ`, `DΣ_V` above the graph, `U₃` Cauchy | ⚠ named: `slice_restart`, `Q = GluedRestartAt` (`hstep`) |
| "well defined", "`u₃` … a GHD" (solving), "a contradiction" | ✓ proved |
| "`U ⊆ U₁` and thus also `u₁|_U = u`", "the unique MGHD" | ✓ both (`_unique`) |

## SCOPE (disclosed)

* **No label is marked**: the equation is abstract, the restart, (4.83)'s topological content,
  the GH side conditions and the agreement (or Thm 4.64's restart hypotheses) are named, and a
  GHD is read "`S` Cauchy". No `sorry` in this file.
* **The paper's shape and the forms of record.** At the maximal development any restart located
  on `∂A ∩ U₂` is vacuous once the conclusion holds (`A = U₂`): given the rest, the fixed-`U₁`
  `hstep` of `ers_theorem_4_82_solution` (the paper's shape) is equivalent to the conclusion
  (`ers_theorem_4_82_solution_hstep_iff`), as for the old form (`ers_theorem_4_82_hstep_iff`).
  `Q` names no maximality, so the restart is a statement about every pair of developments. What
  has content is the restart step at non-maximal pairs (`ers_theorem_4_82_restart`), exercised by
  the witness. The uniform forms `_of_restarts`, `_of_restarts_isCausal` ask the restart of every
  pair, a hypothesis that names no maximal development and is exercised at non-maximal pairs. As
  theorems they are the fixed-`U₁` forms specialised at `U₀ = U₁`, so logically weaker. That the
  conclusion does not imply their hypothesis is argued, not proved here; per pair, the witness
  has the restart holding at `(]-1/2, 1/2[, ]-1, 1[)` while `]-1, 1[ ⊄ ]-1/2, 1/2[`. The old `Q`
  ("`∃ j, dom i₁ < dom j`") holds at a non-maximal base with `j = i₁` and no geometry.
* **Witness** (kb/0011), `Causal.Ers482Witness`: on the timelike line, `S = {0}`, solutions `id`
  on open subsets of `]-1, 1[` (`sol82`). At the non-maximal `]-1/2, 1/2[` against `]-1, 1[`, the
  restart's premise is met at `±1/2` (`restart_exercised`), `Q` is proved (`]p - ε, p + ε[`), and
  the restart step gives a strictly larger development (`timelikeLine_ers_theorem_4_82_restart`);
  the uniform restart holds at every pair (`restarts82`); every form is instantiated at the
  maximal `]-1, 1[`. One causality and one solution: no witness separates `g(u₁)` from `g(u₂)`.
* **Layer 3 stays with the suppliers**: `τ_q`, `Σ` (O'Neill 5.3, 14.46), `DΣ_V` and the Cauchy
  property of `U₁ ∪ DΣ_V` for `g(u₃)` are `slice_restart`'s (T-loc-quasilinear-slice); the chart
  of (4.83) is `one_sided_boundary`'s (Lemma 4.86, T-loc-quasilinear-one-sided).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Function

universe u v

/-! ## 1. Restriction, the glued solution, the geometric restart -/

section Restart

variable {M : Type u} [TopologicalSpace M] {β : Type v}

/-- **Solutions restrict**: a function solving on `U` solves on every open `V ≤ U`. The third
locality property of (4.61), beside `SolutionLocal` and `SolutionsGlue`. Supplier: (4.61) and its
initial condition on `S ∩ U` restrict to open subsets (layer 3, trivially). ERS use it for
"`u₃` is a GHD" (`ghd_02_19.tex:1138`): `u₂` solves on `DΣ_V ⊆ U₂`. -/
def SolutionRestricts (sol : Opens M → (M → β) → Prop) : Prop :=
  ∀ ⦃U V : Opens M⦄ ⦃u : M → β⦄, V ≤ U → sol U u → sol V u

open Classical in
/-- **The glued function** (ERS's `u₃`, `ghd_02_19.tex:1138`): `u₁` on `U₁`, `u₂` off it. -/
noncomputable def glueSolutions (U₁ : Opens M) (u₁ u₂ : M → β) : M → β :=
  fun x => if x ∈ U₁ then u₁ x else u₂ x

/-- The glued function is `u₁` on `U₁`. -/
theorem eqOn_glueSolutions_left (U₁ : Opens M) (u₁ u₂ : M → β) :
    EqOn (glueSolutions U₁ u₁ u₂) u₁ U₁ := fun x hx => by
  classical
  simp only [glueSolutions]
  exact if_pos hx

/-- The glued function is `u₂` on `O` when `u₁ = u₂` on `O ∩ U₁` ("This is well defined since
the region below the graph of f in the chart ψ lies in A, where u1 and u2 agree"). -/
theorem eqOn_glueSolutions_right {U₁ : Opens M} {u₁ u₂ : M → β} {O : Set M}
    (h : EqOn u₁ u₂ (O ∩ U₁)) : EqOn (glueSolutions U₁ u₁ u₂) u₂ O := fun x hx => by
  classical
  simp only [glueSolutions]
  by_cases hx₁ : x ∈ U₁
  · rw [if_pos hx₁]; exact h ⟨hx, hx₁⟩
  · rw [if_neg hx₁]

/-- **The geometric restart of ERS Thm 4.82 at `p`** (the conclusion `Q` of `slice_restart`
here): for every neighbourhood `V ⊆ U₂` of `p` meeting `U₁` inside `A`, an open `O ⊆ V` not
inside `U₁` such that `S` is a Cauchy surface of `U₁ ∪ O` for the causality of the glued solution
`u₃` (`glueSolutions U₁ u₁ u₂`). It takes the two solutions only through the causality of the
glued solution, and names no solution predicate `sol` and no maximality.

Supplier (layer 3, T-loc-quasilinear-slice), ERS `ghd_02_19.tex:1135–1138`: Steps 3–4 of
Thm 4.64 in `U₂` for `g(u₂)` with `V₀` replaced by `A`, inside a convex neighbourhood in `V`,
give a spacelike `Σ ⊆ closure A ∩ V` through a point `q ∈ ∂A ∩ U₂ ⊆ ∂U₁`; `O = DΣ_{V'}` for a
small `V' ∋ q` (O'Neill 14.46) contains `q ∉ U₁`; `S` is a Cauchy surface of `U₁ ∪ O` for
`g(u₃)` ("It is easy to see that u3 : U3 → R is a GHD"). -/
def GluedRestartAt (cau : (M → β) → Causality M) (S : Set M) (U₁ U₂ : Opens M) (u₁ u₂ : M → β)
    (A : Set M) (p : M) : Prop :=
  ∀ V ∈ 𝓝 p, V ⊆ U₂ → V ∩ U₁ ⊆ A →
    ∃ O : Opens M, (O : Set M) ⊆ V ∧ ¬ O ≤ U₁ ∧
      (cau (glueSolutions U₁ u₁ u₂)).IsCauchySurfaceOn (U₁ ⊔ O) S

/-- **The form with `p ∈ O` implies `GluedRestartAt`** when `p ∉ U₁`: the target's wording ("an
open `O ∋ p` in `V`") is the stronger hypothesis. -/
theorem GluedRestartAt.of_mem {cau : (M → β) → Causality M} {S : Set M} {U₁ U₂ : Opens M}
    {u₁ u₂ : M → β} {A : Set M} {p : M} (hp : p ∉ U₁)
    (h : ∀ V ∈ 𝓝 p, V ⊆ U₂ → V ∩ U₁ ⊆ A → ∃ O : Opens M, p ∈ O ∧ (O : Set M) ⊆ V ∧
      (cau (glueSolutions U₁ u₁ u₂)).IsCauchySurfaceOn (U₁ ⊔ O) S) :
    GluedRestartAt cau S U₁ U₂ u₁ u₂ A p := by
  intro V hV hVU₂ hVA
  obtain ⟨O, hpO, hOV, hO⟩ := h V hV hVU₂ hVA
  exact ⟨O, hOV, fun hle => hp (hle hpO), hO⟩

/-- **A frontier point in `U₂` of the component of `U₁ ∩ U₂` through `s₀` is not in `U₁`**
(the inclusion half of (4.84), without `U₂ ⊄ U₁`): "A point in the boundary of ∂A cannot be
contained in U1 as well as in U2 by definition of A" (`ghd_02_19.tex:1118`). -/
theorem notMem_of_mem_frontier_connectedComponentIn [LocallyConnectedSpace M] {U₁ U₂ : Opens M}
    {s₀ p : M} (hp : p ∈ frontier (connectedComponentIn ((U₁ : Set M) ∩ U₂) s₀))
    (hp₂ : p ∈ U₂) : p ∉ U₁ := by
  intro hp₁
  have hAo : IsOpen (connectedComponentIn ((U₁ : Set M) ∩ U₂) s₀) :=
    (U₁.isOpen.inter U₂.isOpen).connectedComponentIn
  rw [hAo.frontier_eq] at hp
  have hpU : p ∈ (U₁ : Set M) ∩ U₂ := ⟨hp₁, hp₂⟩
  have hBo : IsOpen (connectedComponentIn ((U₁ : Set M) ∩ U₂) p) :=
    (U₁.isOpen.inter U₂.isOpen).connectedComponentIn
  obtain ⟨z, hzB, hzA⟩ := mem_closure_iff.1 hp.1 _ hBo (mem_connectedComponentIn hpU)
  refine hp.2 ?_
  rw [connectedComponentIn_eq hzA, ← connectedComponentIn_eq hzB]
  exact mem_connectedComponentIn hpU

/-- **`slice_restart` with the conclusion "`O ∋ p`" gives it with `GluedRestartAt`**: the restart
taken by the theorems of this file is implied by the target's wording. -/
theorem sliceRestart_gluedRestartAt_of_mem [LocallyConnectedSpace M]
    {cau : (M → β) → Causality M} {S : Set M} {U₁ U₂ : Opens M} {u₁ u₂ : M → β} {s₀ : M}
    (h : (cau u₂).SliceRestart U₂ S (connectedComponentIn ((U₁ : Set M) ∩ U₂) s₀) U₂
      (fun p => ∀ V ∈ 𝓝 p, V ⊆ U₂ → V ∩ U₁ ⊆ connectedComponentIn ((U₁ : Set M) ∩ U₂) s₀ →
        ∃ O : Opens M, p ∈ O ∧ (O : Set M) ⊆ V ∧
          (cau (glueSolutions U₁ u₁ u₂)).IsCauchySurfaceOn (U₁ ⊔ O) S)) :
    (cau u₂).SliceRestart U₂ S (connectedComponentIn ((U₁ : Set M) ∩ U₂) s₀) U₂
      (GluedRestartAt cau S U₁ U₂ u₁ u₂ (connectedComponentIn ((U₁ : Set M) ∩ U₂) s₀)) :=
  fun p hp hsp => GluedRestartAt.of_mem (notMem_of_mem_frontier_connectedComponentIn hp.1 hp.2)
    (h p hp hsp)

variable {sol : Opens M → (M → β) → Prop} {cau : (M → β) → Causality M} {S : Set M}

/-! ## 2. The restart step, at any development -/

/-- **The restart step of ERS Thm 4.82, at any development** (`ersthm:ThmNotBlocking`, unmarked;
`ghd_02_19.tex:1118–1138`): if a development `(U₂, u₂)` is not inside the development `(U₁, u₁)`
(maximal or not), there is an open `O ⊆ U₂` such that the glued solution `u₃` on `U₁ ∪ O` is a
development strictly larger than `U₁`, extending `u₁`, equal to `u₂` on `O`.

(4.84) by `frontier_connectedComponentIn_inter`; (4.85) by `exists_spacelike_boundary_point` in
`U₂` (its past form through `C.dual`); `p ∈ ∂U₁ ∖ closure S`; (4.83)'s content gives `V ⊆ U₂`
with `V ∩ U₁ ⊆ A` (`inter_subset_connectedComponentIn`); the restart gives `O`; `u₃` solves on
`U₁` and on `O` (`hagree`, `hres`), hence on `U₁ ∪ O` (`hglue`).

Hypotheses and suppliers: `hloc`, `hglue`, `hres` — (4.61) is local; `hconn`, `hcaus`, `hsplit`,
`hJm`, `hJp`, `hK`, `hSclosed` — `U₂` a GHD of `g(u₂)` (connected, causal, split by `S`, `J^∓`
closed, compact slabs, `S` closed; T-loc-quasilinear-causal-ladder); `honesided` —
`one_sided_boundary` of `U₁` (Lemma 4.86); `hagree` — Remark 4.67's variation; `hstep` —
`slice_restart` with `Q = GluedRestartAt` (T-loc-quasilinear-slice). -/
theorem ers_theorem_4_82_restart [T2Space M] [LocallyConnectedSpace M]
    (hloc : SolutionLocal sol) (hglue : SolutionsGlue sol) (hres : SolutionRestricts sol)
    {s₀ : M} (hs₀ : s₀ ∈ S) {U₁ U₂ : Opens M} {u₁ u₂ : M → β}
    (h₁ : IsDevelopment sol cau S U₁ u₁) (h₂ : IsDevelopment sol cau S U₂ u₂)
    (hnot : ¬ U₂ ≤ U₁) (hconn : IsPreconnected (U₂ : Set M))
    (hcaus : ∀ ⦃x y : M⦄, (cau u₂).le U₂ x y → (cau u₂).le U₂ y x → x = y)
    (hsplit : (cau u₂).SplitBy U₂ S)
    (hJm : ∀ x ∈ U₂, closure ((cau u₂).Jminus U₂ {x}) ∩ U₂ ⊆ (cau u₂).Jminus U₂ {x})
    (hJp : ∀ x ∈ U₂, closure ((cau u₂).Jplus U₂ {x}) ∩ U₂ ⊆ (cau u₂).Jplus U₂ {x})
    (hK : (cau u₂).CompactSlabs U₂ S) (hSclosed : closure S ∩ U₂ ⊆ S)
    (honesided : Causality.OneSidedBoundary U₁ (closure S))
    (hagree : EqOn u₁ u₂ (connectedComponentIn ((U₁ : Set M) ∩ U₂) s₀))
    (hstep : (cau u₂).SliceRestart U₂ S (connectedComponentIn ((U₁ : Set M) ∩ U₂) s₀) U₂
      (GluedRestartAt cau S U₁ U₂ u₁ u₂ (connectedComponentIn ((U₁ : Set M) ∩ U₂) s₀))) :
    ∃ O : Opens M, (O : Set M) ⊆ U₂ ∧ U₁ < U₁ ⊔ O ∧
      IsExtension U₁ u₁ (U₁ ⊔ O) (glueSolutions U₁ u₁ u₂) ∧
      EqOn (glueSolutions U₁ u₁ u₂) u₂ O ∧
      IsDevelopment sol cau S (U₁ ⊔ O) (glueSolutions U₁ u₁ u₂) := by
  have hs₀' : s₀ ∈ (U₁ : Set M) ∩ U₂ := ⟨h₁.subset hs₀, h₂.subset hs₀⟩
  -- (4.84): the component `A` has frontier points in `U₂`, all on the frontier of `U₁`
  obtain ⟨⟨q, hqf, hqU₂⟩, hsub⟩ := Causality.frontier_connectedComponentIn_inter U₁.isOpen
    U₂.isOpen hs₀' hconn fun h => hnot h
  -- (4.85): a frontier point of `A` in `U₂` at which the frontier is spacelike in `U₂`
  obtain ⟨p, hpmem, hp⟩ : ∃ p ∈ frontier (connectedComponentIn ((U₁ : Set M) ∩ U₂) s₀) ∩ U₂,
      (cau u₂).IsSpacelikeBoundaryPoint U₂ S
        (frontier (connectedComponentIn ((U₁ : Set M) ∩ U₂) s₀)) p := by
    rcases hsplit q hqU₂ with hq | hq
    · obtain ⟨p, hpK, hp⟩ := Causality.exists_spacelike_boundary_point hcaus hJm
        isClosed_frontier ⟨hq, hqf⟩ (hK q).1
      obtain ⟨y, -, hpy⟩ := hpK.1.1
      exact ⟨p, ⟨hpK.2, (cau u₂).le_mem_left hpy⟩, Or.inl hp⟩
    · obtain ⟨p, hpK, hp⟩ := Causality.exists_spacelike_boundary_point (C := (cau u₂).dual)
        (fun _ _ h1 h2 => hcaus h2 h1) hJp isClosed_frontier ⟨hq, hqf⟩ (hK q).2
      obtain ⟨y, -, hpy⟩ := hpK.1.1
      exact ⟨p, ⟨hpK.2, (cau u₂).le_mem_right hpy⟩, Or.inr hp⟩
  -- `p` lies on the frontier of `U₁`, off the closure of `S`
  have hp₁ : p ∈ frontier (U₁ : Set M) := hsub hpmem
  have hpS : p ∉ closure S := fun h => by
    have hpU₁ : p ∉ (U₁ : Set M) := by
      rw [U₁.isOpen.frontier_eq] at hp₁; exact hp₁.2
    exact hpU₁ (h₁.subset (hSclosed ⟨h, hpmem.2⟩))
  -- (4.83), through its topological content: a neighbourhood `V ⊆ U₂` of `p` with `V ∩ U₁ ⊆ A`
  obtain ⟨V, hV, hVsub, hVconn⟩ := honesided p ⟨hp₁, hpS⟩ _ (U₂.isOpen.mem_nhds hpmem.2)
  have hVA := Causality.inter_subset_connectedComponentIn (frontier_subset_closure hpmem.1) hV
    hVsub hVconn
  -- the restart: an open `O ⊆ V` leaving `U₁`, with `S` Cauchy in `U₁ ∪ O` for the glued solution
  obtain ⟨O, hOV, hOnot, hOc⟩ := hstep p hpmem hp V hV hVsub hVA
  have hOU₂ : (O : Set M) ⊆ U₂ := hOV.trans hVsub
  -- ERS's `u₃` (`ghd_02_19.tex:1138`): well defined because `V ∩ U₁ ⊆ A`, where `u₁ = u₂`
  have hgO : EqOn (glueSolutions U₁ u₁ u₂) u₂ O :=
    eqOn_glueSolutions_right fun x hx => hagree (hVA ⟨hOV hx.1, hx.2⟩)
  have hsol₁ : sol U₁ (glueSolutions U₁ u₁ u₂) :=
    hloc (eqOn_glueSolutions_left U₁ u₁ u₂).symm h₁.solves
  have hsolO : sol O (glueSolutions U₁ u₁ u₂) := hloc hgO.symm (hres hOU₂ h₂.solves)
  have hsol : sol (U₁ ⊔ O) (glueSolutions U₁ u₁ u₂) := by
    have h := hglue {U₁, O} (glueSolutions U₁ u₁ u₂) (insert_nonempty _ _) (by
      rintro W (rfl | hW)
      · exact hsol₁
      · rw [mem_singleton_iff.1 hW]; exact hsolO)
    rwa [sSup_pair] at h
  refine ⟨O, hOU₂, lt_of_le_of_ne le_sup_left fun h => hOnot (le_sup_right.trans h.symm.le),
    ⟨le_sup_left, (eqOn_glueSolutions_left U₁ u₁ u₂).symm⟩, hgO,
    hsol, fun x hx => (le_sup_left : U₁ ≤ U₁ ⊔ O) (h₁.subset hx), hOc⟩

/-! ## 3. Theorem 4.82 -/

/-- **ERS19 Theorem 4.82 over a solution predicate** (`ersthm:ThmNotBlocking`, unmarked;
`ghd_02_19.tex:1100`, proof 1114–1139): a maximal development `(U₁, u₁)` whose frontier off
`closure S` is one-sided contains every development `(U₂, u₂)`, which it extends: `U₂ ⊆ U₁` and
`u₁ = u₂` on `U₂`. Otherwise `ers_theorem_4_82_restart` gives a strictly larger development
extending `u₁`, against maximality; then `A = U₂` and `hagree` gives the agreement.

The hypotheses on each development are those of `ers_theorem_4_82_of_sliceRestart`, asked of the
developments of `sol` (their suppliers there); `hagree` — Remark 4.67's variation for each
development (derived in `_of_ers_theorem_4_64`); `hstep` — `slice_restart`, the restart of
`U₁` against each development, with the geometric `Q = GluedRestartAt`. -/
theorem ers_theorem_4_82_solution [T2Space M] [LocallyConnectedSpace M]
    (hloc : SolutionLocal sol) (hglue : SolutionsGlue sol) (hres : SolutionRestricts sol)
    {s₀ : M} (hs₀ : s₀ ∈ S) {U₁ : Opens M} {u₁ : M → β}
    (hmax : IsMaximalDevelopment sol cau S U₁ u₁)
    (honesided : Causality.OneSidedBoundary U₁ (closure S))
    (hconn : ∀ U u, IsDevelopment sol cau S U u → IsPreconnected (U : Set M))
    (hcaus : ∀ U u, IsDevelopment sol cau S U u →
      ∀ ⦃x y : M⦄, (cau u).le U x y → (cau u).le U y x → x = y)
    (hsplit : ∀ U u, IsDevelopment sol cau S U u → (cau u).SplitBy U S)
    (hJm : ∀ U u, IsDevelopment sol cau S U u →
      ∀ x ∈ U, closure ((cau u).Jminus U {x}) ∩ U ⊆ (cau u).Jminus U {x})
    (hJp : ∀ U u, IsDevelopment sol cau S U u →
      ∀ x ∈ U, closure ((cau u).Jplus U {x}) ∩ U ⊆ (cau u).Jplus U {x})
    (hK : ∀ U u, IsDevelopment sol cau S U u → (cau u).CompactSlabs U S)
    (hSclosed : ∀ U u, IsDevelopment sol cau S U u → closure S ∩ U ⊆ S)
    (hagree : ∀ U₂ u₂, IsDevelopment sol cau S U₂ u₂ →
      EqOn u₁ u₂ (connectedComponentIn ((U₁ : Set M) ∩ U₂) s₀))
    (hstep : ∀ U₂ u₂, IsDevelopment sol cau S U₂ u₂ →
      (cau u₂).SliceRestart U₂ S (connectedComponentIn ((U₁ : Set M) ∩ U₂) s₀) U₂
        (GluedRestartAt cau S U₁ U₂ u₁ u₂ (connectedComponentIn ((U₁ : Set M) ∩ U₂) s₀))) :
    ∀ U₂ u₂, IsDevelopment sol cau S U₂ u₂ → U₂ ≤ U₁ ∧ EqOn u₁ u₂ U₂ := by
  intro U₂ u₂ h₂
  have hle : U₂ ≤ U₁ := by
    by_contra hnot
    obtain ⟨O, -, hlt, hext, -, hdev⟩ := ers_theorem_4_82_restart hloc hglue hres hs₀ hmax.1 h₂
      hnot (hconn _ _ h₂) (hcaus _ _ h₂) (hsplit _ _ h₂) (hJm _ _ h₂) (hJp _ _ h₂) (hK _ _ h₂)
      (hSclosed _ _ h₂) honesided (hagree _ _ h₂) (hstep _ _ h₂)
    -- ERS: "This is a contradiction" (`ghd_02_19.tex:1138`), with maximality
    exact lt_irrefl _ (hlt.trans_le (hmax.2 _ _ hdev hext))
  refine ⟨hle, ?_⟩
  have hA : connectedComponentIn ((U₁ : Set M) ∩ U₂) s₀ = U₂ := by
    rw [inter_eq_right.2 (show (U₂ : Set M) ⊆ U₁ from hle),
      (hconn _ _ h₂).connectedComponentIn (h₂.subset hs₀)]
  have h := hagree _ _ h₂
  rwa [hA] at h

/-- **"Then u1 : U1 → R is the unique MGHD"**: every maximal development is `(U₁, u₁)`, on its
domain. Hypotheses of `ers_theorem_4_82_solution`. -/
theorem ers_theorem_4_82_solution_unique [T2Space M] [LocallyConnectedSpace M]
    (hloc : SolutionLocal sol) (hglue : SolutionsGlue sol) (hres : SolutionRestricts sol)
    {s₀ : M} (hs₀ : s₀ ∈ S) {U₁ : Opens M} {u₁ : M → β}
    (hmax : IsMaximalDevelopment sol cau S U₁ u₁)
    (honesided : Causality.OneSidedBoundary U₁ (closure S))
    (hconn : ∀ U u, IsDevelopment sol cau S U u → IsPreconnected (U : Set M))
    (hcaus : ∀ U u, IsDevelopment sol cau S U u →
      ∀ ⦃x y : M⦄, (cau u).le U x y → (cau u).le U y x → x = y)
    (hsplit : ∀ U u, IsDevelopment sol cau S U u → (cau u).SplitBy U S)
    (hJm : ∀ U u, IsDevelopment sol cau S U u →
      ∀ x ∈ U, closure ((cau u).Jminus U {x}) ∩ U ⊆ (cau u).Jminus U {x})
    (hJp : ∀ U u, IsDevelopment sol cau S U u →
      ∀ x ∈ U, closure ((cau u).Jplus U {x}) ∩ U ⊆ (cau u).Jplus U {x})
    (hK : ∀ U u, IsDevelopment sol cau S U u → (cau u).CompactSlabs U S)
    (hSclosed : ∀ U u, IsDevelopment sol cau S U u → closure S ∩ U ⊆ S)
    (hagree : ∀ U₂ u₂, IsDevelopment sol cau S U₂ u₂ →
      EqOn u₁ u₂ (connectedComponentIn ((U₁ : Set M) ∩ U₂) s₀))
    (hstep : ∀ U₂ u₂, IsDevelopment sol cau S U₂ u₂ →
      (cau u₂).SliceRestart U₂ S (connectedComponentIn ((U₁ : Set M) ∩ U₂) s₀) U₂
        (GluedRestartAt cau S U₁ U₂ u₁ u₂ (connectedComponentIn ((U₁ : Set M) ∩ U₂) s₀))) :
    ∀ U u, IsMaximalDevelopment sol cau S U u → U = U₁ ∧ EqOn u₁ u U := by
  intro U u h
  obtain ⟨hle, heq⟩ := ers_theorem_4_82_solution hloc hglue hres hs₀ hmax honesided hconn hcaus
    hsplit hJm hJp hK hSclosed hagree hstep U u h.1
  exact ⟨le_antisymm hle (h.2 U₁ u₁ hmax.1 ⟨hle, heq.symm⟩), heq⟩

/-- **Theorem 4.82 over a solution predicate, each development globally hyperbolic and
tarentin** (ladder `globally_hyperbolic`, `tarentin`, read on the development): `hcaus`, `hJm`,
`hJp` derived (`GloballyHyperbolicOn.closure_Jminus_inter_subset`). Otherwise
`ers_theorem_4_82_solution`. -/
theorem ers_theorem_4_82_solution_of_globallyHyperbolicOn [T2Space M] [LocallyConnectedSpace M]
    (hloc : SolutionLocal sol) (hglue : SolutionsGlue sol) (hres : SolutionRestricts sol)
    {s₀ : M} (hs₀ : s₀ ∈ S) {U₁ : Opens M} {u₁ : M → β}
    (hmax : IsMaximalDevelopment sol cau S U₁ u₁)
    (honesided : Causality.OneSidedBoundary U₁ (closure S))
    (hconn : ∀ U u, IsDevelopment sol cau S U u → IsPreconnected (U : Set M))
    (hG : ∀ U u, IsDevelopment sol cau S U u → (cau u).GloballyHyperbolicOn U)
    (hT : ∀ U u, IsDevelopment sol cau S U u → (cau u).TarentinOn U)
    (hsplit : ∀ U u, IsDevelopment sol cau S U u → (cau u).SplitBy U S)
    (hK : ∀ U u, IsDevelopment sol cau S U u → (cau u).CompactSlabs U S)
    (hSclosed : ∀ U u, IsDevelopment sol cau S U u → closure S ∩ U ⊆ S)
    (hagree : ∀ U₂ u₂, IsDevelopment sol cau S U₂ u₂ →
      EqOn u₁ u₂ (connectedComponentIn ((U₁ : Set M) ∩ U₂) s₀))
    (hstep : ∀ U₂ u₂, IsDevelopment sol cau S U₂ u₂ →
      (cau u₂).SliceRestart U₂ S (connectedComponentIn ((U₁ : Set M) ∩ U₂) s₀) U₂
        (GluedRestartAt cau S U₁ U₂ u₁ u₂ (connectedComponentIn ((U₁ : Set M) ∩ U₂) s₀))) :
    ∀ U₂ u₂, IsDevelopment sol cau S U₂ u₂ → U₂ ≤ U₁ ∧ EqOn u₁ u₂ U₂ :=
  ers_theorem_4_82_solution hloc hglue hres hs₀ hmax honesided hconn (fun U u h => (hG U u h).1)
    hsplit (fun U u h => (hG U u h).closure_Jminus_inter_subset (hT U u h))
    (fun U u h => (hG U u h).closure_Jplus_inter_subset (hT U u h)) hK hSclosed hagree hstep

/-- `U₁ ∩ A'`, `A'` the component of `U₁ ∩ U₂` through `s₀` as an open set, is that component. -/
theorem coe_inf_componentOpens [LocallyConnectedSpace M] (U₁ U₂ : Opens M) (s₀ : M) :
    ((U₁ ⊓ componentOpens (U₁ ⊓ U₂) s₀ : Opens M) : Set M) =
      connectedComponentIn ((U₁ : Set M) ∩ U₂) s₀ := by
  rw [Opens.coe_inf]
  exact inter_eq_right.2 fun x hx => (connectedComponentIn_subset _ _ hx).1

/-- **Theorem 4.82 with Remark 4.67's variation derived** ("A slight variation of Remark 4.67
shows that the set A is the MCGHD", `ghd_02_19.tex:1128`): `u₁ = u₂` on `A` is
`Causality.ers_theorem_4_64` for `U₁` and the open `A` (`componentOpens (U₁ ⊓ U₂) s₀`), whose
overlap `U₁ ∩ A = A` is connected. Its hypotheses: `U₁` GH, tarentin, split, compact slabs (from
`hG`, `hT`, `hsplit`, `hK` at `U₁`), `hacausal` (`S` acausal in `U₁`, OQ-41), and, for each
development, its `hlocal` (Prop 4.63, `local_uniqueness`), `hstay` (`frontier_stays_in`),
`hstep₄₆₄` (`slice_restart` with 4.64's `Q`) for the pair `(U₁, A)`. Otherwise
`ers_theorem_4_82_solution_of_globallyHyperbolicOn`. -/
theorem ers_theorem_4_82_solution_of_ers_theorem_4_64 [T2Space M] [LocallyConnectedSpace M]
    (hloc : SolutionLocal sol) (hglue : SolutionsGlue sol) (hres : SolutionRestricts sol)
    {s₀ : M} (hs₀ : s₀ ∈ S) {U₁ : Opens M} {u₁ : M → β}
    (hmax : IsMaximalDevelopment sol cau S U₁ u₁)
    (honesided : Causality.OneSidedBoundary U₁ (closure S))
    (hconn : ∀ U u, IsDevelopment sol cau S U u → IsPreconnected (U : Set M))
    (hG : ∀ U u, IsDevelopment sol cau S U u → (cau u).GloballyHyperbolicOn U)
    (hT : ∀ U u, IsDevelopment sol cau S U u → (cau u).TarentinOn U)
    (hsplit : ∀ U u, IsDevelopment sol cau S U u → (cau u).SplitBy U S)
    (hK : ∀ U u, IsDevelopment sol cau S U u → (cau u).CompactSlabs U S)
    (hSclosed : ∀ U u, IsDevelopment sol cau S U u → closure S ∩ U ⊆ S)
    (hacausal : (cau u₁).IsAcausalOn U₁ S)
    (hlocal : ∀ U₂ u₂, IsDevelopment sol cau S U₂ u₂ →
      ∃ V, (cau u₁).IsCommonDevelopment S U₁ (componentOpens (U₁ ⊓ U₂) s₀)
        (fun V : Opens M => EqOn u₁ u₂ V) V)
    (hstay : ∀ U₂ u₂, IsDevelopment sol cau S U₂ u₂ → ∀ V,
      (cau u₁).IsCommonDevelopment S U₁ (componentOpens (U₁ ⊓ U₂) s₀)
        (fun V : Opens M => EqOn u₁ u₂ V) V →
      (cau u₁).FrontierStaysIn U₁ S V ((U₁ ⊓ componentOpens (U₁ ⊓ U₂) s₀ : Opens M) : Set M))
    (hstep₄₆₄ : ∀ U₂ u₂, IsDevelopment sol cau S U₂ u₂ → ∀ V,
      (cau u₁).IsCommonDevelopment S U₁ (componentOpens (U₁ ⊓ U₂) s₀)
        (fun V : Opens M => EqOn u₁ u₂ V) V →
      (cau u₁).SliceRestart U₁ S V ((U₁ ⊓ componentOpens (U₁ ⊓ U₂) s₀ : Opens M) : Set M)
        (fun _ => ∃ V', (cau u₁).IsCommonDevelopment S U₁ (componentOpens (U₁ ⊓ U₂) s₀)
          (fun V : Opens M => EqOn u₁ u₂ V) V' ∧ V < V'))
    (hstep : ∀ U₂ u₂, IsDevelopment sol cau S U₂ u₂ →
      (cau u₂).SliceRestart U₂ S (connectedComponentIn ((U₁ : Set M) ∩ U₂) s₀) U₂
        (GluedRestartAt cau S U₁ U₂ u₁ u₂ (connectedComponentIn ((U₁ : Set M) ∩ U₂) s₀))) :
    ∀ U₂ u₂, IsDevelopment sol cau S U₂ u₂ → U₂ ≤ U₁ ∧ EqOn u₁ u₂ U₂ := by
  refine ers_theorem_4_82_solution_of_globallyHyperbolicOn hloc hglue hres hs₀ hmax honesided hconn
    hG hT hsplit hK hSclosed (fun U₂ u₂ h₂ => ?_) hstep
  -- "A slight variation of Remark 4.67" (`ghd_02_19.tex:1128`): Thm 4.64 for `U₁` and `A`
  have hA := coe_inf_componentOpens U₁ U₂ s₀
  have h := Causality.ers_theorem_4_64 (C := cau u₁) (agreementGlues_eqOn u₁ u₂)
    (hG U₁ u₁ hmax.1) (hT U₁ u₁ hmax.1) hacausal (hsplit U₁ u₁ hmax.1) (hK U₁ u₁ hmax.1)
    (by rw [hA]; exact isPreconnected_connectedComponentIn) (hlocal U₂ u₂ h₂) (hstay U₂ u₂ h₂)
    (hstep₄₆₄ U₂ u₂ h₂)
  intro x hx
  exact h (by rw [hA]; exact hx)

/-- **Theorem 4.82 over a solution predicate on a second countable background, `S` connected**
(§4's standing hypothesis, `ghd_02_19.tex:814`): `ers_theorem_4_82_solution_of_ers_theorem_4_64`
less `hconn`, `hsplit` (from `S` Cauchy in each development:
`isPreconnected_of_isCauchySurfaceOn_of_t1_…`, `splitBy_of_t1_secondCountable`) and less
`hacausal` (Thm 4.64 through its `_noArc` form, with `S` Cauchy in `U₁`, kb/0292). -/
theorem ers_theorem_4_82_solution_secondCountable [T2Space M] [SecondCountableTopology M]
    [LocallyConnectedSpace M]
    (hloc : SolutionLocal sol) (hglue : SolutionsGlue sol) (hres : SolutionRestricts sol)
    {s₀ : M} (hs₀ : s₀ ∈ S) (hS : IsPreconnected S) {U₁ : Opens M} {u₁ : M → β}
    (hmax : IsMaximalDevelopment sol cau S U₁ u₁)
    (honesided : Causality.OneSidedBoundary U₁ (closure S))
    (hG : ∀ U u, IsDevelopment sol cau S U u → (cau u).GloballyHyperbolicOn U)
    (hT : ∀ U u, IsDevelopment sol cau S U u → (cau u).TarentinOn U)
    (hK : ∀ U u, IsDevelopment sol cau S U u → (cau u).CompactSlabs U S)
    (hSclosed : ∀ U u, IsDevelopment sol cau S U u → closure S ∩ U ⊆ S)
    (hlocal : ∀ U₂ u₂, IsDevelopment sol cau S U₂ u₂ →
      ∃ V, (cau u₁).IsCommonDevelopment S U₁ (componentOpens (U₁ ⊓ U₂) s₀)
        (fun V : Opens M => EqOn u₁ u₂ V) V)
    (hstay : ∀ U₂ u₂, IsDevelopment sol cau S U₂ u₂ → ∀ V,
      (cau u₁).IsCommonDevelopment S U₁ (componentOpens (U₁ ⊓ U₂) s₀)
        (fun V : Opens M => EqOn u₁ u₂ V) V →
      (cau u₁).FrontierStaysIn U₁ S V ((U₁ ⊓ componentOpens (U₁ ⊓ U₂) s₀ : Opens M) : Set M))
    (hstep₄₆₄ : ∀ U₂ u₂, IsDevelopment sol cau S U₂ u₂ → ∀ V,
      (cau u₁).IsCommonDevelopment S U₁ (componentOpens (U₁ ⊓ U₂) s₀)
        (fun V : Opens M => EqOn u₁ u₂ V) V →
      (cau u₁).SliceRestart U₁ S V ((U₁ ⊓ componentOpens (U₁ ⊓ U₂) s₀ : Opens M) : Set M)
        (fun _ => ∃ V', (cau u₁).IsCommonDevelopment S U₁ (componentOpens (U₁ ⊓ U₂) s₀)
          (fun V : Opens M => EqOn u₁ u₂ V) V' ∧ V < V'))
    (hstep : ∀ U₂ u₂, IsDevelopment sol cau S U₂ u₂ →
      (cau u₂).SliceRestart U₂ S (connectedComponentIn ((U₁ : Set M) ∩ U₂) s₀) U₂
        (GluedRestartAt cau S U₁ U₂ u₁ u₂ (connectedComponentIn ((U₁ : Set M) ∩ U₂) s₀))) :
    ∀ U₂ u₂, IsDevelopment sol cau S U₂ u₂ → U₂ ≤ U₁ ∧ EqOn u₁ u₂ U₂ := by
  refine ers_theorem_4_82_solution_of_globallyHyperbolicOn hloc hglue hres hs₀ hmax honesided
    (fun U u h => Causality.isPreconnected_of_isCauchySurfaceOn_of_t1_secondCountable hS h.subset
      h.cauchy) hG hT (fun U u h => Causality.splitBy_of_t1_secondCountable h.cauchy) hK hSclosed
    (fun U₂ u₂ h₂ => ?_) hstep
  have hA := coe_inf_componentOpens U₁ U₂ s₀
  have h := Causality.ers_theorem_4_64_of_isCauchySurfaceOn_secondCountable_noArc (C := cau u₁)
    (agreementGlues_eqOn u₁ u₂) (hG U₁ u₁ hmax.1) (hT U₁ u₁ hmax.1) hmax.1.cauchy
    (hK U₁ u₁ hmax.1) (by rw [hA]; exact isPreconnected_connectedComponentIn) (hlocal U₂ u₂ h₂)
    (hstay U₂ u₂ h₂) (hstep₄₆₄ U₂ u₂ h₂)
  intro x hx
  exact h (by rw [hA]; exact hx)

/-- **At a development containing every development, the restart is vacuous**: if every
development lies in `U₁`, the component `A` of `U₁ ∩ U₂` is `U₂`, whose frontier misses `U₂`
(`Causality.sliceRestart_connectedComponentIn_of_le`). The solution form of
`ers_theorem_4_82_hstep_of_le`. -/
theorem ers_theorem_4_82_solution_hstep_of_le [LocallyConnectedSpace M] {s₀ : M} (hs₀ : s₀ ∈ S)
    {U₁ : Opens M} {u₁ : M → β}
    (hconn : ∀ U u, IsDevelopment sol cau S U u → IsPreconnected (U : Set M))
    (hle : ∀ U₂ u₂, IsDevelopment sol cau S U₂ u₂ → U₂ ≤ U₁) :
    ∀ U₂ u₂, IsDevelopment sol cau S U₂ u₂ →
      (cau u₂).SliceRestart U₂ S (connectedComponentIn ((U₁ : Set M) ∩ U₂) s₀) U₂
        (GluedRestartAt cau S U₁ U₂ u₁ u₂ (connectedComponentIn ((U₁ : Set M) ∩ U₂) s₀)) :=
  fun U₂ u₂ h₂ => Causality.sliceRestart_connectedComponentIn_of_le (hle U₂ u₂ h₂)
    (hconn U₂ u₂ h₂) (h₂.subset hs₀)

/-- **Given its other hypotheses, the restart of `ers_theorem_4_82_solution` at the maximal `U₁`
is equivalent to its conclusion** (the solution form of `ers_theorem_4_82_hstep_iff`): necessarily,
for any restart located on `∂A ∩ U₂`. What has content is the restart step at non-maximal pairs
(`ers_theorem_4_82_restart`), exercised at `(]-1/2, 1/2[, ]-1, 1[)` by
`Ers482Witness.timelikeLine_ers_theorem_4_82_restart` (`restart_exercised`). -/
theorem ers_theorem_4_82_solution_hstep_iff [T2Space M] [LocallyConnectedSpace M]
    (hloc : SolutionLocal sol) (hglue : SolutionsGlue sol) (hres : SolutionRestricts sol)
    {s₀ : M} (hs₀ : s₀ ∈ S) {U₁ : Opens M} {u₁ : M → β}
    (hmax : IsMaximalDevelopment sol cau S U₁ u₁)
    (honesided : Causality.OneSidedBoundary U₁ (closure S))
    (hconn : ∀ U u, IsDevelopment sol cau S U u → IsPreconnected (U : Set M))
    (hcaus : ∀ U u, IsDevelopment sol cau S U u →
      ∀ ⦃x y : M⦄, (cau u).le U x y → (cau u).le U y x → x = y)
    (hsplit : ∀ U u, IsDevelopment sol cau S U u → (cau u).SplitBy U S)
    (hJm : ∀ U u, IsDevelopment sol cau S U u →
      ∀ x ∈ U, closure ((cau u).Jminus U {x}) ∩ U ⊆ (cau u).Jminus U {x})
    (hJp : ∀ U u, IsDevelopment sol cau S U u →
      ∀ x ∈ U, closure ((cau u).Jplus U {x}) ∩ U ⊆ (cau u).Jplus U {x})
    (hK : ∀ U u, IsDevelopment sol cau S U u → (cau u).CompactSlabs U S)
    (hSclosed : ∀ U u, IsDevelopment sol cau S U u → closure S ∩ U ⊆ S)
    (hagree : ∀ U₂ u₂, IsDevelopment sol cau S U₂ u₂ →
      EqOn u₁ u₂ (connectedComponentIn ((U₁ : Set M) ∩ U₂) s₀)) :
    (∀ U₂ u₂, IsDevelopment sol cau S U₂ u₂ →
      (cau u₂).SliceRestart U₂ S (connectedComponentIn ((U₁ : Set M) ∩ U₂) s₀) U₂
        (GluedRestartAt cau S U₁ U₂ u₁ u₂ (connectedComponentIn ((U₁ : Set M) ∩ U₂) s₀))) ↔
      ∀ U₂ u₂, IsDevelopment sol cau S U₂ u₂ → U₂ ≤ U₁ :=
  ⟨fun hstep U₂ u₂ h₂ => (ers_theorem_4_82_solution hloc hglue hres hs₀ hmax honesided hconn hcaus
    hsplit hJm hJp hK hSclosed hagree hstep U₂ u₂ h₂).1,
    ers_theorem_4_82_solution_hstep_of_le hs₀ hconn⟩

/-- **Theorem 4.82 under the uniform restart, each development globally hyperbolic and tarentin**
(a form of record): `slice_restart` with `Q = GluedRestartAt` asked of every pair of developments
`(U₀, u₀)`, `(U₂, u₂)`, maximal or not, a property of the equation which names no maximal
development (ERS's gluing, `ghd_02_19.tex:1138`, uses none; only "This is a contradiction" does).
Specialised at `U₀ = U₁`: `ers_theorem_4_82_solution_of_globallyHyperbolicOn`, so as a theorem it
is logically weaker than that form; its hypothesis is exercised at non-maximal pairs
(`Ers482Witness.restarts82`), and that the conclusion does not imply it is argued, not proved. -/
theorem ers_theorem_4_82_solution_of_restarts [T2Space M] [LocallyConnectedSpace M]
    (hloc : SolutionLocal sol) (hglue : SolutionsGlue sol) (hres : SolutionRestricts sol)
    {s₀ : M} (hs₀ : s₀ ∈ S) {U₁ : Opens M} {u₁ : M → β}
    (hmax : IsMaximalDevelopment sol cau S U₁ u₁)
    (honesided : Causality.OneSidedBoundary U₁ (closure S))
    (hconn : ∀ U u, IsDevelopment sol cau S U u → IsPreconnected (U : Set M))
    (hG : ∀ U u, IsDevelopment sol cau S U u → (cau u).GloballyHyperbolicOn U)
    (hT : ∀ U u, IsDevelopment sol cau S U u → (cau u).TarentinOn U)
    (hsplit : ∀ U u, IsDevelopment sol cau S U u → (cau u).SplitBy U S)
    (hK : ∀ U u, IsDevelopment sol cau S U u → (cau u).CompactSlabs U S)
    (hSclosed : ∀ U u, IsDevelopment sol cau S U u → closure S ∩ U ⊆ S)
    (hagree : ∀ U₂ u₂, IsDevelopment sol cau S U₂ u₂ →
      EqOn u₁ u₂ (connectedComponentIn ((U₁ : Set M) ∩ U₂) s₀))
    (hrestart : ∀ U₀ u₀ U₂ u₂, IsDevelopment sol cau S U₀ u₀ → IsDevelopment sol cau S U₂ u₂ →
      (cau u₂).SliceRestart U₂ S (connectedComponentIn ((U₀ : Set M) ∩ U₂) s₀) U₂
        (GluedRestartAt cau S U₀ U₂ u₀ u₂ (connectedComponentIn ((U₀ : Set M) ∩ U₂) s₀))) :
    ∀ U₂ u₂, IsDevelopment sol cau S U₂ u₂ → U₂ ≤ U₁ ∧ EqOn u₁ u₂ U₂ :=
  ers_theorem_4_82_solution_of_globallyHyperbolicOn hloc hglue hres hs₀ hmax honesided hconn hG hT
    hsplit hK hSclosed hagree fun U₂ u₂ h₂ => hrestart U₁ u₁ U₂ u₂ hmax.1 h₂

/-- **Theorem 4.82 under the uniform restart, `is_causal` on each development** (a form of record,
the `is_causal`-level twin of `ers_theorem_4_82_solution_of_restarts`): the side conditions of
`ers_theorem_4_82_solution` (`hcaus`, `hJm`, `hJp` for `hG`, `hT`), and the restart asked of every
pair of developments. Specialised at `U₀ = U₁`: `ers_theorem_4_82_solution`. -/
theorem ers_theorem_4_82_solution_of_restarts_isCausal [T2Space M] [LocallyConnectedSpace M]
    (hloc : SolutionLocal sol) (hglue : SolutionsGlue sol) (hres : SolutionRestricts sol)
    {s₀ : M} (hs₀ : s₀ ∈ S) {U₁ : Opens M} {u₁ : M → β}
    (hmax : IsMaximalDevelopment sol cau S U₁ u₁)
    (honesided : Causality.OneSidedBoundary U₁ (closure S))
    (hconn : ∀ U u, IsDevelopment sol cau S U u → IsPreconnected (U : Set M))
    (hcaus : ∀ U u, IsDevelopment sol cau S U u →
      ∀ ⦃x y : M⦄, (cau u).le U x y → (cau u).le U y x → x = y)
    (hsplit : ∀ U u, IsDevelopment sol cau S U u → (cau u).SplitBy U S)
    (hJm : ∀ U u, IsDevelopment sol cau S U u →
      ∀ x ∈ U, closure ((cau u).Jminus U {x}) ∩ U ⊆ (cau u).Jminus U {x})
    (hJp : ∀ U u, IsDevelopment sol cau S U u →
      ∀ x ∈ U, closure ((cau u).Jplus U {x}) ∩ U ⊆ (cau u).Jplus U {x})
    (hK : ∀ U u, IsDevelopment sol cau S U u → (cau u).CompactSlabs U S)
    (hSclosed : ∀ U u, IsDevelopment sol cau S U u → closure S ∩ U ⊆ S)
    (hagree : ∀ U₂ u₂, IsDevelopment sol cau S U₂ u₂ →
      EqOn u₁ u₂ (connectedComponentIn ((U₁ : Set M) ∩ U₂) s₀))
    (hrestart : ∀ U₀ u₀ U₂ u₂, IsDevelopment sol cau S U₀ u₀ → IsDevelopment sol cau S U₂ u₂ →
      (cau u₂).SliceRestart U₂ S (connectedComponentIn ((U₀ : Set M) ∩ U₂) s₀) U₂
        (GluedRestartAt cau S U₀ U₂ u₀ u₂ (connectedComponentIn ((U₀ : Set M) ∩ U₂) s₀))) :
    ∀ U₂ u₂, IsDevelopment sol cau S U₂ u₂ → U₂ ≤ U₁ ∧ EqOn u₁ u₂ U₂ :=
  ers_theorem_4_82_solution hloc hglue hres hs₀ hmax honesided hconn hcaus hsplit hJm hJp hK
    hSclosed hagree fun U₂ u₂ h₂ => hrestart U₁ u₁ U₂ u₂ hmax.1 h₂

end Restart

/-! ## 4. Witnesses on the timelike line (kb/0011) -/

/-- On the timelike line, `{0}` is a Cauchy surface of every bounded open interval `]a, b[`
around `0`: the range of `x ↦ m + k·arctan (x + x₀)`, `m = (a + b)/2`, `k = (b - a)/π`,
`arctan x₀ = -m/k` (`timelikeLine_isCauchySurfaceOn_range`). -/
theorem timelikeLine_isCauchySurfaceOn_Ioo_of_neg_of_pos {a b : ℝ} (ha : a < 0) (hb : 0 < b)
    {U : Opens ℝ} (hU : (U : Set ℝ) = Ioo a b) : timelikeLine.IsCauchySurfaceOn U {0} := by
  have hπ : 0 < Real.pi := Real.pi_pos
  set k := (b - a) / Real.pi with hk_def
  have hk : 0 < k := div_pos (by linarith) hπ
  set m := (a + b) / 2 with hm_def
  have hkπ : k * (Real.pi / 2) = (b - a) / 2 := by rw [hk_def]; field_simp
  have hkm : k * (m / k) = m := by field_simp
  have hθ₁ : -(Real.pi / 2) < -(m / k) := by
    rw [neg_lt_neg_iff, div_lt_iff₀ hk]
    linarith
  have hθ₂ : -(m / k) < Real.pi / 2 := by
    rw [neg_lt, lt_div_iff₀ hk]
    linarith
  set x₀ := Real.tan (-(m / k))
  have hx₀ : Real.arctan x₀ = -(m / k) := Real.arctan_tan hθ₁ hθ₂
  have harctan : IsOpenMap Real.arctan :=
    isOpen_Ioo.isOpenMap_subtype_val.comp Real.tanOrderIso.symm.toHomeomorph.isOpenMap
  have hgo : IsOpenMap (fun x => m + k * Real.arctan (x + x₀)) :=
    (Homeomorph.addLeft m).isOpenMap.comp ((Homeomorph.mulLeft₀ k hk.ne').isOpenMap.comp
      (harctan.comp (Homeomorph.addRight x₀).isOpenMap))
  have hmono : StrictMono (fun x => m + k * Real.arctan (x + x₀)) :=
    ((Real.arctan_strictMono.comp fun x y (h : x < y) => by linarith).const_mul hk).const_add m
  have hcont : Continuous (fun x => m + k * Real.arctan (x + x₀)) :=
    continuous_const.add (continuous_const.mul
      (Real.continuous_arctan.comp (continuous_id.add continuous_const)))
  have hr : range (fun x => Real.arctan (x + x₀)) = Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    have hsurj : range (fun x : ℝ => x + x₀) = univ :=
      (Homeomorph.addRight x₀).surjective.range_eq
    rw [range_comp' Real.arctan (· + x₀), hsurj, image_univ, Real.range_arctan]
  have hrange : range (fun x => m + k * Real.arctan (x + x₀)) = Ioo a b := by
    rw [range_comp' (fun y => m + y) (fun x => k * Real.arctan (x + x₀)),
      range_comp' (k * ·) (fun x => Real.arctan (x + x₀)), hr, image_mul_left_Ioo hk,
      image_const_add_Ioo, mul_neg, hkπ]
    congr 1 <;> rw [hm_def] <;> ring
  have h := timelikeLine_isCauchySurfaceOn_range hmono hcont hgo (hU.trans hrange.symm)
  have h0 : m + k * Real.arctan (0 + x₀) = 0 := by
    rw [zero_add, hx₀, mul_neg, hkm]; ring
  rwa [h0] at h

/-- On the timelike line, `{0}` is a Cauchy surface of every bounded, order-connected open set
containing `0`: it is `]inf, sup[`. -/
theorem timelikeLine_isCauchySurfaceOn_of_ordConnected {W : Opens ℝ} (h0 : (0 : ℝ) ∈ W)
    (hW : OrdConnected (W : Set ℝ)) (hb : BddBelow (W : Set ℝ)) (ha : BddAbove (W : Set ℝ)) :
    timelikeLine.IsCauchySurfaceOn W {0} := by
  have hsub : (W : Set ℝ) ⊆ Ioo (sInf (W : Set ℝ)) (sSup (W : Set ℝ)) := fun x hx => by
    obtain ⟨l, r, ⟨hl, hr⟩, hlr⟩ := mem_nhds_iff_exists_Ioo_subset.1 (W.isOpen.mem_nhds hx)
    exact ⟨(csInf_le hb (hlr ⟨by linarith, by linarith⟩ : (l + x) / 2 ∈ W)).trans_lt
        (by linarith), lt_of_lt_of_le (by linarith)
        (le_csSup ha (hlr ⟨by linarith, by linarith⟩ : (x + r) / 2 ∈ W))⟩
  have heq : (W : Set ℝ) = Ioo (sInf (W : Set ℝ)) (sSup (W : Set ℝ)) :=
    hsub.antisymm (IsConnected.Ioo_csInf_csSup_subset ⟨⟨0, h0⟩, hW.isPreconnected⟩ hb ha)
  exact timelikeLine_isCauchySurfaceOn_Ioo_of_neg_of_pos (hsub h0).1 (hsub h0).2 heq

namespace Ers482Witness

open Causality

/-- **The witness problem**: `u` solves on `U` iff `U ⊆ ]-1, 1[` and `u = id` on `U`. -/
def sol82 : Opens ℝ → (ℝ → ℝ) → Prop := fun U u => (U : Set ℝ) ⊆ Ioo (-1) 1 ∧ EqOn u id U

/-- Its causality: the timelike line, whatever the function. -/
def cau82 : (ℝ → ℝ) → Causality ℝ := fun _ => timelikeLine

/-- A solution sees only its domain. -/
theorem sol82_local : SolutionLocal sol82 := fun _ _ _ huv hu =>
  ⟨hu.1, fun _ hx => (huv hx).symm.trans (hu.2 hx)⟩

/-- Solutions glue: a union of open subsets of `]-1, 1[` is one. -/
theorem sol82_glue : SolutionsGlue sol82 := by
  intro 𝒰 v _ h
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨U, hU, hxU⟩ := Opens.mem_sSup.1 hx
    exact (h U hU).1 hxU
  · obtain ⟨U, hU, hxU⟩ := Opens.mem_sSup.1 hx
    exact (h U hU).2 hxU

/-- Solutions restrict. -/
theorem sol82_restricts : SolutionRestricts sol82 := fun _ _ _ hVU hu =>
  ⟨fun _ hx => hu.1 (hVU hx), fun _ hx => hu.2 (hVU hx)⟩

/-- The causality follows the solution (trivially: it is constant). Not a hypothesis of the
forms; recorded so that the witness problem satisfies the whole vocabulary of `Causal.ErsMughd`. -/
theorem cau82_follows : CausalityFollows cau82 := fun _ _ _ _ _ _ _ _ => Iff.rfl

/-- `]-1/2, 1/2[ ⊆ ]-1, 1[`. -/
theorem halfIoo_le : ErsWitness.halfIoo ≤ ersWitnessIoo := ErsWitness.dom82_le false

/-- `(]-1/2, 1/2[, id)` is a development (`timelikeLine_isCauchySurfaceOn_Ioo`). -/
theorem isDevelopment_halfIoo : IsDevelopment sol82 cau82 {0} ErsWitness.halfIoo id :=
  ⟨⟨fun _ hx => halfIoo_le hx, fun _ _ => rfl⟩,
    singleton_subset_iff.2 (show (0 : ℝ) ∈ Ioo (-(1 / 2)) (1 / 2) by constructor <;> norm_num),
    timelikeLine_isCauchySurfaceOn_Ioo one_half_pos ErsWitness.coe_dom82_false⟩

/-- `(]-1, 1[, id)` is a development. -/
theorem isDevelopment_ersWitnessIoo : IsDevelopment sol82 cau82 {0} ersWitnessIoo id :=
  ⟨⟨fun _ hx => hx, fun _ _ => rfl⟩,
    singleton_subset_iff.2 (show (0 : ℝ) ∈ Ioo (-1) 1 by constructor <;> norm_num),
    timelikeLine_isCauchySurfaceOn_Ioo one_pos rfl⟩

/-- **`]-1, 1[` is a maximal development** of the witness problem: every development lies in it. -/
theorem isMaximalDevelopment_ersWitnessIoo :
    IsMaximalDevelopment sol82 cau82 {0} ersWitnessIoo id :=
  ⟨isDevelopment_ersWitnessIoo, fun _ _ h _ => h.solves.1⟩

/-- **`]-1/2, 1/2[` is not**: `]-1, 1[` extends it. -/
theorem not_isMaximalDevelopment_halfIoo :
    ¬ IsMaximalDevelopment sol82 cau82 {0} ErsWitness.halfIoo id := fun h =>
  ErsWitness.three_quarters_not_mem_dom82_false
    (h.2 _ _ isDevelopment_ersWitnessIoo ⟨halfIoo_le, fun _ _ => rfl⟩
      ErsWitness.three_quarters_mem_dom82_true)

/-- The component of `]-1/2, 1/2[ ∩ ]-1, 1[` through `0`. -/
theorem component_eq :
    connectedComponentIn ((ErsWitness.halfIoo : Set ℝ) ∩ ersWitnessIoo) 0 =
      Ioo (-(1 / 2)) (1 / 2) := by
  rw [inter_eq_left.2 (show (ErsWitness.halfIoo : Set ℝ) ⊆ ersWitnessIoo from halfIoo_le)]
  exact isPreconnected_Ioo.connectedComponentIn (show (0 : ℝ) ∈ Ioo (-(1 / 2)) (1 / 2) by
    constructor <;> norm_num)

/-- Its frontier is `{-1/2, 1/2}`. -/
theorem frontier_component :
    frontier (connectedComponentIn ((ErsWitness.halfIoo : Set ℝ) ∩ ersWitnessIoo) 0) =
      {-(1 / 2), 1 / 2} := by
  rw [component_eq, frontier_Ioo (by norm_num)]

/-- **The restart's premise is met, at both frontier points**: `±1/2` are frontier points of the
component `A = ]-1/2, 1/2[` in `U₂ = ]-1, 1[`, spacelike in `U₂` relative to `{0}` (the future
form at `1/2`, the past form at `-1/2`), and `U₂` itself is a neighbourhood `V ⊆ U₂` of each with
`V ∩ U₁ ⊆ A`. So `hstep` is exercised: the conclusion `GluedRestartAt` must be proved there
(`sliceRestart_halfIoo`). -/
theorem restart_exercised :
    (∀ p ∈ ({-(1 / 2), 1 / 2} : Set ℝ),
      p ∈ frontier (connectedComponentIn ((ErsWitness.halfIoo : Set ℝ) ∩ ersWitnessIoo) 0) ∩
        ersWitnessIoo ∧
      (ersWitnessIoo : Set ℝ) ∈ 𝓝 p ∧ (ersWitnessIoo : Set ℝ) ⊆ ersWitnessIoo ∧
      (ersWitnessIoo : Set ℝ) ∩ ErsWitness.halfIoo ⊆
        connectedComponentIn ((ErsWitness.halfIoo : Set ℝ) ∩ ersWitnessIoo) 0) ∧
    timelikeLine.IsSpacelikeBoundaryPoint ersWitnessIoo {0}
      (frontier (connectedComponentIn ((ErsWitness.halfIoo : Set ℝ) ∩ ersWitnessIoo) 0))
      (1 / 2) ∧
    timelikeLine.IsSpacelikeBoundaryPoint ersWitnessIoo {0}
      (frontier (connectedComponentIn ((ErsWitness.halfIoo : Set ℝ) ∩ ersWitnessIoo) 0))
      (-(1 / 2)) := by
  have hsub : ∀ {x y : ℝ}, -1 < x → y < 1 → Icc x y ⊆ (ersWitnessIoo : Set ℝ) :=
    fun hx hy => Icc_subset_Ioo hx hy
  refine ⟨fun p hp => ⟨⟨by rw [frontier_component]; exact hp, ?_⟩,
    ersWitnessIoo.isOpen.mem_nhds ?_, subset_rfl, fun x hx => ?_⟩, Or.inl ?_, Or.inr ?_⟩
  · rcases hp with rfl | rfl <;> constructor <;> norm_num
  · rcases hp with rfl | rfl <;> constructor <;> norm_num
  · rw [component_eq]; exact hx.2
  · rw [frontier_component]
    ext z
    simp only [mem_inter_iff, Precausality.mem_Jminus_singleton, Precausality.mem_Jplus,
      mem_singleton_iff, exists_eq_left, mem_insert_iff, timelikeLine_le]
    constructor
    · rintro ⟨⟨-, hz | hz⟩, h0z, -⟩
      · rw [hz] at h0z; norm_num at h0z
      · exact hz
    · rintro rfl
      exact ⟨⟨⟨le_rfl, hsub (by norm_num) (by norm_num)⟩, Or.inr rfl⟩, by norm_num,
        hsub (by norm_num) (by norm_num)⟩
  · rw [frontier_component]
    ext z
    simp only [mem_inter_iff, Precausality.mem_Jplus_singleton, Precausality.mem_Jminus,
      mem_singleton_iff, exists_eq_left, mem_insert_iff, timelikeLine_le]
    constructor
    · rintro ⟨⟨-, hz | hz⟩, hz0, -⟩
      · exact hz
      · rw [hz] at hz0; norm_num at hz0
    · rintro rfl
      exact ⟨⟨⟨le_rfl, hsub (by norm_num) (by norm_num)⟩, Or.inl rfl⟩, by norm_num,
        hsub (by norm_num) (by norm_num)⟩

/-! ### The hypotheses on every development of the witness problem -/

/-- A development of the witness problem is preconnected (`S = {0}` Cauchy on a second
countable `ℝ`). -/
theorem hconn82 : ∀ (U : Opens ℝ) (u : ℝ → ℝ), IsDevelopment sol82 cau82 {0} U u →
    IsPreconnected (U : Set ℝ) := fun _ _ h =>
  isPreconnected_of_isCauchySurfaceOn_of_t1_secondCountable isPreconnected_singleton h.subset
    h.cauchy

/-- The timelike line is globally hyperbolic on every open set. -/
theorem hG82 : ∀ (U : Opens ℝ) (u : ℝ → ℝ), IsDevelopment sol82 cau82 {0} U u →
    (cau82 u).GloballyHyperbolicOn U := fun U _ _ => timelikeLine_globallyHyperbolicOn U

/-- The timelike line is tarentin on every open set. -/
theorem hT82 : ∀ (U : Opens ℝ) (u : ℝ → ℝ), IsDevelopment sol82 cau82 {0} U u →
    (cau82 u).TarentinOn U := fun U _ _ => timelikeLine_tarentinOn U

/-- `{0}` splits every development (`splitBy_of_t1_secondCountable`). -/
theorem hsplit82 : ∀ (U : Opens ℝ) (u : ℝ → ℝ), IsDevelopment sol82 cau82 {0} U u →
    (cau82 u).SplitBy U {0} := fun _ _ h => splitBy_of_t1_secondCountable h.cauchy

/-- Compact slabs (`GloballyHyperbolicOn.compactSlabs_singleton`). -/
theorem hK82 : ∀ (U : Opens ℝ) (u : ℝ → ℝ), IsDevelopment sol82 cau82 {0} U u →
    (cau82 u).CompactSlabs U {0} := fun U _ _ =>
  (timelikeLine_globallyHyperbolicOn U).compactSlabs_singleton 0

/-- `{0}` is closed. -/
theorem hSclosed82 : ∀ (U : Opens ℝ) (u : ℝ → ℝ), IsDevelopment sol82 cau82 {0} U u →
    closure ({0} : Set ℝ) ∩ U ⊆ {0} := fun _ _ _ => by
  rw [closure_singleton]; exact inter_subset_left

/-- `]-1, 1[` has a one-sided boundary (`oneSidedBoundary_of_ordConnected`). -/
theorem honesided82 : OneSidedBoundary ersWitnessIoo (closure ({0} : Set ℝ)) :=
  oneSidedBoundary_of_ordConnected (show OrdConnected (Ioo (-1 : ℝ) 1) from ordConnected_Ioo) _

/-- **Rem 4.67's variation holds on the witness**: `u₁ = id` agrees with every development on
the component. -/
theorem hagree82 : ∀ (U₂ : Opens ℝ) (u₂ : ℝ → ℝ), IsDevelopment sol82 cau82 {0} U₂ u₂ →
    EqOn id u₂ (connectedComponentIn ((ersWitnessIoo : Set ℝ) ∩ U₂) 0) := fun _ _ h₂ _ hx =>
  (h₂.solves.2 (connectedComponentIn_subset _ _ hx).2).symm

/-- On the witness, the component of `]-1, 1[ ∩ U₂` through `0`, as an open set, is `U₂`. -/
theorem componentOpens_eq {U₂ : Opens ℝ} {u₂ : ℝ → ℝ}
    (h₂ : IsDevelopment sol82 cau82 {0} U₂ u₂) : componentOpens (ersWitnessIoo ⊓ U₂) 0 = U₂ := by
  apply SetLike.coe_injective
  show connectedComponentIn ((ersWitnessIoo ⊓ U₂ : Opens ℝ) : Set ℝ) 0 = U₂
  rw [Opens.coe_inf, inter_eq_right.2 (show (U₂ : Set ℝ) ⊆ ersWitnessIoo from h₂.solves.1)]
  exact (hconn82 _ _ h₂).connectedComponentIn (h₂.subset (mem_singleton 0))

/-- Thm 4.64's restart hypotheses for the pair `(]-1, 1[, A)`, `A = U₂`, on the witness: `U₂`
is a common development; the frontier below a frontier point stays in the interval `U₂`; a
frontier point of a common development `V` in `U₂` is not in `V`, so `V < U₂`. -/
theorem ers_4_64_data82 {U₂ : Opens ℝ} {u₂ : ℝ → ℝ}
    (h₂ : IsDevelopment sol82 cau82 {0} U₂ u₂) :
    (∃ V, (cau82 id).IsCommonDevelopment {0} ersWitnessIoo (componentOpens (ersWitnessIoo ⊓ U₂) 0)
      (fun V : Opens ℝ => EqOn id u₂ V) V) ∧
    (∀ V, (cau82 id).IsCommonDevelopment {0} ersWitnessIoo
        (componentOpens (ersWitnessIoo ⊓ U₂) 0) (fun V : Opens ℝ => EqOn id u₂ V) V →
      (cau82 id).FrontierStaysIn ersWitnessIoo {0} V
        ((ersWitnessIoo ⊓ componentOpens (ersWitnessIoo ⊓ U₂) 0 : Opens ℝ) : Set ℝ)) ∧
    (∀ V, (cau82 id).IsCommonDevelopment {0} ersWitnessIoo
        (componentOpens (ersWitnessIoo ⊓ U₂) 0) (fun V : Opens ℝ => EqOn id u₂ V) V →
      (cau82 id).SliceRestart ersWitnessIoo {0} V
        ((ersWitnessIoo ⊓ componentOpens (ersWitnessIoo ⊓ U₂) 0 : Opens ℝ) : Set ℝ)
        (fun _ => ∃ V', (cau82 id).IsCommonDevelopment {0} ersWitnessIoo
          (componentOpens (ersWitnessIoo ⊓ U₂) 0) (fun V : Opens ℝ => EqOn id u₂ V) V' ∧
            V < V')) := by
  rw [componentOpens_eq h₂]
  have hle : U₂ ≤ ersWitnessIoo := h₂.solves.1
  have hL : ((ersWitnessIoo ⊓ U₂ : Opens ℝ) : Set ℝ) = U₂ := by
    rw [Opens.coe_inf]; exact inter_eq_right.2 hle
  have hcd : (cau82 id).IsCommonDevelopment {0} ersWitnessIoo U₂
      (fun V : Opens ℝ => EqOn id u₂ V) U₂ :=
    ⟨le_inf hle le_rfl, h₂.subset, fun _ hx => (h₂.solves.2 hx).symm, h₂.cauchy⟩
  have hord : OrdConnected (U₂ : Set ℝ) := isPreconnected_iff_ordConnected.1 (hconn82 _ _ h₂)
  have h0 : (0 : ℝ) ∈ U₂ := h₂.subset (mem_singleton 0)
  refine ⟨⟨U₂, hcd⟩, fun V _ q hq => ?_, fun V hV p hp _ => ⟨U₂, hcd, ?_⟩⟩
  · rw [hL] at hq ⊢
    refine ⟨fun _ z hz => ?_, fun _ z hz => ?_⟩
    · obtain ⟨⟨hzq, ⟨_, rfl, h0z⟩⟩, -⟩ := hz
      rw [Precausality.mem_Jminus_singleton] at hzq
      exact hord.out h0 hq.2 ⟨(timelikeLine_le.1 h0z).1, (timelikeLine_le.1 hzq).1⟩
    · obtain ⟨⟨hqz, ⟨_, rfl, hz0⟩⟩, -⟩ := hz
      rw [Precausality.mem_Jplus_singleton] at hqz
      exact hord.out hq.2 h0 ⟨(timelikeLine_le.1 hqz).1, (timelikeLine_le.1 hz0).1⟩
  · refine lt_of_le_of_ne (hV.le.trans inf_le_right) fun hVeq => ?_
    have hpV : p ∈ (V : Set ℝ) := by rw [hVeq, ← hL]; exact hp.2
    have hpf := hp.1
    rw [V.isOpen.frontier_eq] at hpf
    exact hpf.2 hpV

/-- **The geometric restart holds at every pair of developments of the witness problem**,
maximal or not: at a frontier point `p` of the component in `U₂`, for every neighbourhood `V` of
`p`, a ball `O ⊆ V` about `p` leaves `U₀` (`p ∉ U₀`) and meets it (`p ∈ closure U₀`), so `U₀ ∪ O`
is a bounded interval around `0`, of which `{0}` is a Cauchy surface. -/
theorem restarts82 : ∀ (U₀ : Opens ℝ) (u₀ : ℝ → ℝ) (U₂ : Opens ℝ) (u₂ : ℝ → ℝ),
    IsDevelopment sol82 cau82 {0} U₀ u₀ → IsDevelopment sol82 cau82 {0} U₂ u₂ →
    (cau82 u₂).SliceRestart U₂ {0} (connectedComponentIn ((U₀ : Set ℝ) ∩ U₂) 0) U₂
      (GluedRestartAt cau82 {0} U₀ U₂ u₀ u₂ (connectedComponentIn ((U₀ : Set ℝ) ∩ U₂) 0)) := by
  rintro U₀ u₀ U₂ u₂ h₀ - p ⟨hpf, hpU₂⟩ - V hV - -
  have hp₀ : p ∉ U₀ := notMem_of_mem_frontier_connectedComponentIn hpf hpU₂
  have hpcl : p ∈ closure (U₀ : Set ℝ) :=
    closure_mono (fun x hx => (connectedComponentIn_subset _ _ hx).1) (frontier_subset_closure hpf)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hV
  have hO : Ioo (p - ε) (p + ε) ∈ 𝓝 p := Ioo_mem_nhds (by linarith) (by linarith)
  obtain ⟨z, hzO, hz₀⟩ := mem_closure_iff_nhds.1 hpcl _ hO
  refine ⟨⟨Ioo (p - ε) (p + ε), isOpen_Ioo⟩, fun x hx => hball (by rw [Real.ball_eq_Ioo]; exact hx),
    fun hle => hp₀ (hle (show p ∈ Ioo (p - ε) (p + ε) from ⟨by linarith, by linarith⟩)), ?_⟩
  show timelikeLine.IsCauchySurfaceOn _ {0}
  have hcoe : ((U₀ ⊔ ⟨Ioo (p - ε) (p + ε), isOpen_Ioo⟩ : Opens ℝ) : Set ℝ) =
      (U₀ : Set ℝ) ∪ Ioo (p - ε) (p + ε) := Opens.coe_sup _ _
  have h₀sub : (U₀ : Set ℝ) ⊆ Ioo (-1) 1 := h₀.solves.1
  refine timelikeLine_isCauchySurfaceOn_of_ordConnected
    (Or.inl (h₀.subset (mem_singleton 0)) : (0 : ℝ) ∈ (U₀ : Set ℝ) ∪ Ioo (p - ε) (p + ε)) ?_ ?_ ?_
  · rw [hcoe]
    exact isPreconnected_iff_ordConnected.1 ((hconn82 _ _ h₀).union z hz₀ hzO isPreconnected_Ioo)
  · rw [hcoe]
    refine ⟨min (-1) (p - ε), fun x hx => ?_⟩
    rcases hx with hx | hx
    · exact (min_le_left _ _).trans (h₀sub hx).1.le
    · exact (min_le_right _ _).trans hx.1.le
  · rw [hcoe]
    refine ⟨max 1 (p + ε), fun x hx => ?_⟩
    rcases hx with hx | hx
    · exact (h₀sub hx).2.le.trans (le_max_left _ _)
    · exact hx.2.le.trans (le_max_right _ _)

/-- **The geometric restart holds at `]-1/2, 1/2[` in `]-1, 1[`**: at `p = ±1/2`, for every
neighbourhood `V ⊆ ]-1, 1[` of `p`, the interval `O = ]p - δ, p + δ[ ⊆ V` (`δ ≤ 1/2`) leaves
`]-1/2, 1/2[`, and `{0}` is a Cauchy surface of `]-1/2, 1/2[ ∪ O`, an interval around `0`. -/
theorem sliceRestart_halfIoo :
    timelikeLine.SliceRestart ersWitnessIoo {0}
      (connectedComponentIn ((ErsWitness.halfIoo : Set ℝ) ∩ ersWitnessIoo) 0) ersWitnessIoo
      (GluedRestartAt cau82 {0} ErsWitness.halfIoo ersWitnessIoo id id
        (connectedComponentIn ((ErsWitness.halfIoo : Set ℝ) ∩ ersWitnessIoo) 0)) :=
  restarts82 _ _ _ _ isDevelopment_halfIoo isDevelopment_ersWitnessIoo

/-! ### The instances -/

/-- **The restart step at the non-maximal `]-1/2, 1/2[`, against `U₂ = ]-1, 1[`**
(`ers_theorem_4_82_restart`): every hypothesis discharged, `hstep` exercised
(`restart_exercised`) and proved (`sliceRestart_halfIoo`). It gives a strictly larger
development, the glued solution on `]-1/2, 1/2[ ∪ O`. -/
theorem timelikeLine_ers_theorem_4_82_restart :
    ∃ O : Opens ℝ, (O : Set ℝ) ⊆ ersWitnessIoo ∧ ErsWitness.halfIoo < ErsWitness.halfIoo ⊔ O ∧
      IsExtension ErsWitness.halfIoo id (ErsWitness.halfIoo ⊔ O)
        (glueSolutions ErsWitness.halfIoo id id) ∧
      EqOn (glueSolutions ErsWitness.halfIoo id id) id O ∧
      IsDevelopment sol82 cau82 {0} (ErsWitness.halfIoo ⊔ O)
        (glueSolutions ErsWitness.halfIoo id id) :=
  ers_theorem_4_82_restart sol82_local sol82_glue sol82_restricts (mem_singleton 0)
    isDevelopment_halfIoo isDevelopment_ersWitnessIoo
    (fun h => ErsWitness.three_quarters_not_mem_dom82_false
      (h ErsWitness.three_quarters_mem_dom82_true))
    (hconn82 _ _ isDevelopment_ersWitnessIoo) (hG82 _ _ isDevelopment_ersWitnessIoo).1
    (hsplit82 _ _ isDevelopment_ersWitnessIoo)
    ((hG82 _ _ isDevelopment_ersWitnessIoo).closure_Jminus_inter_subset
      (hT82 _ _ isDevelopment_ersWitnessIoo))
    ((hG82 _ _ isDevelopment_ersWitnessIoo).closure_Jplus_inter_subset
      (hT82 _ _ isDevelopment_ersWitnessIoo))
    (hK82 _ _ isDevelopment_ersWitnessIoo) (hSclosed82 _ _ isDevelopment_ersWitnessIoo)
    (oneSidedBoundary_of_ordConnected
      (show OrdConnected (Ioo (-(1 / 2) : ℝ) (1 / 2)) from ordConnected_Ioo) _)
    (fun _ _ => rfl) sliceRestart_halfIoo

/-- **Theorem 4.82 at the maximal `]-1, 1[`** (`ers_theorem_4_82_solution`): every hypothesis
discharged; `hstep` holds vacuously there, necessarily (`ers_theorem_4_82_solution_hstep_of_le`). -/
theorem timelikeLine_ers_theorem_4_82_solution :
    ∀ U₂ u₂, IsDevelopment sol82 cau82 {0} U₂ u₂ → U₂ ≤ ersWitnessIoo ∧ EqOn id u₂ U₂ :=
  ers_theorem_4_82_solution sol82_local sol82_glue sol82_restricts (mem_singleton 0)
    isMaximalDevelopment_ersWitnessIoo honesided82 hconn82 (fun U u h => (hG82 U u h).1) hsplit82
    (fun U u h => (hG82 U u h).closure_Jminus_inter_subset (hT82 U u h))
    (fun U u h => (hG82 U u h).closure_Jplus_inter_subset (hT82 U u h)) hK82 hSclosed82 hagree82
    (ers_theorem_4_82_solution_hstep_of_le (mem_singleton 0) hconn82 fun _ _ h => h.solves.1)

/-- **`]-1, 1[` is the unique maximal development** (`ers_theorem_4_82_solution_unique`). -/
theorem timelikeLine_ers_theorem_4_82_solution_unique :
    ∀ U u, IsMaximalDevelopment sol82 cau82 {0} U u → U = ersWitnessIoo ∧ EqOn id u U :=
  ers_theorem_4_82_solution_unique sol82_local sol82_glue sol82_restricts (mem_singleton 0)
    isMaximalDevelopment_ersWitnessIoo honesided82 hconn82 (fun U u h => (hG82 U u h).1) hsplit82
    (fun U u h => (hG82 U u h).closure_Jminus_inter_subset (hT82 U u h))
    (fun U u h => (hG82 U u h).closure_Jplus_inter_subset (hT82 U u h)) hK82 hSclosed82 hagree82
    (ers_theorem_4_82_solution_hstep_of_le (mem_singleton 0) hconn82 fun _ _ h => h.solves.1)

/-- **The globally hyperbolic and tarentin form at `]-1, 1[`**. -/
theorem timelikeLine_ers_theorem_4_82_solution_of_globallyHyperbolicOn :
    ∀ U₂ u₂, IsDevelopment sol82 cau82 {0} U₂ u₂ → U₂ ≤ ersWitnessIoo ∧ EqOn id u₂ U₂ :=
  ers_theorem_4_82_solution_of_globallyHyperbolicOn sol82_local sol82_glue sol82_restricts
    (mem_singleton 0) isMaximalDevelopment_ersWitnessIoo honesided82 hconn82 hG82 hT82 hsplit82 hK82
    hSclosed82 hagree82
    (ers_theorem_4_82_solution_hstep_of_le (mem_singleton 0) hconn82 fun _ _ h => h.solves.1)

/-- **The form with the agreement derived from Thm 4.64 at `]-1, 1[`**. -/
theorem timelikeLine_ers_theorem_4_82_solution_of_ers_theorem_4_64 :
    ∀ U₂ u₂, IsDevelopment sol82 cau82 {0} U₂ u₂ → U₂ ≤ ersWitnessIoo ∧ EqOn id u₂ U₂ :=
  ers_theorem_4_82_solution_of_ers_theorem_4_64 sol82_local sol82_glue sol82_restricts
    (mem_singleton 0) isMaximalDevelopment_ersWitnessIoo honesided82 hconn82 hG82 hT82 hsplit82 hK82
    hSclosed82 (fun _ hx _ hy _ => (mem_singleton_iff.1 hx).trans (mem_singleton_iff.1 hy).symm)
    (fun _ _ h₂ => (ers_4_64_data82 h₂).1) (fun _ _ h₂ => (ers_4_64_data82 h₂).2.1)
    (fun _ _ h₂ => (ers_4_64_data82 h₂).2.2)
    (ers_theorem_4_82_solution_hstep_of_le (mem_singleton 0) hconn82 fun _ _ h => h.solves.1)

/-- **The second countable form at `]-1, 1[`** (`S = {0}` preconnected). -/
theorem timelikeLine_ers_theorem_4_82_solution_secondCountable :
    ∀ U₂ u₂, IsDevelopment sol82 cau82 {0} U₂ u₂ → U₂ ≤ ersWitnessIoo ∧ EqOn id u₂ U₂ :=
  ers_theorem_4_82_solution_secondCountable sol82_local sol82_glue sol82_restricts
    (mem_singleton 0) isPreconnected_singleton isMaximalDevelopment_ersWitnessIoo honesided82 hG82
    hT82 hK82 hSclosed82 (fun _ _ h₂ => (ers_4_64_data82 h₂).1)
    (fun _ _ h₂ => (ers_4_64_data82 h₂).2.1) (fun _ _ h₂ => (ers_4_64_data82 h₂).2.2)
    (ers_theorem_4_82_solution_hstep_of_le (mem_singleton 0) hconn82 fun _ _ h => h.solves.1)

/-- **The uniform form at `]-1, 1[`** (`ers_theorem_4_82_solution_of_restarts`): its restart
hypothesis, at every pair of developments, holds on the witness problem (`restarts82`), and is
exercised at the pair `(]-1/2, 1/2[, ]-1, 1[)` (`restart_exercised`), where the conclusion
(`dom ≤ ]-1, 1[`) says nothing. -/
theorem timelikeLine_ers_theorem_4_82_solution_of_restarts :
    ∀ U₂ u₂, IsDevelopment sol82 cau82 {0} U₂ u₂ → U₂ ≤ ersWitnessIoo ∧ EqOn id u₂ U₂ :=
  ers_theorem_4_82_solution_of_restarts sol82_local sol82_glue sol82_restricts (mem_singleton 0)
    isMaximalDevelopment_ersWitnessIoo honesided82 hconn82 hG82 hT82 hsplit82 hK82 hSclosed82
    hagree82 restarts82

/-- **The `is_causal`-level uniform form at `]-1, 1[`**
(`ers_theorem_4_82_solution_of_restarts_isCausal`), with `restarts82`. -/
theorem timelikeLine_ers_theorem_4_82_solution_of_restarts_isCausal :
    ∀ U₂ u₂, IsDevelopment sol82 cau82 {0} U₂ u₂ → U₂ ≤ ersWitnessIoo ∧ EqOn id u₂ U₂ :=
  ers_theorem_4_82_solution_of_restarts_isCausal sol82_local sol82_glue sol82_restricts
    (mem_singleton 0) isMaximalDevelopment_ersWitnessIoo honesided82 hconn82
    (fun U u h => (hG82 U u h).1) hsplit82
    (fun U u h => (hG82 U u h).closure_Jminus_inter_subset (hT82 U u h))
    (fun U u h => (hG82 U u h).closure_Jplus_inter_subset (hT82 U u h)) hK82 hSclosed82 hagree82
    restarts82

end Ers482Witness

end Causal
