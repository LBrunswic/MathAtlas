import Causal.CauchyExtension
import Causal.Local

/-!
# An open set read as a spacetime, and the components of an inextensible curve in a smaller one

No label of `ETT.tex` is certified. These model-free lemmas are hoisted out of the model-importing
`Causal.CBG.CausalConvex` (programme target `T-abs-hoist-model-free`, kb/0047), so that a layer-1
module may use them: the module imports `Causal.CauchyExtension` and `Causal.Local`, and no model.
They serve the step of Sbierski's proof of Thm 3.4 quoted below (the union of developments), and
its uses in the CBG work (`Causal.CBG.*`) and in ERS19 §4 (`Causal.NestedCausalities`).

> Take a point on $\gamma$; it lies in some $U_\alpha$ and the corresponding
> curve segment in $U_\alpha$ can be considered to be an inextendible timelike curve in $U_\alpha$
> and thus has to meet $\iota(M)$. (Sbierski 1309.7591, proof of Thm 3.4)

## What is proved (no `sorry` in this file)

* `Causality.curveOn_of_rel_imp`: a curve of `V` for a family of relations is one for any family
  implied by it on the open subsets of `V`. Hence `causalCurveIn_congr_causality`,
  `extensible_congr_causality` and `inextensible_congr_causality`: inextensibility in `V` reads
  only the relations of the open subsets of `V`.
* `Causality.relativeTo U`, **the causality of the open set `U` carried by `M`** (kb/0001: no
  subtype), `(C.restrict U).extend` of `Causal.Local`: `relativeTo_le_iff` (the relations of `C`
  on the opens of `U`), `relativeTo_le_top`, `relativeTo_isCausal` (causal when `≤_U` is
  antisymmetric), `relativeTo_mem`, `relativeTo_causalCurveIn`, `relativeTo_inextensible_top` (an
  inextensible curve of `U` is an inextensible curve of `M` for `relativeTo U`).
* `Causality.inextensible_ordConnectedComponent_of_le`, **relative components**: the component, in
  an open `W ≤ U`, of an inextensible causal curve of `U`, through a parameter whose point lies in
  `W`, is an inextensible causal curve of `W` (`M` Hausdorff, `≤_U` antisymmetric). It is
  `inextensible_ordConnectedComponent` of `Causal.CauchyExtension` (the case `U = ⊤`) applied to
  `relativeTo U`.

## Hypothesis checklist

| source hypothesis | here |
|---|---|
| Thm 3.4's proof: `γ` timelike and inextendible in `U = ⋃ U_α`, the `U_α` globally hyperbolic | ⚠ weakened: `γ` any inextensible causal curve of `U`; `≤_U` antisymmetric and `M` Hausdorff; no global hyperbolicity |

## SCOPE (disclosed)

* Moved verbatim from `Causal.CBG.CausalConvex` (its section `Relative`): names, statements and
  proofs unchanged. `Causal.CBG.CausalConvex` imports this module, so its users resolve as before.
* `Causal.NestedCausalities` proved the same proposition as
  `inextensible_ordConnectedComponent_of_le`, with the names of the two open sets exchanged, as
  `inextensible_ordConnectedComponent_on`, and a special case of `curveOn_of_rel_imp` (the
  hypothesis on every open set) as `CurveOn.of_rel_imp`; both are removed there in favour of these.
* The reading of "the corresponding curve segment": the component of `γ⁻¹(W)` containing the
  parameter (`ordConnectedComponent`), as in `Causal.CauchyExtension`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Filter Function

universe u

namespace Causality

section Relative

variable {M : Type u} [TopologicalSpace M]

/-! ### Curves read in two causalities agreeing below an open set -/

/-- A curve of `V` for a relation family is one for any family implying it on the opens of `V`. -/
theorem curveOn_of_rel_imp {r r' : Opens M → M → M → Prop} {V : Opens M} {c : ℝ → M} {a b : ℝ}
    (h : ∀ N : Opens M, N ≤ V → ∀ x y, r N x y → r' N x y) (hc : CurveOn r V c a b) :
    CurveOn r' V c a b where
  mem := hc.mem
  rel t ht N hN htN := by
    obtain ⟨l, u, hl, hu, hrel⟩ := hc.rel t ht N hN htN
    exact ⟨l, u, hl, hu, fun s hs s' hs' h1 h2 h3 => h N hN _ _ (hrel s hs s' hs' h1 h2 h3)⟩

variable {C₁ C₂ : Causality M} {V : Opens M} {I : Set ℝ} {c : ℝ → M}

theorem causalCurveIn_congr_causality
    (h : ∀ N : Opens M, N ≤ V → ∀ x y, C₁.le N x y ↔ C₂.le N x y) :
    C₁.CausalCurveIn V I c ↔ C₂.CausalCurveIn V I c :=
  ⟨fun hc => ⟨hc.nonempty, hc.ordConnected, fun a ha b hb =>
      curveOn_of_rel_imp (fun N hN x y => (h N hN x y).1) (hc.curve a ha b hb)⟩,
    fun hc => ⟨hc.nonempty, hc.ordConnected, fun a ha b hb =>
      curveOn_of_rel_imp (fun N hN x y => (h N hN x y).2) (hc.curve a ha b hb)⟩⟩

theorem extensible_congr_causality
    (h : ∀ N : Opens M, N ≤ V → ∀ x y, C₁.le N x y ↔ C₂.le N x y) :
    C₁.Extensible V I c ↔ C₂.Extensible V I c := by
  constructor
  · rintro ⟨I', c', hcurve, hrep, hgrow⟩
    exact ⟨I', c', (causalCurveIn_congr_causality h).1 hcurve, hrep, hgrow⟩
  · rintro ⟨I', c', hcurve, hrep, hgrow⟩
    exact ⟨I', c', (causalCurveIn_congr_causality h).2 hcurve, hrep, hgrow⟩

/-- Inextensibility in `V` reads only the relations of the open subsets of `V`. -/
theorem inextensible_congr_causality
    (h : ∀ N : Opens M, N ≤ V → ∀ x y, C₁.le N x y ↔ C₂.le N x y) :
    C₁.Inextensible V I c ↔ C₂.Inextensible V I c :=
  and_congr (causalCurveIn_congr_causality h) (not_congr (extensible_congr_causality h))

/-! ### The open set `U` read as a spacetime -/

/-- **The causality of the open set `U`, carried by `M`**: the restriction of `C` to the open
subsets of `U` (`Causality.restrict`), extended to `M` by the diagonal (`LocalCausality.extend`).
Its relations on the opens of `U` are those of `C`; on `M` it relates `x` to `y` iff `x = y` or
`x ≤_U y`. -/
def relativeTo (C : Causality M) (U : Opens M) : Causality M := (C.restrict U).extend

variable {C : Causality M} {U : Opens M}

theorem relativeTo_le_iff {N : Opens M} (hN : N ≤ U) {x y : M} :
    (C.relativeTo U).le N x y ↔ C.le N x y :=
  LocalCausality.extend_le_iff hN

theorem relativeTo_le_top {x y : M} (h : (C.relativeTo U).le ⊤ x y) : x = y ∨ C.le U x y := by
  have h' : (x = y ∧ x ∈ (⊤ : Opens M)) ∨ C.le (⊤ ⊓ U) x y := h
  rcases h' with ⟨rfl, -⟩ | h'
  · exact Or.inl rfl
  · rw [top_inf_eq] at h'
    exact Or.inr h'

/-- `U` read as a spacetime is causal when `≤_U` is antisymmetric. -/
theorem relativeTo_isCausal (hanti : ∀ ⦃x y : M⦄, C.le U x y → C.le U y x → x = y) :
    (C.relativeTo U).IsCausal := by
  intro x y hxy hyx
  rcases relativeTo_le_top hxy with h | h
  · exact h
  rcases relativeTo_le_top hyx with h' | h'
  · exact h'.symm
  exact hanti h h'

/-- A curve of `M` for `U`'s causality passing through `U` stays in `U`. -/
theorem relativeTo_mem {I : Set ℝ} {c : ℝ → M} (hc : (C.relativeTo U).CausalCurveIn ⊤ I c)
    {t : ℝ} (ht : t ∈ I) (hU : c t ∈ U) {s : ℝ} (hs : s ∈ I) : c s ∈ U := by
  rcases le_total t s with h | h
  · rcases relativeTo_le_top (hc.le_of_le ht hs h) with h' | h'
    · rw [← h']; exact hU
    · exact C.le_mem_right h'
  · rcases relativeTo_le_top (hc.le_of_le hs ht h) with h' | h'
    · rw [h']; exact hU
    · exact C.le_mem_left h'

theorem relativeTo_causalCurveIn {I : Set ℝ} {c : ℝ → M}
    (hc : (C.relativeTo U).CausalCurveIn ⊤ I c) {t : ℝ} (ht : t ∈ I) (hU : c t ∈ U) :
    C.CausalCurveIn U I c := by
  have hc' : (C.relativeTo U).CausalCurveIn U I c :=
    ⟨hc.nonempty, hc.ordConnected, fun a ha b hb => CurveOn.restrict (hc.curve a ha b hb) le_rfl
      le_rfl le_top fun s hs => relativeTo_mem hc ht hU (hc.ordConnected.out ha hb hs)⟩
  exact (causalCurveIn_congr_causality fun N hN x y => relativeTo_le_iff hN).1 hc'

/-- An inextensible curve of `U` is an inextensible curve of `M` for `U`'s causality. -/
theorem relativeTo_inextensible_top {I : Set ℝ} {c : ℝ → M} (hc : C.Inextensible U I c) :
    (C.relativeTo U).Inextensible ⊤ I c := by
  have hcongr : ∀ N : Opens M, N ≤ U → ∀ x y, (C.relativeTo U).le N x y ↔ C.le N x y :=
    fun N hN x y => relativeTo_le_iff hN
  refine ⟨((causalCurveIn_congr_causality hcongr).2 hc.1).mono_opens le_top, ?_⟩
  rintro ⟨I', c', hcurve, ⟨φ, h1, h2, h3, h4⟩, hgrow⟩
  obtain ⟨t₀, ht₀⟩ := hc.1.nonempty
  have hmem : c' (φ t₀) ∈ U := by rw [h4 t₀ ht₀]; exact hc.1.mem ht₀
  exact hc.2 ⟨I', c', relativeTo_causalCurveIn hcurve (h2 ht₀) hmem, ⟨φ, h1, h2, h3, h4⟩, hgrow⟩

/-- **The component of an inextensible curve of `U` in an open `W ≤ U`, through a parameter whose
point lies in `W`, is an inextensible curve of `W`** (`M` Hausdorff, `≤_U` antisymmetric). The
relative form of `inextensible_ordConnectedComponent`, which is its case `U = ⊤`. -/
theorem inextensible_ordConnectedComponent_of_le [T2Space M] {W : Opens M}
    (hanti : ∀ ⦃x y : M⦄, C.le U x y → C.le U y x → x = y) (hWU : W ≤ U) {I : Set ℝ}
    {c : ℝ → M} (hc : C.Inextensible U I c) {t₀ : ℝ} (ht₀ : t₀ ∈ I) (hW : c t₀ ∈ W) :
    C.Inextensible W (ordConnectedComponent (I ∩ c ⁻¹' W) t₀) c :=
  (inextensible_congr_causality fun _ hN _ _ => relativeTo_le_iff (hN.trans hWU)).1
    (inextensible_ordConnectedComponent (relativeTo_isCausal hanti)
      (relativeTo_inextensible_top hc) ht₀ hW)

end Relative

end Causality

end Causal
