import Causal.SubExtension

/-!
# Common sub-extensions: the two sorried statements (scaffold remainder)

`lem:C_ext_connexe` — `ETT.tex:1932`. `prop:Cauchy_pgcd` — `ETT.tex:1945`. Neither is marked: each
rests on a tagged `sorry`.

**Split (DEC-73, 2026-11-02).** This file was `CausalScaffold.SubExtension` in full; its sorry-free
part (`IsRigid`, `CommonSubExtension`, `CommonOverExtension`, `IsPgcdCandidate`, `pgcdOpens`,
`pgcdMap`, the kink/timelike-line and point-space witnesses, `c_ext_connexe_of_isCauchySurfaceOn`,
…, and the labels `def:common_sub_extension`, `def:common_over_extension`) moved verbatim to the
strict module `Causal.SubExtension`, which this file imports. What stays here, verbatim, with the
same namespace, sections and variables: `IsCauchyEmbedding.exists_mem_image_inf` (`sorry`) and
its dependants `IsCauchyEmbedding.isCauchySurfaceOn_inf`, `IsCauchyEmbedding.c_ext_connexe`; and
`cauchy_pgcd` (`sorry`). No statement changed.

> If $A$ and $B$ are open subsets of $N$ containing $\phi(M)$ and such that the inclusions
> $\phi(M)\rightarrow A$ and $\phi(M)\rightarrow B$ are Cauchy embeddings, then $A\cap B$ is
> connected.

> There exists a common sub-extension $\pgcd$ of $M_1$ and $M_2$ which is maximal, and it is
> unique up to equivalence.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| singular flat spacetimes, `𝕄≥0`-morphisms | ⚠ reading: topological spacetimes, `IsEMorphism` |
| rigidity (`rem:CBG_analytique`) | ⚠ named: `IsRigid`; not implied by the abstraction (`timelikeLine_not_isRigid`) |
| `M` connected (C_ext_connexe) | ✓ carried |
| `M₀` connected (Cauchy_pgcd): spacetimes are connected, `ETT.tex:1502`, `ETT.tex:1849` | ✓ carried (`[ConnectedSpace M₀]`, part of the setting) |
| carriers of sub- and over-extensions connected, `T2`, second countable (`ETT.tex:255`, `1502`) | ⚠ weakened: not required |
| `Σ ≅` factor of `M ≅ Σ × ℝ` | ⚠ named: a homeomorphism `ψ` |
| every point of `A ∩ B` on an inextensible curve | ⚠ named (model fact) |
| `N` causally arc-connected, curves extend | ⚠ named |

## SCOPE (disclosed)

* `lem:C_ext_connexe` is proved, with no `sorry`, from "`φ(Σ)` is a Cauchy surface of `A ∩ B`"
  carried as a named hypothesis (`c_ext_connexe_of_isCauchySurfaceOn`, in `Causal.SubExtension`).
  `c_ext_connexe` itself takes that step from `isCauchySurfaceOn_inf`, whose uniqueness half is
  proved (`eq_of_mem_image_inter`, in `Causal.SubExtension`) and whose existence half is the
  `sorry` `exists_mem_image_inf`. That `sorry`'d statement is posed in the abstract setting
  without the end-point and extension facts its obstruction names; its truth there is
  unestablished and it **may be false**, so `c_ext_connexe` is no better than it.
* `prop:Cauchy_pgcd` is stated and rests on a `sorry`; proved, in `Causal.SubExtension`: the set
  `ℰ` (`IsPgcdCandidate`), the gluing step (`IsPgcdCandidate.eqOn`, `pgcdMap_eqOn`). Of the
  obstructions its `sorry` names, two are gaps in the paper's argument (φ injective, the Cauchy
  inclusion into the union) and two are obstructions of the abstraction only (no gluing axiom,
  kb/0014; no transport of global hyperbolicity along a local isomorphism without absolute
  minimality).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Filter Function

open scoped Interval

universe u v w

/-! ### The setting of `def:common_sub_extension` (its declarations are in `Causal.SubExtension`) -/

section SubExtension

variable {M₀ M₁ M₂ : Type u} [TopologicalSpace M₀] [TopologicalSpace M₁] [TopologicalSpace M₂]
  {C₀ : Causality M₀} {C₁ : Causality M₁} {C₂ : Causality M₂} {i₁ : M₀ → M₁} {i₂ : M₀ → M₂}

/-! ### `lem:C_ext_connexe` -/

variable {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]
  {C : Causality M} {D : Causality N} {φ : M → N}

/-- **The step of `lem:C_ext_connexe` the paper asserts without proof**, existence half: every
inextensible causal curve of `A ∩ B` meets `φ(Σ)` ("the map `M → A ∩ B` is a Cauchy embedding").
**This abstract statement may be false**: it is posed without the facts (1)–(3) its `sorry`
names, which hold for Lorentzian manifolds but are neither proved nor assumed for topological
spacetimes. Nothing here establishes its truth in the abstract setting. -/
theorem IsCauchyEmbedding.exists_mem_image_inf [T2Space N] (hφ : IsCauchyEmbedding C D φ)
    {A B : Opens N} (hA : IsCauchyInclusion D hφ.rangeOpens A)
    (hB : IsCauchyInclusion D hφ.rangeOpens B) {S : Set M} (hS : C.IsCauchySurface S)
    {I : Set ℝ} {c : ℝ → N} (hc : D.Inextensible (A ⊓ B) I c) : (c '' I ∩ φ '' S).Nonempty := by
  sorry -- SORRY(lem:C_ext_connexe): an inextensible causal curve of `A ∩ B` is in general extensible in `A` and in `B`; that it meets `φ(Σ)` needs (1) every causal curve of `A` (resp. `B`) over an interval to lie on an inextensible one of `A` (`CurvesExtend` relative to an open set, a Zorn-type existence), (2) the two extensions to leave `A ∩ B` through one end point, which needs that end point to exist in `A` and in `B` (a limit along the curve) and to be unique (Hausdorff), and (3) at an end point in `A ∩ B`, a short causal curve inside `A ∩ B` (`J^±_{A∩B}(p) ≠ {p}` with local causal arc-connectedness). None of the three is proved for topological spacetimes nor carried here as a hypothesis, and the paper gives no argument; in this abstract setting the statement may be false (its truth is unestablished), and `c_ext_connexe` rests on it — its sorry-free core is `c_ext_connexe_of_isCauchySurfaceOn`

/-- "`φ(Σ)` is a Cauchy surface of `A ∩ B`" (`ETT.tex:1940–1941`): uniqueness is proved
(`eq_of_mem_image_inter`), existence is the paper's unproved step (`exists_mem_image_inf`). -/
theorem IsCauchyEmbedding.isCauchySurfaceOn_inf [T2Space N] (hφ : IsCauchyEmbedding C D φ)
    {A B : Opens N} (hA : IsCauchyInclusion D hφ.rangeOpens A)
    (hB : IsCauchyInclusion D hφ.rangeOpens B) {S : Set M} (hS : C.IsCauchySurface S)
    (hDac : D.CausallyArcConnected) (hDext : D.CurvesExtend) :
    D.IsCauchySurfaceOn (A ⊓ B) (φ '' S) := by
  intro I c hc
  obtain ⟨x, hx⟩ := hφ.exists_mem_image_inf hA hB hS hc
  exact ⟨x, hx, fun y hy => hφ.eq_of_mem_image_inter hS hDac hDext hc.1 y hy x hx⟩

/-- `lem:C_ext_connexe`, abstractly: `M` connected, `φ` a Cauchy extension, `A, B` open sets of
`N` into which the inclusions of `φ(M)` are Cauchy embeddings; then `A ∩ B` is connected. Named
hypotheses: the splitting `ψ` of `theo:geroch_sing` (for the connectedness of `Σ`) and, as a
model fact, that every point of `A ∩ B` lies on an inextensible causal curve of `A ∩ B`. The
proof rests on `isCauchySurfaceOn_inf`, hence on the `sorry` `exists_mem_image_inf`, whose
abstract statement may be false; the sorry-free core is `c_ext_connexe_of_isCauchySurfaceOn`. -/
theorem IsCauchyEmbedding.c_ext_connexe [T2Space N] [ConnectedSpace M]
    (hφ : IsCauchyEmbedding C D φ) {A B : Opens N} (hA : IsCauchyInclusion D hφ.rangeOpens A)
    (hB : IsCauchyInclusion D hφ.rangeOpens B) {S : Set M} (hS : C.IsCauchySurface S)
    (ψ : S × ℝ ≃ₜ M) (hDac : D.CausallyArcConnected) (hDext : D.CurvesExtend)
    (hthrough : ∀ x ∈ A ⊓ B, ∃ (I : Set ℝ) (c : ℝ → N), D.Inextensible (A ⊓ B) I c ∧ x ∈ c '' I) :
    IsConnected ((A ⊓ B : Opens N) : Set N) :=
  hφ.c_ext_connexe_of_isCauchySurfaceOn hA hB ψ (hφ.isCauchySurfaceOn_inf hA hB hS hDac hDext)
    hthrough

/-! ### `prop:Cauchy_pgcd` -/

/-- `prop:Cauchy_pgcd`, abstractly, with rigidity (`rem:CBG_analytique`) as a named
hypothesis: two Cauchy extensions of `M₀` have a maximal common sub-extension, unique up to
equivalence. `M₀` is connected, as every spacetime of the section is (`ETT.tex:1849`,
`def:singular_spacetime` at `ETT.tex:1502`): part of the setting, not a strengthening. -/
theorem cauchy_pgcd [ConnectedSpace M₀] [T2Space M₁] [T2Space M₂] (h₁ : IsCauchyEmbedding C₀ C₁ i₁)
    (h₂ : IsCauchyEmbedding C₀ C₂ i₂) (hrig : IsRigid C₁ C₂) :
    (∃ X : CommonSubExtension C₀ C₁ C₂ i₁ i₂, X.IsMaximal) ∧
      ∀ X Y : CommonSubExtension C₀ C₁ C₂ i₁ i₂, X.IsMaximal → Y.IsMaximal → X.Equivalent Y := by
  sorry -- SORRY(prop:Cauchy_pgcd): the step "(∧, φ) ∈ ℰ, hence ∧ is a common sub-extension" is not argued in the paper on two points: (1) condition (b) of ℰ does not ask φ_M injective and nothing shows φ injective, so ∧ → M₂ is not shown to be a Cauchy embedding (WP-4; a gap in the argument, not a refutation: injectivity is plausibly recoverable); (2) the inclusion of i₁(M₀) into the union ∧ = ⋃ M is not shown to be a Cauchy embedding: neither the global hyperbolicity of ∧ nor that i₁(Σ₀) meets every inextensible curve of ∧ follows from the same facts for each M. Two further obstructions belong to the abstraction, not to the paper's proof: (3) the library's causality has no gluing axiom (kb/0014), so the strong-morphism condition of φ on ∧ does not follow from its restrictions to the M; (4) maximality and uniqueness need (b(N), c ∘ b⁻¹) ∈ ℰ for a common sub-extension (N, a, b, c), i.e. b(N) with the causality restricted from M₁ globally hyperbolic, which a local isomorphism of non-local causalities does not transport without absolute minimality. The gluing step also uses lem:C_ext_connexe, itself resting on the sorry exists_mem_image_inf

end SubExtension

end Causal
