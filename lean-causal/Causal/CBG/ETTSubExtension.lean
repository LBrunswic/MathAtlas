import Causal.CBG.ETTSection4

/-!
# ETT §4.3 in ETT's own terms: `lem:C_ext_connexe` and `prop:Cauchy_pgcd` over the CBG geometry

Target `T-ett-subextension` (2026-11-20). Anchors the two rows of ETT §4.3 (common
sub-extensions) to the sorry-free CBG development (`Causal.CBG.*`, DEC-60), as `T-ett-cbg-anchor`
did for ten §4 rows (`Causal.CBG.ETTSection4`). **No label is marked**: everything holds over an
abstract `Geometry` (DEC-60) whose singular `E₀` instance is not in this package
(`T-ett-cbg-e0`), so each row is partial. Cited, unmarked: `lem:C_ext_connexe` — `ETT.tex:1932`,
`prop:Cauchy_pgcd` — `ETT.tex:1945`, `def:common_sub_extension` — `ETT.tex:1914`.

> Let $M$ be a connected globally hyperbolic singular flat spacetime and let
> $\phi:M\rightarrow N$ be a Cauchy extension. If $A$ and $B$ are open subsets of $N$ containing
> $\phi(M)$ and such that the inclusions $\phi(M)\rightarrow A$ and $\phi(M)\rightarrow B$ are
> Cauchy embeddings, then $A\cap B$ is connected. (`ETT.tex:1933–1936`)

> Let $M_0$ be a globally hyperbolic singular flat spacetime and let $M_0\xrightarrow{i_1} M_1$
> and $M_0\xrightarrow{i_2} M_2$ be two Cauchy extensions of $M_0$. There exists a common
> sub-extension $\pgcd$ of $M_1$ and $M_2$ which is maximal, and it is unique up to equivalence.
> (`ETT.tex:1946–1948`)

> Thus $(\pgcd,\phi)\in \mathcal E$, and it is by construction the largest element of
> $\mathcal E$. If $(N,a,b,c)$ is a common sub-extension of $M_1$ and $M_2$, then
> $\left(b(N),c\circ b^{-1}\right)\in \mathcal E$, so $b(N)\subset \pgcd$ and
> $c\circ b^{-1}=\phi_{|b(N)}$ (`ETT.tex:1960–1965`)

## What is proved (no `sorry` in this file)

* `lem:C_ext_connexe`: `ett_c_ext_connexe` (the statement, `M`, `N` spacetimes of the geometry),
  `ett_c_ext_connexe_dev` (the same for a development, ETT's "Cauchy extension"),
  `ett_c_ext_connexe_curves` (the proof's last sentence: every point of `A ∩ B` lies on an
  inextensible causal curve of `A ∩ B` meeting `φ(Σ)`, at most once), `ett_c_ext_connexe_convex`
  (`A ∩ B` causally convex in `N` and globally hyperbolic); witness `flat_c_ext_connexe_hypotheses`.
* `prop:Cauchy_pgcd`: `ett_cauchy_pgcd` (a maximal common sub-extension exists, it receives a
  unique morphism from every common sub-extension, and any two maximal ones are equivalent),
  `CommonSubDev.isCauchyEmbedding_b`, `CommonSubDev.isCauchyEmbedding_c` (the legs of a
  `CommonSubDev` are Cauchy embeddings, so it is `def:common_sub_extension`),
  `CommonSubDev.IsMorphism.unique`, `ett_cauchy_pgcd_range` (the image of the maximal one in `M₁`
  is the union `⋃ ℰ` of the proof); witness `flat_cauchy_pgcd`.

## Hypothesis checklist

| paper | here |
|---|---|
| "spacetime means singular flat spacetime" (`ETT.tex:1852`) | ⚠ strengthened: spacetimes of an abstract `Geometry` (DEC-60); the `E₀` instance is owed (`T-ett-cbg-e0`). Fields used: A2 for `lem:C_ext_connexe`; A1, A2 and the structure laws for `prop:Cauchy_pgcd`; **no** A3/A4 |
| `lem:C_ext_connexe`: `M` connected | ✓ carried `[ConnectedSpace M]` |
| `lem:C_ext_connexe`: `M` GH, singular flat | ✓ GH in `IsCauchyEmbedding`; ⚠ weakened: `M` need not be `T2` or second countable |
| `lem:C_ext_connexe`: `N` singular flat (`T2`, connected, SC, `ETT.tex:255`, `1502`) | ✓ carried |
| `lem:C_ext_connexe`: `φ` a Cauchy extension | ✓ `IsCauchyEmbedding` (DEC-17); ⚠ weakened: `φ` need not be a structure morphism |
| "the inclusions `φ(M) → A`, `φ(M) → B` are Cauchy embeddings" | ✓ `IsCauchyInclusion` (kb/0001, DEC-17; the inclusion is a structure morphism, `Geometry.isMor_val`); ⚠ weakened: `A`, `B` need not be connected (nor second countable), as a Cauchy embedding between singular flat spacetimes would force |
| `prop:Cauchy_pgcd`: `M₀` GH singular flat, connected (`ETT.tex:1502`) | ✓ `[ConnectedSpace M₀]`, GH in `Dev`; ⚠ weakened: `M₀` need not be `T2` or SC |
| `prop:Cauchy_pgcd`: `i₁`, `i₂` Cauchy extensions | ✓ `N₁ N₂ : Dev 𝔊 s₀` |
| common sub-extension, its morphisms, maximal, equivalent (`ETT.tex:1914–1929`) | ✓ `CommonSubDev`, `.IsMorphism` (`isMorphism_iff`), `.IsMaximal`, `.Equivalent`; legs Cauchy embeddings (`isCauchyEmbedding_b`, `_c`) |
| rigidity (`rem:CBG_analytique`) | ✓ the geometry's A1 `Geometry.rigid` (DEC-60), not `SubExtension.IsRigid` |

## SCOPE (disclosed)

* **What stands in for `E₀`.** An abstract `Geometry` (DEC-60). For these two rows only the
  fields A1 (`rigid`) and A2 (`singularFlatAxioms`, `curvesExtend`, `timeFunction`) and the
  structure laws (`isMor_*`, `restrict`, `isMor_corestrict_iff`, `absolutelyMinimalOn`) are used;
  neither A3 (`germExt_*`) nor A4 (`slice_*`), hence none of gx's BTZ obligations of
  `Geometry.ofLocalModelOfBTZ`. The flat geometry (`flatGeometry d`) inhabits every hypothesis
  (`flat_c_ext_connexe_hypotheses`, `flat_cauchy_pgcd`); the rows stay partial until the `E₀`
  instance (`T-ett-cbg-e0`).
* **`lem:C_ext_connexe` is proved by another route than the paper's.** The middle sentence
  ("`φ(Σ)` is a Cauchy surface of `A ∩ B`", `ETT.tex:1940–1941`) is **not** proved: only its
  uniqueness half (`ett_c_ext_connexe_curves`, second conjunct). The connectedness uses
  `φ(M) ⊆ A ∩ B` connected and the paper's last sentence (`c_ext_connexe_of_connectedSpace`,
  `CBG/CausalConvex`), so neither the splitting of `M` (`theo:geroch_sing`) nor a connected
  Cauchy surface is needed.
* The abstract scaffold forms (`IsCauchyEmbedding.exists_mem_image_inf`, and `cauchy_pgcd` with the
  causal `IsRigid`, retired 2026-11-21) are not used. The second was
  refuted, by non-local witnesses on `ℝ`, in `Causal.CBG.SubExtensionAbstract`
  (`not_cauchyPgcdAbstract` with the library's directional `Equivalent`;
  `cauchyPgcdAbstract_counterexample_symm` under every reading of "equivalent" that asks for a
  morphism between the two; the equivalence relation generated by bijective morphisms is not
  refuted, see that module's SCOPE); the first is not refuted.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Filter Function

universe u

namespace CBG

/-! ### `lem:C_ext_connexe` -/

section CExtConnexe

variable {𝔊 : Geometry.{u}} {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]

/-- **`lem:C_ext_connexe` over the geometry** (`ETT.tex:1932–1937`): `M` connected, `N` an
admissible spacetime (Hausdorff, connected, second countable), `φ : M → N` a Cauchy embedding;
`A`, `B` open sets of `N` containing `φ(M)` with `φ(M) → A`, `φ(M) → B` Cauchy inclusions. Then
`A ∩ B` is connected. -/
theorem ett_c_ext_connexe [ConnectedSpace M] [T2Space N] [ConnectedSpace N]
    [SecondCountableTopology N] (s : 𝔊.Str M) (t : 𝔊.Str N) {φ : M → N}
    (hφ : IsCauchyEmbedding (𝔊.causality s) (𝔊.causality t) φ) {A B : Opens N}
    (hA : IsCauchyInclusion (𝔊.causality t) hφ.rangeOpens A)
    (hB : IsCauchyInclusion (𝔊.causality t) hφ.rangeOpens B) :
    IsConnected ((A ⊓ B : Opens N) : Set N) :=
  hφ.c_ext_connexe_of_connectedSpace hA hB (𝔊.curvesExtend t hφ.globallyHyperbolic_target)

/-- **`lem:C_ext_connexe`, the proof's last sentence** (`ETT.tex:1941–1942`): for every Cauchy
surface `Σ` of `M`, every point of `A ∩ B` lies on an inextensible causal curve of `A ∩ B` which
meets `φ(Σ)`, and every causal curve of every open set meets `φ(Σ)` at most once. -/
theorem ett_c_ext_connexe_curves [T2Space N] [ConnectedSpace N] [SecondCountableTopology N]
    (s : 𝔊.Str M) (t : 𝔊.Str N) {φ : M → N}
    (hφ : IsCauchyEmbedding (𝔊.causality s) (𝔊.causality t) φ) {A B : Opens N}
    (hA : IsCauchyInclusion (𝔊.causality t) hφ.rangeOpens A)
    (hB : IsCauchyInclusion (𝔊.causality t) hφ.rangeOpens B) {S : Set M}
    (hS : (𝔊.causality s).IsCauchySurface S) :
    (∀ x ∈ A ⊓ B, ∃ (I : Set ℝ) (c : ℝ → N), (𝔊.causality t).Inextensible (A ⊓ B) I c ∧
      x ∈ c '' I ∧ (c '' I ∩ φ '' S).Nonempty) ∧
    ∀ (W : Opens N) (I : Set ℝ) (c : ℝ → N), (𝔊.causality t).CausalCurveIn W I c →
      ∀ x ∈ c '' I ∩ φ '' S, ∀ y ∈ c '' I ∩ φ '' S, x = y := by
  have hext := 𝔊.curvesExtend t hφ.globallyHyperbolic_target
  refine ⟨fun x hx => hφ.exists_inextensible_inf hA hB hS hext hx, fun W I c hc => ?_⟩
  exact hφ.eq_of_mem_image_inter hS (𝔊.singularFlatAxioms t).causallyArcConnected hext hc

/-- **`A ∩ B` is causally convex in `N` and globally hyperbolic**, in the setting of
`lem:C_ext_connexe` (the part of "`M → A ∩ B` is a Cauchy embedding" which is proved). -/
theorem ett_c_ext_connexe_convex [T2Space N] [ConnectedSpace N] [SecondCountableTopology N]
    (s : 𝔊.Str M) (t : 𝔊.Str N) {φ : M → N}
    (hφ : IsCauchyEmbedding (𝔊.causality s) (𝔊.causality t) φ) {A B : Opens N}
    (hA : IsCauchyInclusion (𝔊.causality t) hφ.rangeOpens A)
    (hB : IsCauchyInclusion (𝔊.causality t) hφ.rangeOpens B) :
    (𝔊.causality t).CausallyConvexIn ((A ⊓ B : Opens N) : Set N) ⊤ ∧
      (𝔊.causality t).GloballyHyperbolicOn (A ⊓ B) :=
  hφ.inf_causallyConvexIn hA hB (𝔊.singularFlatAxioms t).causallyArcConnected
    (𝔊.curvesExtend t hφ.globallyHyperbolic_target)

end CExtConnexe

section CExtConnexeDev

variable {𝔊 : Geometry.{u}} {M₀ : Type u} [TopologicalSpace M₀] {s₀ : 𝔊.Str M₀}

/-- **`lem:C_ext_connexe` for a development** (ETT's "Cauchy extension" `φ : M → N` is a `Dev`):
`A ∩ B` is connected. -/
theorem ett_c_ext_connexe_dev [ConnectedSpace M₀] (N : Dev 𝔊.toPreGeometry s₀)
    {A B : Opens N.carrier}
    (hA : IsCauchyInclusion (𝔊.causality N.str) N.isCauchyEmbedding.rangeOpens A)
    (hB : IsCauchyInclusion (𝔊.causality N.str) N.isCauchyEmbedding.rangeOpens B) :
    IsConnected ((A ⊓ B : Opens N.carrier) : Set N.carrier) :=
  ett_c_ext_connexe s₀ N.str N.isCauchyEmbedding hA hB

end CExtConnexeDev

/-! ### `prop:Cauchy_pgcd` -/

section Pgcd

variable {𝔊 : Geometry.{u}} {M₀ : Type u} [TopologicalSpace M₀] {s₀ : 𝔊.Str M₀}
  {N₁ N₂ : Dev 𝔊.toPreGeometry s₀}

namespace CommonSubDev

/-- **The leg `M → M₁` of a common sub-development is a Cauchy embedding**
(`def:common_sub_extension`, `ETT.tex:1917–1918`): it carries `ι_X(Σ)` onto `ι₁(Σ)`. -/
theorem isCauchyEmbedding_b (X : CommonSubDev N₁ N₂) :
    IsCauchyEmbedding (𝔊.causality X.X.str) (𝔊.causality N₁.str) X.b := by
  obtain ⟨S, hS, -⟩ := X.X.isCauchyEmbedding.exists_cauchy
  refine ⟨X.X.causality_globallyHyperbolic, N₁.causality_globallyHyperbolic,
    𝔊.isEMorphismOn_of_isMor X.isMorphism_b.1, X.injective_b, X.X.emb '' S,
    X.X.isCauchyEmbedding.isCauchySurface_image hS, ?_⟩
  rw [← image_comp, X.isMorphism_b.2]
  exact N₁.isCauchyEmbedding.isCauchySurface_image hS

/-- **The leg `M → M₂` of a common sub-development is a Cauchy embedding**. -/
theorem isCauchyEmbedding_c (X : CommonSubDev N₁ N₂) :
    IsCauchyEmbedding (𝔊.causality X.X.str) (𝔊.causality N₂.str) X.c := by
  obtain ⟨S, hS, -⟩ := X.X.isCauchyEmbedding.exists_cauchy
  refine ⟨X.X.causality_globallyHyperbolic, N₂.causality_globallyHyperbolic,
    𝔊.isEMorphismOn_of_isMor X.isMorphism_c.1, X.injective_c, X.X.emb '' S,
    X.X.isCauchyEmbedding.isCauchySurface_image hS, ?_⟩
  rw [← image_comp, X.isMorphism_c.2]
  exact N₂.isCauchyEmbedding.isCauchySurface_image hS

/-- A morphism of common sub-developments is unique: it is determined by the injective leg `b` of
its target. -/
theorem IsMorphism.unique {X Y : CommonSubDev N₁ N₂} {f g : X.X.carrier → Y.X.carrier}
    (hf : X.IsMorphism Y f) (hg : X.IsMorphism Y g) : f = g :=
  funext fun x => Y.injective_b ((congrFun hf.2.1 x).trans (congrFun hg.2.1 x).symm)

end CommonSubDev

/-- **`prop:Cauchy_pgcd` over the geometry, in ETT's words, with the proof's universal property**
(`ETT.tex:1945–1966`): for two Cauchy extensions `N₁`, `N₂` of a connected `M₀`, a common
sub-extension `∧` exists which is maximal and receives a unique morphism from every common
sub-extension ("`b(N) ⊂ ∧` and `c ∘ b⁻¹ = φ`"), and any two maximal common sub-extensions are
equivalent. -/
theorem ett_cauchy_pgcd [ConnectedSpace M₀] (N₁ N₂ : Dev 𝔊.toPreGeometry s₀) :
    (∃ X : CommonSubDev N₁ N₂, X.IsMaximal ∧
      ∀ Y : CommonSubDev N₁ N₂, ∃! f : Y.X.carrier → X.X.carrier, Y.IsMorphism X f) ∧
    ∀ X Y : CommonSubDev N₁ N₂, X.IsMaximal → Y.IsMaximal → X.Equivalent Y := by
  refine ⟨⟨mcghdSubDev N₁ N₂, mcghdSubDev_isMaximal, fun Y => ?_⟩,
    (cauchy_pgcd_geometry N₁ N₂).2⟩
  exact ⟨_, Y.isMorphism_toMcghd, fun g hg => hg.unique Y.isMorphism_toMcghd⟩

/-- **The image of the maximal common sub-extension in `M₁` is the union `⋃ ℰ`** of the proof
(`ETT.tex:1956`, `mcghdOpens`), and every maximal common sub-extension has that image. -/
theorem ett_cauchy_pgcd_range [ConnectedSpace M₀] {X : CommonSubDev N₁ N₂} (hX : X.IsMaximal) :
    range X.b = (mcghdOpens N₁ N₂ : Set N₁.carrier) := by
  have hbij := hX.bijective_toMcghd
  have hfac := mcghd_factor X.X X.isMorphism_b X.injective_b X.isMorphism_c
  ext y
  constructor
  · rintro ⟨w, rfl⟩; exact hfac.1 w
  · intro hy
    obtain ⟨w, hw⟩ := hbij.2 ⟨y, hy⟩
    exact ⟨w, congrArg Subtype.val hw⟩

end Pgcd

/-! ### Witnesses in the flat geometry (kb/0011) -/

section Flat

variable (d : ℕ)

/-- **The hypotheses of `lem:C_ext_connexe` are inhabited** in the flat geometry: over
`M₀ = 𝕄^{1,d}`, a development `N` with open sets `A = ι(M₀)` and `B = N` Cauchy-including
`ι(M₀)` (they may coincide: whether `ι` is onto is not decided here). -/
theorem flat_c_ext_connexe_hypotheses :
    ∃ (N : Dev (flatGeometry d).toPreGeometry
      (flatStr flat_isCompact_Jplus_inter_Jminus flat_isCompact_Jminus_inter_Jplus (Minkowski d)))
      (A B : Opens N.carrier),
      IsCauchyInclusion ((flatGeometry d).causality N.str) N.isCauchyEmbedding.rangeOpens A ∧
      IsCauchyInclusion ((flatGeometry d).causality N.str) N.isCauchyEmbedding.rangeOpens B := by
  obtain ⟨N, -⟩ := flat_cbg_minkowski (d := d)
  obtain ⟨-, hG, -, S, hS, hS1, -⟩ := N.isCauchyInclusion_range_top
  exact ⟨N, _, ⊤, ⟨le_rfl, hG, hG, S, hS, hS1, hS1⟩, N.isCauchyInclusion_range_top⟩

/-- **The hypotheses of `prop:Cauchy_pgcd` are inhabited** in the flat geometry: a development of
`𝕄^{1,d}`, and a maximal common sub-extension of it with itself. -/
theorem flat_cauchy_pgcd :
    ∃ N : Dev (flatGeometry d).toPreGeometry
      (flatStr flat_isCompact_Jplus_inter_Jminus flat_isCompact_Jminus_inter_Jplus (Minkowski d)),
      ∃ X : CommonSubDev N N, X.IsMaximal := by
  obtain ⟨N, -⟩ := flat_cbg_minkowski (d := d)
  exact ⟨N, (ett_cauchy_pgcd N N).1.imp fun X h => h.1⟩

end Flat

end CBG

end Causal
