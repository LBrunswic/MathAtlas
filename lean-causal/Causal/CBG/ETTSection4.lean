import Causal.CBG.Maximal
import Causal.SingularGeroch
import Causal.Flat.CBG

/-!
# ETT §4 in ETT's own terms: the CBG development read as `theo:CBG` and its lemmas

Target `T-ett-cbg-anchor` (2026-11-20). Bridges the sorry-free CBG development (`Causal.CBG.*`,
`docs/CBG-DESIGN.md`) to ETT §4 in the paper's own setting: two Cauchy extensions `M₁`, `M₂` of
`M₀`, a common sub-extension `N` (`CommonSubDev`, `j₁ = b`, `j₂ = c`), `f = j₂ ∘ j₁⁻¹`, and the
**literal** `C` (pairs with non-separated images in `(M₁ ⊔ M₂)/N`, `Gluing.C b c`). **No label is
marked**: everything holds over an abstract `Geometry` (DEC-60) whose singular `E₀` instance is not
in this package (DEC-134; the CBG geometry of `E₀` is `T-ett-cbg-e0`), so each row is partial. Cited, unmarked:
`theo:CBG` — `ETT.tex:1884`, `rem:CBG_analytique` — `ETT.tex:1903`, `prop:ppcm_Cauchy` —
`ETT.tex:1994`, `lem:corresponding_K` — `ETT.tex:2100`, `cor:ext_continue` — `ETT.tex:2144`,
`cor:model_corresponding` — `ETT.tex:2158`, `prop:Cauchy_non_max` — `ETT.tex:2178`,
`prop:C_connexe` — `ETT.tex:2240`, `prop:Cauchy_point_min` — `ETT.tex:2270`,
`rem:CBG_manquant` — `ETT.tex:2343`. No `sorry` in this file.

> Let $M_0$ be a globally hyperbolic singular flat spacetime. Then $M_0$ admits a maximal Cauchy
> extension, and that extension is unique up to isomorphism. (`ETT.tex:1885–1886`)

> two $\mass{\geq0}$-morphisms defined on a connected manifold and agreeing on a non-empty open
> set agree everywhere (`ETT.tex:1908–1909`)

> If there exists $(p,q)\in C$ with $J_{M_1}(\Sigma_1,p)\setminus\{p\}\subset j_1(N)$, then $N$ is
> not maximal among the common sub-extensions of $M_1$ and $M_2$. (`ETT.tex:2179–2180`)

> If $C\neq \emptyset$, then there exists $(p',q')\in C$ with
> $J_{M_1}(\Sigma_1,p')\setminus\{p'\}\subset j_1(N)$. (`ETT.tex:2271–2272`)

## What is proved (all sorry-free; axioms `propext`, `Classical.choice`, `Quot.sound`)

* `theo:CBG`: `theo_CBG` (an ETT-maximal Cauchy extension exists, is universal, and every maximal
  one is isomorphic to it by a unique morphism), `theo_CBG_of_modelMeasures` (the Cauchy surface
  from `theo:geroch_sing`); `Dev.IsMorphism.injective` (every morphism of extensions is a Cauchy
  embedding), so the readings of "maximal" agree (`Dev.isCEMaximal_iff`).
* `rem:CBG_analytique`: `Geometry.rigid_univ` (the field A1 in the remark's words).
* The setting: `CommonSubDev.U`, `.f`, `.cghdData` (ETT's setting is Sbierski's CGHD setting),
  `.mem_C_iff` (literal `C` = Sbierski's corresponding pairs), `.mem_Cdist_iff`.
* `ett_corresponding_K` (+ `_past`), `ett_ext_continue`, `ett_ext_germ`, `ett_model_corresponding`,
  `ett_C_connexe`, `ett_cauchy_point_min` (+ `_symm`, `_literal`), `ett_cauchy_non_max`,
  `ett_cauchy_non_max_literal_false` (+ `_flat`), `ett_ppcm_Cauchy` (`CommonOverDev`, `ppcmOver`),
  `Dev.card_le_continuum`, `ett_maximal_secondCountable`.

## Hypothesis checklist

| paper | here |
|---|---|
| "spacetime means singular flat spacetime" (`ETT.tex:1852`) | ⚠ strengthened: an abstract `Geometry` (DEC-60); the `E₀` instance is owed (`T-ett-cbg-e0`, and gx's `GermExtFutureBTZ`, `GermExtPastBTZ`, `SliceFutureBTZ` of `Geometry.ofLocalModelOfBTZ`) |
| `M₀` globally hyperbolic (`ETT.tex:1885`) | ⚠ strengthened: plus a Cauchy surface (`theo_CBG`) or the model measures (`theo_CBG_of_modelMeasures`, the named hypothesis of `theo:geroch_sing`); `M₀` T2, connected, second countable (ETT's spacetimes) |
| "maximal" Cauchy extension (never defined) | ✓ all readings proved and equivalent: Cauchy embeddings out bijective (`IsCEMaximal`), morphisms out bijective (`IsETTMaximal`), universal (DEC-59) |
| `C` "not separated" (`ETT.tex:2011–2012`) | ✓ literal `Gluing.C`; where the literal reading is false (`prop:Cauchy_non_max`) or empty (`prop:Cauchy_point_min`), `Cdist` (OQ-14, `rem:non_separe_cas`) |
| `prop:Cauchy_non_max`: `J(Σ₁,p) ∖ {p} ⊂ j₁(N)` | ⚠ weakened: dropped (Lemma 3.9 supplies it) |
| `prop:ppcm_Cauchy`: `pgcd` in `defi:ppcm` | reading: the MCGHD (`prop:Cauchy_pgcd`, `cauchy_pgcd_geometry`) |

## SCOPE (disclosed)

* Over the abstract geometry, `cor:ext_continue`, `cor:model_corresponding`, `prop:C_connexe`
  (openness), `prop:Cauchy_non_max`, `prop:ppcm_Cauchy` and `theo:CBG` rest on the fields A3
  (`germExt_*`, Sbierski Lemma 3.8) and A4 (`slice_*`), discharged off the BTZ locus by
  `Geometry.ofLocalModelOfBTZ` and everywhere for the regular flat model (`flat_cbg`); at BTZ
  points they are gx's open obligations. `lem:corresponding_K` uses A2 only.
* `prop:C_connexe`'s closedness is immediate for the literal `C` (the closure of the graph).
* `prop:Cauchy_point_min` printed is true but empty (`ett_cauchy_point_min_literal`); the printed
  `prop:Cauchy_non_max` is false (`ett_cauchy_non_max_literal_false`, inhabited by `_flat`).
* `ett_maximal_secondCountable` is immediate from `Dev`; its content is `maxSpace_secondCountable`
  through the field `secondCountable_of_cauchy` (gx's (vi) for `E₀`).
* Imports `Causal.Flat.CBG` for the flat witness only.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Filter Function

universe u

namespace CBG

/-! ### General facts on developments -/

section General

variable {𝔊 : Geometry.{u}} {M₀ : Type u} [TopologicalSpace M₀] {s₀ : 𝔊.Str M₀}

/-- **Every morphism of developments is injective**, hence a Cauchy embedding (Lemma 3.3 with the
time function of the source, `Geometry.timeFunction`): `f` is injective on the Cauchy surface
`ι_N(Σ)` and maps it onto the acausal `ι_{N'}(Σ)`. -/
theorem Dev.IsMorphism.injective {N N' : Dev 𝔊.toPreGeometry s₀} {f : N.carrier → N'.carrier}
    (hf : N.IsMorphism N' f) : Injective f := by
  obtain ⟨T, hTc, hTs⟩ := N.causality_hasTimeFunction
  obtain ⟨S, hS, -⟩ := N.isCauchyEmbedding.exists_cauchy
  have hSN := N.isCauchyEmbedding.isCauchySurface_image hS
  have himg : f '' (N.emb '' S) = N'.emb '' S := by
    rw [← image_comp]; exact image_congr fun x _ => congrFun hf.2 x
  have hinjS : InjOn f (N.emb '' S) := by
    rintro _ ⟨a, -, rfl⟩ _ ⟨b, -, rfl⟩ hab
    have : N'.emb a = N'.emb b := (congrFun hf.2 a).symm.trans (hab.trans (congrFun hf.2 b))
    rw [N'.isCauchyEmbedding.injective this]
  have hac : (𝔊.causality N'.str).IsAcausal (f '' (N.emb '' S)) := by
    rw [himg]
    exact (N'.isCauchyEmbedding.isCauchySurface_image hS).isAcausal
      N'.causality_causallyArcConnected N'.causality_curvesExtend
  have hI : InjOn f ((⊤ : Opens N.carrier) : Set N.carrier) :=
    injOn_of_injOn_cauchy (𝔊.isEMorphismOn_of_isMor hf.1) hTc hTs hSN hinjS hac
      N'.causality_globallyHyperbolic.1
  exact fun x y hxy => hI trivial trivial hxy

/-- **`rem:CBG_analytique`, the rigidity sentence in ETT's words** (`ETT.tex:1908–1909`): two
structure morphisms defined on a connected space, into a Hausdorff one, agreeing on a non-empty
open set, agree everywhere. It is the field `Geometry.rigid` (A1) at `V = ⊤`. -/
theorem Geometry.rigid_univ {M N : Type u} [TopologicalSpace M] [TopologicalSpace N] [T2Space N]
    [ConnectedSpace M] (s : 𝔊.Str M) (t : 𝔊.Str N) {f g : M → N} (hf : 𝔊.IsMor s t ⊤ f)
    (hg : 𝔊.IsMor s t ⊤ g) {O : Set M} (hO : IsOpen O) (hne : O.Nonempty) (h : EqOn f g O) :
    f = g := by
  have hV : IsConnected ((⊤ : Opens M) : Set M) := by
    rw [Opens.coe_top]; exact isConnected_univ
  funext z
  exact 𝔊.rigid s t ⊤ hV f g hf hg ⟨O, hO⟩ le_top hne h (show z ∈ (⊤ : Opens M) from trivial)

end General

/-! ### `theo:CBG` in ETT's words -/

section TheoCBG

variable {𝔊 : Geometry.{u}} {M₀ : Type u} [TopologicalSpace M₀] {s₀ : 𝔊.Str M₀}

/-- **ETT-maximality against Cauchy embeddings**: every *injective* morphism of developments out
of `Mbar` (a Cauchy embedding commuting with the embeddings of `M₀`, `ETT.tex:1859–1862`) is
bijective — the reading of "maximal Cauchy extension" by analogy with `def:common_sub_extension`
(`ETT.tex:1928–1929`), whose morphisms are Cauchy embeddings. -/
def Dev.IsCEMaximal (Mbar : Dev 𝔊.toPreGeometry s₀) : Prop :=
  ∀ (N : Dev 𝔊.toPreGeometry s₀) (f : Mbar.carrier → N.carrier), Mbar.IsMorphism N f →
    Injective f → Bijective f

/-- The two readings of ETT-maximality coincide: every morphism of developments is injective
(`Dev.IsMorphism.injective`). -/
theorem Dev.isCEMaximal_iff (Mbar : Dev 𝔊.toPreGeometry s₀) :
    Mbar.IsCEMaximal ↔ Mbar.IsETTMaximal :=
  ⟨fun h N f hf => h N f hf hf.injective, fun h N f hf _ => h N f hf⟩

/-- **`theo:CBG` (`ETT.tex:1884`) over a geometry, with a Cauchy surface of `M₀`**: a Cauchy
extension of `M₀` maximal in ETT's sense exists (every Cauchy embedding out of it is bijective),
every maximal one is isomorphic to it by a unique morphism of developments (whose inverse is a
morphism), and it is moreover universal (DEC-59). -/
theorem theo_CBG [T2Space M₀] [ConnectedSpace M₀] [SecondCountableTopology M₀]
    (s₀ : 𝔊.Str M₀) (hGH : (𝔊.causality s₀).GloballyHyperbolic) {S : Set M₀}
    (hS : (𝔊.causality s₀).IsCauchySurface S) :
    ∃ Mbar : Dev 𝔊.toPreGeometry s₀, Mbar.IsCEMaximal ∧ Mbar.IsUniversal ∧
      ∀ M : Dev 𝔊.toPreGeometry s₀, M.IsCEMaximal →
        ∃! f : Mbar.carrier → M.carrier, Mbar.IsMorphism M f ∧
          ∃ g : M.carrier → Mbar.carrier, M.IsMorphism Mbar g ∧ g ∘ f = id ∧ f ∘ g = id := by
  obtain ⟨Mbar, hU⟩ := cbg s₀ hGH hS
  exact ⟨Mbar, (Dev.isCEMaximal_iff _).2 hU.isETTMaximal, hU, fun M hM =>
    hU.existsUnique_iso (((Dev.isCEMaximal_iff _).1 hM).isUniversal hU)⟩

/-- **`theo:CBG` from global hyperbolicity alone, given the model measures** (the named hypothesis
`ModelMeasures` of `prop:mesure_admissible` / `theo:geroch_sing`, kb/0012): the Cauchy surface is
produced by `theo:geroch_sing` (i)⇒(iii) (`geroch_sing_i_imp_iii`, from A2). -/
theorem theo_CBG_of_modelMeasures [T2Space M₀] [ConnectedSpace M₀] [SecondCountableTopology M₀]
    [MeasurableSpace M₀] [BorelSpace M₀] (s₀ : 𝔊.Str M₀)
    (hGH : (𝔊.causality s₀).GloballyHyperbolic) (hM : (𝔊.causality s₀).ModelMeasures) :
    ∃ Mbar : Dev 𝔊.toPreGeometry s₀, Mbar.IsCEMaximal ∧ Mbar.IsUniversal ∧
      ∀ M : Dev 𝔊.toPreGeometry s₀, M.IsCEMaximal →
        ∃! f : Mbar.carrier → M.carrier, Mbar.IsMorphism M f ∧
          ∃ g : M.carrier → Mbar.carrier, M.IsMorphism Mbar g ∧ g ∘ f = id ∧ f ∘ g = id := by
  obtain ⟨S, hS⟩ := (𝔊.singularFlatAxioms s₀).geroch_sing_i_imp_iii hM hGH
  exact theo_CBG s₀ hGH hS

end TheoCBG

/-! ### The setting of `ETT.tex:2004–2014`: `N`, `j₁`, `j₂`, `f`, `C` -/

section Setting

variable {𝔊 : Geometry.{u}} {M₀ : Type u} [TopologicalSpace M₀] {s₀ : 𝔊.Str M₀}
  {N₁ N₂ : Dev 𝔊.toPreGeometry s₀}

namespace CommonSubDev

instance instNonempty [Nonempty M₀] (X : CommonSubDev N₁ N₂) : Nonempty X.X.carrier :=
  ⟨X.X.emb (Classical.arbitrary M₀)⟩

/-- `j₁(N)`, as an open set of `M₁`. -/
def U (X : CommonSubDev N₁ N₂) : Opens N₁.carrier :=
  (𝔊.isEMorphismOn_of_isMor X.isMorphism_b.1).imageOpens ⊤ le_rfl

@[simp] theorem coe_U (X : CommonSubDev N₁ N₂) : (X.U : Set N₁.carrier) = range X.b := by
  rw [U, IsEMorphismOn.coe_imageOpens, Opens.coe_top, image_univ]

/-- `f = j₂ ∘ j₁⁻¹` (`ETT.tex:2013–2014`), extended arbitrarily off `j₁(N)`. -/
noncomputable def f [Nonempty M₀] (X : CommonSubDev N₁ N₂) : N₁.carrier → N₂.carrier :=
  X.c ∘ invFunOn X.b ((⊤ : Opens X.X.carrier) : Set X.X.carrier)

theorem f_b [Nonempty M₀] (X : CommonSubDev N₁ N₂) (w : X.X.carrier) : X.f (X.b w) = X.c w := by
  show X.c (invFunOn X.b _ (X.b w)) = X.c w
  rw [X.injective_b.injOn.leftInvOn_invFunOn
    (show w ∈ ((⊤ : Opens X.X.carrier) : Set X.X.carrier) from trivial)]

theorem image_f_U [Nonempty M₀] (X : CommonSubDev N₁ N₂) :
    X.f '' (X.U : Set N₁.carrier) = range X.c := by
  rw [coe_U]
  ext y
  constructor
  · rintro ⟨_, ⟨w, rfl⟩, rfl⟩
    exact ⟨w, (X.f_b w).symm⟩
  · rintro ⟨w, rfl⟩
    exact ⟨X.b w, ⟨w, rfl⟩, X.f_b w⟩

theorem image_f_cauchy [Nonempty M₀] (X : CommonSubDev N₁ N₂) (S : Set M₀) :
    X.f '' (N₁.emb '' S) = N₂.emb '' S := by
  rw [← image_comp]
  refine image_congr fun a _ => ?_
  have h1 : N₁.emb a = X.b (X.X.emb a) := (congrFun X.isMorphism_b.2 a).symm
  have h2 : X.c (X.X.emb a) = N₂.emb a := congrFun X.isMorphism_c.2 a
  show X.f (N₁.emb a) = N₂.emb a
  rw [h1, f_b, h2]

theorem isOpenEmbedding_b (X : CommonSubDev N₁ N₂) : IsOpenEmbedding X.b := by
  have hE := 𝔊.isEMorphismOn_of_isMor X.isMorphism_b.1
  refine IsOpenEmbedding.of_continuous_injective_isOpenMap ?_ X.injective_b ?_
  · exact continuousOn_univ.1 hE.continuousOn
  · intro s hs; exact hE.isOpen_image ⟨s, hs⟩ le_top

theorem isOpenEmbedding_c (X : CommonSubDev N₁ N₂) : IsOpenEmbedding X.c := by
  have hE := 𝔊.isEMorphismOn_of_isMor X.isMorphism_c.1
  refine IsOpenEmbedding.of_continuous_injective_isOpenMap ?_ X.injective_c ?_
  · exact continuousOn_univ.1 hE.continuousOn
  · intro s hs; exact hE.isOpen_image ⟨s, hs⟩ le_top

/-- `f` is a structure morphism on `j₁(N)` (`c ∘ b⁻¹`, `isCGHD_of_isMorphism`). -/
theorem isMor_f [Nonempty M₀] (X : CommonSubDev N₁ N₂) : 𝔊.IsMor N₁.str N₂.str X.U X.f :=
  (isCGHD_of_isMorphism X.X X.isMorphism_b X.injective_b X.isMorphism_c).2.1

theorem continuousOn_f [Nonempty M₀] (X : CommonSubDev N₁ N₂) :
    ContinuousOn X.f (X.U : Set N₁.carrier) :=
  (𝔊.isEMorphismOn_of_isMor X.isMor_f).continuousOn

/-- **ETT's setting is package 5's CGHD setting**: `(j₁(N), f)` with `Σ₁ = ι₁(Σ₀)`. -/
theorem cghdData [Nonempty M₀] (X : CommonSubDev N₁ N₂) {S : Set M₀}
    (hS : (𝔊.causality s₀).IsCauchySurface S) :
    CGHDData 𝔊 N₁.str N₂.str X.U X.f (N₁.emb '' S) :=
  (isCGHD_of_isMorphism X.X X.isMorphism_b X.injective_b X.isMorphism_c).cghdData hS

/-- **ETT's literal `C`** (`ETT.tex:2011`: `π(p)`, `π(q)` not separated in `(M₁ ⊔ M₂)/N`) **is
the corresponding relation of Sbierski Def 3.5** for `(j₁(N), f)`. -/
theorem mem_C_iff [Nonempty M₀] (X : CommonSubDev N₁ N₂) {p : N₁.carrier} {q : N₂.carrier} :
    (p, q) ∈ Gluing.C X.b X.c ↔ Corresponds (X.U : Set N₁.carrier) X.f p q := by
  rw [Gluing.C_eq_closure X.isOpenEmbedding_b X.isOpenEmbedding_c, coe_U]
  constructor
  · intro h O hO O' hO'
    obtain ⟨_, hmem, ⟨w, rfl⟩⟩ := mem_closure_iff_nhds.1 h (O ×ˢ O') (prod_mem_nhds hO hO')
    exact ⟨X.b w, ⟨w, rfl⟩, hmem.1, by rw [f_b]; exact hmem.2⟩
  · intro h
    refine mem_closure_iff_nhds.2 fun t ht => ?_
    obtain ⟨O, hO, O', hO', hsub⟩ := mem_nhds_prod_iff.1 ht
    obtain ⟨_, ⟨w, rfl⟩, hxO, hfx⟩ := h O hO O' hO'
    exact ⟨(X.b w, X.c w), hsub ⟨hxO, by rwa [f_b] at hfx⟩, w, rfl⟩

/-- `Cdist` (pairs with distinct non-separated images, `rem:non_separe_cas`'s finding) is the set
of pairs of `C` whose first point lies on `∂ j₁(N)`. -/
theorem mem_Cdist_iff [Nonempty M₀] (X : CommonSubDev N₁ N₂) {p : N₁.carrier} {q : N₂.carrier} :
    (p, q) ∈ Gluing.Cdist X.b X.c ↔
      p ∈ frontier (range X.b) ∧ (p, q) ∈ Gluing.C X.b X.c := by
  have hb := X.isOpenEmbedding_b
  have hc := X.isOpenEmbedding_c
  rw [Gluing.Cdist_eq hb hc, ← Gluing.C_eq_closure hb hc, hb.isOpen_range.frontier_eq]
  constructor
  · rintro ⟨hC, hng⟩
    have hcor := X.mem_C_iff.1 hC
    refine ⟨⟨by rw [← coe_U]; exact mem_closure_of_corresponds hcor, ?_⟩, hC⟩
    rintro ⟨w, rfl⟩
    have hq : q = X.f (X.b w) :=
      (corresponds_iff_eq_of_mem X.continuousOn_f (by rw [coe_U]; exact ⟨w, rfl⟩)).1 hcor
    exact hng ⟨w, by rw [hq, f_b]⟩
  · rintro ⟨⟨-, hp⟩, hC⟩
    refine ⟨hC, ?_⟩
    rintro ⟨w, hw⟩
    exact hp ⟨w, (Prod.mk.inj hw).1⟩

end CommonSubDev

end Setting

/-! ### `lem:corresponding_K`, `cor:ext_continue`, `cor:model_corresponding`, `prop:C_connexe` -/

section Lemmas

variable {𝔊 : Geometry.{u}} {M₀ : Type u} [TopologicalSpace M₀] {s₀ : 𝔊.Str M₀}
  {N₁ N₂ : Dev 𝔊.toPreGeometry s₀} [Nonempty M₀]

/-- **`lem:corresponding_K` in ETT's words** (`ETT.tex:2100–2107`): `Σ₀` a Cauchy surface of `M₀`,
`Σᵢ = ιᵢ(Σ₀)`; for `p ∈ ∂j₁(N) ∩ J⁺(Σ₁)` and `q ∈ ∂j₂(N) ∩ J⁺(Σ₂)`, `(p, q) ∈ C` (literal) iff
`f` induces a bijection `K⁻(p) ∩ J⁺(Σ₁) → K⁻(q) ∩ J⁺(Σ₂)`. -/
theorem ett_corresponding_K (X : CommonSubDev N₁ N₂) {S : Set M₀}
    (hS : (𝔊.causality s₀).IsCauchySurface S) {p : N₁.carrier} {q : N₂.carrier}
    (hp : p ∈ frontier (range X.b)) (hq : q ∈ frontier (range X.c))
    (hpS : p ∈ (𝔊.causality N₁.str).Jplus ⊤ (N₁.emb '' S))
    (hqS : q ∈ (𝔊.causality N₂.str).Jplus ⊤ (N₂.emb '' S)) :
    (p, q) ∈ Gluing.C X.b X.c ↔
      (𝔊.causality N₁.str).Kminus ⊤ {p} ∩ (𝔊.causality N₁.str).Jplus ⊤ (N₁.emb '' S) ⊆
          range X.b ∧
        BijOn X.f ((𝔊.causality N₁.str).Kminus ⊤ {p} ∩ (𝔊.causality N₁.str).Jplus ⊤ (N₁.emb '' S))
          ((𝔊.causality N₂.str).Kminus ⊤ {q} ∩ (𝔊.causality N₂.str).Jplus ⊤ (N₂.emb '' S)) := by
  have h := X.cghdData hS
  have hq' : q ∈ frontier (X.f '' (X.U : Set N₁.carrier)) := by rwa [X.image_f_U]
  have := h.corresponding_K_bijOn (by rwa [X.coe_U]) hq' hpS (by rwa [X.image_f_cauchy])
  rw [X.image_f_cauchy, X.coe_U] at this
  rw [X.mem_C_iff, X.coe_U]
  exact this

/-- **`lem:corresponding_K`, past side** (`K⁺`, `J⁻(Σ)`; the statement ETT's proof of
`cor:ext_continue` needs at points below `Σ₁`, not printed). -/
theorem ett_corresponding_K_past (X : CommonSubDev N₁ N₂) {S : Set M₀}
    (hS : (𝔊.causality s₀).IsCauchySurface S) {p : N₁.carrier} {q : N₂.carrier}
    (hp : p ∈ frontier (range X.b)) (hq : q ∈ frontier (range X.c))
    (hpS : p ∈ (𝔊.causality N₁.str).Jminus ⊤ (N₁.emb '' S))
    (hqS : q ∈ (𝔊.causality N₂.str).Jminus ⊤ (N₂.emb '' S)) :
    (p, q) ∈ Gluing.C X.b X.c ↔
      (𝔊.causality N₁.str).Kplus ⊤ {p} ∩ (𝔊.causality N₁.str).Jminus ⊤ (N₁.emb '' S) ⊆
          range X.b ∧
        BijOn X.f ((𝔊.causality N₁.str).Kplus ⊤ {p} ∩ (𝔊.causality N₁.str).Jminus ⊤ (N₁.emb '' S))
          ((𝔊.causality N₂.str).Kplus ⊤ {q} ∩ (𝔊.causality N₂.str).Jminus ⊤ (N₂.emb '' S)) := by
  have h := X.cghdData hS
  have hq' : q ∈ frontier (X.f '' (X.U : Set N₁.carrier)) := by rwa [X.image_f_U]
  have := h.corresponding_K_past_bijOn (by rwa [X.coe_U]) hq' hpS (by rwa [X.image_f_cauchy])
  rw [X.image_f_cauchy, X.coe_U] at this
  rw [X.mem_C_iff, X.coe_U]
  exact this

/-- **`cor:ext_continue` in ETT's words** (`ETT.tex:2144–2145`): for every `(p, q) ∈ C`
(literal, graph pairs included), `f` extended by `f(p) = q` is continuous at `p` on
`j₁(N) ∪ {p}`. -/
theorem ett_ext_continue [DecidableEq N₁.carrier] (X : CommonSubDev N₁ N₂)
    {p : N₁.carrier} {q : N₂.carrier} (hpq : (p, q) ∈ Gluing.C X.b X.c) :
    ContinuousWithinAt (update X.f p q) (insert p (range X.b)) p := by
  obtain ⟨S, hS, -⟩ := N₁.isCauchyEmbedding.exists_cauchy
  have := (X.cghdData hS).continuousWithinAt_update_of_corresponds (X.mem_C_iff.1 hpq)
  rwa [X.coe_U] at this

/-- **`cor:ext_continue`, the germ form** (Sbierski Lemma 3.8, from A3): at `p ∈ ∂j₁(N)` with
`(p, q) ∈ C`, `f` is the restriction of a structure morphism `φ` near `p` with `φ(p) = q`. -/
theorem ett_ext_germ (X : CommonSubDev N₁ N₂) {p : N₁.carrier} {q : N₂.carrier}
    (hp : p ∈ frontier (range X.b)) (hpq : (p, q) ∈ Gluing.C X.b X.c) :
    ∃ (O : Opens N₁.carrier) (φ : N₁.carrier → N₂.carrier), p ∈ O ∧ 𝔊.IsMor N₁.str N₂.str O φ ∧
      φ p = q ∧ EqOn φ X.f ((O : Set N₁.carrier) ∩ range X.b) := by
  obtain ⟨S, hS, -⟩ := N₁.isCauchyEmbedding.exists_cauchy
  obtain ⟨O, φ, hpO, hφ, hφp, heq, -⟩ :=
    (X.cghdData hS).ext_continue (by rwa [X.coe_U]) (X.mem_C_iff.1 hpq)
  refine ⟨O, φ, hpO, hφ, hφp, fun x hx => heq ?_⟩
  rw [Opens.coe_inf, X.coe_U]
  exact hx

/-- **`cor:model_corresponding` in ETT's words** (`ETT.tex:2159–2160`): a point `p ∈ ∂j₁(N)` has
at most one corresponding point, and corresponding points have the same type `sing_α`, `α ≥ 0`. -/
theorem ett_model_corresponding (X : CommonSubDev N₁ N₂) {p : N₁.carrier}
    (hp : p ∈ frontier (range X.b)) :
    (∀ q q' : N₂.carrier, (p, q) ∈ Gluing.C X.b X.c → (p, q') ∈ Gluing.C X.b X.c → q = q') ∧
      ∀ q : N₂.carrier, (p, q) ∈ Gluing.C X.b X.c → ∀ α : ℝ, 0 ≤ α →
        (p ∈ 𝔊.sing N₁.str α ↔ q ∈ 𝔊.sing N₂.str α) := by
  obtain ⟨S, hS, -⟩ := N₁.isCauchyEmbedding.exists_cauchy
  have h := X.cghdData hS
  have hp' : p ∈ frontier (X.U : Set N₁.carrier) := by rwa [X.coe_U]
  exact ⟨fun q q' hq hq' => h.eq_of_corresponds hp' (X.mem_C_iff.1 hq) (X.mem_C_iff.1 hq'),
    fun q hq α hα => h.mem_sing_iff hp' (X.mem_C_iff.1 hq) hα⟩

/-- **`prop:C_connexe` in ETT's words** (`ETT.tex:2241–2242`): `C₁ = {p ∈ ∂j₁(N) | ∃ q, (p,q) ∈ C}`
is open in `∂j₁(N)`, and `C ∩ (∂j₁(N) × ∂j₂(N))` is closed (in `M₁ × M₂`, hence in
`∂j₁(N) × ∂j₂(N)`). -/
theorem ett_C_connexe (X : CommonSubDev N₁ N₂) :
    (∃ W : Opens N₁.carrier, {p | p ∈ frontier (range X.b) ∧ ∃ q, (p, q) ∈ Gluing.C X.b X.c} =
        (W : Set N₁.carrier) ∩ frontier (range X.b)) ∧
      IsClosed (Gluing.C X.b X.c ∩ frontier (range X.b) ×ˢ frontier (range X.c)) := by
  obtain ⟨S, hS, -⟩ := N₁.isCauchyEmbedding.exists_cauchy
  refine ⟨?_, ?_⟩
  · obtain ⟨W, hW⟩ := (X.cghdData hS).isOpen_correspondingSet
    refine ⟨W, ?_⟩
    rw [X.coe_U] at hW
    rw [← hW]
    ext p
    simp only [correspondingSet, mem_setOf_eq, X.mem_C_iff, X.coe_U]
  · rw [Gluing.C_eq_closure X.isOpenEmbedding_b X.isOpenEmbedding_c]
    exact isClosed_closure.inter (isClosed_frontier.prod isClosed_frontier)

end Lemmas

/-! ### `prop:Cauchy_point_min`, `prop:Cauchy_non_max` -/

section NonMax

variable {𝔊 : Geometry.{u}} {M₀ : Type u} [TopologicalSpace M₀] {s₀ : 𝔊.Str M₀}
  {N₁ N₂ : Dev 𝔊.toPreGeometry s₀} [Nonempty M₀]

/-- A point of `C₁` with its partner, as a pair of `Cdist` (`mem_Cdist_iff`). -/
theorem CommonSubDev.mem_Cdist_of_mem_correspondingSet (X : CommonSubDev N₁ N₂) {p : N₁.carrier}
    (hp : p ∈ correspondingSet (X.U : Set N₁.carrier) X.f) :
    ∃ q, (p, q) ∈ Gluing.Cdist X.b X.c := by
  obtain ⟨hpf, q, hc⟩ := hp
  exact ⟨q, X.mem_Cdist_iff.2 ⟨by rwa [X.coe_U] at hpf, X.mem_C_iff.2 hc⟩⟩

/-- A pair of `Cdist` puts its first point in `C₁`. -/
theorem CommonSubDev.mem_correspondingSet_of_mem_Cdist (X : CommonSubDev N₁ N₂) {p : N₁.carrier}
    {q : N₂.carrier} (h : (p, q) ∈ Gluing.Cdist X.b X.c) :
    p ∈ correspondingSet (X.U : Set N₁.carrier) X.f := by
  obtain ⟨hpf, hC⟩ := X.mem_Cdist_iff.1 h
  exact ⟨by rwa [X.coe_U], q, X.mem_C_iff.1 hC⟩

/-- **`prop:Cauchy_point_min`, intended reading** (`C` = `Cdist`, the pairs with distinct images,
`rem:non_separe_cas`'s finding; `J_{M₁}(Σ₁, p') = J⁺(Σ₁) ∩ J⁻(p')`): if `Cdist ≠ ∅`, some
`(p', q') ∈ Cdist` has `J⁺(Σ₁) ∩ J⁻(p') ∖ {p'} ⊆ j₁(N)`. -/
theorem ett_cauchy_point_min (X : CommonSubDev N₁ N₂) {S : Set M₀}
    (hS : (𝔊.causality s₀).IsCauchySurface S) (hC : (Gluing.Cdist X.b X.c).Nonempty) :
    ∃ pq ∈ Gluing.Cdist X.b X.c,
      ((𝔊.causality N₁.str).Jplus ⊤ (N₁.emb '' S) ∩ (𝔊.causality N₁.str).Jminus ⊤ {pq.1}) \
        {pq.1} ⊆ range X.b := by
  obtain ⟨⟨p₀, q₀⟩, h₀⟩ := hC
  obtain ⟨p, hp, hsub⟩ := (X.cghdData hS).exists_diamond_subset_of_nonempty
    ⟨p₀, X.mem_correspondingSet_of_mem_Cdist h₀⟩
  obtain ⟨q, hq⟩ := X.mem_Cdist_of_mem_correspondingSet hp
  exact ⟨(p, q), hq, by rw [← X.coe_U]; exact hsub⟩

/-- **`prop:Cauchy_point_min`, time-symmetric reading** (`J(Σ₁, p') = J⁻(Σ₁) ∩ J⁺(p')` at a past
point): if `Cdist ≠ ∅`, some `(p', q') ∈ Cdist` lies above `Σ₁` with
`J⁺(Σ₁) ∩ J⁻(p') ∖ {p'} ⊆ j₁(N)` or below with `J⁻(Σ₁) ∩ J⁺(p') ∖ {p'} ⊆ j₁(N)`. -/
theorem ett_cauchy_point_min_symm (X : CommonSubDev N₁ N₂) {S : Set M₀}
    (hS : (𝔊.causality s₀).IsCauchySurface S) (hC : (Gluing.Cdist X.b X.c).Nonempty) :
    ∃ pq ∈ Gluing.Cdist X.b X.c,
      (pq.1 ∈ (𝔊.causality N₁.str).Jplus ⊤ (N₁.emb '' S) ∧
        ((𝔊.causality N₁.str).Jplus ⊤ (N₁.emb '' S) ∩ (𝔊.causality N₁.str).Jminus ⊤ {pq.1}) \
          {pq.1} ⊆ range X.b) ∨
      (pq.1 ∈ (𝔊.causality N₁.str).Jminus ⊤ (N₁.emb '' S) ∧
        ((𝔊.causality N₁.str).Jminus ⊤ (N₁.emb '' S) ∩ (𝔊.causality N₁.str).Jplus ⊤ {pq.1}) \
          {pq.1} ⊆ range X.b) := by
  obtain ⟨⟨p₀, q₀⟩, h₀⟩ := hC
  obtain ⟨p, hp, hsub⟩ := (X.cghdData hS).exists_diamond_subset_symm
    ⟨p₀, X.mem_correspondingSet_of_mem_Cdist h₀⟩
  obtain ⟨q, hq⟩ := X.mem_Cdist_of_mem_correspondingSet hp
  refine ⟨(p, q), hq, ?_⟩
  rw [← X.coe_U]
  exact hsub

/-- **`prop:Cauchy_point_min` as printed is true but empty** (literal `C`): every pair of the graph
`(j₁(x), j₂(x))` lies in `C` and satisfies the conclusion, `j₁(N)` being causally convex in `M₁`. -/
theorem ett_cauchy_point_min_literal (X : CommonSubDev N₁ N₂) {S : Set M₀}
    (hS : (𝔊.causality s₀).IsCauchySurface S) (x : X.X.carrier) :
    (X.b x, X.c x) ∈ Gluing.C X.b X.c ∧
      ((𝔊.causality N₁.str).Jplus ⊤ (N₁.emb '' S) ∩ (𝔊.causality N₁.str).Jminus ⊤ {X.b x}) \
        {X.b x} ⊆ range X.b := by
  refine ⟨Gluing.graph_subset_C ⟨x, rfl⟩, ?_⟩
  rintro y ⟨⟨⟨σ, hσ, hσy⟩, hyp⟩, -⟩
  have h := X.cghdData hS
  rw [← X.coe_U]
  exact h.causallyConvexIn.2 σ (h.subset hσ) (X.b x) (by rw [X.coe_U]; exact ⟨x, rfl⟩)
    ⟨hyp, ⟨σ, rfl, hσy⟩⟩

/-- **`prop:Cauchy_non_max`, strongest true form** (`ETT.tex:2178–2181`, `C` read as `Cdist`; the
diamond hypothesis is dropped, Lemma 3.9 supplying it): if some `(p, q) ∈ C` has `p ∉ j₁(N)`
(equivalently `(p, q) ∈ Cdist`), then `N` is not maximal among the common sub-extensions. -/
theorem ett_cauchy_non_max [ConnectedSpace M₀] (X : CommonSubDev N₁ N₂) {p : N₁.carrier}
    {q : N₂.carrier} (hpq : (p, q) ∈ Gluing.Cdist X.b X.c) : ¬ X.IsMaximal := by
  intro hmax
  have hbij := hmax.bijective_toMcghd
  have hfac := mcghd_factor X.X X.isMorphism_b X.injective_b X.isMorphism_c
  have hrange : range X.b = (mcghdOpens N₁ N₂ : Set N₁.carrier) := by
    ext y
    constructor
    · rintro ⟨w, rfl⟩; exact hfac.1 w
    · intro hy
      obtain ⟨w, hw⟩ := hbij.2 ⟨y, hy⟩
      exact ⟨w, congrArg Subtype.val hw⟩
  have hp := X.mem_correspondingSet_of_mem_Cdist hpq
  have hmem : p ∈ correspondingSet (mcghdOpens N₁ N₂ : Set N₁.carrier) (mcghdMap N₁ N₂) := by
    obtain ⟨hpf, q', hc⟩ := hp
    rw [X.coe_U, hrange] at hpf
    refine ⟨hpf, q', fun O hO O' hO' => ?_⟩
    obtain ⟨x, hxU, hxO, hfx⟩ := hc O hO O' hO'
    rw [X.coe_U] at hxU
    obtain ⟨w, rfl⟩ := hxU
    refine ⟨X.b w, hfac.1 w, hxO, ?_⟩
    rw [show mcghdMap N₁ N₂ (X.b w) = X.c w from congrFun hfac.2 w]
    rwa [X.f_b] at hfx
  rw [correspondingSet_mcghd_eq_empty] at hmem
  exact hmem

/-- **`prop:Cauchy_non_max` as printed is false** (literal `C`): for any two developments of a
non-empty connected `M₀`, the maximal common sub-extension (`mcghdSubDev`, `prop:Cauchy_pgcd`) has
a pair `(p, q) ∈ C` — a graph pair `(j₁(x), j₂(x))` — with `J⁺(Σ₁) ∩ J⁻(p) ∖ {p} ⊆ j₁(N)`. -/
theorem ett_cauchy_non_max_literal_false [ConnectedSpace M₀] {S : Set M₀}
    (hS : (𝔊.causality s₀).IsCauchySurface S) :
    (mcghdSubDev N₁ N₂).IsMaximal ∧
      ∃ pq ∈ Gluing.C (mcghdSubDev N₁ N₂).b (mcghdSubDev N₁ N₂).c,
        ((𝔊.causality N₁.str).Jplus ⊤ (N₁.emb '' S) ∩ (𝔊.causality N₁.str).Jminus ⊤ {pq.1}) \
          {pq.1} ⊆ range (mcghdSubDev N₁ N₂).b := by
  set x := (mcghdSubDev N₁ N₂).X.emb (Classical.arbitrary M₀)
  exact ⟨mcghdSubDev_isMaximal, ((mcghdSubDev N₁ N₂).b x, (mcghdSubDev N₁ N₂).c x),
    ett_cauchy_point_min_literal (mcghdSubDev N₁ N₂) hS x⟩

/-- **The refutation of the printed `prop:Cauchy_non_max` is inhabited** (kb/0011): in the flat
geometry (`flatGeometry d`, `Flat/CBG`), over `M₀ = 𝕄^{1,d}` itself, a development `N` and a Cauchy
surface `Σ₀` exist, and the maximal common sub-extension of `N` with itself has a pair of the
literal `C` satisfying the printed hypothesis of `prop:Cauchy_non_max`. -/
theorem ett_cauchy_non_max_literal_false_flat (d : ℕ) :
    ∃ (N : Dev (flatGeometry d).toPreGeometry
      (flatStr flat_isCompact_Jplus_inter_Jminus flat_isCompact_Jminus_inter_Jplus (Minkowski d)))
      (S : Set (Minkowski d)),
      ((flatGeometry d).causality
        (flatStr flat_isCompact_Jplus_inter_Jminus flat_isCompact_Jminus_inter_Jplus
          (Minkowski d))).IsCauchySurface S ∧
      (mcghdSubDev N N).IsMaximal ∧
      ∃ pq ∈ Gluing.C (mcghdSubDev N N).b (mcghdSubDev N N).c,
        (((flatGeometry d).causality N.str).Jplus ⊤ (N.emb '' S) ∩
          ((flatGeometry d).causality N.str).Jminus ⊤ {pq.1}) \ {pq.1} ⊆
            range (mcghdSubDev N N).b := by
  obtain ⟨N, -⟩ := flat_cbg_minkowski (d := d)
  obtain ⟨S, hS, -⟩ := N.isCauchyEmbedding.exists_cauchy
  exact ⟨N, S, hS, ett_cauchy_non_max_literal_false hS⟩

end NonMax

/-! ### `prop:ppcm_Cauchy`: the least common over-extension -/

section Ppcm

variable {𝔊 : Geometry.{u}} {M₀ : Type u} [TopologicalSpace M₀] {s₀ : 𝔊.Str M₀}

variable (N₁ N₂ : Dev 𝔊.toPreGeometry s₀) in
/-- **A common over-extension** (`def:common_over_extension`, `ETT.tex:1970–1979`, over a
geometry): a development `P` of `M₀` with Cauchy embeddings `M₁ → P`, `M₂ → P` commuting with the
embeddings of `M₀` (injective morphisms of developments). -/
structure CommonOverDev where
  /-- The development. -/
  P : Dev 𝔊.toPreGeometry s₀
  /-- `M₁ → P`. -/
  f₁ : N₁.carrier → P.carrier
  /-- `M₂ → P`. -/
  f₂ : N₂.carrier → P.carrier
  isMorphism₁ : N₁.IsMorphism P f₁
  isMorphism₂ : N₂.IsMorphism P f₂
  injective₁ : Injective f₁
  injective₂ : Injective f₂

variable {N₁ N₂ : Dev 𝔊.toPreGeometry s₀}

namespace CommonOverDev

/-- A morphism of common over-extensions (`ETT.tex:1983`, "as in Section 4.3"): a structure
morphism commuting with the embeddings of `M₁` and `M₂`. -/
def IsMorphism (X Y : CommonOverDev N₁ N₂) (g : X.P.carrier → Y.P.carrier) : Prop :=
  𝔊.IsMor X.P.str Y.P.str ⊤ g ∧ g ∘ X.f₁ = Y.f₁ ∧ g ∘ X.f₂ = Y.f₂

/-- Equivalent common over-extensions: a bijective morphism. -/
def Equivalent (X Y : CommonOverDev N₁ N₂) : Prop :=
  ∃ g, X.IsMorphism Y g ∧ Bijective g

/-- Minimal (`ETT.tex:1983–1985`): a morphism into every common over-extension. -/
def IsMinimal (X : CommonOverDev N₁ N₂) : Prop :=
  ∀ Y : CommonOverDev N₁ N₂, ∃ g, X.IsMorphism Y g

/-- A morphism of common over-extensions is a morphism of developments (it commutes with the
embeddings of `M₀`, through `M₁`). -/
theorem IsMorphism.toDev {X Y : CommonOverDev N₁ N₂} {g : X.P.carrier → Y.P.carrier}
    (hg : X.IsMorphism Y g) : X.P.IsMorphism Y.P g := by
  refine ⟨hg.1, ?_⟩
  rw [← X.isMorphism₁.2, ← Y.isMorphism₁.2, ← comp_assoc, hg.2.1]

theorem IsMorphism.comp {X Y Z : CommonOverDev N₁ N₂} {g : X.P.carrier → Y.P.carrier}
    {h : Y.P.carrier → Z.P.carrier} (hh : Y.IsMorphism Z h) (hg : X.IsMorphism Y g) :
    X.IsMorphism Z (h ∘ g) :=
  ⟨𝔊.isMor_comp hh.1 hg.1 (fun _ _ => trivial), by rw [comp_assoc, hg.2.1, hh.2.1],
    by rw [comp_assoc, hg.2.2, hh.2.2]⟩

/-- **Two minimal common over-extensions are equivalent** (rigidity: a self-morphism of a
development is the identity, `Dev.IsMorphism.eq_id`). -/
theorem IsMinimal.equivalent [Nonempty M₀] {X Y : CommonOverDev N₁ N₂} (hX : X.IsMinimal)
    (hY : Y.IsMinimal) : X.Equivalent Y := by
  obtain ⟨g, hg⟩ := hX Y
  obtain ⟨h, hh⟩ := hY X
  have hhg : h ∘ g = id := (hh.comp hg).toDev.eq_id
  have hgh : g ∘ h = id := (hg.comp hh).toDev.eq_id
  exact ⟨g, hg, LeftInverse.injective (congrFun hhg), RightInverse.surjective (congrFun hgh)⟩

end CommonOverDev

variable [ConnectedSpace M₀]

variable (N₁ N₂) in
/-- **`ppcm` as a common over-extension**: `(M₁ ⊔ M₂)/∼` glued along the greatest common
sub-extension (`defi:ppcm`, `ETT.tex:1987–1991`; the MCGHD, `prop:Cauchy_pgcd`). -/
noncomputable def ppcmOver : CommonOverDev N₁ N₂ where
  P := ppcmDev N₁ N₂ mcghdMap_injOn
  f₁ := Gluing.ι₁ _ _
  f₂ := Gluing.ι₂ _ _
  isMorphism₁ := ppcmDev_isMorphism₁ mcghdMap_injOn
  isMorphism₂ := ppcmDev_isMorphism₂ mcghdMap_injOn
  injective₁ := Gluing.injective_ι₁ Subtype.val_injective (ppcm_injective_j₂ mcghdMap_injOn)
  injective₂ := Gluing.injective_ι₂ Subtype.val_injective (ppcm_injective_j₂ mcghdMap_injOn)

/-- **`prop:ppcm_Cauchy` in ETT's words** (`ETT.tex:1994–1997`): `ppcm` is a minimal common
over-extension, any two minimal common over-extensions are equivalent, and every minimal one is
equivalent to `ppcm`. -/
theorem ett_ppcm_Cauchy :
    (ppcmOver N₁ N₂).IsMinimal ∧
      (∀ X Y : CommonOverDev N₁ N₂, X.IsMinimal → Y.IsMinimal → X.Equivalent Y) ∧
      ∀ X : CommonOverDev N₁ N₂, X.IsMinimal → X.Equivalent (ppcmOver N₁ N₂) := by
  have hmin : (ppcmOver N₁ N₂).IsMinimal := fun Y => by
    obtain ⟨h, hh, -⟩ := ppcmDev_desc mcghdMap_injOn Y.P Y.isMorphism₁ Y.isMorphism₂
    exact ⟨h, hh.1.1, hh.2.1, hh.2.2⟩
  exact ⟨hmin, fun X Y hX hY => hX.equivalent hY, fun X hX => hX.equivalent hmin⟩

end Ppcm

/-! ### `rem:CBG_manquant` -/

section Manquant

variable {𝔊 : Geometry.{u}} {M₀ : Type u} [TopologicalSpace M₀] {s₀ : 𝔊.Str M₀}

/-- **`rem:CBG_manquant` (ii), the cardinality bound** (`ETT.tex:2353–2354`): every Cauchy
extension has cardinality at most that of the continuum (a second countable `T₀` space embeds in
`Set ℕ`, `exists_injective_setNat`). -/
theorem Dev.card_le_continuum (N : Dev 𝔊.toPreGeometry s₀) :
    Cardinal.mk N.carrier ≤ Cardinal.continuum := by
  obtain ⟨g, hg⟩ := exists_injective_setNat N.carrier
  have h := Cardinal.lift_mk_le_lift_mk_of_injective hg
  rwa [Cardinal.mk_set_nat, Cardinal.lift_continuum, Cardinal.lift_uzero] at h

/-- **`rem:CBG_manquant` (i), the gap closed over a geometry** (`ETT.tex:2345–2349`): the maximal
Cauchy extension is second countable, and is universal. -/
theorem ett_maximal_secondCountable [T2Space M₀] [ConnectedSpace M₀] [SecondCountableTopology M₀]
    (s₀ : 𝔊.Str M₀) (hGH : (𝔊.causality s₀).GloballyHyperbolic) {S : Set M₀}
    (hS : (𝔊.causality s₀).IsCauchySurface S) :
    ∃ Mbar : Dev 𝔊.toPreGeometry s₀, Mbar.IsUniversal ∧ SecondCountableTopology Mbar.carrier :=
  (cbg s₀ hGH hS).imp fun Mbar h => ⟨h, Mbar.sc⟩

end Manquant

end CBG

end Causal
