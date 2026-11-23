import Causal.CurvesExtendSecondCountable
import Causal.ErsSecondCountable
import Causal.CExtConnexeSecondCountable

/-!
# The intersection lemmas on second countable spacetimes, without `CurvesExtend`

Programme target `T-abs-curves-free-cauchy` (`programme/roadmap.toml`; DEC-190; layer 1: it
imports `Causal.CurvesExtendSecondCountable`, `Causal.ErsSecondCountable` and
`Causal.CExtConnexeSecondCountable`, all ETT-layer; no model; no metric notion in a statement).
**No label is marked** (SCOPE). The row served, unmarked: `lem:C_ext_connexe` — `ETT.tex:1932`
(its decl `IsCauchyEmbedding.c_ext_connexe_of_isCauchySurfaceOn`, `Causal.SubExtension`, and the
topological steps of `Causal.CBG.CausalConvex` behind `IsCauchyEmbedding.isPreconnected_inf`).

Of the 23 theorems of `Causal.CBG.CausalConvex` with a named `CurvesExtend(On)` binder (kb/0012),
14 have their form in `Causal.CExtConnexeSecondCountable` and `IsCauchySurfaceOn.eq_of_le` has its
form in `Causal.CurvesExtendSecondCountable` (`IsCauchySurfaceOn.eq_of_le_of_t1_secondCountable`);
the 8 others are here, **beside the originals**: the original's binders less `hext`, with
`[SecondCountableTopology M]` inserted after `[T2Space M]`, or `[T1Space M]
[SecondCountableTopology M]` before the first binder where the original has no separation axiom
(`inter_subsingleton_of_curvesExtend`, `isCauchySurfaceOn_iff_of_curvesExtend`). Names: the
original's suffixed `_secondCountable`, and an original's `_of_curvesExtend` replaced by
`_of_t1_secondCountable`. `Causal.SubExtension`'s `c_ext_connexe_of_isCauchySurfaceOn` carries its
through-hypothesis inline (`hthrough`, `InextensibleThrough (A ⊓ B)` written out); its form here
drops it (`Causality.inextensibleThrough_of_t1_secondCountable`, kb/0218) and adds `[T1Space N]
[SecondCountableTopology N]`.

> A topological spacetime is a second countable Hausdorff topological space endowed with a
> causality. (`ETT.tex:255`)

> The map $M\rightarrow A\cap B$ is a Cauchy embedding, so $\phi(\Sigma)$ is a Cauchy surface of
> $A\cap B$ and every point of $A\cap B$ lies on an inextensible causal curve meeting
> $\phi(\Sigma)$. Hence $A\cap B$ is arcwise connected. (`ETT.tex:1940–1942`)

## What is proved (no `sorry`)

1. `Causality.inter_subsingleton_of_t1_secondCountable`,
   `Causality.isCauchySurfaceOn_iff_of_t1_secondCountable` (no separation axiom in the originals).
2. `Causality.exists_inextensible_inf_meeting_of_subsingleton_secondCountable`,
   `exists_inextensible_inf_meeting_secondCountable`,
   `mem_connectedComponentIn_inf_of_subsingleton_secondCountable`,
   `mem_connectedComponentIn_inf_secondCountable`, `isPreconnected_inf_of_subset_secondCountable`,
   `isPreconnected_inf_secondCountable`: `lem:C_ext_connexe`'s topological steps, no named
   hypothesis left beyond the originals' Cauchy data and causality.
3. `IsCauchyEmbedding.c_ext_connexe_of_isCauchySurfaceOn_secondCountable`: the paper's route with
   the middle step named (`hcauchy`), the through-hypothesis gone.
4. Witnesses (kb/0011): `timelikeLine_isPreconnected_inf_secondCountable` (a proper open
   `A = ]-1, 1[` of `B = ℝ`, the common Cauchy surface `{g 0}`),
   `timelikeLine_c_ext_connexe_of_isCauchySurfaceOn_secondCountable` (the identity of the line)
   and `timelikeLine_gateArc_c_ext_connexe_of_isCauchySurfaceOn_secondCountable` (`gateArc`, a
   Cauchy embedding that is not onto, kb/0222).

## Hypothesis checklist

| original | here |
|---|---|
| `hext : C.CurvesExtend` / `hDext` (named, kb/0012) | ✓ dropped: `curvesExtend_of_t1_secondCountable` |
| `hthrough` of `c_ext_connexe_of_isCauchySurfaceOn` (inline `InextensibleThrough`) | ✓ dropped: `inextensibleThrough_of_t1_secondCountable` |
| `[T2Space M]` (6 originals) | ✓ carried; `[SecondCountableTopology M]` added (`ETT.tex:255`) |
| no separation axiom (3 originals) | ⚠ `[T1Space _] [SecondCountableTopology _]` added (`ETT.tex:255`: T2 gives T1) |
| `hcauchy` (`ETT.tex:1940–1941`, unargued in the paper) | ⚠ carried unchanged, named |
| the splitting `ψ` of `theo:geroch_sing` | ⚠ carried unchanged, named |

## SCOPE (disclosed)

* **Nothing marked.** These are curve-free forms of step lemmas, not anchors. The row's principal
  with no named hypothesis is `IsCauchyEmbedding.c_ext_connexe_of_connectedSpace_of_secondCountable`
  (`Causal.CExtConnexeSecondCountable`), whose curation is the master's (DEC-190, OQ-86).
* **Beside, not replacing** (OQ-98 open): the originals are unchanged; each pair is checked by
  elaborated binder lists (kb/0227).
* **Left** (`Causal.SubExtension`): `isConnected_of_curves`' `hcurve` (curves *meeting `T`*, the
  lemma's content, not a curve-extension hypothesis); `eq_of_mem_image_inter`, whose form
  `eq_of_mem_image_inter_of_secondCountable` (`Causal.CExtConnexeSecondCountable`) also drops
  `hDac`, so it is stronger than "the original less `hDext`".

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Filter Function

universe u v

namespace Causality

section Convex

variable {M : Type u} [TopologicalSpace M] {C : Causality M}

/-! ## 1. Meeting a set at most once, and the existence half -/

/-- `inter_subsingleton_of_curvesExtend` without `hext`, `M` T1 and second countable: a set
meeting every inextensible curve of `M` at most once meets every causal curve of every open set at
most once. -/
theorem inter_subsingleton_of_t1_secondCountable [T1Space M] [SecondCountableTopology M]
    {T : Set M}
    (hT : ∀ (I : Set ℝ) (c : ℝ → M), C.Inextensible ⊤ I c → (c '' I ∩ T).Subsingleton)
    {W : Opens M} {I : Set ℝ} {c : ℝ → M} (hc : C.CausalCurveIn W I c) :
    (c '' I ∩ T).Subsingleton :=
  inter_subsingleton_of_curvesExtend (curvesExtend_of_t1_secondCountable C) hT hc

/-- `isCauchySurfaceOn_iff_of_curvesExtend` without `hext`, `M` T1 and second countable: being a
Cauchy surface of an open set reduces to the existence half, for a set meeting every inextensible
curve of `M` at most once. -/
theorem isCauchySurfaceOn_iff_of_t1_secondCountable [T1Space M] [SecondCountableTopology M]
    {T : Set M}
    (hT : ∀ (I : Set ℝ) (c : ℝ → M), C.Inextensible ⊤ I c → (c '' I ∩ T).Subsingleton)
    (W : Opens M) :
    C.IsCauchySurfaceOn W T ↔
      ∀ (I : Set ℝ) (c : ℝ → M), C.Inextensible W I c → (c '' I ∩ T).Nonempty :=
  isCauchySurfaceOn_iff_of_curvesExtend (curvesExtend_of_t1_secondCountable C) hT W

/-! ## 2. `lem:C_ext_connexe`'s topological steps -/

/-- `exists_inextensible_inf_meeting_of_subsingleton` without `hext`, `M` second countable: every
point of `A ∩ B` lies on an inextensible causal curve of `A ∩ B` meeting `T`. -/
theorem exists_inextensible_inf_meeting_of_subsingleton_secondCountable [T2Space M]
    [SecondCountableTopology M] (hcaus : C.IsCausal) {A B : Opens M} {T : Set M}
    (hT : ∀ (I : Set ℝ) (c : ℝ → M), C.Inextensible ⊤ I c → (c '' I ∩ T).Subsingleton)
    (hTA : C.IsCauchySurfaceOn A T) (hTB : C.IsCauchySurfaceOn B T) {x : M} (hx : x ∈ A ⊓ B) :
    ∃ (I : Set ℝ) (c : ℝ → M), C.Inextensible (A ⊓ B) I c ∧ x ∈ c '' I ∧ (c '' I ∩ T).Nonempty :=
  exists_inextensible_inf_meeting_of_subsingleton hcaus (curvesExtend_of_t1_secondCountable C) hT
    hTA hTB hx

/-- `exists_inextensible_inf_meeting` without `hext`, `M` second countable: `T` a Cauchy surface of
`M`, of `A` and of `B`. -/
theorem exists_inextensible_inf_meeting_secondCountable [T2Space M] [SecondCountableTopology M]
    (hcaus : C.IsCausal) {A B : Opens M} {T : Set M} (hT : C.IsCauchySurface T)
    (hTA : C.IsCauchySurfaceOn A T) (hTB : C.IsCauchySurfaceOn B T) {x : M} (hx : x ∈ A ⊓ B) :
    ∃ (I : Set ℝ) (c : ℝ → M), C.Inextensible (A ⊓ B) I c ∧ x ∈ c '' I ∧ (c '' I ∩ T).Nonempty :=
  exists_inextensible_inf_meeting hcaus (curvesExtend_of_t1_secondCountable C) hT hTA hTB hx

/-- `mem_connectedComponentIn_inf_of_subsingleton` without `hext`, `M` second countable: every
connected component of `A ∩ B` meets `T`. -/
theorem mem_connectedComponentIn_inf_of_subsingleton_secondCountable [T2Space M]
    [SecondCountableTopology M] (hcaus : C.IsCausal) {A B : Opens M} {T : Set M}
    (hT : ∀ (I : Set ℝ) (c : ℝ → M), C.Inextensible ⊤ I c → (c '' I ∩ T).Subsingleton)
    (hTA : C.IsCauchySurfaceOn A T) (hTB : C.IsCauchySurfaceOn B T) {x : M} (hx : x ∈ A ⊓ B) :
    ∃ y ∈ T, y ∈ connectedComponentIn ((A ⊓ B : Opens M) : Set M) x :=
  mem_connectedComponentIn_inf_of_subsingleton hcaus (curvesExtend_of_t1_secondCountable C) hT hTA
    hTB hx

/-- `mem_connectedComponentIn_inf` without `hext`, `M` second countable. -/
theorem mem_connectedComponentIn_inf_secondCountable [T2Space M] [SecondCountableTopology M]
    (hcaus : C.IsCausal) {A B : Opens M} {T : Set M} (hT : C.IsCauchySurface T)
    (hTA : C.IsCauchySurfaceOn A T) (hTB : C.IsCauchySurfaceOn B T) {x : M} (hx : x ∈ A ⊓ B) :
    ∃ y ∈ T, y ∈ connectedComponentIn ((A ⊓ B : Opens M) : Set M) x :=
  mem_connectedComponentIn_inf hcaus (curvesExtend_of_t1_secondCountable C) hT hTA hTB hx

/-- **`lem:C_ext_connexe`'s strongest topological form without `hext`**, `M` second countable
(`isPreconnected_inf_of_subset`): `T` a Cauchy surface of `A` and of `B` meeting every
inextensible curve of `M` at most once, `T ⊆ P ⊆ A ∩ B` with `P` preconnected ⟹ `A ∩ B`
preconnected. -/
theorem isPreconnected_inf_of_subset_secondCountable [T2Space M] [SecondCountableTopology M]
    (hcaus : C.IsCausal) {A B : Opens M} {T P : Set M}
    (hT : ∀ (I : Set ℝ) (c : ℝ → M), C.Inextensible ⊤ I c → (c '' I ∩ T).Subsingleton)
    (hTA : C.IsCauchySurfaceOn A T) (hTB : C.IsCauchySurfaceOn B T) (hTP : T ⊆ P)
    (hPsub : P ⊆ ((A ⊓ B : Opens M) : Set M)) (hP : IsPreconnected P) :
    IsPreconnected ((A ⊓ B : Opens M) : Set M) :=
  isPreconnected_inf_of_subset hcaus (curvesExtend_of_t1_secondCountable C) hT hTA hTB hTP hPsub hP

/-- `isPreconnected_inf` without `hext`, `M` second countable: `T` a preconnected Cauchy surface
of `M`, of `A` and of `B`, contained in `A ∩ B` ⟹ `A ∩ B` preconnected. -/
theorem isPreconnected_inf_secondCountable [T2Space M] [SecondCountableTopology M]
    (hcaus : C.IsCausal) {A B : Opens M} {T : Set M} (hT : C.IsCauchySurface T)
    (hTA : C.IsCauchySurfaceOn A T) (hTB : C.IsCauchySurfaceOn B T)
    (hTsub : T ⊆ ((A ⊓ B : Opens M) : Set M)) (hTc : IsPreconnected T) :
    IsPreconnected ((A ⊓ B : Opens M) : Set M) :=
  isPreconnected_inf hcaus (curvesExtend_of_t1_secondCountable C) hT hTA hTB hTsub hTc

end Convex

end Causality

/-! ## 3. `lem:C_ext_connexe` by the paper's route, without the through-hypothesis -/

section CExtConnexe

variable {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]
  {C : Causality M} {D : Causality N} {φ : M → N}

/-- **`lem:C_ext_connexe` from its middle step, without `hthrough`** (`ETT.tex:1932`, unmarked):
`IsCauchyEmbedding.c_ext_connexe_of_isCauchySurfaceOn` with its through-hypothesis (every point of
`A ∩ B` on an inextensible causal curve of `A ∩ B`) discharged on a T1, second countable `N`. `M`
connected, `φ` a Cauchy embedding, `A, B` Cauchy-including `φ(M)`, the splitting `ψ`, and
`φ(Σ)` a Cauchy surface of `A ∩ B` (`hcauchy`, the paper's unargued step) ⟹ `A ∩ B` connected. -/
theorem IsCauchyEmbedding.c_ext_connexe_of_isCauchySurfaceOn_secondCountable [T1Space N]
    [SecondCountableTopology N] [ConnectedSpace M]
    (hφ : IsCauchyEmbedding C D φ) {A B : Opens N} (hA : IsCauchyInclusion D hφ.rangeOpens A)
    (hB : IsCauchyInclusion D hφ.rangeOpens B) {S : Set M} (ψ : S × ℝ ≃ₜ M)
    (hcauchy : D.IsCauchySurfaceOn (A ⊓ B) (φ '' S)) :
    IsConnected ((A ⊓ B : Opens N) : Set N) :=
  hφ.c_ext_connexe_of_isCauchySurfaceOn hA hB ψ hcauchy
    (Causality.inextensibleThrough_of_t1_secondCountable D (A ⊓ B))

end CExtConnexe

/-! ## 4. Witnesses on the timelike line (kb/0011) -/

/-- **The new step lemmas with `A` a proper open subset of `B`**, no curve hypothesis supplied: on
the timelike line, `A = ]-1, 1[ ≠ ℝ = B` with the common Cauchy surface `T = {g 0}` (`g = gateArc`),
also a Cauchy surface of `ℝ`; every point of `A ∩ B` lies on an inextensible causal curve of
`A ∩ B` meeting `T` (`exists_inextensible_inf_meeting_secondCountable`) and `A ∩ B` is preconnected
(`isPreconnected_inf_secondCountable`). -/
theorem timelikeLine_isPreconnected_inf_secondCountable :
    timelikeArcOpens ≠ ⊤ ∧
      (∀ x ∈ timelikeArcOpens ⊓ ⊤, ∃ (I : Set ℝ) (c : ℝ → ℝ),
        timelikeLine.Inextensible (timelikeArcOpens ⊓ ⊤) I c ∧ x ∈ c '' I ∧
          (c '' I ∩ {gateArc 0}).Nonempty) ∧
      IsPreconnected ((timelikeArcOpens ⊓ ⊤ : Opens ℝ) : Set ℝ) := by
  have hCA : timelikeLine.IsCauchySurfaceOn timelikeArcOpens {gateArc 0} := by
    have h := IsEMorphismOn.isCauchySurfaceOn_image_iff timelikeLine_isEMorphism_gateArc
      gateArc_strictMono.injective.injOn (V := ⊤) le_rfl (U := timelikeArcOpens)
      (by simp [timelikeArcOpens]) (S := {0}) (subset_univ _)
    rw [image_singleton] at h
    exact h.1 timelikeLine_isCauchySurface_zero
  have hT : timelikeLine.IsCauchySurface {gateArc 0} := timelikeLine_isCauchySurface_singleton _
  have hsub : ({gateArc 0} : Set ℝ) ⊆ ((timelikeArcOpens ⊓ ⊤ : Opens ℝ) : Set ℝ) :=
    singleton_subset_iff.2 ⟨⟨0, trivial, rfl⟩, trivial⟩
  exact ⟨timelikeLine_causalConvex_proper.1, fun x hx =>
      Causality.exists_inextensible_inf_meeting_secondCountable timelikeLine_isCausal hT hCA hT hx,
    Causality.isPreconnected_inf_secondCountable timelikeLine_isCausal hT hCA hT hsub
      isPreconnected_singleton⟩

/-- **`c_ext_connexe_of_isCauchySurfaceOn_secondCountable` applies with no through-hypothesis
supplied**: on the timelike line along `id`, `A = B = ℝ`, `Σ = {0}` with its splitting; the
original's `hthrough` (`timelikeLine_c_ext_connexe_hypotheses`, last conjunct) is not asked. -/
theorem timelikeLine_c_ext_connexe_of_isCauchySurfaceOn_secondCountable :
    IsConnected (((⊤ : Opens ℝ) ⊓ ⊤ : Opens ℝ) : Set ℝ) := by
  have hA : IsCauchyInclusion timelikeLine timelikeLine_isCauchyEmbedding_id.rangeOpens ⊤ := by
    rw [timelikeLine_rangeOpens_id]; exact timelikeLine_isCauchyInclusion_top
  have hcauchy : timelikeLine.IsCauchySurfaceOn (⊤ ⊓ ⊤) (id '' ({0} : Set ℝ)) := by
    rw [inf_idem, image_id]; exact timelikeLine_isCauchySurface_zero
  exact timelikeLine_isCauchyEmbedding_id.c_ext_connexe_of_isCauchySurfaceOn_secondCountable hA hA
    timelikeLineSplitting hcauchy

/-- **The same off the identity** (kb/0222): along `gateArc : ℝ → ]-1, 1[`, a Cauchy embedding of
the timelike line that is not onto (`timelikeLine_gateArc_secondCountable`), with `A = φ(ℝ)`,
`B = ℝ` and `Σ = {0}`, `A ∩ B` is connected by
`c_ext_connexe_of_isCauchySurfaceOn_secondCountable`; no through-hypothesis is supplied. -/
theorem timelikeLine_gateArc_c_ext_connexe_of_isCauchySurfaceOn_secondCountable :
    IsCauchyEmbedding timelikeLine timelikeLine gateArc ∧
      ∀ hφ : IsCauchyEmbedding timelikeLine timelikeLine gateArc,
        IsConnected ((hφ.rangeOpens ⊓ ⊤ : Opens ℝ) : Set ℝ) := by
  refine ⟨timelikeLine_gateArc_secondCountable.1, fun hφ => ?_⟩
  have hS' : timelikeLine.IsCauchySurface (gateArc '' {0}) := by
    rw [image_singleton]; exact timelikeLine_isCauchySurface_singleton _
  have hCA : timelikeLine.IsCauchySurfaceOn hφ.rangeOpens (gateArc '' {0}) :=
    (hφ.isEMorphism.isCauchySurface_iff hφ.injective {0}).1 timelikeLine_isCauchySurface_zero
  have hsub : gateArc '' {0} ⊆ (hφ.rangeOpens : Set ℝ) := by
    rw [IsCauchyEmbedding.coe_rangeOpens]; exact image_subset_range _ _
  have hA : IsCauchyInclusion timelikeLine hφ.rangeOpens hφ.rangeOpens :=
    ⟨le_rfl, timelikeLine_globallyHyperbolicOn _, timelikeLine_globallyHyperbolicOn _, _, hsub,
      hCA, hCA⟩
  have hB : IsCauchyInclusion timelikeLine hφ.rangeOpens ⊤ :=
    ⟨le_top, timelikeLine_globallyHyperbolicOn _, timelikeLine_globallyHyperbolicOn _, _, hsub,
      hCA, hS'⟩
  have hcauchy : timelikeLine.IsCauchySurfaceOn (hφ.rangeOpens ⊓ ⊤) (gateArc '' {0}) := by
    rw [inf_top_eq]; exact hCA
  exact hφ.c_ext_connexe_of_isCauchySurfaceOn_secondCountable hA hB timelikeLineSplitting hcauchy

end Causal
