import Causal.PlainnessModels.LipschitzPushUp
import Causal.SFATransfer
import Causal.PushUpOfMinimalLocal
import Causal.Remarks.MassiveManifold
import Causal.Remarks.Tarentin

/-!
# `cor:K_lorentzien` at every Lipschitz Lorentzian manifold, through causal plainness (DEC-168)

Target `T-ett-plainness-models` (DEC-168 on OQ-16, OQ-28: keep plainness, prove it for the
models, Lipschitz metrics included). Cited, **unmarked** (SCOPE): `cor:K_lorentzien` —
`ETT.tex:884`; `rem:lorentz_tarentin` — `ETT.tex:783`.

> Let $M$ be a Lorentzian manifold. Then $\forall p\in M, \quad K^\pm(p)=I^\pm(p).$
> (`cor:K_lorentzien`, `ETT.tex:884–886`)
>
> A Lorentzian manifold is a tarentin topological spacetime whose causality is absolutely minimal,
> and by Remark \ref{rem:lorentz_tarentin} each of its points is strongly tarentin in the future and
> in the past. Proposition \ref{prop:tarentin_fort_K} and its analogue for $K^+$ give the
> conclusion. (`ETT.tex:889–891`)
>
> Every point of a Lorentzian manifold is strongly tarentin in the future and in the past.
> (`rem:lorentz_tarentin`, `ETT.tex:784`)

## What is here

* `IsLipschitzLorentzian C n`: the reading of « `M` is a Lorentzian manifold » (OQ-28, DEC-168):
  `C` is absolutely minimal (DEC-167) and every point lies in the source of a chart onto an open
  subset of `ℝ^{1+n}` which is an isomorphism of topological spacetimes (`ChartIso`) onto the
  causality of some **locally Lipschitz** time-oriented Lorentzian metric
  (`LipschitzMetric.causality`).
* At such an `M`: push-up (`pushUp`, local in charts by `LipschitzMetric.pushUp`, global by
  absolute minimality on a T1 space), **causal plainness** (`causallyPlain`), every point strongly
  tarentin both ways (`mem_Zplus`, `mem_Zminus`: `rem:lorentz_tarentin`), and
  **`K^±(p) = I^±(p)` for every `p`** (`K_lorentzien`), through `Causality.K_lorentzien`, i.e.
  `prop:tarentin_fort_K` with causal plainness, the printed proof.
* `LipschitzMetric.absolutelyMinimal`: the causality of every coordinate model is absolutely
  minimal (paths subdivided along any open cover), so every model with the identity chart is a
  Lipschitz Lorentzian manifold (`isLipschitzLorentzian_causality`; non-vacuity, kb/0011), e.g.
  Minkowski's constant metric `LipschitzMetric.minkowskiMetric n` (`minkB`, `T = (1, 0)`;
  `minkowskiMetric_K_lorentzien`). No `sorry` in this file.

## Hypothesis checklist

| paper | here |
|---|---|
| `M` a Lorentzian manifold | ⚠ read (OQ-28, DEC-168): a time-oriented Lorentzian manifold with a **locally Lipschitz** metric, through its causality only: absolutely minimal (DEC-167), charts that are causal isomorphisms onto coordinate models (no smooth atlas: weaker) |
| tarentin (named in the proof) | ⚠ weakened: not used |
| absolutely minimal | ✓ carried (DEC-167) |
| strongly tarentin both ways (`rem:lorentz_tarentin`) | ✓ proved from the charts (`mem_Zplus`, `mem_Zminus`) |
| causally plain (used by `prop:tarentin_fort_K`, omitted by the proof) | ✓ proved (`causallyPlain`) |
| Hausdorff | ⚠ weakened to T1 |

## SCOPE (disclosed)

* **Why unmarked.** The regularity of « Lorentzian manifold » is a reading (OQ-28). DEC-168 asks
  plainness for Lipschitz metrics; the statement here is for locally Lipschitz ones, which is
  where plainness holds (below it, `rem:pas_plat` (i)). Whether « locally Lipschitz » is the
  statement of record is the author's.
* The coordinate model's conventions (paths, `C¹` timelike paths, global metric) are those of
  `Causal.PlainnessModels.LipschitzModel`'s SCOPE.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set Filter Topology TopologicalSpace Relation

universe u

/-- **A Lipschitz Lorentzian manifold**, through its causality: `C` absolutely minimal, and every
point in the source of a chart into `ℝ^{1+n}` which is a causal isomorphism onto the causality of
a locally Lipschitz time-oriented Lorentzian metric. -/
structure IsLipschitzLorentzian {M : Type u} [TopologicalSpace M] (C : Causality M) (n : ℕ) :
    Prop where
  absolutelyMinimal : C.AbsolutelyMinimal
  charts : ∀ x : M, ∃ e : OpenPartialHomeomorph M (Minkowski n), x ∈ e.source ∧
    ∃ L : LipschitzMetric n, ChartIso C L.causality e

namespace IsLipschitzLorentzian

variable {M : Type u} [TopologicalSpace M] {C : Causality M} {n : ℕ}

theorem firstCountableTopology (h : IsLipschitzLorentzian C n) : FirstCountableTopology M := by
  refine ⟨fun x => ?_⟩
  obtain ⟨e, hx, -⟩ := h.charts x
  rw [← e.symm_map_nhds_eq hx]
  infer_instance

/-- Every point has an open neighbourhood with push-up: a chart source. -/
theorem locallyPushUp (h : IsLipschitzLorentzian C n) : C.LocallyPushUp := by
  intro x
  obtain ⟨e, hx, L, he⟩ := h.charts x
  exact ⟨chartSource e, hx, ChartIso.pushUpOn he (LipschitzMetric.pushUp.pushUpOn _)⟩

/-- **Push-up** at every Lipschitz Lorentzian manifold. -/
theorem pushUp [T1Space M] (h : IsLipschitzLorentzian C n) : C.PushUp :=
  Causality.AbsolutelyMinimal.pushUp_of_locallyPushUp h.absolutelyMinimal h.locallyPushUp

theorem locZplus (h : IsLipschitzLorentzian C n) : E0LM.LocZplus C := by
  intro W x hxW N hN
  obtain ⟨e, hx, L, he⟩ := h.charts x
  exact SFATransfer.ChartIso.exists_lt_right he LipschitzMetric.locZplus hx hxW hN

theorem locZminus (h : IsLipschitzLorentzian C n) : E0LM.LocZminus C ∅ := by
  intro W x hxW _ N hN
  obtain ⟨e, hx, L, he⟩ := h.charts x
  exact SFATransfer.ChartIso.exists_lt_left he LipschitzMetric.locZminus hx (notMem_empty _) hxW hN

/-- **Causal plainness** at every Lipschitz Lorentzian manifold (DEC-168). -/
theorem causallyPlain [T1Space M] (h : IsLipschitzLorentzian C n) : C.CausallyPlain :=
  Causality.causallyPlain_of_locZ h.pushUp h.locZplus h.locZminus interior_empty

/-- `rem:lorentz_tarentin` (unmarked), future half, at every Lipschitz Lorentzian manifold. -/
theorem mem_Zplus (h : IsLipschitzLorentzian C n) (p : M) : p ∈ C.Zplus := by
  intro U hU
  obtain ⟨z, hzU, hz⟩ := h.locZplus ⊤ p trivial U hU
  exact ⟨z, Precausality.mem_Iplus_singleton.2 hz, hzU⟩

/-- `rem:lorentz_tarentin` (unmarked), past half, at every Lipschitz Lorentzian manifold. -/
theorem mem_Zminus (h : IsLipschitzLorentzian C n) (p : M) : p ∈ C.Zminus := by
  intro U hU
  obtain ⟨z, hzU, hz⟩ := h.locZminus ⊤ p trivial (notMem_empty _) U hU
  exact ⟨z, Precausality.mem_Iminus_singleton.2 hz, hzU⟩

/-- `cor:K_lorentzien` (unmarked) at every Lipschitz Lorentzian manifold: `K^±(p) = I^±(p)`, through
causal plainness and `prop:tarentin_fort_K` (`Causality.K_lorentzien`), the printed proof. -/
theorem K_lorentzien [T1Space M] (h : IsLipschitzLorentzian C n) (p : M) :
    C.Kplus ⊤ {p} = C.Iplus ⊤ {p} ∧ C.Kminus ⊤ {p} = C.Iminus ⊤ {p} := by
  haveI := h.firstCountableTopology
  refine Causality.K_lorentzien h.absolutelyMinimal h.causallyPlain (fun q => ⟨?_, ?_⟩) p
  · obtain ⟨z, hz, -⟩ := h.mem_Zplus q univ univ_mem
    exact ⟨z, hz⟩
  · obtain ⟨z, hz, -⟩ := h.mem_Zminus q univ univ_mem
    exact ⟨z, hz⟩

end IsLipschitzLorentzian

/-! ### Non-vacuity: Minkowski's constant metric -/

namespace LipschitzMetric

variable {n : ℕ}

/-- `minkB` as a continuous bilinear form. -/
noncomputable def minkBL (n : ℕ) : Minkowski n →L[ℝ] Minkowski n →L[ℝ] ℝ :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ Flat.minkB
      (fun u v w => by simp only [Flat.minkB, Prod.fst_add, Prod.snd_add, inner_add_left]; ring)
      (fun c u w => by
        simp only [Flat.minkB, Prod.smul_fst, Prod.smul_snd, inner_smul_left, smul_eq_mul]
        simp; ring)
      (fun u v w => by simp only [Flat.minkB, Prod.fst_add, Prod.snd_add, inner_add_right]; ring)
      (fun c u w => by
        simp only [Flat.minkB, Prod.smul_fst, Prod.smul_snd, inner_smul_right, smul_eq_mul]
        ring))
    2 fun u v => by
      simp only [LinearMap.mk₂_apply, Flat.minkB, Real.norm_eq_abs]
      have h1 := abs_real_inner_le_norm u.2 v.2
      have h2 : |u.1| ≤ ‖u‖ := norm_fst_le u
      have h3 : |v.1| ≤ ‖v‖ := norm_fst_le v
      have h4 : ‖u.2‖ ≤ ‖u‖ := norm_snd_le u
      have h5 : ‖v.2‖ ≤ ‖v‖ := norm_snd_le v
      calc |-(u.1 * v.1) + inner ℝ u.2 v.2| ≤ |u.1| * |v.1| + ‖u.2‖ * ‖v.2‖ := by
            rw [← abs_mul]
            exact (abs_add_le _ _).trans (by rw [abs_neg]; exact add_le_add le_rfl h1)
        _ ≤ ‖u‖ * ‖v‖ + ‖u‖ * ‖v‖ := add_le_add
            (mul_le_mul h2 h3 (abs_nonneg _) (norm_nonneg _))
            (mul_le_mul h4 h5 (norm_nonneg _) (norm_nonneg _))
        _ = 2 * ‖u‖ * ‖v‖ := by ring

@[simp] theorem minkBL_apply (u v : Minkowski n) : minkBL n u v = Flat.minkB u v := rfl

/-- **Minkowski's metric** on `ℝ^{1+n}`, constant, `T = (1, 0)`. -/
noncomputable def minkowskiMetric (n : ℕ) : LipschitzMetric n where
  g _ := minkBL n
  T _ := (1, 0)
  lorentzian _ := ⟨LinearEquiv.refl ℝ _, fun _ _ => rfl⟩
  locallyLipschitz := (LipschitzWith.const _).locallyLipschitz
  continuous_T := continuous_const
  timelike _ := by simp [Flat.minkB]

/-- **The causality of every locally Lipschitz Lorentzian metric is absolutely minimal.** -/
theorem absolutelyMinimal (L : LipschitzMetric n) : L.causality.AbsolutelyMinimal := by
  show L.causality.toPrecausality.AbsolutelyMinimal
  rw [Precausality.absolutelyMinimal_iff]
  intro S hS V _ x y
  -- one path, subdivided along the cover
  have hsub : ∀ {γ : ℝ → Minkowski n} {a b : ℝ}, a ≤ b → Continuous γ →
      MapsTo γ (Icc a b) (V : Set (Minkowski n)) →
      ∃ t : ℕ → ℝ, t 0 = a ∧ Monotone t ∧ (∃ m, ∀ k ≥ m, t k = b) ∧ (∀ k, t k ∈ Icc a b) ∧
        ∀ k, ∃ O ∈ S, MapsTo γ (Icc (t k) (t (k + 1))) ((V ⊓ O : Opens (Minkowski n)) : Set _) := by
    intro γ a b hab hγ hmaps
    have hcover : Icc a b ⊆ ⋃ O : S, γ ⁻¹' ((O : Opens (Minkowski n)) : Set (Minkowski n)) := by
      intro s hs
      obtain ⟨O, hO, hsO⟩ := hS (γ s) trivial
      exact mem_iUnion.2 ⟨⟨O, hO⟩, hsO⟩
    obtain ⟨t, ht0, hmono, hm, htI, hpiece⟩ :=
      exists_subdivision_Icc hab (fun O : S => (O.1.isOpen.preimage hγ)) hcover
    refine ⟨t, ht0, hmono, hm, htI, fun k => ?_⟩
    obtain ⟨⟨O, hO⟩, hk⟩ := hpiece k
    refine ⟨O, hO, fun s hs => ⟨hmaps ⟨(htI k).1.trans hs.1, hs.2.trans (htI (k + 1)).2⟩, hk hs⟩⟩
  constructor
  · rintro ⟨hx, h⟩
    have hstep : ∀ {u w : Minkowski n}, L.CausalStep V u w →
        TransGen (fun a b => ∃ O ∈ S, L.causality.le (V ⊓ O) a b) u w := by
      rintro u w ⟨γ, a, b, ⟨hab, ⟨K, hK⟩, hmaps, hae⟩, rfl, rfl⟩
      obtain ⟨t, ht0, hmono, ⟨m, hm⟩, htI, hpiece⟩ := hsub hab hK.continuous hmaps
      have hone : ∀ k, ∃ O ∈ S, L.causality.le (V ⊓ O) (γ (t k)) (γ (t (k + 1))) := by
        intro k
        obtain ⟨O, hO, hk⟩ := hpiece k
        have hle := hmono (Nat.le_succ k)
        refine ⟨O, hO, hk ⟨le_rfl, hle⟩, ReflTransGen.single ⟨γ, t k, t (k + 1),
          ⟨hle, ⟨K, hK⟩, hk, ?_⟩, rfl, rfl⟩⟩
        filter_upwards [hae] with s hs hs'
        exact hs ⟨(htI k).1.trans_lt hs'.1, hs'.2.trans_le (htI (k + 1)).2⟩
      have key : ∀ k, TransGen (fun a b => ∃ O ∈ S, L.causality.le (V ⊓ O) a b)
          (γ (t 0)) (γ (t (k + 1))) := by
        intro k
        induction k with
        | zero => exact TransGen.single (hone 0)
        | succ k ih => exact ih.tail (hone (k + 1))
      have := key m
      rwa [ht0, hm (m + 1) (Nat.le_succ m)] at this
    induction h with
    | refl =>
      obtain ⟨O, hO, hxO⟩ := hS x trivial
      exact TransGen.single ⟨O, hO, L.causality.le_refl (U := V ⊓ O) ⟨hx, hxO⟩⟩
    | tail _ hst ih => exact ih.trans (hstep hst)
  · intro h
    have hstep : ∀ {u w : Minkowski n}, L.TimeStep V u w →
        TransGen (fun a b => ∃ O ∈ S, L.causality.lt (V ⊓ O) a b) u w := by
      rintro u w ⟨γ, a, b, hγ, rfl, rfl⟩
      obtain ⟨hab, γ', h1, h2, hmaps, h4⟩ := hγ
      have hcont : Continuous (fun s => γ (projIcc a b hab.le s)) :=
        (IsTimelikePath.continuousOn ⟨hab, γ', h1, h2, hmaps, h4⟩).comp_continuous
          (continuous_subtype_val.comp continuous_projIcc) (fun s => (projIcc a b hab.le s).2)
      have hmaps' : MapsTo (fun s => γ (projIcc a b hab.le s)) (Icc a b) (V : Set _) :=
        fun s hs => by simp only [projIcc_of_mem hab.le hs]; exact hmaps hs
      obtain ⟨t, ht0, hmono, ⟨m, hm⟩, htI, hpiece⟩ := hsub hab.le hcont hmaps'
      have heq : ∀ s ∈ Icc a b, γ (projIcc a b hab.le s) = γ s := fun s hs => by
        simp only [projIcc_of_mem hab.le hs]
      have hone : ∀ k, t k < t (k + 1) →
          ∃ O ∈ S, L.causality.lt (V ⊓ O) (γ (t k)) (γ (t (k + 1))) := by
        intro k hlt
        obtain ⟨O, hO, hk⟩ := hpiece k
        have hsubI : Icc (t k) (t (k + 1)) ⊆ Icc a b :=
          fun s hs => ⟨(htI k).1.trans hs.1, hs.2.trans (htI (k + 1)).2⟩
        refine ⟨O, hO, TransGen.single ⟨γ, t k, t (k + 1), ⟨hlt, γ', h1.mono hsubI,
          fun s hs => h2 s (hsubI hs), fun s hs => ?_, fun s hs => h4 s (hsubI hs)⟩, rfl, rfl⟩⟩
        have : γ (projIcc a b hab.le s) ∈ ((V ⊓ O : Opens (Minkowski n)) : Set _) := hk hs
        rwa [heq s (hsubI hs)] at this
      have key : ∀ k, t 0 < t k → TransGen (fun a b => ∃ O ∈ S, L.causality.lt (V ⊓ O) a b)
          (γ (t 0)) (γ (t k)) := by
        intro k
        induction k with
        | zero => exact fun h => absurd h (lt_irrefl _)
        | succ k ih =>
          intro hk
          rcases (hmono (Nat.le_succ k)).eq_or_lt with heq' | hlt
          · rw [← heq'] at hk ⊢; exact ih hk
          · rcases (hmono (Nat.zero_le k)).eq_or_lt with h0 | h0
            · rw [h0]; exact TransGen.single (hone k hlt)
            · exact (ih h0).tail (hone k hlt)
      have := key m (by rw [ht0, hm m le_rfl]; exact hab)
      rwa [ht0, hm m le_rfl] at this
    induction h with
    | single hst => exact hstep hst
    | tail _ hst ih => exact ih.trans (hstep hst)

end LipschitzMetric

/-- **Non-vacuity** (kb/0011): every coordinate model, in particular Minkowski's metric, with the
identity chart, is a Lipschitz Lorentzian manifold. -/
theorem isLipschitzLorentzian_causality {n : ℕ} (L : LipschitzMetric n) :
    IsLipschitzLorentzian L.causality n :=
  ⟨L.absolutelyMinimal, fun _ => ⟨OpenPartialHomeomorph.refl _, trivial, L, chartIso_refl _⟩⟩

/-- `cor:K_lorentzien` at Minkowski's metric, through this file. -/
theorem minkowskiMetric_K_lorentzien (n : ℕ) (p : Minkowski n) :
    (LipschitzMetric.minkowskiMetric n).causality.Kplus ⊤ {p} =
        (LipschitzMetric.minkowskiMetric n).causality.Iplus ⊤ {p} ∧
      (LipschitzMetric.minkowskiMetric n).causality.Kminus ⊤ {p} =
        (LipschitzMetric.minkowskiMetric n).causality.Iminus ⊤ {p} :=
  (isLipschitzLorentzian_causality _).K_lorentzien p

end Causal
