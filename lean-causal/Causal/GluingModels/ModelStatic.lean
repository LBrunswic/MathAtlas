import Causal.GluingModels.Tools
import Causal.Static
import Causal.Minkowski
import Causal.Model.Massive
import Causal.Model.EAlphaCauchy
import Causal.Model.FlatTimeCylinder
import Causal.Model.QuasilinearOneSided
import Causal.Flat.IsomCausal
import Causal.Flat.FlatSpacetime
import Causal.Flat.CBG
import Causal.ChainsCurves
import Causal.KBorelien
import Causal.CausalIsoInvariance

/-!
# Gluing inventory (DEC-167), model layer: static spacetimes and flat `(G,X)`-manifolds

No paper label is certified by this file. The models of the inventory of `T-abs-gluing-models`
that are static spacetimes over a geodesic space, or flat `(Isom 𝐄^{1,d}, 𝐄^{1,d})`-manifolds, all
glue **hereditarily** (`∀ W, C.AbsolutelyMinimalOn W`), hence on `M`:

* from causal arc-connectedness (`cor:causalement_connexe_minimal`, `ETT.tex:458`, on every
  open): `staticCausality X` (every geodesic `X`), so Minkowski space, the massive models `E_α`,
  Hörmann's cosmic string, the half-plane `staticCausality (Ioi 0)` of `Causal.ChainsCurves`, the
  slope-`δ` cone (a transport of a static causality), the flat time cylinder;
* the flat causality of a flat `(G,X)`-manifold and the transports by isometries:
  `Flat.flatCausality_absolutelyMinimalOn`, `Flat.isomTransport_absolutelyMinimalOn` (cited in the
  table, not restated);
* Minkowski space with spokes along a cone `A` (`Causal.KBorelien`, `rem:K_borelien`): the proof of
  `spokes_absolutelyMinimal` with the cover asked of `W` only.

## Hypothesis checklist

| hypothesis | here |
|---|---|
| second countable, Hausdorff | ⚠ weakened: not used |
| spokes: `A` a cone (`c • z ∈ A` for `c > 0`) | ✓ carried, as in `spokes_absolutelyMinimal` |

## SCOPE (disclosed)

* No definition changes; OQ-95 and OQ-96 are not decided here.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

namespace GluingModels

open Set TopologicalSpace Topology Relation

/-! ### Static spacetimes -/

/-- **A static spacetime over a geodesic space glues hereditarily.** -/
theorem staticCausality_hereditary {X : Type*} [MetricSpace X] [GeodesicSpace X] :
    ∀ W : Opens (ℝ × X), (staticCausality X).AbsolutelyMinimalOn W :=
  forall_of_causallyArcConnected staticCausality.causallyArcConnected

/-- Minkowski space glues hereditarily (also `Flat.minkowski_absolutelyMinimalOn`). -/
theorem minkowski_hereditary (n : ℕ) : ∀ W : Opens (Minkowski n), (minkowski n).AbsolutelyMinimalOn W :=
  forall_of_causallyArcConnected minkowski_causallyArcConnected

/-- The massive model `E_α`, `α > 0`, glues hereditarily. -/
theorem massive_hereditary (α : ℝ) [Fact (0 < α)] :
    ∀ W : Opens (Massive α), (massive α).AbsolutelyMinimalOn W :=
  forall_of_causallyArcConnected massive_causallyArcConnected

/-- Hörmann's cosmic string glues hereditarily. -/
theorem cosmicString_hereditary (α : ℝ) [Fact (0 < α)] :
    ∀ W : Opens (CosmicString α), (cosmicString α).AbsolutelyMinimalOn W :=
  forall_of_causallyArcConnected cosmicString_causallyArcConnected

/-- The half-plane of `Causal.ChainsCurves` (`halfPlane_hypotheses`, the ladder's witness against
`… → causally_compact`) glues hereditarily. -/
theorem halfPlane_hereditary :
    ∀ W : Opens (ℝ × Ioi (0 : ℝ)), (staticCausality (Ioi (0 : ℝ))).AbsolutelyMinimalOn W :=
  forall_of_causallyArcConnected staticCausality.causallyArcConnected

/-- The static cone of slope `δ` is causally arc-connected: a transport of a static causality. -/
theorem slopeCone_causallyArcConnected {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (δ : ℝ) (hδ : 0 < δ) : (slopeCone E δ hδ).CausallyArcConnected :=
  (isCausalIso_transport _ _).causallyArcConnected_iff.1 staticCausality.causallyArcConnected

/-- The static cone of slope `δ` glues hereditarily. -/
theorem slopeCone_hereditary {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (δ : ℝ) (hδ : 0 < δ) : ∀ W : Opens (ℝ × E), (slopeCone E δ hδ).AbsolutelyMinimalOn W :=
  forall_of_causallyArcConnected (slopeCone_causallyArcConnected δ hδ)

theorem slopeCone_minimal {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (δ : ℝ) (hδ : 0 < δ) : (slopeCone E δ hδ).AbsolutelyMinimal :=
  absolutelyMinimal_of_forall (slopeCone_hereditary δ hδ)

/-! ### Flat manifolds -/

/-- The flat time cylinder glues hereditarily. -/
theorem timeCylinder_hereditary (d : ℕ) :
    ∀ W : Opens (Flat.TimeCylinder d), (Flat.timeCylinder d).AbsolutelyMinimalOn W :=
  forall_of_causallyArcConnected Flat.timeCylinder_causallyArcConnected

/-- The transport of Minkowski space by an isometry glues on `M`. -/
theorem isomTransport_minimal {d : ℕ} (g : Flat.isom d) : (Flat.isomTransport g).AbsolutelyMinimal :=
  absolutelyMinimal_of_forall (Flat.isomTransport_absolutelyMinimalOn g)

/-! ### Minkowski space with spokes -/

section Spokes

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {A : Set E}

/-- **Minkowski space with spokes along a cone glues hereditarily**: the proof of
`spokes_absolutelyMinimal` (`Causal.KBorelien`), with the cover asked of `W` only — a chronological
step is a chain of chronological steps by the hereditary gluing of the static causality, a spoke
step a chain of spoke steps along a subdivision of its radial segment, which lies in `V ≤ W`. -/
theorem spokes_hereditary (hA : ∀ z ∈ A, ∀ c : ℝ, 0 < c → c • z ∈ A) :
    ∀ W : Opens (ℝ × E), (spokesCausality A).AbsolutelyMinimalOn W := by
  intro W S hS V hV x y
  have hst := staticCausality_hereditary (X := E) W
  set R : ℝ × E → ℝ × E → Prop := fun a b => ∃ O ∈ S, (spokesCausality A).le (V ⊓ O) a b
    with hR
  -- a chronological step is a chain of chronological steps (Minkowski space)
  have hbase : ∀ a b, Spokes.base (V : Set (ℝ × E)) a b → ReflTransGen R a b := by
    rintro a b (⟨rfl, -⟩ | h)
    · exact ReflTransGen.refl
    · exact (TransGen.mono (fun c d ⟨O, hO, hcd⟩ => ⟨O, hO, Or.inl (Or.inr hcd)⟩)
        ((hst S hS V hV a b).2 h)).to_reflTransGen
  -- a spoke step is a chain of spoke steps (subdivision of the radial segment)
  have hrel : ∀ a b, Spokes.rel A (V : Set (ℝ × E)) a b → ReflTransGen R a b := by
    rintro a b ⟨ha, hb, hAa, c, hc, hbc, hseg⟩
    let φ : ℝ → ℝ × E := fun s => ((0 : ℝ), s • a.2)
    have hφ : Continuous φ := continuous_const.prodMk (continuous_id.smul continuous_const)
    have hcover : Icc c 1 ⊆ ⋃ i : S, φ ⁻¹' ((V ⊓ i.1 : Opens (ℝ × E)) : Set (ℝ × E)) := by
      intro s hs
      obtain ⟨O, hO, hsO⟩ := hS (φ s) (hV (hseg s hs))
      exact mem_iUnion.2 ⟨⟨O, hO⟩, ⟨hseg s hs, hsO⟩⟩
    obtain ⟨t, ht0, hmono, ⟨m, hm⟩, htI, hsub⟩ := exists_subdivision_Icc hc.2
      (fun i : S => (V ⊓ i.1).isOpen.preimage hφ) hcover
    have key : ∀ n, ReflTransGen R (φ (t n)) b := by
      intro n
      induction n with
      | zero =>
        have : φ (t 0) = b := Prod.ext (by simp [φ, hb]) (by simp [φ, ht0, hbc])
        rw [this]
      | succ n ih =>
        obtain ⟨i, hi⟩ := hsub n
        have hle : t n ≤ t (n + 1) := hmono (Nat.le_succ n)
        rcases hle.eq_or_lt with heq | hlt
        · rwa [← heq]
        have h0 : 0 ≤ t n := hc.1.trans (htI n).1
        have hpos : 0 < t (n + 1) := h0.trans_lt hlt
        refine ReflTransGen.head ⟨i.1, i.2, Or.inr ⟨φ (t (n + 1)), φ (t n),
          Or.inl ⟨rfl, hi ⟨hle, le_rfl⟩⟩, ?_, Or.inl ⟨rfl, hi ⟨le_rfl, hle⟩⟩⟩⟩ ih
        refine ⟨rfl, rfl, hA a.2 hAa _ hpos, t n / t (n + 1),
          ⟨div_nonneg h0 hpos.le, (div_le_one hpos).2 hle⟩, ?_, fun σ hσ => ?_⟩
        · simp only [φ]
          rw [smul_smul, div_mul_cancel₀ _ hpos.ne']
        · have hmem := hi (show σ * t (n + 1) ∈ Icc (t n) (t (n + 1)) from
            ⟨(div_le_iff₀ hpos).1 hσ.1, mul_le_of_le_one_left hpos.le hσ.2⟩)
          simp only [φ, mem_preimage] at hmem ⊢
          rwa [smul_smul]
    have hfin : φ (t m) = a := Prod.ext (by simp [φ, ha]) (by simp [φ, hm m le_rfl])
    rw [← hfin]
    exact key m
  refine ⟨fun h => ?_, fun h => TransGen.mono (fun _ _ h => h) ((hst S hS V hV x y).2 h)⟩
  have hx : x ∈ V := h.mem_left
  obtain ⟨O, hO, hxO⟩ := hS x (hV hx)
  have hrefl : R x x := ⟨O, hO, (spokesCausality A).le_refl ⟨hx, hxO⟩⟩
  refine TransGen.head' hrefl ?_
  rcases h with h | ⟨a, b, h₁, h₂, h₃⟩
  · exact hbase x y h
  · exact ((hbase x a h₁).trans (hrel a b h₂)).trans (hbase b y h₃)

end Spokes

end GluingModels

end Causal
