import Causal.LemmaKSCLocal
import Causal.Model.CurvesExtendModels
import Causal.Model.Massive
import Causal.Minkowski

/-!
# Lemma K on static spacetimes, on the massive-particle models and on Minkowski space

No label is marked. The model sections of `Causal.LemmaKBare` and `Causal.LemmaKSCLocal`, moved
here verbatim with the same full names (T-abs-hoist-lemma-k), so that the Lemma K family
(`Causal.LemmaKBare`, `Causal.LemmaKReduction`, `Causal.LemmaKSC`, `Causal.LemmaKLocal`,
`Causal.LevinUtility`, `Causal.LemmaKSCLocal`, `Causal.LemmaK`) imports no model. Lemma K is
DEC-44's abstraction of a sentence Barbot asserts and never proves (Rem 2.3 `clomax`, label at
`GHFspace.tex:572` of the labelled file); it carries no paper label. This module is a model module
(`Causal.Model.*`): a layer-1 module never imports it. Barbot's `𝐌ⁿ` is the library's
`Minkowski d`, `n = d + 1`.

> Cauchy-compact GH spacetimes are automatically absolutely maximal. Indeed, any spacelike
> hypersurface in a given CGH spacetime is a Cauchy hypersurface. (Rem 2.3, l.576–578)

## What is proved

* **The bare form on every static spacetime `ℝ × X` over a proper geodesic space**
  (`staticCausality.isCauchySurface_of_compact_isLocallyCauchy`): the chronal form
  `Causality.isCauchySurface_of_isLocallyCauchy_of_chronal` (`Causal.LemmaKBare`) with every
  hypothesis discharged. Connectedness of `X` is derived (`preconnectedSpace_of_geodesic`), and
  `J^±(p) ≠ {p}` is `staticCausality.Jminus_singleton_ne`, `Jplus_singleton_ne`.
* **The bare statement, verbatim, for `C = staticCausality X`** over any geodesic `X`
  (`staticCausality.isCauchySurface_of_isLocallyCauchy_bare`): global hyperbolicity of `ℝ × X`
  forces `X` proper (`properSpace_of_globallyHyperbolic`).
* **The massive-particle models `E_α`, `α > 0`** (`massive_isCauchySurface_of_compact_isLocallyCauchy`,
  `Causal.Model.Massive`), an instance of the static form; so is Minkowski space.
* **Track A on Minkowski space** (`minkowski_curvesExtend_of_lemmaKSCLocal`): curves extend there
  by Levin's time function (`Causality.curvesExtend_of_secondCountable`), the Minkowski
  non-vacuity witness of `Causal.LemmaKSCLocal`.

## Hypothesis checklist

| hypothesis of the chronal form (`Causal.LemmaKBare`) | on `ℝ × X`, `X` proper geodesic |
|---|---|
| `T2Space`, `ConnectedSpace` | ✓ instances; `X` connected (`preconnectedSpace_of_geodesic`), non-empty as `Σ` is |
| `Tarentin`, `GloballyHyperbolic`, `CausallyArcConnected` | ✓ `staticCausality.tarentin`, `.globallyHyperbolic`, `.causallyArcConnected` |
| `J^±(p) ≠ {p}` | ✓ `staticCausality.Jminus_singleton_ne`, `.Jplus_singleton_ne` |
| `CurvesExtend`, `PushUp`, `Z^± = M` | ✓ `staticCausality.curvesExtend` (`Causal.Model.CurvesExtendModels`), `.pushUp`, `.mem_Zplus`, `.mem_Zminus` |

## SCOPE (disclosed)

* Moved, not restated (T-abs-hoist-lemma-k, 2026-11-22): the section "Static spacetimes: the bare
  form holds" of `Causal.LemmaKBare` with the theorem on `E_α` after it, verbatim, and the
  Minkowski witness of the non-vacuity section of `Causal.LemmaKSCLocal`, verbatim. The
  timelike-line witnesses of both modules are model-free and stay there.
* The flat `ℝ × torus` (a translation spacetime) is an instance mathematically; no torus instance
  is built in the library.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Filter Function

universe u

variable {M : Type u} [TopologicalSpace M]

/-! ### Static spacetimes: the bare form holds -/

namespace staticCausality

variable {X : Type*} [MetricSpace X] [GeodesicSpace X]

theorem Jminus_singleton_ne (p : ℝ × X) : (staticCausality X).Jminus ⊤ {p} ≠ {p} := by
  intro h
  have hmem : (p.1 - 1, p.2) ∈ (staticCausality X).Jminus ⊤ {p} := by
    rw [mem_Jminus_top]; simp
  rw [h, mem_singleton_iff, Prod.ext_iff] at hmem
  simp at hmem

theorem Jplus_singleton_ne (p : ℝ × X) : (staticCausality X).Jplus ⊤ {p} ≠ {p} := by
  intro h
  have hmem : (p.1 + 1, p.2) ∈ (staticCausality X).Jplus ⊤ {p} := by
    rw [mem_Jplus_top]; simp
  rw [h, mem_singleton_iff, Prod.ext_iff] at hmem
  simp at hmem

/-- A geodesic space is preconnected: a geodesic is Lipschitz on `[0, 1]`. -/
theorem preconnectedSpace_of_geodesic : PreconnectedSpace X := by
  refine ⟨isPreconnected_of_forall_pair fun x _ y _ => ?_⟩
  obtain ⟨g, hg0, hg1, hg⟩ := GeodesicSpace.exists_geodesic x y
  have hL : LipschitzOnWith (nndist x y) g (Icc 0 1) :=
    LipschitzOnWith.of_dist_le_mul fun s hs s' hs' => by
      rw [hg s hs s' hs', Real.dist_eq, coe_nndist, mul_comm]
  exact ⟨g '' Icc 0 1, subset_univ _, ⟨0, ⟨le_rfl, zero_le_one⟩, hg0⟩,
    ⟨1, ⟨zero_le_one, le_rfl⟩, hg1⟩, isPreconnected_Icc.image g hL.continuousOn⟩

/-- **Global hyperbolicity of `ℝ × X` forces `X` proper**: the closed ball `B(x, r)` is the
spatial projection of the slice `t = r` of the diamond from `(0, x)` to `(2r, x)`. -/
theorem properSpace_of_globallyHyperbolic (hG : (staticCausality X).GloballyHyperbolic) :
    ProperSpace X := by
  refine ProperSpace.of_isCompact_closedBall_of_le 0 fun x r hr => ?_
  have hK : IsCompact ((staticCausality X).diamond ⊤ (0, x) (2 * r, x) ∩ ({r} ×ˢ univ)) :=
    (hG.2 _ _).inter_right (isClosed_singleton.prod isClosed_univ)
  convert hK.image continuous_snd using 1
  ext y
  constructor
  · intro hy
    rw [Metric.mem_closedBall] at hy
    refine ⟨(r, y), ⟨Causality.mem_diamond.2 ⟨?_, ?_⟩, rfl, trivial⟩, rfl⟩
    · rw [le_top_iff]; simp only; rw [dist_comm]; linarith
    · rw [le_top_iff]; simp only; linarith
  · rintro ⟨⟨t, y'⟩, ⟨hd, ht, -⟩, rfl⟩
    rw [mem_singleton_iff] at ht
    subst ht
    obtain ⟨h1, -⟩ := Causality.mem_diamond.1 hd
    rw [le_top_iff] at h1
    simp only at h1
    rw [Metric.mem_closedBall, dist_comm]; linarith

/-- **Lemma K holds, in its bare DEC-44 form, on every static spacetime `ℝ × X` over a proper
geodesic space**: a compact connected locally Cauchy set is a Cauchy surface. Connectedness of `X`
is automatic (`preconnectedSpace_of_geodesic`, `X` non-empty as `Σ` is). Minkowski space and the
massive-particle models `E_α`, `α > 0`, are instances; the flat `ℝ × torus` (a translation
spacetime) is one mathematically, but no torus instance is built in the library. -/
theorem isCauchySurface_of_compact_isLocallyCauchy [ProperSpace X]
    {S : Set (ℝ × X)} (hSc : IsCompact S) (hSconn : IsConnected S)
    (hloc : (staticCausality X).IsLocallyCauchy S) : (staticCausality X).IsCauchySurface S := by
  haveI : PreconnectedSpace X := preconnectedSpace_of_geodesic
  haveI : Nonempty X := ⟨hSconn.nonempty.some.2⟩
  haveI : ConnectedSpace X := { toNonempty := inferInstance }
  exact Causality.isCauchySurface_of_isLocallyCauchy_of_chronal tarentin globallyHyperbolic
    causallyArcConnected Jminus_singleton_ne Jplus_singleton_ne curvesExtend pushUp mem_Zplus
    mem_Zminus hSc hSconn hloc

/-- **The bare statement `Causality.isCauchySurface_of_isLocallyCauchy`, verbatim, for
`C = staticCausality X`** over any geodesic metric space `X`: properness is derived from global
hyperbolicity (`properSpace_of_globallyHyperbolic`); the other hypotheses are carried only to
match the bare signature (they hold automatically). -/
theorem isCauchySurface_of_isLocallyCauchy_bare [T2Space (ℝ × X)] [ConnectedSpace (ℝ × X)]
    (_hT : (staticCausality X).Tarentin) (hG : (staticCausality X).GloballyHyperbolic)
    (_hC : (staticCausality X).CausallyArcConnected)
    (_hJm : ∀ p : ℝ × X, (staticCausality X).Jminus ⊤ {p} ≠ {p})
    (_hJp : ∀ p : ℝ × X, (staticCausality X).Jplus ⊤ {p} ≠ {p})
    {S : Set (ℝ × X)} (hSc : IsCompact S) (hSconn : IsConnected S)
    (hloc : (staticCausality X).IsLocallyCauchy S) : (staticCausality X).IsCauchySurface S := by
  haveI := properSpace_of_globallyHyperbolic hG
  exact isCauchySurface_of_compact_isLocallyCauchy hSc hSconn hloc

end staticCausality

/-- **The bare form on the massive-particle model `E_α`, `α > 0`** (`Causal.Model.Massive`, a
singular flat model with a timelike singular line): a compact connected locally Cauchy set is a
Cauchy surface. -/
theorem massive_isCauchySurface_of_compact_isLocallyCauchy (α : ℝ) [Fact (0 < α)]
    {S : Set (Massive α)} (hSc : IsCompact S) (hSconn : IsConnected S)
    (hloc : (massive α).IsLocallyCauchy S) : (massive α).IsCauchySurface S :=
  staticCausality.isCauchySurface_of_compact_isLocallyCauchy hSc hSconn hloc

/-! ### Minkowski space: track A of `Causal.LemmaKSCLocal` -/

/-- Track A applies to Minkowski space: curves extend there, by Levin's time function. -/
theorem minkowski_curvesExtend_of_lemmaKSCLocal (n : ℕ) : (minkowski n).CurvesExtend :=
  Causality.curvesExtend_of_secondCountable minkowski_tarentin minkowski_globallyHyperbolic

end Causal
