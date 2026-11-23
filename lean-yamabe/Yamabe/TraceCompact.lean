import Yamabe.RellichManifold
import Yamabe.TraceInterp

/-!
# The compact trace into `L²(∂Σ)` on a compact manifold with boundary

Labels (NOT marked: one step of the proof, under the readings of OQ-93, see SCOPE):

* `lem:positivity` — `Yamabegap.tex:715` (statement l.715–718, proof l.719–721): the compact
  trace `W^{1,2}(Σ) → L²(∂Σ)` that its proof cites (l.720), proved on a compact Riemannian
  manifold with boundary.

> The trace operator $W^{1,2}(\Sigma)\to L^2(\partial\Sigma)$ is compact, so the traces converge
> to $c$ in $L^2(\partial\Sigma)$; [...] (l.720)

## The setting

As in `Yamabe.Trace`: `M` a compact smooth manifold with boundary modelled on
`EuclideanHalfSpace N`, `g` a smooth Riemannian metric, `μ` a locally-Lebesgue volume
(`Yamabe.Sobolev`), and `σ` a boundary measure, `Mfd.IsBoundaryMeasure N σ` (`Yamabe.Trace`).
`W^{1,2}(M)` is read through `C¹(M)`, normed by `Mfd.w12 g μ` (`Yamabe.Sobolev`). As `σ` is carried
by `∂M`, `eLpNorm (u - f) 2 σ` measures the trace of `u` on `∂M`.

## What is proved (no `sorry`, standard axioms)

**`Mfd.trace_compact`**, the one declaration of this file; nothing depends on it. The proof:
Rellich–Kondrachov (`Mfd.rellich_kondrachov`) gives a subsequence `v_k = u_{φ k}` converging in
`L²(μ)`; the interpolation trace inequality in difference form (`Mfd.trace_interp_sub`,
`Yamabe.TraceInterp`)
`‖v_k − v_l‖_{L²(σ)} ≤ C (δ (‖v_k‖_{W^{1,2}} + ‖v_l‖_{W^{1,2}}) + δ⁻¹ ‖v_k − v_l‖_{L²(μ)})`, with
`δ` chosen first against the `W^{1,2}` bound `K`, makes `(v_k)` Cauchy in `L²(σ)`
(`Mfd.memLp_two_of_isC1` puts each `v_k` there); `L²(σ)` is complete.

Provenance of the statement: round 1 (T-yamabe-analysis) stated it with `sorry` in Trace.lean;
T-yamabe-graduate-analysis moved it here unchanged, downstream of `Mfd.rellich_kondrachov`
(`Yamabe.RellichManifold`, which this file imports), so that the chain of `Yamabe.Trace` could
graduate to the strict library. T-yamabe-trace-compact replaced the `sorry` in place, the statement
unchanged.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `Σ` compact Riemannian with boundary | ✓ carried: `CompactSpace`, `T2Space`, smooth `g`, for every `N` with `NeZero N` (the paper's `N ≥ 3` is not asked); `μ` ⚠ read, as in `Yamabe.Sobolev` |
| the induced measure of `∂Σ` | ⚠ read: any `σ` with `IsBoundaryMeasure N σ` (a weakening: only an upper bound is asked) |
| `(u_k)` bounded in `W^{1,2}(Σ)` | ⚠ read: `u_k ∈ C¹(M)` with `w12 g μ (u k) ≤ K` |

## SCOPE (disclosed)

* The proof of lem:positivity needs only the continuity of the trace, not its compactness
  (`Yamabe.Trace`, SCOPE): `lem_positivity` (`Yamabe.Rellich`) uses only `TraceIneq`. The
  compactness the paper states at l.720 is this theorem, proved for completeness (DEC-184).
* The limit `f` is an element of `L²(σ)` (`MemLp f 2 σ`), the limit of the traces. The paper's
  « the traces converge to `c` » identifies it with the constant `u_∞ ≡ c`, which takes the
  constancy step (`Mfd.const_of_tendsto`) and the continuity of the trace
  (`Mfd.trace_embedding`), not this theorem.
* No label is marked: this is one step of lem:positivity's proof, under the readings of OQ-93
  (`W^{1,2}` read through `C¹`, the volume and the boundary measure read as above).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Manifold ContDiff Bundle

noncomputable section

namespace Yamabe

namespace Mfd

variable {N : ℕ} [NeZero N]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace N) M]
  [IsManifold (𝓡∂ N) ∞ M] [MeasurableSpace M] [BorelSpace M]

/-- **The compact trace** (l.720): every sequence bounded in `W^{1,2}(M)` has a subsequence whose
traces converge in `L²(∂M)`. -/
theorem trace_compact [CompactSpace M] [T2Space M] (g : RiemannianMetric N M)
    {μ : Measure M} (hμ : IsLocallyLebesgue N μ) {σ : Measure M} (hσ : IsBoundaryMeasure N σ)
    (u : ℕ → M → ℝ) (hu : ∀ k, IsC1 N (u k)) (hb : ∃ K : ℝ≥0, ∀ k, w12 g μ (u k) ≤ K) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ f : M → ℝ, MemLp f 2 σ ∧
      Tendsto (fun k => eLpNorm (u (φ k) - f) 2 σ) atTop (𝓝 0) := by
  haveI := isFiniteMeasure_of_isLocallyLebesgue hμ
  obtain ⟨A, hA⟩ := trace_interp_sub g hμ hσ
  obtain ⟨K, hK⟩ := hb
  obtain ⟨φ, hφ, f₀, hf₀, hlim⟩ := rellich_kondrachov g hμ u hu ⟨K, hK⟩
  have hmem : ∀ k, MemLp (u k) 2 σ := fun k => memLp_two_of_isC1 g hμ hσ (hu k)
  set F : ℕ → Lp ℝ 2 σ := fun k => (hmem (φ k)).toLp (u (φ k)) with hF
  have hcau : CauchySeq F := by
    rw [EMetric.cauchySeq_iff]
    intro ε hε
    obtain ⟨r, hr0, hr, hrε⟩ := ENNReal.lt_iff_exists_real_btwn.1 hε
    have hr0' : 0 < r := ENNReal.ofReal_pos.1 hr
    have ha : 0 ≤ (A : ℝ) := A.2
    have hκ : 0 ≤ (K : ℝ) := K.2
    set δ : ℝ := r / (4 * ((A : ℝ) * K + 1)) with hδ
    have hδ0 : 0 < δ := by positivity
    set η : ℝ := r * δ / (8 * ((A : ℝ) + 1)) with hη
    have hη0 : 0 < η := by positivity
    have hev : ∀ᶠ k in atTop, eLpNorm (u (φ k) - f₀) 2 μ < ENNReal.ofReal η :=
      (tendsto_order.1 hlim).2 _ (ENNReal.ofReal_pos.2 hη0)
    obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hev
    refine ⟨N₀, fun m hm l hl => ?_⟩
    rw [hF, Lp.edist_toLp_toLp]
    have hd : eLpNorm (u (φ m) - u (φ l)) 2 μ ≤ ENNReal.ofReal η + ENNReal.ofReal η := by
      have e : u (φ m) - u (φ l) = (u (φ m) - f₀) - (u (φ l) - f₀) := by abel
      rw [e]
      refine (eLpNorm_sub_le ?_ ?_ one_le_two).trans (add_le_add (hN₀ m hm).le (hN₀ l hl).le)
      · exact (hu (φ m)).continuous.aestronglyMeasurable.sub hf₀.1
      · exact (hu (φ l)).continuous.aestronglyMeasurable.sub hf₀.1
    have e2 : δ * (4 * ((A : ℝ) * K + 1)) = r := by rw [hδ]; field_simp
    have e3 : δ⁻¹ * (η + η) * (4 * ((A : ℝ) + 1)) = r := by rw [hη]; field_simp; ring
    have h1 : (A : ℝ) * (δ * (K + K)) ≤ r / 2 := by
      have : 4 * (δ * ((A : ℝ) * K)) + 4 * δ = r := by rw [← e2]; ring
      nlinarith
    have h2 : (A : ℝ) * (δ⁻¹ * (η + η)) ≤ r / 4 := by
      have hX : 0 < δ⁻¹ * (η + η) := by positivity
      have : 4 * ((A : ℝ) * (δ⁻¹ * (η + η))) + 4 * (δ⁻¹ * (η + η)) = r := by rw [← e3]; ring
      nlinarith
    calc eLpNorm (u (φ m) - u (φ l)) 2 σ
        ≤ A * (ENNReal.ofReal δ * (w12 g μ (u (φ m)) + w12 g μ (u (φ l))) +
            ENNReal.ofReal δ⁻¹ * eLpNorm (u (φ m) - u (φ l)) 2 μ) :=
          hA δ hδ0 _ _ (hu _) (hu _)
      _ ≤ A * (ENNReal.ofReal δ * ((K : ℝ≥0∞) + K) +
            ENNReal.ofReal δ⁻¹ * (ENNReal.ofReal η + ENNReal.ofReal η)) := by
          gcongr
          · exact hK _
          · exact hK _
      _ = ENNReal.ofReal ((A : ℝ) * (δ * (K + K) + δ⁻¹ * (η + η))) := by
          rw [ENNReal.ofReal_mul ha, ENNReal.ofReal_coe_nnreal,
            ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul hδ0.le,
            ENNReal.ofReal_mul (inv_nonneg.2 hδ0.le), ENNReal.ofReal_add hκ hκ,
            ENNReal.ofReal_add hη0.le hη0.le, ENNReal.ofReal_coe_nnreal]
      _ < ENNReal.ofReal r := by
          rw [ENNReal.ofReal_lt_ofReal_iff hr0']
          nlinarith
      _ < ε := hrε
  obtain ⟨Flim, hFlim⟩ := cauchySeq_tendsto_of_complete hcau
  refine ⟨φ, hφ, Flim, Lp.memLp Flim, ?_⟩
  refine ((Lp.tendsto_Lp_iff_tendsto_eLpNorm' F Flim).1 hFlim).congr fun k => eLpNorm_congr_ae ?_
  exact (hmem (φ k)).coeFn_toLp.sub EventuallyEq.rfl

end Mfd

end Yamabe
