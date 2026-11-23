import Yamabe.RellichManifold

/-!
# Rellich–Kondrachov on a compact manifold with boundary, and lem:positivity

Labels (NOT marked: partial, see SCOPE):

* `lem:positivity` — `Yamabegap.tex:715` (statement l.715–718, proof l.719–721): every step of the
  proof over the measured model, from the Sobolev inequality (`SobolevIneq`), the trace theorem
  (`TraceIneq`), Rellich–Kondrachov (`RellichProp`) and the constancy of a limit with vanishing
  energy on a connected `Σ` (`ConstLimit`, for a limit in `L²`); the constancy statement on a
  compact connected Riemannian manifold with boundary (proved; Rellich–Kondrachov there is
  `Mfd.rellich_kondrachov`, proved in `Yamabe.RellichManifold`, which this file imports);
  and the assemblies with lem:positivity discharged for a model reading such a manifold
  (`cor:negative`'s `hpos`), resting on no `sorry`.

> For every metric $\g$ on the compact connected manifold with non-empty boundary $\Sigma$,
> $\inf_{u\ne0}\Fq_\g(u)>0$. (l.717)

> Suppose $u_k\in W^{1,2}(\Sigma)$ with $\|u_k\|_{L^{\pstar}(\Sigma)}=1$ and $\Fq_\g(u_k)\to0$; then
> $\|\nabla u_k\|_{L^2}\to0$ and $\|u_k\|_{L^{\psharp}(B_j)}\to0$ for every $j$. By
> \eqref{eq:hoelder}, $(u_k)$ is bounded in $W^{1,2}(\Sigma)$, so by the Rellich--Kondrachov
> theorem a subsequence converges in $L^2(\Sigma)$ and weakly in $W^{1,2}(\Sigma)$ to some
> $u_\infty$ with $\|\nabla u_\infty\|_{L^2}\le\liminf\|\nabla u_k\|_{L^2}=0$; since $\Sigma$ is
> connected, $u_\infty\equiv c$ is constant. The trace operator $W^{1,2}(\Sigma)\to L^2(\partial\Sigma)$
> is compact, so the traces converge to $c$ in $L^2(\partial\Sigma)$; but
> $\|u_k\|_{L^2(B_j)}\le\Vol(B_j)^{1/(N-1)}\|u_k\|_{L^{\psharp}(B_j)}\to0$, whence $c=0$. Thus
> $u_k\to0$ in $W^{1,2}(\Sigma)$, and the Sobolev embedding $W^{1,2}(\Sigma)\hookrightarrow
> L^{\pstar}(\Sigma)$ \cite{Hebey1996} gives $\|u_k\|_{L^{\pstar}}\to0$, a contradiction. (l.720)

## What is proved

Over the model, sorry-free: `MeasuredModel.lem_positivity` (lem:positivity, every step of l.720:
the minimising sequence, the normalisation `‖u_k‖_{L^{p*}} = 1` (`F_smul`), `‖∇u_k‖ → 0` and
`‖u_k‖_{L^{p♯}(B_j)} → 0`, the `W^{1,2}` bound through `hoelder_interior`, Rellich, constancy, the
trace step, `c = 0` through `hoelder_boundary`, `u_k → 0` in `W^{1,2}`, Sobolev, contradiction);
`MeasuredModel.cor_negative_of_analytic` (the strict `cor_negative` with `hpos` discharged by
`lem_positivity`). Non-vacuity on the strict two-point toy model: `toy_sobolevIneq`,
`toy_traceIneq`, `toy_rellichProp`, `toy_constLimit` (with `toy_normSq_two`, `toy_w12Sq`,
`toy_memLp`, `tendsto_zero_of_sq`), and `toy_lem_positivity`; `ConstLimit` is the connectedness:
`toyCut_not_constLimit`. On the manifold layer, sorry-free: `Mfd.const_of_tendsto` (the
constancy step for a limit in `L²(μ)`, from `Mfd.const_of_tendsto_of_aestronglyMeasurable`,
`Yamabe.Compactness`), `Mfd.Reads.constLimit` (`ConstLimit` on a model reading `M`) and
`Mfd.readingModel_F` (on the reading model `F^(β)` is eq:trace-sobolev on `C¹(M)`). On the
manifold layer, sorry-free as well, from Rellich–Kondrachov (`Mfd.rellich_kondrachov`,
`Yamabe.RellichManifold`) and the Sobolev and trace theorems
(`Yamabe.ManifoldTheorems`), all proved: `Mfd.Reads.rellichProp`,
`Mfd.Reads.lem_positivity`, `Mfd.Reads.cor_negative` (cor:negative with `hpos` discharged on a
model reading `M`) and `Mfd.lem_positivity` (lem:positivity on `M` itself). None of them assumes
`μ` finite: on a compact `M` that follows from `IsLocallyLebesgue`
(`Mfd.isFiniteMeasure_of_isLocallyLebesgue`).

## What is stated with `sorry`

Nothing. Round 1 stated `Mfd.rellich_kondrachov` here with `sorry`; round 3 proved it in
`Yamabe.RellichManifold` under a primed name, and the integration (T-yamabe-integrate-r3)
deleted the original and gave the proof the round-1 name and statement (that file's SCOPE). Round 1
also stated `Mfd.const_of_tendsto` here with `sorry`, in a form that was false; see SCOPE.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `Σ` compact connected Riemannian with boundary, `N ≥ 3` | on the model: ✓ `N ≥ 3`, compactness as finite `vol_g`, `bvol_g`; connectedness through `ConstLimit`; on `M`: ✓ `CompactSpace`, `ConnectedSpace` (in `const_of_tendsto`), `μ` finite derived (`isFiniteMeasure_of_isLocallyLebesgue`) |
| `∂Σ ≠ ∅` (l.717) | ✓ carried as `∃ j, bvol_g j ≠ 0` (a non-empty boundary has positive area) |
| "for every metric `g`" | ✓ every `FrameMetric` of the model |
| `u ∈ W^{1,2}(Σ) ∖ {0}` | ⚠ read as `Adm` (OQ-44, DEC-186), over the model's `D` |
| Rellich–Kondrachov, compact trace, Sobolev (l.720) | on the model: ⚠ carried as `RellichProp`, `TraceIneq`, `SobolevIneq`, `ConstLimit`; on `M`, transported by `Mfd.Reads.*`: Sobolev and trace proved (`Yamabe.ManifoldTheorems`), the constancy step proved (`Mfd.const_of_tendsto`), Rellich–Kondrachov proved (`Mfd.rellich_kondrachov`, `Yamabe.RellichManifold`); the compact trace is not used (SCOPE) |
| `u_∞ ∈ W^{1,2}(Σ)`, the limit of l.720 | ⚠ read (OQ-93 (c)) as a limit in `L²` (`MemLp f 2`) of the sequence, in `ConstLimit` and `Mfd.const_of_tendsto` |

## SCOPE (disclosed)

* **The constancy step asks a limit in `L²` (finding of T-yamabe-analysis round 2, AUDIT-2;
  repaired by T-yamabe-integrate-r2).** Round 1 stated `MeasuredModel.ConstLimit` and
  `Mfd.const_of_tendsto` with no measurability of the limit `f`; as an `eLpNorm` of a
  non-measurable function is an inner integral, both were false on a manifold carrying a set `S`
  with `μ S ≠ 0` whose measurable subsets are null (a Vitali set in a chart; not in Mathlib at this
  pin): `Mfd.not_const_of_tendsto` (`Yamabe.Compactness`), kept as the record. Both now ask
  `MemLp f 2`, which costs nothing at l.720 (`u_∞ ∈ W^{1,2} ⊂ L²`, and `RellichProp` gives the
  limit in `L²`): `MeasuredModel.lem_positivity` passes the Rellich limit's `MemLp`; the toy
  witnesses `toy_constLimit` and `toyCut_not_constLimit` hold for the repaired Prop;
  `Mfd.const_of_tendsto` and `Mfd.Reads.constLimit` are proved from the round-2 corrected forms
  `Mfd.const_of_tendsto_of_aestronglyMeasurable` and
  `Mfd.Reads.constLimit_of_aestronglyMeasurable`.
* **Weak convergence, read.** The paper's « converges … weakly in `W^{1,2}(Σ)` to some `u_∞` with
  `‖∇u_∞‖ ≤ liminf ‖∇u_k‖ = 0`; since `Σ` is connected, `u_∞ ≡ c` » is carried by `ConstLimit`:
  an `L²` limit of a sequence whose energy tends to `0` is a.e. constant. On a manifold it is
  `Mfd.const_of_tendsto`, proved without weak derivatives (which Mathlib does not have on
  manifolds) by the Poincaré double-integral estimate in charts. Mathlib has no `W^{1,2}(Σ)`; its
  role is played by the model's `D` (on `M`, `C¹(M)`, dense in `W^{1,2}`).
* **Continuity suffices** for the trace step (see `Yamabe.Trace`): the proof here uses the
  trace theorem into `L^{p♯}` (`TraceIneq`), never the compactness of the trace.
* **eq:hoelder at l.720.** The second citation uses the corrected exponent (`hoelder_boundary`:
  `Vol(B_j)^{1/(N-1)}` on the squared norm), as recorded by T-yamabe-quotient (DEC-186).
* **No label is marked while OQ-93 is open.** Since T-yamabe-integrate-r3 the manifold readings
  `Mfd.Reads.lem_positivity`, `Mfd.Reads.cor_negative` and `Mfd.lem_positivity` rest on no `sorry`,
  but under the readings of OQ-93: every locally-Lebesgue `μ` for `vol_g` and every boundary
  measure for the area of `∂Σ` ((a)), `C¹(M)` for `W^{1,2}(Σ)` ((b), which makes lem:positivity
  weaker than printed), and the `L²` limit of the constancy step ((c)). The same integration
  dropped their `[IsFiniteMeasure μ]` binders, now derived, which strengthens them.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Manifold ContDiff Bundle

noncomputable section

namespace Yamabe

/-! ## 1. The model layer -/

namespace MeasuredModel

variable {X D : Type*} [MeasurableSpace X] [AddCommGroup D] [Module ℝ D] {N n : ℕ}
variable (M : MeasuredModel X D N n) (g : FrameMetric X N)

/-- Rellich–Kondrachov on the model (l.720): a sequence bounded in `W^{1,2}(Σ)` has a
subsequence converging in `L²(Σ)`. -/
def RellichProp : Prop :=
  ∀ u : ℕ → D, (∃ K : ℝ, ∀ k, M.w12Sq g (u k) ≤ K) →
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ f : X → ℝ, MemLp f 2 (M.vol g) ∧
      Tendsto (fun k => eLpNorm (M.val (u (φ k)) - f) 2 (M.vol g)) atTop (𝓝 0)

/-- The constancy step of l.720 on a connected `Σ`: an `L²(Σ)` limit `f ∈ L²(Σ)` of a sequence
whose Dirichlet energy tends to `0` is a.e. constant. The limit is asked to be in `L²` (`MemLp f 2`,
as the `u_∞ ∈ W^{1,2} ⊂ L²` of l.720 is, and as `RellichProp` gives it): without measurability the
Prop fails on a model reading a manifold (`Mfd.not_const_of_tendsto`). -/
def ConstLimit : Prop :=
  ∀ (u : ℕ → D) (f : X → ℝ), MemLp f 2 (M.vol g) →
    Tendsto (fun k => M.dirichlet g (u k)) atTop (𝓝 0) →
    Tendsto (fun k => eLpNorm (M.val (u k) - f) 2 (M.vol g)) atTop (𝓝 0) →
      ∃ c : ℝ, f =ᵐ[M.vol g] fun _ => c

/-- The positivity lemma (lem:positivity, l.715–721) over the model: on a model of finite volume
with a boundary component of positive area, with the Sobolev inequality, the trace theorem,
Rellich–Kondrachov and the constancy of energy-free limits, `inf_{u ≠ 0} F_g(u) > 0`. -/
theorem lem_positivity (hN : 3 ≤ N) [IsFiniteMeasure (M.vol g)] [∀ j, IsFiniteMeasure (M.bvol g j)]
    (hV : M.vol g ≠ 0) (hB : ∃ j, M.bvol g j ≠ 0)
    (hD : ∀ u, AEStronglyMeasurable (M.val u) (M.vol g))
    (hS : M.SobolevIneq g) (hT : M.TraceIneq g) (hR : M.RellichProp g) (hC : M.ConstLimit g) :
    0 < M.infF g (fun _ => cN N) := by
  set ν := M.vol g with hν
  have hN' := three_le_cast hN
  have hcN : 0 < cN N := cN_pos (by omega)
  have haN : 0 < aN N := aN_pos hN
  have hVpos : 0 < (ν Set.univ).toReal :=
    ENNReal.toReal_pos (Measure.measure_univ_ne_zero.mpr hV) (measure_ne_top _ _)
  have hadm1 : M.Adm g M.one := by
    unfold Adm
    rw [M.val_one, normSq_one _ (pStar_pos hN)]
    exact Real.rpow_pos_of_pos hVpos _
  have hne : (M.F g (fun _ => cN N) '' {u | M.Adm g u}).Nonempty := ⟨_, M.one, hadm1, rfl⟩
  by_contra hcon
  rw [not_lt] at hcon
  -- a minimising sequence: `u_k ≠ 0` with `F_g(u_k) → 0`
  have hseq : ∀ k : ℕ, ∃ u, M.Adm g u ∧ M.F g (fun _ => cN N) u < 1 / ((k : ℝ) + 1) := by
    intro k
    have hk : M.infF g (fun _ => cN N) < 1 / ((k : ℝ) + 1) :=
      lt_of_le_of_lt hcon (by positivity)
    obtain ⟨_, ⟨u, hu, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt hne hk
    exact ⟨u, hu, hlt⟩
  choose u hadm hF using hseq
  -- normalisation `‖u_k‖_{L^{p*}} = 1`
  set t : ℕ → ℝ := fun k => 1 / Real.sqrt (normSq ν (pStar N) (M.val (u k))) with ht
  have htpos : ∀ k, 0 < t k := fun k => by
    simp only [ht]
    exact one_div_pos.mpr (Real.sqrt_pos.mpr (hadm k))
  set v : ℕ → D := fun k => t k • u k with hvdef
  have hvn : ∀ k, normSq ν (pStar N) (M.val (v k)) = 1 := by
    intro k
    simp only [hvdef, map_smul, normSq_smul, ht]
    rw [div_pow, Real.sq_sqrt (normSq_nonneg _ _ _), one_pow, one_div,
      inv_mul_cancel₀ (ne_of_gt (hadm k))]
  have hvF : ∀ k, M.F g (fun _ => cN N) (v k) < 1 / ((k : ℝ) + 1) := fun k => by
    simp only [hvdef]
    rw [M.F_smul g _ (htpos k).ne' (u k)]
    exact hF k
  have hvF' : ∀ k, M.F g (fun _ => cN N) (v k) =
      aN N * M.dirichlet g (v k) + ∑ j, cN N * normSq (M.bvol g j) (pSharp N) (M.tr (v k)) := by
    intro k
    unfold F traceSobolevQuot
    rw [hvn k, div_one]
  have hsum_nonneg : ∀ k, 0 ≤ ∑ j, cN N * normSq (M.bvol g j) (pSharp N) (M.tr (v k)) :=
    fun k => Finset.sum_nonneg fun j _ => mul_nonneg hcN.le (normSq_nonneg _ _ _)
  -- `‖∇u_k‖_{L²} → 0`
  have hdir_le : ∀ k, M.dirichlet g (v k) ≤ 1 / aN N * (1 / ((k : ℝ) + 1)) := by
    intro k
    have h1 := hvF k
    rw [hvF' k] at h1
    have h2 := hsum_nonneg k
    rw [one_div_mul_eq_div, le_div_iff₀ haN]
    linarith
  have hlim0 : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hdir : Tendsto (fun k => M.dirichlet g (v k)) atTop (𝓝 0) :=
    squeeze_zero (fun k => M.dirichlet_nonneg g _) hdir_le (by simpa using hlim0.const_mul (1 / aN N))
  -- `‖u_k‖_{L^{p♯}(B_j)} → 0`
  have htr_le : ∀ k j, normSq (M.bvol g j) (pSharp N) (M.tr (v k)) ≤
      1 / cN N * (1 / ((k : ℝ) + 1)) := by
    intro k j
    have h1 := hvF k
    rw [hvF' k] at h1
    have h2 : cN N * normSq (M.bvol g j) (pSharp N) (M.tr (v k)) ≤
        ∑ j, cN N * normSq (M.bvol g j) (pSharp N) (M.tr (v k)) :=
      Finset.single_le_sum (f := fun j => cN N * normSq (M.bvol g j) (pSharp N) (M.tr (v k)))
        (fun j _ => mul_nonneg hcN.le (normSq_nonneg _ _ _)) (Finset.mem_univ j)
    have h3 := mul_nonneg haN.le (M.dirichlet_nonneg g (v k))
    rw [one_div_mul_eq_div, le_div_iff₀ hcN]
    linarith
  have htr : ∀ j, Tendsto (fun k => normSq (M.bvol g j) (pSharp N) (M.tr (v k))) atTop (𝓝 0) :=
    fun j => squeeze_zero (fun k => normSq_nonneg _ _ _) (fun k => htr_le k j)
      (by simpa using hlim0.const_mul (1 / cN N))
  -- by eq:hoelder (the interior line), `(u_k)` is bounded in `W^{1,2}(Σ)`
  have hvmem : ∀ k, MemLp (M.val (v k)) (ENNReal.ofReal (pStar N)) ν := fun k => by
    refine ⟨hD _, lt_top_iff_ne_top.mpr fun htop => ?_⟩
    have h1 := hvn k
    simp [normSq, htop] at h1
  have hW : ∀ k, M.w12Sq g (v k) ≤ 1 / aN N + (ν Set.univ).toReal ^ (2 / (N : ℝ)) := by
    intro k
    have h1 := hoelder_interior hN (hvmem k)
    rw [hvn k, mul_one] at h1
    have h2 : 1 / ((k : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      linarith
    have h3 : M.dirichlet g (v k) ≤ 1 / aN N := by
      have := hdir_le k
      have h4 : 1 / aN N * (1 / ((k : ℝ) + 1)) ≤ 1 / aN N := by
        have : 0 < 1 / aN N := by positivity
        nlinarith
      linarith
    unfold w12Sq
    linarith
  -- Rellich–Kondrachov: a subsequence converges in `L²(Σ)`
  obtain ⟨φ, hφ, f, hfm, hconv⟩ := hR v ⟨_, hW⟩
  have hdirφ : Tendsto (fun k => M.dirichlet g (v (φ k))) atTop (𝓝 0) :=
    hdir.comp hφ.tendsto_atTop
  -- `Σ` connected: the limit is a constant `c`
  obtain ⟨c, hfc⟩ := hC (fun k => v (φ k)) f hfm hdirφ hconv
  -- `u_k → c` in `W^{1,2}(Σ)`
  have hL2w : Tendsto (fun k => eLpNorm (M.val (v (φ k) - c • M.one)) (ENNReal.ofReal 2) ν)
      atTop (𝓝 0) := by
    rw [ENNReal.ofReal_ofNat]
    refine hconv.congr fun k => ?_
    rw [M.val_sub_smul_one]
    exact eLpNorm_congr_ae (hfc.mono fun x hx => by simp [hx])
  have hWw : Tendsto (fun k => M.w12Sq g (v (φ k) - c • M.one)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun k => M.dirichlet g (v (φ k) - c • M.one)) atTop (𝓝 0) :=
      hdirφ.congr fun k => (M.dirichlet_sub_smul_one g c _).symm
    have h2 := tendsto_normSq_of_eLpNorm hL2w
    simpa [w12Sq] using h1.add h2
  -- the trace step: the traces converge to `c` in `L²(B_j)`
  obtain ⟨CT, hCT⟩ := M.traceL2_of_traceIneq g hN hT
  obtain ⟨j₀, hj₀⟩ := hB
  have hT1 : Tendsto (fun k => normSq (M.bvol g j₀) 2 (M.tr (v (φ k) - c • M.one))) atTop (𝓝 0) :=
    squeeze_zero (fun k => normSq_nonneg _ _ _) (fun k => (hCT _ j₀).2)
      (by simpa using hWw.const_mul CT)
  -- but `‖u_k‖_{L²(B_j)} ≤ Vol(B_j)^{1/(N-1)} ‖u_k‖_{L^{p♯}(B_j)} → 0` (corrected eq:hoelder)
  obtain ⟨CS0, hTmem⟩ := hT
  have hT2' : Tendsto (fun k => (M.bvol g j₀ Set.univ).toReal ^ (1 / ((N : ℝ) - 1)) *
      normSq (M.bvol g j₀) (pSharp N) (M.tr (v (φ k)))) atTop (𝓝 0) := by
    have := ((htr j₀).comp hφ.tendsto_atTop).const_mul
      ((M.bvol g j₀ Set.univ).toReal ^ (1 / ((N : ℝ) - 1)))
    rw [mul_zero] at this
    exact this
  have hT2 : Tendsto (fun k => normSq (M.bvol g j₀) 2 (M.tr (v (φ k)))) atTop (𝓝 0) :=
    squeeze_zero (fun k => normSq_nonneg _ _ _)
      (fun k => hoelder_boundary hN (hTmem (v (φ k)) j₀).1) hT2'
  have hE1 := tendsto_eLpNorm_of_normSq
    (fun k => by rw [ENNReal.ofReal_ofNat]; exact (hCT (v (φ k) - c • M.one) j₀).1.eLpNorm_ne_top) hT1
  have hE2 := tendsto_eLpNorm_of_normSq
    (fun k => by rw [ENNReal.ofReal_ofNat]; exact (hCT (v (φ k)) j₀).1.eLpNorm_ne_top) hT2
  rw [ENNReal.ofReal_ofNat] at hE1 hE2
  -- whence `c = 0`
  have hc0 : c = 0 := by
    have hle : ∀ k, eLpNorm (fun _ => c) 2 (M.bvol g j₀) ≤
        eLpNorm (M.tr (v (φ k))) 2 (M.bvol g j₀) +
          eLpNorm (M.tr (v (φ k) - c • M.one)) 2 (M.bvol g j₀) := by
      intro k
      have e : (fun _ : X => c) = M.tr (v (φ k)) - M.tr (v (φ k) - c • M.one) := by
        rw [M.tr_sub_smul_one]
        funext x
        simp
      rw [e]
      exact eLpNorm_sub_le (hCT (v (φ k)) j₀).1.aestronglyMeasurable
        (hCT (v (φ k) - c • M.one) j₀).1.aestronglyMeasurable (by norm_num)
    have h0 : eLpNorm (fun _ => c) 2 (M.bvol g j₀) ≤ 0 := by
      have := hE2.add hE1
      rw [add_zero] at this
      exact ge_of_tendsto' this hle
    have h00 : eLpNorm (fun _ => c) 2 (M.bvol g j₀) = 0 := le_antisymm h0 zero_le
    rw [eLpNorm_eq_zero_iff aestronglyMeasurable_const (by norm_num)] at h00
    haveI : (ae (M.bvol g j₀)).NeBot := ae_neBot.mpr hj₀
    obtain ⟨x, hx⟩ := h00.exists
    simpa using hx
  -- thus `u_k → 0` in `W^{1,2}(Σ)`
  subst hc0
  have hWv : Tendsto (fun k => M.w12Sq g (v (φ k))) atTop (𝓝 0) := by
    simpa using hWw
  -- and the Sobolev embedding gives `‖u_k‖_{L^{p*}} → 0`, a contradiction
  obtain ⟨CS, hCS⟩ := hS
  have hlim : Tendsto (fun k => CS * M.w12Sq g (v (φ k))) atTop (𝓝 0) := by
    simpa using hWv.const_mul CS
  obtain ⟨k, hk⟩ := (hlim.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))).exists
  have h1 := hCS (v (φ k))
  rw [hvn] at h1
  linarith

/-- cor:negative (l.502–505) with lem:positivity discharged from the model's analytic properties:
the strict `cor_negative` with `hpos := lem_positivity`. -/
theorem cor_negative_of_analytic {Y E : Type*} [MeasurableSpace Y] [AddCommGroup E] [Module ℝ E]
    (hN : 3 ≤ N) (g : CurvedMetric X N)
    [IsFiniteMeasure (M.vol g.toFrameMetric)] [∀ j, IsFiniteMeasure (M.bvol g.toFrameMetric j)]
    (hV0 : M.vol g.toFrameMetric ≠ 0) (hB0 : ∃ j, M.bvol g.toFrameMetric j ≠ 0)
    (hD : ∀ u, AEStronglyMeasurable (M.val u) (M.vol g.toFrameMetric))
    (hS : M.SobolevIneq g.toFrameMetric) (hT : M.TraceIneq g.toFrameMetric)
    (hR' : M.RellichProp g.toFrameMetric) (hC : M.ConstLimit g.toFrameMetric)
    (hH : M.MinimalBoundary g) {c : ℝ} (hRc : ∀ x, g.R x = c)
    {ι : Type*} {l : Filter ι} [l.NeBot]
    (gs : ι → CurvedMetric X N) (η δ : ι → ℝ) (hη : ∀ i, 0 ≤ η i) (hηt : Tendsto η l (𝓝 0))
    (hclose : ∀ i, UniformlyClose (η i) g.toFrameMetric (gs i).toFrameMetric)
    (hδt : Tendsto δ l (𝓝 0)) (hR : ∀ i x, |(gs i).R x - g.R x| ≤ δ i)
    (hfin : ∀ i, IsFiniteMeasure (M.vol (gs i).toFrameMetric))
    (hV : ∀ i, M.vol (gs i).toFrameMetric ≠ 0) (hB : ∀ i j, M.bvol (gs i).toFrameMetric j ≠ 0)
    (hρ : ∀ i, M.DensityMeasurable (gs i).toFrameMetric) (hHτ : ∀ i, M.MinimalBoundary (gs i))
    (S : ∀ i, GluingInput M Y E (gs i) (fun _ => cN N)) :
    0 < M.infF g.toFrameMetric (fun _ => cN N) ∧ M.Y g < 0 ∧ c < 0 ∧
      c = M.Y g * (M.vol g.toFrameMetric Set.univ).toReal ^ (-(2 / (N : ℝ))) ∧
      ¬ ∀ x, g.R x = 0 :=
  M.cor_negative hN g hD hH hRc
    (M.lem_positivity g.toFrameMetric hN hV0 hB0 hD hS hT hR' hC) gs η δ hη hηt hclose hδt hR
    hfin hV hB hρ hHτ S

end MeasuredModel

/-! ## 2. The hypotheses of `lem_positivity` are satisfiable: the two-point toy model -/

section Toy

lemma toy_normSq_two (u : Bool → ℝ) :
    normSq (toyModel.vol toyMetric) 2 u = u true ^ 2 + u false ^ 2 := by
  have hne : ∀ t : ℝ, ‖t‖ₑ ^ (2 : ℝ) ≠ ⊤ := fun _ =>
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) enorm_ne_top
  rw [normSq_eq_lintegral two_pos, toy_vol, lintegral_count, tsum_fintype, Fintype.sum_bool,
    ENNReal.toReal_add (hne _) (hne _), ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow,
    toReal_enorm, toReal_enorm, div_self two_ne_zero, Real.rpow_one, Real.rpow_two,
    Real.rpow_two, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]

lemma toy_w12Sq (u : Bool → ℝ) :
    toyModel.w12Sq toyMetric u = 2 * (u true - u false) ^ 2 + (u true ^ 2 + u false ^ 2) := by
  unfold MeasuredModel.w12Sq
  rw [toy_dirichlet, show toyModel.val u = u from rfl, toy_normSq_two]

lemma toy_memLp (u : Bool → ℝ) (p : ℝ≥0∞) (ν : Measure Bool) [IsFiniteMeasure ν] : MemLp u p ν :=
  MemLp.of_bound Measurable.of_discrete.aestronglyMeasurable (|u true| + |u false|)
    (ae_of_all _ fun b => by
      cases b <;> simp [Real.norm_eq_abs, abs_nonneg])

/-- The Sobolev inequality on the toy model (`C = 1`). -/
theorem toy_sobolevIneq : toyModel.SobolevIneq toyMetric := by
  refine ⟨1, fun u => ?_⟩
  rw [one_mul, toy_w12Sq]
  have h := toy_normSq_vol_le u
  have : toyModel.val u = u := rfl
  rw [this]
  nlinarith [sq_nonneg (u true - u false)]

/-- The trace theorem on the toy model (`C = 1`). -/
theorem toy_traceIneq : toyModel.TraceIneq toyMetric := by
  haveI := toy_isFiniteMeasure_bvol
  refine ⟨1, fun u j => ⟨toy_memLp _ _ _, ?_⟩⟩
  rw [one_mul, toy_w12Sq, show toyModel.tr u = u from rfl,
    toy_normSq_bvol u j (pSharp_pos (le_refl 3))]
  nlinarith [sq_nonneg (u true - u false), sq_nonneg (u true)]

/-- Rellich–Kondrachov on the toy model (Bolzano–Weierstrass in `ℝ^{Bool}`). -/
theorem toy_rellichProp : toyModel.RellichProp toyMetric := by
  rintro u ⟨K, hK⟩
  haveI := toy_isFiniteMeasure_vol
  have hb : ∀ k b, |u k b| ≤ Real.sqrt K := by
    intro k b
    have h := hK k
    rw [toy_w12Sq] at h
    refine Real.abs_le_sqrt ?_
    cases b <;> nlinarith [sq_nonneg (u k true - u k false), sq_nonneg (u k true),
      sq_nonneg (u k false)]
  have hs : Bornology.IsBounded (Metric.closedBall (0 : Bool → ℝ) (Real.sqrt K)) :=
    Metric.isBounded_closedBall
  have hmem : ∀ k, u k ∈ Metric.closedBall (0 : Bool → ℝ) (Real.sqrt K) := by
    intro k
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
    intro b
    rw [Real.norm_eq_abs]
    exact hb k b
  obtain ⟨a, -, φ, hφ, hlim⟩ := tendsto_subseq_of_bounded hs hmem
  refine ⟨φ, hφ, a, toy_memLp _ _ _, ?_⟩
  have hd : Tendsto (fun k => ‖u (φ k) - a‖) atTop (𝓝 0) := by
    have := (tendsto_iff_norm_sub_tendsto_zero).mp hlim
    simpa using this
  have hle : ∀ k, eLpNorm (toyModel.val (u (φ k)) - a) 2 (toyModel.vol toyMetric) ≤
      toyModel.vol toyMetric Set.univ ^ (2 : ℝ≥0∞).toReal⁻¹ * ENNReal.ofReal ‖u (φ k) - a‖ :=
    fun k => eLpNorm_le_of_ae_bound (ae_of_all _ fun b => norm_le_pi_norm (u (φ k) - a) b)
  have hR : Tendsto (fun k => toyModel.vol toyMetric Set.univ ^ (2 : ℝ≥0∞).toReal⁻¹ *
      ENNReal.ofReal ‖u (φ k) - a‖) atTop (𝓝 0) := by
    have h1 : Tendsto (fun k => ENNReal.ofReal ‖u (φ k) - a‖) atTop (𝓝 0) := by
      simpa using ENNReal.tendsto_ofReal hd
    have h2 := ENNReal.Tendsto.const_mul h1
      (Or.inr (ENNReal.rpow_ne_top_of_nonneg (by norm_num) (measure_ne_top _ _)) :
        (0 : ℝ≥0∞) ≠ 0 ∨ toyModel.vol toyMetric Set.univ ^ (2 : ℝ≥0∞).toReal⁻¹ ≠ ⊤)
    simpa using h2
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hR (fun _ => zero_le) hle

lemma tendsto_zero_of_sq {x : ℕ → ℝ} (h : Tendsto (fun k => x k ^ 2) atTop (𝓝 0)) :
    Tendsto x atTop (𝓝 0) := by
  have h1 : Tendsto (fun k => Real.sqrt (x k ^ 2)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using (Real.continuous_sqrt.tendsto 0).comp h
  simp only [Real.sqrt_sq_eq_abs] at h1
  exact (tendsto_zero_iff_abs_tendsto_zero x).mpr h1

/-- The constancy step on the toy model (its two points are joined by the edge). -/
theorem toy_constLimit : toyModel.ConstLimit toyMetric := by
  intro u f _ hdir hlim
  have hlim2 : Tendsto (fun k => normSq (toyModel.vol toyMetric) 2 (toyModel.val (u k) - f))
      atTop (𝓝 0) := tendsto_normSq_of_eLpNorm (by rwa [ENNReal.ofReal_ofNat])
  simp only [toy_normSq_two] at hlim2
  have hT : Tendsto (fun k => (toyModel.val (u k) - f) true ^ 2) atTop (𝓝 0) :=
    squeeze_zero (fun k => sq_nonneg _) (fun k => le_add_of_nonneg_right (sq_nonneg _)) hlim2
  have hF : Tendsto (fun k => (toyModel.val (u k) - f) false ^ 2) atTop (𝓝 0) :=
    squeeze_zero (fun k => sq_nonneg _) (fun k => le_add_of_nonneg_left (sq_nonneg _)) hlim2
  have hD : Tendsto (fun k => (u k true - u k false) ^ 2) atTop (𝓝 0) := by
    have := hdir.const_mul (1 / 2)
    simp only [toy_dirichlet, mul_zero] at this
    refine this.congr fun k => ?_
    ring
  have h1 := tendsto_zero_of_sq hT
  have h2 := tendsto_zero_of_sq hF
  have h3 := tendsto_zero_of_sq hD
  have hsum := (h3.sub h1).add h2
  simp only [sub_zero, add_zero] at hsum
  have hc : Tendsto (fun _ : ℕ => f true - f false) atTop (𝓝 0) := by
    refine hsum.congr fun k => ?_
    simp only [Pi.sub_apply, show toyModel.val (u k) = u k from rfl]
    ring
  have heq : f true - f false = 0 := tendsto_nhds_unique tendsto_const_nhds hc
  refine ⟨f true, ae_of_all _ fun b => ?_⟩
  cases b
  · simp only; linarith
  · rfl

/-- The hypotheses of `MeasuredModel.lem_positivity` hold jointly on the two-point toy model, and
it recovers `inf F > 0` there. -/
theorem toy_lem_positivity : 0 < toyModel.infF toyMetric (fun _ => cN 3) := by
  haveI := toy_isFiniteMeasure_vol
  haveI := toy_isFiniteMeasure_bvol
  exact toyModel.lem_positivity toyMetric (le_refl 3) toy_vol_ne_zero
    ⟨0, by rw [toy_bvol]; exact Measure.dirac_ne_zero⟩
    (fun _ => Measurable.of_discrete.aestronglyMeasurable) toy_sobolevIneq toy_traceIneq
    toy_rellichProp toy_constLimit

/-- `ConstLimit` is the connectedness of `Σ`: it fails on `toyCut` (an interior point cut off from
the boundary point), where `inf F = 0` (`toyCut_infF`). -/
theorem toyCut_not_constLimit : ¬ toyCut.ConstLimit toyMetric := by
  intro h
  set e : Bool → ℝ := fun b => if b then 1 else 0 with he
  have hd : ∀ k : ℕ, toyCut.dirichlet toyMetric ((fun _ => e) k) = 0 := fun _ => by
    simp [MeasuredModel.dirichlet, MeasuredModel.gradSq, toyCut]
  haveI : IsFiniteMeasure (toyCut.vol toyMetric) := toy_isFiniteMeasure_vol
  obtain ⟨c, hc⟩ := h (fun _ => e) e (toy_memLp e 2 _)
    (tendsto_const_nhds.congr fun k => (hd k).symm)
    (by simp [show toyCut.val e = e from rfl])
  have hv : toyCut.vol toyMetric = Measure.count := toy_vol
  rw [hv] at hc
  have hc' := Measure.ae_count_iff.mp hc
  have h1 := hc' true
  have h2 := hc' false
  simp [he] at h1 h2
  linarith

end Toy

/-! ## 3. The manifold layer -/

namespace Mfd

variable {N : ℕ} [NeZero N]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace N) M]
  [IsManifold (𝓡∂ N) ∞ M] [MeasurableSpace M] [BorelSpace M]

/-- **Constancy of energy-free limits** on a compact connected manifold with boundary (l.720, «
`‖∇u_∞‖_{L²} ≤ liminf ‖∇u_k‖_{L²} = 0`; since `Σ` is connected, `u_∞ ≡ c` »), for a limit
`f ∈ L²(μ)`: `Mfd.const_of_tendsto_of_aestronglyMeasurable` (`Yamabe.Compactness`, the
Poincaré double-integral estimate in charts). Round 1 stated it without `MemLp f 2 μ`, which made it
false (`Mfd.not_const_of_tendsto`). -/
theorem const_of_tendsto [CompactSpace M] [T2Space M] [ConnectedSpace M]
    (g : RiemannianMetric N M) {μ : Measure M} (hμ : IsLocallyLebesgue N μ)
    (u : ℕ → M → ℝ) (hu : ∀ k, IsC1 N (u k)) (f : M → ℝ) (hf : MemLp f 2 μ)
    (hgrad : Tendsto (fun k => eLpNorm (gradNorm g (u k)) 2 μ) atTop (𝓝 0))
    (hlim : Tendsto (fun k => eLpNorm (u k - f) 2 μ) atTop (𝓝 0)) :
    ∃ c : ℝ, f =ᵐ[μ] fun _ => c :=
  const_of_tendsto_of_aestronglyMeasurable g hμ u hu f hf.aestronglyMeasurable hgrad hlim

namespace Reads

variable {D : Type*} [AddCommGroup D] [Module ℝ D] {n : ℕ} {Mm : MeasuredModel M D N n}
  {gm : FrameMetric M N} {g : RiemannianMetric N M} {μ : Measure M} {σ : Fin n → Measure M}

/-- Rellich–Kondrachov on a model reading a compact manifold with boundary. -/
theorem rellichProp [CompactSpace M] [T2Space M]
    (hr : Reads Mm gm g μ σ) (hμ : IsLocallyLebesgue N μ) : Mm.RellichProp gm := by
  haveI := isFiniteMeasure_of_isLocallyLebesgue hμ
  rintro u ⟨K, hK⟩
  have hf := fun k => hr.c1 (u k)
  have hbound : ∃ K' : ℝ≥0, ∀ k, w12 g μ (Mm.val (u k)) ≤ K' := by
    refine ⟨(2 * Real.sqrt K).toNNReal, fun k => ?_⟩
    have ha : eLpNorm (gradNorm g (Mm.val (u k))) 2 μ ≠ ⊤ := (eLpNorm_gradNorm_lt_top g (hf k)).ne
    have hb : eLpNorm (Mm.val (u k)) 2 μ ≠ ⊤ := (memLp_of_isC1 (hf k) 2).eLpNorm_ne_top
    have hk := hK k
    unfold MeasuredModel.w12Sq at hk
    rw [hr.dirichlet_eq, hr.vol_eq] at hk
    unfold normSq at hk
    rw [ENNReal.ofReal_ofNat] at hk
    set a := (eLpNorm (gradNorm g (Mm.val (u k))) 2 μ).toReal
    set b := (eLpNorm (Mm.val (u k)) 2 μ).toReal
    have ha2 : a ≤ Real.sqrt K :=
      (le_abs_self a).trans (Real.abs_le_sqrt (by nlinarith [sq_nonneg b]))
    have hb2 : b ≤ Real.sqrt K :=
      (le_abs_self b).trans (Real.abs_le_sqrt (by nlinarith [sq_nonneg a]))
    unfold w12
    rw [← ENNReal.ofReal_toReal (ENNReal.add_ne_top.mpr ⟨ha, hb⟩), ENNReal.toReal_add ha hb]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  obtain ⟨φ, hφ, f, hfm, hconv⟩ := rellich_kondrachov g hμ (fun k => Mm.val (u k)) hf hbound
  refine ⟨φ, hφ, f, ?_, ?_⟩
  · rw [hr.vol_eq]; exact hfm
  · rw [hr.vol_eq]; exact hconv

/-- The constancy step on a model reading a compact connected manifold with boundary:
`constLimit_of_aestronglyMeasurable` (`Yamabe.Compactness`) at `MemLp.aestronglyMeasurable`. -/
theorem constLimit [CompactSpace M] [T2Space M] [ConnectedSpace M]
    (hr : Reads Mm gm g μ σ) (hμ : IsLocallyLebesgue N μ) : Mm.ConstLimit gm :=
  haveI := isFiniteMeasure_of_isLocallyLebesgue hμ
  fun u f hf hdir hlim =>
    hr.constLimit_of_aestronglyMeasurable hμ u f hf.aestronglyMeasurable hdir hlim

/-- The positivity lemma (lem:positivity, l.717) for a model reading a compact connected
Riemannian manifold with non-empty boundary: `inf F_g > 0`, from the Sobolev, trace and Rellich
theorems on `M`. -/
theorem lem_positivity (hN : 3 ≤ N) [CompactSpace M] [T2Space M] [ConnectedSpace M]
    [∀ j, IsFiniteMeasure (σ j)]
    (hr : Reads Mm gm g μ σ) (hμ : IsLocallyLebesgue N μ) (hσ : ∀ j, IsBoundaryMeasure N (σ j))
    (hV : μ ≠ 0) (hB : ∃ j, σ j ≠ 0) :
    0 < Mm.infF gm (fun _ => cN N) := by
  haveI := isFiniteMeasure_of_isLocallyLebesgue hμ
  haveI : IsFiniteMeasure (Mm.vol gm) := by rw [hr.vol_eq]; infer_instance
  haveI : ∀ j, IsFiniteMeasure (Mm.bvol gm j) := fun j => by rw [hr.bvol_eq j]; infer_instance
  obtain ⟨j, hj⟩ := hB
  exact Mm.lem_positivity gm hN (by rw [hr.vol_eq]; exact hV) ⟨j, by rw [hr.bvol_eq j]; exact hj⟩
    hr.hD (hr.sobolevIneq hN hμ) (hr.traceIneq hN hμ hσ) (hr.rellichProp hμ) (hr.constLimit hμ)

/-- cor:negative (l.502–505) on a model reading a compact connected Riemannian manifold with
non-empty boundary, with lem:positivity (`hpos`) discharged by the Sobolev, trace and Rellich
theorems on `M` (the strict `cor_negative`, its other inputs carried as there). -/
theorem cor_negative {Y E : Type*} [MeasurableSpace Y] [AddCommGroup E] [Module ℝ E]
    (hN : 3 ≤ N) [CompactSpace M] [T2Space M] [ConnectedSpace M]
    [∀ j, IsFiniteMeasure (σ j)] {gc : CurvedMetric M N}
    (hr : Reads Mm gc.toFrameMetric g μ σ) (hμ : IsLocallyLebesgue N μ)
    (hσ : ∀ j, IsBoundaryMeasure N (σ j)) (hV0 : μ ≠ 0) (hB0 : ∃ j, σ j ≠ 0)
    (hH : Mm.MinimalBoundary gc) {c : ℝ} (hRc : ∀ x, gc.R x = c)
    {ι : Type*} {l : Filter ι} [l.NeBot]
    (gs : ι → CurvedMetric M N) (η δ : ι → ℝ) (hη : ∀ i, 0 ≤ η i) (hηt : Tendsto η l (𝓝 0))
    (hclose : ∀ i, MeasuredModel.UniformlyClose (η i) gc.toFrameMetric (gs i).toFrameMetric)
    (hδt : Tendsto δ l (𝓝 0)) (hR : ∀ i x, |(gs i).R x - gc.R x| ≤ δ i)
    (hfin : ∀ i, IsFiniteMeasure (Mm.vol (gs i).toFrameMetric))
    (hV : ∀ i, Mm.vol (gs i).toFrameMetric ≠ 0) (hB : ∀ i j, Mm.bvol (gs i).toFrameMetric j ≠ 0)
    (hρ : ∀ i, Mm.DensityMeasurable (gs i).toFrameMetric) (hHτ : ∀ i, Mm.MinimalBoundary (gs i))
    (S : ∀ i, GluingInput Mm Y E (gs i) (fun _ => cN N)) :
    0 < Mm.infF gc.toFrameMetric (fun _ => cN N) ∧ Mm.Y gc < 0 ∧ c < 0 ∧
      c = Mm.Y gc * (Mm.vol gc.toFrameMetric Set.univ).toReal ^ (-(2 / (N : ℝ))) ∧
      ¬ ∀ x, gc.R x = 0 := by
  haveI := isFiniteMeasure_of_isLocallyLebesgue hμ
  haveI : IsFiniteMeasure (Mm.vol gc.toFrameMetric) := by rw [hr.vol_eq]; infer_instance
  exact Mm.cor_negative hN gc hr.hD hH hRc (hr.lem_positivity hN hμ hσ hV0 hB0) gs η δ hη hηt
    hclose hδt hR hfin hV hB hρ hHτ S

end Reads

/-! ### lem:positivity on the manifold, through the reading model -/

omit [BorelSpace M] in
/-- On the reading model of `(M, g, μ, σ)` the quotient `F^(β)` is the trace-Sobolev quotient of
eq:trace-sobolev (l.489) on `C¹(M)`:
`F^(β)(u) = (a_N ‖∇u‖²_{L²(μ)} + Σ_j β_j ‖u‖²_{L^{p♯}(σ_j)}) / ‖u‖²_{L^{p*}(μ)}`. -/
theorem readingModel_F (g : RiemannianMetric N M) (μ : Measure M) {n : ℕ} (σ : Fin n → Measure M)
    (β : Fin n → ℝ) (u : C1 N M) :
    (readingModel g μ σ).F (flatFrame N M) β u =
      (aN N * normSq μ 2 (gradNorm g u) + ∑ j, β j * normSq (σ j) (pSharp N) u) /
        normSq μ (pStar N) u := by
  have hr := reads_readingModel g μ σ
  unfold MeasuredModel.F traceSobolevQuot
  rw [hr.dirichlet_eq u, hr.vol_eq]
  simp only [hr.bvol_eq, hr.tr_eq]
  rfl

/-- The positivity lemma (lem:positivity, l.717) on a compact connected Riemannian manifold with
non-empty boundary: `inf_{u ∈ C¹(M), u ≠ 0} F_g(u) > 0`, `F_g` the trace-Sobolev quotient of
eq:trace-sobolev (`readingModel_F`), from the Sobolev, trace and Rellich theorems on `M`. -/
theorem lem_positivity (hN : 3 ≤ N) [CompactSpace M] [T2Space M] [ConnectedSpace M]
    (g : RiemannianMetric N M) {μ : Measure M} (hμ : IsLocallyLebesgue N μ)
    {n : ℕ} {σ : Fin n → Measure M} [∀ j, IsFiniteMeasure (σ j)]
    (hσ : ∀ j, IsBoundaryMeasure N (σ j)) (hV : μ ≠ 0) (hB : ∃ j, σ j ≠ 0) :
    0 < (readingModel g μ σ).infF (flatFrame N M) (fun _ => cN N) :=
  (reads_readingModel g μ σ).lem_positivity hN hμ hσ hV hB

end Mfd

end Yamabe
