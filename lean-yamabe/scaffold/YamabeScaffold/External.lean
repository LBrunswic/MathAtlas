import YamabeScaffold.Rellich

/-!
# The named external facts of § 6 (DEC-184), and the paper's steps that consume them

Labels (NOT marked: every row stays partial, see SCOPE; the declarations are named externals and
assemblies over the measured model, never anchors):

* `lem:kobayashi` — `Yamabegap.tex:613`: (a) with its printed left side `EH(Σ, u^{4/(N-2)} g)`,
  through Escobar's conformal law (`kobayashi_EH`, l.619–620);
* `prop:nonpositive` — `Yamabegap.tex:476`: both sentences (`prop_nonpositive`), the first from
  Akutagawa–Botvinnik Cor. 5.3, thm:yamabe (b) and Gromov–Lawson (proof l.641–645), the second
  with lem:kobayashi (b) from the Sobolev inequality;
* `lem:gluing-estimate` — `Yamabegap.tex:648`: with thm:yamabe (b) supplying `h̄` (l.658) and
  `β_j = YB_[g_j](D_j)` (`lem_gluing_estimate_of_yamabe`);
* `thm:upper-bound` — `Yamabegap.tex:493` and `cor:negative` — `Yamabegap.tex:502`: from the
  externals (fact (iv) for `β_j = c_N`, thm:yamabe (b), the conformal law, l.724) and
  lem:positivity from the analytic properties (`cor_negative_of_externals`);
* `lem:positivity` — `Yamabegap.tex:715`: consumed there; proved in `YamabeScaffold.Rellich`.
* eq:cN (l.337–340, `EHB_flatBall`) and l.465 (`ClosedConformal.sigma_nonpos`).

> We shall use the following facts. [...] (i) Every conformal class contains a metric with minimal
> boundary, $H\equiv0$ \cite[Lemma~1.1]{MR1152225} [...] (ii) Under mild hypotheses---always
> satisfied for $N=3$---the infimum $\Y_{[\g]}(\Sigma)$ is attained by a smooth metric with
> constant scalar curvature and minimal boundary [...] (iv) For every compact $(\Sigma,\g)$ with
> boundary, $\YB_{[\g]}(\Sigma)\le\YB(\bar B^N)=\EHB(\bar B^N,\g_{\mathrm{flat}})$, and the flat ball
> attains the boundary Yamabe constant of its conformal class \cite{Escobar1988,MR1173925}.
> Explicitly, $\cN:=\YB(\bar B^N) = 2(N-1)\,\omega_{N-1}^{1/(N-1)}$ [...] (l.330–339)

> By Theorem~\ref{thm:yamabe}(b) there is a smooth $\psi>0$ on $\Sigbar$ such that
> $\bar h:=\psi^{4/(N-2)}\gbar$ has constant scalar curvature
> $\Rs_{\bar h}=\Y_{[\gbar]}(\Sigbar)\Vol(\Sigbar,\bar h)^{-2/N}\le0$. (l.658)

> [...] Corollary~5.3 of \cite{MR1957657} (a consequence of their gluing Theorem~5.1) shows that
> the double $X:=\Sigma\cup_{\partial\Sigma}(-\Sigma)$, a closed manifold, has positive Yamabe
> invariant. By Theorem~\ref{thm:yamabe}(b) a conformal class with positive Yamabe constant
> contains a metric of positive scalar curvature, so $X$ carries such a metric. [...] which is
> enlargeable because $\Sigbar$ is, enlargeability being preserved under connected sums with closed
> manifolds \cite{MR569070}; closed enlargeable manifolds carry no metric of positive scalar
> curvature \cite{MR569070} [...] (l.641–645)

> Since $H_\g\equiv0$, the approximation theorem of Akutagawa and Botvinnik
> \cite[Theorem~4.6]{MR1957657} provides metrics $\tilde\g_\tau$ on $\Sigma$ with minimal boundary
> such that $\tilde\g_\tau\to\g$ and $\Rs_{\tilde\g_\tau}\to\Rs_\g$ in the $C^0$ topology [...] (l.690)

> Since $\sigma(\Sigbar)\le0$, $\Y_{[\gbar_\tau]}(\Sigbar)\le0$, and since $\gbar_\tau|_{D_j}$ is in
> the conformal class of the flat ball, the constants of Lemma~\ref{lem:gluing-estimate} are
> $\beta_j=\cN$ by fact (iv) of Sec.~\ref{sec:boundary}. (l.724)

## The externals (`def … : Prop`)

* **The Yamabe theorem** (thm:yamabe, l.183–188; MR125546, MR240748, MR448404, Aubin1976JMPA,
  MR788292), part (b) in the two forms § 6 uses: `YamabePSC` (l.641, on a closed manifold read
  through its conformal classes, `ClosedConformal`) and `Filling.YamabeB` (l.658, on `Σ̄` read
  through its pieces; `Y_[ḡ](Σ̄)` is `Filling.Ybar`, through eq:conformal-energy, l.178; the
  produced data are `Filling.YamabeData`). Part (a) (Aubin's bound) is not used in § 6.
* **Akutagawa–Botvinnik** (MR1957657): `MeasuredModel.AB46` (Theorem 4.6, l.690; its conclusion
  for a given family is `MeasuredModel.ABFamily`), `MeasuredModel.AB53` (Corollary 5.3, l.641).
* **Gromov–Lawson** (MR569070): `GromovLawson` (l.645: the double, enlargeable, carries no metric
  of positive scalar curvature; the same for any closed enlargeable manifold, l.465).
* **Escobar's facts** (MR1152225, MR1173925, Escobar1988): `MeasuredModel.EscobarLaw`
  (eq:conformal-energy-bdry, l.324–330), `MeasuredModel.EscobarI` (fact (i), l.332),
  `MeasuredModel.EscobarII` (fact (ii), l.333), `MeasuredModel.EscobarIV` (fact (iv) in the form
  used at l.724). Fact (iii) is lem:kobayashi itself (l.334).

## What is proved (no `sorry`, standard axioms)

`ClosedConformal.sigma_nonpos` (l.465); `MeasuredModel.prop_nonpositive_first`,
`MeasuredModel.prop_nonpositive` (prop:nonpositive); `MeasuredModel.kobayashi_EH`
(lem:kobayashi (a), printed left side); `MeasuredModel.EHB_flatBall` (eq:cN);
`Filling.YamabeData.boundaryYamabe` (fact (iv) at l.724), `Filling.YamabeData.gluingInput`,
`Filling.nonempty_gluingInput`; `Filling.lem_gluing_estimate_of_yamabe`;
`MeasuredModel.cor_negative_of_externals` (thm:upper-bound and cor:negative).

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `(Σ, g)` compact Riemannian with boundary; `Σ̄` closed, through its pieces | ⚠ read in the measured model (DEC-186, OQ-44), as the strict library |
| `Y_[ḡ](Σ̄) ≤ σ(Σ̄) ≤ 0` (thm:upper-bound, l.495, l.724) | ⚠ read at the metrics used: `Ybar ≤ 0` per `τ` (SCOPE) |
| `Σ̄` enlargeable; boundary classes positive (prop:nonpositive, l.478) | ⚠ through the externals (`AB53`, `GromovLawson`): not modelled |
| lem:gluing (l.685–695) | ⚠ carried: the family (`ABFamily`, A–B Thm 4.6's conclusion) and the fillings with caps in the flat class (`EscobarIV`) |
| the analytic inputs of lem:positivity and lem:kobayashi (b) | ⚠ the model's properties `SobolevIneq`, `TraceIneq`, `RellichProp`, `ConstLimit` (`ConstLimit` for a limit in `L²`); for a model reading a manifold, `SobolevIneq` and `TraceIneq` are discharged sorry-free (`YamabeScaffold.ManifoldTheorems`), `ConstLimit` sorry-free (`YamabeScaffold.Rellich`), `RellichProp` from the `sorry`-stated `Mfd.rellich_kondrachov` |
| `N ≥ 3`, compactness, `Σ ≠ ∅`, `∂Σ ≠ ∅` | ✓ carried: `3 ≤ N`, finite `vol_g`, `bvol_g`, `vol_g ≠ 0`, `∃ j, bvol_g j ≠ 0` |

## SCOPE (disclosed)

* The model carries the curvatures `R`, `H` as free data (`CurvedMetric`), so an external cannot be
  quantified over all metrics (it would be unsatisfiable: change `H` and the law fails); each
  external is stated at the data where the paper invokes it, as the strict library does with its
  carried inputs. For the same reason `YamabeB` asks Escobar's law at the metric it produces: that
  `h̄` carries the curvatures of `ψ^{4/(N-2)} ḡ` is what the law says in the model.
* The double `X` and the closed `Σ̄` of `GromovLawson`, `AB53`, `YamabePSC` are read through their
  conformal classes (`ClosedConformal`): enlargeability and connected sums have no counterpart in
  the model. Nothing ties that `ClosedConformal` to the double of `Σ`, so the three together are
  weak: a `ClosedConformal` satisfying all three exists iff `M.Y g ≤ 0` (the auditor's probe,
  AUDIT-1 of T-yamabe-analysis), and `prop_nonpositive`'s first sentence restates its own
  hypotheses.
* `AB46` is consumed by lem:gluing (l.690), whose construction (l.690–694) is not formalized: its
  output (the family and the fillings) is a hypothesis of `cor_negative_of_externals`. As stated,
  `AB46` holds for every metric of every model (a constant family; it drops the collar structure
  of l.690), and `EscobarI` is likewise trivially satisfiable (argued): neither is consumed by a
  theorem here.
* `EscobarI`, `EscobarII` are consumed only by rem:existence (l.483), commentary, not formalized.
* `σ(Σ̄) ≤ 0` (thm:upper-bound, l.495, l.724) is read at the metrics the proof uses: `Ybar ≤ 0` at
  each `ḡ_τ`, since `σ` (a supremum over all conformal classes) has no counterpart in the model.
* Non-vacuity of `YamabeB`: not in this file. The auditor's probe (AUDIT-1) shows it satisfiable
  with one boundary component (the toy filling with `R ≡ 0`, `H ≡ 0`, `ψ ≡ 1`, `h̄ = ḡ`, `c = 0`,
  `Ybar = 0`), standard axioms; that all inputs of `cor_negative_of_externals` hold at once is not
  shown.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

noncomputable section

namespace Yamabe

/-! ## 0. Closed manifolds through their conformal classes -/

/-- A closed manifold (`Σ̄`, or the double `X` of l.641) seen through its conformal classes: the
classes, their Yamabe constants `Y(·, [ḡ])` (eq:yamabe-constant, l.168), and whether a class
contains a metric of positive scalar curvature. -/
structure ClosedConformal where
  /-- the conformal classes of Riemannian metrics -/
  Cls : Type
  /-- the Yamabe constant of a class -/
  Y : Cls → ℝ
  /-- the class contains a metric of positive scalar curvature -/
  PSC : Cls → Prop

namespace ClosedConformal

variable (X : ClosedConformal)

/-- The Yamabe invariant `σ = sup_{[ḡ]} Y(·, [ḡ])` (eq:yamabe-invariant, l.170). -/
def sigma : ℝ := ⨆ C, X.Y C

/-- The manifold carries a metric of positive scalar curvature. -/
def HasPSC : Prop := ∃ C, X.PSC C

end ClosedConformal

/-! ## 1. The Yamabe theorem (thm:yamabe, l.183–188) -/

/-- **thm:yamabe (b)** in the form used at l.641: a conformal class with positive Yamabe constant
contains a metric of positive scalar curvature (the minimiser has constant scalar curvature
`Y · Vol^{-2/N} > 0`). -/
def YamabePSC (X : ClosedConformal) : Prop := ∀ C, 0 < X.Y C → X.PSC C

namespace Filling

variable {X D Y E : Type*} [MeasurableSpace X] [AddCommGroup D] [Module ℝ D]
  [MeasurableSpace Y] [AddCommGroup E] [Module ℝ E] {N n : ℕ}
variable (F : Filling X Y E N n) (M : MeasuredModel X D N n) (gbar : GluedMetric X Y N n)

/-- A function on `Σ̄ = Σ ∪ ⊔ D_j`, through its pieces: `u` on `Σ`, `w j` on `D_j`. -/
structure BarFactor (D E : Type*) (n : ℕ) where
  /-- on `Σ` -/
  u : D
  /-- on `D_j` -/
  w : Fin n → E

/-- `‖ψ‖²_{L^{p*}(Σ̄, ḡ)}`, the `L^{p*}` norm over the pieces. -/
def normSqBar (ψ : BarFactor D E n) : ℝ :=
  ((∫⁻ x, ‖M.val ψ.u x‖ₑ ^ pStar N ∂(M.vol gbar.body.toFrameMetric)) +
      ∑ j, ∫⁻ y, ‖(F.piece j).val (ψ.w j) y‖ₑ ^ pStar N
        ∂((F.piece j).vol (gbar.cap j).toFrameMetric)).toReal ^ (2 / pStar N)

/-- The closed conformal energy (eq:conformal-energy, l.178) of `ḡ` at `ψ`, over the pieces:
`(∫_{Σ̄} a_N |∇ψ|² + R_ḡ ψ²) / ‖ψ‖²_{L^{p*}}` (no boundary term: `Σ̄` is closed). -/
def confEnergyBar (ψ : BarFactor D E n) : ℝ :=
  (aN N * (M.dirichlet gbar.body.toFrameMetric ψ.u +
        ∑ j, (F.piece j).dirichlet (gbar.cap j).toFrameMetric (ψ.w j)) +
      (∫ x, gbar.body.R x * M.val ψ.u x ^ 2 ∂(M.vol gbar.body.toFrameMetric) +
        ∑ j, ∫ y, (gbar.cap j).R y * (F.piece j).val (ψ.w j) y ^ 2
          ∂((F.piece j).vol (gbar.cap j).toFrameMetric))) / F.normSqBar M gbar ψ

/-- `ψ` is a competitor on `Σ̄`: positive on every piece, one function across each `B_j`, of
positive finite `L^{p*}` norm. -/
def BarAdm (ψ : BarFactor D E n) : Prop :=
  M.Pos ψ.u ∧ (∀ j, (F.piece j).Pos (ψ.w j)) ∧
    (∀ j, ∀ᵐ x ∂(M.bvol gbar.body.toFrameMetric j), M.tr ψ.u x = (F.piece j).tr (ψ.w j) (F.glue j x)) ∧
    0 < F.normSqBar M gbar ψ

/-- The Yamabe constant `Y_[ḡ](Σ̄) = inf_{ψ > 0} EH(Σ̄, ψ^{4/(N-2)} ḡ)` (eq:yamabe-constant,
l.168), through the closed conformal law eq:conformal-energy (l.178), over the pieces. -/
def Ybar : ℝ := sInf (F.confEnergyBar M gbar '' {ψ | F.BarAdm M gbar ψ})

/-- The data thm:yamabe (b) produces on `(Σ̄, ḡ)` (l.187, as used at l.658): a smooth `ψ > 0` on
`Σ̄` attaining `Y_[ḡ](Σ̄)`, and `h̄ = ψ^{4/(N-2)} ḡ` (piece by piece), of constant scalar curvature
`R_h̄ = Y_[ḡ](Σ̄) Vol(Σ̄, h̄)^{-2/N}`, smooth across each `B_j` (the mean curvatures flip, the areas
match); the regularity a smooth `ψ` on a compact `Σ̄` has. -/
structure YamabeData where
  /-- the minimiser `ψ` -/
  ψ : BarFactor D E n
  /-- `h̄ = ψ^{4/(N-2)} ḡ` -/
  hb : GluedMetric X Y N n
  /-- `R_h̄` -/
  c : ℝ
  adm : F.BarAdm M gbar ψ
  minimizes : F.confEnergyBar M gbar ψ = F.Ybar M gbar
  conf : M.IsConformal gbar.body.toFrameMetric hb.body.toFrameMetric ψ.u
  confCap : ∀ j, (F.piece j).IsConformal (gbar.cap j).toFrameMetric (hb.cap j).toFrameMetric (ψ.w j)
  yamabe : F.IsYamabeMetric M hb (F.Ybar M gbar) c
  flip : F.MeanCurvatureFlip M hb
  bmatch : F.BoundaryMatch M hb
  val_meas : AEStronglyMeasurable (M.val ψ.u) (M.vol gbar.body.toFrameMetric)
  tr_meas : ∀ j, AEStronglyMeasurable (M.tr ψ.u) (M.bvol gbar.body.toFrameMetric j)
  tr_eq : ∀ j, M.tr ψ.u =ᵐ[M.bvol gbar.body.toFrameMetric j] M.val ψ.u
  vol_finite : IsFiniteMeasure (M.vol hb.body.toFrameMetric)
  bvol_finite : ∀ j, IsFiniteMeasure (M.bvol hb.body.toFrameMetric j)
  capAdmB : ∀ j, (F.piece j).AdmB (gbar.cap j).toFrameMetric (ψ.w j)

end Filling

/-! ## 2. Escobar's facts (MR1152225, MR1173925, Escobar1988) -/

namespace MeasuredModel

variable {X D : Type*} [MeasurableSpace X] [AddCommGroup D] [Module ℝ D] {N n : ℕ}
variable (M : MeasuredModel X D N n)

/-- **The conformal law** eq:conformal-energy-bdry (MR1152225, MR1173925; l.324–330), for
`h = u^{4/(N-2)} g`: `EH(Σ, h) ‖u‖²_{L^{p*}} = a_N ‖∇u‖² + ∫ R_g u² + 2(N−1) ∫_{∂Σ} H_g u²`, and the
same right side is `EHB(Σ, h) ‖u‖²_{L^{p♯}(∂Σ)}`. The model carries curvatures as data, so the law
is asked at a given triple `(g, u, h)`: it says that the curvatures of `h` are those of
`u^{4/(N-2)} g`. -/
def EscobarLaw (g h : CurvedMetric X N) (u : D) : Prop :=
  M.IsConformal g.toFrameMetric h.toFrameMetric u → M.ConformalLaw g u h ∧ M.ConformalLawB g u h

/-- **Escobar's fact (i)** (MR1152225, Lemma 1.1; l.332): the conformal class of `g` contains a
metric with minimal boundary. -/
def EscobarI (g : CurvedMetric X N) : Prop :=
  ∃ (u : D) (h : CurvedMetric X N), M.IsConformal g.toFrameMetric h.toFrameMetric u ∧
    M.EscobarLaw g h u ∧ M.MinimalBoundary h

/-- **Escobar's fact (ii)** (MR1152225, MR2189679, MR3210959; l.333), for `N = 3` or under the
mild hypotheses of the sources: `Y_[g](Σ)` is attained by a metric of constant scalar curvature and
minimal boundary in the class of `g`. -/
def EscobarII (g : CurvedMetric X N) : Prop :=
  ∃ (u : D) (h : CurvedMetric X N) (c : ℝ), M.IsConformal g.toFrameMetric h.toFrameMetric u ∧
    M.EscobarLaw g h u ∧ M.MinimalBoundary h ∧ (∀ x, h.R x = c) ∧ M.EH h = M.Y g

/-- **Escobar's fact (iv)** (Escobar1988, MR1173925; l.335–339) in the form used at l.724: `k` is
in the conformal class of the flat unit ball `B̄^N`, whose boundary Yamabe constant
`YB(B̄^N) = EHB(B̄^N, g_flat) = c_N` is attained by the flat ball; in particular the boundary
conformal energies are bounded below. -/
def EscobarIV (k : CurvedMetric X N) : Prop :=
  M.YB k = cN N ∧ BddBelow (M.confEnergyB k '' {u | M.Pos u ∧ M.AdmB k.toFrameMetric u})

end MeasuredModel

namespace Filling

variable {X D Y E : Type*} [MeasurableSpace X] [AddCommGroup D] [Module ℝ D]
  [MeasurableSpace Y] [AddCommGroup E] [Module ℝ E] {N n : ℕ}
variable (F : Filling X Y E N n) (M : MeasuredModel X D N n) (gbar : GluedMetric X Y N n)

/-- **thm:yamabe (b)** (l.187) in the form used at l.658, on `Σ̄` read through its pieces: the
infimum `Y_[ḡ](Σ̄)` is attained by a smooth positive `ψ`, and `h̄ = ψ^{4/(N-2)} ḡ` has constant
scalar curvature `Y_[ḡ](Σ̄) Vol(Σ̄, h̄)^{-2/N}`. The model carries curvatures as data: that `h̄`
carries the curvatures of `ψ^{4/(N-2)} ḡ` is what the conformal law (`EscobarLaw`) sees, on `Σ` and
on each `D_j`, so it is asked at `h̄`. -/
def YamabeB : Prop :=
  ∃ S : F.YamabeData M gbar, M.EscobarLaw gbar.body S.hb.body S.ψ.u ∧
    ∀ j, (F.piece j).EscobarLaw (gbar.cap j) (S.hb.cap j) (S.ψ.w j)

end Filling

/-! ## 3. Akutagawa–Botvinnik (MR1957657) -/

namespace MeasuredModel

variable {X D : Type*} [MeasurableSpace X] [AddCommGroup D] [Module ℝ D] {N n : ℕ}
variable (M : MeasuredModel X D N n)

/-- The conclusion of Akutagawa–Botvinnik's Theorem 4.6 for a given family (l.690): metrics
`g̃_τ = gs i` (`τ → 0` along `i → ∞`) with minimal boundary, `g̃_τ → g` and `R_{g̃_τ} → R_g`
uniformly. -/
def ABFamily (g : CurvedMetric X N) (gs : ℕ → CurvedMetric X N) (η δ : ℕ → ℝ) : Prop :=
  (∀ i, 0 ≤ η i) ∧ Tendsto η atTop (𝓝 0) ∧
    (∀ i, UniformlyClose (η i) g.toFrameMetric (gs i).toFrameMetric) ∧
    Tendsto δ atTop (𝓝 0) ∧ (∀ i x, |(gs i).R x - g.R x| ≤ δ i) ∧
    ∀ i, M.MinimalBoundary (gs i)

/-- **Akutagawa–Botvinnik, Theorem 4.6** (MR1957657; l.690): a metric with minimal boundary is the
`C⁰` limit, with its scalar curvature, of metrics with minimal boundary (which moreover are
`g` outside a `τ`-collar and conformal to a product near `∂Σ`: not modelled). -/
def AB46 (g : CurvedMetric X N) : Prop :=
  M.MinimalBoundary g → ∃ (gs : ℕ → CurvedMetric X N) (η δ : ℕ → ℝ), M.ABFamily g gs η δ

/-- **Akutagawa–Botvinnik, Corollary 5.3** (MR1957657; l.641), for `Σ` whose boundary classes are
positive (automatic for `N = 3`): if `Y_C(Σ) > 0`, the double `X = Σ ∪_{∂Σ} (−Σ)` has positive
Yamabe invariant. -/
def AB53 (g : CurvedMetric X N) (Xd : ClosedConformal) : Prop := 0 < M.Y g → 0 < Xd.sigma

end MeasuredModel

/-! ## 4. Gromov–Lawson (MR569070) -/

/-- **Gromov–Lawson** (MR569070; l.645, l.465): a closed enlargeable manifold carries no metric of
positive scalar curvature (stated for the double `X ≅ Σ̄ # (−Σ̄) # (n−1)(S^{N−1} × S¹)`, enlargeable
because `Σ̄` is and enlargeability is preserved under connected sums; or for `Σ̄` itself, e.g.
`T^N`). -/
def GromovLawson (X : ClosedConformal) : Prop := ¬ X.HasPSC

/-! ## 5. The consumers -/

namespace ClosedConformal

/-- l.465: a closed manifold carrying no metric of positive scalar curvature (e.g. enlargeable,
`GromovLawson`) has `σ ≤ 0`, by thm:yamabe (b). -/
theorem sigma_nonpos (X : ClosedConformal) (hY : YamabePSC X) (hGL : GromovLawson X) :
    X.sigma ≤ 0 := by
  by_contra h
  rw [not_le] at h
  unfold sigma at h
  by_cases hb : BddAbove (Set.range X.Y)
  · rcases isEmpty_or_nonempty X.Cls with hE | hne
    · rw [Real.iSup_of_isEmpty] at h
      exact lt_irrefl _ h
    · obtain ⟨C, hC⟩ := exists_lt_of_lt_ciSup h
      exact hGL ⟨C, hY C hC⟩
  · rw [Real.iSup_of_not_bddAbove hb] at h
    exact lt_irrefl _ h

end ClosedConformal

namespace MeasuredModel

variable {X D : Type*} [MeasurableSpace X] [AddCommGroup D] [Module ℝ D] {N n : ℕ}
variable (M : MeasuredModel X D N n)

/-- prop:nonpositive, first sentence (l.478, proof l.641–645): `Y_[g](Σ) ≤ 0`, from
Akutagawa–Botvinnik Cor. 5.3, thm:yamabe (b) and Gromov–Lawson on the double. -/
theorem prop_nonpositive_first (g : CurvedMetric X N) (Xd : ClosedConformal)
    (hAB : M.AB53 g Xd) (hY : YamabePSC Xd) (hGL : GromovLawson Xd) : M.Y g ≤ 0 := by
  by_contra h
  rw [not_le] at h
  have h1 := hAB h
  have h2 := Xd.sigma_nonpos hY hGL
  linarith

/-- prop:nonpositive (l.476–479), both sentences, over the model: from the externals of the first
sentence and the Sobolev inequality (lem:kobayashi (b)): `Y_[g](Σ) ≤ 0`; and if `g` has constant
scalar curvature and minimal boundary, `R_g ≤ 0` and `EH(Σ, g) = Y_[g](Σ)`. -/
theorem prop_nonpositive (hN : 3 ≤ N) (g : CurvedMetric X N) (Xd : ClosedConformal)
    (hAB : M.AB53 g Xd) (hY : YamabePSC Xd) (hGL : GromovLawson Xd)
    [IsFiniteMeasure (M.vol g.toFrameMetric)] (hV : M.vol g.toFrameMetric ≠ 0)
    (hD : ∀ u, AEStronglyMeasurable (M.val u) (M.vol g.toFrameMetric))
    (hS : M.SobolevIneq g.toFrameMetric) :
    M.Y g ≤ 0 ∧
      (M.MinimalBoundary g → ∀ c : ℝ, (∀ x, g.R x = c) →
          (∀ x, g.R x ≤ 0) ∧ M.EH g = M.Y g) := by
  have hY0 := M.prop_nonpositive_first g Xd hAB hY hGL
  exact ⟨hY0, fun hH c hRc => M.prop_nonpositive_csc_of_sobolev hN g hV hD hH hRc hY0 hS⟩

/-- lem:kobayashi (a) with its printed left side (l.619–620): for `h = u^{4/(N-2)} g`, through
Escobar's conformal law, `EH(Σ, h) ≥ a_N ‖∇u‖²/‖u‖²_{p*} + m Vol(Σ)^{2/N}`, `m = min(0, min R_g)`. -/
theorem kobayashi_EH (hN : 3 ≤ N) (g h : CurvedMetric X N) [IsFiniteMeasure (M.vol g.toFrameMetric)]
    (hH : M.MinimalBoundary g) (u : D) (hu : AEStronglyMeasurable (M.val u) (M.vol g.toFrameMetric))
    (hadm : M.Adm g.toFrameMetric u) (hconf : M.IsConformal g.toFrameMetric h.toFrameMetric u)
    (hlaw : M.EscobarLaw g h u) :
    aN N * M.dirichlet g.toFrameMetric u / normSq (M.vol g.toFrameMetric) (pStar N) (M.val u) +
        g.kobM * (M.vol g.toFrameMetric Set.univ).toReal ^ (2 / (N : ℝ)) ≤ M.EH h := by
  have hE : M.EH h = M.confEnergy g u := by
    unfold confEnergy
    rw [← (hlaw hconf).1, mul_div_assoc, div_self (ne_of_gt hadm), mul_one]
  rw [hE]
  exact M.kobayashi_printed g hN hH u hu

/-- eq:cN (l.337–340): the flat unit ball (`R ≡ 0`, `H ≡ 1` on its boundary sphere, of area
`ω_{N-1}`) has `EHB = 2(N−1) ω_{N-1}^{1/(N-1)} = c_N`. -/
theorem EHB_flatBall (hN : 3 ≤ N) (P : MeasuredModel X D N 1) (k : CurvedMetric X N)
    (hR : ∀ᵐ x ∂(P.vol k.toFrameMetric), k.R x = 0)
    (hH : ∀ᵐ x ∂(P.bvol k.toFrameMetric 0), k.H x = 1)
    (harea : (P.bvol k.toFrameMetric 0 Set.univ).toReal = sphereArea N) :
    P.EHB k = cN N := by
  have hN' := three_le_cast hN
  have hω := sphereArea_pos (N := N) (by omega)
  have hRi : ∫ x, k.R x ∂(P.vol k.toFrameMetric) = 0 := by
    rw [integral_congr_ae hR, integral_zero]
  have hHi : ∫ x, k.H x ∂(P.bvol k.toFrameMetric 0) = sphereArea N := by
    rw [integral_congr_ae hH, integral_const, smul_eq_mul, mul_one, measureReal_def, harea]
  have hact : P.action k = 2 * ((N : ℝ) - 1) * sphereArea N := by
    unfold action
    rw [hRi, Fin.sum_univ_one, hHi, zero_add]
  have hbd : P.bdryVol k.toFrameMetric = sphereArea N := by
    unfold bdryVol
    rw [Fin.sum_univ_one, harea]
  unfold EHB cN
  rw [hact, hbd, mul_div_assoc]
  congr 1
  rw [div_eq_iff (Real.rpow_pos_of_pos hω _).ne', ← Real.rpow_add hω]
  have h1 : (N : ℝ) - 1 ≠ 0 := by linarith
  have e : 1 / ((N : ℝ) - 1) + ((N : ℝ) - 2) / ((N : ℝ) - 1) = 1 := by field_simp; ring
  rw [e, Real.rpow_one]

end MeasuredModel

namespace Filling

variable {X D Y E : Type*} [MeasurableSpace X] [AddCommGroup D] [Module ℝ D]
  [MeasurableSpace Y] [AddCommGroup E] [Module ℝ E] {N n : ℕ}
variable {F : Filling X Y E N n} {M : MeasuredModel X D N n} {gbar : GluedMetric X Y N n}

/-- Fact (iv) at l.724: if each `ḡ|_{D_j}` is in the class of the flat ball (`EscobarIV`), the
Yamabe metric `h̄` of thm:yamabe (b) has `EHB(D_j, h̄|_{D_j}) ≥ c_N`, by the conformal law on `D_j`
and the definition of the boundary Yamabe constant (l.663). -/
theorem YamabeData.boundaryYamabe (S : F.YamabeData M gbar)
    (hIV : ∀ j, (F.piece j).EscobarIV (gbar.cap j))
    (hlawCap : ∀ j, (F.piece j).EscobarLaw (gbar.cap j) (S.hb.cap j) (S.ψ.w j)) :
    F.BoundaryYamabe S.hb (fun _ => cN N) := by
  intro j
  have h := MeasuredModel.YB_le_EHB (S.adm.2.1 j) (S.capAdmB j) (hlawCap j (S.confCap j)).2
    (hIV j).2
  rw [(hIV j).1] at h
  exact h

/-- The inputs of lem:gluing-estimate with `β_j = c_N` (l.724), assembled from the externals:
thm:yamabe (b) (`YamabeData`), `Y_[ḡ](Σ̄) ≤ 0` (from `σ(Σ̄) ≤ 0`), Escobar's fact (iv) on the
caps, and the conformal law on `Σ` and on the caps. -/
def YamabeData.gluingInput (S : F.YamabeData M gbar) (hy : F.Ybar M gbar ≤ 0)
    (hIV : ∀ j, (F.piece j).EscobarIV (gbar.cap j))
    (hlaw : M.EscobarLaw gbar.body S.hb.body S.ψ.u)
    (hlawCap : ∀ j, (F.piece j).EscobarLaw (gbar.cap j) (S.hb.cap j) (S.ψ.w j)) :
    GluingInput M Y E gbar.body (fun _ => cN N) where
  F := F
  hb := S.hb
  u := S.ψ.u
  y := F.Ybar M gbar
  c := S.c
  conf := S.conf
  val_meas := S.val_meas
  tr_meas := S.tr_meas
  tr_eq := S.tr_eq
  vol_finite := S.vol_finite
  bvol_finite := S.bvol_finite
  y_nonpos := hy
  yamabe := S.yamabe
  law := (hlaw S.conf).1
  bdryYamabe := S.boundaryYamabe hIV hlawCap
  flip := S.flip
  bmatch := S.bmatch

/-- thm:yamabe (b), `σ(Σ̄) ≤ 0` and fact (iv) give the inputs of lem:gluing-estimate with
`β_j = c_N` (l.724). -/
theorem nonempty_gluingInput (hyam : F.YamabeB M gbar) (hy : F.Ybar M gbar ≤ 0)
    (hIV : ∀ j, (F.piece j).EscobarIV (gbar.cap j)) :
    Nonempty (GluingInput M Y E gbar.body (fun _ => cN N)) := by
  obtain ⟨S, hlaw, hlawCap⟩ := hyam
  exact ⟨S.gluingInput hy hIV hlaw hlawCap⟩

/-- lem:gluing-estimate (l.648–656), with thm:yamabe (b) supplying `h̄` (l.658) and
`β_j := YB_[g_j](D_j) > -∞` (bounded-below boundary energies on each `D_j`): on `(Σ̄, ḡ)` with
`Y_[ḡ](Σ̄) ≤ 0` and `H_g ≡ 0`, there is `u > 0` (and the Yamabe metric `h̄`) with
`m Vol(Σ, g)^{2/N} ≤ -F^{(β)}_g(u) + Y_[ḡ](Σ̄) (Vol(Σ̄, h̄)/Vol(Σ, h̄))^{(N-2)/N}`, the last term
non-positive. -/
theorem lem_gluing_estimate_of_yamabe (hN : 3 ≤ N) [IsFiniteMeasure (M.vol gbar.body.toFrameMetric)]
    (hV : M.vol gbar.body.toFrameMetric ≠ 0) (hB : ∀ j, M.bvol gbar.body.toFrameMetric j ≠ 0)
    (hρ : M.DensityMeasurable gbar.body.toFrameMetric) (hH : M.MinimalBoundary gbar.body)
    (hyam : F.YamabeB M gbar) (hy : F.Ybar M gbar ≤ 0)
    (hbdd : ∀ j, BddBelow ((F.piece j).confEnergyB (gbar.cap j) ''
      {v | (F.piece j).Pos v ∧ (F.piece j).AdmB (gbar.cap j).toFrameMetric v})) :
    ∃ (u : D) (hb : GluedMetric X Y N n), M.Pos u ∧
      gbar.body.kobM * (M.vol gbar.body.toFrameMetric Set.univ).toReal ^ (2 / (N : ℝ)) ≤
          -M.F gbar.body.toFrameMetric (fun j => (F.piece j).YB (gbar.cap j)) u +
            F.Ybar M gbar * (F.volBar M hb / (M.vol hb.body.toFrameMetric Set.univ).toReal) ^
              (((N : ℝ) - 2) / N) ∧
        F.Ybar M gbar * (F.volBar M hb / (M.vol hb.body.toFrameMetric Set.univ).toReal) ^
            (((N : ℝ) - 2) / N) ≤ 0 := by
  obtain ⟨S, hlaw, hlawCap⟩ := hyam
  haveI := S.vol_finite
  haveI := S.bvol_finite
  exact ⟨S.ψ.u, S.hb, S.conf.1,
    gluing_estimate_YB hN F M gbar.body hV hB hρ hH S.hb S.ψ.u S.conf S.val_meas S.tr_meas
      S.tr_eq hy S.yamabe (hlaw S.conf).1 gbar.cap S.ψ.w S.adm.2.1 S.capAdmB
      (fun j => (hlawCap j (S.confCap j)).2) hbdd S.flip S.bmatch⟩

end Filling

namespace MeasuredModel

variable {X D Y E : Type*} [MeasurableSpace X] [AddCommGroup D] [Module ℝ D]
  [MeasurableSpace Y] [AddCommGroup E] [Module ℝ E] {N n : ℕ}
variable (M : MeasuredModel X D N n)

/-- thm:upper-bound and cor:negative (l.493–505, proof l.723–729) from the externals: the family
`g̃_τ` of Akutagawa–Botvinnik (`ABFamily`), the fillings `ḡ_τ` of lem:gluing (carried) whose caps
are in the class of the flat ball (Escobar's fact (iv)), thm:yamabe (b) on each `(Σ̄, ḡ_τ)`
(with the conformal law at its `h̄`), `Y_[ḡ_τ](Σ̄) ≤ 0` (from `σ(Σ̄) ≤ 0`); and lem:positivity from
the model's analytic properties. Conclusion: `inf F_g > 0`, `Y_[g](Σ) = R_g Vol^{2/N} ≤ -inf F_g`,
`Y_[g](Σ) < 0`, `R_g < 0`, not scalar flat. -/
theorem cor_negative_of_externals (hN : 3 ≤ N) (g : CurvedMetric X N)
    [IsFiniteMeasure (M.vol g.toFrameMetric)] [∀ j, IsFiniteMeasure (M.bvol g.toFrameMetric j)]
    (hV0 : M.vol g.toFrameMetric ≠ 0) (hB0 : ∃ j, M.bvol g.toFrameMetric j ≠ 0)
    (hD : ∀ u, AEStronglyMeasurable (M.val u) (M.vol g.toFrameMetric))
    (hS : M.SobolevIneq g.toFrameMetric) (hT : M.TraceIneq g.toFrameMetric)
    (hRel : M.RellichProp g.toFrameMetric) (hC : M.ConstLimit g.toFrameMetric)
    (hH : M.MinimalBoundary g) {c : ℝ} (hRc : ∀ x, g.R x = c)
    (F : ℕ → Filling X Y E N n) (gbar : ℕ → GluedMetric X Y N n) (η δ : ℕ → ℝ)
    (hfam : M.ABFamily g (fun i => (gbar i).body) η δ)
    (hfin : ∀ i, IsFiniteMeasure (M.vol (gbar i).body.toFrameMetric))
    (hV : ∀ i, M.vol (gbar i).body.toFrameMetric ≠ 0)
    (hB : ∀ i j, M.bvol (gbar i).body.toFrameMetric j ≠ 0)
    (hρ : ∀ i, M.DensityMeasurable (gbar i).body.toFrameMetric)
    (hIV : ∀ i j, ((F i).piece j).EscobarIV ((gbar i).cap j))
    (hyam : ∀ i, (F i).YamabeB M (gbar i)) (hy : ∀ i, (F i).Ybar M (gbar i) ≤ 0) :
    0 < M.infF g.toFrameMetric (fun _ => cN N) ∧
      M.Y g = c * (M.vol g.toFrameMetric Set.univ).toReal ^ (2 / (N : ℝ)) ∧
      M.Y g ≤ -M.infF g.toFrameMetric (fun _ => cN N) ∧
      M.Y g < 0 ∧ c < 0 ∧ ¬ ∀ x, g.R x = 0 := by
  obtain ⟨hη, hηt, hclose, hδt, hR, hHτ⟩ := hfam
  have S : ∀ i, GluingInput M Y E (gbar i).body (fun _ => cN N) := fun i =>
    ((F i).nonempty_gluingInput (hyam i) (hy i) (hIV i)).some
  obtain ⟨-, hYc, hub⟩ := M.upper_bound_of_gluings_of_pos hN g hD hH hRc
    (M.lem_positivity g.toFrameMetric hN hV0 hB0 hD hS hT hRel hC)
    (fun i => (gbar i).body) η δ hη hηt hclose hδt hR hfin hV hB hρ hHτ S
  obtain ⟨hpos, hYneg, hcneg, -, hflat⟩ := M.cor_negative_of_analytic hN g hV0 hB0 hD hS hT hRel
    hC hH hRc (fun i => (gbar i).body) η δ hη hηt hclose hδt hR hfin hV hB hρ hHτ S
  exact ⟨hpos, hYc, hub, hYneg, hcneg, hflat⟩

end MeasuredModel

end Yamabe
