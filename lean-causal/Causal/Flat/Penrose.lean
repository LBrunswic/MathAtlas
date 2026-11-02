import CausalScaffold.Flat.Form
import Causal.CauchyExtension

/-!
# `CausalScaffold.Flat.Penrose` — the Penrose boundary `𝒥^±` and the regular convex domains

T. Barbot, *Globally hyperbolic flat space-times* (`papers/barbot`, arXiv math/0402257), §4.1–4.2
(`GHFspace.tex` l.762–1040). Labels certified (line in `papers/barbot/legacy/labeled/GHFspace.tex`):

* **`bdef:regular_domain`** — `GHFspace.tex:914` (`FutureRegular`, `PastRegular`)
* **`blem:fermons`** — `GHFspace.tex:927` (`interior_omegaPlus_subset`, `interior_omegaMinus_subset`)
* **`bcor:closeregular`** — `GHFspace.tex:951` (`FutureRegular.closure_futureRegular`)
* **`blem:closecool`** — `GHFspace.tex:963` (`isOpen_omegaPlus_of_isClosed`)
* **`blem:fermonsbis`** — `GHFspace.tex:987` (`omegaPlus_closure_eq_interior`, no hypothesis)

Partial, unmarked (see SCOPE): `bdef:omega_lambda` (`GHFspace.tex:893`; its closing sentence is
false for non-closed `Λ`), `bprop:regular_iff_bounded` (`GHFspace.tex:1008`; **sign error**, the
corrected form is proved), `bcor:futetpast` (`GHFspace.tex:1036`; proved for closed `Λ`, false
otherwise), `bprop:laoucapulse` (`GHFspace.tex:855`; the chordal identity and one direction on
`𝒮` proved, the metric reading on `𝒥⁺` refuted for `d = 2`).
Prose items: [4.J] `𝒥 ≅ 𝒮 × ℝ` and the action of `Isom(𝐌ⁿ)` (l.773–849); the observations
after Def 4.4 (l.905–911). Not in the paper: regular domains are globally hyperbolic in ETT's sense.

> If $v = \delta^{+}(P)$ and $s = \nu^{+}(P)$, $P^{+}$ (resp. $P^{-}$) is the domain of points $p$
> in $\mathbf{M}^n$ for which $\langle v \mid p \rangle - s$ is negative (resp. positive). (l.887–890)

> $\Omega^{+}(\Lambda) = \bigcap_{P \in \Lambda} P^{+}$ (resp. $\Omega^{-}(\Lambda) = \bigcap_{P \in
> \Lambda} P^{-}$). If $\Lambda$ contains at least $2$ elements, then $\Omega^{\pm}(\Lambda)$, if
> nonempty, is regular. (l.897–902)

> If $\Omega^{+}(\Lambda)$ (resp. $\Omega^{-}(\Lambda)$) is nonempty and open, then it is called a
> future (resp. past) regular convex domain. (l.915–918)

> If $\overline{\Lambda}$ is the closure in ${\mathcal J}$ of $\Lambda$, then
> $\Omega^{\pm}(\overline{\Lambda})$ contains the interior of $\Omega^{\pm}(\Lambda)$. (l.929–931)

> If $\Lambda$ is future regular, then its closure $\overline{\Lambda}$ is future regular too, and
> $\Omega^{+}(\Lambda) = \Omega^{+}(\overline{\Lambda})$. (l.953–954)

> If $\Lambda$ is closed, then $\Omega^{+}(\Lambda)$ is open (maybe empty). (l.965–966)

> Let $\Lambda$ be a subset of ${\mathcal J}$ with future regular closure. Then,
> $\Omega^{+}(\overline{\Lambda})$ is the interior of $\Omega^{+}(\Lambda)$. (l.989–991)

> A closed subset of ${\mathcal J}$ is future regular (resp. past regular) if and only if there is
> some real number $C$ such that, for every $(v,s)$ in $\Lambda$, the second component $s$ is less
> than $C$ (resp. bigger than $C$). (l.1009–1013)

> $\Lambda$ is future regular and past regular if and only if it is compact. (l.1038–1039)

> Let $g$ be a linear isometry of $\mathbf{M}^n$ […]. Then, the domain in ${\mathcal J}^{+}$ where
> the action of $g$ is expanding is precisely the preimage under $\delta^{+}$ of the domain of
> ${\mathcal S}^{+}$ where the action of $L(g)$ is expanding. (l.859–865)

**Dimension (kb/0024).** Barbot's `𝐌ⁿ` has total dimension `n`; `Minkowski d` has `d` spatial
dimensions, so Barbot's `n` is `d + 1`, and `𝒮 ≅ S^{n−2} = S^{d−1}`.

**Parametrisation.** `𝒮` is `PenroseSphere d`, the unit sphere of `EuclideanSpace ℝ (Fin d)`;
`u ∈ 𝒮` gives the future null vector `nullVec u = (1, u)` (normalised by its time component).
Barbot's `v ∈ 𝒮⁺` (Euclidean norm `N(v) = 1`) is `nullVec u / √2`, and his `s` is ours over `√2`:
`(u, s) ↦ (nullVec u/√2, s/√2)` is a homeomorphism `𝒮 × ℝ ≅ 𝒮⁺ × ℝ` fixing every half-space, so
closures, compactness and the side on which `s` is bounded are unchanged. `Λ ⊆ 𝒮 × ℝ` is read
through `δ⁺ × ν⁺` for both `Ω⁺` and `Ω⁻`, as at l.887. **Finding (normalisation slip, l.782–783,
l.785–789):** on `N(v) = 1`, `|v| = 0` one has `x₀² = Σ xᵢ² = 1/2`, so "necessarily `x₀ = 1/2`"
should read `x₀ = 1/√2`, and the induced metric is the round metric of the sphere of radius
`1/√2`, not of the unit sphere; nothing downstream depends on the radius.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `Λ` nonempty (l.882) | ⚠ weakened: not used, except for `Ω⁺ ∩ Ω⁻ = ∅` (✓ carried) |
| 4.9: `cl Λ` future regular | ⚠ weakened: not used (`omegaPlus_closure_eq_interior`) |
| 4.10: `Λ` closed | ✓ carried; ⚠ weakened for "nonempty ⇔ bounded" (`omegaPlus_nonempty_iff`) |
| 4.11: `Λ` closed (standing convention, l.1001–1009) | ✓ carried as a hypothesis; ⚠ weakened for compact ⇒ regular |
| 4.8: compactness of `𝒮` | ✓ used (a compact slab of `𝒮 × ℝ`) |
| 4.10: compactness of `𝒮` | ⚠ weakened: Cauchy–Schwarz suffices |
| global hyperbolicity (not in the paper) | causally convex open `W`; convexity of `Ω` not used |

## SCOPE (disclosed)

* **`bprop:regular_iff_bounded` has a sign error** (l.1011–1013 against the proof l.1017–1031):
  with `P⁺ = {⟨v|p⟩ < s}` (l.887–890) a closed `Λ` is future regular iff `s` is bounded **below**
  (`futureRegular_iff_exists_lt`), past regular iff bounded **above** (`pastRegular_iff_exists_gt`).
  The printed form is the `Prop` `RegularIffBoundedAsPrinted`, refuted for `d ≥ 1`
  (`not_regularIffBoundedAsPrinted`, `Λ = 𝒮 × [0, ∞)`). For `d = 0`, `𝒮 = ∅`.
* **`bdef:omega_lambda`, l.901–902**, under Def 4.5: false for `Λ = {u₀} × ]0, ∞[`, whose
  `Ω⁺ = {⟨v|p⟩ ≤ 0}` is nonempty and not open (`not_futureRegular_ray`); true for every closed
  `Λ`, with one element or more. The definitions and the observations l.907–911 are proved
  (`convex_omegaPlus`, `Jplus_omegaPlus_subset`, `add_smul_mem_omegaPlus`,
  `disjoint_omegaPlus_omegaMinus`, and the `Ω⁻` forms). "Geodesically complete in the future" is
  read as `J⁺(Ω⁺) ⊆ Ω⁺`, and in its ray form.
* `bcor:futetpast` (partial) is proved for closed `Λ` (`futureRegular_and_pastRegular_iff_isCompact`);
  `Λ = {u₀} × ([0,1] ∖ {1/2})` is future and past regular and not compact
  (`futureRegular_pastRegular_not_isCompact`). Unmarked, because the closedness is a reading of
  l.1001–1009, not printed in the corollary.
* `bprop:laoucapulse` (partial): "expanding" is undefined in the paper. Proved: the action of `SO₀(1,d)`
  on `𝒮` multiplies chordal distances by `(a(u)a(u'))^{1/2}`, `a = 1/c` the common factor of
  l.849–851 (`norm_lorentzSphere_sub_sq`), and `[L(g)]` is metrically expanding where `a > 1`
  (`isExpandingAt_lorentzSphere`). The claim on `𝒥⁺` in the metric reading is the `Prop`
  `LaoucapulseMetricReading`, **refuted for `d = 2`** (Barbot's `n = 3`) by
  `not_laoucapulseMetricReading_two`: the boost `Laoucapulse.boostIsom` (`cosh = 5/4`,
  `sinh = 3/4`) has `a = 5/4 > 1` at `u₀ = (−3/5, 4/5)`, so `[L(g)]` is expanding at `u₀`, and
  `g` is not expanding
  at `(u₀, 4) ∈ 𝒥⁺`: along a curve on which the image `s`-components agree, the image distance is
  at most the distance. The mechanism: the `s`-component `a(g,u)s` has `u`-derivative `s·∂a`, so
  off `s = 0` the differential is not conformal, and for large `|s|` it contracts a direction even
  where `a > 1`; the statement holds for volume expansion, not for metric expansion. The Lean
  metric is the sup product of the chordal metric and `|·|`; the counterexample transfers (not
  formalized) to Barbot's Riemannian product of the round metric and any `λ|·|`, because the two
  image points have equal `s`-component (so every product metric gives the sphere distance), every
  product metric dominates `|Δs|`, chordal and geodesic distances agree to first order, and `λ` is
  absorbed by choosing `s` larger; as `t → 0` the margin is a factor `5.76` in the squared
  distances (`36 t²` against `6.25 t²`).
* [4.J]: lightlike hyperplanes are `IsLightlikeHyperplane` (`{⟨w|·⟩ = c}`, `w ≠ 0` null); `δ⁺×ν⁺` is
  onto (`IsLightlikeHyperplane.exists_eq`) and one-to-one (`lightHyperplane_injective`);
  `frontier (P⁺) = frontier (P⁻) = P` (`frontier_halfPlus`, `frontier_halfMinus`). The action `isomPenrose` is l.834–844 in this
  normalisation; it is shown to carry `P`, `P^±`, `Ω^±` (`isom_preimage_*`), not to be a group
  action. `𝒥⁻` and the `𝒮⁻` parametrisation (l.789–791, l.846–848) are not formalized.
* Past forms of 4.6–4.9 come from the point reflection `p ↦ −p` (`omegaMinus_eq_neg`); the
  paper's "evidently valid" (l.1004).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Barbot campaign,
WP-30c (DEC-34), wave 1.
-/

namespace Causal.Flat

open Set TopologicalSpace Topology Filter Metric

variable {d : ℕ}

/-! ### The sphere `𝒮` and the null vectors -/

/-- The parameter space `𝒮` of the linear lightlike hyperplanes: the unit sphere of the spatial
factor `EuclideanSpace ℝ (Fin d)`. -/
abbrev PenroseSphere (d : ℕ) : Type := Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1

/-- The future null vector `(1, u)` of the direction `u ∈ 𝒮`. -/
def nullVec (u : PenroseSphere d) : Minkowski d := (1, (u : EuclideanSpace ℝ (Fin d)))

theorem norm_penroseSphere (u : PenroseSphere d) : ‖(u : EuclideanSpace ℝ (Fin d))‖ = 1 :=
  norm_eq_of_mem_sphere u

theorem minkB_nullVec (u : PenroseSphere d) (p : Minkowski d) :
    minkB (nullVec u) p = -p.1 + inner ℝ (u : EuclideanSpace ℝ (Fin d)) p.2 := by
  simp [minkB, nullVec]

theorem minkQ_nullVec (u : PenroseSphere d) : minkQ (nullVec u) = 0 := by
  simp [minkQ, nullVec]

theorem isFutureCausal_nullVec (u : PenroseSphere d) : IsFutureCausal (nullVec u) :=
  ⟨zero_le_one, (minkQ_nullVec u).le⟩

theorem nullVec_ne_zero (u : PenroseSphere d) : nullVec u ≠ 0 := fun h => by
  have := congrArg Prod.fst h; simp [nullVec] at this

/-! ### Bilinear algebra of `minkB`

The six `private` lemmas below (`minkB_add_right`, `minkB_sub_right`, `minkB_neg_right`,
`minkB_smul_right`, `minkB_smul_left`, `minkQ_add`) are stated also, publicly and in other argument
orders, by the wave-1 sibling `CausalScaffold.Flat.Isometries`; they are private here so that both
modules can be imported together (a public copy would make any common importer fail with
"environment already contains"). `Isometries` is not imported because it is not built in this
wave; at graduation one copy moves into `Form` and the other is dropped. -/

private theorem minkB_add_right (v p q : Minkowski d) : minkB v (p + q) = minkB v p + minkB v q := by
  simp only [minkB, Prod.fst_add, Prod.snd_add, inner_add_right]; ring

private theorem minkB_sub_right (v p q : Minkowski d) : minkB v (p - q) = minkB v p - minkB v q := by
  simp only [minkB, Prod.fst_sub, Prod.snd_sub, inner_sub_right]; ring

private theorem minkB_neg_right (v p : Minkowski d) : minkB v (-p) = -minkB v p := by
  simp only [minkB, Prod.fst_neg, Prod.snd_neg, inner_neg_right]; ring

private theorem minkB_smul_right (v p : Minkowski d) (c : ℝ) : minkB v (c • p) = c * minkB v p := by
  simp only [minkB, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, real_inner_smul_right]; ring

private theorem minkB_smul_left (v p : Minkowski d) (c : ℝ) : minkB (c • v) p = c * minkB v p := by
  rw [minkB_comm, minkB_smul_right, minkB_comm]

theorem isLinearMap_minkB (v : Minkowski d) : IsLinearMap ℝ (minkB v) :=
  ⟨minkB_add_right v, fun c p => minkB_smul_right v p c⟩

private theorem minkQ_add (v w : Minkowski d) : minkQ (v + w) = minkQ v + 2 * minkB v w + minkQ w := by
  simp only [minkQ, minkB, Prod.fst_add, Prod.snd_add, norm_add_sq_real]; ring

/-- **Polarisation**: a Lorentz transformation preserves `minkB`. -/
theorem lorentz.minkB_apply {A : Minkowski d ≃ₗ[ℝ] Minkowski d} (hA : A ∈ lorentz d)
    (v w : Minkowski d) : minkB (A v) (A w) = minkB v w := by
  have h := minkQ_add (A v) (A w)
  rw [← map_add, lorentz.minkQ_apply hA, lorentz.minkQ_apply hA, lorentz.minkQ_apply hA,
    minkQ_add] at h
  linarith

/-- `|⟨(1,u) | p⟩| ≤ |p₀| + ‖p₁‖`. -/
theorem abs_minkB_nullVec_le (u : PenroseSphere d) (p : Minkowski d) :
    |minkB (nullVec u) p| ≤ |p.1| + ‖p.2‖ := by
  rw [minkB_nullVec]
  have h := abs_real_inner_le_norm (u : EuclideanSpace ℝ (Fin d)) p.2
  rw [norm_penroseSphere, one_mul] at h
  calc |-p.1 + inner ℝ (u : EuclideanSpace ℝ (Fin d)) p.2|
      ≤ |-p.1| + |inner ℝ (u : EuclideanSpace ℝ (Fin d)) p.2| := abs_add_le _ _
    _ ≤ |p.1| + ‖p.2‖ := by rw [abs_neg]; linarith

theorem abs_minkB_nullVec_le_two_mul_norm (u : PenroseSphere d) (p : Minkowski d) :
    |minkB (nullVec u) p| ≤ 2 * ‖p‖ := by
  have h1 : |p.1| ≤ ‖p‖ := by simpa using norm_fst_le p
  have h2 : ‖p.2‖ ≤ ‖p‖ := norm_snd_le p
  linarith [abs_minkB_nullVec_le u p]

/-- Along a causal relation, `⟨(1,u) | ·⟩` does not increase. -/
theorem minkB_nullVec_le_of_le {p q : Minkowski d} (u : PenroseSphere d)
    (h : (minkowski d).le ⊤ p q) : minkB (nullVec u) q ≤ minkB (nullVec u) p := by
  have hd := minkowski_le_top_iff.1 h
  have hi := abs_real_inner_le_norm (u : EuclideanSpace ℝ (Fin d)) (q.2 - p.2)
  rw [norm_penroseSphere, one_mul] at hi
  have := minkB_sub_right (nullVec u) q p
  rw [minkB_nullVec (p := q - p)] at this
  simp only [Prod.fst_sub, Prod.snd_sub] at this
  linarith [le_abs_self (inner ℝ (u : EuclideanSpace ℝ (Fin d)) (q.2 - p.2))]

theorem continuous_minkB_nullVec (u : PenroseSphere d) :
    Continuous fun p : Minkowski d => minkB (nullVec u) p := by
  simp only [minkB_nullVec]; fun_prop

/-- `(u, s) ↦ ⟨(1,u) | p⟩` is continuous on `𝒮 × ℝ`, for a fixed point `p`. -/
theorem continuous_minkB_nullVec_param (p : Minkowski d) :
    Continuous fun w : PenroseSphere d × ℝ => minkB (nullVec w.1) p := by
  simp only [minkB_nullVec]; fun_prop

/-! ### [4.J] Lightlike hyperplanes and the half-spaces `P^±` -/

/-- The lightlike affine hyperplane `{p | ⟨(1,u) | p⟩ = s}`. -/
def lightHyperplane (u : PenroseSphere d) (s : ℝ) : Set (Minkowski d) :=
  {p | minkB (nullVec u) p = s}

/-- Barbot's `P⁺` (l.887–890): `{p | ⟨v | p⟩ − s < 0}`, the future of the hyperplane. -/
def halfPlus (u : PenroseSphere d) (s : ℝ) : Set (Minkowski d) :=
  {p | minkB (nullVec u) p - s < 0}

/-- Barbot's `P⁻` (l.887–890): `{p | ⟨v | p⟩ − s > 0}`, the past of the hyperplane. -/
def halfMinus (u : PenroseSphere d) (s : ℝ) : Set (Minkowski d) :=
  {p | 0 < minkB (nullVec u) p - s}

theorem mem_halfPlus {u : PenroseSphere d} {s : ℝ} {p : Minkowski d} :
    p ∈ halfPlus u s ↔ minkB (nullVec u) p < s := by
  rw [halfPlus, mem_setOf_eq, sub_neg]

theorem mem_halfMinus {u : PenroseSphere d} {s : ℝ} {p : Minkowski d} :
    p ∈ halfMinus u s ↔ s < minkB (nullVec u) p := by
  rw [halfMinus, mem_setOf_eq, sub_pos]

/-- A **lightlike affine hyperplane**: `{p | ⟨w | p⟩ = c}` for a nonzero null `w`. (Every affine
hyperplane is `{⟨w | ·⟩ = c}` for some `w ≠ 0`, by nondegeneracy; its direction `w^⊥` is
degenerate exactly when `w` is null.) -/
def IsLightlikeHyperplane (H : Set (Minkowski d)) : Prop :=
  ∃ w : Minkowski d, w ≠ 0 ∧ minkQ w = 0 ∧ ∃ c : ℝ, H = {p | minkB w p = c}

theorem isLightlikeHyperplane_lightHyperplane (u : PenroseSphere d) (s : ℝ) :
    IsLightlikeHyperplane (lightHyperplane u s) :=
  ⟨nullVec u, nullVec_ne_zero u, minkQ_nullVec u, s, rfl⟩

/-- **`δ⁺ × ν⁺` is onto** (l.809–814): every lightlike affine hyperplane is some
`lightHyperplane u s`. -/
theorem IsLightlikeHyperplane.exists_eq {H : Set (Minkowski d)} (hH : IsLightlikeHyperplane H) :
    ∃ u : PenroseSphere d, ∃ s : ℝ, H = lightHyperplane u s := by
  obtain ⟨w, hw0, hwq, c, rfl⟩ := hH
  have hσ : w.1 ≠ 0 := fun h => hw0 (eq_zero_of_fst_eq_zero h hwq.le)
  have hn : ‖w.2‖ = |w.1| := by
    have h2 : ‖w.2‖ ^ 2 = |w.1| ^ 2 := by
      rw [sq_abs]; unfold minkQ at hwq; linarith
    exact (sq_eq_sq₀ (norm_nonneg _) (abs_nonneg _)).1 h2
  have hu : (w.1)⁻¹ • w.2 ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_smul, hn, norm_inv, Real.norm_eq_abs,
      inv_mul_cancel₀ (abs_ne_zero.2 hσ)]
  refine ⟨⟨_, hu⟩, c / w.1, ?_⟩
  have hw : w = w.1 • nullVec ⟨_, hu⟩ := by
    refine Prod.ext ?_ ?_
    · simp [nullVec]
    · simp [nullVec, smul_smul, mul_inv_cancel₀ hσ]
  ext p
  simp only [lightHyperplane, mem_setOf_eq]
  conv_lhs => rw [hw, minkB_smul_left]
  constructor
  · intro h; rw [← h]; field_simp
  · intro h; rw [h]; field_simp

/-- **`δ⁺ × ν⁺` is one-to-one** (l.813–814). -/
theorem lightHyperplane_injective {u u' : PenroseSphere d} {s s' : ℝ}
    (h : lightHyperplane u s = lightHyperplane u' s') : u = u' ∧ s = s' := by
  have mem : ∀ p, minkB (nullVec u) p = s → minkB (nullVec u') p = s' := fun p hp => by
    have : p ∈ lightHyperplane u' s' := h ▸ hp
    exact this
  have hs : s = s' := by
    have := mem (-s, 0) (by simp [minkB_nullVec])
    simpa [minkB_nullVec] using this
  subst hs
  have h1 := mem (1 - s, (u : EuclideanSpace ℝ (Fin d)))
    (by rw [minkB_nullVec, real_inner_self_eq_norm_sq, norm_penroseSphere]; ring)
  rw [minkB_nullVec] at h1
  have hi : inner ℝ (u' : EuclideanSpace ℝ (Fin d)) u = 1 := by simp only at h1; linarith
  refine ⟨Subtype.ext ?_, rfl⟩
  have := norm_sub_sq_real (u : EuclideanSpace ℝ (Fin d)) u'
  rw [norm_penroseSphere, norm_penroseSphere, real_inner_comm, hi] at this
  have h0 : ‖(u : EuclideanSpace ℝ (Fin d)) - u'‖ = 0 := by
    have : ‖(u : EuclideanSpace ℝ (Fin d)) - u'‖ ^ 2 = 0 := by linarith
    exact pow_eq_zero_iff two_ne_zero |>.1 this
  exact sub_eq_zero.1 (norm_eq_zero.1 h0)

theorem isOpen_halfPlus (u : PenroseSphere d) (s : ℝ) : IsOpen (halfPlus u s) :=
  isOpen_lt ((continuous_minkB_nullVec u).sub continuous_const) continuous_const

theorem isOpen_halfMinus (u : PenroseSphere d) (s : ℝ) : IsOpen (halfMinus u s) :=
  isOpen_lt continuous_const ((continuous_minkB_nullVec u).sub continuous_const)

theorem convex_halfPlus (u : PenroseSphere d) (s : ℝ) : Convex ℝ (halfPlus u s) := by
  have : halfPlus u s = {p | minkB (nullVec u) p < s} := by ext; exact mem_halfPlus
  rw [this]; exact convex_halfSpace_lt (isLinearMap_minkB _) s

theorem convex_halfMinus (u : PenroseSphere d) (s : ℝ) : Convex ℝ (halfMinus u s) := by
  have : halfMinus u s = {p | s < minkB (nullVec u) p} := by ext; exact mem_halfMinus
  rw [this]; exact convex_halfSpace_gt (isLinearMap_minkB _) s

/-- **`P⁺` is future complete**: `J⁺(P⁺) ⊆ P⁺` in `minkowski d`. -/
theorem Jplus_halfPlus_subset (u : PenroseSphere d) (s : ℝ) :
    (minkowski d).Jplus ⊤ (halfPlus u s) ⊆ halfPlus u s := by
  rintro q ⟨p, hp, hpq⟩
  exact mem_halfPlus.2 ((minkB_nullVec_le_of_le u hpq).trans_lt (mem_halfPlus.1 hp))

/-- **`P⁻` is past complete**: `J⁻(P⁻) ⊆ P⁻`. -/
theorem Jminus_halfMinus_subset (u : PenroseSphere d) (s : ℝ) :
    (minkowski d).Jminus ⊤ (halfMinus u s) ⊆ halfMinus u s := by
  rintro p ⟨q, hq, hpq⟩
  exact mem_halfMinus.2 ((mem_halfMinus.1 hq).trans_le (minkB_nullVec_le_of_le u hpq))

/-- Pushing a point by `−t` in time raises `⟨(1,u) | ·⟩` by `t`, whatever `u`. -/
theorem minkB_nullVec_sub_time (u : PenroseSphere d) (p : Minkowski d) (t : ℝ) :
    minkB (nullVec u) (p - ((t, 0) : Minkowski d)) = minkB (nullVec u) p + t := by
  rw [minkB_sub_right, minkB_nullVec (p := ((t, 0) : Minkowski d))]; simp

theorem tendsto_sub_time (p : Minkowski d) :
    Tendsto (fun t : ℝ => p - ((t, 0) : Minkowski d)) (𝓝 0) (𝓝 p) := by
  have hc : Continuous fun t : ℝ => p - ((t, 0) : Minkowski d) := by fun_prop
  simpa [Prod.mk_zero_zero] using hc.tendsto 0

/-- **The boundary of `P⁺` is the lightlike hyperplane** (l.885–886). -/
theorem frontier_halfPlus (u : PenroseSphere d) (s : ℝ) :
    frontier (halfPlus u s) = lightHyperplane u s := by
  have hcl : IsClosed {p : Minkowski d | minkB (nullVec u) p ≤ s} :=
    isClosed_le (continuous_minkB_nullVec u) continuous_const
  ext p
  rw [frontier, (isOpen_halfPlus u s).interior_eq, Set.mem_sdiff]
  constructor
  · rintro ⟨hc, hn⟩
    have h1 : minkB (nullVec u) p ≤ s :=
      closure_minimal (fun x hx => (mem_halfPlus.1 hx).le) hcl hc
    exact le_antisymm h1 (not_lt.1 fun h => hn (mem_halfPlus.2 h))
  · intro hp
    refine ⟨?_, fun h => (mem_halfPlus.1 h).ne hp⟩
    -- `p + (t, 0)`, `t > 0`, lies in `P⁺` and tends to `p`.
    have hc : Continuous fun t : ℝ => p - ((-t, 0) : Minkowski d) := by fun_prop
    have ht : Tendsto (fun t : ℝ => p - ((-t, 0) : Minkowski d)) (𝓝[>] 0) (𝓝 p) := by
      have := hc.tendsto 0
      simp only [neg_zero, Prod.mk_zero_zero, sub_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    refine mem_closure_of_tendsto ht ?_
    filter_upwards [self_mem_nhdsWithin] with t (htp : 0 < t)
    rw [mem_halfPlus, minkB_nullVec_sub_time]
    simp only [lightHyperplane, mem_setOf_eq] at hp
    linarith

/-- **The boundary of `P⁻` is the lightlike hyperplane** too (l.885–886: "admitting both `P` as
boundaries"). -/
theorem frontier_halfMinus (u : PenroseSphere d) (s : ℝ) :
    frontier (halfMinus u s) = lightHyperplane u s := by
  have hcl : IsClosed {p : Minkowski d | s ≤ minkB (nullVec u) p} :=
    isClosed_le continuous_const (continuous_minkB_nullVec u)
  ext p
  rw [frontier, (isOpen_halfMinus u s).interior_eq, Set.mem_sdiff]
  constructor
  · rintro ⟨hc, hn⟩
    have h1 : s ≤ minkB (nullVec u) p :=
      closure_minimal (fun x hx => (mem_halfMinus.1 hx).le) hcl hc
    exact le_antisymm (not_lt.1 fun h => hn (mem_halfMinus.2 h)) h1
  · intro hp
    refine ⟨?_, fun h => (mem_halfMinus.1 h).ne' hp⟩
    -- `p − (t, 0)`, `t > 0`, lies in `P⁻` and tends to `p`.
    refine mem_closure_of_tendsto ((tendsto_sub_time p).mono_left
      (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))) ?_
    filter_upwards [self_mem_nhdsWithin] with t (htp : 0 < t)
    rw [mem_halfMinus, minkB_nullVec_sub_time]
    simp only [lightHyperplane, mem_setOf_eq] at hp
    linarith

/-! ### [4.J] The action of `SO₀(1,d)` on `𝒮`, and of `Isom(𝐌ⁿ)` on `𝒥⁺ ≅ 𝒮 × ℝ` -/

/-- The time component `c(A, u) = (A(1,u))₀` of the image of the null vector `(1, u)`.
In the time normalisation used here it plays the role of Barbot's `N(L(g)v)` (l.798, l.840):
`a(g, v) = 1 / c`. -/
def lorentzScale (A : lorentz d) (u : PenroseSphere d) : ℝ :=
  ((A : Minkowski d ≃ₗ[ℝ] Minkowski d) (nullVec u)).1

theorem lorentzScale_pos (A : lorentz d) (u : PenroseSphere d) : 0 < lorentzScale A u := by
  have hc := lorentz.isFutureCausal_apply A.2 (isFutureCausal_nullVec u)
  refine lt_of_le_of_ne hc.1 fun h => ?_
  have h0 := eq_zero_of_fst_eq_zero h.symm hc.2
  exact nullVec_ne_zero u ((A : Minkowski d ≃ₗ[ℝ] Minkowski d).map_eq_zero_iff.1 h0)

theorem norm_lorentz_nullVec_snd (A : lorentz d) (u : PenroseSphere d) :
    ‖((A : Minkowski d ≃ₗ[ℝ] Minkowski d) (nullVec u)).2‖ = lorentzScale A u := by
  have hq : minkQ ((A : Minkowski d ≃ₗ[ℝ] Minkowski d) (nullVec u)) = 0 := by
    rw [lorentz.minkQ_apply A.2, minkQ_nullVec]
  have h2 : ‖((A : Minkowski d ≃ₗ[ℝ] Minkowski d) (nullVec u)).2‖ ^ 2 = lorentzScale A u ^ 2 := by
    unfold minkQ at hq; unfold lorentzScale; linarith
  exact (sq_eq_sq₀ (norm_nonneg _) (lorentzScale_pos A u).le).1 h2

/-- Barbot's `[L(g)].v = L(g)v / N(L(g)v)` (l.798, l.840): the direction of `A(1,u)`. -/
noncomputable def lorentzSphere (A : lorentz d) (u : PenroseSphere d) : PenroseSphere d :=
  ⟨(lorentzScale A u)⁻¹ • ((A : Minkowski d ≃ₗ[ℝ] Minkowski d) (nullVec u)).2, by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_lorentz_nullVec_snd, norm_inv,
      Real.norm_eq_abs, abs_of_pos (lorentzScale_pos A u),
      inv_mul_cancel₀ (lorentzScale_pos A u).ne']⟩

theorem nullVec_lorentzSphere (A : lorentz d) (u : PenroseSphere d) :
    nullVec (lorentzSphere A u) =
      (lorentzScale A u)⁻¹ • (A : Minkowski d ≃ₗ[ℝ] Minkowski d) (nullVec u) := by
  refine Prod.ext ?_ rfl
  change (1 : ℝ) = (lorentzScale A u)⁻¹ * lorentzScale A u
  rw [inv_mul_cancel₀ (lorentzScale_pos A u).ne']

theorem minkB_nullVec_lorentzSphere (A : lorentz d) (u : PenroseSphere d) (p : Minkowski d) :
    minkB (nullVec (lorentzSphere A u)) ((A : Minkowski d ≃ₗ[ℝ] Minkowski d) p) =
      (lorentzScale A u)⁻¹ * minkB (nullVec u) p := by
  rw [nullVec_lorentzSphere, minkB_smul_left, lorentz.minkB_apply A.2]

/-- The chordal distance of `𝒮` in terms of the null vectors: `⟨(1,u) | (1,u')⟩ = −‖u − u'‖²/2`. -/
theorem minkB_nullVec_nullVec (u u' : PenroseSphere d) :
    minkB (nullVec u) (nullVec u') =
      -(‖(u : EuclideanSpace ℝ (Fin d)) - u'‖ ^ 2) / 2 := by
  rw [minkB_nullVec, norm_sub_sq_real, norm_penroseSphere, norm_penroseSphere]
  simp [nullVec]; ring

/-- **Chordal-distance identity for the action of `SO₀(1,d)` on `𝒮`** (l.799–803; it implies
that the action is conformal, which is not stated here as a Lean notion): the chordal distance is
multiplied by `(c(A,u) c(A,u'))^{-1/2}`, i.e. the factor `a = 1/c` at each end. -/
theorem norm_lorentzSphere_sub_sq (A : lorentz d) (u u' : PenroseSphere d) :
    ‖((lorentzSphere A u : PenroseSphere d) : EuclideanSpace ℝ (Fin d)) - lorentzSphere A u'‖ ^ 2 =
      (lorentzScale A u)⁻¹ * (lorentzScale A u')⁻¹ *
        ‖(u : EuclideanSpace ℝ (Fin d)) - u'‖ ^ 2 := by
  have h := minkB_nullVec_nullVec (lorentzSphere A u) (lorentzSphere A u')
  rw [nullVec_lorentzSphere, nullVec_lorentzSphere, minkB_smul_left, minkB_smul_right,
    lorentz.minkB_apply A.2, minkB_nullVec_nullVec] at h
  linarith

/-- **The action of `Isom(𝐌ⁿ)` on `𝒥⁺ ≅ 𝒮 × ℝ`** (l.829–845): `g.(u, s) = ([L(g)]u, a s + b)`
with `a = 1/c(L(g), u)` and `b = ⟨[L(g)]u | τ⟩`, `τ = g(0)` the translation part. -/
noncomputable def isomPenrose (g : isom d) (w : PenroseSphere d × ℝ) : PenroseSphere d × ℝ :=
  (lorentzSphere (linearPart g) w.1,
    (lorentzScale (linearPart g) w.1)⁻¹ * w.2 +
      minkB (nullVec (lorentzSphere (linearPart g) w.1)) (g • (0 : Minkowski d)))

/-- The defining identity of the action: `⟨g.v | g p⟩ − g.s = a (⟨v | p⟩ − s)`. -/
theorem minkB_isomPenrose (g : isom d) (w : PenroseSphere d × ℝ) (p : Minkowski d) :
    minkB (nullVec (isomPenrose g w).1) (g • p) - (isomPenrose g w).2 =
      (lorentzScale (linearPart g) w.1)⁻¹ * (minkB (nullVec w.1) p - w.2) := by
  have h := isom_sub (g : Minkowski d ≃ᵃ[ℝ] Minkowski d) 0 p
  rw [sub_zero] at h
  have hp : g • p = (linearPart g : Minkowski d ≃ₗ[ℝ] Minkowski d) p + g • (0 : Minkowski d) := by
    rw [isom_smul_def, isom_smul_def, linearPart_apply, ← h]; abel
  simp only [isomPenrose]
  rw [hp, minkB_add_right, minkB_nullVec_lorentzSphere]
  ring

/-- `g` maps the lightlike hyperplane of `w` onto that of `g.w`. -/
theorem isom_preimage_lightHyperplane (g : isom d) (w : PenroseSphere d × ℝ) :
    (fun p => g • p) ⁻¹' lightHyperplane (isomPenrose g w).1 (isomPenrose g w).2 =
      lightHyperplane w.1 w.2 := by
  ext p
  have h := minkB_isomPenrose g w p
  have ha := inv_pos.2 (lorentzScale_pos (linearPart g) w.1)
  simp only [mem_preimage, lightHyperplane, mem_setOf_eq]
  constructor
  · intro h'
    rw [h', sub_self] at h
    have := (mul_eq_zero.1 h.symm).resolve_left ha.ne'
    linarith
  · intro h'
    rw [h', sub_self, mul_zero] at h
    linarith

/-- `g` maps `P⁺(w)` onto `P⁺(g.w)`. -/
theorem isom_preimage_halfPlus (g : isom d) (w : PenroseSphere d × ℝ) :
    (fun p => g • p) ⁻¹' halfPlus (isomPenrose g w).1 (isomPenrose g w).2 = halfPlus w.1 w.2 := by
  ext p
  have h := minkB_isomPenrose g w p
  have ha := inv_pos.2 (lorentzScale_pos (linearPart g) w.1)
  simp only [mem_preimage, halfPlus, mem_setOf_eq, h]
  constructor <;> intro h' <;> nlinarith

/-- `g` maps `P⁻(w)` onto `P⁻(g.w)`. -/
theorem isom_preimage_halfMinus (g : isom d) (w : PenroseSphere d × ℝ) :
    (fun p => g • p) ⁻¹' halfMinus (isomPenrose g w).1 (isomPenrose g w).2 = halfMinus w.1 w.2 := by
  ext p
  have h := minkB_isomPenrose g w p
  have ha := inv_pos.2 (lorentzScale_pos (linearPart g) w.1)
  simp only [mem_preimage, halfMinus, mem_setOf_eq, h]
  constructor <;> intro h' <;> nlinarith

/-! ### `bprop:laoucapulse`: what is proved, and the printed claim as a `Prop` -/

/-- A map of a metric space is **expanding at `x`** (a metric reading of l.863–865): some `λ > 1`
such that `λ · dist y z ≤ dist (f y) (f z)` for all `y, z` near `x`. -/
def IsExpandingAt {X : Type*} [PseudoMetricSpace X] (f : X → X) (x : X) : Prop :=
  ∃ l > 1, ∀ᶠ p in 𝓝 x ×ˢ 𝓝 x, l * dist p.1 p.2 ≤ dist (f p.1) (f p.2)

theorem continuous_nullVec : Continuous (nullVec (d := d)) := by
  unfold nullVec; fun_prop

theorem continuous_lorentzScale (A : lorentz d) : Continuous (lorentzScale A) :=
  continuous_fst.comp ((LinearMap.continuous_of_finiteDimensional
    ((A : Minkowski d ≃ₗ[ℝ] Minkowski d) : Minkowski d →ₗ[ℝ] Minkowski d)).comp continuous_nullVec)

theorem dist_lorentzSphere_sq (A : lorentz d) (u u' : PenroseSphere d) :
    dist (lorentzSphere A u) (lorentzSphere A u') ^ 2 =
      (lorentzScale A u)⁻¹ * (lorentzScale A u')⁻¹ * dist u u' ^ 2 := by
  rw [Subtype.dist_eq, Subtype.dist_eq, dist_eq_norm, dist_eq_norm, norm_lorentzSphere_sub_sq]

/-- **The sphere half of `bprop:laoucapulse`**, one direction: where the conformal factor
`a(g, u) = 1/c` exceeds `1`, the action `[L(g)]` on `𝒮` is expanding. -/
theorem isExpandingAt_lorentzSphere (A : lorentz d) {u : PenroseSphere d}
    (hu : 1 < (lorentzScale A u)⁻¹) : IsExpandingAt (lorentzSphere A) u := by
  set l := (1 + (lorentzScale A u)⁻¹) / 2
  have hl1 : 1 < l := by simp only [l]; linarith
  have hlu : l < (lorentzScale A u)⁻¹ := by simp only [l]; linarith
  have hca : Continuous fun v : PenroseSphere d => (lorentzScale A v)⁻¹ :=
    (continuous_lorentzScale A).inv₀ fun v => (lorentzScale_pos A v).ne'
  have hev : ∀ᶠ v in 𝓝 u, l < (lorentzScale A v)⁻¹ := hca.continuousAt.eventually (lt_mem_nhds hlu)
  refine ⟨l, hl1, (hev.prod_mk hev).mono fun p ⟨h1, h2⟩ => ?_⟩
  have hl0 : 0 ≤ l := by linarith
  have hsq : (l * dist p.1 p.2) ^ 2 ≤ dist (lorentzSphere A p.1) (lorentzSphere A p.2) ^ 2 := by
    rw [dist_lorentzSphere_sq, mul_pow]
    have : l ^ 2 ≤ (lorentzScale A p.1)⁻¹ * (lorentzScale A p.2)⁻¹ := by
      rw [sq]; exact mul_le_mul h1.le h2.le hl0 (by linarith)
    exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
  exact (pow_le_pow_iff_left₀ (mul_nonneg hl0 dist_nonneg) dist_nonneg two_ne_zero).1 hsq

/-- `bprop:laoucapulse` (Prop 4.2, l.854–866) **in the metric reading**, kept as a `Prop`; it is
**refuted** for `d = 2` by `not_laoucapulseMetricReading_two` below: for a linear isometry `g`, `g` is expanding at `(u, s) ∈ 𝒥⁺` iff `[L(g)]` is expanding
at `u ∈ 𝒮`. Here `𝒮 × ℝ` carries the product (sup) metric of the chordal metric and `|·|`;
both are locally bi-Lipschitz to Barbot's metrics with constants tending to `1` only for the
sphere factor, see SCOPE. -/
def LaoucapulseMetricReading (d : ℕ) : Prop :=
  ∀ g : isom d, g • (0 : Minkowski d) = 0 → ∀ w : PenroseSphere d × ℝ,
    IsExpandingAt (isomPenrose g) w ↔ IsExpandingAt (lorentzSphere (linearPart g)) w.1

/-! ### `bdef:omega_lambda`, `bdef:regular_domain` -/

/-- **`Ω⁺(Λ) = ⋂_{(u,s) ∈ Λ} P⁺(u,s)`** (Def 4.4, l.894–899). -/
def omegaPlus (Λ : Set (PenroseSphere d × ℝ)) : Set (Minkowski d) :=
  ⋂ w ∈ Λ, halfPlus w.1 w.2

/-- **`Ω⁻(Λ) = ⋂_{(u,s) ∈ Λ} P⁻(u,s)`** (Def 4.4, l.894–899). -/
def omegaMinus (Λ : Set (PenroseSphere d × ℝ)) : Set (Minkowski d) :=
  ⋂ w ∈ Λ, halfMinus w.1 w.2

/-- **Future regular** (Def 4.5, l.915–918): `Ω⁺(Λ)` is nonempty and open. -/
def FutureRegular (Λ : Set (PenroseSphere d × ℝ)) : Prop :=
  (omegaPlus Λ).Nonempty ∧ IsOpen (omegaPlus Λ)

/-- **Past regular** (Def 4.5, l.915–918): `Ω⁻(Λ)` is nonempty and open. -/
def PastRegular (Λ : Set (PenroseSphere d × ℝ)) : Prop :=
  (omegaMinus Λ).Nonempty ∧ IsOpen (omegaMinus Λ)

variable {Λ Λ' : Set (PenroseSphere d × ℝ)}

theorem mem_omegaPlus {p : Minkowski d} :
    p ∈ omegaPlus Λ ↔ ∀ w ∈ Λ, minkB (nullVec w.1) p < w.2 := by
  simp only [omegaPlus, mem_iInter₂, mem_halfPlus]

theorem mem_omegaMinus {p : Minkowski d} :
    p ∈ omegaMinus Λ ↔ ∀ w ∈ Λ, w.2 < minkB (nullVec w.1) p := by
  simp only [omegaMinus, mem_iInter₂, mem_halfMinus]

theorem omegaPlus_anti (h : Λ ⊆ Λ') : omegaPlus Λ' ⊆ omegaPlus Λ := fun _ hp =>
  mem_omegaPlus.2 fun w hw => mem_omegaPlus.1 hp w (h hw)

theorem omegaMinus_anti (h : Λ ⊆ Λ') : omegaMinus Λ' ⊆ omegaMinus Λ := fun _ hp =>
  mem_omegaMinus.2 fun w hw => mem_omegaMinus.1 hp w (h hw)

/-- Observation (l.907): `Ω⁺(Λ)` is convex. -/
theorem convex_omegaPlus (Λ : Set (PenroseSphere d × ℝ)) : Convex ℝ (omegaPlus Λ) :=
  convex_iInter₂ fun w _ => convex_halfPlus w.1 w.2

/-- Observation (l.907): `Ω⁻(Λ)` is convex. -/
theorem convex_omegaMinus (Λ : Set (PenroseSphere d × ℝ)) : Convex ℝ (omegaMinus Λ) :=
  convex_iInter₂ fun w _ => convex_halfMinus w.1 w.2

/-- Observation (l.909): `Ω⁺(Λ)` is complete in the future, `J⁺(Ω⁺(Λ)) ⊆ Ω⁺(Λ)`. -/
theorem Jplus_omegaPlus_subset (Λ : Set (PenroseSphere d × ℝ)) :
    (minkowski d).Jplus ⊤ (omegaPlus Λ) ⊆ omegaPlus Λ := by
  rintro q ⟨p, hp, hpq⟩
  simp only [omegaPlus, mem_iInter₂] at hp ⊢
  exact fun w hw => Jplus_halfPlus_subset w.1 w.2 ⟨p, hp w hw, hpq⟩

/-- Observation (l.910): `Ω⁻(Λ)` is complete in the past, `J⁻(Ω⁻(Λ)) ⊆ Ω⁻(Λ)`. -/
theorem Jminus_omegaMinus_subset (Λ : Set (PenroseSphere d × ℝ)) :
    (minkowski d).Jminus ⊤ (omegaMinus Λ) ⊆ omegaMinus Λ := by
  rintro p ⟨q, hq, hpq⟩
  simp only [omegaMinus, mem_iInter₂] at hq ⊢
  exact fun w hw => Jminus_halfMinus_subset w.1 w.2 ⟨q, hq w hw, hpq⟩

theorem isFutureCausal_smul {c : ℝ} (hc : 0 ≤ c) {v : Minkowski d} (hv : IsFutureCausal v) :
    IsFutureCausal (c • v) :=
  ⟨by simpa using mul_nonneg hc hv.1, by
    rw [minkQ_smul]; exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg c) hv.2⟩

/-- Observation (l.909), geodesic form: the future causal rays from a point of `Ω⁺(Λ)` stay in it. -/
theorem add_smul_mem_omegaPlus {p : Minkowski d} (hp : p ∈ omegaPlus Λ) {v : Minkowski d}
    (hv : IsFutureCausal v) {t : ℝ} (ht : 0 ≤ t) : p + t • v ∈ omegaPlus Λ :=
  Jplus_omegaPlus_subset Λ ⟨p, hp, le_top_iff_minkQ.2 (by simpa using isFutureCausal_smul ht hv)⟩

/-- Observation (l.909), geodesic form for `Ω⁻(Λ)`. -/
theorem sub_smul_mem_omegaMinus {p : Minkowski d} (hp : p ∈ omegaMinus Λ) {v : Minkowski d}
    (hv : IsFutureCausal v) {t : ℝ} (ht : 0 ≤ t) : p - t • v ∈ omegaMinus Λ :=
  Jminus_omegaMinus_subset Λ ⟨p, hp, le_top_iff_minkQ.2 (by simpa using isFutureCausal_smul ht hv)⟩

/-- Observation (l.910–911): **`Ω⁺(Λ)` and `Ω⁻(Λ)` are disjoint**, `Λ` being nonempty (l.882). -/
theorem disjoint_omegaPlus_omegaMinus (hΛ : Λ.Nonempty) :
    Disjoint (omegaPlus Λ) (omegaMinus Λ) := by
  obtain ⟨w, hw⟩ := hΛ
  rw [Set.disjoint_left]
  intro p hp hm
  exact lt_asymm (mem_omegaPlus.1 hp w hw) (mem_omegaMinus.1 hm w hw)

/-! ### Time reflection: the past statements from the future ones -/

/-- `(u, s) ↦ (u, −s)` on `𝒮 × ℝ`. -/
def negS (d : ℕ) : PenroseSphere d × ℝ ≃ₜ PenroseSphere d × ℝ :=
  (Homeomorph.refl _).prodCongr (Homeomorph.neg ℝ)

@[simp] theorem negS_apply (w : PenroseSphere d × ℝ) : negS d w = (w.1, -w.2) := rfl

/-- `Ω⁻(Λ) = −Ω⁺(−Λ)`, the point reflection `p ↦ −p` exchanging future and past. -/
theorem omegaMinus_eq_neg (Λ : Set (PenroseSphere d × ℝ)) :
    omegaMinus Λ = (Homeomorph.neg (Minkowski d)) ⁻¹' omegaPlus (negS d ⁻¹' Λ) := by
  ext p
  simp only [mem_omegaMinus, mem_preimage, mem_omegaPlus, Homeomorph.coe_neg,
    minkB_neg_right, negS_apply]
  constructor
  · intro h w hw; have := h _ hw; simp only at this; linarith
  · intro h w hw
    have := h (w.1, -w.2) (by simpa using hw)
    simp only at this; linarith

/-! ### `blem:fermons`, `bcor:closeregular`, `blem:closecool`, `blem:fermonsbis` -/

/-- **`blem:fermons`** (Lemma 4.6, l.926–945), future half: `Int Ω⁺(Λ) ⊆ Ω⁺(cl Λ)`. -/
theorem interior_omegaPlus_subset (Λ : Set (PenroseSphere d × ℝ)) :
    interior (omegaPlus Λ) ⊆ omegaPlus (closure Λ) := by
  intro x hx
  -- a point `y = x − (ε, 0)` of `Ω⁺(Λ)`, with `⟨v | y⟩ = ⟨v | x⟩ + ε` for every `v`
  have ht : Tendsto (fun t : ℝ => x - ((t, 0) : Minkowski d)) (𝓝[>] 0) (𝓝 x) :=
    (tendsto_sub_time x).mono_left nhdsWithin_le_nhds
  obtain ⟨ε, hy, hε⟩ :=
    ((ht.eventually (mem_interior_iff_mem_nhds.1 hx)).and self_mem_nhdsWithin).exists
  have hε : (0 : ℝ) < ε := hε
  -- on `Λ`, hence on its closure, `⟨v | y⟩ ≤ s`
  have hcl : closure Λ ⊆ {w | minkB (nullVec w.1) (x - ((ε, 0) : Minkowski d)) ≤ w.2} :=
    closure_minimal (fun w hw => (mem_omegaPlus.1 hy w hw).le)
      (isClosed_le (continuous_minkB_nullVec_param _) continuous_snd)
  refine mem_omegaPlus.2 fun w hw => ?_
  have := hcl hw
  simp only [mem_setOf_eq, minkB_nullVec_sub_time] at this
  linarith

/-- **`blem:fermons`** (Lemma 4.6), past half: `Int Ω⁻(Λ) ⊆ Ω⁻(cl Λ)`. -/
theorem interior_omegaMinus_subset (Λ : Set (PenroseSphere d × ℝ)) :
    interior (omegaMinus Λ) ⊆ omegaMinus (closure Λ) := by
  rw [omegaMinus_eq_neg, omegaMinus_eq_neg, ← Homeomorph.preimage_interior,
    Homeomorph.preimage_closure]
  exact preimage_mono (interior_omegaPlus_subset _)

/-- **`blem:closecool`** (Lemma 4.8, l.962–984): `Λ` closed ⇒ `Ω⁺(Λ)` open. -/
theorem isOpen_omegaPlus_of_isClosed (hΛ : IsClosed Λ) : IsOpen (omegaPlus Λ) := by
  rw [Metric.isOpen_iff]
  intro x hx
  set g : PenroseSphere d × ℝ → ℝ := fun w => w.2 - minkB (nullVec w.1) x with hg_def
  have hg : Continuous g := continuous_snd.sub (continuous_minkB_nullVec_param x)
  have hgpos : ∀ w ∈ Λ, 0 < g w := fun w hw => sub_pos.2 (mem_omegaPlus.1 hx w hw)
  set R := |x.1| + ‖x.2‖
  have hR : ∀ w : PenroseSphere d × ℝ, |minkB (nullVec w.1) x| ≤ R := fun w =>
    abs_minkB_nullVec_le w.1 x
  -- outside a compact slab, `g > 1`; on the slab, `g` has a positive minimum
  set K := Λ ∩ (univ ×ˢ Icc (-R) (R + 1))
  have hK : IsCompact K := (isCompact_univ.prod isCompact_Icc).inter_left hΛ
  have hout : ∀ w ∈ Λ, w ∉ K → 1 ≤ g w := by
    intro w hw hwK
    have h1 : -R < w.2 := by
      have := hgpos w hw; have := neg_abs_le (minkB (nullVec w.1) x); simp only [g] at *
      linarith [hR w]
    have h2 : R + 1 < w.2 := by
      by_contra h
      exact hwK ⟨hw, mem_univ _, h1.le, not_lt.1 h⟩
    simp only [g]; linarith [le_abs_self (minkB (nullVec w.1) x), hR w]
  obtain ⟨δ, hδ, hδg⟩ : ∃ δ > 0, ∀ w ∈ Λ, δ ≤ g w := by
    rcases K.eq_empty_or_nonempty with hKe | hKne
    · exact ⟨1, one_pos, fun w hw => hout w hw (by rw [hKe]; exact notMem_empty w)⟩
    · obtain ⟨w₀, hw₀, hmin⟩ := hK.exists_isMinOn hKne hg.continuousOn
      refine ⟨min (g w₀) 1, lt_min (hgpos w₀ hw₀.1) one_pos, fun w hw => ?_⟩
      by_cases hwK : w ∈ K
      · exact (min_le_left _ _).trans (isMinOn_iff.1 hmin w hwK)
      · exact (min_le_right _ _).trans (hout w hw hwK)
  refine ⟨δ / 2, half_pos hδ, fun y hy => mem_omegaPlus.2 fun w hw => ?_⟩
  have hyx : ‖y - x‖ < δ / 2 := by rw [← dist_eq_norm]; exact hy
  have h1 := abs_minkB_nullVec_le_two_mul_norm w.1 (y - x)
  rw [minkB_sub_right] at h1
  have h2 := hδg w hw
  simp only [g] at h2
  linarith [le_abs_self (minkB (nullVec w.1) y - minkB (nullVec w.1) x)]

/-- **`blem:closecool`** for `Ω⁻` ("the similar statements for past regular domains are evidently
valid", l.1004–1005). -/
theorem isOpen_omegaMinus_of_isClosed (hΛ : IsClosed Λ) : IsOpen (omegaMinus Λ) := by
  rw [omegaMinus_eq_neg]
  exact (isOpen_omegaPlus_of_isClosed (hΛ.preimage (negS d).continuous)).preimage
    (Homeomorph.neg _).continuous

/-- **`blem:fermonsbis`** (Lemma 4.9, l.986–998), with no hypothesis on `Λ`:
`Ω⁺(cl Λ) = Int Ω⁺(Λ)`. -/
theorem omegaPlus_closure_eq_interior (Λ : Set (PenroseSphere d × ℝ)) :
    omegaPlus (closure Λ) = interior (omegaPlus Λ) :=
  (interior_maximal (omegaPlus_anti subset_closure)
    (isOpen_omegaPlus_of_isClosed isClosed_closure)).antisymm (interior_omegaPlus_subset Λ)

/-- **`blem:fermonsbis`** for `Ω⁻`. -/
theorem omegaMinus_closure_eq_interior (Λ : Set (PenroseSphere d × ℝ)) :
    omegaMinus (closure Λ) = interior (omegaMinus Λ) :=
  (interior_maximal (omegaMinus_anti subset_closure)
    (isOpen_omegaMinus_of_isClosed isClosed_closure)).antisymm (interior_omegaMinus_subset Λ)

/-- **`blem:fermonsbis`** as printed: `Λ` with future regular closure. -/
theorem omegaPlus_closure_eq_interior_of_futureRegular (_h : FutureRegular (closure Λ)) :
    omegaPlus (closure Λ) = interior (omegaPlus Λ) :=
  omegaPlus_closure_eq_interior Λ

/-- **`bcor:closeregular`** (Corollary 4.7, l.950–960): `Λ` future regular ⇒ `cl Λ` future regular
and `Ω⁺(Λ) = Ω⁺(cl Λ)`. -/
theorem FutureRegular.closure_futureRegular (h : FutureRegular Λ) :
    FutureRegular (closure Λ) ∧ omegaPlus Λ = omegaPlus (closure Λ) := by
  have he : omegaPlus Λ = omegaPlus (closure Λ) := by
    rw [omegaPlus_closure_eq_interior, h.2.interior_eq]
  exact ⟨⟨he ▸ h.1, he ▸ h.2⟩, he⟩

/-- **`bcor:closeregular`** for past regular sets. -/
theorem PastRegular.closure_pastRegular (h : PastRegular Λ) :
    PastRegular (closure Λ) ∧ omegaMinus Λ = omegaMinus (closure Λ) := by
  have he : omegaMinus Λ = omegaMinus (closure Λ) := by
    rw [omegaMinus_closure_eq_interior, h.2.interior_eq]
  exact ⟨⟨he ▸ h.1, he ▸ h.2⟩, he⟩

/-! ### `bprop:regular_iff_bounded`, `bcor:futetpast` -/

/-- The point `(−C, 0)` has `⟨(1,u) | ·⟩ = C` for every `u`: the lightlike hyperplanes
`{s = C}` are tangent to its cone (l.1018–1022). -/
theorem minkB_nullVec_apex (u : PenroseSphere d) (C : ℝ) :
    minkB (nullVec u) ((-C, 0) : Minkowski d) = C := by
  simp [minkB_nullVec]

/-- `Ω⁺(Λ)` is nonempty iff the second components of `Λ` are bounded **below** — no closedness
needed. -/
theorem omegaPlus_nonempty_iff :
    (omegaPlus Λ).Nonempty ↔ ∃ C : ℝ, ∀ w ∈ Λ, C < w.2 := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨-(|x.1| + ‖x.2‖), fun w hw => ?_⟩
    have := mem_omegaPlus.1 hx w hw
    linarith [neg_abs_le (minkB (nullVec w.1) x), abs_minkB_nullVec_le w.1 x]
  · rintro ⟨C, hC⟩
    exact ⟨(-C, 0), mem_omegaPlus.2 fun w hw => by rw [minkB_nullVec_apex]; exact hC w hw⟩

/-- `Ω⁻(Λ)` is nonempty iff the second components of `Λ` are bounded **above**. -/
theorem omegaMinus_nonempty_iff :
    (omegaMinus Λ).Nonempty ↔ ∃ C : ℝ, ∀ w ∈ Λ, w.2 < C := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨|x.1| + ‖x.2‖, fun w hw => ?_⟩
    have := mem_omegaMinus.1 hx w hw
    linarith [le_abs_self (minkB (nullVec w.1) x), abs_minkB_nullVec_le w.1 x]
  · rintro ⟨C, hC⟩
    exact ⟨(-C, 0), mem_omegaMinus.2 fun w hw => by rw [minkB_nullVec_apex]; exact hC w hw⟩

/-- `bprop:regular_iff_bounded` (Prop 4.10, l.1007–1033), future half, **corrected**: a closed
`Λ` is future regular iff its second components are bounded **below** (the proof's own
conclusion, l.1017–1031; the statement's "less than `C`" is a sign error). -/
theorem futureRegular_iff_exists_lt (hΛ : IsClosed Λ) :
    FutureRegular Λ ↔ ∃ C : ℝ, ∀ w ∈ Λ, C < w.2 :=
  ⟨fun h => omegaPlus_nonempty_iff.1 h.1,
    fun h => ⟨omegaPlus_nonempty_iff.2 h, isOpen_omegaPlus_of_isClosed hΛ⟩⟩

/-- `bprop:regular_iff_bounded`, past half, corrected: bounded **above**. -/
theorem pastRegular_iff_exists_gt (hΛ : IsClosed Λ) :
    PastRegular Λ ↔ ∃ C : ℝ, ∀ w ∈ Λ, w.2 < C :=
  ⟨fun h => omegaMinus_nonempty_iff.1 h.1,
    fun h => ⟨omegaMinus_nonempty_iff.2 h, isOpen_omegaMinus_of_isClosed hΛ⟩⟩

/-- `bprop:regular_iff_bounded` **as printed** (l.1009–1013), kept as a `Prop` (kb/0022, DEC-27):
for every nonempty closed `Λ`, future regular iff `s < C`, past regular iff `s > C`. -/
def RegularIffBoundedAsPrinted (d : ℕ) : Prop :=
  ∀ Λ : Set (PenroseSphere d × ℝ), Λ.Nonempty → IsClosed Λ →
    (FutureRegular Λ ↔ ∃ C : ℝ, ∀ w ∈ Λ, w.2 < C) ∧
      (PastRegular Λ ↔ ∃ C : ℝ, ∀ w ∈ Λ, C < w.2)

/-- A point of `𝒮`, for `d ≥ 1`. -/
noncomputable def sphereBase (hd : 0 < d) : PenroseSphere d :=
  ⟨unitVec d hd, by rw [mem_sphere_zero_iff_norm, norm_unitVec]⟩

/-- **The printed form of `bprop:regular_iff_bounded` is false** in every dimension `d ≥ 1`
(Barbot's `n ≥ 2`): `Λ = 𝒮 × [0, ∞)` is closed, nonempty and future regular (`Ω⁺(Λ)` is the open
future cone of `0`), and its second components are not bounded above. -/
theorem not_regularIffBoundedAsPrinted (hd : 0 < d) : ¬ RegularIffBoundedAsPrinted d := by
  intro h
  have hcl : IsClosed (univ ×ˢ Ici (0 : ℝ) : Set (PenroseSphere d × ℝ)) :=
    isClosed_univ.prod isClosed_Ici
  have hne : (univ ×ˢ Ici (0 : ℝ) : Set (PenroseSphere d × ℝ)).Nonempty :=
    ⟨(sphereBase hd, 0), mem_univ _, self_mem_Ici⟩
  have hfr : FutureRegular (univ ×ˢ Ici (0 : ℝ) : Set (PenroseSphere d × ℝ)) :=
    (futureRegular_iff_exists_lt hcl).2 ⟨-1, fun w hw => by
      have : (0 : ℝ) ≤ w.2 := hw.2
      linarith⟩
  obtain ⟨C, hC⟩ := ((h _ hne hcl).1).1 hfr
  have := hC (sphereBase hd, max C 0) ⟨mem_univ _, mem_Ici.2 (le_max_right _ _)⟩
  exact absurd this (not_lt.2 (le_max_left _ _))

/-- `bcor:futetpast` (Corollary 4.11, l.1035–1039), one direction, no closedness needed: a
compact `Λ` is future regular and past regular. -/
theorem futureRegular_and_pastRegular_of_isCompact (hK : IsCompact Λ) :
    FutureRegular Λ ∧ PastRegular Λ := by
  have hs : IsCompact (Prod.snd '' Λ) := hK.image continuous_snd
  obtain ⟨m, hm⟩ := hs.isBounded.bddBelow
  obtain ⟨M, hM⟩ := hs.isBounded.bddAbove
  refine ⟨(futureRegular_iff_exists_lt hK.isClosed).2 ⟨m - 1, fun w hw => ?_⟩,
    (pastRegular_iff_exists_gt hK.isClosed).2 ⟨M + 1, fun w hw => ?_⟩⟩
  · have := hm ⟨w, hw, rfl⟩; linarith
  · have := hM ⟨w, hw, rfl⟩; linarith

/-- `bcor:futetpast` (Corollary 4.11): a closed `Λ` is future regular and past regular iff it
is compact. -/
theorem futureRegular_and_pastRegular_iff_isCompact (hΛ : IsClosed Λ) :
    FutureRegular Λ ∧ PastRegular Λ ↔ IsCompact Λ := by
  refine ⟨fun ⟨hf, hp⟩ => ?_, futureRegular_and_pastRegular_of_isCompact⟩
  obtain ⟨C₁, h₁⟩ := (futureRegular_iff_exists_lt hΛ).1 hf
  obtain ⟨C₂, h₂⟩ := (pastRegular_iff_exists_gt hΛ).1 hp
  exact (isCompact_univ.prod isCompact_Icc).of_isClosed_subset hΛ fun w hw =>
    ⟨mem_univ _, (h₁ w hw).le, (h₂ w hw).le⟩

/-- A witness (kb/0011): `Λ = 𝒮 × {0}` is future and past regular; `Ω⁺(Λ)` is the open future
cone of the origin, `Ω⁻(Λ)` the open past cone. -/
theorem futureRegular_and_pastRegular_cone :
    FutureRegular (univ ×ˢ {0} : Set (PenroseSphere d × ℝ)) ∧
      PastRegular (univ ×ˢ {0} : Set (PenroseSphere d × ℝ)) :=
  futureRegular_and_pastRegular_of_isCompact (isCompact_univ.prod isCompact_singleton)

/-! ### Two counterexamples, for the non-closed readings -/

/-- If every element of `Λ` has direction `u` and `(u, a) ∈ Λ` has the least `s`, then
`Ω⁺(Λ) = P⁺(u, a)`. -/
theorem omegaPlus_eq_halfPlus_of_least {u : PenroseSphere d} {a : ℝ} (ha : (u, a) ∈ Λ)
    (h : ∀ w ∈ Λ, w.1 = u ∧ a ≤ w.2) : omegaPlus Λ = halfPlus u a := by
  refine (biInter_subset_of_mem ha).antisymm fun p hp => mem_omegaPlus.2 fun w hw => ?_
  obtain ⟨h1, h2⟩ := h w hw
  rw [h1]; exact (mem_halfPlus.1 hp).trans_le h2

/-- If every element of `Λ` has direction `u` and `(u, b) ∈ Λ` has the greatest `s`, then
`Ω⁻(Λ) = P⁻(u, b)`. -/
theorem omegaMinus_eq_halfMinus_of_greatest {u : PenroseSphere d} {b : ℝ} (hb : (u, b) ∈ Λ)
    (h : ∀ w ∈ Λ, w.1 = u ∧ w.2 ≤ b) : omegaMinus Λ = halfMinus u b := by
  refine (biInter_subset_of_mem hb).antisymm fun p hp => mem_omegaMinus.2 fun w hw => ?_
  obtain ⟨h1, h2⟩ := h w hw
  rw [h1]; exact h2.trans_lt (mem_halfMinus.1 hp)

/-- **The sentence closing Def 4.4 (l.901–902) fails for a non-closed `Λ`.** "If `Λ` contains at
least 2 elements, then `Ω^±(Λ)`, if nonempty, is regular": `Λ = {u₀} × ]0, ∞[` has at least two
elements and a nonempty `Ω⁺(Λ) = {⟨v | p⟩ ≤ 0}`, which is not open. (For closed `Λ` the sentence
holds, by `isOpen_omegaPlus_of_isClosed`, whatever the number of elements.) -/
theorem not_futureRegular_ray (hd : 0 < d) :
    ((sphereBase hd, (1 : ℝ)) ∈ ({sphereBase hd} ×ˢ Ioi 0 : Set (PenroseSphere d × ℝ)) ∧
      (sphereBase hd, (2 : ℝ)) ∈ ({sphereBase hd} ×ˢ Ioi 0 : Set (PenroseSphere d × ℝ))) ∧
    (omegaPlus ({sphereBase hd} ×ˢ Ioi 0 : Set (PenroseSphere d × ℝ))).Nonempty ∧
    ¬ FutureRegular ({sphereBase hd} ×ˢ Ioi 0 : Set (PenroseSphere d × ℝ)) := by
  set u := sphereBase hd
  have hΩ : ∀ p, p ∈ omegaPlus ({u} ×ˢ Ioi 0 : Set (PenroseSphere d × ℝ)) ↔
      minkB (nullVec u) p ≤ 0 := by
    intro p
    rw [mem_omegaPlus]
    constructor
    · intro h
      by_contra hp
      push Not at hp
      have := h (u, minkB (nullVec u) p / 2) ⟨rfl, by simp only [mem_Ioi]; linarith⟩
      simp only at this; linarith
    · rintro hp w ⟨hw1, hw2⟩
      simp only [mem_singleton_iff] at hw1
      rw [hw1]; exact hp.trans_lt hw2
  have h0 : (0 : Minkowski d) ∈ omegaPlus ({u} ×ˢ Ioi 0 : Set (PenroseSphere d × ℝ)) := by
    rw [hΩ]; simp [minkB_nullVec]
  refine ⟨⟨⟨rfl, by norm_num⟩, ⟨rfl, by norm_num⟩⟩, ⟨0, h0⟩, fun hreg => ?_⟩
  have ht : Tendsto (fun t : ℝ => (0 : Minkowski d) - ((t, 0) : Minkowski d)) (𝓝[>] 0)
      (𝓝 0) := (tendsto_sub_time 0).mono_left nhdsWithin_le_nhds
  obtain ⟨t, htΩ, htp⟩ :=
    ((ht.eventually (hreg.2.mem_nhds h0)).and self_mem_nhdsWithin).exists
  have htΩ' := (hΩ _).1 htΩ
  rw [minkB_nullVec_sub_time] at htΩ'
  have : (0 : ℝ) < t := htp
  simp [minkB_nullVec] at htΩ'
  linarith

/-- **`bcor:futetpast` needs `Λ` closed.** `Λ = {u₀} × ([0,1] ∖ {1/2})` is future regular and past
regular (`Ω⁺(Λ) = P⁺(u₀, 0)`, `Ω⁻(Λ) = P⁻(u₀, 1)`), and not compact. -/
theorem futureRegular_pastRegular_not_isCompact (hd : 0 < d) :
    FutureRegular ({sphereBase hd} ×ˢ (Icc 0 1 \ {1 / 2}) : Set (PenroseSphere d × ℝ)) ∧
    PastRegular ({sphereBase hd} ×ˢ (Icc 0 1 \ {1 / 2}) : Set (PenroseSphere d × ℝ)) ∧
    ¬ IsCompact ({sphereBase hd} ×ˢ (Icc 0 1 \ {1 / 2}) : Set (PenroseSphere d × ℝ)) := by
  set u := sphereBase hd
  set S : Set ℝ := Icc 0 1 \ {1 / 2}
  have h0 : (u, (0 : ℝ)) ∈ ({u} ×ˢ S : Set (PenroseSphere d × ℝ)) :=
    ⟨rfl, ⟨le_rfl, zero_le_one⟩, by norm_num⟩
  have h1 : (u, (1 : ℝ)) ∈ ({u} ×ˢ S : Set (PenroseSphere d × ℝ)) :=
    ⟨rfl, ⟨zero_le_one, le_rfl⟩, by norm_num⟩
  have hP := omegaPlus_eq_halfPlus_of_least h0 fun w hw => ⟨hw.1, hw.2.1.1⟩
  have hM := omegaMinus_eq_halfMinus_of_greatest h1 fun w hw => ⟨hw.1, hw.2.1.2⟩
  refine ⟨⟨⟨(-(-1), 0), ?_⟩, hP ▸ isOpen_halfPlus u 0⟩, ⟨⟨(-2, 0), ?_⟩, hM ▸ isOpen_halfMinus u 1⟩,
    fun hK => ?_⟩
  · rw [hP, mem_halfPlus, minkB_nullVec_apex]; norm_num
  · rw [hM, mem_halfMinus, minkB_nullVec_apex]; norm_num
  · -- the second projection `S` would be compact, hence closed; but `1/2 ∈ cl S ∖ S`
    have hS : IsClosed S := by
      have := (hK.image continuous_snd).isClosed
      rwa [snd_image_prod (singleton_nonempty u)] at this
    have hc : (1 / 2 : ℝ) ∈ closure S := by
      have ht : Tendsto (fun t : ℝ => 1 / 2 + t) (𝓝[>] 0) (𝓝 (1 / 2)) := by
        have hc : Continuous fun t : ℝ => 1 / 2 + t := by fun_prop
        have := (hc.tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
        simpa using this
      refine mem_closure_of_tendsto ht ?_
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with t ht
      exact ⟨⟨by linarith [ht.1], by linarith [ht.2]⟩, by simp only [mem_singleton_iff]; linarith [ht.1]⟩
    exact (hS.closure_eq ▸ hc).2 rfl

/-! ### Equivariance -/

/-- **`g(Ω⁺(Λ)) = Ω⁺(g.Λ)`**, as a preimage. -/
theorem isom_preimage_omegaPlus (g : isom d) (Λ : Set (PenroseSphere d × ℝ)) :
    (fun p => g • p) ⁻¹' omegaPlus (isomPenrose g '' Λ) = omegaPlus Λ := by
  ext p
  simp only [mem_preimage, omegaPlus, mem_iInter₂, forall_mem_image]
  refine forall₂_congr fun w _ => ?_
  rw [← isom_preimage_halfPlus g w, mem_preimage]

/-- **`g(Ω⁻(Λ)) = Ω⁻(g.Λ)`**, as a preimage. -/
theorem isom_preimage_omegaMinus (g : isom d) (Λ : Set (PenroseSphere d × ℝ)) :
    (fun p => g • p) ⁻¹' omegaMinus (isomPenrose g '' Λ) = omegaMinus Λ := by
  ext p
  simp only [mem_preimage, omegaMinus, mem_iInter₂, forall_mem_image]
  refine forall₂_congr fun w _ => ?_
  rw [← isom_preimage_halfMinus g w, mem_preimage]

/-! ### Global hyperbolicity -/

/-- The straight segment of a causal relation is causal: its points lie between the ends. -/
theorem le_top_of_mem_segment {p q y : Minkowski d} (h : (minkowski d).le ⊤ p q)
    (hy : y ∈ segment ℝ p q) : (minkowski d).le ⊤ p y ∧ (minkowski d).le ⊤ y q := by
  rw [segment_eq_image'] at hy
  obtain ⟨θ, hθ, rfl⟩ := hy
  have hv := le_top_iff_minkQ.1 h
  refine ⟨le_top_iff_minkQ.2 ?_, le_top_iff_minkQ.2 ?_⟩
  · simpa using isFutureCausal_smul hθ.1 hv
  · have : q - (p + θ • (q - p)) = (1 - θ) • (q - p) := by
      rw [sub_smul, one_smul]; abel
    rw [this]; exact isFutureCausal_smul (by linarith [hθ.2]) hv

/-- A causal relation of `𝐌ⁿ` whose straight segment lies in `W` is a relation of `≤_W`: a thin
open thickening of the segment is convex and lies in `W`, and `Form.le_iff_of_convex` applies to it. -/
theorem le_of_le_top_of_segment_subset {W : Opens (Minkowski d)} {p q : Minkowski d}
    (h : (minkowski d).le ⊤ p q) (hs : segment ℝ p q ⊆ W) : (minkowski d).le W p q := by
  have hK : IsCompact (segment ℝ p q) := by
    rw [segment_eq_image']; exact isCompact_Icc.image (by fun_prop)
  obtain ⟨δ, hδ, hδW⟩ := hK.exists_thickening_subset_open W.isOpen hs
  let V : Opens (Minkowski d) := ⟨thickening δ (segment ℝ p q), isOpen_thickening⟩
  have hsub := self_subset_thickening hδ (segment ℝ p q)
  have hV : (minkowski d).le V p q := (le_iff_of_convex ((convex_segment p q).thickening δ)).2
    ⟨hsub (left_mem_segment ℝ p q), hsub (right_mem_segment ℝ p q), h⟩
  exact (minkowski d).le_mono (show V ≤ W from hδW) hV

/-- On a causally convex open `W`, the diamonds of `≤_W` between points of `W` are those of `𝐌ⁿ`. -/
theorem diamond_eq_of_causallyConvexIn {W : Opens (Minkowski d)}
    (hW : (minkowski d).CausallyConvexIn (W : Set (Minkowski d)) ⊤) {p q : Minkowski d}
    (hp : p ∈ W) (hq : q ∈ W) : (minkowski d).diamond W p q = (minkowski d).diamond ⊤ p q := by
  ext x
  simp only [Causality.mem_diamond]
  refine ⟨fun ⟨h1, h2⟩ => ⟨(minkowski d).le_mono le_top h1, (minkowski d).le_mono le_top h2⟩,
    fun ⟨h1, h2⟩ => ⟨le_of_le_top_of_segment_subset h1 fun y hy => ?_,
      le_of_le_top_of_segment_subset h2 fun y hy => ?_⟩⟩
  · obtain ⟨hy1, hy2⟩ := le_top_of_mem_segment h1 hy
    exact hW.2 p hp q hq (Causality.mem_diamond.2 ⟨hy1, (minkowski d).le_trans hy2 h2⟩)
  · obtain ⟨hy1, hy2⟩ := le_top_of_mem_segment h2 hy
    exact hW.2 p hp q hq (Causality.mem_diamond.2 ⟨(minkowski d).le_trans h1 hy1, hy2⟩)

/-- **A causally convex open subset of `𝐌ⁿ` is globally hyperbolic** (ETT's
`def:globally_hyperbolic`, read on `W`). -/
theorem globallyHyperbolicOn_of_causallyConvexIn {W : Opens (Minkowski d)}
    (hW : (minkowski d).CausallyConvexIn (W : Set (Minkowski d)) ⊤) :
    (minkowski d).GloballyHyperbolicOn W := by
  refine ⟨fun x y hxy hyx => minkowski_isCausal ((minkowski d).le_mono le_top hxy)
    ((minkowski d).le_mono le_top hyx), fun p q => ?_⟩
  by_cases hp : p ∈ W
  · by_cases hq : q ∈ W
    · rw [diamond_eq_of_causallyConvexIn hW hp hq]
      exact minkowski_globallyHyperbolic.2 p q
    · convert isCompact_empty
      refine eq_empty_of_forall_notMem fun x hx => hq ?_
      exact (minkowski d).le_mem_right (Causality.mem_diamond.1 hx).2
  · convert isCompact_empty
    refine eq_empty_of_forall_notMem fun x hx => hp ?_
    exact (minkowski d).le_mem_left (Causality.mem_diamond.1 hx).1

/-- A future complete subset of `𝐌ⁿ` is causally convex. -/
theorem causallyConvexIn_of_Jplus_subset {W : Set (Minkowski d)}
    (hW : (minkowski d).Jplus ⊤ W ⊆ W) : (minkowski d).CausallyConvexIn W ⊤ :=
  ⟨fun _ _ => trivial, fun p hp _ _ _ hx => hW ⟨p, hp, (Causality.mem_diamond.1 hx).1⟩⟩

/-- A past complete subset of `𝐌ⁿ` is causally convex. -/
theorem causallyConvexIn_of_Jminus_subset {W : Set (Minkowski d)}
    (hW : (minkowski d).Jminus ⊤ W ⊆ W) : (minkowski d).CausallyConvexIn W ⊤ :=
  ⟨fun _ _ => trivial, fun _ _ q hq _ hx => hW ⟨q, hq, (Causality.mem_diamond.1 hx).2⟩⟩

/-- **An open future complete subset of `𝐌ⁿ` is globally hyperbolic.** Convexity is not used. -/
theorem globallyHyperbolicOn_of_Jplus_subset {W : Opens (Minkowski d)}
    (hW : (minkowski d).Jplus ⊤ (W : Set (Minkowski d)) ⊆ W) :
    (minkowski d).GloballyHyperbolicOn W :=
  globallyHyperbolicOn_of_causallyConvexIn (causallyConvexIn_of_Jplus_subset hW)

/-- **An open past complete subset of `𝐌ⁿ` is globally hyperbolic.** -/
theorem globallyHyperbolicOn_of_Jminus_subset {W : Opens (Minkowski d)}
    (hW : (minkowski d).Jminus ⊤ (W : Set (Minkowski d)) ⊆ W) :
    (minkowski d).GloballyHyperbolicOn W :=
  globallyHyperbolicOn_of_causallyConvexIn (causallyConvexIn_of_Jminus_subset hW)

/-- A future regular convex domain, as an open set. -/
def FutureRegular.opens (h : FutureRegular Λ) : Opens (Minkowski d) := ⟨omegaPlus Λ, h.2⟩

/-- A past regular convex domain, as an open set. -/
def PastRegular.opens (h : PastRegular Λ) : Opens (Minkowski d) := ⟨omegaMinus Λ, h.2⟩

/-- **A future regular convex domain is globally hyperbolic.** -/
theorem FutureRegular.globallyHyperbolicOn (h : FutureRegular Λ) :
    (minkowski d).GloballyHyperbolicOn h.opens :=
  globallyHyperbolicOn_of_Jplus_subset (Jplus_omegaPlus_subset Λ)

/-- **A past regular convex domain is globally hyperbolic.** -/
theorem PastRegular.globallyHyperbolicOn (h : PastRegular Λ) :
    (minkowski d).GloballyHyperbolicOn h.opens :=
  globallyHyperbolicOn_of_Jminus_subset (Jminus_omegaMinus_subset Λ)

/-! ### `bprop:laoucapulse`: the metric reading fails for `d = 2` (Barbot's `n = 3`)

A boost `g` of rapidity `artanh (3/5)`, the point `w = (u₀, 4)` with `u₀ = (−3/5, 4/5)`, where the
conformal factor is `a(g, u₀) = 5/4 > 1`; the curve `γ t = (R_t u₀, s(t))` (`R_t` the rotation with
`tan (θ/2) = t`) with `s(t)` chosen so that `g.γ t` and `g.w` have the same `s`-component. Along it,
`dist (g.w) (g.γ t) ≤ dist w (γ t)`, so `g` is not expanding at `w`, while `[L(g)]` is expanding at
`u₀`. -/

/-! Coordinates of `𝐌³` (`d = 2`). -/

theorem norm_sq_fin_two (x : EuclideanSpace ℝ (Fin 2)) : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]

theorem minkQ_two (p : Minkowski 2) : minkQ p = -p.1 ^ 2 + p.2 0 ^ 2 + p.2 1 ^ 2 := by
  rw [minkQ, norm_sq_fin_two]; ring

theorem norm_eq_one_of_fin_two {x : EuclideanSpace ℝ (Fin 2)} (h : x 0 ^ 2 + x 1 ^ 2 = 1) :
    ‖x‖ = 1 :=
  (sq_eq_sq₀ (norm_nonneg x) zero_le_one).1 (by rw [norm_sq_fin_two, h, one_pow])

namespace Laoucapulse

/-- `(t, x, y) ↦ (c t + σ x, σ t + c x, y)`. -/
noncomputable def boostFun (c σ : ℝ) (p : Minkowski 2) : Minkowski 2 :=
  (c * p.1 + σ * p.2 0, !₂[σ * p.1 + c * p.2 0, p.2 1])

theorem boostFun_boostFun {c σ : ℝ} (h : c ^ 2 - σ ^ 2 = 1) (p : Minkowski 2) :
    boostFun c (-σ) (boostFun c σ p) = p := by
  refine Prod.ext ?_ ?_
  · simp only [boostFun]
    simp
    linear_combination p.1 * h
  · ext i; fin_cases i
    · simp [boostFun]; linear_combination p.2 0 * h
    · simp [boostFun]

/-- The boost of rapidity `artanh (3/5)` (`cosh = 5/4`, `sinh = 3/4`) in the `(t, x)` plane. -/
noncomputable def boostL : Minkowski 2 ≃ₗ[ℝ] Minkowski 2 where
  toFun := boostFun (5 / 4) (3 / 4)
  invFun := boostFun (5 / 4) (-(3 / 4))
  map_add' p q := by
    refine Prod.ext ?_ ?_
    · simp [boostFun]; ring
    · ext i; fin_cases i
      · simp [boostFun]; ring
      · simp [boostFun]
  map_smul' a p := by
    refine Prod.ext ?_ ?_
    · simp [boostFun]; ring
    · ext i; fin_cases i
      · simp [boostFun]; ring
      · simp [boostFun]
  left_inv p := boostFun_boostFun (by norm_num) p
  right_inv p := by simpa using boostFun_boostFun (c := 5 / 4) (σ := -(3 / 4)) (by norm_num) p

theorem boostL_apply (p : Minkowski 2) : boostL p = boostFun (5 / 4) (3 / 4) p := rfl

/-- Coordinates `𝐌³ ≃ ℝ³`, to compute a determinant. -/
noncomputable def coords3 : Minkowski 2 ≃ₗ[ℝ] (Fin 3 → ℝ) where
  toFun p := ![p.1, p.2 0, p.2 1]
  invFun v := (v 0, !₂[v 1, v 2])
  map_add' p q := by funext i; fin_cases i <;> simp
  map_smul' a p := by funext i; fin_cases i <;> simp
  left_inv p := by
    refine Prod.ext rfl ?_
    ext i; fin_cases i <;> simp
  right_inv v := by funext i; fin_cases i <;> simp

theorem boostL_mem : boostL ∈ lorentz 2 := by
  have hQ : ∀ v, minkQ (boostL v) = minkQ v := fun v => by
    rw [minkQ_two, minkQ_two]; simp [boostL_apply, boostFun]; ring
  refine ⟨hQ, fun v hv => ⟨?_, by rw [hQ]; exact hv.2⟩, ?_⟩
  · have h1 := hv.1
    have h2 := hv.2
    rw [minkQ_two] at h2
    simp only [boostL_apply, boostFun]
    nlinarith [sq_nonneg (v.2 1), sq_nonneg (5 * v.1 + 3 * v.2 0), sq_nonneg (v.1 + v.2 0)]
  · rw [← LinearMap.det_conj _ coords3, ← LinearMap.det_toMatrix', Matrix.det_fin_three]
    simp [LinearMap.toMatrix'_apply, coords3, boostL_apply, boostFun]
    norm_num

/-- The boost, as an isometry of `𝐌³` with trivial translation part. -/
noncomputable def boostIsom : isom 2 := ⟨boostL.toAffineEquiv, boostL_mem⟩

theorem boostIsom_smul (p : Minkowski 2) : boostIsom • p = boostL p := rfl

theorem lorentzScale_boost (u : PenroseSphere 2) :
    lorentzScale (linearPart boostIsom) u = 5 / 4 + 3 / 4 * (u : EuclideanSpace ℝ (Fin 2)) 0 := by
  show (boostL (nullVec u)).1 = _
  simp [boostL_apply, boostFun, nullVec]

theorem isomPenrose_boost (w : PenroseSphere 2 × ℝ) :
    isomPenrose boostIsom w =
      (lorentzSphere (linearPart boostIsom) w.1,
        (lorentzScale (linearPart boostIsom) w.1)⁻¹ * w.2) := by
  have h0 : boostIsom • (0 : Minkowski 2) = 0 := by rw [boostIsom_smul, map_zero]
  simp [isomPenrose, h0, minkB]

/-- `u₀ = (−3/5, 4/5)`. -/
noncomputable def laoBase : PenroseSphere 2 :=
  ⟨!₂[-3 / 5, 4 / 5], by rw [mem_sphere_zero_iff_norm]; exact norm_eq_one_of_fin_two (by norm_num)⟩

/-- The `x`-coordinate of `R_t u₀`. -/
noncomputable def laoX (t : ℝ) : ℝ := (-3 * (1 - t ^ 2) - 8 * t) / (5 * (1 + t ^ 2))

/-- The `y`-coordinate of `R_t u₀`. -/
noncomputable def laoY (t : ℝ) : ℝ := (4 * (1 - t ^ 2) - 6 * t) / (5 * (1 + t ^ 2))

theorem laoX_sq_add_laoY_sq (t : ℝ) : laoX t ^ 2 + laoY t ^ 2 = 1 := by
  have : (1 + t ^ 2) ≠ 0 := by positivity
  simp only [laoX, laoY]; field_simp; ring

/-- `R_t u₀`. -/
noncomputable def laoCurve (t : ℝ) : PenroseSphere 2 :=
  ⟨!₂[laoX t, laoY t], by
    rw [mem_sphere_zero_iff_norm]
    exact norm_eq_one_of_fin_two (by simpa using laoX_sq_add_laoY_sq t)⟩

theorem continuous_laoX : Continuous laoX := by
  unfold laoX; exact Continuous.div (by fun_prop) (by fun_prop) fun t => by positivity

theorem continuous_laoCurve : Continuous laoCurve := by
  have hX := continuous_laoX
  have hY : Continuous laoY := by
    unfold laoY; exact Continuous.div (by fun_prop) (by fun_prop) fun t => by positivity
  refine Continuous.subtype_mk ((PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)) _
  fin_cases i
  · simpa using hX
  · simpa using hY

theorem laoCurve_zero : laoCurve 0 = laoBase := by
  refine Subtype.ext ?_
  ext i; fin_cases i <;> simp [laoCurve, laoBase, laoX, laoY]

/-- The `s`-component of the curve, `s(t) = 4 c(R_t u₀) / c(u₀)`. -/
noncomputable def laoS (t : ℝ) : ℝ := 25 / 4 + 15 / 4 * laoX t

theorem laoCurve_coord_zero (t : ℝ) :
    ((laoCurve t : PenroseSphere 2) : EuclideanSpace ℝ (Fin 2)) 0 = laoX t := by
  simp [laoCurve]

theorem dist_laoBase_laoCurve_sq (t : ℝ) :
    dist laoBase (laoCurve t) ^ 2 = 4 * t ^ 2 / (1 + t ^ 2) := by
  have hq : (1 + t ^ 2) ≠ 0 := by positivity
  rw [Subtype.dist_eq, dist_eq_norm, norm_sq_fin_two]
  simp only [laoBase, laoCurve, PiLp.sub_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  unfold laoX laoY
  field_simp
  ring

/-- The real inequality behind the counterexample, `0 < t < 1/3`. -/
theorem laoucapulse_ineq {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1 / 3) :
    (4 / 5 : ℝ)⁻¹ * (5 / 4 + 3 / 4 * laoX t)⁻¹ * (4 * t ^ 2 / (1 + t ^ 2)) ≤ (4 - laoS t) ^ 2 ∧
      0 < 4 - laoS t := by
  have hq : 0 < 1 + t ^ 2 := by positivity
  set P := 8 + 17 * t ^ 2 - 12 * t with hP_def
  have hP : 0 < P := by nlinarith [sq_nonneg t]
  have hc : 5 / 4 + 3 / 4 * laoX t = P / (10 * (1 + t ^ 2)) := by
    unfold laoX; rw [hP_def]; field_simp; ring
  have hs : 4 - laoS t = 3 * t * (4 - 3 * t) / (2 * (1 + t ^ 2)) := by
    unfold laoS laoX; field_simp; ring
  refine ⟨?_, by rw [hs]; apply div_pos <;> nlinarith⟩
  have hL : (4 / 5 : ℝ)⁻¹ * (5 / 4 + 3 / 4 * laoX t)⁻¹ * (4 * t ^ 2 / (1 + t ^ 2)) =
      50 * t ^ 2 / P := by
    rw [hc]; field_simp; ring
  rw [hL, hs, div_pow, div_le_div_iff₀ hP (by positivity)]
  have h1 : 9 ≤ (4 - 3 * t) ^ 2 := by nlinarith
  have h2 : 4 ≤ P := by nlinarith [sq_nonneg t]
  have h3 : (1 + t ^ 2) ^ 2 ≤ 100 / 81 := by
    have h3a : 1 + t ^ 2 ≤ 10 / 9 := by nlinarith
    calc (1 + t ^ 2) ^ 2 ≤ (10 / 9) ^ 2 := pow_le_pow_left₀ hq.le h3a 2
      _ = 100 / 81 := by norm_num
  have key : 200 * (1 + t ^ 2) ^ 2 ≤ 9 * (4 - 3 * t) ^ 2 * P := by
    nlinarith [mul_le_mul h1 h2 (by norm_num) (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left key (sq_nonneg t)]

end Laoucapulse

open Laoucapulse in
/-- **`bprop:laoucapulse` fails in its metric reading** (`d = 2`): the boost `g = boostIsom` is
expanding on `𝒮` at `u₀` (factor `5/4`), and not expanding on `𝒥⁺ ≅ 𝒮 × ℝ` at `(u₀, 4)`. -/
theorem not_laoucapulseMetricReading_two : ¬ LaoucapulseMetricReading 2 := by
  intro h
  have hc0 : lorentzScale (linearPart boostIsom) laoBase = 4 / 5 := by
    rw [lorentzScale_boost]; simp [laoBase]; norm_num
  have hexp : IsExpandingAt (lorentzSphere (linearPart boostIsom)) laoBase :=
    isExpandingAt_lorentzSphere _ (by rw [hc0]; norm_num)
  obtain ⟨l, hl, hev⟩ := (h boostIsom (by rw [boostIsom_smul, map_zero]) (laoBase, 4)).2 hexp
  have hγc : Continuous fun t : ℝ => (laoCurve t, laoS t) :=
    continuous_laoCurve.prodMk (continuous_const.add (continuous_const.mul continuous_laoX))
  have hγ0 : (laoCurve 0, laoS 0) = (laoBase, (4 : ℝ)) := by
    rw [laoCurve_zero]; simp [laoS, laoX]; norm_num
  have hγ : Tendsto (fun t : ℝ => ((laoBase, (4 : ℝ)), (laoCurve t, laoS t))) (𝓝[>] 0)
      (𝓝 (laoBase, (4 : ℝ)) ×ˢ 𝓝 (laoBase, (4 : ℝ))) := by
    refine tendsto_const_nhds.prodMk ?_
    have := hγc.tendsto 0
    rw [hγ0] at this
    exact this.mono_left nhdsWithin_le_nhds
  obtain ⟨t, hlt, ht⟩ :=
    ((hγ.eventually hev).and (Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 3 by norm_num))).exists
  obtain ⟨ht0, ht1⟩ := ht
  simp only [isomPenrose_boost] at hlt
  have hct : lorentzScale (linearPart boostIsom) (laoCurve t) = 5 / 4 + 3 / 4 * laoX t := by
    rw [lorentzScale_boost, laoCurve_coord_zero]
  have hctpos : 0 < 5 / 4 + 3 / 4 * laoX t := hct ▸ lorentzScale_pos _ _
  obtain ⟨hineq, hpos⟩ := laoucapulse_ineq ht0 ht1
  -- the two images have the same `s`-component, `5`
  have he : (lorentzScale (linearPart boostIsom) laoBase)⁻¹ * 4 =
      (lorentzScale (linearPart boostIsom) (laoCurve t))⁻¹ * laoS t := by
    rw [hc0, hct, laoS, show (25 / 4 : ℝ) + 15 / 4 * laoX t = (5 / 4 + 3 / 4 * laoX t) * 5 by ring,
      ← mul_assoc, inv_mul_cancel₀ hctpos.ne', one_mul]
    norm_num
  rw [Prod.dist_eq, Prod.dist_eq] at hlt
  simp only at hlt
  rw [he, dist_self, max_eq_left dist_nonneg] at hlt
  set D := max (dist laoBase (laoCurve t)) (dist (4 : ℝ) (laoS t))
  have hD : |4 - laoS t| ≤ D := le_max_of_le_right (by rw [Real.dist_eq])
  have hDf : dist (lorentzSphere (linearPart boostIsom) laoBase)
      (lorentzSphere (linearPart boostIsom) (laoCurve t)) ≤ |4 - laoS t| := by
    refine (pow_le_pow_iff_left₀ dist_nonneg (abs_nonneg _) two_ne_zero).1 ?_
    rw [dist_lorentzSphere_sq, dist_laoBase_laoCurve_sq, hc0, hct, sq_abs]
    exact hineq
  have hD0 : 0 < D := (abs_pos.2 hpos.ne').trans_le hD
  nlinarith

end Causal.Flat
