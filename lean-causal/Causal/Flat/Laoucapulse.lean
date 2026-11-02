import Causal.Flat.Penrose
import Causal.Flat.Externals
import Mathlib.Analysis.Normed.Module.Connected

/-!
# `Causal.Flat.Laoucapulse` — Barbot's Prop 4.2 in its strongest true reading

T. Barbot, *Globally hyperbolic flat space-times* (`papers/barbot`, arXiv math/0402257), §4.1.
Line numbers are those of `papers/barbot/legacy/labeled/GHFspace.tex`. **No label is marked.**

* `bprop:laoucapulse` — `GHFspace.tex:855` (Prop 4.2), **partial** (DEC-27: false as printed for
  `n = 3` in the sup-product metric reading, for every euclidean metric `lam·|·|` on `ℝ` — the
  `ℓ²`/geodesic readings by the SCOPE transfer argument, not formalized; the strongest true form is
  proved, **no `sorry`**). For a linear isometry
  `g` and any euclidean metric `lam·|·|` on `ℝ`, the expanding domain `E` of `g` on
  `𝒥⁺ ≅ 𝒮⁺ × ℝ` is **open** and `U × {0} ⊆ E ⊆ δ⁺⁻¹(U)`, `U = {a(g,·) > 1}` the conformal
  expanding domain of `L(g)` on `𝒮⁺` (`laoucapulse_corrected`); on the zero section the printed
  equivalence holds in the metric reading for `d ≥ 2` (`laoucapulse_zeroSection`), with sharp
  rate `a(g,u)` (`expandsAtRate_zeroSection`, `le_penroseFactor_of_expandsAtRate`). The inclusion
  `E ⊆ δ⁺⁻¹(U)` holds for every isometry and every `s` (`one_lt_penroseFactor_of_isExpandingAtWrt`).
  Refuted as printed: for `d = 2` and every `lam > 0` (`not_laoucapulseScaledReading_two`), and for
  `d = 1` in the metric reading of `𝒮` already on the zero section
  (`not_laoucapulseScaledReading_one`). **For `d = 1` (`n = 2`) in the conformal reading the printed
  equality `E = δ⁺⁻¹(U)` holds exactly**, for every isometry and every `s`
  (`laoucapulse_one`, `isExpandingAtWrt_penroseDist_one_iff`): `S⁰` is discrete, so only the fibre
  `s ↦ a s + b` is seen. This is not a closure of the label, which covers every `n`. For `n ≥ 3`
  the printed equality holds in the **volume** (Jacobian) reading, not formalized (SCOPE).
* Consumers. l.1660–1661, the paper's **only** citation of Prop 4.2 (Sullivan's property (i) on
  `𝒥` along `Λ̂ × {0}`, trivial cocycle): `laoucapulse_cover`. `bprop:admlox` — `GHFspace.tex:1230`
  (Prop 4.17, owned by `Flat.Loxodromic`), unmarked: its step l.1254–1267 (the repulsive point
  lifts to `x₀ ∈ 𝒥⁺` with basin `⊇ δ⁺⁻¹(U)`) from the eigenvalue alone, no loxodromy
  (`laoucapulse_repulsive_basin`, `…_of_isRepulsiveFixed`); for linear `γ`, `x₀ = (v₀, 0)` and `γ`
  is expanding there (`laoucapulse_repulsive_linear`).
* Prose [4.J] (l.829–851): `isomPenrose` is a group action (`Laou.isomPenrose_mul`, `…_one`,
  `…_iterate`).

> When we use the identification ${\mathcal J} \approx {\mathcal J}^{+} \approx {\mathcal S}
> \times {\mathbb R}$, the action of an isometry $g(x) = L(g)x + \tau$ is expressed by:
> $g.( v , s ) = ( [L(g)].v , a(g, v)s + b(g, v) )$ […] $a(g, v) = \frac{1}{N(L(g)(v))}$
> (l.830–841)

> Observe also that the factor $\frac{1}{N(L(g)v)}$ is common to the $v$ and $s$ components.
> Hence: (l.849–851)

> Equip ${\mathcal J}^{+} \approx {\mathcal S}^{+} \times {\mathbb R}$ with the product metric
> of the round metric on the sphere ${\mathcal S}^{+}$ and any euclidean metric on $\mathbb R$.
> Let $g$ be a linear isometry of \mink, i.e., admitting a trivial translation part $\tau$. Then,
> the domain in ${\mathcal J}^{+}$ where the action of $g$ is expanding is precisely the preimage
> under $\delta^{+}$ of the domain of ${\mathcal S}^{+}$ where the action of $L(g)$ is expanding.
> (l.857–865)

> Indeed, the property $(i)$ follows from proposition \ref{laoucapulse} and the expanding property
> of $\Gamma$ on $\mathcal S$ (l.1660–1661)

> The bassin of repulsion of $x_{0}$ for $\gamma$ contains some open subset of the form
> $\delta^{-1}(U)$, where $U$ is some open neighborhood of $v_{0}$ in $\mathcal S$. […] Then,
> negative iterates of $x$ under $\gamma$ converge towards $x_{0}$. (l.1260–1267)

**Dimension (kb/0024).** Barbot's `n` is `d + 1`; `𝒮 ≅ S^{d−1}`. **Normalisation**: `Penrose`'s
(`nullVec u = (1, u)`); `a(g, u) = penroseFactor (linearPart g) u = 1/c(L(g), u)`. The
identification is exact: Barbot's `N` is the euclidean norm (l.769–771), his `v ∈ 𝒮⁺` is
`(1, u)/√2` (l.775–783; the printed `x₀ = 1/2` at l.783 is a slip for `1/√2`), and a null vector `w` has `N(w) = √2·|w₀|`, so
`N(L(g)v) = (L(g)(1, u))₀ = lorentzScale (linearPart g) u`. His fibre coordinate `⟨v | p⟩` is
`Penrose`'s `⟨(1, u) | p⟩ / √2`, and his sphere has radius `1/√2` against `1` here: both are
global scalings, immaterial for expansion (scale-invariant) and absorbed by `fibreScale`.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `g` linear (`τ = 0`) | ✓ carried (`g • 0 = 0`) for `U × {0} ⊆ E`; ⚠ weakened for `E ⊆ δ⁺⁻¹(U)` (any `g`) |
| product of the round metric and any euclidean metric on `ℝ` | ⚠ read: sup product of the chordal metric and `lam` times the absolute value, every `lam > 0` (`penroseDist`) |
| "expanding" (undefined) | ⚠ read: `∃ l > 1, l·D ≤ D∘f` near the point (`IsExpandingAtWrt`); on `𝒮`, conformal `a > 1` (`IsConformallyExpandingAt`), equal to the metric reading for `d ≥ 2` |
| `n ≥ 3` (not printed) | ⚠ strengthened, for `laoucapulse_zeroSection` only: `d ≥ 2`; false for `d = 1` |
| 4.17: `γ` loxodromic, `v₀` repulsive | ⚠ weakened: only `L(γ)(1,v₀) = λ(1,v₀)`, `0 < λ < 1` |

## SCOPE (disclosed)

* **Why the printed equality fails** (`Penrose`, `not_laoucapulseMetricReading_two`): off the zero
  section `g.(u, s) = ([L(g)]u, a(u)s)` shears, `∂_u(a s) = s·∂a`, and for large `|s|` a
  direction is contracted even where `a > 1`. `fibreScale` conjugates `lam·|·|` to `|·|` and
  commutes with linear `g` (`isExpandingAtWrt_penroseDist_iff`), so no euclidean metric on `ℝ`
  repairs it. On the zero section the shear vanishes and the factor `a` is common to both
  components (l.849–851): there the rate of expansion is exactly `a(g, u)`.
* **`n = 2`**: `𝒮 = S⁰` is discrete, every self-map is metrically expanding
  (`Laou.isExpandingAt_of_one`), so "expanding on `𝒮⁺`" must be read conformally; the boost
  `Laou.boostIsom1` has `a(g, u₊) = 1/2` and refutes the metric reading at `(u₊, 0)`. In the
  conformal reading the printed equality is true for `n = 2`, for every isometry and every `s`
  (`laoucapulse_one`): near `(u, s)` the sup metric sees only the fibre, mapped by `s ↦ a(u)s + b(u)`.
* **Not formalized**: the Riemannian (`ℓ²`) product and the geodesic round metric. Geodesic and
  chordal distance agree to first order, so a rate `l < a` survives with a rate `> 1`; the `ℓ²`
  combination is not locally `1`-bi-Lipschitz to the sup one, and the zero-section estimate for it
  (same mechanism) is not written. The refutations transfer as `Penrose`'s SCOPE argues.
* **Volume reading (not formalized; closes the printed equality for `n ≥ 3`).** In the product
  Riemannian volume the differential of `g.(u, s) = ([L(g)]u, a(u)s + b(u))` is lower triangular:
  a conformal sphere block of factor `a(g, u)`, the fibre entry `a(g, u)`, and the shear
  `s·da + db` below the diagonal. Its Jacobian is `a(g, u)^d`, independent of `s`, of `lam` and of
  the translation part; the sphere Jacobian of `[L(g)]` is `a(g, u)^{d−1}`. So for `d ≥ 2`
  (`n ≥ 3`), "`g` is volume-expanding at `(u, s)`" ⟺ `a(g, u) > 1` ⟺ "`L(g)` is volume-expanding
  at `u`", and the printed equality `E = δ⁺⁻¹(U)` holds exactly, for every isometry and every `s`
  (as `Penrose`'s SCOPE notes: "the statement holds for volume expansion"). It is not the reading
  l.1660 consumes: Sullivan's property (i) is metric expansion on `𝒮`, whose transfer to
  `Λ̂ × {0}` is `laoucapulse_cover`. Which notion the author intends — metric, Sullivan's
  derivative-norm, or volume — is an open question; the label stays unmarked.
* **Sullivan's round metric** (l.1625–1627, l.1660) is "some fixed round metric on `𝒮` in the
  natural conformal class", not necessarily the `N`-normalised one of Prop 4.2. Reading "round" as
  a Möbius image of the standard metric (automatic by Liouville for `n ≥ 4`; a reading for
  `n = 3`, where `𝒮 = S¹` and every metric of length `2π` is round), such a metric is
  the pull-back of the `N`-normalised one by `[h]`, `h ∈ SO₀(1, d)` (a change of time axis); its
  conformal factor of `γ` at `v` is that of `h γ h⁻¹` at `[h]v`, and `h γ h⁻¹` is linear when `γ`
  is. So `laoucapulse_cover`, applied to the `h γ_i h⁻¹` and to `[h](Λ̂)`, gives the transported
  statement; that conjugation is stated here, not formalized.
* The basin is local (a ball, from the chordal identity); `Flat.Loxodromic` proves the global
  basin for loxodromic `γ` (`tendsto_isomPenrose_inv_pow`, not imported: concurrent file).
* Non-vacuity: `boostIsom_isExpandingAtWrt_laoBase_zero` (`d = 2`, `a = 5/4`).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Barbot campaign,
WP-35c-Laoucapulse.
-/

namespace Causal.Flat

open Set TopologicalSpace Topology Filter Metric

variable {d : ℕ}

/-! ### Expansion with respect to a distance function -/

/-- `f` **expands at `x` with rate `l`** for the distance function `D`: `l · D y z ≤ D (f y) (f z)`
for all `y, z` near `x`. -/
def ExpandsAtRate {X : Type*} [TopologicalSpace X] (D : X → X → ℝ) (f : X → X) (x : X) (l : ℝ) :
    Prop :=
  ∀ᶠ p in 𝓝 x ×ˢ 𝓝 x, l * D p.1 p.2 ≤ D (f p.1) (f p.2)

/-- `f` is **expanding at `x`** for `D`: it expands at `x` with some rate `l > 1`. For `D = dist`
this is `IsExpandingAt` (`isExpandingAtWrt_dist_iff`). -/
def IsExpandingAtWrt {X : Type*} [TopologicalSpace X] (D : X → X → ℝ) (f : X → X) (x : X) :
    Prop :=
  ∃ l > 1, ExpandsAtRate D f x l

theorem isExpandingAtWrt_dist_iff {X : Type*} [PseudoMetricSpace X] (f : X → X) (x : X) :
    IsExpandingAtWrt dist f x ↔ IsExpandingAt f x := Iff.rfl

/-- **The expanding domain is open**, for any distance function. -/
theorem isOpen_setOf_isExpandingAtWrt {X : Type*} [TopologicalSpace X] (D : X → X → ℝ)
    (f : X → X) : IsOpen {x | IsExpandingAtWrt D f x} := by
  refine isOpen_iff_mem_nhds.2 fun x ⟨l, hl, h⟩ => ?_
  rw [ExpandsAtRate, ← nhds_prod_eq] at h
  have h2 := ((continuous_id.prodMk continuous_id).tendsto x).eventually h.eventually_nhds
  filter_upwards [h2] with y hy
  exact ⟨l, hl, by rw [ExpandsAtRate, ← nhds_prod_eq]; exact hy⟩

/-! ### The metrics of `𝒥⁺ ≅ 𝒮 × ℝ` and the conformal factor -/

/-- The distance of `𝒥⁺ ≅ 𝒮 × ℝ` used here: the sup product of the chordal metric of `𝒮` and of
`lam · |·|` on `ℝ` (Barbot's "any euclidean metric on `ℝ`", l.858–859, is `lam · |·|`). -/
noncomputable def penroseDist (lam : ℝ) (w w' : PenroseSphere d × ℝ) : ℝ :=
  max (dist w.1 w'.1) (lam * |w.2 - w'.2|)

theorem penroseDist_one (w w' : PenroseSphere d × ℝ) : penroseDist 1 w w' = dist w w' := by
  rw [penroseDist, Prod.dist_eq, Real.dist_eq, one_mul]

/-- Barbot's **`a(g, v) = 1/N(L(g)v)`** (l.841), in the time normalisation of `Penrose`: the
conformal factor of `[A]` at `u` (`dist_lorentzSphere_sq`), and the factor of `g` on the fibre
`ℝ` of `𝒥⁺` over `u`. -/
noncomputable def penroseFactor (A : lorentz d) (u : PenroseSphere d) : ℝ := (lorentzScale A u)⁻¹

theorem penroseFactor_pos (A : lorentz d) (u : PenroseSphere d) : 0 < penroseFactor A u :=
  inv_pos.2 (lorentzScale_pos A u)

theorem continuous_penroseFactor (A : lorentz d) : Continuous (penroseFactor A) :=
  (continuous_lorentzScale A).inv₀ fun v => (lorentzScale_pos A v).ne'

theorem dist_lorentzSphere_sq' (A : lorentz d) (u u' : PenroseSphere d) :
    dist (lorentzSphere A u) (lorentzSphere A u') ^ 2 =
      penroseFactor A u * penroseFactor A u' * dist u u' ^ 2 :=
  dist_lorentzSphere_sq A u u'

/-- **The conformal reading of "the action of `L(g)` on `𝒮⁺` is expanding at `u`"**: its
conformal factor `a(g, u)` exceeds `1`. For `d ≥ 2` it is the metric reading
(`isExpandingAt_lorentzSphere_iff`); for `d = 1` (`𝒮 = S⁰`) the metric reading is vacuous. -/
def IsConformallyExpandingAt (A : lorentz d) (u : PenroseSphere d) : Prop :=
  1 < penroseFactor A u

theorem isomPenrose_fst (g : isom d) (w : PenroseSphere d × ℝ) :
    (isomPenrose g w).1 = lorentzSphere (linearPart g) w.1 := rfl

theorem isomPenrose_snd (g : isom d) (w : PenroseSphere d × ℝ) :
    (isomPenrose g w).2 = penroseFactor (linearPart g) w.1 * w.2 +
      minkB (nullVec (lorentzSphere (linearPart g) w.1)) (g • (0 : Minkowski d)) := rfl

/-- For a **linear** isometry (`τ = 0`), `g.(u, s) = ([L(g)]u, a(g, u) s)` (l.834–844). -/
theorem isomPenrose_of_smul_zero {g : isom d} (hg : g • (0 : Minkowski d) = 0)
    (w : PenroseSphere d × ℝ) :
    isomPenrose g w = (lorentzSphere (linearPart g) w.1, penroseFactor (linearPart g) w.1 * w.2) := by
  refine Prod.ext rfl ?_
  rw [isomPenrose_snd, hg]
  simp [minkB]

/-! ### The inclusion `E(g) ⊆ δ⁺⁻¹(U(g))`, for every isometry and every `s` -/

/-- **The fibre bounds the rate**: if `g` (any isometry, any translation part) expands at
`w ∈ 𝒥⁺` with rate `l`, then `l ≤ a(g, w.1)` — the fibre `ℝ` over `w.1` is mapped affinely with
factor `a(g, w.1)`. -/
theorem le_penroseFactor_of_expandsAtRate (g : isom d) {lam : ℝ} (hlam : 0 < lam)
    {w : PenroseSphere d × ℝ} {l : ℝ} (h : ExpandsAtRate (penroseDist lam) (isomPenrose g) w l) :
    l ≤ penroseFactor (linearPart g) w.1 := by
  have hc : Continuous fun t : ℝ => ((w.1, w.2 + t) : PenroseSphere d × ℝ) := by fun_prop
  have hT : Tendsto (fun t : ℝ => (w, ((w.1, w.2 + t) : PenroseSphere d × ℝ))) (𝓝[>] 0)
      (𝓝 w ×ˢ 𝓝 w) := by
    refine tendsto_const_nhds.prodMk ?_
    have := hc.tendsto 0
    simp only [add_zero, Prod.mk.eta] at this
    exact this.mono_left nhdsWithin_le_nhds
  obtain ⟨t, ht, htpos⟩ := ((hT.eventually h).and self_mem_nhdsWithin).exists
  have htpos' : (0 : ℝ) < t := htpos
  simp only [penroseDist, isomPenrose_fst, isomPenrose_snd, dist_self] at ht
  have e1 : |w.2 - (w.2 + t)| = t := by rw [sub_add_cancel_left, abs_neg, abs_of_pos htpos']
  set a := penroseFactor (linearPart g) w.1
  have ha := penroseFactor_pos (linearPart g) w.1
  have e2 : |a * w.2 + minkB (nullVec (lorentzSphere (linearPart g) w.1)) (g • (0 : Minkowski d)) -
      (a * (w.2 + t) + minkB (nullVec (lorentzSphere (linearPart g) w.1)) (g • (0 : Minkowski d)))|
        = a * t := by
    rw [show a * w.2 + minkB (nullVec (lorentzSphere (linearPart g) w.1)) (g • (0 : Minkowski d)) -
      (a * (w.2 + t) + minkB (nullVec (lorentzSphere (linearPart g) w.1)) (g • (0 : Minkowski d)))
        = -(a * t) by ring, abs_neg, abs_of_pos (mul_pos ha htpos')]
  rw [e1, e2, max_eq_right (by positivity), max_eq_right (by positivity)] at ht
  have hlt : 0 < lam * t := mul_pos hlam htpos'
  nlinarith

/-- **`E(g) ⊆ δ⁺⁻¹ {a(g, ·) > 1}`**: wherever an isometry (any translation part) is expanding on
`𝒥⁺`, the conformal factor of `L(g)` exceeds `1` at the direction. -/
theorem one_lt_penroseFactor_of_isExpandingAtWrt (g : isom d) {lam : ℝ} (hlam : 0 < lam)
    {w : PenroseSphere d × ℝ} (h : IsExpandingAtWrt (penroseDist lam) (isomPenrose g) w) :
    IsConformallyExpandingAt (linearPart g) w.1 := by
  obtain ⟨l, hl, hr⟩ := h
  exact hl.trans_le (le_penroseFactor_of_expandsAtRate g hlam hr)

/-- **The inclusion half of `bprop:laoucapulse`, in its printed metric reading, for every
isometry**: if `g` is expanding at `w ∈ 𝒥⁺` then `L(g)` is (metrically) expanding at `δ⁺(w)`. -/
theorem isExpandingAt_lorentzSphere_of_isExpandingAtWrt (g : isom d) {lam : ℝ} (hlam : 0 < lam)
    {w : PenroseSphere d × ℝ} (h : IsExpandingAtWrt (penroseDist lam) (isomPenrose g) w) :
    IsExpandingAt (lorentzSphere (linearPart g)) w.1 :=
  isExpandingAt_lorentzSphere _ (one_lt_penroseFactor_of_isExpandingAtWrt g hlam h)

/-! ### The zero section: `g` expands at `(u, 0)` with every rate below `a(g, u)` -/

theorem nullVec_sub_nullVec (u u' : PenroseSphere d) :
    nullVec u - nullVec u' = ((0 : ℝ), (u : EuclideanSpace ℝ (Fin d)) - u') := by
  refine Prod.ext ?_ rfl
  simp [nullVec]

/-- `c(A, ·)` is Lipschitz on `𝒮`, with constant `‖A‖`. -/
theorem abs_lorentzScale_sub_le (A : lorentz d) (u u' : PenroseSphere d) :
    |lorentzScale A u - lorentzScale A u'| ≤
      ‖linToCLM (A : Minkowski d ≃ₗ[ℝ] Minkowski d)‖ * dist u u' := by
  have e : lorentzScale A u - lorentzScale A u' =
      ((A : Minkowski d ≃ₗ[ℝ] Minkowski d) (nullVec u - nullVec u')).1 := by
    rw [map_sub]; rfl
  rw [e, ← Real.norm_eq_abs]
  refine (norm_fst_le _).trans ?_
  rw [← linToCLM_apply]
  refine ((linToCLM (A : Minkowski d ≃ₗ[ℝ] Minkowski d)).le_opNorm _).trans_eq ?_
  rw [nullVec_sub_nullVec, Prod.norm_mk, norm_zero, max_eq_right (norm_nonneg _), Subtype.dist_eq,
    dist_eq_norm]

/-- The conformal factor `a(A, ·)` on `𝒮` against `c(A, ·)`:
`a u − a u' = a u · a u' · (c u' − c u)`. -/
theorem penroseFactor_sub (A : lorentz d) (u u' : PenroseSphere d) :
    penroseFactor A u - penroseFactor A u' =
      penroseFactor A u * penroseFactor A u' * (lorentzScale A u' - lorentzScale A u) := by
  have h1 := (lorentzScale_pos A u).ne'
  have h2 := (lorentzScale_pos A u').ne'
  simp only [penroseFactor]
  field_simp

/-- **The key estimate on the zero section.** For a linear isometry `g` (`τ = 0`) and every
`l < a(g, u₀)`, `g` expands at `(u₀, 0) ∈ 𝒥⁺` with rate `l`, for every `lam > 0`. The mechanism:
`g.(u, s) = ([L(g)]u, a(u) s)`; the sphere component expands by `a`, and the `s`-component by `a`
up to the shear `(a(u) − a(u')) s'`, which is small against `dist u u'` when `|s'|` is. -/
theorem expandsAtRate_zeroSection {g : isom d} (hg : g • (0 : Minkowski d) = 0) {lam : ℝ}
    (hlam : 0 < lam) (u₀ : PenroseSphere d) {l : ℝ} (hl : l < penroseFactor (linearPart g) u₀) :
    ExpandsAtRate (penroseDist lam) (isomPenrose g) (u₀, 0) l := by
  set A := linearPart g
  set a := penroseFactor A
  have ha0 : 0 < a u₀ := penroseFactor_pos A u₀
  set m := (max l 0 + a u₀) / 2 with hm_def
  have hlm : l < m := by have := le_max_left l 0; have := max_lt hl ha0; simp only [hm_def]; linarith
  have hm0 : 0 < m := by have := le_max_right l 0; simp only [hm_def]; linarith
  have hma : m < a u₀ := by have := max_lt hl ha0; simp only [hm_def]; linarith
  set M := a u₀ + 1
  have hca : Continuous a := continuous_penroseFactor A
  have N1 : ∀ᶠ u in 𝓝 u₀, m < a u := hca.continuousAt.eventually (lt_mem_nhds hma)
  have N2 : ∀ᶠ u in 𝓝 u₀, a u < M := hca.continuousAt.eventually (gt_mem_nhds (by linarith))
  set K := M * M * ‖linToCLM (A : Minkowski d ≃ₗ[ℝ] Minkowski d)‖
  have hM0 : 0 < M := by linarith
  have hK0 : 0 ≤ K := by positivity
  set ε := (m - l) / (lam * K + 1)
  have hden : 0 < lam * K + 1 := by positivity
  have hε : 0 < ε := div_pos (by linarith) hden
  have hεK : lam * K * ε ≤ m - l := by
    have : lam * K * ε = (m - l) * (lam * K / (lam * K + 1)) := by
      simp only [ε]; field_simp
    rw [this]
    have : lam * K / (lam * K + 1) ≤ 1 := (div_le_one hden).2 (by linarith)
    nlinarith
  have hS : {u | m < a u ∧ a u < M} ×ˢ Ioo (-ε) ε ∈ 𝓝 ((u₀, 0) : PenroseSphere d × ℝ) :=
    prod_mem_nhds (N1.and N2) (Ioo_mem_nhds (by linarith) hε)
  filter_upwards [prod_mem_prod hS hS]
  rintro ⟨⟨u, s⟩, ⟨u', s'⟩⟩ ⟨⟨⟨hu1, hu2⟩, hs⟩, ⟨⟨hu1', hu2'⟩, hs'⟩⟩
  simp only [mem_Ioo] at hs hs'
  simp only [isomPenrose_of_smul_zero hg, penroseDist]
  change l * max (dist u u') (lam * |s - s'|) ≤
    max (dist (lorentzSphere A u) (lorentzSphere A u')) (lam * |a u * s - a u' * s'|)
  set c := dist u u'
  set σ := |s - s'|
  have hc0 : 0 ≤ c := dist_nonneg
  have hσ0 : 0 ≤ σ := abs_nonneg _
  -- the sphere component
  have hc' : m * c ≤ dist (lorentzSphere A u) (lorentzSphere A u') := by
    refine (pow_le_pow_iff_left₀ (by positivity) dist_nonneg two_ne_zero).1 ?_
    rw [dist_lorentzSphere_sq', mul_pow]
    have : m ^ 2 ≤ a u * a u' := by rw [sq]; exact mul_le_mul hu1.le hu1'.le hm0.le (by linarith)
    exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
  -- the Lipschitz bound on `a`
  have hlip : |a u - a u'| ≤ K * c := by
    rw [penroseFactor_sub, abs_mul, abs_of_pos (mul_pos (penroseFactor_pos A u)
      (penroseFactor_pos A u')), abs_sub_comm]
    have h1 := abs_lorentzScale_sub_le A u u'
    have h2 : a u * a u' ≤ M * M :=
      mul_le_mul hu2.le hu2'.le (penroseFactor_pos A u').le hM0.le
    calc a u * a u' * |lorentzScale A u - lorentzScale A u'|
        ≤ M * M * (‖linToCLM (A : Minkowski d ≃ₗ[ℝ] Minkowski d)‖ * c) :=
          mul_le_mul h2 h1 (abs_nonneg _) (by positivity)
      _ = K * c := by simp only [K]; ring
  -- the fibre component
  have hσ' : m * σ - K * c * ε ≤ |a u * s - a u' * s'| := by
    have e : a u * s - a u' * s' = a u * (s - s') + (a u - a u') * s' := by ring
    have h1 := abs_sub_abs_le_abs_sub (a u * (s - s')) (-((a u - a u') * s'))
    rw [sub_neg_eq_add, ← e, abs_neg, abs_mul, abs_of_pos (penroseFactor_pos A u), abs_mul] at h1
    have hs'' : |s'| ≤ ε := abs_le.2 ⟨hs'.1.le, hs'.2.le⟩
    have h2 : |a u - a u'| * |s'| ≤ K * c * ε :=
      mul_le_mul hlip hs'' (abs_nonneg _) (by positivity)
    have h3 : m * σ ≤ a u * σ := mul_le_mul_of_nonneg_right hu1.le hσ0
    linarith
  rcases le_total (lam * σ) c with hcase | hcase
  · rw [max_eq_left hcase]
    refine le_trans ?_ (le_max_left _ _)
    nlinarith
  · rw [max_eq_right hcase]
    refine le_trans ?_ (le_max_right _ _)
    have h4 : lam * K * ε * c ≤ lam * K * ε * (lam * σ) :=
      mul_le_mul_of_nonneg_left hcase (by positivity)
    have h5 : (m - lam * K * ε) * (lam * σ) ≥ l * (lam * σ) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    nlinarith

/-- **The zero section, exactly**: a linear isometry is expanding at `(u, 0) ∈ 𝒥⁺` iff the
conformal factor `a(g, u)` exceeds `1`, for every `lam > 0`. -/
theorem isExpandingAtWrt_zeroSection_iff {g : isom d} (hg : g • (0 : Minkowski d) = 0) {lam : ℝ}
    (hlam : 0 < lam) (u : PenroseSphere d) :
    IsExpandingAtWrt (penroseDist lam) (isomPenrose g) (u, 0) ↔
      IsConformallyExpandingAt (linearPart g) u := by
  refine ⟨fun h => one_lt_penroseFactor_of_isExpandingAtWrt g hlam h, fun h => ?_⟩
  refine ⟨(1 + penroseFactor (linearPart g) u) / 2, ?_, expandsAtRate_zeroSection hg hlam u ?_⟩
  · have : 1 < penroseFactor (linearPart g) u := h
    linarith
  · have : 1 < penroseFactor (linearPart g) u := h
    linarith

/-! ### The sphere: metric and conformal readings agree for `d ≥ 2` -/

/-- For `d ≥ 2`, no point of `𝒮 = S^{d−1}` is isolated (the sphere is connected and has `±u`). -/
theorem nhdsNE_penroseSphere_neBot (hd : 2 ≤ d) (u : PenroseSphere d) : NeBot (𝓝[≠] u) := by
  have hr : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin d)) :=
    Module.one_lt_rank_of_one_lt_finrank (by rw [finrank_euclideanSpace_fin]; omega)
  have : PreconnectedSpace (PenroseSphere d) :=
    Subtype.preconnectedSpace (isPreconnected_sphere hr 0 1)
  rw [neBot_iff]
  intro h
  have ho : IsOpen ({u} : Set (PenroseSphere d)) := (isOpen_singleton_iff_punctured_nhds u).2 h
  have hU := (IsClopen.eq_univ ⟨isClosed_singleton, ho⟩ (singleton_nonempty u))
  have hneg : -(u : EuclideanSpace ℝ (Fin d)) ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_neg, norm_penroseSphere]
  have hm : (⟨_, hneg⟩ : PenroseSphere d) ∈ ({u} : Set (PenroseSphere d)) := hU ▸ mem_univ _
  have he : -(u : EuclideanSpace ℝ (Fin d)) = u := congrArg Subtype.val hm
  have h0 : (u : EuclideanSpace ℝ (Fin d)) = 0 := by
    have : (2 : ℝ) • (u : EuclideanSpace ℝ (Fin d)) = 0 := by
      rw [two_smul]; nth_rewrite 1 [← he]; exact neg_add_cancel _
    exact (smul_eq_zero.1 this).resolve_left two_ne_zero
  have := norm_penroseSphere u
  rw [h0, norm_zero] at this
  exact zero_ne_one this

/-- For `d ≥ 2`, a rate of expansion of `[A]` on `𝒮` at `u` is at most the conformal factor. -/
theorem le_penroseFactor_of_sphere_rate (hd : 2 ≤ d) (A : lorentz d) {u : PenroseSphere d}
    {l : ℝ} (hl : 0 < l) (h : ExpandsAtRate dist (lorentzSphere A) u l) :
    l ≤ penroseFactor A u := by
  haveI := nhdsNE_penroseSphere_neBot hd u
  have hT : Tendsto (fun u' : PenroseSphere d => (u, u')) (𝓝[≠] u) (𝓝 u ×ˢ 𝓝 u) :=
    tendsto_const_nhds.prodMk nhdsWithin_le_nhds
  have hev : ∀ᶠ u' in 𝓝[≠] u, l ^ 2 ≤ penroseFactor A u * penroseFactor A u' := by
    filter_upwards [hT.eventually h, self_mem_nhdsWithin] with u' h1 (h2 : u' ≠ u)
    have hpos : 0 < dist u u' := dist_pos.2 (Ne.symm h2)
    have h3 : (l * dist u u') ^ 2 ≤ dist (lorentzSphere A u) (lorentzSphere A u') ^ 2 :=
      pow_le_pow_left₀ (by positivity) h1 2
    rw [dist_lorentzSphere_sq', mul_pow] at h3
    exact le_of_mul_le_mul_right h3 (by positivity)
  have hlim : Tendsto (fun u' => penroseFactor A u * penroseFactor A u') (𝓝[≠] u)
      (𝓝 (penroseFactor A u * penroseFactor A u)) :=
    tendsto_const_nhds.mul ((continuous_penroseFactor A).continuousAt.mono_left nhdsWithin_le_nhds)
  have h2 : l ^ 2 ≤ penroseFactor A u ^ 2 := by rw [sq (penroseFactor A u)]; exact ge_of_tendsto hlim hev
  exact (pow_le_pow_iff_left₀ hl.le (penroseFactor_pos A u).le two_ne_zero).1 h2

/-- **For `d ≥ 2` (Barbot's `n ≥ 3`), the metric and conformal readings of "the action of `L(g)`
on `𝒮⁺` is expanding at `u`" agree.** -/
theorem isExpandingAt_lorentzSphere_iff (hd : 2 ≤ d) (A : lorentz d) (u : PenroseSphere d) :
    IsExpandingAt (lorentzSphere A) u ↔ IsConformallyExpandingAt A u := by
  refine ⟨fun ⟨l, hl, h⟩ => hl.trans_le (le_penroseFactor_of_sphere_rate hd A (by linarith) h),
    fun h => isExpandingAt_lorentzSphere A h⟩

/-! ### Rescaling the fibre: the choice of the euclidean metric on `ℝ` is immaterial -/

/-- `(u, s) ↦ (u, lam s)`. -/
noncomputable def fibreScale (lam : ℝ) (hlam : 0 < lam) : PenroseSphere d × ℝ ≃ₜ PenroseSphere d × ℝ :=
  (Homeomorph.refl (PenroseSphere d)).prodCongr (Homeomorph.mulLeft₀ lam hlam.ne')

theorem fibreScale_apply (lam : ℝ) (hlam : 0 < lam) (w : PenroseSphere d × ℝ) :
    fibreScale lam hlam w = (w.1, lam * w.2) := rfl

theorem penroseDist_eq_dist_fibreScale {lam : ℝ} (hlam : 0 < lam) (w w' : PenroseSphere d × ℝ) :
    penroseDist lam w w' = dist (fibreScale lam hlam w) (fibreScale lam hlam w') := by
  rw [fibreScale_apply, fibreScale_apply, Prod.dist_eq, Real.dist_eq, penroseDist,
    ← mul_sub, abs_mul, abs_of_pos hlam]

theorem isomPenrose_fibreScale {g : isom d} (hg : g • (0 : Minkowski d) = 0) {lam : ℝ}
    (hlam : 0 < lam) (w : PenroseSphere d × ℝ) :
    isomPenrose g (fibreScale lam hlam w) = fibreScale lam hlam (isomPenrose g w) := by
  rw [isomPenrose_of_smul_zero hg, isomPenrose_of_smul_zero hg, fibreScale_apply, fibreScale_apply]
  simp only [Prod.mk.injEq, true_and]
  ring

/-- **The fibre scale is immaterial for a linear isometry**: expansion at `(u, s)` for the metric
with `lam · |·|` on `ℝ` is expansion at `(u, lam s)` for the metric with `|·|`. -/
theorem expandsAtRate_penroseDist_iff {g : isom d} (hg : g • (0 : Minkowski d) = 0) {lam : ℝ}
    (hlam : 0 < lam) (w : PenroseSphere d × ℝ) (l : ℝ) :
    ExpandsAtRate (penroseDist lam) (isomPenrose g) w l ↔
      ExpandsAtRate dist (isomPenrose g) (fibreScale lam hlam w) l := by
  set σ := fibreScale (d := d) lam hlam
  rw [ExpandsAtRate, ExpandsAtRate, ← σ.map_nhds_eq, prod_map_map_eq, eventually_map]
  simp only [penroseDist_eq_dist_fibreScale hlam, ← isomPenrose_fibreScale hg hlam]
  rfl

theorem isExpandingAtWrt_penroseDist_iff {g : isom d} (hg : g • (0 : Minkowski d) = 0) {lam : ℝ}
    (hlam : 0 < lam) (w : PenroseSphere d × ℝ) :
    IsExpandingAtWrt (penroseDist lam) (isomPenrose g) w ↔
      IsExpandingAt (isomPenrose g) (w.1, lam * w.2) := by
  simp only [IsExpandingAtWrt, expandsAtRate_penroseDist_iff hg hlam, fibreScale_apply]
  rfl

/-- `bprop:laoucapulse` (l.854–866) **in the metric reading, with the fibre metric `lam · |·|`**
("any euclidean metric on `ℝ`", l.858–859), kept as a `Prop`. Refuted for `d = 2` and **every**
`lam > 0` by `not_laoucapulseScaledReading_two`. -/
def LaoucapulseScaledReading (d : ℕ) (lam : ℝ) : Prop :=
  ∀ g : isom d, g • (0 : Minkowski d) = 0 → ∀ w : PenroseSphere d × ℝ,
    IsExpandingAtWrt (penroseDist lam) (isomPenrose g) w ↔
      IsExpandingAt (lorentzSphere (linearPart g)) w.1

/-- **The printed statement fails for every euclidean metric on `ℝ`** (`d = 2`, Barbot's `n = 3`):
the rescaling transports `Penrose`'s counterexample at `(u₀, 4)` to `(u₀, 4/lam)`. -/
theorem not_laoucapulseScaledReading_two {lam : ℝ} (hlam : 0 < lam) :
    ¬ LaoucapulseScaledReading 2 lam := by
  intro h
  refine not_laoucapulseMetricReading_two fun g hg w => ?_
  have := h g hg (w.1, w.2 / lam)
  rw [isExpandingAtWrt_penroseDist_iff hg hlam, mul_div_cancel₀ _ hlam.ne'] at this
  exact this

open Laoucapulse in
/-- **Non-vacuity (`d = 2`)**: `Penrose`'s boost, whose factor at `u₀ = (−3/5, 4/5)` is `5/4`, is
expanding at `(u₀, 0)` for every `lam` — while it is not expanding at `(u₀, 4)`
(`not_laoucapulseMetricReading_two`). -/
theorem boostIsom_isExpandingAtWrt_laoBase_zero {lam : ℝ} (hlam : 0 < lam) :
    IsExpandingAtWrt (penroseDist lam) (isomPenrose Laoucapulse.boostIsom) (laoBase, 0) := by
  have hc0 : lorentzScale (linearPart Laoucapulse.boostIsom) laoBase = 4 / 5 := by
    rw [lorentzScale_boost]; simp [laoBase]; norm_num
  refine (isExpandingAtWrt_zeroSection_iff (by rw [Laoucapulse.boostIsom_smul, map_zero]) hlam laoBase).2 ?_
  rw [IsConformallyExpandingAt, penroseFactor, hc0]
  norm_num

/-! ### `bprop:laoucapulse`, corrected -/

/-- **`bprop:laoucapulse` (Prop 4.2), corrected** (DEC-27's rule). For a linear isometry `g` of
`𝐌ⁿ` and any euclidean metric `lam · |·|` on `ℝ`, let `E` be the domain of `𝒥⁺ ≅ 𝒮 × ℝ` where `g`
is (metrically) expanding and `U = {u | a(g, u) > 1}` the domain of `𝒮` where `L(g)` is
(conformally) expanding. Then `E` is open and

  `U × {0} ⊆ E ⊆ δ⁺⁻¹(U)`,

so `E` meets the zero section exactly in `U × {0}` and contains an open neighbourhood of it; for
`d ≥ 2`, `U` is also the metric expanding domain of `[L(g)]`. The printed equality `E = δ⁺⁻¹(U)`
is false (`not_laoucapulseScaledReading_two`). -/
theorem laoucapulse_corrected {g : isom d} (hg : g • (0 : Minkowski d) = 0) {lam : ℝ}
    (hlam : 0 < lam) :
    IsOpen {w | IsExpandingAtWrt (penroseDist lam) (isomPenrose g) w} ∧
      {u | IsConformallyExpandingAt (linearPart g) u} ×ˢ {(0 : ℝ)} ⊆
        {w | IsExpandingAtWrt (penroseDist lam) (isomPenrose g) w} ∧
      {w | IsExpandingAtWrt (penroseDist lam) (isomPenrose g) w} ⊆
        Prod.fst ⁻¹' {u | IsConformallyExpandingAt (linearPart g) u} ∧
      (2 ≤ d → {u | IsConformallyExpandingAt (linearPart g) u} =
        {u | IsExpandingAt (lorentzSphere (linearPart g)) u}) := by
  refine ⟨isOpen_setOf_isExpandingAtWrt _ _, ?_, fun w hw =>
    one_lt_penroseFactor_of_isExpandingAtWrt g hlam hw, fun hd => ?_⟩
  · rintro ⟨u, s⟩ ⟨hu, hs⟩
    rw [mem_singleton_iff] at hs
    subst hs
    exact (isExpandingAtWrt_zeroSection_iff hg hlam u).2 hu
  · ext u
    exact (isExpandingAt_lorentzSphere_iff hd _ u).symm

/-- **`bprop:laoucapulse` on the zero section, in the printed metric reading** (`d ≥ 2`): a linear
isometry is expanding at `(u, 0) ∈ 𝒥⁺` iff `[L(g)]` is expanding at `u ∈ 𝒮`. -/
theorem laoucapulse_zeroSection (hd : 2 ≤ d) {g : isom d} (hg : g • (0 : Minkowski d) = 0)
    {lam : ℝ} (hlam : 0 < lam) (u : PenroseSphere d) :
    IsExpandingAtWrt (penroseDist lam) (isomPenrose g) (u, 0) ↔
      IsExpandingAt (lorentzSphere (linearPart g)) u :=
  (isExpandingAtWrt_zeroSection_iff hg hlam u).trans (isExpandingAt_lorentzSphere_iff hd _ u).symm

/-- **What l.1660–1661 takes from Prop 4.2**: Sullivan's property (i) transfers from `𝒮` to `𝒥`
along the zero section. If the conformal expanding domains `U_i` of linear isometries `γ_i` cover
`Λ̂ ⊆ 𝒮`, then the (open) expanding domains `E_i` of the `γ_i` on `𝒥⁺` cover `Λ̂ × {0}`. -/
theorem laoucapulse_cover {ι : Type*} (γ : ι → isom d) (hγ : ∀ i, γ i • (0 : Minkowski d) = 0)
    {lam : ℝ} (hlam : 0 < lam) {Λh : Set (PenroseSphere d)}
    (hcov : Λh ⊆ ⋃ i, {u | IsConformallyExpandingAt (linearPart (γ i)) u}) :
    IsOpen (⋃ i, {w | IsExpandingAtWrt (penroseDist lam) (isomPenrose (γ i)) w}) ∧
      Λh ×ˢ {(0 : ℝ)} ⊆ ⋃ i, {w | IsExpandingAtWrt (penroseDist lam) (isomPenrose (γ i)) w} := by
  refine ⟨isOpen_iUnion fun i => isOpen_setOf_isExpandingAtWrt _ _, ?_⟩
  rintro ⟨u, s⟩ ⟨hu, hs⟩
  rw [mem_singleton_iff] at hs
  subst hs
  obtain ⟨i, hi⟩ := mem_iUnion.1 (hcov hu)
  exact mem_iUnion.2 ⟨i, (laoucapulse_corrected (hγ i) hlam).2.1 ⟨hi, rfl⟩⟩

/-! ### `isomPenrose` is an action -/

namespace Laou

theorem image_lightHyperplane (g : isom d) (w : PenroseSphere d × ℝ) :
    (fun p => g • p) '' lightHyperplane w.1 w.2 =
      lightHyperplane (isomPenrose g w).1 (isomPenrose g w).2 := by
  rw [← isom_preimage_lightHyperplane g w, image_preimage_eq _ (MulAction.surjective g)]

theorem isomPenrose_mul (g h : isom d) (w : PenroseSphere d × ℝ) :
    isomPenrose (g * h) w = isomPenrose g (isomPenrose h w) := by
  have e : lightHyperplane (isomPenrose (g * h) w).1 (isomPenrose (g * h) w).2 =
      lightHyperplane (isomPenrose g (isomPenrose h w)).1 (isomPenrose g (isomPenrose h w)).2 := by
    rw [← image_lightHyperplane, ← image_lightHyperplane, ← image_lightHyperplane, image_image]
    simp only [mul_smul]
  obtain ⟨h1, h2⟩ := lightHyperplane_injective e
  exact Prod.ext h1 h2

theorem isomPenrose_one (w : PenroseSphere d × ℝ) : isomPenrose 1 w = w := by
  have e : lightHyperplane (isomPenrose 1 w).1 (isomPenrose 1 w).2 = lightHyperplane w.1 w.2 := by
    rw [← image_lightHyperplane]
    simp only [one_smul, image_id']
  obtain ⟨h1, h2⟩ := lightHyperplane_injective e
  exact Prod.ext h1 h2

theorem isomPenrose_inv_apply (g : isom d) (w : PenroseSphere d × ℝ) :
    isomPenrose g⁻¹ (isomPenrose g w) = w := by
  rw [← isomPenrose_mul, inv_mul_cancel, isomPenrose_one]

theorem isomPenrose_apply_inv (g : isom d) (w : PenroseSphere d × ℝ) :
    isomPenrose g (isomPenrose g⁻¹ w) = w := by
  rw [← isomPenrose_mul, mul_inv_cancel, isomPenrose_one]

/-- The iterates of the action are the action of the powers. -/
theorem isomPenrose_iterate (g : isom d) (n : ℕ) :
    (isomPenrose g)^[n] = isomPenrose (g ^ n) := by
  induction n with
  | zero => funext w; simp [isomPenrose_one]
  | succ n ih =>
    funext w
    rw [Function.iterate_succ_apply', ih, pow_succ', isomPenrose_mul]

theorem iterate_fst (g : isom d) (n : ℕ) (w : PenroseSphere d × ℝ) :
    ((isomPenrose g)^[n] w).1 = (lorentzSphere (linearPart g))^[n] w.1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', isomPenrose_fst, ih]

/-- `x (n+1) ≤ q x n + r n`, `0 ≤ q < 1`, `r → 0`, `x ≥ 0` force `x → 0`. -/
theorem tendsto_zero_of_le_mul_add {x r : ℕ → ℝ} {q : ℝ} (hx : ∀ n, 0 ≤ x n) (hq0 : 0 ≤ q)
    (hq1 : q < 1) (hr : Tendsto r atTop (𝓝 0)) (h : ∀ᶠ n in atTop, x (n + 1) ≤ q * x n + r n) :
    Tendsto x atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hδ : 0 < ε * (1 - q) / 2 := by have : 0 < 1 - q := by linarith
                                      positivity
  obtain ⟨N, hN⟩ := eventually_atTop.1 (h.and ((Metric.tendsto_atTop.1 hr) _ hδ |>.elim
    fun N1 hN1 => eventually_atTop.2 ⟨N1, hN1⟩))
  have claim : ∀ k, x (N + k) ≤ q ^ k * x N + ε / 2 := by
    intro k
    induction k with
    | zero => simp; linarith
    | succ k ih =>
      obtain ⟨h1, h2⟩ := hN (N + k) (by omega)
      rw [Real.dist_eq, sub_zero] at h2
      have h3 : r (N + k) ≤ ε * (1 - q) / 2 := (le_abs_self _).trans h2.le
      rw [← add_assoc]
      calc x (N + k + 1) ≤ q * x (N + k) + r (N + k) := h1
        _ ≤ q * (q ^ k * x N + ε / 2) + ε * (1 - q) / 2 := by gcongr
        _ = q ^ (k + 1) * x N + ε / 2 := by ring
  have hpow : Tendsto (fun k => q ^ k * x N) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const (x N)
  obtain ⟨K, hK⟩ := (Metric.tendsto_atTop.1 hpow) (ε / 2) (by positivity)
  refine ⟨N + K, fun n hn => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, n = N + k := ⟨n - N, by omega⟩
  have h1 := hK k (by omega)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (mul_nonneg (pow_nonneg hq0 k) (hx N))] at h1
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hx _)]
  linarith [claim k]

/-- **An asymptotically contracting affine recursion converges to the fixed point of its limit.** -/
theorem tendsto_of_affine_recursion {s a b : ℕ → ℝ} {α β s₀ : ℝ} (ha0 : ∀ n, 0 ≤ a n)
    (ha : Tendsto a atTop (𝓝 α)) (hb : Tendsto b atTop (𝓝 β)) (hα : α < 1)
    (hs : ∀ n, s (n + 1) = a n * s n + b n) (hfix : s₀ = α * s₀ + β) :
    Tendsto s atTop (𝓝 s₀) := by
  have hα0 : 0 ≤ α := ge_of_tendsto' ha ha0
  set q := (1 + α) / 2
  have hq0 : 0 ≤ q := by simp only [q]; linarith
  have hq1 : q < 1 := by simp only [q]; linarith
  have haq : ∀ᶠ n in atTop, a n ≤ q := ha.eventually (ge_mem_nhds (by simp only [q]; linarith))
  set r : ℕ → ℝ := fun n => |(a n - α) * s₀ + (b n - β)|
  have hr : Tendsto r atTop (𝓝 0) := by
    have : Tendsto (fun n => (a n - α) * s₀ + (b n - β)) atTop (𝓝 ((α - α) * s₀ + (β - β))) :=
      ((ha.sub tendsto_const_nhds).mul tendsto_const_nhds).add (hb.sub tendsto_const_nhds)
    simpa [r] using this.abs
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine tendsto_zero_of_le_mul_add (fun n => norm_nonneg _) hq0 hq1 hr ?_
  filter_upwards [haq] with n hn
  simp only [Real.norm_eq_abs]
  have e : s (n + 1) - s₀ = a n * (s n - s₀) + ((a n - α) * s₀ + (b n - β)) := by
    rw [hs n]; linear_combination -hfix
  rw [e]
  calc |a n * (s n - s₀) + ((a n - α) * s₀ + (b n - β))|
      ≤ |a n * (s n - s₀)| + r n := abs_add_le _ _
    _ = a n * |s n - s₀| + r n := by rw [abs_mul, abs_of_nonneg (ha0 n)]
    _ ≤ q * |s n - s₀| + r n := by gcongr

end Laou

/-! ### Where Prop 4.17 (l.1254–1267) meets Prop 4.2: the repulsive fixed point in `𝒥` -/

theorem lorentzScale_of_eigen {A : lorentz d} {u : PenroseSphere d} {l : ℝ}
    (h : (A : Minkowski d ≃ₗ[ℝ] Minkowski d) (nullVec u) = l • nullVec u) :
    lorentzScale A u = l := by
  show ((A : Minkowski d ≃ₗ[ℝ] Minkowski d) (nullVec u)).1 = l
  rw [h]; simp [nullVec]

theorem linearPart_inv_eigen {γ : isom d} {u : PenroseSphere d} {l : ℝ} (hl : l ≠ 0)
    (h : (linearPart γ : Minkowski d ≃ₗ[ℝ] Minkowski d) (nullVec u) = l • nullVec u) :
    (linearPart γ⁻¹ : Minkowski d ≃ₗ[ℝ] Minkowski d) (nullVec u) = l⁻¹ • nullVec u := by
  rw [map_inv, Subgroup.coe_inv, LinearEquiv.coe_inv, LinearEquiv.symm_apply_eq, map_smul, h,
    smul_smul, inv_mul_cancel₀ hl, one_smul]

namespace Laou

/-- **A fixed point of `[A]` with conformal factor `< 1` attracts a ball**: the chordal identity
gives `dist([A]u, v₀) ≤ q · dist(u, v₀)` near `v₀`, `a(A, v₀) < q < 1`. -/
theorem exists_basin_sphere {A : lorentz d} {v₀ : PenroseSphere d}
    (hfix : lorentzSphere A v₀ = v₀) (hα : penroseFactor A v₀ < 1) :
    ∃ r > 0, ∀ u : PenroseSphere d, dist u v₀ < r →
      Tendsto (fun n : ℕ => (lorentzSphere A)^[n] u) atTop (𝓝 v₀) := by
  set α := penroseFactor A v₀
  have hα0 : 0 < α := penroseFactor_pos A v₀
  set q := (α + 1) / 2
  have hq0 : 0 ≤ q := by simp only [q]; linarith
  have hq1 : q < 1 := by simp only [q]; linarith
  have hαq : α * α < q ^ 2 := by
    have : α < q := by simp only [q]; linarith
    nlinarith
  have hc : Continuous fun u => penroseFactor A u * α := (continuous_penroseFactor A).mul continuous_const
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.1
    ((hc.continuousAt (x := v₀)).eventually (gt_mem_nhds (show penroseFactor A v₀ * α < q ^ 2 from hαq)))
  have hstep : ∀ u, dist u v₀ < r → dist (lorentzSphere A u) v₀ ≤ q * dist u v₀ := by
    intro u hu
    refine (pow_le_pow_iff_left₀ dist_nonneg (by positivity) two_ne_zero).1 ?_
    have h1 := dist_lorentzSphere_sq' A u v₀
    rw [hfix] at h1
    rw [h1, mul_pow]
    exact mul_le_mul_of_nonneg_right (hball hu).le (sq_nonneg _)
  refine ⟨r, hr, fun u hu => ?_⟩
  have hbound : ∀ n : ℕ, dist ((lorentzSphere A)^[n] u) v₀ ≤ q ^ n * dist u v₀ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hlt : dist ((lorentzSphere A)^[n] u) v₀ < r :=
        ih.trans_lt ((mul_le_of_le_one_left dist_nonneg (pow_le_one₀ hq0 hq1.le)).trans_lt hu)
      rw [Function.iterate_succ_apply']
      calc dist (lorentzSphere A ((lorentzSphere A)^[n] u)) v₀
          ≤ q * dist ((lorentzSphere A)^[n] u) v₀ := hstep _ hlt
        _ ≤ q * (q ^ n * dist u v₀) := by gcongr
        _ = q ^ (n + 1) * dist u v₀ := by ring
  refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun n => dist_nonneg) hbound ?_)
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const (dist u v₀)

end Laou

open Laou in
/-- **The repulsive fixed point lifts to `𝒥⁺`, with a basin `δ⁺⁻¹(U)`** (l.1254–1267, the step
of Prop 4.17's proof that rests on the dynamics of Prop 4.2's factor `a`). Let `γ` be any isometry
(any translation part) and `v₀ ∈ 𝒮` with `L(γ)(1, v₀) = l (1, v₀)`, `0 < l < 1` (l.1257–1259).
Then the conformal factor at `v₀` is `a(γ, v₀) = 1/l > 1`, `γ` fixes a point `x₀ = (v₀, s₀)` of
`𝒥⁺`, and there is an open `U ∋ v₀` such that the negative iterates `γ⁻ⁿ.x` of every `x ∈ δ⁺⁻¹(U)`
converge to `x₀`. No loxodromy is assumed: the eigenvalue alone suffices. -/
theorem laoucapulse_repulsive_basin {γ : isom d} {v₀ : PenroseSphere d} {l : ℝ} (hl0 : 0 < l)
    (hl1 : l < 1) (hv : (linearPart γ : Minkowski d ≃ₗ[ℝ] Minkowski d) (nullVec v₀) = l • nullVec v₀) :
    penroseFactor (linearPart γ) v₀ = l⁻¹ ∧
      ∃ s₀ : ℝ, isomPenrose γ (v₀, s₀) = (v₀, s₀) ∧
        ∃ U : Set (PenroseSphere d), IsOpen U ∧ v₀ ∈ U ∧
          ∀ x : PenroseSphere d × ℝ, x.1 ∈ U →
            Tendsto (fun n : ℕ => isomPenrose (γ⁻¹ ^ n) x) atTop (𝓝 (v₀, s₀)) := by
  refine ⟨by rw [penroseFactor, lorentzScale_of_eigen hv], ?_⟩
  set h := γ⁻¹
  set A := linearPart h
  have hvh : (A : Minkowski d ≃ₗ[ℝ] Minkowski d) (nullVec v₀) = l⁻¹ • nullVec v₀ :=
    linearPart_inv_eigen hl0.ne' hv
  have hα : penroseFactor A v₀ = l := by rw [penroseFactor, lorentzScale_of_eigen hvh, inv_inv]
  have hfixA : lorentzSphere A v₀ = v₀ := lorentzSphere_eq_of_eigen hvh
  set β := minkB (nullVec v₀) (h • (0 : Minkowski d))
  set s₀ := β / (1 - l)
  have h1l : (1 - l) ≠ 0 := by linarith
  have hs₀ : s₀ = l * s₀ + β := by simp only [s₀]; field_simp; ring
  have hfixh : isomPenrose h (v₀, s₀) = (v₀, s₀) := by
    refine Prod.ext (by rw [isomPenrose_fst]; exact hfixA) ?_
    rw [isomPenrose_snd]
    change penroseFactor A v₀ * s₀ + minkB (nullVec (lorentzSphere A v₀)) (h • (0 : Minkowski d)) = s₀
    rw [hα, hfixA]
    exact hs₀.symm
  refine ⟨s₀, ?_, ?_⟩
  · conv_lhs => rw [← hfixh]
    exact isomPenrose_apply_inv γ _
  obtain ⟨r, hr, hbasin⟩ := exists_basin_sphere hfixA (by rw [hα]; exact hl1)
  refine ⟨Metric.ball v₀ r, Metric.isOpen_ball, Metric.mem_ball_self hr, fun x hx => ?_⟩
  set F := isomPenrose h
  have hit : ∀ n, isomPenrose (h ^ n) x = F^[n] x := fun n => by rw [isomPenrose_iterate]
  simp only [hit]
  have hv1 : Tendsto (fun n => (F^[n] x).1) atTop (𝓝 v₀) := by
    simp only [F, iterate_fst]; exact hbasin _ hx
  have hbc : Continuous fun u => minkB (nullVec (lorentzSphere A u)) (h • (0 : Minkowski d)) := by
    simp only [minkB_nullVec]
    exact continuous_const.add
      ((continuous_subtype_val.comp (continuous_lorentzSphere A)).inner continuous_const)
  have ha : Tendsto (fun n => penroseFactor A (F^[n] x).1) atTop (𝓝 l) := by
    rw [← hα]; exact ((continuous_penroseFactor A).tendsto v₀).comp hv1
  have hb : Tendsto (fun n => minkB (nullVec (lorentzSphere A (F^[n] x).1)) (h • (0 : Minkowski d)))
      atTop (𝓝 β) := by
    have := (hbc.tendsto v₀).comp hv1
    rw [hfixA] at this
    exact this
  have hs : Tendsto (fun n => (F^[n] x).2) atTop (𝓝 s₀) :=
    tendsto_of_affine_recursion (fun n => (penroseFactor_pos A _).le) ha hb hl1
      (fun n => by rw [Function.iterate_succ_apply']; rfl) hs₀
  exact hv1.prodMk_nhds hs

/-- **The same, from Externals' `IsRepulsiveFixed`** (a loxodromic `L(γ)` with `(1, v₀)` an
eigenvector of eigenvalue in `]0, 1[`, l.1254–1259). -/
theorem laoucapulse_repulsive_basin_of_isRepulsiveFixed {γ : isom d} {v₀ : PenroseSphere d}
    (h : IsRepulsiveFixed (linearPart γ) v₀) :
    IsConformallyExpandingAt (linearPart γ) v₀ ∧
      ∃ s₀ : ℝ, isomPenrose γ (v₀, s₀) = (v₀, s₀) ∧
        ∃ U : Set (PenroseSphere d), IsOpen U ∧ v₀ ∈ U ∧
          ∀ x : PenroseSphere d × ℝ, x.1 ∈ U →
            Tendsto (fun n : ℕ => isomPenrose (γ⁻¹ ^ n) x) atTop (𝓝 (v₀, s₀)) := by
  obtain ⟨-, l, hl0, hl1, hv⟩ := h
  obtain ⟨ha, hrest⟩ := laoucapulse_repulsive_basin hl0 hl1 hv
  refine ⟨?_, hrest⟩
  rw [IsConformallyExpandingAt, ha]
  exact one_lt_inv_iff₀.2 ⟨hl0, hl1⟩

/-- **For a linear `γ` the repulsive fixed point is `(v₀, 0)`, and `γ` is expanding there** for
every `lam`: Prop 4.2's corrected form (`laoucapulse_corrected`) at the point Prop 4.17 uses. -/
theorem laoucapulse_repulsive_linear {γ : isom d} (hg : γ • (0 : Minkowski d) = 0)
    {v₀ : PenroseSphere d} {l : ℝ} (hl0 : 0 < l) (hl1 : l < 1)
    (hv : (linearPart γ : Minkowski d ≃ₗ[ℝ] Minkowski d) (nullVec v₀) = l • nullVec v₀) :
    isomPenrose γ (v₀, 0) = (v₀, 0) ∧
      ∀ lam : ℝ, 0 < lam → IsExpandingAtWrt (penroseDist lam) (isomPenrose γ) (v₀, 0) := by
  have ha := (laoucapulse_repulsive_basin hl0 hl1 hv).1
  refine ⟨?_, fun lam hlam => (isExpandingAtWrt_zeroSection_iff hg hlam v₀).2 ?_⟩
  · rw [isomPenrose_of_smul_zero hg, lorentzSphere_eq_of_eigen hv, mul_zero]
  · rw [IsConformallyExpandingAt, ha]
    exact one_lt_inv_iff₀.2 ⟨hl0, hl1⟩

/-! ### `d = 1` (Barbot's `n = 2`): `𝒮 = S⁰` is discrete, and the metric reading of the sphere
half is vacuous — the printed statement then fails even on the zero section -/

namespace Laou

theorem norm_sq_fin_one (x : EuclideanSpace ℝ (Fin 1)) : ‖x‖ ^ 2 = x 0 ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_one]

theorem penroseSphere_one_coord (u : PenroseSphere 1) :
    ((u : EuclideanSpace ℝ (Fin 1)) 0) ^ 2 = 1 := by
  rw [← norm_sq_fin_one, norm_penroseSphere, one_pow]

/-- Two distinct points of `𝒮 = S⁰` are at chordal distance `2`. -/
theorem dist_eq_two_of_ne {u u' : PenroseSphere 1} (h : u ≠ u') : dist u u' = 2 := by
  have h0 : ((u : EuclideanSpace ℝ (Fin 1)) 0) ≠ (u' : EuclideanSpace ℝ (Fin 1)) 0 := by
    intro he
    apply h
    refine Subtype.ext ?_
    ext i
    fin_cases i
    exact he
  have h1 := penroseSphere_one_coord u
  have h2 := penroseSphere_one_coord u'
  have hneg : (u' : EuclideanSpace ℝ (Fin 1)) 0 = -(u : EuclideanSpace ℝ (Fin 1)) 0 := by
    have : ((u' : EuclideanSpace ℝ (Fin 1)) 0 - (u : EuclideanSpace ℝ (Fin 1)) 0) *
        ((u' : EuclideanSpace ℝ (Fin 1)) 0 + (u : EuclideanSpace ℝ (Fin 1)) 0) = 0 := by
      ring_nf; linarith
    rcases mul_eq_zero.1 this with h3 | h3
    · exact absurd (sub_eq_zero.1 h3).symm h0
    · linarith
  have hd : dist u u' ^ 2 = 4 := by
    rw [Subtype.dist_eq, dist_eq_norm, norm_sq_fin_one, PiLp.sub_apply, hneg]
    nlinarith
  have hd0 : 0 ≤ dist u u' := dist_nonneg
  nlinarith

/-- **For `d = 1` every self-map of `𝒮` is (metrically) expanding everywhere.** -/
theorem isExpandingAt_of_one (f : PenroseSphere 1 → PenroseSphere 1) (u : PenroseSphere 1) :
    IsExpandingAt f u := by
  refine ⟨2, by norm_num, ?_⟩
  filter_upwards [prod_mem_prod (Metric.ball_mem_nhds u one_pos) (Metric.ball_mem_nhds u one_pos)]
  rintro ⟨p, q⟩ ⟨hp, hq⟩
  have e : ∀ v : PenroseSphere 1, v ∈ Metric.ball u 1 → v = u := fun v hv => by
    by_contra hne
    have := dist_eq_two_of_ne hne
    rw [Metric.mem_ball] at hv
    linarith
  simp only [e p hp, e q hq, dist_self, mul_zero, le_refl]

/-- `(t, x) ↦ (5/4 t + 3/4 x, 3/4 t + 5/4 x)` on `𝐌²`. -/
noncomputable def boostFun1 (c σ : ℝ) (p : Minkowski 1) : Minkowski 1 :=
  (c * p.1 + σ * p.2 0, !₂[σ * p.1 + c * p.2 0])

theorem boostFun1_boostFun1 {c σ : ℝ} (h : c ^ 2 - σ ^ 2 = 1) (p : Minkowski 1) :
    boostFun1 c (-σ) (boostFun1 c σ p) = p := by
  refine Prod.ext ?_ ?_
  · simp only [boostFun1]
    simp
    linear_combination p.1 * h
  · ext i; fin_cases i
    simp [boostFun1]; linear_combination p.2 0 * h

noncomputable def boostL1 : Minkowski 1 ≃ₗ[ℝ] Minkowski 1 where
  toFun := boostFun1 (5 / 4) (3 / 4)
  invFun := boostFun1 (5 / 4) (-(3 / 4))
  map_add' p q := by
    refine Prod.ext ?_ ?_
    · simp [boostFun1]; ring
    · ext i; fin_cases i
      simp [boostFun1]; ring
  map_smul' a p := by
    refine Prod.ext ?_ ?_
    · simp [boostFun1]; ring
    · ext i; fin_cases i
      simp [boostFun1]; ring
  left_inv p := boostFun1_boostFun1 (by norm_num) p
  right_inv p := by simpa using boostFun1_boostFun1 (c := 5 / 4) (σ := -(3 / 4)) (by norm_num) p

theorem boostL1_apply (p : Minkowski 1) : boostL1 p = boostFun1 (5 / 4) (3 / 4) p := rfl

theorem minkQ_one (p : Minkowski 1) : minkQ p = -p.1 ^ 2 + p.2 0 ^ 2 := by
  rw [minkQ, norm_sq_fin_one]

/-- Coordinates `𝐌² ≃ ℝ²`, to compute a determinant. -/
noncomputable def coords2 : Minkowski 1 ≃ₗ[ℝ] (Fin 2 → ℝ) where
  toFun p := ![p.1, p.2 0]
  invFun v := (v 0, !₂[v 1])
  map_add' p q := by funext i; fin_cases i <;> simp
  map_smul' a p := by funext i; fin_cases i <;> simp
  left_inv p := by
    refine Prod.ext rfl ?_
    ext i; fin_cases i; simp
  right_inv v := by funext i; fin_cases i <;> simp

theorem boostL1_mem : boostL1 ∈ lorentz 1 := by
  have hQ : ∀ v, minkQ (boostL1 v) = minkQ v := fun v => by
    rw [minkQ_one, minkQ_one]; simp [boostL1_apply, boostFun1]; ring
  refine ⟨hQ, fun v hv => ⟨?_, by rw [hQ]; exact hv.2⟩, ?_⟩
  · have h1 := hv.1
    have h2 := hv.2
    rw [minkQ_one] at h2
    simp only [boostL1_apply, boostFun1]
    nlinarith [sq_nonneg (5 * v.1 + 3 * v.2 0), sq_nonneg (v.1 + v.2 0), sq_nonneg (v.1 - v.2 0)]
  · rw [← LinearMap.det_conj _ coords2, ← LinearMap.det_toMatrix', Matrix.det_fin_two]
    simp [LinearMap.toMatrix'_apply, coords2, boostL1_apply, boostFun1]
    norm_num

/-- The boost of `𝐌²` of rapidity `artanh (3/5)`, as a linear isometry. -/
noncomputable def boostIsom1 : isom 1 := ⟨boostL1.toAffineEquiv, boostL1_mem⟩

theorem boostIsom1_smul (p : Minkowski 1) : boostIsom1 • p = boostL1 p := rfl

/-- `u₊ = (1) ∈ 𝒮 = S⁰`. -/
noncomputable def uPlus : PenroseSphere 1 :=
  ⟨!₂[1], by
    rw [mem_sphere_zero_iff_norm]
    exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).1 (by rw [norm_sq_fin_one]; simp)⟩

theorem lorentzScale_boost1_uPlus : lorentzScale (linearPart boostIsom1) uPlus = 2 := by
  show (boostL1 (nullVec uPlus)).1 = 2
  simp [boostL1_apply, boostFun1, nullVec, uPlus]
  norm_num

end Laou

open Laou in
/-- **For `d = 1` (Barbot's `n = 2`) the printed statement fails for every `lam`, already on the
zero section**: the boost `g` contracts the fibre over `u₊` (`a(g, u₊) = 1/2`), so `g` is not
expanding at `(u₊, 0)`, while every map of the discrete `𝒮 = S⁰` is metrically expanding. So
`laoucapulse_zeroSection` needs `d ≥ 2`, and for `n = 2` "expanding on `𝒮⁺`" can only mean the
conformal reading `a > 1` — under which the printed statement holds (`laoucapulse_one`). -/
theorem not_laoucapulseScaledReading_one {lam : ℝ} (hlam : 0 < lam) :
    ¬ LaoucapulseScaledReading 1 lam := by
  intro h
  have hg : boostIsom1 • (0 : Minkowski 1) = 0 := by rw [boostIsom1_smul, map_zero]
  have h1 := (h boostIsom1 hg (uPlus, 0)).2 (isExpandingAt_of_one _ _)
  have h2 := one_lt_penroseFactor_of_isExpandingAtWrt boostIsom1 hlam h1
  rw [IsConformallyExpandingAt, penroseFactor, lorentzScale_boost1_uPlus] at h2
  norm_num at h2

open Laou in
/-- **For `d = 1` (Barbot's `n = 2`), in the conformal reading, the printed equivalence holds
exactly — for every isometry (any translation part), every `lam > 0` and every `s`.** `𝒮 = S⁰` is
discrete, so near `w` the distance `penroseDist lam` sees only the fibre over `w.1`, which `g` maps
by `s ↦ a(g, w.1) s + b(g, w.1)`: `g` is expanding at `w` iff `a(g, w.1) > 1`. -/
theorem isExpandingAtWrt_penroseDist_one_iff (g : isom 1) {lam : ℝ} (hlam : 0 < lam)
    (w : PenroseSphere 1 × ℝ) :
    IsExpandingAtWrt (penroseDist lam) (isomPenrose g) w ↔
      IsConformallyExpandingAt (linearPart g) w.1 := by
  refine ⟨one_lt_penroseFactor_of_isExpandingAtWrt g hlam, fun h => ⟨_, h, ?_⟩⟩
  have hN : Prod.fst ⁻¹' Metric.ball w.1 1 ∈ 𝓝 w :=
    continuous_fst.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ one_pos)
  have e : ∀ v : PenroseSphere 1, v ∈ Metric.ball w.1 1 → v = w.1 := fun v hv => by
    by_contra hne
    have := dist_eq_two_of_ne hne
    rw [Metric.mem_ball] at hv
    linarith
  filter_upwards [prod_mem_prod hN hN]
  rintro ⟨⟨u, s⟩, ⟨u', s'⟩⟩ ⟨hp, hq⟩
  have hu : u = w.1 := e u hp
  have hu' : u' = w.1 := e u' hq
  simp only [penroseDist, isomPenrose_fst, isomPenrose_snd, hu, hu', dist_self]
  set a := penroseFactor (linearPart g) w.1
  have ha : 0 < a := penroseFactor_pos _ _
  set b := minkB (nullVec (lorentzSphere (linearPart g) w.1)) (g • (0 : Minkowski 1))
  have e2 : |a * s + b - (a * s' + b)| = a * |s - s'| := by
    rw [show a * s + b - (a * s' + b) = a * (s - s') by ring, abs_mul, abs_of_pos ha]
  rw [e2, max_eq_right (by positivity), max_eq_right (by positivity)]
  exact le_of_eq (by ring)

/-- **`bprop:laoucapulse` for `n = 2` in the conformal reading, as the printed set equality**
`E = δ⁺⁻¹(U)`, for every isometry (the paper's `τ = 0` is not needed) and every `lam > 0`. -/
theorem laoucapulse_one (g : isom 1) {lam : ℝ} (hlam : 0 < lam) :
    {w | IsExpandingAtWrt (penroseDist lam) (isomPenrose g) w} =
      Prod.fst ⁻¹' {u | IsConformallyExpandingAt (linearPart g) u} := by
  ext w
  exact isExpandingAtWrt_penroseDist_one_iff g hlam w

end Causal.Flat
