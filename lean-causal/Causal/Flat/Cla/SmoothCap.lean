import Causal.Flat.Cla.SmoothGlue

/-!
# `Causal.Flat.Cla.SmoothCap` — the cap envelope: a compact acausal Cauchy surface of a GH flat spacetime is smoothed by finitely many buried past-hyperboloid caps

T. Barbot, *Globally hyperbolic flat space-times* (`papers/barbot`, arXiv math/0402257), §2.4 and
§11. **No label is marked**: this file proves `exists_capEnvelope_of_isCompact_cauchy`, which
closes the smoothing step `exists_capEnvelope_succ` of `Flat/Cla/CompactComplete.lean` (serving
`bthm:cauclo`, `GHFspace.tex:353`, unmarked: an input of Theorem B, under DEC-35's reading of
Cauchy-completeness). Cited UNMARKED: `[2.4]` Cauchy-complete — l.551–553 (prose, DEC-35);
Cauchy-compact — l.560–565 (prose, `FlatSpacetime.CauchyCompact`'s topological reading). Line
numbers are those of the labelled `papers/barbot/legacy/labeled/GHFspace.tex`.

> We call such a spacetime *Cauchy-compact* GH spacetime (abbreviation CGH). (l.564–565)

> A fundamental observation is that in a GH spacetime, every closed spacelike hypersurface is
> necessarely a Cauchy surface (l.3537–3538)

**Dimension (kb/0024).** Barbot's `𝐌ⁿ` has total dimension `n`; `Minkowski d` has `d` spatial
dimensions, so Barbot's `n` is `d + 1`. Everything here holds for every `d`.

## The construction
At `y ∈ S`, in the chart `e = chartAt y`, inside a ball `B = ball (e y) β` lying in the chart
image of a causally convex `V` (strong causality of the tarentin GH `M`), `S` is the graph of a
strict contraction `G` over the spatial ball of radius `δ = β/4` (`J^±(S)` closed and covering
`M` through the Cauchy splitting, `sigma_separe`; the construction of
`Flat/Cla/LocallyCauchy.lean` step 3 with `f = id`). On the sphere of radius `ρ = δ/2` the
acausality gap `η = min (G x − G y₀ + ρ) > 0` (compactness, strictness). With
`a = min (η/4) (δ/4)`, the cap is the past hyperboloid of `q = (t₀ + 2a, y₀)` of radius `a` over
the closed spatial ball of radius `ρ`:
* its RIM (`‖x − y₀‖ = ρ`) lies strictly below `S` in the chart (height `≤ t₀ + 2a − ρ <
  t₀ − ρ + η ≤ G x`), hence in `I⁻(S)`;
* the points of `S` over the spatial ball of radius `a/2` lie strictly below the cap (height
  `≥ t₀ + a − ‖x − y₀‖ > t₀ + ‖x − y₀‖ ≥ G x`), hence in `I⁻(C)`.
Finitely many such neighbourhoods cover the compact `S`; `K` is the union of their caps. Each rim
is in `I⁻(S) ⊆ I⁻(I⁻(K)) ⊆ I⁻(K)`: **burial needs no comparison between two charts**, because it
goes through `S`. `SmoothGlue`'s gluing then gives the chart description of `K ∖ I⁻(K)`.

## Main declarations
* `lt_of_causallyConvexIn_of_arc` — the chronal analogue of `Causality.le_of_causallyConvexIn`.
* `exists_capData_at` — the local cap at a point of `S` (burial of the rim in `I⁻(S)`, covering
  of a neighbourhood of the point in `S` by `I⁻` of the cap).
* `exists_capEnvelope_of_isCompact_cauchy` — GH, tarentin, `S` a compact acausal Cauchy surface ⇒
  a nonempty compact `K` with `IsLocallyConeZeroSetAt d (K ∖ I⁻(K)) x` at each point of
  `K ∖ I⁻(K)`: the statement of `CompactComplete.exists_capEnvelope_succ`, any dimension.

## Hypothesis checklist
| paper hypothesis | here |
|---|---|
| `M` GH | ✓ carried (`GH M`): closedness of `J⁻(Cₖ)`, strong causality, the splitting |
| `M` Cauchy-compact (l.560–565) | ✓ carried in the topological reading: `S` Cauchy, compact, acausal |
| (none) | ⚠ the tarentin property of `flatCausality` is a hypothesis (`hT`); every flat spacetime is tarentin (`CompactComplete`'s `tarentin_flatCausality`, private there, supplies it), so it is not a restriction |

## SCOPE (disclosed)
* The caps are pieces of past hyperboloids of the chart; their union's upper part is spacelike
  Lipschitz (`SmoothCone`), not smooth: Lipschitz with slope `< 1` point by point is what
  `IsSpacelikeLipschitz` (DEC-35, contract (f)) asks.
* Namespace `Causal.Flat.Cla`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Written for the
Barbot campaign (WP-34e smoothing closer, closing `exists_capEnvelope_succ`).
-/

namespace Causal.Flat.Cla

open Set TopologicalSpace Topology Metric Filter
open scoped NNReal Pointwise

universe u

variable {d : ℕ}

/-- **A chronological pair of a causally convex set is chronological in every open set
containing it** (the chronal analogue of `Causality.le_of_causallyConvexIn`). -/
theorem lt_of_causallyConvexIn_of_arc {M : Type*} [TopologicalSpace M] {C : Causality M}
    (hC : C.CausallyArcConnected) {V : Set M} {N : Opens M}
    (hV : C.CausallyConvexIn V ⊤) (hVN : V ⊆ N) {x y : M} (hx : x ∈ V) (hy : y ∈ V)
    (hxy : C.lt ⊤ x y) : C.lt N x y := by
  obtain ⟨γ, hγ, rfl, rfl⟩ := (hC ⊤ le_rfl x y).2.1 hxy
  have hγc := hγ.causalCurveOn
  have hmem : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ N := fun t ht =>
    hVN (hV.2 _ hx _ hy (Causality.mem_diamond.2
      ⟨hγc.le_of_le le_rfl ht.1 ht.2, hγc.le_of_le ht.1 ht.2 le_rfl⟩))
  have hγN : C.ChronalCurveOn N γ 0 1 := CurveOn.restrict hγ le_rfl le_rfl le_top hmem
  exact hγN.lt_of_lt le_rfl zero_lt_one le_rfl

/-- **The local cap at a point of `S`** (see the module docstring for the numbers): a cap
(`CapData`) in `chartAt y` whose rim lies in `I⁻(S)`, and an open `O ∋ y` whose points of `S` all
lie in `I⁻` of the cap. -/
theorem exists_capData_at {M : FlatSpacetime.{u} d} (hGH : GH M)
    (hT : (flatCausality d M).Tarentin) {S : Set M}
    (hS : (flatCausality d M).IsCauchySurface S) (hac : (flatCausality d M).IsAcausal S)
    {y : M} (hy : y ∈ S) :
    ∃ P : CapData d M, ∃ O : Set M, IsOpen O ∧ y ∈ O ∧
      (∀ c ∈ P.C, P.e c ∉ P.A → c ∈ (flatCausality d M).Iminus ⊤ S) ∧
      ∀ s ∈ S ∩ O, s ∈ (flatCausality d M).Iminus ⊤ P.C := by
  classical
  set Cs := flatCausality d M with hCs
  -- (1) the two sides of `S` are closed and cover `M`
  obtain ⟨ψ, hψ⟩ := flat_exists_isCauchySplitting flat_hasChronalCausalFlow hGH.1 hS hac
  obtain ⟨hJp, hJm, hJpc, hJmc, hJint, -⟩ := Causality.sigma_separe hGH.1 hac hψ
  have hJcov : ∀ m : M, m ∈ Cs.Jplus ⊤ S ∨ m ∈ Cs.Jminus ⊤ S := by
    intro m
    rw [hJp, hJm]
    rcases le_total 0 (ψ.symm m).2 with h | h
    · exact Or.inl ⟨ψ.symm m, ⟨trivial, h⟩, ψ.apply_symm_apply m⟩
    · exact Or.inr ⟨ψ.symm m, ⟨trivial, h⟩, ψ.apply_symm_apply m⟩
  -- (2) the chart at `y` and a causally convex `V`
  set e := chartAt (Minkowski d) y with he_def
  have he : e ∈ (gxGroupoid (isom d) (Minkowski d)).maximalAtlas M :=
    (gxGroupoid (isom d) (Minkowski d)).subset_maximalAtlas (chart_mem_atlas _ y)
  have hiso : ChartIso Cs (minkowski d) e := flatCausality_chartIso he
  have hye : y ∈ e.source := mem_chart_source _ y
  have hArc := flatCausality_causallyArcConnected d M
  have hSC := Causality.GloballyHyperbolic.stronglyCausal hT hGH
  obtain ⟨V, hVn, hVO, hVcc⟩ := hSC y (chartSource e) ((chartSource e).isOpen.mem_nhds hye)
  set p₀ : Minkowski d := e y with hp₀
  obtain ⟨β, hβ, hβsub⟩ : ∃ β > 0, ball p₀ β ⊆ e '' (e.source ∩ interior V) :=
    Metric.isOpen_iff.1 (e.isOpen_image_source_inter isOpen_interior) p₀
      ⟨y, ⟨hye, mem_interior_iff_mem_nhds.2 hVn⟩, rfl⟩
  have hBt : ball p₀ β ⊆ e.target := fun w hw => by
    obtain ⟨n, ⟨hns, -⟩, rfl⟩ := hβsub hw; exact e.map_source hns
  have hBV : ∀ w ∈ ball p₀ β, e.symm w ∈ V := fun w hw => by
    obtain ⟨n, ⟨hns, hnV⟩, rfl⟩ := hβsub hw
    rw [e.left_inv hns]; exact interior_subset hnV
  have hsy : e.symm p₀ = y := e.left_inv hye
  -- (3) the cone of the chart ball read in `M`; acausality of `S` in the chart
  have hkey : ∀ a ∈ ball p₀ β, ∀ b ∈ ball p₀ β, (minkowski d).le ⊤ a b →
      Cs.le ⊤ (e.symm a) (e.symm b) := fun a ha b hb hab => le_symm_of_mem_ball he hBt ha hb hab
  have hcomp : ∀ a ∈ ball p₀ β, ∀ b ∈ ball p₀ β, e.symm a ∈ S → e.symm b ∈ S →
      (minkowski d).le ⊤ a b → a = b := by
    intro a ha b hb hSa hSb hab
    have h := hac _ hSa _ hSb (hkey a ha b hb hab)
    rw [← e.right_inv (hBt ha), ← e.right_inv (hBt hb), h]
  have hvert : ∀ t t' : ℝ, ∀ x, ((t, x) : Minkowski d) ∈ ball p₀ β →
      ((t', x) : Minkowski d) ∈ ball p₀ β → e.symm (t, x) ∈ S → e.symm (t', x) ∈ S → t = t' := by
    intro t t' x h1 h2 h3 h4
    rcases le_total t t' with h | h
    · exact congrArg Prod.fst (hcomp _ h1 _ h2 h3 h4 (minkowski_le_top_iff.2 (by
        show ‖x - x‖ ≤ t' - t
        rw [sub_self, norm_zero]; linarith)))
    · exact (congrArg Prod.fst (hcomp _ h2 _ h1 h4 h3 (minkowski_le_top_iff.2 (by
        show ‖x - x‖ ≤ t - t'
        rw [sub_self, norm_zero]; linarith)))).symm
  have hmemball : ∀ (q : Minkowski d) {ε : ℝ}, |q.1 - p₀.1| < ε → ‖q.2 - p₀.2‖ < ε →
      q ∈ ball p₀ ε := fun q ε ht hy => by
    rw [mem_ball, Prod.dist_eq, Real.dist_eq, dist_eq_norm]
    exact max_lt ht hy
  have hballmem : ∀ q ∈ ball p₀ β, |q.1 - p₀.1| < β ∧ ‖q.2 - p₀.2‖ < β := fun q hq => by
    rw [mem_ball, Prod.dist_eq, Real.dist_eq, dist_eq_norm] at hq
    exact max_lt_iff.1 hq
  -- (4) `S` is a graph over a small ball, in the chart
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = β / 4 := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδ]; positivity
  have hexists : ∀ x ∈ ball p₀.2 δ, ∃ t, |t - p₀.1| ≤ δ ∧ e.symm (t, x) ∈ S := by
    intro x hx
    have hx' : ‖x - p₀.2‖ < δ := by rwa [mem_ball, dist_eq_norm] at hx
    have hKB : closedBall p₀ (2 * δ) ⊆ ball p₀ β := closedBall_subset_ball (by linarith)
    have hΨc : ContinuousOn e.symm (closedBall p₀ (2 * δ)) :=
      e.continuousOn_symm.mono (hKB.trans hBt)
    have hQp := hΨc.preimage_isClosed_of_isClosed isClosed_closedBall hJpc
    have hQm := hΨc.preimage_isClosed_of_isClosed isClosed_closedBall hJmc
    have hsegc : IsPreconnected ((fun t : ℝ => ((t, x) : Minkowski d)) ''
        Icc (p₀.1 - δ) (p₀.1 + δ)) :=
      isPreconnected_Icc.image _ (by fun_prop)
    have hsegK : (fun t : ℝ => ((t, x) : Minkowski d)) '' Icc (p₀.1 - δ) (p₀.1 + δ) ⊆
        closedBall p₀ (2 * δ) := by
      rintro _ ⟨t, ht, rfl⟩
      rw [mem_closedBall, Prod.dist_eq, Real.dist_eq, dist_eq_norm]
      refine max_le ?_ (by linarith)
      rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
    have hp₀B : p₀ ∈ ball p₀ β := mem_ball_self hβ
    have htop : ((p₀.1 + δ, x) : Minkowski d) ∈
        (fun t : ℝ => ((t, x) : Minkowski d)) '' Icc (p₀.1 - δ) (p₀.1 + δ) :=
      ⟨p₀.1 + δ, ⟨by linarith, le_rfl⟩, rfl⟩
    have hbot : ((p₀.1 - δ, x) : Minkowski d) ∈
        (fun t : ℝ => ((t, x) : Minkowski d)) '' Icc (p₀.1 - δ) (p₀.1 + δ) :=
      ⟨p₀.1 - δ, ⟨le_rfl, by linarith⟩, rfl⟩
    obtain ⟨w, hwseg, hwp, hwm⟩ := isPreconnected_closed_iff.1 hsegc _ _ hQp hQm
      (fun w hw => (hJcov (e.symm w)).elim (fun h => Or.inl ⟨hsegK hw, h⟩)
        (fun h => Or.inr ⟨hsegK hw, h⟩))
      ⟨_, htop, hsegK htop, ⟨y, hy, by
        rw [← hsy]
        exact hkey _ hp₀B _ (hKB (hsegK htop)) (minkowski_le_top_iff.2 (by
          show ‖x - p₀.2‖ ≤ p₀.1 + δ - p₀.1
          linarith))⟩⟩
      ⟨_, hbot, hsegK hbot, ⟨y, hy, by
        rw [← hsy]
        exact hkey _ (hKB (hsegK hbot)) _ hp₀B (minkowski_le_top_iff.2 (by
          show ‖p₀.2 - x‖ ≤ p₀.1 - (p₀.1 - δ)
          rw [norm_sub_rev]; linarith))⟩⟩
    obtain ⟨t, ht, rfl⟩ := hwseg
    refine ⟨t, abs_le.2 ⟨by linarith [ht.1], by linarith [ht.2]⟩, ?_⟩
    rw [← hJint]
    exact ⟨hwp.2, hwm.2⟩
  choose! G hG using hexists
  have hGball : ∀ x ∈ ball p₀.2 δ, ((G x, x) : Minkowski d) ∈ ball p₀ β := fun x hx =>
    hmemball (G x, x) (by linarith [(hG x hx).1]) (by
      show ‖x - p₀.2‖ < β
      rw [mem_ball, dist_eq_norm] at hx; linarith)
  have hy₀δ : p₀.2 ∈ ball p₀.2 δ := mem_ball_self hδ0
  have hGy₀ : G p₀.2 = p₀.1 :=
    hvert (G p₀.2) p₀.1 p₀.2 (hGball _ hy₀δ) (mem_ball_self hβ) (hG _ hy₀δ).2 (by
      show e.symm p₀ ∈ S
      rw [hsy]; exact hy)
  have hGstrict : ∀ x ∈ ball p₀.2 δ, ∀ x' ∈ ball p₀.2 δ, x ≠ x' →
      |G x - G x'| < ‖x - x'‖ := by
    intro x hx x' hx' hne
    by_contra hcon
    push Not at hcon
    rcases le_total (G x) (G x') with h | h
    · have habs : |G x - G x'| = G x' - G x := by
        rw [abs_sub_comm]; exact abs_of_nonneg (sub_nonneg.2 h)
      have := hcomp _ (hGball x hx) _ (hGball x' hx') (hG x hx).2 (hG x' hx').2
        (minkowski_le_top_iff.2 (by
          show ‖x' - x‖ ≤ G x' - G x
          rw [norm_sub_rev]; linarith))
      exact hne (congrArg Prod.snd this)
    · have habs : |G x - G x'| = G x - G x' := abs_of_nonneg (sub_nonneg.2 h)
      have := hcomp _ (hGball x' hx') _ (hGball x hx) (hG x' hx').2 (hG x hx).2
        (minkowski_le_top_iff.2 (by
          show ‖x - x'‖ ≤ G x - G x'
          linarith))
      exact hne (congrArg Prod.snd this).symm
  have hGle : ∀ x ∈ ball p₀.2 δ, ∀ x' ∈ ball p₀.2 δ, |G x - G x'| ≤ ‖x - x'‖ := by
    intro x hx x' hx'
    rcases eq_or_ne x x' with h | h
    · rw [h, sub_self, sub_self, abs_zero, norm_zero]
    · exact (hGstrict x hx x' hx' h).le
  have hGcont : ContinuousOn G (ball p₀.2 δ) := by
    have : LipschitzOnWith 1 G (ball p₀.2 δ) := LipschitzOnWith.of_dist_le_mul fun x hx x' hx' => by
      rw [Real.dist_eq, dist_eq_norm, NNReal.coe_one, one_mul]; exact hGle x hx x' hx'
    exact this.continuousOn
  -- (5) the acausality gap of `S` on the sphere of radius `ρ = δ / 2`
  set ρ : ℝ := δ / 2 with hρdef
  have hρ : 0 < ρ := by positivity
  have hsphball : ∀ x, ‖x - p₀.2‖ = ρ → x ∈ ball p₀.2 δ := fun x hx => by
    rw [mem_ball, dist_eq_norm, hx]; linarith
  obtain ⟨η, hη, hηG⟩ : ∃ η > 0, ∀ x, ‖x - p₀.2‖ = ρ → p₀.1 - ρ + η ≤ G x := by
    have hsph : IsCompact (sphere p₀.2 ρ) := isCompact_sphere _ _
    have hmemsph : ∀ x, x ∈ sphere p₀.2 ρ ↔ ‖x - p₀.2‖ = ρ := fun x => by
      rw [mem_sphere, dist_eq_norm]
    rcases (sphere p₀.2 ρ).eq_empty_or_nonempty with hem | hne
    · refine ⟨1, one_pos, fun x hx => ?_⟩
      have : x ∈ sphere p₀.2 ρ := (hmemsph x).2 hx
      rw [hem] at this; exact absurd this (notMem_empty x)
    · have hcs : ContinuousOn (fun x => G x - p₀.1 + ρ) (sphere p₀.2 ρ) :=
        ((hGcont.mono fun x hx => hsphball x ((hmemsph x).1 hx)).sub continuousOn_const).add
          continuousOn_const
      obtain ⟨x₁, hx₁, hmin⟩ := hsph.exists_isMinOn hne hcs
      have hx₁' := (hmemsph x₁).1 hx₁
      have hx₁ne : x₁ ≠ p₀.2 := fun h => by rw [h, sub_self, norm_zero] at hx₁'; linarith
      have hst := hGstrict x₁ (hsphball x₁ hx₁') p₀.2 hy₀δ hx₁ne
      rw [hGy₀, hx₁'] at hst
      refine ⟨G x₁ - p₀.1 + ρ, by linarith [(abs_lt.1 hst).1], fun x hx => ?_⟩
      have := isMinOn_iff.1 hmin x ((hmemsph x).2 hx)
      linarith
  -- (6) the cap: centre `q = (t₀ + 2a, y₀)`, squared radius `a²`, spatial radius `ρ`
  set a : ℝ := min (η / 4) (δ / 4) with hadef
  have ha0 : 0 < a := lt_min (by positivity) (by positivity)
  have haη : a ≤ η / 4 := min_le_left _ _
  have haδ : a ≤ δ / 4 := min_le_right _ _
  set q : Minkowski d := (p₀.1 + 2 * a, p₀.2) with hqdef
  set Z : Set (Minkowski d) :=
    {z | ‖z.2 - p₀.2‖ ≤ ρ ∧ sqTimeSep q z = a ^ 2 ∧ z.1 ≤ q.1} with hZdef
  have hZ : ∀ z ∈ Z, a ≤ q.1 - z.1 ∧ q.1 - z.1 ≤ a + ‖z.2 - p₀.2‖ ∧
      ‖z.2 - p₀.2‖ < q.1 - z.1 ∧ ‖z.2 - p₀.2‖ ≤ ρ ∧
      (q.1 - z.1) ^ 2 = a ^ 2 + ‖z.2 - p₀.2‖ ^ 2 := by
    rintro z ⟨hzρ, hzs, hzq⟩
    have hn0 : 0 ≤ ‖z.2 - p₀.2‖ := norm_nonneg _
    have hu0 : 0 ≤ q.1 - z.1 := by linarith
    have heq : (q.1 - z.1) ^ 2 = a ^ 2 + ‖z.2 - p₀.2‖ ^ 2 := by
      have : sqTimeSep q z = (q.1 - z.1) ^ 2 - ‖z.2 - p₀.2‖ ^ 2 := by
        simp only [sqTimeSep, hqdef]; ring
      linarith
    refine ⟨?_, ?_, ?_, hzρ, heq⟩
    · nlinarith [sq_nonneg ‖z.2 - p₀.2‖]
    · nlinarith [sq_nonneg (a + ‖z.2 - p₀.2‖ - (q.1 - z.1))]
    · nlinarith [sq_nonneg a]
  have hZball : Z ⊆ ball p₀ β := by
    intro z hz
    obtain ⟨h1, h2, -, h4, -⟩ := hZ z hz
    have hq1 : q.1 = p₀.1 + 2 * a := rfl
    refine hmemball z (abs_lt.2 ⟨by linarith, by linarith⟩) (by linarith)
  have hZt : Z ⊆ e.target := hZball.trans hBt
  have hZlt : ∀ z ∈ Z, (minkowski d).lt ⊤ z q := fun z hz => by
    obtain ⟨-, -, h3, -, -⟩ := hZ z hz
    refine minkowski_lt_top_iff.2 ?_
    show ‖p₀.2 - z.2‖ < q.1 - z.1
    rw [norm_sub_rev]; exact h3
  have hZc : IsCompact Z := by
    refine Metric.isCompact_of_isClosed_isBounded ?_ (isBounded_ball.subset hZball)
    refine ((isClosed_le (continuous_snd.sub continuous_const).norm continuous_const).inter
      ((isClosed_eq (continuous_sqTimeSep q) continuous_const).inter
        (isClosed_le continuous_fst continuous_const)))
  set U : Set M := e.source ∩ e ⁻¹' ball p₀ β with hUdef
  set C : Set M := e.symm '' Z with hCdef
  set A : Set (Minkowski d) := ball p₀ β ∩ {z | ‖z.2 - p₀.2‖ < ρ ∧ z.1 < q.1} with hAdef
  have hUV : ∀ p ∈ U, p ∈ V := fun p hp => by
    have := hBV _ hp.2; rwa [e.left_inv hp.1] at this
  have hVs : V ⊆ (chartSource e : Set M) := hVO
  have hCe : ∀ c ∈ C, ∃ z ∈ Z, c = e.symm z ∧ e c = z := by
    rintro c ⟨z, hz, rfl⟩; exact ⟨z, hz, rfl, e.right_inv (hZt hz)⟩
  let P : CapData d M :=
  { e := e
    mem_maximalAtlas := he
    U := U
    U_subset := fun p hp => hp.1
    q := q
    r := a ^ 2
    C := C
    A := A
    isCompact_C := hZc.image_of_continuousOn (e.continuousOn_symm.mono hZt)
    C_subset := by
      rintro c ⟨z, hz, rfl⟩
      exact ⟨e.map_target (hZt hz), by
        show e (e.symm z) ∈ ball p₀ β; rw [e.right_inv (hZt hz)]; exact hZball hz⟩
    lt_q := fun c hc => by
      obtain ⟨z, hz, -, hez⟩ := hCe c hc; rw [hez]; exact hZlt z hz
    sqTimeSep_eq := fun c hc => by
      obtain ⟨z, hz, -, hez⟩ := hCe c hc; rw [hez]; exact hz.2.1
    isOpen_A := isOpen_ball.inter
      ((isOpen_lt (continuous_snd.sub continuous_const).norm continuous_const).inter
        (isOpen_lt continuous_fst continuous_const))
    A_subset := fun z hz => ⟨hBt hz.1, e.map_target (hBt hz.1), by
      show e (e.symm z) ∈ ball p₀ β; rw [e.right_inv (hBt hz.1)]; exact hz.1⟩
    mem_C_iff := by
      intro p hp hpA
      constructor
      · rintro hpC
        obtain ⟨z, hz, -, hez⟩ := hCe p hpC
        rw [hez]; exact hz.2.1
      · intro hr
        exact ⟨e p, ⟨hpA.2.1.le, hr, hpA.2.2.le⟩, e.left_inv hp.1⟩
    le_chart := by
      intro p hp c hc hpc
      have h1 := Causality.le_of_causallyConvexIn hArc hVcc hVs (hUV p hp) (hUV c hc) hpc
      exact (minkowski d).le_mono le_top (((hiso (chartSource e) le_rfl p hp.1 c hc.1).1).1 h1)
    lt_chart := by
      intro p hp c hc hpc
      have h1 := lt_of_causallyConvexIn_of_arc hArc hVcc hVs (hUV p hp) (hUV c hc) hpc
      exact (minkowski d).lt_mono le_top (((hiso (chartSource e) le_rfl p hp.1 c hc.1).2).1 h1) }
  -- (7) the neighbourhood `O` of `y` whose `S`-points lie below the cap
  set σ : ℝ := a / 2 with hσdef
  set O : Set M := e.source ∩ e ⁻¹' (ball p₀ β ∩ {z | ‖z.2 - p₀.2‖ < σ}) with hOdef
  refine ⟨P, O, e.isOpen_inter_preimage (isOpen_ball.inter
    (isOpen_lt (continuous_snd.sub continuous_const).norm continuous_const)),
    ⟨hye, mem_ball_self hβ, by show ‖p₀.2 - p₀.2‖ < σ; rw [sub_self, norm_zero]; positivity⟩,
    ?_, ?_⟩
  · -- burial: the rim of the cap lies below `S`
    intro c hc hcA
    obtain ⟨z, hz, rfl, hez⟩ := hCe c hc
    change e (e.symm z) ∉ A at hcA
    rw [hez] at hcA
    obtain ⟨h1, -, h3, h4, h5⟩ := hZ z hz
    have hzρ : ‖z.2 - p₀.2‖ = ρ := by
      refine le_antisymm h4 (not_lt.1 fun hlt => hcA ⟨hZball hz, hlt, by linarith⟩)
    have hxδ := hsphball z.2 hzρ
    have hGz := hηG z.2 hzρ
    have hu : ρ ≤ q.1 - z.1 := by
      rw [hzρ] at h5; nlinarith [sq_nonneg a]
    have hq1 : q.1 = p₀.1 + 2 * a := rfl
    have hlt : z.1 < G z.2 := by linarith
    refine ⟨e.symm (G z.2, z.2), (hG z.2 hxδ).2, ?_⟩
    refine lt_symm_of_mem_ball he hBt (hZball hz) (hGball z.2 hxδ) (minkowski_lt_top_iff.2 ?_)
    show ‖z.2 - z.2‖ < G z.2 - z.1
    rw [sub_self, norm_zero]; linarith
  · -- covering: the points of `S` near `y` lie below the cap
    rintro s' ⟨hs'S, hs'e, hs'B, hs'σ⟩
    set z := e s' with hzdef
    have hzσ : ‖z.2 - p₀.2‖ < σ := hs'σ
    have hxδ : z.2 ∈ ball p₀.2 δ := by
      rw [mem_ball, dist_eq_norm]; linarith
    have hzG : z.1 = G z.2 := by
      refine hvert z.1 (G z.2) z.2 (by simpa using hs'B) (hGball z.2 hxδ) ?_ (hG z.2 hxδ).2
      simpa [hzdef, e.left_inv hs'e] using hs'S
    set n := ‖z.2 - p₀.2‖ with hndef
    have hn0 : 0 ≤ n := norm_nonneg _
    have hGn : G z.2 ≤ p₀.1 + n := by
      have := hGle z.2 hxδ p₀.2 hy₀δ
      rw [hGy₀] at this
      linarith [(abs_le.1 this).2]
    set w : Minkowski d := (q.1 - Real.sqrt (a ^ 2 + n ^ 2), z.2) with hwdef
    have hsq : Real.sqrt (a ^ 2 + n ^ 2) ≤ a + n :=
      (Real.sqrt_le_left (by linarith)).2 (by nlinarith)
    have hsq0 : 0 ≤ Real.sqrt (a ^ 2 + n ^ 2) := Real.sqrt_nonneg _
    have hwZ : w ∈ Z := by
      refine ⟨by show ‖z.2 - p₀.2‖ ≤ ρ; linarith, ?_, by show q.1 - _ ≤ q.1; linarith⟩
      have h2 := Real.sq_sqrt (show 0 ≤ a ^ 2 + n ^ 2 by positivity)
      simp only [sqTimeSep, hwdef, hqdef]
      rw [← hndef]
      nlinarith [h2]
    refine ⟨e.symm w, ⟨w, hwZ, rfl⟩, ?_⟩
    have hz' : e.symm z = s' := e.left_inv hs'e
    rw [← hz']
    refine lt_symm_of_mem_ball he hBt hs'B (hZball hwZ) (minkowski_lt_top_iff.2 ?_)
    show ‖z.2 - z.2‖ < q.1 - Real.sqrt (a ^ 2 + n ^ 2) - z.1
    have hq1 : q.1 = p₀.1 + 2 * a := rfl
    rw [sub_self, norm_zero]; linarith

/-- **The cap envelope** (`CompactComplete.exists_capEnvelope_succ`'s statement, any dimension,
with the tarentin property as a hypothesis): `S` is nonempty (the Cauchy splitting
`S × ℝ ≃ₜ M` of the nonempty `M`), finitely many local caps (`exists_capData_at`) cover it, each
rim is buried in `I⁻(S) ⊆ I⁻(K)`, and the gluing (`isLocallyConeZeroSetAt_of_capData`, with
`push_of_capData` and `J⁻` of a compact set closed in the GH `M`) gives the chart description of
the upper part. -/
theorem exists_capEnvelope_of_isCompact_cauchy {M : FlatSpacetime.{u} d} (hGH : GH M)
    (hT : (flatCausality d M).Tarentin) {S : Set M}
    (hS : (flatCausality d M).IsCauchySurface S) (hSc : IsCompact S)
    (hac : (flatCausality d M).IsAcausal S) :
    ∃ K : Set M, IsCompact K ∧ K.Nonempty ∧
      ∀ x ∈ K \ (flatCausality d M).Iminus ⊤ K,
        IsLocallyConeZeroSetAt d (K \ (flatCausality d M).Iminus ⊤ K) x := by
  classical
  set Cs := flatCausality d M with hCs
  -- `S` is nonempty: `M` splits as `S × ℝ`
  obtain ⟨ψ, -⟩ := flat_exists_isCauchySplitting flat_hasChronalCausalFlow hGH.1 hS hac
  obtain ⟨m⟩ := (inferInstance : Nonempty M)
  have hSne : S.Nonempty := ⟨(ψ.symm m).1, (ψ.symm m).1.2⟩
  -- the local caps and a finite subcover
  have hloc : ∀ y : S, ∃ P : CapData d M, ∃ O : Set M, IsOpen O ∧ (y : M) ∈ O ∧
      (∀ c ∈ P.C, P.e c ∉ P.A → c ∈ Cs.Iminus ⊤ S) ∧ ∀ s ∈ S ∩ O, s ∈ Cs.Iminus ⊤ P.C :=
    fun y => exists_capData_at hGH hT hS hac y.2
  choose P O hOo hyO hrim hcov using hloc
  obtain ⟨t, ht⟩ := hSc.elim_finite_subcover (fun y : S => O y) hOo
    (fun x hx => mem_iUnion.2 ⟨⟨x, hx⟩, hyO _⟩)
  set K := ⋃ j ∈ t, (P j).C with hKdef
  have hSI : ∀ s ∈ S, s ∈ Cs.Iminus ⊤ K := by
    intro s hs
    obtain ⟨j, hj, hsj⟩ := mem_iUnion₂.1 (ht hs)
    obtain ⟨c, hc, hsc⟩ := hcov j s ⟨hs, hsj⟩
    exact ⟨c, mem_biUnion hj hc, hsc⟩
  have hbur : ∀ k ∈ t, ∀ c ∈ (P k).C, (P k).e c ∉ (P k).A → c ∈ Cs.Iminus ⊤ K := by
    intro k _ c hc hA
    obtain ⟨s, hs, hcs⟩ := hrim k c hc hA
    obtain ⟨c', hc', hsc'⟩ := hSI s hs
    exact ⟨c', hc', Cs.lt_trans hcs hsc'⟩
  have hKc : IsCompact K := t.isCompact_biUnion fun k _ => (P k).isCompact_C
  have hKne : K.Nonempty := by
    obtain ⟨s, hs⟩ := hSne
    obtain ⟨c, hc, -⟩ := hSI s hs
    exact ⟨c, hc⟩
  have hJ : ∀ k ∈ t, IsClosed (Cs.Jminus ⊤ (P k).C) := fun k _ =>
    Causality.isClosed_Jminus_of_isCompact (hGH.isClosed_le hT) (P k).isCompact_C
  exact ⟨K, hKc, hKne,
    isLocallyConeZeroSetAt_of_capData t P hJ hbur (push_of_capData t P hbur)⟩

end Causal.Flat.Cla
