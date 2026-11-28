import Causal.ErsEtaleMghd

/-!
# Witnesses for the étale form of ERS Cor 4.68 and for the two subluminal overlap theorems

Programme target `T-abs-ers-etale-mghd-witnesses` (`programme/roadmap.toml`; layer 1: ETT-layer
imports only, no model, no metric, `uses = [curve_nested, causally_arc_connected, is_causal]`).
Source: AUDIT-1 of `T-abs-ers-etale-mghd`, finding 4. Eperon–Reall–Sbierski, arXiv 1802.03020
(`papers/ers-predictability`, `legacy/labeled/ghd_02_19.tex`). **No label is marked**: these are
kb/0011 witnesses for three theorems of `Causal.ErsEtaleMghd`, not certificates.

* `ers_corollary_4_68_etale` — `ErsEtaleWitness.timelikeLine_ers_corollary_4_68_etale` (the
  timelike line, `S = {0}`, `U₁ = ℝ`, `U₂ = ]-1, 1[ ∪ ]2, 3[`, `A = ]-1, 1[`, `u₁ = 0`,
  `u₂ = ErsWitness.disSol₂`, `x = 5/2`), with the doubled point of the gluing
  (`timelikeLine_ers_corollary_4_68_etale_doubled`); and in the paper's two-development shape
  with `S = {0, 3}` (`timelikeLine_ers_corollary_4_68_etale_twoPoint`), where the étale
  development of `ers_theorem_3_45_etale` has a doubled point on the line
  (`timelikeLine_ers_theorem_3_45_etale_twoPoint`).
* `ers_isPreconnected_inter_of_eqOn` —
  `ErsEtaleWitness.timelikeLine_ers_isPreconnected_inter_of_eqOn` (the problem whose every function
  solves everywhere, its causality the timelike line, `Cm` the timelike line, `S = {0}`,
  `U₁ = ]-2, 1[`, `U₂ = ]-1, 2[`, `u₁ = u₂ = 0`).
* `ers_isOpenEmbedding_proj_of_eqOn` —
  `ErsEtaleWitness.timelikeLine_ers_isOpenEmbedding_proj_of_eqOn` (the same, `A = ]-1, 1[`).
* Findings: `real_eqOn_inter_of_isDevelopment` (on `ℝ`, `ers_corollary_4_68_etale` with `U₂` a
  development of a preconnected `S` has no instance). The other finding of this module,
  `ers_coe_eq_inter_of_eqOn` (the hypotheses of `ers_isOpenEmbedding_proj_of_eqOn` force
  `A = U₁ ∩ U₂`, on every background), moved to `Causal.ErsEtaleMghd` under the same full name,
  beside `ers_isOpenEmbedding_proj_of_eqOn`, which is its corollary (`T-abs-ers-overlap-sharp`).
* Helpers of general use: `timelikeLine_isCauchySurfaceOn_Ioo_of_mem` (`{c}` is a Cauchy surface
  of every bounded `]a, b[ ∋ c` on the timelike line), `timelikeLine_isCauchySurfaceOn_union_Ioo`
  (`{s, t}` one of `]a, b[ ∪ ]c, d[` when `a < s < b ≤ c < t < d`).

> Corollary 4.68. Let u1 : U1 → R and u2 : U2 → R be two globally hyperbolic developments of
> (4.61) arising from the same initial data on a connected hypersurface S ⊆ R^{d+1}. If there
> exists an x ∈ U1 ∩ U2 with u1(x) ≠ u2(x), then U1 ∩ U2 is not connected. (`:921`)

> However, in the case that $u_1$ and $u_2$ are two globally hyperbolic developments of a
> quasilinear wave equation on a fixed background such that $U_1 \cap U_2$ is disconnected,
> glueing them together along the MCGHD […] would yield a solution which is no longer defined
> on a subset of $\R^{d+1}$, but instead on a manifold which projects down on
> $U_1 \cup U_2 \subseteq \R^{d+1}$ and contains the other connected components of
> $U_1 \cap U_2$ twice. (`:852`)

## Hypothesis checklist

Witnesses, not certificates: every binder of each theorem is inhabited at the data, jointly, and
the theorem is applied (not its conclusion proved directly); none is added or dropped.

| theorem | binder | at the witness |
|---|---|---|
| 4.68 étale | `hd₁` | `{0}` Cauchy in `ℝ` (`timelikeLine_isCauchySurface_zero`), `sol = True` |
| 4.68 étale | `h₁`, `h₂`, `hA` | `]-1, 1[ ⊆ ℝ ∩ U₂`, `{0}` Cauchy in it, `0 = disSol₂` on it |
| 4.68 étale | `hclosed` | `ℝ ∩ U₂ ∩ [-1, 1] = ]-1, 1[` |
| 4.68 étale | `hx₁`, `hx₂`, `hne` | `5/2 ∈ ]2, 3[`, `0 ≠ 1` |
| 4.68 étale, two-point | `hd₁`, also `hd₂` | `{0, 3}` Cauchy in each union of two intervals (`timelikeLine_isCauchySurfaceOn_union_Ioo`) |
| 4.68 étale, two-point | `hA`, `hclosed`, `hne` | `A = ]-1, 1[ ∪ ]2, 4[`, `0 = twoSol₂` on it; `3/2`, `0 ≠ 1` |
| 3.45 étale, two-point | `hfollow`, `hfollowLt`, `hanti₁`, `hanti₂`, `harc₁`, `harc₂` | `cau` constant; `≤` of the line goes up; `timelikeLine_causallyArcConnected` |
| subluminal | `hloc`, `hglue`, `hfollow` | `sol = True`, `cau` constant |
| subluminal | `hsub` (`curve_nested`) | `CurveNestedOn.refl` |
| subluminal | `harc` (`causally_arc_connected`) | `timelikeLine_causallyArcConnected` |
| subluminal | `hm` (`is_causal`), `hmacausal`, `hSc` | `timelikeLine_isCausal`; `{0}` a point |
| subluminal | `hd₁`, `hd₂`, `hagree` | `timelikeLine_ers_etale_witness`; `0 = 0` |
| open embedding | `h₁`, `h₂`, `hSA`, `hclosed` | `lineA_subset₁`, `lineA_subset₂`, `timelikeLine_etale_witness` |

## SCOPE (disclosed)

* **What the line can witness, for 4.68.** `ers_corollary_4_68_etale` asks a development of `U₁`
  only, so a disconnected `U₂` is allowed: the witness has a genuinely disconnected overlap
  `]-1, 1[ ∪ ]2, 3[` and a genuine disagreement at `5/2`, and the gluing along `A` is Hausdorff
  with `]2, 3[` doubled. Its `U₂` is a development for no causality
  (`ErsWitness.not_isCauchySurfaceOn_disU₂`). With `U₂` also a development of a preconnected `S`
  the hypotheses have no instance on `ℝ`, for any causalities (`real_eqOn_inter_of_isDevelopment`,
  through `Causality.real_isPreconnected_inf_of_isCauchySurfaceOn`). With `S` disconnected they
  have one: `S = {0, 3}`, `U₁ = ]-7/4, 7/4[ ∪ ]2, 4[`, `U₂ = ]-1, 1[ ∪ ]5/4, 19/4[`,
  `A = ]-1, 1[ ∪ ]2, 4[`, the disagreement at `3/2` in the component `]5/4, 7/4[` of the overlap,
  both developments for the timelike line; there the étale development has a doubled point, which
  `Causal.ErsEtaleMghd`'s SCOPE says no development of `{0}` on the line has.
* **What the line cannot witness, for the subluminal theorems.** On `ℝ` two developments of a
  preconnected `S` always have a preconnected overlap, whatever the causalities
  (`Causality.real_isPreconnected_inf_of_isCauchySurfaceOn`): the witness of
  `ers_isPreconnected_inter_of_eqOn` shows its hypotheses jointly satisfiable with a proper
  overlap (`U₁ ⊄ U₂ ⊄ U₁`), but on `ℝ` its conclusion follows from `hd₁`, `hd₂`, `hSc` alone. A
  model where the agreement is needed (every other hypothesis, a disagreement, a disconnected
  overlap) is not given: no ETT-layer model of the library provides one. Argued, not formalized:
  on a circle a causal `Cm` excludes it (a point of the far component of the overlap is reached
  from `S` along both arcs, so two of its points are `Cm`-related both ways, or `S` is not
  `Cm`-acausal); in `1+1` dimensions, two thin slanted needles over `S = {t = 0}` crossing above a
  thin slab, the cone of `cau u` at a point a function of `u` there, tilted in opposite directions
  inside Minkowski's on the two needles, would give one.
* **What no model can witness, for the open embedding.** Under the hypotheses of
  `ers_isOpenEmbedding_proj_of_eqOn` the common development is the whole overlap,
  `A = U₁ ∩ U₂` (`ers_coe_eq_inter_of_eqOn`, which moved to `Causal.ErsEtaleMghd` beside the
  theorem, `T-abs-ers-overlap-sharp`), on every background: the gluing is always the trivial
  one, and the theorem's content is the connectedness of the overlap. The witness has
  `A = ]-1, 1[ = U₁ ∩ U₂`, necessarily.
* **Imports.** `Causal.ErsEtaleMghd` only (its closure has `Causal.ErsWitnesses`,
  `Causal.Ers482Solution`, `Causal.CausalIsoInvariance`, `Causal.ErsUnions`); ETT layer
  (`tools/ladder.py` `model_path` `None`); not `Causal.ErsSCWitnesses`, whose closure has
  `Causal.CExtConnexeCauchy.SubArc`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set Topology Filter Function TopologicalSpace

universe u v

variable {M : Type u} [TopologicalSpace M]

/-! ## 1. Findings about the statements

The first finding of this module, `ers_coe_eq_inter_of_eqOn` (the hypotheses of
`ers_isOpenEmbedding_proj_of_eqOn` force `A = U₁ ∩ U₂`), is in `Causal.ErsEtaleMghd`, § 5, under
the same full name, just before `ers_isOpenEmbedding_proj_of_eqOn`, which is now its corollary
(`T-abs-ers-overlap-sharp`). -/

section Findings

/-- **On `ℝ`, the étale Cor 4.68 with `U₂` a development has no instance** (the paper's reading,
`:921`: both GHDs, `S` connected): two developments of a preconnected `S`, for any causalities,
with a common development closed in the overlap, agree on all of `U₁ ∩ U₂`, so the disagreement
`hne` of `ers_corollary_4_68_etale` cannot hold. -/
theorem real_eqOn_inter_of_isDevelopment {β : Type v} {sol : Opens ℝ → (ℝ → β) → Prop}
    {cau : (ℝ → β) → Causality ℝ} {S : Set ℝ} {U₁ U₂ A : Opens ℝ} {u₁ u₂ : ℝ → β}
    (hd₁ : IsDevelopment sol cau S U₁ u₁) (hd₂ : IsDevelopment sol cau S U₂ u₂)
    (hSc : IsPreconnected S)
    (hA : (cau u₁).IsCommonDevelopment S U₁ U₂ (fun V => EqOn u₁ u₂ V) A)
    (hclosed : (U₁ : Set ℝ) ∩ U₂ ∩ closure A ⊆ A) : EqOn u₁ u₂ ((U₁ : Set ℝ) ∩ U₂) := by
  intro x hx
  by_contra hne
  have hc := Causality.real_isPreconnected_inf_of_isCauchySurfaceOn hSc hd₁.subset hd₂.subset
    hd₁.cauchy hd₂.cauchy
  rw [Opens.coe_inf] at hc
  exact ers_corollary_4_68_etale hd₁ (fun z hz => (hA.le hz).1) (fun z hz => (hA.le hz).2) hA
    hclosed hx.1 hx.2 hne hc

end Findings

/-! ## 2. Cauchy surfaces of intervals and their unions on the timelike line -/

/-- On the timelike line, `{c}` is a Cauchy surface of every bounded open interval `]a, b[ ∋ c`:
`{0}` is one of `]a - c, b - c[` (`timelikeLine_isCauchySurfaceOn_Ioo_of_neg_of_pos`),
translated by `c` (`timelikeLine_isCausalIso_addRight`). -/
theorem timelikeLine_isCauchySurfaceOn_Ioo_of_mem {a b c : ℝ} (hac : a < c) (hcb : c < b)
    {U : Opens ℝ} (hU : (U : Set ℝ) = Ioo a b) : timelikeLine.IsCauchySurfaceOn U {c} := by
  have h0 : timelikeLine.IsCauchySurfaceOn ⟨Ioo (a - c) (b - c), isOpen_Ioo⟩ {0} :=
    timelikeLine_isCauchySurfaceOn_Ioo_of_neg_of_pos (by linarith) (by linarith) rfl
  have h := (timelikeLine_isCausalIso_addRight c).isCauchySurfaceOn_image h0
  have hV : (Homeomorph.addRight c).opensCongr ⟨Ioo (a - c) (b - c), isOpen_Ioo⟩ = U := by
    refine SetLike.coe_injective ?_
    rw [coe_opensCongr, hU]
    show (fun x => x + c) '' Ioo (a - c) (b - c) = Ioo a b
    rw [image_add_const_Ioo, sub_add_cancel, sub_add_cancel]
  rw [hV, image_singleton] at h
  simpa using h

/-- On the timelike line, `{s, t}` is a Cauchy surface of `]a, b[ ∪ ]c, d[` when
`a < s < b ≤ c < t < d`: each piece has its point as Cauchy surface, `{s, t}` is acausal in the
union (`b` is missing), and `isCauchySurfaceOn_sSup_of_isAcausalOn` glues. -/
theorem timelikeLine_isCauchySurfaceOn_union_Ioo {a b c d s t : ℝ} (has : a < s) (hsb : s < b)
    (hbc : b ≤ c) (hct : c < t) (htd : t < d) {U : Opens ℝ}
    (hU : (U : Set ℝ) = Ioo a b ∪ Ioo c d) : timelikeLine.IsCauchySurfaceOn U {s, t} := by
  have hsup : sSup ({⟨Ioo a b, isOpen_Ioo⟩, ⟨Ioo c d, isOpen_Ioo⟩} : Set (Opens ℝ)) = U := by
    rw [sSup_pair]
    exact SetLike.coe_injective (by rw [Opens.coe_sup, hU]; rfl)
  have hanti : ∀ ⦃x y : ℝ⦄, timelikeLine.le U x y → timelikeLine.le U y x → x = y :=
    fun _ _ h h' => le_antisymm h.1 h'.1
  have hbU : b ∉ (U : Set ℝ) := by
    rw [hU]
    rintro (h | h)
    · exact lt_irrefl _ h.2
    · exact absurd h.1 (not_lt.2 hbc)
  have hac : timelikeLine.IsAcausalOn U ({s, t} : Set ℝ) := by
    rintro x (rfl | rfl) y (rfl | rfl) h
    · rfl
    · exact absurd (h.2 ⟨hsb.le, hbc.trans hct.le⟩) hbU
    · exact absurd h.1 (not_le.2 (by linarith))
    · rfl
  have h := Causality.isCauchySurfaceOn_sSup_of_isAcausalOn (C := timelikeLine) (B := U)
    (𝒟 := {⟨Ioo a b, isOpen_Ioo⟩, ⟨Ioo c d, isOpen_Ioo⟩}) (S := {s, t}) hanti hac ?_ ?_
  · rwa [hsup] at h
  · rintro D (rfl | rfl) x hx
    · rw [← SetLike.mem_coe, hU]
      exact Or.inl hx
    · rw [← SetLike.mem_coe, hU]
      exact Or.inr hx
  · rintro D (rfl | rfl)
    · exact ⟨{s}, by simp, timelikeLine_isCauchySurfaceOn_Ioo_of_mem has hsb rfl⟩
    · exact ⟨{t}, by simp, timelikeLine_isCauchySurfaceOn_Ioo_of_mem hct htd rfl⟩

/-! ## 3. Witness of `ers_corollary_4_68_etale` on the line, `S = {0}` -/

namespace ErsEtaleWitness

open ErsWitness EtaleGluing

/-- `]-1, 1[ ⊆ ℝ`. -/
theorem lineA_subset_top : (lineA : Set ℝ) ⊆ ((⊤ : Opens ℝ) : Set ℝ) :=
  fun _ _ => trivial

/-- `]-1, 1[ ⊆ ]-1, 1[ ∪ ]2, 3[`. -/
theorem lineA_subset_disU₂ : (lineA : Set ℝ) ⊆ disU₂ :=
  fun _ hx => Or.inl hx

/-- **The hypotheses of `ers_corollary_4_68_etale` hold jointly on the timelike line**, and it
applies: the problem whose every function solves everywhere, its causality the timelike line,
`S = {0}`, `U₁ = ℝ`, `U₂ = ]-1, 1[ ∪ ]2, 3[`, `A = ]-1, 1[`, `u₁ = 0`, `u₂ = disSol₂` (`1` on
`]2, ∞[`), `x = 5/2`; the overlap `]-1, 1[ ∪ ]2, 3[` is not connected. -/
theorem timelikeLine_ers_corollary_4_68_etale :
    IsDevelopment (fun _ _ => True) (fun _ : ℝ → ℝ => timelikeLine) {0} ⊤ (fun _ => (0 : ℝ)) ∧
      timelikeLine.IsCommonDevelopment {0} ⊤ disU₂
        (fun V => EqOn (fun _ : ℝ => (0 : ℝ)) disSol₂ V) lineA ∧
      ((⊤ : Opens ℝ) : Set ℝ) ∩ disU₂ ∩ closure lineA ⊆ lineA ∧
      (5 / 2 : ℝ) ∈ (⊤ : Opens ℝ) ∧ (5 / 2 : ℝ) ∈ disU₂ ∧
      (fun _ : ℝ => (0 : ℝ)) (5 / 2) ≠ disSol₂ (5 / 2) ∧
      ¬ IsPreconnected (((⊤ : Opens ℝ) : Set ℝ) ∩ disU₂) := by
  have hd₁ : IsDevelopment (fun _ _ => True) (fun _ : ℝ → ℝ => timelikeLine) {0} ⊤
      (fun _ => (0 : ℝ)) := ⟨trivial, fun _ _ => trivial, timelikeLine_isCauchySurface_zero⟩
  have hA : timelikeLine.IsCommonDevelopment {0} ⊤ disU₂
      (fun V => EqOn (fun _ : ℝ => (0 : ℝ)) disSol₂ V) lineA :=
    isCommonDevelopment_Ioo one_pos le_rfl rfl
  have hclosed : ((⊤ : Opens ℝ) : Set ℝ) ∩ disU₂ ∩ closure lineA ⊆ lineA := by
    rintro z ⟨⟨-, hz⟩, hzc⟩
    have hzc' : z ∈ Icc (-1 : ℝ) 1 := by
      rwa [show (lineA : Set ℝ) = Ioo (-1) 1 from rfl, closure_Ioo (by norm_num)] at hzc
    rcases (hz : z ∈ Ioo (-1 : ℝ) 1 ∪ Ioo 2 3) with hz | hz
    · exact hz
    · exact absurd (hz.1.trans_le hzc'.2) (by norm_num)
  have h52 : (5 / 2 : ℝ) ∈ disU₂ := Or.inr ⟨by norm_num, by norm_num⟩
  have hne : (fun _ : ℝ => (0 : ℝ)) (5 / 2) ≠ disSol₂ (5 / 2) := by norm_num [disSol₂]
  exact ⟨hd₁, hA, hclosed, trivial, h52, hne,
    ers_corollary_4_68_etale hd₁ lineA_subset_top lineA_subset_disU₂ hA hclosed trivial h52 hne⟩

/-- **The 4.68 witness on the gluing**: `E = ℝ ⊔_{]-1, 1[} (]-1, 1[ ∪ ]2, 3[)` is Hausdorff, `5/2`
lies off `A`, its two lifts differ, so `π` is not injective (`]2, 3[` is doubled); and `U₂` is a
development of `{0}` for no causality (`ErsWitness.not_isCauchySurfaceOn_disU₂`), as
`real_eqOn_inter_of_isDevelopment` requires. -/
theorem timelikeLine_ers_corollary_4_68_etale_doubled :
    T2Space (EtaleGluing lineA_subset_top lineA_subset_disU₂) ∧ (5 / 2 : ℝ) ∉ (lineA : Set ℝ) ∧
      Gluing.ι₁ (inclusion lineA_subset_top) (inclusion lineA_subset_disU₂)
          ⟨5 / 2, trivial⟩ ≠
        Gluing.ι₂ (inclusion lineA_subset_top) (inclusion lineA_subset_disU₂)
          ⟨5 / 2, Or.inr ⟨by norm_num, by norm_num⟩⟩ ∧
      ¬ Injective (proj lineA_subset_top lineA_subset_disU₂) ∧
      ∀ C₂ : Causality ℝ, ¬ C₂.IsCauchySurfaceOn disU₂ ({0} : Set ℝ) := by
  obtain ⟨-, hA, hclosed, -, h52, hne, -⟩ := timelikeLine_ers_corollary_4_68_etale
  have hT : T2Space (EtaleGluing lineA_subset_top lineA_subset_disU₂) :=
    (t2Space_iff lineA.isOpen).2 hclosed
  have hu : EqOn (fun _ : ℝ => (0 : ℝ)) disSol₂ (lineA : Set ℝ) := hA.agree
  obtain ⟨hxA, hne', hinj, -⟩ := not_injective_and_not_descends (h₁ := lineA_subset_top)
    (h₂ := lineA_subset_disU₂) (hu := hu) (show (5 / 2 : ℝ) ∈ ((⊤ : Opens ℝ) : Set ℝ) from trivial)
    h52 hne
  exact ⟨hT, hxA, hne', hinj, not_isCauchySurfaceOn_disU₂⟩

/-! ## 4. Witness of the paper's two-development shape, `S = {0, 3}` -/

/-- `]-7/4, 7/4[ ∪ ]2, 4[`, the first domain of the two-point witness. -/
def twoU₁ : Opens ℝ := ⟨Ioo (-(7 / 4)) (7 / 4) ∪ Ioo 2 4, isOpen_Ioo.union isOpen_Ioo⟩

/-- `]-1, 1[ ∪ ]5/4, 19/4[`, the second domain of the two-point witness. -/
def twoU₂ : Opens ℝ := ⟨Ioo (-1) 1 ∪ Ioo (5 / 4) (19 / 4), isOpen_Ioo.union isOpen_Ioo⟩

/-- `]-1, 1[ ∪ ]2, 4[`, the common development of the two-point witness. -/
def twoA : Opens ℝ := ⟨Ioo (-1) 1 ∪ Ioo 2 4, isOpen_Ioo.union isOpen_Ioo⟩

/-- The second solution of the two-point witness: `1` on `]1, 2[`, `0` elsewhere. -/
noncomputable def twoSol₂ : ℝ → ℝ := (Ioo (1 : ℝ) 2).indicator 1

/-- `]-1, 1[ ∪ ]2, 4[ ⊆ ]-7/4, 7/4[ ∪ ]2, 4[`. -/
theorem twoA_subset₁ : (twoA : Set ℝ) ⊆ twoU₁ := by
  intro x hx
  rcases (hx : x ∈ Ioo (-1 : ℝ) 1 ∪ Ioo 2 4) with h | h
  · exact Or.inl ⟨by linarith [h.1], by linarith [h.2]⟩
  · exact Or.inr h

/-- `]-1, 1[ ∪ ]2, 4[ ⊆ ]-1, 1[ ∪ ]5/4, 19/4[`. -/
theorem twoA_subset₂ : (twoA : Set ℝ) ⊆ twoU₂ := by
  intro x hx
  rcases (hx : x ∈ Ioo (-1 : ℝ) 1 ∪ Ioo 2 4) with h | h
  · exact Or.inl h
  · exact Or.inr ⟨by linarith [h.1], by linarith [h.2]⟩

/-- The two solutions of the two-point witness agree on its common development: `]1, 2[` misses
`]-1, 1[ ∪ ]2, 4[`. -/
theorem eqOn_twoSol₂ : EqOn (fun _ : ℝ => (0 : ℝ)) twoSol₂ twoA := by
  intro x hx
  have hx' : x ∉ Ioo (1 : ℝ) 2 := by
    rintro ⟨h1, h2⟩
    rcases (hx : x ∈ Ioo (-1 : ℝ) 1 ∪ Ioo 2 4) with h | h
    · linarith [h.2]
    · linarith [h.1]
  simp [twoSol₂, indicator_of_notMem hx']

/-- **The paper's two-development shape of 4.68 on the line, with `S = {0, 3}`**: both domains
are developments of `S` for the timelike line, `A = ]-1, 1[ ∪ ]2, 4[` is a common development
closed in the overlap `]-1, 1[ ∪ ]5/4, 7/4[ ∪ ]2, 4[`, `u₁ = 0` and `u₂ = twoSol₂` disagree at
`3/2`, and `ers_corollary_4_68_etale` applies: the overlap is not connected. `S` is not
connected, as `real_eqOn_inter_of_isDevelopment` requires. -/
theorem timelikeLine_ers_corollary_4_68_etale_twoPoint :
    IsDevelopment (fun _ _ => True) (fun _ : ℝ → ℝ => timelikeLine) {0, 3} twoU₁
        (fun _ => (0 : ℝ)) ∧
      IsDevelopment (fun _ _ => True) (fun _ : ℝ → ℝ => timelikeLine) {0, 3} twoU₂ twoSol₂ ∧
      timelikeLine.IsCommonDevelopment {0, 3} twoU₁ twoU₂
        (fun V => EqOn (fun _ : ℝ => (0 : ℝ)) twoSol₂ V) twoA ∧
      (twoU₁ : Set ℝ) ∩ twoU₂ ∩ closure twoA ⊆ twoA ∧
      (3 / 2 : ℝ) ∈ twoU₁ ∧ (3 / 2 : ℝ) ∈ twoU₂ ∧ (fun _ : ℝ => (0 : ℝ)) (3 / 2) ≠ twoSol₂ (3 / 2) ∧
      ¬ IsPreconnected ({0, 3} : Set ℝ) ∧
      ¬ IsPreconnected ((twoU₁ : Set ℝ) ∩ twoU₂) := by
  have hS₁ : timelikeLine.IsCauchySurfaceOn twoU₁ ({0, 3} : Set ℝ) :=
    timelikeLine_isCauchySurfaceOn_union_Ioo (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) rfl
  have hS₂ : timelikeLine.IsCauchySurfaceOn twoU₂ ({0, 3} : Set ℝ) :=
    timelikeLine_isCauchySurfaceOn_union_Ioo (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) rfl
  have hSA : timelikeLine.IsCauchySurfaceOn twoA ({0, 3} : Set ℝ) :=
    timelikeLine_isCauchySurfaceOn_union_Ioo (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) rfl
  have hsubA : ({0, 3} : Set ℝ) ⊆ twoA := by
    rintro x (rfl | rfl)
    · exact Or.inl ⟨by norm_num, by norm_num⟩
    · exact Or.inr ⟨by norm_num, by norm_num⟩
  have hA : timelikeLine.IsCommonDevelopment {0, 3} twoU₁ twoU₂
      (fun V => EqOn (fun _ : ℝ => (0 : ℝ)) twoSol₂ V) twoA :=
    ⟨fun x hx => ⟨twoA_subset₁ hx, twoA_subset₂ hx⟩, hsubA, eqOn_twoSol₂, hSA⟩
  have hclosed : (twoU₁ : Set ℝ) ∩ twoU₂ ∩ closure twoA ⊆ twoA := by
    rintro z ⟨⟨hz₁, hz₂⟩, hzc⟩
    have hcl : closure (twoA : Set ℝ) = Icc (-1) 1 ∪ Icc 2 4 := by
      rw [show (twoA : Set ℝ) = Ioo (-1) 1 ∪ Ioo 2 4 from rfl, closure_union,
        closure_Ioo (by norm_num), closure_Ioo (by norm_num)]
    rw [hcl] at hzc
    rcases (hz₁ : z ∈ Ioo (-(7 / 4) : ℝ) (7 / 4) ∪ Ioo 2 4) with h₁ | h₁
    · rcases (hz₂ : z ∈ Ioo (-1 : ℝ) 1 ∪ Ioo (5 / 4) (19 / 4)) with h₂ | h₂
      · exact Or.inl h₂
      · exfalso
        rcases hzc with h | h
        · linarith [h.2, h₂.1]
        · linarith [h.1, h₁.2]
    · exact Or.inr h₁
  have h32₁ : (3 / 2 : ℝ) ∈ twoU₁ := Or.inl ⟨by norm_num, by norm_num⟩
  have h32₂ : (3 / 2 : ℝ) ∈ twoU₂ := Or.inr ⟨by norm_num, by norm_num⟩
  have hne : (fun _ : ℝ => (0 : ℝ)) (3 / 2) ≠ twoSol₂ (3 / 2) := by
    have h : (3 / 2 : ℝ) ∈ Ioo (1 : ℝ) 2 := ⟨by norm_num, by norm_num⟩
    simp [twoSol₂, indicator_of_mem h]
  have hd₁ : IsDevelopment (fun _ _ => True) (fun _ : ℝ → ℝ => timelikeLine) {0, 3} twoU₁
      (fun _ => (0 : ℝ)) := ⟨trivial, hsubA.trans twoA_subset₁, hS₁⟩
  have hd₂ : IsDevelopment (fun _ _ => True) (fun _ : ℝ → ℝ => timelikeLine) {0, 3} twoU₂
      twoSol₂ := ⟨trivial, hsubA.trans twoA_subset₂, hS₂⟩
  have hSnc : ¬ IsPreconnected ({0, 3} : Set ℝ) := by
    intro h
    have h1 := (isPreconnected_iff_ordConnected.1 h).out (Or.inl rfl) (Or.inr rfl)
      (show (1 : ℝ) ∈ Icc 0 3 by constructor <;> norm_num)
    rcases h1 with h1 | h1 <;> norm_num at h1
  exact ⟨hd₁, hd₂, hA, hclosed, h32₁, h32₂, hne, hSnc,
    ers_corollary_4_68_etale hd₁ twoA_subset₁ twoA_subset₂ hA hclosed h32₁ h32₂ hne⟩

/-- **`ers_theorem_3_45_etale` at the two-point witness: a doubled point on the line.** With the
causality the timelike line whatever the solution, the étale development
`E = U₁ ⊔_A U₂` is Hausdorff, two-piece and causal with `{0, 3}` lifted to a Cauchy surface, and
`3/2` is doubled: `π` is not injective and the glued solution lives on no subset of `ℝ`. -/
theorem timelikeLine_ers_theorem_3_45_etale_twoPoint :
    T2Space (EtaleGluing twoA_subset₁ twoA_subset₂) ∧
      (gluedCausality twoA_subset₁ twoA_subset₂ timelikeLine timelikeLine).TwoPiece
        (sheet₁ twoA_subset₁ twoA_subset₂) (sheet₂ twoA_subset₁ twoA_subset₂) ∧
      (gluedCausality twoA_subset₁ twoA_subset₂ timelikeLine timelikeLine).IsCausal ∧
      (gluedCausality twoA_subset₁ twoA_subset₂ timelikeLine timelikeLine).IsCauchySurface
        (lift twoA_subset₁ twoA_subset₂ {0, 3}) ∧
      (3 / 2 : ℝ) ∉ (twoA : Set ℝ) ∧
      ¬ Injective (proj twoA_subset₁ twoA_subset₂) ∧
      ¬ ∃ v : ℝ → ℝ, glue twoA_subset₁ twoA_subset₂ (fun _ => (0 : ℝ)) twoSol₂ eqOn_twoSol₂ =
        v ∘ proj twoA_subset₁ twoA_subset₂ := by
  obtain ⟨hd₁, hd₂, hA, hclosed, h32₁, h32₂, hne, -, -⟩ :=
    timelikeLine_ers_corollary_4_68_etale_twoPoint
  have hanti : ∀ U : Opens ℝ, ∀ ⦃x y : ℝ⦄, timelikeLine.le U x y → timelikeLine.le U y x →
      x = y := fun _ _ _ h h' => le_antisymm h.1 h'.1
  have harc : ∀ U : Opens ℝ, timelikeLine.CausallyArcConnectedOn U :=
    fun _ => Causality.CausallyArcConnectedOn.mono timelikeLine_causallyArcConnected le_top
  obtain ⟨hT2, hTP, hcaus, hcauchy, hxA, -, hinj, hdesc⟩ := ers_theorem_3_45_etale hd₁ hd₂
    (fun _ _ _ _ _ _ _ _ => Iff.rfl) (fun _ _ _ _ _ _ _ _ => Iff.rfl) twoA_subset₁ twoA_subset₂
    hA hclosed (hanti _) (hanti _) (harc _) (harc _) h32₁ h32₂ hne
  exact ⟨hT2, hTP, hcaus, hcauchy, hxA, hinj, hdesc⟩

/-! ## 5. Witnesses of the subluminal theorems on the line, `S = {0}` -/

/-- **The hypotheses of `ers_isPreconnected_inter_of_eqOn` hold jointly on the timelike line**,
and it applies: `sol = True`, `cau` the timelike line whatever the solution, `Cm` the timelike
line, `S = {0}`, `U₁ = ]-2, 1[`, `U₂ = ]-1, 2[`, `u₁ = u₂ = 0`. The overlap is proper: neither
domain contains the other. -/
theorem timelikeLine_ers_isPreconnected_inter_of_eqOn :
    SolutionLocal (fun (_ : Opens ℝ) (_ : ℝ → ℝ) => True) ∧
      SolutionsGlue (fun (_ : Opens ℝ) (_ : ℝ → ℝ) => True) ∧
      CausalityFollows (fun _ : ℝ → ℝ => timelikeLine) ∧
      (∀ (U : Opens ℝ) (_ : ℝ → ℝ), True →
        Causality.CurveNestedOn timelikeLine timelikeLine U) ∧
      (∀ (U : Opens ℝ) (_ : ℝ → ℝ), True → timelikeLine.CausallyArcConnectedOn U) ∧
      timelikeLine.IsCausal ∧ timelikeLine.IsAcausal ({0} : Set ℝ) ∧
      IsPreconnected ({0} : Set ℝ) ∧
      IsDevelopment (fun _ _ => True) (fun _ : ℝ → ℝ => timelikeLine) {0} lineU₁ 0 ∧
      IsDevelopment (fun _ _ => True) (fun _ : ℝ → ℝ => timelikeLine) {0} lineU₂ 0 ∧
      EqOn (0 : ℝ → ℝ) 0 ((lineU₁ : Set ℝ) ∩ lineU₂) ∧
      ¬ (lineU₁ : Set ℝ) ⊆ lineU₂ ∧ ¬ (lineU₂ : Set ℝ) ⊆ lineU₁ ∧
      IsPreconnected ((lineU₁ : Set ℝ) ∩ lineU₂) := by
  obtain ⟨hd₁, hd₂, -, -, -⟩ := timelikeLine_ers_etale_witness
  have hloc : SolutionLocal (fun (_ : Opens ℝ) (_ : ℝ → ℝ) => True) := fun _ _ _ _ _ => trivial
  have hglue : SolutionsGlue (fun (_ : Opens ℝ) (_ : ℝ → ℝ) => True) := fun _ _ _ _ => trivial
  have hfollow : CausalityFollows (fun _ : ℝ → ℝ => timelikeLine) :=
    fun _ _ _ _ _ _ _ _ => Iff.rfl
  have hsub : ∀ (U : Opens ℝ) (_ : ℝ → ℝ), True →
      Causality.CurveNestedOn timelikeLine timelikeLine U :=
    fun U _ _ => Causality.CurveNestedOn.refl _ U
  have harc : ∀ (U : Opens ℝ) (_ : ℝ → ℝ), True → timelikeLine.CausallyArcConnectedOn U :=
    fun _ _ _ => Causality.CausallyArcConnectedOn.mono timelikeLine_causallyArcConnected le_top
  have hmacausal : timelikeLine.IsAcausal ({0} : Set ℝ) := fun x hx y hy _ =>
    (mem_singleton_iff.1 hx).trans (mem_singleton_iff.1 hy).symm
  have hagree : EqOn (0 : ℝ → ℝ) 0 ((lineU₁ : Set ℝ) ∩ lineU₂) := eqOn_refl _ _
  have hn₁ : ¬ (lineU₁ : Set ℝ) ⊆ lineU₂ := fun h => by
    have h' := h (show (-3 / 2 : ℝ) ∈ Ioo (-2 : ℝ) 1 by constructor <;> norm_num)
    exact absurd (h' : (-3 / 2 : ℝ) ∈ Ioo (-1 : ℝ) 2).1 (by norm_num)
  have hn₂ : ¬ (lineU₂ : Set ℝ) ⊆ lineU₁ := fun h => by
    have h' := h (show (3 / 2 : ℝ) ∈ Ioo (-1 : ℝ) 2 by constructor <;> norm_num)
    exact absurd (h' : (3 / 2 : ℝ) ∈ Ioo (-2 : ℝ) 1).2 (by norm_num)
  exact ⟨hloc, hglue, hfollow, hsub, harc, timelikeLine_isCausal, hmacausal,
    isPreconnected_singleton, hd₁, hd₂, hagree, hn₁, hn₂,
    ers_isPreconnected_inter_of_eqOn hloc hglue hfollow hsub harc timelikeLine_isCausal hmacausal
      isPreconnected_singleton hd₁ hd₂ hagree⟩

/-- **The hypotheses of `ers_isOpenEmbedding_proj_of_eqOn` hold jointly on the timelike line**,
and it applies: the data of `timelikeLine_ers_isPreconnected_inter_of_eqOn` with `A = ]-1, 1[`;
`π : ]-2, 1[ ⊔_{]-1, 1[} ]-1, 2[ → ℝ` is an open embedding. `A` is the whole overlap, as
`ers_coe_eq_inter_of_eqOn` forces on every background. -/
theorem timelikeLine_ers_isOpenEmbedding_proj_of_eqOn :
    ({0} : Set ℝ) ⊆ lineA ∧ (lineU₁ : Set ℝ) ∩ lineU₂ ∩ closure lineA ⊆ lineA ∧
      IsOpenEmbedding (proj lineA_subset₁ lineA_subset₂) ∧
      (lineA : Set ℝ) = (lineU₁ : Set ℝ) ∩ lineU₂ := by
  obtain ⟨hloc, hglue, hfollow, hsub, harc, hm, hmacausal, hSc, hd₁, hd₂, hagree, -⟩ :=
    timelikeLine_ers_isPreconnected_inter_of_eqOn
  obtain ⟨-, -, -, -, -, hSA, -, -, -, hcl, -⟩ := timelikeLine_etale_witness
  exact ⟨hSA, hcl, ers_isOpenEmbedding_proj_of_eqOn hloc hglue hfollow hsub harc hm hmacausal hSc
      hd₁ hd₂ lineA_subset₁ lineA_subset₂ hSA hcl hagree,
    ers_coe_eq_inter_of_eqOn hloc hglue hfollow hsub harc hm hmacausal hSc hd₁ hd₂ lineA_subset₁
      lineA_subset₂ hSA hcl hagree⟩

end ErsEtaleWitness

end Causal
