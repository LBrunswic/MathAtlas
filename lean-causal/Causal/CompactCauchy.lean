import Causal.CauchyDiamond

/-!
# Lemma K — a compact connected locally Cauchy set of a globally hyperbolic spacetime is a Cauchy surface

No label is marked. Lemma K is DEC-44's abstraction of a sentence Barbot asserts twice and never
proves (Rem 2.3 `clomax`, `GHFspace.tex:571–579` in the labelled file, the quoted sentence at
l.576–578; §11, l.3537–3540 and l.3578–3581; original numbering l.569–576, l.3494–3497,
l.3535–3538), shared with the gx campaign, which applies it near BTZ lines: so it is stated for an
arbitrary causality, with no smoothness and no Minkowski model inside. (Where a Minkowski space is
meant, Barbot's `𝐌ⁿ` is the library's `Minkowski d` with `n = d + 1`; none appears in this file.)

> Cauchy-compact GH spacetimes are automatically absolutely maximal. Indeed, any spacelike
> hypersurface in a given CGH spacetime is a Cauchy hypersurface. (Rem 2.3)

> A fundamental observation is that in a GH spacetime, every closed spacelike hypersurface is
> necessarely a Cauchy surface, hence, every GH spacetime containing an embedded copy of $M$ is
> necessarely Cauchy-compact. (§11, proof of Theorem B)

> Actually, (ii) follows from (i), since, as noted previously, closed spacelike hypersurfaces in
> GH spacetimes are always Cauchy hypersurfaces. (§11)

The proof template is Brunswic, *Cauchy-compact flat spacetimes with extreme BTZ*
(arXiv 2108.12631), `prop:cauchy_abs_max` (`BTZ_1.tex:1048–1074`): project `Σ` to a Cauchy surface
along a splitting `N ≃ Σ_N × ℝ`, show the projection is a homeomorphism by the lowest-point section,
deduce achronality (O'Neill, Lemma 14.45) and count intersections. Here it is rebuilt causally:

1. **Local facts** (`eq_of_le_of_isCauchySurfaceOn`, `mem_Jplus_or_Jminus_of_isCauchySurfaceOn`):
   in a causally convex open `U` where `Σ ∩ U` is Cauchy, `Σ ∩ U` is acausal and every point of
   `U` lies in `J^+_U(Σ ∩ U) ∪ J^-_U(Σ ∩ U)`; both through `CurvesExtend` and
   `inextensible_ordConnectedComponent`.
2. **The box** (`exists_box`): along the splitting, every line near the line of a point `x ∈ Σ`
   meets `Σ` exactly once in a short time window around `x` — by connectedness of the segment,
   which goes from the open past side to the open future side.
3. **The graph** (`exists_graph`): the lowest-point section is clopen in `Σ`; `Σ` connected makes
   every point lowest, so `Σ` is the graph of a continuous `h : S₀ → ℝ`. This is Brunswic's
   covering argument with the covering theory replaced by a clopen set.
4. **Acausality** (`isAcausal_of_graph`): `F = τ − h ∘ π` vanishes exactly on `Σ`; a causal curve
   from `Σ` can leave `Σ` only into `{F > 0}` and reach `Σ` only from `{F < 0}`.
5. **Existence** (`isCauchySurface_of_isLocallyCauchyTwoSided`): an inextensible curve leaves
   `J^-(Σ)` and `J^+(Σ)` (a compact set, by finitely many diamonds and the extension step of
   `theo:geroch`), so `F ∘ c` changes sign.

The bare DEC-44 form (`isCauchySurface_of_isLocallyCauchy`: locally Cauchy only, no splitting,
no two-sidedness) is **stated with a tagged `sorry`**, so that gx has a target declaration; it is
open in ETT generality and possibly false (see SCOPE). Nothing may depend on it.

## Hypothesis checklist

| DEC-44 hypothesis | here |
|---|---|
| `C` a causality on `M` | ✓ carried |
| `M` connected | ✓ carried, `ConnectedSpace M` |
| separation / countability | ⚠ `T2Space M`; no countability |
| `C.GloballyHyperbolic` | ✓ carried |
| `Σ` compact, connected | ✓ carried (`IsCompact`, `IsConnected`) |
| locally Cauchy (`IsLocallyCauchy`) | ⚠ strengthened: `IsLocallyCauchyTwoSided`, the two sides `J^±_U(Σ ∩ U) ∖ Σ` open |
| — | ⚠ added: `C.Tarentin`, `C.CausallyArcConnected`, `J^±(p) ≠ {p}` (the hypotheses of `theo:geroch`; for gx, `tarentin` and `causallyArcConnected` are fields of `SingularFlatAxioms`, and `J^-(p) ≠ {p}` holds at a BTZ point by its past half-line) |
| — | ⚠ added, named (kb/0012): `C.CurvesExtend` |
| — | ⚠ added, named (kb/0012): a splitting `ψ : S₀ × ℝ ≃ₜ M`, `C.IsCauchySplitting S₀ ψ` |

## SCOPE (disclosed)

* **The DEC-44 form is not proved.** Two named data are added, both model facts the abstract
  library lacks: a global splitting (`IsCauchySplitting`, the form DEC-32 lets gx discharge;
  lines only causally monotone, *not* chronal, so a BTZ line may be a line) and two-sidedness of
  `Σ` in the charts `U`. Two-sidedness is what makes the time window of step 2 controllable at a
  point whose line is not chronal (a BTZ point, `I^-(p) = ∅`). For `U = M` it follows from a
  splitting along `Σ` (`IsCauchySurface.isLocallyCauchyTwoSided_of_splitting`, through
  `sigma_separe`); a chart `U` must supply it from the model.
* **Why the DEC-44 form resists.** Without a global projection there is no way to compare `Σ` with
  a Cauchy surface (Brunswic's covering step); without two-sidedness the window of step 2 is not
  controlled — a point of `U` near `Σ` may be related to `Σ` only through points of `Σ` outside
  `U`, which global acausality (the conclusion) would exclude. Neither is a gap of the paper,
  which works with smooth spacelike hypersurfaces; both are what "spacelike" means here.
* **The bare DEC-44 form is stated, not proved** (`isCauchySurface_of_isLocallyCauchy`,
  `sorry -- SORRY(DEC-44)`), with the ETT regularity hypotheses of the proved form (`T2Space`,
  `Tarentin`, `CausallyArcConnected`, `J^±(p) ≠ {p}`: fields of `SingularFlatAxioms` or true at
  BTZ points, so gx loses nothing) and without the two named data. Its obstruction is the two
  bullets above; it is not known to be true in ETT generality, and no declaration uses it.
* Non-vacuity: a Cauchy surface is locally Cauchy (`IsCauchySurface.isLocallyCauchy`); on the
  timelike line every hypothesis holds jointly with `Σ = {0}` (`timelikeLine_lemmaK_hypotheses`),
  and also with `Σ = {1}` over the splitting along `S₀ = {0}`, so `Σ ≠ S₀`: Lemma K does not need `Σ` to be the
  base of the splitting (`timelikeLine_lemmaK_hypotheses_one`); Lemma K applies in
  both (`timelikeLine_isCauchySurface_zero_of_lemmaK`, `timelikeLine_isCauchySurface_one_of_lemmaK`).
* **gx contract (a)–(f)** (`docs/BARBOT.md`, "The contract with gx"): not applicable. This module
  defines no length, metric or Lipschitz graph; it touches only the Cauchy-surface API
  (`IsCauchySurfaceOn`, `IsCauchySplitting`, `CurvesExtend`) that gx imports.
* Not yet imported by the scaffold root `CausalScaffold.lean` (outside this package's write
  scope): registration, and with it `scripts/AxiomSweep.lean`'s view of this file, is left to the
  master session.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Filter Function

universe u

variable {M : Type u} [TopologicalSpace M]

namespace Causality

variable (C : Causality M)

/-- **Locally Cauchy** (DEC-44): every point of `S` has a causally convex open neighbourhood `U`
in which `S ∩ U` is a Cauchy surface of `U`. -/
def IsLocallyCauchy (S : Set M) : Prop :=
  ∀ x ∈ S, ∃ U : Opens M, x ∈ U ∧ C.CausallyConvexIn (U : Set M) ⊤ ∧
    C.IsCauchySurfaceOn U (S ∩ U)

/-- **Locally Cauchy and two-sided**: as `IsLocallyCauchy`, and the two sides
`J^+_U(S ∩ U) ∖ S`, `J^-_U(S ∩ U) ∖ S` are open. -/
def IsLocallyCauchyTwoSided (S : Set M) : Prop :=
  ∀ x ∈ S, ∃ U : Opens M, x ∈ U ∧ C.CausallyConvexIn (U : Set M) ⊤ ∧
    C.IsCauchySurfaceOn U (S ∩ U) ∧ IsOpen (C.Jplus U (S ∩ U) \ S) ∧
      IsOpen (C.Jminus U (S ∩ U) \ S)

variable {C}

theorem IsLocallyCauchyTwoSided.isLocallyCauchy {S : Set M} (h : C.IsLocallyCauchyTwoSided S) :
    C.IsLocallyCauchy S := fun x hx => by
  obtain ⟨U, hxU, hU, hSU, -, -⟩ := h x hx
  exact ⟨U, hxU, hU, hSU⟩

/-! ### The converse sanity check: Cauchy surfaces are locally Cauchy -/

theorem causallyConvexIn_top : C.CausallyConvexIn ((⊤ : Opens M) : Set M) ⊤ :=
  ⟨subset_rfl, fun _ _ _ _ => by simp⟩

/-- **A Cauchy surface is locally Cauchy**, with `U = M`: the hypothesis of Lemma K is not
vacuous. -/
theorem IsCauchySurface.isLocallyCauchy {S : Set M} (hS : C.IsCauchySurface S) :
    C.IsLocallyCauchy S := fun _ _ =>
  ⟨⊤, trivial, causallyConvexIn_top, by rw [Opens.coe_top, inter_univ]; exact hS⟩

/-- A Cauchy surface whose two sides `J^±(S) ∖ S` are open is locally Cauchy and two-sided. -/
theorem IsCauchySurface.isLocallyCauchyTwoSided {S : Set M} (hS : C.IsCauchySurface S)
    (hp : IsOpen (C.Jplus ⊤ S \ S)) (hm : IsOpen (C.Jminus ⊤ S \ S)) :
    C.IsLocallyCauchyTwoSided S := fun _ _ =>
  ⟨⊤, trivial, causallyConvexIn_top, by rw [Opens.coe_top, inter_univ]; exact hS,
    by rw [Opens.coe_top, inter_univ]; exact hp, by rw [Opens.coe_top, inter_univ]; exact hm⟩

/-- The splitting run backwards in time: `(x, t) ↦ ψ(x, −t)`. -/
def reverseSplitting {S : Set M} (ψ : S × ℝ ≃ₜ M) : S × ℝ ≃ₜ M :=
  ((Homeomorph.refl S).prodCongr (Homeomorph.neg ℝ)).trans ψ

theorem reverseSplitting_apply {S : Set M} (ψ : S × ℝ ≃ₜ M) (x : S) (t : ℝ) :
    reverseSplitting ψ (x, t) = ψ (x, -t) := rfl

/-- A splitting of `C` run backwards is a splitting of `C.dual`. -/
theorem IsCauchySplitting.dual {S : Set M} {ψ : S × ℝ ≃ₜ M} (hψ : C.IsCauchySplitting S ψ) :
    C.dual.IsCauchySplitting S (reverseSplitting ψ) where
  zero x := by rw [reverseSplitting_apply, neg_zero]; exact hψ.zero x
  mono x s t hst := by
    show C.le ⊤ (reverseSplitting ψ (x, t)) (reverseSplitting ψ (x, s))
    rw [reverseSplitting_apply, reverseSplitting_apply]
    exact hψ.mono x (neg_le_neg hst)

/-- Along an acausal `S` carrying a splitting (`lem:Sigma_separe`), the future side `J^+(S) ∖ S`
is open. -/
theorem IsCauchySplitting.isOpen_Jplus_diff (hcaus : C.IsCausal) {S : Set M}
    (hac : C.IsAcausal S) {ψ : S × ℝ ≃ₜ M} (hψ : C.IsCauchySplitting S ψ) :
    IsOpen (C.Jplus ⊤ S \ S) := by
  obtain ⟨-, -, hpc, hmc, hint, hnhds⟩ := sigma_separe hcaus hac hψ
  have hSc : IsClosed S := by rw [← hint]; exact hpc.inter hmc
  refine isOpen_iff_mem_nhds.2 fun y hy => ?_
  rw [sdiff_eq]
  exact inter_mem (hnhds y hy) (hSc.isOpen_compl.mem_nhds hy.2)

/-- **The two sides of an acausal Cauchy surface carrying a splitting are open**, so it is locally
Cauchy and two-sided, with `U = M`: the form in which a splitting along `S` (DEC-32) discharges the
hypothesis of Lemma K. -/
theorem IsCauchySurface.isLocallyCauchyTwoSided_of_splitting (hcaus : C.IsCausal) {S : Set M}
    (hS : C.IsCauchySurface S) (hac : C.IsAcausal S) {ψ : S × ℝ ≃ₜ M}
    (hψ : C.IsCauchySplitting S ψ) : C.IsLocallyCauchyTwoSided S :=
  hS.isLocallyCauchyTwoSided (hψ.isOpen_Jplus_diff hcaus hac)
    (hψ.dual.isOpen_Jplus_diff (dual_isCausal.2 hcaus) (dual_isAcausal.2 hac))

/-! ### Step 1: inside a causally convex open set where `S ∩ U` is Cauchy -/

/-- In a causally arc-connected spacetime the relation of a causally convex open `U` is that of
`M`. -/
theorem le_of_mem_causallyConvexIn (hC : C.CausallyArcConnected) {U : Opens M}
    (hU : C.CausallyConvexIn (U : Set M) ⊤) {x y : M} (hx : x ∈ U) (hy : y ∈ U)
    (hxy : C.le ⊤ x y) : C.le U x y :=
  le_of_causallyConvexIn hC hU subset_rfl hx hy hxy

/-- **`S ∩ U` is acausal** (in `M`'s relation) when it is a Cauchy surface of a causally convex
open `U`, curves extend, and `M` is causal, Hausdorff and causally arc-connected. -/
theorem eq_of_le_of_isCauchySurfaceOn [T2Space M] (hcaus : C.IsCausal)
    (hC : C.CausallyArcConnected) (hext : C.CurvesExtend) {U : Opens M}
    (hU : C.CausallyConvexIn (U : Set M) ⊤) {S : Set M} (hSU : C.IsCauchySurfaceOn U (S ∩ U))
    {z w : M} (hz : z ∈ S ∩ U) (hw : w ∈ S ∩ U) (hzw : C.le ⊤ z w) : z = w := by
  obtain ⟨γ, hγ, hγ0, hγ1⟩ := (hC ⊤ le_rfl z w).1.1 hzw
  obtain ⟨I, c, hc, hsub⟩ := hext γ 0 1 zero_le_one hγ
  obtain ⟨t₁, ht₁, hct₁⟩ : z ∈ c '' I := hsub ⟨0, ⟨le_rfl, zero_le_one⟩, hγ0⟩
  obtain ⟨t₂, ht₂, hct₂⟩ : w ∈ c '' I := hsub ⟨1, ⟨zero_le_one, le_rfl⟩, hγ1⟩
  rcases lt_or_ge t₂ t₁ with h | h
  · have h' := hc.1.le_of_le ht₂ ht₁ h.le
    rw [hct₁, hct₂] at h'
    exact hcaus hzw h'
  · have hU₁ : c t₁ ∈ U := by rw [hct₁]; exact hz.2
    have hJ := inextensible_ordConnectedComponent hcaus hc ht₁ hU₁
    have ht₁J : t₁ ∈ ordConnectedComponent (I ∩ c ⁻¹' U) t₁ :=
      self_mem_ordConnectedComponent.2 ⟨ht₁, hU₁⟩
    have ht₂J : t₂ ∈ ordConnectedComponent (I ∩ c ⁻¹' U) t₁ := by
      refine mem_ordConnectedComponent.2 fun b hb => ?_
      rw [uIcc_of_le h] at hb
      have hbI : b ∈ I := hc.1.ordConnected.out ht₁ ht₂ hb
      refine ⟨hbI, ?_⟩
      show c b ∈ (U : Set M)
      refine hU.2 z hz.2 w hw.2 (mem_diamond.2 ⟨?_, ?_⟩)
      · rw [← hct₁]; exact hc.1.le_of_le ht₁ hbI hb.1
      · rw [← hct₂]; exact hc.1.le_of_le hbI ht₂ hb.2
    obtain ⟨_, -, huniq⟩ := hSU _ c hJ
    exact (huniq z ⟨⟨t₁, ht₁J, hct₁⟩, hz⟩).trans (huniq w ⟨⟨t₂, ht₂J, hct₂⟩, hw⟩).symm

/-- **Every point of `U` is in the causal future or past of `S ∩ U` in `U`.** -/
theorem mem_Jplus_or_Jminus_of_isCauchySurfaceOn [T2Space M] (hcaus : C.IsCausal)
    (hext : C.CurvesExtend) {U : Opens M} {S : Set M} (hSU : C.IsCauchySurfaceOn U (S ∩ U))
    {q : M} (hq : q ∈ U) : q ∈ C.Jplus U (S ∩ U) ∪ C.Jminus U (S ∩ U) := by
  obtain ⟨I, c, hc, hsub⟩ := hext (fun _ => q) 0 0 le_rfl
    (causalCurveOn_const (show q ∈ (⊤ : Opens M) from trivial))
  obtain ⟨t₀, ht₀, hct₀⟩ : q ∈ c '' I := hsub ⟨0, ⟨le_rfl, le_rfl⟩, rfl⟩
  have hU₀ : c t₀ ∈ U := by rw [hct₀]; exact hq
  have hJ := inextensible_ordConnectedComponent hcaus hc ht₀ hU₀
  have ht₀J : t₀ ∈ ordConnectedComponent (I ∩ c ⁻¹' U) t₀ :=
    self_mem_ordConnectedComponent.2 ⟨ht₀, hU₀⟩
  obtain ⟨_, ⟨⟨t, ht, rfl⟩, hS⟩, -⟩ := hSU _ c hJ
  rcases le_total t₀ t with h | h
  · right
    refine ⟨c t, hS, ?_⟩
    rw [← hct₀]; exact hJ.1.le_of_le ht₀J ht h
  · left
    refine ⟨c t, hS, ?_⟩
    rw [← hct₀]; exact hJ.1.le_of_le ht ht₀J h

/-- The two sides meet only on `S`. -/
theorem mem_of_mem_Jplus_of_mem_Jminus (hcaus : C.IsCausal) {U : Opens M} {S : Set M}
    (hacU : ∀ z ∈ S ∩ U, ∀ w ∈ S ∩ U, C.le ⊤ z w → z = w) {q : M}
    (h1 : q ∈ C.Jplus U (S ∩ U)) (h2 : q ∈ C.Jminus U (S ∩ U)) : q ∈ S := by
  obtain ⟨z, hz, hzq⟩ := h1
  obtain ⟨z', hz', hqz'⟩ := h2
  have h := hacU z hz z' hz' (C.le_mono le_top (C.le_trans hzq hqz'))
  subst h
  have : q = z := hcaus (C.le_mono le_top hqz') (C.le_mono le_top hzq)
  rw [this]; exact hz.1

/-! ### Step 2: the box -/

variable {S₀ : Set M} {ψ : S₀ × ℝ ≃ₜ M}

/-- **The box.** Along the splitting `ψ`, let `ψ(y₀, t₀) ∈ S ∩ U` with `U` causally convex, `S ∩ U`
acausal, `U = J^+_U(S ∩ U) ∪ J^-_U(S ∩ U)` with open sides, and the window
`ψ(y₀, [t₀ − ε, t₀ + ε])` in `U`. Then near `y₀` every line meets `S` exactly once in the window,
at an interior time, and its window lies in `U`. -/
theorem exists_box (hψ : C.IsCauchySplitting S₀ ψ) (hC : C.CausallyArcConnected)
    (hcaus : C.IsCausal) {U : Opens M} (hU : C.CausallyConvexIn (U : Set M) ⊤) {S : Set M}
    (hacU : ∀ z ∈ S ∩ U, ∀ w ∈ S ∩ U, C.le ⊤ z w → z = w)
    (hpart : ∀ q ∈ U, q ∈ C.Jplus U (S ∩ U) ∪ C.Jminus U (S ∩ U))
    (hplus : IsOpen (C.Jplus U (S ∩ U) \ S)) (hminus : IsOpen (C.Jminus U (S ∩ U) \ S))
    {y₀ : S₀} {t₀ ε : ℝ} (hx : ψ (y₀, t₀) ∈ S ∩ U) (hε : 0 < ε)
    (ha : ψ (y₀, t₀ - ε) ∈ U) (hb : ψ (y₀, t₀ + ε) ∈ U) :
    ∃ V : Set S₀, IsOpen V ∧ y₀ ∈ V ∧ ∀ y ∈ V,
      (∀ t ∈ Icc (t₀ - ε) (t₀ + ε), ψ (y, t) ∈ U) ∧
      ∃ t ∈ Ioo (t₀ - ε) (t₀ + ε), ψ (y, t) ∈ S ∧
        ∀ t' ∈ Icc (t₀ - ε) (t₀ + ε), ψ (y, t') ∈ S → t' = t := by
  set Ap := C.Jplus U (S ∩ U) \ S with hAp
  set Am := C.Jminus U (S ∩ U) \ S with hAm
  have hdisj : Disjoint Ap Am := by
    rw [Set.disjoint_left]
    rintro q ⟨h1, hqS⟩ ⟨h2, -⟩
    exact hqS (mem_of_mem_Jplus_of_mem_Jminus hcaus hacU h1 h2)
  have hinj : ∀ {y y' : S₀} {s t : ℝ}, ψ (y, s) = ψ (y', t) → y = y' ∧ s = t := fun h => by
    have := ψ.injective h
    simp only [Prod.mk.injEq] at this
    exact this
  have haA : ψ (y₀, t₀ - ε) ∈ Am := by
    have hle : C.le ⊤ (ψ (y₀, t₀ - ε)) (ψ (y₀, t₀)) := hψ.mono y₀ (by linarith)
    refine ⟨⟨ψ (y₀, t₀), hx, le_of_mem_causallyConvexIn hC hU ha hx.2 hle⟩, fun haS => ?_⟩
    have := (hinj (hacU _ ⟨haS, ha⟩ _ hx hle)).2
    linarith
  have hbA : ψ (y₀, t₀ + ε) ∈ Ap := by
    have hle : C.le ⊤ (ψ (y₀, t₀)) (ψ (y₀, t₀ + ε)) := hψ.mono y₀ (by linarith)
    refine ⟨⟨ψ (y₀, t₀), hx, le_of_mem_causallyConvexIn hC hU hx.2 hb hle⟩, fun hbS => ?_⟩
    have := (hinj (hacU _ hx _ ⟨hbS, hb⟩ hle)).2
    linarith
  have hcont : ∀ t : ℝ, Continuous fun y : S₀ => ψ (y, t) := fun t =>
    ψ.continuous.comp (continuous_id.prodMk continuous_const)
  refine ⟨(fun y => ψ (y, t₀ - ε)) ⁻¹' Am ∩ (fun y => ψ (y, t₀ + ε)) ⁻¹' Ap,
    (hminus.preimage (hcont _)).inter (hplus.preimage (hcont _)), ⟨haA, hbA⟩, ?_⟩
  rintro y ⟨hya, hyb⟩
  have hyaU : ψ (y, t₀ - ε) ∈ U := Precausality.Jminus_subset_carrier hya.1
  have hybU : ψ (y, t₀ + ε) ∈ U := Precausality.Jplus_subset_carrier hyb.1
  have hseg : ∀ t ∈ Icc (t₀ - ε) (t₀ + ε), ψ (y, t) ∈ U := fun t ht =>
    hU.2 _ hyaU _ hybU (mem_diamond.2 ⟨hψ.mono y ht.1, hψ.mono y ht.2⟩)
  refine ⟨hseg, ?_⟩
  have hex : ∃ t ∈ Icc (t₀ - ε) (t₀ + ε), ψ (y, t) ∈ S := by
    by_contra hne
    push Not at hne
    have hsub : (fun t => ψ (y, t)) '' Icc (t₀ - ε) (t₀ + ε) ⊆ Ap ∪ Am := by
      rintro _ ⟨t, ht, rfl⟩
      rcases hpart _ (hseg t ht) with h | h
      · exact Or.inl ⟨h, hne t ht⟩
      · exact Or.inr ⟨h, hne t ht⟩
    have hpc : IsPreconnected ((fun t => ψ (y, t)) '' Icc (t₀ - ε) (t₀ + ε)) :=
      isPreconnected_Icc.image _
        (ψ.continuous.comp (continuous_const.prodMk continuous_id)).continuousOn
    rcases hpc.subset_or_subset hplus hminus hdisj hsub with h | h
    · exact Set.disjoint_left.1 hdisj (h ⟨t₀ - ε, ⟨le_rfl, by linarith⟩, rfl⟩) hya
    · exact Set.disjoint_left.1 hdisj hyb (h ⟨t₀ + ε, ⟨by linarith, le_rfl⟩, rfl⟩)
  obtain ⟨t, ht, htS⟩ := hex
  have huniq : ∀ t' ∈ Icc (t₀ - ε) (t₀ + ε), ψ (y, t') ∈ S → t' = t := by
    intro t' ht' ht'S
    rcases le_total t' t with h | h
    · exact (hinj (hacU _ ⟨ht'S, hseg t' ht'⟩ _ ⟨htS, hseg t ht⟩ (hψ.mono y h))).2
    · exact ((hinj (hacU _ ⟨htS, hseg t ht⟩ _ ⟨ht'S, hseg t' ht'⟩ (hψ.mono y h))).2).symm
  refine ⟨t, ⟨lt_of_le_of_ne ht.1 fun h => ?_, lt_of_le_of_ne ht.2 fun h => ?_⟩, htS, huniq⟩
  · rw [← h] at htS; exact hya.2 htS
  · rw [h] at htS; exact hyb.2 htS

/-- The box at a point of a locally Cauchy two-sided set, for every small window. -/
theorem exists_box_of_twoSided [T2Space M] (hcaus : C.IsCausal) (hC : C.CausallyArcConnected)
    (hext : C.CurvesExtend) (hψ : C.IsCauchySplitting S₀ ψ) {S : Set M}
    (hloc : C.IsLocallyCauchyTwoSided S) {y₀ : S₀} {t₀ : ℝ} (hx : ψ (y₀, t₀) ∈ S) :
    ∃ U : Opens M, C.CausallyConvexIn (U : Set M) ⊤ ∧
      (∀ z ∈ S ∩ U, ∀ w ∈ S ∩ U, C.le ⊤ z w → z = w) ∧
      ∃ ε₀ > 0, ∀ ε, 0 < ε → ε ≤ ε₀ → ∃ V : Set S₀, IsOpen V ∧ y₀ ∈ V ∧ ∀ y ∈ V,
        (∀ t ∈ Icc (t₀ - ε) (t₀ + ε), ψ (y, t) ∈ U) ∧
        ∃ t ∈ Ioo (t₀ - ε) (t₀ + ε), ψ (y, t) ∈ S ∧
          ∀ t' ∈ Icc (t₀ - ε) (t₀ + ε), ψ (y, t') ∈ S → t' = t := by
  obtain ⟨U, hxU, hU, hSU, hplus, hminus⟩ := hloc _ hx
  have hacU : ∀ z ∈ S ∩ U, ∀ w ∈ S ∩ U, C.le ⊤ z w → z = w := fun z hz w hw hzw =>
    eq_of_le_of_isCauchySurfaceOn hcaus hC hext hU hSU hz hw hzw
  have hpart : ∀ q ∈ U, q ∈ C.Jplus U (S ∩ U) ∪ C.Jminus U (S ∩ U) := fun q hq =>
    mem_Jplus_or_Jminus_of_isCauchySurfaceOn hcaus hext hSU hq
  have hf : Continuous fun t : ℝ => ψ (y₀, t) :=
    ψ.continuous.comp (continuous_const.prodMk continuous_id)
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 (U.isOpen.preimage hf) t₀
    (show t₀ ∈ (fun t : ℝ => ψ (y₀, t)) ⁻¹' (U : Set M) from hxU)
  have hmem : ∀ t, |t - t₀| < r → ψ (y₀, t) ∈ U := fun t ht =>
    hball (by rw [Metric.mem_ball, Real.dist_eq]; exact ht)
  refine ⟨U, hU, hacU, r / 2, by linarith, fun ε hε hεr => ?_⟩
  exact exists_box hψ hC hcaus hU hacU hpart hplus hminus ⟨hx, hxU⟩ hε
    (hmem _ (by rw [abs_lt]; constructor <;> linarith))
    (hmem _ (by rw [abs_lt]; constructor <;> linarith))

/-! ### Step 3: `S` is the graph of a continuous function over `S₀` -/

/-- **The graph.** A compact connected locally Cauchy two-sided `S` meets every line of the
splitting exactly once, at the time `h y` of a continuous `h`. -/
theorem exists_graph [T2Space M] [ConnectedSpace M] (hcaus : C.IsCausal)
    (hC : C.CausallyArcConnected) (hext : C.CurvesExtend) (hψ : C.IsCauchySplitting S₀ ψ)
    {S : Set M} (hSc : IsCompact S) (hSconn : IsConnected S)
    (hloc : C.IsLocallyCauchyTwoSided S) :
    ∃ h : S₀ → ℝ, Continuous h ∧ ∀ y t, ψ (y, t) ∈ S ↔ t = h y := by
  have hsymm : ∀ (y : S₀) (t : ℝ), ψ.symm (ψ (y, t)) = (y, t) := fun y t => ψ.symm_apply_apply _
  have hpt : ∀ q : M, ψ ((ψ.symm q).1, (ψ.symm q).2) = q := fun q => by
    rw [Prod.mk.eta, ψ.apply_symm_apply]
  have hπ : Continuous fun q : M => (ψ.symm q).1 := continuous_fst.comp ψ.symm.continuous
  have hτ : Continuous fun q : M => (ψ.symm q).2 := continuous_snd.comp ψ.symm.continuous
  -- the times at which a line meets `S` form a compact set
  have hZc : ∀ y : S₀, IsCompact {t : ℝ | ψ (y, t) ∈ S} := by
    intro y
    have heq : {t : ℝ | ψ (y, t) ∈ S} = Prod.snd '' (ψ ⁻¹' S ∩ {p : S₀ × ℝ | p.1 = y}) := by
      ext t
      constructor
      · intro ht
        exact ⟨(y, t), ⟨ht, rfl⟩, rfl⟩
      · rintro ⟨⟨y', t'⟩, ⟨h, h'⟩, rfl⟩
        simp only [mem_setOf_eq] at h'
        subst h'
        exact h
    rw [heq]
    exact ((ψ.isCompact_preimage.2 hSc).inter_right
      (isClosed_eq continuous_fst continuous_const)).image continuous_snd
  -- every line meets `S`: the set of lines meeting `S` is clopen
  have hD : ∀ y : S₀, ∃ t, ψ (y, t) ∈ S := by
    set D : Set S₀ := {y | ∃ t, ψ (y, t) ∈ S} with hDdef
    have hDimg : D = (fun q => (ψ.symm q).1) '' S := by
      ext y
      constructor
      · rintro ⟨t, ht⟩
        exact ⟨ψ (y, t), ht, by simp only [hsymm]⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨(ψ.symm x).2, by rw [hpt]; exact hx⟩
    have hDc : IsClosed D := by
      rw [hDimg]; exact (hSc.image hπ).isClosed
    have hDo : IsOpen D := by
      refine isOpen_iff_forall_mem_open.2 fun y hy => ?_
      obtain ⟨t, ht⟩ := hy
      obtain ⟨U, -, -, ε₀, hε₀, hV⟩ := exists_box_of_twoSided hcaus hC hext hψ hloc ht
      obtain ⟨V, hVo, hyV, hVp⟩ := hV ε₀ hε₀ le_rfl
      refine ⟨V, fun y' hy' => ?_, hVo, hyV⟩
      obtain ⟨-, t', -, ht', -⟩ := hVp y' hy'
      exact ⟨t', ht'⟩
    haveI : ConnectedSpace S₀ :=
      Function.Surjective.connectedSpace (f := fun q : M => (ψ.symm q).1)
        (fun y => ⟨ψ (y, 0), by simp⟩) hπ
    obtain ⟨x, hx⟩ := hSconn.nonempty
    have hDne : D.Nonempty := ⟨(ψ.symm x).1, (ψ.symm x).2, by rw [hpt]; exact hx⟩
    have hDu := IsClopen.eq_univ ⟨hDc, hDo⟩ hDne
    intro y
    have hyD : y ∈ D := by rw [hDu]; exact mem_univ y
    exact hyD
  -- the lowest points of `S` on their lines
  set Low : Set M := {x | ∀ t, ψ ((ψ.symm x).1, t) ∈ S → (ψ.symm x).2 ≤ t} with hLow
  have hLowOpen : ∀ x ∈ S, x ∈ Low →
      ∃ O : Set M, IsOpen O ∧ x ∈ O ∧ ∀ x' ∈ S, x' ∈ O → x' ∈ Low := by
    intro x hxS hxL
    have hxL' : ∀ t, ψ ((ψ.symm x).1, t) ∈ S → (ψ.symm x).2 ≤ t := hxL
    have hx' : ψ ((ψ.symm x).1, (ψ.symm x).2) ∈ S := by rw [hpt]; exact hxS
    obtain ⟨U, -, -, ε, hε, hV⟩ := exists_box_of_twoSided hcaus hC hext hψ hloc hx'
    obtain ⟨V, hVo, hy₀V, hVp⟩ := hV ε hε le_rfl
    set Q := S ∩ {z | (ψ.symm z).2 ≤ (ψ.symm x).2 - ε} with hQ
    have hQc : IsCompact Q := hSc.inter_right (_root_.isClosed_le hτ continuous_const)
    set P := (fun q : M => (ψ.symm q).1) '' Q with hP
    have hPc : IsClosed P := (hQc.image hπ).isClosed
    have hy₀P : (ψ.symm x).1 ∉ P := by
      rintro ⟨z, ⟨hzS, hzτ⟩, hzy⟩
      have h1 : ψ ((ψ.symm x).1, (ψ.symm z).2) ∈ S := by
        simp only at hzy
        rw [← hzy, hpt]; exact hzS
      have := hxL' _ h1
      simp only [mem_setOf_eq] at hzτ
      linarith
    refine ⟨(fun q : M => (ψ.symm q).1) ⁻¹' (V ∩ Pᶜ) ∩
        (fun q : M => (ψ.symm q).2) ⁻¹' Ioo ((ψ.symm x).2 - ε) ((ψ.symm x).2 + ε),
      ((hVo.inter hPc.isOpen_compl).preimage hπ).inter (isOpen_Ioo.preimage hτ),
      ⟨⟨hy₀V, hy₀P⟩, by simp only [mem_preimage, mem_Ioo]; constructor <;> linarith⟩, ?_⟩
    rintro x' hx'S ⟨⟨hy'V, hy'P⟩, hτ'⟩
    simp only [mem_preimage, mem_Ioo] at hτ'
    show ∀ t, ψ ((ψ.symm x').1, t) ∈ S → (ψ.symm x').2 ≤ t
    intro t ht
    obtain ⟨-, th, -, -, huniq⟩ := hVp _ hy'V
    rcases le_or_gt t ((ψ.symm x).2 - ε) with h1 | h1
    · exfalso
      apply hy'P
      refine ⟨ψ ((ψ.symm x').1, t), ⟨ht, ?_⟩, ?_⟩
      · simp only [mem_setOf_eq, hsymm]; exact h1
      · simp only [hsymm]
    rcases le_or_gt t ((ψ.symm x).2 + ε) with h2 | h2
    · have e1 := huniq t ⟨h1.le, h2⟩ ht
      have e2 := huniq (ψ.symm x').2 ⟨hτ'.1.le, hτ'.2.le⟩ (by rw [hpt]; exact hx'S)
      rw [e1, e2]
    · exact (hτ'.2.trans h2).le
  have hLowClosed : ∀ x ∈ S, x ∉ Low →
      ∃ O : Set M, IsOpen O ∧ x ∈ O ∧ ∀ x' ∈ S, x' ∈ O → x' ∉ Low := by
    intro x _ hxL
    have hxL' : ¬ ∀ t, ψ ((ψ.symm x).1, t) ∈ S → (ψ.symm x).2 ≤ t := hxL
    push Not at hxL'
    obtain ⟨t₁, ht₁S, ht₁⟩ := hxL'
    obtain ⟨U, -, -, ε₀, hε₀, hV⟩ := exists_box_of_twoSided hcaus hC hext hψ hloc ht₁S
    set ε := min ε₀ (((ψ.symm x).2 - t₁) / 2) with hεdef
    have hε : 0 < ε := lt_min hε₀ (by linarith)
    have hεle : ε ≤ ((ψ.symm x).2 - t₁) / 2 := min_le_right _ _
    obtain ⟨V, hVo, hyV, hVp⟩ := hV ε hε (min_le_left _ _)
    refine ⟨(fun q : M => (ψ.symm q).1) ⁻¹' V ∩ (fun q : M => (ψ.symm q).2) ⁻¹' Ioi (t₁ + ε),
      (hVo.preimage hπ).inter (isOpen_Ioi.preimage hτ), ⟨hyV, ?_⟩, ?_⟩
    · show t₁ + ε < (ψ.symm x).2
      linarith
    · rintro x' - ⟨hy', hτ'⟩ hlow
      have hlow' : ∀ t, ψ ((ψ.symm x').1, t) ∈ S → (ψ.symm x').2 ≤ t := hlow
      obtain ⟨-, t, ht, htS, -⟩ := hVp _ hy'
      have := hlow' t htS
      simp only [mem_preimage, mem_Ioi] at hτ'
      linarith [ht.2]
  -- `S` connected: every point is lowest
  have hall : S ⊆ Low := by
    have hpre := isPreconnected_iff_subset_of_disjoint.1 hSconn.isPreconnected
    set u := ⋃₀ {O : Set M | IsOpen O ∧ ∀ x' ∈ S, x' ∈ O → x' ∈ Low} with hu
    set v := ⋃₀ {O : Set M | IsOpen O ∧ ∀ x' ∈ S, x' ∈ O → x' ∉ Low} with hv
    have hcov : S ⊆ u ∪ v := by
      intro x hx
      by_cases hxL : x ∈ Low
      · obtain ⟨O, hO, hxO, hOL⟩ := hLowOpen x hx hxL
        exact Or.inl (mem_sUnion.2 ⟨O, ⟨hO, hOL⟩, hxO⟩)
      · obtain ⟨O, hO, hxO, hOL⟩ := hLowClosed x hx hxL
        exact Or.inr (mem_sUnion.2 ⟨O, ⟨hO, hOL⟩, hxO⟩)
    have hdis : S ∩ (u ∩ v) = ∅ := by
      refine eq_empty_iff_forall_notMem.2 fun x ⟨hx, hxu, hxv⟩ => ?_
      obtain ⟨O₁, ⟨-, h₁⟩, hx₁⟩ := mem_sUnion.1 hxu
      obtain ⟨O₂, ⟨-, h₂⟩, hx₂⟩ := mem_sUnion.1 hxv
      exact h₂ x hx hx₂ (h₁ x hx hx₁)
    rcases hpre u v (isOpen_sUnion fun O hO => hO.1) (isOpen_sUnion fun O hO => hO.1) hcov
      hdis with h | h
    · intro x hx
      obtain ⟨O, ⟨-, hOL⟩, hxO⟩ := mem_sUnion.1 (h hx)
      exact hOL x hx hxO
    · exfalso
      obtain ⟨x, hx⟩ := hSconn.nonempty
      have hZne : {t : ℝ | ψ ((ψ.symm x).1, t) ∈ S}.Nonempty :=
        ⟨(ψ.symm x).2, by rw [mem_setOf_eq, hpt]; exact hx⟩
      have ht₁ := (hZc (ψ.symm x).1).sInf_mem hZne
      have hlow : ψ ((ψ.symm x).1, sInf {t : ℝ | ψ ((ψ.symm x).1, t) ∈ S}) ∈ Low := by
        show ∀ t, _ → _
        intro t ht
        simp only [hsymm] at ht ⊢
        exact csInf_le (hZc _).bddBelow ht
      obtain ⟨O, ⟨-, hO⟩, hxO⟩ := mem_sUnion.1 (h ht₁)
      exact hO _ ht₁ hxO hlow
  -- the graph
  have hgraph : ∀ y t, ψ (y, t) ∈ S ↔ t = sInf {t : ℝ | ψ (y, t) ∈ S} := by
    intro y t
    constructor
    · intro ht
      have hL : ∀ t', ψ ((ψ.symm (ψ (y, t))).1, t') ∈ S → (ψ.symm (ψ (y, t))).2 ≤ t' := hall ht
      simp only [hsymm] at hL
      exact le_antisymm (le_csInf ⟨t, ht⟩ hL) (csInf_le (hZc y).bddBelow ht)
    · rintro rfl
      obtain ⟨t', ht'⟩ := hD y
      exact (hZc y).sInf_mem ⟨t', ht'⟩
  refine ⟨fun y => sInf {t : ℝ | ψ (y, t) ∈ S}, ?_, hgraph⟩
  refine continuous_iff_continuousAt.2 fun y₀ => Metric.continuousAt_iff'.2 fun ε hε => ?_
  have hx : ψ (y₀, sInf {t : ℝ | ψ (y₀, t) ∈ S}) ∈ S := (hgraph y₀ _).2 rfl
  obtain ⟨U, -, -, ε₀, hε₀, hV⟩ := exists_box_of_twoSided hcaus hC hext hψ hloc hx
  obtain ⟨V, hVo, hyV, hVp⟩ := hV (min ε ε₀) (lt_min hε hε₀) (min_le_right _ _)
  filter_upwards [hVo.mem_nhds hyV] with y hy
  obtain ⟨-, t, ht, htS, -⟩ := hVp y hy
  have e := (hgraph y t).1 htS
  have hm := min_le_left ε ε₀
  rw [Real.dist_eq, ← e, abs_lt]
  constructor <;> linarith [ht.1, ht.2]

/-! ### Step 4: acausality -/

/-- Around a point of `S`, a point above (below) the graph is in the causal future (past) of the
point of `S` on its line, which lies in a chart where `S` is acausal. -/
theorem exists_sign_nhds [T2Space M] (hcaus : C.IsCausal) (hC : C.CausallyArcConnected)
    (hext : C.CurvesExtend) (hψ : C.IsCauchySplitting S₀ ψ) {S : Set M}
    (hloc : C.IsLocallyCauchyTwoSided S) {h : S₀ → ℝ} (hgraph : ∀ y t, ψ (y, t) ∈ S ↔ t = h y)
    {w : M} (hw : w ∈ S) :
    ∃ O : Set M, IsOpen O ∧ w ∈ O ∧ ∃ U : Opens M, O ⊆ U ∧
      (∀ z ∈ S ∩ U, ∀ z' ∈ S ∩ U, C.le ⊤ z z' → z = z') ∧
      ∀ q ∈ O, ψ ((ψ.symm q).1, h (ψ.symm q).1) ∈ S ∩ U ∧
        (h (ψ.symm q).1 ≤ (ψ.symm q).2 → C.le ⊤ (ψ ((ψ.symm q).1, h (ψ.symm q).1)) q) ∧
        ((ψ.symm q).2 ≤ h (ψ.symm q).1 → C.le ⊤ q (ψ ((ψ.symm q).1, h (ψ.symm q).1))) := by
  have hpt : ∀ q : M, ψ ((ψ.symm q).1, (ψ.symm q).2) = q := fun q => by
    rw [Prod.mk.eta, ψ.apply_symm_apply]
  have hπ : Continuous fun q : M => (ψ.symm q).1 := continuous_fst.comp ψ.symm.continuous
  have hτ : Continuous fun q : M => (ψ.symm q).2 := continuous_snd.comp ψ.symm.continuous
  have hw' : ψ ((ψ.symm w).1, (ψ.symm w).2) ∈ S := by rw [hpt]; exact hw
  obtain ⟨U, -, hacU, ε, hε, hV⟩ := exists_box_of_twoSided hcaus hC hext hψ hloc hw'
  obtain ⟨V, hVo, hyV, hVp⟩ := hV ε hε le_rfl
  refine ⟨(fun q : M => (ψ.symm q).1) ⁻¹' V ∩
      (fun q : M => (ψ.symm q).2) ⁻¹' Ioo ((ψ.symm w).2 - ε) ((ψ.symm w).2 + ε),
    (hVo.preimage hπ).inter (isOpen_Ioo.preimage hτ),
    ⟨hyV, by simp only [mem_preimage, mem_Ioo]; constructor <;> linarith⟩, U, ?_, hacU, ?_⟩
  · rintro q ⟨hqV, hqτ⟩
    simp only [mem_preimage, mem_Ioo] at hqτ
    obtain ⟨hseg, -⟩ := hVp _ hqV
    have := hseg _ ⟨hqτ.1.le, hqτ.2.le⟩
    rwa [hpt] at this
  · rintro q ⟨hqV, -⟩
    obtain ⟨hseg, t, ht, htS, -⟩ := hVp _ hqV
    have e := (hgraph _ t).1 htS
    have hzS : ψ ((ψ.symm q).1, h (ψ.symm q).1) ∈ S := (hgraph _ _).2 rfl
    have hzU : ψ ((ψ.symm q).1, h (ψ.symm q).1) ∈ U := by
      rw [← e]; exact hseg t ⟨ht.1.le, ht.2.le⟩
    refine ⟨⟨hzS, hzU⟩, fun hle => ?_, fun hle => ?_⟩
    · have := hψ.mono (ψ.symm q).1 hle
      rwa [hpt] at this
    · have := hψ.mono (ψ.symm q).1 hle
      rwa [hpt] at this

/-- **`S` is acausal** (the O'Neill step, Lemma 14.45 in Brunswic's proof). -/
theorem isAcausal_of_graph [T2Space M] (hcaus : C.IsCausal) (hC : C.CausallyArcConnected)
    (hext : C.CurvesExtend) (hψ : C.IsCauchySplitting S₀ ψ) {S : Set M} (hSc : IsClosed S)
    (hloc : C.IsLocallyCauchyTwoSided S) {h : S₀ → ℝ} (hcont : Continuous h)
    (hgraph : ∀ y t, ψ (y, t) ∈ S ↔ t = h y) : C.IsAcausal S := by
  have hpt : ∀ q : M, ψ ((ψ.symm q).1, (ψ.symm q).2) = q := fun q => by
    rw [Prod.mk.eta, ψ.apply_symm_apply]
  set F : M → ℝ := fun q => (ψ.symm q).2 - h (ψ.symm q).1 with hF
  have hFc : Continuous F := (continuous_snd.comp ψ.symm.continuous).sub
    (hcont.comp (continuous_fst.comp ψ.symm.continuous))
  have hF0 : ∀ q, q ∈ S ↔ F q = 0 := fun q => by
    have := hgraph (ψ.symm q).1 (ψ.symm q).2
    rw [hpt] at this
    rw [this]
    simp only [hF, sub_eq_zero]
  -- the local facts at a point of a causal curve lying on `S`
  have hside : ∀ {γ : ℝ → M}, C.CausalCurveOn ⊤ γ 0 1 → ∀ s ∈ Icc (0 : ℝ) 1, γ s ∈ S →
      (∃ δ > 0, ∀ s', s < s' → s' < s + δ → s' ≤ 1 → 0 < F (γ s') ∨ γ s' = γ s) ∧
      (∃ δ > 0, ∀ s', s - δ < s' → s' < s → 0 ≤ s' → F (γ s') < 0 ∨ γ s' = γ s) := by
    intro γ hγ s hs hγs
    obtain ⟨O, hO, hwO, U, hOU, hacU, hsign⟩ :=
      exists_sign_nhds hcaus hC hext hψ hloc hgraph hγs
    have hγc : ContinuousOn γ (Icc 0 1) := hγ.continuousOn C.isRelFamily_le
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhdsWithin_iff.1 (hγc s hs (hO.mem_nhds hwO))
    have hnear : ∀ s', |s' - s| < δ → s' ∈ Icc (0 : ℝ) 1 → γ s' ∈ O := fun s' h1 h2 =>
      hball ⟨by rw [Metric.mem_ball, Real.dist_eq]; exact h1, h2⟩
    have hγsU : γ s ∈ S ∩ U := ⟨hγs, hOU hwO⟩
    refine ⟨⟨δ, hδ, fun s' h1 h2 h3 => ?_⟩, ⟨δ, hδ, fun s' h1 h2 h3 => ?_⟩⟩
    · have hq := hnear s' (by rw [abs_lt]; constructor <;> linarith) ⟨by linarith [hs.1], h3⟩
      have hle : C.le ⊤ (γ s) (γ s') := hγ.le_of_le hs.1 h1.le h3
      obtain ⟨hz, -, hqz⟩ := hsign _ hq
      rcases lt_trichotomy (F (γ s')) 0 with hneg | hzero | hpos
      · right
        have hlt : (ψ.symm (γ s')).2 ≤ h (ψ.symm (γ s')).1 := by
          simp only [hF] at hneg; linarith
        have h2 := hqz hlt
        have he := hacU _ hγsU _ hz (C.le_trans hle h2)
        rw [← he] at h2
        exact hcaus h2 hle
      · right
        exact (hacU _ hγsU _ ⟨(hF0 _).2 hzero, hOU hq⟩ hle).symm
      · left; exact hpos
    · have hq := hnear s' (by rw [abs_lt]; constructor <;> linarith) ⟨h3, by linarith [hs.2]⟩
      have hle : C.le ⊤ (γ s') (γ s) := hγ.le_of_le h3 h2.le hs.2
      obtain ⟨hz, hzq, -⟩ := hsign _ hq
      rcases lt_trichotomy (F (γ s')) 0 with hneg | hzero | hpos
      · left; exact hneg
      · right
        exact hacU _ ⟨(hF0 _).2 hzero, hOU hq⟩ _ hγsU hle
      · right
        have hlt : h (ψ.symm (γ s')).1 ≤ (ψ.symm (γ s')).2 := by
          simp only [hF] at hpos; linarith
        have h2 := hzq hlt
        have he := hacU _ hz _ hγsU (C.le_trans h2 hle)
        rw [he] at h2
        exact hcaus hle h2
  -- the global argument along a causal curve from `x` to `w`
  intro x hx w hw hxw
  obtain ⟨γ, hγ, hγ0, hγ1⟩ := (hC ⊤ le_rfl x w).1.1 hxw
  have hγc : ContinuousOn γ (Icc 0 1) := hγ.continuousOn C.isRelFamily_le
  have hgc : ContinuousOn (fun s => F (γ s)) (Icc 0 1) := hFc.comp_continuousOn hγc
  set Z := Icc (0 : ℝ) 1 ∩ γ ⁻¹' {x} with hZ
  have hZc : IsClosed Z := hγc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hZne : Z.Nonempty := ⟨0, ⟨le_rfl, zero_le_one⟩, hγ0⟩
  have hZb : BddAbove Z := ⟨1, fun s hs => hs.1.2⟩
  have hs₀ := hZc.csSup_mem hZne hZb
  set s₀ := sSup Z with hs₀def
  have hγs₀ : γ s₀ = x := hs₀.2
  rcases eq_or_lt_of_le hs₀.1.2 with h1 | h1
  · rw [← hγ1, ← h1, hγs₀]
  · obtain ⟨⟨δ, hδ, hR⟩, -⟩ := hside hγ s₀ hs₀.1 (by rw [hγs₀]; exact hx)
    have hmin1 := min_le_left δ (1 - s₀)
    have hmin2 := min_le_right δ (1 - s₀)
    have hminpos : 0 < min δ (1 - s₀) := lt_min hδ (by linarith)
    set s' := s₀ + min δ (1 - s₀) / 2 with hs'
    have hs's₀ : s₀ < s' := by linarith
    have hs'1 : s' < 1 := by linarith
    have hs'0 : 0 ≤ s' := by linarith [hs₀.1.1]
    have hFs' : 0 < F (γ s') := by
      rcases hR s' hs's₀ (by linarith) hs'1.le with h | h
      · exact h
      · exfalso
        have hs'Z : s' ∈ Z := ⟨⟨hs'0, hs'1.le⟩, by rw [mem_preimage, h, hγs₀]; rfl⟩
        linarith [le_csSup hZb hs'Z]
    set Z₃ := Icc s' 1 ∩ γ ⁻¹' S with hZ₃
    have hZ₃c : IsClosed Z₃ :=
      (hγc.mono (Icc_subset_Icc hs'0 le_rfl)).preimage_isClosed_of_isClosed isClosed_Icc hSc
    have h1Z₃ : (1 : ℝ) ∈ Z₃ := ⟨⟨hs'1.le, le_rfl⟩, by rw [mem_preimage, hγ1]; exact hw⟩
    have hZ₃b : BddBelow Z₃ := ⟨s', fun s hs => hs.1.1⟩
    have hs₃ := hZ₃c.csInf_mem ⟨1, h1Z₃⟩ hZ₃b
    set s₃ := sInf Z₃ with hs₃def
    have hs's₃ : s' < s₃ := lt_of_le_of_ne hs₃.1.1 fun he => by
      have hS' : γ s' ∈ S := by rw [he]; exact hs₃.2
      rw [(hF0 _).1 hS'] at hFs'
      exact lt_irrefl _ hFs'
    have hpos : ∀ r, s' ≤ r → r < s₃ → 0 < F (γ r) := by
      intro r hr1 hr2
      by_contra hle
      push Not at hle
      obtain ⟨r', hr', hr'0⟩ := intermediate_value_Icc' hr1
        (hgc.mono (Icc_subset_Icc hs'0 (by linarith [hs₃.1.2]))) ⟨hle, hFs'.le⟩
      have hr'Z : r' ∈ Z₃ := ⟨⟨hr'.1, by linarith [hr'.2, hs₃.1.2]⟩, (hF0 _).2 hr'0⟩
      linarith [csInf_le hZ₃b hr'Z, hr'.2]
    obtain ⟨-, ⟨δ₃, hδ₃, hL⟩⟩ := hside hγ s₃ ⟨by linarith, hs₃.1.2⟩ hs₃.2
    have hm1 := min_le_left δ₃ (s₃ - s')
    have hm2 := min_le_right δ₃ (s₃ - s')
    have hmpos : 0 < min δ₃ (s₃ - s') := lt_min hδ₃ (by linarith)
    have hr1 : s' < s₃ - min δ₃ (s₃ - s') / 2 := by linarith
    have hr2 : s₃ - min δ₃ (s₃ - s') / 2 < s₃ := by linarith
    rcases hL (s₃ - min δ₃ (s₃ - s') / 2) (by linarith) hr2 (by linarith) with h | h
    · linarith [hpos _ hr1.le hr2]
    · have hrS : γ (s₃ - min δ₃ (s₃ - s') / 2) ∈ S := by rw [h]; exact hs₃.2
      have := hpos _ hr1.le hr2
      rw [(hF0 _).1 hrS] at this
      exact absurd this (lt_irrefl 0)

/-! ### Step 5: an inextensible curve leaves the causal past of a compact set -/

/-- On a tarentin globally hyperbolic Hausdorff causally arc-connected spacetime with
`J^+(p) ≠ {p}`, an inextensible causal curve over `ℝ` leaves the causal past of every compact
set: its tail would lie in finitely many compact diamonds, accumulate, and extend. -/
theorem exists_not_mem_Jminus_of_isCompact [T2Space M] (hT : C.Tarentin)
    (hG : C.GloballyHyperbolic) (hC : C.CausallyArcConnected)
    (hJp : ∀ p : M, C.Jplus ⊤ {p} ≠ {p}) {c : ℝ → M} (hc : C.Inextensible ⊤ univ c)
    {K : Set M} (hK : IsCompact K) : ∃ s, c s ∉ C.Jminus ⊤ K := by
  by_contra hne
  push Not at hne
  choose p _ q _ hpq using fun z => hT z univ univ_mem
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun z => C.openDiamond ⊤ (p z) (q z))
    (fun _ => isOpen_openDiamond) (fun z _ => mem_iUnion.2 ⟨z, hpq z⟩)
  set K' := ⋃ i ∈ t, C.diamond ⊤ (c 0) (q i) with hK'
  have hK'c : IsCompact K' := t.isCompact_biUnion fun i _ => hG.2 _ _
  have htail : ∀ s, 0 ≤ s → c s ∈ K' := by
    intro s hs
    obtain ⟨z, hz, hcz⟩ := hne s
    obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.1 (ht hz)
    refine mem_iUnion₂.2 ⟨i, hi, mem_diamond.2 ⟨hc.1.le_of_le trivial trivial hs, ?_⟩⟩
    exact C.le_trans hcz (mem_diamond.1 (openDiamond_subset_diamond hzi)).2
  obtain ⟨p₀, -, hp₀⟩ := hK'c.exists_clusterPt (f := map c atTop) (by
    rw [le_principal_iff]
    exact mem_map.2 (mem_atTop_sets.2 ⟨0, fun s hs => htail s hs⟩))
  have hle : ∀ s, C.le ⊤ (c s) p₀ := fun s => by
    have hcl := hG.isClosed_Jplus_singleton hT (c s)
    have hev : C.Jplus ⊤ {c s} ∈ map c atTop := mem_map.2 (mem_atTop_sets.2 ⟨s, fun s' hs' => by
      simpa using hc.1.le_of_le trivial trivial hs'⟩)
    have hmem : p₀ ∈ closure (C.Jplus ⊤ {c s}) :=
      mem_closure_iff_clusterPt.2 (hp₀.mono (le_principal_iff.2 hev))
    rw [hcl.closure_eq] at hmem
    simpa using hmem
  exact hc.2 (extensible_of_forall_ge hT hG hC hJp hc.1 hle)

/-- The past form: an inextensible causal curve over `ℝ` leaves the causal future of every compact
set. -/
theorem exists_not_mem_Jplus_of_isCompact [T2Space M] (hT : C.Tarentin)
    (hG : C.GloballyHyperbolic) (hC : C.CausallyArcConnected)
    (hJm : ∀ p : M, C.Jminus ⊤ {p} ≠ {p}) {c : ℝ → M} (hc : C.Inextensible ⊤ univ c)
    {K : Set M} (hK : IsCompact K) : ∃ s, c s ∉ C.Jplus ⊤ K := by
  have hd := hc.dual_reverse
  rw [neg_univ] at hd
  obtain ⟨s, hs⟩ := exists_not_mem_Jminus_of_isCompact (C := C.dual) (dual_tarentin.2 hT)
    (dual_globallyHyperbolic.2 hG) (dual_causallyArcConnectedOn.2 hC) hJm hd hK
  exact ⟨-s, hs⟩

/-! ### Lemma K -/

/-- **Lemma K** (DEC-44), with its named hypotheses. On a connected Hausdorff tarentin globally
hyperbolic causally arc-connected spacetime with `J^±(p) ≠ {p}`, in which curves extend
(`CurvesExtend`) and which carries a splitting `ψ : S₀ × ℝ ≃ₜ M` with causally monotone lines
(`IsCauchySplitting`), a compact connected set which is locally Cauchy and two-sided is a Cauchy
surface. -/
theorem isCauchySurface_of_isLocallyCauchyTwoSided [T2Space M] [ConnectedSpace M]
    (hT : C.Tarentin) (hG : C.GloballyHyperbolic) (hC : C.CausallyArcConnected)
    (hJm : ∀ p : M, C.Jminus ⊤ {p} ≠ {p}) (hJp : ∀ p : M, C.Jplus ⊤ {p} ≠ {p})
    (hext : C.CurvesExtend) (hψ : C.IsCauchySplitting S₀ ψ) {S : Set M} (hSc : IsCompact S)
    (hSconn : IsConnected S) (hloc : C.IsLocallyCauchyTwoSided S) : C.IsCauchySurface S := by
  have hcaus := hG.1
  have hpt : ∀ q : M, ψ ((ψ.symm q).1, (ψ.symm q).2) = q := fun q => by
    rw [Prod.mk.eta, ψ.apply_symm_apply]
  obtain ⟨h, hcont, hgraph⟩ := exists_graph hcaus hC hext hψ hSc hSconn hloc
  have hac : C.IsAcausal S :=
    isAcausal_of_graph hcaus hC hext hψ hSc.isClosed hloc hcont hgraph
  set F : M → ℝ := fun q => (ψ.symm q).2 - h (ψ.symm q).1 with hF
  have hFc : Continuous F := (continuous_snd.comp ψ.symm.continuous).sub
    (hcont.comp (continuous_fst.comp ψ.symm.continuous))
  have hF0 : ∀ q, q ∈ S ↔ F q = 0 := fun q => by
    have := hgraph (ψ.symm q).1 (ψ.symm q).2
    rw [hpt] at this
    rw [this]
    simp only [hF, sub_eq_zero]
  have hzS : ∀ q, ψ ((ψ.symm q).1, h (ψ.symm q).1) ∈ S := fun q => (hgraph _ _).2 rfl
  -- below the graph is in `J^-(S)`, above it in `J^+(S)`
  have hFle : ∀ q, F q ≤ 0 → q ∈ C.Jminus ⊤ S := fun q hq => by
    refine ⟨_, hzS q, ?_⟩
    have := hψ.mono (ψ.symm q).1 (show (ψ.symm q).2 ≤ h (ψ.symm q).1 by
      simp only [hF] at hq; linarith)
    rwa [hpt] at this
  have hFge : ∀ q, 0 ≤ F q → q ∈ C.Jplus ⊤ S := fun q hq => by
    refine ⟨_, hzS q, ?_⟩
    have := hψ.mono (ψ.symm q).1 (show h (ψ.symm q).1 ≤ (ψ.symm q).2 by
      simp only [hF] at hq; linarith)
    rwa [hpt] at this
  intro I c hc
  obtain ⟨φ, -, -, hφr, hcφ⟩ := hc.reparam hC hcaus hJm hJp
  obtain ⟨s₁, hs₁⟩ := exists_not_mem_Jminus_of_isCompact hT hG hC hJp hcφ hSc
  obtain ⟨s₀, hs₀⟩ := exists_not_mem_Jplus_of_isCompact hT hG hC hJm hcφ hSc
  have hF1 : 0 < F ((c ∘ φ) s₁) := lt_of_not_ge fun h' => hs₁ (hFle _ h')
  have hF0' : F ((c ∘ φ) s₀) < 0 := lt_of_not_ge fun h' => hs₀ (hFge _ h')
  have h01 : s₀ ≤ s₁ := by
    by_contra hlt
    push Not at hlt
    obtain ⟨z, hz, hzc⟩ := hFge _ hF1.le
    exact hs₀ ⟨z, hz, C.le_trans hzc (hcφ.1.le_of_le trivial trivial hlt.le)⟩
  obtain ⟨s, -, hFs⟩ := intermediate_value_Icc h01
    (hFc.comp hcφ.1.continuous).continuousOn ⟨hF0'.le, hF1.le⟩
  have hφs : φ s ∈ I := hφr ▸ mem_range_self s
  have hcS : c (φ s) ∈ S := (hF0 _).2 hFs
  refine ⟨c (φ s), ⟨⟨φ s, hφs, rfl⟩, hcS⟩, ?_⟩
  rintro _ ⟨⟨t, ht, rfl⟩, htS⟩
  rcases le_total t (φ s) with hle | hle
  · exact hac _ htS _ hcS (hc.1.le_of_le ht hφs hle)
  · exact (hac _ hcS _ htS (hc.1.le_of_le hφs ht hle)).symm

/-- **Lemma K, the bare DEC-44 form — OPEN, tagged `sorry`; nothing may depend on it.** On a
connected Hausdorff tarentin globally hyperbolic causally arc-connected spacetime with
`J^±(p) ≠ {p}`, a compact connected locally Cauchy set is a Cauchy surface. This is the target gx
points at; it is proved above (`isCauchySurface_of_isLocallyCauchyTwoSided`) only under two more
data, a global splitting with causally monotone lines and two-sidedness in the charts. The
regularity hypotheses kept here are those of the proved form, all dischargeable by gx
(`SingularFlatAxioms.tarentin`, `.causallyArcConnected`, `.t2`; `J^-(p) ≠ {p}` at a BTZ point by
its past half-line); it is not known whether the statement holds in ETT generality. -/
theorem isCauchySurface_of_isLocallyCauchy [T2Space M] [ConnectedSpace M]
    (hT : C.Tarentin) (hG : C.GloballyHyperbolic) (hC : C.CausallyArcConnected)
    (hJm : ∀ p : M, C.Jminus ⊤ {p} ≠ {p}) (hJp : ∀ p : M, C.Jplus ⊤ {p} ≠ {p})
    {S : Set M} (hSc : IsCompact S) (hSconn : IsConnected S) (hloc : C.IsLocallyCauchy S) :
    C.IsCauchySurface S :=
  sorry -- SORRY(DEC-44): open in ETT generality, possibly false. (1) No global projection: without a splitting (or a covering map) of M there is nothing to compare Σ with, which is Brunswic's covering step (prop:cauchy_abs_max, BTZ_1.tex:1048-1074, uses N ≃ Σ_N × ℝ). (2) No two-sidedness: in a chart U a point of U near Σ may be related to Σ ∩ U only through points of Σ outside U, so the time window of the box step (exists_box_of_twoSided) is uncontrolled, and excluding it needs global acausality of Σ, which is the conclusion. Proved under both data as isCauchySurface_of_isLocallyCauchyTwoSided.

end Causality

/-! ### Non-vacuity: the timelike line -/

/-- On the timelike line `{0}` is locally Cauchy and two-sided. -/
theorem timelikeLine_isLocallyCauchyTwoSided_zero :
    timelikeLine.IsLocallyCauchyTwoSided ({0} : Set ℝ) := by
  refine timelikeLine_isCauchySurface_zero.isLocallyCauchyTwoSided ?_ ?_
  · rw [timelikeLine_Jplus_top_singleton, Ici_sdiff_left]; exact isOpen_Ioi
  · rw [timelikeLine_Jminus_top_singleton, Iic_sdiff_right]; exact isOpen_Iio

/-- On the timelike line every translation `p ↦ -a + p` is a strong morphism (the proof of
`timelikeLine_strongMorphism_add`, `Causal/GXStructure.lean`, not imported here). -/
theorem timelikeLine_strongMorphism_neg_add (a : ℝ) :
    StrongMorphism timelikeLine timelikeLine fun p => -a + p where
  continuous := continuous_const.add continuous_id
  isOpenMap := (Homeomorph.addLeft (-a)).isOpenMap
  map_le U V hV x y h := by
    refine ⟨by linarith [h.1], fun z hz => ?_⟩
    have hz' : z - -a ∈ (V : Set ℝ) := h.2 ⟨by linarith [hz.1], by linarith [hz.2]⟩
    rw [hV] at hz'
    simpa using hz'
  map_lt U V hV x y h := by
    refine ⟨by linarith [h.1], fun z hz => ?_⟩
    have hz' : z - -a ∈ (V : Set ℝ) := h.2 ⟨by linarith [hz.1], by linarith [hz.2]⟩
    rw [hV] at hz'
    simpa using hz'

/-- On the timelike line every point `{a}` is a Cauchy surface: `(ii)⇒(iii)` applied to the
Cauchy time function `p ↦ p - a`. -/
theorem timelikeLine_isCauchySurface_singleton (a : ℝ) :
    timelikeLine.IsCauchySurface ({a} : Set ℝ) := by
  have hT : timelikeLine.IsCauchyTimeFunction fun p => -a + p := by
    refine ⟨timelikeLine_strongMorphism_neg_add a, fun c hc => ?_⟩
    obtain ⟨h1, h2⟩ := timelikeLine_isCauchyTimeFunction_id.2 c hc
    exact ⟨tendsto_atBot_add_const_left _ (-a) h1, tendsto_atTop_add_const_left _ (-a) h2⟩
  have := hT.isCauchySurface timelikeLine_causallyArcConnected timelikeLine_stronglyCausal
    timelikeLine_Jminus_ne timelikeLine_Jplus_ne fun x y hxy hne => by
      have := lt_of_le_of_ne (timelikeLine_le.1 hxy).1 hne
      linarith
  have he : (fun p : ℝ => -a + p) ⁻¹' {0} = {a} := by
    ext p
    simp only [mem_preimage, mem_singleton_iff]
    constructor <;> intro h <;> linarith
  rwa [he] at this

/-- On the timelike line every point `{a}` is locally Cauchy and two-sided. -/
theorem timelikeLine_isLocallyCauchyTwoSided_singleton (a : ℝ) :
    timelikeLine.IsLocallyCauchyTwoSided ({a} : Set ℝ) := by
  refine (timelikeLine_isCauchySurface_singleton a).isLocallyCauchyTwoSided ?_ ?_
  · rw [timelikeLine_Jplus_top_singleton, Ici_sdiff_left]; exact isOpen_Ioi
  · rw [timelikeLine_Jminus_top_singleton, Iic_sdiff_right]; exact isOpen_Iio

/-- **The hypotheses of Lemma K are jointly satisfiable**: on the timelike line, with
`S = S₀ = {0}` and the splitting `ψ(0, t) = t`. -/
theorem timelikeLine_lemmaK_hypotheses :
    timelikeLine.Tarentin ∧ timelikeLine.GloballyHyperbolic ∧
      timelikeLine.CausallyArcConnected ∧ (∀ p : ℝ, timelikeLine.Jminus ⊤ {p} ≠ {p}) ∧
      (∀ p : ℝ, timelikeLine.Jplus ⊤ {p} ≠ {p}) ∧ timelikeLine.CurvesExtend ∧
      timelikeLine.IsCauchySplitting {0} timelikeLineSplitting ∧
      IsCompact ({0} : Set ℝ) ∧ IsConnected ({0} : Set ℝ) ∧
      timelikeLine.IsLocallyCauchyTwoSided ({0} : Set ℝ) :=
  ⟨timelikeLine_tarentin, timelikeLine_globallyHyperbolic, timelikeLine_causallyArcConnected,
    timelikeLine_Jminus_ne, timelikeLine_Jplus_ne, timelikeLine_curvesExtend,
    timelikeLine_isCauchySplitting, isCompact_singleton, isConnected_singleton,
    timelikeLine_isLocallyCauchyTwoSided_zero⟩

/-- Lemma K applied on the timelike line. -/
theorem timelikeLine_isCauchySurface_zero_of_lemmaK :
    timelikeLine.IsCauchySurface ({0} : Set ℝ) := by
  obtain ⟨hT, hG, hC, hJm, hJp, hext, hψ, hSc, hSconn, hloc⟩ := timelikeLine_lemmaK_hypotheses
  exact Causality.isCauchySurface_of_isLocallyCauchyTwoSided hT hG hC hJm hJp hext hψ hSc hSconn
    hloc

/-- **The hypotheses of Lemma K hold with `Σ ≠ S₀`**: on the timelike line, `Σ = {1}` over the
splitting `ψ(0, t) = t` along `S₀ = {0}`. -/
theorem timelikeLine_lemmaK_hypotheses_one :
    timelikeLine.Tarentin ∧ timelikeLine.GloballyHyperbolic ∧
      timelikeLine.CausallyArcConnected ∧ (∀ p : ℝ, timelikeLine.Jminus ⊤ {p} ≠ {p}) ∧
      (∀ p : ℝ, timelikeLine.Jplus ⊤ {p} ≠ {p}) ∧ timelikeLine.CurvesExtend ∧
      timelikeLine.IsCauchySplitting {0} timelikeLineSplitting ∧
      IsCompact ({1} : Set ℝ) ∧ IsConnected ({1} : Set ℝ) ∧
      timelikeLine.IsLocallyCauchyTwoSided ({1} : Set ℝ) ∧ ({1} : Set ℝ) ≠ {0} :=
  ⟨timelikeLine_tarentin, timelikeLine_globallyHyperbolic, timelikeLine_causallyArcConnected,
    timelikeLine_Jminus_ne, timelikeLine_Jplus_ne, timelikeLine_curvesExtend,
    timelikeLine_isCauchySplitting, isCompact_singleton, isConnected_singleton,
    timelikeLine_isLocallyCauchyTwoSided_singleton 1, by simp⟩

/-- Lemma K applied on the timelike line to `Σ = {1}`, over the splitting along `{0}`. -/
theorem timelikeLine_isCauchySurface_one_of_lemmaK :
    timelikeLine.IsCauchySurface ({1} : Set ℝ) := by
  obtain ⟨hT, hG, hC, hJm, hJp, hext, hψ, hSc, hSconn, hloc, -⟩ :=
    timelikeLine_lemmaK_hypotheses_one
  exact Causality.isCauchySurface_of_isLocallyCauchyTwoSided hT hG hC hJm hJp hext hψ hSc hSconn
    hloc

end Causal
