import GXScaffold.BTZ.Rigid
import GXScaffold.BTZ.Causality
import Causal.CBG.Geometry
import Causal.CBG.FromModel
import Causal.SingularGeroch
import Causal.Flat.CBGCompact
import Causal.Flat.CauchyComplete
import Causal.Flat.CBG
import Causal.CurvesExtend
import Causal.Flat.Geroch.ChartNull
import Causal.Flat.Geroch.ConeNull
import Causal.LevinUtility
import Causal.Flat.SecondCountable

/-!
# `GXScaffold.BTZ.LocalModel` — the CBG local model `𝔐E₀` for `Y = 𝕄 ⊕ 𝔼₀`

L. Brunswic, *On branched coverings of singular (G,X)-manifolds*, §4 (`papers/gx`), with
`brunswic2021cauchy` (B21, `papers/gx/sources/2108.12631`). Package WP-41f (WAVE5-PLAN.md, WP-39f):
the instance data of `Causal.CBG.LocalModel` (lean-causal `ca2ad78`, `Causal/CBG/Geometry.lean`)
for `Y = 𝕄 ⊕ 𝔼₀` (`GX.E0Y`), `G` the a.e.-isomorphisms (`GX.e0Groupoid`), `singY = GX.e0SingY`,
the causality `GX.E0.causalityYBTZ` (`D`). **No ledger label is marked.** One row is touched,
unmarked: `lem:manifolds_manifolds_causally_connected` (`RamcovGX.tex:2329`), **partial** — the
`BTZ`-manifold half is proved with no hypothesis (`GX.E0LM.e0_causallyArcConnected`), the
`BTZ̃`-manifold half is not covered.

> **Lemma** (`lem:manifolds_manifolds_causally_connected`). $\BTZ$-manifolds and
> $\BTZtilde$-manifolds are causally connected. (`RamcovGX.tex:2329`; "causally connected",
> `def:singular_manifold_endowed_causal` l.2319: $x\le y$ gives a future causal path from $x$ to $y$.)

## What is built

* **`GX.E0LM.e0LocalModelOf` (sorry-free)** — the `LocalModel` from three obligations: the BTZ
  line of every admissible `M` (`hLine`), `secondCountable_of_cauchy` (`hSC`), `typeAgreement`
  (`hTA`). Every other field is proved: `singularFlatAxioms` (18 of its 19 fields; `line` is
  `hLine`), **`timeFunction` and `curvesExtend` by Levin's theorem** (strict
  `Causal.LevinUtility`, from tarentinity `charted_tarentin` and GH; **independent of `hLine`**,
  §5c), `isCompact_*` (Flat/CBGCompact template, through SFA), and the local fields (WP-41c,
  WP-41e; `chartIso_mem` is WP-41e's `E0.chartIso_mem_e0Groupoid`; `localUnique_sing_adherent`
  §6b).
* **§5c `Reg M` is second countable** for every Hausdorff connected `𝔼₀`-manifold, with no second
  countability asked of `M` (`e0RegM_secondCountable`): `Reg M` is a flat
  `(Isom 𝐌³, 𝐌³)`-manifold (`e0RegM_chartedSpace`, `e0RegM_hasGroupoid`; transitions
  `e0_flat_transition_mem`) and connected (`isPreconnected_e0RegM`: the BTZ lines do not disconnect
  `M`), so the strict `Causal.Flat.flat_secondCountableTopology` (DEC-49) applies. **(O4) is
  reduced to the line step** `E0LineStep` (`e0_secondCountable_of_lineStep`, sorry-free).
* **§5b `ModelMeasures` on every GH `𝔼₀`-manifold** (`e0_modelMeasures_of`, `ETT.tex:1736–1745`),
  proved (round 1); no longer consumed by the assembly.
* **§6c `typeAgreement` is FALSE for `𝔐E₀`** (`e0_not_typeAgreement`, WP-41c's counterexample,
  DEC-27; the field is unchanged at `ca2ad78`); its convergence form holds
  (`e0_typeAgreementTendsto`), and verbatim at tips in `𝕄` (`e0_typeAgreement_inl`). So **no
  `LocalModel` with this data exists** until the interface restates the field;
  `e0LocalModel_of_typeAgreement` is the instance given it.
* §1–§5 (round 0): the model's causal facts in every open set, their transfer to every admissible
  `M` (`charted_*`), SFA on `𝔼₀`-manifolds, `J^±` facts, R1.

## Hypothesis checklist

| paper / field | here |
|---|---|
| `BTZ`-manifold | ✓ read: `ChartedSpace E0Y M`, `HasGroupoid M e0Groupoid`, causality `chartedCausality D M` |
| causally connected (l.2319) | ✓ read: `CausallyArcConnected` (`≤` and `≪`, every open set; stronger) |
| `BTZ̃`-manifolds (l.2329) | ✗ not covered |
| `singularFlatAxioms` (B21 Lemma 1.9, `BTZ_1.tex:535`) | ⚠ 18/19 fields; `line` is (O2) |
| `timeFunction`, `curvesExtend` | ✓ (Levin, no `hLine`) |
| `isCompact_*` | ✓ given SFA (hence ⚠ through (O2)) |
| `secondCountable_of_cauchy` | ⚠ reduced to the line step (O4′); `Reg M` second countable ✓ |
| `typeAgreement` | ✗ **false** (`e0_not_typeAgreement`); convergence form ✓ |

## SCOPE (disclosed; §7's two tagged `sorry`s)

* (O2) `e0_globalBTZ`, the SFA field `line` (`M` second countable): `sing₀(M)` is a 1-manifold with
  causally increasing charts (`e0_line_piece`); its global parametrisation by `ℝ` is the
  classification of connected second-countable Hausdorff 1-manifolds, absent from mathlib. Two
  routes not attempted: (i) order-theoretic — `e0_line_piece` gives totally ordered local pieces;
  a countable dense subset of a component and back-and-forth give an order isomorphism with `ℝ`,
  the `S¹` case split off by non-causality; (ii) developing — the axis-preserving transitions
  (`IsAxisAff`, WP-41c) give each component an `(Aff⁺(ℝ), ℝ)`-structure, whose developing map is
  injective (a local homeomorphism of a connected 1-manifold into `ℝ` is monotone).
* (O4′) `e0_lineStep_of_cauchy` (`M` **not** second countable; GH, a second-countable Cauchy
  surface): every component of `sing₀(M)` is an inextensible causal `ℝ`-curve. With it, (O4)
  `e0_secondCountable_of_cauchy` is proved. The round-0 diagnosis ("needs the developing theorem for
  `Reg M`") is withdrawn: `Reg M` is proved second countable here. What is left is excluding a
  non-σ-compact BTZ component without second countability of `M` (route (ii) above gives it), then
  (O2)'s parametrisation and inextensibility. The interface question narrows to this step.
* Round 0's (O1) `chartIso_mem` and (O3) `ModelMeasures` are closed (§6d); (O5) is refuted (§6c).
* `sorry` tags read `SORRY(WP-41f:<field>)`: the obligations are CBG-interface fields, not ledger
  rows, so no ledger label applies.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`; lean-causal `ca2ad78`
(`lake-manifest.json`).
-/

namespace GX

open Set Filter Topology Function TopologicalSpace
open scoped Real

namespace E0LM

/-! ### §1 The two descriptions of the BTZ locus of `Y` agree -/

attribute [local instance] btzE0Structure

theorem toPaper_orbitMk_snd (y : DInfty × ℝ) :
    (E0.toPaper (orbitMk (GammaA (2 * π)) y)).2 = (starRingEnd ℂ) (DInfty.cplx (2 * π) y.1) := by
  show (E0.paperCoords (cylHomeomorph btz_two_pi_ne_zero ℝ _)).2 = _
  rw [cylHomeomorph_apply]; rfl

theorem toPaper_orbitMk_snd_ne_zero_iff (y : DInfty × ℝ) :
    (E0.toPaper (orbitMk (GammaA (2 * π)) y)).2 ≠ 0 ↔ 0 < y.1.r := by
  rw [toPaper_orbitMk_snd, Ne, map_eq_zero, ← norm_eq_zero, DInfty.norm_cplx]
  exact ⟨fun h => lt_of_le_of_ne y.1.r_nonneg (Ne.symm h), fun h => h.ne'⟩

/-- A point of Model's `𝔼₀` is regular iff its paper coordinate `z` is non-zero. -/
theorem mem_reg_btzE0_iff (x : BTZE0) :
    x ∈ Reg (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0 ↔ (E0.toPaper x).2 ≠ 0 := by
  rw [btzE0_reg_eq]
  obtain ⟨y, rfl⟩ := Quotient.mk_surjective x
  constructor
  · rintro ⟨y', hy', he⟩
    have := (toPaper_orbitMk_snd_ne_zero_iff y').2 hy'
    rwa [show orbitMk (GammaA (2 * π)) y' = Quotient.mk _ y from he] at this
  · intro h
    exact ⟨y, (toPaper_orbitMk_snd_ne_zero_iff y).1 h, rfl⟩

/-- **The regular part of `Y`** (Rigid's `e0Reg`, from the atlas) is the complement of the BTZ
locus of Causality's `singY0`, read through `toPaperY`. -/
theorem mem_e0Reg_iff (y : E0Y) : y ∈ e0Reg ↔ E0.toPaperY y ∉ E0.singY0 := by
  rcases y with m | x
  · simp only [inl_mem_e0Reg, true_iff]
    rintro ⟨a, -, ha⟩
    exact Sum.inr_ne_inl ha
  · rw [inr_mem_e0Reg_iff, mem_reg_btzE0_iff]
    show _ ↔ Sum.inr (E0.toPaper x) ∉ Sum.inr '' E0.axis
    rw [(Sum.inr_injective).mem_set_image]
    rfl

/-- **`sing_0` of Rigid's model is Causality's BTZ locus**: `e0SingY 0 = toPaperY ⁻¹' singY0`. -/
theorem e0SingY_zero : e0SingY 0 = E0.toPaperY ⁻¹' E0.singY0 := by
  ext y
  show (0:ℝ) = 0 ∧ y ∉ e0Reg ↔ E0.toPaperY y ∈ E0.singY0
  rw [mem_e0Reg_iff, not_not]
  exact ⟨fun h => h.2, fun h => ⟨rfl, h⟩⟩

theorem e0SingY_of_ne {α : ℝ} (h : α ≠ 0) : e0SingY α = ∅ := by
  ext y; simp [e0SingY, h]


theorem toPaper_orbitMk_fst (y : DInfty × ℝ) :
    (E0.toPaper (orbitMk (GammaA (2 * π)) y)).1 = y.2 / 2 := by
  show (E0.paperCoords (cylHomeomorph btz_two_pi_ne_zero ℝ _)).1 = _
  rw [cylHomeomorph_apply]; rfl

theorem rad_toPaper_orbitMk (y : DInfty × ℝ) :
    E0.rad (E0.toPaper (orbitMk (GammaA (2 * π)) y)) = y.1.r := by
  rw [E0.rad, toPaper_orbitMk_snd, Complex.norm_conj, DInfty.norm_cplx]

/-! ### §2 Local forms of the model's causal facts, in every open set -/

section Local

variable {X : Type*} [TopologicalSpace X]

/-- `Z⁺` in every open set: at every `y ∈ W`, `I⁺_W(y)` meets every neighbourhood of `y`. -/
def LocZplus (D : Causal.Causality X) : Prop :=
  ∀ (W : Opens X) (y : X), y ∈ W → ∀ N ∈ 𝓝 y, ∃ z ∈ N, D.lt W y z

/-- `Z⁻` off `S` in every open set. -/
def LocZminus (D : Causal.Causality X) (S : Set X) : Prop :=
  ∀ (W : Opens X) (y : X), y ∈ W → y ∉ S → ∀ N ∈ 𝓝 y, ∃ z ∈ N, D.lt W z y

/-- Tarentin in every open set: small open diamonds of `W` around every point. -/
def LocTarentin (D : Causal.Causality X) : Prop :=
  ∀ (W : Opens X) (y : X), y ∈ W → ∀ N ∈ 𝓝 y, ∃ p ∈ N, ∃ q ∈ N, y ∈ D.openDiamond W p q

/-- No chronological past at the points of `S`, in every open set. -/
def LocNoPast (D : Causal.Causality X) (S : Set X) : Prop :=
  ∀ (W : Opens X) (y : X), y ∈ S → ∀ z, ¬ D.lt W z y

/-- The causal past of a point of `S` stays in `S`, in every open set. -/
def LocPastIn (D : Causal.Causality X) (S : Set X) : Prop :=
  ∀ (W : Opens X) (y : X), y ∈ S → ∀ z, D.le W z y → z ∈ S

variable {D : Causal.Causality X}

/-- In a causally arc-connected spacetime, the relations of `⊤` between two points of a causally
convex set `V ⊆ W` are relations of `W` (the realising curve stays in the diamond, so in `V`). -/
theorem rel_of_causallyConvex (hD : D.CausallyArcConnected) {V : Set X}
    (hV : D.CausallyConvexIn V ⊤) {W : Opens X} (hVW : V ⊆ W) {y z : X} (hy : y ∈ V)
    (hz : z ∈ V) : (D.le ⊤ y z → D.le W y z) ∧ (D.lt ⊤ y z → D.lt W y z) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨c, hc, h0, h1⟩ := (hD ⊤ le_rfl y z).1.1 h
    subst h0; subst h1
    have hmem : ∀ t ∈ Icc (0 : ℝ) 1, c t ∈ W := fun t ht =>
      hVW (hV.2 _ hy _ hz (Causal.Causality.mem_diamond.2
        ⟨hc.le_of_le le_rfl ht.1 ht.2, hc.le_of_le ht.1 ht.2 le_rfl⟩))
    have hcW : D.CausalCurveOn W c 0 1 := Causal.CurveOn.restrict hc le_rfl le_rfl le_top hmem
    exact hcW.le_of_le le_rfl zero_le_one le_rfl
  · obtain ⟨c, hc, h0, h1⟩ := (hD ⊤ le_rfl y z).2.1 h
    subst h0; subst h1
    have hc' := hc.causalCurveOn
    have hmem : ∀ t ∈ Icc (0 : ℝ) 1, c t ∈ W := fun t ht =>
      hVW (hV.2 _ hy _ hz (Causal.Causality.mem_diamond.2
        ⟨hc'.le_of_le le_rfl ht.1 ht.2, hc'.le_of_le ht.1 ht.2 le_rfl⟩))
    have hcW : D.ChronalCurveOn W c 0 1 := Causal.CurveOn.restrict hc le_rfl le_rfl le_top hmem
    exact hcW.lt_of_lt le_rfl zero_lt_one le_rfl

theorem locZplus_of (hD : D.CausallyArcConnected) (hSC : D.StronglyCausal)
    (hZ : ∀ y, y ∈ D.Zplus) : LocZplus D := by
  intro W y hy N hN
  obtain ⟨V, hV, hVsub, hVc⟩ := hSC y (N ∩ W) (inter_mem hN (W.isOpen.mem_nhds hy))
  obtain ⟨z, hzI, hzV⟩ := hZ y V hV
  exact ⟨z, (hVsub hzV).1, (rel_of_causallyConvex hD hVc (fun w hw => (hVsub hw).2)
    (mem_of_mem_nhds hV) hzV).2 (Causal.Precausality.mem_Iplus_singleton.1 hzI)⟩

theorem locZminus_of (hD : D.CausallyArcConnected) (hSC : D.StronglyCausal) {S : Set X}
    (hZ : ∀ y, y ∉ S → y ∈ D.Zminus) : LocZminus D S := by
  intro W y hy hyS N hN
  obtain ⟨V, hV, hVsub, hVc⟩ := hSC y (N ∩ W) (inter_mem hN (W.isOpen.mem_nhds hy))
  obtain ⟨z, hzI, hzV⟩ := hZ y hyS V hV
  exact ⟨z, (hVsub hzV).1, (rel_of_causallyConvex hD hVc (fun w hw => (hVsub hw).2)
    hzV (mem_of_mem_nhds hV)).2 (Causal.Precausality.mem_Iminus_singleton.1 hzI)⟩

theorem locTarentin_of (hD : D.CausallyArcConnected) (hSC : D.StronglyCausal)
    (hT : D.Tarentin) : LocTarentin D := by
  intro W y hy N hN
  obtain ⟨V, hV, hVsub, hVc⟩ := hSC y (N ∩ W) (inter_mem hN (W.isOpen.mem_nhds hy))
  obtain ⟨p, hp, q, hq, hyd⟩ := hT y V hV
  refine ⟨p, (hVsub hp).1, q, (hVsub hq).1, interior_mono (fun w hw => ?_) hyd⟩
  have hwV : w ∈ V := hVc.2 p hp q hq hw
  obtain ⟨h1, h2⟩ := Causal.Causality.mem_diamond.1 hw
  exact Causal.Causality.mem_diamond.2
    ⟨(rel_of_causallyConvex hD hVc (fun w hw => (hVsub hw).2) hp hwV).1 h1,
      (rel_of_causallyConvex hD hVc (fun w hw => (hVsub hw).2) hwV hq).1 h2⟩

end Local


/-! ### §2b The local forms for `𝔼₀`, `𝕄`, sums, transports, and `Y = 𝕄 ⊕ BTZE0` -/

section LocalModelFacts

theorem e0_locZplus : LocZplus E0.causality :=
  locZplus_of E0.causallyArcConnected E0.stronglyCausal E0.mem_Zplus

theorem e0_locZminus : LocZminus E0.causality E0.axis :=
  locZminus_of E0.causallyArcConnected E0.stronglyCausal fun y hy => (E0.mem_Zminus_iff y).2 hy

theorem e0_locTarentin : LocTarentin E0.causality :=
  locTarentin_of E0.causallyArcConnected E0.stronglyCausal E0.tarentin

theorem e0_locNoPast : LocNoPast E0.causality E0.axis := fun W _ hy z hz => by
  have h := Causal.Precausality.mem_Iminus_singleton.2 hz
  rw [E0.Iminus_axis hy W] at h
  exact notMem_empty z h

theorem e0_locPastIn : LocPastIn E0.causality E0.axis := fun W _ hy _ hz =>
  E0.Jminus_axis_subset hy W (Causal.Precausality.mem_Jminus_singleton.2 hz)

theorem mink_locZplus : LocZplus (Causal.minkowski 2) :=
  locZplus_of Causal.minkowski_causallyArcConnected Causal.minkowski_stronglyCausal
    fun y => by rw [Causal.minkowski_Zplus]; trivial

theorem mink_locZminus : LocZminus (Causal.minkowski 2) ∅ :=
  locZminus_of Causal.minkowski_causallyArcConnected Causal.minkowski_stronglyCausal
    fun y _ => by rw [Causal.minkowski_Zminus]; trivial

theorem mink_locTarentin : LocTarentin (Causal.minkowski 2) :=
  locTarentin_of Causal.minkowski_causallyArcConnected Causal.minkowski_stronglyCausal
    Causal.minkowski_tarentin

section Sum

variable {M₁ M₂ : Type*} [TopologicalSpace M₁] [TopologicalSpace M₂]
  {C₁ : Causal.Causality M₁} {C₂ : Causal.Causality M₂}

theorem sum_locZplus (h₁ : LocZplus C₁) (h₂ : LocZplus C₂) :
    LocZplus (E0.sumCausality C₁ C₂) := by
  intro W y hy N hN
  rcases y with a | a
  · obtain ⟨z, hz, hlt⟩ := h₁ (E0.leftOpens W) a hy _ (continuous_inl.continuousAt.preimage_mem_nhds hN)
    exact ⟨Sum.inl z, hz, hlt⟩
  · obtain ⟨z, hz, hlt⟩ := h₂ (E0.rightOpens W) a hy _ (continuous_inr.continuousAt.preimage_mem_nhds hN)
    exact ⟨Sum.inr z, hz, hlt⟩

theorem sum_locZminus {S₂ : Set M₂} (h₁ : LocZminus C₁ ∅) (h₂ : LocZminus C₂ S₂) :
    LocZminus (E0.sumCausality C₁ C₂) (Sum.inr '' S₂) := by
  intro W y hy hyS N hN
  rcases y with a | a
  · obtain ⟨z, hz, hlt⟩ := h₁ (E0.leftOpens W) a hy (notMem_empty a) _
      (continuous_inl.continuousAt.preimage_mem_nhds hN)
    exact ⟨Sum.inl z, hz, hlt⟩
  · obtain ⟨z, hz, hlt⟩ := h₂ (E0.rightOpens W) a hy (fun h => hyS ⟨a, h, rfl⟩) _
      (continuous_inr.continuousAt.preimage_mem_nhds hN)
    exact ⟨Sum.inr z, hz, hlt⟩

theorem sum_diamond_inl {W : Opens (M₁ ⊕ M₂)} {p q : M₁} :
    Sum.inl '' C₁.diamond (E0.leftOpens W) p q ⊆ (E0.sumCausality C₁ C₂).diamond W (.inl p) (.inl q) := by
  rintro _ ⟨w, hw, rfl⟩
  obtain ⟨h1, h2⟩ := Causal.Causality.mem_diamond.1 hw
  exact Causal.Causality.mem_diamond.2 ⟨h1, h2⟩

theorem sum_diamond_inr {W : Opens (M₁ ⊕ M₂)} {p q : M₂} :
    Sum.inr '' C₂.diamond (E0.rightOpens W) p q ⊆ (E0.sumCausality C₁ C₂).diamond W (.inr p) (.inr q) := by
  rintro _ ⟨w, hw, rfl⟩
  obtain ⟨h1, h2⟩ := Causal.Causality.mem_diamond.1 hw
  exact Causal.Causality.mem_diamond.2 ⟨h1, h2⟩

theorem sum_locTarentin (h₁ : LocTarentin C₁) (h₂ : LocTarentin C₂) :
    LocTarentin (E0.sumCausality C₁ C₂) := by
  intro W y hy N hN
  rcases y with a | a
  · obtain ⟨p, hp, q, hq, hd⟩ := h₁ (E0.leftOpens W) a hy _
      (continuous_inl.continuousAt.preimage_mem_nhds hN)
    refine ⟨Sum.inl p, hp, Sum.inl q, hq, ?_⟩
    have hopen : IsOpen (Sum.inl '' interior (C₁.diamond (E0.leftOpens W) p q) : Set (M₁ ⊕ M₂)) :=
      isOpenMap_inl _ isOpen_interior
    exact interior_maximal ((image_mono interior_subset).trans sum_diamond_inl) hopen ⟨a, hd, rfl⟩
  · obtain ⟨p, hp, q, hq, hd⟩ := h₂ (E0.rightOpens W) a hy _
      (continuous_inr.continuousAt.preimage_mem_nhds hN)
    refine ⟨Sum.inr p, hp, Sum.inr q, hq, ?_⟩
    have hopen : IsOpen (Sum.inr '' interior (C₂.diamond (E0.rightOpens W) p q) : Set (M₁ ⊕ M₂)) :=
      isOpenMap_inr _ isOpen_interior
    exact interior_maximal ((image_mono interior_subset).trans sum_diamond_inr) hopen ⟨a, hd, rfl⟩

theorem sum_locNoPast {S₂ : Set M₂} (h₂ : LocNoPast C₂ S₂) :
    LocNoPast (E0.sumCausality C₁ C₂) (Sum.inr '' S₂) := by
  rintro W _ ⟨b, hb, rfl⟩ z hz
  rcases z with c | c
  · exact hz
  · exact h₂ (E0.rightOpens W) b hb c hz

theorem sum_locPastIn {S₂ : Set M₂} (h₂ : LocPastIn C₂ S₂) :
    LocPastIn (E0.sumCausality C₁ C₂) (Sum.inr '' S₂) := by
  rintro W _ ⟨b, hb, rfl⟩ z hz
  rcases z with c | c
  · exact hz.elim
  · exact ⟨c, h₂ (E0.rightOpens W) b hb c hz, rfl⟩

end Sum

section Transport

variable {X Z : Type*} [TopologicalSpace X] [TopologicalSpace Z] {e : X ≃ₜ Z}
  {C : Causal.Causality Z}

theorem mem_opensImage {U : Opens X} {x : X} (hx : x ∈ U) : e x ∈ E0.opensImage e U := ⟨x, hx, rfl⟩

theorem transport_locZplus (h : LocZplus C) : LocZplus (E0.transportCausality e C) := by
  intro W y hy N hN
  obtain ⟨z', hz', hlt⟩ := h (E0.opensImage e W) (e y) (mem_opensImage hy) _ (e.isOpenMap.image_mem_nhds hN)
  obtain ⟨z, hz, rfl⟩ := hz'
  exact ⟨z, hz, hlt⟩

theorem transport_locZminus {S : Set Z} (h : LocZminus C S) :
    LocZminus (E0.transportCausality e C) (e ⁻¹' S) := by
  intro W y hy hyS N hN
  obtain ⟨z', hz', hlt⟩ := h (E0.opensImage e W) (e y) (mem_opensImage hy) hyS _
    (e.isOpenMap.image_mem_nhds hN)
  obtain ⟨z, hz, rfl⟩ := hz'
  exact ⟨z, hz, hlt⟩

theorem transport_locTarentin (h : LocTarentin C) : LocTarentin (E0.transportCausality e C) := by
  intro W y hy N hN
  obtain ⟨p', hp', q', hq', hd⟩ := h (E0.opensImage e W) (e y) (mem_opensImage hy) _
    (e.isOpenMap.image_mem_nhds hN)
  obtain ⟨p, hp, rfl⟩ := hp'
  obtain ⟨q, hq, rfl⟩ := hq'
  refine ⟨p, hp, q, hq, ?_⟩
  have hsub : e ⁻¹' C.diamond (E0.opensImage e W) (e p) (e q) ⊆
      (E0.transportCausality e C).diamond W p q := fun w hw => by
    obtain ⟨h1, h2⟩ := Causal.Causality.mem_diamond.1 hw
    exact Causal.Causality.mem_diamond.2 ⟨h1, h2⟩
  exact interior_mono hsub (preimage_interior_subset_interior_preimage e.continuous hd)

theorem transport_locNoPast {S : Set Z} (h : LocNoPast C S) :
    LocNoPast (E0.transportCausality e C) (e ⁻¹' S) := fun W y hy z hz =>
  h (E0.opensImage e W) (e y) hy (e z) hz

theorem transport_locPastIn {S : Set Z} (h : LocPastIn C S) :
    LocPastIn (E0.transportCausality e C) (e ⁻¹' S) := fun W y hy z hz =>
  h (E0.opensImage e W) (e y) hy (e z) hz

end Transport

/-- The model causality of `Y = 𝕄 ⊕ BTZE0`, the one the local model carries. -/
noncomputable abbrev D : Causal.Causality E0Y := E0.causalityYBTZ

theorem yb_locZplus : LocZplus D :=
  transport_locZplus (sum_locZplus mink_locZplus e0_locZplus)

theorem yb_locZminus : LocZminus D (e0SingY 0) := by
  rw [e0SingY_zero]
  exact transport_locZminus (sum_locZminus mink_locZminus e0_locZminus)

theorem yb_locTarentin : LocTarentin D :=
  transport_locTarentin (sum_locTarentin mink_locTarentin e0_locTarentin)

theorem yb_locNoPast : LocNoPast D (e0SingY 0) := by
  rw [e0SingY_zero]
  exact transport_locNoPast (sum_locNoPast e0_locNoPast)

theorem yb_locPastIn : LocPastIn D (e0SingY 0) := by
  rw [e0SingY_zero]
  exact transport_locPastIn (sum_locPastIn e0_locPastIn)

end LocalModelFacts


/-! ### §2c Push-up in every open set of `𝔼₀`, of `Y` (WP-41e SCOPE (d)) -/

section PushUpGeneric

variable {X : Type*} [TopologicalSpace X] {C : Causal.Causality X}

/-- A chart isomorphism onto a model with push-up gives push-up on its source. -/
theorem pushUpOn_of_chartIso {Z : Type*} [TopologicalSpace Z] {D : Causal.Causality Z}
    {e : OpenPartialHomeomorph X Z} (h : Causal.ChartIso C D e) (hD : D.PushUp) :
    C.PushUpOn (Causal.chartSource e) := by
  intro U hU x y z
  refine ⟨fun h₁ h₂ => ?_, fun h₁ h₂ => ?_⟩
  · have hx := C.lt_mem_left h₁
    have hy := C.lt_mem_right h₁
    have hz := C.le_mem_right h₂
    exact ((h U hU x hx z hz).2).2 (hD.lt_of_lt_of_le ((h U hU x hx y hy).2.1 h₁)
      ((h U hU y hy z hz).1.1 h₂))
  · have hx := C.le_mem_left h₁
    have hy := C.le_mem_right h₁
    have hz := C.lt_mem_right h₂
    exact ((h U hU x hx z hz).2).2 (hD.lt_of_le_of_lt ((h U hU x hx y hy).1.1 h₁)
      ((h U hU y hy z hz).2.1 h₂))

/-- **The push-up step through a link** (`lem:pushup_local`'s one step): `x ≪_U b` and
`b ≤_{U ⊓ O} b'` with push-up on `O` give `x ≪_U b'`. -/
theorem lt_of_lt_of_le_link (hC : C.CausallyArcConnected) {O U : Opens X} (hO : C.PushUpOn O)
    {x b b' : X} (h₁ : C.lt U x b) (h₂ : C.le (U ⊓ O) b b') : C.lt U x b' := by
  obtain ⟨γ, hγ, hγ0, hγ1⟩ := (hC U le_top x b).2.1 h₁
  have hbN : γ 1 ∈ U ⊓ O := by rw [hγ1]; exact C.le_mem_left h₂
  obtain ⟨l, u, hl, hu, hrel⟩ := hγ.rel 1 ⟨zero_le_one, le_rfl⟩ (U ⊓ O) inf_le_left hbN
  have hmax : max l 0 < 1 := max_lt hl zero_lt_one
  obtain ⟨s, hs1, hs2⟩ := exists_between hmax
  have hl_s : l < s := (le_max_left _ _).trans_lt hs1
  have h0_s : 0 < s := (le_max_right _ _).trans_lt hs1
  have hz' : C.lt (U ⊓ O) (γ s) (γ 1) :=
    hrel s ⟨h0_s.le, hs2.le⟩ 1 ⟨zero_le_one, le_rfl⟩ hl_s hs2 hu
  rw [hγ1] at hz'
  have hz'w : C.lt (U ⊓ O) (γ s) b' := ((hO (U ⊓ O) inf_le_right).1 hz' h₂)
  have hyz' : C.lt U (γ 0) (γ s) := hγ.lt_of_lt le_rfl h0_s hs2.le
  rw [hγ0] at hyz'
  exact C.lt_trans hyz' (C.lt_mono inf_le_left hz'w)

/-- **The push-up step through a link, past form** (`C.dual`). -/
theorem lt_of_le_link_of_lt (hC : C.CausallyArcConnected) {O U : Opens X} (hO : C.PushUpOn O)
    {b b' z : X} (h₁ : C.le (U ⊓ O) b b') (h₂ : C.lt U b' z) : C.lt U b z :=
  lt_of_lt_of_le_link (C := C.dual) (Causal.Causality.dual_causallyArcConnectedOn.2 hC)
    (Causal.Causality.dual_pushUpOn.2 hO) h₂ h₁

/-- **Real induction, downward**: a property of `[0,1]` true at `1`, open downward, and passing
to `t` from `(t, 1]`, holds at `0`. -/
theorem prop_zero_of_down {P : ℝ → Prop} (h1 : P 1)
    (hopen : ∀ t ∈ Icc (0 : ℝ) 1, P t → ∃ η > 0, ∀ s ∈ Icc (0 : ℝ) 1, t - η < s → s ≤ t → P s)
    (hstep : ∀ t ∈ Ico (0 : ℝ) 1, (∀ s ∈ Ioc t 1, P s) → P t) : P 0 := by
  set A := {t ∈ Icc (0 : ℝ) 1 | ∀ s ∈ Icc t 1, P s} with hA
  have hAne : A.Nonempty := ⟨1, ⟨zero_le_one, le_rfl⟩, fun s hs => by
    rw [le_antisymm hs.2 hs.1]; exact h1⟩
  have hAbdd : BddBelow A := ⟨0, fun t ht => ht.1.1⟩
  set m := sInf A
  have hm0 : 0 ≤ m := le_csInf hAne fun t ht => ht.1.1
  have hm1 : m ≤ 1 := csInf_le hAbdd ⟨⟨zero_le_one, le_rfl⟩, fun s hs => by
    rw [le_antisymm hs.2 hs.1]; exact h1⟩
  have habove : ∀ s ∈ Ioc m 1, P s := by
    intro s hs
    obtain ⟨a, haA, has⟩ := (csInf_lt_iff hAbdd hAne).1 hs.1
    exact haA.2 s ⟨has.le, hs.2⟩
  have hPm : P m := by
    rcases hm1.lt_or_eq with h | h
    · exact hstep m ⟨hm0, h⟩ habove
    · rw [h]; exact h1
  rcases hm0.lt_or_eq with hpos | hzero
  · exfalso
    obtain ⟨η, hη, hη'⟩ := hopen m ⟨hm0, hm1⟩ hPm
    set m' := max (m - η / 2) 0
    have hm'A : m' ∈ A := by
      refine ⟨⟨le_max_right _ _, (max_le (by linarith) zero_le_one)⟩, fun s hs => ?_⟩
      rcases le_or_gt s m with hsm | hsm
      · refine hη' s ⟨hs.1.trans' (le_max_right _ _), hs.2⟩ ?_ hsm
        have := hs.1
        have : m - η / 2 ≤ m' := le_max_left _ _
        linarith
      · exact habove s ⟨hsm, hs.2⟩
    have := csInf_le hAbdd hm'A
    have : m' < m := max_lt (by linarith) hpos
    linarith
  · rw [hzero]; exact hPm

/-- **Real induction, upward** (from `prop_zero_of_down` by `t ↦ 1 − t`). -/
theorem prop_one_of_up {P : ℝ → Prop} (h0 : P 0)
    (hopen : ∀ t ∈ Icc (0 : ℝ) 1, P t → ∃ η > 0, ∀ s ∈ Icc (0 : ℝ) 1, t ≤ s → s < t + η → P s)
    (hstep : ∀ t ∈ Ioc (0 : ℝ) 1, (∀ s ∈ Ico 0 t, P s) → P t) : P 1 := by
  have := prop_zero_of_down (P := fun t => P (1 - t)) (by simpa using h0)
    (fun t ht hPt => by
      obtain ⟨η, hη, h⟩ := hopen (1 - t) ⟨by linarith [ht.2], by linarith [ht.1]⟩ hPt
      refine ⟨η, hη, fun s hs h1 h2 => h (1 - s) ⟨by linarith [hs.2], by linarith [hs.1]⟩
        (by linarith) (by linarith)⟩)
    (fun t ht hP => hstep (1 - t) ⟨by linarith [ht.2], by linarith [ht.1]⟩ fun s hs => by
      have := hP (1 - s) ⟨by linarith [hs.2], by linarith [hs.1]⟩
      simpa using this)
  simpa using this

/-- A property `w ↦ w ∈ V`, `V` open, along a curve, is open in the parameter. -/
theorem exists_eta_of_mem_open {δ : ℝ → X} (hδ : ContinuousOn δ (Icc 0 1)) {V : Set X}
    (hV : IsOpen V) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (htV : δ t ∈ V) :
    ∃ η > 0, ∀ s ∈ Icc (0 : ℝ) 1, |s - t| < η → δ s ∈ V := by
  have h := (hδ t ht).preimage_mem_nhdsWithin (hV.mem_nhds htV)
  obtain ⟨η, hη, hball⟩ := Metric.mem_nhdsWithin_iff.1 h
  exact ⟨η, hη, fun s hs hst => hball ⟨by rwa [Metric.mem_ball, Real.dist_eq], hs⟩⟩

end PushUpGeneric


section E0PushUp

theorem e0_pushUpOn_sector {a : E0} (ha : a.2 ≠ 0) :
    E0.causality.PushUpOn (Causal.chartSource (E0.sectorChart a ha)) :=
  pushUpOn_of_chartIso (E0.chartIso_sectorChart ha) Causal.minkowski_pushUp

theorem e0_mem_sector_source {a : E0} (ha : a.2 ≠ 0) :
    a ∈ Causal.chartSource (E0.sectorChart a ha) := E0.mem_sector_self ha

/-- **Push-up in every open set of `𝔼₀`, first form**: `x ≪_U y ≤_U z ⇒ x ≪_U z`. Along a causal
curve from `y` to `z` (regular, `y` having a chronological past), each point is reached through a
sector chart, where Minkowski's push-up holds. -/
theorem e0_lt_of_lt_of_le {U : Opens E0} {x y z : E0} (h₁ : E0.causality.lt U x y) (h₂ : E0.causality.le U y z) :
    E0.causality.lt U x z := by
  obtain ⟨δ, hδ, hδ0, hδ1⟩ := (E0.causallyArcConnected U le_top y z).1.1 h₂
  have hy : y ∉ E0.axis := fun hy => e0_locNoPast U y hy x h₁
  have hcont := hδ.continuousOn E0.causality.isRelFamily_le
  have key := prop_one_of_up (P := fun t => E0.causality.lt U x (δ t)) (by simpa [hδ0] using h₁)
    (fun t ht hPt => by
      obtain ⟨η, hη, h⟩ := exists_eta_of_mem_open hcont (E0.causality.isOpen_lt_right U x) ht hPt
      exact ⟨η, hη, fun s hs h1 h2 => h s hs (by rw [abs_lt]; constructor <;> linarith)⟩)
    (fun t ht hP => by
      have hta : δ t ∉ E0.axis := by
        intro hax
        have hyt : E0.causality.le U y (δ t) := by
          have := hδ.le_of_le le_rfl ht.1.le ht.2
          rwa [hδ0] at this
        exact hy (e0_locPastIn U (δ t) hax y hyt)
      have ha : (δ t).2 ≠ 0 := hta
      set O := Causal.chartSource (E0.sectorChart (δ t) ha)
      obtain ⟨l, u, hl, hu, hrel⟩ := hδ.rel t ⟨ht.1.le, ht.2⟩ (U ⊓ O) inf_le_left
        ⟨hδ.mem t ⟨ht.1.le, ht.2⟩, e0_mem_sector_source ha⟩
      obtain ⟨s, hs1, hs2⟩ := exists_between (max_lt hl ht.1)
      have hls : l < s := (le_max_left _ _).trans_lt hs1
      have h0s : 0 < s := (le_max_right _ _).trans_lt hs1
      have hlink : E0.causality.le (U ⊓ O) (δ s) (δ t) :=
        hrel s ⟨h0s.le, hs2.le.trans ht.2⟩ t ⟨ht.1.le, ht.2⟩ hls hs2 hu
      exact lt_of_lt_of_le_link E0.causallyArcConnected (e0_pushUpOn_sector ha)
        (hP s ⟨h0s.le, hs2⟩) hlink)
  simpa [hδ1] using key

/-- **Push-up in every open set of `𝔼₀`, second form**: `x ≤_U y ≪_U z ⇒ x ≪_U z`. Backwards along
a causal curve from `x` to `y`: at a regular point through a sector chart; at a BTZ point `a`, a
point `b` just above it on the curve has `τ_a ≤ f(b)`, and a regular `w` near `b` with
`f(w) > τ_a` lies in `I⁺_B(a)` for a ball `B` (`Iplus_ball_axis`) and still in `I⁻_U(z)`. -/
theorem e0_lt_of_le_of_lt {U : Opens E0} {x y z : E0} (h₁ : E0.causality.le U x y) (h₂ : E0.causality.lt U y z) :
    E0.causality.lt U x z := by
  obtain ⟨δ, hδ, hδ0, hδ1⟩ := (E0.causallyArcConnected U le_top x y).1.1 h₁
  have hcont := hδ.continuousOn E0.causality.isRelFamily_le
  have key := prop_zero_of_down (P := fun t => E0.causality.lt U (δ t) z) (by simpa [hδ1] using h₂)
    (fun t ht hPt => by
      obtain ⟨η, hη, h⟩ := exists_eta_of_mem_open hcont (E0.causality.isOpen_lt_left U z) ht hPt
      exact ⟨η, hη, fun s hs h1 h2 => h s hs (by rw [abs_lt]; constructor <;> linarith)⟩)
    (fun t ht hP => by
      have htI : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1, ht.2.le⟩
      by_cases hta : δ t ∈ E0.axis
      · -- a BTZ point
        obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 U.isOpen (δ t) (hδ.mem t htI)
        set NB : Opens E0 := ⟨Metric.ball (δ t) ε, Metric.isOpen_ball⟩
        have hNBU : NB ≤ U := hεU
        obtain ⟨l, u, hl, hu, hrel⟩ := hδ.rel t htI (U ⊓ NB) inf_le_left
          ⟨hδ.mem t htI, Metric.mem_ball_self hε⟩
        obtain ⟨s, hs1, hs2⟩ := exists_between (lt_min hu ht.2)
        have hsu : s < u := hs2.trans_le (min_le_left _ _)
        have hs1' : s < 1 := hs2.trans_le (min_le_right _ _)
        have hlink : E0.causality.le (U ⊓ NB) (δ t) (δ s) :=
          hrel t htI s ⟨ht.1.trans hs1.le, hs1'.le⟩ hl hs1 hsu
        set b := δ s
        have hbB : b ∈ Metric.ball (δ t) ε := (E0.causality.le_mem_right hlink).2
        have hfb : (δ t).1 ≤ E0.fcoord b :=
          (E0.le_axis_iff hta).1 (E0.le_of_le hlink)
        have hPb : E0.causality.lt U b z := hP s ⟨hs1, hs1'.le⟩
        have hVo : IsOpen ({w | E0.causality.lt U w z} ∩ Metric.ball (δ t) ε) :=
          (E0.causality.isOpen_lt_left U z).inter Metric.isOpen_ball
        obtain ⟨ρ, hρ, hρV⟩ := Metric.isOpen_iff.1 hVo b ⟨hPb, hbB⟩
        obtain ⟨w, hwV, hwr, hwf⟩ : ∃ w ∈ Metric.ball b ρ, 0 < E0.rad w ∧
            (δ t).1 < E0.fcoord w := by
          by_cases hb : b ∈ E0.axis
          · refine ⟨(b.1 + ρ / 2, ((ρ / 2 : ℝ) : ℂ)), ?_, ?_, ?_⟩
            · rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff, Real.dist_eq]
              have hb0 : b.2 = 0 := hb
              rw [hb0, dist_zero_right, Complex.norm_real, Real.norm_eq_abs]
              constructor
              · rw [show b.1 + ρ / 2 - b.1 = ρ / 2 by ring, abs_of_pos (by positivity)]
                linarith
              · rw [abs_of_pos (by positivity)]; linarith
            · show 0 < ‖((ρ / 2 : ℝ) : ℂ)‖
              rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
              positivity
            · have hfb' : E0.fcoord b = b.1 := by
                rw [E0.fcoord, E0.rad_eq_zero.2 hb]; ring
              show (δ t).1 < (b.1 + ρ / 2) - ‖((ρ / 2 : ℝ) : ℂ)‖ / 2
              rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
              linarith
          · refine ⟨(b.1 + ρ / 2, b.2), ?_, E0.rad_pos.2 hb, ?_⟩
            · rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff, Real.dist_eq, dist_self]
              refine ⟨?_, hρ⟩
              rw [show b.1 + ρ / 2 - b.1 = ρ / 2 by ring, abs_of_pos (by positivity)]
              linarith
            · show (δ t).1 < (b.1 + ρ / 2) - ‖b.2‖ / 2
              have : E0.fcoord b = b.1 - ‖b.2‖ / 2 := rfl
              linarith
        have hwV' := hρV hwV
        have hI : w ∈ E0.causality.Iplus NB {δ t} := by
          rw [E0.Iplus_ball_axis hta]; exact ⟨hwV'.2, hwr, hwf⟩
        exact E0.causality.lt_trans (E0.causality.lt_mono hNBU (Causal.Precausality.mem_Iplus_singleton.1 hI))
          hwV'.1
      · -- a regular point
        have ha : (δ t).2 ≠ 0 := hta
        set O := Causal.chartSource (E0.sectorChart (δ t) ha)
        obtain ⟨l, u, hl, hu, hrel⟩ := hδ.rel t htI (U ⊓ O) inf_le_left
          ⟨hδ.mem t htI, e0_mem_sector_source ha⟩
        obtain ⟨s, hs1, hs2⟩ := exists_between (lt_min hu ht.2)
        have hsu : s < u := hs2.trans_le (min_le_left _ _)
        have hs1' : s < 1 := hs2.trans_le (min_le_right _ _)
        have hlink : E0.causality.le (U ⊓ O) (δ t) (δ s) :=
          hrel t htI s ⟨ht.1.trans hs1.le, hs1'.le⟩ hl hs1 hsu
        exact lt_of_le_link_of_lt E0.causallyArcConnected (e0_pushUpOn_sector ha) hlink
          (hP s ⟨hs1, hs1'.le⟩))
  simpa [hδ0] using key

/-- **`𝔼₀` has push-up in every open set** (WP-41e SCOPE (d), discharged). -/
theorem e0_pushUp : E0.causality.PushUp :=
  Causal.Causality.pushUp_iff.2 fun _ _ _ _ => ⟨e0_lt_of_lt_of_le, e0_lt_of_le_of_lt⟩

end E0PushUp

section PushUpModel

theorem sum_pushUp {M₁ M₂ : Type*} [TopologicalSpace M₁] [TopologicalSpace M₂]
    {C₁ : Causal.Causality M₁} {C₂ : Causal.Causality M₂} (h₁ : C₁.PushUp) (h₂ : C₂.PushUp) :
    (E0.sumCausality C₁ C₂).PushUp := by
  refine Causal.Causality.pushUp_iff.2 fun U x y z => ?_
  rcases x with a | a <;> rcases y with b | b <;> rcases z with c | c <;>
    refine ⟨fun h h' => ?_, fun h h' => ?_⟩ <;>
    first
    | exact h.elim | exact h'.elim
    | exact h₁.lt_of_lt_of_le (U := E0.leftOpens U) h h'
    | exact h₁.lt_of_le_of_lt (U := E0.leftOpens U) h h'
    | exact h₂.lt_of_lt_of_le (U := E0.rightOpens U) h h'
    | exact h₂.lt_of_le_of_lt (U := E0.rightOpens U) h h'

theorem transport_pushUp {X Z : Type*} [TopologicalSpace X] [TopologicalSpace Z] {e : X ≃ₜ Z}
    {C : Causal.Causality Z} (h : C.PushUp) : (E0.transportCausality e C).PushUp :=
  Causal.Causality.pushUp_iff.2 fun U _ _ _ =>
    ⟨fun h₁ h₂ => h.lt_of_lt_of_le (U := E0.opensImage e U) h₁ h₂,
      fun h₁ h₂ => h.lt_of_le_of_lt (U := E0.opensImage e U) h₁ h₂⟩

/-- **The model `Y = 𝕄 ⊕ BTZE0` has push-up in every open set.** -/
theorem yb_pushUp : D.PushUp :=
  transport_pushUp (sum_pushUp Causal.minkowski_pushUp e0_pushUp)

end PushUpModel

/-! ### §2d `Iplus_of_lt` in a ball (DEC-64), on `𝔼₀` and on `Y` -/

section IplusModel

/-- **`Iplus_of_lt` in a ball of `𝔼₀`** (the local form): near an axis point `p'`, a point `p` of
the axis strictly below `p'` is chronologically before every regular `z ≥ p'`. -/
theorem e0_local_Iplus_of_lt {p' : E0} (hp' : p' ∈ E0.axis) {O : Opens E0} (hO : p' ∈ O) :
    ∃ W : Opens E0, p' ∈ W ∧ W ≤ O ∧ ∀ p z, p ∈ E0.axis → z ∉ E0.axis →
      E0.causality.le W p p' → p ≠ p' → E0.causality.le W p' z → E0.causality.lt O p z := by
  obtain ⟨ε, hε, hεO⟩ := Metric.isOpen_iff.1 O.isOpen p' hO
  refine ⟨⟨Metric.ball p' (ε / 3), Metric.isOpen_ball⟩, Metric.mem_ball_self (by positivity),
    fun w hw => hεO (Metric.ball_subset_ball (by linarith) hw), fun p z hp hz h₁ hne h₂ => ?_⟩
  have hpW : dist p p' < ε / 3 := E0.causality.le_mem_left h₁
  have hzW : dist z p' < ε / 3 := E0.causality.le_mem_right h₂
  have hτ : p.1 < p'.1 := by
    have h := ((E0.le_axis_iff' hp').1 (E0.le_of_le h₁)).2
    exact h.lt_of_ne fun e => hne (E0.axis_eq_of_fst_eq hp hp' e)
  have hf : p'.1 ≤ E0.fcoord z := (E0.le_axis_iff hp').1 (E0.le_of_le h₂)
  set B : Opens E0 := ⟨Metric.ball p (2 * ε / 3), Metric.isOpen_ball⟩
  have hzB : z ∈ Metric.ball p (2 * ε / 3) := by
    rw [Metric.mem_ball]
    calc dist z p ≤ dist z p' + dist p' p := dist_triangle _ _ _
      _ < ε / 3 + ε / 3 := by rw [dist_comm p' p]; exact add_lt_add hzW hpW
      _ = 2 * ε / 3 := by ring
  have hI : z ∈ E0.causality.Iplus B {p} := by
    rw [E0.Iplus_ball_axis hp]; exact ⟨hzB, E0.rad_pos.2 hz, by linarith⟩
  refine E0.causality.lt_mono (fun w hw => hεO ?_) (Causal.Precausality.mem_Iplus_singleton.1 hI)
  have hw' : dist w p < 2 * ε / 3 := hw
  rw [Metric.mem_ball]
  calc dist w p' ≤ dist w p + dist p p' := dist_triangle _ _ _
    _ < 2 * ε / 3 + ε / 3 := add_lt_add hw' hpW
    _ = ε := by ring

/-- **The local form of `Iplus_of_lt` on `Y = 𝕄 ⊕ BTZE0`.** -/
theorem yb_local_Iplus_of_lt : ∀ y' ∈ e0SingY 0, ∀ O : Opens E0Y, y' ∈ O →
    ∃ W : Opens E0Y, y' ∈ W ∧ W ≤ O ∧ ∀ y z, y ∈ e0SingY 0 → z ∉ e0SingY 0 →
      D.le W y y' → y ≠ y' → D.le W y' z → D.lt O y z := by
  intro y' hy' O hO
  rw [e0SingY_zero] at hy' ⊢
  obtain ⟨x', rfl⟩ : ∃ x', y' = Sum.inr x' := by
    rcases y' with m | x
    · obtain ⟨a, -, ha⟩ := hy'; exact absurd ha Sum.inr_ne_inl
    · exact ⟨x, rfl⟩
  have hax : E0.toPaper x' ∈ E0.axis := by
    obtain ⟨a, ha, he⟩ := hy'
    have : a = E0.toPaper x' := Sum.inr_injective he
    rw [← this]; exact ha
  set V : Opens E0 := E0.rightOpens (E0.opensImage E0.toPaperY O)
  have hV : E0.toPaper x' ∈ V := ⟨Sum.inr x', hO, rfl⟩
  obtain ⟨W, hW, hWV, hWrel⟩ := e0_local_Iplus_of_lt hax hV
  set WY : Opens E0Y := ⟨E0.toPaperY ⁻¹' (Sum.inr '' (W : Set E0)),
    (isOpenMap_inr _ W.isOpen).preimage E0.toPaperY.continuous⟩
  refine ⟨WY, ⟨E0.toPaper x', hW, rfl⟩, fun z hz => ?_, fun y z hy hz h₁ hne h₂ => ?_⟩
  · obtain ⟨w, hw, hwe⟩ := hz
    obtain ⟨u, hu, hue⟩ := hWV hw
    have : E0.toPaperY u = E0.toPaperY z := hue.trans hwe
    rw [← E0.toPaperY.injective this]; exact hu
  · have hsub : E0.rightOpens (E0.opensImage E0.toPaperY WY) ≤ W := by
      rintro a ⟨u, hu, hue⟩
      obtain ⟨w, hw, hwe⟩ := hu
      rw [← hwe] at hue
      exact Sum.inr_injective hue ▸ hw
    rcases y with m | x
    · exact absurd h₁ id
    rcases z with m | w
    · exact absurd h₂ id
    have hxa : E0.toPaper x ∈ E0.axis := by
      obtain ⟨a, ha, he⟩ := hy
      have : a = E0.toPaper x := Sum.inr_injective he
      rw [← this]; exact ha
    have hwa : E0.toPaper w ∉ E0.axis := fun h => hz ⟨_, h, rfl⟩
    have hne' : E0.toPaper x ≠ E0.toPaper x' := fun e => hne (by rw [E0.toPaper.injective e])
    exact hWrel _ _ hxa hwa (E0.causality.le_mono hsub h₁) hne' (E0.causality.le_mono hsub h₂)

end IplusModel


/-! ### §2e The BTZ line in a ball: points below, local future and past (for `SingularPastAt`) -/

section AxisFacts

theorem e0_dist_fst_le (x y : E0) : dist x.1 y.1 ≤ dist x y := by
  rw [Prod.dist_eq]; exact le_max_left _ _

theorem e0_dist_snd_le (x y : E0) : dist x.2 y.2 ≤ dist x y := by
  rw [Prod.dist_eq]; exact le_max_right _ _

/-- **The axis segment is causal in a ball**: two axis points `p, q` with `τ_p ≤ τ_q`, both in the
ball `B(c, ρ)`, satisfy `p ≤_B q`. -/
theorem e0_le_ball_of_axis {p q c : E0} {ρ : ℝ} (hp : p ∈ E0.axis) (hq : q ∈ E0.axis)
    (hpq : p.1 ≤ q.1) (hpB : p ∈ Metric.ball c ρ) (hqB : q ∈ Metric.ball c ρ) :
    E0.causality.le ⟨Metric.ball c ρ, Metric.isOpen_ball⟩ p q := by
  have hp0 : p.2 = 0 := hp
  have hq0 : q.2 = 0 := hq
  have hmem : ∀ t ∈ Icc (0 : ℝ) (q.1 - p.1),
      E0.axisLine p t ∈ (⟨Metric.ball c ρ, Metric.isOpen_ball⟩ : Opens E0) := by
    intro t ht
    show dist (E0.axisLine p t) c < ρ
    have hpd : dist p c < ρ := hpB
    have hqd : dist q c < ρ := hqB
    rw [Prod.dist_eq] at hpd hqd ⊢
    rw [hp0] at hpd
    rw [hq0] at hqd
    simp only [E0.axisLine]
    rw [max_lt_iff] at hpd hqd ⊢
    refine ⟨?_, hpd.2⟩
    rw [Real.dist_eq] at hpd hqd ⊢
    have h1 := abs_lt.1 hpd.1
    have h2 := abs_lt.1 hqd.1
    rw [abs_lt]; constructor <;> linarith [ht.1, ht.2]
  rcases E0.curveOn_axisLine p ⟨Metric.ball c ρ, Metric.isOpen_ball⟩ 0 (q.1 - p.1) with h | h
  · have hc := E0.causalCurveOn_of_curveOn h
    have := hc.le_of_le le_rfl (sub_nonneg.2 hpq) le_rfl
    have e0 : E0.axisLine p 0 = p := Prod.ext (by simp [E0.axisLine]) (by simp [E0.axisLine, hp0])
    have e1 : E0.axisLine p (q.1 - p.1) = q :=
      Prod.ext (by simp [E0.axisLine]) (by simp [E0.axisLine, hq0])
    rwa [e0, e1] at this
  · exact absurd hmem h

theorem e0_fst_lt_of_le_axis {p q : E0} (hp : p ∈ E0.axis) (hq : q ∈ E0.axis) {W : Opens E0}
    (h : E0.causality.le W p q) (hne : p ≠ q) : p.1 < q.1 :=
  (((E0.le_axis_iff' hq).1 (E0.le_of_le h)).2).lt_of_ne fun e => hne (E0.axis_eq_of_fst_eq hp hq e)

/-- (A1) **points of the axis strictly below, arbitrarily close**. -/
theorem e0_exists_below {y' : E0} (hy' : y' ∈ E0.axis) {O : Opens E0} (hO : y' ∈ O)
    {N : Set E0} (hN : N ∈ 𝓝 y') : ∃ y ∈ N, y ∈ E0.axis ∧ y ≠ y' ∧ E0.causality.le O y y' := by
  obtain ⟨ε, hε, hεs⟩ := Metric.mem_nhds_iff.1 (inter_mem hN (O.isOpen.mem_nhds hO))
  have hy0 : y'.2 = 0 := hy'
  set y : E0 := (y'.1 - ε / 2, 0)
  have hyB : y ∈ Metric.ball y' ε := by
    rw [Metric.mem_ball, Prod.dist_eq, hy0, dist_self, Real.dist_eq, max_lt_iff]
    refine ⟨?_, hε⟩
    rw [show y'.1 - ε / 2 - y'.1 = -(ε / 2) by ring, abs_neg, abs_of_pos (by positivity)]
    linarith
  refine ⟨y, (hεs hyB).1, rfl, fun e => ?_, ?_⟩
  · have := congrArg Prod.fst e
    simp only [y] at this
    linarith
  · exact E0.causality.le_mono (fun w hw => (hεs hw).2)
      (e0_le_ball_of_axis rfl hy' (by simp only [y]; linarith) hyB (Metric.mem_ball_self hε))

/-- (A2) **a point of the axis strictly below `a` has a neighbourhood of `a` in its future**. -/
theorem e0_future_nhds {a : E0} (ha : a ∈ E0.axis) {O : Opens E0} (hO : a ∈ O) :
    ∃ W : Opens E0, a ∈ W ∧ W ≤ O ∧ ∀ b, b ∈ E0.axis → E0.causality.le W b a → b ≠ a →
      ∃ V ∈ 𝓝 a, ∀ z ∈ V, E0.causality.le O b z := by
  obtain ⟨ε, hε, hεO⟩ := Metric.isOpen_iff.1 O.isOpen a hO
  refine ⟨⟨Metric.ball a (ε / 3), Metric.isOpen_ball⟩, Metric.mem_ball_self (by positivity),
    fun w hw => hεO (Metric.ball_subset_ball (by linarith) hw), fun b hb h₁ hne => ?_⟩
  have hbW : dist b a < ε / 3 := E0.causality.le_mem_left h₁
  have hτ := e0_fst_lt_of_le_axis hb ha h₁ hne
  set η := min (ε / 3) ((a.1 - b.1) / 3)
  have hη : 0 < η := lt_min (by positivity) (by linarith)
  refine ⟨Metric.ball a η, Metric.ball_mem_nhds a hη, fun z hz => ?_⟩
  have hzd : dist z a < η := hz
  have hzε : dist z a < ε / 3 := hzd.trans_le (min_le_left _ _)
  have hzτ : dist z a < (a.1 - b.1) / 3 := hzd.trans_le (min_le_right _ _)
  have h1 : |z.1 - a.1| < (a.1 - b.1) / 3 :=
    (by rw [← Real.dist_eq]; exact (e0_dist_fst_le z a).trans_lt hzτ)
  have ha0 : a.2 = 0 := ha
  have h2 : E0.rad z < (a.1 - b.1) / 3 := by
    have : dist z.2 a.2 ≤ dist z a := e0_dist_snd_le z a
    rw [ha0, dist_zero_right] at this
    exact this.trans_lt hzτ
  have hf : b.1 < E0.fcoord z := by
    have := abs_lt.1 h1
    rw [E0.fcoord]; linarith [E0.rad_nonneg z]
  set B : Opens E0 := ⟨Metric.ball b (2 * ε / 3), Metric.isOpen_ball⟩
  have hBO : B ≤ O := fun w hw => hεO (by
    have hw' : dist w b < 2 * ε / 3 := hw
    rw [Metric.mem_ball]
    calc dist w a ≤ dist w b + dist b a := dist_triangle _ _ _
      _ < 2 * ε / 3 + ε / 3 := add_lt_add hw' hbW
      _ = ε := by ring)
  have hzB : z ∈ Metric.ball b (2 * ε / 3) := by
    rw [Metric.mem_ball]
    calc dist z b ≤ dist z a + dist a b := dist_triangle _ _ _
      _ < ε / 3 + ε / 3 := by rw [dist_comm a b]; exact add_lt_add hzε hbW
      _ = 2 * ε / 3 := by ring
  by_cases hz : z ∈ E0.axis
  · have hfz : E0.fcoord z = z.1 := by rw [E0.fcoord, E0.rad_eq_zero.2 hz]; ring
    exact E0.causality.le_mono hBO (e0_le_ball_of_axis hb hz (by linarith)
      (Metric.mem_ball_self (by positivity)) hzB)
  · have hI : z ∈ E0.causality.Iplus B {b} := by
      rw [E0.Iplus_ball_axis hb]; exact ⟨hzB, E0.rad_pos.2 hz, hf⟩
    exact E0.causality.le_mono hBO
      (E0.causality.le_of_lt (Causal.Precausality.mem_Iplus_singleton.1 hI))

/-- (A3) **a point `v` of the axis strictly above `x` is in the future of every axis point near
`x`**. -/
theorem e0_past_nhds {x : E0} (hx : x ∈ E0.axis) {O : Opens E0} (hO : x ∈ O) :
    ∃ W : Opens E0, x ∈ W ∧ W ≤ O ∧ ∀ v, v ∈ E0.axis → E0.causality.le W x v → v ≠ x →
      ∃ V ∈ 𝓝 x, ∀ y ∈ V, y ∈ E0.axis → E0.causality.le O y v := by
  obtain ⟨ε, hε, hεO⟩ := Metric.isOpen_iff.1 O.isOpen x hO
  refine ⟨⟨Metric.ball x (ε / 2), Metric.isOpen_ball⟩, Metric.mem_ball_self (by positivity),
    fun w hw => hεO (Metric.ball_subset_ball (by linarith) hw), fun v hv h₁ hne => ?_⟩
  have hvW : dist v x < ε / 2 := E0.causality.le_mem_right h₁
  have hτ := e0_fst_lt_of_le_axis hx hv h₁ (Ne.symm hne)
  set η := min (ε / 2) (v.1 - x.1)
  have hη : 0 < η := lt_min (by positivity) (by linarith)
  refine ⟨Metric.ball x η, Metric.ball_mem_nhds x hη, fun y hy hya => ?_⟩
  have hyd : dist y x < η := hy
  have h1 : |y.1 - x.1| < v.1 - x.1 :=
    (by rw [← Real.dist_eq]; exact (e0_dist_fst_le y x).trans_lt (hyd.trans_le (min_le_right _ _)))
  have hyB : y ∈ Metric.ball x ε := (hyd.trans_le (min_le_left _ _)).trans (by linarith)
  have hvB : v ∈ Metric.ball x ε := hvW.trans (by linarith)
  exact E0.causality.le_mono (fun w hw => hεO hw)
    (e0_le_ball_of_axis hya hv (by linarith [(abs_lt.1 h1).2]) hyB hvB)

end AxisFacts


section YAxisFacts

/-- The open set of `ℝ × ℂ` read from an open set of `Y`. -/
noncomputable abbrev vOf (O : Opens E0Y) : Opens E0 := E0.rightOpens (E0.opensImage E0.toPaperY O)

/-- The open set of `Y` read from an open set of `ℝ × ℂ`. -/
noncomputable def wOf (W : Opens E0) : Opens E0Y :=
  ⟨E0.toPaperY ⁻¹' (Sum.inr '' (W : Set E0)),
    (isOpenMap_inr _ W.isOpen).preimage E0.toPaperY.continuous⟩

theorem mem_vOf {O : Opens E0Y} {x : BTZE0} (h : (Sum.inr x : E0Y) ∈ O) :
    E0.toPaper x ∈ vOf O := ⟨Sum.inr x, h, rfl⟩

theorem mem_wOf {W : Opens E0} {x : BTZE0} (h : E0.toPaper x ∈ W) : (Sum.inr x : E0Y) ∈ wOf W :=
  ⟨_, h, rfl⟩

theorem wOf_le {W : Opens E0} {O : Opens E0Y} (h : W ≤ vOf O) : wOf W ≤ O := by
  intro z hz
  obtain ⟨w, hw, hwe⟩ := hz
  obtain ⟨u, hu, hue⟩ := h hw
  have : E0.toPaperY u = E0.toPaperY z := hue.trans hwe
  rw [← E0.toPaperY.injective this]; exact hu

theorem vOf_wOf_le (W : Opens E0) : vOf (wOf W) ≤ W := by
  rintro a ⟨u, hu, hue⟩
  obtain ⟨w, hw, hwe⟩ := hu
  rw [← hwe] at hue
  exact Sum.inr_injective hue ▸ hw

theorem mem_e0SingY_zero_iff {y : E0Y} :
    y ∈ e0SingY 0 ↔ ∃ x : BTZE0, y = Sum.inr x ∧ E0.toPaper x ∈ E0.axis := by
  rw [e0SingY_zero]
  constructor
  · intro hy
    rcases y with m | x
    · obtain ⟨a, -, ha⟩ := hy; exact absurd ha Sum.inr_ne_inl
    · refine ⟨x, rfl, ?_⟩
      obtain ⟨a, ha, he⟩ := hy
      have : a = E0.toPaper x := Sum.inr_injective he
      rw [← this]; exact ha
  · rintro ⟨x, rfl, hx⟩; exact ⟨_, hx, rfl⟩

theorem inr_mem_e0SingY_zero_iff {x : BTZE0} :
    (Sum.inr x : E0Y) ∈ e0SingY 0 ↔ E0.toPaper x ∈ E0.axis := by
  rw [mem_e0SingY_zero_iff]
  exact ⟨fun ⟨x', he, h⟩ => Sum.inr_injective he ▸ h, fun h => ⟨x, rfl, h⟩⟩

/-- The open embedding `ℝ × ℂ → Y`, `q ↦ inr (toPaper⁻¹ q)`. -/
noncomputable def emb (q : E0) : E0Y := Sum.inr (E0.toPaper.symm q)

theorem isOpenEmbedding_emb : IsOpenEmbedding emb :=
  IsOpenEmbedding.inr.comp E0.toPaper.symm.isOpenEmbedding

theorem emb_toPaper (x : BTZE0) : emb (E0.toPaper x) = Sum.inr x := by
  simp [emb]

/-- (A1) on `Y`. -/
theorem yb_exists_below : ∀ y' ∈ e0SingY 0, ∀ O : Opens E0Y, y' ∈ O → ∀ N ∈ 𝓝 y',
    ∃ y ∈ N, y ∈ e0SingY 0 ∧ y ≠ y' ∧ D.le O y y' := by
  intro y' hy' O hO N hN
  obtain ⟨x', rfl, hax⟩ := mem_e0SingY_zero_iff.1 hy'
  have hN' : emb ⁻¹' N ∈ 𝓝 (E0.toPaper x') :=
    isOpenEmbedding_emb.continuous.continuousAt.preimage_mem_nhds (by rwa [emb_toPaper])
  obtain ⟨q, hqN, hqa, hne, hle⟩ := e0_exists_below hax (mem_vOf hO) hN'
  refine ⟨emb q, hqN, inr_mem_e0SingY_zero_iff.2 (by simpa [emb] using hqa), fun e => hne ?_, ?_⟩
  · have h1 : E0.toPaper.symm q = x' := Sum.inr_injective e
    rw [← h1, Homeomorph.apply_symm_apply]
  · show E0.causality.le (vOf O) (E0.toPaper (E0.toPaper.symm q)) (E0.toPaper x')
    simpa using hle

/-- (A2) on `Y`. -/
theorem yb_future_nhds : ∀ a ∈ e0SingY 0, ∀ O : Opens E0Y, a ∈ O →
    ∃ W : Opens E0Y, a ∈ W ∧ W ≤ O ∧ ∀ b, b ∈ e0SingY 0 → D.le W b a → b ≠ a →
      ∃ V ∈ 𝓝 a, ∀ z ∈ V, D.le O b z := by
  intro a ha O hO
  obtain ⟨x', rfl, hax⟩ := mem_e0SingY_zero_iff.1 ha
  obtain ⟨W, hW, hWV, hrel⟩ := e0_future_nhds hax (mem_vOf hO)
  refine ⟨wOf W, mem_wOf hW, wOf_le hWV, fun b hb h₁ hne => ?_⟩
  obtain ⟨x, rfl, hbx⟩ := mem_e0SingY_zero_iff.1 hb
  have h₁' : E0.causality.le W (E0.toPaper x) (E0.toPaper x') :=
    E0.causality.le_mono (vOf_wOf_le W) h₁
  have hne' : E0.toPaper x ≠ E0.toPaper x' := fun e => hne (by rw [E0.toPaper.injective e])
  obtain ⟨V, hV, hVrel⟩ := hrel _ hbx h₁' hne'
  refine ⟨emb '' V, by rw [← emb_toPaper]; exact isOpenEmbedding_emb.isOpenMap.image_mem_nhds hV,
    ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  show E0.causality.le (vOf O) (E0.toPaper x) (E0.toPaper (E0.toPaper.symm z))
  simpa using hVrel z hz

/-- (A3) on `Y`. -/
theorem yb_past_nhds : ∀ x ∈ e0SingY 0, ∀ O : Opens E0Y, x ∈ O →
    ∃ W : Opens E0Y, x ∈ W ∧ W ≤ O ∧ ∀ v, v ∈ e0SingY 0 → D.le W x v → v ≠ x →
      ∃ V ∈ 𝓝 x, ∀ y ∈ V, y ∈ e0SingY 0 → D.le O y v := by
  intro x hx O hO
  obtain ⟨x', rfl, hax⟩ := mem_e0SingY_zero_iff.1 hx
  obtain ⟨W, hW, hWV, hrel⟩ := e0_past_nhds hax (mem_vOf hO)
  refine ⟨wOf W, mem_wOf hW, wOf_le hWV, fun v hv h₁ hne => ?_⟩
  obtain ⟨xv, rfl, hvx⟩ := mem_e0SingY_zero_iff.1 hv
  have h₁' : E0.causality.le W (E0.toPaper x') (E0.toPaper xv) :=
    E0.causality.le_mono (vOf_wOf_le W) h₁
  have hne' : E0.toPaper xv ≠ E0.toPaper x' := fun e => hne (by rw [E0.toPaper.injective e])
  obtain ⟨V, hV, hVrel⟩ := hrel _ hvx h₁' hne'
  refine ⟨emb '' V, by rw [← emb_toPaper]; exact isOpenEmbedding_emb.isOpenMap.image_mem_nhds hV,
    ?_⟩
  rintro _ ⟨y, hy, rfl⟩ hys
  have hya : y ∈ E0.axis := by
    have := inr_mem_e0SingY_zero_iff.1 hys
    simpa using this
  show E0.causality.le (vOf O) (E0.toPaper (E0.toPaper.symm y)) (E0.toPaper xv)
  simpa using hVrel y hy hya

end YAxisFacts


/-! ### §3 From the model to every admissible `M`: the local-to-global fields -/

section Charted

universe u

variable {Y : Type u} [TopologicalSpace Y] {G : StructureGroupoid Y} {DY : Causal.Causality Y}
  {singY : ℝ → Set Y} {M : Type u} [TopologicalSpace M] [ChartedSpace Y M] [HasGroupoid M G]

/-- **The type of a point does not depend on the chart** (`prop:GX_sing_dec`): elements of `G`
preserve each `sing_α`. -/
theorem chartAt_mem_singY_iff
    (hS : ∀ e ∈ G, ∀ y ∈ e.source, ∀ α : ℝ, 0 ≤ α → (y ∈ singY α ↔ e y ∈ singY α))
    {x y : M} (hy : y ∈ (chartAt Y x).source) {α : ℝ} (hα : 0 ≤ α) :
    chartAt Y x y ∈ singY α ↔ y ∈ Causal.CBG.chartedSing singY M α := by
  set e := (chartAt Y y).symm.trans (chartAt Y x)
  have he : e ∈ G := HasGroupoid.compatible (chart_mem_atlas Y y) (chart_mem_atlas Y x)
  have hys : chartAt Y y y ∈ e.source := by
    refine ⟨(chartAt Y y).map_source (mem_chart_source Y y), ?_⟩
    show (chartAt Y y).symm (chartAt Y y y) ∈ (chartAt Y x).source
    rw [(chartAt Y y).left_inv (mem_chart_source Y y)]; exact hy
  have hey : e (chartAt Y y y) = chartAt Y x y := by
    show chartAt Y x ((chartAt Y y).symm (chartAt Y y y)) = _
    rw [(chartAt Y y).left_inv (mem_chart_source Y y)]
  rw [← hey, ← hS e he _ hys α hα]
  rfl

variable (hGD : ∀ e ∈ G, Causal.ChartIso DY DY e) (hA : ∀ W : Opens Y, DY.AbsolutelyMinimalOn W)
  (hS : ∀ e ∈ G, ∀ y ∈ e.source, ∀ α : ℝ, 0 ≤ α → (y ∈ singY α ↔ e y ∈ singY α))
include hGD hA

/-- **`Z⁺(M) = M`** from the model's local form (`rem:btz_pas_tarentin`). -/
theorem charted_mem_Zplus (hZ : LocZplus DY) (y : M) : y ∈ (Causal.CBG.chartedCausality DY M).Zplus := by
  intro N hN
  set c := chartAt Y y
  have hys : y ∈ c.source := mem_chart_source Y y
  have hc := Causal.CBG.chartedCausality_chartIso (M := M) hGD hA y
  obtain ⟨z', hz', hlt⟩ := hZ (Causal.chartImage c (Causal.chartSource c)) (c y)
    (Causal.mem_chartImage_of_mem hys hys) _
    (c.image_mem_nhds hys (inter_mem hN (c.open_source.mem_nhds hys)))
  obtain ⟨z, ⟨hzN, hzs⟩, rfl⟩ := hz'
  exact ⟨z, Causal.Precausality.mem_Iplus_singleton.2
    ((Causal.CBG.chartedCausality DY M).lt_mono le_top (((hc _ le_rfl y hys z hzs).2).2 hlt)), hzN⟩

/-- **`Z⁻(M) ⊇ M ∖ sing₀(M)`** from the model's local form. -/
theorem charted_mem_Zminus (hZ : LocZminus DY (singY 0)) {y : M}
    (hy : y ∉ Causal.CBG.chartedSing singY M 0) : y ∈ (Causal.CBG.chartedCausality DY M).Zminus := by
  intro N hN
  set c := chartAt Y y
  have hys : y ∈ c.source := mem_chart_source Y y
  have hc := Causal.CBG.chartedCausality_chartIso (M := M) hGD hA y
  obtain ⟨z', hz', hlt⟩ := hZ (Causal.chartImage c (Causal.chartSource c)) (c y)
    (Causal.mem_chartImage_of_mem hys hys) hy _
    (c.image_mem_nhds hys (inter_mem hN (c.open_source.mem_nhds hys)))
  obtain ⟨z, ⟨hzN, hzs⟩, rfl⟩ := hz'
  exact ⟨z, Causal.Precausality.mem_Iminus_singleton.2
    ((Causal.CBG.chartedCausality DY M).lt_mono le_top (((hc _ le_rfl z hzs y hys).2).2 hlt)), hzN⟩

/-- **`I⁻(p) = ∅` at a BTZ point of `M`, globally**: a chronological relation of `M` is a chain of
relations in chart domains (absolute minimality); its last link ends at `p` in a chart, where the
model has no chronological past. -/
theorem charted_Iminus_eq_empty (hS : ∀ e ∈ G, ∀ y ∈ e.source, ∀ α : ℝ, 0 ≤ α →
      (y ∈ singY α ↔ e y ∈ singY α)) (hP : LocNoPast DY (singY 0)) {p : M}
    (hp : p ∈ Causal.CBG.chartedSing singY M 0) : (Causal.CBG.chartedCausality DY M).Iminus ⊤ {p} = ∅ := by
  refine eq_empty_iff_forall_notMem.2 fun z hz => ?_
  have hz' := Causal.Precausality.mem_Iminus_singleton.1 hz
  have hmin := Causal.CBG.chartedCausality_absolutelyMinimalOn (M := M) hGD hA ⊤
  obtain ⟨b, -, hb⟩ := Relation.TransGen.tail'_iff.1
    ((hmin (range fun x : M => Causal.chartSource (chartAt Y x))
      (fun x _ => ⟨_, mem_range_self x, mem_chart_source Y x⟩) ⊤ le_rfl z p).2 hz')
  obtain ⟨_, ⟨x, rfl⟩, hbp⟩ := hb
  have hc := Causal.CBG.chartedCausality_chartIso (M := M) hGD hA x
  have hle : ⊤ ⊓ Causal.chartSource (chartAt Y x) ≤ Causal.chartSource (chartAt Y x) := inf_le_right
  have hbm := (Causal.CBG.chartedCausality DY M).lt_mem_left hbp
  have hpm := (Causal.CBG.chartedCausality DY M).lt_mem_right hbp
  have hrel := ((hc _ hle b hbm p hpm).2).1 hbp
  have hps : chartAt Y x p ∈ singY 0 := (chartAt_mem_singY_iff hS (hle hpm) le_rfl).2 hp
  exact hP _ _ hps _ hrel

/-- **`J⁻_U(p) ⊆ sing₀(M)` in the chart domain `U` of a BTZ point** (`past_local`). -/
theorem charted_past_local (hS : ∀ e ∈ G, ∀ y ∈ e.source, ∀ α : ℝ, 0 ≤ α →
      (y ∈ singY α ↔ e y ∈ singY α)) (hP : LocPastIn DY (singY 0)) {p : M}
    (hp : p ∈ Causal.CBG.chartedSing singY M 0) :
    ∃ U : Opens M, p ∈ U ∧ ∀ q, (Causal.CBG.chartedCausality DY M).le U q p → q ∈ Causal.CBG.chartedSing singY M 0 := by
  set c := chartAt Y p
  have hc := Causal.CBG.chartedCausality_chartIso (M := M) hGD hA p
  refine ⟨Causal.chartSource c, mem_chart_source Y p, fun q hq => ?_⟩
  have hqs : q ∈ c.source := (Causal.CBG.chartedCausality DY M).le_mem_left hq
  have hrel := ((hc _ le_rfl q hqs p (mem_chart_source Y p)).1).1 hq
  exact (chartAt_mem_singY_iff hS hqs le_rfl).1 (hP _ _ hp _ hrel)

/-- **`M` is tarentin** from the model's local form. -/
theorem charted_tarentin (hT : LocTarentin DY) : (Causal.CBG.chartedCausality DY M).Tarentin := by
  intro y N hN
  set c := chartAt Y y
  have hys : y ∈ c.source := mem_chart_source Y y
  have hc := Causal.CBG.chartedCausality_chartIso (M := M) hGD hA y
  obtain ⟨p', hp', q', hq', hd⟩ := hT (Causal.chartImage c (Causal.chartSource c)) (c y)
    (Causal.mem_chartImage_of_mem hys hys) _
    (c.image_mem_nhds hys (inter_mem hN (c.open_source.mem_nhds hys)))
  obtain ⟨p, ⟨hpN, hps⟩, rfl⟩ := hp'
  obtain ⟨q, ⟨hqN, hqs⟩, rfl⟩ := hq'
  refine ⟨p, hpN, q, hqN, ?_⟩
  have hO : IsOpen (c.source ∩ c ⁻¹' interior (DY.diamond
      (Causal.chartImage c (Causal.chartSource c)) (c p) (c q))) :=
    c.isOpen_inter_preimage isOpen_interior
  refine interior_maximal (fun w hw => ?_) hO ⟨hys, hd⟩
  obtain ⟨h1, h2⟩ := Causal.Causality.mem_diamond.1 (interior_subset hw.2)
  exact Causal.Causality.mem_diamond.2
    ⟨(Causal.CBG.chartedCausality DY M).le_mono le_top (((hc _ le_rfl p hps w hw.1).1).2 h1),
      (Causal.CBG.chartedCausality DY M).le_mono le_top (((hc _ le_rfl w hw.1 q hqs).1).2 h2)⟩

/-- **`M` is causally arc-connected** (`lem:manifolds_manifolds_causally_connected`, `def:
singular_manifold_endowed_causal`): every chart domain is (the model is), and the causality is
absolutely minimal (`lem:precausalite_restriction_minimale`). -/
theorem charted_causallyArcConnected (hD : DY.CausallyArcConnected) : (Causal.CBG.chartedCausality DY M).CausallyArcConnected := by
  refine Causal.Causality.LocallyCausallyArcConnected.causallyArcConnected (fun x N hN => ?_)
    (Causal.CBG.chartedCausality_absolutelyMinimal hA)
  obtain ⟨t, htN, hto, hxt⟩ := mem_nhds_iff.1 hN
  set c := chartAt Y x
  refine ⟨⟨c.source ∩ t, c.open_source.inter hto⟩, ⟨mem_chart_source Y x, hxt⟩,
    fun w hw => htN hw.2, ?_⟩
  exact Causal.Flat.causallyArcConnectedOn_of_chartIso
    (Causal.CBG.chartedCausality_chartIso (M := M) hGD hA x) hD (fun w hw => hw.1)

/-- **Push-up on `M`** (`cor:pushup_sing`, `lem:pushup_local`): `M` is causally arc-connected and
covered by chart domains, each with push-up (the model has it in every open set). -/
theorem charted_pushUp (hD : DY.CausallyArcConnected) (hP : DY.PushUp) :
    (Causal.CBG.chartedCausality DY M).PushUp :=
  Causal.Causality.CausallyArcConnected.pushUp (charted_causallyArcConnected (M := M) hGD hA hD)
    (O := fun x : M => Causal.chartSource (chartAt Y x)) (fun x => ⟨x, mem_chart_source Y x⟩)
    (fun x => pushUpOn_of_chartIso (Causal.CBG.chartedCausality_chartIso (M := M) hGD hA x) hP)

omit hGD hA in
/-- **`sing_α(M)` is closed** when `sing_α(Y)` is. -/
theorem charted_isClosed_sing (hS : ∀ e ∈ G, ∀ y ∈ e.source, ∀ α : ℝ, 0 ≤ α →
      (y ∈ singY α ↔ e y ∈ singY α)) {α : ℝ} (hα : 0 ≤ α) (hcl : IsClosed (singY α)) :
    IsClosed (Causal.CBG.chartedSing singY M α) := by
  refine isOpen_compl_iff.1 (isOpen_iff_mem_nhds.2 fun x hx => ?_)
  set c := chartAt Y x
  have hO : IsOpen (c.source ∩ c ⁻¹' (singY α)ᶜ) := c.isOpen_inter_preimage hcl.isOpen_compl
  refine mem_of_superset (hO.mem_nhds ⟨mem_chart_source Y x, hx⟩) fun w hw hws => ?_
  exact hw.2 ((chartAt_mem_singY_iff hS hw.1 hα).2 hws)

omit hGD hA in
/-- **`sing_α(M)` has empty interior** when `sing_α(Y)` has. -/
theorem charted_interior_sing (hS : ∀ e ∈ G, ∀ y ∈ e.source, ∀ α : ℝ, 0 ≤ α →
      (y ∈ singY α ↔ e y ∈ singY α)) {α : ℝ} (hα : 0 ≤ α) (hint : interior (singY α) = ∅) :
    interior (Causal.CBG.chartedSing singY M α) = ∅ := by
  refine eq_empty_iff_forall_notMem.2 fun x hx => ?_
  set c := chartAt Y x
  have hxs : x ∈ c.source := mem_chart_source Y x
  have hopen : IsOpen (c '' (c.source ∩ interior (Causal.CBG.chartedSing singY M α))) :=
    c.isOpen_image_source_inter isOpen_interior
  have hsub : c '' (c.source ∩ interior (Causal.CBG.chartedSing singY M α)) ⊆ singY α := by
    rintro _ ⟨w, ⟨hws, hwi⟩, rfl⟩
    exact (chartAt_mem_singY_iff hS hws hα).2 (interior_subset hwi)
  have := interior_maximal hsub hopen ⟨x, ⟨hxs, hx⟩, rfl⟩
  rw [hint] at this
  exact this

omit hGD hA [HasGroupoid M G] in
/-- **No isolated point**, when the model has none. -/
theorem charted_nhdsNE_neBot (hY : ∀ y : Y, (𝓝[≠] y).NeBot) (x : M) : (𝓝[≠] x).NeBot := by
  set e := chartAt Y x
  have hx : x ∈ e.source := mem_chart_source _ x
  have hmap := e.map_nhdsWithin_eq hx ({x}ᶜ)
  have himg : e '' (e.source ∩ {x}ᶜ) = e.target ∩ {e x}ᶜ := by
    ext y
    constructor
    · rintro ⟨z, ⟨hz, hzx⟩, rfl⟩
      exact ⟨e.map_source hz, fun h => hzx (e.injOn hz hx h)⟩
    · rintro ⟨hy, hyx⟩
      refine ⟨e.symm y, ⟨e.map_target hy, fun h => hyx ?_⟩, e.right_inv hy⟩
      rw [mem_singleton_iff] at h ⊢
      rw [← h, e.right_inv hy]
  rw [himg, nhdsWithin_inter_of_mem (mem_nhdsWithin_of_mem_nhds
    (e.open_target.mem_nhds (e.map_source hx)))] at hmap
  have : (map e (𝓝[≠] x)).NeBot := by rw [hmap]; exact hY _
  exact (Filter.map_neBot_iff _).1 this

end Charted

/-! ### §3b `Iplus_of_lt` on every admissible `M` -/

section ChartedIplus

universe u

variable {Y : Type u} [TopologicalSpace Y] {G : StructureGroupoid Y} {DY : Causal.Causality Y}
  {singY : ℝ → Set Y} {M : Type u} [TopologicalSpace M] [ChartedSpace Y M] [HasGroupoid M G]
  (hGD : ∀ e ∈ G, Causal.ChartIso DY DY e) (hA : ∀ W : Opens Y, DY.AbsolutelyMinimalOn W)
  (hS : ∀ e ∈ G, ∀ y ∈ e.source, ∀ α : ℝ, 0 ≤ α → (y ∈ singY α ↔ e y ∈ singY α))
include hGD hA hS

/-- **The local form of `Iplus_of_lt` read in a chart of `M`.** -/
theorem charted_local_Iplus_of_lt
    (hK : ∀ y' ∈ singY 0, ∀ O : Opens Y, y' ∈ O → ∃ W : Opens Y, y' ∈ W ∧ W ≤ O ∧
      ∀ y z, y ∈ singY 0 → z ∉ singY 0 → DY.le W y y' → y ≠ y' → DY.le W y' z → DY.lt O y z)
    {a : M} (ha : a ∈ Causal.CBG.chartedSing singY M 0) :
    ∃ N : Opens M, a ∈ N ∧ ∀ b w, b ∈ Causal.CBG.chartedSing singY M 0 →
      w ∉ Causal.CBG.chartedSing singY M 0 →
      (Causal.CBG.chartedCausality DY M).le N b a → b ≠ a →
      (Causal.CBG.chartedCausality DY M).le N a w →
      (Causal.CBG.chartedCausality DY M).lt ⊤ b w := by
  set c := chartAt Y a
  have has : a ∈ c.source := mem_chart_source Y a
  have hc := Causal.CBG.chartedCausality_chartIso (M := M) hGD hA a
  obtain ⟨W, hW, -, hWrel⟩ := hK (c a) ha (Causal.chartImage c (Causal.chartSource c))
    (Causal.mem_chartImage_of_mem has has)
  refine ⟨⟨c.source ∩ c ⁻¹' W, c.isOpen_inter_preimage W.isOpen⟩, ⟨has, hW⟩,
    fun b w hb hw h₁ hne h₂ => ?_⟩
  set N : Opens M := ⟨c.source ∩ c ⁻¹' W, c.isOpen_inter_preimage W.isOpen⟩
  have hNs : N ≤ Causal.chartSource c := fun z hz => hz.1
  have hNW : Causal.chartImage c N ≤ W := by
    rintro _ ⟨z, ⟨-, hz⟩, rfl⟩; exact hz.2
  have hbN := (Causal.CBG.chartedCausality DY M).le_mem_left h₁
  have hwN := (Causal.CBG.chartedCausality DY M).le_mem_right h₂
  have h₁' := DY.le_mono hNW (((hc N hNs b hbN a ⟨has, hW⟩).1).1 h₁)
  have h₂' := DY.le_mono hNW (((hc N hNs a ⟨has, hW⟩ w hwN).1).1 h₂)
  have hcb : c b ∈ singY 0 := (chartAt_mem_singY_iff hS hbN.1 le_rfl).2 hb
  have hcw : c w ∉ singY 0 := fun h => hw ((chartAt_mem_singY_iff hS hwN.1 le_rfl).1 h)
  have hne' : c b ≠ c a := fun e => hne (c.injOn hbN.1 has e)
  have hlt := hWrel _ _ hcb hcw h₁' hne' h₂'
  exact (Causal.CBG.chartedCausality DY M).lt_mono le_top
    (((hc _ le_rfl b hbN.1 w hwN.1).2).2 hlt)

/-- **`Iplus_of_lt` on every admissible `M`** (DEC-64; `ETT.tex:1352–1355`): for BTZ points
`p ≤ p'`, `p ≠ p'`, the regular part of `J⁺(p')` is in `I⁺(p)`. Along a causal curve from `p'` to a
regular `q`, take the last BTZ point `a` and a regular point `w` just after it; along a causal curve
ending at `a`, a BTZ point `b ≠ a` just before it; then `b ≪ w` in a chart at `a` (the local form),
and push-up. -/
theorem charted_Iplus_of_lt [T1Space M] (hD : DY.CausallyArcConnected) (hP : DY.PushUp)
    (hcl : IsClosed (singY 0)) (hPast : LocPastIn DY (singY 0))
    (hK : ∀ y' ∈ singY 0, ∀ O : Opens Y, y' ∈ O → ∃ W : Opens Y, y' ∈ W ∧ W ≤ O ∧
      ∀ y z, y ∈ singY 0 → z ∉ singY 0 → DY.le W y y' → y ≠ y' → DY.le W y' z → DY.lt O y z) :
    ∀ p ∈ Causal.CBG.chartedSing singY M 0, ∀ p' ∈ Causal.CBG.chartedSing singY M 0,
      (Causal.CBG.chartedCausality DY M).le ⊤ p p' → p ≠ p' →
      (Causal.CBG.chartedCausality DY M).Jplus ⊤ {p'} \ Causal.CBG.chartedSing singY M 0 ⊆
        (Causal.CBG.chartedCausality DY M).Iplus ⊤ {p} := by
  set C := Causal.CBG.chartedCausality DY M
  set S₀ := Causal.CBG.chartedSing singY M 0
  have hCAC : C.CausallyArcConnected := charted_causallyArcConnected (M := M) hGD hA hD
  have hPU : C.PushUp := charted_pushUp (M := M) hGD hA hD hP
  have hS₀ : IsClosed S₀ := charted_isClosed_sing (M := M) hS le_rfl hcl
  have hloc := fun p (hp : p ∈ S₀) => charted_past_local (M := M) hGD hA hS hPast hp
  have hJm : ∀ {q a : M}, a ∈ S₀ → C.le ⊤ q a → q ∈ S₀ := fun {q a} ha hqa => by
    obtain ⟨c, hc, hc0, hc1⟩ := (hCAC ⊤ le_rfl q a).1.1 hqa
    have := Causal.Causality.mem_of_causalCurveOn hS₀ hloc hc le_rfl zero_le_one le_rfl
      (by rw [hc1]; exact ha)
    rwa [hc0] at this
  intro p hp p' hp' hpp' hne q ⟨hq, hqS⟩
  have hp'q : C.le ⊤ p' q := Causal.Precausality.mem_Jplus_singleton.1 hq
  -- the last BTZ point `a` on a causal curve from `p'` to `q`, and a regular `w` just after it
  obtain ⟨d, hd, hd0, hd1⟩ := (hCAC ⊤ le_rfl p' q).1.1 hp'q
  have hdc := hd.continuousOn C.isRelFamily_le
  set Z := {s ∈ Icc (0 : ℝ) 1 | d s ∈ S₀}
  have hZc : IsClosed Z := hdc.preimage_isClosed_of_isClosed isClosed_Icc hS₀
  have hZne : Z.Nonempty := ⟨0, ⟨le_rfl, zero_le_one⟩, by rw [hd0]; exact hp'⟩
  have hZb : BddAbove Z := ⟨1, fun s hs => hs.1.2⟩
  set s₂ := sSup Z
  have hs₂Z : s₂ ∈ Z := hZc.csSup_mem hZne hZb
  have hs₂1 : s₂ < 1 := lt_of_le_of_ne hs₂Z.1.2 fun e => hqS (by rw [← hd1, ← e]; exact hs₂Z.2)
  set a := d s₂
  have haS : a ∈ S₀ := hs₂Z.2
  obtain ⟨N, haN, hNrel⟩ := charted_local_Iplus_of_lt (M := M) hGD hA hS hK haS
  obtain ⟨l, u, hl, hu, hrel⟩ := hd.rel s₂ hs₂Z.1 N le_top haN
  obtain ⟨s, hs1, hs2⟩ := exists_between (lt_min hu hs₂1)
  have hsu : s < u := hs2.trans_le (min_le_left _ _)
  have hs1' : s < 1 := hs2.trans_le (min_le_right _ _)
  have hsI : s ∈ Icc (0 : ℝ) 1 := ⟨hs₂Z.1.1.trans hs1.le, hs1'.le⟩
  set w := d s
  have haw : C.le N a w := hrel s₂ hs₂Z.1 s hsI hl hs1 hsu
  have hwS : w ∉ S₀ := fun h => absurd (le_csSup hZb ⟨hsI, h⟩) (not_le.2 hs1)
  have hwq : C.le ⊤ w q := by
    have := hd.le_of_le hsI.1 hs1'.le le_rfl
    rwa [hd1] at this
  have hp'a : C.le ⊤ p' a := by
    have := hd.le_of_le le_rfl hs₂Z.1.1 hs₂Z.1.2
    rwa [hd0] at this
  -- a starting point `x₀ ∈ {p, p'}` with `p ≤ x₀ ≤ a`, `x₀ ≠ a`
  obtain ⟨x₀, hpx₀, hx₀a, hx₀ne⟩ : ∃ x₀, C.le ⊤ p x₀ ∧ C.le ⊤ x₀ a ∧ x₀ ≠ a := by
    by_cases hpa : p = a
    · exact ⟨p', hpp', hp'a, fun e => hne (hpa.trans e.symm)⟩
    · exact ⟨p, C.le_refl trivial, C.le_trans hpp' hp'a, hpa⟩
  -- a BTZ point `b ≠ a` just before `a` on a causal curve from `x₀`
  obtain ⟨e, he, he0, he1⟩ := (hCAC ⊤ le_rfl x₀ a).1.1 hx₀a
  have hec := he.continuousOn C.isRelFamily_le
  set Z' := {s ∈ Icc (0 : ℝ) 1 | e s ∈ ({a} : Set M)}
  have hZ'c : IsClosed Z' := hec.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hZ'ne : Z'.Nonempty := ⟨1, ⟨zero_le_one, le_rfl⟩, he1⟩
  have hZ'b : BddBelow Z' := ⟨0, fun s hs => hs.1.1⟩
  set s₃ := sInf Z'
  have hs₃Z : s₃ ∈ Z' := hZ'c.csInf_mem hZ'ne hZ'b
  have hs₃0 : 0 < s₃ := lt_of_le_of_ne hs₃Z.1.1 fun e0 => hx₀ne (by
    rw [← he0, e0]; exact hs₃Z.2)
  obtain ⟨l', u', hl', hu', hrel'⟩ := he.rel s₃ hs₃Z.1 N le_top (by
    have : e s₃ = a := hs₃Z.2
    rw [this]; exact haN)
  obtain ⟨t, ht1, ht2⟩ := exists_between (max_lt hl' hs₃0)
  have hlt : l' < t := (le_max_left _ _).trans_lt ht1
  have h0t : 0 < t := (le_max_right _ _).trans_lt ht1
  have htI : t ∈ Icc (0 : ℝ) 1 := ⟨h0t.le, ht2.le.trans hs₃Z.1.2⟩
  set b := e t
  have hba : C.le N b a := by
    have := hrel' t htI s₃ hs₃Z.1 hlt ht2 hu'
    have he3 : e s₃ = a := hs₃Z.2
    rwa [he3] at this
  have hbne : b ≠ a := fun h => absurd (csInf_le hZ'b ⟨htI, h⟩) (not_le.2 ht2)
  have hx₀b : C.le ⊤ x₀ b := by
    have := he.le_of_le le_rfl h0t.le htI.2
    rwa [he0] at this
  have hbS : b ∈ S₀ := hJm haS (C.le_mono le_top hba)
  have hbw : C.lt ⊤ b w := hNrel b w hbS hwS hba hbne haw
  exact Causal.Precausality.mem_Iplus_singleton.2
    (hPU.lt_of_le_of_lt (C.le_trans hpx₀ hx₀b) (hPU.lt_of_lt_of_le hbw hwq))

end ChartedIplus


/-! ### §3c `SingularPastAt` on every admissible `M` -/

section ChartedPast

universe u

variable {Y : Type u} [TopologicalSpace Y] {G : StructureGroupoid Y} {DY : Causal.Causality Y}
  {singY : ℝ → Set Y} {M : Type u} [TopologicalSpace M] [ChartedSpace Y M] [HasGroupoid M G]
  (hGD : ∀ e ∈ G, Causal.ChartIso DY DY e) (hA : ∀ W : Opens Y, DY.AbsolutelyMinimalOn W)
  (hS : ∀ e ∈ G, ∀ y ∈ e.source, ∀ α : ℝ, 0 ≤ α → (y ∈ singY α ↔ e y ∈ singY α))
include hGD hA hS

/-- (A1) read in the chart at a BTZ point of `M`. -/
theorem charted_exists_below
    (hA1 : ∀ y' ∈ singY 0, ∀ O : Opens Y, y' ∈ O → ∀ N ∈ 𝓝 y',
      ∃ y ∈ N, y ∈ singY 0 ∧ y ≠ y' ∧ DY.le O y y')
    {p : M} (hp : p ∈ Causal.CBG.chartedSing singY M 0) {N : Set M} (hN : N ∈ 𝓝 p) :
    ∃ y ∈ N, y ∈ Causal.CBG.chartedSing singY M 0 ∧ y ≠ p ∧
      (Causal.CBG.chartedCausality DY M).le ⊤ y p := by
  set c := chartAt Y p
  have hps : p ∈ c.source := mem_chart_source Y p
  have hc := Causal.CBG.chartedCausality_chartIso (M := M) hGD hA p
  obtain ⟨y', hy'N, hy's, hne, hle⟩ := hA1 (c p) hp (Causal.chartImage c (Causal.chartSource c))
    (Causal.mem_chartImage_of_mem hps hps) _
    (c.image_mem_nhds hps (inter_mem hN (c.open_source.mem_nhds hps)))
  obtain ⟨y, ⟨hyN, hys⟩, rfl⟩ := hy'N
  exact ⟨y, hyN, (chartAt_mem_singY_iff hS hys le_rfl).1 hy's, fun e => hne (by rw [e]),
    (Causal.CBG.chartedCausality DY M).le_mono le_top (((hc _ le_rfl y hys p hps).1).2 hle)⟩

/-- (A2) read in the chart at a BTZ point of `M`. -/
theorem charted_future_nhds
    (hA2 : ∀ a ∈ singY 0, ∀ O : Opens Y, a ∈ O → ∃ W : Opens Y, a ∈ W ∧ W ≤ O ∧
      ∀ b, b ∈ singY 0 → DY.le W b a → b ≠ a → ∃ V ∈ 𝓝 a, ∀ z ∈ V, DY.le O b z)
    {p : M} (hp : p ∈ Causal.CBG.chartedSing singY M 0) :
    ∃ N : Opens M, p ∈ N ∧ ∀ b, b ∈ Causal.CBG.chartedSing singY M 0 →
      (Causal.CBG.chartedCausality DY M).le N b p → b ≠ p →
      (Causal.CBG.chartedCausality DY M).Jplus ⊤ {b} ∈ 𝓝 p := by
  set c := chartAt Y p
  have hps : p ∈ c.source := mem_chart_source Y p
  have hc := Causal.CBG.chartedCausality_chartIso (M := M) hGD hA p
  obtain ⟨W, hW, -, hrel⟩ := hA2 (c p) hp (Causal.chartImage c (Causal.chartSource c))
    (Causal.mem_chartImage_of_mem hps hps)
  refine ⟨⟨c.source ∩ c ⁻¹' W, c.isOpen_inter_preimage W.isOpen⟩, ⟨hps, hW⟩,
    fun b hb h₁ hne => ?_⟩
  set N : Opens M := ⟨c.source ∩ c ⁻¹' W, c.isOpen_inter_preimage W.isOpen⟩
  have hNs : N ≤ Causal.chartSource c := fun z hz => hz.1
  have hNW : Causal.chartImage c N ≤ W := by
    rintro _ ⟨z, ⟨-, hz⟩, rfl⟩; exact hz.2
  have hbN := (Causal.CBG.chartedCausality DY M).le_mem_left h₁
  have h₁' := DY.le_mono hNW (((hc N hNs b hbN p ⟨hps, hW⟩).1).1 h₁)
  have hcb : c b ∈ singY 0 := (chartAt_mem_singY_iff hS hbN.1 le_rfl).2 hb
  have hne' : c b ≠ c p := fun e => hne (c.injOn hbN.1 hps e)
  obtain ⟨V, hV, hVrel⟩ := hrel _ hcb h₁' hne'
  refine mem_of_superset (inter_mem (c.open_source.mem_nhds hps)
    (c.continuousAt hps hV)) fun m hm => ?_
  exact Causal.Precausality.mem_Jplus_singleton.2 ((Causal.CBG.chartedCausality DY M).le_mono
    le_top (((hc _ le_rfl b hbN.1 m hm.1).1).2 (hVrel _ hm.2)))

/-- (A3) read in the chart at a BTZ point of `M`. -/
theorem charted_past_nhds
    (hA3 : ∀ x ∈ singY 0, ∀ O : Opens Y, x ∈ O → ∃ W : Opens Y, x ∈ W ∧ W ≤ O ∧
      ∀ v, v ∈ singY 0 → DY.le W x v → v ≠ x → ∃ V ∈ 𝓝 x, ∀ y ∈ V, y ∈ singY 0 → DY.le O y v)
    {x : M} (hx : x ∈ Causal.CBG.chartedSing singY M 0) :
    ∃ N : Opens M, x ∈ N ∧ ∀ v, v ∈ Causal.CBG.chartedSing singY M 0 →
      (Causal.CBG.chartedCausality DY M).le N x v → v ≠ x →
      ∃ V ∈ 𝓝 x, ∀ y ∈ V, y ∈ Causal.CBG.chartedSing singY M 0 →
        (Causal.CBG.chartedCausality DY M).le ⊤ y v := by
  set c := chartAt Y x
  have hxs : x ∈ c.source := mem_chart_source Y x
  have hc := Causal.CBG.chartedCausality_chartIso (M := M) hGD hA x
  obtain ⟨W, hW, -, hrel⟩ := hA3 (c x) hx (Causal.chartImage c (Causal.chartSource c))
    (Causal.mem_chartImage_of_mem hxs hxs)
  refine ⟨⟨c.source ∩ c ⁻¹' W, c.isOpen_inter_preimage W.isOpen⟩, ⟨hxs, hW⟩,
    fun v hv h₁ hne => ?_⟩
  set N : Opens M := ⟨c.source ∩ c ⁻¹' W, c.isOpen_inter_preimage W.isOpen⟩
  have hNs : N ≤ Causal.chartSource c := fun z hz => hz.1
  have hNW : Causal.chartImage c N ≤ W := by
    rintro _ ⟨z, ⟨-, hz⟩, rfl⟩; exact hz.2
  have hvN := (Causal.CBG.chartedCausality DY M).le_mem_right h₁
  have h₁' := DY.le_mono hNW (((hc N hNs x ⟨hxs, hW⟩ v hvN).1).1 h₁)
  have hcv : c v ∈ singY 0 := (chartAt_mem_singY_iff hS hvN.1 le_rfl).2 hv
  have hne' : c v ≠ c x := fun e => hne (c.injOn hvN.1 hxs e)
  obtain ⟨V, hV, hVrel⟩ := hrel _ hcv h₁' hne'
  refine ⟨c.source ∩ c ⁻¹' V, inter_mem (c.open_source.mem_nhds hxs) (c.continuousAt hxs hV),
    fun y hy hys => ?_⟩
  exact (Causal.CBG.chartedCausality DY M).le_mono le_top (((hc _ le_rfl y hy.1 v hvN.1).1).2
    (hVrel _ hy.2 ((chartAt_mem_singY_iff hS hy.1 le_rfl).2 hys)))

/-- **`SingularPastAt` at every BTZ point of an admissible `M`** (`ETT.tex:1349`, the form the
proof of `prop:K_calcul` (c) uses): points of the BTZ line strictly below `p` accumulate at `p`; for
`x < p`, an increasing sequence on a causal curve from `x` to `p`, starting just above `x`, tends
to `p`, each of its points has `p` in the interior of its future (the local future of a lower axis
point, (A2)), and `J⁻(u₀)` is a neighbourhood of `x` in `J⁻(p)` ((A3)). -/
theorem charted_singularPastAt [T2Space M] [FirstCountableTopology M]
    (hD : DY.CausallyArcConnected) (hcl : IsClosed (singY 0)) (hPast : LocPastIn DY (singY 0))
    (hA1 : ∀ y' ∈ singY 0, ∀ O : Opens Y, y' ∈ O → ∀ N ∈ 𝓝 y',
      ∃ y ∈ N, y ∈ singY 0 ∧ y ≠ y' ∧ DY.le O y y')
    (hA2 : ∀ a ∈ singY 0, ∀ O : Opens Y, a ∈ O → ∃ W : Opens Y, a ∈ W ∧ W ≤ O ∧
      ∀ b, b ∈ singY 0 → DY.le W b a → b ≠ a → ∃ V ∈ 𝓝 a, ∀ z ∈ V, DY.le O b z)
    (hA3 : ∀ x ∈ singY 0, ∀ O : Opens Y, x ∈ O → ∃ W : Opens Y, x ∈ W ∧ W ≤ O ∧
      ∀ v, v ∈ singY 0 → DY.le W x v → v ≠ x → ∃ V ∈ 𝓝 x, ∀ y ∈ V, y ∈ singY 0 → DY.le O y v) :
    ∀ p ∈ Causal.CBG.chartedSing singY M 0,
      (Causal.CBG.chartedCausality DY M).SingularPastAt p := by
  set C := Causal.CBG.chartedCausality DY M
  set S₀ := Causal.CBG.chartedSing singY M 0
  have hCAC : C.CausallyArcConnected := charted_causallyArcConnected (M := M) hGD hA hD
  have hS₀ : IsClosed S₀ := charted_isClosed_sing (M := M) hS le_rfl hcl
  have hloc := fun p (hp : p ∈ S₀) => charted_past_local (M := M) hGD hA hS hPast hp
  have hJm : ∀ {q a : M}, a ∈ S₀ → C.le ⊤ q a → q ∈ S₀ := fun {q a} ha hqa => by
    obtain ⟨c, hc, hc0, hc1⟩ := (hCAC ⊤ le_rfl q a).1.1 hqa
    have := Causal.Causality.mem_of_causalCurveOn hS₀ hloc hc le_rfl zero_le_one le_rfl
      (by rw [hc1]; exact ha)
    rwa [hc0] at this
  intro p hp
  refine ⟨?_, fun x hxp hxne => ?_⟩
  · -- (i) points of the line strictly below `p`, tending to `p`
    obtain ⟨B, hB⟩ := (𝓝 p).exists_antitone_basis
    choose u hu using fun n => charted_exists_below (M := M) hGD hA hS hA1 hp (hB.mem n)
    exact ⟨u, hB.tendsto fun n => (hu n).1, fun n => ⟨(hu n).2.2.2, (hu n).2.2.1⟩⟩
  · -- (ii)
    obtain ⟨e, he, he0, he1⟩ := (hCAC ⊤ le_rfl x p).1.1 hxp
    have hec := he.continuousOn C.isRelFamily_le
    set Z := {s ∈ Icc (0 : ℝ) 1 | e s ∈ ({p} : Set M)}
    have hZc : IsClosed Z := hec.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
    have hZne : Z.Nonempty := ⟨1, ⟨zero_le_one, le_rfl⟩, he1⟩
    have hZb : BddBelow Z := ⟨0, fun s hs => hs.1.1⟩
    set s₃ := sInf Z
    have hs₃Z : s₃ ∈ Z := hZc.csInf_mem hZne hZb
    have hes₃ : e s₃ = p := hs₃Z.2
    have hlow : ∀ s ∈ Icc (0 : ℝ) 1, s < s₃ → e s ≠ p := fun s hs hss h =>
      absurd (csInf_le hZb ⟨hs, h⟩) (not_le.2 hss)
    -- the last parameter `s_x ≤ s₃` at `x`
    set Zx := {s ∈ Icc (0 : ℝ) s₃ | e s ∈ ({x} : Set M)}
    have hZxc : IsClosed Zx :=
      (hec.mono (Icc_subset_Icc le_rfl hs₃Z.1.2)).preimage_isClosed_of_isClosed isClosed_Icc
        isClosed_singleton
    have hZxne : Zx.Nonempty := ⟨0, ⟨le_rfl, hs₃Z.1.1⟩, he0⟩
    have hZxb : BddAbove Zx := ⟨s₃, fun s hs => hs.1.2⟩
    set sx := sSup Zx
    have hsxZ : sx ∈ Zx := hZxc.csSup_mem hZxne hZxb
    have hesx : e sx = x := hsxZ.2
    have hsxI : sx ∈ Icc (0 : ℝ) 1 := ⟨hsxZ.1.1, hsxZ.1.2.trans hs₃Z.1.2⟩
    have hsx3 : sx < s₃ := lt_of_le_of_ne hsxZ.1.2 fun h => hxne (by rw [← hesx, h, hes₃])
    have hxS : x ∈ S₀ := hJm hp hxp
    -- `v = e t₀`, just above `x`
    obtain ⟨Nx, hxNx, hNx⟩ := charted_past_nhds (M := M) hGD hA hS hA3 hxS
    obtain ⟨l, u', hl, hu', hrel⟩ := he.rel sx hsxI Nx le_top (by rw [hesx]; exact hxNx)
    obtain ⟨t₀, ht1, ht2⟩ := exists_between (lt_min hu' hsx3)
    have ht₀u : t₀ < u' := ht2.trans_le (min_le_left _ _)
    have ht₀3 : t₀ < s₃ := ht2.trans_le (min_le_right _ _)
    have ht₀I : t₀ ∈ Icc (0 : ℝ) 1 := ⟨hsxI.1.trans ht1.le, ht₀3.le.trans hs₃Z.1.2⟩
    have hxv : C.le Nx x (e t₀) := by
      have := hrel sx hsxI t₀ ht₀I hl ht1 ht₀u
      rwa [hesx] at this
    have hvx : e t₀ ≠ x := fun h =>
      absurd (le_csSup hZxb ⟨⟨ht₀I.1, ht₀3.le⟩, h⟩) (not_le.2 ht1)
    have hvp : C.le ⊤ (e t₀) p := by
      have := he.le_of_le ht₀I.1 ht₀3.le hs₃Z.1.2
      rwa [hes₃] at this
    obtain ⟨V, hV, hVrel⟩ := hNx (e t₀) (hJm hp hvp) hxv hvx
    -- the sequence `t n ↑ s₃`
    set t : ℕ → ℝ := fun n => s₃ - (s₃ - t₀) / ((n : ℝ) + 1)
    have ht0 : t 0 = t₀ := by simp [t]
    have htI : ∀ n, t n ∈ Icc (0 : ℝ) 1 := fun n => by
      have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by have := n.cast_nonneg (α := ℝ); linarith
      have h1 : (s₃ - t₀) / ((n : ℝ) + 1) ≤ s₃ - t₀ := div_le_self (by linarith) hn
      have h2 : 0 < (s₃ - t₀) / ((n : ℝ) + 1) := div_pos (by linarith) (by linarith)
      exact ⟨by simp only [t]; linarith [ht₀I.1], by simp only [t]; linarith [hs₃Z.1.2]⟩
    have hts₃ : ∀ n, t n < s₃ := fun n => by
      have : 0 < (s₃ - t₀) / ((n : ℝ) + 1) := div_pos (by linarith) (by positivity)
      simp only [t]; linarith
    have htmono : Monotone t := by
      intro m n hmn
      simp only [t]
      have hmn' : (m : ℝ) + 1 ≤ (n : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hmn 1
      have := div_le_div_of_nonneg_left (by linarith : (0 : ℝ) ≤ s₃ - t₀) (by positivity) hmn'
      linarith
    have httend : Tendsto t atTop (𝓝 s₃) := by
      have : Tendsto (fun n : ℕ => (s₃ - t₀) / ((n : ℝ) + 1)) atTop (𝓝 0) := by
        simpa [div_eq_mul_inv] using
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (s₃ - t₀)
      simpa using (tendsto_const_nhds (x := s₃)).sub this
    have hutend : Tendsto (fun n => e (t n)) atTop (𝓝 p) := by
      rw [← hes₃]
      exact (hec s₃ hs₃Z.1).tendsto.comp (tendsto_nhdsWithin_iff.2
        ⟨httend, Eventually.of_forall htI⟩)
    obtain ⟨Np, hpNp, hNp⟩ := charted_future_nhds (M := M) hGD hA hS hA2 hp
    obtain ⟨l₃, u₃, hl₃, hu₃, hrel₃⟩ := he.rel s₃ hs₃Z.1 Np le_top (by rw [hes₃]; exact hpNp)
    refine ⟨fun n => e (t n), hutend, fun m n hmn => he.le_of_le (htI m).1 (htmono hmn) (htI n).2,
      fun n => ?_, ?_⟩
    · obtain ⟨k, hk⟩ := (httend.eventually (lt_mem_nhds hl₃)).exists_forall_of_atTop
      set m := max n k
      have hlm : l₃ < t m := hk m (le_max_right _ _)
      have hum : C.le Np (e (t m)) p := by
        have := hrel₃ (t m) (htI m) s₃ hs₃Z.1 hlm (hts₃ m) hu₃
        rwa [hes₃] at this
      have hJ := hNp _ (hJm hp (C.le_mono le_top hum)) hum
        (hlow _ (htI m) (hts₃ m))
      refine mem_interior_iff_mem_nhds.2 (mem_of_superset hJ fun z hz => ?_)
      exact Causal.Precausality.mem_Jplus_singleton.2 (C.le_trans
        (he.le_of_le (htI n).1 (htmono (le_max_left _ _)) (htI m).2)
        (Causal.Precausality.mem_Jplus_singleton.1 hz))
    · refine ⟨Causal.Precausality.mem_Jminus_singleton.2 hxp, ?_⟩
      show C.Jminus ⊤ {e (t 0)} ∈ 𝓝[C.Jminus ⊤ {p}] x
      rw [ht0]
      exact mem_nhdsWithin_iff_exists_mem_nhds_inter.2 ⟨V, hV, fun y hy =>
        Causal.Precausality.mem_Jminus_singleton.2 (hVrel y hy.1
          (hJm hp (Causal.Precausality.mem_Jminus_singleton.1 hy.2)))⟩

end ChartedPast


/-! ### §4 The topology of `Y`, and `SingularFlatAxioms` on `𝔼₀`-manifolds -/

section E0Topology

/-- Model's `𝔼₀` is locally compact (`toPaper : BTZE0 ≃ₜ ℝ × ℂ`). -/
instance locallyCompactSpace_btzE0 : LocallyCompactSpace BTZE0 :=
  E0.toPaper.isOpenEmbedding.locallyCompactSpace

/-- A disjoint union of weakly locally compact spaces is weakly locally compact (a general fact,
used here only as a local instance; to move to a general GX topology file at graduation). -/
theorem weaklyLocallyCompactSpace_sum {X Z : Type*} [TopologicalSpace X] [TopologicalSpace Z]
    [WeaklyLocallyCompactSpace X] [WeaklyLocallyCompactSpace Z] :
    WeaklyLocallyCompactSpace (X ⊕ Z) where
  exists_compact_mem_nhds y := by
    rcases y with a | a
    · obtain ⟨K, hK, hKa⟩ := exists_compact_mem_nhds a
      exact ⟨Sum.inl '' K, hK.image continuous_inl,
        IsOpenEmbedding.inl.isOpenMap.image_mem_nhds hKa⟩
    · obtain ⟨K, hK, hKa⟩ := exists_compact_mem_nhds a
      exact ⟨Sum.inr '' K, hK.image continuous_inr,
        IsOpenEmbedding.inr.isOpenMap.image_mem_nhds hKa⟩

attribute [local instance] weaklyLocallyCompactSpace_sum in
/-- `Y` is locally compact. -/
instance locallyCompactSpace_e0Y : LocallyCompactSpace E0Y := inferInstance

theorem nhdsNE_neBot_of_isOpenEmbedding {X Z : Type*} [TopologicalSpace X] [TopologicalSpace Z]
    {f : X → Z} (hf : IsOpenEmbedding f) (x : X) [(𝓝[≠] x).NeBot] : (𝓝[≠] (f x)).NeBot := by
  have : Tendsto f (𝓝[≠] x) (𝓝[≠] (f x)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (hf.continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
      (eventually_nhdsWithin_of_forall fun y hy h => hy (hf.injective h))
  exact this.neBot

/-- `Y` has no isolated point. -/
theorem e0Y_nhdsNE_neBot (y : E0Y) : (𝓝[≠] y).NeBot := by
  rcases y with m | x
  · exact nhdsNE_neBot_of_isOpenEmbedding IsOpenEmbedding.inl m
  · have h := nhdsNE_neBot_of_isOpenEmbedding E0.toPaper.symm.isOpenEmbedding (E0.toPaper x)
    rw [Homeomorph.symm_apply_apply] at h
    exact nhdsNE_neBot_of_isOpenEmbedding IsOpenEmbedding.inr x

theorem isClosed_e0SingY (α : ℝ) : IsClosed (e0SingY α) := by
  by_cases h : α = 0
  · subst h
    have : e0SingY 0 = e0Regᶜ := by ext y; simp [e0SingY]
    rw [this]; exact isOpen_e0Reg.isClosed_compl
  · rw [e0SingY_of_ne h]; exact isClosed_empty

theorem interior_e0SingY (α : ℝ) : interior (e0SingY α) = ∅ := by
  by_cases h : α = 0
  · subst h
    have : e0SingY 0 = e0Regᶜ := by ext y; simp [e0SingY]
    rw [this, interior_compl, dense_e0Reg.closure_eq, compl_univ]
  · rw [e0SingY_of_ne h, interior_empty]

end E0Topology

section E0SFA

/-- **The global BTZ fact of an `𝔼₀`-manifold not proved here** (the one field of
`Causal.Causality.SingularFlatAxioms` that §3's transfers do not reach): the component of the BTZ
locus through a point is an inextensible causal curve parametrised by `ℝ` (`lem:past_BTZ` (a),
`ETT.tex:1518, 1527–1531`). -/
structure E0GlobalBTZ {M : Type*} [TopologicalSpace M] (C : Causal.Causality M) (S₀ : Set M) :
    Prop where
  line : ∀ p ∈ S₀, ∃ γ : ℝ → M, γ 0 = p ∧ (C.IsCausal → IsClosedEmbedding γ) ∧
    C.Inextensible ⊤ univ γ ∧ range γ = connectedComponentIn S₀ p

variable (hGD : ∀ e ∈ e0Groupoid, Causal.ChartIso D D e)
include hGD

/-- **`Causal.SingularFlatAxioms` on every `𝔼₀`-manifold, from its one global BTZ fact** (the
line, `E0GlobalBTZ`): every
other field — absolute minimality, causal arc-connectedness, tarentinity, `Z⁺ = M`,
`Z⁻ = M ∖ sing₀`, `I⁻(p) = ∅` and `past_local` at BTZ points, and the topology — is proved here
from the model (§2, §3). -/
theorem e0_singularFlatAxioms_of {M : Type} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [ChartedSpace E0Y M] [HasGroupoid M e0Groupoid]
    (h : E0GlobalBTZ (Causal.CBG.chartedCausality D M) (Causal.CBG.chartedSing e0SingY M 0)) :
    (Causal.CBG.chartedCausality D M).SingularFlatAxioms (Causal.CBG.chartedSing e0SingY M) := by
  have hA := E0.absolutelyMinimalOn_YBTZ
  haveI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace E0Y M
  exact
    { singularPastAt := charted_singularPastAt (M := M) hGD hA e0_sing_mem
        E0.causalityYBTZ_causallyArcConnected (isClosed_e0SingY 0) yb_locPastIn yb_exists_below
        yb_future_nhds yb_past_nhds
      Iminus_eq_empty := fun p hp =>
        charted_Iminus_eq_empty (M := M) hGD hA e0_sing_mem yb_locNoPast hp
      Iplus_of_lt := charted_Iplus_of_lt (M := M) hGD hA e0_sing_mem
        E0.causalityYBTZ_causallyArcConnected yb_pushUp (isClosed_e0SingY 0) yb_locPastIn
        yb_local_Iplus_of_lt
      past_local := fun p hp => charted_past_local (M := M) hGD hA e0_sing_mem yb_locPastIn hp
      line := h.line
      pushUp := charted_pushUp (M := M) hGD hA E0.causalityYBTZ_causallyArcConnected yb_pushUp
      absolutelyMinimal := Causal.CBG.chartedCausality_absolutelyMinimal hA
      causallyArcConnected :=
        charted_causallyArcConnected (M := M) hGD hA E0.causalityYBTZ_causallyArcConnected
      tarentin := charted_tarentin (M := M) hGD hA yb_locTarentin
      mem_Zplus := charted_mem_Zplus (M := M) hGD hA yb_locZplus
      mem_Zminus_iff := fun p => ⟨fun hp hps => by
          obtain ⟨z, hz, -⟩ := hp univ univ_mem
          rw [charted_Iminus_eq_empty (M := M) hGD hA e0_sing_mem yb_locNoPast hps] at hz
          exact hz,
        fun hp => charted_mem_Zminus (M := M) hGD hA yb_locZminus hp⟩
      t2 := inferInstance
      secondCountable := inferInstance
      metrizable := TopologicalSpace.metrizableSpace_of_t3_secondCountable M
      locallyCompact := inferInstance
      noIsolated := charted_nhdsNE_neBot (M := M) e0Y_nhdsNE_neBot
      isClosed_sing := fun α hα => charted_isClosed_sing (M := M) e0_sing_mem hα (isClosed_e0SingY α)
      interior_sing := fun α hα => charted_interior_sing (M := M) e0_sing_mem hα (interior_e0SingY α)
      massive_line := fun α hα p hp => by
        have : p ∈ Causal.CBG.chartedSing e0SingY M α := hp
        simp only [Causal.CBG.chartedSing, e0SingY_of_ne hα.ne', mem_setOf_eq,
          mem_empty_iff_false] at this }

end E0SFA


/-! ### §5 Global consequences of `SingularFlatAxioms`: `J^±` of open sets, `J^±(Σ)` closed -/

section SFAGlobal

variable {M : Type*} [TopologicalSpace M] {C : Causal.Causality M} {sing : ℝ → Set M}

/-- **`J⁻(W)` is open for every open `W`**: every point is in `Z⁺`, and push-up. -/
theorem sfa_isOpen_Jminus (h : C.SingularFlatAxioms sing) {W : Set M} (hW : IsOpen W) :
    IsOpen (C.Jminus ⊤ W) := by
  rw [isOpen_iff_mem_nhds]
  rintro x ⟨w, hw, hxw⟩
  obtain ⟨w', hw'I, hw'W⟩ := h.mem_Zplus w W (hW.mem_nhds hw)
  have hxw' : C.lt ⊤ x w' :=
    h.pushUp.lt_of_le_of_lt hxw (Causal.Precausality.mem_Iplus_singleton.1 hw'I)
  exact mem_of_superset (C.isOpen_Iminus.mem_nhds (Causal.Precausality.mem_Iminus_singleton.2 hxw'))
    fun z hz => ⟨w', hw'W, C.le_of_lt (Causal.Precausality.mem_Iminus_singleton.1 hz)⟩

/-- **`J⁺(W)` is open for every open `W`, BTZ points included** (lemma K's obligation): from a
regular point push-up from below; from a BTZ point to a regular one `Iplus_of_lt` along the line;
between two BTZ points the half-line structure of the past (`SingularPastAt`). -/
theorem sfa_isOpen_Jplus (h : C.SingularFlatAxioms sing) {W : Set M} (hW : IsOpen W) :
    IsOpen (C.Jplus ⊤ W) := by
  haveI := h.t2
  rw [isOpen_iff_mem_nhds]
  rintro x ⟨w, hw, hwx⟩
  by_cases hxW : x ∈ W
  · exact mem_of_superset (hW.mem_nhds hxW) fun z hz => ⟨z, hz, C.le_refl trivial⟩
  have hne : w ≠ x := fun e => hxW (e ▸ hw)
  by_cases hws : w ∈ sing 0
  · by_cases hxs : x ∈ sing 0
    · obtain ⟨u, -, -, hint, h0⟩ := (h.singularPastAt x hxs).2 w hwx hne
      have hwu : C.le ⊤ w (u 0) :=
        Causal.Precausality.mem_Jminus_singleton.1 (Causal.interiorWithin_subset h0)
      refine mem_of_superset (mem_interior_iff_mem_nhds.1 (hint 0)) fun z hz => ⟨w, hw, ?_⟩
      exact C.le_trans hwu (Causal.Precausality.mem_Jplus_singleton.1 hz)
    · obtain ⟨⟨u, hu, hup⟩, -⟩ := h.singularPastAt w hws
      obtain ⟨n, hn⟩ := (hu.eventually (hW.mem_nhds hw)).exists
      have hus : u n ∈ sing 0 := h.mem_sing_zero_of_le hws (hup n).1
      have hlt : C.lt ⊤ (u n) x :=
        h.lt_of_lt_of_le_of_not_mem hus hws (hup n).1 (hup n).2 hxs hwx
      exact mem_of_superset (C.isOpen_Iplus.mem_nhds (Causal.Precausality.mem_Iplus_singleton.2 hlt))
        fun z hz => ⟨u n, hn, C.le_of_lt (Causal.Precausality.mem_Iplus_singleton.1 hz)⟩
  · obtain ⟨w', hw'I, hw'W⟩ := (h.mem_Zminus_iff w).2 hws W (hW.mem_nhds hw)
    have hlt : C.lt ⊤ w' x :=
      h.pushUp.lt_of_lt_of_le (Causal.Precausality.mem_Iminus_singleton.1 hw'I) hwx
    exact mem_of_superset (C.isOpen_Iplus.mem_nhds (Causal.Precausality.mem_Iplus_singleton.2 hlt))
      fun z hz => ⟨w', hw'W, C.le_of_lt (Causal.Precausality.mem_Iplus_singleton.1 hz)⟩

end SFAGlobal


section CauchyClosed

variable {M : Type*} [TopologicalSpace M] {C : Causal.Causality M} {S : Set M} {p : M}

/-- **A chronological witness outside `J⁺(Σ)`** above a point `p ∉ J⁺(Σ)` of `Z⁺`: on a chronal curve
`p ≪ ·` extended to an inextensible one, the meeting point `σ` with `Σ` is comparable with every
point; if `σ ≤ c(t)` held for every `t > 0`, closedness of `J⁺(σ)` would give `σ ≤ p`. -/
theorem exists_lt_notMem_Jplus (hcac : C.CausallyArcConnected) (hext : C.CurvesExtend)
    (hZ : p ∈ C.Zplus) (hJ : ∀ σ, IsClosed (C.Jplus ⊤ {σ})) (hS : C.IsCauchySurface S)
    (hac : C.IsAcausal S) (hp : p ∉ C.Jplus ⊤ S) : ∃ r ∉ C.Jplus ⊤ S, C.lt ⊤ p r := by
  obtain ⟨r₀, hr₀, -⟩ := hZ univ univ_mem
  obtain ⟨c, hc, hc0, hc1⟩ := (hcac ⊤ le_rfl p r₀).2.1 (Causal.Precausality.mem_Iplus_singleton.1 hr₀)
  obtain ⟨I, c', hc', hsub⟩ := hext c 0 1 zero_le_one hc.causalCurveOn
  obtain ⟨σ, ⟨⟨s₀, hs₀I, rfl⟩, hσS⟩, -⟩ := hS I c' hc'
  have hcomp : ∀ t ∈ Icc (0 : ℝ) 1, C.le ⊤ (c t) (c' s₀) ∨ C.le ⊤ (c' s₀) (c t) := by
    intro t ht
    obtain ⟨a, haI, ha⟩ := hsub ⟨t, ht, rfl⟩
    rw [← ha]
    rcases le_total a s₀ with h | h
    · exact Or.inl (hc'.1.le_of_le haI hs₀I h)
    · exact Or.inr (hc'.1.le_of_le hs₀I haI h)
  by_contra hcon
  push Not at hcon
  have hall : ∀ t ∈ Ioo (0 : ℝ) 1, c t ∈ C.Jplus ⊤ {c' s₀} := by
    intro t ht
    rw [Causal.Precausality.mem_Jplus_singleton]
    by_contra hnot
    have hle : C.le ⊤ (c t) (c' s₀) := (hcomp t ⟨ht.1.le, ht.2.le⟩).resolve_right hnot
    have hlt : C.lt ⊤ p (c t) := by
      have := hc.lt_of_lt le_rfl ht.1 ht.2.le
      rwa [hc0] at this
    refine hcon (c t) ?_ hlt
    rintro ⟨σ', hσ'S, hσ'c⟩
    have he := hac σ' hσ'S _ hσS (C.le_trans hσ'c hle)
    subst he
    exact hnot hσ'c
  have hcont := (hc.causalCurveOn.continuousOn C.isRelFamily_le) 0 ⟨le_rfl, zero_le_one⟩
  have htend : Tendsto c (𝓝[>] (0 : ℝ)) (𝓝 (c 0)) := by
    have := (hcont.mono Ioo_subset_Icc_self).tendsto
    rwa [nhdsWithin_Ioo_eq_nhdsGT zero_lt_one] at this
  have hmem : c 0 ∈ C.Jplus ⊤ {c' s₀} := (hJ _).mem_of_tendsto htend
    (mem_of_superset (Ioo_mem_nhdsGT zero_lt_one) fun t ht => hall t ht)
  rw [hc0] at hmem
  exact hp ⟨c' s₀, hσS, Causal.Precausality.mem_Jplus_singleton.1 hmem⟩

/-- **A chronological witness outside `J⁻(Σ)`** below a point `p ∉ J⁻(Σ)` of `Z⁻`. -/
theorem exists_lt_notMem_Jminus (hcac : C.CausallyArcConnected) (hext : C.CurvesExtend)
    (hZ : p ∈ C.Zminus) (hJ : ∀ σ, IsClosed (C.Jminus ⊤ {σ})) (hS : C.IsCauchySurface S)
    (hac : C.IsAcausal S) (hp : p ∉ C.Jminus ⊤ S) : ∃ r ∉ C.Jminus ⊤ S, C.lt ⊤ r p := by
  obtain ⟨r₀, hr₀, -⟩ := hZ univ univ_mem
  obtain ⟨c, hc, hc0, hc1⟩ := (hcac ⊤ le_rfl r₀ p).2.1 (Causal.Precausality.mem_Iminus_singleton.1 hr₀)
  obtain ⟨I, c', hc', hsub⟩ := hext c 0 1 zero_le_one hc.causalCurveOn
  obtain ⟨σ, ⟨⟨s₀, hs₀I, rfl⟩, hσS⟩, -⟩ := hS I c' hc'
  have hcomp : ∀ t ∈ Icc (0 : ℝ) 1, C.le ⊤ (c t) (c' s₀) ∨ C.le ⊤ (c' s₀) (c t) := by
    intro t ht
    obtain ⟨a, haI, ha⟩ := hsub ⟨t, ht, rfl⟩
    rw [← ha]
    rcases le_total a s₀ with h | h
    · exact Or.inl (hc'.1.le_of_le haI hs₀I h)
    · exact Or.inr (hc'.1.le_of_le hs₀I haI h)
  by_contra hcon
  push Not at hcon
  have hall : ∀ t ∈ Ioo (0 : ℝ) 1, c t ∈ C.Jminus ⊤ {c' s₀} := by
    intro t ht
    rw [Causal.Precausality.mem_Jminus_singleton]
    by_contra hnot
    have hle : C.le ⊤ (c' s₀) (c t) := (hcomp t ⟨ht.1.le, ht.2.le⟩).resolve_left hnot
    have hlt : C.lt ⊤ (c t) p := by
      have := hc.lt_of_lt ht.1.le ht.2 le_rfl
      rwa [hc1] at this
    refine hcon (c t) ?_ hlt
    rintro ⟨σ', hσ'S, hcσ'⟩
    have he := hac _ hσS σ' hσ'S (C.le_trans hle hcσ')
    subst he
    exact hnot hcσ'
  have hcont := (hc.causalCurveOn.continuousOn C.isRelFamily_le) 1 ⟨zero_le_one, le_rfl⟩
  have htend : Tendsto c (𝓝[<] (1 : ℝ)) (𝓝 (c 1)) := by
    have := (hcont.mono Ioo_subset_Icc_self).tendsto
    rwa [nhdsWithin_Ioo_eq_nhdsLT zero_lt_one] at this
  have hmem : c 1 ∈ C.Jminus ⊤ {c' s₀} := (hJ _).mem_of_tendsto htend
    (mem_of_superset (Ioo_mem_nhdsLT zero_lt_one) fun t ht => hall t ht)
  rw [hc1] at hmem
  exact hp ⟨c' s₀, hσS, Causal.Precausality.mem_Jminus_singleton.1 hmem⟩

/-- **At a BTZ point `p ∉ J⁻(Σ)`, a neighbourhood `J⁺(r)` with `r ∉ J⁻(Σ)`**: `p` lies above the
point `σ` where an inextensible curve through it meets `Σ`; `σ` is on the BTZ half-line below `p`,
and a point `r` of that half-line strictly between `σ` and `p` has `p ∈ Int J⁺(r)`
(`SingularPastAt`). -/
theorem exists_nhds_notMem_Jminus_of_singularPastAt [T2Space M] (hcaus : C.IsCausal)
    (hext : C.CurvesExtend) (hSP : C.SingularPastAt p) (hS : C.IsCauchySurface S)
    (hac : C.IsAcausal S) (hp : p ∉ C.Jminus ⊤ S) :
    ∃ r ∉ C.Jminus ⊤ S, C.Jplus ⊤ {r} ∈ 𝓝 p := by
  obtain ⟨I, c', hc', hsub⟩ := hext (fun _ => p) 0 0 le_rfl
    (Causal.Causality.causalCurveOn_const (W := ⊤) trivial)
  obtain ⟨σ, ⟨⟨s₀, hs₀I, rfl⟩, hσS⟩, -⟩ := hS I c' hc'
  obtain ⟨a, haI, ha⟩ := hsub ⟨0, ⟨le_rfl, le_rfl⟩, rfl⟩
  have ha' : c' a = p := ha
  have hσp : C.le ⊤ (c' s₀) p := by
    rcases le_total a s₀ with h | h
    · have := hc'.1.le_of_le haI hs₀I h
      rw [ha'] at this
      exact absurd ⟨c' s₀, hσS, this⟩ hp
    · have := hc'.1.le_of_le hs₀I haI h
      rwa [ha'] at this
  have hne : c' s₀ ≠ p := fun e => hp ⟨c' s₀, hσS, e ▸ C.le_refl trivial⟩
  obtain ⟨u, hu, hmono, hint, h0⟩ := hSP.2 _ hσp hne
  have hσu : C.le ⊤ (c' s₀) (u 0) :=
    Causal.Precausality.mem_Jminus_singleton.1 (Causal.interiorWithin_subset h0)
  obtain ⟨n, hn⟩ := (hu.eventually (isOpen_compl_singleton.mem_nhds hne.symm)).exists
  refine ⟨u n, ?_, mem_interior_iff_mem_nhds.1 (hint n)⟩
  rintro ⟨σ'', hσ''S, hrσ''⟩
  have hσr : C.le ⊤ (c' s₀) (u n) := C.le_trans hσu (hmono 0 n (Nat.zero_le n))
  have he := hac _ hσS σ'' hσ''S (C.le_trans hσr hrσ'')
  subst he
  exact hn (hcaus hrσ'' hσr)

variable {sing : ℝ → Set M}

/-- **`J⁺(Σ)` is closed** for a Cauchy surface `Σ` of a globally hyperbolic `𝔼≥0`-manifold. -/
theorem sfa_isClosed_Jplus_cauchy (h : C.SingularFlatAxioms sing) (hG : C.GloballyHyperbolic)
    (hext : C.CurvesExtend) (hS : C.IsCauchySurface S) : IsClosed (C.Jplus ⊤ S) := by
  haveI := h.t2
  have hac := hS.isAcausal h.causallyArcConnected hext
  exact Causal.Causality.isClosed_Jplus_of_forall_exists_lt fun p hp =>
    exists_lt_notMem_Jplus h.causallyArcConnected hext (h.mem_Zplus p)
      (hG.isClosed_Jplus_singleton h.tarentin) hS hac hp

/-- **`J⁻(Σ)` is closed** for a Cauchy surface `Σ` of a globally hyperbolic `𝔼≥0`-manifold (BTZ
points through `SingularPastAt`). -/
theorem sfa_isClosed_Jminus_cauchy (h : C.SingularFlatAxioms sing) (hG : C.GloballyHyperbolic)
    (hext : C.CurvesExtend) (hS : C.IsCauchySurface S) : IsClosed (C.Jminus ⊤ S) := by
  haveI := h.t2
  have hac := hS.isAcausal h.causallyArcConnected hext
  refine Causal.Causality.isClosed_Jminus_of_forall_exists fun p hp => ?_
  by_cases hps : p ∈ sing 0
  · exact exists_nhds_notMem_Jminus_of_singularPastAt hG.1 hext (h.singularPastAt p hps) hS hac hp
  · obtain ⟨r, hr, hrp⟩ := exists_lt_notMem_Jminus h.causallyArcConnected hext
      ((h.mem_Zminus_iff p).2 hps) (hG.isClosed_Jminus_singleton h.tarentin) hS hac hp
    exact ⟨r, hr, mem_of_superset (C.isOpen_Iplus.mem_nhds
      (Causal.Precausality.mem_Iplus_singleton.2 hrp)) Causal.Causality.Iplus_subset_Jplus⟩

end CauchyClosed

section Reductions

variable {M : Type*} [TopologicalSpace M] {C : Causal.Causality M} {sing : ℝ → Set M}

/-- **The time function** (`LocalModel.timeFunction`, design §6): `theo:geroch_sing` (i)⇒(ii),
the strict `SingularFlatAxioms.geroch_sing_i_imp_ii` (DEC-78), on the Borel σ-algebra. -/
theorem sfa_timeFunction (h : C.SingularFlatAxioms sing)
    (hM : @Causal.Causality.ModelMeasures M _ (borel M) C) (hG : C.GloballyHyperbolic) :
    ∃ T : M → ℝ, Continuous T ∧ ∀ x y, C.le ⊤ x y → x ≠ y → T x < T y := by
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  obtain ⟨T, hT, hTs⟩ := h.geroch_sing_i_imp_ii hM hG
  exact ⟨T, hT.1.continuous, hTs⟩

/-- **R1, future form**: `J⁺(Σ) ∩ J⁻(p)` compact, from `Flat/CBGCompact`'s model-free template
(`J⁻(p) ∩ Σ` compact without limit curves) and `Flat/CBG`'s reduction. -/
theorem sfa_isCompact_Jplus_inter_Jminus (h : C.SingularFlatAxioms sing)
    (hG : C.GloballyHyperbolic) {T : M → ℝ} (hTc : Continuous T)
    (hT : ∀ x y, C.le ⊤ x y → x ≠ y → T x < T y) {S : Set M} (hS : C.IsCauchySurface S) (p : M) :
    IsCompact (C.Jplus ⊤ S ∩ C.Jminus ⊤ {p}) := by
  haveI := h.t2
  haveI := h.locallyCompact
  have hext := Causal.Causality.curvesExtend_of_timeFunction hTc hT
  have hac := hS.isAcausal h.causallyArcConnected hext
  have hSp := sfa_isClosed_Jplus_cauchy h hG hext hS
  have hSm := sfa_isClosed_Jminus_cauchy h hG hext hS
  exact Causal.CBG.isCompact_Jplus_inter_Jminus_of_isCompact h.tarentin hG hSp
    (Causal.Causality.GloballyHyperbolic.isCompact_Jminus_inter_of_isCauchySurface h.tarentin hG
      h.causallyArcConnected hTc hT (fun W hW => sfa_isOpen_Jminus h hW) hS hac hSp hSm p)

/-- **R1, past form** (no duality). -/
theorem sfa_isCompact_Jminus_inter_Jplus (h : C.SingularFlatAxioms sing)
    (hG : C.GloballyHyperbolic) {T : M → ℝ} (hTc : Continuous T)
    (hT : ∀ x y, C.le ⊤ x y → x ≠ y → T x < T y) {S : Set M} (hS : C.IsCauchySurface S) (p : M) :
    IsCompact (C.Jminus ⊤ S ∩ C.Jplus ⊤ {p}) := by
  haveI := h.t2
  haveI := h.locallyCompact
  have hext := Causal.Causality.curvesExtend_of_timeFunction hTc hT
  have hac := hS.isAcausal h.causallyArcConnected hext
  have hSp := sfa_isClosed_Jplus_cauchy h hG hext hS
  have hSm := sfa_isClosed_Jminus_cauchy h hG hext hS
  exact Causal.CBG.isCompact_Jminus_inter_Jplus_of_isCompact h.tarentin hG hSm
    (Causal.Causality.GloballyHyperbolic.isCompact_Jplus_inter_of_isCauchySurface h.tarentin hG
      h.causallyArcConnected hTc hT (fun W hW => sfa_isOpen_Jplus h hW) hS hac hSp hSm p)

end Reductions


/-! ### §5b Local admissible measures on `𝔼₀`-manifolds (`ModelMeasures`, DEC-78) -/

section Measures

open MeasureTheory




section ChartNullGeneric

variable {M : Type*} [TopologicalSpace M] {C : Causal.Causality M} {d : ℕ}

/-- **`≪` of `𝐌ⁿ` on a convex open set inside the target of a chart isomorphism pulls back to
`≪_⊤`** (`Causal.Flat.flatCausality_lt_top_symm_of_convex`, for any chart isomorphism). -/
theorem lt_top_symm_of_convex_of_chartIso {φ : OpenPartialHomeomorph M (Causal.Minkowski d)}
    (hφ : Causal.ChartIso C (Causal.minkowski d) φ) {B : Set (Causal.Minkowski d)}
    (hBo : IsOpen B) (hBc : Convex ℝ B) (hBt : B ⊆ φ.target) {z y : Causal.Minkowski d}
    (hz : z ∈ B) (hy : y ∈ B) (h : (Causal.minkowski d).lt ⊤ z y) :
    C.lt ⊤ (φ.symm z) (φ.symm y) := by
  let Bo : Opens (Causal.Minkowski d) := ⟨B, hBo⟩
  have hlt : (Causal.minkowski d).lt Bo z y :=
    (Causal.Flat.lt_iff_of_convex (V := Bo) hBc).2 ⟨hz, hy, h⟩
  let U : Opens M := ⟨φ.source ∩ φ ⁻¹' B, φ.continuousOn.isOpen_inter_preimage φ.open_source hBo⟩
  have hUs : U ≤ Causal.chartSource φ := fun _ hw => hw.1
  have hUB : Causal.chartImage φ U = Bo := by
    refine SetLike.ext' ?_
    rw [Causal.coe_chartImage]
    ext p
    constructor
    · rintro ⟨w, ⟨_, _, hw⟩, rfl⟩; exact hw
    · intro hp
      have hpt := hBt hp
      refine ⟨φ.symm p, ⟨φ.map_target hpt, φ.map_target hpt, ?_⟩, φ.right_inv hpt⟩
      show φ (φ.symm p) ∈ B
      rw [φ.right_inv hpt]; exact hp
  have hmem : ∀ q ∈ B, φ.symm q ∈ U := fun q hq => by
    refine ⟨φ.map_target (hBt hq), ?_⟩
    show φ (φ.symm q) ∈ B
    rw [φ.right_inv (hBt hq)]; exact hq
  have key := (hφ U hUs _ (hmem z hz) _ (hmem y hy)).2
  rw [hUB, φ.right_inv (hBt hz), φ.right_inv (hBt hy)] at key
  exact C.lt_mono le_top (key.2 hlt)

/-- **In a chart isomorphism onto `𝐌ⁿ`, the frontier of `I⁻(A)` is Lebesgue-null**
(`Causal.Flat.volume_chart_frontier_Iminus_null`, for any chart isomorphism). -/
theorem volume_chart_frontier_Iminus_null_of_chartIso
    {φ : OpenPartialHomeomorph M (Causal.Minkowski d)}
    (hφ : Causal.ChartIso C (Causal.minkowski d) φ) (A : Set M) :
    volume (φ '' (frontier (C.Iminus ⊤ A) ∩ φ.source)) = 0 := by
  refine measure_mono_null
    (Causal.Flat.image_frontier_inter_source_subset_frontier φ C.isOpen_Iminus) ?_
  refine Causal.Flat.volume_frontier_inter_null_of_balls φ.open_target fun c r hB =>
    Causal.Flat.volume_frontier_inter_null_of_pastCone Metric.isOpen_ball ?_
  rintro _ ⟨w, ⟨hwI, hws⟩, rfl⟩ hy z hz hzy
  have hlt := lt_top_symm_of_convex_of_chartIso hφ Metric.isOpen_ball (convex_ball c r) hB hz hy
    (Causal.minkowski_lt_top_iff.2 hzy)
  rw [φ.left_inv hws] at hlt
  obtain ⟨a, ha, hwa⟩ := hwI
  exact ⟨φ.symm z, ⟨⟨a, ha, C.lt_trans hlt hwa⟩, φ.map_target (hB hz)⟩, φ.right_inv (hB hz)⟩

/-- **In a chart isomorphism onto `𝐌ⁿ`, the frontier of `I⁺(A)` is Lebesgue-null.** -/
theorem volume_chart_frontier_Iplus_null_of_chartIso
    {φ : OpenPartialHomeomorph M (Causal.Minkowski d)}
    (hφ : Causal.ChartIso C (Causal.minkowski d) φ) (A : Set M) :
    volume (φ '' (frontier (C.Iplus ⊤ A) ∩ φ.source)) = 0 := by
  refine measure_mono_null
    (Causal.Flat.image_frontier_inter_source_subset_frontier φ C.isOpen_Iplus) ?_
  refine Causal.Flat.volume_frontier_inter_null_of_balls φ.open_target fun c r hB =>
    Causal.Flat.volume_frontier_inter_null_of_futureCone Metric.isOpen_ball ?_
  rintro _ ⟨w, ⟨hwI, hws⟩, rfl⟩ hy z hz hyz
  have hlt := lt_top_symm_of_convex_of_chartIso hφ Metric.isOpen_ball (convex_ball c r) hB hy hz
    (Causal.minkowski_lt_top_iff.2 hyz)
  rw [φ.left_inv hws] at hlt
  obtain ⟨a, ha, haw⟩ := hwI
  exact ⟨φ.symm z, ⟨⟨a, ha, C.lt_trans haw hlt⟩, φ.map_target (hB hz)⟩, φ.right_inv (hB hz)⟩

end ChartNullGeneric

section ChartMeasureGeneric

variable {M : Type*} [TopologicalSpace M] {d : ℕ}

/-- **A chart measure on an open set `R` covered by charts onto `𝐌ⁿ`**
(`Causal.Flat.exists_chart_measure`, for a family of charts with a property `P` covering `R`):
finite, carried by `R`, positive on every open set meeting `R`, and null on every closed set whose
image in every chart with `P` is Lebesgue-null. -/
theorem exists_chart_measure_on [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
    {R : Set M} (hR : IsOpen R) (P : OpenPartialHomeomorph M (Causal.Minkowski d) → Prop)
    (hφ : ∀ x ∈ R, ∃ φ : OpenPartialHomeomorph M (Causal.Minkowski d), x ∈ φ.source ∧ P φ) :
    ∃ μ : Measure M, IsFiniteMeasure μ ∧ μ Rᶜ = 0 ∧
      (∀ O : Set M, IsOpen O → (O ∩ R).Nonempty → 0 < μ O) ∧
      ∀ S : Set M, IsClosed S →
        (∀ φ : OpenPartialHomeomorph M (Causal.Minkowski d), P φ →
          volume (φ '' (S ∩ φ.source)) = 0) → μ S = 0 := by
  classical
  choose e hxe hPe using hφ
  have hball : ∀ y : R, ∃ r : ℝ, 0 < r ∧
      Metric.ball (e y y.2 y) r ⊆ (e y y.2).target := fun y =>
    Metric.isOpen_iff.1 (e y y.2).open_target _ ((e y y.2).map_source (hxe y y.2))
  choose r hr hrV using hball
  set f : R → OpenPartialHomeomorph M (Causal.Minkowski d) := fun y => e y y.2 with hf_def
  set V : R → Set (Causal.Minkowski d) := fun y => Metric.ball (f y y) (r y) with hV_def
  set W : R → Set M := fun y => (f y).source ∩ (f y) ⁻¹' V y ∩ R with hW_def
  have hVopen : ∀ y, IsOpen (V y) := fun y => Metric.isOpen_ball
  have hVmeas : ∀ y, MeasurableSet (V y) := fun y => (hVopen y).measurableSet
  have hVt : ∀ y, V y ⊆ (f y).target := hrV
  have hVfin : ∀ y, volume (V y) ≠ ⊤ := fun y => measure_ball_lt_top.ne
  have hVpos : ∀ y, volume (V y) ≠ 0 := fun y => (Metric.measure_ball_pos volume _ (hr y)).ne'
  have hWopen : ∀ y, IsOpen (W y) := fun y =>
    ((f y).continuousOn.isOpen_inter_preimage (f y).open_source (hVopen y)).inter hR
  have hyW : ∀ y : R, (y : M) ∈ W y := fun y =>
    ⟨⟨hxe y y.2, Metric.mem_ball_self (hr y)⟩, y.2⟩
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable W hWopen
  haveI : Encodable T := hTc.toEncodable
  have hcover : ∀ p ∈ R, ∃ t : T, p ∈ W t := by
    intro p hp
    have hp' : p ∈ ⋃ i ∈ T, W i := by rw [hTU]; exact mem_iUnion.2 ⟨⟨p, hp⟩, hyW ⟨p, hp⟩⟩
    obtain ⟨i, hi, hpi⟩ := mem_iUnion₂.1 hp'
    exact ⟨⟨i, hi⟩, hpi⟩
  have hae : ∀ y, AEMeasurable (f y).symm (volume.restrict (V y)) := fun y =>
    (((f y).continuousOn_symm.mono (hVt y)).aemeasurable (hVmeas y))
  let c : T → ENNReal := fun t => (2⁻¹ : ENNReal) ^ Encodable.encode t * (volume (V t))⁻¹
  let μ₀ : Measure M := Measure.sum fun t : T => c t • (volume.restrict (V t)).map (f t).symm
  have hμ : ∀ s : Set M, MeasurableSet s →
      μ₀ s = ∑' t : T, c t * volume ((f t).symm ⁻¹' s ∩ V t) := by
    intro s hs
    simp only [μ₀, Measure.sum_apply _ hs, Measure.smul_apply, smul_eq_mul]
    congr 1; ext t
    rw [Measure.map_apply_of_aemeasurable (hae t) hs, Measure.restrict_apply' (hVmeas t)]
  have hfin : μ₀ univ < ⊤ := by
    rw [hμ univ MeasurableSet.univ]
    have : ∀ t : T, c t * volume ((f t).symm ⁻¹' univ ∩ V t) =
        (2⁻¹ : ENNReal) ^ Encodable.encode t := by
      intro t
      simp only [preimage_univ, univ_inter, c]
      rw [mul_assoc, ENNReal.inv_mul_cancel (hVpos t) (hVfin t), mul_one]
    simp_rw [this]
    exact ENNReal.tsum_geometric_two_encode_le_two.trans_lt ENNReal.ofNat_lt_top
  haveI : IsFiniteMeasure μ₀ := ⟨hfin⟩
  refine ⟨μ₀.restrict R, inferInstance, ?_, ?_, ?_⟩
  · rw [Measure.restrict_apply' hR.measurableSet, compl_inter_self, measure_empty]
  · intro O hO ⟨p, hpO, hpR⟩
    rw [Measure.restrict_apply' hR.measurableSet, hμ _ (hO.inter hR).measurableSet]
    obtain ⟨t, hpt⟩ := hcover p hpR
    refine lt_of_lt_of_le ?_ (ENNReal.le_tsum t)
    refine ENNReal.mul_pos ?_ ?_
    · exact (ENNReal.mul_pos (ENNReal.pow_pos (ENNReal.inv_pos.2 ENNReal.ofNat_ne_top) _).ne'
        (ENNReal.inv_ne_zero.2 (hVfin t))).ne'
    · have hU : IsOpen ((f t).target ∩ (f t).symm ⁻¹' (O ∩ R) ∩ V t) :=
        ((f t).continuousOn_symm.isOpen_inter_preimage (f t).open_target (hO.inter hR)).inter
          (hVopen t)
      have hpU : (f t) p ∈ (f t).target ∩ (f t).symm ⁻¹' (O ∩ R) ∩ V t :=
        ⟨⟨(f t).map_source hpt.1.1, by
          simpa [(f t).left_inv hpt.1.1] using (⟨hpO, hpR⟩ : p ∈ O ∩ R)⟩, hpt.1.2⟩
      have hpos : 0 < (volume : Measure (Causal.Minkowski d))
          ((f t).target ∩ (f t).symm ⁻¹' (O ∩ R) ∩ V t) :=
        IsOpen.measure_pos _ hU ⟨_, hpU⟩
      refine (lt_of_lt_of_le hpos (measure_mono ?_)).ne'
      intro z hz
      exact ⟨hz.1.2, hz.2⟩
  · intro S hS hnull
    refine le_antisymm ((Measure.restrict_le_self S).trans ?_) zero_le
    rw [hμ S hS.measurableSet]
    refine le_of_eq ?_
    refine ENNReal.tsum_eq_zero.2 fun t => ?_
    refine mul_eq_zero_of_right _ (measure_mono_null ?_ (hnull (f t) (hPe _ _)))
    intro z ⟨hzS, hzV⟩
    exact ⟨(f t).symm z, ⟨hzS, (f t).map_target (hVt t hzV)⟩, (f t).right_inv (hVt t hzV)⟩

end ChartMeasureGeneric

section AdmissibleAbstract

variable {M : Type*} [TopologicalSpace M] {C : Causal.Causality M}

open Causal.Precausality in
/-- `I⁻(a) ⊆ K⁻(a)` at every point, when `a ∈ Z⁻` or `I⁻(a) = ∅`. -/
theorem Iminus_subset_Kminus_of [FirstCountableTopology M] (hPU : C.PushUp) {S : Set M}
    (hZ : ∀ p ∉ S, p ∈ C.Zminus) (hIm : ∀ p ∈ S, C.Iminus ⊤ {p} = ∅) (a : M) :
    C.Iminus ⊤ {a} ⊆ C.Kminus ⊤ {a} := by
  by_cases ha : a ∈ S
  · rw [hIm a ha]; exact empty_subset _
  · rw [hPU.Kminus_eq_Iminus (hZ a ha)]

open Causal.Precausality in
/-- **A measure admissible in the future** (`defi:mesure_dieckmann`) from a finite regular measure
positive on non-empty open sets and null on every `frontier I⁺(A)`, on a globally hyperbolic,
tarentin spacetime with push-up and `Z⁺ = M` (`Causal.Flat.Geroch.Reach`'s argument). -/
theorem admissibleFuture_of_measure [T2Space M] [FirstCountableTopology M] [MeasurableSpace M]
    (hG : C.GloballyHyperbolic) (hT : C.Tarentin) (hPU : C.PushUp) (hZ : ∀ p, p ∈ C.Zplus)
    {μ : Measure M} [IsFiniteMeasure μ] (hreg : μ.Regular)
    (hpos : ∀ O : Set M, IsOpen O → O.Nonempty → 0 < μ O)
    (hnull : ∀ A : Set M, μ (frontier (C.Iplus ⊤ A)) = 0) : C.AdmissibleFuture μ := by
  refine ⟨hreg, measure_lt_top μ univ, fun p q hpq hne => ?_, fun A => ?_⟩
  · have hp : p ∉ C.Jplus ⊤ {q} := fun h => hne (hG.1 hpq (mem_Jplus_singleton.1 h))
    have hJ := Causal.Causality.GloballyHyperbolic.isClosed_Jplus_singleton hT hG q
    obtain ⟨z, hz1, hz2⟩ := hZ p _ (hJ.isOpen_compl.mem_nhds hp)
    refine lt_of_lt_of_le (hpos _ (C.isOpen_Iplus.inter hJ.isOpen_compl) ⟨z, hz1, hz2⟩)
      (measure_mono fun w hw => ⟨Causal.Causality.Iplus_subset_Jplus hw.1, hw.2⟩)
  · refine measure_mono_null ?_ (hnull A)
    rintro x ⟨⟨a, ha, hax⟩, hxK⟩
    refine ⟨mem_closure_iff_nhds.2 fun N hN => ?_, ?_⟩
    · obtain ⟨z, hz, hzN⟩ := hZ x N hN
      exact ⟨z, hzN, a, ha, hPU.lt_of_le_of_lt hax (mem_Iplus_singleton.1 hz)⟩
    · rw [C.isOpen_Iplus.interior_eq]
      rintro ⟨a', ha', hlt⟩
      refine hxK (Causal.Causality.Kplus_mono (singleton_subset_iff.2 ha') ?_)
      rw [hPU.Kplus_eq_Iplus (hZ a')]
      exact mem_Iplus_singleton.2 hlt

open Causal.Precausality in
/-- **A measure admissible in the past** (`defi:mesure_dieckmann`) on a globally hyperbolic,
tarentin spacetime with push-up whose non-`Z⁻` points `S` (the BTZ points) have no chronological
past, a `SingularPastAt` past and `Iplus_of_lt`, and are covered by countably many causally
totally ordered pieces: `μ + ν`, `μ` positive on open sets and null on `frontier I⁻(A)` and on
points (Lebesgue in charts, `λ₃`), `ν` carried by `S`, atomless and positive on the half-lines
`J⁻(q) ∖ F` (`λ₁` on the line). Property 4: `J⁻(A) ∖ K⁻(A)` lies in `frontier I⁻(A) ∖ S` plus a
set meeting each totally ordered piece in at most one point. -/
theorem admissiblePast_of_measures [T2Space M] [FirstCountableTopology M] [MeasurableSpace M]
    [MeasurableSingletonClass M]
    (hG : C.GloballyHyperbolic) (hT : C.Tarentin) (hPU : C.PushUp) {S : Set M}
    (hZ : ∀ p ∉ S, p ∈ C.Zminus) (hIm : ∀ p ∈ S, C.Iminus ⊤ {p} = ∅)
    (hSP : ∀ p ∈ S, C.SingularPastAt p)
    (hIpl : ∀ p ∈ S, ∀ p' ∈ S, C.le ⊤ p p' → p ≠ p' → C.Jplus ⊤ {p'} \ S ⊆ C.Iplus ⊤ {p})
    {L : Set (Set M)} (hLc : L.Countable) (hLS : S ⊆ ⋃₀ L)
    (hLt : ∀ l ∈ L, ∀ x ∈ l, ∀ y ∈ l, C.le ⊤ x y ∨ C.le ⊤ y x)
    {μ ν : Measure M} [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hreg : (μ + ν).Regular)
    (hpos : ∀ O : Set M, IsOpen O → O.Nonempty → 0 < μ O)
    (hnull : ∀ A : Set M, μ (frontier (C.Iminus ⊤ A)) = 0) (hμpt : ∀ x, μ {x} = 0)
    (hνS : ν Sᶜ = 0) (hνpt : ∀ x, ν {x} = 0)
    (hνpos : ∀ q ∈ S, ∀ F : Set M, IsClosed F → q ∉ F → 0 < ν (C.Jminus ⊤ {q} \ F)) :
    C.AdmissiblePast (μ + ν) := by
  have hIK := Iminus_subset_Kminus_of hPU hZ hIm
  refine ⟨hreg, measure_lt_top _ univ, fun p q hpq hne => ?_, fun A => ?_⟩
  · have hq : q ∉ C.Jminus ⊤ {p} := fun h => hne (hG.1 hpq (mem_Jminus_singleton.1 h))
    have hJ := Causal.Causality.GloballyHyperbolic.isClosed_Jminus_singleton hT hG p
    rw [Measure.add_apply]
    by_cases hqS : q ∈ S
    · exact lt_of_lt_of_le (hνpos q hqS _ hJ hq) le_add_self
    · obtain ⟨z, hz1, hz2⟩ := hZ q hqS _ (hJ.isOpen_compl.mem_nhds hq)
      refine lt_of_lt_of_le ?_ le_self_add
      exact lt_of_lt_of_le (hpos _ (C.isOpen_Iminus.inter hJ.isOpen_compl) ⟨z, hz1, hz2⟩)
        (measure_mono fun w hw => ⟨Causal.Causality.Iminus_subset_Jminus hw.1, hw.2⟩)
  · set X := C.Jminus ⊤ A \ C.Kminus ⊤ A with hX
    -- the regular part of `X` is in the frontier of `I⁻(A)`
    have hreg' : X \ S ⊆ frontier (C.Iminus ⊤ A) \ S := by
      rintro x ⟨⟨⟨a, ha, hxa⟩, hxK⟩, hxS⟩
      refine ⟨⟨mem_closure_iff_nhds.2 fun N hN => ?_, ?_⟩, hxS⟩
      · obtain ⟨z, hz, hzN⟩ := hZ x hxS N hN
        exact ⟨z, hzN, a, ha, hPU.lt_of_lt_of_le (mem_Iminus_singleton.1 hz) hxa⟩
      · rw [C.isOpen_Iminus.interior_eq]
        rintro ⟨a', ha', hlt⟩
        exact hxK (Causal.Causality.Kminus_mono (singleton_subset_iff.2 ha')
          (hIK a' (mem_Iminus_singleton.2 hlt)))
    -- two points of `X ∩ S` in causal order coincide
    have hkey : ∀ x ∈ X ∩ S, ∀ x' ∈ X ∩ S, C.le ⊤ x x' → x = x' := by
      rintro x ⟨⟨_, hxK⟩, hxS⟩ x' ⟨⟨⟨a, ha, hx'a⟩, -⟩, hx'S⟩ hxx'
      by_contra hne
      have hxa : C.le ⊤ x a := C.le_trans hxx' hx'a
      have hxa' : x ≠ a := by
        rintro rfl
        exact hne (hG.1 hxx' hx'a)
      refine hxK (Causal.Causality.Kminus_mono (singleton_subset_iff.2 ha) ?_)
      by_cases haS : a ∈ S
      · exact (hSP a haS).Jminus_diff_subset_Kminus ⟨mem_Jminus_singleton.2 hxa, hxa'⟩
      · exact hIK a (mem_Iminus_singleton.2 (mem_Iplus_singleton.1
          (hIpl x hxS x' hx'S hxx' hne ⟨mem_Jplus_singleton.2 hx'a, haS⟩)))
    have hcount : (X ∩ S).Countable := by
      have hsub : X ∩ S ⊆ ⋃ l ∈ L, (X ∩ S ∩ l) := by
        intro x hx
        obtain ⟨l, hl, hxl⟩ := hLS hx.2
        exact mem_iUnion₂.2 ⟨l, hl, hx, hxl⟩
      refine Countable.mono hsub (hLc.biUnion fun l hl => Subsingleton.countable ?_)
      intro x hx x' hx'
      rcases hLt l hl x hx.2 x' hx'.2 with h | h
      · exact hkey x hx.1 x' hx'.1 h
      · exact (hkey x' hx'.1 x hx.1 h).symm
    have hXsub : X ⊆ (frontier (C.Iminus ⊤ A) \ S) ∪ ⋃ x ∈ X ∩ S, {x} := by
      intro x hx
      by_cases hxS : x ∈ S
      · exact Or.inr (mem_iUnion₂.2 ⟨x, ⟨hx, hxS⟩, rfl⟩)
      · exact Or.inl (hreg' ⟨hx, hxS⟩)
    refine measure_mono_null hXsub (measure_union_null ?_ ((measure_biUnion_null_iff hcount).2
      fun x _ => ?_))
    · rw [Measure.add_apply]
      exact add_eq_zero.2 ⟨measure_mono_null sdiff_subset (hnull A),
        measure_mono_null (fun w hw => hw.2) hνS⟩
    · rw [Measure.add_apply, hμpt, hνpt, add_zero]

end AdmissibleAbstract

section RegularCharts

/-- The chart `𝕄 ⊂ Y → 𝕄` (inverse of `inl`). -/
noncomputable def inlChart : OpenPartialHomeomorph E0Y (Causal.Minkowski 2) :=
  (IsOpenEmbedding.inl.toOpenPartialHomeomorph (Sum.inl : Causal.Minkowski 2 → E0Y)).symm

/-- The chart `𝔼₀ ⊂ Y → ℝ × ℂ` (inverse of `emb`). -/
noncomputable def embChart : OpenPartialHomeomorph E0Y E0 :=
  (isOpenEmbedding_emb.toOpenPartialHomeomorph emb).symm

theorem inlChart_inl (m : Causal.Minkowski 2) : inlChart (Sum.inl m) = m :=
  IsOpenEmbedding.inl.toOpenPartialHomeomorph_left_inv _

theorem embChart_emb (q : E0) : embChart (emb q) = q :=
  isOpenEmbedding_emb.toOpenPartialHomeomorph_left_inv _

theorem inlChart_source : inlChart.source = range Sum.inl := by
  simp [inlChart]

theorem embChart_source : embChart.source = range emb := by
  simp [embChart]

/-- **`inlChart` is a chart isomorphism** onto Minkowski's `𝕄`. -/
theorem chartIso_inlChart : Causal.ChartIso D (Causal.minkowski 2) inlChart := by
  intro U hU a ha b hb
  have hsrc : ∀ z ∈ U, ∃ m, z = Sum.inl m := fun z hz => by
    have h : z ∈ range Sum.inl := inlChart_source ▸ (hU hz : z ∈ inlChart.source)
    obtain ⟨m, hm⟩ := h
    exact ⟨m, hm.symm⟩
  obtain ⟨a', rfl⟩ := hsrc a ha
  obtain ⟨b', rfl⟩ := hsrc b hb
  have hO : Causal.chartImage inlChart U = E0.leftOpens (E0.opensImage E0.toPaperY U) := by
    refine SetLike.ext' ?_
    rw [Causal.coe_chartImage]
    ext m
    constructor
    · rintro ⟨z, ⟨-, hzU⟩, rfl⟩
      obtain ⟨m', rfl⟩ := hsrc z hzU
      rw [inlChart_inl]
      exact ⟨Sum.inl m', hzU, rfl⟩
    · rintro ⟨z, hzU, hze⟩
      obtain ⟨m', rfl⟩ := hsrc z hzU
      have : m' = m := Sum.inl_injective hze
      subst this
      exact ⟨Sum.inl m', ⟨hU hzU, hzU⟩, inlChart_inl m'⟩
  rw [hO, inlChart_inl, inlChart_inl]
  exact ⟨Iff.rfl, Iff.rfl⟩

/-- **`embChart` is a chart isomorphism** onto `𝔼₀` in the paper's coordinates. -/
theorem chartIso_embChart : Causal.ChartIso D E0.causality embChart := by
  intro U hU a ha b hb
  have hsrc : ∀ z ∈ U, ∃ q, z = emb q := fun z hz => by
    have h : z ∈ range emb := embChart_source ▸ (hU hz : z ∈ embChart.source)
    obtain ⟨q, hq⟩ := h
    exact ⟨q, hq.symm⟩
  obtain ⟨a', rfl⟩ := hsrc a ha
  obtain ⟨b', rfl⟩ := hsrc b hb
  have hO : Causal.chartImage embChart U = vOf U := by
    refine SetLike.ext' ?_
    rw [Causal.coe_chartImage]
    ext q
    constructor
    · rintro ⟨z, ⟨-, hzU⟩, rfl⟩
      obtain ⟨q', rfl⟩ := hsrc z hzU
      rw [embChart_emb]
      exact ⟨emb q', hzU, by simp [emb, E0.toPaperY, Homeomorph.sumCongr]⟩
    · rintro ⟨z, hzU, hze⟩
      obtain ⟨q', rfl⟩ := hsrc z hzU
      have : q' = q := by
        have h2 : (Sum.inr (E0.toPaper (E0.toPaper.symm q')) : E0.ModelY) = Sum.inr q := hze
        simpa using h2
      subst this
      exact ⟨emb q', ⟨hU hzU, hzU⟩, embChart_emb q'⟩
  rw [hO, embChart_emb, embChart_emb]
  have h1 : ∀ q : E0, E0.toPaper (E0.toPaper.symm q) = q := fun q => by simp
  constructor
  · show E0.causality.le (vOf U) (E0.toPaper (E0.toPaper.symm a')) (E0.toPaper (E0.toPaper.symm b'))
      ↔ _
    rw [h1, h1]
  · show E0.causality.lt (vOf U) (E0.toPaper (E0.toPaper.symm a')) (E0.toPaper (E0.toPaper.symm b'))
      ↔ _
    rw [h1, h1]

/-- **Every regular point of `Y` is in the source of a chart isomorphism onto `𝐌³`**: `inlChart`
on `𝕄`, a sector chart (`E0.chartIso_sectorChart`) through `embChart` off the axis of `𝔼₀`. -/
theorem exists_minkChart_Y {y : E0Y} (hy : y ∉ e0SingY 0) :
    ∃ ψ : OpenPartialHomeomorph E0Y (Causal.Minkowski 2), y ∈ ψ.source ∧
      Causal.ChartIso D (Causal.minkowski 2) ψ := by
  rcases y with m | b
  · refine ⟨inlChart, ?_, chartIso_inlChart⟩
    rw [inlChart_source]; exact ⟨m, rfl⟩
  · have hax : (E0.toPaper b).2 ≠ 0 := fun h => hy (inr_mem_e0SingY_zero_iff.2 h)
    refine ⟨embChart.trans (E0.sectorChart _ hax), ⟨?_, ?_⟩,
      E0.chartIso_trans chartIso_embChart (E0.chartIso_sectorChart hax)⟩
    · show Sum.inr b ∈ embChart.source
      rw [embChart_source]; exact ⟨E0.toPaper b, emb_toPaper b⟩
    · show embChart (Sum.inr b) ∈ (E0.sectorChart (E0.toPaper b) hax).source
      rw [← emb_toPaper b, embChart_emb]
      exact e0_mem_sector_source hax

end RegularCharts

section LineMeasure

variable {M : Type*} [TopologicalSpace M] {C : Causal.Causality M}

/-- **A measure on the BTZ locus** (`λ₁` on the line, `ETT.tex:1736–1745`) from countably many
chart pieces `γ(]a, b[)` of the line, each causally increasing: carried by `S`, atomless, positive
on every half-line `J⁻(q) ∖ F` (`q ∈ S`, `F` closed, `q ∉ F`); the pieces cover `S`. -/
theorem exists_line_measure [SecondCountableTopology M] [T1Space M] [MeasurableSpace M]
    [BorelSpace M] {S : Set M} (hS : IsClosed S)
    (hpiece : ∀ x ∈ S, ∃ (O : Set M) (γ : ℝ → M) (a b : ℝ), IsOpen O ∧ x ∈ O ∧ a < b ∧
      ContinuousOn γ (Ioo a b) ∧ InjOn γ (Ioo a b) ∧ (∀ τ ∈ Ioo a b, γ τ ∈ S) ∧
      (∀ x' ∈ O, x' ∈ S → ∃ τ ∈ Ioo a b, γ τ = x') ∧
      ∀ τ ∈ Ioo a b, ∀ τ' ∈ Ioo a b, τ ≤ τ' → C.le ⊤ (γ τ) (γ τ')) :
    ∃ ν : Measure M, IsFiniteMeasure ν ∧ ν Sᶜ = 0 ∧ (∀ z, ν {z} = 0) ∧
      (∀ q ∈ S, ∀ F : Set M, IsClosed F → q ∉ F → 0 < ν (C.Jminus ⊤ {q} \ F)) ∧
      ∃ L : Set (Set M), L.Countable ∧ S ⊆ ⋃₀ L ∧
        ∀ l ∈ L, ∀ x ∈ l, ∀ y ∈ l, C.le ⊤ x y ∨ C.le ⊤ y x := by
  classical
  choose O γ a b hO hxO hab hγc hγi hγS hcov hmono using hpiece
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable (fun y : S => O y y.2)
    fun y => hO y y.2
  haveI : Encodable T := hTc.toEncodable
  -- the pieces through `T`
  set g : T → ℝ → M := fun t => γ t.1 t.1.2 with hg
  set I : T → Set ℝ := fun t => Ioo (a t.1 t.1.2) (b t.1 t.1.2) with hI
  have hImeas : ∀ t, MeasurableSet (I t) := fun t => measurableSet_Ioo
  have hIfin : ∀ t, volume (I t) ≠ ⊤ := fun t => by simp [hI]
  have hIpos : ∀ t, volume (I t) ≠ 0 := fun t => by
    simp only [hI, Real.volume_Ioo, ne_eq, ENNReal.ofReal_eq_zero, not_le, sub_pos]
    exact hab _ _
  have hae : ∀ t, AEMeasurable (g t) (volume.restrict (I t)) := fun t =>
    (hγc t.1 t.1.2).aemeasurable (hImeas t)
  -- every point of `S` lies on a piece through `T`
  have hcovS : ∀ q ∈ S, ∃ t : T, ∃ τ ∈ I t, g t τ = q := by
    intro q hq
    have hq' : q ∈ ⋃ i ∈ T, O i i.2 := by
      rw [hTU]; exact mem_iUnion.2 ⟨⟨q, hq⟩, hxO q hq⟩
    obtain ⟨i, hi, hqi⟩ := mem_iUnion₂.1 hq'
    obtain ⟨τ, hτ, he⟩ := hcov i i.2 q hqi hq
    exact ⟨⟨i, hi⟩, τ, hτ, he⟩
  let c : T → ENNReal := fun t => (2⁻¹ : ENNReal) ^ Encodable.encode t * (volume (I t))⁻¹
  have hcpos : ∀ t, c t ≠ 0 := fun t =>
    (ENNReal.mul_pos (ENNReal.pow_pos (ENNReal.inv_pos.2 ENNReal.ofNat_ne_top) _).ne'
      (ENNReal.inv_ne_zero.2 (hIfin t))).ne'
  let ν : Measure M := Measure.sum fun t : T => c t • (volume.restrict (I t)).map (g t)
  have hν : ∀ s : Set M, MeasurableSet s →
      ν s = ∑' t : T, c t * volume (g t ⁻¹' s ∩ I t) := by
    intro s hs
    simp only [ν, Measure.sum_apply _ hs, Measure.smul_apply, smul_eq_mul]
    congr 1; ext t
    rw [Measure.map_apply_of_aemeasurable (hae t) hs, Measure.restrict_apply' (hImeas t)]
  have hfin : ν univ < ⊤ := by
    rw [hν univ MeasurableSet.univ]
    have : ∀ t : T, c t * volume (g t ⁻¹' univ ∩ I t) = (2⁻¹ : ENNReal) ^ Encodable.encode t := by
      intro t
      simp only [preimage_univ, univ_inter, c]
      rw [mul_assoc, ENNReal.inv_mul_cancel (hIpos t) (hIfin t), mul_one]
    simp_rw [this]
    exact ENNReal.tsum_geometric_two_encode_le_two.trans_lt ENNReal.ofNat_lt_top
  refine ⟨ν, ⟨hfin⟩, ?_, ?_, ?_, ?_⟩
  · rw [hν _ hS.isOpen_compl.measurableSet]
    refine ENNReal.tsum_eq_zero.2 fun t => mul_eq_zero_of_right _ ?_
    have : g t ⁻¹' Sᶜ ∩ I t = ∅ := by
      ext τ
      simp only [mem_inter_iff, mem_preimage, mem_compl_iff, mem_empty_iff_false, iff_false,
        not_and]
      exact fun h hτ => h (hγS _ _ τ hτ)
    rw [this, measure_empty]
  · intro z
    rw [hν _ (measurableSet_singleton z)]
    refine ENNReal.tsum_eq_zero.2 fun t => mul_eq_zero_of_right _ ?_
    refine Subsingleton.measure_zero (fun τ hτ τ' hτ' => ?_) _
    exact hγi t.1 t.1.2 hτ.2 hτ'.2 (hτ.1.trans hτ'.1.symm)
  · intro q hq F hF hqF
    obtain ⟨t, τq, hτq, hgq⟩ := hcovS q hq
    have hcont : ContinuousAt (g t) τq :=
      (hγc t.1 t.1.2).continuousAt (Ioo_mem_nhds hτq.1 hτq.2)
    have hN : g t ⁻¹' Fᶜ ∩ I t ∈ 𝓝 τq :=
      inter_mem (hcont.preimage_mem_nhds (hF.isOpen_compl.mem_nhds (hgq ▸ hqF)))
        (Ioo_mem_nhds hτq.1 hτq.2)
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hN
    have hK : Ioo (τq - δ) τq ⊆ g t ⁻¹' (C.Jminus ⊤ {q} \ F) := by
      intro τ hτ
      have hτb : τ ∈ Metric.ball τq δ := by
        rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith [hτ.1, hτ.2]
      obtain ⟨hτF, hτI⟩ := hball hτb
      refine ⟨Causal.Precausality.mem_Jminus_singleton.2 ?_, hτF⟩
      rw [← hgq]
      exact hmono t.1 t.1.2 τ hτI τq hτq hτ.2.le
    have hKI : Ioo (τq - δ) τq ⊆ I t := fun τ hτ => by
      have hτb : τ ∈ Metric.ball τq δ := by
        rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith [hτ.1, hτ.2]
      exact (hball hτb).2
    calc (0 : ENNReal) < c t * ENNReal.ofReal δ :=
          ENNReal.mul_pos (hcpos t) (ENNReal.ofReal_pos.2 hδ).ne'
      _ = c t * volume (Ioo (τq - δ) τq ∩ I t) := by
          rw [inter_eq_left.2 hKI, Real.volume_Ioo]; congr 2; ring
      _ = c t * volume.restrict (I t) (Ioo (τq - δ) τq) := by
          rw [Measure.restrict_apply measurableSet_Ioo]
      _ ≤ c t * volume.restrict (I t) (g t ⁻¹' (C.Jminus ⊤ {q} \ F)) := by
          gcongr
      _ ≤ c t * (volume.restrict (I t)).map (g t) (C.Jminus ⊤ {q} \ F) := by
          gcongr; exact Measure.le_map_apply (hae t) _
      _ = (c t • (volume.restrict (I t)).map (g t)) (C.Jminus ⊤ {q} \ F) := by
          rw [Measure.smul_apply, smul_eq_mul]
      _ ≤ ν (C.Jminus ⊤ {q} \ F) := Measure.le_iff'.1 (Measure.le_sum _ t) _
  · refine ⟨range fun t : T => g t '' I t, countable_range _, fun q hq => ?_, ?_⟩
    · obtain ⟨t, τ, hτ, he⟩ := hcovS q hq
      exact ⟨_, ⟨t, rfl⟩, τ, hτ, he⟩
    · rintro _ ⟨t, rfl⟩ _ ⟨τ, hτ, rfl⟩ _ ⟨τ', hτ', rfl⟩
      rcases le_total τ τ' with h | h
      · exact Or.inl (hmono t.1 t.1.2 τ hτ τ' hτ' h)
      · exact Or.inr (hmono t.1 t.1.2 τ' hτ' τ hτ h)

end LineMeasure

/-- A point of `𝐌³` is Lebesgue-null. -/
theorem minkowski_volume_singleton (p : Causal.Minkowski 2) :
    volume ({p} : Set (Causal.Minkowski 2)) = 0 := by
  refine measure_mono_null (show {p} ⊆ ({p.1} : Set ℝ) ×ˢ
      (Set.univ : Set (EuclideanSpace ℝ (Fin 2))) from
    fun q hq => by rw [Set.mem_singleton_iff.1 hq]; exact ⟨rfl, trivial⟩) ?_
  rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, zero_mul]

section E0Measures

variable {M : Type} [TopologicalSpace M] [ChartedSpace E0Y M] [HasGroupoid M e0Groupoid]

/-- **Every regular point of an `𝔼₀`-manifold is in the source of a chart isomorphism onto
`𝐌³`**: the chart of `M` followed by `exists_minkChart_Y`. -/
theorem e0_exists_minkChart_M {x : M} (hx : x ∉ Causal.CBG.chartedSing e0SingY M 0) :
    ∃ φ : OpenPartialHomeomorph M (Causal.Minkowski 2), x ∈ φ.source ∧
      Causal.ChartIso (Causal.CBG.chartedCausality D M) (Causal.minkowski 2) φ := by
  have hxs := mem_chart_source E0Y x
  have hy : chartAt E0Y x x ∉ e0SingY 0 := fun h =>
    hx ((chartAt_mem_singY_iff e0_sing_mem hxs le_rfl).1 h)
  obtain ⟨ψ, hψ, hψi⟩ := exists_minkChart_Y hy
  exact ⟨(chartAt E0Y x).trans ψ, ⟨hxs, hψ⟩, E0.chartIso_trans
    (Causal.CBG.chartedCausality_chartIso (M := M) E0.chartIso_mem_e0Groupoid
      E0.absolutelyMinimalOn_YBTZ x) hψi⟩

/-- **The BTZ line of an `𝔼₀`-manifold, in a chart**: around every BTZ point, the axis of the
chart `τ ↦ (chartAt x)⁻¹ (emb (τ, 0))` on an interval, causally increasing, covering the BTZ
points of an open neighbourhood. -/
theorem e0_line_piece {x : M} (hx : x ∈ Causal.CBG.chartedSing e0SingY M 0) :
    ∃ (O : Set M) (γ : ℝ → M) (a b : ℝ), IsOpen O ∧ x ∈ O ∧ a < b ∧
      ContinuousOn γ (Ioo a b) ∧ InjOn γ (Ioo a b) ∧
      (∀ τ ∈ Ioo a b, γ τ ∈ Causal.CBG.chartedSing e0SingY M 0) ∧
      (∀ x' ∈ O, x' ∈ Causal.CBG.chartedSing e0SingY M 0 → ∃ τ ∈ Ioo a b, γ τ = x') ∧
      ∀ τ ∈ Ioo a b, ∀ τ' ∈ Ioo a b, τ ≤ τ' →
        (Causal.CBG.chartedCausality D M).le ⊤ (γ τ) (γ τ') := by
  set e := chartAt E0Y x with he
  have hxs : x ∈ e.source := mem_chart_source E0Y x
  have hex : e x ∈ e0SingY 0 := hx
  obtain ⟨b₀, hb₀, hax⟩ := mem_e0SingY_zero_iff.1 hex
  set p₀ := E0.toPaper b₀ with hp₀
  have hp₀2 : p₀.2 = 0 := hax
  have hembp₀ : emb p₀ = e x := by rw [hp₀, emb_toPaper, hb₀]
  have hN : emb ⁻¹' e.target ∈ 𝓝 p₀ :=
    isOpenEmbedding_emb.continuous.continuousAt.preimage_mem_nhds
      (e.open_target.mem_nhds (hembp₀ ▸ e.map_source hxs))
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hN
  -- the line `τ ↦ (τ, 0)` in the ball
  have hlB : ∀ τ ∈ Ioo (p₀.1 - δ) (p₀.1 + δ), ((τ, 0) : E0) ∈ Metric.ball p₀ δ := by
    intro τ hτ
    rw [Metric.mem_ball, Prod.dist_eq, hp₀2, dist_self, Real.dist_eq, max_lt_iff]
    exact ⟨abs_lt.2 ⟨by linarith [hτ.1], by linarith [hτ.2]⟩, hδ⟩
  have htgt : ∀ τ ∈ Ioo (p₀.1 - δ) (p₀.1 + δ), emb ((τ, 0) : E0) ∈ e.target :=
    fun τ hτ => hball (hlB τ hτ)
  have hsingQ : ∀ q : E0, q ∈ E0.axis → emb q ∈ e0SingY 0 := fun q hq =>
    inr_mem_e0SingY_zero_iff.2 (by simpa using hq)
  have hc := Causal.CBG.chartedCausality_chartIso (M := M) E0.chartIso_mem_e0Groupoid
    E0.absolutelyMinimalOn_YBTZ x
  refine ⟨e.source ∩ e ⁻¹' (emb '' Metric.ball p₀ δ), fun τ => e.symm (emb ((τ, 0) : E0)),
    p₀.1 - δ, p₀.1 + δ,
    e.isOpen_inter_preimage (isOpenEmbedding_emb.isOpenMap _ Metric.isOpen_ball),
    ⟨hxs, p₀, Metric.mem_ball_self hδ, hembp₀⟩, by linarith, ?_, ?_, ?_, ?_, ?_⟩
  · refine e.continuousOn_symm.comp (isOpenEmbedding_emb.continuous.comp
      (continuous_id.prodMk continuous_const)).continuousOn htgt
  · intro τ hτ τ' hτ' h
    have h1 := congrArg e h
    simp only at h1
    rw [e.right_inv (htgt τ hτ), e.right_inv (htgt τ' hτ')] at h1
    exact congrArg Prod.fst (isOpenEmbedding_emb.injective h1)
  · intro τ hτ
    have hs : e.symm (emb ((τ, 0) : E0)) ∈ e.source := e.map_target (htgt τ hτ)
    refine (chartAt_mem_singY_iff e0_sing_mem hs le_rfl).1 ?_
    rw [← he, e.right_inv (htgt τ hτ)]
    exact hsingQ _ rfl
  · rintro x' ⟨hx's, q, hqB, hqe⟩ hx'S
    have hq : emb q ∈ e0SingY 0 := by
      rw [hqe]; exact (chartAt_mem_singY_iff e0_sing_mem hx's le_rfl).2 hx'S
    obtain ⟨b', hb', hax'⟩ := mem_e0SingY_zero_iff.1 hq
    have hq2 : q.2 = 0 := by
      have : E0.toPaper (E0.toPaper.symm q) = E0.toPaper b' := by
        rw [Sum.inr_injective hb']
      rw [Homeomorph.apply_symm_apply] at this
      rw [this]; exact hax'
    have hqd : dist q p₀ < δ := hqB
    rw [Prod.dist_eq, max_lt_iff, Real.dist_eq] at hqd
    refine ⟨q.1, ⟨by linarith [(abs_lt.1 hqd.1).1], by linarith [(abs_lt.1 hqd.1).2]⟩, ?_⟩
    have : ((q.1, 0) : E0) = q := Prod.ext rfl hq2.symm
    simp only [this, hqe, e.left_inv hx's]
  · intro τ hτ τ' hτ' hle
    have hs : e.symm (emb ((τ, 0) : E0)) ∈ e.source := e.map_target (htgt τ hτ)
    have hs' : e.symm (emb ((τ', 0) : E0)) ∈ e.source := e.map_target (htgt τ' hτ')
    refine (Causal.CBG.chartedCausality D M).le_mono le_top
      ((hc (Causal.chartSource e) le_rfl _ hs _ hs').1.2 ?_)
    rw [e.right_inv (htgt τ hτ), e.right_inv (htgt τ' hτ')]
    have hB : (⟨Metric.ball p₀ δ, Metric.isOpen_ball⟩ : Opens E0) ≤
        vOf (Causal.chartImage e (Causal.chartSource e)) := by
      intro w hw
      have hwt : emb w ∈ e.target := hball hw
      have hmem : (Sum.inr (E0.toPaper.symm w) : E0Y) ∈
          Causal.chartImage e (Causal.chartSource e) := by
        show emb w ∈ (Causal.chartImage e (Causal.chartSource e) : Set E0Y)
        rw [Causal.coe_chartImage]
        exact ⟨e.symm (emb w), ⟨e.map_target hwt, e.map_target hwt⟩, e.right_inv hwt⟩
      simpa using mem_vOf hmem
    have h := E0.causality.le_mono hB (e0_le_ball_of_axis rfl rfl hle (hlB τ hτ) (hlB τ' hτ'))
    show E0.causality.le (vOf (Causal.chartImage e (Causal.chartSource e)))
      (E0.toPaper (E0.toPaper.symm ((τ, 0) : E0))) (E0.toPaper (E0.toPaper.symm ((τ', 0) : E0)))
    simpa using h

/-- **Local admissible measures on every globally hyperbolic `𝔼₀`-manifold** (`ModelMeasures`,
the input of the strict `geroch_sing_i_imp_ii`, DEC-78; `ETT.tex:1736–1745`). One global pair,
admissible on the causally convex open set `M` itself: in the future, `μ`, Lebesgue measure read
in countably many regular chart isomorphisms onto `𝐌³` (`exists_chart_measure_on`), whose
frontiers of chronological futures are null (`volume_chart_frontier_Iplus_null_of_chartIso`); in
the past, `μ + ν` with `ν` Lebesgue measure on the BTZ line read in countably many axis charts
(`exists_line_measure`, `e0_line_piece`) — the paper's `λ₃ + λ₁`. -/
theorem e0_modelMeasures_of [T2Space M] [SecondCountableTopology M]
    (hGH : (Causal.CBG.chartedCausality D M).GloballyHyperbolic) :
    @Causal.Causality.ModelMeasures M _ (borel M) (Causal.CBG.chartedCausality D M) := by
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  haveI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace E0Y M
  haveI : MetrizableSpace M := TopologicalSpace.metrizableSpace_of_t3_secondCountable M
  set C := Causal.CBG.chartedCausality D M with hC
  set S := Causal.CBG.chartedSing e0SingY M 0 with hSdef
  have hGD := E0.chartIso_mem_e0Groupoid
  have hA := E0.absolutelyMinimalOn_YBTZ
  have hScl : IsClosed S := charted_isClosed_sing (M := M) e0_sing_mem le_rfl (isClosed_e0SingY 0)
  have hSint : interior S = ∅ :=
    charted_interior_sing (M := M) e0_sing_mem le_rfl (interior_e0SingY 0)
  have hT : C.Tarentin := charted_tarentin (M := M) hGD hA yb_locTarentin
  have hPU : C.PushUp :=
    charted_pushUp (M := M) hGD hA E0.causalityYBTZ_causallyArcConnected yb_pushUp
  -- `μ`: Lebesgue measure in the regular chart isomorphisms
  obtain ⟨μ, hμf, hμR, hμpos, hμnull⟩ := exists_chart_measure_on (d := 2) hScl.isOpen_compl
    (fun φ => Causal.ChartIso C (Causal.minkowski 2) φ) fun x hx => e0_exists_minkChart_M hx
  haveI := hμf
  have hpos : ∀ O : Set M, IsOpen O → O.Nonempty → 0 < μ O := by
    intro O hO hne
    refine hμpos O hO ?_
    by_contra h
    rw [not_nonempty_iff_eq_empty, ← disjoint_iff_inter_eq_empty, disjoint_compl_right_iff_subset]
      at h
    obtain ⟨z, hz⟩ := hne
    have := interior_maximal h hO hz
    rw [hSint] at this
    exact this
  have hpt : ∀ x : M, μ {x} = 0 := fun x => hμnull _ isClosed_singleton fun φ _ =>
    measure_mono_null (Set.image_mono inter_subset_left)
      (by rw [image_singleton]; exact minkowski_volume_singleton _)
  refine ⟨fun _ => ⟨⊤, trivial, ⟨fun _ _ => trivial, fun _ _ _ _ _ _ => trivial⟩, ?_⟩,
    fun _ => ⟨⊤, trivial, ⟨fun _ _ => trivial, fun _ _ _ _ _ _ => trivial⟩, μ,
      Causal.Causality.admissibleFutureOn_top.2 ?_⟩⟩
  · -- the past: `μ + ν`
    obtain ⟨ν, hνf, hνS, hνpt, hνpos, L, hLc, hLS, hLt⟩ :=
      exists_line_measure (C := C) hScl fun x hx => e0_line_piece hx
    haveI := hνf
    refine ⟨μ + ν, Causal.Causality.admissiblePastOn_top.2 ?_⟩
    exact admissiblePast_of_measures hGH hT hPU
      (fun p hp => charted_mem_Zminus (M := M) hGD hA yb_locZminus hp)
      (fun p hp => charted_Iminus_eq_empty (M := M) hGD hA e0_sing_mem yb_locNoPast hp)
      (charted_singularPastAt (M := M) hGD hA e0_sing_mem
        E0.causalityYBTZ_causallyArcConnected (isClosed_e0SingY 0) yb_locPastIn yb_exists_below
        yb_future_nhds yb_past_nhds)
      (charted_Iplus_of_lt (M := M) hGD hA e0_sing_mem
        E0.causalityYBTZ_causallyArcConnected yb_pushUp (isClosed_e0SingY 0) yb_locPastIn
        yb_local_Iplus_of_lt)
      hLc hLS hLt inferInstance hpos
      (fun A => hμnull _ isClosed_frontier fun φ hφ =>
        volume_chart_frontier_Iminus_null_of_chartIso hφ A)
      hpt hνS hνpt hνpos
  · exact admissibleFuture_of_measure hGH hT hPU
      (charted_mem_Zplus (M := M) hGD hA yb_locZplus) inferInstance hpos
      fun A => hμnull _ isClosed_frontier fun φ hφ =>
        volume_chart_frontier_Iplus_null_of_chartIso hφ A

end E0Measures

end Measures

/-! ### §5c Time functions without measures (Levin), and second countability of `Reg M`

`timeFunction` and `curvesExtend` from the strict `Causal.LevinUtility` (Levin's theorem: a
continuous utility for the closed causal order of a second-countable tarentin globally hyperbolic
`M`); tarentinity is `charted_tarentin`, so neither field depends on the BTZ line (O2). Then
`Reg M` is a connected flat `(Isom 𝐌³, 𝐌³)`-manifold (`e0RegM_chartedSpace`, `e0RegM_hasGroupoid`,
`isPreconnected_e0RegM`), hence second countable by Geroch's flat theorem with no second
countability asked of `M` (`e0RegM_secondCountable`), and `secondCountable_of_cauchy` is reduced
to the BTZ-line step `E0LineStep` (`e0_secondCountable_of_lineStep`). -/

section Levin

variable {M : Type} [TopologicalSpace M] [ChartedSpace E0Y M] [HasGroupoid M e0Groupoid]

theorem e0_tarentin : (Causal.CBG.chartedCausality D M).Tarentin :=
  charted_tarentin (M := M) E0.chartIso_mem_e0Groupoid E0.absolutelyMinimalOn_YBTZ yb_locTarentin

theorem e0_timeFunction [T2Space M] [SecondCountableTopology M]
    (hGH : (Causal.CBG.chartedCausality D M).GloballyHyperbolic) :
    ∃ T : M → ℝ, Continuous T ∧
      ∀ x y, (Causal.CBG.chartedCausality D M).le ⊤ x y → x ≠ y → T x < T y := by
  obtain ⟨T, hT, -, hTs⟩ :=
    Causal.Causality.exists_timeFunction_of_secondCountable (e0_tarentin (M := M)) hGH
  exact ⟨T, hT, hTs⟩

theorem e0_curvesExtend [T2Space M] [SecondCountableTopology M]
    (hGH : (Causal.CBG.chartedCausality D M).GloballyHyperbolic) :
    (Causal.CBG.chartedCausality D M).CurvesExtend :=
  Causal.Causality.curvesExtend_of_secondCountable (e0_tarentin (M := M)) hGH

end Levin

section RegM

variable {M : Type} [TopologicalSpace M] [ChartedSpace E0Y M] [HasGroupoid M e0Groupoid]

variable (M) in
/-- The regular part `Reg M = M ∖ sing₀(M)` of an `𝔼₀`-manifold, as an open set. -/
def e0RegM : Opens M :=
  ⟨(Causal.CBG.chartedSing e0SingY M 0)ᶜ,
    (charted_isClosed_sing (M := M) e0_sing_mem le_rfl (isClosed_e0SingY 0)).isOpen_compl⟩

theorem mem_e0RegM_iff {x y : M} (hy : y ∈ (chartAt E0Y x).source) :
    y ∈ e0RegM M ↔ chartAt E0Y x y ∈ e0Reg := by
  show y ∉ Causal.CBG.chartedSing e0SingY M 0 ↔ _
  rw [← chartAt_mem_singY_iff e0_sing_mem hy le_rfl]
  simp [e0SingY]

theorem dense_e0RegM : Dense (e0RegM M : Set M) := by
  show Dense (Causal.CBG.chartedSing e0SingY M 0)ᶜ
  rw [← interior_eq_empty_iff_dense_compl]
  exact charted_interior_sing (M := M) e0_sing_mem le_rfl (interior_e0SingY 0)

/-- Every point of an `𝔼₀`-manifold has an open neighbourhood whose regular part is
preconnected (the model fact `isPreconnected_inter_e0Reg`, read in the chart). -/
theorem exists_isPreconnected_inter_e0RegM (x : M) :
    ∃ V : Set M, IsOpen V ∧ x ∈ V ∧ IsPreconnected (V ∩ e0RegM M) := by
  set e := chartAt E0Y x
  set W := connectedComponentIn e.target (e x)
  have hW : IsOpen W := e.open_target.connectedComponentIn
  have hWt : W ⊆ e.target := connectedComponentIn_subset _ _
  refine ⟨e.source ∩ e ⁻¹' W, e.isOpen_inter_preimage hW,
    ⟨mem_chart_source E0Y x, mem_connectedComponentIn (e.map_source (mem_chart_source E0Y x))⟩, ?_⟩
  have heq : e.source ∩ e ⁻¹' W ∩ e0RegM M = e.symm '' (W ∩ e0Reg) := by
    ext z
    constructor
    · rintro ⟨⟨hz, hzW⟩, hzR⟩
      exact ⟨e z, ⟨hzW, (mem_e0RegM_iff hz).1 hzR⟩, e.left_inv hz⟩
    · rintro ⟨w, ⟨hwW, hwR⟩, rfl⟩
      have hwt := hWt hwW
      have hzs : e.symm w ∈ e.source := e.map_target hwt
      refine ⟨⟨hzs, ?_⟩, (mem_e0RegM_iff hzs).2 ?_⟩
      · show e (e.symm w) ∈ W; rw [e.right_inv hwt]; exact hwW
      · rw [e.right_inv hwt]; exact hwR
  rw [heq]
  exact (isPreconnected_inter_e0Reg hW isPreconnected_connectedComponentIn).image _
    (e.continuousOn_symm.mono fun w hw => hWt hw.1)

/-- **`Reg M` is preconnected** when `M` is: the singular part of an `𝔼₀`-manifold does not
disconnect it. -/
theorem isPreconnected_e0RegM [PreconnectedSpace M] : IsPreconnected (e0RegM M : Set M) := by
  set R : Set M := (e0RegM M : Set M)
  have hRo : IsOpen R := (e0RegM M).isOpen
  have hRd : Dense R := dense_e0RegM
  rw [isPreconnected_iff_subset_of_disjoint]
  intro u v hu hv hRuv hRuv0
  by_contra hcon
  simp only [not_or, not_subset] at hcon
  obtain ⟨⟨a, haR, hau⟩, ⟨b, hbR, hbv⟩⟩ := hcon
  have hav : a ∈ v := (hRuv haR).resolve_left hau
  have hbu : b ∈ u := (hRuv hbR).resolve_right hbv
  set A : Set M := {x | ∃ V : Set M, IsOpen V ∧ x ∈ V ∧ V ∩ R ⊆ u}
  set B : Set M := {x | ∃ V : Set M, IsOpen V ∧ x ∈ V ∧ V ∩ R ⊆ v}
  have hAo : IsOpen A := isOpen_iff_forall_mem_open.2 fun x ⟨V, hV, hxV, hVu⟩ =>
    ⟨V, fun y hy => ⟨V, hV, hy, hVu⟩, hV, hxV⟩
  have hBo : IsOpen B := isOpen_iff_forall_mem_open.2 fun x ⟨V, hV, hxV, hVv⟩ =>
    ⟨V, fun y hy => ⟨V, hV, hy, hVv⟩, hV, hxV⟩
  have hcov : (univ : Set M) ⊆ A ∪ B := by
    intro x _
    obtain ⟨V, hV, hxV, hVc⟩ := exists_isPreconnected_inter_e0RegM x
    have hsub : V ∩ R ⊆ (u ∩ R) ∪ (v ∩ R) := fun z hz =>
      (hRuv hz.2).imp (fun h => ⟨h, hz.2⟩) (fun h => ⟨h, hz.2⟩)
    have hdis : Disjoint (u ∩ R) (v ∩ R) := by
      rw [Set.disjoint_left]
      rintro z ⟨hzu, hzR⟩ ⟨hzv, -⟩
      have : z ∈ R ∩ (u ∩ v) := ⟨hzR, hzu, hzv⟩
      rw [hRuv0] at this
      exact this
    rcases hVc.subset_or_subset (hu.inter hRo) (hv.inter hRo) hdis hsub with h | h
    · exact Or.inl ⟨V, hV, hxV, fun z hz => (h hz).1⟩
    · exact Or.inr ⟨V, hV, hxV, fun z hz => (h hz).1⟩
  have hA : (univ ∩ A).Nonempty := ⟨b, trivial, u ∩ R, hu.inter hRo, ⟨hbu, hbR⟩, fun z hz => hz.1.1⟩
  have hB : (univ ∩ B).Nonempty := ⟨a, trivial, v ∩ R, hv.inter hRo, ⟨hav, haR⟩, fun z hz => hz.1.1⟩
  obtain ⟨x, -, ⟨V, hV, hxV, hVu⟩, ⟨V', hV', hxV', hVv⟩⟩ :=
    (PreconnectedSpace.isPreconnected_univ (α := M)) A B hAo hBo hcov hA hB
  obtain ⟨z, ⟨hzV, hzV'⟩, hzR⟩ := hRd.inter_open_nonempty (V ∩ V') (hV.inter hV') ⟨x, hxV, hxV'⟩
  have : z ∈ R ∩ (u ∩ v) := ⟨hzR, hVu ⟨hzV, hzR⟩, hVv ⟨hzV', hzR⟩⟩
  rw [hRuv0] at this
  exact this

end RegM

section RegCharts

/-- `Causal.gxGroupoid (Isom 𝐌³) 𝐌³` is closed under restriction (used locally, through `haveI`). -/
theorem flatGroupoid_closedUnderRestriction :
    ClosedUnderRestriction (Causal.gxGroupoid (Causal.Flat.isom 2) (Causal.Minkowski 2)) := by
  rw [closedUnderRestriction_iff_id_le, StructureGroupoid.le_iff]
  rintro e ⟨s, hs, hes⟩
  exact StructureGroupoid.mem_of_eqOnSource _
    (Causal.mem_gxGroupoid_of_eq_id (fun z _ => rfl) (fun z _ => rfl)) hes

/-- The charts of `e0Atlas` land in the regular part. -/
theorem source_subset_e0Reg {c : OpenPartialHomeomorph E0Y (Causal.Minkowski 2)} (hc : c ∈ e0Atlas) :
    c.source ⊆ e0Reg := fun _ hx => mem_support.2 ⟨c, hc, hx⟩

/-- **An element of `G` read in two regular charts is locally a translation by `Isom(𝐌³)`**. -/
theorem e0_flat_transition_aux {t : OpenPartialHomeomorph E0Y E0Y} (ht : t ∈ e0Groupoid)
    {c c' : OpenPartialHomeomorph E0Y (Causal.Minkowski 2)} (hc : c ∈ e0Atlas) (hc' : c' ∈ e0Atlas) :
    ∀ z ∈ (c.symm.trans (t.trans c')).source, ∃ g : Causal.Flat.isom 2,
      (c.symm.trans (t.trans c')) =ᶠ[𝓝 z] fun y => g • y := by
  rintro z ⟨hz, hzt, hzc'⟩
  have hz' : z ∈ c.target := hz
  have hw : c.symm z ∈ c.source := c.map_target hz'
  obtain ⟨-, hch⟩ := ((mem_e0Groupoid_iff.1 ht).1 (c.symm z) hzt).2 (source_subset_e0Reg hc hw)
  obtain ⟨g, hg⟩ := hch c hc c' hc' hw hzc'
  refine ⟨g, ?_⟩
  have h1 := (c.continuousAt_symm hz').eventually hg
  filter_upwards [h1, c.open_target.mem_nhds hz'] with y hy hyt
  simp only [OpenPartialHomeomorph.coe_trans, comp_apply]
  rw [hy, c.right_inv hyt]

/-- **An element of `G` read in two regular charts is in the flat groupoid.** -/
theorem e0_flat_transition_mem {t : OpenPartialHomeomorph E0Y E0Y} (ht : t ∈ e0Groupoid)
    {c c' : OpenPartialHomeomorph E0Y (Causal.Minkowski 2)} (hc : c ∈ e0Atlas) (hc' : c' ∈ e0Atlas) :
    c.symm.trans (t.trans c') ∈ Causal.gxGroupoid (Causal.Flat.isom 2) (Causal.Minkowski 2) := by
  have hsymm : (c.symm.trans (t.trans c')).symm = c'.symm.trans (t.symm.trans c) := by
    simp only [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.symm_symm, OpenPartialHomeomorph.trans_assoc]
  refine mem_groupoid_of_pregroupoid.2 ⟨e0_flat_transition_aux ht hc hc', ?_⟩
  intro z hz
  rw [← OpenPartialHomeomorph.symm_source, hsymm] at hz
  obtain ⟨g, hg⟩ := e0_flat_transition_aux (e0Groupoid.symm ht) hc' hc z hz
  exact ⟨g, by rw [hsymm]; exact hg⟩

variable {M : Type} [TopologicalSpace M] [ChartedSpace E0Y M] [HasGroupoid M e0Groupoid]

theorem e0RegM_chart_reg (y : e0RegM M) : chartAt E0Y (y : M) y ∈ support e0Atlas :=
  (mem_e0RegM_iff (mem_chart_source E0Y (y : M))).1 y.2

/-- A regular chart of `Y` at the chart image of a regular point of `M`. -/
noncomputable def regAtlasChart (y : e0RegM M) : OpenPartialHomeomorph E0Y (Causal.Minkowski 2) :=
  Classical.choose (mem_support.1 (e0RegM_chart_reg y))

theorem regAtlasChart_mem (y : e0RegM M) : regAtlasChart y ∈ e0Atlas :=
  (Classical.choose_spec (mem_support.1 (e0RegM_chart_reg y))).1

theorem mem_regAtlasChart_source (y : e0RegM M) :
    chartAt E0Y (y : M) y ∈ (regAtlasChart y).source :=
  (Classical.choose_spec (mem_support.1 (e0RegM_chart_reg y))).2

/-- **The flat chart of `M` at a regular point**: the chart of `M` followed by a regular chart of
`Y`, onto an open subset of `𝐌³`. -/
noncomputable def regChartM (y : e0RegM M) : OpenPartialHomeomorph M (Causal.Minkowski 2) :=
  (chartAt E0Y (y : M)).trans (regAtlasChart y)

/-- **`Reg M` is a `(Isom 𝐌³, 𝐌³)`-manifold**: its charted structure. -/
noncomputable instance e0RegM_chartedSpace : ChartedSpace (Causal.Minkowski 2) (e0RegM M) where
  atlas := range fun y : e0RegM M => (regChartM y).subtypeRestr ⟨y⟩
  chartAt y := (regChartM y).subtypeRestr ⟨y⟩
  mem_chart_source y := by
    rw [OpenPartialHomeomorph.subtypeRestr_source]
    exact ⟨mem_chart_source E0Y (y : M), mem_regAtlasChart_source y⟩
  chart_mem_atlas y := ⟨y, rfl⟩

/-- **The transitions of `Reg M` are in `Isom(𝐌³)`**. -/
instance e0RegM_hasGroupoid :
    HasGroupoid (e0RegM M) (Causal.gxGroupoid (Causal.Flat.isom 2) (Causal.Minkowski 2)) where
  compatible := by
    haveI := flatGroupoid_closedUnderRestriction
    rintro _ _ ⟨y, rfl⟩ ⟨y', rfl⟩
    refine StructureGroupoid.mem_of_eqOnSource _ (closedUnderRestriction' ?_
      ((regChartM y).isOpen_inter_preimage_symm (e0RegM M).isOpen))
      (OpenPartialHomeomorph.subtypeRestr_symm_trans_subtypeRestr _ (regChartM y) (regChartM y'))
    have ht : (chartAt E0Y (y : M)).symm.trans (chartAt E0Y (y' : M)) ∈ e0Groupoid :=
      HasGroupoid.compatible (chart_mem_atlas E0Y _) (chart_mem_atlas E0Y _)
    have := e0_flat_transition_mem ht (regAtlasChart_mem y) (regAtlasChart_mem y')
    have heq : (regChartM y).symm.trans (regChartM y') = (regAtlasChart y).symm.trans
        (((chartAt E0Y (y : M)).symm.trans (chartAt E0Y (y' : M))).trans (regAtlasChart y')) := by
      simp only [regChartM, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
        OpenPartialHomeomorph.trans_assoc]
    rw [heq]; exact this

/-- **`Reg M` is second countable** for every Hausdorff connected `𝔼₀`-manifold `M`, with no
second countability asked of `M`: `Reg M` is connected (`isPreconnected_e0RegM`) and a flat
`(Isom 𝐌³, 𝐌³)`-manifold (`e0RegM_hasGroupoid`), so Geroch's flat theorem
`Causal.Flat.flat_secondCountableTopology` (DEC-49; developing map of the universal cover,
`GX.developing_theorem`) applies. -/
theorem e0RegM_secondCountable [T2Space M] [ConnectedSpace M] :
    SecondCountableTopology (e0RegM M) := by
  obtain ⟨x₀⟩ := (inferInstance : Nonempty M)
  obtain ⟨z, -, hz⟩ := (dense_e0RegM (M := M)).inter_open_nonempty univ isOpen_univ ⟨x₀, trivial⟩
  haveI : PreconnectedSpace (e0RegM M) :=
    Subtype.preconnectedSpace isPreconnected_e0RegM
  haveI : ConnectedSpace (e0RegM M) := { toNonempty := ⟨⟨z, hz⟩⟩ }
  exact Causal.Flat.flat_secondCountableTopology (d := 2) (e0RegM M)

end RegCharts

section SCOfCauchy

variable {M : Type} [TopologicalSpace M] [ChartedSpace E0Y M] [HasGroupoid M e0Groupoid]

/-- Around each BTZ point of `M`, an open set whose BTZ points all lie in the component of
`sing₀(M)` of that point (`e0_line_piece`). -/
theorem e0_sing_nhds_component {x : M} (hx : x ∈ Causal.CBG.chartedSing e0SingY M 0) :
    ∃ O : Set M, IsOpen O ∧ x ∈ O ∧ O ∩ Causal.CBG.chartedSing e0SingY M 0 ⊆
      connectedComponentIn (Causal.CBG.chartedSing e0SingY M 0) x := by
  obtain ⟨O, γ, a, b, hO, hxO, -, hγc, -, hγs, hγO, -⟩ := e0_line_piece hx
  refine ⟨O, hO, hxO, ?_⟩
  obtain ⟨τ₀, hτ₀, hγτ₀⟩ := hγO x hxO hx
  have hsub : γ '' Ioo a b ⊆ connectedComponentIn (Causal.CBG.chartedSing e0SingY M 0) x :=
    (isPreconnected_Ioo.image _ hγc).subset_connectedComponentIn
      (hγτ₀ ▸ mem_image_of_mem γ hτ₀) (image_subset_iff.2 fun τ hτ => hγs τ hτ)
  rintro x' ⟨hx'O, hx's⟩
  obtain ⟨τ, hτ, rfl⟩ := hγO x' hx'O hx's
  exact hsub (mem_image_of_mem γ hτ)

omit [HasGroupoid M e0Groupoid] in
/-- The chart domains of an `𝔼₀`-manifold are second countable (`Y = 𝕄 ⊕ 𝔼₀` is). -/
theorem e0_chart_source_secondCountable (x : M) :
    SecondCountableTopology (chartAt E0Y x).source := by
  haveI : SecondCountableTopology BTZE0 :=
    (quotientBase_topology (Z := ℝ) btz_two_pi_ne_zero).2.2 inferInstance
  exact (chartAt E0Y x).toHomeomorphSourceTarget.secondCountableTopology

/-- **The BTZ-line step, with no second countability asked of `M`**: each component of the BTZ
locus `S₀` is the image of one inextensible causal curve `ℝ → M`. (`E0GlobalBTZ`'s `line`,
without the closed-embedding clause, stated for a possibly non-second-countable `M`.) -/
def E0LineStep {M : Type*} [TopologicalSpace M] (C : Causal.Causality M) (S₀ : Set M) : Prop :=
  ∀ p ∈ S₀, ∃ γ : ℝ → M, C.Inextensible ⊤ univ γ ∧ range γ = connectedComponentIn S₀ p

/-- **`secondCountable_of_cauchy` from the BTZ-line step** (O4 reduced): a Hausdorff connected
`𝔼₀`-manifold with a second-countable Cauchy surface `Σ` is second countable once its BTZ lines
are inextensible causal curves. `Reg M` is second countable (`e0RegM_secondCountable`); each BTZ
line meets `Σ`; the components of `sing₀` meeting `Σ` are countably many, because `Σ ∩ sing₀` is
Lindelöf and each BTZ point has a neighbourhood whose BTZ points lie in its own component
(`e0_sing_nhds_component`); each line, the image of `ℝ`, is Lindelöf. So `M` is Lindelöf, hence
covered by countably many (second-countable) chart domains. -/
theorem e0_secondCountable_of_lineStep [T2Space M] [ConnectedSpace M]
    (hL : E0LineStep (Causal.CBG.chartedCausality D M) (Causal.CBG.chartedSing e0SingY M 0))
    (S : Set M) (hS : (Causal.CBG.chartedCausality D M).IsCauchySurface S)
    (hSS : SecondCountableTopology S) : SecondCountableTopology M := by
  set S₀ := Causal.CBG.chartedSing e0SingY M 0 with hS₀def
  have hS₀ : IsClosed S₀ := charted_isClosed_sing (M := M) e0_sing_mem le_rfl (isClosed_e0SingY 0)
  haveI := e0RegM_secondCountable (M := M)
  have hR : IsLindelof (S₀ᶜ) := isLindelof_iff_lindelofSpace.2 (inferInstance :
    LindelofSpace (e0RegM M))
  have hSL : IsLindelof (S ∩ S₀) := (isLindelof_iff_lindelofSpace.2 inferInstance).inter_right hS₀
  choose! O hO hxO hOc using fun x (hx : x ∈ S₀) => e0_sing_nhds_component hx
  obtain ⟨T, hTsub, hTc, hTcov⟩ := hSL.elim_countable_subcover_image (b := S ∩ S₀) (c := O)
    (fun q hq => hO q hq.2) fun q hq => mem_biUnion hq (hxO q hq.2)
  choose! γ hγi hγr using hL
  have hsing : S₀ ⊆ ⋃ q ∈ T, range (γ q) := by
    intro p hp
    obtain ⟨s, ⟨⟨t, -, rfl⟩, hsS⟩, -⟩ := hS univ (γ p) (hγi p hp)
    have hsp : γ p t ∈ connectedComponentIn S₀ p := hγr p hp ▸ mem_range_self t
    have hs₀ : γ p t ∈ S₀ := connectedComponentIn_subset _ _ hsp
    obtain ⟨q, hqT, hsq⟩ := mem_iUnion₂.1 (hTcov ⟨hsS, hs₀⟩)
    have hq := hTsub hqT
    have hsq' : γ p t ∈ connectedComponentIn S₀ q := hOc q hq.2 ⟨hsq, hs₀⟩
    refine mem_iUnion₂.2 ⟨q, hqT, ?_⟩
    rw [hγr q hq.2, connectedComponentIn_eq hsq', ← connectedComponentIn_eq hsp]
    exact mem_connectedComponentIn hp
  have hlin : IsLindelof (univ : Set M) := by
    have h1 : IsLindelof (⋃ q ∈ T, range (γ q)) := hTc.isLindelof_biUnion fun q hq =>
      isLindelof_range (hγi q (hTsub hq).2).1.continuous
    refine (hR.union h1).of_isClosed_subset isClosed_univ fun x _ => ?_
    by_cases hx : x ∈ S₀
    · exact Or.inr (hsing hx)
    · exact Or.inl hx
  obtain ⟨r, -, hrc, hrcov⟩ := hlin.elim_countable_subcover_image (b := univ)
    (c := fun x : M => (chartAt E0Y x).source) (fun x _ => (chartAt E0Y x).open_source)
    fun x _ => mem_biUnion (mem_univ x) (mem_chart_source E0Y x)
  haveI : Countable r := hrc.to_subtype
  haveI : ∀ x : r, SecondCountableTopology (chartAt E0Y (x : M)).source :=
    fun x => e0_chart_source_secondCountable _
  refine secondCountableTopology_of_countable_cover (U := fun x : r => (chartAt E0Y (x : M)).source)
    (fun x => (chartAt E0Y (x : M)).open_source) ?_
  refine eq_univ_of_univ_subset fun x hx => ?_
  obtain ⟨y, hyr, hxy⟩ := mem_iUnion₂.1 (hrcov hx)
  exact mem_iUnion.2 ⟨⟨y, hyr⟩, hxy⟩

end SCOfCauchy

/-! ### §6b `localUnique_sing_adherent` (Rigid's (b1)) -/

/-- **`localUnique_sing_adherent` for `𝔐E₀`** (B21 `prop:isom_strong`'s past-side form, interface
round 3): Rigid's reduction `e0_localUniqueSingAdherent_of_region` discharged for the model
causality. At a BTZ tip `y₀ ≪_O r`, `I⁻_O(r)` is an open neighbourhood of `y₀`; in a ball `B(p₀, δ)`
inside it and inside `O`, `I⁺_B(p₀) = B ∩ {r > 0, f > τ₀}` (`E0.Iplus_ball_axis`), which contains the
circle-swept box `{r < δ/4, τ₀ + δ/4 < τ < τ₀ + δ/2}`. -/
theorem e0_localUniqueSingAdherent : E0LocalUniqueSingAdherent D := by
  refine e0_localUniqueSingAdherent_of_region D fun y₀ hy₀ O hyO r _ _ hlt => ?_
  rw [e0SingY_zero] at hy₀
  obtain ⟨x₀, rfl⟩ : ∃ x₀, y₀ = Sum.inr x₀ := by
    rcases y₀ with m | x
    · obtain ⟨a, -, ha⟩ := hy₀; exact absurd ha Sum.inr_ne_inl
    · exact ⟨x, rfl⟩
  have hax : E0.toPaper x₀ ∈ E0.axis := by
    obtain ⟨a, ha, he⟩ := hy₀
    have : a = E0.toPaper x₀ := Sum.inr_injective he
    rw [← this]; exact ha
  set p₀ := E0.toPaper x₀ with hp₀
  set V : Opens E0 := E0.rightOpens (E0.opensImage E0.toPaperY O) with hVdef
  have hp₀V : p₀ ∈ V := ⟨Sum.inr x₀, hyO, rfl⟩
  have hN : D.Iminus O {r} ∈ 𝓝 (Sum.inr x₀ : E0Y) :=
    D.isOpen_Iminus.mem_nhds (Causal.Precausality.mem_Iminus_singleton.2 hlt)
  have hN' : (fun q => (Sum.inr (E0.toPaper.symm q) : E0Y)) ⁻¹' D.Iminus O {r} ∈ 𝓝 p₀ := by
    apply (continuous_inr.comp E0.toPaper.symm.continuous).continuousAt.preimage_mem_nhds
    simpa [hp₀] using hN
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 (inter_mem hN' (V.isOpen.mem_nhds hp₀V))
  refine ⟨e0Box (Real.log (δ / 4)) (2 * p₀.1 + 3 * δ / 4) (δ / 4), isOpen_e0Box _ _ _,
    convex_e0Box _ _ _, ⟨((Real.log (δ / 4) - 1 : ℝ), 2 * p₀.1 + 3 * δ / 4), ?_, ?_⟩,
    fun w hw s => mem_e0Box_add hw s, fun w hw => ?_⟩
  · show ((Real.log (δ / 4) - 1 : ℝ) : ℂ).re < Real.log (δ / 4)
    rw [Complex.ofReal_re]; linarith
  · show dist (2 * p₀.1 + 3 * δ / 4) (2 * p₀.1 + 3 * δ / 4) < δ / 4
    rw [dist_self]; linarith
  obtain ⟨hw1, hw2⟩ := hw
  set q := E0.toPaper (orbitMk (GammaA (2 * π)) (e0BoxSec w)) with hq
  have hq1 : q.1 = w.2 / 2 := by rw [hq, toPaper_orbitMk_fst, e0BoxSec_t]
  have hqr : E0.rad q = Real.exp w.1.re := by rw [hq, rad_toPaper_orbitMk, e0BoxSec_r]
  have hr4 : Real.exp w.1.re < δ / 4 := by
    calc Real.exp w.1.re < Real.exp (Real.log (δ / 4)) := Real.exp_lt_exp.2 hw1
      _ = δ / 4 := Real.exp_log (by positivity)
  have hrpos : 0 < E0.rad q := hqr ▸ Real.exp_pos _
  have hp₀2 : p₀.2 = 0 := hax
  have hw2' := abs_lt.1 (show |w.2 - (2 * p₀.1 + 3 * δ / 4)| < δ / 4 from hw2)
  have hqball : q ∈ Metric.ball p₀ δ := by
    rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
    refine ⟨?_, ?_⟩
    · rw [Real.dist_eq, hq1, abs_lt]; constructor <;> linarith
    · rw [hp₀2, dist_zero_right]
      have : ‖q.2‖ = E0.rad q := rfl
      rw [this, hqr]; linarith
  have hqf : p₀.1 < E0.fcoord q := by
    rw [E0.fcoord, hq1, hqr]; linarith
  have hsub := hball hqball
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [e0RegSet_eq, inr_mem_e0Reg_iff, mem_reg_btzE0_iff]
    intro h0
    have : E0.rad q = 0 := by
      show ‖q.2‖ = 0
      rw [hq, h0, norm_zero]
    linarith
  · rw [Causal.Precausality.mem_Iplus_singleton]
    have hI : q ∈ E0.causality.Iplus ⟨Metric.ball p₀ δ, Metric.isOpen_ball⟩ {p₀} := by
      rw [E0.Iplus_ball_axis hax]; exact ⟨hqball, hrpos, hqf⟩
    have hlt' := E0.causality.lt_mono (show (⟨Metric.ball p₀ δ, Metric.isOpen_ball⟩ : Opens E0) ≤ V
      from fun z hz => (hball hz).2) (Causal.Precausality.mem_Iplus_singleton.1 hI)
    exact hlt'
  · have := hsub.1
    simp only [mem_preimage, hq, Homeomorph.symm_apply_apply] at this
    exact this


/-! ### §6c `typeAgreement`: false for `𝔐E₀`; its convergence form (WP-41c's discharge, ported) -/

section TypeAgreement

theorem ta_toPaper_btzDevInv {v : ℝ × ℝ × ℝ} (hv : 0 < v.2.1) :
    E0.toPaper (orbitMk (GammaA (2 * π)) (btzDevInv v)) = E0.unlift v := by
  have h := E0.toPaper_posEmb hv (-(v.2.2 / v.2.1)) ((v.1 + v.2.1 - v.2.2 ^ 2 / v.2.1) / 2)
  have e1 : btzDevInv v = (DInfty.posEmb ⟨(v.2.1, -(-(v.2.2 / v.2.1))), hv⟩,
      2 * ((v.1 + v.2.1 - v.2.2 ^ 2 / v.2.1) / 2)) := by
    rw [btzDevInv, dif_pos hv, neg_neg]
    congr 1; ring
  rw [e1, h]
  simp only [E0.unlift]
  refine Prod.ext ?_ rfl
  ring

theorem ta_segLt_inl : E0TASegLt E0.causalityYBTZ e0TAInl univ := by
  intro O V hVo hVc _ hVO v hv w hw h
  show (Causal.minkowski 2).lt (E0.leftOpens (E0.opensImage E0.toPaperY O))
    (nullToMink v) (nullToMink w)
  set V' : Opens (Causal.Minkowski 2) := ⟨nullToMink '' V, by
    rw [← coe_nullToMinkHomeomorph]; exact nullToMinkHomeomorph.isOpenMap V hVo⟩
  have hV'c : Convex ℝ (V' : Set (Causal.Minkowski 2)) :=
    hVc.linear_image nullToMink.toLinearMap
  have hle : V' ≤ E0.leftOpens (E0.opensImage E0.toPaperY O) := by
    rintro _ ⟨u, hu, rfl⟩
    exact ⟨Sum.inl (nullToMink u), hVO u hu, rfl⟩
  exact (Causal.minkowski 2).lt_mono hle ((Causal.Flat.lt_iff_of_convex hV'c).2
    ⟨⟨v, hv, rfl⟩, ⟨w, hw, rfl⟩, h⟩)

theorem ta_segLt_inr : E0TASegLt E0.causalityYBTZ e0TAInr {v | 0 < v.2.1} := by
  intro O V _ hVc hVb hVO v hv w hw h
  have hVb' : ∀ u ∈ V, 0 < u.2.1 := fun u hu => hVb hu
  show E0.CLt (E0.rightOpens (E0.opensImage E0.toPaperY O))
    (E0.toPaper (orbitMk (GammaA (2 * π)) (btzDevInv v)))
    (E0.toPaper (orbitMk (GammaA (2 * π)) (btzDevInv w)))
  rw [ta_toPaper_btzDevInv (hVb' v hv), ta_toPaper_btzDevInv (hVb' w hw)]
  have hv' := E0.lift_unlift (Or.inl (hVb' v hv))
  have hw' := E0.lift_unlift (Or.inl (hVb' w hw))
  refine E0.clt_of_seg (E0.polar_unlift (hVb' v hv).le) (E0.polar_unlift (hVb' w hw).le)
    (by rw [hv', hw']; exact (E0.minkowski_lt_nullToMink v w).1 h) fun s hs => ?_
  rw [hv', hw']
  have hm : E0.seg v w s ∈ V := hVc.add_smul_sub_mem hv hw hs
  refine ⟨e0TAInr (E0.seg v w s), hVO _ hm, ?_⟩
  show Sum.inr (E0.toPaper _) = Sum.inr _
  rw [ta_toPaper_btzDevInv (hVb' _ hm)]

/-- **`typeAgreement`, convergence form, for `𝕄 ⊕ 𝔼₀` with the model causality.** -/
theorem e0_typeAgreementTendsto : E0TypeAgreementTendsto E0.causalityYBTZ :=
  e0_typeAgreementTendsto_of _ ta_segLt_inl ta_segLt_inr

/-- **`typeAgreement` verbatim at the tips in `𝕄`, for the model causality.** -/
theorem e0_typeAgreement_inl : E0TypeAgreementInl E0.causalityYBTZ :=
  e0_typeAgreement_inl_of E0.causalityYBTZ ta_segLt_inl

/-- **The diamond of the counterexample, for the model causality**: a point chronologically below
the tip `y₀ = [D⁻¹(0,1,0)]` in `O = [D⁻¹ B(v₀, 1/5)]` is `[D⁻¹ w]` with `w` in the past cone of
`v₀` (`E0.Lt.of_polar`: the developments at nearby angles are chronologically related). -/
theorem ta_diam : ∀ x : E0Y, E0.causalityYBTZ.lt e0CEO x e0CEy → x ∈ e0TAInr '' e0CEA := by
  intro x hx
  obtain ⟨w, hw, rfl⟩ := E0.causalityYBTZ.lt_mem_left hx
  have hb := e0CE_ball_b hw
  have hb₀ : (0 : ℝ) < e0CEv.2.1 := by simp [e0CEv]
  have h1 : E0.CLt (E0.rightOpens (E0.opensImage E0.toPaperY e0CEO))
      (E0.toPaper (orbitMk (GammaA (2 * π)) (btzDevInv w)))
      (E0.toPaper (orbitMk (GammaA (2 * π)) (btzDevInv e0CEv))) := hx
  rw [ta_toPaper_btzDevInv hb, ta_toPaper_btzDevInv hb₀] at h1
  have h2 := h1.lt
  have hθ : |-(e0CEv.2.2 / e0CEv.2.1) - -(w.2.2 / w.2.1)| ≤ π := by
    obtain ⟨-, hb', hc'⟩ := e0CE_abs_lt_of_dist hw
    simp only [e0CEv, sub_zero] at hb' hc' ⊢
    rw [abs_lt] at hb'
    have hw4 : 4 / 5 < w.2.1 := by linarith
    have : |w.2.2 / w.2.1| ≤ 1 := by
      rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < w.2.1), div_le_one (by linarith)]
      linarith
    have hπ := Real.pi_gt_three
    simp only [zero_div, neg_zero, zero_sub, abs_neg]
    linarith
  have h3 := E0.Lt.of_polar h2 (E0.polar_unlift hb.le) (E0.polar_unlift hb₀.le) hθ
  rw [E0.lift_unlift (Or.inl hb), E0.lift_unlift (Or.inl hb₀)] at h3
  exact ⟨w, ⟨hw, h3⟩, rfl⟩

/-- **`typeAgreement` is false for the model causality** (DEC-27 counterexample). -/
theorem e0_not_typeAgreement : ¬ E0TypeAgreement E0.causalityYBTZ :=
  e0_not_typeAgreement_of _ ta_segLt_inr ta_diam

end TypeAgreement

/-! ### §6 The local model `𝔐E₀` -/

section Assembly

/-- **The local model `𝔐E₀` from its open obligations** (`Causal.CBG.LocalModel`, the structure of
`Causal/CBG/Geometry.lean`, for `Y = 𝕄 ⊕ 𝔼₀`, `G` the a.e.-isomorphisms): the BTZ lines of every
admissible `M` (`hLine`, the `line` field of `SingularFlatAxioms`), `secondCountable_of_cauchy`
(`hSC`) and `typeAgreement` (`hTA`, **refuted**: `e0_not_typeAgreement`). Every other field is
proved: the model fields by WP-41c/WP-41e and §6b, `chartIso_mem` by WP-41e
(`E0.chartIso_mem_e0Groupoid`), `singularFlatAxioms` and `isCompact_*` here (§3–§5), and
`timeFunction`, `curvesExtend` by Levin's theorem (§5c; they do not use `hLine`). -/
noncomputable def e0LocalModelOf
    (hLine : ∀ (M : Type) [TopologicalSpace M] [T2Space M] [ConnectedSpace M]
      [SecondCountableTopology M] [ChartedSpace E0Y M] [HasGroupoid M e0Groupoid],
      E0GlobalBTZ (Causal.CBG.chartedCausality D M) (Causal.CBG.chartedSing e0SingY M 0))
    (hSC : ∀ {M : Type} [TopologicalSpace M] [T2Space M] [ConnectedSpace M] [ChartedSpace E0Y M]
      [HasGroupoid M e0Groupoid], (Causal.CBG.chartedCausality D M).GloballyHyperbolic →
      ∀ S : Set M, (Causal.CBG.chartedCausality D M).IsCauchySurface S →
      SecondCountableTopology S → SecondCountableTopology M)
    (hTA : E0TypeAgreement D) :
    Causal.CBG.LocalModel.{0} where
  Y := E0Y
  G := e0Groupoid
  causalityY := D
  singY := e0SingY
  rigid := e0_rigid
  localUnique_sing := e0_localUnique_sing
  localUnique_sing_adherent := e0_localUniqueSingAdherent
  localUnique_reg := e0_localUnique_reg
  regularChart := e0_regularChart
  absolutelyMinimalOn_Y := E0.absolutelyMinimalOn_YBTZ
  chartIso_mem := E0.chartIso_mem_e0Groupoid
  sing_mem := e0_sing_mem
  singularFlatAxioms := fun {M} _ _ _ _ _ _ =>
    e0_singularFlatAxioms_of E0.chartIso_mem_e0Groupoid (hLine M)
  curvesExtend := fun {M} _ _ _ _ _ _ hGH => e0_curvesExtend hGH
  timeFunction := fun {M} _ _ _ _ _ _ hGH => e0_timeFunction hGH
  isCompact_Jplus_inter_Jminus := fun {M} _ _ _ _ _ _ hGH S hS p => by
    have h := e0_singularFlatAxioms_of E0.chartIso_mem_e0Groupoid (hLine M)
    obtain ⟨T, hTc, hT⟩ := e0_timeFunction hGH
    exact sfa_isCompact_Jplus_inter_Jminus h hGH hTc hT hS p
  isCompact_Jminus_inter_Jplus := fun {M} _ _ _ _ _ _ hGH S hS p => by
    have h := e0_singularFlatAxioms_of E0.chartIso_mem_e0Groupoid (hLine M)
    obtain ⟨T, hTc, hT⟩ := e0_timeFunction hGH
    exact sfa_isCompact_Jminus_inter_Jplus h hGH hTc hT hS p
  secondCountable_of_cauchy := hSC
  isOpen_regY := e0_isOpen_regY
  dense_regY := e0_dense_regY
  typeAgreement := hTA
  coneSliceFuture := by
    rw [e0SingY_zero]
    exact E0.coneSliceFuture_YBTZ
  coneSlicePast := E0.coneSlicePast_YBTZ

end Assembly


/-! ### §6d Round-0 obligations now closed (wrappers) -/

section ClosedObligations

/-- **`chartIso_mem`** for `𝔐E₀` (round 0's (O1), closed): WP-41e's `E0.chartIso_mem_e0Groupoid`. -/
theorem e0_chartIso_mem : ∀ e ∈ e0Groupoid, Causal.ChartIso D D e :=
  E0.chartIso_mem_e0Groupoid

/-- **Local admissible measures** on globally hyperbolic `𝔼₀`-manifolds (round 0's (O3), closed,
§5b). No longer consumed by the assembly (Levin's theorem gives the time function, §5c); kept as
the `ModelMeasures` input of the strict `geroch_sing_i_imp_ii`. -/
theorem e0_modelMeasures (M : Type) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [ChartedSpace E0Y M] [HasGroupoid M e0Groupoid]
    (hGH : (Causal.CBG.chartedCausality D M).GloballyHyperbolic) :
    @Causal.Causality.ModelMeasures M _ (borel M) (Causal.CBG.chartedCausality D M) :=
  e0_modelMeasures_of hGH

end ClosedObligations

/-! ### §7 The remaining obligations: the BTZ lines (O2), and the line step (O4) -/

section Obligations

/-- **(O2) The BTZ lines of `M`** (`E0GlobalBTZ`, the field `line` of `SingularFlatAxioms`) on every
second-countable `𝔼₀`-manifold. -/
theorem e0_globalBTZ (M : Type) [TopologicalSpace M] [T2Space M] [ConnectedSpace M]
    [SecondCountableTopology M] [ChartedSpace E0Y M] [HasGroupoid M e0Groupoid] :
    E0GlobalBTZ (Causal.CBG.chartedCausality D M) (Causal.CBG.chartedSing e0SingY M 0) := by
  sorry -- SORRY(WP-41f:singularFlatAxioms.line): sing₀(M) is a topological 1-manifold with causally increasing charts (`e0_line_piece`: every BTZ point has an open O and an injective continuous γ : ]a,b[ → sing₀(M) onto sing₀(M) ∩ O, monotone for ≤); the global parametrisation of a component by ℝ (inextensible, a closed embedding when M is causal) is the classification of connected second-countable Hausdorff 1-manifolds (ℝ or S¹), absent from mathlib at this pin (alternative routes, not built: SCOPE (O2))

/-- **(O4′) The BTZ-line step on a globally hyperbolic `𝔼₀`-manifold with a second-countable Cauchy
surface**, `M` not assumed second countable: every component of `sing₀(M)` is the image of one
inextensible causal curve `ℝ → M`. The only input of `secondCountable_of_cauchy` left open
(`e0_secondCountable_of_lineStep`). The local model gives each BTZ point an increasing causal
interval of its component (`e0_line_piece`); the global step — excluding a non-σ-compact component
and parametrising the component by `ℝ`, inextensibly — is SCOPE (O4′). -/
theorem e0_lineStep_of_cauchy {M : Type} [TopologicalSpace M] [T2Space M]
    [ConnectedSpace M] [ChartedSpace E0Y M] [HasGroupoid M e0Groupoid]
    (_hGH : (Causal.CBG.chartedCausality D M).GloballyHyperbolic) (S : Set M)
    (_hS : (Causal.CBG.chartedCausality D M).IsCauchySurface S)
    (_hSS : SecondCountableTopology S) :
    E0LineStep (Causal.CBG.chartedCausality D M) (Causal.CBG.chartedSing e0SingY M 0) := by
  sorry -- SORRY(WP-41f:secondCountable_of_cauchy): the global BTZ line of (O2) without [SecondCountableTopology M]: each component L of sing₀(M) must be shown to be the image of an inextensible causal ℝ-curve. Reg M is second countable (`e0RegM_secondCountable`, proved) and L is locally an increasing causal interval (`e0_line_piece`), but excluding a non-σ-compact (long-line-type) component needs the (Aff⁺(ℝ), ℝ)-structure that the axis-preserving transitions induce on L (developing map into ℝ, then `Causal.secondCountableTopology_of_gx`), not built, and then O2's parametrisation and inextensibility; every global tool of the library on M (SingularFlatAxioms, Levin, geroch_sing_split, R1) asks [SecondCountableTopology M]

/-- **(O4) `secondCountable_of_cauchy`** for `𝔐E₀`: from the line step (O4′) by
`e0_secondCountable_of_lineStep` (sorry-free: `Reg M` second countable, countably many BTZ lines
through the Lindelöf `Σ ∩ sing₀`). -/
theorem e0_secondCountable_of_cauchy {M : Type} [TopologicalSpace M] [T2Space M]
    [ConnectedSpace M] [ChartedSpace E0Y M] [HasGroupoid M e0Groupoid]
    (hGH : (Causal.CBG.chartedCausality D M).GloballyHyperbolic) (S : Set M)
    (hS : (Causal.CBG.chartedCausality D M).IsCauchySurface S)
    (hSS : SecondCountableTopology S) : SecondCountableTopology M :=
  e0_secondCountable_of_lineStep (e0_lineStep_of_cauchy hGH S hS hSS) S hS hSS

end Obligations

/-- **The local model `𝔐E₀`, given `typeAgreement`** (`Y = 𝕄 ⊕ 𝔼₀`), through `e0LocalModelOf`, with
(O2) and (O4) as §7's tagged `sorry`s. **Its hypothesis is refutable** (`e0_not_typeAgreement`):
the CBG field `typeAgreement` is false for `𝔐E₀`, so no `Causal.CBG.LocalModel` with these
`Y, G, causalityY, singY` exists until the interface restates that field (its convergence form
`E0TypeAgreementTendsto D` is proved, `e0_typeAgreementTendsto`). -/
noncomputable def e0LocalModel_of_typeAgreement (hTA : E0TypeAgreement D) :
    Causal.CBG.LocalModel.{0} :=
  e0LocalModelOf e0_globalBTZ (fun hGH S hS hSS => e0_secondCountable_of_cauchy hGH S hS hSS) hTA

/-- **`lem:manifolds_manifolds_causally_connected` for `𝔼₀`-manifolds** (`RamcovGX.tex:2329`): the
causality of every `𝔼₀`-manifold is causally arc-connected. -/
theorem e0_causallyArcConnected {M : Type}
    [TopologicalSpace M] [ChartedSpace E0Y M] [HasGroupoid M e0Groupoid] :
    (Causal.CBG.chartedCausality D M).CausallyArcConnected :=
  charted_causallyArcConnected (M := M) E0.chartIso_mem_e0Groupoid E0.absolutelyMinimalOn_YBTZ
    E0.causalityYBTZ_causallyArcConnected

end E0LM

end GX
