import CausalScaffold.CBG.FromModel
import CausalScaffold.CBG.Corresponding
import CausalScaffold.Flat.Penrose
import CausalScaffold.Flat.SecondCountable

/-!
# A3 for the flat local model: germ extension at a corresponding boundary point, both time directions

Part of package 12 of the CBG campaign (design `docs/CBG-DESIGN.md` §4 "Flat instance": « A3
trivial (one g on a connected V) »; §5 rows 11–12). **No label is marked** (`docs/CBG-DESIGN.md:5–6`:
ETT labels are the ETT campaign's; rows stay partial until the singular instance discharges the
model). Cited, unmarked: `cor:ext_continue` — `ETT.tex:2144`; Sbierski 1309.7591, Prop 3.7, Lemma 3.8
(pp. 15–16). Barbot's `𝐌ⁿ` is `Minkowski d` with `n = d + 1` (kb/0024).

> Lemma 3.8. Let U be a CGHD of M and M′ with isometric embedding ψ : U ⊆ M → M′. Then the set C
> is open in ∂U and the isometric embedding ψ : U → M′ extends smoothly to ψ : U ∪ C → M′.
> (Sbierski, p. 16)

> Let p ∈ W ⊆ V be a small open neighbourhood of p such that W ⊆ I⁺(γ(−ε)) […] We can now define
> the smooth extension ψ̂ : W → M′ […] it also agrees with ψ on W ∩ U, since the exponential map
> commutes with isometries. (Sbierski, proof of Lemma 3.8, p. 16)

> Let $(p,q)\in C$. Then $f$ extends continuously to $p$ by setting $f(p)=q$.
> (`cor:ext_continue`, `ETT.tex:2145`)

## What is proved (no `sorry`, axioms `propext`, `Classical.choice`, `Quot.sound`)

* **`flat_germExtFuture`, `flat_germExtPast`**: for every `𝔐 : LocalModel.{0}` whose data are the
  flat ones (`𝔐.Y = Minkowski d` and four `HEq`s: topology, `G = gxGroupoid (isom d) (Minkowski d)`,
  `causalityY = minkowski d`, `singY = ∅`), `𝔐.GermExtFuture` and `𝔐.GermExtPast` — the Level-A
  fields A3 of `CBG/FromModel`, read on `𝔐`, verbatim. For `flatModelOf d hJ₁ hJ₂` (`Flat/CBG`) the
  five hypotheses are `rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl`. Only `𝔐`'s own fields are used: B1
  `rigid`, B2 `localUnique_reg`, B3 `chartIso_mem`, `absolutelyMinimalOn_Y`, `singularFlatAxioms`,
  `curvesExtend`, and one compactness field (`isCompact_Jminus_inter_Jplus` future side,
  `isCompact_Jplus_inter_Jminus` past side, for `lem:Sigma_separe` at `p` and `q`); second
  countability of `M`, `N` (absent from the A3 field, obstruction (0) of `FromModel`'s `SORRY`) is
  `flat_secondCountableTopology` (DEC-49).
* **Sbierski Prop 3.7 (i) ⇒ (ii), model-free** (`IsCorrPair`, any causalities):
  `IsCorrPair.lt_of_lt_of_corresponds` (`x ∈ U`, `x ≪ p` ⇒ `ψ x ≪ q`),
  `IsCorrPair.exists_lt_forall_mem` (for every neighbourhood `V'` of `q` an `x₀ ∈ U ∩ I⁻(p)` with
  `ψ(I⁺(x₀) ∩ I⁻(p) ∩ U) ⊆ V'`, from strong causality of `N` = GH + tarentin), the q-side
  `IsCorrPair.mem_Jplus_of_corresponds` (Sbierski's footnote 21: `q ∈ J⁺(ψ Σ)` when `p ∈ J⁺(Σ)`),
  `mem_of_mem_Jplus_of_lt`, `IsCorrPair.mem_of_lt_of_corresponds`.
* **The causal localisation (the step `Flat/CBG` named as owed)**: along the chart segment
  `κ p − s ε e₀` (`s → 0⁺`), which lies in `U`, `ψ → q` (`germ_core`); the timelike segment plays
  Sbierski's geodesic `γ`.
* **The chart step** `germ_chart_extend` (geometric, `ε = ±1`): on the component of
  `κ(U ∩ ψ⁻¹ dom κ')` containing the end of the segment, `κ' ∘ ψ ∘ κ⁻¹` is one `e ∈ G` (B2), whose
  source is all of `Minkowski d`; `e (κ p) = κ' q` by continuity; `φ = κ'⁻¹ ∘ e ∘ κ` agrees with
  `ψ` on all of `O ∩ U` for `O = κ⁻¹(B(κ p, ρ₁) ∩ I^ε(c))`, `c` on the segment: that piece of `U` is
  star-shaped from `c` in the chart (causal convexity of `U`, read through `germ_chart_rel`), hence
  connected, and B1 rigidity (`eqOn_of_liftPropOn`) applies — Sbierski's `W ⊆ I⁺(γ(−ε))`.
* `germ_isCorrPair`: `CGHDData.isCorrPair`/`causallyConvexIn`/`causallyConvexIn'` on a flat atlas,
  without a `Geometry`; `germ_chart_rel` (`≤`, `≪` of `Minkowski d` in a chart ball are those of
  `chartedCausality`); `flat_germ_future`, `flat_germ_past` (the same with the model facts as named
  hypotheses); the Minkowski cones `germCone` (open, convex, star-shaped).

## Hypothesis checklist (Sbierski Lemma 3.8, extension part; `cor:ext_continue`)

| paper | here |
|---|---|
| `U` a CGHD of `M`, `M′`, `ψ` an isometric embedding | ✓ carried: the hypotheses of `GermExtFuture`/`GermExtPast` verbatim (`ψ` an injective `LiftPropOn` morphism on `U`, `M`, `N`, `U`, `ψ(U)` GH, `Σ` Cauchy in all four) |
| `(p, p′)` corresponding (Def 3.5) | ✓ carried: `MapClusterPt q (𝓝[U] p) ψ` (`corresponds_iff_mapClusterPt`) |
| `p ∈ J⁺(Σ)` (resp. `J⁻(Σ)`), « without loss of generality » | ✓ carried: the two fields; the side of `q` is proved (footnote 21, `mem_Jplus_of_corresponds`) |
| convex normal neighbourhoods, `exp` | ⚠ replaced (flat): convex chart balls and straight segments; `exp` is the chart |
| strong causality of `M′`; `≤` closed | ✓ derived: GH + tarentin (`GloballyHyperbolic.stronglyCausal`, `isClosed_Jplus_singleton`) |
| `M`, `M′` second countable (Sbierski's manifolds) | ✓ derived for flat atlases (`flat_secondCountableTopology`), not assumed |
| model | ⚠ strengthened: **regular flat data only** (`singY = ∅`); the BTZ case is gx's |
| « `C` is open in `∂U` » (first assertion) | not here: `CGHDData.isOpen_correspondingSet` (package 5) derives it from A3 |

## SCOPE (disclosed)

* **What the flat A3 rests on.** Nothing beyond `𝔐`'s fields. For `flatModelOf d hJ₁ hJ₂` that is
  `hJ₂` (future side) / `hJ₁` (past side) through `isCompact_*`; for `flatModel d` the two tagged R1
  `sorry`s of `Flat/CBG` (`flat_isCompact_Jminus_inter_of_isCauchySurface` and past form). The
  compactness is used only for `lem:Sigma_separe` (`J^±(Σ)` a neighbourhood of `p`, `q`); the
  chronal-flow splitting (`flat_isClosed_Jplus_Jminus_of_isCauchySurface`, `Flat/CBG`) gives the
  closedness of `J^∓(Σ)` without R1 and could replace it (not done: this file may not import
  `Flat/CBG`).
* **The connected piece is not `U ∩ B` for a chart ball `B`** (the earlier reading): it is
  `U ∩ κ⁻¹(B(κ p, ρ₁) ∩ I^ε(c))`, star-shaped from a point `c` of `U` on the segment, which is what
  Sbierski's proof uses; its connectedness needs only causal convexity of `U`, no `J⁺(Σ)`-cylinder.
* **The statement quantifies over local models with flat data** (`HEq` hypotheses) rather than
  naming `flatModelOf`, because this file must not import `Flat/CBG` (which imports it). `A3` depends
  on `𝔐` only through its data, so the integrator passes `rfl` and `HEq.rfl`.
* `LocalModel.IsMor` (`LiftPropOn` of the groupoid) is not identified with `IsLocalIsometry`
  (`Flat/FlatSpacetime`), as in `Flat/CBG`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set Topology Filter Function TopologicalSpace ChartedSpace StructureGroupoid Flat

namespace CBG

section ModelFree

variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  {C : Causality M} {D : Causality N} {U : Opens M} {V : Opens N} {ψ : M → N} {g : N → M}

/-- **Step A of Sbierski Prop 3.7** (« `ψ(q) ≪ ψ(s) ≤ p′` »): for corresponding `p`, `q` and
`x ∈ U` with `x ≪ p`, `ψ x ≪ q`. -/
theorem IsCorrPair.lt_of_lt_of_corresponds (h : IsCorrPair C D U V ψ g)
    (hcv : C.CausallyConvexIn (U : Set M) ⊤) {p : M} {q : N} (hZ : p ∈ C.Zminus)
    (hPD : D.PushUp) (hclD : ∀ y, IsClosed (D.Jplus ⊤ {y}))
    (hc : Corresponds (U : Set M) ψ p q) {x : M} (hx : x ∈ U) (hxp : C.lt ⊤ x p) :
    D.lt ⊤ (ψ x) q := by
  obtain ⟨s, hxs, hsp⟩ := Causality.exists_lt_lt_of_mem_Zminus hZ hxp
  obtain ⟨u, hus, huU⟩ := mem_closure_iff_nhds.1 (mem_closure_of_corresponds hc) _
    (Causality.isOpen_Iplus.mem_nhds (show p ∈ C.Iplus ⊤ {s} by simpa using hsp))
  have hsU : s ∈ U := hcv.2 x hx u huU
    (Causality.mem_diamond.2 ⟨C.le_of_lt hxs, C.le_of_lt (by simpa using hus)⟩)
  exact h.lt_of_corresponds hPD (hclD _) hx hsU hxs (Causality.Jplus_mem_nhds_of_lt hsp) hc

/-- A point of `J⁺(T)` (`T ⊆ V`) chronologically below a point `q` corresponding to `p` lies in
`V` (causal convexity of `V`; `q ∈ closure V`). -/
theorem IsCorrPair.mem_of_lt_of_corresponds (h : IsCorrPair C D U V ψ g)
    (hcv : D.CausallyConvexIn (V : Set N) ⊤) {T : Set N} (hTV : T ⊆ V) {p : M} {q : N}
    (hc : Corresponds (U : Set M) ψ p q) {y : N} (hy : y ∈ D.Jplus ⊤ T) (hyq : D.lt ⊤ y q) :
    y ∈ V := by
  obtain ⟨τ, hτ, hτy⟩ := hy
  obtain ⟨x, hxU, -, hψx⟩ := hc univ univ_mem _
    (Causality.isOpen_Iplus.mem_nhds (show q ∈ D.Iplus ⊤ {y} by simpa using hyq))
  exact hcv.2 τ (hTV hτ) (ψ x) (h.mapsTo hxU)
    (Causality.mem_diamond.2 ⟨hτy, D.le_of_lt (by simpa using hψx)⟩)

/-- **Sbierski Prop 3.7, (i) ⇒ (ii), in the form Lemma 3.8 uses** (the strong causality of
`N` at `q`, « we can find a `q′ ∈ V′ ∩ I⁻(p′)` such that `I⁺(q′) ∩ I⁻(p′) ⊆ V′` »): for every
neighbourhood `V'` of `q` there is `x₀ ∈ U ∩ I⁻(p)` with `ψ(I⁺(x₀) ∩ I⁻(p) ∩ U) ⊆ V'`. Model-free;
`T ⊆ V` with `J⁺(T)` a neighbourhood of `q` is `lem:Sigma_separe` at `q` (`T = ψ S`). -/
theorem IsCorrPair.exists_lt_forall_mem (h : IsCorrPair C D U V ψ g)
    (hcvU : C.CausallyConvexIn (U : Set M) ⊤) (hcvV : D.CausallyConvexIn (V : Set N) ⊤)
    [T2Space N] (hGD : D.GloballyHyperbolic) (hTD : D.Tarentin) {p : M} {q : N}
    (hZp : p ∈ C.Zminus) (hZq : q ∈ D.Zminus) (hPC : C.PushUp) (hPD : D.PushUp)
    (hclC : ∀ x, IsClosed (C.Jplus ⊤ {x})) (hclD : ∀ y, IsClosed (D.Jplus ⊤ {y}))
    {T : Set N} (hTV : T ⊆ V) (hsep : D.Jplus ⊤ T ∈ 𝓝 q)
    (hc : Corresponds (U : Set M) ψ p q) {V' : Set N} (hV' : V' ∈ 𝓝 q) :
    ∃ x₀ ∈ U, C.lt ⊤ x₀ p ∧ ∀ y ∈ U, C.lt ⊤ x₀ y → C.lt ⊤ y p → ψ y ∈ V' := by
  obtain ⟨W, hW, hWsub, hWcv⟩ := hGD.stronglyCausal hTD q _ (inter_mem hV' hsep)
  obtain ⟨s', hs'I, hs'W⟩ := hZq W hW
  have hs'q : D.lt ⊤ s' q := by simpa using hs'I
  obtain ⟨s'', hs's'', hs''q⟩ := Causality.exists_lt_lt_of_mem_Zminus hZq hs'q
  have hs'J : s' ∈ D.Jplus ⊤ T := (hWsub hs'W).2
  have hs''J : s'' ∈ D.Jplus ⊤ T := by
    obtain ⟨τ, hτ, hτs⟩ := hs'J
    exact ⟨τ, hτ, D.le_trans hτs (D.le_of_lt hs's'')⟩
  have hs'V := h.mem_of_lt_of_corresponds hcvV hTV hc hs'J hs'q
  have hs''V := h.mem_of_lt_of_corresponds hcvV hTV hc hs''J hs''q
  have hx₀p : C.lt ⊤ (g s') p := h.symm.lt_of_corresponds hPC (hclC _) hs'V hs''V hs's''
    (Causality.Jplus_mem_nhds_of_lt hs''q) (h.corresponds_symm hc)
  have hx₀U : g s' ∈ U := h.mapsTo_inv hs'V
  refine ⟨g s', hx₀U, hx₀p, fun y hyU hx₀y hyp => ?_⟩
  have h1 : D.lt ⊤ s' (ψ y) := by
    have := (h.lt_iff _ hx₀U _ hyU).1 hx₀y
    rwa [h.rightInvOn hs'V] at this
  have h2 := h.lt_of_lt_of_corresponds hcvU hZp hPD hclD hc hyU hyp
  exact (hWsub (hWcv.2 s' hs'W q (mem_of_mem_nhds hW)
    (Causality.mem_diamond.2 ⟨D.le_of_lt h1, D.le_of_lt h2⟩))).1

/-- A point of `J⁺(S)` (`S ⊆ U`) chronologically below a point `p` of `closure U` lies in `U`
(causal convexity of `U`). -/
theorem mem_of_mem_Jplus_of_lt (hcv : C.CausallyConvexIn (U : Set M) ⊤) {S : Set M}
    (hSU : S ⊆ U) {p : M} (hp : p ∈ closure (U : Set M)) {x : M} (hx : x ∈ C.Jplus ⊤ S)
    (hxp : C.lt ⊤ x p) : x ∈ U := by
  obtain ⟨σ, hσ, hσx⟩ := hx
  obtain ⟨u, hux, huU⟩ := mem_closure_iff_nhds.1 hp _
    (Causality.isOpen_Iplus.mem_nhds (show p ∈ C.Iplus ⊤ {x} by simpa using hxp))
  exact hcv.2 σ (hSU hσ) u huU
    (Causality.mem_diamond.2 ⟨hσx, C.le_of_lt (by simpa using hux)⟩)

/-- **Footnote 21 of Sbierski** (« one cannot have one lying to the future and the other to the
past »): if `p ∈ ∂U` lies in the future of `S` (`J⁺(S)` a neighbourhood of `p`, `S ⊆ U` acausal)
and `q ∉ V` corresponds to `p`, then `q` is not in `J⁻(ψ S) ∖ J⁺(ψ S)`. -/
theorem IsCorrPair.mem_Jplus_of_corresponds (h : IsCorrPair C D U V ψ g)
    (hcv : C.CausallyConvexIn (U : Set M) ⊤) {p : M} {q : N} (hZ : p ∈ C.Zminus)
    (hPD : D.PushUp) (hclD : ∀ y, IsClosed (D.Jplus ⊤ {y}))
    (hc : Corresponds (U : Set M) ψ p q) (hqV : q ∉ V) (hcausM : C.IsCausal)
    (hcausN : D.IsCausal) {S : Set M} (hac : C.IsAcausal S) (hSU : S ⊆ U)
    (hsep : C.Jplus ⊤ S ∈ 𝓝 p) (hcov : q ∈ D.Jplus ⊤ (ψ '' S) ∪ D.Jminus ⊤ (ψ '' S)) :
    q ∈ D.Jplus ⊤ (ψ '' S) := by
  rcases hcov with h1 | ⟨_, ⟨σ₀, hσ₀, rfl⟩, hqσ⟩
  · exact h1
  exfalso
  obtain ⟨x, hxI, hxJ⟩ := hZ _ hsep
  have hxp : C.lt ⊤ x p := by simpa using hxI
  have hxU := mem_of_mem_Jplus_of_lt hcv hSU (mem_closure_of_corresponds hc) hxJ hxp
  have hxq := h.lt_of_lt_of_corresponds hcv hZ hPD hclD hc hxU hxp
  have hxσ₀ : C.le ⊤ x σ₀ :=
    (h.le_iff x hxU σ₀ (hSU hσ₀)).2 (D.le_trans (D.le_of_lt hxq) hqσ)
  obtain ⟨σ, hσ, hσx⟩ := hxJ
  have e : σ = σ₀ := hac σ hσ σ₀ hσ₀ (C.le_trans hσx hxσ₀)
  subst e
  have hx : x = σ := hcausM hxσ₀ hσx
  subst hx
  exact hqV (hcausN hqσ (D.le_of_lt hxq) ▸ h.mapsTo hxU)

end ModelFree

/-! ### The chart step: one element of the groupoid on a star-shaped piece -/

section Chart

variable {d : ℕ}

local notation "𝔾" => gxGroupoid (isom d) (Minkowski d)

/-- The time vector `ε e₀` of `Minkowski d` (`ε = ±1` picks the time direction). -/
def germVec (d : ℕ) (ε : ℝ) : Minkowski d := (ε, 0)

theorem norm_germVec {ε : ℝ} (hε : ε = 1 ∨ ε = -1) : ‖germVec d ε‖ = 1 := by
  rcases hε with rfl | rfl <;> simp [germVec, Prod.norm_def]

theorem dist_sub_smul_germVec {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (y : Minkowski d) (s s' : ℝ) :
    dist (y - s • germVec d ε) (y - s' • germVec d ε) = |s - s'| := by
  rw [dist_eq_norm, show y - s • germVec d ε - (y - s' • germVec d ε) = (s' - s) • germVec d ε by
    rw [sub_smul]; abel, norm_smul, norm_germVec hε, mul_one, Real.norm_eq_abs, abs_sub_comm]

theorem dist_sub_smul_germVec_self {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (y : Minkowski d) (s : ℝ) :
    dist (y - s • germVec d ε) y = |s| := by
  simpa using dist_sub_smul_germVec hε y s 0

/-- The open `ε`-cone at `c`: `I⁺(c)` for `ε = 1`, `I⁻(c)` for `ε = -1`. -/
def germCone (ε : ℝ) (c : Minkowski d) : Set (Minkowski d) := {y | ‖y.2 - c.2‖ < ε * (y.1 - c.1)}

theorem isOpen_germCone {ε : ℝ} {c : Minkowski d} : IsOpen (germCone ε c) :=
  isOpen_lt (by fun_prop) (by fun_prop)

theorem convex_germCone {ε : ℝ} {c : Minkowski d} : Convex ℝ (germCone ε c) := by
  refine convex_iff_forall_pos.2 fun a ha b hb θ₁ θ₂ h1 h2 h12 => ?_
  simp only [germCone, mem_setOf_eq] at ha hb ⊢
  have e2 : (θ₁ • a + θ₂ • b).2 - c.2 = θ₁ • (a.2 - c.2) + θ₂ • (b.2 - c.2) := by
    simp only [Prod.snd_add, Prod.smul_snd, smul_sub]
    rw [show (θ₁ • a.2 + θ₂ • b.2 - c.2) = θ₁ • a.2 + θ₂ • b.2 - (θ₁ + θ₂) • c.2 by rw [h12, one_smul],
      add_smul]
    abel
  have e1 : (θ₁ • a + θ₂ • b).1 - c.1 = θ₁ * (a.1 - c.1) + θ₂ * (b.1 - c.1) := by
    simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
    linear_combination c.1 * h12
  rw [e2, e1]
  calc ‖θ₁ • (a.2 - c.2) + θ₂ • (b.2 - c.2)‖ ≤ θ₁ * ‖a.2 - c.2‖ + θ₂ * ‖b.2 - c.2‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, norm_smul, Real.norm_of_nonneg h1.le, Real.norm_of_nonneg h2.le]
    _ < θ₁ * (ε * (a.1 - c.1)) + θ₂ * (ε * (b.1 - c.1)) := by
        have := mul_lt_mul_of_pos_left ha h1
        have := mul_lt_mul_of_pos_left hb h2
        linarith
    _ = ε * (θ₁ * (a.1 - c.1) + θ₂ * (b.1 - c.1)) := by ring

theorem germCone_add_smul {ε : ℝ} {c y : Minkowski d} (hy : y ∈ germCone ε c) {t : ℝ}
    (ht : 0 < t) : c + t • (y - c) ∈ germCone ε c := by
  simp only [germCone, mem_setOf_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    Prod.fst_sub, Prod.snd_sub, add_sub_cancel_left, smul_eq_mul, norm_smul,
    Real.norm_of_nonneg ht.le] at hy ⊢
  nlinarith

theorem sub_smul_mem_germCone {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (y : Minkowski d) {s s₀ : ℝ}
    (h : s < s₀) : y - s • germVec d ε ∈ germCone ε (y - s₀ • germVec d ε) := by
  have hεε : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
  simp only [germCone, germVec, mem_setOf_eq, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul, smul_zero, sub_zero, sub_self, norm_zero]
  nlinarith

theorem le_of_mem_germCone_one {c y : Minkowski d} (hy : y ∈ germCone 1 c) :
    (minkowski d).le ⊤ c y := by
  rw [minkowski_le_top_iff]
  simp only [germCone, mem_setOf_eq, one_mul] at hy
  exact hy.le

theorem le_of_mem_germCone_neg {c y : Minkowski d} (hy : y ∈ germCone (-1) c) :
    (minkowski d).le ⊤ y c := by
  rw [minkowski_le_top_iff, norm_sub_rev]
  simp only [germCone, mem_setOf_eq] at hy
  linarith

/-- **The chart step of Sbierski Lemma 3.8, flat** (geometric form, both time directions `ε = ±1`).
Read in the chart `κ` at `p`, let the open segment `κ p − s ε e₀` (`0 < s < ρ`, in the ball
`B(κ p, ρ) ⊆ κ.target`) lie in `U`, let `ψ` converge to `q` along it, and let `U` be causally convex
in the chart (`hconv`). Then `ψ` extends near `p` by one element of the groupoid: on the component
of the chart image of `U ∩ ψ⁻¹(dom κ')` containing the end of the segment, `κ' ∘ ψ ∘ κ⁻¹` is one
`e ∈ G` (B2, `hreg`), `e (κ p) = κ' q` by continuity, and `κ'⁻¹ ∘ e ∘ κ` agrees with `ψ` on all
of `O ∩ U` for `O` the preimage of `B(κ p, ρ₁) ∩ I^ε(c)`, `c` on the segment: that piece of `U` is
star-shaped from `c` in the chart (`hconv`), so connected, and rigidity (B1, `hrig`) applies. -/
theorem germ_chart_extend {M N : Type*} [TopologicalSpace M] [TopologicalSpace N] [T2Space N]
    [ChartedSpace (Minkowski d) M] [ChartedSpace (Minkowski d) N] [HasGroupoid M 𝔾]
    [HasGroupoid N 𝔾]
    (hrig : ∀ e ∈ 𝔾, ∀ e' ∈ 𝔾, ∀ U : Set (Minkowski d), IsOpen U → IsPreconnected U →
      U ⊆ e.source → U ⊆ e'.source → ∀ O ⊆ U, IsOpen O → O.Nonempty → EqOn e e' O → EqOn e e' U)
    (hreg : ∀ W : Set (Minkowski d), IsOpen W → IsConnected W → ∀ f : Minkowski d → Minkowski d,
      (∀ y ∈ W, (𝔾).IsLocalStructomorphWithinAt f W y) → InjOn f W →
      ∃ e ∈ 𝔾, (∀ y ∈ W, connectedComponent y ⊆ e.source) ∧ EqOn f e W)
    (U : Opens M) {ψ : M → N} (hψ : LiftPropOn (𝔾).IsLocalStructomorphWithinAt ψ U)
    (hinj : InjOn ψ U) {p : M} {q : N} {ε : ℝ} (hε : ε = 1 ∨ ε = -1) {ρ : ℝ} (hρ : 0 < ρ)
    (hball : Metric.ball (chartAt (Minkowski d) p p) ρ ⊆ (chartAt (Minkowski d) p).target)
    (hseg : ∀ s ∈ Ioo 0 ρ,
      (chartAt (Minkowski d) p).symm (chartAt (Minkowski d) p p - s • germVec d ε) ∈ U)
    (hlim : Tendsto (fun s : ℝ => ψ ((chartAt (Minkowski d) p).symm
      (chartAt (Minkowski d) p p - s • germVec d ε))) (𝓝[>] 0) (𝓝 q))
    (hconv : ∀ y ∈ Metric.ball (chartAt (Minkowski d) p p) ρ,
      ∀ w ∈ Metric.ball (chartAt (Minkowski d) p p) ρ,
      ∀ z ∈ Metric.ball (chartAt (Minkowski d) p p) ρ,
      (minkowski d).le ⊤ y w → (minkowski d).le ⊤ w z → (chartAt (Minkowski d) p).symm y ∈ U →
        (chartAt (Minkowski d) p).symm z ∈ U → (chartAt (Minkowski d) p).symm w ∈ U) :
    ∃ (O : Opens M) (φ : M → N), p ∈ O ∧ LiftPropOn (𝔾).IsLocalStructomorphWithinAt φ O ∧
      φ p = q ∧ EqOn φ ψ (O ⊓ U : Opens M) := by
  set κ := chartAt (Minkowski d) p with hκdef
  set κ' := chartAt (Minkowski d) q with hκ'def
  set y₀ := κ p with hy₀
  set γ : ℝ → Minkowski d := fun s => y₀ - s • germVec d ε with hγ
  have hγc : Continuous γ := continuous_const.sub (continuous_id.smul continuous_const)
  have hγdist : ∀ s, dist (γ s) y₀ = |s| := dist_sub_smul_germVec_self hε y₀
  have hγball : ∀ s ∈ Ioo 0 ρ, γ s ∈ Metric.ball y₀ ρ := fun s hs => by
    rw [Metric.mem_ball, hγdist, abs_of_pos hs.1]; exact hs.2
  have hγt : Tendsto γ (𝓝[>] 0) (𝓝 y₀) := by
    have : Tendsto γ (𝓝 0) (𝓝 (γ 0)) := hγc.tendsto 0
    rw [show γ 0 = y₀ by simp [γ]] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), ψ (κ.symm (γ s)) ∈ κ'.source :=
    Filter.mem_map.1 (hlim (κ'.open_source.mem_nhds (mem_chart_source _ q)))
  obtain ⟨u, hu, hus⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
  have hu0 : (0 : ℝ) < u := hu
  set s₁ := min (u / 2) (ρ / 2) with hs₁def
  have hs₁ : 0 < s₁ := lt_min (half_pos hu0) (half_pos hρ)
  have hs₁u : s₁ < u := (min_le_left _ _).trans_lt (half_lt_self hu0)
  have hs₁ρ : s₁ < ρ := (min_le_right _ _).trans_lt (half_lt_self hρ)
  have hIoc : ∀ s ∈ Ioc 0 s₁, s ∈ Ioo 0 ρ ∧ s ∈ Ioo 0 u := fun s hs =>
    ⟨⟨hs.1, hs.2.trans_lt hs₁ρ⟩, ⟨hs.1, hs.2.trans_lt hs₁u⟩⟩
  have hψc : ContinuousOn ψ U := fun y hy => (hψ y hy).continuousWithinAt
  set Ω : Set (Minkowski d) := κ.target ∩ κ.symm ⁻¹' ((U : Set M) ∩ ψ ⁻¹' κ'.source) with hΩdef
  have hΩ : IsOpen Ω := κ.continuousOn_symm.isOpen_inter_preimage κ.open_target
    (hψc.isOpen_inter_preimage U.isOpen κ'.open_source)
  have hsegΩ : γ '' Ioc 0 s₁ ⊆ Ω := by
    rintro _ ⟨s, hs, rfl⟩
    obtain ⟨h1, h2⟩ := hIoc s hs
    exact ⟨hball (hγball s h1), hseg s h1, hus h2⟩
  have hsegc : IsPreconnected (γ '' Ioc 0 s₁) := isPreconnected_Ioc.image _ hγc.continuousOn
  have hc₁ : γ s₁ ∈ γ '' Ioc 0 s₁ := ⟨s₁, ⟨hs₁, le_rfl⟩, rfl⟩
  set Ω₀ := connectedComponentIn Ω (γ s₁) with hΩ₀def
  have hΩ₀o : IsOpen Ω₀ := hΩ.connectedComponentIn
  have hsegΩ₀ : γ '' Ioc 0 s₁ ⊆ Ω₀ := hsegc.subset_connectedComponentIn hc₁ hsegΩ
  have hΩ₀Ω : Ω₀ ⊆ Ω := connectedComponentIn_subset _ _
  have hΩ₀c : IsConnected Ω₀ := isConnected_connectedComponentIn_iff.2 (hsegΩ hc₁)
  set f : Minkowski d → Minkowski d := κ' ∘ ψ ∘ κ.symm with hfdef
  have hG := isLocalStructomorphWithinAt_localInvariantProp 𝔾
  have hκ : κ ∈ (𝔾).maximalAtlas M := StructureGroupoid.chart_mem_maximalAtlas _ p
  have hκ' : κ' ∈ (𝔾).maximalAtlas N := StructureGroupoid.chart_mem_maximalAtlas _ q
  have hloc : ∀ y ∈ Ω₀, (𝔾).IsLocalStructomorphWithinAt f Ω₀ y := by
    intro y hy
    have hyΩ := hΩ₀Ω hy
    have hP := hG.liftPropOn_indep_chart hκ hκ' hψ (y := y) ⟨hyΩ.1, hyΩ.2⟩
    intro _
    obtain ⟨e, he, hef, hex⟩ := hP hyΩ.2.1
    exact ⟨e, he, fun z hz => hef ⟨(hΩ₀Ω hz.1).2.1, hz.2⟩, hex⟩
  have hinjf : InjOn f Ω₀ := by
    intro a ha b hb hab
    have ha' := hΩ₀Ω ha
    have hb' := hΩ₀Ω hb
    have := hinj ha'.2.1 hb'.2.1 (κ'.injOn ha'.2.2 hb'.2.2 hab)
    exact κ.symm.injOn ha'.1 hb'.1 this
  obtain ⟨e, he, hesrc, hfe⟩ := hreg Ω₀ hΩ₀o hΩ₀c f hloc hinjf
  have hesrc' : e.source = univ := by
    have := hesrc (γ s₁) (mem_connectedComponentIn (hsegΩ hc₁))
    rw [PreconnectedSpace.connectedComponent_eq_univ] at this
    exact eq_univ_of_univ_subset this
  have hey₀ : e y₀ = κ' q := by
    have h1 : Tendsto (fun s => e (γ s)) (𝓝[>] 0) (𝓝 (e y₀)) :=
      ((e.continuousOn.continuousAt (e.open_source.mem_nhds (by rw [hesrc']; trivial))).tendsto).comp
        hγt
    have h2 : Tendsto (fun s => κ' (ψ (κ.symm (γ s)))) (𝓝[>] 0) (𝓝 (κ' q)) :=
      ((κ'.continuousAt (mem_chart_source _ q)).tendsto).comp hlim
    have h3 : (fun s => e (γ s)) =ᶠ[𝓝[>] 0] (fun s => κ' (ψ (κ.symm (γ s)))) := by
      filter_upwards [Ioo_mem_nhdsGT hs₁] with s hs
      exact (hfe (hsegΩ₀ ⟨s, ⟨hs.1, hs.2.le⟩, rfl⟩)).symm
    exact tendsto_nhds_unique (h1.congr' h3) h2
  set O₁ : Set M := κ.source ∩ κ ⁻¹' (e.source ∩ e ⁻¹' κ'.target) with hO₁def
  have hO₁ : IsOpen O₁ := κ.isOpen_inter_preimage (e.isOpen_inter_preimage κ'.open_target)
  set φ : M → N := κ'.symm ∘ e ∘ κ with hφdef
  have hφ : LiftPropOn (𝔾).IsLocalStructomorphWithinAt φ O₁ := by
    refine liftPropOn_of_maximalAtlas_rep hκ hκ' hO₁ (fun z hz => hz.1) ?_ ?_ he
      (fun z hz => hz.2.1) ?_
    · intro z hz; exact κ'.map_target hz.2.2
    · refine κ'.continuousOn_symm.comp
        (e.continuousOn.comp (κ.continuousOn.mono fun z hz => hz.1) ?_) ?_
      · intro z hz; exact hz.2.1
      · intro z hz; exact hz.2.2
    · intro z hz
      simp only [φ, comp_apply]
      exact κ'.right_inv hz.2.2
  have hφψ : ∀ z ∈ κ.source, κ z ∈ Ω₀ → φ z = ψ z := by
    intro z hz hzΩ
    have hzΩ' := hΩ₀Ω hzΩ
    have hψz : ψ z ∈ κ'.source := by
      have := hzΩ'.2.2; rwa [mem_preimage, κ.left_inv hz] at this
    simp only [φ, comp_apply]
    rw [← hfe hzΩ]
    simp only [f, comp_apply, κ.left_inv hz]
    exact κ'.left_inv hψz
  -- the radius `ρ₁` on which `e` lands in the chart at `q`
  have hnhd : Metric.ball y₀ ρ ∩ e ⁻¹' κ'.target ∈ 𝓝 y₀ :=
    inter_mem (Metric.ball_mem_nhds _ hρ)
      ((e.continuousOn.continuousAt (e.open_source.mem_nhds (by rw [hesrc']; trivial))).preimage_mem_nhds
        (κ'.open_target.mem_nhds (by rw [hey₀]; exact κ'.map_source (mem_chart_source _ q))))
  obtain ⟨ρ₁, hρ₁, hρ₁sub⟩ := Metric.mem_nhds_iff.1 hnhd
  set s₀ := min s₁ ρ₁ / 2 with hs₀def
  have hs₀ : 0 < s₀ := half_pos (lt_min hs₁ hρ₁)
  have hs₀s₁ : s₀ < s₁ := (half_lt_self (lt_min hs₁ hρ₁)).trans_le (min_le_left _ _)
  have hs₀ρ₁ : s₀ < ρ₁ := (half_lt_self (lt_min hs₁ hρ₁)).trans_le (min_le_right _ _)
  set c := γ s₀ with hcdef
  have hcΩ₀ : c ∈ Ω₀ := hsegΩ₀ ⟨s₀, ⟨hs₀, hs₀s₁.le⟩, rfl⟩
  have hcU : κ.symm c ∈ U := (hΩ₀Ω hcΩ₀).2.1
  have hct : c ∈ κ.target := (hΩ₀Ω hcΩ₀).1
  have hcB₁ : c ∈ Metric.ball y₀ ρ₁ := by
    rw [Metric.mem_ball, hγdist, abs_of_pos hs₀]; exact hs₀ρ₁
  have hB₁ : Metric.ball y₀ ρ₁ ⊆ Metric.ball y₀ ρ := fun y hy => (hρ₁sub hy).1
  have hγΓ : ∀ s, s < s₀ → γ s ∈ germCone ε c := fun s hs => sub_smul_mem_germCone hε y₀ hs
  have hy₀Γ : y₀ ∈ germCone ε c := by
    have := hγΓ 0 hs₀; simpa [γ] using this
  set B : Set (Minkowski d) := Metric.ball y₀ ρ₁ ∩ germCone ε c with hBdef
  have hBo : IsOpen B := Metric.isOpen_ball.inter isOpen_germCone
  let O : Opens M := ⟨κ.source ∩ κ ⁻¹' B, κ.isOpen_inter_preimage hBo⟩
  have hpO : p ∈ O := ⟨mem_chart_source _ p, Metric.mem_ball_self hρ₁, hy₀Γ⟩
  have hOO₁ : (O : Set M) ⊆ O₁ := fun z hz =>
    ⟨hz.1, by rw [hesrc']; trivial, (hρ₁sub hz.2.1).2⟩
  refine ⟨O, φ, hpO, liftPropOn_mono_of_le hO₁ O.isOpen hφ hOO₁, ?_, ?_⟩
  · show κ'.symm (e (κ p)) = q
    rw [← hy₀, hey₀]
    exact κ'.left_inv (mem_chart_source _ q)
  -- rigidity on `A = O ∩ U`
  set A : Set M := (O : Set M) ∩ U with hAdef
  have hAo : IsOpen A := O.isOpen.inter U.isOpen
  set KA : Set (Minkowski d) := B ∩ κ.target ∩ κ.symm ⁻¹' U with hKAdef
  have hAeq : A = κ.symm '' KA := by
    ext z
    constructor
    · rintro ⟨⟨hzs, hzB⟩, hzU⟩
      exact ⟨κ z, ⟨⟨hzB, κ.map_source hzs⟩, by rw [mem_preimage, κ.left_inv hzs]; exact hzU⟩,
        κ.left_inv hzs⟩
    · rintro ⟨y, ⟨⟨hyB, hyt⟩, hyU⟩, rfl⟩
      exact ⟨⟨κ.map_target hyt, by rw [mem_preimage, κ.right_inv hyt]; exact hyB⟩, hyU⟩
  have hstar : ∀ y ∈ KA, ∀ t ∈ Ioc (0 : ℝ) 1, c + t • (y - c) ∈ KA := by
    rintro y ⟨⟨⟨hyb, hyΓ⟩, hyt⟩, hyU⟩ t ht
    have hw : c + t • (y - c) ∈ segment ℝ c y := by
      rw [segment_eq_image']; exact ⟨t, ⟨ht.1.le, ht.2⟩, rfl⟩
    have hwb : c + t • (y - c) ∈ Metric.ball y₀ ρ₁ :=
      (convex_ball y₀ ρ₁).segment_subset hcB₁ hyb hw
    refine ⟨⟨⟨hwb, germCone_add_smul hyΓ ht.1⟩, hball (hB₁ hwb)⟩, ?_⟩
    show κ.symm (c + t • (y - c)) ∈ U
    rcases hε with rfl | rfl
    · obtain ⟨h1, h2⟩ := le_top_of_mem_segment (le_of_mem_germCone_one hyΓ) hw
      exact hconv c (hB₁ hcB₁) _ (hB₁ hwb) y (hB₁ hyb) h1 h2 hcU hyU
    · obtain ⟨h1, h2⟩ := le_top_of_mem_segment (le_of_mem_germCone_neg hyΓ)
        (by rw [segment_symm]; exact hw)
      exact hconv y (hB₁ hyb) _ (hB₁ hwb) c (hB₁ hcB₁) h1 h2 hyU hcU
  have hcnhd : κ.target ∩ κ.symm ⁻¹' U ∈ 𝓝 c :=
    inter_mem (κ.open_target.mem_nhds hct)
      ((κ.continuousAt_symm hct).preimage_mem_nhds (U.isOpen.mem_nhds hcU))
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.1 hcnhd
  set D : Set (Minkowski d) := Metric.ball c δ ∩ B with hDdef
  have hDKA : D ⊆ KA := fun y hy => ⟨⟨hy.2, (hδsub hy.1).1⟩, (hδsub hy.1).2⟩
  have hDconv : Convex ℝ D := (convex_ball c δ).inter ((convex_ball y₀ ρ₁).inter convex_germCone)
  set σ := min δ s₀ / 2 with hσdef
  have hσ : 0 < σ := half_pos (lt_min hδ hs₀)
  have hσδ : σ < δ := (half_lt_self (lt_min hδ hs₀)).trans_le (min_le_left _ _)
  have hσs₀ : σ < s₀ := (half_lt_self (lt_min hδ hs₀)).trans_le (min_le_right _ _)
  set x₀ := γ (s₀ - σ) with hx₀def
  have hx₀B : x₀ ∈ B := by
    refine ⟨?_, hγΓ _ (by linarith)⟩
    rw [Metric.mem_ball, hγdist, abs_of_pos (by linarith)]; linarith
  have hx₀D : x₀ ∈ D := by
    refine ⟨?_, hx₀B⟩
    rw [Metric.mem_ball, hx₀def, hcdef, dist_sub_smul_germVec hε, show s₀ - σ - s₀ = -σ by ring,
      abs_neg, abs_of_pos hσ]
    exact hσδ
  have hKAc : IsPreconnected KA := by
    refine isPreconnected_of_forall x₀ fun y hy => ?_
    have hyc : 0 ≤ dist y c := dist_nonneg
    set τ := min 1 (δ / (2 * (dist y c + 1))) with hτdef
    have hτ0 : 0 < τ := lt_min one_pos (div_pos hδ (by positivity))
    have hτ1 : τ ≤ 1 := min_le_left _ _
    have hwKA : c + τ • (y - c) ∈ KA := hstar y hy τ ⟨hτ0, hτ1⟩
    have hwD : c + τ • (y - c) ∈ D := by
      refine ⟨?_, hwKA.1.1⟩
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hτ0.le,
        ← dist_eq_norm]
      have h1 : τ ≤ δ / (2 * (dist y c + 1)) := min_le_right _ _
      have h2 : τ * dist y c ≤ δ / (2 * (dist y c + 1)) * dist y c :=
        mul_le_mul_of_nonneg_right h1 hyc
      have h3 : δ / (2 * (dist y c + 1)) * dist y c < δ := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith
      linarith
    refine ⟨segment ℝ x₀ (c + τ • (y - c)) ∪ segment ℝ (c + τ • (y - c)) y, ?_,
      Or.inl (left_mem_segment ℝ _ _), Or.inr (right_mem_segment ℝ _ _), ?_⟩
    · refine union_subset ((hDconv.segment_subset hx₀D hwD).trans hDKA) ?_
      rintro _ ⟨a, b, ha, hb, hab, rfl⟩
      have hb' : b = 1 - a := by linarith
      subst hb'
      have key : a • (c + τ • (y - c)) + (1 - a) • y = c + (a * τ + (1 - a)) • (y - c) := by
        simp only [smul_add, smul_sub, add_smul, sub_smul, mul_smul, one_smul]
        abel
      rw [key]
      refine hstar y hy _ ⟨?_, ?_⟩
      · nlinarith
      · nlinarith
    · exact (convex_segment _ _).isPreconnected.union (c + τ • (y - c)) (right_mem_segment ℝ _ _)
        (left_mem_segment ℝ _ _) (convex_segment _ _).isPreconnected
  have hApc : IsPreconnected A := by
    rw [hAeq]
    exact hKAc.image _ (κ.continuousOn_symm.mono fun y hy => hy.1.2)
  have hφA : LiftPropOn (𝔾).IsLocalStructomorphWithinAt φ A :=
    liftPropOn_mono_of_le hO₁ hAo hφ fun z hz => hOO₁ hz.1
  have hψA : LiftPropOn (𝔾).IsLocalStructomorphWithinAt ψ A :=
    liftPropOn_mono_of_le U.isOpen hAo hψ fun z hz => hz.2
  set A₀ : Set M := A ∩ (κ.source ∩ κ ⁻¹' Ω₀) with hA₀def
  have hA₀o : IsOpen A₀ := hAo.inter (κ.isOpen_inter_preimage hΩ₀o)
  have hx₀Ω₀ : x₀ ∈ Ω₀ := hsegΩ₀ ⟨s₀ - σ, ⟨by linarith, by linarith⟩, rfl⟩
  have hx₀t : x₀ ∈ κ.target := (hΩ₀Ω hx₀Ω₀).1
  have hA₀ne : A₀.Nonempty := by
    refine ⟨κ.symm x₀, ⟨⟨κ.map_target hx₀t, ?_⟩, (hΩ₀Ω hx₀Ω₀).2.1⟩, κ.map_target hx₀t, ?_⟩
    · show κ (κ.symm x₀) ∈ B; rw [κ.right_inv hx₀t]; exact hx₀B
    · show κ (κ.symm x₀) ∈ Ω₀; rw [κ.right_inv hx₀t]; exact hx₀Ω₀
  have := eqOn_of_liftPropOn hrig hAo hApc hφA hψA hA₀o inter_subset_left hA₀ne
    fun z hz => hφψ z hz.2.1 hz.2.2
  exact this

/-- **Relations read in a convex chart ball**: in a ball `B(κ x, ρ) ⊆ κ.target` of the chart at
`x`, a relation of `Minkowski d` between two points is one of the generated causality between their
preimages (`chartedCausality_chartIso`, `Form.le_iff_of_convex`). -/
theorem germ_chart_rel {M : Type} [TopologicalSpace M] [ChartedSpace (Minkowski d) M]
    [HasGroupoid M 𝔾] (hGD : ∀ e ∈ 𝔾, ChartIso (minkowski d) (minkowski d) e)
    (hA : ∀ W : Opens (Minkowski d), (minkowski d).AbsolutelyMinimalOn W) (x : M) {ρ : ℝ}
    (hball : Metric.ball (chartAt (Minkowski d) x x) ρ ⊆ (chartAt (Minkowski d) x).target)
    {y z : Minkowski d} (hy : y ∈ Metric.ball (chartAt (Minkowski d) x x) ρ)
    (hz : z ∈ Metric.ball (chartAt (Minkowski d) x x) ρ) :
    ((minkowski d).le ⊤ y z → (chartedCausality (minkowski d) M).le ⊤
        ((chartAt (Minkowski d) x).symm y) ((chartAt (Minkowski d) x).symm z)) ∧
      ((minkowski d).lt ⊤ y z → (chartedCausality (minkowski d) M).lt ⊤
        ((chartAt (Minkowski d) x).symm y) ((chartAt (Minkowski d) x).symm z)) := by
  set κ := chartAt (Minkowski d) x
  have hc := chartedCausality_chartIso (M := M) hGD hA x
  let W₀ : Opens M := ⟨κ.source ∩ κ ⁻¹' Metric.ball (κ x) ρ,
    κ.isOpen_inter_preimage Metric.isOpen_ball⟩
  have hW₀ : W₀ ≤ chartSource κ := fun _ h => h.1
  let Bo : Opens (Minkowski d) := ⟨Metric.ball (κ x) ρ, Metric.isOpen_ball⟩
  have himg : chartImage κ W₀ = Bo := by
    ext w
    simp only [coe_chartImage, SetLike.mem_coe]
    constructor
    · rintro ⟨a, ⟨_, ha⟩, rfl⟩; exact ha.2
    · intro hw
      exact ⟨κ.symm w, ⟨κ.map_target (hball hw), κ.map_target (hball hw), by
        rw [mem_preimage, κ.right_inv (hball hw)]; exact hw⟩, κ.right_inv (hball hw)⟩
  have hmem : ∀ w ∈ Metric.ball (κ x) ρ, κ.symm w ∈ W₀ := fun w hw =>
    ⟨κ.map_target (hball hw), by rw [mem_preimage, κ.right_inv (hball hw)]; exact hw⟩
  have key := hc W₀ hW₀ _ (hmem y hy) _ (hmem z hz)
  rw [himg, κ.right_inv (hball hy), κ.right_inv (hball hz)] at key
  refine ⟨fun h => (chartedCausality (minkowski d) M).le_mono le_top
    (key.1.2 ((le_iff_of_convex (convex_ball _ _)).2 ⟨hy, hz, h⟩)), fun h =>
    (chartedCausality (minkowski d) M).lt_mono le_top
    (key.2.2 ((lt_iff_of_convex (convex_ball _ _)).2 ⟨hy, hz, h⟩))⟩

/-- **The core of A3, flat, one time direction** (`C' = C`, `ε = 1` for the future side;
`C' = C.dual`, `ε = -1` for the past side): Prop 3.7 (`IsCorrPair.exists_lt_forall_mem`) makes `ψ`
converge to `q` along the chart segment below (above) `p`, which lies in `U`
(`mem_of_mem_Jplus_of_lt`, `lem:Sigma_separe` at `p`); then `germ_chart_extend`. -/
theorem germ_core {M N : Type*} [TopologicalSpace M] [TopologicalSpace N] [T2Space N]
    [ChartedSpace (Minkowski d) M] [ChartedSpace (Minkowski d) N] [HasGroupoid M 𝔾]
    [HasGroupoid N 𝔾]
    (hrig : ∀ e ∈ 𝔾, ∀ e' ∈ 𝔾, ∀ U : Set (Minkowski d), IsOpen U → IsPreconnected U →
      U ⊆ e.source → U ⊆ e'.source → ∀ O ⊆ U, IsOpen O → O.Nonempty → EqOn e e' O → EqOn e e' U)
    (hreg : ∀ W : Set (Minkowski d), IsOpen W → IsConnected W → ∀ f : Minkowski d → Minkowski d,
      (∀ y ∈ W, (𝔾).IsLocalStructomorphWithinAt f W y) → InjOn f W →
      ∃ e ∈ 𝔾, (∀ y ∈ W, connectedComponent y ⊆ e.source) ∧ EqOn f e W)
    {C' : Causality M} {D' : Causality N} (U : Opens M) {V : Opens N} {ψ : M → N} {g : N → M}
    (hψ : LiftPropOn (𝔾).IsLocalStructomorphWithinAt ψ U) (hinj : InjOn ψ U)
    (hcorr : IsCorrPair C' D' U V ψ g) (hcvU : C'.CausallyConvexIn (U : Set M) ⊤)
    (hcvV : D'.CausallyConvexIn (V : Set N) ⊤) (hGN : D'.GloballyHyperbolic) (hTN : D'.Tarentin)
    (hZM : ∀ x, x ∈ C'.Zminus) (hZN : ∀ y, y ∈ D'.Zminus) (hPM : C'.PushUp) (hPN : D'.PushUp)
    (hclM : ∀ x, IsClosed (C'.Jplus ⊤ {x})) (hclN : ∀ y, IsClosed (D'.Jplus ⊤ {y}))
    {S : Set M} (hSU : S ⊆ U) {p : M} {q : N} (hc : Corresponds (U : Set M) ψ p q)
    (hsepM : C'.Jplus ⊤ S ∈ 𝓝 p) (hsepN : D'.Jplus ⊤ (ψ '' S) ∈ 𝓝 q)
    {ε : ℝ} (hε : ε = 1 ∨ ε = -1) {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀)
    (hball : Metric.ball (chartAt (Minkowski d) p p) ρ₀ ⊆ (chartAt (Minkowski d) p).target)
    (hseglt : ∀ s ∈ Ioo 0 ρ₀,
      C'.lt ⊤ ((chartAt (Minkowski d) p).symm (chartAt (Minkowski d) p p - s • germVec d ε)) p)
    (hconv : ∀ y ∈ Metric.ball (chartAt (Minkowski d) p p) ρ₀,
      ∀ w ∈ Metric.ball (chartAt (Minkowski d) p p) ρ₀,
      ∀ z ∈ Metric.ball (chartAt (Minkowski d) p p) ρ₀,
      (minkowski d).le ⊤ y w → (minkowski d).le ⊤ w z → (chartAt (Minkowski d) p).symm y ∈ U →
        (chartAt (Minkowski d) p).symm z ∈ U → (chartAt (Minkowski d) p).symm w ∈ U) :
    ∃ (O : Opens M) (φ : M → N), p ∈ O ∧ LiftPropOn (𝔾).IsLocalStructomorphWithinAt φ O ∧
      φ p = q ∧ EqOn φ ψ (O ⊓ U : Opens M) := by
  set κ := chartAt (Minkowski d) p with hκdef
  have hpcl : p ∈ closure (U : Set M) := mem_closure_of_corresponds hc
  have hκp : κ p ∈ κ.target := κ.map_source (mem_chart_source _ p)
  have hκs : ContinuousAt κ.symm (κ p) := κ.continuousAt_symm hκp
  have hnhd : κ.symm ⁻¹' (C'.Jplus ⊤ S) ∈ 𝓝 (κ p) :=
    hκs.preimage_mem_nhds (by rw [κ.left_inv (mem_chart_source _ p)]; exact hsepM)
  obtain ⟨ρ₁, hρ₁, hsub⟩ := Metric.mem_nhds_iff.1 hnhd
  set ρ := min ρ₀ ρ₁ with hρdef
  have hρ : 0 < ρ := lt_min hρ₀ hρ₁
  have hρρ₀ : Metric.ball (κ p) ρ ⊆ Metric.ball (κ p) ρ₀ := Metric.ball_subset_ball (min_le_left _ _)
  have hρρ₁ : Metric.ball (κ p) ρ ⊆ Metric.ball (κ p) ρ₁ := Metric.ball_subset_ball (min_le_right _ _)
  have hγb : ∀ s ∈ Ioo 0 ρ, κ p - s • germVec d ε ∈ Metric.ball (κ p) ρ := fun s hs => by
    rw [Metric.mem_ball, dist_sub_smul_germVec_self hε, abs_of_pos hs.1]; exact hs.2
  have hIoo : ∀ s ∈ Ioo 0 ρ, s ∈ Ioo 0 ρ₀ := fun s hs => ⟨hs.1, hs.2.trans_le (min_le_left _ _)⟩
  have hseg : ∀ s ∈ Ioo 0 ρ, κ.symm (κ p - s • germVec d ε) ∈ U := fun s hs =>
    mem_of_mem_Jplus_of_lt hcvU hSU hpcl (hsub (hρρ₁ (hγb s hs))) (hseglt s (hIoo s hs))
  have hxs : Tendsto (fun s : ℝ => κ.symm (κ p - s • germVec d ε)) (𝓝[>] 0) (𝓝 p) := by
    have h1 : Tendsto (fun s : ℝ => κ p - s • germVec d ε) (𝓝 0) (𝓝 (κ p)) := by
      simpa using ((continuous_const.sub (continuous_id.smul continuous_const)).tendsto (0 : ℝ) :
        Tendsto (fun s : ℝ => κ p - s • germVec d ε) (𝓝 0) (𝓝 (κ p - (0 : ℝ) • germVec d ε)))
    have h2 := hκs.tendsto.comp (h1.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ))))
    rwa [κ.left_inv (mem_chart_source _ p)] at h2
  have hTV : ψ '' S ⊆ V := (hcorr.mapsTo.mono_left hSU).image_subset
  have hlim : Tendsto (fun s : ℝ => ψ (κ.symm (κ p - s • germVec d ε))) (𝓝[>] 0) (𝓝 q) := by
    intro V' hV'
    obtain ⟨x₀, -, hx₀p, hx₀⟩ := hcorr.exists_lt_forall_mem hcvU hcvV hGN hTN (hZM p) (hZN q)
      hPM hPN hclM hclN hTV hsepN hc hV'
    refine Filter.mem_map.2 ?_
    filter_upwards [hxs (Causality.isOpen_Iplus.mem_nhds
      (show p ∈ C'.Iplus ⊤ {x₀} by simpa using hx₀p)), Ioo_mem_nhdsGT hρ] with s hs1 hs2
    exact hx₀ _ (hseg s hs2) (by simpa using hs1) (hseglt s (hIoo s hs2))
  exact germ_chart_extend hrig hreg U hψ hinj hε hρ (hρρ₀.trans hball) hseg hlim
    fun y hy w hw z hz => hconv y (hρρ₀ hy) w (hρρ₀ hw) z (hρρ₀ hz)

section Assembly

variable {M N : Type} [TopologicalSpace M] [TopologicalSpace N] [ChartedSpace (Minkowski d) M]
  [ChartedSpace (Minkowski d) N] [HasGroupoid M (gxGroupoid (isom d) (Minkowski d))]
  [HasGroupoid N (gxGroupoid (isom d) (Minkowski d))]

/-- **The CGHD setting of A3 read on a flat atlas** (`CGHDData.isCorrPair`, `causallyConvexIn`,
`causallyConvexIn'`, here without a `Geometry`): `U`, `ψ(U)` causally convex, and `ψ : U → ψ(U)`
matching the relations of `M` and `N`. -/
theorem germ_isCorrPair [T2Space M] [T2Space N] [Nonempty M]
    (hGD : ∀ e ∈ 𝔾, ChartIso (minkowski d) (minkowski d) e)
    (hAm : ∀ W : Opens (Minkowski d), (minkowski d).AbsolutelyMinimalOn W)
    (hCM : (chartedCausality (minkowski d) M).CausallyArcConnected)
    (hCN : (chartedCausality (minkowski d) N).CausallyArcConnected)
    (hextM : (chartedCausality (minkowski d) M).CurvesExtend)
    (hextN : (chartedCausality (minkowski d) N).CurvesExtend)
    (U : Opens M) {ψ : M → N} {S : Set M} (hψ : LiftPropOn (𝔾).IsLocalStructomorphWithinAt ψ U)
    (hinj : InjOn ψ U) (hGM : (chartedCausality (minkowski d) M).GloballyHyperbolic)
    (hGN : (chartedCausality (minkowski d) N).GloballyHyperbolic)
    (hGU : (chartedCausality (minkowski d) M).GloballyHyperbolicOn U)
    (hGV : (chartedCausality (minkowski d) N).GloballyHyperbolicOn
      ((isEMorphismOn_of_liftPropOn hGD hAm hψ).imageOpens U le_rfl))
    (hSU : S ⊆ U) (hS : (chartedCausality (minkowski d) M).IsCauchySurface S)
    (hSU' : (chartedCausality (minkowski d) M).IsCauchySurfaceOn U S)
    (hψS : (chartedCausality (minkowski d) N).IsCauchySurface (ψ '' S))
    (hψSV : (chartedCausality (minkowski d) N).IsCauchySurfaceOn
      ((isEMorphismOn_of_liftPropOn hGD hAm hψ).imageOpens U le_rfl) (ψ '' S)) :
    (chartedCausality (minkowski d) M).CausallyConvexIn (U : Set M) ⊤ ∧
      (chartedCausality (minkowski d) N).CausallyConvexIn
        ((isEMorphismOn_of_liftPropOn hGD hAm hψ).imageOpens U le_rfl : Set N) ⊤ ∧
      IsCorrPair (chartedCausality (minkowski d) M) (chartedCausality (minkowski d) N) U
        ((isEMorphismOn_of_liftPropOn hGD hAm hψ).imageOpens U le_rfl) ψ (invFunOn ψ U) := by
  set C := chartedCausality (minkowski d) M
  set D := chartedCausality (minkowski d) N
  have hE := isEMorphismOn_of_liftPropOn hGD hAm hψ
  set V := hE.imageOpens U le_rfl with hVdef
  have hE' : IsEMorphismOn D C V (invFunOn ψ U) :=
    isEMorphismOn_of_liftPropOn hGD hAm (W := V) (liftPropOn_invFunOn U.isOpen hψ hinj)
  have hcvU : C.CausallyConvexIn (U : Set M) ⊤ :=
    IsCauchyInclusion.causallyConvexIn ⟨le_top, hGU, hGM, S, hSU, hSU', hS⟩ hCM
      (Causality.curvesExtendOn_top.2 hextM)
  have hcvV : D.CausallyConvexIn (V : Set N) ⊤ :=
    IsCauchyInclusion.causallyConvexIn ⟨le_top, hGV, hGN, ψ '' S, image_mono hSU, hψSV, hψS⟩ hCN
      (Causality.curvesExtendOn_top.2 hextN)
  have hl := hinj.leftInvOn_invFunOn
  have hmaps : MapsTo ψ U V := fun z hz => ⟨z, hz, rfl⟩
  refine ⟨hcvU, hcvV,
    { mapsTo := hmaps
      mapsTo_inv := fun y hy => invFunOn_mem hy
      leftInvOn := hl
      rightInvOn := fun y hy => invFunOn_eq hy
      continuousOn := hE.continuousOn
      continuousOn_inv := hE'.continuousOn
      le_iff := fun x hx y hy => ⟨fun hxy => ?_, fun hxy => ?_⟩
      lt_iff := fun x hx y hy => ⟨fun hxy => ?_, fun hxy => ?_⟩ }⟩
  · exact D.le_mono le_top (hE.map_le U V le_rfl hmaps
      (Causality.le_of_causallyConvexIn_of_le hCM hcvU subset_rfl le_top hx hy hxy))
  · have hV' := Causality.le_of_causallyConvexIn_of_le hCN hcvV subset_rfl le_top (hmaps hx)
      (hmaps hy) hxy
    have := hE'.map_le V ⊤ le_rfl (fun _ _ => trivial) hV'
    rwa [hl hx, hl hy] at this
  · exact D.lt_mono le_top (hE.map_lt U V le_rfl hmaps
      (Causality.lt_of_causallyConvexIn hCM hcvU hx hy hxy))
  · have hV' := Causality.lt_of_causallyConvexIn hCN hcvV (hmaps hx) (hmaps hy) hxy
    have := hE'.map_lt V ⊤ le_rfl (fun _ _ => trivial) hV'
    rwa [hl hx, hl hy] at this

/-- **A3 future for a flat atlas** (Sbierski Lemma 3.8 at a boundary point in the future of `Σ`):
the hypotheses of `LocalModel.GermExtFuture` on flat atlases, the model facts (B1 `hrig`, B2
`hreg`, B3 `hGD`, `hAm`, `hAxM`/`hAxN`, `hextM`/`hextN`, the past compactness `hcptM`/`hcptN`)
named. -/
theorem flat_germ_future [T2Space M] [T2Space N]
    (hrig : ∀ e ∈ 𝔾, ∀ e' ∈ 𝔾, ∀ U : Set (Minkowski d), IsOpen U → IsPreconnected U →
      U ⊆ e.source → U ⊆ e'.source → ∀ O ⊆ U, IsOpen O → O.Nonempty → EqOn e e' O → EqOn e e' U)
    (hreg : ∀ W : Set (Minkowski d), IsOpen W → IsConnected W → ∀ f : Minkowski d → Minkowski d,
      (∀ y ∈ W, (𝔾).IsLocalStructomorphWithinAt f W y) → InjOn f W →
      ∃ e ∈ 𝔾, (∀ y ∈ W, connectedComponent y ⊆ e.source) ∧ EqOn f e W)
    (hGD : ∀ e ∈ 𝔾, ChartIso (minkowski d) (minkowski d) e)
    (hAm : ∀ W : Opens (Minkowski d), (minkowski d).AbsolutelyMinimalOn W)
    (hAxM : (chartedCausality (minkowski d) M).SingularFlatAxiomsCorr
      (chartedSing (fun _ => (∅ : Set (Minkowski d))) M))
    (hAxN : (chartedCausality (minkowski d) N).SingularFlatAxiomsCorr
      (chartedSing (fun _ => (∅ : Set (Minkowski d))) N))
    (hextM : (chartedCausality (minkowski d) M).CurvesExtend)
    (hextN : (chartedCausality (minkowski d) N).CurvesExtend)
    (hcptM : ∀ S : Set M, (chartedCausality (minkowski d) M).IsCauchySurface S → ∀ x : M,
      IsCompact ((chartedCausality (minkowski d) M).Jminus ⊤ S ∩
        (chartedCausality (minkowski d) M).Jplus ⊤ {x}))
    (hcptN : ∀ S : Set N, (chartedCausality (minkowski d) N).IsCauchySurface S → ∀ x : N,
      IsCompact ((chartedCausality (minkowski d) N).Jminus ⊤ S ∩
        (chartedCausality (minkowski d) N).Jplus ⊤ {x}))
    (U : Opens M) (ψ : M → N) (S : Set M) (hψ : LiftPropOn (𝔾).IsLocalStructomorphWithinAt ψ U)
    (hinj : InjOn ψ U) (hGM : (chartedCausality (minkowski d) M).GloballyHyperbolic)
    (hGN : (chartedCausality (minkowski d) N).GloballyHyperbolic)
    (hGU : (chartedCausality (minkowski d) M).GloballyHyperbolicOn U)
    (hGV : (chartedCausality (minkowski d) N).GloballyHyperbolicOn
      ((isEMorphismOn_of_liftPropOn hGD hAm hψ).imageOpens U le_rfl))
    (hSU : S ⊆ U) (hS : (chartedCausality (minkowski d) M).IsCauchySurface S)
    (hSU' : (chartedCausality (minkowski d) M).IsCauchySurfaceOn U S)
    (hψS : (chartedCausality (minkowski d) N).IsCauchySurface (ψ '' S))
    (hψSV : (chartedCausality (minkowski d) N).IsCauchySurfaceOn
      ((isEMorphismOn_of_liftPropOn hGD hAm hψ).imageOpens U le_rfl) (ψ '' S))
    (p : M) (q : N) (hp : p ∈ frontier (U : Set M))
    (hpS : p ∈ (chartedCausality (minkowski d) M).Jplus ⊤ S)
    (hcl : MapClusterPt q (𝓝[(U : Set M)] p) ψ) :
    ∃ (O : Opens M) (φ : M → N), p ∈ O ∧ LiftPropOn (𝔾).IsLocalStructomorphWithinAt φ O ∧
      φ p = q ∧ EqOn φ ψ (O ⊓ U : Opens M) := by
  set C := chartedCausality (minkowski d) M
  set D := chartedCausality (minkowski d) N
  haveI := hAxM.secondCountable
  haveI := hAxN.secondCountable
  haveI : Nonempty M := ⟨p⟩
  obtain ⟨hcvU, hcvV, hcorr⟩ := germ_isCorrPair hGD hAm hAxM.causallyArcConnected
    hAxN.causallyArcConnected hextM hextN U hψ hinj hGM hGN hGU hGV hSU hS hSU' hψS hψSV
  set V := (isEMorphismOn_of_liftPropOn hGD hAm hψ).imageOpens U le_rfl with hVdef
  have hc : Corresponds (U : Set M) ψ p q := corresponds_iff_mapClusterPt.2 hcl
  have hZM : ∀ x, x ∈ C.Zminus := fun x => (hAxM.mem_Zminus_iff x).2 (by simp [chartedSing])
  have hZN : ∀ y, y ∈ D.Zminus := fun y => (hAxN.mem_Zminus_iff y).2 (by simp [chartedSing])
  have hclM := hGM.isClosed_Jplus_singleton hAxM.tarentin
  have hclN := hGN.isClosed_Jplus_singleton hAxN.tarentin
  have hpU : p ∉ (U : Set M) := by rw [U.isOpen.frontier_eq] at hp; exact hp.2
  have hsepM : C.Jplus ⊤ S ∈ 𝓝 p :=
    Causality.Jplus_mem_nhds_of_isCauchySurface hGM.1 hAxM.causallyArcConnected hextM hS
      (fun x => (hAxM.K_densite_sing x).2) (hcptM S hS) ⟨hpS, fun h => hpU (hSU h)⟩
  have hqfr := hcorr.mem_frontier_of_corresponds hp hc
  have hqV : q ∉ (V : Set N) := by rw [V.isOpen.frontier_eq] at hqfr; exact hqfr.2
  have hqS := hcorr.mem_Jplus_of_corresponds hcvU (hZM p) hAxN.pushUp hclN hc hqV hGM.1 hGN.1
    (hS.isAcausal hAxM.causallyArcConnected hextM) hSU hsepM
    (Causality.mem_Jplus_union_Jminus_of_isCauchySurface hextN hψS q)
  have hsepN : D.Jplus ⊤ (ψ '' S) ∈ 𝓝 q :=
    Causality.Jplus_mem_nhds_of_isCauchySurface hGN.1 hAxN.causallyArcConnected hextN hψS
      (fun x => (hAxN.K_densite_sing x).2) (hcptN _ hψS)
      ⟨hqS, fun h => hqV ((hcorr.mapsTo.mono_left hSU).image_subset h)⟩
  set κ := chartAt (Minkowski d) p with hκdef
  have hκp : κ p ∈ κ.target := κ.map_source (mem_chart_source _ p)
  obtain ⟨ρ₀, hρ₀, hball⟩ := Metric.mem_nhds_iff.1 (κ.open_target.mem_nhds hκp)
  have hseglt : ∀ s ∈ Ioo 0 ρ₀, C.lt ⊤ (κ.symm (κ p - s • germVec d 1)) p := by
    intro s hs
    have hy : κ p - s • germVec d 1 ∈ Metric.ball (κ p) ρ₀ := by
      rw [Metric.mem_ball, dist_sub_smul_germVec_self (Or.inl rfl), abs_of_pos hs.1]; exact hs.2
    have hM : (minkowski d).lt ⊤ (κ p - s • germVec d 1) (κ p) := by
      rw [minkowski_lt_top_iff]; simp [germVec, hs.1]
    have := (germ_chart_rel hGD hAm p hball hy (Metric.mem_ball_self hρ₀)).2 hM
    rwa [κ.left_inv (mem_chart_source _ p)] at this
  refine germ_core hrig hreg U hψ hinj hcorr hcvU hcvV hGN hAxN.tarentin hZM hZN hAxM.pushUp
    hAxN.pushUp hclM hclN hSU hc hsepM hsepN (Or.inl rfl) hρ₀ hball hseglt ?_
  intro y hy w hw z hz h1 h2 hyU hzU
  exact hcvU.2 _ hyU _ hzU (Causality.mem_diamond.2
    ⟨(germ_chart_rel hGD hAm p hball hy hw).1 h1, (germ_chart_rel hGD hAm p hball hw hz).1 h2⟩)

/-- **A3 past for a flat atlas** (Sbierski Lemma 3.8 at a boundary point in the past of `Σ`; no
time reversal of the model is used: the past side is `germ_core` for `C.dual`, `D.dual` with
`ε = -1` in the chart, the future compactness `hcptM`/`hcptN` and `K⁺` density). -/
theorem flat_germ_past [T2Space M] [T2Space N]
    (hrig : ∀ e ∈ 𝔾, ∀ e' ∈ 𝔾, ∀ U : Set (Minkowski d), IsOpen U → IsPreconnected U →
      U ⊆ e.source → U ⊆ e'.source → ∀ O ⊆ U, IsOpen O → O.Nonempty → EqOn e e' O → EqOn e e' U)
    (hreg : ∀ W : Set (Minkowski d), IsOpen W → IsConnected W → ∀ f : Minkowski d → Minkowski d,
      (∀ y ∈ W, (𝔾).IsLocalStructomorphWithinAt f W y) → InjOn f W →
      ∃ e ∈ 𝔾, (∀ y ∈ W, connectedComponent y ⊆ e.source) ∧ EqOn f e W)
    (hGD : ∀ e ∈ 𝔾, ChartIso (minkowski d) (minkowski d) e)
    (hAm : ∀ W : Opens (Minkowski d), (minkowski d).AbsolutelyMinimalOn W)
    (hAxM : (chartedCausality (minkowski d) M).SingularFlatAxiomsCorr
      (chartedSing (fun _ => (∅ : Set (Minkowski d))) M))
    (hAxN : (chartedCausality (minkowski d) N).SingularFlatAxiomsCorr
      (chartedSing (fun _ => (∅ : Set (Minkowski d))) N))
    (hextM : (chartedCausality (minkowski d) M).CurvesExtend)
    (hextN : (chartedCausality (minkowski d) N).CurvesExtend)
    (hcptM : ∀ S : Set M, (chartedCausality (minkowski d) M).IsCauchySurface S → ∀ x : M,
      IsCompact ((chartedCausality (minkowski d) M).Jplus ⊤ S ∩
        (chartedCausality (minkowski d) M).Jminus ⊤ {x}))
    (hcptN : ∀ S : Set N, (chartedCausality (minkowski d) N).IsCauchySurface S → ∀ x : N,
      IsCompact ((chartedCausality (minkowski d) N).Jplus ⊤ S ∩
        (chartedCausality (minkowski d) N).Jminus ⊤ {x}))
    (U : Opens M) (ψ : M → N) (S : Set M) (hψ : LiftPropOn (𝔾).IsLocalStructomorphWithinAt ψ U)
    (hinj : InjOn ψ U) (hGM : (chartedCausality (minkowski d) M).GloballyHyperbolic)
    (hGN : (chartedCausality (minkowski d) N).GloballyHyperbolic)
    (hGU : (chartedCausality (minkowski d) M).GloballyHyperbolicOn U)
    (hGV : (chartedCausality (minkowski d) N).GloballyHyperbolicOn
      ((isEMorphismOn_of_liftPropOn hGD hAm hψ).imageOpens U le_rfl))
    (hSU : S ⊆ U) (hS : (chartedCausality (minkowski d) M).IsCauchySurface S)
    (hSU' : (chartedCausality (minkowski d) M).IsCauchySurfaceOn U S)
    (hψS : (chartedCausality (minkowski d) N).IsCauchySurface (ψ '' S))
    (hψSV : (chartedCausality (minkowski d) N).IsCauchySurfaceOn
      ((isEMorphismOn_of_liftPropOn hGD hAm hψ).imageOpens U le_rfl) (ψ '' S))
    (p : M) (q : N) (hp : p ∈ frontier (U : Set M))
    (hpS : p ∈ (chartedCausality (minkowski d) M).Jminus ⊤ S)
    (hcl : MapClusterPt q (𝓝[(U : Set M)] p) ψ) :
    ∃ (O : Opens M) (φ : M → N), p ∈ O ∧ LiftPropOn (𝔾).IsLocalStructomorphWithinAt φ O ∧
      φ p = q ∧ EqOn φ ψ (O ⊓ U : Opens M) := by
  set C := chartedCausality (minkowski d) M
  set D := chartedCausality (minkowski d) N
  haveI := hAxM.secondCountable
  haveI := hAxN.secondCountable
  haveI : Nonempty M := ⟨p⟩
  obtain ⟨hcvU, hcvV, hcorr⟩ := germ_isCorrPair hGD hAm hAxM.causallyArcConnected
    hAxN.causallyArcConnected hextM hextN U hψ hinj hGM hGN hGU hGV hSU hS hSU' hψS hψSV
  set V := (isEMorphismOn_of_liftPropOn hGD hAm hψ).imageOpens U le_rfl with hVdef
  have hc : Corresponds (U : Set M) ψ p q := corresponds_iff_mapClusterPt.2 hcl
  have hcorr' := hcorr.dual
  have hcvU' : C.dual.CausallyConvexIn (U : Set M) ⊤ := Causality.dual_causallyConvexIn.2 hcvU
  have hcvV' : D.dual.CausallyConvexIn (V : Set N) ⊤ := Causality.dual_causallyConvexIn.2 hcvV
  have hZM : ∀ x, x ∈ C.dual.Zminus := fun x => hAxM.mem_Zplus x
  have hZN : ∀ y, y ∈ D.dual.Zminus := fun y => hAxN.mem_Zplus y
  have hPM : C.dual.PushUp := Causality.dual_pushUp.2 hAxM.pushUp
  have hPN : D.dual.PushUp := Causality.dual_pushUp.2 hAxN.pushUp
  have hclM : ∀ x, IsClosed (C.dual.Jplus ⊤ {x}) := hGM.isClosed_Jminus_singleton hAxM.tarentin
  have hclN : ∀ y, IsClosed (D.dual.Jplus ⊤ {y}) := hGN.isClosed_Jminus_singleton hAxN.tarentin
  have hpU : p ∉ (U : Set M) := by rw [U.isOpen.frontier_eq] at hp; exact hp.2
  have hsepM : C.dual.Jplus ⊤ S ∈ 𝓝 p :=
    Causality.Jminus_mem_nhds_of_isCauchySurface hGM.1 hAxM.causallyArcConnected hextM hS
      (fun x => (hAxM.K_densite_sing x).1) (hcptM S hS) ⟨hpS, fun h => hpU (hSU h)⟩
  have hqfr := hcorr.mem_frontier_of_corresponds hp hc
  have hqV : q ∉ (V : Set N) := by rw [V.isOpen.frontier_eq] at hqfr; exact hqfr.2
  have hqS : q ∈ D.dual.Jplus ⊤ (ψ '' S) := hcorr'.mem_Jplus_of_corresponds hcvU' (hZM p) hPN
    hclN hc hqV (Causality.dual_isCausal.2 hGM.1) (Causality.dual_isCausal.2 hGN.1)
    (Causality.dual_isAcausal.2 (hS.isAcausal hAxM.causallyArcConnected hextM)) hSU hsepM
    (Causality.mem_Jplus_union_Jminus_of_isCauchySurface hextN hψS q).symm
  have hsepN : D.dual.Jplus ⊤ (ψ '' S) ∈ 𝓝 q :=
    Causality.Jminus_mem_nhds_of_isCauchySurface hGN.1 hAxN.causallyArcConnected hextN hψS
      (fun x => (hAxN.K_densite_sing x).1) (hcptN _ hψS)
      ⟨hqS, fun h => hqV ((hcorr.mapsTo.mono_left hSU).image_subset h)⟩
  set κ := chartAt (Minkowski d) p with hκdef
  have hκp : κ p ∈ κ.target := κ.map_source (mem_chart_source _ p)
  obtain ⟨ρ₀, hρ₀, hball⟩ := Metric.mem_nhds_iff.1 (κ.open_target.mem_nhds hκp)
  have hseglt : ∀ s ∈ Ioo 0 ρ₀, C.dual.lt ⊤ (κ.symm (κ p - s • germVec d (-1))) p := by
    intro s hs
    have hy : κ p - s • germVec d (-1) ∈ Metric.ball (κ p) ρ₀ := by
      rw [Metric.mem_ball, dist_sub_smul_germVec_self (Or.inr rfl), abs_of_pos hs.1]; exact hs.2
    have hM : (minkowski d).lt ⊤ (κ p) (κ p - s • germVec d (-1)) := by
      rw [minkowski_lt_top_iff]; simp [germVec, hs.1]
    have := (germ_chart_rel hGD hAm p hball (Metric.mem_ball_self hρ₀) hy).2 hM
    rw [κ.left_inv (mem_chart_source _ p)] at this
    exact this
  refine germ_core hrig hreg U hψ hinj hcorr' hcvU' hcvV'
    (Causality.dual_globallyHyperbolic.2 hGN) (Causality.dual_tarentin.2 hAxN.tarentin) hZM hZN
    hPM hPN hclM hclN hSU hc hsepM hsepN (Or.inr rfl) hρ₀ hball hseglt ?_
  intro y hy w hw z hz h1 h2 hyU hzU
  exact hcvU.2 _ hyU _ hzU (Causality.mem_diamond.2
    ⟨(germ_chart_rel hGD hAm p hball hy hw).1 h1, (germ_chart_rel hGD hAm p hball hw hz).1 h2⟩)

end Assembly

end Chart

/-! ### A3 for the flat local model, in the Level-A form -/

section Model

/-- The B2 field of a flat model (`singY = ∅`) without its vacuous regularity clauses. -/
theorem germ_hreg_of_localUnique_reg {d : ℕ}
    (lur : ∀ U : Set (Minkowski d), IsOpen U → IsConnected U →
      (∀ y ∈ U, ∀ z ∈ connectedComponent y, ∀ α : ℝ, 0 ≤ α →
        z ∉ (fun _ : ℝ => (∅ : Set (Minkowski d))) α) →
      ∀ f : Minkowski d → Minkowski d,
      (∀ y ∈ U, (gxGroupoid (isom d) (Minkowski d)).IsLocalStructomorphWithinAt f U y) →
      InjOn f U → MapsTo f U {z | ∀ w ∈ connectedComponent z, ∀ α : ℝ, 0 ≤ α →
        w ∉ (fun _ : ℝ => (∅ : Set (Minkowski d))) α} →
      ∃ e ∈ gxGroupoid (isom d) (Minkowski d), (∀ y ∈ U, connectedComponent y ⊆ e.source) ∧
        EqOn f e U) :
    ∀ W : Set (Minkowski d), IsOpen W → IsConnected W → ∀ f : Minkowski d → Minkowski d,
      (∀ y ∈ W, (gxGroupoid (isom d) (Minkowski d)).IsLocalStructomorphWithinAt f W y) →
      InjOn f W → ∃ e ∈ gxGroupoid (isom d) (Minkowski d),
        (∀ y ∈ W, connectedComponent y ⊆ e.source) ∧ EqOn f e W :=
  fun W hW hWc f hf hinj => lur W hW hWc (fun _ _ _ _ _ _ => notMem_empty _) f hf hinj
    fun _ _ _ _ _ _ => notMem_empty _

/-- **A3 future for the flat local model** (Sbierski Lemma 3.8, regular case): every local model
whose data are those of the flat one — `Y = Minkowski d`, its topology, `G` the isometry groupoid,
`causalityY = minkowski d`, `singY = ∅` (the five `HEq`s, each `HEq.rfl` for `flatModelOf`) —
satisfies `LocalModel.GermExtFuture`. Only `𝔐`'s own fields are used (B1 `rigid`, B2
`localUnique_reg`, B3 `chartIso_mem`, `absolutelyMinimalOn_Y`, `singularFlatAxioms`,
`curvesExtend`, `isCompact_Jminus_inter_Jplus`), with second countability from
`flat_secondCountableTopology`. Integrator: `flat_germExtFuture (flatModelOf d hJ₁ hJ₂) rfl
HEq.rfl HEq.rfl HEq.rfl HEq.rfl : (flatModelOf d hJ₁ hJ₂).GermExtFuture`. -/
theorem flat_germExtFuture {d : ℕ} (𝔐 : LocalModel.{0}) (hY : 𝔐.Y = Minkowski d)
    (htop : HEq 𝔐.topY (inferInstance : TopologicalSpace (Minkowski d)))
    (hG : HEq 𝔐.G (gxGroupoid (isom d) (Minkowski d)))
    (hC : HEq 𝔐.causalityY (minkowski d))
    (hsing : HEq 𝔐.singY (fun _ : ℝ => (∅ : Set (Minkowski d)))) : 𝔐.GermExtFuture := by
  revert hY htop hG hC hsing
  obtain ⟨Y, G, causalityY, singY, rigid, -, -, lur, -, amY, cim, -, sfa, ce, -, -, ic2, -, -,
    -⟩ := 𝔐
  intro hY htop hG hC hsing
  dsimp only at hY htop hG hC hsing
  subst hY
  cases htop
  cases hG
  cases hC
  cases hsing
  intro M N _ _ _ _ _ _ s t U ψ S h hinj hGM hGN hGU hGV hSU hS hSU' hψS hψSV p q hp hpS hcl
  obtain ⟨cs, hgs⟩ := s
  obtain ⟨ct, hgt⟩ := t
  haveI := flat_secondCountableTopology (d := d) M
  haveI := flat_secondCountableTopology (d := d) N
  exact flat_germ_future rigid (germ_hreg_of_localUnique_reg lur) cim amY sfa sfa (ce hGM)
    (ce hGN) (ic2 hGM) (ic2 hGN) U ψ S h hinj hGM hGN hGU hGV hSU hS hSU' hψS hψSV p q hp hpS hcl

/-- **A3 past for the flat local model** (Sbierski Lemma 3.8, regular case, in the past of `Σ`):
as `flat_germExtFuture`, with `isCompact_Jplus_inter_Jminus`. Integrator: `flat_germExtPast
(flatModelOf d hJ₁ hJ₂) rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl : (flatModelOf d hJ₁ hJ₂).GermExtPast`. -/
theorem flat_germExtPast {d : ℕ} (𝔐 : LocalModel.{0}) (hY : 𝔐.Y = Minkowski d)
    (htop : HEq 𝔐.topY (inferInstance : TopologicalSpace (Minkowski d)))
    (hG : HEq 𝔐.G (gxGroupoid (isom d) (Minkowski d)))
    (hC : HEq 𝔐.causalityY (minkowski d))
    (hsing : HEq 𝔐.singY (fun _ : ℝ => (∅ : Set (Minkowski d)))) : 𝔐.GermExtPast := by
  revert hY htop hG hC hsing
  obtain ⟨Y, G, causalityY, singY, rigid, -, -, lur, -, amY, cim, -, sfa, ce, -, ic1, -, -, -,
    -⟩ := 𝔐
  intro hY htop hG hC hsing
  dsimp only at hY htop hG hC hsing
  subst hY
  cases htop
  cases hG
  cases hC
  cases hsing
  intro M N _ _ _ _ _ _ s t U ψ S h hinj hGM hGN hGU hGV hSU hS hSU' hψS hψSV p q hp hpS hcl
  obtain ⟨cs, hgs⟩ := s
  obtain ⟨ct, hgt⟩ := t
  haveI := flat_secondCountableTopology (d := d) M
  haveI := flat_secondCountableTopology (d := d) N
  exact flat_germ_past rigid (germ_hreg_of_localUnique_reg lur) cim amY sfa sfa (ce hGM)
    (ce hGN) (ic1 hGM) (ic1 hGN) U ψ S h hinj hGM hGN hGU hGV hSU hS hSU' hψS hψSV p q hp hpS hcl

end Model

end CBG

end Causal
