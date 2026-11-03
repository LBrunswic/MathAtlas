import GX.BTZ.Manifolds

/-!
# `GX.BTZ.LiftGH` — `M` globally hyperbolic ⇒ `\widetilde M` globally hyperbolic (natural topology)

Package WP-46d (round 1, after `AUDIT-1.json`). `papers/gx` §4.5 (`RamcovGX.tex:2325–2361`).
Rulings: DEC-106 (`\widetilde M` carries its natural Fox-completion topology for causality and
GH), **DEC-118** (a) FD read for the chart-generated `≪` (`BTZTildeData.causality`), (b) "`M` GH ⇒
`\widetilde M` GH" in the natural topology is this package, (c) the chartwise `\widetilde M` and
D-10 accepted; DEC-33 (Causal.*). **0 `sorry`.**

* **`lem:globally_hyperbolic_manifolds_manifolds`** (l.2325) — certificate in `GX.BTZ.Manifolds`
  (`GX.e0SingManifold_isFutureDistinguishing`, `GX.e0Manifold_isFutureDistinguishing`,
  `GX.BTZTildeData.isFutureDistinguishing_of_natGloballyHyperbolic`); this file discharges the
  `\widetilde{BTZ}` half's hypothesis for every globally hyperbolic `𝔼₀`-manifold, BTZ points
  included: `GX.BTZTildeData.natGloballyHyperbolic_of_base` (the chartwise datum, DEC-118 (c)) and
  `GX.exists_btzTildeData_natGloballyHyperbolic` (such a datum exists). A concrete instance with
  `sing M ≠ ∅` (`{τ < 0} ⊆ 𝔼₀`) is checked in `campaign/WP-46d/Witness.lean` (not a module).
* **`lem:globally_hyperbolic_manifolds_maximal`** (l.2359) — certificate in `GX.BTZ.Manifolds`
  (`GX.BTZTildeData.isFutureDistinguishing_of_base`, proved directly, DEC-118 (a)); the paper's
  route l.2361 ("`M` GH ⇒ `\widetilde M` GH ⇒ FD") is now also proved, for the chartwise datum:
  `GX.BTZTildeData.isFutureDistinguishing_of_base_viaNatGH`.

**DEC-118 (b), what is proved.** `GX.BTZTildeData.natGloballyHyperbolic_of_base`: if the
`𝔼₀`-manifold `M` is GH, the chartwise `\widetilde M` is GH for `natCausality` (diamonds compact in
the natural topology). It is assembled from (1) **the abstract lifting theorem**
`GX.LiftGH.isCompact_of_liftLocalData`: a diamond `J(a,b)` over a compact `J(pa,pb)` of a strongly
causal base is compact as soon as every point of `J(pa,pb)` carries *local lifting data*
`GX.LiftGH.LiftLocalData` — the finite-chain argument of
`Causal.Flat.Cla.isCompact_diamond_of_isFiniteCover` with the finitely many **centres** as labels in
place of the (infinitely many) sheets, so no finite-sheet count is needed; (2) **the finite-sheet
half**, local data over `reg M`, `GX.BTZTildeData.liftLocalData_reg` (any datum); (3) **the
BTZ-sheet limit step**, local data over `sing M`, `GX.BTZTildeData.liftLocalData_sing_of_isChartwise`:
ONE descending chart `c` at `m` lifts at every point over its domain
(`GX.BTZTildeData.exists_liftedChart_of_isChartwise`), so `W = c⁻¹(int V₀)` (`V₀` causally convex
in `𝔼₀`) serves all components of `p⁻¹(W)` at once; the model facts are that the developed order
of `𝔻_∞ × ℝ` is closed in the natural topology although `D` is not continuous there
(`GX.isClosed_btzDevLe`) and that coordinate boxes are compact (`GX.isCompact_btzBox`).

> \begin{lem} Globally hyperbolic $\BTZ$-manifolds and $\BTZtilde$-manifolds are future
> distinguishing. \end{lem}
> \begin{lem} Let $M$ be a Globally hyperbolic $\BTZ$-manifolds. its maximal branched covering
> $\widetilde M$ is future distinguishing. \end{lem}
> Although, one has to re-prove most causal properties from scratch, the proof of this Lemma it
> not different from the proof of the similar statement for Lorentzian manifolds. (l.2325–2361)

## Hypothesis checklist

| paper / dispatch | here |
|---|---|
| `M` a globally hyperbolic `BTZ`-manifold | ✓ carried: `IsBTZSingModelled M`, GH for `e0ManifoldCausality M` (DEC-33) |
| `\widetilde M` GH, natural topology (DEC-106, DEC-118 (b)) | ✓ `d.natCausality.GloballyHyperbolic` for the chartwise datum (`d.IsChartwise`, DEC-118 (c): the `T'` of `btz_manifold_exists_chartwise_tamifying_reg`, which `BTZTildeData.nonempty` builds) |
| finite-sheet lemma | ✓ replaced by a stronger mechanism: centres as labels (`isCompact_of_liftLocalData`) + sheet data over `reg M` (`liftLocalData_reg`) |
| BTZ-sheet limit step | ✓ `liftLocalData_sing_of_isChartwise` (model: `isClosed_btzDevLe`, `isCompact_btzBox`) |

## SCOPE (disclosed)

* (a) The abstract theorem needs, besides the local data, only: `M` strongly causal with compact
  diamonds (GH), `p` continuous and causal (`proj_le`), `\widetilde M` Hausdorff and locally
  connected (`maxBranched_basic`), monotone continuous paths (`isCausallyConnected`, a `T'`-curve
  is a natural curve).
* (b) Over `reg M` the local data hold for every set `J` and every datum: `W = ψ⁻¹(ball)` inside
  an evenly covered set; on each sheet `D = g · ψ ∘ p` (`exists_smul_eq_dev_on`), `D` is naturally
  continuous (`nhds_reg`), and two points of the sheet with `D u ≤ D w` are joined by the lift of a
  straight segment, a link of the sheet's chart `g₀ · ψ ∘ p` (`retopBTZ`).
* (c) **Over `sing M`, the chartwise datum.** For a component `S` of `p⁻¹(W)` through `u`, the
  descent `Ψ : V̂ → Û ∋ u` of the fixed chart `c` is a natural homeomorphism, chartwise `T_BTZ`
  for `T'` (`IsChartwise`), with `D ∘ Ψ = g · btzDevM ∘ Φ` on all of `V̂` (regular part by
  `exists_smul_eq_of_isChartDescent`, then `T_BTZ`-density). (1) On `S ∩ p⁻¹(Q) ∩ J(a,b)` the model
  point `Φ Ψ⁻¹ z` lies in a box (`r`, `rθ`, `rθ² − r + t` bounded by the diamond of `𝐌³`, `t` by
  `Q`), compact by `isCompact_btzBox`; the limit is in `V̂` and `Ψ` of it is the limit, in `S`
  (`LiftGH.mem_connectedComponentIn_of_le_nhds`). (2) The developed order passes to the limit
  (`isClosed_btzDevLe`); the straight segment of `J⁺(Δ₀)` between the limits projects between two
  points of `V₀` (`e0Le_of_btzDevM_le`), hence into `V₀ ⊆ c(U)`, and is connected, so it stays in
  the target of the explicit chart `LiftGH.exists_chart_of_descent`, a link.
* (d) **An arbitrary `BTZTildeData` is not covered.** Its `T'` is pinned near a singular point
  only through the existential lifted chart of `isLocallyBTZTilde`, one per lift and with its own
  `𝔼₀`-chart; the round-0 statement for every datum (`liftLocalData_sing`, a tagged `sorry`) is
  removed. The `sing M = ∅` case holds for every datum
  (`natGloballyHyperbolic_of_base_of_sing_eq_empty`, an implication).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`; lean-causal `ca2ad78`.
-/

namespace GX

open Set Filter Topology Function
open scoped Real

namespace LiftGH

/-! ### Chains along a list of labels (after `Causal.Flat.Cla.CoverMGH` §2c) -/

section Chains

variable {σ E : Type*}

/-- A chain along a list of labels: `a = c₀ R_{s₁} c₁ R_{s₂} ⋯ R_{sₖ} cₖ = b`. -/
def LabelChain (R : σ → E → E → Prop) : List σ → E → E → Prop
  | [], a, b => a = b
  | s :: l, a, b => ∃ c, R s a c ∧ LabelChain R l c b

theorem labelChain_append (R : σ → E → E → Prop) (l₁ l₂ : List σ) (a b : E) :
    LabelChain R (l₁ ++ l₂) a b ↔ ∃ c, LabelChain R l₁ a c ∧ LabelChain R l₂ c b := by
  induction l₁ generalizing a with
  | nil => simp [LabelChain]
  | cons s l ih =>
    simp only [List.cons_append, LabelChain, ih]
    constructor
    · rintro ⟨c, hc, e, he, he'⟩
      exact ⟨e, ⟨c, hc, he⟩, he'⟩
    · rintro ⟨e, ⟨c, hc, he⟩, he'⟩
      exact ⟨c, hc, e, he, he'⟩

theorem LabelChain.rel {R : σ → E → E → Prop} {Q : E → E → Prop} (hrefl : ∀ a, Q a a)
    (htrans : ∀ a b c, Q a b → Q b c → Q a c) (hR : ∀ s a b, R s a b → Q a b) :
    ∀ {l : List σ} {a b : E}, LabelChain R l a b → Q a b
  | [], a, _, h => h ▸ hrefl a
  | _ :: _, _, _, ⟨_, hc, h⟩ => htrans _ _ _ (hR _ _ _ hc) (LabelChain.rel hrefl htrans hR h)

/-- The shortcut: if two steps with the same label can be merged whenever their outer ends are
related, a step followed by a chain with pairwise distinct labels is again such a chain. -/
theorem exists_nodup_labelChain {R : σ → E → E → Prop} {Q : E → E → Prop}
    (hrefl : ∀ a, Q a a) (htrans : ∀ a b c, Q a b → Q b c → Q a c)
    (hR : ∀ s a b, R s a b → Q a b)
    (hshort : ∀ s a b c e, R s a b → R s c e → Q a e → R s a e)
    {s : σ} {a c b : E} (hac : R s a c) {l : List σ} (hl : l.Nodup)
    (hcb : LabelChain R l c b) : ∃ l' : List σ, l'.Nodup ∧ LabelChain R l' a b := by
  by_cases hs : s ∈ l
  · obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem hs
    obtain ⟨e, h₁, f, hef, h₂⟩ := (labelChain_append R l₁ (s :: l₂) c b).1 hcb
    have hQ : Q a f := htrans _ _ _
      (htrans _ _ _ (hR _ _ _ hac) (LabelChain.rel hrefl htrans hR h₁)) (hR _ _ _ hef)
    exact ⟨s :: l₂, hl.sublist (List.sublist_append_right _ _), f,
      hshort _ _ _ _ _ hac hef hQ, h₂⟩
  · exact ⟨s :: l, List.nodup_cons.2 ⟨hs, hl⟩, c, hac, hcb⟩

/-- Lists of bounded length over a finite type form a finite set. -/
theorem finite_length_le (σ : Type*) [Finite σ] (N : ℕ) :
    {l : List σ | l.length ≤ N}.Finite := by
  have hinj : InjOn (fun l : List σ => fun i : Fin N => l[(i : ℕ)]?) {l | l.length ≤ N} := by
    intro l₁ h₁ l₂ h₂ h
    have h₁' : l₁.length ≤ N := h₁
    have h₂' : l₂.length ≤ N := h₂
    apply List.ext_getElem?
    intro n
    by_cases hn : n < N
    · exact congrFun h ⟨n, hn⟩
    · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
  exact Set.Finite.of_finite_image (Set.toFinite _) hinj

end Chains

/-! ### The abstract lifting theorem -/

section Abstract

variable {X M : Type*} [TopologicalSpace X] [TopologicalSpace M]

/-- **Local lifting data over an open set `W` of the base** for a relation `le` on `X`, a
projection `p : X → M` and a set `J ⊆ X` (in the application: the diamond). For every compact
`Q ⊆ W` and every component `S` of `p⁻¹(W)`:
(1) an ultrafilter carried by `S ∩ p⁻¹(Q) ∩ J` converges to a point of `S`;
(2) the relation `le` passes to limits inside `S` from pairs in `S ∩ p⁻¹(Q) ∩ J`. -/
def LiftLocalData (le : X → X → Prop) (p : X → M) (J : Set X) (W : Set M) : Prop :=
  ∀ Q : Set M, Q ⊆ W → IsCompact Q → ∀ u : X, p u ∈ W →
    (∀ 𝒰 : Ultrafilter X, connectedComponentIn (p ⁻¹' W) u ∩ (p ⁻¹' Q ∩ J) ∈ 𝒰 →
        ∃ w ∈ connectedComponentIn (p ⁻¹' W) u, ↑𝒰 ≤ 𝓝 w) ∧
    (∀ (𝒰 : Ultrafilter X) (F G : X → X) (u' w' : X),
        (∀ᶠ e in (𝒰 : Filter X), F e ∈ connectedComponentIn (p ⁻¹' W) u ∩ (p ⁻¹' Q ∩ J) ∧
          G e ∈ connectedComponentIn (p ⁻¹' W) u ∩ (p ⁻¹' Q ∩ J) ∧ le (F e) (G e)) →
        Tendsto F 𝒰 (𝓝 u') → Tendsto G 𝒰 (𝓝 w') →
        u' ∈ connectedComponentIn (p ⁻¹' W) u → w' ∈ connectedComponentIn (p ⁻¹' W) u → le u' w')

/-- **The abstract lifting theorem.** -/
theorem isCompact_of_liftLocalData [T2Space X] [LocallyConnectedSpace X] [T2Space M]
    (C : Causal.Causality M) (le : X → X → Prop) (hrefl : ∀ x, le x x)
    (htrans : ∀ x y z, le x y → le y z → le x z) (p : X → M) (hp : Continuous p) (a b : X)
    (hmono : ∀ x y, le x y → C.le ⊤ (p x) (p y))
    (hK : IsCompact (C.diamond ⊤ (p a) (p b))) (hSC : C.StronglyCausal)
    (hcurve : ∀ x y, le a x → le y b → le x y → ∃ γ : ℝ → X, ContinuousOn γ (Icc 0 1) ∧
      γ 0 = x ∧ γ 1 = y ∧ ∀ s ∈ Icc (0 : ℝ) 1, ∀ s' ∈ Icc (0 : ℝ) 1, s ≤ s' → le (γ s) (γ s'))
    (hLD : ∀ m ∈ C.diamond ⊤ (p a) (p b), ∃ W : Set M, IsOpen W ∧ m ∈ W ∧
      LiftLocalData le p {x | le a x ∧ le x b} W) :
    IsCompact {x | le a x ∧ le x b} := by
  classical
  set J := {x | le a x ∧ le x b} with hJdef
  set K := C.diamond ⊤ (p a) (p b) with hKdef
  have hJK : ∀ x ∈ J, p x ∈ K := fun x hx =>
    Causal.Causality.mem_diamond.2 ⟨hmono _ _ hx.1, hmono _ _ hx.2⟩
  -- the local data at the points of `K`
  choose! W hWo hmW hWL using hLD
  have hV : ∀ m ∈ K, ∃ V ∈ 𝓝 m, V ⊆ W m ∧ C.CausallyConvexIn V ⊤ := fun m hm =>
    hSC m _ ((hWo m hm).mem_nhds (hmW m hm))
  choose! V hVn hVW hVconv using hV
  -- compact `Q m ⊆ V m`, a neighbourhood of `m` in `K`
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  have hQ : ∀ m ∈ K, ∃ Q : Set M, IsCompact Q ∧ Q ⊆ V m ∧ ∃ U : Set M, IsOpen U ∧ m ∈ U ∧
      ∀ y ∈ K, y ∈ U → y ∈ Q := by
    intro m hm
    have hn : (Subtype.val ⁻¹' V m : Set K) ∈ 𝓝 (⟨m, hm⟩ : K) :=
      continuous_subtype_val.continuousAt.preimage_mem_nhds (hVn m hm)
    obtain ⟨t, htn, htc, htV⟩ := exists_mem_nhds_isClosed_subset hn
    refine ⟨Subtype.val '' t, htc.isCompact.image continuous_subtype_val, ?_, ?_⟩
    · rintro _ ⟨y, hy, rfl⟩; exact htV hy
    · rw [nhds_subtype, mem_comap] at htn
      obtain ⟨s', hs', hs't⟩ := htn
      refine ⟨interior s', isOpen_interior, mem_interior_iff_mem_nhds.2 hs', fun y hy hyU => ?_⟩
      have hys : y ∈ s' := interior_subset hyU
      exact ⟨⟨y, hy⟩, hs't (show (⟨y, hy⟩ : K) ∈ Subtype.val ⁻¹' s' from hys), rfl⟩
  choose! Q hQc hQV U hUo hmU hUQ using hQ
  have hQW : ∀ m ∈ K, Q m ⊆ W m := fun m hm => (hQV m hm).trans (hVW m hm)
  -- finitely many centres
  obtain ⟨t, htK, hKt⟩ := hK.elim_nhds_subcover U fun m hm => (hUo m hm).mem_nhds (hmU m hm)
  let σ := {c // c ∈ t}
  haveI : Fintype σ := Fintype.ofFinite σ
  -- the steps
  let R : σ → X → X → Prop := fun s x y => le x y ∧ x ∈ J ∧ y ∈ J ∧ p x ∈ U s.1 ∧
    p y ∈ U s.1 ∧ x ∈ connectedComponentIn (p ⁻¹' W s.1) y
  have hRle : ∀ s x y, R s x y → le x y := fun _ _ _ h => h.1
  have hJ_of_le : ∀ x y z, x ∈ J → z ∈ J → le x y → le y z → y ∈ J := fun _ _ _ hx hz h₁ h₂ =>
    ⟨htrans _ _ _ hx.1 h₁, htrans _ _ _ h₂ hz.2⟩
  have hpQ : ∀ (s : σ) x, x ∈ J → p x ∈ U s.1 → p x ∈ Q s.1 := fun s x hx hxU =>
    hUQ s.1 (htK s.1 s.2) _ (hJK x hx) hxU
  -- the merge: two steps over the same centre
  have hshort : ∀ s x y z w, R s x y → R s z w → le x w → R s x w := by
    intro s x y z w hxy hzw hxw
    refine ⟨hxw, hxy.2.1, hzw.2.2.1, hxy.2.2.2.1, hzw.2.2.2.2.1, ?_⟩
    obtain ⟨γ, hγc, hγ0, hγ1, hγm⟩ := hcurve x w hxy.2.1.1 hzw.2.2.1.2 hxw
    have hsK := htK s.1 s.2
    have hxV : p x ∈ V s.1 := hQV _ hsK (hpQ s x hxy.2.1 hxy.2.2.2.1)
    have hwV : p w ∈ V s.1 := hQV _ hsK (hpQ s w hzw.2.2.1 hzw.2.2.2.2.1)
    have hP : IsPreconnected (γ '' Icc 0 1) := isPreconnected_Icc.image _ hγc
    have hsub : γ '' Icc 0 1 ⊆ p ⁻¹' W s.1 := by
      rintro _ ⟨τ, hτ, rfl⟩
      have h1 : le x (γ τ) := hγ0 ▸ hγm 0 ⟨le_rfl, zero_le_one⟩ τ hτ hτ.1
      have h2 : le (γ τ) w := hγ1 ▸ hγm τ hτ 1 ⟨zero_le_one, le_rfl⟩ hτ.2
      exact hVW _ hsK ((hVconv _ hsK).2 _ hxV _ hwV
        (Causal.Causality.mem_diamond.2 ⟨hmono _ _ h1, hmono _ _ h2⟩))
    have hw : w ∈ γ '' Icc 0 1 := ⟨1, ⟨zero_le_one, le_rfl⟩, hγ1⟩
    have hx : x ∈ γ '' Icc 0 1 := ⟨0, ⟨le_rfl, zero_le_one⟩, hγ0⟩
    exact hP.subset_connectedComponentIn hw hsub hx
  -- (1) every relation of `J` is a chain with distinct centres
  have hchain : ∀ x y, x ∈ J → y ∈ J → le x y → ∃ l : List σ, l.Nodup ∧ LabelChain R l x y := by
    intro x y hx hy hxy
    obtain ⟨γ, hγc, hγ0, hγ1, hγm⟩ := hcurve x y hx.1 hy.2 hxy
    have hγJ : ∀ τ ∈ Icc (0 : ℝ) 1, γ τ ∈ J := fun τ hτ =>
      hJ_of_le x (γ τ) y hx hy (hγ0 ▸ hγm 0 ⟨le_rfl, zero_le_one⟩ τ hτ hτ.1)
        (hγ1 ▸ hγm τ hτ 1 ⟨zero_le_one, le_rfl⟩ hτ.2)
    have hf : ContinuousOn (fun τ => p (γ τ)) (Icc 0 1) := hp.comp_continuousOn hγc
    have hO : ∀ s : σ, ∃ O : Set ℝ, IsOpen O ∧
        (fun τ => p (γ τ)) ⁻¹' U s.1 ∩ Icc 0 1 = O ∩ Icc 0 1 :=
      fun s => continuousOn_iff'.1 hf _ (hUo _ (htK s.1 s.2))
    choose O hOo hOeq using hO
    have hcov : Icc (0 : ℝ) 1 ⊆ ⋃ s, O s := by
      intro τ hτ
      obtain ⟨c, hc, hcU⟩ := mem_iUnion₂.1 (hKt (hJK _ (hγJ τ hτ)))
      have h' : τ ∈ (fun τ => p (γ τ)) ⁻¹' U c ∩ Icc 0 1 := ⟨hcU, hτ⟩
      rw [hOeq ⟨c, hc⟩] at h'
      exact mem_iUnion.2 ⟨⟨c, hc⟩, h'.1⟩
    obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric isCompact_Icc hOo hcov
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / δ)
    have hNpos : (0 : ℝ) < N := lt_trans (by positivity) hN
    have hN1 : 1 / (N : ℝ) < δ := by
      have := (div_lt_iff₀ hδ).1 hN
      rw [div_lt_iff₀ hNpos]; linarith [mul_comm (N : ℝ) δ]
    have key : ∀ j : ℕ, j ≤ N → ∃ l : List σ, l.Nodup ∧
        LabelChain R l (γ (((N : ℝ) - j) / N)) y := by
      intro j
      induction j with
      | zero =>
        intro _
        refine ⟨[], List.nodup_nil, ?_⟩
        show γ (((N : ℝ) - ((0 : ℕ) : ℝ)) / N) = y
        rw [Nat.cast_zero, sub_zero, div_self hNpos.ne', hγ1]
      | succ j ih =>
        intro hj
        obtain ⟨l, hl, hch⟩ := ih (Nat.le_of_succ_le hj)
        have hjN : ((j : ℝ) + 1) ≤ N := by exact_mod_cast hj
        set τ : ℝ := ((N : ℝ) - ((j + 1 : ℕ) : ℝ)) / N with hτdef
        set τ' : ℝ := ((N : ℝ) - j) / N with hτ'def
        have hτ0 : 0 ≤ τ := by
          rw [hτdef]; push_cast; exact div_nonneg (by linarith) hNpos.le
        have hτ'1 : τ' ≤ 1 := by
          rw [hτ'def, div_le_one hNpos]; linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
        have hττ' : τ' - τ = 1 / N := by
          rw [hτdef, hτ'def]; push_cast; field_simp; ring
        have hτ : τ ∈ Icc (0 : ℝ) 1 := ⟨hτ0, by linarith [hττ', (by positivity : (0 : ℝ) ≤ 1 / N)]⟩
        have hτ' : τ' ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hττ', (by positivity : (0 : ℝ) ≤ 1 / N)], hτ'1⟩
        have hle' : τ ≤ τ' := by linarith [hττ', (by positivity : (0 : ℝ) ≤ 1 / N)]
        obtain ⟨s, hs⟩ := hball τ hτ
        have hsK := htK s.1 s.2
        have hseg : ∀ ρ ∈ Icc τ τ', ρ ∈ Icc (0 : ℝ) 1 ∧ p (γ ρ) ∈ U s.1 := by
          intro ρ hρ
          have hρ01 : ρ ∈ Icc (0 : ℝ) 1 := ⟨hτ0.trans hρ.1, hρ.2.trans hτ'1⟩
          have hρb : ρ ∈ Metric.ball τ δ := by
            rw [Metric.mem_ball, Real.dist_eq, abs_lt]
            constructor <;> linarith [hρ.1, hρ.2]
          have h' : ρ ∈ O s ∩ Icc 0 1 := ⟨hs hρb, hρ01⟩
          rw [← hOeq s] at h'
          exact ⟨hρ01, h'.1⟩
        have hR : R s (γ τ) (γ τ') := by
          refine ⟨hγm τ hτ τ' hτ' hle', hγJ τ hτ, hγJ τ' hτ', (hseg τ ⟨le_rfl, hle'⟩).2,
            (hseg τ' ⟨hle', le_rfl⟩).2, ?_⟩
          have hP : IsPreconnected (γ '' Icc τ τ') :=
            isPreconnected_Icc.image _ (hγc.mono (Icc_subset_Icc hτ0 hτ'1))
          have hsub : γ '' Icc τ τ' ⊆ p ⁻¹' W s.1 := by
            rintro _ ⟨ρ, hρ, rfl⟩
            obtain ⟨hρ01, hρU⟩ := hseg ρ hρ
            exact hQW _ hsK (hpQ s _ (hγJ ρ hρ01) hρU)
          exact hP.subset_connectedComponentIn ⟨τ', ⟨hle', le_rfl⟩, rfl⟩ hsub
            ⟨τ, ⟨le_rfl, hle'⟩, rfl⟩
        exact exists_nodup_labelChain hrefl htrans hRle hshort hR hl hch
    obtain ⟨l, hl, hch⟩ := key N le_rfl
    refine ⟨l, hl, ?_⟩
    have h0 : ((N : ℝ) - (N : ℝ)) / N = 0 := by simp
    rw [h0, hγ0] at hch
    exact hch
  -- (2) one step passes to the limit
  have hlim1 : ∀ (s : σ) (𝒰 : Ultrafilter X) (F G : X → X) (u : X),
      Tendsto F 𝒰 (𝓝 u) → (∀ᶠ e in (𝒰 : Filter X), R s (F e) (G e)) →
      ∃ w, Tendsto G 𝒰 (𝓝 w) ∧ le u w := by
    intro s 𝒰 F G u hF hR
    have hsK := htK s.1 s.2
    have hFQ : ∀ᶠ e in (𝒰 : Filter X), p (F e) ∈ Q s.1 :=
      hR.mono fun e he => hpQ s _ he.2.1 he.2.2.2.1
    have huQ : p u ∈ Q s.1 :=
      (hQc _ hsK).isClosed.mem_of_tendsto ((hp.tendsto u).comp hF) hFQ
    have huW : p u ∈ W s.1 := hQW _ hsK huQ
    have hSo : IsOpen (connectedComponentIn (p ⁻¹' W s.1) u) :=
      ((hWo _ hsK).preimage hp).connectedComponentIn
    have hFS : ∀ᶠ e in (𝒰 : Filter X), F e ∈ connectedComponentIn (p ⁻¹' W s.1) u :=
      hF (hSo.mem_nhds (mem_connectedComponentIn huW))
    have hGS : ∀ᶠ e in (𝒰 : Filter X),
        G e ∈ connectedComponentIn (p ⁻¹' W s.1) u ∩ (p ⁻¹' Q s.1 ∩ J) := by
      filter_upwards [hR, hFS] with e he hFe
      have hGQ : p (G e) ∈ Q s.1 := hpQ s _ he.2.2.1 he.2.2.2.2.1
      have h1 : connectedComponentIn (p ⁻¹' W s.1) (G e) =
          connectedComponentIn (p ⁻¹' W s.1) (F e) := connectedComponentIn_eq he.2.2.2.2.2
      have h2 : connectedComponentIn (p ⁻¹' W s.1) u =
          connectedComponentIn (p ⁻¹' W s.1) (F e) := connectedComponentIn_eq hFe
      refine ⟨?_, hGQ, he.2.2.1⟩
      rw [h2, ← h1]
      exact mem_connectedComponentIn (hQW _ hsK hGQ)
    obtain ⟨hL1, hL2⟩ := hWL s.1 hsK (Q s.1) (hQW _ hsK) (hQc _ hsK) u huW
    obtain ⟨w, hwS, hw⟩ := hL1 (𝒰.map G) (by rw [Ultrafilter.mem_map]; exact hGS)
    have hGw : Tendsto G 𝒰 (𝓝 w) := by rw [Ultrafilter.coe_map] at hw; exact hw
    refine ⟨w, hGw, hL2 𝒰 F G u w ?_ hF hGw (mem_connectedComponentIn huW) hwS⟩
    filter_upwards [hR, hFS, hFQ, hGS] with e he h1 h2 h3
    exact ⟨⟨h1, h2, he.2.1⟩, h3, he.1⟩
  -- (3) a chain of a fixed shape passes to the limit
  have hlim : ∀ (l : List σ) (𝒰 : Ultrafilter X) (F G : X → X) (u : X),
      Tendsto F 𝒰 (𝓝 u) → (∀ᶠ e in (𝒰 : Filter X), LabelChain R l (F e) (G e)) →
      ∃ w, Tendsto G 𝒰 (𝓝 w) ∧ le u w := by
    intro l
    induction l with
    | nil =>
      intro 𝒰 F G u hF hch
      exact ⟨u, hF.congr' (hch.mono fun e he => he), hrefl u⟩
    | cons s l ih =>
      intro 𝒰 F G u hF hch
      let c' : X → X := fun e =>
        if h : ∃ c, R s (F e) c ∧ LabelChain R l c (G e) then h.choose else e
      have hc' : ∀ᶠ e in (𝒰 : Filter X), R s (F e) (c' e) ∧ LabelChain R l (c' e) (G e) :=
        hch.mono fun e he => by
          have hce : c' e = he.choose := dif_pos he
          rw [hce]
          exact he.choose_spec
      obtain ⟨w₁, hw₁, h₁⟩ := hlim1 s 𝒰 F c' u hF (hc'.mono fun e he => he.1)
      obtain ⟨w, hw, h₂⟩ := ih 𝒰 c' G w₁ hw₁ (hc'.mono fun e he => he.2)
      exact ⟨w, hw, htrans _ _ _ h₁ h₂⟩
  -- (4) finitely many shapes
  have hfinite : ∀ (P : List σ → X → Prop) (𝒰 : Ultrafilter X),
      (∀ᶠ e in (𝒰 : Filter X), ∃ l : List σ, l.Nodup ∧ P l e) →
      ∃ l : List σ, ∀ᶠ e in (𝒰 : Filter X), P l e := by
    intro P 𝒰 h
    have hL : {l : List σ | l.length ≤ Fintype.card σ}.Finite := finite_length_le σ _
    have hmem : (⋃ l ∈ {l : List σ | l.length ≤ Fintype.card σ}, {e | P l e}) ∈ 𝒰 :=
      Filter.mem_of_superset h fun e ⟨l, hl, hP⟩ =>
        mem_iUnion₂.2 ⟨l, show l.length ≤ Fintype.card σ from hl.length_le_card, hP⟩
    obtain ⟨l, -, hl⟩ := (Ultrafilter.finite_biUnion_mem_iff hL).1 hmem
    exact ⟨l, hl⟩
  -- (5) an ultrafilter on `J` converges in `J`
  rw [isCompact_iff_ultrafilter_le_nhds]
  intro 𝒰 h𝒰
  have hev : ∀ᶠ e in (𝒰 : Filter X), e ∈ J := le_principal_iff.1 h𝒰
  obtain ⟨x₀, hx₀⟩ := hev.exists
  have hab : le a b := htrans _ _ _ hx₀.1 hx₀.2
  have haJ : a ∈ J := ⟨hrefl a, hab⟩
  have hbJ : b ∈ J := ⟨hab, hrefl b⟩
  obtain ⟨l, hl⟩ := hfinite (fun l e => LabelChain R l a e) 𝒰
    (hev.mono fun e he => hchain a e haJ he he.1)
  obtain ⟨z, hz, haz⟩ := hlim l 𝒰 (fun _ => a) id a tendsto_const_nhds hl
  obtain ⟨l', hl'⟩ := hfinite (fun l e => LabelChain R l e b) 𝒰
    (hev.mono fun e he => hchain e b he hbJ he.2)
  obtain ⟨w, hw, hzw⟩ := hlim l' 𝒰 id (fun _ => b) z hz hl'
  have hwb : b = w := tendsto_nhds_unique tendsto_const_nhds hw
  exact ⟨z, ⟨haz, hwb ▸ hzw⟩, hz⟩

end Abstract

end LiftGH

/-! ### The BTZ-sheet limit step in the model `𝔻_∞ × ℝ` -/

section ModelLimit

/-- The causal order of `𝐌³` between the developments `btzDevM 0 btzV0 y`, `btzDevM 0 btzV0 y'` of
two points of `𝔻_∞ × ℝ`, in the coordinates `(r, θ, t)` (`btzV0 = (−1, 1, 0)`): the three
conditions of `btzJ_le_iff` on `btzDev y' − btzDev y`. -/
def BtzDevLe (y y' : DInfty × ℝ) : Prop :=
  0 ≤ (y'.1.r * y'.1.θ ^ 2 - y'.1.r + y'.2) - (y.1.r * y.1.θ ^ 2 - y.1.r + y.2) ∧
    0 ≤ y'.1.r - y.1.r ∧
    (y'.1.r * y'.1.θ - y.1.r * y.1.θ) ^ 2 ≤
      ((y'.1.r * y'.1.θ ^ 2 - y'.1.r + y'.2) - (y.1.r * y.1.θ ^ 2 - y.1.r + y.2)) *
        (y'.1.r - y.1.r)

theorem btzDevM_le_iff (y y' : DInfty × ℝ) :
    (Causal.minkowski 2).le ⊤ (btzDevM 0 btzV0 y) (btzDevM 0 btzV0 y') ↔ BtzDevLe y y' := by
  rw [btzDevM, btzDevM, btzJ_le_iff]
  have e : btzDev 0 btzV0 y' - btzDev 0 btzV0 y =
      ((y'.1.r * y'.1.θ ^ 2 - y'.1.r + y'.2) - (y.1.r * y.1.θ ^ 2 - y.1.r + y.2),
        y'.1.r - y.1.r, y'.1.r * y'.1.θ - y.1.r * y.1.θ) := by
    rw [btzDev_coords, btzDev_coords]
    ext <;> (simp [btzV0]; try ring)
  rw [e]; rfl

/-- **The `θ`-free consequences of the developed order**: `r ≤ r'`, `t ≤ t'` and
`(r' − r)² ≤ (r' − r)(t' − t)` (the identity `Δ₁Δ₂ − Δ₃² = (r'−r)(t'−t) − (r'−r)² − r r' (θ'−θ)²`). -/
theorem BtzDevLe.thetaFree {y y' : DInfty × ℝ} (h : BtzDevLe y y') :
    y.1.r ≤ y'.1.r ∧ y.2 ≤ y'.2 ∧ (y'.1.r - y.1.r) ^ 2 ≤ (y'.1.r - y.1.r) * (y'.2 - y.2) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hr := y.1.r_nonneg
  have hr' := y'.1.r_nonneg
  have hid : ((y'.1.r * y'.1.θ ^ 2 - y'.1.r + y'.2) - (y.1.r * y.1.θ ^ 2 - y.1.r + y.2)) *
      (y'.1.r - y.1.r) - (y'.1.r * y'.1.θ - y.1.r * y.1.θ) ^ 2 =
      (y'.1.r - y.1.r) * (y'.2 - y.2) - (y'.1.r - y.1.r) ^ 2 -
        y.1.r * y'.1.r * (y'.1.θ - y.1.θ) ^ 2 := by ring
  have hq : (y'.1.r - y.1.r) ^ 2 ≤ (y'.1.r - y.1.r) * (y'.2 - y.2) := by
    have : 0 ≤ y.1.r * y'.1.r * (y'.1.θ - y.1.θ) ^ 2 := by positivity
    linarith
  refine ⟨by linarith, ?_, hq⟩
  rcases h2.lt_or_eq with h2 | h2
  · nlinarith
  · -- `r = r'`: then `Δ₃ = 0`
    have hr'r : y'.1.r = y.1.r := by linarith
    have h3' : y.1.r * y'.1.θ - y.1.r * y.1.θ = 0 := by
      rw [hr'r, sub_self, mul_zero] at h3
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (le_antisymm h3 (sq_nonneg _))
    rcases y.1.pos_or_eq_apex with hp | hp
    · have hθ : y'.1.θ = y.1.θ := by
        have : y.1.r * (y'.1.θ - y.1.θ) = 0 := by rw [mul_sub]; exact h3'
        rcases mul_eq_zero.1 this with h | h
        · exact absurd h hp.ne'
        · linarith
      rw [hr'r, hθ] at h1; linarith
    · have hy0 : y.1.r = 0 := by rw [hp]; rfl
      have hy0' : y'.1.r = 0 := by rw [hr'r, hy0]
      rw [hy0, hy0'] at h1; linarith

/-- At an apex point the developed order is `θ`-free: `(apex, t) ≤ y'` iff
`r' ≤ r'`-conditions of `BtzDevLe.thetaFree` hold. -/
theorem btzDevLe_apex_of {t : ℝ} {y' : DInfty × ℝ} (h1 : (DInfty.apex, t).2 ≤ y'.2)
    (h2 : (y'.1.r - 0) ^ 2 ≤ (y'.1.r - 0) * (y'.2 - t)) : BtzDevLe (DInfty.apex, t) y' := by
  have hr' := y'.1.r_nonneg
  simp only [BtzDevLe, DInfty.apex_r, DInfty.apex_θ, zero_mul, sub_zero, zero_add] at h1 h2 ⊢
  refine ⟨?_, hr', ?_⟩
  · rcases hr'.lt_or_eq with h | h
    · have : y'.1.r ≤ y'.2 - t := by nlinarith
      nlinarith [sq_nonneg y'.1.θ, mul_nonneg hr' (sq_nonneg y'.1.θ)]
    · rw [← h]; simp; linarith
  · nlinarith [sq_nonneg y'.1.θ, mul_nonneg hr' (sq_nonneg y'.1.θ)]

/-- **The BTZ-sheet limit step, in the model**: the developed order of `𝔻_∞ × ℝ` is closed for
its natural (product) topology — although `btzDevM` is not continuous at the apex (the angle is
unbounded there). Off the apex all coordinates are continuous; at an apex point `(apex, t)` the
order is `θ`-free (`btzDevLe_apex_of`) and its `θ`-free consequences (`BtzDevLe.thetaFree`) pass
to the limit. -/
theorem isClosed_btzDevLe : IsClosed {z : (DInfty × ℝ) × (DInfty × ℝ) | BtzDevLe z.1 z.2} := by
  have hr1 : Continuous fun z : (DInfty × ℝ) × (DInfty × ℝ) => z.1.1.r :=
    DInfty.continuous_r'.comp (continuous_fst.comp continuous_fst)
  have hr2 : Continuous fun z : (DInfty × ℝ) × (DInfty × ℝ) => z.2.1.r :=
    DInfty.continuous_r'.comp (continuous_fst.comp continuous_snd)
  have ht1 : Continuous fun z : (DInfty × ℝ) × (DInfty × ℝ) => z.1.2 :=
    continuous_snd.comp continuous_fst
  have ht2 : Continuous fun z : (DInfty × ℝ) × (DInfty × ℝ) => z.2.2 :=
    continuous_snd.comp continuous_snd
  set P := {z : (DInfty × ℝ) × (DInfty × ℝ) | z.1.1.r ≤ z.2.1.r ∧ z.1.2 ≤ z.2.2 ∧
    (z.2.1.r - z.1.1.r) ^ 2 ≤ (z.2.1.r - z.1.1.r) * (z.2.2 - z.1.2)} with hPdef
  have hPc : IsClosed P :=
    (isClosed_le hr1 hr2).inter ((isClosed_le ht1 ht2).inter
      (isClosed_le ((hr2.sub hr1).pow 2) ((hr2.sub hr1).mul (ht2.sub ht1))))
  rw [← closure_subset_iff_isClosed]
  intro x hx
  have hxP : x ∈ P := closure_minimal (fun z hz => BtzDevLe.thetaFree hz) hPc hx
  rcases x.1.1.pos_or_eq_apex with hp | hp
  · -- both points regular: every coordinate is continuous at `x`
    have hp' : 0 < x.2.1.r := lt_of_lt_of_le hp hxP.1
    set O := {z : (DInfty × ℝ) × (DInfty × ℝ) | 0 < z.1.1.r ∧ 0 < z.2.1.r} with hOdef
    have hOo : IsOpen O := (isOpen_lt continuous_const hr1).inter (isOpen_lt continuous_const hr2)
    have hθ1 : ContinuousAt (fun z : (DInfty × ℝ) × (DInfty × ℝ) => z.1.1.θ) x :=
      ContinuousAt.comp (f := fun z : (DInfty × ℝ) × (DInfty × ℝ) => z.1.1)
        (DInfty.continuousOn_θ'.continuousAt (DInfty.isOpen_pos.mem_nhds hp))
        (continuous_fst.comp continuous_fst).continuousAt
    have hθ2 : ContinuousAt (fun z : (DInfty × ℝ) × (DInfty × ℝ) => z.2.1.θ) x :=
      ContinuousAt.comp (f := fun z : (DInfty × ℝ) × (DInfty × ℝ) => z.2.1)
        (DInfty.continuousOn_θ'.continuousAt (DInfty.isOpen_pos.mem_nhds hp'))
        (continuous_fst.comp continuous_snd).continuousAt
    set f : (DInfty × ℝ) × (DInfty × ℝ) → ℝ × ℝ × ℝ := fun z =>
      ((z.2.1.r * z.2.1.θ ^ 2 - z.2.1.r + z.2.2) - (z.1.1.r * z.1.1.θ ^ 2 - z.1.1.r + z.1.2),
        z.2.1.r - z.1.1.r, z.2.1.r * z.2.1.θ - z.1.1.r * z.1.1.θ) with hfdef
    have hfc : ContinuousAt f x := by
      refine ContinuousAt.prodMk ?_ (ContinuousAt.prodMk ?_ ?_)
      · exact (((hr2.continuousAt.mul (hθ2.pow 2)).sub hr2.continuousAt).add ht2.continuousAt).sub
          (((hr1.continuousAt.mul (hθ1.pow 2)).sub hr1.continuousAt).add ht1.continuousAt)
      · exact hr2.continuousAt.sub hr1.continuousAt
      · exact (hr2.continuousAt.mul hθ2).sub (hr1.continuousAt.mul hθ1)
    have hC : IsClosed {w : ℝ × ℝ × ℝ | 0 ≤ w.1 ∧ 0 ≤ w.2.1 ∧ w.2.2 ^ 2 ≤ w.1 * w.2.1} :=
      (isClosed_le continuous_const continuous_fst).inter
        ((isClosed_le continuous_const (continuous_fst.comp continuous_snd)).inter
          (isClosed_le ((continuous_snd.comp continuous_snd).pow 2)
            (continuous_fst.mul (continuous_fst.comp continuous_snd))))
    have hx' : x ∈ closure (O ∩ {z | BtzDevLe z.1 z.2}) := hOo.inter_closure ⟨⟨hp, hp'⟩, hx⟩
    have hfx : f x ∈ closure (f '' (O ∩ {z | BtzDevLe z.1 z.2})) :=
      mem_closure_image hfc hx'
    have hsub : f '' (O ∩ {z | BtzDevLe z.1 z.2}) ⊆
        {w : ℝ × ℝ × ℝ | 0 ≤ w.1 ∧ 0 ≤ w.2.1 ∧ w.2.2 ^ 2 ≤ w.1 * w.2.1} := by
      rintro _ ⟨z, ⟨-, hz⟩, rfl⟩; exact hz
    exact closure_minimal hsub hC hfx
  · -- an apex point: the order there is `θ`-free
    have hx1 : x.1 = (DInfty.apex, x.1.2) := Prod.ext hp rfl
    show BtzDevLe x.1 x.2
    rw [hx1]
    obtain ⟨-, h2, h3⟩ := hxP
    rw [hp, DInfty.apex_r] at h3
    exact btzDevLe_apex_of h2 h3

/-- **Boxes of `𝔻_∞ × ℝ` are compact** (natural topology): `r ≤ R`, `r θ² ≤ C`, `t ∈ [T₁, T₂]`.
Near the apex the angle is free (its neighbourhoods are `{r < ε}`); away from it `θ² ≤ C / r` is
bounded. With `btzDevM` bounded on a diamond (`D` increasing) and the time of the base point
bounded on a compact set, this is the relative compactness half of the BTZ-sheet step. -/
theorem isCompact_btzBox (R C T₁ T₂ : ℝ) :
    IsCompact {y : DInfty × ℝ | y.1.r ≤ R ∧ y.1.r * y.1.θ ^ 2 ≤ C ∧ y.2 ∈ Icc T₁ T₂} := by
  rw [isCompact_iff_ultrafilter_le_nhds]
  intro 𝒰 h𝒰
  have hev : ∀ᶠ y in (𝒰 : Filter (DInfty × ℝ)),
      y.1.r ≤ R ∧ y.1.r * y.1.θ ^ 2 ≤ C ∧ y.2 ∈ Icc T₁ T₂ := le_principal_iff.1 h𝒰
  obtain ⟨y₁, hy₁⟩ := hev.exists
  have hC : 0 ≤ C := (mul_nonneg y₁.1.r_nonneg (sq_nonneg _)).trans hy₁.2.1
  obtain ⟨r₀, hr₀, hr⟩ := isCompact_Icc.ultrafilter_le_nhds (𝒰.map fun y => y.1.r) (by
    rw [Ultrafilter.coe_map, le_principal_iff, mem_map]
    exact hev.mono fun y hy => ⟨y.1.r_nonneg, hy.1⟩)
  obtain ⟨t₀, ht₀, ht⟩ := isCompact_Icc.ultrafilter_le_nhds (𝒰.map fun y => y.2) (by
    rw [Ultrafilter.coe_map, le_principal_iff, mem_map]
    exact hev.mono fun y hy => hy.2.2)
  rw [Ultrafilter.coe_map] at hr ht
  replace hr : Tendsto (fun y : DInfty × ℝ => y.1.r) 𝒰 (𝓝 r₀) := hr
  replace ht : Tendsto (fun y : DInfty × ℝ => y.2) 𝒰 (𝓝 t₀) := ht
  rcases hr₀.1.lt_or_eq with hpos | hzero
  · -- away from the apex the angle is bounded
    have hθb : ∀ᶠ y in (𝒰 : Filter (DInfty × ℝ)), y.1.θ ∈ Icc (-Real.sqrt (2 * C / r₀))
        (Real.sqrt (2 * C / r₀)) := by
      filter_upwards [hev, hr (Ioi_mem_nhds (half_lt_self hpos))] with y hy hyr
      have hr2 : r₀ / 2 < y.1.r := hyr
      have : y.1.θ ^ 2 ≤ 2 * C / r₀ := by
        rw [le_div_iff₀ hpos]; nlinarith [sq_nonneg y.1.θ, hy.2.1]
      exact abs_le.1 (Real.abs_le_sqrt this)
    obtain ⟨θ₀, -, hθ⟩ := isCompact_Icc.ultrafilter_le_nhds (𝒰.map fun y => y.1.θ) (by
      rw [Ultrafilter.coe_map, le_principal_iff, mem_map]; exact hθb)
    rw [Ultrafilter.coe_map] at hθ
    replace hθ : Tendsto (fun y : DInfty × ℝ => y.1.θ) 𝒰 (𝓝 θ₀) := hθ
    have h2 : ∀ᶠ y in (𝒰 : Filter (DInfty × ℝ)), 0 < y.1.r := hr (Ioi_mem_nhds hpos)
    let f : DInfty × ℝ → {q : ℝ × ℝ // 0 < q.1} := fun y =>
      if h : 0 < y.1.r then ⟨(y.1.r, y.1.θ), h⟩ else ⟨(r₀, θ₀), hpos⟩
    have hf : Tendsto f 𝒰 (𝓝 ⟨(r₀, θ₀), hpos⟩) := by
      rw [tendsto_subtype_rng]
      refine (hr.prodMk_nhds hθ).congr' ?_
      filter_upwards [h2] with y hy
      simp only [f, dif_pos hy]
    have hfst : Tendsto (fun y : DInfty × ℝ => y.1) 𝒰 (𝓝 (DInfty.posEmb ⟨(r₀, θ₀), hpos⟩)) := by
      refine ((DInfty.continuous_posEmb.tendsto _).comp hf).congr' ?_
      filter_upwards [h2] with y hy
      simp only [comp_apply, f, dif_pos hy]
      ext <;> rfl
    refine ⟨(DInfty.posEmb ⟨(r₀, θ₀), hpos⟩, t₀), ⟨hr₀.2, ?_, ht₀⟩, hfst.prodMk_nhds ht⟩
    exact le_of_tendsto (hr.mul (hθ.pow 2)) (hev.mono fun y hy => hy.2.1)
  · -- at the apex
    have hfst : Tendsto (fun y : DInfty × ℝ => y.1) 𝒰 (𝓝 DInfty.apex) :=
      DInfty.hasBasis_nhds_apex.tendsto_right_iff.2 fun ε hε =>
        hr (Iio_mem_nhds (hzero ▸ hε))
    refine ⟨(DInfty.apex, t₀), ⟨by rw [DInfty.apex_r, hzero]; exact hr₀.2, by simpa using hC,
      ht₀⟩, hfst.prodMk_nhds ht⟩

end ModelLimit

/-! ### Two general tools: limits stay in a component; the explicit singular chart -/

namespace LiftGH

/-- **A limit of a filter carried by a component stays in it**: in a locally connected space, if a
non-trivial filter `l` converges to `w ∈ O` (`O` open) and is carried by the component of `O`
through `u`, then `w` lies in that component. -/
theorem mem_connectedComponentIn_of_le_nhds {X : Type*} [TopologicalSpace X]
    [LocallyConnectedSpace X] {O : Set X} (hO : IsOpen O) {u w : X} {l : Filter X} [l.NeBot]
    (hl : l ≤ 𝓝 w) (hw : w ∈ O) (hS : connectedComponentIn O u ∈ l) :
    w ∈ connectedComponentIn O u := by
  have hwS : connectedComponentIn O w ∈ l :=
    hl ((hO.connectedComponentIn).mem_nhds (mem_connectedComponentIn hw))
  obtain ⟨x, hxw, hxu⟩ := Filter.nonempty_of_mem (Filter.inter_mem hwS hS)
  rw [connectedComponentIn_eq hxu, ← connectedComponentIn_eq hxw]
  exact mem_connectedComponentIn hw

variable {E : Type*} [TopologicalSpace E] {D : E → Causal.Minkowski 2}

/-- **The singular chart, explicitly** (`GX.exists_mem_btzTildeDevAtlas_of_descent` with its chart
named): a lifted chart `Ψ : V̂ → Û` with `D ∘ Ψ = g · btzDevM ∘ Φ` gives a chart `κ` of the
developed atlas with source `Û`, `κ ∘ Ψ = btzJDev ∘ Φ` on `V̂`, and whose target contains every
`q` with `Φ⁻¹(btzJDev⁻¹ q) ∈ V̂`. -/
theorem exists_chart_of_descent {F : Type*} (Φ : F ≃ DInfty × ℝ) {V : Set F}
    (hV : IsOpen[TopologicalSpace.induced Φ hornTop] V) {U : Set E} (hU : IsOpen U) {Ψ : F → E}
    (hbij : BijOn Ψ V U)
    (hn : ∀ v ∈ V, 𝓝 (Ψ v) = Filter.map Ψ (@nhds _ (TopologicalSpace.induced Φ hornTop) v))
    {g : Causal.Flat.isom 2} (hg : ∀ v ∈ V, D (Ψ v) = g • btzDevM 0 btzV0 (Φ v)) (hne : V.Nonempty) :
    ∃ κ : OpenPartialHomeomorph E BTZJ0, κ ∈ btzTildeDevAtlas D ∧ κ.source = U ∧
      (∀ v ∈ V, κ (Ψ v) = btzJDev (0 : ℝ × ℝ × ℝ) btzV0 btzV0_pos (Φ v)) ∧
      ∀ q : BTZJ0, Φ.symm ((btzJDevEquiv (0 : ℝ × ℝ × ℝ) btzV0 btzV0_pos).symm q) ∈ V →
        q ∈ κ.target := by
  obtain ⟨v₀, hv₀⟩ := hne
  haveI : Nonempty F := ⟨v₀⟩
  set TF : TopologicalSpace F := TopologicalSpace.induced Φ hornTop
  set j : DInfty × ℝ → BTZJ0 := btzJDev (0 : ℝ × ℝ × ℝ) btzV0 btzV0_pos
  set js : BTZJ0 → DInfty × ℝ := ⇑(btzJDevEquiv (0 : ℝ × ℝ × ℝ) btzV0 btzV0_pos).symm
  have hj : Continuous[hornTop, btzJTop 0] j := continuous_btzJDev btzV0_pos
  have hjs : Continuous[btzJTop 0, hornTop] js := continuous_btzJDevEquiv_symm btzV0_pos
  have hjjs : ∀ q, j (js q) = q := fun q =>
    (btzJDevEquiv (0 : ℝ × ℝ × ℝ) btzV0 btzV0_pos).apply_symm_apply q
  have hjsj : ∀ y, js (j y) = y := fun y =>
    (btzJDevEquiv (0 : ℝ × ℝ × ℝ) btzV0 btzV0_pos).symm_apply_apply y
  have hΦ : Continuous[TF, hornTop] Φ := continuous_induced_dom
  have hΦs : Continuous[hornTop, TF] Φ.symm := continuous_induced_rng.2 (by
    have : (⇑Φ ∘ ⇑Φ.symm) = id := funext fun y => Φ.apply_symm_apply y
    rw [this]; exact @continuous_id _ hornTop)
  set inv : E → F := Function.invFunOn Ψ V
  have hinv : ∀ w ∈ U, inv w ∈ V ∧ Ψ (inv w) = w := fun w hw => by
    have h := hbij.surjOn hw
    exact ⟨Function.invFunOn_mem h, Function.invFunOn_eq h⟩
  have hinvΨ : ∀ v ∈ V, inv (Ψ v) = v := fun v hv => hbij.injOn.leftInvOn_invFunOn hv
  have hVo : IsOpen[hornTop] (Φ.symm ⁻¹' V) := by
    obtain ⟨O, hO, rfl⟩ := (@isOpen_induced_iff _ _ hornTop _ _).1 hV
    have : Φ.symm ⁻¹' (Φ ⁻¹' O) = O := by
      ext y; simp
    rw [this]; exact hO
  let κ : OpenPartialHomeomorph E BTZJ0 :=
    { toFun := fun w => j (Φ (inv w))
      invFun := fun q => Ψ (Φ.symm (js q))
      source := U
      target := js ⁻¹' (Φ.symm ⁻¹' V)
      map_source' := fun w hw => by
        show Φ.symm (js (j (Φ (inv w)))) ∈ V
        rw [hjsj, Φ.symm_apply_apply]; exact (hinv w hw).1
      map_target' := fun q hq => hbij.mapsTo hq
      left_inv' := fun w hw => by
        show Ψ (Φ.symm (js (j (Φ (inv w))))) = w
        rw [hjsj, Φ.symm_apply_apply]; exact (hinv w hw).2
      right_inv' := fun q hq => by
        show j (Φ (inv (Ψ (Φ.symm (js q))))) = q
        rw [hinvΨ _ hq, Φ.apply_symm_apply, hjjs]
      open_source := hU
      open_target := @IsOpen.preimage _ _ (btzJTop 0) hornTop _ hjs _ hVo
      continuousOn_toFun := fun w hw => by
        obtain ⟨v, hv, rfl⟩ := hbij.surjOn hw
        refine ContinuousAt.continuousWithinAt ?_
        show Tendsto (fun w => j (Φ (inv w))) (𝓝 (Ψ v)) (𝓝 (j (Φ (inv (Ψ v)))))
        rw [hinvΨ v hv, hn v hv, tendsto_map'_iff]
        have hc : Continuous[TF, btzJTop 0] (fun v => j (Φ v)) :=
          @Continuous.comp _ _ _ TF hornTop (btzJTop 0) _ _ hj hΦ
        refine (@Continuous.tendsto _ _ TF _ _ hc v).congr' ?_
        filter_upwards [@IsOpen.mem_nhds _ TF _ _ hV hv] with v' hv'
        simp only [comp_apply, hinvΨ v' hv']
      continuousOn_invFun := fun q hq => by
        refine ContinuousAt.continuousWithinAt ?_
        show Tendsto _ (𝓝 q) (𝓝 (Ψ (Φ.symm (js q))))
        rw [hn _ hq]
        have hc : Continuous[btzJTop 0, TF] (fun q => Φ.symm (js q)) :=
          @Continuous.comp _ _ _ (btzJTop 0) hornTop TF _ _ hΦs hjs
        exact (tendsto_map (f := Ψ)).comp (@Continuous.tendsto _ _ (btzJTop 0) TF _ hc q) }
  refine ⟨κ, ⟨g, fun w hw => ?_⟩, rfl, fun v hv => ?_, fun q hq => hq⟩
  · obtain ⟨hv, hw'⟩ := hinv w hw
    show D w = g • btzDevM 0 btzV0 (Φ (inv w))
    conv_lhs => rw [← hw']
    exact hg _ hv
  · show j (Φ (inv (Ψ v))) = j (Φ v)
    rw [hinvΨ v hv]

end LiftGH

/-! ### `\widetilde M` with its natural topology -/

section TildeLift

universe v

attribute [local instance] btzE0Structure

variable {M : Type v} [TopologicalSpace M] [T2Space M] [LocPathConnectedSpace M]
  [FirstCountableTopology M] [ConnectedSpace M]
  [SingularGXStructure (Causal.Flat.isom 2) (Causal.Minkowski 2) M]

namespace BTZTildeData

variable {y₀ : ((Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) M)ᶜ : Set M)}
  {yN : ((Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0)ᶜ : Set BTZE0)}
  {Φ : MaxBranchedCover (Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0) yN ≃ₜ DInfty × ℝ}
  (d : BTZTildeData M y₀ Φ)

omit [T2Space M] [LocPathConnectedSpace M] [FirstCountableTopology M] [ConnectedSpace M] in
theorem semilocallySimplyConnected_reg :
    SemilocallySimplyConnected ((Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) M)ᶜ : Set M) :=
  semilocallySimplyConnected_compl_of_sing_subset (G := Causal.Flat.isom 2)
    (isLocallyUnloopable_of_normedSpace (Causal.Minkowski 2))
    (isClosed_sing (Causal.Flat.isom 2) (Causal.Minkowski 2) M) subset_rfl

/-- `\widetilde M` (natural topology) is locally path-connected (`GX.maxBranched_basic`). -/
theorem locPathConnectedSpace_maxBranched :
    LocPathConnectedSpace (MaxBranchedCover (Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) M) y₀) :=
  (maxBranched_basic (isSkeletal_sing (Causal.Flat.isom 2) (Causal.Minkowski 2) M)
    semilocallySimplyConnected_reg y₀).2.2.2.2.1

/-- **The natural diamonds are compact as soon as local lifting data exist over the base
diamond** — `GX.LiftGH.isCompact_of_liftLocalData` for `\widetilde M` with its natural topology
and the natural causality `natCausality`: monotone continuous paths from causal connectedness
(`isCausallyConnected`, a `T'`-curve is natural), the projection causal (`proj_le`), `M` globally
hyperbolic, hence strongly causal (`GloballyHyperbolic.stronglyCausal`). -/
theorem isCompact_natDiamond_of_liftLocalData (hM : IsBTZSingModelled M)
    (hG : (e0ManifoldCausality M hM).GloballyHyperbolic)
    (a b : MaxBranchedCover (Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) M) y₀)
    (hLD : ∀ m ∈ (e0ManifoldCausality M hM).diamond ⊤ a.base b.base, ∃ W : Set M, IsOpen W ∧
      m ∈ W ∧ LiftGH.LiftLocalData (fun x y => d.natCausality.le ⊤ x y) SpreadEnd.base
        {x | d.natCausality.le ⊤ a x ∧ d.natCausality.le ⊤ x b} W) :
    IsCompact (d.natCausality.diamond ⊤ a b) := by
  haveI := locPathConnectedSpace_maxBranched (y₀ := y₀)
  have hJ : d.natCausality.diamond ⊤ a b =
      {x | d.natCausality.le ⊤ a x ∧ d.natCausality.le ⊤ x b} := by
    ext x; exact Causal.Causality.mem_diamond
  rw [hJ]
  refine LiftGH.isCompact_of_liftLocalData (e0ManifoldCausality M hM)
    (fun x y => d.natCausality.le ⊤ x y) (fun x => d.natCausality.le_refl trivial)
    (fun _ _ _ h₁ h₂ => d.natCausality.le_trans h₁ h₂) SpreadEnd.base
    (continuous_base_weakTopMax (Causal.Flat.isom 2) (Causal.Minkowski 2) M y₀) a b
    (fun x y h => d.proj_le hM ((d.natCausality_le_top_iff).1 h)) (hG.2 _ _)
    (hG.stronglyCausal (e0ManifoldCausality_tarentin hM)) ?_ hLD
  intro x y _ _ hxy
  obtain ⟨c, hc, hc0, hc1⟩ := d.isCausallyConnected (d.fromNat x) (d.fromNat y)
    ((d.natCausality_le_top_iff).1 hxy)
  refine ⟨fun s => d.toNat (c s), d.continuous_toNat.comp_continuousOn
    (Causal.CurveOn.continuousOn (Causal.Precausality.isRelFamily_le _) hc), hc0, hc1, ?_⟩
  intro s hs s' hs' hss'
  exact (d.natCausality_le_top_iff).2 (hc.le_of_le hs.1 hss' hs'.2)

/-- **On a connected open set over `reg M`, `D` is a translate of a chart of `M` read through
`p`** (`exists_smul_eq_on_of_isRegularOn`: two regular maps of a connected set into the model
differ by one isometry). -/
theorem exists_smul_eq_dev_on {S : Set (MaxBranchedCover
    (Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) M) y₀)} (hS : IsPreconnected S)
    (hSo : IsOpen S)
    (hSreg : S ⊆ SpreadEnd.base ⁻¹' Reg (Causal.Flat.isom 2) (Causal.Minkowski 2) M)
    {ψ : OpenPartialHomeomorph M (Causal.Minkowski 2)}
    (hψ : ψ ∈ aeAtlas (Causal.Flat.isom 2) (Causal.Minkowski 2) M)
    (hψS : ∀ z ∈ S, z.base ∈ ψ.source) :
    ∃ g : Causal.Flat.isom 2, ∀ y ∈ S, ψ y.base = g • d.D y := by
  have hreg := semilocallySimplyConnected_reg (M := M)
  obtain ⟨hA, hβR⟩ := isRegularOn_base_maxBranched (G := Causal.Flat.isom 2)
    (X := Causal.Minkowski 2) hreg y₀
  have hD : IsRegularOn (Causal.Flat.isom 2) (aePullback (Causal.Flat.isom 2)
      (aeAtlas (Causal.Flat.isom 2) (Causal.Minkowski 2) M)
      (SpreadEnd.base : MaxBranchedCover (Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) M) y₀
        → M)) (gxModelAtlas (Causal.Flat.isom 2) (Causal.Minkowski 2)) d.D S :=
    IsRegularOn.mono d.isRegDeveloping hSreg hSo
  have hF' : IsRegularOn (Causal.Flat.isom 2) (aePullback (Causal.Flat.isom 2)
      (aeAtlas (Causal.Flat.isom 2) (Causal.Minkowski 2) M)
      (SpreadEnd.base : MaxBranchedCover (Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) M) y₀
        → M)) (gxModelAtlas (Causal.Flat.isom 2) (Causal.Minkowski 2))
      (fun z => ψ z.base) S :=
    isRegularOn_model_of_eventually_comp hA (hβR.mono hSreg hSo) fun z hz =>
      ⟨ψ, hψ, hψS z hz, 1, Filter.Eventually.of_forall fun y => (one_smul _ _).symm⟩
  exact exists_smul_eq_on_of_isRegularOn hS hD hF'

set_option maxHeartbeats 1600000 in
/-- **Local lifting data over a regular point** (the *finite-sheet* half of DEC-118 (b)): a
regular point `m` of `M` has an open neighbourhood `W` — the preimage of a Euclidean ball by a
chart `ψ` of `reg M`, inside an evenly covered set — such that for every component `S` of
`p⁻¹(W)` (a sheet, homeomorphic to `W` by `p`):
(1) `S ∩ p⁻¹(Q)` is compact for every compact `Q ⊆ W` (it is the lift of `Q` to the sheet);
(2) `≤` passes to limits in `S`: on the sheet `D = g · ψ ∘ p` (`exists_smul_eq_on_of_isRegularOn`),
`D` is naturally continuous there (`nhds_reg`), the order of `𝐌³` is closed, and two points of the
sheet with `D u ≤ D w` are joined by the lift of the straight segment of the ball, a chart link
of `\widetilde M` (the chart `g₀ · ψ ∘ p` of the sheet, `g₀` a fixed translation into the
half-space `J⁺(Δ₀) ∖ Δ₀`). No hypothesis on the diamond is used. -/
theorem liftLocalData_reg {m : M} (hm : m ∈ Reg (Causal.Flat.isom 2) (Causal.Minkowski 2) M) :
    ∃ W : Set M, IsOpen W ∧ m ∈ W ∧
      ∀ J : Set (MaxBranchedCover (Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) M) y₀),
        LiftGH.LiftLocalData (fun x y => d.natCausality.le ⊤ x y) SpreadEnd.base J W := by
  classical
  haveI := locPathConnectedSpace_maxBranched (y₀ := y₀)
  have hreg := semilocallySimplyConnected_reg (M := M)
  obtain ⟨-, -, hβS, -, -, -⟩ :=
    maxBranched_basic (isSkeletal_sing (Causal.Flat.isom 2) (Causal.Minkowski 2) M) hreg y₀
  have hms : m ∉ Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) M := fun h => h hm
  have hord : m ∈ ordY (SpreadEnd.base : MaxBranchedCover
      (Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) M) y₀ → M) := by
    by_contra h; exact hms (hβS h)
  obtain ⟨U, hUo, hmU, -, hcov⟩ := hord
  obtain ⟨ψ, hψ, hmψ⟩ := mem_support.1 hm
  -- the translation into the half-space
  obtain ⟨g₀, hg₀⟩ : ∃ g₀ : Causal.Flat.isom 2, ∀ x, g₀ • x = (btzJ0Pt - ψ m) + x :=
    ⟨⟨AffineEquiv.constVAdd ℝ (Causal.Minkowski 2) (btzJ0Pt - ψ m),
      Causal.Flat.constVAdd_mem_isom _⟩, fun x => by rw [Causal.Flat.isom_smul_def]; rfl⟩
  -- the ball
  have hO : IsOpen (ψ.target ∩ ψ.symm ⁻¹' U) := ψ.isOpen_inter_preimage_symm hUo
  have hmO : ψ m ∈ ψ.target ∩ ψ.symm ⁻¹' U :=
    ⟨ψ.map_source hmψ, by rw [mem_preimage, ψ.left_inv hmψ]; exact hmU⟩
  obtain ⟨ε₁, hε₁, hB₁⟩ := Metric.isOpen_iff.1 hO _ hmO
  obtain ⟨ε₂, hε₂, hB₂⟩ := Metric.isOpen_iff.1 isOpen_btzJ0HalfSpace _ btzJ0Pt_mem
  obtain ⟨ε, hε, hεε₁, hεε₂⟩ : ∃ ε : ℝ, 0 < ε ∧ ε ≤ ε₁ ∧ ε ≤ ε₂ :=
    ⟨min ε₁ ε₂, lt_min hε₁ hε₂, min_le_left _ _, min_le_right _ _⟩
  have hBt : Metric.ball (ψ m) ε ⊆ ψ.target ∩ ψ.symm ⁻¹' U :=
    (Metric.ball_subset_ball hεε₁).trans hB₁
  have hBh : ∀ x ∈ Metric.ball (ψ m) ε, g₀ • x ∈ Metric.ball btzJ0Pt ε := fun x hx => by
    rw [hg₀, Metric.mem_ball, dist_eq_norm]
    have : btzJ0Pt - ψ m + x - btzJ0Pt = x - ψ m := by abel
    rw [this, ← dist_eq_norm]; exact hx
  have hBh' : ∀ x, g₀ • x ∈ Metric.ball btzJ0Pt ε → x ∈ Metric.ball (ψ m) ε := fun x hx => by
    rw [hg₀, Metric.mem_ball, dist_eq_norm] at hx
    have : btzJ0Pt - ψ m + x - btzJ0Pt = x - ψ m := by abel
    rw [this, ← dist_eq_norm] at hx; exact hx
  have hHalf : Metric.ball btzJ0Pt ε ⊆ btzJ0HalfSpace :=
    (Metric.ball_subset_ball hεε₂).trans hB₂
  obtain ⟨W, hWdef⟩ : ∃ W : Set M, W = ψ.source ∩ ψ ⁻¹' Metric.ball (ψ m) ε := ⟨_, rfl⟩
  have hWo : IsOpen W := hWdef ▸ ψ.isOpen_inter_preimage Metric.isOpen_ball
  have hmW : m ∈ W := hWdef ▸ ⟨hmψ, Metric.mem_ball_self hε⟩
  have hWU : W ⊆ U := fun x hx => by
    rw [hWdef] at hx
    have := (hBt hx.2).2; rwa [mem_preimage, ψ.left_inv hx.1] at this
  have hWreg : W ⊆ Reg (Causal.Flat.isom 2) (Causal.Minkowski 2) M := fun x hx =>
    mem_support.2 ⟨ψ, hψ, by rw [hWdef] at hx; exact hx.1⟩
  have hWψ : ∀ x ∈ W, x ∈ ψ.source ∧ ψ x ∈ Metric.ball (ψ m) ε := fun x hx => by
    rw [hWdef] at hx; exact hx
  have hWc : IsPreconnected W := by
    rw [hWdef, ← ψ.symm_image_eq_source_inter_preimage (fun x hx => (hBt hx).1)]
    exact (convex_ball _ _).isPreconnected.image _
      (ψ.continuousOn_symm.mono fun x hx => (hBt hx).1)
  refine ⟨W, hWo, hmW, fun J Q hQW hQc u hu => ?_⟩
  -- the sheet through `u`
  obtain ⟨e, he⟩ := hcov u (hWU hu)
  have huT : u ∈ connectedComponentIn (SpreadEnd.base ⁻¹' U) u := mem_connectedComponentIn (hWU hu)
  have hST : connectedComponentIn (SpreadEnd.base ⁻¹' W) u ⊆
      connectedComponentIn (SpreadEnd.base ⁻¹' U) u := connectedComponentIn_mono _ (preimage_mono hWU)
  have hSW : connectedComponentIn (SpreadEnd.base ⁻¹' W) u ⊆ SpreadEnd.base ⁻¹' W :=
    connectedComponentIn_subset _ _
  have hSo : IsOpen (connectedComponentIn ((SpreadEnd.base : MaxBranchedCover
      (Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) M) y₀ → M) ⁻¹' W) u) :=
    (hWo.preimage SpreadEnd.continuous_base).connectedComponentIn
  -- the section of the sheet
  obtain ⟨sec, hsecc, hsec⟩ : ∃ sec : U → MaxBranchedCover
      (Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) M) y₀, Continuous sec ∧
      ∀ y, sec y = ((e.symm y : connectedComponentIn (SpreadEnd.base ⁻¹' U) u) :
        MaxBranchedCover (Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) M) y₀) :=
    ⟨_, continuous_subtype_val.comp e.symm.continuous, fun _ => rfl⟩
  have heb : ∀ y : U, (sec y).base = y := fun y => by
    have := he (e.symm y); rw [e.apply_symm_apply] at this; rw [hsec]; exact this.symm
  have hsecz : ∀ z (hz : z ∈ connectedComponentIn (SpreadEnd.base ⁻¹' U) u),
      sec (e ⟨z, hz⟩) = z := fun z hz => by rw [hsec, e.symm_apply_apply]
  have hlift : ∀ y : U, (y : M) ∈ W → sec y ∈ connectedComponentIn (SpreadEnd.base ⁻¹' W) u := by
    have h1 : IsPreconnected (Subtype.val ⁻¹' W : Set U) := by
      rw [← Topology.IsInducing.subtypeVal.isPreconnected_image, Subtype.image_preimage_coe,
        inter_eq_right.2 hWU]
      exact hWc
    have hP := h1.image _ hsecc.continuousOn
    have huP : u ∈ sec '' (Subtype.val ⁻¹' W : Set U) :=
      ⟨e ⟨u, huT⟩, by rw [mem_preimage, he]; exact hu, hsecz u huT⟩
    have hPW : sec '' (Subtype.val ⁻¹' W : Set U) ⊆ SpreadEnd.base ⁻¹' W := by
      rintro _ ⟨y, hy, rfl⟩; rw [mem_preimage, heb]; exact hy
    intro y hy
    exact hP.subset_connectedComponentIn huP hPW ⟨y, hy, rfl⟩
  refine ⟨fun 𝒰 h𝒰 => ?_, fun 𝒰 F G u' w' hFG hF hG hu' hw' => ?_⟩
  · -- (1) the lift of `Q` to the sheet is compact
    have hK'c : IsCompact (sec '' (Subtype.val ⁻¹' Q : Set U)) := by
      refine IsCompact.image ?_ hsecc
      rw [Subtype.isCompact_iff, Subtype.image_preimage_coe, inter_eq_right.2 (hQW.trans hWU)]
      exact hQc
    have hsub : connectedComponentIn (SpreadEnd.base ⁻¹' W) u ∩ (SpreadEnd.base ⁻¹' Q ∩ J) ⊆
        sec '' (Subtype.val ⁻¹' Q : Set U) := by
      rintro z ⟨hzS, hzQ, -⟩
      refine ⟨e ⟨z, hST hzS⟩, ?_, hsecz z (hST hzS)⟩
      rw [mem_preimage, he]; exact hzQ
    obtain ⟨w, hwK, hw⟩ := isCompact_iff_ultrafilter_le_nhds.1 hK'c 𝒰
      (le_principal_iff.2 (Filter.mem_of_superset h𝒰 hsub))
    obtain ⟨y, hyQ, rfl⟩ := hwK
    exact ⟨_, hlift y (hQW hyQ), hw⟩
  · -- (2) `≤` passes to limits in the sheet, through `D`
    have hSreg : connectedComponentIn (SpreadEnd.base ⁻¹' W) u ⊆
        SpreadEnd.base ⁻¹' Reg (Causal.Flat.isom 2) (Causal.Minkowski 2) M :=
      fun z hz => hWreg (hSW hz)
    obtain ⟨g₁, hg₁⟩ := d.exists_smul_eq_dev_on isPreconnected_connectedComponentIn hSo hSreg hψ
      fun z hz => (hWψ _ (hSW hz)).1
    -- `D` is naturally continuous on the sheet
    have hcont : ∀ z ∈ connectedComponentIn (SpreadEnd.base ⁻¹' W) u, ContinuousAt d.D z :=
      fun z hz => by
        have h := @Continuous.continuousAt _ _ d.T'.top _ _ z d.continuous_D
        unfold ContinuousAt at h ⊢
        rwa [d.nhds_reg z (hSreg hz)] at h
    have hle : ∀ᶠ e in (𝒰 : Filter _), (Causal.minkowski 2).le ⊤ (d.D (F e)) (d.D (G e)) :=
      hFG.mono fun e he => (btzTilde_le_dev (N := d.Space) (D := d.D) (hD := d.isBTZTildeDev)
        ((d.natCausality_le_top_iff).1 he.2.2)).1
    have hDuw : (Causal.minkowski 2).le ⊤ (d.D u') (d.D w') :=
      (Causal.minkowski_globallyHyperbolic.isClosed_le Causal.minkowski_tarentin).mem_of_tendsto
        (((hcont u' hu').tendsto.comp hF).prodMk_nhds ((hcont w' hw').tendsto.comp hG)) hle
    have hψuw : (Causal.minkowski 2).le ⊤ (ψ u'.base) (ψ w'.base) := by
      rw [hg₁ u' hu', hg₁ w' hw']; exact (Causal.Flat.isom_le_top_iff g₁).2 hDuw
    -- the chart of the sheet
    obtain ⟨sec', hsec'c, hsec'⟩ : ∃ sec' : M → MaxBranchedCover
        (Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) M) y₀, ContinuousOn sec' U ∧
        ∀ y : U, sec' y = sec y := by
      refine ⟨fun m' => if h : m' ∈ U then sec ⟨m', h⟩ else u, ?_, fun y => dif_pos y.2⟩
      rw [continuousOn_iff_continuous_restrict]
      have : U.restrict (fun m' => if h : m' ∈ U then sec ⟨m', h⟩ else u) = sec :=
        funext fun y => dif_pos y.2
      rw [this]; exact hsecc
    have hBW : ∀ x ∈ Metric.ball (ψ m) ε, ψ.symm x ∈ W := fun x hx => by
      rw [hWdef]
      exact ⟨ψ.map_target (hBt hx).1, by rw [mem_preimage, ψ.right_inv (hBt hx).1]; exact hx⟩
    have hval : ∀ z ∈ connectedComponentIn (SpreadEnd.base ⁻¹' W) u,
        (btzJ0RegInv (g₀ • ψ z.base)).val = g₀ • ψ z.base := fun z hz =>
      btzJ0RegInv_val (btzJ0HalfSpace_subset (hHalf (hBh _ (hWψ _ (hSW hz)).2)))
    let κN : OpenPartialHomeomorph (MaxBranchedCover
        (Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) M) y₀) BTZJ0 :=
      { toFun := fun z => btzJ0RegInv (g₀ • ψ z.base)
        invFun := fun q => sec' (ψ.symm (g₀⁻¹ • q.val))
        source := connectedComponentIn (SpreadEnd.base ⁻¹' W) u
        target := {q | q.val ∈ Metric.ball btzJ0Pt ε}
        map_source' := fun z hz => by
          show (btzJ0RegInv (g₀ • ψ z.base)).val ∈ Metric.ball btzJ0Pt ε
          rw [hval z hz]; exact hBh _ (hWψ _ (hSW hz)).2
        map_target' := fun q hq => by
          have hx : g₀⁻¹ • q.val ∈ Metric.ball (ψ m) ε :=
            hBh' _ (by rw [smul_inv_smul]; exact hq)
          show sec' (ψ.symm (g₀⁻¹ • q.val)) ∈ _
          rw [hsec' ⟨_, (hBt hx).2⟩]
          exact hlift _ (hBW _ hx)
        left_inv' := fun z hz => by
          show sec' (ψ.symm (g₀⁻¹ • (btzJ0RegInv (g₀ • ψ z.base)).val)) = z
          rw [hval z hz, inv_smul_smul, ψ.left_inv (hWψ _ (hSW hz)).1]
          have hzU : z.base ∈ U := hWU (hSW hz)
          rw [hsec' ⟨_, hzU⟩]
          have h2 : (⟨z.base, hzU⟩ : U) = e ⟨z, hST hz⟩ := Subtype.ext (he ⟨z, hST hz⟩).symm
          rw [h2, hsecz]
        right_inv' := fun q hq => by
          have hx : g₀⁻¹ • q.val ∈ Metric.ball (ψ m) ε :=
            hBh' _ (by rw [smul_inv_smul]; exact hq)
          show btzJ0RegInv (g₀ • ψ (sec' (ψ.symm (g₀⁻¹ • q.val))).base) = q
          rw [hsec' ⟨_, (hBt hx).2⟩, heb, ψ.right_inv (hBt hx).1, smul_inv_smul,
            btzJ0RegInv_of_mem q.mem]
          rfl
        open_source := hSo
        open_target := Metric.isOpen_ball.preimage continuous_btzJ_val
        continuousOn_toFun := fun z hz => by
          refine ContinuousAt.continuousWithinAt ?_
          have hc1 : ContinuousAt (fun z : MaxBranchedCover
              (Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) M) y₀ => ψ z.base) z :=
            (ψ.continuousAt (hWψ _ (hSW hz)).1).comp SpreadEnd.continuous_base.continuousAt
          have hc2 : ContinuousAt btzJ0RegInv (g₀ • ψ z.base) :=
            btzJ0RegIncl.continuousAt_symm (hHalf (hBh _ (hWψ _ (hSW hz)).2))
          have hc3 : Continuous (fun x : Causal.Minkowski 2 => g₀ • x) :=
            (Causal.Flat.isom.toHomeomorph g₀).continuous
          have h4 : ContinuousAt (fun z : MaxBranchedCover
              (Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) M) y₀ => g₀ • ψ z.base) z :=
            ContinuousAt.comp (g := fun x : Causal.Minkowski 2 => g₀ • x)
              (f := fun z : MaxBranchedCover (Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) M) y₀ =>
                ψ z.base) hc3.continuousAt hc1
          exact ContinuousAt.comp (f := fun z : MaxBranchedCover
            (Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) M) y₀ => g₀ • ψ z.base) hc2 h4
        continuousOn_invFun := by
          have hc3 : Continuous (fun x : Causal.Minkowski 2 => g₀⁻¹ • x) :=
            (Causal.Flat.isom.toHomeomorph g₀⁻¹).continuous
          refine hsec'c.comp (ψ.continuousOn_symm.comp
            (hc3.comp continuous_btzJ_val).continuousOn ?_) ?_
          · intro q hq
            exact (hBt (hBh' _ (by rw [smul_inv_smul]; exact hq))).1
          · intro q hq
            exact (hBt (hBh' _ (by rw [smul_inv_smul]; exact hq))).2 }
    let κ : OpenPartialHomeomorph d.Space BTZJ0 :=
      OpenPartialHomeomorph.retopBTZ d.T' κN d.le_natural (fun x hx => d.nhds_reg x (hSreg hx))
    have hκv : ∀ z : d.Space, d.toNat z ∈ connectedComponentIn (SpreadEnd.base ⁻¹' W) u →
        (κ z).val = g₀ • ψ (d.toNat z).base := fun z hz => hval _ hz
    have hκ : κ ∈ btzTildeDevAtlas (N := d.Space) d.D := by
      refine ⟨g₁⁻¹ * g₀⁻¹, fun z hz => ?_⟩
      have hz' : d.toNat z ∈ connectedComponentIn (SpreadEnd.base ⁻¹' W) u := hz
      show d.D (d.toNat z) = _
      rw [hκv z hz', mul_smul, inv_smul_smul]
      exact (inv_smul_eq_iff.2 (hg₁ _ hz')).symm
    have hlink : btzJLe (κ (d.fromNat u')) (κ (d.fromNat w')) := by
      show (Causal.minkowski 2).le ⊤ (κ (d.fromNat u')).val (κ (d.fromNat w')).val
      rw [hκv (d.fromNat u') hu', hκv (d.fromNat w') hw']; exact (Causal.Flat.isom_le_top_iff g₀).2 hψuw
    have hseg : ∀ s ∈ Icc (0 : ℝ) 1,
        btzJSeg hlink s ∈ Causal.chartImage κ (⊤ ⊓ Causal.chartSource κ) := by
      intro s hs
      have hmem : (btzJSeg hlink s).val ∈ Metric.ball btzJ0Pt ε := by
        rw [btzJSeg_val]
        refine btzJSegPt_mem_ball ?_ ?_ hs
        · rw [hκv (d.fromNat u') hu']; exact hBh _ (hWψ _ (hSW hu')).2
        · rw [hκv (d.fromNat w') hw']; exact hBh _ (hWψ _ (hSW hw')).2
      have hmem' : btzJSeg hlink s ∈ κ.target := hmem
      exact ⟨κ.symm (btzJSeg hlink s), ⟨κ.map_target hmem', trivial, κ.map_target hmem'⟩,
        κ.right_inv hmem'⟩
    have hu'κ : d.fromNat u' ∈ κ.source := hu'
    have hw'κ : d.fromNat w' ∈ κ.source := hw'
    have hle' : d.causality.le ⊤ (d.fromNat u') (d.fromNat w') :=
      btzTildeAtlasCausality_le_of_link (hA := d.isBTZTildeDev) hκ
        (btzTilde_link_le_iff.2 ⟨⟨trivial, hu'κ⟩, ⟨trivial, hw'κ⟩,
          0, 1, zero_le_one, btzJSeg hlink, btzJ_curveOn_seg hlink hseg, btzJSeg_zero hlink,
          btzJSeg_one hlink⟩)
    exact (d.natCausality_le_top_iff).2 hle'

/-- **The chartwise datum** (DEC-118 (c), the `\widetilde M` actually constructed): the topology
`T'` of `d` is chartwise `T_BTZ` for EVERY descending `𝔼₀`-chart and EVERY descent of it — the
third conclusion of `GX.btz_manifold_exists_chartwise_tamifying_reg`, which is how
`BTZTildeData.nonempty` builds its datum (`exists_isChartwise`). -/
def IsChartwise : Prop :=
  ∀ (y : M) (c : XAChart (Causal.Flat.isom 2) (Causal.Minkowski 2) btzFam btzFamS () y),
    IsDescendingChartMap (Causal.Flat.isom 2) (Causal.Minkowski 2) c.φ →
    ∀ (f : MaxBranchedCover (Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0) yN)
      (Ψ : MaxBranchedCover (Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0) yN →
        MaxBranchedCover (Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) M) y₀),
      IsChartDescent (c.U : Set M) (c.V : Set BTZE0) (chartExt c.φ) f Ψ →
      ∀ v ∈ connectedComponentIn (SpreadEnd.base ⁻¹' (c.V : Set BTZE0)) f,
        @nhds _ d.T'.top (Ψ v) = Filter.map Ψ (@nhds _ (TopologicalSpace.induced Φ hornTop) v)

/-- **The chartwise datum exists** for every `𝔼₀`-manifold, base point and presentation (the
construction of `BTZTildeData.nonempty`, keeping the chartwise clause). -/
theorem exists_isChartwise (hM : IsBTZSingModelled M)
    (hΦ : ∀ e, orbitMk (GammaA (2 * π)) (Φ e) = e.base) :
    ∃ d : BTZTildeData M y₀ Φ, d.IsChartwise := by
  obtain ⟨T, hT, hreg, hch⟩ := btz_manifold_exists_chartwise_tamifying_reg hM y₀ yN Φ hΦ
  obtain ⟨D, hDc, hDr⟩ := hT.exists_extension
  exact ⟨⟨⟨T⟩, hT.le_natural, hreg, D, hDc, hDr,
    isLocallyBTZTilde_of_chartwise hM hΦ ⟨T⟩ hT hch hDc hDr, hΦ⟩, hch⟩

set_option maxHeartbeats 1600000 in
/-- **The lifted chart of ONE descending chart, at every point over its domain** (for the
chartwise datum): for a descending `𝔼₀`-chart `c : U ≅ V` (centred anywhere) and every `z` over
`U`, a descent `Ψ : V̂ → Û` with `Ψ f = z` (`Û ∋ z` the component of `p⁻¹(U)`), an open bijection
(natural and `T_BTZ`), a natural local homeomorphism, chartwise `T_BTZ` for `T'`, and
`D ∘ Ψ = g · btzDevM ∘ Φ` on ALL of `V̂` (on the regular part by
`exists_smul_eq_of_isChartDescent`, then by `T_BTZ`-density as in
`isLocallyBTZTilde_of_chartwise`). This is the uniformity over the lifts that an arbitrary datum
lacks (SCOPE (c)). -/
theorem exists_liftedChart_of_isChartwise (hd : d.IsChartwise) {x : M}
    (c : XAChart (Causal.Flat.isom 2) (Causal.Minkowski 2) btzFam btzFamS () x)
    (hc : IsDescendingChartMap (Causal.Flat.isom 2) (Causal.Minkowski 2) c.φ)
    (z : MaxBranchedCover (Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) M) y₀)
    (hz : z.base ∈ (c.U : Set M)) :
    ∃ (f : MaxBranchedCover (Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0) yN)
      (Ψ : MaxBranchedCover (Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0) yN →
        MaxBranchedCover (Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) M) y₀),
      IsChartDescent (c.U : Set M) (c.V : Set BTZE0) (chartExt c.φ) f Ψ ∧ Ψ f = z ∧
      IsOpen (connectedComponentIn (SpreadEnd.base ⁻¹' (c.V : Set BTZE0)) f) ∧
      IsOpen[TopologicalSpace.induced Φ hornTop]
        (connectedComponentIn (SpreadEnd.base ⁻¹' (c.V : Set BTZE0)) f) ∧
      IsOpen (connectedComponentIn (SpreadEnd.base ⁻¹' (c.U : Set M)) z) ∧
      BijOn Ψ (connectedComponentIn (SpreadEnd.base ⁻¹' (c.V : Set BTZE0)) f)
        (connectedComponentIn (SpreadEnd.base ⁻¹' (c.U : Set M)) z) ∧
      (∀ v ∈ connectedComponentIn (SpreadEnd.base ⁻¹' (c.V : Set BTZE0)) f,
        𝓝 (Ψ v) = Filter.map Ψ (𝓝 v)) ∧
      (∀ v ∈ connectedComponentIn (SpreadEnd.base ⁻¹' (c.V : Set BTZE0)) f,
        @nhds _ d.T'.top (Ψ v) =
          Filter.map Ψ (@nhds _ (TopologicalSpace.induced Φ hornTop) v)) ∧
      ∃ g : Causal.Flat.isom 2,
        ∀ v ∈ connectedComponentIn (SpreadEnd.base ⁻¹' (c.V : Set BTZE0)) f,
          d.D (Ψ v) = g • btzDevM 0 btzV0 (Φ v) := by
  have hX := isLocallyUnloopable_of_normedSpace (Causal.Minkowski 2)
  have hregM := semilocallySimplyConnected_compl_of_sing_subset (G := Causal.Flat.isom 2) hX
    (isClosed_sing (Causal.Flat.isom 2) (Causal.Minkowski 2) M) subset_rfl
  have hregN := semilocallySimplyConnected_compl_of_sing_subset (G := Causal.Flat.isom 2) hX
    (isClosed_sing (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0) subset_rfl
  have hΦ := d.isPresentation
  obtain ⟨-, hβN, -, -, hβlN, -⟩ := maxBranched_basic
    (isSkeletal_sing (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0) hregN yN
  obtain ⟨-, hβM, -, -, hβlM, -⟩ := maxBranched_basic
    (isSkeletal_sing (Causal.Flat.isom 2) (Causal.Minkowski 2) M) hregM y₀
  obtain ⟨f, hf⟩ := hβN.surjective (chartExt c.φ z.base)
  obtain ⟨Ψ, hΨ, hΨf⟩ := hc y₀ yN z f hz hf
  have hVo : IsOpen (connectedComponentIn
      ((SpreadEnd.base : MaxBranchedCover (Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0)
        yN → BTZE0) ⁻¹' (c.V : Set BTZE0)) f) := by
    haveI := hβlN
    exact (c.V.isOpen.preimage hβN.isSpread.continuous).connectedComponentIn
  have hUo : IsOpen (connectedComponentIn
      ((SpreadEnd.base : MaxBranchedCover (Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) M)
        y₀ → M) ⁻¹' (c.U : Set M)) z) := by
    haveI := hβlM
    exact (c.U.isOpen.preimage hβM.isSpread.continuous).connectedComponentIn
  let TN : WrappedTop
      (MaxBranchedCover (Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0) yN) :=
    ⟨TopologicalSpace.induced Φ hornTop⟩
  have hTN : IsTamifyingTopology (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0 yN TN.top :=
    btz_isTamifyingTopology btzV0_pos btz_two_pi_ne_zero isBTZStructure_btzE0 hΦ
  have hdisc : ∀ x : BTZE0, DiscreteTopology
      ((SpreadEnd.base : MaxBranchedCover (Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0)
        yN → BTZE0) ⁻¹' {x}) :=
    fun x => discreteTopology_fiber_of_isLocallyGaloisian hX isLocallyGaloisian_btzE0 yN x
  have hfV := mem_connectedComponentIn (F := SpreadEnd.base ⁻¹' (c.V : Set BTZE0)) hΨ.base_mem
  obtain ⟨g, hg⟩ := exists_smul_eq_of_isChartDescent hregM hregN c.isAEMorphism d.isRegDeveloping
    (btz_isRegDevelopingOnReg btzV0_pos btz_two_pi_ne_zero isBTZStructure_btzE0 hΦ) hΨ
  have hT'n := hd x c hc f Ψ hΨ
  have hVoB := TopologicalSpace.le_def.1 hTN.le_natural _ hVo
  have hsurj : SurjOn Ψ (connectedComponentIn (SpreadEnd.base ⁻¹' (c.V : Set BTZE0)) f)
      (connectedComponentIn (SpreadEnd.base ⁻¹' (c.U : Set M)) z) := by
    have := hΨ.surjOn_cc_of_lift hregM hregN c.U.isOpen c.V.isOpen (continuousOn_chartExt c.φ)
      (injOn_chartExt c.φ) (mapsTo_chartExt c.φ)
      (fun m hm => chartExt_mem_reg_iff c.isAEMorphism hm) hdisc hTN
      (fun z f' hz hf' => hc y₀ yN z f' hz hf')
    rwa [hΨf] at this
  have hmaps : MapsTo Ψ (connectedComponentIn (SpreadEnd.base ⁻¹' (c.V : Set BTZE0)) f)
      (connectedComponentIn (SpreadEnd.base ⁻¹' (c.U : Set M)) z) := by
    have := hΨ.mapsTo_cc hfV; rwa [hΨf] at this
  refine ⟨f, Ψ, hΨ, hΨf, hVo, hVoB, hUo,
    ⟨hmaps, btz_descent_injOn c.isAEMorphism hΦ hΨ, hsurj⟩, fun v hv => ?_, hT'n, g, ?_⟩
  · exact hΨ.nhds_eq_map_of_lift hregM hregN c.U.isOpen c.V.isOpen (continuousOn_chartExt c.φ)
      (injOn_chartExt c.φ) (fun m hm => chartExt_mem_reg_iff c.isAEMorphism hm) hdisc hTN
      (fun z f' hz hf' => hc y₀ yN z f' hz hf') hv
  -- the identity extends from the `T_BTZ`-dense regular part of `V̂` by continuity
  have hc1 : @ContinuousOn _ _ (TopologicalSpace.induced Φ hornTop) _ (fun v => d.D (Ψ v))
      (connectedComponentIn (SpreadEnd.base ⁻¹' (c.V : Set BTZE0)) f) := fun v hv => by
    have h1 := @Continuous.tendsto _ _ d.T'.top _ d.D d.continuous_D (Ψ v)
    rw [hT'n v hv] at h1
    exact (tendsto_map'_iff.1 h1).mono_left
      (@nhdsWithin_le_nhds _ (TopologicalSpace.induced Φ hornTop) v _)
  have hc2 : @ContinuousOn _ _ (TopologicalSpace.induced Φ hornTop) _
      (fun v => g • btzDevM 0 btzV0 (Φ v))
      (connectedComponentIn (SpreadEnd.base ⁻¹' (c.V : Set BTZE0)) f) := by
    have hdev : Continuous[TopologicalSpace.induced Φ hornTop, _]
        (fun v => btzDevM 0 btzV0 (Φ v)) :=
      @Continuous.comp _ _ _ (TopologicalSpace.induced Φ hornTop) hornTop _ _ _
        (continuous_btzDevM_hornTop 0 btzV0_pos) continuous_induced_dom
    exact @Continuous.continuousOn _ _ (TopologicalSpace.induced Φ hornTop) _ _ _
      (@Continuous.comp _ _ _ (TopologicalSpace.induced Φ hornTop) _ _ _ _
        (continuous_const_smul g) hdev)
  have hcl := @Dense.open_subset_closure_inter _ (TopologicalSpace.induced Φ hornTop) _ _
    (@IsPortly.dense _ (TopologicalSpace.induced Φ hornTop) _ hTN.isPortly) hVoB
  exact @Set.EqOn.of_subset_closure _ _ (TopologicalSpace.induced Φ hornTop) _ _ _ _ _ _
    (fun v hv => hg v ⟨hv.1, hv.2⟩) hc1 hc2 inter_subset_left hcl

set_option maxHeartbeats 3200000 in
/-- **Local lifting data over a singular point** (the *BTZ-sheet limit step* of DEC-118 (b)), for
the chartwise datum and the diamond `J(a, b)`. `c : U ≅ V` a descending `𝔼₀`-chart at `m`,
`V₀ ∋ c(m)` a causally convex neighbourhood in `𝔼₀` (`E0.stronglyCausal`) inside `c(U)`, and
`W = c⁻¹(int V₀)`. A component `S` of `p⁻¹(W)` lies in the image `Û` of ONE descent
`Ψ : V̂ → Û` of `c` (`exists_liftedChart_of_isChartwise`), on which `D = g · btzDevM ∘ Φ ∘ Ψ⁻¹`.
(1) On `S ∩ p⁻¹(Q) ∩ J(a, b)` the model point `Φ Ψ⁻¹ z` lies in a box of `𝔻_∞ × ℝ` (`D` bounded
by the diamond of `𝐌³`, the time by `Q`), compact (`isCompact_btzBox`); its limit is in `V̂`, and
`Ψ` of it is the limit in `S`. (2) The developed order passes to the limit in the natural
topology (`isClosed_btzDevLe`) and the straight segment of `J⁺(Δ₀)` between the two limits
stays in the chart: its points project between two points of `V₀` (`e0Le_of_btzDevM_le`), hence
into `V₀ ⊆ c(U)` by convexity, and the segment is connected. -/
theorem liftLocalData_sing_of_isChartwise (hd : d.IsChartwise) (hM : IsBTZSingModelled M)
    (a b : MaxBranchedCover (Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) M) y₀) {m : M}
    (hm : m ∈ Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) M) :
    ∃ W : Set M, IsOpen W ∧ m ∈ W ∧
      LiftGH.LiftLocalData (fun x y => d.natCausality.le ⊤ x y) SpreadEnd.base
        {x | d.natCausality.le ⊤ a x ∧ d.natCausality.le ⊤ x b} W := by
  classical
  haveI := locPathConnectedSpace_maxBranched (y₀ := y₀)
  haveI := locPathConnectedSpace_maxBranched (M := BTZE0) (y₀ := yN)
  obtain ⟨c, hc⟩ := btz_exists_descendingChart hM hm
  -- a causally convex neighbourhood in `𝔼₀`
  have hφm : chartExt c.φ m ∈ (c.V : Set BTZE0) := mapsTo_chartExt c.φ c.mem
  have hOn : E0.toPaper '' (c.V : Set BTZE0) ∈ 𝓝 (E0.toPaper (chartExt c.φ m)) :=
    (E0.toPaper.isOpenMap _ c.V.isOpen).mem_nhds ⟨_, hφm, rfl⟩
  obtain ⟨V₀, hV₀n, hV₀O, hV₀c⟩ := E0.stronglyCausal _ _ hOn
  have hφc : ContinuousOn (fun y => E0.toPaper (chartExt c.φ y)) (c.U : Set M) :=
    E0.toPaper.continuous.comp_continuousOn (continuousOn_chartExt c.φ)
  obtain ⟨W, hWdef⟩ : ∃ W : Set M,
      W = (c.U : Set M) ∩ (fun y => E0.toPaper (chartExt c.φ y)) ⁻¹' interior V₀ := ⟨_, rfl⟩
  have hWo : IsOpen W := hWdef ▸ hφc.isOpen_inter_preimage c.U.isOpen isOpen_interior
  have hmW : m ∈ W := hWdef ▸ ⟨c.mem, mem_interior_iff_mem_nhds.2 hV₀n⟩
  have hWU : W ⊆ c.U := hWdef ▸ inter_subset_left
  have hWV₀ : ∀ y ∈ W, E0.toPaper (chartExt c.φ y) ∈ V₀ := fun y hy => by
    rw [hWdef] at hy; exact interior_subset hy.2
  refine ⟨W, hWo, hmW, fun Q hQW hQc u hu => ?_⟩
  obtain ⟨f, Ψ, hΨ, -, -, hVoB, hUo, hbij, hnat, hT'n, g, hg⟩ :=
    d.exists_liftedChart_of_isChartwise hd c hc u (hWU hu)
  have hSU : connectedComponentIn (SpreadEnd.base ⁻¹' W) u ⊆
      connectedComponentIn (SpreadEnd.base ⁻¹' (c.U : Set M)) u :=
    connectedComponentIn_mono _ (preimage_mono hWU)
  have hSW : connectedComponentIn ((SpreadEnd.base : MaxBranchedCover
      (Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) M) y₀ → M) ⁻¹' W) u ⊆
      SpreadEnd.base ⁻¹' W := connectedComponentIn_subset _ _
  have hfV : f ∈ connectedComponentIn ((SpreadEnd.base : MaxBranchedCover
      (Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0) yN → BTZE0) ⁻¹' (c.V : Set BTZE0)) f :=
    mem_connectedComponentIn hΨ.base_mem
  have hVo : IsOpen (connectedComponentIn ((SpreadEnd.base : MaxBranchedCover
      (Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0) yN → BTZE0) ⁻¹' (c.V : Set BTZE0)) f) :=
    (c.V.isOpen.preimage SpreadEnd.continuous_base).connectedComponentIn
  -- the inverse of the descent
  haveI : Nonempty (MaxBranchedCover (Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0) yN) :=
    ⟨f⟩
  obtain ⟨inv, hinvdef⟩ : ∃ inv : MaxBranchedCover (Sing (Causal.Flat.isom 2) (Causal.Minkowski 2)
      M) y₀ → MaxBranchedCover (Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0) yN,
      inv = Function.invFunOn Ψ (connectedComponentIn (SpreadEnd.base ⁻¹' (c.V : Set BTZE0)) f) :=
    ⟨_, rfl⟩
  have hinv : ∀ w ∈ connectedComponentIn (SpreadEnd.base ⁻¹' (c.U : Set M)) u,
      inv w ∈ connectedComponentIn (SpreadEnd.base ⁻¹' (c.V : Set BTZE0)) f ∧ Ψ (inv w) = w :=
    fun w hw => by
      have h := hbij.surjOn hw
      rw [hinvdef]
      exact ⟨Function.invFunOn_mem h, Function.invFunOn_eq h⟩
  have hinvΨ : ∀ v ∈ connectedComponentIn (SpreadEnd.base ⁻¹' (c.V : Set BTZE0)) f,
      inv (Ψ v) = v := fun v hv => by rw [hinvdef]; exact hbij.injOn.leftInvOn_invFunOn hv
  have hinvc : ∀ w ∈ connectedComponentIn (SpreadEnd.base ⁻¹' (c.U : Set M)) u,
      Tendsto inv (𝓝 w) (𝓝 (inv w)) := by
    intro w hw
    obtain ⟨hv, hΨv⟩ := hinv w hw
    have h : Tendsto inv (𝓝 (Ψ (inv w))) (𝓝 (inv w)) := by
      rw [hnat _ hv, tendsto_map'_iff]
      exact tendsto_id.congr' (Filter.eventually_of_mem (hVo.mem_nhds hv)
        fun v' hv' => (hinvΨ v' hv').symm)
    rwa [hΨv] at h
  have hΨc : ∀ v ∈ connectedComponentIn (SpreadEnd.base ⁻¹' (c.V : Set BTZE0)) f,
      Tendsto Ψ (𝓝 v) (𝓝 (Ψ v)) := fun v hv => by rw [hnat _ hv]; exact tendsto_map
  have hbase : ∀ w ∈ connectedComponentIn (SpreadEnd.base ⁻¹' (c.U : Set M)) u,
      (inv w).base = chartExt c.φ w.base := fun w hw => by
    have h := hΨ.base (inv w) (hinv w hw).1
    rw [(hinv w hw).2] at h; exact h.symm
  -- the model point
  have hproj : ∀ w ∈ connectedComponentIn (SpreadEnd.base ⁻¹' (c.U : Set M)) u,
      orbitMk (GammaA (2 * π)) (Φ (inv w)) = chartExt c.φ w.base := fun w hw => by
    rw [d.isPresentation]; exact hbase w hw
  have hDy : ∀ w ∈ connectedComponentIn (SpreadEnd.base ⁻¹' (c.U : Set M)) u,
      d.D w = g • btzDevM 0 btzV0 (Φ (inv w)) := fun w hw => by
    have h := hg _ (hinv w hw).1; rw [(hinv w hw).2] at h; exact h
  have hyc : ∀ w ∈ connectedComponentIn (SpreadEnd.base ⁻¹' (c.U : Set M)) u,
      Tendsto (fun z => Φ (inv z)) (𝓝 w) (𝓝 (Φ (inv w))) := fun w hw =>
    (Φ.continuous.tendsto _).comp (hinvc w hw)
  refine ⟨fun 𝒰 h𝒰 => ?_, fun 𝒰 F G u' w' hFG hF hG hu' hw' => ?_⟩
  · -- (1) a limit, through the box of `𝔻_∞ × ℝ`
    have hev : ∀ᶠ z in (𝒰 : Filter _), z ∈ connectedComponentIn (SpreadEnd.base ⁻¹' W) u ∧
        z.base ∈ Q ∧ d.natCausality.le ⊤ a z ∧ d.natCausality.le ⊤ z b :=
      Filter.mem_of_superset h𝒰 fun z hz => ⟨hz.1, hz.2.1, hz.2.2⟩
    -- `D` is bounded on the diamond
    have hK : IsCompact ((Causal.minkowski 2).diamond ⊤ (g⁻¹ • d.D a) (g⁻¹ • d.D b)) :=
      Causal.minkowski_globallyHyperbolic.2 _ _
    obtain ⟨A, hA⟩ := (hK.image nullToMinkHomeomorph.symm.continuous).isBounded.exists_norm_le
    -- the time of the base point is bounded on `Q`
    have hTc : ContinuousOn (fun w : M => 2 * (E0.toPaper (chartExt c.φ w)).1) Q :=
      (continuous_const.mul continuous_fst).comp_continuousOn (hφc.mono (hQW.trans hWU))
    obtain ⟨C, hC⟩ := hQc.exists_bound_of_continuousOn hTc
    have hbox : ∀ᶠ z in (𝒰 : Filter _), Φ (inv z) ∈ {y : DInfty × ℝ | y.1.r ≤ A ∧
        y.1.r * y.1.θ ^ 2 ≤ 2 * A + C ∧ y.2 ∈ Icc (-C) C} := hev.mono fun z hz => by
      have hzU := hSU hz.1
      have h1 := (btzTilde_le_dev (N := d.Space) (D := d.D) (hD := d.isBTZTildeDev)
        ((d.natCausality_le_top_iff).1 hz.2.2.1)).1
      have h2 := (btzTilde_le_dev (N := d.Space) (D := d.D) (hD := d.isBTZTildeDev)
        ((d.natCausality_le_top_iff).1 hz.2.2.2)).1
      have h1' : (Causal.minkowski 2).le ⊤ (d.D a) (d.D z) := h1
      have h2' : (Causal.minkowski 2).le ⊤ (d.D z) (d.D b) := h2
      rw [hDy z hzU] at h1' h2'
      have hmem : btzDevM 0 btzV0 (Φ (inv z)) ∈
          (Causal.minkowski 2).diamond ⊤ (g⁻¹ • d.D a) (g⁻¹ • d.D b) := by
        refine Causal.Causality.mem_diamond.2 ⟨?_, ?_⟩
        · have := (Causal.Flat.isom_le_top_iff g⁻¹).2 h1'
          rwa [inv_smul_smul] at this
        · have := (Causal.Flat.isom_le_top_iff g⁻¹).2 h2'
          rwa [inv_smul_smul] at this
      have hnorm := hA _ ⟨_, hmem, rfl⟩
      rw [coe_nullToMinkHomeomorph_symm, btzDevM, LinearEquiv.symm_apply_apply, btzDev_coords]
        at hnorm
      have hn1 := (norm_fst_le _).trans hnorm
      have hn2 := ((norm_fst_le _).trans (norm_snd_le _)).trans hnorm
      simp only [btzV0, Prod.fst_zero, Prod.snd_zero, Real.norm_eq_abs] at hn1 hn2
      have ht : (Φ (inv z)).2 = 2 * (E0.toPaper (chartExt c.φ z.base)).1 := by
        rw [← hproj z hzU, E0LM.toPaper_orbitMk_fst]; ring
      have htC := hC _ hz.2.1
      rw [Real.norm_eq_abs, ← ht] at htC
      obtain ⟨hr1, hr2⟩ := abs_le.1 hn2
      obtain ⟨ha1, ha2⟩ := abs_le.1 hn1
      obtain ⟨ht1, ht2⟩ := abs_le.1 htC
      refine ⟨by linarith, by linarith, ht1, ht2⟩
    obtain ⟨yL, -, hyL⟩ := (isCompact_btzBox A (2 * A + C) (-C) C).ultrafilter_le_nhds
      (𝒰.map fun z => Φ (inv z)) (by
        rw [Ultrafilter.coe_map, le_principal_iff, mem_map]; exact hbox)
    rw [Ultrafilter.coe_map] at hyL
    have hinvt : Tendsto inv 𝒰 (𝓝 (Φ.symm yL)) :=
      ((Φ.symm.continuous.tendsto yL).comp hyL).congr fun z => Φ.symm_apply_apply _
    -- the limit lies in `V̂`
    have hQi : IsCompact (chartExt c.φ '' Q) :=
      hQc.image_of_continuousOn ((continuousOn_chartExt c.φ).mono (hQW.trans hWU))
    have hbaseL : (Φ.symm yL).base ∈ chartExt c.φ '' Q :=
      hQi.isClosed.mem_of_tendsto ((SpreadEnd.continuous_base.tendsto _).comp hinvt)
        (hev.mono fun z hz => by
          show (inv z).base ∈ _
          rw [hbase z (hSU hz.1)]; exact ⟨_, hz.2.1, rfl⟩)
    have hvL : Φ.symm yL ∈ connectedComponentIn (SpreadEnd.base ⁻¹' (c.V : Set BTZE0)) f := by
      haveI : (Filter.map inv (𝒰 : Filter _)).NeBot := Filter.map_neBot
      refine LiftGH.mem_connectedComponentIn_of_le_nhds
        (c.V.isOpen.preimage SpreadEnd.continuous_base) hinvt ?_ ?_
      · obtain ⟨q, hq, hqe⟩ := hbaseL
        rw [mem_preimage, ← hqe]
        exact mapsTo_chartExt c.φ (hWU (hQW hq))
      · rw [mem_map]
        exact hev.mono fun z hz => (hinv z (hSU hz.1)).1
    -- its image by `Ψ` is the limit
    have hid : (𝒰 : Filter _) ≤ 𝓝 (Ψ (Φ.symm yL)) := by
      have h := (hΨc _ hvL).comp hinvt
      have h2 : Tendsto (fun z => z) (𝒰 : Filter _) (𝓝 (Ψ (Φ.symm yL))) :=
        h.congr' (hev.mono fun z hz => (hinv z (hSU hz.1)).2)
      exact tendsto_id'.1 h2
    have hwQ : (Ψ (Φ.symm yL)).base ∈ Q :=
      hQc.isClosed.mem_of_tendsto ((SpreadEnd.continuous_base.tendsto _).comp hid)
        (hev.mono fun z hz => hz.2.1)
    exact ⟨_, LiftGH.mem_connectedComponentIn_of_le_nhds
      (hWo.preimage SpreadEnd.continuous_base) hid (hQW hwQ) (hev.mono fun z hz => hz.1), hid⟩
  · -- (2) the order passes to the limit
    have hu'U := hSU hu'
    have hw'U := hSU hw'
    have hle : ∀ᶠ e in (𝒰 : Filter _), BtzDevLe (Φ (inv (F e))) (Φ (inv (G e))) :=
      hFG.mono fun e he => by
        have h := (btzTilde_le_dev (N := d.Space) (D := d.D) (hD := d.isBTZTildeDev)
          ((d.natCausality_le_top_iff).1 he.2.2)).1
        have h' : (Causal.minkowski 2).le ⊤ (d.D (F e)) (d.D (G e)) := h
        rw [hDy _ (hSU he.1.1), hDy _ (hSU he.2.1.1), Causal.Flat.isom_le_top_iff] at h'
        exact (btzDevM_le_iff _ _).1 h'
    have hlim : BtzDevLe (Φ (inv u')) (Φ (inv w')) :=
      isClosed_btzDevLe.mem_of_tendsto
        (((hyc u' hu'U).comp hF).prodMk_nhds ((hyc w' hw'U).comp hG)) hle
    -- the chart of `Û`
    obtain ⟨κ, hκA, hκs, hκΨ, hκt⟩ := LiftGH.exists_chart_of_descent (E := d.Space) (D := d.D)
      Φ.toEquiv hVoB (TopologicalSpace.le_def.1 d.le_natural _ hUo) hbij hT'n hg ⟨f, hfV⟩
    have hκu : ∀ w ∈ connectedComponentIn (SpreadEnd.base ⁻¹' (c.U : Set M)) u,
        κ (d.fromNat w) = btzJDev (0 : ℝ × ℝ × ℝ) btzV0 btzV0_pos (Φ (inv w)) := fun w hw => by
      have h := hκΨ _ (hinv w hw).1
      rw [(hinv w hw).2] at h; exact h
    have hlink : btzJLe (κ (d.fromNat u')) (κ (d.fromNat w')) := by
      show (Causal.minkowski 2).le ⊤ (κ (d.fromNat u')).val (κ (d.fromNat w')).val
      rw [hκu u' hu'U, hκu w' hw'U, btzJDev_val, btzJDev_val, btzDevM_le_iff]; exact hlim
    -- the model inverse
    set js : BTZJ0 → DInfty × ℝ := ⇑(btzJDevEquiv (0 : ℝ × ℝ × ℝ) btzV0 btzV0_pos).symm
      with hjsdef
    have hjs : Continuous[btzJTop 0, hornTop] js := continuous_btzJDevEquiv_symm btzV0_pos
    have hjs' : Continuous js := continuous_le_rng hornTop_le hjs
    have hjv : ∀ q : BTZJ0, btzDevM 0 btzV0 (js q) = q.val := fun q =>
      (btzJDev_val (x₀ := (0 : ℝ × ℝ × ℝ)) btzV0_pos (js q)).symm.trans
        (congrArg BTZJplus.val ((btzJDevEquiv (0 : ℝ × ℝ × ℝ) btzV0 btzV0_pos).apply_symm_apply q))
    have hjsj : ∀ y, js (btzJDev (0 : ℝ × ℝ × ℝ) btzV0 btzV0_pos y) = y := fun y =>
      (btzJDevEquiv (0 : ℝ × ℝ × ℝ) btzV0 btzV0_pos).symm_apply_apply y
    -- the segment projects into `V₀`
    have hV₀ : ∀ s ∈ Icc (0 : ℝ) 1,
        E0.toPaper (orbitMk (GammaA (2 * π)) (js (btzJSeg hlink s))) ∈ V₀ := by
      intro s hs
      have hp₁ : E0.toPaper (orbitMk (GammaA (2 * π)) (Φ (inv u'))) ∈ V₀ := by
        rw [hproj u' hu'U]; exact hWV₀ _ (hSW hu')
      have hp₂ : E0.toPaper (orbitMk (GammaA (2 * π)) (Φ (inv w'))) ∈ V₀ := by
        rw [hproj w' hw'U]; exact hWV₀ _ (hSW hw')
      have h1 : (Causal.minkowski 2).le ⊤ (btzDevM 0 btzV0 (Φ (inv u')))
          (btzDevM 0 btzV0 (js (btzJSeg hlink s))) := by
        rw [hjv, btzJSeg_val, ← btzJDev_val (x₀ := (0 : ℝ × ℝ × ℝ)) btzV0_pos, ← hκu u' hu'U,
          ← btzJSegPt_zero (κ (d.fromNat u')) (κ (d.fromNat w'))]
        exact btzJ_le_segPt hlink hs.1
      have h2 : (Causal.minkowski 2).le ⊤ (btzDevM 0 btzV0 (js (btzJSeg hlink s)))
          (btzDevM 0 btzV0 (Φ (inv w'))) := by
        rw [hjv, btzJSeg_val, ← btzJDev_val (x₀ := (0 : ℝ × ℝ × ℝ)) btzV0_pos, ← hκu w' hw'U,
          ← btzJSegPt_one (κ (d.fromNat u')) (κ (d.fromNat w'))]
        exact btzJ_le_segPt hlink hs.2
      exact hV₀c.2 _ hp₁ _ hp₂ (Causal.Causality.mem_diamond.2
        ⟨E0.le_top_iff.2 (e0Le_of_btzDevM_le h1), E0.le_top_iff.2 (e0Le_of_btzDevM_le h2)⟩)
    -- hence the segment stays in `V̂`
    have hγc : ContinuousOn (fun s => Φ.symm (js (btzJSeg hlink s))) (Icc 0 1) :=
      Φ.symm.continuous.comp_continuousOn (hjs'.comp_continuousOn (btzJ_continuousOn_seg hlink))
    have hγsub : (fun s => Φ.symm (js (btzJSeg hlink s))) '' Icc 0 1 ⊆
        SpreadEnd.base ⁻¹' (c.V : Set BTZE0) := by
      rintro _ ⟨s, hs, rfl⟩
      obtain ⟨x, hx, hxe⟩ := hV₀O (hV₀ s hs)
      rw [mem_preimage, ← d.isPresentation, Φ.apply_symm_apply, ← E0.toPaper.injective hxe]
      exact hx
    have hγ0 : Φ.symm (js (btzJSeg hlink 0)) = inv u' := by
      rw [btzJSeg_zero, hκu u' hu'U, hjsj, Φ.symm_apply_apply]
    have hγV : ∀ s ∈ Icc (0 : ℝ) 1, Φ.symm (js (btzJSeg hlink s)) ∈
        connectedComponentIn (SpreadEnd.base ⁻¹' (c.V : Set BTZE0)) f := by
      intro s hs
      have h : Φ.symm (js (btzJSeg hlink s)) ∈ connectedComponentIn
          (SpreadEnd.base ⁻¹' (c.V : Set BTZE0)) (Φ.symm (js (btzJSeg hlink 0))) :=
        (isPreconnected_Icc.image _ hγc).subset_connectedComponentIn
          ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩ hγsub ⟨s, hs, rfl⟩
      rwa [hγ0, ← connectedComponentIn_eq (hinv u' hu'U).1] at h
    have hseg : ∀ s ∈ Icc (0 : ℝ) 1,
        btzJSeg hlink s ∈ Causal.chartImage κ (⊤ ⊓ Causal.chartSource κ) := by
      intro s hs
      have hmem' : btzJSeg hlink s ∈ κ.target := hκt _ (hγV s hs)
      exact ⟨κ.symm (btzJSeg hlink s), ⟨κ.map_target hmem', trivial, κ.map_target hmem'⟩,
        κ.right_inv hmem'⟩
    have hu'κ : d.fromNat u' ∈ κ.source := by rw [hκs]; exact hu'U
    have hw'κ : d.fromNat w' ∈ κ.source := by rw [hκs]; exact hw'U
    have hle' : d.causality.le ⊤ (d.fromNat u') (d.fromNat w') :=
      btzTildeAtlasCausality_le_of_link (hA := d.isBTZTildeDev) hκA
        (btzTilde_link_le_iff.2 ⟨⟨trivial, hu'κ⟩, ⟨trivial, hw'κ⟩,
          0, 1, zero_le_one, btzJSeg hlink, btzJ_curveOn_seg hlink hseg, btzJSeg_zero hlink,
          btzJSeg_one hlink⟩)
    exact (d.natCausality_le_top_iff).2 hle'

/-- **DEC-118 (b): if `M` is globally hyperbolic, so is `\widetilde M` in its natural topology**
(DEC-106), for the chartwise `\widetilde M` (DEC-118 (c); `exists_isChartwise`): `natCausality` is
causal and its diamonds are compact (`isCompact_natDiamond_of_liftLocalData`, local data over
`reg M` `liftLocalData_reg`, over `sing M` `liftLocalData_sing_of_isChartwise`). -/
theorem natGloballyHyperbolic_of_base (hd : d.IsChartwise) (hM : IsBTZSingModelled M)
    (hG : (e0ManifoldCausality M hM).GloballyHyperbolic) : d.natCausality.GloballyHyperbolic := by
  refine ⟨d.natCausality_isCausal, fun a b =>
    d.isCompact_natDiamond_of_liftLocalData hM hG a b fun m _ => ?_⟩
  by_cases hm : m ∈ Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) M
  · exact d.liftLocalData_sing_of_isChartwise hd hM a b hm
  · obtain ⟨W, hW, hmW, hL⟩ := d.liftLocalData_reg (m := m) (by simpa [Sing] using hm)
    exact ⟨W, hW, hmW, hL _⟩

/-- **The regular case, with no `sorry`**: if `M` is globally hyperbolic and the diamond
`J(p a, p b)` of `M` avoids `sing M`, the natural diamond `J(a, b)` of `\widetilde M` is compact
(the finite-sheet half alone, `liftLocalData_reg`). -/
theorem isCompact_natDiamond_of_base_of_subset_reg (hM : IsBTZSingModelled M)
    (hG : (e0ManifoldCausality M hM).GloballyHyperbolic)
    (a b : MaxBranchedCover (Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) M) y₀)
    (hab : (e0ManifoldCausality M hM).diamond ⊤ a.base b.base ⊆
      Reg (Causal.Flat.isom 2) (Causal.Minkowski 2) M) :
    IsCompact (d.natCausality.diamond ⊤ a b) :=
  d.isCompact_natDiamond_of_liftLocalData hM hG a b fun m hm => by
    obtain ⟨W, hW, hmW, hL⟩ := d.liftLocalData_reg (hab hm)
    exact ⟨W, hW, hmW, hL _⟩

/-- **`M` globally hyperbolic without BTZ line ⇒ `\widetilde M` globally hyperbolic, with no
`sorry`**: when `sing M = ∅`, `\widetilde M` is the universal cover of `M` and the regular case
applies to every diamond. -/
theorem natGloballyHyperbolic_of_base_of_sing_eq_empty (hM : IsBTZSingModelled M)
    (hG : (e0ManifoldCausality M hM).GloballyHyperbolic)
    (hS : Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) M = ∅) :
    d.natCausality.GloballyHyperbolic :=
  ⟨d.natCausality_isCausal, fun a b => d.isCompact_natDiamond_of_base_of_subset_reg hM hG a b
    fun m _ => by
      have : m ∉ Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) M := by rw [hS]; exact id
      simpa [Sing] using this⟩

/-- **The paper's route of `lem:globally_hyperbolic_manifolds_maximal`** (l.2361: "`M` GH ⇒
`\widetilde M` GH ⇒ future distinguishing"), in the ruled readings (DEC-106 for GH, DEC-118 (a)
for FD): through `natGloballyHyperbolic_of_base` and
`isFutureDistinguishing_of_natGloballyHyperbolic`. The statement itself is also
`isFutureDistinguishing_of_base` (`GX.BTZ.Manifolds`, proved directly, no `sorry`). -/
theorem isFutureDistinguishing_of_base_viaNatGH (hd : d.IsChartwise) (hM : IsBTZSingModelled M)
    (hG : (e0ManifoldCausality M hM).GloballyHyperbolic) : IsFutureDistinguishing d.causality :=
  d.isFutureDistinguishing_of_natGloballyHyperbolic (d.natGloballyHyperbolic_of_base hd hM hG)

end BTZTildeData

/-- **Non-vacuity of the `\widetilde{BTZ}` half of `lem:globally_hyperbolic_manifolds_manifolds`**
(DEC-118 (b)): for every globally hyperbolic `𝔼₀`-manifold `M`, every base point and every
presentation `Φ` of `\widetilde{𝔼₀}`, the chartwise datum `\widetilde M` (the one
`BTZTildeData.nonempty` constructs) is globally hyperbolic in its natural topology. -/
theorem exists_btzTildeData_natGloballyHyperbolic (hM : IsBTZSingModelled M)
    (hG : (e0ManifoldCausality M hM).GloballyHyperbolic)
    (y₀ : ((Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) M)ᶜ : Set M))
    {yN : ((Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0)ᶜ : Set BTZE0)}
    {Φ : MaxBranchedCover (Sing (Causal.Flat.isom 2) (Causal.Minkowski 2) BTZE0) yN ≃ₜ DInfty × ℝ}
    (hΦ : ∀ e, orbitMk (GammaA (2 * π)) (Φ e) = e.base) :
    ∃ d : BTZTildeData M y₀ Φ, d.IsChartwise ∧ d.natCausality.GloballyHyperbolic :=
  let ⟨d, hd⟩ := BTZTildeData.exists_isChartwise (y₀ := y₀) hM hΦ
  ⟨d, hd, d.natGloballyHyperbolic_of_base hd hM hG⟩

end TildeLift

end GX
