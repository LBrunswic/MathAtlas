import Causal.Geroch
import Causal.CauchySeparation

/-!
# The generalised Geroch theorem, repaired by local causal closedness (DEC-148)

`theo:geroch` — `ETT.tex:1256` (statement l.1256–1267; (iii)⇒(i) l.1301–1306). **Not marked**:
the repaired (iii)⇒(i) is proved sorry-free only under two hypotheses the paper does not have
(causal openness, chronal cones); in the form the author ruled (DEC-148) it rests on one `sorry`
(SCOPE). `theo:geroch_sing` — `ETT.tex:1771` — is not certified here: its (iii)⇒(i) under DEC-149
is `CausalScaffold.GerochIIIImpI`, from this file's engine. `theo:geroch_mr` (`ETT.tex:1002`) is
cited by the paper and not formalized (no Lorentzian manifolds).

> Let $M$ be a metrizable, locally compact topological spacetime. Assume moreover that $M$ is
> tarentin, causally arc-connected and locally causally convex, and that $J^\pm(p)\neq \{p\}$ for
> every $p\in M$. If $M$ admits a pair $(\mu_+,\mu_-)$ of measures admissible respectively in the
> future and in the past, then the following are equivalent: (i) $M$ is globally hyperbolic;
> (ii) $M$ admits a Cauchy time function; (iii) $M$ admits a Cauchy hypersurface.

> \underline{$(iii)\Rightarrow(i)$} This step is technical and uses the notion of quasi-limit of a
> sequence of causal curves (Definition 7, p.~407 of \cite{oneil}). [...] That proof carries over
> verbatim under the hypotheses of metrizability and local compactness.

The printed step is false (OQ-32: chronological Minkowski space, `CausalScaffold.GerochCauchy`).
DEC-148 rules repair (b): **local causal closedness**, `≤` closed near every point (O'Neill's use;
`lem:densite_modele` in the models). Read here as `LocallyCausallyClosed`: every point has an open
neighbourhood `U` with `≤_U` closed in `U × U`.

## What is proved

* `LocallyCausallyClosed` is implied by a closed relation (`locallyCausallyClosed_of_isClosed_le`),
  hence by (i) on a tarentin Hausdorff `M` (`GloballyHyperbolic.locallyCausallyClosed`); it is
  time-symmetric; with strong causality and causal arc-connectedness it closes the **global**
  relation on arbitrarily small compact neighbourhoods (`LocallyCausallyClosed.exists_isCompact`).
* **The engine** `globallyHyperbolic_of_isCauchySurface_of_isOpen`, sorry-free, with no limit
  curve, no quasi-limit and no time function: a second countable, locally compact, metrizable
  spacetime, causally arc-connected, strongly causal and locally causally closed, in which `J^∓` of
  every open set is open, with a Cauchy surface `S` such that `J^±(S)` are closed, is globally
  hyperbolic. In particular `J⁻(q) ∩ J⁺(S)` is compact (`exists_isCompact_Jminus_inter_Jplus`,
  with `isClosed_Jplus_singleton_of_isCauchySurface`): OQ-32's second question, under these terms.
* **Repaired `theo:geroch`, sorry-free**: `geroch_of_locallyCausallyClosed_of_causallyOpen`, the
  paper's hypotheses with local causal closedness, causal openness (DEC-8) and `I^±(x) ≠ ∅`.
* **Repaired `theo:geroch` as ruled**: `geroch_of_locallyCausallyClosed`, the paper's hypotheses
  with local causal closedness; (iii)⇒(i) (`geroch_iii_imp_i_of_locallyCausallyClosed`) is its
  one `sorry`. `geroch_tfae_locallyCausallyClosed`: (i) ⇔ (ii) ∧ L ⇔ (iii) ∧ L.
* Local causal closedness cannot be dropped: chronological Minkowski space has every other
  hypothesis of the engine and of the sorry-free form, and is not GH
  (`CausalScaffold.GerochIIIImpI`: `chronoMinkowski_not_locallyCausallyClosed`).

## Hypothesis checklist (`geroch_of_locallyCausallyClosed`)

| paper hypothesis | here |
|---|---|
| metrizable, locally compact | ✓ carried |
| a topological spacetime: Hausdorff, second countable (`ETT.tex:255`) | ✓ carried (`SecondCountableTopology M`; T2 from metrizability) |
| tarentin, causally arc-connected, `J^±(p) ≠ {p}` | ✓ carried |
| locally causally convex | ⚠ reading: `StronglyCausal` (DEC-7) |
| a pair `(μ₊, μ₋)` | ✓ carried; `BorelSpace M` |
| local causal closedness (DEC-148) | ✓ carried (ruled); ⚠ reading of "closed near every point" (SCOPE) |
| (ii) DEC-15; (iii) DEC-14 | ✓ carried |
| — (`geroch_of_locallyCausallyClosed_of_causallyOpen` only) | ⚠ strengthened: `CausallyOpen`, `NonemptyChronalCones` |

## SCOPE (disclosed)

* **Two `sorry`s.** The repaired one is `geroch_iii_imp_i_of_locallyCausallyClosed` (the other is
  the printed form's, below). The engine gives it as soon
  as `J^∓(W)` is open for open `W` and `J^±(S)` is closed. The first enters only through
  `PastUnboundedAt.of_le` and its time reversal (the past-unbounded points form a future set).
  The second the
  library derives only from chronology at every point (`sigma_separe_of_nonemptyChronalCones`)
  or from `SingularFlatAxioms`. Neither is a hypothesis of `theo:geroch`; whether (iii)⇒(i) holds
  with local causal closedness alone is open.
* **Reading of DEC-148**: `∃` one open `U ∋ p` with `≤_U` closed in `U × U`; a closed `≤_M`
  gives it with `U = M`. With strong causality and causal arc-connectedness it implies DEC-148's
  literal « `≤_M` closed near every point », which is all the engine uses; the converse is not
  shown (it seems to need open causally convex neighbourhoods), so this reading is not established
  as the weakest. Stating the engine with the literal form would change no proof.
* **The printed forms** `geroch_iii_imp_i`, `geroch_tfae_strict`, `geroch` are false
  (`Causal.not_gerochIIIImpIAsPrinted`, `Causal.not_geroch_tfae`); their `sorry` cannot be
  discharged. They are kept, statements unchanged, because `CausalScaffold.SingularGeroch` and the
  curation cite them.
* **Twins**: `PastUnboundedAt` is `Causal.Flat.CBGCompact`'s `PastNoncompactAt`, and
  `exists_mem_frontier_of_le_of_notMem` its `exists_frontier_of_le`, restated because that module
  imports models; this module is ETT layer (`Causal.Geroch`, `Causal.CauchySeparation`).
* The witnesses `timelikeLine_engine_hypotheses` and
  `timelikeLine_geroch_of_locallyCausallyClosed_of_causallyOpen` show the hypotheses satisfiable.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Filter MeasureTheory Metric

universe u

namespace Causality

/-! ### Local causal closedness (DEC-148) -/

section LocalClosedness

variable {M : Type*} [TopologicalSpace M] {C : Causality M} {U : Opens M} {x y p : M}

variable (C) in
/-- **`≤_U` is closed in `U × U`**: a pair of points of `U` in the closure of the causal relation
of `U` is related in `U`. -/
def IsCausallyClosedOn (U : Opens M) : Prop :=
  closure {z : M × M | C.le U z.1 z.2} ∩ ((U : Set M) ×ˢ (U : Set M)) ⊆
    {z : M × M | C.le U z.1 z.2}

variable (C) in
/-- **Local causal closedness** (DEC-148, read): every point has an open neighbourhood `U` whose
causal relation `≤_U` is closed in `U × U` (O'Neill's convex neighbourhoods, `lem:densite_modele`
in the models). -/
def LocallyCausallyClosed : Prop :=
  ∀ p : M, ∃ U : Opens M, p ∈ U ∧ C.IsCausallyClosedOn U

/-- On `M` itself, `≤_M` closed in `M × M` is the closedness of the causal relation. -/
theorem isCausallyClosedOn_top :
    C.IsCausallyClosedOn ⊤ ↔ IsClosed {z : M × M | C.le ⊤ z.1 z.2} := by
  simp only [IsCausallyClosedOn, Opens.coe_top, univ_prod_univ, inter_univ]
  exact closure_subset_iff_isClosed

/-- A closed causal relation is locally closed (`U = M`). -/
theorem locallyCausallyClosed_of_isClosed_le (hle : IsClosed {z : M × M | C.le ⊤ z.1 z.2}) :
    C.LocallyCausallyClosed :=
  fun _ => ⟨⊤, trivial, isCausallyClosedOn_top.2 hle⟩

/-- **(i) implies local causal closedness** on a tarentin Hausdorff spacetime
(`prop:GH_Jferme`, through `GloballyHyperbolic.isClosed_le`). -/
theorem GloballyHyperbolic.locallyCausallyClosed [T2Space M] (hT : C.Tarentin)
    (hG : C.GloballyHyperbolic) : C.LocallyCausallyClosed :=
  locallyCausallyClosed_of_isClosed_le (hG.isClosed_le hT)

/-- Time reversal (kb/0002): `≤_U` closed iff its reverse is. -/
theorem IsCausallyClosedOn.dual (h : C.IsCausallyClosedOn U) : C.dual.IsCausallyClosedOn U := by
  rintro ⟨a, b⟩ ⟨hcl, ha, hb⟩
  have h' : Prod.swap ((a, b) : M × M) ∈ closure {z : M × M | C.le U z.1 z.2} :=
    map_mem_closure continuous_swap hcl fun z hz => hz
  exact h ⟨h', hb, ha⟩

theorem dual_isCausallyClosedOn : C.dual.IsCausallyClosedOn U ↔ C.IsCausallyClosedOn U :=
  ⟨fun h => h.dual, fun h => h.dual⟩

theorem dual_locallyCausallyClosed : C.dual.LocallyCausallyClosed ↔ C.LocallyCausallyClosed :=
  ⟨fun h p => let ⟨U, hp, hU⟩ := h p; ⟨U, hp, hU.dual⟩,
    fun h p => let ⟨U, hp, hU⟩ := h p; ⟨U, hp, hU.dual⟩⟩

/-- The filter form: limits of related points of `U`, both in `U`, are related in `U`. -/
theorem IsCausallyClosedOn.le_of_tendsto (h : C.IsCausallyClosedOn U) {ι : Type*} {l : Filter ι}
    [l.NeBot] {f g : ι → M} (hf : Tendsto f l (𝓝 x)) (hg : Tendsto g l (𝓝 y)) (hx : x ∈ U)
    (hy : y ∈ U) (hfg : ∀ᶠ i in l, C.le U (f i) (g i)) : C.le U x y :=
  h ⟨mem_closure_of_tendsto (hf.prodMk_nhds hg) hfg, hx, hy⟩

/-- **The global relation is closed near every point**: under strong causality and causal
arc-connectedness, local causal closedness gives arbitrarily small open `W ∋ p` on which `≤_M`
is closed in `W × W`. -/
theorem LocallyCausallyClosed.exists_isOpen (hL : C.LocallyCausallyClosed)
    (hSC : C.StronglyCausal) (hC : C.CausallyArcConnected) {N : Set M} (hN : N ∈ 𝓝 p) :
    ∃ W : Set M, IsOpen W ∧ p ∈ W ∧ W ⊆ N ∧
      closure {z : M × M | C.le ⊤ z.1 z.2} ∩ (W ×ˢ W) ⊆ {z : M × M | C.le ⊤ z.1 z.2} := by
  obtain ⟨U, hpU, hU⟩ := hL p
  obtain ⟨V, hV, hVN, hVc⟩ := hSC p (N ∩ U) (inter_mem hN (U.isOpen.mem_nhds hpU))
  have hVU : V ⊆ U := hVN.trans inter_subset_right
  refine ⟨interior V, isOpen_interior, mem_interior_iff_mem_nhds.2 hV,
    interior_subset.trans (hVN.trans inter_subset_left), ?_⟩
  rintro ⟨a, b⟩ ⟨hcl, ha, hb⟩
  have hsub : (interior V ×ˢ interior V) ∩ {z : M × M | C.le ⊤ z.1 z.2} ⊆
      {z : M × M | C.le U z.1 z.2} := by
    rintro ⟨c, d⟩ ⟨⟨hc, hd⟩, hcd⟩
    exact le_of_causallyConvexIn hC hVc hVU (interior_subset hc) (interior_subset hd) hcd
  have hmem : ((a, b) : M × M) ∈ closure {z : M × M | C.le U z.1 z.2} :=
    closure_mono hsub ((isOpen_interior.prod isOpen_interior).inter_closure ⟨⟨ha, hb⟩, hcl⟩)
  exact C.le_mono le_top (hU ⟨hmem, hVU (interior_subset ha), hVU (interior_subset hb)⟩)

/-- The compact form of `exists_isOpen`. -/
theorem LocallyCausallyClosed.exists_isCompact [LocallyCompactSpace M]
    (hL : C.LocallyCausallyClosed) (hSC : C.StronglyCausal) (hC : C.CausallyArcConnected)
    {N : Set M} (hN : N ∈ 𝓝 p) :
    ∃ K ∈ 𝓝 p, IsCompact K ∧ K ⊆ N ∧
      closure {z : M × M | C.le ⊤ z.1 z.2} ∩ (K ×ˢ K) ⊆ {z : M × M | C.le ⊤ z.1 z.2} := by
  obtain ⟨W, hWo, hpW, hWN, hWR⟩ := hL.exists_isOpen hSC hC hN
  obtain ⟨K, hK, hKW, hKc⟩ := local_compact_nhds (hWo.mem_nhds hpW)
  exact ⟨K, hK, hKc, hKW.trans hWN, fun z hz => hWR ⟨hz.1, hKW hz.2.1, hKW hz.2.2⟩⟩

end LocalClosedness

/-! ### (iii)⇒(i) without limit curves: the engine -/

section Engine

variable {M : Type*} [TopologicalSpace M] {C : Causality M}

variable (C) in
/-- `x` is **past-unbounded relative to `A`**: for every neighbourhood `V` of `x`, `J⁻(V) ∩ A`
lies in no compact set. -/
def PastUnboundedAt (A : Set M) (x : M) : Prop :=
  ∀ V ∈ 𝓝 x, ¬ ∃ K : Set M, IsCompact K ∧ C.Jminus ⊤ V ∩ A ⊆ K

/-- The past-unbounded points form a closed set. -/
theorem pastUnboundedAt_of_mem_closure {A : Set M} {x : M}
    (hx : x ∈ closure {y | C.PastUnboundedAt A y}) : C.PastUnboundedAt A x := by
  intro V hV hK
  obtain ⟨y, hyV, hy⟩ := mem_closure_iff_nhds.1 hx _ (interior_mem_nhds.2 hV)
  exact hy V (mem_interior_iff_mem_nhds.1 hyV) hK

/-- The past-unbounded points form a future set, when `J⁻` of an open set is open. -/
theorem PastUnboundedAt.of_le (hJo : ∀ W : Set M, IsOpen W → IsOpen (C.Jminus ⊤ W))
    {A : Set M} {x w : M} (hx : C.PastUnboundedAt A x) (hxw : C.le ⊤ x w) :
    C.PastUnboundedAt A w := by
  rintro V hV ⟨K, hK, hsub⟩
  refine hx (C.Jminus ⊤ (interior V))
    ((hJo _ isOpen_interior).mem_nhds ⟨w, mem_interior_iff_mem_nhds.2 hV, hxw⟩) ⟨K, hK, ?_⟩
  rintro y ⟨⟨v, ⟨w', hw', hvw'⟩, hyv⟩, hyA⟩
  exact hsub ⟨⟨w', interior_subset hw', C.le_trans hyv hvw'⟩, hyA⟩

/-- Exit through the frontier along a causal curve. -/
theorem exists_mem_frontier_of_le_of_notMem (hC : C.CausallyArcConnected) {N : Set M} {x ℓ : M}
    (hx : x ∉ N) (hℓ : ℓ ∈ interior N) (hxℓ : C.le ⊤ x ℓ) :
    ∃ z ∈ frontier N, C.le ⊤ x z ∧ C.le ⊤ z ℓ := by
  obtain ⟨γ, hγ, h0, h1⟩ := ((hC ⊤ le_rfl x ℓ).1).1 hxℓ
  have hcont : ContinuousOn γ (Icc 0 1) := CurveOn.continuousOn C.isRelFamily_le hγ
  have hpc : IsPreconnected (γ '' Icc 0 1) := isPreconnected_Icc.image γ hcont
  by_contra hne
  have hsub : γ '' Icc 0 1 ⊆ interior N ∪ (closure N)ᶜ := by
    rintro _ ⟨t, ht, rfl⟩
    by_cases hi : γ t ∈ interior N
    · exact Or.inl hi
    · refine Or.inr fun hcl => hne ⟨γ t, ⟨hcl, hi⟩, ?_, ?_⟩
      · rw [← h0]; exact hγ.le_of_le le_rfl ht.1 ht.2
      · rw [← h1]; exact hγ.le_of_le ht.1 ht.2 le_rfl
  have hdisj : Disjoint (interior N) (closure N)ᶜ :=
    disjoint_compl_right.mono_left (interior_subset.trans subset_closure)
  have hin := hpc.subset_left_of_subset_union isOpen_interior isClosed_closure.isOpen_compl hdisj
    hsub ⟨ℓ, ⟨1, ⟨zero_le_one, le_rfl⟩, h1⟩, hℓ⟩
  exact hx (interior_subset (hin ⟨0, ⟨le_rfl, zero_le_one⟩, h0⟩))

/-- On a closed `N` on which `≤_M` is closed, `N ∩ J⁻(y)` is closed for `y ∈ N`. -/
theorem isClosed_inter_setOf_le {N : Set M} (hNc : IsClosed N)
    (hNR : closure {z : M × M | C.le ⊤ z.1 z.2} ∩ (N ×ˢ N) ⊆ {z : M × M | C.le ⊤ z.1 z.2})
    {y : M} (hy : y ∈ N) : IsClosed (N ∩ {z | C.le ⊤ z y}) := by
  refine isClosed_of_closure_subset fun z hz => ?_
  have hzN : z ∈ N := hNc.closure_subset (closure_mono inter_subset_left hz)
  have hcl : (fun w : M => ((w, y) : M × M)) z ∈ closure {w : M × M | C.le ⊤ w.1 w.2} :=
    map_mem_closure (f := fun w : M => ((w, y) : M × M)) (continuous_id.prodMk continuous_const)
      hz fun w (hw : w ∈ N ∩ {z | C.le ⊤ z y}) => hw.2
  exact ⟨hzN, hNR ⟨hcl, hzN, hy⟩⟩

/-- **The step, relative to a closed future set `A`**: a past-unbounded `y` has a past-unbounded
`z ≤ y` in `A` on the frontier of any compact `N`, `y ∈ int N`, on which `≤_M` is closed. With
`A = J⁺(S)` this is `Causal.Flat.CBGCompact`'s step with its global closedness replaced by
closedness on `N × N`. -/
theorem exists_pastUnboundedAt_frontier [T2Space M] (hC : C.CausallyArcConnected) {A : Set M}
    (hAc : IsClosed A) (hAf : ∀ x ∈ A, ∀ z, C.le ⊤ x z → z ∈ A) {y : M}
    (hy : C.PastUnboundedAt A y) {N : Set M} (hN : IsCompact N) (hyN : y ∈ interior N)
    (hNR : closure {z : M × M | C.le ⊤ z.1 z.2} ∩ (N ×ˢ N) ⊆ {z : M × M | C.le ⊤ z.1 z.2}) :
    ∃ z ∈ frontier N, C.le ⊤ z y ∧ z ∈ A ∧ C.PastUnboundedAt A z := by
  by_contra hcon
  push Not at hcon
  have hNc : IsClosed N := hN.isClosed
  have hfrN : frontier N ⊆ N := frontier_subset_closure.trans hNc.closure_eq.subset
  have hyN' : y ∈ N := interior_subset hyN
  set Z := frontier N ∩ ((N ∩ {z | C.le ⊤ z y}) ∩ A) with hZdef
  have hZ : IsCompact Z := hN.of_isClosed_subset
    (isClosed_frontier.inter ((isClosed_inter_setOf_le hNc hNR hyN').inter hAc))
    (inter_subset_left.trans hfrN)
  have hgood : ∀ z ∈ Z, ∃ V ∈ 𝓝 z, ∃ K : Set M, IsCompact K ∧ C.Jminus ⊤ V ∩ A ⊆ K := by
    rintro z ⟨hzfr, ⟨-, hzy⟩, hzA⟩
    have := hcon z hzfr hzy hzA
    unfold PastUnboundedAt at this
    push Not at this
    exact this
  choose! V hV K hK hVK using hgood
  obtain ⟨t, htZ, hcov⟩ := hZ.elim_nhds_subcover (fun z => interior (V z))
    (fun z hz => interior_mem_nhds.2 (hV z hz))
  set W := ⋃ z ∈ t, interior (V z) with hWdef
  have hWo : IsOpen W := isOpen_biUnion fun _ _ => isOpen_interior
  set Kc := ⋃ z ∈ t, K z with hKcdef
  have hKc : IsCompact Kc := t.isCompact_biUnion fun z hz => hK z (htZ z hz)
  have hW : C.Jminus ⊤ W ∩ A ⊆ Kc := by
    rintro x ⟨⟨w, hw, hxw⟩, hxA⟩
    obtain ⟨z, hzt, hwz⟩ := mem_iUnion₂.1 hw
    exact mem_iUnion₂.2 ⟨z, hzt, hVK z (htZ z hzt) ⟨⟨w, interior_subset hwz, hxw⟩, hxA⟩⟩
  set F := frontier N ∩ A ∩ Wᶜ with hFdef
  have hF : IsCompact F := hN.of_isClosed_subset
    ((isClosed_frontier.inter hAc).inter hWo.isClosed_compl)
    (inter_subset_left.trans (inter_subset_left.trans hfrN))
  set Q := (F ×ˢ N) ∩ {z : M × M | C.le ⊤ z.1 z.2} with hQdef
  have hQc : IsClosed Q := by
    refine isClosed_of_closure_subset fun w hw => ?_
    have h1 : w ∈ F ×ˢ N :=
      (hF.isClosed.prod hNc).closure_subset (closure_mono inter_subset_left hw)
    exact ⟨h1, hNR ⟨closure_mono inter_subset_right hw, hfrN h1.1.1.1, h1.2⟩⟩
  have hQ : IsCompact Q := (hF.prod hN).of_isClosed_subset hQc inter_subset_left
  set P := Prod.snd '' Q with hPdef
  have hP : IsClosed P := (hQ.image continuous_snd).isClosed
  have hyP : y ∉ P := by
    rintro ⟨⟨z, ℓ⟩, ⟨⟨hzF, -⟩, hzℓ⟩, rfl⟩
    have hzZ : z ∈ Z := ⟨hzF.1.1, ⟨hfrN hzF.1.1, hzℓ⟩, hzF.1.2⟩
    exact hzF.2 (hcov hzZ)
  set L := interior N ∩ Pᶜ with hLdef
  have hL : L ∈ 𝓝 y := (isOpen_interior.inter hP.isOpen_compl).mem_nhds ⟨hyN, hyP⟩
  refine hy L hL ⟨(N ∩ A) ∪ Kc, (hN.inter_right hAc).union hKc, ?_⟩
  rintro x ⟨⟨ℓ, hℓL, hxℓ⟩, hxA⟩
  by_cases hxN : x ∈ N
  · exact Or.inl ⟨hxN, hxA⟩
  right
  obtain ⟨z, hzfr, hxz, hzℓ⟩ := exists_mem_frontier_of_le_of_notMem hC hxN hℓL.1 hxℓ
  have hzA : z ∈ A := hAf x hxA z hxz
  by_cases hzW : z ∈ W
  · exact hW ⟨⟨z, hzW, hxz⟩, hxA⟩
  · exact absurd ⟨(z, ℓ), ⟨⟨⟨⟨hzfr, hzA⟩, hzW⟩, interior_subset hℓL.1⟩, hzℓ⟩, rfl⟩ hℓL.2

/-- **The step for closedness**: a point `y` of `closure J⁺(p) ∖ J⁺(p)` has a point `z ≤ y` of
`closure J⁺(p) ∖ J⁺(p)` on the frontier of any compact `N`, `y ∈ int N`, on which `≤_M` is
closed. (`p ∉ N`, else `p ≤ y` by closedness; then a curve from `p` to a point of `J⁺(p)` near `y`
exits through the frontier.) -/
theorem exists_frontier_closure_Jplus [T2Space M] (hC : C.CausallyArcConnected) {p y : M}
    (hy : y ∈ closure (C.Jplus ⊤ {p})) (hy' : y ∉ C.Jplus ⊤ {p}) {N : Set M} (hN : IsCompact N)
    (hyN : y ∈ interior N)
    (hNR : closure {z : M × M | C.le ⊤ z.1 z.2} ∩ (N ×ˢ N) ⊆ {z : M × M | C.le ⊤ z.1 z.2}) :
    ∃ z ∈ frontier N, C.le ⊤ z y ∧ z ∈ closure (C.Jplus ⊤ {p}) ∧ z ∉ C.Jplus ⊤ {p} := by
  have hNc : IsClosed N := hN.isClosed
  have hfrN : frontier N ⊆ N := frontier_subset_closure.trans hNc.closure_eq.subset
  have hyN' : y ∈ N := interior_subset hyN
  -- `p ∉ N`: otherwise `(p, y)` is a limit of related pairs of `N × N`
  have hpN : p ∉ N := by
    intro hpN
    have hcl : (fun w : M => ((p, w) : M × M)) y ∈ closure {z : M × M | C.le ⊤ z.1 z.2} :=
      map_mem_closure (f := fun w : M => ((p, w) : M × M)) (continuous_const.prodMk continuous_id)
        hy fun w (hw : w ∈ C.Jplus ⊤ {p}) => Precausality.mem_Jplus_singleton.1 hw
    exact hy' (Precausality.mem_Jplus_singleton.2 (hNR ⟨hcl, hpN, hyN'⟩))
  by_contra hcon
  push Not at hcon
  set F := frontier N ∩ closure (C.Jplus ⊤ {p}) with hFdef
  have hF : IsCompact F := hN.of_isClosed_subset (isClosed_frontier.inter isClosed_closure)
    (inter_subset_left.trans hfrN)
  set Q := (F ×ˢ N) ∩ {z : M × M | C.le ⊤ z.1 z.2} with hQdef
  have hQc : IsClosed Q := by
    refine isClosed_of_closure_subset fun w hw => ?_
    have h1 : w ∈ F ×ˢ N :=
      (hF.isClosed.prod hNc).closure_subset (closure_mono inter_subset_left hw)
    exact ⟨h1, hNR ⟨closure_mono inter_subset_right hw, hfrN h1.1.1, h1.2⟩⟩
  have hQ : IsCompact Q := (hF.prod hN).of_isClosed_subset hQc inter_subset_left
  set P := Prod.snd '' Q with hPdef
  have hP : IsClosed P := (hQ.image continuous_snd).isClosed
  have hyP : y ∉ P := by
    rintro ⟨⟨z, ℓ⟩, ⟨⟨hzF, -⟩, hzℓ⟩, rfl⟩
    have hzJ := hcon z hzF.1 hzℓ hzF.2
    exact hy' (Precausality.mem_Jplus_singleton.2
      (C.le_trans (Precausality.mem_Jplus_singleton.1 hzJ) hzℓ))
  set L := interior N ∩ Pᶜ with hLdef
  have hL : L ∈ 𝓝 y := (isOpen_interior.inter hP.isOpen_compl).mem_nhds ⟨hyN, hyP⟩
  obtain ⟨y', hy'L, hy'J⟩ := mem_closure_iff_nhds.1 hy L hL
  have hpy' : C.le ⊤ p y' := Precausality.mem_Jplus_singleton.1 hy'J
  obtain ⟨z, hzfr, hpz, hzy'⟩ := exists_mem_frontier_of_le_of_notMem hC hpN hy'L.1 hpy'
  have hzF : z ∈ F := ⟨hzfr, subset_closure (Precausality.mem_Jplus_singleton.2 hpz)⟩
  exact hy'L.2 ⟨(z, y'), ⟨⟨hzF, interior_subset hy'L.1⟩, hzy'⟩, rfl⟩

/-- **A chain that does not converge**, general topology: if every point `y` of `P` has, for
every compact `N ∋ y` in whose interior it lies and on which `R` is closed, a point `z ∈ P ∩ ∂N`
with `(z, y) ∈ R`, then from any `x ∈ P` there is a sequence in `P`, each term `R`-below the
previous one and distinct from it, with no limit. The `N` are closed balls of a compatible metric
of radius half the largest admissible one, so a limit would force the steps to stay long. -/
theorem exists_antitone_chain [MetrizableSpace M] {R : Set (M × M)}
    (hloc : ∀ p : M, ∃ K ∈ 𝓝 p, IsCompact K ∧ closure R ∩ (K ×ˢ K) ⊆ R) {P : Set M}
    (hstep : ∀ y ∈ P, ∀ N : Set M, IsCompact N → y ∈ interior N → closure R ∩ (N ×ˢ N) ⊆ R →
      ∃ z ∈ frontier N, (z, y) ∈ R ∧ z ∈ P) {x : M} (hx : x ∈ P) :
    ∃ z : ℕ → M, z 0 = x ∧ (∀ k, z k ∈ P) ∧ (∀ k, (z (k + 1), z k) ∈ R) ∧
      (∀ k, z (k + 1) ≠ z k) ∧ ∀ y, ¬ Tendsto z atTop (𝓝 y) := by
  letI := metrizableSpaceMetric M
  set g : M → ℝ → Prop := fun a s => IsCompact (closedBall a s) ∧
    closure R ∩ (closedBall a s ×ˢ closedBall a s) ⊆ R with hg
  have hmono : ∀ {a b : M} {s t : ℝ}, g a s → closedBall b t ⊆ closedBall a s → g b t := by
    intro a b s t h hsub
    exact ⟨h.1.of_isClosed_subset isClosed_closedBall hsub,
      fun w hw => h.2 ⟨hw.1, hsub hw.2.1, hsub hw.2.2⟩⟩
  have hpos : ∀ a : M, ∃ s, 0 < s ∧ s ≤ 1 ∧ g a s := by
    intro a
    obtain ⟨K, hK, hKc, hKR⟩ := hloc a
    obtain ⟨ε, hε, hεK⟩ := Metric.mem_nhds_iff.1 hK
    refine ⟨min (ε / 2) 1, lt_min (half_pos hε) one_pos, min_le_right _ _, ?_⟩
    have hsub : closedBall a (min (ε / 2) 1) ⊆ K :=
      (closedBall_subset_ball (lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε))).trans hεK
    exact ⟨hKc.of_isClosed_subset isClosed_closedBall hsub,
      fun w hw => hKR ⟨hw.1, hsub hw.2.1, hsub hw.2.2⟩⟩
  set T : M → Set ℝ := fun a => {s | 0 < s ∧ s ≤ 1 ∧ g a s} with hT
  have hTbdd : ∀ a, BddAbove (T a) := fun a => ⟨1, fun s hs => hs.2.1⟩
  have hTne : ∀ a, (T a).Nonempty := fun a => let ⟨s, hs⟩ := hpos a; ⟨s, hs⟩
  set rad : M → ℝ := fun a => sSup (T a) / 2 with hrad
  have hrad_pos : ∀ a, 0 < rad a := by
    intro a
    obtain ⟨s, hs⟩ := hTne a
    have := le_csSup (hTbdd a) hs
    simp only [hrad]
    linarith [hs.1]
  have hrad_g : ∀ a, g a (rad a) := by
    intro a
    have hlt : rad a < sSup (T a) := by
      have := hrad_pos a
      simp only [hrad] at this ⊢
      linarith
    obtain ⟨s, hs, hlt'⟩ := exists_lt_of_lt_csSup (hTne a) hlt
    exact hmono hs.2.2 (closedBall_subset_closedBall hlt'.le)
  have hrad_ge : ∀ a s, s ∈ T a → s / 2 ≤ rad a := by
    intro a s hs
    have := le_csSup (hTbdd a) hs
    simp only [hrad]
    linarith
  have hnext : ∀ a : P, ∃ b : P, b.1 ∈ sphere a.1 (rad a.1) ∧ (b.1, a.1) ∈ R := by
    rintro ⟨a, ha⟩
    obtain ⟨b, hbfr, hbR, hbP⟩ := hstep a ha (closedBall a (rad a)) (hrad_g a).1
      (ball_subset_interior_closedBall (mem_ball_self (hrad_pos a))) (hrad_g a).2
    exact ⟨⟨b, hbP⟩, frontier_closedBall_subset_sphere hbfr, hbR⟩
  choose next hnext_sphere hnext_R using hnext
  let seq : ℕ → P := fun k => Nat.rec ⟨x, hx⟩ (fun _ a => next a) k
  have hseqS : ∀ k, seq (k + 1) = next (seq k) := fun k => rfl
  refine ⟨fun k => (seq k).1, rfl, fun k => (seq k).2, fun k => ?_, fun k => ?_, fun y hy => ?_⟩
  · simp only [hseqS]
    exact hnext_R _
  · intro heq
    have hd := hnext_sphere (seq k)
    rw [← hseqS, mem_sphere] at hd
    simp only at heq
    rw [heq, dist_self] at hd
    exact (hrad_pos _).ne hd
  · obtain ⟨s₀, hs₀, hs₀1, hgs₀⟩ := hpos y
    obtain ⟨K, hK⟩ := (Metric.tendsto_atTop.1 hy) (s₀ / 8) (by positivity)
    have hk : dist (seq K).1 y < s₀ / 8 := hK K le_rfl
    have hk1 : dist (seq (K + 1)).1 y < s₀ / 8 := hK (K + 1) (Nat.le_succ K)
    have hsub : closedBall (seq K).1 (s₀ / 2) ⊆ closedBall y s₀ :=
      closedBall_subset_closedBall' (by linarith)
    have hTK : s₀ / 2 ∈ T (seq K).1 := ⟨by positivity, by linarith, hmono hgs₀ hsub⟩
    have hge := hrad_ge _ _ hTK
    have hd := hnext_sphere (seq K)
    rw [mem_sphere, ← hseqS] at hd
    have htri := dist_triangle (seq (K + 1)).1 y (seq K).1
    rw [dist_comm y] at htri
    linarith

/-- **Concatenation of a chain**: a sequence `z (k+1) ≤ z k` lies on one causal curve over `ℝ`,
`c(-k) = z k`, constant `= z 0` on `[0, ∞)`. -/
theorem exists_causalCurveIn_univ_of_chain (hC : C.CausallyArcConnected) {z : ℕ → M}
    (hz : ∀ k, C.le ⊤ (z (k + 1)) (z k)) :
    ∃ c : ℝ → M, C.CausalCurveIn ⊤ univ c ∧ ∀ k : ℕ, c (-(k : ℝ)) = z k := by
  have hγ : ∀ k, ∃ γ : ℝ → M, C.CausalCurveOn ⊤ γ 0 1 ∧ γ 0 = z (k + 1) ∧ γ 1 = z k :=
    fun k => (hC ⊤ le_rfl _ _).1.1 (hz k)
  choose γ hγc hγ0 hγ1 using hγ
  set c : ℝ → M := fun t => if 0 ≤ t then z 0 else γ ⌊-t⌋₊ (t + ⌊-t⌋₊ + 1) with hcdef
  -- on `[-(k + 1), -k]`, `c` is `γ k` translated
  have hpiece : ∀ k : ℕ, ∀ t ∈ Icc (-((k : ℝ) + 1)) (-(k : ℝ)), c t = γ k (t + k + 1) := by
    intro k t ht
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    rcases eq_or_lt_of_le ht.1 with h | h
    · have ht0 : ¬ 0 ≤ t := by rw [← h]; linarith
      have hfl : ⌊-t⌋₊ = k + 1 := by
        rw [← h, neg_neg]
        exact_mod_cast Nat.floor_natCast (k + 1)
      simp only [hcdef, ht0, if_false, hfl]
      rw [← h]
      push_cast
      have e1 : -((k : ℝ) + 1) + ((k : ℝ) + 1) + 1 = 1 := by ring
      have e2 : -((k : ℝ) + 1) + (k : ℝ) + 1 = 0 := by ring
      rw [e1, e2, hγ1, hγ0]
    · by_cases ht0 : 0 ≤ t
      · have hk : k = 0 := by
          have : (k : ℝ) ≤ 0 := by linarith [ht.2]
          exact_mod_cast le_antisymm this hk0
        subst hk
        have ht' : t = 0 := by simp at ht; linarith [ht.2]
        subst ht'
        simp only [hcdef, le_refl, if_true]
        norm_num [hγ1]
      · simp only [hcdef, ht0, if_false]
        have hfl : ⌊-t⌋₊ = k := by
          rw [Nat.floor_eq_iff (by linarith)]
          constructor <;> linarith [ht.2, h]
        rw [hfl]
  have hseg : ∀ k : ℕ, C.CausalCurveOn ⊤ c (-((k : ℝ) + 1)) (-(k : ℝ)) := by
    intro k
    have h1 : C.CausalCurveOn ⊤ (γ k) (1 * (-((k : ℝ) + 1)) + ((k : ℝ) + 1))
        (1 * (-(k : ℝ)) + ((k : ℝ) + 1)) := by
      have e1 : 1 * (-((k : ℝ) + 1)) + ((k : ℝ) + 1) = 0 := by ring
      have e2 : 1 * (-(k : ℝ)) + ((k : ℝ) + 1) = 1 := by ring
      rw [e1, e2]
      exact hγc k
    refine (CurveOn.comp_affine one_pos h1).congr fun t ht => ?_
    simp only
    rw [hpiece k t ht]
    congr 1
    ring
  have hlong : ∀ n : ℕ, C.CausalCurveOn ⊤ c (-(n : ℝ)) 0 := by
    intro n
    induction n with
    | zero =>
      refine (causalCurveOn_const (show z 0 ∈ (⊤ : Opens M) from trivial)).congr
        fun t ht => ?_
      have : t = 0 := by simpa using ht
      subst this
      simp [hcdef]
    | succ n ih =>
      have h := CurveOn.concat C.isRelFamily_le (hseg n) ih (by linarith)
        (by simp) rfl
      push_cast
      exact h.congr fun t _ => by simp
  have hposit : ∀ b : ℝ, 0 ≤ b → C.CausalCurveOn ⊤ c 0 b := by
    intro b hb
    exact (causalCurveOn_const (show z 0 ∈ (⊤ : Opens M) from trivial)).congr
      fun t ht => by simp [hcdef, ht.1]
  refine ⟨c, ⟨univ_nonempty, ordConnected_univ, fun a _ b _ => ?_⟩, fun k => ?_⟩
  · rcases lt_or_ge b a with hba | hab
    · exact CurveOn.of_lt hba
    obtain ⟨n, hn⟩ := exists_nat_ge (-a)
    have hbig := CurveOn.concat C.isRelFamily_le (hlong n) (hposit (max b 0) (le_max_right _ _))
      (by linarith [Nat.cast_nonneg (α := ℝ) n]) (le_max_right _ _) rfl
    have hbig' : C.CausalCurveOn ⊤ c (-(n : ℝ)) (max b 0) := hbig.congr fun t _ => by simp
    exact hbig'.restrict (by linarith) (le_max_left _ _) le_rfl fun _ _ => trivial
  · rcases k with _ | j
    · simp [hcdef]
    · have := hpiece j (-((j : ℝ) + 1)) ⟨le_rfl, by linarith⟩
      push_cast
      rw [this]
      have e : -((j : ℝ) + 1) + (j : ℝ) + 1 = 0 := by ring
      rw [e, hγ0]

/-- **An inextensible curve above a chain without limit**: in a T1, second countable spacetime, a
strictly decreasing chain with no limit lies on an inextensible causal curve every point of which
is above some term of the chain (its parameters decrease to the lower end of the interval). -/
theorem exists_inextensible_above_chain [T1Space M] [SecondCountableTopology M]
    (hC : C.CausallyArcConnected) (hcaus : C.IsCausal) {z : ℕ → M}
    (hz : ∀ k, C.le ⊤ (z (k + 1)) (z k)) (hne : ∀ k, z (k + 1) ≠ z k)
    (hlim : ∀ y, ¬ Tendsto z atTop (𝓝 y)) :
    ∃ (J : Set ℝ) (G : ℝ → M), C.Inextensible ⊤ J G ∧ ∀ s ∈ J, ∃ k, C.le ⊤ (z k) (G s) := by
  obtain ⟨c, hc, hcz⟩ := exists_causalCurveIn_univ_of_chain hC hz
  obtain ⟨J, G, hG, hsub⟩ := exists_inextensible_of_t1_secondCountable hc
  have ht : ∀ k, ∃ t ∈ J, G t = z k := fun k => by
    obtain ⟨t, ht, e⟩ := hsub ⟨-(k : ℝ), trivial, hcz k⟩
    exact ⟨t, ht, e⟩
  choose t htJ htz using ht
  have hanti : ∀ k, t (k + 1) < t k := by
    intro k
    by_contra hle
    push Not at hle
    have h1 : C.le ⊤ (G (t k)) (G (t (k + 1))) := hG.1.le_of_le (htJ k) (htJ (k + 1)) hle
    rw [htz, htz] at h1
    exact hne k (hcaus (hz k) h1)
  refine ⟨J, G, hG, fun s hs => ?_⟩
  by_contra hno
  push Not at hno
  have hlt : ∀ k, s < t k := by
    intro k
    by_contra hle
    push Not at hle
    exact hno k (by rw [← htz k]; exact hG.1.le_of_le (htJ k) hs hle)
  have hA : StrictAnti t := strictAnti_nat_of_succ_lt hanti
  have hbdd : BddBelow (range t) := ⟨s, by rintro _ ⟨k, rfl⟩; exact (hlt k).le⟩
  have htend : Tendsto t atTop (𝓝 (⨅ k, t k)) := tendsto_atTop_ciInf hA.antitone hbdd
  have hst : s ≤ ⨅ k, t k := le_ciInf fun k => (hlt k).le
  have ht₀ : (⨅ k, t k) ≤ t 0 := ciInf_le hbdd 0
  have hcont : ContinuousOn G (Icc s (t 0)) :=
    CurveOn.continuousOn C.isRelFamily_le (hG.1.curve s hs (t 0) (htJ 0))
  have hmem : ∀ k, t k ∈ Icc s (t 0) := fun k => ⟨(hlt k).le, hA.antitone (Nat.zero_le k)⟩
  have hGt : Tendsto (fun k => G (t k)) atTop (𝓝 (G (⨅ k, t k))) :=
    (hcont _ ⟨hst, ht₀⟩).tendsto.comp
      (tendsto_nhdsWithin_iff.2 ⟨htend, Eventually.of_forall hmem⟩)
  exact hlim _ (by simpa [htz] using hGt)

/-- In a strongly causal spacetime a decreasing chain tends to each of its cluster points (the
sequence form of `tendsto_of_mapClusterPt`). -/
theorem tendsto_of_mapClusterPt_of_chain (hSC : C.StronglyCausal) {z : ℕ → M}
    (hz : ∀ k, C.le ⊤ (z (k + 1)) (z k)) {y : M} (hy : MapClusterPt y atTop z) :
    Tendsto z atTop (𝓝 y) := by
  have hmono : ∀ j k, j ≤ k → C.le ⊤ (z k) (z j) := by
    intro j k hjk
    induction hjk with
    | refl => exact C.le_refl trivial
    | step _ ih => exact C.le_trans (hz _) ih
  intro N hN
  obtain ⟨V, hV, hVN, hVc⟩ := hSC y N hN
  have hfreq := frequently_atTop.1 (mapClusterPt_iff_frequently.1 hy V hV)
  obtain ⟨k₁, -, hk₁⟩ := hfreq 0
  refine mem_map.2 (mem_atTop_sets.2 ⟨k₁, fun k hk => hVN ?_⟩)
  obtain ⟨k₂, hk₂, hk₂V⟩ := hfreq k
  exact hVc.2 _ hk₂V _ hk₁ (mem_diamond.2 ⟨hmono _ _ hk₂, hmono _ _ hk⟩)

variable [SecondCountableTopology M] [LocallyCompactSpace M] [MetrizableSpace M]

/-- **No point is past-unbounded relative to `J⁺(S)`**: a past-unbounded point would start a
chain of past-unbounded points without limit (`exists_antitone_chain`), whose inextensible curve
(`exists_inextensible_above_chain`) lies in the future set of past-unbounded points and meets `S`;
and no point of `S` is past-unbounded (the step, `S` acausal). -/
theorem not_pastUnboundedAt_of_isCauchySurface (hC : C.CausallyArcConnected)
    (hSC : C.StronglyCausal) (hL : C.LocallyCausallyClosed)
    (hJm : ∀ W : Set M, IsOpen W → IsOpen (C.Jminus ⊤ W)) {S : Set M}
    (hS : C.IsCauchySurface S) (hSp : IsClosed (C.Jplus ⊤ S)) (q : M) :
    ¬ C.PastUnboundedAt (C.Jplus ⊤ S) q := by
  have hcaus : C.IsCausal := hSC.isCausal
  have hac : C.IsAcausal S := hS.isAcausal_of_t1_secondCountable hC
  have hloc : ∀ p : M, ∃ K ∈ 𝓝 p, IsCompact K ∧
      closure {z : M × M | C.le ⊤ z.1 z.2} ∩ (K ×ˢ K) ⊆ {z : M × M | C.le ⊤ z.1 z.2} :=
    fun p => by
      obtain ⟨K, hK, hKc, -, hKR⟩ := hL.exists_isCompact hSC hC (p := p) univ_mem
      exact ⟨K, hK, hKc, hKR⟩
  have hAf : ∀ x ∈ C.Jplus ⊤ S, ∀ z, C.le ⊤ x z → z ∈ C.Jplus ⊤ S :=
    fun x ⟨σ, hσ, hσx⟩ z hxz => ⟨σ, hσ, C.le_trans hσx hxz⟩
  -- no point of `S` is past-unbounded
  have hBS : ∀ x ∈ S, ¬ C.PastUnboundedAt (C.Jplus ⊤ S) x := by
    intro x hxS hx
    obtain ⟨K, hK, hKc, hKR⟩ := hloc x
    obtain ⟨z, hzfr, hzx, ⟨σ, hσS, hσz⟩, -⟩ :=
      exists_pastUnboundedAt_frontier hC hSp hAf hx hKc (mem_interior_iff_mem_nhds.2 hK) hKR
    have hσx : σ = x := hac σ hσS x hxS (C.le_trans hσz hzx)
    subst hσx
    have hzx' : z = σ := hcaus hzx hσz
    subst hzx'
    exact hzfr.2 (mem_interior_iff_mem_nhds.2 hK)
  intro hq
  obtain ⟨z, -, hzB, hzR, hzne, hzlim⟩ :=
    exists_antitone_chain (R := {w : M × M | C.le ⊤ w.1 w.2}) hloc
      (P := {x | C.PastUnboundedAt (C.Jplus ⊤ S) x})
      (fun y hy N hN hyN hNR =>
        let ⟨z, hzfr, hzy, _, hzB⟩ := exists_pastUnboundedAt_frontier hC hSp hAf hy hN hyN hNR
        ⟨z, hzfr, hzy, hzB⟩) hq
  obtain ⟨J, G, hG, habove⟩ := exists_inextensible_above_chain hC hcaus hzR hzne hzlim
  obtain ⟨w, ⟨⟨s, hs, rfl⟩, hwS⟩, -⟩ := hS J G hG
  obtain ⟨k, hk⟩ := habove s hs
  exact hBS _ hwS (PastUnboundedAt.of_le hJm (hzB k) hk)

/-- **`J⁻(q) ∩ J⁺(S)` lies in a compact set** (OQ-32's compactness, bounded part). -/
theorem exists_isCompact_Jminus_inter_Jplus (hC : C.CausallyArcConnected)
    (hSC : C.StronglyCausal) (hL : C.LocallyCausallyClosed)
    (hJm : ∀ W : Set M, IsOpen W → IsOpen (C.Jminus ⊤ W)) {S : Set M}
    (hS : C.IsCauchySurface S) (hSp : IsClosed (C.Jplus ⊤ S)) (q : M) :
    ∃ K : Set M, IsCompact K ∧ C.Jminus ⊤ {q} ∩ C.Jplus ⊤ S ⊆ K := by
  have h := not_pastUnboundedAt_of_isCauchySurface hC hSC hL hJm hS hSp q
  unfold PastUnboundedAt at h
  push Not at h
  obtain ⟨V, hV, K, hK, hVK⟩ := h
  refine ⟨K, hK, fun x hx => hVK ⟨?_, hx.2⟩⟩
  exact ⟨q, mem_of_mem_nhds hV, Precausality.mem_Jminus_singleton.1 hx.1⟩

/-- **`J⁺(p)` is closed**: a point of `closure J⁺(p) ∖ J⁺(p)` would start a chain in that set
without limit (`exists_frontier_closure_Jplus`); the chain lies below it, in `J⁺(S)` or in
`closure J⁺(p) ∖ J⁺(S)`, hence in the compact sets of `exists_isCompact_Jminus_inter_Jplus` and
of its time reversal, so it has a cluster point, to which it tends by strong causality. -/
theorem isClosed_Jplus_singleton_of_isCauchySurface (hC : C.CausallyArcConnected)
    (hSC : C.StronglyCausal) (hL : C.LocallyCausallyClosed)
    (hJm : ∀ W : Set M, IsOpen W → IsOpen (C.Jminus ⊤ W))
    (hJp : ∀ W : Set M, IsOpen W → IsOpen (C.Jplus ⊤ W)) {S : Set M}
    (hS : C.IsCauchySurface S) (hSp : IsClosed (C.Jplus ⊤ S)) (hSm : IsClosed (C.Jminus ⊤ S))
    (p : M) : IsClosed (C.Jplus ⊤ {p}) := by
  have hloc : ∀ p : M, ∃ K ∈ 𝓝 p, IsCompact K ∧
      closure {z : M × M | C.le ⊤ z.1 z.2} ∩ (K ×ˢ K) ⊆ {z : M × M | C.le ⊤ z.1 z.2} :=
    fun p => by
      obtain ⟨K, hK, hKc, -, hKR⟩ := hL.exists_isCompact hSC hC (p := p) univ_mem
      exact ⟨K, hK, hKc, hKR⟩
  refine isClosed_of_closure_subset fun x hx => ?_
  by_contra hxJ
  obtain ⟨z, hz0, hzP, hzR, -, hzlim⟩ :=
    exists_antitone_chain (R := {w : M × M | C.le ⊤ w.1 w.2}) hloc
      (P := closure (C.Jplus ⊤ {p}) \ C.Jplus ⊤ {p})
      (fun y hy N hN hyN hNR =>
        let ⟨z, hzfr, hzy, hzcl, hzJ⟩ := exists_frontier_closure_Jplus hC hy.1 hy.2 hN hyN hNR
        ⟨z, hzfr, hzy, hzcl, hzJ⟩) ⟨hx, hxJ⟩
  have hmono : ∀ k, C.le ⊤ (z k) x := by
    intro k
    induction k with
    | zero => rw [hz0]; exact C.le_refl trivial
    | succ k ih => exact C.le_trans (hzR k) ih
  obtain ⟨K₁, hK₁, hK₁sub⟩ := exists_isCompact_Jminus_inter_Jplus hC hSC hL hJm hS hSp x
  obtain ⟨K₂, hK₂, hK₂sub⟩ := exists_isCompact_Jminus_inter_Jplus (C := C.dual)
    (dual_causallyArcConnectedOn.2 hC) (dual_stronglyCausal.2 hSC)
    (dual_locallyCausallyClosed.2 hL) hJp (dual_isCauchySurfaceOn.2 hS) hSm p
  have hsub₂ : (C.Jplus ⊤ S)ᶜ ∩ C.Jplus ⊤ {p} ⊆ K₂ := by
    rintro w ⟨hwS, hwp⟩
    have hw : w ∈ C.Jminus ⊤ S := (hS.cover_of_t1_secondCountable w).resolve_left hwS
    exact hK₂sub ⟨hwp, hw⟩
  have hin : ∀ k, z k ∈ K₁ ∪ K₂ := by
    intro k
    by_cases h : z k ∈ C.Jplus ⊤ S
    · exact Or.inl (hK₁sub ⟨Precausality.mem_Jminus_singleton.2 (hmono k), h⟩)
    · right
      have hcl : z k ∈ closure ((C.Jplus ⊤ S)ᶜ ∩ C.Jplus ⊤ {p}) :=
        hSp.isOpen_compl.inter_closure ⟨h, (hzP k).1⟩
      exact hK₂.isClosed.closure_subset (closure_mono hsub₂ hcl)
  obtain ⟨y, -, hy⟩ := (hK₁.union hK₂).exists_mapClusterPt (f := atTop) (u := z)
    (tendsto_principal.2 (Eventually.of_forall hin))
  exact hzlim y (tendsto_of_mapClusterPt_of_chain hSC hzR hy)

/-- **The engine: (iii)⇒(i) without limit curves.** A second countable, locally compact,
metrizable spacetime, causally arc-connected, strongly causal and locally causally closed, in
which `J^∓` of every open set is open, with a Cauchy surface `S` such that `J^±(S)` are closed, is
globally hyperbolic: `J(p, q)` is closed and lies in `(J⁻(q) ∩ J⁺(S)) ∪ (J⁺(p) ∩ J⁻(S))`. -/
theorem globallyHyperbolic_of_isCauchySurface_of_isOpen (hC : C.CausallyArcConnected)
    (hSC : C.StronglyCausal) (hL : C.LocallyCausallyClosed)
    (hJm : ∀ W : Set M, IsOpen W → IsOpen (C.Jminus ⊤ W))
    (hJp : ∀ W : Set M, IsOpen W → IsOpen (C.Jplus ⊤ W)) {S : Set M}
    (hS : C.IsCauchySurface S) (hSp : IsClosed (C.Jplus ⊤ S)) (hSm : IsClosed (C.Jminus ⊤ S)) :
    C.GloballyHyperbolic := by
  refine ⟨hSC.isCausal, fun p q => ?_⟩
  have hclp := isClosed_Jplus_singleton_of_isCauchySurface hC hSC hL hJm hJp hS hSp hSm p
  have hclq : IsClosed (C.Jminus ⊤ {q}) := isClosed_Jplus_singleton_of_isCauchySurface
    (C := C.dual) (dual_causallyArcConnectedOn.2 hC) (dual_stronglyCausal.2 hSC)
    (dual_locallyCausallyClosed.2 hL) hJp hJm (dual_isCauchySurfaceOn.2 hS) hSm hSp q
  obtain ⟨K₁, hK₁, hK₁sub⟩ := exists_isCompact_Jminus_inter_Jplus hC hSC hL hJm hS hSp q
  obtain ⟨K₂, hK₂, hK₂sub⟩ := exists_isCompact_Jminus_inter_Jplus (C := C.dual)
    (dual_causallyArcConnectedOn.2 hC) (dual_stronglyCausal.2 hSC)
    (dual_locallyCausallyClosed.2 hL) hJp (dual_isCauchySurfaceOn.2 hS) hSm p
  refine (hK₁.union hK₂).of_isClosed_subset (hclq.inter hclp) fun x hx => ?_
  rcases hS.cover_of_t1_secondCountable x with h | h
  · exact Or.inl (hK₁sub ⟨hx.1, h⟩)
  · exact Or.inr (hK₂sub ⟨hx.2, h⟩)

end Engine

/-! ### `theo:geroch`, repaired (DEC-148) -/

section Repaired

variable {M : Type u} [TopologicalSpace M] [MetrizableSpace M] [LocallyCompactSpace M]
  [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] {C : Causality M}
  {μp μm : Measure M}

omit [MeasurableSpace M] [BorelSpace M] in
/-- **`theo:geroch` (iii)⇒(i), repaired (DEC-148), under causal openness and chronal cones**:
the paper's hypotheses, local causal closedness, `J^±` of open sets open and `I^±(x) ≠ ∅`. -/
theorem geroch_iii_imp_i_of_causallyOpen (hC : C.CausallyArcConnected) (hSC : C.StronglyCausal)
    (hJm : ∀ p : M, C.Jminus ⊤ {p} ≠ {p}) (hL : C.LocallyCausallyClosed) (hO : C.CausallyOpen)
    (hI : C.NonemptyChronalCones) (h : ∃ S : Set M, C.IsCauchySurface S) :
    C.GloballyHyperbolic := by
  obtain ⟨S, hS⟩ := h
  obtain ⟨hSp, hSm, -⟩ := hS.sigma_separe_of_nonemptyChronalCones hSC.isCausal hC hJm hI
  exact globallyHyperbolic_of_isCauchySurface_of_isOpen hC hSC hL
    (fun W hW => hO.2 ⊤ ⟨W, hW⟩ le_top) (fun W hW => hO.1 ⊤ ⟨W, hW⟩ le_top) hS hSp hSm

/-- **`theo:geroch`, repaired (DEC-148), under causal openness and chronal cones**, sorry-free:
the paper's hypotheses with local causal closedness, `CausallyOpen` (DEC-8) and
`NonemptyChronalCones` give (i) ⇔ (ii) ⇔ (iii). -/
theorem geroch_of_locallyCausallyClosed_of_causallyOpen (hT : C.Tarentin)
    (hC : C.CausallyArcConnected) (hSC : C.StronglyCausal) (hJm : ∀ p : M, C.Jminus ⊤ {p} ≠ {p})
    (hJp : ∀ p : M, C.Jplus ⊤ {p} ≠ {p}) (hμp : C.AdmissibleFuture μp)
    (hμm : C.AdmissiblePast μm) (hL : C.LocallyCausallyClosed) (hO : C.CausallyOpen)
    (hI : C.NonemptyChronalCones) :
    List.TFAE [C.GloballyHyperbolic,
      ∃ T : M → ℝ, C.IsCauchyTimeFunction T ∧ ∀ x y, C.le ⊤ x y → x ≠ y → T x < T y,
      ∃ S : Set M, C.IsCauchySurface S] := by
  tfae_have 1 → 2 := geroch_i_imp_ii hμp hμm hT hC hJm hJp
  tfae_have 2 → 3 := geroch_ii_imp_iii hC hSC hJm hJp
  tfae_have 3 → 1 := geroch_iii_imp_i_of_causallyOpen hC hSC hJm hL hO hI
  tfae_finish

/-- **`theo:geroch` (iii)⇒(i), repaired as ruled (DEC-148)**: the paper's hypotheses (with the
second countability of `def:category_topological_spacetimes`) and local causal closedness. Rests
on one `sorry`: `globallyHyperbolic_of_isCauchySurface_of_isOpen` proves it once `J^∓` of open sets
are open and `J^±(S)` closed, which these hypotheses are not known to give. -/
theorem geroch_iii_imp_i_of_locallyCausallyClosed (hT : C.Tarentin)
    (hC : C.CausallyArcConnected) (hSC : C.StronglyCausal) (hJm : ∀ p : M, C.Jminus ⊤ {p} ≠ {p})
    (hJp : ∀ p : M, C.Jplus ⊤ {p} ≠ {p}) (hμp : C.AdmissibleFuture μp)
    (hμm : C.AdmissiblePast μm) (hL : C.LocallyCausallyClosed)
    (h : ∃ S : Set M, C.IsCauchySurface S) : C.GloballyHyperbolic := by
  sorry -- SORRY(theo:geroch): open; globallyHyperbolic_of_isCauchySurface_of_isOpen (sorry-free, this file) proves it once J^∓ of every open set is open and J^±(S) is closed for the Cauchy surface S, and geroch_iii_imp_i_of_causallyOpen once M is causally open with nonempty chronal cones; neither J^∓(W) open nor J^±(S) closed is a hypothesis of theo:geroch or is derived from them here (the library closes J^±(S) only from chronology at every point, IsCauchySurface.sigma_separe_of_nonemptyChronalCones, or from SingularFlatAxioms); the openness enters the engine only through PastUnboundedAt.of_le and its time reversal

/-- **`theo:geroch`, repaired as ruled (DEC-148)**: under the paper's hypotheses and local causal
closedness, (i) ⇔ (ii) ⇔ (iii). (i)⇒(ii)⇒(iii) are proved (`Causal.Geroch`); (iii)⇒(i) is
`geroch_iii_imp_i_of_locallyCausallyClosed`, one `sorry`. -/
theorem geroch_of_locallyCausallyClosed (hT : C.Tarentin) (hC : C.CausallyArcConnected)
    (hSC : C.StronglyCausal) (hJm : ∀ p : M, C.Jminus ⊤ {p} ≠ {p})
    (hJp : ∀ p : M, C.Jplus ⊤ {p} ≠ {p}) (hμp : C.AdmissibleFuture μp)
    (hμm : C.AdmissiblePast μm) (hL : C.LocallyCausallyClosed) :
    List.TFAE [C.GloballyHyperbolic,
      ∃ T : M → ℝ, C.IsCauchyTimeFunction T ∧ ∀ x y, C.le ⊤ x y → x ≠ y → T x < T y,
      ∃ S : Set M, C.IsCauchySurface S] := by
  tfae_have 1 → 2 := geroch_i_imp_ii hμp hμm hT hC hJm hJp
  tfae_have 2 → 3 := geroch_ii_imp_iii hC hSC hJm hJp
  tfae_have 3 → 1 := geroch_iii_imp_i_of_locallyCausallyClosed hT hC hSC hJm hJp hμp hμm hL
  tfae_finish

/-- **`theo:geroch`, repaired, with local causal closedness in the conditions**: (i) ⇔ (ii) ∧ L ⇔
(iii) ∧ L, no closedness assumed; (i) gives L (`GloballyHyperbolic.locallyCausallyClosed`). -/
theorem geroch_tfae_locallyCausallyClosed (hT : C.Tarentin) (hC : C.CausallyArcConnected)
    (hSC : C.StronglyCausal) (hJm : ∀ p : M, C.Jminus ⊤ {p} ≠ {p})
    (hJp : ∀ p : M, C.Jplus ⊤ {p} ≠ {p}) (hμp : C.AdmissibleFuture μp)
    (hμm : C.AdmissiblePast μm) :
    List.TFAE [C.GloballyHyperbolic,
      (∃ T : M → ℝ, C.IsCauchyTimeFunction T ∧ ∀ x y, C.le ⊤ x y → x ≠ y → T x < T y) ∧
        C.LocallyCausallyClosed,
      (∃ S : Set M, C.IsCauchySurface S) ∧ C.LocallyCausallyClosed] := by
  tfae_have 1 → 2 := fun hG =>
    ⟨geroch_i_imp_ii hμp hμm hT hC hJm hJp hG, hG.locallyCausallyClosed hT⟩
  tfae_have 2 → 3 := fun ⟨h, hL⟩ => ⟨geroch_ii_imp_iii hC hSC hJm hJp h, hL⟩
  tfae_have 3 → 1 := fun ⟨h, hL⟩ =>
    geroch_iii_imp_i_of_locallyCausallyClosed hT hC hSC hJm hJp hμp hμm hL h
  tfae_finish

end Repaired

/-! ### The printed forms (refuted; kept for `CausalScaffold.SingularGeroch`) -/

section Printed

variable {M : Type u} [TopologicalSpace M] [MetrizableSpace M] [LocallyCompactSpace M]
  [MeasurableSpace M] [BorelSpace M] {C : Causality M} {μp μm : Measure M}

/-- `theo:geroch`, (iii)⇒(i), **as printed — FALSE** (`Causal.not_gerochIIIImpIAsPrinted`,
`CausalScaffold.GerochCauchy`). Kept, statement unchanged, because `CausalScaffold.SingularGeroch`
and the curation cite `geroch`; its `sorry` cannot be discharged. Repaired form:
`geroch_iii_imp_i_of_locallyCausallyClosed` (DEC-148). -/
theorem geroch_iii_imp_i (hT : C.Tarentin) (hC : C.CausallyArcConnected)
    (hSC : C.StronglyCausal) (hJm : ∀ p : M, C.Jminus ⊤ {p} ≠ {p})
    (hJp : ∀ p : M, C.Jplus ⊤ {p} ≠ {p}) (hμp : C.AdmissibleFuture μp)
    (hμm : C.AdmissiblePast μm) (h : ∃ S : Set M, C.IsCauchySurface S) :
    C.GloballyHyperbolic := by
  sorry -- SORRY(theo:geroch): FALSE as printed (Causal.not_gerochIIIImpIAsPrinted, CausalScaffold.GerochCauchy: chronological Minkowski space); kept only because CausalScaffold.SingularGeroch cites `geroch`; the repaired form is geroch_iii_imp_i_of_locallyCausallyClosed (DEC-148)

/-- `theo:geroch` as printed, under the name it had before DEC-15 — **FALSE**
(`Causal.not_geroch_tfae`); kept for the citations. -/
theorem geroch_tfae_strict (hT : C.Tarentin) (hC : C.CausallyArcConnected)
    (hSC : C.StronglyCausal) (hJm : ∀ p : M, C.Jminus ⊤ {p} ≠ {p})
    (hJp : ∀ p : M, C.Jplus ⊤ {p} ≠ {p}) (hμp : C.AdmissibleFuture μp)
    (hμm : C.AdmissiblePast μm) :
    List.TFAE [C.GloballyHyperbolic,
      ∃ T : M → ℝ, C.IsCauchyTimeFunction T ∧ ∀ x y, C.le ⊤ x y → x ≠ y → T x < T y,
      ∃ S : Set M, C.IsCauchySurface S] := by
  tfae_have 1 → 2 := geroch_i_imp_ii hμp hμm hT hC hJm hJp
  tfae_have 2 → 3 := geroch_ii_imp_iii hC hSC hJm hJp
  tfae_have 3 → 1 := geroch_iii_imp_i hT hC hSC hJm hJp hμp hμm
  tfae_finish

/-- `theo:geroch` as printed (DEC-15) — **FALSE** (`Causal.not_geroch_tfae`); kept because
`CausalScaffold.SingularGeroch` and the curation cite it. Repaired: `geroch_of_locallyCausallyClosed`
(as ruled, one `sorry`), `geroch_of_locallyCausallyClosed_of_causallyOpen` (sorry-free). -/
theorem geroch (hT : C.Tarentin) (hC : C.CausallyArcConnected)
    (hSC : C.StronglyCausal) (hJm : ∀ p : M, C.Jminus ⊤ {p} ≠ {p})
    (hJp : ∀ p : M, C.Jplus ⊤ {p} ≠ {p}) (hμp : C.AdmissibleFuture μp)
    (hμm : C.AdmissiblePast μm) :
    List.TFAE [C.GloballyHyperbolic,
      ∃ T : M → ℝ, C.IsCauchyTimeFunction T ∧ ∀ x y, C.le ⊤ x y → x ≠ y → T x < T y,
      ∃ S : Set M, C.IsCauchySurface S] :=
  geroch_tfae_strict hT hC hSC hJm hJp hμp hμm

end Printed

end Causality

/-! ### Witnesses on the timelike line -/

/-- The timelike line is locally causally closed (it is globally hyperbolic). -/
theorem timelikeLine_locallyCausallyClosed : timelikeLine.LocallyCausallyClosed :=
  Causality.GloballyHyperbolic.locallyCausallyClosed timelikeLine_tarentin
    timelikeLine_globallyHyperbolic

/-- **The hypotheses of the engine are jointly satisfiable**: the timelike line with `S = {0}`. -/
theorem timelikeLine_engine_hypotheses :
    timelikeLine.CausallyArcConnected ∧ timelikeLine.StronglyCausal ∧
      timelikeLine.LocallyCausallyClosed ∧
      (∀ W : Set ℝ, IsOpen W → IsOpen (timelikeLine.Jminus ⊤ W)) ∧
      (∀ W : Set ℝ, IsOpen W → IsOpen (timelikeLine.Jplus ⊤ W)) ∧
      timelikeLine.IsCauchySurface {0} ∧ IsClosed (timelikeLine.Jplus ⊤ ({0} : Set ℝ)) ∧
      IsClosed (timelikeLine.Jminus ⊤ ({0} : Set ℝ)) :=
  ⟨timelikeLine_causallyArcConnected, timelikeLine_stronglyCausal,
    timelikeLine_locallyCausallyClosed,
    fun W hW => timelikeLine_causallyOpen_of_chronalNeighbours.2 ⊤ ⟨W, hW⟩ le_top,
    fun W hW => timelikeLine_causallyOpen_of_chronalNeighbours.1 ⊤ ⟨W, hW⟩ le_top,
    timelikeLine_isCauchySurface_zero, timelikeLine_sigma_separe_of_nonemptyChronalCones.1,
    timelikeLine_sigma_separe_of_nonemptyChronalCones.2.1⟩

/-- The printed form's witness, kept (it rests on the printed form's `sorry`). -/
theorem timelikeLine_geroch_tfae :
    List.TFAE [timelikeLine.GloballyHyperbolic,
      ∃ T : ℝ → ℝ, timelikeLine.IsCauchyTimeFunction T ∧
        ∀ x y, timelikeLine.le ⊤ x y → x ≠ y → T x < T y,
      ∃ S : Set ℝ, timelikeLine.IsCauchySurface S] :=
  Causality.geroch timelikeLine_tarentin timelikeLine_causallyArcConnected
    timelikeLine_stronglyCausal timelikeLine_Jminus_ne timelikeLine_Jplus_ne
    timelikeLine_admissible_past_and_future.2 timelikeLine_admissible_past_and_future.1

/-- **The hypotheses of `geroch_of_locallyCausallyClosed_of_causallyOpen` are jointly
satisfiable**: the timelike line. -/
theorem timelikeLine_geroch_of_locallyCausallyClosed_of_causallyOpen :
    List.TFAE [timelikeLine.GloballyHyperbolic,
      ∃ T : ℝ → ℝ, timelikeLine.IsCauchyTimeFunction T ∧
        ∀ x y, timelikeLine.le ⊤ x y → x ≠ y → T x < T y,
      ∃ S : Set ℝ, timelikeLine.IsCauchySurface S] :=
  Causality.geroch_of_locallyCausallyClosed_of_causallyOpen timelikeLine_tarentin
    timelikeLine_causallyArcConnected timelikeLine_stronglyCausal timelikeLine_Jminus_ne
    timelikeLine_Jplus_ne timelikeLine_admissible_past_and_future.2
    timelikeLine_admissible_past_and_future.1 timelikeLine_locallyCausallyClosed
    timelikeLine_causallyOpen_of_chronalNeighbours timelikeLine_nonemptyChronalCones

end Causal
