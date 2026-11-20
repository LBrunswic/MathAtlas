import Causal.ArcConnected
import Causal.LinesCurves

/-!
# Locating an extension: a chronal curve leaves an open set through its boundary

Programme target `T-abs-locate-extension` (`programme/roadmap.toml`; layer 1, causal-topological,
no paper label): Sbierski 1507.00601 Lemma 2.17, Grant–Kunzinger–Sämann (GKS) 1804.10423
Lemma 3.8, `references/sbierski/SYNTHESIS.md` Q4 #2. For an open `O ⊆ M` (the image of an open
embedding), `∂⁺O` (`futureBoundary`) and `∂⁻O` (`pastBoundary`) are the points outside `O`
reached by a future, resp. past, chronal curve of `M` lying in `O` before its endpoint.

* **`T-abs-locate-extension/0-characterisation`** — `futureBoundary_nonempty_iff`,
  `pastBoundary_nonempty_iff`: in a causally arc-connected spacetime a future (past) chronal
  curve leaves the open set `O` iff `I⁺(O) ⊄ O` (`I⁻(O) ⊄ O`); the endpoint lies on `∂O`
  (`futureBoundary_subset_frontier`); and **some chronal curve leaves `O` iff some point of `∂O`
  has a chronal neighbour** (`futureBoundary_union_pastBoundary_nonempty_iff`).
* `T-abs-locate-extension/1-locate` — **not marked: false as the target states it.**
  `not_exists_leaving_bare`: on `ℝ`, a causally arc-connected, causally open (`J⁺` and `J⁻`),
  causally plain causality (`isolatedLine`) and the connected proper open `(0, ∞)`: no chronal
  curve leaves it; its boundary point `0` has no chronal neighbour. Strongest true form, with the
  named localisation hypothesis `HasChronalNeighbour` at the boundary points: `exists_leaving`,
  `futureBoundary_union_pastBoundary_nonempty`, Sbierski's statement for an open embedding,
  `exists_leaving_of_isOpenEmbedding`, and `exists_leaving_of_local` (arc-connectedness and the
  chronal neighbour asked only in a neighbourhood of each boundary point).
* `T-abs-locate-extension/2-one-sided` — `exists_leaving_of_Iplus_nonempty` (local: inside any
  causally arc-connected open `W` in which `p ∈ ∂O` has a chronological future; nothing is asked
  of its past), `exists_leaving_of_Iminus_nonempty`, `exists_leaving_of_frontier_subset_Zplus`
  (`∂O ⊆ Z⁺(M)`, true on every `E_{≥0}`-manifold by `rem:btz_pas_tarentin`, `ETT.tex:1358`);
  model-free witness of a boundary point with `I⁻ = ∅ ≠ I⁺`: `closedHalfLine_oneSided`.
* `T-abs-locate-extension/3-ladder-form` — `futureBoundary_union_pastBoundary_nonempty_of_tarentin`:
  ladder nodes only (tarentin, causally plain, causally arc-connected), `M` connected, `O` open,
  non-empty and **not dense**; neither tarentin nor plainness can be dropped
  (`tarentin_and_plain_needed`).
* `T-abs-locate-extension/4-density` — `frontier_subset_closure_boundary`: when every boundary
  point has a chronal neighbour, `∂⁺O ∪ ∂⁻O` is dense in `∂O`.

> Lemma 2.17. Let (M, g) be a time-oriented Lorentzian manifold with a smooth metric, let k ∈ ℕ,
> and let ι : M ↪ M̃ be a Cᵏ-extension of (M, g). Then, there exists a timelike curve
> γ̃ : [0, 1] → M̃ such that γ̃([0, 1)) ⊆ ι(M) and γ̃(1) ∈ M̃ \ ι(M).
> Proof. Since ι(M) is a proper subset of the connected manifold M̃, its boundary ∂(ι(M)) is
> non-empty. Let p̃ ∈ ∂(ι(M)). We can find a small neighbourhood Ũ of p̃ that is time-oriented.
> Let q̃ ∈ I⁻(p̃, Ũ). […] 2. q̃ ∈ M̃ \ ι(M): Since I⁺(q̃, Ũ) is open by Proposition 2.6 and
> contains p̃ ∈ ∂(ι(M)), it must also contain a point r̃ ∈ ι(M).
> (`references/sbierski/text/sbierski2015c.txt:654–671`; the large brackets of `γ̃([0, 1))` and
> `∂(ι(M))` are dropped by pdftotext, and GKS's restatement prints them)

> Lemma 3.8. […] Then there is a ≪̃-timelike curve γ̃ : [0, 1] → X̃ such that γ̃([0, 1)) ⊆ ι(X)
> and γ̃(1) ∈ X̃\ι(X), i.e., ∂⁺(X) ∪ ∂⁻(X) ≠ ∅. Proof: […] Let p̃ ∈ ∂ι(X) and let Ω̃ be a
> localising neighbourhood of p̃ in X̃. Then, Ĩ±(p̃) ∩ Ω̃ ≠ ∅ and let q̃ ∈ Ĩ⁻(p̃) ∩ Ω̃.
> (`grant2018inextendibility.txt:418–427`; Def. 3.7 of `∂±`, `:407–413`)

## Hypothesis checklist

| source hypothesis | here |
|---|---|
| `(M, g)` time-oriented Lorentzian; `ι` a `Cᵏ` isometric embedding of the same dimension | ⚠ weakened: `ι : N → M` an open embedding (`IsOpenEmbedding`) of a non-empty space; only `ι(N)` open is used |
| `ι(M)` proper; manifolds connected (tacit, `sbierski2015c.txt:628`) | ✓ carried: `range ι ≠ univ`, `[PreconnectedSpace M]`, `[Nonempty N]` |
| `I⁺(q̃, Ũ)` open (Prop. 2.6); GKS: `Ĩ⁺(q̃) ∩ Ω̃` a neighbourhood of `p̃` | ✓ free: `≪_U` is open in both directions by axiom (`isOpen_lt_left`, `isOpen_lt_right`). The target's `uses` entry `causally_open_future` (`J⁺_U(V)` open) is **not used** |
| timelike curves realise `≪` (both sources define `≪` by curves) | ✓ carried: causal arc-connectedness of `M`, or of an open `W ∋ p` (local forms) |
| "Let q̃ ∈ I⁻(p̃, Ũ)" (time-oriented `Ũ`; GKS: `Ĩ±(p̃) ∩ Ω̃ ≠ ∅`) | ⚠ strengthened, named: `HasChronalNeighbour` at the boundary points, **one-sided** (a future or a past); without it the statement fails (`not_exists_leaving_bare`); at one boundary point it is necessary and sufficient (`futureBoundary_union_pastBoundary_nonempty_iff`) |
| (3-ladder-form) | ⚠ strengthened: tarentin and causally plain (ladder nodes beyond the target's `uses`), `closure O ≠ univ` |

## SCOPE (disclosed)

* **The curve is future or past.** Both proofs produce either (Sbierski's case 1 a future curve,
  case 2 a past one), and "timelike" covers both; here `C.ChronalCurveOn … ∨
  C.dual.ChronalCurveOn …`. The future alternative alone is false under every hypothesis:
  `timelikeLine_futureBoundary_Ioi` (`(0, ∞)` is a chronological future set). Sbierski's "without
  loss of generality future directed (otherwise reverse the time orientation)" (`:710–711`) is
  `C.dual`. The endpoint is on `∂O`, not only outside `O`.
* **What "one-sided" is.** In ETT the openness of `I^±(q)` is an axiom, so the target's "with `I⁺`
  open" costs nothing, and `causally_open_future` is unused. What the proofs take from the metric
  is a chronological past of the boundary point; it is replaced by a past **or** a future. With
  only `I⁺` of points open (GKS's case 2), the argument needs `q̃ ∈ I⁻(p̃)`, which a BTZ point
  lacks; covering it with `q̃ ∈ I⁺(p̃)` uses `I⁻(q̃)` open. ETT has both.
* **Layer 3 for `HasChronalNeighbour`**: a `C⁰` Lorentzian manifold (every point, both sides:
  a chart in which `∂/∂x⁰` is timelike, as in the proof of Sbierski's Prop. 2.6,
  `sbierski2015c.txt:450–466`); a Lorentzian length space (every point of a localising
  neighbourhood, both sides: Kunzinger–Sämann 1711.08990 Def. 3.16 (ii), the non-triviality
  condition, `kunzinger2018lorentzian.txt:1296–1299`, restated in GKS `:169–174`);
  an `E_{≥0}`-manifold (the future side: `rem:btz_pas_tarentin`; in the library the field
  `SingularFlatAxioms.mem_Zplus` of `Causal.SingularFlat`, with `BTZAxioms.Iminus_eq_empty` at BTZ
  points; that module and `Causal.Remarks.BTZPoints` import models and are not imported here).
  Under arc-connectedness it is `p ∈ Z⁺ ∪ Z⁻` with no separation axiom
  (`CausallyArcConnected.hasChronalNeighbour_iff`; `AbsolutelyMinimal.mem_Zplus_iff` asks T1).
* **The dense case of 3-ladder-form is open**: whether tarentin, plainness and arc-connectedness
  give a chronal neighbour to some boundary point of a dense open set (e.g. `M` minus a point);
  by `futureBoundary_union_pastBoundary_nonempty_iff` that is the whole question. Not proved or
  refuted here.
* Not addressed: the inextensibility of `ι⁻¹ ∘ γ` in `N` (Sbierski Thm 3.1, step 1), and a
  causality on `N` transported by `ι`; the curve is a chronal curve of the open set `ι(N)` on every
  `[0, s]`, `s < 1`.
* Witnesses: the timelike line satisfies every hypothesis (`timelikeLine_hasChronalNeighbour`,
  `timelikeLine_pastBoundary_Ioi_nonempty`); the closed half-line `[0, ∞)` (`closedHalfLine`, a
  causally arc-connected causality on `Ici (0 : ℝ)`) has an endpoint with `I⁻ = ∅ ≠ I⁺`
  (`closedHalfLine_oneSided`). No `sorry`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Filter Function

universe u v

variable {M : Type u} [TopologicalSpace M]

namespace Causality

variable (C : Causality M)

/-- The **future boundary** of a set `O` (Grant–Kunzinger–Sämann 1804.10423, Def. 3.7, after
Galloway–Ling): the points `p ∉ O` reached by a future chronal curve of `M` over `[0, 1]` lying
in `O` before its endpoint `p`. For `O` open it lies in `∂O` (`futureBoundary_subset_frontier`). -/
def futureBoundary (O : Set M) : Set M :=
  {p | p ∉ O ∧ ∃ γ : ℝ → M, C.ChronalCurveOn ⊤ γ 0 1 ∧ (∀ t ∈ Ico (0 : ℝ) 1, γ t ∈ O) ∧ γ 1 = p}

/-- The **past boundary** of `O`: the future boundary for the reversed causality, i.e. the
points `p ∉ O` reached by a past chronal curve lying in `O` before `p`. -/
def pastBoundary (O : Set M) : Set M := C.dual.futureBoundary O

/-- **A point with a chronal neighbour** — a named localisation hypothesis (no ladder node):
`p` is chronologically related to some point of `M`, to the future or to the past. It is
one-sided: a point with `I⁻(p) = ∅` and `I⁺(p) ≠ ∅` (a BTZ point of an `E₀`-manifold) has one.
Under causal arc-connectedness it is `p ∈ Z⁺(M) ∪ Z⁻(M)`, the points strongly tarentin in the
future or in the past (`CausallyArcConnected.hasChronalNeighbour_iff`).

Layer 3 supplies it: for a `C⁰` time-oriented Lorentzian manifold, every point has both (the
coordinate line of a chart in which `∂/∂x⁰` is timelike, as in the proof of Sbierski 1507.00601
Prop. 2.6; the proof of Lemma 2.17 uses it as "Let q̃ ∈ I⁻(p̃, Ũ)"); for a Lorentzian length
space, every point of a localising neighbourhood has both (Kunzinger–Sämann 1711.08990,
Def. 3.16 (ii), the non-triviality condition `I^±(y) ∩ Ωₓ ≠ ∅`, used by Grant–Kunzinger–Sämann
Lemma 3.8); on an `E_{≥0}`-manifold every point is strongly tarentin in the future
(`rem:btz_pas_tarentin`, `ETT.tex:1358`; the field `SingularFlatAxioms.mem_Zplus` of
`Causal.SingularFlat`), the past being empty exactly at BTZ points. -/
def HasChronalNeighbour (p : M) : Prop :=
  (C.Iplus ⊤ {p}).Nonempty ∨ (C.Iminus ⊤ {p}).Nonempty

variable {C} {O : Set M} {W W' : Opens M} {p : M}

@[simp] theorem dual_futureBoundary : C.dual.futureBoundary O = C.pastBoundary O := rfl

@[simp] theorem dual_pastBoundary : C.dual.pastBoundary O = C.futureBoundary O := rfl

theorem dual_hasChronalNeighbour : C.dual.HasChronalNeighbour p ↔ C.HasChronalNeighbour p :=
  Or.comm

/-! ### The first exit of a chronal curve from an open set -/

/-- **First exit.** A future chronal curve of `W` over `[0, 1]` starting in the open set `O` and
ending outside it has an initial piece, reparametrised over `[0, 1]`, which is a future chronal
curve of `W` lying in `O` on `[0, 1)` and ending outside `O`. -/
theorem ChronalCurveOn.exists_firstExit {c : ℝ → M} (hc : C.ChronalCurveOn W c 0 1)
    (hO : IsOpen O) (h0 : c 0 ∈ O) (h1 : c 1 ∉ O) :
    ∃ γ : ℝ → M, C.ChronalCurveOn W γ 0 1 ∧ (∀ t ∈ Ico (0 : ℝ) 1, γ t ∈ O) ∧ γ 1 ∉ O ∧
      γ 0 = c 0 := by
  have hcont : ContinuousOn c (Icc 0 1) := CurveOn.continuousOn C.isRelFamily_lt hc
  set S : Set ℝ := Icc 0 1 ∩ c ⁻¹' Oᶜ
  have hSc : IsClosed S := hcont.preimage_isClosed_of_isClosed isClosed_Icc hO.isClosed_compl
  have h1S : (1 : ℝ) ∈ S := ⟨right_mem_Icc.2 zero_le_one, h1⟩
  have hSb : BddBelow S := ⟨0, fun s hs => hs.1.1⟩
  have hs₀ : sInf S ∈ S := hSc.csInf_mem ⟨1, h1S⟩ hSb
  set s₀ := sInf S
  have hs₀pos : 0 < s₀ := by
    rcases hs₀.1.1.eq_or_lt with h | h
    · exact absurd (h ▸ h0) hs₀.2
    · exact h
  have hlt : ∀ t, 0 ≤ t → t < s₀ → c t ∈ O := by
    intro t ht0 hts
    by_contra hct
    exact absurd (csInf_le hSb ⟨⟨ht0, hts.le.trans hs₀.1.2⟩, hct⟩) (not_le.2 hts)
  have hres : C.ChronalCurveOn W c (s₀ * 0 + 0) (s₀ * 1 + 0) := by
    simp only [mul_zero, mul_one, add_zero]
    exact CurveOn.restrict hc le_rfl hs₀.1.2 le_rfl
      (fun t ht => hc.mem t ⟨ht.1, ht.2.trans hs₀.1.2⟩)
  refine ⟨fun t => c (s₀ * t + 0), CurveOn.comp_affine hs₀pos hres, ?_, ?_, ?_⟩
  · intro t ht
    simp only [add_zero]
    exact hlt _ (mul_nonneg hs₀pos.le ht.1) (mul_lt_of_lt_one_right hs₀pos ht.2)
  · simpa using hs₀.2
  · simp

/-- A curve leaving the open set `O` is, before its endpoint, a chronal curve of `O` seen as a
spacetime: the ETT form of "`ι⁻¹ ∘ γ̃|[0,1)` is a timelike curve of `M`". -/
theorem ChronalCurveOn.chronalCurveOn_inf_of_mem {γ : ℝ → M} (hγ : C.ChronalCurveOn W γ 0 1)
    (hO : IsOpen O) (hmem : ∀ t ∈ Ico (0 : ℝ) 1, γ t ∈ O) {s : ℝ} (hs : s ∈ Ico (0 : ℝ) 1) :
    C.ChronalCurveOn (W ⊓ ⟨O, hO⟩) γ 0 s :=
  CurveOn.restrict hγ le_rfl hs.2.le inf_le_left fun t ht =>
    ⟨hγ.mem t ⟨ht.1, ht.2.trans hs.2.le⟩, hmem t ⟨ht.1, ht.2.trans_lt hs.2⟩⟩

/-- The endpoint of a curve leaving an open set lies on its frontier. -/
theorem futureBoundary_subset_frontier (hO : IsOpen O) : C.futureBoundary O ⊆ frontier O := by
  rintro p ⟨hpO, γ, hγ, hmem, rfl⟩
  rw [hO.frontier_eq]
  refine ⟨?_, hpO⟩
  have hcont : ContinuousWithinAt γ (Ico 0 1) 1 :=
    ((CurveOn.continuousOn C.isRelFamily_lt hγ) 1 (right_mem_Icc.2 zero_le_one)).mono
      Ico_subset_Icc_self
  have h1 : (1 : ℝ) ∈ closure (Ico (0 : ℝ) 1) := by
    rw [closure_Ico zero_ne_one]; exact right_mem_Icc.2 zero_le_one
  exact closure_mono (image_subset_iff.2 hmem) (hcont.mem_closure_image h1)

theorem pastBoundary_subset_frontier (hO : IsOpen O) : C.pastBoundary O ⊆ frontier O :=
  futureBoundary_subset_frontier (C := C.dual) hO

/-! ### Characterisation: a chronal curve leaves `O` iff `O` is not a chronological future set -/

/-- **A future chronal curve leaves the open set `O` iff `I⁺(O) ⊄ O`**, in a causally
arc-connected spacetime. -/
theorem futureBoundary_nonempty_iff (hC : C.CausallyArcConnected) (hO : IsOpen O) :
    (C.futureBoundary O).Nonempty ↔ (C.Iplus ⊤ O \ O).Nonempty := by
  constructor
  · rintro ⟨p, hpO, γ, hγ, hmem, rfl⟩
    exact ⟨γ 1, ⟨γ 0, hmem 0 ⟨le_rfl, zero_lt_one⟩, hγ.lt_of_lt le_rfl zero_lt_one le_rfl⟩, hpO⟩
  · rintro ⟨y, ⟨x, hxO, hxy⟩, hyO⟩
    obtain ⟨c, hc, h0, h1⟩ := (hC ⊤ le_top x y).2.1 hxy
    obtain ⟨γ, hγ, hmem, hγ1, -⟩ :=
      ChronalCurveOn.exists_firstExit hc hO (h0 ▸ hxO) (h1 ▸ hyO)
    exact ⟨γ 1, hγ1, γ, hγ, hmem, rfl⟩

/-- **A past chronal curve leaves the open set `O` iff `I⁻(O) ⊄ O`.** -/
theorem pastBoundary_nonempty_iff (hC : C.CausallyArcConnected) (hO : IsOpen O) :
    (C.pastBoundary O).Nonempty ↔ (C.Iminus ⊤ O \ O).Nonempty :=
  futureBoundary_nonempty_iff (C := C.dual) (dual_causallyArcConnectedOn.2 hC) hO

/-! ### Chronal neighbours under causal arc-connectedness -/

/-- A chronological future in `W'` gives one in every smaller open `W ∋ p`, when `W'` is causally
arc-connected. -/
theorem CausallyArcConnectedOn.Iplus_nonempty_of_le (hW' : C.CausallyArcConnectedOn W')
    (hWW' : W ≤ W') (hp : p ∈ W) (h : (C.Iplus W' {p}).Nonempty) :
    (C.Iplus W {p}).Nonempty := by
  obtain ⟨q, hq⟩ := h
  rw [Precausality.mem_Iplus_singleton] at hq
  obtain ⟨c, hc, h0, -⟩ := (hW' W' le_rfl p q).2.1 hq
  obtain ⟨l, u, hl, hu, hrel⟩ :=
    hc.rel 0 (left_mem_Icc.2 zero_le_one) W hWW' (h0 ▸ hp)
  have hpos : 0 < min (u / 2) 1 := lt_min (by linarith) one_pos
  have hr := hrel 0 (left_mem_Icc.2 zero_le_one) (min (u / 2) 1)
    ⟨hpos.le, min_le_right _ _⟩ hl hpos ((min_le_left _ _).trans_lt (by linarith))
  rw [h0] at hr
  exact ⟨c (min (u / 2) 1), Precausality.mem_Iplus_singleton.2 hr⟩

theorem CausallyArcConnectedOn.Iminus_nonempty_of_le (hW' : C.CausallyArcConnectedOn W')
    (hWW' : W ≤ W') (hp : p ∈ W) (h : (C.Iminus W' {p}).Nonempty) :
    (C.Iminus W {p}).Nonempty :=
  CausallyArcConnectedOn.Iplus_nonempty_of_le (C := C.dual) (dual_causallyArcConnectedOn.2 hW')
    hWW' hp h

/-- `rem:absolutely_minimal_topological_spacetime` without separation, under causal
arc-connectedness: `p ∈ Z⁺(M)` iff `I⁺(p) ≠ ∅`. -/
theorem CausallyArcConnected.mem_Zplus_iff (hC : C.CausallyArcConnected) :
    p ∈ C.Zplus ↔ (C.Iplus ⊤ {p}).Nonempty := by
  refine ⟨Iplus_nonempty_of_mem_Zplus, fun h N hN => ?_⟩
  let V : Opens M := ⟨interior N, isOpen_interior⟩
  have hpV : p ∈ V := mem_interior_iff_mem_nhds.2 hN
  obtain ⟨r, hr⟩ := CausallyArcConnectedOn.Iplus_nonempty_of_le hC le_top hpV h
  rw [Precausality.mem_Iplus_singleton] at hr
  exact ⟨r, Precausality.mem_Iplus_singleton.2 (C.lt_mono le_top hr),
    interior_subset (C.lt_mem_right hr)⟩

theorem CausallyArcConnected.mem_Zminus_iff (hC : C.CausallyArcConnected) :
    p ∈ C.Zminus ↔ (C.Iminus ⊤ {p}).Nonempty :=
  CausallyArcConnected.mem_Zplus_iff (C := C.dual) (dual_causallyArcConnectedOn.2 hC)

theorem CausallyArcConnected.hasChronalNeighbour_iff (hC : C.CausallyArcConnected) :
    C.HasChronalNeighbour p ↔ p ∈ C.Zplus ∪ C.Zminus := by
  rw [HasChronalNeighbour, mem_union, CausallyArcConnected.mem_Zplus_iff hC,
    CausallyArcConnected.mem_Zminus_iff hC]

/-! ### The local, one-sided lemma -/

/-- **Locating an extension, one-sided and local.** Let `O` be open and `p ∈ ∂O`, and let `W ∋ p`
be a causally arc-connected open set in which `p` has a chronological **future**. Then a chronal
curve of `W`, future or past, lies in `O` on `[0, 1)` and ends outside `O`. Nothing is asked of
the past of `p`: a BTZ point qualifies. -/
theorem exists_leaving_of_Iplus_nonempty (hW : C.CausallyArcConnectedOn W) (hO : IsOpen O)
    (hp : p ∈ closure O) (hpO : p ∉ O) (hI : (C.Iplus W {p}).Nonempty) :
    ∃ γ : ℝ → M, (C.ChronalCurveOn W γ 0 1 ∨ C.dual.ChronalCurveOn W γ 0 1) ∧
      (∀ t ∈ Ico (0 : ℝ) 1, γ t ∈ O) ∧ γ 1 ∉ O := by
  obtain ⟨q, hq⟩ := hI
  rw [Precausality.mem_Iplus_singleton] at hq
  by_cases hqO : q ∈ O
  · -- `p ∉ O ∋ q`: the curve from `p` to `q`, reversed, leaves `O` to the past
    obtain ⟨c, hc, h0, h1⟩ := (hW W le_rfl p q).2.1 hq
    have hc' : C.dual.ChronalCurveOn W (fun t => c (0 + 1 - t)) 0 1 := CurveOn.reverse hc
    obtain ⟨γ, hγ, hmem, hγ1, -⟩ := ChronalCurveOn.exists_firstExit hc' hO
      (by simpa [h1] using hqO) (by simpa [h0] using hpO)
    exact ⟨γ, Or.inr hγ, hmem, hγ1⟩
  · -- `p, q ∉ O`: `I⁻_W(q)` is open and contains `p ∈ closure O`, so it meets `O`
    obtain ⟨r, hr, hrO⟩ := mem_closure_iff.1 hp _ (C.isOpen_lt_left W q) hq
    obtain ⟨c, hc, h0, h1⟩ := (hW W le_rfl r q).2.1 hr
    obtain ⟨γ, hγ, hmem, hγ1, -⟩ :=
      ChronalCurveOn.exists_firstExit hc hO (h0 ▸ hrO) (h1 ▸ hqO)
    exact ⟨γ, Or.inl hγ, hmem, hγ1⟩

/-- The same with a chronological **past** of `p` in `W` (Sbierski's and GKS's choice,
`q̃ ∈ I⁻(p̃)`). -/
theorem exists_leaving_of_Iminus_nonempty (hW : C.CausallyArcConnectedOn W) (hO : IsOpen O)
    (hp : p ∈ closure O) (hpO : p ∉ O) (hI : (C.Iminus W {p}).Nonempty) :
    ∃ γ : ℝ → M, (C.ChronalCurveOn W γ 0 1 ∨ C.dual.ChronalCurveOn W γ 0 1) ∧
      (∀ t ∈ Ico (0 : ℝ) 1, γ t ∈ O) ∧ γ 1 ∉ O := by
  obtain ⟨γ, hγ, hmem, h1⟩ := exists_leaving_of_Iplus_nonempty (C := C.dual)
    (dual_causallyArcConnectedOn.2 hW) hO hp hpO hI
  exact ⟨γ, hγ.symm, hmem, h1⟩

/-- **Every boundary point with a chronal neighbour is a limit of endpoints of leaving curves**:
inside every neighbourhood `N` of `p ∈ ∂O`, a chronal curve of `interior N`, future or past,
leaves `O`, so `p` lies in the closure of `∂⁺O ∪ ∂⁻O`. -/
theorem mem_closure_boundary_of_hasChronalNeighbour (hC : C.CausallyArcConnected) (hO : IsOpen O)
    (hp : p ∈ frontier O) (hchr : C.HasChronalNeighbour p) :
    p ∈ closure (C.futureBoundary O ∪ C.pastBoundary O) := by
  rw [mem_closure_iff_nhds]
  intro N hN
  let V : Opens M := ⟨interior N, isOpen_interior⟩
  have hpV : p ∈ V := mem_interior_iff_mem_nhds.2 hN
  have hV : C.CausallyArcConnectedOn V := CausallyArcConnectedOn.mono hC le_top
  rw [hO.frontier_eq] at hp
  obtain ⟨γ, hγ, hmem, h1⟩ : ∃ γ : ℝ → M,
      (C.ChronalCurveOn V γ 0 1 ∨ C.dual.ChronalCurveOn V γ 0 1) ∧
        (∀ t ∈ Ico (0 : ℝ) 1, γ t ∈ O) ∧ γ 1 ∉ O := by
    rcases hchr with h | h
    · exact exists_leaving_of_Iplus_nonempty hV hO hp.1 hp.2
        (CausallyArcConnectedOn.Iplus_nonempty_of_le hC le_top hpV h)
    · exact exists_leaving_of_Iminus_nonempty hV hO hp.1 hp.2
        (CausallyArcConnectedOn.Iminus_nonempty_of_le hC le_top hpV h)
  rcases hγ with h | h
  · exact ⟨γ 1, interior_subset (h.mem 1 (right_mem_Icc.2 zero_le_one)),
      Or.inl ⟨h1, γ, CurveOn.mono_opens C.isRelFamily_lt h le_top, hmem, rfl⟩⟩
  · exact ⟨γ 1, interior_subset (h.mem 1 (right_mem_Icc.2 zero_le_one)),
      Or.inr ⟨h1, γ, CurveOn.mono_opens C.dual.isRelFamily_lt h le_top, hmem, rfl⟩⟩

/-- **Density**: if every boundary point of `O` has a chronal neighbour, the future and past
boundaries together are dense in `∂O`. -/
theorem frontier_subset_closure_boundary (hC : C.CausallyArcConnected) (hO : IsOpen O)
    (hchr : ∀ p ∈ frontier O, C.HasChronalNeighbour p) :
    frontier O ⊆ closure (C.futureBoundary O ∪ C.pastBoundary O) :=
  fun _ hp => mem_closure_boundary_of_hasChronalNeighbour hC hO hp (hchr _ hp)

/-- The endpoint of a curve leaving `O` has a chronal neighbour: the start of the curve. -/
theorem hasChronalNeighbour_of_mem_boundary {b : M}
    (hb : b ∈ C.futureBoundary O ∪ C.pastBoundary O) : C.HasChronalNeighbour b := by
  rcases hb with ⟨-, γ, hγ, -, rfl⟩ | ⟨-, γ, hγ, -, rfl⟩
  · exact Or.inr ⟨γ 0, Precausality.mem_Iminus_singleton.2
      (hγ.lt_of_lt le_rfl zero_lt_one le_rfl)⟩
  · exact Or.inl ⟨γ 0, Precausality.mem_Iplus_singleton.2
      (hγ.lt_of_lt le_rfl zero_lt_one le_rfl)⟩

/-- **Locating an extension, sharp form**: in a causally arc-connected spacetime, a chronal curve,
future or past, leaves the open set `O` **iff some boundary point of `O` has a chronal
neighbour**. No connectedness, no separation. -/
theorem futureBoundary_union_pastBoundary_nonempty_iff (hC : C.CausallyArcConnected)
    (hO : IsOpen O) :
    (C.futureBoundary O ∪ C.pastBoundary O).Nonempty ↔
      ∃ p ∈ frontier O, C.HasChronalNeighbour p := by
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨b, ?_, hasChronalNeighbour_of_mem_boundary hb⟩
    rcases hb with hb | hb
    · exact futureBoundary_subset_frontier hO hb
    · exact pastBoundary_subset_frontier hO hb
  · rintro ⟨p, hp, hchr⟩
    exact closure_nonempty_iff.1 ⟨p, mem_closure_boundary_of_hasChronalNeighbour hC hO hp hchr⟩

/-! ### The global lemma (Sbierski Lemma 2.17, Grant–Kunzinger–Sämann Lemma 3.8) -/

/-- **Locating an extension, from local data at the boundary only**: `O` a proper non-empty open
subset of a connected spacetime, and every boundary point `p` has a causally arc-connected open
neighbourhood `W` in which it has a chronological future or past. Then some chronal curve of `M`,
future or past, lies in `O` on `[0, 1)` and ends on `∂O`. Nothing is asked of `M` away from `∂O`. -/
theorem exists_leaving_of_local [PreconnectedSpace M] (hO : IsOpen O) (hne : O.Nonempty)
    (hne' : O ≠ univ) (hloc : ∀ p ∈ frontier O, ∃ W : Opens M, C.CausallyArcConnectedOn W ∧
      ((C.Iplus W {p}).Nonempty ∨ (C.Iminus W {p}).Nonempty)) :
    ∃ γ : ℝ → M, (C.ChronalCurveOn ⊤ γ 0 1 ∨ C.dual.ChronalCurveOn ⊤ γ 0 1) ∧
      (∀ t ∈ Ico (0 : ℝ) 1, γ t ∈ O) ∧ γ 1 ∉ O ∧ γ 1 ∈ frontier O := by
  obtain ⟨p, hp⟩ : (frontier O).Nonempty := nonempty_frontier_iff.2 ⟨hne, hne'⟩
  have hpf := hp
  rw [hO.frontier_eq] at hpf
  obtain ⟨W, hW, hI⟩ := hloc p hp
  obtain ⟨γ, hγ, hmem, h1⟩ : ∃ γ : ℝ → M,
      (C.ChronalCurveOn W γ 0 1 ∨ C.dual.ChronalCurveOn W γ 0 1) ∧
        (∀ t ∈ Ico (0 : ℝ) 1, γ t ∈ O) ∧ γ 1 ∉ O := by
    rcases hI with h | h
    · exact exists_leaving_of_Iplus_nonempty hW hO hpf.1 hpf.2 h
    · exact exists_leaving_of_Iminus_nonempty hW hO hpf.1 hpf.2 h
  rcases hγ with h | h
  · have h' := CurveOn.mono_opens C.isRelFamily_lt h (le_top : W ≤ ⊤)
    exact ⟨γ, Or.inl h', hmem, h1, futureBoundary_subset_frontier hO ⟨h1, γ, h', hmem, rfl⟩⟩
  · have h' := CurveOn.mono_opens C.dual.isRelFamily_lt h (le_top : W ≤ ⊤)
    exact ⟨γ, Or.inr h', hmem, h1, pastBoundary_subset_frontier hO ⟨h1, γ, h', hmem, rfl⟩⟩

/-- **Locating an extension**, for a proper non-empty open subset `O` of a connected causally
arc-connected spacetime whose boundary points have chronal neighbours: some chronal curve of `M`,
future or past, lies in `O` on `[0, 1)` and ends on `∂O`; equivalently `∂⁺O ∪ ∂⁻O ≠ ∅`. -/
theorem exists_leaving [PreconnectedSpace M] (hC : C.CausallyArcConnected) (hO : IsOpen O)
    (hne : O.Nonempty) (hne' : O ≠ univ) (hchr : ∀ p ∈ frontier O, C.HasChronalNeighbour p) :
    ∃ γ : ℝ → M, (C.ChronalCurveOn ⊤ γ 0 1 ∨ C.dual.ChronalCurveOn ⊤ γ 0 1) ∧
      (∀ t ∈ Ico (0 : ℝ) 1, γ t ∈ O) ∧ γ 1 ∉ O ∧ γ 1 ∈ frontier O :=
  exists_leaving_of_local hO hne hne' fun p hp => ⟨⊤, hC, hchr p hp⟩

theorem futureBoundary_union_pastBoundary_nonempty [PreconnectedSpace M]
    (hC : C.CausallyArcConnected) (hO : IsOpen O) (hne : O.Nonempty) (hne' : O ≠ univ)
    (hchr : ∀ p ∈ frontier O, C.HasChronalNeighbour p) :
    (C.futureBoundary O ∪ C.pastBoundary O).Nonempty := by
  obtain ⟨γ, hγ, hmem, h1, -⟩ := exists_leaving hC hO hne hne' hchr
  rcases hγ with h | h
  · exact ⟨γ 1, Or.inl ⟨h1, γ, h, hmem, rfl⟩⟩
  · exact ⟨γ 1, Or.inr ⟨h1, γ, h, hmem, rfl⟩⟩

/-- **Sbierski 1507.00601 Lemma 2.17 in ETT**: an open embedding `ι : N → M` of a non-empty space
onto a proper subset of a connected causally arc-connected spacetime whose boundary points of
`ι(N)` have chronal neighbours. For `D = C` or `D = C.dual` (a future or a past curve) there is a
chronal curve `γ` of `D` in `M` with `γ([0, 1)) ⊆ ι(N)` and `γ(1) ∈ ∂ι(N)`, so `γ(1) ∉ ι(N)`; on
every `[0, s]`, `s < 1`, it is a chronal curve of `D` in `ι(N)` seen as a spacetime (the ETT form
of "`ι⁻¹ ∘ γ̃|[0,1)` is a timelike curve of `M`"). -/
theorem exists_leaving_of_isOpenEmbedding {N : Type v} [TopologicalSpace N] [Nonempty N]
    [PreconnectedSpace M] {ι : N → M} (hι : IsOpenEmbedding ι) (hproper : range ι ≠ univ)
    (hC : C.CausallyArcConnected) (hchr : ∀ p ∈ frontier (range ι), C.HasChronalNeighbour p) :
    ∃ D : Causality M, (D = C ∨ D = C.dual) ∧ ∃ γ : ℝ → M, D.ChronalCurveOn ⊤ γ 0 1 ∧
      (∀ t ∈ Ico (0 : ℝ) 1, γ t ∈ range ι) ∧ γ 1 ∉ range ι ∧ γ 1 ∈ frontier (range ι) ∧
      ∀ s ∈ Ico (0 : ℝ) 1, D.ChronalCurveOn ⟨range ι, hι.isOpen_range⟩ γ 0 s := by
  obtain ⟨γ, hγ, hmem, h1, hfr⟩ := exists_leaving hC hι.isOpen_range (range_nonempty ι)
    hproper hchr
  have hsub : ∀ s ∈ Ico (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) s,
      γ t ∈ (⟨range ι, hι.isOpen_range⟩ : Opens M) :=
    fun s hs t ht => hmem t ⟨ht.1, ht.2.trans_lt hs.2⟩
  rcases hγ with h | h
  · exact ⟨C, Or.inl rfl, γ, h, hmem, h1, hfr, fun s hs =>
      CurveOn.restrict h le_rfl hs.2.le le_top (hsub s hs)⟩
  · exact ⟨C.dual, Or.inr rfl, γ, h, hmem, h1, hfr, fun s hs =>
      CurveOn.restrict h le_rfl hs.2.le le_top (hsub s hs)⟩

/-- The BTZ form: every boundary point strongly tarentin **in the future** (`∂O ⊆ Z⁺(M)`, which
holds on an `E₀`-manifold) suffices. -/
theorem exists_leaving_of_frontier_subset_Zplus [PreconnectedSpace M]
    (hC : C.CausallyArcConnected) (hO : IsOpen O) (hne : O.Nonempty) (hne' : O ≠ univ)
    (hZ : frontier O ⊆ C.Zplus) :
    (C.futureBoundary O ∪ C.pastBoundary O).Nonempty :=
  futureBoundary_union_pastBoundary_nonempty hC hO hne hne' fun _ hp =>
    Or.inl (Iplus_nonempty_of_mem_Zplus (hZ hp))

/-! ### A form with ladder properties only, for a set which is not dense -/

/-- **Locating an extension with ladder properties only**: in a connected tarentin, causally
plain, causally arc-connected spacetime, a chronal curve leaves every non-empty open set `O` which
is not dense. No chronal neighbour is asked of the boundary. -/
theorem futureBoundary_union_pastBoundary_nonempty_of_tarentin [PreconnectedSpace M]
    (hC : C.CausallyArcConnected) (hT : C.Tarentin) (hP : C.CausallyPlain) (hO : IsOpen O)
    (hne : O.Nonempty) (hdense : closure O ≠ univ) :
    (C.futureBoundary O ∪ C.pastBoundary O).Nonempty := by
  -- a boundary point `y` of `O` outside the interior of `closure O`
  obtain ⟨y, hy⟩ : (frontier (closure O)).Nonempty :=
    nonempty_frontier_iff.2 ⟨hne.mono subset_closure, hdense⟩
  have hyc : y ∈ closure O := by simpa using frontier_subset_closure hy
  have hyi : y ∉ interior (closure O) := hy.2
  -- tarentin: `y ∈ Int J⁻(q)`; plain: `Int J⁻(q) ⊆ closure I⁻(q)`
  obtain ⟨p, -, q, -, hpq⟩ := hT y univ univ_mem
  have hyW : y ∈ interior (C.Jminus ⊤ {q}) := interior_mono inter_subset_left hpq
  have hWcl : interior (C.Jminus ⊤ {q}) ⊆ closure (C.Iminus ⊤ {q}) := (hP ⊤ {q}).2
  by_cases hqO : q ∈ O
  · -- a point `z ∉ closure O` of `I⁻(q)`, `q ∈ O`: a past chronal curve leaves `O`
    have hnot : ¬ interior (C.Jminus ⊤ {q}) ⊆ closure O :=
      fun h => hyi (interior_maximal h isOpen_interior hyW)
    obtain ⟨w, hwW, hwO⟩ := not_subset.1 hnot
    obtain ⟨z, ⟨-, hzO⟩, hz⟩ := mem_closure_iff.1 (hWcl hwW) _
      (isOpen_interior.inter isClosed_closure.isOpen_compl) ⟨hwW, hwO⟩
    have hz' : C.lt ⊤ z q := Precausality.mem_Iminus_singleton.1 hz
    obtain ⟨b, hb⟩ := (pastBoundary_nonempty_iff hC hO).2
      ⟨z, ⟨q, hqO, hz'⟩, fun h => hzO (subset_closure h)⟩
    exact ⟨b, Or.inr hb⟩
  · -- a point `z ∈ O` of `I⁻(q)`, `q ∉ O`: a future chronal curve leaves `O`
    obtain ⟨w, hwW, hwO⟩ := mem_closure_iff.1 hyc _ isOpen_interior hyW
    obtain ⟨z, ⟨-, hzO⟩, hz⟩ :=
      mem_closure_iff.1 (hWcl hwW) _ (isOpen_interior.inter hO) ⟨hwW, hwO⟩
    have hz' : C.lt ⊤ z q := Precausality.mem_Iminus_singleton.1 hz
    obtain ⟨b, hb⟩ := (futureBoundary_nonempty_iff hC hO).2 ⟨q, ⟨z, hzO, hz'⟩, hqO⟩
    exact ⟨b, Or.inl hb⟩

end Causality

/-! ### Witnesses -/

/-- On the timelike line every point has a chronal neighbour: the hypotheses of `exists_leaving`
are satisfiable. -/
theorem timelikeLine_hasChronalNeighbour (p : ℝ) : timelikeLine.HasChronalNeighbour p :=
  Or.inl ⟨p + 1, Precausality.mem_Iplus_singleton.2 ⟨lt_add_one p, by simp⟩⟩

theorem Ioi_zero_ne_univ : Ioi (0 : ℝ) ≠ univ := fun he => by
  have h0 : (0 : ℝ) ∈ Ioi (0 : ℝ) := he ▸ mem_univ _
  exact lt_irrefl _ (mem_Ioi.1 h0)

/-- **The future alternative alone is false**, even when every hypothesis holds: on the timelike
line `(0, ∞)` is a chronological future set, so no future chronal curve leaves it. -/
theorem timelikeLine_futureBoundary_Ioi : timelikeLine.futureBoundary (Ioi 0) = ∅ := by
  refine eq_empty_iff_forall_notMem.2 ?_
  rintro _ ⟨hp, γ, hγ, hmem, rfl⟩
  have h01 := hγ.lt_of_lt le_rfl zero_lt_one le_rfl
  exact hp (lt_trans (hmem 0 ⟨le_rfl, zero_lt_one⟩) h01.1)

/-- On the timelike line a past chronal curve leaves `(0, ∞)`: `exists_leaving` applies. -/
theorem timelikeLine_pastBoundary_Ioi_nonempty : (timelikeLine.pastBoundary (Ioi 0)).Nonempty := by
  have h := Causality.futureBoundary_union_pastBoundary_nonempty timelikeLine_causallyArcConnected
    isOpen_Ioi ⟨1, mem_Ioi.2 one_pos⟩ Ioi_zero_ne_univ
    (fun p _ => timelikeLine_hasChronalNeighbour p)
  rwa [timelikeLine_futureBoundary_Ioi, empty_union] at h

/-- **The line with a chronologically isolated origin**: the timelike line of `ℝ ∖ {0}`, with `0`
related to itself only. `x ≤_U y` iff `x = y ∈ U`, or `x < y` and `[x, y] ⊆ U ∖ {0}`; `x ≪_U y`
iff `x < y` and `[x, y] ⊆ U ∖ {0}`. -/
def isolatedLine : Causality ℝ where
  le U x y := (x = y ∧ x ∈ U) ∨ (x < y ∧ Icc x y ⊆ (U : Set ℝ) ∩ {0}ᶜ)
  lt U x y := x < y ∧ Icc x y ⊆ (U : Set ℝ) ∩ {0}ᶜ
  le_mem_left h := by
    rcases h with ⟨-, h⟩ | ⟨h1, h2⟩
    · exact h
    · exact (h2 (left_mem_Icc.2 h1.le)).1
  le_mem_right h := by
    rcases h with ⟨rfl, h⟩ | ⟨h1, h2⟩
    · exact h
    · exact (h2 (right_mem_Icc.2 h1.le)).1
  lt_mem_left h := (h.2 (left_mem_Icc.2 h.1.le)).1
  lt_mem_right h := (h.2 (right_mem_Icc.2 h.1.le)).1
  le_refl hx := Or.inl ⟨rfl, hx⟩
  le_trans h₁ h₂ := by
    rcases h₁ with ⟨rfl, -⟩ | ⟨h1, h3⟩
    · exact h₂
    rcases h₂ with ⟨rfl, -⟩ | ⟨h1', h3'⟩
    · exact Or.inr ⟨h1, h3⟩
    · exact Or.inr ⟨h1.trans h1', Icc_subset_Icc_union_Icc.trans (union_subset h3 h3')⟩
  lt_trans h₁ h₂ := ⟨h₁.1.trans h₂.1, Icc_subset_Icc_union_Icc.trans (union_subset h₁.2 h₂.2)⟩
  le_mono h _ _ h' := by
    rcases h' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1, h h2⟩
    · exact Or.inr ⟨h1, fun _ hz => ⟨h (h2 hz).1, (h2 hz).2⟩⟩
  lt_mono h _ _ h' := ⟨h'.1, fun _ hz => ⟨h (h'.2 hz).1, (h'.2 hz).2⟩⟩
  le_of_lt h := Or.inr h
  isOpen_lt_right U x :=
    isOpen_setOf_lt_and_Icc_subset_right (U ⊓ ⟨{0}ᶜ, isOpen_compl_singleton⟩) x
  isOpen_lt_left U y :=
    isOpen_setOf_lt_and_Icc_subset_left (U ⊓ ⟨{0}ᶜ, isOpen_compl_singleton⟩) y

/-- The open set `ℝ ∖ {0}`. -/
def puncturedLine : Opens ℝ := ⟨{0}ᶜ, isOpen_compl_singleton⟩

theorem isolatedLine_lt {U : Opens ℝ} {x y : ℝ} :
    isolatedLine.lt U x y ↔ timelikeLine.lt (U ⊓ puncturedLine) x y := Iff.rfl

theorem isolatedLine_causallyArcConnected : isolatedLine.CausallyArcConnected := by
  rw [Causality.CausallyArcConnected, Causality.causallyArcConnectedOn_iff]
  intro U _ p q
  have key : isolatedLine.lt U p q →
      ∃ c : ℝ → ℝ, isolatedLine.ChronalCurveOn U c 0 1 ∧ c 0 = p ∧ c 1 = q := by
    intro hpq
    have h := timelikeLine_chronalCurveOn_affine (U := U ⊓ puncturedLine) hpq.1 hpq.2
    refine ⟨fun t => p + t * (q - p), ⟨fun t ht => (inf_le_left : U ⊓ puncturedLine ≤ U)
      (h.mem t ht), fun t ht N hN htN => ?_⟩, by simp, by simp⟩
    obtain ⟨l, u, hl, hu, hrel⟩ := h.rel t ht (N ⊓ puncturedLine)
      (inf_le_inf_right _ hN) ⟨htN, (inf_le_right : U ⊓ puncturedLine ≤ puncturedLine)
        (h.mem t ht)⟩
    exact ⟨l, u, hl, hu, fun s hs s' hs' h1 h2 h3 => hrel s hs s' hs' h1 h2 h3⟩
  refine ⟨fun h => ?_, key⟩
  rcases h with ⟨rfl, hp⟩ | h
  · exact ⟨fun _ => p, Causality.causalCurveOn_const hp, rfl, rfl⟩
  · obtain ⟨c, hc, h0, h1⟩ := key h
    exact ⟨c, hc.causalCurveOn, h0, h1⟩

theorem isolatedLine_causallyOpen : isolatedLine.CausallyOpen := by
  refine ⟨fun U V hVU => ?_, fun U V hVU => ?_⟩
  · rw [isOpen_iff_mem_nhds]
    rintro y ⟨x, hx, hxy⟩
    rcases hxy with ⟨rfl, -⟩ | hxy
    · exact Filter.mem_of_superset (V.isOpen.mem_nhds hx)
        fun z hz => ⟨z, hz, Or.inl ⟨rfl, hVU hz⟩⟩
    · exact Filter.mem_of_superset ((isolatedLine.isOpen_lt_right U x).mem_nhds hxy)
        fun z hz => ⟨x, hx, Or.inr hz⟩
  · rw [isOpen_iff_mem_nhds]
    rintro y ⟨x, hx, hyx⟩
    rcases hyx with ⟨rfl, -⟩ | hyx
    · exact Filter.mem_of_superset (V.isOpen.mem_nhds hx)
        fun z hz => ⟨z, hz, Or.inl ⟨rfl, hVU hz⟩⟩
    · exact Filter.mem_of_superset ((isolatedLine.isOpen_lt_left U x).mem_nhds hyx)
        fun z hz => ⟨x, hx, Or.inr hz⟩

/-- A non-empty open subset of `ℝ` contains an interval around a point, missing `0`. -/
theorem exists_Ioo_subset_compl_zero {O : Set ℝ} (hO : IsOpen O) (hne : O.Nonempty) :
    ∃ l z u : ℝ, l < z ∧ z < u ∧ z ∈ O ∧ Ioo l u ⊆ O ∩ {0}ᶜ := by
  obtain ⟨z, hzO, hz0⟩ : ∃ z ∈ O, z ≠ 0 := by
    obtain ⟨w, hw⟩ := hne
    by_cases hw0 : w = 0
    · subst hw0
      obtain ⟨l, u, ⟨hl, hu⟩, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.1 (hO.mem_nhds hw)
      exact ⟨u / 2, hsub ⟨by linarith, by linarith⟩, by positivity⟩
    · exact ⟨w, hw, hw0⟩
  obtain ⟨l, u, ⟨hl, hu⟩, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.1
    ((hO.inter isOpen_compl_singleton).mem_nhds ⟨hzO, hz0⟩)
  exact ⟨l, z, u, hl, hu, hzO, hsub⟩

theorem isolatedLine_causallyPlain : isolatedLine.CausallyPlain := by
  rw [Causality.causallyPlain_iff]
  intro U A O hO hne
  obtain ⟨l, z, u, hl, hu, hzO, hsub⟩ := exists_Ioo_subset_compl_zero hO hne
  refine ⟨fun hOJ => ?_, fun hOJ => ?_⟩
  · obtain ⟨x, hxA, hxz⟩ := hOJ hzO
    rcases hxz with ⟨rfl, -⟩ | hxz
    · -- `x = z ∈ A`: the point `b` a little after `z` lies in `I⁺_U(A)`
      have hb : (x + u) / 2 ∈ Ioo l u := ⟨by linarith, by linarith⟩
      have hIcc : Icc x ((x + u) / 2) ⊆ (U : Set ℝ) ∩ {0}ᶜ := fun w hw => by
        have hw' : w ∈ Ioo l u := ⟨by linarith [hw.1], by linarith [hw.2]⟩
        exact ⟨Precausality.Jplus_subset_carrier (hOJ (hsub hw').1), (hsub hw').2⟩
      exact ⟨(x + u) / 2, (hsub hb).1, x, hxA, by linarith, hIcc⟩
    · exact ⟨z, hzO, x, hxA, hxz⟩
  · obtain ⟨x, hxA, hzx⟩ := hOJ hzO
    rcases hzx with ⟨rfl, -⟩ | hzx
    · have hb : (l + z) / 2 ∈ Ioo l u := ⟨by linarith, by linarith⟩
      have hIcc : Icc ((l + z) / 2) z ⊆ (U : Set ℝ) ∩ {0}ᶜ := fun w hw => by
        have hw' : w ∈ Ioo l u := ⟨by linarith [hw.1], by linarith [hw.2]⟩
        exact ⟨Precausality.Jminus_subset_carrier (hOJ (hsub hw').1), (hsub hw').2⟩
      exact ⟨(l + z) / 2, (hsub hb).1, z, hxA, by linarith, hIcc⟩
    · exact ⟨z, hzO, x, hxA, hzx⟩

theorem isolatedLine_not_hasChronalNeighbour_zero : ¬ isolatedLine.HasChronalNeighbour 0 := by
  rintro (⟨y, hy⟩ | ⟨y, hy⟩)
  · have hy' : isolatedLine.lt ⊤ 0 y := Precausality.mem_Iplus_singleton.1 hy
    exact (hy'.2 (left_mem_Icc.2 hy'.1.le)).2 (mem_singleton 0)
  · have hy' : isolatedLine.lt ⊤ y 0 := Precausality.mem_Iminus_singleton.1 hy
    exact (hy'.2 (right_mem_Icc.2 hy'.1.le)).2 (mem_singleton 0)

theorem isolatedLine_futureBoundary_Ioi : isolatedLine.futureBoundary (Ioi 0) = ∅ := by
  refine eq_empty_iff_forall_notMem.2 ?_
  rintro _ ⟨hp, γ, hγ, hmem, rfl⟩
  have h01 := hγ.lt_of_lt le_rfl zero_lt_one le_rfl
  exact hp (lt_trans (hmem 0 ⟨le_rfl, zero_lt_one⟩) h01.1)

theorem isolatedLine_pastBoundary_Ioi : isolatedLine.pastBoundary (Ioi 0) = ∅ := by
  refine eq_empty_iff_forall_notMem.2 ?_
  rintro _ ⟨hp, γ, hγ, hmem, rfl⟩
  have h10 : isolatedLine.lt ⊤ (γ 1) (γ 0) := hγ.lt_of_lt le_rfl zero_lt_one le_rfl
  have h0 : (0 : ℝ) < γ 0 := hmem 0 ⟨le_rfl, zero_lt_one⟩
  have h1 : γ 1 ≤ 0 := not_lt.1 hp
  exact (h10.2 ⟨h1, h0.le⟩).2 (mem_singleton 0)

/-- **The target's bare form is false.** On the real line, a causally arc-connected, causally
open (in the future and in the past), causally plain causality and the open embedding of
`(0, ∞)`: no chronal curve, future or past, leaves the image. The boundary point `0` has no
chronal neighbour. -/
theorem not_exists_leaving_bare :
    ¬ ∀ (C : Causality ℝ) (O : Set ℝ), C.CausallyArcConnected → C.CausallyOpen →
      C.CausallyPlain → IsOpen O → O.Nonempty → O ≠ univ → IsConnected O →
      (C.futureBoundary O ∪ C.pastBoundary O).Nonempty := by
  intro h
  have := h isolatedLine (Ioi 0) isolatedLine_causallyArcConnected isolatedLine_causallyOpen
    isolatedLine_causallyPlain isOpen_Ioi ⟨1, mem_Ioi.2 one_pos⟩ Ioi_zero_ne_univ isConnected_Ioi
  rw [isolatedLine_futureBoundary_Ioi, isolatedLine_pastBoundary_Ioi, union_empty] at this
  exact not_nonempty_empty this

/-- The lightlike line is causally arc-connected. -/
theorem lightlikeLine_causallyArcConnected : lightlikeLine.CausallyArcConnected := by
  rw [Causality.CausallyArcConnected, Causality.causallyArcConnectedOn_iff]
  intro U _ p q
  refine ⟨fun hpq => ?_, fun h => h.elim⟩
  rcases hpq.1.eq_or_lt with h | h
  · subst h
    exact ⟨fun _ => p, Causality.causalCurveOn_const (hpq.2 (left_mem_Icc.2 le_rfl)), rfl, rfl⟩
  · exact ⟨fun t => p + t * (q - p),
      (timelikeLine_chronalCurveOn_affine h hpq.2).causalCurveOn, by simp, by simp⟩

/-- No chronal curve over `[0, 1]` exists on the lightlike line: its future and past boundaries
are empty, for every set. -/
theorem lightlikeLine_futureBoundary (O : Set ℝ) : lightlikeLine.futureBoundary O = ∅ :=
  eq_empty_iff_forall_notMem.2 fun _ ⟨_, _, hγ, _⟩ => hγ.lt_of_lt le_rfl zero_lt_one le_rfl

theorem lightlikeLine_pastBoundary (O : Set ℝ) : lightlikeLine.pastBoundary O = ∅ :=
  eq_empty_iff_forall_notMem.2 fun _ ⟨_, _, hγ, _⟩ => hγ.lt_of_lt le_rfl zero_lt_one le_rfl

theorem closure_Ioi_zero_ne_univ : closure (Ioi (0 : ℝ)) ≠ univ := by
  rw [closure_Ioi]
  intro he
  have : (-1 : ℝ) ∈ Ici (0 : ℝ) := he ▸ mem_univ (-1 : ℝ)
  exact absurd (mem_Ici.1 this) (by norm_num)

/-- **Neither tarentin nor causal plainness can be dropped** from
`futureBoundary_union_pastBoundary_nonempty_of_tarentin`: the lightlike line is tarentin and
not plain, the line with an isolated origin is plain and not tarentin; both are connected and
causally arc-connected, and no chronal curve leaves `(0, ∞)`, which is not dense. -/
theorem tarentin_and_plain_needed :
    (lightlikeLine.CausallyArcConnected ∧ lightlikeLine.Tarentin ∧
      ¬ lightlikeLine.CausallyPlain ∧
      (lightlikeLine.futureBoundary (Ioi 0) ∪ lightlikeLine.pastBoundary (Ioi 0)) = ∅) ∧
    (isolatedLine.CausallyArcConnected ∧ isolatedLine.CausallyPlain ∧
      ¬ isolatedLine.Tarentin ∧
      (isolatedLine.futureBoundary (Ioi 0) ∪ isolatedLine.pastBoundary (Ioi 0)) = ∅) ∧
    closure (Ioi (0 : ℝ)) ≠ univ := by
  have hl : lightlikeLine.futureBoundary (Ioi 0) ∪ lightlikeLine.pastBoundary (Ioi 0) = ∅ := by
    rw [lightlikeLine_futureBoundary, lightlikeLine_pastBoundary, union_empty]
  have hi : isolatedLine.futureBoundary (Ioi 0) ∪ isolatedLine.pastBoundary (Ioi 0) = ∅ := by
    rw [isolatedLine_futureBoundary_Ioi, isolatedLine_pastBoundary_Ioi, union_empty]
  refine ⟨⟨lightlikeLine_causallyArcConnected, (timelikeLine_tarentin : lightlikeLine.Tarentin), fun hP => ?_, hl⟩,
    ⟨isolatedLine_causallyArcConnected, isolatedLine_causallyPlain, fun hT => ?_, hi⟩,
    closure_Ioi_zero_ne_univ⟩
  · have h := Causality.futureBoundary_union_pastBoundary_nonempty_of_tarentin
      lightlikeLine_causallyArcConnected (timelikeLine_tarentin : lightlikeLine.Tarentin) hP isOpen_Ioi
      ⟨1, mem_Ioi.2 one_pos⟩ closure_Ioi_zero_ne_univ
    rw [hl] at h
    exact not_nonempty_empty h
  · have h := Causality.futureBoundary_union_pastBoundary_nonempty_of_tarentin
      isolatedLine_causallyArcConnected hT isolatedLine_causallyPlain isOpen_Ioi
      ⟨1, mem_Ioi.2 one_pos⟩ closure_Ioi_zero_ne_univ
    rw [hi] at h
    exact not_nonempty_empty h

/-! ### A model-free BTZ-like boundary point: the closed half-line -/

/-- The closed half-line `[0, ∞)`, with the topology of `ℝ`. -/
abbrev ClosedHalfLine : Type := Ici (0 : ℝ)

/-- Its endpoint. -/
def ClosedHalfLine.zero : ClosedHalfLine := ⟨0, self_mem_Ici⟩

/-- On the half-line, "every point between `x` and `y` lies in `U`" is "`[x, y] ⊆ V`" for any open
`V` of `ℝ` tracing `U`. -/
theorem closedHalfLine_between_iff {U : Set ClosedHalfLine} {V : Set ℝ}
    (hV : Subtype.val ⁻¹' V = U) {x y : ClosedHalfLine} :
    (∀ z : ClosedHalfLine, x ≤ z → z ≤ y → z ∈ U) ↔ Icc x.1 y.1 ⊆ V := by
  constructor
  · intro h w hw
    have hz : (⟨w, x.2.trans hw.1⟩ : ClosedHalfLine) ∈ U := h _ hw.1 hw.2
    rw [← hV] at hz
    exact hz
  · intro h z h1 h2
    rw [← hV]
    exact h ⟨h1, h2⟩

theorem closedHalfLine_isOpen_right (U : Opens ClosedHalfLine) (x : ClosedHalfLine) :
    IsOpen {y : ClosedHalfLine | x < y ∧ ∀ z : ClosedHalfLine, x ≤ z → z ≤ y → z ∈ U} := by
  obtain ⟨V, hVo, hV⟩ := isOpen_induced_iff.1 U.isOpen
  have : {y : ClosedHalfLine | x < y ∧ ∀ z : ClosedHalfLine, x ≤ z → z ≤ y → z ∈ U} =
      Subtype.val ⁻¹' {y' : ℝ | x.1 < y' ∧ Icc x.1 y' ⊆ V} := by
    ext y
    exact and_congr Iff.rfl (closedHalfLine_between_iff hV)
  rw [this]
  exact (isOpen_setOf_lt_and_Icc_subset_right ⟨V, hVo⟩ x.1).preimage continuous_subtype_val

theorem closedHalfLine_isOpen_left (U : Opens ClosedHalfLine) (y : ClosedHalfLine) :
    IsOpen {x : ClosedHalfLine | x < y ∧ ∀ z : ClosedHalfLine, x ≤ z → z ≤ y → z ∈ U} := by
  obtain ⟨V, hVo, hV⟩ := isOpen_induced_iff.1 U.isOpen
  have : {x : ClosedHalfLine | x < y ∧ ∀ z : ClosedHalfLine, x ≤ z → z ≤ y → z ∈ U} =
      Subtype.val ⁻¹' {x' : ℝ | x' < y.1 ∧ Icc x' y.1 ⊆ V} := by
    ext x
    exact and_congr Iff.rfl (closedHalfLine_between_iff hV)
  rw [this]
  exact (isOpen_setOf_lt_and_Icc_subset_left ⟨V, hVo⟩ y.1).preimage continuous_subtype_val

/-- **The closed half-line** `[0, ∞)` with the causality of the timelike line: `x ≤_U y` iff
`x ≤ y` and `[x, y] ⊆ U`, `x ≪_U y` iff `x < y` and `[x, y] ⊆ U`. Its endpoint has a chronological
future and no chronological past. -/
def closedHalfLine : Causality ClosedHalfLine where
  le U x y := x ≤ y ∧ ∀ z : ClosedHalfLine, x ≤ z → z ≤ y → z ∈ U
  lt U x y := x < y ∧ ∀ z : ClosedHalfLine, x ≤ z → z ≤ y → z ∈ U
  le_mem_left h := h.2 _ le_rfl h.1
  le_mem_right h := h.2 _ h.1 le_rfl
  lt_mem_left h := h.2 _ le_rfl h.1.le
  lt_mem_right h := h.2 _ h.1.le le_rfl
  le_refl hx := ⟨le_rfl, fun _ h1 h2 => le_antisymm h2 h1 ▸ hx⟩
  le_trans := @fun _ _ y _ h₁ h₂ => ⟨h₁.1.trans h₂.1, fun z h1 h2 =>
    (le_total z y).elim (fun h => h₁.2 z h1 h) (fun h => h₂.2 z h h2)⟩
  lt_trans := @fun _ _ y _ h₁ h₂ => ⟨h₁.1.trans h₂.1, fun z h1 h2 =>
    (le_total z y).elim (fun h => h₁.2 z h1 h) (fun h => h₂.2 z h h2)⟩
  le_mono h _ _ h' := ⟨h'.1, fun z h1 h2 => h (h'.2 z h1 h2)⟩
  lt_mono h _ _ h' := ⟨h'.1, fun z h1 h2 => h (h'.2 z h1 h2)⟩
  le_of_lt h := ⟨h.1.le, h.2⟩
  isOpen_lt_right := closedHalfLine_isOpen_right
  isOpen_lt_left := closedHalfLine_isOpen_left

/-- The half-line is causally arc-connected. -/
theorem closedHalfLine_causallyArcConnected : closedHalfLine.CausallyArcConnected := by
  rw [Causality.CausallyArcConnected, Causality.causallyArcConnectedOn_iff]
  intro U _ p q
  have key : closedHalfLine.lt U p q →
      ∃ c : ℝ → ClosedHalfLine, closedHalfLine.ChronalCurveOn U c 0 1 ∧ c 0 = p ∧ c 1 = q := by
    rintro ⟨hpq, hsub⟩
    obtain ⟨V, hVo, hV⟩ := isOpen_induced_iff.1 U.isOpen
    have hpq' : p.1 < q.1 := hpq
    have hIcc : Icc p.1 q.1 ⊆ (⟨V, hVo⟩ : Opens ℝ) := (closedHalfLine_between_iff hV).1 hsub
    have h := timelikeLine_chronalCurveOn_affine hpq' hIcc
    let a : ℝ → ℝ := fun t => p.1 + t * (q.1 - p.1)
    have ha : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ a t := fun t ht => by
      have := p.2
      simp only [a, mem_Ici] at this ⊢
      nlinarith [ht.1, hpq']
    let c : ℝ → ClosedHalfLine := fun t => ⟨max 0 (a t), mem_Ici.2 (le_max_left _ _)⟩
    have hca : ∀ t ∈ Icc (0 : ℝ) 1, (c t).1 = a t := fun t ht => max_eq_right (ha t ht)
    refine ⟨c, ⟨fun t ht => ?_, fun t ht N hN htN => ?_⟩, ?_, ?_⟩
    · have : (c t).1 ∈ V := by rw [hca t ht]; exact h.mem t ht
      have hmem : c t ∈ (U : Set ClosedHalfLine) := by rw [← hV]; exact this
      exact hmem
    · obtain ⟨VN, hVNo, hVN⟩ := isOpen_induced_iff.1 N.isOpen
      have hat : a t ∈ (⟨VN, hVNo⟩ ⊓ ⟨V, hVo⟩ : Opens ℝ) := by
        refine ⟨?_, h.mem t ht⟩
        have htN' : c t ∈ (N : Set ClosedHalfLine) := htN
        rw [← hVN] at htN'
        show a t ∈ VN
        rw [← hca t ht]; exact htN'
      obtain ⟨l, u, hl, hu, hrel⟩ := h.rel t ht _ inf_le_right hat
      refine ⟨l, u, hl, hu, fun s hs s' hs' h1 h2 h3 => ?_⟩
      obtain ⟨hlt, hsub'⟩ := hrel s hs s' hs' h1 h2 h3
      refine ⟨?_, ?_⟩
      · show (c s).1 < (c s').1
        rw [hca s hs, hca s' hs']; exact hlt
      · refine (closedHalfLine_between_iff hVN).2 ?_
        rw [hca s hs, hca s' hs']
        exact fun w hw => (hsub' hw).1
    · apply Subtype.ext
      show max 0 (a 0) = p.1
      simp only [a, zero_mul, add_zero]
      exact max_eq_right p.2
    · apply Subtype.ext
      show max 0 (a 1) = q.1
      simp only [a, one_mul, add_sub_cancel]
      exact max_eq_right q.2
  refine ⟨fun hpq => ?_, key⟩
  rcases hpq.1.eq_or_lt with h | h
  · subst h
    exact ⟨fun _ => p, Causality.causalCurveOn_const (hpq.2 p le_rfl le_rfl), rfl, rfl⟩
  · obtain ⟨c, hc, h0, h1⟩ := key ⟨h, hpq.2⟩
    exact ⟨c, hc.causalCurveOn, h0, h1⟩

/-- The open half `(0, ∞)` of the half-line. -/
def closedHalfLinePos : Set ClosedHalfLine := {x | 0 < x.1}

theorem isOpen_closedHalfLinePos : IsOpen closedHalfLinePos :=
  isOpen_Ioi.preimage continuous_subtype_val

theorem closedHalfLine_zero_mem_frontier : ClosedHalfLine.zero ∈ frontier closedHalfLinePos := by
  rw [isOpen_closedHalfLinePos.frontier_eq]
  refine ⟨?_, lt_irrefl (0 : ℝ)⟩
  rw [IsInducing.subtypeVal.closure_eq_preimage_closure_image]
  have himage : Subtype.val '' closedHalfLinePos = Ioi (0 : ℝ) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, mem_Ici.2 (le_of_lt hx)⟩, hx, rfl⟩
  rw [himage, closure_Ioi]
  exact (self_mem_Ici : (0 : ℝ) ∈ Ici 0)

theorem closedHalfLine_Iminus_zero : closedHalfLine.Iminus ⊤ {ClosedHalfLine.zero} = ∅ := by
  refine eq_empty_iff_forall_notMem.2 fun z hz => ?_
  have hz' : closedHalfLine.lt ⊤ z ClosedHalfLine.zero := Precausality.mem_Iminus_singleton.1 hz
  have h1 : z.1 < 0 := hz'.1
  exact absurd z.2 (not_le.2 h1)

theorem closedHalfLine_hasChronalNeighbour (p : ClosedHalfLine) :
    closedHalfLine.HasChronalNeighbour p :=
  Or.inl ⟨⟨p.1 + 1, mem_Ici.2 (by linarith [mem_Ici.1 p.2])⟩,
    Precausality.mem_Iplus_singleton.2 ⟨show p.1 < p.1 + 1 by linarith, fun _ _ _ => trivial⟩⟩

/-- **A model-free BTZ-like boundary point, and the one-sided lemma at work.** On the closed
half-line, `(0, ∞)` is a proper open set whose boundary point `0` has a chronological future and
no chronological past, as a BTZ point of `E₀` (`rem:btz_pas_tarentin`, `ETT.tex:1358`): the
two-sided hypothesis of Sbierski's and GKS's proofs ("let q̃ ∈ I⁻(p̃)") fails there, the
one-sided `HasChronalNeighbour` holds, and a chronal curve leaves `(0, ∞)`. -/
theorem closedHalfLine_oneSided :
    ClosedHalfLine.zero ∈ frontier closedHalfLinePos ∧
      closedHalfLine.Iminus ⊤ {ClosedHalfLine.zero} = ∅ ∧
      closedHalfLine.HasChronalNeighbour ClosedHalfLine.zero ∧
      (closedHalfLine.futureBoundary closedHalfLinePos ∪
        closedHalfLine.pastBoundary closedHalfLinePos).Nonempty := by
  haveI : PreconnectedSpace ClosedHalfLine := Subtype.preconnectedSpace isPreconnected_Ici
  refine ⟨closedHalfLine_zero_mem_frontier, closedHalfLine_Iminus_zero,
    closedHalfLine_hasChronalNeighbour _, ?_⟩
  refine Causality.futureBoundary_union_pastBoundary_nonempty closedHalfLine_causallyArcConnected
    isOpen_closedHalfLinePos ⟨⟨1, mem_Ici.2 zero_le_one⟩, show (0 : ℝ) < 1 from one_pos⟩ ?_
    (fun p _ => closedHalfLine_hasChronalNeighbour p)
  intro he
  have h0 : ClosedHalfLine.zero ∈ closedHalfLinePos := he ▸ mem_univ _
  exact lt_irrefl (0 : ℝ) h0

end Causal
