import Causal.Port.E0SingularFlat
import Causal.Model.EAlphaCauchy

/-!
# The model-space rows at `κ = 0`, at the ported `E₀`, beside their `κ > 0` halves

Target `T-ett-model-rows-e0` (no `sorry`). Cited, **unmarked** (SCOPE (a)):
`cor:model_minimal` — `ETT.tex:1386`; `rem:pushup` — `ETT.tex:1374`; `lem:IJ_calc` —
`ETT.tex:1441`; `lem:densite_modele` — `ETT.tex:1464`; the model sentence of
`rem:galileo_spacetime_not_strongly` — `ETT.tex:672–673`. Each row is one conjunction for every
`κ ≥ 0`: the `κ > 0` half (strict `Causal.Model.Massive`, `Causal.Model.EAlphaCauchy`, reused)
and the `κ = 0` half at the model of record `Causal.E0` (strict `Causal.Port.E0*`).

> For every $\kappa\geq 0$ the causality of $\mass{\kappa}$ is absolutely minimal.
> (`ETT.tex:1386`)

> In the model spaces, the concatenation of a future causal curve with a future chronological one
> is future chronological. Equivalently, for every $x$,
> $J^+(I^+(x))\subset I^+(x)$ and $I^+(J^+(x))\subset I^+(x)$, and symmetrically in the past.
> Since this holds in every open subset of $\mass{\kappa}$, the model spaces have the push-up
> property of Definition \ref{defi:pushup}. (`ETT.tex:1375–1379`)

> For every $\kappa\geq 0$ and every $p\in \mass{\kappa}$,
> $\ring J^\pm(p)\cap Z^\mp(\mass{\kappa})=I^\pm(p).$ (`ETT.tex:1442–1443`)

> Let $\kappa\geq 0$ and let $p\in \mass{\kappa}$. Then (a) $J^+(p)=\overline{I^+(p)}$;
> (b) $J^-(p)=\overline{I^-(p)}$ if $\kappa>0$, or if $\kappa=0$ and $p\in \reg(\mass{0})$;
> (c) $J^-(p)=\overline{J^-(p)\setminus\{p\}}$ if $\kappa=0$ and $p\in \sing(\mass{0})$.
> The same holds in any causally convex open subset of $\mass{\kappa}$, with $J^\pm$ and $I^\pm$
> taken in that subset. (`ETT.tex:1465–1472`)

> The flat model spacetimes of Section \ref{subsec:sing_spacetime_defi} are, by contrast, strongly
> causal. (`ETT.tex:672–673`)

## What is proved (no `sorry` in this file)

* `cor:model_minimal` (`model_minimal`): `E_α` and `E₀` causally arc-connected, hence
  absolutely minimal (the paper's route, `cor:causalement_connexe_minimal`); `E₀` on every open
  set too.
* `rem:pushup` (`pushup`): push-up and `PushUpOn W` for every open `W`, both halves. **The first
  sentence is false at `E₀` as printed** (`pushup_concat_counterexample`,
  `e0_concat_not_chronal`): the axis segment `[−1, 0]` ending at a BTZ point is a future causal
  curve, a future chronal curve leaves that point, and their concatenation is a future causal
  curve which is not chronal, since nothing is `≪` a point of the axis. So the "Equivalently"
  joins a false sentence to a true one; the inclusions are what is proved.
* `lem:IJ_calc` (`IJ_calc`): at `E₀` by the abstract `Causality.J_int` (T1, absolutely minimal,
  push-up). With the proof's first paragraph, `Z⁺(E₀) = E₀` and `Z⁻(E₀) = E₀ ∖ sing₀`
  (`e0_Zplus_eq`, `e0_Zminus_eq`): `Int J⁺(p) ∖ sing₀ = I⁺(p)`, `Int J⁻(p) = I⁻(p)`
  (`e0_IJ_calc_reg`).
* `lem:densite_modele` (`densite_modele`): (a), (b), (c) at `E₀`, and the same in every causally
  convex open `V` (`e0_densite`), beside (a), (b) for `E_α`. Proved directly, without the cited
  closure-of-interior fact and without `I⁺(p) = reg(J⁺(p))`, though it uses the closedness of
  `J^±(p)`, which the paper does not state and which would come from the same reference: push-up and `Z⁺` in every open set give
  `J⁺_U(p) ⊂ closure I⁺_U(p)` (`Causality.Jplus_subset_closure_Iplus_of_locZplus`); for (b), the
  axis points of `J⁻(p)` are limits of axis points chronologically below `p` (`E0.lt_axis_iff`);
  `J^±(p)` is closed (`E0.isClosed_Jplus`, `isClosed_Jminus`); `V` by
  `restriction_convexe_future`/`_past`. **The proof's cited fact (l.1481–1482) is false for `J⁻`
  at a BTZ point** (`e0_Jminus_axis_ne_closure_interior`: `Int J⁻(p) = ∅`); it contradicts the
  paper's own l.1347 (`J⁻(p)` at a BTZ point is the half-line), so it stands whatever OQ-34 rules. It is true for `J⁺`
  everywhere and for `J⁻` off the axis (`e0_Jplus_eq_closure_interior`,
  `e0_Jminus_eq_closure_interior`). (b) fails at every BTZ point
  (`e0_Jminus_axis_ne_closure_Iminus`), as the statement allows. The `V` clauses are not vacuous:
  a causally convex open `V ≠ E₀` holds a BTZ point and a regular point
  (`e0_exists_causallyConvexIn_axis`).
* `rem:galileo_spacetime_not_strongly`, its model sentence (`models_stronglyCausal`): `E_α` and
  `E₀` strongly causal in both forms (`StronglyCausal`, `StronglyCausalOpen`; OQ-8, OQ-9). The
  open form at `E₀` is new (`e0_stronglyCausalOpen`): the causally convex set of
  `E0.stronglyCausal` is `J⁺(B) ∩ J⁻(B)` for a ball `B`, which is open (`E0.isOpen_Jplus`,
  `isOpen_Jminus`).

## Hypothesis checklist

| paper | here |
|---|---|
| `E_κ`, `κ > 0` | ✓ `Massive α`, `massive α`, `[Fact (0 < α)]` |
| `E₀`, the extreme BTZ model | ⚠ read: `Causal.E0`, `E0.causality` (OQ-34, OQ-35; SCOPE (a)) |
| `sing(E₀)`, `reg(E₀)` | ✓ `E0.axis` (`= E0.singE0 0`) and its complement |
| `I^±(p)`, `J^±(p)`, `Z^±(E_κ)` | ✓ global (`U = ⊤`), as printed |
| causally convex open subset; `J^±`, `I^±` "taken in that subset" | ✓ `CausallyConvexIn V ⊤`, `V` open; `J^±_V`, `I^±_V`; ⚠ read: closure in `V` is `closure · ∩ V` (SCOPE (b)) |
| future causal / chronological curves, concatenation (`rem:pushup`) | ✓ `CausalCurveOn`, `ChronalCurveOn` (DEC-6), `CurveOn.concat` |
| strongly causal (`def:strongly_causal_spacetime`) | ✓ both readings (OQ-8, OQ-9) |
| "the flat model spacetimes" (l.673) | ⚠ read: the model spaces `E_κ`, `κ ≥ 0` (SCOPE (c)) |

## SCOPE (disclosed)

* **(a) Why no label is marked.** Every `κ = 0` clause is proved at `Causal.E0` under OQ-34
  (gx's flat extreme-BTZ metric `−2dτdr + dr² + r²dθ²` through `D`, DEC-33's causal curves) and
  OQ-35, both open; under the printed metric (l.1330) the singular line is timelike. The marks wait
  on them. `rem:pushup`'s first sentence is false as printed. The `κ > 0` case is a recorded
  finding that has no Lean witness here, since this file is scoped to `κ = 0`.
* **(b) "Taken in that subset".** For `V` open, the closure in the subspace `V` of a set
  `A ⊂ V` is `closure A ∩ V`; this is the reading of the strict `massive_densite_of_causallyConvexIn`.
  The closure in `E_κ` cannot be meant, since it can leave `V`.
* **(c) "The flat model spacetimes of Section subsec:sing_spacetime_defi".** Read as the model
  spaces of its first subsection, `E_κ`, `κ ≥ 0` (`E_{2π} ≅ E^{1,2}`, `massiveTwoPi_iso`), not the
  `E_{≥0}`-manifolds of its second.
* **(d) Not used.** `E0GX.chartIso_of_mem_aeAtlas` and the sector charts were offered for (a), (b)
  off the axis; no chart is needed.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Model of record:
`Causal.Port.E0*` (strict, ported from gx `c48aa45`, T-ett-port-e0, T-ett-port-e0-sfa).
-/

namespace Causal

namespace ModelRowsE0

open Set TopologicalSpace Topology Filter

/-! ### `cor:model_minimal` -/

/-- `cor:model_minimal` **at `κ = 0`**: the causality of `E₀` is absolutely minimal, by the
paper's route (causal arc-connectedness and `cor:causalement_connexe_minimal`). -/
theorem e0_absolutelyMinimal : E0.causality.AbsolutelyMinimal :=
  E0.causallyArcConnected.absolutelyMinimal

/-- **`cor:model_minimal` for every `κ ≥ 0`** (`ETT.tex:1386`): `E_α` (`α > 0`) and `E₀` are
causally arc-connected (the proof's premise) and absolutely minimal; `E₀` also on every open set. -/
theorem model_minimal :
    (∀ (α : ℝ) [Fact (0 < α)],
      (massive α).CausallyArcConnected ∧ (massive α).AbsolutelyMinimal) ∧
    (E0.causality.CausallyArcConnected ∧ E0.causality.AbsolutelyMinimal ∧
      ∀ W : Opens E0, E0.causality.AbsolutelyMinimalOn W) :=
  ⟨fun _ _ => ⟨massive_causallyArcConnected, massive_absolutelyMinimal⟩,
    E0.causallyArcConnected, e0_absolutelyMinimal, E0.absolutelyMinimalOn⟩

/-! ### `rem:pushup` -/

/-- Push-up of `E₀` for the open subset `W` seen as a spacetime (`PushUpOn`), every `W`. -/
theorem e0_pushUpOn (W : Opens E0) : E0.causality.PushUpOn W := fun _ _ _ _ _ =>
  ⟨fun h₁ h₂ => E0LM.e0_pushUp.lt_of_lt_of_le h₁ h₂,
    fun h₁ h₂ => E0LM.e0_pushUp.lt_of_le_of_lt h₁ h₂⟩

/-- **`rem:pushup` for every `κ ≥ 0`, its inclusions** (`ETT.tex:1376–1379`): `E_α` and `E₀`
have the push-up property (`defi:pushup`, every open set, future and past), and push-up holds in
every open subset seen as a spacetime. The first sentence is refuted at `E₀` by
`pushup_concat_counterexample`. -/
theorem pushup :
    (∀ (α : ℝ) [Fact (0 < α)], (massive α).PushUp ∧ ∀ W, (massive α).PushUpOn W) ∧
    (E0.causality.PushUp ∧ ∀ W, E0.causality.PushUpOn W) :=
  ⟨fun _ _ => ⟨massive_pushUp, massive_pushUpOn⟩, E0LM.e0_pushUp, e0_pushUpOn⟩

/-- Every point of `E₀`, a BTZ point included, is the start of a future chronal curve (`Z⁺ = E₀`
and causal arc-connectedness). -/
theorem e0_exists_chronalCurveOn (p : E0) :
    ∃ c : ℝ → E0, E0.causality.ChronalCurveOn ⊤ c 0 1 ∧ c 0 = p := by
  obtain ⟨q, -, h⟩ := E0.exists_lt_mem p (univ_mem : univ ∈ 𝓝 p)
  obtain ⟨c, hc, h0, -⟩ := (E0.causallyArcConnected ⊤ le_rfl p q).2.1 (E0.lt_top_iff.2 h)
  exact ⟨c, hc, h0⟩

/-- **The printed first sentence of `rem:pushup` fails at `E₀`** (`ETT.tex:1375–1376`): let `p`
be a BTZ point and `c` any future chronal curve of `W` from `p`. The axis segment `[−1, 0]` ending
at `p` is a future causal curve of `W`, and its concatenation with `c` is a future causal curve
of `W` which is not chronal: its points at `−1` and `0` both lie on the axis, and nothing is `≪`
a point of the axis. -/
theorem e0_concat_not_chronal {p : E0} (hp : p ∈ E0.axis) {W : Opens E0} {c : ℝ → E0}
    (hW : ∀ t ∈ Icc (-1 : ℝ) 0, E0.axisLine p t ∈ W) (hc : E0.causality.ChronalCurveOn W c 0 1)
    (hc0 : c 0 = p) :
    E0.causality.CausalCurveOn W (E0.axisLine p) (-1) 0 ∧ E0.axisLine p 0 = c 0 ∧
    E0.causality.CausalCurveOn W (fun t => if t ≤ 0 then E0.axisLine p t else c t) (-1) 1 ∧
    ¬ E0.causality.ChronalCurveOn W (fun t => if t ≤ 0 then E0.axisLine p t else c t) (-1) 1 := by
  have h₁ : E0.causality.CausalCurveOn W (E0.axisLine p) (-1) 0 := E0.axis_causalCurveOn p W hW
  have h0 : E0.axisLine p 0 = c 0 := by
    rw [hc0]; exact Prod.ext (add_zero _) hp.symm
  refine ⟨h₁, h0, CurveOn.concat E0.causality.isRelFamily_le h₁ hc.causalCurveOn
    (by norm_num) (by norm_num) h0, fun h => ?_⟩
  have hlt := h.lt_of_lt (s := -1) (s' := 0) le_rfl (by norm_num) (by norm_num)
  simp only [le_refl, if_true] at hlt
  exact E0.not_lt_of_mem_axis (E0.axisLine_mem p 0) W _ hlt

/-- **The printed first sentence of `rem:pushup` is false at `E₀`**, assembled: the segment
`[−1, 0]` of the axis through the origin is a future causal curve, some future chronal curve leaves
the origin, and their concatenation is a future causal curve which is not chronal. -/
theorem pushup_concat_counterexample :
    ∃ c₁ c₂ : ℝ → E0, E0.causality.CausalCurveOn ⊤ c₁ (-1) 0 ∧
      E0.causality.ChronalCurveOn ⊤ c₂ 0 1 ∧ c₁ 0 = c₂ 0 ∧
      E0.causality.CausalCurveOn ⊤ (fun t => if t ≤ 0 then c₁ t else c₂ t) (-1) 1 ∧
      ¬ E0.causality.ChronalCurveOn ⊤ (fun t => if t ≤ 0 then c₁ t else c₂ t) (-1) 1 := by
  obtain ⟨c, hc, hc0⟩ := e0_exists_chronalCurveOn (((0 : ℝ), (0 : ℂ)) : E0)
  obtain ⟨h₁, h0, h₂, h₃⟩ :=
    e0_concat_not_chronal (p := ((0 : ℝ), (0 : ℂ))) (W := ⊤) rfl (fun _ _ => trivial) hc hc0
  exact ⟨_, c, h₁, hc, h0, h₂, h₃⟩

/-! ### `lem:IJ_calc` -/

/-- The first paragraph of `lem:IJ_calc`'s proof at `κ = 0`: `Z⁺(E₀) = E₀`. -/
theorem e0_Zplus_eq : E0.causality.Zplus = univ := eq_univ_of_forall E0.mem_Zplus

/-- The first paragraph of `lem:IJ_calc`'s proof at `κ = 0`: `Z⁻(E₀) = reg(E₀)`. -/
theorem e0_Zminus_eq : E0.causality.Zminus = E0.axisᶜ := Set.ext E0.mem_Zminus_iff

/-- `lem:IJ_calc` **at `κ = 0`, as printed**: `Int J^±(p) ∩ Z^∓(E₀) = I^±(p)` for every `p`,
BTZ points included, by the abstract `Causality.J_int`. -/
theorem e0_IJ_calc (p : E0) :
    interior (E0.causality.Jplus ⊤ {p}) ∩ E0.causality.Zminus = E0.causality.Iplus ⊤ {p} ∧
      interior (E0.causality.Jminus ⊤ {p}) ∩ E0.causality.Zplus = E0.causality.Iminus ⊤ {p} :=
  Causality.J_int e0_absolutelyMinimal E0LM.e0_pushUp p

/-- `lem:IJ_calc` at `κ = 0` with `Z⁻(E₀) = reg(E₀)` and `Z⁺(E₀) = E₀` substituted:
`I⁺(p) = Int J⁺(p) ∖ sing₀` and `I⁻(p) = Int J⁻(p)` for every `p`. At a BTZ point the first is
`E0.Iplus_axis_eq_interior_diff`, the second says `Int J⁻(p) = ∅`. -/
theorem e0_IJ_calc_reg (p : E0) :
    interior (E0.causality.Jplus ⊤ {p}) \ E0.axis = E0.causality.Iplus ⊤ {p} ∧
      interior (E0.causality.Jminus ⊤ {p}) = E0.causality.Iminus ⊤ {p} := by
  obtain ⟨h₁, h₂⟩ := e0_IJ_calc p
  rw [e0_Zminus_eq] at h₁
  rw [e0_Zplus_eq, inter_univ] at h₂
  exact ⟨h₁, h₂⟩

/-- **`lem:IJ_calc` for every `κ ≥ 0`** (`ETT.tex:1441`), as printed in both halves. -/
theorem IJ_calc :
    (∀ (α : ℝ) [Fact (0 < α)] (p : Massive α),
      interior ((massive α).Jplus ⊤ {p}) ∩ (massive α).Zminus = (massive α).Iplus ⊤ {p} ∧
        interior ((massive α).Jminus ⊤ {p}) ∩ (massive α).Zplus = (massive α).Iminus ⊤ {p}) ∧
    (∀ p : E0,
      interior (E0.causality.Jplus ⊤ {p}) ∩ E0.causality.Zminus = E0.causality.Iplus ⊤ {p} ∧
        interior (E0.causality.Jminus ⊤ {p}) ∩ E0.causality.Zplus =
          E0.causality.Iminus ⊤ {p}) :=
  ⟨fun _ _ p => massive_IJ_calc p, e0_IJ_calc⟩

/-! ### `lem:densite_modele` -/

/-- In an open set `V`, the closure taken in `V` does not see the part of `A` outside `V`. -/
theorem closure_inter_inter_of_isOpen {X : Type*} [TopologicalSpace X] {V A : Set X}
    (hV : IsOpen V) : closure (A ∩ V) ∩ V = closure A ∩ V := by
  refine Subset.antisymm (fun x hx => ⟨closure_mono inter_subset_left hx.1, hx.2⟩)
    fun x hx => ⟨?_, hx.2⟩
  have := hV.inter_closure ⟨hx.2, hx.1⟩
  rwa [inter_comm] at this

/-- `lem:densite_modele` (a) at `κ = 0`, every point, BTZ points included:
`J⁺(p) = closure I⁺(p)`. Push-up and `Z⁺` in every open set give `⊂`; `J⁺(p)` is closed. -/
theorem e0_densite_a (p : E0) :
    E0.causality.Jplus ⊤ {p} = closure (E0.causality.Iplus ⊤ {p}) :=
  Subset.antisymm
    (Causality.Jplus_subset_closure_Iplus_of_locZplus E0LM.e0_pushUp E0LM.e0_locZplus ⊤ {p})
    (closure_minimal Causality.Iplus_subset_Jplus (E0.isClosed_Jplus p))

/-- `lem:densite_modele` (b) at `κ = 0`, `p ∈ reg(E₀)`: `J⁻(p) = closure I⁻(p)`. A point of
`J⁻(p)` off the axis is in `Z⁻`; a point `q` of `J⁻(p)` on the axis has `τ_q ≤ f(p)`, so the axis
points `(τ_q − ε, 0)` are `≪ p` (`r(p) > 0`) and tend to `q`. -/
theorem e0_densite_b {p : E0} (hp : p ∉ E0.axis) :
    E0.causality.Jminus ⊤ {p} = closure (E0.causality.Iminus ⊤ {p}) := by
  refine Subset.antisymm (fun q hq => ?_)
    (closure_minimal Causality.Iminus_subset_Jminus (E0.isClosed_Jminus p))
  by_cases hqa : q ∈ E0.axis
  · -- `q` on the axis: the axis points just below `q` are chronologically below `p`
    have hqp : q.1 ≤ E0.fcoord p :=
      (E0.le_axis_iff hqa).1 (E0.le_top_iff.1 (Precausality.mem_Jminus_singleton.1 hq))
    rw [mem_closure_iff_nhds]
    intro N hN
    obtain ⟨ε, hε, hmem⟩ := E0.exists_axis_below hqa hN
    refine ⟨_, hmem, Precausality.mem_Iminus_singleton.2 (E0.lt_top_iff.2
      ((E0.lt_axis_iff rfl).2 ⟨E0.rad_pos.2 hp, ?_⟩))⟩
    show q.1 - ε < E0.fcoord p
    linarith
  · exact Causality.Jminus_diff_subset_closure_Iminus_of_locZminus E0LM.e0_pushUp
      E0LM.e0_locZminus ⊤ {p} ⟨hq, hqa⟩

/-- `lem:densite_modele` (c) at `κ = 0`, `p ∈ sing(E₀)`: `J⁻(p) = closure (J⁻(p) ∖ {p})`; the
half-line below `p` is the closure of the open half-line. -/
theorem e0_densite_c {p : E0} (hp : p ∈ E0.axis) :
    E0.causality.Jminus ⊤ {p} = closure (E0.causality.Jminus ⊤ {p} \ {p}) := by
  refine Subset.antisymm (fun q hq => ?_) (closure_minimal sdiff_subset (E0.isClosed_Jminus p))
  by_cases hqp : q = p
  · subst hqp
    rw [mem_closure_iff_nhds]
    intro N hN
    obtain ⟨ε, hε, hmem⟩ := E0.exists_axis_below hp hN
    refine ⟨_, hmem, ?_, fun h => ?_⟩
    · rw [E0.Jminus_axis hp]
      exact ⟨rfl, by show q.1 - ε ≤ q.1; linarith⟩
    · have h1 := congrArg Prod.fst (mem_singleton_iff.1 h)
      simp only at h1
      linarith
  · exact subset_closure ⟨hq, hqp⟩

/-- (a) in a causally convex open subset `V` of `E₀`, with `J⁺`, `I⁺` and the closure taken in
`V`. -/
theorem e0_densite_a_of_causallyConvexIn {V : Opens E0}
    (hV : E0.causality.CausallyConvexIn (V : Set E0) ⊤) {p : E0} (hp : p ∈ V) :
    E0.causality.Jplus V {p} = closure (E0.causality.Iplus V {p}) ∩ V := by
  obtain ⟨hJ, hI, -⟩ := Causality.restriction_convexe_future E0.causallyArcConnected hV
    (singleton_subset_iff.2 hp)
  rw [hJ, hI, e0_densite_a p, closure_inter_inter_of_isOpen V.isOpen]

/-- (b) in a causally convex open subset `V` of `E₀`, `p ∈ V ∩ reg(E₀)`. -/
theorem e0_densite_b_of_causallyConvexIn {V : Opens E0}
    (hV : E0.causality.CausallyConvexIn (V : Set E0) ⊤) {p : E0} (hp : p ∈ V)
    (hpa : p ∉ E0.axis) :
    E0.causality.Jminus V {p} = closure (E0.causality.Iminus V {p}) ∩ V := by
  obtain ⟨hJ, hI, -⟩ := Causality.restriction_convexe_past E0.causallyArcConnected hV
    (singleton_subset_iff.2 hp)
  rw [hJ, hI, e0_densite_b hpa, closure_inter_inter_of_isOpen V.isOpen]

/-- (c) in a causally convex open subset `V` of `E₀`, `p ∈ V ∩ sing(E₀)`. -/
theorem e0_densite_c_of_causallyConvexIn {V : Opens E0}
    (hV : E0.causality.CausallyConvexIn (V : Set E0) ⊤) {p : E0} (hp : p ∈ V)
    (hpa : p ∈ E0.axis) :
    E0.causality.Jminus V {p} = closure (E0.causality.Jminus V {p} \ {p}) ∩ V := by
  obtain ⟨hJ, -, -⟩ := Causality.restriction_convexe_past E0.causallyArcConnected hV
    (singleton_subset_iff.2 hp)
  have hd : (E0.causality.Jminus ⊤ {p} ∩ (V : Set E0)) \ {p} =
      (E0.causality.Jminus ⊤ {p} \ {p}) ∩ V := by
    ext x
    simp only [Set.mem_sdiff, mem_inter_iff]
    tauto
  rw [hJ, hd, closure_inter_inter_of_isOpen V.isOpen, ← e0_densite_c hpa]

/-- `lem:densite_modele` **at `κ = 0`**: (a), (b), (c), and the same in every causally convex open
subset. -/
theorem e0_densite :
    (∀ p : E0, E0.causality.Jplus ⊤ {p} = closure (E0.causality.Iplus ⊤ {p})) ∧
    (∀ p : E0, p ∉ E0.axis →
      E0.causality.Jminus ⊤ {p} = closure (E0.causality.Iminus ⊤ {p})) ∧
    (∀ p : E0, p ∈ E0.axis →
      E0.causality.Jminus ⊤ {p} = closure (E0.causality.Jminus ⊤ {p} \ {p})) ∧
    ∀ V : Opens E0, E0.causality.CausallyConvexIn (V : Set E0) ⊤ → ∀ p ∈ V,
      E0.causality.Jplus V {p} = closure (E0.causality.Iplus V {p}) ∩ V ∧
      (p ∉ E0.axis → E0.causality.Jminus V {p} = closure (E0.causality.Iminus V {p}) ∩ V) ∧
      (p ∈ E0.axis →
        E0.causality.Jminus V {p} = closure (E0.causality.Jminus V {p} \ {p}) ∩ V) :=
  ⟨e0_densite_a, fun _ hp => e0_densite_b hp, fun _ hp => e0_densite_c hp, fun _ hV _ hp =>
    ⟨e0_densite_a_of_causallyConvexIn hV hp, e0_densite_b_of_causallyConvexIn hV hp,
      e0_densite_c_of_causallyConvexIn hV hp⟩⟩

/-- **`lem:densite_modele` for every `κ ≥ 0`** (`ETT.tex:1464`): for `κ > 0`, (a) and (b) at
every point and in every causally convex open subset ((c) is vacuous: `E_α` has no BTZ point);
for `κ = 0`, `e0_densite`. -/
theorem densite_modele :
    (∀ (α : ℝ) [Fact (0 < α)] (p : Massive α),
      ((massive α).Jplus ⊤ {p} = closure ((massive α).Iplus ⊤ {p}) ∧
        (massive α).Jminus ⊤ {p} = closure ((massive α).Iminus ⊤ {p})) ∧
      ∀ V : Opens (Massive α), (massive α).CausallyConvexIn (V : Set (Massive α)) ⊤ → p ∈ V →
        (massive α).Jplus V {p} = closure ((massive α).Iplus V {p}) ∩ V ∧
          (massive α).Jminus V {p} = closure ((massive α).Iminus V {p}) ∩ V) ∧
    ((∀ p : E0, E0.causality.Jplus ⊤ {p} = closure (E0.causality.Iplus ⊤ {p})) ∧
    (∀ p : E0, p ∉ E0.axis →
      E0.causality.Jminus ⊤ {p} = closure (E0.causality.Iminus ⊤ {p})) ∧
    (∀ p : E0, p ∈ E0.axis →
      E0.causality.Jminus ⊤ {p} = closure (E0.causality.Jminus ⊤ {p} \ {p})) ∧
    ∀ V : Opens E0, E0.causality.CausallyConvexIn (V : Set E0) ⊤ → ∀ p ∈ V,
      E0.causality.Jplus V {p} = closure (E0.causality.Iplus V {p}) ∩ V ∧
      (p ∉ E0.axis → E0.causality.Jminus V {p} = closure (E0.causality.Iminus V {p}) ∩ V) ∧
      (p ∈ E0.axis →
        E0.causality.Jminus V {p} = closure (E0.causality.Jminus V {p} \ {p}) ∩ V)) :=
  ⟨fun _ _ p => ⟨massive_densite p, fun _ hV hp => massive_densite_of_causallyConvexIn hV hp⟩,
    e0_densite⟩

/-- The fact `lem:densite_modele`'s proof cites (`ETT.tex:1481–1482`), for `J⁺`: at every point
of `E₀`, `J⁺(p)` is the closure of its interior. -/
theorem e0_Jplus_eq_closure_interior (p : E0) :
    E0.causality.Jplus ⊤ {p} = closure (interior (E0.causality.Jplus ⊤ {p})) :=
  Subset.antisymm ((e0_densite_a p).subset.trans (closure_mono
      (interior_maximal Causality.Iplus_subset_Jplus Causality.isOpen_Iplus)))
    (closure_minimal interior_subset (E0.isClosed_Jplus p))

/-- The cited fact for `J⁻`, off the axis: `J⁻(p)` is the closure of its interior. -/
theorem e0_Jminus_eq_closure_interior {p : E0} (hp : p ∉ E0.axis) :
    E0.causality.Jminus ⊤ {p} = closure (interior (E0.causality.Jminus ⊤ {p})) :=
  Subset.antisymm ((e0_densite_b hp).subset.trans (closure_mono
      (interior_maximal Causality.Iminus_subset_Jminus Causality.isOpen_Iminus)))
    (closure_minimal interior_subset (E0.isClosed_Jminus p))

/-- **The cited fact is false for `J⁻` at a BTZ point** (`ETT.tex:1481–1482`, "for every `p`"):
`J⁻(p)` is the half-line below `p`, whose interior is empty, so it is not the closure of its
interior. -/
theorem e0_Jminus_axis_ne_closure_interior {p : E0} (hp : p ∈ E0.axis) :
    interior (E0.causality.Jminus ⊤ {p}) = ∅ ∧
      E0.causality.Jminus ⊤ {p} ≠ closure (interior (E0.causality.Jminus ⊤ {p})) := by
  have hint : interior (E0.causality.Jminus ⊤ {p}) = ∅ := by
    refine eq_empty_of_subset_empty ?_
    rw [← E0.interior_axis]
    exact interior_mono (E0.Jminus_axis_subset hp ⊤)
  refine ⟨hint, fun h => ?_⟩
  have hpp : p ∈ E0.causality.Jminus ⊤ {p} :=
    Precausality.mem_Jminus_singleton.2 (E0.causality.le_refl trivial)
  rw [h, hint, closure_empty] at hpp
  exact hpp

/-- (b) fails at every BTZ point: `I⁻(p) = ∅`, while `p ∈ J⁻(p)`. The statement excludes these
points; with the hypothesis `p ∈ Z^∓` of `ETT.tex:1482`, read for `J⁻` as `p ∈ Z⁺ = E₀`, the
proof's argument would reach them. -/
theorem e0_Jminus_axis_ne_closure_Iminus {p : E0} (hp : p ∈ E0.axis) :
    E0.causality.Jminus ⊤ {p} ≠ closure (E0.causality.Iminus ⊤ {p}) := by
  intro h
  have hpp : p ∈ E0.causality.Jminus ⊤ {p} :=
    Precausality.mem_Jminus_singleton.2 (E0.causality.le_refl trivial)
  rw [h, E0.Iminus_axis hp ⊤, closure_empty] at hpp
  exact hpp

/-! ### `rem:galileo_spacetime_not_strongly`, the model sentence -/

/-- **`E₀` is strongly causal with open causally convex neighbourhoods**
(`def:strongly_causal_spacetime`, `StronglyCausalOpen`): `E0.stronglyCausal`'s neighbourhood
`J⁺(B) ∩ J⁻(B)`, `B` a small ball, is open because `J^±` of an open set is open. -/
theorem e0_stronglyCausalOpen : E0.causality.StronglyCausalOpen := by
  intro p U hU
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hU
  set B := Metric.ball p (δ / 10)
  have hBo : IsOpen B := Metric.isOpen_ball
  have hpB : p ∈ B := Metric.mem_ball_self (by positivity)
  refine ⟨⟨E0.causality.Jplus ⊤ B ∩ E0.causality.Jminus ⊤ B,
    (E0.isOpen_Jplus hBo).inter (E0.isOpen_Jminus hBo)⟩,
    ⟨⟨p, hpB, E0.causality.le_refl trivial⟩, ⟨p, hpB, E0.causality.le_refl trivial⟩⟩, ?_, ?_⟩
  · rintro z ⟨⟨u, hu, huz⟩, ⟨v, hv, hzv⟩⟩
    apply hball
    have h1 := (E0.le_top_iff.1 huz).dist_le
    have h2 := (E0.le_top_iff.1 hzv).closed.1
    have hu' : dist u p < δ / 10 := hu
    have hv' : dist v p < δ / 10 := hv
    have hτu := abs_lt.1 ((E0.abs_fst_sub_le_dist u p).trans_lt hu')
    have hτv := abs_lt.1 ((E0.abs_fst_sub_le_dist v p).trans_lt hv')
    rw [Metric.mem_ball]
    calc dist z p ≤ dist z u + dist u p := dist_triangle _ _ _
      _ = dist u z + dist u p := by rw [dist_comm z u]
      _ < δ := by linarith [hτu.1, hτu.2, hτv.1, hτv.2]
  · refine ⟨fun _ _ => trivial, fun a ha b hb w hw => ?_⟩
    obtain ⟨⟨u, hu, hua⟩, -⟩ := ha
    obtain ⟨-, ⟨v, hv, hbv⟩⟩ := hb
    have hwb : E0.causality.le ⊤ w b := Precausality.mem_Jminus_singleton.1 hw.1
    have haw : E0.causality.le ⊤ a w := Precausality.mem_Jplus_singleton.1 hw.2
    exact ⟨⟨u, hu, E0.causality.le_trans hua haw⟩, ⟨v, hv, E0.causality.le_trans hwb hbv⟩⟩

/-- Non-vacuity of `lem:densite_modele`'s clauses in causally convex open sets: some causally convex
open `V ≠ E₀` contains the BTZ point `(0, 0)` and a regular point. -/
theorem e0_exists_causallyConvexIn_axis :
    ∃ V : Opens E0, ((0 : ℝ), (0 : ℂ)) ∈ V ∧ (∃ q ∈ V, q ∉ E0.axis) ∧ (V : Set E0) ≠ univ ∧
      E0.causality.CausallyConvexIn (V : Set E0) ⊤ := by
  obtain ⟨V, hpV, hVU, hconv⟩ :=
    e0_stronglyCausalOpen ((0 : ℝ), (0 : ℂ)) _ (Metric.ball_mem_nhds _ one_pos)
  refine ⟨V, hpV, ?_, fun h => ?_, hconv⟩
  · by_contra hq
    have hq' : (V : Set E0) ⊆ E0.axis := fun q hqV => by
      by_contra hqa
      exact hq ⟨q, hqV, hqa⟩
    have hsub : (V : Set E0) ⊆ interior E0.axis := interior_maximal hq' V.isOpen
    rw [E0.interior_axis] at hsub
    exact hsub hpV
  have h5 : (((5 : ℝ), (0 : ℂ)) : E0) ∈ Metric.ball (((0 : ℝ), (0 : ℂ)) : E0) 1 :=
    hVU (h ▸ mem_univ _)
  rw [Metric.mem_ball] at h5
  have h5' : dist (5 : ℝ) 0 < 1 := (le_max_left _ _).trans_lt h5
  rw [Real.dist_eq] at h5'
  norm_num at h5'

/-- **The model sentence of `rem:galileo_spacetime_not_strongly` for every `κ ≥ 0`**
(`ETT.tex:672–673`): `E_α` (`α > 0`) and `E₀` are strongly causal, in both readings. -/
theorem models_stronglyCausal :
    (∀ (α : ℝ) [Fact (0 < α)], (massive α).StronglyCausal ∧ (massive α).StronglyCausalOpen) ∧
    (E0.causality.StronglyCausal ∧ E0.causality.StronglyCausalOpen) :=
  ⟨fun _ _ => ⟨massive_stronglyCausal, massive_stronglyCausalOpen⟩, E0.stronglyCausal,
    e0_stronglyCausalOpen⟩

end ModelRowsE0

end Causal
