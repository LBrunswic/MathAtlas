import Causal.CorrespondingPoints
import Causal.LocateExtension

/-!
# Sbierski Prop 3.7 (i) ⇒ (ii), model-free: a timelike curve ending at `p` is carried to `q`

ETT programme, layer 1 (`programme/roadmap.toml` T-abs-sbierski-prop-3-7). Cited, **not marked**:
`mghdprop:EquivCha` — `Maximal_GHD2.tex:544` (proof `:563–581`), Sbierski 1309.7591 Prop 3.7.
(i) ⇒ (ii), the target, is proved in full (`sbierski_prop_3_7_i_imp_ii`); the label's
(ii) ⇒ (iii), and the uniqueness through it, ask causal arc-connectedness (SCOPE). Imports
`Causal.CorrespondingPoints` and `Causal.LocateExtension` only: no model, no `Causal.CBG.*`
module, directly or transitively. **No A3**: nothing here uses `Causal.CBG.Geometry` or
`germExt_*`, so these declarations may discharge A3 (Sbierski proves Lemma 3.8 = A3 from (ii)).
No `sorry`.

> Let $U$ be a CGHD of $M$ and $M'$ with isometric embedding $\psi : U \subseteq M \to M'$.
> The following statements are equivalent: i) The points $p \in \partial U$ and
> $p' \in \partial \psi(U)$ are corresponding boundary points. ii) If
> $\gamma : (-\varepsilon, 0) \to U$ is a timelike curve with $\lim_{s \nearrow 0} \gamma(s) = p$,
> then $\lim_{s \nearrow 0} (\psi \circ \gamma) (s) = p'$. iii) There is a timelike curve
> $\gamma : (-\varepsilon, 0) \to U$ with $\lim_{s \nearrow 0} \gamma(s) = p$ such that
> $\lim_{s \nearrow 0} \psi \circ \gamma (s) = p'$. In particular it follows from ii) and iii)
> that $p \in \partial U$ has at most one corresponding boundary point. (`:546–553`)

> […] we get $\psi(q) \leq p'$ since the relation $\leq$ is closed on globally hyperbolic
> manifolds. […] take an $s \in U$ with $q \ll s \ll p$ […] $\psi(q) \ll \psi(s) \leq p'$, and
> thus $\psi(q) \ll p'$. […] Since $M'$ satisfies the strong causality condition, we can find a
> $q' \in V' \cap I^-(p',M')$ such that $I^+(q',M') \cap I^-(p',M') \subseteq V'$. […] we know
> that $q := \psi^{-1}(q') \in I^-(p,M)$. (`:569–580`)

## What is proved

* **(i) ⇒ (ii)**, `CBG.sbierski_prop_3_7_i_imp_ii`: for `IsCorrPair C D U V ψ g`, the `K`-calculus
  on both spacetimes in both time directions (`KSide C S _`, `KSide C.dual S' _`, `KSide D T _`,
  `KSide D.dual T' _`, any sets), `D` strongly causal and `V` causally convex, if `p`, `q`
  correspond then `ψ ∘ γ → q` for **every** timelike curve `γ` of `U` over `(a, 0)` with
  `γ → p`, future or past (`Causality.TimelikeCurveIn`); no side of a Cauchy surface, no
  `p ∈ ∂U`, no `q ∈ ∂V`, no convexity of `U`. Strong causality from GH:
  `_of_globallyHyperbolic`. **From ladder properties only**, no `KSide`:
  `sbierski_prop_3_7_i_imp_ii_ladder` (push-up, GH, tarentin on both sides, `N` causally
  arc-connected, Hausdorff). Sbierski's "without loss of generality" forms, which ask the
  `K`-calculus of one time direction only: `IsCorrPair.tendsto_comp_of_kSide` (`p ∈ J⁺(S)`; a
  past curve cannot end at `p`, `Causality.false_of_tendsto_past`) and `_past`.
* The core, with the named facts it uses: `IsCorrPair.tendsto_comp_of_chain` (a chronological
  chain, not a curve: push-up and closed `J⁺` of points on both sides, `q ∈ Z⁻`, strong causality
  of `D`, `V` convex); `tendsto_comp_of_chronalCurveOn`, `_past`, `_kSide`; Sbierski's first step
  `IsCorrPair.lt_of_tendsto_of_chain` (`ψ(γ s) ≪ q`), `Causality.lt_of_tendsto_of_chain`.
* **The equivalence** (i) ⟺ (ii) ⟺ (iii), `CBG.sbierski_prop_3_7` (`p ∈ J⁺(S) ∪ J⁻(S)`,
  `_future`, `_past`), and "at most one corresponding point", `sbierski_prop_3_7_unique`, with no
  condition on `q`, `q'`; both **under causal arc-connectedness of `M` and `p` regular** (SCOPE).
  `Causality.exists_chronalCurve_tendsto`, `KSide.exists_timelikeCurveIn_tendsto`: a timelike
  curve of `U` ending at `p`. `eq_of_corresponds_of_timelikeCurveIn`: uniqueness given one.
* **Witnesses** (kb/0011): `timelikeLine_sbierski_prop_3_7` (every hypothesis, with the curve
  `s ↦ 1 + s` and the conclusion); `lightlikeLine_sbierski_prop_3_7_iii_fails`: at a BTZ point
  (i) holds and (iii) fails, every other hypothesis of `sbierski_prop_3_7_future` holding;
  `timelikeLine_sbierski_prop_3_7_ladder`.

## Hypothesis checklist

| paper | here |
|---|---|
| `U` a CGHD of `M`, `M'`, `ψ` an isometric embedding | ⚠ replaced: `IsCorrPair` (`ψ : U → V` with continuous inverse `g`, carrying `≤`, `≪` of `M` onto those of `N`), `KSide` (named facts, kb/0012), `V` causally convex (`U` too in the WLOG forms and the equivalence); the CGHD setting supplies them (`CBG.CGHDData.isCorrPair`, `kSide_future`/`kSide_past`, `causallyConvexIn`/`causallyConvexIn'`) |
| `p ∈ ∂U`, `p' ∈ ∂ψ(U)` | ⚠ weakened in (i) ⇒ (ii): not used; `p ∈ ∂U` carried in the equivalence |
| WLOG `p`, `p'` to the future (`:564`, footnote) | ⚠ weakened: not needed by `sbierski_prop_3_7_i_imp_ii`; the WLOG forms ask `p ∈ J⁺(S)` only |
| "timelike curve `γ : (−ε, 0) → U`" | ✓ carried: `TimelikeCurveIn` — a future or past chronal curve of `U` over every segment of `(a, 0)`, `a < 0`; the core asks a chronological chain only |
| `≤` closed (O'Neill 14.22) | ✓ carried: `KSide.isClosed_Jplus`/`_Jminus`, or GH and tarentin (ladder form); only `J^±` of points of `U`, `V` |
| `ψ(q) ≪ ψ(s) ≤ p' ⇒ ψ(q) ≪ p'` (O'Neill 10.46) | ✓ carried: push-up (`KSide.pushUp`), on both sides |
| `t'_i ≫ p'`, `t'_i → p'` (`:568–569`) | ⚠ weakened: not used (`J⁺(ψ x)` closed, `IsCorrPair.le_of_corresponds`) |
| "an `s ∈ U` with `q ≪ s ≪ p`" (`:571`) | ⚠ weakened: on `M`'s side the curve's own points interpolate |
| `M'` strongly causal | ✓ carried: `D.StronglyCausal`; from GH and tarentin in `_of_globallyHyperbolic` and `_ladder` |
| "`q' ∈ V' ∩ I⁻(p')`", the "other inclusion by symmetry" | ✓ carried: `q ∈ Z⁻(N)` — `KSide.mem_Zminus` (`q` is regular: `ψ(γ s) ≪ q`, `KSide.Iminus_sing`); ⚠ in the ladder form, an added hypothesis instead: causal arc-connectedness of `N` (`CausallyArcConnected.mem_Zminus_iff`) |
| (ii) ⇒ (iii) "trivial" (`:564`) | ⚠ strengthened: a timelike curve of `U` ending at `p` — `C.CausallyArcConnected` and `p ∉ Sing` (SCOPE) |
| uniqueness | ✓ carried: `[T2Space N]` (manifolds are Hausdorff) |

## SCOPE (disclosed)

* **(ii) ⇒ (iii) needs a timelike curve of `U` ending at `p`.** Sbierski's "trivial" uses one;
  in ETT it comes from causal arc-connectedness (`def:causal_arc_connectedness`, the ETT form of
  the paper's `p ≪ q` "iff there is a future directed timelike curve", `:558`), outside the
  target's `uses`, and from a regular `p`: at a BTZ point (`I⁻(p) = ∅`) no chronal curve ends at
  `p`, so (ii) is vacuous and (iii) false while (i) may hold
  (`lightlikeLine_sbierski_prop_3_7_iii_fails`). In the paper's smooth setting `Sing = ∅`; in the
  CBG setting arc-connectedness is `SingularFlatAxioms.causallyArcConnected`, and `p` may be BTZ.
  Hence the label is not marked; (i) ⇒ (ii) needs neither.
* **`q := ψ⁻¹(q')` asks `q' ∈ ψ(U)`** (`:580`), which "`q' ∈ V' ∩ I⁻(p')`" (`:573`) does not
  give. Here `q'` is taken in `I⁺(ψ(γ s₀))`, and causal convexity of `V` puts it in `V`
  (`Causality.mem_of_le_of_lt_of_mem_closure`).
* The paper's first claim, `ψ(I⁻(p) ∩ U) = I⁻(p') ∩ ψ(U)`, is used only at the points it needs:
  the curve's (`IsCorrPair.lt_of_tendsto_of_chain`) and `q'`; the library's `K⁻` form is
  `IsCorrPair.image_Kminus_eq` (`Causal.CorrespondingPoints`).
* `Z⁻` at `q` (`def:strongly_tarentin_point`, the paper's "pick a point `q' ∈ W' ∩ I⁻(p')`",
  `:573` footnote) is not a ladder node: it is a `KSide` field, or follows from causal
  arc-connectedness of `N` (the ladder form). Whether (ii) holds with `Causality.Tarentin` alone
  in its place is not settled here (open).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set Topology Filter Function TopologicalSpace

universe u v

namespace Causality

variable {M : Type u} [TopologicalSpace M] {C : Causality M} {U : Opens M} {γ : ℝ → M}
  {a b : ℝ} {p : M}

/-- Sbierski's "timelike curve `γ : (a, b) → U`" (Prop 3.7 (ii), (iii), `Maximal_GHD2.tex:550`):
a future or a past chronal curve of the open set `U` over every segment of `(a, b)`. -/
def TimelikeCurveIn (C : Causality M) (U : Opens M) (γ : ℝ → M) (a b : ℝ) : Prop :=
  (∀ s ∈ Ioo a b, ∀ s' ∈ Ioo a b, C.ChronalCurveOn U γ s s') ∨
    ∀ s ∈ Ioo a b, ∀ s' ∈ Ioo a b, C.dual.ChronalCurveOn U γ s s'

theorem dual_timelikeCurveIn : C.dual.TimelikeCurveIn U γ a b ↔ C.TimelikeCurveIn U γ a b :=
  or_comm

/-- A timelike curve of `U` lies in `U`. -/
theorem TimelikeCurveIn.mem (hγ : C.TimelikeCurveIn U γ a b) {s : ℝ} (hs : s ∈ Ioo a b) :
    γ s ∈ U := by
  rcases hγ with hf | hpast
  · exact (hf s hs s hs).mem s ⟨le_rfl, le_rfl⟩
  · exact (hpast s hs s hs).mem s ⟨le_rfl, le_rfl⟩

/-- **A chronological chain tending to `p` lies in `I⁻(p)`** (Sbierski, `:580`: "`γ(s) ∈ I⁻(p)`"):
with push-up and `J⁺` of the chain's points closed, `γ s ≪ γ s' ≤ p`. -/
theorem lt_of_tendsto_of_chain (hP : C.PushUp) (hJ : ∀ s ∈ Ioo a b, IsClosed (C.Jplus ⊤ {γ s}))
    (hlt : ∀ s ∈ Ioo a b, ∀ s' ∈ Ioo a b, s < s' → C.lt ⊤ (γ s) (γ s'))
    (hlim : Tendsto γ (𝓝[<] b) (𝓝 p)) {s : ℝ} (hs : s ∈ Ioo a b) : C.lt ⊤ (γ s) p := by
  have hs' : (s + b) / 2 ∈ Ioo a b := ⟨by linarith [hs.1, hs.2], by linarith [hs.2]⟩
  have hss' : s < (s + b) / 2 := by linarith [hs.2]
  have hle : C.le ⊤ (γ ((s + b) / 2)) p := by
    have hmem : p ∈ closure (C.Jplus ⊤ {γ ((s + b) / 2)}) := by
      apply mem_closure_of_tendsto hlim
      filter_upwards [Ioo_mem_nhdsLT hs'.2] with t ht
      rw [Precausality.mem_Jplus_singleton]
      exact C.le_of_lt (hlt _ hs' t ⟨hs'.1.trans ht.1, ht.2⟩ ht.1)
    rw [(hJ _ hs').closure_eq, Precausality.mem_Jplus_singleton] at hmem
    exact hmem
  exact hP.lt_of_lt_of_le (hlt s hs _ hs' hss') hle

/-- For `V` causally convex and `q ∈ closure V`: a point above a point of `V` and in `I⁻(q)` is in
`V` (no first countability; `I⁺(z)` is a neighbourhood of `q`, so it meets `V`). -/
theorem mem_of_le_of_lt_of_mem_closure {V : Set M} (hV : C.CausallyConvexIn V ⊤) {y z q : M}
    (hy : y ∈ V) (hyz : C.le ⊤ y z) (hzq : C.lt ⊤ z q) (hq : q ∈ closure V) : z ∈ V := by
  obtain ⟨v, hvI, hvV⟩ := mem_closure_iff_nhds.1 hq _
    (Causality.isOpen_Iplus.mem_nhds (show q ∈ C.Iplus ⊤ {z} by simpa using hzq))
  exact hV.2 y hy v hvV (mem_diamond.2 ⟨hyz, C.le_of_lt (by simpa using hvI)⟩)

/-- **Sbierski's "(necessarily) future directed"** (`:564`): no past chronal curve of a causally
convex `U ⊇ S` ends at a point of `J⁺(S) ∖ U`, when `J⁻` of the points of `U` is closed. -/
theorem false_of_tendsto_past (hJ : ∀ x ∈ U, IsClosed (C.Jminus ⊤ {x}))
    (hcv : C.CausallyConvexIn (U : Set M) ⊤) {S : Set M} (hSU : S ⊆ U) (hpU : p ∉ U)
    (hpS : p ∈ C.Jplus ⊤ S) (hab : a < b)
    (hγ : ∀ s ∈ Ioo a b, ∀ s' ∈ Ioo a b, C.dual.ChronalCurveOn U γ s s')
    (hlim : Tendsto γ (𝓝[<] b) (𝓝 p)) : False := by
  have hs : (a + b) / 2 ∈ Ioo a b := ⟨by linarith, by linarith⟩
  have hsU : γ ((a + b) / 2) ∈ U := (hγ _ hs _ hs).mem _ ⟨le_rfl, le_rfl⟩
  have hmem : p ∈ closure (C.Jminus ⊤ {γ ((a + b) / 2)}) := by
    apply mem_closure_of_tendsto hlim
    filter_upwards [Ioo_mem_nhdsLT hs.2] with t ht
    have htI : t ∈ Ioo a b := ⟨hs.1.trans ht.1, ht.2⟩
    have hlt : C.dual.lt U (γ ((a + b) / 2)) (γ t) :=
      (hγ _ hs t htI).lt_of_lt le_rfl ht.1 le_rfl
    rw [Precausality.mem_Jminus_singleton]
    exact C.le_of_lt (C.lt_mono le_top hlt)
  rw [(hJ _ hsU).closure_eq, Precausality.mem_Jminus_singleton] at hmem
  obtain ⟨σ, hσ, hσp⟩ := hpS
  exact hpU (hcv.2 σ (hSU hσ) _ hsU (mem_diamond.2 ⟨hσp, hmem⟩))

/-- **A timelike curve of `U` ending at `p`**, from a point `x ∈ U ∩ I⁻(p)`, `U` causally convex,
`p ∈ closure U`: the chronal curve from `x` to `p` given by causal arc-connectedness, run over
`(-1, 0)`. -/
theorem exists_chronalCurve_tendsto (hac : C.CausallyArcConnected)
    (hcv : C.CausallyConvexIn (U : Set M) ⊤) {x : M} (hxU : x ∈ U) (hxp : C.lt ⊤ x p)
    (hpU : p ∈ closure (U : Set M)) :
    ∃ γ : ℝ → M, (∀ s ∈ Ioo (-1 : ℝ) 0, ∀ s' ∈ Ioo (-1 : ℝ) 0, C.ChronalCurveOn U γ s s') ∧
      Tendsto γ (𝓝[<] 0) (𝓝 p) := by
  obtain ⟨c, hc, hc0, hc1⟩ := (hac ⊤ le_rfl x p).2.1 hxp
  have hcU : ∀ t ∈ Ico (0 : ℝ) 1, c t ∈ U := by
    intro t ht
    have h1 : C.le ⊤ x (c t) := by
      rw [← hc0]; exact hc.causalCurveOn.le_of_le le_rfl ht.1 ht.2.le
    have h2 : C.lt ⊤ (c t) p := by
      rw [← hc1]; exact hc.lt_of_lt ht.1 ht.2 le_rfl
    exact mem_of_le_of_lt_of_mem_closure hcv hxU h1 h2 hpU
  refine ⟨fun s => c (1 * s + 1), fun s hs s' hs' => ?_, ?_⟩
  · refine CurveOn.comp_affine one_pos (CurveOn.restrict hc (by linarith [hs.1])
      (by linarith [hs'.2]) le_top fun t ht => hcU t ⟨by linarith [hs.1, ht.1], ?_⟩)
    linarith [hs'.2, ht.2]
  · have hcont : ContinuousWithinAt c (Icc 0 1) 1 :=
      CurveOn.continuousOn C.isRelFamily_lt hc 1 ⟨zero_le_one, le_rfl⟩
    rw [ContinuousWithinAt, hc1] at hcont
    refine hcont.comp (tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩)
    · have : Tendsto (fun s : ℝ => 1 * s + 1) (𝓝 0) (𝓝 (1 * 0 + 1)) :=
        ((continuous_const.mul continuous_id).add continuous_const).tendsto 0
      rw [mul_zero, zero_add] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsLT (show (-1 : ℝ) < 0 by norm_num)] with s hs
      exact ⟨by linarith [hs.1], by linarith [hs.2]⟩

end Causality

namespace CBG

variable {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]
  {C : Causality M} {D : Causality N} {U : Opens M} {V : Opens N} {ψ : M → N} {g : N → M}
  {p : M} {q : N} {γ : ℝ → M} {a b : ℝ}

namespace IsCorrPair

/-- A point corresponding to a point of `M` lies in `closure V`. -/
theorem mem_closure_target_of_corresponds (h : IsCorrPair C D U V ψ g)
    (hc : Corresponds (U : Set M) ψ p q) : q ∈ closure (V : Set N) :=
  mem_closure_iff_nhds.2 fun O' hO' => by
    obtain ⟨x, hxU, -, hψ⟩ := hc univ univ_mem O' hO'
    exact ⟨ψ x, hψ, h.mapsTo hxU⟩

/-- **Sbierski's first step, at the curve's points** (`:566–571`, "`ψ(q) ≪ p'`"): a chronological
chain of `U` tending to `p` is carried into `I⁻(q)`. The interpolant `q ≪ s ≪ p` of the paper is
the chain's next point. -/
theorem lt_of_tendsto_of_chain (h : IsCorrPair C D U V ψ g) (hPC : C.PushUp)
    (hJC : ∀ x ∈ U, IsClosed (C.Jplus ⊤ {x})) (hPD : D.PushUp)
    (hJD : ∀ y ∈ V, IsClosed (D.Jplus ⊤ {y})) (hc : Corresponds (U : Set M) ψ p q)
    (hmem : ∀ s ∈ Ioo a b, γ s ∈ U)
    (hlt : ∀ s ∈ Ioo a b, ∀ s' ∈ Ioo a b, s < s' → C.lt ⊤ (γ s) (γ s'))
    (hlim : Tendsto γ (𝓝[<] b) (𝓝 p)) {s : ℝ} (hs : s ∈ Ioo a b) : D.lt ⊤ (ψ (γ s)) q := by
  have hs' : (s + b) / 2 ∈ Ioo a b := ⟨by linarith [hs.1, hs.2], by linarith [hs.2]⟩
  have hss' : s < (s + b) / 2 := by linarith [hs.2]
  have hγp := Causality.lt_of_tendsto_of_chain hPC (fun t ht => hJC _ (hmem t ht)) hlt hlim hs'
  exact h.lt_of_corresponds hPD (hJD _ (h.mapsTo (hmem _ hs'))) (hmem s hs) (hmem _ hs')
    (hlt s hs _ hs' hss') (Causality.Jplus_mem_nhds_of_lt hγp) hc

/-- **Prop 3.7 (i) ⇒ (ii), the core**, for a chronological chain `γ` of `U` over `(a, b)` (a
curve is not needed): push-up and closed `J⁺` of points on both sides, `q` strongly tarentin in
the past, `D` strongly causal, `V` causally convex. Sbierski's proof (`:573–580`): a causally
convex `W ⊆ O'` around `q`, `q' ∈ W ∩ I⁻(q)` taken in `V`, `g q' ≪ p`, and eventually
`ψ(γ s) ∈ J(q', q) ⊆ W`. -/
theorem tendsto_comp_of_chain (h : IsCorrPair C D U V ψ g) (hPC : C.PushUp)
    (hJC : ∀ x ∈ U, IsClosed (C.Jplus ⊤ {x})) (hPD : D.PushUp)
    (hJD : ∀ y ∈ V, IsClosed (D.Jplus ⊤ {y})) (hSC : D.StronglyCausal)
    (hcvN : D.CausallyConvexIn (V : Set N) ⊤) (hZ : q ∈ D.Zminus)
    (hc : Corresponds (U : Set M) ψ p q) (hab : a < b) (hmem : ∀ s ∈ Ioo a b, γ s ∈ U)
    (hlt : ∀ s ∈ Ioo a b, ∀ s' ∈ Ioo a b, s < s' → C.lt ⊤ (γ s) (γ s'))
    (hlim : Tendsto γ (𝓝[<] b) (𝓝 p)) : Tendsto (ψ ∘ γ) (𝓝[<] b) (𝓝 q) := by
  have hqV : q ∈ closure (V : Set N) := h.mem_closure_target_of_corresponds hc
  have hψq : ∀ s ∈ Ioo a b, D.lt ⊤ (ψ (γ s)) q := fun s hs =>
    h.lt_of_tendsto_of_chain hPC hJC hPD hJD hc hmem hlt hlim hs
  have hs₀ : (a + b) / 2 ∈ Ioo a b := ⟨by linarith, by linarith⟩
  have hy₀V : ψ (γ ((a + b) / 2)) ∈ V := h.mapsTo (hmem _ hs₀)
  rw [tendsto_def]
  intro O' hO'
  -- strong causality at `q`: a causally convex neighbourhood `W ⊆ O'`
  obtain ⟨W, hW, hWO, hWc⟩ := hSC q O' hO'
  -- `q' ∈ W ∩ I⁻(q) ∩ I⁺(y₀)`, a point of `V` (Sbierski: "a `q' ∈ V' ∩ I⁻(p')`")
  have hI₀ : D.Iplus ⊤ {ψ (γ ((a + b) / 2))} ∈ 𝓝 q :=
    Causality.isOpen_Iplus.mem_nhds (by simpa using hψq _ hs₀)
  obtain ⟨q', hq'q, hq'W, hq'y⟩ := hZ _ (inter_mem hW hI₀)
  rw [Precausality.mem_Iminus_singleton] at hq'q
  rw [Precausality.mem_Iplus_singleton] at hq'y
  have hq'V : q' ∈ V :=
    Causality.mem_of_le_of_lt_of_mem_closure hcvN hy₀V (D.le_of_lt hq'y) hq'q hqV
  -- an interpolant `q' ≪ s' ≪ q` in `V`, so that `g q' ≪ p` (the paper's "other inclusion")
  obtain ⟨s', hs'q, hs'q'⟩ := hZ _
    (Causality.isOpen_Iplus.mem_nhds (show q ∈ D.Iplus ⊤ {q'} by simpa using hq'q))
  rw [Precausality.mem_Iminus_singleton] at hs'q
  rw [Precausality.mem_Iplus_singleton] at hs'q'
  have hs'V : s' ∈ V :=
    Causality.mem_of_le_of_lt_of_mem_closure hcvN hq'V (D.le_of_lt hs'q') hs'q hqV
  have hgq' : C.lt ⊤ (g q') p :=
    h.symm.lt_of_corresponds hPC (hJC _ (h.mapsTo_inv hs'V)) hq'V hs'V hs'q'
      (Causality.Jplus_mem_nhds_of_lt hs'q) (h.corresponds_symm hc)
  -- eventually `γ s ∈ I⁺(g q')`, so `ψ (γ s) ∈ J(q', q) ⊆ W ⊆ O'`
  have hev : ∀ᶠ s in 𝓝[<] b, γ s ∈ C.Iplus ⊤ {g q'} :=
    hlim (Causality.isOpen_Iplus.mem_nhds (by simpa using hgq'))
  filter_upwards [hev, Ioo_mem_nhdsLT hab] with s hsI hs
  have h1 : D.lt ⊤ q' (ψ (γ s)) := by
    have := (h.lt_iff _ (h.mapsTo_inv hq'V) _ (hmem s hs)).1 (by simpa using hsI)
    rwa [h.rightInvOn hq'V] at this
  exact hWO (hWc.2 q' hq'W q (mem_of_mem_nhds hW)
    (Causality.mem_diamond.2 ⟨D.le_of_lt h1, D.le_of_lt (hψq s hs)⟩))

/-- Prop 3.7 (i) ⇒ (ii) for a **future** chronal curve of `U` over `(a, b)`. -/
theorem tendsto_comp_of_chronalCurveOn (h : IsCorrPair C D U V ψ g) (hPC : C.PushUp)
    (hJC : ∀ x ∈ U, IsClosed (C.Jplus ⊤ {x})) (hPD : D.PushUp)
    (hJD : ∀ y ∈ V, IsClosed (D.Jplus ⊤ {y})) (hSC : D.StronglyCausal)
    (hcvN : D.CausallyConvexIn (V : Set N) ⊤) (hZ : q ∈ D.Zminus)
    (hc : Corresponds (U : Set M) ψ p q) (hab : a < b)
    (hγ : ∀ s ∈ Ioo a b, ∀ s' ∈ Ioo a b, C.ChronalCurveOn U γ s s')
    (hlim : Tendsto γ (𝓝[<] b) (𝓝 p)) : Tendsto (ψ ∘ γ) (𝓝[<] b) (𝓝 q) :=
  h.tendsto_comp_of_chain hPC hJC hPD hJD hSC hcvN hZ hc hab
    (fun s hs => (hγ s hs s hs).mem s ⟨le_rfl, le_rfl⟩)
    (fun s hs s' hs' hss' => C.lt_mono le_top ((hγ s hs s' hs').lt_of_lt le_rfl hss' le_rfl))
    hlim

/-- Prop 3.7 (i) ⇒ (ii) for a **past** chronal curve: the future statement for `C.dual`,
`D.dual` (closed `J⁻`, `q ∈ Z⁺`). -/
theorem tendsto_comp_of_chronalCurveOn_past (h : IsCorrPair C D U V ψ g) (hPC : C.PushUp)
    (hJC : ∀ x ∈ U, IsClosed (C.Jminus ⊤ {x})) (hPD : D.PushUp)
    (hJD : ∀ y ∈ V, IsClosed (D.Jminus ⊤ {y})) (hSC : D.StronglyCausal)
    (hcvN : D.CausallyConvexIn (V : Set N) ⊤) (hZ : q ∈ D.Zplus)
    (hc : Corresponds (U : Set M) ψ p q) (hab : a < b)
    (hγ : ∀ s ∈ Ioo a b, ∀ s' ∈ Ioo a b, C.dual.ChronalCurveOn U γ s s')
    (hlim : Tendsto γ (𝓝[<] b) (𝓝 p)) : Tendsto (ψ ∘ γ) (𝓝[<] b) (𝓝 q) :=
  h.dual.tendsto_comp_of_chronalCurveOn (Causality.dual_pushUp.2 hPC) hJC
    (Causality.dual_pushUp.2 hPD) hJD (Causality.dual_stronglyCausal.2 hSC)
    (Causality.dual_causallyConvexIn.2 hcvN) hZ hc hab hγ hlim

/-- Prop 3.7 (i) ⇒ (ii) for a future chronal curve, under the `K`-calculus of `KSide` (any sets):
`q` is regular, since `ψ(γ s) ≪ q` while `I⁻ = ∅` at the singular points, so `q ∈ Z⁻`. -/
theorem tendsto_comp_of_chronalCurveOn_kSide (h : IsCorrPair C D U V ψ g) {S SingM : Set M}
    {T SingN : Set N} (hM : KSide C S SingM) (hN : KSide D T SingN) (hSC : D.StronglyCausal)
    (hcvN : D.CausallyConvexIn (V : Set N) ⊤) (hc : Corresponds (U : Set M) ψ p q) (hab : a < b)
    (hγ : ∀ s ∈ Ioo a b, ∀ s' ∈ Ioo a b, C.ChronalCurveOn U γ s s')
    (hlim : Tendsto γ (𝓝[<] b) (𝓝 p)) : Tendsto (ψ ∘ γ) (𝓝[<] b) (𝓝 q) := by
  have hZ : q ∈ D.Zminus := by
    by_cases hq : q ∈ SingN
    · exfalso
      have hs₀ : (a + b) / 2 ∈ Ioo a b := ⟨by linarith, by linarith⟩
      have hlt := h.lt_of_tendsto_of_chain hM.pushUp (fun x _ => hM.isClosed_Jplus x) hN.pushUp
        (fun y _ => hN.isClosed_Jplus y) hc (fun s hs => (hγ s hs s hs).mem s ⟨le_rfl, le_rfl⟩)
        (fun s hs s' hs' hss' => C.lt_mono le_top ((hγ s hs s' hs').lt_of_lt le_rfl hss' le_rfl))
        hlim hs₀
      have hmem : ψ (γ ((a + b) / 2)) ∈ D.Iminus ⊤ {q} := by simpa using hlt
      rw [hN.Iminus_sing q hq] at hmem
      exact hmem
    · exact hN.mem_Zminus q hq
  exact h.tendsto_comp_of_chronalCurveOn hM.pushUp (fun x _ => hM.isClosed_Jplus x) hN.pushUp
    (fun y _ => hN.isClosed_Jplus y) hSC hcvN hZ hc hab hγ hlim

/-- **Prop 3.7 (i) ⇒ (ii), future side**, Sbierski's "without loss of generality" (`:564`): for
`p ∈ ∂U ∩ J⁺(S)`, `S ⊆ U`, `U` causally convex, and the future `K`-calculus on both sides, every
timelike curve of `U` ending at `p` is carried to one ending at `q`. A past one cannot end at `p`
(`Causality.false_of_tendsto_past`). -/
theorem tendsto_comp_of_kSide (h : IsCorrPair C D U V ψ g) {S SingM : Set M} {T SingN : Set N}
    (hM : KSide C S SingM) (hN : KSide D T SingN) (hSC : D.StronglyCausal)
    (hcvM : C.CausallyConvexIn (U : Set M) ⊤) (hcvN : D.CausallyConvexIn (V : Set N) ⊤)
    (hSU : S ⊆ U) (hp : p ∈ frontier (U : Set M)) (hpS : p ∈ C.Jplus ⊤ S)
    (hc : Corresponds (U : Set M) ψ p q) (ha : a < 0) (hγ : C.TimelikeCurveIn U γ a 0)
    (hlim : Tendsto γ (𝓝[<] 0) (𝓝 p)) : Tendsto (ψ ∘ γ) (𝓝[<] 0) (𝓝 q) := by
  rcases hγ with hf | hpast
  · exact h.tendsto_comp_of_chronalCurveOn_kSide hM hN hSC hcvN hc ha hf hlim
  · have hpU : p ∉ (U : Set M) := by rw [U.isOpen.frontier_eq] at hp; exact hp.2
    exact (Causality.false_of_tendsto_past (fun x _ => hM.isClosed_Jminus x) hcvM hSU hpU hpS ha
      hpast hlim).elim

/-- **Prop 3.7 (i) ⇒ (ii), past side**: `tendsto_comp_of_kSide` for `C.dual`, `D.dual`. -/
theorem tendsto_comp_of_kSide_past (h : IsCorrPair C D U V ψ g) {S SingM : Set M}
    {T SingN : Set N} (hM : KSide C.dual S SingM) (hN : KSide D.dual T SingN)
    (hSC : D.StronglyCausal) (hcvM : C.CausallyConvexIn (U : Set M) ⊤)
    (hcvN : D.CausallyConvexIn (V : Set N) ⊤) (hSU : S ⊆ U) (hp : p ∈ frontier (U : Set M))
    (hpS : p ∈ C.Jminus ⊤ S) (hc : Corresponds (U : Set M) ψ p q) (ha : a < 0)
    (hγ : C.TimelikeCurveIn U γ a 0) (hlim : Tendsto γ (𝓝[<] 0) (𝓝 p)) :
    Tendsto (ψ ∘ γ) (𝓝[<] 0) (𝓝 q) :=
  h.dual.tendsto_comp_of_kSide hM hN (Causality.dual_stronglyCausal.2 hSC)
    (Causality.dual_causallyConvexIn.2 hcvM) (Causality.dual_causallyConvexIn.2 hcvN) hSU hp hpS
    hc ha (Causality.dual_timelikeCurveIn.2 hγ) hlim

end IsCorrPair

/-- **Sbierski Prop 3.7 (i) ⇒ (ii)** (`Maximal_GHD2.tex:549–550`), model-free, in both time
orientations and with no side of a Cauchy surface: for corresponding `p`, `q` of a pair
`IsCorrPair C D U V ψ g`, with the future and past `K`-calculus on both spacetimes, `D` strongly
causal and `V` causally convex, `ψ ∘ γ → q` for every timelike curve `γ : (a, 0) → U` with
`γ → p`. -/
theorem sbierski_prop_3_7_i_imp_ii (h : IsCorrPair C D U V ψ g) {S S' SingM SingM' : Set M}
    {T T' SingN SingN' : Set N} (hM : KSide C S SingM) (hM' : KSide C.dual S' SingM')
    (hN : KSide D T SingN) (hN' : KSide D.dual T' SingN') (hSC : D.StronglyCausal)
    (hcvN : D.CausallyConvexIn (V : Set N) ⊤) (hc : Corresponds (U : Set M) ψ p q) (ha : a < 0)
    (hγ : C.TimelikeCurveIn U γ a 0) (hlim : Tendsto γ (𝓝[<] 0) (𝓝 p)) :
    Tendsto (ψ ∘ γ) (𝓝[<] 0) (𝓝 q) := by
  rcases hγ with hf | hpast
  · exact h.tendsto_comp_of_chronalCurveOn_kSide hM hN hSC hcvN hc ha hf hlim
  · exact h.dual.tendsto_comp_of_chronalCurveOn_kSide hM' hN'
      (Causality.dual_stronglyCausal.2 hSC) (Causality.dual_causallyConvexIn.2 hcvN) hc ha hpast
      hlim

/-- `sbierski_prop_3_7_i_imp_ii`, strong causality from global hyperbolicity and the tarentin
property (`GloballyHyperbolic.stronglyCausal`, Hausdorff). -/
theorem sbierski_prop_3_7_i_imp_ii_of_globallyHyperbolic [T2Space N]
    (h : IsCorrPair C D U V ψ g) {S S' SingM SingM' : Set M} {T T' SingN SingN' : Set N}
    (hM : KSide C S SingM) (hM' : KSide C.dual S' SingM') (hN : KSide D T SingN)
    (hN' : KSide D.dual T' SingN') (hGH : D.GloballyHyperbolic) (hT : D.Tarentin)
    (hcvN : D.CausallyConvexIn (V : Set N) ⊤) (hc : Corresponds (U : Set M) ψ p q) (ha : a < 0)
    (hγ : C.TimelikeCurveIn U γ a 0) (hlim : Tendsto γ (𝓝[<] 0) (𝓝 p)) :
    Tendsto (ψ ∘ γ) (𝓝[<] 0) (𝓝 q) :=
  sbierski_prop_3_7_i_imp_ii h hM hM' hN hN' (hGH.stronglyCausal hT) hcvN hc ha hγ hlim

/-- (i) ⇒ (ii) for a future chronal curve, **from ladder properties only**: closed `J⁺` from
GH and tarentin (`GloballyHyperbolic.isClosed_Jplus_singleton`), strong causality from GH, and
`q ∈ Z⁻` from causal arc-connectedness of `N` (`CausallyArcConnected.mem_Zminus_iff`), since
`ψ(γ s) ≪ q`. -/
theorem IsCorrPair.tendsto_comp_of_chronalCurveOn_ladder [T2Space M] [T2Space N]
    (h : IsCorrPair C D U V ψ g) (hPC : C.PushUp) (hGC : C.GloballyHyperbolic)
    (hTC : C.Tarentin) (hPD : D.PushUp) (hGD : D.GloballyHyperbolic) (hTD : D.Tarentin)
    (hacD : D.CausallyArcConnected) (hcvN : D.CausallyConvexIn (V : Set N) ⊤)
    (hc : Corresponds (U : Set M) ψ p q) (hab : a < b)
    (hγ : ∀ s ∈ Ioo a b, ∀ s' ∈ Ioo a b, C.ChronalCurveOn U γ s s')
    (hlim : Tendsto γ (𝓝[<] b) (𝓝 p)) : Tendsto (ψ ∘ γ) (𝓝[<] b) (𝓝 q) := by
  have hJC : ∀ x ∈ U, IsClosed (C.Jplus ⊤ {x}) := fun x _ => hGC.isClosed_Jplus_singleton hTC x
  have hJD : ∀ y ∈ V, IsClosed (D.Jplus ⊤ {y}) := fun y _ => hGD.isClosed_Jplus_singleton hTD y
  have hs₀ : (a + b) / 2 ∈ Ioo a b := ⟨by linarith, by linarith⟩
  have hlt := h.lt_of_tendsto_of_chain hPC hJC hPD hJD hc
    (fun s hs => (hγ s hs s hs).mem s ⟨le_rfl, le_rfl⟩)
    (fun s hs s' hs' hss' => C.lt_mono le_top ((hγ s hs s' hs').lt_of_lt le_rfl hss' le_rfl))
    hlim hs₀
  have hZ : q ∈ D.Zminus := hacD.mem_Zminus_iff.2 ⟨_, by simpa using hlt⟩
  exact h.tendsto_comp_of_chronalCurveOn hPC hJC hPD hJD (hGD.stronglyCausal hTD) hcvN hZ hc hab
    hγ hlim

/-- **Sbierski Prop 3.7 (i) ⇒ (ii) from ladder properties only** (the target's "open `I`, closed
`≤` and strong causality"): push-up, GH and tarentin on both spacetimes (Hausdorff), `N` causally
arc-connected, `V` causally convex; both time orientations, no `KSide`. -/
theorem sbierski_prop_3_7_i_imp_ii_ladder [T2Space M] [T2Space N] (h : IsCorrPair C D U V ψ g)
    (hPC : C.PushUp) (hGC : C.GloballyHyperbolic) (hTC : C.Tarentin) (hPD : D.PushUp)
    (hGD : D.GloballyHyperbolic) (hTD : D.Tarentin) (hacD : D.CausallyArcConnected)
    (hcvN : D.CausallyConvexIn (V : Set N) ⊤) (hc : Corresponds (U : Set M) ψ p q) (ha : a < 0)
    (hγ : C.TimelikeCurveIn U γ a 0) (hlim : Tendsto γ (𝓝[<] 0) (𝓝 p)) :
    Tendsto (ψ ∘ γ) (𝓝[<] 0) (𝓝 q) := by
  rcases hγ with hf | hpast
  · exact h.tendsto_comp_of_chronalCurveOn_ladder hPC hGC hTC hPD hGD hTD hacD hcvN hc ha hf hlim
  · exact h.dual.tendsto_comp_of_chronalCurveOn_ladder (Causality.dual_pushUp.2 hPC)
      (Causality.dual_globallyHyperbolic.2 hGC) (Causality.dual_tarentin.2 hTC)
      (Causality.dual_pushUp.2 hPD) (Causality.dual_globallyHyperbolic.2 hGD)
      (Causality.dual_tarentin.2 hTD) (Causality.dual_causallyArcConnectedOn.2 hacD)
      (Causality.dual_causallyConvexIn.2 hcvN) hc ha hpast hlim

/-- **A timelike curve of `U` ending at `p`**, at a regular point `p ∈ ∂U ∩ J⁺(S)`: `J⁺(S)` is a
neighbourhood of `p` (`KSide.separates`), `p ∈ Z⁻`, so some `x ∈ I⁻(p) ∩ J⁺(S)` lies in `U`, and
causal arc-connectedness joins it to `p`. -/
theorem KSide.exists_timelikeCurveIn_tendsto {S SingM : Set M} (hM : KSide C S SingM)
    (hac : C.CausallyArcConnected) (hcvM : C.CausallyConvexIn (U : Set M) ⊤) (hSU : S ⊆ U)
    (hp : p ∈ frontier (U : Set M)) (hpS : p ∈ C.Jplus ⊤ S) (hreg : p ∉ SingM) :
    ∃ γ : ℝ → M, C.TimelikeCurveIn U γ (-1) 0 ∧ Tendsto γ (𝓝[<] 0) (𝓝 p) := by
  have hpU : p ∉ (U : Set M) := by rw [U.isOpen.frontier_eq] at hp; exact hp.2
  have hJS : C.Jplus ⊤ S ∈ 𝓝 p := hM.separates p ⟨hpS, fun hm => hpU (hSU hm)⟩
  obtain ⟨x, hxI, σ, hσ, hσx⟩ := hM.mem_Zminus p hreg _ hJS
  have hxp : C.lt ⊤ x p := by simpa using hxI
  have hxU : x ∈ U := Causality.mem_of_le_of_lt_of_mem_closure hcvM (hSU hσ) hσx hxp
    (frontier_subset_closure hp)
  obtain ⟨γ, hγ, hlim⟩ :=
    Causality.exists_chronalCurve_tendsto hac hcvM hxU hxp (frontier_subset_closure hp)
  exact ⟨γ, Or.inl hγ, hlim⟩

/-- **Sbierski Prop 3.7, future side** (`:546–551`): at a regular point `p ∈ ∂U ∩ J⁺(S)`, under
causal arc-connectedness of `M`, (i) ⟺ (ii) ⟺ (iii). (i) ⇒ (ii) is
`IsCorrPair.tendsto_comp_of_kSide`; (ii) ⇒ (iii) is `KSide.exists_timelikeCurveIn_tendsto`;
(iii) ⇒ (i) is `corresponds_of_tendsto`. -/
theorem sbierski_prop_3_7_future (h : IsCorrPair C D U V ψ g) {S SingM : Set M}
    {T SingN : Set N} (hM : KSide C S SingM) (hN : KSide D T SingN) (hSC : D.StronglyCausal)
    (hac : C.CausallyArcConnected) (hcvM : C.CausallyConvexIn (U : Set M) ⊤)
    (hcvN : D.CausallyConvexIn (V : Set N) ⊤) (hSU : S ⊆ U) (hp : p ∈ frontier (U : Set M))
    (hpS : p ∈ C.Jplus ⊤ S) (hreg : p ∉ SingM) :
    List.TFAE [Corresponds (U : Set M) ψ p q,
      ∀ (γ : ℝ → M) (a : ℝ), a < 0 → C.TimelikeCurveIn U γ a 0 → Tendsto γ (𝓝[<] 0) (𝓝 p) →
        Tendsto (ψ ∘ γ) (𝓝[<] 0) (𝓝 q),
      ∃ (γ : ℝ → M) (a : ℝ), a < 0 ∧ C.TimelikeCurveIn U γ a 0 ∧ Tendsto γ (𝓝[<] 0) (𝓝 p) ∧
        Tendsto (ψ ∘ γ) (𝓝[<] 0) (𝓝 q)] := by
  tfae_have 1 → 2 := fun hc γ a ha hγ hlim =>
    h.tendsto_comp_of_kSide hM hN hSC hcvM hcvN hSU hp hpS hc ha hγ hlim
  tfae_have 2 → 3 := by
    intro hii
    obtain ⟨γ, hγ, hlim⟩ := hM.exists_timelikeCurveIn_tendsto hac hcvM hSU hp hpS hreg
    exact ⟨γ, -1, by norm_num, hγ, hlim, hii γ (-1) (by norm_num) hγ hlim⟩
  tfae_have 3 → 1 := by
    rintro ⟨γ, a, ha, hγ, hlim, hψ⟩
    refine corresponds_of_tendsto (tendsto_nhdsWithin_iff.2 ⟨hlim, ?_⟩) hψ
    filter_upwards [Ioo_mem_nhdsLT ha] with s hs using hγ.mem hs
  tfae_finish

/-- **Sbierski Prop 3.7, past side**: `sbierski_prop_3_7_future` for `C.dual`, `D.dual`. -/
theorem sbierski_prop_3_7_past (h : IsCorrPair C D U V ψ g) {S SingM : Set M} {T SingN : Set N}
    (hM : KSide C.dual S SingM) (hN : KSide D.dual T SingN) (hSC : D.StronglyCausal)
    (hac : C.CausallyArcConnected) (hcvM : C.CausallyConvexIn (U : Set M) ⊤)
    (hcvN : D.CausallyConvexIn (V : Set N) ⊤) (hSU : S ⊆ U) (hp : p ∈ frontier (U : Set M))
    (hpS : p ∈ C.Jminus ⊤ S) (hreg : p ∉ SingM) :
    List.TFAE [Corresponds (U : Set M) ψ p q,
      ∀ (γ : ℝ → M) (a : ℝ), a < 0 → C.TimelikeCurveIn U γ a 0 → Tendsto γ (𝓝[<] 0) (𝓝 p) →
        Tendsto (ψ ∘ γ) (𝓝[<] 0) (𝓝 q),
      ∃ (γ : ℝ → M) (a : ℝ), a < 0 ∧ C.TimelikeCurveIn U γ a 0 ∧ Tendsto γ (𝓝[<] 0) (𝓝 p) ∧
        Tendsto (ψ ∘ γ) (𝓝[<] 0) (𝓝 q)] := by
  simpa only [Causality.dual_timelikeCurveIn] using
    sbierski_prop_3_7_future h.dual hM hN (Causality.dual_stronglyCausal.2 hSC)
      (Causality.dual_causallyArcConnectedOn.2 hac) (Causality.dual_causallyConvexIn.2 hcvM)
      (Causality.dual_causallyConvexIn.2 hcvN) hSU hp hpS hreg

/-- **Sbierski Prop 3.7** (`Maximal_GHD2.tex:544–551`), model-free: for `p ∈ ∂U` on either side
of `S` (`M = J⁺(S) ∪ J⁻(S)` for a Cauchy surface), regular, with the `K`-calculus of both time
directions and `M` causally arc-connected, (i) ⟺ (ii) ⟺ (iii). -/
theorem sbierski_prop_3_7 (h : IsCorrPair C D U V ψ g) {S SingM SingM' : Set M}
    {T T' SingN SingN' : Set N} (hM : KSide C S SingM) (hM' : KSide C.dual S SingM')
    (hN : KSide D T SingN) (hN' : KSide D.dual T' SingN') (hSC : D.StronglyCausal)
    (hac : C.CausallyArcConnected) (hcvM : C.CausallyConvexIn (U : Set M) ⊤)
    (hcvN : D.CausallyConvexIn (V : Set N) ⊤) (hSU : S ⊆ U) (hp : p ∈ frontier (U : Set M))
    (hpS : p ∈ C.Jplus ⊤ S ∪ C.Jminus ⊤ S) (hreg : p ∉ SingM) (hreg' : p ∉ SingM') :
    List.TFAE [Corresponds (U : Set M) ψ p q,
      ∀ (γ : ℝ → M) (a : ℝ), a < 0 → C.TimelikeCurveIn U γ a 0 → Tendsto γ (𝓝[<] 0) (𝓝 p) →
        Tendsto (ψ ∘ γ) (𝓝[<] 0) (𝓝 q),
      ∃ (γ : ℝ → M) (a : ℝ), a < 0 ∧ C.TimelikeCurveIn U γ a 0 ∧ Tendsto γ (𝓝[<] 0) (𝓝 p) ∧
        Tendsto (ψ ∘ γ) (𝓝[<] 0) (𝓝 q)] := by
  rcases hpS with hpS | hpS
  · exact sbierski_prop_3_7_future h hM hN hSC hac hcvM hcvN hSU hp hpS hreg
  · exact sbierski_prop_3_7_past h hM' hN' hSC hac hcvM hcvN hSU hp hpS hreg'

/-- "It follows from ii) and iii) that `p` has at most one corresponding boundary point",
given one timelike curve of `U` ending at `p` (`N` Hausdorff; no condition on `q`, `q'`). -/
theorem eq_of_corresponds_of_timelikeCurveIn [T2Space N] (h : IsCorrPair C D U V ψ g)
    {S S' SingM SingM' : Set M} {T T' SingN SingN' : Set N} (hM : KSide C S SingM)
    (hM' : KSide C.dual S' SingM') (hN : KSide D T SingN) (hN' : KSide D.dual T' SingN')
    (hSC : D.StronglyCausal) (hcvN : D.CausallyConvexIn (V : Set N) ⊤) {q' : N} (ha : a < 0)
    (hγ : C.TimelikeCurveIn U γ a 0) (hlim : Tendsto γ (𝓝[<] 0) (𝓝 p))
    (hc : Corresponds (U : Set M) ψ p q) (hc' : Corresponds (U : Set M) ψ p q') : q = q' :=
  tendsto_nhds_unique (sbierski_prop_3_7_i_imp_ii h hM hM' hN hN' hSC hcvN hc ha hγ hlim)
    (sbierski_prop_3_7_i_imp_ii h hM hM' hN hN' hSC hcvN hc' ha hγ hlim)

/-- **Sbierski Prop 3.7, "in particular"** (`:553`): under the hypotheses of `sbierski_prop_3_7`,
`p` has at most one corresponding point (`N` Hausdorff; `q`, `q'` anywhere). -/
theorem sbierski_prop_3_7_unique [T2Space N] (h : IsCorrPair C D U V ψ g)
    {S SingM SingM' : Set M} {T T' SingN SingN' : Set N} (hM : KSide C S SingM)
    (hM' : KSide C.dual S SingM') (hN : KSide D T SingN) (hN' : KSide D.dual T' SingN')
    (hSC : D.StronglyCausal) (hac : C.CausallyArcConnected)
    (hcvM : C.CausallyConvexIn (U : Set M) ⊤) (hcvN : D.CausallyConvexIn (V : Set N) ⊤)
    (hSU : S ⊆ U) (hp : p ∈ frontier (U : Set M)) (hpS : p ∈ C.Jplus ⊤ S ∪ C.Jminus ⊤ S)
    (hreg : p ∉ SingM) (hreg' : p ∉ SingM') {q' : N} (hc : Corresponds (U : Set M) ψ p q)
    (hc' : Corresponds (U : Set M) ψ p q') : q = q' := by
  obtain ⟨γ, a, ha, hγ, hlim, -⟩ :=
    ((sbierski_prop_3_7 h hM hM' hN hN' hSC hac hcvM hcvN hSU hp hpS hreg hreg').out 0 2).1 hc
  exact eq_of_corresponds_of_timelikeCurveIn h hM hM' hN hN' hSC hcvN ha hγ hlim hc hc'

/-! ### Witnesses -/

section Witness

/-- On the timelike line, `t ↦ c + t` is a future chronal curve of every open set containing
`[c + s, c + s']`. -/
theorem timelikeLine_chronalCurveOn_add {W : Opens ℝ} {c s s' : ℝ}
    (hsub : Icc (c + s) (c + s') ⊆ (W : Set ℝ)) :
    timelikeLine.ChronalCurveOn W (fun t => c + t) s s' where
  mem t ht := hsub ⟨by linarith [ht.1], by linarith [ht.2]⟩
  rel t _ N _ htN := by
    obtain ⟨l', u', ⟨hl', hu'⟩, hsub'⟩ :=
      mem_nhds_iff_exists_Ioo_subset.1 (N.isOpen.mem_nhds htN)
    refine ⟨l' - c, u' - c, by linarith, by linarith, fun r _ r' _ h1 h2 h3 => ?_⟩
    refine ⟨by linarith, ?_⟩
    rintro z ⟨hz1, hz2⟩
    exact hsub' ⟨by linarith, by linarith⟩

/-- `I⁺(x) = ]x, ∞[` on the timelike line. -/
theorem timelikeLine_Iplus_singleton (x : ℝ) : timelikeLine.Iplus ⊤ {x} = Ioi x := by
  ext y; simp

/-- The past `K`-calculus of the timelike line, with `S = {0}` and no singular point. -/
theorem timelikeLine_kSide_past : KSide timelikeLine.dual {0} ∅ where
  pushUp := Causality.dual_pushUp.2 timelikeLine_pushUp
  causal := Causality.dual_isCausal.2 timelikeLine_isCausal
  isClosed_Jplus x := by
    show IsClosed (timelikeLine.Jminus ⊤ {x})
    rw [timelikeLine_Jminus_top_singleton]; exact isClosed_Iic
  isClosed_Jminus x := by
    show IsClosed (timelikeLine.Jplus ⊤ {x})
    rw [timelikeLine_Jplus_top_singleton]; exact isClosed_Ici
  Kminus_reg x _ := Causality.PushUp.Kminus_eq_Iminus (C := timelikeLine.dual)
    (Causality.dual_pushUp.2 timelikeLine_pushUp) (timelikeLine_mem_Zplus x)
  mem_Zminus x _ := timelikeLine_mem_Zplus x
  Kminus_sing x hx := absurd hx (notMem_empty x)
  Iminus_sing x hx := absurd hx (notMem_empty x)
  dense x := by
    rw [Causality.PushUp.Kminus_eq_Iminus (C := timelikeLine.dual)
      (Causality.dual_pushUp.2 timelikeLine_pushUp) (timelikeLine_mem_Zplus x)]
    show timelikeLine.Jplus ⊤ {x} ⊆ closure (timelikeLine.Iplus ⊤ {x})
    rw [timelikeLine_Jplus_top_singleton, timelikeLine_Iplus_singleton, closure_Ioi]
  separates y hy := by
    change y ∈ timelikeLine.Jminus ⊤ {0} \ {0} at hy
    show timelikeLine.Jminus ⊤ {0} ∈ 𝓝 y
    rw [timelikeLine_Jminus_top_singleton] at hy ⊢
    exact Iic_mem_nhds (lt_of_le_of_ne hy.1 hy.2)
  isCompact x := by
    show IsCompact (timelikeLine.Jminus ⊤ {0} ∩ timelikeLine.Jplus ⊤ {x})
    rw [timelikeLine_Jminus_top_singleton, timelikeLine_Jplus_top_singleton, Iic_inter_Ici]
    exact isCompact_Icc

/-- `s ↦ 1 + s` is a timelike curve of `]-∞, 1[` over `(-1, 0)` on the timelike line. -/
theorem timelikeLine_timelikeCurveIn :
    timelikeLine.TimelikeCurveIn iioOne (fun s => 1 + s) (-1) 0 :=
  Or.inl fun _ _ _ hs' => timelikeLine_chronalCurveOn_add fun z hz => by
    show z < 1; linarith [hz.2, hs'.2]

theorem tendsto_one_add_nhdsLT : Tendsto (fun s : ℝ => 1 + s) (𝓝[<] 0) (𝓝 1) := by
  have : Tendsto (fun s : ℝ => 1 + s) (𝓝 0) (𝓝 (1 + 0)) :=
    (continuous_const.add continuous_id).tendsto 0
  rw [add_zero] at this
  exact this.mono_left nhdsWithin_le_nhds

/-- **The hypotheses of `sbierski_prop_3_7_i_imp_ii` and `sbierski_prop_3_7` are jointly
satisfiable, with a genuine curve** (kb/0011): the timelike line, `U = V = ]-∞, 1[`,
`ψ = g = id`, `S = T = {0}`, no singular point, `p = q = 1`, `γ s = 1 + s`; the conclusion of
(i) ⇒ (ii) holds. -/
theorem timelikeLine_sbierski_prop_3_7 :
    IsCorrPair timelikeLine timelikeLine iioOne iioOne id id ∧ KSide timelikeLine {0} ∅ ∧
      KSide timelikeLine.dual {0} ∅ ∧ timelikeLine.StronglyCausal ∧
      timelikeLine.CausallyArcConnected ∧ timelikeLine.CausallyConvexIn (iioOne : Set ℝ) ⊤ ∧
      ({0} : Set ℝ) ⊆ iioOne ∧ (1 : ℝ) ∈ frontier (iioOne : Set ℝ) ∧
      (1 : ℝ) ∈ timelikeLine.Jplus ⊤ {0} ∧ Corresponds (iioOne : Set ℝ) id (1 : ℝ) 1 ∧
      timelikeLine.TimelikeCurveIn iioOne (fun s => 1 + s) (-1) 0 ∧
      Tendsto (fun s : ℝ => 1 + s) (𝓝[<] 0) (𝓝 1) ∧
      Tendsto (id ∘ fun s : ℝ => 1 + s) (𝓝[<] 0) (𝓝 1) := by
  have hfr : (1 : ℝ) ∈ frontier (iioOne : Set ℝ) := by
    show (1 : ℝ) ∈ frontier (Iio (1 : ℝ)); rw [frontier_Iio]; rfl
  have hsub : ({0} : Set ℝ) ⊆ iioOne := by
    rintro _ rfl; show (0 : ℝ) < 1; norm_num
  have h1 : (1 : ℝ) ∈ timelikeLine.Jplus ⊤ {0} := by
    rw [timelikeLine_Jplus_top_singleton]; norm_num
  refine ⟨timelikeLine_isCorrPair_id, timelikeLine_kSide, timelikeLine_kSide_past,
    timelikeLine_stronglyCausal, timelikeLine_causallyArcConnected,
    timelikeLine_causallyConvexIn_iioOne, hsub, hfr, h1, timelikeLine_corresponds_one,
    timelikeLine_timelikeCurveIn, tendsto_one_add_nhdsLT, ?_⟩
  exact sbierski_prop_3_7_i_imp_ii timelikeLine_isCorrPair_id timelikeLine_kSide
    timelikeLine_kSide_past timelikeLine_kSide timelikeLine_kSide_past timelikeLine_stronglyCausal
    timelikeLine_causallyConvexIn_iioOne timelikeLine_corresponds_one (by norm_num : (-1 : ℝ) < 0)
    timelikeLine_timelikeCurveIn tendsto_one_add_nhdsLT

/-- The hypotheses of `sbierski_prop_3_7_i_imp_ii_ladder` on the timelike line, with its
conclusion for `γ s = 1 + s` (kb/0011). -/
theorem timelikeLine_sbierski_prop_3_7_ladder :
    timelikeLine.PushUp ∧ timelikeLine.GloballyHyperbolic ∧ timelikeLine.Tarentin ∧
      timelikeLine.CausallyArcConnected ∧ Tendsto (id ∘ fun s : ℝ => 1 + s) (𝓝[<] 0) (𝓝 1) :=
  ⟨timelikeLine_pushUp, timelikeLine_globallyHyperbolic, timelikeLine_tarentin,
    timelikeLine_causallyArcConnected,
    sbierski_prop_3_7_i_imp_ii_ladder timelikeLine_isCorrPair_id timelikeLine_pushUp
      timelikeLine_globallyHyperbolic timelikeLine_tarentin timelikeLine_pushUp
      timelikeLine_globallyHyperbolic timelikeLine_tarentin timelikeLine_causallyArcConnected
      timelikeLine_causallyConvexIn_iioOne timelikeLine_corresponds_one
      (by norm_num : (-1 : ℝ) < 0) timelikeLine_timelikeCurveIn tendsto_one_add_nhdsLT⟩

/-- The lightlike line has no timelike curve over a non-empty interval (`≪ = ∅`). -/
theorem lightlikeLine_not_timelikeCurveIn {W : Opens ℝ} {γ : ℝ → ℝ} {a : ℝ} (ha : a < 0) :
    ¬ lightlikeLine.TimelikeCurveIn W γ a 0 := by
  have hs : 2 * a / 3 ∈ Ioo a 0 := ⟨by linarith, by linarith⟩
  have hs' : a / 3 ∈ Ioo a 0 := ⟨by linarith, by linarith⟩
  have hss' : 2 * a / 3 < a / 3 := by linarith
  rintro (hf | hpast)
  · exact (hf _ hs _ hs').lt_of_lt le_rfl hss' le_rfl
  · exact (hpast _ hs _ hs').lt_of_lt le_rfl hss' le_rfl

/-- **At a BTZ point (i) ⇒ (iii) fails** (the ETT setting with singular points; Sbierski's is
smooth): on the lightlike line, every point singular (`Sing = univ`), `U = V = ]-∞, 1[`,
`ψ = id`, every hypothesis of `sbierski_prop_3_7_future` holds except `p ∉ Sing`, `1`
corresponds to `1`, and no timelike curve of `U` ends at `1`. -/
theorem lightlikeLine_sbierski_prop_3_7_iii_fails :
    IsCorrPair lightlikeLine lightlikeLine iioOne iioOne id id ∧ KSide lightlikeLine {0} univ ∧
      lightlikeLine.StronglyCausal ∧ lightlikeLine.CausallyArcConnected ∧
      lightlikeLine.CausallyConvexIn (iioOne : Set ℝ) ⊤ ∧ ({0} : Set ℝ) ⊆ iioOne ∧
      (1 : ℝ) ∈ frontier (iioOne : Set ℝ) ∧ (1 : ℝ) ∈ lightlikeLine.Jplus ⊤ {0} ∧
      Corresponds (iioOne : Set ℝ) id (1 : ℝ) 1 ∧
      ¬ ∃ (γ : ℝ → ℝ) (a : ℝ), a < 0 ∧ lightlikeLine.TimelikeCurveIn iioOne γ a 0 ∧
        Tendsto γ (𝓝[<] 0) (𝓝 1) ∧ Tendsto (id ∘ γ) (𝓝[<] 0) (𝓝 1) := by
  have hfr : (1 : ℝ) ∈ frontier (iioOne : Set ℝ) := by
    show (1 : ℝ) ∈ frontier (Iio (1 : ℝ)); rw [frontier_Iio]; rfl
  have hsub : ({0} : Set ℝ) ⊆ iioOne := by
    rintro _ rfl; show (0 : ℝ) < 1; norm_num
  have h1 : (1 : ℝ) ∈ lightlikeLine.Jplus ⊤ {0} := by
    rw [lightlikeLine_Jplus_singleton]; norm_num
  refine ⟨lightlikeLine_isCorrPair_id, lightlikeLine_kSide,
    (timelikeLine_stronglyCausal : lightlikeLine.StronglyCausal),
    lightlikeLine_causallyArcConnected, lightlikeLine_causallyConvexIn_iioOne, hsub, hfr, h1,
    timelikeLine_corresponds_one, ?_⟩
  rintro ⟨γ, a, ha, hγ, -, -⟩
  exact lightlikeLine_not_timelikeCurveIn ha hγ

end Witness

end CBG

end Causal
