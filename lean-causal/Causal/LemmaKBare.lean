import CausalScaffold.CompactCauchy
import CausalScaffold.Splitting
import CausalScaffold.CurvesExtend
import Causal.Model.Massive

/-!
# Lemma K without a splitting — a compact connected locally Cauchy set is a Cauchy surface when its strict causal future and past are open

No label is marked. Lemma K is DEC-44's abstraction of a sentence Barbot asserts twice and never
proves (Rem 2.3 `clomax`, label at `GHFspace.tex:572` of the labelled file, block l.571–579, the
sentence at l.576–578; §11, l.3537–3540 and l.3578–3580); Lemma K itself carries no paper label.
Its bare form is `isCauchySurface_of_isLocallyCauchy` (`CausalScaffold.CompactCauchy`), a tagged
`sorry`. This file **settles the bare form wherever curves extend, `C` has push-up and
`Z^± = M`** (e.g. every static spacetime over a proper geodesic space), with no splitting and no
two-sidedness. It does not settle the bare form as stated: those three hypotheses are not among
its hypotheses, and no counterexample was found (SCOPE). Barbot's `𝐌ⁿ` is the library's
`Minkowski d`, `n = d + 1` (it enters only through the static corollary).

> Cauchy-compact GH spacetimes are automatically absolutely maximal. Indeed, any spacelike
> hypersurface in a given CGH spacetime is a Cauchy hypersurface. (Rem 2.3, l.576–578)

False as written (a small spacelike disc; OQ-22, `docs/BARBOT-THEOREMS.md` §4); DEC-44's
corrected form takes `Σ` compact and connected, which is Lemma K.

> A fundamental observation is that in a GH spacetime, every closed spacelike hypersurface is
> necessarely a Cauchy surface (§11, l.3537–3539)

## What is proved

* **The core** (`isCauchySurface_of_isLocallyCauchy_of_isOpen_strictJplus`): the exact
  hypotheses of the bare form, plus `CurvesExtend`, plus the openness of the **strict causal
  future** `{x | ∃ z ∈ Σ, z ≤ x, x ≠ z}` of `Σ` and of its strict past (`strictJplus`, for `C`
  and `C.dual`). No global projection, no two-sidedness. **It subsumes `CompactCauchy`'s proved
  form**: a splitting plus two-sidedness give both openness hypotheses
  (`isOpen_strictJplus_of_isCauchySplitting`, through `CompactCauchy`'s graph step), and the
  proved form is re-derived through the core (`isCauchySurface_of_isCauchySplitting_via_strictJplus`).
* **The chronal form** (`isCauchySurface_of_isLocallyCauchy_of_chronal`): push-up and every
  point strongly tarentin in the future and in the past (`Z^± = M`) give both openness
  conditions. Instances: **every static spacetime `ℝ × X` over a proper geodesic space**
  (`staticCausality.isCauchySurface_of_compact_isLocallyCauchy`; connectedness of `X` is derived,
  `preconnectedSpace_of_geodesic`), hence Minkowski space and the massive-particle models `E_α`,
  `α > 0` (`massive_isCauchySurface_of_compact_isLocallyCauchy`), and mathematically the flat
  `ℝ × torus` — no torus instance is built here. Over any geodesic `X` the **bare statement
  holds verbatim** for `C = staticCausality X` (`staticCausality.isCauchySurface_of_isLocallyCauchy_bare`):
  global hyperbolicity of `ℝ × X` forces `X` proper (`properSpace_of_globallyHyperbolic`).
* **Two-sided, no splitting** (`isCauchySurface_of_isLocallyCauchyTwoSided_of_isOpen_Jplus`): the
  proved form of `CompactCauchy` with its splitting replaced by "the causal future and past of an
  open set are open" (implied by push-up and `Z^∓ = M`, `isOpen_Jplus_of_pushUp`).
* **The gx shape** (`isCauchySurface_of_isLocallyCauchyTwoSided_of_pushUp`): the past side from
  push-up and `Z^+ = M` (both fields of `SingularFlatAxioms`, true at BTZ points), the future side
  from two-sidedness and "the causal future of an open set is open".

The chronal, two-sided-open and gx forms are **alternatives, incomparable with `CompactCauchy`'s
proved form** (neither hypothesis set implies the other); only the core subsumes it.

The proof: (1) `Σ` is acausal — the set `A` of points of `Σ` in the strict future of `Σ` is open
in `Σ` (hypothesis), closed in `Σ` (the closed relation of a GH spacetime minus an open
neighbourhood of the diagonal on which `Σ` is locally acausal, projected from the compact
`Σ × Σ`), and misses a `≤`-minimal point of `Σ` (Zorn, the diamonds `Σ ∩ J^-(w)` being compact),
so `A = ∅` as `Σ` is connected. (2) `J^+(Σ) ∪ J^-(Σ)` is closed (GH), open (the charts at `Σ`,
the strict sides off `Σ`), hence `M`. (3) an inextensible curve leaves `J^-(Σ)` and `J^+(Σ)`
(`CompactCauchy`), so by connectedness of a segment it meets `J^+(Σ) ∩ J^-(Σ) = Σ`.

## Hypothesis checklist

| DEC-44 hypothesis | here |
|---|---|
| `C` a causality on `M`, `M` connected | ✓ carried |
| `T2Space`, `Tarentin`, `CausallyArcConnected`, `J^±(p) ≠ {p}` (those of the bare form) | ✓ carried |
| `C.GloballyHyperbolic` | ✓ carried |
| `Σ` compact, connected, `IsLocallyCauchy` | ✓ carried — no two-sidedness in the core |
| — | ⚠ strengthened, named (kb/0012): `C.CurvesExtend` (as in `CompactCauchy`'s proved form) |
| — | ⚠ strengthened: the strict future and past of `Σ` open — or, sufficient: `PushUp` and `Z^± = M`; or two-sidedness and causal openness of `J^±(V)`, `V` open; or a splitting and two-sidedness |
| a splitting `IsCauchySplitting` (the proved form's datum) | ⚠ weakened: **not used** by the core, which subsumes the proved form; the other three forms are incomparable with it |

## SCOPE (disclosed)

* **The bare form is settled where `CurvesExtend`, `PushUp` and `Z^± = M` all hold**, and open
  when any of them fails (none is a hypothesis of the bare form). For gx the case at hand is the
  BTZ point: `Z^-` fails there (`SingularFlatAxioms.mem_Zminus_iff`), `J^+(Σ) ∖ Σ ≠ I^+(Σ)` on a lightlike
  line (`lightlikeLine_Jplus_diff_ne_Iplus`, `CausalScaffold.Splitting`), and the future-side
  openness must come from the model: two-sidedness in the charts plus "`J^+(V)` open for `V`
  open" (`isCauchySurface_of_isLocallyCauchyTwoSided_of_pushUp`). No counterexample to the bare
  form was found: one must break at least one of `CurvesExtend`, `PushUp`, `Z^+ = M`,
  `Z^- = M`, so none exists among static spacetimes (the static corollaries); and a fold of `Σ`
  around a cylinder (`Σ` meeting a line twice) is excluded by step (1) — acausality from
  connectedness, given the openness hypothesis — with no projection to compare `Σ` with.
* **Local non-static candidates examined (none is a counterexample; arguments not formalised
  unless named).** The one-dimensional causalities — `timelikeLine`, `lightlikeLine` (push-up
  vacuous, `Z^± = ∅`, the library's only `BTZAxioms` instance, `lightlikeLine_btzAxioms`),
  `halfChronoLine` (`Z^-` fails at every `p ≤ -1`): a compact connected locally Cauchy
  `Σ ⊆ ℝ` is an interval meeting the inextensible curve of a chart once, hence a point, and a
  point is a Cauchy surface (`timelikeLine_isCauchySurface_singleton`,
  `lightlikeLine_isCauchySurface_zero`). `spacelikeLine` violates `J^±(p) ≠ {p}`;
  `orderLine` and `timelikeLineTop` are not local (kb/0014; the latter is not even causal). `puncturedPlane` has push-up and `Z^± = M`
  but is not GH (a diamond around the puncture is not compact). The massive models `E_α` are
  static (proved above). **Not tried**: gluings (`Causal/Pushout*.lean`) and any
  `E_{≥0}`-manifold with a BTZ line and a compact Cauchy surface — none is constructed in the
  importable library (`E_0` is not built, `Causal.Model.Massive`). A counterexample must
  therefore live in dimension ≥ 2 and break `CurvesExtend`, push-up, `Z^+ = M` or `Z^- = M`;
  the BTZ case (`Z^-` fails) is where gx would meet it.
* `CurvesExtend` stays a named hypothesis (kb/0012), discharged on static spacetimes
  (`staticCausality.curvesExtend`) and under Geroch's hypotheses
  (`GloballyHyperbolic.curvesExtend`). It is not a field of `SingularFlatAxioms`, so gx owes it
  in every form here.
* For the regular flat quotients `Γ\Ω` of Rem 2.3 and §11 the chronal form is mathematically
  sufficient (smooth Lorentzian: push-up, `Z^± = M`, Geroch curve extension), but not yet
  discharged in the library: no `PushUp`, `Z^±` or `CurvesExtend` instance exists for them; it is
  owed by the Theorem B consumer.
* Non-vacuity: the timelike line with `Σ = {0}` satisfies the hypotheses of the chronal form
  (`timelikeLine_lemmaKBare_hypotheses`) and jointly those of the two-sided and gx forms
  (`timelikeLine_lemmaKBare_twoSided_hypotheses`); each form is applied there.
* gx contract (a)–(f): not applicable; no length, metric or Lipschitz graph is defined here.
* Not imported by the scaffold root `CausalScaffold.lean` (outside this package's write scope).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Filter Function

universe u

variable {M : Type u} [TopologicalSpace M]

namespace Causality

variable (C : Causality M)

/-- The **strict causal future** of `S`: the points `x` with `z ≤ x` for some `z ∈ S`, `x ≠ z`.
For `C.dual` it is the strict causal past. -/
def strictJplus (S : Set M) : Set M := {x | ∃ z ∈ S, C.le ⊤ z x ∧ x ≠ z}

variable {C}

/-! ### Duality -/

/-- `CurvesExtend` for the reversed causality. -/
theorem CurvesExtend.dual (h : C.CurvesExtend) : C.dual.CurvesExtend := by
  intro c a b hab hc
  have hc' : C.CausalCurveOn ⊤ (fun t => c (-t)) (-b) (-a) :=
    CurveOn.neg (r := C.dual.le) (W := ⊤) (c := c) (a := -b) (b := -a)
      (by rw [neg_neg, neg_neg]; exact hc)
  obtain ⟨I, c', hc'i, hsub⟩ := h _ (-b) (-a) (neg_le_neg hab) hc'
  refine ⟨-I, fun t => c' (-t), hc'i.dual_reverse, ?_⟩
  rintro _ ⟨t, ht, rfl⟩
  obtain ⟨u, hu, hcu⟩ := hsub ⟨-t, ⟨neg_le_neg ht.2, neg_le_neg ht.1⟩, rfl⟩
  exact ⟨-u, by simpa using hu, by simpa using hcu⟩

theorem IsLocallyCauchy.dual {S : Set M} (h : C.IsLocallyCauchy S) : C.dual.IsLocallyCauchy S :=
  fun x hx => by
    obtain ⟨U, hxU, hU, hSU⟩ := h x hx
    exact ⟨U, hxU, dual_causallyConvexIn.2 hU, dual_isCauchySurfaceOn.2 hSU⟩

theorem IsLocallyCauchyTwoSided.dual {S : Set M} (h : C.IsLocallyCauchyTwoSided S) :
    C.dual.IsLocallyCauchyTwoSided S := fun x hx => by
  obtain ⟨U, hxU, hU, hSU, hp, hm⟩ := h x hx
  exact ⟨U, hxU, dual_causallyConvexIn.2 hU, dual_isCauchySurfaceOn.2 hSU, hm, hp⟩

/-! ### Leaving a point along a causal curve, inside an open set -/

/-- On a causal curve from `z` to `x ≠ z`, there is a point `y ≠ z` as close to `z` as wished:
`y ∈ U`, `z ≤ y ≤ x`. -/
theorem exists_le_le_mem_ne_of_le [T1Space M] (hC : C.CausallyArcConnected) {U : Set M}
    (hU : IsOpen U) {z x : M} (hz : z ∈ U) (hzx : C.le ⊤ z x) (hne : x ≠ z) :
    ∃ y ∈ U, y ≠ z ∧ C.le ⊤ z y ∧ C.le ⊤ y x := by
  obtain ⟨γ, hγ, hγ0, hγ1⟩ := (hC ⊤ le_rfl z x).1.1 hzx
  have hcont : ContinuousOn γ (Icc 0 1) := hγ.continuousOn C.isRelFamily_le
  set T0 : Set ℝ := Icc (0 : ℝ) 1 ∩ γ ⁻¹' {z} with hT0
  have hT0c : IsClosed T0 := hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have h0 : (0 : ℝ) ∈ T0 := ⟨⟨le_rfl, zero_le_one⟩, by simp [hγ0]⟩
  have hbdd : BddAbove T0 := ⟨1, fun t ht => ht.1.2⟩
  set t1 := sSup T0 with ht1def
  have ht1 : t1 ∈ T0 := hT0c.csSup_mem ⟨0, h0⟩ hbdd
  have hγt1 : γ t1 = z := ht1.2
  have ht1lt : t1 < 1 := lt_of_le_of_ne ht1.1.2 fun h => hne (by rw [← hγ1, ← h, hγt1])
  have hU1 : γ t1 ∈ U := by rw [hγt1]; exact hz
  obtain ⟨O, hO, ht1O, hOsub⟩ :=
    mem_nhdsWithin.1 ((hcont t1 ht1.1).preimage_mem_nhdsWithin (hU.mem_nhds hU1))
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hO t1 ht1O
  have hm : 0 < min ε (1 - t1) := lt_min hε (sub_pos.2 ht1lt)
  have hm1 := min_le_left ε (1 - t1)
  have hm2 := min_le_right ε (1 - t1)
  set t := t1 + min ε (1 - t1) / 2 with htdef
  have htt1 : t1 < t := by linarith
  have htI : t ∈ Icc (0 : ℝ) 1 := ⟨by linarith [ht1.1.1], by linarith⟩
  have htO : t ∈ O := hball (by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith)
  refine ⟨γ t, hOsub ⟨htO, htI⟩, fun h => ?_, ?_, ?_⟩
  · have : t ≤ t1 := le_csSup hbdd ⟨htI, h⟩
    linarith
  · rw [← hγ0]; exact hγ.le_of_le le_rfl htI.1 htI.2
  · rw [← hγ1]; exact hγ.le_of_le htI.1 htI.2 le_rfl

/-! ### The chronal side: `Z^- = M` and push-up -/

/-- **In a chart, a point just above `Σ` is in the chronological future of `Σ`.** Let `U` be a
causally convex open set in which `S ∩ U` is Cauchy, `z ∈ S ∩ U`, `y ∈ U ∖ S`, `z ≤ y`. If `y` is
strongly tarentin in the past and `C` has push-up, then `σ ≪ y` for some `σ ∈ S`: a chronal curve
into `y` from a point of a causally convex neighbourhood of `y` missing `S`, extended to an
inextensible curve of `U`, meets `S` before that point. -/
theorem exists_lt_of_le_of_isCauchySurfaceOn [T2Space M] (hT : C.Tarentin)
    (hG : C.GloballyHyperbolic) (hC : C.CausallyArcConnected) (hext : C.CurvesExtend)
    (hpush : C.PushUp) {U : Opens M} (hU : C.CausallyConvexIn (U : Set M) ⊤) {S : Set M}
    (hSc : IsClosed S) (hSU : C.IsCauchySurfaceOn U (S ∩ U)) {z y : M} (hz : z ∈ S ∩ U)
    (hy : y ∈ U) (hyS : y ∉ S) (hyZ : y ∈ C.Zminus) (hzy : C.le ⊤ z y) :
    ∃ σ ∈ S, C.lt ⊤ σ y := by
  have hcaus := hG.1
  have hN : (U : Set M) ∩ Sᶜ ∈ 𝓝 y :=
    inter_mem (U.isOpen.mem_nhds hy) (hSc.isOpen_compl.mem_nhds hyS)
  obtain ⟨V, hV, hVN, hVc⟩ := hG.stronglyCausal hT y _ hN
  obtain ⟨p, ⟨y', hy', hpy⟩, hpV⟩ := hyZ V hV
  rw [mem_singleton_iff] at hy'
  subst hy'
  obtain ⟨γ, hγ, hγ0, hγ1⟩ := (hC ⊤ le_rfl p y').1.1 (C.le_of_lt hpy)
  obtain ⟨I, c, hc, hsub⟩ := hext γ 0 1 zero_le_one hγ
  obtain ⟨tp, htp, hctp⟩ : p ∈ c '' I := hsub ⟨0, ⟨le_rfl, zero_le_one⟩, hγ0⟩
  obtain ⟨ty, hty, hcty⟩ : y' ∈ c '' I := hsub ⟨1, ⟨zero_le_one, le_rfl⟩, hγ1⟩
  have hUy : c ty ∈ U := by rw [hcty]; exact hy
  have hJ := inextensible_ordConnectedComponent hcaus hc hty hUy
  obtain ⟨_, ⟨⟨t, htJ, rfl⟩, hS⟩, -⟩ := hSU _ c hJ
  have htI : t ∈ I := (ordConnectedComponent_subset htJ).1
  rcases le_total ty t with h | h
  · exfalso
    have hyt : C.le ⊤ y' (c t) := by rw [← hcty]; exact hc.1.le_of_le hty htI h
    have he := eq_of_le_of_isCauchySurfaceOn hcaus hC hext hU hSU hz hS (C.le_trans hzy hyt)
    rw [← he] at hyt
    exact hyS (hcaus hyt hzy ▸ hz.1)
  · rcases le_total t tp with h' | h'
    · refine ⟨c t, hS.1, ?_⟩
      have hle : C.le ⊤ (c t) p := by rw [← hctp]; exact hc.1.le_of_le htI htp h'
      exact hpush.lt_of_le_of_lt hle hpy
    · exfalso
      have h1 : C.le ⊤ p (c t) := by rw [← hctp]; exact hc.1.le_of_le htp htI h'
      have h2 : C.le ⊤ (c t) y' := by rw [← hcty]; exact hc.1.le_of_le htI hty h
      have hmem : c t ∈ V := hVc.2 p hpV y' (mem_of_mem_nhds hV) (mem_diamond.2 ⟨h1, h2⟩)
      exact (hVN hmem).2 hS.1

/-- **Globally**: if `z ∈ Σ`, `z ≤ x` and `x ≠ z`, then `σ ≪ x` for some `σ ∈ Σ` — through a
point of the curve from `z` to `x` just above `z`, and push-up. -/
theorem exists_lt_of_le_of_ne_of_isLocallyCauchy [T2Space M] (hT : C.Tarentin)
    (hG : C.GloballyHyperbolic) (hC : C.CausallyArcConnected) (hext : C.CurvesExtend)
    (hpush : C.PushUp) (hZm : ∀ p : M, p ∈ C.Zminus) {S : Set M} (hSc : IsClosed S)
    (hloc : C.IsLocallyCauchy S) {z x : M} (hz : z ∈ S) (hzx : C.le ⊤ z x) (hne : x ≠ z) :
    ∃ σ ∈ S, C.lt ⊤ σ x := by
  obtain ⟨U, hzU, hU, hSU⟩ := hloc z hz
  obtain ⟨y, hyU, hyz, hzy, hyx⟩ := exists_le_le_mem_ne_of_le hC U.isOpen hzU hzx hne
  have hyS : y ∉ S := fun h =>
    hyz (eq_of_le_of_isCauchySurfaceOn hG.1 hC hext hU hSU ⟨hz, hzU⟩ ⟨h, hyU⟩ hzy).symm
  obtain ⟨σ, hσ, hσy⟩ := exists_lt_of_le_of_isCauchySurfaceOn hT hG hC hext hpush hU hSc hSU
    ⟨hz, hzU⟩ hyU hyS (hZm y) hzy
  exact ⟨σ, hσ, hpush.lt_of_lt_of_le hσy hyx⟩

/-- **The strict causal future of a locally Cauchy closed set is open** when `Z^- = M` and `C`
has push-up. -/
theorem isOpen_strictJplus_of_Zminus [T2Space M] (hT : C.Tarentin) (hG : C.GloballyHyperbolic)
    (hC : C.CausallyArcConnected) (hJm : ∀ p : M, C.Jminus ⊤ {p} ≠ {p}) (hext : C.CurvesExtend)
    (hpush : C.PushUp) (hZm : ∀ p : M, p ∈ C.Zminus) {S : Set M} (hSc : IsClosed S)
    (hloc : C.IsLocallyCauchy S) : IsOpen (C.strictJplus S) := by
  rw [isOpen_iff_mem_nhds]
  rintro x ⟨z, hz, hzx, hne⟩
  obtain ⟨σ, hσ, hσx⟩ :=
    exists_lt_of_le_of_ne_of_isLocallyCauchy hT hG hC hext hpush hZm hSc hloc hz hzx hne
  refine mem_of_superset ((C.isOpen_lt_right ⊤ σ).mem_nhds hσx) fun w hw => ?_
  exact ⟨σ, hσ, C.le_of_lt hw, (ne_of_lt_top hC hG.1 hJm hw).symm⟩

/-- **The strict causal future is open** when `Σ` is two-sided in its charts and the causal
future of an open set is open. -/
theorem isOpen_strictJplus_of_twoSided [T2Space M] (hcaus : C.IsCausal)
    (hC : C.CausallyArcConnected) (hext : C.CurvesExtend) (hO : ∀ V : Opens M, IsOpen (C.Jplus ⊤ V))
    {S : Set M} (hloc : C.IsLocallyCauchyTwoSided S) : IsOpen (C.strictJplus S) := by
  rw [isOpen_iff_mem_nhds]
  rintro x ⟨z, hz, hzx, hne⟩
  obtain ⟨U, hzU, hU, hSU, hp, -⟩ := hloc z hz
  obtain ⟨y, hyU, hyz, hzy, hyx⟩ := exists_le_le_mem_ne_of_le hC U.isOpen hzU hzx hne
  have hyS : y ∉ S := fun h =>
    hyz (eq_of_le_of_isCauchySurfaceOn hcaus hC hext hU hSU ⟨hz, hzU⟩ ⟨h, hyU⟩ hzy).symm
  let O : Opens M := ⟨C.Jplus U (S ∩ U) \ S, hp⟩
  have hyO : y ∈ (O : Set M) :=
    ⟨⟨z, ⟨hz, hzU⟩, le_of_mem_causallyConvexIn hC hU hzU hyU hzy⟩, hyS⟩
  refine mem_of_superset ((hO O).mem_nhds ⟨y, hyO, hyx⟩) ?_
  rintro w ⟨o, ⟨⟨z', hz', hz'o⟩, hoS⟩, how⟩
  have hz'o' : C.le ⊤ z' o := C.le_mono le_top hz'o
  refine ⟨z', hz'.1, C.le_trans hz'o' how, fun h => ?_⟩
  subst h
  exact hoS (hcaus how hz'o' ▸ hz'.1)

/-- **The causal future of an open set is open** when `C` has push-up and `Z^- = M`: a point
`v ∈ V` has a chronological past point `p ∈ V`, and `I^+(p) ⊆ J^+(V)` is a neighbourhood of every
`x ≥ v`. So the extra hypotheses of the two-sided form follow from those of the chronal form. -/
theorem isOpen_Jplus_of_pushUp (hpush : C.PushUp) (hZm : ∀ p : M, p ∈ C.Zminus) (V : Opens M) :
    IsOpen (C.Jplus ⊤ V) := by
  rw [isOpen_iff_mem_nhds]
  rintro x ⟨v, hv, hvx⟩
  obtain ⟨p, ⟨v', hv', hpv⟩, hpV⟩ := hZm v V (V.isOpen.mem_nhds hv)
  rw [mem_singleton_iff] at hv'
  rw [hv'] at hpv
  exact mem_of_superset ((C.isOpen_lt_right ⊤ p).mem_nhds (hpush.lt_of_lt_of_le hpv hvx))
    fun w hw => ⟨p, hpV, C.le_of_lt hw⟩

/-! ### Step 1: acausality -/

/-- **A compact connected locally Cauchy set whose strict causal future is open is acausal.** -/
theorem isAcausal_of_isLocallyCauchy [T2Space M] (hT : C.Tarentin) (hG : C.GloballyHyperbolic)
    (hC : C.CausallyArcConnected) (hext : C.CurvesExtend) {S : Set M} (hSc : IsCompact S)
    (hSconn : IsConnected S) (hloc : C.IsLocallyCauchy S) (hQ : IsOpen (C.strictJplus S)) :
    C.IsAcausal S := by
  have hcaus := hG.1
  -- an open neighbourhood of the diagonal of `S` on which `S` is acausal
  set W : Set (M × M) := ⋃ (U : Opens M) (_ : C.CausallyConvexIn (U : Set M) ⊤ ∧
    C.IsCauchySurfaceOn U (S ∩ U)), (U : Set M) ×ˢ (U : Set M) with hWdef
  have hWo : IsOpen W := isOpen_iUnion fun U => isOpen_iUnion fun _ => U.isOpen.prod U.isOpen
  have hWdiag : ∀ z ∈ S, (z, z) ∈ W := fun z hz => by
    obtain ⟨U, hzU, hU, hSU⟩ := hloc z hz
    exact mem_iUnion₂.2 ⟨U, ⟨hU, hSU⟩, hzU, hzU⟩
  have hWac : ∀ z ∈ S, ∀ w ∈ S, C.le ⊤ z w → (z, w) ∈ W → z = w := by
    intro z hz w hw hzw hW
    obtain ⟨U, ⟨hU, hSU⟩, hzU, hwU⟩ := mem_iUnion₂.1 hW
    exact eq_of_le_of_isCauchySurfaceOn hcaus hC hext hU hSU ⟨hz, hzU⟩ ⟨hw, hwU⟩ hzw
  -- the strictly related pairs of `S`, a compact set
  set P : Set (M × M) := ((S ×ˢ S) ∩ {q | C.le ⊤ q.1 q.2}) \ W with hPdef
  have hPc : IsCompact P :=
    (hSc.prod hSc).of_isClosed_subset
      (((hSc.isClosed.prod hSc.isClosed).inter (hG.isClosed_le hT)).sdiff hWo)
      fun q hq => hq.1.1
  have hK : IsClosed (Prod.snd '' P) := (hPc.image continuous_snd).isClosed
  have hKQ : Prod.snd '' P ⊆ C.strictJplus S := by
    rintro _ ⟨⟨z, w⟩, ⟨⟨⟨hz, -⟩, hzw⟩, hW⟩, rfl⟩
    refine ⟨z, hz, hzw, fun h => hW ?_⟩
    simp only at h
    rw [h]; exact hWdiag z hz
  have hQK : S ∩ C.strictJplus S ⊆ Prod.snd '' P := by
    rintro w ⟨hw, z, hz, hzw, hne⟩
    exact ⟨(z, w), ⟨⟨⟨hz, hw⟩, hzw⟩, fun hW => hne (hWac z hz w hw hzw hW).symm⟩, rfl⟩
  -- a `≤`-minimal point of `S` (Zorn), which is not in the strict future
  obtain ⟨s₀, hs₀⟩ := hSconn.nonempty
  obtain ⟨m, hm⟩ := exists_maximal_of_chains_bounded (α := S)
    (r := fun a b : S => C.le ⊤ (b : M) a) (fun c hc => by
      by_cases hne : c.Nonempty
      · haveI : Nonempty c := hne.to_subtype
        let t : c → Set M := fun i => S ∩ C.Jminus ⊤ {((i : S) : M)}
        have hmem : ∀ i : c, ((i : S) : M) ∈ t i := fun i =>
          ⟨(i : S).2, ⟨_, mem_singleton _, C.le_refl trivial⟩⟩
        obtain ⟨m', hm'⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed t
          (fun i j => by
            by_cases hij : (i : S) = (j : S)
            · refine ⟨i, le_rfl, ?_⟩
              show t i ⊆ t j
              simp only [t, hij, subset_refl]
            · rcases hc i.2 j.2 hij with h | h
              · refine ⟨j, fun x hx => ⟨hx.1, ?_⟩, le_rfl⟩
                obtain ⟨_, rfl, hxj⟩ := hx.2
                exact ⟨_, mem_singleton _, C.le_trans hxj h⟩
              · refine ⟨i, le_rfl, fun x hx => ⟨hx.1, ?_⟩⟩
                obtain ⟨_, rfl, hxi⟩ := hx.2
                exact ⟨_, mem_singleton _, C.le_trans hxi h⟩)
          (fun i => ⟨_, hmem i⟩) (fun i => hSc.inter_right (hG.isClosed_Jminus_singleton hT _))
          (fun i => hSc.isClosed.inter (hG.isClosed_Jminus_singleton hT _))
        have hm'S : m' ∈ S := (mem_iInter.1 hm' (Classical.arbitrary c)).1
        refine ⟨⟨m', hm'S⟩, fun a ha => ?_⟩
        obtain ⟨_, rfl, h⟩ := (mem_iInter.1 hm' ⟨a, ha⟩).2
        exact h
      · refine ⟨⟨s₀, hs₀⟩, fun a ha => absurd ⟨a, ha⟩ hne⟩)
    (fun h₁ h₂ => C.le_trans h₂ h₁)
  have hmQ : (m : M) ∉ C.strictJplus S := by
    rintro ⟨z, hz, hzm, hne⟩
    exact hne (hcaus (hm ⟨z, hz⟩ hzm) hzm)
  -- connectedness
  by_contra hnac
  have hA : (S ∩ C.strictJplus S).Nonempty := by
    simp only [IsAcausal, not_forall] at hnac
    obtain ⟨z, hz, w, hw, hzw, hne⟩ := hnac
    exact ⟨w, hw, z, hz, hzw, Ne.symm hne⟩
  obtain ⟨s, hsS, hsQ, hsK⟩ := hSconn.isPreconnected _ _ hQ hK.isOpen_compl
    (fun s hs => by
      by_cases h : s ∈ C.strictJplus S
      · exact Or.inl h
      · exact Or.inr fun h' => h (hKQ h'))
    hA ⟨m, m.2, fun h => hmQ (hKQ h)⟩
  exact hsK (hQK ⟨hsS, hsQ⟩)

/-! ### Lemma K -/

/-- **Lemma K without a splitting** (the core). On a connected Hausdorff tarentin globally
hyperbolic causally arc-connected spacetime with `J^±(p) ≠ {p}` in which curves extend, a compact
connected locally Cauchy set `Σ` whose strict causal future and strict causal past are open is a
Cauchy surface. -/
theorem isCauchySurface_of_isLocallyCauchy_of_isOpen_strictJplus [T2Space M] [ConnectedSpace M]
    (hT : C.Tarentin) (hG : C.GloballyHyperbolic) (hC : C.CausallyArcConnected)
    (hJm : ∀ p : M, C.Jminus ⊤ {p} ≠ {p}) (hJp : ∀ p : M, C.Jplus ⊤ {p} ≠ {p})
    (hext : C.CurvesExtend) {S : Set M} (hSc : IsCompact S) (hSconn : IsConnected S)
    (hloc : C.IsLocallyCauchy S) (hQp : IsOpen (C.strictJplus S))
    (hQm : IsOpen (C.dual.strictJplus S)) : C.IsCauchySurface S := by
  have hcaus := hG.1
  have hac := isAcausal_of_isLocallyCauchy hT hG hC hext hSc hSconn hloc hQp
  have hle := hG.isClosed_le hT
  have hEc : IsClosed (C.Jminus ⊤ S) := isClosed_Jminus_of_isCompact hle hSc
  have hFc : IsClosed (C.Jplus ⊤ S) := isClosed_Jplus_of_isCompact hle hSc
  have hEF : ∀ q, q ∈ C.Jplus ⊤ S → q ∈ C.Jminus ⊤ S → q ∈ S := by
    rintro q ⟨z, hz, hzq⟩ ⟨w, hw, hqw⟩
    have h := hac z hz w hw (C.le_trans hzq hqw)
    subst h
    rw [hcaus hqw hzq]; exact hz
  -- step 2: `J^+(S) ∪ J^-(S) = M`
  have hD : ∀ q, q ∈ C.Jplus ⊤ S ∪ C.Jminus ⊤ S := by
    have hopen : IsOpen (C.Jplus ⊤ S ∪ C.Jminus ⊤ S) := by
      rw [isOpen_iff_mem_nhds]
      intro q hq
      by_cases hqS : q ∈ S
      · obtain ⟨U, hqU, hU, hSU⟩ := hloc q hqS
        refine mem_of_superset (U.isOpen.mem_nhds hqU) fun r hr => ?_
        rcases mem_Jplus_or_Jminus_of_isCauchySurfaceOn hcaus hext hSU hr with
          ⟨z, hz, hzr⟩ | ⟨z, hz, hrz⟩
        · exact Or.inl ⟨z, hz.1, C.le_mono le_top hzr⟩
        · exact Or.inr ⟨z, hz.1, C.le_mono le_top hrz⟩
      · rcases hq with ⟨z, hz, hzq⟩ | ⟨z, hz, hqz⟩
        · have hmem : q ∈ C.strictJplus S := ⟨z, hz, hzq, fun h => hqS (h ▸ hz)⟩
          refine mem_of_superset (hQp.mem_nhds hmem) ?_
          rintro r ⟨z', hz', hz'r, -⟩
          exact Or.inl ⟨z', hz', hz'r⟩
        · have hmem : q ∈ C.dual.strictJplus S := ⟨z, hz, hqz, fun h => hqS (h ▸ hz)⟩
          refine mem_of_superset (hQm.mem_nhds hmem) ?_
          rintro r ⟨z', hz', hrz', -⟩
          exact Or.inr ⟨z', hz', hrz'⟩
    have hne : (C.Jplus ⊤ S ∪ C.Jminus ⊤ S).Nonempty := by
      obtain ⟨s, hs⟩ := hSconn.nonempty
      exact ⟨s, Or.inl ⟨s, hs, C.le_refl trivial⟩⟩
    have huniv := IsClopen.eq_univ ⟨hFc.union hEc, hopen⟩ hne
    intro q
    rw [huniv]; trivial
  -- step 3: every inextensible curve meets `S`
  intro I c hc
  obtain ⟨φ, -, -, hφr, hcφ⟩ := hc.reparam hC hcaus hJm hJp
  obtain ⟨s₁, hs₁⟩ := exists_not_mem_Jminus_of_isCompact hT hG hC hJp hcφ hSc
  obtain ⟨s₀, hs₀⟩ := exists_not_mem_Jplus_of_isCompact hT hG hC hJm hcφ hSc
  have hF1 : (c ∘ φ) s₁ ∈ C.Jplus ⊤ S := (hD _).resolve_right hs₁
  have hE0 : (c ∘ φ) s₀ ∈ C.Jminus ⊤ S := (hD _).resolve_left hs₀
  have h01 : s₀ ≤ s₁ := by
    by_contra hlt
    push Not at hlt
    obtain ⟨z, hz, hzc⟩ := hF1
    exact hs₀ ⟨z, hz, C.le_trans hzc (hcφ.1.le_of_le trivial trivial hlt.le)⟩
  have hcont : Continuous (c ∘ φ) := hcφ.1.continuous
  obtain ⟨s, -, hsE, hsF⟩ := isPreconnected_closed_iff.1 isPreconnected_Icc _ _
    (hEc.preimage hcont) (hFc.preimage hcont) (fun t _ => (hD ((c ∘ φ) t)).symm)
    ⟨s₀, ⟨le_rfl, h01⟩, hE0⟩ ⟨s₁, ⟨h01, le_rfl⟩, hF1⟩
  have hcS : c (φ s) ∈ S := hEF _ hsF hsE
  have hφs : φ s ∈ I := hφr ▸ mem_range_self s
  refine ⟨c (φ s), ⟨⟨φ s, hφs, rfl⟩, hcS⟩, ?_⟩
  rintro _ ⟨⟨t, ht, rfl⟩, htS⟩
  rcases le_total t (φ s) with hle | hle
  · exact hac _ htS _ hcS (hc.1.le_of_le ht hφs hle)
  · exact (hac _ hcS _ htS (hc.1.le_of_le hφs ht hle)).symm

/-- **Lemma K, the chronal form (no splitting, no two-sidedness).** The hypotheses of the bare
DEC-44 form (`isCauchySurface_of_isLocallyCauchy`), plus `CurvesExtend`, push-up, and every point
strongly tarentin in the future and in the past (`Z^± = M`). No splitting, no two-sidedness. -/
theorem isCauchySurface_of_isLocallyCauchy_of_chronal [T2Space M] [ConnectedSpace M]
    (hT : C.Tarentin) (hG : C.GloballyHyperbolic) (hC : C.CausallyArcConnected)
    (hJm : ∀ p : M, C.Jminus ⊤ {p} ≠ {p}) (hJp : ∀ p : M, C.Jplus ⊤ {p} ≠ {p})
    (hext : C.CurvesExtend) (hpush : C.PushUp) (hZp : ∀ p : M, p ∈ C.Zplus)
    (hZm : ∀ p : M, p ∈ C.Zminus) {S : Set M} (hSc : IsCompact S) (hSconn : IsConnected S)
    (hloc : C.IsLocallyCauchy S) : C.IsCauchySurface S :=
  isCauchySurface_of_isLocallyCauchy_of_isOpen_strictJplus hT hG hC hJm hJp hext hSc hSconn hloc
    (isOpen_strictJplus_of_Zminus hT hG hC hJm hext hpush hZm hSc.isClosed hloc)
    (isOpen_strictJplus_of_Zminus (C := C.dual) (dual_tarentin.2 hT)
      (dual_globallyHyperbolic.2 hG) (dual_causallyArcConnectedOn.2 hC) hJp hext.dual
      (dual_pushUp.2 hpush) hZp hSc.isClosed hloc.dual)

/-- **Lemma K, two-sided, without a splitting**: `CompactCauchy`'s proved form
(`isCauchySurface_of_isLocallyCauchyTwoSided`) with its splitting replaced by causal openness of
`⊤` — the causal future and past of an open set are open. -/
theorem isCauchySurface_of_isLocallyCauchyTwoSided_of_isOpen_Jplus [T2Space M] [ConnectedSpace M]
    (hT : C.Tarentin) (hG : C.GloballyHyperbolic) (hC : C.CausallyArcConnected)
    (hJm : ∀ p : M, C.Jminus ⊤ {p} ≠ {p}) (hJp : ∀ p : M, C.Jplus ⊤ {p} ≠ {p})
    (hext : C.CurvesExtend) (hOp : ∀ V : Opens M, IsOpen (C.Jplus ⊤ V))
    (hOm : ∀ V : Opens M, IsOpen (C.Jminus ⊤ V)) {S : Set M} (hSc : IsCompact S)
    (hSconn : IsConnected S) (hloc : C.IsLocallyCauchyTwoSided S) : C.IsCauchySurface S :=
  isCauchySurface_of_isLocallyCauchy_of_isOpen_strictJplus hT hG hC hJm hJp hext hSc hSconn
    hloc.isLocallyCauchy (isOpen_strictJplus_of_twoSided hG.1 hC hext hOp hloc)
    (isOpen_strictJplus_of_twoSided (C := C.dual) (dual_isCausal.2 hG.1)
      (dual_causallyArcConnectedOn.2 hC) hext.dual hOm hloc.dual)

/-- **Lemma K in the shape gx needs** (no splitting): the past side from push-up and `Z^+ = M`
(both fields of `SingularFlatAxioms`, true at BTZ points), the future side from two-sidedness in
the charts and "the causal future of an open set is open". -/
theorem isCauchySurface_of_isLocallyCauchyTwoSided_of_pushUp [T2Space M] [ConnectedSpace M]
    (hT : C.Tarentin) (hG : C.GloballyHyperbolic) (hC : C.CausallyArcConnected)
    (hJm : ∀ p : M, C.Jminus ⊤ {p} ≠ {p}) (hJp : ∀ p : M, C.Jplus ⊤ {p} ≠ {p})
    (hext : C.CurvesExtend) (hpush : C.PushUp) (hZp : ∀ p : M, p ∈ C.Zplus)
    (hOp : ∀ V : Opens M, IsOpen (C.Jplus ⊤ V)) {S : Set M} (hSc : IsCompact S)
    (hSconn : IsConnected S) (hloc : C.IsLocallyCauchyTwoSided S) : C.IsCauchySurface S :=
  isCauchySurface_of_isLocallyCauchy_of_isOpen_strictJplus hT hG hC hJm hJp hext hSc hSconn
    hloc.isLocallyCauchy (isOpen_strictJplus_of_twoSided hG.1 hC hext hOp hloc)
    (isOpen_strictJplus_of_Zminus (C := C.dual) (dual_tarentin.2 hT)
      (dual_globallyHyperbolic.2 hG) (dual_causallyArcConnectedOn.2 hC) hJp hext.dual
      (dual_pushUp.2 hpush) hZp hSc.isClosed hloc.isLocallyCauchy.dual)

/-! ### The core subsumes `CompactCauchy`'s proved form -/

/-- **Under `CompactCauchy`'s data (a splitting and two-sidedness) the core's openness hypotheses
hold**: the strict causal future of `Σ` is `{F > 0}` and its strict past `{F < 0}`, for the
graph function `F = τ − h ∘ π` of `CompactCauchy` (`exists_graph`, `isAcausal_of_graph`). The
derivation goes through `CompactCauchy`'s graph step, so it shows that the hypothesis sets nest,
not a second proof of acausality. -/
theorem isOpen_strictJplus_of_isCauchySplitting [T2Space M] [ConnectedSpace M] (hcaus : C.IsCausal)
    (hC : C.CausallyArcConnected) (hext : C.CurvesExtend) {S₀ : Set M} {ψ : S₀ × ℝ ≃ₜ M}
    (hψ : C.IsCauchySplitting S₀ ψ) {S : Set M} (hSc : IsCompact S) (hSconn : IsConnected S)
    (hloc : C.IsLocallyCauchyTwoSided S) :
    IsOpen (C.strictJplus S) ∧ IsOpen (C.dual.strictJplus S) := by
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
  have hP : C.strictJplus S = F ⁻¹' Ioi 0 := by
    ext q
    constructor
    · rintro ⟨z, hz, hzq, hne⟩
      by_contra hq
      obtain ⟨w, hw, hqw⟩ := hFle q (not_lt.1 hq)
      have hzw := hac z hz w hw (C.le_trans hzq hqw)
      subst hzw
      exact hne (hcaus hqw hzq)
    · intro hq
      have hq' : 0 < F q := hq
      obtain ⟨z, hz, hzq⟩ := hFge q hq'.le
      exact ⟨z, hz, hzq, fun he => hq'.ne' ((hF0 q).1 (he ▸ hz))⟩
  have hM : C.dual.strictJplus S = F ⁻¹' Iio 0 := by
    ext q
    constructor
    · rintro ⟨z, hz, hqz, hne⟩
      by_contra hq
      obtain ⟨w, hw, hwq⟩ := hFge q (not_lt.1 hq)
      have hwz := hac w hw z hz (C.le_trans hwq hqz)
      subst hwz
      exact hne (hcaus hqz hwq)
    · intro hq
      have hq' : F q < 0 := hq
      obtain ⟨z, hz, hqz⟩ := hFle q hq'.le
      exact ⟨z, hz, hqz, fun he => hq'.ne ((hF0 q).1 (he ▸ hz))⟩
  exact ⟨hP ▸ isOpen_Ioi.preimage hFc, hM ▸ isOpen_Iio.preimage hFc⟩

/-- **`CompactCauchy`'s proved form, through the core**: its hypotheses imply the core's
(`isOpen_strictJplus_of_isCauchySplitting`), so the core is a true generalisation of
`isCauchySurface_of_isLocallyCauchyTwoSided`. -/
theorem isCauchySurface_of_isCauchySplitting_via_strictJplus [T2Space M] [ConnectedSpace M]
    (hT : C.Tarentin) (hG : C.GloballyHyperbolic) (hC : C.CausallyArcConnected)
    (hJm : ∀ p : M, C.Jminus ⊤ {p} ≠ {p}) (hJp : ∀ p : M, C.Jplus ⊤ {p} ≠ {p})
    (hext : C.CurvesExtend) {S₀ : Set M} {ψ : S₀ × ℝ ≃ₜ M} (hψ : C.IsCauchySplitting S₀ ψ)
    {S : Set M} (hSc : IsCompact S) (hSconn : IsConnected S) (hloc : C.IsLocallyCauchyTwoSided S) :
    C.IsCauchySurface S :=
  have h := isOpen_strictJplus_of_isCauchySplitting hG.1 hC hext hψ hSc hSconn hloc
  isCauchySurface_of_isLocallyCauchy_of_isOpen_strictJplus hT hG hC hJm hJp hext hSc hSconn
    hloc.isLocallyCauchy h.1 h.2

end Causality

/-! ### Static spacetimes: the bare form holds -/

namespace staticCausality

variable {X : Type*} [MetricSpace X] [GeodesicSpace X]

theorem Jminus_singleton_ne (p : ℝ × X) : (staticCausality X).Jminus ⊤ {p} ≠ {p} := by
  intro h
  have hmem : (p.1 - 1, p.2) ∈ (staticCausality X).Jminus ⊤ {p} := by
    rw [mem_Jminus_top]; simp
  rw [h, mem_singleton_iff, Prod.ext_iff] at hmem
  simp at hmem

theorem Jplus_singleton_ne (p : ℝ × X) : (staticCausality X).Jplus ⊤ {p} ≠ {p} := by
  intro h
  have hmem : (p.1 + 1, p.2) ∈ (staticCausality X).Jplus ⊤ {p} := by
    rw [mem_Jplus_top]; simp
  rw [h, mem_singleton_iff, Prod.ext_iff] at hmem
  simp at hmem

/-- A geodesic space is preconnected: a geodesic is Lipschitz on `[0, 1]`. -/
theorem preconnectedSpace_of_geodesic : PreconnectedSpace X := by
  refine ⟨isPreconnected_of_forall_pair fun x _ y _ => ?_⟩
  obtain ⟨g, hg0, hg1, hg⟩ := GeodesicSpace.exists_geodesic x y
  have hL : LipschitzOnWith (nndist x y) g (Icc 0 1) :=
    LipschitzOnWith.of_dist_le_mul fun s hs s' hs' => by
      rw [hg s hs s' hs', Real.dist_eq, coe_nndist, mul_comm]
  exact ⟨g '' Icc 0 1, subset_univ _, ⟨0, ⟨le_rfl, zero_le_one⟩, hg0⟩,
    ⟨1, ⟨zero_le_one, le_rfl⟩, hg1⟩, isPreconnected_Icc.image g hL.continuousOn⟩

/-- **Global hyperbolicity of `ℝ × X` forces `X` proper**: the closed ball `B(x, r)` is the
spatial projection of the slice `t = r` of the diamond from `(0, x)` to `(2r, x)`. -/
theorem properSpace_of_globallyHyperbolic (hG : (staticCausality X).GloballyHyperbolic) :
    ProperSpace X := by
  refine ProperSpace.of_isCompact_closedBall_of_le 0 fun x r hr => ?_
  have hK : IsCompact ((staticCausality X).diamond ⊤ (0, x) (2 * r, x) ∩ ({r} ×ˢ univ)) :=
    (hG.2 _ _).inter_right (isClosed_singleton.prod isClosed_univ)
  convert hK.image continuous_snd using 1
  ext y
  constructor
  · intro hy
    rw [Metric.mem_closedBall] at hy
    refine ⟨(r, y), ⟨Causality.mem_diamond.2 ⟨?_, ?_⟩, rfl, trivial⟩, rfl⟩
    · rw [le_top_iff]; simp only; rw [dist_comm]; linarith
    · rw [le_top_iff]; simp only; linarith
  · rintro ⟨⟨t, y'⟩, ⟨hd, ht, -⟩, rfl⟩
    rw [mem_singleton_iff] at ht
    subst ht
    obtain ⟨h1, -⟩ := Causality.mem_diamond.1 hd
    rw [le_top_iff] at h1
    simp only at h1
    rw [Metric.mem_closedBall, dist_comm]; linarith

/-- **Lemma K holds, in its bare DEC-44 form, on every static spacetime `ℝ × X` over a proper
geodesic space**: a compact connected locally Cauchy set is a Cauchy surface. Connectedness of `X`
is automatic (`preconnectedSpace_of_geodesic`, `X` non-empty as `Σ` is). Minkowski space and the
massive-particle models `E_α`, `α > 0`, are instances; the flat `ℝ × torus` (a translation
spacetime) is one mathematically, but no torus instance is built in the library. -/
theorem isCauchySurface_of_compact_isLocallyCauchy [ProperSpace X]
    {S : Set (ℝ × X)} (hSc : IsCompact S) (hSconn : IsConnected S)
    (hloc : (staticCausality X).IsLocallyCauchy S) : (staticCausality X).IsCauchySurface S := by
  haveI : PreconnectedSpace X := preconnectedSpace_of_geodesic
  haveI : Nonempty X := ⟨hSconn.nonempty.some.2⟩
  haveI : ConnectedSpace X := { toNonempty := inferInstance }
  exact Causality.isCauchySurface_of_isLocallyCauchy_of_chronal tarentin globallyHyperbolic
    causallyArcConnected Jminus_singleton_ne Jplus_singleton_ne curvesExtend pushUp mem_Zplus
    mem_Zminus hSc hSconn hloc

/-- **The bare statement `Causality.isCauchySurface_of_isLocallyCauchy`, verbatim, for
`C = staticCausality X`** over any geodesic metric space `X`: properness is derived from global
hyperbolicity (`properSpace_of_globallyHyperbolic`); the other hypotheses are carried only to
match the bare signature (they hold automatically). -/
theorem isCauchySurface_of_isLocallyCauchy_bare [T2Space (ℝ × X)] [ConnectedSpace (ℝ × X)]
    (_hT : (staticCausality X).Tarentin) (hG : (staticCausality X).GloballyHyperbolic)
    (_hC : (staticCausality X).CausallyArcConnected)
    (_hJm : ∀ p : ℝ × X, (staticCausality X).Jminus ⊤ {p} ≠ {p})
    (_hJp : ∀ p : ℝ × X, (staticCausality X).Jplus ⊤ {p} ≠ {p})
    {S : Set (ℝ × X)} (hSc : IsCompact S) (hSconn : IsConnected S)
    (hloc : (staticCausality X).IsLocallyCauchy S) : (staticCausality X).IsCauchySurface S := by
  haveI := properSpace_of_globallyHyperbolic hG
  exact isCauchySurface_of_compact_isLocallyCauchy hSc hSconn hloc

end staticCausality

/-- **The bare form on the massive-particle model `E_α`, `α > 0`** (`Causal.Model.Massive`, a
singular flat model with a timelike singular line): a compact connected locally Cauchy set is a
Cauchy surface. -/
theorem massive_isCauchySurface_of_compact_isLocallyCauchy (α : ℝ) [Fact (0 < α)]
    {S : Set (Massive α)} (hSc : IsCompact S) (hSconn : IsConnected S)
    (hloc : (massive α).IsLocallyCauchy S) : (massive α).IsCauchySurface S :=
  staticCausality.isCauchySurface_of_compact_isLocallyCauchy hSc hSconn hloc

/-! ### Non-vacuity: the timelike line -/

/-- The hypotheses of `isCauchySurface_of_isLocallyCauchy_of_chronal` hold jointly on the timelike
line with `Σ = {0}`. -/
theorem timelikeLine_lemmaKBare_hypotheses :
    timelikeLine.Tarentin ∧ timelikeLine.GloballyHyperbolic ∧
      timelikeLine.CausallyArcConnected ∧ (∀ p : ℝ, timelikeLine.Jminus ⊤ {p} ≠ {p}) ∧
      (∀ p : ℝ, timelikeLine.Jplus ⊤ {p} ≠ {p}) ∧ timelikeLine.CurvesExtend ∧
      timelikeLine.PushUp ∧ (∀ p : ℝ, p ∈ timelikeLine.Zplus) ∧
      (∀ p : ℝ, p ∈ timelikeLine.Zminus) ∧ IsCompact ({0} : Set ℝ) ∧
      IsConnected ({0} : Set ℝ) ∧ timelikeLine.IsLocallyCauchy ({0} : Set ℝ) := by
  obtain ⟨hT, hG, hC, hJm, hJp, hext, -, hSc, hSconn, hloc⟩ := timelikeLine_lemmaK_hypotheses
  exact ⟨hT, hG, hC, hJm, hJp, hext, timelikeLine_pushUp, timelikeLine_mem_Zplus,
    timelikeLine_mem_Zminus, hSc, hSconn, hloc.isLocallyCauchy⟩

/-- The chronal form of Lemma K applied on the timelike line. -/
theorem timelikeLine_isCauchySurface_zero_of_lemmaKBare :
    timelikeLine.IsCauchySurface ({0} : Set ℝ) := by
  obtain ⟨hT, hG, hC, hJm, hJp, hext, hpush, hZp, hZm, hSc, hSconn, hloc⟩ :=
    timelikeLine_lemmaKBare_hypotheses
  exact Causality.isCauchySurface_of_isLocallyCauchy_of_chronal hT hG hC hJm hJp hext hpush hZp
    hZm hSc hSconn hloc

theorem timelikeLine_isOpen_Jplus (V : Opens ℝ) : IsOpen (timelikeLine.Jplus ⊤ V) :=
  Causality.isOpen_Jplus_of_pushUp timelikeLine_pushUp timelikeLine_mem_Zminus V

theorem timelikeLine_isOpen_Jminus (V : Opens ℝ) : IsOpen (timelikeLine.Jminus ⊤ V) :=
  Causality.isOpen_Jplus_of_pushUp (C := timelikeLine.dual) (Causality.dual_pushUp.2 timelikeLine_pushUp)
    timelikeLine_mem_Zplus V

/-- The hypotheses of `isCauchySurface_of_isLocallyCauchyTwoSided_of_isOpen_Jplus` and of
`isCauchySurface_of_isLocallyCauchyTwoSided_of_pushUp` hold jointly on the timelike line with
`Σ = {0}`. -/
theorem timelikeLine_lemmaKBare_twoSided_hypotheses :
    timelikeLine.Tarentin ∧ timelikeLine.GloballyHyperbolic ∧
      timelikeLine.CausallyArcConnected ∧ (∀ p : ℝ, timelikeLine.Jminus ⊤ {p} ≠ {p}) ∧
      (∀ p : ℝ, timelikeLine.Jplus ⊤ {p} ≠ {p}) ∧ timelikeLine.CurvesExtend ∧
      timelikeLine.PushUp ∧ (∀ p : ℝ, p ∈ timelikeLine.Zplus) ∧
      (∀ V : Opens ℝ, IsOpen (timelikeLine.Jplus ⊤ V)) ∧
      (∀ V : Opens ℝ, IsOpen (timelikeLine.Jminus ⊤ V)) ∧ IsCompact ({0} : Set ℝ) ∧
      IsConnected ({0} : Set ℝ) ∧ timelikeLine.IsLocallyCauchyTwoSided ({0} : Set ℝ) := by
  obtain ⟨hT, hG, hC, hJm, hJp, hext, -, hSc, hSconn, hloc⟩ := timelikeLine_lemmaK_hypotheses
  exact ⟨hT, hG, hC, hJm, hJp, hext, timelikeLine_pushUp, timelikeLine_mem_Zplus,
    timelikeLine_isOpen_Jplus, timelikeLine_isOpen_Jminus, hSc, hSconn, hloc⟩

/-- The two-sided form of Lemma K applied on the timelike line. -/
theorem timelikeLine_isCauchySurface_zero_of_lemmaKBare_twoSided :
    timelikeLine.IsCauchySurface ({0} : Set ℝ) := by
  obtain ⟨hT, hG, hC, hJm, hJp, hext, -, -, hOp, hOm, hSc, hSconn, hloc⟩ :=
    timelikeLine_lemmaKBare_twoSided_hypotheses
  exact Causality.isCauchySurface_of_isLocallyCauchyTwoSided_of_isOpen_Jplus hT hG hC hJm hJp
    hext hOp hOm hSc hSconn hloc

/-- The gx form of Lemma K applied on the timelike line. -/
theorem timelikeLine_isCauchySurface_zero_of_lemmaKBare_gx :
    timelikeLine.IsCauchySurface ({0} : Set ℝ) := by
  obtain ⟨hT, hG, hC, hJm, hJp, hext, hpush, hZp, hOp, -, hSc, hSconn, hloc⟩ :=
    timelikeLine_lemmaKBare_twoSided_hypotheses
  exact Causality.isCauchySurface_of_isLocallyCauchyTwoSided_of_pushUp hT hG hC hJm hJp hext
    hpush hZp hOp hSc hSconn hloc

end Causal
