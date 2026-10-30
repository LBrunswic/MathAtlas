import Causal.Cauchy
import Causal.Measure
import Causal.MeasureRemarks

/-!
# The generalised Geroch theorem: (i) ⇒ (ii) and (ii) ⇒ (iii)

`theo:geroch` — `ETT.tex:1256`, implications (i)⇒(ii) and (ii)⇒(iii), both proved in full, with
(ii) as the author ruled it (DEC-15): **a Cauchy time function strictly increasing along `≤`**
(`geroch_i_imp_ii`, `geroch_ii_imp_iii`). The label is not marked because it is an equivalence
whose third implication, (iii)⇒(i), is cited by the paper (`CausalScaffold.GerochEquiv`). The
notions are those of DEC-13 (inextensible, `Causal.Inextensible`) and DEC-14 (Cauchy
surface, `Causal.Cauchy`).

> Let $M$ be a metrizable, locally compact topological spacetime. Assume moreover that $M$ is
> tarentin, causally arc-connected and locally causally convex, and that $J^\pm(p)\neq \{p\}$ for
> every $p\in M$. If $M$ admits a pair $(\mu_+,\mu_-)$ of measures admissible respectively in the
> future and in the past, then the following are equivalent: (i) $M$ is globally hyperbolic;
> (ii) $M$ admits a Cauchy time function; (iii) $M$ admits a Cauchy hypersurface.

DEC-15: (ii) asks a Cauchy time function strictly increasing: `x ≤ y`, `x ≠ y` ⇒ `T x < T y`.

> We then set $T(x)=\log\left(-\frac{t^-(x)}{t^+(x)}\right)$. $T$ is a time function. […]
> It suffices to take $S=T^{-1}(0)$ as Cauchy hypersurface.

## Hypothesis checklist

| paper hypothesis | (i)⇒(ii), `geroch_i_imp_ii` | (ii)⇒(iii), `geroch_ii_imp_iii` |
|---|---|---|
| metrizable | ⚠ weakened: `T2Space`, `FirstCountableTopology` | ⚠ weakened: `T1Space` |
| locally compact | ⚠ weakened: not used | ⚠ weakened: not used |
| tarentin | ✓ carried | ⚠ weakened: not used |
| causally arc-connected | ✓ carried | ✓ carried |
| locally causally convex | ⚠ reading: `StronglyCausal` (DEC-7, causally convex neighbourhoods not necessarily open); `ETT.tex:1215–1216` suggests *open* causally convex neighbourhoods, which is stronger, so the Lean hypothesis is weaker. (i)⇒(ii): not used at all — a consequence of global hyperbolicity (`prop:GH_fortement_causal`) | ⚠ reading, as on the left: `StronglyCausal`, carried |
| `J^±(p) ≠ {p}` | ✓ carried | ✓ carried |
| `μ₊`, `μ₋` admissible in the future, in the past | ✓ carried, `BorelSpace M` (property 1.) | ⚠ weakened: not used |
| (ii) strictly increasing along `≤` (DEC-15) | ✓ produced (`gerochTime_lt`) | ✓ carried |

## SCOPE (disclosed)

* **The open-map gap of WP-1 is closed.** DEC-10 asks a time function to be an open map, and the
  sketch never shows that `T = log(−t⁻/t⁺)` is one. It is (`isOpenMap_gerochTime`): around `x`,
  strong causality gives a causally convex neighbourhood `V` inside a given open set, the
  tarentin property a diamond `J(p, q) ⊂ V` with `x` in its interior, and `p ≠ x ≠ q`, because
  in a causally arc-connected causal `T1` spacetime with `J^-(x) ≠ {x}` the causal future `J^+(x)`
  is never a neighbourhood of `x` (`Jplus_not_mem_nhds`: a causal curve from a point of
  `J^-(x) ∖ {x}` to `x` would have to jump). Then `T(p) < T(x) < T(q)`, and `[T p, T q] ⊂ T(V)`
  by the intermediate value theorem along a causal curve from `p` to `q`, which stays in
  `J(p,q) ⊂ V`.
* **Chronology is derived.** `T` must send `≪` to `<`, which needs `x ≪ y ⇒ x ≠ y`; the same
  lemma gives it (`ne_of_lt_top`): if `x ≪ x`, `I^+(x)` is an open neighbourhood of `x` inside
  `J^+(x)`.
* **(i)⇒(ii) follows the sketch**, with these precisions. The decreasing sequence `(x_n)` is the
  sequence `c(−n)`, `n ∈ ℕ`, and `μ₋(⋂ J^-(c(−n))) > 0` gives `q ≤ c(s)` for every `s`
  (`exists_le_of_bddBelow`). The accumulation point is unique by causal convexity, which needs
  no second accumulation point: a single causally convex neighbourhood that the curve visits
  arbitrarily far in the past contains the whole tail (`tendsto_of_mapClusterPt`). The curve
  over `ℝ` is reparametrised by `log` over `]0, ∞[` and Fact 1 of `Causal.Inextensible`
  (adjoin the limit, then prepend) applies, as an extension **at the past end**
  (`pastExtensible_of_forall_le`). So the statement is the sketch's one-sided one (DEC-13,
  `ETT.tex:1295–1296`), for curves over `ℝ` (the paper states it over any interval, with limits at
  its ends; curves over `ℝ` are what `def:cauchy_time_function` quantifies over): `T → −∞` along
  every *past*-inextensible curve
  (`tendsto_atBot_gerochTime_of_pastInextensible`) and `T → +∞` along every
  *future*-inextensible curve (`tendsto_atTop_gerochTime_of_futureInextensible`); the future end is
  the past end of `C.dual`, with `μ₊`, `μ₋` exchanged (`gerochTime_dual`,
  `dual_pastInextensible_iff`).
* **(ii)⇒(iii) with `S = T⁻¹(0)` needs `T` strictly increasing along the causal relation**, which
  a time function (DEC-10: `≤ ↦ ≤`, `≪ ↦ <`) need not be; this is why the author ruled DEC-15.
  *Finding, formalized as `minkowski2_dec15` in `Causal.Minkowski` (with `g` a Lipschitz clamp):* on 1+1 Minkowski space, `T(t,x) = t − g(x)` with `g` smooth, bounded,
  `|g'| ≤ 1` and `g(x) = x` on `[0, 1]` is a Cauchy time function in the sense of DEC-10, and
  `T⁻¹(0)` contains the null segment from `(0,0)` to `(1,1)`, which an inextensible null geodesic
  meets in infinitely many points. What holds for every Cauchy time function is that `T⁻¹(0)`
  meets every inextensible causal curve **at least once** (`IsCauchyTimeFunction.exists_mem_zero`);
  exactly once holds under strict monotonicity (`IsCauchyTimeFunction.isCauchySurface`), which is
  (ii) as ruled (DEC-15). The function `T` built in (i)⇒(ii) is strictly increasing
  (`gerochTime_lt`), so (i)⇒(iii) holds with `S = T⁻¹(0)` (`geroch_i_imp_iii`).
* **Witnesses** (kb/0011): on the timelike line `id` is a Cauchy time function strictly
  increasing along `≤`, and `{0}` is a Cauchy surface (`timelikeLine_isCauchyTimeFunction_id`,
  `timelikeLine_isCauchySurface_zero`). The hypotheses of (i)⇒(ii) are jointly satisfiable: on
  the timelike line the standard Gaussian measure is admissible in the past and in the future
  (`timelikeLine_admissible_past_and_future`; `K^-(a) ⊇ ]-∞, a[`, so `J^-(A) ∖ K^-(A)` has at most
  one point and is null, the measure having no atoms — the argument of
  `lightlikeLine_admissible_past_and_future` in `Causal.MeasureRemarks`), and `geroch_i_imp_ii`
  applies (`timelikeLine_exists_strict_isCauchyTimeFunction`). Construction due to the WP-7
  audit.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Filter MeasureTheory

open scoped ENNReal

universe u

variable {M : Type u} [TopologicalSpace M]

namespace Causality

variable {C : Causality M}

/-! ### Causal facts -/

/-- In a causally arc-connected causal `T1` spacetime, if `J^-(x) ≠ {x}` then `J^+(x)` is not a
neighbourhood of `x`. -/
theorem Jplus_not_mem_nhds [T1Space M] (hC : C.CausallyArcConnected) (hcaus : C.IsCausal)
    {x : M} (hx : C.Jminus ⊤ {x} ≠ {x}) : C.Jplus ⊤ {x} ∉ 𝓝 x := by
  intro hN
  obtain ⟨y, hyJ, hyx⟩ := exists_ne_of_ne_singleton
    (by simpa using C.le_refl (show x ∈ (⊤ : Opens M) from trivial) : x ∈ C.Jminus ⊤ {x}) hx
  have hy : C.le ⊤ y x := by simpa using hyJ
  obtain ⟨γ, hγ, hγ0, hγ1⟩ := (hC ⊤ le_rfl y x).1.1 hy
  have hxD : x ∈ interior (C.Jplus ⊤ {x}) := mem_interior_iff_mem_nhds.2 hN
  have hpre : IsPreconnected (γ '' Icc 0 1) :=
    isPreconnected_Icc.image γ (hγ.continuousOn C.isRelFamily_le)
  have key : ∀ z ∈ γ '' Icc 0 1, z ∈ interior (C.Jplus ⊤ {x}) → z = x := by
    rintro _ ⟨s, hs, rfl⟩ hzD
    have h1 : C.le ⊤ x (γ s) := by simpa using interior_subset hzD
    have h2 : C.le ⊤ (γ s) x := by rw [← hγ1]; exact hγ.le_of_le hs.1 hs.2 le_rfl
    exact hcaus h2 h1
  obtain ⟨z, hz, hzD, hzx⟩ := hpre _ _ isOpen_interior isClosed_singleton.isOpen_compl
    (fun z _ => by
      by_cases h : z = x
      · left; rw [h]; exact hxD
      · right; exact h)
    ⟨x, ⟨1, ⟨zero_le_one, le_rfl⟩, hγ1⟩, hxD⟩ ⟨y, ⟨0, ⟨le_rfl, zero_le_one⟩, hγ0⟩, hyx⟩
  exact hzx (key z hz hzD)

/-- **Chronology** in a causally arc-connected causal `T1` spacetime with `J^-(x) ≠ {x}`:
`x ≪ y` implies `x ≠ y`. -/
theorem ne_of_lt_top [T1Space M] (hC : C.CausallyArcConnected) (hcaus : C.IsCausal)
    (hJm : ∀ p : M, C.Jminus ⊤ {p} ≠ {p}) {x y : M} (hxy : C.lt ⊤ x y) : x ≠ y := by
  rintro rfl
  apply Jplus_not_mem_nhds hC hcaus (hJm x)
  refine mem_of_superset ((C.isOpen_lt_right ⊤ x).mem_nhds hxy) fun z hz => ?_
  simpa using C.le_of_lt hz

/-- A monotone map from `ℝ` which has an accumulation point at `−∞`, in a strongly causal
spacetime, tends to it: a causally convex neighbourhood visited arbitrarily far in the past
contains the whole tail. -/
theorem tendsto_of_mapClusterPt (hSC : C.StronglyCausal) {c : ℝ → M}
    (hmono : ∀ s s', s ≤ s' → C.le ⊤ (c s) (c s')) {p : M} (hp : MapClusterPt p atBot c) :
    Tendsto c atBot (𝓝 p) := by
  intro N hN
  obtain ⟨V, hV, hVN, hVc⟩ := hSC p N hN
  have hfreq := frequently_atBot.1 (mapClusterPt_iff_frequently.1 hp V hV)
  obtain ⟨s₁, -, hs₁⟩ := hfreq 0
  refine mem_map.2 (mem_atBot_sets.2 ⟨s₁, fun s hs => hVN ?_⟩)
  obtain ⟨s₂, hs₂, hs₂V⟩ := hfreq s
  exact hVc.2 _ hs₂V _ hs₁ (mem_diamond.2 ⟨hmono _ _ hs₂, hmono _ _ hs⟩)

/-- **The extension step of (i)⇒(ii)**, causal part, one-sided (DEC-13): on a tarentin globally
hyperbolic Hausdorff causally arc-connected spacetime with `J^-(p) ≠ {p}`, a causal curve over `ℝ`
bounded below by a point `q` (`q ≤ c(s)` for every `s`) is extensible **at the past end**. -/
theorem pastExtensible_of_forall_le [T2Space M] (hT : C.Tarentin) (hG : C.GloballyHyperbolic)
    (hC : C.CausallyArcConnected) (hJm : ∀ p : M, C.Jminus ⊤ {p} ≠ {p}) {c : ℝ → M}
    (hc : C.CausalCurveIn ⊤ univ c) {q : M} (hq : ∀ s, C.le ⊤ q (c s)) :
    C.PastExtensible ⊤ univ c := by
  have hSC := hG.stronglyCausal hT
  have hJ := hG.isClosed_Jminus_singleton hT
  have hmono : ∀ s s', s ≤ s' → C.le ⊤ (c s) (c s') := fun s s' h =>
    hc.le_of_le trivial trivial h
  -- an accumulation point at `−∞`, in the compact diamond `J(q, c 0)`
  have hK := hG.2 q (c 0)
  obtain ⟨p, -, hp⟩ := hK.exists_clusterPt (f := map c atBot) (by
    rw [le_principal_iff]
    exact mem_map.2 (mem_atBot_sets.2 ⟨0, fun s hs => mem_diamond.2 ⟨hq s, hmono s 0 hs⟩⟩))
  have hlim : Tendsto c atBot (𝓝 p) := tendsto_of_mapClusterPt hSC hmono hp
  -- reparametrise by `log` over `]0, ∞[`
  have hc₁ : C.CausalCurveIn ⊤ (Ioi 0) (c ∘ Real.log) :=
    hc.comp ⟨1, mem_Ioi.2 (one_pos : (0 : ℝ) < 1)⟩ ordConnected_Ioi Real.strictMonoOn_log
      (Real.continuousOn_log.mono fun x hx => ne_of_gt hx) fun _ _ => trivial
  have hlim₁ : Tendsto (c ∘ Real.log) (𝓝[>] 0) (𝓝 p) := hlim.comp Real.tendsto_log_nhdsGT_zero
  have hext := pastExtensible_of_tendsto hJ hSC hC hG.1 hc₁ (a := 0) (fun _ ht => ht)
    (by rw [Ioi_insert]; exact ordConnected_Ici) hlim₁ (hJm p)
  exact hext.of_comp (ψ := Real.exp) (Real.exp_strictMono.strictMonoOn _)
    (fun t _ => Real.exp_pos t) (fun y hy => ⟨Real.log y, trivial, Real.exp_log hy⟩)
    (fun t _ => by simp [Real.log_exp])

/-- **The extension step of (i)⇒(ii)**, causal part: a causal curve over `ℝ` bounded below by a
point is extensible. -/
theorem extensible_of_forall_le [T2Space M] (hT : C.Tarentin) (hG : C.GloballyHyperbolic)
    (hC : C.CausallyArcConnected) (hJm : ∀ p : M, C.Jminus ⊤ {p} ≠ {p}) {c : ℝ → M}
    (hc : C.CausalCurveIn ⊤ univ c) {q : M} (hq : ∀ s, C.le ⊤ q (c s)) :
    C.Extensible ⊤ univ c :=
  (pastExtensible_of_forall_le hT hG hC hJm hc hq).extensible

/-- The extension step at the future end, one-sided: a causal curve over `ℝ` bounded above by a
point is extensible at the future end. -/
theorem futureExtensible_of_forall_ge [T2Space M] (hT : C.Tarentin) (hG : C.GloballyHyperbolic)
    (hC : C.CausallyArcConnected) (hJp : ∀ p : M, C.Jplus ⊤ {p} ≠ {p}) {c : ℝ → M}
    (hc : C.CausalCurveIn ⊤ univ c) {q : M} (hq : ∀ s, C.le ⊤ (c s) q) :
    C.FutureExtensible ⊤ univ c := by
  have hrev : C.dual.CausalCurveIn ⊤ univ (fun t => c (-t)) := by simpa using hc.reverse
  have h := pastExtensible_of_forall_le (C := C.dual) (dual_tarentin.2 hT)
    (dual_globallyHyperbolic.2 hG) (dual_causallyArcConnectedOn.2 hC) hJp hrev
    (q := q) fun s => hq (-s)
  exact FutureExtensible.of_dual_reverse (I := univ) (by simpa using h)

/-- The extension step, at the future end. -/
theorem extensible_of_forall_ge [T2Space M] (hT : C.Tarentin) (hG : C.GloballyHyperbolic)
    (hC : C.CausallyArcConnected) (hJp : ∀ p : M, C.Jplus ⊤ {p} ≠ {p}) {c : ℝ → M}
    (hc : C.CausalCurveIn ⊤ univ c) {q : M} (hq : ∀ s, C.le ⊤ (c s) q) :
    C.Extensible ⊤ univ c :=
  (futureExtensible_of_forall_ge hT hG hC hJp hc hq).extensible

/-! ### (ii) ⇒ (iii) -/

/-- (ii)⇒(iii), existence: `T⁻¹(0)` meets every inextensible causal curve **at least once**. -/
theorem IsCauchyTimeFunction.exists_mem_zero [T1Space M] (hC : C.CausallyArcConnected)
    (hSC : C.StronglyCausal) (hJm : ∀ p : M, C.Jminus ⊤ {p} ≠ {p})
    (hJp : ∀ p : M, C.Jplus ⊤ {p} ≠ {p}) {T : M → ℝ} (hT : C.IsCauchyTimeFunction T)
    {I : Set ℝ} {c : ℝ → M} (hc : C.Inextensible ⊤ I c) : ∃ x ∈ c '' I, T x = 0 := by
  obtain ⟨ψ, -, -, hψr, hcψ⟩ := hc.reparam hC hSC.isCausal hJm hJp
  obtain ⟨hbot, htop⟩ := hT.2 _ hcψ
  have hcont : Continuous (T ∘ (c ∘ ψ)) := hT.1.continuous.comp hcψ.1.continuous
  obtain ⟨s₁, hs₁⟩ := (hbot.eventually (eventually_le_atBot 0)).exists
  obtain ⟨s₂, hs₂⟩ := (htop.eventually (eventually_ge_atTop 0)).exists
  obtain ⟨s, hs⟩ := intermediate_value_univ s₁ s₂ hcont ⟨hs₁, hs₂⟩
  exact ⟨c (ψ s), ⟨ψ s, hψr ▸ mem_range_self s, rfl⟩, hs⟩

/-- **`theo:geroch`, (ii)⇒(iii)**, for a Cauchy time function strictly increasing along the causal
relation, as (ii) is ruled (DEC-15): `S = T⁻¹(0)` is a Cauchy surface. -/
theorem IsCauchyTimeFunction.isCauchySurface [T1Space M] (hC : C.CausallyArcConnected)
    (hSC : C.StronglyCausal) (hJm : ∀ p : M, C.Jminus ⊤ {p} ≠ {p})
    (hJp : ∀ p : M, C.Jplus ⊤ {p} ≠ {p}) {T : M → ℝ} (hT : C.IsCauchyTimeFunction T)
    (hstrict : ∀ x y, C.le ⊤ x y → x ≠ y → T x < T y) : C.IsCauchySurface (T ⁻¹' {0}) := by
  intro I c hc
  obtain ⟨x, hx, hx0⟩ := hT.exists_mem_zero hC hSC hJm hJp hc
  refine ⟨x, ⟨hx, hx0⟩, ?_⟩
  rintro y ⟨⟨t, ht, rfl⟩, hy0⟩
  obtain ⟨s, hs, rfl⟩ := hx
  have hy0' : T (c t) = 0 := hy0
  by_contra hne
  rcases le_total s t with h | h
  · have := hstrict _ _ (hc.1.le_of_le hs ht h) (Ne.symm hne)
    linarith
  · have := hstrict _ _ (hc.1.le_of_le ht hs h) hne
    linarith

/-- **`theo:geroch`, (ii)⇒(iii)** (DEC-15): a Cauchy time function strictly increasing along the
causal relation gives a Cauchy surface. -/
theorem geroch_ii_imp_iii [T1Space M] (hC : C.CausallyArcConnected) (hSC : C.StronglyCausal)
    (hJm : ∀ p : M, C.Jminus ⊤ {p} ≠ {p}) (hJp : ∀ p : M, C.Jplus ⊤ {p} ≠ {p})
    (h : ∃ T : M → ℝ, C.IsCauchyTimeFunction T ∧ ∀ x y, C.le ⊤ x y → x ≠ y → T x < T y) :
    ∃ S : Set M, C.IsCauchySurface S := by
  obtain ⟨T, hT, hstrict⟩ := h
  exact ⟨T ⁻¹' {0}, hT.isCauchySurface hC hSC hJm hJp hstrict⟩

/-! ### The time function `T = log(−t⁻/t⁺)` -/

variable [MeasurableSpace M]

/-- The function of the sketch of (i)⇒(ii): `T(x) = log(μ₋(J^-(x)) / μ₊(J^+(x)))`, that is
`log(−t⁻(x)/t⁺(x))` with `t⁺ = μ₊(J^+(·))` and `t⁻ = −μ₋(J^-(·))`. -/
noncomputable def gerochTime (C : Causality M) (μp μm : Measure M) (x : M) : ℝ :=
  Real.log ((μm (C.Jminus ⊤ {x})).toReal / (μp (C.Jplus ⊤ {x})).toReal)

variable {μp μm : Measure M}

/-- Past from future: the time function of the reversed causality, the measures exchanged, is
`−T`. -/
theorem gerochTime_dual (x : M) : gerochTime C.dual μm μp x = -gerochTime C μp μm x := by
  unfold gerochTime
  rw [← Real.log_inv, inv_div]
  rfl

/-- `t⁻` does not vanish: `μ₋(J^-(x)) > 0`, because `J^-(x) ≠ {x}`. -/
theorem toReal_measure_Jminus_pos (hμm : C.AdmissiblePast μm) (hJm : ∀ p : M, C.Jminus ⊤ {p} ≠ {p})
    (x : M) : 0 < (μm (C.Jminus ⊤ {x})).toReal := by
  obtain ⟨q, hqJ, hqne⟩ := exists_ne_of_ne_singleton
    (by simpa using C.le_refl (show x ∈ (⊤ : Opens M) from trivial) : x ∈ C.Jminus ⊤ {x}) (hJm x)
  have hq : C.le ⊤ q x := by simpa using hqJ
  have hpos := hμm.pos hq hqne
  refine ENNReal.toReal_pos (ne_of_gt (hpos.trans_le (measure_mono sdiff_subset))) ?_
  exact ne_of_lt ((measure_mono (subset_univ _)).trans_lt hμm.finite)

/-- `t⁺` does not vanish: `μ₊(J^+(x)) > 0`, because `J^+(x) ≠ {x}`. -/
theorem toReal_measure_Jplus_pos (hμp : C.AdmissibleFuture μp) (hJp : ∀ p : M, C.Jplus ⊤ {p} ≠ {p})
    (x : M) : 0 < (μp (C.Jplus ⊤ {x})).toReal :=
  toReal_measure_Jminus_pos (C := C.dual) (dual_admissiblePast.2 hμp) hJp x

/-- **`T` is strictly increasing along the causal relation**: `x ≤ y`, `x ≠ y` give
`T(x) < T(y)` (property 3. of both measures). -/
theorem gerochTime_lt [T2Space M] [BorelSpace M] (hμp : C.AdmissibleFuture μp)
    (hμm : C.AdmissiblePast μm) (hT : C.Tarentin) (hG : C.GloballyHyperbolic)
    (hJm : ∀ p : M, C.Jminus ⊤ {p} ≠ {p}) (hJp : ∀ p : M, C.Jplus ⊤ {p} ≠ {p}) {x y : M}
    (hxy : C.le ⊤ x y) (hne : x ≠ y) : gerochTime C μp μm x < gerochTime C μp μm y := by
  haveI : IsFiniteMeasure μp := ⟨hμp.finite⟩
  haveI : IsFiniteMeasure μm := ⟨hμm.finite⟩
  have ha := ENNReal.toReal_strict_mono (measure_ne_top _ _) (hμm.lt_of_le_of_ne hT hG hxy hne)
  have hb := ENNReal.toReal_strict_mono (measure_ne_top _ _) (hμp.lt_of_le_of_ne hT hG hxy hne)
  have hax := toReal_measure_Jminus_pos hμm hJm x
  have hay := toReal_measure_Jminus_pos hμm hJm y
  have hbx := toReal_measure_Jplus_pos hμp hJp x
  have hby := toReal_measure_Jplus_pos hμp hJp y
  unfold gerochTime
  apply Real.log_lt_log (div_pos hax hbx)
  calc (μm (C.Jminus ⊤ {x})).toReal / (μp (C.Jplus ⊤ {x})).toReal
      < (μm (C.Jminus ⊤ {y})).toReal / (μp (C.Jplus ⊤ {x})).toReal :=
        div_lt_div_of_pos_right ha hbx
    _ < (μm (C.Jminus ⊤ {y})).toReal / (μp (C.Jplus ⊤ {y})).toReal :=
        div_lt_div_of_pos_left hay hby hb

/-- `T` is non-decreasing along the causal relation. -/
theorem gerochTime_le [T2Space M] [BorelSpace M] (hμp : C.AdmissibleFuture μp)
    (hμm : C.AdmissiblePast μm) (hT : C.Tarentin) (hG : C.GloballyHyperbolic)
    (hJm : ∀ p : M, C.Jminus ⊤ {p} ≠ {p}) (hJp : ∀ p : M, C.Jplus ⊤ {p} ≠ {p}) {x y : M}
    (hxy : C.le ⊤ x y) : gerochTime C μp μm x ≤ gerochTime C μp μm y := by
  rcases eq_or_ne x y with h | h
  · rw [h]
  · exact (gerochTime_lt hμp hμm hT hG hJm hJp hxy h).le

/-- `T` is continuous (`prop:cont_ext_cont`). -/
theorem continuous_gerochTime [T2Space M] [FirstCountableTopology M] [BorelSpace M]
    (hμp : C.AdmissibleFuture μp) (hμm : C.AdmissiblePast μm) (hT : C.Tarentin)
    (hG : C.GloballyHyperbolic) (hJm : ∀ p : M, C.Jminus ⊤ {p} ≠ {p})
    (hJp : ∀ p : M, C.Jplus ⊤ {p} ≠ {p}) : Continuous (gerochTime C μp μm) := by
  haveI : IsFiniteMeasure μp := ⟨hμp.finite⟩
  haveI : IsFiniteMeasure μm := ⟨hμm.finite⟩
  have hA : Continuous fun x => (μm (C.Jminus ⊤ {x})).toReal :=
    ENNReal.continuousOn_toReal.comp_continuous (hμm.continuous_measure_Jminus hT hG)
      fun _ => measure_ne_top μm _
  have hB : Continuous fun x => (μp (C.Jplus ⊤ {x})).toReal :=
    ENNReal.continuousOn_toReal.comp_continuous (hμp.continuous_measure_Jplus hT hG)
      fun _ => measure_ne_top μp _
  exact (hA.div hB fun x => (toReal_measure_Jplus_pos hμp hJp x).ne').log fun x =>
    (div_pos (toReal_measure_Jminus_pos hμm hJm x) (toReal_measure_Jplus_pos hμp hJp x)).ne'

/-- **`T` is an open map** — the step the sketch omits, which DEC-10 requires. -/
theorem isOpenMap_gerochTime [T2Space M] [FirstCountableTopology M] [BorelSpace M]
    (hμp : C.AdmissibleFuture μp) (hμm : C.AdmissiblePast μm) (hT : C.Tarentin)
    (hG : C.GloballyHyperbolic) (hC : C.CausallyArcConnected)
    (hJm : ∀ p : M, C.Jminus ⊤ {p} ≠ {p}) (hJp : ∀ p : M, C.Jplus ⊤ {p} ≠ {p}) :
    IsOpenMap (gerochTime C μp μm) := by
  have hSC := hG.stronglyCausal hT
  have hcont := continuous_gerochTime hμp hμm hT hG hJm hJp
  intro O hO
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨x, hxO, rfl⟩
  obtain ⟨V, hV, hVO, hVc⟩ := hSC x O (hO.mem_nhds hxO)
  obtain ⟨p, hp, q, hq, hx⟩ := hT x V hV
  have hpq := mem_diamond.1 (openDiamond_subset_diamond hx)
  have hDn : C.openDiamond ⊤ p q ∈ 𝓝 x := isOpen_openDiamond.mem_nhds hx
  have hpx : p ≠ x := by
    rintro rfl
    exact Jplus_not_mem_nhds hC hG.1 (hJm p)
      (mem_of_superset hDn (openDiamond_subset_diamond.trans diamond_subset_Jplus))
  have hqx : q ≠ x := by
    rintro rfl
    exact Jplus_not_mem_nhds (C := C.dual) (dual_causallyArcConnectedOn.2 hC)
      (dual_isCausal.2 hG.1) (hJp q)
      (mem_of_superset hDn (openDiamond_subset_diamond.trans diamond_subset_Jminus))
  have h1 := gerochTime_lt hμp hμm hT hG hJm hJp hpq.1 hpx
  have h2 := gerochTime_lt hμp hμm hT hG hJm hJp hpq.2 (Ne.symm hqx)
  refine mem_of_superset (Ioo_mem_nhds h1 h2) fun z hz => ?_
  obtain ⟨γ, hγ, hγ0, hγ1⟩ := (hC ⊤ le_rfl p q).1.1 (C.le_trans hpq.1 hpq.2)
  have hγc : ContinuousOn (gerochTime C μp μm ∘ γ) (Icc 0 1) :=
    hcont.comp_continuousOn (hγ.continuousOn C.isRelFamily_le)
  obtain ⟨s, hs, hsz⟩ := intermediate_value_Icc zero_le_one hγc
    (by simp only [Function.comp, hγ0, hγ1]; exact ⟨hz.1.le, hz.2.le⟩)
  refine ⟨γ s, hVO (hVc.2 p hp q hq (mem_diamond.2 ⟨?_, ?_⟩)), hsz⟩
  · rw [← hγ0]; exact hγ.le_of_le le_rfl hs.1 hs.2
  · rw [← hγ1]; exact hγ.le_of_le hs.1 hs.2 le_rfl

/-- **`T` is a time function** (DEC-10). -/
theorem isTimeFunction_gerochTime [T2Space M] [FirstCountableTopology M] [BorelSpace M]
    (hμp : C.AdmissibleFuture μp) (hμm : C.AdmissiblePast μm) (hT : C.Tarentin)
    (hG : C.GloballyHyperbolic) (hC : C.CausallyArcConnected)
    (hJm : ∀ p : M, C.Jminus ⊤ {p} ≠ {p}) (hJp : ∀ p : M, C.Jplus ⊤ {p} ≠ {p}) :
    C.IsTimeFunction (gerochTime C μp μm) := by
  rw [isTimeFunction_iff_order hC, isTimeFunctionOrder_iff]
  exact ⟨continuous_gerochTime hμp hμm hT hG hJm hJp,
    isOpenMap_gerochTime hμp hμm hT hG hC hJm hJp,
    fun _ _ hxy => gerochTime_le hμp hμm hT hG hJm hJp hxy,
    fun _ _ hxy => gerochTime_lt hμp hμm hT hG hJm hJp (C.le_of_lt hxy)
      (ne_of_lt_top hC hG.1 hJm hxy)⟩

/-- The measure step of (i)⇒(ii): along a causal curve over `ℝ` on which `T` is bounded below,
`μ₋(⋂ₙ J^-(c(−n))) > 0`, so a point `q` lies below the whole curve. -/
theorem exists_le_of_bddBelow [T2Space M] [BorelSpace M] (hμp : C.AdmissibleFuture μp)
    (hμm : C.AdmissiblePast μm) (hT : C.Tarentin) (hG : C.GloballyHyperbolic)
    (hJm : ∀ p : M, C.Jminus ⊤ {p} ≠ {p}) (hJp : ∀ p : M, C.Jplus ⊤ {p} ≠ {p}) {c : ℝ → M}
    (hc : C.CausalCurveIn ⊤ univ c) {L : ℝ} (hL : ∀ s, L < gerochTime C μp μm (c s)) :
    ∃ q, ∀ s, C.le ⊤ q (c s) := by
  haveI : IsFiniteMeasure μp := ⟨hμp.finite⟩
  haveI : IsFiniteMeasure μm := ⟨hμm.finite⟩
  have hmono : ∀ s s', s ≤ s' → C.le ⊤ (c s) (c s') := fun s s' h =>
    hc.le_of_le trivial trivial h
  set l := Real.exp L * (μp (C.Jplus ⊤ {c 0})).toReal with hl_def
  have hl : 0 < l := mul_pos (Real.exp_pos L) (toReal_measure_Jplus_pos hμp hJp _)
  have hbound : ∀ s ≤ 0, l ≤ (μm (C.Jminus ⊤ {c s})).toReal := by
    intro s hs
    have hbs := toReal_measure_Jplus_pos hμp hJp (c s)
    have h1 : Real.exp L < (μm (C.Jminus ⊤ {c s})).toReal / (μp (C.Jplus ⊤ {c s})).toReal := by
      have := hL s
      unfold gerochTime at this
      exact (Real.lt_log_iff_exp_lt (div_pos (toReal_measure_Jminus_pos hμm hJm _) hbs)).1 this
    rw [lt_div_iff₀ hbs] at h1
    have h2 : (μp (C.Jplus ⊤ {c 0})).toReal ≤ (μp (C.Jplus ⊤ {c s})).toReal :=
      ENNReal.toReal_mono (measure_ne_top _ _)
        (measure_mono (Precausality.Jplus_singleton_subset (hmono s 0 hs)))
    calc l ≤ Real.exp L * (μp (C.Jplus ⊤ {c s})).toReal :=
          mul_le_mul_of_nonneg_left h2 (Real.exp_pos L).le
      _ ≤ _ := h1.le
  set E : ℕ → Set M := fun n => C.Jminus ⊤ {c (-(n : ℝ))} with hE
  have hanti : Antitone E := fun n n' h =>
    Precausality.Jminus_singleton_subset (hmono _ _ (by
      have : (n : ℝ) ≤ n' := by exact_mod_cast h
      linarith))
  have hmeas : ∀ n, NullMeasurableSet (E n) μm := fun n =>
    (hG.isClosed_Jminus_singleton hT _).measurableSet.nullMeasurableSet
  have hinter := hanti.measure_iInter hmeas ⟨0, measure_ne_top _ _⟩
  have hpos : μm (⋂ n, E n) ≠ 0 := by
    rw [hinter]
    refine (lt_of_lt_of_le (ENNReal.ofReal_pos.2 hl) (le_iInf fun n => ?_)).ne'
    rw [ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)]
    exact hbound _ (by simp)
  obtain ⟨q, hq⟩ := nonempty_of_measure_ne_zero hpos
  refine ⟨q, fun s => ?_⟩
  obtain ⟨n, hn⟩ := exists_nat_ge (-s)
  have hqn : C.le ⊤ q (c (-(n : ℝ))) := by simpa [hE] using mem_iInter.1 hq n
  exact C.le_trans hqn (hmono _ _ (by linarith))

/-- (i)⇒(ii), the past end, as the sketch has it (`ETT.tex:1295`, DEC-13): along a
**past-inextensible** causal curve over `ℝ`, `T → −∞` at `−∞`. -/
theorem tendsto_atBot_gerochTime_of_pastInextensible [T2Space M] [BorelSpace M]
    (hμp : C.AdmissibleFuture μp) (hμm : C.AdmissiblePast μm) (hT : C.Tarentin)
    (hG : C.GloballyHyperbolic) (hC : C.CausallyArcConnected)
    (hJm : ∀ p : M, C.Jminus ⊤ {p} ≠ {p}) (hJp : ∀ p : M, C.Jplus ⊤ {p} ≠ {p}) {c : ℝ → M}
    (hc : C.PastInextensible ⊤ univ c) : Tendsto (gerochTime C μp μm ∘ c) atBot atBot := by
  have hmono : Monotone (gerochTime C μp μm ∘ c) := fun s s' h =>
    gerochTime_le hμp hμm hT hG hJm hJp (hc.1.le_of_le trivial trivial h)
  by_contra h
  have hbdd : ∃ L, ∀ s, L < gerochTime C μp μm (c s) := by
    by_contra h'
    simp only [not_exists, not_forall, not_lt] at h'
    exact h (tendsto_atBot_atBot_of_monotone hmono h')
  obtain ⟨L, hL⟩ := hbdd
  obtain ⟨q, hq⟩ := exists_le_of_bddBelow hμp hμm hT hG hJm hJp hc.1 hL
  exact hc.2 (pastExtensible_of_forall_le hT hG hC hJm hc.1 hq)

/-- (i)⇒(ii), the future end, as the sketch has it (`ETT.tex:1296`, DEC-13): along a
**future-inextensible** causal curve over `ℝ`, `T → +∞` at `+∞`. By time reversal. -/
theorem tendsto_atTop_gerochTime_of_futureInextensible [T2Space M] [BorelSpace M]
    (hμp : C.AdmissibleFuture μp) (hμm : C.AdmissiblePast μm) (hT : C.Tarentin)
    (hG : C.GloballyHyperbolic) (hC : C.CausallyArcConnected)
    (hJm : ∀ p : M, C.Jminus ⊤ {p} ≠ {p}) (hJp : ∀ p : M, C.Jplus ⊤ {p} ≠ {p}) {c : ℝ → M}
    (hc : C.FutureInextensible ⊤ univ c) : Tendsto (gerochTime C μp μm ∘ c) atTop atTop := by
  have hrev : C.dual.PastInextensible ⊤ univ (fun t => c (-t)) := by
    simpa using dual_pastInextensible_iff.2 hc
  have h1 := tendsto_atBot_gerochTime_of_pastInextensible (C := C.dual) (μp := μm) (μm := μp)
    (dual_admissibleFuture.2 hμm) (dual_admissiblePast.2 hμp) (dual_tarentin.2 hT)
    (dual_globallyHyperbolic.2 hG) (dual_causallyArcConnectedOn.2 hC) hJp hJm hrev
  have h2' : Tendsto (fun t => -gerochTime C μp μm (c (-t))) atBot atBot :=
    h1.congr fun t => gerochTime_dual (c (-t))
  have h2 : Tendsto (fun t => gerochTime C μp μm (c (-t))) atBot atTop :=
    tendsto_neg_atBot_iff.1 h2'
  have h3 := h2.comp tendsto_neg_atTop_atBot
  refine h3.congr fun u => ?_
  simp [Function.comp]

/-- (i)⇒(ii), the past end: along an inextensible causal curve over `ℝ`, `T → −∞` at `−∞`. -/
theorem tendsto_atBot_gerochTime [T2Space M] [BorelSpace M] (hμp : C.AdmissibleFuture μp)
    (hμm : C.AdmissiblePast μm) (hT : C.Tarentin) (hG : C.GloballyHyperbolic)
    (hC : C.CausallyArcConnected) (hJm : ∀ p : M, C.Jminus ⊤ {p} ≠ {p})
    (hJp : ∀ p : M, C.Jplus ⊤ {p} ≠ {p}) {c : ℝ → M} (hc : C.Inextensible ⊤ univ c) :
    Tendsto (gerochTime C μp μm ∘ c) atBot atBot :=
  tendsto_atBot_gerochTime_of_pastInextensible hμp hμm hT hG hC hJm hJp
    (inextensible_iff.1 hc).1

/-- (i)⇒(ii), the future end. -/
theorem tendsto_atTop_gerochTime [T2Space M] [BorelSpace M] (hμp : C.AdmissibleFuture μp)
    (hμm : C.AdmissiblePast μm) (hT : C.Tarentin) (hG : C.GloballyHyperbolic)
    (hC : C.CausallyArcConnected) (hJm : ∀ p : M, C.Jminus ⊤ {p} ≠ {p})
    (hJp : ∀ p : M, C.Jplus ⊤ {p} ≠ {p}) {c : ℝ → M} (hc : C.Inextensible ⊤ univ c) :
    Tendsto (gerochTime C μp μm ∘ c) atTop atTop :=
  tendsto_atTop_gerochTime_of_futureInextensible hμp hμm hT hG hC hJm hJp
    (inextensible_iff.1 hc).2

/-- **`theo:geroch`, (i)⇒(ii)**: `T = log(−t⁻/t⁺)` is a Cauchy time function. -/
theorem GloballyHyperbolic.isCauchyTimeFunction_gerochTime [T2Space M]
    [FirstCountableTopology M] [BorelSpace M] (hμp : C.AdmissibleFuture μp)
    (hμm : C.AdmissiblePast μm) (hT : C.Tarentin) (hC : C.CausallyArcConnected)
    (hJm : ∀ p : M, C.Jminus ⊤ {p} ≠ {p}) (hJp : ∀ p : M, C.Jplus ⊤ {p} ≠ {p})
    (hG : C.GloballyHyperbolic) : C.IsCauchyTimeFunction (gerochTime C μp μm) :=
  ⟨isTimeFunction_gerochTime hμp hμm hT hG hC hJm hJp, fun _ hc =>
    ⟨tendsto_atBot_gerochTime hμp hμm hT hG hC hJm hJp hc,
      tendsto_atTop_gerochTime hμp hμm hT hG hC hJm hJp hc⟩⟩

/-- **`theo:geroch`, (i)⇒(ii)**, with the strict monotonicity the construction gives. -/
theorem geroch_i_imp_ii [T2Space M] [FirstCountableTopology M] [BorelSpace M]
    (hμp : C.AdmissibleFuture μp) (hμm : C.AdmissiblePast μm) (hT : C.Tarentin)
    (hC : C.CausallyArcConnected) (hJm : ∀ p : M, C.Jminus ⊤ {p} ≠ {p})
    (hJp : ∀ p : M, C.Jplus ⊤ {p} ≠ {p}) (hG : C.GloballyHyperbolic) :
    ∃ T : M → ℝ, C.IsCauchyTimeFunction T ∧ ∀ x y, C.le ⊤ x y → x ≠ y → T x < T y :=
  ⟨gerochTime C μp μm, hG.isCauchyTimeFunction_gerochTime hμp hμm hT hC hJm hJp,
    fun _ _ hxy hne => gerochTime_lt hμp hμm hT hG hJm hJp hxy hne⟩

/-- **(i)⇒(iii)**, with `S = T⁻¹(0)` for `T = log(−t⁻/t⁺)`, under the hypotheses of
`theo:geroch` (metrizability read as `T2` and first countability; local compactness and strong
causality not used). -/
theorem geroch_i_imp_iii [T2Space M] [FirstCountableTopology M] [BorelSpace M]
    (hμp : C.AdmissibleFuture μp) (hμm : C.AdmissiblePast μm) (hT : C.Tarentin)
    (hC : C.CausallyArcConnected) (hJm : ∀ p : M, C.Jminus ⊤ {p} ≠ {p})
    (hJp : ∀ p : M, C.Jplus ⊤ {p} ≠ {p}) (hG : C.GloballyHyperbolic) :
    C.IsCauchySurface (gerochTime C μp μm ⁻¹' {0}) :=
  (hG.isCauchyTimeFunction_gerochTime hμp hμm hT hC hJm hJp).isCauchySurface hC
    (hG.stronglyCausal hT) hJm hJp fun _ _ hxy hne => gerochTime_lt hμp hμm hT hG hJm hJp hxy hne

end Causality

/-! ### Witnesses on the timelike line -/

theorem timelikeLine_Jminus_ne (p : ℝ) : timelikeLine.Jminus ⊤ {p} ≠ {p} := by
  intro h
  have : p - 1 ∈ timelikeLine.Jminus ⊤ {p} := by
    simp only [Precausality.mem_Jminus_singleton, timelikeLine_le]
    exact ⟨by linarith, fun _ _ => trivial⟩
  rw [h] at this
  have : p - 1 = p := this
  linarith

theorem timelikeLine_Jplus_ne (p : ℝ) : timelikeLine.Jplus ⊤ {p} ≠ {p} := by
  intro h
  have : p + 1 ∈ timelikeLine.Jplus ⊤ {p} := by
    simp only [Precausality.mem_Jplus_singleton, timelikeLine_le]
    exact ⟨by linarith, fun _ _ => trivial⟩
  rw [h] at this
  have : p + 1 = p := this
  linarith

/-- **Witness.** On the timelike line the identity is a Cauchy time function. -/
theorem timelikeLine_isCauchyTimeFunction_id : timelikeLine.IsCauchyTimeFunction id := by
  refine ⟨timelikeLine_isTimeFunction_id, fun c hc => ⟨?_, ?_⟩⟩
  · have hmono : Monotone (id ∘ c) := fun s s' h =>
      (timelikeLine_le.1 (hc.1.le_of_le trivial trivial h)).1
    by_contra h
    have hbdd : ∃ L, ∀ s, L < c s := by
      by_contra h'
      simp only [not_exists, not_forall, not_lt] at h'
      exact h (tendsto_atBot_atBot_of_monotone hmono h')
    obtain ⟨L, hL⟩ := hbdd
    exact hc.2 (Causality.extensible_of_forall_le timelikeLine_tarentin
      timelikeLine_globallyHyperbolic timelikeLine_causallyArcConnected timelikeLine_Jminus_ne
      hc.1 (q := L) fun s => timelikeLine_le.2 ⟨(hL s).le, fun _ _ => trivial⟩)
  · have hmono : Monotone (id ∘ c) := fun s s' h =>
      (timelikeLine_le.1 (hc.1.le_of_le trivial trivial h)).1
    by_contra h
    have hbdd : ∃ L, ∀ s, c s < L := by
      by_contra h'
      simp only [not_exists, not_forall, not_lt] at h'
      exact h (tendsto_atTop_atTop_of_monotone hmono h')
    obtain ⟨L, hL⟩ := hbdd
    exact hc.2 (Causality.extensible_of_forall_ge timelikeLine_tarentin
      timelikeLine_globallyHyperbolic timelikeLine_causallyArcConnected timelikeLine_Jplus_ne
      hc.1 (q := L) fun s => timelikeLine_le.2 ⟨(hL s).le, fun _ _ => trivial⟩)

/-- **Witness.** On the timelike line `{0}` is a Cauchy surface: `(ii)⇒(iii)` applied to `id`. -/
theorem timelikeLine_isCauchySurface_zero : timelikeLine.IsCauchySurface ({0} : Set ℝ) := by
  have := timelikeLine_isCauchyTimeFunction_id.isCauchySurface
    timelikeLine_causallyArcConnected timelikeLine_stronglyCausal timelikeLine_Jminus_ne
    timelikeLine_Jplus_ne fun x y hxy hne => lt_of_le_of_ne (timelikeLine_le.1 hxy).1 hne
  simpa using this

/-! ### The hypotheses of (i)⇒(ii) are satisfiable: the timelike line with a Gaussian measure -/

section Witness

open Causality

theorem timelikeLine_Jminus_top_singleton (a : ℝ) : timelikeLine.Jminus ⊤ {a} = Iic a := by
  ext x; simp [timelikeLine_le]

theorem timelikeLine_Jplus_top_singleton (a : ℝ) : timelikeLine.Jplus ⊤ {a} = Ici a := by
  ext x; simp [timelikeLine_le]

/-- On the timelike line, `]-∞, a[ ⊂ K^-(a)`. -/
theorem timelikeLine_mem_Kminus_of_lt {y a : ℝ} (h : y < a) : y ∈ timelikeLine.Kminus ⊤ {a} := by
  rw [mem_Kminus_singleton]
  intro u hu
  set m := (y + a) / 2
  have hm : m < a := by simp only [m]; linarith
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hu.eventually (Ioi_mem_nhds hm))
  refine ⟨N, ?_⟩
  rw [mem_interiorWithin]
  refine ⟨by rw [timelikeLine_Jminus_top_singleton]; exact h.le, mem_nhdsWithin.2 ⟨Iio m,
    isOpen_Iio, (by simp only [m, mem_Iio]; linarith), fun z hz => ⟨hz.2, ?_⟩⟩⟩
  simp only [mem_iInter]
  intro n hn
  rw [timelikeLine_Jminus_top_singleton]
  exact le_of_lt (lt_trans hz.1 (hN n hn))

/-- On the timelike line, `]a, +∞[ ⊂ K^+(a)`. -/
theorem timelikeLine_mem_Kplus_of_lt {y a : ℝ} (h : a < y) : y ∈ timelikeLine.Kplus ⊤ {a} := by
  rw [mem_Kplus_singleton]
  intro u hu
  set m := (y + a) / 2
  have hm : a < m := by simp only [m]; linarith
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hu.eventually (Iio_mem_nhds hm))
  refine ⟨N, ?_⟩
  rw [mem_interiorWithin]
  refine ⟨by rw [timelikeLine_Jplus_top_singleton]; exact h.le, mem_nhdsWithin.2 ⟨Ioi m,
    isOpen_Ioi, (by simp only [m, mem_Ioi]; linarith), fun z hz => ⟨hz.2, ?_⟩⟩⟩
  simp only [mem_iInter]
  intro n hn
  rw [timelikeLine_Jplus_top_singleton]
  exact le_of_lt (lt_trans (hN n hn) hz.1)

theorem timelikeLine_Jminus_diff_Kminus_subsingleton (A : Set ℝ) :
    (timelikeLine.Jminus ⊤ A \ timelikeLine.Kminus ⊤ A).Subsingleton := by
  have key : ∀ y ∈ timelikeLine.Jminus ⊤ A \ timelikeLine.Kminus ⊤ A,
      y ∈ A ∧ ∀ a ∈ A, a ≤ y := by
    rintro y ⟨⟨a, ha, hya⟩, hyK⟩
    have hall : ∀ a ∈ A, a ≤ y := by
      intro a ha
      by_contra h
      apply hyK
      rw [Kminus_eq_biUnion]
      exact mem_iUnion₂.2 ⟨a, ha, timelikeLine_mem_Kminus_of_lt (not_le.1 h)⟩
    have hy : y = a := le_antisymm (timelikeLine_le.1 hya).1 (hall a ha)
    exact ⟨hy ▸ ha, hall⟩
  intro y hy y' hy'
  obtain ⟨hyA, hy⟩ := key y hy
  obtain ⟨hy'A, hy'⟩ := key y' hy'
  exact le_antisymm (hy' y hyA) (hy y' hy'A)

theorem timelikeLine_Jplus_diff_Kplus_subsingleton (A : Set ℝ) :
    (timelikeLine.Jplus ⊤ A \ timelikeLine.Kplus ⊤ A).Subsingleton := by
  have key : ∀ y ∈ timelikeLine.Jplus ⊤ A \ timelikeLine.Kplus ⊤ A,
      y ∈ A ∧ ∀ a ∈ A, y ≤ a := by
    rintro y ⟨⟨a, ha, hay⟩, hyK⟩
    have hall : ∀ a ∈ A, y ≤ a := by
      intro a ha
      by_contra h
      apply hyK
      rw [Kplus_eq_biUnion]
      exact mem_iUnion₂.2 ⟨a, ha, timelikeLine_mem_Kplus_of_lt (not_le.1 h)⟩
    have hy : y = a := le_antisymm (hall a ha) (timelikeLine_le.1 hay).1
    exact ⟨hy ▸ ha, hall⟩
  intro y hy y' hy'
  obtain ⟨hyA, hy⟩ := key y hy
  obtain ⟨hy'A, hy'⟩ := key y' hy'
  exact le_antisymm (hy y' hy'A) (hy' y hyA)

/-- **Witness.** On the timelike line the standard Gaussian measure is admissible in the past and
in the future. -/
theorem timelikeLine_admissible_past_and_future :
    timelikeLine.AdmissiblePast (ProbabilityTheory.gaussianReal 0 1) ∧
      timelikeLine.AdmissibleFuture (ProbabilityTheory.gaussianReal 0 1) := by
  haveI := ProbabilityTheory.noAtoms_gaussianReal (μ := 0) (v := 1) one_ne_zero
  refine ⟨⟨inferInstance, measure_lt_top _ _, fun p q hpq hne => ?_, fun A => ?_⟩,
    ⟨inferInstance, measure_lt_top _ _, fun p q hpq hne => ?_, fun A => ?_⟩⟩
  · have hlt : p < q := lt_of_le_of_ne (timelikeLine_le.1 hpq).1 hne
    refine (gaussianReal_Ioo_pos hlt).trans_le (measure_mono fun x hx => ?_)
    rw [timelikeLine_Jminus_top_singleton, timelikeLine_Jminus_top_singleton]
    exact ⟨hx.2.le, fun h => absurd hx.1 (not_lt.2 h)⟩
  · exact (timelikeLine_Jminus_diff_Kminus_subsingleton A).countable.measure_zero _
  · have hlt : p < q := lt_of_le_of_ne (timelikeLine_le.1 hpq).1 hne
    refine (gaussianReal_Ioo_pos hlt).trans_le (measure_mono fun x hx => ?_)
    rw [timelikeLine_Jplus_top_singleton, timelikeLine_Jplus_top_singleton]
    exact ⟨hx.1.le, fun h => absurd hx.2 (not_lt.2 h)⟩
  · exact (timelikeLine_Jplus_diff_Kplus_subsingleton A).countable.measure_zero _

/-- **Witness: the hypotheses of `geroch_i_imp_ii` are jointly satisfiable**, and on the timelike
line it gives a Cauchy time function strictly increasing along `≤`. -/
theorem timelikeLine_exists_strict_isCauchyTimeFunction :
    ∃ T : ℝ → ℝ, timelikeLine.IsCauchyTimeFunction T ∧
      ∀ x y, timelikeLine.le ⊤ x y → x ≠ y → T x < T y :=
  geroch_i_imp_ii timelikeLine_admissible_past_and_future.2
    timelikeLine_admissible_past_and_future.1 timelikeLine_tarentin
    timelikeLine_causallyArcConnected timelikeLine_Jminus_ne timelikeLine_Jplus_ne
    timelikeLine_globallyHyperbolic

end Witness

end Causal
