import BenzecriScaffold.Cone.Section
import Mathlib.Analysis.Normed.Module.Connected

/-!
# `BenzecriScaffold.Cone.Counterexample` — an affine conical manifold whose base is not Hausdorff (DEC-122)

J.-P. Benzécri, *Sur les variétés localement affines et localement projectives*, Bull. SMF 88
(1960) 229–332, Chapter 1 § 2, journal pp. 240–241; transcription
`papers/benzecri/legacy/labeled/benzecri1960_ch1.tex`. Package WP-45p (wave-3 fix round). The
construction is the wave-3 audit's (`campaign/WP-45n/AUDIT-1.json`, check `B_hausdorff`), ruled a
FINDING by the author (DEC-122). No label is marked here: the marks are on the corrected forms.

THE FINDING (DEC-122), for Benzécri's dimension `n = 3` (Lean's `ConeBase 2 V`, `V` charted on
`RnO (2 + 1) = ℝ³ − {O}`):

* `W = {(x, y, z) : z > 0, (x, y) ≠ (0, 0)}` (`ConeCex.W`), an open cone, and
  `A = diag(4, 1/8, 2) ∈ GU(3)` (`ConeCex.A 1`; `ConeCex.A k` is `A^k`). The `ℤ`-action
  `k · v = A^k v` on `W` is free and properly discontinuous (`A^k` multiplies `z` by `2^k`).
* `V = W/⟨A⟩` (`ConeCex.V`) is Hausdorff, second countable, connected and paracompact, with an
  affine conical structure whose cone charts are `f_N = (π|N)⁻¹` on the cones
  `N(i, r) = {r z < |v_i| < 2 r z}` (`ConeCex.chart`) and whose transitions are the `A^k`
  (`ConeCex.chart_transition`): `[ChartedSpace] [HasGroupoid V (coneGroupoid 3)]
  [HasConeCharts 3 V] [T2Space V]`. Its positive homotheties are those of `W`
  (`ConeCex.posSMul_π'`).
* **The base `B = V/ℝ⁺` is NOT Hausdorff** (`ConeCex.not_t2Space_coneBase`): `[(1,0)]` and
  `[(0,1)]` are inseparable, since `y_k = π(1, 16^{-k}, 1) → π(1, 0, 1)` while
  `2^k · y_k = π(2^{-k}, 1, 1) → π(0, 1, 1)`.
* Consequences, each the refutation of a `Prop` holding the printed statement (kb/0022):
  - `bzprop:c1s2p2_base_cone` — `benzecri1960_ch1.tex:540` (§ 2 Prop. 2, l.540–546, p. 240), read
    with a « variété » base (plan F6): `ConeCex.Prop2HausdorffBaseAsRead`,
    `ConeCex.not_prop2HausdorffBaseAsRead`;
  - `bzdef:c1s2d3_homotheties_positives` — `benzecri1960_ch1.tex:526` (Déf. 3, l.526–538,
    p. 240), « cet espace fibré est topologiquement trivial »: `ConeCex.Def3TrivialAsPrinted`,
    `ConeCex.not_def3TrivialAsPrinted` (indeed `V` is homeomorphic to `B × ℝ₊*` by no
    homeomorphism at all, `ConeCex.isEmpty_homeomorph`);
  - the p. 241 prose — `benzecri1960_ch1.tex:549` (l.549–552, no label), « si $V$ est supposé
    para-compact, on peut donc construire une section »: `ConeCex.P241SectionAsPrinted`,
    `ConeCex.not_p241SectionAsPrinted` (`V` is paracompact; `ConeCex.not_exists_section`).
  - The action of `ℝ₊*` is not proper (`ConeCex.not_properSMul`).
  The whole construction in one statement: `ConeCex.counterexample`.

The corrected forms (DEC-122: add « the action of `ℝ₊*` is proper », equivalently `B` Hausdorff,
`ConeBase.t2Space_iff_properSMul`) are `ConeBase.existsUnique_baseStructure_of_properSMul`
(`Cone/Base`), `ConeBase.exists_trivialization_of_properSMul` and
`ConeBase.exists_section_of_properSMul` (`Cone/Section`); in dimension `n ≤ 2` no hypothesis is
needed (`Cone/LowDim`).

> **Prop. 2.** Sur le quotient $B=V/\R^+$, appelé *base* de l'espace fibré $V$, est définie
> canoniquement une structure localement projective […]
>
> (Déf. 3) $V$ est ainsi munie d'une structure d'espace fibré $\R^+$-principal : cet espace fibré
> est topologiquement trivial, puisque $\R^+$ est homéomorphe au segment ouvert, et nous en
> construirons plus loin une section.
>
> Tout fibré localement trivial, dont la fibre est contractile, et dont la base est un espace
> normal, à base dénombrable d'ouverts, possède une section; si $V$ est supposé para-compact, on
> peut donc construire une section de $V$ au-desus de $B$.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `V` an affine conical manifold of dimension 3 (Déf. 2, with 3°) | ✓ proved for `V`: cone charts `f_N` onto the open cones `N(i, r)`, transitions `A^k ∈ GU(3)` |
| `V` a « variété »: Hausdorff, second countable, connected (plan F6) | ✓ proved: `T2Space V` (Mathlib, properly discontinuous action), `SecondCountableTopology V`, `ConnectedSpace V`; also `ParacompactSpace V` |
| « $V$ para-compact » (p. 241) | ✓ proved |
| `B` a « variété » (Prop. 2 read with plan F6) | ✗ refuted: `B` is not Hausdorff |

## SCOPE (disclosed)

* Only Benzécri's dimension `n = 3` is formalized (DEC-122 asks for `n = 3`). For `n ≥ 3` the
  audit's `diag(4, 1/8, 2, 1, …, 1)` on `{v₃ > 0, (v₁, v₂) ≠ 0}` works the same way (not
  formalized). For `n ≤ 2` the base is always Hausdorff (`Cone/LowDim`).
* `A` fixes no ray of `W` (every eigenline of `A` meets `W` in nothing); the proof does not need
  this fact separately: it is what makes the `N(i, r)` disjoint from their translates
  (`ConeCex.eq_zero_of_mem_N`).
* The instances on `V` are stated over `RnO (2 + 1)`, `coneGroupoid (2 + 1)` and
  `HasConeCharts (2 + 1)`, the syntactic form `ConeBase 2 V` asks for (instance search does not
  identify `2 + 1` with `3`). All instances are on this file's own types `ConeCex.Dom` and
  `ConeCex.V`; `locallyCompactSpace_RnO3` is a theorem, not an instance.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

noncomputable section

open Set Filter Topology

namespace Benzecri

namespace ConeCex

/-- The diagonal of `A^k = diag(4, 1/8, 2)^k`. -/
def dg (k : ℤ) : Fin 3 → ℝ := ![(4 : ℝ) ^ k, (8 : ℝ) ^ (-k), (2 : ℝ) ^ k]

@[simp] theorem dg_zero' (k : ℤ) : dg k 0 = (4 : ℝ) ^ k := rfl
@[simp] theorem dg_one' (k : ℤ) : dg k 1 = (8 : ℝ) ^ (-k) := rfl
@[simp] theorem dg_two' (k : ℤ) : dg k 2 = (2 : ℝ) ^ k := rfl

theorem dg_pos (k : ℤ) (i : Fin 3) : 0 < dg k i := by
  fin_cases i <;> simp [dg] <;> positivity

theorem dg_add (k l : ℤ) (i : Fin 3) : dg (k + l) i = dg k i * dg l i := by
  fin_cases i <;> simp [dg, zpow_add₀, mul_comm]

theorem dg_zero (i : Fin 3) : dg 0 i = 1 := by
  fin_cases i <;> simp [dg]

theorem prod_dg (k : ℤ) : ∏ i, dg k i = 1 := by
  rw [Fin.prod_univ_three]
  simp only [dg_zero', dg_one', dg_two', zpow_neg]
  have h : (4 : ℝ) ^ k * (2 : ℝ) ^ k = (8 : ℝ) ^ k := by
    rw [← mul_zpow]; norm_num
  have h8 : (8 : ℝ) ^ k ≠ 0 := by positivity
  calc (4 : ℝ) ^ k * ((8 : ℝ) ^ k)⁻¹ * 2 ^ k = (4 ^ k * 2 ^ k) * ((8 : ℝ) ^ k)⁻¹ := by ring
    _ = 1 := by rw [h, mul_inv_cancel₀ h8]

/-- The linear map `diag(dg k)`. -/
def dgLin (k : ℤ) : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) := Matrix.toLin' (Matrix.diagonal (dg k))

theorem dgLin_apply (k : ℤ) (v : Fin 3 → ℝ) (i : Fin 3) : dgLin k v i = dg k i * v i := by
  simp [dgLin, Matrix.toLin'_apply, Matrix.mulVec_diagonal]

/-- `A^k` as a linear automorphism of `ℝ³`. -/
def Alin (k : ℤ) : GLR 3 :=
  LinearEquiv.ofLinear (dgLin k) (dgLin (-k))
    (by ext v i; simp [dgLin_apply, ← mul_assoc, ← dg_add, dg_zero])
    (by ext v i; simp [dgLin_apply, ← mul_assoc, ← dg_add, dg_zero])

theorem Alin_apply (k : ℤ) (v : Fin 3 → ℝ) (i : Fin 3) : Alin k v i = dg k i * v i :=
  dgLin_apply k v i

/-- **`A^k ∈ GU(3)`** (`det A = 4 · 1/8 · 2 = 1`). -/
def A (k : ℤ) : GUR 3 :=
  ⟨Alin k, by
    rw [mem_GU, LinearEquiv.coe_det]
    show |LinearMap.det (dgLin k)| = 1
    rw [dgLin, LinearMap.det_toLin', Matrix.det_diagonal, prod_dg, abs_one]⟩

@[simp] theorem A_val (k : ℤ) (v : RnO 3) (i : Fin 3) : (A k • v).val i = dg k i * v.val i :=
  Alin_apply k v.val i


/-! ### The open cone `W` and the action of `ℤ` -/

/-- **The open cone `W = {(x, y, z) : z > 0, (x, y) ≠ (0, 0)}`** of `ℝ³ − {O}`. -/
def W : Set (RnO 3) := {v | 0 < v.val 2 ∧ (v.val 0 ≠ 0 ∨ v.val 1 ≠ 0)}

theorem isOpen_W : IsOpen W := by
  have hc : ∀ i : Fin 3, Continuous fun v : RnO 3 => v.val i := fun i =>
    (continuous_apply i).comp Punctured.continuous_val
  exact (isOpen_lt continuous_const (hc 2)).inter
    ((isOpen_ne_fun (hc 0) continuous_const).union (isOpen_ne_fun (hc 1) continuous_const))

theorem A_mem_W (k : ℤ) {v : RnO 3} (hv : v ∈ W) : A k • v ∈ W := by
  obtain ⟨hz, hxy⟩ := hv
  refine ⟨by rw [A_val]; exact mul_pos (dg_pos k 2) hz, ?_⟩
  simp only [A_val]
  rcases hxy with h | h
  · exact Or.inl (mul_ne_zero (dg_pos k 0).ne' h)
  · exact Or.inr (mul_ne_zero (dg_pos k 1).ne' h)

theorem smul_mem_W (c : RPos) {v : RnO 3} (hv : v ∈ W) : c • v ∈ W := by
  obtain ⟨hz, hxy⟩ := hv
  have hc := Punctured.pos c
  refine ⟨by simpa using mul_pos hc hz, ?_⟩
  simp only [Punctured.val_smul_pos, Pi.smul_apply, smul_eq_mul]
  rcases hxy with h | h
  · exact Or.inl (mul_ne_zero hc.ne' h)
  · exact Or.inr (mul_ne_zero hc.ne' h)

/-- The points of `W`, a type of this file. -/
def Dom : Type := {v : RnO 3 // v ∈ W}

instance : TopologicalSpace Dom := instTopologicalSpaceSubtype

/-- The coordinates of a point of `W`. -/
def Dom.vec (d : Dom) : Fin 3 → ℝ := d.1.val

theorem isOpenEmbedding_vec : IsOpenEmbedding Dom.vec :=
  Punctured.isOpenEmbedding_val.comp (isOpen_W.isOpenEmbedding_subtypeVal)

instance : T2Space Dom := isOpenEmbedding_vec.isEmbedding.t2Space

instance : SecondCountableTopology Dom := isOpenEmbedding_vec.isInducing.secondCountableTopology

instance : LocallyCompactSpace Dom := isOpenEmbedding_vec.locallyCompactSpace

instance : Inhabited Dom := ⟨⟨Punctured.mk ![1, 0, 1] (fun h => by simpa using congrFun h 0),
  by simp [W]⟩⟩

instance : SMul (Multiplicative ℤ) Dom :=
  ⟨fun k x => ⟨A (Multiplicative.toAdd k) • x.1, A_mem_W _ x.2⟩⟩

theorem smul_val (k : Multiplicative ℤ) (x : Dom) : (k • x).1 = A (Multiplicative.toAdd k) • x.1 :=
  rfl

/-- **`ℤ` acts on `W` by `k · v = A^k v`.** -/
instance : MulAction (Multiplicative ℤ) Dom where
  one_smul x := Subtype.ext (Punctured.ext (funext fun i => by
    rw [smul_val, A_val, toAdd_one, dg_zero, one_mul]))
  mul_smul a b x := Subtype.ext (Punctured.ext (funext fun i => by
    rw [smul_val, smul_val, smul_val, A_val, A_val, A_val, toAdd_mul, dg_add, mul_assoc]))

instance : ContinuousConstSMul (Multiplicative ℤ) Dom :=
  ⟨fun k => continuous_induced_rng.2 ((continuous_const_smul (A (Multiplicative.toAdd k))).comp
    continuous_subtype_val)⟩

/-- `|k| < R` when `R⁻¹ ≤ 2^k ≤ R`. -/
theorem natAbs_lt_of_zpow_two {k : ℤ} {R : ℝ} (h1 : (2 : ℝ) ^ k ≤ R) (h2 : R⁻¹ ≤ (2 : ℝ) ^ k) :
    (k.natAbs : ℝ) < R := by
  rcases Int.natAbs_eq k with hk | hk
  · rw [hk, zpow_natCast] at h1
    exact lt_of_lt_of_le (by exact_mod_cast Nat.lt_two_pow_self) h1
  · have hR : 0 < R := lt_of_lt_of_le (by positivity) h1
    rw [hk, zpow_neg, zpow_natCast] at h2
    have : (2 : ℝ) ^ k.natAbs ≤ R := by
      rwa [inv_le_inv₀ hR (by positivity)] at h2
    exact lt_of_lt_of_le (by exact_mod_cast Nat.lt_two_pow_self) this

/-- **The action is properly discontinuous**: `A^k` multiplies `z` by `2^k`, and `z` is bounded
above and away from `0` on a compact set of `W`. -/
instance : ProperlyDiscontinuousSMul (Multiplicative ℤ) Dom where
  finite_disjoint_inter_image {K L} hK hL := by
    set z : Dom → ℝ := fun d => d.1.val 2
    have hz : Continuous z := (continuous_apply 2).comp isOpenEmbedding_vec.continuous
    have hzpos : ∀ d : Dom, 0 < z d := fun d => d.2.1
    rcases (K ∪ L).eq_empty_or_nonempty with he | hne
    · refine Set.finite_empty.subset fun γ ⟨_, ⟨x, hx, _⟩, _⟩ => ?_
      exact (he ▸ (mem_union_left L hx) : x ∈ (∅ : Set Dom))
    obtain ⟨x₀, hx₀, hmin⟩ := (hK.union hL).exists_isMinOn hne hz.continuousOn
    obtain ⟨x₁, -, hmax⟩ := (hK.union hL).exists_isMaxOn hne hz.continuousOn
    set a := z x₀
    set b := z x₁
    have ha : 0 < a := hzpos x₀
    set R := b / a
    set N := ⌈R⌉₊
    refine ((Set.finite_Icc (-(N : ℤ)) N).preimage
      Multiplicative.toAdd.injective.injOn).subset fun γ hγ => ?_
    obtain ⟨_, ⟨x, hx, rfl⟩, hxL⟩ := hγ
    set k := Multiplicative.toAdd γ
    have hzx : z (γ • x) = (2 : ℝ) ^ k * z x := by
      show (A k • x.1).val 2 = _
      rw [A_val, dg_two']
    have h1 : a ≤ z x := hmin (mem_union_left L hx)
    have h2 : z x ≤ b := hmax (mem_union_left L hx)
    have h3 : a ≤ z (γ • x) := hmin (mem_union_right K hxL)
    have h4 : z (γ • x) ≤ b := hmax (mem_union_right K hxL)
    rw [hzx] at h3 h4
    have hk2 : 0 < (2 : ℝ) ^ k := by positivity
    have hzx0 := hzpos x
    have hR1 : (2 : ℝ) ^ k ≤ R := by
      rw [le_div_iff₀ ha]
      nlinarith
    have hR2 : R⁻¹ ≤ (2 : ℝ) ^ k := by
      rw [inv_div, div_le_iff₀ (hzpos x₁)]
      nlinarith
    have hlt := natAbs_lt_of_zpow_two hR1 hR2
    have hN : (k.natAbs : ℝ) ≤ N := hlt.le.trans (Nat.le_ceil R)
    have hN' : k.natAbs ≤ N := by exact_mod_cast hN
    simp only [mem_preimage, mem_Icc]
    omega


/-! ### The quotient `V = W/⟨A⟩` -/

/-- **The manifold `V = W/⟨A⟩`** of DEC-122's counterexample. -/
def V : Type := MulAction.orbitRel.Quotient (Multiplicative ℤ) Dom

instance : TopologicalSpace V := instTopologicalSpaceQuotient

/-- The projection `π : W → V`. -/
def π (d : Dom) : V := Quotient.mk (MulAction.orbitRel (Multiplicative ℤ) Dom) d

/-- **`V` is Hausdorff** (the action is free and properly discontinuous; Mathlib's
`t2Space_of_properlyDiscontinuousSMul_of_t2Space`). -/
instance : T2Space V :=
  inferInstanceAs (T2Space (Quotient (MulAction.orbitRel (Multiplicative ℤ) Dom)))

theorem continuous_π : Continuous π := continuous_quot_mk

theorem isOpenMap_π : IsOpenMap π := isOpenMap_quotient_mk'_mul

theorem π_surjective : Function.Surjective π := Quotient.mk_surjective

/-- **`V` is second countable.** -/
instance : SecondCountableTopology V :=
  TopologicalSpace.Quotient.secondCountableTopology isOpenMap_quotient_mk'_mul

theorem π_eq_π_iff {d d' : Dom} : π d = π d' ↔ ∃ k : ℤ, A k • d'.1 = d.1 := by
  have : π d = π d' ↔ MulAction.orbitRel (Multiplicative ℤ) Dom d d' := Quotient.eq
  rw [this, MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨γ, hγ⟩
    exact ⟨Multiplicative.toAdd γ, congrArg Subtype.val hγ⟩
  · rintro ⟨k, hk⟩
    exact ⟨Multiplicative.ofAdd k, Subtype.ext hk⟩

open scoped Classical in
/-- The projection, extended to `ℝ³ − {O}` (a junk value off `W`). -/
def π' (w : RnO 3) : V := if h : w ∈ W then π ⟨w, h⟩ else π default

theorem π'_of_mem {w : RnO 3} (hw : w ∈ W) : π' w = π ⟨w, hw⟩ := dif_pos hw

theorem π'_val (d : Dom) : π' d.1 = π d := π'_of_mem d.2

theorem π'_eq_π'_iff {w w' : RnO 3} (hw : w ∈ W) (hw' : w' ∈ W) :
    π' w = π' w' ↔ ∃ k : ℤ, A k • w' = w := by
  rw [π'_of_mem hw, π'_of_mem hw', π_eq_π_iff]

theorem π'_A_smul (k : ℤ) {w : RnO 3} (hw : w ∈ W) : π' (A k • w) = π' w :=
  (π'_eq_π'_iff (A_mem_W k hw) hw).2 ⟨k, rfl⟩

theorem continuousOn_π' : ContinuousOn π' W := by
  rw [continuousOn_iff_continuous_restrict]
  have : W.restrict π' = π := funext fun d => π'_val d
  rw [this]
  exact continuous_π

/-! ### The cone charts -/

/-- **The cone neighbourhoods** `N(i, r) = {r z < |v_i| < 2 r z, z > 0}` (`i = 0, 1`): open cones in
`W`, disjoint from their translates by `A^k`, `k ≠ 0` (the ratio `|v_i| / z` is multiplied by `2^k`
for `i = 0`, by `16^{-k}` for `i = 1`). -/
def N (i : Fin 2) (r : ℝ) : Set (RnO 3) :=
  {w | 0 < w.val 2 ∧ r * w.val 2 < |w.val (Fin.castSucc i)| ∧
    |w.val (Fin.castSucc i)| < 2 * r * w.val 2}

theorem isOpen_N (i : Fin 2) (r : ℝ) : IsOpen (N i r) := by
  have hc : ∀ j : Fin 3, Continuous fun v : RnO 3 => v.val j := fun j =>
    (continuous_apply j).comp Punctured.continuous_val
  simp only [N, setOf_and]
  refine (isOpen_lt continuous_const (hc 2)).inter ((isOpen_lt ?_ ?_).inter (isOpen_lt ?_ ?_))
  · exact continuous_const.mul (hc 2)
  · exact (hc _).abs
  · exact (hc _).abs
  · exact continuous_const.mul (hc 2)

theorem N_subset_W {i : Fin 2} {r : ℝ} (hr : 0 < r) : N i r ⊆ W := by
  rintro w ⟨hz, h1, -⟩
  have hx : w.val (Fin.castSucc i) ≠ 0 := by
    intro h
    rw [h, abs_zero] at h1
    nlinarith
  refine ⟨hz, ?_⟩
  fin_cases i
  · exact Or.inl hx
  · exact Or.inr hx

theorem isConeSet_N (i : Fin 2) (r : ℝ) : IsConeSet (N i r) := by
  refine ⟨isOpen_N i r, fun c w ⟨hz, h1, h2⟩ => ?_⟩
  have hc := Punctured.pos c
  simp only [N, mem_setOf_eq, Punctured.val_smul_pos, Pi.smul_apply, smul_eq_mul, abs_mul,
    abs_of_pos hc]
  refine ⟨mul_pos hc hz, ?_, ?_⟩ <;> nlinarith

/-- `1/2 < a^k < 2` with `a ≥ 2` forces `k = 0`. -/
theorem eq_zero_of_zpow_mem {a : ℝ} (ha : 2 ≤ a) {k : ℤ} (h1 : 1 / 2 < a ^ k) (h2 : a ^ k < 2) :
    k = 0 := by
  have ha1 : 1 ≤ a := by linarith
  by_contra hk
  rcases lt_or_gt_of_ne hk with hk | hk
  · have : a ^ k ≤ a ^ (-1 : ℤ) := zpow_le_zpow_right₀ ha1 (by omega)
    rw [zpow_neg_one] at this
    have : a⁻¹ ≤ 1 / 2 := by
      rw [one_div]; exact inv_anti₀ (by norm_num) ha
    linarith
  · have : a ^ (1 : ℤ) ≤ a ^ k := zpow_le_zpow_right₀ ha1 (by omega)
    rw [zpow_one] at this
    linarith

/-- The factor by which `A^k` multiplies `|v_i| / z`. -/
theorem dg_div (k : ℤ) (i : Fin 2) :
    dg k (Fin.castSucc i) = (if i = 0 then (2 : ℝ) ^ k else (16 : ℝ) ^ (-k)) * (2 : ℝ) ^ k := by
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue, Fin.castSucc_zero, dg_zero', ↓reduceIte]
    rw [← mul_zpow]; norm_num
  · simp only [Fin.mk_one, Fin.isValue, Fin.castSucc_one, dg_one', one_ne_zero, ↓reduceIte]
    rw [zpow_neg, zpow_neg, show (16 : ℝ) = 8 * 2 by norm_num, mul_zpow, mul_inv,
      mul_assoc, inv_mul_cancel₀ (by positivity), mul_one]

/-- **`N(i, r)` is disjoint from its translates**: `w, A^k w ∈ N(i, r)` forces `k = 0`. -/
theorem eq_zero_of_mem_N {i : Fin 2} {r : ℝ} {w : RnO 3} (hw : w ∈ N i r) {k : ℤ}
    (hk : A k • w ∈ N i r) : k = 0 := by
  obtain ⟨hz, h1, h2⟩ := hw
  obtain ⟨-, h3, h4⟩ := hk
  simp only [A_val, abs_mul, abs_of_pos (dg_pos k _)] at h3 h4
  rw [dg_two', dg_div] at *
  set t := (if i = 0 then (2 : ℝ) ^ k else (16 : ℝ) ^ (-k))
  have h2k : 0 < (2 : ℝ) ^ k := by positivity
  set x := |w.val (Fin.castSucc i)|
  have hx : 0 < x := by nlinarith
  have ht1 : 1 / 2 < t := by
    by_contra h
    push Not at h
    have : t * 2 ^ k * x ≤ 2 ^ k * x / 2 := by
      have := mul_le_mul_of_nonneg_right h (by positivity : (0 : ℝ) ≤ 2 ^ k * x)
      linarith
    nlinarith
  have ht2 : t < 2 := by
    by_contra h
    push Not at h
    have : 2 * (2 ^ k * x) ≤ t * 2 ^ k * x := by
      have := mul_le_mul_of_nonneg_right h (by positivity : (0 : ℝ) ≤ 2 ^ k * x)
      linarith
    nlinarith
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue, ↓reduceIte, t] at ht1 ht2
    exact eq_zero_of_zpow_mem le_rfl ht1 ht2
  · simp only [Fin.mk_one, Fin.isValue, one_ne_zero, ↓reduceIte, t] at ht1 ht2
    have := eq_zero_of_zpow_mem (by norm_num : (2 : ℝ) ≤ 16) ht1 ht2
    omega

theorem injOn_π' {i : Fin 2} {r : ℝ} (hr : 0 < r) : InjOn π' (N i r) := by
  intro w hw w' hw' h
  obtain ⟨k, hk⟩ := (π'_eq_π'_iff (N_subset_W hr hw) (N_subset_W hr hw')).1 h
  have hk0 : k = 0 := eq_zero_of_mem_N hw' (hk ▸ hw)
  subst hk0
  rw [← hk]
  exact Punctured.ext (funext fun j => by rw [A_val, dg_zero, one_mul])


/-- The index of a cone chart: a coordinate `i ∈ {0, 1}` and a ratio `r > 0`. -/
abbrev Idx : Type := Fin 2 × {r : ℝ // 0 < r}

/-- The cone neighbourhood of an index. -/
abbrev Nj (j : Idx) : Set (RnO 3) := N j.1 j.2.1

theorem isOpenMap_restrict_π' (j : Idx) : IsOpenMap ((Nj j).restrict π') := by
  intro U hU
  have hU' : IsOpen (Subtype.val '' U : Set (RnO 3)) := (isOpen_N _ _).isOpenMap_subtype_val U hU
  have : (Nj j).restrict π' '' U = π '' {d : Dom | d.1 ∈ Subtype.val '' U} := by
    ext x
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨⟨w.1, N_subset_W j.2.2 w.2⟩, ⟨w, hw, rfl⟩, (π'_val ⟨w.1, N_subset_W j.2.2 w.2⟩).symm⟩
    · rintro ⟨d, ⟨w, hw, hwd⟩, rfl⟩
      refine ⟨w, hw, ?_⟩
      show π' w.1 = π d
      rw [hwd, π'_val]
  rw [this]
  exact isOpenMap_π _ (hU'.preimage (continuous_subtype_val : Continuous fun d : Dom => d.1))

/-- The inverse of a cone chart: `π'` restricted to `N(i, r)`. -/
def chartInv (j : Idx) : OpenPartialHomeomorph (RnO 3) V :=
  OpenPartialHomeomorph.ofContinuousOpenRestrict ((injOn_π' j.2.2).toPartialEquiv π' (Nj j))
    (continuousOn_π'.mono (N_subset_W j.2.2)) (isOpenMap_restrict_π' j) (isOpen_N _ _)

/-- **The cone chart `f_N = (π|N)⁻¹ : π(N) → N`** (audit WP-45n, `cone_charts_3deg`). -/
def chart (j : Idx) : OpenPartialHomeomorph V (RnO 3) := (chartInv j).symm

theorem chart_target (j : Idx) : (chart j).target = Nj j := rfl

theorem chart_source (j : Idx) : (chart j).source = π' '' Nj j := rfl

theorem chart_symm_apply (j : Idx) (w : RnO 3) : (chart j).symm w = π' w := rfl

theorem chart_π' (j : Idx) {w : RnO 3} (hw : w ∈ Nj j) : chart j (π' w) = w :=
  (chartInv j).left_inv hw

theorem π'_chart (j : Idx) {x : V} (hx : x ∈ (chart j).source) : π' (chart j x) = x :=
  (chart j).left_inv hx

theorem exists_idx {w : RnO 3} (hw : w ∈ W) : ∃ j : Idx, w ∈ Nj j := by
  obtain ⟨hz, hxy⟩ := hw
  have key : ∀ i : Fin 2, w.val (Fin.castSucc i) ≠ 0 → ∃ j : Idx, w ∈ Nj j := by
    intro i hi
    have hx : 0 < |w.val (Fin.castSucc i)| := abs_pos.2 hi
    refine ⟨(i, ⟨2 * |w.val (Fin.castSucc i)| / (3 * w.val 2), by positivity⟩), hz, ?_, ?_⟩
    · show 2 * |w.val (Fin.castSucc i)| / (3 * w.val 2) * w.val 2 < _
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith
    · show _ < 2 * (2 * |w.val (Fin.castSucc i)| / (3 * w.val 2)) * w.val 2
      rw [mul_div_assoc', div_mul_eq_mul_div, lt_div_iff₀ (by positivity)]
      nlinarith
  rcases hxy with h | h
  · exact key 0 h
  · exact key 1 h

/-- The chosen index at a point of `V`. -/
def idxAt (x : V) : Idx := (exists_idx (Quotient.out x : Dom).2).choose

theorem mem_chart_idxAt_source (x : V) : x ∈ (chart (idxAt x)).source := by
  refine ⟨(Quotient.out x : Dom).1, (exists_idx (Quotient.out x : Dom).2).choose_spec, ?_⟩
  rw [π'_val]
  exact Quotient.out_eq x

/-- **The charted space of `V`**: the cone charts `f_N` (stated over `RnO (2 + 1)`, the form
`ConeBase 2 V` asks for). -/
instance : ChartedSpace (RnO (2 + 1)) V where
  atlas := range chart
  chartAt x := chart (idxAt x)
  mem_chart_source := mem_chart_idxAt_source
  chart_mem_atlas _ := mem_range_self _

/-- **The transitions are the `A^k`**: near a point of the overlap of two cone charts,
`f_{N'} = A^k ∘ f_N`. -/
theorem chart_transition (j₁ j₂ : Idx) {x : V} (hx₁ : x ∈ (chart j₁).source)
    (hx₂ : x ∈ (chart j₂).source) :
    ∃ k : ℤ, ∀ᶠ z in 𝓝 x, chart j₂ z = A k • chart j₁ z := by
  obtain ⟨w₁, hw₁, rfl⟩ := hx₁
  obtain ⟨w₂, hw₂, hw⟩ := hx₂
  obtain ⟨k, hk⟩ := (π'_eq_π'_iff (N_subset_W j₂.2.2 hw₂) (N_subset_W j₁.2.2 hw₁)).1 hw
  refine ⟨k, ?_⟩
  have hc : ContinuousAt (fun z => A k • chart j₁ z) (π' w₁) :=
    (continuous_const_smul _).continuousAt.comp ((chart j₁).continuousAt ⟨w₁, hw₁, rfl⟩)
  have hmem : A k • chart j₁ (π' w₁) ∈ Nj j₂ := by rw [chart_π' j₁ hw₁, hk]; exact hw₂
  filter_upwards [(chart j₁).open_source.mem_nhds ⟨w₁, hw₁, rfl⟩,
    hc.eventually ((isOpen_N _ _).mem_nhds hmem)] with z hz hz'
  have hW : chart j₁ z ∈ W := N_subset_W j₁.2.2 ((chart j₁).map_source hz)
  calc chart j₂ z = chart j₂ (π' (A k • chart j₁ z)) := by rw [π'_A_smul k hW, π'_chart j₁ hz]
    _ = A k • chart j₁ z := chart_π' j₂ hz'

/-- **`V` is an affine conical manifold** — a `(GU(3), ℝ³ − {O})`-manifold… -/
instance : HasGroupoid V (coneGroupoid (2 + 1)) where
  compatible := by
    rintro _ _ ⟨j₁, rfl⟩ ⟨j₂, rfl⟩
    refine symm_trans_mem_gxGroupoid fun x hx => ?_
    obtain ⟨k, hk⟩ := chart_transition j₁ j₂ hx.1 hx.2
    exact ⟨A k, hk⟩

theorem isConeChart_chart (j : Idx) : IsConeChart (2 + 1) (chart j) :=
  ⟨(coneGroupoid (2 + 1)).subset_maximalAtlas (mem_range_self j), isConeSet_N _ _⟩

/-- … **with cone charts** (Déf. 2, 3°). -/
instance : HasConeCharts (2 + 1) V :=
  ⟨fun x => ⟨chart (idxAt x), isConeChart_chart _, mem_chart_idxAt_source x⟩⟩

/-- **The positive homotheties of `V`** (Déf. 3) are induced by those of `W`:
`λ π(v) = π(λ v)`. -/
theorem posSMul_π' (c : RPos) {w : RnO 3} (hw : w ∈ W) :
    posSMul (2 + 1) c (π' w) = π' (c • w) := by
  obtain ⟨j, hj⟩ := exists_idx hw
  refine (posSMul_eq (isConeChart_chart j) ⟨w, hj, rfl⟩ c).trans ?_
  rw [chart_π' j hj, chart_symm_apply]


/-! ### `V` is a « variété »: connected, and paracompact -/

/-- `W` is connected: it is the image of `(ℝ² − {O}) × ]0, ∞[`. -/
instance : ConnectedSpace Dom := by
  have h2 : ConnectedSpace {q : Fin 2 → ℝ // q ≠ 0} := by
    have : IsConnected ({0}ᶜ : Set (Fin 2 → ℝ)) :=
      isConnected_compl_singleton_of_one_lt_rank (by rw [rank_fin_fun]; norm_num) 0
    exact isConnected_iff_connectedSpace.1 this
  have hI : ConnectedSpace {t : ℝ // 0 < t} := isConnected_iff_connectedSpace.1 isConnected_Ioi
  let F : {q : Fin 2 → ℝ // q ≠ 0} × {t : ℝ // 0 < t} → Dom := fun p =>
    ⟨Punctured.mk ![p.1.1 0, p.1.1 1, p.2.1] (fun h => by
      have := congrFun h 2
      simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, Pi.zero_apply] at this
      exact p.2.2.ne' this), by
      refine ⟨by simpa using p.2.2, ?_⟩
      by_contra h
      push Not at h
      apply p.1.2
      funext i
      fin_cases i
      · simpa using h.1
      · simpa using h.2⟩
  have hF : Continuous F := by
    refine continuous_induced_rng.2 (continuous_induced_rng.2 ?_)
    show Continuous fun p : {q : Fin 2 → ℝ // q ≠ 0} × {t : ℝ // 0 < t} =>
      (![p.1.1 0, p.1.1 1, p.2.1] : Fin 3 → ℝ)
    refine continuous_pi fun i => ?_
    fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons]
    · exact (continuous_apply 0).comp (continuous_subtype_val.comp continuous_fst)
    · exact (continuous_apply 1).comp (continuous_subtype_val.comp continuous_fst)
    · exact continuous_subtype_val.comp continuous_snd
  have hsurj : Function.Surjective F := by
    intro d
    have hz : 0 < d.1.val 2 := d.2.1
    have hq : (![d.1.val 0, d.1.val 1] : Fin 2 → ℝ) ≠ 0 := by
      intro h
      rcases d.2.2 with h' | h'
      · exact h' (by simpa using congrFun h 0)
      · exact h' (by simpa using congrFun h 1)
    refine ⟨(⟨_, hq⟩, ⟨_, hz⟩), Subtype.ext (Punctured.ext (funext fun i => ?_))⟩
    fin_cases i <;> rfl
  exact hsurj.connectedSpace hF

/-- **`V` is connected.** -/
instance : ConnectedSpace V := π_surjective.connectedSpace continuous_π

theorem locallyCompactSpace_RnO3 : LocallyCompactSpace (RnO 3) :=
  Punctured.isOpenEmbedding_val.locallyCompactSpace

/-- `V` is locally compact (it is charted on `ℝ³ − {O}`). -/
instance : LocallyCompactSpace V :=
  haveI := locallyCompactSpace_RnO3
  ChartedSpace.locallyCompactSpace (RnO 3) V

/-- **`V` is paracompact** (Hausdorff, locally compact, second countable). -/
example : ParacompactSpace V := inferInstance

/-! ### The base is not Hausdorff -/

/-- `(1, 16^{-k}, 1)`. -/
def yv (k : ℕ) : RnO 3 := Punctured.mk ![1, (16 : ℝ)⁻¹ ^ k, 1] (fun h => by
  simpa using congrFun h 0)

/-- `(2^{-k}, 1, 1)`. -/
def zv (k : ℕ) : RnO 3 := Punctured.mk ![(2 : ℝ)⁻¹ ^ k, 1, 1] (fun h => by
  simpa using congrFun h 1)

/-- `(1, 0, 1)`. -/
def p₁ : RnO 3 := Punctured.mk ![1, 0, 1] (fun h => by simpa using congrFun h 0)

/-- `(0, 1, 1)`. -/
def p₂ : RnO 3 := Punctured.mk ![0, 1, 1] (fun h => by simpa using congrFun h 1)

theorem yv_mem (k : ℕ) : yv k ∈ W := ⟨by simp [yv], Or.inl (by simp [yv])⟩
theorem zv_mem (k : ℕ) : zv k ∈ W := ⟨by simp [zv], Or.inr (by simp [zv])⟩
theorem p₁_mem : p₁ ∈ W := ⟨by simp [p₁], Or.inl (by simp [p₁])⟩
theorem p₂_mem : p₂ ∈ W := ⟨by simp [p₂], Or.inr (by simp [p₂])⟩

theorem tendsto_yv : Tendsto yv atTop (𝓝 p₁) := by
  rw [Punctured.isEmbedding_val.tendsto_nhds_iff, tendsto_pi_nhds]
  intro i
  fin_cases i
  · simp [yv, p₁]
  · simpa [yv, p₁] using
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 16⁻¹) (by norm_num)
  · simp [yv, p₁]

theorem tendsto_zv : Tendsto zv atTop (𝓝 p₂) := by
  rw [Punctured.isEmbedding_val.tendsto_nhds_iff, tendsto_pi_nhds]
  intro i
  fin_cases i
  · simpa [zv, p₂] using
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 2⁻¹) (by norm_num)
  · simp [zv, p₂]
  · simp [zv, p₂]

/-- **`2^k y_k = A^k z_k`, so `π(2^k y_k) = π(z_k)`** (`z_k = (2^{-k}, 1, 1)`): the two sequences
have the same image in `B`. -/
theorem π'_smul_yv (k : ℕ) :
    π' (Punctured.posUnit ((2 : ℝ) ^ k) (by positivity) • yv k) = π' (zv k) := by
  refine (π'_eq_π'_iff (smul_mem_W _ (yv_mem k)) (zv_mem k)).2 ⟨k, ?_⟩
  refine Punctured.ext (funext fun i => ?_)
  rw [A_val]
  fin_cases i
  · simp only [zv, yv, Fin.zero_eta, Fin.isValue, dg_zero', Punctured.val_smul_pos,
      Punctured.coe_posUnit, Punctured.val_mk, Pi.smul_apply, Matrix.cons_val_zero, smul_eq_mul]
    rw [zpow_natCast, show (4 : ℝ) = 2 * 2 by norm_num, mul_pow, inv_pow]
    field_simp
  · simp only [zv, yv, Fin.mk_one, Fin.isValue, dg_one', Punctured.val_smul_pos,
      Punctured.coe_posUnit, Punctured.val_mk, Pi.smul_apply, Matrix.cons_val_one,
      Matrix.cons_val_zero, smul_eq_mul]
    rw [zpow_neg, zpow_natCast, inv_pow, show (16 : ℝ) = 2 * 8 by norm_num, mul_pow]
    field_simp
  · simp only [zv, yv, Fin.reduceFinMk, Fin.isValue, dg_two', Punctured.val_smul_pos,
      Punctured.coe_posUnit, Punctured.val_mk, Pi.smul_apply, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.head_cons, smul_eq_mul, zpow_natCast]

/-- **THE FINDING (DEC-122): the base `B = V/ℝ⁺` of the Hausdorff, second countable, connected
affine conical manifold `V` is not Hausdorff.** The rays `[(1, 0)]` and `[(0, 1)]` are not
separated: `y_k = π(1, 16^{-k}, 1) → π(1, 0, 1)` while `2^k · y_k = π(2^{-k}, 1, 1) → π(0, 1, 1)`,
and `π(0, 1, 1) ∉ ℝ₊* · π(1, 0, 1)`. -/
theorem not_t2Space_coneBase : ¬ T2Space (ConeBase 2 V) := by
  intro hT
  have hc₁ : Tendsto (fun k => ConeBase.mk (n := 2) (π' (yv k))) atTop
      (𝓝 (ConeBase.mk (π' p₁))) :=
    (ConeBase.continuous_mk.tendsto _).comp
      ((continuousOn_π'.continuousAt (isOpen_W.mem_nhds p₁_mem)).tendsto.comp tendsto_yv)
  have hc₂ : Tendsto (fun k => ConeBase.mk (n := 2) (π' (zv k))) atTop
      (𝓝 (ConeBase.mk (π' p₂))) :=
    (ConeBase.continuous_mk.tendsto _).comp
      ((continuousOn_π'.continuousAt (isOpen_W.mem_nhds p₂_mem)).tendsto.comp tendsto_zv)
  have heq : ∀ k, ConeBase.mk (n := 2) (π' (yv k)) = ConeBase.mk (π' (zv k)) := fun k => by
    rw [← π'_smul_yv k, ← posSMul_π' _ (yv_mem k), ConeBase.mk_posSMul]
  have hb : ConeBase.mk (n := 2) (π' p₁) = ConeBase.mk (π' p₂) :=
    tendsto_nhds_unique hc₁ (hc₂.congr fun k => (heq k).symm)
  obtain ⟨c, hc⟩ := ConeBase.mk_eq_mk_iff.1 hb
  rw [posSMul_π' c p₂_mem] at hc
  obtain ⟨k, hk⟩ := (π'_eq_π'_iff (smul_mem_W c p₂_mem) p₁_mem).1 hc
  have := congrArg (fun v : RnO 3 => v.val 0) hk
  simp [p₁, p₂, A_val] at this
  exact absurd this (by positivity)


/-! ### Consequences: the three statements that fail -/

/-- **The action of `ℝ₊*` on `V` is not proper** (`ConeBase.t2Space_iff_properSMul`). -/
theorem not_properSMul : ¬ @ProperSMul RPos V _ _ _ (coneMulAction (2 + 1) V) :=
  fun h => not_t2Space_coneBase (ConeBase.t2Space_of_properSMul h)

/-- **`V → B` has no continuous section** (a section would embed `B` in the Hausdorff `V`,
`ConeBase.t2Space_of_section`). -/
theorem not_exists_section :
    ¬ ∃ σ : ConeBase 2 V → V, Continuous σ ∧ ∀ b, ConeBase.mk (σ b) = b := by
  rintro ⟨σ, hσ, hmk⟩
  exact not_t2Space_coneBase (ConeBase.t2Space_of_section hσ hmk)

/-- **`V` is not homeomorphic to `B × ℝ₊*`**, by any homeomorphism (over `B` or not). -/
theorem isEmpty_homeomorph : IsEmpty (V ≃ₜ ConeBase 2 V × RPos) :=
  ⟨fun T => not_t2Space_coneBase (ConeBase.t2Space_of_homeomorph T)⟩

/-- **§ 2 Prop. 2 read with a « variété » base** (plan F6: « structure localement projective » on a
variété, Déf. 12), as a `Prop` (kb/0022): the base of every Hausdorff, second countable, connected
affine conical 3-manifold is Hausdorff. FALSE (`not_prop2HausdorffBaseAsRead`); the corrected form
is `ConeBase.existsUnique_baseStructure_of_properSMul`. -/
def Prop2HausdorffBaseAsRead : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [ChartedSpace (RnO (2 + 1)) X]
    [HasGroupoid X (coneGroupoid (2 + 1))] [HasConeCharts (2 + 1) X] [T2Space X]
    [SecondCountableTopology X] [ConnectedSpace X], T2Space (ConeBase 2 X)

/-- **FINDING (DEC-122) against § 2 Prop. 2** (`bzprop:c1s2p2_base_cone`). -/
theorem not_prop2HausdorffBaseAsRead : ¬ Prop2HausdorffBaseAsRead :=
  fun h => not_t2Space_coneBase (h V)

/-- **Déf. 3's « cet espace fibré est topologiquement trivial », as printed** (kb/0022): every
Hausdorff, second countable, connected affine conical 3-manifold `X` is `ℝ₊*`-equivariantly
homeomorphic to `B × ℝ₊*` over `B`. FALSE (`not_def3TrivialAsPrinted`); the corrected form is
`ConeBase.exists_trivialization_of_properSMul`. -/
def Def3TrivialAsPrinted : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [ChartedSpace (RnO (2 + 1)) X]
    [HasGroupoid X (coneGroupoid (2 + 1))] [HasConeCharts (2 + 1) X] [T2Space X]
    [SecondCountableTopology X] [ConnectedSpace X],
    ∃ T : X ≃ₜ ConeBase 2 X × RPos, (∀ m, (T m).1 = ConeBase.mk m) ∧
      ∀ (c : RPos) (m : X), T (posSMul (2 + 1) c m) = ((T m).1, c * (T m).2)

/-- **FINDING (DEC-122) against Déf. 3** (`bzdef:c1s2d3_homotheties_positives`). -/
theorem not_def3TrivialAsPrinted : ¬ Def3TrivialAsPrinted := fun h => by
  obtain ⟨T, -, -⟩ := h V
  exact isEmpty_homeomorph.false T

/-- **The p. 241 inference, as printed** (kb/0022): « si $V$ est supposé para-compact, on peut donc
construire une section de $V$ au-dessus de $B$ », for every Hausdorff, second countable, connected,
paracompact affine conical 3-manifold. FALSE (`not_p241SectionAsPrinted`); the corrected form is
`ConeBase.exists_section_of_properSMul`. -/
def P241SectionAsPrinted : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [ChartedSpace (RnO (2 + 1)) X]
    [HasGroupoid X (coneGroupoid (2 + 1))] [HasConeCharts (2 + 1) X] [T2Space X]
    [SecondCountableTopology X] [ConnectedSpace X] [ParacompactSpace X],
    ∃ σ : ConeBase 2 X → X, Continuous σ ∧ ∀ b, ConeBase.mk (σ b) = b

/-- **FINDING (DEC-122) against the p. 241 prose**: `V` is paracompact and has no section. -/
theorem not_p241SectionAsPrinted : ¬ P241SectionAsPrinted :=
  fun h => not_exists_section (h V)

/-- **DEC-122's counterexample in one statement**: `V = W/⟨A⟩` is a Hausdorff, second countable,
connected, paracompact affine conical 3-manifold whose base is not Hausdorff, whose `ℝ₊*`-action is
not proper, and which has no section and is not homeomorphic to `B × ℝ₊*`. -/
theorem counterexample :
    T2Space V ∧ SecondCountableTopology V ∧ ConnectedSpace V ∧ ParacompactSpace V ∧
      ¬ T2Space (ConeBase 2 V) ∧ ¬ @ProperSMul RPos V _ _ _ (coneMulAction (2 + 1) V) ∧
      (¬ ∃ σ : ConeBase 2 V → V, Continuous σ ∧ ∀ b, ConeBase.mk (σ b) = b) ∧
      IsEmpty (V ≃ₜ ConeBase 2 V × RPos) :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance, not_t2Space_coneBase,
    not_properSMul, not_exists_section, isEmpty_homeomorph⟩

end ConeCex
end Benzecri
