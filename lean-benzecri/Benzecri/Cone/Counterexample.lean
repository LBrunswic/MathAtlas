import Benzecri.Cone.Section
import Mathlib.Analysis.Normed.Module.Connected

/-!
# `Benzecri.Cone.Counterexample` — affine conical manifolds whose base is not Hausdorff, in every dimension `n ≥ 3` (DEC-122, DEC-124)

J.-P. Benzécri, *Sur les variétés localement affines et localement projectives*, Bull. SMF 88
(1960) 229–332, Chapter 1 § 2, journal pp. 240–241; transcription
`papers/benzecri/legacy/labeled/benzecri1960_ch1.tex`. Package WP-45p (wave-3 fix round;
generalised to every `n ≥ 3` at the pre-graduation pass, DEC-124). The construction is the wave-3
audit's (`campaign/WP-45n/AUDIT-1.json`, check `B_hausdorff`), ruled a FINDING by the author
(DEC-122); DEC-124 asks for it in every dimension. No label is marked here: the marks are on the
corrected forms (DEC-124: the corrected forms are the formalizations of record, the printed forms
stay refuted here as the paper finding).

THE FINDING (DEC-122, DEC-124), for every Benzécri dimension `n = m + 3 ≥ 3` (Lean's
`ConeBase (m + 2) (VDim m)`, `VDim m` charted on `RnO (m + 2 + 1) = ℝⁿ − {O}`):

* `W = {v : v₂ > 0, (v₀, v₁) ≠ (0, 0)}` (`ConeCex.W m`), an open cone, and
  `A = diag(4, 1/8, 2, 1, …, 1) ∈ GU(n)` (`ConeCex.A m 1`; `ConeCex.A m k` is `A^k`). The
  `ℤ`-action `k · v = A^k v` on `W` is free and properly discontinuous (`A^k` multiplies `v₂` by
  `2^k`).
* `V = W/⟨A⟩` (`ConeCex.VDim m`) is Hausdorff, second countable, connected and paracompact, with
  an affine conical structure whose cone charts are `f_N = (proj|N)⁻¹` on the cones
  `N(i, r) = {r v₂ < |v_i| < 2 r v₂}` (`ConeCex.chart`) and whose transitions are the `A^k`
  (`ConeCex.chart_transition`): `[ChartedSpace] [HasGroupoid V (coneGroupoid n)]
  [HasConeCharts n V] [T2Space V]`. Its positive homotheties are those of `W`
  (`ConeCex.posSMul_proj'`).
* **The base `B = V/ℝ⁺` is NOT Hausdorff** (`ConeCex.not_t2Space_coneBase_dim`): `[(1,0,…)]` and
  `[(0,1,…)]` are inseparable, since `y_k = proj(1, 16^{-k}, 1, 0, …) → proj(1, 0, 1, 0, …)` while
  `2^k · y_k = proj(2^{-k}, 1, 1, 0, …) → proj(0, 1, 1, 0, …)`.
* Consequences, each the refutation of a `Prop` holding the printed statement (kb/0022), for every
  `n ≥ 3` (the `Prop`s take Lean's base dimension `n − 1 ≥ 2`):
  - `bzprop:c1s2p2_base_cone` — `benzecri1960_ch1.tex:540` (§ 2 Prop. 2, l.540–546, p. 240), read
    with a « variété » base (plan F6): `ConeCex.Prop2HausdorffBaseAsReadDim`,
    `ConeCex.not_prop2HausdorffBaseAsRead_dim`;
  - `bzdef:c1s2d3_homotheties_positives` — `benzecri1960_ch1.tex:526` (Déf. 3, l.526–538,
    p. 240), « cet espace fibré est topologiquement trivial »: `ConeCex.Def3TrivialAsPrintedDim`,
    `ConeCex.not_def3TrivialAsPrinted_dim` (indeed `V` is homeomorphic to `B × ℝ₊*` by no
    homeomorphism at all, `ConeCex.isEmpty_homeomorph_dim`);
  - the p. 241 prose — `benzecri1960_ch1.tex:549` (l.549–552, no label), « si $V$ est supposé
    para-compact, on peut donc construire une section »: `ConeCex.P241SectionAsPrintedDim`,
    `ConeCex.not_p241SectionAsPrinted_dim` (`V` is paracompact;
    `ConeCex.not_exists_section_dim`).
  - The action of `ℝ₊*` is not proper (`ConeCex.not_properSMul_dim`).
  The whole construction in one statement: `ConeCex.counterexample_dim`.
* **Benzécri's `n = 3`** keeps the names of wave 3, now specialisations (`m = 0`): `ConeCex.V`
  (`= VDim 0`, on `ℝ³ − {O}`, `A = diag(4, 1/8, 2)`), `not_t2Space_coneBase`, `not_properSMul`,
  `not_exists_section`, `isEmpty_homeomorph`, the `Prop`s `Prop2HausdorffBaseAsRead`,
  `Def3TrivialAsPrinted`, `P241SectionAsPrinted` (each the `…Dim 2` one) with their refutations
  `not_prop2HausdorffBaseAsRead`, `not_def3TrivialAsPrinted`, `not_p241SectionAsPrinted`, and
  `counterexample`.

The corrected forms (DEC-122: add « the action of `ℝ₊*` is proper », equivalently `B` Hausdorff,
`ConeBase.t2Space_iff_properSMul`) are `ConeBase.existsUnique_baseStructure_of_properSMul`
(`Cone/Base`), `ConeBase.exists_trivialization_of_properSMul` and
`ConeBase.exists_section_of_properSMul` (`Cone/Section`), MARKED (DEC-124); in dimension `n ≤ 2`
no hypothesis is needed (`Cone/LowDim`).

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
| `V` an affine conical manifold of dimension `n ≥ 3` (Déf. 2, with 3°) | ✓ proved for `V`: cone charts `f_N` onto the open cones `N(i, r)`, transitions `A^k ∈ GU(n)` |
| `V` a « variété »: Hausdorff, second countable, connected (plan F6) | ✓ proved: `T2Space V` (Mathlib, properly discontinuous action), `SecondCountableTopology V`, `ConnectedSpace V`; also `ParacompactSpace V` |
| « $V$ para-compact » (p. 241) | ✓ proved |
| `B` a « variété » (Prop. 2 read with plan F6) | ✗ refuted: `B` is not Hausdorff |

## SCOPE (disclosed)

* Every Benzécri dimension `n ≥ 3` is formalized (DEC-124): `m = n − 3`, the extra coordinates
  `v₃, …, v_{n−1}` carry the eigenvalue `1` and play no role (the test vectors have them `0`). For
  `n ≤ 2` the base is always Hausdorff (`Cone/LowDim`).
* `A` fixes no ray of `W` (every eigenline of `A` meets `W` in nothing; the eigenspace of `1`
  lies in `v₂ = 0`); the proof does not need this fact separately: it is what makes the `N(i, r)`
  disjoint from their translates (`ConeCex.eq_zero_of_mem_N`).
* The instances on `VDim m` are stated over `RnO (m + 2 + 1)`, `coneGroupoid (m + 2 + 1)` and
  `HasConeCharts (m + 2 + 1)`, the syntactic form `ConeBase (m + 2)` asks for; instance search
  unifies `0 + 2 + 1` with `2 + 1`, so `ConeCex.V := VDim 0` (an `abbrev`) inherits them in the
  form `ConeBase 2 V` asks for. All instances are on this file's own types `ConeCex.Dom m` and
  `ConeCex.VDim m`; `locallyCompactSpace_RnO` is a theorem, not an instance.
* The projection `W → V` is `ConeCex.proj` (`proj'` its extension by a junk value): the wave-3 name
  `π` collided with `Real.pi`'s notation under `open Real` (audit WP-45p). The machinery (`dg`,
  `A`, `W`, `Dom`, `N`, `chart`, …) now takes the dimension `m` as an argument; no alias is kept
  for the `n = 3`-typed machinery, only for the results above.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

noncomputable section

open Set Filter Topology

namespace Benzecri

namespace ConeCex

/-! ### The matrix `A = diag(4, 1/8, 2, 1, …, 1)`

Lean's cone dimension is `m + 2 + 1` (Benzécri's `n = m + 3 ≥ 3`, base `ConeBase (m + 2)`). -/

variable {m : ℕ}

/-- The coordinate `x` (index `0`) of `ℝ^{m+3}`. -/
def ix (m : ℕ) : Fin (m + 2 + 1) := ⟨0, by omega⟩

/-- The coordinate `y` (index `1`) of `ℝ^{m+3}`. -/
def iy (m : ℕ) : Fin (m + 2 + 1) := ⟨1, by omega⟩

/-- The coordinate `z` (index `2`) of `ℝ^{m+3}`. -/
def iz (m : ℕ) : Fin (m + 2 + 1) := ⟨2, by omega⟩

/-- The coordinate `x` (`i = 0`) or `y` (`i = 1`). -/
def ixy (m : ℕ) (i : Fin 2) : Fin (m + 2 + 1) := ⟨i, by have := i.isLt; omega⟩

/-- The diagonal of `A^k = diag(4, 1/8, 2, 1, …, 1)^k`. -/
def dg (m : ℕ) (k : ℤ) (i : Fin (m + 2 + 1)) : ℝ :=
  if (i : ℕ) = 0 then (4 : ℝ) ^ k else if (i : ℕ) = 1 then (8 : ℝ) ^ (-k)
  else if (i : ℕ) = 2 then (2 : ℝ) ^ k else 1

@[simp] theorem dg_ix (k : ℤ) : dg m k (ix m) = (4 : ℝ) ^ k := by simp [dg, ix]
@[simp] theorem dg_iy (k : ℤ) : dg m k (iy m) = (8 : ℝ) ^ (-k) := by simp [dg, iy]
@[simp] theorem dg_iz (k : ℤ) : dg m k (iz m) = (2 : ℝ) ^ k := by simp [dg, iz]

theorem dg_of_three_le (k : ℤ) {i : Fin (m + 2 + 1)} (hi : 3 ≤ (i : ℕ)) : dg m k i = 1 := by
  simp only [dg]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem dg_pos (k : ℤ) (i : Fin (m + 2 + 1)) : 0 < dg m k i := by
  simp only [dg]
  split_ifs <;> positivity

theorem dg_add (k l : ℤ) (i : Fin (m + 2 + 1)) : dg m (k + l) i = dg m k i * dg m l i := by
  simp only [dg]
  split_ifs <;> simp [zpow_add₀, mul_comm]

theorem dg_zero (i : Fin (m + 2 + 1)) : dg m 0 i = 1 := by
  simp only [dg]
  split_ifs <;> simp

theorem prod_dg (k : ℤ) : ∏ i, dg m k i = 1 := by
  rw [Fin.prod_univ_succ, Fin.prod_univ_succ, Fin.prod_univ_succ]
  have h3 : ∏ i : Fin m, dg m k i.succ.succ.succ = 1 :=
    Finset.prod_eq_one fun i _ => dg_of_three_le k (by simp)
  have h0 : dg m k 0 = (4 : ℝ) ^ k := dg_ix k
  have h1 : dg m k (Fin.succ 0) = (8 : ℝ) ^ (-k) := dg_iy k
  have h2 : dg m k (Fin.succ (Fin.succ 0)) = (2 : ℝ) ^ k := dg_iz k
  rw [h3, h0, h1, h2, mul_one, zpow_neg]
  have h : (4 : ℝ) ^ k * (2 : ℝ) ^ k = (8 : ℝ) ^ k := by
    rw [← mul_zpow]; norm_num
  have h8 : (8 : ℝ) ^ k ≠ 0 := by positivity
  calc (4 : ℝ) ^ k * (((8 : ℝ) ^ k)⁻¹ * 2 ^ k) = (4 ^ k * 2 ^ k) * ((8 : ℝ) ^ k)⁻¹ := by ring
    _ = 1 := by rw [h, mul_inv_cancel₀ h8]

/-- The linear map `diag(dg k)`. -/
def dgLin (m : ℕ) (k : ℤ) : (Fin (m + 2 + 1) → ℝ) →ₗ[ℝ] (Fin (m + 2 + 1) → ℝ) :=
  Matrix.toLin' (Matrix.diagonal (dg m k))

theorem dgLin_apply (k : ℤ) (v : Fin (m + 2 + 1) → ℝ) (i : Fin (m + 2 + 1)) :
    dgLin m k v i = dg m k i * v i := by
  simp [dgLin, Matrix.toLin'_apply, Matrix.mulVec_diagonal]

/-- `A^k` as a linear automorphism of `ℝ^{m+3}`. -/
def Alin (m : ℕ) (k : ℤ) : GLR (m + 2 + 1) :=
  LinearEquiv.ofLinear (dgLin m k) (dgLin m (-k))
    (by ext v i; simp [dgLin_apply, ← mul_assoc, ← dg_add, dg_zero])
    (by ext v i; simp [dgLin_apply, ← mul_assoc, ← dg_add, dg_zero])

theorem Alin_apply (k : ℤ) (v : Fin (m + 2 + 1) → ℝ) (i : Fin (m + 2 + 1)) :
    Alin m k v i = dg m k i * v i :=
  dgLin_apply k v i

/-- **`A^k ∈ GU(m + 3)`** (`det A = 4 · 1/8 · 2 · 1 ⋯ 1 = 1`). -/
def A (m : ℕ) (k : ℤ) : GUR (m + 2 + 1) :=
  ⟨Alin m k, by
    rw [mem_GU, LinearEquiv.coe_det]
    show |LinearMap.det (dgLin m k)| = 1
    rw [dgLin, LinearMap.det_toLin', Matrix.det_diagonal, prod_dg, abs_one]⟩

@[simp] theorem A_val (k : ℤ) (v : RnO (m + 2 + 1)) (i : Fin (m + 2 + 1)) :
    (A m k • v).val i = dg m k i * v.val i :=
  Alin_apply k v.val i

/-- The vector `(a, b, c, 0, …, 0)` of `ℝ^{m+3}`. -/
def vec3 (m : ℕ) (a b c : ℝ) : Fin (m + 2 + 1) → ℝ := fun i =>
  if (i : ℕ) = 0 then a else if (i : ℕ) = 1 then b else if (i : ℕ) = 2 then c else 0

@[simp] theorem vec3_ix (a b c : ℝ) : vec3 m a b c (ix m) = a := by simp [vec3, ix]
@[simp] theorem vec3_iy (a b c : ℝ) : vec3 m a b c (iy m) = b := by simp [vec3, iy]
@[simp] theorem vec3_iz (a b c : ℝ) : vec3 m a b c (iz m) = c := by simp [vec3, iz]

theorem vec3_ne_zero {a b c : ℝ} (hc : c ≠ 0) : vec3 m a b c ≠ 0 := fun h =>
  hc (by simpa using congrFun h (iz m))


/-! ### The open cone `W` and the action of `ℤ` -/

/-- **The open cone `W = {v : v₂ > 0, (v₀, v₁) ≠ (0, 0)}`** of `ℝ^{m+3} − {O}` (coordinates
`x = v₀`, `y = v₁`, `z = v₂`). -/
def W (m : ℕ) : Set (RnO (m + 2 + 1)) :=
  {v | 0 < v.val (iz m) ∧ (v.val (ix m) ≠ 0 ∨ v.val (iy m) ≠ 0)}

theorem isOpen_W : IsOpen (W m) := by
  have hc : ∀ i : Fin (m + 2 + 1), Continuous fun v : RnO (m + 2 + 1) => v.val i := fun i =>
    (continuous_apply i).comp Punctured.continuous_val
  exact (isOpen_lt continuous_const (hc _)).inter
    ((isOpen_ne_fun (hc _) continuous_const).union (isOpen_ne_fun (hc _) continuous_const))

theorem A_mem_W (k : ℤ) {v : RnO (m + 2 + 1)} (hv : v ∈ W m) : A m k • v ∈ W m := by
  obtain ⟨hz, hxy⟩ := hv
  refine ⟨by rw [A_val]; exact mul_pos (dg_pos k _) hz, ?_⟩
  simp only [A_val]
  rcases hxy with h | h
  · exact Or.inl (mul_ne_zero (dg_pos k _).ne' h)
  · exact Or.inr (mul_ne_zero (dg_pos k _).ne' h)

theorem smul_mem_W (c : RPos) {v : RnO (m + 2 + 1)} (hv : v ∈ W m) : c • v ∈ W m := by
  obtain ⟨hz, hxy⟩ := hv
  have hc := Punctured.pos c
  refine ⟨by simpa using mul_pos hc hz, ?_⟩
  simp only [Punctured.val_smul_pos, Pi.smul_apply, smul_eq_mul]
  rcases hxy with h | h
  · exact Or.inl (mul_ne_zero hc.ne' h)
  · exact Or.inr (mul_ne_zero hc.ne' h)

/-- `(1, 0, 1, 0, …, 0)`. -/
def p₁ (m : ℕ) : RnO (m + 2 + 1) := Punctured.mk (vec3 m 1 0 1) (vec3_ne_zero one_ne_zero)

/-- `(0, 1, 1, 0, …, 0)`. -/
def p₂ (m : ℕ) : RnO (m + 2 + 1) := Punctured.mk (vec3 m 0 1 1) (vec3_ne_zero one_ne_zero)

theorem p₁_mem : p₁ m ∈ W m := ⟨by simp [p₁], Or.inl (by simp [p₁])⟩
theorem p₂_mem : p₂ m ∈ W m := ⟨by simp [p₂], Or.inr (by simp [p₂])⟩

/-- The points of `W`, a type of this file. -/
def Dom (m : ℕ) : Type := {v : RnO (m + 2 + 1) // v ∈ W m}

instance : TopologicalSpace (Dom m) := instTopologicalSpaceSubtype

/-- The coordinates of a point of `W`. -/
def Dom.vec (d : Dom m) : Fin (m + 2 + 1) → ℝ := d.1.val

theorem isOpenEmbedding_vec : IsOpenEmbedding (Dom.vec (m := m)) :=
  Punctured.isOpenEmbedding_val.comp (isOpen_W.isOpenEmbedding_subtypeVal)

instance : T2Space (Dom m) := isOpenEmbedding_vec.isEmbedding.t2Space

instance : SecondCountableTopology (Dom m) :=
  isOpenEmbedding_vec.isInducing.secondCountableTopology

instance : LocallyCompactSpace (Dom m) := isOpenEmbedding_vec.locallyCompactSpace

instance : Inhabited (Dom m) := ⟨⟨p₁ m, p₁_mem⟩⟩

instance : SMul (Multiplicative ℤ) (Dom m) :=
  ⟨fun k x => ⟨A m (Multiplicative.toAdd k) • x.1, A_mem_W _ x.2⟩⟩

theorem smul_val (k : Multiplicative ℤ) (x : Dom m) :
    (k • x).1 = A m (Multiplicative.toAdd k) • x.1 :=
  rfl

/-- **`ℤ` acts on `W` by `k · v = A^k v`.** -/
instance : MulAction (Multiplicative ℤ) (Dom m) where
  one_smul x := Subtype.ext (Punctured.ext (funext fun i => by
    rw [smul_val, A_val, toAdd_one, dg_zero, one_mul]))
  mul_smul a b x := Subtype.ext (Punctured.ext (funext fun i => by
    rw [smul_val, smul_val, smul_val, A_val, A_val, A_val, toAdd_mul, dg_add, mul_assoc]))

instance : ContinuousConstSMul (Multiplicative ℤ) (Dom m) :=
  ⟨fun k => continuous_induced_rng.2 ((continuous_const_smul (A m (Multiplicative.toAdd k))).comp
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
instance : ProperlyDiscontinuousSMul (Multiplicative ℤ) (Dom m) where
  finite_disjoint_inter_image {K L} hK hL := by
    set z : Dom m → ℝ := fun d => d.1.val (iz m)
    have hz : Continuous z := (continuous_apply _).comp isOpenEmbedding_vec.continuous
    have hzpos : ∀ d : Dom m, 0 < z d := fun d => d.2.1
    rcases (K ∪ L).eq_empty_or_nonempty with he | hne
    · refine Set.finite_empty.subset fun γ ⟨_, ⟨x, hx, _⟩, _⟩ => ?_
      exact (he ▸ (mem_union_left L hx) : x ∈ (∅ : Set (Dom m)))
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
      show (A m k • x.1).val (iz m) = _
      rw [A_val, dg_iz]
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

/-- **The manifold `V = W/⟨A⟩`** of DEC-122's counterexample, in Benzécri's dimension `m + 3`
(DEC-124: every `n ≥ 3`). -/
def VDim (m : ℕ) : Type := MulAction.orbitRel.Quotient (Multiplicative ℤ) (Dom m)

instance : TopologicalSpace (VDim m) := instTopologicalSpaceQuotient

/-- The projection `W → V` (named `proj`, not `π`: `π` is `Real.pi` under `open Real`). -/
def proj (d : Dom m) : VDim m := Quotient.mk (MulAction.orbitRel (Multiplicative ℤ) (Dom m)) d

/-- **`V` is Hausdorff** (the action is free and properly discontinuous; Mathlib's
`t2Space_of_properlyDiscontinuousSMul_of_t2Space`). -/
instance : T2Space (VDim m) :=
  inferInstanceAs (T2Space (Quotient (MulAction.orbitRel (Multiplicative ℤ) (Dom m))))

theorem continuous_proj : Continuous (proj (m := m)) := continuous_quot_mk

theorem isOpenMap_proj : IsOpenMap (proj (m := m)) := isOpenMap_quotient_mk'_mul

theorem proj_surjective : Function.Surjective (proj (m := m)) := Quotient.mk_surjective

/-- **`V` is second countable.** -/
instance : SecondCountableTopology (VDim m) :=
  TopologicalSpace.Quotient.secondCountableTopology isOpenMap_quotient_mk'_mul

theorem proj_eq_proj_iff {d d' : Dom m} : proj d = proj d' ↔ ∃ k : ℤ, A m k • d'.1 = d.1 := by
  have : proj d = proj d' ↔ MulAction.orbitRel (Multiplicative ℤ) (Dom m) d d' := Quotient.eq
  rw [this, MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨γ, hγ⟩
    exact ⟨Multiplicative.toAdd γ, congrArg Subtype.val hγ⟩
  · rintro ⟨k, hk⟩
    exact ⟨Multiplicative.ofAdd k, Subtype.ext hk⟩

open scoped Classical in
/-- The projection, extended to `ℝ^{m+3} − {O}` (a junk value off `W`). -/
def proj' (w : RnO (m + 2 + 1)) : VDim m := if h : w ∈ W m then proj ⟨w, h⟩ else proj default

theorem proj'_of_mem {w : RnO (m + 2 + 1)} (hw : w ∈ W m) : proj' w = proj ⟨w, hw⟩ := dif_pos hw

theorem proj'_val (d : Dom m) : proj' d.1 = proj d := proj'_of_mem d.2

theorem proj'_eq_proj'_iff {w w' : RnO (m + 2 + 1)} (hw : w ∈ W m) (hw' : w' ∈ W m) :
    proj' w = proj' w' ↔ ∃ k : ℤ, A m k • w' = w := by
  rw [proj'_of_mem hw, proj'_of_mem hw', proj_eq_proj_iff]

theorem proj'_A_smul (k : ℤ) {w : RnO (m + 2 + 1)} (hw : w ∈ W m) : proj' (A m k • w) = proj' w :=
  (proj'_eq_proj'_iff (A_mem_W k hw) hw).2 ⟨k, rfl⟩

theorem continuousOn_proj' : ContinuousOn (proj' (m := m)) (W m) := by
  rw [continuousOn_iff_continuous_restrict]
  have : (W m).restrict proj' = proj := funext fun d => proj'_val d
  rw [this]
  exact continuous_proj

/-! ### The cone charts -/

/-- **The cone neighbourhoods** `N(i, r) = {r z < |v_i| < 2 r z, z > 0}` (`i = 0, 1`): open cones in
`W`, disjoint from their translates by `A^k`, `k ≠ 0` (the ratio `|v_i| / z` is multiplied by `2^k`
for `i = 0`, by `16^{-k}` for `i = 1`). -/
def N (m : ℕ) (i : Fin 2) (r : ℝ) : Set (RnO (m + 2 + 1)) :=
  {w | 0 < w.val (iz m) ∧ r * w.val (iz m) < |w.val (ixy m i)| ∧
    |w.val (ixy m i)| < 2 * r * w.val (iz m)}

theorem isOpen_N (i : Fin 2) (r : ℝ) : IsOpen (N m i r) := by
  have hc : ∀ j : Fin (m + 2 + 1), Continuous fun v : RnO (m + 2 + 1) => v.val j := fun j =>
    (continuous_apply j).comp Punctured.continuous_val
  simp only [N, setOf_and]
  refine (isOpen_lt continuous_const (hc _)).inter ((isOpen_lt ?_ ?_).inter (isOpen_lt ?_ ?_))
  · exact continuous_const.mul (hc _)
  · exact (hc _).abs
  · exact (hc _).abs
  · exact continuous_const.mul (hc _)

theorem N_subset_W {i : Fin 2} {r : ℝ} (hr : 0 < r) : N m i r ⊆ W m := by
  rintro w ⟨hz, h1, -⟩
  have hx : w.val (ixy m i) ≠ 0 := by
    intro h
    rw [h, abs_zero] at h1
    nlinarith
  refine ⟨hz, ?_⟩
  fin_cases i
  · exact Or.inl hx
  · exact Or.inr hx

theorem isConeSet_N (i : Fin 2) (r : ℝ) : IsConeSet (N m i r) := by
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
    dg m k (ixy m i) = (if i = 0 then (2 : ℝ) ^ k else (16 : ℝ) ^ (-k)) * (2 : ℝ) ^ k := by
  fin_cases i
  · simp only [dg, ixy, Fin.zero_eta, Fin.isValue, Fin.val_zero, ↓reduceIte]
    rw [← mul_zpow]; norm_num
  · simp only [dg, ixy, Fin.mk_one, Fin.isValue, Fin.val_one, one_ne_zero, ↓reduceIte]
    rw [zpow_neg, zpow_neg, show (16 : ℝ) = 8 * 2 by norm_num, mul_zpow, mul_inv,
      mul_assoc, inv_mul_cancel₀ (by positivity), mul_one]

/-- **`N(i, r)` is disjoint from its translates**: `w, A^k w ∈ N(i, r)` forces `k = 0`. -/
theorem eq_zero_of_mem_N {i : Fin 2} {r : ℝ} {w : RnO (m + 2 + 1)} (hw : w ∈ N m i r) {k : ℤ}
    (hk : A m k • w ∈ N m i r) : k = 0 := by
  obtain ⟨hz, h1, h2⟩ := hw
  obtain ⟨-, h3, h4⟩ := hk
  simp only [A_val, abs_mul, abs_of_pos (dg_pos k _)] at h3 h4
  rw [dg_iz, dg_div] at *
  set t := (if i = 0 then (2 : ℝ) ^ k else (16 : ℝ) ^ (-k))
  have h2k : 0 < (2 : ℝ) ^ k := by positivity
  set x := |w.val (ixy m i)|
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

theorem injOn_proj' {i : Fin 2} {r : ℝ} (hr : 0 < r) : InjOn (proj' (m := m)) (N m i r) := by
  intro w hw w' hw' h
  obtain ⟨k, hk⟩ := (proj'_eq_proj'_iff (N_subset_W hr hw) (N_subset_W hr hw')).1 h
  have hk0 : k = 0 := eq_zero_of_mem_N hw' (hk ▸ hw)
  subst hk0
  rw [← hk]
  exact Punctured.ext (funext fun j => by rw [A_val, dg_zero, one_mul])


/-- The index of a cone chart: a coordinate `i ∈ {0, 1}` and a ratio `r > 0`. -/
abbrev Idx : Type := Fin 2 × {r : ℝ // 0 < r}

/-- The cone neighbourhood of an index. -/
abbrev Nj (m : ℕ) (j : Idx) : Set (RnO (m + 2 + 1)) := N m j.1 j.2.1

theorem isOpenMap_restrict_proj' (j : Idx) : IsOpenMap ((Nj m j).restrict proj') := by
  intro U hU
  have hU' : IsOpen (Subtype.val '' U : Set (RnO (m + 2 + 1))) :=
    (isOpen_N _ _).isOpenMap_subtype_val U hU
  have : (Nj m j).restrict proj' '' U = proj '' {d : Dom m | d.1 ∈ Subtype.val '' U} := by
    ext x
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨⟨w.1, N_subset_W j.2.2 w.2⟩, ⟨w, hw, rfl⟩,
        (proj'_val ⟨w.1, N_subset_W j.2.2 w.2⟩).symm⟩
    · rintro ⟨d, ⟨w, hw, hwd⟩, rfl⟩
      refine ⟨w, hw, ?_⟩
      show proj' w.1 = proj d
      rw [hwd, proj'_val]
  rw [this]
  exact isOpenMap_proj _ (hU'.preimage (continuous_subtype_val : Continuous fun d : Dom m => d.1))

/-- The inverse of a cone chart: `proj'` restricted to `N(i, r)`. -/
def chartInv (m : ℕ) (j : Idx) : OpenPartialHomeomorph (RnO (m + 2 + 1)) (VDim m) :=
  OpenPartialHomeomorph.ofContinuousOpenRestrict ((injOn_proj' j.2.2).toPartialEquiv proj' (Nj m j))
    (continuousOn_proj'.mono (N_subset_W j.2.2)) (isOpenMap_restrict_proj' j) (isOpen_N _ _)

/-- **The cone chart `f_N = (proj|N)⁻¹ : proj(N) → N`** (audit WP-45n, `cone_charts_3deg`). -/
def chart (m : ℕ) (j : Idx) : OpenPartialHomeomorph (VDim m) (RnO (m + 2 + 1)) :=
  (chartInv m j).symm

theorem chart_target (j : Idx) : (chart m j).target = Nj m j := rfl

theorem chart_source (j : Idx) : (chart m j).source = proj' '' Nj m j := rfl

theorem chart_symm_apply (j : Idx) (w : RnO (m + 2 + 1)) : (chart m j).symm w = proj' w := rfl

theorem chart_proj' (j : Idx) {w : RnO (m + 2 + 1)} (hw : w ∈ Nj m j) : chart m j (proj' w) = w :=
  (chartInv m j).left_inv hw

theorem proj'_chart (j : Idx) {x : VDim m} (hx : x ∈ (chart m j).source) :
    proj' (chart m j x) = x :=
  (chart m j).left_inv hx

theorem exists_idx {w : RnO (m + 2 + 1)} (hw : w ∈ W m) : ∃ j : Idx, w ∈ Nj m j := by
  obtain ⟨hz, hxy⟩ := hw
  have key : ∀ i : Fin 2, w.val (ixy m i) ≠ 0 → ∃ j : Idx, w ∈ Nj m j := by
    intro i hi
    have hx : 0 < |w.val (ixy m i)| := abs_pos.2 hi
    refine ⟨(i, ⟨2 * |w.val (ixy m i)| / (3 * w.val (iz m)), by positivity⟩), hz, ?_, ?_⟩
    · show 2 * |w.val (ixy m i)| / (3 * w.val (iz m)) * w.val (iz m) < _
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith
    · show _ < 2 * (2 * |w.val (ixy m i)| / (3 * w.val (iz m))) * w.val (iz m)
      rw [mul_div_assoc', div_mul_eq_mul_div, lt_div_iff₀ (by positivity)]
      nlinarith
  rcases hxy with h | h
  · exact key 0 h
  · exact key 1 h

/-- The chosen index at a point of `V`. -/
def idxAt (x : VDim m) : Idx := (exists_idx (Quotient.out x : Dom m).2).choose

theorem mem_chart_idxAt_source (x : VDim m) : x ∈ (chart m (idxAt x)).source := by
  refine ⟨(Quotient.out x : Dom m).1, (exists_idx (Quotient.out x : Dom m).2).choose_spec, ?_⟩
  rw [proj'_val]
  exact Quotient.out_eq x

/-- **The charted space of `V`**: the cone charts `f_N` (stated over `RnO (m + 2 + 1)`, the form
`ConeBase (m + 2) V` asks for). -/
instance : ChartedSpace (RnO (m + 2 + 1)) (VDim m) where
  atlas := range (chart m)
  chartAt x := chart m (idxAt x)
  mem_chart_source := mem_chart_idxAt_source
  chart_mem_atlas _ := mem_range_self _

/-- **The transitions are the `A^k`**: near a point of the overlap of two cone charts,
`f_{N'} = A^k ∘ f_N`. -/
theorem chart_transition (j₁ j₂ : Idx) {x : VDim m} (hx₁ : x ∈ (chart m j₁).source)
    (hx₂ : x ∈ (chart m j₂).source) :
    ∃ k : ℤ, ∀ᶠ z in 𝓝 x, chart m j₂ z = A m k • chart m j₁ z := by
  obtain ⟨w₁, hw₁, rfl⟩ := hx₁
  obtain ⟨w₂, hw₂, hw⟩ := hx₂
  obtain ⟨k, hk⟩ := (proj'_eq_proj'_iff (N_subset_W j₂.2.2 hw₂) (N_subset_W j₁.2.2 hw₁)).1 hw
  refine ⟨k, ?_⟩
  have hc : ContinuousAt (fun z => A m k • chart m j₁ z) (proj' w₁) :=
    (continuous_const_smul _).continuousAt.comp ((chart m j₁).continuousAt ⟨w₁, hw₁, rfl⟩)
  have hmem : A m k • chart m j₁ (proj' w₁) ∈ Nj m j₂ := by rw [chart_proj' j₁ hw₁, hk]; exact hw₂
  filter_upwards [(chart m j₁).open_source.mem_nhds ⟨w₁, hw₁, rfl⟩,
    hc.eventually ((isOpen_N _ _).mem_nhds hmem)] with z hz hz'
  have hW : chart m j₁ z ∈ W m := N_subset_W j₁.2.2 ((chart m j₁).map_source hz)
  calc chart m j₂ z = chart m j₂ (proj' (A m k • chart m j₁ z)) := by
        rw [proj'_A_smul k hW, proj'_chart j₁ hz]
    _ = A m k • chart m j₁ z := chart_proj' j₂ hz'

/-- **`V` is an affine conical manifold** — a `(GU(m + 3), ℝ^{m+3} − {O})`-manifold… -/
instance : HasGroupoid (VDim m) (coneGroupoid (m + 2 + 1)) where
  compatible := by
    rintro _ _ ⟨j₁, rfl⟩ ⟨j₂, rfl⟩
    refine symm_trans_mem_gxGroupoid fun x hx => ?_
    obtain ⟨k, hk⟩ := chart_transition j₁ j₂ hx.1 hx.2
    exact ⟨A m k, hk⟩

theorem isConeChart_chart (j : Idx) : IsConeChart (m + 2 + 1) (chart m j) :=
  ⟨(coneGroupoid (m + 2 + 1)).subset_maximalAtlas (mem_range_self j), isConeSet_N _ _⟩

/-- … **with cone charts** (Déf. 2, 3°). -/
instance : HasConeCharts (m + 2 + 1) (VDim m) :=
  ⟨fun x => ⟨chart m (idxAt x), isConeChart_chart _, mem_chart_idxAt_source x⟩⟩

/-- **The positive homotheties of `V`** (Déf. 3) are induced by those of `W`:
`λ proj(v) = proj(λ v)`. -/
theorem posSMul_proj' (c : RPos) {w : RnO (m + 2 + 1)} (hw : w ∈ W m) :
    posSMul (m + 2 + 1) c (proj' w) = proj' (c • w) := by
  obtain ⟨j, hj⟩ := exists_idx hw
  refine (posSMul_eq (isConeChart_chart j) ⟨w, hj, rfl⟩ c).trans ?_
  rw [chart_proj' j hj, chart_symm_apply]


/-! ### `V` is a « variété »: connected, and paracompact -/

/-- `W` is connected: it is the image of `(ℝ² − {O}) × ]0, ∞[ × ℝ^{m+3}` under
`(q, t, u) ↦ (q₀, q₁, t, u₃, …, u_{m+2})`. -/
instance : ConnectedSpace (Dom m) := by
  have h2 : ConnectedSpace {q : Fin 2 → ℝ // q ≠ 0} := by
    have : IsConnected ({0}ᶜ : Set (Fin 2 → ℝ)) :=
      isConnected_compl_singleton_of_one_lt_rank (by rw [rank_fin_fun]; norm_num) 0
    exact isConnected_iff_connectedSpace.1 this
  have hI : ConnectedSpace {t : ℝ // 0 < t} := isConnected_iff_connectedSpace.1 isConnected_Ioi
  let f : {q : Fin 2 → ℝ // q ≠ 0} × {t : ℝ // 0 < t} × (Fin (m + 2 + 1) → ℝ) →
      Fin (m + 2 + 1) → ℝ := fun p i =>
    if (i : ℕ) = 0 then p.1.1 0 else if (i : ℕ) = 1 then p.1.1 1
    else if (i : ℕ) = 2 then p.2.1.1 else p.2.2 i
  have hfz : ∀ p, f p (iz m) = p.2.1.1 := fun p => by simp [f, iz]
  have hfx : ∀ p, f p (ix m) = p.1.1 0 := fun p => by simp [f, ix]
  have hfy : ∀ p, f p (iy m) = p.1.1 1 := fun p => by simp [f, iy]
  have hmem : ∀ p, f p ≠ 0 := fun p h => p.2.1.2.ne' (by simpa [hfz] using congrFun h (iz m))
  have hW : ∀ p, Punctured.mk (f p) (hmem p) ∈ W m := fun p => by
    refine ⟨by simpa [hfz] using p.2.1.2, ?_⟩
    by_contra h
    push Not at h
    apply p.1.2
    funext i
    fin_cases i
    · simpa [hfx] using h.1
    · simpa [hfy] using h.2
  let F : {q : Fin 2 → ℝ // q ≠ 0} × {t : ℝ // 0 < t} × (Fin (m + 2 + 1) → ℝ) → Dom m :=
    fun p => ⟨Punctured.mk (f p) (hmem p), hW p⟩
  have hF : Continuous F := by
    refine continuous_induced_rng.2 (continuous_induced_rng.2 ?_)
    show Continuous f
    refine continuous_pi fun i => ?_
    simp only [f]
    split_ifs
    · exact (continuous_apply 0).comp (continuous_subtype_val.comp continuous_fst)
    · exact (continuous_apply 1).comp (continuous_subtype_val.comp continuous_fst)
    · exact continuous_subtype_val.comp (continuous_fst.comp continuous_snd)
    · exact (continuous_apply i).comp (continuous_snd.comp continuous_snd)
  have hsurj : Function.Surjective F := by
    intro d
    have hz : 0 < d.1.val (iz m) := d.2.1
    have hq : (![d.1.val (ix m), d.1.val (iy m)] : Fin 2 → ℝ) ≠ 0 := by
      intro h
      rcases d.2.2 with h' | h'
      · exact h' (by simpa using congrFun h 0)
      · exact h' (by simpa using congrFun h 1)
    refine ⟨(⟨_, hq⟩, ⟨_, hz⟩, d.1.val), Subtype.ext (Punctured.ext (funext fun i => ?_))⟩
    show f _ i = d.1.val i
    simp only [f]
    split_ifs with h0 h1 h2
    · simp [show i = ix m from Fin.ext h0]
    · simp [show i = iy m from Fin.ext h1]
    · simp [show i = iz m from Fin.ext h2]
    · rfl
  exact hsurj.connectedSpace hF

/-- **`V` is connected.** -/
instance : ConnectedSpace (VDim m) := proj_surjective.connectedSpace continuous_proj

theorem locallyCompactSpace_RnO (k : ℕ) : LocallyCompactSpace (RnO k) :=
  Punctured.isOpenEmbedding_val.locallyCompactSpace

theorem locallyCompactSpace_RnO3 : LocallyCompactSpace (RnO 3) := locallyCompactSpace_RnO 3

/-- `V` is locally compact (it is charted on `ℝ^{m+3} − {O}`). -/
instance : LocallyCompactSpace (VDim m) :=
  haveI := locallyCompactSpace_RnO (m + 2 + 1)
  ChartedSpace.locallyCompactSpace (RnO (m + 2 + 1)) (VDim m)

/-- **`V` is paracompact** (Hausdorff, locally compact, second countable). -/
example : ParacompactSpace (VDim m) := inferInstance

/-! ### The base is not Hausdorff -/

/-- `(1, 16^{-k}, 1, 0, …, 0)`. -/
def yv (m k : ℕ) : RnO (m + 2 + 1) :=
  Punctured.mk (vec3 m 1 ((16 : ℝ)⁻¹ ^ k) 1) (vec3_ne_zero one_ne_zero)

/-- `(2^{-k}, 1, 1, 0, …, 0)`. -/
def zv (m k : ℕ) : RnO (m + 2 + 1) :=
  Punctured.mk (vec3 m ((2 : ℝ)⁻¹ ^ k) 1 1) (vec3_ne_zero one_ne_zero)

theorem yv_mem (k : ℕ) : yv m k ∈ W m := ⟨by simp [yv], Or.inl (by simp [yv])⟩
theorem zv_mem (k : ℕ) : zv m k ∈ W m := ⟨by simp [zv], Or.inr (by simp [zv])⟩

theorem tendsto_yv : Tendsto (yv m) atTop (𝓝 (p₁ m)) := by
  rw [Punctured.isEmbedding_val.tendsto_nhds_iff, tendsto_pi_nhds]
  intro i
  simp only [Function.comp_def, yv, p₁, Punctured.val_mk, vec3]
  split_ifs
  · exact tendsto_const_nhds
  · exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  · exact tendsto_const_nhds
  · exact tendsto_const_nhds

theorem tendsto_zv : Tendsto (zv m) atTop (𝓝 (p₂ m)) := by
  rw [Punctured.isEmbedding_val.tendsto_nhds_iff, tendsto_pi_nhds]
  intro i
  simp only [Function.comp_def, zv, p₂, Punctured.val_mk, vec3]
  split_ifs
  · exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  · exact tendsto_const_nhds
  · exact tendsto_const_nhds
  · exact tendsto_const_nhds

/-- **`2^k y_k = A^k z_k`, so `proj(2^k y_k) = proj(z_k)`** (`z_k = (2^{-k}, 1, 1, 0, …, 0)`): the
two sequences have the same image in `B`. -/
theorem proj'_smul_yv (k : ℕ) :
    proj' (Punctured.posUnit ((2 : ℝ) ^ k) (by positivity) • yv m k) = proj' (zv m k) := by
  refine (proj'_eq_proj'_iff (smul_mem_W _ (yv_mem k)) (zv_mem k)).2 ⟨k, ?_⟩
  refine Punctured.ext (funext fun i => ?_)
  rw [A_val]
  simp only [zv, yv, dg, vec3, Punctured.val_smul_pos, Punctured.coe_posUnit, Punctured.val_mk,
    Pi.smul_apply, smul_eq_mul]
  split_ifs
  · rw [zpow_natCast, show (4 : ℝ) = 2 * 2 by norm_num, mul_pow, inv_pow]
    field_simp
  · rw [zpow_neg, zpow_natCast, inv_pow, show (16 : ℝ) = 2 * 8 by norm_num, mul_pow]
    field_simp
  · rw [zpow_natCast]
  · simp

/-- **THE FINDING (DEC-122, every `n ≥ 3` by DEC-124): the base `B = V/ℝ⁺` of the Hausdorff,
second countable, connected affine conical `(m + 3)`-manifold `V` is not Hausdorff.** The rays
`[(1, 0, …)]` and `[(0, 1, …)]` are not separated: `y_k = proj(1, 16^{-k}, 1, 0, …) → proj(1, 0,
1, 0, …)` while `2^k · y_k = proj(2^{-k}, 1, 1, 0, …) → proj(0, 1, 1, 0, …)`, and
`proj(0, 1, 1, 0, …) ∉ ℝ₊* · proj(1, 0, 1, 0, …)`. -/
theorem not_t2Space_coneBase_dim (m : ℕ) : ¬ T2Space (ConeBase (m + 2) (VDim m)) := by
  intro hT
  have hc₁ : Tendsto (fun k => ConeBase.mk (n := m + 2) (proj' (yv m k))) atTop
      (𝓝 (ConeBase.mk (proj' (p₁ m)))) :=
    (ConeBase.continuous_mk.tendsto _).comp
      ((continuousOn_proj'.continuousAt (isOpen_W.mem_nhds p₁_mem)).tendsto.comp tendsto_yv)
  have hc₂ : Tendsto (fun k => ConeBase.mk (n := m + 2) (proj' (zv m k))) atTop
      (𝓝 (ConeBase.mk (proj' (p₂ m)))) :=
    (ConeBase.continuous_mk.tendsto _).comp
      ((continuousOn_proj'.continuousAt (isOpen_W.mem_nhds p₂_mem)).tendsto.comp tendsto_zv)
  have heq : ∀ k, ConeBase.mk (n := m + 2) (proj' (yv m k)) = ConeBase.mk (proj' (zv m k)) :=
    fun k => by rw [← proj'_smul_yv k, ← posSMul_proj' _ (yv_mem k), ConeBase.mk_posSMul]
  have hb : ConeBase.mk (n := m + 2) (proj' (p₁ m)) = ConeBase.mk (proj' (p₂ m)) :=
    tendsto_nhds_unique hc₁ (hc₂.congr fun k => (heq k).symm)
  obtain ⟨c, hc⟩ := ConeBase.mk_eq_mk_iff.1 hb
  rw [posSMul_proj' c p₂_mem] at hc
  obtain ⟨k, hk⟩ := (proj'_eq_proj'_iff (smul_mem_W c p₂_mem) p₁_mem).1 hc
  have := congrArg (fun v : RnO (m + 2 + 1) => v.val (ix m)) hk
  simp [p₁, p₂, A_val] at this
  exact absurd this (by positivity)


/-! ### Consequences: the three statements that fail, in every dimension `n ≥ 3` -/

/-- **The action of `ℝ₊*` on `V` is not proper** (`ConeBase.t2Space_iff_properSMul`). -/
theorem not_properSMul_dim (m : ℕ) :
    ¬ @ProperSMul RPos (VDim m) _ _ _ (coneMulAction (m + 2 + 1) (VDim m)) :=
  fun h => not_t2Space_coneBase_dim m (ConeBase.t2Space_of_properSMul h)

/-- **`V → B` has no continuous section** (a section would embed `B` in the Hausdorff `V`,
`ConeBase.t2Space_of_section`). -/
theorem not_exists_section_dim (m : ℕ) :
    ¬ ∃ σ : ConeBase (m + 2) (VDim m) → VDim m, Continuous σ ∧ ∀ b, ConeBase.mk (σ b) = b := by
  rintro ⟨σ, hσ, hmk⟩
  exact not_t2Space_coneBase_dim m (ConeBase.t2Space_of_section hσ hmk)

/-- **`V` is not homeomorphic to `B × ℝ₊*`**, by any homeomorphism (over `B` or not). -/
theorem isEmpty_homeomorph_dim (m : ℕ) : IsEmpty (VDim m ≃ₜ ConeBase (m + 2) (VDim m) × RPos) :=
  ⟨fun T => not_t2Space_coneBase_dim m (ConeBase.t2Space_of_homeomorph T)⟩

/-- **§ 2 Prop. 2 read with a « variété » base** (plan F6: « structure localement projective » on a
variété, Déf. 12), as a `Prop` (kb/0022), in Lean's base dimension `n` (Benzécri's cone dimension
`n + 1`): the base of every Hausdorff, second countable, connected affine conical
`(n + 1)`-manifold is Hausdorff. FALSE for every `n ≥ 2`, i.e. Benzécri's `n + 1 ≥ 3`
(`not_prop2HausdorffBaseAsRead_dim`); the corrected form is
`ConeBase.existsUnique_baseStructure_of_properSMul`. -/
def Prop2HausdorffBaseAsReadDim (n : ℕ) : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [ChartedSpace (RnO (n + 1)) X]
    [HasGroupoid X (coneGroupoid (n + 1))] [HasConeCharts (n + 1) X] [T2Space X]
    [SecondCountableTopology X] [ConnectedSpace X], T2Space (ConeBase n X)

/-- **FINDING (DEC-122) against § 2 Prop. 2** (`bzprop:c1s2p2_base_cone`), in every Benzécri
dimension `n + 1 ≥ 3` (DEC-124). -/
theorem not_prop2HausdorffBaseAsRead_dim {n : ℕ} (hn : 2 ≤ n) :
    ¬ Prop2HausdorffBaseAsReadDim n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  exact fun h => not_t2Space_coneBase_dim m (h (VDim m))

/-- **Déf. 3's « cet espace fibré est topologiquement trivial », as printed** (kb/0022), in Lean's
base dimension `n`: every Hausdorff, second countable, connected affine conical `(n + 1)`-manifold
`X` is `ℝ₊*`-equivariantly homeomorphic to `B × ℝ₊*` over `B`. FALSE for every `n ≥ 2`
(`not_def3TrivialAsPrinted_dim`); the corrected form is
`ConeBase.exists_trivialization_of_properSMul`. -/
def Def3TrivialAsPrintedDim (n : ℕ) : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [ChartedSpace (RnO (n + 1)) X]
    [HasGroupoid X (coneGroupoid (n + 1))] [HasConeCharts (n + 1) X] [T2Space X]
    [SecondCountableTopology X] [ConnectedSpace X],
    ∃ T : X ≃ₜ ConeBase n X × RPos, (∀ m, (T m).1 = ConeBase.mk m) ∧
      ∀ (c : RPos) (m : X), T (posSMul (n + 1) c m) = ((T m).1, c * (T m).2)

/-- **FINDING (DEC-122) against Déf. 3** (`bzdef:c1s2d3_homotheties_positives`), in every Benzécri
dimension `n + 1 ≥ 3` (DEC-124). -/
theorem not_def3TrivialAsPrinted_dim {n : ℕ} (hn : 2 ≤ n) : ¬ Def3TrivialAsPrintedDim n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  intro h
  obtain ⟨T, -, -⟩ := h (VDim m)
  exact (isEmpty_homeomorph_dim m).false T

/-- **The p. 241 inference, as printed** (kb/0022): « si $V$ est supposé para-compact, on peut donc
construire une section de $V$ au-dessus de $B$ », for every Hausdorff, second countable, connected,
paracompact affine conical `(n + 1)`-manifold. FALSE for every `n ≥ 2`
(`not_p241SectionAsPrinted_dim`); the corrected form is `ConeBase.exists_section_of_properSMul`. -/
def P241SectionAsPrintedDim (n : ℕ) : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [ChartedSpace (RnO (n + 1)) X]
    [HasGroupoid X (coneGroupoid (n + 1))] [HasConeCharts (n + 1) X] [T2Space X]
    [SecondCountableTopology X] [ConnectedSpace X] [ParacompactSpace X],
    ∃ σ : ConeBase n X → X, Continuous σ ∧ ∀ b, ConeBase.mk (σ b) = b

/-- **FINDING (DEC-122) against the p. 241 prose**, in every Benzécri dimension `n + 1 ≥ 3`
(DEC-124): `V` is paracompact and has no section. -/
theorem not_p241SectionAsPrinted_dim {n : ℕ} (hn : 2 ≤ n) : ¬ P241SectionAsPrintedDim n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  exact fun h => not_exists_section_dim m (h (VDim m))

/-- **DEC-122's counterexample in one statement, in every dimension (DEC-124)**: for Benzécri's
`n = m + 3 ≥ 3`, `V = W/⟨A⟩` is a Hausdorff, second countable, connected, paracompact affine
conical `n`-manifold whose base is not Hausdorff, whose `ℝ₊*`-action is not proper, and which has
no section and is not homeomorphic to `B × ℝ₊*`. -/
theorem counterexample_dim (m : ℕ) :
    T2Space (VDim m) ∧ SecondCountableTopology (VDim m) ∧ ConnectedSpace (VDim m) ∧
      ParacompactSpace (VDim m) ∧ ¬ T2Space (ConeBase (m + 2) (VDim m)) ∧
      ¬ @ProperSMul RPos (VDim m) _ _ _ (coneMulAction (m + 2 + 1) (VDim m)) ∧
      (¬ ∃ σ : ConeBase (m + 2) (VDim m) → VDim m, Continuous σ ∧ ∀ b, ConeBase.mk (σ b) = b) ∧
      IsEmpty (VDim m ≃ₜ ConeBase (m + 2) (VDim m) × RPos) :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance, not_t2Space_coneBase_dim m,
    not_properSMul_dim m, not_exists_section_dim m, isEmpty_homeomorph_dim m⟩


/-! ### Benzécri's `n = 3` (Lean's `ConeBase 2 V`): the specialisations -/

/-- **The manifold `V = W/⟨A⟩` in Benzécri's dimension `n = 3`**: `W = {(x, y, z) : z > 0,
(x, y) ≠ (0, 0)} ⊂ ℝ³ − {O}`, `A = diag(4, 1/8, 2)` (`VDim 0`). -/
abbrev V : Type := VDim 0

/-- **THE FINDING (DEC-122), `n = 3`**: the base of `V` is not Hausdorff. -/
theorem not_t2Space_coneBase : ¬ T2Space (ConeBase 2 V) := not_t2Space_coneBase_dim 0

/-- **The action of `ℝ₊*` on `V` is not proper** (`n = 3`). -/
theorem not_properSMul : ¬ @ProperSMul RPos V _ _ _ (coneMulAction (2 + 1) V) :=
  not_properSMul_dim 0

/-- **`V → B` has no continuous section** (`n = 3`). -/
theorem not_exists_section :
    ¬ ∃ σ : ConeBase 2 V → V, Continuous σ ∧ ∀ b, ConeBase.mk (σ b) = b :=
  not_exists_section_dim 0

/-- **`V` is not homeomorphic to `B × ℝ₊*`** (`n = 3`). -/
theorem isEmpty_homeomorph : IsEmpty (V ≃ₜ ConeBase 2 V × RPos) := isEmpty_homeomorph_dim 0

/-- **§ 2 Prop. 2 read with a « variété » base**, for affine conical 3-manifolds
(`Prop2HausdorffBaseAsReadDim 2`). FALSE (`not_prop2HausdorffBaseAsRead`). -/
def Prop2HausdorffBaseAsRead : Prop := Prop2HausdorffBaseAsReadDim 2

/-- **FINDING (DEC-122) against § 2 Prop. 2** (`bzprop:c1s2p2_base_cone`), `n = 3`. -/
theorem not_prop2HausdorffBaseAsRead : ¬ Prop2HausdorffBaseAsRead :=
  not_prop2HausdorffBaseAsRead_dim le_rfl

/-- **Déf. 3's « topologiquement trivial », as printed**, for affine conical 3-manifolds
(`Def3TrivialAsPrintedDim 2`). FALSE (`not_def3TrivialAsPrinted`). -/
def Def3TrivialAsPrinted : Prop := Def3TrivialAsPrintedDim 2

/-- **FINDING (DEC-122) against Déf. 3** (`bzdef:c1s2d3_homotheties_positives`), `n = 3`. -/
theorem not_def3TrivialAsPrinted : ¬ Def3TrivialAsPrinted := not_def3TrivialAsPrinted_dim le_rfl

/-- **The p. 241 inference, as printed**, for affine conical 3-manifolds
(`P241SectionAsPrintedDim 2`). FALSE (`not_p241SectionAsPrinted`). -/
def P241SectionAsPrinted : Prop := P241SectionAsPrintedDim 2

/-- **FINDING (DEC-122) against the p. 241 prose**, `n = 3`. -/
theorem not_p241SectionAsPrinted : ¬ P241SectionAsPrinted :=
  not_p241SectionAsPrinted_dim le_rfl

/-- **DEC-122's counterexample in one statement, `n = 3`** (`counterexample_dim 0`). -/
theorem counterexample :
    T2Space V ∧ SecondCountableTopology V ∧ ConnectedSpace V ∧ ParacompactSpace V ∧
      ¬ T2Space (ConeBase 2 V) ∧ ¬ @ProperSMul RPos V _ _ _ (coneMulAction (2 + 1) V) ∧
      (¬ ∃ σ : ConeBase 2 V → V, Continuous σ ∧ ∀ b, ConeBase.mk (σ b) = b) ∧
      IsEmpty (V ≃ₜ ConeBase 2 V × RPos) :=
  counterexample_dim 0

end ConeCex
end Benzecri
