import Benzecri.Projective.Subvariety
import Benzecri.Projective.Groups
import Benzecri.Affine.Basic

/-!
# `Benzecri.Projective.Hemisphere` — the affine structure of an open hemisphere (Déf. 6)

J.-P. Benzécri, *Sur les variétés localement affines et localement projectives*, Bull. SMF 88
(1960) 229–332, Chapter 1 § 1, journal pp. 235–236; transcription
`papers/benzecri/legacy/labeled/benzecri1960_ch1.tex`. Package WP-45f (wave 2, layer L2).

* **`bzdef:c1s1d6_structure_affine_hemisphere`** — `benzecri1960_ch1.tex:222` (Déf. 6,
  l.222–232, p. 235). The translation space `L(E/N, N)` (`Benzecri.Sphere.HemiTrans l`,
  `N = l⁻¹(O)`), the formula `m + u = s(M + u(q(M)))` (`Benzecri.Sphere.hvadd`), its independence of
  the representative `M ∈ F(m)` (`hvadd_mk`, `mk_transl_eq_of_mk_eq`, `coe_vadd_eq`), the action on
  `H` (`instAddActionHemi`), simply transitive on EVERY open hemisphere (`isSimplyTransitive_hemi`,
  Déf. 1 as printed), an affine space in DEC-114's reading of Déf. 1 iff `H ≠ ∅`
  (`isAffineSpace_hemi_iff`), Mathlib's `AddTorsor` (`instAddTorsorHemi`). The structure depends
  only on `H`, not on the equation `l`: same kernel (`ker_eq_of_openHemisphere_eq`), and a linear
  isomorphism `L(E/N, N) ≃ L(E/N', N')` intertwining the two actions (`hemiTransEquiv`,
  `coe_vadd_hemiTransEquiv`, `hemi_vadd_indep`).
* The sentence of p. 236, `benzecri1960_ch1.tex:280` (no label, « Un hémisphère ouvert de $S(n)$ est
  muni d'une structure affine isomorphe à celle de $\R^n$ (cf. déf. 6) »): the chart
  `hemiEquivLevelOne : H ≃ᵃ[ℝ] {l = 1}` onto the affine hyperplane `l = 1` (an `AffineSubspace` of
  direction `N`), and `nonempty_hemi_affineEquiv : Nonempty (H ≃ᵃ[ℝ] ℝⁿ)` for `dim E = n + 1`.
* Groundwork for the Remarque `bzrem:c1s1r1_affine_vers_projective` (`benzecri1960_ch1.tex:319`,
  certified and marked in `Structure/Basic`): the elements of `GS(E)` preserving `H`
  act on it by affine maps (`isAffine_hemiMap`, `isAffine_gse_restrict`, after `mapsTo_smul_openHemisphere_iff`:
  `g` preserves `H` iff `l ∘ g = c l`, `c > 0`); the standard chart `j : ℝⁿ → S(n)`,
  `y ↦ s(y, 1)` (`hemiChart`), an open embedding onto `H₀ = {x_{n+1} > 0}`
  (`isOpenEmbedding_hemiChart`, `range_hemiChart`) and an affine bijection `ℝⁿ → H₀`
  (`isAffine_hemiChartH`, `bijective_hemiChartH`); the injective hom `φ : GA(n) →* GS(n)`
  (`affToGS`, `affToGS_injective`) with `j(f y) = φ(f) • j(y)` (`hemiChart_apply_eq_smul`); and
  **every affine injection `j : ℝⁿ → H` into ANY open hemisphere of `S(n)` is `σ • hemiChart` for
  some `σ ∈ GS(n)`** (`exists_eq_smul_hemiChart`), which is what makes the Remarque's structure
  independent of `j` (`Structure/Basic`).

> **Déf. 6.** Sur tout hémisphère ouvert $H$ de $S(E)$, nous allons définir une structure d'espace
> affin.
>
> Soient $l$ une équation de $H$ et $N$ le sous-espace vectoriel $l^{-1}(O)$; le groupe des
> translations de $H$ sera l'espace vectoriel $L(E/N, N)$ opérant sur $H$ comme suit :
>
> Soient $m\in H$, $u\in L(E/N, N)$, $M\in F(m)$, $q$ l'application de $E$ sur son quotient $E/N$
> $$m+u=s(M+u(q(M)))$$
> Il est clair que cette expression est indépendante du choix de $m$.
>
> (p. 236) Un hémisphère ouvert de $S(n)$ est muni d'une structure affine isomorphe à celle de
> $\R^n$ (*cf.* déf. 6).

**Notation.** Mathlib writes the action on the left, `u +ᵥ m`, for Benzécri's `m + u`; `L(E/N, N)`
is `(E ⧸ ker l) →ₗ[ℝ] ker l`; `q` is `(ker l).mkQ` (`hq l`); `l̄ : E/N → ℝ` is `lbar l`.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `H` an open hemisphere of `S(E)`, `l` an equation of `H` | ✓ carried: `H = openHemisphere l` for `l : Module.Dual ℝ E` (Déf. 5's `F(H) = l⁻¹(ℝ⁺)` is `F_openHemisphere`); the openness of `H` is never used, so no topology is assumed |
| `E` a real vector space | ✓ carried, any dimension, for Déf. 6; `dim E = n + 1` only for the p. 236 sentence |
| « structure d'espace affin » (Déf. 1) | reading (DEC-114/DEC-120, ruled): as printed (`IsSimplyTransitive`, every `l`) and in DEC-114's reading (`IsAffineSpace`, nonempty), the latter iff `l ≠ 0`, Déf. 5's reading (DEC-114, accepted by DEC-120) |
| independence of the equation `l` (« Soient $l$ une équation de $H$ ») | ✓ carried: `hemi_vadd_indep` |
| `M ∈ F(m)` arbitrary | ✓ carried: the formula holds for every representative (`coe_vadd_eq`) |

## SCOPE (disclosed)

* **Mark (rests on DEC-114/DEC-120).** Déf. 6 is marked: the action is defined by the printed
  formula, proved independent of the representative and of the equation, and simply transitive on
  every open hemisphere with no hypothesis (Déf. 1 as printed); in DEC-114's reading of Déf. 1 (an
  affine space is nonempty) it is an affine space exactly when `l ≠ 0`, which is DEC-114's reading
  of Déf. 5 (« l'hyperplan fermé $h$ » forces `l ≠ 0`). The two readings are the author's rulings
  and agree here, so no hypothesis is added to Déf. 6; DEC-120 accepts the mark on that basis.
* **`[sic]`, not a finding.** « indépendante du choix de $m$ » is read « de $M$ », as the
  transcription's comment says.
* `HemiTrans l` is indexed by the equation `l`, not by `H`: two equations of the same `H` are
  positive multiples (`openHemisphere_eq_iff`) and have the same kernel
  (`ker_eq_of_openHemisphere_eq`); the types `HemiTrans l` and `HemiTrans (c • l)` are not
  definitionally equal, and the independence of the equation is the linear isomorphism
  `hemiTransEquiv`, which leaves the formula `M ↦ M + u(q M)` unchanged (`transl_hemiTransEquiv`,
  by `rfl`) and intertwines the actions (`coe_vadd_hemiTransEquiv`).
* Outside `H`, `hvadd` is extended by the same formula (and by the identity where
  `M + u(q M) = 0`, which never happens on `H`); only its restriction to `H` is Déf. 6.
* The topology of `H` and continuity of the action are not used by Déf. 6; the standard chart
  `hemiChart` is proved an open embedding, which `Structure/Basic` uses for the Remarque.
* The converse of `isAffine_hemiMap` is proved in the form the Remarque uses: an affine injection
  `ℝⁿ → H` is the restriction of an element of `GS(n)` composed with the standard chart
  (`exists_eq_smul_hemiChart`); the group isomorphism `GA(n) ≅ Stab_{GS(n)}(H₀)` is not stated.
* Generic helpers (`mk_eq_mk_of_eq`, the `Fin.snoc`/`Fin.init` lemmas, `GAR.apply_eq`) are
  `private`; `affLin`, `affToGL`, `affToGS` belong to `Projective/Groups` at graduation (REPORT
  `upstream_moves`).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

noncomputable section

open Set Topology

namespace Benzecri

namespace Sphere

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Two representatives that are equal give the same point (a cast helper). -/
private theorem mk_eq_mk_of_eq {v w : E} (hv : v ≠ 0) (h : v = w) : mk v hv = mk w (h ▸ hv) := by
  subst h; rfl

section Def6

variable (l : Module.Dual ℝ E)

/-- The translation space of the open hemisphere of equation `l` (Déf. 6): `L(E/N, N)`, `N = l⁻¹(O)`. -/
abbrev HemiTrans : Type _ := (E ⧸ LinearMap.ker l) →ₗ[ℝ] LinearMap.ker l

/-- The quotient map `q : E → E/N`. -/
abbrev hq : E →ₗ[ℝ] E ⧸ LinearMap.ker l := (LinearMap.ker l).mkQ

/-- The form `l` read on `E/N`. -/
def lbar : (E ⧸ LinearMap.ker l) →ₗ[ℝ] ℝ := (LinearMap.ker l).liftQ l le_rfl

@[simp] theorem lbar_hq (v : E) : lbar l (hq l v) = l v := rfl

variable {l}

/-- `M ↦ M + u(q M)`, the vector formula of Déf. 6. -/
def transl (u : HemiTrans l) (M : E) : E := M + (u (hq l M) : E)

theorem l_coe_ker (w : LinearMap.ker l) : l (w : E) = 0 := w.2

@[simp] theorem l_transl (u : HemiTrans l) (M : E) : l (transl u M) = l M := by
  simp [transl]

theorem transl_smul (u : HemiTrans l) (c : ℝ) (M : E) : transl u (c • M) = c • transl u M := by
  simp [transl, smul_add]

theorem hq_coe_ker (w : LinearMap.ker l) : hq l (w : E) = 0 :=
  (Submodule.Quotient.mk_eq_zero _).2 w.2

@[simp] theorem hq_transl (u : HemiTrans l) (M : E) : hq l (transl u M) = hq l M := by
  simp [transl]

theorem transl_add (u v : HemiTrans l) (M : E) : transl (u + v) M = transl u (transl v M) := by
  simp only [transl, LinearMap.add_apply, Submodule.coe_add, map_add, hq_coe_ker, add_zero]
  abel

@[simp] theorem transl_zero (M : E) : transl (0 : HemiTrans l) M = M := by simp [transl]

open scoped Classical in
variable (l) in
/-- **The action of Déf. 6 on `S(E)`**: `m + u = s(M + u(q M))`, for any representative `M` of `m`
(well defined: the formula is homogeneous). Where `M + u(q M) = 0` (never on the hemisphere) the
point is left fixed. -/
def hvadd (u : HemiTrans l) : Sphere E → Sphere E :=
  lift (fun v => if h : transl u v.1 = 0 then mk v.1 v.2 else mk (transl u v.1) h) fun v w hvw => by
    obtain ⟨c, hc, hcw⟩ := hvw.exists_pos_left v.2 w.2
    have hw : (w : E) = c • (v : E) := hcw.symm
    simp only [hw, transl_smul]
    show (if h : transl u (v : E) = 0 then _ else _) = (if h : c • transl u (v : E) = 0 then _ else _)
    by_cases h : transl u (v : E) = 0
    · have h' : c • transl u (v : E) = 0 := by rw [h, smul_zero]
      rw [dif_pos h, dif_pos h']
      exact (mk_smul v.2 hc _).symm
    · have h' : c • transl u (v : E) ≠ 0 := smul_ne_zero hc.ne' h
      rw [dif_neg h, dif_neg h']
      exact (mk_smul h hc _).symm

/-- **Déf. 6, the formula with any representative** (« Il est clair que cette expression est
indépendante du choix de $m$ », read « de $M$ », `[sic]`): for every nonzero `M` with
`M + u(q M) ≠ 0`, `s(M) + u = s(M + u(q M))`. -/
theorem hvadd_mk (u : HemiTrans l) {M : E} (hM : M ≠ 0) (h : transl u M ≠ 0) :
    hvadd l u (mk M hM) = mk (transl u M) h := by
  rw [hvadd, lift_mk]
  exact dif_neg h

/-- The independence of the representative, explicitly: two representatives of the same point
give the same `s(M + u(q M))`. -/
theorem mk_transl_eq_of_mk_eq (u : HemiTrans l) {M M' : E} (hM : M ≠ 0) (hM' : M' ≠ 0)
    (h : transl u M ≠ 0) (h' : transl u M' ≠ 0) (hMM' : mk M hM = mk M' hM') :
    mk (transl u M) h = mk (transl u M') h' := by
  rw [← hvadd_mk u hM h, ← hvadd_mk u hM' h', hMM']

theorem ne_zero_of_l_pos {v : E} (hv : 0 < l v) : v ≠ 0 := by
  rintro rfl; simp at hv

theorem transl_ne_zero (u : HemiTrans l) {M : E} (hM : 0 < l M) : transl u M ≠ 0 :=
  ne_zero_of_l_pos (by rwa [l_transl])

theorem hvadd_mem (u : HemiTrans l) {x : Sphere E} (hx : x ∈ openHemisphere l) :
    hvadd l u x ∈ openHemisphere l := by
  induction x using ind with
  | h v hv =>
    have hl : 0 < l v := (mk_mem_openHemisphere hv).1 hx
    rw [hvadd_mk u hv (transl_ne_zero u hl), mk_mem_openHemisphere, l_transl]
    exact hl

/-- The normalised representative `M / l(M)` (on the hemisphere, the representative with
`l = 1`). -/
def nrep (l : Module.Dual ℝ E) : Sphere E → E :=
  lift (fun v => (l v.1)⁻¹ • v.1) fun v w hvw => by
    obtain ⟨c, hc, hcw⟩ := hvw.exists_pos_left v.2 w.2
    rw [← hcw, map_smul, smul_eq_mul, smul_smul, mul_inv, mul_comm c⁻¹, mul_assoc,
      inv_mul_cancel₀ hc.ne', mul_one]

@[simp] theorem nrep_mk {v : E} (hv : v ≠ 0) : nrep l (mk v hv) = (l v)⁻¹ • v := rfl

theorem l_nrep {x : Sphere E} (hx : x ∈ openHemisphere l) : l (nrep l x) = 1 := by
  induction x using ind with
  | h v hv =>
    have hl : 0 < l v := (mk_mem_openHemisphere hv).1 hx
    rw [nrep_mk, map_smul, smul_eq_mul, inv_mul_cancel₀ hl.ne']

theorem nrep_ne_zero {x : Sphere E} (hx : x ∈ openHemisphere l) : nrep l x ≠ 0 :=
  ne_zero_of_l_pos (by rw [l_nrep hx]; exact one_pos)

theorem mk_nrep {x : Sphere E} (hx : x ∈ openHemisphere l) : mk (nrep l x) (nrep_ne_zero hx) = x := by
  induction x using ind with
  | h v hv =>
    have hl : 0 < l v := (mk_mem_openHemisphere hv).1 hx
    simp only [nrep_mk]
    exact mk_smul hv (inv_pos.2 hl) _

theorem nrep_mk_of_l_eq_one {v : E} (hv : l v = 1) : nrep l (mk v (ne_zero_of_l_pos (by rw [hv]; exact one_pos))) = v := by
  rw [nrep_mk, hv, inv_one, one_smul]

theorem nrep_hvadd (u : HemiTrans l) {x : Sphere E} (hx : x ∈ openHemisphere l) :
    nrep l (hvadd l u x) = transl u (nrep l x) := by
  conv_lhs => rw [← mk_nrep hx]
  have h1 : l (nrep l x) = 1 := l_nrep hx
  rw [hvadd_mk u _ (transl_ne_zero u (by rw [h1]; exact one_pos))]
  exact nrep_mk_of_l_eq_one (by rw [l_transl, h1])


/-! #### The affine structure on the hemisphere -/

/-- The action of `L(E/N, N)` on the open hemisphere `H` of equation `l` (Déf. 6). -/
instance instVAddHemi : VAdd (HemiTrans l) (openHemisphere l) :=
  ⟨fun u m => ⟨hvadd l u m, hvadd_mem u m.2⟩⟩

theorem coe_hvadd (u : HemiTrans l) (m : openHemisphere l) :
    ((u +ᵥ m : openHemisphere l) : Sphere E) = hvadd l u m := rfl

/-- **Déf. 6, as printed**: for `m ∈ H`, `u ∈ L(E/N, N)` and ANY `M ∈ F(m)`,
`m + u = s(M + u(q(M)))`. -/
theorem coe_vadd_eq (u : HemiTrans l) (m : openHemisphere l) {M : E} (hM : M ≠ 0)
    (hMm : mk M hM = m) :
    ((u +ᵥ m : openHemisphere l) : Sphere E) =
      mk (transl u M) (transl_ne_zero u ((mk_mem_openHemisphere hM).1 (hMm ▸ m.2))) := by
  obtain ⟨x, hx⟩ := m
  simp only at hMm
  subst hMm
  exact hvadd_mk u hM _

theorem nrep_vadd (u : HemiTrans l) (m : openHemisphere l) :
    nrep l (u +ᵥ m : openHemisphere l) = transl u (nrep l m) :=
  nrep_hvadd u m.2

theorem openHemisphere_ext {m m' : openHemisphere l} (h : nrep l m = nrep l m') : m = m' := by
  apply Subtype.ext
  rw [← mk_nrep m.2, ← mk_nrep m'.2]
  simp only [h]

instance instAddActionHemi : AddAction (HemiTrans l) (openHemisphere l) where
  zero_vadd m := openHemisphere_ext (by rw [nrep_vadd, transl_zero])
  add_vadd u v m := openHemisphere_ext (by rw [nrep_vadd, nrep_vadd, nrep_vadd, transl_add])

/-- On `E/N`, every class is `l̄(ξ)` times the class of a vector of `l = 1`. -/
theorem hq_eq_smul {v₁ : E} (hv₁ : l v₁ = 1) (v : E) : hq l v = l v • hq l v₁ := by
  rw [← map_smul, ← sub_eq_zero, ← map_sub, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero, LinearMap.mem_ker, map_sub, map_smul, hv₁, smul_eq_mul,
    mul_one, sub_self]

/-- A linear map `E/N → N` is determined by its value on the class of a vector of `l = 1`:
`u = l̄(·) • u(q v₁)`. -/
theorem eq_smulRight {v₁ : E} (hv₁ : l v₁ = 1) (u : HemiTrans l) :
    u = (lbar l).smulRight (u (hq l v₁)) := by
  apply Submodule.linearMap_qext
  ext v
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.smulRight_apply]
  rw [show (LinearMap.ker l).mkQ v = hq l v from rfl, lbar_hq, hq_eq_smul hv₁ v, map_smul]

theorem nrep_sub_mem (m m' : openHemisphere l) : nrep l m' - nrep l m ∈ LinearMap.ker l := by
  rw [LinearMap.mem_ker, map_sub, l_nrep m.2, l_nrep m'.2, sub_self]

/-- The difference `m' - m` in `L(E/N, N)`: `l̄(·) • (m'/l(m') - m/l(m))`. -/
instance instVSubHemi : VSub (HemiTrans l) (openHemisphere l) :=
  ⟨fun m' m => (lbar l).smulRight (⟨nrep l m' - nrep l m, nrep_sub_mem m m'⟩ : LinearMap.ker l)⟩

theorem vsub_apply_hq (m m' : openHemisphere l) (v : E) :
    ((m' -ᵥ m : HemiTrans l) (hq l v) : E) = l v • (nrep l m' - nrep l m) := rfl

/-- **The action of Déf. 6 is simply transitive**, on every open hemisphere (Déf. 1 as printed;
no hypothesis on `l`). -/
theorem isSimplyTransitive_hemi : IsSimplyTransitive (HemiTrans l) (openHemisphere l) := by
  intro m m'
  refine ⟨m' -ᵥ m, openHemisphere_ext ?_, fun u hu => ?_⟩
  · rw [nrep_vadd, transl, vsub_apply_hq, l_nrep m.2, one_smul, add_sub_cancel]
  · have h1 : l (nrep l (m : Sphere E)) = 1 := l_nrep m.2
    have := congrArg (nrep l ∘ Subtype.val) hu
    simp only [Function.comp_apply] at this
    rw [nrep_vadd, transl] at this
    rw [eq_smulRight h1 u]
    congr 1
    apply Subtype.ext
    simp only [← this, add_sub_cancel_left]

/-- **Déf. 6**: on an open hemisphere of nonzero equation, `L(E/N, N)` acting by
`m + u = s(M + u(q M))` is a structure of affine space (Mathlib's `AddTorsor`). -/
instance instAddTorsorHemi [Fact (l ≠ 0)] : AddTorsor (HemiTrans l) (openHemisphere l) where
  toAddAction := instAddActionHemi
  toVSub := instVSubHemi
  nonempty := by
    obtain ⟨x, hx⟩ := (openHemisphere_nonempty_iff l).2 (Fact.out)
    exact ⟨⟨x, hx⟩⟩
  vsub_vadd' m' m := openHemisphere_ext (by
    rw [nrep_vadd, transl, vsub_apply_hq, l_nrep m.2, one_smul, add_sub_cancel])
  vadd_vsub' u m := by
    have h1 : l (nrep l (m : Sphere E)) = 1 := l_nrep m.2
    conv_rhs => rw [eq_smulRight h1 u]
    show (lbar l).smulRight _ = _
    congr 1
    apply Subtype.ext
    simp only [nrep_vadd, transl, add_sub_cancel_left]

/-- **Déf. 6 in the reading of DEC-114** (an affine space is nonempty): the open hemisphere of
equation `l` is an affine space under `L(E/N, N)` iff `l ≠ 0`, i.e. iff it is nonempty. -/
theorem isAffineSpace_hemi_iff : IsAffineSpace (HemiTrans l) (openHemisphere l) ↔ l ≠ 0 := by
  constructor
  · rintro ⟨⟨m⟩, -⟩
    exact (openHemisphere_nonempty_iff l).1 ⟨m, m.2⟩
  · intro hl
    obtain ⟨x, hx⟩ := (openHemisphere_nonempty_iff l).2 hl
    exact ⟨⟨⟨x, hx⟩⟩, isSimplyTransitive_hemi⟩

/-- The translation space depends only on the hemisphere: two equations of the same open hemisphere
have the same kernel `N`. -/
theorem ker_eq_of_openHemisphere_eq {l' : Module.Dual ℝ E} (h : openHemisphere l = openHemisphere l') :
    LinearMap.ker l = LinearMap.ker l' := by
  obtain ⟨c, hc, rfl⟩ := (openHemisphere_eq_iff l l').1 h
  exact (LinearMap.ker_smul l c hc.ne').symm

/-- **The translation space does not depend on the equation** (« Soient $l$ une équation de $H$ … le
groupe des translations de $H$ »): for two equations `l`, `l'` of the same open hemisphere,
`L(E/N, N) ≃ L(E/N', N')` (`N = N'`, `ker_eq_of_openHemisphere_eq`), `u ↦ u` read through `N = N'`. -/
def hemiTransEquiv {l' : Module.Dual ℝ E} (h : openHemisphere l = openHemisphere l') :
    HemiTrans l ≃ₗ[ℝ] HemiTrans l' :=
  LinearEquiv.arrowCongr (Submodule.quotEquivOfEq _ _ (ker_eq_of_openHemisphere_eq h))
    (LinearEquiv.ofEq _ _ (ker_eq_of_openHemisphere_eq h))

/-- `hemiTransEquiv` does not change the vector formula `M ↦ M + u(q M)`. -/
theorem transl_hemiTransEquiv {l' : Module.Dual ℝ E} (h : openHemisphere l = openHemisphere l')
    (u : HemiTrans l) (M : E) : transl (hemiTransEquiv h u) M = transl u M :=
  rfl

/-- **The affine structure of Déf. 6 does not depend on the equation `l`**: for two equations `l`,
`l'` of the same open hemisphere `H`, the linear isomorphism `hemiTransEquiv` of the translation
spaces intertwines the two actions on `H`. -/
theorem coe_vadd_hemiTransEquiv {l' : Module.Dual ℝ E} (h : openHemisphere l = openHemisphere l')
    (u : HemiTrans l) (m : openHemisphere l) :
    ((hemiTransEquiv h u +ᵥ (⟨m, h ▸ m.2⟩ : openHemisphere l') : openHemisphere l') : Sphere E) =
      ((u +ᵥ m : openHemisphere l) : Sphere E) := by
  obtain ⟨x, hx⟩ := m
  induction x using ind with
  | h v hv =>
    rw [coe_vadd_eq _ _ hv rfl, coe_vadd_eq _ _ hv rfl]
    exact mk_eq_mk_of_eq _ (transl_hemiTransEquiv h u v)

/-- **Déf. 6 is independent of the equation** (the form asked by the WP-45f audit): two equations of
the same open hemisphere give linearly isomorphic translation spaces acting identically on `H`. -/
theorem hemi_vadd_indep {l' : Module.Dual ℝ E} (h : openHemisphere l = openHemisphere l') :
    ∃ e : HemiTrans l ≃ₗ[ℝ] HemiTrans l', ∀ (u : HemiTrans l) (m : openHemisphere l),
      ((e u +ᵥ (⟨m, h ▸ m.2⟩ : openHemisphere l') : openHemisphere l') : Sphere E) =
        ((u +ᵥ m : openHemisphere l) : Sphere E) :=
  ⟨hemiTransEquiv h, coe_vadd_hemiTransEquiv h⟩

/-! #### The chart: the affine hyperplane `l = 1`, and `ℝⁿ` -/

/-- **`L(E/N, N) ≃ N`**, evaluation at the class of a vector `v₁` with `l(v₁) = 1` (the class is
the same for every such `v₁`). -/
def evalTrans {v₁ : E} (hv₁ : l v₁ = 1) : HemiTrans l ≃ₗ[ℝ] LinearMap.ker l where
  toFun u := u (hq l v₁)
  invFun w := (lbar l).smulRight w
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv u := (eq_smulRight hv₁ u).symm
  right_inv w := by
    simp only [LinearMap.smulRight_apply, lbar_hq, hv₁, one_smul]

@[simp] theorem evalTrans_apply {v₁ : E} (hv₁ : l v₁ = 1) (u : HemiTrans l) :
    evalTrans hv₁ u = u (hq l v₁) := rfl

/-- **The affine hyperplane `l = 1`** of `E`, through a point `v₁` of it, with direction `N`. -/
def levelOne {v₁ : E} (_hv₁ : l v₁ = 1) : AffineSubspace ℝ E := AffineSubspace.mk' v₁ (LinearMap.ker l)

theorem mem_levelOne {v₁ : E} (hv₁ : l v₁ = 1) {v : E} : v ∈ levelOne hv₁ ↔ l v = 1 := by
  rw [levelOne, AffineSubspace.mem_mk', vsub_eq_sub, LinearMap.mem_ker, map_sub, hv₁, sub_eq_zero]

instance {v₁ : E} (hv₁ : l v₁ = 1) : Nonempty (levelOne hv₁) :=
  ⟨⟨v₁, AffineSubspace.self_mem_mk' _ _⟩⟩

theorem direction_levelOne {v₁ : E} (hv₁ : l v₁ = 1) :
    (levelOne hv₁).direction = LinearMap.ker l :=
  AffineSubspace.direction_mk' _ _

/-- **The chart of Déf. 6: the open hemisphere is affinely isomorphic to the affine hyperplane
`l = 1`**, by `m ↦ M / l(M)` (`M ∈ F(m)`), with linear part `u ↦ u(q v₁)`. -/
def hemiEquivLevelOne [Fact (l ≠ 0)] {v₁ : E} (hv₁ : l v₁ = 1) :
    openHemisphere l ≃ᵃ[ℝ] levelOne hv₁ where
  toFun m := ⟨nrep l m, (mem_levelOne hv₁).2 (l_nrep m.2)⟩
  invFun v := ⟨mk (v : E) (ne_zero_of_l_pos (by rw [(mem_levelOne hv₁).1 v.2]; exact one_pos)),
    (mk_mem_openHemisphere _).2 (by rw [(mem_levelOne hv₁).1 v.2]; exact one_pos)⟩
  left_inv m := Subtype.ext (mk_nrep m.2)
  right_inv v := Subtype.ext (nrep_mk_of_l_eq_one ((mem_levelOne hv₁).1 v.2))
  linear := (evalTrans hv₁).trans (LinearEquiv.ofEq _ _ (direction_levelOne hv₁).symm)
  map_vadd' m u := by
    apply Subtype.ext
    simp only [Equiv.coe_fn_mk, AffineSubspace.coe_vadd, vadd_eq_add]
    rw [nrep_vadd, transl, add_comm]
    congr 2
    rw [hq_eq_smul hv₁ (nrep l m), l_nrep m.2, one_smul]
    rfl

@[simp] theorem coe_hemiEquivLevelOne [Fact (l ≠ 0)] {v₁ : E} (hv₁ : l v₁ = 1)
    (m : openHemisphere l) : (hemiEquivLevelOne hv₁ m : E) = nrep l m := rfl

/-- A nonzero form takes the value `1`. -/
theorem exists_l_eq_one (hl : l ≠ 0) : ∃ v₁ : E, l v₁ = 1 := by
  obtain ⟨u, hu⟩ := exists_pos_of_ne_zero hl
  exact ⟨(l u)⁻¹ • u, by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hu.ne']⟩

/-- The translation space of an open hemisphere of `S(E)`, `dim E = n + 1`, has dimension `n`. -/
theorem finrank_hemiTrans [FiniteDimensional ℝ E] {n : ℕ} (hE : Module.finrank ℝ E = n + 1)
    (hl : l ≠ 0) : Module.finrank ℝ (HemiTrans l) = n := by
  obtain ⟨v₁, hv₁⟩ := exists_l_eq_one hl
  rw [(evalTrans hv₁).finrank_eq]
  have hsurj : Function.Surjective l := fun c => ⟨c • v₁, by rw [map_smul, hv₁, smul_eq_mul, mul_one]⟩
  have h := LinearMap.finrank_range_add_finrank_ker l
  rw [LinearMap.range_eq_top.2 hsurj, finrank_top, Module.finrank_self, hE] at h
  omega

/-- **« Un hémisphère ouvert de $S(n)$ est muni d'une structure affine isomorphe à celle de
$\R^n$ »** (p. 236, `cf.` Déf. 6): for `dim E = n + 1` and `l ≠ 0`, the affine space of Déf. 6 on
the open hemisphere of equation `l` is isomorphic to `ℝⁿ`. -/
theorem nonempty_hemi_affineEquiv [FiniteDimensional ℝ E] {n : ℕ} (hE : Module.finrank ℝ E = n + 1)
    [Fact (l ≠ 0)] : Nonempty (openHemisphere l ≃ᵃ[ℝ] (Fin n → ℝ)) := by
  obtain ⟨m⟩ := (inferInstance : Nonempty (openHemisphere l))
  have hfin : Module.finrank ℝ (HemiTrans l) = Module.finrank ℝ (Fin n → ℝ) := by
    rw [finrank_hemiTrans hE Fact.out, Module.finrank_fin_fun]
  exact ⟨(AffineEquiv.vaddConst ℝ m).symm.trans
    (LinearEquiv.ofFinrankEq _ _ hfin).toAffineEquiv⟩

/-! #### The elements of `GS` preserving the hemisphere act by affine maps -/

/-- **Inclusion of open hemispheres**: `{l > 0} ⊆ {l' > 0}` with `l ≠ 0` iff `l' = c l`, `c > 0`
(no topology, any dimension). -/
theorem openHemisphere_subset_iff {l' : Module.Dual ℝ E} (hl : l ≠ 0) :
    openHemisphere l ⊆ openHemisphere l' ↔ ∃ c : ℝ, 0 < c ∧ l' = c • l := by
  constructor
  · intro h
    have hpos : ∀ v, 0 < l v → 0 < l' v := fun v hv =>
      (mk_mem_openHemisphere (ne_zero_of_l_pos hv)).1
        (h ((mk_mem_openHemisphere (ne_zero_of_l_pos hv)).2 hv))
    obtain ⟨v₁, hv₁⟩ := exists_l_eq_one hl
    have hker : ∀ w, l w = 0 → l' w = 0 := by
      intro w hw
      by_contra hne
      have := hpos (v₁ + (-(l' v₁ + 1) / l' w) • w) (by
        rw [map_add, map_smul, hw, smul_zero, add_zero, hv₁]; exact one_pos)
      rw [map_add, map_smul, smul_eq_mul, div_mul_cancel₀ _ hne] at this
      linarith
    refine ⟨l' v₁, hpos v₁ (by rw [hv₁]; exact one_pos), ?_⟩
    ext v
    have := hker (v - l v • v₁) (by rw [map_sub, map_smul, hv₁, smul_eq_mul, mul_one, sub_self])
    rw [map_sub, map_smul, smul_eq_mul, sub_eq_zero] at this
    rw [this, LinearMap.smul_apply, smul_eq_mul, mul_comm]
  · rintro ⟨c, hc, rfl⟩
    rw [(openHemisphere_eq_iff l (c • l)).2 ⟨c, hc, rfl⟩]

theorem smul_mem_openHemisphere_iff (g : E ≃ₗ[ℝ] E) (x : Sphere E) :
    g • x ∈ openHemisphere l ↔ x ∈ openHemisphere (l ∘ₗ (g : E →ₗ[ℝ] E)) := by
  induction x using ind with
  | h v hv =>
    rw [smul_mk, mk_mem_openHemisphere, mk_mem_openHemisphere]
    rfl

/-- **An element of `GL(E)` maps the open hemisphere `H` of equation `l ≠ 0` into itself iff it
multiplies the equation by a positive factor** (it then maps `H` onto `H`). -/
theorem mapsTo_smul_openHemisphere_iff (hl : l ≠ 0) (g : E ≃ₗ[ℝ] E) :
    MapsTo (g • ·) (openHemisphere l) (openHemisphere l) ↔
      ∃ c : ℝ, 0 < c ∧ l ∘ₗ (g : E →ₗ[ℝ] E) = c • l := by
  rw [← openHemisphere_subset_iff hl]
  exact ⟨fun h x hx => (smul_mem_openHemisphere_iff g x).1 (h hx),
    fun h x hx => (smul_mem_openHemisphere_iff g x).2 (h hx)⟩

section Stabilizer

variable {g : E ≃ₗ[ℝ] E} (hg : ∃ c : ℝ, 0 < c ∧ l ∘ₗ (g : E →ₗ[ℝ] E) = c • l)
include hg

theorem map_mem_ker_of_stab {w : E} (hw : w ∈ LinearMap.ker l) : g w ∈ LinearMap.ker l := by
  obtain ⟨c, -, hc⟩ := hg
  have := LinearMap.congr_fun hc w
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, LinearMap.smul_apply,
    smul_eq_mul] at this
  rw [LinearMap.mem_ker, this, LinearMap.mem_ker.1 hw, mul_zero]

theorem symm_mem_ker_of_stab {w : E} (hw : w ∈ LinearMap.ker l) : g.symm w ∈ LinearMap.ker l := by
  obtain ⟨c, hc0, hc⟩ := hg
  have := LinearMap.congr_fun hc (g.symm w)
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, LinearMap.smul_apply,
    smul_eq_mul, LinearEquiv.apply_symm_apply, LinearMap.mem_ker.1 hw] at this
  exact LinearMap.mem_ker.2 ((mul_eq_zero.1 this.symm).resolve_left hc0.ne')

theorem smul_mem_of_stab {x : Sphere E} (hx : x ∈ openHemisphere l) : g • x ∈ openHemisphere l := by
  obtain ⟨c, hc0, hc⟩ := hg
  rw [smul_mem_openHemisphere_iff, hc, ← (openHemisphere_eq_iff l (c • l)).2 ⟨c, hc0, rfl⟩]
  exact hx

/-- The map induced on `H` by an element of `GL(E)` preserving it. -/
def hemiMap (m : openHemisphere l) : openHemisphere l := ⟨g • (m : Sphere E), smul_mem_of_stab hg m.2⟩

/-- The linear part of `hemiMap`: `u ↦ g ∘ u ∘ ḡ⁻¹` on `L(E/N, N)`. -/
def hemiMapLinear : HemiTrans l →ₗ[ℝ] HemiTrans l where
  toFun u := ((g : E →ₗ[ℝ] E).restrict fun _ hw => map_mem_ker_of_stab hg hw).comp
    (u.comp ((LinearMap.ker l).mapQ (LinearMap.ker l) (g.symm : E →ₗ[ℝ] E)
      fun _ hw => symm_mem_ker_of_stab hg hw))
  map_add' u v := by ext; simp
  map_smul' c u := by ext; simp

theorem hemiMapLinear_apply_hq (u : HemiTrans l) (v : E) :
    ((hemiMapLinear hg u) (hq l (g v)) : E) = g (u (hq l v)) := by
  simp [hemiMapLinear]

/-- **The elements of `GL(E)` preserving the open hemisphere act on it by affine maps** for the
structure of Déf. 6 (`IsAffine`, Déf. 2 in the reading of DEC-114), with linear part
`u ↦ g ∘ u ∘ ḡ⁻¹`. -/
theorem isAffine_hemiMap [Fact (l ≠ 0)] : IsAffine ℝ (hemiMap hg) := by
  refine ⟨hemiMapLinear hg, fun m u => ?_⟩
  obtain ⟨x, hx⟩ := m
  induction x using ind with
  | h v hv =>
    have hlv : 0 < l v := (mk_mem_openHemisphere hv).1 hx
    have hglv : 0 < l (g v) := by
      have := (smul_mem_openHemisphere_iff g (mk v hv)).1 (smul_mem_of_stab hg hx)
      exact (mk_mem_openHemisphere hv).1 this
    apply Subtype.ext
    show g • ((u +ᵥ (⟨mk v hv, hx⟩ : openHemisphere l) : openHemisphere l) : Sphere E) =
      ((hemiMapLinear hg u +ᵥ (hemiMap hg ⟨mk v hv, hx⟩) : openHemisphere l) : Sphere E)
    rw [coe_vadd_eq u _ hv rfl, coe_vadd_eq _ _ (g.map_ne_zero_iff.2 hv)
      (by simp [hemiMap, smul_mk]), smul_mk]
    congr 1
    simp only [transl, map_add, hemiMapLinear_apply_hq]

end Stabilizer

/-- **The elements of `GS(E)` preserving an open hemisphere act on it by affine maps** (Déf. 6):
for `γ ∈ GS(E)` mapping `H` into itself, the induced map of `H` is affine. -/
theorem isAffine_gse_restrict [Fact (l ≠ 0)] (γ : GSE E)
    (hγ : MapsTo (γ • ·) (openHemisphere l) (openHemisphere l)) :
    IsAffine ℝ (fun m : openHemisphere l => (⟨γ • (m : Sphere E), hγ m.2⟩ : openHemisphere l)) := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective γ
  have hg := (mapsTo_smul_openHemisphere_iff Fact.out g).1 hγ
  exact isAffine_hemiMap hg

end Def6

/-! ### The standard hemisphere chart `ℝⁿ → S(n)` and the embedding `GA(n) ↪ GS(n)` -/

section Standard

variable {n : ℕ}

private theorem snoc_add_snoc (a b : Fin n → ℝ) (s t : ℝ) :
    (Fin.snoc a s : Fin (n + 1) → ℝ) + Fin.snoc b t = Fin.snoc (a + b) (s + t) := by
  ext i
  refine Fin.lastCases ?_ (fun i => ?_) i <;> simp

private theorem smul_snoc (c : ℝ) (a : Fin n → ℝ) (s : ℝ) :
    c • (Fin.snoc a s : Fin (n + 1) → ℝ) = Fin.snoc (c • a) (c * s) := by
  ext i
  refine Fin.lastCases ?_ (fun i => ?_) i <;> simp

private theorem init_add (v w : Fin (n + 1) → ℝ) :
    (Fin.init (v + w) : Fin n → ℝ) = Fin.init v + Fin.init w := rfl

private theorem init_smul (c : ℝ) (v : Fin (n + 1) → ℝ) :
    (Fin.init (c • v) : Fin n → ℝ) = c • Fin.init v := rfl

variable (n) in
/-- The last coordinate `x_{n+1}` of `ℝⁿ⁺¹`. -/
def lastForm : Module.Dual ℝ (Fin (n + 1) → ℝ) := LinearMap.proj (Fin.last n)

@[simp] theorem lastForm_apply (v : Fin (n + 1) → ℝ) : lastForm n v = v (Fin.last n) := rfl

theorem lastForm_ne_zero : lastForm n ≠ 0 := by
  intro h
  have := LinearMap.congr_fun h (Fin.snoc 0 1)
  simp at this

instance : Fact (lastForm n ≠ 0) := ⟨lastForm_ne_zero⟩

theorem snoc_one_ne_zero (y : Fin n → ℝ) : (Fin.snoc y 1 : Fin (n + 1) → ℝ) ≠ 0 := by
  intro h
  have := congr_fun h (Fin.last n)
  simp at this

variable (n) in
/-- **The standard hemisphere chart** `j : ℝⁿ → S(n)`, `y ↦ s(y, 1)`, onto the open hemisphere
`H₀ = {x_{n+1} > 0}` (the `j` of the Remarque, `bzrem:c1s1r1_affine_vers_projective`). -/
def hemiChart (y : Fin n → ℝ) : S n := mk (Fin.snoc y 1) (snoc_one_ne_zero y)

theorem hemiChart_mem (y : Fin n → ℝ) : hemiChart n y ∈ openHemisphere (lastForm n) := by
  rw [hemiChart, mk_mem_openHemisphere]
  simp

theorem nrep_hemiChart (y : Fin n → ℝ) : nrep (lastForm n) (hemiChart n y) = Fin.snoc y 1 :=
  nrep_mk_of_l_eq_one (by simp)

theorem hemiChart_injective : Function.Injective (hemiChart n) := by
  intro y y' h
  have := congrArg (fun x => (Fin.init (nrep (lastForm n) x) : Fin n → ℝ)) h
  simpa [nrep_hemiChart] using this

private theorem snoc_init_smul_eq (v : Fin (n + 1) → ℝ) (hv : v (Fin.last n) ≠ 0) :
    (Fin.snoc ((v (Fin.last n))⁻¹ • Fin.init v) 1 : Fin (n + 1) → ℝ) = (v (Fin.last n))⁻¹ • v := by
  ext i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · simp [inv_mul_cancel₀ hv]
  · simp [Fin.init]

/-- The range of the standard chart is the open hemisphere `x_{n+1} > 0`. -/
theorem range_hemiChart : range (hemiChart n) = openHemisphere (lastForm n) := by
  refine Subset.antisymm (range_subset_iff.2 hemiChart_mem) fun x hx => ?_
  induction x using ind with
  | h v hv =>
    have hl : 0 < v (Fin.last n) := (mk_mem_openHemisphere hv).1 hx
    refine ⟨(v (Fin.last n))⁻¹ • Fin.init v, ?_⟩
    rw [hemiChart, mk_eq_mk_of_eq _ (snoc_init_smul_eq v hl.ne')]
    exact mk_smul hv (inv_pos.2 hl) _

theorem continuous_hemiChart : Continuous (hemiChart n) := by
  have : Continuous fun y : Fin n → ℝ => (Fin.snoc y (1 : ℝ) : Fin (n + 1) → ℝ) :=
    Continuous.finSnoc (A := fun _ => ℝ) continuous_id continuous_const
  exact continuous_mk_comp this snoc_one_ne_zero

private theorem continuous_init : Continuous (Fin.init : (Fin (n + 1) → ℝ) → (Fin n → ℝ)) :=
  continuous_pi fun _ => continuous_apply _

theorem isOpenMap_hemiChart : IsOpenMap (hemiChart n) := by
  intro U hU
  set f : (Fin (n + 1) → ℝ) → (Fin n → ℝ) := fun v => (v (Fin.last n))⁻¹ • Fin.init v with hf
  set C : Set (Fin (n + 1) → ℝ) := {v | 0 < v (Fin.last n)} ∩ f ⁻¹' U with hC
  have himg : hemiChart n '' U = ofCone C := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact mk_mem_ofCone _ ⟨by simp, by simpa [hf] using hy⟩
    · intro hx
      obtain ⟨v, hv, hvC, rfl⟩ := mem_ofCone.1 hx
      refine ⟨f v, hvC.2, ?_⟩
      rw [hemiChart, mk_eq_mk_of_eq _ (snoc_init_smul_eq v hvC.1.ne')]
      exact mk_smul hv (inv_pos.2 hvC.1) _
  rw [himg]
  refine isOpen_ofCone (fun c hc v hv => ⟨?_, ?_⟩) ?_
  · show 0 < (c • v) (Fin.last n)
    simpa using mul_pos hc hv.1
  · show f (c • v) ∈ U
    have : f (c • v) = f v := by
      simp only [hf, Pi.smul_apply, smul_eq_mul, init_smul, smul_smul, mul_inv]
      rw [mul_assoc, mul_left_comm, inv_mul_cancel₀ hc.ne', mul_one]
    rw [this]; exact hv.2
  · have hcont : ContinuousOn f {v | 0 < v (Fin.last n)} :=
      (((continuous_apply _).continuousOn.inv₀ fun v hv => ne_of_gt hv)).smul
        continuous_init.continuousOn
    exact hcont.isOpen_inter_preimage (isOpen_lt continuous_const (continuous_apply _)) hU

/-- **The standard hemisphere chart is an open embedding** `ℝⁿ ↪ S(n)`. -/
theorem isOpenEmbedding_hemiChart : Topology.IsOpenEmbedding (hemiChart n) :=
  .of_continuous_injective_isOpenMap continuous_hemiChart hemiChart_injective isOpenMap_hemiChart

variable (n) in
/-- `v ↦ (v, 0)`, linear. -/
def snocZero : (Fin n → ℝ) →ₗ[ℝ] (Fin (n + 1) → ℝ) where
  toFun v := Fin.snoc v 0
  map_add' a b := by rw [snoc_add_snoc, add_zero]
  map_smul' c a := by rw [smul_snoc, mul_zero]; rfl

theorem lastForm_snoc_zero_one : lastForm n (Fin.snoc 0 1) = 1 := by simp

variable (n) in
/-- The linear part of the standard chart, `ℝⁿ → L(E/N, N)`. -/
def hemiChartLinear : (Fin n → ℝ) →ₗ[ℝ] HemiTrans (lastForm n) :=
  (evalTrans (lastForm_snoc_zero_one (n := n))).symm.toLinearMap ∘ₗ
    (snocZero n).codRestrict (LinearMap.ker (lastForm n)) fun v => by simp [snocZero]

variable (n) in
/-- The standard chart, as a map into the hemisphere. -/
def hemiChartH (y : Fin n → ℝ) : openHemisphere (lastForm n) := ⟨hemiChart n y, hemiChart_mem y⟩

/-- **The standard chart is an affine isomorphism `ℝⁿ ≃ H₀`** for the structure of Déf. 6 (it is
« un isomorphisme, compatible avec la structure affine de $\R^n$ sur un hémisphère » of the
Remarque): it is affine (`IsAffine`, Déf. 2), with linear part `v ↦ l̄(·) • (v, 0)`. -/
theorem isAffine_hemiChartH : IsAffine ℝ (hemiChartH n) := by
  refine ⟨hemiChartLinear n, fun y v => openHemisphere_ext ?_⟩
  show nrep _ (hemiChart n (v +ᵥ y)) = nrep _ ((hemiChartLinear n v +ᵥ hemiChartH n y : _) : S n)
  rw [nrep_vadd, nrep_hemiChart, transl, show ((hemiChartH n y : openHemisphere _) : S n) =
    hemiChart n y from rfl, nrep_hemiChart]
  simp only [hemiChartLinear, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
  show _ = _ + (((lbar (lastForm n)).smulRight _) _ : Fin (n + 1) → ℝ)
  rw [LinearMap.smulRight_apply, lbar_hq]
  simp only [lastForm_apply, Fin.snoc_last, one_smul, LinearMap.codRestrict_apply, snocZero,
    LinearMap.coe_mk, AddHom.coe_mk, vadd_eq_add]
  rw [snoc_add_snoc, add_zero, add_comm v y]

theorem bijective_hemiChartH : Function.Bijective (hemiChartH n) := by
  refine ⟨fun y y' h => hemiChart_injective (congrArg Subtype.val h), fun m => ?_⟩
  obtain ⟨y, hy⟩ : (m : S n) ∈ range (hemiChart n) := by rw [range_hemiChart]; exact m.2
  exact ⟨y, Subtype.ext hy⟩

/-- The linear map of `ℝⁿ⁺¹` attached to an affine automorphism `f` of `ℝⁿ`:
`(y, t) ↦ (f'(y) + t f(0), t)`. -/
def affLin (f : GAR n) : (Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin (n + 1) → ℝ) where
  toFun v := Fin.snoc (f.linear (Fin.init v) + v (Fin.last n) • f 0) (v (Fin.last n))
  map_add' v w := by
    rw [snoc_add_snoc, init_add, map_add, Pi.add_apply, add_smul]
    congr 1
    abel
  map_smul' c v := by
    rw [smul_snoc, init_smul, map_smul, Pi.smul_apply, smul_eq_mul, smul_add, mul_smul]
    rfl

theorem affLin_snoc (f : GAR n) (y : Fin n → ℝ) (t : ℝ) :
    affLin f (Fin.snoc y t) = Fin.snoc (f.linear y + t • f 0) t := by
  simp [affLin]

private theorem GAR.apply_eq (f : GAR n) (y : Fin n → ℝ) : f y = f.linear y + f 0 := by
  have := f.map_vadd 0 y
  simpa [vadd_eq_add] using this

theorem affLin_mul (f g : GAR n) : affLin (f * g) = (affLin f).comp (affLin g) := by
  refine LinearMap.ext fun v => ?_
  rw [← Fin.snoc_init_self v]
  simp only [LinearMap.coe_comp, Function.comp_apply, affLin_snoc]
  congr 1
  have h1 : (f * g).linear = f.linear * g.linear := rfl
  have h0 : (f * g) 0 = f.linear (g 0) + f 0 := by
    rw [AffineEquiv.coe_mul, Function.comp_apply, GAR.apply_eq f]
  rw [h1, h0, map_add, map_smul, LinearEquiv.mul_apply, smul_add]
  abel

theorem affLin_one : affLin (1 : GAR n) = LinearMap.id := by
  refine LinearMap.ext fun v => ?_
  conv_lhs => rw [← Fin.snoc_init_self v]
  rw [affLin_snoc, show (1 : GAR n).linear = LinearEquiv.refl ℝ _ from rfl]
  simp

/-- **`GA(n, ℝ) → GL(n+1, ℝ)`**, `f ↦ ((y, t) ↦ (f'(y) + t f(0), t))`. -/
def affToGL : GAR n →* GLR (n + 1) where
  toFun f := LinearEquiv.ofLinear (affLin f) (affLin f⁻¹)
    (by rw [← affLin_mul, mul_inv_cancel, affLin_one])
    (by rw [← affLin_mul, inv_mul_cancel, affLin_one])
  map_one' := by
    ext v : 1
    simp [affLin_one]
  map_mul' f g := by
    ext v : 1
    simp [affLin_mul, LinearEquiv.mul_apply]

@[simp] theorem affToGL_apply (f : GAR n) (v : Fin (n + 1) → ℝ) : affToGL f v = affLin f v := rfl

/-- **The embedding `GA(n, ℝ) ↪ GS(n, ℝ)` of the Remarque** (`bzrem:c1s1r1_affine_vers_projective`):
`affToGL` followed by the projection `GL(n+1) → GS(n)`. -/
def affToGS : GAR n →* GSR n := (QuotientGroup.mk' (posHomotheties _)).comp affToGL

/-- **Equivariance of the standard chart**: `j(f(y)) = φ(f) • j(y)`. -/
theorem hemiChart_apply_eq_smul (f : GAR n) (y : Fin n → ℝ) :
    hemiChart n (f y) = affToGS f • hemiChart n y := by
  rw [affToGS, MonoidHom.comp_apply, QuotientGroup.mk'_apply, GSE.mk_smul, hemiChart, hemiChart,
    smul_mk]
  apply mk_eq_mk_of_eq _
  rw [show ((affToGL f : GLR (n + 1)) (Fin.snoc y 1)) = affLin f (Fin.snoc y 1) from rfl,
    affLin_snoc, one_smul, GAR.apply_eq]

/-- **`GA(n, ℝ) → GS(n, ℝ)` is injective.** -/
theorem affToGS_injective : Function.Injective (affToGS (n := n)) := by
  refine (injective_iff_map_eq_one _).2 fun f hf => ?_
  rw [affToGS, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hf
  obtain ⟨c, -, hc⟩ := mem_posHomotheties.1 hf
  have h1 := hc (Fin.snoc 0 1)
  rw [affToGL_apply, affLin_snoc, smul_snoc] at h1
  have hc1 : c = 1 := by
    have := congr_fun h1 (Fin.last n)
    simpa using this.symm
  subst hc1
  ext y : 1
  have := hc (Fin.snoc y 1)
  rw [affToGL_apply, affLin_snoc, one_smul, one_smul] at this
  have := congrArg (fun v : Fin (n + 1) → ℝ => (Fin.init v : Fin n → ℝ)) this
  simp only [Fin.init_snoc] at this
  rw [GAR.apply_eq, this]
  rfl

/-- **Every affine injection of `ℝⁿ` into an open hemisphere is the standard chart followed by an
element of `GS(n)`** (the Remarque's `j`, `bzrem:c1s1r1_affine_vers_projective`): if
`j : ℝⁿ → H` is injective and affine for the structure of Déf. 6 on the open hemisphere `H` of
equation `l ≠ 0` of `S(n)`, then `j(y) = σ • s(y, 1)` for some `σ ∈ GS(n)`. (`σ` is the class of
`(y, t) ↦ j̃'(y) + t j̃(0)`, `j̃ = M / l(M)` the lift of `j` to the affine hyperplane `l = 1`.) -/
theorem exists_eq_smul_hemiChart {l : Module.Dual ℝ (Fin (n + 1) → ℝ)} [Fact (l ≠ 0)]
    {j : (Fin n → ℝ) → openHemisphere l} (hj : IsAffine ℝ j) (hinj : Function.Injective j) :
    ∃ σ : GSR n, ∀ y, (j y : S n) = σ • hemiChart n y := by
  obtain ⟨v₁, hv₁⟩ := exists_l_eq_one (Fact.out : l ≠ 0)
  obtain ⟨f, hf⟩ := (isAffine_iff ℝ j).1 hj
  let a : (Fin n → ℝ) →ᵃ[ℝ] (Fin (n + 1) → ℝ) :=
    (levelOne hv₁).subtype.comp ((hemiEquivLevelOne hv₁).toAffineMap.comp f)
  have ha : ∀ y, a y = nrep l (j y) := fun y => by rw [← hf]; rfl
  have hl1 : ∀ y, l (a y) = 1 := fun y => by rw [ha]; exact l_nrep (j y).2
  have hlin : ∀ v, a.linear v = a v - a 0 := fun v => by
    have := a.linearMap_vsub v 0
    rwa [vsub_eq_sub, sub_zero, vsub_eq_sub] at this
  have hl0 : ∀ v, l (a.linear v) = 0 := fun v => by rw [hlin, map_sub, hl1, hl1, sub_self]
  have hlinj : ∀ v, a.linear v = 0 → v = 0 := fun v hv => by
    rw [hlin, sub_eq_zero, ha, ha] at hv
    exact hinj (openHemisphere_ext hv)
  let L : (Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin (n + 1) → ℝ) :=
    a.linear ∘ₗ LinearMap.funLeft ℝ ℝ Fin.castSucc + (LinearMap.proj (Fin.last n)).smulRight (a 0)
  have hL : ∀ w, L w = a.linear (Fin.init w) + w (Fin.last n) • a 0 := fun w => rfl
  have hLinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    rw [hL] at hw
    have h1 : w (Fin.last n) = 0 := by
      have := congrArg l hw
      rwa [map_add, map_smul, hl0, hl1, smul_eq_mul, mul_one, zero_add, map_zero] at this
    rw [h1, zero_smul, add_zero] at hw
    have h2 := hlinj _ hw
    rw [← Fin.snoc_init_self w, h2, h1]
    ext i
    refine Fin.lastCases ?_ (fun i => ?_) i <;> simp
  refine ⟨QuotientGroup.mk (LinearEquiv.ofInjectiveEndo L hLinj), fun y => ?_⟩
  rw [GSE.mk_smul, hemiChart, smul_mk, ← mk_nrep (j y).2]
  apply mk_eq_mk_of_eq
  show nrep l (j y) = L (Fin.snoc y 1)
  rw [hL, Fin.init_snoc, Fin.snoc_last, one_smul, hlin, ← ha, sub_add_cancel]

end Standard


end Sphere

end Benzecri
