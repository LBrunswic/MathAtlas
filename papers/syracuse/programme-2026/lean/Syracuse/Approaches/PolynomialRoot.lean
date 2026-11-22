import Syracuse.Basic

/-!
# `polynomial-root`: the Fox cocycle `S = χ ∘ ∂_u` and its reduced polynomials

Formalises `approaches/polynomial-root` (report sections `01-construction`, `02-catalogue`,
`03-cohomology`).

**Conventions.** The notes work on the free *group* `F₂ = ⟨u, v⟩` and its group ring `ℤ[F₂]`
(conjugation by `g⁻¹` is used in Prop. 1.8), so we use Mathlib's `FreeGroup Letter`; positive
words are `List Letter`, embedded by `pos`. The Fox derivative `∂_x : ℤ[F₂] → ℤ[F₂]` is the
translation part of the homomorphism `F₂ → Aff ℤ[F₂]`, `y ↦ (y, δ_{xy})`, into the affine group
(`fox`, linear extension `foxLin`). The universal character `χ(u) = X`, `χ(v) = Y` takes values in
an arbitrary commutative ring `R` with units `X, Y`; the universal case `Λ = ℤ[X^{±1}, Y^{±1}]`
is `Lam` with `Xl, Yl`. On positive words the cocycle needs no inverses (`foxSP`).
Letters follow the accelerated `T`-map: `u : x ↦ (3x+1)/2`, `v : x ↦ x/2`. A word has type
`(E, o)` = (length, number of `u`), `χ(w) = X^o Y^{E-o}`. The coprime closure substitution is
the note's `X ↦ t^{-(E-o)}`, `Y ↦ t^{o}` (`~/syracuse_words/formalization.md` uses its inverse
`t ↦ t⁻¹`).

**Dictionary with `Basic`.** The gap word `(d₀, …, d_{o-1})` (all `dᵢ ≥ 1`) is
`toLetters w = u v^{d₀-1} ⋯ u v^{d_{o-1}-1}`, of type `(w.sum, w.length)`, and
`S_Basic(A, B; w) = B^{o-1} S(A B⁻¹, A; toLetters w) = A^{E-1} S(B A⁻¹, A⁻¹; (toLetters w)ᴿ)`.

## Coverage

| Note claim (file) | Lean | Status |
|---|---|---|
| Def 1.2 character `χ` (01) | `chiU`, `chi`, `Lam`, `Xl`, `Yl` | defined |
| Def 1.3 Fox derivative, Leibniz, `∂(g⁻¹)` (01) | `fox`, `fox_mul`, `fox_of`, `fox_inv`, `foxLin` | proved |
| Def 1.4 `S = χ∂_u`; `T = χ∂_v` (01, 03) | `foxS`, `foxT` | defined |
| Prop 1.5 closed form on positive words (01) | `foxS_pos`, `foxSP_eq_sum` | proved |
| Prop 1.6 cocycle law, uniqueness (01) | `foxS_mul`, `foxT_mul`, `foxS_unique` | proved |
| Def 1.7 type, `χ(w) = X^o Y^{E-o}` (01) | `chiU_pos`, `mono_eq` | proved |
| Prop 1.8 conjugation formula, invariance mod `1 - χ(w)` up to `χ(g)` (01) | `foxS_conj`, `chiU_conj`, `foxS_conj_mod`, `foxS_rotate_mod` | proved |
| Prop 1.9, `d = 1`: `Λ/(1 - X^o Y^{E-o}) ≅ ℤ[t^{±1}]` (01, 02) | `reparamIso`, `reparam_universal`, `reparam_kills`, `reparamIso_foxS`, `closureIdeal_eq` | proved |
| Prop 1.9, `d > 1`: `≅ ℤ[t^{±1}, s]/(s^d - 1)` (01) | — | not formalized |
| Rem 1.10 "at `(X,Y) = (2,3)`, `S(w)/(χ(w)-1)` is the fixed point" (01) | `tWord_eq`, `tWord_fixed`, `remark_1_10_counterexample` | corrected: fixed point is `½ S(wᴿ)/(1 - χ(w))` at `(3/2, 1/2)`; `uv` refutes the literal claim |
| Bridge to `Basic.S` ("opposite roles", `gen_table`: "X↔Y plus reversal") | `toLetters`, `S_eq_foxSP`, `S_eq_foxS`, `S_eq_foxSP_reverse` | corrected: exact Laurent substitutions above, not a plain swap |
| Lemma 3.2 Crowell–Fox `(X-1)S + (Y-1)T = χ - 1` (03) | `crowellFox_groupRing`, `crowellFox`, `crowellFox_red` | proved |
| §2 `uuv ↦ t+1`, `uuuv ↦ Φ₃` (02) | `redS_uuv`, `redS_uuuv` | proved |
| §2 `uvuv ↦ 1+s`, `uuu ↦ 1+s+s²` in `R_d` (02) | — | not formalized (`d > 1`) |
| Four cycles: fixed points, `P_w`, `P_{-17} = Φ₇ R_w`, `Q_w` (02) | `tWord_cycles`, `toLetters_minus17`, `minus17_basic`, `redS_u`, `redS_uv`, `redS_minus17`, `P17_factor`, `R17_tower` | proved |
| Prop 2.1 `g_o ∣ P_w` (02) | `core_gcd` | proved over `ℚ[t^{±1}]` for `o, E-o > 0` (via Crowell–Fox and `gcd(g_o, g_{E-o}) = 1`, not the note's residue argument) |
| Prop 2.1 `P_w` is `0/1` with `o` terms; `R_w ∈ {-1,0,1}[t]` (02) | — | not formalized |
| Cor 2.2 `R_w(1) = 1` (02) | `core_gcd` | proved |
| Cor 2.2 `Q_w ∈ {0,1}[t]` (02) | `R17_tower` (one instance) | not formalized in general |
| Prop 2.3 `uuvuvvv`: `P_w = Φ₃ (t³ - t² + 1)` (02) | `redS_plastic`, `plastic_factor`, `plastic_factor_rel` | proved; `t³ - t² + 1` is `x³ - x - 1` under `t = -1/x` |
| Prop 2.3 frontier `E+o ≤ 9` cyclotomic; Mahler = plastic number; Galois `S₃` (02) | — | empirical / not formalized (enumeration, numerics) |
| Prop 2.4 Lehmer word: `P_w = Φ₇ · (t¹⁰ - t⁹ + t⁷ - ⋯ - t + 1)` (02) | `redS_lehmer`, `PLehmer_factor`, `lehmer_comp_neg`, `lehmer_not_dvd` | corrected: that factor is `L(-t)` for Lehmer's `L`; `L ∤ P_w` |
| Prop 2.4 smallest Mahler measure `> 1` over the 1233 classes; ranges, counts (02) | — | empirical (computational) |
| Prop 2.5 `R_{wᴿ}`, `R_{w̄}` reciprocal to `R_w` (02) | `foxSP_reverse`, `foxSP_complement` | partial: cocycle-level identities proved, core-level statement not formalized |
| Prop 2.5 fibre statistics, `R_cores.csv`; Rem 3.7 duality-locus counts (02, 03) | — | empirical |
| CRT splitting for `d > 1` (02, 03) | — | not formalized |
| Prop 3.1 restriction to `⟨w⟩` (03) | (`foxS_conj_mod`) | not formalized as cohomology |
| Thm 3.3 `gcd(S, T) = R_w` over `ℚ[t^{±1}]` (03) | `core_gcd` | proved: `S̄ = g_o R`, `T̄ = t^{-(E-o)} g_{E-o} R`, common divisors of `S̄, T̄` are the divisors of `R` |
| Thm 3.3 `ℚ ⊗ H²(G_w; M) ≅ ℚ[t^{±1}]/(R_w)` (03) | `AlexanderClaim` | stated only (needs Lyndon asphericity) |
| Rem 3.4–3.6: Lehmer–pretzel, Fox–Lyndon resolution, torsion, `H₁(G_w) ≅ ℤ ⊕ ℤ/d` (03) | — | not formalized |
-/

namespace Syracuse.PolynomialRoot

/-- The two letters of the free group `F₂ = ⟨u, v⟩`. -/
inductive Letter
  | u
  | v
  deriving DecidableEq, Repr

open Letter

/-- `Aff A`: pairs `(λ, a) ∈ Aˣ × A`, i.e. affine maps `z ↦ λ z + a`, composed as maps. -/
@[ext] structure Aff (A : Type*) [Ring A] where
  /-- The linear part `λ`. -/
  lin : Aˣ
  /-- The translation part `a`. -/
  tr : A

namespace Aff

variable {A B : Type*} [Ring A] [Ring B]

instance : Mul (Aff A) := ⟨fun f g => ⟨f.lin * g.lin, f.tr + f.lin * g.tr⟩⟩
instance : One (Aff A) := ⟨⟨1, 0⟩⟩
instance : Inv (Aff A) := ⟨fun f => ⟨f.lin⁻¹, -(↑f.lin⁻¹ * f.tr)⟩⟩

@[simp] lemma mul_lin (f g : Aff A) : (f * g).lin = f.lin * g.lin := rfl
@[simp] lemma mul_tr (f g : Aff A) : (f * g).tr = f.tr + f.lin * g.tr := rfl
@[simp] lemma one_lin : (1 : Aff A).lin = 1 := rfl
@[simp] lemma one_tr : (1 : Aff A).tr = 0 := rfl
@[simp] lemma inv_lin (f : Aff A) : f⁻¹.lin = f.lin⁻¹ := rfl
@[simp] lemma inv_tr (f : Aff A) : f⁻¹.tr = -(↑f.lin⁻¹ * f.tr) := rfl

instance : Group (Aff A) where
  mul_assoc f g h := by ext <;> simp [mul_add, mul_assoc, add_assoc]
  one_mul f := by ext <;> simp
  mul_one f := by ext <;> simp
  inv_mul_cancel f := by ext <;> simp

/-- The linear part as a group homomorphism. -/
def linHom : Aff A →* Aˣ where
  toFun f := f.lin
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Functoriality of `Aff` along ring homomorphisms. -/
def map (φ : A →+* B) : Aff A →* Aff B where
  toFun f := ⟨Units.map φ f.lin, φ f.tr⟩
  map_one' := by ext <;> simp
  map_mul' f g := by ext <;> simp

@[simp] lemma map_lin (φ : A →+* B) (f : Aff A) : (map φ f).lin = Units.map φ f.lin := rfl
@[simp] lemma map_tr (φ : A →+* B) (f : Aff A) : (map φ f).tr = φ f.tr := rfl

end Aff

/-- A group homomorphism `F₂ → Aff A` is the same as a character `ρ` plus a cocycle; two cocycles
for the same `ρ` that agree on `u` and `v` agree everywhere. -/
theorem cocycle_ext {A : Type*} [Ring A] (ρ : FreeGroup Letter →* Aˣ) {f g : FreeGroup Letter → A}
    (hf : ∀ a b, f (a * b) = f a + ρ a * f b) (hg : ∀ a b, g (a * b) = g a + ρ a * g b)
    (hu : f (.of u) = g (.of u)) (hv : f (.of v) = g (.of v)) : f = g := by
  have h0 : ∀ {k : FreeGroup Letter → A}, (∀ a b, k (a * b) = k a + ρ a * k b) → k 1 = 0 := by
    intro k hk
    have := hk 1 1
    simp only [mul_one, map_one, Units.val_one, one_mul, left_eq_add] at this
    exact this
  let F : FreeGroup Letter →* Aff A :=
    { toFun := fun a => ⟨ρ a, f a⟩, map_one' := by ext <;> simp [h0 hf]
      map_mul' := fun a b => by ext <;> simp [hf] }
  let G : FreeGroup Letter →* Aff A :=
    { toFun := fun a => ⟨ρ a, g a⟩, map_one' := by ext <;> simp [h0 hg]
      map_mul' := fun a b => by ext <;> simp [hg] }
  have : F = G := FreeGroup.ext_hom F G (by rintro (_ | _) <;> ext <;> simp [F, G, hu, hv])
  funext a
  exact congrArg Aff.tr (DFunLike.congr_fun this a)

/-! ## Fox derivatives on `ℤ[F₂]` -/

/-- The integral group ring `ℤ[F₂]`. -/
abbrev ZF := MonoidAlgebra ℤ (FreeGroup Letter)

/-- `g ↦ g` as a unit of `ℤ[F₂]`. -/
noncomputable def ofU : FreeGroup Letter →* ZFˣ := (MonoidAlgebra.of ℤ _).toHomUnits

@[simp] lemma ofU_val (g : FreeGroup Letter) : (ofU g : ZF) = MonoidAlgebra.of ℤ _ g := rfl

/-- The homomorphism `F₂ → Aff ℤ[F₂]`, `y ↦ (y, δ_{xy})`, whose translation part is the Fox
derivative `∂_x`. -/
noncomputable def foxAff (x : Letter) : FreeGroup Letter →* Aff ZF :=
  FreeGroup.lift fun y => ⟨ofU (.of y), if y = x then 1 else 0⟩

/-- The **Fox derivative** `∂_x g ∈ ℤ[F₂]` of a group element. -/
noncomputable def fox (x : Letter) (g : FreeGroup Letter) : ZF := (foxAff x g).tr

/-- The linear part of `foxAff x g` is `g` itself. -/
lemma foxAff_lin (x : Letter) (g : FreeGroup Letter) : (foxAff x g).lin = ofU g := by
  have : Aff.linHom.comp (foxAff x) = ofU :=
    FreeGroup.ext_hom _ _ fun a => by simp [foxAff, Aff.linHom]
  exact DFunLike.congr_fun this g

/-- **Leibniz rule** `∂_x(gh) = ∂_x g + g ∂_x h`. -/
theorem fox_mul (x : Letter) (g h : FreeGroup Letter) :
    fox x (g * h) = fox x g + MonoidAlgebra.of ℤ _ g * fox x h := by
  simp [fox, foxAff_lin]

/-- `∂_x(y) = δ_{xy}`: `∂_u u = 1`, `∂_u v = 0`. -/
@[simp] theorem fox_of (x y : Letter) : fox x (.of y) = if y = x then 1 else 0 := by
  simp [fox, foxAff]

/-- `∂_x(1) = 0`. -/
@[simp] theorem fox_one (x : Letter) : fox x 1 = 0 := by simp [fox]

/-- `∂_x(g⁻¹) = -g⁻¹ ∂_x(g)`. -/
theorem fox_inv (x : Letter) (g : FreeGroup Letter) :
    fox x g⁻¹ = -(MonoidAlgebra.of ℤ _ g⁻¹ * fox x g) := by
  have h := fox_mul x g⁻¹ g
  rw [inv_mul_cancel, fox_one] at h
  exact eq_neg_of_add_eq_zero_left h.symm

/-- The `ℤ`-linear extension `∂_x : ℤ[F₂] → ℤ[F₂]`. -/
noncomputable def foxLin (x : Letter) : ZF →+ ZF :=
  MonoidAlgebra.liftNC (Int.castRingHom ZF : ℤ →+ ZF) (fox x)

/-- `∂_x` on group elements is the restriction of its linear extension. -/
@[simp] theorem foxLin_of (x : Letter) (g : FreeGroup Letter) :
    foxLin x (MonoidAlgebra.of ℤ _ g) = fox x g := by
  simp [foxLin, MonoidAlgebra.of_apply, MonoidAlgebra.liftNC_single]

/-- **Crowell–Fox fundamental formula** in `ℤ[F₂]`: `∂_u g (u-1) + ∂_v g (v-1) = g - 1`. -/
theorem crowellFox_groupRing (g : FreeGroup Letter) :
    fox u g * (MonoidAlgebra.of ℤ _ (.of u) - 1) + fox v g * (MonoidAlgebra.of ℤ _ (.of v) - 1)
      = MonoidAlgebra.of ℤ _ g - 1 := by
  have := cocycle_ext ofU
    (f := fun g => fox u g * (MonoidAlgebra.of ℤ _ (.of u) - 1) +
      fox v g * (MonoidAlgebra.of ℤ _ (.of v) - 1))
    (g := fun g => MonoidAlgebra.of ℤ _ g - 1)
    (fun a b => by simp only [fox_mul, ofU_val]; noncomm_ring)
    (fun a b => by simp only [map_mul, ofU_val]; noncomm_ring)
    (by simp) (by simp)
  exact congrFun this g

/-! ## The universal character and the word cocycles -/

section Character

variable {R : Type*} [CommRing R] (X Y : Rˣ)

/-- The values of the universal character on the letters: `u ↦ X`, `v ↦ Y`. -/
def gen : Letter → Rˣ
  | u => X
  | v => Y

/-- The universal character on `F₂`, `χ(u) = X`, `χ(v) = Y`. -/
def chiU : FreeGroup Letter →* Rˣ := FreeGroup.lift (gen X Y)

@[simp] lemma chiU_of_u : chiU X Y (.of u) = X := by simp [chiU, gen]
@[simp] lemma chiU_of_v : chiU X Y (.of v) = Y := by simp [chiU, gen]

/-- The universal character as a ring homomorphism `χ : ℤ[F₂] → R`. -/
noncomputable def chi : ZF →+* R :=
  (MonoidAlgebra.lift ℤ R (FreeGroup Letter) ((Units.coeHom R).comp (chiU X Y))).toRingHom

@[simp] lemma chi_of (g : FreeGroup Letter) :
    chi X Y (MonoidAlgebra.of ℤ _ g) = chiU X Y g := by
  simp [chi]

/-- The **word cocycle** `S = χ ∘ ∂_u`. -/
noncomputable def foxS (g : FreeGroup Letter) : R := chi X Y (fox u g)

/-- The companion cocycle `T = χ ∘ ∂_v`. -/
noncomputable def foxT (g : FreeGroup Letter) : R := chi X Y (fox v g)

/-- **Prop. 1.6 (cocycle law).** `S(gh) = S(g) + χ(g) S(h)`. -/
theorem foxS_mul (g h : FreeGroup Letter) :
    foxS X Y (g * h) = foxS X Y g + chiU X Y g * foxS X Y h := by
  simp only [foxS, fox_mul, map_add, map_mul, chi_of]

/-- The cocycle law for `T`. -/
theorem foxT_mul (g h : FreeGroup Letter) :
    foxT X Y (g * h) = foxT X Y g + chiU X Y g * foxT X Y h := by
  simp only [foxT, fox_mul, map_add, map_mul, chi_of]

@[simp] lemma foxS_of_u : foxS X Y (.of u) = 1 := by simp [foxS]
@[simp] lemma foxS_of_v : foxS X Y (.of v) = 0 := by simp [foxS]
@[simp] lemma foxT_of_u : foxT X Y (.of u) = 0 := by simp [foxT]
@[simp] lemma foxT_of_v : foxT X Y (.of v) = 1 := by simp [foxT]

/-- **Prop. 1.6 (uniqueness).** `S(u) = 1`, `S(v) = 0` and the cocycle law determine `S`. -/
theorem foxS_unique {f : FreeGroup Letter → R} (hf : ∀ a b, f (a * b) = f a + chiU X Y a * f b)
    (hu : f (.of u) = 1) (hv : f (.of v) = 0) : f = foxS X Y :=
  cocycle_ext (chiU X Y) hf (foxS_mul X Y) (by simp [hu]) (by simp [hv])

@[simp] lemma foxS_one : foxS X Y 1 = 0 := by simp [foxS, fox]

/-- `S(g⁻¹) = -χ(g)⁻¹ S(g)`. -/
theorem foxS_inv (g : FreeGroup Letter) :
    foxS X Y g⁻¹ = -(↑(chiU X Y g)⁻¹ * foxS X Y g) := by
  have h := foxS_mul X Y g g⁻¹
  rw [mul_inv_cancel, foxS_one] at h
  have hu : (↑(chiU X Y g)⁻¹ : R) * chiU X Y g = 1 := Units.inv_mul _
  linear_combination (-(↑(chiU X Y g)⁻¹ : R)) * h + (-foxS X Y g⁻¹) * hu

/-- **Crowell–Fox fundamental formula** after `χ`: `(X-1) S(g) + (Y-1) T(g) = χ(g) - 1`. -/
theorem crowellFox (g : FreeGroup Letter) :
    ((X : R) - 1) * foxS X Y g + ((Y : R) - 1) * foxT X Y g = chiU X Y g - 1 := by
  have := congrArg (chi X Y) (crowellFox_groupRing g)
  simp only [map_add, map_mul, map_sub, map_one, chi_of, chiU_of_u, chiU_of_v] at this
  rw [← this, foxS, foxT]; ring

/-- **Prop. 1.8 (conjugation formula).** `S(g w g⁻¹) = χ(g) S(w) + S(g) (1 - χ(w))`. -/
theorem foxS_conj (g w : FreeGroup Letter) :
    foxS X Y (g * w * g⁻¹) = chiU X Y g * foxS X Y w + foxS X Y g * (1 - chiU X Y w) := by
  rw [foxS_mul, foxS_mul, foxS_inv, map_mul]
  have hu : (chiU X Y g : R) * ↑(chiU X Y g)⁻¹ = 1 := Units.mul_inv _
  simp only [Units.val_mul]
  linear_combination (-(chiU X Y w : R) * foxS X Y g) * hu

/-- `χ` is a class function: `χ(g w g⁻¹) = χ(w)`. -/
theorem chiU_conj (g w : FreeGroup Letter) : chiU X Y (g * w * g⁻¹) = chiU X Y w := by
  simp [mul_assoc]

/-- **Prop. 1.8 (conjugacy invariance).** Modulo the closure ideal `(1 - χ(w))`, the class of
`S(g w g⁻¹)` is the class of `S(w)` times the monomial unit `χ(g)`; the ideal itself is the same
for `w` and `g w g⁻¹`. -/
theorem foxS_conj_mod (g w : FreeGroup Letter) :
    Ideal.Quotient.mk (Ideal.span {1 - (chiU X Y w : R)}) (foxS X Y (g * w * g⁻¹)) =
      Ideal.Quotient.mk _ (chiU X Y g : R) * Ideal.Quotient.mk _ (foxS X Y w) := by
  rw [← map_mul, Ideal.Quotient.eq, foxS_conj]
  exact Ideal.mem_span_singleton.2 ⟨foxS X Y g, by ring⟩

end Character

/-! ## Positive words -/

/-- A positive word `x₁ ⋯ x_E` over `{u, v}`, as an element of `F₂`. -/
def pos (l : List Letter) : FreeGroup Letter := (l.map FreeGroup.of).prod

@[simp] lemma pos_nil : pos [] = 1 := rfl
@[simp] lemma pos_cons (a : Letter) (l : List Letter) : pos (a :: l) = .of a * pos l := by
  simp [pos]
@[simp] lemma pos_append (l₁ l₂ : List Letter) : pos (l₁ ++ l₂) = pos l₁ * pos l₂ := by
  simp [pos]

section Semiring

variable {R : Type*} [CommSemiring R] (x y : R)

/-- Letter values `u ↦ x`, `v ↦ y` in an arbitrary commutative semiring. -/
def val : Letter → R
  | u => x
  | v => y

/-- The character on positive words, `χ(w) = x^{#u} y^{#v}` (no inverses needed). -/
def mono (l : List Letter) : R := (l.map (val x y)).prod

/-- The Fox cocycle on positive words, for arbitrary ring elements `x, y`: the recursion
`S(a w) = S(a) + χ(a) S(w)` with `S(u) = 1`, `S(v) = 0`. -/
def foxSP : List Letter → R
  | [] => 0
  | a :: l => (if a = u then 1 else 0) + val x y a * foxSP l

/-- The companion `T` on positive words (`T(u) = 0`, `T(v) = 1`). -/
def foxTP : List Letter → R
  | [] => 0
  | a :: l => (if a = v then 1 else 0) + val x y a * foxTP l

@[simp] lemma mono_nil : mono x y [] = 1 := rfl
@[simp] lemma mono_cons (a : Letter) (l : List Letter) :
    mono x y (a :: l) = val x y a * mono x y l := rfl
@[simp] lemma foxSP_nil : foxSP x y [] = 0 := rfl
@[simp] lemma foxSP_cons (a : Letter) (l : List Letter) :
    foxSP x y (a :: l) = (if a = u then 1 else 0) + val x y a * foxSP x y l := rfl
@[simp] lemma foxTP_nil : foxTP x y [] = 0 := rfl
@[simp] lemma foxTP_cons (a : Letter) (l : List Letter) :
    foxTP x y (a :: l) = (if a = v then 1 else 0) + val x y a * foxTP x y l := rfl
omit [CommSemiring R] in
@[simp] lemma val_u : val x y u = x := rfl
omit [CommSemiring R] in
@[simp] lemma val_v : val x y v = y := rfl

/-- `χ` does not see the order of the letters. -/
lemma mono_reverse (l : List Letter) : mono x y l.reverse = mono x y l := by
  simp [mono, List.prod_reverse]

lemma mono_append (l₁ l₂ : List Letter) : mono x y (l₁ ++ l₂) = mono x y l₁ * mono x y l₂ := by
  simp [mono]

/-- The cocycle law on positive words. -/
lemma foxSP_append (l₁ l₂ : List Letter) :
    foxSP x y (l₁ ++ l₂) = foxSP x y l₁ + mono x y l₁ * foxSP x y l₂ := by
  induction l₁ with
  | nil => simp
  | cons a l ih => simp only [List.cons_append, foxSP_cons, ih, mono_cons]; ring

/-- `χ(w) = x^{#u(w)} y^{#v(w)}`. -/
lemma mono_eq (l : List Letter) : mono x y l = x ^ l.count u * y ^ l.count v := by
  induction l with
  | nil => simp
  | cons a l ih => cases a <;> simp [ih, pow_succ] <;> ring

/-- **Prop. 1.5 (closed form on positive words).** For `w = x₀ x₁ ⋯ x_{E-1}`,
`S(w) = Σ_{k : x_k = u} x^{α_k} y^{β_k}` with `α_k, β_k` the numbers of `u`'s and `v`'s before
position `k`. -/
theorem foxSP_eq_sum (l : List Letter) :
    foxSP x y l = ∑ k ∈ Finset.range l.length,
      if l[k]? = some u then x ^ (l.take k).count u * y ^ (l.take k).count v else 0 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [foxSP_cons, ih, List.length_cons, Finset.sum_range_succ', Finset.mul_sum, add_comm]
    congr 1
    · refine Finset.sum_congr rfl fun k _ => ?_
      cases a <;> simp only [List.getElem?_cons_succ, List.take_succ_cons, List.count_cons,
        val_u, val_v] <;> split_ifs <;> simp_all [pow_succ] <;> ring
    · cases a <;> simp

end Semiring

/-- The free-group cocycle on a positive word is the positive-word recursion. -/
theorem foxS_pos {R : Type*} [CommRing R] (X Y : Rˣ) (l : List Letter) :
    foxS X Y (pos l) = foxSP (X : R) Y l := by
  induction l with
  | nil => simp
  | cons a l ih => cases a <;> simp [foxS_mul, ih]

/-- The same for `T`. -/
theorem foxT_pos {R : Type*} [CommRing R] (X Y : Rˣ) (l : List Letter) :
    foxT X Y (pos l) = foxTP (X : R) Y l := by
  induction l with
  | nil => simp [foxT, fox]
  | cons a l ih => cases a <;> simp [foxT_mul, ih]

/-- The character on a positive word. -/
theorem chiU_pos {R : Type*} [CommRing R] (X Y : Rˣ) (l : List Letter) :
    (chiU X Y (pos l) : R) = mono (X : R) Y l := by
  induction l with
  | nil => simp
  | cons a l ih => cases a <;> simp [ih]

/-- **Rotations (after Prop. 1.8).** The rotation `qp` of `pq` is the conjugate
`(pq)` by `p⁻¹`, so modulo `(1 - χ(pq))` its cocycle is `χ(p)⁻¹ S(pq)`. -/
theorem foxS_rotate_mod {R : Type*} [CommRing R] (X Y : Rˣ) (p q : List Letter) :
    Ideal.Quotient.mk (Ideal.span {1 - (chiU X Y (pos (p ++ q)) : R)}) (foxS X Y (pos (q ++ p))) =
      Ideal.Quotient.mk _ (↑(chiU X Y (pos p))⁻¹ : R) *
        Ideal.Quotient.mk _ (foxS X Y (pos (p ++ q))) := by
  have h : pos (q ++ p) = (pos p)⁻¹ * pos (p ++ q) * (pos p)⁻¹⁻¹ := by
    simp
  rw [h, foxS_conj_mod, map_inv]

section Symmetry

variable {R : Type*} [CommRing R]

/-- The complement `u ↔ v`. -/
def swapL : Letter → Letter
  | u => v
  | v => u

/-- **Complement (ingredient of Prop. 2.5).** `S(w̄)(X, Y) = T(w)(Y, X)`. -/
theorem foxSP_complement (x y : R) (l : List Letter) :
    foxSP x y (l.map swapL) = foxTP y x l := by
  induction l with
  | nil => rfl
  | cons a l ih => cases a <;> simp [swapL, ih]

/-- **Reversal (ingredient of Prop. 2.5).** With `x x' = 1`, `y y' = 1`:
`x S(wᴿ)(x, y) = χ(w) S(w)(x', y')`, i.e. reversal is `X ↦ X⁻¹, Y ↦ Y⁻¹` up to a monomial. -/
theorem foxSP_reverse (x y x' y' : R) (hx : x * x' = 1) (hy : y * y' = 1) (l : List Letter) :
    x * foxSP x y l.reverse = mono x y l * foxSP x' y' l := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.reverse_cons, foxSP_append, mono_reverse]
    cases a
    · simp only [foxSP_cons, foxSP_nil, ite_true, val_u, mul_zero, add_zero, mono_cons]
      linear_combination ih - (mono x y l * foxSP x' y' l) * hx
    · simp only [foxSP_cons, foxSP_nil, reduceCtorEq, ite_false, val_v, mul_zero, add_zero,
        zero_add, mono_cons]
      linear_combination ih - (mono x y l * foxSP x' y' l) * hy

end Symmetry

/-! ## The dictionary with the project's gap words -/

/-- **Dictionary.** The gap word `(d₀, …, d_{o-1})` (a Syracuse word, all `dᵢ ≥ 1`) is the
`{u, v}`-word `u v^{d₀-1} u v^{d₁-1} ⋯ u v^{d_{o-1}-1}` of the accelerated `T`-map
(`u : x ↦ (3x+1)/2`, `v : x ↦ x/2`). Its type is `(E, o) = (w.sum, w.length)`. -/
def toLetters : Word → List Letter
  | [] => []
  | d :: w => u :: List.replicate (d - 1) v ++ toLetters w

@[simp] lemma toLetters_nil : toLetters [] = [] := rfl
@[simp] lemma toLetters_cons (d : ℕ) (w : Word) :
    toLetters (d :: w) = u :: List.replicate (d - 1) v ++ toLetters w := rfl

/-- The type of the dictionary word: `#u = o`. -/
@[simp] lemma count_u_toLetters (w : Word) : (toLetters w).count u = w.length := by
  induction w with
  | nil => rfl
  | cons d w ih => simp [List.count_replicate, ih, add_comm]

/-- The type of the dictionary word: length `E` (for a positive gap word). -/
lemma length_toLetters {w : Word} (hw : w.Pos) : (toLetters w).length = w.sum := by
  induction w with
  | nil => rfl
  | cons d w ih =>
    have hd : 1 ≤ d := hw d (by simp)
    have := ih fun d' hd' => hw d' (by simp [hd'])
    simp only [toLetters_cons, List.length_cons, List.length_append, List.length_replicate,
      this, List.sum_cons]
    omega

section Bridge

variable {R : Type*} [CommRing R]

lemma foxSP_replicate_v (x y : R) (n : ℕ) (l : List Letter) :
    foxSP x y (List.replicate n v ++ l) = y ^ n * foxSP x y l := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ, ih, pow_succ]; ring

lemma foxSP_replicate_v' (x y : R) (n : ℕ) : foxSP x y (List.replicate n v) = 0 := by
  simpa using foxSP_replicate_v x y n []

lemma mono_replicate_v (x y : R) (n : ℕ) : mono x y (List.replicate n v) = y ^ n := by
  rw [mono_eq]; simp [List.count_replicate]

/-- The bridge with `B` multiplied through (no truncated subtraction). -/
lemma S_bridge_aux (A B C : R) (hBC : B * C = 1) {w : Word} (hw : w.Pos) :
    B * S A B w = B ^ w.length * foxSP (A * C) A (toLetters w) := by
  induction w with
  | nil => simp
  | cons d w ih =>
    have hd : 1 ≤ d := hw d (by simp)
    have ih := ih fun d' hd' => hw d' (by simp [hd'])
    obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
    simp only [S_cons, toLetters_cons, List.cons_append, foxSP_cons, ite_true, val_u,
      foxSP_replicate_v, List.length_cons, add_tsub_cancel_right]
    linear_combination A ^ (n + 1) * ih -
      (A ^ (n + 1) * B ^ w.length * foxSP (A * C) A (toLetters w)) * hBC

/-- **Bridge to `Basic`.** For a Syracuse gap word `w` (all gaps `≥ 1`) of type `(E, o)`,
`S_Basic(A, B; w) = B^{o-1} · S_Fox(A B⁻¹, A; u v^{d₀-1} ⋯ u v^{d_{o-1}-1})`: the project's
`S X Y` is the Fox cocycle of the dictionary word at `χ(u) = X Y⁻¹`, `χ(v) = X`, times the
monomial `Y^{o-1}`. Stated with `C = B⁻¹` so that it holds in every commutative semiring. -/
theorem S_eq_foxSP (A B C : R) (hBC : B * C = 1) {w : Word} (hw : w.Pos) :
    S A B w = B ^ (w.length - 1) * foxSP (A * C) A (toLetters w) := by
  have h := S_bridge_aux A B C hBC hw
  rcases w with _ | ⟨d, w⟩
  · simp
  · simp only [List.length_cons, add_tsub_cancel_right] at h ⊢
    linear_combination C * h - (S A B (d :: w)) * hBC +
      (B ^ w.length * foxSP (A * C) A (toLetters (d :: w))) * hBC

/-- `χ` of the dictionary word at `X = B A⁻¹`, `Y = A⁻¹`, times `A^E`, is `B^o`. -/
lemma mono_toLetters_aux (A B C : R) (hAC : A * C = 1) {w : Word} (hw : w.Pos) :
    mono (B * C) C (toLetters w) * A ^ w.sum = B ^ w.length := by
  induction w with
  | nil => simp
  | cons d w ih =>
    have hd : 1 ≤ d := hw d (by simp)
    have ih := ih fun d' hd' => hw d' (by simp [hd'])
    obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
    have hp : (A * C) ^ (n + 1) = 1 := by rw [hAC, one_pow]
    simp only [toLetters_cons, List.cons_append, mono_cons, mono_append, mono_replicate_v,
      val_u, List.sum_cons, List.length_cons, add_tsub_cancel_right, pow_add, pow_one]
    linear_combination (B * (A * C) ^ (n + 1)) * ih + B ^ (w.length + 1) * hp

/-- The reversed bridge with `A` multiplied through. -/
lemma S_bridge_rev_aux (A B C : R) (hAC : A * C = 1) {w : Word} (hw : w.Pos) :
    A * S A B w = A ^ w.sum * foxSP (B * C) C (toLetters w).reverse := by
  induction w with
  | nil => simp
  | cons d w ih =>
    have hd : 1 ≤ d := hw d (by simp)
    have hw' : Word.Pos w := fun d' hd' => hw d' (by simp [hd'])
    have ih := ih hw'
    have hm := mono_toLetters_aux A B C hAC hw'
    obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
    have hp : (A * C) ^ n = 1 := by rw [hAC, one_pow]
    simp only [S_cons, toLetters_cons, List.reverse_cons, List.reverse_append,
      List.reverse_replicate, foxSP_append, foxSP_replicate_v', mono_reverse, mono_replicate_v,
      add_tsub_cancel_right, foxSP_cons, foxSP_nil, ite_true, mul_zero,
      add_zero, List.sum_cons, pow_add, pow_one]
    linear_combination A ^ (n + 1) * ih - A * (A * C) ^ n * hm - A * B ^ w.length * hp

/-- **Bridge to `Basic`, reversed form.** For a Syracuse gap word `w` of type `(E, o)`,
`S_Basic(A, B; w) = A^{E-1} · S_Fox(B A⁻¹, A⁻¹; wᴿ)` where `wᴿ` is the dictionary word read
backwards. This is the form in which the Fox cocycle computes the affine word map of the
`T`-map (see `tWord_eq`). Stated with `C = A⁻¹`. -/
theorem S_eq_foxSP_reverse (A B C : R) (hAC : A * C = 1) {w : Word} (hw : w.Pos) :
    S A B w = A ^ (w.sum - 1) * foxSP (B * C) C (toLetters w).reverse := by
  have h := S_bridge_rev_aux A B C hAC hw
  rcases Nat.eq_zero_or_pos w.sum with h0 | h0
  · have : w = [] := by
      rcases w with _ | ⟨d, w⟩
      · rfl
      · have := hw d (by simp); simp at h0; omega
    subst this; simp
  · obtain ⟨k, hk⟩ : ∃ k, w.sum = k + 1 := ⟨w.sum - 1, by omega⟩
    rw [hk] at h ⊢
    simp only [add_tsub_cancel_right]
    linear_combination C * h - (S A B w) * hAC +
      (A ^ k * foxSP (B * C) C (toLetters w).reverse) * hAC

end Bridge

/-- The free-group form of the bridge: for units `A, B` of a commutative ring,
`S_Basic(A, B; w) = B^{o-1} S(pos(toLetters w))` with `χ(u) = A B⁻¹`, `χ(v) = A`. -/
theorem S_eq_foxS {R : Type*} [CommRing R] (A B : Rˣ) {w : Word} (hw : w.Pos) :
    S (A : R) B w = (B : R) ^ (w.length - 1) * foxS (A * B⁻¹) A (pos (toLetters w)) := by
  rw [foxS_pos, Units.val_mul]
  exact S_eq_foxSP _ _ _ (Units.mul_inv B) hw

/-! ## The fixed point of the affine word map (correcting Remark 1.10) -/

/-- One letter of the accelerated `T`-map: `u : z ↦ (3z+1)/2`, `v : z ↦ z/2`. -/
def tStep : Letter → ℚ → ℚ
  | u, z => (3 * z + 1) / 2
  | v, z => z / 2

/-- The word map, applying the letters from left to right (as in a parity sequence). -/
def tWord (l : List Letter) (z : ℚ) : ℚ := l.foldl (fun z a => tStep a z) z

/-- The word map is affine, `z ↦ χ(w) z + ½ S(wᴿ)` at `(X, Y) = (3/2, 1/2)`: its translation
part is the Fox cocycle of the **reversed** word. -/
theorem tWord_eq (l : List Letter) (z : ℚ) :
    tWord l z = mono (3 / 2) (1 / 2) l * z + 1 / 2 * foxSP (3 / 2) (1 / 2) l.reverse := by
  induction l generalizing z with
  | nil => simp [tWord]
  | cons a l ih =>
    have : tWord (a :: l) z = tWord l (tStep a z) := rfl
    rw [this, ih, List.reverse_cons, foxSP_append, mono_reverse]
    cases a <;> simp [tStep] <;> ring

/-- **Corrected Remark 1.10.** A fixed point `a` of the word map of `w` (a cycle with parity
word `w`) satisfies `(1 - χ(w)) a = ½ S(wᴿ)` at `(X, Y) = (3/2, 1/2)`. -/
theorem tWord_fixed {l : List Letter} {a : ℚ} (h : tWord l a = a) :
    (1 - mono (3 / 2) (1 / 2) l) * a = 1 / 2 * foxSP (3 / 2) (1 / 2) l.reverse := by
  rw [tWord_eq] at h
  linear_combination -h

/-- **Remark 1.10 is false as written.** The word `uv` is the cycle `{1, 2}` (`tWord [u,v] 1 = 1`)
but `S(w) / (χ(w) - 1)` at `(X, Y) = (2, 3)` is `1/5`, not `1`. -/
theorem remark_1_10_counterexample :
    tWord [u, v] 1 = 1 ∧ foxSP (2 : ℚ) 3 [u, v] / (mono (2 : ℚ) 3 [u, v] - 1) = 1 / 5 := by
  constructor <;> norm_num [tWord, tStep, mono]

/-! ## The coprime normal form `ℤ[t^{±1}]` and the catalogue -/

open LaurentPolynomial Polynomial

section Reduced

variable (K : Type*) [CommRing K]

/-- `T n = t^n` as a unit of `K[t^{±1}]`. -/
noncomputable def tU (n : ℤ) : (K[T;T⁻¹])ˣ :=
  ⟨T n, T (-n), by rw [← T_add]; simp, by rw [← T_add]; simp⟩

@[simp] lemma tU_val (n : ℤ) : (tU K n : K[T;T⁻¹]) = T n := rfl

/-- **The reduced cocycle** of a positive word `w` of type `(E, o)`: `S(w)` under the closure
substitution `X ↦ t^{-(E-o)}`, `Y ↦ t^{o}` of §2 (Prop. 1.9 with `d = 1`). Here `E - o = #v`. -/
noncomputable def redS (l : List Letter) : K[T;T⁻¹] :=
  foxS (tU K (-(l.count v : ℤ))) (tU K (l.count u)) (pos l)

/-- The reduced companion cocycle `T(w)` under the same substitution. -/
noncomputable def redT (l : List Letter) : K[T;T⁻¹] :=
  foxT (tU K (-(l.count v : ℤ))) (tU K (l.count u)) (pos l)

lemma redS_eq (l : List Letter) :
    redS K l = foxSP (T (-(l.count v : ℤ))) (T (l.count u)) l := by
  simp [redS, foxS_pos]

lemma redT_eq (l : List Letter) :
    redT K l = foxTP (T (-(l.count v : ℤ))) (T (l.count u)) l := by
  simp [redT, foxT_pos]

/-- The substitution kills the closure relation: `χ(w) ↦ 1`. -/
theorem chiU_red (l : List Letter) :
    (chiU (tU K (-(l.count v : ℤ))) (tU K (l.count u)) (pos l) : K[T;T⁻¹]) = 1 := by
  rw [chiU_pos, mono_eq]
  simp only [tU_val, T_pow, ← T_add]
  rw [← T_zero]; congr 1; ring

end Reduced

/-! ### The four known cycles -/

/-- The trivial cycle `u` (`x = -1`): `P_w = 1`. -/
theorem redS_u : redS ℤ [u] = 1 := by norm_num [redS_eq]

/-- The trivial cycle `uv` (`x = 1`): `P_w = 1`. -/
theorem redS_uv : redS ℤ [u, v] = 1 := by norm_num [redS_eq]

/-- The `-5` cycle `uuv`: `P_w = t + 1 = Φ₂`. -/
theorem redS_uuv : redS ℤ [u, u, v] = T (-1) * toLaurent (cyclotomic 2 ℤ) := by
  simp only [redS_eq, cyclotomic_two]
  norm_num [-T_mul]
  simp only [mul_add, mul_one, ← T_add]
  norm_num [-T_mul]

/-- The fixed points of the four cycle words are `-1, 1, -5, -17`. -/
theorem tWord_cycles : tWord [u] (-1) = -1 ∧ tWord [u, v] 1 = 1 ∧ tWord [u, u, v] (-5) = -5 ∧
    tWord [u, u, u, u, v, u, u, u, v, v, v] (-17) = -17 := by
  norm_num [tWord, tStep]

/-- The `-17` cycle in the project's gap-word encoding: gap word `(1,1,1,2,1,1,4)`. -/
theorem toLetters_minus17 :
    toLetters [1, 1, 1, 2, 1, 1, 4] = [u, u, u, u, v, u, u, u, v, v, v] := rfl

/-- The `-17` cycle in `Basic`'s cycle equation: `S(2,3) = 2363 = (-139)(-17)`, `D = 2^{11} - 3^7
= -139`. -/
theorem minus17_basic : Sz [1, 1, 1, 2, 1, 1, 4] = 2363 ∧ Dz [1, 1, 1, 2, 1, 1, 4] = -139 := by
  norm_num [Sz, Dz, S, D]

/-- The cleared reduced cocycle of the `-17` cycle. -/
noncomputable def P17 : ℤ[X] := X ^ 17 + X ^ 13 + X ^ 9 + X ^ 8 + X ^ 5 + X ^ 4 + 1

/-- The `-17` cycle `uuuuvuuuvvv`, type `(11, 7)`: `S ↦ t^{-17} P_w`. -/
theorem redS_minus17 : redS ℤ [u, u, u, u, v, u, u, u, v, v, v] = T (-17) * toLaurent P17 := by
  simp only [redS_eq, P17]
  norm_num [-T_mul]
  simp only [mul_add, mul_one, ← T_add]
  norm_num [-T_mul]
  abel

/-- `P_w = Φ₇ · R_w` with core `R_w = t^{11} - t^{10} + t^7 - t^6 + t^4 - t + 1`. -/
theorem P17_factor :
    P17 = cyclotomic 7 ℤ * (X ^ 11 - X ^ 10 + X ^ 7 - X ^ 6 + X ^ 4 - X + 1) := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  simp only [P17, cyclotomic_prime, Finset.sum_range_succ, Finset.sum_range_zero]
  ring

/-- Cor. 2.2 for the `-17` core: `R_w = 1 + (t - 1) Q_w`, `Q_w = t^{10} + t^6 + t^3 + t^2 + t`. -/
theorem R17_tower : (X ^ 11 - X ^ 10 + X ^ 7 - X ^ 6 + X ^ 4 - X + 1 : ℤ[X]) =
    1 + (X - 1) * (X ^ 10 + X ^ 6 + X ^ 3 + X ^ 2 + X) := by ring

/-! ### Catalogue facts -/

/-- `uuuv`, type `(4, 3)`: `P_w = Φ₃` (cyclotomic; corrects the early `(4,3)` guess). -/
theorem redS_uuuv : redS ℤ [u, u, u, v] = T (-2) * toLaurent (cyclotomic 3 ℤ) := by
  simp only [redS_eq, cyclotomic_three]
  norm_num [-T_mul]
  simp only [mul_add, mul_one, ← T_add]
  norm_num [-T_mul]
  abel

/-- `uuvuvvv`, type `(7, 3)`: `S ↦ t^{-5} (t^5 + t + 1)`. -/
theorem redS_plastic : redS ℤ [u, u, v, u, v, v, v] = T (-5) * toLaurent (X ^ 5 + X + 1) := by
  simp only [redS_eq]
  norm_num [-T_mul]
  simp only [mul_add, mul_one, ← T_add]
  norm_num [-T_mul]
  abel

/-- **Prop. 2.3.** `t^5 + t + 1 = Φ₃(t) (t³ - t² + 1)`. -/
theorem plastic_factor : (X ^ 5 + X + 1 : ℤ[X]) = cyclotomic 3 ℤ * (X ^ 3 - X ^ 2 + 1) := by
  rw [cyclotomic_three]; ring

/-- The factor `t³ - t² + 1` is the plastic polynomial `x³ - x - 1` under `t = -1/x`:
`(-x⁻¹)³ - (-x⁻¹)² + 1 = x⁻³ (x³ - x - 1)`. So it is the reciprocal of `x³ - x - 1` **composed
with `t ↦ -t`**, not `x³ - x - 1` or its reciprocal; the Mahler measure is the same. -/
theorem plastic_factor_rel {K : Type*} [CommRing K] (x : Kˣ) :
    (-(↑x⁻¹ : K)) ^ 3 - (-(↑x⁻¹ : K)) ^ 2 + 1 = (↑x⁻¹ : K) ^ 3 * ((x : K) ^ 3 - x - 1) := by
  have h : (x : K) * ↑x⁻¹ = 1 := Units.mul_inv x
  linear_combination ((↑x⁻¹ : K) ^ 2 - ((x : K) * ↑x⁻¹) ^ 2 - (x : K) * ↑x⁻¹ - 1) * h

/-- Lehmer's polynomial `L(x) = x^{10} + x^9 - x^7 - x^6 - x^5 - x^4 - x^3 + x + 1`. -/
noncomputable def lehmer : ℤ[X] :=
  X ^ 10 + X ^ 9 - X ^ 7 - X ^ 6 - X ^ 5 - X ^ 4 - X ^ 3 + X + 1

/-- The cleared reduced cocycle of the Lehmer word. -/
noncomputable def PLehmer : ℤ[X] := X ^ 16 + X ^ 13 + X ^ 11 + X ^ 8 + X ^ 5 + X ^ 3 + 1

/-- `uuuvuuvvvuuv`, type `(12, 7)`: `S ↦ t^{-13} P_w`. -/
theorem redS_lehmer :
    redS ℤ [u, u, u, v, u, u, v, v, v, u, u, v] = T (-13) * toLaurent PLehmer := by
  simp only [redS_eq, PLehmer]
  norm_num [-T_mul]
  simp only [mul_add, mul_one, ← T_add]
  norm_num [-T_mul]
  abel

/-- **Prop. 2.4 (corrected).** `P_w = Φ₇(t) · L(-t)`: the non-cyclotomic factor is Lehmer's
polynomial at `-t`, i.e. `t^{10} - t^9 + t^7 - t^6 + t^5 - t^4 + t^3 - t + 1`. -/
theorem PLehmer_factor : PLehmer = cyclotomic 7 ℤ * lehmer.comp (-X) := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  simp only [PLehmer, lehmer, cyclotomic_prime, Finset.sum_range_succ, Finset.sum_range_zero,
    add_comp, sub_comp, pow_comp, X_comp, one_comp]
  ring

/-- The non-cyclotomic factor written out, as printed in Prop. 2.4. -/
theorem lehmer_comp_neg : lehmer.comp (-X) =
    X ^ 10 - X ^ 9 + X ^ 7 - X ^ 6 + X ^ 5 - X ^ 4 + X ^ 3 - X + 1 := by
  simp only [lehmer, add_comp, sub_comp, pow_comp, X_comp, one_comp]
  ring

/-- Lehmer's polynomial itself does **not** divide `P_w` (evaluate at `2`: `1291 ∤ 76073`). -/
theorem lehmer_not_dvd : ¬ lehmer ∣ PLehmer := by
  rintro ⟨q, hq⟩
  have h := congrArg (eval 2) hq
  simp only [PLehmer, lehmer, eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_one] at h
  norm_num at h
  omega

/-! ## Prop. 1.9 for coprime type: `Λ/(1 - X^o Y^{E-o}) ≅ ℤ[t^{±1}]`, universal form -/

/-- Bezout in a commutative group: if `X^o Y^m = 1` and `o a + m b = 1` then `t = X^{-b} Y^{a}`
satisfies `t^{-m} = X` and `t^{o} = Y`. -/
lemma bezout_units {G : Type*} [CommGroup G] (X Y : G) {o m : ℕ} (h : X ^ o * Y ^ m = 1)
    (a b : ℤ) (hab : (o : ℤ) * a + m * b = 1) :
    (X ^ (-b) * Y ^ a) ^ (-(m : ℤ)) = X ∧ (X ^ (-b) * Y ^ a) ^ (o : ℤ) = Y := by
  have h' : X ^ (o : ℤ) * Y ^ (m : ℤ) = 1 := by simpa [zpow_natCast] using h
  have hY : Y ^ (m : ℤ) = (X ^ (o : ℤ))⁻¹ := eq_inv_of_mul_eq_one_right h'
  have hX : X ^ (o : ℤ) = (Y ^ (m : ℤ))⁻¹ := eq_inv_of_mul_eq_one_left h'
  constructor
  · calc (X ^ (-b) * Y ^ a) ^ (-(m : ℤ)) = X ^ (m * b) * (Y ^ (m : ℤ)) ^ (-a) := by
          rw [mul_zpow, ← zpow_mul, ← zpow_mul, ← zpow_mul]; congr 2 <;> ring
      _ = X ^ (m * b) * X ^ ((o : ℤ) * a) := by rw [hY, inv_zpow', neg_neg, ← zpow_mul]
      _ = X := by rw [← zpow_add, show (m : ℤ) * b + o * a = 1 by linarith, zpow_one]
  · calc (X ^ (-b) * Y ^ a) ^ (o : ℤ) = (X ^ (o : ℤ)) ^ (-b) * Y ^ (o * a) := by
          rw [mul_zpow, ← zpow_mul, ← zpow_mul, ← zpow_mul]; congr 2 <;> ring
      _ = Y ^ ((m : ℤ) * b) * Y ^ ((o : ℤ) * a) := by rw [hX, inv_zpow', neg_neg, ← zpow_mul]
      _ = Y := by rw [← zpow_add, show (m : ℤ) * b + o * a = 1 by linarith, zpow_one]

/-- The substitution `X ↦ t^{-m}`, `Y ↦ t^{o}` kills the closure relation `X^o Y^m = 1`. -/
theorem reparam_kills (o m : ℕ) : (tU ℤ (-(m : ℤ))) ^ o * (tU ℤ o) ^ m = 1 := by
  apply Units.ext
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, tU_val, T_pow, ← T_add, Units.val_one]
  rw [← T_zero]; congr 1; ring

/-- The exponents `n` at which two ring homomorphisms out of `R[t^{±1}]` agree on `t^n` form a
subgroup of `ℤ`. -/
def agree {R K : Type*} [CommRing R] [CommRing K] (f g : R[T;T⁻¹] →+* K) : AddSubgroup ℤ where
  carrier := {n | f (T n) = g (T n)}
  zero_mem' := show f (T 0) = g (T 0) by simp [T_zero]
  add_mem' := fun {i j} (hi : f (T i) = g (T i)) (hj : f (T j) = g (T j)) =>
    show f (T (i + j)) = g (T (i + j)) by rw [T_add, map_mul, map_mul, hi, hj]
  neg_mem' := fun {n} (hn : f (T n) = g (T n)) => show f (T (-n)) = g (T (-n)) by
    have h1 : f (T (-n)) * f (T n) = 1 := by rw [← map_mul, ← T_add]; simp [T_zero]
    have h2 : g (T n) * g (T (-n)) = 1 := by rw [← map_mul, ← T_add]; simp [T_zero]
    linear_combination g (T (-n)) * h1 - f (T (-n)) * h2 - f (T (-n)) * g (T (-n)) * hn

/-- Membership in `agree f g`. -/
lemma mem_agree {R K : Type*} [CommRing R] [CommRing K] {f g : R[T;T⁻¹] →+* K} {n : ℤ} :
    n ∈ agree f g ↔ f (T n) = g (T n) := Iff.rfl

/-- Ring homomorphisms out of `R[t^{±1}]` that agree on `R` and on `t` are equal. -/
lemma laurent_ringHom_ext {R K : Type*} [CommRing R] [CommRing K] {f g : R[T;T⁻¹] →+* K}
    (hC : f.comp C = g.comp C) (hT : f (T 1) = g (T 1)) : f = g := by
  apply AddMonoidAlgebra.ringHom_ext
  · intro b; exact RingHom.congr_fun hC b
  · intro n
    have : n • (1 : ℤ) ∈ agree f g := (agree f g).zsmul_mem (mem_agree.2 hT) n
    rwa [smul_eq_mul, mul_one, mem_agree] at this

/-- **Prop. 1.9, coprime case (universal form).** Let `gcd(o, m) = 1` (`m = E - o`). For every
commutative ring `K` and units `X, Y` with `X^o Y^m = 1` there is exactly one ring homomorphism
`ℤ[t^{±1}] → K` with `t^{-m} ↦ X` and `t^{o} ↦ Y`. -/
theorem reparam_universal {o m : ℕ} (hom : Nat.Coprime o m) {K : Type*} [CommRing K] (X Y : Kˣ)
    (h : X ^ o * Y ^ m = 1) :
    ∃! φ : ℤ[T;T⁻¹] →+* K, φ (T (-(m : ℤ))) = X ∧ φ (T o) = Y := by
  have hab : (o : ℤ) * Nat.gcdA o m + m * Nat.gcdB o m = 1 := by
    have := Nat.gcd_eq_gcd_ab o m
    rw [Nat.Coprime.gcd_eq_one hom] at this
    exact_mod_cast this.symm
  obtain ⟨hX, hY⟩ := bezout_units X Y h _ _ hab
  refine ⟨eval₂ (Int.castRingHom K) (X ^ (-Nat.gcdB o m) * Y ^ Nat.gcdA o m),
    ⟨by rw [eval₂_T, hX], by rw [eval₂_T, hY]⟩, ?_⟩
  rintro ψ ⟨hψX, hψY⟩
  set φ := eval₂ (Int.castRingHom K) (X ^ (-Nat.gcdB o m) * Y ^ Nat.gcdA o m)
  have hm : -(m : ℤ) ∈ agree ψ φ := by rw [mem_agree, hψX, eval₂_T, hX]
  have ho : (o : ℤ) ∈ agree ψ φ := by rw [mem_agree, hψY, eval₂_T, hY]
  have h1 : (1 : ℤ) ∈ agree ψ φ := by
    have := (agree ψ φ).add_mem ((agree ψ φ).zsmul_mem ho (Nat.gcdA o m))
      ((agree ψ φ).zsmul_mem hm (-Nat.gcdB o m))
    convert this using 1; simp only [smul_eq_mul]; linarith
  exact laurent_ringHom_ext (RingHom.ext_int _ _) h1

/-! ### The literal isomorphism `Λ/(1 - X^o Y^m) ≃ ℤ[t^{±1}]` -/

/-- `Λ = ℤ[X^{±1}, Y^{±1}]`, realised as `ℤ[X^{±1}][Y^{±1}]`. -/
abbrev Lam := (ℤ[T;T⁻¹])[T;T⁻¹]

/-- The variable `X ∈ Λˣ`. -/
noncomputable def Xl : Lamˣ := Units.map (C : ℤ[T;T⁻¹] →+* Lam).toMonoidHom (tU ℤ 1)

/-- The variable `Y ∈ Λˣ`. -/
noncomputable def Yl : Lamˣ := tU (ℤ[T;T⁻¹]) 1

/-- Ring homomorphisms out of `Λ` are determined by their values on `X` and `Y`. -/
lemma lam_ringHom_ext {K : Type*} [CommRing K] {f g : Lam →+* K}
    (hX : f Xl = g Xl) (hY : f Yl = g Yl) : f = g := by
  refine laurent_ringHom_ext (laurent_ringHom_ext (RingHom.ext_int _ _) ?_) hY
  simpa [Xl] using hX

/-- The evaluation `Λ → K`, `X ↦ x`, `Y ↦ y`. -/
noncomputable def liftLam {K : Type*} [CommRing K] (x y : Kˣ) : Lam →+* K :=
  eval₂ (eval₂ (Int.castRingHom K) x) y

@[simp] lemma liftLam_X {K : Type*} [CommRing K] (x y : Kˣ) : liftLam x y Xl = x := by
  simp only [liftLam, Xl, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, tU_val]
  rw [LaurentPolynomial.eval₂_C, LaurentPolynomial.eval₂_T, zpow_one]

@[simp] lemma liftLam_Y {K : Type*} [CommRing K] (x y : Kˣ) : liftLam x y Yl = y := by
  simp [liftLam, Yl]

/-- The closure ideal `(1 - X^o Y^m) ⊂ Λ` (for a word of type `(E, o)`, `m = E - o`). -/
noncomputable def closureIdeal (o m : ℕ) : Ideal Lam :=
  Ideal.span {1 - ((Xl ^ o * Yl ^ m : Lamˣ) : Lam)}

/-- `Λ/(1 - X^o Y^m) → ℤ[t^{±1}]`, `X ↦ t^{-m}`, `Y ↦ t^{o}`. -/
noncomputable def reparamFwd (o m : ℕ) : Lam ⧸ closureIdeal o m →+* ℤ[T;T⁻¹] :=
  Ideal.Quotient.lift _ (liftLam (tU ℤ (-(m : ℤ))) (tU ℤ o)) fun a ha => by
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    have := congrArg Units.val (reparam_kills o m)
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_one] at this
    rw [map_mul, map_sub, map_one, Units.val_mul, map_mul, Units.val_pow_eq_pow_val,
      Units.val_pow_eq_pow_val, map_pow, map_pow, liftLam_X, liftLam_Y, this, sub_self, mul_zero]

/-- The classes of `X, Y` as units of the quotient. -/
noncomputable def xq (o m : ℕ) : (Lam ⧸ closureIdeal o m)ˣ :=
  Units.map (Ideal.Quotient.mk _).toMonoidHom Xl
/-- The class of `Y`. -/
noncomputable def yq (o m : ℕ) : (Lam ⧸ closureIdeal o m)ˣ :=
  Units.map (Ideal.Quotient.mk _).toMonoidHom Yl

/-- The closure relation holds in the quotient. -/
lemma xq_yq_rel (o m : ℕ) : xq o m ^ o * yq o m ^ m = 1 := by
  apply Units.ext
  have : Ideal.Quotient.mk (closureIdeal o m) (1 - ((Xl ^ o * Yl ^ m : Lamˣ) : Lam)) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
  rw [map_sub, map_one, sub_eq_zero, Units.val_mul, map_mul, Units.val_pow_eq_pow_val,
    Units.val_pow_eq_pow_val, map_pow, map_pow] at this
  simp only [xq, yq, Units.val_mul, Units.val_pow_eq_pow_val, Units.coe_map,
    RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, Units.val_one]
  exact this.symm

/-- The inverse map `ℤ[t^{±1}] → Λ/(1 - X^o Y^m)`, `t^{-m} ↦ X`, `t^{o} ↦ Y`. -/
noncomputable def reparamBwd {o m : ℕ} (hom : Nat.Coprime o m) :
    ℤ[T;T⁻¹] →+* Lam ⧸ closureIdeal o m :=
  Classical.choose (reparam_universal (K := Lam ⧸ closureIdeal o m) hom (xq o m) (yq o m)
    (xq_yq_rel o m)).exists

/-- `reparamBwd` sends `t^{-m} ↦ X`, `t^{o} ↦ Y`. -/
lemma reparamBwd_spec {o m : ℕ} (hom : Nat.Coprime o m) :
    reparamBwd hom (T (-(m : ℤ))) = xq o m ∧ reparamBwd hom (T o) = yq o m := by
  have h := Classical.choose_spec (reparam_universal (K := Lam ⧸ closureIdeal o m) hom (xq o m)
    (yq o m) (xq_yq_rel o m)).exists
  exact h

lemma reparamFwd_X (o m : ℕ) : reparamFwd o m (Ideal.Quotient.mk _ Xl) = T (-(m : ℤ)) := by
  simp [reparamFwd]

lemma reparamFwd_Y (o m : ℕ) : reparamFwd o m (Ideal.Quotient.mk _ Yl) = T o := by
  simp [reparamFwd]

/-- **Prop. 1.9, coprime case.** For `gcd(o, m) = 1`, the reduction map is a ring isomorphism
`Λ/(1 - X^o Y^m) ≃ ℤ[t^{±1}]` with `X ↦ t^{-m}`, `Y ↦ t^{o}`. -/
noncomputable def reparamIso {o m : ℕ} (hom : Nat.Coprime o m) :
    (Lam ⧸ closureIdeal o m) ≃+* ℤ[T;T⁻¹] :=
  RingEquiv.ofRingHom (reparamFwd o m) (reparamBwd hom)
    (by
      obtain ⟨_, _, huniq⟩ := reparam_universal hom _ _ (reparam_kills o m)
      have h1 : ((reparamFwd o m).comp (reparamBwd hom)) (T (-(m : ℤ))) = T (-(m : ℤ)) := by
        rw [RingHom.comp_apply, (reparamBwd_spec hom).1]; exact reparamFwd_X o m
      have h2 : ((reparamFwd o m).comp (reparamBwd hom)) (T o) = T o := by
        rw [RingHom.comp_apply, (reparamBwd_spec hom).2]; exact reparamFwd_Y o m
      rw [huniq _ ⟨h1, h2⟩, huniq (RingHom.id _) ⟨rfl, rfl⟩])
    (by
      refine Ideal.Quotient.ringHom_ext (lam_ringHom_ext (K := Lam ⧸ closureIdeal o m) ?_ ?_)
      · simp only [RingHom.comp_apply, RingHom.id_apply]
        rw [reparamFwd_X, (reparamBwd_spec hom).1]; rfl
      · simp only [RingHom.comp_apply, RingHom.id_apply]
        rw [reparamFwd_Y, (reparamBwd_spec hom).2]; rfl)

lemma reparamIso_apply {o m : ℕ} (hom : Nat.Coprime o m) (a : Lam ⧸ closureIdeal o m) :
    reparamIso hom a = reparamFwd o m a := rfl

@[simp] lemma reparamIso_X {o m : ℕ} (hom : Nat.Coprime o m) :
    reparamIso hom (Ideal.Quotient.mk _ Xl) = T (-(m : ℤ)) := reparamFwd_X o m

@[simp] lemma reparamIso_Y {o m : ℕ} (hom : Nat.Coprime o m) :
    reparamIso hom (Ideal.Quotient.mk _ Yl) = T o := reparamFwd_Y o m

/-- `S` commutes with ring homomorphisms (naturality in the coefficients). -/
lemma map_foxSP {R R' : Type*} [CommSemiring R] [CommSemiring R'] (f : R →+* R') (x y : R)
    (l : List Letter) : f (foxSP x y l) = foxSP (f x) (f y) l := by
  induction l with
  | nil => simp
  | cons a l ih => cases a <;> simp [ih]

/-- At `X = Y = 1`, `S(w)` counts the letters `u`: `S(w)(1,1) = o`. -/
lemma foxSP_one_one {R : Type*} [CommSemiring R] (l : List Letter) :
    foxSP (1 : R) 1 l = l.count u := by
  induction l with
  | nil => simp
  | cons a l ih =>
    cases a
    · simp [ih]; ring
    · simp [ih]

/-- The class of `S(w)` in `Λ/(1 - χ(w))` is carried by `reparamIso` to the reduced cocycle. -/
theorem reparamIso_foxS (l : List Letter) (hom : Nat.Coprime (l.count u) (l.count v)) :
    reparamIso hom (Ideal.Quotient.mk _ (foxS Xl Yl (pos l))) = redS ℤ l := by
  rw [reparamIso_apply, reparamFwd, Ideal.Quotient.lift_mk, foxS_pos, map_foxSP, liftLam_X,
    liftLam_Y, redS_eq]
  rfl

/-- The closure ideal of a word of type `(E, o)` is `(1 - X^o Y^{E-o}) = (1 - χ(w))`. -/
theorem closureIdeal_eq (l : List Letter) :
    closureIdeal (l.count u) (l.count v) = Ideal.span {1 - (chiU Xl Yl (pos l) : Lam)} := by
  rw [closureIdeal, chiU_pos, mono_eq, Units.val_mul, Units.val_pow_eq_pow_val,
    Units.val_pow_eq_pow_val]

/-! ## Theorem 3.3, algebraic part: `g_o ∣ P_w` and `R_w = gcd(S, T)` over `ℚ[t^{±1}]` -/

/-- `g_n = 1 + t + ⋯ + t^{n-1}` in `ℚ[t^{±1}]`. -/
noncomputable def g (n : ℕ) : ℚ[T;T⁻¹] := toLaurent (∑ i ∈ Finset.range n, (X : ℚ[X]) ^ i)

/-- `t^n - 1 = (t - 1) g_n`. -/
lemma T_sub_one (n : ℕ) : (T n : ℚ[T;T⁻¹]) - 1 = (T 1 - 1) * g n := by
  rw [g, ← toLaurent_X, ← map_one toLaurent, ← map_sub, ← map_mul, mul_comm, geom_sum_mul,
    map_sub, map_pow, toLaurent_X, T_pow, map_one, mul_one]

/-- For coprime `o, m > 0`, `g_o` and `g_m` are coprime in `ℚ[t^{±1}]` (they are products of
cyclotomic polynomials `Φ_d` over disjoint sets of indices `d > 1`). -/
lemma g_isCoprime {o m : ℕ} (ho : 0 < o) (hm : 0 < m) (h : Nat.Coprime o m) :
    IsCoprime (g o) (g m) := by
  unfold g
  rw [← prod_cyclotomic_eq_geom_sum ho, ← prod_cyclotomic_eq_geom_sum hm]
  refine IsCoprime.map (f := (toLaurent : ℚ[X] →+* ℚ[T;T⁻¹])) ?_
  refine IsCoprime.prod_left fun i hi => IsCoprime.prod_right fun j hj => ?_
  refine cyclotomic.isCoprime_rat fun hij => ?_
  subst hij
  simp only [Finset.mem_erase, Nat.mem_divisors] at hi hj
  have := Nat.dvd_gcd hi.2.1 hj.2.1
  rw [h.gcd_eq_one] at this
  exact hi.1 (Nat.dvd_one.mp this)

/-- `g_n ≠ 0` for `n > 0` (it is `n` at `t = 1`). -/
lemma g_ne_zero {n : ℕ} (hn : 0 < n) : g n ≠ 0 := by
  rw [g, Ne, toLaurent_eq_zero]
  intro h0
  have := congrArg (eval 1) h0
  simp at this
  omega

/-- `t - 1 ≠ 0` (evaluate at `t = 2`). -/
lemma T_one_sub_one_ne_zero : (T 1 : ℚ[T;T⁻¹]) - 1 ≠ 0 := by
  intro h0
  have := congrArg (LaurentPolynomial.eval₂ (RingHom.id ℚ) (Units.mk0 (2 : ℚ) two_ne_zero)) h0
  norm_num at this

/-- The Crowell–Fox formula after the closure substitution:
`(t^{-m} - 1) S̄ + (t^{o} - 1) T̄ = 0`. -/
theorem crowellFox_red (l : List Letter) :
    ((T (-(l.count v : ℤ)) : ℚ[T;T⁻¹]) - 1) * redS ℚ l + (T (l.count u) - 1) * redT ℚ l = 0 := by
  have := crowellFox (tU ℚ (-(l.count v : ℤ))) (tU ℚ (l.count u)) (pos l)
  rw [chiU_red, sub_self] at this
  simpa [redS, redT] using this

/-- **Cor. 2.2 / Thm. 3.3 (algebraic part).** For a positive word of coprime type `(E, o)` with
`o, m = E - o > 0`, over `ℚ[t^{±1}]`: the full cyclotomic factor `g_o` divides the reduced
cocycle, `S̄ = g_o R`, the companion is `T̄ = t^{-m} g_m R`, and `R` is a gcd of `S̄` and `T̄`
(every common divisor of `S̄, T̄` divides `R`). Moreover `R(1) = 1`. -/
theorem core_gcd (l : List Letter) (ho : 0 < l.count u) (hm : 0 < l.count v)
    (hcop : Nat.Coprime (l.count u) (l.count v)) :
    ∃ R : ℚ[T;T⁻¹], redS ℚ l = g (l.count u) * R ∧
      redT ℚ l = T (-(l.count v : ℤ)) * g (l.count v) * R ∧
      (∀ D, D ∣ redS ℚ l ∧ D ∣ redT ℚ l ↔ D ∣ R) ∧
      LaurentPolynomial.eval₂ (RingHom.id ℚ) 1 R = 1 := by
  set o := l.count u
  set m := l.count v
  have hTm : (T (-(m : ℤ)) : ℚ[T;T⁻¹]) - 1 = -T (-(m : ℤ)) * ((T 1 - 1) * g m) := by
    have hTT : (T (-(m : ℤ)) : ℚ[T;T⁻¹]) * T m = 1 := by rw [← T_add]; simp [T_zero]
    rw [← T_sub_one]
    linear_combination hTT
  have hcf := crowellFox_red l
  rw [hTm, T_sub_one] at hcf
  have key : g o * redT ℚ l = T (-(m : ℤ)) * g m * redS ℚ l := by
    have h' : (T 1 - 1) * (g o * redT ℚ l - T (-(m : ℤ)) * g m * redS ℚ l) = 0 := by
      linear_combination hcf
    have := (mul_eq_zero.mp h').resolve_left T_one_sub_one_ne_zero
    linear_combination this
  have hcopg := g_isCoprime ho hm hcop
  have hdvd : g o ∣ redS ℚ l := by
    have h1 : g o ∣ g m * (T (-(m : ℤ)) * redS ℚ l) := ⟨redT ℚ l, by linear_combination -key⟩
    obtain ⟨c, hc⟩ := hcopg.dvd_of_dvd_mul_left h1
    refine ⟨T m * c, ?_⟩
    have hTT : (T (m : ℤ) : ℚ[T;T⁻¹]) * T (-(m : ℤ)) = 1 := by rw [← T_add]; simp [T_zero]
    linear_combination T (m : ℤ) * hc - redS ℚ l * hTT
  obtain ⟨R, hR⟩ := hdvd
  have hT : redT ℚ l = T (-(m : ℤ)) * g m * R := by
    apply mul_left_cancel₀ (g_ne_zero ho)
    rw [key, hR]; ring
  refine ⟨R, hR, hT, fun D => ⟨fun ⟨hS, hT'⟩ => ?_, fun hD => ⟨?_, ?_⟩⟩, ?_⟩
  · obtain ⟨α, β, hαβ⟩ := hcopg
    have hR' : R = α * redS ℚ l + β * T (m : ℤ) * redT ℚ l := by
      have hTT : (T (m : ℤ) : ℚ[T;T⁻¹]) * T (-(m : ℤ)) = 1 := by rw [← T_add]; simp [T_zero]
      rw [hR, hT]
      linear_combination (-R) * hαβ - (β * g m * R) * hTT
    rw [hR']
    exact dvd_add (dvd_mul_of_dvd_right hS _) (dvd_mul_of_dvd_right hT' _)
  · rw [hR]; exact dvd_mul_of_dvd_right hD _
  · rw [hT]; exact dvd_mul_of_dvd_right hD _
  · -- normalisation `R(1) = 1`: evaluate `S̄ = g_o R` at `t = 1`
    have h1 := congrArg (LaurentPolynomial.eval₂ (RingHom.id ℚ) 1) hR
    rw [redS_eq, map_foxSP, map_mul, g, eval₂_toLaurent] at h1
    simp only [eval₂_T, one_zpow, Units.val_one, foxSP_one_one, Polynomial.eval₂_finsetSum,
      Polynomial.eval₂_X_pow, one_pow, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, mul_one] at h1
    have ho' : (o : ℚ) ≠ 0 := by exact_mod_cast ho.ne'
    exact (mul_eq_left₀ ho').mp h1.symm

/-! ## §3: the cohomological statement (not formalized) -/

/-- The one-relator group `G_w = ⟨u, v | w⟩`. -/
abbrev Gw (l : List Letter) : Type := PresentedGroup {pos l}

/-- The character `χ` descends to `G_w → ℚ[t^{±1}]ˣ` (`u ↦ t^{-m}`, `v ↦ t^{o}`). -/
noncomputable def chiBar (l : List Letter) : Gw l →* (ℚ[T;T⁻¹])ˣ :=
  PresentedGroup.toGroup (f := gen (tU ℚ (-(l.count v : ℤ))) (tU ℚ (l.count u))) (by
    rintro r rfl
    exact Units.ext (by simpa [chiU] using chiU_red ℚ l))

/-- The `G_w`-module `M = ℚ[t^{±1}]`, `G_w` acting by multiplication through `χ̄`. -/
noncomputable def alexRep (l : List Letter) : Representation ℚ (Gw l) ℚ[T;T⁻¹] :=
  (Algebra.lmul ℚ ℚ[T;T⁻¹]).toMonoidHom.comp ((Units.coeHom _).comp (chiBar l))

/-- **Thm. 3.3 (cohomological part), stated only.** `ℚ ⊗ H²(G_w; M) ≅ ℚ[t^{±1}]/(R_w)`, here as
`ℚ`-vector spaces with rational coefficients `M = ℚ[t^{±1}]`, for the core `R_w` of `core_gcd`.
The note's proof needs Lyndon's asphericity theorem for one-relator presentations (so that the
presentation complex computes `H²(G_w; -)` as `M/(S(w), T(w))`), which is not in Mathlib. -/
def AlexanderClaim (l : List Letter) : Prop :=
  ∀ R : ℚ[T;T⁻¹], redS ℚ l = g (l.count u) * R →
    Nonempty (groupCohomology (Rep.of (alexRep l)) 2 ≃ₗ[ℚ] (ℚ[T;T⁻¹] ⧸ Ideal.span {R}))

end Syracuse.PolynomialRoot
