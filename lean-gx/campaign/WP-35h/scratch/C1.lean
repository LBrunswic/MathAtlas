import GXScaffold.Branched.GaloisExamples

noncomputable section

open Set Filter Topology Function unitInterval

namespace GX

attribute [local instance] Classical.propDecidable
attribute [local instance] absGal_locPath
attribute [local instance] absGal_simplyConnected

set_option linter.unusedSectionVars false

section CantorFibre

variable (y₀ : (fibSᶜ : Set ℂ))

/-- The point `aₙ = 1/(n+1)` of `S`. -/
def cantPt (n : ℕ) : ℂ := ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)

theorem cantPt_mem (n : ℕ) : cantPt n ∈ fibS := fibPt_mem n

/-- `p - aₙ`, into `ℂ ∖ {0}`. -/
def cantSubC (n : ℕ) : C(AbsU y₀, CStar) :=
  (subFib _ (cantPt_mem n)).comp ⟨UniversalCover.proj _ y₀, UniversalCover.continuous_proj⟩

theorem cant_exists_ℓ (n : ℕ) :
    ∃ ℓ : C(AbsU y₀, ℂ), ∀ c, Complex.exp (ℓ c) = absP y₀ c - cantPt n := by
  obtain ⟨ℓ, ⟨-, hℓ⟩, -⟩ := isCoveringMap_cExp.existsUnique_continuousMap_lifts (cantSubC y₀ n)
    (UniversalCover.base y₀) (Complex.log (cantSubC y₀ n (UniversalCover.base y₀)))
    (Subtype.ext (Complex.exp_log (cantSubC y₀ n _).2))
  exact ⟨ℓ, fun c => congrArg Subtype.val (congrFun hℓ c)⟩

/-- A continuous logarithm of `p - aₙ` on `\widetilde{ℂ∖S}`. -/
def cantℓ (n : ℕ) : C(AbsU y₀, ℂ) := (cant_exists_ℓ y₀ n).choose

theorem cantℓ_spec (n : ℕ) (c : AbsU y₀) : Complex.exp (cantℓ y₀ n c) = absP y₀ c - cantPt n :=
  (cant_exists_ℓ y₀ n).choose_spec c

/-- The continuous square root `sₙ = exp(ℓₙ/2)` of `p - aₙ`. -/
def cantSq (n : ℕ) (c : AbsU y₀) : ℂ := Complex.exp (cantℓ y₀ n c / 2)

theorem continuous_cantSq (n : ℕ) : Continuous (cantSq y₀ n) := by
  unfold cantSq; fun_prop

theorem cantSq_sq (n : ℕ) (c : AbsU y₀) : cantSq y₀ n c ^ 2 = absP y₀ c - cantPt n := by
  rw [cantSq, sq, ← Complex.exp_add, add_halves, cantℓ_spec]

theorem cantSq_ne_zero (n : ℕ) (c : AbsU y₀) : cantSq y₀ n c ≠ 0 := Complex.exp_ne_zero _

section Deck

variable {y₀} (φ : AbsU y₀ ≃ₜ AbsU y₀) (hφ : ∀ c, absP y₀ (φ c) = absP y₀ c)

/-- The sign `±1` by which a deck transformation acts on `sₙ`. -/
def cantSign (n : ℕ) : ℂ :=
  Complex.exp ((cantℓ y₀ n (φ (UniversalCover.base y₀)) - cantℓ y₀ n (UniversalCover.base y₀)) / 2)

include hφ in
theorem cantSq_deck (n : ℕ) (c : AbsU y₀) : cantSq y₀ n (φ c) = cantSign φ n * cantSq y₀ n c := by
  have := absGal_expLift_eq (cantℓ y₀ n).continuous ((cantℓ y₀ n).continuous.comp φ.continuous)
    (fun a => by simp only [comp_apply, cantℓ_spec, hφ]) (UniversalCover.base y₀) c
  simp only [comp_apply] at this
  rw [cantSq, this, add_div, Complex.exp_add, cantSign, cantSq, mul_comm]

end Deck

/-- `εₙ(g)`: the sign by which the deck transformation of `g ∈ π₁(ℂ ∖ S)` acts on `sₙ`. -/
def cantEps (n : ℕ) (g : AbsGamma y₀) : ℂ := cantSign (UniversalCover.deckHom g).1 n

theorem cantSq_deckHom (n : ℕ) (g : AbsGamma y₀) (c : AbsU y₀) :
    cantSq y₀ n ((UniversalCover.deckHom g).1 c) = cantEps y₀ n g * cantSq y₀ n c :=
  cantSq_deck _ (absP_deckHom y₀ g) n c

theorem cantEps_mul (n : ℕ) (a b : AbsGamma y₀) :
    cantEps y₀ n (a * b) = cantEps y₀ n a * cantEps y₀ n b := by
  have h := cantSq_deckHom y₀ n (a * b) (UniversalCover.base y₀)
  rw [map_mul] at h
  have h2 : cantSq y₀ n ((UniversalCover.deckHom a).1 ((UniversalCover.deckHom b).1
      (UniversalCover.base y₀))) = cantEps y₀ n a * (cantEps y₀ n b *
        cantSq y₀ n (UniversalCover.base y₀)) := by
    rw [cantSq_deckHom, cantSq_deckHom]
  have h3 : cantSq y₀ n (((UniversalCover.deckHom a) * (UniversalCover.deckHom b)).1
      (UniversalCover.base y₀)) = cantSq y₀ n ((UniversalCover.deckHom a).1
        ((UniversalCover.deckHom b).1 (UniversalCover.base y₀))) := rfl
  rw [h3, h2] at h
  have hne := cantSq_ne_zero y₀ n (UniversalCover.base y₀)
  have : (cantEps y₀ n (a * b) - cantEps y₀ n a * cantEps y₀ n b) *
      cantSq y₀ n (UniversalCover.base y₀) = 0 := by linear_combination -h
  exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hne)

theorem cantEps_one (n : ℕ) : cantEps y₀ n 1 = 1 := by
  have h := cantSq_deckHom y₀ n 1 (UniversalCover.base y₀)
  rw [map_one] at h
  change cantSq y₀ n (UniversalCover.base y₀) = _ at h
  have hne := cantSq_ne_zero y₀ n (UniversalCover.base y₀)
  have : (cantEps y₀ n 1 - 1) * cantSq y₀ n (UniversalCover.base y₀) = 0 := by
    linear_combination -h
  exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hne)

theorem cantEps_sq (n : ℕ) (g : AbsGamma y₀) : cantEps y₀ n g ^ 2 = 1 := by
  have h := cantSq_deckHom y₀ n g (UniversalCover.base y₀)
  have h2 := congrArg (· ^ 2) h
  simp only [mul_pow, cantSq_sq, absP_deckHom] at h2
  have hne : absP y₀ (UniversalCover.base y₀) - cantPt n ≠ 0 :=
    sub_ne_zero.2 fun e => absP_not_mem y₀ _ (e ▸ cantPt_mem n)
  have : (cantEps y₀ n g ^ 2 - 1) * (absP y₀ (UniversalCover.base y₀) - cantPt n) = 0 := by
    linear_combination -h2
  exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hne)

theorem cantEps_eq (n : ℕ) (g : AbsGamma y₀) : cantEps y₀ n g = 1 ∨ cantEps y₀ n g = -1 := by
  have := cantEps_sq y₀ n g
  rw [sq] at this
  exact mul_self_eq_one_iff.1 this

theorem cantEps_inv (n : ℕ) (g : AbsGamma y₀) : cantEps y₀ n g⁻¹ = cantEps y₀ n g := by
  have h := cantEps_mul y₀ n g g⁻¹
  rw [mul_inv_cancel, cantEps_one] at h
  rcases cantEps_eq y₀ n g with e | e <;> rw [e] at h ⊢
  · simpa using h.symm
  · have : cantEps y₀ n g⁻¹ = -1 := by linear_combination h
    exact this

/-- **`Γ₂'`, the corrected subgroup of `ex:consider_denote_absolute_galois` (DEC-69)**: the kernel
of the mod-2 windings around the points `1/n` (`GX.mem_cantGamma_iff`), i.e. the deck
transformations fixing every square root `sₙ`. -/
def cantGamma : Subgroup (AbsGamma y₀) where
  carrier := {g | ∀ n, cantEps y₀ n g = 1}
  one_mem' := fun n => cantEps_one y₀ n
  mul_mem' := by
    intro a b ha hb n
    show cantEps y₀ n (a * b) = 1
    rw [cantEps_mul, ha n, hb n, one_mul]
  inv_mem' := by
    intro a ha n
    show cantEps y₀ n a⁻¹ = 1
    rw [cantEps_inv]; exact ha n

theorem mem_cantGamma {g : AbsGamma y₀} : g ∈ cantGamma y₀ ↔ ∀ n, cantEps y₀ n g = 1 := Iff.rfl

/-- Along the canonical lift `L` of a loop `δ` of `ℂ ∖ S`, `sₙ` changes by `(-1)^w`, `w` the
winding number of `δ` around `aₙ`. -/
theorem cantSq_liftFrom_loop {b : (fibSᶜ : Set ℂ)} (c : Path.Homotopic.Quotient y₀ b)
    (δ : Path b b) (n : ℕ) :
    cantSq y₀ n (UniversalCover.liftFrom c δ 1) =
      (-1 : ℂ) ^ cWinding (δ.map (subFib _ (cantPt_mem n)).continuous) *
        cantSq y₀ n (UniversalCover.liftFrom c δ 0) := by
  set L := UniversalCover.liftFrom c δ
  have hL : ∀ t, Complex.exp ((cantℓ y₀ n).comp ⟨L, L.continuous⟩ t) =
      (δ.map (subFib _ (cantPt_mem n)).continuous) t := fun t => by
    show Complex.exp (cantℓ y₀ n (L t)) = ((δ t : ℂ) - cantPt n)
    rw [cantℓ_spec]; rfl
  have e := cWinding_spec _ hL
  simp only [ContinuousMap.coe_comp, ContinuousMap.coe_mk, comp_apply] at e
  rw [cantSq, cantSq, e, add_div, Complex.exp_add, mul_comm]
  congr 1
  rw [show (cWinding (δ.map (subFib _ (cantPt_mem n)).continuous) : ℂ) * (2 * Real.pi * Complex.I) / 2
      = (cWinding (δ.map (subFib _ (cantPt_mem n)).continuous) : ℂ) * (Real.pi * Complex.I) by ring,
    Complex.exp_int_mul, Complex.exp_pi_mul_I]

theorem neg_one_zpow_neg' (w : ℤ) : (-1 : ℂ) ^ (-w) = (-1 : ℂ) ^ w := by
  rw [zpow_neg]
  rcases Int.even_or_odd w with h | h
  · rw [h.neg_one_zpow, inv_one]
  · rw [h.neg_one_zpow]; norm_num

/-- `εₙ([γ]) = (-1)^{w(γ, aₙ)}`. -/
theorem cantEps_fromPath (n : ℕ) (γ : Path y₀ y₀) :
    cantEps y₀ n (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ)) =
      (-1 : ℂ) ^ windAt y₀ _ (cantPt_mem n) γ := by
  have h := cantSq_deckHom y₀ n (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ))
    (UniversalCover.base y₀)
  rw [absGal_deckHom_base, cantSq_liftFrom_loop, absGal_cWinding_symm] at h
  have h0 : UniversalCover.liftFrom (Path.Homotopic.Quotient.refl y₀) γ.symm 0 =
      UniversalCover.base y₀ := (UniversalCover.liftFrom _ γ.symm).source
  rw [h0, neg_one_zpow_neg'] at h
  have hne := cantSq_ne_zero y₀ n (UniversalCover.base y₀)
  have : ((-1 : ℂ) ^ windAt y₀ _ (cantPt_mem n) γ -
      cantEps y₀ n (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ))) *
      cantSq y₀ n (UniversalCover.base y₀) = 0 := by
    unfold windAt; linear_combination h
  exact (sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hne)).symm

theorem neg_one_zpow_eq_one_iff (w : ℤ) : (-1 : ℂ) ^ w = 1 ↔ Even w := by
  rcases Int.even_or_odd w with h | h
  · simp [h.neg_one_zpow, h]
  · rw [h.neg_one_zpow]
    simp only [Int.not_even_iff_odd.2 h, iff_false]
    norm_num

/-- **`Γ₂'` is the kernel of the mod-2 windings**: a loop class lies in `Γ₂'` iff the loop winds
an even number of times around every point `1/n` of `S`. -/
theorem mem_cantGamma_iff (γ : Path y₀ y₀) :
    FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ) ∈ cantGamma y₀ ↔
      ∀ n, Even (windAt y₀ _ (cantPt_mem n) γ) := by
  simp only [mem_cantGamma, cantEps_fromPath, neg_one_zpow_eq_one_iff]


/-! #### The signs near `0` -/

/-- A branch `rₙ(z) = i·√(aₙ - z)` of the square root of `z - aₙ`, continuous on `Re z < aₙ`. -/
def cantRoot (n : ℕ) (z : ℂ) : ℂ := Complex.I * Complex.exp (Complex.log (cantPt n - z) / 2)

theorem cantPt_re (n : ℕ) : (cantPt n).re = 1 / ((n : ℝ) + 1) := by rw [cantPt, Complex.ofReal_re]

theorem cantRoot_sq {n : ℕ} {z : ℂ} (hz : cantPt n - z ≠ 0) : cantRoot n z ^ 2 = z - cantPt n := by
  rw [cantRoot, mul_pow, Complex.I_sq, sq (Complex.exp _), ← Complex.exp_add, add_halves,
    Complex.exp_log hz]
  ring

theorem cant_slit {n : ℕ} {z : ℂ} (hz : z.re < 1 / ((n : ℝ) + 1)) :
    cantPt n - z ∈ Complex.slitPlane :=
  Complex.mem_slitPlane_iff.2 (Or.inl (by rw [Complex.sub_re, cantPt_re]; linarith))

theorem continuousAt_cantRoot {n : ℕ} {z : ℂ} (hz : z.re < 1 / ((n : ℝ) + 1)) :
    ContinuousAt (cantRoot n) z := by
  unfold cantRoot
  exact continuousAt_const.mul
    (((continuousAt_const.sub continuousAt_id).clog (cant_slit hz)).div_const 2).cexp

/-- The sign `σₙ = sₙ / rₙ(p)`, equal to `±1` over `Re z < aₙ`. -/
def cantSigma (n : ℕ) (c : AbsU y₀) : ℂ := cantSq y₀ n c / cantRoot n (absP y₀ c)

theorem cantSigma_eq {n : ℕ} {c : AbsU y₀} (hc : (absP y₀ c).re < 1 / ((n : ℝ) + 1)) :
    cantSigma y₀ n c = 1 ∨ cantSigma y₀ n c = -1 := by
  have hne : cantPt n - absP y₀ c ≠ 0 := Complex.slitPlane_ne_zero (cant_slit hc)
  have hne' : absP y₀ c - cantPt n ≠ 0 := fun h => hne (by linear_combination -h)
  have hr : cantRoot n (absP y₀ c) ≠ 0 := fun h => by
    have := cantRoot_sq hne; rw [h] at this; exact hne' (by rw [← this]; ring)
  have : cantSigma y₀ n c ^ 2 = 1 := by
    rw [cantSigma, div_pow, cantSq_sq, cantRoot_sq hne, div_self hne']
  rw [sq] at this
  exact mul_self_eq_one_iff.1 this

theorem cantSigma_deckHom (n : ℕ) (g : AbsGamma y₀) (c : AbsU y₀) :
    cantSigma y₀ n ((UniversalCover.deckHom g).1 c) = cantEps y₀ n g * cantSigma y₀ n c := by
  rw [cantSigma, cantSigma, cantSq_deckHom, absP_deckHom, mul_div_assoc]

theorem cantSigma_eventually {n : ℕ} {c₀ : AbsU y₀} (hc : (absP y₀ c₀).re < 1 / ((n : ℝ) + 1)) :
    ∀ᶠ c in 𝓝 c₀, cantSigma y₀ n c = cantSigma y₀ n c₀ := by
  have hne : cantPt n - absP y₀ c₀ ≠ 0 := Complex.slitPlane_ne_zero (cant_slit hc)
  have hne' : absP y₀ c₀ - cantPt n ≠ 0 := fun h => hne (by linear_combination -h)
  have hr : cantRoot n (absP y₀ c₀) ≠ 0 := fun h => by
    have := cantRoot_sq hne; rw [h] at this; exact hne' (by rw [← this]; ring)
  have hcont : ContinuousAt (cantSigma y₀ n) c₀ :=
    (continuous_cantSq y₀ n).continuousAt.div
      ((continuousAt_cantRoot hc).comp (continuous_absP y₀).continuousAt) hr
  have hV : ∀ᶠ c in 𝓝 c₀, (absP y₀ c).re < 1 / ((n : ℝ) + 1) :=
    ((Complex.continuous_re.comp (continuous_absP y₀)).tendsto c₀).eventually (eventually_lt_nhds hc)
  filter_upwards [hV, hcont.eventually (Metric.ball_mem_nhds _ one_pos)] with c hc' hd
  rcases cantSigma_eq y₀ hc with h0 | h0 <;> rcases cantSigma_eq y₀ hc' with h1 | h1 <;>
    simp only [h0, h1] at hd ⊢ <;> norm_num [Complex.dist_eq] at hd

/-- The bit `σₙ = 1`. -/
def cantBit (n : ℕ) (c : AbsU y₀) : Bool := decide (cantSigma y₀ n c = 1)

theorem cant_re_lt_of_mem_fibD {n k : ℕ} (hnk : n < k) {z : ℂ} (hz : z ∈ fibD k) :
    z.re < 1 / ((n : ℝ) + 1) := by
  rw [fibD, Metric.mem_ball, dist_zero_right] at hz
  have h1 : z.re ≤ ‖z‖ := Complex.re_le_norm z
  have h2 : 1 / ((k : ℝ) + 1 / 2) ≤ 1 / ((n : ℝ) + 1) := by
    have : (n : ℝ) + 1 ≤ k := by exact_mod_cast hnk
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  linarith

theorem cant_isOpen_level {n k : ℕ} (hnk : n < k) (b : Bool) :
    IsOpen {c : AbsU y₀ | absP y₀ c ∈ fibD k ∧ cantBit y₀ n c = b} := by
  rw [isOpen_iff_mem_nhds]
  rintro c₀ ⟨hc₀, hb⟩
  filter_upwards [cantSigma_eventually y₀ (cant_re_lt_of_mem_fibD hnk hc₀),
    (continuous_absP y₀).continuousAt.preimage_mem_nhds (Metric.isOpen_ball.mem_nhds hc₀)]
    with c hc hD
  exact ⟨hD, by rw [← hb, cantBit, cantBit, hc]⟩

/-- A `Bool`-valued function with open level sets over an open set is constant on its
preconnected subsets. -/
theorem cant_const_of_isOpen_level {Z : Type*} [TopologicalSpace Z] {A : Set Z} {f : Z → Bool}
    (h : ∀ b, IsOpen {x | x ∈ A ∧ f x = b}) {s : Set Z} (hs : IsPreconnected s) (hsA : s ⊆ A)
    {x y : Z} (hx : x ∈ s) (hy : y ∈ s) : f y = f x := by
  have := GX.IsPreconnected.subset_of_pairwise_disjoint (T := fun b => {x | x ∈ A ∧ f x = b}) h
    (fun i j hij => by
      rw [Function.onFun, Set.disjoint_left]
      rintro z ⟨-, hi⟩ ⟨-, hj⟩
      exact hij (hi.symm.trans hj)) hs (fun z hz => mem_iUnion.2 ⟨f z, hsA hz, rfl⟩)
    (j := f x) ⟨x, hx, hsA hx, rfl⟩
  exact (this hy).2

theorem cantBit_const {n k : ℕ} (hnk : n < k) {s : Set (AbsU y₀)} (hs : IsPreconnected s)
    (hsk : s ⊆ absP y₀ ⁻¹' fibD k) {x y : AbsU y₀} (hx : x ∈ s) (hy : y ∈ s) :
    cantBit y₀ n y = cantBit y₀ n x :=
  cant_const_of_isOpen_level (A := absP y₀ ⁻¹' fibD k) (fun b => cant_isOpen_level y₀ hnk b) hs hsk
    hx hy

theorem cantSigma_eq_of_bit {n : ℕ} {c c' : AbsU y₀} (hc : (absP y₀ c).re < 1 / ((n : ℝ) + 1))
    (hc' : (absP y₀ c').re < 1 / ((n : ℝ) + 1)) (h : cantBit y₀ n c' = cantBit y₀ n c) :
    cantSigma y₀ n c' = cantSigma y₀ n c := by
  unfold cantBit at h
  rcases cantSigma_eq y₀ hc with h0 | h0 <;> rcases cantSigma_eq y₀ hc' with h1 | h1 <;>
    simp only [h0, h1] at h ⊢ <;> norm_num at h

theorem cantSigma_const {n k : ℕ} (hnk : n < k) {s : Set (AbsU y₀)} (hs : IsPreconnected s)
    (hsk : s ⊆ absP y₀ ⁻¹' fibD k) {x y : AbsU y₀} (hx : x ∈ s) (hy : y ∈ s) :
    cantSigma y₀ n y = cantSigma y₀ n x :=
  cantSigma_eq_of_bit y₀ (cant_re_lt_of_mem_fibD hnk (hsk hx)) (cant_re_lt_of_mem_fibD hnk (hsk hy))
    (cantBit_const y₀ hnk hs hsk hx hy)

/-! #### Deck transformations, components, lifts -/

theorem cant_exists_deck {c c' : AbsU y₀} (h : c.pt = c'.pt) :
    ∃ g : AbsGamma y₀, (UniversalCover.deckHom g).1 c = c' := by
  obtain ⟨b, γ⟩ := c
  obtain ⟨b', γ'⟩ := c'
  simp only at h
  subst h
  refine ⟨(FundamentalGroup.fromPath (γ'.trans γ.symm))⁻¹, ?_⟩
  rw [UniversalCover.deckHom_apply, inv_inv]
  show (⟨b, (γ'.trans γ.symm).trans γ⟩ : AbsU y₀) = ⟨b, γ'⟩
  rw [Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.symm_trans,
    Path.Homotopic.Quotient.trans_refl]

theorem cant_deck_image_comp (g : AbsGamma y₀) {U : Set ℂ} {c : AbsU y₀} (hc : absP y₀ c ∈ U) :
    (UniversalCover.deckHom g).1 '' connectedComponentIn (absP y₀ ⁻¹' U) c =
      connectedComponentIn (absP y₀ ⁻¹' U) ((UniversalCover.deckHom g).1 c) := by
  rw [Homeomorph.image_connectedComponentIn _ (show c ∈ absP y₀ ⁻¹' U from hc)]
  congr 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    show absP y₀ ((UniversalCover.deckHom g).1 y) ∈ U
    rw [absP_deckHom]; exact hy
  · intro hx
    refine ⟨(UniversalCover.deckHom g).1.symm x, ?_, (UniversalCover.deckHom g).1.apply_symm_apply x⟩
    have := absP_deckHom y₀ g ((UniversalCover.deckHom g).1.symm x)
    rw [Homeomorph.apply_symm_apply] at this
    show absP y₀ _ ∈ U
    rw [← this]; exact hx

/-- `cpt k c`: the component of `c` in the preimage of `D_k`. -/
abbrev cantComp (k : ℕ) (c : AbsU y₀) : Set (AbsU y₀) :=
  connectedComponentIn (absP y₀ ⁻¹' fibD k) c

theorem cant_mem_comp_of_deck {k : ℕ} {c : AbsU y₀} (hc : absP y₀ c ∈ fibD k) {a : AbsGamma y₀}
    (ha : (UniversalCover.deckHom a).1 c ∈ cantComp y₀ k c) {x : AbsU y₀} (hx : x ∈ cantComp y₀ k c) :
    (UniversalCover.deckHom a).1 x ∈ cantComp y₀ k c := by
  have h1 : (UniversalCover.deckHom a).1 x ∈ (UniversalCover.deckHom a).1 '' cantComp y₀ k c :=
    mem_image_of_mem _ hx
  rw [cant_deck_image_comp y₀ a hc, ← connectedComponentIn_eq ha] at h1
  exact h1

theorem cant_stab_mul {k : ℕ} {c : AbsU y₀} (hc : absP y₀ c ∈ fibD k) {a b : AbsGamma y₀}
    (ha : (UniversalCover.deckHom a).1 c ∈ cantComp y₀ k c)
    (hb : (UniversalCover.deckHom b).1 c ∈ cantComp y₀ k c) :
    (UniversalCover.deckHom (a * b)).1 c ∈ cantComp y₀ k c := by
  rw [map_mul]
  exact cant_mem_comp_of_deck y₀ hc ha hb

/-- Every point of `D_k ∖ S` is reached from `c` inside its component. -/
theorem cant_reach {k : ℕ} (c : AbsU y₀) (hc : absP y₀ c ∈ fibD k) (b : (fibSᶜ : Set ℂ))
    (hb : (b : ℂ) ∈ fibD k) : ∃ c₀ ∈ cantComp y₀ k c, c₀.pt = b := by
  have hj := (isPathConnected_fibD_diff k).joinedIn (absP y₀ c) ⟨hc, absP_not_mem y₀ c⟩ b ⟨hb, b.2⟩
  let δ : Path c.pt b :=
    { toFun := fun t => ⟨hj.somePath t, (hj.somePath_mem t).2⟩
      continuous_toFun := hj.somePath.continuous.subtype_mk _
      source' := Subtype.ext hj.somePath.source
      target' := Subtype.ext hj.somePath.target }
  let L := UniversalCover.liftFrom c.cls δ
  refine ⟨L 1, ?_, (UniversalCover.proj_liftFrom _ _ 1).trans δ.target⟩
  have hsub : range L ⊆ absP y₀ ⁻¹' fibD k := by
    rintro _ ⟨t, rfl⟩; exact (hj.somePath_mem t).1
  exact (isPreconnected_range L.continuous).subset_connectedComponentIn ⟨0, L.source⟩ hsub ⟨1, rfl⟩

/-- A loop in `D_k ∖ S` gives a deck transformation preserving the component of `c` and acting on
the `sₘ` by the parities of its windings. -/
theorem cant_loop_realize {k : ℕ} (c : AbsU y₀) (hc : absP y₀ c ∈ fibD k) {b : (fibSᶜ : Set ℂ)}
    (δ : Path b b) (hδ : ∀ t, ((δ t : (fibSᶜ : Set ℂ)) : ℂ) ∈ fibD k) :
    ∃ h : AbsGamma y₀, (∀ m, cantEps y₀ m h =
      (-1 : ℂ) ^ cWinding (δ.map (subFib _ (cantPt_mem m)).continuous)) ∧
      (UniversalCover.deckHom h).1 c ∈ cantComp y₀ k c := by
  obtain ⟨c₀, hc₀, hpt⟩ := cant_reach y₀ c hc b (by simpa using hδ 0)
  obtain ⟨b', cls⟩ := c₀
  simp only at hpt
  subst hpt
  set L := UniversalCover.liftFrom cls δ
  have hsub : range L ⊆ absP y₀ ⁻¹' fibD k := by
    rintro _ ⟨t, rfl⟩; exact hδ t
  have hrange : range L ⊆ cantComp y₀ k ⟨b', cls⟩ :=
    (isPreconnected_range L.continuous).subset_connectedComponentIn ⟨0, L.source⟩ hsub
  have hcc : cantComp y₀ k c = cantComp y₀ k ⟨b', cls⟩ := connectedComponentIn_eq hc₀
  obtain ⟨h, hh⟩ := cant_exists_deck y₀ (c := ⟨b', cls⟩) (c' := L 1)
    ((UniversalCover.proj_liftFrom _ _ 1).trans δ.target).symm
  refine ⟨h, fun m => ?_, ?_⟩
  · have e1 := cantSq_deckHom y₀ m h ⟨b', cls⟩
    rw [hh, cantSq_liftFrom_loop] at e1
    have e0 : L 0 = ⟨b', cls⟩ := L.source
    rw [e0] at e1
    have hne := cantSq_ne_zero y₀ m ⟨b', cls⟩
    have : ((-1 : ℂ) ^ cWinding (δ.map (subFib _ (cantPt_mem m)).continuous) - cantEps y₀ m h) *
        cantSq y₀ m ⟨b', cls⟩ = 0 := by linear_combination e1
    exact (sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hne)).symm
  · have hc0 : absP y₀ ⟨b', cls⟩ ∈ fibD k := hsub ⟨0, L.source⟩
    have h1 : (UniversalCover.deckHom h).1 ⟨b', cls⟩ ∈ cantComp y₀ k ⟨b', cls⟩ := by
      rw [hh]; exact hrange ⟨1, rfl⟩
    rw [hcc]
    exact cant_mem_comp_of_deck y₀ hc0 h1 (hcc ▸ mem_connectedComponentIn hc)

/-! #### Realising sign patterns by loops in `D_k` -/

/-- The sign patterns realised by deck transformations preserving the component of `c` over
`D_k`. -/
def CantReal (k : ℕ) (c : AbsU y₀) (τ : ℕ → ℂ) : Prop :=
  ∃ h : AbsGamma y₀, (∀ m, cantEps y₀ m h = τ m) ∧ (UniversalCover.deckHom h).1 c ∈ cantComp y₀ k c

theorem cantReal_one {k : ℕ} {c : AbsU y₀} (hc : absP y₀ c ∈ fibD k) : CantReal y₀ k c fun _ => 1 :=
  ⟨1, fun m => cantEps_one y₀ m, by rw [map_one]; exact mem_connectedComponentIn hc⟩

theorem cantReal_mul {k : ℕ} {c : AbsU y₀} (hc : absP y₀ c ∈ fibD k) {τ τ' : ℕ → ℂ}
    (h : CantReal y₀ k c τ) (h' : CantReal y₀ k c τ') : CantReal y₀ k c fun m => τ m * τ' m := by
  obtain ⟨a, ha, hac⟩ := h
  obtain ⟨b, hb, hbc⟩ := h'
  exact ⟨a * b, fun m => by rw [cantEps_mul, ha, hb], cant_stab_mul y₀ hc hac hbc⟩

theorem cantReal_congr {k : ℕ} {c : AbsU y₀} {τ τ' : ℕ → ℂ} (he : ∀ m, τ m = τ' m)
    (h : CantReal y₀ k c τ) : CantReal y₀ k c τ' := by
  obtain ⟨a, ha, hac⟩ := h
  exact ⟨a, fun m => (ha m).trans (he m), hac⟩

theorem cantPt_eq_absGalP_iff (m n : ℕ) : cantPt m = (absGalP n : ℂ) ↔ m = n := by
  rw [cantPt, Complex.ofReal_inj, absGalP]
  constructor
  · intro h
    have : (m : ℝ) + 1 = (n : ℝ) + 1 := by
      have h' := h
      field_simp at h'
      linarith
    exact_mod_cast (by linarith : (m : ℝ) = n)
  · rintro rfl; rfl

theorem cant_absGalCirc_mem {k n : ℕ} (hkn : k ≤ n) (t : I) : absGalCirc n t ∈ fibD k := by
  rw [fibD, Metric.mem_ball, dist_zero_right]
  have h1 : ‖absGalCirc n t‖ ≤ ‖absGalCirc n t - absGalP n‖ + ‖((absGalP n : ℝ) : ℂ)‖ := by
    calc ‖absGalCirc n t‖ = ‖(absGalCirc n t - absGalP n) + ((absGalP n : ℝ) : ℂ)‖ := by ring_nf
      _ ≤ _ := norm_add_le _ _
  rw [norm_absGalCirc_sub, Complex.norm_real, Real.norm_of_nonneg (by unfold absGalP; positivity)]
    at h1
  have h2 : absGalρ n + absGalP n < 1 / ((n : ℝ) + 1 / 2) := by
    unfold absGalρ absGalP
    rw [div_add_div _ _ (by positivity) (by positivity), div_lt_div_iff₀ (by positivity)
      (by positivity)]
    nlinarith
  have h3 : 1 / ((n : ℝ) + 1 / 2) ≤ 1 / ((k : ℝ) + 1 / 2) :=
    one_div_le_one_div_of_le (by positivity) (by have : (k : ℝ) ≤ n := (by exact_mod_cast hkn); linarith)
  linarith

/-- The flip of the single sign `n ≥ k` is realised (the small circle around `aₙ`). -/
theorem cantReal_flip {k : ℕ} {c : AbsU y₀} (hc : absP y₀ c ∈ fibD k) {n : ℕ} (hkn : k ≤ n) :
    CantReal y₀ k c fun m => if m = n then -1 else 1 := by
  obtain ⟨h, hh, hc'⟩ := cant_loop_realize y₀ c hc (absGalCircPath n)
    fun t => cant_absGalCirc_mem hkn t
  refine ⟨h, fun m => ?_, hc'⟩
  beta_reduce
  rw [hh, absGal_cWinding_circ]
  by_cases hm : m = n
  · rw [if_pos ((cantPt_eq_absGalP_iff m n).2 hm), if_pos hm]; norm_num
  · rw [if_neg (fun e => hm ((cantPt_eq_absGalP_iff m n).1 e)), if_neg hm]; norm_num

/-- The circle `t ↦ -R e^{2iπt}` around `0`. -/
def cantCirc (R : ℝ) (t : I) : ℂ := -(R : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (t : ℝ))

theorem cant_norm_exp (t : ℝ) : ‖Complex.exp (2 * Real.pi * Complex.I * t)‖ = 1 := by
  rw [show (2 * Real.pi * Complex.I * t : ℂ) = ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I by
    push_cast; ring, Complex.norm_exp_ofReal_mul_I]

theorem cant_norm_exp_neg (t : ℝ) : ‖Complex.exp (-(2 * Real.pi * Complex.I * t))‖ = 1 := by
  rw [show (-(2 * Real.pi * Complex.I * t) : ℂ) = ((-(2 * Real.pi * t) : ℝ) : ℂ) * Complex.I by
    push_cast; ring, Complex.norm_exp_ofReal_mul_I]

theorem norm_cantCirc {R : ℝ} (hR : 0 ≤ R) (t : I) : ‖cantCirc R t‖ = R := by
  rw [cantCirc, norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg hR, cant_norm_exp, mul_one]

theorem cantCirc_zero (R : ℝ) : cantCirc R 0 = -(R : ℂ) := by simp [cantCirc]

theorem cantCirc_one (R : ℝ) : cantCirc R 1 = -(R : ℂ) := by
  simp only [cantCirc, Set.Icc.coe_one, Complex.ofReal_one, mul_one, Complex.exp_two_pi_mul_I]

theorem cantCirc_not_mem {R : ℝ} (hR : 0 ≤ R) (hS : ∀ s ∈ fibS, ‖s‖ ≠ R) (t : I) :
    cantCirc R t ∉ fibS := fun h => hS _ h (norm_cantCirc hR t)

theorem cant_negR_not_mem {R : ℝ} (hR : 0 ≤ R) (hS : ∀ s ∈ fibS, ‖s‖ ≠ R) : -(R : ℂ) ∉ fibS :=
  cantCirc_zero R ▸ cantCirc_not_mem hR hS 0

/-- The circle as a loop of `ℂ ∖ S`. -/
def cantCircPath {R : ℝ} (hR : 0 ≤ R) (hS : ∀ s ∈ fibS, ‖s‖ ≠ R) :
    Path (⟨-(R : ℂ), cant_negR_not_mem hR hS⟩ : (fibSᶜ : Set ℂ)) ⟨-(R : ℂ), cant_negR_not_mem hR hS⟩ where
  toFun t := ⟨cantCirc R t, cantCirc_not_mem hR hS t⟩
  continuous_toFun := by refine Continuous.subtype_mk ?_ _; unfold cantCirc; fun_prop
  source' := Subtype.ext (cantCirc_zero R)
  target' := Subtype.ext (cantCirc_one R)

theorem cant_slit_of_norm {w : ℂ} (hw : ‖w‖ < 1) : 1 + w ∈ Complex.slitPlane := by
  refine Complex.mem_slitPlane_iff.2 (Or.inl ?_)
  have := Complex.abs_re_le_norm w
  rw [Complex.add_re, Complex.one_re]
  linarith [abs_lt.1 (this.trans_lt hw)]

/-- The circle of radius `R` winds once around the points of `S` inside it. -/
theorem cant_cWinding_circ_in {R : ℝ} (hR : 0 < R) (hS : ∀ s ∈ fibS, ‖s‖ ≠ R) {q : ℂ}
    (hq : q ∈ fibS) (hqR : ‖q‖ < R) :
    cWinding ((cantCircPath hR.le hS).map (subFib q hq).continuous) = 1 := by
  set w : I → ℂ := fun t => q / (R : ℂ) * Complex.exp (-(2 * Real.pi * Complex.I * (t : ℝ)))
  have hR0 : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hR.ne'
  have hw : ∀ t, ‖w t‖ < 1 := fun t => by
    simp only [w, norm_mul, norm_div, Complex.norm_real, Real.norm_of_nonneg hR.le,
      cant_norm_exp_neg, mul_one]
    rwa [div_lt_one hR]
  have hwc : Continuous w := by simp only [w]; fun_prop
  refine cWinding_eq _ (Γ := ⟨fun t => Complex.log (-(R : ℂ)) + 2 * Real.pi * Complex.I * (t : ℝ) +
      Complex.log (1 + w t), (continuous_const.add (by fun_prop)).add
        (continuous_iff_continuousAt.2 fun t =>
          (continuous_const.add hwc).continuousAt.clog (cant_slit_of_norm (hw t)))⟩) (fun t => ?_) ?_
  · show Complex.exp (Complex.log (-(R : ℂ)) + 2 * Real.pi * Complex.I * (t : ℝ) +
      Complex.log (1 + w t)) = cantCirc R t - q
    rw [Complex.exp_add, Complex.exp_add, Complex.exp_log (neg_ne_zero.2 hR0),
      Complex.exp_log (Complex.slitPlane_ne_zero (cant_slit_of_norm (hw t)))]
    simp only [w, cantCirc, Complex.exp_neg]
    have hE := Complex.exp_ne_zero (2 * Real.pi * Complex.I * (t : ℝ))
    field_simp
    ring
  · simp only [ContinuousMap.coe_mk, w, Set.Icc.coe_one, Set.Icc.coe_zero, Complex.ofReal_one,
      Complex.ofReal_zero, mul_one, mul_zero, neg_zero, Complex.exp_zero, Int.cast_one, one_mul]
    rw [Complex.exp_neg, Complex.exp_two_pi_mul_I, inv_one, mul_one]
    ring

/-- The circle of radius `R` does not wind around the points of `S` outside it. -/
theorem cant_cWinding_circ_out {R : ℝ} (hR : 0 < R) (hS : ∀ s ∈ fibS, ‖s‖ ≠ R) {q : ℂ}
    (hq : q ∈ fibS) (hqR : R < ‖q‖) :
    cWinding ((cantCircPath hR.le hS).map (subFib q hq).continuous) = 0 := by
  have hq0 : q ≠ 0 := fun h => by rw [h, norm_zero] at hqR; linarith
  set w : I → ℂ := fun t => (R : ℂ) / q * Complex.exp (2 * Real.pi * Complex.I * (t : ℝ))
  have hw : ∀ t, ‖w t‖ < 1 := fun t => by
    simp only [w, norm_mul, norm_div, Complex.norm_real, Real.norm_of_nonneg hR.le,
      cant_norm_exp, mul_one]
    rwa [div_lt_one (by linarith)]
  have hwc : Continuous w := by simp only [w]; fun_prop
  refine cWinding_eq _ (Γ := ⟨fun t => Complex.log (-q) + Complex.log (1 + w t),
      continuous_const.add (continuous_iff_continuousAt.2 fun t =>
          (continuous_const.add hwc).continuousAt.clog (cant_slit_of_norm (hw t)))⟩) (fun t => ?_) ?_
  · show Complex.exp (Complex.log (-q) + Complex.log (1 + w t)) = cantCirc R t - q
    rw [Complex.exp_add, Complex.exp_log (neg_ne_zero.2 hq0),
      Complex.exp_log (Complex.slitPlane_ne_zero (cant_slit_of_norm (hw t)))]
    simp only [w, cantCirc]
    field_simp
    ring
  · simp only [ContinuousMap.coe_mk, w, Set.Icc.coe_one, Set.Icc.coe_zero, Complex.ofReal_one,
      Complex.ofReal_zero, mul_one, mul_zero, Complex.exp_zero, Int.cast_zero, zero_mul, add_zero,
      Complex.exp_two_pi_mul_I]

/-- The radius `R_k` between `a_k` and the radius of `D_k`. -/
def cantR (k : ℕ) : ℝ := (1 / ((k : ℝ) + 1) + 1 / ((k : ℝ) + 1 / 2)) / 2

theorem cantR_pos (k : ℕ) : 0 < cantR k := by unfold cantR; positivity

theorem cantR_gt (k : ℕ) : 1 / ((k : ℝ) + 1) < cantR k := by
  have : 1 / ((k : ℝ) + 1) < 1 / ((k : ℝ) + 1 / 2) :=
    one_div_lt_one_div_of_lt (by positivity) (by linarith)
  unfold cantR; linarith

theorem cantR_lt (k : ℕ) : cantR k < 1 / ((k : ℝ) + 1 / 2) := by
  have : 1 / ((k : ℝ) + 1) < 1 / ((k : ℝ) + 1 / 2) :=
    one_div_lt_one_div_of_lt (by positivity) (by linarith)
  unfold cantR; linarith

theorem norm_cantPt (m : ℕ) : ‖cantPt m‖ = 1 / ((m : ℝ) + 1) := by
  rw [cantPt, Complex.norm_real, Real.norm_of_nonneg (by positivity)]

theorem cant_norm_lt_cantR {k m : ℕ} (h : k ≤ m) : ‖cantPt m‖ < cantR k := by
  rw [norm_cantPt]
  have : 1 / ((m : ℝ) + 1) ≤ 1 / ((k : ℝ) + 1) :=
    one_div_le_one_div_of_le (by positivity) (by have : (k : ℝ) ≤ m := (by exact_mod_cast h); linarith)
  linarith [cantR_gt k]

theorem cant_cantR_lt_norm {k m : ℕ} (h : m < k) : cantR k < ‖cantPt m‖ := by
  rw [norm_cantPt]
  have : 1 / ((k : ℝ) + 1 / 2) < 1 / ((m : ℝ) + 1) :=
    one_div_lt_one_div_of_lt (by positivity) (by have : (m : ℝ) + 1 ≤ k := (by exact_mod_cast h); linarith)
  linarith [cantR_lt k]

theorem cantR_ne (k : ℕ) : ∀ s ∈ fibS, ‖s‖ ≠ cantR k := by
  rintro s (rfl | ⟨m, rfl⟩)
  · rw [norm_zero]; exact (cantR_pos k).ne
  · show ‖cantPt m‖ ≠ cantR k
    rcases lt_or_ge m k with h | h
    · exact (cant_cantR_lt_norm h).ne'
    · exact (cant_norm_lt_cantR h).ne

/-- The flip of all the signs `m ≥ k` is realised (the circle of radius `R_k` around `0`). -/
theorem cantReal_big {k : ℕ} {c : AbsU y₀} (hc : absP y₀ c ∈ fibD k) :
    CantReal y₀ k c fun m => if k ≤ m then -1 else 1 := by
  obtain ⟨h, hh, hc'⟩ := cant_loop_realize y₀ c hc (cantCircPath (cantR_pos k).le (cantR_ne k))
    fun t => by
      show cantCirc (cantR k) t ∈ fibD k
      rw [fibD, Metric.mem_ball, dist_zero_right, norm_cantCirc (cantR_pos k).le]
      exact cantR_lt k
  refine ⟨h, fun m => ?_, hc'⟩
  beta_reduce
  rw [hh]
  by_cases hm : k ≤ m
  · rw [cant_cWinding_circ_in (cantR_pos k) (cantR_ne k) _ (cant_norm_lt_cantR hm), if_pos hm]
    norm_num
  · rw [cant_cWinding_circ_out (cantR_pos k) (cantR_ne k) _ (cant_cantR_lt_norm (not_le.1 hm)),
      if_neg hm]
    norm_num

/-- Every `±1` pattern supported in `[k, N)` is realised. -/
theorem cantReal_finite {k : ℕ} {c : AbsU y₀} (hc : absP y₀ c ∈ fibD k) :
    ∀ (N : ℕ) (τ : ℕ → ℂ), (∀ m, τ m = 1 ∨ τ m = -1) → (∀ m, m < k ∨ N ≤ m → τ m = 1) →
      CantReal y₀ k c τ := by
  intro N
  induction N with
  | zero =>
    intro τ _ hτ
    exact cantReal_congr y₀ (fun m => (hτ m (Or.inr (Nat.zero_le m))).symm) (cantReal_one y₀ hc)
  | succ N ih =>
    intro τ hpm hτ
    have h' := ih (fun m => if m = N then 1 else τ m)
      (fun m => by split_ifs <;> simp_all) (fun m hm => by
        split_ifs with h
        · rfl
        · refine hτ m ?_
          rcases hm with hm | hm
          · exact Or.inl hm
          · exact Or.inr (by omega))
    rcases hpm N with hN | hN
    · exact cantReal_congr y₀ (fun m => by split_ifs with h <;> simp_all) h'
    · have hkN : k ≤ N := by
        by_contra hlt
        have := hτ N (Or.inl (not_le.1 hlt))
        rw [hN] at this; norm_num at this
      refine cantReal_congr y₀ (fun m => ?_) (cantReal_mul y₀ hc h' (cantReal_flip y₀ hc hkN))
      by_cases h : m = N
      · subst h; simp [hN]
      · simp [h]

/-! #### The signs of a loop class are eventually constant -/

theorem cant_wind_eq_of_small (γ : Path y₀ y₀) {δ : ℝ}
    (hmin : ∀ t, δ ≤ ‖((γ t : (fibSᶜ : Set ℂ)) : ℂ)‖) {n m : ℕ} (hn : ‖cantPt n‖ < δ / 3)
    (hm : ‖cantPt m‖ < δ / 3) :
    windAt y₀ _ (cantPt_mem n) γ = windAt y₀ _ (cantPt_mem m) γ := by
  unfold windAt
  obtain ⟨Γ, hΓ⟩ := exists_expLift (γ.map (subFib _ (cantPt_mem m)).continuous).toContinuousMap
  have e := cWinding_spec _ hΓ
  have hden : ∀ t, ((γ t : (fibSᶜ : Set ℂ)) : ℂ) - cantPt m ≠ 0 := fun t h =>
    (γ t).2 (by rw [sub_eq_zero] at h; rw [h]; exact cantPt_mem m)
  set w : I → ℂ := fun t => (cantPt m - cantPt n) / (((γ t : (fibSᶜ : Set ℂ)) : ℂ) - cantPt m)
  have hw : ∀ t, ‖w t‖ < 1 := fun t => by
    have h1 : ‖cantPt m - cantPt n‖ ≤ ‖cantPt m‖ + ‖cantPt n‖ := norm_sub_le _ _
    have h2 : ‖((γ t : (fibSᶜ : Set ℂ)) : ℂ)‖ - ‖cantPt m‖ ≤
        ‖((γ t : (fibSᶜ : Set ℂ)) : ℂ) - cantPt m‖ := norm_sub_norm_le _ _
    have h3 := hmin t
    have hpos : 0 < ‖((γ t : (fibSᶜ : Set ℂ)) : ℂ) - cantPt m‖ := norm_pos_iff.2 (hden t)
    simp only [w, norm_div]
    rw [div_lt_one hpos]
    linarith [norm_nonneg (cantPt n), norm_nonneg (cantPt m)]
  have hwc : Continuous w := by
    simp only [w]
    exact continuous_const.div ((continuous_subtype_val.comp γ.continuous).sub continuous_const) hden
  have hL : Continuous fun t => Complex.log (1 + w t) :=
    continuous_iff_continuousAt.2 fun t =>
      (continuous_const.add hwc).continuousAt.clog (cant_slit_of_norm (hw t))
  refine cWinding_eq _ (Γ := Γ + ⟨fun t => Complex.log (1 + w t), hL⟩) (fun t => ?_) ?_
  · show Complex.exp (Γ t + Complex.log (1 + w t)) = ((γ t : (fibSᶜ : Set ℂ)) : ℂ) - cantPt n
    rw [Complex.exp_add, Complex.exp_log (Complex.slitPlane_ne_zero (cant_slit_of_norm (hw t))), hΓ t]
    show (((γ t : (fibSᶜ : Set ℂ)) : ℂ) - cantPt m) * (1 + w t) = _
    simp only [w]
    field_simp [hden t]
    ring
  · have hw10 : w 1 = w 0 := by simp only [w, γ.source, γ.target]
    simp only [ContinuousMap.add_apply, ContinuousMap.coe_mk]
    rw [hw10, e]
    ring

theorem cant_wind_eventually (γ : Path y₀ y₀) :
    ∃ N, ∀ n ≥ N, windAt y₀ _ (cantPt_mem n) γ = windAt y₀ _ (cantPt_mem N) γ := by
  obtain ⟨t₀, -, ht₀⟩ := isCompact_univ.exists_isMinOn univ_nonempty
    (f := fun t : I => ‖((γ t : (fibSᶜ : Set ℂ)) : ℂ)‖)
    (continuous_norm.comp (continuous_subtype_val.comp γ.continuous)).continuousOn
  set δ := ‖((γ t₀ : (fibSᶜ : Set ℂ)) : ℂ)‖
  have hδ : 0 < δ := norm_pos_iff.2 fun h => (γ t₀).2 (h ▸ Set.mem_insert 0 _)
  have hmin : ∀ t, δ ≤ ‖((γ t : (fibSᶜ : Set ℂ)) : ℂ)‖ := fun t => ht₀ (mem_univ t)
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt (show 0 < δ / 3 by positivity)
  have hsmall : ∀ n ≥ N, ‖cantPt n‖ < δ / 3 := fun n hn => by
    rw [norm_cantPt]
    have : 1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by have : (N : ℝ) ≤ n := (by exact_mod_cast hn); linarith)
    linarith
  exact ⟨N, fun n hn => cant_wind_eq_of_small y₀ γ hmin (hsmall n hn) (hsmall N le_rfl)⟩

theorem cant_eps_eventually (g : AbsGamma y₀) :
    ∃ N, ∀ n ≥ N, cantEps y₀ n g = cantEps y₀ N g := by
  suffices h : ∀ q : Path.Homotopic.Quotient y₀ y₀, ∃ N, ∀ n ≥ N,
      cantEps y₀ n (FundamentalGroup.fromPath q) = cantEps y₀ N (FundamentalGroup.fromPath q) from
    h (FundamentalGroup.toPath g)
  intro q
  induction q using Path.Homotopic.Quotient.ind with
  | mk γ =>
    obtain ⟨N, hN⟩ := cant_wind_eventually y₀ γ
    exact ⟨N, fun n hn => by rw [cantEps_fromPath, cantEps_fromPath, hN n hn]⟩

/-- Every deck transformation trivial on the signs `m < k` has its pattern realised inside the
component of `c` over `D_k`. -/
theorem cantReal_of_eps {k : ℕ} {c : AbsU y₀} (hc : absP y₀ c ∈ fibD k) (g : AbsGamma y₀)
    (hg : ∀ m < k, cantEps y₀ m g = 1) : CantReal y₀ k c fun m => cantEps y₀ m g := by
  obtain ⟨N₀, hN₀⟩ := cant_eps_eventually y₀ g
  set N := max N₀ k
  have hN : ∀ n ≥ N, cantEps y₀ n g = cantEps y₀ N g := fun n hn =>
    (hN₀ n (le_trans (le_max_left _ _) hn)).trans (hN₀ N (le_max_left _ _)).symm
  rcases cantEps_eq y₀ N g with hE | hE
  · exact cantReal_finite y₀ hc N _ (fun m => cantEps_eq y₀ m g) fun m hm =>
      hm.elim (hg m) fun h => (hN m h).trans hE
  · have h' := cantReal_finite y₀ hc N (fun m => cantEps y₀ m g * if k ≤ m then -1 else 1)
      (fun m => by
        rcases cantEps_eq y₀ m g with e | e <;> rw [e] <;> split_ifs <;> norm_num)
      (fun m hm => by
        rcases hm with hm | hm
        · rw [hg m hm, if_neg (not_le.2 hm)]; ring
        · rw [hN m hm, hE, if_pos (le_trans (le_max_right _ _) hm)]; ring)
    refine cantReal_congr y₀ (fun m => ?_) (cantReal_mul y₀ hc h' (cantReal_big y₀ hc))
    split_ifs <;> ring

/-! #### `Γ₂' \ \widetilde{ℂ∖S}`, its completion `Y₂'`, and the components over `D_k` -/

/-- `Γ₂'` as a group of homeomorphisms of `\widetilde{ℂ∖S}`. -/
def cantHomeo : Subgroup (AbsU y₀ ≃ₜ AbsU y₀) :=
  ((cantGamma y₀).map UniversalCover.deckHom).map
    (deckGroup (UniversalCover.proj (fibSᶜ : Set ℂ) y₀)).subtype

/-- `Γ₂' \ ord(\widetilde Y^S)`. -/
abbrev CantOrd : Type := HomeoQuotient (cantHomeo y₀)

/-- The spread `Γ₂' \ ord(\widetilde Y^S) → Y`. -/
def cantProj : CantOrd y₀ → ℂ :=
  Quotient.lift (univCoverProj fibS y₀) fun a b ⟨φ, hφ, h⟩ => by
    obtain ⟨ψ, -, rfl⟩ := Subgroup.mem_map.1 hφ
    rw [← h]
    exact (congrArg Subtype.val (congrFun ψ.2 a)).symm

/-- **`Y₂'`**, the completion of the spread `Γ₂' \ ord(\widetilde Y^S) → Y` (DEC-69). -/
abbrev CantY₂ : Type := SpreadEnd (cantProj y₀)

/-- The fibre of `Y₂'` above `0`. -/
def cantFiber0 : Set (CantY₂ y₀) := SpreadEnd.base ⁻¹' {0}

theorem cantProj_mk (c : AbsU y₀) : cantProj y₀ (homeoQuotientMk _ c) = absP y₀ c := rfl

theorem cantSigma_inv {φ : AbsU y₀ ≃ₜ AbsU y₀} (hφ : φ ∈ cantHomeo y₀) (n : ℕ) (c : AbsU y₀) :
    cantSigma y₀ n (φ c) = cantSigma y₀ n c := by
  obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.1 hφ
  obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.1 hd
  show cantSigma y₀ n ((UniversalCover.deckHom g).1 c) = _
  rw [cantSigma_deckHom, hg n, one_mul]

/-- The bit `σₙ = 1` on `Γ₂' \ \widetilde{ℂ∖S}`. -/
def cantBitQ (n : ℕ) : CantOrd y₀ → Bool :=
  Quotient.lift (cantBit y₀ n) fun a b ⟨φ, hφ, h⟩ => by
    rw [← h]; unfold cantBit; rw [cantSigma_inv y₀ hφ]

theorem cant_isOpen_levelQ {n k : ℕ} (hnk : n < k) (b : Bool) :
    IsOpen {x : CantOrd y₀ | cantProj y₀ x ∈ fibD k ∧ cantBitQ y₀ n x = b} := by
  rw [← isQuotientMap_quotient_mk'.isOpen_preimage]
  exact cant_isOpen_level y₀ hnk b

theorem cantBitQ_const {n k : ℕ} (hnk : n < k) {x x' : CantOrd y₀} (hx : cantProj y₀ x ∈ fibD k)
    (hx' : x' ∈ connectedComponentIn (cantProj y₀ ⁻¹' fibD k) x) :
    cantBitQ y₀ n x' = cantBitQ y₀ n x :=
  cant_const_of_isOpen_level (A := cantProj y₀ ⁻¹' fibD k) (fun b => cant_isOpen_levelQ y₀ hnk b)
    isPreconnected_connectedComponentIn (connectedComponentIn_subset _ _)
    (mem_connectedComponentIn hx) hx'

/-- **Points of `Γ₂' \ \widetilde{ℂ∖S}` over `D_k` with the same signs `σₙ`, `n < k`, lie in the
same component of the preimage of `D_k`.** -/
theorem cant_mem_comp_of_sigma {k : ℕ} {c c' : AbsU y₀} (hc : absP y₀ c ∈ fibD k)
    (hc' : absP y₀ c' ∈ fibD k) (hs : ∀ n < k, cantSigma y₀ n c' = cantSigma y₀ n c) :
    homeoQuotientMk _ c' ∈ connectedComponentIn (cantProj y₀ ⁻¹' fibD k) (homeoQuotientMk _ c) := by
  obtain ⟨c'', hc'', hpt⟩ := cant_reach y₀ c hc c'.pt hc'
  obtain ⟨g, hg⟩ := cant_exists_deck y₀ hpt
  have hc''k : absP y₀ c'' ∈ fibD k := connectedComponentIn_subset (absP y₀ ⁻¹' fibD k) c hc''
  have hgk : ∀ m < k, cantEps y₀ m g = 1 := by
    intro m hm
    have e1 := cantSigma_deckHom y₀ m g c''
    rw [hg] at e1
    have e2 : cantSigma y₀ m c'' = cantSigma y₀ m c :=
      cantSigma_const y₀ hm isPreconnected_connectedComponentIn (connectedComponentIn_subset _ _)
        (mem_connectedComponentIn hc) hc''
    rw [hs m hm, e2] at e1
    have hne : cantSigma y₀ m c ≠ 0 := by
      rcases cantSigma_eq y₀ (cant_re_lt_of_mem_fibD hm hc) with e | e <;> rw [e] <;> norm_num
    have : (cantEps y₀ m g - 1) * cantSigma y₀ m c = 0 := by linear_combination -e1
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hne)
  obtain ⟨h, hh, hhc⟩ := cantReal_of_eps y₀ hc''k g hgk
  have hu : g * h⁻¹ ∈ cantGamma y₀ := fun m => by
    show cantEps y₀ m (g * h⁻¹) = 1
    rw [cantEps_mul, cantEps_inv, hh m]
    beta_reduce
    rw [← sq, cantEps_sq]
  have heq : homeoQuotientMk (cantHomeo y₀) ((UniversalCover.deckHom h).1 c'') =
      homeoQuotientMk _ c' := Quotient.sound
    ⟨(UniversalCover.deckHom (g * h⁻¹)).1,
      Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem _ hu), by
        rw [← hg]
        show ((UniversalCover.deckHom (g * h⁻¹)) * (UniversalCover.deckHom h)).1 c'' = _
        rw [← map_mul, inv_mul_cancel_right]⟩
  rw [← heq]
  have hcomp : cantComp y₀ k c'' = cantComp y₀ k c := (connectedComponentIn_eq hc'').symm
  have hmem : (UniversalCover.deckHom h).1 c'' ∈ cantComp y₀ k c := hcomp ▸ hhc
  exact (isPreconnected_connectedComponentIn.image _ continuous_quotient_mk'.continuousOn)
    |>.subset_connectedComponentIn ⟨c, mem_connectedComponentIn hc, rfl⟩
      (image_subset_iff.2 fun x hx => by
        exact (connectedComponentIn_subset (absP y₀ ⁻¹' fibD k) c hx : absP y₀ x ∈ fibD k))
      ⟨_, hmem, rfl⟩

/-- The set of points over `D_k` with signs `τ₀, …, τ_{k-1}`. -/
def cantZ (k : ℕ) (τ : ℕ → Bool) : Set (CantOrd y₀) :=
  {x | cantProj y₀ x ∈ fibD k ∧ ∀ n < k, cantBitQ y₀ n x = τ n}

/-- **The components of the preimage of `D_k` are exactly the sets `cantZ k τ`.** -/
theorem cantZ_comp {k : ℕ} {τ : ℕ → Bool} {x : CantOrd y₀} (hx : x ∈ cantZ y₀ k τ) :
    connectedComponentIn (cantProj y₀ ⁻¹' fibD k) x = cantZ y₀ k τ := by
  ext y
  constructor
  · intro hy
    exact ⟨connectedComponentIn_subset (cantProj y₀ ⁻¹' fibD k) x hy, fun n hn =>
      (cantBitQ_const y₀ hn hx.1 hy).trans (hx.2 n hn)⟩
  · intro hy
    induction x using Quotient.inductionOn with
    | h c =>
      induction y using Quotient.inductionOn with
      | h c' =>
        refine cant_mem_comp_of_sigma y₀ hx.1 hy.1 fun n hn => ?_
        exact cantSigma_eq_of_bit y₀ (cant_re_lt_of_mem_fibD hn hx.1)
          (cant_re_lt_of_mem_fibD hn hy.1) ((hy.2 n hn).trans (hx.2 n hn).symm)

theorem cantZ_nonempty (k : ℕ) (τ : ℕ → Bool) : (cantZ y₀ k τ).Nonempty := by
  set c₀ := absGalW y₀ k
  have hc₀ : absP y₀ c₀ ∈ fibD k := by rw [absP_absGalW]; exact (fibQ_mem k).1
  have hc₀0 : absP y₀ c₀ ∈ fibD 0 := fibD_subset_iff.2 (Nat.zero_le k) hc₀
  set ρ : ℕ → ℂ := fun m => if m < k ∧ cantBit y₀ m c₀ ≠ τ m then -1 else 1
  obtain ⟨h, hh, -⟩ := cantReal_finite y₀ hc₀0 k ρ
    (fun m => by simp only [ρ]; split_ifs <;> simp)
    (fun m hm => by
      simp only [ρ]
      rw [if_neg]
      rintro ⟨h1, -⟩
      omega)
  refine ⟨homeoQuotientMk _ ((UniversalCover.deckHom h).1 c₀), hc₀, fun n hn => ?_⟩
  show cantBit y₀ n ((UniversalCover.deckHom h).1 c₀) = τ n
  have hreg := cant_re_lt_of_mem_fibD hn hc₀
  by_cases hb : cantBit y₀ n c₀ = τ n
  · have hρ : ρ n = 1 := if_neg (fun h' => h'.2 hb)
    unfold cantBit
    simp only [cantSigma_deckHom, hh n, hρ, one_mul]
    exact hb
  · have hρ : ρ n = -1 := if_pos ⟨hn, hb⟩
    unfold cantBit at hb ⊢
    simp only [cantSigma_deckHom, hh n, hρ]
    rcases cantSigma_eq y₀ hreg with e | e <;> simp only [e] at hb ⊢ <;> revert hb <;>
      cases τ n <;> norm_num

/-- The thread `D_k ↦ cantZ k τ`. -/
def cantThread (τ : ℕ → Bool) : FiberThread (cantProj y₀) (range fibD) where
  toFun U := cantZ y₀ (absGalIdx U) τ
  isCompOf U := by
    have hU := absGalIdx_spec U
    obtain ⟨x, hx⟩ := cantZ_nonempty y₀ (absGalIdx U) τ
    refine ⟨x, hU ▸ hx.1, ?_⟩
    rw [← cantZ_comp y₀ hx, hU]
  mono U V hUV := by
    have hU := absGalIdx_spec U
    have hV := absGalIdx_spec V
    rw [← hU, ← hV, fibD_subset_iff] at hUV
    exact fun x hx => ⟨fibD_subset_iff.2 hUV hx.1, fun n hn => hx.2 n (lt_of_lt_of_le hn hUV)⟩

/-- The end of `Y₂'` over `0` with signs `τ`. -/
def cantEnd (τ : ℕ → Bool) : CantY₂ y₀ := (cantThread y₀ τ).toEnd absGal_h𝓤 fibD_basis

theorem cantEnd_base (τ : ℕ → Bool) : (cantEnd y₀ τ).base = 0 := rfl

theorem cantEnd_apply (τ : ℕ → Bool) (k : ℕ) : cantEnd y₀ τ (fibD k) = cantZ y₀ k τ := by
  have := FiberThread.toEnd_apply absGal_h𝓤 fibD_basis (cantThread y₀ τ) ⟨fibD k, k, rfl⟩
  rw [cantEnd, this]
  show cantZ y₀ (absGalIdx ⟨fibD k, k, rfl⟩) τ = _
  rw [fibD_injective (absGalIdx_spec ⟨fibD k, k, rfl⟩)]

theorem cantEnd_injective : Injective (cantEnd y₀) := by
  intro τ τ' h
  funext n
  obtain ⟨x, hx⟩ := cantZ_nonempty y₀ (n + 1) τ
  have hx' : x ∈ cantZ y₀ (n + 1) τ' := by rw [← cantEnd_apply, ← h, cantEnd_apply]; exact hx
  exact (hx.2 n (Nat.lt_succ_self n)).symm.trans (hx'.2 n (Nat.lt_succ_self n))

theorem cantEnd_surj (e : CantY₂ y₀) (he : e.base = 0) : ∃ τ, cantEnd y₀ τ = e := by
  have hD : ∀ k, IsCNbhd e.base (fibD k) := fun k => he ▸ isCNbhd_fibD k
  choose y hy using fun n => e.nonempty (hD (n + 1))
  refine ⟨fun n => cantBitQ y₀ n (y n), ?_⟩
  have hk : ∀ k, e (fibD k) = cantZ y₀ k (fun n => cantBitQ y₀ n (y n)) := by
    intro k
    obtain ⟨x, hx⟩ := e.nonempty (hD k)
    have hxZ : x ∈ cantZ y₀ k (fun n => cantBitQ y₀ n (y n)) := by
      refine ⟨e.subset_preimage (hD k) hx, fun n hn => ?_⟩
      have hsub : e (fibD k) ⊆ e (fibD (n + 1)) :=
        e.mono _ _ (hD k) (hD (n + 1)) (fibD_subset_iff.2 hn)
      have hc := (e.isCompOf _ (hD (n + 1))).eq_of_mem (hy n)
      have hx' : x ∈ connectedComponentIn (cantProj y₀ ⁻¹' fibD (n + 1)) (y n) := hc ▸ hsub hx
      exact cantBitQ_const y₀ (Nat.lt_succ_self n) (e.subset_preimage (hD (n + 1)) (hy n)) hx'
    rw [(e.isCompOf _ (hD k)).eq_of_mem hx, cantZ_comp y₀ hxZ]
  refine SpreadEnd.ext_of_isCNbhd ((cantEnd_base y₀ _).trans he.symm) fun U hU => ?_
  have hU0 : IsCNbhd (0 : ℂ) U := hU
  obtain ⟨_, ⟨k, rfl⟩, hkU⟩ := fibD_basis U (hU0.1.mem_nhds hU0.2.2)
  obtain ⟨x, hx⟩ := cantZ_nonempty y₀ k (fun n => cantBitQ y₀ n (y n))
  have h1 : x ∈ cantEnd y₀ _ U :=
    (cantEnd y₀ _).mono _ _ (isCNbhd_fibD k) hU hkU (by rw [cantEnd_apply]; exact hx)
  have h2 : x ∈ e U := e.mono _ _ (hD k) (he ▸ hU0) hkU (by rw [hk]; exact hx)
  exact ((cantEnd y₀ _).isCompOf U hU).eq_of_meets (e.isCompOf U (he ▸ hU0)) ⟨x, h1, h2⟩

theorem continuous_cantEnd : Continuous (cantEnd y₀) := by
  refine continuous_iff_continuousAt.2 fun τ =>
    ((SpreadEnd.hasBasis_nhds (cantEnd y₀ τ)).tendsto_right_iff).2 fun W hW => ?_
  have hW' : IsCNbhd (0 : ℂ) W := hW
  obtain ⟨_, ⟨k, rfl⟩, hkW⟩ := fibD_basis W (hW'.1.mem_nhds hW'.2.2)
  have hev : ∀ᶠ τ' in 𝓝 τ, ∀ n ∈ Finset.range k, τ' n = τ n :=
    (Filter.eventually_all_finset _).2 fun n _ =>
      ((continuous_apply n).tendsto τ) ((isOpen_discrete {τ n}).mem_nhds rfl)
  filter_upwards [hev] with τ' hτ'
  refine ⟨fibD k, isCNbhd_fibD k, hkW, ?_⟩
  have hZ : cantZ y₀ k τ' = cantZ y₀ k τ := by
    ext x
    simp only [cantZ, mem_setOf_eq]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, fun n hn => (h2 n hn).trans (hτ' n (Finset.mem_range.2 hn))⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, fun n hn => (h2 n hn).trans (hτ' n (Finset.mem_range.2 hn)).symm⟩
  rw [cantEnd_apply, hZ, ← cantEnd_apply]
  exact (cantEnd y₀ τ).mono _ _ (isCNbhd_fibD k) hW' hkW

/-- The fibre of `Y₂'` above `0` is homeomorphic to `{0,1}^ℕ`. -/
def cantFiberHomeo : (ℕ → Bool) ≃ₜ cantFiber0 y₀ :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective (fun τ => ⟨cantEnd y₀ τ, cantEnd_base y₀ τ⟩)
      ⟨fun _ _ h => cantEnd_injective y₀ (congrArg Subtype.val h), fun e =>
        ⟨(cantEnd_surj y₀ e.1 e.2).choose, Subtype.ext (cantEnd_surj y₀ e.1 e.2).choose_spec⟩⟩)
    ((continuous_cantEnd y₀).subtype_mk _)

/-- **`ex:consider_denote_absolute_galois`, the fibre claim, CORRECTED (DEC-69)**: with
`Γ₂' = ker(π₁(ℂ∖S) → (ℤ/2)^ℕ)` the kernel of the mod-2 windings around the points `1/n`
(`GX.mem_cantGamma_iff`), the fibre above `0` of the completion `Y₂'` of the spread
`Γ₂' \ ord(\widetilde Y^S) → Y` IS a Cantor set. -/
theorem cant_fiber_isCantor : Nonempty (cantFiber0 y₀ ≃ₜ cantorSet) :=
  ⟨(cantFiberHomeo y₀).symm.trans cantorSetHomeomorphNatToBool.symm⟩

end CantorFibre

end GX
