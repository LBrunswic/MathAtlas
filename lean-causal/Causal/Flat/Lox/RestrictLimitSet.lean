import CausalScaffold.Flat.TwistedProduct
import CausalScaffold.Flat.Externals

/-!
# The regular domain of `Γ` restricts to that of `Γ_{|U}`, and `Λ₀` is a finite-index invariant

Two steps of Barbot's §10, generic loxodromic case ([10.G]), served to
`loxo_generic_centralExtension` (`Flat/Loxodromic.lean`) and through it to
`loxo_generic_torusProduct`: they identify the base domain `ι⁻¹ Ω(S̃)` of the linear twisted
product with the regular domain `Ω^±(Λ(Γ_{|U}))` that family (b) asks for. Line numbers are
those of `papers/barbot/legacy/labeled/GHFspace.tex`. **No label is marked**: these are
sentences of a proof, not statements of the paper. Barbot's `𝐌ⁿ` is `Minkowski d` with
`n = d + 1` (and `U ≅ 𝐌^{d₁+1}`).

* [10.G], `GHFspace.tex:3391–3395`, the "obviously equal" (**no `sorry`**):
  `preimage_omega_closure_repJ` — for an orthochronous `ι` with `ι.RestrictsIn Γ`, the preimage
  under `ι` of `Ω^±` of the closure of the repulsive points of `Γ` in `𝒥` is `Ω^±` of the closure
  of the repulsive points of the restricted group `ι.restrictGroup Γ` in `𝒥(U)`.
* [10.G], `GHFspace.tex:3397–3403`, `3418–3419` (**no `sorry`**): `repJ_eq_of_relIndex_ne_zero` —
  a finite-index subgroup has the same repulsive points in `𝒥`, so "replacing `Γ` by some finite
  index subgroup" does not move `Ω^±(Λ(Γ))`.

> Actually, thanks to Proposition \ref{suspendre}, we can restrict our
> study to the case ${\bf U} = {\bf M}^{n}$ (be aware that
> $\Omega_{lox}(\Gamma)$ is obviously equal to
> ${\bf U}^{\perp} \oplus \Omega_{lox}(\Gamma_{\mid \bf U})$,
> where $\Gamma_{\mid \bf U}$ denotes the restriction of
> $\Gamma$ to ${\bf U}$).

> During the proof of lemma \ref{loxregular}, we actually proved
> that $\Omega(\widetilde{S})$ is the regular convex domain
> defined by the closure of repulsive points of loxodromic
> elements of $\Gamma$. Therefore, it coincides precisely
> with the regular convex domain $\Omega^{+}(\Lambda(\rho))$
> appearing in definition \ref{definitioncauchyhyp}.

> Hence, replacing $\Gamma$ by some finite index subgroup,
> we can assume that this action is trivial.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `Γ` preserves `U` and restricts to isometries of `U` | ✓ carried (`hres : ι.RestrictsIn Γ`) |
| `U` timelike, time orientation of `U` induced | ✓ carried (`ι` an `AffineMinkEmbedding`, `hι`) |
| `Γ` discrete, nonelementary, loxodromic elements exist | ⚠ weakened: not used (any `Γ`) |
| `Γ'` of finite index in `Γ` | ✓ carried (`hle`, `hidx`) |

## SCOPE (disclosed)

The sets are written unfolded: they are, definitionally, `Flat.Loxodromic`'s `loxRepSet`
(`IsRepulsiveFixedJ`), which this file does not import. The paper's `U^⊥ ⊕ Ω_lox(Γ_{|U})` is
read on the section `U` only (the preimage under `ι`), which is what the base of the twisted
product needs; the `U^⊥`-invariance of `Ω` is `TwistedProduct`'s business.

Proof. A point `w₁ = (u₁, s₁)` of `𝒥(U)` goes to `jmap w₁ = (u, s)` with `(1,u)` the
normalisation of the future null `ι.lin (1,u₁)` (first coordinate `c > 0`, by `hι`) and
`⟨(1,u) | p⟩ − s = c⁻¹ (⟨(1,u₁) | q p⟩ − s₁)`, `q = ι.retract`. `jmap` is a closed embedding
(`𝒮(U)` compact), it maps the repulsive points of `Γ_{|U}` onto those of `Γ` (onto: a null
eigenvector of `L(γ)` with eigenvalue `≠ ±1` has no `U^⊥` component, since `U^⊥` is spacelike and
`L(γ)`-stable), so closures correspond. Finite index: a positive power `γᵏ ∈ Γ'` has the same
repulsive point with eigenvalue `λᵏ`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Barbot campaign
(DEC-34), [10.G] integration.
-/

namespace Causal.Flat.Lox

open Set Topology Function

variable {d d₁ : ℕ}

/-! ### Null vectors and the normalisation -/

private theorem rls_fst_pos_of_minkB_neg {f e : Minkowski d} (hf : 0 < f.1) (hfq : minkQ f < 0)
    (he : minkQ e = 0) (hfe : minkB f e < 0) : 0 < e.1 := by
  by_contra hneg
  replace hneg := not_lt.1 hneg
  have hf2 : ‖f.2‖ ≤ f.1 := by
    have := minkQ_lt_zero_iff.1 hfq
    nlinarith [norm_nonneg f.2]
  have he2 : ‖e.2‖ = -e.1 := by
    have h2 : ‖e.2‖ ^ 2 = (-e.1) ^ 2 := by simp only [minkQ] at he; nlinarith
    exact (sq_eq_sq₀ (norm_nonneg _) (by linarith)).1 h2
  have hin := abs_real_inner_le_norm f.2 e.2
  have hin' := neg_abs_le (inner ℝ f.2 e.2)
  simp only [minkB] at hfe
  nlinarith [mul_nonneg (neg_nonneg.2 hneg) (sub_nonneg.2 hf2)]

private theorem rls_exists_nullVec_eq_smul {e : Minkowski d} (he0 : e ≠ 0) (he : minkQ e = 0) :
    ∃ (u : PenroseSphere d) (c : ℝ), c ≠ 0 ∧ nullVec u = c • e := by
  have he1 : e.1 ≠ 0 := fun h0 => he0 (eq_zero_of_fst_eq_zero h0 he.le)
  have hnorm : ‖e.2‖ = |e.1| := by
    have h2 : ‖e.2‖ ^ 2 = |e.1| ^ 2 := by
      have := he; simp only [minkQ] at this; rw [sq_abs]; linarith
    exact (sq_eq_sq₀ (norm_nonneg _) (abs_nonneg _)).1 h2
  refine ⟨⟨e.1⁻¹ • e.2, by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, Real.norm_eq_abs, hnorm,
      inv_mul_cancel₀ (abs_ne_zero.2 he1)]⟩, e.1⁻¹, inv_ne_zero he1, ?_⟩
  refine Prod.ext ?_ rfl
  simp [nullVec, inv_mul_cancel₀ he1]

variable (ι : AffineMinkEmbedding d₁ d)

/-- The first coordinate of `ι.lin (1, u₁)`. -/
private noncomputable def cf (u₁ : PenroseSphere d₁) : ℝ := (ι.lin (nullVec u₁)).1

/-- The offset `⟨ι.lin (1,u₁) | ι 0⟩`. -/
private noncomputable def bf (u₁ : PenroseSphere d₁) : ℝ := minkB (ι.lin (nullVec u₁)) (ι 0)

variable {ι}

private theorem minkQ_lin_nullVec (u₁ : PenroseSphere d₁) : minkQ (ι.lin (nullVec u₁)) = 0 := by
  rw [ι.minkQ_lin, minkQ_nullVec]

private theorem cf_pos (hι : ι.Orthochronous) (u₁ : PenroseSphere d₁) : 0 < cf ι u₁ := by
  refine rls_fst_pos_of_minkB_neg hι (by rw [ι.minkQ_lin_timeVec]; norm_num)
    (minkQ_lin_nullVec u₁) ?_
  rw [ι.minkB_lin]
  simp [minkB, nullVec]

private theorem norm_snd_lin_nullVec (hι : ι.Orthochronous) (u₁ : PenroseSphere d₁) :
    ‖(ι.lin (nullVec u₁)).2‖ = cf ι u₁ := by
  have he := minkQ_lin_nullVec (ι := ι) u₁
  have h2 : ‖(ι.lin (nullVec u₁)).2‖ ^ 2 = (cf ι u₁) ^ 2 := by
    simp only [minkQ] at he; simp only [cf]; linarith
  exact (sq_eq_sq₀ (norm_nonneg _) (cf_pos hι u₁).le).1 h2

variable (ι)

/-- The direction of `ι.lin (1, u₁)` on the sphere `𝒮` of `𝐌ⁿ`. -/
private noncomputable def sig (hι : ι.Orthochronous) (u₁ : PenroseSphere d₁) : PenroseSphere d :=
  ⟨(cf ι u₁)⁻¹ • (ι.lin (nullVec u₁)).2, by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, Real.norm_eq_abs,
      abs_of_pos (cf_pos hι u₁), norm_snd_lin_nullVec hι, inv_mul_cancel₀ (cf_pos hι u₁).ne']⟩

/-- **The correspondence `𝒥(U) → 𝒥`.** -/
private noncomputable def jmap (hι : ι.Orthochronous) (w₁ : PenroseSphere d₁ × ℝ) :
    PenroseSphere d × ℝ :=
  (sig ι hι w₁.1, (cf ι w₁.1)⁻¹ * (w₁.2 + bf ι w₁.1))

variable {ι}

private theorem nullVec_sig (hι : ι.Orthochronous) (u₁ : PenroseSphere d₁) :
    nullVec (sig ι hι u₁) = (cf ι u₁)⁻¹ • ι.lin (nullVec u₁) := by
  refine Prod.ext ?_ rfl
  show (1 : ℝ) = (cf ι u₁)⁻¹ * (ι.lin (nullVec u₁)).1
  rw [← cf, inv_mul_cancel₀ (cf_pos hι u₁).ne']

/-- **The key identity**: `⟨(1,u) | p⟩ − s = c⁻¹ (⟨(1,u₁) | q p⟩ − s₁)`. -/
private theorem jmap_key (hι : ι.Orthochronous) (w₁ : PenroseSphere d₁ × ℝ) (p : Minkowski d) :
    minkB (nullVec (jmap ι hι w₁).1) p - (jmap ι hι w₁).2 =
      (cf ι w₁.1)⁻¹ * (minkB (nullVec w₁.1) (ι.retract p) - w₁.2) := by
  set x := ι.retract p
  have hw : p - ι x ∈ ι.perp := ι.sub_apply_retract_mem_perp p
  have hp : p = ι.lin x + ι 0 + (p - ι x) := by rw [← ι.apply_eq]; abel
  have h0 : minkB (ι.lin (nullVec w₁.1)) (p - ι x) = 0 := by
    rw [minkB_comm]; exact hw _
  show minkB (nullVec (sig ι hι w₁.1)) p - (cf ι w₁.1)⁻¹ * (w₁.2 + bf ι w₁.1) = _
  rw [nullVec_sig, minkB_smul_left]
  conv_lhs => rw [hp]
  rw [minkB_add_right, minkB_add_right, h0, ι.minkB_lin, bf]
  ring

private theorem jmap_key_apply (hι : ι.Orthochronous) (w₁ : PenroseSphere d₁ × ℝ)
    (x : Minkowski d₁) :
    minkB (nullVec (jmap ι hι w₁).1) (ι x) - (jmap ι hι w₁).2 =
      (cf ι w₁.1)⁻¹ * (minkB (nullVec w₁.1) x - w₁.2) := by
  rw [jmap_key, ι.retract_apply]

/-! ### `jmap` is a closed embedding -/

private theorem continuous_lin_nullVec :
    Continuous fun u₁ : PenroseSphere d₁ => ι.lin (nullVec u₁) :=
  (ι.lin.continuous_of_finiteDimensional).comp continuous_nullVec

private theorem continuous_cf : Continuous (cf ι) :=
  continuous_fst.comp continuous_lin_nullVec

private theorem continuous_bf : Continuous (bf ι) := by
  have h := continuous_lin_nullVec (ι := ι)
  unfold bf minkB
  fun_prop

private theorem continuous_sig (hι : ι.Orthochronous) : Continuous (sig ι hι) :=
  Continuous.subtype_mk ((continuous_cf.inv₀ fun u₁ => (cf_pos hι u₁).ne').smul
    (continuous_snd.comp continuous_lin_nullVec)) _

private theorem sig_injective (hι : ι.Orthochronous) : Injective (sig ι hι) := by
  intro u₁ u₁' h
  have h1 := congrArg nullVec h
  rw [nullVec_sig, nullVec_sig, ← map_smul, ← map_smul] at h1
  have h2 := ι.lin_injective h1
  have h3 := congrArg Prod.fst h2
  simp only [Prod.smul_fst, nullVec, smul_eq_mul, mul_one] at h3
  have h4 := congrArg Prod.snd h2
  simp only [Prod.smul_snd, nullVec, h3] at h4
  exact Subtype.ext (smul_right_injective _ (inv_ne_zero (cf_pos hι u₁').ne') h4)

/-- The fibrewise affine reparametrisation `(u₁, s₁) ↦ (u₁, c⁻¹ (s₁ + b))`. -/
private noncomputable def shear (hι : ι.Orthochronous) :
    PenroseSphere d₁ × ℝ ≃ₜ PenroseSphere d₁ × ℝ where
  toFun w := (w.1, (cf ι w.1)⁻¹ * (w.2 + bf ι w.1))
  invFun w := (w.1, cf ι w.1 * w.2 - bf ι w.1)
  left_inv w := by
    have := (cf_pos hι w.1).ne'
    ext
    · rfl
    · show cf ι w.1 * ((cf ι w.1)⁻¹ * (w.2 + bf ι w.1)) - bf ι w.1 = w.2
      field_simp; ring
  right_inv w := by
    have := (cf_pos hι w.1).ne'
    ext
    · rfl
    · show (cf ι w.1)⁻¹ * (cf ι w.1 * w.2 - bf ι w.1 + bf ι w.1) = w.2
      field_simp; ring
  continuous_toFun := continuous_fst.prodMk
    (((continuous_cf.comp continuous_fst).inv₀ fun w => (cf_pos hι w.1).ne').mul
      (continuous_snd.add (continuous_bf.comp continuous_fst)))
  continuous_invFun := continuous_fst.prodMk
    (((continuous_cf.comp continuous_fst).mul continuous_snd).sub
      (continuous_bf.comp continuous_fst))

private theorem isClosedEmbedding_jmap (hι : ι.Orthochronous) :
    IsClosedEmbedding (jmap ι hι) := by
  have hσ : IsClosedEmbedding (sig ι hι) :=
    (continuous_sig hι).isClosedEmbedding (sig_injective hι)
  have : jmap ι hι = Prod.map (sig ι hι) id ∘ shear hι := rfl
  rw [this]
  exact (hσ.prodMap IsClosedEmbedding.id).comp (shear hι).isClosedEmbedding

/-- Every point of `𝒥` whose null vector lies in the direction of `U` is in the image of `jmap`. -/
private theorem exists_jmap_eq (hι : ι.Orthochronous) {w : PenroseSphere d × ℝ} {v : Minkowski d₁}
    (hv : ι.lin v = nullVec w.1) : ∃ w₁, jmap ι hι w₁ = w := by
  have hvq : minkQ v = 0 := by rw [← ι.minkQ_lin, hv, minkQ_nullVec]
  have hv0 : v ≠ 0 := by
    rintro rfl; rw [map_zero] at hv; exact nullVec_ne_zero _ hv.symm
  obtain ⟨u₁, c, hc, hu₁⟩ := rls_exists_nullVec_eq_smul hv0 hvq
  have hlin : ι.lin (nullVec u₁) = c • nullVec w.1 := by rw [hu₁, map_smul, hv]
  have hcf : cf ι u₁ = c := by
    show (ι.lin (nullVec u₁)).1 = c
    rw [hlin]; simp [nullVec]
  refine ⟨(u₁, c * w.2 - bf ι u₁), Prod.ext ?_ ?_⟩
  · apply Subtype.ext
    show (cf ι u₁)⁻¹ • (ι.lin (nullVec u₁)).2 = _
    rw [hcf, hlin]
    simp [nullVec, smul_smul, inv_mul_cancel₀ hc]
  · show (cf ι u₁)⁻¹ * (c * w.2 - bf ι u₁ + bf ι u₁) = w.2
    rw [hcf]; field_simp; ring

/-- **A null eigenvector of `L(γ)` with eigenvalue `λ ≠ ±1` lies in the direction of `U`**:
its `U^⊥` component is an eigenvector of the euclidean isometry `L(γ)|_{U^⊥}`. -/
private theorem mem_range_lin_of_eigen {γ : isom d} {g : isom d₁} (h : ι.Restricts γ g)
    {n : Minkowski d} {l : ℝ} (hl : l ^ 2 ≠ 1) (hn : linOf γ n = l • n) :
    ι.lin (ι.coproj n) = n := by
  set v := ι.coproj n
  set w := n - ι.lin v
  have hw : w ∈ ι.perp := ι.sub_lin_coproj_mem_perp n
  have hnd : n = ι.lin v + w := by simp [w]
  have hLw : linOf γ w ∈ ι.perp := h.linear_mem_perp hw
  have hLv : linOf γ (ι.lin v) = ι.lin (linOf g v) := (h.lin v).symm
  have heq : ι.lin (linOf g v - l • v) = l • w - linOf γ w := by
    have := hn
    rw [hnd, map_add, hLv, smul_add] at this
    rw [map_sub, map_smul, sub_eq_sub_iff_add_eq_add, this]
    abel
  have hmem : ι.lin (linOf g v - l • v) ∈ ι.perp := by
    rw [heq]; exact ι.sub_mem_perp (ι.smul_mem_perp l hw) hLw
  have h0 : linOf g v - l • v = 0 := ι.lin_mem_perp_iff.1 hmem
  rw [h0, map_zero] at heq
  have hLw' : linOf γ w = l • w := (sub_eq_zero.1 heq.symm).symm
  have hQ : minkQ w = 0 := by
    have h1 := lorentz.minkQ_apply (linOf_mem γ) w
    rw [hLw', minkQ_smul] at h1
    have : (l ^ 2 - 1) * minkQ w = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hl)
  have hw0 : w = 0 := by
    by_contra hne
    exact (ι.minkQ_pos_of_mem_perp hw hne).ne' hQ
  rw [hnd, hw0, add_zero]

/-! ### The repulsive sets correspond -/

/-- The repulsive points in `𝒥` of the loxodromic elements of `Γ` (unfolded `loxRepSet`). -/
private def repJ (Γ : Subgroup (isom d)) : Set (PenroseSphere d × ℝ) :=
  {w | ∃ γ ∈ Γ, IsLoxodromic (linOf γ) ∧
    ∃ l : ℝ, 0 < l ∧ l < 1 ∧ linOf γ (nullVec w.1) = l • nullVec w.1 ∧
      ∀ p : Minkowski d, minkB (nullVec w.1) (γ • p) - w.2 =
        l⁻¹ * (minkB (nullVec w.1) p - w.2)}

private theorem sq_ne_one {l : ℝ} (hl0 : 0 < l) (hl1 : l < 1) : l ^ 2 ≠ 1 := by
  intro h; nlinarith

private theorem repJ_eq_image (hι : ι.Orthochronous) {Γ : Subgroup (isom d)}
    (hres : ι.RestrictsIn Γ) : repJ Γ = jmap ι hι '' repJ (ι.restrictGroup Γ) := by
  apply Subset.antisymm
  · rintro w ⟨γ, hγ, -, l, hl0, hl1, hn, hf⟩
    obtain ⟨g, hg⟩ := hres γ hγ
    have hv := mem_range_lin_of_eigen hg (sq_ne_one hl0 hl1) hn
    obtain ⟨w₁, rfl⟩ := exists_jmap_eq hι hv
    refine ⟨w₁, ?_, rfl⟩
    have hgΓ : g ∈ ι.restrictGroup Γ := ⟨γ, hγ, hg⟩
    have hc := (cf_pos hι w₁.1).ne'
    have hn1 : linOf g (nullVec w₁.1) = l • nullVec w₁.1 := by
      apply ι.lin_injective
      have e := hn
      change linOf γ (nullVec (sig ι hι w₁.1)) = l • nullVec (sig ι hι w₁.1) at e
      rw [nullVec_sig, map_smul, smul_comm] at e
      rw [hg.lin, map_smul]
      exact smul_right_injective _ (inv_ne_zero hc) e
    refine ⟨g, hgΓ, isLoxodromic_of_null_eigen (linOf_mem g) (nullVec_ne_zero _)
      (minkQ_nullVec _) hl0 hl1.ne hn1, l, hl0, hl1, hn1, fun x => ?_⟩
    have e1 := jmap_key_apply hι w₁ (g • x)
    have e2 := jmap_key_apply hι w₁ x
    rw [hg x, hf, e2] at e1
    have : minkB (nullVec w₁.1) (g • x) - w₁.2 =
        cf ι w₁.1 * ((cf ι w₁.1)⁻¹ * (minkB (nullVec w₁.1) (g • x) - w₁.2)) := by
      field_simp
    rw [this, ← e1]; field_simp
  · rintro _ ⟨w₁, ⟨g, ⟨γ, hγ, hg⟩, -, l, hl0, hl1, hn, hf⟩, rfl⟩
    have hc := (cf_pos hι w₁.1).ne'
    have hnγ : linOf γ (nullVec (jmap ι hι w₁).1) = l • nullVec (jmap ι hι w₁).1 := by
      show linOf γ (nullVec (sig ι hι w₁.1)) = l • nullVec (sig ι hι w₁.1)
      rw [nullVec_sig, map_smul, ← hg.lin, hn, map_smul, smul_comm]
    refine ⟨γ, hγ, isLoxodromic_of_null_eigen (linOf_mem γ) (nullVec_ne_zero _)
      (minkQ_nullVec _) hl0 hl1.ne hnγ, l, hl0, hl1, hnγ, fun p => ?_⟩
    rw [jmap_key, jmap_key, hg.retract_smul, hf]
    ring

/-- **Closures correspond**: `closure (repJ Γ) = jmap '' closure (repJ Γ_{|U})`. -/
private theorem closure_repJ_eq (hι : ι.Orthochronous) {Γ : Subgroup (isom d)}
    (hres : ι.RestrictsIn Γ) :
    closure (repJ Γ) = jmap ι hι '' closure (repJ (ι.restrictGroup Γ)) := by
  rw [repJ_eq_image hι hres, (isClosedEmbedding_jmap hι).closure_image_eq]

/-- **[10.G], l.3391–3395, read on the section `U`, and l.3397–3403**: the preimage under the
orthochronous parametrisation `ι` of `U` of `Ω^±` of the closure of the repulsive points of `Γ` in
`𝒥` is `Ω^±` of the closure of the repulsive points of the restriction `Γ_{|U}` in `𝒥(U)`. -/
theorem preimage_omega_closure_repJ {d d₁ : ℕ} (ι : AffineMinkEmbedding d₁ d) (hι : ι.Orthochronous)
    {Γ : Subgroup (isom d)} (hres : ι.RestrictsIn Γ) :
    ι ⁻¹' omegaPlus (closure {w : PenroseSphere d × ℝ | ∃ γ ∈ Γ, IsLoxodromic (linOf γ) ∧
        ∃ l : ℝ, 0 < l ∧ l < 1 ∧ linOf γ (nullVec w.1) = l • nullVec w.1 ∧
          ∀ p : Minkowski d, minkB (nullVec w.1) (γ • p) - w.2 =
            l⁻¹ * (minkB (nullVec w.1) p - w.2)}) =
      omegaPlus (closure {w : PenroseSphere d₁ × ℝ | ∃ g ∈ ι.restrictGroup Γ,
        IsLoxodromic (linOf g) ∧
        ∃ l : ℝ, 0 < l ∧ l < 1 ∧ linOf g (nullVec w.1) = l • nullVec w.1 ∧
          ∀ p : Minkowski d₁, minkB (nullVec w.1) (g • p) - w.2 =
            l⁻¹ * (minkB (nullVec w.1) p - w.2)}) ∧
    ι ⁻¹' omegaMinus (closure {w : PenroseSphere d × ℝ | ∃ γ ∈ Γ, IsLoxodromic (linOf γ) ∧
        ∃ l : ℝ, 0 < l ∧ l < 1 ∧ linOf γ (nullVec w.1) = l • nullVec w.1 ∧
          ∀ p : Minkowski d, minkB (nullVec w.1) (γ • p) - w.2 =
            l⁻¹ * (minkB (nullVec w.1) p - w.2)}) =
      omegaMinus (closure {w : PenroseSphere d₁ × ℝ | ∃ g ∈ ι.restrictGroup Γ,
        IsLoxodromic (linOf g) ∧
        ∃ l : ℝ, 0 < l ∧ l < 1 ∧ linOf g (nullVec w.1) = l • nullVec w.1 ∧
          ∀ p : Minkowski d₁, minkB (nullVec w.1) (g • p) - w.2 =
            l⁻¹ * (minkB (nullVec w.1) p - w.2)}) := by
  change ι ⁻¹' omegaPlus (closure (repJ Γ)) = omegaPlus (closure (repJ (ι.restrictGroup Γ))) ∧
    ι ⁻¹' omegaMinus (closure (repJ Γ)) = omegaMinus (closure (repJ (ι.restrictGroup Γ)))
  rw [closure_repJ_eq hι hres]
  constructor
  · ext x
    simp only [mem_preimage, mem_omegaPlus, forall_mem_image]
    refine forall₂_congr fun w₁ _ => ?_
    have e := jmap_key_apply hι w₁ x
    have hc := inv_pos.2 (cf_pos hι w₁.1)
    constructor
    · intro h
      have : (cf ι w₁.1)⁻¹ * (minkB (nullVec w₁.1) x - w₁.2) < 0 := by rw [← e]; linarith
      have := (mul_neg_iff.1 this).resolve_right (by rintro ⟨h1, -⟩; linarith)
      linarith [this.2]
    · intro h
      have : (cf ι w₁.1)⁻¹ * (minkB (nullVec w₁.1) x - w₁.2) < 0 :=
        mul_neg_of_pos_of_neg hc (by linarith)
      linarith
  · ext x
    simp only [mem_preimage, mem_omegaMinus, forall_mem_image]
    refine forall₂_congr fun w₁ _ => ?_
    have e := jmap_key_apply hι w₁ x
    have hc := inv_pos.2 (cf_pos hι w₁.1)
    constructor
    · intro h
      have : 0 < (cf ι w₁.1)⁻¹ * (minkB (nullVec w₁.1) x - w₁.2) := by rw [← e]; linarith
      have := (pos_iff_pos_of_mul_pos this).1 hc
      linarith
    · intro h
      have : 0 < (cf ι w₁.1)⁻¹ * (minkB (nullVec w₁.1) x - w₁.2) :=
        mul_pos hc (by linarith)
      linarith

/-- **[10.G], l.3418–3419**: a finite-index subgroup `Γ' ≤ Γ` has the same repulsive points in
`𝒥` (a positive power `γᵏ ∈ Γ'` of a loxodromic `γ ∈ Γ` is loxodromic with the same repulsive
point, eigenvalue `λᵏ`), so `Λ(Γ') = Λ(Γ)`. -/
theorem repJ_eq_of_relIndex_ne_zero {d : ℕ} {Γ Γ' : Subgroup (isom d)} (hle : Γ' ≤ Γ)
    (hidx : Γ'.relIndex Γ ≠ 0) :
    {w : PenroseSphere d × ℝ | ∃ γ ∈ Γ', IsLoxodromic (linOf γ) ∧
        ∃ l : ℝ, 0 < l ∧ l < 1 ∧ linOf γ (nullVec w.1) = l • nullVec w.1 ∧
          ∀ p : Minkowski d, minkB (nullVec w.1) (γ • p) - w.2 =
            l⁻¹ * (minkB (nullVec w.1) p - w.2)} =
      {w : PenroseSphere d × ℝ | ∃ γ ∈ Γ, IsLoxodromic (linOf γ) ∧
        ∃ l : ℝ, 0 < l ∧ l < 1 ∧ linOf γ (nullVec w.1) = l • nullVec w.1 ∧
          ∀ p : Minkowski d, minkB (nullVec w.1) (γ • p) - w.2 =
            l⁻¹ * (minkB (nullVec w.1) p - w.2)} := by
  apply Subset.antisymm
  · rintro w ⟨γ, hγ, h⟩
    exact ⟨γ, hle hγ, h⟩
  · rintro w ⟨γ, hγ, -, l, hl0, hl1, hn, hf⟩
    obtain ⟨k, hk, -, hmem⟩ := Subgroup.exists_pow_mem_of_relIndex_ne_zero hidx hγ
    have hpow : ∀ m : ℕ, linOf (γ ^ m) (nullVec w.1) = l ^ m • nullVec w.1 ∧
        ∀ p : Minkowski d, minkB (nullVec w.1) ((γ ^ m) • p) - w.2 =
          (l ^ m)⁻¹ * (minkB (nullVec w.1) p - w.2) := by
      intro m
      induction m with
      | zero =>
        refine ⟨by simp; rfl, fun p => by simp⟩
      | succ m ih =>
        refine ⟨?_, fun p => ?_⟩
        · rw [pow_succ, show linOf (γ ^ m * γ) = linOf (γ ^ m) * linOf γ from rfl,
            LinearEquiv.mul_apply, hn, map_smul, ih.1, smul_smul, pow_succ, mul_comm]
        · rw [pow_succ, mul_smul, ih.2, hf, pow_succ, mul_inv]; ring
    have hlk0 : 0 < l ^ k := pow_pos hl0 k
    have hlk1 : l ^ k < 1 := pow_lt_one₀ hl0.le hl1 hk.ne'
    exact ⟨γ ^ k, hmem.1, isLoxodromic_of_null_eigen (linOf_mem _) (nullVec_ne_zero _)
      (minkQ_nullVec _) hlk0 hlk1.ne (hpow k).1, l ^ k, hlk0, hlk1, (hpow k).1, (hpow k).2⟩

end Causal.Flat.Lox
