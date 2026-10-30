import Causal.CauchyExtension

/-!
# A Cauchy surface separates; diamonds and reachable pasts through a Cauchy extension

`lem:Sigma_separe` — `ETT.tex:2062`. `lem:image_diamant` — `ETT.tex:2024`. `lem:passe_pgcd` —
`ETT.tex:2042`. None is marked: each is proved in full, with no `sorry`, under named hypotheses
carrying facts of the singular flat setting (kb/0012). The timelike line satisfies them jointly
(`timelikeLine_cauchy_diamond_hypotheses`), but two only weakly: the `prop:K_calcul` facts on
`Sing` vacuously (`Sing = ∅`), and the hypothesis on `p` of `passe_pgcd` only at points of
`range id = ℝ`, where its conclusion is trivial.

> Then $J^+(\Sigma)=\psi\left(\Sigma\times \RR_+\right)$ and
> $J^-(\Sigma)=\psi\left(\Sigma\times \RR_-\right)$. In particular $J^\pm(\Sigma)$ are closed,
> $J^+(\Sigma)\cap J^-(\Sigma)=\Sigma$, and $J^+(\Sigma)$ is a neighbourhood of each of its points
> outside $\Sigma$.

> Let $i:M\rightarrow N$ be a Cauchy extension and let $p\in J^+_M(\Sigma)$. Then
> $i\left(J_M(\Sigma,p)\right)=J_N\left(i(\Sigma),i(p)\right)$.

> let $p\in \partial i(M)\cap J^+\left(i(\Sigma)\right)$. Then
> $K^-_N(p)\cap J^+\left(i(\Sigma)\right)\subset i(M)$

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `ψ : Σ × ℝ → M` of `theo:geroch_sing` | ⚠ named: `IsCauchySplitting` (homeomorphism, `ψ(x,0) = x`, lines future causal) |
| `Σ` a Cauchy surface (Sigma_separe) | ⚠ strengthened: what is assumed is `Σ` acausal (`IsAcausal`), which a Cauchy surface is under `CurvesExtend` and causal arc-connectedness (`IsCauchySurface.isAcausal`) |
| `M` causal | ✓ carried |
| `K = J_M(Σ, p)` compact, "since `M` is globally hyperbolic" | ⚠ strengthened: named hypothesis |
| `M = J⁺(Σ) ∪ J⁻(Σ)` (used in image_diamant) | ⚠ named: `hcover`, given by `IsCauchySplitting.cover` |
| `N` causally arc-connected; curves of `N` extend | ⚠ named |
| `p ∈ ∂ i(M) ∩ J⁺(i Σ)` (passe_pgcd) | ⚠ weakened: `p ∈ closure (i M)` |
| `N` second countable | ⚠ weakened: first countable |
| `prop:K_calcul` on `sing₀(N)` | ⚠ named: a set `Sing` and the two values of `K⁻` |

## SCOPE (disclosed)

* `J_M(Σ, p)` is read `J⁺(Σ) ∩ J⁻(p)`. The proof of `image_diamant` follows the paper's
  (least parameter `s₀` from which the curve stays in `i(K)`), along a future curve from `q` to
  `i(p)`.
* `lem:passe_pgcd` applies `image_diamant` at points `p_n ∈ i(M)` the paper does not show to lie in
  `i(J⁺(Σ))`; the case of a point of `J⁻(Σ)` is `diamond_subset_range`, by acausality of `i(Σ)`.
* `CurvesExtend` (every causal curve over a segment lies on an inextensible one) is a model fact.
  The step it replaces in the proof of `lem:Sigma_separe` (extending the concatenated curve to an
  inextensible one before invoking the Cauchy property) is an omitted standard step of an
  **editorial** proof (`ETT.tex:2068`, "[editorial] supplied 2026-08-22 -- verify"), not of the
  author's.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Filter Function

universe u v

variable {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]

namespace Causality

variable {C : Causality M}

/-! ### `lem:Sigma_separe` -/

/-- **The splitting of `theo:geroch_sing`, carried as a named hypothesis** (kb/0012): `ψ` is a
homeomorphism `S × ℝ → M` with `ψ(x, 0) = x` whose lines `t ↦ ψ(x, t)` are future causal, in the
sense that `s ≤ t` gives `ψ(x, s) ≤ ψ(x, t)`. The paper builds `ψ` as the flow of a causal
vector field (`lem:vecteur`); the library has neither. -/
structure IsCauchySplitting (C : Causality M) (S : Set M) (ψ : S × ℝ ≃ₜ M) : Prop where
  zero : ∀ x : S, ψ (x, 0) = x
  mono : ∀ (x : S) ⦃s t : ℝ⦄, s ≤ t → C.le ⊤ (ψ (x, s)) (ψ (x, t))

/-- `lem:Sigma_separe`, first equality: `J⁺(S) = ψ(S × ℝ₊)`. -/
theorem IsCauchySplitting.Jplus_eq (hcaus : C.IsCausal) {S : Set M} (hS : C.IsAcausal S)
    {ψ : S × ℝ ≃ₜ M} (hψ : IsCauchySplitting C S ψ) :
    C.Jplus ⊤ S = ψ '' (univ ×ˢ Ici 0) := by
  ext y
  constructor
  · rintro ⟨σ, hσ, hσy⟩
    obtain ⟨⟨x, t⟩, rfl⟩ := ψ.surjective y
    refine ⟨(x, t), ⟨trivial, ?_⟩, rfl⟩
    show (0 : ℝ) ≤ t
    by_contra ht
    have ht' : t < 0 := lt_of_not_ge ht
    have h1 : C.le ⊤ (ψ (x, t)) x := by
      have := hψ.mono x ht'.le
      rwa [hψ.zero] at this
    have h2 : σ = x := hS σ hσ x x.2 (C.le_trans hσy h1)
    have h3 : ψ (x, t) = x := hcaus h1 (h2 ▸ hσy)
    have h4 := ψ.injective (h3.trans (hψ.zero x).symm)
    simp only [Prod.mk.injEq, true_and] at h4
    exact ht (h4 ▸ le_rfl)
  · rintro ⟨⟨x, t⟩, ⟨-, ht⟩, rfl⟩
    refine ⟨x, x.2, ?_⟩
    have := hψ.mono x (show (0 : ℝ) ≤ t from ht)
    rwa [hψ.zero] at this

/-- `lem:Sigma_separe`, second equality: `J⁻(S) = ψ(S × ℝ₋)`. -/
theorem IsCauchySplitting.Jminus_eq (hcaus : C.IsCausal) {S : Set M} (hS : C.IsAcausal S)
    {ψ : S × ℝ ≃ₜ M} (hψ : IsCauchySplitting C S ψ) :
    C.Jminus ⊤ S = ψ '' (univ ×ˢ Iic 0) := by
  ext y
  constructor
  · rintro ⟨σ, hσ, hyσ⟩
    obtain ⟨⟨x, t⟩, rfl⟩ := ψ.surjective y
    refine ⟨(x, t), ⟨trivial, ?_⟩, rfl⟩
    show t ≤ 0
    by_contra ht
    have ht' : 0 < t := lt_of_not_ge ht
    have h1 : C.le ⊤ x (ψ (x, t)) := by
      have := hψ.mono x ht'.le
      rwa [hψ.zero] at this
    have h2 : (x : M) = σ := hS x x.2 σ hσ (C.le_trans h1 hyσ)
    rw [← h2] at hyσ
    have h4 := ψ.injective ((hcaus hyσ h1).trans (hψ.zero x).symm)
    simp only [Prod.mk.injEq, true_and] at h4
    exact ht (h4 ▸ le_rfl)
  · rintro ⟨⟨x, t⟩, ⟨-, ht⟩, rfl⟩
    refine ⟨x, x.2, ?_⟩
    have := hψ.mono x (show t ≤ 0 from ht)
    rwa [hψ.zero] at this

/-- `lem:Sigma_separe`, under the splitting `ψ` of `theo:geroch_sing` and an acausal `S`:
`J⁺(S) = ψ(S × ℝ₊)`, `J⁻(S) = ψ(S × ℝ₋)`; `J^±(S)` are closed, `J⁺(S) ∩ J⁻(S) = S`, and `J⁺(S)` is
a neighbourhood of each of its points outside `S`. -/
theorem sigma_separe (hcaus : C.IsCausal) {S : Set M} (hS : C.IsAcausal S)
    {ψ : S × ℝ ≃ₜ M} (hψ : IsCauchySplitting C S ψ) :
    C.Jplus ⊤ S = ψ '' (univ ×ˢ Ici 0) ∧ C.Jminus ⊤ S = ψ '' (univ ×ˢ Iic 0) ∧
      IsClosed (C.Jplus ⊤ S) ∧ IsClosed (C.Jminus ⊤ S) ∧ C.Jplus ⊤ S ∩ C.Jminus ⊤ S = S ∧
      ∀ y ∈ C.Jplus ⊤ S \ S, C.Jplus ⊤ S ∈ 𝓝 y := by
  have hp := hψ.Jplus_eq hcaus hS
  have hm := hψ.Jminus_eq hcaus hS
  refine ⟨hp, hm, ?_, ?_, ?_, ?_⟩
  · rw [hp]; exact ψ.isClosedMap _ (isClosed_univ.prod isClosed_Ici)
  · rw [hm]; exact ψ.isClosedMap _ (isClosed_univ.prod isClosed_Iic)
  · apply Subset.antisymm
    · rw [hp, hm]
      rintro _ ⟨⟨⟨x, t⟩, ⟨-, ht⟩, rfl⟩, ⟨⟨x', t'⟩, ⟨-, ht'⟩, he⟩⟩
      have he' := ψ.injective he
      simp only [Prod.mk.injEq] at he'
      obtain ⟨rfl, rfl⟩ := he'
      have h0 : t' = 0 := le_antisymm ht' ht
      rw [h0, hψ.zero]
      exact x'.2
    · intro x hx
      exact ⟨⟨x, hx, C.le_refl trivial⟩, ⟨x, hx, C.le_refl trivial⟩⟩
  · rintro y ⟨hy, hyS⟩
    rw [hp] at hy ⊢
    obtain ⟨⟨x, t⟩, ⟨-, ht⟩, rfl⟩ := hy
    have ht0 : (0 : ℝ) < t := lt_of_le_of_ne ht fun h => hyS (by
      rw [← h, hψ.zero]; exact x.2)
    refine Filter.mem_of_superset ((ψ.isOpenMap _ (isOpen_univ.prod isOpen_Ioi)).mem_nhds
      ⟨(x, t), ⟨trivial, ht0⟩, rfl⟩) ?_
    exact image_mono (prod_mono subset_rfl Ioi_subset_Ici_self)

/-- The consequence used by `lem:image_diamant`: `M = J⁺(S) ∪ J⁻(S)`. -/
theorem IsCauchySplitting.cover {S : Set M} {ψ : S × ℝ ≃ₜ M} (hψ : IsCauchySplitting C S ψ)
    (x : M) : x ∈ C.Jplus ⊤ S ∪ C.Jminus ⊤ S := by
  obtain ⟨⟨s, t⟩, rfl⟩ := ψ.surjective x
  rcases le_total 0 t with ht | ht
  · left
    refine ⟨s, s.2, ?_⟩
    have := hψ.mono s ht
    rwa [hψ.zero] at this
  · right
    refine ⟨s, s.2, ?_⟩
    have := hψ.mono s ht
    rwa [hψ.zero] at this

end Causality

/-! ### `lem:image_diamant` -/

variable {C : Causality M} {D : Causality N} {i : M → N}

/-- `lem:image_diamant`, abstractly. `i` is a Cauchy extension, `S` a Cauchy surface of `M`,
`p ∈ J⁺(S)`. Then `i(J⁺(S) ∩ J⁻(p)) = J⁺(i S) ∩ J⁻(i p)`. Carried as named hypotheses: the
compactness of `J⁺(S) ∩ J⁻(p)` (the paper: "since `M` is globally hyperbolic"); `M = J⁺(S) ∪ J⁻(S)`
(`IsCauchySplitting.cover`, from `theo:geroch_sing`); causal arc-connectedness of `N`; and
`CurvesExtend` for `N`, which with `lem:Cauchy_plongement_toutes` makes `i(S)` acausal. -/
theorem IsCauchyEmbedding.image_diamant [T2Space N] (hi : IsCauchyEmbedding C D i)
    {S : Set M} (hS : C.IsCauchySurface S) (hcover : ∀ x, x ∈ C.Jplus ⊤ S ∪ C.Jminus ⊤ S)
    (hDac : D.CausallyArcConnected) (hDext : D.CurvesExtend) {p : M}
    (hp : p ∈ C.Jplus ⊤ S) (hK : IsCompact (C.Jplus ⊤ S ∩ C.Jminus ⊤ {p})) :
    i '' (C.Jplus ⊤ S ∩ C.Jminus ⊤ {p}) = D.Jplus ⊤ (i '' S) ∩ D.Jminus ⊤ {i p} := by
  have hrel : ∀ x y, C.le ⊤ x y → D.le ⊤ (i x) (i y) := fun x y h =>
    hi.isEMorphism.map_le ⊤ ⊤ le_rfl (fun _ _ => trivial) h
  have hD : D.IsCausal := hi.globallyHyperbolic_target.1
  have hacausal : D.IsAcausal (i '' S) :=
    (hi.isCauchySurface_image hS).isAcausal hDac hDext
  apply Subset.antisymm
  · rintro _ ⟨x, ⟨⟨σ, hσ, hσx⟩, hxp⟩, rfl⟩
    rw [Precausality.mem_Jminus_singleton] at hxp
    exact ⟨⟨i σ, ⟨σ, hσ, rfl⟩, hrel _ _ hσx⟩, by
      rw [Precausality.mem_Jminus_singleton]; exact hrel _ _ hxp⟩
  rintro q ⟨⟨_, ⟨σ, hσ, rfl⟩, hσq⟩, hqp⟩
  rw [Precausality.mem_Jminus_singleton] at hqp
  obtain ⟨c, hc, hc0, hc1⟩ := (hDac ⊤ le_rfl q (i p)).1.1 hqp
  set K := C.Jplus ⊤ S ∩ C.Jminus ⊤ {p} with hKdef
  have hpK : p ∈ K := ⟨hp, by rw [Precausality.mem_Jminus_singleton]; exact C.le_refl trivial⟩
  have hK' : IsClosed (i '' K) :=
    (hK.image (by
      have := hi.isEMorphism.continuousOn
      rw [Opens.coe_top, continuousOn_univ] at this
      exact this)).isClosed
  set T := {s ∈ Icc (0 : ℝ) 1 | Icc s 1 ⊆ c ⁻¹' (i '' K)} with hT
  have h1T : (1 : ℝ) ∈ T := ⟨⟨zero_le_one, le_rfl⟩, fun u hu => by
    rw [le_antisymm hu.2 hu.1, mem_preimage, hc1]; exact ⟨p, hpK, rfl⟩⟩
  have hTne : T.Nonempty := ⟨1, h1T⟩
  have hTbdd : BddBelow T := ⟨0, fun s hs => hs.1.1⟩
  set s₀ := sInf T with hs₀def
  have hs₀0 : 0 ≤ s₀ := le_csInf hTne fun s hs => hs.1.1
  have hs₀1 : s₀ ≤ 1 := csInf_le hTbdd h1T
  have hcont : ContinuousOn c (Icc 0 1) := CurveOn.continuousOn D.isRelFamily_le hc
  have habove : ∀ u, s₀ < u → u ≤ 1 → c u ∈ i '' K := fun u hu hu1 => by
    obtain ⟨s, hs, hsu⟩ := exists_lt_of_csInf_lt hTne hu
    exact hs.2 ⟨hsu.le, hu1⟩
  have hs₀K : c s₀ ∈ i '' K := by
    rcases hs₀1.eq_or_lt with h | h
    · rw [h, hc1]; exact ⟨p, hpK, rfl⟩
    · have hclosed : IsClosed (Icc (0 : ℝ) 1 ∩ c ⁻¹' (i '' K)) :=
        hcont.preimage_isClosed_of_isClosed isClosed_Icc hK'
      have hsub : Ioc s₀ 1 ⊆ Icc 0 1 ∩ c ⁻¹' (i '' K) := fun u hu =>
        ⟨⟨hs₀0.trans hu.1.le, hu.2⟩, habove u hu.1 hu.2⟩
      have hcl := hclosed.closure_subset_iff.2 hsub
      rw [closure_Ioc h.ne] at hcl
      exact (hcl ⟨le_rfl, h.le⟩).2
  have hs₀ : s₀ = 0 := by
    by_contra hne
    have hpos : 0 < s₀ := lt_of_le_of_ne hs₀0 (Ne.symm hne)
    have hrange : c s₀ ∈ hi.rangeOpens := by
      obtain ⟨x, -, hx⟩ := hs₀K
      show c s₀ ∈ (hi.rangeOpens : Set N)
      rw [IsCauchyEmbedding.coe_rangeOpens]; exact ⟨x, hx⟩
    have hU : c ⁻¹' (hi.rangeOpens : Set N) ∈ 𝓝[Icc 0 1] s₀ :=
      hcont s₀ ⟨hs₀0, hs₀1⟩ (hi.rangeOpens.isOpen.mem_nhds hrange)
    rw [Metric.mem_nhdsWithin_iff] at hU
    obtain ⟨ε, hε, hsub⟩ := hU
    have ha0 : 0 ≤ max 0 (s₀ - ε / 2) := le_max_left _ _
    have has₀ : max 0 (s₀ - ε / 2) < s₀ := max_lt hpos (by linarith)
    set a := max 0 (s₀ - ε / 2) with ha
    have hmem : ∀ u ∈ Icc a s₀, c u ∈ hi.rangeOpens := fun u hu => hsub
      ⟨by
        rw [Metric.mem_ball, Real.dist_eq, abs_of_nonpos (by linarith [hu.2])]
        linarith [hu.1, le_max_right 0 (s₀ - ε / 2)],
       ⟨ha0.trans hu.1, hu.2.trans hs₀1⟩⟩
    have hcU : D.CausalCurveOn hi.rangeOpens c a s₀ := CurveOn.restrict hc ha0 hs₀1 le_top hmem
    haveI : Nonempty M := ⟨p⟩
    have hg : LeftInvOn (invFunOn i ((⊤ : Opens M) : Set M)) i ((⊤ : Opens M) : Set M) :=
      hi.injective.injOn.leftInvOn_invFunOn
    set g := invFunOn i ((⊤ : Opens M) : Set M)
    have hgc : C.CausalCurveOn ⊤ (g ∘ c) a s₀ :=
      hi.isEMorphism.causalCurveOn_invComp hg le_rfl rfl hcU
    have hφg : ∀ u ∈ Icc a s₀, i (g (c u)) = c u := fun u hu =>
      (IsEMorphismOn.leftInvOn_image hg le_rfl rfl (hmem u hu)).2
    have hgs₀ : g (c s₀) ∈ K := by
      obtain ⟨x, hx, hxe⟩ := hs₀K
      rw [← hxe, hg trivial]; exact hx
    have hnew : ∀ u ∈ Icc a s₀, c u ∈ i '' K := fun u hu => by
      refine ⟨g (c u), ⟨?_, ?_⟩, hφg u hu⟩
      · rcases hcover (g (c u)) with h | ⟨σ'', hσ'', hle⟩
        · exact h
        · have h1 : D.le ⊤ (c u) (i σ'') := by
            have := hrel _ _ hle; rwa [hφg u hu] at this
          have h0 : D.le ⊤ (i σ) (c u) := D.le_trans hσq (by
            rw [← hc0]; exact hc.le_of_le le_rfl (ha0.trans hu.1) (hu.2.trans hs₀1))
          have heqσ : i σ = i σ'' :=
            hacausal (i σ) ⟨σ, hσ, rfl⟩ (i σ'') ⟨σ'', hσ'', rfl⟩ (D.le_trans h0 h1)
          have hcu : c u = i σ'' := hD h1 (heqσ ▸ h0)
          have hgu : g (c u) = σ'' := by rw [hcu, hg trivial]
          rw [hgu]; exact ⟨σ'', hσ'', C.le_refl trivial⟩
      · rw [Precausality.mem_Jminus_singleton]
        have hgs₀p := hgs₀.2
        rw [Precausality.mem_Jminus_singleton] at hgs₀p
        exact C.le_trans (hgc.le_of_le hu.1 hu.2 le_rfl) hgs₀p
    have haT : a ∈ T := ⟨⟨ha0, has₀.le.trans hs₀1⟩, fun u hu => by
      rcases le_or_gt u s₀ with h | h
      · exact hnew u ⟨hu.1, h⟩
      · exact habove u h hu.2⟩
    exact absurd (csInf_le hTbdd haT) (not_le.2 has₀)
  rw [hs₀, hc0] at hs₀K
  exact hs₀K

/-- The diamond from `i(S)` to the image of **any** point of `M` lies in `i(M)`: for a point of
`J⁺(S)` this is `image_diamant`; for a point of `J⁻(S)` the diamond is that point, `i(S)` being
acausal. This is what `lem:passe_pgcd` applies to its sequence `(p_n)`, about which the paper does
not say that it lies in `J⁺(S)`. -/
theorem IsCauchyEmbedding.diamond_subset_range [T2Space N] (hi : IsCauchyEmbedding C D i)
    {S : Set M} (hS : C.IsCauchySurface S) (hcover : ∀ x, x ∈ C.Jplus ⊤ S ∪ C.Jminus ⊤ S)
    (hDac : D.CausallyArcConnected) (hDext : D.CurvesExtend)
    (hK : ∀ m ∈ C.Jplus ⊤ S, IsCompact (C.Jplus ⊤ S ∩ C.Jminus ⊤ {m})) (m : M) :
    D.Jplus ⊤ (i '' S) ∩ D.Jminus ⊤ {i m} ⊆ range i := by
  rcases hcover m with hm | ⟨σ'', hσ'', hle⟩
  · rw [← hi.image_diamant hS hcover hDac hDext hm (hK m hm)]
    exact image_subset_range _ _
  · rintro q ⟨⟨_, ⟨σ, hσ, rfl⟩, hσq⟩, hqm⟩
    rw [Precausality.mem_Jminus_singleton] at hqm
    have h1 : D.le ⊤ (i m) (i σ'') := hi.isEMorphism.map_le ⊤ ⊤ le_rfl (fun _ _ => trivial) hle
    have hacausal : D.IsAcausal (i '' S) :=
      (hi.isCauchySurface_image hS).isAcausal hDac hDext
    have heqσ : i σ = i σ'' := hacausal (i σ) ⟨σ, hσ, rfl⟩ (i σ'') ⟨σ'', hσ'', rfl⟩
      (D.le_trans hσq (D.le_trans hqm h1))
    have : q = i m := hi.globallyHyperbolic_target.1 hqm (D.le_trans h1 (heqσ ▸ hσq))
    exact ⟨m, this.symm⟩

/-! ### `lem:passe_pgcd` -/

/-- `lem:passe_pgcd`, the inclusion `K⁻_N(p) ∩ J⁺(i S) ⊆ i(M)`, for every `p` in the closure of
`i(M)` (the paper takes `p ∈ ∂ i(M) ∩ J⁺(i S)`; neither half is used). The hypotheses are those of
`image_diamant` at every point of `J⁺(S)`, and first countability of `N` for the sequence. -/
theorem IsCauchyEmbedding.passe_pgcd [T2Space N] [FirstCountableTopology N]
    (hi : IsCauchyEmbedding C D i) {S : Set M} (hS : C.IsCauchySurface S)
    (hcover : ∀ x, x ∈ C.Jplus ⊤ S ∪ C.Jminus ⊤ S) (hDac : D.CausallyArcConnected)
    (hDext : D.CurvesExtend) (hK : ∀ m ∈ C.Jplus ⊤ S, IsCompact (C.Jplus ⊤ S ∩ C.Jminus ⊤ {m}))
    {p : N} (hp : p ∈ closure (range i)) :
    D.Kminus ⊤ {p} ∩ D.Jplus ⊤ (i '' S) ⊆ range i := by
  rintro q ⟨hqK, hqJ⟩
  obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.1 hp
  rw [Causality.mem_Kminus_singleton] at hqK
  obtain ⟨N₀, hN₀⟩ := hqK u hlim
  have hq : q ∈ D.Jminus ⊤ {u N₀} := mem_iInter₂.1 (interiorWithin_subset hN₀).2 N₀ le_rfl
  obtain ⟨m, hm⟩ := hu N₀
  rw [← hm] at hq
  exact hi.diamond_subset_range hS hcover hDac hDext hK m ⟨hqJ, hq⟩

/-- **The two explicit forms of `lem:passe_pgcd`**, with the facts of `prop:K_calcul` about the
singular set `sing₀(N)` carried as named hypotheses on a set `Sing` (kb/0012): `K⁻(q) = I⁻(q)` off
`Sing`, `K⁻(q) = J⁻(q) ∖ {q}` on it. -/
theorem IsCauchyEmbedding.passe_pgcd_explicit [T2Space N] [FirstCountableTopology N]
    (hi : IsCauchyEmbedding C D i) {S : Set M} (hS : C.IsCauchySurface S)
    (hcover : ∀ x, x ∈ C.Jplus ⊤ S ∪ C.Jminus ⊤ S) (hDac : D.CausallyArcConnected)
    (hDext : D.CurvesExtend) (hK : ∀ m ∈ C.Jplus ⊤ S, IsCompact (C.Jplus ⊤ S ∩ C.Jminus ⊤ {m}))
    (Sing : Set N) (hreg : ∀ q ∉ Sing, D.Kminus ⊤ {q} = D.Iminus ⊤ {q})
    (hsing : ∀ q ∈ Sing, D.Kminus ⊤ {q} = D.Jminus ⊤ {q} \ {q})
    {p : N} (hp : p ∈ closure (range i)) :
    (p ∉ Sing → D.Iminus ⊤ {p} ∩ D.Jplus ⊤ (i '' S) ⊆ range i) ∧
      (p ∈ Sing → (D.Jplus ⊤ (i '' S) ∩ D.Jminus ⊤ {p}) \ {p} ⊆ range i) := by
  have h := hi.passe_pgcd hS hcover hDac hDext hK hp
  refine ⟨fun hpS => ?_, fun hpS => ?_⟩
  · rw [← hreg p hpS]; exact h
  · rintro q ⟨⟨hqJ, hqp⟩, hqne⟩
    refine h ⟨?_, hqJ⟩
    rw [hsing p hpS]
    exact ⟨hqp, hqne⟩

/-! ### Witnesses: the timelike line satisfies the named hypotheses jointly (`Sing = ∅`) -/

/-- The splitting of the timelike line along `{0}`: `ψ(0, t) = t`. -/
def timelikeLineSplitting : ({0} : Set ℝ) × ℝ ≃ₜ ℝ := Homeomorph.uniqueProd _ ℝ

theorem timelikeLine_isCauchySplitting :
    Causality.IsCauchySplitting timelikeLine {0} timelikeLineSplitting where
  zero x := by
    show (0 : ℝ) = x
    exact x.2.symm
  mono _ _ _ hst := ⟨hst, fun _ _ => trivial⟩

theorem timelikeLine_isAcausal_zero : timelikeLine.IsAcausal {0} := by
  rintro x rfl y rfl _; rfl

theorem timelikeLine_Jplus_zero_inter (m : ℝ) :
    timelikeLine.Jplus ⊤ {0} ∩ timelikeLine.Jminus ⊤ {m} = Icc 0 m := by
  ext x
  simp [Precausality.mem_Jplus_singleton, Precausality.mem_Jminus_singleton]

/-- **The hypotheses of `lem:Sigma_separe`, `image_diamant` and `passe_pgcd` are jointly
satisfiable**: on the timelike line with `S = {0}`, `i = id`, `Sing = ∅`. (The hypothesis on `p`
of `passe_pgcd` is met only by points of `range id = ℝ`, so its conclusion is trivial there.) -/
theorem timelikeLine_cauchy_diamond_hypotheses :
    Causality.IsCauchySplitting timelikeLine {0} timelikeLineSplitting ∧
      timelikeLine.IsAcausal {0} ∧ timelikeLine.IsCauchySurface {0} ∧
      (∀ x, x ∈ timelikeLine.Jplus ⊤ {0} ∪ timelikeLine.Jminus ⊤ {0}) ∧
      timelikeLine.CausallyArcConnected ∧ timelikeLine.CurvesExtend ∧
      (∀ m ∈ timelikeLine.Jplus ⊤ {0},
        IsCompact (timelikeLine.Jplus ⊤ {0} ∩ timelikeLine.Jminus ⊤ {m})) ∧
      (∀ q ∉ (∅ : Set ℝ), timelikeLine.Kminus ⊤ {q} = timelikeLine.Iminus ⊤ {q}) :=
  ⟨timelikeLine_isCauchySplitting, timelikeLine_isAcausal_zero,
    timelikeLine_isCauchySurface_zero, timelikeLine_isCauchySplitting.cover,
    timelikeLine_causallyArcConnected, timelikeLine_curvesExtend,
    fun m _ => by rw [timelikeLine_Jplus_zero_inter]; exact isCompact_Icc,
    fun q _ => timelikeLine_pushUp.Kminus_eq_Iminus fun U hU => by
      obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hU
      refine ⟨q - ε / 2, ?_, hball ?_⟩
      · rw [Precausality.mem_Iminus_singleton]
        exact ⟨by linarith, fun _ _ => trivial⟩
      · rw [Metric.mem_ball, Real.dist_eq, abs_of_neg (by linarith)]; linarith⟩

end Causal
