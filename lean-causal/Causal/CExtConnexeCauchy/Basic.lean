import Causal.CExtConnexeCauchy.SubArc
import Causal.CExtConnexeSecondCountable

/-!
# `lem:C_ext_connexe`'s middle step on a Hausdorff, second countable `N`: `φ(Σ)` is Cauchy in `A ∩ B`

Programme target `T-abs-c-ext-connexe-cauchy` (`programme/roadmap.toml`; layer 1: it imports
`Causal.CExtConnexeCauchy.SubArc` and `Causal.CExtConnexeSecondCountable`, ETT-layer; no
model; no metric notion in a statement). The label served, **not marked** (SCOPE):
`lem:C_ext_connexe` — `ETT.tex:1932`.

> Let $M$ be a connected globally hyperbolic singular flat spacetime and let
> $\phi:M\rightarrow N$ be a Cauchy extension. If $A$ and $B$ are open subsets of $N$ containing
> $\phi(M)$ and such that the inclusions $\phi(M)\rightarrow A$ and $\phi(M)\rightarrow B$ are
> Cauchy embeddings, then $A\cap B$ is connected. (`ETT.tex:1933–1936`)

> Let $\Sigma$ be a Cauchy surface of $M$; it is connected because $M$ is, being homeomorphic to
> $\Sigma\times \RR$ by Theorem \ref{theo:geroch_sing}. The map $M\rightarrow A\cap B$ is a Cauchy
> embedding, so $\phi(\Sigma)$ is a Cauchy surface of $A\cap B$ and every point of $A\cap B$ lies on
> an inextensible causal curve meeting $\phi(\Sigma)$. Hence $A\cap B$ is arcwise connected.
> (`ETT.tex:1939–1943`)

> A topological spacetime is a second countable Hausdorff topological space endowed with a
> causality. (`ETT.tex:255`)

## What is proved (no `sorry`)

1. **The middle step, abstractly** (`Causality.exists_mem_inf_of_isCauchySurfaceOn`): in a causal,
   Hausdorff, second countable spacetime, a Cauchy surface `T` of `M` that is a Cauchy surface of
   the open sets `A` and `B` meets every inextensible causal curve of `A ∩ B`; so it is a Cauchy
   surface of `A ∩ B` (`Causality.isCauchySurfaceOn_inf_of_secondCountable`). The argument is the
   target's (b)–(d), an end-point argument the paper does not give (ETT.tex:1940–1941 asserts the
   step):
   * trim the curve `c` of `A ∩ B` (`exists_tailFree_retraction`); it stays inextensible
     (`Inextensible.of_retraction`);
   * `c` is a reparametrised sub-arc of inextensible curves `γ_A` of `A`, `γ_B` of `B`
     (`exists_subArc_of_tailFree`), which meet `T` at `s_A`, `s_B`;
   * if `s_A` (or `s_B`) is a parameter of `c`, done; if `γ_A` meets `T` after `c` and `γ_B`
     before, a segment of `γ_B` followed by one of `γ_A` is a causal curve of `M` meeting `T` twice
     unless it meets it on `c` (`mem_of_le_of_le_of_subsingleton`, `M` causal);
   * if both meet `T` after `c` (`Inextensible.mem_image_or_tendsto_of_above`): either `γ_A` meets
     `T` at a value of `c`, or `c` has no last parameter and a limit `p_A ∈ A ∖ (A ∩ B)` at its
     future end. A last value `c(t₁)` is left by `γ_A` inside `A ∩ B` at a new value unless `γ_A`
     meets `T` at it; a limit in `A ∩ B` extends `c`; both contradict inextensibility
     (`Inextensible.image_subset_of_subArc`). The two limits `p_A ∈ A ∖ B`, `p_B ∈ B ∖ A` are
     equal (Hausdorff): a contradiction. Before, by time reversal
     (`Inextensible.mem_image_or_tendsto_of_below`).
2. **`lem:C_ext_connexe`'s middle step**: `IsCauchyEmbedding.exists_mem_image_inf_of_secondCountable`
   is the scaffold's `IsCauchyEmbedding.exists_mem_image_inf` with `[SecondCountableTopology N]`
   added, `IsCauchyEmbedding.isCauchySurfaceOn_inf_of_secondCountable` the scaffold's
   `isCauchySurfaceOn_inf` without `hDac` and `hDext`: `φ(Σ)` is a Cauchy surface of `A ∩ B`. With
   `N` causally arc-connected, the inclusion `φ(M) → A ∩ B` is a Cauchy inclusion
   (`IsCauchyEmbedding.isCauchyInclusion_inf_of_secondCountable`): "the map `M → A ∩ B` is a
   Cauchy embedding" in full.
3. **`lem:C_ext_connexe` by the paper's route** (`IsCauchyEmbedding.c_ext_connexe_of_secondCountable`,
   the scaffold's `IsCauchyEmbedding.c_ext_connexe` without `hDac`, `hDext`, `hthrough`): `M`
   connected with the splitting `ψ`, and `A ∩ B` connected through "`φ(Σ)` is a Cauchy surface of
   `A ∩ B`" and "every point of `A ∩ B` lies on an inextensible causal curve meeting `φ(Σ)`".
4. **Witness** (kb/0011, kb/0222): `gateArc : ℝ → ]-1, 1[`, a Cauchy embedding of the timelike
   line that is not onto, with `A = φ(ℝ)`, `B = ℝ` (`timelikeLine_gateArc_cauchy_inf`).

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| singular flat spacetimes, `𝕄≥0`-morphisms | ⚠ weakened (a reading, OQ-94): any causality on a topological space, `IsEMorphism` (`Causal/SubExtension.lean:43`) |
| — second countable Hausdorff (`ETT.tex:255`) | ✓ carried on `N`: `[T2Space N] [SecondCountableTopology N]`; nothing on `M` |
| `M` globally hyperbolic, `φ` a Cauchy extension | ✓ carried (`IsCauchyEmbedding`, DEC-17) |
| `A, B` open, `φ(M) → A`, `φ(M) → B` Cauchy embeddings | ✓ carried (`IsCauchyInclusion`) |
| `M` connected | ✓ carried by `c_ext_connexe_of_secondCountable`; ⚠ weakened: not used by the middle step |
| `Σ` connected through `theo:geroch_sing` | ⚠ strengthened: the splitting `ψ` named in `c_ext_connexe_of_secondCountable` (as in the scaffold form); not used by the middle step |
| "the map `M → A ∩ B` is a Cauchy embedding" (asserted) | ✓ proved: the Cauchy surface with no further hypothesis; the global hyperbolicity of `A ∩ B` with `N` causally arc-connected (⚠ strengthened, `isCauchyInclusion_inf_of_secondCountable` only) |
| (scaffold forms) `hDac`, `hDext`, `hthrough` | ⚠ weakened: not used (`hDac` only for the Cauchy inclusion) |
| (abstract form) `T` Cauchy in `M`, `A`, `B`; `M` causal | ✓ the setting of `exists_mem_inf_of_isCauchySurfaceOn`; `φ(Σ)` is Cauchy in `N` by `lem:Cauchy_plongement_toutes` |

## SCOPE (disclosed)

* **Nothing marked.** The forms are in the abstract setting (any causality, `IsEMorphism`); whether
  it may anchor `lem:C_ext_connexe` is OQ-94, open. If it may, the middle sentence of the proof
  (`ETT.tex:1940–1941`) is proved by `IsCauchyEmbedding.isCauchySurfaceOn_inf_of_secondCountable`
  and the paper's whole route by `IsCauchyEmbedding.c_ext_connexe_of_secondCountable`; the
  lemma's statement already has the hypothesis-free `c_ext_connexe_of_connectedSpace_of_secondCountable`
  (`Causal.CExtConnexeSecondCountable`).
* **The scaffold `sorry` stays.** `CausalScaffold.SubExtension`'s `exists_mem_image_inf` is posed
  without second countability; its truth there is not decided here (the curves theorem needs
  second countability, `Causal.CurvesExtendSecondCountable`, SCOPE: the long ray). Its retirement
  or restatement is the master's.
* **Global hyperbolicity of `A ∩ B`** (part of "`M → A ∩ B` is a Cauchy embedding") is taken from
  `inf_causallyConvexIn_of_secondCountable`, which asks `N` causally arc-connected; without it,
  whether the diamonds of `A ∩ B` are compact is not decided here.
* **The witness** has `A ⊆ B` (`A = ]-1, 1[`, `B = ℝ`); a pair of incomparable Cauchy-including
  open sets is not formalized.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set Filter Topology Function TopologicalSpace

universe u v

/-! ## 1. The middle step, abstractly -/

/-- A point outside an ordconnected set of reals lies above all of it or below all of it. -/
theorem forall_lt_or_forall_gt_of_notMem {P : Set ℝ} (hP : P.OrdConnected) {s : ℝ}
    (hs : s ∉ P) : (∀ x ∈ P, x < s) ∨ ∀ x ∈ P, s < x := by
  by_contra h
  push Not at h
  obtain ⟨⟨x, hx, hxs⟩, ⟨y, hy, hys⟩⟩ := h
  exact hs (hP.out hy hx ⟨hys, hxs⟩)

/-- An ordconnected set with a greatest point `e`, followed by `[e, u]`, is ordconnected. -/
theorem ordConnected_union_Icc_of_isGreatest {P : Set ℝ} (hP : P.OrdConnected) {e u : ℝ}
    (he : e ∈ P) (hle : ∀ x ∈ P, x ≤ e) : (P ∪ Icc e u).OrdConnected := by
  refine ⟨fun x hx y hy z hz => ?_⟩
  rcases le_or_gt z e with hze | hze
  · rcases hx with hx | hx
    · exact Or.inl (hP.out hx he ⟨hz.1, hze⟩)
    · left
      rw [le_antisymm hze (hx.1.trans hz.1)]
      exact he
  · rcases hy with hy | hy
    · exact absurd (hz.2.trans (hle y hy)) (not_le.2 hze)
    · exact Or.inr ⟨hze.le, hz.2.trans hy.2⟩

/-- An ordconnected set bounded above, with its supremum added, is ordconnected. -/
theorem ordConnected_union_csSup {P : Set ℝ} (hP : P.OrdConnected) (hne : P.Nonempty)
    (hbdd : BddAbove P) : (P ∪ {sSup P}).OrdConnected := by
  have hy_le : ∀ y ∈ P ∪ {sSup P}, y ≤ sSup P := by
    rintro y (hy | hy)
    · exact le_csSup hbdd hy
    · rw [mem_singleton_iff] at hy; rw [hy]
  refine ⟨fun x hx y hy z hz => ?_⟩
  rcases hz.2.lt_or_eq with hzy | hzy
  · obtain ⟨w, hw, hzw⟩ := exists_lt_of_lt_csSup hne (hzy.trans_le (hy_le y hy))
    rcases hx with hx | hx
    · exact Or.inl (hP.out hx hw ⟨hz.1, hzw.le⟩)
    · rw [mem_singleton_iff] at hx
      exact absurd (hzy.trans_le (hy_le y hy)) (not_lt.2 (hx ▸ hz.1))
  · rw [hzy]; exact hy

namespace Causality

variable {M : Type u} [TopologicalSpace M] {C : Causality M}

/-- **An inextensible curve does not grow along a sub-arc relation**: if `c` is inextensible in
`W ≤ A` and `c = γ ∘ ψ` on `I` for a causal curve `γ` of `A`, every ordconnected `K` between
`ψ(I)` and the interval of `γ` on which `γ` stays in `W` has `γ(K) ⊆ c(I)`: otherwise `(K, γ)`
strictly extends `c` in `W`. -/
theorem Inextensible.image_subset_of_subArc {W A : Opens M} (hWA : W ≤ A) {I : Set ℝ}
    {c : ℝ → M} (hc : C.Inextensible W I c) {J K : Set ℝ} {γ : ℝ → M} {ψ : ℝ → ℝ}
    (hγ : C.CausalCurveIn A J γ) (hψ : StrictMonoOn ψ I) (hψo : (ψ '' I).OrdConnected)
    (heq : ∀ t ∈ I, γ (ψ t) = c t) (hK : K.OrdConnected) (hIK : ψ '' I ⊆ K) (hKJ : K ⊆ J)
    (hKW : γ '' K ⊆ W) : γ '' K ⊆ c '' I := by
  rintro _ ⟨k, hk, rfl⟩
  by_contra hnot
  apply hc.2
  obtain ⟨t₀, ht₀⟩ := hc.1.nonempty
  refine ⟨K, γ, ⟨⟨ψ t₀, hIK ⟨t₀, ht₀, rfl⟩⟩, hK, fun x hx y hy => ?_⟩,
    ⟨ψ, hψ, fun t ht => hIK ⟨t, ht, rfl⟩, hψo, heq⟩, ⟨k, hk, fun t ht h => hnot ⟨t, ht, h.symm⟩⟩⟩
  exact CurveOn.restrict (hγ.curve x (hKJ hx) y (hKJ hy)) le_rfl le_rfl hWA
    fun t ht => hKW ⟨t, hK.out hx hy ht, rfl⟩

/-- **The end-point step, future end**: `c` tail-free and inextensible in `W ≤ A`, `c = γ ∘ ψ`
for a causal curve `γ` of `A` (`≤_A` antisymmetric), and `s` a parameter of `γ` after `ψ(I)`.
Either `γ(s)` is a value of `c`, or `c` converges at its future end to a point of `A` outside
`W`. -/
theorem Inextensible.mem_image_or_tendsto_of_above [T1Space M] {W A : Opens M} (hWA : W ≤ A)
    (hanti : ∀ ⦃x y : M⦄, C.le A x y → C.le A y x → x = y) {I : Set ℝ} {c : ℝ → M}
    (hc : C.Inextensible W I c) (htf : TailFree I c) {J : Set ℝ} {γ : ℝ → M} {ψ : ℝ → ℝ}
    (hγ : C.CausalCurveIn A J γ) (hψ : StrictMonoOn ψ I) (hψm : MapsTo ψ I J)
    (hψo : (ψ '' I).OrdConnected) (heq : ∀ t ∈ I, γ (ψ t) = c t) {s : ℝ} (hs : s ∈ J)
    (habove : ∀ t ∈ I, ψ t < s) :
    γ s ∈ c '' I ∨
      ∃ p ∈ (A : Set M), p ∉ W ∧ ∀ O ∈ 𝓝 p, ∃ t₀ ∈ I, ∀ t ∈ I, t₀ ≤ t → c t ∈ O := by
  obtain ⟨t₀, ht₀⟩ := hc.1.nonempty
  have hPne : (ψ '' I).Nonempty := ⟨ψ t₀, t₀, ht₀, rfl⟩
  have hPbdd : BddAbove (ψ '' I) := ⟨s, by rintro _ ⟨t, ht, rfl⟩; exact (habove t ht).le⟩
  have hle_e : ∀ t ∈ I, ψ t ≤ sSup (ψ '' I) := fun t ht => le_csSup hPbdd ⟨t, ht, rfl⟩
  have he_s : sSup (ψ '' I) ≤ s :=
    csSup_le hPne (by rintro _ ⟨t, ht, rfl⟩; exact (habove t ht).le)
  have heJ : sSup (ψ '' I) ∈ J := hγ.ordConnected.out (hψm ht₀) hs ⟨hle_e t₀ ht₀, he_s⟩
  have hle : ∀ x ∈ J, ∀ y ∈ J, x ≤ y → C.le A (γ x) (γ y) := fun x hx y hy h =>
    hγ.le_of_le hx hy h
  have hcW : ∀ t ∈ I, c t ∈ W := fun t ht => hc.1.mem ht
  by_cases heP : sSup (ψ '' I) ∈ ψ '' I
  · -- `c` has a last parameter `t₁`, and a last value `p`
    left
    obtain ⟨t₁, ht₁, he₁⟩ := heP
    have hcont : ContinuousOn γ (Icc (sSup (ψ '' I)) s) := hγ.continuousOn_Icc heJ hs
    set e := sSup (ψ '' I) with he
    set p := γ e with hp
    have hpc : p = c t₁ := by rw [hp, ← he₁, heq t₁ ht₁]
    have hpW : p ∈ W := by rw [hpc]; exact hcW t₁ ht₁
    set Z := Icc e s ∩ γ ⁻¹' {p} with hZ
    have hZc : IsClosed Z :=
      hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
    have hZne : Z.Nonempty := ⟨e, ⟨le_rfl, he_s⟩, rfl⟩
    have hZbdd : BddAbove Z := ⟨s, fun x hx => hx.1.2⟩
    have he'Z : sSup Z ∈ Z := hZc.csSup_mem hZne hZbdd
    have hZle : ∀ x ∈ Z, x ≤ sSup Z := fun x hx => le_csSup hZbdd hx
    set e' := sSup Z with he'
    have he'J : e' ∈ J := hγ.ordConnected.out heJ hs he'Z.1
    have hγe' : γ e' = p := he'Z.2
    rcases he'Z.1.2.lt_or_eq with hlt | heqs
    · exfalso
      -- a short piece after `e'` stays in `W`
      have hpre : γ ⁻¹' W ∈ 𝓝[Icc e s] e' :=
        hcont e' he'Z.1 (W.isOpen.mem_nhds (by rw [hγe']; exact hpW))
      obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.1 hpre
      have he'u : e' < min (e' + ε / 2) s := lt_min (by linarith) hlt
      have hus : min (e' + ε / 2) s ≤ s := min_le_right _ _
      have hue : min (e' + ε / 2) s ≤ e' + ε / 2 := min_le_left _ _
      set u := min (e' + ε / 2) s with hu
      have huJ : u ∈ J := hγ.ordConnected.out heJ hs ⟨he'Z.1.1.trans he'u.le, hus⟩
      have hpiece : ∀ v ∈ Icc e' u, γ v ∈ W := fun v hv => hball ⟨by
        rw [Metric.mem_ball, Real.dist_eq, abs_lt]
        constructor <;> linarith [hv.1, hv.2], he'Z.1.1.trans hv.1, hv.2.trans hus⟩
      -- `γ` stays at `p` on `[e, e']`
      have hconst : ∀ v ∈ Icc e e', γ v = p := fun v hv => by
        have hvJ : v ∈ J := hγ.ordConnected.out heJ he'J hv
        have h1 : C.le A (γ v) (γ e') := hle v hvJ e' he'J hv.2
        rw [hγe'] at h1
        exact hanti h1 (hle e heJ v hvJ hv.1)
      -- the value at `u` is new
      have hnew : γ u ∉ c '' I := by
        rintro ⟨t, ht, htu⟩
        have h1 : C.le A (γ (ψ t)) (γ e') :=
          hle _ (hψm ht) e' he'J ((hle_e t ht).trans he'Z.1.1)
        have h2 : C.le A (γ e') (γ u) := hle e' he'J u huJ he'u.le
        rw [heq t ht, htu] at h1
        have h3 : γ u = p := by rw [← hγe']; exact hanti h1 h2
        exact absurd (hZle u ⟨⟨he'Z.1.1.trans he'u.le, hus⟩, h3⟩) (not_le.2 he'u)
      apply hnew
      refine hc.image_subset_of_subArc hWA hγ hψ hψo heq
        (ordConnected_union_Icc_of_isGreatest hψo ⟨t₁, ht₁, he₁⟩ fun x hx => ?_)
        subset_union_left ?_ ?_ ⟨u, Or.inr ⟨he'Z.1.1.trans he'u.le, le_rfl⟩, rfl⟩
      · obtain ⟨t, ht, rfl⟩ := hx; exact hle_e t ht
      · rintro x (hx | hx)
        · obtain ⟨t, ht, rfl⟩ := hx; exact hψm ht
        · exact hγ.ordConnected.out heJ huJ hx
      · rintro _ ⟨x, hx | hx, rfl⟩
        · obtain ⟨t, ht, rfl⟩ := hx; rw [heq t ht]; exact hcW t ht
        · rcases le_total x e' with h | h
          · rw [hconst x ⟨hx.1, h⟩]; exact hpW
          · exact hpiece x ⟨h, hx.2⟩
    · -- `γ` meets `T`-side parameter `s` at the last value
      rw [heqs] at hγe'
      exact ⟨t₁, ht₁, by rw [← hpc]; exact hγe'.symm⟩
  · -- no last parameter: the limit `γ e` is outside `W`
    have hlt_e : ∀ t ∈ I, ψ t < sSup (ψ '' I) := fun t ht =>
      lt_of_le_of_ne (hle_e t ht) fun h => heP ⟨t, ht, h⟩
    have hnomax : ∀ t ∈ I, ∃ t' ∈ I, t < t' := fun t ht => by
      obtain ⟨_, ⟨t', ht', rfl⟩, hlt⟩ := exists_lt_of_lt_csSup hPne (hlt_e t ht)
      exact ⟨t', ht', (hψ.lt_iff_lt ht ht').1 hlt⟩
    right
    refine ⟨γ (sSup (ψ '' I)), hγ.mem heJ, fun hpW => ?_, fun O hO => ?_⟩
    · obtain ⟨t, ht, hte⟩ := hc.image_subset_of_subArc hWA hγ hψ hψo heq
        (ordConnected_union_csSup hψo hPne hPbdd) subset_union_left
        (by
          rintro x (hx | hx)
          · obtain ⟨t, ht, rfl⟩ := hx; exact hψm ht
          · rw [mem_singleton_iff] at hx; rw [hx]; exact heJ)
        (by
          rintro _ ⟨x, hx | hx, rfl⟩
          · obtain ⟨t, ht, rfl⟩ := hx; rw [heq t ht]; exact hcW t ht
          · rw [mem_singleton_iff] at hx; rw [hx]; exact hpW)
        ⟨sSup (ψ '' I), Or.inr rfl, rfl⟩
      obtain ⟨t', ht', htt'⟩ := hnomax t ht
      obtain ⟨s', hs', hts', hne⟩ := htf.1 t ht t' ht' htt'
      apply hne
      have h1 : C.le A (γ (ψ t)) (γ (ψ s')) :=
        hle _ (hψm ht) _ (hψm hs') (hψ.monotoneOn ht hs' hts')
      have h2 : C.le A (γ (ψ s')) (γ (sSup (ψ '' I))) := hle _ (hψm hs') _ heJ (hle_e s' hs')
      rw [heq t ht, heq s' hs'] at h1
      rw [heq s' hs', ← hte] at h2
      exact hanti h2 h1
    · have hcont : ContinuousOn γ (Icc (ψ t₀) (sSup (ψ '' I))) :=
        hγ.continuousOn_Icc (hψm ht₀) heJ
      have hpre : γ ⁻¹' O ∈ 𝓝[Icc (ψ t₀) (sSup (ψ '' I))] sSup (ψ '' I) :=
        hcont _ ⟨hle_e t₀ ht₀, le_rfl⟩ hO
      obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.1 hpre
      obtain ⟨_, ⟨t₁, ht₁, rfl⟩, hlt⟩ := exists_lt_of_lt_csSup hPne
        (show max (ψ t₀) (sSup (ψ '' I) - ε / 2) < sSup (ψ '' I) from
          max_lt (hlt_e t₀ ht₀) (by linarith))
      refine ⟨t₁, ht₁, fun t ht htt => ?_⟩
      have h1 : ψ t₁ ≤ ψ t := hψ.monotoneOn ht₁ ht htt
      have h2 : ψ t ≤ sSup (ψ '' I) := hle_e t ht
      have h3 := le_max_left (ψ t₀) (sSup (ψ '' I) - ε / 2)
      have h4 := le_max_right (ψ t₀) (sSup (ψ '' I) - ε / 2)
      rw [← heq t ht]
      exact hball ⟨by
        rw [Metric.mem_ball, Real.dist_eq, abs_lt]
        constructor <;> linarith, by linarith, h2⟩

/-- **The end-point step, past end**: `mem_image_or_tendsto_of_above` through time reversal. -/
theorem Inextensible.mem_image_or_tendsto_of_below [T1Space M] {W A : Opens M} (hWA : W ≤ A)
    (hanti : ∀ ⦃x y : M⦄, C.le A x y → C.le A y x → x = y) {I : Set ℝ} {c : ℝ → M}
    (hc : C.Inextensible W I c) (htf : TailFree I c) {J : Set ℝ} {γ : ℝ → M} {ψ : ℝ → ℝ}
    (hγ : C.CausalCurveIn A J γ) (hψ : StrictMonoOn ψ I) (hψm : MapsTo ψ I J)
    (hψo : (ψ '' I).OrdConnected) (heq : ∀ t ∈ I, γ (ψ t) = c t) {s : ℝ} (hs : s ∈ J)
    (hbelow : ∀ t ∈ I, s < ψ t) :
    γ s ∈ c '' I ∨
      ∃ p ∈ (A : Set M), p ∉ W ∧ ∀ O ∈ 𝓝 p, ∃ t₀ ∈ I, ∀ t ∈ I, t ≤ t₀ → c t ∈ O := by
  have h := Inextensible.mem_image_or_tendsto_of_above (C := C.dual) (I := -I)
    (c := fun t => c (-t)) (J := -J) (γ := fun u => γ (-u)) (ψ := fun t => -ψ (-t)) (s := -s)
    hWA (fun x y h1 h2 => hanti h2 h1) hc.dual_reverse htf.neg hγ.reverse
    (fun x hx y hy hxy => neg_lt_neg (hψ hy hx (neg_lt_neg hxy)))
    (fun t ht => show -(-ψ (-t)) ∈ J by rw [neg_neg]; exact hψm ht)
    (ordConnected_image_neg hψo) (fun t ht => by simp only [neg_neg]; exact heq (-t) ht)
    (show -(-s) ∈ J by rw [neg_neg]; exact hs) (fun t ht => neg_lt_neg (hbelow (-t) ht))
  rcases h with ⟨t, ht, hts⟩ | ⟨p, hpA, hpW, hlim⟩
  · exact Or.inl ⟨-t, ht, by simpa using hts⟩
  · refine Or.inr ⟨p, hpA, hpW, fun O hO => ?_⟩
    obtain ⟨t₀, ht₀, h₀⟩ := hlim O hO
    refine ⟨-t₀, ht₀, fun t ht htt => ?_⟩
    have := h₀ (-t) (show -(-t) ∈ I by rw [neg_neg]; exact ht) (by linarith)
    simpa using this

/-- **Two meetings on opposite sides** (the target's (d)): `γ₁` meets `T` at `s₁` before `u₁`,
`γ₂` meets it at `s₂` after `u₂`, and `γ₁(u₁) = γ₂(u₂)`. A segment of `γ₁` followed by one of
`γ₂` is a causal curve of `M`, which meets `T` at most once, so `γ₁(s₁) = γ₂(s₂)`, and the
common point lies between them: it is in `T` (`M` causal). -/
theorem mem_of_le_of_le_of_subsingleton (hC : C.IsCausal) {T : Set M}
    (hT : ∀ (J : Set ℝ) (d : ℝ → M), C.CausalCurveIn ⊤ J d → (d '' J ∩ T).Subsingleton)
    {A₁ A₂ : Opens M} {J₁ J₂ : Set ℝ} {γ₁ γ₂ : ℝ → M} (hγ₁ : C.CausalCurveIn A₁ J₁ γ₁)
    (hγ₂ : C.CausalCurveIn A₂ J₂ γ₂) {s₁ u₁ u₂ s₂ : ℝ} (hs₁ : s₁ ∈ J₁) (hu₁ : u₁ ∈ J₁)
    (hu₂ : u₂ ∈ J₂) (hs₂ : s₂ ∈ J₂) (h₁ : s₁ ≤ u₁) (h₂ : u₂ ≤ s₂) (hT₁ : γ₁ s₁ ∈ T)
    (hT₂ : γ₂ s₂ ∈ T) (hx : γ₁ u₁ = γ₂ u₂) : γ₁ u₁ ∈ T := by
  have hc₁ : C.CausalCurveOn ⊤ γ₁ s₁ u₁ :=
    CurveOn.mono_opens C.isRelFamily_le (hγ₁.curve s₁ hs₁ u₁ hu₁) le_top
  have hc₂ : C.CausalCurveOn ⊤ γ₂ u₂ s₂ :=
    CurveOn.mono_opens C.isRelFamily_le (hγ₂.curve u₂ hu₂ s₂ hs₂) le_top
  have hd₁ : C.CausalCurveOn ⊤ (fun v => γ₁ (1 * v + u₁)) (s₁ - u₁) 0 := by
    refine CurveOn.comp_affine one_pos ?_
    rw [show 1 * (s₁ - u₁) + u₁ = s₁ by ring, show (1 : ℝ) * 0 + u₁ = u₁ by ring]
    exact hc₁
  have hd₂ : C.CausalCurveOn ⊤ (fun v => γ₂ (1 * v + u₂)) 0 (s₂ - u₂) := by
    refine CurveOn.comp_affine one_pos ?_
    rw [show 1 * (s₂ - u₂) + u₂ = s₂ by ring, show (1 : ℝ) * 0 + u₂ = u₂ by ring]
    exact hc₂
  have hd := CurveOn.concat C.isRelFamily_le hd₁ hd₂ (by linarith) (by linarith)
    (by simp only [mul_zero, zero_add]; exact hx)
  have hdI := CausalCurveOn.causalCurveIn_Icc (C := C) hd (by linarith)
  have hv₁ : (fun t => if t ≤ 0 then (fun v => γ₁ (1 * v + u₁)) t
      else (fun v => γ₂ (1 * v + u₂)) t) (s₁ - u₁) = γ₁ s₁ := by
    simp only [if_pos (show s₁ - u₁ ≤ 0 by linarith)]
    congr 1
    ring
  have hv₂ : (fun t => if t ≤ 0 then (fun v => γ₁ (1 * v + u₁)) t
      else (fun v => γ₂ (1 * v + u₂)) t) (s₂ - u₂) = γ₂ s₂ := by
    by_cases h : s₂ - u₂ ≤ 0
    · have e : s₂ = u₂ := le_antisymm (by linarith) h₂
      simp only [if_pos h]
      rw [e, sub_self, mul_zero, zero_add]
      exact hx
    · simp only [if_neg h]
      congr 1
      ring
  have heq₁₂ : γ₁ s₁ = γ₂ s₂ := hT _ _ hdI ⟨⟨s₁ - u₁, ⟨le_rfl, by linarith⟩, hv₁⟩, hT₁⟩
    ⟨⟨s₂ - u₂, ⟨by linarith, le_rfl⟩, hv₂⟩, hT₂⟩
  have hA : C.le ⊤ (γ₁ s₁) (γ₁ u₁) := hc₁.le_of_le le_rfl h₁ le_rfl
  have hB : C.le ⊤ (γ₁ u₁) (γ₁ s₁) := by
    rw [hx, heq₁₂]; exact hc₂.le_of_le le_rfl h₂ le_rfl
  rw [hC hB hA]
  exact hT₁

/-- **The middle step, abstractly**: in a causal, Hausdorff, second countable spacetime, a Cauchy
surface `T` of `M` that is a Cauchy surface of the open sets `A` and `B` meets every inextensible
causal curve of `A ∩ B`. -/
theorem exists_mem_inf_of_isCauchySurfaceOn [T2Space M] [SecondCountableTopology M]
    (hC : C.IsCausal) {T : Set M} (hT : C.IsCauchySurface T) {A B : Opens M}
    (hTA : C.IsCauchySurfaceOn A T) (hTB : C.IsCauchySurfaceOn B T) {I : Set ℝ} {c : ℝ → M}
    (hc : C.Inextensible (A ⊓ B) I c) : (c '' I ∩ T).Nonempty := by
  -- trim `c`: it stays inextensible
  obtain ⟨I₀, hI₀I, ρ, hne, ho, htf, hρm, hρmono, hρid, hρc, -⟩ :=
    exists_tailFree_retraction hc.1.nonempty hc.1.ordConnected
      (fun a ha b hb => CurveOn.continuousOn C.isRelFamily_le (hc.1.curve a ha b hb))
  have hc₀ : C.Inextensible (A ⊓ B) I₀ c := hc.of_retraction hI₀I hne ho hρm hρmono hρid hρc
  suffices h : (c '' I₀ ∩ T).Nonempty from h.mono (inter_subset_inter_left _ (image_mono hI₀I))
  have hanti : ∀ (U : Opens M) ⦃x y : M⦄, C.le U x y → C.le U y x → x = y := fun _ _ _ h1 h2 =>
    hC (C.le_mono le_top h1) (C.le_mono le_top h2)
  have hsub : ∀ (J : Set ℝ) (d : ℝ → M), C.CausalCurveIn ⊤ J d → (d '' J ∩ T).Subsingleton :=
    fun _ _ hd => inter_subsingleton_of_curvesExtend (curvesExtend_of_t1_secondCountable C)
      hT.inter_subsingleton hd
  -- `c` is a sub-arc of inextensible curves of `A` and of `B`, which meet `T`
  obtain ⟨JA, γA, ψA, hγA, -, hψA, -, hψAm, hψAo, heqA⟩ :=
    exists_subArc_of_tailFree (hc₀.1.mono_opens inf_le_left) htf
  obtain ⟨JB, γB, ψB, hγB, -, hψB, -, hψBm, hψBo, heqB⟩ :=
    exists_subArc_of_tailFree (hc₀.1.mono_opens inf_le_right) htf
  obtain ⟨_, ⟨⟨sA, hsA, rfl⟩, hxA⟩, -⟩ := hTA JA γA hγA
  obtain ⟨_, ⟨⟨sB, hsB, rfl⟩, hxB⟩, -⟩ := hTB JB γB hγB
  -- (b) a meeting at a parameter of `c`
  by_cases hA : sA ∈ ψA '' I₀
  · obtain ⟨t, ht, rfl⟩ := hA
    exact ⟨c t, ⟨t, ht, rfl⟩, heqA t ht ▸ hxA⟩
  by_cases hB : sB ∈ ψB '' I₀
  · obtain ⟨t, ht, rfl⟩ := hB
    exact ⟨c t, ⟨t, ht, rfl⟩, heqB t ht ▸ hxB⟩
  obtain ⟨t₀, ht₀⟩ := hne
  rcases forall_lt_or_forall_gt_of_notMem hψAo hA with hAa | hAb <;>
    rcases forall_lt_or_forall_gt_of_notMem hψBo hB with hBa | hBb
  · -- (c) both meetings after `c`: two future limits, one in `A ∖ B`, one in `B ∖ A`
    rcases hc₀.mem_image_or_tendsto_of_above inf_le_left (hanti A) htf hγA.1 hψA hψAm hψAo heqA
      hsA (fun t ht => hAa _ ⟨t, ht, rfl⟩) with h | ⟨p, hpA, hpW, hlimA⟩
    · exact ⟨γA sA, h, hxA⟩
    rcases hc₀.mem_image_or_tendsto_of_above inf_le_right (hanti B) htf hγB.1 hψB hψBm hψBo heqB
      hsB (fun t ht => hBa _ ⟨t, ht, rfl⟩) with h | ⟨q, hqB, hqW, hlimB⟩
    · exact ⟨γB sB, h, hxB⟩
    exfalso
    have hpq : p = q := by
      by_contra hne'
      obtain ⟨U, V, hU, hV, hpU, hqV, hUV⟩ := t2_separation hne'
      obtain ⟨a₁, ha₁, h₁⟩ := hlimA U (hU.mem_nhds hpU)
      obtain ⟨a₂, ha₂, h₂⟩ := hlimB V (hV.mem_nhds hqV)
      have hm : max a₁ a₂ ∈ I₀ := by
        rcases max_choice a₁ a₂ with h | h <;> rw [h]
        exacts [ha₁, ha₂]
      exact Set.disjoint_left.1 hUV (h₁ _ hm (le_max_left _ _)) (h₂ _ hm (le_max_right _ _))
    exact hpW ⟨hpA, hpq ▸ hqB⟩
  · -- (d) `γ_B` meets `T` before `c`, `γ_A` after it
    refine ⟨c t₀, ⟨t₀, ht₀, rfl⟩, ?_⟩
    have := mem_of_le_of_le_of_subsingleton hC hsub hγB.1 hγA.1 hsB (hψBm ht₀) (hψAm ht₀) hsA
      (hBb _ ⟨t₀, ht₀, rfl⟩).le (hAa _ ⟨t₀, ht₀, rfl⟩).le hxB hxA
      (by rw [heqB t₀ ht₀, heqA t₀ ht₀])
    rwa [heqB t₀ ht₀] at this
  · -- (d) `γ_A` meets `T` before `c`, `γ_B` after it
    refine ⟨c t₀, ⟨t₀, ht₀, rfl⟩, ?_⟩
    have := mem_of_le_of_le_of_subsingleton hC hsub hγA.1 hγB.1 hsA (hψAm ht₀) (hψBm ht₀) hsB
      (hAb _ ⟨t₀, ht₀, rfl⟩).le (hBa _ ⟨t₀, ht₀, rfl⟩).le hxA hxB
      (by rw [heqA t₀ ht₀, heqB t₀ ht₀])
    rwa [heqA t₀ ht₀] at this
  · -- (c) both meetings before `c`: two past limits
    rcases hc₀.mem_image_or_tendsto_of_below inf_le_left (hanti A) htf hγA.1 hψA hψAm hψAo heqA
      hsA (fun t ht => hAb _ ⟨t, ht, rfl⟩) with h | ⟨p, hpA, hpW, hlimA⟩
    · exact ⟨γA sA, h, hxA⟩
    rcases hc₀.mem_image_or_tendsto_of_below inf_le_right (hanti B) htf hγB.1 hψB hψBm hψBo heqB
      hsB (fun t ht => hBb _ ⟨t, ht, rfl⟩) with h | ⟨q, hqB, hqW, hlimB⟩
    · exact ⟨γB sB, h, hxB⟩
    exfalso
    have hpq : p = q := by
      by_contra hne'
      obtain ⟨U, V, hU, hV, hpU, hqV, hUV⟩ := t2_separation hne'
      obtain ⟨a₁, ha₁, h₁⟩ := hlimA U (hU.mem_nhds hpU)
      obtain ⟨a₂, ha₂, h₂⟩ := hlimB V (hV.mem_nhds hqV)
      have hm : min a₁ a₂ ∈ I₀ := by
        rcases min_choice a₁ a₂ with h | h <;> rw [h]
        exacts [ha₁, ha₂]
      exact Set.disjoint_left.1 hUV (h₁ _ hm (min_le_left _ _)) (h₂ _ hm (min_le_right _ _))
    exact hpW ⟨hpA, hpq ▸ hqB⟩

/-- **A Cauchy surface of `M`, of `A` and of `B` is a Cauchy surface of `A ∩ B`**, in a causal,
Hausdorff, second countable spacetime. -/
theorem isCauchySurfaceOn_inf_of_secondCountable [T2Space M] [SecondCountableTopology M]
    (hC : C.IsCausal) {T : Set M} (hT : C.IsCauchySurface T) {A B : Opens M}
    (hTA : C.IsCauchySurfaceOn A T) (hTB : C.IsCauchySurfaceOn B T) :
    C.IsCauchySurfaceOn (A ⊓ B) T :=
  (isCauchySurfaceOn_iff_of_curvesExtend (curvesExtend_of_t1_secondCountable C)
    hT.inter_subsingleton (A ⊓ B)).2 fun _ _ hc =>
      exists_mem_inf_of_isCauchySurfaceOn hC hT hTA hTB hc

end Causality

/-! ## 2. `lem:C_ext_connexe`'s middle step -/

section CExtConnexe

variable {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]
  {C : Causality M} {D : Causality N} {φ : M → N}

/-- **`lem:C_ext_connexe`'s middle step, existence half** (`ETT.tex:1940–1941`): the scaffold's
`IsCauchyEmbedding.exists_mem_image_inf` with `[SecondCountableTopology N]` added. Every
inextensible causal curve of `A ∩ B` meets `φ(Σ)`. -/
theorem IsCauchyEmbedding.exists_mem_image_inf_of_secondCountable [T2Space N]
    [SecondCountableTopology N] (hφ : IsCauchyEmbedding C D φ) {A B : Opens N}
    (hA : IsCauchyInclusion D hφ.rangeOpens A) (hB : IsCauchyInclusion D hφ.rangeOpens B)
    {S : Set M} (hS : C.IsCauchySurface S) {I : Set ℝ} {c : ℝ → N}
    (hc : D.Inextensible (A ⊓ B) I c) : (c '' I ∩ φ '' S).Nonempty :=
  Causality.exists_mem_inf_of_isCauchySurfaceOn hφ.globallyHyperbolic_target.1
    (hφ.isCauchySurface_image hS) (hφ.isCauchySurfaceOn_of_isCauchyInclusion hA hS)
    (hφ.isCauchySurfaceOn_of_isCauchyInclusion hB hS) hc

/-- **"`φ(Σ)` is a Cauchy surface of `A ∩ B`"** (`ETT.tex:1940–1941`), `N` Hausdorff and second
countable: the scaffold's `IsCauchyEmbedding.isCauchySurfaceOn_inf` without `hDac` and
`hDext`. -/
theorem IsCauchyEmbedding.isCauchySurfaceOn_inf_of_secondCountable [T2Space N]
    [SecondCountableTopology N] (hφ : IsCauchyEmbedding C D φ) {A B : Opens N}
    (hA : IsCauchyInclusion D hφ.rangeOpens A) (hB : IsCauchyInclusion D hφ.rangeOpens B)
    {S : Set M} (hS : C.IsCauchySurface S) : D.IsCauchySurfaceOn (A ⊓ B) (φ '' S) :=
  Causality.isCauchySurfaceOn_inf_of_secondCountable hφ.globallyHyperbolic_target.1
    (hφ.isCauchySurface_image hS) (hφ.isCauchySurfaceOn_of_isCauchyInclusion hA hS)
    (hφ.isCauchySurfaceOn_of_isCauchyInclusion hB hS)

/-- **"The map `M → A ∩ B` is a Cauchy embedding"** (`ETT.tex:1940`), with `N` causally
arc-connected (for the global hyperbolicity of `A ∩ B`, `inf_causallyConvexIn_of_secondCountable`):
the inclusion of `φ(M)` into `A ∩ B` is a Cauchy inclusion. -/
theorem IsCauchyEmbedding.isCauchyInclusion_inf_of_secondCountable [T2Space N]
    [SecondCountableTopology N] (hφ : IsCauchyEmbedding C D φ) {A B : Opens N}
    (hA : IsCauchyInclusion D hφ.rangeOpens A) (hB : IsCauchyInclusion D hφ.rangeOpens B)
    (hDac : D.CausallyArcConnected) : IsCauchyInclusion D hφ.rangeOpens (A ⊓ B) := by
  obtain ⟨S, hS, -⟩ := hφ.exists_cauchy
  have hsub : φ '' S ⊆ (hφ.rangeOpens : Set N) := by
    rw [IsCauchyEmbedding.coe_rangeOpens]; exact image_subset_range φ S
  exact ⟨le_inf hA.1 hB.1, hA.2.1, (hφ.inf_causallyConvexIn_of_secondCountable hA hB hDac).2,
    φ '' S, hsub, (hφ.isEMorphism.isCauchySurface_iff hφ.injective S).1 hS,
    hφ.isCauchySurfaceOn_inf_of_secondCountable hA hB hS⟩

/-- **`lem:C_ext_connexe` by the paper's route** (`ETT.tex:1932–1943`): `M` connected with the
splitting `ψ` of `theo:geroch_sing`, `φ` a Cauchy embedding, `A, B` Cauchy-including `φ(M)`, `N`
Hausdorff and second countable; `φ(Σ)` is a Cauchy surface of `A ∩ B` and every point of `A ∩ B`
lies on an inextensible causal curve meeting it, so `A ∩ B` is connected. The scaffold's
`IsCauchyEmbedding.c_ext_connexe` without `hDac`, `hDext`, `hthrough`. Its statement is exactly
that of `IsCauchyEmbedding.c_ext_connexe'_of_secondCountable` (`Causal.CExtConnexeSecondCountable`);
only the proof route, through the middle step, is new here. -/
theorem IsCauchyEmbedding.c_ext_connexe_of_secondCountable [T2Space N] [SecondCountableTopology N]
    [ConnectedSpace M] (hφ : IsCauchyEmbedding C D φ) {A B : Opens N}
    (hA : IsCauchyInclusion D hφ.rangeOpens A) (hB : IsCauchyInclusion D hφ.rangeOpens B)
    {S : Set M} (hS : C.IsCauchySurface S) (ψ : S × ℝ ≃ₜ M) :
    IsConnected ((A ⊓ B : Opens N) : Set N) := by
  refine hφ.c_ext_connexe_of_isCauchySurfaceOn hA hB ψ
    (hφ.isCauchySurfaceOn_inf_of_secondCountable hA hB hS) fun _ hx => ?_
  obtain ⟨I, c, hc, hxc, -⟩ := hφ.exists_inextensible_inf_of_secondCountable hA hB hS hx
  exact ⟨I, c, hc, hxc⟩

end CExtConnexe

/-! ## 3. Witness (kb/0011, kb/0222) -/

/-- **The middle step off the identity**: on the timelike line, `gateArc : ℝ → ]-1, 1[` is a
Cauchy embedding that is not onto; with `A = φ(ℝ)` and `B = ℝ`, `φ({0})` is a Cauchy surface of
`A ∩ B` and the inclusion of `φ(ℝ)` into `A ∩ B` is a Cauchy inclusion. -/
theorem timelikeLine_gateArc_cauchy_inf :
    ∃ hφ : IsCauchyEmbedding timelikeLine timelikeLine gateArc, range gateArc ≠ univ ∧
      timelikeLine.IsCauchySurfaceOn (hφ.rangeOpens ⊓ ⊤) (gateArc '' {0}) ∧
      IsCauchyInclusion timelikeLine hφ.rangeOpens (hφ.rangeOpens ⊓ ⊤) := by
  obtain ⟨hφ, hne, -⟩ := timelikeLine_gateArc_secondCountable
  have hS' : timelikeLine.IsCauchySurface (gateArc '' {0}) := by
    rw [image_singleton]; exact timelikeLine_isCauchySurface_singleton _
  have hCA : timelikeLine.IsCauchySurfaceOn hφ.rangeOpens (gateArc '' {0}) :=
    (hφ.isEMorphism.isCauchySurface_iff hφ.injective {0}).1 timelikeLine_isCauchySurface_zero
  have hsub : gateArc '' {0} ⊆ (hφ.rangeOpens : Set ℝ) := by
    rw [IsCauchyEmbedding.coe_rangeOpens]; exact image_subset_range _ _
  have hA : IsCauchyInclusion timelikeLine hφ.rangeOpens hφ.rangeOpens :=
    ⟨le_rfl, timelikeLine_globallyHyperbolicOn _, timelikeLine_globallyHyperbolicOn _, _, hsub,
      hCA, hCA⟩
  have hB : IsCauchyInclusion timelikeLine hφ.rangeOpens ⊤ :=
    ⟨le_top, timelikeLine_globallyHyperbolicOn _, timelikeLine_globallyHyperbolicOn _, _, hsub,
      hCA, hS'⟩
  exact ⟨hφ, hne,
    hφ.isCauchySurfaceOn_inf_of_secondCountable hA hB timelikeLine_isCauchySurface_zero,
    hφ.isCauchyInclusion_inf_of_secondCountable hA hB timelikeLine_causallyArcConnected⟩

end Causal
