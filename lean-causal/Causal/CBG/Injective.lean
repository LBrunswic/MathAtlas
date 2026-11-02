import Causal.CurvesExtend
import Causal.Splitting

/-!
# A morphism injective on a Cauchy surface is injective (CBG, design §3 step 2)

No label is marked. This is step 2 of `docs/CBG-DESIGN.md` §3 — Sbierski's Lemma 3.3
(`papers/gx/sources/1309.7591`, p. 13), which fills gap (1) of the ETT ledger's
`prop:Cauchy_pgcd` (`ETT.tex:1945`; `CausalScaffold.SubExtension`, "nothing shows φ injective")
and is used by `theo:CBG` (`ETT.tex:1884`); both are cited unmarked: marking ETT labels is the ETT
campaign's (DEC-59, DEC-60). Proved model-free (ETT generality, abstract `IsEMorphism`, DEC-17),
in full, with no `sorry` and no rigidity:

> **Lemma 3.3.** Say $(M,g)$ and $(M',g')$ are two globally hyperbolic spacetimes with Cauchy
> surfaces $\Sigma$ and $\Sigma'$, respectively. Let $\psi : M\to M'$ be an isometric immersion
> such that $\psi|_\Sigma:\Sigma\to\Sigma'$ is a diffeomorphism. Then $\psi$ is an isometric
> embedding.

> Proof. It suffices to show that ψ is injective. [...] Let σ : (c, d) → M denote the
> inextendible timelike geodesic with σ(0) = p [...] By the global hyperbolicity of (M', g'),
> the geodesics ψ ∘ γ and ψ ∘ σ cannot intersect Σ' more than once, which implies that τ0 = τ1.

## What is proved

* **Principal theorem, on an open set** (`Causal.CBG.injOn_of_injOn_cauchy`, kb/0001): `φ` an
  abstract morphism on the open `U ⊆ M` (`IsEMorphismOn`), `M`, `N` Hausdorff, a continuous
  `T : M → ℝ` strictly increasing along `≤_M`, `Σ` a Cauchy surface of `U`, `N` causal. If `φ` is
  injective on `Σ` and `φ(Σ)` is acausal in `N`, then `φ` is injective on `U`. For `U = M`:
  `injective_of_injOn_cauchy`. The open-set form is the one `prop:Cauchy_pgcd` consumes (the
  union of the common developments is an open set of `M₁`).
* **Sbierski's form**: `injective_of_mapsTo_cauchy` (`φ(Σ) ⊆ Σ'`, `Σ'` a Cauchy surface of a
  causal, causally arc-connected `N` with `CurvesExtend`), and `sbierski_lemma_3_3`, the printed
  conclusion: between globally hyperbolic spacetimes, `φ` is a Cauchy embedding
  (`IsCauchyEmbedding`) when `φ(Σ)` is a Cauchy surface.
* **Globally hyperbolic form** (`injective_of_globallyHyperbolic`): `T` is Geroch's time function
  (`geroch_i_imp_ii`), under the hypotheses of `theo:geroch` (i)⇒(ii).
* **Lemmas of general use** (model-free): path lifting along a local homeomorphism
  (`exists_lift`: the lift covers the segment, or a half-open `[a, e)` with no limit at `e`),
  uniqueness of lifts (`IsLiftOn.eqOn`, `eq_of_lift_const`), gluing through a chart
  (`IsLiftOn.extend`); an abstract morphism on `U` is a local homeomorphism there
  (`exists_chart_of_isEMorphismOn`); time reversal of abstract morphisms (`isEMorphismOn_dual`);
  a lift of a causal curve is a causal curve (`causalCurveOn_of_lift`); `φ⁻¹(φ Σ) ∩ U ⊆ Σ`
  (`mem_of_map_mem_image`).
* **Witnesses** (kb/0011): `minkowski_injective_hypotheses` (every hypothesis of the principal
  theorem on `𝐌^{1,d}`, the identity, `{t = 0}`), `minkowski_sbierski_lemma_3_3`;
  `timelikeLine_injective_of_globallyHyperbolic` (every hypothesis of the globally hyperbolic
  form on the timelike line `𝐌^{1,0}`, with the Gaussian measure; on `𝐌^{1,d}` the admissible
  measure rests on the open item `prop:mesure_dieckmann_Lorentz` (`minkowski_exists_measure`),
  so that witness is not used).

## The proof: lifts of curves for geodesics

Let `φ p = φ q`; an inextensible curve `γ` of `U` through `q` (the time function gives one) meets
`Σ` at `z`; by time reversal it runs from `q` to `z` on `[a, b]`. (1) `φ⁻¹(φ Σ) ⊆ Σ`: an
inextensible curve through `x` meets `Σ` at `v`, and `φ x, φ v` are related points of the acausal
`φ(Σ)`, so `φ` is constant along the curve between them and the curve (a lift of a constant) is
constant. (2) Lift `φ ∘ γ` from `p` (unique lifts: `M` Hausdorff). If the lift covers `[a, b]`,
its end lies on `Σ` by (1) and is `z` by injectivity on `Σ`; two lifts agreeing at `b` agree at
`a`. (3) Otherwise the lift `σ` over `[a, e)` has no limit at `e`. It is a causal curve, on an
inextensible curve `κ` parametrised by `T` (`exists_inextensible_of_timeFunction`) meeting `Σ` at
`κ τᵤ`. Were `T ∘ σ < τᵤ` throughout, `σ = κ ∘ (T ∘ σ)` would have a limit. So `κ τᵤ ≤ p` or
`κ τᵤ = σ t`; in both cases acausality of `φ(Σ)` squeezes `φ ∘ γ` to a constant on `[t, b]`, `σ`
is constant on `[t, e)`, and has a limit: a contradiction. Sbierski's step "`ψ ∘ γ` and `ψ ∘ σ`
meet `Σ'` once" is the acausality of `φ(Σ)`; his `σ` (a maximal geodesic, inextendible) is the
maximal lift, inextensible because it has no limit — completed here by `κ`.

## Hypothesis checklist (Sbierski, Lemma 3.3)

| paper hypothesis | here |
|---|---|
| `(M, g)` globally hyperbolic | ⚠ strengthened (abstract setting): `M` Hausdorff with a continuous `T` strictly increasing along `≤_M` carried — incomparable with GH in the abstract framework (GH does not give `T`, `T` does not give GH); compact diamonds never used; `T` is automatic for smooth GH spacetimes, and derived from GH only under the hypotheses of `theo:geroch` (i)⇒(ii) (`injective_of_globallyHyperbolic`); `sbierski_lemma_3_3` carries GH(M) **and** `T` |
| `(M', g')` globally hyperbolic | principal form: `N` Hausdorff and causal (weaker than GH); `sbierski_lemma_3_3`: ⚠ strengthened — carries GH(N) (for its conclusion) **and** `CausallyArcConnected`, `CurvesExtend` of `N` as model facts (kb/0012), as does `injective_of_mapsTo_cauchy` |
| `Σ`, `Σ'` Cauchy surfaces | `Σ` ✓ (of the open `U`); `Σ'` ⚠ weakened to: `φ(Σ)` acausal |
| `ψ` an isometric immersion | ⚠ reading: `IsEMorphismOn` (DEC-17) |
| `ψ|_Σ : Σ → Σ'` a diffeomorphism | ⚠ weakened: injective on `Σ`; onto `Σ'` only for the `IsCauchyEmbedding` conclusion |
| conclusion "isometric embedding" | ✓ injective; `IsCauchyEmbedding` in `sbierski_lemma_3_3` |

## SCOPE (disclosed)

* `T` is carried in place of global hyperbolicity of `M` (an added hypothesis in the abstract
  setting, see the checklist) because step (3) extends a curve over a half-open
  interval: the library's `CurvesExtend` covers segments only, and `T` is also what
  parametrises `κ`. No compactness of diamonds is used.
* Rigidity is not used and not needed: Sbierski uses uniqueness of geodesics only as uniqueness
  of lifts, which a Hausdorff source gives for any local homeomorphism.
* No axiom; `#print axioms injOn_of_injOn_cauchy`: `propext`, `Classical.choice`, `Quot.sound`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Filter Function

universe u v

variable {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]

namespace CBG

/-! ### Lifts of paths along a local homeomorphism -/

/-- `σ` **lifts `c` along `φ` on `[a, s]`**: `σ` is continuous on `[a, s]` and `φ ∘ σ = c` there. -/
def IsLiftOn (φ : M → N) (c : ℝ → N) (a s : ℝ) (σ : ℝ → M) : Prop :=
  ContinuousOn σ (Icc a s) ∧ ∀ t ∈ Icc a s, φ (σ t) = c t

variable {φ : M → N} {c : ℝ → N} {a b s : ℝ} {σ σ' : ℝ → M} {W : Set M}

omit [TopologicalSpace N] in
/-- A lift on `[a, s]` is a lift on every `[a, s']`, `s' ≤ s`. -/
theorem IsLiftOn.mono (h : IsLiftOn φ c a s σ) {s' : ℝ} (hs : s' ≤ s) : IsLiftOn φ c a s' σ :=
  ⟨h.1.mono (Icc_subset_Icc le_rfl hs), fun t ht => h.2 t ⟨ht.1, ht.2.trans hs⟩⟩

omit [TopologicalSpace N] in
/-- **Uniqueness of lifts**: two lifts on `[a, s]` with values in a set `W` on which `φ` is
locally injective (every point of `W` has a neighbourhood on which `φ` is injective), `M`
Hausdorff, agreeing at one point, agree on `[a, s]`. -/
theorem IsLiftOn.eqOn [T2Space M] (hinj : ∀ y ∈ W, ∃ V ∈ 𝓝 y, InjOn φ V)
    (h₁ : IsLiftOn φ c a s σ) (h₂ : IsLiftOn φ c a s σ') (hm₁ : MapsTo σ (Icc a s) W)
    (hm₂ : MapsTo σ' (Icc a s) W) {t₀ : ℝ} (ht₀ : t₀ ∈ Icc a s) (he : σ t₀ = σ' t₀) :
    EqOn σ σ' (Icc a s) := by
  have hp : IsLocallyInjective (W.restrict φ) := isLocallyInjective_iff_nhds.2 fun y => by
    obtain ⟨V, hV, hinjV⟩ := hinj y y.2
    exact ⟨Subtype.val ⁻¹' V, continuous_subtype_val.continuousAt.preimage_mem_nhds hV,
      fun z hz w hw hzw => Subtype.ext (hinjV hz hw hzw)⟩
  haveI : PreconnectedSpace (Icc a s) := isPreconnected_iff_preconnectedSpace.1 isPreconnected_Icc
  have hc₁ := h₁.1.mapsToRestrict hm₁
  have hc₂ := h₂.1.mapsToRestrict hm₂
  have key := (T2Space.isSeparatedMap (W.restrict φ)).eq_of_comp_eq hp hc₁ hc₂
    (funext fun t => by
      simp only [Function.comp, Set.restrict, MapsTo.val_restrict_apply]
      rw [h₁.2 t t.2, h₂.2 t t.2]) ⟨t₀, ht₀⟩ (Subtype.ext he)
  intro t ht
  exact congrArg Subtype.val (congrFun key ⟨t, ht⟩)

omit [TopologicalSpace N] in
/-- **A lift of a constant is constant.** -/
theorem eq_of_lift_const [T2Space M] (hinj : ∀ y ∈ W, ∃ V ∈ 𝓝 y, InjOn φ V) {t r : ℝ}
    (htr : t ≤ r) (hσ : ContinuousOn σ (Icc t r)) (hm : MapsTo σ (Icc t r) W) {y : N}
    (hy : ∀ x ∈ Icc t r, φ (σ x) = y) : σ r = σ t :=
  IsLiftOn.eqOn (c := fun _ => y) hinj ⟨hσ, hy⟩
    ⟨continuousOn_const, fun _ _ => hy t ⟨le_rfl, htr⟩⟩ hm (fun _ _ => hm ⟨le_rfl, htr⟩)
    ⟨le_rfl, htr⟩ rfl ⟨htr, le_rfl⟩

/-- **Extension of a lift through a chart.** A lift on `[a, t₁]` with values in `W` whose end lies
in the source `⊆ W` of a chart `E` of `φ`, and a path staying in the target of `E` on `[t₁, s₂]`,
glue into a lift on `[a, s₂]` with values in `W`: follow `σ`, then `E⁻¹ ∘ c`. -/
theorem IsLiftOn.extend {t₁ : ℝ} (hσ : IsLiftOn φ c a t₁ σ) (hσW : MapsTo σ (Icc a t₁) W)
    (hat : a ≤ t₁) {s₂ : ℝ} (h12 : t₁ ≤ s₂) (E : OpenPartialHomeomorph M N) (hE : φ = E)
    (hEW : E.source ⊆ W) (hsrc : σ t₁ ∈ E.source) (hc : ContinuousOn c (Icc t₁ s₂))
    (htgt : ∀ t ∈ Icc t₁ s₂, c t ∈ E.target) :
    IsLiftOn φ c a s₂ (fun t => if t ≤ t₁ then σ t else E.symm (c t)) ∧
      MapsTo (fun t => if t ≤ t₁ then σ t else E.symm (c t)) (Icc a s₂) W := by
  have hct₁ : E.symm (c t₁) = σ t₁ := by
    rw [← hσ.2 t₁ ⟨hat, le_rfl⟩, hE]; exact E.left_inv hsrc
  refine ⟨⟨?_, fun t ht => ?_⟩, fun t ht => ?_⟩
  · rw [← Icc_union_Icc_eq_Icc hat h12]
    refine ContinuousOn.union_of_isClosed ?_ ?_ isClosed_Icc isClosed_Icc
    · exact hσ.1.congr fun t ht => if_pos ht.2
    · refine (E.continuousOn_symm.comp hc fun t ht => htgt t ht).congr fun t ht => ?_
      by_cases h : t ≤ t₁
      · have : t = t₁ := le_antisymm h ht.1
        subst this; simp only [le_refl, if_true, Function.comp]; exact hct₁.symm
      · simp only [h, if_false, Function.comp]
  · by_cases h : t ≤ t₁
    · simp only [h, if_true]; exact hσ.2 t ⟨ht.1, h⟩
    · simp only [h, if_false]
      rw [hE]; exact E.right_inv (htgt t ⟨(not_le.1 h).le, ht.2⟩)
  · by_cases h : t ≤ t₁
    · simp only [h, if_true]; exact hσW ⟨ht.1, h⟩
    · simp only [h, if_false]
      exact hEW (E.map_target (htgt t ⟨(not_le.1 h).le, ht.2⟩))

/-- **Path lifting along a local homeomorphism**, `M` and `N` Hausdorff. Let `W ⊆ M` be covered by
charts of `φ` with sources in `W`. A path `c` continuous on `[a, b]`, starting at `φ x`, `x ∈ W`,
lifts from `x` into `W` on all of `[a, b]`, or on a half-open `[a, e)`, `a < e ≤ b`, where the
lift has no limit in `W` at `e`. -/
theorem exists_lift [T2Space M] [T2Space N]
    (hφ : ∀ y ∈ W, ∃ E : OpenPartialHomeomorph M N, y ∈ E.source ∧ E.source ⊆ W ∧ φ = E)
    (hab : a ≤ b) (hc : ContinuousOn c (Icc a b)) {x : M} (hxW : x ∈ W) (hx : φ x = c a) :
    (∃ σ, IsLiftOn φ c a b σ ∧ MapsTo σ (Icc a b) W ∧ σ a = x) ∨
      ∃ e ∈ Ioc a b, ∃ σ : ℝ → M, ContinuousOn σ (Ico a e) ∧ MapsTo σ (Ico a e) W ∧ σ a = x ∧
        (∀ t ∈ Ico a e, φ (σ t) = c t) ∧ ¬ ∃ y ∈ W, Tendsto σ (𝓝[<] e) (𝓝 y) := by
  classical
  have hinj : ∀ y ∈ W, ∃ V ∈ 𝓝 y, InjOn φ V := fun y hy => by
    obtain ⟨E, hyE, -, hE⟩ := hφ y hy
    exact ⟨E.source, E.open_source.mem_nhds hyE, hE ▸ E.injOn⟩
  -- `S`: the ends `s ∈ [a, b]` up to which a lift from `x` into `W` exists
  set S : Set ℝ := {s | s ∈ Icc a b ∧ ∃ σ, IsLiftOn φ c a s σ ∧ MapsTo σ (Icc a s) W ∧ σ a = x}
    with hSdef
  have haS : a ∈ S := ⟨⟨le_rfl, hab⟩, fun _ => x, ⟨continuousOn_const, fun t ht => by
    rw [show t = a from le_antisymm ht.2 ht.1]; exact hx⟩, fun _ _ => hxW, rfl⟩
  have hbdd : BddAbove S := ⟨b, fun s hs => hs.1.2⟩
  have hSne : S.Nonempty := ⟨a, haS⟩
  set e := sSup S with he
  have hae : a ≤ e := le_csSup hbdd haS
  have heb : e ≤ b := csSup_le hSne fun s hs => hs.1.2
  have hdown : ∀ s ∈ S, ∀ t, a ≤ t → t ≤ s → t ∈ S := fun s hs t h1 h2 => by
    obtain ⟨hsI, σ, hσ, hσW, hσa⟩ := hs
    exact ⟨⟨h1, h2.trans hsI.2⟩, σ, hσ.mono h2, hσW.mono_left (Icc_subset_Icc le_rfl h2), hσa⟩
  -- two lifts from `x` agree on the shorter segment
  have hagree : ∀ s s' σ σ', IsLiftOn φ c a s σ → MapsTo σ (Icc a s) W → σ a = x →
      IsLiftOn φ c a s' σ' → MapsTo σ' (Icc a s') W → σ' a = x → s ≤ s' → a ≤ s →
        EqOn σ σ' (Icc a s) := fun s s' σ σ' h hW h0 h' hW' h0' hss has =>
    h.eqOn hinj (h'.mono hss) hW (hW'.mono_left (Icc_subset_Icc le_rfl hss)) ⟨le_rfl, has⟩
      (h0.trans h0'.symm)
  -- the extension step
  have hext : ∀ t₁ σ, IsLiftOn φ c a t₁ σ → MapsTo σ (Icc a t₁) W → σ a = x → a ≤ t₁ →
      ∀ E : OpenPartialHomeomorph M N, φ = E → E.source ⊆ W → σ t₁ ∈ E.source → ∀ s₂, t₁ ≤ s₂ →
        s₂ ≤ b → (∀ t ∈ Icc t₁ s₂, c t ∈ E.target) → s₂ ∈ S :=
    fun t₁ σ hσ hσW hσa hat E hE hEW hsrc s₂ h12 hs₂ htgt => by
      obtain ⟨h1, h2⟩ := hσ.extend hσW hat h12 E hE hEW hsrc
        (hc.mono (Icc_subset_Icc (hat.trans le_rfl) hs₂)) htgt
      exact ⟨⟨hat.trans h12, hs₂⟩, _, h1, h2, by simp only [hat, if_true]; exact hσa⟩
  -- a neighbourhood of `e` on which `c` stays in an open set containing `c e`
  have hnbhd : ∀ O : Set N, IsOpen O → c e ∈ O →
      ∃ δ > 0, ∀ t ∈ Icc a b, dist t e < δ → c t ∈ O := fun O hO hce => by
    have h : c ⁻¹' O ∈ 𝓝[Icc a b] e := hc e ⟨hae, heb⟩ (hO.mem_nhds hce)
    rw [Metric.mem_nhdsWithin_iff] at h
    obtain ⟨δ, hδ, hsub⟩ := h
    exact ⟨δ, hδ, fun t ht htd => hsub ⟨htd, ht⟩⟩
  by_cases heS : e ∈ S
  · obtain ⟨-, σ, hσ, hσW, hσa⟩ := heS
    rcases heb.lt_or_eq with hlt | heq
    · exfalso
      obtain ⟨E, hyE, hEW, hE⟩ := hφ (σ e) (hσW ⟨hae, le_rfl⟩)
      have hce : c e ∈ E.target := by
        rw [← hσ.2 e ⟨hae, le_rfl⟩, hE]; exact E.map_source hyE
      obtain ⟨δ, hδ, hO⟩ := hnbhd E.target E.open_target hce
      have hs₂ := hext e σ hσ hσW hσa hae E hE hEW hyE (min (e + δ / 2) b)
        (le_min (by linarith) heb) (min_le_right _ _) fun t ht => hO t
          ⟨hae.trans ht.1, ht.2.trans (min_le_right _ _)⟩ (by
            rw [Real.dist_eq, abs_lt]
            constructor <;> linarith [ht.1, ht.2.trans (min_le_left (e + δ / 2) b)])
      have := le_csSup hbdd hs₂
      have hlt' : e < min (e + δ / 2) b := lt_min (by linarith) hlt
      linarith
    · exact Or.inl ⟨σ, heq ▸ hσ, heq ▸ hσW, hσa⟩
  · -- the lift exists on `[a, e)`
    have hae' : a < e := lt_of_le_of_ne hae fun h => heS (h ▸ haS)
    have hmemS : ∀ t ∈ Ico a e, t ∈ S := fun t ht => by
      obtain ⟨s, hs, hts⟩ := exists_lt_of_lt_csSup hSne ht.2
      exact hdown s hs t ht.1 hts.le
    have hex : ∀ t ∈ Ico a e, ∃ σ, IsLiftOn φ c a t σ ∧ MapsTo σ (Icc a t) W ∧ σ a = x :=
      fun t ht => (hmemS t ht).2
    haveI : Nonempty M := ⟨x⟩
    choose! L hL hLW hLa using hex
    set σ : ℝ → M := fun t => L t t with hσdef
    have hσeq : ∀ s ∈ Ico a e, EqOn σ (L s) (Icc a s) := fun s hs t ht => by
      have htI : t ∈ Ico a e := ⟨ht.1, lt_of_le_of_lt ht.2 hs.2⟩
      exact hagree t s (L t) (L s) (hL t htI) (hLW t htI) (hLa t htI) (hL s hs) (hLW s hs)
        (hLa s hs) ht.2 ht.1 ⟨ht.1, le_rfl⟩
    have hσc : ContinuousOn σ (Ico a e) := fun t ht => by
      obtain ⟨s, hs, hts⟩ := exists_lt_of_lt_csSup hSne ht.2
      have hsI : s ∈ Ico a e :=
        ⟨ht.1.trans hts.le, lt_of_le_of_ne (le_csSup hbdd hs) fun h => heS (h ▸ hs)⟩
      have h1 : ContinuousOn σ (Icc a s) := (hL s hsI).1.congr (hσeq s hsI)
      refine (h1 t ⟨ht.1, hts.le⟩).mono_of_mem_nhdsWithin ?_
      refine mem_nhdsWithin.2 ⟨Iio s, isOpen_Iio, hts, fun r hr => ⟨hr.2.1, le_of_lt hr.1⟩⟩
    have hσW : MapsTo σ (Ico a e) W := fun t ht => hLW t ht ⟨ht.1, le_rfl⟩
    have hσa : σ a = x := hLa a ⟨le_rfl, hae'⟩
    have hσl : ∀ t ∈ Ico a e, φ (σ t) = c t := fun t ht => (hL t ht).2 t ⟨ht.1, le_rfl⟩
    refine Or.inr ⟨e, ⟨hae', heb⟩, σ, hσc, hσW, hσa, hσl, ?_⟩
    rintro ⟨y, hyW, hy⟩
    obtain ⟨E, hyE, hEW, hE⟩ := hφ y hyW
    -- the limit lies over `c e`
    have hev : ∀ᶠ t in 𝓝[<] e, t ∈ Ioo a e := Ioo_mem_nhdsLT hae'
    have h1 : Tendsto (φ ∘ σ) (𝓝[<] e) (𝓝 (φ y)) := by
      rw [hE]; exact (E.continuousAt hyE).tendsto.comp hy
    have h2 : Tendsto c (𝓝[<] e) (𝓝 (c e)) := by
      have := ((hc e ⟨hae, heb⟩).mono (Ioo_subset_Icc_self.trans
        (Icc_subset_Icc le_rfl heb))).tendsto
      rwa [nhdsWithin_Ioo_eq_nhdsLT hae'] at this
    have h3 : (φ ∘ σ) =ᶠ[𝓝[<] e] c := hev.mono fun t ht => hσl t ⟨ht.1.le, ht.2⟩
    have hyc : φ y = c e := tendsto_nhds_unique (h1.congr' h3) h2
    have hce : c e ∈ E.target := by rw [← hyc, hE]; exact E.map_source hyE
    obtain ⟨δ, hδ, hO⟩ := hnbhd E.target E.open_target hce
    have hev2 : ∀ᶠ t in 𝓝[<] e, σ t ∈ E.source := hy (E.open_source.mem_nhds hyE)
    have hev3 : ∀ᶠ t in 𝓝[<] e, t ∈ Ioo (max a (e - δ)) e :=
      Ioo_mem_nhdsLT (max_lt hae' (by linarith))
    obtain ⟨t₁, ht₁, ht₁'⟩ := (hev2.and hev3).exists
    have ht₁I : t₁ ∈ Ico a e := ⟨(le_max_left _ _).trans ht₁'.1.le, ht₁'.2⟩
    have hsrc : L t₁ t₁ ∈ E.source := ht₁
    have hs₂ := hext t₁ (L t₁) (hL t₁ ht₁I) (hLW t₁ ht₁I) (hLa t₁ ht₁I) ht₁I.1 E hE hEW hsrc
      (min (e + δ / 2) b) (le_min (by linarith [ht₁'.2]) (ht₁'.2.le.trans heb))
      (min_le_right _ _) fun t ht =>
        hO t ⟨ht₁I.1.trans ht.1, ht.2.trans (min_le_right _ _)⟩ (by
          have h4 := ht.2.trans (min_le_left (e + δ / 2) b)
          have h5 := (le_max_right a (e - δ)).trans_lt ht₁'.1
          rw [Real.dist_eq, abs_lt]
          constructor <;> linarith [ht.1])
    have hle := le_csSup hbdd hs₂
    have hge : e ≤ min (e + δ / 2) b := le_min (by linarith) heb
    have heq : min (e + δ / 2) b = e := le_antisymm hle hge
    rw [heq] at hs₂
    exact heS hs₂

/-! ### Abstract morphisms: local homeomorphisms, time reversal, lifts of causal curves -/

variable {C : Causality M} {D : Causality N} {U : Opens M}

/-- **An abstract `𝕄≥0`-morphism on the open set `U` is a local homeomorphism there**: every point
of `U` lies in the source of a chart of `φ` (an open partial homeomorphism agreeing with `φ`)
whose source is contained in `U`. -/
theorem exists_chart_of_isEMorphismOn (h : IsEMorphismOn C D U φ) :
    ∀ y ∈ (U : Set M), ∃ E : OpenPartialHomeomorph M N, y ∈ E.source ∧ E.source ⊆ U ∧ φ = E := by
  have hloc : IsLocalHomeomorphOn φ U := by
    rw [isLocalHomeomorphOn_iff_isOpenEmbedding_restrict]
    intro x hx
    obtain ⟨V, hVU, hxV, hinj, -⟩ := h.locally x hx
    refine ⟨V, V.isOpen.mem_nhds hxV, ?_⟩
    refine IsOpenEmbedding.of_continuous_injective_isOpenMap ?_ ?_ ?_
    · exact (h.continuousOn.mono hVU).restrict
    · intro y z hyz; exact Subtype.ext (hinj y.2 z.2 hyz)
    · intro O hO
      obtain ⟨O', hO', rfl⟩ := isOpen_induced_iff.1 hO
      have him : (V : Set M).restrict φ '' (Subtype.val ⁻¹' O') = φ '' ((V : Set M) ∩ O') := by
        rw [Set.restrict_eq, image_comp, Subtype.image_preimage_coe]
      rw [him]
      exact h.isOpen_image (V ⊓ ⟨O', hO'⟩) (inf_le_left.trans hVU)
  intro y hy
  obtain ⟨E, hyE, hE⟩ := hloc y hy
  exact ⟨E.restrOpen U U.isOpen, ⟨hyE, hy⟩, fun z hz => hz.2, by rw [E.coe_restrOpen]; exact hE⟩

/-- An abstract morphism on `U` is locally injective on `U`. -/
theorem locallyInjOn_of_isEMorphismOn (h : IsEMorphismOn C D U φ) :
    ∀ y ∈ (U : Set M), ∃ V ∈ 𝓝 y, InjOn φ V := fun y hy => by
  obtain ⟨V, -, hyV, hinj, -⟩ := h.locally y hy
  exact ⟨V, V.isOpen.mem_nhds hyV, hinj⟩

/-- **Time reversal of an abstract morphism**: a morphism `C → D` on `U` is one `C.dual → D.dual`
(kb/0002). -/
theorem isEMorphismOn_dual (h : IsEMorphismOn C D U φ) : IsEMorphismOn C.dual D.dual U φ where
  continuousOn := h.continuousOn
  isOpen_image := h.isOpen_image
  map_le V U hV hmaps _ _ hxy := h.map_le V U hV hmaps hxy
  map_lt V U hV hmaps _ _ hxy := h.map_lt V U hV hmaps hxy
  locally x hx := by
    obtain ⟨V, hVW, hxV, hinj, hmatch⟩ := h.locally x hx
    exact ⟨V, hVW, hxV, hinj, fun V' hV' U hU y hy z hz => hmatch V' hV' U hU z hz y hy⟩

/-- **A lift of a causal curve along an abstract morphism is a causal curve.** If `c` is a future
causal curve of `N` over `[a, b]` and `σ` is continuous on `[a, b]` with values in `U` and
`φ ∘ σ = c`, then `σ` is a future causal curve of `U`: near each parameter `σ` stays in a
neighbourhood on which `φ` matches the relations of every smaller open set with those of its
image. -/
theorem causalCurveOn_of_lift (hφ : IsEMorphismOn C D U φ) (hc : D.CausalCurveOn ⊤ c a b)
    (hσc : ContinuousOn σ (Icc a b)) (hσU : ∀ t ∈ Icc a b, σ t ∈ U)
    (hσ : ∀ t ∈ Icc a b, φ (σ t) = c t) : C.CausalCurveOn U σ a b where
  mem := hσU
  rel t ht N' hN' hσt := by
    obtain ⟨V, hVU, hxV, -, hmatch⟩ := hφ.locally (σ t) (hσU t ht)
    set V' : Opens M := V ⊓ N' with hV'
    set U' : Opens N := ⟨φ '' V', hφ.isOpen_image V' (inf_le_left.trans hVU)⟩ with hU'
    have hct : c t ∈ U' := ⟨σ t, ⟨hxV, hσt⟩, hσ t ht⟩
    obtain ⟨l, u, hl, hu, hrel⟩ := hc.rel t ht U' le_top hct
    have h : σ ⁻¹' (V' : Set M) ∈ 𝓝[Icc a b] t := hσc t ht (V'.isOpen.mem_nhds ⟨hxV, hσt⟩)
    rw [Metric.mem_nhdsWithin_iff] at h
    obtain ⟨ε, hε, hsub⟩ := h
    refine ⟨max l (t - ε), min u (t + ε), max_lt hl (by linarith),
      lt_min hu (by linarith), fun s hs s' hs' h1 h2 h3 => ?_⟩
    have hl1 := le_max_right l (t - ε)
    have hu1 := min_le_right u (t + ε)
    have hsV : σ s ∈ V' :=
      hsub ⟨by rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith, hs⟩
    have hs'V : σ s' ∈ V' :=
      hsub ⟨by rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith, hs'⟩
    have hD := hrel s hs s' hs' (lt_of_le_of_lt (le_max_left _ _) h1) h2
      (lt_of_lt_of_le h3 (min_le_left _ _))
    rw [← hσ s hs, ← hσ s' hs'] at hD
    have := ((hmatch V' inf_le_left U' rfl (σ s) hsV (σ s') hs'V).1).2 hD
    exact C.le_mono inf_le_right this

/-! ### The steps of Lemma 3.3 -/

variable {T : M → ℝ} {S : Set M}

/-- Through every point of an open `U` runs an inextensible causal curve of `U`, when a
continuous `T` is strictly increasing along `≤_M` (`exists_inextensible_of_timeFunction`, applied
to a constant curve). -/
theorem exists_inextensible_through (hTc : Continuous T)
    (hT : ∀ x y, C.le ⊤ x y → x ≠ y → T x < T y) {x : M} (hx : x ∈ U) :
    ∃ (I : Set ℝ) (γ : ℝ → M), C.Inextensible U I γ ∧ ∃ t ∈ I, γ t = x := by
  have hconst : C.CausalCurveIn U (Icc 0 0) (fun _ => x) :=
    (Causality.causalCurveOn_const (C := C) (W := U) (p := x) (a := 0) (b := 0) hx).causalCurveIn_Icc
      le_rfl
  obtain ⟨I, γ, hγ, hsub, -⟩ := Causality.exists_inextensible_of_timeFunction hTc hT hconst
  obtain ⟨t, ht, hγt⟩ := hsub ⟨0, ⟨le_rfl, le_rfl⟩, rfl⟩
  exact ⟨I, γ, hγ, t, ht, hγt⟩

/-- In a causal spacetime, a causal curve taking one value at two parameters is constant between
them. -/
theorem eq_of_mem_Icc_of_isCausal {I : Set ℝ} {c : ℝ → N} (hD : D.IsCausal)
    (hc : D.CausalCurveIn ⊤ I c) {s s' r : ℝ} (hs : s ∈ I) (hs' : s' ∈ I) (hr : r ∈ Icc s s')
    (h : c s = c s') : c r = c s := by
  have hrI : r ∈ I := hc.ordConnected.out hs hs' hr
  have h1 := hc.le_of_le hs hrI hr.1
  have h2 := hc.le_of_le hrI hs' hr.2
  rw [← h] at h2
  exact hD h2 h1

/-- **φ⁻¹(φ Σ) ∩ U ⊆ Σ.** If `x ∈ U` and `φ x ∈ φ(Σ)`, then `x ∈ Σ`: an inextensible curve
of `U` through `x` meets `Σ` at a point `v`; `φ x` and `φ v` are causally related points of the
acausal set `φ(Σ)`, hence equal; `N` being causal, `φ` is constant along the curve between them,
so the curve (a lift of a constant) is constant there, and `x = v`. Injectivity on `Σ` is not
used. -/
theorem mem_of_map_mem_image [T2Space M] (hφ : IsEMorphismOn C D U φ) (hTc : Continuous T)
    (hT : ∀ x y, C.le ⊤ x y → x ≠ y → T x < T y) (hS : C.IsCauchySurfaceOn U S)
    (hac : D.IsAcausal (φ '' S)) (hD : D.IsCausal) {x : M} (hxU : x ∈ U)
    (hx : φ x ∈ φ '' S) : x ∈ S := by
  obtain ⟨I, β, hβ, s, hs, rfl⟩ := exists_inextensible_through hTc hT hxU
  obtain ⟨_, ⟨⟨s', hs', rfl⟩, hv⟩, -⟩ := hS I β hβ
  have hφβ : D.CausalCurveIn ⊤ I (φ ∘ β) :=
    IsEMorphismOn.causalCurveIn_comp hφ le_rfl (U := ⊤) (fun _ _ => trivial) hβ.1
  have hvS : φ (β s') ∈ φ '' S := ⟨β s', hv, rfl⟩
  have hmap : ∀ {y z : M}, C.le U y z → D.le ⊤ (φ y) (φ z) := fun h =>
    hφ.map_le U ⊤ le_rfl (fun _ _ => trivial) h
  have hinjl := locallyInjOn_of_isEMorphismOn hφ
  have hβU : ∀ {r r' : ℝ}, r ∈ I → r' ∈ I → MapsTo β (Icc r r') U := fun hr hr' t ht =>
    hβ.1.mem (hβ.1.ordConnected.out hr hr' ht)
  rcases le_total s s' with h | h
  · have heq : φ (β s) = φ (β s') := hac _ hx _ hvS (hmap (hβ.1.le_of_le hs hs' h))
    have := eq_of_lift_const hinjl h (hβ.1.continuousOn_Icc hs hs') (hβU hs hs')
      (fun r hr => eq_of_mem_Icc_of_isCausal hD hφβ hs hs' hr heq)
    rw [← this]; exact hv
  · have heq : φ (β s') = φ (β s) := hac _ hvS _ hx (hmap (hβ.1.le_of_le hs' hs h))
    have := eq_of_lift_const hinjl h (hβ.1.continuousOn_Icc hs' hs) (hβU hs' hs)
      (fun r hr => eq_of_mem_Icc_of_isCausal hD hφβ hs' hs hr heq)
    rw [this]; exact hv

/-- **Lemma 3.3, the case of a future curve from `q` to `Σ`**, in an open set `U`. Let `p, q ∈ U`,
`φ p = φ q`, and `γ` a future causal curve of `U` over an interval `I ∋ a, b`, `a ≤ b`, from
`γ a = q` to a point `γ b ∈ Σ`. Then `p = q`. The curve `φ ∘ γ` is lifted from `p` into `U`
(`exists_lift`): if the lift covers `[a, b]`, it ends on `Σ` (`mem_of_map_mem_image`) at `γ b`
(injectivity on `Σ`), and two lifts agreeing at `b` agree at `a`. Otherwise the lift `σ` over
`[a, e)` has no limit in `U` at `e`; it is a causal curve of `U` (`causalCurveOn_of_lift`) lying on
an inextensible curve `κ` of `U` parametrised by `T`, which meets `Σ` at `κ τᵤ`. If `T ∘ σ` stayed
below `τᵤ`, `σ = κ ∘ (T ∘ σ)` would have a limit; so `κ τᵤ ≤ p`, or `κ τᵤ = σ t` for some `t`.
Either way acausality of `φ(Σ)` makes `φ ∘ γ` constant on `[t, b]`, and the lift of a constant is
constant: `σ` has a limit at `e` after all. -/
theorem eq_of_curve_to_cauchy [T2Space M] [T2Space N] (hφ : IsEMorphismOn C D U φ)
    (hTc : Continuous T) (hT : ∀ x y, C.le ⊤ x y → x ≠ y → T x < T y)
    (hS : C.IsCauchySurfaceOn U S) (hinj : InjOn φ S) (hac : D.IsAcausal (φ '' S))
    (hD : D.IsCausal) {p q : M} (hpU : p ∈ U) (hpq : φ p = φ q) {I : Set ℝ} {γ : ℝ → M}
    (hγ : C.CausalCurveIn U I γ) (ha : a ∈ I) (hb : b ∈ I) (hab : a ≤ b) (hγa : γ a = q)
    (hγb : γ b ∈ S) : p = q := by
  have hchart := exists_chart_of_isEMorphismOn hφ
  have hinjl := locallyInjOn_of_isEMorphismOn hφ
  set c : ℝ → N := φ ∘ γ with hcdef
  have hc : D.CausalCurveIn ⊤ I c :=
    IsEMorphismOn.causalCurveIn_comp hφ le_rfl (U := ⊤) (fun _ _ => trivial) hγ
  have hcont : ContinuousOn c (Icc a b) := hc.continuousOn_Icc ha hb
  have hIab : Icc a b ⊆ I := hc.ordConnected.out ha hb
  have hcb : c b ∈ φ '' S := ⟨γ b, hγb, rfl⟩
  have hpc : φ p = c a := by simp only [hcdef, Function.comp, hγa, hpq]
  have hmap : ∀ {y z : M}, C.le U y z → D.le ⊤ (φ y) (φ z) := fun h =>
    hφ.map_le U ⊤ le_rfl (fun _ _ => trivial) h
  have hγlift : IsLiftOn φ c a b γ := ⟨hγ.continuousOn_Icc ha hb, fun _ _ => rfl⟩
  have hγU : MapsTo γ (Icc a b) U := fun t ht => hγ.mem (hIab ht)
  rcases exists_lift hchart hab hcont hpU hpc with
    ⟨σ, hσ, hσU, hσa⟩ | ⟨e, he, σ, hσc, hσU, hσa, hσl, hnolim⟩
  · -- the lift covers `[a, b]`
    have hσb : σ b ∈ S := mem_of_map_mem_image hφ hTc hT hS hac hD (hσU ⟨hab, le_rfl⟩)
      (by rw [hσ.2 b ⟨hab, le_rfl⟩]; exact hcb)
    have hσbγ : σ b = γ b := hinj hσb hγb (hσ.2 b ⟨hab, le_rfl⟩)
    have := hσ.eqOn hinjl hγlift hσU hγU ⟨hab, le_rfl⟩ hσbγ ⟨le_rfl, hab⟩
    rw [← hσa, this, hγa]
  · exfalso
    -- a constant tail of `c` gives the lift a limit at `e`
    have key : ∀ t ∈ Ico a e, (∀ r ∈ Icc t b, c r = c b) → False := by
      intro t ht hconst
      apply hnolim
      refine ⟨σ t, hσU ht, tendsto_const_nhds.congr' ?_⟩
      filter_upwards [Ioo_mem_nhdsLT ht.2] with r hr
      have hsub : Icc t r ⊆ Ico a e := fun x hx => ⟨ht.1.trans hx.1, lt_of_le_of_lt hx.2 hr.2⟩
      exact (eq_of_lift_const (y := c b) hinjl hr.1.le (hσc.mono hsub) (hσU.mono_left hsub)
        (fun x hx => by
          rw [hσl x (hsub hx)]; exact hconst x ⟨hx.1, hx.2.trans (hr.2.le.trans he.2)⟩)).symm
    -- the lift is a causal curve of `U` over `[a, e)`
    have hσcurve : C.CausalCurveIn U (Ico a e) σ := by
      refine ⟨⟨a, le_rfl, he.1⟩, ordConnected_Ico, fun a' ha' b' hb' => ?_⟩
      rcases le_or_gt a' b' with h | h
      · have hsub : Icc a' b' ⊆ Ico a e := ordConnected_Ico.out ha' hb'
        have hsubI : Icc a' b' ⊆ Icc a b := fun x hx => ⟨(hsub hx).1, (hsub hx).2.le.trans he.2⟩
        exact causalCurveOn_of_lift hφ
          (hc.curve a' (hIab (hsubI ⟨le_rfl, h⟩)) b' (hIab (hsubI ⟨h, le_rfl⟩)))
          (hσc.mono hsub) (fun t ht => hσU (hsub ht)) fun t ht => hσl t (hsub ht)
      · exact CurveOn.of_lt h
    obtain ⟨J, κ, hκ, hsub, hTκ⟩ := Causality.exists_inextensible_of_timeFunction hTc hT hσcurve
    have hσκ : ∀ t ∈ Ico a e, T (σ t) ∈ J ∧ κ (T (σ t)) = σ t := by
      intro t ht
      obtain ⟨τ, hτ, hκτ⟩ := hsub ⟨t, ht, rfl⟩
      rw [← hκτ, hTκ τ hτ]; exact ⟨hτ, rfl⟩
    obtain ⟨_, ⟨⟨τu, hτu, rfl⟩, hu⟩, -⟩ := hS J κ hκ
    have haI : a ∈ Ico a e := ⟨le_rfl, he.1⟩
    -- `T ∘ σ` reaches `τu`, else `σ = κ ∘ (T ∘ σ)` has a limit
    have hreach : ∃ t₁ ∈ Ico a e, τu ≤ T (σ t₁) := by
      by_contra hno
      push Not at hno
      set f : ℝ → ℝ := fun t => T (σ (max t a)) with hf
      have hmaxI : ∀ t < e, max t a ∈ Ico a e := fun t ht =>
        ⟨le_max_right _ _, max_lt ht he.1⟩
      have hfmono : MonotoneOn f (Iio e) := fun x hx y hy hxy =>
        hσcurve.time_mono hT (hmaxI x hx) (hmaxI y hy) (max_le_max hxy le_rfl)
      have hfmem : ∀ t < e, f t ∈ Icc (T (σ a)) τu := fun t ht =>
        ⟨hσcurve.time_mono hT haI (hmaxI t ht) (le_max_right _ _), (hno _ (hmaxI t ht)).le⟩
      have hfbdd : BddAbove (f '' Iio e) := ⟨τu, by
        rintro _ ⟨t, ht, rfl⟩; exact (hfmem t ht).2⟩
      have hlim : Tendsto f (𝓝[<] e) (𝓝 (sSup (f '' Iio e))) := hfmono.tendsto_nhdsLT hfbdd
      have hfa : f a = T (σ a) := by simp only [hf, max_self]
      have hLmem : sSup (f '' Iio e) ∈ Icc (T (σ a)) τu :=
        ⟨hfa ▸ le_csSup hfbdd ⟨a, he.1, rfl⟩,
          csSup_le ⟨f a, a, he.1, rfl⟩ fun _ ⟨t, ht, h⟩ => h ▸ (hfmem t ht).2⟩
      have hLJ : sSup (f '' Iio e) ∈ J := hκ.1.ordConnected.out (hσκ a haI).1 hτu hLmem
      have hκc : ContinuousOn κ (Icc (T (σ a)) τu) := hκ.1.continuousOn_Icc (hσκ a haI).1 hτu
      apply hnolim
      refine ⟨κ (sSup (f '' Iio e)), hκ.1.mem hLJ, ?_⟩
      have h1 : Tendsto (κ ∘ f) (𝓝[<] e) (𝓝 (κ (sSup (f '' Iio e)))) :=
        (hκc _ hLmem).tendsto.comp (tendsto_nhdsWithin_iff.2
          ⟨hlim, eventually_nhdsWithin_of_forall fun t ht => hfmem t ht⟩)
      refine h1.congr' ?_
      filter_upwards [Ioo_mem_nhdsLT he.1] with t ht
      simp only [Function.comp, hf, max_eq_left ht.1.le]
      exact (hσκ t ⟨ht.1.le, ht.2⟩).2
    obtain ⟨t₁, ht₁, hτt₁⟩ := hreach
    rcases le_or_gt τu (T (σ a)) with hle | hlt
    · -- `κ` meets `Σ` at a point `u ≤ p`
      have hup : C.le U (κ τu) p := by
        rw [← hσa, ← (hσκ a haI).2]; exact hκ.1.le_of_le hτu (hσκ a haI).1 hle
      have h0 : D.le ⊤ (φ (κ τu)) (c a) := by rw [← hpc]; exact hmap hup
      have h1 : D.le ⊤ (φ (κ τu)) (c b) := D.le_trans h0 (hc.le_of_le ha hb hab)
      have heq : φ (κ τu) = c b := hac _ ⟨_, hu, rfl⟩ _ hcb h1
      refine key a haI fun r hr => ?_
      have hr' : r ∈ I := hIab hr
      have h2 : D.le ⊤ (c b) (c r) := by
        rw [← heq]; exact D.le_trans h0 (hc.le_of_le ha hr' hr.1)
      exact hD (hc.le_of_le hr' hb hr.2) h2
    · -- `κ` meets `Σ` on the lift, at `σ t`
      have hcontT : ContinuousOn (T ∘ σ) (Icc a t₁) :=
        hTc.comp_continuousOn (hσc.mono (Icc_subset_Ico_right ht₁.2))
      obtain ⟨t, htI, htT⟩ := intermediate_value_Icc ht₁.1 hcontT ⟨hlt.le, hτt₁⟩
      have htIco : t ∈ Ico a e := ⟨htI.1, lt_of_le_of_lt htI.2 ht₁.2⟩
      have hσt : σ t = κ τu := by
        rw [← (hσκ t htIco).2]; simp only [Function.comp] at htT; rw [htT]
      have hct : c t ∈ φ '' S := ⟨κ τu, hu, by rw [← hσt, hσl t htIco]⟩
      have htb : t ≤ b := htIco.2.le.trans he.2
      have htI' : t ∈ I := hIab ⟨htI.1, htb⟩
      have heq : c t = c b := hac _ hct _ hcb (hc.le_of_le htI' hb htb)
      exact key t htIco fun r hr => (eq_of_mem_Icc_of_isCausal hD hc htI' hb hr heq).trans heq

/-! ### Lemma 3.3 -/

/-- **Sbierski, Lemma 3.3 — the principal form, on an open set** (kb/0001). Let `φ` be an abstract
`𝕄≥0`-morphism on the open set `U` of `M` (`IsEMorphismOn`), `M` and `N` Hausdorff, `M` carrying a
continuous `T` strictly increasing along `≤_M`, `Σ` a Cauchy surface of `U`, `N` causal. If `φ`
is injective on `Σ` and maps `Σ` onto an acausal set, `φ` is injective on `U`. Global
hyperbolicity is not used beyond the time function; no rigidity is used. -/
theorem injOn_of_injOn_cauchy [T2Space M] [T2Space N] (hφ : IsEMorphismOn C D U φ)
    (hTc : Continuous T) (hT : ∀ x y, C.le ⊤ x y → x ≠ y → T x < T y)
    (hS : C.IsCauchySurfaceOn U S) (hinj : InjOn φ S) (hac : D.IsAcausal (φ '' S))
    (hD : D.IsCausal) : InjOn φ U := by
  intro p hpU q hqU hpq
  obtain ⟨I, γ, hγ, tq, htq, rfl⟩ := exists_inextensible_through hTc hT hqU
  obtain ⟨_, ⟨⟨tz, htz, rfl⟩, hz⟩, -⟩ := hS I γ hγ
  rcases le_total tq tz with h | h
  · exact eq_of_curve_to_cauchy hφ hTc hT hS hinj hac hD hpU hpq hγ.1 htq htz h rfl hz
  · -- time reversal (kb/0002)
    have hT' : ∀ x y, C.dual.le ⊤ x y → x ≠ y → (fun x => -T x) x < (fun x => -T x) y :=
      fun x y hxy hne => by
        have := hT y x hxy (Ne.symm hne); simp only; linarith
    exact eq_of_curve_to_cauchy (C := C.dual) (D := D.dual) (T := fun x => -T x)
      (isEMorphismOn_dual hφ) hTc.neg hT' (Causality.dual_isCauchySurfaceOn.2 hS) hinj
      (Causality.dual_isAcausal.2 hac) (Causality.dual_isCausal.2 hD) hpU hpq hγ.1.reverse
      (a := -tq) (b := -tz) (by simpa using htq) (by simpa using htz) (neg_le_neg h)
      (by simp) (by simpa using hz)

/-- **Sbierski, Lemma 3.3 — the principal form, for `M` itself.** -/
theorem injective_of_injOn_cauchy [T2Space M] [T2Space N] (hφ : IsEMorphism C D φ)
    (hTc : Continuous T) (hT : ∀ x y, C.le ⊤ x y → x ≠ y → T x < T y)
    (hS : C.IsCauchySurface S) (hinj : InjOn φ S) (hac : D.IsAcausal (φ '' S))
    (hD : D.IsCausal) : Injective φ := fun _ _ hpq =>
  injOn_of_injOn_cauchy hφ hTc hT hS hinj hac hD trivial trivial hpq

/-- **Sbierski's hypotheses on the target**: `φ(Σ) ⊆ Σ'` for a Cauchy surface `Σ'` of a causal,
causally arc-connected `N` in which curves extend; `Σ'` is then acausal
(`IsCauchySurface.isAcausal`), and so is `φ(Σ)`. -/
theorem injective_of_mapsTo_cauchy [T2Space M] [T2Space N] (hφ : IsEMorphism C D φ)
    (hTc : Continuous T) (hT : ∀ x y, C.le ⊤ x y → x ≠ y → T x < T y)
    (hS : C.IsCauchySurface S) (hinj : InjOn φ S) {S' : Set N} (hS' : D.IsCauchySurface S')
    (hmaps : MapsTo φ S S') (hD : D.IsCausal) (hDC : D.CausallyArcConnected)
    (hDext : D.CurvesExtend) : Injective φ := by
  have hac' := hS'.isAcausal hDC hDext
  refine injective_of_injOn_cauchy hφ hTc hT hS hinj (fun x hx y hy hxy => ?_) hD
  exact hac' x (hmaps.image_subset hx) y (hmaps.image_subset hy) hxy

/-- **Sbierski, Lemma 3.3, with its printed conclusion**: between globally hyperbolic spacetimes,
an abstract `𝕄≥0`-morphism injective on a Cauchy surface `Σ` of `M` whose image `φ(Σ)` is a Cauchy
surface of `N` ("`ψ|_Σ : Σ → Σ'` a diffeomorphism") is a Cauchy embedding
(`def:cauchy_embedding_cauchy_extension`): "`ψ` is an isometric embedding". The time function of
`M`, and `CurvesExtend` and causal arc-connectedness of `N`, are what global hyperbolicity provides
in Sbierski's setting (`injective_of_globallyHyperbolic` derives the first). -/
theorem sbierski_lemma_3_3 [T2Space M] [T2Space N] (hGM : C.GloballyHyperbolic)
    (hGN : D.GloballyHyperbolic) (hφ : IsEMorphism C D φ) (hTc : Continuous T)
    (hT : ∀ x y, C.le ⊤ x y → x ≠ y → T x < T y) (hS : C.IsCauchySurface S)
    (hS' : D.IsCauchySurface (φ '' S)) (hinj : InjOn φ S) (hDC : D.CausallyArcConnected)
    (hDext : D.CurvesExtend) : IsCauchyEmbedding C D φ :=
  ⟨hGM, hGN, hφ, injective_of_mapsTo_cauchy hφ hTc hT hS hinj hS' (mapsTo_image φ S) hGN.1 hDC
    hDext, ⟨S, hS, hS'⟩⟩

/-- **Lemma 3.3 for globally hyperbolic `M`**, the time function being Geroch's
(`geroch_i_imp_ii`, `theo:geroch` (i)⇒(ii)), under its hypotheses: admissible measures, tarentin,
causally arc-connected, `J^±(p) ≠ {p}`, Hausdorff and first countable. -/
theorem injective_of_globallyHyperbolic [T2Space M] [FirstCountableTopology M] [MeasurableSpace M]
    [BorelSpace M] [T2Space N] {μp μm : MeasureTheory.Measure M} (hμp : C.AdmissibleFuture μp)
    (hμm : C.AdmissiblePast μm) (hTar : C.Tarentin) (hC : C.CausallyArcConnected)
    (hJm : ∀ p : M, C.Jminus ⊤ {p} ≠ {p}) (hJp : ∀ p : M, C.Jplus ⊤ {p} ≠ {p})
    (hG : C.GloballyHyperbolic) (hφ : IsEMorphism C D φ) (hS : C.IsCauchySurface S)
    (hinj : InjOn φ S) (hac : D.IsAcausal (φ '' S)) (hD : D.IsCausal) : Injective φ := by
  obtain ⟨τ, hτ, hτs⟩ := Causality.geroch_i_imp_ii hμp hμm hTar hC hJm hJp hG
  exact injective_of_injOn_cauchy hφ hτ.1.continuous hτs hS hinj hac hD

/-! ### Witnesses on Minkowski space -/

/-- **The hypotheses of the principal theorem are jointly satisfiable on Minkowski space**
`𝐌^{1,d}` (kb/0011): the identity, the time coordinate, the slice `{t = 0}`. -/
theorem minkowski_injective_hypotheses (d : ℕ) :
    IsEMorphism (minkowski d) (minkowski d) id ∧ Continuous (fun p : Minkowski d => p.1) ∧
      (∀ x y : Minkowski d, (minkowski d).le ⊤ x y → x ≠ y → x.1 < y.1) ∧
      (minkowski d).IsCauchySurface (minkowskiSlice d 0) ∧ InjOn id (minkowskiSlice d 0) ∧
      (minkowski d).IsAcausal (id '' minkowskiSlice d 0) ∧ (minkowski d).IsCausal := by
  refine ⟨IsEMorphism.id, continuous_fst, minkowski_time_strict.2,
    minkowski_isCauchySurface_slice 0, injOn_id _, ?_, minkowski_isCausal⟩
  rw [image_id]
  exact minkowski_isAcausal_of_isCauchySurface (minkowski_isCauchySurface_slice 0)

/-- **Sbierski's form is non-vacuous**: the identity of Minkowski space is a Cauchy embedding by
`sbierski_lemma_3_3`, every hypothesis discharged. -/
theorem minkowski_sbierski_lemma_3_3 (d : ℕ) :
    IsCauchyEmbedding (minkowski d) (minkowski d) id := by
  have hS := minkowski_isCauchySurface_slice (d := d) 0
  exact sbierski_lemma_3_3 minkowski_globallyHyperbolic minkowski_globallyHyperbolic
    IsEMorphism.id continuous_fst minkowski_time_strict.2 hS (by rw [image_id]; exact hS)
    (injOn_id _) minkowski_causallyArcConnected (minkowski_curvesExtend d)

/-- **The globally hyperbolic form is non-vacuous** (kb/0011): on the timelike line `𝐌^{1,0}`
with the standard Gaussian measure (`timelikeLine_admissible_past_and_future`), every hypothesis
of `injective_of_globallyHyperbolic` holds for the identity and the Cauchy surface `{0}`, and it
applies. (On `𝐌^{1,d}` the admissible measure is `minkowski_mesure_dieckmann`, which rests
on the open item `prop:mesure_dieckmann_Lorentz` (`minkowski_exists_measure`); it is
deliberately not used here.) -/
theorem timelikeLine_injective_of_globallyHyperbolic :
    (timelikeLine.AdmissibleFuture (ProbabilityTheory.gaussianReal 0 1) ∧
      timelikeLine.AdmissiblePast (ProbabilityTheory.gaussianReal 0 1) ∧ timelikeLine.Tarentin ∧
      timelikeLine.CausallyArcConnected ∧ (∀ p : ℝ, timelikeLine.Jminus ⊤ {p} ≠ {p}) ∧
      (∀ p : ℝ, timelikeLine.Jplus ⊤ {p} ≠ {p}) ∧ timelikeLine.GloballyHyperbolic ∧
      IsEMorphism timelikeLine timelikeLine id ∧ timelikeLine.IsCauchySurface ({0} : Set ℝ) ∧
      InjOn id ({0} : Set ℝ) ∧ timelikeLine.IsAcausal (id '' ({0} : Set ℝ)) ∧
      timelikeLine.IsCausal) ∧ Injective (id : ℝ → ℝ) := by
  have hac : timelikeLine.IsAcausal (id '' ({0} : Set ℝ)) := by
    rw [image_id]; exact timelikeLine_isAcausal_zero
  refine ⟨⟨timelikeLine_admissible_past_and_future.2, timelikeLine_admissible_past_and_future.1,
    timelikeLine_tarentin, timelikeLine_causallyArcConnected, timelikeLine_Jminus_ne,
    timelikeLine_Jplus_ne, timelikeLine_globallyHyperbolic, IsEMorphism.id,
    timelikeLine_isCauchySurface_zero, injOn_id _, hac, timelikeLine_isCausal⟩, ?_⟩
  exact injective_of_globallyHyperbolic (C := timelikeLine) (D := timelikeLine)
    timelikeLine_admissible_past_and_future.2 timelikeLine_admissible_past_and_future.1
    timelikeLine_tarentin timelikeLine_causallyArcConnected timelikeLine_Jminus_ne
    timelikeLine_Jplus_ne timelikeLine_globallyHyperbolic IsEMorphism.id
    timelikeLine_isCauchySurface_zero (injOn_id _) hac timelikeLine_isCausal

end CBG

end Causal
