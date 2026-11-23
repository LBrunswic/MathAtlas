import Causal.ErsMughd
import Causal.AbstractDev

/-!
# Maximal developments by Zorn's lemma on a fixed background: ERS Remark 3.56

Programme target `T-abs-maximal-zorn` (`programme/roadmap.toml`; layer 1: ETT-layer imports only,
no model, no metric). Sources: Eperon–Reall–Sbierski 1802.03020 (`papers/ers-predictability`),
and Chruściel, *On maximal globally hyperbolic vacuum space-times*, arXiv 1112.5779, Theorem 2.2,
whose abstract form, the namespace `Causal.AbstractDev`, is the module `Causal.AbstractDev`
(split out of this one by `T-tac-curves-fact-rule`, same full names and statements; it imports
Mathlib only, so `Causal.CurvesExtendSecondCountable` uses it without this module's
`Causal.ErsMughd`). Chruściel is not ledgered. **No label is marked**; cited, unmarked:

* `ersrem:note_two_ghds_constructed` — `ghd_02_19.tex:731` (statement 731–733): `ers_remark_3_56`,
  `exists_isMaximalDevelopment`, `ers_remark_3_56_family`, `ers_remark_3_56_of_curveNested`.

> We note that the two GHDs constructed in the proof of Theorem 3.45 are not maximal. However, an
> application of Zorn's Lemma (!) to the set of globally hyperbolic extensions of Φ_a : U_a → ℝ
> shows that there exists a MGHD which contains Φ_a : U_a → ℝ. In the same way one shows the
> existence of a MGHD which contains Φ_b : U_b → ℝ. These two MGHDs are clearly distinct. In fact
> one can even show that there are infinitely many distinct MGHDs of the constructed initial data.
> We leave the details to the reader. (ERS Remark 3.56, `ghd_02_19.tex:732`)

> A GHD (M, u) is extendible if there exists another GHD (M', u') with M ⊊ M' and u = u' on M. We
> say that (M, u) is a maximal globally hyperbolic development (MGHD) of the initial data if
> (M, u) is not extendible as a GHD of the specified data on S. (`ghd_02_19.tex:117`)

## What is proved

* **The abstract theory**, Chruściel Thm 2.2 (`Causal.AbstractDev`, imported): developments with
  morphisms, chain inheritance and a size bound have maximal ones without rigidity
  (`AbstractDev.exists_isMaximal`, Zorn on towers), inextensible under (2.1)
  (`AbstractDev.chrusciel_theorem_2_2`), each hypothesis needed; used here through
  `AbstractDev.exists_isMaximal_of_chainsInherit`.
* **Developments on a fixed background** (the vocabulary of `Causal.ErsMughd`): `IsExtension`,
  `IsMaximalDevelopment` (ERS l. 117, `isMaximalDevelopment_iff`); a directed union of opens with
  `S` Cauchy has `S` Cauchy (`Causality.isCauchySurfaceOn_sSup_of_directedOn`), so the union of a
  chain of developments is one (`isDevelopment_sSup_of_isChain`); the developments as an abstract
  class (`Developments`, `ersMor`, `ersMor_hypotheses`, `isMaximal_ersMor_iff`), whence
  `exists_isMaximalDevelopment` from `AbstractDev.exists_isMaximal_of_chainsInherit`; ERS Remark
  3.56 (`ers_remark_3_56`, `_family`, `_of_curveNested`); witness `timelikeLine_ers_remark_3_56`.

## Hypothesis checklist

| ERS Remark 3.56 | here |
|---|---|
| ERS: Zorn's lemma (Chruściel Thm 2.2, abstractly) | ✓ `Causal.AbstractDev` (its own checklist): `exists_isMaximal_of_chainsInherit`, rigidity not needed for existence |
| ERS: the Born–Infeld equation on ℝ^{1+1} | ⚠ abstract: `sol`, `cau`, `SolutionLocal`, `SolutionsGlue`, `CausalityFollows` (as `Causal.ErsMughd`) |
| ERS: GHD, GH with Cauchy surface S | ⚠ read: `IsDevelopment` (`S` Cauchy for `cau u`, GH not asked: OQ-57 (c), as `Causal.ErsMughd`) |
| ERS: Zorn applies (the union of a chain of GHDs is a GHD, implicit) | ✓ proved (`isDevelopment_sSup_of_isChain`), ⚠ named `hanti`: `≤` antisymmetric on each solution's domain (ERS's GH reading gives it on the GHDs only, not on every domain `hanti` quantifies over; subluminality supplies it, `ers_remark_3_56_of_curveNested`); `M` T2 |
| ERS: Φ_a, Φ_b differ at a common point (Thm 3.45) | ✓ hypotheses `ha`, `hb`, `hx`, `hab`; Theorem 3.45 itself is layer 3 |
| ERS: "these two MGHDs are clearly distinct" | ✓ `ua' x ≠ ub' x` and `¬ (Ua' = Ub' ∧ EqOn ua' ub' Ua')` |
| ERS: "the two GHDs … are not maximal"; "infinitely many" | ✗ the first (a fact of the construction, layer 3); ⚠ the second, abstract half only (`ers_remark_3_56_family`) |

## SCOPE (disclosed)

* **Nothing marked.** `ersrem:note_two_ghds_constructed` is partial: the equation is abstract, a GHD
  is read "`S` Cauchy", `hanti` is named, the remark's first sentence is not formalised and its
  "infinitely many" only in the abstract half (the infinite family of GHDs of the Born–Infeld
  data, which the paper leaves to the reader, is not constructed).
* **The abstract theory's scope** (rigidity not needed for existence, the size bound a universe,
  the Zorn-free `Causal.CBG` beside it) is disclosed in `Causal.AbstractDev`.
* **ERS's two definitions.** `IsMaximalDevelopment` is l. 117 (no development *extends* it with a
  larger domain); l. 1094 ("there does not exist a GHD u₂ : U₂ → ℝ … with U₁ ⊊ U₂") asks it of
  every development, agreeing or not, and is equivalent given Thm 4.64 on nested pairs, as ERS
  note there.
* The witness `timelikeLine_ers_remark_3_56` is degenerate (one domain, `ℝ`; two constants).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Function

/-! ## Developments on a fixed background: ERS Remark 3.56 -/

universe u v

namespace Causality

variable {M : Type u} [TopologicalSpace M] {C : Causality M} {S : Set M}

/-- **A directed union of open sets of which `S` is a Cauchy surface has `S` as Cauchy surface**
(`M` Hausdorff, `≤` antisymmetric on the union). An inextensible curve of the union meets `S`
through its component in one member; it meets it once, because the segment between two meeting
parameters is compact, so lies in one member, where its component is inextensible. No acausality
of `S` in the union (`isCauchySurfaceOn_iSup_of_isAcausalOn`) and no ambient open set
(`isCauchySurfaceOn_iSup` of `Causal.CBG.CausalConvex`) is used: directedness replaces both. For a
chain, `Causality.ers_theorem_4_77` also applies (its pairwise-overlap hypothesis is automatic on a
chain); the gain here is directed families and no `S ⊆ U`. -/
theorem isCauchySurfaceOn_sSup_of_directedOn [T2Space M] {𝒰 : Set (Opens M)}
    (h𝒰 : DirectedOn (· ≤ ·) 𝒰)
    (hanti : ∀ ⦃x y : M⦄, C.le (sSup 𝒰) x y → C.le (sSup 𝒰) y x → x = y)
    (hU : ∀ U ∈ 𝒰, C.IsCauchySurfaceOn U S) : C.IsCauchySurfaceOn (sSup 𝒰) S := by
  intro I c hc
  obtain ⟨t₀, ht₀⟩ := hc.1.nonempty
  obtain ⟨U, hU𝒰, hU₀⟩ := Opens.mem_sSup.1 (hc.1.mem ht₀)
  obtain ⟨_, ⟨⟨τ, hτ, rfl⟩, hτS⟩, -⟩ :=
    hU U hU𝒰 _ c (inextensible_ordConnectedComponent_of_le hanti (le_sSup hU𝒰) hc ht₀ hU₀)
  have hτI : τ ∈ I := (ordConnectedComponent_subset hτ).1
  refine ⟨c τ, ⟨⟨τ, hτI, rfl⟩, hτS⟩, ?_⟩
  rintro _ ⟨⟨σ, hσI, rfl⟩, hσS⟩
  have hseg : uIcc σ τ ⊆ I := hc.1.ordConnected.uIcc_subset hσI hτI
  have hlo : σ ⊓ τ ∈ I := hseg (left_mem_Icc.2 inf_le_sup)
  have hhi : σ ⊔ τ ∈ I := hseg (right_mem_Icc.2 inf_le_sup)
  have hK : IsCompact (c '' uIcc σ τ) :=
    isCompact_Icc.image_of_continuousOn
      (CurveOn.continuousOn C.isRelFamily_le (hc.1.curve _ hlo _ hhi))
  haveI : Nonempty 𝒰 := ⟨⟨U, hU𝒰⟩⟩
  obtain ⟨⟨V, hV𝒰⟩, hV⟩ := hK.elim_directed_cover (fun W : 𝒰 => (W.1 : Set M))
    (fun W => W.1.isOpen)
    (by
      rintro _ ⟨t, ht, rfl⟩
      obtain ⟨W, hW, hcW⟩ := Opens.mem_sSup.1 (hc.1.mem (hseg ht))
      exact mem_iUnion.2 ⟨⟨W, hW⟩, hcW⟩)
    (fun W W' => by
      obtain ⟨W'', hW'', h₁, h₂⟩ := h𝒰 W.1 W.2 W'.1 W'.2
      exact ⟨⟨W'', hW''⟩, h₁, h₂⟩)
  have hσV : c σ ∈ V := hV ⟨σ, left_mem_uIcc, rfl⟩
  have hinV := inextensible_ordConnectedComponent_of_le hanti (le_sSup hV𝒰) hc hσI hσV
  have hτc : τ ∈ ordConnectedComponent (I ∩ c ⁻¹' V) σ :=
    mem_ordConnectedComponent.2 fun t ht => ⟨hseg ht, hV ⟨t, ht, rfl⟩⟩
  have hσc : σ ∈ ordConnectedComponent (I ∩ c ⁻¹' V) σ :=
    self_mem_ordConnectedComponent.2 ⟨hσI, hσV⟩
  exact (hU V hV𝒰 _ c hinV).unique ⟨⟨σ, hσc, rfl⟩, hσS⟩ ⟨⟨τ, hτc, rfl⟩, hτS⟩

end Causality

section Developments

variable {M : Type u} [TopologicalSpace M] {β : Type v}

/-- **`(U', u')` extends `(U, u)`** (ERS `ghd_02_19.tex:117`, "M ⊊ M' and u = u' on M", without
the strictness): `U ⊆ U'` and `u = u'` on `U`. -/
def IsExtension (U : Opens M) (u : M → β) (U' : Opens M) (u' : M → β) : Prop :=
  U ≤ U' ∧ EqOn u u' U

theorem IsExtension.refl (U : Opens M) (u : M → β) : IsExtension U u U u := ⟨le_rfl, fun _ _ => rfl⟩

theorem IsExtension.trans {U U' U'' : Opens M} {u u' u'' : M → β} (h : IsExtension U u U' u')
    (h' : IsExtension U' u' U'' u'') : IsExtension U u U'' u'' :=
  ⟨h.1.trans h'.1, fun _ hx => (h.2 hx).trans (h'.2 (h.1 hx))⟩

/-- **A maximal development** (ERS's MGHD, `ghd_02_19.tex:117`, read with `IsDevelopment`): a
development `(U, u)` such that every development extending it has domain `U`. -/
def IsMaximalDevelopment (sol : Opens M → (M → β) → Prop) (cau : (M → β) → Causality M)
    (S : Set M) (U : Opens M) (u : M → β) : Prop :=
  IsDevelopment sol cau S U u ∧
    ∀ (U' : Opens M) (u' : M → β), IsDevelopment sol cau S U' u' → IsExtension U u U' u' → U' ≤ U

variable {sol : Opens M → (M → β) → Prop} {cau : (M → β) → Causality M} {S : Set M}

/-- ERS's wording (`ghd_02_19.tex:117`): "not extendible", i.e. no development `(U', u')` with
`U ⊊ U'` and `u = u'` on `U`. -/
theorem isMaximalDevelopment_iff {U : Opens M} {u : M → β} :
    IsMaximalDevelopment sol cau S U u ↔ IsDevelopment sol cau S U u ∧
      ¬ ∃ (U' : Opens M) (u' : M → β), IsDevelopment sol cau S U' u' ∧ U < U' ∧ EqOn u u' U := by
  constructor
  · rintro ⟨h, hmax⟩
    refine ⟨h, fun ⟨U', u', h', hlt, heq⟩ => ?_⟩
    exact hlt.ne (le_antisymm hlt.le (hmax U' u' h' ⟨hlt.le, heq⟩))
  · rintro ⟨h, hnot⟩
    refine ⟨h, fun U' u' h' hext => ?_⟩
    by_contra hle
    exact hnot ⟨U', u', h', hext.1.lt_of_ne fun h => hle (le_of_eq h.symm), hext.2⟩

/-- **The union of a chain of developments is a development** (the upper bound of ERS's Zorn
argument, Remark 3.56): the solutions glue (`hloc`, `hglue`), and `S` is a Cauchy surface of the
union for the glued causality (`hfollow`, `isCauchySurfaceOn_sSup_of_directedOn`), `≤` being
antisymmetric on the domain of every solution (`hanti`). -/
theorem isDevelopment_sSup_of_isChain [T2Space M] (hloc : SolutionLocal sol)
    (hglue : SolutionsGlue sol) (hfollow : CausalityFollows cau)
    (hanti : ∀ U u, sol U u → ∀ ⦃x y : M⦄, (cau u).le U x y → (cau u).le U y x → x = y)
    {𝒟 : Set (Opens M × (M → β))} (hne : 𝒟.Nonempty)
    (hchain : IsChain (fun d d' => IsExtension d.1 d.2 d'.1 d'.2) 𝒟)
    (hdev : ∀ d ∈ 𝒟, IsDevelopment sol cau S d.1 d.2) :
    ∃ v : M → β, (∀ d ∈ 𝒟, EqOn v d.2 d.1) ∧ IsDevelopment sol cau S (sSup (Prod.fst '' 𝒟)) v := by
  have hagree : ∀ d ∈ 𝒟, ∀ d' ∈ 𝒟, EqOn d.2 d'.2 (d.1 ⊓ d'.1 : Opens M) := by
    intro d hd d' hd' x hx
    by_cases h : d = d'
    · subst h
      rfl
    · rcases hchain hd hd' h with h' | h'
      · exact h'.2 hx.1
      · exact (h'.2 hx.2).symm
  obtain ⟨v, hv⟩ := exists_eqOn_of_pairwise hne hagree
  have hsol : sol (sSup (Prod.fst '' 𝒟)) v := by
    refine hglue _ v (hne.image _) ?_
    rintro _ ⟨d, hd, rfl⟩
    exact hloc (fun x hx => (hv d hd hx).symm) (hdev d hd).solves
  obtain ⟨d₀, hd₀⟩ := hne
  refine ⟨v, hv, hsol, fun x hx => (le_sSup (mem_image_of_mem Prod.fst hd₀) :
    d₀.1 ≤ sSup (Prod.fst '' 𝒟)) ((hdev d₀ hd₀).subset hx), ?_⟩
  refine Causality.isCauchySurfaceOn_sSup_of_directedOn ?_ (hanti _ _ hsol) ?_
  · rintro _ ⟨d, hd, rfl⟩ _ ⟨d', hd', rfl⟩
    by_cases h : d = d'
    · subst h
      exact ⟨d.1, mem_image_of_mem _ hd, le_rfl, le_rfl⟩
    · rcases hchain hd hd' h with h' | h'
      · exact ⟨d'.1, mem_image_of_mem _ hd', h'.1, le_rfl⟩
      · exact ⟨d.1, mem_image_of_mem _ hd, le_rfl, h'.1⟩
  · rintro _ ⟨d, hd, rfl⟩
    exact Causality.isCauchySurfaceOn_of_agree
      (fun V hV x y => hfollow (fun z hz => (hv d hd hz).symm) V hV x y) (hdev d hd).cauchy

/-! ### The developments as an abstract class -/

/-- **The developments of one initial value problem**, as a type: the pairs `(U, u)` with
`IsDevelopment sol cau S U u`. -/
abbrev Developments (sol : Opens M → (M → β) → Prop) (cau : (M → β) → Causality M) (S : Set M) :
    Type (max u v) :=
  {d : Opens M × (M → β) // IsDevelopment sol cau S d.1 d.2}

/-- **The developments as an abstract class** (§1): the carrier of `(U, u)` is its domain `U`, a
morphism `(U, u) → (U', u')` is the inclusion `U → U'` when `u = u'` on `U`. -/
def ersMor (sol : Opens M → (M → β) → Prop) (cau : (M → β) → Causality M) (S : Set M)
    (d d' : Developments sol cau S) (f : d.1.1 → d'.1.1) : Prop :=
  (∀ x, (f x : M) = x) ∧ EqOn d.1.2 d'.1.2 d.1.1

/-- A morphism of developments exists exactly when one extends the other. -/
theorem extends_ersMor_iff {d d' : Developments sol cau S} :
    AbstractDev.Extends (carrier := fun d : Developments sol cau S => d.1.1) (ersMor sol cau S) d d' ↔
      IsExtension d.1.1 d.1.2 d'.1.1 d'.1.2 := by
  constructor
  · rintro ⟨f, hf, heq⟩
    refine ⟨fun x hx => ?_, heq⟩
    have h := (f ⟨x, hx⟩).2
    rw [hf ⟨x, hx⟩] at h
    exact h
  · rintro ⟨hle, heq⟩
    exact ⟨fun x => ⟨x.1, hle x.2⟩, fun _ => rfl, heq⟩

/-- **The hypotheses of Chruściel's theorem hold for the developments** of an abstract initial
value problem on a fixed background: morphisms compose and are unique (inclusions), and chains
inherit (`isDevelopment_sSup_of_isChain`); the size bound is `AbstractDev.sizeBound_self`, the
developments being a type of the universe of `M × β`. -/
theorem ersMor_hypotheses [T2Space M] (hloc : SolutionLocal sol) (hglue : SolutionsGlue sol)
    (hfollow : CausalityFollows cau)
    (hanti : ∀ U u, sol U u → ∀ ⦃x y : M⦄, (cau u).le U x y → (cau u).le U y x → x = y) :
    AbstractDev.MorphismsCompose (carrier := fun d : Developments sol cau S => d.1.1) (ersMor sol cau S) ∧
      AbstractDev.UniqueMorphisms (carrier := fun d : Developments sol cau S => d.1.1) (ersMor sol cau S) ∧
      AbstractDev.ChainsInherit.{max u v} (carrier := fun d : Developments sol cau S => d.1.1) (ersMor sol cau S) := by
  refine ⟨⟨fun _ => ⟨fun _ => rfl, fun _ _ => rfl⟩, ?_⟩, ?_, ?_⟩
  · rintro X Y Z f g ⟨hf, hfe⟩ ⟨hg, hge⟩
    refine ⟨fun x => (hg (f x)).trans (hf x), fun x hx => (hfe hx).trans ?_⟩
    have := hge (f ⟨x, hx⟩).2
    rwa [hf ⟨x, hx⟩] at this
  · rintro X Y f g ⟨hf, -⟩ ⟨hg, -⟩
    funext x
    exact Subtype.ext ((hf x).trans (hg x).symm)
  · intro ι _ _ r X φ hX
    have hext : ∀ i j, r i j → IsExtension (X i).1.1 (X i).1.2 (X j).1.1 (X j).1.2 :=
      fun i j h => extends_ersMor_iff.1 ⟨φ h, hX.isMor h⟩
    have hc : IsChain (fun d d' : Opens M × (M → β) => IsExtension d.1 d.2 d'.1 d'.2)
        (range fun i => (X i).1) := by
      rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ -
      exact (hX.total i j).imp (hext i j) (hext j i)
    obtain ⟨i₀⟩ := ‹Nonempty ι›
    obtain ⟨v, hv, hdev⟩ := isDevelopment_sSup_of_isChain hloc hglue hfollow hanti
      ⟨_, mem_range_self i₀⟩ hc (by rintro _ ⟨i, rfl⟩; exact (X i).2)
    have hle : ∀ i, (X i).1.1 ≤ sSup (Prod.fst '' range fun i => (X i).1) :=
      fun i => le_sSup (mem_image_of_mem _ (mem_range_self i))
    refine ⟨⟨(_, v), hdev⟩, fun i x => ⟨x.1, hle i x.2⟩,
      fun i => ⟨fun _ => rfl, fun x hx => (hv _ (mem_range_self i) hx).symm⟩,
      fun i j h => funext fun x => Subtype.ext ((hX.isMor h).1 x)⟩

/-- **Maximal in the abstract sense is ERS's maximality** (`ghd_02_19.tex:117`). -/
theorem isMaximal_ersMor_iff {d : Developments sol cau S} :
    AbstractDev.IsMaximal (carrier := fun d : Developments sol cau S => d.1.1) (ersMor sol cau S) d ↔
      IsMaximalDevelopment sol cau S d.1.1 d.1.2 := by
  constructor
  · intro h
    refine ⟨d.2, fun U' u' h' hext => ?_⟩
    obtain ⟨f, hf⟩ := (extends_ersMor_iff (d := d) (d' := ⟨(U', u'), h'⟩)).2 hext
    exact (extends_ersMor_iff.1 (h ⟨(U', u'), h'⟩ f hf)).1
  · intro h Y f hf
    have hext := extends_ersMor_iff.1 ⟨f, hf⟩
    have hle : Y.1.1 ≤ d.1.1 := h.2 Y.1.1 Y.1.2 Y.2 hext
    exact extends_ersMor_iff.2 ⟨hle, fun x hx => (hext.2 (hle hx)).symm⟩

/-- **Every development extends to a maximal one** (ERS Remark 3.56, "an application of Zorn's
Lemma (!) to the set of globally hyperbolic extensions of Φ_a : U_a → ℝ shows that there exists
a MGHD which contains Φ_a : U_a → ℝ"): Chruściel's theorem for the class `ersMor`
(`AbstractDev.exists_isMaximal_of_chainsInherit`). -/
theorem exists_isMaximalDevelopment [T2Space M] (hloc : SolutionLocal sol)
    (hglue : SolutionsGlue sol) (hfollow : CausalityFollows cau)
    (hanti : ∀ U u, sol U u → ∀ ⦃x y : M⦄, (cau u).le U x y → (cau u).le U y x → x = y)
    {U₀ : Opens M} {u₀ : M → β} (h₀ : IsDevelopment sol cau S U₀ u₀) :
    ∃ (U : Opens M) (u : M → β), IsExtension U₀ u₀ U u ∧ IsMaximalDevelopment sol cau S U u := by
  obtain ⟨hcomp, -, hchain⟩ := ersMor_hypotheses (S := S) hloc hglue hfollow hanti
  obtain ⟨Z, f, hf, hZ⟩ :=
    AbstractDev.exists_isMaximal_of_chainsInherit hcomp hchain
      (⟨(U₀, u₀), h₀⟩ : Developments sol cau S)
  exact ⟨Z.1.1, Z.1.2, extends_ersMor_iff.1 ⟨f, hf⟩, isMaximal_ersMor_iff.1 hZ⟩

/-- **ERS19 Remark 3.56** (`ersrem:note_two_ghds_constructed`, unmarked): two developments that
differ at a common point (the conclusion of Theorem 3.45) extend to two maximal developments, and
"these two MGHDs are clearly distinct": they differ at that point. -/
theorem ers_remark_3_56 [T2Space M] (hloc : SolutionLocal sol) (hglue : SolutionsGlue sol)
    (hfollow : CausalityFollows cau)
    (hanti : ∀ U u, sol U u → ∀ ⦃x y : M⦄, (cau u).le U x y → (cau u).le U y x → x = y)
    {Ua Ub : Opens M} {ua ub : M → β} (ha : IsDevelopment sol cau S Ua ua)
    (hb : IsDevelopment sol cau S Ub ub) {x : M} (hx : x ∈ Ua ⊓ Ub) (hab : ua x ≠ ub x) :
    ∃ (Ua' Ub' : Opens M) (ua' ub' : M → β),
      IsExtension Ua ua Ua' ua' ∧ IsMaximalDevelopment sol cau S Ua' ua' ∧
      IsExtension Ub ub Ub' ub' ∧ IsMaximalDevelopment sol cau S Ub' ub' ∧
      x ∈ Ua' ⊓ Ub' ∧ ua' x ≠ ub' x ∧ ¬ (Ua' = Ub' ∧ EqOn ua' ub' Ua') := by
  obtain ⟨Ua', ua', hea, hma⟩ := exists_isMaximalDevelopment hloc hglue hfollow hanti ha
  obtain ⟨Ub', ub', heb, hmb⟩ := exists_isMaximalDevelopment hloc hglue hfollow hanti hb
  have hne : ua' x ≠ ub' x := by
    rw [← hea.2 hx.1, ← heb.2 hx.2]
    exact hab
  exact ⟨Ua', Ub', ua', ub', hea, hma, heb, hmb, ⟨hea.1 hx.1, heb.1 hx.2⟩, hne,
    fun ⟨_, h⟩ => hne (h (hea.1 hx.1))⟩

/-- **ERS19 Remark 3.56, "infinitely many distinct MGHDs", its abstract half**: a family of
developments differing pairwise at a common point extends to a family of maximal developments,
pairwise distinct. The family itself (infinitely many GHDs of the Born–Infeld data, "we leave the
details to the reader") is not constructed. -/
theorem ers_remark_3_56_family [T2Space M] (hloc : SolutionLocal sol)
    (hglue : SolutionsGlue sol) (hfollow : CausalityFollows cau)
    (hanti : ∀ U u, sol U u → ∀ ⦃x y : M⦄, (cau u).le U x y → (cau u).le U y x → x = y)
    {ι : Type*} {U : ι → Opens M} {u : ι → M → β} (hdev : ∀ i, IsDevelopment sol cau S (U i) (u i))
    (hdiff : Pairwise fun i j => ∃ x ∈ U i ⊓ U j, u i x ≠ u j x) :
    ∃ (V : ι → Opens M) (w : ι → M → β),
      (∀ i, IsExtension (U i) (u i) (V i) (w i) ∧ IsMaximalDevelopment sol cau S (V i) (w i)) ∧
      Pairwise fun i j => ¬ (V i = V j ∧ EqOn (w i) (w j) (V i)) := by
  choose V w hV using fun i => exists_isMaximalDevelopment hloc hglue hfollow hanti (hdev i)
  refine ⟨V, w, hV, fun i j hij ⟨_, h⟩ => ?_⟩
  obtain ⟨x, hx, hne⟩ := hdiff hij
  apply hne
  rw [(hV i).1.2 hx.1, (hV j).1.2 hx.2]
  exact h ((hV i).1.1 hx.1)

/-- **ERS19 Remark 3.56 under subluminality** (the Born–Infeld equation of Theorem 3.45 is
subluminal): `hanti` from curve nesting in a causal `Cm` (`antisymm_of_curveNestedOn`), the
hypotheses of `ers_remark_4_78`. -/
theorem ers_remark_3_56_of_curveNested [T2Space M] {Cm : Causality M} (hloc : SolutionLocal sol)
    (hglue : SolutionsGlue sol) (hfollow : CausalityFollows cau)
    (hsub : ∀ U u, sol U u → Causality.CurveNestedOn (cau u) Cm U)
    (harc : ∀ U u, sol U u → (cau u).CausallyArcConnectedOn U) (hm : Cm.IsCausal)
    {Ua Ub : Opens M} {ua ub : M → β} (ha : IsDevelopment sol cau S Ua ua)
    (hb : IsDevelopment sol cau S Ub ub) {x : M} (hx : x ∈ Ua ⊓ Ub) (hab : ua x ≠ ub x) :
    ∃ (Ua' Ub' : Opens M) (ua' ub' : M → β),
      IsExtension Ua ua Ua' ua' ∧ IsMaximalDevelopment sol cau S Ua' ua' ∧
      IsExtension Ub ub Ub' ub' ∧ IsMaximalDevelopment sol cau S Ub' ub' ∧
      x ∈ Ua' ⊓ Ub' ∧ ua' x ≠ ub' x ∧ ¬ (Ua' = Ub' ∧ EqOn ua' ub' Ua') :=
  ers_remark_3_56 hloc hglue hfollow
    (fun U u h => Causality.antisymm_of_curveNestedOn (harc U u h) (hsub U u h) hm) ha hb hx hab

end Developments

/-- **A witness** (kb/0011): on the timelike line, `S = {0}`, every function a solution on `ℝ`
(`sol U u := U = ⊤`), the causality the timelike line: two distinct maximal developments, from
the constants `0` and `1`. -/
theorem timelikeLine_ers_remark_3_56 :
    ∃ (Ua Ub : Opens ℝ) (ua ub : ℝ → ℝ),
      IsMaximalDevelopment (fun (U : Opens ℝ) (_ : ℝ → ℝ) => U = ⊤) (fun _ => timelikeLine) {0}
        Ua ua ∧
      IsMaximalDevelopment (fun (U : Opens ℝ) (_ : ℝ → ℝ) => U = ⊤) (fun _ => timelikeLine) {0}
        Ub ub ∧
      ¬ (Ua = Ub ∧ EqOn ua ub Ua) := by
  have hloc : SolutionLocal (fun (U : Opens ℝ) (_ : ℝ → ℝ) => U = ⊤) := fun _ _ _ _ h => h
  have hglue : SolutionsGlue (fun (U : Opens ℝ) (_ : ℝ → ℝ) => U = ⊤) := by
    intro 𝒰 _ ⟨U₀, hU₀⟩ h
    exact top_le_iff.1 (by rw [← h U₀ hU₀]; exact le_sSup hU₀)
  have hfollow : CausalityFollows (fun _ : ℝ → ℝ => timelikeLine) :=
    fun _ _ _ _ _ _ _ _ => Iff.rfl
  have hanti : ∀ (U : Opens ℝ) (u : ℝ → ℝ), U = ⊤ → ∀ ⦃x y : ℝ⦄,
      timelikeLine.le U x y → timelikeLine.le U y x → x = y :=
    fun _ _ _ _ _ h h' =>
      timelikeLine_isCausal (timelikeLine.le_mono le_top h) (timelikeLine.le_mono le_top h')
  have hdev : ∀ a : ℝ, IsDevelopment (fun (U : Opens ℝ) (_ : ℝ → ℝ) => U = ⊤)
      (fun _ => timelikeLine) {0} ⊤ (fun _ => a) :=
    fun _ => ⟨rfl, fun _ _ => trivial, timelikeLine_isCauchySurface_zero⟩
  obtain ⟨Ua', Ub', ua', ub', -, hma, -, hmb, -, -, hdist⟩ :=
    ers_remark_3_56 hloc hglue hfollow hanti (hdev 0) (hdev 1) (x := 0) ⟨trivial, trivial⟩
      (by simp)
  exact ⟨Ua', Ub', ua', ub', hma, hmb, hdist⟩

end Causal
