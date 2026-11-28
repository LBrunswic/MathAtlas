import Benzecri.Chapter3.FacetteDuale

/-!
# Chapter 3 § 4 — `𝒟∘𝒟∘𝒟 = 𝒟` (Prop. 8), and `𝒟∘𝒟(F) = F` iff `F̄` is the section of `W` by a hyperplane (Prop. 9)

J.-P. Benzécri, *Sur les variétés localement affines et localement projectives*, Bull. SMF 88
(1960) 229–332, Chapter 3 § 4, journal p. 275; transcription
`papers/benzecri/legacy/labeled/benzecri1960_ch3.tex` (TO BE CHECKED BY THE AUTHOR, OQ-160),
checked against the page image (PDF p. 48). Target T-bz-c3-facette-exposee. On `S(n)` with the dot
product (`dotPairing n`); `𝒟` is `Benzecri.Sphere.facetteDuale` (Chapter3/FacetteDuale.lean), so
`𝒟∘𝒟(F)` is `facetteDuale (D W) (facetteDuale W F)`, a facette of `D(D(W)) = W̄`
(`D_D_eq_closure`), and `𝒟∘𝒟∘𝒟(F)` is a facette of `D(D(D(W))) = D(W)` (`D_D_D`).

* **`bzprop:c3s4p8_D_cube`** — `benzecri1960_ch3.tex:1072` (Prop. 8, l.1072–1074; proof
  l.1076–1085) — under both live readings of OQ-165 (c), for every convex part `W` (no
  closedness): `Benzecri.Sphere.prop8_facetteDuale` (genuine facettes: as soon as `𝒟(F)` is a
  facette, `𝒟∘𝒟(F)` and `𝒟∘𝒟∘𝒟(F)` are facettes and `𝒟∘𝒟∘𝒟(F) = 𝒟(F)`) and
  `Benzecri.Sphere.prop8_facetteDualeExt` (`𝒟` extended to the facette `∅` of dimension `−1` by
  Prop. 7's minimality, `facetteDualeExt`: the identity for every extended facette).
* `bzprop:c3s4p9_facette_exposee` — `benzecri1960_ch3.tex:1087` (Prop. 9, l.1087–1090; proof
  l.1092–1100) — NOT marked: `Benzecri.Sphere.prop9_facetteDuale`, proved for `W` closed and
  `𝒟∘𝒟(F)` read with `𝒟(F)` a genuine facette; false for a non-closed convex part
  (`FacetteExposeeInstance.not_prop9_nonclosed`) and imprecise under the extended reading of
  OQ-165 (c) (`FacetteExposeeInstance.prop9_ext_imprecise`). The `𝒟(F) = ∅` side:
  `not_section_of_facetteDuale_eq_empty`.
* Instances (`Benzecri.FacetteExposeeInstance`): the vertex `{s(e₀)}` of the closed simplex `T`
  of `S(n + 1)` is exposed, `vertex0_section` (`{s(e₀)} = T ∩ ⟨·, (0, 1, …, 1)⟩^⊥`) and
  `vertex0_exposee` (`𝒟∘𝒟({s(e₀)}) = {s(e₀)}`); the interior facette of `T` (`interieur`,
  `facetteDuale_interieur`: `𝒟 = ∅`); the triangle minus a vertex (`triangleMoinsSommet`, convex,
  `D = T`, `facetteK_triangleMoinsSommet`). The stadium of p. 276 (free text, no row) is not
  formalized.

> La correspondance $\Dc$ n'est pas nécessairement biunivoque, mais voici quelques propriétés de
> $\Dc$ :
>
> **Proposition 8.** $\Dc\circ\Dc\circ\Dc=\Dc$.
>
> *Démonstration.* $\Dc\circ\Dc(F)$ n'est autre que la facette de $W$ minimale au sens de
> $\alpha$ parmi celles $F_i$ qui vérifient $\langle F_i, \Dc(F)\rangle=0$.
> $\Dc\circ\Dc\circ\Dc(F)$ est la facette de $D(W)$ minimale parmi celles $F'$ qui vérifient
> $\langle\Dc\circ\Dc(F), F'\rangle=0$. Or, $\Dc(F)$ est minimale parmi celles $F'$ vérifiant
> $\langle F, F'\rangle=0$, donc *a fortiori* parmi celles vérifiant
> $\langle\Dc\circ\Dc(F), F'\rangle=0$.
>
> **Proposition 9.** Une facette $F$ vérifie $\Dc\circ\Dc(F)=F$ si et seulement si
> $\overline{F}$ est l'intersection de $W$ avec un hyperplan.
>
> *Démonstration.* Si $\Dc\circ\Dc(F)=F$, soit $p\in\Dc(F)$, $\overline{F}$ n'est autre que
> l'intersection de $W$ avec l'hyperplan frontière de $D(\{p\})$. Réciproquement, si
> $\overline{F}=W\cap h$, où $h$ est l'hyperplan frontière de $D(\{p\})$, $p\in W$, $F$ est
> transformée par $\Dc$ de la facette $F'$ de $p$, donc
> $\Dc\circ\Dc(F)=\Dc\circ\Dc\circ\Dc(F')=\Dc(F')=F$.

## The proofs formalized

Prop. 8 (genuine). With `F₁ = 𝒟(F)`, `G = 𝒟(F₁)`, `H = 𝒟(G)`: every point of `F` lies in
`D(D(W)) = W̄` and is orthogonal to `F₁`, so `F ⊆ Ḡ = D((D W)_p)` and `G ≠ ∅`; `p ∈ F₁` lies in
`D(D(D W)) = D(W)` and is orthogonal to `G`, so `H ≠ ∅`. Prop. 7 for `D(W)` (`⟨G, F₁⟩ = 0`) gives
`H α F₁`; `⟨G, H⟩ = 0` passes to `Ḡ ⊇ F` (orthogonality to a point is a closed condition,
`isClosed_setOf_orthPts`), so `⟨F, H⟩ = 0` and Prop. 7 for `W` gives `F₁ α H`; α is antisymmetric on
facettes. This is the printed « a fortiori » with `F ⊆ closure(𝒟∘𝒟(F))` in place of
`𝒟∘𝒟(F) α F`, which needs no closedness of `W`. Prop. 8 (extended): if `𝒟(F) = ∅` then
`𝒟∘𝒟(F)` is the α-least facette `R` of `W̄`, and no point of `D(W)` is orthogonal to the least
point `r` (it would be orthogonal to every point of `W̄`, `orthPts_of_alphaK_left`, hence lie in
`D(W_a) = ∅`), so `𝒟(R) = ∅`; if `F = ∅`, `𝒟(∅) = R₁` is the least facette of `D(W)`, and `𝒟(𝒟(R₁))`
is `R₁` by Prop. 7 one way and leastness the other (or `∅ ↦ R₁` again when `𝒟(R₁) = ∅`).

Prop. 9 (⇒) is the printed proof: `F̄ = closure(𝒟∘𝒟(F)) = D((D W)_p) = W ∩ p^⊥` (Prop. 3). (⇐) The
printed proof starts from a hyperplane already known to be `∂D({p})`, `p ∈ D(W)` (« $p\in W$ »
read `p ∈ D(W)`, OQ-160 (a)); the statement allows any hyperplane, so first
`supports_of_closure_eq`: a hyperplane `h` with `F̄ = W ∩ h` leaves `W` on one side (if
`l(x) < 0 < l(y)` for `x`, `y ∈ W′`, the point `Z = cA + l(y)x − l(x)y`, `a ∈ F`, lies in `W ∩ h = F̄`, so
`a α Z α y` and `y` lies in the support of `F`, inside `h`). Then the printed argument:
`F = 𝒟(F′)`, `F′` the facette of `p` in `D(W)` (uniqueness of the facette with closure `D((D W)_p)`),
and Prop. 8 for `D(W)`.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| § 4 standing: « $E$ est $\R^{n+1}$ … $\sum_i x_iy_i$ » | ✓ carried: `S n`, `dotPairing n` |
| « $W\in K(S(n))$ » (Prop. 6, the domain of `𝒟`) | ✓ carried by Prop. 8: `IsConvexPart W`, no closedness; ⚠ strengthened: Prop. 9 adds `IsClosed W` (needed: `not_prop9_nonclosed`) |
| Prop. 8 « $\Dc\circ\Dc\circ\Dc=\Dc$ » | ✓ carried, as an identity of partial maps (genuine) and of total maps (extended) |
| Prop. 9 « une facette $F$ » | ✓ carried: `IsFacetteK W F` |
| Prop. 9 « $\Dc\circ\Dc(F)=F$ » | ⚠ reading: `𝒟(F)` a genuine facette and `𝒟(𝒟(F)) = F`; under the extended reading the statement fails (`prop9_ext_imprecise`) |
| Prop. 9 « un hyperplan » | ✓ carried, any hyperplane: `IsHyperplane H` (Chapter 1, p. 234), not only a supporting one |
| Prop. 9's proof « $p\in W$ » | read `p ∈ D(W)` (OQ-160 (a)); the statement is unaffected |

## SCOPE (disclosed)

* No `sorry`, no axiom beyond the standard three.
* **Prop. 8 is marked**: `prop8_facetteDuale` and `prop8_facetteDualeExt` cover both live readings
  of « facette » in Prop. 6 (OQ-165 (c)), for every convex part `W`. The literal `facetteDuale`
  at `F = ∅` is a choice among all extended facettes (Chapter3/FacetteDuale.lean) and is no
  reading; it is never used at `∅` here. `𝒟(∅)` is defined by the minimality of l.1064
  (« la facette minimale (au sens de α) parmi celles F′ qui vérifient ⟨F, F′⟩ = 0 »), which at
  `F = ∅` selects the α-least facette of `D(W)`. The mixed reading (∅ admitted as a value of `𝒟`
  but not as an argument) is not live: under it `𝒟` would not be a map on the facettes of `D(W)`
  (its output `∅` could not be fed back), so `𝒟∘𝒟∘𝒟` would not be defined there.
* **Prop. 9 is not marked**: it needs `W` closed (the printed proof treats `𝒟∘𝒟(F)` as a facette
  of `W`, i.e. `D(D(W)) = W`); without it `not_prop9_nonclosed` is a counterexample in `S(2)` with
  every iterate genuine. Under the extended reading of OQ-165 (c) it fails at the interior
  facette of the closed simplex (`prop9_ext_imprecise`, the dimension `−1` case).
* `facetteLeast K` is the facette of an α(K)-least point (`exists_alphaK_least`), `∅` if `K = ∅`;
  `facetteDualeExt W ∅ = facetteLeast (D W)` is Prop. 7's minimality at `F = ∅`
  (`prop7_facetteDualeExt_empty`).
* General lemmas (candidates upstream): `D_D_eq_closure`, `D_D_D`, `orthFacettes_comm`,
  `isClosed_setOf_orthPts`, `isFacetteK_of_ext`, `IsFacetteKExt.subset`, `facetteDuale_subset`,
  `mem_closure_facetteDuale_iff`, `exists_dotPairing_eq`, `isHyperplane_orth`,
  `supports_of_closure_eq`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

open Set Filter Topology

namespace Benzecri

namespace Sphere

variable {n : ℕ}

/-- `D(D(W)) = W̄`. -/
theorem D_D_eq_closure {W : Set (S n)} (hW : IsConvexPart W) :
    D (dotPairing n) (D (dotPairing n) W) = closure W := by
  have := D'_D_eq_closure (dotPairing n) (identifiesDual_dotPairing n) hW
  rwa [D'_dotPairing] at this

/-- `D(D(D(W))) = D(W)`. -/
theorem D_D_D (W : Set (S n)) :
    D (dotPairing n) (D (dotPairing n) (D (dotPairing n) W)) = D (dotPairing n) W := by
  rw [D_D_eq_closure (claim_a_convexPart _ W), (isClosed_D_dot W).closure_eq]

theorem orthFacettes_comm {F F' : Set (S n)} : OrthFacettes F F' ↔ OrthFacettes F' F :=
  ⟨fun h m hm m' hm' => orthPts_comm.1 (h m' hm' m hm),
    fun h m hm m' hm' => orthPts_comm.1 (h m' hm' m hm)⟩

theorem isClosed_setOf_orthPts (p : S n) : IsClosed {x : S n | OrthPts x p} := by
  have : {x : S n | OrthPts x p} =
      D (dotPairing n) {p} ∩ (fun x : S n => -x) ⁻¹' D (dotPairing n) {p} := by
    ext x; exact orthPts_iff_D
  rw [this]
  exact (isClosed_D_dot _).inter ((isClosed_D_dot _).preimage Sphere.continuous_neg)

theorem isFacetteK_of_ext {K G : Set (S n)} (hK : IsConvexPart K) (hG : IsFacetteKExt K G)
    (hne : G.Nonempty) : IsFacetteK K G := by
  rcases (isFacetteKExt_iff hK).1 hG with h | ⟨rfl, -⟩
  · exact h
  · exact absurd hne (by simp)

theorem IsFacetteKExt.subset {K G : Set (S n)} (hK : IsConvexPart K) (hG : IsFacetteKExt K G) :
    G ⊆ K := by
  rcases (isFacetteKExt_iff hK).1 hG with h | ⟨rfl, -⟩
  · exact h.subset
  · exact empty_subset _

theorem facetteDuale_subset (W F : Set (S n)) : facetteDuale W F ⊆ D (dotPairing n) W := by
  unfold facetteDuale
  split_ifs with h
  · exact h.choose_spec.1.subset (claim_a_convexPart _ W)
  · exact empty_subset _

/-- The closure of `𝒟(F)`, read through Prop. 3. -/
theorem mem_closure_facetteDuale_iff {W : Set (S n)} (hW : IsConvexPart W) {F : Set (S n)}
    (hF : IsFacetteK W F) {a : S n} (ha : a ∈ F) {m : S n} :
    m ∈ closure (facetteDuale W F) ↔ m ∈ D (dotPairing n) W ∧ OrthPts m a := by
  rw [(facetteDuale_spec hW hF).2 a ha, prop3_coneAppui a hW (hF.subset ha)]; rfl
/-- **Prop. 8** where `𝒟(F)` is a genuine facette. -/
theorem prop8_facetteDuale {W : Set (S n)} (hW : IsConvexPart W) {F : Set (S n)}
    (hF : IsFacetteK W F) (hne : (facetteDuale W F).Nonempty) :
    IsFacetteK (D (dotPairing n) W) (facetteDuale W F) ∧
    IsFacetteK (D (dotPairing n) (D (dotPairing n) W))
      (facetteDuale (D (dotPairing n) W) (facetteDuale W F)) ∧
    IsFacetteK (D (dotPairing n) W)
      (facetteDuale (D (dotPairing n) (D (dotPairing n) W))
        (facetteDuale (D (dotPairing n) W) (facetteDuale W F))) ∧
    facetteDuale (D (dotPairing n) (D (dotPairing n) W))
        (facetteDuale (D (dotPairing n) W) (facetteDuale W F)) = facetteDuale W F := by
  set K := D (dotPairing n) W with hKdef
  have hK : IsConvexPart K := claim_a_convexPart _ W
  have hK2 : IsConvexPart (D (dotPairing n) K) := claim_a_convexPart _ K
  have hDD : D (dotPairing n) K = closure W := D_D_eq_closure hW
  have hDDD : D (dotPairing n) (D (dotPairing n) K) = K := D_D_D W
  set F1 := facetteDuale W F with hF1def
  have hF1 : IsFacetteK K F1 := isFacetteK_of_ext hK (facetteDuale_spec hW hF).1 hne
  have o1 : OrthFacettes F F1 := orthFacettes_facetteDuale hW hF
  set G := facetteDuale K F1 with hGdef
  obtain ⟨p, hp⟩ := hne
  have hFG : F ⊆ closure G := by
    intro a ha
    rw [mem_closure_facetteDuale_iff hK hF1 hp]
    exact ⟨hDD ▸ subset_closure (hF.subset ha), o1 a ha p hp⟩
  obtain ⟨a₀, ha₀⟩ := hF.nonempty
  have hG : IsFacetteK (D (dotPairing n) K) G := by
    refine isFacetteK_of_ext hK2 (facetteDuale_spec hK hF1).1 ?_
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    have := hFG ha₀
    rw [h, closure_empty] at this
    exact this
  have o2 : OrthFacettes F1 G := orthFacettes_facetteDuale hK hF1
  set H := facetteDuale (D (dotPairing n) K) G with hHdef
  obtain ⟨g, hg⟩ := hG.nonempty
  have hpK : p ∈ D (dotPairing n) (D (dotPairing n) K) := by
    rw [hDDD]; exact hF1.subset hp
  have hpH : p ∈ closure H := by
    rw [mem_closure_facetteDuale_iff hK2 hG hg]
    exact ⟨hpK, o2 p hp g hg⟩
  have hH : IsFacetteK K H := by
    have h := isFacetteK_of_ext (claim_a_convexPart _ _) (facetteDuale_spec hK2 hG).1
      (closure_nonempty_iff.1 ⟨p, hpH⟩)
    rwa [hDDD] at h
  have o3 : OrthFacettes G H := orthFacettes_facetteDuale hK2 hG
  have hF1' : IsFacetteK (D (dotPairing n) (D (dotPairing n) K)) F1 := by rw [hDDD]; exact hF1
  have le1 : FacetteKLE (D (dotPairing n) (D (dotPairing n) K)) H F1 :=
    prop7_facetteDuale hK2 hG hF1' (orthFacettes_comm.1 o2)
  rw [hDDD] at le1
  have oFH : OrthFacettes F H := by
    intro a ha h hh
    have hcl : closure G ⊆ {x | OrthPts x h} :=
      closure_minimal (fun x hx => o3 x hx h hh) (isClosed_setOf_orthPts h)
    exact hcl (hFG ha)
  have le2 : FacetteKLE K F1 H := prop7_facetteDuale hW hF hH oFH
  have hHF1 : H = F1 := FacetteKLE.antisymm hK hH hF1 le1 le2
  exact ⟨hF1, hG, hH, hHF1⟩
/-- The α-least facette of `K` (the facette of a point `a` with `a α(K) b` for every `b ∈ K`;
`∅` when there is none, i.e. when `K = ∅`). -/
noncomputable def facetteLeast (K : Set (S n)) : Set (S n) :=
  open Classical in
  if h : ∃ a ∈ K, ∀ b ∈ K, AlphaK K a b then facetteK K h.choose else ∅

theorem facetteLeast_eq {K : Set (S n)} (hK : IsConvexPart K) {a : S n} (ha : a ∈ K)
    (hmin : ∀ b ∈ K, AlphaK K a b) : facetteLeast K = facetteK K a := by
  have h : ∃ a ∈ K, ∀ b ∈ K, AlphaK K a b := ⟨a, ha, hmin⟩
  rw [facetteLeast, dif_pos h]
  obtain ⟨hc, hcmin⟩ := h.choose_spec
  exact facetteK_eq_of_fk hK ⟨hcmin a ha, hmin _ hc⟩

theorem facetteLeast_empty : facetteLeast (∅ : Set (S n)) = ∅ := by
  rw [facetteLeast, dif_neg (by simp)]

theorem facetteLeast_spec {K : Set (S n)} (hK : IsConvexPart K) (hne : K.Nonempty) :
    IsFacetteK K (facetteLeast K) ∧ ∀ f, IsFacetteK K f → FacetteKLE K (facetteLeast K) f := by
  obtain ⟨a, ha, hmin⟩ := exists_alphaK_least hK hne
  rw [facetteLeast_eq hK ha hmin]
  refine ⟨⟨a, ha, rfl⟩, fun f hf => ?_⟩
  obtain ⟨b, hb⟩ := hf.nonempty
  exact ⟨a, mem_facetteK_self ha, b, hb, hmin b (hf.subset hb)⟩

/-- **`𝒟` extended to the facette `∅`** by Prop. 7's minimality: `𝒟(∅)` is the α-least facette
of `D(W)` among those `F'` with `⟨∅, F'⟩ = 0`, i.e. among all of them. -/
noncomputable def facetteDualeExt (W F : Set (S n)) : Set (S n) :=
  open Classical in
  if F = ∅ then facetteLeast (D (dotPairing n) W) else facetteDuale W F

theorem facetteDualeExt_of_ne {W F : Set (S n)} (h : F.Nonempty) :
    facetteDualeExt W F = facetteDuale W F := by
  rw [facetteDualeExt, if_neg h.ne_empty]

theorem facetteDualeExt_empty (W : Set (S n)) :
    facetteDualeExt W ∅ = facetteLeast (D (dotPairing n) W) := by
  rw [facetteDualeExt, if_pos rfl]

/-- The extension is Prop. 7's characterization at `F = ∅`: `𝒟(∅)` is a facette of `D(W)` below
every facette of `D(W)`. -/
theorem prop7_facetteDualeExt_empty {W : Set (S n)} (hne : (D (dotPairing n) W).Nonempty) :
    IsFacetteK (D (dotPairing n) W) (facetteDualeExt W ∅) ∧
      ∀ F', IsFacetteK (D (dotPairing n) W) F' → OrthFacettes ∅ F' →
        FacetteKLE (D (dotPairing n) W) (facetteDualeExt W ∅) F' := by
  rw [facetteDualeExt_empty]
  obtain ⟨h1, h2⟩ := facetteLeast_spec (claim_a_convexPart _ W) hne
  exact ⟨h1, fun F' hF' _ => h2 F' hF'⟩

/-- **Prop. 8 with `𝒟` extended to `∅`** (`facetteDualeExt`): `𝒟∘𝒟∘𝒟(F) = 𝒟(F)` for every
extended facette `F` of `W`. -/
theorem prop8_facetteDualeExt {W : Set (S n)} (hW : IsConvexPart W) {F : Set (S n)}
    (hF : IsFacetteKExt W F) :
    facetteDualeExt (D (dotPairing n) (D (dotPairing n) W))
        (facetteDualeExt (D (dotPairing n) W) (facetteDualeExt W F)) = facetteDualeExt W F := by
  set K := D (dotPairing n) W with hKdef
  have hK : IsConvexPart K := claim_a_convexPart _ W
  have hK2 : IsConvexPart (D (dotPairing n) K) := claim_a_convexPart _ K
  have hDD : D (dotPairing n) K = closure W := D_D_eq_closure hW
  have hDDD : D (dotPairing n) (D (dotPairing n) K) = K := D_D_D W
  rcases (isFacetteKExt_iff hW).1 hF with hF | ⟨rfl, -⟩
  · obtain ⟨a, ha⟩ := hF.nonempty
    rw [facetteDualeExt_of_ne ⟨a, ha⟩]
    rcases (facetteDuale W F).eq_empty_or_nonempty with h0 | hne
    · -- case `𝒟(F) = ∅`
      rw [h0, facetteDualeExt_empty]
      have hWne : (D (dotPairing n) K).Nonempty := ⟨a, hDD ▸ subset_closure (hF.subset ha)⟩
      obtain ⟨hR, -⟩ := facetteLeast_spec hK2 hWne
      rw [facetteDualeExt_of_ne hR.nonempty]
      obtain ⟨r, hr⟩ := hR.nonempty
      obtain ⟨r', hr'K, hmin⟩ := exists_alphaK_least hK2 hWne
      have hRr : facetteLeast (D (dotPairing n) K) = facetteK (D (dotPairing n) K) r' :=
        facetteLeast_eq hK2 hr'K hmin
      apply subset_empty_iff.1
      intro m hm
      have hmc : m ∈ closure (facetteDuale (D (dotPairing n) K)
          (facetteLeast (D (dotPairing n) K))) := subset_closure hm
      rw [mem_closure_facetteDuale_iff hK2 hR hr] at hmc
      obtain ⟨hmD, hmr⟩ := hmc
      rw [hDDD] at hmD
      -- `r α a` in `D(K) = W̄`, so `⟨a, m⟩ = 0`
      have hra : AlphaK (D (dotPairing n) K) r a := by
        rw [hRr] at hr
        exact alphaK_trans hK2 hr.2 (hmin a (hDD ▸ subset_closure (hF.subset ha)))
      have hmD' : m ∈ D (dotPairing n) (D (dotPairing n) K) := by rw [hDDD]; exact hmD
      have ham : OrthPts a m := orthPts_of_alphaK_left hK2 hra hmD' (orthPts_comm.1 hmr)
      have : m ∈ closure (facetteDuale W F) := by
        rw [mem_closure_facetteDuale_iff hW hF ha]
        exact ⟨hmD, orthPts_comm.1 ham⟩
      rw [h0, closure_empty] at this
      exact this
    · -- case `𝒟(F) ≠ ∅`: Prop. 8 for genuine facettes
      obtain ⟨-, hG, -, hH⟩ := prop8_facetteDuale hW hF hne
      rw [facetteDualeExt_of_ne hne, facetteDualeExt_of_ne hG.nonempty, hH]
  · -- case `F = ∅`
    rw [facetteDualeExt_empty]
    rcases (facetteDualeExt K (facetteLeast K)).eq_empty_or_nonempty with h0 | hne
    · rw [h0, facetteDualeExt_empty, hDDD]
    rw [facetteDualeExt_of_ne hne]
    rcases K.eq_empty_or_nonempty with hK0 | hKne
    · have h := facetteDuale_subset (D (dotPairing n) K) (facetteDualeExt K (facetteLeast K))
      rw [hDDD] at h
      rw [subset_empty_iff.1 (h.trans hK0.subset)]
      show ∅ = facetteLeast K
      rw [hK0, facetteLeast_empty]
    obtain ⟨hR, hRmin⟩ := facetteLeast_spec hK hKne
    rw [facetteDualeExt_of_ne hR.nonempty] at hne ⊢
    have hG : IsFacetteK (D (dotPairing n) K) (facetteDuale K (facetteLeast K)) :=
      isFacetteK_of_ext hK2 (facetteDuale_spec hK hR).1 hne
    have o2 : OrthFacettes (facetteLeast K) (facetteDuale K (facetteLeast K)) :=
      orthFacettes_facetteDuale hK hR
    obtain ⟨g, hg⟩ := hG.nonempty
    obtain ⟨r, hr⟩ := hR.nonempty
    have hrH : r ∈ closure (facetteDuale (D (dotPairing n) K) (facetteDuale K (facetteLeast K))) := by
      rw [mem_closure_facetteDuale_iff hK2 hG hg, hDDD]
      exact ⟨hR.subset hr, o2 r hr g hg⟩
    have hH : IsFacetteK K
        (facetteDuale (D (dotPairing n) K) (facetteDuale K (facetteLeast K))) := by
      have h := isFacetteK_of_ext (claim_a_convexPart _ _) (facetteDuale_spec hK2 hG).1
        (closure_nonempty_iff.1 ⟨r, hrH⟩)
      rwa [hDDD] at h
    have hR' : IsFacetteK (D (dotPairing n) (D (dotPairing n) K)) (facetteLeast K) := by
      rw [hDDD]; exact hR
    have le1 := prop7_facetteDuale hK2 hG hR' (orthFacettes_comm.1 o2)
    rw [hDDD] at le1
    exact FacetteKLE.antisymm hK hH hR le1 (hRmin _ hH)
/-- Every linear form on `ℝⁿ⁺¹` is `⟨·, P⟩`. -/
theorem exists_dotPairing_eq (l : Module.Dual ℝ (Fin (n + 1) → ℝ)) :
    ∃ P : Fin (n + 1) → ℝ, ∀ v, l v = dotPairing n v P := by
  refine ⟨fun i => l (Pi.single i 1), fun v => ?_⟩
  rw [dotPairing_apply]
  conv_lhs => rw [show v = ∑ i, v i • (Pi.single i 1 : Fin (n + 1) → ℝ) by
    funext j; simp [Finset.sum_apply, Pi.single_apply]]
  simp [map_sum, smul_eq_mul]

/-- The hyperplane `⟨·, p⟩ = 0`. -/
theorem isHyperplane_orth (p : S n) :
    IsHyperplane {x : S n | OrthPts x p} := by
  set P := Module.Ray.someVector p
  have hP : P ≠ 0 := Module.Ray.someVector_ne_zero p
  set l : Module.Dual ℝ (Fin (n + 1) → ℝ) := (dotPairing n).flip P
  have hl : l ≠ 0 := by
    intro h
    have := LinearMap.congr_fun h P
    simp only [l, LinearMap.flip_apply, LinearMap.zero_apply] at this
    exact hP (dotPairing_self_eq_zero this)
  have : {x : S n | OrthPts x p} = linearSubvariety (LinearMap.ker l) := by
    ext x
    induction x using ind with
    | h v hv =>
    rw [mem_setOf_eq, mk_mem_linearSubvariety hv, orthPts_iff (isRep_mk v hv)
      (exists_isRep_someVector p), LinearMap.mem_ker]
    rfl
  rw [this]
  exact isHyperplane_linearSubvariety_ker hl

/-- A hyperplane meeting a convex part `W` in the closure of one of its facettes supports `W`. -/
theorem supports_of_closure_eq {W : Set (S n)} (hW : IsConvexPart W) {F : Set (S n)}
    (hF : IsFacetteK W F) {l : Module.Dual ℝ (Fin (n + 1) → ℝ)}
    (h : closure F = W ∩ linearSubvariety (LinearMap.ker l)) :
    (∀ x ∈ kPrime W, 0 ≤ l x) ∨ (∀ x ∈ kPrime W, l x ≤ 0) := by
  by_contra hc
  simp only [not_or, not_forall, not_le] at hc
  obtain ⟨⟨x, hxk, hx⟩, ⟨y, hyk, hy⟩⟩ := hc
  obtain ⟨a, ha⟩ := hF.nonempty
  obtain ⟨A, hA⟩ : ∃ A, IsRep A a := ⟨_, exists_isRep_someVector a⟩
  have hAk : A ∈ kPrime W := mem_kPrime_of_isRep hA (hF.subset ha)
  have hacl : a ∈ closure F := subset_closure ha
  rw [h] at hacl
  have hlA : l A = 0 := by
    obtain ⟨hA0, rfl⟩ := hA
    exact (mk_mem_linearSubvariety hA0).1 hacl.2
  set s := l y
  set t := -l x
  have hs : 0 < s := hy
  have ht : 0 < t := by simp only [t]; linarith
  have key : ∃ c : ℝ, 0 < c ∧ c • A + t • y + s • x ≠ 0 := by
    by_cases h1 : (1 : ℝ) • A + t • y + s • x = 0
    · refine ⟨2, by norm_num, fun h2 => hA.ne_zero ?_⟩
      have : (2 : ℝ) • A + t • y + s • x - ((1 : ℝ) • A + t • y + s • x) = A := by module
      rw [← this, h1, h2, sub_zero]
    · exact ⟨1, one_pos, h1⟩
  obtain ⟨c, hc, hZ0⟩ := key
  set Z := c • A + t • y + s • x
  have hZk : Z ∈ kPrime W :=
    add_mem_kPrime hW (add_mem_kPrime hW (smul_mem_kPrime hAk hc.le) (smul_mem_kPrime hyk ht.le))
      (smul_mem_kPrime hxk hs.le)
  have hlZ : l Z = 0 := by
    simp only [Z, map_add, map_smul, smul_eq_mul, hlA, t, s]; ring
  have hzW : mk Z hZ0 ∈ W := mem_of_isRep_of_mem_kPrime (isRep_mk Z hZ0) hZk
  have hzcl : mk Z hZ0 ∈ closure F := by
    rw [h]; exact ⟨hzW, (mk_mem_linearSubvariety hZ0).2 hlZ⟩
  have h1 : AlphaK W a (mk Z hZ0) := alphaK_of_mem_closure hW hF ha hzW hzcl
  have hy0 : y ≠ 0 := by
    rintro rfl; simp [s] at hs
  have hyW' : mk y hy0 ∈ W := mem_of_isRep_of_mem_kPrime (isRep_mk y hy0) hyk
  have h2 : AlphaK W (mk Z hZ0) (mk y hy0) := by
    rw [alphaK_iff hW (isRep_mk Z hZ0) (isRep_mk y hy0), alphaW_iff_extend (convex_kPrime hW)]
    refine ⟨hZk, hyk, t, ht, ?_⟩
    have e : Z + t • (Z - y) = ((1 + t) * c) • A + (t * t) • y + ((1 + t) * s) • x := by
      simp only [Z]; module
    rw [e]
    exact add_mem_kPrime hW (add_mem_kPrime hW (smul_mem_kPrime hAk (by positivity))
      (smul_mem_kPrime hyk (by positivity))) (smul_mem_kPrime hxk (by positivity))
  have h3 := (alphaK_iff_mem_supportK hW hF ha hyW').1 (alphaK_trans hW h1 h2)
  have hFL : F ⊆ linearSubvariety (LinearMap.ker l) :=
    fun b hb => (h ▸ subset_closure hb : b ∈ W ∩ _).2
  have := supportK_subset hFL h3
  rw [mk_mem_linearSubvariety hy0, LinearMap.mem_ker] at this
  exact hs.ne' this
/-- **Prop. 9** for a closed `W`, `𝒟(F)` a genuine facette. -/
theorem prop9_facetteDuale {W : Set (S n)} (hW : IsConvexPart W) (hWc : IsClosed W)
    {F : Set (S n)} (hF : IsFacetteK W F) :
    ((facetteDuale W F).Nonempty ∧ facetteDuale (D (dotPairing n) W) (facetteDuale W F) = F) ↔
      ∃ H, IsHyperplane H ∧ closure F = W ∩ H := by
  have hK : IsConvexPart (D (dotPairing n) W) := claim_a_convexPart _ W
  have hDDW : D (dotPairing n) (D (dotPairing n) W) = W := by
    rw [D_D_eq_closure hW, hWc.closure_eq]
  constructor
  · rintro ⟨hne, h2⟩
    obtain ⟨hF1, -, -, -⟩ := prop8_facetteDuale hW hF hne
    obtain ⟨p, hp⟩ := hne
    refine ⟨{x | OrthPts x p}, isHyperplane_orth p, ?_⟩
    ext m
    rw [← h2, mem_closure_facetteDuale_iff hK hF1 hp, hDDW]
    rfl
  · rintro ⟨H, ⟨L, hL, rfl⟩, h⟩
    obtain ⟨l, hl0, hker⟩ := exists_dual_ker_eq hL
    rw [← hker] at h
    obtain ⟨l', hl'0, hker', hpos⟩ : ∃ l' : Module.Dual ℝ (Fin (n + 1) → ℝ), l' ≠ 0 ∧
        LinearMap.ker l' = LinearMap.ker l ∧ ∀ x ∈ kPrime W, 0 ≤ l' x := by
      rcases supports_of_closure_eq hW hF h with h1 | h1
      · exact ⟨l, hl0, rfl, h1⟩
      · refine ⟨-l, neg_ne_zero.2 hl0, LinearMap.ker_neg l, fun x hx => ?_⟩
        rw [LinearMap.neg_apply]; linarith [h1 x hx]
    obtain ⟨P, hP⟩ := exists_dotPairing_eq l'
    have hP0 : P ≠ 0 := by
      rintro rfl
      exact hl'0 (LinearMap.ext fun v => by rw [hP v, map_zero, LinearMap.zero_apply])
    set q := mk P hP0
    have hq : q ∈ D (dotPairing n) W := by
      rw [mk_mem_D]
      intro m hm
      rw [← hP m]
      exact hpos m (mem_insert_of_mem _ hm)
    have hHq : linearSubvariety (LinearMap.ker l) = {x | OrthPts x q} := by
      ext x
      induction x using ind with
      | h v hv =>
      rw [mk_mem_linearSubvariety hv, ← hker', LinearMap.mem_ker, mem_setOf_eq,
        orthPts_iff (isRep_mk v hv) (isRep_mk P hP0), hP v]
    have hC : D (dotPairing n) (coneAppui (D (dotPairing n) W) q) = closure F := by
      rw [prop3_coneAppui q hK hq, hDDW, h, hHq]; rfl
    obtain ⟨a', -, -, -, -, huniq⟩ := exists_facetteK_closure_eq_D_coneAppui hK hq
      (hC ▸ closure_nonempty_iff.2 hF.nonempty)
    have hFe : F = facetteK (D (dotPairing n) (D (dotPairing n) W)) a' := by
      refine huniq F ?_ hC.symm
      rw [hDDW]
      exact (isFacetteKExt_iff hW).2 (Or.inl hF)
    have hF' : IsFacetteK (D (dotPairing n) W) (facetteK (D (dotPairing n) W) q) := ⟨q, hq, rfl⟩
    have hFF' : facetteDuale (D (dotPairing n) W) (facetteK (D (dotPairing n) W) q) = F := by
      rw [hFe]
      exact huniq _ (facetteDuale_spec hK hF').1
        ((facetteDuale_spec hK hF').2 q (mem_facetteK_self hq))
    obtain ⟨-, hG2, -, h3⟩ := prop8_facetteDuale hK hF' (hFF' ▸ hF.nonempty)
    have e1 : facetteDuale W F = facetteDuale (D (dotPairing n) (D (dotPairing n) W))
        (facetteDuale (D (dotPairing n) W) (facetteK (D (dotPairing n) W) q)) := by
      rw [hFF', hDDW]
    rw [D_D_D W] at h3
    refine ⟨e1 ▸ hG2.nonempty, ?_⟩
    rw [e1, h3, hFF']

/-- **Prop. 9, the facettes with `𝒟(F) = ∅`**: their closure is the section of a closed `W` by no
hyperplane, so the genuine-facette reading of Prop. 9 loses nothing on the right-hand side. -/
theorem not_section_of_facetteDuale_eq_empty {W : Set (S n)} (hW : IsConvexPart W)
    (hWc : IsClosed W) {F : Set (S n)} (hF : IsFacetteK W F) (h0 : facetteDuale W F = ∅) :
    ¬ ∃ H, IsHyperplane H ∧ closure F = W ∩ H := fun h => by
  obtain ⟨hne, -⟩ := (prop9_facetteDuale hW hWc hF).2 h
  rw [h0] at hne
  exact not_nonempty_empty hne

end Sphere

namespace FacetteExposeeInstance

open Sphere FacetteDualeInstance

variable {n : ℕ}

/-- The vector `(1, …, 1)`. -/
def oneVec (n : ℕ) : Fin (n + 1) → ℝ := fun _ => 1

theorem oneVec_ne_zero : oneVec n ≠ 0 := fun h => by simpa [oneVec] using congrFun h 0

/-- The centre `s(1, …, 1)` of the simplex. -/
def centre (n : ℕ) : S n := mk (oneVec n) oneVec_ne_zero

theorem oneVec_mem_orthant : oneVec n ∈ orthant n := fun _ => by simp [oneVec]

theorem centre_mem : centre n ∈ simplexS n :=
  (mk_mem_simplexS_iff _).2 oneVec_mem_orthant

theorem centre_least : ∀ b ∈ simplexS n, AlphaK (simplexS n) (centre n) b := by
  intro b hb
  refine (alphaK_simplexS_iff (isRep_mk _ _) (exists_isRep_someVector b)).2
    ⟨oneVec_mem_orthant, ?_, fun i hi => by simp [oneVec] at hi⟩
  rw [← kPrime_simplexS]
  exact mem_kPrime_of_isRep (exists_isRep_someVector b) hb

/-- The interior facette of the simplex: the facette of its centre. -/
def interieur (n : ℕ) : Set (S n) := facetteK (simplexS n) (centre n)

theorem isFacetteK_interieur : IsFacetteK (simplexS n) (interieur n) :=
  ⟨centre n, centre_mem, rfl⟩

/-- `𝒟` of the interior facette is `∅`: no point of `D(T) = T` is orthogonal to the centre. -/
theorem facetteDuale_interieur : facetteDuale (simplexS n) (interieur n) = ∅ := by
  apply subset_empty_iff.1
  intro m hm
  have hmc : m ∈ closure (facetteDuale (simplexS n) (interieur n)) := subset_closure hm
  rw [mem_closure_facetteDuale_iff isConvexPart_simplexS isFacetteK_interieur
    (mem_facetteK_self centre_mem), D_simplexS] at hmc
  obtain ⟨hmT, hmo⟩ := hmc
  have hM := exists_isRep_someVector m
  have hMo : Module.Ray.someVector m ∈ orthant n := by
    rw [← kPrime_simplexS]; exact mem_kPrime_of_isRep hM hmT
  rw [centre, orthPts_iff hM (isRep_mk _ _), dotPairing_apply] at hmo
  simp only [oneVec, mul_one] at hmo
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hMo i)).1 hmo
  exact hM.ne_zero (funext fun i => h0 i (Finset.mem_univ i))

/-- With `𝒟` extended to `∅` (`facetteDualeExt`), `𝒟∘𝒟` fixes the interior facette. -/
theorem facetteDualeExt_interieur :
    facetteDualeExt (D (dotPairing n) (simplexS n))
      (facetteDualeExt (simplexS n) (interieur n)) = interieur n := by
  rw [facetteDualeExt_of_ne isFacetteK_interieur.nonempty, facetteDuale_interieur,
    facetteDualeExt_empty, D_simplexS, D_simplexS,
    facetteLeast_eq isConvexPart_simplexS centre_mem centre_least]
  rfl

/-- The closure of the interior facette is no section of `T` by a hyperplane: the facette
contains `s(1, …, 1)` and every `s(1, …, 1) + eᵢ`, which span `ℝⁿ⁺¹`. -/
theorem interieur_not_section :
    ¬ ∃ H, IsHyperplane H ∧ closure (interieur n) = simplexS n ∩ H := by
  rintro ⟨H, ⟨L, hL, rfl⟩, h⟩
  obtain ⟨l, hl0, hker⟩ := exists_dual_ker_eq hL
  have hsub : interieur n ⊆ linearSubvariety L := fun x hx => by
    have : x ∈ closure (interieur n) := subset_closure hx
    rw [h] at this
    exact this.2
  have hpos : ∀ v : Fin (n + 1) → ℝ, (∀ i, 0 < v i) → l v = 0 := by
    intro v hv
    have hv0 : v ≠ 0 := fun h0 => by simpa [h0] using hv 0
    have hvo : v ∈ orthant n := fun i => (hv i).le
    have hmem : mk v hv0 ∈ interieur n :=
      ⟨(alphaK_simplexS_iff (isRep_mk _ _) (isRep_mk v hv0)).2
        ⟨oneVec_mem_orthant, hvo, fun i hi => by simp [oneVec] at hi⟩,
       (alphaK_simplexS_iff (isRep_mk v hv0) (isRep_mk _ _)).2
        ⟨hvo, oneVec_mem_orthant, fun i hi => absurd hi (hv i).ne'⟩⟩
    have := (mk_mem_linearSubvariety hv0).1 (hsub hmem)
    rw [← hker] at this
    exact this
  obtain ⟨P, hP⟩ := exists_dotPairing_eq l
  apply hl0
  have hPi : ∀ i, P i = 0 := by
    intro i
    have h1 := hpos (oneVec n) (fun _ => by simp [oneVec])
    have h2 := hpos (oneVec n + Pi.single i 1) (fun j => by
      simp only [Pi.add_apply, oneVec]
      have : (0 : ℝ) ≤ Pi.single (M := fun _ => ℝ) i 1 j := by
        rw [Pi.single_apply]; split_ifs <;> norm_num
      linarith)
    rw [map_add, h1, zero_add, hP, dotPairing_single] at h2
    exact h2
  have : P = 0 := funext hPi
  exact LinearMap.ext fun v => by rw [hP v, this, map_zero, LinearMap.zero_apply]

theorem isClosed_simplexS : IsClosed (simplexS n) := by
  rw [← D_simplexS]; exact isClosed_D_dot _

/-- **Instance of Prop. 9** (the planner's): the vertex `{s(e₀)}` of the closed simplex of
`S(n + 1)` (the closed triangle of `S(2)` for `n = 1`) is the section of `T` by the hyperplane
`⟨·, (0, 1, …, 1)⟩ = 0`, so `𝒟∘𝒟({s(e₀)}) = {s(e₀)}`. -/
theorem vertex0_section :
    closure {vertex0 (n + 1)} =
      simplexS (n + 1) ∩ {x | OrthPts x (mk (oppVec n) oppVec_ne_zero)} := by
  have he : (Pi.single 0 1 : Fin (n + 2) → ℝ) ≠ 0 := by intro h; simpa using congrFun h 0
  rw [closure_singleton]
  ext x
  constructor
  · rintro rfl
    refine ⟨isFacetteK_vertex0.subset (mem_singleton _), ?_⟩
    rw [mem_setOf_eq, vertex0, orthPts_iff (isRep_mk _ he) (isRep_mk _ _), dotPairing_single]
    simp [oppVec]
  · rintro ⟨hxT, hxo⟩
    rw [← facetteK_vertex0]
    induction x using ind with
    | h X hX =>
    have hXo : X ∈ orthant (n + 1) := (mk_mem_simplexS_iff hX).1 hxT
    rw [mem_setOf_eq, orthPts_iff (isRep_mk X hX) (isRep_mk _ _), dotPairing_apply] at hxo
    have hz : ∀ i, i ≠ 0 → X i = 0 := by
      have h0 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => mul_nonneg (hXo i)
        (show (0 : ℝ) ≤ oppVec n i by simp only [oppVec]; split_ifs <;> norm_num))).1 hxo
      intro i hi
      have := h0 i (Finset.mem_univ i)
      simpa [oppVec, hi] using this
    have hX0 : X 0 ≠ 0 := by
      intro h0
      exact hX (funext fun i => by
        by_cases hi : i = 0
        · rw [hi, h0]; rfl
        · exact hz i hi)
    refine ⟨(alphaK_simplexS_iff (isRep_mk _ he) (isRep_mk X hX)).2 ⟨?_, hXo, fun i hi => ?_⟩,
      (alphaK_simplexS_iff (isRep_mk X hX) (isRep_mk _ he)).2 ⟨hXo, ?_, fun i hi => ?_⟩⟩
    · intro j; rw [Pi.single_apply]; split_ifs <;> norm_num
    · by_cases hi0 : i = 0
      · subst hi0; simp at hi
      · exact hz i hi0
    · intro j; rw [Pi.single_apply]; split_ifs <;> norm_num
    · by_cases hi0 : i = 0
      · subst hi0; exact absurd hi hX0
      · simp [hi0]

/-- **Instance of Prop. 9**: `𝒟∘𝒟` fixes the vertex facette `{s(e₀)}` of `T`. -/
theorem vertex0_exposee :
    (facetteDuale (simplexS (n + 1)) {vertex0 (n + 1)}).Nonempty ∧
      facetteDuale (D (dotPairing (n + 1)) (simplexS (n + 1)))
        (facetteDuale (simplexS (n + 1)) {vertex0 (n + 1)}) = {vertex0 (n + 1)} :=
  (prop9_facetteDuale isConvexPart_simplexS isClosed_simplexS isFacetteK_vertex0).2
    ⟨_, isHyperplane_orth _, vertex0_section⟩

/-! ### Prop. 9 needs `W` closed: the closed triangle minus one vertex -/

/-- The cone of `T ∖ {s(e₁)}` in `ℝ³`: `v ≥ 0` and `v₀ + v₂ > 0`. -/
def coneW : Set (Fin 3 → ℝ) := {v | (∀ i, 0 ≤ v i) ∧ 0 < v 0 + v 2}

theorem isPosCone_coneW : IsPosCone coneW := fun c hc v hv => by
  refine ⟨fun i => ?_, ?_⟩
  · have := hv.1 i; simp only [Pi.smul_apply, smul_eq_mul]; positivity
  · have := hv.2; simp only [Pi.smul_apply, smul_eq_mul]; nlinarith

/-- The closed triangle of `S(2)` deprived of its vertex `s(e₁)`: a convex part, not closed. -/
def triangleMoinsSommet : Set (S 2) := ofCone coneW

theorem kPrime_triangleMoinsSommet : kPrime triangleMoinsSommet = insert 0 coneW := by
  rw [kPrime, triangleMoinsSommet, F_ofCone isPosCone_coneW, Set.insert_sdiff_singleton]

theorem nonneg_of_mem_insert {v : Fin 3 → ℝ} (hv : v ∈ insert 0 coneW) (i : Fin 3) : 0 ≤ v i := by
  rcases hv with rfl | hv
  · simp
  · exact hv.1 i

theorem smul_eq_zero_or_pos {v : Fin 3 → ℝ} (hv : v ∈ insert 0 coneW) {a : ℝ} (ha : 0 ≤ a) :
    a • v = 0 ∨ 0 < a * (v 0 + v 2) := by
  rcases hv with rfl | hv
  · left; simp
  rcases ha.lt_or_eq with ha | rfl
  · exact Or.inr (mul_pos ha hv.2)
  · left; simp

theorem isConvexPart_triangleMoinsSommet : IsConvexPart triangleMoinsSommet := by
  show Convex ℝ (kPrime triangleMoinsSommet)
  rw [kPrime_triangleMoinsSommet]
  intro x hx y hy a b ha hb _
  by_cases hz : a • x + b • y = 0
  · rw [hz]; exact mem_insert _ _
  refine mem_insert_of_mem _ ⟨fun i => ?_, ?_⟩
  · have := nonneg_of_mem_insert hx i
    have := nonneg_of_mem_insert hy i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; positivity
  · have e : (a • x + b • y) 0 + (a • x + b • y) 2 = a * (x 0 + x 2) + b * (y 0 + y 2) := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [e]
    have h1 : 0 ≤ a * (x 0 + x 2) :=
      mul_nonneg ha (add_nonneg (nonneg_of_mem_insert hx 0) (nonneg_of_mem_insert hx 2))
    have h2 : 0 ≤ b * (y 0 + y 2) :=
      mul_nonneg hb (add_nonneg (nonneg_of_mem_insert hy 0) (nonneg_of_mem_insert hy 2))
    rcases smul_eq_zero_or_pos hx ha with hx' | hx'
    · rcases smul_eq_zero_or_pos hy hb with hy' | hy'
      · exact absurd (by rw [hx', hy', add_zero]) hz
      · linarith
    · linarith

theorem mk_mem_triangleMoinsSommet_iff {v : Fin 3 → ℝ} (hv : v ≠ 0) :
    mk v hv ∈ triangleMoinsSommet ↔ v ∈ coneW :=
  mk_mem_ofCone_iff isPosCone_coneW hv

theorem triangleMoinsSommet_subset : triangleMoinsSommet ⊆ simplexS 2 :=
  ofCone_subset_ofCone fun _ hv => hv.1

/-- `D(T ∖ {s(e₁)}) = T`. -/
theorem D_triangleMoinsSommet : D (dotPairing 2) triangleMoinsSommet = simplexS 2 := by
  ext m
  induction m using ind with
  | h M hM =>
  rw [mk_mem_D, mk_mem_simplexS_iff, triangleMoinsSommet, F_ofCone isPosCone_coneW]
  constructor
  · intro h i
    have h0 := h (Pi.single 0 1) ⟨⟨fun j => by rw [Pi.single_apply]; split_ifs <;> norm_num,
      by simp⟩, by simp⟩
    have h2 := h (Pi.single 2 1) ⟨⟨fun j => by rw [Pi.single_apply]; split_ifs <;> norm_num,
      by simp⟩, by simp⟩
    rw [dotPairing_single] at h0 h2
    fin_cases i
    · exact h0
    · show 0 ≤ M 1
      by_contra hneg
      push Not at hneg
      set k := (|M 0| + 1) / (-M 1)
      have hk : 0 < k := div_pos (by positivity) (by linarith)
      have hv : (![1, k, 0] : Fin 3 → ℝ) ∈ coneW \ {0} :=
        ⟨⟨fun j => by fin_cases j <;> simp [hk.le], by simp⟩, by
          intro h0; have := congrFun h0 0; simp at this⟩
      have := h _ hv
      rw [dotPairing_apply, Fin.sum_univ_three] at this
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons, one_mul, zero_mul, add_zero] at this
      have hkM : k * M 1 = -(|M 0| + 1) := by
        simp only [k]; field_simp; rw [div_self hneg.ne]
      have := le_abs_self (M 0)
      nlinarith
    · exact h2
  · intro h m hm
    rw [dotPairing_apply]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (hm.1.1 i) (h i)

/-- The open edge `]s(e₁), s(e₂)[`, the facette of `u = s(0, 1, 1)`. -/
theorem u_mem_triangleMoinsSommet :
    mk (oppVec 1) oppVec_ne_zero ∈ triangleMoinsSommet := by
  rw [mk_mem_triangleMoinsSommet_iff]
  refine ⟨fun i => ?_, ?_⟩
  · simp only [oppVec]; split_ifs <;> norm_num
  · simp [oppVec]

/-- The facette of `u` in `T ∖ {s(e₁)}` is its facette in `T`, the open edge. -/
theorem facetteK_triangleMoinsSommet :
    facetteK triangleMoinsSommet (mk (oppVec 1) oppVec_ne_zero) =
      facetteK (simplexS 2) (mk (oppVec 1) oppVec_ne_zero) := by
  have hW := isConvexPart_triangleMoinsSommet
  have hcv := convex_kPrime hW
  ext x
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨alphaK_mono triangleMoinsSommet_subset h1, alphaK_mono triangleMoinsSommet_subset h2⟩
  · intro hx
    induction x using ind with
    | h X hX =>
    obtain ⟨hX0, hXp⟩ := (mk_mem_facetteK_oppVec hX).1 hx
    have hX1 := hXp 1 (by decide)
    have hX2 := hXp 2 (by decide)
    have hU : oppVec 1 ∈ kPrime triangleMoinsSommet := by
      rw [kPrime_triangleMoinsSommet]
      exact mem_insert_of_mem _ ((mk_mem_triangleMoinsSommet_iff _).1 u_mem_triangleMoinsSommet)
    have hXk : X ∈ kPrime triangleMoinsSommet := by
      rw [kPrime_triangleMoinsSommet]
      refine mem_insert_of_mem _ ⟨fun i => ?_, by rw [hX0]; linarith⟩
      fin_cases i
      · exact hX0.ge
      · exact hX1.le
      · exact hX2.le
    have e0 : oppVec 1 0 = 0 := by simp [oppVec]
    have e1 : oppVec 1 1 = 1 := by simp [oppVec]
    have e2 : oppVec 1 2 = 1 := by simp [oppVec]
    refine ⟨(alphaK_iff hW (isRep_mk _ _) (isRep_mk X hX)).2
      ((alphaW_iff_extend hcv).2 ⟨hU, hXk, 1 / (1 + X 1 + X 2), by positivity, ?_⟩),
      (alphaK_iff hW (isRep_mk X hX) (isRep_mk _ _)).2
      ((alphaW_iff_extend hcv).2 ⟨hXk, hU, min (X 1) (X 2) / 2, by positivity, ?_⟩)⟩
    · rw [kPrime_triangleMoinsSommet]
      set ε := 1 / (1 + X 1 + X 2)
      have hε : 0 < ε := by positivity
      have h1 : ε * X 1 < 1 := by
        rw [div_mul_eq_mul_div, one_mul, div_lt_one (by positivity)]; linarith
      have h2 : ε * X 2 < 1 := by
        rw [div_mul_eq_mul_div, one_mul, div_lt_one (by positivity)]; linarith
      refine mem_insert_of_mem _ ⟨fun i => ?_, ?_⟩
      · simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
        fin_cases i
        · simp [e0, hX0]
        · simp only [Fin.mk_one, e1]; nlinarith
        · show oppVec 1 2 + ε * (oppVec 1 2 - X 2) ≥ 0
          rw [e2]; nlinarith
      · simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, e0, e2, hX0]
        nlinarith
    · rw [kPrime_triangleMoinsSommet]
      set ε := min (X 1) (X 2) / 2
      have hε : 0 < ε := by positivity
      have h1 : ε < X 1 := by
        have := min_le_left (X 1) (X 2); simp only [ε]; linarith
      have h2 : ε < X 2 := by
        have := min_le_right (X 1) (X 2); simp only [ε]; linarith
      refine mem_insert_of_mem _ ⟨fun i => ?_, ?_⟩
      · simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
        fin_cases i
        · simp [e0, hX0]
        · simp only [Fin.mk_one, e1]; nlinarith
        · show X 2 + ε * (X 2 - oppVec 1 2) ≥ 0
          rw [e2]; nlinarith
      · simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, e0, e2, hX0]
        nlinarith

/-- **Prop. 9 fails for a convex part that is not closed** (`bzprop:c3s4p9_facette_exposee` read
with `W ∈ K(S(n))` any convex part, § 3 l.642): in `W = T ∖ {s(e₁)}` the open edge
`F = ]s(e₁), s(e₂)[` is a facette with `𝒟(F) = {s(e₀)}` genuine and `𝒟∘𝒟(F) = F`, yet `F̄`, which
contains `s(e₁) ∉ W`, is the section of `W` by no hyperplane. -/
theorem not_prop9_nonclosed :
    IsConvexPart triangleMoinsSommet ∧
      IsFacetteK triangleMoinsSommet
        (facetteK triangleMoinsSommet (mk (oppVec 1) oppVec_ne_zero)) ∧
      facetteDuale triangleMoinsSommet
        (facetteK triangleMoinsSommet (mk (oppVec 1) oppVec_ne_zero)) = {vertex0 2} ∧
      facetteDuale (D (dotPairing 2) triangleMoinsSommet) (facetteDuale triangleMoinsSommet
        (facetteK triangleMoinsSommet (mk (oppVec 1) oppVec_ne_zero))) =
          facetteK triangleMoinsSommet (mk (oppVec 1) oppVec_ne_zero) ∧
      ¬ ∃ H, IsHyperplane H ∧
        closure (facetteK triangleMoinsSommet (mk (oppVec 1) oppVec_ne_zero)) =
          triangleMoinsSommet ∩ H := by
  have hW := isConvexPart_triangleMoinsSommet
  have hu := u_mem_triangleMoinsSommet
  set u : S 2 := mk (oppVec 1) oppVec_ne_zero
  have hF : IsFacetteK triangleMoinsSommet (facetteK triangleMoinsSommet u) := ⟨u, hu, rfl⟩
  have hC : D (dotPairing 2) (coneAppui triangleMoinsSommet u) = closure {vertex0 2} := by
    rw [prop3_coneAppui u hW hu, D_triangleMoinsSommet, vertex0_section (n := 1)]; rfl
  obtain ⟨a', -, -, -, -, huniq⟩ := exists_facetteK_closure_eq_D_coneAppui hW hu
    (hC ▸ ⟨vertex0 2, subset_closure rfl⟩)
  have e1 := huniq _ (facetteDuale_spec hW hF).1
    ((facetteDuale_spec hW hF).2 u (mem_facetteK_self hu))
  have e2 := huniq {vertex0 2} (by
      rw [D_triangleMoinsSommet]
      exact (isFacetteKExt_iff isConvexPart_simplexS).2 (Or.inl isFacetteK_vertex0)) hC.symm
  have hD1 : facetteDuale triangleMoinsSommet (facetteK triangleMoinsSommet u) = {vertex0 2} :=
    e1.trans e2.symm
  have hD2 : facetteDuale (simplexS 2) {vertex0 2} = facetteK triangleMoinsSommet u := by
    rw [facetteK_triangleMoinsSommet]
    exact (facetteDuale_vertex0 (n := 1)).1
  refine ⟨hW, hF, hD1, by rw [hD1, D_triangleMoinsSommet, hD2], ?_⟩
  rintro ⟨H, -, h⟩
  have he1 : (Pi.single 1 1 : Fin 3 → ℝ) ≠ 0 := by intro h; simpa using congrFun h 1
  have hmem : mk (Pi.single 1 1) he1 ∈ closure (facetteK triangleMoinsSommet u) := by
    rw [← hD2, mem_closure_facetteDuale_iff isConvexPart_simplexS isFacetteK_vertex0
      (mem_singleton _), D_simplexS, mk_mem_simplexS_iff, vertex0,
      orthPts_iff (isRep_mk _ he1) (isRep_mk _ _), dotPairing_single]
    refine ⟨fun j => ?_, by simp⟩
    rw [Pi.single_apply]; split_ifs <;> norm_num
  rw [h] at hmem
  have := ((mk_mem_triangleMoinsSommet_iff he1).1 hmem.1).2
  simp at this

/-- **Prop. 9 with `𝒟` extended to `∅` is imprecise** (OQ-165 (c)): for the interior facette `F`
of the closed simplex of `S(n)`, `𝒟(F) = ∅` and the extended `𝒟∘𝒟(F) = F`, yet `F̄ = T` is the
section of `T` by no hyperplane. The degenerate case is the facette `∅` of dimension `−1`. -/
theorem prop9_ext_imprecise :
    IsConvexPart (simplexS n) ∧ IsClosed (simplexS n) ∧
      IsFacetteK (simplexS n) (interieur n) ∧ facetteDuale (simplexS n) (interieur n) = ∅ ∧
      facetteDualeExt (D (dotPairing n) (simplexS n))
        (facetteDualeExt (simplexS n) (interieur n)) = interieur n ∧
      ¬ ∃ H, IsHyperplane H ∧ closure (interieur n) = simplexS n ∩ H :=
  ⟨isConvexPart_simplexS, isClosed_simplexS, isFacetteK_interieur, facetteDuale_interieur,
    facetteDualeExt_interieur, interieur_not_section⟩

end FacetteExposeeInstance

end Benzecri
