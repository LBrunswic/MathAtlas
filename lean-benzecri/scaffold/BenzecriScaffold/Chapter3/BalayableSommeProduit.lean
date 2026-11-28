import Benzecri.Chapter3.BalayableSomme
import Benzecri.Applications.ConverseGeneral

/-!
# Chapter 3 § 2, Proposition 4 in the notation of Chapter 1: `w ≅ F⁻¹(F(v₁) × … × F(v_p))`

J.-P. Benzécri, *Sur les variétés localement affines et localement projectives*, Bull. SMF 88
(1960) 229–332, Chapter 3 § 2, journal p. 268; transcription
`papers/benzecri/legacy/labeled/benzecri1960_ch3.tex` (TO BE CHECKED BY THE AUTHOR).
Target T-bz-c3-balayable-somme; split off `BalayableSomme.lean` so that it stays sorry-free.

* `bzprop:c3s2p4_automorphisme_compatible` — `benzecri1960_ch3.tex:599` (Prop. 4, l.599–611),
  NOT marked: `Benzecri.Sphere.prop4_produit`, the Chapter 1 form (a projective isomorphism
  `PiBase n B ≃ₜ w` and `IsCompatiblePi` of every transported automorphism), STATED on one
  tagged `sorry`. The intrinsic forms are proved in `BalayableSomme.lean` (`prop4_somme`,
  `prop4_automorphisme_compatible`).

> **Proposition 4.** Soient $w$ un ouvert convexe de $S(\R^{n+1})=S(n)$, de noyau vide, $l_i$
> les $p$ sous-variétés distinguées simples relatives à $w$, $v_i$ les convexes de $l_i$ dont
> $w$ est la somme; on peut écrire avec les notations du chapitre 1, paragraphes 1 et 2
> $$ w=F^{-1}(F(v_1)\times\ldots\times F(v_p)) $$
> tout automorphisme projectif de $w$ est un automorphisme compatible au sens du chapitre 1,
> paragraphe 3, définition 2.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `w` ouvert, convexe, de noyau vide | ✓ carried |
| (not printed) `F(w)` contains no line | ⚠ ADDED (OQ-168), as in `BalayableSomme.lean` |
| (not printed) `w ≠ ∅` | ⚠ reading: `w.Nonempty` |
| « avec les notations du chapitre 1 » | reading: bases `bᵢ : lᵢ ≅ ℝ^{nᵢ+1}`, `Bᵢ = s(bᵢ(F(vᵢ)))` open in `S(nᵢ)` |

## SCOPE (disclosed)

* The single `sorry` is the transport described in the comment of `prop4_produit`: no
  mathematical gap, the content is `prop4_somme` and `prop4_automorphisme_compatible`.
* Not marked for that reason and for OQ-168 (see `BalayableSomme.lean`).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

open Set Function Filter Topology
open scoped Pointwise

namespace Benzecri

namespace Sphere

section Model

variable {m : ℕ}

/-- **Prop. 4, the Chapter 1 form**: with `n i + 1 = dim lᵢ` and bases `bᵢ : Lᵢ ≅ ℝ^{nᵢ+1}`, each
`vᵢ` is an open subset `Bᵢ` of `S(nᵢ)`; `w` is projectively isomorphic to
`F⁻¹(F(B₀) × … × F(B_q))` (`PiBase`, Ch. 1 § 3), and every projective automorphism of `w`,
transported, is compatible (Ch. 1 § 3 Déf. 2, `IsCompatiblePi`). -/
theorem prop4_produit {w : Set (S m)} (hw : IsConvexPart w) (hopen : IsOpen w)
    (hne : w.Nonempty) (hn : noyau w = ∅) (hd : ¬ ContientDroite (F w)) {q : ℕ}
    (l : Fin (q + 1) ≃ simplesS w) (n : Fin (q + 1) → ℕ)
    (b : ∀ i, (l i : Submodule ℝ (Fin (m + 1) → ℝ)) ≃ₗ[ℝ] (Fin (n i + 1) → ℝ)) :
    ∃ hB : ∀ i, IsOpen (ofCone (b i '' (Subtype.val ⁻¹' sommandeS w (l i))) : Set (S (n i))),
      ∃ Ψ : PiBase n (fun i => (⟨_, hB i⟩ : TopologicalSpace.Opens (S (n i)))) ≃ₜ
          (⟨w, hopen⟩ : TopologicalSpace.Opens (S m)),
        IsProjIso (pdim n) m Ψ ∧
        ∀ f : GXAut (GSR m) (S m) (⟨w, hopen⟩ : TopologicalSpace.Opens (S m)),
          ∃ h : IsProjIso (pdim n) (pdim n) ((Ψ.trans f.toHomeomorph).trans Ψ.symm),
            IsCompatiblePi h.toAut := by
  -- The mathematics is `prop4_somme` + `prop4_automorphisme_compatible`; what is missing is the
  -- transport through Chapter 1's cone machinery: (i) the global cone chart
  -- `FCone.coneChart` of the inclusion chart of each open `Bᵢ ⊆ S(nᵢ)` (source everything,
  -- target `toSphere⁻¹' Bᵢ`); (ii) their product chart `piChart` and its base chart
  -- `ConeBase.baseChart` on `PiBase`, composed with the linear iso `ℝ^{pdim n+1} ≅ ℝ^{m+1}`,
  -- `(yᵢ) ↦ ∑ bᵢ⁻¹ yᵢ` (which maps `∏ bᵢ(F(vᵢ))` onto `F(w)` by `prop4_somme`), made a
  -- `Homeomorph` onto the subtype `w` and shown a `GSR` morphism after `subst` of
  -- `pdim n = m`; (iii) for `f`, the conical isomorphisms `φᵢ` read `cᵢ⁻¹ bᵢ g b_{τ(i)}⁻¹` in
  -- these charts, NORMALISED to `|det| = 1` by `cᵢ = |det(bᵢ g b_{τ(i)}⁻¹)|^{1/(nᵢ+1)}` because
  -- the cone groupoid is `GU`, the torus element `t = [(cᵢ)]` absorbing the normalisation,
  -- and the identity `f • [x] = t • [φ(x ∘ τ)]` checked through (i)–(ii).
  sorry -- SORRY(bzprop:c3s2p4_automorphisme_compatible): the transport of prop4_somme / prop4_automorphisme_compatible to PiBase (global cone charts of FCone over open subsets, base chart of the product chart, dimension cast pdim n = m, GU-normalisation of the φᵢ); see the comment above

end Model

end Sphere

end Benzecri
