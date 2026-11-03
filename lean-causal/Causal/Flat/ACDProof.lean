import Causal.Flat.ACDReduction
import Causal.Flat.ACDHall
import Causal.Flat.ACDNull
import Causal.Flat.ACDLoxodromic
import Causal.Flat.GromovProof

/-!
# `Causal.Flat.ACDProof` — the Auslander–Carrière–Dal'bo theorem, proved for isometries

T. Barbot, *Globally hyperbolic flat space-times* (`papers/barbot`, arXiv math/0402257), §5,
Theorem 5.1, `bthm:ausl` — `GHFspace.tex:1696` (cited by Barbot as `cardal` Theorem 1.2.1), in
the form of the named external `AuslanderCarriereDalbo d` (`Flat/Externals`, DEC-36), is
**proved, for every `d`** (DEC-121): `auslanderCarriereDalbo d`. **The label is not marked**
(kb/0011): the Lean statement is for discrete groups of *isometries* of `𝐌ⁿ`, narrower than the
paper's discrete subgroups of `Aff(n, ℝ)` (a candidate for the author's mark in a reading; the
ledger row is curated).

> Let $\Gamma$ be a discrete subgroup of $\mbox{Aff}(n, {\mathbb R})$.
> Then, the identity component $G_{0}$ of
> the closure of $L(\Gamma)$ in $GL(n, {\mathbb R})$ is nilpotent.
> In particular, $\Gamma_{nd} = L^{-1}(G_{0} \cap L(\Gamma))$
> is nilpotent. (l.1699–1703)

**Dimension (kb/0024).** Barbot's `𝐌ⁿ` has total dimension `n`; `Minkowski d` has `d` spatial
dimensions, so Barbot's `n` is `d + 1`.

The route is a Lorentz Zassenhaus–Frobenius argument (`docs/CARRIERE-DALBO-SURVEY.md` §2.2 T1):

* **Step 1** (`Flat/ACDHall`, discreteness): `g, h ∈ Γ` with `‖L − 1‖ < 1/128` generate a
  nilpotent group (scaling + multi-letter halving + Hall's lemma).
* **Step 2** (no discreteness): near-identity elements (`< 1/2`) of a nilpotent `N ≤ SO₀(1, d)`
  commute — `commute_of_isNilpotent_lorentz` here, by the dichotomy loxodromic
  (`Flat/ACDLoxodromic`, reduced to the null case) / none (`fixesTimelikeOrNull_of_noLox`,
  `Flat/GromovProof`, then `Flat/ACDNull`).
* Hence **(★) with `ε = 1/128`** for every discrete `Γ` (`acdStar`), and **Steps 3–5**
  (`Flat/ACDReduction`) give `AusConclusion Γ`.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `Γ` discrete (l.1699) | ✓ carried: `DiscreteTopology Γ` (in `isomTopology`) |
| "subgroup of $\mbox{Aff}(n, {\mathbb R})$" (l.1699) | ⚠ strengthened (as `AuslanderCarriereDalbo`): `Γ ≤ Isom(𝐌ⁿ)`; the closure is taken in `SO₀(1, d)`, closed in `GL`, so it agrees |
| "`G₀` … is nilpotent" (l.1700–1701) | ✓ carried (the proof gives `G₀` abelian) |
| "`Γ_nd` … is nilpotent" (l.1702–1703) | ✓ carried |

## SCOPE (disclosed)

* Nothing open: the four step modules and this one are sorry-free and axiom-free.
* Finite generation is not used; Lie theory, the Zariski closure and Cartan's closed-subgroup
  theorem are not used.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Barbot campaign,
DEC-121 (integrator of the Lorentz Zassenhaus–Frobenius route: `Flat/ACDReduction`, `…Hall`,
`…Null`, `…Loxodromic`).
-/

namespace Causal.Flat

variable {d : ℕ}

/-- **Step 2 (Lorentz Frobenius, no discreteness).** Near-identity elements (`1/2`-close to `1`
in operator norm) of a nilpotent subgroup of `SO₀(1, d)` commute. -/
theorem commute_of_isNilpotent_lorentz {N : Subgroup (lorentz d)} (hN : Group.IsNilpotent N)
    {a b : lorentz d} (ha : a ∈ N) (hb : b ∈ N)
    (haε : ‖linToCLM (a : Minkowski d ≃ₗ[ℝ] Minkowski d) - 1‖ < 1 / 2)
    (hbε : ‖linToCLM (b : Minkowski d ≃ₗ[ℝ] Minkowski d) - 1‖ < 1 / 2) : a * b = b * a := by
  by_cases hl : ∃ ℓ ∈ N, IsLoxodromic (ℓ : Minkowski d ≃ₗ[ℝ] Minkowski d)
  · obtain ⟨ℓ, hℓ, hlox⟩ := hl
    exact commute_of_isNilpotent_of_loxodromic
      (fun N hN v₀ hv0 hv hfix a ha b hb h1 h2 =>
        commute_of_isNilpotent_of_fixNull hN hv0 hv hfix ha hb h1 h2)
      (fun v₀ hv0 hv A => norm_screenRot_sub_one_le hv0 hv A) hN hℓ hlox ha hb haε hbε
  · push Not at hl
    exact commute_of_isNilpotent_of_fixesTimelikeOrNull hN (fixesTimelikeOrNull_of_noLox hl)
      ha hb haε hbε

/-- **The local commutation property (★_Γ) for every discrete `Γ`**, with `ε = 1/128`. -/
theorem acdStar {Γ : Subgroup (isom d)} (hdisc : DiscreteTopology Γ) : ACDStar Γ := by
  refine ⟨1 / 128, by norm_num, fun g hg h hh hgε hhε => ?_⟩
  set H := Subgroup.closure ({g, h} : Set (isom d))
  haveI : Group.IsNilpotent H := isNilpotent_closure_pair_of_near_one hdisc hg hh hgε hhε
  have hN : Group.IsNilpotent (H.map linearPart) :=
    Group.nilpotent_of_surjective (linearPart.subgroupMap H) (linearPart.subgroupMap_surjective H)
  have hgH : g ∈ H := Subgroup.subset_closure (by simp)
  have hhH : h ∈ H := Subgroup.subset_closure (by simp)
  have hL : ∀ x : isom d, ((linearPart x : lorentz d) : Minkowski d ≃ₗ[ℝ] Minkowski d) =
      linOf x := fun x => (linOf_eq_linearPart x).symm
  have key := commute_of_isNilpotent_lorentz hN (a := linearPart g) (b := linearPart h)
    ⟨g, hgH, rfl⟩ ⟨h, hhH, rfl⟩ (by rw [hL]; linarith) (by rw [hL]; linarith)
  have := congrArg (fun x : lorentz d => (x : Minkowski d ≃ₗ[ℝ] Minkowski d)) key
  simpa [hL] using this

variable (d) in
/-- **The Auslander–Carrière–Dal'bo theorem, proved** (DEC-121; was the named external of
DEC-36): for every discrete `Γ ≤ Isom(𝐌ⁿ)`, `G₀` and `Γ_nd` are nilpotent. -/
theorem auslanderCarriereDalbo : AuslanderCarriereDalbo d :=
  fun _ hΓ => ausConclusion_of_star hΓ (acdStar hΓ)

end Causal.Flat
