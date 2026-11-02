import Causal.CBG.NoCorresponding
import Causal.CBG.CausalConvex

/-!
# Two developments embed in a common one: the gluing along the MCGHD (Sbierski Thm 2.7)

Package 7 (`docs/CBG-DESIGN.md` §3 step 5; §5 row 7). **No label is marked** (DEC-60: ETT labels
are the ETT campaign's; rows stay partial until the singular instance discharges the model).
Cited, unmarked: `prop:ppcm_Cauchy` — `ETT.tex:1994`, `defi:ppcm` — `ETT.tex:1987`,
`def:common_over_extension` — `ETT.tex:1970`, `rem:non_separe_cas` — `ETT.tex:2016`,
`rem:CBG_analytique` — `ETT.tex:1903`; thesis `prop:ppcm_Cauchy` (`these.tex:6473`); Sbierski
1309.7591, **Thm 2.7** (p. 12) and its proof (pp. 20–21).

> Then $\ppcm$ is, up to equivalence, the unique minimal common over-extension of $M_1$ and
> $M_2$. (`prop:ppcm_Cauchy`, `ETT.tex:1994–1998`)

> The quotient $\ppcm$ is a $\mass{\geq0}$-manifold by construction --- the charts of $M_1$ and
> $M_2$ descend --- and it is second countable. Everything therefore reduces to the Hausdorff
> property […] (`ETT.tex:2000–2002`)

> Hence $C=\emptyset$, so by Remark \ref{rem:non_separe_cas} the quotient $\ppcm$ is Hausdorff,
> and it is a singular flat spacetime. […] The maps $a\circ j_1$ and $b\circ j_2$ from $\pgcd$ to
> $M$ agree on $M_0$, hence agree by rigidity […]. Therefore $a\coprod b$ descends to the quotient
> and yields a Cauchy embedding $\ppcm\rightarrow M$ […]. Minimality and uniqueness up to
> equivalence follow. (proof of `prop:ppcm_Cauchy`, `ETT.tex:2319–2331`)

> Theorem 2.7 (Global uniqueness). Given two GHDs M and M′ of the same initial data, there exists
> a GHD M̃ that is an extension of M and M′. (Sbierski, p. 12)

> 4. (M̃, g̃) is globally hyperbolic with Cauchy surface ι̃(M) […] γ|J can be considered as an
> inextendible timelike curve in M and thus has to intersect ι(M). […] Assume γ intersected ι̃(M)
> more than once. (Sbierski, proof of Thm 2.7, p. 21)

> $\ppcm$ est l'unique sur-extension commune minimale à $M_1$ et $M_2$ à équivalence près.
> (`these.tex:6477`)

## What is proved (no `sorry` in this file)

* **Model-free** (namespace `Causal.Causality`): `exists_mem_cauchy_between` (a relation from
  `J⁻(S)` to `J⁺(S)` crosses the Cauchy surface `S`), `isClosed_Jminus_of_dense`,
  `Jplus_inter_Jminus_eq`; `CauchySide` (the facts of a GH piece the argument consumes);
  **`TwoPiece`** — a spacetime covered by two open pieces with causally convex overlap and
  agreeing relations, absolutely minimal: `le_top_iff` (`≤_P` is a one- or two-step chain),
  `le_of_le_top`, `mem_of_le_top` (**each piece is causally convex in `P`: the exit/re-entry
  argument**), `exists_mid`, `isCausal`, `isCauchySurface` (a common Cauchy surface of the
  pieces is one of `P`); `PieceChart` and **`TwoPiece.globallyHyperbolic`** (compact diamonds:
  inside a piece, and across, `isCompact_diamond_mixed`, by an explicit decomposition through `Σ̃`).
* **Level A** (namespace `Causal.CBG`): `Dev.cauchySide`, `pieceChart_of_isMor`; the gluing
  `PpcmSpace` along the MCGHD, its structure (`exists_ppcmStr`, `Geometry.glue`), `ppcm_twoPiece`,
  `ppcm_globallyHyperbolic` (**GH proved directly**: no `curvesExtend`, no `isCompact_*` on `ppcm`),
  `ppcm_isCauchySurface`, `ppcm_connectedSpace`, `ppcm_secondCountable`, **`ppcmDev`** (a
  development; T2 by `t2Space_gluing_mcghd`, package 6), `ppcmDev_isMorphism₁/₂`,
  **`ppcmDev_desc`** (minimality, unique factorisation: rigidity A1 + `Gluing.desc`),
  `ppcmDev_desc_injective` (the factorisation is injective, by the time function of the
  development `ppcm`), **`ppcmDev_unique`** (unique minimal up to equivalence), **`exists_ppcm`**
  (the principal theorem, no hypothesis beyond the geometry and `M₀` connected),
  `exists_common_extension`.
* **Witnesses** (namespace `Causal.Causality`): `timelikeLine_twoPiece`, `timelikeLine_cauchySide`,
  `timelikeLine_twoPiece_globallyHyperbolic` (all hypotheses of `TwoPiece.globallyHyperbolic`
  jointly, with proper `PieceChart` images).

## Hypothesis checklist

| paper | here |
|---|---|
| `M₀` GH singular flat, `M₁`, `M₂` Cauchy extensions (`ETT.tex:1995–1996`) | ✓ `N₁ N₂ : Dev 𝔊 s₀` over any `Geometry` (DEC-60); `[ConnectedSpace M₀]` carried as in packages 4, 6 (`lem:C_ext_connexe`) |
| `ψ` an isometric **embedding** (Sbierski: « the isometric embedding of `U` into `M′` ») | ✓ derived (`mcghdMap_injOn`: Lemma 3.3, `IsCGHD.injOn`, from the interface field `Geometry.timeFunction`, round 2); not carried by `exists_ppcm` / `exists_common_extension`. The construction lemmas (`ppcmStr`, `ppcmDev`, `ppcmDev_desc`, `ppcmDev_unique`, …) keep `hinj` as a proof parameter (see SCOPE) |
| `ppcm` « a manifold by construction — the charts descend » (`ETT.tex:2000–2001`) | ✓ `Geometry.glue` (transitions `id`, `ψ`, `ψ⁻¹`; Sbierski's atlas, step 1) |
| second countable (`ETT.tex:2001`; Sbierski step 2) | ✓ `ppcm_secondCountable` (open quotient of `N₁ ⊔ N₂`) |
| Hausdorff (`ETT.tex:2323–2324`, `rem:non_separe_cas`) | ✓ `t2Space_gluing_mcghd` (package 6, Thm 3.13) |
| « it is a singular flat spacetime » (`ETT.tex:2324`): global hyperbolicity, `ι(Σ)` Cauchy | ✓ proved (ETT's GH, causal + compact diamonds): `ppcm_globallyHyperbolic`, `ppcm_isCauchySurface`; ⚠ route replaced: Sbierski's step 4 uses timelike curves and the GH of `U`; here the exit/re-entry argument on chains (`TwoPiece.mem_of_le_top`), and compactness by `isCompact_diamond_mixed`; ETT gives no argument (finding) |
| minimality: a morphism `ppcm → M` for every common over-extension (`ETT.tex:1983–1985`, `2326–2330`) | ✓ `ppcmDev_desc`, ⚠ weakened hypothesis: `g₁`, `g₂` any morphisms of developments (not asked injective), and the factorisation is **unique**; « yields a Cauchy embedding »: injectivity by `ppcmDev_desc_injective` (the time function of the development `ppcm`, `Geometry.timeFunction`) |
| rigidity (`rem:CBG_analytique`) | ✓ `Geometry.rigid` (A1), on the connected `U` (`mcghd_connectedSpace`) |
| uniqueness up to equivalence | ✓ `ppcmDev_unique`, ⚠ weakened: the competitor `R` need only factor pairs of **injective** morphisms `gᵢ` (ETT's Cauchy embeddings), not uniquely |
| connected | ✓ `ppcm_connectedSpace` (no injectivity used) |

## SCOPE (disclosed)

* **No `Geometry` field beyond interface round 2 is needed.** The construction uses `glue`,
  `isMor_*`, `isMor_inv`, `absolutelyMinimalOn`, `rigid`, and on `N₁`, `N₂` (developments, so GH)
  A2's `singularFlatAxioms` (`K_densite_sing`, `tarentin`), `curvesExtend`, `isCompact_*`,
  `timeFunction`. On `ppcm` itself none of `curvesExtend`, `isCompact_*`,
  `secondCountable_of_cauchy` is used (only `timeFunction`, in `ppcmDev_desc_injective`, once
  `ppcm` is a `Dev`), so the package-10 risk (design §6) does not arise here.
* **Interface round 2 (1), applied.** The two hypotheses this package carried before the field
  existed are discharged: `InjOn mcghdMap mcghdOpens` is `mcghdMap_injOn` (`CBG/Pgcd`, Lemma 3.3
  from `Geometry.timeFunction` on `N₁`), so `exists_ppcm` and `exists_common_extension` no longer
  take it; and the time function on `ppcmStr hinj` of `ppcmDev_desc_injective` is
  `(ppcmDev N₁ N₂ hinj).causality_hasTimeFunction`, so that hypothesis is removed. The redundant
  `exists_ppcm_of_timeFunction` is deleted (no user). The construction lemmas and definitions
  (`convex_mcghdImage`, `mcghd_le_iff`, `ppcm_injective_j₂`, `ppcm_ι₁_eq_ι₂_iff`, `exists_ppcmStr`,
  `ppcmStr`, `isMor_ppcm_ι₁/₂`, `ppcm_chart₁/₂`, `ppcm_twoPiece`, `ppcm_globallyHyperbolic`,
  `ppcm_isCauchySurface`, `ppcm_isCauchyEmbedding`, `ppcmDev`, `ppcmDev_isMorphism₁/₂`,
  `ppcmDev_desc`, `ppcmDev_desc_injective`, `ppcmDev_unique`) keep `hinj` as a **proof
  parameter**: it is a `Prop`, so `ppcmDev N₁ N₂ h` does not depend on `h` (proof irrelevance), it
  is always supplied by `mcghdMap_injOn`, and `CBG/Maximal`'s family construction passes it per
  pair; removing it would only move `N₁ N₂` to explicit arguments throughout. `ppcm_hj₂` and
  `ppcm_secondCountable` no longer take it (they had stopped using it).
* The causality of the glued structure is **not** identified with `Gluing.causality` (the planned
  lemma `CBG/Geometry`'s SCOPE and `glue` docstring assign to this package): the obligation is
  **discharged by replacement** — the two charts `ι₁`, `ι₂` (`pieceChart_of_isMor`: open embeddings
  matching the relations, from the morphisms and absolute minimality) carry all the causal
  information the proof reads, and `TwoPiece` is the model-free form. The `Geometry` text is the
  master's to update (reported, `REPORT.json`).
* `ppcmStr` is a choice (`Classical.choose` of `Geometry.glue`); `ppcmDev_desc` and
  `ppcmDev_unique` make the result independent of it up to unique isomorphism of developments.
* `ppcm_le_of_image` (private) is a third copy of `Flat.LocalIso.rel_of_image` (causal half;
  `CBG/Pgcd` has the second), kept private so that this module imports no Barbot-campaign module.
* `TwoPiece` is for **two** pieces; package 10 (`Maximal`) glues a family: the same exit/re-entry
  argument applies chain-wise, but its family form is not proved here.
* Witnesses: `timelikeLine_twoPiece` (a proper overlap `]0,1[`, local and absolutely minimal, with a
  mixed pair `-1 ≤ 2`), `timelikeLine_cauchySide` (`{0}`) and
  `timelikeLine_twoPiece_globallyHyperbolic` (charts `a ↦ 1 - e^{-a}/2`, `b ↦ e^{b}/2` with proper
  images, Cauchy sides `{0}` with common image `{1/2}`: every hypothesis of
  `TwoPiece.globallyHyperbolic` at once). `Geometry` has no inhabitant (its SCOPE), so the Level-A
  statements are witnessed only through packages 11, 12.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/
namespace Causal

open Set Topology Filter Function TopologicalSpace

universe u

namespace Causality

section Crossing

variable {M : Type u} [TopologicalSpace M] {C : Causality M}

/-- **A causal relation from the past of a Cauchy surface to its future crosses it**: `x ≤ y`,
`x ∈ J⁻(S)`, `y ∈ J⁺(S)` give `σ ∈ S` with `x ≤ σ ≤ y` (`M` causal, causally arc-connected, curves
extending, `S` an acausal Cauchy surface). The inextensible curve through a causal curve from `x`
to `y` meets `S` once, at `c τ`; if `τ` lies before `x` (after `y`) on the curve, acausality of `S`
forces `x ∈ S` (`y ∈ S`). -/
theorem exists_mem_cauchy_between (hcaus : C.IsCausal) (hC : C.CausallyArcConnected)
    (hext : C.CurvesExtend) {S : Set M} (hS : C.IsCauchySurface S) (hac : C.IsAcausal S)
    {x y : M} (hx : x ∈ C.Jminus ⊤ S) (hy : y ∈ C.Jplus ⊤ S) (hxy : C.le ⊤ x y) :
    ∃ σ ∈ S, C.le ⊤ x σ ∧ C.le ⊤ σ y := by
  obtain ⟨γ, hγ, hγ0, hγ1⟩ := (hC ⊤ le_rfl x y).1.1 hxy
  obtain ⟨I, c, hc, hsub⟩ := hext γ 0 1 zero_le_one hγ
  obtain ⟨tx, htx, hctx⟩ : x ∈ c '' I := hsub ⟨0, ⟨le_rfl, zero_le_one⟩, hγ0⟩
  obtain ⟨ty, hty, hcty⟩ : y ∈ c '' I := hsub ⟨1, ⟨zero_le_one, le_rfl⟩, hγ1⟩
  obtain ⟨_, ⟨⟨τ, hτ, rfl⟩, hτS⟩, -⟩ := hS I c hc
  rcases le_total τ tx with h1 | h1
  · obtain ⟨σ₀, hσ₀, hxσ₀⟩ := hx
    have h' : C.le ⊤ (c τ) x := by rw [← hctx]; exact hc.1.le_of_le hτ htx h1
    have heq : c τ = σ₀ := hac _ hτS _ hσ₀ (C.le_trans h' hxσ₀)
    rw [← heq] at hxσ₀
    have hx' : x = c τ := hcaus hxσ₀ h'
    exact ⟨x, hx' ▸ hτS, C.le_refl trivial, hxy⟩
  rcases le_total τ ty with h2 | h2
  · exact ⟨c τ, hτS, by rw [← hctx]; exact hc.1.le_of_le htx hτ h1,
      by rw [← hcty]; exact hc.1.le_of_le hτ hty h2⟩
  · obtain ⟨σ₁, hσ₁, hσ₁y⟩ := hy
    have h' : C.le ⊤ y (c τ) := by rw [← hcty]; exact hc.1.le_of_le hty hτ h2
    have heq : σ₁ = c τ := hac _ hσ₁ _ hτS (C.le_trans hσ₁y h')
    rw [heq] at hσ₁y
    have hy' : y = c τ := hcaus h' hσ₁y
    exact ⟨y, hy' ▸ hτS, hxy, C.le_refl trivial⟩

/-- **`J⁻(S)` is closed** for any set `S`, given `K⁻` density (`J⁻(x) ⊆ closure K⁻(x)` for every
`x`) and compact `J⁻(S) ∩ J⁺(x)` for every `x` (no acausality and no covering of `M` is assumed).
It is the first step of `Jplus_mem_nhds_of_isAcausal`, `CBG/Corresponding`, whose proof it repeats:
that lemma does not export it. -/
theorem isClosed_Jminus_of_dense [T2Space M] [FirstCountableTopology M] {S : Set M}
    (hdense : ∀ x, C.Jminus ⊤ {x} ⊆ closure (C.Kminus ⊤ {x}))
    (hcpt : ∀ x, IsCompact (C.Jminus ⊤ S ∩ C.Jplus ⊤ {x})) : IsClosed (C.Jminus ⊤ S) := by
  refine isClosed_of_closure_subset fun z hz => ?_
  have hzK : z ∈ closure (C.Kminus ⊤ {z}) :=
    hdense z (by simpa using C.le_refl (U := ⊤) (x := z) trivial)
  obtain ⟨x, -, hx⟩ := mem_closure_iff_nhds.1 hzK univ univ_mem
  have hJ := Jplus_mem_nhds_of_mem_Kminus hx
  have hz' : z ∈ closure (C.Jminus ⊤ S ∩ C.Jplus ⊤ {x}) := by
    rw [mem_closure_iff_nhds] at hz ⊢
    intro O hO
    obtain ⟨w, ⟨hwO, hwJ⟩, hwS⟩ := hz (O ∩ C.Jplus ⊤ {x}) (inter_mem hO hJ)
    exact ⟨w, hwO, hwS, hwJ⟩
  exact ((hcpt x).isClosed.closure_subset hz').1

/-- In a causal `M`, an acausal set `S` is `J⁺(S) ∩ J⁻(S)` (no covering of `M` by the two sides
of `S` is assumed). -/
theorem Jplus_inter_Jminus_eq (hcaus : C.IsCausal) {S : Set M} (hac : C.IsAcausal S) :
    C.Jplus ⊤ S ∩ C.Jminus ⊤ S = S := by
  refine Subset.antisymm ?_ fun x hx => ⟨⟨x, hx, C.le_refl trivial⟩, ⟨x, hx, C.le_refl trivial⟩⟩
  rintro x ⟨⟨σ, hσ, hσx⟩, ⟨σ', hσ', hxσ'⟩⟩
  have e : σ = σ' := hac σ hσ σ' hσ' (C.le_trans hσx hxσ')
  subst e
  rw [hcaus hxσ' hσx]; exact hσ

end Crossing

/-! ### Cauchy sides: the facts of a globally hyperbolic piece the gluing argument consumes -/

section CauchySide

variable {X : Type u} [TopologicalSpace X]

/-- **The facts about a globally hyperbolic spacetime `X` with Cauchy surface `S` that the
gluing argument consumes** (time-symmetric): every point is on one side of `S`; a relation from
`J⁻(S)` to `J⁺(S)` crosses `S`; the causal relation and `S` are closed; the half-diamonds
`J^±(S) ∩ J^∓(x)` are compact. For a development, `Dev.cauchySide` (from A2). -/
structure CauchySide (C : Causality X) (S : Set X) : Prop where
  cover : ∀ x, x ∈ C.Jplus ⊤ S ∪ C.Jminus ⊤ S
  crossing : ∀ x y, x ∈ C.Jminus ⊤ S → y ∈ C.Jplus ⊤ S → C.le ⊤ x y →
    ∃ σ ∈ S, C.le ⊤ x σ ∧ C.le ⊤ σ y
  isClosed_le : IsClosed {z : X × X | C.le ⊤ z.1 z.2}
  isClosed : IsClosed S
  isCompact_future : ∀ x, IsCompact (C.Jplus ⊤ S ∩ C.Jminus ⊤ {x})
  isCompact_past : ∀ x, IsCompact (C.Jminus ⊤ S ∩ C.Jplus ⊤ {x})

end CauchySide

/-! ### Two pieces: a spacetime covered by two open sets glued along a causally convex overlap -/

section TwoPiece

variable {P : Type u} [TopologicalSpace P] (D : Causality P) (A B : Opens P)

/-- **A spacetime covered by two open pieces `A`, `B` along a causally convex overlap** — the
abstract shape of the gluing of two developments along their MCGHD (Sbierski, proof of Thm 2.7):
`D` absolutely minimal on `P` (so `≤_P` is generated by `≤_A` and `≤_B`), the overlap `A ∩ B`
causally convex in each piece for that piece's relation, and the two relations agreeing between
points of the overlap. -/
structure TwoPiece : Prop where
  cover : ∀ z, z ∈ A ∨ z ∈ B
  absolutelyMinimalOn : D.AbsolutelyMinimalOn ⊤
  convex_left : ∀ x y z, x ∈ B → z ∈ B → D.le A x y → D.le A y z → y ∈ B
  convex_right : ∀ x y z, x ∈ A → z ∈ A → D.le B x y → D.le B y z → y ∈ A
  agree : ∀ x y, x ∈ A → x ∈ B → y ∈ A → y ∈ B → (D.le A x y ↔ D.le B x y)

/-- The relation the chains of `≤_A`, `≤_B` reduce to: one step in a piece, or a step in each
piece through a point of the overlap. -/
def twoPieceRel (x y : P) : Prop :=
  D.le A x y ∨ D.le B x y ∨ (∃ u, u ∈ A ∧ u ∈ B ∧ D.le A x u ∧ D.le B u y) ∨
    (∃ u, u ∈ A ∧ u ∈ B ∧ D.le B x u ∧ D.le A u y)

variable {D A B}

namespace TwoPiece

/-- The hypotheses are symmetric in the two pieces. -/
theorem symm (h : D.TwoPiece A B) : D.TwoPiece B A where
  cover z := (h.cover z).symm
  absolutelyMinimalOn := h.absolutelyMinimalOn
  convex_left := h.convex_right
  convex_right := h.convex_left
  agree x y hxB hxA hyB hyA := (h.agree x y hxA hxB hyA hyB).symm

/-- `twoPieceRel` is transitive (sixteen cases: convexity of the overlap and the agreement
of the relations reduce every composite to one of the four forms). -/
theorem rel_trans (h : D.TwoPiece A B) {x y z : P} (h₁ : twoPieceRel D A B x y)
    (h₂ : twoPieceRel D A B y z) : twoPieceRel D A B x z := by
  rcases h₁ with h₁ | h₁ | ⟨u, huA, huB, hxu, huy⟩ | ⟨u, huA, huB, hxu, huy⟩ <;>
  rcases h₂ with h₂ | h₂ | ⟨v, hvA, hvB, hyv, hvz⟩ | ⟨v, hvA, hvB, hyv, hvz⟩
  · exact Or.inl (D.le_trans h₁ h₂)
  · exact Or.inr (Or.inr (Or.inl ⟨y, D.le_mem_right h₁, D.le_mem_left h₂, h₁, h₂⟩))
  · exact Or.inr (Or.inr (Or.inl ⟨v, hvA, hvB, D.le_trans h₁ hyv, hvz⟩))
  · have := (h.agree y v (D.le_mem_right h₁) (D.le_mem_left hyv) hvA hvB).2 hyv
    exact Or.inl (D.le_trans h₁ (D.le_trans this hvz))
  · exact Or.inr (Or.inr (Or.inr ⟨y, D.le_mem_left h₂, D.le_mem_right h₁, h₁, h₂⟩))
  · exact Or.inr (Or.inl (D.le_trans h₁ h₂))
  · have := (h.agree y v (D.le_mem_left hyv) (D.le_mem_right h₁) hvA hvB).1 hyv
    exact Or.inr (Or.inl (D.le_trans h₁ (D.le_trans this hvz)))
  · exact Or.inr (Or.inr (Or.inr ⟨v, hvA, hvB, D.le_trans h₁ hyv, hvz⟩))
  · have := (h.agree u y huA huB (D.le_mem_left h₂) (D.le_mem_right huy)).2 huy
    exact Or.inl (D.le_trans hxu (D.le_trans this h₂))
  · exact Or.inr (Or.inr (Or.inl ⟨u, huA, huB, hxu, D.le_trans huy h₂⟩))
  · have := (h.agree u y huA huB (D.le_mem_left hyv) (D.le_mem_right huy)).2 huy
    exact Or.inr (Or.inr (Or.inl ⟨v, hvA, hvB, D.le_trans hxu (D.le_trans this hyv), hvz⟩))
  · have hyA := h.convex_right u y v huA hvA huy hyv
    have := (h.agree u v huA huB hvA hvB).2 (D.le_trans huy hyv)
    exact Or.inl (D.le_trans hxu (D.le_trans this hvz))
  · exact Or.inr (Or.inr (Or.inr ⟨u, huA, huB, hxu, D.le_trans huy h₂⟩))
  · have := (h.agree u y huA huB (D.le_mem_right huy) (D.le_mem_left h₂)).1 huy
    exact Or.inr (Or.inl (D.le_trans hxu (D.le_trans this h₂)))
  · have hyB := h.convex_left u y v huB hvB huy hyv
    have := (h.agree u v huA huB hvA hvB).1 (D.le_trans huy hyv)
    exact Or.inr (Or.inl (D.le_trans hxu (D.le_trans this hvz)))
  · have := (h.agree u y huA huB (D.le_mem_right huy) (D.le_mem_left hyv)).1 huy
    exact Or.inr (Or.inr (Or.inr ⟨v, hvA, hvB, D.le_trans hxu (D.le_trans this hyv), hvz⟩))

/-- **The causal relation of `P` is generated by the pieces**: `x ≤_P y` iff `twoPieceRel`
(absolute minimality on the cover `{A, B}`, then `rel_trans`). -/
theorem le_top_iff (h : D.TwoPiece A B) {x y : P} : D.le ⊤ x y ↔ twoPieceRel D A B x y := by
  constructor
  · intro hxy
    have hS : ∀ z ∈ (⊤ : Opens P), ∃ O ∈ ({A, B} : Set (Opens P)), z ∈ O := fun z _ =>
      (h.cover z).elim (fun hz => ⟨A, Or.inl rfl, hz⟩) (fun hz => ⟨B, Or.inr rfl, hz⟩)
    have hc := (h.absolutelyMinimalOn _ hS ⊤ le_rfl x y).1 hxy
    clear hxy
    induction hc with
    | single hl =>
      obtain ⟨O, hO, hab⟩ := hl
      rw [top_inf_eq] at hab
      rcases hO with rfl | rfl
      · exact Or.inl hab
      · exact Or.inr (Or.inl hab)
    | tail _ hl ih =>
      obtain ⟨O, hO, hab⟩ := hl
      rw [top_inf_eq] at hab
      refine h.rel_trans ih ?_
      rcases hO with rfl | rfl
      · exact Or.inl hab
      · exact Or.inr (Or.inl hab)
  · rintro (h₁ | h₁ | ⟨u, -, -, hxu, huy⟩ | ⟨u, -, -, hxu, huy⟩)
    · exact D.le_mono le_top h₁
    · exact D.le_mono le_top h₁
    · exact D.le_trans (D.le_mono le_top hxu) (D.le_mono le_top huy)
    · exact D.le_trans (D.le_mono le_top hxu) (D.le_mono le_top huy)

/-- **Between two points of a piece, the relation of `P` is the piece's.** -/
theorem le_of_le_top (h : D.TwoPiece A B) {x y : P} (hx : x ∈ A) (hy : y ∈ A)
    (hxy : D.le ⊤ x y) : D.le A x y := by
  rcases h.le_top_iff.1 hxy with h₁ | h₁ | ⟨u, huA, huB, hxu, huy⟩ | ⟨u, huA, huB, hxu, huy⟩
  · exact h₁
  · exact (h.agree x y hx (D.le_mem_left h₁) hy (D.le_mem_right h₁)).2 h₁
  · exact D.le_trans hxu ((h.agree u y huA huB hy (D.le_mem_right huy)).2 huy)
  · exact D.le_trans ((h.agree x u hx (D.le_mem_left hxu) huA huB).2 hxu) huy

/-- **Each piece is causally convex in `P`** (the exit/re-entry argument: a chain leaving `A` runs
in `B` between two points of the overlap, which is causally convex in `B`). -/
theorem mem_of_le_top (h : D.TwoPiece A B) {x y z : P} (hx : x ∈ A) (hz : z ∈ A)
    (hxy : D.le ⊤ x y) (hyz : D.le ⊤ y z) : y ∈ A := by
  by_contra hy
  obtain ⟨u, huA, huy⟩ : ∃ u, u ∈ A ∧ D.le B u y := by
    rcases h.le_top_iff.1 hxy with h₁ | h₁ | ⟨u, huA, -, -, huy⟩ | ⟨u, -, -, -, huy⟩
    · exact absurd (D.le_mem_right h₁) hy
    · exact ⟨x, hx, h₁⟩
    · exact ⟨u, huA, huy⟩
    · exact absurd (D.le_mem_right huy) hy
  obtain ⟨v, hvA, hyv⟩ : ∃ v, v ∈ A ∧ D.le B y v := by
    rcases h.le_top_iff.1 hyz with h₂ | h₂ | ⟨v, -, -, hyv, -⟩ | ⟨v, hvA, -, hyv, -⟩
    · exact absurd (D.le_mem_left h₂) hy
    · exact ⟨z, hz, h₂⟩
    · exact absurd (D.le_mem_left hyv) hy
    · exact ⟨v, hvA, hyv⟩
  exact hy (h.convex_right u y v huA hvA huy hyv)

/-- **A relation from `A` to `B` passes through the overlap**: `x ∈ A`, `y ∈ B`, `x ≤_P y` give
`u ∈ A ∩ B` with `x ≤_A u ≤_B y`. -/
theorem exists_mid (h : D.TwoPiece A B) {x y : P} (hx : x ∈ A) (hy : y ∈ B)
    (hxy : D.le ⊤ x y) : ∃ u, u ∈ A ∧ u ∈ B ∧ D.le A x u ∧ D.le B u y := by
  rcases h.le_top_iff.1 hxy with h₁ | h₁ | ⟨u, huA, huB, hxu, huy⟩ | ⟨u, huA, huB, hxu, huy⟩
  · exact ⟨y, D.le_mem_right h₁, hy, h₁, D.le_refl hy⟩
  · exact ⟨x, hx, D.le_mem_left h₁, D.le_refl hx, h₁⟩
  · exact ⟨u, huA, huB, hxu, huy⟩
  · have hyA := D.le_mem_right huy
    have h' := (h.agree x u hx (D.le_mem_left hxu) huA huB).2 hxu
    exact ⟨y, hyA, hy, D.le_trans h' huy, D.le_refl hy⟩

/-- The diamonds of `P` between two points of a piece are the piece's. -/
theorem diamond_top_eq (h : D.TwoPiece A B) {p q : P} (hp : p ∈ A) (hq : q ∈ A) :
    D.diamond ⊤ p q = D.diamond A p q := by
  ext z
  rw [mem_diamond, mem_diamond]
  constructor
  · rintro ⟨h₁, h₂⟩
    have hz := h.mem_of_le_top hp hq h₁ h₂
    exact ⟨h.le_of_le_top hp hz h₁, h.le_of_le_top hz hq h₂⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨D.le_mono le_top h₁, D.le_mono le_top h₂⟩

/-- **`P` is causal when both pieces are.** -/
theorem isCausal (h : D.TwoPiece A B)
    (hA : ∀ x y, D.le A x y → D.le A y x → x = y) (hB : ∀ x y, D.le B x y → D.le B y x → x = y) :
    D.IsCausal := by
  intro x y hxy hyx
  rcases h.cover x with hx | hx
  · have hy := h.mem_of_le_top hx hx hxy hyx
    exact hA x y (h.le_of_le_top hx hy hxy) (h.le_of_le_top hy hx hyx)
  · have hy := h.symm.mem_of_le_top hx hx hxy hyx
    exact hB x y (h.symm.le_of_le_top hx hy hxy) (h.symm.le_of_le_top hy hx hyx)

/-- **A common Cauchy surface of the two pieces is a Cauchy surface of `P`** (Sbierski, proof
of Thm 2.7, step 4): existence through the component of the curve in one piece; uniqueness
because two points of `S` on one curve are related in `P`, hence in `A` (`le_of_le_top`), where
`S` is acausal. -/
theorem isCauchySurface [T2Space P] (h : D.TwoPiece A B) (hcaus : D.IsCausal) {S : Set P}
    (hSsub : S ⊆ A) (hSA : D.IsCauchySurfaceOn A S) (hSB : D.IsCauchySurfaceOn B S)
    (hac : ∀ x ∈ S, ∀ y ∈ S, D.le A x y → x = y) : D.IsCauchySurface S := by
  intro I c hc
  obtain ⟨t₀, ht₀⟩ := hc.1.nonempty
  have key : ∀ W : Opens P, D.IsCauchySurfaceOn W S → c t₀ ∈ W → ∃ x, x ∈ c '' I ∩ S :=
    fun W hW hmem => by
      obtain ⟨_, ⟨⟨τ, hτ, rfl⟩, hxS⟩, -⟩ := hW _ c
        (inextensible_ordConnectedComponent_of_le (U := ⊤) (fun x y h₁ h₂ => hcaus h₁ h₂)
          le_top hc ht₀ hmem)
      exact ⟨c τ, ⟨τ, (ordConnectedComponent_subset hτ).1, rfl⟩, hxS⟩
  obtain ⟨x, hx⟩ := (h.cover (c t₀)).elim (key A hSA) (key B hSB)
  refine ⟨x, hx, ?_⟩
  rintro _ ⟨⟨s, hs, rfl⟩, hyS⟩
  obtain ⟨⟨t, ht, rfl⟩, hxS⟩ := hx
  rcases le_total s t with hst | hts
  · exact hac _ hyS _ hxS (h.le_of_le_top (hSsub hyS) (hSsub hxS) (hc.1.le_of_le hs ht hst))
  · exact (hac _ hxS _ hyS (h.le_of_le_top (hSsub hxS) (hSsub hyS) (hc.1.le_of_le ht hs hts))).symm

end TwoPiece

end TwoPiece

/-! ### Charts of the pieces, and the compactness of the diamonds of `P` -/

section PieceChart

variable {P : Type u} [TopologicalSpace P] {D : Causality P} {A B : Opens P}
  {X : Type u} [TopologicalSpace X] {Y : Type u} [TopologicalSpace Y]

variable (D A) in
/-- **A chart of the piece `A`**: an open embedding `e : X → P` onto `A` matching the relation of
the spacetime `X` with that of `A` (for the gluing: `ι₁` of the development `N₁`). -/
structure PieceChart (C : Causality X) (e : X → P) : Prop where
  isOpenEmbedding : IsOpenEmbedding e
  range_eq : range e = (A : Set P)
  le_iff : ∀ a b, D.le A (e a) (e b) ↔ C.le ⊤ a b

namespace PieceChart

variable {C : Causality X} {e : X → P}

theorem mem (he : PieceChart D A C e) (a : X) : e a ∈ A := by
  rw [← SetLike.mem_coe, ← he.range_eq]; exact mem_range_self a

theorem exists_eq (he : PieceChart D A C e) {z : P} (hz : z ∈ A) : ∃ a, e a = z := by
  rw [← SetLike.mem_coe, ← he.range_eq] at hz; exact hz

/-- The diamonds of the piece are the images of those of `X`. -/
theorem diamond_eq (he : PieceChart D A C e) (a b : X) :
    D.diamond A (e a) (e b) = e '' C.diamond ⊤ a b := by
  ext z
  rw [mem_diamond]
  constructor
  · rintro ⟨h₁, h₂⟩
    obtain ⟨c, rfl⟩ := he.exists_eq (D.le_mem_right h₁)
    exact ⟨c, mem_diamond.2 ⟨(he.le_iff a c).1 h₁, (he.le_iff c b).1 h₂⟩, rfl⟩
  · rintro ⟨c, hc, rfl⟩
    exact ⟨(he.le_iff a c).2 (mem_diamond.1 hc).1, (he.le_iff c b).2 (mem_diamond.1 hc).2⟩

/-- The relation of the piece is antisymmetric when `X` is causal. -/
theorem antisymm (he : PieceChart D A C e) (hC : C.IsCausal) :
    ∀ x y, D.le A x y → D.le A y x → x = y := by
  intro x y hxy hyx
  obtain ⟨a, rfl⟩ := he.exists_eq (D.le_mem_left hxy)
  obtain ⟨b, rfl⟩ := he.exists_eq (D.le_mem_right hxy)
  rw [hC ((he.le_iff a b).1 hxy) ((he.le_iff b a).1 hyx)]

/-- A diamond of `P` between two points of a globally hyperbolic piece is compact. -/
theorem isCompact_diamond (h : D.TwoPiece A B) (he : PieceChart D A C e)
    (hG : C.GloballyHyperbolic) {p q : P} (hp : p ∈ A) (hq : q ∈ A) :
    IsCompact (D.diamond ⊤ p q) := by
  obtain ⟨a, rfl⟩ := he.exists_eq hp
  obtain ⟨b, rfl⟩ := he.exists_eq hq
  rw [h.diamond_top_eq hp hq, he.diamond_eq]
  exact (hG.2 a b).image he.isOpenEmbedding.continuous

end PieceChart

/-- **A diamond of `P` from the past piece to the future piece is compact** (the mixed case of
the global hyperbolicity of the gluing). For `p = e a ∈ A ∖ B`, `q = f b ∈ B ∖ A`, `S`, `T` Cauchy
surfaces of `X`, `Y` with the same image `Σ̃` in `P`:
`J(p, q) = e(J⁻(S) ∩ J⁺(a) ∩ J⁻(F)) ∪ f(J⁺(T) ∩ J⁻(b) ∩ J⁺(G))`, `F = e⁻¹ f(T ∩ J⁻(b))`,
`G = f⁻¹ e(S ∩ J⁺(a))` compact; each part is a closed subset of a compact half-diamond
(`CauchySide`). A point of `J(p, q)` in `A` and in the past of `S` reaches `q` through the overlap,
hence (crossing `S` in `X`, or `T` in `Y`) through `Σ̃`; a point of `A` in the future of `S` lies in
the overlap (convexity), and is treated in `B`. -/
theorem TwoPiece.isCompact_diamond_mixed [T2Space X] [T2Space Y] (h : D.TwoPiece A B)
    {C : Causality X} {C' : Causality Y} {e : X → P} {f : Y → P}
    (he : PieceChart D A C e) (hf : PieceChart D B C' f) {S : Set X} {T : Set Y}
    (hS : CauchySide C S) (hT : CauchySide C' T) (hST : e '' S = f '' T)
    {p q : P} (hpA : p ∈ A) (hpB : p ∉ B) (hqB : q ∈ B) (hqA : q ∉ A) :
    IsCompact (D.diamond ⊤ p q) := by
  obtain ⟨a, rfl⟩ := he.exists_eq hpA
  obtain ⟨b, rfl⟩ := hf.exists_eq hqB
  have hσ : ∀ σ ∈ S, ∃ τ ∈ T, f τ = e σ := fun σ hσS => by
    have : e σ ∈ f '' T := hST ▸ mem_image_of_mem e hσS
    exact this
  have hτ : ∀ τ ∈ T, ∃ σ ∈ S, e σ = f τ := fun τ hτT => by
    have : f τ ∈ e '' S := hST.symm ▸ mem_image_of_mem f hτT
    exact this
  have hσB : ∀ σ ∈ S, e σ ∈ B := fun σ hσS => by
    obtain ⟨τ, -, e'⟩ := hσ σ hσS; rw [← e']; exact hf.mem τ
  have hτA : ∀ τ ∈ T, f τ ∈ A := fun τ hτT => by
    obtain ⟨σ, -, e'⟩ := hτ τ hτT; rw [← e']; exact he.mem σ
  set F : Set X := e ⁻¹' (f '' (T ∩ C'.Jminus ⊤ {b})) with hFdef
  set G : Set Y := f ⁻¹' (e '' (S ∩ C.Jplus ⊤ {a})) with hGdef
  have hFc : IsCompact F := by
    have h1 : IsCompact (T ∩ C'.Jminus ⊤ {b}) :=
      (hT.isCompact_future b).of_isClosed_subset
        (hT.isClosed.inter (isClosed_Jminus_of_isCompact hT.isClosed_le isCompact_singleton))
        (fun y hy => ⟨⟨y, hy.1, C'.le_refl trivial⟩, hy.2⟩)
    refine he.isOpenEmbedding.isInducing.isCompact_preimage'
      (h1.image hf.isOpenEmbedding.continuous) ?_
    rintro _ ⟨τ, ⟨hτT, -⟩, rfl⟩
    obtain ⟨σ, -, e'⟩ := hτ τ hτT
    exact ⟨σ, e'⟩
  have hGc : IsCompact G := by
    have h1 : IsCompact (S ∩ C.Jplus ⊤ {a}) :=
      (hS.isCompact_past a).of_isClosed_subset
        (hS.isClosed.inter (isClosed_Jplus_of_isCompact hS.isClosed_le isCompact_singleton))
        (fun x hx => ⟨⟨x, hx.1, C.le_refl trivial⟩, hx.2⟩)
    refine hf.isOpenEmbedding.isInducing.isCompact_preimage'
      (h1.image he.isOpenEmbedding.continuous) ?_
    rintro _ ⟨σ, ⟨hσS, -⟩, rfl⟩
    obtain ⟨τ, -, e'⟩ := hσ σ hσS
    exact ⟨τ, e'⟩
  set K₁ : Set X := C.Jminus ⊤ S ∩ C.Jplus ⊤ {a} ∩ C.Jminus ⊤ F with hK₁def
  set K₂ : Set Y := C'.Jplus ⊤ T ∩ C'.Jminus ⊤ {b} ∩ C'.Jplus ⊤ G with hK₂def
  have hK₁ : IsCompact K₁ :=
    (hS.isCompact_past a).inter_right (isClosed_Jminus_of_isCompact hS.isClosed_le hFc)
  have hK₂ : IsCompact K₂ :=
    (hT.isCompact_future b).inter_right (isClosed_Jplus_of_isCompact hT.isClosed_le hGc)
  suffices heq : D.diamond ⊤ (e a) (f b) = e '' K₁ ∪ f '' K₂ by
    rw [heq]
    exact (hK₁.image he.isOpenEmbedding.continuous).union
      (hK₂.image hf.isOpenEmbedding.continuous)
  ext z
  constructor
  · intro hz
    obtain ⟨hpz, hzq⟩ := mem_diamond.1 hz
    obtain ⟨u₀, hu₀A, hu₀B, hpu₀, hu₀q⟩ :=
      h.exists_mid (he.mem a) (hf.mem b) (D.le_trans hpz hzq)
    have ha : a ∈ C.Jminus ⊤ S := by
      rcases hS.cover a with ⟨σ, hσS, hσa⟩ | ha
      · exact absurd (h.convex_left (e σ) (e a) u₀ (hσB σ hσS) hu₀B
          ((he.le_iff σ a).2 hσa) hpu₀) hpB
      · exact ha
    have hb : b ∈ C'.Jplus ⊤ T := by
      rcases hT.cover b with hb | ⟨τ, hτT, hbτ⟩
      · exact hb
      · exact absurd (h.convex_right u₀ (f b) (f τ) hu₀A (hτA τ hτT) hu₀q
          ((hf.le_iff b τ).2 hbτ)) hqA
    have P1 : ∀ c, e c = z → c ∈ C.Jminus ⊤ S → z ∈ e '' K₁ ∪ f '' K₂ := by
      rintro c rfl hcS
      have hac : C.le ⊤ a c := (he.le_iff a c).1 (h.le_of_le_top (he.mem a) (he.mem c) hpz)
      obtain ⟨u, huA, huB, hzu, huq⟩ := h.exists_mid (he.mem c) (hf.mem b) hzq
      obtain ⟨u₁, rfl⟩ := he.exists_eq huA
      obtain ⟨u₂, hu₂⟩ := hf.exists_eq huB
      have hcu : C.le ⊤ c u₁ := (he.le_iff c u₁).1 hzu
      have hu₂b : C'.le ⊤ u₂ b := (hf.le_iff u₂ b).1 (hu₂ ▸ huq)
      obtain ⟨σ, hσF, hcσ⟩ : ∃ σ ∈ F, C.le ⊤ c σ := by
        rcases hS.cover u₁ with hu₁ | ⟨σ', hσ'S, hu₁σ'⟩
        · obtain ⟨σ, hσS, hcσ, hσu⟩ := hS.crossing c u₁ hcS hu₁ hcu
          obtain ⟨τ, hτT, hfτ⟩ := hσ σ hσS
          have h1 : D.le B (e σ) (e u₁) :=
            (h.agree _ _ (he.mem σ) (hσB σ hσS) huA huB).1 ((he.le_iff σ u₁).2 hσu)
          rw [← hfτ, ← hu₂] at h1
          have hτu : C'.le ⊤ τ u₂ := (hf.le_iff τ u₂).1 h1
          exact ⟨σ, ⟨τ, ⟨hτT, by simpa using C'.le_trans hτu hu₂b⟩, hfτ⟩, hcσ⟩
        · obtain ⟨τ', hτ'T, hfτ'⟩ := hσ σ' hσ'S
          have h1 : D.le B (e u₁) (e σ') :=
            (h.agree _ _ huA huB (he.mem σ') (hσB σ' hσ'S)).1 ((he.le_iff u₁ σ').2 hu₁σ')
          rw [← hfτ', ← hu₂] at h1
          have hu₂T : u₂ ∈ C'.Jminus ⊤ T := ⟨τ', hτ'T, (hf.le_iff u₂ τ').1 h1⟩
          obtain ⟨τ, hτT, hu₂τ, hτb⟩ := hT.crossing u₂ b hu₂T hb hu₂b
          obtain ⟨σ, hσS, heσ⟩ := hτ τ hτT
          have h2 : D.le B (e u₁) (e σ) := by
            rw [← hu₂, heσ]; exact (hf.le_iff u₂ τ).2 hu₂τ
          have h3 := (h.agree _ _ huA huB (he.mem σ) (hσB σ hσS)).2 h2
          exact ⟨σ, ⟨τ, ⟨hτT, by simpa using hτb⟩, heσ.symm⟩,
            C.le_trans hcu ((he.le_iff u₁ σ).1 h3)⟩
      exact Or.inl ⟨c, ⟨⟨hcS, by simpa using hac⟩, σ, hσF, hcσ⟩, rfl⟩
    have P2 : ∀ d, f d = z → d ∈ C'.Jplus ⊤ T → z ∈ e '' K₁ ∪ f '' K₂ := by
      rintro d rfl hdT
      have hdb : C'.le ⊤ d b :=
        (hf.le_iff d b).1 (h.symm.le_of_le_top (hf.mem d) (hf.mem b) hzq)
      obtain ⟨u, huA, huB, hpu, huz⟩ := h.exists_mid (he.mem a) (hf.mem d) hpz
      obtain ⟨u₁, rfl⟩ := he.exists_eq huA
      obtain ⟨u₂, hu₂⟩ := hf.exists_eq huB
      have hau : C.le ⊤ a u₁ := (he.le_iff a u₁).1 hpu
      have hu₂d : C'.le ⊤ u₂ d := (hf.le_iff u₂ d).1 (hu₂ ▸ huz)
      obtain ⟨τ, hτG, hτd⟩ : ∃ τ ∈ G, C'.le ⊤ τ d := by
        rcases hT.cover u₂ with ⟨τ', hτ'T, hτ'u₂⟩ | hu₂T
        · obtain ⟨σ', hσ'S, heσ'⟩ := hτ τ' hτ'T
          have h1 : D.le A (e σ') (e u₁) := by
            have h0 : D.le B (f τ') (f u₂) := (hf.le_iff τ' u₂).2 hτ'u₂
            rw [← heσ', hu₂] at h0
            exact (h.agree _ _ (he.mem σ') (hσB σ' hσ'S) huA huB).2 h0
          have hu₁S : u₁ ∈ C.Jplus ⊤ S := ⟨σ', hσ'S, (he.le_iff σ' u₁).1 h1⟩
          obtain ⟨σ, hσS, haσ, hσu₁⟩ := hS.crossing a u₁ ha hu₁S hau
          obtain ⟨τ, hτT, hfτ⟩ := hσ σ hσS
          have h2 : D.le B (f τ) (f u₂) := by
            rw [hfτ, hu₂]
            exact (h.agree _ _ (he.mem σ) (hσB σ hσS) huA huB).1 ((he.le_iff σ u₁).2 hσu₁)
          exact ⟨τ, ⟨σ, ⟨hσS, by simpa using haσ⟩, hfτ.symm⟩,
            C'.le_trans ((hf.le_iff τ u₂).1 h2) hu₂d⟩
        · obtain ⟨τ, hτT, hu₂τ, hτd⟩ := hT.crossing u₂ d hu₂T hdT hu₂d
          obtain ⟨σ, hσS, heσ⟩ := hτ τ hτT
          have h2 : D.le A (e u₁) (e σ) := by
            have h0 : D.le B (f u₂) (f τ) := (hf.le_iff u₂ τ).2 hu₂τ
            rw [hu₂, ← heσ] at h0
            exact (h.agree _ _ huA huB (he.mem σ) (hσB σ hσS)).2 h0
          exact ⟨τ, ⟨σ, ⟨hσS, by simpa using C.le_trans hau ((he.le_iff u₁ σ).1 h2)⟩, heσ⟩,
            hτd⟩
      exact Or.inr ⟨d, ⟨⟨hdT, by simpa using hdb⟩, τ, hτG, hτd⟩, rfl⟩
    rcases h.cover z with hzA | hzB
    · obtain ⟨c, rfl⟩ := he.exists_eq hzA
      rcases hS.cover c with ⟨σ₀, hσ₀S, hσ₀c⟩ | hcS
      · obtain ⟨u, -, huB, hzu, -⟩ := h.exists_mid (he.mem c) (hf.mem b) hzq
        have hzB := h.convex_left (e σ₀) (e c) u (hσB σ₀ hσ₀S) huB ((he.le_iff σ₀ c).2 hσ₀c) hzu
        obtain ⟨d, hd⟩ := hf.exists_eq hzB
        obtain ⟨τ₀, hτ₀T, hfτ₀⟩ := hσ σ₀ hσ₀S
        have h1 : D.le B (f τ₀) (f d) := by
          rw [hfτ₀, hd]
          exact (h.agree _ _ (he.mem σ₀) (hσB σ₀ hσ₀S) (he.mem c) hzB).1
            ((he.le_iff σ₀ c).2 hσ₀c)
        exact P2 d hd ⟨τ₀, hτ₀T, (hf.le_iff τ₀ d).1 h1⟩
      · exact P1 c rfl hcS
    · obtain ⟨d, rfl⟩ := hf.exists_eq hzB
      rcases hT.cover d with hdT | ⟨τ₀, hτ₀T, hdτ₀⟩
      · exact P2 d rfl hdT
      · obtain ⟨u, huA, -, -, huz⟩ := h.exists_mid (he.mem a) (hf.mem d) hpz
        have hzA := h.convex_right u (f d) (f τ₀) huA (hτA τ₀ hτ₀T) huz
          ((hf.le_iff d τ₀).2 hdτ₀)
        obtain ⟨c, hc⟩ := he.exists_eq hzA
        obtain ⟨σ₀, hσ₀S, heσ₀⟩ := hτ τ₀ hτ₀T
        have h1 : D.le A (e c) (e σ₀) := by
          rw [hc, heσ₀]
          exact (h.agree _ _ hzA (hf.mem d) (hτA τ₀ hτ₀T) (hf.mem τ₀)).2
            ((hf.le_iff d τ₀).2 hdτ₀)
        exact P1 c hc ⟨σ₀, hσ₀S, (he.le_iff c σ₀).1 h1⟩
  · rintro (⟨c, ⟨⟨-, hac⟩, σ, hσF, hcσ⟩, rfl⟩ | ⟨d, ⟨⟨-, hdb⟩, τ, hτG, hτd⟩, rfl⟩)
    · obtain ⟨τ, ⟨-, hτb⟩, hfτ⟩ := hσF
      refine mem_diamond.2 ⟨D.le_mono le_top ((he.le_iff a c).2 (by simpa using hac)), ?_⟩
      have h1 : D.le ⊤ (e c) (e σ) := D.le_mono le_top ((he.le_iff c σ).2 hcσ)
      have h2 : D.le ⊤ (f τ) (f b) := D.le_mono le_top ((hf.le_iff τ b).2 (by simpa using hτb))
      rw [hfτ] at h2
      exact D.le_trans h1 h2
    · obtain ⟨σ, ⟨-, haσ⟩, heσ⟩ := hτG
      refine mem_diamond.2 ⟨?_, D.le_mono le_top ((hf.le_iff d b).2 (by simpa using hdb))⟩
      have h1 : D.le ⊤ (e a) (e σ) := D.le_mono le_top ((he.le_iff a σ).2 (by simpa using haσ))
      have h2 : D.le ⊤ (f τ) (f d) := D.le_mono le_top ((hf.le_iff τ d).2 hτd)
      rw [← heσ] at h2
      exact D.le_trans h1 h2

/-- **The two-piece spacetime is globally hyperbolic** when both pieces are, through charts, with
a common Cauchy surface: causal (`TwoPiece.isCausal`), and every diamond compact — inside a piece
by `PieceChart.isCompact_diamond`, across the pieces by `isCompact_diamond_mixed` in either time
orientation. -/
theorem TwoPiece.globallyHyperbolic [T2Space X] [T2Space Y] (h : D.TwoPiece A B)
    {C : Causality X} {C' : Causality Y} {e : X → P} {f : Y → P}
    (he : PieceChart D A C e) (hf : PieceChart D B C' f) (hG : C.GloballyHyperbolic)
    (hG' : C'.GloballyHyperbolic) {S : Set X} {T : Set Y}
    (hS : CauchySide C S) (hT : CauchySide C' T) (hST : e '' S = f '' T) :
    D.GloballyHyperbolic := by
  refine ⟨h.isCausal (he.antisymm hG.1) (hf.antisymm hG'.1), fun p q => ?_⟩
  by_cases hpA : p ∈ A
  · by_cases hqA : q ∈ A
    · exact he.isCompact_diamond h hG hpA hqA
    have hqB : q ∈ B := (h.cover q).resolve_left hqA
    by_cases hpB : p ∈ B
    · exact hf.isCompact_diamond h.symm hG' hpB hqB
    · exact h.isCompact_diamond_mixed he hf hS hT hST hpA hpB hqB hqA
  · have hpB : p ∈ B := (h.cover p).resolve_left hpA
    by_cases hqB : q ∈ B
    · exact hf.isCompact_diamond h.symm hG' hpB hqB
    have hqA : q ∈ A := (h.cover q).resolve_right hqB
    exact h.symm.isCompact_diamond_mixed hf he hT hS hST.symm hpB hpA hqA hqB

end PieceChart

end Causality

namespace CBG

/-! ### Developments: Cauchy sides, charts, relations along the MCGHD -/

section Private

open Relation

variable {M' : Type*} {N' : Type*} [TopologicalSpace M'] [TopologicalSpace N']
  {C : Causality M'} {D : Causality N'} {φ : M' → N'}

-- Private copy of the lifting lemma of `CBG/Pgcd` (itself a copy of the one in
-- `Flat/FlatSpacetime.lean`), so that this module imports no Barbot-campaign module.
omit [TopologicalSpace M'] [TopologicalSpace N'] in
private theorem ppcm_lift_transGen_image (hinj : Injective φ) {R : M' → M' → Prop}
    (hR : ∀ {a b c}, R a b → R b c → R a c) {x : M'} {b' : N'}
    (h : TransGen (fun a' b' => ∃ a b, a' = φ a ∧ b' = φ b ∧ R a b) (φ x) b') :
    ∃ b, b' = φ b ∧ R x b := by
  induction h with
  | single hl =>
    obtain ⟨a, b, ha, rfl, hab⟩ := hl
    exact ⟨b, rfl, hinj ha ▸ hab⟩
  | tail _ hl ih =>
    obtain ⟨c, rfl, hxc⟩ := ih
    obtain ⟨a, b, ha, rfl, hab⟩ := hl
    exact ⟨b, rfl, hR hxc (hinj ha ▸ hab)⟩

/-- An injective local isomorphism into a causality absolutely minimal on every open set reflects
the causal relation (private copy of `Flat.LocalIso.rel_of_image`, causal half; the same
statement and proof as `CBG/Pgcd`'s private `rel_of_image_localIso`). -/
private theorem ppcm_le_of_image (hφ : LocalIsomorphism C D φ) (hinj : Injective φ)
    (hD : ∀ U : Opens N', D.AbsolutelyMinimalOn U) (V : Opens M') (U : Opens N')
    (hU : (U : Set N') = φ '' V) (x y : M') (hxy : D.le U (φ x) (φ y)) : C.le V x y := by
  choose V₁ hx₁ _hi₁ hV₁ using hφ.2
  have himg : ∀ O : Opens M', IsOpen (φ '' O) := fun O => hφ.1.isOpenMap _ O.isOpen
  let O' : M' → Opens N' := fun z => ⟨φ '' ((V ⊓ V₁ z : Opens M') : Set M'), himg _⟩
  let S : Set (Opens N') := range O'
  have hS : ∀ p ∈ U, ∃ O ∈ S, p ∈ O := by
    intro p hp
    rw [← SetLike.mem_coe, hU] at hp
    obtain ⟨a, ha, rfl⟩ := hp
    exact ⟨O' a, ⟨a, rfl⟩, a, ⟨ha, hx₁ a⟩, rfl⟩
  have hOU : ∀ z, (U ⊓ O' z : Set N') = φ '' (V ⊓ V₁ z : Opens M') := by
    intro z
    apply Set.inter_eq_right.2
    rintro _ ⟨w, hw, rfl⟩
    rw [hU]; exact ⟨w, hw.1, rfl⟩
  have hc := ((hD U) S hS U le_rfl _ _).1 hxy
  have hc' : TransGen (fun a' b' => ∃ a b, a' = φ a ∧ b' = φ b ∧ C.le V a b) (φ x) (φ y) := by
    refine TransGen.mono (fun a' b' => ?_) hc
    rintro ⟨O, ⟨z, rfl⟩, hab⟩
    have ha := D.le_mem_left hab
    have hb := D.le_mem_right hab
    obtain ⟨a, ha', rfl⟩ : a' ∈ φ '' (V ⊓ V₁ z : Opens M') := hOU z ▸ ha
    obtain ⟨b, hb', rfl⟩ : b' ∈ φ '' (V ⊓ V₁ z : Opens M') := hOU z ▸ hb
    exact ⟨a, b, rfl, rfl, C.le_mono inf_le_left
      (((hV₁ z _ inf_le_right _ (hOU z) a ha' b hb').1).2 hab)⟩
  obtain ⟨b, hb, hxb⟩ :=
    ppcm_lift_transGen_image hinj (R := C.le V) (fun h₁ h₂ => C.le_trans h₁ h₂) hc'
  rwa [← hinj hb] at hxb

end Private

section DevFacts

variable {𝔊 : Geometry.{u}} {M₀ : Type u} [TopologicalSpace M₀] {s₀ : 𝔊.Str M₀}

/-- **A Cauchy surface of a development gives a `CauchySide`** (A2: `isCompact_*`,
`K_densite_sing`, `tarentin`; the development's causal arc-connectedness and curve extension). -/
theorem Dev.cauchySide (N : Dev 𝔊.toPreGeometry s₀) {S : Set N.carrier}
    (hS : (𝔊.causality N.str).IsCauchySurface S) :
    Causality.CauchySide (𝔊.causality N.str) S := by
  have hG := N.causality_globallyHyperbolic
  have hA := 𝔊.singularFlatAxioms N.str
  have hC := N.causality_causallyArcConnected
  have hext := N.causality_curvesExtend
  have hac := hS.isAcausal hC hext
  have hJm : IsClosed ((𝔊.causality N.str).Jminus ⊤ S) :=
    Causality.isClosed_Jminus_of_dense (fun x => (hA.K_densite_sing x).2)
      (𝔊.isCompact_Jminus_inter_Jplus N.str hG S hS)
  have hJp : IsClosed ((𝔊.causality N.str).Jplus ⊤ S) :=
    Causality.isClosed_Jminus_of_dense (C := (𝔊.causality N.str).dual)
      (fun x => (hA.K_densite_sing x).1) (𝔊.isCompact_Jplus_inter_Jminus N.str hG S hS)
  exact
    { cover := Causality.mem_Jplus_union_Jminus_of_isCauchySurface hext hS
      crossing := fun x y hx hy hxy =>
        Causality.exists_mem_cauchy_between hG.1 hC hext hS hac hx hy hxy
      isClosed_le := hG.isClosed_le hA.tarentin
      isClosed := by
        rw [← Causality.Jplus_inter_Jminus_eq hG.1 hac]; exact hJp.inter hJm
      isCompact_future := 𝔊.isCompact_Jplus_inter_Jminus N.str hG S hS
      isCompact_past := 𝔊.isCompact_Jminus_inter_Jplus N.str hG S hS }

/-- **A structure morphism `e : X → P` on `X`, injective, is a chart of the open set `e(X)`** for
the generated causalities: it is an open embedding, and the relation of `e(X)` between two
images is that of `X` (`→` by local isomorphism and absolute minimality, the private
`ppcm_le_of_image`; `←` the morphism). -/
theorem pieceChart_of_isMor {X P : Type u} [TopologicalSpace X] [TopologicalSpace P]
    {s : 𝔊.Str X} {t : 𝔊.Str P} {e : X → P} (he : 𝔊.IsMor s t ⊤ e) (hinj : Injective e)
    (A : Opens P) (hA : (A : Set P) = range e) :
    Causality.PieceChart (𝔊.causality t) A (𝔊.causality s) e := by
  have hE : IsEMorphism (𝔊.causality s) (𝔊.causality t) e := 𝔊.isEMorphismOn_of_isMor he
  have hcont : Continuous e := by
    have := hE.continuousOn; rwa [Opens.coe_top, continuousOn_univ] at this
  refine ⟨.of_continuous_injective_isOpenMap hcont hinj fun V hV =>
    hE.isOpen_image ⟨V, hV⟩ le_top, hA.symm, fun a b => ⟨fun h => ?_, fun h => ?_⟩⟩
  · exact ppcm_le_of_image (isEMorphism_iff.1 hE).2 hinj (𝔊.absolutelyMinimalOn t) ⊤ A
      (by rw [hA, Opens.coe_top, image_univ]) a b h
  · exact hE.map_le ⊤ A le_rfl (fun x _ => by rw [hA]; exact mem_range_self x) h

end DevFacts

/-! ### The gluing of two developments along their MCGHD -/

section Ppcm

variable {𝔊 : Geometry.{u}} {M₀ : Type u} [TopologicalSpace M₀] {s₀ : 𝔊.Str M₀}
  [ConnectedSpace M₀]

variable (N₁ N₂ : Dev 𝔊.toPreGeometry s₀)

/-- **`ppcm` as a space** (`defi:ppcm`, `ETT.tex:1987`; Sbierski's `(M ⊔ M′)/∼`, proof of
Thm 2.7): `N₁ ⊔ N₂` with `x ∈ U` identified with `ψ(x)`, `U` the MCGHD and `ψ` its morphism. -/
abbrev PpcmSpace : Type u :=
  Gluing (Subtype.val : mcghdOpens N₁ N₂ → N₁.carrier)
    (mcghdMap N₁ N₂ ∘ (Subtype.val : mcghdOpens N₁ N₂ → N₁.carrier))

/-- The image `ψ(U)` of the MCGHD in `N₂`, as an open set. -/
noncomputable def mcghdImage : Opens N₂.carrier :=
  (𝔊.isEMorphismOn_of_isMor (isCGHD_mcghd (N₁ := N₁) (N₂ := N₂)).2.1).imageOpens _ le_rfl

theorem coe_mcghdImage :
    (mcghdImage N₁ N₂ : Set N₂.carrier) = mcghdMap N₁ N₂ '' (mcghdOpens N₁ N₂ : Set N₁.carrier) :=
  rfl

variable {N₁ N₂}

/-- The MCGHD is causally convex in `N₁` (a Cauchy inclusion into `N₁`, `CBG/CausalConvex`). -/
theorem convex_mcghdOpens :
    (𝔊.causality N₁.str).CausallyConvexIn (mcghdOpens N₁ N₂ : Set N₁.carrier) ⊤ :=
  (((isCGHD_mcghd (N₁ := N₁) (N₂ := N₂)).1).of_le N₁.isCauchyInclusion_range_top
    le_top).causallyConvexIn N₁.causality_causallyArcConnected
      (Causality.curvesExtendOn_top.2 N₁.causality_curvesExtend)

/-- Its image `ψ(U)` is causally convex in `N₂` (given `ψ` injective). -/
theorem convex_mcghdImage (hinj : InjOn (mcghdMap N₁ N₂) (mcghdOpens N₁ N₂)) :
    (𝔊.causality N₂.str).CausallyConvexIn (mcghdImage N₁ N₂ : Set N₂.carrier) ⊤ :=
  (((isCGHD_mcghd (N₁ := N₁) (N₂ := N₂)).isCauchyInclusion_image hinj).of_le
    N₂.isCauchyInclusion_range_top le_top).causallyConvexIn N₂.causality_causallyArcConnected
      (Causality.curvesExtendOn_top.2 N₂.causality_curvesExtend)

/-- **`ψ` transfers the causal relation between points of the MCGHD**, both ways: by causal
convexity of `U` in `N₁` and of `ψ(U)` in `N₂`, `ψ` a morphism on `U` and `ψ⁻¹` one on `ψ(U)`
(`isMor_inv`). -/
theorem mcghd_le_iff (hinj : InjOn (mcghdMap N₁ N₂) (mcghdOpens N₁ N₂)) {u u' : N₁.carrier}
    (hu : u ∈ mcghdOpens N₁ N₂) (hu' : u' ∈ mcghdOpens N₁ N₂) :
    (𝔊.causality N₁.str).le ⊤ u u' ↔
      (𝔊.causality N₂.str).le ⊤ (mcghdMap N₁ N₂ u) (mcghdMap N₁ N₂ u') := by
  haveI : Nonempty N₁.carrier := ⟨N₁.emb (Classical.arbitrary M₀)⟩
  have hψ := (isCGHD_mcghd (N₁ := N₁) (N₂ := N₂)).2.1
  have hE := 𝔊.isEMorphismOn_of_isMor hψ
  have hEinv := 𝔊.isEMorphismOn_of_isMor (𝔊.isMor_inv hψ hinj)
  have hψu : mcghdMap N₁ N₂ u ∈ mcghdImage N₁ N₂ := ⟨u, hu, rfl⟩
  have hψu' : mcghdMap N₁ N₂ u' ∈ mcghdImage N₁ N₂ := ⟨u', hu', rfl⟩
  constructor
  · intro h
    have h1 := Causality.le_of_causallyConvexIn N₁.causality_causallyArcConnected
      convex_mcghdOpens subset_rfl hu hu' h
    exact (𝔊.causality N₂.str).le_mono le_top
      (hE.map_le _ (mcghdImage N₁ N₂) le_rfl (fun x hx => ⟨x, hx, rfl⟩) h1)
  · intro h
    have h1 := Causality.le_of_causallyConvexIn N₂.causality_causallyArcConnected
      (convex_mcghdImage hinj) subset_rfl hψu hψu' h
    have h2 := hEinv.map_le _ (mcghdOpens N₁ N₂) le_rfl
      (surjOn_image (mcghdMap N₁ N₂) _).mapsTo_invFunOn h1
    rw [hinj.leftInvOn_invFunOn hu, hinj.leftInvOn_invFunOn hu'] at h2
    exact (𝔊.causality N₁.str).le_mono le_top h2

omit [ConnectedSpace M₀] in
theorem ppcm_hj₁ : IsOpenEmbedding (Subtype.val : mcghdOpens N₁ N₂ → N₁.carrier) :=
  (mcghdOpens N₁ N₂).isOpen.isOpenEmbedding_subtypeVal

theorem ppcm_hj₂ :
    IsOpenEmbedding (mcghdMap N₁ N₂ ∘ (Subtype.val : mcghdOpens N₁ N₂ → N₁.carrier)) := by
  haveI : Nonempty N₁.carrier := ⟨N₁.emb (Classical.arbitrary M₀)⟩
  obtain ⟨S, hS, -⟩ := N₁.isCauchyEmbedding.exists_cauchy
  exact ((isCGHD_mcghd (N₁ := N₁) (N₂ := N₂)).cghdData hS).isCorrPair.isOpenEmbedding_comp_val

theorem ppcm_injective_j₂ (hinj : InjOn (mcghdMap N₁ N₂) (mcghdOpens N₁ N₂)) :
    Injective (mcghdMap N₁ N₂ ∘ (Subtype.val : mcghdOpens N₁ N₂ → N₁.carrier)) :=
  fun a b hab => Subtype.ext (hinj a.2 b.2 hab)

/-- `ι₁ x = ι₂ ψ(x)` on the MCGHD. -/
theorem ppcm_ι₁_eq {x : N₁.carrier} (hx : x ∈ mcghdOpens N₁ N₂) :
    Gluing.ι₁ (Subtype.val : mcghdOpens N₁ N₂ → N₁.carrier)
      (mcghdMap N₁ N₂ ∘ Subtype.val) x =
    Gluing.ι₂ (Subtype.val : mcghdOpens N₁ N₂ → N₁.carrier)
      (mcghdMap N₁ N₂ ∘ Subtype.val) (mcghdMap N₁ N₂ x) :=
  Gluing.ι₁_j₁ (j₁ := (Subtype.val : mcghdOpens N₁ N₂ → N₁.carrier))
    (j₂ := mcghdMap N₁ N₂ ∘ Subtype.val) ⟨x, hx⟩

/-- `ι₁ ∘ ι_{N₁} = ι₂ ∘ ι_{N₂}`: the two copies of `M₀` are identified. -/
theorem ppcm_ι₁_emb (x : M₀) :
    Gluing.ι₁ (Subtype.val : mcghdOpens N₁ N₂ → N₁.carrier)
      (mcghdMap N₁ N₂ ∘ Subtype.val) (N₁.emb x) =
    Gluing.ι₂ (Subtype.val : mcghdOpens N₁ N₂ → N₁.carrier)
      (mcghdMap N₁ N₂ ∘ Subtype.val) (N₂.emb x) :=
  (ppcm_ι₁_eq ((isCGHD_mcghd (N₁ := N₁) (N₂ := N₂)).1.1 (N₁.emb_mem_range x))).trans
    (congrArg _ (congrFun (isCGHD_mcghd (N₁ := N₁) (N₂ := N₂)).2.2 x))

/-- **The identification is exactly along the MCGHD**: `ι₁ x = ι₂ y` iff `x ∈ U` and
`ψ(x) = y`. -/
theorem ppcm_ι₁_eq_ι₂_iff (hinj : InjOn (mcghdMap N₁ N₂) (mcghdOpens N₁ N₂)) {x : N₁.carrier}
    {y : N₂.carrier} :
    Gluing.ι₁ (Subtype.val : mcghdOpens N₁ N₂ → N₁.carrier)
      (mcghdMap N₁ N₂ ∘ Subtype.val) x =
    Gluing.ι₂ (Subtype.val : mcghdOpens N₁ N₂ → N₁.carrier)
      (mcghdMap N₁ N₂ ∘ Subtype.val) y ↔ x ∈ mcghdOpens N₁ N₂ ∧ mcghdMap N₁ N₂ x = y := by
  rw [Gluing.ι₁_eq_ι₂_iff Subtype.val_injective (ppcm_injective_j₂ hinj)]
  constructor
  · rintro ⟨w, rfl, rfl⟩; exact ⟨w.2, rfl⟩
  · rintro ⟨hx, rfl⟩; exact ⟨⟨x, hx⟩, rfl, rfl⟩

/-! #### The structure of `ppcm` (`Geometry.glue`) -/

variable (N₁ N₂) in
/-- The two pieces, indexed by `ULift Bool` (`Geometry.glue` asks an index type in `Type u`). -/
def ppcmPiece : ULift.{u} Bool → Type u
  | ⟨true⟩ => N₁.carrier
  | ⟨false⟩ => N₂.carrier

instance ppcmPieceTop (b : ULift.{u} Bool) : TopologicalSpace (ppcmPiece N₁ N₂ b) :=
  match b with
  | ⟨true⟩ => N₁.top
  | ⟨false⟩ => N₂.top

variable (N₁ N₂) in
def ppcmPieceStr : ∀ b : ULift.{u} Bool, 𝔊.Str (ppcmPiece N₁ N₂ b)
  | ⟨true⟩ => N₁.str
  | ⟨false⟩ => N₂.str

variable (N₁ N₂) in
noncomputable def ppcmPieceEmb : ∀ b : ULift.{u} Bool, ppcmPiece N₁ N₂ b → PpcmSpace N₁ N₂
  | ⟨true⟩ => Gluing.ι₁ _ _
  | ⟨false⟩ => Gluing.ι₂ _ _

/-- **`ppcm` carries a structure for which both inclusions are morphisms** (`Geometry.glue`; the
transitions are `id`, `ψ` on `U` and `ψ⁻¹` on `ψ(U)`: Sbierski's atlas, proof of Thm 2.7,
step 1; ETT's « the charts of `M₁` and `M₂` descend », `ETT.tex:2000`). -/
theorem exists_ppcmStr (hinj : InjOn (mcghdMap N₁ N₂) (mcghdOpens N₁ N₂)) :
    ∃ t : 𝔊.Str (PpcmSpace N₁ N₂), 𝔊.IsMor N₁.str t ⊤ (Gluing.ι₁ _ _) ∧
      𝔊.IsMor N₂.str t ⊤ (Gluing.ι₂ _ _) := by
  haveI : Nonempty N₁.carrier := ⟨N₁.emb (Classical.arbitrary M₀)⟩
  have hj₁ := ppcm_hj₁ (N₁ := N₁) (N₂ := N₂)
  have hj₂ := ppcm_hj₂ (N₁ := N₁) (N₂ := N₂)
  have hψ := (isCGHD_mcghd (N₁ := N₁) (N₂ := N₂)).2.1
  obtain ⟨t, ht⟩ := 𝔊.glue (ppcmPiece N₁ N₂) (ppcmPieceStr N₁ N₂) (ppcmPieceEmb N₁ N₂)
    (by
      rintro ⟨_ | _⟩
      · exact Gluing.isOpenEmbedding_ι₂ hj₁ hj₂
      · exact Gluing.isOpenEmbedding_ι₁ hj₁ hj₂)
    (by
      intro z
      rcases Gluing.exists_ι z with ⟨x, rfl⟩ | ⟨y, rfl⟩
      · exact ⟨⟨true⟩, x, rfl⟩
      · exact ⟨⟨false⟩, y, rfl⟩)
    (by
      rintro ⟨_ | _⟩ ⟨_ | _⟩
      · exact ⟨id, 𝔊.isMor_id _ _, fun _ _ => rfl⟩
      · refine ⟨(invFunOn (mcghdMap N₁ N₂) (mcghdOpens N₁ N₂ : Set N₁.carrier) :
          N₂.carrier → N₁.carrier), 𝔊.isMor_mono (𝔊.isMor_inv hψ hinj) ?_, ?_⟩
        · rintro y ⟨x, hx⟩
          obtain ⟨hxU, rfl⟩ := (ppcm_ι₁_eq_ι₂_iff hinj).1 hx
          exact ⟨x, hxU, rfl⟩
        · rintro y ⟨x, hx⟩
          obtain ⟨hxU, rfl⟩ := (ppcm_ι₁_eq_ι₂_iff hinj).1 hx
          show Gluing.ι₁ _ _ (invFunOn (mcghdMap N₁ N₂) (mcghdOpens N₁ N₂) (mcghdMap N₁ N₂ x)) =
            Gluing.ι₂ _ _ (mcghdMap N₁ N₂ x)
          rw [hinj.leftInvOn_invFunOn hxU]
          exact ppcm_ι₁_eq hxU
      · refine ⟨(mcghdMap N₁ N₂ : N₁.carrier → N₂.carrier), 𝔊.isMor_mono hψ ?_, ?_⟩
        · rintro x ⟨y, hy⟩
          exact ((ppcm_ι₁_eq_ι₂_iff hinj).1 hy.symm).1
        · rintro x ⟨y, hy⟩
          obtain ⟨hxU, rfl⟩ := (ppcm_ι₁_eq_ι₂_iff hinj).1 hy.symm
          exact hy
      · exact ⟨id, 𝔊.isMor_id _ _, fun _ _ => rfl⟩)
  exact ⟨t, ht ⟨true⟩, ht ⟨false⟩⟩

/-- The structure of `ppcm` (a choice: any structure with both inclusions morphisms;
`ppcmDev_desc` and `ppcmDev_unique` show the result does not depend on it up to unique
isomorphism). -/
noncomputable def ppcmStr (hinj : InjOn (mcghdMap N₁ N₂) (mcghdOpens N₁ N₂)) :
    𝔊.Str (PpcmSpace N₁ N₂) :=
  Classical.choose (exists_ppcmStr hinj)

theorem isMor_ppcm_ι₁ (hinj : InjOn (mcghdMap N₁ N₂) (mcghdOpens N₁ N₂)) :
    𝔊.IsMor N₁.str (ppcmStr hinj) ⊤ (Gluing.ι₁ _ _) :=
  (Classical.choose_spec (exists_ppcmStr hinj)).1

theorem isMor_ppcm_ι₂ (hinj : InjOn (mcghdMap N₁ N₂) (mcghdOpens N₁ N₂)) :
    𝔊.IsMor N₂.str (ppcmStr hinj) ⊤ (Gluing.ι₂ _ _) :=
  (Classical.choose_spec (exists_ppcmStr hinj)).2

/-! #### The causality of `ppcm`: two pieces, two charts -/

/-- `ι₁ : N₁ → ppcm` is a chart of the piece `ι₁(N₁)`. -/
theorem ppcm_chart₁ (hinj : InjOn (mcghdMap N₁ N₂) (mcghdOpens N₁ N₂)) :
    Causality.PieceChart (𝔊.causality (ppcmStr hinj)) (Gluing.O₁ ppcm_hj₁ (ppcm_hj₂))
      (𝔊.causality N₁.str) (Gluing.ι₁ _ _) :=
  pieceChart_of_isMor (isMor_ppcm_ι₁ hinj)
    (Gluing.injective_ι₁ Subtype.val_injective (ppcm_injective_j₂ hinj)) _ rfl

/-- `ι₂ : N₂ → ppcm` is a chart of the piece `ι₂(N₂)`. -/
theorem ppcm_chart₂ (hinj : InjOn (mcghdMap N₁ N₂) (mcghdOpens N₁ N₂)) :
    Causality.PieceChart (𝔊.causality (ppcmStr hinj)) (Gluing.O₂ ppcm_hj₁ (ppcm_hj₂))
      (𝔊.causality N₂.str) (Gluing.ι₂ _ _) :=
  pieceChart_of_isMor (isMor_ppcm_ι₂ hinj)
    (Gluing.injective_ι₂ Subtype.val_injective (ppcm_injective_j₂ hinj)) _ rfl

/-- **`ppcm` is a two-piece spacetime** (`Causality.TwoPiece`): its causality is absolutely
minimal (A, `absolutelyMinimalOn`), the overlap `ι₁(U) = ι₂(ψ(U))` is causally convex in each
piece (`convex_mcghdOpens`, `convex_mcghdImage`), and the two relations agree there
(`mcghd_le_iff`). -/
theorem ppcm_twoPiece (hinj : InjOn (mcghdMap N₁ N₂) (mcghdOpens N₁ N₂)) :
    (𝔊.causality (ppcmStr hinj)).TwoPiece (Gluing.O₁ ppcm_hj₁ (ppcm_hj₂))
      (Gluing.O₂ ppcm_hj₁ (ppcm_hj₂)) := by
  have c₁ := ppcm_chart₁ hinj
  have c₂ := ppcm_chart₂ hinj
  have mem₂ : ∀ {x : N₁.carrier}, Gluing.ι₁ _ _ x ∈ Gluing.O₂ ppcm_hj₁ (ppcm_hj₂) ↔
      x ∈ mcghdOpens N₁ N₂ := fun {x} =>
    ⟨fun ⟨y, hy⟩ => ((ppcm_ι₁_eq_ι₂_iff hinj).1 hy.symm).1, fun hx => ⟨_, (ppcm_ι₁_eq hx).symm⟩⟩
  have mem₁ : ∀ {y : N₂.carrier}, Gluing.ι₂ _ _ y ∈ Gluing.O₁ ppcm_hj₁ (ppcm_hj₂) ↔
      y ∈ mcghdImage N₁ N₂ := fun {y} =>
    ⟨fun ⟨x, hx⟩ => by
      obtain ⟨hxU, rfl⟩ := (ppcm_ι₁_eq_ι₂_iff hinj).1 hx
      exact ⟨x, hxU, rfl⟩,
     fun ⟨x, hx, hxy⟩ => ⟨x, by rw [← hxy]; exact ppcm_ι₁_eq hx⟩⟩
  refine ⟨fun z => ?_, 𝔊.absolutelyMinimalOn _ ⊤, ?_, ?_, ?_⟩
  · rcases Gluing.exists_ι z with ⟨x, rfl⟩ | ⟨y, rfl⟩
    · exact Or.inl (c₁.mem x)
    · exact Or.inr (c₂.mem y)
  · intro x y z hx hz hxy hyz
    obtain ⟨a, rfl⟩ := c₁.exists_eq ((𝔊.causality (ppcmStr hinj)).le_mem_left hxy)
    obtain ⟨b, rfl⟩ := c₁.exists_eq ((𝔊.causality (ppcmStr hinj)).le_mem_right hxy)
    obtain ⟨c, rfl⟩ := c₁.exists_eq ((𝔊.causality (ppcmStr hinj)).le_mem_right hyz)
    exact mem₂.2 (convex_mcghdOpens.2 a (mem₂.1 hx) c (mem₂.1 hz)
      (Causality.mem_diamond.2 ⟨(c₁.le_iff a b).1 hxy, (c₁.le_iff b c).1 hyz⟩))
  · intro x y z hx hz hxy hyz
    obtain ⟨a, rfl⟩ := c₂.exists_eq ((𝔊.causality (ppcmStr hinj)).le_mem_left hxy)
    obtain ⟨b, rfl⟩ := c₂.exists_eq ((𝔊.causality (ppcmStr hinj)).le_mem_right hxy)
    obtain ⟨c, rfl⟩ := c₂.exists_eq ((𝔊.causality (ppcmStr hinj)).le_mem_right hyz)
    exact mem₁.2 ((convex_mcghdImage hinj).2 a (mem₁.1 hx) c (mem₁.1 hz)
      (Causality.mem_diamond.2 ⟨(c₂.le_iff a b).1 hxy, (c₂.le_iff b c).1 hyz⟩))
  · intro x y hx₁ hx₂ hy₁ hy₂
    obtain ⟨u, rfl⟩ := c₁.exists_eq hx₁
    obtain ⟨u', rfl⟩ := c₁.exists_eq hy₁
    have hu := mem₂.1 hx₂
    have hu' := mem₂.1 hy₂
    rw [c₁.le_iff, mcghd_le_iff hinj hu hu', ← c₂.le_iff, ← ppcm_ι₁_eq hu, ← ppcm_ι₁_eq hu']

/-- The common Cauchy surface: `ι₁(ι_{N₁}(S)) = ι₂(ι_{N₂}(S))`. -/
theorem ppcm_image_cauchy (S : Set M₀) :
    Gluing.ι₁ (Subtype.val : mcghdOpens N₁ N₂ → N₁.carrier) (mcghdMap N₁ N₂ ∘ Subtype.val) ''
        (N₁.emb '' S) =
      Gluing.ι₂ (Subtype.val : mcghdOpens N₁ N₂ → N₁.carrier) (mcghdMap N₁ N₂ ∘ Subtype.val) ''
        (N₂.emb '' S) := by
  ext z
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨_, ⟨x, hx, rfl⟩, (ppcm_ι₁_emb x).symm⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨_, ⟨x, hx, rfl⟩, ppcm_ι₁_emb x⟩

/-- **`ppcm` is globally hyperbolic** — directly, without `curvesExtend` or `isCompact_*` on `ppcm`
itself (design §6, the package-10 risk): `TwoPiece.globallyHyperbolic` with the charts `ι₁`, `ι₂`
and the Cauchy sides of `ι_{N₁}(Σ)`, `ι_{N₂}(Σ)`, whose images agree. -/
theorem ppcm_globallyHyperbolic (hinj : InjOn (mcghdMap N₁ N₂) (mcghdOpens N₁ N₂)) :
    (𝔊.causality (ppcmStr hinj)).GloballyHyperbolic := by
  obtain ⟨S, hS, hS₁⟩ := N₁.isCauchyEmbedding.exists_cauchy
  exact (ppcm_twoPiece hinj).globallyHyperbolic (ppcm_chart₁ hinj) (ppcm_chart₂ hinj)
    N₁.causality_globallyHyperbolic N₂.causality_globallyHyperbolic (N₁.cauchySide hS₁)
    (N₂.cauchySide (N₂.isCauchyEmbedding.isCauchySurface_image hS)) (ppcm_image_cauchy S)

/-- **The image of a Cauchy surface of `M₀` is a Cauchy surface of `ppcm`** (Sbierski, proof of
Thm 2.7, step 4; `TwoPiece.isCauchySurface`). -/
theorem ppcm_isCauchySurface (hinj : InjOn (mcghdMap N₁ N₂) (mcghdOpens N₁ N₂)) {S : Set M₀}
    (hS : (𝔊.causality s₀).IsCauchySurface S) :
    (𝔊.causality (ppcmStr hinj)).IsCauchySurface
      (Gluing.ι₁ (Subtype.val : mcghdOpens N₁ N₂ → N₁.carrier) (mcghdMap N₁ N₂ ∘ Subtype.val) ''
        (N₁.emb '' S)) := by
  haveI := t2Space_gluing_mcghd (N₁ := N₁) (N₂ := N₂)
  have hS₁ := N₁.isCauchyEmbedding.isCauchySurface_image hS
  have hS₂ := N₂.isCauchyEmbedding.isCauchySurface_image hS
  have c₁ := ppcm_chart₁ hinj
  have hE₁ := 𝔊.isEMorphismOn_of_isMor (isMor_ppcm_ι₁ hinj)
  have hE₂ := 𝔊.isEMorphismOn_of_isMor (isMor_ppcm_ι₂ hinj)
  have hSA := (hE₁.isCauchySurfaceOn_image_iff
    (Gluing.injective_ι₁ Subtype.val_injective (ppcm_injective_j₂ hinj)).injOn le_rfl
    (U := Gluing.O₁ ppcm_hj₁ (ppcm_hj₂)) (by rw [Opens.coe_top, image_univ]; rfl)
    (subset_univ _)).1 hS₁
  have hSB := (hE₂.isCauchySurfaceOn_image_iff
    (Gluing.injective_ι₂ Subtype.val_injective (ppcm_injective_j₂ hinj)).injOn le_rfl
    (U := Gluing.O₂ ppcm_hj₁ (ppcm_hj₂)) (by rw [Opens.coe_top, image_univ]; rfl)
    (subset_univ _)).1 hS₂
  rw [← ppcm_image_cauchy] at hSB
  have hac := hS₁.isAcausal N₁.causality_causallyArcConnected N₁.causality_curvesExtend
  refine (ppcm_twoPiece hinj).isCauchySurface (ppcm_globallyHyperbolic hinj).1
    (fun _ ⟨x, _, hx⟩ => hx ▸ c₁.mem x) hSA hSB ?_
  rintro _ ⟨σ, hσ, rfl⟩ _ ⟨σ', hσ', rfl⟩ h
  exact congrArg _ (hac σ hσ σ' hσ' ((c₁.le_iff σ σ').1 h))

/-- `ppcm` is connected: the union of the connected `ι₁(N₁)`, `ι₂(N₂)`, which meet along the image
of `M₀`. -/
theorem ppcm_connectedSpace : ConnectedSpace (PpcmSpace N₁ N₂) := by
  rw [connectedSpace_iff_univ, ← Gluing.range_ι₁_union_range_ι₂]
  obtain ⟨x₀⟩ := (inferInstance : Nonempty M₀)
  exact IsConnected.union ⟨Gluing.ι₁ _ _ (N₁.emb x₀), mem_range_self _, N₂.emb x₀,
    (ppcm_ι₁_emb x₀).symm⟩ (isConnected_range Gluing.continuous_ι₁)
    (isConnected_range Gluing.continuous_ι₂)

/-- `ppcm` is second countable (an open quotient of the second-countable `N₁ ⊔ N₂`; Sbierski,
proof of Thm 2.7, step 2; ETT `ETT.tex:2000–2001`). -/
theorem ppcm_secondCountable :
    SecondCountableTopology (PpcmSpace N₁ N₂) :=
  isQuotientMap_quot_mk.secondCountableTopology (Gluing.isOpenMap_mk ppcm_hj₁ ppcm_hj₂)

/-- `M₀ → ppcm`, `x ↦ ι₁(ι_{N₁}(x))`, is a Cauchy embedding. -/
theorem ppcm_isCauchyEmbedding (hinj : InjOn (mcghdMap N₁ N₂) (mcghdOpens N₁ N₂)) :
    IsCauchyEmbedding (𝔊.causality s₀) (𝔊.causality (ppcmStr hinj))
      (Gluing.ι₁ (Subtype.val : mcghdOpens N₁ N₂ → N₁.carrier) (mcghdMap N₁ N₂ ∘ Subtype.val) ∘
        N₁.emb) := by
  obtain ⟨S, hS, -⟩ := N₁.isCauchyEmbedding.exists_cauchy
  exact ⟨N₁.isCauchyEmbedding.globallyHyperbolic_source, ppcm_globallyHyperbolic hinj,
    𝔊.isEMorphismOn_of_isMor (𝔊.isMor_comp (isMor_ppcm_ι₁ hinj) N₁.isMor fun _ _ => trivial),
    (Gluing.injective_ι₁ Subtype.val_injective (ppcm_injective_j₂ hinj)).comp
      N₁.isCauchyEmbedding.injective,
    S, hS, by rw [image_comp]; exact ppcm_isCauchySurface hinj hS⟩

variable (N₁ N₂) in
/-- **The least common extension `ppcm` of two developments, as a development of `M₀`**
(`defi:ppcm`, `prop:ppcm_Cauchy`; Sbierski Thm 2.7): the gluing along the MCGHD, Hausdorff by
Sbierski Thm 3.13 (`t2Space_gluing_mcghd`), with the glued structure, `M₀` Cauchy-embedded through
`N₁`. -/
noncomputable def ppcmDev (hinj : InjOn (mcghdMap N₁ N₂) (mcghdOpens N₁ N₂)) :
    Dev 𝔊.toPreGeometry s₀ where
  carrier := PpcmSpace N₁ N₂
  t2 := t2Space_gluing_mcghd
  conn := ppcm_connectedSpace
  sc := ppcm_secondCountable
  str := ppcmStr hinj
  emb := Gluing.ι₁ _ _ ∘ N₁.emb
  isCauchyEmbedding := ppcm_isCauchyEmbedding hinj
  isMor := 𝔊.isMor_comp (isMor_ppcm_ι₁ hinj) N₁.isMor fun _ _ => trivial

/-- `ι₁ : N₁ → ppcm` is a morphism of developments. -/
theorem ppcmDev_isMorphism₁ (hinj : InjOn (mcghdMap N₁ N₂) (mcghdOpens N₁ N₂)) :
    N₁.IsMorphism (ppcmDev N₁ N₂ hinj) (Gluing.ι₁ _ _) :=
  ⟨isMor_ppcm_ι₁ hinj, rfl⟩

/-- `ι₂ : N₂ → ppcm` is a morphism of developments. -/
theorem ppcmDev_isMorphism₂ (hinj : InjOn (mcghdMap N₁ N₂) (mcghdOpens N₁ N₂)) :
    N₂.IsMorphism (ppcmDev N₁ N₂ hinj) (Gluing.ι₂ _ _) :=
  ⟨isMor_ppcm_ι₂ hinj, funext fun x => (ppcm_ι₁_emb x).symm⟩

/-- **Minimality of `ppcm`** (`prop:ppcm_Cauchy`, `ETT.tex:2326–2330`; thesis `these.tex:6876–6879`):
two morphisms of developments `g₁ : N₁ → Q`, `g₂ : N₂ → Q` agree along the MCGHD (`g₁` and `g₂ ∘ ψ`
are morphisms on the connected `U` agreeing on `ι_{N₁}(M₀)`: rigidity A1, `Q` Hausdorff), so
`g₁ ⊔ g₂` descends (`Gluing.desc`), to a morphism of developments, the unique one with
`h ∘ ι₁ = g₁`, `h ∘ ι₂ = g₂`. -/
theorem ppcmDev_desc (hinj : InjOn (mcghdMap N₁ N₂) (mcghdOpens N₁ N₂))
    (Q : Dev 𝔊.toPreGeometry s₀) {g₁ : N₁.carrier → Q.carrier} {g₂ : N₂.carrier → Q.carrier}
    (hg₁ : N₁.IsMorphism Q g₁) (hg₂ : N₂.IsMorphism Q g₂) :
    ∃! h : (ppcmDev N₁ N₂ hinj).carrier → Q.carrier, (ppcmDev N₁ N₂ hinj).IsMorphism Q h ∧
      h ∘ Gluing.ι₁ _ _ = g₁ ∧ h ∘ Gluing.ι₂ _ _ = g₂ := by
  haveI : Nonempty N₁.carrier := ⟨N₁.emb (Classical.arbitrary M₀)⟩
  haveI : Nonempty N₂.carrier := ⟨N₂.emb (Classical.arbitrary M₀)⟩
  have hU := isCGHD_mcghd (N₁ := N₁) (N₂ := N₂)
  have hEq : EqOn g₁ (g₂ ∘ mcghdMap N₁ N₂) (mcghdOpens N₁ N₂) := by
    obtain ⟨x₀⟩ := (inferInstance : Nonempty M₀)
    refine 𝔊.rigid N₁.str Q.str (mcghdOpens N₁ N₂) (isConnected_iff_connectedSpace.2 (mcghd_connectedSpace (N₁ := N₁) (N₂ := N₂)))
      g₁ (g₂ ∘ mcghdMap N₁ N₂) (𝔊.isMor_mono hg₁.1 le_top)
      (𝔊.isMor_comp hg₂.1 hU.2.1 fun _ _ => trivial) N₁.isCauchyEmbedding.rangeOpens hU.1.1
      ⟨N₁.emb x₀, N₁.emb_mem_range x₀⟩ ?_
    intro y hy
    rw [IsCauchyEmbedding.coe_rangeOpens] at hy
    obtain ⟨x, rfl⟩ := hy
    exact (congrFun hg₁.2 x).trans ((congrFun hg₂.2 x).symm.trans
      (congrArg g₂ (congrFun hU.2.2 x).symm))
  have hagree : ∀ w : mcghdOpens N₁ N₂, g₁ w.1 = g₂ ((mcghdMap N₁ N₂ ∘ Subtype.val) w) :=
    fun w => hEq w.2
  let h : (ppcmDev N₁ N₂ hinj).carrier → Q.carrier := Gluing.desc g₁ g₂ hagree
  refine ⟨h, ⟨⟨?_, funext fun x => congrFun hg₁.2 x⟩, rfl, rfl⟩, ?_⟩
  · refine 𝔊.isMor_of_locally fun z _ => ?_
    rcases Gluing.exists_ι z with ⟨x, rfl⟩ | ⟨y, rfl⟩
    · have hinj₁ := Gluing.injective_ι₁ (j₁ := (Subtype.val : mcghdOpens N₁ N₂ → N₁.carrier))
        Subtype.val_injective (ppcm_injective_j₂ hinj)
      have hinv := 𝔊.isMor_inv (isMor_ppcm_ι₁ hinj) hinj₁.injOn
      refine ⟨(𝔊.isEMorphismOn_of_isMor (isMor_ppcm_ι₁ hinj)).imageOpens ⊤ le_rfl, le_top,
        ⟨x, trivial, rfl⟩, 𝔊.isMor_congr (𝔊.isMor_comp hg₁.1 hinv fun _ _ => trivial) ?_⟩
      rintro _ ⟨x', -, rfl⟩
      show g₁ (invFunOn _ _ (Gluing.ι₁ _ _ x')) = g₁ x'
      rw [hinj₁.injOn.leftInvOn_invFunOn (show x' ∈ ((⊤ : Opens N₁.carrier) : Set N₁.carrier)
        from trivial)]
    · have hinj₂ := Gluing.injective_ι₂ (j₁ := (Subtype.val : mcghdOpens N₁ N₂ → N₁.carrier))
        Subtype.val_injective (ppcm_injective_j₂ hinj)
      have hinv := 𝔊.isMor_inv (isMor_ppcm_ι₂ hinj) hinj₂.injOn
      refine ⟨(𝔊.isEMorphismOn_of_isMor (isMor_ppcm_ι₂ hinj)).imageOpens ⊤ le_rfl, le_top,
        ⟨y, trivial, rfl⟩, 𝔊.isMor_congr (𝔊.isMor_comp hg₂.1 hinv fun _ _ => trivial) ?_⟩
      rintro _ ⟨y', -, rfl⟩
      show g₂ (invFunOn _ _ (Gluing.ι₂ _ _ y')) = g₂ y'
      rw [hinj₂.injOn.leftInvOn_invFunOn (show y' ∈ ((⊤ : Opens N₂.carrier) : Set N₂.carrier)
        from trivial)]
  · rintro h' ⟨-, h₁, h₂⟩
    exact Gluing.eq_desc (fun x => congrFun h₁ x) (fun y => congrFun h₂ y)

/-- **The induced morphism is injective**, hence a Cauchy embedding (ETT's « yields a Cauchy
embedding `ppcm → M` », `ETT.tex:2329`), by the time function of the development `ppcm`
(`Dev.causality_hasTimeFunction`, from `Geometry.timeFunction`) and Lemma 3.3 (`CBG/Injective`:
injective on the Cauchy surface `ι₁(ι_{N₁}(Σ))`, onto the acausal `ι_Q(Σ)`). -/
theorem ppcmDev_desc_injective (hinj : InjOn (mcghdMap N₁ N₂) (mcghdOpens N₁ N₂))
    (Q : Dev 𝔊.toPreGeometry s₀)
    {h : (ppcmDev N₁ N₂ hinj).carrier → Q.carrier} (hh : (ppcmDev N₁ N₂ hinj).IsMorphism Q h) :
    Injective h := by
  haveI := t2Space_gluing_mcghd (N₁ := N₁) (N₂ := N₂)
  obtain ⟨T, hTc, hTs⟩ := (ppcmDev N₁ N₂ hinj).causality_hasTimeFunction
  obtain ⟨S, hS, -⟩ := N₁.isCauchyEmbedding.exists_cauchy
  have hSP := ppcm_isCauchySurface hinj hS
  have himg : h '' (Gluing.ι₁ (Subtype.val : mcghdOpens N₁ N₂ → N₁.carrier)
      (mcghdMap N₁ N₂ ∘ Subtype.val) '' (N₁.emb '' S)) = Q.emb '' S := by
    rw [← image_comp, ← image_comp]
    exact image_congr fun x _ => congrFun hh.2 x
  have hinjS : InjOn h (Gluing.ι₁ (Subtype.val : mcghdOpens N₁ N₂ → N₁.carrier)
      (mcghdMap N₁ N₂ ∘ Subtype.val) '' (N₁.emb '' S)) := by
    rintro _ ⟨_, ⟨a, -, rfl⟩, rfl⟩ _ ⟨_, ⟨b, -, rfl⟩, rfl⟩ hab
    have : Q.emb a = Q.emb b := (congrFun hh.2 a).symm.trans (hab.trans (congrFun hh.2 b))
    rw [Q.isCauchyEmbedding.injective this]
  have hac : (𝔊.causality Q.str).IsAcausal (h '' (Gluing.ι₁ (Subtype.val : mcghdOpens N₁ N₂ →
      N₁.carrier) (mcghdMap N₁ N₂ ∘ Subtype.val) '' (N₁.emb '' S))) := by
    rw [himg]
    exact (Q.isCauchyEmbedding.isCauchySurface_image hS).isAcausal
      Q.causality_causallyArcConnected Q.causality_curvesExtend
  have hI : InjOn h ((⊤ : Opens (ppcmDev N₁ N₂ hinj).carrier) : Set _) :=
    injOn_of_injOn_cauchy (𝔊.isEMorphismOn_of_isMor hh.1) hTc hTs hSP hinjS hac
      Q.causality_globallyHyperbolic.1
  exact fun x y hxy => hI trivial trivial hxy

end Ppcm

/-! ### Uniqueness up to equivalence, and the principal theorem -/

section Principal

variable {𝔊 : Geometry.{u}} {M₀ : Type u} [TopologicalSpace M₀] {s₀ : 𝔊.Str M₀}

/-- **A morphism of a development into itself is the identity** (rigidity A1 on the connected
Hausdorff carrier, agreeing with `id` on the image of `M₀`; the argument of
`Dev.IsUniversal.isETTMaximal`). -/
theorem Dev.IsMorphism.eq_id [Nonempty M₀] {R : Dev 𝔊.toPreGeometry s₀}
    {f : R.carrier → R.carrier} (hf : R.IsMorphism R f) : f = _root_.id := by
  have hV : IsConnected ((⊤ : Opens R.carrier) : Set R.carrier) := by
    rw [Opens.coe_top]; exact isConnected_univ
  have hO : (R.isCauchyEmbedding.rangeOpens : Set R.carrier).Nonempty :=
    ⟨R.emb (Classical.arbitrary M₀), R.emb_mem_range _⟩
  have heq : EqOn f _root_.id R.isCauchyEmbedding.rangeOpens := by
    intro y hy
    rw [IsCauchyEmbedding.coe_rangeOpens] at hy
    obtain ⟨x, rfl⟩ := hy
    exact congrFun hf.2 x
  funext z
  exact 𝔊.rigid R.str R.str ⊤ hV f _root_.id hf.1 (𝔊.isMor_id _ _) _ le_top hO heq
    (show z ∈ (⊤ : Opens R.carrier) from trivial)

variable [ConnectedSpace M₀] {N₁ N₂ : Dev 𝔊.toPreGeometry s₀}

/-- **`ppcm` is, up to equivalence, the unique minimal common over-extension**
(`prop:ppcm_Cauchy`, `ETT.tex:1994–1997`, uniqueness half): a development `R` with morphisms
`r₁`, `r₂` from `N₁`, `N₂`, admitting a morphism (commuting with the `rᵢ`) into every development
receiving **injective** morphisms from `N₁` and `N₂`, is isomorphic to `ppcm` by mutually inverse
morphisms of developments commuting with the inclusions. `l ∘ k = id` by the uniqueness of
`ppcmDev_desc`; `k ∘ l = id` by rigidity (`Dev.IsMorphism.eq_id`). -/
theorem ppcmDev_unique (hinj : InjOn (mcghdMap N₁ N₂) (mcghdOpens N₁ N₂))
    (R : Dev 𝔊.toPreGeometry s₀) {r₁ : N₁.carrier → R.carrier} {r₂ : N₂.carrier → R.carrier}
    (hr₁ : N₁.IsMorphism R r₁) (hr₂ : N₂.IsMorphism R r₂)
    (hmin : ∀ (Q : Dev 𝔊.toPreGeometry s₀) (g₁ : N₁.carrier → Q.carrier)
      (g₂ : N₂.carrier → Q.carrier), N₁.IsMorphism Q g₁ → N₂.IsMorphism Q g₂ → Injective g₁ →
        Injective g₂ → ∃ h : R.carrier → Q.carrier, R.IsMorphism Q h ∧ h ∘ r₁ = g₁ ∧ h ∘ r₂ = g₂) :
    ∃ (k : (ppcmDev N₁ N₂ hinj).carrier → R.carrier) (l : R.carrier → (ppcmDev N₁ N₂ hinj).carrier),
      (ppcmDev N₁ N₂ hinj).IsMorphism R k ∧ R.IsMorphism (ppcmDev N₁ N₂ hinj) l ∧ l ∘ k = id ∧
        k ∘ l = id ∧ k ∘ Gluing.ι₁ _ _ = r₁ ∧ k ∘ Gluing.ι₂ _ _ = r₂ := by
  obtain ⟨k, ⟨hk, hk₁, hk₂⟩, -⟩ := ppcmDev_desc hinj R hr₁ hr₂
  obtain ⟨l, hl, hl₁, hl₂⟩ := hmin (ppcmDev N₁ N₂ hinj) _ _ (ppcmDev_isMorphism₁ hinj)
    (ppcmDev_isMorphism₂ hinj) (Gluing.injective_ι₁ Subtype.val_injective (ppcm_injective_j₂ hinj))
    (Gluing.injective_ι₂ Subtype.val_injective (ppcm_injective_j₂ hinj))
  obtain ⟨c, -, hc⟩ := ppcmDev_desc hinj (ppcmDev N₁ N₂ hinj) (ppcmDev_isMorphism₁ hinj)
    (ppcmDev_isMorphism₂ hinj)
  have hlk : l ∘ k = id := by
    rw [hc (l ∘ k) ⟨hl.comp hk, by rw [comp_assoc, hk₁, hl₁], by rw [comp_assoc, hk₂, hl₂]⟩,
      hc id ⟨Dev.IsMorphism.id _, rfl, rfl⟩]
  exact ⟨k, l, hk, hl, hlk, (hk.comp hl).eq_id, hk₁, hk₂⟩

/-- **Sbierski Theorem 2.7 / `prop:ppcm_Cauchy` in the geometry — the principal theorem of this
file.** Two developments `N₁`, `N₂` of a connected `M₀` embed in a common development `P`
(Hausdorff, connected, second countable, globally hyperbolic, `M₀` Cauchy-embedded) by injective
morphisms of developments `f₁`, `f₂` which cover `P`, identify exactly along the MCGHD
(`f₁ x = f₂ y ↔ x ∈ U ∧ ψ x = y`), and are universal: any pair of morphisms of developments
`g₁ : N₁ → Q`, `g₂ : N₂ → Q` factors uniquely through them. `P = ppcmDev N₁ N₂ mcghdMap_injOn`
(the MCGHD morphism is injective by Lemma 3.3 from the interface's `Geometry.timeFunction`);
uniqueness up to equivalence: `ppcmDev_unique`. -/
theorem exists_ppcm (N₁ N₂ : Dev 𝔊.toPreGeometry s₀) :
    ∃ (P : Dev 𝔊.toPreGeometry s₀) (f₁ : N₁.carrier → P.carrier) (f₂ : N₂.carrier → P.carrier),
      N₁.IsMorphism P f₁ ∧ N₂.IsMorphism P f₂ ∧ Injective f₁ ∧ Injective f₂ ∧
      range f₁ ∪ range f₂ = univ ∧
      (∀ x y, f₁ x = f₂ y ↔ x ∈ mcghdOpens N₁ N₂ ∧ mcghdMap N₁ N₂ x = y) ∧
      ∀ (Q : Dev 𝔊.toPreGeometry s₀) (g₁ : N₁.carrier → Q.carrier) (g₂ : N₂.carrier → Q.carrier),
        N₁.IsMorphism Q g₁ → N₂.IsMorphism Q g₂ →
          ∃! h : P.carrier → Q.carrier, P.IsMorphism Q h ∧ h ∘ f₁ = g₁ ∧ h ∘ f₂ = g₂ :=
  have hinj : InjOn (mcghdMap N₁ N₂) (mcghdOpens N₁ N₂) := mcghdMap_injOn
  ⟨ppcmDev N₁ N₂ hinj, Gluing.ι₁ _ _, Gluing.ι₂ _ _, ppcmDev_isMorphism₁ hinj,
    ppcmDev_isMorphism₂ hinj, Gluing.injective_ι₁ Subtype.val_injective (ppcm_injective_j₂ hinj),
    Gluing.injective_ι₂ Subtype.val_injective (ppcm_injective_j₂ hinj),
    Gluing.range_ι₁_union_range_ι₂, fun _ _ => ppcm_ι₁_eq_ι₂_iff hinj,
    fun Q _ _ hg₁ hg₂ => ppcmDev_desc hinj Q hg₁ hg₂⟩

/-- **Two developments have a common extension** (Sbierski Thm 2.7 as printed: « there exists a
GHD `M̃` that is an extension of `M` and `M′` »), the form package 10 consumes. -/
theorem exists_common_extension (N₁ N₂ : Dev 𝔊.toPreGeometry s₀) :
    ∃ (P : Dev 𝔊.toPreGeometry s₀) (f₁ : N₁.carrier → P.carrier) (f₂ : N₂.carrier → P.carrier),
      N₁.IsMorphism P f₁ ∧ N₂.IsMorphism P f₂ ∧ Injective f₁ ∧ Injective f₂ := by
  obtain ⟨P, f₁, f₂, h₁, h₂, i₁, i₂, -⟩ := exists_ppcm N₁ N₂
  exact ⟨P, f₁, f₂, h₁, h₂, i₁, i₂⟩

end Principal

end CBG

/-! ### Witnesses (kb/0011): the model-free hypotheses on the timelike line -/

namespace Causality

section Witness

/-- **`TwoPiece` is satisfiable with a proper overlap**: the timelike line covered by `]-∞, 1[` and
`]0, +∞[`, overlap `]0, 1[` (a local causality, absolutely minimal, kb/0014/0019). The mixed case
of `isCompact_diamond_mixed` occurs (`-1 ≤ 2`, `-1 ∉ ]0,+∞[`, `2 ∉ ]-∞,1[`). -/
theorem timelikeLine_twoPiece :
    timelikeLine.TwoPiece ⟨Iio (1 : ℝ), isOpen_Iio⟩ ⟨Ioi (0 : ℝ), isOpen_Ioi⟩ ∧
      timelikeLine.le ⊤ (-1) 2 ∧ (-1 : ℝ) ∉ Ioi (0 : ℝ) ∧ (2 : ℝ) ∉ Iio (1 : ℝ) := by
  refine ⟨⟨fun z => ?_, timelikeLine_absolutelyMinimalOn ⊤, ?_, ?_, ?_⟩, ?_, by norm_num,
    by norm_num⟩
  · rcases lt_or_ge z 1 with h | h
    · exact Or.inl h
    · exact Or.inr (show (0 : ℝ) < z by linarith)
  · rintro x y z (hx : (0 : ℝ) < x) - ⟨hxy, -⟩ -
    exact show (0 : ℝ) < y by linarith
  · rintro x y z - (hz : z < (1 : ℝ)) - ⟨hyz, -⟩
    exact show y < (1 : ℝ) by linarith
  · rintro x y (hx1 : x < (1 : ℝ)) (hx0 : (0 : ℝ) < x) (hy1 : y < (1 : ℝ)) (hy0 : (0 : ℝ) < y)
    simp only [timelikeLine_le]
    constructor
    · rintro ⟨hxy, -⟩
      exact ⟨hxy, fun w hw => show (0 : ℝ) < w by linarith [hw.1]⟩
    · rintro ⟨hxy, -⟩
      exact ⟨hxy, fun w hw => show w < (1 : ℝ) by linarith [hw.2]⟩
  · exact ⟨by norm_num, fun _ _ => trivial⟩

/-- **`CauchySide` is satisfiable**: the timelike line with the Cauchy surface `{0}`. -/
theorem timelikeLine_cauchySide : CauchySide timelikeLine {(0 : ℝ)} := by
  have hle : ∀ x y : ℝ, timelikeLine.le ⊤ x y ↔ x ≤ y := fun x y => by
    simp only [timelikeLine_le, Opens.coe_top, subset_univ, and_true]
  have hJp : ∀ y : ℝ, y ∈ timelikeLine.Jplus ⊤ {0} ↔ 0 ≤ y := fun y => by
    rw [Precausality.mem_Jplus_singleton]; exact hle 0 y
  have hJm : ∀ y : ℝ, y ∈ timelikeLine.Jminus ⊤ {0} ↔ y ≤ 0 := fun y => by
    rw [Precausality.mem_Jminus_singleton]; exact hle y 0
  refine ⟨fun x => ?_, fun x y hx hy hxy => ⟨0, rfl, ?_, ?_⟩, ?_, isClosed_singleton,
    fun x => ?_, fun x => ?_⟩
  · rcases le_total 0 x with h | h
    · exact Or.inl ((hJp x).2 h)
    · exact Or.inr ((hJm x).2 h)
  · exact (hle x 0).2 ((hJm x).1 hx)
  · exact (hle 0 y).2 ((hJp y).1 hy)
  · have : {z : ℝ × ℝ | timelikeLine.le ⊤ z.1 z.2} = {z | z.1 ≤ z.2} := by
      ext z; exact hle z.1 z.2
    rw [this]; exact _root_.isClosed_le continuous_fst continuous_snd
  · have : timelikeLine.Jplus ⊤ {0} ∩ timelikeLine.Jminus ⊤ {x} = Icc 0 x := by
      ext y
      rw [mem_inter_iff, hJp, Precausality.mem_Jminus_singleton, hle, mem_Icc]
    rw [this]; exact isCompact_Icc
  · have : timelikeLine.Jminus ⊤ {0} ∩ timelikeLine.Jplus ⊤ {x} = Icc x 0 := by
      ext y
      rw [mem_inter_iff, hJm, Precausality.mem_Jplus_singleton, hle, mem_Icc, and_comm]
    rw [this]; exact isCompact_Icc

/-- The chart `a ↦ 1 - e^{-a}/2` of the past piece `]-∞, 1[` of the timelike line. -/
private noncomputable def lineChartPast (a : ℝ) : ℝ := 1 - Real.exp (-a) / 2

/-- The chart `b ↦ e^{b}/2` of the future piece `]0, +∞[` of the timelike line. -/
private noncomputable def lineChartFuture (b : ℝ) : ℝ := Real.exp b / 2

private theorem lineChartPast_strictMono : StrictMono lineChartPast := fun a b h => by
  have := Real.exp_lt_exp.2 (neg_lt_neg h)
  simp only [lineChartPast]; linarith

private theorem lineChartFuture_strictMono : StrictMono lineChartFuture := fun a b h => by
  have := Real.exp_lt_exp.2 h
  simp only [lineChartFuture]; linarith

private theorem range_lineChartPast : range lineChartPast = Iio (1 : ℝ) := by
  ext z
  constructor
  · rintro ⟨a, rfl⟩
    have := Real.exp_pos (-a)
    show lineChartPast a < 1
    simp only [lineChartPast]; linarith
  · intro (hz : z < 1)
    refine ⟨-Real.log (2 * (1 - z)), ?_⟩
    simp only [lineChartPast, neg_neg]
    rw [Real.exp_log (by linarith)]; ring

private theorem range_lineChartFuture : range lineChartFuture = Ioi (0 : ℝ) := by
  ext z
  constructor
  · rintro ⟨b, rfl⟩
    have := Real.exp_pos b
    show 0 < lineChartFuture b
    simp only [lineChartFuture]; linarith
  · intro (hz : 0 < z)
    refine ⟨Real.log (2 * z), ?_⟩
    simp only [lineChartFuture]
    rw [Real.exp_log (by linarith)]; ring

/-- A strictly monotone map onto an open interval `I` is a chart of the piece `I` of the timelike
line (the relation of `I` holds iff the plain order does, `I` being convex). -/
private theorem pieceChart_of_strictMono {I : Opens ℝ} {e : ℝ → ℝ} (he : StrictMono e)
    (hr : range e = (I : Set ℝ)) (hc : OrdConnected (I : Set ℝ)) :
    PieceChart timelikeLine I timelikeLine e := by
  refine ⟨⟨he.isEmbedding_of_ordConnected (hr ▸ hc), hr ▸ I.isOpen⟩, hr, fun a b => ?_⟩
  simp only [timelikeLine_le, Opens.coe_top, subset_univ, and_true, he.le_iff_le]
  constructor
  · exact fun h => h.1
  · intro h
    exact ⟨h, hc.out (hr ▸ mem_range_self a) (hr ▸ mem_range_self b)⟩

/-- **The global hyperbolicity criterion `TwoPiece.globallyHyperbolic` has jointly satisfiable
hypotheses, with proper pieces and charts**: on the timelike line covered by `]-∞, 1[` and
`]0, +∞[` (`timelikeLine_twoPiece`), the monotone homeomorphisms `a ↦ 1 - e^{-a}/2 : ℝ → ]-∞, 1[`
and `b ↦ e^{b}/2 : ℝ → ]0, +∞[` are `PieceChart`s with proper images, the Cauchy sides `{0}`
(`timelikeLine_cauchySide`) have the same image `{1/2}` in the overlap, and the criterion applies. -/
theorem timelikeLine_twoPiece_globallyHyperbolic :
    ∃ e f : ℝ → ℝ,
      PieceChart timelikeLine ⟨Iio (1 : ℝ), isOpen_Iio⟩ timelikeLine e ∧
      PieceChart timelikeLine ⟨Ioi (0 : ℝ), isOpen_Ioi⟩ timelikeLine f ∧
      range e ≠ univ ∧ range f ≠ univ ∧ e '' {0} = f '' {0} ∧
      timelikeLine.GloballyHyperbolic := by
  have he : PieceChart timelikeLine ⟨Iio (1 : ℝ), isOpen_Iio⟩ timelikeLine lineChartPast :=
    pieceChart_of_strictMono lineChartPast_strictMono range_lineChartPast ordConnected_Iio
  have hf : PieceChart timelikeLine ⟨Ioi (0 : ℝ), isOpen_Ioi⟩ timelikeLine lineChartFuture :=
    pieceChart_of_strictMono lineChartFuture_strictMono range_lineChartFuture ordConnected_Ioi
  have hST : lineChartPast '' {0} = lineChartFuture '' {0} := by
    simp only [image_singleton, lineChartPast, lineChartFuture, neg_zero, Real.exp_zero]; norm_num
  refine ⟨lineChartPast, lineChartFuture, he, hf, ?_, ?_, hST,
    timelikeLine_twoPiece.1.globallyHyperbolic he hf timelikeLine_globallyHyperbolic
      timelikeLine_globallyHyperbolic timelikeLine_cauchySide timelikeLine_cauchySide hST⟩
  · rw [range_lineChartPast]; intro h
    exact (lt_irrefl (1 : ℝ)) (h ▸ mem_univ (1 : ℝ) : (1 : ℝ) ∈ Iio 1)
  · rw [range_lineChartFuture]; intro h
    exact (lt_irrefl (0 : ℝ)) (h ▸ mem_univ (0 : ℝ) : (0 : ℝ) ∈ Ioi 0)

end Witness

end Causality

end Causal
