import CausalScaffold.CBG.Ppcm
import CausalScaffold.CBG.Bound
import CausalScaffold.CBG.Pgcd
import CausalScaffold.CBG.FamilyGluing

/-!
# The maximal Cauchy development: gluing all developments along their pairwise MCGHDs (Sbierski Thm 2.8)

Package 10 (`docs/CBG-DESIGN.md` §3 step 7; §5 row 10). **No label is marked** (DEC-60: ETT
labels are the ETT campaign's; rows stay partial until the singular instance discharges the
model). Cited, unmarked: `theo:CBG` — `ETT.tex:1884`, its proof `ETT.tex:2335–2341`,
`rem:CBG_manquant` — `ETT.tex:2343`, `rem:CBG_analytique` — `ETT.tex:1903`; thesis
`theo:Cauchy_ext` (`these.tex:6287`); Sbierski 1309.7591, **Thm 2.8** and its proof (pp. 21–24,
`pdftotext` lines 1145–1288).

> Let $M_0$ be a globally hyperbolic singular flat spacetime. Then $M_0$ admits a maximal Cauchy
> extension, and that extension is unique up to isomorphism. (`theo:CBG`, `ETT.tex:1885–1886`)

> By Proposition \ref{prop:ppcm_Cauchy} any two Cauchy extensions of $M_0$ admit a common
> over-extension, so the family of Cauchy extensions of $M_0$ is directed. It admits an inductive
> limit $\overline{M_0}$ in the category of Hausdorff spaces endowed with a $\mass{\geq0}$-structure;
> the limit is maximal and unique up to equivalence, and the natural map
> $M_0\rightarrow \overline{M_0}$ is a Cauchy embedding. (`ETT.tex:2336–2340`)

> Theorem 2.8 (Existence of MGHD). Given initial data there exists a GHD $\tilde M$ that is an
> extension of any other GHD of the same initial data. (Sbierski, p. 12, `pdftotext` l. 569)

> We denote the MCGHD of Mαi and Mαk with Uαiαk ⊆ Mαi and the corresponding isometric embedding
> with ψαiαk […] For the transitivity observe that […] Uαiαk ∩ ψ⁻¹αiαk(Uαkαl) together with the
> composition ψαkαl ◦ ψαiαk is a CGHD of Mαi and Mαl that contains pαi and identifies it with pαl.
> (Sbierski, `pdftotext` lines 1156–1170) — 1. M̃ is Hausdorff […] (l. 1172) — 4. (M̃, g̃) is
> globally hyperbolic with Cauchy surface ι̃(M) […] (l. 1226) — 5. M̃ is second countable: This
> follows directly from a Theorem of Geroch (l. 1239) — 6. M̃ is an extension of any GHD of the
> same initial data (l. 1242)

## What is proved

* **`cbg`** — the principal theorem (universal form, DEC-59): **sorry-free** (axioms: `propext`,
  `Classical.choice`, `Quot.sound`), stated and proved here since interface round 2 (the sorried
  `CBG/Geometry.cbg` is deleted). `cbg_of_mcghdInjective` is the construction under its parameter
  `MCGHDInjective`, which always holds (`mcghdInjective`, Lemma 3.3 from the field
  `Geometry.timeFunction`); `cbg_of_hasTimeFunctions` is `cbg` with a now-redundant hypothesis,
  kept for `Flat/CBG`.
* The construction, in Sbierski's order: index set `SmallDev 𝔊 s₀ : Type u` (package 9);
  `maxGlueData` (`FamilyGlueData`, package 8) along the pairwise MCGHDs, symmetry
  `mcghdMap_mem_symm`, identity `mcghd_self`, **cocycle `mcghd_cocycle`**; `maxSpace_t2` (T2 from
  the pairs: `t2Space_gluing_mcghd`, package 6); `maxSpace_connected`; the structure
  `exists_maxStr` (`Geometry.glue`); **`maxStr_globallyHyperbolic` FIRST** (design §6 risk:
  without `curvesExtend`/`isCompact_*` on `M̃`), `maxStr_isCauchySurface`, THEN
  `maxSpace_secondCountable` (`Geometry.secondCountable_of_cauchy`); `maxDev`;
  **universality `maxDev_isUniversal`** (DEC-59).
* **Model-free** (`Causal.Causality`): `ManyPiece` — a spacetime covered by a family of pieces with
  causally convex overlaps, agreeing relations and a common set on which every piece has Cauchy
  sides; `le_of_fut`, `le_of_past`, `exists_cross` (chain-wise exit/re-entry), `le_of_le_top`,
  `mem_of_le_top` (each piece causally convex), `exists_mid`, `mem_or_mem`, `isCausal`,
  `isCauchySurface`, `manyPiece_of_charts`, `isCompact_diamond_mixed`, **`globallyHyperbolic`**;
  witness `timelikeLine_manyPiece`.
* **ETT corollaries** (DEC-59, kb/0022), all sorry-free: `cbg_ett` (an ETT-maximal development
  exists and every ETT-maximal one is isomorphic to it by a unique morphism), `cbg_isETTMaximal`,
  `isETTMaximal_iff_isUniversal` (the corollaries formerly stated in `CBG/Geometry`, same
  statements, deleted there at round 2), `Dev.IsUniversal.existsUnique_iso`.

## Hypothesis checklist

| paper / Sbierski | here |
|---|---|
| `M₀` GH singular flat (`ETT.tex:1885`) | ✓ `Geometry` (DEC-60); ⚠ strengthened as in `cbg`: a Cauchy surface `S`, `M₀` T2, connected, second countable (`CBG/Geometry` SCOPE) |
| Lemma 3.3 (`ψ_{ik}` injective) is **proved** from the Lorentzian structure (a time function on each GHD; the embedding property is then used at l. 1157) | ✓ proved from the interface field `Geometry.timeFunction` (A2, interface round 2 (1): a time function on every GH admissible spacetime) — `mcghdInjective` (`mcghdMap_injOn`, `IsCGHD.injOn`); no hypothesis carried by `cbg` |
| (3.15) transitive: `U_ik ∩ ψ⁻¹(U_kl)` is a CGHD (l. 1166–1170) | ✓ the conclusion (`mcghd_cocycle`); ⚠ route replaced (SCOPE) |
| `M̃` Hausdorff from Thm 2.7 (l. 1172) | ✓ `maxSpace_t2` |
| `M̃` GH with Cauchy surface `ι̃(M)` (l. 1226–1240) | ✓ `maxStr_globallyHyperbolic` (ETT's GH: causal + compact diamonds), `maxStr_isCauchySurface`; ⚠ route: chains, not timelike curves |
| `M̃` second countable, Geroch (l. 1239) | ✓ `secondCountable_of_cauchy` (A2, gx C2), applied after GH |
| `M̃` an extension of any GHD (l. 1242) | ✓ universality, the morphism **unique** (rigidity A1); small → all: `Dev.isUniversal_of_small` |
| inductive limit, small skeleton (`ETT.tex:2337`, `rem:CBG_manquant` (ii)) | ✓ `SmallDev` (package 9) and Sbierski's gluing in place of a categorical limit |
| unique up to isomorphism | ✓ `Dev.IsUniversal.existsUnique_iso` (the isomorphism is unique) |

## SCOPE (disclosed)

* **Interface round 2 (1), applied.** `Geometry` now has `timeFunction`; `cbg` is sorry-free
  (formerly `cbg_proof`, whose one `sorry` was this field). It is used only through
  `MCGHDInjective` (Lemma 3.3 on each pair, `mcghdInjective`); no other field is missing. The
  construction (`maxGlueData` … `maxDev_isUniversal`) keeps `hinj : MCGHDInjective 𝔊 s₀` as a
  proof parameter (a `Prop`, always `mcghdInjective 𝔊 s₀`). Renamed: `cbg_proof` → `cbg`,
  `cbg_proof_ett` → `cbg_ett`, `cbg_proof_isETTMaximal` → `cbg_isETTMaximal`,
  `isETTMaximal_iff_isUniversal_proof` → `isETTMaximal_iff_isUniversal` (no alias: no user).
  Deleted as redundant (no user): `cbg_ett_of_mcghdInjective`, `mcghdInjective_of_devTimeFunction`,
  `mcghdInjective_of_hasTimeFunctions`. `Geometry.HasTimeFunctions` and `cbg_of_hasTimeFunctions`
  stay, `Flat/CBG` using both (its hypothesis is now redundant: `𝔊.timeFunction` proves it).
* **The cocycle is not proved by Sbierski's route.** His step needs `U₁₂ ∩ ψ₁₂⁻¹(U₂₃)` to be a
  CGHD, i.e. `ι₁(Σ)` a Cauchy surface of an intersection of Cauchy inclusions — the existence half
  `CBG/CausalConvex` leaves open. Instead: agreement on `U₁₂ ∩ U₁₃` through the `ppcm` of `N₂, N₃`
  (`IsCGHD.eqOn`), and `W ⊆ U₁₃` by connectedness of `W` (`lem:C_ext_connexe`, re-routed) and an
  open–closed argument whose closed half is the Hausdorffness of the `ppcm` of `N₁, N₃`.
* **GH of `M̃` before second countability** (design §6 risk, resolved): `ManyPiece` is the family
  form of package 7's `TwoPiece`; its diamond decomposition is package 7's
  `isCompact_diamond_mixed` proof, copied with the family facts. On `M̃` no `curvesExtend`,
  `isCompact_*`, second countability or time function is used; A2 is used on the `M i` only
  (`timeFunction` there, through `mcghdInjective`).
* The causality of the glued structure is read through the charts `ι i` (`pieceChart_of_isMor`),
  not identified with `FamilyGlueData.causality` (as in package 7).
* `maxStr` is a choice (`Geometry.glue`); universality makes `M̃` independent of it up to unique
  isomorphism. The base index `i₀` (the small copy of `Dev.self`) is likewise immaterial.
* `Geometry` has no inhabitant (its SCOPE); `ManyPiece` is witnessed on the timelike line.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set Topology Filter Function TopologicalSpace Relation

universe u v

namespace Causality

/-! ### Many pieces: a spacetime covered by a family of pieces sharing a Cauchy surface -/

section ManyPiece

variable {P : Type u} [TopologicalSpace P] {ι : Type v}

/-- **A spacetime covered by a family of open pieces `O i` sharing a set `S`** — the abstract
shape of the gluing of all developments along their pairwise MCGHDs (Sbierski, proof of Thm 2.8,
step 4): `D` absolutely minimal on `P`, every overlap `O i ∩ O j` causally convex in `O i` for the
relation of `O i`, the relations of two pieces agreeing on their overlap, `S` in every piece, every
point of a piece on one side of `S` in that piece, and a relation of a piece from the past of `S`
to its future crossing `S` in that piece. -/
structure ManyPiece (D : Causality P) (O : ι → Opens P) (S : Set P) : Prop where
  cover : ∀ z, ∃ i, z ∈ O i
  absolutelyMinimalOn : D.AbsolutelyMinimalOn ⊤
  convex : ∀ i j x y z, x ∈ O j → z ∈ O j → D.le (O i) x y → D.le (O i) y z → y ∈ O j
  agree : ∀ i j x y, x ∈ O i → x ∈ O j → y ∈ O i → y ∈ O j →
    (D.le (O i) x y ↔ D.le (O j) x y)
  subset : ∀ i, S ⊆ O i
  side : ∀ i, ∀ x ∈ O i, (∃ σ ∈ S, D.le (O i) σ x) ∨ ∃ σ ∈ S, D.le (O i) x σ
  crossing : ∀ i x y, (∃ σ ∈ S, D.le (O i) x σ) → (∃ σ ∈ S, D.le (O i) σ y) →
    D.le (O i) x y → ∃ σ ∈ S, D.le (O i) x σ ∧ D.le (O i) σ y

/-- `x` lies in the future of `S` in some piece. -/
def ManyFut (D : Causality P) (O : ι → Opens P) (S : Set P) (x : P) : Prop :=
  ∃ i, ∃ σ ∈ S, D.le (O i) σ x

/-- `x` lies in the past of `S` in some piece. -/
def ManyPast (D : Causality P) (O : ι → Opens P) (S : Set P) (x : P) : Prop :=
  ∃ i, ∃ σ ∈ S, D.le (O i) x σ

variable {D : Causality P} {O : ι → Opens P} {S : Set P}

namespace ManyPiece

/-- The side of `S` is independent of the piece: in the future of `S` in some piece, hence in
every piece containing the point (agreement on the overlap, `S` in every piece). -/
theorem fut_in (h : D.ManyPiece O S) {x : P} {j : ι} (hx : x ∈ O j) (hf : ManyFut D O S x) :
    ∃ σ ∈ S, D.le (O j) σ x := by
  obtain ⟨i, σ, hσ, hle⟩ := hf
  exact ⟨σ, hσ, (h.agree i j σ x (h.subset i hσ) (h.subset j hσ) (D.le_mem_right hle) hx).1 hle⟩

theorem past_in (h : D.ManyPiece O S) {x : P} {j : ι} (hx : x ∈ O j) (hp : ManyPast D O S x) :
    ∃ σ ∈ S, D.le (O j) x σ := by
  obtain ⟨i, σ, hσ, hle⟩ := hp
  exact ⟨σ, hσ, (h.agree i j x σ (D.le_mem_left hle) hx (h.subset i hσ) (h.subset j hσ)).1 hle⟩

/-- Every point is on one side of `S`. -/
theorem fut_or_past (h : D.ManyPiece O S) (x : P) : ManyFut D O S x ∨ ManyPast D O S x := by
  obtain ⟨i, hi⟩ := h.cover x
  rcases h.side i x hi with ⟨σ, hσ, hle⟩ | ⟨σ, hσ, hle⟩
  · exact Or.inl ⟨i, σ, hσ, hle⟩
  · exact Or.inr ⟨i, σ, hσ, hle⟩

theorem fut_of_mem (h : D.ManyPiece O S) {σ : P} (hσ : σ ∈ S) (i : ι) : ManyFut D O S σ :=
  ⟨i, σ, hσ, D.le_refl (h.subset i hσ)⟩

theorem past_of_mem (h : D.ManyPiece O S) {σ : P} (hσ : σ ∈ S) (i : ι) : ManyPast D O S σ :=
  ⟨i, σ, hσ, D.le_refl (h.subset i hσ)⟩

/-- `≤_P` is a chain of relations of the pieces (absolute minimality on the cover `O`). -/
theorem chain (h : D.ManyPiece O S) {x y : P} (hxy : D.le ⊤ x y) :
    TransGen (fun a b => ∃ i, D.le (O i) a b) x y := by
  have hS : ∀ z ∈ (⊤ : Opens P), ∃ O' ∈ range O, z ∈ O' := fun z _ => by
    obtain ⟨i, hi⟩ := h.cover z
    exact ⟨O i, mem_range_self i, hi⟩
  refine TransGen.mono ?_ ((h.absolutelyMinimalOn _ hS ⊤ le_rfl x y).1 hxy)
  rintro a b ⟨_, ⟨i, rfl⟩, hab⟩
  rw [top_inf_eq] at hab
  exact ⟨i, hab⟩

theorem le_of_chain {x y : P} (hc : TransGen (fun a b => ∃ i, D.le (O i) a b) x y) :
    D.le ⊤ x y := by
  induction hc with
  | single hl =>
    obtain ⟨i, hl⟩ := hl
    exact D.le_mono le_top hl
  | tail _ hl ih =>
    obtain ⟨i, hl⟩ := hl
    exact D.le_trans ih (D.le_mono le_top hl)

/-- **A relation of `P` from the future of `S` into a piece stays in that piece** (the exit/re-entry
argument, chain-wise from the end): every point of the chain lies between a point of `S` and the
end, so in the piece by convexity of the overlaps. -/
theorem le_of_fut (h : D.ManyPiece O S) {x y : P} {j : ι} (hxy : D.le ⊤ x y)
    (hf : ManyFut D O S x) (hy : y ∈ O j) : x ∈ O j ∧ D.le (O j) x y := by
  have hc := h.chain hxy
  clear hxy
  revert hf
  induction hc using TransGen.head_induction_on with
  | @single a hl =>
    intro hf
    obtain ⟨k, hk⟩ := hl
    obtain ⟨σ, hσ, hσx⟩ := h.fut_in (D.le_mem_left hk) hf
    have hxj := h.convex k j σ a _ (h.subset j hσ) hy hσx hk
    exact ⟨hxj, (h.agree k j a _ (D.le_mem_left hk) hxj (D.le_mem_right hk) hy).1 hk⟩
  | @head a c hl _ ih =>
    intro hf
    obtain ⟨k, hk⟩ := hl
    obtain ⟨σ, hσ, hσa⟩ := h.fut_in (D.le_mem_left hk) hf
    obtain ⟨hcj, hcy⟩ := ih ⟨k, σ, hσ, D.le_trans hσa hk⟩
    have haj := h.convex k j σ a c (h.subset j hσ) hcj hσa hk
    exact ⟨haj, D.le_trans ((h.agree k j a c (D.le_mem_left hk) haj (D.le_mem_right hk)
      hcj).1 hk) hcy⟩

/-- **A relation of `P` from a piece into the past of `S` stays in that piece.** -/
theorem le_of_past (h : D.ManyPiece O S) {x y : P} {i : ι} (hxy : D.le ⊤ x y)
    (hp : ManyPast D O S y) (hx : x ∈ O i) : y ∈ O i ∧ D.le (O i) x y := by
  have hc := h.chain hxy
  clear hxy
  revert hp
  induction hc with
  | single hl =>
    intro hp
    obtain ⟨k, hk⟩ := hl
    obtain ⟨σ, hσ, hyσ⟩ := h.past_in (D.le_mem_right hk) hp
    have hyi := h.convex k i x _ σ hx (h.subset i hσ) hk hyσ
    exact ⟨hyi, (h.agree k i x _ (D.le_mem_left hk) hx (D.le_mem_right hk) hyi).1 hk⟩
  | @tail b c _ hl ih =>
    intro hp
    obtain ⟨k, hk⟩ := hl
    obtain ⟨σ, hσ, hcσ⟩ := h.past_in (D.le_mem_right hk) hp
    obtain ⟨hbi, hxb⟩ := ih ⟨k, σ, hσ, D.le_trans hk hcσ⟩
    have hci := h.convex k i b c σ hbi (h.subset i hσ) hk hcσ
    exact ⟨hci, D.le_trans hxb ((h.agree k i b c (D.le_mem_left hk) hbi (D.le_mem_right hk)
      hci).1 hk)⟩

/-- **A relation of `P` from the past of `S` to its future crosses `S`.** -/
theorem exists_cross (h : D.ManyPiece O S) {x y : P} (hxy : D.le ⊤ x y)
    (hp : ManyPast D O S x) (hf : ManyFut D O S y) :
    ∃ σ ∈ S, D.le ⊤ x σ ∧ D.le ⊤ σ y := by
  have hc := h.chain hxy
  clear hxy
  revert hf
  induction hc with
  | single hl =>
    intro hf
    obtain ⟨k, hk⟩ := hl
    obtain ⟨σ, hσ, h₁, h₂⟩ := h.crossing k _ _ (h.past_in (D.le_mem_left hk) hp)
      (h.fut_in (D.le_mem_right hk) hf) hk
    exact ⟨σ, hσ, D.le_mono le_top h₁, D.le_mono le_top h₂⟩
  | @tail b c hxb hl ih =>
    intro hf
    obtain ⟨k, hk⟩ := hl
    rcases h.fut_or_past b with hfb | hpb
    · obtain ⟨σ, hσ, h₁, h₂⟩ := ih hfb
      exact ⟨σ, hσ, h₁, D.le_trans h₂ (D.le_mono le_top hk)⟩
    · obtain ⟨σ, hσ, h₁, h₂⟩ := h.crossing k _ _ (h.past_in (D.le_mem_left hk) hpb)
        (h.fut_in (D.le_mem_right hk) hf) hk
      exact ⟨σ, hσ, D.le_trans (le_of_chain hxb) (D.le_mono le_top h₁), D.le_mono le_top h₂⟩

/-- **Between two points of a piece, the relation of `P` is the piece's.** -/
theorem le_of_le_top (h : D.ManyPiece O S) {x y : P} {i : ι} (hx : x ∈ O i) (hy : y ∈ O i)
    (hxy : D.le ⊤ x y) : D.le (O i) x y := by
  rcases h.fut_or_past x with hfx | hpx
  · exact (h.le_of_fut hxy hfx hy).2
  rcases h.fut_or_past y with hfy | hpy
  · obtain ⟨σ, hσ, h₁, h₂⟩ := h.exists_cross hxy hpx hfy
    exact D.le_trans (h.le_of_past h₁ (h.past_of_mem hσ i) hx).2
      (h.le_of_fut h₂ (h.fut_of_mem hσ i) hy).2
  · exact (h.le_of_past hxy hpy hx).2

/-- **A relation from a piece to another passes through their overlap.** -/
theorem exists_mid (h : D.ManyPiece O S) {x y : P} {i j : ι} (hx : x ∈ O i) (hy : y ∈ O j)
    (hxy : D.le ⊤ x y) : ∃ u, u ∈ O i ∧ u ∈ O j ∧ D.le (O i) x u ∧ D.le (O j) u y := by
  rcases h.fut_or_past x with hfx | hpx
  · obtain ⟨hxj, hle⟩ := h.le_of_fut hxy hfx hy
    exact ⟨x, hx, hxj, D.le_refl hx, hle⟩
  rcases h.fut_or_past y with hfy | hpy
  · obtain ⟨σ, hσ, h₁, h₂⟩ := h.exists_cross hxy hpx hfy
    obtain ⟨hσi, h₁'⟩ := h.le_of_past h₁ (h.past_of_mem hσ i) hx
    obtain ⟨hσj, h₂'⟩ := h.le_of_fut h₂ (h.fut_of_mem hσ i) hy
    exact ⟨σ, hσi, hσj, h₁', h₂'⟩
  · obtain ⟨hyi, hle⟩ := h.le_of_past hxy hpy hx
    exact ⟨y, hyi, hy, hle, D.le_refl hy⟩

/-- **Each piece is causally convex in `P`.** -/
theorem mem_of_le_top (h : D.ManyPiece O S) {x y z : P} {i : ι} (hx : x ∈ O i) (hz : z ∈ O i)
    (hxy : D.le ⊤ x y) (hyz : D.le ⊤ y z) : y ∈ O i := by
  rcases h.fut_or_past y with hfy | hpy
  · exact (h.le_of_fut hyz hfy hz).1
  · exact (h.le_of_past hxy hpy hx).1

/-- **A diamond between two pieces lies in their union.** -/
theorem mem_or_mem (h : D.ManyPiece O S) {x y z : P} {i j : ι} (hx : x ∈ O i) (hz : z ∈ O j)
    (hxy : D.le ⊤ x y) (hyz : D.le ⊤ y z) : y ∈ O i ∨ y ∈ O j := by
  rcases h.fut_or_past y with hfy | hpy
  · exact Or.inr (h.le_of_fut hyz hfy hz).1
  · exact Or.inl (h.le_of_past hxy hpy hx).1

/-- The diamonds of `P` between two points of a piece are the piece's. -/
theorem diamond_top_eq (h : D.ManyPiece O S) {p q : P} {i : ι} (hp : p ∈ O i) (hq : q ∈ O i) :
    D.diamond ⊤ p q = D.diamond (O i) p q := by
  ext z
  rw [mem_diamond, mem_diamond]
  constructor
  · rintro ⟨h₁, h₂⟩
    have hz := h.mem_of_le_top hp hq h₁ h₂
    exact ⟨h.le_of_le_top hp hz h₁, h.le_of_le_top hz hq h₂⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨D.le_mono le_top h₁, D.le_mono le_top h₂⟩

/-- **`P` is causal when every piece is.** -/
theorem isCausal (h : D.ManyPiece O S)
    (hO : ∀ i x y, D.le (O i) x y → D.le (O i) y x → x = y) : D.IsCausal := by
  intro x y hxy hyx
  obtain ⟨i, hx⟩ := h.cover x
  have hy := h.mem_of_le_top hx hx hxy hyx
  exact hO i x y (h.le_of_le_top hx hy hxy) (h.le_of_le_top hy hx hyx)

/-- **A Cauchy surface of every piece, acausal in one of them, is a Cauchy surface of `P`**
(Sbierski, proof of Thm 2.8, step 4): existence through the component of the curve in a piece;
uniqueness because two points of `S` on one curve are related in `P`, hence in the piece. -/
theorem isCauchySurface [T2Space P] (h : D.ManyPiece O S) (hcaus : D.IsCausal)
    (hSO : ∀ i, D.IsCauchySurfaceOn (O i) S) {i₀ : ι}
    (hac : ∀ x ∈ S, ∀ y ∈ S, D.le (O i₀) x y → x = y) : D.IsCauchySurface S := by
  intro I c hc
  obtain ⟨t₀, ht₀⟩ := hc.1.nonempty
  have key : ∀ W : Opens P, D.IsCauchySurfaceOn W S → c t₀ ∈ W → ∃ x, x ∈ c '' I ∩ S :=
    fun W hW hmem => by
      obtain ⟨_, ⟨⟨τ, hτ, rfl⟩, hxS⟩, -⟩ := hW _ c
        (inextensible_ordConnectedComponent_of_le (U := ⊤) (fun x y h₁ h₂ => hcaus h₁ h₂)
          le_top hc ht₀ hmem)
      exact ⟨c τ, ⟨τ, (ordConnectedComponent_subset hτ).1, rfl⟩, hxS⟩
  obtain ⟨i, hi⟩ := h.cover (c t₀)
  obtain ⟨x, hx⟩ := key (O i) (hSO i) hi
  refine ⟨x, hx, ?_⟩
  rintro _ ⟨⟨s, hs, rfl⟩, hyS⟩
  obtain ⟨⟨t, ht, rfl⟩, hxS⟩ := hx
  rcases le_total s t with hst | hts
  · exact hac _ hyS _ hxS (h.le_of_le_top (h.subset i₀ hyS) (h.subset i₀ hxS)
      (hc.1.le_of_le hs ht hst))
  · exact (hac _ hxS _ hyS (h.le_of_le_top (h.subset i₀ hxS) (h.subset i₀ hyS)
      (hc.1.le_of_le ht hs hts))).symm

end ManyPiece

end ManyPiece

/-! ### Charts of the pieces; global hyperbolicity of a many-piece spacetime -/

section ManyChart

variable {P : Type u} [TopologicalSpace P] {ι : Type v} {D : Causality P} {O : ι → Opens P}
  {K₀ : Set P}

/-- **A many-piece spacetime from charts** (the form in which the gluing provides it): pieces
charted by spacetimes `X i` with Cauchy-side sets `T i` all sent onto `K₀`; the side and crossing
fields of `ManyPiece` are read through the charts from `CauchySide`. -/
theorem manyPiece_of_charts {X : ι → Type u} [∀ i, TopologicalSpace (X i)]
    {C : ∀ i, Causality (X i)} {e : ∀ i, X i → P} (hcover : ∀ z, ∃ i, z ∈ O i)
    (habs : D.AbsolutelyMinimalOn ⊤)
    (hconv : ∀ i j x y z, x ∈ O j → z ∈ O j → D.le (O i) x y → D.le (O i) y z → y ∈ O j)
    (hagree : ∀ i j x y, x ∈ O i → x ∈ O j → y ∈ O i → y ∈ O j →
      (D.le (O i) x y ↔ D.le (O j) x y))
    (he : ∀ i, PieceChart D (O i) (C i) (e i)) {T : ∀ i, Set (X i)}
    (hT : ∀ i, CauchySide (C i) (T i)) (hTK : ∀ i, e i '' T i = K₀) : D.ManyPiece O K₀ where
  cover := hcover
  absolutelyMinimalOn := habs
  convex := hconv
  agree := hagree
  subset i := by
    rw [← hTK i]
    rintro _ ⟨τ, -, rfl⟩
    exact (he i).mem τ
  side i x hx := by
    obtain ⟨a, rfl⟩ := (he i).exists_eq hx
    rcases (hT i).cover a with ⟨τ, hτ, hτa⟩ | ⟨τ, hτ, haτ⟩
    · exact Or.inl ⟨e i τ, hTK i ▸ mem_image_of_mem _ hτ, ((he i).le_iff τ a).2 hτa⟩
    · exact Or.inr ⟨e i τ, hTK i ▸ mem_image_of_mem _ hτ, ((he i).le_iff a τ).2 haτ⟩
  crossing i x y := by
    rintro ⟨σ, hσ, hxσ⟩ ⟨σ', hσ', hσ'y⟩ hxy
    obtain ⟨a, rfl⟩ := (he i).exists_eq (D.le_mem_left hxy)
    obtain ⟨b, rfl⟩ := (he i).exists_eq (D.le_mem_right hxy)
    rw [← hTK i] at hσ hσ'
    obtain ⟨τ, hτ, rfl⟩ := hσ
    obtain ⟨τ', hτ', rfl⟩ := hσ'
    obtain ⟨τ'', hτ'', h₁, h₂⟩ := (hT i).crossing a b ⟨τ, hτ, ((he i).le_iff a τ).1 hxσ⟩
      ⟨τ', hτ', ((he i).le_iff τ' b).1 hσ'y⟩ (((he i).le_iff a b).1 hxy)
    exact ⟨e i τ'', hTK i ▸ mem_image_of_mem _ hτ'', ((he i).le_iff a τ'').2 h₁,
      ((he i).le_iff τ'' b).2 h₂⟩

variable {X : Type u} [TopologicalSpace X] {Y : Type u} [TopologicalSpace Y]

/-- **A diamond of `P` from one piece to another is compact** (the mixed case; the proof of
`TwoPiece.isCompact_diamond_mixed`, `CBG/Ppcm`, verbatim, with `ManyPiece.exists_mid`,
`convex`, `agree`, `le_of_le_top` for the pair `O i`, `O j`, and `ManyPiece.mem_or_mem` in place
of the two-piece cover: the diamond lies in `O i ∪ O j`). -/
theorem ManyPiece.isCompact_diamond_mixed [T2Space X] [T2Space Y] (h : D.ManyPiece O K₀) {i j : ι}
    {C : Causality X} {C' : Causality Y} {e : X → P} {f : Y → P}
    (he : PieceChart D (O i) C e) (hf : PieceChart D (O j) C' f) {S : Set X} {T : Set Y}
    (hS : CauchySide C S) (hT : CauchySide C' T) (hST : e '' S = f '' T)
    {p q : P} (hpA : p ∈ O i) (hpB : p ∉ O j) (hqB : q ∈ O j) (hqA : q ∉ O i) :
    IsCompact (D.diamond ⊤ p q) := by
  obtain ⟨a, rfl⟩ := he.exists_eq hpA
  obtain ⟨b, rfl⟩ := hf.exists_eq hqB
  have hσ : ∀ σ ∈ S, ∃ τ ∈ T, f τ = e σ := fun σ hσS => by
    have : e σ ∈ f '' T := hST ▸ mem_image_of_mem e hσS
    exact this
  have hτ : ∀ τ ∈ T, ∃ σ ∈ S, e σ = f τ := fun τ hτT => by
    have : f τ ∈ e '' S := hST.symm ▸ mem_image_of_mem f hτT
    exact this
  have hσB : ∀ σ ∈ S, e σ ∈ O j := fun σ hσS => by
    obtain ⟨τ, -, e'⟩ := hσ σ hσS; rw [← e']; exact hf.mem τ
  have hτA : ∀ τ ∈ T, f τ ∈ O i := fun τ hτT => by
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
      · exact absurd (h.convex i j (e σ) (e a) u₀ (hσB σ hσS) hu₀B
          ((he.le_iff σ a).2 hσa) hpu₀) hpB
      · exact ha
    have hb : b ∈ C'.Jplus ⊤ T := by
      rcases hT.cover b with hb | ⟨τ, hτT, hbτ⟩
      · exact hb
      · exact absurd (h.convex j i u₀ (f b) (f τ) hu₀A (hτA τ hτT) hu₀q
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
          have h1 : D.le (O j) (e σ) (e u₁) :=
            (h.agree i j _ _ (he.mem σ) (hσB σ hσS) huA huB).1 ((he.le_iff σ u₁).2 hσu)
          rw [← hfτ, ← hu₂] at h1
          have hτu : C'.le ⊤ τ u₂ := (hf.le_iff τ u₂).1 h1
          exact ⟨σ, ⟨τ, ⟨hτT, by simpa using C'.le_trans hτu hu₂b⟩, hfτ⟩, hcσ⟩
        · obtain ⟨τ', hτ'T, hfτ'⟩ := hσ σ' hσ'S
          have h1 : D.le (O j) (e u₁) (e σ') :=
            (h.agree i j _ _ huA huB (he.mem σ') (hσB σ' hσ'S)).1 ((he.le_iff u₁ σ').2 hu₁σ')
          rw [← hfτ', ← hu₂] at h1
          have hu₂T : u₂ ∈ C'.Jminus ⊤ T := ⟨τ', hτ'T, (hf.le_iff u₂ τ').1 h1⟩
          obtain ⟨τ, hτT, hu₂τ, hτb⟩ := hT.crossing u₂ b hu₂T hb hu₂b
          obtain ⟨σ, hσS, heσ⟩ := hτ τ hτT
          have h2 : D.le (O j) (e u₁) (e σ) := by
            rw [← hu₂, heσ]; exact (hf.le_iff u₂ τ).2 hu₂τ
          have h3 := (h.agree i j _ _ huA huB (he.mem σ) (hσB σ hσS)).2 h2
          exact ⟨σ, ⟨τ, ⟨hτT, by simpa using hτb⟩, heσ.symm⟩,
            C.le_trans hcu ((he.le_iff u₁ σ).1 h3)⟩
      exact Or.inl ⟨c, ⟨⟨hcS, by simpa using hac⟩, σ, hσF, hcσ⟩, rfl⟩
    have P2 : ∀ d, f d = z → d ∈ C'.Jplus ⊤ T → z ∈ e '' K₁ ∪ f '' K₂ := by
      rintro d rfl hdT
      have hdb : C'.le ⊤ d b :=
        (hf.le_iff d b).1 (h.le_of_le_top (hf.mem d) (hf.mem b) hzq)
      obtain ⟨u, huA, huB, hpu, huz⟩ := h.exists_mid (he.mem a) (hf.mem d) hpz
      obtain ⟨u₁, rfl⟩ := he.exists_eq huA
      obtain ⟨u₂, hu₂⟩ := hf.exists_eq huB
      have hau : C.le ⊤ a u₁ := (he.le_iff a u₁).1 hpu
      have hu₂d : C'.le ⊤ u₂ d := (hf.le_iff u₂ d).1 (hu₂ ▸ huz)
      obtain ⟨τ, hτG, hτd⟩ : ∃ τ ∈ G, C'.le ⊤ τ d := by
        rcases hT.cover u₂ with ⟨τ', hτ'T, hτ'u₂⟩ | hu₂T
        · obtain ⟨σ', hσ'S, heσ'⟩ := hτ τ' hτ'T
          have h1 : D.le (O i) (e σ') (e u₁) := by
            have h0 : D.le (O j) (f τ') (f u₂) := (hf.le_iff τ' u₂).2 hτ'u₂
            rw [← heσ', hu₂] at h0
            exact (h.agree i j _ _ (he.mem σ') (hσB σ' hσ'S) huA huB).2 h0
          have hu₁S : u₁ ∈ C.Jplus ⊤ S := ⟨σ', hσ'S, (he.le_iff σ' u₁).1 h1⟩
          obtain ⟨σ, hσS, haσ, hσu₁⟩ := hS.crossing a u₁ ha hu₁S hau
          obtain ⟨τ, hτT, hfτ⟩ := hσ σ hσS
          have h2 : D.le (O j) (f τ) (f u₂) := by
            rw [hfτ, hu₂]
            exact (h.agree i j _ _ (he.mem σ) (hσB σ hσS) huA huB).1 ((he.le_iff σ u₁).2 hσu₁)
          exact ⟨τ, ⟨σ, ⟨hσS, by simpa using haσ⟩, hfτ.symm⟩,
            C'.le_trans ((hf.le_iff τ u₂).1 h2) hu₂d⟩
        · obtain ⟨τ, hτT, hu₂τ, hτd⟩ := hT.crossing u₂ d hu₂T hdT hu₂d
          obtain ⟨σ, hσS, heσ⟩ := hτ τ hτT
          have h2 : D.le (O i) (e u₁) (e σ) := by
            have h0 : D.le (O j) (f u₂) (f τ) := (hf.le_iff u₂ τ).2 hu₂τ
            rw [hu₂, ← heσ] at h0
            exact (h.agree i j _ _ huA huB (he.mem σ) (hσB σ hσS)).2 h0
          exact ⟨τ, ⟨σ, ⟨hσS, by simpa using C.le_trans hau ((he.le_iff u₁ σ).1 h2)⟩, heσ⟩,
            hτd⟩
      exact Or.inr ⟨d, ⟨⟨hdT, by simpa using hdb⟩, τ, hτG, hτd⟩, rfl⟩
    rcases h.mem_or_mem (he.mem a) (hf.mem b) hpz hzq with hzA | hzB
    · obtain ⟨c, rfl⟩ := he.exists_eq hzA
      rcases hS.cover c with ⟨σ₀, hσ₀S, hσ₀c⟩ | hcS
      · obtain ⟨u, -, huB, hzu, -⟩ := h.exists_mid (he.mem c) (hf.mem b) hzq
        have hzB := h.convex i j (e σ₀) (e c) u (hσB σ₀ hσ₀S) huB ((he.le_iff σ₀ c).2 hσ₀c) hzu
        obtain ⟨d, hd⟩ := hf.exists_eq hzB
        obtain ⟨τ₀, hτ₀T, hfτ₀⟩ := hσ σ₀ hσ₀S
        have h1 : D.le (O j) (f τ₀) (f d) := by
          rw [hfτ₀, hd]
          exact (h.agree i j _ _ (he.mem σ₀) (hσB σ₀ hσ₀S) (he.mem c) hzB).1
            ((he.le_iff σ₀ c).2 hσ₀c)
        exact P2 d hd ⟨τ₀, hτ₀T, (hf.le_iff τ₀ d).1 h1⟩
      · exact P1 c rfl hcS
    · obtain ⟨d, rfl⟩ := hf.exists_eq hzB
      rcases hT.cover d with hdT | ⟨τ₀, hτ₀T, hdτ₀⟩
      · exact P2 d rfl hdT
      · obtain ⟨u, huA, -, -, huz⟩ := h.exists_mid (he.mem a) (hf.mem d) hpz
        have hzA := h.convex j i u (f d) (f τ₀) huA (hτA τ₀ hτ₀T) huz
          ((hf.le_iff d τ₀).2 hdτ₀)
        obtain ⟨c, hc⟩ := he.exists_eq hzA
        obtain ⟨σ₀, hσ₀S, heσ₀⟩ := hτ τ₀ hτ₀T
        have h1 : D.le (O i) (e c) (e σ₀) := by
          rw [hc, heσ₀]
          exact (h.agree i j _ _ hzA (hf.mem d) (hτA τ₀ hτ₀T) (hf.mem τ₀)).2
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


/-- **A many-piece spacetime is globally hyperbolic** when every piece is, through charts, with
Cauchy sides sent onto the common `K₀` (Sbierski, proof of Thm 2.8, step 4, in ETT's sense:
causal and compact diamonds): causal by `ManyPiece.isCausal`, diamonds inside a piece compact by
`diamond_top_eq` and the chart, across two pieces by `isCompact_diamond_mixed`. No curve
extension, no compactness and no second countability of `P` is used. -/
theorem ManyPiece.globallyHyperbolic {Xs : ι → Type u} [∀ i, TopologicalSpace (Xs i)]
    [∀ i, T2Space (Xs i)] (h : D.ManyPiece O K₀) {C : ∀ i, Causality (Xs i)}
    {e : ∀ i, Xs i → P} (he : ∀ i, PieceChart D (O i) (C i) (e i))
    (hG : ∀ i, (C i).GloballyHyperbolic) {T : ∀ i, Set (Xs i)}
    (hT : ∀ i, CauchySide (C i) (T i)) (hTK : ∀ i, e i '' T i = K₀) :
    D.GloballyHyperbolic := by
  refine ⟨h.isCausal fun i => (he i).antisymm (hG i).1, fun p q => ?_⟩
  have hsame : ∀ i, p ∈ O i → q ∈ O i → IsCompact (D.diamond ⊤ p q) := fun i hp hq => by
    obtain ⟨a, rfl⟩ := (he i).exists_eq hp
    obtain ⟨b, rfl⟩ := (he i).exists_eq hq
    rw [h.diamond_top_eq hp hq, (he i).diamond_eq]
    exact ((hG i).2 a b).image (he i).isOpenEmbedding.continuous
  obtain ⟨i, hpi⟩ := h.cover p
  obtain ⟨j, hqj⟩ := h.cover q
  by_cases hqi : q ∈ O i
  · exact hsame i hpi hqi
  by_cases hpj : p ∈ O j
  · exact hsame j hpj hqj
  exact h.isCompact_diamond_mixed (he i) (he j) (hT i) (hT j) ((hTK i).trans (hTK j).symm)
    hpi hpj hqj hqi

end ManyChart

/-! ### Witness: the many-piece hypotheses are satisfiable (kb/0011) -/

section Witness

/-- The cover of the timelike line by `]-∞, 1[` and `]0, +∞[`. -/
def lineCover : Bool → Opens ℝ
  | true => ⟨Iio (1 : ℝ), isOpen_Iio⟩
  | false => ⟨Ioi (0 : ℝ), isOpen_Ioi⟩

theorem ordConnected_lineCover (b : Bool) : OrdConnected (lineCover b : Set ℝ) := by
  cases b
  · exact ordConnected_Ioi
  · exact ordConnected_Iio

theorem half_mem_lineCover (b : Bool) : (1 / 2 : ℝ) ∈ lineCover b := by
  cases b
  · show (0 : ℝ) < 1 / 2; norm_num
  · show (1 / 2 : ℝ) < 1; norm_num

theorem timelikeLine_le_lineCover {b : Bool} {x y : ℝ} (hx : x ∈ lineCover b)
    (hy : y ∈ lineCover b) : timelikeLine.le (lineCover b) x y ↔ x ≤ y := by
  simp only [timelikeLine_le]
  exact ⟨fun h => h.1, fun h => ⟨h, (ordConnected_lineCover b).out hx hy⟩⟩

/-- **`ManyPiece` is satisfiable with proper pieces** — the timelike line (a local causality,
absolutely minimal; kb/0014/0019) covered by `]-∞, 1[` and `]0, +∞[`, with `S = {1/2}`; the mixed
case of `isCompact_diamond_mixed` occurs (`-1 ≤ 2`, `-1 ∉ ]0,+∞[`, `2 ∉ ]-∞,1[`). -/
theorem timelikeLine_manyPiece :
    timelikeLine.ManyPiece lineCover {(1 / 2 : ℝ)} ∧
      timelikeLine.le ⊤ (-1) 2 ∧ (-1 : ℝ) ∉ lineCover false ∧ (2 : ℝ) ∉ lineCover true := by
  refine ⟨⟨fun z => ?_, timelikeLine_absolutelyMinimalOn ⊤, ?_, ?_, ?_, ?_, ?_⟩,
    ⟨by norm_num, fun _ _ => trivial⟩, by show ¬ (0 : ℝ) < -1; norm_num,
    by show ¬ (2 : ℝ) < 1; norm_num⟩
  · rcases lt_or_ge z 1 with h | h
    · exact ⟨true, h⟩
    · exact ⟨false, show (0 : ℝ) < z by linarith⟩
  · rintro i j x y z hx hz ⟨hxy, -⟩ ⟨hyz, -⟩
    exact (ordConnected_lineCover j).out hx hz ⟨hxy, hyz⟩
  · intro i j x y hxi hxj hyi hyj
    rw [timelikeLine_le_lineCover hxi hyi, timelikeLine_le_lineCover hxj hyj]
  · intro i σ hσ
    rw [mem_singleton_iff] at hσ
    subst hσ
    exact half_mem_lineCover i
  · intro i x hx
    rcases le_total (1 / 2 : ℝ) x with h | h
    · exact Or.inl ⟨1 / 2, rfl, (timelikeLine_le_lineCover (half_mem_lineCover i) hx).2 h⟩
    · exact Or.inr ⟨1 / 2, rfl, (timelikeLine_le_lineCover hx (half_mem_lineCover i)).2 h⟩
  · rintro i x y ⟨σ, hσ, hxσ⟩ ⟨σ', hσ', hσ'y⟩ -
    rw [mem_singleton_iff] at hσ hσ'
    subst hσ hσ'
    exact ⟨1 / 2, rfl, hxσ, hσ'y⟩

end Witness

end Causality

namespace CBG

/-! ### The pairwise MCGHDs form a cocycle (Sbierski, proof of Thm 2.8, transitivity of (3.15)) -/

section Cocycle

variable {𝔊 : Geometry.{u}} {M₀ : Type u} [TopologicalSpace M₀] {s₀ : 𝔊.Str M₀}
  [ConnectedSpace M₀]

/-- **The MCGHD of a development with itself is the whole development, with the identity.** -/
theorem mcghd_self (N : Dev 𝔊.toPreGeometry s₀) :
    mcghdOpens N N = ⊤ ∧ EqOn (mcghdMap N N) id (⊤ : Opens N.carrier) := by
  have h : IsCGHD N N ⊤ id := ⟨N.isCauchyInclusion_range_top, 𝔊.isMor_id _ _, rfl⟩
  exact ⟨top_le_iff.1 (le_mcghdOpens h), mcghdMap_eqOn h⟩

/-- **Symmetry of the MCGHD** (`U_{ki} = ψ_{ik}(U_{ik})`, used by Sbierski without statement):
`ψ(U₁₂)` with `ψ⁻¹` is a common Cauchy development of `N₂` and `N₁`, so `ψ(U₁₂) ⊆ U₂₁`. -/
theorem mcghdMap_mem_symm {N₁ N₂ : Dev 𝔊.toPreGeometry s₀}
    (hinj : InjOn (mcghdMap N₁ N₂) (mcghdOpens N₁ N₂)) {x : N₁.carrier}
    (hx : x ∈ mcghdOpens N₁ N₂) : mcghdMap N₁ N₂ x ∈ mcghdOpens N₂ N₁ := by
  haveI : Nonempty N₁.carrier := ⟨N₁.emb (Classical.arbitrary M₀)⟩
  have hU := isCGHD_mcghd (N₁ := N₁) (N₂ := N₂)
  have h : IsCGHD N₂ N₁ (mcghdImage N₁ N₂)
      (invFunOn (mcghdMap N₁ N₂) (mcghdOpens N₁ N₂ : Set N₁.carrier)) := by
    refine ⟨hU.isCauchyInclusion_image hinj, 𝔊.isMor_inv hU.2.1 hinj, ?_⟩
    funext a
    have ha : N₁.emb a ∈ mcghdOpens N₁ N₂ := hU.1.1 (N₁.emb_mem_range a)
    show invFunOn _ _ (N₂.emb a) = N₁.emb a
    rw [← congrFun hU.2.2 a, comp_apply, hinj.leftInvOn_invFunOn ha]
  exact le_mcghdOpens h ⟨x, hx, rfl⟩

/-- The MCGHD is preconnected after composing with a second MCGHD:
`U₁₂ ∩ ψ₁₂⁻¹(U₂₃)` is the image by `ψ₁₂⁻¹` of `ψ₁₂(U₁₂) ∩ U₂₃`, an intersection of two Cauchy
inclusions of `ι₂(M₀)` in `N₂`, connected by `lem:C_ext_connexe` (`c_ext_connexe_of_connectedSpace`,
re-routed). -/
theorem isPreconnected_mcghd_inter {N₁ N₂ N₃ : Dev 𝔊.toPreGeometry s₀}
    (hinj : InjOn (mcghdMap N₁ N₂) (mcghdOpens N₁ N₂)) :
    IsPreconnected ((mcghdOpens N₁ N₂ : Set N₁.carrier) ∩
      mcghdMap N₁ N₂ ⁻¹' (mcghdOpens N₂ N₃ : Set N₂.carrier)) := by
  haveI : Nonempty N₁.carrier := ⟨N₁.emb (Classical.arbitrary M₀)⟩
  have hU := isCGHD_mcghd (N₁ := N₁) (N₂ := N₂)
  have hconn := N₂.isCauchyEmbedding.c_ext_connexe_of_connectedSpace
    (hU.isCauchyInclusion_image hinj) (isCGHD_mcghd (N₁ := N₂) (N₂ := N₃)).1
    N₂.causality_curvesExtend
  have hcont : ContinuousOn (invFunOn (mcghdMap N₁ N₂) (mcghdOpens N₁ N₂ : Set N₁.carrier))
      (mcghdImage N₁ N₂ : Set N₂.carrier) :=
    (𝔊.isEMorphismOn_of_isMor (𝔊.isMor_inv hU.2.1 hinj)).continuousOn
  have heq : invFunOn (mcghdMap N₁ N₂) (mcghdOpens N₁ N₂ : Set N₁.carrier) ''
      ((mcghdImage N₁ N₂ ⊓ mcghdOpens N₂ N₃ : Opens N₂.carrier) : Set N₂.carrier) =
      (mcghdOpens N₁ N₂ : Set N₁.carrier) ∩
        mcghdMap N₁ N₂ ⁻¹' (mcghdOpens N₂ N₃ : Set N₂.carrier) := by
    ext x
    constructor
    · rintro ⟨_, ⟨⟨y, hy, rfl⟩, hy3⟩, rfl⟩
      rw [hinj.leftInvOn_invFunOn hy]
      exact ⟨hy, hy3⟩
    · rintro ⟨hx, hx3⟩
      exact ⟨mcghdMap N₁ N₂ x, ⟨⟨x, hx, rfl⟩, hx3⟩, hinj.leftInvOn_invFunOn hx⟩
  rw [← heq]
  exact hconn.isPreconnected.image _ (hcont.mono inf_le_left)

/-- **The cocycle condition** (Sbierski, proof of Thm 2.8: "`U_{ik} ∩ ψ⁻¹_{ik}(U_{kl})` together
with `ψ_{kl} ∘ ψ_{ik}` is a CGHD of `M_i` and `M_l` […] so certainly the MCGHD of `M_i` and `M_l`
leads to the same identification"): `x ∈ U₁₂`, `ψ₁₂ x ∈ U₂₃` give `x ∈ U₁₃` and
`ψ₂₃ (ψ₁₂ x) = ψ₁₃ x`.

Sbierski's route needs `U₁₂ ∩ ψ₁₂⁻¹(U₂₃)` to be a CGHD, i.e. `ι₁(Σ)` a Cauchy surface of an
intersection of Cauchy inclusions — the existence half `CBG/CausalConvex` leaves open. It is
replaced: the identity holds on `U₁₂ ∩ U₁₃` (both sides are CGHDs of `N₁` and the `ppcm` of `N₂`,
`N₃`, which agree by `IsCGHD.eqOn`), and `W := U₁₂ ∩ ψ₁₂⁻¹(U₂₃)`, preconnected
(`isPreconnected_mcghd_inter`), lies in `U₁₃` by an open–closed argument whose closed half is
the **Hausdorffness of the gluing of `N₁` and `N₃` along `U₁₃`** (`t2Space_gluing_mcghd`, Sbierski
Thm 3.13): at a limit point `x ∈ W` of `W ∩ U₁₃`, `ι₁ a = ι₃ (ψ₂₃ ψ₁₂ a)` for `a → x`, so
`ι₁ x = ι₃ (ψ₂₃ ψ₁₂ x)`. -/
theorem mcghd_cocycle {N₁ N₂ N₃ : Dev 𝔊.toPreGeometry s₀}
    (h₁₂ : InjOn (mcghdMap N₁ N₂) (mcghdOpens N₁ N₂))
    (h₂₃ : InjOn (mcghdMap N₂ N₃) (mcghdOpens N₂ N₃))
    (h₁₃ : InjOn (mcghdMap N₁ N₃) (mcghdOpens N₁ N₃)) {x : N₁.carrier}
    (hx : x ∈ mcghdOpens N₁ N₂) (hy : mcghdMap N₁ N₂ x ∈ mcghdOpens N₂ N₃) :
    x ∈ mcghdOpens N₁ N₃ ∧ mcghdMap N₂ N₃ (mcghdMap N₁ N₂ x) = mcghdMap N₁ N₃ x := by
  haveI : Nonempty N₁.carrier := ⟨N₁.emb (Classical.arbitrary M₀)⟩
  have hU₁₂ := isCGHD_mcghd (N₁ := N₁) (N₂ := N₂)
  have hU₂₃ := isCGHD_mcghd (N₁ := N₂) (N₂ := N₃)
  have hU₁₃ := isCGHD_mcghd (N₁ := N₁) (N₂ := N₃)
  -- the identity on `U₁₂ ∩ U₁₃ ∩ ψ₁₂⁻¹(U₂₃)`, through the ppcm of `N₂` and `N₃`
  have hP₁ := ppcmDev_isMorphism₁ h₂₃
  have hP₂ := ppcmDev_isMorphism₂ h₂₃
  have hA : IsCGHD N₁ (ppcmDev N₂ N₃ h₂₃) (mcghdOpens N₁ N₂)
      (Gluing.ι₁ (Subtype.val : mcghdOpens N₂ N₃ → N₂.carrier) (mcghdMap N₂ N₃ ∘ Subtype.val) ∘
        mcghdMap N₁ N₂) :=
    ⟨hU₁₂.1, 𝔊.isMor_comp hP₁.1 hU₁₂.2.1 (fun _ _ => trivial), by
      rw [Function.comp_assoc, hU₁₂.2.2]; exact hP₁.2⟩
  have hB : IsCGHD N₁ (ppcmDev N₂ N₃ h₂₃) (mcghdOpens N₁ N₃)
      (Gluing.ι₂ (Subtype.val : mcghdOpens N₂ N₃ → N₂.carrier) (mcghdMap N₂ N₃ ∘ Subtype.val) ∘
        mcghdMap N₁ N₃) :=
    ⟨hU₁₃.1, 𝔊.isMor_comp hP₂.1 hU₁₃.2.1 (fun _ _ => trivial), by
      rw [Function.comp_assoc, hU₁₃.2.2]; exact hP₂.2⟩
  have hagree : ∀ a, a ∈ mcghdOpens N₁ N₂ → a ∈ mcghdOpens N₁ N₃ →
      mcghdMap N₁ N₂ a ∈ mcghdOpens N₂ N₃ →
      mcghdMap N₂ N₃ (mcghdMap N₁ N₂ a) = mcghdMap N₁ N₃ a := by
    intro a ha₂ ha₃ hay
    have e1 := hA.eqOn hB ⟨ha₂, ha₃⟩
    simp only [comp_apply] at e1
    rw [ppcm_ι₁_eq hay] at e1
    exact Gluing.injective_ι₂ Subtype.val_injective (ppcm_injective_j₂ h₂₃) e1
  -- `W := U₁₂ ∩ ψ₁₂⁻¹(U₂₃)` lies in `U₁₃`
  have hcont₁₂ : ContinuousOn (mcghdMap N₁ N₂) (mcghdOpens N₁ N₂ : Set N₁.carrier) :=
    (𝔊.isEMorphismOn_of_isMor hU₁₂.2.1).continuousOn
  have hcont₂₃ : ContinuousOn (mcghdMap N₂ N₃) (mcghdOpens N₂ N₃ : Set N₂.carrier) :=
    (𝔊.isEMorphismOn_of_isMor hU₂₃.2.1).continuousOn
  have hWopen : IsOpen ((mcghdOpens N₁ N₂ : Set N₁.carrier) ∩
      mcghdMap N₁ N₂ ⁻¹' (mcghdOpens N₂ N₃ : Set N₂.carrier)) :=
    hcont₁₂.isOpen_inter_preimage (mcghdOpens N₁ N₂).isOpen (mcghdOpens N₂ N₃).isOpen
  have hsub : (mcghdOpens N₁ N₂ : Set N₁.carrier) ∩
      mcghdMap N₁ N₂ ⁻¹' (mcghdOpens N₂ N₃ : Set N₂.carrier) ⊆ mcghdOpens N₁ N₃ := by
    refine (isPreconnected_mcghd_inter h₁₂).subset_of_closure_inter_subset
      (mcghdOpens N₁ N₃).isOpen ?_ ?_
    · obtain ⟨a⟩ := (inferInstance : Nonempty M₀)
      refine ⟨N₁.emb a, ⟨hU₁₂.1.1 (N₁.emb_mem_range a), ?_⟩, hU₁₃.1.1 (N₁.emb_mem_range a)⟩
      show mcghdMap N₁ N₂ (N₁.emb a) ∈ (mcghdOpens N₂ N₃ : Set N₂.carrier)
      rw [show mcghdMap N₁ N₂ (N₁.emb a) = N₂.emb a from congrFun hU₁₂.2.2 a]
      exact hU₂₃.1.1 (N₂.emb_mem_range a)
    · rintro z ⟨hzc, hzW⟩
      by_contra hz
      haveI := t2Space_gluing_mcghd (N₁ := N₁) (N₂ := N₃)
      have hzc' := hWopen.inter_closure ⟨hzW, hzc⟩
      haveI := mem_closure_iff_nhdsWithin_neBot.1 hzc'
      have hg : ContinuousAt (mcghdMap N₂ N₃ ∘ mcghdMap N₁ N₂) z :=
        (hcont₂₃.continuousAt ((mcghdOpens N₂ N₃).isOpen.mem_nhds hzW.2)).comp
          (hcont₁₂.continuousAt ((mcghdOpens N₁ N₂).isOpen.mem_nhds hzW.1))
      have t1 := ((Gluing.continuous_ι₁ (j₁ := (Subtype.val : mcghdOpens N₁ N₃ → N₁.carrier))
        (j₂ := mcghdMap N₁ N₃ ∘ Subtype.val)).continuousAt (x := z)).tendsto.mono_left
          (nhdsWithin_le_nhds (s := (mcghdOpens N₁ N₂ : Set N₁.carrier) ∩
            mcghdMap N₁ N₂ ⁻¹' (mcghdOpens N₂ N₃ : Set N₂.carrier) ∩ mcghdOpens N₁ N₃))
      have t2 := (((Gluing.continuous_ι₂ (j₁ := (Subtype.val : mcghdOpens N₁ N₃ → N₁.carrier))
        (j₂ := mcghdMap N₁ N₃ ∘ Subtype.val)).continuousAt).comp hg).tendsto.mono_left
          (nhdsWithin_le_nhds (s := (mcghdOpens N₁ N₂ : Set N₁.carrier) ∩
            mcghdMap N₁ N₂ ⁻¹' (mcghdOpens N₂ N₃ : Set N₂.carrier) ∩ mcghdOpens N₁ N₃))
      have heq : (Gluing.ι₁ (Subtype.val : mcghdOpens N₁ N₃ → N₁.carrier)
          (mcghdMap N₁ N₃ ∘ Subtype.val)) =ᶠ[𝓝[(mcghdOpens N₁ N₂ : Set N₁.carrier) ∩
            mcghdMap N₁ N₂ ⁻¹' (mcghdOpens N₂ N₃ : Set N₂.carrier) ∩ mcghdOpens N₁ N₃] z]
          (Gluing.ι₂ (Subtype.val : mcghdOpens N₁ N₃ → N₁.carrier)
            (mcghdMap N₁ N₃ ∘ Subtype.val) ∘ (mcghdMap N₂ N₃ ∘ mcghdMap N₁ N₂)) := by
        filter_upwards [self_mem_nhdsWithin] with a ha
        obtain ⟨⟨ha₂, ha₃'⟩, ha₃⟩ := ha
        show _ = Gluing.ι₂ _ _ (mcghdMap N₂ N₃ (mcghdMap N₁ N₂ a))
        rw [hagree a ha₂ ha₃ ha₃']
        exact ppcm_ι₁_eq ha₃
      exact hz ((ppcm_ι₁_eq_ι₂_iff h₁₃).1 (tendsto_nhds_unique (t1.congr' heq) t2)).1
  have hx₃ := hsub ⟨hx, hy⟩
  exact ⟨hx₃, hagree x hx hx₃ hy⟩

end Cocycle

/-! ### The gluing of all small developments along their pairwise MCGHDs -/

section MaxGluing

variable {𝔊 : Geometry.{u}} {M₀ : Type u} [TopologicalSpace M₀] {s₀ : 𝔊.Str M₀}
  [ConnectedSpace M₀]

variable (𝔊 s₀) in
/-- **The MCGHD morphisms are injective**, for every pair of developments (Sbierski: « the
corresponding isometric embedding `ψ_{α_i α_k}` »), as a predicate: the parameter of the
construction below. It always holds (`mcghdInjective`, Lemma 3.3 from the interface field
`Geometry.timeFunction`). -/
def MCGHDInjective : Prop :=
  ∀ N₁ N₂ : Dev 𝔊.toPreGeometry s₀, InjOn (mcghdMap N₁ N₂) (mcghdOpens N₁ N₂)

variable (𝔊 s₀) in
/-- **Every MCGHD morphism is injective** (Sbierski Lemma 3.3 on each pair, `mcghdMap_injOn`,
`CBG/Pgcd`, by the time function of `Geometry.timeFunction`, interface round 2). -/
theorem mcghdInjective : MCGHDInjective 𝔊 s₀ :=
  fun _ _ => mcghdMap_injOn

variable (hinj : MCGHDInjective 𝔊 s₀)

/-- **The glue data of all small developments** (Sbierski (3.15)): `U i j` the MCGHD of `i` and
`j`, `φ i j` its morphism; symmetry `mcghdMap_mem_symm`, identity `mcghd_self`, cocycle
`mcghd_cocycle`. -/
noncomputable def maxGlueData :
    FamilyGlueData (SmallDev 𝔊.toPreGeometry s₀) fun i => i.Carrier where
  U i j := mcghdOpens i.toDev j.toDev
  φ i j := mcghdMap i.toDev j.toDev ∘ Subtype.val
  continuous_φ i j :=
    (𝔊.isEMorphismOn_of_isMor
      (isCGHD_mcghd (N₁ := i.toDev) (N₂ := j.toDev)).2.1).continuousOn.comp_continuous
      continuous_subtype_val fun x => x.2
  φ_mem _ _ x := mcghdMap_mem_symm (hinj _ _) x.2
  U_self i := (mcghd_self i.toDev).1
  φ_self i x := (mcghd_self i.toDev).2 (show (x : i.Carrier) ∈ (⊤ : Opens i.Carrier) from trivial)
  cocycle _ _ _ x h :=
    ⟨(mcghd_cocycle (hinj _ _) (hinj _ _) (hinj _ _) x.2 h).1,
      (mcghd_cocycle (hinj _ _) (hinj _ _) (hinj _ _) x.2 h).2⟩

/-- **The glued space** `M̃ = (⊔ M_α)/∼` (Sbierski, proof of Thm 2.8). -/
abbrev MaxSpace : Type u := (maxGlueData hinj).Glued

/-- `ι i x ∈ ι j (M j)` iff `x` is in the MCGHD of `i` and `j`. -/
theorem maxι_mem_O_iff {i j : SmallDev 𝔊.toPreGeometry s₀} {x : i.Carrier} :
    (maxGlueData hinj).ι i x ∈ (maxGlueData hinj).O j ↔ x ∈ mcghdOpens i.toDev j.toDev :=
  ⟨fun ⟨_, hy⟩ => ((maxGlueData hinj).ι_eq_ι_iff.1 hy.symm).1,
    fun hx => ⟨_, (maxGlueData hinj).ι_φ i j ⟨x, hx⟩⟩⟩

theorem maxι_eq {i j : SmallDev 𝔊.toPreGeometry s₀} {x : i.Carrier}
    (hx : x ∈ mcghdOpens i.toDev j.toDev) :
    (maxGlueData hinj).ι i x = (maxGlueData hinj).ι j (mcghdMap i.toDev j.toDev x) :=
  ((maxGlueData hinj).ι_φ i j ⟨x, hx⟩).symm

/-- The copies of `M₀` are identified: `ι i ∘ ι_i = ι j ∘ ι_j`. -/
theorem maxι_emb (i j : SmallDev 𝔊.toPreGeometry s₀) (a : M₀) :
    (maxGlueData hinj).ι i (i.toDev.emb a) = (maxGlueData hinj).ι j (j.toDev.emb a) :=
  (maxι_eq hinj ((isCGHD_mcghd (N₁ := i.toDev) (N₂ := j.toDev)).1.1
    (i.toDev.emb_mem_range a))).trans
    (congrArg _ (congrFun (isCGHD_mcghd (N₁ := i.toDev) (N₂ := j.toDev)).2.2 a))

/-- **`M̃` is Hausdorff** (Sbierski, proof of Thm 2.8, step 1): every pair gluing is the gluing of
two developments along their MCGHD, Hausdorff by Sbierski Thm 3.13 (`t2Space_gluing_mcghd`,
package 6), and the family gluing is Hausdorff iff its pair gluings are
(`FamilyGlueData.t2Space_iff`, package 8). -/
theorem maxSpace_t2 : T2Space (MaxSpace hinj) :=
  (FamilyGlueData.t2Space_iff _).2 fun i j => t2Space_gluing_mcghd (N₁ := i.toDev) (N₂ := j.toDev)

/-- `M̃` is connected: the union of the connected `ι i (M i)`, all containing the image of `M₀`. -/
theorem maxSpace_connected (i₀ : SmallDev 𝔊.toPreGeometry s₀) :
    ConnectedSpace (MaxSpace hinj) := by
  obtain ⟨a₀⟩ := (inferInstance : Nonempty M₀)
  rw [connectedSpace_iff_univ, ← (maxGlueData hinj).iUnion_range_ι]
  exact ⟨⟨_, mem_iUnion.2 ⟨i₀, mem_range_self (i₀.toDev.emb a₀)⟩⟩,
    isPreconnected_iUnion ⟨(maxGlueData hinj).ι i₀ (i₀.toDev.emb a₀),
      mem_iInter.2 fun i => ⟨i.toDev.emb a₀, maxι_emb hinj i i₀ a₀⟩⟩
      fun i => isPreconnected_range ((maxGlueData hinj).continuous_ι i)⟩

/-- **`M̃` carries a structure for which every `ι i` is a morphism** (`Geometry.glue`; Sbierski,
proof of Thm 2.8, steps 2–3, « exactly as in the proof of Theorem 2.7 »). -/
theorem exists_maxStr : ∃ t : 𝔊.Str (MaxSpace hinj),
    ∀ i : SmallDev 𝔊.toPreGeometry s₀, 𝔊.IsMor i.toDev.str t ⊤ ((maxGlueData hinj).ι i) :=
  𝔊.glue (Z := MaxSpace hinj) (fun i : SmallDev 𝔊.toPreGeometry s₀ => i.Carrier)
    (fun i => i.toDev.str) (maxGlueData hinj).ι (maxGlueData hinj).isOpenEmbedding_ι
    (fun z => by
      obtain ⟨i, x, hx⟩ := (maxGlueData hinj).exists_ι z
      exact ⟨i, x, hx⟩)
    (fun i j => ⟨mcghdMap i.toDev j.toDev,
      𝔊.isMor_mono (isCGHD_mcghd (N₁ := i.toDev) (N₂ := j.toDev)).2.1
        (fun _ hx => (maxι_mem_O_iff hinj).1 hx),
      fun _ hx => (maxι_eq hinj ((maxι_mem_O_iff hinj).1 hx)).symm⟩)

/-- The structure of `M̃` (a choice; universality makes the result independent of it up to
unique isomorphism). -/
noncomputable def maxStr : 𝔊.Str (MaxSpace hinj) := Classical.choose (exists_maxStr hinj)

theorem isMor_maxι (i : SmallDev 𝔊.toPreGeometry s₀) :
    𝔊.IsMor i.toDev.str (maxStr hinj) ⊤ ((maxGlueData hinj).ι i) :=
  Classical.choose_spec (exists_maxStr hinj) i

/-- `ι i : M i → M̃` is a chart of the piece `ι i (M i)`. -/
theorem maxChart (i : SmallDev 𝔊.toPreGeometry s₀) :
    Causality.PieceChart (𝔊.causality (maxStr hinj)) ((maxGlueData hinj).O i)
      (𝔊.causality i.toDev.str) ((maxGlueData hinj).ι i) :=
  pieceChart_of_isMor (isMor_maxι hinj i) ((maxGlueData hinj).injective_ι i) _ rfl

/-- **The common Cauchy surface** `ι̃(Σ)` (Sbierski: « `ι̃ := π ∘ j_i ∘ ι_i` for some `α_i`.
This definition does obviously not depend on `α_i` », `maxCauchy_eq`). -/
def maxCauchy (i₀ : SmallDev 𝔊.toPreGeometry s₀) (S : Set M₀) : Set (MaxSpace hinj) :=
  (maxGlueData hinj).ι i₀ '' (i₀.toDev.emb '' S)

theorem maxCauchy_eq (i₀ i : SmallDev 𝔊.toPreGeometry s₀) (S : Set M₀) :
    (maxGlueData hinj).ι i '' (i.toDev.emb '' S) = maxCauchy hinj i₀ S := by
  rw [maxCauchy, ← image_comp, ← image_comp]
  congr 1
  funext a
  exact maxι_emb hinj i i₀ a

variable {S : Set M₀} (hS : (𝔊.causality s₀).IsCauchySurface S)
include hS

/-- **`M̃` is a many-piece spacetime** (`Causality.ManyPiece`): absolutely minimal (A), the overlaps
`ι i (U i j)` causally convex in each piece (`convex_mcghdOpens`), the relations agreeing there
(`mcghd_le_iff`), the Cauchy sides of the `ι_i(Σ)` read through the charts. -/
theorem maxManyPiece (i₀ : SmallDev 𝔊.toPreGeometry s₀) :
    (𝔊.causality (maxStr hinj)).ManyPiece (maxGlueData hinj).O (maxCauchy hinj i₀ S) := by
  refine Causality.manyPiece_of_charts (C := fun i => 𝔊.causality i.toDev.str)
    (fun z => (maxGlueData hinj).mem_O z) (𝔊.absolutelyMinimalOn _ ⊤) ?_ ?_ (maxChart hinj)
    (T := fun i => i.toDev.emb '' S)
    (fun i => i.toDev.cauchySide (i.toDev.isCauchyEmbedding.isCauchySurface_image hS))
    (fun i => maxCauchy_eq hinj i₀ i S)
  · intro i j x y z hx hz hxy hyz
    have c := maxChart hinj i
    obtain ⟨a, rfl⟩ := c.exists_eq ((𝔊.causality (maxStr hinj)).le_mem_left hxy)
    obtain ⟨b, rfl⟩ := c.exists_eq ((𝔊.causality (maxStr hinj)).le_mem_right hxy)
    obtain ⟨c', rfl⟩ := c.exists_eq ((𝔊.causality (maxStr hinj)).le_mem_right hyz)
    exact (maxι_mem_O_iff hinj).2 ((convex_mcghdOpens (N₁ := i.toDev) (N₂ := j.toDev)).2 a
      ((maxι_mem_O_iff hinj).1 hx) c' ((maxι_mem_O_iff hinj).1 hz)
      (Causality.mem_diamond.2 ⟨(c.le_iff a b).1 hxy, (c.le_iff b c').1 hyz⟩))
  · intro i j x y hxi hxj hyi hyj
    obtain ⟨u, rfl⟩ := (maxChart hinj i).exists_eq hxi
    obtain ⟨u', rfl⟩ := (maxChart hinj i).exists_eq hyi
    have hu := (maxι_mem_O_iff hinj).1 hxj
    have hu' := (maxι_mem_O_iff hinj).1 hyj
    rw [(maxChart hinj i).le_iff, mcghd_le_iff (hinj _ _) hu hu', maxι_eq hinj hu,
      maxι_eq hinj hu', (maxChart hinj j).le_iff]

/-- **`M̃` is globally hyperbolic — proved FIRST, before its second countability, and without
`curvesExtend` or `isCompact_*` on `M̃`** (the package-10 risk of design §6): causal convexity of
every piece in `M̃` (`ManyPiece.mem_of_le_top`, the chain-wise exit/re-entry argument), compact
diamonds inside a piece by the chart, across two pieces by `ManyPiece.isCompact_diamond_mixed`.
A2 is used on the developments `M i` only (their `CauchySide`). -/
theorem maxStr_globallyHyperbolic (i₀ : SmallDev 𝔊.toPreGeometry s₀) :
    (𝔊.causality (maxStr hinj)).GloballyHyperbolic :=
  (maxManyPiece hinj hS i₀).globallyHyperbolic (Xs := fun i => i.Carrier) (maxChart hinj)
    (fun i => i.toDev.causality_globallyHyperbolic)
    (fun i => i.toDev.cauchySide (i.toDev.isCauchyEmbedding.isCauchySurface_image hS))
    (fun i => maxCauchy_eq hinj i₀ i S)

/-- **`ι̃(Σ)` is a Cauchy surface of `M̃`** (Sbierski, proof of Thm 2.8, step 4). -/
theorem maxStr_isCauchySurface (i₀ : SmallDev 𝔊.toPreGeometry s₀) :
    (𝔊.causality (maxStr hinj)).IsCauchySurface (maxCauchy hinj i₀ S) := by
  haveI := maxSpace_t2 hinj
  refine (maxManyPiece hinj hS i₀).isCauchySurface (maxStr_globallyHyperbolic hinj hS i₀).1
    (fun i => ?_) (i₀ := i₀) ?_
  · have hE := 𝔊.isEMorphismOn_of_isMor (isMor_maxι hinj i)
    have := (hE.isCauchySurfaceOn_image_iff ((maxGlueData hinj).injective_ι i).injOn le_rfl
      (U := (maxGlueData hinj).O i) (by rw [Opens.coe_top, image_univ]; rfl)
      (subset_univ _)).1 (i.toDev.isCauchyEmbedding.isCauchySurface_image hS)
    rwa [maxCauchy_eq hinj i₀ i S] at this
  · have hac := (i₀.toDev.isCauchyEmbedding.isCauchySurface_image hS).isAcausal
      i₀.toDev.causality_causallyArcConnected i₀.toDev.causality_curvesExtend
    rintro _ ⟨y, hy, rfl⟩ _ ⟨y', hy', rfl⟩ hle
    exact congrArg _ (hac y hy y' hy' (((maxChart hinj i₀).le_iff y y').1 hle))

omit hS in
/-- The embedding `ι i₀ ∘ ι_{i₀} : M₀ → M̃` is a structure morphism. -/
theorem isMor_maxEmb (i₀ : SmallDev 𝔊.toPreGeometry s₀) :
    𝔊.IsMor s₀ (maxStr hinj) ⊤ ((maxGlueData hinj).ι i₀ ∘ i₀.toDev.emb) :=
  𝔊.isMor_comp (isMor_maxι hinj i₀) i₀.toDev.isMor fun _ _ => trivial

/-- **`M̃` is second countable** (Sbierski, proof of Thm 2.8, step 5, « a Theorem of Geroch »):
by the interface's `secondCountable_of_cauchy`, applied AFTER global hyperbolicity
(`maxStr_globallyHyperbolic`) and the Cauchy surface (`maxStr_isCauchySurface`); `ι̃(Σ)` is
homeomorphic to `Σ ⊆ M₀`, second countable. -/
theorem maxSpace_secondCountable [SecondCountableTopology M₀] (i₀ : SmallDev 𝔊.toPreGeometry s₀) :
    SecondCountableTopology (MaxSpace hinj) := by
  haveI := maxSpace_t2 hinj
  haveI := maxSpace_connected hinj i₀
  refine 𝔊.secondCountable_of_cauchy (maxStr hinj) (maxStr_globallyHyperbolic hinj hS i₀) _
    (maxStr_isCauchySurface hinj hS i₀) ?_
  have hE := 𝔊.isEMorphismOn_of_isMor (isMor_maxEmb hinj i₀)
  have hcont : Continuous ((maxGlueData hinj).ι i₀ ∘ i₀.toDev.emb) := by
    have := hE.continuousOn; rwa [Opens.coe_top, continuousOn_univ] at this
  have hF : IsEmbedding ((maxGlueData hinj).ι i₀ ∘ i₀.toDev.emb) :=
    (IsOpenEmbedding.of_continuous_injective_isOpenMap hcont
      (((maxGlueData hinj).injective_ι i₀).comp i₀.toDev.isCauchyEmbedding.injective)
      fun V hV => hE.isOpen_image ⟨V, hV⟩ le_top).isEmbedding
  have := (hF.homeomorphImage S).symm.secondCountableTopology
  rw [maxCauchy, ← image_comp]
  exact this

/-- **The maximal development** `M̃`, as a development of `M₀` (Sbierski Thm 2.8): Hausdorff,
connected, second countable, globally hyperbolic, `M₀` Cauchy-embedded through `i₀`. -/
noncomputable def maxDev [SecondCountableTopology M₀] (i₀ : SmallDev 𝔊.toPreGeometry s₀) :
    Dev 𝔊.toPreGeometry s₀ where
  carrier := MaxSpace hinj
  t2 := maxSpace_t2 hinj
  conn := maxSpace_connected hinj i₀
  sc := maxSpace_secondCountable hinj hS i₀
  str := maxStr hinj
  emb := (maxGlueData hinj).ι i₀ ∘ i₀.toDev.emb
  isCauchyEmbedding :=
    ⟨i₀.toDev.isCauchyEmbedding.globallyHyperbolic_source, maxStr_globallyHyperbolic hinj hS i₀,
      𝔊.isEMorphismOn_of_isMor (isMor_maxEmb hinj i₀),
      ((maxGlueData hinj).injective_ι i₀).comp i₀.toDev.isCauchyEmbedding.injective,
      S, hS, by rw [image_comp]; exact maxStr_isCauchySurface hinj hS i₀⟩
  isMor := isMor_maxEmb hinj i₀

/-- Every small development maps into `M̃` by its inclusion (Sbierski, step 6, for the members
of `X`). -/
theorem maxDev_isMorphism [SecondCountableTopology M₀] (i₀ N : SmallDev 𝔊.toPreGeometry s₀) :
    N.toDev.IsMorphism (maxDev hinj hS i₀) ((maxGlueData hinj).ι N) :=
  ⟨isMor_maxι hinj N, funext fun a => maxι_emb hinj N i₀ a⟩

/-- **Universality of `M̃`** (DEC-59; Sbierski Thm 2.8, step 6): every development maps uniquely
into `M̃` — a small one by its inclusion (uniquely: rigidity A1 on the connected carrier, into the
Hausdorff `M̃`, agreeing on the image of `M₀`), any one through its small copy
(`Dev.isUniversal_of_small`, package 9). -/
theorem maxDev_isUniversal [SecondCountableTopology M₀] (i₀ : SmallDev 𝔊.toPreGeometry s₀) :
    (maxDev hinj hS i₀).IsUniversal := by
  refine Dev.isUniversal_of_small fun N => ⟨_, maxDev_isMorphism hinj hS i₀ N, fun g hg => ?_⟩
  haveI := maxSpace_t2 hinj
  have hV : IsConnected ((⊤ : Opens N.toDev.carrier) : Set N.toDev.carrier) := by
    rw [Opens.coe_top]; exact isConnected_univ
  have hO : (N.toDev.isCauchyEmbedding.rangeOpens : Set N.toDev.carrier).Nonempty :=
    ⟨N.toDev.emb (Classical.arbitrary M₀), N.toDev.emb_mem_range _⟩
  have heq : EqOn g ((maxGlueData hinj).ι N) N.toDev.isCauchyEmbedding.rangeOpens := by
    intro y hy
    rw [IsCauchyEmbedding.coe_rangeOpens] at hy
    obtain ⟨a, rfl⟩ := hy
    exact (congrFun hg.2 a).trans (congrFun (maxDev_isMorphism hinj hS i₀ N).2 a).symm
  funext z
  exact 𝔊.rigid N.toDev.str (maxStr hinj) ⊤ hV g _ hg.1 (isMor_maxι hinj N) _ le_top hO heq
    (show z ∈ (⊤ : Opens N.toDev.carrier) from trivial)

end MaxGluing

/-! ### The principal theorem and the ETT corollaries -/

section Principal

variable {𝔊 : Geometry.{u}} {M₀ : Type u} [TopologicalSpace M₀]

/-- **The time-function field of interface round 2 (design §6), as a predicate on a geometry**:
every admissible globally hyperbolic spacetime (T2, connected, second countable) carries a
continuous function strictly increasing along `≤` (`Causality.HasTimeFunction`, `CBG/Pgcd`).
Every geometry satisfies it: the field `Geometry.timeFunction` is a proof,
`𝔊.timeFunction : 𝔊.HasTimeFunctions` (definitional unfolding). Kept because `Flat/CBG` names
it (`flatGeometryOf_hasTimeFunctions`, and the redundant hypothesis of `cbg_of_hasTimeFunctions`). Flat: `Flat/GerochFlat`; `E₀`:
`SingularGeroch`. -/
def Geometry.HasTimeFunctions (𝔊 : Geometry.{u}) : Prop :=
  ∀ {M : Type u} [TopologicalSpace M] [T2Space M] [ConnectedSpace M] [SecondCountableTopology M]
    (s : 𝔊.Str M), (𝔊.causality s).GloballyHyperbolic → (𝔊.causality s).HasTimeFunction

/-- **CBG, universal form, given injective MCGHD morphisms** (sorry-free): the gluing of all small
developments along their pairwise MCGHDs is a universal development. -/
theorem cbg_of_mcghdInjective [T2Space M₀] [ConnectedSpace M₀] [SecondCountableTopology M₀]
    (s₀ : 𝔊.Str M₀) (hGH : (𝔊.causality s₀).GloballyHyperbolic) {S : Set M₀}
    (hS : (𝔊.causality s₀).IsCauchySurface S) (hinj : MCGHDInjective 𝔊 s₀) :
    ∃ Mbar : Dev 𝔊.toPreGeometry s₀, Mbar.IsUniversal :=
  ⟨maxDev hinj hS (SmallDev.ofDev (Dev.self 𝔊 s₀ hGH hS)), maxDev_isUniversal hinj hS _⟩

/-- **CBG — the principal theorem** (`theo:CBG`, `ETT.tex:1884`, universal reading DEC-59,
framework DEC-60; Sbierski Thm 2.8): a globally hyperbolic admissible `M₀` (T2, connected, second
countable) with a Cauchy surface has a **universal** Cauchy development — every development maps
into it by a unique morphism of developments. Sorry-free: the gluing of all small developments
(`cbg_of_mcghdInjective`), its MCGHD morphisms injective by Lemma 3.3 from the interface field
`Geometry.timeFunction` (round 2; `mcghdInjective`). -/
theorem cbg [T2Space M₀] [ConnectedSpace M₀] [SecondCountableTopology M₀]
    (s₀ : 𝔊.Str M₀)
    (hGH : (𝔊.causality s₀).GloballyHyperbolic) {S : Set M₀}
    (hS : (𝔊.causality s₀).IsCauchySurface S) :
    ∃ Mbar : Dev 𝔊.toPreGeometry s₀, Mbar.IsUniversal :=
  cbg_of_mcghdInjective s₀ hGH hS (mcghdInjective 𝔊 s₀)

/-- **CBG under the time-function predicate** — `cbg` with a now-redundant hypothesis (every
geometry satisfies `Geometry.HasTimeFunctions`, `𝔊.timeFunction` being a proof), kept with its
pre-round-2 signature because `Flat/CBG`'s `flat_cbg_of` calls it. Sorry-free. -/
theorem cbg_of_hasTimeFunctions [T2Space M₀] [ConnectedSpace M₀] [SecondCountableTopology M₀]
    (s₀ : 𝔊.Str M₀) (hGH : (𝔊.causality s₀).GloballyHyperbolic) {S : Set M₀}
    (hS : (𝔊.causality s₀).IsCauchySurface S) (_hT : 𝔊.HasTimeFunctions) :
    ∃ Mbar : Dev 𝔊.toPreGeometry s₀, Mbar.IsUniversal :=
  cbg s₀ hGH hS

/-- **Uniqueness up to unique isomorphism** (Sbierski Thm 2.8, « unique up to isometry »;
`theo:CBG`, « unique up to isomorphism »; DEC-59): between two universal developments there is
exactly one morphism, and it is an isomorphism of developments. No rigidity, no `cbg`. -/
theorem Dev.IsUniversal.existsUnique_iso {s₀ : 𝔊.Str M₀} {M₁ M₂ : Dev 𝔊.toPreGeometry s₀}
    (h₁ : M₁.IsUniversal) (h₂ : M₂.IsUniversal) :
    ∃! f : M₁.carrier → M₂.carrier, M₁.IsMorphism M₂ f ∧
      ∃ g : M₂.carrier → M₁.carrier, M₂.IsMorphism M₁ g ∧ g ∘ f = id ∧ f ∘ g = id := by
  obtain ⟨f, g, hf, hg, hgf, hfg⟩ := h₁.unique h₂
  refine ⟨f, ⟨hf, g, hg, hgf, hfg⟩, fun f' hf' => ?_⟩
  obtain ⟨k, -, hk⟩ := h₂ M₁
  rw [hk _ hf'.1, hk _ hf]

/-- **The ETT/Barbot reading** of `theo:CBG` (DEC-59, kb/0022; sorry-free): an ETT-maximal
development exists (every morphism out of it is bijective), and any ETT-maximal development is
isomorphic to it by a unique morphism of developments. From `cbg`. -/
theorem cbg_ett [T2Space M₀] [ConnectedSpace M₀] [SecondCountableTopology M₀]
    (s₀ : 𝔊.Str M₀) (hGH : (𝔊.causality s₀).GloballyHyperbolic) {S : Set M₀}
    (hS : (𝔊.causality s₀).IsCauchySurface S) :
    ∃ Mbar : Dev 𝔊.toPreGeometry s₀, Mbar.IsETTMaximal ∧
      ∀ M : Dev 𝔊.toPreGeometry s₀, M.IsETTMaximal →
        ∃! f : Mbar.carrier → M.carrier, Mbar.IsMorphism M f ∧
          ∃ g : M.carrier → Mbar.carrier, M.IsMorphism Mbar g ∧ g ∘ f = id ∧ f ∘ g = id := by
  obtain ⟨Mbar, hU⟩ := cbg s₀ hGH hS
  exact ⟨Mbar, hU.isETTMaximal, fun M hM => hU.existsUnique_iso (hM.isUniversal hU)⟩

/-- **An ETT-maximal development exists** (`theo:CBG`, existence half, ETT/Barbot reading;
sorry-free), from `cbg` (`Dev.IsUniversal.isETTMaximal`). -/
theorem cbg_isETTMaximal [T2Space M₀] [ConnectedSpace M₀] [SecondCountableTopology M₀]
    (s₀ : 𝔊.Str M₀)
    (hGH : (𝔊.causality s₀).GloballyHyperbolic) {S : Set M₀}
    (hS : (𝔊.causality s₀).IsCauchySurface S) :
    ∃ Mbar : Dev 𝔊.toPreGeometry s₀, Mbar.IsETTMaximal :=
  (cbg s₀ hGH hS).imp fun _ h => h.isETTMaximal

/-- **The two readings of « maximal » agree** (DEC-59; sorry-free): a development is
ETT-maximal iff it is universal, given that a universal one exists (`cbg`). -/
theorem isETTMaximal_iff_isUniversal [T2Space M₀] [ConnectedSpace M₀]
    [SecondCountableTopology M₀] (s₀ : 𝔊.Str M₀) (hGH : (𝔊.causality s₀).GloballyHyperbolic)
    {S : Set M₀}
    (hS : (𝔊.causality s₀).IsCauchySurface S) (M : Dev 𝔊.toPreGeometry s₀) :
    M.IsETTMaximal ↔ M.IsUniversal := by
  obtain ⟨Mbar, hU⟩ := cbg s₀ hGH hS
  exact ⟨fun h => h.isUniversal hU, fun h => h.isETTMaximal⟩

end Principal

end CBG

end Causal
