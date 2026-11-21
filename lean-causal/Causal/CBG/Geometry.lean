import Causal.SubExtension
import Causal.CompactCauchy
import Causal.PushoutCausal
import Causal.SingularFlat
import Causal.GXStructure
import Mathlib.Geometry.Manifold.LocalInvariantProperties
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-!
# The geometry interface of the CBG campaign: Level A, Level B, developments

Package WP-36a-CBGGeometry, design `docs/CBG-DESIGN.md` §1–§2 (the interface, **gated**: reviewed by
the gx session before any package builds on it). No paper label is marked. Cited, unmarked:
`theo:CBG` — `ETT.tex:1884`, `rem:CBG_analytique` — `ETT.tex:1903`, `rem:CBG_manquant` —
`ETT.tex:2343`, `def:common_sub_extension` — `ETT.tex:1914`; thesis `theo:Cauchy_ext`
(`these.tex:6287`), `prop:GX_liouville` (`these.tex:1476`), `prop:isom` (`these.tex:4332`);
Sbierski 1309.7591, Thm 2.8, Lemma 3.8, Thm 3.6.

Framework (DEC-60): Brunswic's thesis, **rigid morphisms of singular `(G,X)`-manifolds**:

> Un $X_A$-morphisme est une application $f:M\rightarrow N$ telle que pour tout $x\in \sing(M)$, il
> existe une carte $(\U_1,Y_1,\V_1,\phi_1)$ de $\A$ au voisinage de $x$, et une carte
> $(\U_2,Y_2,\V_2,\phi_2)$ au voisinage de $f(x)$ telles que pour tout ouvert connexe
> $\W\subset \U_1\cap f^{-1}(\U_2)$, on ait : (i) $Y_1=Y_2=Y$ ; (ii) il existe $g\in G_Y$ tel que
> $f_{|\W}= \phi_2^{-1}\circ g\circ \phi_{1|\W}$ (`these.tex:3173–3186`)

> Un $(G,X,X_A)$-atlas […] tel que $Y_i\in \{X_\alpha\}\cup\{X\}$ […] et
> $\phi_{j}\circ (\phi_{i|\U_i\cap\U_j})^{-1}$ est un $(G,X)$-morphisme presque partout.
> (`these.tex:3040–3053`)

> Soient $(M_1,\A), (M_2,\B)$ deux $(G,X)$-variétés […] Si $M_1$ est connexe et s'il existe un
> ouvert non vide $\U$ de $M_1$ tel que ${f_1}_{|\U}={f_2}_{|\U}$ alors $f_1=f_2$.
> (`prop:GX_liouville`, `these.tex:1476–1480`; a $(G,X)$-variété is « séparé à base dénombrable »,
> `these.tex:1357–1359`)

> La structure $(\isom(\mass{}),\mass{},\mass{\geq0})$ est analytique. (`prop:isom`,
> `these.tex:4332–4334`) — $Y$ analytique: « pour tout ouvert connexe $\U$ voisinage d'un point
> singulier, tout $(G,X)$-morphisme $f: \reg(\U)\rightarrow \reg(Y)$ est la restriction d'un
> automorphisme de $Y$ » (`these.tex:3335–3340`); « L'hypothèse d'injectivité est alors
> nécessaire » (`these.tex:4426`).

> Un Cauchy-plongement de $M$ dans $N$ est un $\mass{A}$-morphisme injectif tel que l'image d'une
> surface de Cauchy de $M$ est une surface de Cauchy de $N$. (`these.tex:6246–6248`)
> Il existe une extension de Cauchy de $M$ maximale, cette extension est de plus unique à
> isomorphisme près. (`theo:Cauchy_ext`, `these.tex:6287–6291`)

> Theorem 2.8 (Existence of MGHD). Given initial data there exists a GHD $\tilde M$ that is an
> extension of any other GHD of the same initial data. (Sbierski, p. 12)

> Definition 3.5. […] Two points $p\in\partial U\subseteq M$ and $p'\in\partial\psi(U)\subseteq M'$ are
> called corresponding boundary points of $U$ iff for all neighbourhoods $V$ of $p$ and for all
> neighbourhoods $V'$ of $p'$ one has $\psi^{-1}(V'\cap\psi(U))\cap V\neq\emptyset$. (Sbierski, p. 15)

## Hypothesis checklist

| thesis / Sbierski | here |
|---|---|
| `X_A`-morphism (`these.tex:3173–3186`) | Level A: `IsMor`, abstract, sheaf laws; Level B: `LocalModel.IsMor` = `LiftPropOn G.IsLocalStructomorphWithinAt` (local form, every `x ∈ M`) |
| « pour tout $x\in\sing(M)$ » (`these.tex:3176`) | ✓ **gx DEC-63** (2026-11-01): the condition holds **at every** singular point; here it is asked at every `x ∈ M`, the regular points adding nothing (`Y = X` there, `these.tex:3043`; the equivalence `these.tex:3398–3407`) |
| one `g ∈ G_Y` on every connected `W` (`these.tex:3177–3182`) | ✓ **gx DEC-62** (2026-11-01): `X_A`-morphisms are taken in the **local** form (locally isomorphisms onto open subsets of the models), matching gx's a.e. morphisms (DEC-25) and `def:atlas` (l.1905); the one-`g` form follows on injective maps by B1 + B2 (`localUnique_sing`, `localUnique_reg`) |
| `X_A`-atlas, transitions a.e. `(G,X)` (`these.tex:3040–3053`) | ⚠ reading: `HasGroupoid M G` (transitions in `G`); equivalent for an analytic family (`these.tex:3398–3407`) |
| analyticity of `(G,X)`, `prop:GX_liouville` (rigidity) | ✓ `Geometry.rigid` (A1), target `T2` (branching line), `LocalModel.rigid` (B1) + `locallyConnected` |
| analytic model `def:analytique` (`these.tex:3335–3340`), `prop:isom` (injective) | ✓ `LocalModel.localUnique_sing` (B2 at a singular point: `f : reg(U) → reg(Y)` into the **same** model, the component of `y₀`; one element of `G` on that component, « automorphisme de $Y$ »), injectivity carried |
| famille analytique (b), `def:incompatibles` (`these.tex:3328–3332`, `3346–3353`) | ⚠ reading: carried as the `MapsTo` hypotheses of B2 (same model / fully regular target); derived at the instance (package 11) |
| Liouville on the regular part (`prop:GX_liouville`) | ⚠ added: `LocalModel.localUnique_reg` (B2 on a fully regular component, values in a fully regular component) + `regularChart` — not a thesis definition; true for gx's `𝕄 ⊕ Σ_α 𝔼_α` and for `Minkowski d` |
| manifolds Hausdorff, connected (`these.tex:1357`, `5729`) | ✓ `Dev` carriers `T2Space`, `ConnectedSpace` |
| second countable (`these.tex:1357`, `rem:CBG_manquant` (i)) | ✓ carried (gx review C2): `Dev` carriers `SecondCountableTopology`; the A2/B3 fields assume it, and since interface round 3 so do A3 (`germExt_*`: `M` and `N`) and A4 (`slice_*`: `M`); ⚠ added obligation `secondCountable_of_cauchy` (GH + SC Cauchy surface ⇒ SC), for `M̄` (package 10) |
| `defi:causal_E0`: $I^+(p)=J^+(p)\setminus\sing_0$ (`ETT.tex:1352–1355`) | ✗ **false in `E₀`** (gx review C1, radial null ray): corrected in the strict library (DEC-64), `BTZAxioms.Iplus_of_lt`; A2/B3 ask the library's `SingularFlatAxioms`; `K_monotone`, `K_densite_sing`, `K_ordre` proved there from it — finding |
| `CurvesExtend` | ⚠ restricted (gx review C3): on globally hyperbolic `M` only, the only use (§3.1 on developments) |
| `M₀` globally hyperbolic (`theo:CBG`, `ETT.tex:1885`; `theo:Cauchy_ext`, `these.tex:6288`) | ⚠ strengthened: `cbg` (stated and proved in `CBG/Maximal`) also assumes a Cauchy surface `S` (the library's `GloballyHyperbolic`, `Causal/Properties.lean:144`, is causal + compact diamonds and gives none; without one no `Dev` exists); recoverable at the singular flat instance via `theo:geroch_sing` (`ETT.tex:1771`, DEC-18), never for an abstract `Geometry` |
| Sbierski Lemma 3.8 (extension at corresponding points, Def 3.5) | A3 `germExt_future`/`germExt_past`: `MapClusterPt q (𝓝[U] p) ψ` is Def 3.5 |
| "maximal" | DEC-59: `Dev.IsUniversal` (Sbierski); `Dev.IsETTMaximal` the ETT form, equivalent given `cbg` (`CBG/Maximal`) |
| Sbierski Lemma 3.3 (`ψ` injective; « time function » on each GHD) | ✓ round 2 (1): `Geometry.timeFunction` (A2), `LocalModel.timeFunction` (B3): every GH admissible spacetime has a continuous function strictly increasing along `≤` (the body of `Causality.HasTimeFunction`, `Causal.CurvesExtend`); discharges the `hT` of `Pgcd`, `NoCorresponding`, `Ppcm` and `Geometry.HasTimeFunctions` of `Maximal` |
| `cor:model_corresponding` (`ETT.tex:2158`), type of corresponding points | ⚠ added, read on `Y` (round 4 (3), gx-agreed): `LocalModel.typeAgreement`, at non-BTZ `y₀`, for pieces containing a chronological diamond with tip `y₀` |
| B4 slices (Sbierski (3.12), Lemma 3.11) | ⚠ replaced (round 4 (2), gx-agreed): cone-slice forms `coneSliceFuture` (off `sing₀`), `coneSlicePast` (everywhere); the level-set B4 is deleted |
| model Hausdorff; singular loci closed | ✓ round 4 (1), (4): `[t2Y : T2Space Y]`, `isOpen_regY`; `dense_regY` (added by the round-4 author, accepted by gx 2026-11-02) |
| past side at a BTZ point (gx, `A3-B-INVESTIGATION.md`; the thesis never treats it) | ⚠ added, gx's form: `LocalModel.localUnique_sing_adherent`, largeness clause in the **diamond form with a regular tip** (interface round 3, 2026-11-02; round 2's clause was vacuous at `α₀ = 0`, SCOPE) |

## SCOPE (disclosed)

* **`cbg` and its corollaries are not in this file.** The principal theorem `cbg` (universal
  form), `cbg_isETTMaximal` and `isETTMaximal_iff_isUniversal` are **stated and proved in
  `CBG/Maximal`** (which imports this file, so they cannot be proved here); their sorried
  placeholders were deleted on 2026-11-01 (interface round 2). This file keeps the definitions
  (`Dev`, `Dev.IsMorphism`, `Dev.IsUniversal`, `Dev.IsETTMaximal`, `Dev.self`) and the facts that
  need no `cbg`: `Dev.IsUniversal.unique`, `Dev.IsUniversal.isETTMaximal`,
  `Dev.IsETTMaximal.isUniversal`, proved outright. The file is sorry-free.
* **Interface round 2 (design §6, gx 2026-11-01), applied.** (1) `Geometry.timeFunction` and its
  Level-B counterpart `LocalModel.timeFunction`: GH admissible (T2, connected, SC) ⇒ a continuous
  `T` strictly increasing along `≤`. Stated with the body of `Causality.HasTimeFunction` written
  out, because that definition lived in `CBG/Pgcd`, downstream (it is in `Causal.CurvesExtend`, upstream,
  since T-abs-hoist-time-function); the two are definitionally equal,
  so `𝔊.timeFunction s hGH` is a `(𝔊.causality s).HasTimeFunction` and
  `fun s hGH => 𝔊.timeFunction s hGH` a `𝔊.HasTimeFunctions` (`CBG/Maximal`) as they stand.
  (2) `LocalModel.localUnique_sing_adherent`, the past-side B2 step in gx's form. **Finding
  (round 2; resolved by round 3, next bullet)
  (from `CBG/FromModel`'s `BTZAxioms.exists_le_inter_Iminus_subset`)**: at a BTZ point
  (`α₀ = 0`) of a model where BTZ points have empty chronological past (`E₀`), its largeness clause
  holds for every `U` (`r := y₀`), so there the field is the point-contact form, which the cone
  counterexample refutes in `E₀`; the wrap-around reading needs `r` regular (candidate repair: the
  conjunct `r ∈ regY`). Transcribed as agreed then; amended by gx in round 3.
  **Interface round 3 (design §6, agreed with gx 2026-11-02), applied.** (A) the largeness clause
  of `localUnique_sing_adherent` is now the **diamond form with a regular tip**,
  `∃ O ∋ y₀, ∃ r ∈ O, r ∈ reg ∧ y₀ ≪_O r ∧ reg ∩ I⁺_O(y₀) ∩ I⁻_O(r) ⊆ U` (the vacuity above is
  gone: `r ∈ reg` excludes `r := y₀` and the line); the piece A3-past produces meets it
  (`CBG/FromModel`, `diamond_clause_of_piece`). (B) `[SecondCountableTopology M]`
  `[SecondCountableTopology N]` on `germExt_future`/`germExt_past`, `[SecondCountableTopology M]`
  on `slice_future`/`slice_past` (and on `CBG/FromModel`'s `GermExtFuture`, … copies), so that A3/A4
  are derivable from the B3 facts, which all assume it; consumers had it in scope
  (`CGHDData.ext_continue` now asks it of `N`).
  Level B → Level A (`Geometry.ofLocalModelOfBTZ`, `CBG/FromModel`) is package 11. A3 (`germExt_*`) and A4 (`slice_*`)
  are stated in the CGHD setting of Sbierski Lemma 3.8 / Thm 3.6, in both time directions (no
  duality, gx D-12(e)). The thesis extends only under `J(Σ,p) ∖ {p} ⊂ N`
  (`prop:Cauchy_non_max`, `these.tex:6634–6640`); A3 asks it at every corresponding point.
* **Interface round 4 (design §6, gx-agreed 2026-11-02), applied to `LocalModel`.** (1)
  `[t2Y : T2Space Y]` (instance field). (2) The level-set B4 `slice_future`/`slice_past` of rounds
  1–3 is **deleted** and replaced by the cone-slice forms `coneSliceFuture` (off the BTZ locus) and
  `coneSlicePast` (everywhere), round 3's `ConeSliceFuture`/`ConeSlicePast` verbatim; the old B4
  had no consumer (`CBG/FromModel` derived A4 from the cone forms since round 3; its only
  inhabitants, `Flat/CBG`'s `minkowski_slice_future`/`_past`, stay as lemmas). (3)
  `typeAgreement`, on `Y`: for a connected open `U` containing a chronological diamond with tip
  `y₀ ∉ sing₀`, an injective local `G`-structomorphism on `U` clustering at `z₀` at `y₀` has
  `y₀ ∈ sing_α ↔ z₀ ∈ sing_α` (`α ≥ 0`) and, `y₀` singular, `z₀` in the component of `y₀`. (4)
  `isOpen_regY`. **Plus `dense_regY`, added by the round-4 author and accepted by gx (2026-11-02)**
  (the massive case of A3 needs regular points accumulating in the piece; see its docstring for
  why no agreed field gives it). With them `CBG/FromModel` derives A3 and A4 at every non-BTZ
  boundary point and is sorry-free; the BTZ-point cases are the explicit hypotheses of
  `Geometry.ofLocalModelOfBTZ`. The flat model (`Flat/CBG`'s `flatModelOf`) supplies all six.
* Witnesses, proved: in the causal pre-geometry (`causalPreGeometry`, morphisms `IsEMorphismOn`)
  the timelike half-line has **no universal development** (`kinkIso`), the line is not
  ETT-maximal (`arctanSelf`, a non-surjective Cauchy self-embedding) and rigidity fails
  (`timelikeLine_not_isRigid`); rigidity into the non-T2 branching line fails for every morphism
  predicate containing its two inclusions (`not_isRigidFor_branchingLine`). **Not formalized**:
  design §2's T2 witness proper (without T2 carriers the branching line IS a minimal
  over-extension, so `CommonSubExtension` / `CommonOverExtension` must ask T2) — only the weaker
  rigidity failure into a non-T2 target is proved; and the long ray (size bound; no long line in
  mathlib). In the ETT reading, only "the candidate `ℝ` is not ETT-maximal" is proved; that no
  ETT-maximal development exists (or that uniqueness fails) is **not** proved.
* `Geometry` and `LocalModel` have **no inhabitant in this file** (kb/0011, kb/0012): their joint
  satisfiability is witnessed only by `CBG/FromModel` (package 11) and `Flat/CBG` (package 12).
  Before the gate closes, the flat `LocalModel` (`Y = Minkowski d`, `singY = ∅`, `G` the isometry
  groupoid, `regularChart := refl`) is to be checked field by field (gx or package 12).
* No field relates the causality of `restrict s W`, `transport e s` or the glued structure to the
  original causality. The intended derivation — `isMor_val` / `isMor_transport` / the glue
  embeddings, then `isEMorphismOn_of_isMor`, `absolutelyMinimalOn` and `LocalIsomorphism.unique` —
  is a **planned lemma** of package 4 (`Pgcd`, restrict) and package 7 (`Ppcm`, glue).
* `Dev` carriers are types (open subsets as subtypes, `restrict`): a development is an object.
* **gx review (`lean-gx/campaign/WP-28-scope/CBG-REVIEW.md`), changes applied.** C1: A2/B3 ask
  the corrected bundle (the former `Iplus_eq` is false in `E₀`), since DEC-64 the strict library's
  own `SingularFlatAxioms` (field `Iplus_of_lt`; the file's former copy `SingularFlatAxiomsCorr`
  is deleted); C2: second countability a hypothesis (`Dev.sc`, binders on A2/B3) plus the field
  `secondCountable_of_cauchy`; C3: `curvesExtend` on GH `M`; C4: `localUnique_sing` kept strong.
  **Design §3 against C1**: the false implication reaches §3 only through the K± calculus —
  step 4 (Prop 3.7 = `lem:corresponding_K`, via `K_ordre`/`K_monotone`; Lemma 3.9 via the Geroch
  time, whose admissible measures `SingularGeroch.mesure_admissible` take `K_monotone`) and,
  through the Geroch time, C3's `curvesExtend_of_timeFunction` (step 1). `Iplus_of_lt` suffices
  for all three: `SingularFlatAxioms.K_monotone`, `.K_densite_sing`, `.K_ordre` are proved in
  the strict library from it (DEC-64), and `SingularGeroch.mesure_admissible` takes the corrected
  `K_monotone` as it stands. Steps 2, 3, 5, 6, 7 never used `Iplus_eq`.
* **Size bound (§3.6) consistency**: every `Dev` carrier is SC and T2, hence T0 and of cardinality
  `≤ 𝔠`, so it embeds in `Set ℕ` as the design's `SmallDev` needs; the glued `M̄` re-enters `Dev`
  by `secondCountable_of_cauchy` (its Cauchy surface is the image of `M₀`'s, SC as a subspace of
  the SC `M₀`). `cbg` (`CBG/Maximal`) and `Dev.self` ask `[SecondCountableTopology M₀]`, necessary: `M₀`
  embeds openly in any development.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set Topology Filter Function TopologicalSpace

universe u

/-! ### The singular flat bundle (gx review C1, DEC-64)

The corrected bundle this file used to carry (`BTZAxiomsCorr`, `SingularFlatAxiomsCorr`, the
library's with `Iplus_eq` replaced by `Iplus_of_lt`) **graduated into the strict library** under
DEC-64 (2026-11-02): `Causality.BTZAxioms` (`Causal/SingularFlat.lean`) now has the field
`Iplus_of_lt` (`p < p′` on the BTZ line ⇒ `J⁺(p′) ∖ sing₀ ⊆ I⁺(p)`) in place of the false
`Iplus_eq` (`I⁺(p) = J⁺(p) ∖ sing₀`, refuted in `E₀` by the radial null ray, see the library's
SCOPE), and `SingularFlatAxioms.K_monotone`, `.K_densite_sing`, `.K_ordre` are proved there from it
with their statements unchanged. A2/B3 ask the library bundle `SingularFlatAxioms` directly; the
corrected structures, their bridges `toCorr` and their duplicated `K` lemmas are deleted. -/

namespace CBG

/-! ### Rigidity relative to a morphism predicate -/

section Rigid

variable {M : Type*} {N : Type*} [TopologicalSpace M]

/-- **Rigidity for a morphism predicate** `P` (`P V f`: `f` is a morphism on the open `V`): two
morphisms on a connected open `V` agreeing on a non-empty open `O ⊆ V` agree on `V`
(`prop:GX_liouville`, `these.tex:1476`; Sbierski Cor 3.2). -/
def IsRigidFor (P : Opens M → (M → N) → Prop) : Prop :=
  ∀ V : Opens M, IsConnected (V : Set M) → ∀ f g : M → N, P V f → P V g →
    ∀ O : Opens M, O ≤ V → (O : Set M).Nonempty → EqOn f g O → EqOn f g V

/-- `SubExtension.IsRigid` is `IsRigidFor` of the abstract morphisms. -/
theorem isRigid_iff_isRigidFor [TopologicalSpace N] {C : Causality M} {D : Causality N} :
    IsRigid C D ↔ IsRigidFor (IsEMorphismOn C D) :=
  Iff.rfl

end Rigid

/-! ### Level A -/

/-- **The data of a geometry**: a type of structures on every topological space, the causality a
structure generates, and the morphisms of structures defined on an open set. -/
structure PreGeometry where
  /-- The structures on `M` (Level B: a charted space with transitions in `G`). -/
  Str : ∀ (M : Type u) [TopologicalSpace M], Type u
  /-- The causality a structure generates (`these.tex:5729`). -/
  causality : ∀ {M : Type u} [TopologicalSpace M], Str M → Causality M
  /-- `IsMor s t W f`: `f` is a structure morphism on the open `W` (`these.tex:3173`). -/
  IsMor : ∀ {M N : Type u} [TopologicalSpace M] [TopologicalSpace N],
    Str M → Str N → Opens M → (M → N) → Prop

/-- **Level A: what the CBG proof consumes** (design §2). Each field is justified, in its
docstring, by its use in the design's §3. -/
structure Geometry extends PreGeometry.{u} where
  /-- Sheaf law, restriction. §3.3 (candidates restricted to overlaps). -/
  isMor_mono : ∀ {M N : Type u} [TopologicalSpace M] [TopologicalSpace N] {s : Str M}
    {t : Str N} {W W' : Opens M} {f : M → N}, IsMor s t W f → W' ≤ W → IsMor s t W' f
  /-- Sheaf law, locality. §3.3 (`pgcdMap` on the union), §3.4 (`ψ ∪ φ` on `U ∪ O`). -/
  isMor_of_locally : ∀ {M N : Type u} [TopologicalSpace M] [TopologicalSpace N] {s : Str M}
    {t : Str N} {W : Opens M} {f : M → N},
    (∀ x ∈ W, ∃ V : Opens M, V ≤ W ∧ x ∈ V ∧ IsMor s t V f) → IsMor s t W f
  /-- Identity. §1 (`Dev.self`), §3.7 (universality). -/
  isMor_id : ∀ {M : Type u} [TopologicalSpace M] (s : Str M) (W : Opens M), IsMor s s W id
  /-- Composition. §1 (`Dev.IsMorphism` composes), §3.7. -/
  isMor_comp : ∀ {M N P : Type u} [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace P]
    {s : Str M} {t : Str N} {r : Str P} {W : Opens M} {V : Opens N} {f : M → N} {g : N → P},
    IsMor t r V g → IsMor s t W f → MapsTo f W V → IsMor s r W (g ∘ f)
  /-- Congruence. §3.3, §3.4 (a map equal to a morphism on `W`). -/
  isMor_congr : ∀ {M N : Type u} [TopologicalSpace M] [TopologicalSpace N] {s : Str M}
    {t : Str N} {W : Opens M} {f g : M → N}, IsMor s t W f → EqOn f g W → IsMor s t W g
  /-- A structure morphism is an abstract `𝕄≥0`-morphism of the generated causalities
  (`ETT.tex:1849–1852`, DEC-17). Every causal argument of §3. -/
  isEMorphismOn_of_isMor : ∀ {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    {s : Str M} {t : Str N} {W : Opens M} {f : M → N},
    IsMor s t W f → IsEMorphismOn (causality s) (causality t) W f
  /-- The generated causality is absolutely minimal on every open set (kb/0014). §3.5 (the
  causality of the gluing is `Gluing.causality`, uniqueness by `LocalIsomorphism.unique`). -/
  absolutelyMinimalOn : ∀ {M : Type u} [TopologicalSpace M] (s : Str M) (W : Opens M),
    (causality s).AbsolutelyMinimalOn W
  /-- Inverse of an injective morphism, on the image. §3.3 (`c ∘ b⁻¹` in `prop:Cauchy_pgcd`),
  §3.7 (cocycle). -/
  isMor_inv : ∀ {M N : Type u} [TopologicalSpace M] [TopologicalSpace N] [Nonempty M]
    {s : Str M} {t : Str N} {W : Opens M} {f : M → N} (h : IsMor s t W f), InjOn f W →
    IsMor t s ((isEMorphismOn_of_isMor h).imageOpens W le_rfl) (invFunOn f W)
  /-- The structure induced on an open subset. §3.3 (the MCGHD `pgcdOpens` as a development).
  Its causality is the restriction of `causality s` by `isMor_val`, `isEMorphismOn_of_isMor`,
  `absolutelyMinimalOn` and `LocalIsomorphism.unique` — a planned lemma of package 4 (`Pgcd`). -/
  restrict : ∀ {M : Type u} [TopologicalSpace M], Str M → (W : Opens M) → Str W
  /-- A map into `W` is a morphism into `restrict s W` iff it is one into `M`. §3.3 (the
  embedding of `M₀` into the MCGHD). -/
  isMor_corestrict_iff : ∀ {M N : Type u} [TopologicalSpace M] [TopologicalSpace N] (s : Str M)
    (W : Opens M) (t : Str N) (V : Opens N) (g : N → W),
    IsMor t (restrict s W) V g ↔ IsMor t s V (Subtype.val ∘ g)
  /-- Transport along a homeomorphism. §3.6 (small skeleton, carriers in `Set ℕ`). -/
  transport : ∀ {M M' : Type u} [TopologicalSpace M] [TopologicalSpace M'],
    (M ≃ₜ M') → Str M → Str M'
  isMor_transport : ∀ {M M' : Type u} [TopologicalSpace M] [TopologicalSpace M'] (e : M ≃ₜ M')
    (s : Str M), IsMor s (transport e s) ⊤ e
  /-- **Gluing** (the sheaf axiom of structures). Pieces `M i` open-embedded in `Z`, covering it,
  with transitions that are morphisms, glue to a structure on `Z` for which every embedding is a
  morphism. §3.5 (`ppcm`), §3.7 (`FamilyGlueData.Glued`, whose `ι i` are such embeddings). The
  glued causality agrees with `Gluing.causality` by the same derivation as for `restrict`
  (planned lemma, package 7). The transition hypothesis `∃ φ : M i → M j` is unsatisfiable when
  `M j` is empty and `M i` is not; harmless, developments being non-empty. -/
  glue : ∀ {Z : Type u} [TopologicalSpace Z] {ι : Type u} (M : ι → Type u)
    [∀ i, TopologicalSpace (M i)] (s : ∀ i, Str (M i)) (e : ∀ i, M i → Z)
    (he : ∀ i, IsOpenEmbedding (e i)), (∀ z, ∃ i, z ∈ range (e i)) →
    (∀ i j, ∃ φ : M i → M j,
      IsMor (s i) (s j) ⟨e i ⁻¹' range (e j), (he j).isOpen_range.preimage (he i).continuous⟩ φ ∧
        ∀ x, e i x ∈ range (e j) → e j (φ x) = e i x) →
    ∃ t : Str Z, ∀ i, IsMor (s i) t ⊤ (e i)
  /-- **A1, rigidity** (`prop:GX_liouville`, `rem:CBG_analytique`), into Hausdorff targets
  (`not_isRigidFor_branchingLine`). §3.1 (Cor 3.2), §3.3, §3.7 (cocycle, uniqueness). -/
  rigid : ∀ {M N : Type u} [TopologicalSpace M] [TopologicalSpace N] [T2Space N] (s : Str M)
    (t : Str N), IsRigidFor (IsMor s t)
  /-- The singular loci `sing_α`. §3.4 (`lem:corresponding_K`, BTZ points). -/
  sing : ∀ {M : Type u} [TopologicalSpace M], Str M → ℝ → Set M
  /-- Morphisms preserve the type of a point (`cor:model_corresponding`). §3.4. -/
  isMor_sing : ∀ {M N : Type u} [TopologicalSpace M] [TopologicalSpace N] {s : Str M}
    {t : Str N} {W : Opens M} {f : M → N}, IsMor s t W f → ∀ {x : M}, x ∈ W → ∀ {α : ℝ},
    0 ≤ α → (x ∈ sing s α ↔ f x ∈ sing t α)
  /-- **A2**: the causal facts of `𝔼≥0`-manifolds, in the **corrected** bundle
  `SingularFlatAxioms` (gx review C1, DEC-64: the former field `BTZAxioms.Iplus_eq` is false in
  `E₀` and is replaced by `Iplus_of_lt` in the strict library). Second countability is a **hypothesis** (gx review
  C2: it is part of the definition of a singular manifold, gx
  `def:singular_manifold_locally_connected`, `these.tex:1357`, not a theorem; R2), so the
  bundle's `secondCountable` field is free. §3.1–§3.6. -/
  singularFlatAxioms : ∀ {M : Type u} [TopologicalSpace M] [T2Space M] [ConnectedSpace M]
    [SecondCountableTopology M] (s : Str M), (causality s).SingularFlatAxioms (sing s)
  /-- **A2**: `CurvesExtend`, on **globally hyperbolic** `M` only (gx review C3: the proof consumes
  it on developments, which are GH, and there `curvesExtend_of_timeFunction`,
  `Causal/CurvesExtend.lean:423`, discharges it from a continuous time function strictly
  increasing along `≤`, e.g. the Geroch time of `SingularGeroch`, whose `K_monotone` input survives
  C1 by `SingularFlatAxioms.K_monotone`, DEC-64). §3.1 (re-routing around `exists_mem_image_inf`). -/
  curvesExtend : ∀ {M : Type u} [TopologicalSpace M] [T2Space M] [ConnectedSpace M]
    [SecondCountableTopology M] (s : Str M), (causality s).GloballyHyperbolic →
    (causality s).CurvesExtend
  /-- **A2, a time function on every globally hyperbolic admissible spacetime** (design §6,
  interface round 2 (1), ACCEPTED by gx 2026-11-01): a continuous `T : M → ℝ` strictly increasing
  along `≤`. The conclusion is, verbatim, the body of `Causality.HasTimeFunction` (`Causal.CurvesExtend`,
  defined there, downstream of this file; the two are definitionally equal, so
  `𝔊.timeFunction s hGH : (𝔊.causality s).HasTimeFunction` and
  `fun s hGH => 𝔊.timeFunction s hGH : 𝔊.HasTimeFunctions` (`CBG/Maximal`) typecheck as they are).
  It is weaker than `Causality.IsTimeFunction` (`Causal/Morphism.lean`) and is the hypothesis form
  of `curvesExtend_of_timeFunction` (`Causal/CurvesExtend.lean:423`). §3.2 (Sbierski
  Lemma 3.3, `IsCGHD.injOn`: MCGHD morphisms injective), hence §3.3, §3.5, §3.7. Discharge: flat,
  the Geroch time of admissible measures (`Flat/GerochFlat`); `E₀`, `SingularGeroch` (its
  `K_monotone` input: `SingularFlatAxioms.K_monotone`, DEC-64). Gives `LocalModel.timeFunction` at
  Level B. -/
  timeFunction : ∀ {M : Type u} [TopologicalSpace M] [T2Space M] [ConnectedSpace M]
    [SecondCountableTopology M] (s : Str M), (causality s).GloballyHyperbolic →
    ∃ T : M → ℝ, Continuous T ∧ ∀ x y, (causality s).le ⊤ x y → x ≠ y → T x < T y
  /-- **A2**: `J⁺(Σ) ∩ J⁻(p)` compact (R1). §3.4 (Lemmas 3.9, 3.11). -/
  isCompact_Jplus_inter_Jminus : ∀ {M : Type u} [TopologicalSpace M] [T2Space M]
    [ConnectedSpace M] [SecondCountableTopology M] (s : Str M),
    (causality s).GloballyHyperbolic → ∀ S : Set M,
    (causality s).IsCauchySurface S → ∀ p : M,
      IsCompact ((causality s).Jplus ⊤ S ∩ (causality s).Jminus ⊤ {p})
  /-- **A2**, time-reversed form (no duality). §3.4. -/
  isCompact_Jminus_inter_Jplus : ∀ {M : Type u} [TopologicalSpace M] [T2Space M]
    [ConnectedSpace M] [SecondCountableTopology M] (s : Str M),
    (causality s).GloballyHyperbolic → ∀ S : Set M,
    (causality s).IsCauchySurface S → ∀ p : M,
      IsCompact ((causality s).Jminus ⊤ S ∩ (causality s).Jplus ⊤ {p})
  /-- **A2, second countability from a Cauchy surface** (gx review C2): a globally hyperbolic
  admissible spacetime with a second-countable Cauchy surface is second countable (gx discharges
  it by the splitting `M ≅ S × ℝ`, `IsCausalFlow.exists_isCauchySplitting` / `geroch_sing_split`).
  §3.7 (package 10: the glued `M̄` is a `Dev`, its Cauchy surface the image of `M₀`'s); §3.6 (the
  size bound then applies to every development, carriers being SC and T2). -/
  secondCountable_of_cauchy : ∀ {M : Type u} [TopologicalSpace M] [T2Space M] [ConnectedSpace M]
    (s : Str M), (causality s).GloballyHyperbolic → ∀ S : Set M, (causality s).IsCauchySurface S →
    SecondCountableTopology S → SecondCountableTopology M
  /-- **A3, germ extension at a corresponding boundary point in the future of `Σ`** (Sbierski
  Lemma 3.8; `cor:ext_continue`; the `K⁻` side at BTZ points). `U ⊆ M` is a common Cauchy
  sub-development with injective morphism `ψ`, `q` corresponds to `p ∈ ∂U`. `M`, `N` second
  countable (interface round 3: every B3 fact the derivation uses assumes it). §3.4. -/
  germExt_future : ∀ {M N : Type u} [TopologicalSpace M] [TopologicalSpace N] [T2Space M]
    [ConnectedSpace M] [SecondCountableTopology M] [T2Space N] [ConnectedSpace N]
    [SecondCountableTopology N] (s : Str M) (t : Str N) (U : Opens M)
    (ψ : M → N) (S : Set M) (h : IsMor s t U ψ), InjOn ψ U →
    (causality s).GloballyHyperbolic → (causality t).GloballyHyperbolic →
    (causality s).GloballyHyperbolicOn U →
    (causality t).GloballyHyperbolicOn ((isEMorphismOn_of_isMor h).imageOpens U le_rfl) →
    S ⊆ U → (causality s).IsCauchySurface S → (causality s).IsCauchySurfaceOn U S →
    (causality t).IsCauchySurface (ψ '' S) →
    (causality t).IsCauchySurfaceOn ((isEMorphismOn_of_isMor h).imageOpens U le_rfl) (ψ '' S) →
    ∀ p : M, ∀ q : N, p ∈ frontier (U : Set M) → p ∈ (causality s).Jplus ⊤ S →
      MapClusterPt q (𝓝[(U : Set M)] p) ψ →
      ∃ (O : Opens M) (φ : M → N), p ∈ O ∧ IsMor s t O φ ∧ φ p = q ∧ EqOn φ ψ (O ⊓ U : Opens M)
  /-- **A3** in the past of `Σ` (the `K⁺` side; no time reversal). §3.4. -/
  germExt_past : ∀ {M N : Type u} [TopologicalSpace M] [TopologicalSpace N] [T2Space M]
    [ConnectedSpace M] [SecondCountableTopology M] [T2Space N] [ConnectedSpace N]
    [SecondCountableTopology N] (s : Str M) (t : Str N) (U : Opens M)
    (ψ : M → N) (S : Set M) (h : IsMor s t U ψ), InjOn ψ U →
    (causality s).GloballyHyperbolic → (causality t).GloballyHyperbolic →
    (causality s).GloballyHyperbolicOn U →
    (causality t).GloballyHyperbolicOn ((isEMorphismOn_of_isMor h).imageOpens U le_rfl) →
    S ⊆ U → (causality s).IsCauchySurface S → (causality s).IsCauchySurfaceOn U S →
    (causality t).IsCauchySurface (ψ '' S) →
    (causality t).IsCauchySurfaceOn ((isEMorphismOn_of_isMor h).imageOpens U le_rfl) (ψ '' S) →
    ∀ p : M, ∀ q : N, p ∈ frontier (U : Set M) → p ∈ (causality s).Jminus ⊤ S →
      MapClusterPt q (𝓝[(U : Set M)] p) ψ →
      ∃ (O : Opens M) (φ : M → N), p ∈ O ∧ IsMor s t O φ ∧ φ p = q ∧ EqOn φ ψ (O ⊓ U : Opens M)
  /-- **A4, a slice through a future boundary point** (Sbierski Thm 3.6: `τ_q`, Lemma 3.11):
  if `J⁻(p) ∩ ∂U ∩ J⁺(Σ) = {p}` (Lemma 3.9), `U` enlarges inside any neighbourhood of `p` with
  `Σ` still Cauchy. `M` second countable (interface round 3). §3.4 (Thm 3.6). -/
  slice_future : ∀ {M : Type u} [TopologicalSpace M] [T2Space M] [ConnectedSpace M]
    [SecondCountableTopology M] (s : Str M) (U : Opens M) (S : Set M),
    (causality s).GloballyHyperbolic →
    (causality s).GloballyHyperbolicOn U → S ⊆ U → (causality s).IsCauchySurface S →
    (causality s).IsCauchySurfaceOn U S → ∀ p : M, p ∈ frontier (U : Set M) →
    p ∈ (causality s).Jplus ⊤ S →
    (causality s).Jminus ⊤ {p} ∩ frontier (U : Set M) ∩ (causality s).Jplus ⊤ S = {p} →
    ∀ O : Opens M, p ∈ O → ∃ U' : Opens M, U < U' ∧ (U' : Set M) ⊆ U ∪ O ∧
      (causality s).GloballyHyperbolicOn U' ∧ (causality s).IsCauchySurfaceOn U' S
  /-- **A4** through a past boundary point (no time reversal). §3.4. -/
  slice_past : ∀ {M : Type u} [TopologicalSpace M] [T2Space M] [ConnectedSpace M]
    [SecondCountableTopology M] (s : Str M) (U : Opens M) (S : Set M),
    (causality s).GloballyHyperbolic →
    (causality s).GloballyHyperbolicOn U → S ⊆ U → (causality s).IsCauchySurface S →
    (causality s).IsCauchySurfaceOn U S → ∀ p : M, p ∈ frontier (U : Set M) →
    p ∈ (causality s).Jminus ⊤ S →
    (causality s).Jplus ⊤ {p} ∩ frontier (U : Set M) ∩ (causality s).Jminus ⊤ S = {p} →
    ∀ O : Opens M, p ∈ O → ∃ U' : Opens M, U < U' ∧ (U' : Set M) ⊆ U ∪ O ∧
      (causality s).GloballyHyperbolicOn U' ∧ (causality s).IsCauchySurfaceOn U' S

namespace Geometry

variable (𝔊 : Geometry.{u}) {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]

/-- The inclusion of an open subset is a morphism. -/
theorem isMor_val (s : 𝔊.Str M) (W : Opens M) :
    𝔊.IsMor (𝔊.restrict s W) s ⊤ (Subtype.val : W → M) :=
  (𝔊.isMor_corestrict_iff s W (𝔊.restrict s W) ⊤ id).1 (𝔊.isMor_id _ ⊤)

/-- A morphism on `W` is a morphism on the open subset `W` seen as a space. -/
theorem IsMor.restrict {s : 𝔊.Str M} {t : 𝔊.Str N} {W : Opens M} {f : M → N}
    (hf : 𝔊.IsMor s t W f) : 𝔊.IsMor (𝔊.restrict s W) t ⊤ (f ∘ Subtype.val) :=
  𝔊.isMor_comp hf (𝔊.isMor_val s W) (fun x _ => x.2)

end Geometry

/-! ### Level B: a local model -/

section Charted

variable {Y : Type u} [TopologicalSpace Y]

/-- The causality generated by an atlas (`these.tex:5729`: « munie de la causalité engendrée par
son $X_A$-atlas »): the generated causality (`theo:causalite_engendre`) of the transports of `D`
along the preferred charts. -/
noncomputable def chartedCausality (D : Causality Y) (M : Type u) [TopologicalSpace M]
    [ChartedSpace Y M] : Causality M :=
  Causality.generated (fun x : M => chartSource (chartAt Y x))
    (fun x => ⟨x, mem_chart_source Y x⟩) (fun x => D.chartTransport (chartAt Y x))

/-- `sing_α(M)` read through the preferred chart (`these.tex:3149–3152`). -/
def chartedSing (singY : ℝ → Set Y) (M : Type u) [TopologicalSpace M] [ChartedSpace Y M]
    (α : ℝ) : Set M :=
  {x | chartAt Y x x ∈ singY α}

end Charted

/-- **Level B: a local model** (design §2; the thesis's `(G, X, X_A)`, `these.tex:3027–3070`).
The model space `Y` (for gx: `𝕄 ⊕ Σ_α 𝔼_α`; flat: `Minkowski d`), the groupoid `G` of the
`X_A`-morphisms between open subsets of `Y` — near a singular point the restrictions of the model
automorphisms `G_α = Aut(X_α)` (`these.tex:3053`), on the regular part the `(G,X)`-morphisms (the
atlas transitions of `these.tex:3048–3050`) — the causality and singular loci of `Y`; the admissible
spacetimes are `ChartedSpace Y M`, `HasGroupoid M G`, Hausdorff, connected, second
countable (`Dev`; gx review C2). Morphisms are
`LiftPropOn G.IsLocalStructomorphWithinAt` (`LocalModel.IsMor`), the thesis's `X_A`-morphisms
(`these.tex:3173`). -/
structure LocalModel where
  /-- The model space. -/
  Y : Type u
  [topY : TopologicalSpace Y]
  /-- The groupoid of `X_A`-morphisms between open subsets of `Y` (the transitions of an
  `X_A`-atlas, `these.tex:3048–3050`). -/
  G : StructureGroupoid Y
  /-- `G` is closed under restriction: open subsets inherit the structure (`restrict`), and
  `IsLocalStructomorphWithinAt` is a local invariant property. §3.3. -/
  [closedUnderRestriction : ClosedUnderRestriction G]
  /-- The causality of the model (`defi:causal_Ealpha`, `defi:causal_E0`). -/
  causalityY : Causality Y
  /-- The singular loci of the model, `sing_α(Y)` (`these.tex:3149`). -/
  singY : ℝ → Set Y
  /-- `Y` is locally connected (Minkowski space, the `𝔼_α`). The open–closed argument deriving A1
  from B1 needs connected chart neighbourhoods; so does A3 (one element of `G` on a connected
  piece of `U` near `p`). §3.1, §3.4. -/
  [locallyConnected : LocallyConnectedSpace Y]
  /-- **Round 4 (1), gx-agreed 2026-11-02: the model is Hausdorff** (Minkowski space and gx's
  `𝕄 ⊕ Σ_α 𝔼_α` are metric). Used by A3 (`CBG/FromModel`, `germ_ext_reg`, `germ_ext_nonBTZ`):
  the element `e ∈ G` that B2 gives on a connected piece and the chart at `q` both carry `ψ`'s
  germ to a limit at the chart image of `p`, so `e (κ p) = κ' q` is uniqueness of limits in `Y`;
  and the extension of an agreement from the regular part of a piece to the whole piece. -/
  [t2Y : T2Space Y]
  /-- **B1, rigidity of `G`** (analyticity of `(G,X)`, `these.tex:1185–1192`: « deux éléments
  $g_1,g_2$ de $G$ sont égaux si et seulement si les restrictions […] à $\U$ sont égales »):
  elements of `G` agreeing on a non-empty open subset of a connected open set agree on it. Gives
  A1 (`prop:GX_liouville`, `these.tex:1476`) with `locallyConnected`. -/
  rigid : ∀ e ∈ G, ∀ e' ∈ G, ∀ U : Set Y, IsOpen U → IsPreconnected U → U ⊆ e.source →
    U ⊆ e'.source → ∀ O ⊆ U, IsOpen O → O.Nonempty → EqOn e e' O → EqOn e e' U
  /-- **B2 at a singular point: the model family is analytic** (`def:analytique`,
  `these.tex:3335–3340`: « pour tout ouvert connexe $\U$ voisinage d'un point singulier, tout
  $(G,X)$-morphisme $f:\reg(\U)\rightarrow\reg(Y)$ est la restriction d'un automorphisme de
  $Y$ »; for `𝔼≥0`, `prop:isom`, `these.tex:4332`, with the injectivity « nécessaire »,
  `these.tex:4426`). `U` is a connected open set meeting `sing_{α₀}` at `y₀`; `f` is an injective
  local `G`-structomorphism on `reg(U)` **into the same model** — `MapsTo f reg(U)` the connected
  component of `y₀`, the thesis's $\reg(Y)$ with $Y$ the model of `y₀` (in gx's
  `Y = 𝕄 ⊕ Σ_α 𝔼_α`, the component `𝔼_{α₀}`). Conclusion: `f` is the restriction of one element of
  `G` **defined on that whole component** (« un automorphisme de $Y$ », not a germ: A3 extends `ψ`
  from `U ∩ O` to a neighbourhood of `p ∉ U`). The same-model hypothesis is what the thesis's
  definition says; a map from `reg(U)` into a *different* model is excluded there by
  `def:incompatibles` / famille analytique (b) (`these.tex:3328–3332`, `3346–3353`), here by the
  hypothesis (package 11 derives it at a BTZ boundary point from `sing_mem` and the chart at `q`).
  Gives A3 at singular points.

  **Kept in this strong form** (gx review C4). For `E₀` it is B21 `prop:isom_strong` at
  `α = β = 0` (arXiv 2108.12631, `papers/gx/sources/2108.12631/src/BTZ_1.tex:468–475`: « let
  $\phi:\reg(\U)\rightarrow \E^{1,2}_\beta$ be a $\mass{}$-morphism. If $\phi$ is a injective
  then $\alpha=\beta$ and $\phi$ is the restriction of an element of $\isom(\E^{1,2}_\alpha)$ »),
  i.e. the thesis's `prop:isom` with the injectivity it calls necessary. The weaker form (`f`
  defined on all of `U`, B21 `prop:isom`, `BTZ_1.tex:378`) does **not** suffice, by gx's past-side
  example: `U = M ∖ (line below a)` is a CGHD, every `p < a` on the line is a corresponding point,
  and `U ∩ O = reg(O)` contains no singular point; Sbierski's **Lemma 3.9** (1309.7591) walks
  along such points with Lemma 3.8 (A3), which needs the extension from `reg(U)` alone. gx's
  route avoids invariance of domain (absent from mathlib): lift to `E₀,∞`, `g ∘ D = D ∘ φ̃`, `g`
  stabilises `Δ` and normalises `⟨P⟩`, the explicit list, injectivity forcing `ℓ = 1`. -/
  localUnique_sing : ∀ U : Set Y, IsOpen U → IsConnected U → ∀ y₀ ∈ U, ∀ α₀ : ℝ, 0 ≤ α₀ →
    y₀ ∈ singY α₀ → ∀ f : Y → Y,
    (∀ y ∈ U ∩ {y | ∀ α : ℝ, 0 ≤ α → y ∉ singY α},
      G.IsLocalStructomorphWithinAt f (U ∩ {y | ∀ α : ℝ, 0 ≤ α → y ∉ singY α}) y) →
    InjOn f (U ∩ {y | ∀ α : ℝ, 0 ≤ α → y ∉ singY α}) →
    MapsTo f (U ∩ {y | ∀ α : ℝ, 0 ≤ α → y ∉ singY α}) (connectedComponent y₀) →
    ∃ e ∈ G, connectedComponent y₀ ⊆ e.source ∧
      EqOn f e (U ∩ {y | ∀ α : ℝ, 0 ≤ α → y ∉ singY α})
  /-- **B2 at a singular point, past side: a regular piece adherent to `y₀`** (design §6,
  interface round 2 (2), gx 2026-11-01; **largeness clause amended in interface round 3**, gx
  2026-11-02, the **diamond form with a regular tip**). `U` is a connected open set of **regular**
  points (not a neighbourhood of `y₀`); the largeness clause: for some open `O ∋ y₀` and some
  **regular** `r ∈ O` with `y₀ ≪_O r`, `U ⊇ reg ∩ I⁺_O(y₀) ∩ I⁻_O(r)` (the regular part of the
  chronological diamond of `y₀` and `r` in `O`). `f` is an injective local `G`-structomorphism on
  `U` into the component of `y₀` (the same model, as in `localUnique_sing`), converging along `U`
  at `y₀` to a point `z₀` of the same singular locus `sing_{α₀}` (`MapClusterPt z₀ (𝓝[U] y₀) f`,
  Sbierski Def 3.5). Conclusion: `f` is the restriction of one element of `G` defined on the whole
  component of `y₀`. Needed by A3 in the past of `Σ` at a BTZ boundary point, where the connected
  piece `U ∩ I⁻_W(r)` is regular and adherent to `p` but need not be `reg` of a neighbourhood of
  `p` (gx `A3-B-INVESTIGATION.md`: (B) can fail on the past side); that piece contains the diamond
  `I⁺_W(p) ∩ I⁻_W(r)` (`Causality.CausallyConvexIn.Iplus_inter_Iminus_subset`, `CBG/FromModel`),
  which is exactly this clause read in a chart.

  **gx's justification in `E₀`** (2026-11-02, by hand): `r ∈ I⁺_O(y₀)`, an open set, so there is
  a point `q` of `y₀`'s line with `y₀ < q ≪ r`; `I⁻_O(r) ∋ q` contains a basic piece near `q`
  holding every regular point of small radius, for every angle `θ`, and so does `I⁺_O(y₀)` (by
  `Iplus_of_lt`, `q` lying strictly above `y₀` on the line); so the regular part of the diamond
  contains a full `θ`-loop around `Δ`, whose holonomy is the parabolic `P`; `f` maps it to a loop
  winding the same way, so the lift of `f` normalises `⟨P⟩`, and the normaliser is `Isom(E₀)`.

  **The round-2 clause it replaces was vacuous** (finding, `CBG/FromModel`,
  `Causality.BTZAxioms.exists_le_inter_Iminus_subset`): `∃ r ∈ O, y₀ ≤_O r ∧
  reg ∩ I⁻_O(r) ⊆ U` holds for every `U` at a BTZ point (`r := y₀`: BTZ points have empty
  chronological past, `Iminus_eq_empty`), so it was the point-contact form, which the cone
  counterexample refutes in `E₀`. Here `r ∈ regY` excludes `r := y₀` and every `r` on the line,
  and `y₀ ≪_O r` makes the diamond non-empty. Rejected (design §6): point contact and "the
  closure of `U` contains a segment of the line" (a boost along `Δ` conjugates `P` to a
  non-integral power). Vacuous for the flat instance (`singY = ∅`). -/
  localUnique_sing_adherent : ∀ U : Set Y, IsOpen U → IsConnected U →
    U ⊆ {y | ∀ α : ℝ, 0 ≤ α → y ∉ singY α} → ∀ y₀ : Y, ∀ α₀ : ℝ, 0 ≤ α₀ → y₀ ∈ singY α₀ →
    (∃ O : Opens Y, y₀ ∈ O ∧ ∃ r ∈ O, r ∈ {y | ∀ α : ℝ, 0 ≤ α → y ∉ singY α} ∧
      causalityY.lt O y₀ r ∧
      {y | ∀ α : ℝ, 0 ≤ α → y ∉ singY α} ∩ causalityY.Iplus O {y₀} ∩ causalityY.Iminus O {r} ⊆ U) →
    ∀ z₀ ∈ singY α₀, ∀ f : Y → Y, (∀ y ∈ U, G.IsLocalStructomorphWithinAt f U y) → InjOn f U →
    MapsTo f U (connectedComponent y₀) → MapClusterPt z₀ (𝓝[U] y₀) f →
    ∃ e ∈ G, connectedComponent y₀ ⊆ e.source ∧ EqOn f e U
  /-- **B2 on a regular component** (Liouville for `(G,X)` analytic, `prop:GX_liouville`,
  `these.tex:1476`; **not** the thesis's `def:analytique`, which only covers neighbourhoods of
  singular points — this branch is this file's own, and its hypotheses are chosen so that it holds
  for gx's model): an injective local `G`-structomorphism on a connected open `U` lying in a
  component of `Y` without singular points, **with values in a component without singular points**
  (`MapsTo`), is the restriction of one element of `G` defined on the whole component of `U`. The
  `MapsTo` hypothesis is necessary: without it, `f := e₀.symm` for an `e₀ ∈ G` given by
  `regularChart` at a regular point of `𝔼_α` would force an element of `G` sending all of `𝕄` into
  `reg(𝔼_α)`, which the developing map rules out. Flat instance (`singY = ∅`): Liouville, the
  affine extension. Gives A3 at regular points, with `regularChart` applied on both sides. -/
  localUnique_reg : ∀ U : Set Y, IsOpen U → IsConnected U →
    (∀ y ∈ U, ∀ z ∈ connectedComponent y, ∀ α : ℝ, 0 ≤ α → z ∉ singY α) →
    ∀ f : Y → Y, (∀ y ∈ U, G.IsLocalStructomorphWithinAt f U y) → InjOn f U →
    MapsTo f U {z | ∀ w ∈ connectedComponent z, ∀ α : ℝ, 0 ≤ α → w ∉ singY α} →
    ∃ e ∈ G, (∀ y ∈ U, connectedComponent y ⊆ e.source) ∧ EqOn f e U
  /-- **B2, regular charts** (`these.tex:3043`: $Y_i\in\{X_\alpha\}\cup\{X\}$; a regular point has
  a chart in `X`): a regular point of `Y` is moved by an element of `G` into a component of `Y`
  without singular points. A3 at a regular boundary point `p` (corresponding to `q`): compose the
  charts of `M` at `p` and of `N` at `q` with the elements this field gives, so that both sides
  land in fully regular components; the transported `ψ` then satisfies the `MapsTo` hypothesis of
  `localUnique_reg`. For a model without singular locus, `e = refl`. -/
  regularChart : ∀ y : Y, (∀ α : ℝ, 0 ≤ α → y ∉ singY α) → ∃ e ∈ G, y ∈ e.source ∧
    ∀ z ∈ connectedComponent (e y), ∀ α : ℝ, 0 ≤ α → z ∉ singY α
  /-- **B3**: the model causality is absolutely minimal on every open set (`cor:massA_causalite`).
  Gives `Geometry.absolutelyMinimalOn`. -/
  absolutelyMinimalOn_Y : ∀ W : Opens Y, causalityY.AbsolutelyMinimalOn W
  /-- **B3**: elements of `G` are isomorphisms of the model causality on their source
  (`ChartIso`, kb/0018). The chart transports then agree on overlaps. -/
  chartIso_mem : ∀ e ∈ G, ChartIso causalityY causalityY e
  /-- **B3**: elements of `G` preserve the type of a point (`prop:GX_sing_dec`). Gives
  `Geometry.isMor_sing`, and makes `chartedSing` chart-independent. -/
  sing_mem : ∀ e ∈ G, ∀ y ∈ e.source, ∀ α : ℝ, 0 ≤ α → (y ∈ singY α ↔ e y ∈ singY α)
  /-- **B3, the global causal facts of `𝔼≥0`-manifolds** (gx §4 (i): the **corrected** bundle
  `SingularFlatAxioms`, gx review C1, DEC-64 — the former `Iplus_eq` is false in `E₀`, radial null
  ray; not local, so not derivable from `Y`). Second countability is a hypothesis (C2; gx §4 (vi)
  is now `secondCountable_of_cauchy`). Gives A2. -/
  singularFlatAxioms : ∀ {M : Type u} [TopologicalSpace M] [T2Space M] [ConnectedSpace M]
    [SecondCountableTopology M] [ChartedSpace Y M] [HasGroupoid M G],
    (chartedCausality causalityY M).SingularFlatAxioms (chartedSing singY M)
  /-- **B3**: `CurvesExtend` on **globally hyperbolic** `M` (gx review C3). For gx:
  `curvesExtend_of_timeFunction` (`CurvesExtend.lean:423`) with the Geroch time of
  `SingularGeroch` (its `K_monotone` input: `SingularFlatAxioms.K_monotone`, DEC-64), or
  `GloballyHyperbolic.curvesExtend` (`CurvesExtend.lean:461`) from admissible measures. Flat
  instance, existing proofs: `curvesExtend_of_isCausalFlow` (`Flat/CauchyComplete.lean:2467`,
  from a causal flow, so for every GH flat `M` with one, DEC-49), and on opens
  `curvesExtendOn_of_timeFunction` (`CBG/CausalConvex.lean:273`). Gives A2. -/
  curvesExtend : ∀ {M : Type u} [TopologicalSpace M] [T2Space M] [ConnectedSpace M]
    [SecondCountableTopology M] [ChartedSpace Y M] [HasGroupoid M G],
    (chartedCausality causalityY M).GloballyHyperbolic →
    (chartedCausality causalityY M).CurvesExtend
  /-- **B3, time functions** (design §6, interface round 2 (1), the counterpart of
  `Geometry.timeFunction`, which `Geometry.ofLocalModelOfGermSlice` fills from it): every globally hyperbolic
  admissible `M` carries a continuous `T : M → ℝ` strictly increasing along `≤` (the body of
  `Causality.HasTimeFunction`, `Causal.CurvesExtend`, verbatim). Flat instance: the Geroch time of admissible
  measures (`Flat/GerochFlat`; `Flat/CBG` already proves the statement for `flatCausality`); `E₀`:
  `SingularGeroch` (gx). Gives A2 (`timeFunction`). -/
  timeFunction : ∀ {M : Type u} [TopologicalSpace M] [T2Space M] [ConnectedSpace M]
    [SecondCountableTopology M] [ChartedSpace Y M] [HasGroupoid M G],
    (chartedCausality causalityY M).GloballyHyperbolic →
    ∃ T : M → ℝ, Continuous T ∧
      ∀ x y, (chartedCausality causalityY M).le ⊤ x y → x ≠ y → T x < T y
  /-- **B3**: `J⁺(Σ) ∩ J⁻(p)` compact (gx §4 (vii), R1). Gives A2. -/
  isCompact_Jplus_inter_Jminus : ∀ {M : Type u} [TopologicalSpace M] [T2Space M]
    [ConnectedSpace M] [SecondCountableTopology M] [ChartedSpace Y M] [HasGroupoid M G],
    (chartedCausality causalityY M).GloballyHyperbolic → ∀ S : Set M,
    (chartedCausality causalityY M).IsCauchySurface S → ∀ p : M,
      IsCompact ((chartedCausality causalityY M).Jplus ⊤ S ∩
        (chartedCausality causalityY M).Jminus ⊤ {p})
  /-- **B3**, time-reversed (no duality). -/
  isCompact_Jminus_inter_Jplus : ∀ {M : Type u} [TopologicalSpace M] [T2Space M]
    [ConnectedSpace M] [SecondCountableTopology M] [ChartedSpace Y M] [HasGroupoid M G],
    (chartedCausality causalityY M).GloballyHyperbolic → ∀ S : Set M,
    (chartedCausality causalityY M).IsCauchySurface S → ∀ p : M,
      IsCompact ((chartedCausality causalityY M).Jminus ⊤ S ∩
        (chartedCausality causalityY M).Jplus ⊤ {p})
  /-- **B3, second countability from a Cauchy surface** (gx review C2; gx §4 (vi)): a globally
  hyperbolic admissible `M` with a second-countable Cauchy surface is second countable. gx
  discharges it by the splitting `M ≅ S × ℝ` (`IsCausalFlow.exists_isCauchySplitting`,
  `Splitting.lean:298`, or `geroch_sing_split`, `SingularGeroch.lean:277`; flat instance:
  `flat_exists_isCauchySplitting`, `Splitting.lean:1934`). Gives A2 (`secondCountable_of_cauchy`),
  used by package 10 for `M̄`. -/
  secondCountable_of_cauchy : ∀ {M : Type u} [TopologicalSpace M] [T2Space M] [ConnectedSpace M]
    [ChartedSpace Y M] [HasGroupoid M G], (chartedCausality causalityY M).GloballyHyperbolic →
    ∀ S : Set M, (chartedCausality causalityY M).IsCauchySurface S →
    SecondCountableTopology S → SecondCountableTopology M
  /-- **Round 4 (4), gx-agreed 2026-11-02: the regular part of the model is open**, i.e. the
  singular loci `⋃_{α ≥ 0} sing_α(Y)` form a closed set (in gx's `𝕄 ⊕ Σ_α 𝔼_α` each `sing_α` is a
  line of `𝔼_α`; flat: `singY = ∅`). Consumed by `CBG/FromModel`'s `germ_ext_nonBTZ` (massive
  case): the regular part `A ∩ κ⁻¹ reg(Y)` of A3's piece is open, so `ψ` restricts to a morphism
  on it, where B2 at a singular point (`localUnique_sing`) is applied; the agreement is then
  extended to `A` by `dense_regY` and `T2Space Y`. -/
  isOpen_regY : IsOpen {y | ∀ α : ℝ, 0 ≤ α → y ∉ singY α}
  /-- **Round 4, added by the round-4 author, accepted by gx (2026-11-02; every stratum closed with
  empty interior, countably many strata): the regular part of the model is dense.** Needed by A3 at a massive boundary point (`α > 0`,
  `CBG/FromModel`'s `germ_ext_nonBTZ`): B2 at a singular point (`localUnique_sing`) gives one
  `e ∈ G` agreeing with `ψ` (read in charts) on the **regular** part of the connected piece `A`
  only; to get `e (κ p) = κ' q` and agreement on `A` the regular part must accumulate at every
  point of `A`. Neither `isOpen_regY` nor the B3 facts give it: `interior_sing` is per `α`, and an
  open set can be covered by uncountably many loci `sing_α` (a foliation by timelike lines, each
  of its own `α`), each closed with empty interior, with `⋃_α sing_α` closed. True in gx's model
  (the singular loci are lines in 3-manifolds) and for the flat model (`singY = ∅`). -/
  dense_regY : Dense {y | ∀ α : ℝ, 0 ≤ α → y ∉ singY α}
  /-- **Round 4 (3), gx-agreed 2026-11-02 ("type agreement, stated on `Y`"): the type of a
  corresponding point, and its component.** `U` is a connected open set of `Y` containing a
  chronological diamond with tip `y₀` — below `y₀` (`r ≪_O y₀`, `I⁺_O(r) ∩ I⁻_O(y₀) ⊆ U`, the
  future-side piece of A3) or above it (`y₀ ≪_O r`, `I⁺_O(y₀) ∩ I⁻_O(r) ⊆ U`, the past-side piece);
  `y₀` is not a BTZ point; `f` is an injective local `G`-structomorphism on `U` (at its singular
  points too) clustering at `z₀` along `U` at `y₀` (`MapClusterPt z₀ (𝓝[U] y₀) f`, Sbierski
  Def 3.5 read in charts). Conclusion: `y₀` and `z₀` have the same type
  (`cor:model_corresponding`, `ETT.tex:2158`, read on `Y`), and if `y₀` is singular, `z₀` lies in
  the component of `y₀` (in gx's model each type `α > 0` lies in the one component `𝔼_α`). This
  is exactly what `CBG/FromModel` consumes (`germ_ext_nonBTZ`): with `y₀ = κ p`, `z₀ = κ' q`,
  `f = κ' ∘ ψ ∘ κ⁻¹` on the chart image of A3's piece; the type equality decides the case (both
  regular: `localUnique_reg` via `regularChart`; both singular: `localUnique_sing`), the component
  is `localUnique_sing`'s `MapsTo … (connectedComponent y₀)` hypothesis. Only `α ≥ 0` is asked
  (`sing_α` is unconstrained for `α < 0`), and BTZ `y₀` are excluded (those cases are the
  explicit hypotheses of `Geometry.ofLocalModelOfBTZ`). Vacuous for the flat model. -/
  typeAgreement : ∀ U : Set Y, IsOpen U → IsConnected U → ∀ y₀ : Y, y₀ ∉ singY 0 →
    (∃ O : Opens Y, y₀ ∈ O ∧ ∃ r ∈ O,
      (causalityY.lt O r y₀ ∧ causalityY.Iplus O {r} ∩ causalityY.Iminus O {y₀} ⊆ U) ∨
      (causalityY.lt O y₀ r ∧ causalityY.Iplus O {y₀} ∩ causalityY.Iminus O {r} ⊆ U)) →
    ∀ z₀ : Y, ∀ f : Y → Y, (∀ y ∈ U, G.IsLocalStructomorphWithinAt f U y) → InjOn f U →
    MapClusterPt z₀ (𝓝[U] y₀) f →
    (∀ α : ℝ, 0 ≤ α → (y₀ ∈ singY α ↔ z₀ ∈ singY α)) ∧
      ((∃ α : ℝ, 0 ≤ α ∧ y₀ ∈ singY α) → z₀ ∈ connectedComponent y₀)
  /-- **B4, future side, in cone-slice form** (round 4 (2), gx-agreed 2026-11-02: replaces the
  level-set B4 `slice_future` of rounds 1–3; statement verbatim `CBG/FromModel`'s round-3
  `ConeSliceFuture`). At every point `y` off the BTZ locus and in every open `O ∋ y`, a set
  `K ⊆ O` of points of the punctured causal past `J⁻_O(y) ∖ {y}`, off the BTZ locus, such that
  **every open `V ⊇ K` contains a Cauchy surface `Γ` of some open `N ∋ y`, `N ⊆ O`** (`Γ ⊆ N`).
  Flat (`Flat/CBGSlice`, `minkowski_coneSlice`): `K` the closed slice ball
  `{t = t(y) − δ, ‖x − x(y)‖ ≤ δ}` on the past cone of `y`, `N` the diamond over a slightly larger
  slice ball, which an open `V ⊇ K` contains by compactness. Gives A4 future at every boundary
  point off the BTZ locus (`CBG/FromModel`, `slice_future_of_cone`). Asked only off the BTZ locus:
  near a BTZ point the punctured past is a segment of the line (`past_local`), so no cone slice
  exists there. -/
  coneSliceFuture : ∀ y : Y, y ∉ singY 0 → ∀ O : Opens Y, y ∈ O → ∃ K : Set Y, K ⊆ O ∧
    (∀ z ∈ K, z ∉ singY 0 ∧ z ≠ y ∧ causalityY.le O z y) ∧
    ∀ V : Set Y, IsOpen V → K ⊆ V → ∃ (N : Opens Y) (Γ : Set Y), y ∈ N ∧ N ≤ O ∧
      Γ ⊆ N ∧ Γ ⊆ V ∧ causalityY.IsCauchySurfaceOn N Γ
  /-- **B4, past side, in cone-slice form** (round 4 (2), gx-agreed: replaces `slice_past`;
  statement verbatim `CBG/FromModel`'s round-3 `ConeSlicePast`): as `coneSliceFuture` with `K` in
  the punctured causal future `J⁺_O(y) ∖ {y}`, **at every point** (every point is in `Z⁺`,
  `mem_Zplus`; at a BTZ `y` of `E₀` the future cone is large, `Iplus_of_lt`). No time reversal
  (gx D-12(e)). Gives A4 past everywhere (`slice_past_of_cone`). -/
  coneSlicePast : ∀ y : Y, ∀ O : Opens Y, y ∈ O → ∃ K : Set Y, K ⊆ O ∧
    (∀ z ∈ K, z ≠ y ∧ causalityY.le O y z) ∧
    ∀ V : Set Y, IsOpen V → K ⊆ V → ∃ (N : Opens Y) (Γ : Set Y), y ∈ N ∧ N ≤ O ∧
      Γ ⊆ N ∧ Γ ⊆ V ∧ causalityY.IsCauchySurfaceOn N Γ

namespace LocalModel

variable (𝔐 : LocalModel.{u})

attribute [instance] LocalModel.topY LocalModel.closedUnderRestriction LocalModel.locallyConnected
  LocalModel.t2Y

/-- The regular part of the model, `reg(Y)`. -/
def regY : Set 𝔐.Y := {y | ∀ α : ℝ, 0 ≤ α → y ∉ 𝔐.singY α}

/-- A point of `Y` that is not regular lies in some `sing_α`, `α ≥ 0`. -/
theorem exists_mem_singY_of_not_mem_regY {y : 𝔐.Y} (h : y ∉ 𝔐.regY) :
    ∃ α : ℝ, 0 ≤ α ∧ y ∈ 𝔐.singY α := by
  by_contra hcon
  exact h fun α hα hy => hcon ⟨α, hα, hy⟩

/-- A Level-B structure on `M`: an atlas modelled on `Y` with transitions in `G`
(`these.tex:3133`, read through `HasGroupoid`). -/
def Str (M : Type u) [TopologicalSpace M] : Type u :=
  Σ' cs : ChartedSpace 𝔐.Y M, @HasGroupoid 𝔐.Y _ M _ cs 𝔐.G

variable {𝔐}

/-- The causality generated by a Level-B structure. -/
noncomputable def causality {M : Type u} [TopologicalSpace M] (s : 𝔐.Str M) : Causality M :=
  letI := s.1; chartedCausality 𝔐.causalityY M

/-- **Level-B morphisms** (`these.tex:3173`): `LiftPropOn G.IsLocalStructomorphWithinAt`. -/
def IsMor {M N : Type u} [TopologicalSpace M] [TopologicalSpace N] (s : 𝔐.Str M)
    (t : 𝔐.Str N) (W : Opens M) (f : M → N) : Prop :=
  letI := s.1; letI := t.1; ChartedSpace.LiftPropOn 𝔐.G.IsLocalStructomorphWithinAt f W

/-- `sing_α` of a Level-B structure. -/
def sing {M : Type u} [TopologicalSpace M] (s : 𝔐.Str M) (α : ℝ) : Set M :=
  letI := s.1; chartedSing 𝔐.singY M α

variable (𝔐)

/-- The pre-geometry of a local model. `Geometry.ofLocalModelOfBTZ` (package 11, `CBG/FromModel`)
completes it to Level A, the BTZ-point cases of A3/A4 as explicit hypotheses. -/
noncomputable def toPreGeometry : PreGeometry.{u} where
  Str := 𝔐.Str
  causality := causality
  IsMor := IsMor

end LocalModel

/-! ### Developments -/

section Dev

variable (𝔊 : PreGeometry.{u}) {M₀ : Type u} [TopologicalSpace M₀] (s₀ : 𝔊.Str M₀)

/-- **A Cauchy development of `M₀`** (design §1; `these.tex:6246`, Sbierski Def 2.1): an
admissible spacetime (Hausdorff, connected, a structure) with a Cauchy embedding of `M₀` which is
a structure morphism. -/
structure Dev where
  /-- The carrier. -/
  carrier : Type u
  [top : TopologicalSpace carrier]
  [t2 : T2Space carrier]
  [conn : ConnectedSpace carrier]
  /-- Second countable (gx review C2): a singular manifold is « séparé à base dénombrable »
  (`these.tex:1357`, gx `def:singular_manifold_locally_connected`), so `IsETTMaximal` quantifies
  over exactly gx's Cauchy-maximality competitors (B21 Lemma 2.3). Also the size bound (§3.6:
  SC + T0 ↪ `Set ℕ`) applies to every development. -/
  [sc : SecondCountableTopology carrier]
  /-- The structure. -/
  str : 𝔊.Str carrier
  /-- The embedding of `M₀`. -/
  emb : M₀ → carrier
  isCauchyEmbedding : IsCauchyEmbedding (𝔊.causality s₀) (𝔊.causality str) emb
  isMor : 𝔊.IsMor s₀ str ⊤ emb

attribute [instance] Dev.top Dev.t2 Dev.conn Dev.sc

variable {𝔊 s₀}

/-- A morphism of developments: a structure morphism commuting with the embeddings (Sbierski
Def 2.2; `these.tex:6363` for sub-extensions). -/
def Dev.IsMorphism (N N' : Dev 𝔊 s₀) (f : N.carrier → N'.carrier) : Prop :=
  𝔊.IsMor N.str N'.str ⊤ f ∧ f ∘ N.emb = N'.emb

/-- **Universality (DEC-59; Sbierski Thm 2.8)**: every development maps uniquely into `Mbar`. -/
def Dev.IsUniversal (Mbar : Dev 𝔊 s₀) : Prop :=
  ∀ N : Dev 𝔊 s₀, ∃! f : N.carrier → Mbar.carrier, N.IsMorphism Mbar f

/-- **The ETT/Barbot form of maximality**: every morphism out of `Mbar` is bijective. -/
def Dev.IsETTMaximal (Mbar : Dev 𝔊 s₀) : Prop :=
  ∀ (N : Dev 𝔊 s₀) (f : Mbar.carrier → N.carrier), Mbar.IsMorphism N f → Bijective f

end Dev

section DevGeometry

variable (𝔊 : Geometry.{u}) {M₀ : Type u} [TopologicalSpace M₀]

/-- `M₀` itself, as a development of itself. -/
def Dev.self [T2Space M₀] [ConnectedSpace M₀] [SecondCountableTopology M₀]
    (s₀ : 𝔊.Str M₀)
    (hGH : (𝔊.causality s₀).GloballyHyperbolic) {S : Set M₀}
    (hS : (𝔊.causality s₀).IsCauchySurface S) : Dev 𝔊.toPreGeometry s₀ where
  carrier := M₀
  str := s₀
  emb := id
  isCauchyEmbedding := ⟨hGH, hGH, IsEMorphism.id, injective_id, ⟨S, hS, by rwa [image_id]⟩⟩
  isMor := 𝔊.isMor_id s₀ ⊤

variable {𝔊}

/-- The identity is a morphism of developments. -/
theorem Dev.IsMorphism.id {s₀ : 𝔊.Str M₀} (N : Dev 𝔊.toPreGeometry s₀) :
    N.IsMorphism N id :=
  ⟨𝔊.isMor_id _ _, rfl⟩

/-- Morphisms of developments compose. -/
theorem Dev.IsMorphism.comp {s₀ : 𝔊.Str M₀} {N N' N'' : Dev 𝔊.toPreGeometry s₀}
    {f : N.carrier → N'.carrier} {g : N'.carrier → N''.carrier} (hg : N'.IsMorphism N'' g)
    (hf : N.IsMorphism N' f) : N.IsMorphism N'' (g ∘ f) :=
  ⟨𝔊.isMor_comp hg.1 hf.1 (fun _ _ => trivial), by rw [comp_assoc, hf.2, hg.2]⟩

/-- **Uniqueness up to unique isomorphism** (DEC-59; Sbierski Thm 2.8, « unique up to
isometry »; `theo:Cauchy_ext`, « unique à isomorphisme près »): two universal developments are
isomorphic by mutually inverse morphisms, each the unique morphism of its kind. No rigidity is
used. -/
theorem Dev.IsUniversal.unique {s₀ : 𝔊.Str M₀} {M₁ M₂ : Dev 𝔊.toPreGeometry s₀}
    (h₁ : M₁.IsUniversal) (h₂ : M₂.IsUniversal) :
    ∃ (f : M₁.carrier → M₂.carrier) (g : M₂.carrier → M₁.carrier),
      M₁.IsMorphism M₂ f ∧ M₂.IsMorphism M₁ g ∧ g ∘ f = id ∧ f ∘ g = id := by
  obtain ⟨f, hf, -⟩ := h₂ M₁
  obtain ⟨g, hg, -⟩ := h₁ M₂
  obtain ⟨i₁, -, hu₁⟩ := h₁ M₁
  obtain ⟨i₂, -, hu₂⟩ := h₂ M₂
  refine ⟨f, g, hf, hg, ?_, ?_⟩
  · rw [hu₁ _ (hg.comp hf), hu₁ _ (Dev.IsMorphism.id M₁)]
  · rw [hu₂ _ (hf.comp hg), hu₂ _ (Dev.IsMorphism.id M₂)]

/-- **Universal ⇒ ETT-maximal** (DEC-59, kb/0022): uses composition, identity and rigidity (A1)
on the connected Hausdorff target, `M₀` non-empty. -/
theorem Dev.IsUniversal.isETTMaximal [Nonempty M₀] {s₀ : 𝔊.Str M₀}
    {Mbar : Dev 𝔊.toPreGeometry s₀} (h : Mbar.IsUniversal) : Mbar.IsETTMaximal := by
  intro N f hf
  obtain ⟨g, hg, -⟩ := h N
  have hgf : g ∘ f = id := by
    obtain ⟨k, -, hk⟩ := h Mbar
    have h1 : Mbar.IsMorphism Mbar (g ∘ f) :=
      ⟨𝔊.isMor_comp hg.1 hf.1 (fun _ _ => trivial), by rw [comp_assoc, hf.2, hg.2]⟩
    have h2 : Mbar.IsMorphism Mbar id := ⟨𝔊.isMor_id _ _, rfl⟩
    rw [hk _ h1, hk _ h2]
  have hfg : f ∘ g = id := by
    have hV : IsConnected ((⊤ : Opens N.carrier) : Set N.carrier) := by
      rw [Opens.coe_top]; exact isConnected_univ
    let O := (𝔊.isEMorphismOn_of_isMor N.isMor).imageOpens ⊤ le_rfl
    have hO : (O : Set N.carrier).Nonempty :=
      ⟨N.emb (Classical.arbitrary M₀), Classical.arbitrary M₀, trivial, rfl⟩
    have heq : EqOn (f ∘ g) id O := by
      rintro _ ⟨x, -, rfl⟩
      show f (g (N.emb x)) = N.emb x
      rw [show g (N.emb x) = Mbar.emb x from congrFun hg.2 x]
      exact congrFun hf.2 x
    funext z
    exact 𝔊.rigid N.str N.str ⊤ hV (f ∘ g) id (𝔊.isMor_comp hf.1 hg.1 (fun _ _ => trivial))
      (𝔊.isMor_id _ _) O le_top hO heq (show z ∈ (⊤ : Opens N.carrier) from trivial)
  exact ⟨LeftInverse.injective (congrFun hgf), RightInverse.surjective (congrFun hfg)⟩

/-- **ETT-maximal ⇒ universal, given a universal development** (DEC-59: the ETT form is a
corollary): an ETT-maximal development receives a morphism from the universal one's universal
property, bijective by ETT-maximality, whose inverse is a morphism (`isMor_inv`). -/
theorem Dev.IsETTMaximal.isUniversal [Nonempty M₀] {s₀ : 𝔊.Str M₀}
    {M Mbar : Dev 𝔊.toPreGeometry s₀} (hM : M.IsETTMaximal) (hU : Mbar.IsUniversal) :
    M.IsUniversal := by
  obtain ⟨f, hf, -⟩ := hU M
  have hbij := hM Mbar f hf
  haveI : Nonempty M.carrier := ⟨M.emb (Classical.arbitrary M₀)⟩
  have hinv := 𝔊.isMor_inv hf.1 hbij.1.injOn
  have htop : (𝔊.isEMorphismOn_of_isMor hf.1).imageOpens ⊤ le_rfl = ⊤ := by
    apply SetLike.coe_injective
    rw [IsEMorphismOn.coe_imageOpens, Opens.coe_top, image_univ_of_surjective hbij.2,
      Opens.coe_top]
  rw [htop] at hinv
  set k := invFunOn f ((⊤ : Opens M.carrier) : Set M.carrier) with hk
  have hkf : k ∘ f = id := funext fun x =>
    hbij.1.injOn.leftInvOn_invFunOn (show x ∈ ((⊤ : Opens M.carrier) : Set M.carrier) from trivial)
  intro N
  obtain ⟨g, hg, hguniq⟩ := hU N
  refine ⟨k ∘ g, ⟨𝔊.isMor_comp hinv hg.1 (fun _ _ => trivial), ?_⟩, ?_⟩
  · rw [comp_assoc, hg.2, ← hf.2, ← comp_assoc, hkf, id_comp]
  · intro h' hh'
    have : f ∘ h' = g := hguniq _ ⟨𝔊.isMor_comp hf.1 hh'.1 (fun _ _ => trivial),
      by rw [comp_assoc, hh'.2, hf.2]⟩
    rw [← this, ← comp_assoc, hkf, id_comp]

end DevGeometry

/-! ### Why rigidity, Hausdorffness and a size bound: witnesses on the timelike line -/

section Witnesses

/-- **The causal pre-geometry**: structures are causalities, morphisms the abstract
`𝕄≥0`-morphisms `IsEMorphismOn` (DEC-17, ETT §4's reading). CBG fails for it (DEC-60):
`not_exists_isUniversal_halfLineDev`, `not_isETTMaximal_halfLineDev`. -/
def causalPreGeometry : PreGeometry.{u} where
  Str M _ := Causality M
  causality s := s
  IsMor s t W f := IsEMorphismOn s t W f

/-- A continuous strictly increasing map of `ℝ` is an abstract morphism of the timelike line
(generalises `OrderIso.isEMorphism_timelikeLine` of `SubExtension`). -/
theorem isEMorphism_timelikeLine_of_strictMono {f : ℝ → ℝ} (hf : StrictMono f)
    (hc : Continuous f) : IsEMorphism timelikeLine timelikeLine f := by
  have hIcc : ∀ {x y : ℝ}, x ≤ y → f '' Icc x y = Icc (f x) (f y) := fun hxy =>
    hc.continuousOn.image_Icc_of_monotoneOn hxy (hf.monotone.monotoneOn _)
  have hopen : IsOpenMap f := by
    intro U hU
    rw [isOpen_iff_mem_nhds]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU x hx
    have hsub : Icc (x - ε / 2) (x + ε / 2) ⊆ U := fun z hz => hball (by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith [hz.1, hz.2])
    have hIoo : Ioo (f (x - ε / 2)) (f (x + ε / 2)) ⊆ f '' U := by
      intro w hw
      have : w ∈ f '' Icc (x - ε / 2) (x + ε / 2) := by
        rw [hIcc (by linarith)]; exact Ioo_subset_Icc_self hw
      obtain ⟨z, hz, rfl⟩ := this
      exact ⟨z, hsub hz, rfl⟩
    exact Filter.mem_of_superset (Ioo_mem_nhds (hf (by linarith)) (hf (by linarith))) hIoo
  refine
    { continuousOn := hc.continuousOn
      isOpen_image := fun V _ => hopen _ V.isOpen
      map_le := fun V U _ hmaps x y ⟨hxy, hsub⟩ => ⟨hf.monotone hxy, by
        rw [← hIcc hxy]; exact (image_mono hsub).trans (image_subset_iff.2 hmaps)⟩
      map_lt := fun V U _ hmaps x y ⟨hxy, hsub⟩ => ⟨hf hxy, by
        rw [← hIcc hxy.le]; exact (image_mono hsub).trans (image_subset_iff.2 hmaps)⟩
      locally := fun x _ => ⟨⊤, le_rfl, trivial, hf.injective.injOn,
        fun V' _ U hU y _ z _ => ?_⟩ }
  have key : ∀ {a b : ℝ}, a ≤ b → (Icc a b ⊆ (V' : Set ℝ) ↔ Icc (f a) (f b) ⊆ (U : Set ℝ)) :=
    fun hab => by rw [hU, ← hIcc hab, image_subset_image_iff hf.injective]
  constructor
  · show (y ≤ z ∧ Icc y z ⊆ (V' : Set ℝ)) ↔ (f y ≤ f z ∧ Icc (f y) (f z) ⊆ (U : Set ℝ))
    rw [hf.le_iff_le]; exact and_congr_right fun h => key h
  · show (y < z ∧ Icc y z ⊆ (V' : Set ℝ)) ↔ (f y < f z ∧ Icc (f y) (f z) ⊆ (U : Set ℝ))
    rw [hf.lt_iff_lt]; exact and_congr_right fun h => key h.le

/-- The embedding `x ↦ -e^{-x}` of the timelike line onto the half-line `]-∞, 0[`. -/
noncomputable def halfLineEmb (x : ℝ) : ℝ := -Real.exp (-x)

theorem halfLineEmb_strictMono : StrictMono halfLineEmb := fun a b hab => by
  simp only [halfLineEmb, neg_lt_neg_iff]; exact Real.exp_lt_exp.2 (by linarith)

theorem halfLineEmb_neg (x : ℝ) : halfLineEmb x < 0 := neg_neg_of_pos (Real.exp_pos _)

theorem halfLineEmb_isEMorphism : IsEMorphism timelikeLine timelikeLine halfLineEmb :=
  isEMorphism_timelikeLine_of_strictMono halfLineEmb_strictMono (by unfold halfLineEmb; fun_prop)

/-- **The half-line development**: the timelike line `M₀ = ℝ` Cauchy-embedded in `ℝ` onto
`]-∞, 0[`, a development for `causalPreGeometry`. -/
noncomputable def halfLineDev : Dev causalPreGeometry.{0} (M₀ := ℝ) timelikeLine where
  carrier := ℝ
  str := (timelikeLine : Causality ℝ)
  emb := halfLineEmb
  isCauchyEmbedding := ⟨timelikeLine_globallyHyperbolic, timelikeLine_globallyHyperbolic,
    halfLineEmb_isEMorphism, halfLineEmb_strictMono.injective,
    ⟨{0}, timelikeLine_isCauchySurface_zero, by
      rw [image_singleton]; exact timelikeLine_isCauchySurface_singleton _⟩⟩
  isMor := halfLineEmb_isEMorphism

theorem kinkIso_halfLineEmb (x : ℝ) : kinkIso (halfLineEmb x) = halfLineEmb x := by
  rw [kinkIso_apply, if_pos (halfLineEmb_neg x).le]

/-- **Without rigidity there is no universal development** (design §2; DEC-60): for
`causalPreGeometry`, the half-line development has no universal development. If `f` were the
unique morphism into one, `f ∘ kinkIso` would be another (`kinkIso` fixes `]-∞, 0[`), so
`f 1 = f 2`; then `f` is constant on `[1, 2]` (the target is causal), against its local
injectivity. -/
theorem not_exists_isUniversal_halfLineDev :
    ¬ ∃ Mbar : Dev causalPreGeometry.{0} (M₀ := ℝ) timelikeLine, Mbar.IsUniversal := by
  rintro ⟨Mbar, hM⟩
  obtain ⟨f, ⟨hfmor, hfemb⟩, huniq⟩ := hM halfLineDev
  change ℝ → Mbar.carrier at f
  have hf : IsEMorphism timelikeLine Mbar.str f := hfmor
  have hg : halfLineDev.IsMorphism Mbar (f ∘ kinkIso) := by
    refine ⟨IsEMorphism.comp hf (OrderIso.isEMorphism_timelikeLine kinkIso), ?_⟩
    rw [← hfemb]
    funext x
    show f (kinkIso (halfLineEmb x)) = f (halfLineEmb x)
    rw [kinkIso_halfLineEmb]
  have h21 : f 2 = f 1 := by
    have := congrFun (huniq _ hg) (1 : ℝ)
    have h1 : kinkIso 1 = 2 := by rw [kinkIso_apply, if_neg (by norm_num)]; norm_num
    simpa [h1] using this
  have hcaus : (Mbar.str : Causality Mbar.carrier).IsCausal :=
    Mbar.isCauchyEmbedding.globallyHyperbolic_target.1
  have hconst : ∀ t ∈ Icc (1 : ℝ) 2, f t = f 1 := by
    intro t ht
    have hle : ∀ a b : ℝ, a ≤ b → (Mbar.str : Causality Mbar.carrier).le ⊤ (f a) (f b) :=
      fun a b hab => hf.map_le ⊤ ⊤ le_rfl (fun _ _ => trivial)
        (show timelikeLine.le ⊤ a b from ⟨hab, fun _ _ => trivial⟩)
    exact hcaus (h21 ▸ hle t 2 ht.2) (hle 1 t ht.1)
  obtain ⟨V, -, hxV, hinj, -⟩ := hf.locally (3 / 2) trivial
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 V.isOpen (3 / 2) hxV
  set t : ℝ := 3 / 2 + min (ε / 2) (1 / 4) with ht
  have hmin : 0 < min (ε / 2) (1 / 4) := lt_min (by linarith) (by norm_num)
  have hmin' : min (ε / 2) (1 / 4) ≤ 1 / 4 := min_le_right _ _
  have hmin'' : min (ε / 2) (1 / 4) ≤ ε / 2 := min_le_left _ _
  have htV : t ∈ V := hball (by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith)
  have htI : t ∈ Icc (1 : ℝ) 2 := ⟨by linarith, by linarith⟩
  have h32 : (3 / 2 : ℝ) ∈ Icc (1 : ℝ) 2 := ⟨by norm_num, by norm_num⟩
  have := hinj htV hxV ((hconst t htI).trans (hconst _ h32).symm)
  linarith

/-- The map `x ↦ x` (`x ≤ 0`), `x ↦ arctan x` (`x > 0`): a non-surjective Cauchy self-embedding
of the line fixing `]-∞, 0]` (the 1-D form of the DEC-45 finding). -/
noncomputable def arctanSelf (x : ℝ) : ℝ := if x ≤ 0 then x else Real.arctan x

theorem arctanSelf_strictMono : StrictMono arctanSelf := by
  intro a b hab
  unfold arctanSelf
  by_cases ha : a ≤ 0 <;> by_cases hb : b ≤ 0
  · rw [if_pos ha, if_pos hb]; exact hab
  · rw [if_pos ha, if_neg hb]
    exact ha.trans_lt (Real.arctan_pos.2 (lt_of_not_ge hb))
  · exact absurd (hab.le.trans hb) ha
  · rw [if_neg ha, if_neg hb]; exact Real.arctan_strictMono hab

theorem arctanSelf_continuous : Continuous arctanSelf :=
  Continuous.if_le continuous_id Real.continuous_arctan continuous_id continuous_const
    (fun x hx => by simp [hx])

theorem arctanSelf_not_surjective : ¬ Surjective arctanSelf := by
  intro h
  obtain ⟨x, hx⟩ := h 2
  unfold arctanSelf at hx
  split_ifs at hx with h0
  · linarith
  · have := Real.arctan_lt_pi_div_two x
    linarith [Real.pi_le_four]

/-- `arctanSelf` is a morphism of the half-line development into itself. -/
theorem isMorphism_arctanSelf : halfLineDev.IsMorphism halfLineDev arctanSelf := by
  refine ⟨isEMorphism_timelikeLine_of_strictMono arctanSelf_strictMono arctanSelf_continuous, ?_⟩
  funext x
  show arctanSelf (halfLineEmb x) = halfLineEmb x
  rw [arctanSelf, if_pos (halfLineEmb_neg x).le]

/-- `arctanSelf` is a **non-surjective Cauchy self-embedding** of the timelike line
(`IsCauchyEmbedding`: `{0}` is sent to the Cauchy surface `{0}`). -/
theorem isCauchyEmbedding_arctanSelf :
    IsCauchyEmbedding timelikeLine timelikeLine arctanSelf :=
  ⟨timelikeLine_globallyHyperbolic, timelikeLine_globallyHyperbolic,
    isEMorphism_timelikeLine_of_strictMono arctanSelf_strictMono arctanSelf_continuous,
    arctanSelf_strictMono.injective,
    ⟨{0}, timelikeLine_isCauchySurface_zero, by
      rw [image_singleton]; exact timelikeLine_isCauchySurface_singleton _⟩⟩

/-- **Without rigidity the obvious candidate is not maximal** (the arctan self-embedding): the
half-line development `ℝ` is not ETT-maximal for `causalPreGeometry`. -/
theorem not_isETTMaximal_halfLineDev : ¬ halfLineDev.IsETTMaximal :=
  fun h => arctanSelf_not_surjective (h halfLineDev arctanSelf isMorphism_arctanSelf).2

/-- **Rigidity fails for `causalPreGeometry`** (`timelikeLine_not_isRigid`), though `ℝ` is
Hausdorff. -/
theorem not_isRigidFor_causalPreGeometry :
    ¬ IsRigidFor (causalPreGeometry.{0}.IsMor (M := ℝ) (N := ℝ) timelikeLine timelikeLine) :=
  timelikeLine_not_isRigid

/-! #### The branching line: rigidity needs a Hausdorff target -/

/-- The inclusion of `]-∞, 0[` in `ℝ`. -/
abbrev branchInc : ↥(Iio (0 : ℝ)) → ℝ := Subtype.val

/-- **The branching line** (`ETT.tex:1312–1314`): two copies of the timelike line glued along
`]-∞, 0[`. -/
abbrev BranchingLine : Type := Gluing branchInc branchInc

theorem isOpenEmbedding_branchInc : IsOpenEmbedding branchInc :=
  isOpen_Iio.isOpenEmbedding_subtypeVal

/-- The two zeros form a pair of `Cdist`: distinct, not separated. -/
theorem branchingLine_mem_Cdist : ((0 : ℝ), (0 : ℝ)) ∈ Gluing.Cdist branchInc branchInc := by
  rw [Gluing.Cdist_eq isOpenEmbedding_branchInc isOpenEmbedding_branchInc]
  refine ⟨?_, ?_⟩
  · have h0 : (0 : ℝ) ∈ closure (Iio (0 : ℝ)) := by rw [closure_Iio]; exact self_mem_Iic
    refine map_mem_closure (f := fun t : ℝ => (t, t)) (by fun_prop) h0 ?_
    intro t ht
    exact ⟨⟨t, ht⟩, rfl⟩
  · rintro ⟨⟨t, ht⟩, h⟩
    have : t = 0 := (Prod.mk.inj h).1
    exact (lt_irrefl (0 : ℝ)) (this ▸ ht)

/-- The branching line is not Hausdorff. -/
theorem branchingLine_not_t2Space : ¬ T2Space BranchingLine := by
  rw [Gluing.t2Space_iff_Cdist_eq_empty isOpenEmbedding_branchInc isOpenEmbedding_branchInc]
  exact (Set.nonempty_of_mem branchingLine_mem_Cdist).ne_empty

/-- The two timelike lines agree along `]-∞, 0[`. -/
theorem branchingLine_compatibleAlong :
    Gluing.CompatibleAlong branchInc branchInc timelikeLine timelikeLine := by
  intro V₁ V₂ h₁ h₂ hpre u u'
  have hV : V₁ = V₂ := by
    apply SetLike.coe_injective
    ext x
    constructor
    · intro hx
      obtain ⟨w, rfl⟩ := h₁ hx
      have : w ∈ branchInc ⁻¹' (V₂ : Set ℝ) := hpre ▸ hx
      exact this
    · intro hx
      obtain ⟨w, rfl⟩ := h₂ hx
      have : w ∈ branchInc ⁻¹' (V₁ : Set ℝ) := hpre.symm ▸ hx
      exact this
  subst hV
  exact ⟨Iff.rfl, Iff.rfl⟩

/-- The causality of the branching line (`Gluing.causality`). -/
noncomputable def branchingCausality : Causality BranchingLine :=
  Gluing.causality isOpenEmbedding_branchInc isOpenEmbedding_branchInc timelikeLine timelikeLine

/-- The two inclusions of `ℝ` in the branching line are abstract morphisms. -/
theorem isEMorphism_branching_ι₁ :
    IsEMorphism timelikeLine branchingCausality (Gluing.ι₁ branchInc branchInc) :=
  isEMorphism_iff.2 ⟨Gluing.strongMorphism_ι₁ branchingLine_compatibleAlong,
    Gluing.localIsomorphism_ι₁ branchingLine_compatibleAlong⟩

theorem isEMorphism_branching_ι₂ :
    IsEMorphism timelikeLine branchingCausality (Gluing.ι₂ branchInc branchInc) :=
  isEMorphism_iff.2 ⟨Gluing.strongMorphism_ι₂ branchingLine_compatibleAlong,
    Gluing.localIsomorphism_ι₂ branchingLine_compatibleAlong⟩

/-- **Rigidity needs a Hausdorff target** (why `Geometry.rigid` asks `[T2Space N]` and `Dev`
carriers are Hausdorff): any morphism predicate admitting the two inclusions `ι₁, ι₂ : ℝ →`
branching line — open embeddings, read as the identity in each other's charts, so local
isometries of any translation structure — fails rigidity: they agree on `]-∞, 0[` and differ at
`0`. -/
theorem not_isRigidFor_branchingLine (P : Opens ℝ → (ℝ → BranchingLine) → Prop)
    (h₁ : P ⊤ (Gluing.ι₁ branchInc branchInc)) (h₂ : P ⊤ (Gluing.ι₂ branchInc branchInc)) :
    ¬ IsRigidFor P := by
  intro h
  have := h ⊤ (by rw [Opens.coe_top]; exact isConnected_univ) _ _ h₁ h₂ ⟨Iio 0, isOpen_Iio⟩
    le_top ⟨-1, show (-1 : ℝ) < 0 by norm_num⟩
    (fun x (hx : x < 0) => Gluing.ι₁_j₁ (j₁ := branchInc) (j₂ := branchInc) ⟨x, hx⟩)
    (show (0 : ℝ) ∈ ((⊤ : Opens ℝ) : Set ℝ) from trivial)
  exact branchingLine_mem_Cdist.2 this

/-- In particular for the abstract morphisms into the branching line. -/
theorem not_isRigidFor_branchingCausality :
    ¬ IsRigidFor (IsEMorphismOn timelikeLine branchingCausality) :=
  not_isRigidFor_branchingLine _ isEMorphism_branching_ι₁ isEMorphism_branching_ι₂

end Witnesses

end CBG

end Causal
