import CausalScaffold.CBG.Geometry
import CausalScaffold.CBG.CausalConvex
import CausalScaffold.CBG.Injective

/-!
# The maximal common Cauchy development of two developments over a geometry (CBG, step 3)

No label is marked (package 4, design `docs/CBG-DESIGN.md` §3 step 3; DEC-59, DEC-60: CBG is proved
in the framework of rigid morphisms of singular `(G,X)`-manifolds; marking ETT labels is the ETT
campaign's). Cited, unmarked: `prop:Cauchy_pgcd` — `ETT.tex:1945`; `def:common_sub_extension` —
`ETT.tex:1914`; `lem:C_ext_connexe` — `ETT.tex:1932`; `rem:CBG_analytique` — `ETT.tex:1903`;
`theo:CBG` — `ETT.tex:1884`; thesis `prop:Cauchy_pgcd` (`these.tex:6394`); Sbierski 1309.7591,
Def 2.4, Cor 3.2, Lemma 3.3, **Thm 3.4**.

> **Theorem 3.4** (Existence of MCGHD). Given two GHDs $M$ and $M'$ of the same initial data,
> there exists a unique CGHD $U$ of $M$ and $M'$ with the property that if $V$ is another CGHD of
> $M$ and $M'$, then $U$ is an extension of $V$. […] We consider the set $\{U_\alpha\subseteq M\}$
> of all CGHDs of $M$ and $M'$. […] 2. $U$ is globally hyperbolic with Cauchy surface $\iota(M)$
> […] 4. […] For each $\alpha$ there is such an isometric immersion $\psi_\alpha : U_\alpha\to M'$.
> We define $\psi(p) := \psi_\alpha(p)$ for $p\in U_\alpha$. By Corollary 3.2 this is
> well-defined […] 5. That $U$ is maximal follows directly from its definition.
> (Sbierski, p. 14; Def 2.4, p. 11: a CGHD is a GHD $U\subseteq M$ such that $M'$ is an extension
> of $U$.)

> **Proposition** (`prop:Cauchy_pgcd`). […] There exists a common sub-extension $\pgcd$ of $M_1$ and
> $M_2$ which is maximal, and it is unique up to equivalence. *Proof.* Consider the set
> $\mathcal E$ of pairs $(M,\phi_M)$ such that (a) $i_1(M_0)\subset M\subset M_1$, $M$ open, and the
> inclusion $i_1(M_0)\rightarrow M$ is a Cauchy embedding; (b) $\phi_M:M\rightarrow M_2$ is a
> $\mass{\geq0}$-morphism with $\phi_M\circ i_1=i_2$. Put $\pgcd:=\bigcup M$ […] This is well
> defined: […] $M\cap M'$ is connected by Lemma `lem:C_ext_connexe`, and $\phi_M$ and $\phi_{M'}$
> agree on the non-empty open set $i_1(M_0)$, hence on $M\cap M'$ by the rigidity […] If
> $(N,a,b,c)$ is a common sub-extension of $M_1$ and $M_2$, then $(b(N),c\circ b^{-1})\in
> \mathcal E$ […] (`ETT.tex:1945–1966`)

## What is proved (no `sorry` in this file)

* **Principal theorem, Sbierski Thm 3.4 relative to the geometry** (`exists_mcghd`): for two
  developments `N₁`, `N₂ : Dev 𝔊 s₀` of a connected `M₀`, `U := mcghdOpens`, `ψ := mcghdMap` (the
  union of all common Cauchy developments `IsCGHD`, Sbierski Def 2.4 / ETT's `ℰ` with the
  geometry's morphisms) is a common Cauchy development, `ψ` is injective on `U`, `ψ(U)` is an open
  set Cauchy-including `ι₂(M₀)`, and every common Cauchy development lies in `U` with its morphism
  the restriction of `ψ`. Uniqueness: `mcghd_unique`. Rigidity is `Geometry.rigid` (A1,
  `IsRigidFor IsMor`), not `SubExtension.IsRigid`. No hypothesis beyond the geometry and `M₀`
  connected: Lemma 3.3's time function is the interface field `Geometry.timeFunction` (round 2),
  through `Dev.causality_hasTimeFunction`.
* **`prop:Cauchy_pgcd` over the geometry, in ETT's form** (`cauchy_pgcd_geometry`): a maximal
  common sub-development (`CommonSubDev`, `def:common_sub_extension` with developments and
  injective morphisms of developments) exists — the MCGHD, as a development (`mcghdDev`,
  `mcghdSubDev`) — and any two maximal ones are equivalent. ETT's step "`(b(N), c ∘ b⁻¹) ∈ ℰ`"
  is `isCGHD_of_isMorphism`, `mcghd_factor`.
* The ingredients: the gluing step (`IsCGHD.eqOn`: `lem:C_ext_connexe` re-routed + A1), the union
  is a Cauchy inclusion (`isCGHD_mcghd`, via `CBG/CausalConvex`'s `isCauchyInclusion_iSup`: ETT
  gap 2 closed), injectivity (`IsCGHD.injOn`, `CBG/Injective`'s Lemma 3.3 with the time function
  of `Geometry.timeFunction`, `Dev.causality_hasTimeFunction`; for the MCGHD `mcghdMap_injOn`:
  ETT gap 1 closed), the
  image is Cauchy-included (`IsCGHD.isCauchyInclusion_image`, by causal convexity, not by
  transport); and `Geometry.causality_restrict`, the planned lemma of `CBG/Geometry`'s SCOPE:
  the causality of `restrict s W` is the restriction of `causality s`.
* **Witness** (`causal_pgcd_not_unique`): in the causal reading (abstract `IsEMorphism`, no
  rigidity), on the timelike line (local, absolutely minimal), the half-line development has two
  inequivalent maximal common sub-extensions with itself, `(ℝ, ι, id, id)` and
  `(ℝ, ι, id, kinkIso)`.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `M₀` GH singular flat, `i₁`, `i₂` Cauchy extensions | ✓ `N₁ N₂ : Dev 𝔊 s₀` over a `Geometry` (DEC-60); GH of `M₀` is in `Dev.isCauchyEmbedding` |
| `M₀` connected (spacetimes are, `ETT.tex:1502`, `1849`) | ✓ carried `[ConnectedSpace M₀]` (for `lem:C_ext_connexe`) |
| rigidity (`rem:CBG_analytique`, `prop:GX_liouville`) | ✓ `Geometry.rigid` (A1, into Hausdorff targets) |
| `ℰ` (b): a `𝕄≥0`-morphism | ✓ a structure morphism `𝔊.IsMor` (DEC-60); ⚠ the thesis's (b), `these.tex:6407`, asks no morphism at all (finding) |
| `ℰ` (b) / Sbierski Def 2.4: `φ_M` injective | ⚠ weakened: not asked (as ETT prints); derived (`IsCGHD.injOn`) |
| `φ` injective on `∧` (ETT gap 1) | ✓ proved (`IsCGHD.injOn`, Lemma 3.3 in the abstract setting, `CBG/Injective`) from the interface field `Geometry.timeFunction` (A2, interface round 2 (1): a time function on every GH admissible spacetime), via `Dev.causality_hasTimeFunction`; no hypothesis carried |
| `i₁(M₀) → ∧` a Cauchy embedding (ETT gap 2) | ✓ proved from A2 (`curvesExtend`, `causallyArcConnected`) |
| common sub-extension: Cauchy embeddings `M → M₁, M₂` | ✓ `CommonSubDev`: a `Dev` with injective morphisms of developments (Cauchy images automatic) |
| morphism of common sub-extensions: an `𝕄≥0`-morphism commuting with `b`, `c` (`ETT.tex:1926–1927`) | ✓ `CommonSubDev.IsMorphism` also asks `f ∘ ι_X = ι_Y`, redundant given `injective_b` (`CommonSubDev.isMorphism_iff`) |
| carriers T2, connected, second countable (`ETT.tex:255`, `1502`) | ✓ `Dev` carriers; `mcghdDev` is one |

## SCOPE (disclosed)

* **Interface round 2 (1), applied** (design §6): `Geometry` now has the field `timeFunction`
  (GH admissible ⇒ a continuous `T` strictly increasing along `≤`, verbatim the body of
  `Causality.HasTimeFunction`), so the hypothesis `hT : (𝔊.causality N₁.str).HasTimeFunction`
  formerly carried by `IsCGHD.injOn`, `exists_mcghd`, `mcghdSubDev`,
  `CommonSubDev.isMorphism_toMcghd`, `mcghdSubDev_isMaximal`,
  `CommonSubDev.IsMaximal.bijective_toMcghd` and `cauchy_pgcd_geometry` is **removed**: it is
  `Dev.causality_hasTimeFunction` (`𝔊.timeFunction N.str N.causality_globallyHyperbolic`);
  `mcghdMap_injOn` packages it for the MCGHD (what packages 6, 7, 10 consume). No
  hypothesis-taking variant is kept (none had a user outside this campaign's files). The union,
  its maximality, `mcghd_unique` and `mcghdDev` never used a time function.
  `Causality.HasTimeFunction` stays defined here (Geometry cannot name it; the field spells its
  body out). `curvesExtend` stays a separate field (`curvesExtend_of_timeFunction` would derive
  it; not done here).
* `SubExtension.cauchy_pgcd` (causal `IsRigid`) is **untouched** and believed false (design §2,
  DEC-60), **not refuted here**: its rigidity is the wrong hypothesis (`timelikeLine_not_isRigid`,
  `not_exists_isUniversal_halfLineDev`, `causal_pgcd_not_unique` show what fails without it), and
  it carries neither curve extension nor causal arc-connectedness, on which gap 2 rests here.
  `pgcdOpens`/`pgcdMap`/`pgcdMap_eqOn` do not fit (they range over causal morphisms and need the
  causal `IsRigid`); `IsPgcdCandidate` is reused as a consequence (`IsCGHD.isPgcdCandidate`).
* `Geometry` has no inhabitant yet (its SCOPE): no Level-A witness of the hypothesis set is
  given here; the kink witness is in the causal pre-geometry.
* `Geometry.causality_restrict` uses `Flat.LocalIso.rel_of_image` (`Flat/FlatSpacetime.lean`), a
  model-free lemma living in the Barbot campaign's flat module. To keep CBG's build independent of
  that campaign's file, it is **not imported**: a private copy, `rel_of_image_localIso` (same
  statement, same proof), sits in the `Restrict` section, to be deleted once the master moves the
  lemma to a model-free module (REPORT kb_proposals).
* `imageOpens_top` sits in the root namespace `Causal`, beside `Causal.imageOpens`
  (`Causal/Morphism.lean`) of which it is a fact, rather than in `Causal.CBG`/`Causal.Causality`
  (it is about neither a CBG object nor a causality); no collision.
* `CommonSubDev.IsMorphism` asks a morphism of developments (`Dev.IsMorphism`, i.e. also
  `f ∘ ι_X = ι_Y`) where `ETT.tex:1926–1927` asks an `𝕄≥0`-morphism commuting with the embeddings into
  `M₁`, `M₂`: the extra conjunct is redundant given `injective_b`
  (`CommonSubDev.isMorphism_iff`), so `IsMaximal`, `Equivalent` are ETT's.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Filter Function

universe u

/-- **A continuous time function strictly increasing along `≤`** (the hypothesis of
`CBG.injOn_of_injOn_cauchy`, Sbierski Lemma 3.3 in the abstract setting): carried as a named
hypothesis by `CBG/Injective`; over a `Geometry` it is produced by the field `timeFunction`
(interface round 2, `Dev.causality_hasTimeFunction`), whose conclusion is this body verbatim. It
is weaker
than the strict library's `Causality.IsTimeFunction` (`Causal/Morphism.lean:832`, a strong morphism
to `timelikeLine`) and than `IsCauchyTimeFunction` (`Causal/Cauchy.lean:83`), and must not be read
as either: it is exactly the hypothesis form of `curvesExtend_of_timeFunction`
(`CausalScaffold/CurvesExtend.lean:409`). -/
def Causality.HasTimeFunction {M : Type*} [TopologicalSpace M] (C : Causality M) : Prop :=
  ∃ T : M → ℝ, Continuous T ∧ ∀ x y, C.le ⊤ x y → x ≠ y → T x < T y

/-- The image of `⊤ : Opens ↥W` is `W`. -/
theorem imageOpens_top {M : Type*} [TopologicalSpace M] (W : Opens M) :
    imageOpens (⊤ : Opens W) = W :=
  SetLike.coe_injective (by
    show Subtype.val '' ((⊤ : Opens W) : Set W) = (W : Set M)
    rw [Opens.coe_top, image_univ, Subtype.range_coe])

/-- **An open set globally hyperbolic in `M` is globally hyperbolic as a space** with the
restricted causality: relations of `↥W` are those of `W`, its diamonds the preimages of those of
`W`, compact because `↥W → M` is an embedding. -/
theorem Causality.globallyHyperbolic_toSubtype {M : Type*} [TopologicalSpace M] {C : Causality M}
    {W : Opens M} (h : C.GloballyHyperbolicOn W) :
    ((C.restrict W).toSubtype).GloballyHyperbolic := by
  have hle : ∀ x y : W, ((C.restrict W).toSubtype).le ⊤ x y ↔ C.le W x y := fun x y => by
    show C.le (imageOpens (⊤ : Opens W)) x y ↔ _
    rw [imageOpens_top]
  refine ⟨fun x y hxy hyx => Subtype.ext (h.1 ((hle x y).1 hxy) ((hle y x).1 hyx)), fun p q => ?_⟩
  have heq : ((C.restrict W).toSubtype).diamond ⊤ p q =
      Subtype.val ⁻¹' C.diamond W p q := by
    ext z
    rw [mem_preimage, Causality.mem_diamond, Causality.mem_diamond, hle, hle]
  rw [heq, Topology.IsInducing.subtypeVal.isCompact_preimage_iff]
  · exact h.2 p q
  · rw [Subtype.range_coe]
    exact fun z hz => C.le_mem_right (Causality.mem_diamond.1 hz).1

namespace CBG

section Pgcd

variable {𝔊 : Geometry.{u}} {M₀ : Type u} [TopologicalSpace M₀] {s₀ : 𝔊.Str M₀}

/-! ### The causal facts of a development -/

namespace Dev

variable (N : Dev 𝔊.toPreGeometry s₀)

/-- A development is globally hyperbolic (the target of its Cauchy embedding). -/
theorem causality_globallyHyperbolic : (𝔊.causality N.str).GloballyHyperbolic :=
  N.isCauchyEmbedding.globallyHyperbolic_target

/-- Curves extend in a development (A2, `Geometry.curvesExtend`, on GH carriers). -/
theorem causality_curvesExtend : (𝔊.causality N.str).CurvesExtend :=
  𝔊.curvesExtend N.str N.causality_globallyHyperbolic

/-- **A development has a time function** (A2, `Geometry.timeFunction`, interface round 2 (1), on
GH carriers): a continuous `T` strictly increasing along `≤` — the input of Lemma 3.3
(`IsCGHD.injOn`). -/
theorem causality_hasTimeFunction : (𝔊.causality N.str).HasTimeFunction :=
  𝔊.timeFunction N.str N.causality_globallyHyperbolic

/-- A development is causally arc-connected (A2, `SingularFlatAxiomsCorr`). -/
theorem causality_causallyArcConnected : (𝔊.causality N.str).CausallyArcConnected :=
  (𝔊.singularFlatAxioms N.str).causallyArcConnected

/-- The image of a Cauchy surface of `M₀` is a Cauchy surface of the image of `M₀`. -/
theorem isCauchySurfaceOn_range {S : Set M₀} (hS : (𝔊.causality s₀).IsCauchySurface S) :
    (𝔊.causality N.str).IsCauchySurfaceOn N.isCauchyEmbedding.rangeOpens (N.emb '' S) :=
  (N.isCauchyEmbedding.isEMorphism.isCauchySurface_iff N.isCauchyEmbedding.injective S).1 hS

theorem image_subset_range (S : Set M₀) :
    N.emb '' S ⊆ (N.isCauchyEmbedding.rangeOpens : Set N.carrier) := by
  rw [IsCauchyEmbedding.coe_rangeOpens]; exact Set.image_subset_range _ _

theorem emb_mem_range (x : M₀) : N.emb x ∈ N.isCauchyEmbedding.rangeOpens := by
  show N.emb x ∈ (N.isCauchyEmbedding.rangeOpens : Set N.carrier)
  rw [IsCauchyEmbedding.coe_rangeOpens]; exact ⟨x, rfl⟩

/-- **The image of `M₀` is Cauchy-included in the development**: in particular it is globally
hyperbolic, by causal convexity (`CBG/CausalConvex`), which `IsCauchyEmbedding` does not state. -/
theorem isCauchyInclusion_range_top :
    IsCauchyInclusion (𝔊.causality N.str) N.isCauchyEmbedding.rangeOpens ⊤ := by
  obtain ⟨S, hS, hS'⟩ := N.isCauchyEmbedding.exists_cauchy
  have hconv := Causality.causallyConvexIn_of_isCauchySurfaceOn
    N.causality_globallyHyperbolic.1 N.causality_causallyArcConnected
    (Causality.curvesExtendOn_top.2 N.causality_curvesExtend) le_top (N.image_subset_range S)
    (N.isCauchySurfaceOn_range hS) hS'
  exact ⟨le_top, Causality.GloballyHyperbolicOn.of_causallyConvexIn
    N.causality_causallyArcConnected N.causality_globallyHyperbolic hconv,
    N.causality_globallyHyperbolic, _, N.image_subset_range S, N.isCauchySurfaceOn_range hS, hS'⟩

end Dev

/-! ### Common Cauchy developments (Sbierski Def 2.4) -/

variable (N₁ N₂ : Dev 𝔊.toPreGeometry s₀)

/-- **A common Cauchy development of `N₁` and `N₂`, realised in `N₁`** (Sbierski Def 2.4, the CGHD;
ETT's set `ℰ`, `ETT.tex:1951–1955`, with the geometry's morphisms): an open `W ⊆ N₁` into which
the inclusion of `ι₁(M₀)` is a Cauchy inclusion, with a structure morphism `f` on `W` such that
`f ∘ ι₁ = ι₂`. Injectivity of `f` is **not** asked (as in ETT's (b)): it follows from Lemma 3.3
(`IsCGHD.injOn`), so maximality among these is maximality among Sbierski's embeddings too. -/
def IsCGHD (W : Opens N₁.carrier) (f : N₁.carrier → N₂.carrier) : Prop :=
  IsCauchyInclusion (𝔊.causality N₁.str) N₁.isCauchyEmbedding.rangeOpens W ∧
    𝔊.IsMor N₁.str N₂.str W f ∧ f ∘ N₁.emb = N₂.emb

variable {N₁ N₂}

/-- A common Cauchy development is an element of `SubExtension`'s `ℰ` (`IsPgcdCandidate`),
structure morphisms being abstract `𝕄≥0`-morphisms (`isEMorphismOn_of_isMor`). The converse
fails: `ℰ` admits the kink (design §2). -/
theorem IsCGHD.isPgcdCandidate {W : Opens N₁.carrier} {f : N₁.carrier → N₂.carrier}
    (h : IsCGHD N₁ N₂ W f) :
    IsPgcdCandidate N₁.isCauchyEmbedding (𝔊.causality N₂.str) N₂.emb W f :=
  ⟨h.1, 𝔊.isEMorphismOn_of_isMor h.2.1, h.2.2⟩

variable (N₁ N₂)

/-- The map `ι₂ ∘ ι₁⁻¹` on `ι₁(M₀)`. -/
noncomputable def baseMap [Nonempty M₀] : N₁.carrier → N₂.carrier :=
  N₂.emb ∘ invFunOn N₁.emb ((⊤ : Opens M₀) : Set M₀)

/-- **`ι₁(M₀)` itself is a common Cauchy development** (Sbierski: "by Theorem 2.6 this set is
non-empty" — here `M₀` is a development of itself). -/
theorem isCGHD_range [Nonempty M₀] :
    IsCGHD N₁ N₂ N₁.isCauchyEmbedding.rangeOpens (baseMap N₁ N₂) := by
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨-, hG, -, S, hS, hS1, -⟩ := N₁.isCauchyInclusion_range_top
    exact ⟨le_rfl, hG, hG, S, hS, hS1, hS1⟩
  · have hinv := 𝔊.isMor_inv N₁.isMor N₁.isCauchyEmbedding.injective.injOn
    exact 𝔊.isMor_comp N₂.isMor hinv (fun _ _ => trivial)
  · funext x
    show N₂.emb (invFunOn N₁.emb _ (N₁.emb x)) = N₂.emb x
    rw [N₁.isCauchyEmbedding.injective.injOn.leftInvOn_invFunOn
      (show x ∈ ((⊤ : Opens M₀) : Set M₀) from trivial)]

variable {N₁ N₂}

/-- **The gluing step** (Sbierski Cor 3.2; `ETT.tex:1956–1960`): two common Cauchy developments
agree on the intersection of their open sets — it is connected (`lem:C_ext_connexe`, re-routed:
`IsCauchyEmbedding.c_ext_connexe_of_connectedSpace`, `M₀` connected) and the two morphisms agree
on the non-empty open `ι₁(M₀)`, so they agree on it by rigidity of the geometry (A1). -/
theorem IsCGHD.eqOn [ConnectedSpace M₀] {W W' : Opens N₁.carrier}
    {f f' : N₁.carrier → N₂.carrier} (h : IsCGHD N₁ N₂ W f) (h' : IsCGHD N₁ N₂ W' f') :
    EqOn f f' (W ⊓ W' : Opens N₁.carrier) := by
  have hconn := N₁.isCauchyEmbedding.c_ext_connexe_of_connectedSpace h.1 h'.1
    N₁.causality_curvesExtend
  refine 𝔊.rigid N₁.str N₂.str (W ⊓ W') hconn f f' (𝔊.isMor_mono h.2.1 inf_le_left)
    (𝔊.isMor_mono h'.2.1 inf_le_right) N₁.isCauchyEmbedding.rangeOpens (le_inf h.1.1 h'.1.1)
    ?_ ?_
  · obtain ⟨x⟩ := (inferInstance : Nonempty M₀)
    exact ⟨N₁.emb x, N₁.emb_mem_range x⟩
  · intro y hy
    rw [IsCauchyEmbedding.coe_rangeOpens] at hy
    obtain ⟨x, rfl⟩ := hy
    exact (congrFun h.2.2 x).trans (congrFun h'.2.2 x).symm

/-- **Lemma 3.3 for a common Cauchy development** (`CBG/Injective`): its morphism is injective —
by the time function of `N₁` (`Dev.causality_hasTimeFunction`, from the interface field
`Geometry.timeFunction`). -/
theorem IsCGHD.injOn {W : Opens N₁.carrier} {f : N₁.carrier → N₂.carrier}
    (h : IsCGHD N₁ N₂ W f) : InjOn f W := by
  obtain ⟨T, hTc, hTs⟩ := N₁.causality_hasTimeFunction
  obtain ⟨S, hS, -⟩ := N₁.isCauchyEmbedding.exists_cauchy
  have hSW := N₁.isCauchyEmbedding.isCauchySurfaceOn_of_isCauchyInclusion h.1 hS
  have himg : f '' (N₁.emb '' S) = N₂.emb '' S := by rw [← image_comp, h.2.2]
  refine injOn_of_injOn_cauchy (𝔊.isEMorphismOn_of_isMor h.2.1) hTc hTs hSW ?_ ?_
    N₂.causality_globallyHyperbolic.1
  · rintro _ ⟨a, -, rfl⟩ _ ⟨b, -, rfl⟩ hab
    have : N₂.emb a = N₂.emb b :=
      (congrFun h.2.2 a).symm.trans (hab.trans (congrFun h.2.2 b))
    rw [N₂.isCauchyEmbedding.injective this]
  · rw [himg]
    exact (N₂.isCauchyEmbedding.isCauchySurface_image hS).isAcausal
      N₂.causality_causallyArcConnected N₂.causality_curvesExtend

/-- **The image of an injective common Cauchy development is Cauchy-included in `N₂`** (the
other half of "`N₂` is an extension of `W`", Sbierski Def 2.2/2.4): `ψ(W)` contains `ι₂(M₀)`,
`ι₂(Σ)` is a Cauchy surface of `ψ(W)` (transport along the injective morphism) and of `N₂`, so
`ψ(W)` is causally convex in `N₂`, hence globally hyperbolic. -/
theorem IsCGHD.isCauchyInclusion_image {W : Opens N₁.carrier} {f : N₁.carrier → N₂.carrier}
    (h : IsCGHD N₁ N₂ W f) (hinj : InjOn f W) :
    IsCauchyInclusion (𝔊.causality N₂.str) N₂.isCauchyEmbedding.rangeOpens
      ((𝔊.isEMorphismOn_of_isMor h.2.1).imageOpens W le_rfl) := by
  obtain ⟨S, hS, -⟩ := N₁.isCauchyEmbedding.exists_cauchy
  have hSW := N₁.isCauchyEmbedding.isCauchySurfaceOn_of_isCauchyInclusion h.1 hS
  have himg : f '' (N₁.emb '' S) = N₂.emb '' S := by rw [← image_comp, h.2.2]
  have hSsub : N₁.emb '' S ⊆ (W : Set N₁.carrier) :=
    fun _ hx => h.1.1 (N₁.image_subset_range S hx)
  have hV : (𝔊.causality N₂.str).IsCauchySurfaceOn
      ((𝔊.isEMorphismOn_of_isMor h.2.1).imageOpens W le_rfl) (N₂.emb '' S) := by
    rw [← himg]
    exact ((𝔊.isEMorphismOn_of_isMor h.2.1).isCauchySurfaceOn_image_iff hinj le_rfl rfl
      hSsub).1 hSW
  have hsub2 : N₂.emb '' S ⊆
      ((𝔊.isEMorphismOn_of_isMor h.2.1).imageOpens W le_rfl : Set N₂.carrier) := by
    rw [IsEMorphismOn.coe_imageOpens, ← himg]; exact image_mono hSsub
  have hconv := Causality.causallyConvexIn_of_isCauchySurfaceOn
    N₂.causality_globallyHyperbolic.1 N₂.causality_causallyArcConnected
    (Causality.curvesExtendOn_top.2 N₂.causality_curvesExtend) le_top hsub2 hV
    (N₂.isCauchyEmbedding.isCauchySurface_image hS)
  refine ⟨?_, N₂.isCauchyInclusion_range_top.2.1,
    Causality.GloballyHyperbolicOn.of_causallyConvexIn N₂.causality_causallyArcConnected
      N₂.causality_globallyHyperbolic hconv, _, N₂.image_subset_range S,
    N₂.isCauchySurfaceOn_range hS, hV⟩
  intro y hy
  have hy' : y ∈ range N₂.emb := by
    rw [← IsCauchyEmbedding.coe_rangeOpens N₂.isCauchyEmbedding]; exact hy
  obtain ⟨a, rfl⟩ := hy'
  exact ⟨N₁.emb a, h.1.1 (N₁.emb_mem_range a), congrFun h.2.2 a⟩

/-! ### The union -/

variable (N₁ N₂)

/-- **The MCGHD's open set** `⋃_{(W, f) CGHD} W` (Sbierski Thm 3.4; `M₁ ∧ M₂` of `ETT.tex:1956`). -/
def mcghdOpens : Opens N₁.carrier :=
  ⨆ p : {p : Opens N₁.carrier × (N₁.carrier → N₂.carrier) // IsCGHD N₁ N₂ p.1 p.2}, p.1.1

/-- **The MCGHD's morphism**: at `x`, the value of some common Cauchy development containing `x`
(Sbierski: `ψ(p) := ψ_α(p)` for `p ∈ U_α`). -/
noncomputable def mcghdMap [Nonempty M₀] (x : N₁.carrier) : N₂.carrier := by
  classical
  exact if hx : ∃ p : Opens N₁.carrier × (N₁.carrier → N₂.carrier), IsCGHD N₁ N₂ p.1 p.2 ∧ x ∈ p.1
    then (Classical.choose hx).2 x else N₂.emb (Classical.arbitrary M₀)

variable {N₁ N₂}

theorem le_mcghdOpens {W : Opens N₁.carrier} {f : N₁.carrier → N₂.carrier}
    (h : IsCGHD N₁ N₂ W f) : W ≤ mcghdOpens N₁ N₂ :=
  le_iSup (fun p : {p : Opens N₁.carrier × (N₁.carrier → N₂.carrier) // IsCGHD N₁ N₂ p.1 p.2} =>
    p.1.1) ⟨(W, f), h⟩

/-- **`ψ` is well defined** (Sbierski: "by Corollary 3.2 this is well-defined"): it agrees with
every common Cauchy development on its open set. -/
theorem mcghdMap_eqOn [ConnectedSpace M₀] {W : Opens N₁.carrier} {f : N₁.carrier → N₂.carrier}
    (h : IsCGHD N₁ N₂ W f) : EqOn (mcghdMap N₁ N₂) f W := by
  intro x hx
  have hex : ∃ p : Opens N₁.carrier × (N₁.carrier → N₂.carrier),
      IsCGHD N₁ N₂ p.1 p.2 ∧ x ∈ p.1 := ⟨(W, f), h, hx⟩
  simp only [mcghdMap, dif_pos hex]
  obtain ⟨hp, hxp⟩ := Classical.choose_spec hex
  exact hp.eqOn h ⟨hxp, hx⟩

/-- **The union is a common Cauchy development** (Sbierski Thm 3.4, steps 1–4; closes ETT gap 2):
`ι₁(M₀) → U` is a Cauchy inclusion (`isCauchyInclusion_iSup`: the union of Cauchy inclusions,
causally convex in `N₁`), `ψ` is a morphism (locality of morphisms, `isMor_of_locally`, from the
gluing step) and `ψ ∘ ι₁ = ι₂`. -/
theorem isCGHD_mcghd [ConnectedSpace M₀] :
    IsCGHD N₁ N₂ (mcghdOpens N₁ N₂) (mcghdMap N₁ N₂) := by
  refine ⟨?_, ?_, ?_⟩
  · haveI : Nonempty
        {p : Opens N₁.carrier × (N₁.carrier → N₂.carrier) // IsCGHD N₁ N₂ p.1 p.2} :=
      ⟨⟨(_, _), isCGHD_range N₁ N₂⟩⟩
    exact (isCauchyInclusion_iSup N₁.causality_causallyArcConnected
      (Causality.curvesExtendOn_top.2 N₁.causality_curvesExtend)
      N₁.isCauchyInclusion_range_top (fun p => p.2.1) (fun _ => le_top)).1
  · refine 𝔊.isMor_of_locally fun x hx => ?_
    obtain ⟨⟨⟨W, f⟩, h⟩, hxW⟩ := Opens.mem_iSup.1 hx
    exact ⟨W, le_mcghdOpens h, hxW, 𝔊.isMor_congr h.2.1 (mcghdMap_eqOn h).symm⟩
  · funext x
    have h := isCGHD_range N₁ N₂
    exact (mcghdMap_eqOn h (N₁.emb_mem_range x)).trans (congrFun h.2.2 x)

/-- **The MCGHD morphism is injective** (Sbierski Thm 3.4: « isometric embedding »; Lemma 3.3,
`IsCGHD.injOn`, by the interface's `Geometry.timeFunction`): the hypothesis `InjOn mcghdMap
mcghdOpens` that packages 6, 7, 10 carried before interface round 2. -/
theorem mcghdMap_injOn [ConnectedSpace M₀] : InjOn (mcghdMap N₁ N₂) (mcghdOpens N₁ N₂) :=
  isCGHD_mcghd.injOn

/-- **Maximality**: every common Cauchy development lies in the MCGHD, and its morphism is the
restriction of `ψ` ("`U` is an extension of `V`", Sbierski Thm 3.4, step 5). -/
theorem IsCGHD.le_mcghd [ConnectedSpace M₀] {W : Opens N₁.carrier} {f : N₁.carrier → N₂.carrier}
    (h : IsCGHD N₁ N₂ W f) : W ≤ mcghdOpens N₁ N₂ ∧ EqOn f (mcghdMap N₁ N₂) W :=
  ⟨le_mcghdOpens h, (mcghdMap_eqOn h).symm⟩

/-- **Sbierski Theorem 3.4 (existence of the MCGHD), relative to a geometry** — the principal
theorem of this file. For two developments `N₁`, `N₂` of a connected `M₀` over a `Geometry` (A1
rigidity, A2, the time function `Geometry.timeFunction` for Lemma 3.3): there is an open
`U ⊆ N₁` and a map `ψ : N₁ → N₂` such that
* `(U, ψ)` is a common Cauchy development (`ι₁(M₀) → U` a Cauchy inclusion, `ψ` a structure
  morphism on `U`, `ψ ∘ ι₁ = ι₂`);
* `ψ` is injective on `U`, and `ψ(U)` is an open set into which `ι₂(M₀)` is Cauchy-included: `N₂`
  is an extension of `U` (Sbierski Def 2.2, 2.4);
* every common Cauchy development `(W, f)` has `W ⊆ U` and `f = ψ` on `W`.
`U = mcghdOpens N₁ N₂`, `ψ = mcghdMap N₁ N₂`; uniqueness: `mcghd_unique`. -/
theorem exists_mcghd [ConnectedSpace M₀] (N₁ N₂ : Dev 𝔊.toPreGeometry s₀) :
    ∃ (U : Opens N₁.carrier) (ψ : N₁.carrier → N₂.carrier), IsCGHD N₁ N₂ U ψ ∧ InjOn ψ U ∧
      (∃ V : Opens N₂.carrier, (V : Set N₂.carrier) = ψ '' U ∧
        IsCauchyInclusion (𝔊.causality N₂.str) N₂.isCauchyEmbedding.rangeOpens V) ∧
      ∀ (W : Opens N₁.carrier) (f : N₁.carrier → N₂.carrier), IsCGHD N₁ N₂ W f →
        W ≤ U ∧ EqOn f ψ W := by
  have h := isCGHD_mcghd (N₁ := N₁) (N₂ := N₂)
  have hinj := h.injOn
  exact ⟨_, _, h, hinj, ⟨_, rfl, h.isCauchyInclusion_image hinj⟩, fun W f hW => hW.le_mcghd⟩

/-- **Uniqueness of the MCGHD** (Sbierski Thm 3.4, "unique"; `prop:Cauchy_pgcd`, "unique up to
equivalence"): a common Cauchy development containing every other one, with their morphisms as
restrictions, is the MCGHD — same open set, same morphism on it. No time function is used. -/
theorem mcghd_unique [ConnectedSpace M₀] {U : Opens N₁.carrier} {ψ : N₁.carrier → N₂.carrier}
    (h : IsCGHD N₁ N₂ U ψ)
    (hmax : ∀ (W : Opens N₁.carrier) (f : N₁.carrier → N₂.carrier), IsCGHD N₁ N₂ W f →
      W ≤ U ∧ EqOn f ψ W) :
    U = mcghdOpens N₁ N₂ ∧ EqOn ψ (mcghdMap N₁ N₂) U :=
  ⟨le_antisymm (le_mcghdOpens h) (hmax _ _ isCGHD_mcghd).1, (mcghdMap_eqOn h).symm⟩

/-! ### Common sub-developments: the ETT form of the maximality -/

/-- **A common sub-development gives a common Cauchy development** (`ETT.tex:1963–1964`: "If
`(N, a, b, c)` is a common sub-extension of `M₁` and `M₂`, then `(b(N), c ∘ b⁻¹) ∈ ℰ`"): for a
development `X` with morphisms of developments `b : X → N₁` (injective) and `c : X → N₂`, the
open set `b(X)` with `c ∘ b⁻¹` is a common Cauchy development. `b(X)` is globally hyperbolic by
causal convexity in `N₁` (`ι₁(Σ)` is a Cauchy surface of `b(X)` and of `N₁`), which is how the
abstraction's obstruction (4) of `SubExtension.cauchy_pgcd` (transport of global hyperbolicity
along a local isomorphism) is avoided. -/
theorem isCGHD_of_isMorphism (X : Dev 𝔊.toPreGeometry s₀) {b : X.carrier → N₁.carrier}
    {c : X.carrier → N₂.carrier} (hb : X.IsMorphism N₁ b) (hbinj : Injective b)
    (hc : X.IsMorphism N₂ c) [Nonempty X.carrier] :
    IsCGHD N₁ N₂ ((𝔊.isEMorphismOn_of_isMor hb.1).imageOpens ⊤ le_rfl)
      (c ∘ invFunOn b ((⊤ : Opens X.carrier) : Set X.carrier)) := by
  have hbE := 𝔊.isEMorphismOn_of_isMor hb.1
  obtain ⟨S, hS, -⟩ := N₁.isCauchyEmbedding.exists_cauchy
  have hSX : (𝔊.causality X.str).IsCauchySurface (X.emb '' S) :=
    X.isCauchyEmbedding.isCauchySurface_image hS
  have himg : b '' (X.emb '' S) = N₁.emb '' S := by rw [← image_comp, hb.2]
  have hrange : (N₁.isCauchyEmbedding.rangeOpens : Set N₁.carrier) ⊆ hbE.imageOpens ⊤ le_rfl := by
    rw [IsCauchyEmbedding.coe_rangeOpens]
    rintro _ ⟨a, rfl⟩
    exact ⟨X.emb a, trivial, congrFun hb.2 a⟩
  have hV : (𝔊.causality N₁.str).IsCauchySurfaceOn (hbE.imageOpens ⊤ le_rfl) (N₁.emb '' S) := by
    rw [← himg]
    exact (hbE.isCauchySurfaceOn_image_iff hbinj.injOn le_rfl rfl (subset_univ _)).1 hSX
  have hsub : N₁.emb '' S ⊆ (hbE.imageOpens ⊤ le_rfl : Set N₁.carrier) :=
    (N₁.image_subset_range S).trans hrange
  have hconv := Causality.causallyConvexIn_of_isCauchySurfaceOn
    N₁.causality_globallyHyperbolic.1 N₁.causality_causallyArcConnected
    (Causality.curvesExtendOn_top.2 N₁.causality_curvesExtend) le_top hsub hV
    (N₁.isCauchyEmbedding.isCauchySurface_image hS)
  refine ⟨⟨hrange, N₁.isCauchyInclusion_range_top.2.1,
    Causality.GloballyHyperbolicOn.of_causallyConvexIn N₁.causality_causallyArcConnected
      N₁.causality_globallyHyperbolic hconv, _, N₁.image_subset_range S,
    N₁.isCauchySurfaceOn_range hS, hV⟩, ?_, ?_⟩
  · exact 𝔊.isMor_comp hc.1 (𝔊.isMor_inv hb.1 hbinj.injOn) (fun _ _ => trivial)
  · funext a
    rw [comp_apply, ← congrFun hb.2 a, comp_apply, comp_apply,
      hbinj.injOn.leftInvOn_invFunOn (show X.emb a ∈ ((⊤ : Opens X.carrier) : Set X.carrier)
      from trivial)]
    exact congrFun hc.2 a

/-- **The ETT maximality of the MCGHD** (`ETT.tex:1963–1965`): every common sub-development
`(X, b, c)` (`b` injective) factors through the MCGHD: `b(X) ⊆ U` and `ψ ∘ b = c`. -/
theorem mcghd_factor [ConnectedSpace M₀] (X : Dev 𝔊.toPreGeometry s₀)
    {b : X.carrier → N₁.carrier} {c : X.carrier → N₂.carrier} (hb : X.IsMorphism N₁ b)
    (hbinj : Injective b) (hc : X.IsMorphism N₂ c) :
    (∀ x, b x ∈ mcghdOpens N₁ N₂) ∧ mcghdMap N₁ N₂ ∘ b = c := by
  haveI : Nonempty X.carrier := ⟨X.emb (Classical.arbitrary M₀)⟩
  have h := isCGHD_of_isMorphism X hb hbinj hc
  have hx : ∀ x, b x ∈ (𝔊.isEMorphismOn_of_isMor hb.1).imageOpens ⊤ le_rfl := fun x => by
    show b x ∈ (((𝔊.isEMorphismOn_of_isMor hb.1).imageOpens ⊤ le_rfl : Opens N₁.carrier) :
      Set N₁.carrier)
    exact ⟨x, trivial, rfl⟩
  refine ⟨fun x => (le_mcghdOpens h) (hx x), funext fun x => ?_⟩
  rw [comp_apply, mcghdMap_eqOn h (hx x)]
  show c (invFunOn b _ (b x)) = c x
  rw [hbinj.injOn.leftInvOn_invFunOn (show x ∈ ((⊤ : Opens X.carrier) : Set X.carrier)
    from trivial)]

/-! ### The causality of an induced structure (the planned lemma of `Geometry`'s SCOPE) -/

section Restrict

section RelOfImage

open Relation

variable {M' : Type*} {N' : Type*} [TopologicalSpace M'] [TopologicalSpace N']
  {C : Causality M'} {D : Causality N'} {φ : M' → N'}

-- Lifting a chain of image relations along an injective map (private copy of the one in
-- `Flat/FlatSpacetime.lean`, kept here so that CBG does not import a Barbot-campaign module).
omit [TopologicalSpace M'] [TopologicalSpace N'] in
private theorem lift_transGen_image (hinj : Injective φ) {R : M' → M' → Prop}
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

/-- An **injective** local isomorphism into a causality absolutely minimal on every open set
reflects the relations: a relation of `φ(V)` between two images is one of `V`. A **private copy**
of `Flat.LocalIso.rel_of_image` (`Flat/FlatSpacetime.lean`, model-free; same statement, same
proof), so that this CBG module does not import the Barbot campaign's flat module; to be deleted
once the master moves the lemma to a model-free module (REPORT kb_proposals). -/
private theorem rel_of_image_localIso (hφ : LocalIsomorphism C D φ) (hinj : Injective φ)
    (hD : ∀ U : Opens N', D.AbsolutelyMinimalOn U) (V : Opens M') (U : Opens N')
    (hU : (U : Set N') = φ '' V) (x y : M') :
    (D.le U (φ x) (φ y) → C.le V x y) ∧ (D.lt U (φ x) (φ y) → C.lt V x y) := by
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
  constructor
  · intro hxy
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
      lift_transGen_image hinj (R := C.le V) (fun h₁ h₂ => C.le_trans h₁ h₂) hc'
    rwa [← hinj hb] at hxb
  · intro hxy
    have hc := ((hD U) S hS U le_rfl _ _).2 hxy
    have hc' : TransGen (fun a' b' => ∃ a b, a' = φ a ∧ b' = φ b ∧ C.lt V a b) (φ x) (φ y) := by
      refine TransGen.mono (fun a' b' => ?_) hc
      rintro ⟨O, ⟨z, rfl⟩, hab⟩
      have ha := D.lt_mem_left hab
      have hb := D.lt_mem_right hab
      obtain ⟨a, ha', rfl⟩ : a' ∈ φ '' (V ⊓ V₁ z : Opens M') := hOU z ▸ ha
      obtain ⟨b, hb', rfl⟩ : b' ∈ φ '' (V ⊓ V₁ z : Opens M') := hOU z ▸ hb
      exact ⟨a, b, rfl, rfl, C.lt_mono inf_le_left
        (((hV₁ z _ inf_le_right _ (hOU z) a ha' b hb').2).2 hab)⟩
    obtain ⟨b, hb, hxb⟩ :=
      lift_transGen_image hinj (R := C.lt V) (fun h₁ h₂ => C.lt_trans h₁ h₂) hc'
    rwa [← hinj hb] at hxb

end RelOfImage

variable {M : Type u} [TopologicalSpace M]

/-- **The causality of `restrict s W` is the restriction of `causality s`** (the "planned lemma of
package 4" of `CBG/Geometry`'s SCOPE): for every open `V` of `↥W`, `x ≤_V y` for the induced
structure iff `x ≤_{V} y` in `M`. The inclusion is a structure morphism (`isMor_val`), hence an
abstract morphism, giving `→`; it is an injective local isomorphism into a causality absolutely
minimal on every open set (`absolutelyMinimalOn`), giving `←` (`rel_of_image_localIso`, a
private copy of `Flat.LocalIso.rel_of_image`). -/
theorem Geometry.causality_restrict (s : 𝔊.Str M) (W : Opens M) :
    𝔊.causality (𝔊.restrict s W) = ((𝔊.causality s).restrict W).toSubtype := by
  have hval : IsEMorphism (𝔊.causality (𝔊.restrict s W)) (𝔊.causality s) Subtype.val :=
    𝔊.isEMorphismOn_of_isMor (𝔊.isMor_val s W)
  have hloc := (isEMorphism_iff.1 hval).2
  have hmaps : ∀ V : Opens W, MapsTo Subtype.val (V : Set W) (imageOpens V : Set M) :=
    fun V x hx => ⟨x, hx, rfl⟩
  apply Causality.ext_toPrecausality
  ext V x y
  · exact ⟨fun h => hval.map_le V (imageOpens V) le_top (hmaps V) h, fun h =>
      (rel_of_image_localIso hloc Subtype.val_injective (𝔊.absolutelyMinimalOn s) V
        (imageOpens V) rfl x y).1 h⟩
  · exact ⟨fun h => hval.map_lt V (imageOpens V) le_top (hmaps V) h, fun h =>
      (rel_of_image_localIso hloc Subtype.val_injective (𝔊.absolutelyMinimalOn s) V
        (imageOpens V) rfl x y).2 h⟩

end Restrict

/-! ### The MCGHD as a development -/

variable [ConnectedSpace M₀]

instance mcghd_connectedSpace :
    ConnectedSpace (mcghdOpens N₁ N₂) := by
  have h := (isCGHD_mcghd (N₁ := N₁) (N₂ := N₂)).1
  have := N₁.isCauchyEmbedding.c_ext_connexe_of_connectedSpace h h N₁.causality_curvesExtend
  rw [inf_idem] at this
  exact isConnected_iff_connectedSpace.1 this

variable (N₁ N₂) in
/-- **The MCGHD as a development of `M₀`**: the open set `U` with the induced structure
(`restrict`), `M₀` Cauchy-embedded by `ι₁` (corestricted). Connected by `lem:C_ext_connexe`
(re-routed, `U ∩ U`), Hausdorff and second countable as a subspace of `N₁`; globally hyperbolic
and with `ι₁(Σ)` as a Cauchy surface through `Geometry.causality_restrict`. -/
noncomputable def mcghdDev : Dev 𝔊.toPreGeometry s₀ where
  carrier := mcghdOpens N₁ N₂
  str := 𝔊.restrict N₁.str (mcghdOpens N₁ N₂)
  emb x := ⟨N₁.emb x, (isCGHD_mcghd (N₁ := N₁) (N₂ := N₂)).1.1 (N₁.emb_mem_range x)⟩
  isCauchyEmbedding := by
    have h := (isCGHD_mcghd (N₁ := N₁) (N₂ := N₂)).1
    set U := mcghdOpens N₁ N₂
    have hmor : 𝔊.IsMor s₀ (𝔊.restrict N₁.str U) ⊤
        (fun x => (⟨N₁.emb x, h.1 (N₁.emb_mem_range x)⟩ : U)) :=
      (𝔊.isMor_corestrict_iff N₁.str U s₀ ⊤ _).2 N₁.isMor
    have hval : IsEMorphism (𝔊.causality (𝔊.restrict N₁.str U)) (𝔊.causality N₁.str)
        Subtype.val := 𝔊.isEMorphismOn_of_isMor (𝔊.isMor_val N₁.str U)
    obtain ⟨S, hS, -⟩ := N₁.isCauchyEmbedding.exists_cauchy
    refine ⟨N₁.isCauchyEmbedding.globallyHyperbolic_source, ?_, 𝔊.isEMorphismOn_of_isMor hmor,
      fun a b hab => N₁.isCauchyEmbedding.injective (congrArg Subtype.val hab), S, hS, ?_⟩
    · rw [Geometry.causality_restrict]
      exact Causality.globallyHyperbolic_toSubtype h.2.2.1
    · have hU : ((U : Set N₁.carrier)) = Subtype.val '' ((⊤ : Opens U) : Set U) := by
        rw [Opens.coe_top, image_univ, Subtype.range_coe]
      refine (hval.isCauchySurfaceOn_image_iff Subtype.val_injective.injOn le_rfl hU
        (subset_univ _)).2 ?_
      rw [image_image]
      exact N₁.isCauchyEmbedding.isCauchySurfaceOn_of_isCauchyInclusion h hS
  isMor := (𝔊.isMor_corestrict_iff N₁.str _ s₀ ⊤ _).2 N₁.isMor

/-- The inclusion `U → N₁` is a morphism of developments. -/
theorem mcghdDev_isMorphism_val :
    (mcghdDev N₁ N₂).IsMorphism N₁ (Subtype.val : mcghdOpens N₁ N₂ → N₁.carrier) :=
  ⟨𝔊.isMor_val N₁.str _, rfl⟩

/-- `ψ` restricted to `U` is a morphism of developments `U → N₂`. -/
theorem mcghdDev_isMorphism_map :
    (mcghdDev N₁ N₂).IsMorphism N₂
      (mcghdMap N₁ N₂ ∘ (Subtype.val : mcghdOpens N₁ N₂ → N₁.carrier)) :=
  ⟨Geometry.IsMor.restrict 𝔊 (isCGHD_mcghd (N₁ := N₁) (N₂ := N₂)).2.1, by
    funext x; exact congrFun (isCGHD_mcghd (N₁ := N₁) (N₂ := N₂)).2.2 x⟩

end Pgcd

/-! ### `prop:Cauchy_pgcd` in the geometry: maximal common sub-developments -/

section SubDev

variable {𝔊 : Geometry.{u}} {M₀ : Type u} [TopologicalSpace M₀] {s₀ : 𝔊.Str M₀}

variable (N₁ N₂ : Dev 𝔊.toPreGeometry s₀) in
/-- **A common sub-development** (`def:common_sub_extension`, `ETT.tex:1914`, over a geometry): a
development `X` of `M₀` with morphisms of developments `b : X → N₁`, `c : X → N₂`, both
injective — Cauchy embeddings (`ETT.tex:1917–1918`; their Cauchy surfaces are automatic, the images
of `ι_X(Σ)`). -/
structure CommonSubDev where
  /-- The development. -/
  X : Dev 𝔊.toPreGeometry s₀
  /-- Its embedding into `N₁`. -/
  b : X.carrier → N₁.carrier
  /-- Its embedding into `N₂`. -/
  c : X.carrier → N₂.carrier
  isMorphism_b : X.IsMorphism N₁ b
  isMorphism_c : X.IsMorphism N₂ c
  injective_b : Injective b
  injective_c : Injective c

variable {N₁ N₂ : Dev 𝔊.toPreGeometry s₀}

namespace CommonSubDev

/-- A morphism of common sub-developments (`ETT.tex:1926–1927`): a morphism of developments commuting
with the embeddings into `N₁` and `N₂`. -/
def IsMorphism (X Y : CommonSubDev N₁ N₂) (f : X.X.carrier → Y.X.carrier) : Prop :=
  X.X.IsMorphism Y.X f ∧ Y.b ∘ f = X.b ∧ Y.c ∘ f = X.c

/-- **The conjunct `f ∘ ι_X = ι_Y` is redundant**: a morphism of common sub-developments is
exactly ETT's (`ETT.tex:1926–1927`), a structure morphism commuting with the embeddings into `N₁` and
`N₂` — compatibility with the embeddings of `M₀` follows, `Y.b` being injective and
`b ∘ ι = ι₁` on both sides. -/
theorem isMorphism_iff (X Y : CommonSubDev N₁ N₂) (f : X.X.carrier → Y.X.carrier) :
    X.IsMorphism Y f ↔ 𝔊.IsMor X.X.str Y.X.str ⊤ f ∧ Y.b ∘ f = X.b ∧ Y.c ∘ f = X.c := by
  refine ⟨fun h => ⟨h.1.1, h.2⟩, fun ⟨hf, hb, hc⟩ => ⟨⟨hf, funext fun a => Y.injective_b ?_⟩,
    hb, hc⟩⟩
  have h1 := congrFun hb (X.X.emb a)
  have h2 := congrFun X.isMorphism_b.2 a
  have h3 := congrFun Y.isMorphism_b.2 a
  simp only [comp_apply] at h1 h2 h3
  rw [comp_apply, h1, h2, h3]

/-- Equivalent common sub-developments: a bijective morphism (`ETT.tex:1927–1928`). -/
def Equivalent (X Y : CommonSubDev N₁ N₂) : Prop :=
  ∃ f, X.IsMorphism Y f ∧ Bijective f

/-- A maximal common sub-development: every morphism out of it is bijective (`ETT.tex:1928–1929`). -/
def IsMaximal (X : CommonSubDev N₁ N₂) : Prop :=
  ∀ (Y : CommonSubDev N₁ N₂) (f : X.X.carrier → Y.X.carrier), X.IsMorphism Y f → Bijective f

end CommonSubDev

variable [ConnectedSpace M₀]

variable (N₁ N₂) in
/-- **The MCGHD as a common sub-development** (injective by Lemma 3.3, `IsCGHD.injOn`). -/
noncomputable def mcghdSubDev : CommonSubDev N₁ N₂ where
  X := mcghdDev N₁ N₂
  b := Subtype.val
  c := mcghdMap N₁ N₂ ∘ Subtype.val
  isMorphism_b := mcghdDev_isMorphism_val
  isMorphism_c := mcghdDev_isMorphism_map
  injective_b := Subtype.val_injective
  injective_c := fun x y hxy => Subtype.ext (((isCGHD_mcghd (N₁ := N₁) (N₂ := N₂)).injOn) x.2
    y.2 hxy)

/-- **Every common sub-development maps into the MCGHD**, by `x ↦ b x` (`mcghd_factor`). -/
theorem CommonSubDev.isMorphism_toMcghd (X : CommonSubDev N₁ N₂) :
    X.IsMorphism (mcghdSubDev N₁ N₂)
      (fun x => ⟨X.b x, (mcghd_factor X.X X.isMorphism_b X.injective_b X.isMorphism_c).1 x⟩) := by
  have hf := mcghd_factor X.X X.isMorphism_b X.injective_b X.isMorphism_c
  refine ⟨⟨(𝔊.isMor_corestrict_iff N₁.str _ X.X.str ⊤ _).2 X.isMorphism_b.1, ?_⟩, rfl, ?_⟩
  · funext a
    exact Subtype.ext (congrFun X.isMorphism_b.2 a)
  · exact hf.2

/-- **The MCGHD is a maximal common sub-development** (`prop:Cauchy_pgcd`, existence): a morphism
`f` out of it is injective (`b ∘ f` is the inclusion) and onto (every common sub-development lies
in `U`, `mcghd_factor`). -/
theorem mcghdSubDev_isMaximal : (mcghdSubDev N₁ N₂).IsMaximal := by
  intro Y f hf
  have hb : ∀ x, Y.b (f x) = x.1 := fun x => congrFun hf.2.1 x
  refine ⟨fun x y hxy => Subtype.ext (by rw [← hb x, ← hb y, hxy]), fun y => ?_⟩
  have hy := (mcghd_factor Y.X Y.isMorphism_b Y.injective_b Y.isMorphism_c).1 y
  exact ⟨⟨Y.b y, hy⟩, Y.injective_b (hb _)⟩

/-- A maximal common sub-development is equivalent to the MCGHD, by the morphism into it. -/
theorem CommonSubDev.IsMaximal.bijective_toMcghd {X : CommonSubDev N₁ N₂} (hX : X.IsMaximal) :
    Bijective (fun x => (⟨X.b x, (mcghd_factor X.X X.isMorphism_b X.injective_b
      X.isMorphism_c).1 x⟩ : (mcghdSubDev N₁ N₂).X.carrier)) :=
  hX _ _ X.isMorphism_toMcghd

/-- **`prop:Cauchy_pgcd` over a geometry** (`ETT.tex:1945`, "There exists a common sub-extension
`∧` of `M₁` and `M₂` which is maximal, and it is unique up to equivalence"), in the framework of
rigid morphisms (DEC-60): for two developments of a connected `M₀` (Lemma 3.3 by the interface's
`Geometry.timeFunction`), a maximal common sub-development exists — the MCGHD — and any two are
equivalent. -/
theorem cauchy_pgcd_geometry (N₁ N₂ : Dev 𝔊.toPreGeometry s₀) :
    (∃ X : CommonSubDev N₁ N₂, X.IsMaximal) ∧
      ∀ X Y : CommonSubDev N₁ N₂, X.IsMaximal → Y.IsMaximal → X.Equivalent Y := by
  refine ⟨⟨_, mcghdSubDev_isMaximal⟩, fun X Y hX hY => ?_⟩
  set Z := mcghdSubDev N₁ N₂
  set gX : X.X.carrier → Z.X.carrier := fun x =>
    ⟨X.b x, (mcghd_factor X.X X.isMorphism_b X.injective_b X.isMorphism_c).1 x⟩
  set gY : Y.X.carrier → Z.X.carrier := fun x =>
    ⟨Y.b x, (mcghd_factor Y.X Y.isMorphism_b Y.injective_b Y.isMorphism_c).1 x⟩
  have hgX : X.IsMorphism Z gX := X.isMorphism_toMcghd
  have hgY : Y.IsMorphism Z gY := Y.isMorphism_toMcghd
  have bX : Bijective gX := hX.bijective_toMcghd
  have bY : Bijective gY := hY.bijective_toMcghd
  haveI : Nonempty Y.X.carrier := ⟨Y.X.emb (Classical.arbitrary M₀)⟩
  set k := invFunOn gY ((⊤ : Opens Y.X.carrier) : Set Y.X.carrier) with hk
  have hkY : ∀ z, gY (k z) = z := fun z =>
    (bY.surjective.surjOn (t := univ) |>.rightInvOn_invFunOn) (show z ∈ univ from trivial)
  have hYk : ∀ y, k (gY y) = y := fun y =>
    bY.1.injOn.leftInvOn_invFunOn (show y ∈ ((⊤ : Opens Y.X.carrier) : Set Y.X.carrier)
      from trivial)
  have hinv := 𝔊.isMor_inv hgY.1.1 bY.1.injOn
  have htop : (𝔊.isEMorphismOn_of_isMor hgY.1.1).imageOpens ⊤ le_rfl = ⊤ := by
    apply SetLike.coe_injective
    rw [IsEMorphismOn.coe_imageOpens, Opens.coe_top, image_univ_of_surjective bY.2,
      Opens.coe_top]
  rw [htop] at hinv
  refine ⟨k ∘ gX, ⟨⟨𝔊.isMor_comp hinv hgX.1.1 (fun _ _ => trivial), ?_⟩, ?_, ?_⟩, ?_⟩
  · funext a
    show k (gX (X.X.emb a)) = Y.X.emb a
    rw [show gX (X.X.emb a) = gY (Y.X.emb a) from
      (congrFun hgX.1.2 a).trans (congrFun hgY.1.2 a).symm, hYk]
  · funext x
    show Y.b (k (gX x)) = X.b x
    have := congrFun hgY.2.1 (k (gX x))
    simp only [comp_apply, hkY] at this
    rw [← this]; rfl
  · funext x
    show Y.c (k (gX x)) = X.c x
    have h1 := congrFun hgY.2.2 (k (gX x))
    have h2 := congrFun hgX.2.2 x
    simp only [comp_apply, hkY] at h1 h2
    rw [← h1, h2]
  · exact ⟨fun x y hxy => bX.1 (by
      have := congrArg gY hxy; simpa only [comp_apply, hkY] using this),
      fun y => by
        obtain ⟨x, hx⟩ := bX.2 (gY y)
        exact ⟨x, by simp only [comp_apply, hx, hYk]⟩⟩

end SubDev

/-! ### Why the causal reading fails: two inequivalent maximal common sub-extensions -/

section KinkWitness

/-- `kinkIso` is a Cauchy self-embedding of the timelike line (it fixes `0`). -/
theorem isCauchyEmbedding_kinkIso : IsCauchyEmbedding timelikeLine timelikeLine kinkIso :=
  ⟨timelikeLine_globallyHyperbolic, timelikeLine_globallyHyperbolic,
    OrderIso.isEMorphism_timelikeLine kinkIso, kinkIso.injective,
    ⟨{0}, timelikeLine_isCauchySurface_zero, by
      rw [image_singleton]; exact timelikeLine_isCauchySurface_singleton _⟩⟩

/-- The common sub-extension `(ℝ, ι, id, c)` of the half-line development with itself
(`M₀ = ℝ`, `i₁ = i₂ = halfLineEmb` onto `]-∞, 0[`), for a Cauchy self-embedding `c` fixing
`]-∞, 0[`. -/
noncomputable def halfLineSub (c : ℝ → ℝ) (hc : IsCauchyEmbedding timelikeLine timelikeLine c)
    (hfix : c ∘ halfLineEmb = halfLineEmb) :
    CommonSubExtension timelikeLine timelikeLine timelikeLine halfLineEmb halfLineEmb where
  carrier := ℝ
  causality := timelikeLine
  a := halfLineEmb
  b := id
  c := c
  ha := halfLineDev.isCauchyEmbedding
  hb := timelikeLine_isCauchyEmbedding_id
  hc := hc
  comm₁ := rfl
  comm₂ := hfix

theorem halfLineSub_isMaximal (c : ℝ → ℝ) (hc : IsCauchyEmbedding timelikeLine timelikeLine c)
    (hfix : c ∘ halfLineEmb = halfLineEmb) : (halfLineSub c hc hfix).IsMaximal := by
  rintro Y f ⟨-, hb, -⟩
  have hb' : ∀ x, Y.b (f x) = x := fun x => congrFun hb x
  exact ⟨fun x y hxy => by rw [← hb' x, ← hb' y, hxy],
    fun y => ⟨Y.b y, Y.hb.injective (hb' _)⟩⟩

/-- **`prop:Cauchy_pgcd`'s uniqueness fails in the causal reading** (ETT §4's `𝕄≥0`-morphisms
read as abstract `IsEMorphism`, DEC-17, without rigidity; design §2; DEC-60): on the timelike
line — a **local** causality, absolutely minimal (`timelikeLine_absolutelyMinimal`), kb/0014,
kb/0019 — the half-line development has two
maximal common sub-extensions with itself, `(ℝ, ι, id, id)` and `(ℝ, ι, id, kinkIso)`, which are
not equivalent (a morphism must be `id` by the first leg and `kinkIso` by the second). This is
the uniqueness half of the design's §2 kink witness (`timelikeLine_not_isRigid`,
`not_exists_isUniversal_halfLineDev`); it does not refute `SubExtension.cauchy_pgcd`, which
carries the causal `IsRigid`, false on this line. -/
theorem causal_pgcd_not_unique :
    ∃ X Y : CommonSubExtension timelikeLine timelikeLine timelikeLine halfLineEmb halfLineEmb,
      X.IsMaximal ∧ Y.IsMaximal ∧ ¬ X.Equivalent Y := by
  have hfix : kinkIso ∘ halfLineEmb = halfLineEmb := funext kinkIso_halfLineEmb
  refine ⟨halfLineSub id timelikeLine_isCauchyEmbedding_id rfl,
    halfLineSub kinkIso isCauchyEmbedding_kinkIso hfix, halfLineSub_isMaximal _ _ _,
    halfLineSub_isMaximal _ _ _, ?_⟩
  rintro ⟨f, ⟨-, hb, hc⟩, -⟩
  have hf : f (1 : ℝ) = (1 : ℝ) := congrFun hb (1 : ℝ)
  have h1 := congrFun hc (1 : ℝ)
  change kinkIso (f (1 : ℝ)) = (1 : ℝ) at h1
  rw [hf, kinkIso_apply, if_neg (by norm_num)] at h1
  norm_num at h1

end KinkWitness

end CBG

end Causal
