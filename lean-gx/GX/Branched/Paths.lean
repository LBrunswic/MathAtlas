import GX.Branched.Universality

/-!
# Paths and the maximal branched covering possibly branched over `S` (§3.3)

Packages WP-26e, WP-27d, WP-35a, WP-40a; `RamcovGX.tex:1189–1416`; rulings DEC-55, DEC-56,
DEC-68 (a)(b), DEC-70, DEC-79 (a)(b). "Almost trivial" is the literal compact-open form (`…CC`
names); see SCOPE (a).

* **`def:almost_trivial_loop`** — `RamcovGX.tex:1210`: `GX.AlmostTrivialCC`, `GX.OmegaSet`,
  `GX.MemOmega`; homotopy form `GX.AlmostTrivial`, `GX.almostTrivialCC_iff`.
* **`ex:consider_carthesian_coordinates_usual`** — `RamcovGX.tex:1214` (`S₂` by DEC-68 (a)):
  `GX.carthesian_piOne_S₁`, `GX.carthesian_piOne_S₂`, `GX.carthesian_S₁_trivial`,
  `GX.carthesian_S₂_almostTrivial`, `GX.carthesian_S₂_not_trivial` (`GX.IsHomTrivial`, DEC-56 (g)).
* **`def:almost_homotopic_paths`** — `RamcovGX.tex:1262`: `GX.AlmostHomotopicCC`.
* **`rem:implicitely_two_almost_homotopic`** — `RamcovGX.tex:1268`: `GX.AlmostHomotopicCC.ends`.
* **`lem:almost_homotopic_carac`** — `RamcovGX.tex:1271` (`U` slsc, DEC-68 (b)):
  `GX.almost_homotopic_carac_cc_component`, `GX.almost_homotopic_carac_cc`,
  `GX.AlmostTrivialCC.of_carac_component`, `GX.AlmostTrivialCC.of_carac`.
* **`lem:hausdorff_first_countable_connected`** — `RamcovGX.tex:1290` (`U` slsc, DEC-68 (b)):
  `GX.hausdorff_first_countable_connected_cc`, `GX.AlmostHomotopicCC.trans`.
* **`lem:almost_homotopic_carac2`** — `RamcovGX.tex:1306` (`\widetilde Y^S` of `prop:universality`,
  DEC-79 (a)): `GX.almost_homotopic_carac2_cc`, `GX.almost_homotopic_carac2_of_isMaximal_cc`.
* **`theo:ramified_covering_path`** — `RamcovGX.tex:1322` (`Y ∖ S` slsc, DEC-70; (d) DEC-79 (b)):
  `GX.ramified_covering_path`, `GX.omegaEnd_isBranchedCovering`, `GX.OmegaQuot`, `GX.OmegaRel`.
* **`def:covering_branched_two_paths`** — `RamcovGX.tex:1385`: `GX.PHomotopic`, `GX.FreePath`.
* **`prop:general_fiber_path`** — `RamcovGX.tex:1390`: `GX.general_fiber_path`, `GX.PiOneP`.
* **`prop:general_fiber_path_universal`** — `RamcovGX.tex:1399`: `GX.general_fiber_path_universal`,
  `GX.PiOneU`, `GX.FreeHomotopic`.
* **`ex:consider_fiber_above_homeomorphic`** — `RamcovGX.tex:1409`: `GX.fiber_above_homeomorphic`
  (`GX.fibS`, `GX.fibD`, `GX.towerHomeomorph`, `GX.not_locallyCompactSpace_nat_pi`).

> A loop $\gamma\in \Omega(x,x,\U)$ is almost trivial with respect to $\U$ if its connected
> component in $\Omega(x,x,\U)$ intersects $\Omega(x,x,\V\cap \U)$ for all neighborhood $\V$ of $x$.
>
> Two paths $\gamma_1,\gamma_2 \in \Omega(x,y,\U)$ are almost homotopic with respect to $\U$ if
> the loop $(\gamma_2)^{-1}*\gamma_1$ is almost trivial with respect to $\U$.
>
> Then, $\varphi$ induces a branched covering $X \xrightarrow{\overline\varphi} Y$ isomorphic to
> $\widetilde Y^S \xrightarrow{p} Y$.
>
> Consider $Y = \RR^2$ and $S=\{(\frac{1}{n},0)~:~n\in \N^*\cup\{\infty\}\}$. The fiber above
> $(0,0)$ in $\widetilde Y^S$ is homeomorphic to $\mathbb Z^\N$ endowed with the weak topology;
> hence is not locally compact.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `def:almost_trivial_loop`, `def:almost_homotopic_paths`: `X` Hausdorff, LPC; `U` open; `x ∈ closure U` | ⚠ weakened: not used by the definitions |
| `lem:almost_homotopic_carac`, `lem:hausdorff…`: `X` Hausdorff, first countable, connected, LPC; `U` open | ✓ `X` LPC, `U` open carried; Hausdorff, first countable, connected not used |
| `lem:almost_homotopic_carac`, `lem:hausdorff…`: `U` semilocally simply connected (DEC-68 (b)) | ✓ carried, used only by (i) ⇒ (ii) and by transitivity |
| `lem:hausdorff…`: `(x,y) ∈ U × closure U` | ✓ `x ∈ U` carried; `y ∈ closure U` not used |
| `lem:almost_homotopic_carac2`: `\widetilde Y^S` maximal possibly branched over `S` | ✓ read (DEC-79 (a)): `\widetilde Y^S` is the covering of `prop:universality`, so `S` skeletal and `Y ∖ S` slsc (`Y` connected, DEC-66 (b)); `GX.almost_homotopic_carac2_of_isMaximal_cc` for any maximal covering under the same hypotheses; SCOPE (i) |
| `lem:almost_homotopic_carac2`: `Y`, `X` T2, LPC, first countable | ✓ carried (§3 standing assumption, l.815, DEC-66 (a)) |
| `theo:ramified_covering_path`: `Y` first countable, connected, LPC, Hausdorff; `S` skeletal | ✓ carried |
| `theo:ramified_covering_path`: `Y ∖ S` semilocally simply connected (DEC-70) | ✓ carried (omitted in print, l.1322; used at l.1349) |
| `prop:general_fiber_path`: `p` a covering branched over `S` | ✓ branched covering, a covering over `Y ∖ S` (`GX.isCoveringMap_restrict_compl`), `S` skeletal (as the branching locus is); `X` LPC, `Y` T1, loc. connected (standing assumptions, l.815, l.962) |
| `prop:general_fiber_path_universal` | ✓ carried |
| `ex:consider_fiber_above_homeomorphic`: `Y = ℝ²` | ✓ `ℂ`; `S` skeletal and `ℂ ∖ S` slsc proved, not assumed |

## SCOPE (disclosed)

(a) DEC-55: "almost trivial" is the literal compact-open form `GX.AlmostTrivialCC`. The proofs of
the paper use homotopies; the literal form is related to them by `GX.almostTrivialCC_iff` (for `U`
open, semilocally simply connected, `X` LPC) and by `GX.AlmostTrivial.almostTrivialCC` (always).
(b) `*` is "any parameterization": `GX.splice` keeps `γ` on `[0,t₀] ∪ [t₁,1]`. (c) DEC-56:
"standard neighbourhood" (l.1311) is `GX.IsStandardNbhd`. (d) DEC-79 (b) (covered by DEC-70):
`X` of `theo:ramified_covering_path` carries the quotient of the compact-open topology of `Ω`,
the quotient being by `GX.OmegaRel` (an equivalence relation, `GX.omegaRel_equivalence`).
(e) DEC-56: the paths of `def:covering_branched_two_paths` and of `π₁(a,U)` lie in `Y ∖ S`; "up to
homotopy" is homotopy in `Y ∖ S` with start fixed and free end in `U` (`GX.FreeHomotopic`). (f) DEC-56: `≃` of the fibre
propositions is an embedding onto the limit, the `π₁` discrete. (g) DEC-56: "homotopically
trivial" (l.1219) is `GX.IsHomTrivial`. (g') DEC-68 (a): `S₂` is the topologist's sine curve
with its limit segment in the plane `{z = 0}` (as printed, l.1216, `{y = sin(1/x)}` is a surface
of `ℝ³` and `S₂` is not closed). (h) DEC-68 (b): `U` is semilocally simply connected in
`lem:almost_homotopic_carac` and `lem:hausdorff_first_countable_connected`; "homotopic in
`Ω(x,x,U)`" of item (ii) is read literally (same compact-open component,
`GX.almost_homotopic_carac_cc_component`), the homotopy form being proved as well. (i) DEC-70:
`theo:ramified_covering_path` carries "`Y ∖ S` semilocally simply connected"; DEC-79 (b): DEC-70
covers its reading (d). DEC-79 (a): `\widetilde Y^S` of `lem:almost_homotopic_carac2` (l.1307, "a
maximal covering possibly branched above some `S`") is the covering of `prop:universality`, so `S`
skeletal and `Y ∖ S` slsc (`Y` connected by DEC-66 (b)); the proof at l.1316 uses that
`p⁻¹(Y ∖ S)` is simply connected. Certified in full under that reading, marked
(`GX.almost_homotopic_carac2_cc`; any maximal covering under the same hypotheses:
`GX.almost_homotopic_carac2_of_isMaximal_cc`). (j) The homotopy-form names `GX.AlmostTrivial`,
`GX.AlmostHomotopic` are kept because `GX.Branched.Galois` consumes them. Further declarations of
the rows: `GX.AlmostTrivial.almostTrivialCC`, `GX.AlmostTrivialCC.almostTrivial`,
`GX.eventually_almostTrivialAt_iff`, `GX.eventually_homotopic_family`, `GX.cartS₁`, `GX.cartS₂`,
`GX.cartDeg`, `GX.cartHE`, `GX.cartDeg₂`, `GX.cart_middle_homotopic`, `GX.cartCirc`,
`GX.not_isHomTrivial_cartγ`, `GX.AlmostHomotopicCC.mem`, `GX.splice`, `GX.almost_homotopic_carac`,
`GX.almostHomotopicCC_refl`, `GX.AlmostHomotopicCC.symm`, `GX.maxBranched_existsUnique_lift`,
`GX.IsStandardNbhd`, `GX.IsSpread.hasBasis_standardNbhd`, `GX.OmegaSpace`,
`GX.omegaRel_equivalence`, `GX.omegaEnd`, `GX.piOnePMap`, `GX.compOfClass`, `GX.piOneUMap`,
`GX.fibS_tower`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

noncomputable section

open Set Filter Topology Function unitInterval

namespace GX

attribute [local instance] Classical.propDecidable

set_option linter.unusedSectionVars false

variable {X : Type*} [TopologicalSpace X]

/-! ### Paths with interior in `U` -/

/-- `Ω_X(x, y, U)`: a path `γ : x ⇝ y` with `γ(]0,1[) ⊆ U`. -/
def MemOmega (U : Set X) {x y : X} (γ : Path x y) : Prop :=
  ∀ t : I, 0 < (t : ℝ) → (t : ℝ) < 1 → γ t ∈ U

/-- Two paths of `Ω(x,y,U)` are *homotopic with respect to `U`* (`RamcovGX.tex:1201`): a
homotopy `H` with fixed ends with `H([0,1] × ]0,1[) ⊆ U`. -/
def OmegaHomotopic (U : Set X) {x y : X} (γ₁ γ₂ : Path x y) : Prop :=
  ∃ F : Path.Homotopy γ₁ γ₂, ∀ s t : I, 0 < (t : ℝ) → (t : ℝ) < 1 → F (s, t) ∈ U

/-- Homotopic *in* `U`: a homotopy with fixed ends all of whose values lie in `U`. -/
def HomotopicIn (U : Set X) {x y : X} (γ₁ γ₂ : Path x y) : Prop :=
  ∃ F : Path.Homotopy γ₁ γ₂, ∀ z, F z ∈ U

section Basic

variable {U : Set X} {x y z : X}

theorem OmegaHomotopic.memOmega_left {γ₁ γ₂ : Path x y} (h : OmegaHomotopic U γ₁ γ₂) :
    MemOmega U γ₁ := by
  obtain ⟨F, hF⟩ := h
  intro t h0 h1
  have := hF 0 t h0 h1
  rwa [F.apply_zero] at this

theorem OmegaHomotopic.memOmega_right {γ₁ γ₂ : Path x y} (h : OmegaHomotopic U γ₁ γ₂) :
    MemOmega U γ₂ := by
  obtain ⟨F, hF⟩ := h
  intro t h0 h1
  have := hF 1 t h0 h1
  rwa [F.apply_one] at this

theorem OmegaHomotopic.refl {γ : Path x y} (h : MemOmega U γ) : OmegaHomotopic U γ γ :=
  ⟨Path.Homotopy.refl γ, fun s t h0 h1 => by simpa using h t h0 h1⟩

theorem OmegaHomotopic.symm {γ₁ γ₂ : Path x y} (h : OmegaHomotopic U γ₁ γ₂) :
    OmegaHomotopic U γ₂ γ₁ := by
  obtain ⟨F, hF⟩ := h
  exact ⟨F.symm, fun s t h0 h1 => by simpa using hF (σ s) t h0 h1⟩

theorem OmegaHomotopic.trans {γ₁ γ₂ γ₃ : Path x y} (h : OmegaHomotopic U γ₁ γ₂)
    (h' : OmegaHomotopic U γ₂ γ₃) : OmegaHomotopic U γ₁ γ₃ := by
  obtain ⟨F, hF⟩ := h
  obtain ⟨G, hG⟩ := h'
  refine ⟨F.trans G, fun s t h0 h1 => ?_⟩
  rw [Path.Homotopy.trans_apply]
  split_ifs
  · exact hF _ t h0 h1
  · exact hG _ t h0 h1

theorem HomotopicIn.omegaHomotopic {γ₁ γ₂ : Path x y} (h : HomotopicIn U γ₁ γ₂) :
    OmegaHomotopic U γ₁ γ₂ := by
  obtain ⟨F, hF⟩ := h
  exact ⟨F, fun s t _ _ => hF (s, t)⟩

theorem HomotopicIn.mem_left {γ₁ γ₂ : Path x y} (h : HomotopicIn U γ₁ γ₂) (t : I) :
    γ₁ t ∈ U := by
  obtain ⟨F, hF⟩ := h
  have := hF (0, t)
  rwa [F.apply_zero] at this

theorem HomotopicIn.mem_right {γ₁ γ₂ : Path x y} (h : HomotopicIn U γ₁ γ₂) (t : I) :
    γ₂ t ∈ U := by
  obtain ⟨F, hF⟩ := h
  have := hF (1, t)
  rwa [F.apply_one] at this

theorem HomotopicIn.refl {γ : Path x y} (h : ∀ t, γ t ∈ U) : HomotopicIn U γ γ :=
  ⟨Path.Homotopy.refl γ, fun z => by simpa using h z.2⟩

theorem HomotopicIn.symm {γ₁ γ₂ : Path x y} (h : HomotopicIn U γ₁ γ₂) :
    HomotopicIn U γ₂ γ₁ := by
  obtain ⟨F, hF⟩ := h
  exact ⟨F.symm, fun z => by simpa using hF (σ z.1, z.2)⟩

theorem HomotopicIn.trans {γ₁ γ₂ γ₃ : Path x y} (h : HomotopicIn U γ₁ γ₂)
    (h' : HomotopicIn U γ₂ γ₃) : HomotopicIn U γ₁ γ₃ := by
  obtain ⟨F, hF⟩ := h
  obtain ⟨G, hG⟩ := h'
  refine ⟨F.trans G, fun z => ?_⟩
  rw [Path.Homotopy.trans_apply]
  split_ifs
  · exact hF _
  · exact hG _

theorem HomotopicIn.cast {γ₁ γ₂ : Path x y} (h : HomotopicIn U γ₁ γ₂) {x' y' : X}
    (hx : x' = x) (hy : y' = y) : HomotopicIn U (γ₁.cast hx hy) (γ₂.cast hx hy) := by
  obtain ⟨F, hF⟩ := h
  exact ⟨F.pathCast hx hy, fun z => hF z⟩

theorem HomotopicIn.of_eq {γ₁ γ₂ γ₁' γ₂' : Path x y} (h : HomotopicIn U γ₁ γ₂) (h₁ : γ₁ = γ₁')
    (h₂ : γ₂ = γ₂') : HomotopicIn U γ₁' γ₂' := h₁ ▸ h₂ ▸ h

theorem HomotopicIn.hcomp {p₀ q₀ : Path x y} {p₁ q₁ : Path y z} (h₀ : HomotopicIn U p₀ q₀)
    (h₁ : HomotopicIn U p₁ q₁) : HomotopicIn U (p₀.trans p₁) (q₀.trans q₁) := by
  obtain ⟨F, hF⟩ := h₀
  obtain ⟨G, hG⟩ := h₁
  refine ⟨F.hcomp G, fun w => ?_⟩
  rw [Path.Homotopy.hcomp_apply]
  split_ifs
  · exact hF _
  · exact hG _

theorem HomotopicIn.mono {V : Set X} {γ₁ γ₂ : Path x y} (h : HomotopicIn U γ₁ γ₂) (hUV : U ⊆ V) :
    HomotopicIn V γ₁ γ₂ := by
  obtain ⟨F, hF⟩ := h
  exact ⟨F, fun w => hUV (hF w)⟩

end Basic

/-! ### Paths in a subspace -/

section Sub

variable {U : Set X} {x y z : X}

/-- A path of `X` with values in `U`, as a path of the subspace `U`. -/
def pathToSub (γ : Path x y) (h : ∀ t, γ t ∈ U) :
    Path (⟨x, γ.source ▸ h 0⟩ : U) ⟨y, γ.target ▸ h 1⟩ where
  toFun t := ⟨γ t, h t⟩
  continuous_toFun := γ.continuous.subtype_mk _
  source' := Subtype.ext γ.source
  target' := Subtype.ext γ.target

@[simp] theorem pathToSub_apply (γ : Path x y) (h : ∀ t, γ t ∈ U) (t : I) :
    (pathToSub γ h t : X) = γ t := rfl

theorem pathToSub_trans (γ : Path x y) (γ' : Path y z) (h : ∀ t, γ t ∈ U) (h' : ∀ t, γ' t ∈ U)
    (h'' : ∀ t, (γ.trans γ') t ∈ U) :
    pathToSub (γ.trans γ') h'' = (pathToSub γ h).trans (pathToSub γ' h') := by
  ext t
  simp only [pathToSub_apply, Path.trans_apply]
  split_ifs <;> rfl

theorem pathToSub_symm (γ : Path x y) (h : ∀ t, γ t ∈ U) (h' : ∀ t, γ.symm t ∈ U) :
    pathToSub γ.symm h' = (pathToSub γ h).symm := by
  ext t
  rfl

theorem pathToSub_cast (γ : Path x y) (h : ∀ t, γ t ∈ U) {x' y' : X} (hx : x' = x)
    (hy : y' = y) (h' : ∀ t, (γ.cast hx hy) t ∈ U) :
    pathToSub (γ.cast hx hy) h' = (pathToSub γ h).cast (Subtype.ext hx) (Subtype.ext hy) := by
  ext t
  rfl

theorem homotopicIn_iff {γ₁ γ₂ : Path x y} :
    HomotopicIn U γ₁ γ₂ ↔ ∃ (h₁ : ∀ t, γ₁ t ∈ U) (h₂ : ∀ t, γ₂ t ∈ U),
      (pathToSub γ₁ h₁).Homotopic (pathToSub γ₂ h₂) := by
  constructor
  · intro h
    refine ⟨h.mem_left, h.mem_right, ?_⟩
    obtain ⟨F, hF⟩ := h
    exact ⟨{ toFun := fun w => ⟨F w, hF w⟩
             continuous_toFun := F.continuous.subtype_mk _
             map_zero_left := fun t => Subtype.ext (F.apply_zero t)
             map_one_left := fun t => Subtype.ext (F.apply_one t)
             prop' := fun s t ht => Subtype.ext (F.eq_fst s ht) }⟩
  · rintro ⟨h₁, h₂, ⟨G⟩⟩
    have e₁ : (pathToSub γ₁ h₁).map continuous_subtype_val = γ₁ := by ext; rfl
    have e₂ : (pathToSub γ₂ h₂).map continuous_subtype_val = γ₂ := by ext; rfl
    refine ⟨(G.map ⟨Subtype.val, continuous_subtype_val⟩).cast e₁ e₂, fun w => ?_⟩
    exact (G w).2

end Sub

/-! ### Straight-line homotopies, sub-paths, splicing -/

section Line

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E]

/-- The straight-line homotopy between two paths of a real topological vector space. -/
def lineHomotopy {a b : E} (α β : Path a b) : Path.Homotopy α β where
  toFun w := AffineMap.lineMap (α w.2) (β w.2) (w.1 : ℝ)
  continuous_toFun := by
    simp only [AffineMap.lineMap_apply_module]
    fun_prop
  map_zero_left t := by simp
  map_one_left t := by simp
  prop' s t ht := by
    rcases ht with rfl | rfl <;> simp

theorem lineHomotopy_apply {a b : E} (α β : Path a b) (w : I × I) :
    lineHomotopy α β w = AffineMap.lineMap (α w.2) (β w.2) (w.1 : ℝ) := rfl

/-- Two paths of a convex `A` with the same ends have homotopic images under any `F`, the
homotopy taking its values in `F(A)`. -/
theorem homotopicIn_map_of_convex {U : Set X} {a b : E} (α β : Path a b) {A : Set E}
    (hA : Convex ℝ A) (hα : ∀ t, α t ∈ A) (hβ : ∀ t, β t ∈ A) {F : E → X} (hF : Continuous F)
    (hFA : ∀ e ∈ A, F e ∈ U) : HomotopicIn U (α.map hF) (β.map hF) :=
  ⟨(lineHomotopy α β).map ⟨F, hF⟩, fun w => hFA _ (hA.lineMap_mem (hα w.2) (hβ w.2) w.1.2)⟩

end Line

section Splice

variable {U : Set X} {x y z : X}

/-- The sub-path `γ_{|[a,b]}` (affinely reparametrised; `a`, `b` in any order). -/
def subpath (γ : Path x y) (a b : I) : Path (γ a) (γ b) :=
  ((Path.segment (a : ℝ) (b : ℝ)).map γ.continuous_extend).cast (γ.extend_extends' a).symm
    (γ.extend_extends' b).symm

theorem subpath_apply (γ : Path x y) (a b : I) (t : I) :
    subpath γ a b t = γ.extend (AffineMap.lineMap (a : ℝ) (b : ℝ) (t : ℝ)) := rfl

theorem subpath_apply' (γ : Path x y) (a b : I) (t : I) :
    subpath γ a b t = γ.extend ((1 - (t : ℝ)) * a + t * b) := by
  rw [subpath_apply, AffineMap.lineMap_apply_module]
  simp [smul_eq_mul]

/-- The values of a sub-path lie in the image of the interval between its ends. -/
theorem subpath_mem (γ : Path x y) (a b : I) (t : I) :
    ∃ s : I, min (a : ℝ) b ≤ s ∧ (s : ℝ) ≤ max (a : ℝ) b ∧ subpath γ a b t = γ s := by
  set r : ℝ := (1 - (t : ℝ)) * a + t * b with hr
  have ht0 := t.2.1
  have ht1 := t.2.2
  have h1 : min (a : ℝ) b ≤ r := by
    rcases le_total (a : ℝ) b with h | h
    · rw [min_eq_left h]; nlinarith
    · rw [min_eq_right h]; nlinarith
  have h2 : r ≤ max (a : ℝ) b := by
    rcases le_total (a : ℝ) b with h | h
    · rw [max_eq_right h]; nlinarith
    · rw [max_eq_left h]; nlinarith
  have hrI : r ∈ I := ⟨le_trans (le_min a.2.1 b.2.1) h1, h2.trans (max_le a.2.2 b.2.2)⟩
  refine ⟨⟨r, hrI⟩, h1, h2, ?_⟩
  rw [subpath_apply', Path.extend_apply γ hrI]

/-- The head `γ_{|[0,s]}` of a path, from `x`. -/
def head (γ : Path x y) (s : I) : Path x (γ s) :=
  (subpath γ 0 s).cast γ.source.symm rfl

theorem head_apply (γ : Path x y) (s t : I) : head γ s t = subpath γ 0 s t := rfl

/-- Reparametrising a path inside an interval on which it stays in `U` is a homotopy in `U`. -/
theorem homotopicIn_reparam (γ : Path x y) {a b : ℝ} (α β : Path a b) {A : Set ℝ}
    (hA : Convex ℝ A) (hα : ∀ t, α t ∈ A) (hβ : ∀ t, β t ∈ A) (hγA : ∀ r ∈ A, γ.extend r ∈ U) :
    HomotopicIn U (α.map γ.continuous_extend) (β.map γ.continuous_extend) :=
  homotopicIn_map_of_convex α β hA hα hβ γ.continuous_extend hγA

end Splice

section Splice2

variable {U : Set X} {x y z : X}

theorem subpath_trans_homotopicIn (γ : Path x y) (a b c : I)
    (hU : ∀ r : ℝ, min (min (a : ℝ) b) c ≤ r → r ≤ max (max (a : ℝ) b) c → γ.extend r ∈ U) :
    HomotopicIn U (subpath γ a c) ((subpath γ a b).trans (subpath γ b c)) := by
  set A : Set ℝ := Icc (min (min (a : ℝ) b) c) (max (max (a : ℝ) b) c)
  have hAc : Convex ℝ A := convex_Icc _ _
  have ha : (a : ℝ) ∈ A := ⟨by simp, by simp⟩
  have hb : (b : ℝ) ∈ A := ⟨by simp, by simp⟩
  have hc : (c : ℝ) ∈ A := ⟨by simp, by simp⟩
  have hseg : ∀ {p q : ℝ}, p ∈ A → q ∈ A → ∀ t, Path.segment p q t ∈ A := fun hp hq t => by
    rw [Path.segment_apply]; exact hAc.lineMap_mem hp hq t.2
  have h := homotopicIn_reparam γ (Path.segment (a : ℝ) c)
    ((Path.segment (a : ℝ) b).trans (Path.segment (b : ℝ) c)) hAc (hseg ha hc)
    (fun t => by
      rw [Path.trans_apply]; split_ifs
      · exact hseg ha hb _
      · exact hseg hb hc _) (fun r hr => hU r hr.1 hr.2)
  have h' := h.cast (γ.extend_extends' a).symm (γ.extend_extends' c).symm
  refine h'.of_eq rfl ?_
  ext t
  simp only [Path.cast_coe, Path.map_coe, comp_apply, Path.trans_apply]
  split_ifs <;> rfl

/-- The function underlying a splice, for a family parametrised by `Q`. -/
def spliceFun {Q : Type*} (g : Q × I → X) (w : Q × I → X) (t₀ t₁ : I) (z : Q × I) : X :=
  if (z.2 : ℝ) ≤ t₀ then g z
  else if (z.2 : ℝ) ≤ t₁ then w (z.1, Set.projIcc 0 1 zero_le_one ((z.2 - t₀) / (t₁ - t₀)))
  else g z

theorem projIcc_div_self {t₀ t₁ : ℝ} (h : t₀ < t₁) :
    Set.projIcc (0 : ℝ) 1 zero_le_one ((t₁ - t₀) / (t₁ - t₀)) = 1 := by
  rw [div_self (sub_ne_zero.2 h.ne')]
  exact Subtype.ext (by simp)

theorem projIcc_sub_self_div (t₀ t₁ : ℝ) :
    Set.projIcc (0 : ℝ) 1 zero_le_one ((t₀ - t₀) / (t₁ - t₀)) = 0 := by
  rw [sub_self, zero_div]
  exact Subtype.ext (by simp)

theorem continuous_spliceFun {Q : Type*} [TopologicalSpace Q] {g w : Q × I → X}
    (hg : Continuous g) (hw : Continuous w) {t₀ t₁ : I} (h : (t₀ : ℝ) < t₁)
    (h0 : ∀ q, w (q, 0) = g (q, t₀)) (h1 : ∀ q, w (q, 1) = g (q, t₁)) :
    Continuous (spliceFun g w t₀ t₁) := by
  have hproj : Continuous fun z : Q × I =>
      w (z.1, Set.projIcc 0 1 zero_le_one (((z.2 : ℝ) - t₀) / (t₁ - t₀))) :=
    hw.comp (continuous_fst.prodMk (continuous_projIcc.comp (by fun_prop)))
  have hinner : Continuous fun z : Q × I =>
      if (z.2 : ℝ) ≤ t₁ then w (z.1, Set.projIcc 0 1 zero_le_one ((z.2 - t₀) / (t₁ - t₀)))
      else g z := by
    refine Continuous.if_le hproj hg (by fun_prop) continuous_const fun z hz => ?_
    rw [hz, projIcc_div_self h, h1]
    congr 1
    exact Prod.ext rfl (Subtype.ext hz.symm)
  refine Continuous.if_le hg hinner (by fun_prop) continuous_const fun z hz => ?_
  rw [if_pos (hz.le.trans h.le), hz, projIcc_sub_self_div, h0]
  congr 1
  exact Prod.ext rfl (Subtype.ext hz)

/-- `γ_{|[0,t₀]} * ω * γ_{|[t₁,1]}`, in the parametrisation keeping `γ` on `[0,t₀] ∪ [t₁,1]`
and running `ω` on `[t₀,t₁]` (the paper's `*` is "any parameterization",
`RamcovGX.tex:1204`). -/
def splice (γ : Path x y) (t₀ t₁ : I) (h : (t₀ : ℝ) < t₁) (ω : Path (γ t₀) (γ t₁)) :
    Path x y where
  toFun t := spliceFun (fun z : Unit × I => γ z.2) (fun z => ω z.2) t₀ t₁ ((), t)
  continuous_toFun := (continuous_spliceFun (by fun_prop) (by fun_prop) h (fun _ => ω.source)
    (fun _ => ω.target)).comp (by fun_prop)
  source' := by
    simp only [spliceFun, Icc.coe_zero, if_pos t₀.2.1, γ.source]
  target' := by
    simp only [spliceFun, Icc.coe_one]
    have h1 : ¬ (1 : ℝ) ≤ t₀ := fun h' => absurd (h'.trans_lt h) (not_lt.2 t₁.2.2)
    rw [if_neg h1]
    split_ifs with h2
    · have : (t₁ : ℝ) = 1 := le_antisymm t₁.2.2 h2
      have ht₁ : t₁ = 1 := Subtype.ext this
      have e : (1 - (t₀ : ℝ)) / (t₁ - t₀) = (t₁ - t₀) / (t₁ - t₀) := by rw [this]
      rw [e, projIcc_div_self h, ω.target, ht₁, γ.target]
    · exact γ.target

theorem splice_apply (γ : Path x y) {t₀ t₁ : I} (h : (t₀ : ℝ) < t₁) (ω : Path (γ t₀) (γ t₁))
    (t : I) : splice γ t₀ t₁ h ω t =
      spliceFun (fun z : Unit × I => γ z.2) (fun z => ω z.2) t₀ t₁ ((), t) := rfl

theorem splice_apply_of_le (γ : Path x y) {t₀ t₁ : I} (h : (t₀ : ℝ) < t₁)
    (ω : Path (γ t₀) (γ t₁)) {t : I} (ht : (t : ℝ) ≤ t₀) : splice γ t₀ t₁ h ω t = γ t := by
  rw [splice_apply]
  simp only [spliceFun, if_pos ht]

theorem splice_apply_of_ge (γ : Path x y) {t₀ t₁ : I} (h : (t₀ : ℝ) < t₁)
    (ω : Path (γ t₀) (γ t₁)) {t : I} (ht : (t₁ : ℝ) ≤ t) : splice γ t₀ t₁ h ω t = γ t := by
  rw [splice_apply]
  simp only [spliceFun, if_neg (not_le.2 (h.trans_le ht))]
  split_ifs with h2
  · have : (t : ℝ) = t₁ := le_antisymm h2 ht
    rw [this, projIcc_div_self h, ω.target]
    congr 1; exact Subtype.ext this.symm
  · rfl

theorem splice_apply_mid (γ : Path x y) {t₀ t₁ : I} (h : (t₀ : ℝ) < t₁)
    (ω : Path (γ t₀) (γ t₁)) {t : I} (ht : (t₀ : ℝ) < t) (ht' : (t : ℝ) ≤ t₁) :
    splice γ t₀ t₁ h ω t = ω (Set.projIcc 0 1 zero_le_one ((t - t₀) / (t₁ - t₀))) := by
  rw [splice_apply]
  simp only [spliceFun, if_neg (not_le.2 ht), if_pos ht']

theorem projIcc_mid {t₀ t₁ t : ℝ} (h : t₀ < t₁) (ht : t₀ ≤ t) (ht' : t ≤ t₁) :
    ((Set.projIcc (0 : ℝ) 1 zero_le_one ((t - t₀) / (t₁ - t₀)) : I) : ℝ) = (t - t₀) / (t₁ - t₀) := by
  have hd : 0 < t₁ - t₀ := sub_pos.2 h
  rw [Set.projIcc_of_mem]
  exact ⟨div_nonneg (sub_nonneg.2 ht) hd.le, (div_le_one hd).2 (by linarith)⟩

/-- The values of a splice. -/
theorem splice_mem (γ : Path x y) {t₀ t₁ : I} (h : (t₀ : ℝ) < t₁) (ω : Path (γ t₀) (γ t₁))
    (t : I) : ((t : ℝ) ≤ t₀ ∧ splice γ t₀ t₁ h ω t = γ t) ∨
      ((t₁ : ℝ) ≤ t ∧ splice γ t₀ t₁ h ω t = γ t) ∨ splice γ t₀ t₁ h ω t ∈ range ω := by
  rcases le_or_gt (t : ℝ) t₀ with h1 | h1
  · exact Or.inl ⟨h1, splice_apply_of_le γ h ω h1⟩
  rcases le_or_gt (t : ℝ) t₁ with h2 | h2
  · exact Or.inr (Or.inr ⟨_, (splice_apply_mid γ h ω h1 h2).symm⟩)
  · exact Or.inr (Or.inl ⟨h2.le, splice_apply_of_ge γ h ω h2.le⟩)

/-- Splicing `γ`'s own sub-path gives `γ` back. -/
theorem splice_subpath (γ : Path x y) {t₀ t₁ : I} (h : (t₀ : ℝ) < t₁) :
    splice γ t₀ t₁ h (subpath γ t₀ t₁) = γ := by
  ext t
  rcases le_or_gt (t : ℝ) t₀ with h1 | h1
  · exact splice_apply_of_le γ h _ h1
  rcases le_or_gt (t : ℝ) t₁ with h2 | h2
  · rw [splice_apply_mid γ h _ h1 h2, subpath_apply', projIcc_mid h h1.le h2]
    have hd : (t₁ : ℝ) - t₀ ≠ 0 := sub_ne_zero.2 h.ne'
    have : (1 - ((t : ℝ) - t₀) / (t₁ - t₀)) * t₀ + ((t : ℝ) - t₀) / (t₁ - t₀) * t₁ = t := by
      field_simp; ring
    rw [this, Path.extend_apply γ t.2]
  · exact splice_apply_of_ge γ h _ h2.le

/-- **The splice lemma.** If the middle `γ_{|[t₀,t₁]}` of `γ ∈ Ω(x,y,U)` is homotopic in `U` to
`ω`, then `γ` is homotopic with respect to `U` to `γ_{|[0,t₀]} * ω * γ_{|[t₁,1]}`. -/
theorem splice_omegaHomotopic {γ : Path x y} (hγ : MemOmega U γ) {t₀ t₁ : I}
    (h : (t₀ : ℝ) < t₁) (h1 : (t₁ : ℝ) < 1) {ω : Path (γ t₀) (γ t₁)}
    (hω : HomotopicIn U (subpath γ t₀ t₁) ω) : OmegaHomotopic U γ (splice γ t₀ t₁ h ω) := by
  obtain ⟨G, hG⟩ := hω
  have hc := continuous_spliceFun (g := fun z : I × I => γ z.2) (w := fun z => G z)
    (by fun_prop) G.continuous h (fun q => G.source q) (fun q => G.target q)
  have e0 : ∀ t, spliceFun (fun z : I × I => γ z.2) (fun z => G z) t₀ t₁ (0, t) = γ t := by
    intro t
    conv_rhs => rw [← splice_subpath γ h]
    simp only [splice, spliceFun, Path.coe_mk_mk]
    split_ifs
    · rfl
    · rw [G.apply_zero]; rfl
    · rfl
  have e1 : ∀ t, spliceFun (fun z : I × I => γ z.2) (fun z => G z) t₀ t₁ (1, t) =
      splice γ t₀ t₁ h ω t := by
    intro t
    simp only [splice, spliceFun, Path.coe_mk_mk]
    split_ifs
    · rfl
    · rw [G.apply_one]; rfl
    · rfl
  refine ⟨{ toFun := spliceFun (fun z : I × I => γ z.2) (fun z => G z) t₀ t₁
            continuous_toFun := hc
            map_zero_left := e0
            map_one_left := e1
            prop' := fun s t ht => ?_ }, fun s t ht0 ht1 => ?_⟩
  · rcases ht with rfl | rfl
    · change spliceFun (fun z : I × I => γ z.2) (fun z => G z) t₀ t₁ (s, 0) = γ 0
      simp only [spliceFun, Icc.coe_zero, if_pos t₀.2.1]
    · change spliceFun (fun z : I × I => γ z.2) (fun z => G z) t₀ t₁ (s, 1) = γ 1
      simp only [spliceFun, Icc.coe_one, if_neg (not_le.2 (h.trans h1)), if_neg (not_le.2 h1)]
  · change spliceFun (fun z : I × I => γ z.2) (fun z => G z) t₀ t₁ (s, t) ∈ U
    simp only [spliceFun]
    split_ifs
    · exact hγ t ht0 ht1
    · exact hG _
    · exact hγ t ht0 ht1

end Splice2

/-! ### Tails of paths, and the tube lemma -/

section Tails

variable {x y : X}

/-- A path stays in a neighbourhood of its origin for small times. -/
theorem exists_head_mem (γ : Path x y) {V : Set X} (hV : V ∈ 𝓝 x) {c : ℝ} (hc : 0 < c) :
    ∃ t₀ : I, 0 < (t₀ : ℝ) ∧ (t₀ : ℝ) < c ∧ ∀ t : I, (t : ℝ) ≤ t₀ → γ t ∈ V := by
  have h : ∀ᶠ t in 𝓝 (0 : I), γ t ∈ V :=
    γ.continuous.continuousAt.preimage_mem_nhds (by rw [γ.source]; exact hV)
  obtain ⟨ε, hε, hεV⟩ := Metric.eventually_nhds_iff.1 h
  set r : ℝ := min ε (min c 1) / 2 with hr
  have hr0 : 0 < r := by positivity
  have hr1 : r < ε := by rw [hr]; linarith [min_le_left ε (min c 1)]
  have hrc : r < c := by rw [hr]; linarith [min_le_right ε (min c 1), min_le_left c 1]
  have hr2 : r ≤ 1 := by rw [hr]; linarith [min_le_right ε (min c 1), min_le_right c 1]
  refine ⟨⟨r, hr0.le, hr2⟩, hr0, hrc, fun t ht => hεV ?_⟩
  rw [Subtype.dist_eq, Icc.coe_zero, Real.dist_eq, sub_zero, abs_of_nonneg t.2.1]
  exact lt_of_le_of_lt ht hr1

/-- A path stays in a neighbourhood of its end for times close to `1`. -/
theorem exists_tail_mem (γ : Path x y) {V : Set X} (hV : V ∈ 𝓝 y) {c : ℝ} (hc : 0 < c) :
    ∃ t₁ : I, 1 - c < (t₁ : ℝ) ∧ (t₁ : ℝ) < 1 ∧ ∀ t : I, (t₁ : ℝ) ≤ t → γ t ∈ V := by
  obtain ⟨t₀, h0, hc', ht⟩ := exists_head_mem γ.symm hV hc
  refine ⟨σ t₀, by rw [unitInterval.coe_symm_eq]; linarith,
    by rw [unitInterval.coe_symm_eq]; linarith, fun t ht' => ?_⟩
  have := ht (σ t) (by rw [unitInterval.coe_symm_eq] at ht' ⊢; linarith)
  simpa only [Path.symm_apply, Function.comp_apply, unitInterval.symm_symm] using this

/-- The tube lemma at the two ends of a homotopy with fixed ends. -/
theorem homotopy_exists_ends_mem {γ₁ γ₂ : Path x y} (F : Path.Homotopy γ₁ γ₂)
    {V : Set X} (hV : IsOpen V) (hx : x ∈ V) (hy : y ∈ V) :
    ∃ ε > (0 : ℝ), ∀ s t : I, ((t : ℝ) < ε → F (s, t) ∈ V) ∧ (1 - ε < (t : ℝ) → F (s, t) ∈ V) := by
  have key : ∀ (t₀ : I), F (0, t₀) ∈ V → (∀ s, F (s, t₀) = F (0, t₀)) →
      ∃ ε > (0 : ℝ), ∀ s t : I, dist t t₀ < ε → F (s, t) ∈ V := by
    intro t₀ hV0 hconst
    have hP : ∀ s ∈ (univ : Set I), ∀ᶠ z : I × I in 𝓝 (t₀, s), F (z.2, z.1) ∈ V := by
      intro s _
      have hc : Continuous fun z : I × I => F (z.2, z.1) := F.continuous.comp continuous_swap
      exact hc.continuousAt.preimage_mem_nhds (hV.mem_nhds (by rw [hconst]; exact hV0))
    obtain ⟨ε, hε, h⟩ := Metric.eventually_nhds_iff.1
      (isCompact_univ.eventually_forall_of_forall_eventually (P := fun t s => F (s, t) ∈ V) hP)
    exact ⟨ε, hε, fun s t ht => h ht s (mem_univ s)⟩
  obtain ⟨ε₀, hε₀, h₀⟩ := key 0 (by rw [F.source]; exact hx) (fun s => by rw [F.source, F.source])
  obtain ⟨ε₁, hε₁, h₁⟩ := key 1 (by rw [F.target]; exact hy) (fun s => by rw [F.target, F.target])
  refine ⟨min ε₀ ε₁, lt_min hε₀ hε₁, fun s t => ⟨fun ht => h₀ s t ?_, fun ht => h₁ s t ?_⟩⟩
  · rw [Subtype.dist_eq, Icc.coe_zero, Real.dist_eq, sub_zero, abs_of_nonneg t.2.1]
    exact ht.trans_le (min_le_left _ _)
  · rw [Subtype.dist_eq, Icc.coe_one, Real.dist_eq, abs_of_nonpos (by linarith [t.2.2])]
    linarith [min_le_right ε₀ ε₁]

end Tails

/-! ### `def:almost_trivial_loop` -/

/-- The **homotopy form** of `def:almost_trivial_loop` (`RamcovGX.tex:1210`; the "or,
equivalently" of l.1201 — DEC-55 reads the definition literally, `GX.AlmostTrivialCC`). A loop
`γ ∈ Ω(x,x,U)` is *almost trivial with respect to `U`* if for every neighbourhood `V` of `x` it
is homotopic with respect to `U` to a loop of `Ω(x,x,V ∩ U)`. -/
def AlmostTrivial (U : Set X) {x : X} (γ : Path x x) : Prop :=
  MemOmega U γ ∧ ∀ V ∈ 𝓝 x, ∃ γ' : Path x x, MemOmega (V ∩ U) γ' ∧ OmegaHomotopic U γ γ'

/-- The homotopy form of almost triviality at one neighbourhood `V`: `γ` is homotopic with
respect to `U` to a loop of `Ω(x,x,V ∩ U)`. -/
def AlmostTrivialAt (U V : Set X) {x : X} (γ : Path x x) : Prop :=
  ∃ γ' : Path x x, MemOmega (V ∩ U) γ' ∧ OmegaHomotopic U γ γ'

/-- `Ω_X(x,y,U)` as a subspace of `C([0,1], X)` (compact-open topology, `RamcovGX.tex:1199`). -/
def OmegaSet (U : Set X) (x y : X) : Set C(I, X) :=
  {f | f 0 = x ∧ f 1 = y ∧ ∀ t : I, 0 < (t : ℝ) → (t : ℝ) < 1 → f t ∈ U}

/-- **`def:almost_trivial_loop`** in its **literal** form (DEC-55) (`RamcovGX.tex:1212`): the connected
component of `γ` in the compact-open `Ω(x,x,U)` meets `Ω(x,x,V ∩ U)` for every neighbourhood
`V` of `x`. -/
def AlmostTrivialCC (U : Set X) {x : X} (γ : Path x x) : Prop :=
  γ.toContinuousMap ∈ OmegaSet U x x ∧ ∀ V ∈ 𝓝 x,
    (connectedComponentIn (OmegaSet U x x) γ.toContinuousMap ∩ OmegaSet (V ∩ U) x x).Nonempty

/-- Homotopic with respect to `U` implies in the same connected component of the compact-open
`Ω(x,y,U)` (the half of the "equivalently" of `RamcovGX.tex:1201` that holds in general). -/
theorem OmegaHomotopic.mem_connectedComponentIn {U : Set X} {x y : X} {γ₁ γ₂ : Path x y}
    (h : OmegaHomotopic U γ₁ γ₂) :
    γ₂.toContinuousMap ∈ connectedComponentIn (OmegaSet U x y) γ₁.toContinuousMap := by
  obtain ⟨F, hF⟩ := h
  set c : C(I, C(I, X)) := F.toContinuousMap.curry
  have hc0 : c 0 = γ₁.toContinuousMap := ContinuousMap.ext fun t => F.apply_zero t
  have hc1 : c 1 = γ₂.toContinuousMap := ContinuousMap.ext fun t => F.apply_one t
  have hsub : range c ⊆ OmegaSet U x y := by
    rintro _ ⟨s, rfl⟩
    exact ⟨F.source s, F.target s, fun t h0 h1 => hF s t h0 h1⟩
  have := (isPreconnected_range c.continuous).subset_connectedComponentIn ⟨0, hc0⟩ hsub
  exact this ⟨1, hc1⟩

/-- The homotopy reading of `def:almost_trivial_loop` implies the literal one. -/
theorem AlmostTrivial.almostTrivialCC {U : Set X} {x : X} {γ : Path x x}
    (h : AlmostTrivial U γ) : AlmostTrivialCC U γ := by
  refine ⟨⟨γ.source, γ.target, h.1⟩, fun V hV => ?_⟩
  obtain ⟨γ', hγ', hh⟩ := h.2 V hV
  exact ⟨γ'.toContinuousMap, hh.mem_connectedComponentIn, ⟨γ'.source, γ'.target, hγ'⟩⟩

section Square

variable {U : Set X} {x : X}

/-- A map on the square, extended to `ℝ²` through `projIcc`. -/
def squareExt (F : I × I → X) (p : ℝ × ℝ) : X :=
  F (Set.projIcc 0 1 zero_le_one p.1, Set.projIcc 0 1 zero_le_one p.2)

theorem continuous_squareExt {F : I × I → X} (hF : Continuous F) : Continuous (squareExt F) :=
  hF.comp ((continuous_projIcc.comp continuous_fst).prodMk (continuous_projIcc.comp continuous_snd))

theorem squareExt_apply (F : I × I → X) (a : ℝ) {b : ℝ} (hb : b ∈ I) :
    squareExt F (a, b) = F (Set.projIcc 0 1 zero_le_one a, ⟨b, hb⟩) := by
  simp only [squareExt, Set.projIcc_of_mem _ hb]

theorem projIcc_zero' : Set.projIcc (0 : ℝ) 1 zero_le_one 0 = 0 := Subtype.ext (by simp)

theorem projIcc_one' : Set.projIcc (0 : ℝ) 1 zero_le_one 1 = 1 := Subtype.ext (by simp)

theorem mem_segment_prod {a b c d : ℝ} {e : ℝ × ℝ} (he : e ∈ segment ℝ (a, b) (c, d)) :
    ∃ r ∈ Icc (0 : ℝ) 1, e = ((1 - r) * a + r * c, (1 - r) * b + r * d) := by
  rw [segment_eq_image_lineMap] at he
  obtain ⟨r, hr, rfl⟩ := he
  refine ⟨r, hr, ?_⟩
  simp [AffineMap.lineMap_apply_module, smul_eq_mul]

/-- **The square argument** of `lem:almost_homotopic_carac` (`RamcovGX.tex:1279–1286`), in the
strong form the proof of `lem:hausdorff_first_countable_connected` uses: if `γ` is almost
trivial, `V` an open neighbourhood of `x` and `γ([0,t₀] ∪ [t₁,1]) ⊆ V`, the middle
`γ_{|[t₀,t₁]}` is homotopic **in `U`** to a path `ω` of `V ∩ U`. -/
theorem AlmostTrivialAt.exists_mid {γ : Path x x} {V : Set X} (hγ : AlmostTrivialAt U V γ)
    (hV : IsOpen V) (hxV : x ∈ V) {t₀ t₁ : I} (h0 : 0 < (t₀ : ℝ)) (h : (t₀ : ℝ) < t₁)
    (h1 : (t₁ : ℝ) < 1) (hγ₀ : ∀ t : I, (t : ℝ) ≤ t₀ → γ t ∈ V)
    (hγ₁ : ∀ t : I, (t₁ : ℝ) ≤ t → γ t ∈ V) :
    ∃ ω : Path (γ t₀) (γ t₁), (∀ s, ω s ∈ V ∩ U) ∧ HomotopicIn U (subpath γ t₀ t₁) ω := by
  obtain ⟨γ', hγ', F, hF⟩ := hγ
  obtain ⟨ε, hε, hεV⟩ := homotopy_exists_ends_mem F hV hxV hxV
  have ht₁' : 0 < 1 - (t₁ : ℝ) := sub_pos.2 h1
  set τ : ℝ := min (min ε (t₀ : ℝ)) (1 - t₁) / 2 with hτ
  have hm1 := min_le_left (min ε (t₀ : ℝ)) (1 - t₁)
  have hm2 := min_le_right (min ε (t₀ : ℝ)) (1 - t₁)
  have hm3 := min_le_left ε (t₀ : ℝ)
  have hm4 := min_le_right ε (t₀ : ℝ)
  have hτ0 : 0 < τ := by positivity
  have hτε : τ < ε := by rw [hτ]; linarith
  have hτt₀ : τ < t₀ := by rw [hτ]; linarith
  have hτt₁ : τ < 1 - t₁ := by rw [hτ]; linarith
  set G : ℝ × ℝ → X := squareExt (fun z => F z) with hGdef
  have hG : Continuous G := continuous_squareExt F.continuous
  set A : Set (ℝ × ℝ) := (univ : Set ℝ) ×ˢ Icc τ (1 - τ) with hAdef
  have hAc : Convex ℝ A := convex_univ.prod (convex_Icc _ _)
  have hGU : ∀ e ∈ A, G e ∈ U := by
    rintro ⟨a, b⟩ ⟨-, hb1, hb2⟩
    have hb : b ∈ I := ⟨by linarith, by linarith⟩
    rw [hGdef, squareExt_apply _ a hb]
    exact hF _ _ (by show 0 < b; linarith) (by show b < 1; linarith)
  -- the route
  set P0 : ℝ × ℝ := (0, t₀)
  set P1 : ℝ × ℝ := (0, τ)
  set P2 : ℝ × ℝ := (1, τ)
  set P3 : ℝ × ℝ := (1, 1 - τ)
  set P4 : ℝ × ℝ := (0, 1 - τ)
  set P5 : ℝ × ℝ := (0, t₁)
  set Good : Set (ℝ × ℝ) := {e | e ∈ A ∧ G e ∈ V} with hGood
  have hγG : ∀ u : ℝ, ∀ hu : u ∈ I, G (0, u) = γ ⟨u, hu⟩ := fun u hu => by
    rw [hGdef, squareExt_apply _ 0 hu, projIcc_zero']
    exact F.apply_zero _
  have s01 : segment ℝ P0 P1 ⊆ Good := by
    intro e he
    obtain ⟨r, ⟨hr0, hr1⟩, rfl⟩ := mem_segment_prod he
    have hu1 : τ ≤ (1 - r) * t₀ + r * τ := by nlinarith
    have hu2 : (1 - r) * t₀ + r * τ ≤ t₀ := by nlinarith
    have hu : (1 - r) * t₀ + r * τ ∈ I := ⟨by linarith, by linarith [t₀.2.2]⟩
    refine ⟨⟨mem_univ _, hu1, by linarith⟩, ?_⟩
    simp only [mul_zero, add_zero]
    rw [hγG _ hu]
    exact hγ₀ _ hu2
  have s12 : segment ℝ P1 P2 ⊆ Good := by
    intro e he
    obtain ⟨r, ⟨hr0, hr1⟩, rfl⟩ := mem_segment_prod he
    have hu : (1 - r) * τ + r * τ = τ := by ring
    have hτI : τ ∈ I := ⟨hτ0.le, by linarith⟩
    refine ⟨⟨mem_univ _, by rw [hu], by rw [hu]; linarith⟩, ?_⟩
    rw [hu, hGdef, squareExt_apply _ _ hτI]
    exact (hεV _ _).1 hτε
  have s23 : segment ℝ P2 P3 ⊆ Good := by
    intro e he
    obtain ⟨r, ⟨hr0, hr1⟩, rfl⟩ := mem_segment_prod he
    have hu1 : τ ≤ (1 - r) * τ + r * (1 - τ) := by nlinarith
    have hu2 : (1 - r) * τ + r * (1 - τ) ≤ 1 - τ := by nlinarith
    have hu : (1 - r) * τ + r * (1 - τ) ∈ I := ⟨by linarith, by linarith⟩
    refine ⟨⟨mem_univ _, hu1, hu2⟩, ?_⟩
    have h11 : (1 - r) * 1 + r * 1 = 1 := by ring
    rw [h11, hGdef, squareExt_apply _ _ hu, projIcc_one', F.apply_one]
    exact (hγ' _ (show (0 : ℝ) < _ by linarith) (show _ < (1 : ℝ) by linarith)).1
  have s34 : segment ℝ P3 P4 ⊆ Good := by
    intro e he
    obtain ⟨r, ⟨hr0, hr1⟩, rfl⟩ := mem_segment_prod he
    have hu : (1 - r) * (1 - τ) + r * (1 - τ) = 1 - τ := by ring
    have hτI : 1 - τ ∈ I := ⟨by linarith, by linarith⟩
    refine ⟨⟨mem_univ _, by rw [hu]; linarith, by rw [hu]⟩, ?_⟩
    rw [hu, hGdef, squareExt_apply _ _ hτI]
    exact (hεV _ _).2 (by show 1 - ε < 1 - τ; linarith)
  have s45 : segment ℝ P4 P5 ⊆ Good := by
    intro e he
    obtain ⟨r, ⟨hr0, hr1⟩, rfl⟩ := mem_segment_prod he
    have hu1 : (t₁ : ℝ) ≤ (1 - r) * (1 - τ) + r * t₁ := by nlinarith
    have hu2 : (1 - r) * (1 - τ) + r * t₁ ≤ 1 - τ := by nlinarith
    have hu : (1 - r) * (1 - τ) + r * t₁ ∈ I := ⟨by linarith [t₁.2.1], by linarith⟩
    refine ⟨⟨mem_univ _, by linarith, hu2⟩, ?_⟩
    simp only [mul_zero, add_zero]
    rw [hγG _ hu]
    exact hγ₁ _ hu1
  set η : Path P0 P5 := ((((Path.segment P0 P1).trans (Path.segment P1 P2)).trans
    (Path.segment P2 P3)).trans (Path.segment P3 P4)).trans (Path.segment P4 P5) with hη
  have hηG : ∀ t, η t ∈ Good := by
    intro t
    have : η t ∈ range η := mem_range_self t
    simp only [hη, Path.trans_range, Path.range_segment] at this
    rcases this with (((h | h) | h) | h) | h
    · exact s01 h
    · exact s12 h
    · exact s23 h
    · exact s34 h
    · exact s45 h
  have e0 : γ t₀ = G P0 := (hγG _ t₀.2).symm
  have e5 : γ t₁ = G P5 := (hγG _ t₁.2).symm
  refine ⟨(η.map hG).cast e0 e5, fun s => ?_, ?_⟩
  · exact ⟨(hηG s).2, hGU _ (hηG s).1⟩
  · have hP0 : P0 ∈ A := ⟨mem_univ _, hτt₀.le, by linarith⟩
    have hP5 : P5 ∈ A := ⟨mem_univ _, by linarith [t₁.2.1], by linarith⟩
    have hmain := homotopicIn_map_of_convex (Path.segment P0 P5) η hAc
      (fun t => by rw [Path.segment_apply]; exact hAc.lineMap_mem hP0 hP5 t.2)
      (fun t => (hηG t).1) hG hGU
    refine (hmain.cast e0 e5).of_eq ?_ rfl
    ext r
    rw [Path.cast_coe, Path.map_coe, comp_apply, Path.segment_apply, subpath_apply']
    have hl : AffineMap.lineMap P0 P5 (r : ℝ) = (0, (1 - (r : ℝ)) * t₀ + r * t₁) := by
      simp [P0, P5, AffineMap.lineMap_apply_module, smul_eq_mul]
    obtain ⟨w, hw1, hw2, hw⟩ := subpath_mem γ t₀ t₁ r
    have hwI : (1 - (r : ℝ)) * t₀ + r * t₁ ∈ I := by
      constructor <;> nlinarith [r.2.1, r.2.2, t₀.2.1, t₁.2.2]
    rw [hl, hγG _ hwI, Path.extend_apply γ hwI]

/-- The square argument for an almost trivial loop (the homotopy form). -/
theorem AlmostTrivial.exists_mid {γ : Path x x} (hγ : AlmostTrivial U γ) {V : Set X}
    (hV : IsOpen V) (hxV : x ∈ V) {t₀ t₁ : I} (h0 : 0 < (t₀ : ℝ)) (h : (t₀ : ℝ) < t₁)
    (h1 : (t₁ : ℝ) < 1) (hγ₀ : ∀ t : I, (t : ℝ) ≤ t₀ → γ t ∈ V)
    (hγ₁ : ∀ t : I, (t₁ : ℝ) ≤ t → γ t ∈ V) :
    ∃ ω : Path (γ t₀) (γ t₁), (∀ s, ω s ∈ V ∩ U) ∧ HomotopicIn U (subpath γ t₀ t₁) ω :=
  AlmostTrivialAt.exists_mid (hγ.2 V (hV.mem_nhds hxV)) hV hxV h0 h h1 hγ₀ hγ₁

end Square

/-! ### `lem:almost_homotopic_carac` -/

section Carac

variable {U : Set X} {x : X}

/-- `lem:almost_homotopic_carac` (`RamcovGX.tex:1271`) for the homotopy form. For `γ ∈ Ω(x,x,U)`: `γ` is almost
trivial iff for every open neighbourhood `V` of `x` and all `0 < t₀ < t₁ < 1` with
`γ([0,t₀] ∪ [t₁,1]) ⊆ V` there is a path `ω : γ(t₀) ⇝ γ(t₁)` in `V ∩ U` with `γ` homotopic in
`Ω(x,x,U)` to `γ_{|[0,t₀]} * ω * γ_{|[t₁,1]}`. -/
theorem almost_homotopic_carac {γ : Path x x} (hγ : MemOmega U γ) :
    AlmostTrivial U γ ↔ ∀ V : Set X, IsOpen V → x ∈ V → ∀ t₀ t₁ : I, 0 < (t₀ : ℝ) →
      ∀ h : (t₀ : ℝ) < t₁, (t₁ : ℝ) < 1 → (∀ t : I, (t : ℝ) ≤ t₀ → γ t ∈ V) →
      (∀ t : I, (t₁ : ℝ) ≤ t → γ t ∈ V) →
      ∃ ω : Path (γ t₀) (γ t₁), (∀ s, ω s ∈ V ∩ U) ∧
        OmegaHomotopic U γ (splice γ t₀ t₁ h ω) := by
  constructor
  · intro hat V hV hxV t₀ t₁ h0 h h1 hv0 hv1
    obtain ⟨ω, hω, hh⟩ := hat.exists_mid hV hxV h0 h h1 hv0 hv1
    exact ⟨ω, hω, splice_omegaHomotopic hγ h h1 hh⟩
  · intro H
    refine ⟨hγ, fun V hV => ?_⟩
    obtain ⟨V', hV'V, hV', hxV'⟩ := mem_nhds_iff.1 hV
    obtain ⟨t₀, h0, h0', hv0⟩ := exists_head_mem γ (hV'.mem_nhds hxV') (c := 1 / 2) (by norm_num)
    obtain ⟨t₁, h1', h1, hv1⟩ := exists_tail_mem γ (hV'.mem_nhds hxV') (c := 1 / 2) (by norm_num)
    have h : (t₀ : ℝ) < t₁ := by linarith
    obtain ⟨ω, hω, hh⟩ := H V' hV' hxV' t₀ t₁ h0 h h1 hv0 hv1
    refine ⟨splice γ t₀ t₁ h ω, fun t ht0 ht1 => ?_, hh⟩
    rcases splice_mem γ h ω t with ⟨ht, he⟩ | ⟨ht, he⟩ | ⟨s, hs⟩
    · rw [he]; exact ⟨hV'V (hv0 t ht), hγ t ht0 ht1⟩
    · rw [he]; exact ⟨hV'V (hv1 t ht), hγ t ht0 ht1⟩
    · rw [← hs]; exact ⟨hV'V (hω s).1, (hω s).2⟩

end Carac

/-! ### The compact-open reading (DEC-55): components of `Ω(x,x,U)` versus homotopies

`def:almost_trivial_loop` is read literally (DEC-55, `GX.AlmostTrivialCC`). The homotopy form
`GX.AlmostTrivial` always implies it (`GX.AlmostTrivial.almostTrivialCC`). The converse is proved
here when `U` is open and semilocally simply connected and `X` locally path-connected
(`GX.AlmostTrivialCC.almostTrivial`): for a fixed open `V ∋ x`, the set of loops of `Ω(x,x,U)`
homotopic with respect to `U` to a loop of `Ω(x,x,V ∩ U)` is clopen in the compact-open
`Ω(x,x,U)`, because it is decided by the middle of the loop, and a compact-open perturbation of
the middle is, up to short connecting paths near its ends, a homotopy in `U`
(`GX.eventually_homotopic_family`, by the homotopy lifting property of the universal covering of
`U`). -/

/-- **Perturbing a continuous family of paths in a semilocally simply connected space.** If
`δ q : a q ⇝ b q` is a family of paths of a locally path-connected, semilocally simply connected
space `Z`, continuous in `(t, q)`, then near `q₀` every `δ q` is homotopic to
`w₀ * δ q₀ * w₁` for any connecting paths `w₀`, `w₁` in path-connected neighbourhoods `A`, `B` of
the ends of `δ q₀`, inside given neighbourhoods `Oa`, `Ob`. -/
theorem eventually_homotopic_family {Z Q : Type*} [TopologicalSpace Z] [TopologicalSpace Q]
    [LocPathConnectedSpace Z] (hZ : SemilocallySimplyConnected Z) {a b : Q → Z}
    (δ : ∀ q, Path (a q) (b q)) (hδ : Continuous fun z : I × Q => δ z.2 z.1) (q₀ : Q)
    {Oa Ob : Set Z} (hOa : Oa ∈ 𝓝 (a q₀)) (hOb : Ob ∈ 𝓝 (b q₀)) :
    ∃ A ⊆ Oa, ∃ B ⊆ Ob, a q₀ ∈ A ∧ b q₀ ∈ B ∧ IsPathConnected A ∧ IsPathConnected B ∧
      ∀ᶠ q in 𝓝 q₀, a q ∈ A ∧ b q ∈ B ∧ ∀ (w₀ : Path (a q) (a q₀)) (w₁ : Path (b q₀) (b q)),
        (∀ t, w₀ t ∈ A) → (∀ t, w₁ t ∈ B) →
          (δ q).Homotopic ((w₀.trans (δ q₀)).trans w₁) := by
  have hacont : Continuous a := by
    have : Continuous fun q : Q => δ q 0 := hδ.comp (continuous_const.prodMk continuous_id)
    simpa only [Path.source] using this
  have hbcont : Continuous b := by
    have : Continuous fun q : Q => δ q 1 := hδ.comp (continuous_const.prodMk continuous_id)
    simpa only [Path.target] using this
  set p := UniversalCover.proj Z (a q₀)
  have cov : IsCoveringMap p := UniversalCover.isCoveringMap_proj hZ
  haveI : SimplyConnectedSpace (UniversalCover Z (a q₀)) := UniversalCover.simplyConnectedSpace hZ
  have cp : Continuous p := UniversalCover.continuous_proj
  set c₀ := UniversalCover.base (a q₀)
  obtain ⟨e, hc₀, hpe⟩ := cov.isLocalHomeomorph c₀
  have he : ∀ z ∈ e.target, p (e.symm z) = z := fun z hz => by rw [hpe]; exact e.right_inv hz
  have ha : a q₀ ∈ e.target := by
    have : e c₀ = a q₀ := by rw [← hpe]; rfl
    have h := e.map_source hc₀
    rw [this] at h; exact h
  set A := pathComponentIn (interior Oa ∩ e.target) (a q₀) with hAdef
  have hAo : IsOpen A := (isOpen_interior.inter e.open_target).pathComponentIn _
  have haA : a q₀ ∈ A := mem_pathComponentIn_self ⟨mem_interior_iff_mem_nhds.2 hOa, ha⟩
  have hAs : A ⊆ interior Oa ∩ e.target := pathComponentIn_subset
  have hAt : ∀ {z}, z ∈ A → z ∈ e.target := fun hz => (hAs hz).2
  let P := {q : Q // a q ∈ A}
  let f : C(P, UniversalCover Z (a q₀)) :=
    ⟨fun q => e.symm (a q.1), e.continuousOn_symm.comp_continuous
      (hacont.comp continuous_subtype_val) (fun q => hAt q.2)⟩
  let H : C(I × P, Z) := ⟨fun z => δ z.2.1 z.1,
    hδ.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))⟩
  have H_0 : ∀ q, H (0, q) = p (f q) := by
    intro q
    show δ q.1 0 = p (e.symm (a q.1))
    rw [he _ (hAt q.2)]; exact (δ q.1).source
  set Hl := cov.liftHomotopy H f H_0
  have hlift : ∀ z, p (Hl z) = H z := fun z => congrFun (cov.liftHomotopy_lifts H f H_0) z
  have hHl0 : ∀ q, Hl (0, q) = f q := cov.liftHomotopy_zero H f H_0
  set g : P → UniversalCover Z (a q₀) := fun q => Hl (1, q)
  have hg : Continuous g := Hl.continuous.comp (continuous_const.prodMk continuous_id)
  set q₀' : P := ⟨q₀, haA⟩
  obtain ⟨e₁, hg₁, hpe₁⟩ := cov.isLocalHomeomorph (g q₀')
  have he₁ : ∀ z ∈ e₁.target, p (e₁.symm z) = z := fun z hz => by rw [hpe₁]; exact e₁.right_inv hz
  have hgp : ∀ q, p (g q) = b q.1 := fun q => (hlift (1, q)).trans (δ q.1).target
  have hb : b q₀ ∈ e₁.target := by
    have : e₁ (g q₀') = b q₀ := by rw [← hpe₁]; exact hgp q₀'
    have h := e₁.map_source hg₁
    rw [this] at h; exact h
  set B := pathComponentIn (interior Ob ∩ e₁.target) (b q₀) with hBdef
  have hBo : IsOpen B := (isOpen_interior.inter e₁.open_target).pathComponentIn _
  have hbB : b q₀ ∈ B := mem_pathComponentIn_self ⟨mem_interior_iff_mem_nhds.2 hOb, hb⟩
  have hBs : B ⊆ interior Ob ∩ e₁.target := pathComponentIn_subset
  have hBt : ∀ {z}, z ∈ B → z ∈ e₁.target := fun hz => (hBs hz).2
  refine ⟨A, hAs.trans (inter_subset_left.trans interior_subset), B,
    hBs.trans (inter_subset_left.trans interior_subset), haA, hbB,
    isPathConnected_pathComponentIn ⟨mem_interior_iff_mem_nhds.2 hOa, ha⟩,
    isPathConnected_pathComponentIn ⟨mem_interior_iff_mem_nhds.2 hOb, hb⟩, ?_⟩
  have hPo : IsOpen {q | a q ∈ A} := hAo.preimage hacont
  have hO : IsOpen {q : P | g q ∈ e₁.source ∧ b q.1 ∈ B} :=
    (e₁.open_source.preimage hg).inter (hBo.preimage (hbcont.comp continuous_subtype_val))
  have hN := hPo.isOpenMap_subtype_val _ hO
  have hq₀N : q₀ ∈ Subtype.val '' {q : P | g q ∈ e₁.source ∧ b q.1 ∈ B} :=
    ⟨q₀', ⟨hg₁, hbB⟩, rfl⟩
  filter_upwards [hN.mem_nhds hq₀N] with q hq
  obtain ⟨q', ⟨hgq, hbq⟩, rfl⟩ := hq
  refine ⟨q'.2, hbq, fun w₀ w₁ hw₀ hw₁ => ?_⟩
  -- the lifts
  let Λ : ∀ r : P, Path (f r) (g r) := fun r =>
    { toFun := fun t => Hl (t, r)
      continuous_toFun := Hl.continuous.comp (continuous_id.prodMk continuous_const)
      source' := hHl0 r
      target' := rfl }
  have hgq' : e₁.symm (b q'.1) = g q' := by
    have : e₁ (g q') = b q'.1 := by rw [← hpe₁]; exact hgp q'
    rw [← this]; exact e₁.left_inv hgq
  have hg₀' : e₁.symm (b q₀) = g q₀' := by
    have : e₁ (g q₀') = b q₀ := by rw [← hpe₁]; exact hgp q₀'
    rw [← this]; exact e₁.left_inv hg₁
  let L₀ : Path (f q') (f q₀') :=
    { toFun := fun t => e.symm (w₀ t)
      continuous_toFun := e.continuousOn_symm.comp_continuous w₀.continuous (fun t => hAt (hw₀ t))
      source' := by simp only [w₀.source]; rfl
      target' := by simp only [w₀.target]; rfl }
  let L₁ : Path (g q₀') (g q') :=
    { toFun := fun t => e₁.symm (w₁ t)
      continuous_toFun := e₁.continuousOn_symm.comp_continuous w₁.continuous
        (fun t => hBt (hw₁ t))
      source' := by simp only [w₁.source]; exact hg₀'
      target' := by simp only [w₁.target]; exact hgq' }
  have hom : (Λ q').Homotopic ((L₀.trans (Λ q₀')).trans L₁) :=
    SimplyConnectedSpace.paths_homotopic _ _
  obtain ⟨F⟩ := hom.map ⟨p, cp⟩
  have h0 : a q'.1 = p (f q') := by rw [← H_0]; exact (δ q'.1).source.symm
  have h1 : b q'.1 = p (g q') := (hgp q').symm
  have F' := F.pathCast h0 h1
  have eL : ((Λ q').map cp).cast h0 h1 = δ q'.1 := by
    ext t; exact hlift (t, q')
  have eR : (((L₀.trans (Λ q₀')).trans L₁).map cp).cast h0 h1 = (w₀.trans (δ q₀)).trans w₁ := by
    ext t
    simp only [Path.cast_coe, Path.map_coe, comp_apply, Path.trans_apply]
    split_ifs
    · exact he _ (hAt (hw₀ _))
    · exact hlift _
    · exact he₁ _ (hBt (hw₁ _))
  rw [eL, eR] at F'
  exact ⟨F'⟩


open Path.Homotopic.Quotient in
/-- Cancelling the connecting paths: `P ≃ w₀ * Q * w₁` gives `Q ≃ w₀⁻¹ * P * w₁⁻¹`. -/
theorem homotopic_cancel_ends {Z : Type*} [TopologicalSpace Z] {a a' b b' : Z} {P : Path a' b'}
    {Q : Path a b} {w₀ : Path a' a} {w₁ : Path b b'}
    (h : P.Homotopic ((w₀.trans Q).trans w₁)) :
    Q.Homotopic ((w₀.symm.trans P).trans w₁.symm) := by
  rw [← Path.Homotopic.Quotient.eq] at h ⊢
  rw [mk_trans, mk_trans, mk_symm, mk_symm, h, mk_trans, mk_trans]
  rw [trans_assoc, trans_assoc, trans_symm, trans_refl, ← trans_assoc, symm_trans, refl_trans]

section CompactOpen

variable {U : Set X} {x : X}

/-- A loop which splices `γ`'s ends with a middle in `V ∩ U` homotopic in `U` to `γ`'s middle is
almost trivial at `V` (the easy half of `lem:almost_homotopic_carac`, at one `V`). -/
theorem AlmostTrivialAt.of_mid {γ : Path x x} (hγ : MemOmega U γ) {V : Set X} {t₀ t₁ : I}
    (h : (t₀ : ℝ) < t₁) (h1 : (t₁ : ℝ) < 1) (hγ₀ : ∀ t : I, (t : ℝ) ≤ t₀ → γ t ∈ V)
    (hγ₁ : ∀ t : I, (t₁ : ℝ) ≤ t → γ t ∈ V) (ω : Path (γ t₀) (γ t₁)) (hω : ∀ s, ω s ∈ V ∩ U)
    (hh : HomotopicIn U (subpath γ t₀ t₁) ω) : AlmostTrivialAt U V γ := by
  refine ⟨splice γ t₀ t₁ h ω, fun t ht0 ht1 => ?_, splice_omegaHomotopic hγ h h1 hh⟩
  rcases splice_mem γ h ω t with ⟨ht, he⟩ | ⟨ht, he⟩ | ⟨s, hs⟩
  · rw [he]; exact ⟨hγ₀ t ht, hγ t ht0 ht1⟩
  · rw [he]; exact ⟨hγ₁ t ht, hγ t ht0 ht1⟩
  · rw [← hs]; exact hω s

/-- A point of the compact-open `Ω(x,y,U)`, as a path. -/
def omegaPath {y : X} (q : OmegaSet U x y) : Path x y := ⟨q.1, q.2.1, q.2.2.1⟩

theorem omegaPath_apply {y : X} (q : OmegaSet U x y) (t : I) : omegaPath q t = q.1 t := rfl

theorem omegaPath_memOmega {y : X} (q : OmegaSet U x y) : MemOmega U (omegaPath q) := q.2.2.2

/-- The affine parameter `(1 - s) t₀ + s t₁`. -/
def affI (t₀ t₁ : I) (s : I) : I :=
  ⟨(1 - (s : ℝ)) * t₀ + s * t₁, by
    constructor <;> nlinarith [s.2.1, s.2.2, t₀.2.1, t₀.2.2, t₁.2.1, t₁.2.2]⟩

theorem continuous_affI (t₀ t₁ : I) : Continuous (affI t₀ t₁) :=
  Continuous.subtype_mk (by fun_prop) _

theorem subpath_eq_affI {y : X} (γ : Path x y) (t₀ t₁ s : I) :
    subpath γ t₀ t₁ s = γ (affI t₀ t₁ s) := by
  rw [subpath_apply']; exact Path.extend_apply γ (affI t₀ t₁ s).2

/-- **Almost triviality at an open `V` is locally constant on the compact-open `Ω(x,x,U)`**, for
`U` open and semilocally simply connected, `X` locally path-connected. -/
theorem eventually_almostTrivialAt_iff [LocPathConnectedSpace X] (hU : IsOpen U)
    (hsc : SemilocallySimplyConnected U) {V : Set X} (hV : IsOpen V) (hxV : x ∈ V)
    (q : OmegaSet U x x) :
    ∀ᶠ q' in 𝓝 q, (AlmostTrivialAt U V (omegaPath q) ↔ AlmostTrivialAt U V (omegaPath q')) := by
  haveI : LocPathConnectedSpace U := hU.locPathConnectedSpace
  obtain ⟨t₀, h0, h0', hv0⟩ := exists_head_mem (omegaPath q) (hV.mem_nhds hxV) (c := 1 / 2)
    (by norm_num)
  obtain ⟨t₁, h1', h1, hv1⟩ := exists_tail_mem (omegaPath q) (hV.mem_nhds hxV) (c := 1 / 2)
    (by norm_num)
  have h : (t₀ : ℝ) < t₁ := by linarith
  have haff0 : ∀ s, 0 < ((affI t₀ t₁ s : I) : ℝ) := fun s => by
    show 0 < (1 - (s : ℝ)) * t₀ + s * t₁; nlinarith [s.2.1, s.2.2]
  have haff1 : ∀ s, ((affI t₀ t₁ s : I) : ℝ) < 1 := fun s => by
    show (1 - (s : ℝ)) * t₀ + s * t₁ < 1; nlinarith [s.2.1, s.2.2]
  have hmid : ∀ (r : OmegaSet U x x) (s : I), subpath (omegaPath r) t₀ t₁ s ∈ U := fun r s => by
    rw [subpath_eq_affI]; exact omegaPath_memOmega r _ (haff0 s) (haff1 s)
  have hδ : Continuous fun z : I × OmegaSet U x x =>
      pathToSub (subpath (omegaPath z.2) t₀ t₁) (hmid z.2) z.1 := by
    refine Continuous.subtype_mk ?_ _
    have : Continuous fun z : I × OmegaSet U x x => z.2.1 (affI t₀ t₁ z.1) :=
      continuous_eval.comp ((continuous_subtype_val.comp continuous_snd).prodMk
        ((continuous_affI t₀ t₁).comp continuous_fst))
    exact this.congr fun z => (subpath_eq_affI (omegaPath z.2) t₀ t₁ z.1).symm
  obtain ⟨A, hAV, B, hBV, haA, hbB, hAc, hBc, hev⟩ := eventually_homotopic_family hsc
    (fun r => pathToSub (subpath (omegaPath r) t₀ t₁) (hmid r)) hδ q
    ((hV.preimage continuous_subtype_val).mem_nhds (hv0 t₀ le_rfl))
    ((hV.preimage continuous_subtype_val).mem_nhds (hv1 t₁ le_rfl))
  have hO : ∀ K : Set I, IsCompact K → (∀ t ∈ K, omegaPath q t ∈ V) →
      ∀ᶠ r in 𝓝 q, ∀ t ∈ K, omegaPath r t ∈ V := fun K hK hq =>
    ((ContinuousMap.isOpen_setOf_mapsTo hK hV).preimage continuous_subtype_val).mem_nhds
      fun t ht => hq t ht
  have hK0 : IsCompact {t : I | (t : ℝ) ≤ t₀} :=
    (isClosed_le continuous_subtype_val continuous_const).isCompact
  have hK1 : IsCompact {t : I | (t₁ : ℝ) ≤ t} :=
    (isClosed_le continuous_const continuous_subtype_val).isCompact
  filter_upwards [hev, hO _ hK0 fun t ht => hv0 t ht, hO _ hK1 fun t ht => hv1 t ht] with
    r ⟨ha', hb', hhom⟩ hr0 hr1
  set w₀ := (hAc.joinedIn _ ha' _ haA).somePath
  have hw₀ : ∀ t, w₀ t ∈ A := (hAc.joinedIn _ ha' _ haA).somePath_mem
  set w₁ := (hBc.joinedIn _ hbB _ hb').somePath
  have hw₁ : ∀ t, w₁ t ∈ B := (hBc.joinedIn _ hbB _ hb').somePath_mem
  have hh := hhom w₀ w₁ hw₀ hw₁
  have hw₀V : ∀ t, w₀ t ∈ (Subtype.val ⁻¹' V : Set U) := fun t => hAV (hw₀ t)
  have hw₁V : ∀ t, w₁ t ∈ (Subtype.val ⁻¹' V : Set U) := fun t => hBV (hw₁ t)
  constructor
  · intro hat
    obtain ⟨ω, hω, hhω⟩ := hat.exists_mid hV hxV h0 h h1 hv0 hv1
    obtain ⟨_h₁, hωU, hωs⟩ := homotopicIn_iff.1 hhω
    set Ω' := (w₀.trans (pathToSub ω hωU)).trans w₁
    have hΩ : (pathToSub (subpath (omegaPath r) t₀ t₁) (hmid r)).Homotopic Ω' :=
      hh.trans (((Path.Homotopic.refl w₀).hcomp hωs).hcomp (Path.Homotopic.refl w₁))
    have hΩV : ∀ s, Ω' s ∈ (Subtype.val ⁻¹' V : Set U) :=
      path_trans_mem (path_trans_mem hw₀V fun s => (hω s).1) hw₁V
    refine AlmostTrivialAt.of_mid (omegaPath_memOmega r) h h1 (fun t ht => hr0 t ht)
      (fun t ht => hr1 t ht) (Ω'.map continuous_subtype_val) (fun s => ⟨hΩV s, (Ω' s).2⟩) ?_
    exact homotopicIn_iff.2 ⟨hmid r, fun s => (Ω' s).2, hΩ⟩
  · intro hat
    obtain ⟨ω, hω, hhω⟩ := hat.exists_mid hV hxV h0 h h1 (fun t ht => hr0 t ht)
      (fun t ht => hr1 t ht)
    obtain ⟨_h₁, hωU, hωs⟩ := homotopicIn_iff.1 hhω
    set Ω' := (w₀.symm.trans (pathToSub ω hωU)).trans w₁.symm
    have hΩ : (pathToSub (subpath (omegaPath q) t₀ t₁) (hmid q)).Homotopic Ω' :=
      (homotopic_cancel_ends hh).trans
        (((Path.Homotopic.refl w₀.symm).hcomp hωs).hcomp (Path.Homotopic.refl w₁.symm))
    have hΩV : ∀ s, Ω' s ∈ (Subtype.val ⁻¹' V : Set U) :=
      path_trans_mem (path_trans_mem (path_symm_mem hw₀V) fun s => (hω s).1) (path_symm_mem hw₁V)
    refine AlmostTrivialAt.of_mid (omegaPath_memOmega q) h h1 hv0 hv1
      (Ω'.map continuous_subtype_val) (fun s => ⟨hΩV s, (Ω' s).2⟩) ?_
    exact homotopicIn_iff.2 ⟨hmid q, fun s => (Ω' s).2, hΩ⟩

/-- **DEC-55: the literal (compact-open) form implies the homotopy form**, for `U` open and
semilocally simply connected and `X` locally path-connected. -/
theorem AlmostTrivialCC.almostTrivial [LocPathConnectedSpace X] (hU : IsOpen U)
    (hsc : SemilocallySimplyConnected U) {γ : Path x x} (h : AlmostTrivialCC U γ) :
    AlmostTrivial U γ := by
  refine ⟨h.1.2.2, fun V hV => ?_⟩
  obtain ⟨V', hV'V, hV', hxV'⟩ := mem_nhds_iff.1 hV
  obtain ⟨η, hηC, hηV⟩ := h.2 V' (hV'.mem_nhds hxV')
  set S := OmegaSet U x x
  set K : Set S := {r | AlmostTrivialAt U V' (omegaPath r)}
  have hK : IsClopen K := by
    constructor
    · rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
      intro r hr
      exact (eventually_almostTrivialAt_iff hU hsc hV' hxV' r).mono fun r' h' hr' => hr (h'.2 hr')
    · rw [isOpen_iff_mem_nhds]
      intro r hr
      exact (eventually_almostTrivialAt_iff hU hsc hV' hxV' r).mono fun r' h' => h'.1 hr
  have hηS : η ∈ S := connectedComponentIn_subset _ _ hηC
  have hηK : (⟨η, hηS⟩ : S) ∈ K :=
    ⟨omegaPath ⟨η, hηS⟩, hηV.2.2, OmegaHomotopic.refl (omegaPath_memOmega _)⟩
  rw [connectedComponentIn_eq_image h.1] at hηC
  obtain ⟨r, hr, hrη⟩ := hηC
  have hr' : r = ⟨η, hηS⟩ := Subtype.ext hrη
  subst hr'
  have hmem : (⟨γ.toContinuousMap, h.1⟩ : S) ∈ connectedComponent (⟨η, hηS⟩ : S) := by
    rw [← connectedComponent_eq hr]; exact mem_connectedComponent
  obtain ⟨γ', hγ', hh⟩ := hK.connectedComponent_subset hηK hmem
  exact ⟨γ', fun t h0 h1 => ⟨hV'V (hγ' t h0 h1).1, (hγ' t h0 h1).2⟩, hh⟩

/-- **DEC-55**: under `U` open semilocally simply connected and `X` locally path-connected, the
literal and the homotopy forms of `def:almost_trivial_loop` agree. -/
theorem almostTrivialCC_iff [LocPathConnectedSpace X] (hU : IsOpen U)
    (hsc : SemilocallySimplyConnected U) {γ : Path x x} :
    AlmostTrivialCC U γ ↔ AlmostTrivial U γ :=
  ⟨AlmostTrivialCC.almostTrivial hU hsc, AlmostTrivial.almostTrivialCC⟩

/-- `lem:almost_homotopic_carac`, (ii) ⇒ (i), in the literal reading and with no hypothesis. -/
theorem AlmostTrivialCC.of_carac {γ : Path x x} (hγ : MemOmega U γ)
    (H : ∀ V : Set X, IsOpen V → x ∈ V → ∀ t₀ t₁ : I, 0 < (t₀ : ℝ) →
      ∀ h : (t₀ : ℝ) < t₁, (t₁ : ℝ) < 1 → (∀ t : I, (t : ℝ) ≤ t₀ → γ t ∈ V) →
      (∀ t : I, (t₁ : ℝ) ≤ t → γ t ∈ V) →
      ∃ ω : Path (γ t₀) (γ t₁), (∀ s, ω s ∈ V ∩ U) ∧
        OmegaHomotopic U γ (splice γ t₀ t₁ h ω)) : AlmostTrivialCC U γ :=
  ((almost_homotopic_carac hγ).2 H).almostTrivialCC

/-- `lem:almost_homotopic_carac` (`RamcovGX.tex:1271`) in the literal reading (DEC-55), for
`X` locally path-connected and `U` open and semilocally simply connected: `γ ∈ Ω(x,x,U)` is
almost trivial iff for every open neighbourhood `V` of `x` and all `0 < t₀ < t₁ < 1` with
`γ([0,t₀] ∪ [t₁,1]) ⊆ V` there is a path `ω : γ(t₀) ⇝ γ(t₁)` in `V ∩ U` with `γ` homotopic in
`Ω(x,x,U)` to `γ_{|[0,t₀]} * ω * γ_{|[t₁,1]}`. -/
theorem almost_homotopic_carac_cc [LocPathConnectedSpace X] (hU : IsOpen U)
    (hsc : SemilocallySimplyConnected U) {γ : Path x x} (hγ : MemOmega U γ) :
    AlmostTrivialCC U γ ↔ ∀ V : Set X, IsOpen V → x ∈ V → ∀ t₀ t₁ : I, 0 < (t₀ : ℝ) →
      ∀ h : (t₀ : ℝ) < t₁, (t₁ : ℝ) < 1 → (∀ t : I, (t : ℝ) ≤ t₀ → γ t ∈ V) →
      (∀ t : I, (t₁ : ℝ) ≤ t → γ t ∈ V) →
      ∃ ω : Path (γ t₀) (γ t₁), (∀ s, ω s ∈ V ∩ U) ∧
        OmegaHomotopic U γ (splice γ t₀ t₁ h ω) := by
  rw [almostTrivialCC_iff hU hsc]; exact almost_homotopic_carac hγ

/-- `lem:almost_homotopic_carac`, (ii) ⇒ (i), with **both** items in the literal reading
(DEC-55): "homotopic in `Ω(x,x,U)`" of item (ii) read as "in the same connected component of
the compact-open `Ω(x,x,U)`". No hypothesis on `U` or `X`. -/
theorem AlmostTrivialCC.of_carac_component {γ : Path x x} (hγ : MemOmega U γ)
    (H : ∀ V : Set X, IsOpen V → x ∈ V → ∀ t₀ t₁ : I, 0 < (t₀ : ℝ) →
      ∀ h : (t₀ : ℝ) < t₁, (t₁ : ℝ) < 1 → (∀ t : I, (t : ℝ) ≤ t₀ → γ t ∈ V) →
      (∀ t : I, (t₁ : ℝ) ≤ t → γ t ∈ V) →
      ∃ ω : Path (γ t₀) (γ t₁), (∀ s, ω s ∈ V ∩ U) ∧
        (splice γ t₀ t₁ h ω).toContinuousMap ∈
          connectedComponentIn (OmegaSet U x x) γ.toContinuousMap) :
    AlmostTrivialCC U γ := by
  refine ⟨⟨γ.source, γ.target, hγ⟩, fun V hV => ?_⟩
  obtain ⟨V', hV'V, hV', hxV'⟩ := mem_nhds_iff.1 hV
  obtain ⟨t₀, h0, h0', hv0⟩ := exists_head_mem γ (hV'.mem_nhds hxV') (c := 1 / 2) (by norm_num)
  obtain ⟨t₁, h1', h1, hv1⟩ := exists_tail_mem γ (hV'.mem_nhds hxV') (c := 1 / 2) (by norm_num)
  have h : (t₀ : ℝ) < t₁ := by linarith
  obtain ⟨ω, hω, hh⟩ := H V' hV' hxV' t₀ t₁ h0 h h1 hv0 hv1
  refine ⟨_, hh, (splice γ t₀ t₁ h ω).source, (splice γ t₀ t₁ h ω).target, fun t ht0 ht1 => ?_⟩
  show splice γ t₀ t₁ h ω t ∈ V ∩ U
  rcases splice_mem γ h ω t with ⟨ht, he⟩ | ⟨ht, he⟩ | ⟨s, hs⟩
  · rw [he]; exact ⟨hV'V (hv0 t ht), hγ t ht0 ht1⟩
  · rw [he]; exact ⟨hV'V (hv1 t ht), hγ t ht0 ht1⟩
  · rw [← hs]; exact ⟨hV'V (hω s).1, (hω s).2⟩

/-- **`lem:almost_homotopic_carac`** (`RamcovGX.tex:1271`) with both items in the literal reading
(DEC-55) and `U` semilocally simply connected (DEC-68 (b)): `γ ∈ Ω(x,x,U)` is almost trivial iff
for every open neighbourhood `V` of `x` and all `0 < t₀ < t₁ < 1` with
`γ([0,t₀] ∪ [t₁,1]) ⊆ V` there is a path `ω : γ(t₀) ⇝ γ(t₁)` in `V ∩ U` with
`γ_{|[0,t₀]} * ω * γ_{|[t₁,1]}` in the connected component of `γ` in the compact-open
`Ω(x,x,U)`. (The homotopy form of item (ii), `GX.almost_homotopic_carac_cc`, is stronger and
also holds.) -/
theorem almost_homotopic_carac_cc_component [LocPathConnectedSpace X] (hU : IsOpen U)
    (hsc : SemilocallySimplyConnected U) {γ : Path x x} (hγ : MemOmega U γ) :
    AlmostTrivialCC U γ ↔ ∀ V : Set X, IsOpen V → x ∈ V → ∀ t₀ t₁ : I, 0 < (t₀ : ℝ) →
      ∀ h : (t₀ : ℝ) < t₁, (t₁ : ℝ) < 1 → (∀ t : I, (t : ℝ) ≤ t₀ → γ t ∈ V) →
      (∀ t : I, (t₁ : ℝ) ≤ t → γ t ∈ V) →
      ∃ ω : Path (γ t₀) (γ t₁), (∀ s, ω s ∈ V ∩ U) ∧
        (splice γ t₀ t₁ h ω).toContinuousMap ∈
          connectedComponentIn (OmegaSet U x x) γ.toContinuousMap := by
  refine ⟨fun hat V hV hxV t₀ t₁ h0 h h1 hv0 hv1 => ?_, AlmostTrivialCC.of_carac_component hγ⟩
  obtain ⟨ω, hω, hh⟩ :=
    (almost_homotopic_carac_cc hU hsc hγ).1 hat V hV hxV t₀ t₁ h0 h h1 hv0 hv1
  exact ⟨ω, hω, hh.mem_connectedComponentIn⟩

end CompactOpen

/-! ### Groupoid calculus for homotopies in `U` -/

section Groupoid

variable {U : Set X} {x y z w : X}

open Path.Homotopic.Quotient in
theorem homotopicIn_iff_mk {γ₁ γ₂ : Path x y} (h₁ : ∀ t, γ₁ t ∈ U) (h₂ : ∀ t, γ₂ t ∈ U) :
    HomotopicIn U γ₁ γ₂ ↔ mk (pathToSub γ₁ h₁) = mk (pathToSub γ₂ h₂) := by
  rw [Path.Homotopic.Quotient.eq, homotopicIn_iff]
  exact ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨h₁, h₂, h⟩⟩

open Path.Homotopic.Quotient in
/-- `A⁻¹ * B ≃ W` iff `B ≃ A * W`, in `U`. -/
theorem homotopicIn_symm_trans_iff {A : Path x y} {B : Path x z} {W : Path y z}
    (hA : ∀ t, A t ∈ U) (hB : ∀ t, B t ∈ U) (hW : ∀ t, W t ∈ U) :
    HomotopicIn U (A.symm.trans B) W ↔ HomotopicIn U B (A.trans W) := by
  have h1 := path_trans_mem (path_symm_mem hA) hB
  have h2 := path_trans_mem hA hW
  rw [homotopicIn_iff_mk h1 hW, homotopicIn_iff_mk hB h2,
    pathToSub_trans _ _ (path_symm_mem hA) hB, pathToSub_symm _ hA, pathToSub_trans _ _ hA hW,
    mk_trans, mk_trans, mk_symm]
  constructor
  · intro h
    rw [← h, ← trans_assoc, trans_symm, refl_trans]
  · intro h
    rw [h, ← trans_assoc, symm_trans, refl_trans]

open Path.Homotopic.Quotient in
theorem homotopicIn_trans_assoc {p : Path x y} {q : Path y z} {r : Path z w}
    (hp : ∀ t, p t ∈ U) (hq : ∀ t, q t ∈ U) (hr : ∀ t, r t ∈ U) :
    HomotopicIn U ((p.trans q).trans r) (p.trans (q.trans r)) := by
  rw [homotopicIn_iff_mk (path_trans_mem (path_trans_mem hp hq) hr)
    (path_trans_mem hp (path_trans_mem hq hr)), pathToSub_trans _ _ (path_trans_mem hp hq) hr,
    pathToSub_trans _ _ hp hq, pathToSub_trans _ _ hp (path_trans_mem hq hr),
    pathToSub_trans _ _ hq hr]
  simp only [mk_trans, trans_assoc]

open Path.Homotopic.Quotient in
/-- `B ≃ A * W` gives `A ≃ B * W⁻¹`, in `U`. -/
theorem homotopicIn_swap {A : Path x y} {B : Path x z} {W : Path y z}
    (hA : ∀ t, A t ∈ U) (hB : ∀ t, B t ∈ U) (hW : ∀ t, W t ∈ U)
    (h : HomotopicIn U B (A.trans W)) : HomotopicIn U A (B.trans W.symm) := by
  rw [homotopicIn_iff_mk hB (path_trans_mem hA hW), pathToSub_trans _ _ hA hW, mk_trans] at h
  rw [homotopicIn_iff_mk hA (path_trans_mem hB (path_symm_mem hW)),
    pathToSub_trans _ _ hB (path_symm_mem hW), pathToSub_symm _ hW, mk_trans, mk_symm, h,
    trans_assoc, trans_symm, trans_refl]

end Groupoid

/-! ### `def:almost_homotopic_paths`, `rem:implicitely_two_almost_homotopic` -/

/-- The homotopy form of `def:almost_homotopic_paths` (`RamcovGX.tex:1262`). Two paths `γ₁, γ₂ ∈ Ω(x,y,U)` are
*almost homotopic with respect to `U`* if the loop `γ₂⁻¹ * γ₁` is almost trivial with respect
to `U`. (Being a loop of `Ω(y,y,U)`, this forces `x ∈ U` and `γ₁, γ₂ ∈ Ω(x,y,U)`:
`GX.AlmostHomotopic.mem`.) -/
def AlmostHomotopic (U : Set X) {x y : X} (γ₁ γ₂ : Path x y) : Prop :=
  AlmostTrivial U (γ₂.symm.trans γ₁)

section AlmostHom

variable {U : Set X} {x y : X}

/-- `rem:implicitely_two_almost_homotopic` (`RamcovGX.tex:1268`) for the homotopy form: two almost homotopic paths
have the same ends (here by typing: both are paths `x ⇝ y`). -/
theorem AlmostHomotopic.ends {γ₁ γ₂ : Path x y} (_ : AlmostHomotopic U γ₁ γ₂) :
    γ₁ 0 = γ₂ 0 ∧ γ₁ 1 = γ₂ 1 := by
  simp

theorem loop_apply_le (γ₁ γ₂ : Path x y) {t : I} (ht : (t : ℝ) ≤ 1 / 2) :
    (γ₂.symm.trans γ₁) t = γ₂ ⟨1 - 2 * t, by constructor <;> linarith [t.2.1]⟩ := by
  rw [Path.trans_apply, dif_pos ht, Path.symm_apply]
  congr 1

theorem loop_apply_ge (γ₁ γ₂ : Path x y) {t : I} (ht : 1 / 2 ≤ (t : ℝ)) :
    (γ₂.symm.trans γ₁) t = γ₁ ⟨2 * t - 1, by constructor <;> linarith [t.2.2]⟩ := by
  rw [Path.trans_apply]
  split_ifs with h
  · have h' : (t : ℝ) = 1 / 2 := le_antisymm h ht
    rw [Path.symm_apply]
    have e1 : (σ ⟨2 * (t : ℝ), (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, h⟩⟩ : I) = 0 :=
      Subtype.ext (by simp [h'])
    have e2 : (⟨2 * (t : ℝ) - 1, by constructor <;> linarith [t.2.2]⟩ : I) = 0 :=
      Subtype.ext (by simp [h'])
    simp only [comp_apply, e1, e2, γ₂.source, γ₁.source]
  · rfl

/-- The values of a path of `Ω(x,y,U)` before time `1` lie in `U`, when `x ∈ U`. -/
theorem MemOmega.extend_mem {γ : Path x y} (hγ : MemOmega U γ) (hx : x ∈ U) {r : ℝ}
    (hr : r < 1) : γ.extend r ∈ U := by
  rcases le_or_gt r 0 with h | h
  · rw [Path.extend_of_le_zero γ h]; exact hx
  · rw [Path.extend_apply γ ⟨h.le, hr.le⟩]; exact hγ _ h hr

theorem MemOmega.loop {γ₁ γ₂ : Path x y} (hx : x ∈ U) (h₁ : MemOmega U γ₁)
    (h₂ : MemOmega U γ₂) : MemOmega U (γ₂.symm.trans γ₁) := by
  intro t h0 h1
  rcases le_total (t : ℝ) (1 / 2) with h | h
  · rw [loop_apply_le γ₁ γ₂ h]
    rcases eq_or_lt_of_le h with h' | h'
    · have : (⟨1 - 2 * (t : ℝ), by constructor <;> linarith [t.2.1]⟩ : I) = 0 :=
        Subtype.ext (by simp [h'])
      rw [this, γ₂.source]; exact hx
    · exact h₂ _ (show (0 : ℝ) < 1 - 2 * t by linarith) (show 1 - 2 * (t : ℝ) < 1 by linarith)
  · rw [loop_apply_ge γ₁ γ₂ h]
    rcases eq_or_lt_of_le h with h' | h'
    · have : (⟨2 * (t : ℝ) - 1, by constructor <;> linarith [t.2.2]⟩ : I) = 0 :=
        Subtype.ext (by simp [← h'])
      rw [this, γ₁.source]; exact hx
    · exact h₁ _ (show (0 : ℝ) < 2 * t - 1 by linarith) (show 2 * (t : ℝ) - 1 < 1 by linarith)

/-- If the loop `γ₂⁻¹ * γ₁` lies in `Ω(y,y,U)`, then `x ∈ U` and `γ₁, γ₂ ∈ Ω(x,y,U)`. -/
theorem MemOmega.of_loop {γ₁ γ₂ : Path x y} (hL : MemOmega U (γ₂.symm.trans γ₁)) :
    x ∈ U ∧ MemOmega U γ₁ ∧ MemOmega U γ₂ := by
  have hhalf : (0 : ℝ) < ((⟨1 / 2, by norm_num, by norm_num⟩ : I) : ℝ) := by norm_num
  refine ⟨?_, fun t h0 h1 => ?_, fun t h0 h1 => ?_⟩
  · have := hL ⟨1 / 2, by norm_num, by norm_num⟩ hhalf (by norm_num)
    rw [loop_apply_le γ₁ γ₂ (by norm_num)] at this
    have e : (⟨1 - 2 * (1 / 2 : ℝ), by norm_num, by norm_num⟩ : I) = 0 := Subtype.ext (by norm_num)
    rwa [e, γ₂.source] at this
  · have := hL ⟨(1 + t) / 2, by constructor <;> linarith⟩ (by show (0 : ℝ) < _; linarith)
      (by show _ < (1 : ℝ); linarith)
    rw [loop_apply_ge γ₁ γ₂ (by show (1 / 2 : ℝ) ≤ _; linarith)] at this
    have e : (⟨2 * ((1 + (t : ℝ)) / 2) - 1, by constructor <;> linarith⟩ : I) = t :=
      Subtype.ext (by simp; ring)
    rwa [e] at this
  · have := hL ⟨(1 - t) / 2, by constructor <;> linarith⟩ (by show (0 : ℝ) < _; linarith)
      (by show _ < (1 : ℝ); linarith)
    rw [loop_apply_le γ₁ γ₂ (by show _ ≤ (1 / 2 : ℝ); linarith)] at this
    have e : (⟨1 - 2 * ((1 - (t : ℝ)) / 2), by constructor <;> linarith⟩ : I) = t :=
      Subtype.ext (by simp; ring)
    rwa [e] at this

/-- An almost homotopy lives in `Ω(x,y,U)` with `x ∈ U`. -/
theorem AlmostHomotopic.mem {γ₁ γ₂ : Path x y} (h : AlmostHomotopic U γ₁ γ₂) :
    x ∈ U ∧ MemOmega U γ₁ ∧ MemOmega U γ₂ :=
  MemOmega.of_loop h.1

/-- The parameter `(1 - s)/2`. -/
def loopLo (s : I) : I := ⟨(1 - s) / 2, by constructor <;> linarith [s.2.1, s.2.2]⟩

/-- The parameter `(1 + s)/2`. -/
def loopHi (s : I) : I := ⟨(1 + s) / 2, by constructor <;> linarith [s.2.1, s.2.2]⟩

theorem loop_loopLo (γ₁ γ₂ : Path x y) (s : I) : (γ₂.symm.trans γ₁) (loopLo s) = γ₂ s := by
  rw [loop_apply_le γ₁ γ₂ (by show (1 - (s : ℝ)) / 2 ≤ 1 / 2; linarith [s.2.1])]
  congr 1; exact Subtype.ext (by simp [loopLo]; ring)

theorem loop_loopHi (γ₁ γ₂ : Path x y) (s : I) : (γ₂.symm.trans γ₁) (loopHi s) = γ₁ s := by
  rw [loop_apply_ge γ₁ γ₂ (by show 1 / 2 ≤ (1 + (s : ℝ)) / 2; linarith [s.2.1])]
  congr 1; exact Subtype.ext (by simp [loopHi]; ring)

/-- The middle of `γ₂⁻¹ * γ₁` between `(1-s)/2` and `(1+s)/2` is `(γ₂{|[0,s]})⁻¹ * γ₁{|[0,s]}`. -/
theorem subpath_loop (γ₁ γ₂ : Path x y) {s : I} (hs : 0 < (s : ℝ)) :
    subpath (γ₂.symm.trans γ₁) (loopLo s) (loopHi s) =
      ((head γ₂ s).symm.trans (head γ₁ s)).cast (loop_loopLo γ₁ γ₂ s)
        (loop_loopHi γ₁ γ₂ s) := by
  ext r
  rw [Path.cast_coe, subpath_apply', Path.trans_apply]
  have hr0 := r.2.1
  have hr1 := r.2.2
  have hs1 := s.2.2
  have hu : (1 - (r : ℝ)) * (loopLo s : ℝ) + r * (loopHi s : ℝ) ∈ I := by
    simp only [loopLo, loopHi]; constructor <;> nlinarith
  rw [Path.extend_apply _ hu]
  split_ifs with h
  · rw [loop_apply_le γ₁ γ₂ (by simp only [loopLo, loopHi]; nlinarith), Path.symm_apply,
      comp_apply, head_apply, subpath_apply']
    have hv : (1 - ((σ ⟨2 * (r : ℝ), (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨hr0, h⟩⟩ : I) :
        ℝ)) * ((0 : I) : ℝ) + ((σ ⟨2 * (r : ℝ), (unitInterval.mul_pos_mem_iff zero_lt_two).2
        ⟨hr0, h⟩⟩ : I) : ℝ) * s ∈ I := by
      simp only [unitInterval.coe_symm_eq, Icc.coe_zero, mul_zero, zero_add]
      constructor <;> nlinarith
    rw [Path.extend_apply _ hv]
    congr 1
    exact Subtype.ext (by simp [loopLo, loopHi]; ring)
  · rw [not_le] at h
    rw [loop_apply_ge γ₁ γ₂ (by simp only [loopLo, loopHi]; nlinarith), head_apply,
      subpath_apply']
    have hv : (1 - ((⟨2 * (r : ℝ) - 1, unitInterval.two_mul_sub_one_mem_iff.2 ⟨h.le, hr1⟩⟩ : I) :
        ℝ)) * ((0 : I) : ℝ) + ((⟨2 * (r : ℝ) - 1, unitInterval.two_mul_sub_one_mem_iff.2
        ⟨h.le, hr1⟩⟩ : I) : ℝ) * s ∈ I := by
      simp only [Icc.coe_zero, mul_zero, zero_add]
      constructor <;> nlinarith
    rw [Path.extend_apply _ hv]
    congr 1
    exact Subtype.ext (by simp [loopLo, loopHi]; ring)

end AlmostHom

/-! ### The germ form of almost homotopy, and `lem:hausdorff_first_countable_connected` -/

section Germ

variable {U : Set X} {x y : X}

/-- The class of a path of `U` in the fundamental groupoid of the subspace `U`. -/
abbrev qU {a b : X} (γ : Path a b) (h : ∀ t, γ t ∈ U) :
    Path.Homotopic.Quotient (⟨a, γ.source ▸ h 0⟩ : U) ⟨b, γ.target ▸ h 1⟩ :=
  Path.Homotopic.Quotient.mk (pathToSub γ h)

theorem qU_trans {a b c : X} (γ : Path a b) (γ' : Path b c) (h : ∀ t, γ t ∈ U)
    (h' : ∀ t, γ' t ∈ U) :
    qU (γ.trans γ') (path_trans_mem h h') = (qU γ h).trans (qU γ' h') := by
  rw [qU, pathToSub_trans _ _ h h', Path.Homotopic.Quotient.mk_trans]

theorem homotopicIn_iff_qU {a b : X} {γ₁ γ₂ : Path a b} (h₁ : ∀ t, γ₁ t ∈ U)
    (h₂ : ∀ t, γ₂ t ∈ U) : HomotopicIn U γ₁ γ₂ ↔ qU γ₁ h₁ = qU γ₂ h₂ :=
  homotopicIn_iff_mk h₁ h₂

theorem head_mem {γ : Path x y} (hγ : MemOmega U γ) (hx : x ∈ U) {s : I} (hs : (s : ℝ) < 1)
    (t : I) : head γ s t ∈ U := by
  rw [head_apply, subpath_apply']
  refine hγ.extend_mem hx ?_
  simp only [Icc.coe_zero, mul_zero, zero_add]
  nlinarith [t.2.1, t.2.2, s.2.1]

theorem subpath_mem_of_memOmega {γ : Path x y} (hγ : MemOmega U γ) (hx : x ∈ U) {a b : I}
    (ha : (a : ℝ) < 1) (hb : (b : ℝ) < 1) (t : I) : subpath γ a b t ∈ U := by
  obtain ⟨w, -, hw2, hw⟩ := subpath_mem γ a b t
  rw [hw, ← Path.extend_extends' γ w]
  exact hγ.extend_mem hx (hw2.trans_lt (max_lt ha hb))

theorem subpath_mem_of_tail {γ : Path x y} {V : Set X} {c : ℝ}
    (hV : ∀ t : I, c ≤ t → γ t ∈ V) {a b : I} (ha : c ≤ a) (hb : c ≤ b) (t : I) :
    subpath γ a b t ∈ V := by
  obtain ⟨w, hw1, -, hw⟩ := subpath_mem γ a b t
  rw [hw]; exact hV w ((le_min ha hb).trans hw1)

theorem head_trans_subpath {γ : Path x y} (hγ : MemOmega U γ) (hx : x ∈ U) {a b : I}
    (ha : (a : ℝ) < 1) (hb : (b : ℝ) < 1) :
    HomotopicIn U (head γ b) ((head γ a).trans (subpath γ a b)) := by
  have h := subpath_trans_homotopicIn (U := U) γ 0 a b (fun r _ hr => hγ.extend_mem hx
    (hr.trans_lt (max_lt (max_lt (by simp) ha) hb)))
  refine (h.cast γ.source.symm rfl).of_eq rfl ?_
  ext t
  simp only [Path.cast_coe, Path.trans_apply]
  split_ifs <;> rfl

/-- **The germ form of almost homotopy.** `γ₁ ≈ γ₂` iff for every open neighbourhood `V` of `y`
and all `s₁, s₂ < 1` with `γᵢ([sᵢ,1]) ⊆ V` there is `ω : γ₂(s₂) ⇝ γ₁(s₁)` in `V ∩ U` with
`γ₁{|[0,s₁]} ≃ γ₂{|[0,s₂]} * ω` in `U`. (`GX.almostHomotopic_iff_germEquiv`.) -/
def GermEquiv (U : Set X) {x y : X} (γ₁ γ₂ : Path x y) : Prop :=
  ∀ V : Set X, IsOpen V → y ∈ V → ∀ s₁ s₂ : I, (s₁ : ℝ) < 1 → (s₂ : ℝ) < 1 →
    (∀ t : I, (s₁ : ℝ) ≤ t → γ₁ t ∈ V) → (∀ t : I, (s₂ : ℝ) ≤ t → γ₂ t ∈ V) →
    ∃ ω : Path (γ₂ s₂) (γ₁ s₁), (∀ τ, ω τ ∈ V ∩ U) ∧
      HomotopicIn U (head γ₁ s₁) ((head γ₂ s₂).trans ω)

open Path.Homotopic.Quotient in
/-- Moving the cut points of a germ relation along the tails. -/
theorem germ_adjust {γ₁ γ₂ : Path x y} (h₁ : MemOmega U γ₁) (h₂ : MemOmega U γ₂) (hx : x ∈ U)
    {s s' a a' : I} (hs : (s : ℝ) < 1) (hs' : (s' : ℝ) < 1) (ha : (a : ℝ) < 1) (ha' : (a' : ℝ) < 1)
    {ω : Path (γ₂ s') (γ₁ s)} (hω : ∀ τ, ω τ ∈ U)
    (h : HomotopicIn U (head γ₁ s) ((head γ₂ s').trans ω)) :
    HomotopicIn U (head γ₁ a)
      ((head γ₂ a').trans ((subpath γ₂ a' s').trans (ω.trans (subpath γ₁ s a)))) := by
  have m1 := subpath_mem_of_memOmega h₁ hx hs ha
  have m2 := subpath_mem_of_memOmega h₂ hx ha' hs'
  have e1 := (homotopicIn_iff_qU (head_mem h₁ hx ha)
    (path_trans_mem (head_mem h₁ hx hs) m1)).1 (head_trans_subpath h₁ hx hs ha)
  have e2 := (homotopicIn_iff_qU (head_mem h₂ hx hs')
    (path_trans_mem (head_mem h₂ hx ha') m2)).1 (head_trans_subpath h₂ hx ha' hs')
  have e3 := (homotopicIn_iff_qU (head_mem h₁ hx hs)
    (path_trans_mem (head_mem h₂ hx hs') hω)).1 h
  rw [qU_trans _ _ (head_mem h₁ hx hs) m1] at e1
  rw [qU_trans _ _ (head_mem h₂ hx ha') m2] at e2
  rw [qU_trans _ _ (head_mem h₂ hx hs') hω] at e3
  rw [homotopicIn_iff_qU (head_mem h₁ hx ha) (path_trans_mem (head_mem h₂ hx ha')
    (path_trans_mem m2 (path_trans_mem hω m1))), qU_trans _ _ (head_mem h₂ hx ha')
    (path_trans_mem m2 (path_trans_mem hω m1)), qU_trans _ _ m2 (path_trans_mem hω m1),
    qU_trans _ _ hω m1, e1, e3, e2]
  simp only [trans_assoc]

theorem germEquiv_refl {γ : Path x y} (hγ : MemOmega U γ) (hx : x ∈ U) : GermEquiv U γ γ := by
  intro V hV hyV s₁ s₂ hs₁ hs₂ ht₁ ht₂
  refine ⟨subpath γ s₂ s₁, fun τ => ?_, head_trans_subpath hγ hx hs₂ hs₁⟩
  obtain ⟨w, hw1, hw2, hw⟩ := subpath_mem γ s₂ s₁ τ
  refine ⟨?_, subpath_mem_of_memOmega hγ hx hs₂ hs₁ τ⟩
  rw [hw]
  rcases le_total (s₂ : ℝ) s₁ with h | h
  · exact ht₂ w (by rw [min_eq_left h] at hw1; exact hw1)
  · exact ht₁ w (by rw [min_eq_right h] at hw1; exact hw1)

theorem GermEquiv.symm {γ₁ γ₂ : Path x y} (h₁ : MemOmega U γ₁) (h₂ : MemOmega U γ₂)
    (hx : x ∈ U) (h : GermEquiv U γ₁ γ₂) : GermEquiv U γ₂ γ₁ := by
  intro V hV hyV a b ha hb hta htb
  obtain ⟨ω, hω, hh⟩ := h V hV hyV b a hb ha htb hta
  exact ⟨ω.symm, path_symm_mem hω, homotopicIn_swap (head_mem h₂ hx ha) (head_mem h₁ hx hb)
    (fun τ => (hω τ).2) hh⟩

theorem GermEquiv.trans {γ₁ γ₂ γ₃ : Path x y} (h₃ : MemOmega U γ₃) (hx : x ∈ U) (h : GermEquiv U γ₁ γ₂) (h' : GermEquiv U γ₂ γ₃) :
    GermEquiv U γ₁ γ₃ := by
  intro V hV hyV s₁ s₃ hs₁ hs₃ ht₁ ht₃
  obtain ⟨s₂, -, hs₂, ht₂⟩ := exists_tail_mem γ₂ (hV.mem_nhds hyV) (c := 1) one_pos
  obtain ⟨ω₁, hω₁, hh₁⟩ := h V hV hyV s₁ s₂ hs₁ hs₂ ht₁ ht₂
  obtain ⟨ω₂, hω₂, hh₂⟩ := h' V hV hyV s₂ s₃ hs₂ hs₃ ht₂ ht₃
  have hU₁ : ∀ τ, ω₁ τ ∈ U := fun τ => (hω₁ τ).2
  have hU₂ : ∀ τ, ω₂ τ ∈ U := fun τ => (hω₂ τ).2
  refine ⟨ω₂.trans ω₁, path_trans_mem hω₂ hω₁, ?_⟩
  refine hh₁.trans ((hh₂.hcomp (HomotopicIn.refl hU₁)).trans ?_)
  exact homotopicIn_trans_assoc (head_mem h₃ hx hs₃) hU₂ hU₁

theorem AlmostHomotopic.germEquiv {γ₁ γ₂ : Path x y} (h : AlmostHomotopic U γ₁ γ₂) :
    GermEquiv U γ₁ γ₂ := by
  obtain ⟨hx, h₁, h₂⟩ := h.mem
  intro V hV hyV s₁ s₂ hs₁ hs₂ ht₁ ht₂
  set s : I := ⟨max (max (s₁ : ℝ) s₂) (1 / 2), by
    constructor
    · exact le_max_of_le_right (by norm_num)
    · exact max_le (max_le s₁.2.2 s₂.2.2) (by norm_num)⟩ with hsdef
  have hs1 : (s : ℝ) < 1 := max_lt (max_lt hs₁ hs₂) (by norm_num)
  have hs0 : (1 / 2 : ℝ) ≤ s := le_max_right _ _
  have hss₁ : (s₁ : ℝ) ≤ s := (le_max_left _ _).trans (le_max_left _ _)
  have hss₂ : (s₂ : ℝ) ≤ s := (le_max_right _ _).trans (le_max_left _ _)
  have hlo : ∀ t : I, (t : ℝ) ≤ loopLo s → (γ₂.symm.trans γ₁) t ∈ V := by
    intro t ht
    have ht' : (t : ℝ) ≤ 1 / 2 := ht.trans (by simp only [loopLo]; linarith)
    rw [loop_apply_le γ₁ γ₂ ht']
    exact ht₂ _ (by simp only [loopLo] at ht; show (s₂ : ℝ) ≤ 1 - 2 * t; linarith)
  have hhi : ∀ t : I, (loopHi s : ℝ) ≤ t → (γ₂.symm.trans γ₁) t ∈ V := by
    intro t ht
    have ht' : (1 / 2 : ℝ) ≤ t := le_trans (by simp only [loopHi]; linarith [s.2.1]) ht
    rw [loop_apply_ge γ₁ γ₂ ht']
    exact ht₁ _ (by simp only [loopHi] at ht; show (s₁ : ℝ) ≤ 2 * t - 1; linarith)
  obtain ⟨ω', hω', hh⟩ := h.exists_mid hV hyV (t₀ := loopLo s) (t₁ := loopHi s)
    (by simp only [loopLo]; linarith) (by simp only [loopLo, loopHi]; linarith)
    (by simp only [loopHi]; linarith) hlo hhi
  rw [subpath_loop γ₁ γ₂ (by linarith)] at hh
  set ω : Path (γ₂ s) (γ₁ s) := ω'.cast (loop_loopLo γ₁ γ₂ s).symm (loop_loopHi γ₁ γ₂ s).symm
  have hωV : ∀ τ, ω τ ∈ V ∩ U := fun τ => hω' τ
  have hh' : HomotopicIn U ((head γ₂ s).symm.trans (head γ₁ s)) ω :=
    (hh.cast (loop_loopLo γ₁ γ₂ s).symm (loop_loopHi γ₁ γ₂ s).symm).of_eq (by ext; rfl) rfl
  have hB := (homotopicIn_symm_trans_iff (head_mem h₂ hx hs1) (head_mem h₁ hx hs1)
    (fun τ => (hωV τ).2)).1 hh'
  refine ⟨_, fun τ => ?_, germ_adjust h₁ h₂ hx hs1 hs1 hs₁ hs₂ (fun τ => (hωV τ).2) hB⟩
  have m1 := subpath_mem_of_tail ht₂ (le_refl (s₂ : ℝ)) hss₂
  have m2 := subpath_mem_of_tail ht₁ hss₁ (le_refl (s₁ : ℝ))
  have m1' := subpath_mem_of_memOmega h₂ hx hs₂ hs1
  have m2' := subpath_mem_of_memOmega h₁ hx hs1 hs₁
  exact path_trans_mem (W := V ∩ U) (fun t => ⟨m1 t, m1' t⟩)
    (path_trans_mem hωV fun t => ⟨m2 t, m2' t⟩) τ

theorem almostHomotopic_of_germEquiv {γ₁ γ₂ : Path x y} (hx : x ∈ U) (h₁ : MemOmega U γ₁)
    (h₂ : MemOmega U γ₂) (h : GermEquiv U γ₁ γ₂) : AlmostHomotopic U γ₁ γ₂ := by
  have hL := MemOmega.loop hx h₁ h₂
  refine ⟨hL, fun V hV => ?_⟩
  obtain ⟨V', hV'V, hV', hyV'⟩ := mem_nhds_iff.1 hV
  obtain ⟨a, -, ha, hta⟩ := exists_tail_mem γ₁ (hV'.mem_nhds hyV') (c := 1) one_pos
  obtain ⟨b, -, hb, htb⟩ := exists_tail_mem γ₂ (hV'.mem_nhds hyV') (c := 1) one_pos
  set s : I := ⟨max (max (a : ℝ) b) (1 / 2), by
    constructor
    · exact le_max_of_le_right (by norm_num)
    · exact max_le (max_le a.2.2 b.2.2) (by norm_num)⟩ with hsdef
  have hs1 : (s : ℝ) < 1 := max_lt (max_lt ha hb) (by norm_num)
  have hs0 : (1 / 2 : ℝ) ≤ s := le_max_right _ _
  have hsa : (a : ℝ) ≤ s := (le_max_left _ _).trans (le_max_left _ _)
  have hsb : (b : ℝ) ≤ s := (le_max_right _ _).trans (le_max_left _ _)
  obtain ⟨ω, hω, hh⟩ := h V' hV' hyV' s s hs1 hs1 (fun t ht => hta t (hsa.trans ht))
    (fun t ht => htb t (hsb.trans ht))
  have hh' := (homotopicIn_symm_trans_iff (head_mem h₂ hx hs1) (head_mem h₁ hx hs1)
    (fun τ => (hω τ).2)).2 hh
  have hmid : HomotopicIn U (subpath (γ₂.symm.trans γ₁) (loopLo s) (loopHi s))
      (ω.cast (loop_loopLo γ₁ γ₂ s) (loop_loopHi γ₁ γ₂ s)) := by
    rw [subpath_loop γ₁ γ₂ (by linarith)]
    exact hh'.cast _ _
  have hlohi : ((loopLo s : I) : ℝ) < loopHi s := by simp only [loopLo, loopHi]; linarith
  refine ⟨_, fun t ht0 ht1 => ?_,
    splice_omegaHomotopic hL hlohi (by simp only [loopHi]; linarith) hmid⟩
  rcases splice_mem _ hlohi (ω.cast (loop_loopLo γ₁ γ₂ s) (loop_loopHi γ₁ γ₂ s)) t with
    ⟨ht, he⟩ | ⟨ht, he⟩ | ⟨r, hr⟩
  · rw [he]
    refine ⟨hV'V ?_, hL t ht0 ht1⟩
    have ht' : (t : ℝ) ≤ 1 / 2 := ht.trans (by simp only [loopLo]; linarith)
    rw [loop_apply_le γ₁ γ₂ ht']
    exact htb _ (by simp only [loopLo] at ht; show (b : ℝ) ≤ 1 - 2 * t; linarith)
  · rw [he]
    refine ⟨hV'V ?_, hL t ht0 ht1⟩
    have ht' : (1 / 2 : ℝ) ≤ t := le_trans (by simp only [loopHi]; linarith) ht
    rw [loop_apply_ge γ₁ γ₂ ht']
    exact hta _ (by simp only [loopHi] at ht; show (a : ℝ) ≤ 2 * t - 1; linarith)
  · rw [← hr]
    exact ⟨hV'V (hω r).1, (hω r).2⟩

/-- Almost homotopy is the germ relation (for paths of `Ω(x,y,U)`, `x ∈ U`). -/
theorem almostHomotopic_iff_germEquiv {γ₁ γ₂ : Path x y} (hx : x ∈ U) (h₁ : MemOmega U γ₁)
    (h₂ : MemOmega U γ₂) : AlmostHomotopic U γ₁ γ₂ ↔ GermEquiv U γ₁ γ₂ :=
  ⟨AlmostHomotopic.germEquiv, almostHomotopic_of_germEquiv hx h₁ h₂⟩

theorem almostHomotopic_refl {γ : Path x y} (hx : x ∈ U) (hγ : MemOmega U γ) :
    AlmostHomotopic U γ γ :=
  almostHomotopic_of_germEquiv hx hγ hγ (germEquiv_refl hγ hx)

theorem AlmostHomotopic.symm {γ₁ γ₂ : Path x y} (h : AlmostHomotopic U γ₁ γ₂) :
    AlmostHomotopic U γ₂ γ₁ := by
  obtain ⟨hx, h₁, h₂⟩ := h.mem
  exact almostHomotopic_of_germEquiv hx h₂ h₁ (h.germEquiv.symm h₁ h₂ hx)

theorem AlmostHomotopic.trans {γ₁ γ₂ γ₃ : Path x y} (h : AlmostHomotopic U γ₁ γ₂)
    (h' : AlmostHomotopic U γ₂ γ₃) : AlmostHomotopic U γ₁ γ₃ := by
  obtain ⟨hx, h₁, -⟩ := h.mem
  obtain ⟨-, -, h₃⟩ := h'.mem
  exact almostHomotopic_of_germEquiv hx h₁ h₃ (h.germEquiv.trans h₃ hx h'.germEquiv)

/-- `lem:hausdorff_first_countable_connected` (`RamcovGX.tex:1290`) for the homotopy form. For `x ∈ U`, almost
homotopy with respect to `U` is an equivalence relation on `Ω(x,y,U)`. -/
theorem hausdorff_first_countable_connected (hx : x ∈ U) :
    Equivalence fun γ₁ γ₂ : {γ : Path x y // MemOmega U γ} => AlmostHomotopic U γ₁.1 γ₂.1 :=
  ⟨fun γ => almostHomotopic_refl hx γ.2, fun h => h.symm, fun h h' => h.trans h'⟩

end Germ

/-! ### `def:almost_homotopic_paths` and `lem:hausdorff_first_countable_connected` in the
literal reading (DEC-55) -/

section AlmostHomCC

variable {U : Set X} {x y : X}

/-- **`def:almost_homotopic_paths`** (`RamcovGX.tex:1262`), with `def:almost_trivial_loop` read
literally (DEC-55): `γ₁, γ₂ ∈ Ω(x,y,U)` are *almost homotopic with respect to `U`* if the loop
`γ₂⁻¹ * γ₁` is almost trivial with respect to `U` (`GX.AlmostTrivialCC`). Being a loop of
`Ω(y,y,U)` forces `x ∈ U` and `γ₁, γ₂ ∈ Ω(x,y,U)` (`GX.AlmostHomotopicCC.mem`). -/
def AlmostHomotopicCC (U : Set X) {x y : X} (γ₁ γ₂ : Path x y) : Prop :=
  AlmostTrivialCC U (γ₂.symm.trans γ₁)

/-- **`rem:implicitely_two_almost_homotopic`** (`RamcovGX.tex:1268`): two almost homotopic paths
have the same ends (here by typing: both are paths `x ⇝ y`). -/
theorem AlmostHomotopicCC.ends {γ₁ γ₂ : Path x y} (_ : AlmostHomotopicCC U γ₁ γ₂) :
    γ₁ 0 = γ₂ 0 ∧ γ₁ 1 = γ₂ 1 := by
  simp

theorem AlmostHomotopicCC.mem {γ₁ γ₂ : Path x y} (h : AlmostHomotopicCC U γ₁ γ₂) :
    x ∈ U ∧ MemOmega U γ₁ ∧ MemOmega U γ₂ :=
  MemOmega.of_loop h.1.2.2

theorem AlmostHomotopic.almostHomotopicCC {γ₁ γ₂ : Path x y} (h : AlmostHomotopic U γ₁ γ₂) :
    AlmostHomotopicCC U γ₁ γ₂ :=
  AlmostTrivial.almostTrivialCC h

theorem AlmostHomotopicCC.almostHomotopic [LocPathConnectedSpace X] (hU : IsOpen U)
    (hsc : SemilocallySimplyConnected U) {γ₁ γ₂ : Path x y} (h : AlmostHomotopicCC U γ₁ γ₂) :
    AlmostHomotopic U γ₁ γ₂ :=
  AlmostTrivialCC.almostTrivial hU hsc h

theorem almostHomotopicCC_iff [LocPathConnectedSpace X] (hU : IsOpen U)
    (hsc : SemilocallySimplyConnected U) {γ₁ γ₂ : Path x y} :
    AlmostHomotopicCC U γ₁ γ₂ ↔ AlmostHomotopic U γ₁ γ₂ :=
  ⟨AlmostHomotopicCC.almostHomotopic hU hsc, AlmostHomotopic.almostHomotopicCC⟩

/-- Reversing loops preserves the literal almost triviality (no hypothesis): `f ↦ f ∘ σ` is a
continuous self-map of every compact-open `Ω(x,x,W)`. -/
theorem AlmostTrivialCC.symm {γ : Path x x} (h : AlmostTrivialCC U γ) :
    AlmostTrivialCC U γ.symm := by
  set R : C(I, X) → C(I, X) := fun f => f.comp ⟨σ, continuous_symm⟩
  have hR : Continuous R := ContinuousMap.continuous_precomp _
  have hRS : ∀ {W : Set X} {f : C(I, X)}, f ∈ OmegaSet W x x → R f ∈ OmegaSet W x x := by
    rintro W f ⟨h0, h1, hf⟩
    refine ⟨by simp [R, h1], by simp [R, h0], fun t ht0 ht1 => hf _ ?_ ?_⟩
    · show (0 : ℝ) < ((σ t : I) : ℝ); rw [coe_symm_eq]; linarith
    · show ((σ t : I) : ℝ) < 1; rw [coe_symm_eq]; linarith
  have hRγ : R γ.toContinuousMap = γ.symm.toContinuousMap := ContinuousMap.ext fun t => rfl
  refine ⟨hRγ ▸ hRS h.1, fun V hV => ?_⟩
  obtain ⟨η, hηC, hηV⟩ := h.2 V hV
  refine ⟨R η, ?_, hRS hηV⟩
  rw [← hRγ]
  exact (isPreconnected_connectedComponentIn.image R hR.continuousOn).subset_connectedComponentIn
    (mem_image_of_mem R (mem_connectedComponentIn h.1))
    (image_subset_iff.2 fun f hf =>
      show f ∈ R ⁻¹' OmegaSet U x x from hRS (connectedComponentIn_subset _ _ hf)) (mem_image_of_mem R hηC)

theorem almostHomotopicCC_refl {γ : Path x y} (hx : x ∈ U) (hγ : MemOmega U γ) :
    AlmostHomotopicCC U γ γ :=
  (almostHomotopic_refl hx hγ).almostHomotopicCC

/-- Symmetry of the literal almost homotopy, with no hypothesis. -/
theorem AlmostHomotopicCC.symm {γ₁ γ₂ : Path x y} (h : AlmostHomotopicCC U γ₁ γ₂) :
    AlmostHomotopicCC U γ₂ γ₁ := by
  have := AlmostTrivialCC.symm h
  rwa [Path.trans_symm, Path.symm_symm] at this

theorem AlmostHomotopicCC.trans [LocPathConnectedSpace X] (hU : IsOpen U)
    (hsc : SemilocallySimplyConnected U) {γ₁ γ₂ γ₃ : Path x y} (h : AlmostHomotopicCC U γ₁ γ₂)
    (h' : AlmostHomotopicCC U γ₂ γ₃) : AlmostHomotopicCC U γ₁ γ₃ :=
  ((h.almostHomotopic hU hsc).trans (h'.almostHomotopic hU hsc)).almostHomotopicCC

/-- **`lem:hausdorff_first_countable_connected`** (`RamcovGX.tex:1290`) in the literal reading
(DEC-55): for `X` locally path-connected, `U` open and semilocally simply connected (DEC-68 (b))
and `x ∈ U`, almost
homotopy with respect to `U` is an equivalence relation on `Ω(x,y,U)`. Reflexivity
(`GX.almostHomotopicCC_refl`) and symmetry (`GX.AlmostHomotopicCC.symm`) hold with no hypothesis
on `U`. -/
theorem hausdorff_first_countable_connected_cc [LocPathConnectedSpace X] (hU : IsOpen U)
    (hsc : SemilocallySimplyConnected U) (hx : x ∈ U) :
    Equivalence fun γ₁ γ₂ : {γ : Path x y // MemOmega U γ} => AlmostHomotopicCC U γ₁.1 γ₂.1 :=
  ⟨fun γ => almostHomotopicCC_refl hx γ.2, fun h => h.symm, fun h h' => h.trans hU hsc h'⟩

end AlmostHomCC

/-! ### Lifting paths through a map which is a covering over `s` -/

section Lift

variable {E Y : Type*} [TopologicalSpace E] [TopologicalSpace Y] {p : E → Y} {s : Set Y}

/-- Lifts of a path lying in `s` before time `1` are unique (`E` Hausdorff, `p` a covering
over `s`). -/
theorem lift_unique [T2Space E] (cov : IsCoveringMap (s.restrictPreimage p)) {γ : I → Y}
    (hγ : ∀ t : I, (t : ℝ) < 1 → γ t ∈ s) {Γ₁ Γ₂ : C(I, E)} (h₁ : ∀ t, p (Γ₁ t) = γ t)
    (h₂ : ∀ t, p (Γ₂ t) = γ t) (h0 : Γ₁ 0 = Γ₂ 0) : Γ₁ = Γ₂ := by
  have key : ∀ a : I, (a : ℝ) < 1 → Γ₁ a = Γ₂ a := by
    intro a ha
    have hm : ∀ (Γ : C(I, E)), (∀ t, p (Γ t) = γ t) → ∀ t : I, Γ (t * a) ∈ p ⁻¹' s :=
      fun Γ hΓ t => by
        show p (Γ (t * a)) ∈ s
        rw [hΓ]
        exact hγ _ (by
          rw [Set.Icc.coe_mul]
          exact lt_of_le_of_lt (mul_le_of_le_one_left a.2.1 t.2.2) ha)
    let f : (Γ : C(I, E)) → (∀ t, p (Γ t) = γ t) → I → p ⁻¹' s :=
      fun Γ hΓ t => ⟨Γ (t * a), hm Γ hΓ t⟩
    have hf : ∀ Γ hΓ, Continuous (f Γ hΓ) := fun Γ hΓ =>
      (Γ.continuous.comp (continuous_id.mul continuous_const)).subtype_mk _
    have := cov.eq_of_comp_eq (hf Γ₁ h₁) (hf Γ₂ h₂) (funext fun t => Subtype.ext (by
      show p (Γ₁ (t * a)) = p (Γ₂ (t * a))
      rw [h₁, h₂])) 0 (Subtype.ext (by
        show Γ₁ (0 * a) = Γ₂ (0 * a)
        rw [zero_mul]; exact h0))
    have h1 := congrArg Subtype.val (congrFun this 1)
    simpa [f] using h1
  ext t
  exact (Continuous.ext_on dense_setOf_lt_one Γ₁.continuous Γ₂.continuous
    (fun t (ht : t < 1) => key t ht)).symm ▸ rfl

/-- Lifts exist through a complete spread which is a covering over `s`. -/
theorem exists_lift [T1Space Y] [LocallyConnectedSpace Y] (hp : IsSpread p)
    (hc : IsCompleteSpread p) (cov : IsCoveringMap (s.restrictPreimage p)) (γ : C(I, Y))
    (hγ : ∀ t : I, (t : ℝ) < 1 → γ t ∈ s) {e : E} (he : p e = γ 0) :
    ∃ Γ : C(I, E), (∀ t, p (Γ t) = γ t) ∧ Γ 0 = e := by
  obtain ⟨f, hf, hf0, hfs⟩ := exists_partial_lift cov γ (fun t ht => hγ t ht)
    (he ▸ hγ 0 (by simp)) he
  obtain ⟨g, hg, hgf⟩ := exists_extend_path_of_isCompleteSpread hp hc γ f hf
    (fun t ht => (hfs t ht).2)
  exact ⟨g, hg, by rw [hgf 0 (by exact zero_lt_one), hf0]⟩

/-- Lifts of paths homotopic in `s` end at the same point. -/
theorem lift_end_eq_of_homotopicIn (cov : IsCoveringMap (s.restrictPreimage p)) {a b : Y}
    {δ δ' : Path a b} (h : HomotopicIn s δ δ') {Δ Δ' : C(I, E)} (hΔ : ∀ t, p (Δ t) = δ t)
    (hΔ' : ∀ t, p (Δ' t) = δ' t) (h0 : Δ 0 = Δ' 0) : Δ 1 = Δ' 1 := by
  obtain ⟨h₁, h₂, hom⟩ := homotopicIn_iff.1 h
  have hm : ∀ t, Δ t ∈ p ⁻¹' s := fun t => by show p (Δ t) ∈ s; rw [hΔ]; exact h₁ t
  have hm' : ∀ t, Δ' t ∈ p ⁻¹' s := fun t => by show p (Δ' t) ∈ s; rw [hΔ']; exact h₂ t
  set e : p ⁻¹' s := ⟨Δ 0, hm 0⟩
  let D : C(I, p ⁻¹' s) := ⟨fun t => ⟨Δ t, hm t⟩, Δ.continuous.subtype_mk _⟩
  let D' : C(I, p ⁻¹' s) := ⟨fun t => ⟨Δ' t, hm' t⟩, Δ'.continuous.subtype_mk _⟩
  have he0 : (pathToSub δ h₁).toContinuousMap 0 = s.restrictPreimage p e :=
    Subtype.ext (by simp [e, hΔ])
  have he0' : (pathToSub δ' h₂).toContinuousMap 0 = s.restrictPreimage p e :=
    Subtype.ext (by simp [e, h0, hΔ'])
  have hD : D = cov.liftPath (pathToSub δ h₁).toContinuousMap e he0 :=
    (cov.eq_liftPath_iff' he0).2 ⟨funext fun t => Subtype.ext (hΔ t), rfl⟩
  have hD' : D' = cov.liftPath (pathToSub δ' h₂).toContinuousMap e he0' :=
    (cov.eq_liftPath_iff' he0').2 ⟨funext fun t => Subtype.ext (hΔ' t), Subtype.ext h0.symm⟩
  have := cov.liftPath_apply_one_eq_of_homotopicRel hom e he0 he0'
  rw [← hD, ← hD'] at this
  exact congrArg Subtype.val this

end Lift

section Lift2

variable {E Y : Type*} [TopologicalSpace E] [TopologicalSpace Y] {p : E → Y} {s : Set Y}

/-- A path all of whose values lie in `s` lifts through a covering over `s`. -/
theorem exists_lift_of_mem (cov : IsCoveringMap (s.restrictPreimage p)) {a b : Y}
    (δ : Path a b) (h : ∀ t, δ t ∈ s) {e : E} (he : p e = a) :
    ∃ Δ : C(I, E), (∀ t, p (Δ t) = δ t) ∧ Δ 0 = e := by
  have he' : p e ∈ s := by rw [he]; exact δ.source ▸ h 0
  have h0 : (pathToSub δ h).toContinuousMap 0 = s.restrictPreimage p ⟨e, he'⟩ :=
    Subtype.ext (by simp [he])
  set L := cov.liftPath (pathToSub δ h).toContinuousMap ⟨e, he'⟩ h0
  refine ⟨⟨fun t => (L t : E), continuous_subtype_val.comp L.continuous⟩, fun t => ?_, ?_⟩
  · have := congrFun (cov.liftPath_lifts (pathToSub δ h).toContinuousMap ⟨e, he'⟩ h0) t
    exact congrArg Subtype.val this
  · show (L 0 : E) = e
    rw [cov.liftPath_zero]

/-- The lift of a head is the restriction of the lift. -/
theorem lift_head {x y : Y} {γ : Path x y} {Γ : C(I, E)} (hΓ : ∀ t, p (Γ t) = γ t) (s₀ : I) :
    ∃ Δ : C(I, E), (∀ t, p (Δ t) = head γ s₀ t) ∧ Δ 0 = Γ 0 ∧ Δ 1 = Γ s₀ := by
  refine ⟨⟨fun t => Γ (t * s₀), Γ.continuous.comp (continuous_id.mul continuous_const)⟩,
    fun t => ?_, by simp, by simp⟩
  show p (Γ (t * s₀)) = head γ s₀ t
  rw [hΓ, head_apply, subpath_apply']
  have hm : (1 - (t : ℝ)) * ((0 : I) : ℝ) + t * s₀ ∈ I := by
    simp only [Icc.coe_zero, mul_zero, zero_add]
    exact (t * s₀).2
  rw [Path.extend_apply γ hm]
  congr 1
  exact Subtype.ext (by simp)

/-- The lift of a concatenation is the concatenation of the lifts. -/
theorem lift_trans {a b c : Y} {A : Path a b} {B : Path b c} {ΔA ΔB : C(I, E)}
    (hA : ∀ t, p (ΔA t) = A t) (hB : ∀ t, p (ΔB t) = B t) (h : ΔB 0 = ΔA 1) :
    ∃ Δ : C(I, E), (∀ t, p (Δ t) = (A.trans B) t) ∧ Δ 0 = ΔA 0 ∧ Δ 1 = ΔB 1 := by
  set PA : Path (ΔA 0) (ΔA 1) := ⟨ΔA, rfl, rfl⟩
  set PB : Path (ΔA 1) (ΔB 1) := ⟨ΔB, h, rfl⟩
  refine ⟨(PA.trans PB).toContinuousMap, fun t => ?_, (PA.trans PB).source,
    (PA.trans PB).target⟩
  show p ((PA.trans PB) t) = (A.trans B) t
  rw [Path.trans_apply, Path.trans_apply]
  split_ifs
  · exact hA _
  · exact hB _

theorem HomotopicIn.map {Z : Type*} [TopologicalSpace Z] {U : Set Z} {V : Set Y} {f : Z → Y}
    (hf : Continuous f) (hfU : MapsTo f U V) {a b : Z} {P Q : Path a b}
    (h : HomotopicIn U P Q) : HomotopicIn V (P.map hf) (Q.map hf) := by
  obtain ⟨F, hF⟩ := h
  exact ⟨F.map ⟨f, hf⟩, fun w => hfU (hF w)⟩

end Lift2

/-! ### `lem:almost_homotopic_carac2` -/

section Carac2

variable {E Y : Type*} [TopologicalSpace E] [TopologicalSpace Y]

/-- `lem:almost_homotopic_carac2`, "if" half, for **any** spread `p` which is a covering over
`Y ∖ S` (no maximality, no simple connectivity): lifts of almost homotopic paths from the same
point end at the same point. -/
theorem lift_end_eq_of_almostHomotopic [T1Space E] [LocallyConnectedSpace Y] {p : E → Y}
    (hp : IsSpread p) {S : Set Y} (cov : IsCoveringMap (Sᶜ.restrictPreimage p)) {x y : Y}
    {γ₁ γ₂ : Path x y} (h : AlmostHomotopic Sᶜ γ₁ γ₂) {Γ₁ Γ₂ : C(I, E)}
    (hΓ₁ : ∀ t, p (Γ₁ t) = γ₁ t) (hΓ₂ : ∀ t, p (Γ₂ t) = γ₂ t) (h0 : Γ₁ 0 = Γ₂ 0) :
    Γ₁ 1 = Γ₂ 1 := by
  haveI := hp.locallyConnectedSpace
  have hg := h.germEquiv
  suffices key : ∀ N : Set E, IsOpen N → Γ₂ 1 ∈ N → Γ₁ 1 ∈ N by
    by_contra hne
    exact key {Γ₁ 1}ᶜ isOpen_compl_singleton (Ne.symm hne) rfl
  intro N hN hmem
  obtain ⟨V, hV, hyV, hVN⟩ := (isSpread_iff.1 hp).2.2 (Γ₂ 1) N hN hmem
  have hy : p (Γ₂ 1) = y := by rw [hΓ₂, γ₂.target]
  rw [hy] at hyV
  set V' := connectedComponentIn V y
  have hV' : IsOpen V' := hV.connectedComponentIn
  have hyV' : y ∈ V' := mem_connectedComponentIn hyV
  set W := connectedComponentIn (p ⁻¹' V') (Γ₂ 1) with hWdef
  have hW : IsOpen W := (hV'.preimage hp.continuous).connectedComponentIn
  have hmemW : Γ₂ 1 ∈ W := mem_connectedComponentIn (show p (Γ₂ 1) ∈ V' by rw [hy]; exact hyV')
  have hWN : W ⊆ N := (connectedComponentIn_mono _ (preimage_mono
    (connectedComponentIn_subset V y))).trans hVN
  have hWV' : ∀ e ∈ W, p e ∈ V' := fun e he =>
    (connectedComponentIn_subset (p ⁻¹' V') _ he : e ∈ p ⁻¹' V')
  obtain ⟨s₂, -, hs₂, ht₂W⟩ := exists_tail_mem (⟨Γ₂, rfl, rfl⟩ : Path (Γ₂ 0) (Γ₂ 1))
    (hW.mem_nhds hmemW) (c := 1) one_pos
  obtain ⟨s₁, -, hs₁, ht₁⟩ := exists_tail_mem γ₁ (hV'.mem_nhds hyV') (c := 1) one_pos
  have ht₂ : ∀ t : I, (s₂ : ℝ) ≤ t → γ₂ t ∈ V' := fun t ht => by
    rw [← hΓ₂]; exact hWV' _ (ht₂W t ht)
  obtain ⟨ω, hω, hh⟩ := hg V' hV' hyV' s₁ s₂ hs₁ hs₂ ht₁ ht₂
  obtain ⟨Δ₁, hΔ₁, hΔ₁0, hΔ₁1⟩ := lift_head hΓ₁ s₁
  obtain ⟨Δ₂, hΔ₂, hΔ₂0, hΔ₂1⟩ := lift_head hΓ₂ s₂
  obtain ⟨Ωl, hΩl, hΩl0⟩ := exists_lift_of_mem cov ω (fun t => (hω t).2) (hΓ₂ s₂)
  obtain ⟨Δ, hΔ, hΔ0, hΔ1⟩ := lift_trans hΔ₂ hΩl (hΩl0.trans hΔ₂1.symm)
  have heq := lift_end_eq_of_homotopicIn cov hh hΔ₁ hΔ (by rw [hΔ₁0, hΔ0, hΔ₂0, h0])
  rw [hΔ₁1, hΔ1] at heq
  have hΩW : range Ωl ⊆ W := by
    have h1 : Ωl 0 ∈ W := by rw [hΩl0]; exact ht₂W s₂ le_rfl
    rw [hWdef, connectedComponentIn_eq h1]
    exact (isPreconnected_range Ωl.continuous).subset_connectedComponentIn (mem_range_self 0)
      (by rintro _ ⟨t, rfl⟩; show p (Ωl t) ∈ V'; rw [hΩl]; exact (hω t).1)
  have hs₁W : Γ₁ s₁ ∈ W := heq ▸ hΩW (mem_range_self 1)
  have hseg : Γ₁ '' Icc s₁ 1 ⊆ W := by
    rw [hWdef, connectedComponentIn_eq hs₁W]
    exact (isPreconnected_Icc.image _ Γ₁.continuous.continuousOn).subset_connectedComponentIn
      ⟨s₁, ⟨le_rfl, s₁.2.2⟩, rfl⟩ (by
        rintro _ ⟨t, ht, rfl⟩
        show p (Γ₁ t) ∈ V'
        rw [hΓ₁]; exact ht₁ t ht.1)
  exact hWN (hseg ⟨1, ⟨s₁.2.2, le_rfl⟩, rfl⟩)

/-- `lem:almost_homotopic_carac2`, "only if" half, for a branched covering possibly branched
over a skeletal `S` whose part over `Y ∖ S` is simply connected: lifts ending at the same point
come from almost homotopic paths. -/
theorem almostHomotopic_of_lift_end_eq [LocPathConnectedSpace E] {p : E → Y}
    (hp : IsBranchedCovering p) {S : Set Y} (hS : IsSkeletal S)
    [SimplyConnectedSpace (p ⁻¹' Sᶜ)] {x y : Y} (hx : x ∈ Sᶜ) {γ₁ γ₂ : Path x y}
    (h₁ : MemOmega Sᶜ γ₁) (h₂ : MemOmega Sᶜ γ₂) {Γ₁ Γ₂ : C(I, E)} (hΓ₁ : ∀ t, p (Γ₁ t) = γ₁ t)
    (hΓ₂ : ∀ t, p (Γ₂ t) = γ₂ t) (h0 : Γ₁ 0 = Γ₂ 0) (h1 : Γ₁ 1 = Γ₂ 1) :
    AlmostHomotopic Sᶜ γ₁ γ₂ := by
  refine almostHomotopic_of_germEquiv hx h₁ h₂ ?_
  intro V hV hyV s₁ s₂ hs₁ hs₂ ht₁ ht₂
  have hE : IsPortly (p ⁻¹' Sᶜ) := hp.isPortly_preimage hS
  set e := Γ₂ 1
  have hpe : p e = y := by rw [hΓ₂, γ₂.target]
  set W := connectedComponentIn (p ⁻¹' V) e with hWdef
  have hpV : IsOpen (p ⁻¹' V) := hV.preimage hp.isSpread.continuous
  have hW : IsOpen W := hpV.connectedComponentIn
  have heW : e ∈ W := mem_connectedComponentIn (show p e ∈ V by rw [hpe]; exact hyV)
  have hWV : ∀ z ∈ W, p z ∈ V := fun z hz =>
    (connectedComponentIn_subset (p ⁻¹' V) _ hz : z ∈ p ⁻¹' V)
  have tailW : ∀ (Γ : C(I, E)) (γ : Path x y), (∀ t, p (Γ t) = γ t) → Γ 1 = e → ∀ s₀ : I,
      (∀ t : I, (s₀ : ℝ) ≤ t → γ t ∈ V) → Γ s₀ ∈ W := by
    intro Γ γ hΓ he s₀ ht
    have hseg : Γ '' Icc s₀ 1 ⊆ W := by
      rw [hWdef, ← he]
      exact (isPreconnected_Icc.image _ Γ.continuous.continuousOn).subset_connectedComponentIn
        ⟨1, ⟨s₀.2.2, le_rfl⟩, rfl⟩ (by
          rintro _ ⟨t, ht', rfl⟩
          show p (Γ t) ∈ V
          rw [hΓ]; exact ht t ht'.1)
    exact hseg ⟨s₀, ⟨le_rfl, s₀.2.2⟩, rfl⟩
  have hW₁ := tailW Γ₁ γ₁ hΓ₁ h1 s₁ ht₁
  have hW₂ := tailW Γ₂ γ₂ hΓ₂ rfl s₂ ht₂
  have hE₁ : Γ₁ s₁ ∈ p ⁻¹' Sᶜ := by
    show p (Γ₁ s₁) ∈ Sᶜ
    rw [hΓ₁, ← Path.extend_extends' γ₁ s₁]; exact h₁.extend_mem hx hs₁
  have hE₂ : Γ₂ s₂ ∈ p ⁻¹' Sᶜ := by
    show p (Γ₂ s₂) ∈ Sᶜ
    rw [hΓ₂, ← Path.extend_extends' γ₂ s₂]; exact h₂.extend_mem hx hs₂
  have hWc : IsConnected W := ⟨⟨e, heW⟩, isPreconnected_connectedComponentIn⟩
  have hpc : IsPathConnected (W ∩ p ⁻¹' Sᶜ) :=
    (hW.inter hE.isOpen).isConnected_iff_isPathConnected.1 (hE.isConnected_inter hW hWc)
  have hj := hpc.joinedIn _ ⟨hW₂, hE₂⟩ _ ⟨hW₁, hE₁⟩
  set ωl := hj.somePath
  have hωl : ∀ t, ωl t ∈ W ∩ p ⁻¹' Sᶜ := hj.somePath_mem
  set ω : Path (γ₂ s₂) (γ₁ s₁) := (ωl.map hp.isSpread.continuous).cast (hΓ₂ s₂).symm
    (hΓ₁ s₁).symm
  have hωV : ∀ τ, ω τ ∈ V ∩ Sᶜ := fun τ => ⟨hWV _ (hωl τ).1, (hωl τ).2⟩
  refine ⟨ω, hωV, ?_⟩
  -- lifts of both sides inside `p ⁻¹' Sᶜ`
  obtain ⟨Δ₁, hΔ₁, hΔ₁0, hΔ₁1⟩ := lift_head hΓ₁ s₁
  obtain ⟨Δ₂, hΔ₂, hΔ₂0, hΔ₂1⟩ := lift_head hΓ₂ s₂
  set P₁ : Path (Γ₁ 0) (Γ₁ s₁) := ⟨Δ₁, hΔ₁0, hΔ₁1⟩
  set P₂ : Path (Γ₁ 0) (Γ₂ s₂) := ⟨Δ₂, hΔ₂0.trans h0.symm, hΔ₂1⟩
  have hP₁ : ∀ t, P₁ t ∈ p ⁻¹' Sᶜ := fun t => by
    show p (Δ₁ t) ∈ Sᶜ; rw [hΔ₁]; exact head_mem h₁ hx hs₁ t
  have hP₂ : ∀ t, (P₂.trans ωl) t ∈ p ⁻¹' Sᶜ := path_trans_mem (fun t => by
    show p (Δ₂ t) ∈ Sᶜ; rw [hΔ₂]; exact head_mem h₂ hx hs₂ t) (fun t => (hωl t).2)
  have hhom : HomotopicIn (p ⁻¹' Sᶜ) P₁ (P₂.trans ωl) :=
    homotopicIn_iff.2 ⟨hP₁, hP₂, SimplyConnectedSpace.paths_homotopic _ _⟩
  have hmap := (hhom.map hp.isSpread.continuous (fun z hz => hz)).cast
    (show x = p (Γ₁ 0) by rw [hΓ₁, γ₁.source]) (hΓ₁ s₁).symm
  refine hmap.of_eq ?_ ?_
  · ext t
    simp only [Path.cast_coe, Path.map_coe, comp_apply]
    exact hΔ₁ t
  · ext t
    simp only [Path.cast_coe, Path.map_coe, comp_apply, Path.trans_apply]
    split_ifs
    · exact hΔ₂ _
    · rfl

end Carac2

section MaxCover

universe u

variable {Y : Type u} [TopologicalSpace Y] [T2Space Y] [LocPathConnectedSpace Y]
  [FirstCountableTopology Y] [ConnectedSpace Y] {S : Set Y}

/-- The lifting facts of `\widetilde Y^S` used in §3.3: a covering over `Y ∖ S`, with a simply
connected part over `Y ∖ S` (it is `\widetilde{Y ∖ S}`). -/
theorem maxBranched_lifting (hS : IsSkeletal S) (hSc : SemilocallySimplyConnected (Sᶜ : Set Y))
    (y₀ : (Sᶜ : Set Y)) :
    IsCoveringMap (Sᶜ.restrictPreimage (SpreadEnd.base : MaxBranchedCover S y₀ → Y)) ∧
      SimplyConnectedSpace ((SpreadEnd.base : MaxBranchedCover S y₀ → Y) ⁻¹' Sᶜ) := by
  have hO : IsPortly (Sᶜ : Set Y) := isSkeletal_iff.1 hS
  haveI : LocPathConnectedSpace (Sᶜ : Set Y) := hO.isOpen.locPathConnectedSpace
  obtain ⟨-, hbc, hpb, hpre, -, hsp⟩ := maxBranched_basic hS hSc y₀
  have hOp : (Sᶜ : Set Y) ⊆ ordY (SpreadEnd.base : MaxBranchedCover S y₀ → Y) := fun y hy => by
    by_contra h
    exact hy (hpb h)
  refine ⟨(hbc.restrict_isCoveringMap hO hOp).1, ?_⟩
  haveI : T2Space (UniversalCover (Sᶜ : Set Y) y₀) :=
    t2Space_of_isCoveringMap (UniversalCover.isCoveringMap_proj (y₀ := y₀) hSc)
  haveI := UniversalCover.simplyConnectedSpace (y₀ := y₀) hSc
  have hemb₁ := SpreadEnd.isEmbedding_ofPoint hsp
  set ψ : UniversalCover (Sᶜ : Set Y) y₀ ≃ₜ
      ((SpreadEnd.base : MaxBranchedCover S y₀ → Y) ⁻¹' Sᶜ) :=
    hemb₁.toHomeomorph.trans (Homeomorph.setCongr hpre.symm)
  exact ψ.symm.toHomotopyEquiv.simplyConnectedSpace

/-- Paths of `Ω(x,y,Y ∖ S)`, `x ∈ Y ∖ S`, lift uniquely to `\widetilde Y^S` from any point over
`x` ("the respective lifts" of `lem:almost_homotopic_carac2`). -/
theorem maxBranched_existsUnique_lift (hS : IsSkeletal S)
    (hSc : SemilocallySimplyConnected (Sᶜ : Set Y)) (y₀ : (Sᶜ : Set Y)) {x y : Y} (hx : x ∈ Sᶜ)
    {γ : Path x y} (hγ : MemOmega Sᶜ γ) {e : MaxBranchedCover S y₀} (he : e.base = x) :
    ∃! Γ : C(I, MaxBranchedCover S y₀), (∀ t, (Γ t).base = γ t) ∧ Γ 0 = e := by
  obtain ⟨-, hbc, -, -, -, -⟩ := maxBranched_basic hS hSc y₀
  obtain ⟨cov, -⟩ := maxBranched_lifting hS hSc y₀
  have hγs : ∀ t : I, (t : ℝ) < 1 → γ t ∈ Sᶜ := fun t ht => by
    rw [← Path.extend_extends' γ t]; exact hγ.extend_mem hx ht
  obtain ⟨Γ, hΓ, hΓ0⟩ := exists_lift hbc.isSpread hbc.isComplete cov γ.toContinuousMap hγs
    (by rw [he]; exact γ.source.symm)
  exact ⟨Γ, ⟨hΓ, hΓ0⟩, fun Γ' ⟨hΓ', hΓ'0⟩ =>
    lift_unique cov hγs hΓ' hΓ (hΓ'0.trans hΓ0.symm)⟩

/-- `lem:almost_homotopic_carac2` (`RamcovGX.tex:1306`) for the homotopy form. Let `\widetilde Y^S → Y` be the
maximal covering possibly branched over `S` (`Y ∖ S` semilocally simply connected), `x ∈ Y ∖ S`,
`γ₁, γ₂ ∈ Ω(x,y,Y ∖ S)` and `Γ₁, Γ₂` their lifts from the same point. Then
`Γ₁(1) = Γ₂(1)` iff `γ₁` and `γ₂` are almost homotopic. -/
theorem almost_homotopic_carac2 (hS : IsSkeletal S)
    (hSc : SemilocallySimplyConnected (Sᶜ : Set Y)) (y₀ : (Sᶜ : Set Y)) {x y : Y} (hx : x ∈ Sᶜ)
    {γ₁ γ₂ : Path x y} (h₁ : MemOmega Sᶜ γ₁) (h₂ : MemOmega Sᶜ γ₂)
    {Γ₁ Γ₂ : C(I, MaxBranchedCover S y₀)} (hΓ₁ : ∀ t, (Γ₁ t).base = γ₁ t)
    (hΓ₂ : ∀ t, (Γ₂ t).base = γ₂ t) (h0 : Γ₁ 0 = Γ₂ 0) :
    Γ₁ 1 = Γ₂ 1 ↔ AlmostHomotopic Sᶜ γ₁ γ₂ := by
  obtain ⟨-, hbc, -, -, hl, -⟩ := maxBranched_basic hS hSc y₀
  haveI := hl
  obtain ⟨cov, hsc⟩ := maxBranched_lifting hS hSc y₀
  haveI := hsc
  exact ⟨fun h1 => almostHomotopic_of_lift_end_eq hbc hS hx h₁ h₂ hΓ₁ hΓ₂ h0 h1,
    fun h => lift_end_eq_of_almostHomotopic hbc.isSpread cov h hΓ₁ hΓ₂ h0⟩

/-- `lem:almost_homotopic_carac2` for **any** maximal covering `p : X → Y` possibly branched
over `S` (transported along `GX.IsMaximalPossiblyBranched.nonempty_homeomorph`). -/
theorem almost_homotopic_carac2_of_isMaximal (hS : IsSkeletal S)
    (hSc : SemilocallySimplyConnected (Sᶜ : Set Y)) (y₀ : (Sᶜ : Set Y)) {X : Type*}
    [TopologicalSpace X] [T2Space X] [LocPathConnectedSpace X] [FirstCountableTopology X]
    {p : X → Y} (hp : IsMaximalPossiblyBranched.{u} p S) {x y : Y} (hx : x ∈ Sᶜ)
    {γ₁ γ₂ : Path x y} (h₁ : MemOmega Sᶜ γ₁) (h₂ : MemOmega Sᶜ γ₂) {Γ₁ Γ₂ : C(I, X)}
    (hΓ₁ : ∀ t, p (Γ₁ t) = γ₁ t) (hΓ₂ : ∀ t, p (Γ₂ t) = γ₂ t) (h0 : Γ₁ 0 = Γ₂ 0) :
    Γ₁ 1 = Γ₂ 1 ↔ AlmostHomotopic Sᶜ γ₁ γ₂ := by
  obtain ⟨Φ, hΦ⟩ := hp.nonempty_homeomorph hS hSc y₀
  have hb : ∀ (Γ : C(I, X)) (γ : Path x y), (∀ t, p (Γ t) = γ t) →
      ∀ t, ((ContinuousMap.comp ⟨Φ.symm, Φ.symm.continuous⟩ Γ) t).base = γ t := fun Γ γ hΓ t => by
    show (Φ.symm (Γ t)).base = γ t
    rw [← hΦ, Φ.apply_symm_apply, hΓ]
  rw [← almost_homotopic_carac2 hS hSc y₀ hx h₁ h₂ (hb Γ₁ γ₁ hΓ₁) (hb Γ₂ γ₂ hΓ₂)
    (by show Φ.symm (Γ₁ 0) = Φ.symm (Γ₂ 0); rw [h0])]
  exact ⟨fun h => by show Φ.symm (Γ₁ 1) = Φ.symm (Γ₂ 1); rw [h],
    fun h => Φ.symm.injective h⟩

/-- **`lem:almost_homotopic_carac2`** (`RamcovGX.tex:1306`) in the literal reading (DEC-55), with
`\widetilde Y^S` read as the covering of `prop:universality` (DEC-79 (a), module SCOPE (i)).
Let `\widetilde Y^S → Y` be the maximal covering possibly branched over `S` of `prop:universality`
(`S` skeletal, `Y ∖ S` semilocally simply connected — the hypotheses of `prop:universality`),
`x ∈ Y ∖ S`, `γ₁, γ₂ ∈ Ω(x,y,Y ∖ S)` and `Γ₁, Γ₂` their lifts from the same point.
Then `Γ₁(1) = Γ₂(1)` iff `γ₁` and `γ₂` are almost homotopic (compact-open components). -/
theorem almost_homotopic_carac2_cc (hS : IsSkeletal S)
    (hSc : SemilocallySimplyConnected (Sᶜ : Set Y)) (y₀ : (Sᶜ : Set Y)) {x y : Y} (hx : x ∈ Sᶜ)
    {γ₁ γ₂ : Path x y} (h₁ : MemOmega Sᶜ γ₁) (h₂ : MemOmega Sᶜ γ₂)
    {Γ₁ Γ₂ : C(I, MaxBranchedCover S y₀)} (hΓ₁ : ∀ t, (Γ₁ t).base = γ₁ t)
    (hΓ₂ : ∀ t, (Γ₂ t).base = γ₂ t) (h0 : Γ₁ 0 = Γ₂ 0) :
    Γ₁ 1 = Γ₂ 1 ↔ AlmostHomotopicCC Sᶜ γ₁ γ₂ := by
  rw [almostHomotopicCC_iff (isSkeletal_iff.1 hS).isOpen hSc]
  exact almost_homotopic_carac2 hS hSc y₀ hx h₁ h₂ hΓ₁ hΓ₂ h0

/-- `lem:almost_homotopic_carac2` in the literal reading, for **any** maximal covering `p : X → Y`
possibly branched over `S`. -/
theorem almost_homotopic_carac2_of_isMaximal_cc (hS : IsSkeletal S)
    (hSc : SemilocallySimplyConnected (Sᶜ : Set Y)) (y₀ : (Sᶜ : Set Y)) {X : Type*}
    [TopologicalSpace X] [T2Space X] [LocPathConnectedSpace X] [FirstCountableTopology X]
    {p : X → Y} (hp : IsMaximalPossiblyBranched.{u} p S) {x y : Y} (hx : x ∈ Sᶜ)
    {γ₁ γ₂ : Path x y} (h₁ : MemOmega Sᶜ γ₁) (h₂ : MemOmega Sᶜ γ₂) {Γ₁ Γ₂ : C(I, X)}
    (hΓ₁ : ∀ t, p (Γ₁ t) = γ₁ t) (hΓ₂ : ∀ t, p (Γ₂ t) = γ₂ t) (h0 : Γ₁ 0 = Γ₂ 0) :
    Γ₁ 1 = Γ₂ 1 ↔ AlmostHomotopicCC Sᶜ γ₁ γ₂ := by
  rw [almostHomotopicCC_iff (isSkeletal_iff.1 hS).isOpen hSc]
  exact almost_homotopic_carac2_of_isMaximal hS hSc y₀ hp hx h₁ h₂ hΓ₁ hΓ₂ h0

end MaxCover

/-! ### Gluing a path to the end of another, and perturbing tails in the compact-open topology -/

section Glue

variable {Z : Type*} [TopologicalSpace Z]

/-- Follow `f` on `[0,t₀]`, then `g` (affinely rescaled) on `[t₀,1]`. -/
def glue (f : C(I, Z)) (t₀ : I) (_h : (t₀ : ℝ) < 1) (g : C(I, Z)) (hg : g 0 = f t₀) : C(I, Z) where
  toFun t := if (t : ℝ) ≤ t₀ then f t else g (Set.projIcc 0 1 zero_le_one ((t - t₀) / (1 - t₀)))
  continuous_toFun := by
    refine Continuous.if_le f.continuous (g.continuous.comp (continuous_projIcc.comp (by fun_prop)))
      (by fun_prop) continuous_const fun t ht => ?_
    rw [ht, projIcc_sub_self_div, hg]
    congr 1
    exact Subtype.ext ht

variable {f : C(I, Z)} {t₀ : I} {h : (t₀ : ℝ) < 1} {g : C(I, Z)} {hg : g 0 = f t₀}

theorem glue_apply_le {t : I} (ht : (t : ℝ) ≤ t₀) : glue f t₀ h g hg t = f t := by
  show (if (t : ℝ) ≤ t₀ then _ else _) = _
  rw [if_pos ht]

theorem glue_apply_gt {t : I} (ht : (t₀ : ℝ) < t) :
    glue f t₀ h g hg t = g (Set.projIcc 0 1 zero_le_one ((t - t₀) / (1 - t₀))) := by
  show (if (t : ℝ) ≤ t₀ then _ else _) = _
  rw [if_neg (not_le.2 ht)]

theorem glue_zero : glue f t₀ h g hg 0 = f 0 := glue_apply_le (by simp [t₀.2.1])

theorem glue_one : glue f t₀ h g hg 1 = g 1 := by
  rw [glue_apply_gt (by simpa using h)]
  congr 1
  rw [Icc.coe_one]
  exact projIcc_div_self h

theorem glue_mem (t : I) : ((t : ℝ) ≤ t₀ ∧ glue f t₀ h g hg t = f t) ∨
    ∃ r : I, glue f t₀ h g hg t = g r ∧ ((t : ℝ) < 1 → (r : ℝ) < 1) := by
  rcases le_or_gt (t : ℝ) t₀ with ht | ht
  · exact Or.inl ⟨ht, glue_apply_le ht⟩
  · refine Or.inr ⟨_, glue_apply_gt ht, fun ht1 => ?_⟩
    rw [projIcc_mid h ht.le t.2.2]
    have : 0 < 1 - (t₀ : ℝ) := sub_pos.2 h
    rw [div_lt_one this]; linarith

theorem glue_map {Z' : Type*} [TopologicalSpace Z'] {φ : Z → Z'} {f' g' : C(I, Z')}
    (hf : ∀ t, φ (f t) = f' t) (hg' : ∀ t, φ (g t) = g' t) (hg'' : g' 0 = f' t₀) (t : I) :
    φ (glue f t₀ h g hg t) = glue f' t₀ h g' hg'' t := by
  rcases le_or_gt (t : ℝ) t₀ with ht | ht
  · rw [glue_apply_le ht, glue_apply_le ht, hf]
  · rw [glue_apply_gt ht, glue_apply_gt ht, hg']

end Glue

section Perturb

variable {Y : Type*} [TopologicalSpace Y]

theorem coe_maxI (a b : I) : ((max a b : I) : ℝ) = max (a : ℝ) b := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, max_eq_right (Subtype.coe_le_coe.2 h)]
  · rw [max_eq_left h, max_eq_left (Subtype.coe_le_coe.2 h)]

/-- **Tails in the compact-open topology.** A neighbourhood of a path `γ` contains every path
agreeing with `γ` on some `[0,t₀]`, `t₀ < 1`, and staying in some neighbourhood of `γ(1)` after
`t₀`. -/
theorem exists_tail_perturb {γ : C(I, Y)} {O : Set C(I, Y)} (hO : O ∈ 𝓝 γ) :
    ∃ t₀ : I, (t₀ : ℝ) < 1 ∧ ∃ V ∈ 𝓝 (γ 1), (∀ t : I, (t₀ : ℝ) ≤ t → γ t ∈ V) ∧
      ∀ f : C(I, Y), (∀ t : I, (t : ℝ) ≤ t₀ → f t = γ t) → (∀ t : I, (t₀ : ℝ) ≤ t → f t ∈ V) →
        f ∈ O := by
  let P : Set C(I, Y) → Prop := fun O => ∃ t₀ : I, (t₀ : ℝ) < 1 ∧ ∃ V ∈ 𝓝 (γ 1),
    (∀ t : I, (t₀ : ℝ) ≤ t → γ t ∈ V) ∧
      ∀ f : C(I, Y), (∀ t : I, (t : ℝ) ≤ t₀ → f t = γ t) → (∀ t : I, (t₀ : ℝ) ≤ t → f t ∈ V) →
        f ∈ O
  let 𝓕 : Filter C(I, Y) :=
    { sets := {O | P O}
      univ_sets := ⟨0, by simp, univ, univ_mem, fun _ _ => mem_univ _, fun _ _ _ => mem_univ _⟩
      sets_of_superset := fun {O O'} ⟨t₀, h1, V, hV, hγV, hf⟩ hOO' =>
        ⟨t₀, h1, V, hV, hγV, fun f h₁ h₂ => hOO' (hf f h₁ h₂)⟩
      inter_sets := fun {O O'} ⟨t₁, h1, V₁, hV₁, hγV₁, hf₁⟩ ⟨t₂, h2, V₂, hV₂, hγV₂, hf₂⟩ => by
        refine ⟨max t₁ t₂, by rw [coe_maxI]; exact max_lt h1 h2, V₁ ∩ V₂, inter_mem hV₁ hV₂,
          fun t ht => ⟨hγV₁ t ((le_max_left _ _).trans (by rwa [coe_maxI] at ht)),
            hγV₂ t ((le_max_right _ _).trans (by rwa [coe_maxI] at ht))⟩, fun f hf hfV => ?_⟩
        rw [coe_maxI] at hf hfV
        refine ⟨hf₁ f (fun t ht => hf t (ht.trans (le_max_left _ _))) fun t ht => ?_,
          hf₂ f (fun t ht => hf t (ht.trans (le_max_right _ _))) fun t ht => ?_⟩
        · rcases le_total (t : ℝ) (max (t₁ : ℝ) t₂) with h | h
          · rw [hf t h]; exact hγV₁ t ht
          · exact (hfV t h).1
        · rcases le_total (t : ℝ) (max (t₁ : ℝ) t₂) with h | h
          · rw [hf t h]; exact hγV₂ t ht
          · exact (hfV t h).2 }
  suffices hle : 𝓕 ≤ 𝓝 γ from hle hO
  rw [ContinuousMap.nhds_compactOpen]
  refine le_iInf₂ fun K hK => le_iInf₂ fun U hU => le_iInf fun hγ => le_principal_iff.2 ?_
  by_cases h1 : (1 : I) ∈ K
  · have hU1 : U ∈ 𝓝 (γ 1) := hU.mem_nhds (hγ h1)
    obtain ⟨t₀, -, ht₀, htail⟩ := exists_tail_mem (⟨γ, rfl, rfl⟩ : Path (γ 0) (γ 1)) hU1
      (c := 1) one_pos
    refine ⟨t₀, ht₀, U, hU1, htail, fun f hf hfU k hk => ?_⟩
    rcases le_total (k : ℝ) t₀ with h | h
    · show f k ∈ U; rw [hf k h]; exact hγ hk
    · exact hfU k h
  · rcases K.eq_empty_or_nonempty with hKe | hKne
    · exact ⟨0, by simp, univ, univ_mem, fun _ _ => mem_univ _, fun f _ _ => by
        rw [hKe]; exact mapsTo_empty _ _⟩
    · obtain ⟨m, hmK, hm⟩ := hK.exists_isGreatest hKne
      have hm1 : (m : ℝ) < 1 := lt_of_le_of_ne m.2.2 fun h => h1 (by
        rw [show (1 : I) = m from Subtype.ext h.symm]; exact hmK)
      refine ⟨m, hm1, univ, univ_mem, fun _ _ => mem_univ _, fun f hf _ k hk => ?_⟩
      show f k ∈ U
      rw [hf k (hm hk)]; exact hγ hk

end Perturb

/-! ### `theo:ramified_covering_path` -/

section Ramified

universe u

variable {Y : Type u} [TopologicalSpace Y]

/-- `Ω = ⋃_{x ∈ Y} Ω(y₀, x, Y ∖ S)` (`RamcovGX.tex:1324`), as a subspace of `C([0,1], Y)` with the
compact-open topology. -/
def OmegaSpace (S : Set Y) (y₀ : Y) : Set C(I, Y) :=
  {γ | γ 0 = y₀ ∧ ∀ t : I, 0 < (t : ℝ) → (t : ℝ) < 1 → γ t ∈ Sᶜ}

variable {S : Set Y} {y₀ : Y}

/-- An element of `Ω` as a path `y₀ ⇝ γ(1)`. -/
def OmegaSpace.toPath (γ : OmegaSpace S y₀) : Path y₀ (γ.1 1) := ⟨γ.1, γ.2.1, rfl⟩

theorem OmegaSpace.memOmega (γ : OmegaSpace S y₀) : MemOmega Sᶜ (OmegaSpace.toPath γ) := γ.2.2

theorem OmegaSpace.mem_compl (hy₀ : y₀ ∈ Sᶜ) (γ : OmegaSpace S y₀) {t : I} (ht : (t : ℝ) < 1) :
    γ.1 t ∈ Sᶜ := by
  rcases eq_or_lt_of_le t.2.1 with h | h
  · rw [show t = 0 from Subtype.ext h.symm, γ.2.1]; exact hy₀
  · exact γ.2.2 t h ht

theorem AlmostHomotopic.cast {U : Set Y} {x y : Y} {γ₁ γ₂ : Path x y}
    (h : AlmostHomotopic U γ₁ γ₂) {x' y' : Y} (hx : x' = x) (hy : y' = y) :
    AlmostHomotopic U (γ₁.cast hx hy) (γ₂.cast hx hy) := by
  subst hx; subst hy; exact h

theorem AlmostHomotopicCC.cast {U : Set Y} {x y : Y} {γ₁ γ₂ : Path x y}
    (h : AlmostHomotopicCC U γ₁ γ₂) {x' y' : Y} (hx : x' = x) (hy : y' = y) :
    AlmostHomotopicCC U (γ₁.cast hx hy) (γ₂.cast hx hy) := by
  subst hx; subst hy; exact h

/-- Almost homotopy with respect to `Y ∖ S` on `Ω` (paths with the same end), in the literal
reading of `def:almost_trivial_loop` (DEC-55). -/
def OmegaRel (S : Set Y) (y₀ : Y) (γ γ' : OmegaSpace S y₀) : Prop :=
  ∃ h : γ.1 1 = γ'.1 1,
    AlmostHomotopicCC Sᶜ (OmegaSpace.toPath γ) ((OmegaSpace.toPath γ').cast rfl h)

/-- Almost homotopy is an equivalence relation on `Ω` (`lem:hausdorff_first_countable_connected`
for `U = Y ∖ S`). -/
theorem omegaRel_equivalence [LocPathConnectedSpace Y] (hSo : IsOpen (Sᶜ : Set Y))
    (hsc : SemilocallySimplyConnected (Sᶜ : Set Y)) (hy₀ : y₀ ∈ Sᶜ) :
    Equivalence (OmegaRel S y₀) where
  refl γ := ⟨rfl, almostHomotopicCC_refl hy₀ (OmegaSpace.memOmega γ)⟩
  symm := fun ⟨h, H⟩ => ⟨h.symm, H.symm.cast rfl h.symm⟩
  trans := fun ⟨h, H⟩ ⟨h', H'⟩ => ⟨h.trans h', H.trans hSo hsc (H'.cast rfl h)⟩

/-- `X`: the almost homotopy classes of `Ω` with respect to `Y ∖ S`, with the quotient topology
(the quotient by `GX.OmegaRel`, an equivalence relation under the hypotheses of the theorem,
`GX.omegaRel_equivalence`). -/
abbrev OmegaQuot (S : Set Y) (y₀ : (Sᶜ : Set Y)) : Type u := Quot (OmegaRel S (y₀ : Y))

/-- `\overline φ : X → Y`, induced by `φ : γ ↦ γ(1)`. -/
def omegaEnd (S : Set Y) (y₀ : (Sᶜ : Set Y)) : OmegaQuot S y₀ → Y :=
  Quot.lift (fun γ : OmegaSpace S (y₀ : Y) => γ.1 1) fun _ _ h => h.1

end Ramified

section RamifiedMain

universe u

variable {Y : Type u} [TopologicalSpace Y] [T2Space Y] [LocPathConnectedSpace Y]
  [FirstCountableTopology Y] [ConnectedSpace Y] {S : Set Y}

/-- The base point `ŷ₀` of `\widetilde Y^S` over `y₀`. -/
def maxBase (S : Set Y) (y₀ : (Sᶜ : Set Y)) : MaxBranchedCover S y₀ :=
  SpreadEnd.ofPoint (univCoverProj S y₀) (UniversalCover.base y₀)

theorem maxBase_base (y₀ : (Sᶜ : Set Y)) : (maxBase S y₀).base = y₀ := rfl

/-- The lift from `ŷ₀` of a path of `Ω`. -/
def omegaLift (hS : IsSkeletal S) (hSc : SemilocallySimplyConnected (Sᶜ : Set Y))
    (y₀ : (Sᶜ : Set Y)) (γ : OmegaSpace S (y₀ : Y)) : C(I, MaxBranchedCover S y₀) :=
  (maxBranched_existsUnique_lift hS hSc y₀ y₀.2 (OmegaSpace.memOmega γ)
    (maxBase_base y₀)).exists.choose

variable (hS : IsSkeletal S) (hSc : SemilocallySimplyConnected (Sᶜ : Set Y)) (y₀ : (Sᶜ : Set Y))

theorem omegaLift_spec (γ : OmegaSpace S (y₀ : Y)) :
    (∀ t, (omegaLift hS hSc y₀ γ t).base = γ.1 t) ∧ omegaLift hS hSc y₀ γ 0 = maxBase S y₀ :=
  (maxBranched_existsUnique_lift hS hSc y₀ y₀.2 (OmegaSpace.memOmega γ)
    (maxBase_base y₀)).exists.choose_spec

theorem omegaLift_unique (γ : OmegaSpace S (y₀ : Y)) {Γ : C(I, MaxBranchedCover S y₀)}
    (hΓ : ∀ t, (Γ t).base = γ.1 t) (h0 : Γ 0 = maxBase S y₀) : Γ = omegaLift hS hSc y₀ γ :=
  (maxBranched_existsUnique_lift hS hSc y₀ y₀.2 (OmegaSpace.memOmega γ)
    (maxBase_base y₀)).unique ⟨hΓ, h0⟩ (omegaLift_spec hS hSc y₀ γ)

/-- `ψ` is constant exactly on the almost homotopy classes (`lem:almost_homotopic_carac2`). -/
theorem omegaLift_one_eq_iff (γ γ' : OmegaSpace S (y₀ : Y)) :
    omegaLift hS hSc y₀ γ 1 = omegaLift hS hSc y₀ γ' 1 ↔ OmegaRel S y₀ γ γ' := by
  constructor
  · intro h1
    have hb : γ.1 1 = γ'.1 1 := by
      rw [← (omegaLift_spec hS hSc y₀ γ).1, ← (omegaLift_spec hS hSc y₀ γ').1, h1]
    exact ⟨hb, (almost_homotopic_carac2_cc hS hSc y₀ y₀.2 (OmegaSpace.memOmega γ)
      (γ₂ := (OmegaSpace.toPath γ').cast rfl hb) (OmegaSpace.memOmega γ')
      (omegaLift_spec hS hSc y₀ γ).1 (omegaLift_spec hS hSc y₀ γ').1
      ((omegaLift_spec hS hSc y₀ γ).2.trans (omegaLift_spec hS hSc y₀ γ').2.symm)).1 h1⟩
  · rintro ⟨hb, H⟩
    exact (almost_homotopic_carac2_cc hS hSc y₀ y₀.2 (OmegaSpace.memOmega γ)
      (γ₂ := (OmegaSpace.toPath γ').cast rfl hb) (OmegaSpace.memOmega γ')
      (omegaLift_spec hS hSc y₀ γ).1 (omegaLift_spec hS hSc y₀ γ').1
      ((omegaLift_spec hS hSc y₀ γ).2.trans (omegaLift_spec hS hSc y₀ γ').2.symm)).2 H

omit [T2Space Y] [LocPathConnectedSpace Y] [FirstCountableTopology Y] [ConnectedSpace Y] in
/-- The tail of a path lying over `V` stays in one component of `p ⁻¹' V`. -/
theorem comp_tail {E : Type*} [TopologicalSpace E] {p : E → Y} {Γ : C(I, E)} {V : Set Y}
    {t₀ : I} (h : ∀ t : I, (t₀ : ℝ) ≤ t → p (Γ t) ∈ V) :
    (∀ t : I, (t₀ : ℝ) ≤ t → Γ t ∈ connectedComponentIn (p ⁻¹' V) (Γ t₀)) ∧
      connectedComponentIn (p ⁻¹' V) (Γ t₀) = connectedComponentIn (p ⁻¹' V) (Γ 1) := by
  have hsub : Γ '' Icc t₀ 1 ⊆ connectedComponentIn (p ⁻¹' V) (Γ t₀) :=
    (isPreconnected_Icc.image _ Γ.continuous.continuousOn).subset_connectedComponentIn
      ⟨t₀, ⟨le_rfl, t₀.2.2⟩, rfl⟩ (by
        rintro _ ⟨t, ht, rfl⟩
        exact h t ht.1)
  have hm : ∀ t : I, (t₀ : ℝ) ≤ t → Γ t ∈ connectedComponentIn (p ⁻¹' V) (Γ t₀) :=
    fun t ht => hsub ⟨t, ⟨ht, t.2.2⟩, rfl⟩
  exact ⟨hm, connectedComponentIn_eq (hm 1 t₀.2.2)⟩

/-- `ψ : Ω → \widetilde Y^S` is continuous (the second item of the proof of
`theo:ramified_covering_path`; here through the homotopy lifting property over `Y ∖ S`). -/
theorem continuous_omegaLift_one :
    Continuous fun γ : OmegaSpace S (y₀ : Y) => omegaLift hS hSc y₀ γ 1 := by
  obtain ⟨-, hbc, -, -, hl, -⟩ := maxBranched_basic hS hSc y₀
  haveI := hl
  obtain ⟨cov, -⟩ := maxBranched_lifting hS hSc y₀
  set E := MaxBranchedCover S y₀
  have hbase : Continuous (SpreadEnd.base : E → Y) := hbc.isSpread.continuous
  rw [continuous_iff_continuousAt]
  intro γ
  rw [ContinuousAt, (nhds_basis_opens _).tendsto_right_iff]
  rintro N ⟨hmem, hN⟩
  set L := omegaLift hS hSc y₀ γ
  obtain ⟨V, hV, hyV, hVN⟩ := (isSpread_iff.1 hbc.isSpread).2.2 (L 1) N hN hmem
  have hL1 : (L 1).base = γ.1 1 := (omegaLift_spec hS hSc y₀ γ).1 1
  rw [hL1] at hyV
  set V' := connectedComponentIn V (γ.1 1)
  have hV' : IsOpen V' := hV.connectedComponentIn
  have hyV' : γ.1 1 ∈ V' := mem_connectedComponentIn hyV
  set W := connectedComponentIn ((SpreadEnd.base : E → Y) ⁻¹' V') (L 1) with hWdef
  have hW : IsOpen W := (hV'.preimage hbase).connectedComponentIn
  have hWN : W ⊆ N := (connectedComponentIn_mono _ (preimage_mono
    (connectedComponentIn_subset V _))).trans hVN
  obtain ⟨t₀, -, ht₀1, ht₀⟩ := exists_tail_mem (OmegaSpace.toPath γ) (hV'.mem_nhds hyV')
    (c := 1) one_pos
  -- the homotopy `(t, η) ↦ η(t t₀)` and its lift
  have hlt : ∀ t : I, ((t * t₀ : I) : ℝ) < 1 := fun t => by
    rw [Set.Icc.coe_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left t₀.2.1 t.2.2) ht₀1
  have hmemH : ∀ z : I × OmegaSpace S (y₀ : Y), z.2.1 (z.1 * t₀) ∈ Sᶜ := fun z =>
    OmegaSpace.mem_compl y₀.2 z.2 (hlt z.1)
  let H : C(I × OmegaSpace S (y₀ : Y), (Sᶜ : Set Y)) :=
    ⟨fun z => ⟨z.2.1 (z.1 * t₀), hmemH z⟩, by
      refine Continuous.subtype_mk ?_ _
      exact continuous_eval.comp ((continuous_subtype_val.comp continuous_snd).prodMk
        (continuous_fst.mul continuous_const))⟩
  have hb0 : (maxBase S y₀) ∈ (SpreadEnd.base : E → Y) ⁻¹' Sᶜ := y₀.2
  let f : C(OmegaSpace S (y₀ : Y), (SpreadEnd.base : E → Y) ⁻¹' Sᶜ) :=
    ContinuousMap.const _ ⟨maxBase S y₀, hb0⟩
  have H_0 : ∀ a, H (0, a) = Sᶜ.restrictPreimage SpreadEnd.base (f a) := fun a => Subtype.ext (by
    show a.1 (0 * t₀) = (maxBase S y₀).base
    rw [zero_mul, a.2.1, maxBase_base])
  set Hl := cov.liftHomotopy H f H_0
  have claim : ∀ η : OmegaSpace S (y₀ : Y), (Hl (1, η) : E) = omegaLift hS hSc y₀ η t₀ := by
    intro η
    let Γ₁ : C(I, E) := ⟨fun t => (Hl (t, η) : E),
      continuous_subtype_val.comp (Hl.continuous.comp (continuous_id.prodMk continuous_const))⟩
    let Γ₂ : C(I, E) := ⟨fun t => omegaLift hS hSc y₀ η (t * t₀),
      (omegaLift hS hSc y₀ η).continuous.comp (continuous_id.mul continuous_const)⟩
    have := lift_unique cov (γ := fun t => η.1 (t * t₀)) (Γ₁ := Γ₁) (Γ₂ := Γ₂)
      (fun t _ => hmemH (t, η))
      (fun t => congrArg Subtype.val (congrFun (cov.liftHomotopy_lifts H f H_0) (t, η)))
      (fun t => (omegaLift_spec hS hSc y₀ η).1 _)
      (by
        show (Hl (0, η) : E) = omegaLift hS hSc y₀ η (0 * t₀)
        rw [cov.liftHomotopy_zero, zero_mul, (omegaLift_spec hS hSc y₀ η).2]; rfl)
    have h1 := congrArg (fun Γ : C(I, E) => Γ 1) this
    simpa [Γ₁, Γ₂] using h1
  set g : OmegaSpace S (y₀ : Y) → E := fun η => (Hl (1, η) : E)
  have hg : Continuous g :=
    continuous_subtype_val.comp (Hl.continuous.comp (continuous_const.prodMk continuous_id))
  have htail : ∀ η : OmegaSpace S (y₀ : Y), (∀ t : I, (t₀ : ℝ) ≤ t → η.1 t ∈ V') →
      (∀ t : I, (t₀ : ℝ) ≤ t → (omegaLift hS hSc y₀ η t).base ∈ V') := fun η h t ht => by
    rw [(omegaLift_spec hS hSc y₀ η).1]; exact h t ht
  have hγW : g γ ∈ W := by
    show (Hl (1, γ) : E) ∈ W
    rw [claim, hWdef, ← (comp_tail (htail γ ht₀)).2]
    exact mem_connectedComponentIn (htail γ ht₀ t₀ le_rfl)
  have hO₂ : IsOpen {η : OmegaSpace S (y₀ : Y) | MapsTo η.1 (Icc t₀ 1) V'} :=
    (ContinuousMap.isOpen_setOf_mapsTo isCompact_Icc hV').preimage continuous_subtype_val
  refine Filter.mem_of_superset (inter_mem ((hW.preimage hg).mem_nhds hγW)
    (hO₂.mem_nhds fun t ht => ht₀ t ht.1)) ?_
  rintro η ⟨h1, h2⟩
  have h2' : ∀ t : I, (t₀ : ℝ) ≤ t → η.1 t ∈ V' := fun t ht => h2 ⟨ht, t.2.2⟩
  have hct := comp_tail (htail η h2')
  have hgη : omegaLift hS hSc y₀ η t₀ ∈ W := by
    have := h1; simp only [mem_preimage, g, claim] at this; exact this
  apply hWN
  have hW' : W = connectedComponentIn ((SpreadEnd.base : E → Y) ⁻¹' V')
      (omegaLift hS hSc y₀ η t₀) := by rw [hWdef]; exact connectedComponentIn_eq hgη
  rw [hW']
  exact hct.1 1 t₀.2.2

/-- `ψ : Ω → \widetilde Y^S` is onto (the first item of the proof). -/
theorem surjective_omegaLift_one :
    Surjective fun γ : OmegaSpace S (y₀ : Y) => omegaLift hS hSc y₀ γ 1 := by
  obtain ⟨-, hbc, -, -, hl, -⟩ := maxBranched_basic hS hSc y₀
  haveI := hl
  haveI := hbc.connectedSpace_source
  set E := MaxBranchedCover S y₀
  have hE : IsPortly ((SpreadEnd.base : E → Y) ⁻¹' Sᶜ) := hbc.isPortly_preimage hS
  intro e
  obtain ⟨γh, hγh⟩ := path_covering hE (a := maxBase S y₀) (b := e) y₀.2
  set η : C(I, Y) := (γh.map hbc.isSpread.continuous).toContinuousMap
  have hη : η ∈ OmegaSpace S (y₀ : Y) := ⟨by
    show (γh 0).base = y₀
    rw [γh.source]; rfl, fun t _ h1 => hγh t h1⟩
  refine ⟨⟨η, hη⟩, ?_⟩
  have := omegaLift_unique hS hSc y₀ ⟨η, hη⟩ (Γ := γh.toContinuousMap) (fun t => rfl) γh.source
  show omegaLift hS hSc y₀ ⟨η, hη⟩ 1 = e
  rw [← this]; exact γh.target

/-- `ψ : Ω → \widetilde Y^S` is open (the third item of the proof, `RamcovGX.tex:1365`; see the
SCOPE for why the paper's subbasic case analysis is replaced). -/
theorem isOpenMap_omegaLift_one :
    IsOpenMap fun γ : OmegaSpace S (y₀ : Y) => omegaLift hS hSc y₀ γ 1 := by
  obtain ⟨-, hbc, -, -, hl, -⟩ := maxBranched_basic hS hSc y₀
  haveI := hl
  set E := MaxBranchedCover S y₀
  have hbase : Continuous (SpreadEnd.base : E → Y) := hbc.isSpread.continuous
  have hE : IsPortly ((SpreadEnd.base : E → Y) ⁻¹' Sᶜ) := hbc.isPortly_preimage hS
  intro O hO
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨γ, hγO, rfl⟩
  obtain ⟨O', hO'n, hO'O⟩ := (mem_nhds_subtype _ γ O).1 (hO.mem_nhds hγO)
  obtain ⟨t₀, ht₀1, V, hV, hγV, hP⟩ := exists_tail_perturb hO'n
  obtain ⟨V₀, hV₀V, hV₀o, hγ1V₀⟩ := mem_nhds_iff.1 hV
  set V₃ := connectedComponentIn V₀ (γ.1 1)
  have hV₃o : IsOpen V₃ := hV₀o.connectedComponentIn
  have hγ1V₃ : γ.1 1 ∈ V₃ := mem_connectedComponentIn hγ1V₀
  have hV₃V : V₃ ⊆ V := (connectedComponentIn_subset _ _).trans hV₀V
  obtain ⟨t₂, -, ht₂1, ht₂⟩ := exists_tail_mem (OmegaSpace.toPath γ) (hV₃o.mem_nhds hγ1V₃)
    (c := 1) one_pos
  set t₁ : I := ⟨max (max (t₀ : ℝ) t₂) (1 / 2), by
    constructor
    · exact le_max_of_le_right (by norm_num)
    · exact max_le (max_le t₀.2.2 t₂.2.2) (by norm_num)⟩ with ht₁def
  have ht₁1 : (t₁ : ℝ) < 1 := max_lt (max_lt ht₀1 ht₂1) (by norm_num)
  have ht₁0 : (t₀ : ℝ) ≤ t₁ := (le_max_left _ _).trans (le_max_left _ _)
  have ht₁2 : (t₂ : ℝ) ≤ t₁ := (le_max_right _ _).trans (le_max_left _ _)
  have hP' : ∀ f : C(I, Y), (∀ t : I, (t : ℝ) ≤ t₁ → f t = γ.1 t) →
      (∀ t : I, (t₁ : ℝ) ≤ t → f t ∈ V₃) → f ∈ O' := fun f hf hfV => hP f
    (fun t ht => hf t (ht.trans ht₁0)) fun t ht => by
      rcases le_total (t : ℝ) t₁ with h | h
      · rw [hf t h]; exact hγV t ht
      · exact hV₃V (hfV t h)
  set L := omegaLift hS hSc y₀ γ
  set W := connectedComponentIn ((SpreadEnd.base : E → Y) ⁻¹' V₃) (L 1) with hWdef
  have hWo : IsOpen W := (hV₃o.preimage hbase).connectedComponentIn
  have hL1 : L 1 ∈ W := mem_connectedComponentIn (show (L 1).base ∈ V₃ by
    rw [(omegaLift_spec hS hSc y₀ γ).1]; exact hγ1V₃)
  have htail : ∀ t : I, (t₁ : ℝ) ≤ t → (L t).base ∈ V₃ := fun t ht => by
    rw [(omegaLift_spec hS hSc y₀ γ).1]; exact ht₂ t (ht₁2.trans ht)
  have hct := comp_tail htail
  have hLW : L t₁ ∈ W := by rw [hWdef, ← hct.2]; exact mem_connectedComponentIn (htail t₁ le_rfl)
  have hLE : L t₁ ∈ (SpreadEnd.base : E → Y) ⁻¹' Sᶜ := by
    show (L t₁).base ∈ Sᶜ
    rw [(omegaLift_spec hS hSc y₀ γ).1]; exact OmegaSpace.mem_compl y₀.2 γ ht₁1
  refine Filter.mem_of_superset (hWo.mem_nhds hL1) fun e' he' => ?_
  obtain ⟨ζ, hζW, hζE⟩ := exists_path_of_isPortly_of_isOpen hE hWo
    isPreconnected_connectedComponentIn hLE hLW he'
  set ζY : C(I, Y) := (ζ.map hbase).toContinuousMap
  have hζ0 : ζY 0 = γ.1 t₁ := by
    show (ζ 0).base = γ.1 t₁
    rw [ζ.source, (omegaLift_spec hS hSc y₀ γ).1]
  set η₀ : C(I, Y) := glue γ.1 t₁ ht₁1 ζY hζ0
  have hη₀ : η₀ ∈ OmegaSpace S (y₀ : Y) := by
    refine ⟨by rw [glue_zero]; exact γ.2.1, fun t h0 h1 => ?_⟩
    rcases glue_mem (f := γ.1) (h := ht₁1) (hg := hζ0) t with ⟨_, he⟩ | ⟨r, he, hr⟩
    · rw [he]; exact γ.2.2 t h0 h1
    · rw [he]; exact hζE r (hr h1)
  have hη₀O' : η₀ ∈ O' := hP' η₀ (fun t ht => glue_apply_le ht) fun t ht => by
    rcases eq_or_lt_of_le ht with h | h
    · rw [glue_apply_le h.ge]; exact ht₂ t (ht₁2.trans ht)
    · rw [glue_apply_gt h]
      exact (connectedComponentIn_subset _ _ (hζW _) : ζ _ ∈ (SpreadEnd.base : E → Y) ⁻¹' V₃)
  refine ⟨⟨η₀, hη₀⟩, hO'O hη₀O', ?_⟩
  have hζ0' : ζ.toContinuousMap 0 = L t₁ := ζ.source
  have hlift := omegaLift_unique hS hSc y₀ ⟨η₀, hη₀⟩ (Γ := glue L t₁ ht₁1 ζ.toContinuousMap hζ0')
    (fun t => glue_map (φ := SpreadEnd.base) (fun t => (omegaLift_spec hS hSc y₀ γ).1 t)
      (fun t => rfl) hζ0 t)
    (by rw [glue_zero]; exact (omegaLift_spec hS hSc y₀ γ).2)
  show omegaLift hS hSc y₀ ⟨η₀, hη₀⟩ 1 = e'
  rw [← hlift, glue_one]; exact ζ.target

include hS hSc in
/-- **`theo:ramified_covering_path`** (`RamcovGX.tex:1322`), with the semilocal simple
connectivity of `Y ∖ S` (DEC-70; the proof uses it, and without it `\widetilde Y^S` is not defined;
reading (d) of SCOPE, the quotient topology, is covered by DEC-70, DEC-79 (b)). The
almost homotopy classes `X` of `Ω = ⋃_x Ω(y₀,x,Y ∖ S)` with the quotient of the compact-open
topology are homeomorphic over `Y` to `\widetilde Y^S`: `\overline φ = p ∘ Ψ`. -/
theorem ramified_covering_path :
    ∃ Ψ : OmegaQuot S y₀ ≃ₜ MaxBranchedCover S y₀, ∀ q, (Ψ q).base = omegaEnd S y₀ q := by
  set ψ : OmegaSpace S (y₀ : Y) → MaxBranchedCover S y₀ := fun γ => omegaLift hS hSc y₀ γ 1
  have hψc : Continuous ψ := continuous_omegaLift_one hS hSc y₀
  have hψo : IsOpenMap ψ := isOpenMap_omegaLift_one hS hSc y₀
  have hψs : Surjective ψ := surjective_omegaLift_one hS hSc y₀
  set ψb : OmegaQuot S y₀ → MaxBranchedCover S y₀ :=
    Quot.lift ψ fun a b h => (omegaLift_one_eq_iff hS hSc y₀ a b).2 h
  have hinj : Injective ψb := by
    intro q q'
    induction q using Quot.inductionOn with | h a =>
    induction q' using Quot.inductionOn with | h b =>
    intro h
    exact Quot.sound ((omegaLift_one_eq_iff hS hSc y₀ a b).1 h)
  have hsurj : Surjective ψb := fun e => by
    obtain ⟨γ, hγ⟩ := hψs e
    exact ⟨Quot.mk _ γ, hγ⟩
  have hc : Continuous ψb := continuous_quot_lift _ hψc
  have ho : IsOpenMap ψb := by
    intro O hO
    have : ψb '' O = ψ '' (Quot.mk (OmegaRel S (y₀ : Y)) ⁻¹' O) := by
      ext e
      constructor
      · rintro ⟨q, hq, rfl⟩
        induction q using Quot.inductionOn with | h a =>
        exact ⟨a, hq, rfl⟩
      · rintro ⟨a, ha, rfl⟩
        exact ⟨_, ha, rfl⟩
    rw [this]
    exact hψo _ (hO.preimage continuous_quot_mk)
  refine ⟨(Equiv.ofBijective ψb ⟨hinj, hsurj⟩).toHomeomorphOfContinuousOpen hc ho, fun q => ?_⟩
  induction q using Quot.inductionOn with | h a =>
  exact (omegaLift_spec hS hSc y₀ a).1 1

include hS hSc in
/-- `theo:ramified_covering_path`, the branched covering: `\overline φ : X → Y` is a branched
covering, possibly branched over `S`. -/
theorem omegaEnd_isBranchedCovering :
    IsBranchedCovering (omegaEnd S y₀) ∧ IsPossiblyBranchedOver (omegaEnd S y₀) S := by
  obtain ⟨Ψ, hΨ⟩ := ramified_covering_path hS hSc y₀
  obtain ⟨hbc, hpb⟩ := maxBranched_isBranchedCovering hS hSc y₀
  have heq : omegaEnd S y₀ = (SpreadEnd.base : MaxBranchedCover S y₀ → Y) ∘ Ψ :=
    funext fun q => (hΨ q).symm
  rw [heq]
  have hord := image_ordY_of_homeomorph (p := (SpreadEnd.base : MaxBranchedCover S y₀ → Y))
    (p' := SpreadEnd.base ∘ Ψ) Ψ.symm (Homeomorph.refl Y) (fun e => by simp)
  have hid : ⇑(Homeomorph.refl Y) = id := rfl
  rw [hid, image_id] at hord
  refine ⟨hbc.comp_homeomorph Ψ, ?_⟩
  unfold IsPossiblyBranchedOver branchingLocus
  rw [← hord]
  exact hpb

end RamifiedMain

/-! ### `def:covering_branched_two_paths`, `prop:general_fiber_path` -/

section FiberPath

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Paths with fixed start `a`, in `Y ∖ S`, with free end in `U` (`RamcovGX.tex:1387`). -/
def FreePath (S : Set Y) (a : Y) (U : Set Y) : Set C(I, Y) :=
  {γ | γ 0 = a ∧ (∀ t, γ t ∈ Sᶜ) ∧ γ 1 ∈ U}

/-- **`def:covering_branched_two_paths`** (`RamcovGX.tex:1385`). Two paths from `a` with free end
in `U` are *`p`-homotopic* if their lifts from the same start point `â` end in the same connected
component of `p⁻¹(U)`. -/
def PHomotopic (p : X → Y) (â : X) (U : Set Y) (γ₁ γ₂ : C(I, Y)) : Prop :=
  ∃ Γ₁ Γ₂ : C(I, X), (∀ t, p (Γ₁ t) = γ₁ t) ∧ (∀ t, p (Γ₂ t) = γ₂ t) ∧ Γ₁ 0 = â ∧ Γ₂ 0 = â ∧
    connectedComponentIn (p ⁻¹' U) (Γ₁ 1) = connectedComponentIn (p ⁻¹' U) (Γ₂ 1)

variable [T2Space X] {p : X → Y} {S : Set Y} (cov : IsCoveringMap (Sᶜ.restrictPreimage p))
  {a : Y} {â : X} (hâ : p â = a)

/-- An element of `FreePath` as a path. -/
def FreePath.toPath {U : Set Y} (γ : FreePath S a U) : Path a (γ.1 1) := ⟨γ.1, γ.2.1, rfl⟩

include cov hâ in
theorem FreePath.exists_lift {U : Set Y} (γ : FreePath S a U) :
    ∃ Γ : C(I, X), (∀ t, p (Γ t) = γ.1 t) ∧ Γ 0 = â :=
  exists_lift_of_mem cov (FreePath.toPath γ) γ.2.2.1 hâ

include cov in
theorem FreePath.lift_unique {U : Set Y} (γ : FreePath S a U) {Γ Γ' : C(I, X)}
    (hΓ : ∀ t, p (Γ t) = γ.1 t) (hΓ' : ∀ t, p (Γ' t) = γ.1 t) (h0 : Γ 0 = Γ' 0) : Γ = Γ' :=
  _root_.GX.lift_unique cov (fun t _ => γ.2.2.1 t) hΓ hΓ' h0

include cov in
theorem pHomotopic_iff {U : Set Y} {γ₁ γ₂ : FreePath S a U} {Γ₁ Γ₂ : C(I, X)}
    (hΓ₁ : ∀ t, p (Γ₁ t) = γ₁.1 t) (hΓ₂ : ∀ t, p (Γ₂ t) = γ₂.1 t) (h₁ : Γ₁ 0 = â)
    (h₂ : Γ₂ 0 = â) :
    PHomotopic p â U γ₁.1 γ₂.1 ↔
      connectedComponentIn (p ⁻¹' U) (Γ₁ 1) = connectedComponentIn (p ⁻¹' U) (Γ₂ 1) := by
  constructor
  · rintro ⟨Δ₁, Δ₂, hΔ₁, hΔ₂, h₁', h₂', h⟩
    rw [FreePath.lift_unique cov γ₁ hΓ₁ hΔ₁ (h₁.trans h₁'.symm),
      FreePath.lift_unique cov γ₂ hΓ₂ hΔ₂ (h₂.trans h₂'.symm)]
    exact h
  · exact fun h => ⟨Γ₁, Γ₂, hΓ₁, hΓ₂, h₁, h₂, h⟩

include cov hâ in
theorem pHomotopic_equivalence (U : Set Y) :
    Equivalence fun γ₁ γ₂ : FreePath S a U => PHomotopic p â U γ₁.1 γ₂.1 where
  refl γ := by
    obtain ⟨Γ, hΓ, h0⟩ := FreePath.exists_lift cov hâ γ
    exact (pHomotopic_iff cov hΓ hΓ h0 h0).2 rfl
  symm := fun ⟨Γ₁, Γ₂, h₁, h₂, h₁0, h₂0, h⟩ => ⟨Γ₂, Γ₁, h₂, h₁, h₂0, h₁0, h.symm⟩
  trans := fun {γ₁ γ₂ γ₃} ⟨Γ₁, Γ₂, h₁, h₂, h₁0, h₂0, h⟩ ⟨Γ₂', Γ₃, h₂', h₃, h₂0', h₃0, h'⟩ => by
    refine ⟨Γ₁, Γ₃, h₁, h₃, h₁0, h₃0, h.trans ?_⟩
    rw [FreePath.lift_unique cov γ₂ h₂ h₂' (h₂0.trans h₂0'.symm)]
    exact h'

/-- The `p`-homotopy setoid. -/
def pSetoid (U : Set Y) : Setoid (FreePath S a U) :=
  ⟨fun γ₁ γ₂ => PHomotopic p â U γ₁.1 γ₂.1, pHomotopic_equivalence cov hâ U⟩

/-- **`π₁(a,p,U)`** (`RamcovGX.tex:1392`): paths with fixed start at `a` and free end in `U` up to
`p`-homotopy (a discrete space). -/
def PiOneP (U : Set Y) : Type _ := Quotient (pSetoid cov hâ U)

instance (U : Set Y) : TopologicalSpace (PiOneP cov hâ U) := ⊥

instance (U : Set Y) : DiscreteTopology (PiOneP cov hâ U) := ⟨rfl⟩

/-- The natural map `π₁(a,p,U) → π₁(a,p,V)` for `U ⊆ V`. -/
def piOnePMap {U V : Set Y} (hUV : U ⊆ V) : PiOneP cov hâ U → PiOneP cov hâ V :=
  Quotient.map (fun γ => ⟨γ.1, γ.2.1, γ.2.2.1, hUV γ.2.2.2⟩) fun γ₁ γ₂ ⟨Γ₁, Γ₂, h₁, h₂, h₁0, h₂0, h⟩ =>
    ⟨Γ₁, Γ₂, h₁, h₂, h₁0, h₂0, by
      have hm : Γ₂ 1 ∈ connectedComponentIn (p ⁻¹' U) (Γ₁ 1) := by
        rw [h]; exact mem_connectedComponentIn (show p (Γ₂ 1) ∈ U by rw [h₂]; exact γ₂.2.2.2)
      exact connectedComponentIn_eq (connectedComponentIn_mono _ (preimage_mono hUV) hm)⟩

/-- The component of `p⁻¹(U)` in which the lifts of a class end. -/
def compOfClass (U : Set Y) : PiOneP cov hâ U → Set X :=
  Quotient.lift (fun γ : FreePath S a U => connectedComponentIn (p ⁻¹' U)
      ((FreePath.exists_lift cov hâ γ).choose 1)) fun γ₁ γ₂ h =>
    (pHomotopic_iff cov (FreePath.exists_lift cov hâ γ₁).choose_spec.1
      (FreePath.exists_lift cov hâ γ₂).choose_spec.1 (FreePath.exists_lift cov hâ γ₁).choose_spec.2
      (FreePath.exists_lift cov hâ γ₂).choose_spec.2).1 h

theorem compOfClass_mk {U : Set Y} (γ : FreePath S a U) {Γ : C(I, X)} (hΓ : ∀ t, p (Γ t) = γ.1 t)
    (h0 : Γ 0 = â) : compOfClass cov hâ U (Quotient.mk _ γ) = connectedComponentIn (p ⁻¹' U) (Γ 1) := by
  show connectedComponentIn (p ⁻¹' U) ((FreePath.exists_lift cov hâ γ).choose 1) = _
  rw [FreePath.lift_unique cov γ (FreePath.exists_lift cov hâ γ).choose_spec.1 hΓ
    ((FreePath.exists_lift cov hâ γ).choose_spec.2.trans h0.symm)]

theorem compOfClass_injective (U : Set Y) : Injective (compOfClass cov hâ U) := by
  intro c c'
  induction c using Quotient.inductionOn with | h γ =>
  induction c' using Quotient.inductionOn with | h γ' =>
  intro h
  obtain ⟨Γ, hΓ, h0⟩ := FreePath.exists_lift cov hâ γ
  obtain ⟨Γ', hΓ', h0'⟩ := FreePath.exists_lift cov hâ γ'
  rw [compOfClass_mk cov hâ γ hΓ h0, compOfClass_mk cov hâ γ' hΓ' h0'] at h
  exact Quotient.sound ((pHomotopic_iff cov hΓ hΓ' h0 h0').2 h)

theorem compOfClass_isCompOf {U : Set Y} (c : PiOneP cov hâ U) :
    IsCompOf p U (compOfClass cov hâ U c) := by
  induction c using Quotient.inductionOn with | h γ =>
  obtain ⟨Γ, hΓ, h0⟩ := FreePath.exists_lift cov hâ γ
  rw [compOfClass_mk cov hâ γ hΓ h0]
  exact isCompOf_connectedComponentIn (by rw [hΓ]; exact γ.2.2.2)

theorem compOfClass_piOnePMap {U V : Set Y} (hUV : U ⊆ V) (c : PiOneP cov hâ U) :
    compOfClass cov hâ U c ⊆ compOfClass cov hâ V (piOnePMap cov hâ hUV c) := by
  induction c using Quotient.inductionOn with | h γ =>
  obtain ⟨Γ, hΓ, h0⟩ := FreePath.exists_lift cov hâ γ
  rw [compOfClass_mk cov hâ γ hΓ h0]
  show _ ⊆ compOfClass cov hâ V (Quotient.mk _ ⟨γ.1, γ.2.1, γ.2.2.1, hUV γ.2.2.2⟩)
  rw [compOfClass_mk cov hâ ⟨γ.1, γ.2.1, γ.2.2.1, hUV γ.2.2.2⟩ hΓ h0]
  exact connectedComponentIn_mono _ (preimage_mono hUV)

include hâ in
theorem compOfClass_surjective [LocPathConnectedSpace X] (hp : IsBranchedCovering p)
    (hS : IsSkeletal S) (haS : a ∈ Sᶜ) {U : Set Y} (hU : IsOpen U) {C : Set X}
    (hC : IsCompOf p U C) : ∃ c, compOfClass cov hâ U c = C := by
  haveI := hp.connectedSpace_source
  have hE : IsPortly (p ⁻¹' Sᶜ) := hp.isPortly_preimage hS
  have hEpc : IsPathConnected (p ⁻¹' Sᶜ) :=
    hE.isOpen.isConnected_iff_isPathConnected.1 hE.isConnected
  obtain ⟨z₀, hz₀, rfl⟩ := hC
  have hCo : IsOpen (connectedComponentIn (p ⁻¹' U) z₀) :=
    (hU.preimage hp.isSpread.continuous).connectedComponentIn
  obtain ⟨z, hzC, hzE⟩ := hE.dense.inter_open_nonempty _ hCo
    ⟨z₀, mem_connectedComponentIn (show z₀ ∈ p ⁻¹' U from hz₀)⟩
  have hâE : â ∈ p ⁻¹' Sᶜ := by show p â ∈ Sᶜ; rw [hâ]; exact haS
  obtain ⟨ζ, hζ⟩ := hEpc.joinedIn â hâE z hzE
  have hγ : (ζ.map hp.isSpread.continuous).toContinuousMap ∈ FreePath S a U :=
    ⟨by show p (ζ 0) = a; rw [ζ.source, hâ], fun t => hζ t, by
      show p (ζ 1) ∈ U; rw [ζ.target]
      exact (connectedComponentIn_subset (p ⁻¹' U) _ hzC : z ∈ p ⁻¹' U)⟩
  refine ⟨Quotient.mk _ ⟨_, hγ⟩, ?_⟩
  rw [compOfClass_mk cov hâ ⟨_, hγ⟩ (Γ := ζ.toContinuousMap) (fun t => rfl) ζ.source]
  show connectedComponentIn (p ⁻¹' U) (ζ 1) = _
  rw [ζ.target]; exact (connectedComponentIn_eq hzC).symm

/-- `def:covering_branched_two_paths` is set in a covering possibly branched over `S`: the part
over `Y ∖ S` is a covering, so lifts exist and are unique. -/
theorem isCoveringMap_restrict_compl {p : X → Y} (hp : IsBranchedCovering p) {S : Set Y}
    (hS : IsSkeletal S) (hpS : IsPossiblyBranchedOver p S) :
    IsCoveringMap (Sᶜ.restrictPreimage p) :=
  (hp.restrict_isCoveringMap (isSkeletal_iff.1 hS) fun y hy => by
    by_contra h; exact hy (hpS h)).1

/-- **`prop:general_fiber_path`** (`RamcovGX.tex:1390`). For a covering `p : X → Y` possibly
branched over a skeletal `S`, `a ∈ Y ∖ S`, `â` over `a`, every `b ∈ Y` and every basis `𝓤` of
connected open neighbourhoods of `b`, the natural map `p⁻¹(b) → ∏_{U ∈ 𝓤} π₁(a,p,U)`
(`x ↦` the classes whose lifts end in the component of `x`) is an embedding (each `π₁(a,p,U)`
discrete) onto the projective limit `lim_{U ∈ 𝓤} π₁(a,p,U)` of the natural maps. -/
theorem general_fiber_path [LocPathConnectedSpace X] [T1Space Y] [LocallyConnectedSpace Y]
    (hp : IsBranchedCovering p) (hS : IsSkeletal S) (haS : a ∈ Sᶜ) {b : Y} (𝓤 : Set (Set Y))
    (h𝓤 : ∀ U ∈ 𝓤, IsCNbhd b U) (hbasis : ∀ N ∈ 𝓝 b, ∃ U ∈ 𝓤, U ⊆ N) :
    ∃ Φ : p ⁻¹' {b} → ∀ U : 𝓤, PiOneP cov hâ U,
      (∀ x (U : 𝓤), compOfClass cov hâ U (Φ x U) = connectedComponentIn (p ⁻¹' U) x) ∧
      IsEmbedding Φ ∧
      range Φ = {f | ∀ U V : 𝓤, ∀ h : (U : Set Y) ⊆ V, piOnePMap cov hâ h (f U) = f V} := by
  have hmem : ∀ (x : p ⁻¹' {b}) (U : 𝓤), IsCompOf p U (connectedComponentIn (p ⁻¹' U) x) :=
    fun x U => isCompOf_connectedComponentIn (by
      rw [show p x = b from x.2]; exact (h𝓤 U U.2).mem)
  have hex : ∀ (x : p ⁻¹' {b}) (U : 𝓤), ∃ c, compOfClass cov hâ U c =
      connectedComponentIn (p ⁻¹' U) x := fun x U =>
    compOfClass_surjective cov hâ hp hS haS (h𝓤 U U.2).isOpen (hmem x U)
  choose Φ hΦ using hex
  have hinj : ∀ U : 𝓤, Injective (compOfClass cov hâ U) := fun U => compOfClass_injective cov hâ U
  -- continuity
  have hfc := continuous_fiberMap hp.isSpread h𝓤
  have hΦc : Continuous Φ := by
    refine continuous_pi fun U => continuous_discrete_rng.2 fun c => ?_
    have : (fun x => Φ x U) ⁻¹' {c} =
        (fun x => (fiberMap p 𝓤 h𝓤 x).toFun U) ⁻¹' {compOfClass cov hâ U c} := by
      ext x
      simp only [mem_preimage, mem_singleton_iff]
      constructor
      · rintro rfl; exact (hΦ x U).symm
      · intro h
        apply hinj U
        rw [hΦ x U]; exact h
    rw [this]
    exact (FiberThread.isOpen_cylinder U _).preimage hfc
  set G : (∀ U : 𝓤, PiOneP cov hâ U) → (𝓤 → DiscreteSets X) :=
    fun f U => compOfClass cov hâ U (f U)
  have hGc : Continuous G :=
    continuous_pi fun U => continuous_of_discreteTopology.comp (continuous_apply U)
  have hcomp : G ∘ Φ = FiberThread.coords ∘ fiberMap p 𝓤 h𝓤 := by
    funext x U
    exact hΦ x U
  have hind : IsInducing (FiberThread.coords ∘ fiberMap p 𝓤 h𝓤) :=
    (IsInducing.induced _).comp (isInducing_fiberMap hp.isSpread h𝓤 hbasis)
  have hΦi : IsInducing Φ := IsInducing.of_comp hΦc hGc (hcomp ▸ hind)
  refine ⟨Φ, hΦ, ⟨hΦi, hΦi.injective⟩, ?_⟩
  ext f
  constructor
  · rintro ⟨x, rfl⟩ U V h
    apply hinj V
    rw [hΦ x V]
    refine (compOfClass_isCompOf cov hâ _).eq_of_meets (hmem x V) ⟨x, ?_, ?_⟩
    · apply compOfClass_piOnePMap cov hâ h
      rw [hΦ x U]
      exact mem_connectedComponentIn (show p x ∈ (U : Set Y) by
        rw [show p x = b from x.2]; exact (h𝓤 U U.2).mem)
    · exact mem_connectedComponentIn (show p x ∈ (V : Set Y) by
        rw [show p x = b from x.2]; exact (h𝓤 V V.2).mem)
  · intro hf
    let s : FiberThread p 𝓤 :=
      { toFun := fun U => compOfClass cov hâ U (f U)
        isCompOf := fun U => compOfClass_isCompOf cov hâ _
        mono := fun U V h => by
          have := compOfClass_piOnePMap cov hâ h (f U)
          rwa [hf U V h] at this }
    obtain ⟨x, hx⟩ := isCompleteSpread_iff_forall_surjective_fiberMap.1 hp.isComplete b 𝓤 h𝓤
      hbasis s
    refine ⟨x, funext fun U => hinj U ?_⟩
    rw [hΦ x U]
    exact congrArg (fun t : FiberThread p 𝓤 => t.toFun U) hx

end FiberPath

/-! ### `prop:general_fiber_path_universal` -/

section FreeHom

variable {Y : Type*} [TopologicalSpace Y]

/-- Homotopy of paths of `Y ∖ S` with fixed start `a` and free end in `U` (the "up to homotopy" of
`RamcovGX.tex:1402`): a homotopy `H` in `Y ∖ S`, `H(s,0) = a`, `H(s,1) ∈ U`. -/
def FreeHomotopic (S : Set Y) (a : Y) (U : Set Y) (γ₁ γ₂ : C(I, Y)) : Prop :=
  ∃ H : C(I × I, Y), (∀ t, H (0, t) = γ₁ t) ∧ (∀ t, H (1, t) = γ₂ t) ∧ (∀ s, H (s, 0) = a) ∧
    (∀ s, H (s, 1) ∈ U) ∧ ∀ z, H z ∈ Sᶜ

variable {S : Set Y} {a : Y} {U : Set Y}

theorem freeHomotopic_refl {γ : C(I, Y)} (hγ : γ ∈ FreePath S a U) : FreeHomotopic S a U γ γ :=
  ⟨⟨fun z => γ z.2, by fun_prop⟩, fun _ => rfl, fun _ => rfl, fun _ => hγ.1, fun _ => hγ.2.2,
    fun z => hγ.2.1 z.2⟩

theorem FreeHomotopic.symm {γ₁ γ₂ : C(I, Y)} (h : FreeHomotopic S a U γ₁ γ₂) :
    FreeHomotopic S a U γ₂ γ₁ := by
  obtain ⟨H, h0, h1, ha, hU, hS⟩ := h
  refine ⟨⟨fun z => H (σ z.1, z.2), by fun_prop⟩, fun t => ?_, fun t => ?_, fun s => ha _,
    fun s => hU _, fun z => hS _⟩
  · show H (σ 0, t) = _; rw [unitInterval.symm_zero, h1]
  · show H (σ 1, t) = _; rw [unitInterval.symm_one, h0]

theorem FreeHomotopic.trans {γ₁ γ₂ γ₃ : C(I, Y)} (h : FreeHomotopic S a U γ₁ γ₂)
    (h' : FreeHomotopic S a U γ₂ γ₃) : FreeHomotopic S a U γ₁ γ₃ := by
  obtain ⟨H, h0, h1, ha, hU, hS⟩ := h
  obtain ⟨H', h0', h1', ha', hU', hS'⟩ := h'
  set pr : ℝ → I := Set.projIcc 0 1 zero_le_one
  let K : I × I → Y := fun z =>
    if (z.1 : ℝ) ≤ 1 / 2 then H (pr (2 * z.1), z.2) else H' (pr (2 * z.1 - 1), z.2)
  have hK : Continuous K := by
    refine Continuous.if_le (H.continuous.comp ((continuous_projIcc.comp (by fun_prop)).prodMk
      continuous_snd)) (H'.continuous.comp ((continuous_projIcc.comp (by fun_prop)).prodMk
      continuous_snd)) (by fun_prop) continuous_const fun z hz => ?_
    rw [hz]
    have e1 : pr (2 * (1 / 2 : ℝ)) = 1 := Subtype.ext (by simp [pr])
    have e2 : pr (2 * (1 / 2 : ℝ) - 1) = 0 := Subtype.ext (by simp [pr])
    rw [e1, e2, h1, h0']
  have hmem : ∀ z, K z = H (pr (2 * z.1), z.2) ∨ K z = H' (pr (2 * z.1 - 1), z.2) := fun z => by
    simp only [K]; split_ifs <;> simp
  refine ⟨⟨K, hK⟩, fun t => ?_, fun t => ?_, fun s => ?_, fun s => ?_, fun z => ?_⟩
  · show K (0, t) = _
    simp only [K, Icc.coe_zero, mul_zero, if_pos (show (0 : ℝ) ≤ 1 / 2 by norm_num)]
    rw [show pr 0 = 0 from Subtype.ext (by simp [pr]), h0]
  · show K (1, t) = _
    simp only [K, Icc.coe_one, if_neg (show ¬ (1 : ℝ) ≤ 1 / 2 by norm_num)]
    rw [show pr (2 * 1 - 1) = 1 from Subtype.ext (by norm_num [pr]), h1']
  · show K (s, 0) = a
    rcases hmem (s, 0) with h | h <;> rw [h]
    · exact ha _
    · exact ha' _
  · show K (s, 1) ∈ U
    rcases hmem (s, 1) with h | h <;> rw [h]
    · exact hU _
    · exact hU' _
  · show K z ∈ Sᶜ
    rcases hmem z with h | h <;> rw [h]
    · exact hS _
    · exact hS' _

theorem freeHomotopic_of_homotopicIn {c : Y} (hc : c ∈ U) {P Q : Path a c}
    (h : HomotopicIn Sᶜ P Q) : FreeHomotopic S a U P.toContinuousMap Q.toContinuousMap := by
  obtain ⟨F, hF⟩ := h
  exact ⟨F.toContinuousMap, F.apply_zero, F.apply_one, F.source, fun s => (F.target s).symm ▸ hc,
    hF⟩

/-- Moving the end back along a path of `U ∖ S`. -/
theorem freeHomotopic_trans_shrink {c d : Y} (P : Path a c) (hP : ∀ t, P t ∈ Sᶜ) (ω : Path c d)
    (hω : ∀ t, ω t ∈ U ∩ Sᶜ) :
    FreeHomotopic S a U (P.trans ω).toContinuousMap (P.trans (Path.refl c)).toContinuousMap := by
  set pr : ℝ → I := Set.projIcc 0 1 zero_le_one
  let K : I × I → Y := fun z =>
    if (z.2 : ℝ) ≤ 1 / 2 then P.extend (2 * z.2) else ω.extend ((1 - z.1) * (2 * z.2 - 1))
  have hK : Continuous K := by
    refine Continuous.if_le (by fun_prop) (by fun_prop) (by fun_prop) continuous_const
      fun z hz => ?_
    rw [hz]; simp
  have hK1 : ∀ z : I × I, (1 / 2 : ℝ) < z.2 → K z ∈ U ∩ Sᶜ := fun z hz => by
    simp only [K, if_neg (not_le.2 hz)]
    rw [ω.extend_apply ⟨by nlinarith [z.1.2.2, z.2.2.2], by nlinarith [z.1.2.1, z.2.2.2]⟩]
    exact hω _
  refine ⟨⟨K, hK⟩, fun t => ?_, fun t => ?_, fun s => ?_, fun s => ?_, fun z => ?_⟩
  · show K (0, t) = (P.trans ω) t
    simp only [K, Icc.coe_zero, sub_zero, one_mul, Path.trans_apply]
    split_ifs with h
    · rw [P.extend_apply]
    · rw [ω.extend_apply]
  · show K (1, t) = (P.trans (Path.refl c)) t
    simp only [K, Icc.coe_one, sub_self, zero_mul, Path.trans_apply]
    split_ifs with h
    · rw [P.extend_apply]
    · rw [ω.extend_zero]; rfl
  · show K (s, 0) = a
    simp [K]
  · exact (hK1 (s, 1) (by simp; norm_num)).1
  · show K z ∈ Sᶜ
    rcases le_or_gt (z.2 : ℝ) (1 / 2) with h | h
    · simp only [K, if_pos h]
      rw [P.extend_apply ⟨by linarith [z.2.2.1], by linarith⟩]; exact hP _
    · exact (hK1 z h).2

theorem freeHomotopic_equivalence :
    Equivalence fun γ₁ γ₂ : FreePath S a U => FreeHomotopic S a U γ₁.1 γ₂.1 :=
  ⟨fun γ => freeHomotopic_refl γ.2, fun h => h.symm, fun h h' => h.trans h'⟩

/-- **`π₁(a,U)`** (`RamcovGX.tex:1402`): paths of `Y ∖ S` with fixed start at `a` and free end in
`U`, up to homotopy (with free end in `U`); a discrete space. -/
def PiOneU (S : Set Y) (a : Y) (U : Set Y) : Type _ :=
  Quotient (⟨fun γ₁ γ₂ : FreePath S a U => FreeHomotopic S a U γ₁.1 γ₂.1,
    freeHomotopic_equivalence⟩ : Setoid (FreePath S a U))

instance : TopologicalSpace (PiOneU S a U) := ⊥

instance : DiscreteTopology (PiOneU S a U) := ⟨rfl⟩

/-- The natural map `π₁(a,U) → π₁(a,V)` for `U ⊆ V`. -/
def piOneUMap {V : Set Y} (hUV : U ⊆ V) : PiOneU S a U → PiOneU S a V :=
  Quotient.map (fun γ => ⟨γ.1, γ.2.1, γ.2.2.1, hUV γ.2.2.2⟩)
    fun _ _ ⟨H, h0, h1, ha, hU, hS⟩ => ⟨H, h0, h1, ha, fun s => hUV (hU s), hS⟩

end FreeHom

section FiberUniv

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space X] {p : X → Y}
  {S : Set Y} (cov : IsCoveringMap (Sᶜ.restrictPreimage p)) {a : Y} {â : X} (hâ : p â = a)

include cov hâ in
/-- A homotopy with free end in `U` lifts: free-end homotopic paths are `p`-homotopic (for any
covering over `Y ∖ S`). -/
theorem pHomotopic_of_freeHomotopic {U : Set Y} {γ₁ γ₂ : FreePath S a U}
    (h : FreeHomotopic S a U γ₁.1 γ₂.1) : PHomotopic p â U γ₁.1 γ₂.1 := by
  obtain ⟨H, h0, h1, ha, hU, hS⟩ := h
  let H' : C(I × I, (Sᶜ : Set Y)) := ⟨fun z => ⟨H (z.2, z.1), hS _⟩, by
    refine Continuous.subtype_mk ?_ _
    exact H.continuous.comp continuous_swap⟩
  have hâS : â ∈ p ⁻¹' Sᶜ := by show p â ∈ Sᶜ; rw [hâ, ← ha 0]; exact hS _
  let f : C(I, p ⁻¹' Sᶜ) := ContinuousMap.const _ ⟨â, hâS⟩
  have H_0 : ∀ s, H' (0, s) = Sᶜ.restrictPreimage p (f s) := fun s => Subtype.ext (by
    show H (s, 0) = p â
    rw [ha, hâ])
  set Hl := cov.liftHomotopy H' f H_0
  have hlift : ∀ z : I × I, p (Hl z) = H (z.2, z.1) := fun z =>
    congrArg Subtype.val (congrFun (cov.liftHomotopy_lifts H' f H_0) z)
  let Γ₁ : C(I, X) := ⟨fun t => (Hl (t, 0) : X),
    continuous_subtype_val.comp (Hl.continuous.comp (continuous_id.prodMk continuous_const))⟩
  let Γ₂ : C(I, X) := ⟨fun t => (Hl (t, 1) : X),
    continuous_subtype_val.comp (Hl.continuous.comp (continuous_id.prodMk continuous_const))⟩
  refine ⟨Γ₁, Γ₂, fun t => by show p (Hl (t, 0)) = _; rw [hlift, h0],
    fun t => by show p (Hl (t, 1)) = _; rw [hlift, h1],
    by show (Hl (0, 0) : X) = â; rw [cov.liftHomotopy_zero]; rfl,
    by show (Hl (0, 1) : X) = â; rw [cov.liftHomotopy_zero]; rfl, ?_⟩
  have hr : range (fun s : I => (Hl (1, s) : X)) ⊆ connectedComponentIn (p ⁻¹' U) (Γ₁ 1) :=
    (isPreconnected_range (continuous_subtype_val.comp (Hl.continuous.comp
      (continuous_const.prodMk continuous_id)))).subset_connectedComponentIn
      ⟨0, rfl⟩ (by rintro _ ⟨s, rfl⟩; show p (Hl (1, s)) ∈ U; rw [hlift]; exact hU s)
  exact connectedComponentIn_eq (hr ⟨1, rfl⟩)

include hâ in
/-- Conversely, over a simply connected part over `Y ∖ S`, `p`-homotopic paths are homotopic
with free end in `U`. -/
theorem freeHomotopic_of_pHomotopic [LocPathConnectedSpace X] (hp : IsBranchedCovering p)
    (hS : IsSkeletal S) [SimplyConnectedSpace (p ⁻¹' Sᶜ)] {U : Set Y} (hU : IsOpen U)
    {γ₁ γ₂ : FreePath S a U} (h : PHomotopic p â U γ₁.1 γ₂.1) :
    FreeHomotopic S a U γ₁.1 γ₂.1 := by
  obtain ⟨Γ₁, Γ₂, hΓ₁, hΓ₂, h₁0, h₂0, hc⟩ := h
  have hpc : Continuous p := hp.isSpread.continuous
  have hE : IsPortly (p ⁻¹' Sᶜ) := hp.isPortly_preimage hS
  set C := connectedComponentIn (p ⁻¹' U) (Γ₁ 1)
  have hCo : IsOpen C := (hU.preimage hpc).connectedComponentIn
  have hΓ₁U : Γ₁ 1 ∈ p ⁻¹' U := by show p (Γ₁ 1) ∈ U; rw [hΓ₁]; exact γ₁.2.2.2
  have hΓ₂U : Γ₂ 1 ∈ p ⁻¹' U := by show p (Γ₂ 1) ∈ U; rw [hΓ₂]; exact γ₂.2.2.2
  have h1C : Γ₁ 1 ∈ C := mem_connectedComponentIn hΓ₁U
  have h2C : Γ₂ 1 ∈ C := by rw [hc]; exact mem_connectedComponentIn hΓ₂U
  have hpath : IsPathConnected (C ∩ p ⁻¹' Sᶜ) :=
    (hCo.inter hE.isOpen).isConnected_iff_isPathConnected.1
      (hE.isConnected_inter hCo ⟨⟨_, h1C⟩, isPreconnected_connectedComponentIn⟩)
  have hE₁ : Γ₁ 1 ∈ p ⁻¹' Sᶜ := by show p (Γ₁ 1) ∈ Sᶜ; rw [hΓ₁]; exact γ₁.2.2.1 1
  have hE₂ : Γ₂ 1 ∈ p ⁻¹' Sᶜ := by show p (Γ₂ 1) ∈ Sᶜ; rw [hΓ₂]; exact γ₂.2.2.1 1
  obtain ⟨ωt, hωt⟩ := hpath.joinedIn _ ⟨h2C, hE₂⟩ _ ⟨h1C, hE₁⟩
  set P₁ : Path â (Γ₁ 1) := ⟨Γ₁, h₁0, rfl⟩
  set P₂ : Path â (Γ₂ 1) := ⟨Γ₂, h₂0, rfl⟩
  have hP₁ : ∀ t, P₁ t ∈ p ⁻¹' Sᶜ := fun t => by
    show p (Γ₁ t) ∈ Sᶜ; rw [hΓ₁]; exact γ₁.2.2.1 t
  have hP₂ : ∀ t, P₂ t ∈ p ⁻¹' Sᶜ := fun t => by
    show p (Γ₂ t) ∈ Sᶜ; rw [hΓ₂]; exact γ₂.2.2.1 t
  have hhom : HomotopicIn (p ⁻¹' Sᶜ) P₁ (P₂.trans ωt) := homotopicIn_iff.2
    ⟨hP₁, path_trans_mem hP₂ fun t => (hωt t).2, SimplyConnectedSpace.paths_homotopic _ _⟩
  have hmap := (hhom.map hpc fun z hz => hz).cast hâ.symm rfl
  set Q : Path a (p (Γ₂ 1)) := (P₂.map hpc).cast hâ.symm rfl
  set ω : Path (p (Γ₂ 1)) (p (Γ₁ 1)) := ωt.map hpc
  have hQ : ∀ t, Q t ∈ Sᶜ := fun t => hP₂ t
  have hω : ∀ t, ω t ∈ U ∩ Sᶜ := fun t =>
    ⟨(connectedComponentIn_subset (p ⁻¹' U) _ (hωt t).1 : ωt t ∈ p ⁻¹' U), (hωt t).2⟩
  have e₁ : ((P₁.map hpc).cast hâ.symm rfl).toContinuousMap = γ₁.1 := ContinuousMap.ext hΓ₁
  have e₂ : (((P₂.trans ωt).map hpc).cast hâ.symm rfl) = Q.trans ω := by
    ext t
    simp only [Path.cast_coe, Path.map_coe, comp_apply, Path.trans_apply, Q, ω]
    split_ifs <;> rfl
  have eQ : Q.toContinuousMap = γ₂.1 := ContinuousMap.ext hΓ₂
  have step1 := freeHomotopic_of_homotopicIn (S := S) hΓ₁U hmap
  rw [e₁, e₂] at step1
  have step2 := freeHomotopic_trans_shrink Q hQ ω hω
  have step3 : FreeHomotopic S a U (Q.trans (Path.refl _)).toContinuousMap Q.toContinuousMap := by
    refine freeHomotopic_of_homotopicIn (show p (Γ₂ 1) ∈ U from hΓ₂U) ?_
    have hr : ∀ t, (Path.refl (p (Γ₂ 1))) t ∈ Sᶜ := fun _ => hQ 1
    refine homotopicIn_iff.2 ⟨path_trans_mem hQ hr, hQ, ?_⟩
    rw [pathToSub_trans _ _ hQ hr]
    have : pathToSub (Path.refl (p (Γ₂ 1))) hr = Path.refl _ := by ext; rfl
    rw [this]
    exact Path.Homotopic.trans_refl _
  rw [eQ] at step3
  exact step1.trans (step2.trans step3)

end FiberUniv

section FiberUniv2

universe u

variable {Y : Type u} [TopologicalSpace Y] [T2Space Y] [LocPathConnectedSpace Y]
  [FirstCountableTopology Y] [ConnectedSpace Y] {S : Set Y}

/-- **`prop:general_fiber_path_universal`** (`RamcovGX.tex:1399`). For `\widetilde Y^S → Y` (`S`
skeletal, `Y ∖ S` semilocally simply connected), `a ∈ Y ∖ S`, `â` over `a`, every `b ∈ Y` and every
basis `𝓤` of connected open neighbourhoods of `b`, the natural map
`p⁻¹(b) → ∏_{U ∈ 𝓤} π₁(a,U)` (a class goes to `x` when its lift from `â` ends in the component of
`x` in `p⁻¹(U)`) is an embedding (`π₁(a,U)` discrete) onto `lim_{U ∈ 𝓤} π₁(a,U)`. -/
theorem general_fiber_path_universal (hS : IsSkeletal S)
    (hSc : SemilocallySimplyConnected (Sᶜ : Set Y)) (y₀ : (Sᶜ : Set Y)) {a : Y} (haS : a ∈ Sᶜ)
    {â : MaxBranchedCover S y₀} (hâ : â.base = a) {b : Y} (𝓤 : Set (Set Y))
    (h𝓤 : ∀ U ∈ 𝓤, IsCNbhd b U) (hbasis : ∀ N ∈ 𝓝 b, ∃ U ∈ 𝓤, U ⊆ N) :
    ∃ Φ : (SpreadEnd.base : MaxBranchedCover S y₀ → Y) ⁻¹' {b} → ∀ U : 𝓤, PiOneU S a U,
      (∀ (x : (SpreadEnd.base : MaxBranchedCover S y₀ → Y) ⁻¹' {b}) (U : 𝓤) (γ : FreePath S a U)
        (Γ : C(I, MaxBranchedCover S y₀)), (∀ t, (Γ t).base = γ.1 t) → Γ 0 = â →
          Γ 1 ∈ connectedComponentIn ((SpreadEnd.base : MaxBranchedCover S y₀ → Y) ⁻¹' U)
            (x : MaxBranchedCover S y₀) →
          Φ x U = Quotient.mk _ γ) ∧
      IsEmbedding Φ ∧
      range Φ = {f | ∀ U V : 𝓤, ∀ h : (U : Set Y) ⊆ V, piOneUMap h (f U) = f V} := by
  obtain ⟨-, hbc, -, -, hl, -⟩ := maxBranched_basic hS hSc y₀
  haveI := hl
  obtain ⟨cov, hsc⟩ := maxBranched_lifting hS hSc y₀
  haveI := hsc
  obtain ⟨Φ', hΦ', hemb, hrange⟩ := general_fiber_path cov hâ hbc hS haS 𝓤 h𝓤 hbasis
  have hiff : ∀ (U : 𝓤) (γ₁ γ₂ : FreePath S a U),
      PHomotopic SpreadEnd.base â U γ₁.1 γ₂.1 ↔ FreeHomotopic S a U γ₁.1 γ₂.1 := fun U γ₁ γ₂ =>
    ⟨freeHomotopic_of_pHomotopic hâ hbc hS (h𝓤 U U.2).isOpen,
      pHomotopic_of_freeHomotopic cov hâ⟩
  let e : ∀ U : 𝓤, PiOneP cov hâ U ≃ PiOneU S a U := fun U =>
    Quotient.congr (Equiv.refl _) (hiff U)
  let eh : ∀ U : 𝓤, PiOneP cov hâ U ≃ₜ PiOneU S a U := fun U =>
    { toEquiv := e U
      continuous_toFun := continuous_of_discreteTopology
      continuous_invFun := continuous_of_discreteTopology }
  set Θ := Homeomorph.piCongrRight eh
  have hΘ : ∀ f U, Θ f U = e U (f U) := fun _ _ => rfl
  have hcomm : ∀ (U V : 𝓤) (h : (U : Set Y) ⊆ V) (c : PiOneP cov hâ U),
      piOneUMap h (e U c) = e V (piOnePMap cov hâ h c) := by
    intro U V h c
    induction c using Quotient.inductionOn with | h γ => rfl
  refine ⟨Θ ∘ Φ', fun x U γ Γ hΓ h0 hx => ?_, Θ.isEmbedding.comp hemb, ?_⟩
  · show e U (Φ' x U) = _
    have : Φ' x U = Quotient.mk (pSetoid cov hâ U) γ := by
      apply compOfClass_injective cov hâ U
      rw [hΦ' x U, compOfClass_mk cov hâ γ hΓ h0, connectedComponentIn_eq hx]
    rw [this]; rfl
  · ext f
    constructor
    · rintro ⟨x, rfl⟩ U V h
      have hx : Φ' x ∈ range Φ' := ⟨x, rfl⟩
      rw [hrange] at hx
      simp only [comp_apply, hΘ, hcomm, hx U V h]
    · intro hf
      have hf' : Θ.symm f ∈ range Φ' := by
        rw [hrange]
        intro U V h
        apply (e V).injective
        have h1 := hf U V h
        have h2 : f = Θ (Θ.symm f) := (Θ.apply_symm_apply f).symm
        rw [h2] at h1
        simp only [hΘ] at h1
        rw [← hcomm, h1]
      obtain ⟨x, hx⟩ := hf'
      exact ⟨x, by simp only [comp_apply, hx, Θ.apply_symm_apply]⟩

end FiberUniv2

/-! ### Standard neighbourhoods (the reading of `RamcovGX.tex:1311`) -/

section Standard

variable {E Y : Type*} [TopologicalSpace E] [TopologicalSpace Y]

/-- A *standard neighbourhood* of `e` for a spread `p` (undefined in the paper,
`RamcovGX.tex:1311`; the reading taken): the connected component containing `e` of `p⁻¹(V)`,
`V` an open connected neighbourhood of `p(e)`. -/
def IsStandardNbhd (p : E → Y) (e : E) (W : Set E) : Prop :=
  ∃ V, IsCNbhd (p e) V ∧ W = connectedComponentIn (p ⁻¹' V) e

/-- For a spread over a locally connected base, standard neighbourhoods are open and form a basis
of neighbourhoods. -/
theorem IsSpread.hasBasis_standardNbhd [LocallyConnectedSpace Y] {p : E → Y} (hp : IsSpread p)
    (e : E) : (𝓝 e).HasBasis (IsStandardNbhd p e) id := by
  haveI := hp.locallyConnectedSpace
  have hopen : ∀ W, IsStandardNbhd p e W → IsOpen W := by
    rintro W ⟨V, hV, rfl⟩
    exact (hV.isOpen.preimage hp.continuous).connectedComponentIn
  have hmem : ∀ W, IsStandardNbhd p e W → e ∈ W := by
    rintro W ⟨V, hV, rfl⟩
    exact mem_connectedComponentIn (show p e ∈ V from hV.mem)
  refine ⟨fun N => ⟨fun hN => ?_, fun ⟨W, hW, hWN⟩ => mem_of_superset
    ((hopen W hW).mem_nhds (hmem W hW)) hWN⟩⟩
  obtain ⟨O, hON, hO, heO⟩ := mem_nhds_iff.1 hN
  obtain ⟨V, hV, hpV, hVO⟩ := (isSpread_iff.1 hp).2.2 e O hO heO
  refine ⟨connectedComponentIn (p ⁻¹' connectedComponentIn V (p e)) e,
    ⟨connectedComponentIn V (p e), ⟨hV.connectedComponentIn, isPreconnected_connectedComponentIn,
      mem_connectedComponentIn hpV⟩, rfl⟩, ?_⟩
  exact ((connectedComponentIn_mono _ (preimage_mono (connectedComponentIn_subset _ _))).trans
    hVO).trans hON

end Standard

/-! ### `ex:consider_carthesian_coordinates_usual` -/

section Trivial

variable {U : Set X} {x : X}

/-- `γ ∈ Ω(x,x,U)` is *homotopically trivial* (the reading of `RamcovGX.tex:1218–1220`): a
homotopy with fixed ends to the constant loop through loops of `Ω(x,x,U)`, the constant loop
being reached only at the end. -/
def IsHomTrivial (U : Set X) {x : X} (γ : Path x x) : Prop :=
  ∃ F : Path.Homotopy γ (Path.refl x), ∀ s t : I, (s : ℝ) < 1 → 0 < (t : ℝ) → (t : ℝ) < 1 →
    F (s, t) ∈ U

/-- "homotopically trivial hence almost trivial" (`RamcovGX.tex:1219`). -/
theorem IsHomTrivial.almostTrivial {γ : Path x x} (hγ : MemOmega U γ) (h : IsHomTrivial U γ) :
    AlmostTrivial U γ := by
  obtain ⟨F, hF⟩ := h
  refine ⟨hγ, fun V hV => ?_⟩
  obtain ⟨V', hV'V, hV', hxV'⟩ := mem_nhds_iff.1 hV
  have hP : ∀ t ∈ (univ : Set I), ∀ᶠ z : I × I in 𝓝 (1, t), F z ∈ V' := fun t _ =>
    F.continuous.continuousAt.preimage_mem_nhds (hV'.mem_nhds (by
      rw [F.apply_one]; exact hxV'))
  obtain ⟨ε, hε, hεV⟩ := Metric.eventually_nhds_iff.1
    (isCompact_univ.eventually_forall_of_forall_eventually (P := fun s t => F (s, t) ∈ V') hP)
  set s₀ : I := ⟨max 0 (1 - ε / 2), le_max_left _ _, max_le zero_le_one (by linarith)⟩
  have hs₀ : (s₀ : ℝ) < 1 := max_lt zero_lt_one (by linarith)
  have hs₀V : ∀ t, F (s₀, t) ∈ V' := fun t => hεV (by
    have e : (s₀ : ℝ) = max 0 (1 - ε / 2) := rfl
    rw [Subtype.dist_eq, Icc.coe_one, Real.dist_eq, abs_of_nonpos (by linarith), e]
    linarith [le_max_right (0 : ℝ) (1 - ε / 2)]) t (mem_univ t)
  refine ⟨F.eval s₀, fun t h0 h1 => ⟨hV'V (hs₀V t), hF s₀ t hs₀ h0 h1⟩, ?_⟩
  refine ⟨{ toFun := fun z => F (z.1 * s₀, z.2)
            continuous_toFun := F.continuous.comp ((continuous_fst.mul continuous_const).prodMk
              continuous_snd)
            map_zero_left := fun t => by simp
            map_one_left := fun t => by simp [Path.Homotopy.eval]
            prop' := fun s t ht => by
              rcases ht with rfl | rfl
              · simp
              · simp }, fun s t h0 h1 => ?_⟩
  exact hF _ t (by
    show ((s * s₀ : I) : ℝ) < 1
    rw [Set.Icc.coe_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left s₀.2.1 s.2.2) hs₀) h0 h1

/-- "homotopically trivial hence almost trivial" (`RamcovGX.tex:1219`), in the literal reading
of `def:almost_trivial_loop` (DEC-55). -/
theorem IsHomTrivial.almostTrivialCC {γ : Path x x} (hγ : MemOmega U γ) (h : IsHomTrivial U γ) :
    AlmostTrivialCC U γ :=
  (h.almostTrivial hγ).almostTrivialCC

end Trivial

section Winding

/-- `ℂ ∖ {0}` as a subtype. -/
abbrev CStar : Type := {w : ℂ // w ≠ 0}

/-- `exp : ℂ → ℂ ∖ {0}`. -/
def cExp : C(ℂ, CStar) := ⟨fun z => ⟨Complex.exp z, Complex.exp_ne_zero z⟩, by fun_prop⟩

theorem cExp_apply (z : ℂ) : ((cExp z : CStar) : ℂ) = Complex.exp z := rfl

theorem isCoveringMap_cExp : IsCoveringMap (cExp : ℂ → CStar) := Complex.isCoveringMap_exp

/-- Two lifts through `exp` of the same path differ by a constant. -/
theorem expLift_sub_const {Γ Γ' : C(I, ℂ)} (h : ∀ t, Complex.exp (Γ t) = Complex.exp (Γ' t))
    (t : I) : Γ' t = Γ t + (Γ' 0 - Γ 0) := by
  have hc : Complex.exp (Γ' 0 - Γ 0) = 1 := by
    rw [Complex.exp_sub, ← h 0, div_self (Complex.exp_ne_zero _)]
  have := isCoveringMap_cExp.eq_of_comp_eq (g₁ := fun t => Γ t + (Γ' 0 - Γ 0)) (g₂ := Γ')
    (by fun_prop) Γ'.continuous (funext fun t => Subtype.ext (by
      simp only [comp_apply, cExp_apply, Complex.exp_add, hc, mul_one, h t])) 0 (by ring)
  exact (congrFun this t).symm

/-- Every path of `ℂ ∖ {0}` lifts through `exp`. -/
theorem exists_expLift (δ : C(I, CStar)) : ∃ Γ : C(I, ℂ), ∀ t, Complex.exp (Γ t) = δ t := by
  obtain ⟨Γ, hΓ, -⟩ := isCoveringMap_cExp.exists_path_lifts δ (Complex.log (δ 0))
    (Subtype.ext (Complex.exp_log (δ 0).2).symm)
  exact ⟨Γ, fun t => congrArg Subtype.val (congrFun hΓ t)⟩

theorem exists_int_winding {z : CStar} (δ : Path z z) :
    ∃ n : ℤ, ∀ Γ : C(I, ℂ), (∀ t, Complex.exp (Γ t) = δ t) →
      Γ 1 = Γ 0 + n * (2 * Real.pi * Complex.I) := by
  obtain ⟨Γ₀, hΓ₀⟩ := exists_expLift δ.toContinuousMap
  have h01 : Complex.exp (Γ₀ 1) = Complex.exp (Γ₀ 0) := by
    rw [hΓ₀, hΓ₀]; simp
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 h01
  refine ⟨n, fun Γ hΓ => ?_⟩
  have h := expLift_sub_const (Γ := Γ₀) (Γ' := Γ) (fun t => by rw [hΓ₀ t, hΓ t]; rfl)
  rw [h 1, hn, h 0]; ring

/-- The winding number of a loop of `ℂ ∖ {0}` (through any lift by `exp`). -/
def cWinding {z : CStar} (δ : Path z z) : ℤ := (exists_int_winding δ).choose

theorem cWinding_spec {z : CStar} (δ : Path z z) {Γ : C(I, ℂ)}
    (hΓ : ∀ t, Complex.exp (Γ t) = δ t) :
    Γ 1 = Γ 0 + cWinding δ * (2 * Real.pi * Complex.I) :=
  (exists_int_winding δ).choose_spec Γ hΓ

theorem cWinding_eq {z : CStar} (δ : Path z z) {Γ : C(I, ℂ)}
    (hΓ : ∀ t, Complex.exp (Γ t) = δ t) {n : ℤ} (hn : Γ 1 = Γ 0 + n * (2 * Real.pi * Complex.I)) :
    cWinding δ = n := by
  have h := cWinding_spec δ hΓ
  rw [hn] at h
  have h' : ((n : ℂ) - cWinding δ) * (2 * Real.pi * Complex.I) = 0 := by linear_combination h
  rcases mul_eq_zero.1 h' with h'' | h''
  · exact_mod_cast (sub_eq_zero.1 h'').symm
  · exact absurd h'' Complex.two_pi_I_ne_zero

theorem cWinding_homotopic {z : CStar} {δ δ' : Path z z} (h : δ.Homotopic δ') :
    cWinding δ = cWinding δ' := by
  obtain ⟨H⟩ := h
  have hrel : δ.toContinuousMap.HomotopicRel δ'.toContinuousMap {0, 1} := ⟨H⟩
  have h0 : δ.toContinuousMap 0 = cExp (Complex.log z) :=
    Subtype.ext (by simp [cExp_apply, Complex.exp_log z.2])
  have h0' : δ'.toContinuousMap 0 = cExp (Complex.log z) :=
    Subtype.ext (by simp [cExp_apply, Complex.exp_log z.2])
  have key := isCoveringMap_cExp.liftPath_apply_one_eq_of_homotopicRel hrel _ h0 h0'
  set Γ := isCoveringMap_cExp.liftPath δ.toContinuousMap _ h0
  set Γ' := isCoveringMap_cExp.liftPath δ'.toContinuousMap _ h0'
  have hΓ : ∀ t, Complex.exp (Γ t) = δ t := fun t =>
    congrArg Subtype.val (congrFun (isCoveringMap_cExp.liftPath_lifts δ.toContinuousMap _ h0) t)
  have hΓ' : ∀ t, Complex.exp (Γ' t) = δ' t := fun t =>
    congrArg Subtype.val (congrFun (isCoveringMap_cExp.liftPath_lifts δ'.toContinuousMap _ h0') t)
  have e0 : Γ 0 = Γ' 0 := by
    rw [isCoveringMap_cExp.liftPath_zero, isCoveringMap_cExp.liftPath_zero]
  refine (cWinding_eq δ' hΓ' ?_).symm
  rw [← key, ← e0]
  exact cWinding_spec δ hΓ

theorem cWinding_trans {z : CStar} (δ₁ δ₂ : Path z z) :
    cWinding (δ₁.trans δ₂) = cWinding δ₁ + cWinding δ₂ := by
  obtain ⟨Γ₁, hΓ₁⟩ := exists_expLift δ₁.toContinuousMap
  obtain ⟨Γ₂, hΓ₂⟩ := exists_expLift δ₂.toContinuousMap
  have e1 := cWinding_spec δ₁ hΓ₁
  have e2 := cWinding_spec δ₂ hΓ₂
  set c := Γ₁ 1 - Γ₂ 0
  have hc : Complex.exp c = 1 := by
    rw [Complex.exp_sub, hΓ₁, hΓ₂]
    simp [div_self z.2]
  let P₁ : Path (Γ₁ 0) (Γ₁ 1) := ⟨Γ₁, rfl, rfl⟩
  let P₂ : Path (Γ₁ 1) (Γ₂ 1 + c) :=
    ⟨⟨fun t => Γ₂ t + c, by fun_prop⟩, by simp [c], rfl⟩
  have hP : ∀ t, Complex.exp ((P₁.trans P₂) t) = (δ₁.trans δ₂) t := by
    intro t
    rw [Path.trans_apply, Path.trans_apply]
    split_ifs
    · exact hΓ₁ _
    · show Complex.exp (Γ₂ _ + c) = _
      rw [Complex.exp_add, hc, mul_one, hΓ₂]; rfl
  refine cWinding_eq _ (Γ := (P₁.trans P₂).toContinuousMap) hP ?_
  show (P₁.trans P₂) 1 = (P₁.trans P₂) 0 + _
  rw [Path.target, Path.source]
  push_cast
  rw [show Γ₂ 1 + c = Γ₂ 1 - Γ₂ 0 + Γ₁ 1 by ring, e2, e1]; ring

/-- The loop `t ↦ z e^{2πint}` of `ℂ ∖ {0}`. -/
def cLoop (z : CStar) (n : ℤ) : Path z z where
  toFun t := ⟨z * Complex.exp (n * (2 * Real.pi * Complex.I) * (t : ℝ)),
    mul_ne_zero z.2 (Complex.exp_ne_zero _)⟩
  continuous_toFun := by fun_prop
  source' := Subtype.ext (by simp)
  target' := Subtype.ext (by simp [Complex.exp_int_mul_two_pi_mul_I])

theorem cWinding_cLoop (z : CStar) (n : ℤ) : cWinding (cLoop z n) = n := by
  refine cWinding_eq _ (Γ := ⟨fun t => Complex.log z + n * (2 * Real.pi * Complex.I) * (t : ℝ),
    by fun_prop⟩) (fun t => ?_) (by simp)
  show Complex.exp (Complex.log z + _) = z * _
  rw [Complex.exp_add, Complex.exp_log z.2]

theorem homotopic_refl_of_cWinding_eq_zero {z : CStar} (δ : Path z z) (h : cWinding δ = 0) :
    δ.Homotopic (Path.refl z) := by
  obtain ⟨Γ, hΓ⟩ := exists_expLift δ.toContinuousMap
  have e := cWinding_spec δ hΓ
  rw [h] at e
  simp only [Int.cast_zero, zero_mul, add_zero] at e
  let P : Path (Γ 0) (Γ 0) := ⟨Γ, rfl, e⟩
  have hz : cExp (Γ 0) = z := Subtype.ext (by rw [cExp_apply, hΓ 0]; simp)
  subst hz
  have h1 := Path.Homotopic.map (⟨lineHomotopy P (Path.refl (Γ 0))⟩ : P.Homotopic (Path.refl (Γ 0))) cExp
  have hm : P.map cExp.continuous = δ := by
    ext t; show Complex.exp (Γ t) = _; rw [hΓ t]; rfl
  have hr : (Path.refl (Γ 0)).map cExp.continuous = Path.refl (cExp (Γ 0)) := by
    ext t; rfl
  rw [← hm, ← hr]
  exact h1

end Winding

section Carthesian

/-- `O`, the origin of `ℝ³` (`RamcovGX.tex:1217`). -/
abbrev cartO : ℝ × ℝ × ℝ := (0, 0, 0)

/-- `S₁ = {y = z = 0}` (`RamcovGX.tex:1216`). -/
def cartS₁ : Set (ℝ × ℝ × ℝ) := {q | q.2.1 = 0 ∧ q.2.2 = 0}

/-- `S₂`, the topologist's sine curve in the plane `{z = 0}` and its limit segment
(`RamcovGX.tex:1216`, with `z = 0` on the graph: DEC-68 (a)). -/
def cartS₂ : Set (ℝ × ℝ × ℝ) :=
  {q | q.1 ≠ 0 ∧ q.2.1 = Real.sin (1 / q.1) ∧ q.2.2 = 0} ∪ {q | q.1 = 0 ∧ q.2.2 = 0 ∧ |q.2.1| ≤ 1}

theorem cartO_mem_cartS₁ : cartO ∈ cartS₁ := ⟨rfl, rfl⟩

theorem cartO_mem_cartS₂ : cartO ∈ cartS₂ := Or.inr ⟨rfl, rfl, by simp⟩

/-- `ex:consider_carthesian_coordinates_usual`, second claim (`RamcovGX.tex:1219`): every loop of
`Ω(O,O,Y ∖ S₁)` is homotopically trivial (by the radial contraction: `S₁` is a cone at `O`),
hence almost trivial. -/
theorem carthesian_S₁_trivial {γ : Path cartO cartO} (hγ : MemOmega cartS₁ᶜ γ) :
    IsHomTrivial cartS₁ᶜ γ ∧ AlmostTrivialCC cartS₁ᶜ γ := by
  have h : IsHomTrivial cartS₁ᶜ γ := by
    refine ⟨{ toFun := fun z => (1 - (z.1 : ℝ)) • γ z.2
              continuous_toFun := by fun_prop
              map_zero_left := fun t => by simp
              map_one_left := fun t => by simp; rfl
              prop' := fun s t ht => by
                rcases ht with rfl | rfl
                · simp
                · simp }, fun s t hs h0 h1 => ?_⟩
    have hγt := hγ t h0 h1
    have hne : (1 - (s : ℝ)) ≠ 0 := by linarith
    show (1 - (s : ℝ)) • γ t ∉ cartS₁
    rintro ⟨h2, h3⟩
    apply hγt
    simp only [Prod.smul_snd, Prod.smul_fst, smul_eq_mul, mul_eq_zero, hne, false_or] at h2 h3
    exact ⟨h2, h3⟩
  exact ⟨h, h.almostTrivialCC hγ⟩

/-- `ex:consider_carthesian_coordinates_usual`, first claim (`RamcovGX.tex:1218`), as a `Prop`:
`π₁(Y ∖ S) ≅ ℤ`. -/
def CartPiOneZ (S : Set (ℝ × ℝ × ℝ)) : Prop :=
  ∀ y : (Sᶜ : Set (ℝ × ℝ × ℝ)), Nonempty (FundamentalGroup (Sᶜ : Set (ℝ × ℝ × ℝ)) y ≃* Multiplicative ℤ)

theorem cart_ne_zero (q : (cartS₁ᶜ : Set (ℝ × ℝ × ℝ))) :
    ((q.1.2.1 : ℂ) + q.1.2.2 * Complex.I) ≠ 0 := fun h => q.2
  ⟨by simpa using congrArg Complex.re h, by simpa using congrArg Complex.im h⟩

/-- `(x, y, z) ↦ y + iz`, from `ℝ³ ∖ S₁` to `ℂ ∖ {0}`. -/
def cartF : C((cartS₁ᶜ : Set (ℝ × ℝ × ℝ)), CStar) :=
  ⟨fun q => ⟨(q.1.2.1 : ℂ) + q.1.2.2 * Complex.I, cart_ne_zero q⟩, by fun_prop⟩

theorem cartF_re (q : (cartS₁ᶜ : Set (ℝ × ℝ × ℝ))) : ((cartF q : CStar) : ℂ).re = q.1.2.1 := by
  simp [cartF]

theorem cartF_im (q : (cartS₁ᶜ : Set (ℝ × ℝ × ℝ))) : ((cartF q : CStar) : ℂ).im = q.1.2.2 := by
  simp [cartF]

theorem not_mem_cartS₁_of_ne_zero (x : ℝ) (w : CStar) :
    (x, (w : ℂ).re, (w : ℂ).im) ∈ (cartS₁ᶜ : Set (ℝ × ℝ × ℝ)) := fun h =>
  w.2 (Complex.ext h.1 h.2)

/-- The winding number around `S₁`, a homomorphism `π₁(ℝ³ ∖ S₁, y) → ℤ`. -/
def cartDeg (y : (cartS₁ᶜ : Set (ℝ × ℝ × ℝ))) :
    FundamentalGroup (cartS₁ᶜ : Set (ℝ × ℝ × ℝ)) y →* Multiplicative ℤ where
  toFun g := Multiplicative.ofAdd (Quotient.lift (fun γ : Path y y => cWinding (γ.map cartF.continuous))
    (fun _ _ h => cWinding_homotopic (Path.Homotopic.map h cartF)) (FundamentalGroup.toPath g))
  map_one' := by
    show Multiplicative.ofAdd (cWinding ((Path.refl y).map cartF.continuous)) = 1
    rw [show cWinding ((Path.refl y).map cartF.continuous) = 0 from
      cWinding_eq _ (Γ := ContinuousMap.const I (Complex.log (cartF y)))
        (fun t => by simp [Complex.exp_log (cartF y).2]) (by simp)]
    rfl
  map_mul' a b := by
    show Multiplicative.ofAdd (Quotient.lift _ _ ((FundamentalGroup.toPath b).trans
      (FundamentalGroup.toPath a))) = Multiplicative.ofAdd (Quotient.lift _ _ _) *
        Multiplicative.ofAdd (Quotient.lift _ _ _)
    induction FundamentalGroup.toPath a using Quotient.inductionOn with | h α =>
    induction FundamentalGroup.toPath b using Quotient.inductionOn with | h β =>
    show Multiplicative.ofAdd (cWinding ((β.trans α).map cartF.continuous)) =
      Multiplicative.ofAdd (cWinding (α.map cartF.continuous)) *
        Multiplicative.ofAdd (cWinding (β.map cartF.continuous))
    rw [Path.map_trans, cWinding_trans, ← ofAdd_add, add_comm]

theorem cartDeg_mk (y : (cartS₁ᶜ : Set (ℝ × ℝ × ℝ))) (γ : Path y y) :
    cartDeg y (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ)) =
      Multiplicative.ofAdd (cWinding (γ.map cartF.continuous)) := rfl

theorem cartDeg_bijective (y : (cartS₁ᶜ : Set (ℝ × ℝ × ℝ))) : Bijective (cartDeg y) := by
  constructor
  · rw [injective_iff_map_eq_one]
    intro g hg
    induction g using Quotient.inductionOn with | h γ =>
    have h0 : cWinding (γ.map cartF.continuous) = 0 := by
      have := hg
      rw [show (Quotient.mk _ γ : FundamentalGroup _ y) =
        FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ) from rfl, cartDeg_mk] at this
      exact Multiplicative.ofAdd.injective this
    obtain ⟨G⟩ := homotopic_refl_of_cWinding_eq_zero _ h0
    let F : Path.Homotopy γ (Path.refl y) :=
      { toFun := fun w => ⟨((1 - (w.1 : ℝ)) * (γ w.2).1.1 + (w.1 : ℝ) * y.1.1,
            ((G w : CStar) : ℂ).re, ((G w : CStar) : ℂ).im), not_mem_cartS₁_of_ne_zero _ _⟩
        continuous_toFun := by
          refine Continuous.subtype_mk ?_ _
          have hG : Continuous fun w => ((G w : CStar) : ℂ) :=
            continuous_subtype_val.comp G.continuous
          refine Continuous.prodMk ?_ (Continuous.prodMk ?_ ?_)
          · have : Continuous fun w : I × I => (γ w.2).1.1 :=
              continuous_fst.comp (continuous_subtype_val.comp (γ.continuous.comp continuous_snd))
            fun_prop
          · exact Complex.continuous_re.comp hG
          · exact Complex.continuous_im.comp hG
        map_zero_left := fun t => by
          have h : G (0, t) = cartF (γ t) := G.apply_zero t
          apply Subtype.ext
          show ((1 - ((0 : I) : ℝ)) * (γ t).1.1 + ((0 : I) : ℝ) * y.1.1,
            ((G (0, t) : CStar) : ℂ).re, ((G (0, t) : CStar) : ℂ).im) = (γ t).1
          rw [h, cartF_re, cartF_im]; simp
        map_one_left := fun t => by
          have h : G (1, t) = cartF y := G.apply_one t
          apply Subtype.ext
          show ((1 - ((1 : I) : ℝ)) * (γ t).1.1 + ((1 : I) : ℝ) * y.1.1,
            ((G (1, t) : CStar) : ℂ).re, ((G (1, t) : CStar) : ℂ).im) = y.1
          rw [h, cartF_re, cartF_im]; simp
        prop' := fun s t ht => by
          apply Subtype.ext
          have hγt : γ t = y := by rcases ht with rfl | rfl <;> simp
          have hGt : G (s, t) = cartF y := by
            rw [G.eq_fst s ht]; simp [hγt]
          show ((1 - (s : ℝ)) * (γ t).1.1 + (s : ℝ) * y.1.1,
            ((G (s, t) : CStar) : ℂ).re, ((G (s, t) : CStar) : ℂ).im) = (γ t).1
          rw [hGt, cartF_re, cartF_im, hγt]
          ext <;> simp; ring }
    exact Quotient.sound ⟨F⟩
  · intro n
    let c := cLoop (cartF y) (Multiplicative.toAdd n)
    let γ : Path y y :=
      { toFun := fun t => ⟨(y.1.1, ((c t : CStar) : ℂ).re, ((c t : CStar) : ℂ).im),
          not_mem_cartS₁_of_ne_zero _ _⟩
        continuous_toFun := by
          refine Continuous.subtype_mk ?_ _
          have hc : Continuous fun t => ((c t : CStar) : ℂ) :=
            continuous_subtype_val.comp c.continuous
          exact continuous_const.prodMk ((Complex.continuous_re.comp hc).prodMk
            (Complex.continuous_im.comp hc))
        source' := by
          apply Subtype.ext
          simp only [c.source, cartF_re, cartF_im]
        target' := by
          apply Subtype.ext
          simp only [c.target, cartF_re, cartF_im] }
    have hγ : γ.map cartF.continuous = c := by
      ext t
      show ((cartF (γ t) : CStar) : ℂ) = ((c t : CStar) : ℂ)
      apply Complex.ext
      · rw [cartF_re]; rfl
      · rw [cartF_im]; rfl
    refine ⟨FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ), ?_⟩
    rw [cartDeg_mk, hγ, cWinding_cLoop]
    rfl

/-- `ex:consider_carthesian_coordinates_usual`, first claim for `S₁` (`RamcovGX.tex:1218`):
`π₁(ℝ³ ∖ S₁) ≅ ℤ` at every base point, by the number of turns around `S₁`. -/
theorem carthesian_piOne_S₁_at (y : (cartS₁ᶜ : Set (ℝ × ℝ × ℝ))) :
    Nonempty (FundamentalGroup (cartS₁ᶜ : Set (ℝ × ℝ × ℝ)) y ≃* Multiplicative ℤ) :=
  ⟨MulEquiv.ofBijective (cartDeg y) (cartDeg_bijective y)⟩

/-- `ex:consider_carthesian_coordinates_usual`, first claim, for `S₁`. -/
theorem carthesian_piOne_S₁ : CartPiOneZ cartS₁ := carthesian_piOne_S₁_at

/-! #### The planar picture of `S₂`, and the fourth claim

`S₂ = P × {0}` with `P ⊆ ℝ²` the closed topologist's sine curve (both sides, with its limit
segment); `ℝ² ∖ P` is the union of the open regions `A₊` above and `A₋` below `P`. The fourth claim
is proved by the paper's argument (`RamcovGX.tex:1229–1257`), with its mod 2 intersection numbers
replaced by windings around `0` of `ψ + i z`, `ψ` a signed distance to `P`: globally `ψ > 0` on
`A₊`; locally (in the strip `|y| < 1/2`) `ψ* > 0` only on finitely many "pockets" of `A₊`, which
stay away from `O`. -/

/-- `P`, the planar topologist's sine curve with its limit segment. -/
def cartPl : Set (ℝ × ℝ) :=
  {p | (p.1 ≠ 0 ∧ p.2 = Real.sin (1 / p.1)) ∨ (p.1 = 0 ∧ |p.2| ≤ 1)}

/-- `A₊`, the region above `P`. -/
def cartAp : Set (ℝ × ℝ) :=
  {p | (p.1 ≠ 0 ∧ Real.sin (1 / p.1) < p.2) ∨ (p.1 = 0 ∧ 1 < p.2)}

/-- `A₋`, the region below `P`. -/
def cartAm : Set (ℝ × ℝ) :=
  {p | (p.1 ≠ 0 ∧ p.2 < Real.sin (1 / p.1)) ∨ (p.1 = 0 ∧ p.2 < -1)}

theorem mem_cartS₂_iff (q : ℝ × ℝ × ℝ) : q ∈ cartS₂ ↔ (q.1, q.2.1) ∈ cartPl ∧ q.2.2 = 0 := by
  simp only [cartS₂, cartPl, mem_union, mem_setOf_eq]
  tauto

theorem cartPl_trichotomy (p : ℝ × ℝ) : p ∈ cartPl ∨ p ∈ cartAp ∨ p ∈ cartAm := by
  simp only [cartPl, cartAp, cartAm, mem_setOf_eq]
  by_cases h : p.1 = 0
  · rcases le_or_gt |p.2| 1 with h' | h'
    · exact Or.inl (Or.inr ⟨h, h'⟩)
    · rcases lt_abs.1 h' with h'' | h''
      · exact Or.inr (Or.inl (Or.inr ⟨h, h''⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨h, by linarith⟩))
  · rcases lt_trichotomy p.2 (Real.sin (1 / p.1)) with h' | h' | h'
    · exact Or.inr (Or.inr (Or.inl ⟨h, h'⟩))
    · exact Or.inl (Or.inl ⟨h, h'⟩)
    · exact Or.inr (Or.inl (Or.inl ⟨h, h'⟩))

theorem not_mem_cartPl_of_mem_cartAp {p : ℝ × ℝ} (h : p ∈ cartAp) : p ∉ cartPl := by
  simp only [cartPl, cartAp, mem_setOf_eq] at h ⊢
  rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> rcases h with ⟨h3, h4⟩ | ⟨h3, h4⟩
  · linarith
  · exact h1 h3
  · exact h3 h1
  · linarith [le_abs_self p.2]

theorem not_mem_cartPl_of_mem_cartAm {p : ℝ × ℝ} (h : p ∈ cartAm) : p ∉ cartPl := by
  simp only [cartPl, cartAm, mem_setOf_eq] at h ⊢
  rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> rcases h with ⟨h3, h4⟩ | ⟨h3, h4⟩
  · linarith
  · exact h1 h3
  · exact h3 h1
  · linarith [neg_abs_le p.2]

theorem not_mem_cartAm_of_mem_cartAp {p : ℝ × ℝ} (h : p ∈ cartAp) : p ∉ cartAm := by
  simp only [cartAm, cartAp, mem_setOf_eq] at h ⊢
  rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> rcases h with ⟨h3, h4⟩ | ⟨h3, h4⟩
  · linarith
  · exact h1 h3
  · exact h3 h1
  · linarith

theorem continuousOn_sin_inv_fst :
    ContinuousOn (fun p : ℝ × ℝ => Real.sin (1 / p.1)) {p | p.1 ≠ 0} :=
  Real.continuous_sin.comp_continuousOn
    (continuousOn_const.div continuous_fst.continuousOn fun _ hp => hp)

theorem isOpen_cartAp : IsOpen cartAp := by
  have e : cartAp = ({p : ℝ × ℝ | p.1 ≠ 0} ∩ (fun p : ℝ × ℝ => p.2 - Real.sin (1 / p.1)) ⁻¹'
      Ioi 0) ∪ {p | 1 < p.2} := by
    ext p
    simp only [cartAp, mem_union, mem_inter_iff, mem_setOf_eq, mem_preimage, mem_Ioi, sub_pos]
    constructor
    · rintro (h | ⟨-, h⟩)
      · exact Or.inl h
      · exact Or.inr h
    · rintro (h | h)
      · exact Or.inl h
      · by_cases h0 : p.1 = 0
        · exact Or.inr ⟨h0, h⟩
        · exact Or.inl ⟨h0, lt_of_le_of_lt (Real.sin_le_one _) h⟩
  rw [e]
  refine IsOpen.union ?_ (isOpen_lt continuous_const continuous_snd)
  exact (continuous_snd.continuousOn.sub continuousOn_sin_inv_fst).isOpen_inter_preimage
    (isOpen_ne_fun continuous_fst continuous_const) isOpen_Ioi

theorem isOpen_cartAm : IsOpen cartAm := by
  have e : cartAm = ({p : ℝ × ℝ | p.1 ≠ 0} ∩ (fun p : ℝ × ℝ => Real.sin (1 / p.1) - p.2) ⁻¹'
      Ioi 0) ∪ {p | p.2 < -1} := by
    ext p
    simp only [cartAm, mem_union, mem_inter_iff, mem_setOf_eq, mem_preimage, mem_Ioi, sub_pos]
    constructor
    · rintro (h | ⟨-, h⟩)
      · exact Or.inl h
      · exact Or.inr h
    · rintro (h | h)
      · exact Or.inl h
      · by_cases h0 : p.1 = 0
        · exact Or.inr ⟨h0, h⟩
        · exact Or.inl ⟨h0, lt_of_lt_of_le h (Real.neg_one_le_sin _)⟩
  rw [e]
  refine IsOpen.union ?_ (isOpen_lt continuous_snd continuous_const)
  exact (continuousOn_sin_inv_fst.sub continuous_snd.continuousOn).isOpen_inter_preimage
    (isOpen_ne_fun continuous_fst continuous_const) isOpen_Ioi

theorem isClosed_cartPl : IsClosed cartPl := by
  have : cartPlᶜ = cartAp ∪ cartAm := by
    ext p
    simp only [mem_compl_iff, mem_union]
    constructor
    · intro h
      rcases cartPl_trichotomy p with h' | h' | h'
      · exact absurd h' h
      · exact Or.inl h'
      · exact Or.inr h'
    · rintro (h | h)
      · exact not_mem_cartPl_of_mem_cartAp h
      · exact not_mem_cartPl_of_mem_cartAm h
  rw [← isOpen_compl_iff, this]
  exact isOpen_cartAp.union isOpen_cartAm

theorem cartPl_nonempty : cartPl.Nonempty := ⟨(0, 0), Or.inr ⟨rfl, by simp⟩⟩

/-- The signed distance to `P`, positive on `W`. -/
def sgnDist {E : Type*} [PseudoMetricSpace E] (W P : Set E) (p : E) : ℝ :=
  if p ∈ W then Metric.infDist p P else -Metric.infDist p P

theorem continuousOn_sgnDist {E : Type*} [PseudoMetricSpace E] {P W G : Set E} (hW : IsOpen W)
    (hR : IsOpen (G \ (P ∪ W))) : ContinuousOn (sgnDist W P) G := by
  intro p hp
  apply ContinuousAt.continuousWithinAt
  by_cases h1 : p ∈ W
  · exact (Metric.continuous_infDist_pt P).continuousAt.congr
      (Filter.eventually_of_mem (hW.mem_nhds h1) fun q hq => (if_pos hq).symm)
  by_cases h2 : p ∈ P
  · have h0 : sgnDist W P p = 0 := by simp [sgnDist, h1, Metric.infDist_zero_of_mem h2]
    rw [ContinuousAt, h0, tendsto_zero_iff_norm_tendsto_zero]
    have hn : ∀ q, ‖sgnDist W P q‖ = Metric.infDist q P := fun q => by
      unfold sgnDist
      split_ifs
      · exact Real.norm_of_nonneg Metric.infDist_nonneg
      · rw [norm_neg]; exact Real.norm_of_nonneg Metric.infDist_nonneg
    simp only [hn]
    have := (Metric.continuous_infDist_pt P).tendsto p
    rwa [Metric.infDist_zero_of_mem h2] at this
  · exact (Metric.continuous_infDist_pt P).neg.continuousAt.congr
      (Filter.eventually_of_mem (hR.mem_nhds ⟨hp, fun h => h.elim h2 h1⟩) fun q hq =>
        (if_neg fun h => hq.2 (Or.inr h)).symm)

theorem sgnDist_pos {E : Type*} [PseudoMetricSpace E] {P W : Set E} (hP : IsClosed P)
    (hPn : P.Nonempty) {p : E} (hpW : p ∈ W) (hpP : p ∉ P) : 0 < sgnDist W P p := by
  rw [sgnDist, if_pos hpW]; exact (hP.notMem_iff_infDist_pos hPn).1 hpP

theorem sgnDist_neg {E : Type*} [PseudoMetricSpace E] {P W : Set E} (hP : IsClosed P)
    (hPn : P.Nonempty) {p : E} (hpW : p ∉ W) (hpP : p ∉ P) : sgnDist W P p < 0 := by
  rw [sgnDist, if_neg hpW, neg_lt_zero]; exact (hP.notMem_iff_infDist_pos hPn).1 hpP

theorem sgnDist_zero {E : Type*} [PseudoMetricSpace E] {P W : Set E} {p : E} (hpW : p ∉ W)
    (hpP : p ∈ P) : sgnDist W P p = 0 := by
  rw [sgnDist, if_neg hpW, Metric.infDist_zero_of_mem hpP, neg_zero]

/-- `ψ`: the signed distance to `P`, positive above it. -/
def cartPsi : ℝ × ℝ → ℝ := sgnDist cartAp cartPl

theorem continuous_cartPsi : Continuous cartPsi := by
  rw [← continuousOn_univ]
  refine continuousOn_sgnDist isOpen_cartAp ?_
  have : (univ : Set (ℝ × ℝ)) \ (cartPl ∪ cartAp) = cartAm := by
    ext p
    simp only [Set.mem_sdiff, mem_univ, mem_union, true_and, not_or]
    constructor
    · rintro ⟨h1, h2⟩
      rcases cartPl_trichotomy p with h | h | h
      · exact absurd h h1
      · exact absurd h h2
      · exact h
    · intro h
      exact ⟨not_mem_cartPl_of_mem_cartAm h, fun h' => not_mem_cartAm_of_mem_cartAp h' h⟩
  rw [this]; exact isOpen_cartAm

/-- `F₀ = ψ + i z : ℝ³ → ℂ`, nonzero off `S₂`. -/
def cartF₀ (q : ℝ × ℝ × ℝ) : ℂ := (cartPsi (q.1, q.2.1) : ℂ) + (q.2.2 : ℂ) * Complex.I

theorem continuous_cartF₀ : Continuous cartF₀ := by
  unfold cartF₀
  have : Continuous fun q : ℝ × ℝ × ℝ => cartPsi (q.1, q.2.1) :=
    continuous_cartPsi.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))
  fun_prop

@[simp] theorem cartF₀_re (q : ℝ × ℝ × ℝ) : (cartF₀ q).re = cartPsi (q.1, q.2.1) := by
  simp [cartF₀]

@[simp] theorem cartF₀_im (q : ℝ × ℝ × ℝ) : (cartF₀ q).im = q.2.2 := by
  simp [cartF₀]

theorem cartPsi_pos {p : ℝ × ℝ} (h : p ∈ cartAp) : 0 < cartPsi p :=
  sgnDist_pos isClosed_cartPl cartPl_nonempty h (not_mem_cartPl_of_mem_cartAp h)

theorem cartPsi_neg {p : ℝ × ℝ} (h : p ∈ cartAm) : cartPsi p < 0 :=
  sgnDist_neg isClosed_cartPl cartPl_nonempty (fun h' => not_mem_cartAm_of_mem_cartAp h' h)
    (not_mem_cartPl_of_mem_cartAm h)

theorem cartPsi_zero {p : ℝ × ℝ} (h : p ∈ cartPl) : cartPsi p = 0 :=
  sgnDist_zero (fun h' => not_mem_cartPl_of_mem_cartAp h' h) h

theorem cartF₀_ne_zero {q : ℝ × ℝ × ℝ} (hq : q ∉ cartS₂) : cartF₀ q ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp only [cartF₀_re, cartF₀_im, Complex.zero_re, Complex.zero_im] at hre him
  apply hq
  rw [mem_cartS₂_iff]
  refine ⟨?_, him⟩
  rcases cartPl_trichotomy (q.1, q.2.1) with h' | h' | h'
  · exact h'
  · exact absurd hre (cartPsi_pos h').ne'
  · exact absurd hre (cartPsi_neg h').ne

/-- **Windings along a family.** For a continuous family `w(s, ·)` of paths of `ℂ ∖ {0}` whose
ends are opposite, `w(s,1) = -w(s,0)`, off the real axis, the winding `Λ(1) - Λ(0)` of any lift
`Λ` of `w(s, ·)` through `exp` does not depend on `s`. -/
theorem wind_const_family {w : I × I → ℂ} (hwc : Continuous w) (hw : ∀ z, w z ≠ 0)
    (hend : ∀ s, w (s, 1) = -w (s, 0)) (him : ∀ s, (w (s, 0)).im ≠ 0) {Λ Λ' : C(I, ℂ)}
    (hΛ : ∀ t, Complex.exp (Λ t) = w (0, t)) (hΛ' : ∀ t, Complex.exp (Λ' t) = w (1, t)) :
    Λ 1 - Λ 0 = Λ' 1 - Λ' 0 := by
  let G : C(I × I, CStar) := ⟨fun z => ⟨w (z.2, z.1), hw _⟩,
    (hwc.comp continuous_swap).subtype_mk _⟩
  have hsl : ∀ s, w (s, 0) ∈ Complex.slitPlane := fun s => Complex.mem_slitPlane_iff.2 (Or.inr (him s))
  let f : C(I, ℂ) := ⟨fun s => Complex.log (w (s, 0)),
    (hwc.comp (continuous_id.prodMk continuous_const)).clog fun s => hsl s⟩
  have hG0 : ∀ s, G (0, s) = cExp (f s) := fun s => Subtype.ext (by
    show w (s, 0) = Complex.exp (Complex.log (w (s, 0)))
    rw [Complex.exp_log (hw _)])
  let L := isCoveringMap_cExp.liftHomotopy G f hG0
  have hL : ∀ z, Complex.exp (L z) = w (z.2, z.1) := fun z =>
    congrArg Subtype.val (congrFun (isCoveringMap_cExp.liftHomotopy_lifts G f hG0) z)
  have hL0 : ∀ s, L (0, s) = Complex.log (w (s, 0)) := isCoveringMap_cExp.liftHomotopy_zero G f hG0
  -- the winding along each `w(s, ·)` is constant in `s`
  let g : I → ℂ := fun s => L (1, s) - L (0, s)
  have hgc : Continuous g := (L.continuous.comp (continuous_const.prodMk continuous_id)).sub
    (L.continuous.comp (continuous_const.prodMk continuous_id))
  have hgexp : ∀ s s', cExp (g s) = cExp (g s') := fun s s' => Subtype.ext (by
    simp only [cExp_apply, g, Complex.exp_sub, hL, hend, hL0, Complex.exp_log (hw _)]
    rw [neg_div, neg_div, div_self (hw _), div_self (hw _)])
  have hg := isCoveringMap_cExp.const_of_comp hgc hgexp 0 1
  -- compare with the given lifts
  let L₀ : C(I, ℂ) := ⟨fun t => L (t, 0), by fun_prop⟩
  let L₁ : C(I, ℂ) := ⟨fun t => L (t, 1), by fun_prop⟩
  have e₀ := expLift_sub_const (Γ := Λ) (Γ' := L₀) (fun t => by
    show Complex.exp (Λ t) = Complex.exp (L (t, 0)); rw [hΛ, hL])
  have e₁ := expLift_sub_const (Γ := Λ') (Γ' := L₁) (fun t => by
    show Complex.exp (Λ' t) = Complex.exp (L (t, 1)); rw [hΛ', hL])
  have a₀ := e₀ 1
  have a₁ := e₁ 1
  simp only [L₀, L₁, ContinuousMap.coe_mk] at a₀ a₁
  simp only [g] at hg
  linear_combination hg - a₀ + a₁

/-- The pockets of `A₊` in the strip `|y| < 1/2` beyond the cuts `x = ε₁`, `x = -ε₂`. -/
def cartW (ε₁ ε₂ : ℝ) : Set (ℝ × ℝ) :=
  {p | p ∈ cartAp ∧ |p.2| < 1 / 2 ∧ (ε₁ < p.1 ∨ p.1 < -ε₂)}

theorem isOpen_cartW (ε₁ ε₂ : ℝ) : IsOpen (cartW ε₁ ε₂) :=
  isOpen_cartAp.inter ((isOpen_lt (continuous_abs.comp continuous_snd) continuous_const).inter
    ((isOpen_lt continuous_const continuous_fst).union (isOpen_lt continuous_fst continuous_const)))

theorem cartW_subset (ε₁ ε₂ : ℝ) : cartW ε₁ ε₂ ⊆ cartAp := fun _ h => h.1

/-- The cuts are where `sin (1/x) = 1`, so no point of `A₊` in the strip lies on them. -/
theorem isOpen_strip_diff_cartW {ε₁ ε₂ : ℝ} (h₁ : Real.sin (1 / ε₁) = 1)
    (h₂ : Real.sin (1 / -ε₂) = 1) :
    IsOpen ({p : ℝ × ℝ | |p.2| < 1 / 2} \ (cartPl ∪ cartW ε₁ ε₂)) := by
  have hcut : ∀ p ∈ cartAp, |p.2| < 1 / 2 → p.1 ≠ ε₁ ∧ p.1 ≠ -ε₂ := by
    intro p hp hy
    have hy' := (abs_lt.1 hy).2
    rcases hp with ⟨h0, hs⟩ | ⟨h0, hs⟩
    · constructor
      · rintro rfl; linarith
      · rintro h; rw [h] at hs; linarith
    · linarith
  have e : {p : ℝ × ℝ | |p.2| < 1 / 2} \ (cartPl ∪ cartW ε₁ ε₂) =
      ({p : ℝ × ℝ | |p.2| < 1 / 2} ∩ cartAm) ∪
        ({p : ℝ × ℝ | |p.2| < 1 / 2} ∩ (cartAp ∩ ({p | -ε₂ < p.1} ∩ {p | p.1 < ε₁}))) := by
    ext p
    simp only [Set.mem_sdiff, mem_union, mem_inter_iff, mem_setOf_eq, not_or]
    constructor
    · rintro ⟨hy, hP, hW⟩
      rcases cartPl_trichotomy p with h | h | h
      · exact absurd h hP
      · refine Or.inr ⟨hy, h, ?_, ?_⟩
        · rcases lt_or_ge (-ε₂) p.1 with h' | h'
          · exact h'
          · rcases h'.lt_or_eq with h'' | h''
            · exact absurd ⟨h, hy, Or.inr h''⟩ hW
            · exact absurd h'' (hcut p h hy).2
        · rcases lt_or_ge p.1 ε₁ with h' | h'
          · exact h'
          · rcases h'.lt_or_eq with h'' | h''
            · exact absurd ⟨h, hy, Or.inl h''⟩ hW
            · exact absurd h''.symm (hcut p h hy).1
      · exact Or.inl ⟨hy, h⟩
    · rintro (⟨hy, h⟩ | ⟨hy, h, h1, h2⟩)
      · exact ⟨hy, not_mem_cartPl_of_mem_cartAm h,
          fun hW => not_mem_cartAm_of_mem_cartAp hW.1 h⟩
      · refine ⟨hy, not_mem_cartPl_of_mem_cartAp h, ?_⟩
        rintro ⟨-, -, h3 | h3⟩ <;> linarith
  rw [e]
  have hy : IsOpen {p : ℝ × ℝ | |p.2| < 1 / 2} :=
    isOpen_lt (continuous_abs.comp continuous_snd) continuous_const
  exact (hy.inter isOpen_cartAm).union (hy.inter (isOpen_cartAp.inter
    ((isOpen_lt continuous_const continuous_fst).inter (isOpen_lt continuous_fst continuous_const))))

/-- `ψ*`: the signed distance to `P`, positive on the pockets `cartW ε₁ ε₂`. -/
def cartPsiW (ε₁ ε₂ : ℝ) : ℝ × ℝ → ℝ := sgnDist (cartW ε₁ ε₂) cartPl

/-- `F* = ψ* + i z`. -/
def cartFW (ε₁ ε₂ : ℝ) (q : ℝ × ℝ × ℝ) : ℂ :=
  (cartPsiW ε₁ ε₂ (q.1, q.2.1) : ℂ) + (q.2.2 : ℂ) * Complex.I

theorem continuousOn_cartFW {ε₁ ε₂ : ℝ} (h₁ : Real.sin (1 / ε₁) = 1)
    (h₂ : Real.sin (1 / -ε₂) = 1) :
    ContinuousOn (cartFW ε₁ ε₂) {q | |q.2.1| < 1 / 2} := by
  have hψ : ContinuousOn (cartPsiW ε₁ ε₂) {p : ℝ × ℝ | |p.2| < 1 / 2} :=
    continuousOn_sgnDist (isOpen_cartW ε₁ ε₂) (isOpen_strip_diff_cartW h₁ h₂)
  have hc : ContinuousOn (fun q : ℝ × ℝ × ℝ => cartPsiW ε₁ ε₂ (q.1, q.2.1))
      {q | |q.2.1| < 1 / 2} :=
    hψ.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd)).continuousOn
      fun q hq => hq
  unfold cartFW
  exact (Complex.continuous_ofReal.comp_continuousOn hc).add
    ((Complex.continuous_ofReal.comp (continuous_snd.comp continuous_snd)).continuousOn.mul
      continuousOn_const)

@[simp] theorem cartFW_re (ε₁ ε₂ : ℝ) (q : ℝ × ℝ × ℝ) :
    (cartFW ε₁ ε₂ q).re = cartPsiW ε₁ ε₂ (q.1, q.2.1) := by
  simp [cartFW]

@[simp] theorem cartFW_im (ε₁ ε₂ : ℝ) (q : ℝ × ℝ × ℝ) : (cartFW ε₁ ε₂ q).im = q.2.2 := by
  simp [cartFW]

theorem cartPsiW_pos {ε₁ ε₂ : ℝ} {p : ℝ × ℝ} (h : p ∈ cartW ε₁ ε₂) : 0 < cartPsiW ε₁ ε₂ p :=
  sgnDist_pos isClosed_cartPl cartPl_nonempty h (not_mem_cartPl_of_mem_cartAp h.1)

theorem cartPsiW_neg {ε₁ ε₂ : ℝ} {p : ℝ × ℝ} (h : p ∉ cartW ε₁ ε₂) (h' : p ∉ cartPl) :
    cartPsiW ε₁ ε₂ p < 0 :=
  sgnDist_neg isClosed_cartPl cartPl_nonempty h h'

theorem cartPsiW_zero {ε₁ ε₂ : ℝ} {p : ℝ × ℝ} (h : p ∈ cartPl) : cartPsiW ε₁ ε₂ p = 0 :=
  sgnDist_zero (fun h' => not_mem_cartPl_of_mem_cartAp h'.1 h) h

theorem cartFW_ne_zero {ε₁ ε₂ : ℝ} {q : ℝ × ℝ × ℝ} (hq : q ∉ cartS₂) : cartFW ε₁ ε₂ q ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp only [cartFW_re, cartFW_im, Complex.zero_re, Complex.zero_im] at hre him
  apply hq
  rw [mem_cartS₂_iff]
  refine ⟨?_, him⟩
  by_contra hP
  by_cases hW : (q.1, q.2.1) ∈ cartW ε₁ ε₂
  · exact (cartPsiW_pos hW).ne' hre
  · exact (cartPsiW_neg hW hP).ne hre

/-- The loop of the fourth claim: it leaves `O` upwards, crosses the plane `{z = 0}` once, at
`(0,4,0) ∈ A₊`, and comes back to `O` from below. -/
def cartγ : Path cartO cartO where
  toFun u := (0, 4 * Real.sin (Real.pi * u) ^ 2, Real.sin (Real.pi * u) * Real.cos (Real.pi * u))
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by simp

theorem cartγ_apply (u : I) :
    cartγ u = (0, 4 * Real.sin (Real.pi * u) ^ 2, Real.sin (Real.pi * u) * Real.cos (Real.pi * u)) := rfl

theorem cartγ_interior {u : I} (h0 : 0 < (u : ℝ)) (h1 : (u : ℝ) < 1) :
    0 < Real.sin (Real.pi * u) ∧ (Real.sin (Real.pi * u) * Real.cos (Real.pi * u) = 0 → 1 < 4 * Real.sin (Real.pi * u) ^ 2) := by
  have hs : 0 < Real.sin (Real.pi * u) := Real.sin_pos_of_pos_of_lt_pi (by positivity)
    (by nlinarith [Real.pi_pos])
  refine ⟨hs, fun h => ?_⟩
  have hc : Real.cos (Real.pi * u) = 0 := by
    rcases mul_eq_zero.1 h with h | h
    · exact absurd h hs.ne'
    · exact h
  have := Real.sin_sq_add_cos_sq (Real.pi * u)
  rw [hc] at this
  nlinarith

theorem cartγ_memOmega : MemOmega cartS₂ᶜ cartγ := by
  intro u h0 h1 hS
  rw [mem_cartS₂_iff, cartγ_apply] at hS
  obtain ⟨hP, hz⟩ := hS
  have h4 := (cartγ_interior h0 h1).2 hz
  rcases hP with ⟨h, -⟩ | ⟨-, h⟩
  · exact h rfl
  · simp only at h
    rw [abs_of_nonneg (by positivity)] at h
    linarith

theorem cartF₀_cartγ_mem_slitPlane {u : I} (h0 : 0 < (u : ℝ)) (h1 : (u : ℝ) < 1) :
    cartF₀ (cartγ u) ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff, cartF₀_re, cartF₀_im, cartγ_apply]
  by_cases hz : Real.sin (Real.pi * u) * Real.cos (Real.pi * u) = 0
  · left
    apply cartPsi_pos
    exact Or.inr ⟨rfl, (cartγ_interior h0 h1).2 hz⟩
  · exact Or.inr hz

/-- Near its ends, `γ` lies over the limit segment of `P` (`x = 0`, `|y| ≤ 1`). -/
theorem cartγ_end {u : I} (h0 : 0 < (u : ℝ)) (h1 : (u : ℝ) ≤ 1 / 10) :
    ((cartγ u).1, (cartγ u).2.1) ∈ cartPl ∧ 0 < (cartγ u).2.2 ∧
      cartγ (σ u) = ((cartγ u).1, (cartγ u).2.1, -(cartγ u).2.2) := by
  have hs0 : 0 < Real.sin (Real.pi * u) := Real.sin_pos_of_pos_of_lt_pi (by positivity)
    (by nlinarith [Real.pi_pos])
  have hsle : Real.sin (Real.pi * u) ≤ Real.pi * u := Real.sin_le (by positivity)
  have hpi := Real.pi_le_four
  have hc0 : 0 < Real.cos (Real.pi * u) := Real.cos_pos_of_mem_Ioo ⟨by nlinarith [Real.pi_pos],
    by nlinarith [Real.pi_pos]⟩
  refine ⟨Or.inr ⟨rfl, ?_⟩, mul_pos hs0 hc0, ?_⟩
  · simp only [cartγ_apply]
    rw [abs_of_nonneg (by positivity)]
    have hb : Real.sin (Real.pi * u) ≤ 2 / 5 := le_trans hsle (by nlinarith)
    nlinarith
  · rw [cartγ_apply, cartγ_apply, coe_symm_eq, mul_sub, mul_one, Real.sin_pi_sub, Real.cos_pi_sub]
    simp

theorem cartF₀_of_mem {q : ℝ × ℝ × ℝ} (h : (q.1, q.2.1) ∈ cartPl) :
    cartF₀ q = (q.2.2 : ℂ) * Complex.I := by
  rw [cartF₀, cartPsi_zero h]; simp

theorem cartFW_of_mem {ε₁ ε₂ : ℝ} {q : ℝ × ℝ × ℝ} (h : (q.1, q.2.1) ∈ cartPl) :
    cartFW ε₁ ε₂ q = (q.2.2 : ℂ) * Complex.I := by
  rw [cartFW, cartPsiW_zero h]; simp

theorem arg_ofReal_mul_I {c : ℝ} (hc : 0 < c) :
    Complex.arg ((c : ℂ) * Complex.I) = Real.pi / 2 := by
  rw [Complex.arg_real_mul _ hc, Complex.arg_I]

theorem arg_neg_ofReal_mul_I {c : ℝ} (hc : 0 < c) :
    Complex.arg (-((c : ℂ) * Complex.I)) = -(Real.pi / 2) := by
  rw [← mul_neg, Complex.arg_real_mul _ hc, Complex.arg_neg_I]

/-- The quotient of `b + i z` by `a + i z` is off `(-∞, 0]` when `a` and `b` have the same sign
whenever `z = 0`. -/
theorem div_mem_slitPlane_of_sameSign {a b z : ℝ} (h : z = 0 → 0 < a * b)
    (hne : (a : ℂ) + (z : ℂ) * Complex.I ≠ 0) :
    ((b : ℂ) + (z : ℂ) * Complex.I) / ((a : ℂ) + (z : ℂ) * Complex.I) ∈ Complex.slitPlane := by
  set w : ℂ := (a : ℂ) + (z : ℂ) * Complex.I with hw
  have hn : 0 < Complex.normSq w := Complex.normSq_pos.2 hne
  have hre : (((b : ℂ) + (z : ℂ) * Complex.I) / w).re = (b * a + z * z) / Complex.normSq w := by
    rw [hw, Complex.div_re]; simp; ring
  have him : (((b : ℂ) + (z : ℂ) * Complex.I) / w).im = (z * a - b * z) / Complex.normSq w := by
    rw [hw, Complex.div_im]; simp; ring
  rw [Complex.mem_slitPlane_iff, hre, him]
  by_cases h0 : z * a - b * z = 0
  · left
    refine div_pos ?_ hn
    have : z * (a - b) = 0 := by linarith
    rcases mul_eq_zero.1 this with h' | h'
    · have := h h'; rw [h']; nlinarith
    · have hab : a = b := by linarith
      rw [← hab]
      rcases eq_or_ne z 0 with hz | hz
      · have := h hz; rw [hab] at this ⊢; nlinarith
      · nlinarith [mul_self_pos.2 hz, mul_self_nonneg a]
  · right
    exact div_ne_zero h0 hn.ne'

theorem squareExt_eq (F : I × I → X) {u₁ u₂ : ℝ} (hσ : u₁ ∈ I) (hτ : u₂ ∈ I) :
    squareExt F (u₁, u₂) = F (⟨u₁, hσ⟩, ⟨u₂, hτ⟩) := by
  rw [squareExt_apply _ _ hτ, Set.projIcc_of_mem _ hσ]

section NotTrivial

variable (H : Path.Homotopy cartγ (Path.refl cartO))

/-- The reparametrised homotopy of the proof of the fourth claim (the paper's `H' = H ∘ c`,
`RamcovGX.tex:1236–1241`): at time `s`, run along `H(·, a)` from `γ(a)`, then `H(s, ·)` on
`[a, 1 - a]`, then back along `H(·, 1 - a)` to `γ(1 - a)`, with `a = (1 - s)/10`. -/
def cartM (p : ℝ × ℝ) : ℝ × ℝ × ℝ :=
  if p.2 ≤ 1 / 3 then squareExt (fun z => H z) (3 * p.2 * p.1, (1 - p.1) / 10)
  else if p.2 ≤ 2 / 3 then
    squareExt (fun z => H z) (p.1, (1 - p.1) / 10 + (3 * p.2 - 1) * (1 - 2 * ((1 - p.1) / 10)))
  else squareExt (fun z => H z) ((3 - 3 * p.2) * p.1, 1 - (1 - p.1) / 10)

theorem continuous_cartM : Continuous (cartM H) := by
  have hG : Continuous (squareExt fun z => H z) := continuous_squareExt H.continuous
  unfold cartM
  refine Continuous.if_le (hG.comp (by fun_prop)) (Continuous.if_le (hG.comp (by fun_prop))
    (hG.comp (by fun_prop)) continuous_snd continuous_const ?_) continuous_snd continuous_const ?_
  · intro p hp
    simp only [hp]
    congr 1; ext <;> simp <;> ring
  · intro p hp
    simp only [hp, show (1 / 3 : ℝ) ≤ 2 / 3 by norm_num, if_true]
    congr 1; ext <;> simp

/-- The values of `cartM` are values of `H` on the frame of `[0,s] × [a, 1-a]`. -/
theorem cartM_frame {s t : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∃ u₁ u₂ : I, cartM H (s, t) = H (u₁, u₂) ∧ (u₁ : ℝ) ≤ s ∧ (1 - s) / 10 ≤ u₂ ∧
      (u₂ : ℝ) ≤ 1 - (1 - s) / 10 ∧
      ((u₂ : ℝ) = (1 - s) / 10 ∨ (u₁ : ℝ) = s ∨ (u₂ : ℝ) = 1 - (1 - s) / 10) := by
  unfold cartM
  simp only
  split_ifs with h1 h2
  · have hσ : 3 * t * s ∈ I := ⟨by positivity, by nlinarith⟩
    have hτ : (1 - s) / 10 ∈ I := ⟨by linarith, by linarith⟩
    refine ⟨⟨_, hσ⟩, ⟨_, hτ⟩, squareExt_eq _ hσ hτ, by show 3 * t * s ≤ s; nlinarith,
      le_refl _, by show (1 - s) / 10 ≤ 1 - (1 - s) / 10; linarith, Or.inl rfl⟩
  · have hσ : s ∈ I := ⟨hs0, hs1⟩
    have hτ : (1 - s) / 10 + (3 * t - 1) * (1 - 2 * ((1 - s) / 10)) ∈ I :=
      ⟨by nlinarith, by nlinarith⟩
    refine ⟨⟨_, hσ⟩, ⟨_, hτ⟩, squareExt_eq _ hσ hτ, le_refl s,
      by show (1 - s) / 10 ≤ _; nlinarith, by show _ ≤ 1 - (1 - s) / 10; nlinarith,
      Or.inr (Or.inl rfl)⟩
  · have hσ : (3 - 3 * t) * s ∈ I := ⟨by nlinarith, by nlinarith⟩
    have hτ : 1 - (1 - s) / 10 ∈ I := ⟨by linarith, by linarith⟩
    refine ⟨⟨_, hσ⟩, ⟨_, hτ⟩, squareExt_eq _ hσ hτ, by show (3 - 3 * t) * s ≤ s; nlinarith,
      by show (1 - s) / 10 ≤ 1 - (1 - s) / 10; linarith, le_refl _, Or.inr (Or.inr rfl)⟩

theorem cartM_zero {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    cartM H (s, 0) = cartγ ⟨(1 - s) / 10, by constructor <;> linarith⟩ := by
  have hτ : (1 - s) / 10 ∈ I := ⟨by linarith, by linarith⟩
  have h0 : (0 : ℝ) ∈ I := ⟨le_rfl, zero_le_one⟩
  unfold cartM
  simp only [show (0 : ℝ) ≤ 1 / 3 by norm_num, if_true, mul_zero, zero_mul]
  rw [squareExt_eq _ h0 hτ]
  exact H.apply_zero _

theorem cartM_one {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    cartM H (s, 1) = cartγ (σ ⟨(1 - s) / 10, by constructor <;> linarith⟩) := by
  have hτ : 1 - (1 - s) / 10 ∈ I := ⟨by linarith, by linarith⟩
  have h0 : (0 : ℝ) ∈ I := ⟨le_rfl, zero_le_one⟩
  unfold cartM
  simp only [show ¬ (1 : ℝ) ≤ 1 / 3 by norm_num, show ¬ (1 : ℝ) ≤ 2 / 3 by norm_num, if_false,
    mul_one, sub_self, zero_mul]
  rw [squareExt_eq _ h0 hτ]
  refine (H.apply_zero _).trans ?_
  congr 1

theorem cartM_not_mem (hH : ∀ s t : I, (s : ℝ) < 1 → 0 < (t : ℝ) → (t : ℝ) < 1 →
    H (s, t) ∈ cartS₂ᶜ) {s t : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    cartM H (s, t) ∉ cartS₂ := by
  obtain ⟨σ', τ, he, hσ, hτ0, hτ1, -⟩ := cartM_frame H hs0 hs1.le ht0 ht1
  rw [he]
  exact hH σ' τ (by linarith) (by linarith) (by linarith)

theorem cartM_small (ε : ℝ) (hε : 0 < ε) :
    ∃ s' : ℝ, 0 ≤ s' ∧ s' < 1 ∧ ∀ s t : ℝ, s' ≤ s → s ≤ 1 → 0 ≤ t → t ≤ 1 →
      ‖cartM H (s, t)‖ < ε := by
  obtain ⟨δ, hδ, hH⟩ := Metric.uniformContinuous_iff.1
    (CompactSpace.uniformContinuous_of_continuous H.continuous) ε hε
  refine ⟨max 0 (1 - δ / 2), le_max_left _ _, max_lt zero_lt_one (by linarith), ?_⟩
  intro s t hs hs1 ht0 ht1
  have hs0 : 0 ≤ s := le_trans (le_max_left _ _) hs
  have hsδ : 1 - s < δ := by linarith [le_max_right 0 (1 - δ / 2)]
  obtain ⟨σ', τ, he, hσ, hτ0, hτ1, hcase⟩ := cartM_frame H hs0 hs1 ht0 ht1
  rw [he, ← dist_zero_right]
  have hO : (0 : ℝ × ℝ × ℝ) = cartO := rfl
  rcases hcase with h | h | h
  · have : H (σ', 0) = 0 := H.source σ'
    rw [← this]
    apply hH
    rw [Prod.dist_eq, dist_self, Subtype.dist_eq, Icc.coe_zero, Real.dist_eq, h,
      abs_of_nonneg (by linarith)]
    exact max_lt (by linarith) (by linarith)
  · have : H (1, τ) = 0 := by rw [H.apply_one]; rfl
    rw [← this]
    apply hH
    rw [Prod.dist_eq, dist_self, Subtype.dist_eq, Icc.coe_one, Real.dist_eq, h,
      abs_of_nonpos (by linarith)]
    exact max_lt (by linarith) (by linarith)
  · have : H (σ', 1) = 0 := H.target σ'
    rw [← this]
    apply hH
    rw [Prod.dist_eq, dist_self, Subtype.dist_eq, Icc.coe_one, Real.dist_eq, h,
      abs_of_nonpos (by linarith)]
    exact max_lt (by linarith) (by linarith)

end NotTrivial

/-- **`ex:consider_carthesian_coordinates_usual`, fourth claim, for the loop `cartγ`**: `γ` is not
homotopically trivial in `Ω(O,O,Y ∖ S₂)` (reading (g), DEC-56). The paper's argument
(`RamcovGX.tex:1229–1257`): along the reparametrised homotopy `cartM`, the winding of
`F₀ = ψ + i z` around `0` from `γ(a)` to `γ(1 - a)` stays `-π` (the plane is crossed in `A₊`);
near the end of the homotopy the loops lie in a small ball, where the winding of `F* = ψ* + i z`
— `ψ*` positive only on the finitely many pockets of `A₊` crossed at an intermediate time — is
`+π`, while it agrees with that of `F₀` at the intermediate time and is constant in between. -/
theorem not_isHomTrivial_cartγ : ¬ IsHomTrivial cartS₂ᶜ cartγ := by
  rintro ⟨H, hH⟩
  have hMc := continuous_cartM H
  have hE : ∀ s : ℝ, 0 ≤ s → s < 1 →
      ((cartM H (s, 0)).1, (cartM H (s, 0)).2.1) ∈ cartPl ∧ 0 < (cartM H (s, 0)).2.2 ∧
      cartM H (s, 1) = ((cartM H (s, 0)).1, (cartM H (s, 0)).2.1, -(cartM H (s, 0)).2.2) := by
    intro s hs0 hs1
    rw [cartM_zero H hs0 hs1.le, cartM_one H hs0 hs1.le]
    exact cartγ_end (by show (0 : ℝ) < (1 - s) / 10; linarith)
      (by show (1 - s) / 10 ≤ 1 / 10; linarith)
  have hF₀0 : ∀ s : ℝ, 0 ≤ s → s < 1 →
      cartF₀ (cartM H (s, 0)) = ((cartM H (s, 0)).2.2 : ℂ) * Complex.I :=
    fun s h0 h1 => cartF₀_of_mem (hE s h0 h1).1
  have hF₀1 : ∀ s : ℝ, 0 ≤ s → s < 1 →
      cartF₀ (cartM H (s, 1)) = -(((cartM H (s, 0)).2.2 : ℂ) * Complex.I) := by
    intro s h0 h1
    rw [(hE s h0 h1).2.2, cartF₀_of_mem (q := ((cartM H (s, 0)).1, (cartM H (s, 0)).2.1,
      -(cartM H (s, 0)).2.2)) (hE s h0 h1).1]
    push_cast; ring
  have hFW0 : ∀ ε₁ ε₂ : ℝ, ∀ s : ℝ, 0 ≤ s → s < 1 →
      cartFW ε₁ ε₂ (cartM H (s, 0)) = ((cartM H (s, 0)).2.2 : ℂ) * Complex.I :=
    fun _ _ s h0 h1 => cartFW_of_mem (hE s h0 h1).1
  have hFW1 : ∀ ε₁ ε₂ : ℝ, ∀ s : ℝ, 0 ≤ s → s < 1 →
      cartFW ε₁ ε₂ (cartM H (s, 1)) = -(((cartM H (s, 0)).2.2 : ℂ) * Complex.I) := by
    intro _ _ s h0 h1
    rw [(hE s h0 h1).2.2, cartFW_of_mem (q := ((cartM H (s, 0)).1, (cartM H (s, 0)).2.1,
      -(cartM H (s, 0)).2.2)) (hE s h0 h1).1]
    push_cast; ring
  -- Step A: from `s₀` on, the loops lie in the strip `|y| < 1/2`
  obtain ⟨s₀, hs₀0, hs₀1, hsm₀⟩ := cartM_small H (1 / 2) (by norm_num)
  have hstrip : ∀ s t : ℝ, s₀ ≤ s → s ≤ 1 → 0 ≤ t → t ≤ 1 → |(cartM H (s, t)).2.1| < 1 / 2 := by
    intro s t h1 h2 h3 h4
    have := hsm₀ s t h1 h2 h3 h4
    have h5 : ‖(cartM H (s, t)).2.1‖ ≤ ‖cartM H (s, t)‖ := (norm_fst_le _).trans (norm_snd_le _)
    rw [Real.norm_eq_abs] at h5; linarith
  -- Step B: the crossings of `A₊` at time `s₀` stay away from `x = 0`
  have hMt : Continuous fun t : I => cartM H (s₀, t) :=
    hMc.comp (continuous_const.prodMk continuous_subtype_val)
  set T : Set I := {t | (cartM H (s₀, t)).2.2 = 0 ∧
    ((cartM H (s₀, t)).1, (cartM H (s₀, t)).2.1) ∉ cartAm} with hTdef
  have hTc : IsClosed T :=
    (isClosed_eq ((continuous_snd.comp continuous_snd).comp hMt) continuous_const).inter
      (isOpen_cartAm.preimage ((continuous_fst.prodMk (continuous_fst.comp continuous_snd)).comp
        hMt)).isClosed_compl
  have hTAp : ∀ t ∈ T, ((cartM H (s₀, t)).1, (cartM H (s₀, t)).2.1) ∈ cartAp ∧
      (cartM H (s₀, t)).1 ≠ 0 := by
    rintro t ⟨hz, hAm⟩
    have hns := cartM_not_mem H hH hs₀0 hs₀1 t.2.1 t.2.2
    have hPl : ((cartM H (s₀, t)).1, (cartM H (s₀, t)).2.1) ∉ cartPl := fun h =>
      hns ((mem_cartS₂_iff _).2 ⟨h, hz⟩)
    have hAp : ((cartM H (s₀, t)).1, (cartM H (s₀, t)).2.1) ∈ cartAp := by
      rcases cartPl_trichotomy ((cartM H (s₀, t)).1, (cartM H (s₀, t)).2.1) with h | h | h
      · exact absurd h hPl
      · exact h
      · exact absurd h hAm
    refine ⟨hAp, ?_⟩
    rcases hAp with ⟨h, -⟩ | ⟨-, h⟩
    · exact h
    · have := (abs_lt.1 (hstrip s₀ t le_rfl hs₀1.le t.2.1 t.2.2)).2
      simp only at h; linarith
  obtain ⟨m, hm, hmT⟩ : ∃ m > 0, ∀ t ∈ T, m ≤ |(cartM H (s₀, t)).1| := by
    rcases T.eq_empty_or_nonempty with he | hne
    · exact ⟨1, one_pos, fun t ht => by rw [he] at ht; exact ht.elim⟩
    · obtain ⟨t₀, ht₀, hmin⟩ := hTc.isCompact.exists_isMinOn hne
        (continuous_abs.comp (continuous_fst.comp hMt)).continuousOn
      exact ⟨_, abs_pos.2 (hTAp t₀ ht₀).2, fun t ht => hmin ht⟩
  -- Step C: the cuts, where `sin (1/x) = 1`
  obtain ⟨k, hk⟩ := exists_nat_gt (1 / m)
  have hpi := Real.pi_pos
  have hpi3 := Real.pi_gt_three
  have hk0 : (0 : ℝ) ≤ k := k.cast_nonneg
  set ε₁ : ℝ := 1 / (Real.pi / 2 + k * (2 * Real.pi)) with hε₁def
  set ε₂ : ℝ := 1 / (3 * Real.pi / 2 + k * (2 * Real.pi)) with hε₂def
  have hε₁ : 0 < ε₁ := by positivity
  have hε₂ : 0 < ε₂ := by positivity
  have hsin₁ : Real.sin (1 / ε₁) = 1 := by
    rw [hε₁def, one_div_one_div, Real.sin_add_nat_mul_two_pi, Real.sin_pi_div_two]
  have hsin₂ : Real.sin (1 / -ε₂) = 1 := by
    rw [one_div_neg_eq_neg_one_div, hε₂def, one_div_one_div, Real.sin_neg,
      Real.sin_add_nat_mul_two_pi]
    have : 3 * Real.pi / 2 = Real.pi / 2 + Real.pi := by ring
    rw [this, Real.sin_add_pi, Real.sin_pi_div_two]; ring
  have hkk : (k : ℝ) ≤ k * (2 * Real.pi) := by nlinarith
  have hε₁m : ε₁ < m := by
    rw [hε₁def]; exact (one_div_lt (by positivity) hm).2 (by linarith)
  have hε₂m : ε₂ < m := by
    rw [hε₂def]; exact (one_div_lt (by positivity) hm).2 (by linarith)
  have hTW : ∀ t ∈ T, ((cartM H (s₀, t)).1, (cartM H (s₀, t)).2.1) ∈ cartW ε₁ ε₂ := by
    intro t ht
    refine ⟨(hTAp t ht).1, hstrip s₀ t le_rfl hs₀1.le t.2.1 t.2.2, ?_⟩
    have := hmT t ht
    simp only
    rcases le_or_gt 0 (cartM H (s₀, t)).1 with h | h
    · left; rw [abs_of_nonneg h] at this; linarith
    · right; rw [abs_of_neg h] at this; linarith
  -- Step D: a time `s₁ ≥ s₀` at which the loop is in a ball missing the pockets
  obtain ⟨s₁', -, hs₁'1, hsm₁⟩ := cartM_small H (min ε₁ ε₂) (lt_min hε₁ hε₂)
  set s₁ := max s₀ s₁' with hs₁def
  have hs₁0 : s₀ ≤ s₁ := le_max_left _ _
  have hs₁1 : s₁ < 1 := max_lt hs₀1 hs₁'1
  have hnotW : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      ((cartM H (s₁, t)).1, (cartM H (s₁, t)).2.1) ∉ cartW ε₁ ε₂ := by
    rintro t h0 h1 ⟨-, -, hx⟩
    have := hsm₁ s₁ t (le_max_right _ _) hs₁1.le h0 h1
    have h5 : ‖(cartM H (s₁, t)).1‖ ≤ ‖cartM H (s₁, t)‖ := norm_fst_le _
    rw [Real.norm_eq_abs] at h5
    have h7 := min_le_left ε₁ ε₂
    have h8 := min_le_right ε₁ ε₂
    simp only at hx
    rcases hx with hx | hx
    · have := le_abs_self (cartM H (s₁, t)).1; linarith
    · have := neg_abs_le (cartM H (s₁, t)).1; linarith
  -- Step E₀: the winding of `F₀` at time `0`, through the principal logarithm
  have hslit0 : ∀ t : I, cartF₀ (cartM H (0, t)) ∈ Complex.slitPlane := by
    intro t
    obtain ⟨u₁, u₂, he, hu₁, hu₂0, hu₂1, -⟩ := cartM_frame H le_rfl zero_le_one t.2.1 t.2.2
    have hu₁0 : u₁ = 0 := Subtype.ext (le_antisymm hu₁ u₁.2.1)
    rw [he, hu₁0, H.apply_zero]
    exact cartF₀_cartγ_mem_slitPlane (by linarith) (by linarith)
  have hc0 : Continuous fun t : I => cartF₀ (cartM H (0, t)) :=
    continuous_cartF₀.comp (hMc.comp (continuous_const.prodMk continuous_subtype_val))
  let Λa : C(I, ℂ) := ⟨fun t => Complex.log (cartF₀ (cartM H (0, t))), hc0.clog hslit0⟩
  -- Step E₁: from time `0` to time `s₀`
  have hne₀ : ∀ s t : ℝ, 0 ≤ s → s < 1 → 0 ≤ t → t ≤ 1 → cartF₀ (cartM H (s, t)) ≠ 0 :=
    fun s t h0 h1 h2 h3 => cartF₀_ne_zero (cartM_not_mem H hH h0 h1 h2 h3)
  have hneW : ∀ s t : ℝ, 0 ≤ s → s < 1 → 0 ≤ t → t ≤ 1 → cartFW ε₁ ε₂ (cartM H (s, t)) ≠ 0 :=
    fun s t h0 h1 h2 h3 => cartFW_ne_zero (cartM_not_mem H hH h0 h1 h2 h3)
  obtain ⟨Λb, hΛb⟩ := exists_expLift ⟨fun t : I => (⟨cartF₀ (cartM H (s₀, t)),
    hne₀ s₀ t hs₀0 hs₀1 t.2.1 t.2.2⟩ : CStar), (continuous_cartF₀.comp hMt).subtype_mk _⟩
  have hΛb' : ∀ t, Complex.exp (Λb t) = cartF₀ (cartM H (s₀, t)) := hΛb
  have e1 : Λa 1 - Λa 0 = Λb 1 - Λb 0 := by
    have hs : ∀ σ' : I, 0 ≤ (σ' : ℝ) * s₀ ∧ (σ' : ℝ) * s₀ < 1 := fun σ' =>
      ⟨mul_nonneg σ'.2.1 hs₀0, by nlinarith [σ'.2.2]⟩
    refine wind_const_family (w := fun z : I × I => cartF₀ (cartM H ((z.1 : ℝ) * s₀, z.2)))
      (continuous_cartF₀.comp (hMc.comp (((continuous_subtype_val.comp continuous_fst).mul
        continuous_const).prodMk (continuous_subtype_val.comp continuous_snd))))
      (fun z => hne₀ _ _ (hs z.1).1 (hs z.1).2 z.2.2.1 z.2.2.2)
      (fun σ' => by
        simp only [Icc.coe_one, Icc.coe_zero]
        rw [hF₀1 _ (hs σ').1 (hs σ').2, hF₀0 _ (hs σ').1 (hs σ').2])
      (fun σ' => by
        simp only [Icc.coe_zero]
        rw [hF₀0 _ (hs σ').1 (hs σ').2]
        simpa using (hE _ (hs σ').1 (hs σ').2).2.1.ne') (fun t => ?_) (fun t => ?_)
    · simp only [Icc.coe_zero, zero_mul, Λa, ContinuousMap.coe_mk]
      exact Complex.exp_log (hne₀ 0 t le_rfl one_pos t.2.1 t.2.2)
    · simp only [Icc.coe_one, one_mul]; exact hΛb' t
  -- Step E₂: at time `s₀`, `F₀` and `F*` have the same winding
  have hcW : Continuous fun t : I => cartFW ε₁ ε₂ (cartM H (s₀, t)) :=
    (continuousOn_cartFW hsin₁ hsin₂).comp_continuous hMt
      fun t => hstrip s₀ t le_rfl hs₀1.le t.2.1 t.2.2
  have hrslit : ∀ t : I, cartFW ε₁ ε₂ (cartM H (s₀, t)) / cartF₀ (cartM H (s₀, t)) ∈
      Complex.slitPlane := by
    intro t
    refine div_mem_slitPlane_of_sameSign ?_ (hne₀ s₀ t hs₀0 hs₀1 t.2.1 t.2.2)
    intro hz
    have hns := cartM_not_mem H hH hs₀0 hs₀1 t.2.1 t.2.2
    have hPl : ((cartM H (s₀, t)).1, (cartM H (s₀, t)).2.1) ∉ cartPl := fun h =>
      hns ((mem_cartS₂_iff _).2 ⟨h, hz⟩)
    rcases cartPl_trichotomy ((cartM H (s₀, t)).1, (cartM H (s₀, t)).2.1) with h | h | h
    · exact absurd h hPl
    · exact mul_pos (cartPsi_pos h) (cartPsiW_pos (hTW t ⟨hz, not_mem_cartAm_of_mem_cartAp h⟩))
    · exact mul_pos_of_neg_of_neg (cartPsi_neg h)
        (cartPsiW_neg (fun hW => not_mem_cartAm_of_mem_cartAp hW.1 h) hPl)
  let Λc : C(I, ℂ) := ⟨fun t => Λb t + Complex.log (cartFW ε₁ ε₂ (cartM H (s₀, t)) /
    cartF₀ (cartM H (s₀, t))), Λb.continuous.add ((hcW.div (continuous_cartF₀.comp hMt)
      fun t => hne₀ s₀ t hs₀0 hs₀1 t.2.1 t.2.2).clog hrslit)⟩
  have hΛc : ∀ t, Complex.exp (Λc t) = cartFW ε₁ ε₂ (cartM H (s₀, t)) := by
    intro t
    simp only [Λc, ContinuousMap.coe_mk]
    rw [Complex.exp_add, hΛb', Complex.exp_log (Complex.slitPlane_ne_zero (hrslit t)),
      mul_div_cancel₀ _ (hne₀ s₀ t hs₀0 hs₀1 t.2.1 t.2.2)]
  have e2 : Λc 1 - Λc 0 = Λb 1 - Λb 0 := by
    have r0 : cartFW ε₁ ε₂ (cartM H (s₀, ((0 : I) : ℝ))) / cartF₀ (cartM H (s₀, ((0 : I) : ℝ)))
        = 1 := by
      rw [Icc.coe_zero, hFW0 _ _ s₀ hs₀0 hs₀1, ← hF₀0 s₀ hs₀0 hs₀1]
      exact div_self (hne₀ s₀ 0 hs₀0 hs₀1 le_rfl zero_le_one)
    have r1 : cartFW ε₁ ε₂ (cartM H (s₀, ((1 : I) : ℝ))) / cartF₀ (cartM H (s₀, ((1 : I) : ℝ)))
        = 1 := by
      rw [Icc.coe_one, hFW1 _ _ s₀ hs₀0 hs₀1, ← hF₀1 s₀ hs₀0 hs₀1]
      exact div_self (hne₀ s₀ 1 hs₀0 hs₀1 zero_le_one le_rfl)
    simp only [Λc, ContinuousMap.coe_mk, r0, r1, Complex.log_one, add_zero]
  -- Step E₃: from time `s₀` to time `s₁`, the winding of `F*` is constant
  have hs' : ∀ σ' : I, s₀ ≤ s₀ + (σ' : ℝ) * (s₁ - s₀) ∧ s₀ + (σ' : ℝ) * (s₁ - s₀) ≤ s₁ :=
    fun σ' => ⟨by nlinarith [σ'.2.1], by nlinarith [σ'.2.2]⟩
  have hd1 : Continuous fun t : I => cartFW ε₁ ε₂ (cartM H (s₁, t)) :=
    (continuousOn_cartFW hsin₁ hsin₂).comp_continuous
      (hMc.comp (continuous_const.prodMk continuous_subtype_val))
      fun t => hstrip s₁ t hs₁0 hs₁1.le t.2.1 t.2.2
  have hdslit : ∀ t : I, -cartFW ε₁ ε₂ (cartM H (s₁, t)) ∈ Complex.slitPlane := by
    intro t
    rw [Complex.mem_slitPlane_iff, Complex.neg_re, Complex.neg_im, cartFW_re, cartFW_im]
    by_cases hz : (cartM H (s₁, t)).2.2 = 0
    · left
      have hns := cartM_not_mem H hH (hs₀0.trans hs₁0) hs₁1 t.2.1 t.2.2
      have hPl : ((cartM H (s₁, t)).1, (cartM H (s₁, t)).2.1) ∉ cartPl := fun h =>
        hns ((mem_cartS₂_iff _).2 ⟨h, hz⟩)
      linarith [cartPsiW_neg (hnotW t t.2.1 t.2.2) hPl]
    · right; exact neg_ne_zero.2 hz
  let Λd : C(I, ℂ) := ⟨fun t => Complex.log (-cartFW ε₁ ε₂ (cartM H (s₁, t))) +
    (Real.pi : ℂ) * Complex.I, (hd1.neg.clog hdslit).add continuous_const⟩
  have e3 : Λc 1 - Λc 0 = Λd 1 - Λd 0 := by
    refine wind_const_family
      (w := fun z : I × I => cartFW ε₁ ε₂ (cartM H (s₀ + (z.1 : ℝ) * (s₁ - s₀), z.2)))
      ((continuousOn_cartFW hsin₁ hsin₂).comp_continuous (hMc.comp ((continuous_const.add
        ((continuous_subtype_val.comp continuous_fst).mul continuous_const)).prodMk
          (continuous_subtype_val.comp continuous_snd)))
        fun z => hstrip _ _ (hs' z.1).1 ((hs' z.1).2.trans hs₁1.le) z.2.2.1 z.2.2.2)
      (fun z => hneW _ _ (hs₀0.trans (hs' z.1).1) ((hs' z.1).2.trans_lt hs₁1) z.2.2.1 z.2.2.2)
      (fun σ' => by
        simp only [Icc.coe_one, Icc.coe_zero]
        rw [hFW1 _ _ _ (hs₀0.trans (hs' σ').1) ((hs' σ').2.trans_lt hs₁1),
          hFW0 _ _ _ (hs₀0.trans (hs' σ').1) ((hs' σ').2.trans_lt hs₁1)])
      (fun σ' => by
        simp only [Icc.coe_zero]
        rw [hFW0 _ _ _ (hs₀0.trans (hs' σ').1) ((hs' σ').2.trans_lt hs₁1)]
        simpa using (hE _ (hs₀0.trans (hs' σ').1) ((hs' σ').2.trans_lt hs₁1)).2.1.ne')
      (fun t => ?_) (fun t => ?_)
    · simp only [Icc.coe_zero, zero_mul, add_zero]; exact hΛc t
    · simp only [Icc.coe_one, one_mul, add_sub_cancel]
      simp only [Λd, ContinuousMap.coe_mk]
      rw [Complex.exp_add, Complex.exp_log (Complex.slitPlane_ne_zero (hdslit t)),
        Complex.exp_pi_mul_I]
      ring
  -- the contradiction: `-π = π`
  have key : Λa 1 - Λa 0 = Λd 1 - Λd 0 := by rw [e1, ← e2, e3]
  have hz0 := (hE 0 le_rfl one_pos).2.1
  have hz1 := (hE s₁ (hs₀0.trans hs₁0) hs₁1).2.1
  have ha : (Λa 1 - Λa 0).im = -Real.pi := by
    simp only [Λa, ContinuousMap.coe_mk, Icc.coe_one, Icc.coe_zero]
    rw [hF₀1 0 le_rfl one_pos, hF₀0 0 le_rfl one_pos, Complex.sub_im, Complex.log_im,
      Complex.log_im, arg_neg_ofReal_mul_I hz0, arg_ofReal_mul_I hz0]
    ring
  have hd : (Λd 1 - Λd 0).im = Real.pi := by
    simp only [Λd, ContinuousMap.coe_mk, Icc.coe_one, Icc.coe_zero]
    rw [hFW1 _ _ s₁ (hs₀0.trans hs₁0) hs₁1, hFW0 _ _ s₁ (hs₀0.trans hs₁0) hs₁1, neg_neg,
      add_sub_add_right_eq_sub, Complex.sub_im, Complex.log_im, Complex.log_im,
      arg_ofReal_mul_I hz1, arg_neg_ofReal_mul_I hz1]
    ring
  have := congrArg Complex.im key
  rw [ha, hd] at this
  linarith

/-! #### The first claim for `S₂`: `ℝ³ ∖ S₂` is homotopy equivalent to `ℝ³ ∖ S₁`

The deformation `(x, y, z) ↦ (x, y + 2s ψ/(|ψ| + |z|), z)` pushes the plane points of `A₊` up and
those of `A₋` down, off the strip `ℝ × [-1, 1] × {0}`; the radial expansion
`(x, w) ↦ (x, (1 + s/|w|) w)` (`w = (y, z)`) pushes `ℝ³ ∖ S₁` into the complement `Y'` of that
strip; both preserve `Y'`. -/

/-- `Y'`: the complement of the strip `ℝ × [-1, 1] × {0}`. -/
def cartYp : Set (ℝ × ℝ × ℝ) := {q | q.2.2 ≠ 0 ∨ 1 < |q.2.1|}

theorem cartYp_subset_S₂ {q : ℝ × ℝ × ℝ} (h : q ∈ cartYp) : q ∉ cartS₂ := by
  rw [mem_cartS₂_iff]
  rintro ⟨hP, hz⟩
  rcases h with h | h
  · exact h hz
  · rcases hP with ⟨-, hy⟩ | ⟨-, hy⟩
    · simp only at hy; rw [hy] at h; linarith [Real.abs_sin_le_one (1 / q.1)]
    · simp only at hy; linarith

theorem cartYp_subset_S₁ {q : ℝ × ℝ × ℝ} (h : q ∈ cartYp) : q ∉ cartS₁ := by
  rintro ⟨hy, hz⟩
  rcases h with h | h
  · exact h hz
  · rw [hy, abs_zero] at h; linarith

theorem cartAp_up {p : ℝ × ℝ} (h : p ∈ cartAp) {y' : ℝ} (hy : p.2 ≤ y') : (p.1, y') ∈ cartAp := by
  rcases h with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · exact Or.inl ⟨h0, by simp only; linarith⟩
  · exact Or.inr ⟨h0, by simp only; linarith⟩

theorem cartAm_down {p : ℝ × ℝ} (h : p ∈ cartAm) {y' : ℝ} (hy : y' ≤ p.2) : (p.1, y') ∈ cartAm := by
  rcases h with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · exact Or.inl ⟨h0, by simp only; linarith⟩
  · exact Or.inr ⟨h0, by simp only; linarith⟩

theorem cartAp_gt {p : ℝ × ℝ} (h : p ∈ cartAp) : -1 < p.2 := by
  rcases h with ⟨-, h1⟩ | ⟨-, h1⟩
  · linarith [Real.neg_one_le_sin (1 / p.1)]
  · linarith

theorem cartAm_lt {p : ℝ × ℝ} (h : p ∈ cartAm) : p.2 < 1 := by
  rcases h with ⟨-, h1⟩ | ⟨-, h1⟩
  · linarith [Real.sin_le_one (1 / p.1)]
  · linarith

theorem mem_cartAp_of_one_lt {p : ℝ × ℝ} (h : 1 < p.2) : p ∈ cartAp := by
  by_cases h0 : p.1 = 0
  · exact Or.inr ⟨h0, h⟩
  · exact Or.inl ⟨h0, lt_of_le_of_lt (Real.sin_le_one _) h⟩

theorem mem_cartAm_of_lt_neg_one {p : ℝ × ℝ} (h : p.2 < -1) : p ∈ cartAm := by
  by_cases h0 : p.1 = 0
  · exact Or.inr ⟨h0, h⟩
  · exact Or.inl ⟨h0, lt_of_lt_of_le h (Real.neg_one_le_sin _)⟩

theorem cart_den_pos {q : ℝ × ℝ × ℝ} (hq : q ∉ cartS₂) :
    0 < |cartPsi (q.1, q.2.1)| + |q.2.2| := by
  rcases (add_nonneg (abs_nonneg (cartPsi (q.1, q.2.1))) (abs_nonneg q.2.2)).lt_or_eq with h | h
  · exact h
  · exfalso
    apply cartF₀_ne_zero hq
    have a1 := abs_nonneg (cartPsi (q.1, q.2.1))
    have a2 := abs_nonneg q.2.2
    have h1 : |cartPsi (q.1, q.2.1)| = 0 := by linarith
    have h2 : |q.2.2| = 0 := by linarith
    apply Complex.ext <;> simp [abs_eq_zero.1 h1, abs_eq_zero.1 h2]

/-- The vertical shift `2ψ/(|ψ| + |z|)`. -/
def cartShift (q : ℝ × ℝ × ℝ) : ℝ := 2 * cartPsi (q.1, q.2.1) / (|cartPsi (q.1, q.2.1)| + |q.2.2|)

/-- The deformation `Φ_s`. -/
def cartΦ (s : ℝ) (q : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ := (q.1, q.2.1 + s * cartShift q, q.2.2)

theorem cartShift_plane {q : ℝ × ℝ × ℝ} (hq : q ∉ cartS₂) (hz : q.2.2 = 0) :
    ((q.1, q.2.1) ∈ cartAp ∧ cartShift q = 2) ∨ ((q.1, q.2.1) ∈ cartAm ∧ cartShift q = -2) := by
  have hPl : (q.1, q.2.1) ∉ cartPl := fun h => hq ((mem_cartS₂_iff _).2 ⟨h, hz⟩)
  rcases cartPl_trichotomy (q.1, q.2.1) with h | h | h
  · exact absurd h hPl
  · left
    refine ⟨h, ?_⟩
    have := cartPsi_pos h
    rw [cartShift, hz, abs_zero, add_zero, abs_of_pos this, mul_div_assoc, div_self this.ne']
    ring
  · right
    refine ⟨h, ?_⟩
    have := cartPsi_neg h
    rw [cartShift, hz, abs_zero, add_zero, abs_of_neg this, mul_div_assoc, div_neg,
      div_self this.ne]
    ring

theorem cartΦ_not_mem {s : ℝ} (hs : 0 ≤ s) {q : ℝ × ℝ × ℝ} (hq : q ∉ cartS₂) :
    cartΦ s q ∉ cartS₂ := by
  rw [mem_cartS₂_iff]
  rintro ⟨hP, hz⟩
  simp only [cartΦ] at hP hz
  rcases cartShift_plane hq hz with ⟨h, h2⟩ | ⟨h, h2⟩
  · rw [h2] at hP
    exact not_mem_cartPl_of_mem_cartAp (cartAp_up h (y' := q.2.1 + s * 2) (by simp only; linarith)) hP
  · rw [h2] at hP
    exact not_mem_cartPl_of_mem_cartAm (cartAm_down h (y' := q.2.1 + s * -2) (by simp only; linarith))
      hP

theorem cartΦ_one_mem {q : ℝ × ℝ × ℝ} (hq : q ∉ cartS₂) : cartΦ 1 q ∈ cartYp := by
  by_cases hz : q.2.2 = 0
  · right
    simp only [cartΦ]
    rcases cartShift_plane hq hz with ⟨h, h2⟩ | ⟨h, h2⟩
    · rw [h2]; have := cartAp_gt h; simp only at this
      rw [abs_of_pos (by linarith)]; linarith
    · rw [h2]; have := cartAm_lt h; simp only at this
      rw [abs_of_neg (by linarith)]; linarith
  · exact Or.inl hz

theorem cartΦ_mem {s : ℝ} (hs : 0 ≤ s) {q : ℝ × ℝ × ℝ} (hq : q ∈ cartYp) : cartΦ s q ∈ cartYp := by
  rcases hq with hz | hy
  · exact Or.inl hz
  by_cases hz : q.2.2 = 0
  · right
    simp only [cartΦ]
    rcases cartShift_plane (cartYp_subset_S₂ (Or.inr hy)) hz with ⟨h, h2⟩ | ⟨h, h2⟩
    · rw [h2]
      rcases lt_abs.1 hy with hy' | hy'
      · rw [abs_of_pos (by linarith)]; linarith
      · exact absurd (mem_cartAm_of_lt_neg_one (p := (q.1, q.2.1)) (by simp only; linarith))
          (not_mem_cartAm_of_mem_cartAp h)
    · rw [h2]
      rcases lt_abs.1 hy with hy' | hy'
      · exact absurd (mem_cartAp_of_one_lt (p := (q.1, q.2.1)) hy')
          (fun h' => not_mem_cartAm_of_mem_cartAp h' h)
      · rw [abs_of_neg (by linarith)]; linarith
  · exact Or.inl hz

/-- The norm `|w|` of `w = (y, z)`. -/
def cartRho (q : ℝ × ℝ × ℝ) : ℝ := Real.sqrt (q.2.1 ^ 2 + q.2.2 ^ 2)

theorem cartRho_pos {q : ℝ × ℝ × ℝ} (hq : q ∉ cartS₁) : 0 < cartRho q := by
  apply Real.sqrt_pos.2
  by_contra h
  apply hq
  have h1 := sq_nonneg q.2.1
  have h2 := sq_nonneg q.2.2
  exact ⟨pow_eq_zero_iff (n := 2) two_ne_zero |>.1 (by linarith),
    pow_eq_zero_iff (n := 2) two_ne_zero |>.1 (by linarith)⟩

/-- The radial expansion `r_s`. -/
def cartR (s : ℝ) (q : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (q.1, (1 + s / cartRho q) * q.2.1, (1 + s / cartRho q) * q.2.2)

theorem cartR_not_mem {s : ℝ} (hs : 0 ≤ s) {q : ℝ × ℝ × ℝ} (hq : q ∉ cartS₁) :
    cartR s q ∉ cartS₁ := by
  have hf : 0 < 1 + s / cartRho q := by have := cartRho_pos hq; positivity
  rintro ⟨h1, h2⟩
  simp only [cartR] at h1 h2
  exact hq ⟨(mul_eq_zero.1 h1).resolve_left hf.ne', (mul_eq_zero.1 h2).resolve_left hf.ne'⟩

theorem cartR_mem {s : ℝ} (hs : 0 ≤ s) {q : ℝ × ℝ × ℝ} (hq : q ∈ cartYp) : cartR s q ∈ cartYp := by
  have hρ := cartRho_pos (cartYp_subset_S₁ hq)
  have hf : 1 ≤ 1 + s / cartRho q := by have : 0 ≤ s / cartRho q := by positivity
                                        linarith
  rcases hq with hz | hy
  · exact Or.inl (by simp only [cartR]; exact mul_ne_zero (by linarith) hz)
  · right
    simp only [cartR]
    rw [abs_mul, abs_of_pos (by linarith)]
    nlinarith [abs_nonneg q.2.1]

theorem cartR_one_mem {q : ℝ × ℝ × ℝ} (hq : q ∉ cartS₁) : cartR 1 q ∈ cartYp := by
  by_cases hz : q.2.2 = 0
  · right
    have hy : q.2.1 ≠ 0 := fun hy => hq ⟨hy, hz⟩
    have hρ : cartRho q = |q.2.1| := by
      rw [cartRho, hz]; simp [Real.sqrt_sq_eq_abs]
    simp only [cartR]
    rw [hρ, abs_mul, abs_of_pos (by have := abs_pos.2 hy; positivity)]
    have := abs_pos.2 hy
    rw [add_mul, one_mul, div_mul_cancel₀ _ this.ne']
    linarith
  · left
    have hf : 0 < 1 + 1 / cartRho q := by have := cartRho_pos hq; positivity
    simp only [cartR]; exact mul_ne_zero hf.ne' hz

/-- `S₂ᶜ` as a type. -/
abbrev CartS2c : Type := (cartS₂ᶜ : Set (ℝ × ℝ × ℝ))
/-- `S₁ᶜ` as a type. -/
abbrev CartS1c : Type := (cartS₁ᶜ : Set (ℝ × ℝ × ℝ))

theorem continuous_cartShift_S2c : Continuous fun q : CartS2c => cartShift q.1 := by
  have hψ : Continuous fun q : CartS2c => cartPsi (q.1.1, q.1.2.1) :=
    continuous_cartPsi.comp ((continuous_fst.comp continuous_subtype_val).prodMk
      ((continuous_fst.comp continuous_snd).comp continuous_subtype_val))
  have hz : Continuous fun q : CartS2c => q.1.2.2 :=
    (continuous_snd.comp continuous_snd).comp continuous_subtype_val
  exact (continuous_const.mul hψ).div (hψ.abs.add hz.abs) fun q => (cart_den_pos q.2).ne'

theorem continuous_cartRho_S1c : Continuous fun q : CartS1c => cartRho q.1 := by
  unfold cartRho; fun_prop

/-- `κ = Φ₁ : ℝ³ ∖ S₂ → ℝ³ ∖ S₁`. -/
def cartKappa : C(CartS2c, CartS1c) :=
  ⟨fun q => ⟨cartΦ 1 q.1, cartYp_subset_S₁ (cartΦ_one_mem q.2)⟩, by
    refine Continuous.subtype_mk ?_ _
    have := continuous_cartShift_S2c
    unfold cartΦ; fun_prop⟩

/-- `λ = r₁ : ℝ³ ∖ S₁ → ℝ³ ∖ S₂`. -/
def cartLambda : C(CartS1c, CartS2c) :=
  ⟨fun q => ⟨cartR 1 q.1, cartYp_subset_S₂ (cartR_one_mem q.2)⟩, by
    refine Continuous.subtype_mk ?_ _
    have := continuous_cartRho_S1c
    have hρ : ∀ q : CartS1c, cartRho q.1 ≠ 0 := fun q => (cartRho_pos q.2).ne'
    unfold cartR
    refine (continuous_fst.comp continuous_subtype_val).prodMk
      (((continuous_const.add (continuous_const.div this hρ)).mul
        ((continuous_fst.comp continuous_snd).comp continuous_subtype_val)).prodMk
      ((continuous_const.add (continuous_const.div this hρ)).mul
        ((continuous_snd.comp continuous_snd).comp continuous_subtype_val)))⟩

/-- A homotopy equivalence induces isomorphisms of fundamental groups. -/
noncomputable def fgMulEquivOfHomotopyEquiv {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    (e : ContinuousMap.HomotopyEquiv A B) (a : A) :
    FundamentalGroup A a ≃* FundamentalGroup B (e.toFun a) :=
  (FundamentalGroupoidFunctor.equivOfHomotopyEquiv e).fullyFaithfulFunctor.mulEquivEnd
    (FundamentalGroupoid.mk a : FundamentalGroupoid (TopCat.of A))

theorem continuous_cartΦ_one : Continuous fun q : CartS2c => cartΦ 1 q.1 := by
  have := continuous_cartShift_S2c
  unfold cartΦ; fun_prop

theorem continuous_cartR_one : Continuous fun q : CartS1c => cartR 1 q.1 :=
  continuous_subtype_val.comp cartLambda.continuous

/-- **`ℝ³ ∖ S₂ ≃ₕ ℝ³ ∖ S₁`**, by `κ = Φ₁` and `λ = r₁`. -/
noncomputable def cartHE : ContinuousMap.HomotopyEquiv CartS2c CartS1c where
  toFun := cartKappa
  invFun := cartLambda
  left_inv := by
    let Φ₁ : C(CartS2c, CartS2c) :=
      ⟨fun q => ⟨cartΦ 1 q.1, cartΦ_not_mem zero_le_one q.2⟩,
        continuous_cartΦ_one.subtype_mk _⟩
    let Ha : ContinuousMap.Homotopy (ContinuousMap.id CartS2c) Φ₁ :=
      { toFun := fun z => ⟨cartΦ z.1 z.2.1, cartΦ_not_mem z.1.2.1 z.2.2⟩
        continuous_toFun := by
          refine Continuous.subtype_mk ?_ _
          have h1 : Continuous fun z : I × CartS2c => cartShift z.2.1 :=
            continuous_cartShift_S2c.comp continuous_snd
          unfold cartΦ; fun_prop
        map_zero_left := fun q => Subtype.ext (by simp [cartΦ])
        map_one_left := fun q => rfl }
    have hρ : Continuous fun z : I × CartS2c => cartRho (cartΦ 1 z.2.1) :=
      continuous_cartRho_S1c.comp (cartKappa.continuous.comp continuous_snd)
    have hρ0 : ∀ z : I × CartS2c, cartRho (cartΦ 1 z.2.1) ≠ 0 := fun z =>
      (cartRho_pos (cartKappa z.2).2).ne'
    let Hb : ContinuousMap.Homotopy Φ₁ (cartLambda.comp cartKappa) :=
      { toFun := fun z => ⟨cartR z.1 (cartΦ 1 z.2.1),
          cartYp_subset_S₂ (cartR_mem z.1.2.1 (cartΦ_one_mem z.2.2))⟩
        continuous_toFun := by
          refine Continuous.subtype_mk ?_ _
          have h2 : Continuous fun z : I × CartS2c => cartΦ 1 z.2.1 :=
            continuous_cartΦ_one.comp continuous_snd
          have hs : Continuous fun z : I × CartS2c => ((z.1 : I) : ℝ) :=
            continuous_subtype_val.comp continuous_fst
          refine (continuous_fst.comp h2).prodMk
            (((continuous_const.add (hs.div hρ hρ0)).mul
              ((continuous_fst.comp continuous_snd).comp h2)).prodMk
            ((continuous_const.add (hs.div hρ hρ0)).mul
              ((continuous_snd.comp continuous_snd).comp h2)))
        map_zero_left := fun q => Subtype.ext (by simp [cartR]; rfl)
        map_one_left := fun q => rfl }
    exact ⟨(Ha.trans Hb).symm⟩
  right_inv := by
    let R₁ : C(CartS1c, CartS1c) :=
      ⟨fun q => ⟨cartR 1 q.1, cartR_not_mem zero_le_one q.2⟩,
        continuous_cartR_one.subtype_mk _⟩
    have hρ : Continuous fun z : I × CartS1c => cartRho z.2.1 :=
      continuous_cartRho_S1c.comp continuous_snd
    have hρ0 : ∀ z : I × CartS1c, cartRho z.2.1 ≠ 0 := fun z => (cartRho_pos z.2.2).ne'
    let Hc : ContinuousMap.Homotopy (ContinuousMap.id CartS1c) R₁ :=
      { toFun := fun z => ⟨cartR z.1 z.2.1, cartR_not_mem z.1.2.1 z.2.2⟩
        continuous_toFun := by
          refine Continuous.subtype_mk ?_ _
          have h2 : Continuous fun z : I × CartS1c => z.2.1 :=
            continuous_subtype_val.comp continuous_snd
          have hs : Continuous fun z : I × CartS1c => ((z.1 : I) : ℝ) :=
            continuous_subtype_val.comp continuous_fst
          refine (continuous_fst.comp h2).prodMk
            (((continuous_const.add (hs.div hρ hρ0)).mul
              ((continuous_fst.comp continuous_snd).comp h2)).prodMk
            ((continuous_const.add (hs.div hρ hρ0)).mul
              ((continuous_snd.comp continuous_snd).comp h2)))
        map_zero_left := fun q => Subtype.ext (by simp [cartR])
        map_one_left := fun q => rfl }
    let Hd : ContinuousMap.Homotopy R₁ (cartKappa.comp cartLambda) :=
      { toFun := fun z => ⟨cartΦ z.1 (cartR 1 z.2.1),
          cartYp_subset_S₁ (cartΦ_mem z.1.2.1 (cartR_one_mem z.2.2))⟩
        continuous_toFun := by
          refine Continuous.subtype_mk ?_ _
          have h1 : Continuous fun z : I × CartS1c => cartShift (cartR 1 z.2.1) :=
            continuous_cartShift_S2c.comp (cartLambda.continuous.comp continuous_snd)
          have h2 : Continuous fun z : I × CartS1c => cartR 1 z.2.1 :=
            continuous_cartR_one.comp continuous_snd
          unfold cartΦ; fun_prop
        map_zero_left := fun q => Subtype.ext (by simp [cartΦ]; rfl)
        map_one_left := fun q => rfl }
    exact ⟨(Hc.trans Hd).symm⟩

/-- **`ex:consider_carthesian_coordinates_usual`, first claim for `S₂`** (`RamcovGX.tex:1218`):
`π₁(ℝ³ ∖ S₂) ≅ ℤ` at every base point, by the number of turns around `S₂` (through the homotopy
equivalence `GX.cartHE` with `ℝ³ ∖ S₁` and `GX.cartDeg`). -/
theorem carthesian_piOne_S₂ : CartPiOneZ cartS₂ := fun y =>
  ⟨(fgMulEquivOfHomotopyEquiv cartHE y).trans
    (MulEquiv.ofBijective (cartDeg (cartKappa y)) (cartDeg_bijective _))⟩

/-! #### The third claim for `S₂`: every loop of `Ω(O,O,Y ∖ S₂)` is almost trivial -/

theorem cart_norm_lt {q : ℝ × ℝ × ℝ} {r : ℝ} :
    q ∈ Metric.ball cartO r ↔ |q.1| < r ∧ |q.2.1| < r ∧ |q.2.2| < r := by
  rw [Metric.mem_ball]
  show dist q 0 < r ↔ _
  rw [dist_zero_right, Prod.norm_def, Prod.norm_def, Real.norm_eq_abs,
    Real.norm_eq_abs, Real.norm_eq_abs, max_lt_iff, max_lt_iff]

/-- Two points of `B ∖ S₂`, the first above the plane and the second not below it, are joined by
the segment. -/
theorem cart_joined_pos {r : ℝ} {a b : ℝ × ℝ × ℝ} (ha : a ∈ Metric.ball cartO r ∩ cartS₂ᶜ)
    (hb : b ∈ Metric.ball cartO r ∩ cartS₂ᶜ) (hz : 0 < a.2.2) (hz' : 0 ≤ b.2.2) :
    JoinedIn (Metric.ball cartO r ∩ cartS₂ᶜ) a b := by
  refine JoinedIn.of_segment_subset fun e he => ⟨(convex_ball _ _).segment_subset ha.1 hb.1 he, ?_⟩
  obtain ⟨u, v, hu, hv, huv, rfl⟩ := he
  rcases eq_or_lt_of_le (show v ≤ 1 by linarith) with h | h
  · have hu0 : u = 0 := by linarith
    rw [h, hu0, zero_smul, one_smul, zero_add]; exact hb.2
  · intro hS
    have hz0 := ((mem_cartS₂_iff _).1 hS).2
    simp only [Prod.smul_snd, Prod.snd_add, smul_eq_mul] at hz0
    nlinarith

theorem cart_joined_neg {r : ℝ} {a b : ℝ × ℝ × ℝ} (ha : a ∈ Metric.ball cartO r ∩ cartS₂ᶜ)
    (hb : b ∈ Metric.ball cartO r ∩ cartS₂ᶜ) (hz : a.2.2 < 0) (hz' : b.2.2 ≤ 0) :
    JoinedIn (Metric.ball cartO r ∩ cartS₂ᶜ) a b := by
  refine JoinedIn.of_segment_subset fun e he => ⟨(convex_ball _ _).segment_subset ha.1 hb.1 he, ?_⟩
  obtain ⟨u, v, hu, hv, huv, rfl⟩ := he
  rcases eq_or_lt_of_le (show v ≤ 1 by linarith) with h | h
  · have hu0 : u = 0 := by linarith
    rw [h, hu0, zero_smul, one_smul, zero_add]; exact hb.2
  · intro hS
    have hz0 := ((mem_cartS₂_iff _).1 hS).2
    simp only [Prod.smul_snd, Prod.snd_add, smul_eq_mul] at hz0
    nlinarith

/-- `B(O, r) ∖ S₂` is path-connected. -/
theorem isPathConnected_ball_diff_cartS₂ {r : ℝ} (hr : 0 < r) :
    IsPathConnected (Metric.ball cartO r ∩ cartS₂ᶜ) := by
  set W := Metric.ball cartO r ∩ cartS₂ᶜ
  have hzS : ∀ q : ℝ × ℝ × ℝ, q.2.2 ≠ 0 → q ∉ cartS₂ := fun q hq hS =>
    hq ((mem_cartS₂_iff _).1 hS).2
  have hcp : ((0 : ℝ), (0 : ℝ), r / 2) ∈ W :=
    ⟨cart_norm_lt.2 ⟨by simp [hr], by simp [hr], by rw [abs_of_pos (by linarith)]; linarith⟩,
      hzS _ (by simp only; linarith)⟩
  have hr2 : |(-(r / 2) : ℝ)| < r := by rw [abs_neg, abs_of_pos (by linarith)]; linarith
  have hcm : ((0 : ℝ), (0 : ℝ), -(r / 2)) ∈ W :=
    ⟨cart_norm_lt.2 ⟨by simp [hr], by simp [hr], hr2⟩, hzS _ (by simp only; linarith)⟩
  -- a plane point of `A₋` near `O`
  obtain ⟨k, hk⟩ := exists_nat_gt (2 / r)
  have hpi := Real.pi_pos
  have hpi3 := Real.pi_gt_three
  have hk0 : (0 : ℝ) ≤ k := k.cast_nonneg
  set x₁ : ℝ := 1 / (Real.pi / 2 + k * (2 * Real.pi)) with hx₁
  have hx₁0 : 0 < x₁ := by positivity
  have hx₁r : x₁ < r := by
    rw [hx₁]
    refine (one_div_lt (by positivity) hr).2 ?_
    have : (k : ℝ) ≤ k * (2 * Real.pi) := by nlinarith
    have : 1 / r < 2 / r := by
      rw [div_lt_div_iff_of_pos_right hr]; norm_num
    linarith
  have hs₁ : Real.sin (1 / x₁) = 1 := by
    rw [hx₁, one_div_one_div, Real.sin_add_nat_mul_two_pi, Real.sin_pi_div_two]
  have hq₀ : (x₁, (0 : ℝ), (0 : ℝ)) ∈ W := by
    refine ⟨cart_norm_lt.2 ⟨by rw [abs_of_pos hx₁0]; exact hx₁r, by simp [hr], by simp [hr]⟩, ?_⟩
    intro hS
    obtain ⟨hP, -⟩ := (mem_cartS₂_iff _).1 hS
    exact not_mem_cartPl_of_mem_cartAm (Or.inl ⟨hx₁0.ne', by simp only; rw [hs₁]; norm_num⟩) hP
  have hjm : JoinedIn W (0, 0, r / 2) (x₁, 0, 0) :=
    cart_joined_pos hcp hq₀ (by simp only; linarith) le_rfl
  have hjm' : JoinedIn W (0, 0, -(r / 2)) (x₁, 0, 0) :=
    cart_joined_neg hcm hq₀ (by simp only; linarith) le_rfl
  refine ⟨(0, 0, r / 2), hcp, fun p hp => ?_⟩
  rcases lt_trichotomy p.2.2 0 with h | h | h
  · exact hjm.trans ((hjm'.symm.trans (cart_joined_neg hcm hp (by simp only; linarith) h.le)))
  · have hp' : (p.1, p.2.1, r / 2) ∈ W := by
      obtain ⟨h1, h2, -⟩ := cart_norm_lt.1 hp.1
      exact ⟨cart_norm_lt.2 ⟨h1, h2, by rw [abs_of_pos (by linarith)]; linarith⟩,
        hzS _ (by simp only; linarith)⟩
    exact (cart_joined_pos hcp hp' (by simp only; linarith) (by simp only; linarith)).trans
      (cart_joined_pos hp' hp (by simp only; linarith) h.ge)
  · exact (cart_joined_pos hp hcp h (by simp only; linarith)).symm

/-- The loops of `π₁(Y ∖ S₂, P)` represented by loops of a set `W ∋ P` form a subgroup. -/
def cartLoopSubgroup (W : Set (ℝ × ℝ × ℝ)) (P : CartS2c) (hP : (P : ℝ × ℝ × ℝ) ∈ W) :
    Subgroup (FundamentalGroup CartS2c P) where
  carrier := {g | ∃ μ : Path P P, (∀ t, (μ t : ℝ × ℝ × ℝ) ∈ W) ∧
    FundamentalGroup.toPath g = Path.Homotopic.Quotient.mk μ}
  one_mem' := ⟨Path.refl P, fun _ => hP, rfl⟩
  mul_mem' := by
    rintro a b ⟨μa, ha, hμa⟩ ⟨μb, hb, hμb⟩
    refine ⟨μb.trans μa, fun t => ?_, ?_⟩
    · rw [Path.trans_apply]; split_ifs
      · exact hb _
      · exact ha _
    · show (FundamentalGroup.toPath b).trans (FundamentalGroup.toPath a) = _
      rw [hμa, hμb, Path.Homotopic.Quotient.mk_trans]
  inv_mem' := by
    rintro a ⟨μ, hμ, hμa⟩
    refine ⟨μ.symm, fun t => hμ _, ?_⟩
    show (FundamentalGroup.toPath a).symm = _
    rw [hμa, Path.Homotopic.Quotient.mk_symm]

/-- The number of turns around `S₂`: `π₁(ℝ³ ∖ S₂, P) ≅ ℤ`. -/
noncomputable def cartDeg₂ (P : CartS2c) : FundamentalGroup CartS2c P ≃* Multiplicative ℤ :=
  (fgMulEquivOfHomotopyEquiv cartHE P).trans
    (MulEquiv.ofBijective (cartDeg (cartKappa P)) (cartDeg_bijective _))

theorem cartDeg₂_mk (P : CartS2c) (ℓ : Path P P) :
    cartDeg₂ P (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk ℓ)) =
      Multiplicative.ofAdd (cWinding ((ℓ.map cartKappa.continuous).map cartF.continuous)) := rfl

/-- A small circle around the arc of `S₂` through `(x₀, 0, 0)`, in the plane `x = x₀`. -/
def cartCirc (x₀ ρ₀ : ℝ) : Path (x₀, ρ₀, (0 : ℝ)) (x₀, ρ₀, 0) where
  toFun θ := (x₀, ρ₀ * Real.cos (2 * Real.pi * θ), ρ₀ * Real.sin (2 * Real.pi * θ))
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by simp

theorem cartCirc_apply (x₀ ρ₀ : ℝ) (θ : I) : cartCirc x₀ ρ₀ θ =
    (x₀, ρ₀ * Real.cos (2 * Real.pi * θ), ρ₀ * Real.sin (2 * Real.pi * θ)) := rfl

theorem cartCirc_not_mem {x₀ ρ₀ : ℝ} (hx₀ : x₀ ≠ 0) (hs : Real.sin (1 / x₀) = 0) (hρ : 0 < ρ₀)
    (θ : I) : cartCirc x₀ ρ₀ θ ∉ cartS₂ := by
  rw [mem_cartS₂_iff, cartCirc_apply]
  rintro ⟨hP, hz⟩
  have hsin : Real.sin (2 * Real.pi * θ) = 0 := (mul_eq_zero.1 hz).resolve_left hρ.ne'
  have hcos : Real.cos (2 * Real.pi * θ) ^ 2 = 1 := by
    have := Real.sin_sq_add_cos_sq (2 * Real.pi * θ); rw [hsin] at this; linarith
  rcases hP with ⟨-, hy⟩ | ⟨h0, -⟩
  · simp only at hy
    rw [hs] at hy
    have := (mul_eq_zero.1 hy).resolve_left hρ.ne'
    rw [this] at hcos; norm_num at hcos
  · exact hx₀ h0

theorem cartShift_of_mem_cartAp {q : ℝ × ℝ × ℝ} (hq : q ∉ cartS₂) (hz : q.2.2 = 0)
    (h : (q.1, q.2.1) ∈ cartAp) : cartShift q = 2 := by
  rcases cartShift_plane hq hz with ⟨-, h2⟩ | ⟨h', -⟩
  · exact h2
  · exact absurd h' (not_mem_cartAm_of_mem_cartAp h)

theorem cartShift_of_mem_cartAm {q : ℝ × ℝ × ℝ} (hq : q ∉ cartS₂) (hz : q.2.2 = 0)
    (h : (q.1, q.2.1) ∈ cartAm) : cartShift q = -2 := by
  rcases cartShift_plane hq hz with ⟨h', -⟩ | ⟨-, h2⟩
  · exact absurd h (not_mem_cartAm_of_mem_cartAp h')
  · exact h2

theorem log_neg_I_mul_ofReal {b : ℝ} (hb : 0 < b) :
    Complex.log (-Complex.I * b) = Real.log b - Real.pi / 2 * Complex.I := by
  rw [show -Complex.I * (b : ℂ) = (b : ℂ) * (-Complex.I) by ring,
    Complex.log_ofReal_mul hb (neg_ne_zero.2 Complex.I_ne_zero), Complex.log_neg_I]; ring

theorem log_I_mul_ofReal {b : ℝ} (hb : 0 < b) :
    Complex.log (Complex.I * b) = Real.log b + Real.pi / 2 * Complex.I := by
  rw [show Complex.I * (b : ℂ) = (b : ℂ) * Complex.I by ring,
    Complex.log_ofReal_mul hb Complex.I_ne_zero, Complex.log_I]

/-- **The circle turns once around `S₂`.** -/
theorem cWinding_cartCirc {x₀ ρ₀ : ℝ} (hx₀ : x₀ ≠ 0) (hs : Real.sin (1 / x₀) = 0)
    (hρ : 0 < ρ₀) :
    cWinding (((pathToSub (cartCirc x₀ ρ₀) (cartCirc_not_mem hx₀ hs hρ)).map
      cartKappa.continuous).map cartF.continuous) = 1 := by
  set δ := ((pathToSub (cartCirc x₀ ρ₀) (cartCirc_not_mem hx₀ hs hρ)).map
      cartKappa.continuous).map cartF.continuous
  set w : I → ℂ := fun θ => ((δ θ : CStar) : ℂ)
  have hw : ∀ θ, w θ = ((ρ₀ * Real.cos (2 * Real.pi * θ) + 1 * cartShift (cartCirc x₀ ρ₀ θ) : ℝ) : ℂ)
      + ((ρ₀ * Real.sin (2 * Real.pi * θ) : ℝ) : ℂ) * Complex.I := fun θ => rfl
  have hwc : Continuous w := continuous_subtype_val.comp δ.continuous
  have hw0 : ∀ θ, w θ ≠ 0 := fun θ => (δ θ).2
  have him : ∀ θ, (w θ).im = ρ₀ * Real.sin (2 * Real.pi * θ) := fun θ => by
    rw [hw]
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re,
      Complex.I_im, mul_zero, mul_one, zero_add, add_zero]
  have hpi := Real.pi_pos
  have him_up : ∀ θ : I, (θ : ℝ) ≤ 1 / 2 → 0 ≤ (w θ).im := fun θ h => by
    rw [him]; exact mul_nonneg hρ.le (Real.sin_nonneg_of_nonneg_of_le_pi (by
      nlinarith [θ.2.1]) (by nlinarith))
  have him_dn : ∀ θ : I, 1 / 2 ≤ (θ : ℝ) → (w θ).im ≤ 0 := fun θ h => by
    rw [him]
    have : 0 ≤ Real.sin (2 * Real.pi * θ - Real.pi) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by nlinarith) (by nlinarith [θ.2.2])
    rw [Real.sin_sub_pi] at this
    nlinarith
  have hslit_up : ∀ θ : I, (θ : ℝ) ≤ 1 / 2 → -Complex.I * w θ ∈ Complex.slitPlane := by
    intro θ h
    rw [Complex.mem_slitPlane_iff]
    simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.I_re,
      Complex.I_im]
    rcases (him_up θ h).lt_or_eq with h' | h'
    · left; linarith
    · right
      intro h''
      apply hw0 θ
      apply Complex.ext
      · simp only [Complex.zero_re]; linarith
      · simp only [Complex.zero_im]; linarith
  have hslit_dn : ∀ θ : I, 1 / 2 ≤ (θ : ℝ) → Complex.I * w θ ∈ Complex.slitPlane := by
    intro θ h
    rw [Complex.mem_slitPlane_iff]
    simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
    rcases (him_dn θ h).lt_or_eq with h' | h'
    · left; linarith
    · right
      intro h''
      apply hw0 θ
      apply Complex.ext
      · simp only [Complex.zero_re]; linarith
      · simp only [Complex.zero_im]; linarith
  -- the values at `0`, `1/2`, `1`
  have hAp : ((cartCirc x₀ ρ₀ 0).1, (cartCirc x₀ ρ₀ 0).2.1) ∈ cartAp :=
    Or.inl ⟨hx₀, by simp only [cartCirc_apply, Icc.coe_zero, mul_zero, Real.cos_zero, mul_one]
                    rw [hs]; exact hρ⟩
  have hhalf : (⟨1 / 2, by norm_num, by norm_num⟩ : I) = ⟨1 / 2, by norm_num, by norm_num⟩ := rfl
  set h2 : I := ⟨1 / 2, by norm_num, by norm_num⟩
  have hc2 : cartCirc x₀ ρ₀ h2 = (x₀, -ρ₀, 0) := by
    rw [cartCirc_apply]
    have : 2 * Real.pi * ((h2 : I) : ℝ) = Real.pi := by simp [h2]; ring
    rw [this, Real.cos_pi, Real.sin_pi]; simp
  have hAm : ((cartCirc x₀ ρ₀ h2).1, (cartCirc x₀ ρ₀ h2).2.1) ∈ cartAm := by
    rw [hc2]; exact Or.inl ⟨hx₀, by simp only; rw [hs]; linarith⟩
  have hs0 : cartShift (cartCirc x₀ ρ₀ 0) = 2 :=
    cartShift_of_mem_cartAp (cartCirc_not_mem hx₀ hs hρ 0) (by simp) hAp
  have hs2 : cartShift (cartCirc x₀ ρ₀ h2) = -2 :=
    cartShift_of_mem_cartAm (cartCirc_not_mem hx₀ hs hρ h2) (by rw [hc2]) hAm
  have hw00 : w 0 = ((ρ₀ + 2 : ℝ) : ℂ) := by
    rw [hw, hs0]
    simp only [Icc.coe_zero, mul_zero, Real.cos_zero, Real.sin_zero, mul_one, one_mul,
      Complex.ofReal_zero, zero_mul, add_zero]
  have hw11 : w 1 = ((ρ₀ + 2 : ℝ) : ℂ) := by
    rw [show w 1 = w 0 by simp only [w, δ.source, δ.target]]; exact hw00
  have hw22 : w h2 = -((ρ₀ + 2 : ℝ) : ℂ) := by
    rw [hw, hs2]
    have : 2 * Real.pi * ((h2 : I) : ℝ) = Real.pi := by simp [h2]; ring
    rw [this, Real.cos_pi, Real.sin_pi]
    simp only [mul_zero, Complex.ofReal_zero, zero_mul, add_zero]
    push_cast; ring
  have hb : 0 < ρ₀ + 2 := by linarith
  -- the lift
  let f₁ : I → ℂ := fun θ => Complex.log (-Complex.I * w θ) + Real.pi / 2 * Complex.I
  let f₂ : I → ℂ := fun θ => Complex.log (Complex.I * w θ) + 3 * Real.pi / 2 * Complex.I
  have hf₁ : ContinuousOn f₁ {θ | (θ : ℝ) ≤ 1 / 2} :=
    ((continuous_const.mul hwc).continuousOn.clog fun θ h => hslit_up θ h).add continuousOn_const
  have hf₂ : ContinuousOn f₂ {θ | 1 / 2 ≤ (θ : ℝ)} :=
    ((continuous_const.mul hwc).continuousOn.clog fun θ h => hslit_dn θ h).add continuousOn_const
  have hmatch : ∀ θ : I, (θ : ℝ) = 1 / 2 → f₁ θ = f₂ θ := by
    intro θ h
    have : θ = h2 := Subtype.ext h
    subst this
    simp only [f₁, f₂, hw22]
    rw [show -Complex.I * -((ρ₀ + 2 : ℝ) : ℂ) = Complex.I * ((ρ₀ + 2 : ℝ) : ℂ) by ring,
      show Complex.I * -((ρ₀ + 2 : ℝ) : ℂ) = -Complex.I * ((ρ₀ + 2 : ℝ) : ℂ) by ring,
      log_I_mul_ofReal hb, log_neg_I_mul_ofReal hb]
    ring
  let Γ : C(I, ℂ) := ⟨fun θ => if (θ : ℝ) ≤ 1 / 2 then f₁ θ else f₂ θ,
    continuous_if_le continuous_subtype_val continuous_const hf₁ hf₂ hmatch⟩
  have hexp3 : Complex.exp (3 * Real.pi / 2 * Complex.I) = -Complex.I := by
    rw [show (3 * Real.pi / 2 * Complex.I : ℂ) = Real.pi / 2 * Complex.I + Real.pi * Complex.I by
      ring, Complex.exp_add, Complex.exp_pi_div_two_mul_I, Complex.exp_pi_mul_I]; ring
  refine cWinding_eq δ (Γ := Γ) (fun θ => ?_) ?_
  · show Complex.exp (if (θ : ℝ) ≤ 1 / 2 then f₁ θ else f₂ θ) = w θ
    split_ifs with h
    · simp only [f₁]
      rw [Complex.exp_add, Complex.exp_log (Complex.slitPlane_ne_zero (hslit_up θ h)),
        Complex.exp_pi_div_two_mul_I]
      ring_nf; rw [Complex.I_sq]; ring
    · simp only [f₂]
      rw [Complex.exp_add, Complex.exp_log (Complex.slitPlane_ne_zero (hslit_dn θ (by linarith))),
        hexp3]
      ring_nf; rw [Complex.I_sq]; ring
  · show (if ((1 : I) : ℝ) ≤ 1 / 2 then f₁ 1 else f₂ 1) =
      (if ((0 : I) : ℝ) ≤ 1 / 2 then f₁ 0 else f₂ 0) + ((1 : ℤ) : ℂ) * (2 * Real.pi * Complex.I)
    rw [if_neg (by norm_num), if_pos (by norm_num)]
    simp only [f₁, f₂, hw00, hw11, log_I_mul_ofReal hb, log_neg_I_mul_ofReal hb]
    push_cast; ring

/-- **The middles of loops can be pushed into small balls**: a path of `Y ∖ S₂` between two
points of `B(O, r) ∖ S₂` is homotopic in `Y ∖ S₂` to a path of `B(O, r) ∖ S₂`. The class of the
loop through it is a power of the small circle, by `π₁(Y ∖ S₂) ≅ ℤ`. -/
theorem cart_middle_homotopic {r : ℝ} (hr : 0 < r) {p₁ p₂ : ℝ × ℝ × ℝ}
    (h₁ : p₁ ∈ Metric.ball cartO r ∩ cartS₂ᶜ) (h₂ : p₂ ∈ Metric.ball cartO r ∩ cartS₂ᶜ)
    (m : Path p₁ p₂) (hm : ∀ t, m t ∈ cartS₂ᶜ) :
    ∃ ω : Path p₁ p₂, (∀ s, ω s ∈ Metric.ball cartO r ∩ cartS₂ᶜ) ∧ HomotopicIn cartS₂ᶜ m ω := by
  set W := Metric.ball cartO r ∩ cartS₂ᶜ with hWdef
  have hW := isPathConnected_ball_diff_cartS₂ hr
  have hWS : ∀ {q}, q ∈ W → q ∈ cartS₂ᶜ := fun hq => hq.2
  -- the circle
  obtain ⟨k, hk⟩ := exists_nat_gt (2 / r)
  have hpi := Real.pi_pos
  have hpi3 := Real.pi_gt_three
  have hk1 : (1 : ℝ) ≤ k := by
    have : (0 : ℝ) < k := lt_trans (by positivity) hk
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (by exact_mod_cast this.ne')
  set x₀ : ℝ := 1 / (k * (2 * Real.pi)) with hx₀def
  have hx₀ : 0 < x₀ := by positivity
  have hx₀r : x₀ < r := by
    rw [hx₀def]
    refine (one_div_lt (by positivity) hr).2 ?_
    have : 1 / r < 2 / r := by rw [div_lt_div_iff_of_pos_right hr]; norm_num
    nlinarith
  have hs : Real.sin (1 / x₀) = 0 := by
    rw [hx₀def, one_div_one_div, show (k : ℝ) * (2 * Real.pi) = ((2 * k : ℕ) : ℝ) * Real.pi by
      push_cast; ring]
    exact Real.sin_nat_mul_pi _
  set ρ₀ : ℝ := r / 2 with hρ₀def
  have hρ : 0 < ρ₀ := by positivity
  have hcircW : ∀ θ, cartCirc x₀ ρ₀ θ ∈ W := fun θ =>
    ⟨cart_norm_lt.2 ⟨by show |x₀| < r; rw [abs_of_pos hx₀]; exact hx₀r,
      by show |ρ₀ * Real.cos (2 * Real.pi * θ)| < r
         rw [abs_mul, abs_of_pos hρ]; nlinarith [Real.abs_cos_le_one (2 * Real.pi * θ), hρ₀def],
      by show |ρ₀ * Real.sin (2 * Real.pi * θ)| < r
         rw [abs_mul, abs_of_pos hρ]; nlinarith [Real.abs_sin_le_one (2 * Real.pi * θ), hρ₀def]⟩,
      cartCirc_not_mem hx₀.ne' hs hρ θ⟩
  have hc : ((x₀, ρ₀, (0 : ℝ)) : ℝ × ℝ × ℝ) ∈ W := by
    have := hcircW 0; rwa [(cartCirc x₀ ρ₀).source] at this
  -- connecting paths in `W`
  set sp := (hW.joinedIn _ h₁ _ hc).somePath
  have hsp : ∀ t, sp t ∈ W := (hW.joinedIn _ h₁ _ hc).somePath_mem
  set ω₀ := (hW.joinedIn _ h₂ _ h₁).somePath
  have hω₀ : ∀ t, ω₀ t ∈ W := (hW.joinedIn _ h₂ _ h₁).somePath_mem
  -- the loop at the centre of the circle
  set L := sp.symm.trans ((m.trans ω₀).trans sp)
  have hL : ∀ t, L t ∈ cartS₂ᶜ := path_trans_mem (path_symm_mem fun t => hWS (hsp t))
    (path_trans_mem (path_trans_mem hm fun t => hWS (hω₀ t)) fun t => hWS (hsp t))
  set C : CartS2c := ⟨(x₀, ρ₀, 0), hc.2⟩
  set Ls : Path C C := pathToSub L hL
  set Cs : Path C C := pathToSub (cartCirc x₀ ρ₀) (cartCirc_not_mem hx₀.ne' hs hρ)
  set g := FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk Ls)
  set g₁ := FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk Cs)
  have hg₁ : cartDeg₂ C g₁ = Multiplicative.ofAdd 1 := by
    rw [cartDeg₂_mk]; exact congrArg _ (cWinding_cartCirc hx₀.ne' hs hρ)
  have hgg : g = g₁ ^ (Multiplicative.toAdd (cartDeg₂ C g)) := by
    apply (cartDeg₂ C).injective
    rw [map_zpow, hg₁, ← ofAdd_zsmul, smul_eq_mul, mul_one, ofAdd_toAdd]
  have hmem : g ∈ cartLoopSubgroup W C hc := by
    rw [hgg]
    exact Subgroup.zpow_mem _ (show g₁ ∈ cartLoopSubgroup W C hc from ⟨Cs, hcircW, rfl⟩) _
  obtain ⟨μ, hμW, hμ⟩ := hmem
  have hLμ : Ls.Homotopic μ := Path.Homotopic.Quotient.eq.1 hμ
  -- back in `ℝ³`
  set μ' : Path (x₀, ρ₀, (0 : ℝ)) (x₀, ρ₀, 0) := μ.map continuous_subtype_val
  have hμ'W : ∀ t, μ' t ∈ W := hμW
  have hLμ' : HomotopicIn cartS₂ᶜ L μ' := by
    refine homotopicIn_iff.2 ⟨hL, fun t => (μ t).2, ?_⟩
    have : pathToSub μ' (fun t => (μ t).2) = μ := Path.ext (funext fun _ => rfl)
    rw [this]; exact hLμ
  have hU : ∀ {a b : ℝ × ℝ × ℝ} (P : Path a b), (∀ t, P t ∈ W) → ∀ t, P t ∈ cartS₂ᶜ :=
    fun P hP t => hWS (hP t)
  have hmω : ∀ t, (m.trans ω₀) t ∈ cartS₂ᶜ := path_trans_mem hm (hU _ hω₀)
  have e1 := (homotopicIn_symm_trans_iff (hU _ hsp)
    (path_trans_mem hmω (hU _ hsp)) (hU _ hμ'W)).1 hLμ'
  have e2 := homotopicIn_swap hmω (path_trans_mem (hU _ hsp) (hU _ hμ'W)) (hU _ hsp) e1.symm
  have e3 := homotopicIn_swap hm (path_trans_mem (path_trans_mem (hU _ hsp) (hU _ hμ'W))
    (path_symm_mem (hU _ hsp))) (hU _ hω₀) e2.symm
  refine ⟨_, ?_, e3⟩
  exact path_trans_mem (path_trans_mem (path_trans_mem hsp hμ'W) (path_symm_mem hsp))
    (path_symm_mem hω₀)

/-- **`ex:consider_carthesian_coordinates_usual`, third claim** (`RamcovGX.tex:1221`): every loop
of `Ω(O,O,Y ∖ S₂)` is almost trivial, in the literal reading (DEC-55). For every ball `B` around
`O`, the middle of the loop is homotopic in `Y ∖ S₂` to a path of `B ∖ S₂`
(`GX.cart_middle_homotopic`), so the loop is homotopic with respect to `Y ∖ S₂` to a loop of
`Ω(O,O,B ∖ S₂)`. -/
theorem carthesian_S₂_almostTrivial {γ : Path cartO cartO} (hγ : MemOmega cartS₂ᶜ γ) :
    AlmostTrivialCC cartS₂ᶜ γ := by
  refine AlmostTrivial.almostTrivialCC ⟨hγ, fun V hV => ?_⟩
  obtain ⟨r, hr, hrV⟩ := Metric.mem_nhds_iff.1 hV
  have hB : Metric.ball cartO r ∈ 𝓝 cartO := Metric.ball_mem_nhds _ hr
  obtain ⟨t₀, h0, h0', hv0⟩ := exists_head_mem γ hB (c := 1 / 2) (by norm_num)
  obtain ⟨t₁, h1', h1, hv1⟩ := exists_tail_mem γ hB (c := 1 / 2) (by norm_num)
  have h01 : (t₀ : ℝ) < t₁ := by linarith
  have hmid : ∀ s, subpath γ t₀ t₁ s ∈ cartS₂ᶜ := fun s => by
    obtain ⟨u, hu1, hu2, he⟩ := subpath_mem γ t₀ t₁ s
    rw [he]
    rw [min_eq_left h01.le] at hu1
    rw [max_eq_right h01.le] at hu2
    exact hγ u (lt_of_lt_of_le h0 hu1) (lt_of_le_of_lt hu2 h1)
  have hp₀ : γ t₀ ∈ Metric.ball cartO r ∩ cartS₂ᶜ :=
    ⟨hv0 t₀ le_rfl, hγ t₀ h0 (by linarith)⟩
  have hp₁ : γ t₁ ∈ Metric.ball cartO r ∩ cartS₂ᶜ :=
    ⟨hv1 t₁ le_rfl, hγ t₁ (by linarith) h1⟩
  obtain ⟨ω, hω, hh⟩ := cart_middle_homotopic hr hp₀ hp₁ (subpath γ t₀ t₁) hmid
  obtain ⟨γ', hγ', hh'⟩ := AlmostTrivialAt.of_mid hγ h01 h1 hv0 hv1 ω
    (fun s => ⟨(hω s).1, (hω s).2⟩) hh
  exact ⟨γ', fun t a b => ⟨hrV (hγ' t a b).1, (hγ' t a b).2⟩, hh'⟩

/-- `ex:consider_carthesian_coordinates_usual`, fourth claim (`RamcovGX.tex:1222`): a loop of
`Ω(O,O,Y ∖ S₂)` which is not homotopically trivial. -/
theorem carthesian_S₂_not_trivial :
    ∃ γ : Path cartO cartO, MemOmega cartS₂ᶜ γ ∧ ¬ IsHomTrivial cartS₂ᶜ γ :=
  ⟨cartγ, cartγ_memOmega, not_isHomTrivial_cartγ⟩

end Carthesian

/-! ### `ex:consider_fiber_above_homeomorphic` -/

section Tower

variable {A : ℕ → Type*} [∀ k, TopologicalSpace (A k)] [∀ k, DiscreteTopology (A k)]
  (f : ∀ k, A (k + 1) → A k)

/-- The projective limit of a tower `⋯ → A 2 → A 1 → A 0` (a subspace of the product). -/
def TowerLim : Set (∀ k, A k) := {x | ∀ k, f k (x (k + 1)) = x k}

variable (hfib : ∀ k (c : A k), Infinite (f k ⁻¹' {c}) ∧ Countable (f k ⁻¹' {c}))

/-- A bijection of each fibre with `ℕ`. -/
def towerEqv (k : ℕ) (c : A k) : f k ⁻¹' {c} ≃ ℕ :=
  haveI := (hfib k c).1
  haveI := (hfib k c).2
  (nonempty_denumerable (f k ⁻¹' {c})).some.eqv

/-- The thread of the tower starting at `a₀` with fibre coordinates `s`. -/
def towerSeq (a₀ : A 0) (s : ℕ → ℕ) : ∀ k, A k
  | 0 => a₀
  | k + 1 => ((towerEqv f hfib k (towerSeq a₀ s k)).symm (s k)).1

theorem towerSeq_mem (a₀ : A 0) (s : ℕ → ℕ) : towerSeq f hfib a₀ s ∈ TowerLim f := fun k =>
  ((towerEqv f hfib k (towerSeq f hfib a₀ s k)).symm (s k)).2

/-- The fibre coordinates of a thread. -/
def towerCoord (x : TowerLim f) (k : ℕ) : ℕ := towerEqv f hfib k (x.1 k) ⟨x.1 (k + 1), x.2 k⟩

theorem towerSeq_towerCoord (x : TowerLim f) :
    towerSeq f hfib (x.1 0) (towerCoord f hfib x) = x.1 := by
  funext k
  induction k with
  | zero => rfl
  | succ k ih =>
    show (fun t => ((towerEqv f hfib k t).symm (towerCoord f hfib x k)).1)
      (towerSeq f hfib (x.1 0) (towerCoord f hfib x) k) = x.1 (k + 1)
    rw [ih]
    simp [towerCoord]

theorem towerCoord_towerSeq (a₀ : A 0) (s : ℕ → ℕ) :
    towerCoord f hfib ⟨towerSeq f hfib a₀ s, towerSeq_mem f hfib a₀ s⟩ = s := by
  funext k
  show towerEqv f hfib k (towerSeq f hfib a₀ s k) ⟨((towerEqv f hfib k (towerSeq f hfib a₀ s k)).symm
    (s k)).1, _⟩ = s k
  simp

theorem continuous_towerCoord : Continuous (towerCoord f hfib) := by
  refine continuous_pi fun k => ?_
  let g : A k × A (k + 1) → ℕ := fun p =>
    if h : f k p.2 = p.1 then towerEqv f hfib k p.1 ⟨p.2, h⟩ else 0
  have hg : (fun x : TowerLim f => towerCoord f hfib x k) =
      g ∘ fun x : TowerLim f => (x.1 k, x.1 (k + 1)) := by
    funext x
    simp only [g, comp_apply, dif_pos (x.2 k)]
    rfl
  rw [hg]
  exact continuous_of_discreteTopology.comp
    (((continuous_apply k).comp continuous_subtype_val).prodMk
      ((continuous_apply (k + 1)).comp continuous_subtype_val))

theorem continuous_towerSeq_apply (k : ℕ) :
    Continuous fun p : A 0 × (ℕ → ℕ) => towerSeq f hfib p.1 p.2 k := by
  induction k with
  | zero => exact continuous_fst
  | succ k ih =>
    let g : A k × ℕ → A (k + 1) := fun q => ((towerEqv f hfib k q.1).symm q.2).1
    have : (fun p : A 0 × (ℕ → ℕ) => towerSeq f hfib p.1 p.2 (k + 1)) =
        g ∘ fun p => (towerSeq f hfib p.1 p.2 k, p.2 k) := rfl
    rw [this]
    exact continuous_of_discreteTopology.comp (ih.prodMk ((continuous_apply k).comp continuous_snd))

/-- The projective limit of a tower of discrete spaces with countably infinite fibres is
`A 0 × ℕ^ℕ`. -/
def towerHomeomorph : TowerLim f ≃ₜ A 0 × (ℕ → ℕ) where
  toFun x := (x.1 0, towerCoord f hfib x)
  invFun p := ⟨towerSeq f hfib p.1 p.2, towerSeq_mem f hfib p.1 p.2⟩
  left_inv x := Subtype.ext (towerSeq_towerCoord f hfib x)
  right_inv p := Prod.ext rfl (towerCoord_towerSeq f hfib p.1 p.2)
  continuous_toFun := ((continuous_apply 0).comp continuous_subtype_val).prodMk
    (continuous_towerCoord f hfib)
  continuous_invFun := (continuous_pi fun k => continuous_towerSeq_apply f hfib k).subtype_mk _

end Tower

/-- `α^ℕ ≃ₜ α × α^ℕ` (head and tail). -/
def piNatHeadTail (α : Type*) [TopologicalSpace α] : (ℕ → α) ≃ₜ α × (ℕ → α) where
  toFun s := (s 0, fun n => s (n + 1))
  invFun p n := Nat.casesOn n p.1 p.2
  left_inv s := funext fun n => by cases n <;> rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_apply 0).prodMk (continuous_pi fun n => continuous_apply (n + 1))
  continuous_invFun := continuous_pi fun n => by
    cases n with
    | zero => exact continuous_fst
    | succ n => exact (continuous_apply n).comp continuous_snd

/-- For `B` countable, nonempty and discrete, `B × ℕ^ℕ ≃ₜ ℕ^ℕ`. -/
def prodNatPiHomeomorph (B : Type*) [TopologicalSpace B] [DiscreteTopology B] [Countable B]
    [Nonempty B] : B × (ℕ → ℕ) ≃ₜ (ℕ → ℕ) :=
  haveI : Infinite (B × ℕ) := inferInstance
  ((Homeomorph.refl B).prodCongr (piNatHeadTail ℕ)).trans ((Homeomorph.prodAssoc B ℕ (ℕ → ℕ)).symm.trans
    (((nonempty_denumerable (B × ℕ)).some.eqv.toHomeomorphOfDiscrete.prodCongr
      (Homeomorph.refl _)).trans (piNatHeadTail ℕ).symm))

/-- `ℕ^ℕ` (product topology) is not locally compact. -/
theorem not_locallyCompactSpace_nat_pi {α : Type*} [TopologicalSpace α] [DiscreteTopology α]
    [Infinite α] [Inhabited α] : ¬ LocallyCompactSpace (ℕ → α) := by
  intro h
  obtain ⟨s, hs, -, hsc⟩ := h.local_compact_nhds (fun _ => default) univ univ_mem
  rw [nhds_pi, Filter.mem_pi] at hs
  obtain ⟨J, hJ, t, ht, hts⟩ := hs
  obtain ⟨n, hn⟩ := hJ.infinite_compl.nonempty
  have himg : (fun x : ℕ → α => x n) '' s = univ := by
    refine eq_univ_of_forall fun m => ⟨Function.update (fun _ => default) n m, hts fun i hi => ?_,
      by simp⟩
    have hin : i ≠ n := fun h => hn (h ▸ hi)
    rw [Function.update_of_ne hin]
    exact mem_of_mem_nhds (ht i)
  have := hsc.image (continuous_apply n)
  rw [himg] at this
  exact infinite_univ (isCompact_iff_finite.1 this)


section FiberExample

/-- `S = {(1/n, 0) : n ∈ ℕ* ∪ {∞}} ⊆ ℝ² = ℂ` (`RamcovGX.tex:1410`). -/
def fibS : Set ℂ := insert 0 (range fun n : ℕ => ((1 / ((n : ℝ) + 1) : ℝ) : ℂ))

theorem isClosed_fibS : IsClosed fibS := by
  refine (Tendsto.isCompact_insert_range ?_).isClosed
  have h := (Complex.continuous_ofReal.tendsto 0).comp
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  rw [Complex.ofReal_zero] at h
  exact h

theorem countable_fibS : fibS.Countable := (countable_range _).insert 0

/-- `S` is skeletal. -/
theorem isSkeletal_fibS : IsSkeletal fibS := isSkeletal_of_countable_complex isClosed_fibS countable_fibS

/-- `ℂ ∖ S` is semilocally simply connected. -/
theorem semilocallySimplyConnected_fibS : SemilocallySimplyConnected (fibSᶜ : Set ℂ) :=
  semilocallySimplyConnected_of_isOpen isClosed_fibS.isOpen_compl

/-- The disc `D_{k+1}` of `ℂ` centred at `0` of radius `1/(k + 1/2)` (the paper's `D_n`,
`n = k + 1`, `RamcovGX.tex:1415`). -/
def fibD (k : ℕ) : Set ℂ := Metric.ball 0 (1 / ((k : ℝ) + 1 / 2))

theorem fibD_radius_pos (k : ℕ) : 0 < 1 / ((k : ℝ) + 1 / 2) := by positivity

theorem fibD_subset_iff {m n : ℕ} : fibD m ⊆ fibD n ↔ n ≤ m := by
  constructor
  · intro h
    by_contra hlt
    rw [not_le] at hlt
    have hr : 1 / ((n : ℝ) + 1 / 2) < 1 / ((m : ℝ) + 1 / 2) :=
      one_div_lt_one_div_of_lt (by positivity) (by exact_mod_cast (by linarith [(show (m : ℝ) < n by exact_mod_cast hlt)] : (m : ℝ) + 1 / 2 < n + 1 / 2))
    set ρ := (1 / ((n : ℝ) + 1 / 2) + 1 / ((m : ℝ) + 1 / 2)) / 2 with hρdef
    have hρ : 0 ≤ ρ := by have := fibD_radius_pos n; have := fibD_radius_pos m; positivity
    have hmem : ((ρ : ℝ) : ℂ) ∈ fibD m := by
      rw [fibD, Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_of_nonneg hρ]
      linarith [hρdef]
    have := h hmem
    rw [fibD, Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_of_nonneg hρ] at this
    linarith [hρdef]
  · intro h
    apply Metric.ball_subset_ball
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast (by linarith [(show (n : ℝ) ≤ m by exact_mod_cast h)] : (n : ℝ) + 1 / 2 ≤ m + 1 / 2))

theorem fibD_succ_subset (k : ℕ) : fibD (k + 1) ⊆ fibD k := fibD_subset_iff.2 (Nat.le_succ k)

theorem fibD_injective : Injective fibD := fun _ _ h =>
  le_antisymm (fibD_subset_iff.1 h.symm.subset) (fibD_subset_iff.1 h.subset)

theorem isCNbhd_fibD (k : ℕ) : IsCNbhd (0 : ℂ) (fibD k) :=
  ⟨Metric.isOpen_ball, (convex_ball _ _).isPreconnected, Metric.mem_ball_self (fibD_radius_pos k)⟩

/-- The discs `D_n` form a basis of neighbourhoods of `0`. -/
theorem fibD_basis : ∀ N ∈ 𝓝 (0 : ℂ), ∃ U ∈ range fibD, U ⊆ N := by
  intro N hN
  obtain ⟨ε, hε, hεN⟩ := Metric.mem_nhds_iff.1 hN
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt (half_pos hε)
  refine ⟨fibD k, mem_range_self k, (Metric.ball_subset_ball ?_).trans hεN⟩
  have h1 : 1 / ((k : ℝ) + 1 / 2) ≤ 2 * (1 / ((k : ℝ) + 1)) := by
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  linarith

theorem piOneUMap_self {Y : Type*} [TopologicalSpace Y] {S : Set Y} {a : Y} {U : Set Y}
    (h : U ⊆ U) (c : PiOneU S a U) : piOneUMap h c = c := by
  induction c using Quotient.inductionOn with | h γ => rfl

theorem piOneUMap_piOneUMap {Y : Type*} [TopologicalSpace Y] {S : Set Y} {a : Y} {U V W : Set Y}
    (h₁ : U ⊆ V) (h₂ : V ⊆ W) (c : PiOneU S a U) :
    piOneUMap h₂ (piOneUMap h₁ c) = piOneUMap (h₁.trans h₂) c := by
  induction c using Quotient.inductionOn with | h γ => rfl

theorem not_mem_fibS_of_im_ne_zero {z : ℂ} (h : z.im ≠ 0) : z ∉ fibS := by
  rintro (h0 | ⟨n, hn⟩)
  · exact h (by rw [h0]; simp)
  · exact h (by rw [← hn]; simp)

/-- A point of `D_k ∖ S` on the imaginary axis. -/
def fibQ (k : ℕ) : ℂ := ((1 / ((k : ℝ) + 1 / 2) / 2 : ℝ) : ℂ) * Complex.I

theorem fibQ_mem (k : ℕ) : fibQ k ∈ fibD k ∩ fibSᶜ := by
  have hr := fibD_radius_pos k
  refine ⟨?_, not_mem_fibS_of_im_ne_zero ?_⟩
  · rw [fibD, Metric.mem_ball, dist_zero_right, fibQ, norm_mul, Complex.norm_I, mul_one,
      Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    linarith
  · rw [fibQ, Complex.mul_I_im, Complex.ofReal_re]; positivity

theorem isPathConnected_fibS_compl : IsPathConnected (fibSᶜ : Set ℂ) := by
  have hO : IsPortly (fibSᶜ : Set ℂ) := isSkeletal_iff.1 isSkeletal_fibS
  exact hO.isOpen.isConnected_iff_isPathConnected.1 hO.isConnected

theorem isPathConnected_fibD_diff (k : ℕ) : IsPathConnected (fibD k ∩ fibSᶜ) := by
  have ho : IsOpen (fibD k ∩ fibSᶜ) := Metric.isOpen_ball.inter isClosed_fibS.isOpen_compl
  refine ho.isConnected_iff_isPathConnected.1 ⟨⟨_, fibQ_mem k⟩, ?_⟩
  rw [← Set.sdiff_eq]
  exact isPreconnected_diff_countable countable_fibS Metric.isOpen_ball
    (convex_ball _ _).isPreconnected

/-- A path from `a` into `U`, extended by a path of `U ∖ S`, is homotopic to itself with free end
in `U`. -/
theorem freeHomotopic_trans_tail {Y : Type*} [TopologicalSpace Y] {S U : Set Y} {a c d : Y}
    (P : Path a c) (hP : ∀ t, P t ∈ Sᶜ) (hc : c ∈ U) (ω : Path c d) (hω : ∀ t, ω t ∈ U ∩ Sᶜ) :
    FreeHomotopic S a U (P.trans ω).toContinuousMap P.toContinuousMap := by
  have step2 := freeHomotopic_trans_shrink P hP ω hω
  have step3 : FreeHomotopic S a U (P.trans (Path.refl c)).toContinuousMap P.toContinuousMap := by
    refine freeHomotopic_of_homotopicIn hc ?_
    have hr : ∀ t, (Path.refl c) t ∈ Sᶜ := fun _ => by simpa using hP 1
    refine homotopicIn_iff.2 ⟨path_trans_mem hP hr, hP, ?_⟩
    rw [pathToSub_trans _ _ hP hr]
    have : pathToSub (Path.refl c) hr = Path.refl _ := by ext; rfl
    rw [this]
    exact Path.Homotopic.trans_refl _
  exact step2.trans step3

/-- `π₁(a, D_k)` is countable (`π₁(ℂ ∖ S)` is countable and maps onto it). -/
theorem countable_piOneU_fibD (a : ℂ) (ha : a ∈ fibSᶜ) (k : ℕ) :
    Countable (PiOneU fibS a (fibD k)) := by
  obtain ⟨hu, huS⟩ := fibQ_mem k
  set u := fibQ k
  let a' : (fibSᶜ : Set ℂ) := ⟨a, ha⟩
  let u' : (fibSᶜ : Set ℂ) := ⟨u, huS⟩
  haveI : LocPathConnectedSpace (fibSᶜ : Set ℂ) :=
    isClosed_fibS.isOpen_compl.locPathConnectedSpace
  haveI : PathConnectedSpace (fibSᶜ : Set ℂ) :=
    isPathConnected_iff_pathConnectedSpace.1 isPathConnected_fibS_compl
  haveI : Countable (FundamentalGroup (fibSᶜ : Set ℂ) a') :=
    UniversalCover.countable_fundamentalGroup semilocallySimplyConnected_fibS a'
  let P₀ := Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath a' u')
  have hcancel : ∀ q : Path.Homotopic.Quotient a' u', (q.trans P₀.symm).trans P₀ = q := fun q => by
    rw [Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.symm_trans,
      Path.Homotopic.Quotient.trans_refl]
  have hinj : Injective fun q : Path.Homotopic.Quotient a' u' =>
      (FundamentalGroup.fromPath (q.trans P₀.symm) : FundamentalGroup (fibSᶜ : Set ℂ) a') := by
    intro q q' h
    have h' : q.trans P₀.symm = q'.trans P₀.symm := h
    rw [← hcancel q, h', hcancel]
  haveI : Countable (Path.Homotopic.Quotient a' u') := hinj.countable
  let Ξ : Path.Homotopic.Quotient a' u' → PiOneU fibS a (fibD k) :=
    Quotient.lift (fun γ : Path a' u' => (Quotient.mk _ ⟨(γ.map continuous_subtype_val).toContinuousMap,
        by simp [a'], fun t => (γ t).2, by simpa [u'] using hu⟩ : PiOneU fibS a (fibD k)))
      (fun γ γ' ⟨F⟩ => Quotient.sound ⟨⟨fun z => (F z : ℂ), by fun_prop⟩, fun t => by simp,
        fun t => by simp, fun s => by simp [a'], fun s => by simpa [u'] using hu,
        fun z => (F z).2⟩)
  refine (show Surjective Ξ from ?_).countable
  intro cl
  induction cl using Quotient.inductionOn with | h γ =>
  obtain ⟨hγ0, hγS, hγU⟩ := γ.2
  obtain ⟨β, hβ⟩ := (isPathConnected_fibD_diff k).joinedIn (γ.1 1) ⟨hγU, hγS 1⟩ u ⟨hu, huS⟩
  let P : Path a (γ.1 1) := ⟨γ.1, hγ0, rfl⟩
  have hP : ∀ t, P t ∈ fibSᶜ := hγS
  have hPβ : ∀ t, (P.trans β) t ∈ fibSᶜ := path_trans_mem hP fun t => (hβ t).2
  refine ⟨Path.Homotopic.Quotient.mk (pathToSub (P.trans β) hPβ), ?_⟩
  exact Quotient.sound (freeHomotopic_trans_tail P hP hγU β hβ)

/-! The winding of a path around a point, read through `exp`. -/

/-- `Λ` lifts `c - δ` through `exp`. -/
def IsArgLift (c : ℂ) (δ : I → ℂ) (Λ : C(I, ℂ)) : Prop := ∀ t, Complex.exp (Λ t) = c - δ t

theorem exists_argLift {c : ℂ} {δ : C(I, ℂ)} (hδ : ∀ t, δ t ≠ c) : ∃ Λ, IsArgLift c δ Λ := by
  obtain ⟨Λ, hΛ⟩ := exists_expLift
    ⟨fun t => (⟨c - δ t, sub_ne_zero.2 (hδ t).symm⟩ : CStar), by fun_prop⟩
  exact ⟨Λ, hΛ⟩

theorem IsArgLift.sub_eq {c : ℂ} {δ : I → ℂ} {Λ Λ' : C(I, ℂ)} (h : IsArgLift c δ Λ)
    (h' : IsArgLift c δ Λ') : Λ' 1 - Λ' 0 = Λ 1 - Λ 0 := by
  have := expLift_sub_const (Γ := Λ) (Γ' := Λ') (fun t => by rw [h t, h' t])
  rw [this 1]; ring

theorem IsArgLift.trans {c x y z : ℂ} {P : Path x y} {Q : Path y z} {ΛP ΛQ : C(I, ℂ)}
    (hP : IsArgLift c P ΛP) (hQ : IsArgLift c Q ΛQ) :
    ∃ Λ, IsArgLift c (P.trans Q) Λ ∧ Λ 1 - Λ 0 = (ΛP 1 - ΛP 0) + (ΛQ 1 - ΛQ 0) := by
  set d := ΛP 1 - ΛQ 0
  have hne : c - y ≠ 0 := by
    have := hP 1; rw [P.target] at this; rw [← this]; exact Complex.exp_ne_zero _
  have hd : Complex.exp d = 1 := by
    rw [Complex.exp_sub, hP 1, hQ 0, P.target, Q.source, div_self hne]
  let L₁ : Path (ΛP 0) (ΛP 1) := ⟨ΛP, rfl, rfl⟩
  let L₂ : Path (ΛP 1) (ΛQ 1 + d) := ⟨⟨fun t => ΛQ t + d, by fun_prop⟩, by simp [d], rfl⟩
  refine ⟨(L₁.trans L₂).toContinuousMap, fun t => ?_, ?_⟩
  · show Complex.exp ((L₁.trans L₂) t) = c - (P.trans Q) t
    rw [Path.trans_apply, Path.trans_apply]
    split_ifs
    · exact hP _
    · show Complex.exp (ΛQ _ + d) = _
      rw [Complex.exp_add, hd, mul_one, hQ]
  · show (L₁.trans L₂) 1 - (L₁.trans L₂) 0 = _
    rw [Path.target, Path.source]
    simp only [d]; ring

/-- The winding read through `exp`, corrected by the principal argument of the free end, is
invariant under homotopy with free end in a `U` on which `c - z` has positive real part. -/
theorem argLift_freeHomotopic {S U : Set ℂ} {a c : ℂ} (hc : c ∈ S)
    (hU : ∀ z ∈ U, 0 < (c - z).re) {γ₁ γ₂ : C(I, ℂ)} (h : FreeHomotopic S a U γ₁ γ₂)
    {Λ₁ Λ₂ : C(I, ℂ)} (h₁ : IsArgLift c γ₁ Λ₁) (h₂ : IsArgLift c γ₂ Λ₂) :
    Λ₁ 1 - Λ₁ 0 - Complex.log (c - γ₁ 1) = Λ₂ 1 - Λ₂ 0 - Complex.log (c - γ₂ 1) := by
  obtain ⟨H, h0, h1, ha, hHU, hS⟩ := h
  have hne : ∀ z, c - H z ≠ 0 := fun z h => hS z (by rw [sub_eq_zero] at h; rw [← h]; exact hc)
  have hca : c - a ≠ 0 := by have := hne (0, 0); rwa [ha] at this
  let G : C(I × I, CStar) := ⟨fun w => ⟨c - H (w.2, w.1), hne _⟩, by fun_prop⟩
  have hG0 : ∀ s, G (0, s) = cExp (ContinuousMap.const I (Complex.log (c - a)) s) := fun s =>
    Subtype.ext (by
      show c - H (s, 0) = Complex.exp (Complex.log (c - a))
      rw [ha, Complex.exp_log hca])
  let L := isCoveringMap_cExp.liftHomotopy G _ hG0
  have hL : ∀ w, Complex.exp (L w) = c - H (w.2, w.1) := fun w =>
    congrArg Subtype.val (congrFun (isCoveringMap_cExp.liftHomotopy_lifts G _ hG0) w)
  have hL0 : ∀ s, L (0, s) = Complex.log (c - a) := isCoveringMap_cExp.liftHomotopy_zero G _ hG0
  let g : I → ℂ := fun s => L (1, s) - Complex.log (c - H (s, 1))
  have hgc : Continuous g :=
    (L.continuous.comp (continuous_const.prodMk continuous_id)).sub
      ((continuous_const.sub (H.continuous.comp (continuous_id.prodMk continuous_const))).clog
        fun s => Complex.mem_slitPlane_iff.2 (Or.inl (hU _ (hHU s))))
  have hgexp : ∀ s s', cExp (g s) = cExp (g s') := fun s s' => Subtype.ext (by
    simp only [cExp_apply, g, Complex.exp_sub, hL, Complex.exp_log (hne _), div_self (hne _)])
  have hg := isCoveringMap_cExp.const_of_comp hgc hgexp 0 1
  have hs₀ : IsArgLift c γ₁ ⟨fun t => L (t, 0), by fun_prop⟩ := fun t => by
    show Complex.exp (L (t, 0)) = _; rw [hL, h0]
  have hs₁ : IsArgLift c γ₂ ⟨fun t => L (t, 1), by fun_prop⟩ := fun t => by
    show Complex.exp (L (t, 1)) = _; rw [hL, h1]
  have e₁ := h₁.sub_eq hs₀
  have e₂ := h₂.sub_eq hs₁
  simp only [ContinuousMap.coe_mk] at e₁ e₂
  rw [← e₁, ← e₂, hL0, hL0, ← h0 1, ← h1 1]
  simp only [g] at hg
  linear_combination hg

/-- The circle `t ↦ c + ε e^{2πijt}`. -/
def fibCircle (c : ℂ) (ε : ℝ) (j : ℤ) : Path (c + ε) (c + ε) where
  toFun t := c + ε * Complex.exp (j * (2 * Real.pi * Complex.I) * (t : ℝ))
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by simp [Complex.exp_int_mul_two_pi_mul_I]

theorem argLift_fibCircle (c : ℂ) {ε : ℝ} (hε : 0 < ε) (j : ℤ) :
    IsArgLift c (fibCircle c ε j) ⟨fun t => (Real.log ε : ℂ) + Real.pi * Complex.I +
      j * (2 * Real.pi * Complex.I) * (t : ℝ), by fun_prop⟩ := fun t => by
  show Complex.exp (_ + _ + _) = c - (c + ε * _)
  rw [Complex.exp_add, Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hε,
    Complex.exp_pi_mul_I]
  ring

theorem norm_fibCircle_sub (c : ℂ) {ε : ℝ} (hε : 0 < ε) (j : ℤ) (t : I) :
    ‖fibCircle c ε j t - c‖ = ε := by
  show ‖c + ε * Complex.exp (j * (2 * Real.pi * Complex.I) * (t : ℝ)) - c‖ = ε
  rw [add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_of_nonneg hε.le,
    Complex.norm_exp]
  simp

theorem fibS_sep {k : ℕ} {s : ℂ} (hs : s ∈ fibS) (hne : s ≠ ((1 / ((k : ℝ) + 1) : ℝ) : ℂ)) :
    1 / ((k : ℝ) + 1) / ((k : ℝ) + 2) ≤ ‖s - ((1 / ((k : ℝ) + 1) : ℝ) : ℂ)‖ := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  rcases hs with h0 | ⟨m, rfl⟩
  · rw [h0, zero_sub, norm_neg, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    exact div_le_self (by positivity) (by linarith)
  · rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    have hmk : m ≠ k := fun h => hne (by rw [h])
    rcases Nat.lt_or_gt_of_ne hmk with h | h
    · have hm : (m : ℝ) + 1 ≤ k := by exact_mod_cast h
      have e : 1 / ((m : ℝ) + 1) - 1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 1) / ((k : ℝ) + 2) =
          (((k : ℝ) + 2) * ((k : ℝ) + 1 - ((m : ℝ) + 1)) - ((m : ℝ) + 1)) /
            (((m : ℝ) + 1) * ((k : ℝ) + 1) * ((k : ℝ) + 2)) := by
        field_simp
      have hpos : 0 ≤ 1 / ((m : ℝ) + 1) - 1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 1) / ((k : ℝ) + 2) := by
        rw [e]; apply div_nonneg _ (by positivity); nlinarith
      rw [abs_of_nonneg (by linarith [div_nonneg zero_le_one (show (0 : ℝ) ≤ (k + 1) * (k + 2) by positivity), show 0 ≤ 1 / ((k : ℝ) + 1) / ((k : ℝ) + 2) by positivity])]
      linarith
    · have hm : (k : ℝ) + 2 ≤ m + 1 := by exact_mod_cast (by omega : k + 2 ≤ m + 1)
      have h1 : 1 / ((m : ℝ) + 1) ≤ 1 / ((k : ℝ) + 2) :=
        one_div_le_one_div_of_le (by positivity) hm
      have e : 1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 2) = 1 / ((k : ℝ) + 1) / ((k : ℝ) + 2) := by
        field_simp; ring
      rw [abs_sub_comm, abs_of_nonneg (by linarith [show 0 ≤ 1 / ((k : ℝ) + 1) / ((k : ℝ) + 2) by positivity])]
      linarith

/-- The maps `π₁(a, D_{n+1}) → π₁(a, D_n)` have infinite fibres (`RamcovGX.tex:1414`): the paths
`γ * ω * x_n^j * ω'` (`x_n` a small circle around `1/n`, the only point of `S` in
`D_n ∖ D_{n+1}`), `j ∈ ℤ`, all map to the class of `γ`, and are told apart by their winding
around `1/n` (`GX.argLift_freeHomotopic`). -/
theorem infinite_fiber_piOneUMap_fibD (a : ℂ) (k : ℕ) (cl : PiOneU fibS a (fibD k)) :
    Infinite (piOneUMap (S := fibS) (a := a) (fibD_succ_subset k) ⁻¹' {cl}) := by
  induction cl using Quotient.inductionOn with | h γ =>
  obtain ⟨hγ0, hγS, hγU⟩ := γ.2
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  set r : ℝ := 1 / ((k : ℝ) + 1) with hr
  set c : ℂ := (r : ℂ)
  set ε : ℝ := r / (4 * ((k : ℝ) + 2)) with hεdef
  have hrpos : 0 < r := by positivity
  have hcS : c ∈ fibS := Or.inr ⟨k, rfl⟩
  have hε : 0 < ε := by positivity
  have hεr : ε < r / ((k : ℝ) + 2) := by
    rw [hεdef]; apply div_lt_div_of_pos_left hrpos (by positivity); linarith
  have hrε : r + ε < 1 / ((k : ℝ) + 1 / 2) := by
    rw [hεdef, hr, div_div, div_add_div _ _ (by positivity) (by positivity),
      div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hcirc : ∀ j t, fibCircle c ε j t ∈ fibD k ∩ fibSᶜ := by
    intro j t
    have hn := norm_fibCircle_sub c hε j t
    refine ⟨?_, fun hS => ?_⟩
    · rw [fibD, Metric.mem_ball, dist_zero_right]
      calc ‖fibCircle c ε j t‖ = ‖c + (fibCircle c ε j t - c)‖ := by ring_nf
        _ ≤ ‖c‖ + ‖fibCircle c ε j t - c‖ := norm_add_le _ _
        _ = r + ε := by rw [hn, Complex.norm_real, Real.norm_of_nonneg hrpos.le]
        _ < _ := hrε
    · have hne : fibCircle c ε j t ≠ c := fun h => by
        rw [h, sub_self, norm_zero] at hn; linarith
      have := fibS_sep hS hne
      rw [hn] at this
      linarith
  have hp₀ : c + (ε : ℂ) ∈ fibD k ∩ fibSᶜ := by
    have := hcirc 0 0; rwa [Path.source] at this
  obtain ⟨Pe, hPe⟩ := (isPathConnected_fibD_diff k).joinedIn (γ.1 1) ⟨hγU, hγS 1⟩ _ hp₀
  obtain ⟨hq, hqS⟩ := fibQ_mem (k + 1)
  have hqk : fibQ (k + 1) ∈ fibD k := fibD_succ_subset k hq
  obtain ⟨Qp, hQp⟩ := (isPathConnected_fibD_diff k).joinedIn _ hp₀ (fibQ (k + 1)) ⟨hqk, hqS⟩
  let G : Path a (γ.1 1) := ⟨γ.1, hγ0, rfl⟩
  let ω : ℤ → Path (γ.1 1) (fibQ (k + 1)) := fun j => Pe.trans ((fibCircle c ε j).trans Qp)
  have hω : ∀ j t, ω j t ∈ fibD k ∩ fibSᶜ := fun j =>
    path_trans_mem hPe (path_trans_mem (hcirc j) hQp)
  have hGω : ∀ j t, (G.trans (ω j)) t ∈ fibSᶜ := fun j =>
    path_trans_mem (fun t => hγS t) (fun t => (hω j t).2)
  let γj : ℤ → FreePath fibS a (fibD (k + 1)) := fun j =>
    ⟨(G.trans (ω j)).toContinuousMap, (G.trans (ω j)).source, hGω j, by
      show (G.trans (ω j)) 1 ∈ _; rw [Path.target]; exact hq⟩
  let φ : ℤ → (piOneUMap (S := fibS) (a := a) (fibD_succ_subset k) ⁻¹' {Quotient.mk _ γ}) :=
    fun j => ⟨Quotient.mk _ (γj j), Quotient.sound
      (freeHomotopic_trans_tail G (fun t => hγS t) hγU (ω j) (hω j))⟩
  refine Infinite.of_injective φ fun j j' hjj => ?_
  have hfh : FreeHomotopic fibS a (fibD (k + 1)) (γj j).1 (γj j').1 :=
    Quotient.exact (congrArg Subtype.val hjj)
  have hUre : ∀ z ∈ fibD (k + 1), 0 < (c - z).re := fun z hz => by
    rw [fibD, Metric.mem_ball, dist_zero_right] at hz
    have h1 : z.re ≤ ‖z‖ := Complex.re_le_norm z
    have h2 : 1 / (((k + 1 : ℕ) : ℝ) + 1 / 2) < r := by
      rw [hr]; push_cast; apply one_div_lt_one_div_of_lt (by positivity); linarith
    rw [Complex.sub_re, Complex.ofReal_re]; linarith
  have avoid : ∀ {x y : ℂ} (P : Path x y), (∀ t, P t ∈ fibSᶜ) → ∀ t, P.toContinuousMap t ≠ c :=
    fun P hP t h => hP t (h ▸ hcS)
  obtain ⟨ΛG, hΛG⟩ := exists_argLift (avoid G fun t => hγS t)
  obtain ⟨ΛP, hΛP⟩ := exists_argLift (avoid Pe fun t => (hPe t).2)
  obtain ⟨ΛQ, hΛQ⟩ := exists_argLift (avoid Qp fun t => (hQp t).2)
  have key : ∀ j : ℤ, ∃ Λ, IsArgLift c (G.trans (ω j)) Λ ∧ Λ 1 - Λ 0 = (ΛG 1 - ΛG 0) +
      ((ΛP 1 - ΛP 0) + (j * (2 * Real.pi * Complex.I) + (ΛQ 1 - ΛQ 0))) := by
    intro j
    obtain ⟨Λ₁, h₁, e₁⟩ := (argLift_fibCircle c hε j).trans (Q := Qp) hΛQ
    obtain ⟨Λ₂, h₂, e₂⟩ := IsArgLift.trans (P := Pe) hΛP h₁
    obtain ⟨Λ₃, h₃, e₃⟩ := IsArgLift.trans (P := G) hΛG h₂
    refine ⟨Λ₃, h₃, ?_⟩
    rw [e₃, e₂, e₁]
    simp only [ContinuousMap.coe_mk, Set.Icc.coe_one, Set.Icc.coe_zero, Complex.ofReal_one,
      Complex.ofReal_zero, mul_one, mul_zero, add_zero]
    ring
  obtain ⟨Λ, hΛ, eΛ⟩ := key j
  obtain ⟨Λ', hΛ', eΛ'⟩ := key j'
  have hinv := argLift_freeHomotopic hcS hUre hfh hΛ hΛ'
  have h1 : (γj j).1 1 = (γj j').1 1 := by
    show (G.trans (ω j)) 1 = (G.trans (ω j')) 1
    rw [Path.target, Path.target]
  rw [h1, eΛ, eΛ'] at hinv
  have : ((j : ℂ) - j') * (2 * Real.pi * Complex.I) = 0 := by linear_combination hinv
  rcases mul_eq_zero.1 this with h | h
  · exact_mod_cast sub_eq_zero.1 h
  · exact absurd h Complex.two_pi_I_ne_zero

/-- The projective system `π₁(a, D_n)` (`RamcovGX.tex:1414`): countable sets, and maps
`π₁(a, D_{n+1}) → π₁(a, D_n)` with infinite fibres. -/
theorem fibS_tower (a : ℂ) (ha : a ∈ fibSᶜ) :
    Countable (PiOneU fibS a (fibD 0)) ∧ ∀ (k : ℕ) (c : PiOneU fibS a (fibD k)),
      Infinite (piOneUMap (S := fibS) (a := a) (fibD_succ_subset k) ⁻¹' {c}) ∧
        Countable (PiOneU fibS a (fibD (k + 1))) :=
  ⟨countable_piOneU_fibD a ha 0, fun k c =>
    ⟨infinite_fiber_piOneUMap_fibD a k c, countable_piOneU_fibD a ha (k + 1)⟩⟩

theorem nonempty_piOneU_fibD_zero (a : ℂ) (ha : a ∈ fibSᶜ) : Nonempty (PiOneU fibS a (fibD 0)) := by
  obtain ⟨hq, hqS⟩ := fibQ_mem 0
  obtain ⟨γ, hγ⟩ := isPathConnected_fibS_compl.joinedIn a ha (fibQ 0) hqS
  exact ⟨Quotient.mk _ ⟨γ.toContinuousMap, γ.source, hγ, by
    show γ 1 ∈ fibD 0
    rw [γ.target]; exact hq⟩⟩

/-- **`ex:consider_fiber_above_homeomorphic`** (`RamcovGX.tex:1409`). For `S = {1/n} ∪ {0} ⊆ ℂ` (skeletal, with `ℂ ∖ S`
semilocally simply connected), the fibre above `0` of the maximal covering `\widetilde Y^S`
possibly branched over `S` is homeomorphic to `ℤ^ℕ` with the product ("weak") topology, hence is not
locally compact. -/
theorem fiber_above_homeomorphic (y₀ : (fibSᶜ : Set ℂ)) :
    IsSkeletal fibS ∧ SemilocallySimplyConnected (fibSᶜ : Set ℂ) ∧
      Nonempty ((SpreadEnd.base : MaxBranchedCover fibS y₀ → ℂ) ⁻¹' {0} ≃ₜ (ℕ → ℤ)) ∧
      ¬ LocallyCompactSpace ((SpreadEnd.base : MaxBranchedCover fibS y₀ → ℂ) ⁻¹' {0}) := by
  set a : ℂ := (y₀ : ℂ)
  have ha : a ∈ fibSᶜ := y₀.2
  set 𝓤 : Set (Set ℂ) := range fibD
  obtain ⟨Φ, -, hemb, hrange⟩ := general_fiber_path_universal isSkeletal_fibS
    semilocallySimplyConnected_fibS y₀ ha (maxBase_base y₀) 𝓤
    (by rintro _ ⟨k, rfl⟩; exact isCNbhd_fibD k) fibD_basis
  -- the tower
  let A : ℕ → Type := fun k => PiOneU fibS a (fibD k)
  let f : ∀ k, A (k + 1) → A k := fun k => piOneUMap (fibD_succ_subset k)
  obtain ⟨hcount0, hfib⟩ := fibS_tower a ha
  haveI : Nonempty (A 0) := nonempty_piOneU_fibD_zero a ha
  haveI : Countable (A 0) := hcount0
  have hfib' : ∀ k (c : A k), Infinite (f k ⁻¹' {c}) ∧ Countable (f k ⁻¹' {c}) := fun k c =>
    ⟨(hfib k c).1, by haveI := (hfib k c).2; infer_instance⟩
  -- threads over `𝓤` versus threads over `ℕ`
  have chain : ∀ x ∈ TowerLim f, ∀ n m (h : n ≤ m),
      piOneUMap (S := fibS) (a := a) (fibD_subset_iff.2 h) (x m) = x n := by
    intro x hx n m h
    induction m, h using Nat.le_induction with
    | base => exact piOneUMap_self _ _
    | succ m hnm ih =>
      rw [← piOneUMap_piOneUMap (fibD_succ_subset m) (fibD_subset_iff.2 hnm)]
      show piOneUMap _ (f m (x (m + 1))) = _
      rw [hx m]; exact ih
  let ρ : (∀ U : 𝓤, PiOneU fibS a U) → ∀ k, A k := fun F k => F ⟨fibD k, mem_range_self k⟩
  let sec : (∀ k, A k) → ∀ U : 𝓤, PiOneU fibS a U := fun x U =>
    piOneUMap U.2.choose_spec.subset (x U.2.choose)
  have hsec : ∀ x ∈ TowerLim f, ∀ (U : 𝓤) (k : ℕ) (hk : fibD k ⊆ U), k ≤ U.2.choose →
      sec x U = piOneUMap hk (x k) := by
    intro x hx U k hk hle
    show piOneUMap _ (x U.2.choose) = _
    rw [← chain x hx k _ hle, piOneUMap_piOneUMap]
  have hidx : ∀ k : ℕ, (⟨fibD k, mem_range_self k⟩ : 𝓤).2.choose = k := fun k =>
    fibD_injective (⟨fibD k, mem_range_self k⟩ : 𝓤).2.choose_spec
  have hρmem : ∀ F ∈ range Φ, ρ F ∈ TowerLim f := by
    intro F hF k
    rw [hrange] at hF
    exact hF ⟨fibD (k + 1), mem_range_self _⟩ ⟨fibD k, mem_range_self _⟩ (fibD_succ_subset k)
  have hσmem : ∀ x ∈ TowerLim f, sec x ∈ range Φ := by
    intro x hx
    rw [hrange]
    intro U V h
    have hm := U.2.choose_spec
    have hn := V.2.choose_spec
    have hle : V.2.choose ≤ U.2.choose := fibD_subset_iff.1 (by rw [hm, hn]; exact h)
    show piOneUMap h (piOneUMap _ (x U.2.choose)) = piOneUMap _ (x V.2.choose)
    rw [piOneUMap_piOneUMap, ← chain x hx _ _ hle, piOneUMap_piOneUMap]
  have hρσ : ∀ x ∈ TowerLim f, ρ (sec x) = x := by
    intro x hx
    funext k
    show sec x ⟨fibD k, mem_range_self k⟩ = x k
    rw [hsec x hx _ k subset_rfl (by rw [hidx]), piOneUMap_self]
  have hσρ : ∀ F ∈ range Φ, sec (ρ F) = F := by
    intro F hF
    have hF' := hF
    rw [hrange] at hF'
    funext U
    exact hF' ⟨fibD U.2.choose, mem_range_self _⟩ U U.2.choose_spec.subset
  let Θ : range Φ ≃ₜ TowerLim f :=
    { toFun := fun F => ⟨ρ F.1, hρmem F.1 F.2⟩
      invFun := fun x => ⟨sec x.1, hσmem x.1 x.2⟩
      left_inv := fun F => Subtype.ext (hσρ F.1 F.2)
      right_inv := fun x => Subtype.ext (hρσ x.1 x.2)
      continuous_toFun := (continuous_pi fun k =>
        (continuous_apply (⟨fibD k, mem_range_self k⟩ : 𝓤)).comp
          (continuous_subtype_val (p := (· ∈ range Φ)))).subtype_mk _
      continuous_invFun := (continuous_pi fun (U : 𝓤) =>
        (continuous_of_discreteTopology (f := piOneUMap (S := fibS) (a := a)
          U.2.choose_spec.subset)).comp ((continuous_apply U.2.choose).comp
            (continuous_subtype_val (p := (· ∈ TowerLim f))))).subtype_mk _ }
  let ζ : (ℕ → ℕ) ≃ₜ (ℕ → ℤ) :=
    Homeomorph.piCongrRight fun _ => Equiv.intEquivNat.symm.toHomeomorphOfDiscrete
  let Ψ := hemb.toHomeomorph.trans (Θ.trans ((towerHomeomorph f hfib').trans
    ((prodNatPiHomeomorph (A 0)).trans ζ)))
  refine ⟨isSkeletal_fibS, semilocallySimplyConnected_fibS, ⟨Ψ⟩, fun h => ?_⟩
  haveI := h
  haveI : LocallyCompactSpace (ℕ → ℤ) := Ψ.symm.isOpenEmbedding.locallyCompactSpace
  exact not_locallyCompactSpace_nat_pi (α := ℤ) inferInstance

end FiberExample

end GX
