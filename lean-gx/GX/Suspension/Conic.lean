import GX.Singular.Suspension

/-!
# Conical `(G,X)`-structures at a point, and the induced action on the link

Package BBS-Conic (layer L0 of `papers/bbs/REVIEW.md` §B). L0 is NEW THEORY, built under the
author's ruling. Its starting point is draft material commented out in
`papers/gx/sources/thesis/these.tex` (l.3560–3677, here l.3566–3618, "`(G,X)`-structures
coniques"), not part of the thesis: the author discarded it ("It was commented out for a
reason"), so nothing below is a claim of the thesis; the counterexamples below are motivation
for the corrected definitions. Every `these.tex` line cited in l.3560–3677 refers to that
discarded draft; the `these:*` labels are row keys naming the file, not thesis results. The paper
`papers/gx/legacy/labeled/RamcovGX.tex` l.734–740 asks for this layer ("geometrical suspension
… a lift of the topological suspension functor"). **No ledger label is marked**: the draft is
not a ledger source. Rows touched, unmarked:

* `draft:structure_conique` (Définition « Structure conique », `these.tex:3569`) — formalized in
  two layers. `GX.ConicChart X p L`: an open neighbourhood `U` of `p` and a homeomorphism `φ` of
  `U` onto an open neighbourhood of the apex `O` of `susp(L)` (`RamcovGX.tex:710`, `GX.Susp`),
  `φ p ∈ O`. `GX.ConicChart.IsRayCompatible`: the draft's third item verbatim, for a subgroup
  `H` of the stabiliser (BBS-Q2: `H` a parameter; the draft's `G_p` is `H = stabilizer`).
  `GX.ConicStructure G p H L`: **a sufficient corrected form** (radius preserved), a conic chart
  which conjugates every `h ∈ H` to the radial extension `susp(h·)` of an action of `H` on `L`
  (`map_smul`). It is sufficient for the draft's suspension proposition, NOT necessary
  (BBS-Celestial): a candidate MINIMAL hypothesis, for the author, is "for each `h ∈ H` some
  `g_h ∈ G` with `φ ∘ g_h = susp(h·) ∘ φ`" (a radial lift), which is radius preservation
  (`g_h = h`) when `G ⊆ Isom`; it is not formalized here.
* `draft:propri_action` (the « propri » after the definition, `these.tex:3581`) — **proved**
  from the draft's literal ray condition, with `G` acting by homeomorphisms
  (`ContinuousConstSMul`, part of « structure analytique », `these.tex:1185`; the proof's
  "`U ∩ g⁻¹U` is a neighbourhood of `p`" is where it is used): `GX.ConicChart.linkAction` (a
  `MulAction H L`), characterised by `GX.ConicChart.dir_smul_linkAction` and unique
  (`GX.ConicChart.linkAction_unique`); continuity of the action,
  `GX.ConicStructure.continuousConstSMul`.
* `draft:lem_analytique` (`these.tex:3606`: `(G_p, X_p)` analytic if `(G,X)` is) — the draft's
  lemma, read literally, fails; the counterexample motivates radius preservation in
  `ConicStructure` (a design note): `GX.lem_analytique_counterexample` (in
  `GX.Suspension.Affine`) takes `(G,X) = (Aff(V), V)`, analytic, at `p = 0` with the
  sphere chart `φ = (σ, r) ↦ rσ` inverted and `G_p = GL(V)`; the ray condition holds
  (`GX.affineConic_isRayCompatible`) but the homothety `2·id ≠ 1` acts trivially on `S(V)`, so
  the induced action is not faithful. The draft's argument (l.3611, "les actions de `g` et `h` sur
  `U × ℝ₊` sont égales") uses that `h` acts on the cone as `susp(h·)`. What holds, proved: for a
  conic STRUCTURE (radius preserved), `GX.ConicStructure.isAnalyticAction` (faithful and rigid)
  and `GX.ConicStructure.isRigidAction` (rigid from rigid). Under the ray condition alone,
  faithfulness fails; whether rigidity survives is not settled here.
* Design notes: `GX.ConicStructure.eq_of_tendsto_pow` (no RADIUS-PRESERVING conic structure has a
  contracting element in `H`, e.g. a linear map with an eigenvalue in `]0,1[`; for BBS's
  `SO₀(1,2)` see `GX.isEmpty_conicStructure_nullIsom0_stabilizer` in
  `GX.Suspension.Affine`), `GX.ConicStructure.map_smul_of_isFull` (a conic structure
  onto the whole cone is `H`-invariant and equivariant on all of `U`).
* Witness: `GX.ConicStructure.tautological` (the apex of `susp(L)` itself, `H = ⊤`).

> \begin{defi}[Structure conique] Soit $(G,X)$ une structure analytique et soit $p\in X$.
> Une structure conique en $p$ est un triplet $(\U_p,X_p,\V_p,\phi_p)$ tel que
> \begin{itemize} \item $\U_p$ est un voisinage de $p$; \item $\phi_p : \U\rightarrow
> \susp(X_p)$ est un homéomorphisme avec $\phi_p(p)=O$; \item Pour tout $g\in G_p:=\stab_G(p)$
> et tout $x,y\in \U\cap g^{-1}\U$, $$\pi\circ \phi_p(x) = \pi\circ \phi_p(y) \Rightarrow
> \pi\circ \phi_p(g\cdot x) = \pi\circ \phi_p(g\cdot y)$$ avec $\pi :
> \susp^*(X_p)\rightarrow X_p$ la projection naturelle. \end{itemize} \end{defi}
> (commented-out draft, these.tex:3569–3578)
>
> \begin{propri} … L'action $\forall g \in G_p,~ \forall x \in X_p, ~~g\cdot x := \pi\circ
> \phi\left(g \cdot x'\right)$ avec $x'\in \U\cap g^{-1}\U$ tel que $\pi\circ \phi(x')=x$, est
> bien définie. \end{propri} (commented-out draft, these.tex:3581–3586)
>
> \begin{lem} Soit une $(G,X)$-structure conique et soit $p$ dans $X$. Si $(G,X)$ est une
> structure analytique alors $(G_p,X_p)$ est analytique. \end{lem} (commented-out draft,
> these.tex:3606–3608)

## Hypothesis checklist

| draft hypothesis | here |
|---|---|
| `(G,X)` analytic | ⚠ weakened: only what each theorem uses (1) |
| `G_p = Stab_G(p)` | ⚠ generalised: any `H ≤ Stab_G(p)` (BBS-Q2); `G_p` is `H = stabilizer` |
| `U_p` a neighbourhood, `φ_p : U → susp(X_p)` a homeomorphism | ⚠ weakened (2) |
| the propri's "`U ∩ g⁻¹U` is a neighbourhood of `p`" | ✓ carried: `ContinuousConstSMul G X` (3) |
| the ray condition (third item) | ✓ carried verbatim; ⚠ strengthened in `ConicStructure` (4) |

1. `ContinuousConstSMul G X` for the action, `IsRigidAction G X` for rigidity, `T2Space X` for
   `map_smul_of_isFull`.
2. `U` open, `φ` onto an OPEN NEIGHBOURHOOD of `O` (BBS's "open subset"; any neighbourhood
   contains an open one, and a homeomorphism onto `susp` maps it onto an open set); onto the
   whole cone is `ConicChart.IsFull`.
3. `G` acts by homeomorphisms, part of « structure analytique », `these.tex:1185`, and of
   `RamcovGX.tex:341`.
4. Radius preserved too. A DESIGN NOTE: the draft's arguments for the suspension proposition
   (l.3651–3673) and for the analyticity lemma use it; it is SUFFICIENT, not necessary, for the
   suspension proposition (BBS-Celestial), and the draft's lemma, read literally, fails without
   it (`GX.lem_analytique_counterexample`, the counterexample motivating the hypothesis).

## SCOPE (disclosed)

* The link `X_p` is the type parameter `L` (not a bundled field), to keep universes free; the
  draft's `V_p` (the image) is `φ.target`.
* `π : susp*(L) → L` is `GX.Susp.dir`, a total function equal to `π` off `O`
  (`Susp.dir_mk_of_pos`); every statement using it is guarded by `∉ O`.
* `susp(L)` carries RamcovGX's topology (`GX.Susp`, `RamcovGX.tex:710`), not the thesis's
  quotient topology of `X × ℝ₊/∼` (`these.tex:3685–3687`). The two agree for compact links
  (`GX.Susp.eq_quotTop_of_compactSpace`: the spheres, `Bool`), not in general.
* `ConicStructure` takes the action `[MulAction H L]` as a parameter and asks equivariance
  `φ(h·x) = susp(h·)(φ x)` on `U ∩ h⁻¹U`; by `linkAction_unique` the action is then the draft's
  induced action, so nothing is lost by this packaging. `ConicChart.toConicStructure` builds one
  from the draft's data plus radius preservation.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

noncomputable section

open Set Filter Topology NNReal

namespace GX

namespace Susp

variable {S T : Type*}

/-! ### The projection `π : susp*(Σ) → Σ` -/

/-- The direction of a point of `susp(Σ)`: the first coordinate of a representative. Off `O` it
is the natural projection `π : susp*(Σ) → Σ` of the draft (`these.tex:3578`, `dir_mk_of_pos`); on
`O` it is an arbitrary point, and every statement below that uses it is guarded by `∉ O`. -/
def dir (a : Susp S) : S := (Quotient.out a).1

theorem mk_dir_r (a : Susp S) : mk (a.dir, a.r) = a := by
  have h : mk (Quotient.out a) = a := Quotient.out_eq a
  have hr : a.r = (Quotient.out a).2 :=
    calc a.r = (mk (Quotient.out a)).r := by rw [h]
      _ = (Quotient.out a).2 := rfl
  rw [hr]
  exact h

theorem dir_mk_of_pos {q : S × ℝ≥0} (hq : 0 < q.2) : (mk q).dir = q.1 := by
  have h := mk_dir_r (mk q)
  exact (Prod.ext_iff.1 (eq_of_mk_eq_of_pos h (by simpa using hq))).1

theorem eq_of_dir_eq_of_r_eq {a b : Susp S} (hd : a.dir = b.dir) (hr : a.r = b.r) : a = b := by
  rw [← mk_dir_r a, ← mk_dir_r b, hd, hr]

theorem notMem_O_iff {a : Susp S} : a ∉ (O : Set (Susp S)) ↔ 0 < a.r := by
  rw [pos_iff_ne_zero]; rfl

theorem map_eq_mk (f : S → T) (a : Susp S) : map f a = mk (f a.dir, a.r) := by
  conv_lhs => rw [← mk_dir_r a]
  rfl

theorem dir_map_of_pos (f : S → T) {a : Susp S} (ha : 0 < a.r) : (map f a).dir = f a.dir := by
  rw [map_eq_mk]; exact dir_mk_of_pos ha

theorem map_mem_O_iff (f : S → T) {a : Susp S} : map f a ∈ (O : Set (Susp T)) ↔ a ∈ O := by
  show (map f a).r = 0 ↔ a.r = 0
  rw [r_map]

variable [TopologicalSpace S] [TopologicalSpace T]

/-- `π` is continuous on `susp*(Σ)`. -/
theorem continuousAt_dir {a : Susp S} (ha : 0 < a.r) : ContinuousAt dir a := by
  obtain ⟨q, rfl⟩ := mk_surjective a
  have hq : 0 < q.2 := ha
  unfold ContinuousAt
  rw [nhds_mk_of_pos hq, tendsto_map'_iff, dir_mk_of_pos hq]
  refine (continuous_fst.tendsto q).congr' ?_
  filter_upwards [isOpen_posPart.mem_nhds hq] with y hy
  exact (dir_mk_of_pos hy).symm

theorem continuous_mk_left (r : ℝ≥0) : Continuous fun σ : S => mk (σ, r) :=
  continuous_mk.comp (continuous_id.prodMk continuous_const)

/-- The radial extension `susp(f)` of a map continuous at `q.1` is continuous at `(q.1, q.2)`,
`q.2 > 0`. -/
theorem continuousAt_map_mk {f : S → T} {q : S × ℝ≥0} (hq : 0 < q.2) (hf : ContinuousAt f q.1) :
    ContinuousAt (map f) (mk q) := by
  unfold ContinuousAt
  rw [nhds_mk_of_pos hq, tendsto_map'_iff, map_mk]
  have : ContinuousAt (fun y : S × ℝ≥0 => (f y.1, y.2)) q :=
    (hf.comp continuous_fst.continuousAt).prodMk continuous_snd.continuousAt
  exact (continuous_mk.continuousAt.comp this)

/-! ### The radial extension of an action -/

/-- The radial extension of an action of `K` on `Σ` to `susp(Σ)`: `k · (σ, r) = (k · σ, r)`. A
`def`, to be installed with `letI`. -/
@[reducible] def radialAction (K : Type*) [Group K] [MulAction K S] : MulAction K (Susp S) where
  smul k a := map (k • ·) a
  one_smul a := by
    obtain ⟨q, rfl⟩ := mk_surjective a
    show mk (((1 : K) • q.1), q.2) = mk q
    rw [one_smul]
  mul_smul k k' a := by
    obtain ⟨q, rfl⟩ := mk_surjective a
    show mk ((k * k') • q.1, q.2) = mk (k • k' • q.1, q.2)
    rw [mul_smul]

end Susp

/-! ### Conic charts -/

variable {G : Type*} {X : Type*} [Group G] [TopologicalSpace X] [MulAction G X]

variable (X) in
/-- A **conic chart** at `p` with link `L` (the commented-out draft, `these.tex:3569`, first two
items, in BBS's reading):
a homeomorphism `φ` of an open neighbourhood `U = φ.source` of `p` onto an open neighbourhood
`φ.target` of the apex of `susp(L)`, with `φ p = O`. -/
structure ConicChart (p : X) (L : Type*) [TopologicalSpace L] where
  /-- The chart `φ_p : U_p → susp(X_p)`. -/
  φ : OpenPartialHomeomorph X (Susp L)
  mem_source : p ∈ φ.source
  map_mem_O : φ p ∈ Susp.O

omit [TopologicalSpace X] in
/-- An element of the stabiliser of `p` moves no other point to `p`. -/
theorem ConicChart.smul_ne_of_mem_stabilizer {p : X} {H : Subgroup G}
    (hH : H ≤ MulAction.stabilizer G p) {h : G} (hh : h ∈ H) {x : X} (hxp : x ≠ p) : h • x ≠ p := by
  intro hx
  have hp : h • p = p := hH hh
  exact hxp (MulAction.injective h (hx.trans hp.symm))

namespace ConicChart

variable {p : X} {L : Type*} [TopologicalSpace L] (c : ConicChart X p L)

theorem eq_of_map_mem_O {x : X} (hx : x ∈ c.φ.source) (h : c.φ x ∈ Susp.O) : x = p :=
  c.φ.injOn hx c.mem_source (Susp.eq_of_mem_O h c.map_mem_O)

theorem map_notMem_O {x : X} (hx : x ∈ c.φ.source) (hxp : x ≠ p) : c.φ x ∉ Susp.O :=
  fun h => hxp (c.eq_of_map_mem_O hx h)

theorem symm_mk_zero (σ : L) : c.φ.symm (Susp.mk (σ, 0)) = p := by
  rw [show Susp.mk (σ, 0) = c.φ p from Susp.eq_of_mem_O rfl c.map_mem_O]
  exact c.φ.left_inv c.mem_source

/-- Every neighbourhood of `p` meets every ray of the link: for each `σ : L` there is `x` in it,
off `p`, with `π(φ x) = σ`. (The topology of `susp` makes the balls `{r < ε}` a basis at `O`.) -/
theorem exists_mem_dir_eq {W : Set X} (hW : W ∈ 𝓝 p) (σ : L) :
    ∃ x ∈ c.φ.source ∩ W, c.φ x ∉ Susp.O ∧ (c.φ x).dir = σ := by
  obtain ⟨W', hW'W, hW'o, hpW'⟩ := mem_nhds_iff.1 hW
  have ho : IsOpen (c.φ '' (c.φ.source ∩ W')) := c.φ.isOpen_image_source_inter hW'o
  obtain ⟨ε, hε, hball⟩ :=
    Susp.exists_ball_subset_of_isOpen ho c.map_mem_O ⟨p, ⟨c.mem_source, hpW'⟩, rfl⟩
  have hmem : Susp.mk (σ, ε / 2) ∈ Susp.ball ε := show ε / 2 < ε from half_lt_self hε.ne'
  obtain ⟨x, ⟨hxs, hxW⟩, hx⟩ := hball hmem
  have hpos : (0 : ℝ≥0) < ε / 2 := half_pos hε
  refine ⟨x, ⟨hxs, hW'W hxW⟩, ?_, ?_⟩
  · rw [hx, Susp.notMem_O_iff]; exact hpos
  · rw [hx]; exact Susp.dir_mk_of_pos hpos

/-- The third item of the draft's definition, **verbatim** (`these.tex:3574`), for a subgroup
`H` of the stabiliser: for `h ∈ H` and `x, y ∈ U ∩ h⁻¹U` off `p`,
`π φ x = π φ y ⇒ π φ(hx) = π φ(hy)`. -/
def IsRayCompatible (H : Subgroup G) : Prop :=
  ∀ h ∈ H, ∀ x ∈ c.φ.source, ∀ y ∈ c.φ.source, h • x ∈ c.φ.source → h • y ∈ c.φ.source →
    c.φ x ∉ Susp.O → c.φ y ∉ Susp.O → (c.φ x).dir = (c.φ y).dir →
      (c.φ (h • x)).dir = (c.φ (h • y)).dir

variable {H : Subgroup G}

/-- `U ∩ h⁻¹U` is a neighbourhood of `p` (the step "comme `U ∩ g⁻¹U` est un voisinage de `p`" of
`these.tex:3588`; it needs `h` continuous). -/
theorem preimage_smul_source_mem_nhds [ContinuousConstSMul G X]
    (hH : H ≤ MulAction.stabilizer G p) {h : G} (hh : h ∈ H) :
    (fun x => h • x) ⁻¹' c.φ.source ∈ 𝓝 p := by
  have hp : h • p = p := hH hh
  refine (continuous_const_smul h).continuousAt.preimage_mem_nhds ?_
  rw [hp]; exact c.φ.open_source.mem_nhds c.mem_source

theorem exists_mem_smul_mem [ContinuousConstSMul G X] (hH : H ≤ MulAction.stabilizer G p)
    (h : H) (σ : L) : ∃ x ∈ c.φ.source, (h : G) • x ∈ c.φ.source ∧ c.φ x ∉ Susp.O ∧
      (c.φ x).dir = σ := by
  obtain ⟨x, ⟨hx, hhx⟩, hO, hd⟩ :=
    c.exists_mem_dir_eq (c.preimage_smul_source_mem_nhds hH h.2) σ
  exact ⟨x, hx, hhx, hO, hd⟩

/-- The underlying function of the induced action (`these.tex:3582`): `h · σ := π φ(h · x')` for a
chosen `x' ∈ U ∩ h⁻¹U` off `p` with `π φ x' = σ`. -/
def linkSmul [ContinuousConstSMul G X] (hH : H ≤ MulAction.stabilizer G p) (h : H) (σ : L) : L :=
  (c.φ ((h : G) • (c.exists_mem_smul_mem hH h σ).choose)).dir

/-- **The induced action is well defined** (`draft:propri_action`, the first half of the proof,
`these.tex:3588–3591`): `h · σ = π φ(h · x)` for EVERY `x ∈ U ∩ h⁻¹U` off `p` with `π φ x = σ`. -/
theorem linkSmul_spec [ContinuousConstSMul G X] (hH : H ≤ MulAction.stabilizer G p)
    (hc : c.IsRayCompatible H) (h : H) {x : X} (hx : x ∈ c.φ.source)
    (hhx : (h : G) • x ∈ c.φ.source) (hxO : c.φ x ∉ Susp.O) :
    c.linkSmul hH h (c.φ x).dir = (c.φ ((h : G) • x)).dir := by
  have hs := (c.exists_mem_smul_mem hH h (c.φ x).dir).choose_spec
  exact hc h h.2 _ hs.1 x hx hs.2.1 hhx hs.2.2.1 hxO hs.2.2.2

/-- **`draft:propri_action`** (`these.tex:3581`): the induced map is a group action of `H` on the
link — the draft's statement, under `ContinuousConstSMul G X` (carried: part of « structure
analytique »). -/
@[reducible] def linkAction [ContinuousConstSMul G X] (hH : H ≤ MulAction.stabilizer G p)
    (hc : c.IsRayCompatible H) : MulAction H L where
  smul := c.linkSmul hH
  one_smul σ := by
    obtain ⟨x, hx, -, hxO, hd⟩ := c.exists_mem_smul_mem hH 1 σ
    have h1 : ((1 : H) : G) • x ∈ c.φ.source := by simpa using hx
    have := c.linkSmul_spec hH hc 1 hx h1 hxO
    rw [hd] at this
    show c.linkSmul hH 1 σ = σ
    rw [this, show ((1 : H) : G) = 1 from rfl, one_smul, hd]
  mul_smul h₁ h₂ σ := by
    -- a point of `U ∩ h₂⁻¹U ∩ (h₁h₂)⁻¹U` on the ray `σ` (`these.tex:3593`)
    obtain ⟨x, ⟨hx, hx2, hx12⟩, hxO, hd⟩ := c.exists_mem_dir_eq
      (inter_mem (c.preimage_smul_source_mem_nhds hH h₂.2)
        (c.preimage_smul_source_mem_nhds hH (h₁ * h₂).2)) σ
    have hx12' : ((h₁ * h₂ : H) : G) • x ∈ c.φ.source := hx12
    have hx2' : (h₂ : G) • x ∈ c.φ.source := hx2
    have hxp : x ≠ p := fun e => hxO (e ▸ c.map_mem_O)
    have hx2O : c.φ ((h₂ : G) • x) ∉ Susp.O :=
      c.map_notMem_O hx2' (smul_ne_of_mem_stabilizer hH h₂.2 hxp)
    have e12 := c.linkSmul_spec hH hc (h₁ * h₂) hx hx12' hxO
    have e2 := c.linkSmul_spec hH hc h₂ hx hx2' hxO
    have hx12'' : (h₁ : G) • ((h₂ : G) • x) ∈ c.φ.source := by
      rw [← mul_smul]; exact hx12'
    have e1 := c.linkSmul_spec hH hc h₁ hx2' hx12'' hx2O
    rw [hd] at e12 e2
    show c.linkSmul hH (h₁ * h₂) σ = c.linkSmul hH h₁ (c.linkSmul hH h₂ σ)
    rw [e12, e2, e1, Subgroup.coe_mul, mul_smul]

/-- The characterisation of the induced action: `π φ(h·x) = h · π φ x` on `U ∩ h⁻¹U` off `p`. -/
theorem dir_smul_linkAction [ContinuousConstSMul G X] (hH : H ≤ MulAction.stabilizer G p)
    (hc : c.IsRayCompatible H) (h : H) {x : X} (hx : x ∈ c.φ.source)
    (hhx : (h : G) • x ∈ c.φ.source) (hxO : c.φ x ∉ Susp.O) :
    (c.φ ((h : G) • x)).dir = (letI := c.linkAction hH hc; h • (c.φ x).dir) :=
  (c.linkSmul_spec hH hc h hx hhx hxO).symm

/-- **Uniqueness of the induced action**: any action of `H` on `L` for which `π φ(h·x) = h · π φ x`
on `U ∩ h⁻¹U` off `p` is the induced one. -/
theorem linkAction_unique [ContinuousConstSMul G X] (hH : H ≤ MulAction.stabilizer G p)
    (inst : MulAction H L)
    (hdir : ∀ h : H, ∀ x ∈ c.φ.source, (h : G) • x ∈ c.φ.source → c.φ x ∉ Susp.O →
      (c.φ ((h : G) • x)).dir = h • (c.φ x).dir) (h : H) (σ : L) :
    h • σ = c.linkSmul hH h σ := by
  obtain ⟨x, hx, hhx, hxO, rfl⟩ := c.exists_mem_smul_mem hH h σ
  have hs := (c.exists_mem_smul_mem hH h (c.φ x).dir).choose_spec
  -- `hdir` computes the image of the chosen point on the ray
  unfold linkSmul
  rw [hdir h _ hs.1 hs.2.1 hs.2.2.1, hs.2.2.2]


/-- The draft's literal reading of "`φ_p : U → susp(X_p)` est un homéomorphisme": `φ` is ONTO the
whole cone. -/
def IsFull : Prop := c.φ.target = univ

end ConicChart

/-! ### Conic structures: a sufficient corrected form -/

variable (G) in
/-- A **conic structure** at `p` for the subgroup `H ≤ Stab_G(p)` with link `(H, L)`
(`draft:structure_conique`, `these.tex:3569`, in a SUFFICIENT corrected form): a conic chart
which conjugates each `h ∈ H`, on `U ∩ h⁻¹U`, to the radial extension `susp(h·)` of the given
action of `H` on `L`. It implies the draft's ray condition (`ConicStructure.isRayCompatible`);
the converse fails (radius preservation is extra), and the extra is what the draft's argument for
the suspension proposition uses (`these.tex:3667`: "`(φ_p g φ_p⁻¹)(φ_i(x), r) = (g φ_i(x),
r)`"). It is not the minimal correction: a radial lift `φ ∘ g_h = susp(h·) ∘ φ` with `g_h ∈ G`
(not necessarily `h`) also suffices for that proof. -/
structure ConicStructure (p : X) (H : Subgroup G) (L : Type*) [TopologicalSpace L]
    [MulAction H L] extends ConicChart X p L where
  le_stabilizer : H ≤ MulAction.stabilizer G p
  map_smul : ∀ h : H, ∀ x ∈ φ.source, (h : G) • x ∈ φ.source →
    φ ((h : G) • x) = Susp.map (fun σ : L => h • σ) (φ x)

namespace ConicStructure

variable {p : X} {H : Subgroup G} {L : Type*} [TopologicalSpace L] [MulAction H L]
  (c : ConicStructure G p H L)

theorem r_map_smul (h : H) {x : X} (hx : x ∈ c.φ.source) (hhx : (h : G) • x ∈ c.φ.source) :
    (c.φ ((h : G) • x)).r = (c.φ x).r := by
  rw [c.map_smul h x hx hhx, Susp.r_map]

theorem dir_map_smul (h : H) {x : X} (hx : x ∈ c.φ.source) (hhx : (h : G) • x ∈ c.φ.source)
    (hxO : c.φ x ∉ Susp.O) : (c.φ ((h : G) • x)).dir = h • (c.φ x).dir := by
  rw [c.map_smul h x hx hhx, Susp.dir_map_of_pos _ (Susp.notMem_O_iff.1 hxO)]

/-- A conic structure satisfies the draft's ray condition. -/
theorem isRayCompatible : c.IsRayCompatible H := by
  intro h hh x hx y hy hhx hhy hxO hyO hxy
  rw [c.dir_map_smul ⟨h, hh⟩ hx hhx hxO, c.dir_map_smul ⟨h, hh⟩ hy hhy hyO, hxy]

/-- The given action of `H` on `L` is the draft's induced action. -/
theorem smul_eq_linkSmul [ContinuousConstSMul G X] (h : H) (σ : L) :
    h • σ = c.linkSmul c.le_stabilizer h σ :=
  c.linkAction_unique c.le_stabilizer ‹_› (fun h x hx hhx hxO => c.dir_map_smul h hx hhx hxO) h σ

/-- A point `x ∈ U ∩ h⁻¹U` on the ray `σ` at radius `r`, for any `σ`, at a uniform radius: the
image of `U ∩ h⁻¹U` contains a ball `{r < ε}` around `O`. -/
theorem exists_ball_subset [ContinuousConstSMul G X] (h : H) :
    ∃ ε > 0, Susp.ball ε ⊆ c.φ '' (c.φ.source ∩ (fun x => (h : G) • x) ⁻¹' c.φ.source) := by
  have ho : IsOpen (c.φ '' (c.φ.source ∩ (fun x => (h : G) • x) ⁻¹' c.φ.source)) :=
    c.φ.isOpen_image_source_inter (c.φ.open_source.preimage (continuous_const_smul _))
  have hp : (h : G) • p = p := c.le_stabilizer h.2
  exact Susp.exists_ball_subset_of_isOpen ho c.map_mem_O
    ⟨p, ⟨c.mem_source, show (h : G) • p ∈ c.φ.source by rw [hp]; exact c.mem_source⟩, rfl⟩

include c in
/-- **The induced action is continuous** (`draft:propri_action`, continuity, not in the draft):
each `h ∈ H` acts on `L` by `σ ↦ π φ(h · φ⁻¹(σ, r₀))` for a fixed small `r₀`. -/
theorem continuousConstSMul [ContinuousConstSMul G X] : ContinuousConstSMul H L := by
  refine ⟨fun h => ?_⟩
  obtain ⟨ε, hε, hball⟩ := c.exists_ball_subset h
  set r₀ : ℝ≥0 := ε / 2
  have hr₀ : 0 < r₀ := half_pos hε
  have hmem : ∀ σ : L, Susp.mk (σ, r₀) ∈ c.φ '' (c.φ.source ∩
      (fun x => (h : G) • x) ⁻¹' c.φ.source) := fun σ =>
    hball (show r₀ < ε from half_lt_self hε.ne')
  -- the formula
  have key : ∀ σ : L, h • σ =
      (c.φ ((h : G) • c.φ.symm (Susp.mk (σ, r₀)))).dir := by
    intro σ
    obtain ⟨x, ⟨hx, hhx⟩, hxe⟩ := hmem σ
    have hxs : c.φ.symm (Susp.mk (σ, r₀)) = x := by rw [← hxe]; exact c.φ.left_inv hx
    rw [hxs, c.map_smul h x hx hhx, hxe, Susp.map_mk, Susp.dir_mk_of_pos hr₀]
  have hfun : (fun σ : L => h • σ) =
      fun σ => (c.φ ((h : G) • c.φ.symm (Susp.mk (σ, r₀)))).dir := funext key
  rw [hfun]
  refine continuous_iff_continuousAt.2 fun σ => ?_
  obtain ⟨x, ⟨hx, hhx⟩, hxe⟩ := hmem σ
  have htgt : Susp.mk (σ, r₀) ∈ c.φ.target := hxe ▸ c.φ.map_source hx
  have hxs : c.φ.symm (Susp.mk (σ, r₀)) = x := by rw [← hxe]; exact c.φ.left_inv hx
  have h1 : ContinuousAt (fun σ' : L => c.φ.symm (Susp.mk (σ', r₀))) σ :=
    ContinuousAt.comp (g := c.φ.symm) (f := fun σ' : L => Susp.mk (σ', r₀))
      (c.φ.continuousAt_symm htgt) (Susp.continuous_mk_left r₀).continuousAt
  have h2 : ContinuousAt (fun σ' : L => (h : G) • c.φ.symm (Susp.mk (σ', r₀))) σ :=
    (continuous_const_smul _).continuousAt.comp h1
  have h3 : ContinuousAt (fun σ' : L => c.φ ((h : G) • c.φ.symm (Susp.mk (σ', r₀)))) σ := by
    refine ContinuousAt.comp (f := fun σ' : L => (h : G) • c.φ.symm (Susp.mk (σ', r₀)))
      (g := c.φ) ?_ h2
    rw [hxs]; exact c.φ.continuousAt hhx
  refine ContinuousAt.comp (f := fun σ' : L => c.φ ((h : G) • c.φ.symm (Susp.mk (σ', r₀))))
    (g := Susp.dir) ?_ h3
  show ContinuousAt Susp.dir (c.φ ((h : G) • c.φ.symm (Susp.mk (σ, r₀))))
  rw [hxs, c.map_smul h x hx hhx, hxe]
  exact Susp.continuousAt_dir (show 0 < r₀ from hr₀)

include c in
/-- The core of `draft:lem_analytique`: if `h, k ∈ H` agree on a nonempty open subset of the link,
they agree on all of `X` (`G` rigid): they agree on the open cone over that subset. -/
theorem smul_eq_of_eqOn_link [ContinuousConstSMul G X] [IsRigidAction G X] {h k : H} {U : Set L}
    (hU : IsOpen U) (hne : U.Nonempty) (heq : EqOn (fun σ : L => h • σ) (fun σ => k • σ) U)
    (y : X) : (h : G) • y = (k : G) • y := by
  set A : Set X := c.φ.source ∩ (fun x => (h : G) • x) ⁻¹' c.φ.source ∩
    (fun x => (k : G) • x) ⁻¹' c.φ.source with hA
  have hAo : IsOpen A :=
    (c.φ.open_source.inter (c.φ.open_source.preimage (continuous_const_smul _))).inter
      (c.φ.open_source.preimage (continuous_const_smul _))
  have hBo : IsOpen (Susp.mk '' (U ×ˢ Ioi (0 : ℝ≥0)) : Set (Susp L)) :=
    Susp.isOpen_image_mk (hU.prod isOpen_Ioi) fun q hq => hq.2
  -- the open set of `X` over the cone on `U`, inside `U ∩ h⁻¹U ∩ k⁻¹U`
  set W : Set X := A ∩ c.φ ⁻¹' (Susp.mk '' (U ×ˢ Ioi 0)) with hW
  have hWo : IsOpen W :=
    (c.φ.continuousOn.mono fun x hx => hx.1.1).isOpen_inter_preimage hAo hBo
  have hnear : ∀ τ : L, ∃ x ∈ c.φ.source, (h : G) • x ∈ c.φ.source ∧
      (k : G) • x ∈ c.φ.source ∧ c.φ x ∉ Susp.O ∧ (c.φ x).dir = τ := by
    intro τ
    obtain ⟨x, ⟨hx, hhx, hkx⟩, hxO, hd⟩ := c.exists_mem_dir_eq
      (inter_mem (c.preimage_smul_source_mem_nhds c.le_stabilizer h.2)
        (c.preimage_smul_source_mem_nhds c.le_stabilizer k.2)) τ
    exact ⟨x, hx, hhx, hkx, hxO, hd⟩
  obtain ⟨σ₀, hσ₀⟩ := hne
  obtain ⟨x₀, hx₀, hhx₀, hkx₀, hx₀O, hd₀⟩ := hnear σ₀
  have hx₀W : x₀ ∈ W := by
    refine ⟨⟨⟨hx₀, hhx₀⟩, hkx₀⟩, ⟨((c.φ x₀).dir, (c.φ x₀).r), ⟨hd₀ ▸ hσ₀, ?_⟩,
      Susp.mk_dir_r _⟩⟩
    exact Susp.notMem_O_iff.1 hx₀O
  have heqW : EqOn (fun y : X => (h : G) • y) (fun y => (k : G) • y) W := by
    rintro y ⟨⟨⟨hy, hhy⟩, hky⟩, q, ⟨hqU, hq⟩, hqy⟩
    have hyO : c.φ y ∉ Susp.O := by
      rw [← hqy, Susp.notMem_O_iff]; exact hq
    have hdir : (c.φ y).dir ∈ U := by rw [← hqy, Susp.dir_mk_of_pos hq]; exact hqU
    refine c.φ.injOn hhy hky ?_
    show c.φ ((h : G) • y) = c.φ ((k : G) • y)
    rw [c.map_smul h y hy hhy, c.map_smul k y hy hky, Susp.map_eq_mk, Susp.map_eq_mk]
    exact congrArg (fun τ => Susp.mk (τ, (c.φ y).r)) (heq hdir)
  exact IsRigidAction.smul_eq_of_eqOn hWo ⟨x₀, hx₀W⟩ heqW y

include c in
/-- `h, k ∈ H` acting alike on `X` act alike on the link. -/
theorem smul_link_eq_of_forall [ContinuousConstSMul G X] {h k : H}
    (hall : ∀ y : X, (h : G) • y = (k : G) • y) (σ : L) : h • σ = k • σ := by
  obtain ⟨x, ⟨hx, hhx, hkx⟩, hxO, rfl⟩ := c.exists_mem_dir_eq
    (inter_mem (c.preimage_smul_source_mem_nhds c.le_stabilizer h.2)
      (c.preimage_smul_source_mem_nhds c.le_stabilizer k.2)) σ
  rw [← c.dir_map_smul h hx hhx hxO, ← c.dir_map_smul k hx hkx hxO, hall x]

include c in
/-- **Rigidity of the link, for a conic STRUCTURE** (radius preserved; row key
`draft:lem_analytique`, the draft's `these.tex:3606`, corrected): if `G` acts rigidly on `X`,
then `H` acts rigidly on the link. -/
theorem isRigidAction [ContinuousConstSMul G X] [IsRigidAction G X] : IsRigidAction H L :=
  ⟨fun hU hne heq σ => c.smul_link_eq_of_forall (c.smul_eq_of_eqOn_link hU hne heq) σ⟩

include c in
/-- **Analyticity of the link, for a conic STRUCTURE** (radius preserved; row key
`draft:lem_analytique`, the draft's `these.tex:3606`, corrected): if `G` acts analytically
(faithfully and rigidly) on `X`, then `H` acts analytically on the link `L`. For the draft's
ray-only notion the lemma, read literally, fails: faithfulness fails
(`GX.lem_analytique_counterexample`, `GX.Suspension.Affine`), the counterexample
motivating radius preservation. -/
theorem isAnalyticAction [ContinuousConstSMul G X] [IsAnalyticAction G X] :
    IsAnalyticAction H L := by
  have hL : Nonempty L := ⟨(c.φ p).dir⟩
  refine { toFaithfulSMul := ⟨fun {h k} heq => ?_⟩, toIsRigidAction := c.isRigidAction }
  obtain ⟨σ⟩ := hL
  have hall := c.smul_eq_of_eqOn_link isOpen_univ ⟨σ, mem_univ _⟩ (fun τ _ => heq τ)
  exact Subtype.ext (FaithfulSMul.eq_of_smul_eq_smul hall)


/-- **No contracting element** (a design note): if `h ∈ H` and the forward orbit of `x ∈ U` stays in
`U` and tends to `p`, then `x = p`. The radius `|φ(hⁿx)|` is constant and tends to `|φ p| = 0`.
So a RADIUS-PRESERVING conic structure (`ConicStructure`) exists for no `H` containing a
contraction fixing `p` — e.g. a linear map with an eigenvalue in `]0,1[`
(`GX.Suspension.Affine`). It says nothing about the draft's ray-only notion, nor about
the weaker radial-lift correction. -/
theorem eq_of_tendsto_pow (h : H) {x : X} (hx : x ∈ c.φ.source)
    (hxn : ∀ n : ℕ, ((h : G) ^ n) • x ∈ c.φ.source)
    (hlim : Tendsto (fun n : ℕ => ((h : G) ^ n) • x) atTop (𝓝 p)) : x = p := by
  have hr : ∀ n : ℕ, (c.φ (((h : G) ^ n) • x)).r = (c.φ x).r := by
    intro n
    induction n with
    | zero => rw [pow_zero, one_smul]
    | succ n ih =>
      have e : ((h : G) ^ (n + 1)) • x = (h : G) • (((h : G) ^ n) • x) := by
        rw [pow_succ', mul_smul]
      rw [e, c.r_map_smul h (hxn n) (e ▸ hxn (n + 1)), ih]
  have hlim' : Tendsto (fun n : ℕ => (c.φ (((h : G) ^ n) • x)).r) atTop (𝓝 (c.φ p).r) :=
    (Susp.continuous_r.tendsto _).comp ((c.φ.continuousAt c.mem_source).tendsto.comp hlim)
  have hconst : Tendsto (fun n : ℕ => (c.φ (((h : G) ^ n) • x)).r) atTop (𝓝 (c.φ x).r) := by
    simp only [hr]; exact tendsto_const_nhds
  have h0 : (c.φ x).r = 0 := (tendsto_nhds_unique hconst hlim').trans c.map_mem_O
  exact c.eq_of_map_mem_O hx h0

/-- **A full conic structure is equivariant on all of `U`** (needed by the suspension
proposition, `these.tex:3665`, whose computation is done on all of `U_i × ℝ₊*`): if `φ` is onto
the whole cone, every `h ∈ H` maps `U` into `U` and `φ(h·x) = susp(h·)(φ x)` for every `x ∈ U`.
The proof follows each ray `t ↦ φ⁻¹(σ, t)` from the apex by real induction. -/
theorem map_smul_of_isFull [T2Space X] [ContinuousConstSMul G X] (hf : c.IsFull) (h : H)
    {x : X} (hx : x ∈ c.φ.source) :
    (h : G) • x ∈ c.φ.source ∧ c.φ ((h : G) • x) = Susp.map (fun σ : L => h • σ) (c.φ x) := by
  set σ := (c.φ x).dir with hσ
  set R := (c.φ x).r with hR
  have hsymm : Continuous c.φ.symm := by
    rw [← continuousOn_univ]
    have := c.φ.continuousOn_symm
    rwa [show c.φ.target = univ from hf] at this
  have hsrc : ∀ a, c.φ.symm a ∈ c.φ.source := fun a =>
    c.φ.map_target (show a ∈ c.φ.target by rw [show c.φ.target = univ from hf]; trivial)
  have hrinv : ∀ a, c.φ (c.φ.symm a) = a := fun a =>
    c.φ.right_inv (show a ∈ c.φ.target by rw [show c.φ.target = univ from hf]; trivial)
  set γ : ℝ≥0 → X := fun t => c.φ.symm (Susp.mk (σ, t)) with hγdef
  set γ' : ℝ≥0 → X := fun t => c.φ.symm (Susp.mk (h • σ, t)) with hγ'def
  have hγ : Continuous γ :=
    hsymm.comp (Susp.continuous_mk.comp (continuous_const.prodMk continuous_id))
  have hγ' : Continuous γ' :=
    hsymm.comp (Susp.continuous_mk.comp (continuous_const.prodMk continuous_id))
  set T : Set ℝ≥0 := {t | (h : G) • γ t = γ' t} with hT
  have hTc : IsClosed T := isClosed_eq ((continuous_const_smul _).comp hγ) hγ'
  have h0 : (0 : ℝ≥0) ∈ T := by
    show (h : G) • γ 0 = γ' 0
    simp only [hγdef, hγ'def, c.symm_mk_zero]
    exact c.le_stabilizer h.2
  have hstep : ∀ t ∈ T ∩ Ico 0 R, T ∈ 𝓝[>] t := by
    rintro t ⟨ht, -⟩
    refine mem_nhdsWithin_of_mem_nhds ?_
    have hWo : IsOpen ((fun s => (h : G) • γ s) ⁻¹' c.φ.source) :=
      c.φ.open_source.preimage ((continuous_const_smul _).comp hγ)
    have htW : t ∈ (fun s => (h : G) • γ s) ⁻¹' c.φ.source := by
      show (h : G) • γ t ∈ c.φ.source
      rw [show (h : G) • γ t = γ' t from ht]; exact hsrc _
    refine mem_of_superset (hWo.mem_nhds htW) fun s hs => ?_
    have hs' : (h : G) • γ s ∈ c.φ.source := hs
    have e := c.map_smul h (γ s) (hsrc _) hs'
    rw [hrinv, Susp.map_mk] at e
    show (h : G) • γ s = γ' s
    calc (h : G) • γ s = c.φ.symm (c.φ ((h : G) • γ s)) := (c.φ.left_inv hs').symm
      _ = γ' s := by rw [e]
  have hRT : R ∈ T := IsClosed.Icc_subset_of_forall_mem_nhdsWithin (hTc.inter isClosed_Icc) h0
    hstep ⟨zero_le, le_rfl⟩
  have hxγ : γ R = x := by
    show c.φ.symm (Susp.mk ((c.φ x).dir, (c.φ x).r)) = x
    rw [Susp.mk_dir_r]; exact c.φ.left_inv hx
  have e : (h : G) • x = γ' R := by rw [← hxγ]; exact hRT
  refine ⟨e ▸ hsrc _, ?_⟩
  rw [e, hrinv, Susp.map_eq_mk]

end ConicStructure

/-- From the draft's data plus **radius preservation** (`|φ(h·x)| = |φ x|` on `U ∩ h⁻¹U`), the
induced action makes `φ` a conic structure. -/
def ConicChart.toConicStructure [ContinuousConstSMul G X] {p : X} {L : Type*}
    [TopologicalSpace L] {H : Subgroup G} (c : ConicChart X p L) (hH : H ≤ MulAction.stabilizer G p)
    (hc : c.IsRayCompatible H)
    (hr : ∀ h ∈ H, ∀ x ∈ c.φ.source, h • x ∈ c.φ.source → (c.φ (h • x)).r = (c.φ x).r) :
    letI := c.linkAction hH hc; ConicStructure G p H L :=
  letI := c.linkAction hH hc
  { toConicChart := c
    le_stabilizer := hH
    map_smul := fun h x hx hhx => by
      by_cases hxp : x = p
      · subst hxp
        have hp : (h : G) • x = x := hH h.2
        rw [hp]
        exact Susp.eq_of_mem_O c.map_mem_O ((Susp.map_mem_O_iff _).2 c.map_mem_O)
      · have hxO := c.map_notMem_O hx hxp
        refine Susp.eq_of_dir_eq_of_r_eq ?_ ?_
        · rw [Susp.dir_map_of_pos _ (Susp.notMem_O_iff.1 hxO)]
          exact c.dir_smul_linkAction hH hc h hx hhx hxO
        · rw [Susp.r_map]; exact hr h h.2 x hx hhx }

/-! ### Witness -/

/-- **Witness** (non-vacuity): the apex of `susp(L)` itself, for a group `K` acting on `L` and on
`susp(L)` radially (`Susp.radialAction`), with `H = ⊤` and `φ` the identity — a full conic
structure (`tautological_isFull`) for the whole group. -/
def ConicStructure.tautological (K : Type*) [Group K] (L : Type*) [TopologicalSpace L]
    [MulAction K L] (σ₀ : L) :
    letI := Susp.radialAction K (S := L); ConicStructure K (Susp.mk (σ₀, 0) : Susp L) ⊤ L :=
  letI := Susp.radialAction K (S := L)
  { φ := OpenPartialHomeomorph.refl _
    mem_source := mem_univ _
    map_mem_O := rfl
    le_stabilizer := fun _ _ => MulAction.mem_stabilizer_iff.2 (Susp.mk_zero_eq _ _)
    map_smul := fun _ _ _ _ => rfl }

theorem ConicStructure.tautological_isFull (K : Type*) [Group K] (L : Type*) [TopologicalSpace L]
    [MulAction K L] (σ₀ : L) :
    letI := Susp.radialAction K (S := L)
    (ConicStructure.tautological K L σ₀).toConicChart.IsFull :=
  rfl

end GX
