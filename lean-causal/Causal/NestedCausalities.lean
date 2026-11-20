import Causal.CauchyExtension
import Causal.Subdivision
import Mathlib.Topology.Connected.LocallyConnected

/-!
# Two nested causalities on one space: global hyperbolicity, domains of dependence, ERS19 §4

Programme target `T-abs-nested-causalities` (layer 1). No label of `ETT.tex`: the assertions are
the target's (`programme/roadmap.toml`), sources Eperon–Reall–Sbierski 1802.03020 (archived
`references/sbierski/text/eperon2018predictability.txt`) and Reall 2101.11623.

`T-abs-nested-causalities/1-gh` — wider GH ⇒ narrower GH with exactly the extra hypothesis
needed: `globallyHyperbolicOn_of_nested`, `globallyHyperbolic_iff_of_nested` (Hausdorff: iff the
narrower diamonds are closed), the bare implication refuted
(`not_globallyHyperbolic_of_nested_bare`).
`T-abs-nested-causalities/2-dod` — `dependenceDomainOn_subset_of_nested`,
`IsCauchySurfaceOn.of_nested` under the nesting of inextensible curves (a named localisation
hypothesis), discharged on `M` from ladder properties
(`GloballyHyperbolic.inextensibleNestedOn_top`); without it both fail
(`not_isCauchySurface_of_nested_bare`, `not_dependenceDomain_nested_bare`).
`T-abs-nested-causalities/3-ers-4.70` (ERS19 Lemma 4.70, text line 1761) — `ers_lemma_4_70_core`,
`ers_lemma_4_70`. `T-abs-nested-causalities/3-ers-4.72` (Lemma 4.72, line 1806) — `ers_lemma_4_72`.
`T-abs-nested-causalities/3-ers-4.77` (Theorem 4.77, line 1906) — `ers_theorem_4_77`,
`ers_theorem_4_77_greatest`. `T-abs-nested-causalities/3-ers-4.82` (Theorem 4.82, line 2027) —
`frontier_connectedComponentIn_inter` (4.84), `exists_spacelike_boundary_point` (4.85),
`ers_theorem_4_82`. The ERS items are causal-topological skeletons with named layer-3 hypotheses.
No assertion is marked (1-gh: see SCOPE).

> Lemma 4.70. Assume that there exists a vector field T on R^{d+1} such that T is timelike with
> respect to g^{µν}(u, du) for all u, du […]. Let u1 : U1 → R and u2 : U2 → R be two globally
> hyperbolic developments of (4.61) arising from the same initial data on a connected
> hypersurface S which has the property that every maximal integral curve of T intersects S at
> most once. Then U1 ∩ U2 is connected.

> Lemma 4.72. Let u1 : U1 → R and u2 : U2 → R be two GHDs of a subluminal quasilinear wave
> equation (4.61) arising from the same initial data given on a connected hypersurface S that is
> achronal with respect to the Minkowski metric m. Assume, moreover, that u1 : U1 → R is a
> m-GHD. Then U1 ∩ U2 is connected.

> Theorem 4.77. […] there then exists a unique maximal globally hyperbolic development
> umax : Umax → R […] for any other globally hyperbolic development u : U → R of the same initial
> data we have U ⊆ Umax and umax|U = u.

> Theorem 4.82. Let u1 : U1 → R be a MGHD […] and assume that for every p ∈ (∂U1 \ ∂S) […] all
> points below graph f […] are mapped into U1 and all points above graph f […] into R^{d+1} \ U1.
> (4.83) Then u1 : U1 → R is the unique MGHD.

## Nesting (the reading)

`LeNested C C'` (`≤_U` of `C` inside `≤_U` of `C'`, every open `U`) is the basic notion;
`CurveNestedOn` (causal curves of `W`) is implied by it; `InextensibleNestedOn` (inextensible curves
of `W`) is **not** (the cut line); item 2 is proved under it. Each result asks only the nesting
it uses, among these three: item 1 only `≤` at `M` (or at `W`); item 2 inextensible curves; 4.72 causal curves of `U₂`;
4.70 inextensible curves of the field's causality `Cτ` in each development. `≪`-nesting
(`LtNested`) is used by nothing here.

## Hypothesis checklist

| source hypothesis | here |
|---|---|
| 1-gh: nesting, wider GH | ✓ carried: `≤` at `M` only; ⚠ strengthened by what the target asks to find: narrower diamonds closed in the wider ones; sharp (iff, Hausdorff), hence unmarked |
| 2-dod: nesting | ⚠ named: `InextensibleNestedOn`; on `M` from `CurveNestedOn` + GH, tarentin, arc-connected, `J^±(x) ≠ {x}`, Hausdorff |
| 4.70: (4.62) `T` timelike for every `g(u, du)` | ⚠ named: `InextensibleNestedOn Cτ Cᵢ Uᵢ`; maximal integral curves `hthrough`; `Cτ` causal: no closed orbit of `T`, a layer-3 consequence of (4.62) — `g` does not depend on `x` (4.61), so `T` lies in one time cone of the constant metric `g(0, 0)` and a linear function increases strictly along its integral curves |
| 4.70: every maximal integral curve meets `S` at most once | ✓ `honce` (on the image); integral curves of `T` being injective, counting points or parameters agree; the core reads it "between two meetings the curve stays on `S`" |
| 4.70/4.72: GHDs, `S` connected | ✓ `IsCauchySurfaceOn Uᵢ S`, `IsPreconnected S` (GH of `Uᵢ` not used) |
| 4.72: subluminal | ✓ `CurveNestedOn C₂ Cm U₂` |
| 4.72: `S` m-achronal | ⚠ strengthened: m-acausal (`IsAcausal`); `Cm.CurvesExtend` named |
| 4.72: `u₁` is a GHD | ⚠ weakened: not used, only `U₁` m-GH with Cauchy surface `S` |
| 4.77: Cor 4.71 / Remark 4.67 | ⚠ named: one causality on the union; `S` Cauchy in each pairwise intersection |
| 4.77: (union causal) | ⚠ strengthened: `hcaus`, not in ERS (they get it a posteriori) |
| 4.82: (4.83) graph chart | ⚠ weakened: its topological content, `V ∩ U₁` preconnected for small `V` |
| 4.82: Steps 2–5 of Thm 4.64 | Step 2 proved (compactness, no geodesic); Steps 3–5 + Prop 4.63 named (`hstep`) |

## SCOPE (disclosed)

* **1-gh is not marked** (ruling of this wave): the bare "wider GH ⇒ narrower GH" is false
  (`not_globallyHyperbolic_of_nested_bare`, the line cut at `0`), and the theorem carries the
  closedness of the narrower diamonds, a hypothesis beyond nesting and the ladder. It is sharp:
  in a Hausdorff space, with the wider causality globally hyperbolic, the narrower one is globally
  hyperbolic iff its diamonds are closed (`globallyHyperbolic_iff_of_nested`).
* The ERS results are factored: what is proved is causal-topological; local existence (Thm 4.75),
  uniqueness on connected overlaps (Thm 4.64), integral curves of `T`, the time-separation
  function, spacelike level sets and their domains of dependence are named hypotheses.
* 4.77 concludes that `S` is a Cauchy surface of the union; "globally hyperbolic" from it is
  Geroch's (iii)⇒(i), the cited and unproved step of `CausalScaffold.GerochEquiv`, not invoked.
* `dependenceDomainOn` is definitionally `Causal.dependenceDomain` of `Causal.Flat.LipschitzGraph`
  (a model module, not importable here): two-sided, as the library's. `D^±` are not treated.
* `inextensible_ordConnectedComponent_on` restates, for an ambient open `W`, the strict library's
  `inextensible_ordConnectedComponent` (`W = ⊤`); the proof is that one, with `W` for `⊤`.
* `exists_minimal_of_isCompact_on` and `exists_spacelike_boundary_point` are the open-set forms of
  `Causality.exists_minimal_of_isCompact` and of Sbierski's Lemma 3.9 in
  `Causal.CBG.NoCorresponding` (`W = ⊤`, `J⁻` closed in `M`), which imports a model and cannot be
  imported here.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Filter Function

open scoped Interval

universe u

variable {M : Type u} [TopologicalSpace M]

/-! ## 0. Nesting -/

/-- A curve for the relations `r` is a curve for any family `r'` containing them. -/
theorem CurveOn.of_rel_imp {r r' : Opens M → M → M → Prop} {W : Opens M} {c : ℝ → M} {a b : ℝ}
    (hc : CurveOn r W c a b) (h : ∀ N x y, r N x y → r' N x y) : CurveOn r' W c a b where
  mem := hc.mem
  rel t ht N hN htN := by
    obtain ⟨l, u, hl, hu, hrel⟩ := hc.rel t ht N hN htN
    exact ⟨l, u, hl, hu, fun s hs s' hs' h1 h2 h3 => h _ _ _ (hrel s hs s' hs' h1 h2 h3)⟩

namespace Causality

/-- **Nesting for the causal relation**: `C'` is wider than `C` when every `x ≤_U y` of `C` is an
`x ≤_U y` of `C'`, for every open `U`. -/
def LeNested (C C' : Causality M) : Prop :=
  ∀ ⦃U : Opens M⦄ ⦃x y : M⦄, C.le U x y → C'.le U x y

/-- **Nesting for the chronological relation**. -/
def LtNested (C C' : Causality M) : Prop :=
  ∀ ⦃U : Opens M⦄ ⦃x y : M⦄, C.lt U x y → C'.lt U x y

/-- **Nesting for the causal curves of `W`**: every future causal curve of `W` for `C`, over a
segment, is one for `C'`. Implied by `LeNested` (`LeNested.curveNestedOn`). -/
def CurveNestedOn (C C' : Causality M) (W : Opens M) : Prop :=
  ∀ ⦃c : ℝ → M⦄ ⦃a b : ℝ⦄, C.CausalCurveOn W c a b → C'.CausalCurveOn W c a b

/-- **Nesting for the inextensible curves of `W`** — a localisation hypothesis: every inextensible
causal curve of `W` for the narrower `C` is an inextensible causal curve of `W` for `C'`. -/
def InextensibleNestedOn (C C' : Causality M) (W : Opens M) : Prop :=
  ∀ ⦃I : Set ℝ⦄ ⦃c : ℝ → M⦄, C.Inextensible W I c → C'.Inextensible W I c

variable {C C' : Causality M} {U V W : Opens M} {I : Set ℝ} {c : ℝ → M} {S : Set M}

theorem LeNested.refl (C : Causality M) : LeNested C C := fun _ _ _ h => h

theorem LeNested.trans {C'' : Causality M} (h : LeNested C C') (h' : LeNested C' C'') :
    LeNested C C'' := fun _ _ _ hxy => h' (h hxy)

theorem dual_leNested_iff : LeNested C.dual C'.dual ↔ LeNested C C' :=
  ⟨fun h _ _ _ hxy => h hxy, fun h _ _ _ hxy => h hxy⟩

theorem LeNested.curveNestedOn (h : LeNested C C') (W : Opens M) : CurveNestedOn C C' W :=
  fun _ _ _ hc => CurveOn.of_rel_imp hc fun _ _ _ h' => h h'

theorem CurveNestedOn.causalCurveIn (h : CurveNestedOn C C' W) (hc : C.CausalCurveIn W I c) :
    C'.CausalCurveIn W I c :=
  ⟨hc.nonempty, hc.ordConnected, fun a ha b hb => h (hc.curve a ha b hb)⟩

theorem CurveNestedOn.mono (h : CurveNestedOn C C' W) (hVW : V ≤ W) : CurveNestedOn C C' V :=
  fun _ _ _ hc => CurveOn.restrict (h (CurveOn.mono_opens C.isRelFamily_le hc hVW)) le_rfl le_rfl
    hVW hc.mem

/-! ## 1. Wider globally hyperbolic ⇒ narrower globally hyperbolic -/

theorem isCausal_of_le_top (hle : ∀ x y, C.le ⊤ x y → C'.le ⊤ x y) (h : C'.IsCausal) :
    C.IsCausal :=
  fun x y hxy hyx => h (hle x y hxy) (hle y x hyx)

theorem diamond_subset_of_le (hle : ∀ x y, C.le W x y → C'.le W x y) (p q : M) :
    C.diamond W p q ⊆ C'.diamond W p q := fun z hz => by
  rw [mem_diamond] at hz ⊢
  exact ⟨hle _ _ hz.1, hle _ _ hz.2⟩

/-- **Wider GH ⇒ narrower GH, on an open set `W`**, under the exact extra hypothesis: each
narrower diamond is closed inside the wider one. -/
theorem globallyHyperbolicOn_of_nested (hle : ∀ x y, C.le W x y → C'.le W x y)
    (hGH : C'.GloballyHyperbolicOn W)
    (hrel : ∀ p q, closure (C.diamond W p q) ∩ C'.diamond W p q ⊆ C.diamond W p q) :
    C.GloballyHyperbolicOn W := by
  refine ⟨fun x y hxy hyx => hGH.1 (hle _ _ hxy) (hle _ _ hyx), fun p q => ?_⟩
  have heq : C.diamond W p q = C'.diamond W p q ∩ closure (C.diamond W p q) :=
    Subset.antisymm (fun z hz => ⟨diamond_subset_of_le hle p q hz, subset_closure hz⟩)
      (fun z hz => hrel p q ⟨hz.2, hz.1⟩)
  rw [heq]
  exact (hGH.2 p q).inter_right isClosed_closure

/-- **Wider GH ⇒ narrower GH**. -/
theorem GloballyHyperbolic.of_nested (hle : ∀ x y, C.le ⊤ x y → C'.le ⊤ x y)
    (hGH : C'.GloballyHyperbolic)
    (hrel : ∀ p q, closure (C.diamond ⊤ p q) ∩ C'.diamond ⊤ p q ⊆ C.diamond ⊤ p q) :
    C.GloballyHyperbolic :=
  globallyHyperbolicOn_of_nested hle hGH hrel

theorem GloballyHyperbolic.of_nested_of_isClosed (hle : ∀ x y, C.le ⊤ x y → C'.le ⊤ x y)
    (hGH : C'.GloballyHyperbolic) (hcl : ∀ p q, IsClosed (C.diamond ⊤ p q)) :
    C.GloballyHyperbolic :=
  GloballyHyperbolic.of_nested hle hGH fun p q => by
    rw [(hcl p q).closure_eq]; exact inter_subset_left

theorem GloballyHyperbolic.of_nested_of_isClosed_J (hle : ∀ x y, C.le ⊤ x y → C'.le ⊤ x y)
    (hGH : C'.GloballyHyperbolic) (hJp : ∀ x, IsClosed (C.Jplus ⊤ {x}))
    (hJm : ∀ x, IsClosed (C.Jminus ⊤ {x})) : C.GloballyHyperbolic :=
  GloballyHyperbolic.of_nested_of_isClosed hle hGH fun p q => (hJm q).inter (hJp p)

/-- **In a Hausdorff space, closed narrower diamonds are exactly what is needed.** -/
theorem globallyHyperbolic_iff_of_nested [T2Space M] (hle : ∀ x y, C.le ⊤ x y → C'.le ⊤ x y)
    (hGH : C'.GloballyHyperbolic) :
    C.GloballyHyperbolic ↔ ∀ p q, IsClosed (C.diamond ⊤ p q) :=
  ⟨fun h p q => (h.2 p q).isClosed, GloballyHyperbolic.of_nested_of_isClosed hle hGH⟩

end Causality

/-! ### The witness: a cut line -/

/-- **The line cut at `a`**: the timelike line in which nothing lies causally before `a` but `a`
itself. `x ≤_U y` iff `x = y ∈ U`, or `x < y`, `y ≠ a` and `[x, y] ⊆ U`. -/
def cutLine (a : ℝ) : Causality ℝ where
  le U x y := (x = y ∧ x ∈ U) ∨ (x < y ∧ y ≠ a ∧ Icc x y ⊆ (U : Set ℝ))
  lt U x y := x < y ∧ y ≠ a ∧ Icc x y ⊆ (U : Set ℝ)
  le_mem_left h := by
    rcases h with ⟨-, h⟩ | ⟨h1, -, h2⟩
    · exact h
    · exact h2 (left_mem_Icc.2 h1.le)
  le_mem_right h := by
    rcases h with ⟨rfl, h⟩ | ⟨h1, -, h2⟩
    · exact h
    · exact h2 (right_mem_Icc.2 h1.le)
  lt_mem_left h := h.2.2 (left_mem_Icc.2 h.1.le)
  lt_mem_right h := h.2.2 (right_mem_Icc.2 h.1.le)
  le_refl hx := Or.inl ⟨rfl, hx⟩
  le_trans h₁ h₂ := by
    rcases h₁ with ⟨rfl, -⟩ | ⟨h1, h2, h3⟩
    · exact h₂
    rcases h₂ with ⟨rfl, -⟩ | ⟨h1', h2', h3'⟩
    · exact Or.inr ⟨h1, h2, h3⟩
    · exact Or.inr ⟨h1.trans h1', h2', Icc_subset_Icc_union_Icc.trans (union_subset h3 h3')⟩
  lt_trans h₁ h₂ := ⟨h₁.1.trans h₂.1, h₂.2.1,
    Icc_subset_Icc_union_Icc.trans (union_subset h₁.2.2 h₂.2.2)⟩
  le_mono h _ _ h' := by
    rcases h' with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
    · exact Or.inl ⟨h1, h h2⟩
    · exact Or.inr ⟨h1, h2, fun _ hz => h (h3 hz)⟩
  lt_mono h _ _ h' := ⟨h'.1, h'.2.1, fun _ hz => h (h'.2.2 hz)⟩
  le_of_lt h := Or.inr h
  isOpen_lt_right U x := by
    have : {y : ℝ | x < y ∧ y ≠ a ∧ Icc x y ⊆ (U : Set ℝ)} =
        {y : ℝ | x < y ∧ Icc x y ⊆ (U : Set ℝ)} ∩ {a}ᶜ := by
      ext y; simp only [mem_setOf_eq, mem_inter_iff, mem_compl_iff, mem_singleton_iff]; tauto
    rw [this]
    exact (isOpen_setOf_lt_and_Icc_subset_right U x).inter isOpen_compl_singleton
  isOpen_lt_left U y := by
    by_cases hy : y = a
    · have : {x : ℝ | x < y ∧ y ≠ a ∧ Icc x y ⊆ (U : Set ℝ)} = ∅ := by
        ext x; simp [hy]
      rw [this]; exact isOpen_empty
    · have : {x : ℝ | x < y ∧ y ≠ a ∧ Icc x y ⊆ (U : Set ℝ)} =
          {x : ℝ | x < y ∧ Icc x y ⊆ (U : Set ℝ)} := by
        ext x; simp only [mem_setOf_eq]; tauto
      rw [this]
      exact isOpen_setOf_lt_and_Icc_subset_left U y

theorem cutLine_leNested (a : ℝ) : (cutLine a).LeNested timelikeLine := by
  intro U x y h
  rcases h with ⟨rfl, hx⟩ | ⟨h1, -, h3⟩
  · exact ⟨le_rfl, by simpa using hx⟩
  · exact ⟨h1.le, h3⟩

theorem cutLine_isCausal (a : ℝ) : (cutLine a).IsCausal :=
  fun _ _ hxy hyx => timelikeLine_isCausal (cutLine_leNested a hxy) (cutLine_leNested a hyx)

/-- The cut line is not globally hyperbolic: its diamond from `a - 1` to `a + 1` is
`[a - 1, a + 1] ∖ {a}`. -/
theorem cutLine_not_globallyHyperbolic (a : ℝ) : ¬ (cutLine a).GloballyHyperbolic := by
  intro h
  have hcl := (h.2 (a - 1) (a + 1)).isClosed
  have hsub : Ioo a (a + 1) ⊆ (cutLine a).diamond ⊤ (a - 1) (a + 1) := by
    intro z hz
    rw [Causality.mem_diamond]
    refine ⟨Or.inr ⟨by linarith [hz.1], ne_of_gt hz.1, subset_univ _⟩,
      Or.inr ⟨hz.2, by linarith, subset_univ _⟩⟩
  have hmem : a ∈ closure (Ioo a (a + 1)) := by
    rw [closure_Ioo (by linarith : a ≠ a + 1)]
    exact ⟨le_rfl, by linarith⟩
  have ha := hcl.closure_subset (closure_mono hsub hmem)
  rw [Causality.mem_diamond] at ha
  rcases ha.1 with ⟨h1, -⟩ | ⟨-, h2, -⟩
  · linarith
  · exact h2 rfl

/-- **The bare implication "wider GH ⇒ narrower GH" is false**, even for local causalities on a
line: the cut line is nested in the (globally hyperbolic) timelike line and is not globally
hyperbolic. -/
theorem not_globallyHyperbolic_of_nested_bare :
    ¬ ∀ C C' : Causality ℝ, C.LeNested C' → C'.GloballyHyperbolic → C.GloballyHyperbolic :=
  fun h => cutLine_not_globallyHyperbolic 0
    (h _ _ (cutLine_leNested 0) timelikeLine_globallyHyperbolic)

namespace Causality

variable {C C' : Causality M} {U V W : Opens M} {I : Set ℝ} {c : ℝ → M} {S : Set M}

/-! ## 2. Domains of dependence and Cauchy surfaces -/

variable (C) in
/-- **The domain of dependence** `D(S)` of `S` in the open `W`: the points of `W` every
inextensible causal curve of `W` through which meets `S`. -/
def dependenceDomainOn (W : Opens M) (S : Set M) : Set M :=
  {p | p ∈ W ∧ ∀ (I : Set ℝ) (c : ℝ → M), C.Inextensible W I c → p ∈ c '' I →
    (c '' I ∩ S).Nonempty}

theorem dependenceDomainOn_subset : C.dependenceDomainOn W S ⊆ W := fun _ hp => hp.1

theorem subset_dependenceDomainOn (hSW : S ⊆ W) : S ⊆ C.dependenceDomainOn W S :=
  fun p hp => ⟨hSW hp, fun _ _ _ hpc => ⟨p, hpc, hp⟩⟩

theorem dependenceDomainOn_eq_of_isCauchySurfaceOn (h : C.IsCauchySurfaceOn W S) :
    C.dependenceDomainOn W S = W :=
  Subset.antisymm dependenceDomainOn_subset fun _ hp => ⟨hp, fun I c hc _ => by
    obtain ⟨x, hx, -⟩ := h I c hc
    exact ⟨x, hx⟩⟩

/-- **Nested domains of dependence**: the wider causality has the smaller domain of dependence,
when inextensibility is nested. -/
theorem dependenceDomainOn_subset_of_nested (h : InextensibleNestedOn C C' W) (S : Set M) :
    C'.dependenceDomainOn W S ⊆ C.dependenceDomainOn W S :=
  fun _ hp => ⟨hp.1, fun I c hc hpc => hp.2 I c (h hc) hpc⟩

/-- **A Cauchy surface of the wider causality is one of the narrower**, when inextensibility is
nested. -/
theorem IsCauchySurfaceOn.of_nested (h : InextensibleNestedOn C C' W)
    (hS : C'.IsCauchySurfaceOn W S) : C.IsCauchySurfaceOn W S :=
  fun I c hc => hS I c (h hc)

/-- A curve `c` over `I` read through a strictly increasing `φ` onto an interval: `c'` with
`c' ∘ φ = c` on `I` is a causal curve over `φ '' I`. Purely order-theoretic. -/
theorem causalCurveIn_image_of_comp {φ : ℝ → ℝ} {c' : ℝ → M} (hc : C.CausalCurveIn W I c)
    (hφ : StrictMonoOn φ I) (hoc : (φ '' I).OrdConnected) (heq : ∀ t ∈ I, c' (φ t) = c t) :
    C.CausalCurveIn W (φ '' I) c' := by
  refine ⟨hc.nonempty.image φ, hoc, ?_⟩
  rintro _ ⟨α, hα, rfl⟩ _ ⟨β, hβ, rfl⟩
  rcases lt_or_ge (φ β) (φ α) with hba | hab
  · exact CurveOn.of_lt hba
  have hIcc : Icc α β ⊆ I := hc.ordConnected.out hα hβ
  have hpre : ∀ τ ∈ Icc (φ α) (φ β), ∃ ρ ∈ Icc α β, φ ρ = τ := by
    intro τ hτ
    obtain ⟨ρ, hρ, rfl⟩ := hoc.out (mem_image_of_mem φ hα) (mem_image_of_mem φ hβ) hτ
    exact ⟨ρ, ⟨(hφ.le_iff_le hα hρ).1 hτ.1, (hφ.le_iff_le hρ hβ).1 hτ.2⟩, rfl⟩
  have hcurve := hc.curve α hα β hβ
  refine ⟨fun τ hτ => ?_, fun τ hτ N hN hτN => ?_⟩
  · obtain ⟨ρ, hρ, rfl⟩ := hpre τ hτ
    rw [heq ρ (hIcc hρ)]; exact hcurve.mem ρ hρ
  obtain ⟨σ, hσ, rfl⟩ := hpre τ hτ
  rw [heq σ (hIcc hσ)] at hτN
  obtain ⟨l₀, u₀, hl₀, hu₀, hrel⟩ := hcurve.rel σ hσ N hN hτN
  obtain ⟨l, hl, hlow⟩ : ∃ l, l < φ σ ∧ ∀ ρ ∈ Icc α β, l < φ ρ → l₀ < ρ := by
    by_cases hασ : α < σ
    · have hρ₁σ : max ((l₀ + σ) / 2) α < σ := max_lt (by linarith) hασ
      have hl₀ρ₁ : l₀ < max ((l₀ + σ) / 2) α := lt_of_lt_of_le (by linarith) (le_max_left _ _)
      have hρ₁I : max ((l₀ + σ) / 2) α ∈ I := hIcc ⟨le_max_right _ _, hρ₁σ.le.trans hσ.2⟩
      refine ⟨φ (max ((l₀ + σ) / 2) α), hφ hρ₁I (hIcc hσ) hρ₁σ, fun ρ hρ h => ?_⟩
      exact hl₀ρ₁.trans ((hφ.lt_iff_lt hρ₁I (hIcc hρ)).1 h)
    · have hσα : σ = α := le_antisymm (not_lt.1 hασ) hσ.1
      refine ⟨φ σ - 1, by linarith, fun ρ hρ _ => ?_⟩
      have : σ ≤ ρ := by rw [hσα]; exact hρ.1
      exact hl₀.trans_le this
  obtain ⟨u, hu, hup⟩ : ∃ u, φ σ < u ∧ ∀ ρ ∈ Icc α β, φ ρ < u → ρ < u₀ := by
    by_cases hσβ : σ < β
    · have hσρ₂ : σ < min ((σ + u₀) / 2) β := lt_min (by linarith) hσβ
      have hρ₂u₀ : min ((σ + u₀) / 2) β < u₀ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
      have hρ₂I : min ((σ + u₀) / 2) β ∈ I := hIcc ⟨hσ.1.trans hσρ₂.le, min_le_right _ _⟩
      refine ⟨φ (min ((σ + u₀) / 2) β), hφ (hIcc hσ) hρ₂I hσρ₂, fun ρ hρ h => ?_⟩
      exact ((hφ.lt_iff_lt (hIcc hρ) hρ₂I).1 h).trans hρ₂u₀
    · have hσβ' : σ = β := le_antisymm hσ.2 (not_lt.1 hσβ)
      refine ⟨φ σ + 1, by linarith, fun ρ hρ _ => ?_⟩
      have : ρ ≤ σ := by rw [hσβ']; exact hρ.2
      exact lt_of_le_of_lt this hu₀
  refine ⟨l, u, hl, hu, fun τ₁ hτ₁ τ₂ hτ₂ h1 h2 h3 => ?_⟩
  obtain ⟨ρ₁, hρ₁, rfl⟩ := hpre τ₁ hτ₁
  obtain ⟨ρ₂, hρ₂, rfl⟩ := hpre τ₂ hτ₂
  rw [heq ρ₁ (hIcc hρ₁), heq ρ₂ (hIcc hρ₂)]
  exact hrel ρ₁ hρ₁ ρ₂ hρ₂ (hlow ρ₁ hρ₁ h1) ((hφ.lt_iff_lt (hIcc hρ₁) (hIcc hρ₂)).1 h2)
    (hup ρ₂ hρ₂ h3)

/-- **A strict extension at the past end by a continuous curve gives one by a causal curve**, when
`C` is causally arc-connected, causal, strongly causal, has closed causal pasts and no point
without causal past. The extending curve `c'` is a causal curve of any causality `C'`: only its
continuity is used. -/
theorem extensible_of_strictlyExtendsPast (hC : C.CausallyArcConnected) (hcaus : C.IsCausal)
    (hSC : C.StronglyCausal) (hJm : ∀ x, IsClosed (C.Jminus ⊤ {x}))
    (hpast : ∀ x, C.Jminus ⊤ {x} ≠ {x}) (hc : C.CausalCurveIn ⊤ I c) {I' : Set ℝ}
    {c' : ℝ → M} (h : C'.StrictlyExtendsPast ⊤ I c I' c') : C.Extensible ⊤ I c := by
  obtain ⟨hc', ⟨φ, hφ, hmaps, hoc, heq, hfinal⟩, ⟨t', ht', hnew⟩⟩ := h
  have hbelow : ∀ t ∈ I, t' < φ t := fun t ht => lt_of_not_ge fun hle => by
    obtain ⟨s, hs, hse⟩ := hfinal t ht t' ht' hle
    exact hnew s hs (by rw [← hse]; exact heq s hs)
  obtain ⟨t₀, ht₀⟩ := hc.nonempty
  have hJne : (φ '' I).Nonempty := ⟨φ t₀, t₀, ht₀, rfl⟩
  have hJbdd : BddBelow (φ '' I) := ⟨t', by rintro _ ⟨t, ht, rfl⟩; exact (hbelow t ht).le⟩
  have hs₀le : ∀ t ∈ I, sInf (φ '' I) ≤ φ t := fun t ht => csInf_le hJbdd ⟨t, ht, rfl⟩
  have ht's₀ : t' ≤ sInf (φ '' I) :=
    le_csInf hJne (by rintro _ ⟨t, ht, rfl⟩; exact (hbelow t ht).le)
  have hs₀I' : sInf (φ '' I) ∈ I' :=
    hc'.ordConnected.out ht' (hmaps ht₀) ⟨ht's₀, hs₀le t₀ ht₀⟩
  by_cases hs₀J : sInf (φ '' I) ∈ φ '' I
  · obtain ⟨a, ha, hφa⟩ := hs₀J
    have hleast : IsLeast I a :=
      ⟨ha, fun t ht => (hφ.le_iff_le ha ht).1 (by rw [hφa]; exact hs₀le t ht)⟩
    exact extensible_of_isLeast hC hcaus hc hleast (hpast (c a))
  have hJcurve : C.CausalCurveIn ⊤ (φ '' I) c' := causalCurveIn_image_of_comp hc hφ hoc heq
  have hgt : ∀ t ∈ φ '' I, sInf (φ '' I) < t := fun t ht =>
    lt_of_le_of_ne (csInf_le hJbdd ht) fun h => hs₀J (h ▸ ht)
  have hins : (insert (sInf (φ '' I)) (φ '' I)).OrdConnected := by
    refine ⟨fun x hx y hy z hz => ?_⟩
    rcases eq_or_ne z (sInf (φ '' I)) with hzs | hzs
    · rw [hzs]; exact mem_insert _ _
    refine mem_insert_of_mem _ ?_
    have hs₀z : sInf (φ '' I) < z := by
      rcases hx with hx | hx
      · rw [hx] at hz; exact lt_of_le_of_ne hz.1 (Ne.symm hzs)
      · exact (hgt x hx).trans_le hz.1
    rcases hy with hy | hy
    · rw [hy] at hz; exact absurd hz.2 (not_le.2 hs₀z)
    obtain ⟨j, hj, hjz⟩ := exists_lt_of_csInf_lt hJne hs₀z
    exact hoc.out hj hy ⟨hjz.le, hz.2⟩
  have hφt₀ : sInf (φ '' I) < φ t₀ := hgt _ ⟨t₀, ht₀, rfl⟩
  have hlim : Tendsto c' (𝓝[>] (sInf (φ '' I))) (𝓝 (c' (sInf (φ '' I)))) := by
    have hw := hc'.continuousOn_Icc hs₀I' (hmaps ht₀) (sInf (φ '' I)) ⟨le_rfl, hφt₀.le⟩
    exact hw.tendsto.mono_left
      (nhdsWithin_le_of_mem (mem_of_superset (Ioo_mem_nhdsGT hφt₀) Ioo_subset_Icc_self))
  exact (extensible_of_tendsto hJm hSC hC hcaus hJcurve hgt hins hlim (hpast _)).of_comp hφ
    (mapsTo_image φ I) (surjOn_image φ I) heq

/-- **Inextensibility is nested on `M`** when the narrower causality is causally arc-connected,
causal, strongly causal, with closed `J^±` of points and no point without causal past or
future, and its causal curves are curves of the wider one. -/
theorem inextensibleNestedOn_top (hnest : CurveNestedOn C C' ⊤) (hC : C.CausallyArcConnected)
    (hcaus : C.IsCausal) (hSC : C.StronglyCausal) (hJp : ∀ x, IsClosed (C.Jplus ⊤ {x}))
    (hJm : ∀ x, IsClosed (C.Jminus ⊤ {x})) (hpast : ∀ x, C.Jminus ⊤ {x} ≠ {x})
    (hfut : ∀ x, C.Jplus ⊤ {x} ≠ {x}) : InextensibleNestedOn C C' ⊤ := by
  intro I c hc
  refine ⟨hnest.causalCurveIn hc.1, fun hext => hc.2 ?_⟩
  rcases (extensible_iff (C := C') hc.1.nonempty).1 hext with ⟨I', c', hp⟩ | hf
  · exact extensible_of_strictlyExtendsPast hC hcaus hSC hJm hpast hc.1 hp
  · have hpd : C'.dual.PastExtensible ⊤ (-I) (fun t => c (-t)) :=
      PastExtensible.of_dual_reverse (C := C'.dual) (I := -I) (c := fun t => c (-t))
        (by simpa using hf)
    obtain ⟨I'', c'', hpe⟩ := hpd
    exact Extensible.of_dual_reverse (extensible_of_strictlyExtendsPast (C := C.dual)
      (C' := C'.dual) (dual_causallyArcConnectedOn.2 hC) (dual_isCausal.2 hcaus)
      (dual_stronglyCausal.2 hSC) hJp hfut hc.1.reverse hpe)

/-- The same, from global hyperbolicity of the narrower causality (Hausdorff, tarentin). -/
theorem GloballyHyperbolic.inextensibleNestedOn_top [T2Space M] (hT : C.Tarentin)
    (hG : C.GloballyHyperbolic) (hC : C.CausallyArcConnected)
    (hpast : ∀ x, C.Jminus ⊤ {x} ≠ {x}) (hfut : ∀ x, C.Jplus ⊤ {x} ≠ {x})
    (hnest : CurveNestedOn C C' ⊤) : InextensibleNestedOn C C' ⊤ :=
  Causality.inextensibleNestedOn_top hnest hC hG.1 (hG.stronglyCausal hT)
    (hG.isClosed_Jplus_singleton hT) (hG.isClosed_Jminus_singleton hT) hpast hfut

/-- **A Cauchy surface of the wider causality is one of the narrower, on `M`**, from ladder
properties of the narrower one alone (Hausdorff, tarentin, globally hyperbolic, causally
arc-connected, no point without causal past or future) and the nesting of causal curves. -/
theorem GloballyHyperbolic.isCauchySurface_of_nested [T2Space M] (hT : C.Tarentin)
    (hG : C.GloballyHyperbolic) (hC : C.CausallyArcConnected)
    (hpast : ∀ x, C.Jminus ⊤ {x} ≠ {x}) (hfut : ∀ x, C.Jplus ⊤ {x} ≠ {x})
    (hnest : CurveNestedOn C C' ⊤) (hS : C'.IsCauchySurface S) : C.IsCauchySurface S :=
  IsCauchySurfaceOn.of_nested (hG.inextensibleNestedOn_top hT hC hpast hfut hnest) hS

/-- **Nested domains of dependence, on `M`**, under the same ladder properties. -/
theorem GloballyHyperbolic.dependenceDomainOn_subset_of_nested [T2Space M] (hT : C.Tarentin)
    (hG : C.GloballyHyperbolic) (hC : C.CausallyArcConnected)
    (hpast : ∀ x, C.Jminus ⊤ {x} ≠ {x}) (hfut : ∀ x, C.Jplus ⊤ {x} ≠ {x})
    (hnest : CurveNestedOn C C' ⊤) (S : Set M) :
    C'.dependenceDomainOn ⊤ S ⊆ C.dependenceDomainOn ⊤ S :=
  Causality.dependenceDomainOn_subset_of_nested
    (hG.inextensibleNestedOn_top hT hC hpast hfut hnest) S

/-- **Items 1 and 2 together**: if the wider causality is globally hyperbolic with Cauchy surface
`S`, the narrower one is globally hyperbolic with Cauchy surface `S` as soon as its diamonds are
closed, it is tarentin, causally arc-connected and no point lacks a causal past or future. -/
theorem globallyHyperbolic_isCauchySurface_of_nested [T2Space M] (hle : LeNested C C')
    (hGH : C'.GloballyHyperbolic) (hcl : ∀ p q, IsClosed (C.diamond ⊤ p q)) (hT : C.Tarentin)
    (hC : C.CausallyArcConnected) (hpast : ∀ x, C.Jminus ⊤ {x} ≠ {x})
    (hfut : ∀ x, C.Jplus ⊤ {x} ≠ {x}) (hS : C'.IsCauchySurface S) :
    C.GloballyHyperbolic ∧ C.IsCauchySurface S := by
  have hG : C.GloballyHyperbolic :=
    GloballyHyperbolic.of_nested_of_isClosed (fun _ _ h => hle h) hGH hcl
  exact ⟨hG, hG.isCauchySurface_of_nested hT hC hpast hfut (hle.curveNestedOn ⊤) hS⟩

end Causality

/-! ### The witness: the nesting of inextensibility cannot be dropped -/

/-- On the line cut at `1`, the identity over `[1, +∞[` is an inextensible causal curve. -/
theorem cutLine_inextensible_Ici : (cutLine 1).Inextensible ⊤ (Ici 1) id := by
  have hcurve : (cutLine 1).CausalCurveIn ⊤ (Ici 1) id := by
    refine ⟨⟨1, self_mem_Ici⟩, ordConnected_Ici, fun a ha b _ => ?_⟩
    refine ⟨fun _ _ => trivial, fun t _ N _ htN => ?_⟩
    obtain ⟨l, u, ⟨hl, hu⟩, hlu⟩ := mem_nhds_iff_exists_Ioo_subset.1 (N.isOpen.mem_nhds htN)
    refine ⟨l, u, hl, hu, fun s hs s' _ h1 h2 h3 => Or.inr ⟨h2, ?_, ?_⟩⟩
    · have h1a : (1 : ℝ) ≤ a := ha
      have : (1 : ℝ) < s' := lt_of_le_of_lt (h1a.trans hs.1) h2
      exact ne_of_gt this
    · intro z hz; exact hlu ⟨h1.trans_le hz.1, hz.2.trans_lt h3⟩
  refine ⟨hcurve, fun hext => ?_⟩
  rcases (Causality.extensible_iff ⟨1, self_mem_Ici⟩).1 hext with
    ⟨I', c', hc', ⟨φ, -, hmaps, -, heq, hfin⟩, ⟨t', ht', hnew⟩⟩ |
    ⟨I', c', hc', ⟨φ, -, hmaps, -, heq, hinit⟩, ⟨t', ht', hnew⟩⟩
  · have hlt : t' < φ 1 := lt_of_not_ge fun h => by
      obtain ⟨s, hs, hse⟩ := hfin 1 self_mem_Ici t' ht' h
      exact hnew s hs (by rw [← hse]; exact heq s hs)
    have hrel := hc'.le_of_le ht' (hmaps self_mem_Ici) hlt.le
    rw [heq 1 self_mem_Ici] at hrel
    rcases hrel with ⟨h1, -⟩ | ⟨-, h2, -⟩
    · exact hnew 1 self_mem_Ici h1
    · exact h2 rfl
  · have hgt : ∀ t ∈ Ici (1 : ℝ), φ t < t' := fun t ht => lt_of_not_ge fun h => by
      obtain ⟨s, hs, hse⟩ := hinit t ht t' ht' h
      exact hnew s hs (by rw [← hse]; exact heq s hs)
    have hge : ∀ t ∈ Ici (1 : ℝ), t ≤ c' t' := fun t ht => by
      have := cutLine_leNested 1 (hc'.le_of_le (hmaps ht) ht' (hgt t ht).le)
      rw [heq t ht] at this
      exact this.1
    have h1 := hge 1 self_mem_Ici
    have h2 := hge (c' t' + 1) (by rw [mem_Ici]; linarith)
    linarith

/-- **"A Cauchy surface of the wider causality is one of the narrower" is false without the
nesting of inextensibility**: `{0}` is a Cauchy surface of the timelike line, not of the line cut
at `1`, which is nested in it. -/
theorem not_isCauchySurface_of_nested_bare :
    ¬ ∀ (C C' : Causality ℝ) (S : Set ℝ), C.LeNested C' → C'.IsCauchySurface S →
      C.IsCauchySurface S := by
  intro h
  obtain ⟨_, ⟨⟨t, ht, rfl⟩, hx⟩, -⟩ := h (cutLine 1) timelikeLine {0} (cutLine_leNested 1)
    timelikeLine_isCauchySurface_zero (Ici 1) id cutLine_inextensible_Ici
  have h1 : (1 : ℝ) ≤ t := ht
  rw [mem_singleton_iff, id] at hx
  linarith

/-- **Nor are domains of dependence nested without it**: `1` lies in the domain of dependence of
`{0}` for the timelike line and not for the line cut at `1`. -/
theorem not_dependenceDomain_nested_bare :
    ¬ ∀ (C C' : Causality ℝ) (S : Set ℝ), C.LeNested C' →
      C'.dependenceDomainOn ⊤ S ⊆ C.dependenceDomainOn ⊤ S := by
  intro h
  have h1 : (1 : ℝ) ∈ timelikeLine.dependenceDomainOn ⊤ {0} := by
    rw [Causality.dependenceDomainOn_eq_of_isCauchySurfaceOn timelikeLine_isCauchySurface_zero]
    trivial
  obtain ⟨-, hD⟩ := h (cutLine 1) timelikeLine {0} (cutLine_leNested 1) h1
  obtain ⟨_, ⟨t, ht, rfl⟩, hx⟩ := hD (Ici 1) id cutLine_inextensible_Ici ⟨1, self_mem_Ici, rfl⟩
  have h1 : (1 : ℝ) ≤ t := ht
  rw [mem_singleton_iff, id] at hx
  linarith

namespace Causality

variable {C C' : Causality M} {U V W : Opens M} {I : Set ℝ} {c : ℝ → M} {S : Set M}

/-! ## 3. ERS19, causal-topological skeletons -/

/-! ### Tools -/

theorem CausalCurveIn.continuousOn_uIcc (hc : C.CausalCurveIn W I c) {a b : ℝ} (ha : a ∈ I)
    (hb : b ∈ I) : ContinuousOn c [[a, b]] := by
  rcases le_total a b with h | h
  · rw [uIcc_of_le h]; exact hc.continuousOn_Icc ha hb
  · rw [uIcc_of_ge h]; exact hc.continuousOn_Icc hb ha

/-- A set every point of which is joined, by a path inside it, to a preconnected subset, is
preconnected. -/
theorem isPreconnected_of_segments {A S : Set M} (hS : IsPreconnected S) (hSA : S ⊆ A)
    (h : ∀ x ∈ A, ∃ (c : ℝ → M) (a b : ℝ), ContinuousOn c [[a, b]] ∧ c a = x ∧ c b ∈ S ∧
      c '' [[a, b]] ⊆ A) : IsPreconnected A := by
  rcases S.eq_empty_or_nonempty with hSe | ⟨s₀, hs₀⟩
  · have hA : A = ∅ := eq_empty_iff_forall_notMem.2 fun x hx => by
      obtain ⟨c, a, b, -, -, hb, -⟩ := h x hx
      rw [hSe] at hb; exact hb
    rw [hA]; exact isPreconnected_empty
  refine isPreconnected_of_forall s₀ fun y hy => ?_
  obtain ⟨c, a, b, hcont, rfl, hb, hsub⟩ := h y hy
  refine ⟨S ∪ c '' [[a, b]], union_subset hSA hsub, Or.inl hs₀,
    Or.inr ⟨a, left_mem_uIcc, rfl⟩, ?_⟩
  exact hS.union (c b) hb ⟨b, right_mem_uIcc, rfl⟩ (isPreconnected_uIcc.image c hcont)

/-- Along a causal curve of a causal causality, a curve point lying causally between `c a` and
`c b` is the image of a parameter between `a` and `b`. -/
theorem mem_image_uIcc_of_between (hcaus : C.IsCausal) (hc : C.CausalCurveIn ⊤ I c)
    {a b r : ℝ} (ha : a ∈ I) (hb : b ∈ I) (hr : r ∈ I)
    (hbtw : (C.le ⊤ (c a) (c r) ∧ C.le ⊤ (c r) (c b)) ∨
      (C.le ⊤ (c b) (c r) ∧ C.le ⊤ (c r) (c a))) : c r ∈ c '' [[a, b]] := by
  by_cases hrab : r ∈ [[a, b]]
  · exact ⟨r, hrab, rfl⟩
  have hle : ∀ s ∈ I, ∀ t ∈ I, s ≤ t → C.le ⊤ (c s) (c t) := fun s hs t ht h =>
    hc.le_of_le hs ht h
  have key : c r = c a ∨ c r = c b := by
    rw [mem_uIcc] at hrab
    push Not at hrab
    obtain ⟨h1, h2⟩ := hrab
    rcases lt_or_ge r a with hra | hra
    · have hrb : r < b := lt_of_not_ge fun hbr => absurd (h2 hbr) (not_lt.2 hra.le)
      rcases hbtw with ⟨k1, -⟩ | ⟨k1, -⟩
      · exact Or.inl (hcaus (hle r hr a ha hra.le) k1)
      · exact Or.inr (hcaus (hle r hr b hb hrb.le) k1)
    · have hbr : b < r := h1 hra
      have har : a < r := h2 hbr.le
      rcases hbtw with ⟨-, k2⟩ | ⟨-, k2⟩
      · exact Or.inr (hcaus k2 (hle b hb r hr hbr.le))
      · exact Or.inl (hcaus k2 (hle a ha r hr har.le))
  rcases key with h | h
  · rw [h]; exact ⟨a, left_mem_uIcc, rfl⟩
  · rw [h]; exact ⟨b, right_mem_uIcc, rfl⟩

/-- Along a causal curve of `W`, `W` causal, a curve which returns to a point is constant in
between. -/
theorem eq_of_mem_uIcc_of_eq (hcaus : ∀ ⦃x y : M⦄, C.le W x y → C.le W y x → x = y)
    (hc : C.CausalCurveIn W I c) {s t u : ℝ} (hs : s ∈ I) (ht : t ∈ I) (hst : c s = c t)
    (hu : u ∈ [[s, t]]) : c u = c s := by
  have huI : u ∈ I := hc.ordConnected.uIcc_subset hs ht hu
  rcases le_total s t with h | h
  · rw [uIcc_of_le h] at hu
    have h1 := hc.le_of_le hs huI hu.1
    have h2 := hc.le_of_le huI ht hu.2
    rw [← hst] at h2
    exact hcaus h2 h1
  · rw [uIcc_of_ge h] at hu
    have h1 := hc.le_of_le ht huI hu.1
    have h2 := hc.le_of_le huI hs hu.2
    rw [← hst] at h1
    exact hcaus h2 h1

/-- **A curve of `M` entering a Cauchy development stays in it until it meets the Cauchy
surface.** `U` open, `S ⊆ U` an acausal Cauchy surface of `U`, `c` an inextensible causal curve of
`M` (Hausdorff, causal) with `c t₀ ∈ U`: then `c` maps every segment from `t₀` to a parameter of
`c⁻¹(S)` into `U`. -/
theorem image_uIcc_subset_of_isCauchySurfaceOn [T2Space M] (hcaus : C.IsCausal) (hSU : S ⊆ U)
    (hU : C.IsCauchySurfaceOn U S) (hS : C.IsAcausal S) (hc : C.Inextensible ⊤ I c) {t₀ r : ℝ}
    (ht₀ : t₀ ∈ I) (hr : r ∈ I) (hx : c t₀ ∈ U) (hrS : c r ∈ S) : c '' [[t₀, r]] ⊆ U := by
  have hJ := inextensible_ordConnectedComponent hcaus hc ht₀ hx
  obtain ⟨_, ⟨⟨σ, hσ, rfl⟩, hσS⟩, -⟩ := hU _ c hJ
  have hσI : σ ∈ I := (ordConnectedComponent_subset hσ).1
  have hσr : c σ = c r := by
    rcases le_total σ r with h | h
    · exact hS _ hσS _ hrS (hc.1.le_of_le hσI hr h)
    · exact (hS _ hrS _ hσS (hc.1.le_of_le hr hσI h)).symm
  have ht₀J : t₀ ∈ ordConnectedComponent (I ∩ c ⁻¹' U) t₀ :=
    self_mem_ordConnectedComponent.2 ⟨ht₀, hx⟩
  have hJoc : (ordConnectedComponent (I ∩ c ⁻¹' U) t₀).OrdConnected := inferInstance
  rintro _ ⟨u, hu, rfl⟩
  rcases uIcc_subset_uIcc_union_uIcc (b := σ) hu with hu | hu
  · exact (ordConnectedComponent_subset (hJoc.uIcc_subset ht₀J hσ hu)).2
  · rw [eq_of_mem_uIcc_of_eq hcaus hc.1 hσI hr hσr hu]; exact hSU hσS

/-! ### The component of an inextensible curve, in an open set `W` -/

/-- `futureExtensible_of_final` (`Causal.CauchyExtension`), in an open set `W` instead of `M`. -/
theorem futureExtensible_of_final_on (hcaus : ∀ ⦃x y : M⦄, C.le W x y → C.le W y x → x = y)
    {I J I' : Set ℝ} {c c' : ℝ → M} {t₀ : ℝ}
    (hc : C.CausalCurveIn W I c) (hJI : J ⊆ I) (ht₀ : t₀ ∈ J)
    (hfin : ∀ t ∈ I, ∀ s ∈ J, s ≤ t → t ∈ J)
    (hc' : C.CausalCurveIn W I' c') {φ : ℝ → ℝ} (hφ : StrictMonoOn φ J) (hmaps : MapsTo φ J I')
    (hoc : (φ '' J).OrdConnected) (heq : ∀ t ∈ J, c' (φ t) = c t)
    (hinit : ∀ t ∈ J, ∀ t' ∈ I', t' ≤ φ t → t' ∈ φ '' J)
    {t' : ℝ} (ht' : t' ∈ I') (hlt : ∀ t ∈ J, φ t < t') (hnew : ∀ t ∈ J, c' t' ≠ c t) :
    C.FutureExtensible W I c := by
  set δ := φ t₀ - t₀ with hδ
  set I'' : Set ℝ := {t | (t ∈ I ∧ t ≤ t₀) ∨ (t₀ ≤ t ∧ t + δ ∈ I')} with hI''
  set d : ℝ → M := fun t => if t ≤ t₀ then c t else c' (t + δ) with hd
  set ψ : ℝ → ℝ := fun t => if t ≤ t₀ then t else φ t - δ with hψ
  have ht₀I : t₀ ∈ I := hJI ht₀
  have hφt₀ : φ t₀ = t₀ + δ := by rw [hδ]; ring
  have hI''le : ∀ t ∈ I'', t ≤ t₀ → t ∈ I := by
    rintro t (⟨h, -⟩ | ⟨h1, -⟩) h2
    · exact h
    · rw [le_antisymm h2 h1]; exact ht₀I
  have hI''ge : ∀ t ∈ I'', t₀ ≤ t → t + δ ∈ I' := by
    rintro t (⟨-, h1⟩ | ⟨-, h⟩) h2
    · rw [le_antisymm h1 h2, ← hφt₀]; exact hmaps ht₀
    · exact h
  have ht₀I'' : t₀ ∈ I'' := Or.inl ⟨ht₀I, le_rfl⟩
  have hgtJ : ∀ t ∈ I, t₀ ≤ t → t ∈ J := fun t ht h => hfin t ht t₀ ht₀ h
  have hdle : ∀ t, t ≤ t₀ → d t = c t := fun t h => if_pos h
  have hdgt : ∀ t, t₀ < t → d t = c' (t + δ) := fun t h => if_neg (not_le.2 h)
  have hdt₀ : d t₀ = c' (t₀ + δ) := by rw [hdle t₀ le_rfl, ← hφt₀, heq t₀ ht₀]
  have hshift : ∀ a b : ℝ, a + δ ∈ I' → b + δ ∈ I' →
      CurveOn C.le W (fun t => c' (t + δ)) a b := fun a b ha hb => by
    have h := CurveOn.comp_affine (r := C.le) (W := W) (c := c') (k := 1) (m := δ) (a' := a)
      (b' := b) one_pos (by rw [one_mul, one_mul]; exact hc'.curve _ ha _ hb)
    exact h.congr fun t _ => by simp only [one_mul]
  -- the new curve
  have hd_curve : C.CausalCurveIn W I'' d := by
    refine ⟨⟨t₀, ht₀I''⟩, ⟨fun x hx y hy z hz => ?_⟩, fun a ha b hb => ?_⟩
    · rcases le_total z t₀ with hzt | hzt
      · exact Or.inl ⟨hc.ordConnected.out (hI''le x hx (hz.1.trans hzt)) ht₀I ⟨hz.1, hzt⟩, hzt⟩
      · refine Or.inr ⟨hzt, ?_⟩
        rcases le_total y t₀ with hyt | hyt
        · have : z = t₀ := le_antisymm (hz.2.trans hyt) hzt
          rw [this, ← hφt₀]; exact hmaps ht₀
        · exact hc'.ordConnected.out (hmaps ht₀) (hI''ge y hy hyt)
            ⟨by rw [hφt₀]; linarith, by linarith [hz.2]⟩
    · rcases lt_or_ge b a with hba | hab
      · exact CurveOn.of_lt hba
      by_cases hbt : b ≤ t₀
      · exact CurveOn.congr (hc.curve a (hI''le a ha (hab.trans hbt)) b (hI''le b hb hbt))
          fun t ht => (hdle t (ht.2.trans hbt)).symm
      by_cases hta : t₀ ≤ a
      · refine (hshift a b (hI''ge a ha hta) (hI''ge b hb (hta.trans hab))).congr
          fun t ht => ?_
        rcases (hta.trans ht.1).eq_or_lt with h | h
        · rw [← h, hdt₀]
        · rw [hdgt t h]
      · have hbt' : t₀ < b := lt_of_not_ge hbt
        have hta' : a < t₀ := lt_of_not_ge hta
        have h2 := hshift t₀ b (by rw [← hφt₀]; exact hmaps ht₀) (hI''ge b hb hbt'.le)
        have := CurveOn.concat C.isRelFamily_le (hc.curve a (hI''le a ha hta'.le) t₀ ht₀I) h2
          hta'.le hbt'.le (by rw [← hdt₀, hdle t₀ le_rfl])
        exact this
  -- the reparametrisation
  have hψle : ∀ t, t ≤ t₀ → ψ t = t := fun t h => if_pos h
  have hψgt : ∀ t, t₀ < t → ψ t = φ t - δ := fun t h => if_neg (not_le.2 h)
  have hφgt : ∀ t ∈ J, t₀ < t → t₀ < φ t - δ := fun t ht h => by
    have := hφ ht₀ ht h; linarith
  have hφgt' : ∀ t ∈ J, φ t₀ < φ t → t₀ < t := fun t ht h =>
    lt_of_not_ge fun h' => absurd (hφ.monotoneOn ht ht₀ h') (not_le.2 h)
  have hψmono : StrictMonoOn ψ I := by
    intro s hs t ht hst
    rcases le_or_gt t t₀ with htt | htt
    · rw [hψle s (hst.le.trans htt), hψle t htt]; exact hst
    · rw [hψgt t htt]
      rcases le_or_gt s t₀ with hst' | hst'
      · rw [hψle s hst']; linarith [hφgt t (hgtJ t ht htt.le) htt]
      · rw [hψgt s hst']
        have := hφ (hgtJ s hs hst'.le) (hgtJ t ht htt.le) hst
        linarith
  have hψmaps : MapsTo ψ I I'' := by
    intro t ht
    rcases le_or_gt t t₀ with htt | htt
    · rw [hψle t htt]; exact Or.inl ⟨ht, htt⟩
    · rw [hψgt t htt]
      refine Or.inr ⟨(hφgt t (hgtJ t ht htt.le) htt).le, ?_⟩
      rw [sub_add_cancel]; exact hmaps (hgtJ t ht htt.le)
  have hψoc : (ψ '' I).OrdConnected := by
    refine ⟨?_⟩
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ z hz
    rcases le_or_gt z t₀ with hzt | hzt
    · have hat : a ≤ t₀ := le_of_not_gt fun h => by
        have := hφgt a (hgtJ a ha h.le) h
        rw [hψgt a h] at hz; linarith [hz.1]
      rw [hψle a hat] at hz
      exact ⟨z, hc.ordConnected.out ha ht₀I ⟨hz.1, hzt⟩, hψle z hzt⟩
    · have hbt : t₀ < b := lt_of_not_ge fun h => by
        rw [hψle b h] at hz; linarith [hz.2]
      have hbJ := hgtJ b hb hbt.le
      rw [hψgt b hbt] at hz
      obtain ⟨w, hw, hwz⟩ := hoc.out (mem_image_of_mem φ ht₀) (mem_image_of_mem φ hbJ)
        (show z + δ ∈ Icc (φ t₀) (φ b) from ⟨by rw [hφt₀]; linarith, by linarith [hz.2]⟩)
      have hwt : t₀ < w := hφgt' w hw (by rw [hwz, hφt₀]; linarith)
      exact ⟨w, hJI hw, by rw [hψgt w hwt, hwz]; ring⟩
  have hdψ : ∀ t ∈ I, d (ψ t) = c t := by
    intro t ht
    rcases le_or_gt t t₀ with htt | htt
    · rw [hψle t htt, hdle t htt]
    · have htJ := hgtJ t ht htt.le
      rw [hψgt t htt, hdgt _ (hφgt t htJ htt), sub_add_cancel]
      exact heq t htJ
  have hψinit : ∀ t ∈ I, ∀ t'' ∈ I'', t'' ≤ ψ t → t'' ∈ ψ '' I := by
    intro t ht t'' ht'' hle
    rcases le_or_gt t'' t₀ with h | h
    · exact ⟨t'', hI''le t'' ht'' h, hψle t'' h⟩
    · have htt : t₀ < t := lt_of_not_ge fun h' => by rw [hψle t h'] at hle; linarith
      have htJ := hgtJ t ht htt.le
      rw [hψgt t htt] at hle
      obtain ⟨w, hw, hwz⟩ := hinit t htJ (t'' + δ) (hI''ge t'' ht'' h.le) (by linarith)
      have hwt : t₀ < w := hφgt' w hw (by rw [hwz, hφt₀]; linarith)
      exact ⟨w, hJI hw, by rw [hψgt w hwt, hwz]; ring⟩
  -- the new value
  have hφt' : φ t₀ < t' := hlt t₀ ht₀
  have hnewI'' : t' - δ ∈ I'' := Or.inr ⟨by rw [hφt₀] at hφt'; linarith, by
    rw [sub_add_cancel]; exact ht'⟩
  have hdnew : d (t' - δ) = c' t' := by
    rw [hdgt _ (by rw [hφt₀] at hφt'; linarith), sub_add_cancel]
  refine ⟨I'', d, hd_curve, ⟨ψ, hψmono, hψmaps, hψoc, hdψ, hψinit⟩,
    ⟨t' - δ, hnewI'', fun s hs => ?_⟩⟩
  rw [hdnew]
  by_cases hsJ : s ∈ J
  · exact hnew s hsJ
  · intro heqs
    have hst : s < t₀ := lt_of_not_ge fun h => hsJ (hgtJ s hs h)
    have h1 : C.le W (d s) (d t₀) := hd_curve.le_of_le (Or.inl ⟨hs, hst.le⟩) ht₀I'' hst.le
    have h2 : C.le W (d t₀) (d (t' - δ)) :=
      hd_curve.le_of_le ht₀I'' hnewI'' (by rw [hφt₀] at hφt'; linarith)
    rw [hdle s hst.le, hdle t₀ le_rfl] at h1
    rw [hdnew, heqs, hdle t₀ le_rfl] at h2
    exact hnew t₀ ht₀ (heqs.trans (hcaus h1 h2))

/-- `not_futureExtensible_of_component` (`Causal.CauchyExtension`), in an open set `W`. -/
theorem not_futureExtensible_of_component_on [T2Space M]
    (hcaus : ∀ ⦃x y : M⦄, C.le W x y → C.le W y x → x = y) (hUW : U ≤ W)
    {I J : Set ℝ} {c : ℝ → M} {t₀ : ℝ} (hc : C.FutureInextensible W I c) (hJI : J ⊆ I)
    (ht₀ : t₀ ∈ J) (hJoc : J.OrdConnected) (hJU : ∀ t ∈ J, c t ∈ U)
    (hmax : ∀ t ∈ I, [[t₀, t]] ⊆ c ⁻¹' U → t ∈ J) : ¬ C.FutureExtensible U J c := by
  rintro ⟨I', c', hcurve, ⟨φ, hφ, hmaps, hoc, heq, hinit⟩, ⟨t', ht', hnew⟩⟩
  have hlt : ∀ t ∈ J, φ t < t' := fun t ht => lt_of_not_ge fun h => by
    obtain ⟨s, hs, hse⟩ := hinit t ht t' ht' h
    exact hnew s hs (hse ▸ heq s hs)
  by_cases hfin : ∀ t ∈ I, ∀ s ∈ J, s ≤ t → t ∈ J
  · exact hc.2 (futureExtensible_of_final_on hcaus hc.1 hJI ht₀ hfin (hcurve.mono_opens hUW) hφ
      hmaps hoc heq hinit ht' hlt hnew)
  push Not at hfin
  obtain ⟨T, hT, s, hs, hsT, hTJ⟩ := hfin
  have hJlt : ∀ j ∈ J, j < T := fun j hj =>
    lt_of_not_ge fun h => hTJ (hJoc.out hs hj ⟨hsT, h⟩)
  have hJne : J.Nonempty := ⟨t₀, ht₀⟩
  have hbdd : BddAbove J := ⟨T, fun j hj => (hJlt j hj).le⟩
  set β := sSup J with hβ
  have ht₀β : t₀ ≤ β := le_csSup hbdd ht₀
  have hβT : β ≤ T := csSup_le hJne fun j hj => (hJlt j hj).le
  have ht₀T : t₀ ≤ T := ht₀β.trans hβT
  have hIcc : Icc t₀ T ⊆ I := hc.1.ordConnected.out (hJI ht₀) hT
  have hβI : β ∈ I := hIcc ⟨ht₀β, hβT⟩
  have hcont : ContinuousOn c (Icc t₀ T) := hc.1.continuousOn_Icc (hJI ht₀) hT
  have hbelow : ∀ y, t₀ ≤ y → y < β → y ∈ J := fun y h1 h2 => by
    obtain ⟨j, hj, hyj⟩ := exists_lt_of_lt_csSup hJne h2
    exact hJoc.out ht₀ hj ⟨h1, hyj.le⟩
  have hnbhd : c β ∈ U → ∃ ε > 0, ∀ y ∈ Icc t₀ T, dist y β < ε → c y ∈ U := fun hβU => by
    have h : c ⁻¹' (U : Set M) ∈ 𝓝[Icc t₀ T] β :=
      hcont β ⟨ht₀β, hβT⟩ (U.isOpen.mem_nhds hβU)
    rw [Metric.mem_nhdsWithin_iff] at h
    obtain ⟨ε, hε, hsub⟩ := h
    exact ⟨ε, hε, fun y hy hyd => hsub ⟨hyd, hy⟩⟩
  have hβJ : β ∉ J := fun hβJ => by
    obtain ⟨ε, hε, hU⟩ := hnbhd (hJU β hβJ)
    have hβT' : β < T := hJlt β hβJ
    have hβx : β < min (β + ε / 2) T := lt_min (by linarith) hβT'
    have hxT : min (β + ε / 2) T ≤ T := min_le_right _ _
    have hxJ : min (β + ε / 2) T ∈ J := by
      refine hmax _ (hIcc ⟨ht₀β.trans hβx.le, hxT⟩) ?_
      rw [uIcc_of_le (ht₀β.trans hβx.le)]
      intro y hy
      rcases le_or_gt y β with hyβ | hyβ
      · exact hJU y (hJoc.out ht₀ hβJ ⟨hy.1, hyβ⟩)
      · refine hU y ⟨hy.1, hy.2.trans hxT⟩ ?_
        rw [Real.dist_eq, abs_of_pos (by linarith)]
        linarith [hy.2, min_le_left (β + ε / 2) T]
    exact absurd (le_csSup hbdd hxJ) (not_le.2 hβx)
  have hβt₀ : t₀ < β := lt_of_le_of_ne ht₀β fun h => hβJ (h ▸ ht₀)
  have hβU : c β ∉ U := fun hβU => by
    obtain ⟨ε, hε, hU⟩ := hnbhd hβU
    obtain ⟨j, hj, hjβ⟩ := exists_lt_of_lt_csSup hJne (show β - ε < β by linarith)
    have hmJ : max j t₀ ∈ J := by
      rcases le_total j t₀ with h | h
      · rw [max_eq_right h]; exact ht₀
      · rw [max_eq_left h]; exact hj
    refine hβJ (hmax β hβI ?_)
    rw [uIcc_of_le ht₀β]
    intro y hy
    rcases le_or_gt y (max j t₀) with hyj | hyj
    · exact hJU y (hJoc.out ht₀ hmJ ⟨hy.1, hyj⟩)
    · refine hU y ⟨hy.1, hy.2.trans hβT⟩ ?_
      rw [Real.dist_eq, abs_of_nonpos (by linarith [hy.2])]
      linarith [le_max_left j t₀]
  -- the extension passes through `c β`
  have hmaxJ : ∀ t < β, max t t₀ ∈ J := fun t ht =>
    hbelow _ (le_max_right _ _) (max_lt ht hβt₀)
  set f : ℝ → ℝ := fun t => φ (max t t₀) with hf
  have hfmono : MonotoneOn f (Iio β) := fun a ha b hb hab =>
    hφ.monotoneOn (hmaxJ a ha) (hmaxJ b hb) (max_le_max hab le_rfl)
  have hfmem : ∀ t < β, f t ∈ Icc (φ t₀) t' := fun t ht =>
    ⟨hφ.monotoneOn ht₀ (hmaxJ t ht) (le_max_right _ _), (hlt _ (hmaxJ t ht)).le⟩
  have hfbdd : BddAbove (f '' Iio β) := ⟨t', by
    rintro _ ⟨t, ht, rfl⟩; exact (hfmem t ht).2⟩
  have hlim : Tendsto f (𝓝[<] β) (𝓝 (sSup (f '' Iio β))) := hfmono.tendsto_nhdsLT hfbdd
  have hf₀ : f t₀ = φ t₀ := by simp only [hf, max_self]
  have hsmem : sSup (f '' Iio β) ∈ Icc (φ t₀) t' :=
    ⟨hf₀ ▸ le_csSup hfbdd ⟨t₀, hβt₀, rfl⟩,
      csSup_le ⟨f t₀, t₀, hβt₀, rfl⟩ fun _ ⟨t, ht, h⟩ => h ▸ (hfmem t ht).2⟩
  have hsI' : sSup (f '' Iio β) ∈ I' := hcurve.ordConnected.out (hmaps ht₀) ht' hsmem
  have hcont' : ContinuousOn c' (Icc (φ t₀) t') := hcurve.continuousOn_Icc (hmaps ht₀) ht'
  have h1 : Tendsto (c' ∘ f) (𝓝[<] β) (𝓝 (c' (sSup (f '' Iio β)))) :=
    (hcont' _ hsmem).tendsto.comp (tendsto_nhdsWithin_iff.2
      ⟨hlim, eventually_nhdsWithin_of_forall fun t ht => hfmem t ht⟩)
  have h2 : Tendsto (fun t => c (max t t₀)) (𝓝[<] β) (𝓝 (c β)) := by
    have hg : Tendsto (fun t => max t t₀) (𝓝[<] β) (𝓝[Icc t₀ T] β) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun t ht =>
        ⟨le_max_right _ _, max_le ((show t < β from ht).le.trans hβT) ht₀T⟩⟩
      have h : Tendsto (fun t => max t t₀) (𝓝 β) (𝓝 (max β t₀)) :=
        (continuous_id.max continuous_const).tendsto β
      rw [max_eq_left ht₀β] at h
      exact h.mono_left nhdsWithin_le_nhds
    exact (hcont β ⟨ht₀β, hβT⟩).tendsto.comp hg
  have heq' : (c' ∘ f) =ᶠ[𝓝[<] β] (fun t => c (max t t₀)) :=
    eventually_nhdsWithin_of_forall fun t ht => heq _ (hmaxJ t ht)
  have hlimeq := tendsto_nhds_unique (h1.congr' heq') h2
  exact hβU (hlimeq ▸ hcurve.mem hsI')

/-- **The component, in an open `U ≤ W`, of an inextensible causal curve of `W` is an
inextensible causal curve of `U`** (`M` Hausdorff, `W` causal). For `W = ⊤` this is
`inextensible_ordConnectedComponent` of `Causal.CauchyExtension`. -/
theorem inextensible_ordConnectedComponent_on [T2Space M]
    (hcaus : ∀ ⦃x y : M⦄, C.le W x y → C.le W y x → x = y) (hUW : U ≤ W)
    (hc : C.Inextensible W I c) {t₀ : ℝ} (ht₀ : t₀ ∈ I)
    (hU : c t₀ ∈ U) : C.Inextensible U (ordConnectedComponent (I ∩ c ⁻¹' U) t₀) c := by
  set J := ordConnectedComponent (I ∩ c ⁻¹' U) t₀
  have ht₀J : t₀ ∈ J := self_mem_ordConnectedComponent.2 ⟨ht₀, hU⟩
  have hJI : J ⊆ I := fun t ht => (ordConnectedComponent_subset ht).1
  have hJU : ∀ t ∈ J, c t ∈ U := fun t ht => (ordConnectedComponent_subset ht).2
  have hJoc : J.OrdConnected := inferInstance
  have hmax : ∀ t ∈ I, [[t₀, t]] ⊆ c ⁻¹' U → t ∈ J := fun t ht h =>
    mem_ordConnectedComponent.2 fun x hx => ⟨hc.1.ordConnected.uIcc_subset ht₀ ht hx, h hx⟩
  have hcurve : C.CausalCurveIn U J c := ⟨⟨t₀, ht₀J⟩, hJoc, fun a ha b hb =>
    CurveOn.restrict (hc.1.curve a (hJI ha) b (hJI hb)) le_rfl le_rfl hUW
      (fun t ht => hJU t (hJoc.out ha hb ht))⟩
  obtain ⟨hpast, hfut⟩ := inextensible_iff.1 hc
  refine inextensible_iff.2 ⟨⟨hcurve, ?_⟩,
    ⟨hcurve, not_futureExtensible_of_component_on hcaus hUW hfut hJI ht₀J hJoc hJU hmax⟩⟩
  have hd : C.dual.FutureInextensible U (-J) (fun t => c (-t)) := by
    refine ⟨hcurve.reverse, not_futureExtensible_of_component_on (C := C.dual) (t₀ := -t₀)
      (fun _ _ hxy hyx => hcaus hyx hxy) hUW (dual_futureInextensible_iff.2 hpast)
      (fun t ht => hJI ht)
      (show - -t₀ ∈ J by rw [neg_neg]; exact ht₀J)
      ⟨fun x hx y hy z hz => show -z ∈ J from hJoc.out hy hx ⟨neg_le_neg hz.2, neg_le_neg hz.1⟩⟩
      (fun t ht => hJU _ ht) fun t ht h => ?_⟩
    refine hmax (-t) ht fun x hx => ?_
    have hx' : -x ∈ [[-t₀, t]] := by
      rcases mem_uIcc.1 hx with h' | h'
      · exact mem_uIcc.2 (Or.inr ⟨by linarith [h'.2], by linarith [h'.1]⟩)
      · exact mem_uIcc.2 (Or.inl ⟨by linarith [h'.2], by linarith [h'.1]⟩)
    have := h hx'
    simpa using this
  exact (dual_futureInextensible_iff.1 hd).2

theorem causalCurveOn_of_agree (h : ∀ V : Opens M, V ≤ W → ∀ x y, C.le V x y ↔ C'.le V x y)
    {a b : ℝ} (hc : C.CausalCurveOn W c a b) : C'.CausalCurveOn W c a b where
  mem := hc.mem
  rel t ht N hN htN := by
    obtain ⟨l, u, hl, hu, hrel⟩ := hc.rel t ht N hN htN
    exact ⟨l, u, hl, hu, fun s hs s' hs' h1 h2 h3 => (h N hN _ _).1 (hrel s hs s' hs' h1 h2 h3)⟩

theorem causalCurveIn_of_agree (h : ∀ V : Opens M, V ≤ W → ∀ x y, C.le V x y ↔ C'.le V x y)
    (hc : C.CausalCurveIn W I c) : C'.CausalCurveIn W I c :=
  ⟨hc.nonempty, hc.ordConnected, fun a ha b hb => causalCurveOn_of_agree h (hc.curve a ha b hb)⟩

theorem inextensible_of_agree (h : ∀ V : Opens M, V ≤ W → ∀ x y, C.le V x y ↔ C'.le V x y)
    (hc : C.Inextensible W I c) : C'.Inextensible W I c := by
  have h' : ∀ V : Opens M, V ≤ W → ∀ x y, C'.le V x y ↔ C.le V x y :=
    fun V hV x y => (h V hV x y).symm
  refine ⟨causalCurveIn_of_agree h hc.1, fun ⟨I', c', hext⟩ => hc.2 ⟨I', c', ?_⟩⟩
  exact ⟨causalCurveIn_of_agree h' hext.curve, hext.reparam, hext.grows⟩

/-- Two causalities with the same causal relations on the open subsets of `W` have the same
Cauchy surfaces of `W`. -/
theorem isCauchySurfaceOn_of_agree (h : ∀ V : Opens M, V ≤ W → ∀ x y, C.le V x y ↔ C'.le V x y)
    (hS : C.IsCauchySurfaceOn W S) : C'.IsCauchySurfaceOn W S :=
  fun I c hc => hS I c (inextensible_of_agree (fun V hV x y => (h V hV x y).symm) hc)

/-! ### ERS19 Lemma 4.70 (superluminal): connected overlaps -/

/-- **ERS19 Lemma 4.70, the core**: through every point `x` of `U₁ ∩ U₂` runs a curve `γ` whose
components through `x` in `U₁` and in `U₂` are inextensible there (for `C₁`, `C₂`), and which meets
`S` "at most once" — between two parameters on `S` it stays on `S`. Then `U₁ ∩ U₂` is
preconnected. No causality of the curve family is assumed.

Suppliers: `hC₁`, `hC₂` — the two GHDs (`S` a Cauchy hypersurface of `Uᵢ` for `g(uᵢ, duᵢ)`);
`htrans` — the maximal integral curve of `T` through `x` (Picard–Lindelöf), whose components in
`Uᵢ` are inextensible there by (4.62) (they are `g(uᵢ)`-timelike, and a maximal integral curve has
no endpoint in `Uᵢ`), and ERS's "every maximal integral curve of `T` intersects `S` at most once"
(the curve being injective by (4.62), see `ers_lemma_4_70`). -/
theorem ers_lemma_4_70_core {C₁ C₂ : Causality M} {U₁ U₂ : Opens M}
    (hS : IsPreconnected S) (hS₁ : S ⊆ U₁) (hS₂ : S ⊆ U₂)
    (hC₁ : C₁.IsCauchySurfaceOn U₁ S) (hC₂ : C₂.IsCauchySurfaceOn U₂ S)
    (htrans : ∀ x ∈ U₁ ⊓ U₂, ∃ (I : Set ℝ) (γ : ℝ → M) (t₀ : ℝ), t₀ ∈ I ∧ γ t₀ = x ∧
      C₁.Inextensible U₁ (ordConnectedComponent (I ∩ γ ⁻¹' U₁) t₀) γ ∧
      C₂.Inextensible U₂ (ordConnectedComponent (I ∩ γ ⁻¹' U₂) t₀) γ ∧
      ∀ s ∈ I, ∀ t ∈ I, γ s ∈ S → γ t ∈ S → γ '' [[s, t]] ⊆ S) :
    IsPreconnected ((U₁ ⊓ U₂ : Opens M) : Set M) := by
  refine isPreconnected_of_segments hS (fun s hs => ⟨hS₁ hs, hS₂ hs⟩) fun x hx => ?_
  obtain ⟨I, γ, t₀, ht₀, rfl, hJ₁, hJ₂, honce⟩ := htrans x hx
  have hx₁ : γ t₀ ∈ U₁ := hx.1
  have hx₂ : γ t₀ ∈ U₂ := hx.2
  obtain ⟨_, ⟨⟨s₁, hs₁, rfl⟩, hs₁S⟩, -⟩ := hC₁ _ γ hJ₁
  obtain ⟨_, ⟨⟨s₂, hs₂, rfl⟩, hs₂S⟩, -⟩ := hC₂ _ γ hJ₂
  have hs₁I : s₁ ∈ I := (ordConnectedComponent_subset hs₁).1
  have hs₂I : s₂ ∈ I := (ordConnectedComponent_subset hs₂).1
  have ht₀J₁ : t₀ ∈ ordConnectedComponent (I ∩ γ ⁻¹' U₁) t₀ :=
    self_mem_ordConnectedComponent.2 ⟨ht₀, hx₁⟩
  have ht₀J₂ : t₀ ∈ ordConnectedComponent (I ∩ γ ⁻¹' U₂) t₀ :=
    self_mem_ordConnectedComponent.2 ⟨ht₀, hx₂⟩
  have hJ₁oc : (ordConnectedComponent (I ∩ γ ⁻¹' U₁) t₀).OrdConnected := inferInstance
  have hJ₂oc : (ordConnectedComponent (I ∩ γ ⁻¹' U₂) t₀).OrdConnected := inferInstance
  refine ⟨γ, t₀, s₁, hJ₁.1.continuousOn_uIcc ht₀J₁ hs₁, rfl, hs₁S, ?_⟩
  rintro _ ⟨u, hu, rfl⟩
  refine ⟨(ordConnectedComponent_subset (hJ₁oc.uIcc_subset ht₀J₁ hs₁ hu)).2, ?_⟩
  rcases uIcc_subset_uIcc_union_uIcc (b := s₂) hu with hu' | hu'
  · exact (ordConnectedComponent_subset (hJ₂oc.uIcc_subset ht₀J₂ hs₂ hu')).2
  · exact hS₂ (honce s₂ hs₂I s₁ hs₁I hs₂S hs₁S ⟨u, hu', rfl⟩)

/-- **ERS19 Lemma 4.70, causal-topological skeleton, with the nesting.** `Cτ` is the causality of
the vector field `T` (its inextensible causal curves of `M` are the maximal integral curves of
`T`), nested in the causalities `C₁`, `C₂` of the two developments on `U₁`, `U₂`
(`InextensibleNestedOn`: ERS's (4.62), "`T` is timelike with respect to `g(u, du)`").

Suppliers (layer 3): `hn₁`, `hn₂` — (4.62): an integral curve of `T` in `Uᵢ` is
`g(uᵢ, duᵢ)`-timelike, and a curve of `Uᵢ` without endpoint in `Uᵢ` is `g(uᵢ)`-inextendible there
(inextendibility of a continuous causal curve is the absence of an endpoint); `hthrough` — maximal
integral curves of `T` (Picard–Lindelöf); `hτ` — `T` has no closed orbit, a consequence of (4.62):
`g` does not depend on `x` (4.61), so `T` is timelike for the constant metric `h = g(0, 0)`, lies
in one time cone `K` of `h`, and for `e ∈ K` the linear form `-h(e, ·)` increases strictly along
its integral curves; `honce` — ERS's hypothesis on `S`; `hC₁`, `hC₂` — the two GHDs. -/
theorem ers_lemma_4_70 [T2Space M] {Cτ C₁ C₂ : Causality M} {U₁ U₂ : Opens M}
    (hS : IsPreconnected S) (hS₁ : S ⊆ U₁) (hS₂ : S ⊆ U₂)
    (hC₁ : C₁.IsCauchySurfaceOn U₁ S) (hC₂ : C₂.IsCauchySurfaceOn U₂ S) (hτ : Cτ.IsCausal)
    (hthrough : ∀ x ∈ U₁ ⊓ U₂, ∃ (I : Set ℝ) (γ : ℝ → M), Cτ.Inextensible ⊤ I γ ∧ x ∈ γ '' I)
    (honce : ∀ (I : Set ℝ) (γ : ℝ → M), Cτ.Inextensible ⊤ I γ →
      ∀ y ∈ γ '' I ∩ S, ∀ z ∈ γ '' I ∩ S, y = z)
    (hn₁ : InextensibleNestedOn Cτ C₁ U₁) (hn₂ : InextensibleNestedOn Cτ C₂ U₂) :
    IsPreconnected ((U₁ ⊓ U₂ : Opens M) : Set M) := by
  refine ers_lemma_4_70_core hS hS₁ hS₂ hC₁ hC₂ fun x hx => ?_
  obtain ⟨I, γ, hγ, t₀, ht₀, rfl⟩ := hthrough x hx
  refine ⟨I, γ, t₀, ht₀, rfl, hn₁ (inextensible_ordConnectedComponent hτ hγ ht₀ hx.1),
    hn₂ (inextensible_ordConnectedComponent hτ hγ ht₀ hx.2), fun s hs t ht hsS htS => ?_⟩
  have hst : γ s = γ t := honce I γ hγ _ ⟨⟨s, hs, rfl⟩, hsS⟩ _ ⟨⟨t, ht, rfl⟩, htS⟩
  rintro _ ⟨u, hu, rfl⟩
  rw [eq_of_mem_uIcc_of_eq hτ hγ.1 hs ht hst hu]
  exact hsS

/-- ERS19 Lemma 4.70 as printed ("connected"): `S` non-empty. -/
theorem ers_lemma_4_70_isConnected [T2Space M] {Cτ C₁ C₂ : Causality M} {U₁ U₂ : Opens M}
    (hS : IsConnected S) (hS₁ : S ⊆ U₁) (hS₂ : S ⊆ U₂)
    (hC₁ : C₁.IsCauchySurfaceOn U₁ S) (hC₂ : C₂.IsCauchySurfaceOn U₂ S) (hτ : Cτ.IsCausal)
    (hthrough : ∀ x ∈ U₁ ⊓ U₂, ∃ (I : Set ℝ) (γ : ℝ → M), Cτ.Inextensible ⊤ I γ ∧ x ∈ γ '' I)
    (honce : ∀ (I : Set ℝ) (γ : ℝ → M), Cτ.Inextensible ⊤ I γ →
      ∀ y ∈ γ '' I ∩ S, ∀ z ∈ γ '' I ∩ S, y = z)
    (hn₁ : InextensibleNestedOn Cτ C₁ U₁) (hn₂ : InextensibleNestedOn Cτ C₂ U₂) :
    IsConnected ((U₁ ⊓ U₂ : Opens M) : Set M) := by
  obtain ⟨s, hs⟩ := hS.nonempty
  exact ⟨⟨s, hS₁ hs, hS₂ hs⟩, ers_lemma_4_70 hS.isPreconnected hS₁ hS₂ hC₁ hC₂ hτ hthrough honce
    hn₁ hn₂⟩

/-! ### ERS19 Lemma 4.72 (subluminal): connected overlaps -/

/-- **A curve segment of `M` with an end in `U` and an end on an acausal Cauchy surface `S` of `U`
lies in `U`**, when causal curves of `M` extend to inextensible ones (`CurvesExtend`), `M` is
Hausdorff and causal. -/
theorem image_Icc_subset_of_curvesExtend [T2Space M] (hcaus : C.IsCausal) (hext : C.CurvesExtend)
    (hSU : S ⊆ U) (hU : C.IsCauchySurfaceOn U S) (hS : C.IsAcausal S) {γ : ℝ → M} {a b : ℝ}
    (hab : a ≤ b) (hγ : C.CausalCurveOn ⊤ γ a b)
    (hend : (γ a ∈ U ∧ γ b ∈ S) ∨ (γ a ∈ S ∧ γ b ∈ U)) :
    γ '' Icc a b ⊆ U := by
  obtain ⟨I', c', hc', hsub⟩ := hext γ a b hab hγ
  obtain ⟨ta, hta, hca⟩ := hsub ⟨a, left_mem_Icc.2 hab, rfl⟩
  obtain ⟨tb, htb, hcb⟩ := hsub ⟨b, right_mem_Icc.2 hab, rfl⟩
  have hstay : c' '' [[ta, tb]] ⊆ U := by
    rcases hend with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact image_uIcc_subset_of_isCauchySurfaceOn hcaus hSU hU hS hc' hta htb
        (by rw [hca]; exact ha) (by rw [hcb]; exact hb)
    · rw [uIcc_comm]
      exact image_uIcc_subset_of_isCauchySurfaceOn hcaus hSU hU hS hc' htb hta
        (by rw [hcb]; exact hb) (by rw [hca]; exact ha)
  rintro _ ⟨u, hu, rfl⟩
  obtain ⟨ρ, hρ, hρeq⟩ := hsub ⟨u, hu, rfl⟩
  rw [← hρeq]
  refine hstay (mem_image_uIcc_of_between hcaus hc'.1 hta htb hρ (Or.inl ?_))
  rw [hρeq, hca, hcb]
  exact ⟨hγ.le_of_le le_rfl hu.1 hu.2, hγ.le_of_le hu.1 hu.2 le_rfl⟩

/-- **ERS19 Lemma 4.72, causal-topological skeleton.** `Cm` is the wider causality (Minkowski),
`C₂` the narrower one of the second development.

Suppliers (layer 3): `hnest` — subluminality, the causal cone of `g(u₂, du₂)` inside that of `m`;
`hm` — Minkowski space is causal; `hmext` — in Minkowski space every causal curve lies on an
inextendible one (in the library, `Causal.CurvesExtend` through a time function: a model module);
`hthrough` — through every point of `U₂` an inextendible `g(u₂)`-causal curve of `U₂` (the integral
curve of a `g(u₂)`-timelike vector field); `hacausal` — ERS's "`S` achronal w.r.t. `m`", here
strengthened to acausal; `hmU₁` — `u₁` is an m-GHD; `hC₂` — `u₂` is a GHD. -/
theorem ers_lemma_4_72 [T2Space M] {Cm C₂ : Causality M} {U₁ U₂ : Opens M}
    (hS : IsPreconnected S) (hS₁ : S ⊆ U₁) (hS₂ : S ⊆ U₂)
    (hm : Cm.IsCausal) (hmext : Cm.CurvesExtend) (hacausal : Cm.IsAcausal S)
    (hmU₁ : Cm.IsCauchySurfaceOn U₁ S) (hC₂ : C₂.IsCauchySurfaceOn U₂ S)
    (hthrough : ∀ x ∈ U₁ ⊓ U₂, ∃ (I : Set ℝ) (γ : ℝ → M), C₂.Inextensible U₂ I γ ∧ x ∈ γ '' I)
    (hnest : CurveNestedOn C₂ Cm U₂) :
    IsPreconnected ((U₁ ⊓ U₂ : Opens M) : Set M) := by
  refine isPreconnected_of_segments hS (fun s hs => ⟨hS₁ hs, hS₂ hs⟩) fun x hx => ?_
  obtain ⟨I, γ, hγ, t₀, ht₀, rfl⟩ := hthrough x hx
  obtain ⟨_, ⟨⟨s₂, hs₂, rfl⟩, hs₂S⟩, -⟩ := hC₂ I γ hγ
  refine ⟨γ, t₀, s₂, hγ.1.continuousOn_uIcc ht₀ hs₂, rfl, hs₂S, ?_⟩
  have hseg : ∀ a ∈ I, ∀ b ∈ I, Cm.CausalCurveOn ⊤ γ a b := fun a ha b hb =>
    CurveOn.mono_opens Cm.isRelFamily_le (hnest (hγ.1.curve a ha b hb)) le_top
  have h₁ : γ '' [[t₀, s₂]] ⊆ U₁ := by
    rcases le_total t₀ s₂ with h | h
    · rw [uIcc_of_le h]
      exact image_Icc_subset_of_curvesExtend hm hmext hS₁ hmU₁ hacausal h (hseg t₀ ht₀ s₂ hs₂)
        (Or.inl ⟨hx.1, hs₂S⟩)
    · rw [uIcc_of_ge h]
      exact image_Icc_subset_of_curvesExtend hm hmext hS₁ hmU₁ hacausal h (hseg s₂ hs₂ t₀ ht₀)
        (Or.inr ⟨hs₂S, hx.1⟩)
  rintro _ ⟨u, hu, rfl⟩
  exact ⟨h₁ ⟨u, hu, rfl⟩, hγ.1.mem (hγ.1.ordConnected.uIcc_subset ht₀ hs₂ hu)⟩

/-- ERS19 Lemma 4.72 as printed ("connected"): `S` non-empty. -/
theorem ers_lemma_4_72_isConnected [T2Space M] {Cm C₂ : Causality M} {U₁ U₂ : Opens M}
    (hS : IsConnected S) (hS₁ : S ⊆ U₁) (hS₂ : S ⊆ U₂)
    (hm : Cm.IsCausal) (hmext : Cm.CurvesExtend) (hacausal : Cm.IsAcausal S)
    (hmU₁ : Cm.IsCauchySurfaceOn U₁ S) (hC₂ : C₂.IsCauchySurfaceOn U₂ S)
    (hthrough : ∀ x ∈ U₁ ⊓ U₂, ∃ (I : Set ℝ) (γ : ℝ → M), C₂.Inextensible U₂ I γ ∧ x ∈ γ '' I)
    (hnest : CurveNestedOn C₂ Cm U₂) :
    IsConnected ((U₁ ⊓ U₂ : Opens M) : Set M) := by
  obtain ⟨s, hs⟩ := hS.nonempty
  exact ⟨⟨s, hS₁ hs, hS₂ hs⟩, ers_lemma_4_72 hS.isPreconnected hS₁ hS₂ hm hmext hacausal hmU₁
    hC₂ hthrough hnest⟩

/-! ### ERS19 Theorem 4.77: the union of the developments -/

/-- **ERS19 Theorem 4.77, causal-topological skeleton**: the union of open sets in each of which,
and in each pairwise intersection of which, `S` is a Cauchy surface, has `S` for Cauchy surface,
when the union is causal and `M` Hausdorff.

Suppliers: `C` — the causality of `g(umax, dumax)`, well defined by Corollary 4.71 (Lemma 4.70
here + Theorem 4.64, PDE uniqueness on connected overlaps); its agreement with each `g(uα)` on
`Uα` transports Cauchy surfaces (`isCauchySurfaceOn_of_agree`); `hU` — each `uα` is a GHD;
`hpair` — Remark 4.67 (the intersection of two GHDs is their maximal common GHD, with Cauchy
hypersurface `S`), from Theorem 4.64 and Lemma 4.70; `hcaus` — the union causal: supplied by no
lemma of ERS (they obtain global hyperbolicity of `Umax` a posteriori), an added hypothesis, used
by the component lemma `inextensible_ordConnectedComponent_on` and by the constancy step
`eq_of_mem_uIcc_of_eq`. -/
theorem ers_theorem_4_77 [T2Space M] {ι : Type*} (U : ι → Opens M) (hSU : ∀ i, S ⊆ U i)
    (hcaus : ∀ ⦃x y : M⦄, C.le (⨆ i, U i) x y → C.le (⨆ i, U i) y x → x = y)
    (hU : ∀ i, C.IsCauchySurfaceOn (U i) S) (hpair : ∀ i j, C.IsCauchySurfaceOn (U i ⊓ U j) S) :
    C.IsCauchySurfaceOn (⨆ i, U i) S := by
  have hUW : ∀ i, U i ≤ ⨆ i, U i := fun i => le_iSup U i
  -- the step of the continuity argument (ERS: "`J` is closed", by Remark 4.67)
  have step : ∀ {I : Set ℝ} {c : ℝ → M}, C.Inextensible (⨆ i, U i) I c → ∀ i j,
      ∀ s₁ ∈ I, ∀ r ∈ I, s₁ ≤ r → c s₁ ∈ S → Icc s₁ r ⊆ c ⁻¹' U i → c r ∈ U j →
        Icc s₁ r ⊆ c ⁻¹' U j := by
    intro I c hc i j s₁ hs₁ r hr hs₁r hs₁S hseg hrj
    have hIcc : Icc s₁ r ⊆ I := hc.1.ordConnected.out hs₁ hr
    have hcausi : ∀ ⦃x y : M⦄, C.le (U i) x y → C.le (U i) y x → x = y := fun _ _ h1 h2 =>
      hcaus (C.le_mono (hUW i) h1) (C.le_mono (hUW i) h2)
    have hs₁Ui : c s₁ ∈ U i := hseg ⟨le_rfl, hs₁r⟩
    have hs₁J : s₁ ∈ ordConnectedComponent (I ∩ c ⁻¹' U i) s₁ :=
      self_mem_ordConnectedComponent.2 ⟨hs₁, hs₁Ui⟩
    have hJi := inextensible_ordConnectedComponent_on hcaus (hUW i) hc hs₁ hs₁Ui
    have hrij : c r ∈ U i ⊓ U j := ⟨hseg ⟨hs₁r, le_rfl⟩, hrj⟩
    have hJij := inextensible_ordConnectedComponent_on hcaus (inf_le_left.trans (hUW i)) hc hr hrij
    obtain ⟨_, ⟨⟨σ, hσ, rfl⟩, hσS⟩, -⟩ := hpair i j _ c hJij
    have hσ' := mem_ordConnectedComponent.1 hσ
    have hσJi : σ ∈ ordConnectedComponent (I ∩ c ⁻¹' U i) s₁ := by
      refine mem_ordConnectedComponent.2 fun x hx => ?_
      rcases uIcc_subset_uIcc_union_uIcc (b := r) hx with hx | hx
      · rw [uIcc_of_le hs₁r] at hx; exact ⟨hIcc hx, hseg hx⟩
      · exact ⟨(hσ' hx).1, (hσ' hx).2.1⟩
    have hcσ : c σ = c s₁ := by
      obtain ⟨_, -, huniq⟩ := hU i _ c hJi
      exact (huniq _ ⟨⟨σ, hσJi, rfl⟩, hσS⟩).trans (huniq _ ⟨⟨s₁, hs₁J, rfl⟩, hs₁S⟩).symm
    intro u hu
    have huu : u ∈ [[s₁, r]] := by rw [uIcc_of_le hs₁r]; exact hu
    rcases uIcc_subset_uIcc_union_uIcc (b := σ) huu with h' | h'
    · show c u ∈ U j
      rw [eq_of_mem_uIcc_of_eq hcausi hJi.1 hs₁J hσJi hcσ.symm h']
      exact hSU j hs₁S
    · exact (hσ' (by rw [uIcc_comm]; exact h')).2.2
  intro I c hc
  obtain ⟨t₀, ht₀⟩ := hc.1.nonempty
  obtain ⟨i₀, hi₀⟩ := Opens.mem_iSup.1 (hc.1.mem ht₀)
  have hJ := inextensible_ordConnectedComponent_on hcaus (hUW i₀) hc ht₀ hi₀
  obtain ⟨_, ⟨⟨σ, hσ, rfl⟩, hσS⟩, -⟩ := hU i₀ _ c hJ
  have hσI : σ ∈ I := (ordConnectedComponent_subset hσ).1
  have key : ∀ s₁ ∈ I, ∀ s₂ ∈ I, s₁ ≤ s₂ → c s₁ ∈ S → c s₂ ∈ S → c s₂ = c s₁ := by
    intro s₁ hs₁ s₂ hs₂ h12 hs₁S hs₂S
    have hIcc : Icc s₁ s₂ ⊆ I := hc.1.ordConnected.out hs₁ hs₂
    have hcont : ContinuousOn c (Icc s₁ s₂) := hc.1.continuousOn_Icc hs₁ hs₂
    choose V hVo hVeq using fun i => (continuousOn_iff'.1 hcont) (U i) (U i).isOpen
    have hcover : Icc s₁ s₂ ⊆ ⋃ i, V i := fun t ht => by
      obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hc.1.mem (hIcc ht))
      have : t ∈ c ⁻¹' U i ∩ Icc s₁ s₂ := ⟨hi, ht⟩
      rw [hVeq i] at this
      exact mem_iUnion.2 ⟨i, this.1⟩
    obtain ⟨t, ht0, hmono, ⟨m, hm⟩, htmem, hsub⟩ := exists_subdivision_Icc h12 hVo hcover
    have hseg : ∀ n, ∃ i, Icc (t n) (t (n + 1)) ⊆ c ⁻¹' U i := fun n => by
      obtain ⟨i, hi⟩ := hsub n
      refine ⟨i, fun x hx => ?_⟩
      have hxI : x ∈ Icc s₁ s₂ := ⟨(htmem n).1.trans hx.1, hx.2.trans (htmem (n + 1)).2⟩
      have : x ∈ V i ∩ Icc s₁ s₂ := ⟨hi hx, hxI⟩
      rw [← hVeq i] at this
      exact this.1
    have hind : ∀ n, ∃ i, Icc s₁ (t n) ⊆ c ⁻¹' U i := by
      intro n
      induction n with
      | zero =>
        obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hc.1.mem hs₁)
        refine ⟨i, ?_⟩
        rw [ht0, Icc_self]
        intro x hx
        rw [mem_singleton_iff.1 hx]
        exact hi
      | succ n ih =>
        obtain ⟨i, hi⟩ := ih
        obtain ⟨j, hj⟩ := hseg n
        have htn : t n ≤ t (n + 1) := hmono (Nat.le_succ n)
        have hst := step hc i j s₁ hs₁ (t n) (hIcc (htmem n)) (htmem n).1 hs₁S hi
          (hj ⟨le_rfl, htn⟩)
        refine ⟨j, fun x hx => ?_⟩
        rcases le_total x (t n) with hxn | hxn
        · exact hst ⟨hx.1, hxn⟩
        · exact hj ⟨hxn, hx.2⟩
    obtain ⟨i, hi⟩ := hind m
    rw [hm m le_rfl] at hi
    have hs₁Ui : c s₁ ∈ U i := hi ⟨le_rfl, h12⟩
    have hJi := inextensible_ordConnectedComponent_on hcaus (hUW i) hc hs₁ hs₁Ui
    have hs₂J : s₂ ∈ ordConnectedComponent (I ∩ c ⁻¹' U i) s₁ :=
      mem_ordConnectedComponent.2 (by rw [uIcc_of_le h12]; exact fun x hx => ⟨hIcc hx, hi hx⟩)
    obtain ⟨_, -, huniq⟩ := hU i _ c hJi
    exact (huniq _ ⟨⟨s₂, hs₂J, rfl⟩, hs₂S⟩).trans
      (huniq _ ⟨⟨s₁, self_mem_ordConnectedComponent.2 ⟨hs₁, hs₁Ui⟩, rfl⟩, hs₁S⟩).symm
  refine ⟨c σ, ⟨⟨σ, hσI, rfl⟩, hσS⟩, ?_⟩
  rintro _ ⟨⟨s, hs, rfl⟩, hsS⟩
  rcases le_total σ s with h | h
  · exact key σ hσI s hs h hσS hsS
  · exact (key s hs σ hσI h hsS hσS).symm

/-- **ERS19 Theorem 4.77, the maximal development**: among the open sets of which `S` is a Cauchy
surface, the union is the greatest.

Suppliers: `hex` — local existence (Theorem 4.75); `hpair` — Remark 4.67 (Theorem 4.64 and
Lemma 4.70); `hcaus` — added, as in `ers_theorem_4_77`. -/
theorem ers_theorem_4_77_greatest [T2Space M]
    (hex : ∃ U : Opens M, S ⊆ U ∧ C.IsCauchySurfaceOn U S)
    (hcaus : ∀ ⦃x y : M⦄, C.le (sSup {U : Opens M | S ⊆ U ∧ C.IsCauchySurfaceOn U S}) x y →
      C.le (sSup {U : Opens M | S ⊆ U ∧ C.IsCauchySurfaceOn U S}) y x → x = y)
    (hpair : ∀ U V : Opens M, S ⊆ U → C.IsCauchySurfaceOn U S → S ⊆ V →
      C.IsCauchySurfaceOn V S → C.IsCauchySurfaceOn (U ⊓ V) S) :
    IsGreatest {U : Opens M | S ⊆ U ∧ C.IsCauchySurfaceOn U S}
      (sSup {U : Opens M | S ⊆ U ∧ C.IsCauchySurfaceOn U S}) := by
  obtain ⟨U₀, hSU₀, hU₀⟩ := hex
  have hsSup : sSup {U : Opens M | S ⊆ U ∧ C.IsCauchySurfaceOn U S} =
      ⨆ U : {U : Opens M | S ⊆ U ∧ C.IsCauchySurfaceOn U S}, (U : Opens M) := sSup_eq_iSup' _
  refine ⟨⟨fun x hx => le_sSup (show U₀ ∈ {U : Opens M | S ⊆ U ∧ C.IsCauchySurfaceOn U S} from
    ⟨hSU₀, hU₀⟩) (hSU₀ hx), ?_⟩, fun U hU => le_sSup hU⟩
  rw [hsSup]
  refine ers_theorem_4_77 (fun U : {U : Opens M | S ⊆ U ∧ C.IsCauchySurfaceOn U S} =>
    (U : Opens M)) (fun U => U.2.1) ?_ (fun U => U.2.2)
    (fun U V => hpair _ _ U.2.1 U.2.2 V.2.1 V.2.2)
  rw [← hsSup]
  exact hcaus

/-! ### ERS19 Theorem 4.82: one-sided boundaries -/

/-- **(4.84)**: the component `A` of `U₁ ∩ U₂` through `s₀` has boundary points in `U₂`, all on the
boundary of `U₁`, when `U₂ ⊄ U₁` is connected (`M` locally connected). -/
theorem frontier_connectedComponentIn_inter [LocallyConnectedSpace M] {U₁ U₂ : Set M}
    (hU₁ : IsOpen U₁) (hU₂ : IsOpen U₂) {s₀ : M} (hs₀ : s₀ ∈ U₁ ∩ U₂)
    (hU₂c : IsPreconnected U₂) (hnot : ¬ U₂ ⊆ U₁) :
    (frontier (connectedComponentIn (U₁ ∩ U₂) s₀) ∩ U₂).Nonempty ∧
      frontier (connectedComponentIn (U₁ ∩ U₂) s₀) ∩ U₂ ⊆ frontier U₁ := by
  have hAo : IsOpen (connectedComponentIn (U₁ ∩ U₂) s₀) := (hU₁.inter hU₂).connectedComponentIn
  have hAsub : connectedComponentIn (U₁ ∩ U₂) s₀ ⊆ U₁ ∩ U₂ := connectedComponentIn_subset _ _
  have hs₀A : s₀ ∈ connectedComponentIn (U₁ ∩ U₂) s₀ := mem_connectedComponentIn hs₀
  have hfr := hAo.frontier_eq
  constructor
  · by_contra hne
    rw [not_nonempty_iff_eq_empty] at hne
    have hsub : U₂ ⊆ connectedComponentIn (U₁ ∩ U₂) s₀ :=
      hU₂c.subset_of_closure_inter_subset hAo ⟨s₀, hs₀.2, hs₀A⟩ fun p ⟨hpA, hpU₂⟩ => by
        by_contra hpA'
        have : p ∈ frontier (connectedComponentIn (U₁ ∩ U₂) s₀) ∩ U₂ :=
          ⟨by rw [hfr]; exact ⟨hpA, hpA'⟩, hpU₂⟩
        rw [hne] at this
        exact this
    exact hnot fun x hx => (hAsub (hsub hx)).1
  · rintro p ⟨hpf, hpU₂⟩
    rw [hfr] at hpf
    rw [hU₁.frontier_eq]
    refine ⟨closure_mono (fun x hx => (hAsub hx).1) hpf.1, fun hpU₁ => hpf.2 ?_⟩
    have hp : p ∈ U₁ ∩ U₂ := ⟨hpU₁, hpU₂⟩
    have hBo : IsOpen (connectedComponentIn (U₁ ∩ U₂) p) := (hU₁.inter hU₂).connectedComponentIn
    obtain ⟨z, hzB, hzA⟩ := mem_closure_iff.1 hpf.1 _ hBo (mem_connectedComponentIn hp)
    rw [connectedComponentIn_eq hzA, ← connectedComponentIn_eq hzB]
    exact mem_connectedComponentIn hp

/-- **How the one-sidedness (4.83) is used**: near a boundary point `q` of the component `A`,
a neighbourhood `V ⊆ U₂` meeting `U₁` in a preconnected set meets it inside `A`. -/
theorem inter_subset_connectedComponentIn {U₁ U₂ V : Set M} {s₀ q : M}
    (hq : q ∈ closure (connectedComponentIn (U₁ ∩ U₂) s₀)) (hV : V ∈ 𝓝 q) (hVU₂ : V ⊆ U₂)
    (hconn : IsPreconnected (V ∩ U₁)) : V ∩ U₁ ⊆ connectedComponentIn (U₁ ∩ U₂) s₀ := by
  obtain ⟨z, hzV, hzA⟩ := mem_closure_iff_nhds.1 hq V hV
  have hzF : z ∈ U₁ ∩ U₂ := connectedComponentIn_subset _ _ hzA
  rw [connectedComponentIn_eq hzA]
  exact hconn.subset_connectedComponentIn ⟨hzV, hzF.1⟩ fun y hy => ⟨hy.2, hVU₂ hy.1⟩

/-- **A compact set has a causally minimal point** (`W` causal, `M` Hausdorff, the pasts closed in
the set). -/
theorem exists_minimal_of_isCompact_on [T2Space M]
    (hcaus : ∀ ⦃x y : M⦄, C.le W x y → C.le W y x → x = y) {K : Set M} (hK : IsCompact K)
    (hKW : K ⊆ W) (hne : K.Nonempty) (hJ : ∀ x ∈ K, IsClosed (C.Jminus W {x} ∩ K)) :
    ∃ p ∈ K, C.Jminus W {p} ∩ K = {p} := by
  have hKcl : IsClosed K := hK.isClosed
  have hdown : ∀ x ∈ K, ∀ y ∈ C.Jminus W {x} ∩ K, C.Jminus W {y} ∩ K ⊆ C.Jminus W {x} ∩ K := by
    intro x _ y hy z hz
    have h1 : C.le W z y := by simpa using hz.1
    have h2 : C.le W y x := by simpa using hy.1
    exact ⟨by simpa using C.le_trans h1 h2, hz.2⟩
  have hself : ∀ x ∈ K, x ∈ C.Jminus W {x} ∩ K := fun x hx =>
    ⟨by simpa using C.le_refl (hKW hx), hx⟩
  let 𝒮 : Set (Set M) :=
    {A | A ⊆ K ∧ A.Nonempty ∧ IsClosed A ∧ ∀ x ∈ A, C.Jminus W {x} ∩ K ⊆ A}
  have hK𝒮 : K ∈ 𝒮 := ⟨subset_rfl, hne, hKcl, fun _ _ => inter_subset_right⟩
  have hchains : ∀ c ⊆ 𝒮, IsChain (· ⊆ ·) c → c.Nonempty → ∃ lb ∈ 𝒮, ∀ s ∈ c, lb ⊆ s := by
    intro c hc hchain hcne
    have hdir : DirectedOn (· ⊇ ·) c := fun A hA B hB => by
      rcases eq_or_ne A B with rfl | hAB
      · exact ⟨A, hA, subset_rfl, subset_rfl⟩
      rcases hchain hA hB hAB with h | h
      · exact ⟨A, hA, subset_rfl, h⟩
      · exact ⟨B, hB, h, subset_rfl⟩
    haveI : Nonempty c := hcne.to_subtype
    refine ⟨⋂₀ c, ⟨?_, ?_, isClosed_sInter fun A hA => (hc hA).2.2.1, ?_⟩,
      fun A hA => sInter_subset_of_mem hA⟩
    · obtain ⟨A, hA⟩ := hcne
      exact (sInter_subset_of_mem hA).trans (hc hA).1
    · exact IsCompact.nonempty_sInter_of_directed_nonempty_isCompact_isClosed hdir
        (fun A hA => (hc hA).2.1) (fun A hA => hK.of_isClosed_subset (hc hA).2.2.1 (hc hA).1)
        (fun A hA => (hc hA).2.2.1)
    · intro x hx y hy
      exact mem_sInter.2 fun A hA => (hc hA).2.2.2 x (mem_sInter.1 hx A hA) hy
  obtain ⟨m, -, hm⟩ := zorn_superset_nonempty 𝒮 hchains K hK𝒮
  obtain ⟨hmK, ⟨p, hp⟩, -, hmdown⟩ := hm.prop
  have heq : ∀ x ∈ m, m = C.Jminus W {x} ∩ K := fun x hx => by
    have hx𝒮 : C.Jminus W {x} ∩ K ∈ 𝒮 :=
      ⟨inter_subset_right, ⟨x, hself x (hmK hx)⟩, hJ x (hmK hx), hdown x (hmK hx)⟩
    exact Subset.antisymm (hm.2 hx𝒮 (hmdown x hx)) (hmdown x hx)
  refine ⟨p, hmK hp, ?_⟩
  rw [← heq p hp]
  refine eq_singleton_iff_unique_mem.2 ⟨hp, fun z hz => ?_⟩
  have hzp : z ∈ C.Jminus W {p} ∩ K := by rw [← heq p hp]; exact hz
  have hpz : p ∈ C.Jminus W {z} ∩ K := by rw [← heq z hz]; exact hp
  have h1 : C.le W z p := by simpa using hzp.1
  have h2 : C.le W p z := by simpa using hpz.1
  exact hcaus h1 h2

/-- **(4.65)/(4.85) without null geodesics**: on a closed set `B`, below a point `q` of
`B ∩ J⁺(S)`, there is a point `p` with `J⁻(p) ∩ B ∩ J⁺(S) = {p}`, when `J⁻(q) ∩ J⁺(S)` is
compact and the pasts are closed in `W`. -/
theorem exists_spacelike_boundary_point [T2Space M]
    (hcaus : ∀ ⦃x y : M⦄, C.le W x y → C.le W y x → x = y)
    (hJ : ∀ x ∈ W, closure (C.Jminus W {x}) ∩ W ⊆ C.Jminus W {x}) {B : Set M} (hB : IsClosed B)
    {q : M} (hq : q ∈ C.Jplus W S ∩ B) (hK : IsCompact (C.Jminus W {q} ∩ C.Jplus W S)) :
    ∃ p ∈ C.Jminus W {q} ∩ C.Jplus W S ∩ B, C.Jminus W {p} ∩ B ∩ C.Jplus W S = {p} := by
  have hqW : q ∈ W := by
    obtain ⟨s, -, hsq⟩ := hq.1
    exact C.le_mem_right hsq
  have hKW : C.Jminus W {q} ∩ C.Jplus W S ∩ B ⊆ W := fun x hx => by
    obtain ⟨y, -, hxy⟩ := hx.1.1
    exact C.le_mem_left hxy
  have hKc : IsCompact (C.Jminus W {q} ∩ C.Jplus W S ∩ B) := hK.inter_right hB
  have hKne : (C.Jminus W {q} ∩ C.Jplus W S ∩ B).Nonempty :=
    ⟨q, ⟨by simpa using C.le_refl hqW, hq.1⟩, hq.2⟩
  have hJK : ∀ x ∈ C.Jminus W {q} ∩ C.Jplus W S ∩ B,
      IsClosed (C.Jminus W {x} ∩ (C.Jminus W {q} ∩ C.Jplus W S ∩ B)) := by
    intro x hx
    refine isClosed_of_closure_subset fun y hy => ?_
    have hyK : y ∈ C.Jminus W {q} ∩ C.Jplus W S ∩ B :=
      hKc.isClosed.closure_subset (closure_mono inter_subset_right hy)
    exact ⟨hJ x (hKW hx) ⟨closure_mono inter_subset_left hy, hKW hyK⟩, hyK⟩
  obtain ⟨p, hpK, hp⟩ := exists_minimal_of_isCompact_on hcaus hKc hKW hKne hJK
  refine ⟨p, hpK, ?_⟩
  refine Eq.trans ?_ hp
  ext z
  constructor
  · rintro ⟨⟨hzp, hzB⟩, hzS⟩
    refine ⟨hzp, ⟨⟨?_, hzS⟩, hzB⟩⟩
    have h1 : C.le W z p := by simpa using hzp
    have h2 : C.le W p q := by simpa using hpK.1.1
    simpa using C.le_trans h1 h2
  · rintro ⟨hzp, ⟨⟨-, hzS⟩, hzB⟩⟩
    exact ⟨⟨hzp, hzB⟩, hzS⟩

/-- **ERS19 Theorem 4.82, causal-topological skeleton.** `dom i` are the domains of the GHDs,
`cau i` the causalities of `g(uᵢ, duᵢ)`, `dom i₁` the MGHD (`hmax`); `A` is the component of
`U₁ ∩ U₂` through `s₀ ∈ S`.

Suppliers (layer 3): `hstep` — Steps 3–5 of Theorem 4.64 as used at the end of the proof of 4.82:
the time separation `τ_q` from a point `q ∈ I⁺(p)` in a convex neighbourhood, its smoothness via
`exp_q`, the spacelike level set `Σ = τ_q⁻¹(τ₀)` (O'Neill Ch. 5, Cor. 3) meeting `∂A`, the
acausality of `Σ_V` (O'Neill 14.46), its domain of dependence `D(Σ_V)` in `V ⊆ U₂`, local
uniqueness (Proposition 4.63), the half "points above the graph lie outside `U₁`" of (4.83), and
"`u₃` on `U₁ ∪ D(Σ_V)` is a GHD" (text line 2114); `honesided` — (4.83), through the chart: shrink
the base of the box so that each vertical fibre below the graph is a non-empty interval (`V ∩ U₁`
preconnected), the condition Lemma 4.86 supplies from (4.87); `hconn` — each GHD domain is connected
(`S` connected and every point on an inextendible curve meeting `S`:
`Causal.isConnected_of_curves`, module `Causal.SubExtension`); `hsplit` — a Cauchy hypersurface splits its
development into `J⁺(S) ∪ J⁻(S)`; `hJm`, `hJp` — `J^±(x)` closed in a globally hyperbolic
development; `hKm`, `hKp` — `J^∓(q) ∩ J^±(S)` compact in a globally hyperbolic development with
Cauchy hypersurface `S`; `hcaus` — a globally hyperbolic development is causal; `hSclosed` — a
Cauchy hypersurface is closed in its development; `hmax` — `u₁` is an MGHD. -/
theorem ers_theorem_4_82 [T2Space M] [LocallyConnectedSpace M] {ι : Type*}
    (dom : ι → Opens M) (cau : ι → Causality M) {s₀ : M} (hs₀ : s₀ ∈ S) (i₁ : ι)
    (hSU : ∀ i, S ⊆ dom i)
    (hmax : ∀ i, dom i₁ ≤ dom i → dom i = dom i₁)
    (hconn : ∀ i, IsPreconnected (dom i : Set M))
    (hcaus : ∀ i ⦃x y : M⦄, (cau i).le (dom i) x y → (cau i).le (dom i) y x → x = y)
    (hsplit : ∀ i, ∀ q ∈ dom i, q ∈ (cau i).Jplus (dom i) S ∪ (cau i).Jminus (dom i) S)
    (hJm : ∀ i, ∀ x ∈ dom i, closure ((cau i).Jminus (dom i) {x}) ∩ dom i ⊆
      (cau i).Jminus (dom i) {x})
    (hJp : ∀ i, ∀ x ∈ dom i, closure ((cau i).Jplus (dom i) {x}) ∩ dom i ⊆
      (cau i).Jplus (dom i) {x})
    (hKm : ∀ i q, IsCompact ((cau i).Jminus (dom i) {q} ∩ (cau i).Jplus (dom i) S))
    (hKp : ∀ i q, IsCompact ((cau i).Jplus (dom i) {q} ∩ (cau i).Jminus (dom i) S))
    (hSclosed : ∀ i, closure S ∩ dom i ⊆ S)
    (honesided : ∀ p ∈ frontier (dom i₁ : Set M) \ closure S, ∀ N ∈ 𝓝 p,
      ∃ V ∈ 𝓝 p, V ⊆ N ∧ IsPreconnected (V ∩ dom i₁))
    (hstep : ∀ i, ∀ p ∈ frontier (connectedComponentIn ((dom i₁ : Set M) ∩ dom i) s₀) ∩ dom i,
      ((cau i).Jminus (dom i) {p} ∩ frontier (connectedComponentIn ((dom i₁ : Set M) ∩ dom i) s₀)
          ∩ (cau i).Jplus (dom i) S = {p} ∨
        (cau i).Jplus (dom i) {p} ∩ frontier (connectedComponentIn ((dom i₁ : Set M) ∩ dom i) s₀)
          ∩ (cau i).Jminus (dom i) S = {p}) →
      (∃ V ∈ 𝓝 p, V ⊆ dom i ∧
        V ∩ dom i₁ ⊆ connectedComponentIn ((dom i₁ : Set M) ∩ dom i) s₀) →
      ∃ j, dom i₁ < dom j) :
    ∀ i, dom i ≤ dom i₁ := by
  intro i
  by_contra hnot
  have hs₀' : s₀ ∈ (dom i₁ : Set M) ∩ dom i := ⟨hSU i₁ hs₀, hSU i hs₀⟩
  obtain ⟨⟨q, hqf, hqi⟩, hsub⟩ := frontier_connectedComponentIn_inter (dom i₁).isOpen
    (dom i).isOpen hs₀' (hconn i) fun h => hnot h
  have hBcl : IsClosed (frontier (connectedComponentIn ((dom i₁ : Set M) ∩ dom i) s₀)) :=
    isClosed_frontier
  -- (4.65)/(4.85): a boundary point with no other boundary point causally below (or above) it
  obtain ⟨p, hpmem, hp⟩ : ∃ p ∈ frontier (connectedComponentIn ((dom i₁ : Set M) ∩ dom i) s₀) ∩
      dom i, ((cau i).Jminus (dom i) {p} ∩
          frontier (connectedComponentIn ((dom i₁ : Set M) ∩ dom i) s₀) ∩
          (cau i).Jplus (dom i) S = {p} ∨
        (cau i).Jplus (dom i) {p} ∩
          frontier (connectedComponentIn ((dom i₁ : Set M) ∩ dom i) s₀) ∩
          (cau i).Jminus (dom i) S = {p}) := by
    rcases hsplit i q hqi with hq | hq
    · obtain ⟨p, hpK, hp⟩ := exists_spacelike_boundary_point (hcaus i) (hJm i) hBcl ⟨hq, hqf⟩
        (hKm i q)
      obtain ⟨y, -, hpy⟩ := hpK.1.1
      exact ⟨p, ⟨hpK.2, (cau i).le_mem_left hpy⟩, Or.inl hp⟩
    · obtain ⟨p, hpK, hp⟩ := exists_spacelike_boundary_point (C := (cau i).dual)
        (fun _ _ h1 h2 => hcaus i h2 h1) (hJp i) hBcl ⟨hq, hqf⟩ (hKp i q)
      obtain ⟨y, -, hpy⟩ := hpK.1.1
      exact ⟨p, ⟨hpK.2, (cau i).le_mem_right hpy⟩, Or.inr hp⟩
  -- `p` lies on the boundary of `U₁`, off the closure of `S`
  have hp₁ : p ∈ frontier (dom i₁ : Set M) := hsub hpmem
  have hpS : p ∉ closure S := fun h => by
    have hpU₁ : p ∉ (dom i₁ : Set M) := by
      rw [(dom i₁).isOpen.frontier_eq] at hp₁; exact hp₁.2
    exact hpU₁ (hSU i₁ (hSclosed i ⟨h, hpmem.2⟩))
  -- the one-sidedness (4.83) gives a neighbourhood meeting `U₁` inside the component
  obtain ⟨V, hV, hVsub, hVconn⟩ := honesided p ⟨hp₁, hpS⟩ _ ((dom i).isOpen.mem_nhds hpmem.2)
  have hVA := inter_subset_connectedComponentIn (frontier_subset_closure hpmem.1) hV hVsub hVconn
  obtain ⟨j, hj⟩ := hstep i p hpmem hp ⟨V, hV, hVsub, hVA⟩
  have := hmax j hj.le
  rw [this] at hj
  exact lt_irrefl _ hj

end Causality

/-! ### Witnesses: the hypotheses are jointly satisfiable (kb/0011) -/

/-- The timelike line is nested in itself in the sense of inextensibility, through
`GloballyHyperbolic.inextensibleNestedOn_top`: its hypotheses are satisfiable. -/
theorem timelikeLine_inextensibleNestedOn_top :
    Causality.InextensibleNestedOn timelikeLine timelikeLine ⊤ :=
  Causality.GloballyHyperbolic.inextensibleNestedOn_top timelikeLine_tarentin
    timelikeLine_globallyHyperbolic timelikeLine_causallyArcConnected timelikeLine_Jminus_ne
    timelikeLine_Jplus_ne ((Causality.LeNested.refl _).curveNestedOn ⊤)

/-- The hypotheses of `ers_lemma_4_70` are jointly satisfiable: the timelike line for `Cτ`, `C₁`,
`C₂`, `U₁ = U₂ = ℝ`, `S = {0}`. -/
theorem timelikeLine_ers_lemma_4_70 :
    IsPreconnected (((⊤ : Opens ℝ) ⊓ ⊤ : Opens ℝ) : Set ℝ) :=
  Causality.ers_lemma_4_70 (Cτ := timelikeLine) (C₁ := timelikeLine) (C₂ := timelikeLine)
    (S := {0}) isPreconnected_singleton (fun _ _ => trivial) (fun _ _ => trivial)
    timelikeLine_isCauchySurface_zero timelikeLine_isCauchySurface_zero timelikeLine_isCausal
    (fun x _ => ⟨univ, id, timelikeLine_inextensible_id, x, trivial, rfl⟩)
    (fun _ _ _ _ hy _ hz => (mem_singleton_iff.1 hy.2).trans (mem_singleton_iff.1 hz.2).symm)
    (fun _ _ h => h) (fun _ _ h => h)

/-- The hypotheses of `ers_lemma_4_72` are jointly satisfiable: the timelike line for `Cm` and
`C₂`, `U₁ = U₂ = ℝ`, `S = {0}`. -/
theorem timelikeLine_ers_lemma_4_72 :
    IsPreconnected (((⊤ : Opens ℝ) ⊓ ⊤ : Opens ℝ) : Set ℝ) :=
  Causality.ers_lemma_4_72 (Cm := timelikeLine) (C₂ := timelikeLine) (S := {0})
    isPreconnected_singleton (fun _ _ => trivial) (fun _ _ => trivial) timelikeLine_isCausal
    timelikeLine_curvesExtend
    (fun _ hx _ hy _ => (mem_singleton_iff.1 hx).trans (mem_singleton_iff.1 hy).symm)
    timelikeLine_isCauchySurface_zero timelikeLine_isCauchySurface_zero
    (fun x _ => ⟨univ, id, timelikeLine_inextensible_id, x, trivial, rfl⟩)
    ((Causality.LeNested.refl _).curveNestedOn ⊤)

/-- The hypotheses of `ers_theorem_4_77` are jointly satisfiable: the timelike line, the family
`ℝ` indexed by `Unit`, `S = {0}`. -/
theorem timelikeLine_ers_theorem_4_77 :
    timelikeLine.IsCauchySurfaceOn (⨆ _ : Unit, (⊤ : Opens ℝ)) {0} :=
  Causality.ers_theorem_4_77 (fun _ : Unit => (⊤ : Opens ℝ)) (fun _ _ _ => trivial)
    (fun _ _ h1 h2 => timelikeLine_isCausal (timelikeLine.le_mono le_top h1)
      (timelikeLine.le_mono le_top h2))
    (fun _ => timelikeLine_isCauchySurface_zero)
    (fun _ _ => by rw [inf_top_eq]; exact timelikeLine_isCauchySurface_zero)

end Causal
