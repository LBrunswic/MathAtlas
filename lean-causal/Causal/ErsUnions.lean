import Causal.ErsUniqueness
import Causal.CBG.CausalConvex
import Mathlib.Topology.Connected.LocallyConnected

/-!
# ERS19 Proposition 4.63 and Theorem 4.75 on a fixed background: unions of local developments

Programme target `T-abs-ers-unions` (`programme/roadmap.toml`; layer 1, ETT-layer imports only,
no model, no metric). Source: Eperon–Reall–Sbierski, arXiv 1802.03020, `papers/ers-predictability`
(`legacy/labeled/ghd_02_19.tex`; text `references/sbierski/text/eperon2018predictability.txt`).
Causal-topological skeletons whose analytic inputs (local uniqueness, local existence, the slice
restart of Thm 4.64) are named hypotheses; **no label is marked**:

* `ersprop:PropLocUniqueness` — `ghd_02_19.tex:836` (proof 840–844): `ers_prop_4_63` (the union
  of the local developments is a common development), `ers_prop_4_63_globallyHyperbolicOn` (and
  it is globally hyperbolic, causally convex in `U₁`), `ers_prop_4_63_of_hasTimeFunction` (the
  same from ladder properties at `M`); the union lemmas `isCauchySurfaceOn_sSup_of_isAcausalOn`,
  `isCauchySurfaceOn_sSup_of_curvesExtendOn`, `globallyHyperbolicOn_sSup_of_pieces`; in a region,
  `isDevelopmentIn_localDevelopmentUnion`; with 4.64, `ers_theorem_4_64_of_localUniqueness`.
* `ersthm:ThmEx` — `ghd_02_19.tex:1001` (proof 1011–1022): `ers_theorem_4_75` (the local
  developments patch to a solution on `⋃ DS_p`, of which `S` is a Cauchy surface),
  `ers_theorem_4_75_eqOn` (the claim `u_p = u_q` on `DS_p ∩ DS_q`), through
  `ers_theorem_4_64_in` (Theorem 4.64's argument run in a component of `DS_p ∩ DS_q`) and
  `isCauchySurfaceOn_iSup_of_inf` (Theorem 4.77's union argument without `S ⊆ Uᵢ`).

> Proposition 4.63 (Local uniqueness). Let u1 : U1 → R and u2 : U2 → R be two globally
> hyperbolic developments for (4.61) of the same initial data prescribed on a hypersurface
> S ⊆ R^{d+1}. Then there exists a common globally hyperbolic development v : V → R.
> *Proof.* […] The standard literature methods […] ensure that there is an open neighbourhood
> DS_p ⊆ W_p of S_p with the property that any two solutions, which are defined on DS_p and attain
> the given initial data on S_p, agree, and such that DS_p is globally hyperbolic with Cauchy
> hypersurface S_p. It thus follows that u1|DS_p = u2|DS_p. We now set V = ⋃_{p∈S} DS_p. It is
> immediate that u1 and u2 agree on this set and that V is globally hyperbolic with Cauchy
> hypersurface S.

> Theorem 4.75 (Local existence). Given initial data for a quasilinear wave equation (4.61), there
> exists a globally hyperbolic development.
> *Proof.* […] there exists a globally hyperbolic development u_p : DS_p → R for (4.61) of the
> initial data on S_p, where DS_p ⊆ W_p. […] We now claim that for all p, q ∈ S we have u_p = u_q
> on DS_p ∩ DS_q. […] let A be a connected component of DS_p ∩ DS_q. […] Theorem 4.64 implies
> that we have u_p = u_q on D_pS_A ∩ D_qS_A. […] We thus conclude that D_pS_A ∩ D_qS_A = A. […]
> Hence, we can finish the proof by constructing a GHD u : U → R of the given initial data on S
> by setting U = ⋃_{p∈S} DS_p and u(x) = u_p(x) for x ∈ DS_p.

## The reading

As `Causal.ErsUniqueness` (OQ-57): `M` the fixed background, solutions an agreement predicate
that glues (`AgreementGlues`; for functions `EqOn`), a common development (`IsCommonDevelopment`)
has `S` as Cauchy surface, GH concluded only where proved. Local uniqueness (Sogge) is the named
`LocalUniqueness`: every `p ∈ S` lies in an open `DS_p ≤ L` on which the solutions agree, with a
Cauchy surface `S_p ⊆ S`. In Theorem 4.75 each local solution `u_p` has its own causality
`cau p` (of `g(u_p)`); the patched causality `Cu` (of `g(u)`) is any causality agreeing with
`cau p` on the open subsets of `DS_p`, chosen after the patching. A *development in a region `L`*
(`IsDevelopmentIn`) is an open `V ≤ L` containing `S ∩ L`, with agreement and `S` Cauchy.

## Hypothesis checklist

| paper | here |
|---|---|
| standing (ghd_02_19.tex:812–814): `S` connected, `U ⊆ ℝ^{d+1}`, `u` real-valued | ⚠ weakened: `S` any set, connectedness not used; `ℝ^{d+1}` read as `[T2Space M]` (4.63), `[T2Space M] [LocallyConnectedSpace M]` (4.75); values in any `β`, `[Nonempty β]` (4.75) |
| 4.63: `u₁` a GHD with Cauchy hypersurface `S` | ✓ `GloballyHyperbolicOn U₁` (ladder `globally_hyperbolic` on `U₁`), `IsCauchySurfaceOn U₁ S` (GH form); in `ers_prop_4_63` the reading (OQ-41, as 4.64) `IsAcausalOn U₁ S`, with only `≤_{U₁}` antisymmetric |
| 4.63: `u₂` a GHD | ⚠ weakened: not used (consumed by the supplier of `LocalUniqueness`) |
| 4.63: Sogge's `DS_p` (local uniqueness) | ⚠ named: `LocalUniqueness S (U₁ ⊓ U₂) agree` (binder `local_uniqueness`); only `p ∈ DS_p`, `S_p ⊆ S` asked |
| 4.63: "immediate": `V` has Cauchy hypersurface `S` | ✓ proved, from `S` acausal in `U₁`, or from `S` Cauchy in `U₁` with curves extending in `U₁` |
| 4.63: "immediate": `V` globally hyperbolic | ✓ proved under ⚠ strengthened: `CausallyArcConnectedOn U₁` and `CurvesExtendOn U₁` (Lorentzian facts, kb/0012; at `M`: `causally_arc_connected`, `time_function`) |
| 4.75: local existence on `{t = 0}` patches (Sogge) | ⚠ named: the family `D i`, `u i`, `cau i` covering `S`, each an `IsLocalDevelopment` (4.64's inputs for a GHD) |
| 4.75: `N` timelike on `DS_p`; its integral curves | ⚠ named: each component of `DS_p ∩ DS_q` meets `S` (`RestartsIn.meets`) |
| 4.75: Thm 4.64 on `D_pS_A, D_qS_A`; `D_pS_A ∩ D_qS_A = A` | ✓ replaced by 4.64's argument in the component `A` (`ers_theorem_4_64_in`); its inputs ⚠ named, located in `A` (`RestartsIn`: Prop 4.63's local uniqueness and `SliceRestart`, supplier T-loc-quasilinear-slice; `FrontierStaysIn`, supplier T-loc-quasilinear-frontier; both scoped today to `U₁ ∩ U₂`), for `p ≠ q` only |
| 4.75: `U = ⋃ DS_p` a GHD (:1021, not argued) | ✓ `S` Cauchy in `U` for `Cu` (Thm 4.77's argument); ⚠ strengthened: `≤_U` of `Cu` antisymmetric, a part of the paper's printed conclusion (`U` a GHD, :1021, so GH, so causal, :814) assumed, as in `ers_theorem_4_77` (`hcaus`, OQ-41 (d)); GH not concluded (OQ-57 (c)) |

## SCOPE (disclosed)

* **No label is marked.** Both statements rest on named analytic inputs which the paper cites
  (Sogge) rather than assumes; 4.75 also on Theorem 4.64's named restart.
* **Prop 4.63's full conclusion** (not a certification: the row is partial, unmarked).
  `ers_prop_4_63_globallyHyperbolicOn` concludes everything the paper does: a common development,
  globally hyperbolic with Cauchy surface `S`, under the strengthened hypotheses of the checklist.
  ERS get GH of `V` from its Cauchy property (Geroch), so they use `U₁` once, for the uniqueness
  of the meeting with `S`. In ETT, for developments inside a GH `U₁`, no Geroch (iii) ⇒ (i) is
  needed: causal convexity in `U₁` suffices
  (`IsCommonDevelopment.globallyHyperbolicOn`, which applies to the maximal common development
  `V₀` of Thm 4.64 as well, and gives Remark 4.67's "maximal common GHD" as printed,
  `ers_remark_4_67_globallyHyperbolicOn`) — evidence for OQ-57 (c), not a ruling.
* **Thm 4.75's union is not GH here**: there is no ambient development (Geroch (iii) ⇒ (i),
  `CausalScaffold.GerochEquiv`). ERS do not argue the Cauchy property of `U` either
  (ghd_02_19.tex:1021–1022); it is Thm 4.77's open–closed argument, with `S` Cauchy in each
  `DS_p ∩ DS_q` (a by-product of the claim) and `≤_U` antisymmetric (ETT's component lemma),
  which is a part of the printed conclusion assumed.
* **The route of the claim.** ERS apply 4.64 to the domains of dependence `D_pS_A`, `D_qS_A`
  of a component `S_A` of `A ∩ S` and show `D_pS_A ∩ D_qS_A = A` by a boundary argument. Here
  4.64's argument is run in `A` itself (`maxDevelopmentIn_eq`): the maximal development in `A`
  is `A`. This gives the agreement and `S` Cauchy in `A` at once, with no domain of dependence.
* **`LocalUniqueness` is not a ladder node**: it is a predicate on `C`, `S`, a region and the
  solutions, not on one causality.
* **Non-vacuity** (kb/0011): `timelikeLine_ers_prop_4_63` (`U₂ = ]-1, 1[`, `DS_0 = ]-1/2, 1/2[`)
  and `timelikeLine_ers_theorem_4_75` (two patches `ℝ`, `]-1, 1[`, solutions `id` and the
  clamp). The ambient cannot be dropped from the union lemmas:
  `timelikeLine_not_isCauchySurfaceOn_union` (`S = {0, 1}`, patches `]-1, 1[ ∋ 0`, `]0, 2[ ∋ 1`;
  1+0 dimensions, `S` disconnected, whereas ERS's `S` is connected, :814). In the 4.75 witness
  the `SliceRestart` premise is inhabited (`V = ]-1/2, 1/2[`, frontier point `1/2`), but the
  restart branch of `maxDevelopmentIn_eq` is not entered: `]-1, 1[` is itself a development.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Filter Function

open scoped Interval

universe u v

variable {M : Type u} [TopologicalSpace M]

/-- The connected component of `x` in the open set `W`, as an open set (`M` locally connected):
ERS's component `A` of `DS_p ∩ DS_q`. -/
def componentOpens [LocallyConnectedSpace M] (W : Opens M) (x : M) : Opens M :=
  ⟨connectedComponentIn (W : Set M) x, W.isOpen.connectedComponentIn⟩

theorem componentOpens_le [LocallyConnectedSpace M] (W : Opens M) (x : M) :
    componentOpens W x ≤ W :=
  connectedComponentIn_subset _ _

theorem mem_componentOpens [LocallyConnectedSpace M] {W : Opens M} {x : M} (hx : x ∈ W) :
    x ∈ componentOpens W x :=
  mem_connectedComponentIn hx

/-- A preconnected open set is its own component. -/
theorem componentOpens_eq_self [LocallyConnectedSpace M] {W : Opens M}
    (hW : IsPreconnected (W : Set M)) {x : M} (hx : x ∈ W) : componentOpens W x = W :=
  SetLike.coe_injective (hW.connectedComponentIn hx)

namespace Causality

variable {C : Causality M} {S : Set M}

/-! ## 1. Cauchy surfaces of unions of local developments -/

/-- **Existence by the pieces, uniqueness by acausality**: if every inextensible curve of `W`
meets `S` and `S` is acausal in `W`, then `S` is a Cauchy surface of `W`. -/
theorem isCauchySurfaceOn_of_meets_of_isAcausalOn {W : Opens M}
    (hmeet : ∀ (I : Set ℝ) (c : ℝ → M), C.Inextensible W I c → (c '' I ∩ S).Nonempty)
    (hac : C.IsAcausalOn W S) : C.IsCauchySurfaceOn W S := by
  intro I c hc
  obtain ⟨x, hx⟩ := hmeet I c hc
  refine ⟨x, hx, ?_⟩
  obtain ⟨⟨s, hs, rfl⟩, hxS⟩ := hx
  rintro _ ⟨⟨t, ht, rfl⟩, hyS⟩
  rcases le_total s t with h | h
  · exact (hac _ hxS _ hyS (hc.1.le_of_le hs ht h)).symm
  · exact hac _ hyS _ hxS (hc.1.le_of_le ht hs h)

/-- A piece `S' ⊆ S` Cauchy in `W`, `S` acausal in `W`: `S` is Cauchy in `W` (ERS's `S_p` and
`S ∩ DS_p`). -/
theorem IsCauchySurfaceOn.of_subset_of_isAcausalOn {W : Opens M} {S' : Set M}
    (hW : C.IsCauchySurfaceOn W S') (hS' : S' ⊆ S) (hac : C.IsAcausalOn W S) :
    C.IsCauchySurfaceOn W S := by
  refine isCauchySurfaceOn_of_meets_of_isAcausalOn (fun I c hc => ?_) hac
  obtain ⟨x, hx, -⟩ := hW I c hc
  exact ⟨x, hx.1, hS' hx.2⟩

/-- Two points of `S` on a causal curve of `W ≤ B` coincide when `S` is a Cauchy surface of `B`
in which curves extend (Sbierski: "`γ` is also a segment of an inextendible timelike curve"). -/
theorem eq_of_mem_of_curvesExtendOn {W B : Opens M} (hWB : W ≤ B)
    (hext : C.CurvesExtendOn B) (hB : C.IsCauchySurfaceOn B S) {I : Set ℝ} {c : ℝ → M}
    (hc : C.CausalCurveIn W I c) {s t : ℝ} (hs : s ∈ I) (ht : t ∈ I) (hsS : c s ∈ S)
    (htS : c t ∈ S) : c s = c t := by
  have key : ∀ s ∈ I, ∀ s' ∈ I, s ≤ s' → c s ∈ S → c s' ∈ S → c s = c s' := by
    intro s hs s' hs' h hsS hs'S
    obtain ⟨J, c', hc', hsub⟩ := hext c s s' h
      (CurveOn.mono_opens C.isRelFamily_le (hc.curve s hs s' hs') hWB)
    exact (hB J c' hc').unique ⟨hsub ⟨s, ⟨le_rfl, h⟩, rfl⟩, hsS⟩
      ⟨hsub ⟨s', ⟨h, le_rfl⟩, rfl⟩, hs'S⟩
  rcases le_total s t with h | h
  · exact key s hs t ht h hsS htS
  · exact (key t ht s hs h htS hsS).symm

/-- A piece `S' ⊆ S` Cauchy in `W ≤ B`, `S` Cauchy in `B` with curves extending in `B`: `S` is
Cauchy in `W`. -/
theorem IsCauchySurfaceOn.of_subset_of_curvesExtendOn {W B : Opens M} {S' : Set M}
    (hW : C.IsCauchySurfaceOn W S') (hS' : S' ⊆ S) (hWB : W ≤ B) (hext : C.CurvesExtendOn B)
    (hB : C.IsCauchySurfaceOn B S) : C.IsCauchySurfaceOn W S := by
  intro I c hc
  obtain ⟨_, ⟨⟨s, hs, rfl⟩, hsS'⟩, -⟩ := hW I c hc
  refine ⟨c s, ⟨⟨s, hs, rfl⟩, hS' hsS'⟩, ?_⟩
  rintro _ ⟨⟨t, ht, rfl⟩, htS⟩
  exact (eq_of_mem_of_curvesExtendOn hWB hext hB hc.1 hs ht (hS' hsS') htS).symm

/-- **ERS Prop 4.63's union, by acausality**: a set `𝒟` of opens inside `B`, each with a Cauchy
surface `S' ⊆ S`, `≤_B` antisymmetric, `S` acausal in `B`, `M` Hausdorff: `S` is a Cauchy surface
of `⋃ 𝒟`. An inextensible curve of the union meets `S` through its component in one member
(`inextensible_ordConnectedComponent_of_le`); at most once by acausality. -/
theorem isCauchySurfaceOn_sSup_of_isAcausalOn [T2Space M] {B : Opens M} {𝒟 : Set (Opens M)}
    (hanti : ∀ ⦃x y : M⦄, C.le B x y → C.le B y x → x = y) (hac : C.IsAcausalOn B S)
    (h𝒟B : ∀ D ∈ 𝒟, D ≤ B) (h𝒟 : ∀ D ∈ 𝒟, ∃ S' ⊆ S, C.IsCauchySurfaceOn D S') :
    C.IsCauchySurfaceOn (sSup 𝒟) S := by
  have hUB : sSup 𝒟 ≤ B := sSup_le h𝒟B
  have hantiU : ∀ ⦃x y : M⦄, C.le (sSup 𝒟) x y → C.le (sSup 𝒟) y x → x = y :=
    fun _ _ h h' => hanti (C.le_mono hUB h) (C.le_mono hUB h')
  refine isCauchySurfaceOn_of_meets_of_isAcausalOn (fun I c hc => ?_) (hac.mono hUB)
  obtain ⟨t₀, ht₀⟩ := hc.1.nonempty
  obtain ⟨D, hD, hcD⟩ := Opens.mem_sSup.1 (hc.1.mem ht₀)
  obtain ⟨S', hS'S, hS'⟩ := h𝒟 D hD
  obtain ⟨_, ⟨⟨τ, hτ, rfl⟩, hτS⟩, -⟩ := hS' _ c
    (inextensible_ordConnectedComponent_of_le hantiU (le_sSup hD) hc ht₀ hcD)
  exact ⟨c τ, ⟨τ, (ordConnectedComponent_subset hτ).1, rfl⟩, hS'S hτS⟩

/-- **ERS Prop 4.63's union, by an ambient Cauchy surface**: as
`isCauchySurfaceOn_sSup_of_isAcausalOn`, with "`S` acausal in `B`" replaced by "`S` a Cauchy
surface of `B`, curves extending in `B`" (`Causality.isCauchySurfaceOn_iSup` for pieces). -/
theorem isCauchySurfaceOn_sSup_of_curvesExtendOn [T2Space M] {B : Opens M} {𝒟 : Set (Opens M)}
    (hanti : ∀ ⦃x y : M⦄, C.le B x y → C.le B y x → x = y) (hext : C.CurvesExtendOn B)
    (hB : C.IsCauchySurfaceOn B S) (h𝒟B : ∀ D ∈ 𝒟, D ≤ B)
    (h𝒟 : ∀ D ∈ 𝒟, ∃ S' ⊆ S, C.IsCauchySurfaceOn D S') :
    C.IsCauchySurfaceOn (sSup 𝒟) S := by
  rw [sSup_eq_iSup']
  refine Causality.isCauchySurfaceOn_iSup hanti hext (fun D => h𝒟B D.1 D.2) (fun D => ?_) hB
  obtain ⟨S', hS'S, hS'⟩ := h𝒟 D.1 D.2
  exact hS'.of_subset_of_curvesExtendOn hS'S (h𝒟B D.1 D.2) hext hB

/-- **The union is globally hyperbolic** (ERS Prop 4.63's last assertion): inside a globally
hyperbolic `B`, causally arc-connected, with curves extending and `S` a Cauchy surface, a union of
opens with Cauchy surfaces `S' ⊆ S` and containing `S` has `S` as Cauchy surface, is causally
convex in `B` (`causallyConvexIn_of_isCauchySurfaceOn`), hence globally hyperbolic
(`GloballyHyperbolicOn.of_causallyConvexIn`). -/
theorem globallyHyperbolicOn_sSup_of_pieces [T2Space M] {B : Opens M} {𝒟 : Set (Opens M)}
    (hC : C.CausallyArcConnectedOn B) (hext : C.CurvesExtendOn B) (hG : C.GloballyHyperbolicOn B)
    (hB : C.IsCauchySurfaceOn B S) (h𝒟B : ∀ D ∈ 𝒟, D ≤ B)
    (h𝒟 : ∀ D ∈ 𝒟, ∃ S' ⊆ S, C.IsCauchySurfaceOn D S') (hS : S ⊆ (sSup 𝒟 : Opens M)) :
    C.IsCauchySurfaceOn (sSup 𝒟) S ∧ C.CausallyConvexIn ((sSup 𝒟 : Opens M) : Set M) B ∧
      C.GloballyHyperbolicOn (sSup 𝒟) := by
  have hU := isCauchySurfaceOn_sSup_of_curvesExtendOn hG.1 hext hB h𝒟B h𝒟
  have hconv : C.CausallyConvexIn ((sSup 𝒟 : Opens M) : Set M) B :=
    causallyConvexIn_of_isCauchySurfaceOn hG.1 hC hext (sSup_le h𝒟B) hS hU hB
  exact ⟨hU, hconv, GloballyHyperbolicOn.of_causallyConvexIn hC hG hconv⟩

/-! ## 2. Local uniqueness and Proposition 4.63 -/

variable (C) in
/-- **Local uniqueness** (ERS Prop 4.63's PDE input: Sogge, energy estimates; proposed ladder id
`local_uniqueness`, binder `open_localisation`): every point `p ∈ S` lies in an open `DS_p ≤ L`
on which the solutions agree, with a Cauchy surface `S_p ⊆ S`. Supplier: ERS's `DS_p ⊆ W_p`,
`S_p` an open neighbourhood of `p` in `S` (T-loc-quasilinear-slice). Only `p ∈ DS_p` is asked,
not `p ∈ S_p ⊆ DS_p`. -/
def LocalUniqueness (S : Set M) (L : Opens M) (agree : Opens M → Prop) : Prop :=
  ∀ p ∈ S, ∃ D : Opens M, p ∈ D ∧ D ≤ L ∧ agree D ∧ ∃ Sp ⊆ S, C.IsCauchySurfaceOn D Sp

variable (C) in
/-- ERS's `V = ⋃_{p∈S} DS_p`: the union of all opens `D ≤ L` on which the solutions agree, with a
Cauchy surface contained in `S`. -/
def localDevelopmentUnion (S : Set M) (L : Opens M) (agree : Opens M → Prop) : Opens M :=
  sSup {D : Opens M | D ≤ L ∧ agree D ∧ ∃ Sp ⊆ S, C.IsCauchySurfaceOn D Sp}

variable (C) in
/-- A **development in the region `L`**: an open `V ≤ L` containing `S ∩ L`, on which the
solutions agree, with `S` as Cauchy surface. For `L = U₁ ⊓ U₂ ⊇ S` it is a common development
(`isCommonDevelopment_iff_isDevelopmentIn`); for `L` a component of `DS_p ∩ DS_q` it is what
Theorem 4.75's claim runs on. -/
structure IsDevelopmentIn (S : Set M) (L : Opens M) (agree : Opens M → Prop) (V : Opens M) :
    Prop where
  le : V ≤ L
  subset : S ∩ L ⊆ V
  agree : agree V
  cauchy : C.IsCauchySurfaceOn V S

theorem isCommonDevelopment_iff_isDevelopmentIn {U₁ U₂ V : Opens M} {agree : Opens M → Prop}
    (hS : S ⊆ ((U₁ ⊓ U₂ : Opens M) : Set M)) :
    C.IsCommonDevelopment S U₁ U₂ agree V ↔ C.IsDevelopmentIn S (U₁ ⊓ U₂) agree V := by
  constructor
  · intro h
    exact ⟨h.le, fun x hx => h.subset hx.1, h.agree, h.cauchy⟩
  · intro h
    exact ⟨h.le, fun x hx => h.subset ⟨hx, hS hx⟩, h.agree, h.cauchy⟩

/-- **ERS19 Proposition 4.63 in a region `L`** of an open `W` in which `≤_W` is antisymmetric and
`S` acausal: local uniqueness on `S ∩ L` makes the union of the local developments a development
in `L`. -/
theorem isDevelopmentIn_localDevelopmentUnion [T2Space M] {W L : Opens M}
    {agree : Opens M → Prop} (hglue : AgreementGlues agree)
    (hanti : ∀ ⦃x y : M⦄, C.le W x y → C.le W y x → x = y) (hacausal : C.IsAcausalOn W S)
    (hLW : L ≤ W) (hloc : C.LocalUniqueness (S ∩ L) L agree) :
    C.IsDevelopmentIn S L agree (C.localDevelopmentUnion (S ∩ L) L agree) := by
  set 𝒟 := {D : Opens M | D ≤ L ∧ agree D ∧ ∃ Sp ⊆ S ∩ L, C.IsCauchySurfaceOn D Sp}
  have h𝒟L : sSup 𝒟 ≤ L := sSup_le fun D hD => hD.1
  refine ⟨h𝒟L, fun p hp => ?_, hglue _ fun D hD => hD.2.1, ?_⟩
  · obtain ⟨D, hpD, hDL, hagD, hSp⟩ := hloc p hp
    exact le_sSup (show D ∈ 𝒟 from ⟨hDL, hagD, hSp⟩) hpD
  · refine isCauchySurfaceOn_sSup_of_isAcausalOn hanti hacausal
      (fun D hD => hD.1.trans hLW) fun D hD => ?_
    obtain ⟨Sp, hSpS, hSp⟩ := hD.2.2
    exact ⟨Sp, hSpS.trans inter_subset_left, hSp⟩

/-- **ERS19 Proposition 4.63, causal-topological skeleton** (`ersprop:PropLocUniqueness`,
unmarked): two developments of the same data have a common development, the union `V` of the
local developments `DS_p`. Hypotheses and suppliers: `hglue` — the solutions are functions
(`agreementGlues_eqOn`); `hG` — `U₁` GH for `g(u₁)` (only `≤_{U₁}` antisymmetric is used);
`hacausal` — `S` acausal in `U₁` (OQ-41); `hloc` — local uniqueness (Sogge). -/
theorem ers_prop_4_63 [T2Space M] {U₁ U₂ : Opens M} {agree : Opens M → Prop}
    (hglue : AgreementGlues agree) (hG : C.GloballyHyperbolicOn U₁)
    (hacausal : C.IsAcausalOn U₁ S) (hloc : C.LocalUniqueness S (U₁ ⊓ U₂) agree) :
    C.IsCommonDevelopment S U₁ U₂ agree (C.localDevelopmentUnion S (U₁ ⊓ U₂) agree) := by
  have hS : S ⊆ ((U₁ ⊓ U₂ : Opens M) : Set M) := fun p hp => by
    obtain ⟨D, hpD, hDL, -⟩ := hloc p hp
    exact hDL hpD
  have h := isDevelopmentIn_localDevelopmentUnion (L := U₁ ⊓ U₂) hglue hG.1 hacausal inf_le_left
    (by rwa [inter_eq_left.2 hS])
  rw [inter_eq_left.2 hS] at h
  exact (isCommonDevelopment_iff_isDevelopmentIn hS).2 h

/-- **A common development inside a GH `U₁` is GH**: `S` a Cauchy surface of `U₁`, `U₁` causally
arc-connected with curves extending; the common development is causally convex in `U₁`. Applies
to the maximal common development of Thm 4.64 (`isCommonDevelopment_maxCommonDevelopment`). -/
theorem IsCommonDevelopment.globallyHyperbolicOn [T2Space M] {U₁ U₂ V : Opens M}
    {agree : Opens M → Prop} (hV : C.IsCommonDevelopment S U₁ U₂ agree V)
    (hG : C.GloballyHyperbolicOn U₁) (hS : C.IsCauchySurfaceOn U₁ S)
    (hC : C.CausallyArcConnectedOn U₁) (hext : C.CurvesExtendOn U₁) :
    C.GloballyHyperbolicOn V ∧ C.CausallyConvexIn (V : Set M) U₁ := by
  have hconv : C.CausallyConvexIn (V : Set M) U₁ :=
    causallyConvexIn_of_isCauchySurfaceOn hG.1 hC hext (hV.le.trans inf_le_left) hV.subset
      hV.cauchy hS
  exact ⟨GloballyHyperbolicOn.of_causallyConvexIn hC hG hconv, hconv⟩

/-- **ERS19 Remark 4.67 with global hyperbolicity** (evidence for OQ-57 (c); `ersrem:RemTime`,
unmarked): under the hypotheses of `ers_remark_4_67`, with `S` a Cauchy surface of `U₁` and `U₁`
causally arc-connected with curves extending, `U₁ ∩ U₂` is the greatest common development **and
is globally hyperbolic**, causally convex in `U₁`: "the maximal common GHD" as printed. -/
theorem ers_remark_4_67_globallyHyperbolicOn [T2Space M] {U₁ U₂ : Opens M}
    {agree : Opens M → Prop} (hglue : AgreementGlues agree)
    (hG : C.GloballyHyperbolicOn U₁) (hT : C.TarentinOn U₁) (hacausal : C.IsAcausalOn U₁ S)
    (hsplit : C.SplitBy U₁ S) (hK : C.CompactSlabs U₁ S)
    (hconn : IsPreconnected ((U₁ ⊓ U₂ : Opens M) : Set M))
    (hlocal : ∃ V, C.IsCommonDevelopment S U₁ U₂ agree V)
    (hstay : ∀ V, C.IsCommonDevelopment S U₁ U₂ agree V →
      C.FrontierStaysIn U₁ S V ((U₁ ⊓ U₂ : Opens M) : Set M))
    (hstep : ∀ V, C.IsCommonDevelopment S U₁ U₂ agree V →
      C.SliceRestart U₁ S V ((U₁ ⊓ U₂ : Opens M) : Set M)
        (fun _ => ∃ V', C.IsCommonDevelopment S U₁ U₂ agree V' ∧ V < V'))
    (hS : C.IsCauchySurfaceOn U₁ S) (hC : C.CausallyArcConnectedOn U₁)
    (hext : C.CurvesExtendOn U₁) :
    IsGreatest {V | C.IsCommonDevelopment S U₁ U₂ agree V} (U₁ ⊓ U₂) ∧
      C.GloballyHyperbolicOn (U₁ ⊓ U₂) ∧ C.CausallyConvexIn ((U₁ ⊓ U₂ : Opens M) : Set M) U₁ := by
  have h := ers_remark_4_67 hglue hG hT hacausal hsplit hK hconn hlocal hstay hstep
  exact ⟨h, (show C.IsCommonDevelopment S U₁ U₂ agree (U₁ ⊓ U₂) from h.1).globallyHyperbolicOn
    hG hS hC hext⟩

/-- **ERS19 Proposition 4.63, the printed conclusion** (`ersprop:PropLocUniqueness`, unmarked):
the union `V` of the local developments is a common development, **globally hyperbolic** with
Cauchy surface `S`, causally convex in `U₁`. Hypotheses: `hG`, `hS` — `u₁` a GHD with Cauchy
hypersurface `S`; `hC`, `hext` — `U₁` causally arc-connected (ladder `causally_arc_connected`,
read on `U₁`) with curves extending (`CurvesExtendOn U₁`, kb/0012): Lorentzian facts, added;
`hloc` — local uniqueness. The acausality of `S` in `U₁` is derived
(`IsCauchySurfaceOn.eq_of_le`). -/
theorem ers_prop_4_63_globallyHyperbolicOn [T2Space M] {U₁ U₂ : Opens M}
    {agree : Opens M → Prop} (hglue : AgreementGlues agree) (hG : C.GloballyHyperbolicOn U₁)
    (hS : C.IsCauchySurfaceOn U₁ S) (hC : C.CausallyArcConnectedOn U₁)
    (hext : C.CurvesExtendOn U₁) (hloc : C.LocalUniqueness S (U₁ ⊓ U₂) agree) :
    C.IsCommonDevelopment S U₁ U₂ agree (C.localDevelopmentUnion S (U₁ ⊓ U₂) agree) ∧
      C.GloballyHyperbolicOn (C.localDevelopmentUnion S (U₁ ⊓ U₂) agree) ∧
      C.CausallyConvexIn ((C.localDevelopmentUnion S (U₁ ⊓ U₂) agree : Opens M) : Set M) U₁ := by
  have hacausal : C.IsAcausalOn U₁ S := fun x hx y hy hxy => hS.eq_of_le hC hext hx hy hxy
  have hV := ers_prop_4_63 hglue hG hacausal hloc
  exact ⟨hV, hV.globallyHyperbolicOn hG hS hC hext⟩

/-- **ERS19 Proposition 4.63, the printed conclusion, from ladder properties at `M`**
(`ersprop:PropLocUniqueness`, unmarked): `ers_prop_4_63_globallyHyperbolicOn` with the two added
relative hypotheses supplied by the ladder nodes `causally_arc_connected` (inherited by `U₁`) and
`time_function` (`HasTimeFunction`: curves extend in every open set,
`curvesExtendOn_of_timeFunction`). -/
theorem ers_prop_4_63_of_hasTimeFunction [T2Space M] {U₁ U₂ : Opens M}
    {agree : Opens M → Prop} (hglue : AgreementGlues agree) (hG : C.GloballyHyperbolicOn U₁)
    (hS : C.IsCauchySurfaceOn U₁ S) (hC : C.CausallyArcConnected) (hTf : C.HasTimeFunction)
    (hloc : C.LocalUniqueness S (U₁ ⊓ U₂) agree) :
    C.IsCommonDevelopment S U₁ U₂ agree (C.localDevelopmentUnion S (U₁ ⊓ U₂) agree) ∧
      C.GloballyHyperbolicOn (C.localDevelopmentUnion S (U₁ ⊓ U₂) agree) ∧
      C.CausallyConvexIn ((C.localDevelopmentUnion S (U₁ ⊓ U₂) agree : Opens M) : Set M) U₁ := by
  obtain ⟨T, hTc, hT⟩ := hTf
  exact ers_prop_4_63_globallyHyperbolicOn hglue hG hS (fun U _ => hC U le_top)
    (curvesExtendOn_of_timeFunction hTc hT U₁) hloc

/-- **Theorem 4.64 with Prop 4.63 assembled**: `ers_theorem_4_64` with its `hlocal` (some common
development exists) supplied by local uniqueness through `ers_prop_4_63`. -/
theorem ers_theorem_4_64_of_localUniqueness [T2Space M] {U₁ U₂ : Opens M}
    {agree : Opens M → Prop} (hglue : AgreementGlues agree)
    (hG : C.GloballyHyperbolicOn U₁) (hT : C.TarentinOn U₁) (hacausal : C.IsAcausalOn U₁ S)
    (hsplit : C.SplitBy U₁ S) (hK : C.CompactSlabs U₁ S)
    (hconn : IsPreconnected ((U₁ ⊓ U₂ : Opens M) : Set M))
    (hloc : C.LocalUniqueness S (U₁ ⊓ U₂) agree)
    (hstay : ∀ V, C.IsCommonDevelopment S U₁ U₂ agree V →
      C.FrontierStaysIn U₁ S V ((U₁ ⊓ U₂ : Opens M) : Set M))
    (hstep : ∀ V, C.IsCommonDevelopment S U₁ U₂ agree V →
      C.SliceRestart U₁ S V ((U₁ ⊓ U₂ : Opens M) : Set M)
        (fun _ => ∃ V', C.IsCommonDevelopment S U₁ U₂ agree V' ∧ V < V')) :
    agree (U₁ ⊓ U₂) := by
  exact ers_theorem_4_64 hglue hG hT hacausal hsplit hK hconn
    ⟨_, ers_prop_4_63 hglue hG hacausal hloc⟩ hstay hstep

/-! ## 3. Theorem 4.64 run in a region -/

variable (C) in
/-- The **maximal development in the region `L`**: the union of the developments in `L`. -/
def maxDevelopmentIn (S : Set M) (L : Opens M) (agree : Opens M → Prop) : Opens M :=
  sSup {V : Opens M | C.IsDevelopmentIn S L agree V}

/-- **Step 1 in a region**: the maximal development in `L ≤ W` is a development in `L`, when local
uniqueness holds on `S ∩ L`, `≤_W` is antisymmetric and `S` acausal in `W`. -/
theorem isDevelopmentIn_maxDevelopmentIn [T2Space M] {W L : Opens M} {agree : Opens M → Prop}
    (hglue : AgreementGlues agree) (hanti : ∀ ⦃x y : M⦄, C.le W x y → C.le W y x → x = y)
    (hacausal : C.IsAcausalOn W S) (hLW : L ≤ W) (hloc : C.LocalUniqueness (S ∩ L) L agree) :
    C.IsDevelopmentIn S L agree (C.maxDevelopmentIn S L agree) := by
  have h₀ := isDevelopmentIn_localDevelopmentUnion hglue hanti hacausal hLW hloc
  refine ⟨sSup_le fun V hV => hV.le, fun x hx => ?_, hglue _ fun V hV => hV.agree, ?_⟩
  · exact (le_sSup h₀ : _ ≤ C.maxDevelopmentIn S L agree) (h₀.subset hx)
  · exact isCauchySurfaceOn_sSup_of_isAcausalOn hanti hacausal (fun V hV => hV.le.trans hLW)
      fun V hV => ⟨S, subset_rfl, hV.cauchy⟩

/-- **ERS19 Theorem 4.64's argument in a region** (used by Theorem 4.75 on a component `A` of
`DS_p ∩ DS_q`): in a GH tarentin `W` with `S` acausal, splitting, with compact slabs, a
preconnected open `L ≤ W` meeting `S`, with local uniqueness on `S ∩ L` and the restart located
in `L`, has `L` as maximal development. Steps 1, 2 and the restart as in
`ers_theorem_4_64_maxCommonDevelopment`. -/
theorem maxDevelopmentIn_eq [T2Space M] {W L : Opens M} {agree : Opens M → Prop}
    (hglue : AgreementGlues agree) (hG : C.GloballyHyperbolicOn W) (hT : C.TarentinOn W)
    (hacausal : C.IsAcausalOn W S) (hsplit : C.SplitBy W S) (hK : C.CompactSlabs W S)
    (hLW : L ≤ W) (hconn : IsPreconnected (L : Set M)) (hSL : (S ∩ L).Nonempty)
    (hloc : C.LocalUniqueness (S ∩ L) L agree)
    (hstay : ∀ V, C.IsDevelopmentIn S L agree V → C.FrontierStaysIn W S V L)
    (hstep : ∀ V, C.IsDevelopmentIn S L agree V →
      C.SliceRestart W S V L (fun _ => ∃ V', C.IsDevelopmentIn S L agree V' ∧ V < V')) :
    C.maxDevelopmentIn S L agree = L := by
  have hV₀ := isDevelopmentIn_maxDevelopmentIn hglue hG.1 hacausal hLW hloc
  refine le_antisymm hV₀.le ?_
  by_contra hnot
  obtain ⟨s, hs⟩ := hSL
  have hne : ((L : Set M) ∩ C.maxDevelopmentIn S L agree).Nonempty := ⟨s, hs.2, hV₀.subset hs⟩
  -- a frontier point `q` of `V₀` in `L` (`L` connected)
  obtain ⟨q, hq⟩ := exists_mem_frontier_inter hconn (C.maxDevelopmentIn S L agree).isOpen hne
    fun h => hnot h
  -- Step 2: a spacelike frontier point `p` in `L`
  obtain ⟨p, hp, hsp⟩ := exists_isSpacelikeBoundaryPoint hG hT hsplit hK (fun x hx => hLW hx)
    (hstay _ hV₀) hq
  -- Steps 3–5 (the restart): a strictly larger development in `L`, against maximality
  obtain ⟨V', hV', hlt⟩ := hstep _ hV₀ p hp hsp
  exact lt_irrefl _ (hlt.trans_le (le_sSup hV'))

/-- **ERS19 Theorem 4.64 in a region**: under the hypotheses of `maxDevelopmentIn_eq`, the
solutions agree on `L` and `S` is a Cauchy surface of `L`. -/
theorem ers_theorem_4_64_in [T2Space M] {W L : Opens M} {agree : Opens M → Prop}
    (hglue : AgreementGlues agree) (hG : C.GloballyHyperbolicOn W) (hT : C.TarentinOn W)
    (hacausal : C.IsAcausalOn W S) (hsplit : C.SplitBy W S) (hK : C.CompactSlabs W S)
    (hLW : L ≤ W) (hconn : IsPreconnected (L : Set M)) (hSL : (S ∩ L).Nonempty)
    (hloc : C.LocalUniqueness (S ∩ L) L agree)
    (hstay : ∀ V, C.IsDevelopmentIn S L agree V → C.FrontierStaysIn W S V L)
    (hstep : ∀ V, C.IsDevelopmentIn S L agree V →
      C.SliceRestart W S V L (fun _ => ∃ V', C.IsDevelopmentIn S L agree V' ∧ V < V')) :
    agree L ∧ C.IsCauchySurfaceOn L S := by
  have hV₀ := isDevelopmentIn_maxDevelopmentIn hglue hG.1 hacausal hLW hloc
  rw [maxDevelopmentIn_eq hglue hG hT hacausal hsplit hK hLW hconn hSL hloc hstay hstep] at hV₀
  exact ⟨hV₀.agree, hV₀.cauchy⟩

/-! ## 4. Theorem 4.75 -/

variable (C) in
/-- **A local development** (ERS Thm 4.75: `u_p : DS_p → ℝ`, a GHD of the data on `S_p`), read
through what Theorem 4.64 uses (as `ers_theorem_4_64`'s hypotheses): `W` globally hyperbolic and
tarentin, `S` acausal in `W`, splitting it, with compact slabs, and a Cauchy surface of `W`.
Supplier: local existence (Sogge) on a `{t = 0}` patch, with `S ∩ DS_p = S_p` (the integral
curves of `N`; `IsCauchySurfaceOn.of_subset_of_isAcausalOn` from `S_p` to `S`). -/
structure IsLocalDevelopment (W : Opens M) (S : Set M) : Prop where
  gh : C.GloballyHyperbolicOn W
  tarentin : C.TarentinOn W
  acausal : C.IsAcausalOn W S
  split : C.SplitBy W S
  slabs : C.CompactSlabs W S
  cauchy : C.IsCauchySurfaceOn W S

variable (C) in
/-- **Theorem 4.64's named inputs located in the region `L` of `W`** (ERS Thm 4.75, for `L` a
component `A` of `DS_p ∩ DS_q` and `W = DS_p`): `L` meets `S` (the integral curves of `N`,
ghd_02_19.tex:1014–1015); local uniqueness on `S ∩ L` (Prop 4.63's input); Step 2's `U₂` half
(`FrontierStaysIn`, the null generator staying in `DS_q`, hence in `A`); Steps 3–5 with
Prop 4.63 (`SliceRestart`, a strictly larger development in `L`). -/
structure RestartsIn (W L : Opens M) (S : Set M) (agree : Opens M → Prop) : Prop where
  meets : (S ∩ L).Nonempty
  localUniq : C.LocalUniqueness (S ∩ L) L agree
  stay : ∀ V, C.IsDevelopmentIn S L agree V → C.FrontierStaysIn W S V L
  step : ∀ V, C.IsDevelopmentIn S L agree V →
    C.SliceRestart W S V L (fun _ => ∃ V', C.IsDevelopmentIn S L agree V' ∧ V < V')

/-- For a point `s`, the slabs `J⁻_W(q) ∩ J⁺_W(s)` and `J⁺_W(q) ∩ J⁻_W(s)` are the diamonds
`J_W(s, q)`, `J_W(q, s)`: compact when `W` is globally hyperbolic. -/
theorem GloballyHyperbolicOn.compactSlabs_singleton {W : Opens M} (hG : C.GloballyHyperbolicOn W)
    (s : M) : C.CompactSlabs W {s} := by
  intro q
  have h₁ : C.Jminus W {q} ∩ C.Jplus W {s} = C.diamond W s q := by
    ext z
    rw [mem_inter_iff, Precausality.mem_Jminus_singleton, Precausality.mem_Jplus_singleton,
      mem_diamond]
    exact and_comm
  have h₂ : C.Jplus W {q} ∩ C.Jminus W {s} = C.diamond W q s := by
    ext z
    rw [mem_inter_iff, Precausality.mem_Jplus_singleton, Precausality.mem_Jminus_singleton,
      mem_diamond]
  exact ⟨h₁ ▸ hG.2 s q, h₂ ▸ hG.2 q s⟩

/-- **A Cauchy surface of every component is a Cauchy surface** of the open `W` (`M` locally
connected and Hausdorff, `≤_W` antisymmetric): an inextensible curve of `W` lies in one component
and is inextensible there. -/
theorem isCauchySurfaceOn_of_componentOpens [T2Space M] [LocallyConnectedSpace M] {W : Opens M}
    (hanti : ∀ ⦃x y : M⦄, C.le W x y → C.le W y x → x = y)
    (h : ∀ x ∈ W, C.IsCauchySurfaceOn (componentOpens W x) S) : C.IsCauchySurfaceOn W S := by
  intro I c hc
  obtain ⟨t₀, ht₀⟩ := hc.1.nonempty
  have hx₀ : c t₀ ∈ W := hc.1.mem ht₀
  have hcA : ∀ t ∈ I, c t ∈ componentOpens W (c t₀) := by
    intro t ht
    have hpre : IsPreconnected (c '' [[t₀, t]]) :=
      isPreconnected_uIcc.image _ (hc.1.continuousOn_uIcc ht₀ ht)
    have hsub : c '' [[t₀, t]] ⊆ (W : Set M) := by
      rintro _ ⟨r, hr, rfl⟩
      exact hc.1.mem (hc.1.ordConnected.uIcc_subset ht₀ ht hr)
    exact hpre.subset_connectedComponentIn ⟨t₀, left_mem_uIcc, rfl⟩ hsub
      ⟨t, right_mem_uIcc, rfl⟩
  have hJ := inextensible_ordConnectedComponent_of_le hanti (componentOpens_le W (c t₀)) hc ht₀
    (mem_componentOpens hx₀)
  have hJI : ordConnectedComponent (I ∩ c ⁻¹' (componentOpens W (c t₀) : Set M)) t₀ = I := by
    haveI := hc.1.ordConnected
    exact Subset.antisymm (fun t ht => (ordConnectedComponent_subset ht).1)
      (subset_ordConnectedComponent ht₀ fun t ht => ⟨ht, hcA t ht⟩)
  rw [hJI] at hJ
  exact h (c t₀) hx₀ I c hJ

/-- **ERS19 Theorem 4.77's union argument without `S ⊆ Uᵢ`**: open sets in each of which, and in
each pairwise intersection of which, `S` is a Cauchy surface, with causal union (`M` Hausdorff),
have `S` as Cauchy surface of the union. `ers_theorem_4_77` is the case `S ⊆ Uᵢ`; the proof is
its own, the step "`c s₁ ∈ Uⱼ`" read off the meeting point in `Uᵢ ∩ Uⱼ` instead of `S ⊆ Uⱼ`. -/
theorem isCauchySurfaceOn_iSup_of_inf [T2Space M] {ι : Type*} (U : ι → Opens M)
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
    have hJi := inextensible_ordConnectedComponent_of_le hcaus (hUW i) hc hs₁ hs₁Ui
    have hrij : c r ∈ U i ⊓ U j := ⟨hseg ⟨hs₁r, le_rfl⟩, hrj⟩
    have hJij :=
      inextensible_ordConnectedComponent_of_le hcaus (inf_le_left.trans (hUW i)) hc hr hrij
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
      exact hcσ ▸ (ordConnectedComponent_subset hσ).2.2
    · exact (hσ' (by rw [uIcc_comm]; exact h')).2.2
  intro I c hc
  obtain ⟨t₀, ht₀⟩ := hc.1.nonempty
  obtain ⟨i₀, hi₀⟩ := Opens.mem_iSup.1 (hc.1.mem ht₀)
  have hJ := inextensible_ordConnectedComponent_of_le hcaus (hUW i₀) hc ht₀ hi₀
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
    have hJi := inextensible_ordConnectedComponent_of_le hcaus (hUW i) hc hs₁ hs₁Ui
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

/-- **ERS19 Theorem 4.75, the claim** (`ersthm:ThmEx`, unmarked): `u_p = u_q` on `DS_p ∩ DS_q`,
and `S` is a Cauchy surface of `DS_p ∩ DS_q` for `g(u_p)`. On each component `A` of
`DS_p ∩ DS_q`: Theorem 4.64's argument in `A` (`ers_theorem_4_64_in`, `W = DS_p`) gives the
agreement on `A` and `S` Cauchy in `A`; agreement is pointwise, and the Cauchy property passes
from the components (`isCauchySurfaceOn_of_componentOpens`).

Hypotheses and suppliers: `hdev` — local existence (Sogge): each `u_p` a GHD of the data on
`S_p` (`IsLocalDevelopment`, T-loc-quasilinear-slice); `hcomp` — for `p ≠ q`, on each component
`A`, Theorem 4.64's named inputs located in `A` (`RestartsIn`: `N`'s integral curves, Prop 4.63,
`FrontierStaysIn`, `SliceRestart`). -/
theorem ers_theorem_4_75_eqOn [T2Space M] [LocallyConnectedSpace M] {ι : Type*} {β : Type v}
    (cau : ι → Causality M) (D : ι → Opens M) (u : ι → M → β)
    (hdev : ∀ i, (cau i).IsLocalDevelopment (D i) S)
    (hcomp : ∀ i j, i ≠ j → ∀ x ∈ D i ⊓ D j,
      (cau i).RestartsIn (D i) (componentOpens (D i ⊓ D j) x) S (fun V => EqOn (u i) (u j) V))
    (i j : ι) :
    EqOn (u i) (u j) (D i ⊓ D j : Opens M) ∧ (cau i).IsCauchySurfaceOn (D i ⊓ D j) S := by
  by_cases hij : i = j
  · subst hij
    rw [inf_idem]
    exact ⟨fun _ _ => rfl, (hdev i).cauchy⟩
  have hanti : ∀ ⦃x y : M⦄, (cau i).le (D i ⊓ D j) x y → (cau i).le (D i ⊓ D j) y x → x = y :=
    fun _ _ h h' =>
      (hdev i).gh.1 ((cau i).le_mono inf_le_left h) ((cau i).le_mono inf_le_left h')
  have hA : ∀ x ∈ D i ⊓ D j, EqOn (u i) (u j) (componentOpens (D i ⊓ D j) x : Set M) ∧
      (cau i).IsCauchySurfaceOn (componentOpens (D i ⊓ D j) x) S := by
    intro x hx
    obtain ⟨hmeet, hloc, hstay, hstep⟩ := hcomp i j hij x hx
    exact ers_theorem_4_64_in (agreementGlues_eqOn (u i) (u j)) (hdev i).gh (hdev i).tarentin
      (hdev i).acausal (hdev i).split (hdev i).slabs ((componentOpens_le _ x).trans inf_le_left)
      isPreconnected_connectedComponentIn hmeet hloc hstay hstep
  exact ⟨fun x hx => (hA x hx).1 (mem_componentOpens hx),
    isCauchySurfaceOn_of_componentOpens hanti fun x hx => (hA x hx).2⟩

/-- **ERS19 Theorem 4.75, causal-topological skeleton** (`ersthm:ThmEx`, unmarked): the local
developments patch. There is `v` with `v = u_p` on every `DS_p`; `S ⊆ U = ⋃ DS_p`; and for every
causality `Cu` agreeing with each `g(u_p)` on the open subsets of `DS_p` (the causality of
`g(v)`, `v` being the patched solution) whose `≤_U` is antisymmetric, `S` is a Cauchy surface of
`U`. GH of `U` is not concluded (OQ-57 (c)).

Hypotheses and suppliers: `hex` — the patches cover `S` (`p ∈ S_p ⊆ DS_p`); `hdev`, `hcomp` as
in `ers_theorem_4_75_eqOn`; `hagreeC` — `g(v) = g(u_p)` on `DS_p`; `hcaus` — strengthened, as in
`ers_theorem_4_77`: part of the printed conclusion (`U` a GHD, `ghd_02_19.tex:1021`, hence causal,
`:814`), assumed here. -/
theorem ers_theorem_4_75 [T2Space M] [LocallyConnectedSpace M] {ι : Type*} {β : Type v}
    [Nonempty β] (cau : ι → Causality M) (D : ι → Opens M) (u : ι → M → β)
    (hex : ∀ p ∈ S, ∃ i, p ∈ D i) (hdev : ∀ i, (cau i).IsLocalDevelopment (D i) S)
    (hcomp : ∀ i j, i ≠ j → ∀ x ∈ D i ⊓ D j,
      (cau i).RestartsIn (D i) (componentOpens (D i ⊓ D j) x) S (fun V => EqOn (u i) (u j) V)) :
    ∃ v : M → β, (∀ i, EqOn v (u i) (D i)) ∧ S ⊆ ((⨆ i, D i : Opens M) : Set M) ∧
      ∀ Cu : Causality M,
        (∀ i, ∀ V : Opens M, V ≤ D i → ∀ x y, (cau i).le V x y ↔ Cu.le V x y) →
        (∀ ⦃x y : M⦄, Cu.le (⨆ i, D i) x y → Cu.le (⨆ i, D i) y x → x = y) →
        Cu.IsCauchySurfaceOn (⨆ i, D i) S := by
  classical
  have hpair := ers_theorem_4_75_eqOn cau D u hdev hcomp
  refine ⟨fun x => if h : ∃ i, x ∈ D i then u h.choose x else Classical.arbitrary β,
    fun i x hx => ?_, fun p hp => ?_, fun Cu hagreeC hcaus => ?_⟩
  · have h : ∃ i, x ∈ D i := ⟨i, hx⟩
    show (if h : ∃ i, x ∈ D i then u h.choose x else Classical.arbitrary β) = u i x
    rw [dif_pos h]
    exact (hpair h.choose i).1 ⟨h.choose_spec, hx⟩
  · obtain ⟨i, hi⟩ := hex p hp
    exact Opens.mem_iSup.2 ⟨i, hi⟩
  · refine isCauchySurfaceOn_iSup_of_inf D hcaus (fun i => ?_) fun i j => ?_
    · exact isCauchySurfaceOn_of_agree (hagreeC i) (hdev i).cauchy
    · exact isCauchySurfaceOn_of_agree (fun V hV => hagreeC i V (hV.trans inf_le_left))
        (hpair i j).2

end Causality

/-! ## 5. Witnesses on the timelike line -/

open Causality in
/-- On the timelike line, `{1}` is a Cauchy surface of `]0, 2[`: the range of
`x ↦ 1 + arctan x / (π/2)` (`timelikeLine_isCauchySurfaceOn_range`). -/
theorem timelikeLine_isCauchySurfaceOn_Ioo_zero_two {U : Opens ℝ} (hU : (U : Set ℝ) = Ioo 0 2) :
    timelikeLine.IsCauchySurfaceOn U {1} := by
  have hπ : 0 < Real.pi / 2 := by positivity
  set c := 1 / (Real.pi / 2) with hc_def
  have hc : 0 < c := div_pos one_pos hπ
  have harctan : IsOpenMap Real.arctan :=
    isOpen_Ioo.isOpenMap_subtype_val.comp Real.tanOrderIso.symm.toHomeomorph.isOpenMap
  have hgo : IsOpenMap (fun x => 1 + c * Real.arctan x) :=
    (Homeomorph.addLeft (1 : ℝ)).isOpenMap.comp
      ((Homeomorph.mulLeft₀ c hc.ne').isOpenMap.comp harctan)
  have hrange : range (fun x => 1 + c * Real.arctan x) = Ioo 0 2 := by
    rw [range_comp' (fun y => 1 + y) (fun x => c * Real.arctan x),
      range_comp' (c * ·) Real.arctan, Real.range_arctan, image_mul_left_Ioo hc,
      image_const_add_Ioo]
    have : c * (Real.pi / 2) = 1 := by rw [hc_def]; field_simp
    rw [mul_neg, this]
    norm_num
  have h := timelikeLine_isCauchySurfaceOn_range (g := fun x => 1 + c * Real.arctan x)
    ((Real.arctan_strictMono.const_mul hc).const_add 1)
    (continuous_const.add (continuous_const.mul Real.continuous_arctan)) hgo
    (hU.trans hrange.symm)
  simpa [Real.arctan_zero] using h

open Causality in
/-- **The acausality of `S` cannot be dropped from the union lemma**
(`isCauchySurfaceOn_sSup_of_isAcausalOn`; nor "`S` Cauchy in an ambient `B`" from
`isCauchySurfaceOn_sSup_of_curvesExtendOn`): on the timelike line (causal, Hausdorff, curves
extending), `{0}` is a Cauchy surface of `]-1, 1[` and `{1}` one of `]0, 2[`, both pieces of
`S = {0, 1}`, and `S` is not a Cauchy surface of their union `]-1, 2[`: the inextensible curve
of `]-1, 2[` through the segment `[0, 1]` meets `S` twice. This is what the ambient `U₁` of
Prop 4.63 provides and what Theorem 4.75 has to replace (here `]-1, 1[ ∩ ]0, 2[` misses `S`:
`RestartsIn.meets` fails). -/
theorem timelikeLine_not_isCauchySurfaceOn_union :
    timelikeLine.IsCauchySurfaceOn ⟨Ioo (-1) 1, isOpen_Ioo⟩ {0} ∧
      timelikeLine.IsCauchySurfaceOn ⟨Ioo 0 2, isOpen_Ioo⟩ {1} ∧
      ¬ timelikeLine.IsCauchySurfaceOn
        ((⟨Ioo (-1) 1, isOpen_Ioo⟩ : Opens ℝ) ⊔ ⟨Ioo 0 2, isOpen_Ioo⟩) {0, 1} := by
  refine ⟨timelikeLine_isCauchySurfaceOn_Ioo one_pos rfl,
    timelikeLine_isCauchySurfaceOn_Ioo_zero_two rfl, fun hS => ?_⟩
  have hmem : ∀ t ∈ Icc (0 : ℝ) 1,
      id t ∈ ((⟨Ioo (-1) 1, isOpen_Ioo⟩ : Opens ℝ) ⊔ ⟨Ioo 0 2, isOpen_Ioo⟩) := fun t ht => by
    rcases eq_or_lt_of_le ht.1 with h | h
    · exact Opens.mem_sup.2 (Or.inl (show t ∈ Ioo (-1 : ℝ) 1 by
        rw [← h]; exact ⟨by norm_num, by norm_num⟩))
    · exact Opens.mem_sup.2 (Or.inr (show t ∈ Ioo (0 : ℝ) 2 from ⟨h, by linarith [ht.2]⟩))
  have hseg : timelikeLine.CausalCurveOn
      ((⟨Ioo (-1) 1, isOpen_Ioo⟩ : Opens ℝ) ⊔ ⟨Ioo 0 2, isOpen_Ioo⟩) id 0 1 :=
    CurveOn.restrict (timelikeLine_causalCurveOn_id 0 1) le_rfl le_rfl le_top hmem
  have hext : timelikeLine.CurvesExtendOn
      ((⟨Ioo (-1) 1, isOpen_Ioo⟩ : Opens ℝ) ⊔ ⟨Ioo 0 2, isOpen_Ioo⟩) :=
    curvesExtendOn_of_timeFunction continuous_id
      (fun _ _ h hne => lt_of_le_of_ne (timelikeLine_le.1 h).1 hne) _
  obtain ⟨I, c, hc, hsub⟩ := hext id 0 1 zero_le_one hseg
  obtain ⟨_, -, huniq⟩ := hS I c hc
  have h0 : (0 : ℝ) ∈ c '' I ∩ {0, 1} :=
    ⟨hsub ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩, Or.inl rfl⟩
  have h1 : (1 : ℝ) ∈ c '' I ∩ {0, 1} :=
    ⟨hsub ⟨1, ⟨zero_le_one, le_rfl⟩, rfl⟩, Or.inr rfl⟩
  have h01 := (huniq _ h0).trans (huniq _ h1).symm
  norm_num at h01

open Causality in
/-- **A proper instance of `ers_prop_4_63_globallyHyperbolicOn`**: on the timelike line, `U₁ = ℝ`,
`U₂ = ]-1, 1[`, `S = {0}`, `u₁ = id`, `u₂` the clamp to `[-1, 1]`; local uniqueness by
`DS_0 = ]-1/2, 1/2[`. The union of the local developments is a common development, globally
hyperbolic. -/
theorem timelikeLine_ers_prop_4_63 :
    ∃ V : Opens ℝ, timelikeLine.IsCommonDevelopment {0} ⊤ ⟨Ioo (-1) 1, isOpen_Ioo⟩
        (fun V => EqOn (id : ℝ → ℝ) (fun x => max (-1) (min x 1)) V) V ∧
      timelikeLine.GloballyHyperbolicOn V := by
  have hloc : timelikeLine.LocalUniqueness ({0} : Set ℝ) (⊤ ⊓ ⟨Ioo (-1) 1, isOpen_Ioo⟩)
      (fun V => EqOn (id : ℝ → ℝ) (fun x => max (-1) (min x 1)) V) := by
    rintro p rfl
    refine ⟨⟨Ioo (-(1 / 2)) (1 / 2), isOpen_Ioo⟩, show (0 : ℝ) ∈ Ioo (-(1 / 2)) (1 / 2) by
      constructor <;> norm_num, fun x hx => Opens.mem_inf.2 ⟨trivial,
      show x ∈ Ioo (-1 : ℝ) 1 from ⟨by linarith [hx.1], by linarith [hx.2]⟩⟩,
      fun x hx => ?_, {0}, subset_rfl, timelikeLine_isCauchySurfaceOn_Ioo one_half_pos rfl⟩
    obtain ⟨h1, h2⟩ := hx
    simp [min_eq_left (by linarith : x ≤ 1), max_eq_right (by linarith : (-1 : ℝ) ≤ x)]
  obtain ⟨h1, h2, -⟩ := ers_prop_4_63_globallyHyperbolicOn (agreementGlues_eqOn _ _)
    timelikeLine_globallyHyperbolic timelikeLine_isCauchySurface_zero
    timelikeLine_causallyArcConnected (curvesExtendOn_top.2 timelikeLine_curvesExtend) hloc
  exact ⟨_, h1, h2⟩

open Causality in
/-- The timelike line is a local development of `{0}` on `ℝ`, in the sense of Theorem 4.64's
inputs. -/
theorem timelikeLine_isLocalDevelopment_top :
    timelikeLine.IsLocalDevelopment ⊤ ({0} : Set ℝ) where
  gh := timelikeLine_globallyHyperbolic
  tarentin := tarentinOn_top.2 timelikeLine_tarentin
  acausal := by
    intro x hx y hy _
    rw [mem_singleton_iff] at hx hy
    rw [hx, hy]
  split := by
    intro q _
    rcases le_total 0 q with h | h
    · exact Or.inl ⟨0, rfl, timelikeLine_le_top.2 h⟩
    · exact Or.inr ⟨0, rfl, timelikeLine_le_top.2 h⟩
  slabs := GloballyHyperbolicOn.compactSlabs_singleton timelikeLine_globallyHyperbolic 0
  cauchy := timelikeLine_isCauchySurface_zero

/-- The interval `]-1, 1[` as an open set of `ℝ`. -/
def ersWitnessIoo : Opens ℝ := ⟨Ioo (-1) 1, isOpen_Ioo⟩

theorem mem_ersWitnessIoo {x : ℝ} : x ∈ ersWitnessIoo ↔ x ∈ Ioo (-1 : ℝ) 1 := Iff.rfl

open Causality in
/-- The timelike line on `]-1, 1[` is a local development of `{0}`. -/
theorem timelikeLine_isLocalDevelopment_ersWitnessIoo :
    timelikeLine.IsLocalDevelopment ersWitnessIoo ({0} : Set ℝ) where
  gh := timelikeLine_globallyHyperbolicOn _
  tarentin := by
    intro x hx N hN
    obtain ⟨l, u, ⟨hl, hu⟩, hlu⟩ :=
      mem_nhds_iff_exists_Ioo_subset.1 (inter_mem hN (ersWitnessIoo.isOpen.mem_nhds hx))
    refine ⟨(l + x) / 2, (hlu ⟨by linarith, by linarith⟩).1, (x + u) / 2,
      (hlu ⟨by linarith, by linarith⟩).1, ?_⟩
    show x ∈ interior (timelikeLine.diamond ersWitnessIoo ((l + x) / 2) ((x + u) / 2))
    refine interior_maximal (t := Ioo ((l + x) / 2) ((x + u) / 2)) (fun z hz => ?_) isOpen_Ioo
      ⟨by linarith, by linarith⟩
    rw [mem_diamond, timelikeLine_le, timelikeLine_le]
    exact ⟨⟨hz.1.le, fun w hw => (hlu ⟨by linarith [hw.1], by linarith [hw.2, hz.2]⟩).2⟩,
      hz.2.le, fun w hw => (hlu ⟨by linarith [hw.1, hz.1], by linarith [hw.2]⟩).2⟩
  acausal := by
    intro x hx y hy _
    rw [mem_singleton_iff] at hx hy
    rw [hx, hy]
  split := by
    intro q hq
    have hq' : q ∈ Ioo (-1 : ℝ) 1 := hq
    rcases le_total 0 q with h | h
    · exact Or.inl ⟨0, rfl, timelikeLine_le.2 ⟨h, fun w hw =>
        mem_ersWitnessIoo.2 ⟨by linarith [hw.1], hw.2.trans_lt hq'.2⟩⟩⟩
    · exact Or.inr ⟨0, rfl, timelikeLine_le.2 ⟨h, fun w hw =>
        mem_ersWitnessIoo.2 ⟨hq'.1.trans_le hw.1, by linarith [hw.2]⟩⟩⟩
  slabs := GloballyHyperbolicOn.compactSlabs_singleton (timelikeLine_globallyHyperbolicOn _) 0
  cauchy := timelikeLine_isCauchySurfaceOn_Ioo one_pos rfl

open Causality in
/-- Theorem 4.64's inputs located in `]-1, 1[`, inside any `W ⊇ ]-1, 1[`, for solutions agreeing
on every open subset of `]-1, 1[`. -/
theorem timelikeLine_restartsIn_ersWitnessIoo {W : Opens ℝ} {agree : Opens ℝ → Prop}
    (hag : ∀ V : Opens ℝ, (V : Set ℝ) ⊆ Ioo (-1) 1 → agree V) :
    timelikeLine.RestartsIn W ersWitnessIoo ({0} : Set ℝ) agree where
  meets := ⟨0, rfl, mem_ersWitnessIoo.2 ⟨by norm_num, by norm_num⟩⟩
  localUniq := fun _ hp => ⟨ersWitnessIoo, hp.2, le_rfl, hag _ subset_rfl, {0},
    fun z hz => ⟨hz, by
      rw [mem_singleton_iff.1 hz]; exact mem_ersWitnessIoo.2 ⟨by norm_num, by norm_num⟩⟩,
    timelikeLine_isCauchySurfaceOn_Ioo one_pos rfl⟩
  stay := by
    intro V _ q hq
    have hq' : q ∈ Ioo (-1 : ℝ) 1 := hq.2
    refine ⟨fun _ z hz => ?_, fun _ z hz => ?_⟩
    · obtain ⟨⟨hzq, ⟨_, rfl, h0z⟩⟩, -⟩ := hz
      rw [Precausality.mem_Jminus_singleton, timelikeLine_le] at hzq
      rw [timelikeLine_le] at h0z
      exact mem_ersWitnessIoo.2 ⟨by linarith [h0z.1], hzq.1.trans_lt hq'.2⟩
    · obtain ⟨⟨hqz, ⟨_, rfl, hz0⟩⟩, -⟩ := hz
      rw [Precausality.mem_Jplus_singleton, timelikeLine_le] at hqz
      rw [timelikeLine_le] at hz0
      exact mem_ersWitnessIoo.2 ⟨hq'.1.trans_le hqz.1, by linarith [hz0.1]⟩
  step := by
    intro V hV p hp _
    refine ⟨ersWitnessIoo, ⟨le_rfl, inter_subset_right, hag _ subset_rfl,
      timelikeLine_isCauchySurfaceOn_Ioo one_pos rfl⟩, lt_of_le_of_ne hV.le fun hVeq => ?_⟩
    have hpV : p ∈ (V : Set ℝ) := by rw [hVeq]; exact hp.2
    have := hp.1
    rw [V.isOpen.frontier_eq] at this
    exact this.2 hpV

/-- The two patches of the 4.75 witness: `ℝ` and `]-1, 1[`. -/
def ersWitnessPatches : Bool → Opens ℝ := fun b => cond b ⊤ ersWitnessIoo

/-- The two local solutions of the 4.75 witness: `id` on `ℝ`, the clamp to `[-1, 1]` on
`]-1, 1[`. -/
def ersWitnessSolutions : Bool → ℝ → ℝ := fun b => cond b id fun x => max (-1) (min x 1)

open Causality in
/-- **A proper instance of `ers_theorem_4_75`**: on the timelike line, `S = {0}`, two local
developments, `u = id` on `ℝ` and `u = ` the clamp on `]-1, 1[`. Their overlap `]-1, 1[` is one
component; there `maxDevelopmentIn_eq` applies (`RestartsIn` holds by the geometry of the line, its
restart branch never entered) and the two solutions agree; they patch to `v` on `ℝ`, of which `{0}` is a Cauchy
surface for every causality agreeing with the timelike line and causal on `ℝ`. -/
theorem timelikeLine_ers_theorem_4_75 :
    ∃ v : ℝ → ℝ, (∀ b, EqOn v (ersWitnessSolutions b) (ersWitnessPatches b)) ∧
      ({0} : Set ℝ) ⊆ ((⨆ b, ersWitnessPatches b : Opens ℝ) : Set ℝ) ∧
      ∀ Cu : Causality ℝ,
        (∀ b, ∀ V : Opens ℝ, V ≤ ersWitnessPatches b → ∀ x y,
          timelikeLine.le V x y ↔ Cu.le V x y) →
        (∀ ⦃x y : ℝ⦄, Cu.le (⨆ b, ersWitnessPatches b) x y →
          Cu.le (⨆ b, ersWitnessPatches b) y x → x = y) →
        Cu.IsCauchySurfaceOn (⨆ b, ersWitnessPatches b) {0} := by
  have hclamp : ∀ V : Opens ℝ, (V : Set ℝ) ⊆ Ioo (-1) 1 →
      EqOn (id : ℝ → ℝ) (fun x => max (-1) (min x 1)) V := fun V hV x hx => by
    obtain ⟨h1, h2⟩ := hV hx
    simp [min_eq_left h2.le, max_eq_right h1.le]
  have hinter : ∀ i j : Bool, i ≠ j →
      ((ersWitnessPatches i ⊓ ersWitnessPatches j : Opens ℝ) : Set ℝ) = Ioo (-1) 1 := by
    intro i j hij
    cases i <;> cases j <;> simp_all [ersWitnessPatches, ersWitnessIoo]
  refine Causality.ers_theorem_4_75 (fun _ => timelikeLine) ersWitnessPatches ersWitnessSolutions
    (fun _ _ => ⟨true, trivial⟩) (fun b => ?_) fun i j hij x hx => ?_
  · cases b
    · exact timelikeLine_isLocalDevelopment_ersWitnessIoo
    · exact timelikeLine_isLocalDevelopment_top
  · have hA : componentOpens (ersWitnessPatches i ⊓ ersWitnessPatches j) x = ersWitnessIoo := by
      rw [componentOpens_eq_self (by rw [hinter i j hij]; exact isPreconnected_Ioo) hx]
      exact SetLike.coe_injective (hinter i j hij)
    rw [hA]
    refine timelikeLine_restartsIn_ersWitnessIoo fun V hV => ?_
    cases i <;> cases j
    · exact absurd rfl hij
    · exact (hclamp V hV).symm
    · exact hclamp V hV
    · exact absurd rfl hij

end Causal
