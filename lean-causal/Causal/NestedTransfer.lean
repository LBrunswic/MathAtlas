import Causal.NestedCausalities
import Causal.LadderLocal
import Causal.CurvesExtend

/-!
# What a ≤-nesting carries to the narrower causality: strong causality and time functions do, tarentin does not

Programme target `T-abs-nested-transfer` (`programme/roadmap.toml:552`; layer 1, no label of
`ETT.tex`; ETT-layer imports only, no model, no metric notion). `C` is the narrower causality,
`C'` the wider: `LeNested C C'` (`Causal/NestedCausalities.lean:121`).

**`T-abs-nested-transfer/1-strongly-causal`** — `LeNested.stronglyCausal`; principal form
`stronglyCausal_of_le_top`, through `CausallyConvexIn.of_le`.
**`T-abs-nested-transfer/2-strongly-causal-open`** — `LeNested.stronglyCausalOpen`; principal form
`stronglyCausalOpen_of_le_top`.
**`T-abs-nested-transfer/3-time-function`** — `LeNested.hasTimeFunction`; principal form
`hasTimeFunction_of_le_top`.
**`T-abs-nested-transfer/4-tarentin`** — `spacelikeLine_leNested_timelikeLine`,
`spacelikeLine_not_tarentin`, `spacelikeLine_separates_tarentin`, `not_tarentin_of_leNested_bare`;
in one statement with the ladder properties of both lines, `leNested_tarentin_counterexample`.
Beyond the target: tarentin passes the other way, to the wider causality
(`LeNested.tarentin_wider`); `LeNested.isCausal`; `spacelikeLine_separates_tarentin_full`.

> What a ≤-nesting carries to the narrower causality: strong causality and its open form pass from
> the wider C' to the narrower C (LeNested C C'), and so does a time function
> (C'.HasTimeFunction → C.HasTimeFunction); tarentin does not: the spacelike line, ≤-nested in the
> timelike line, is not tarentin (spacelikeLine_not_tarentin), conjoined with its push-up, causal
> openness and global hyperbolicity (spacelikeLine_separates_tarentin, the first globally
> hyperbolic model that is not tarentin) (`programme/roadmap.toml:553`)

> A causally convex set for C' is causally convex for C (its ≤ is smaller), whence SC and SCO; a
> time function of C' is one of C. […] Causal.spacelikeLine (≤ the diagonal, Causal/Lines.lean:113)
> is ≤-nested in Causal.timelikeLine […] and is not tarentin (each of its diamonds is at most a
> point, of empty interior) (`programme/roadmap.toml:562`)

## Hypothesis checklist

| target hypothesis | here |
|---|---|
| 1–3: `LeNested C C'` (`≤_U` nested for every open `U`) | ⚠ weakened in the principal forms: `≤` nested at `M` only (`∀ x y, C.le ⊤ x y → C'.le ⊤ x y`), the hypothesis of `isCausal_of_le_top`; the `LeNested.*` forms, which the ladder cites, are their corollaries. `CausallyConvexIn.of_le` asks `≤_U` nested at the one open `U` |
| 1: `C'` strongly causal | ✓ carried |
| 2: `C'` strongly causal, open form | ✓ carried |
| 3: `C'.HasTimeFunction` | ✓ carried; the time function of `C` is the same `T` |
| 4: the spacelike line `≤`-nested in the timelike line, not tarentin; push-up, causal openness, GH | ✓ each proved; the library's `spacelikeLine_pushUp`, `spacelikeLine_causallyOpen`, `spacelikeLine_globallyHyperbolic` reused |

## SCOPE (disclosed)

* **No separation, no countability**: no instance on `M` beyond its topology; the counterexample
  lives on `ℝ` (Hausdorff, second countable), one of ETT's spacetimes.
* **The transfers read `≤` only.** Strong causality (both forms) asks causally convex
  neighbourhoods, and a diamond of `C` lies in the diamond of `C'` with the same vertices
  (`diamond_subset_of_le`); a time function asks strict increase along `≤_M`. `≪` is not read, so
  `LtNested` is not asked. ETT's own time function `IsTimeFunction` (`defi:fonction_temps`, a strong
  morphism to the timelike line, `Causal/Morphism.lean:832`) carries `≪` and is not treated here;
  it is incomparable with `HasTimeFunction` (kb/0065).
* **Tarentin goes up, not down.** An open diamond of `C` lies in the open diamond of `C'`
  (`interior_mono`), so tarentin passes from the narrower to the wider causality
  (`Tarentin.wider_of_le_top`, `LeNested.tarentin_wider`) and not conversely
  (`not_tarentin_of_leNested_bare`). The other direction of 1–3 (to the wider causality) is not
  treated.
* **Why the spacelike line fails**: every diamond `J_U(p, q)` lies in `{p}`
  (`spacelikeLine_diamond_subset`), and `ℝ` has no isolated point, so every open diamond is empty
  (`spacelikeLine_openDiamond`, mathlib's `interior_singleton`).
* **Its other ladder properties**, for the separations: strongly causal in both forms
  (`spacelikeLine_stronglyCausalOpen`, `spacelikeLine_stronglyCausal`: every subset is causally
  convex, `spacelikeLine_causallyConvexIn`), absolutely minimal
  (`spacelikeLine_absolutelyMinimal`), with a time function (`spacelikeLine_hasTimeFunction`,
  `id`). Its causal arc-connectedness is not stated here: it is T-abs-nested-converse's
  (`scaffold/CausalScaffold/NestedConverse.lean`), a module this one does not import. The timelike
  line's open strong causality and time function are stated for the conjoined counterexample
  (`timelikeLine_stronglyCausalOpen`, `timelikeLine_hasTimeFunction`).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Filter

universe u

variable {M : Type u} [TopologicalSpace M]

namespace Causality

variable {C C' : Causality M} {U : Opens M}

/-! ## 1. Strong causality passes to the narrower causality -/

/-- **A set causally convex for the wider causality is causally convex for the narrower one**, in
any open `U`: the narrower diamonds `J_U(p, q)` lie in the wider ones. Only `≤_U` is asked
nested. -/
theorem CausallyConvexIn.of_le {V : Set M} (hle : ∀ x y, C.le U x y → C'.le U x y)
    (h : C'.CausallyConvexIn V U) : C.CausallyConvexIn V U :=
  ⟨h.1, fun p hp q hq => (diamond_subset_of_le hle p q).trans (h.2 p hp q hq)⟩

/-- **Strong causality passes from the wider to the narrower causality**, `≤` nested at `M`
only. -/
theorem stronglyCausal_of_le_top (hle : ∀ x y, C.le ⊤ x y → C'.le ⊤ x y)
    (h : C'.StronglyCausal) : C.StronglyCausal := fun p N hN =>
  let ⟨V, hV, hVN, hconv⟩ := h p N hN
  ⟨V, hV, hVN, hconv.of_le hle⟩

/-- **Strong causality passes along a ≤-nesting**, from the wider `C'` to the narrower `C`: the
ladder's transfer of `strongly_causal` along `le_nested`, `to_narrower`. -/
theorem LeNested.stronglyCausal (h : LeNested C C') (h' : C'.StronglyCausal) :
    C.StronglyCausal :=
  stronglyCausal_of_le_top (fun _ _ hxy => h hxy) h'

/-! ## 2. The open form of strong causality passes to the narrower causality -/

/-- **The open form of strong causality passes from the wider to the narrower causality**, `≤`
nested at `M` only. -/
theorem stronglyCausalOpen_of_le_top (hle : ∀ x y, C.le ⊤ x y → C'.le ⊤ x y)
    (h : C'.StronglyCausalOpen) : C.StronglyCausalOpen := fun p N hN =>
  let ⟨V, hpV, hVN, hconv⟩ := h p N hN
  ⟨V, hpV, hVN, hconv.of_le hle⟩

/-- **The open form of strong causality passes along a ≤-nesting**: the ladder's transfer of
`strongly_causal_open` along `le_nested`, `to_narrower`. -/
theorem LeNested.stronglyCausalOpen (h : LeNested C C') (h' : C'.StronglyCausalOpen) :
    C.StronglyCausalOpen :=
  stronglyCausalOpen_of_le_top (fun _ _ hxy => h hxy) h'

/-! ## 3. A time function passes to the narrower causality -/

/-- **A time function of the wider causality is one of the narrower**, `≤` nested at `M` only:
the same `T`, strictly increasing along the smaller `≤_M`. -/
theorem hasTimeFunction_of_le_top (hle : ∀ x y, C.le ⊤ x y → C'.le ⊤ x y)
    (h : C'.HasTimeFunction) : C.HasTimeFunction :=
  let ⟨T, hTc, hT⟩ := h
  ⟨T, hTc, fun x y hxy hne => hT x y (hle x y hxy) hne⟩

/-- **A time function passes along a ≤-nesting**: the ladder's transfer of `time_function` along
`le_nested`, `to_narrower`. -/
theorem LeNested.hasTimeFunction (h : LeNested C C') (h' : C'.HasTimeFunction) :
    C.HasTimeFunction :=
  hasTimeFunction_of_le_top (fun _ _ hxy => h hxy) h'

/-- **Causality passes along a ≤-nesting**, from the wider to the narrower causality:
`isCausal_of_le_top` (`Causal.NestedCausalities`) read through `LeNested`, the form of the three
transfers above. -/
theorem LeNested.isCausal (h : LeNested C C') (h' : C'.IsCausal) : C.IsCausal :=
  isCausal_of_le_top (fun _ _ hxy => h hxy) h'

/-! ## 4. Tarentin passes the other way, to the wider causality -/

/-- **Tarentin passes from the narrower to the wider causality**, `≤` nested at `M` only: an open
diamond `Int J(p, q)` of `C` lies in the open diamond `Int J(p, q)` of `C'`. -/
theorem Tarentin.wider_of_le_top (hle : ∀ x y, C.le ⊤ x y → C'.le ⊤ x y) (h : C.Tarentin) :
    C'.Tarentin := fun x N hN =>
  let ⟨p, hp, q, hq, hx⟩ := h x N hN
  ⟨p, hp, q, hq, interior_mono (diamond_subset_of_le hle p q) hx⟩

/-- **Tarentin passes along a ≤-nesting to the wider causality**: the ladder's transfer of
`tarentin` along `le_nested`, `to_wider`. -/
theorem LeNested.tarentin_wider (h : LeNested C C') (hC : C.Tarentin) : C'.Tarentin :=
  hC.wider_of_le_top fun _ _ hxy => h hxy

end Causality

/-! ## 5. Tarentin does not pass to the narrower causality: the spacelike line -/

/-- **The spacelike line is ≤-nested in the timelike line**: `x = y ∈ U` gives `x ≤ y` and
`[x, y] = {x} ⊆ U`. -/
theorem spacelikeLine_leNested_timelikeLine : spacelikeLine.LeNested timelikeLine := by
  rintro U x y ⟨rfl, hx⟩
  exact ⟨le_rfl, by simpa using hx⟩

/-- Every diamond of the spacelike line lies in its lower vertex. -/
theorem spacelikeLine_diamond_subset (U : Opens ℝ) (p q : ℝ) :
    spacelikeLine.diamond U p q ⊆ {p} :=
  fun _ hz => (Causality.mem_diamond.1 hz).1.1.symm

/-- Every open diamond of the spacelike line is empty: `Int J_U(p, q) ⊆ Int {p} = ∅`. -/
theorem spacelikeLine_openDiamond (U : Opens ℝ) (p q : ℝ) :
    spacelikeLine.openDiamond U p q = ∅ :=
  eq_empty_of_subset_empty
    ((interior_mono (spacelikeLine_diamond_subset U p q)).trans (interior_singleton p).subset)

/-- **The spacelike line is not tarentin**: each diamond `J(p, q)` lies in `{p}`, whose interior
in `ℝ` is empty, so no open diamond contains a point. -/
theorem spacelikeLine_not_tarentin : ¬ spacelikeLine.Tarentin := fun h => by
  obtain ⟨p, -, q, -, hx⟩ := h 0 univ univ_mem
  rw [spacelikeLine_openDiamond] at hx
  exact hx

/-- **Tarentin is not implied** by push-up, causal openness and global hyperbolicity together: the
spacelike line, the first model of the library proved globally hyperbolic and not tarentin. -/
theorem spacelikeLine_separates_tarentin :
    spacelikeLine.PushUp ∧ spacelikeLine.CausallyOpen ∧ spacelikeLine.GloballyHyperbolic ∧
      ¬ spacelikeLine.Tarentin :=
  ⟨spacelikeLine_pushUp, spacelikeLine_causallyOpen, spacelikeLine_globallyHyperbolic,
    spacelikeLine_not_tarentin⟩

/-- **Tarentin does not pass along a ≤-nesting to the narrower causality**: the spacelike line is
≤-nested in the tarentin timelike line and is not tarentin. -/
theorem not_tarentin_of_leNested_bare :
    ¬ ∀ C C' : Causality ℝ, C.LeNested C' → C'.Tarentin → C.Tarentin :=
  fun h => spacelikeLine_not_tarentin
    (h _ _ spacelikeLine_leNested_timelikeLine timelikeLine_tarentin)

/-! ### The ladder properties of the two lines, for the separations -/

/-- Every subset of the spacelike line is causally convex in `M`: its diamonds lie in their lower
vertex. -/
theorem spacelikeLine_causallyConvexIn (V : Set ℝ) : spacelikeLine.CausallyConvexIn V ⊤ :=
  ⟨fun _ _ => trivial, fun a ha b _ =>
    (spacelikeLine_diamond_subset ⊤ a b).trans (singleton_subset_iff.2 ha)⟩

/-- The spacelike line is strongly causal in the open form: every open neighbourhood is causally
convex. -/
theorem spacelikeLine_stronglyCausalOpen : spacelikeLine.StronglyCausalOpen := fun _ N hN =>
  ⟨⟨interior N, isOpen_interior⟩, mem_interior_iff_mem_nhds.2 hN, interior_subset,
    spacelikeLine_causallyConvexIn _⟩

/-- The spacelike line is strongly causal. -/
theorem spacelikeLine_stronglyCausal : spacelikeLine.StronglyCausal :=
  spacelikeLine_stronglyCausalOpen.stronglyCausal

/-- The spacelike line has a time function, `id`, vacuously strictly increasing along `≤_M`. -/
theorem spacelikeLine_hasTimeFunction : spacelikeLine.HasTimeFunction :=
  ⟨id, continuous_id, fun _ _ h hne => absurd h.1 hne⟩

/-- The spacelike line is absolutely minimal: `x ≤_V x` is localised in any member of a cover
containing `x`, and `≪` is empty. -/
theorem spacelikeLine_absolutelyMinimal : spacelikeLine.AbsolutelyMinimal := by
  refine Precausality.absolutelyMinimal_iff.2 fun S hS V _ x y => ⟨fun h => ?_, fun h => h.elim⟩
  obtain ⟨O, hO, hxO⟩ := hS x trivial
  exact Relation.TransGen.single ⟨O, hO, h.1, h.2, hxO⟩

/-- The timelike line is strongly causal in the open form (`StronglyCausal.stronglyCausalOpen`:
tarentin and causally open). -/
theorem timelikeLine_stronglyCausalOpen : timelikeLine.StronglyCausalOpen :=
  timelikeLine_stronglyCausal.stronglyCausalOpen timelikeLine_tarentin
    timelikeLine_causallyOpen_of_chronalNeighbours

/-- The timelike line has a time function, `id`. -/
theorem timelikeLine_hasTimeFunction : timelikeLine.HasTimeFunction :=
  ⟨id, continuous_id, fun _ _ h hne => lt_of_le_of_ne h.1 hne⟩

/-- **Tarentin is not implied** by global hyperbolicity, the open form of strong causality,
push-up, causal openness, absolute minimality and a time function together: the spacelike line.
Through the ladder's edges also is_causal, causally_compact, strongly_causal, causally_open_future,
the local forms and curves_extend ⇏ tarentin. -/
theorem spacelikeLine_separates_tarentin_full :
    spacelikeLine.GloballyHyperbolic ∧ spacelikeLine.StronglyCausalOpen ∧ spacelikeLine.PushUp ∧
      spacelikeLine.CausallyOpen ∧ spacelikeLine.AbsolutelyMinimal ∧
      spacelikeLine.HasTimeFunction ∧ ¬ spacelikeLine.Tarentin :=
  ⟨spacelikeLine_globallyHyperbolic, spacelikeLine_stronglyCausalOpen, spacelikeLine_pushUp,
    spacelikeLine_causallyOpen, spacelikeLine_absolutelyMinimal, spacelikeLine_hasTimeFunction,
    spacelikeLine_not_tarentin⟩

/-- **The counterexample to the transfer of tarentin to the narrower causality, in one
statement**: the spacelike line is ≤-nested in the timelike line; the wider timelike line is
tarentin, globally hyperbolic, strongly causal (open form), causally open, causally plain,
causally arc-connected, with push-up, chronal neighbours and a time function; the narrower
spacelike line is globally hyperbolic, strongly causal (open form), causally open, absolutely
minimal, with push-up and a time function, and is not tarentin. So no combination of these
properties of either line makes tarentin pass to the narrower causality. -/
theorem leNested_tarentin_counterexample :
    spacelikeLine.LeNested timelikeLine ∧
      (timelikeLine.Tarentin ∧ timelikeLine.GloballyHyperbolic ∧
        timelikeLine.StronglyCausalOpen ∧ timelikeLine.PushUp ∧ timelikeLine.CausallyOpen ∧
        timelikeLine.CausallyPlain ∧ timelikeLine.ChronalNeighbours ∧
        timelikeLine.CausallyArcConnected ∧ timelikeLine.HasTimeFunction) ∧
      (spacelikeLine.GloballyHyperbolic ∧ spacelikeLine.StronglyCausalOpen ∧
        spacelikeLine.PushUp ∧ spacelikeLine.CausallyOpen ∧ spacelikeLine.AbsolutelyMinimal ∧
        spacelikeLine.HasTimeFunction) ∧
      ¬ spacelikeLine.Tarentin :=
  ⟨spacelikeLine_leNested_timelikeLine,
    ⟨timelikeLine_tarentin, timelikeLine_globallyHyperbolic, timelikeLine_stronglyCausalOpen,
      timelikeLine_pushUp, timelikeLine_causallyOpen_of_chronalNeighbours,
      timelikeLine_causallyPlain, timelikeLine_chronalNeighbours,
      timelikeLine_causallyArcConnected, timelikeLine_hasTimeFunction⟩,
    ⟨spacelikeLine_globallyHyperbolic, spacelikeLine_stronglyCausalOpen, spacelikeLine_pushUp,
      spacelikeLine_causallyOpen, spacelikeLine_absolutelyMinimal,
      spacelikeLine_hasTimeFunction⟩,
    spacelikeLine_not_tarentin⟩

end Causal
