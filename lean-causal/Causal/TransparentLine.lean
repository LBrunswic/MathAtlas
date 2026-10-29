import Causal.Lines

/-!
# A line with a transparent point: absolute minimality is not hereditary

**`cexemple:point_transparent`** — `ETT.tex:472`.
`rem:minimalite_non_hereditaire` — `ETT.tex:485`.

> Endow $M=\RR$ with the following causality: for $\W$ open and $x,y\in \W$,
> $$x\leq_\W y \iff x\leq y \text{ and } [x,y]\subset \W\cup\{0\}, \qquad
>   x\ll_\W y \iff x< y \text{ and } [x,y]\subset \W\cup\{0\},$$
> that is, the timelike line except that the point $0$ is \emph{transparent} […]
> This is a topological spacetime, and it is even causally plain. […]
> It is absolutely minimal on $\RR$. […]
> Its restriction to the open subset $\U:=\RR\setminus\{0\}$ is \emph{not} absolutely minimal.

> The obstruction is structural. For $\U$ open and $\mathcal O$ an open cover of $M$, restriction
> commutes with generation: $\mathrm{Gen}(\mathcal O,P)|_\U=\mathrm{Gen}(\mathcal O|_\U,P|_\U)$,
> where $\mathcal O|_\U=(\O_a\cap \U)_a$. So the covers of $\U$ reachable from covers of $M$ are
> the ones refined by some trace $\mathcal O|_\U$; quantifying over arbitrarily fine covers of
> $\U$ this forces $\overline\U\cap(M\setminus \U)=\emptyset$, i.e. $\U$ clopen. Absolute
> minimality is hereditary only for clopen subsets.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `cexemple:point_transparent`: `M = ℝ`, the relations above | ✓ carried (`transparentLine`) |
| — "for `W` open and `x, y ∈ W`" | ✓ carried: `x ∈ W ∧ y ∈ W` is part of both relations |
| `rem:minimalite_non_hereditaire`, "restriction commutes with generation" | ✓ carried, for any precausality on any space (`generated_restrict_le`, `generated_restrict_lt`) |
| — "hereditary only for clopen subsets", the direction *clopen ⇒ hereditary* | ✓ proved, ⚠ weakened: `U` closed in `M` (it is open), absolute minimality asked on any open `W ⊇ U` (`Precausality.AbsolutelyMinimalOn.of_isClosed`) |

## SCOPE (disclosed)

* `cexemple:point_transparent` is certified in full: the relations form a causality
  (`transparentLine`), which is causally plain (`transparentLine_causallyPlain`), absolutely
  minimal (`transparentLine_absolutelyMinimal`), and whose restriction to `ℝ ∖ {0}` is not
  absolutely minimal (`transparentLine_not_absolutelyMinimalOn`), by the paper's cover and the
  paper's `W`. The paper's "equivalently, … the same connected component of `W ∪ {0}`" is
  `transparentLine_le_iff`. The paper's justification of openness (`I^+_W(x) = ]x,b[ ∩ W`) is
  not followed: openness is proved directly.
* `rem:minimalite_non_hereditaire` is **not marked**. It is an argument, and its content is taken
  to be three assertions. (1) Restriction commutes with generation: proved. (2) A clopen subset
  inherits absolute minimality: proved. (3) "Absolute minimality is hereditary *only* for clopen
  subsets". The reading for one precausality (`P|_U` absolutely minimal ⇒ `U` clopen) cannot
  be the intended one, since it contradicts `lem:precausalite_restriction_minimale`
  (`ETT.tex:491`); it is ruled out formally by the timelike line, absolutely minimal on
  `]0,+∞[` (`timelikeLine_rules_out_per_precausality_reading`). The fair reading is the subset
  one (`U` open and non-clopen ⇒ some absolutely minimal precausality on `M` restricts to a
  non-absolutely-minimal one on `U`); it is not stated: the paper's sentence "quantifying over arbitrarily fine covers this forces
  `Ū ∩ (M ∖ U) = ∅`" is a heuristic, not a proof, and the transparent-point construction needs a
  boundary point of `U` with points of `U` on both sides (it does not apply to `U = ]0,+∞[`).
  This reading is a question for the author.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Relation

/-! ### The construction -/

/-- The chronological future of a point of the transparent line is open. -/
theorem isOpen_transparent_right (U : Opens ℝ) (x : ℝ) :
    IsOpen {y : ℝ | x ∈ U ∧ y ∈ U ∧ x < y ∧ Icc x y ⊆ (U : Set ℝ) ∪ {0}} := by
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨hxU, hyU, hxy, hsub⟩
  obtain ⟨l, u, ⟨hl, hu⟩, hlu⟩ := mem_nhds_iff_exists_Ioo_subset.1 (U.isOpen.mem_nhds hyU)
  refine Filter.mem_of_superset (Ioo_mem_nhds (max_lt hxy hl) hu) ?_
  rintro y' ⟨hy'1, hy'2⟩
  refine ⟨hxU, hlu ⟨(le_max_right _ _).trans_lt hy'1, hy'2⟩,
    (le_max_left _ _).trans_lt hy'1, ?_⟩
  rintro z ⟨hz1, hz2⟩
  by_cases hzy : z ≤ y
  · exact hsub ⟨hz1, hzy⟩
  · exact Or.inl (hlu ⟨hl.trans (not_le.1 hzy), hz2.trans_lt hy'2⟩)

/-- The chronological past of a point of the transparent line is open. -/
theorem isOpen_transparent_left (U : Opens ℝ) (y : ℝ) :
    IsOpen {x : ℝ | x ∈ U ∧ y ∈ U ∧ x < y ∧ Icc x y ⊆ (U : Set ℝ) ∪ {0}} := by
  rw [isOpen_iff_mem_nhds]
  rintro x ⟨hxU, hyU, hxy, hsub⟩
  obtain ⟨l, u, ⟨hl, hu⟩, hlu⟩ := mem_nhds_iff_exists_Ioo_subset.1 (U.isOpen.mem_nhds hxU)
  refine Filter.mem_of_superset (Ioo_mem_nhds hl (lt_min hxy hu)) ?_
  rintro x' ⟨hx'1, hx'2⟩
  refine ⟨hlu ⟨hx'1, hx'2.trans_le (min_le_right _ _)⟩, hyU,
    hx'2.trans_le (min_le_left _ _), ?_⟩
  rintro z ⟨hz1, hz2⟩
  by_cases hxz : x ≤ z
  · exact hsub ⟨hxz, hz2⟩
  · exact Or.inl (hlu ⟨hx'1.trans_le hz1, (not_le.1 hxz).trans hu⟩)

theorem Icc_subset_union_of_trans {S : Set ℝ} {x y z : ℝ} (hxy : x ≤ y) (hyz : y ≤ z)
    (h₁ : Icc x y ⊆ S) (h₂ : Icc y z ⊆ S) : Icc x z ⊆ S := by
  have := hxy; have := hyz
  exact Icc_subset_Icc_union_Icc.trans (union_subset h₁ h₂)

/-- **`cexemple:point_transparent`**: the line with a transparent point `0`. For `W` open,
`x ≤_W y` iff `x, y ∈ W`, `x ≤ y` and `[x,y] ⊂ W ∪ {0}`; likewise `x ≪_W y` with `x < y`. -/
def transparentLine : Causality ℝ where
  le U x y := x ∈ U ∧ y ∈ U ∧ x ≤ y ∧ Icc x y ⊆ (U : Set ℝ) ∪ {0}
  lt U x y := x ∈ U ∧ y ∈ U ∧ x < y ∧ Icc x y ⊆ (U : Set ℝ) ∪ {0}
  le_mem_left h := h.1
  le_mem_right h := h.2.1
  lt_mem_left h := h.1
  lt_mem_right h := h.2.1
  le_refl hx := ⟨hx, hx, le_rfl, by simp [hx]⟩
  le_trans h₁ h₂ := ⟨h₁.1, h₂.2.1, h₁.2.2.1.trans h₂.2.2.1,
    Icc_subset_union_of_trans h₁.2.2.1 h₂.2.2.1 h₁.2.2.2 h₂.2.2.2⟩
  lt_trans h₁ h₂ := ⟨h₁.1, h₂.2.1, h₁.2.2.1.trans h₂.2.2.1,
    Icc_subset_union_of_trans h₁.2.2.1.le h₂.2.2.1.le h₁.2.2.2 h₂.2.2.2⟩
  le_mono h _ _ h' := ⟨h h'.1, h h'.2.1, h'.2.2.1, h'.2.2.2.trans (union_subset_union_left _ h)⟩
  lt_mono h _ _ h' := ⟨h h'.1, h h'.2.1, h'.2.2.1, h'.2.2.2.trans (union_subset_union_left _ h)⟩
  le_of_lt h := ⟨h.1, h.2.1, h.2.2.1.le, h.2.2.2⟩
  isOpen_lt_right := isOpen_transparent_right
  isOpen_lt_left := isOpen_transparent_left

variable {U V W : Opens ℝ} {x y : ℝ}

@[simp] theorem transparentLine_le :
    transparentLine.le U x y ↔ x ∈ U ∧ y ∈ U ∧ x ≤ y ∧ Icc x y ⊆ (U : Set ℝ) ∪ {0} := Iff.rfl

@[simp] theorem transparentLine_lt :
    transparentLine.lt U x y ↔ x ∈ U ∧ y ∈ U ∧ x < y ∧ Icc x y ⊆ (U : Set ℝ) ∪ {0} := Iff.rfl

/-- The paper's "equivalently": `x ≤_W y` iff `x ≤ y` and `x, y` lie in the same connected
component of `W ∪ {0}` (with `x, y ∈ W`). -/
theorem transparentLine_le_iff :
    transparentLine.le U x y ↔
      x ∈ U ∧ y ∈ U ∧ x ≤ y ∧ y ∈ connectedComponentIn ((U : Set ℝ) ∪ {0}) x := by
  rw [transparentLine_le]
  constructor
  · rintro ⟨hx, hy, hxy, hsub⟩
    have hxI : x ∈ Icc x y := left_mem_Icc.2 hxy
    exact ⟨hx, hy, hxy,
      isPreconnected_Icc.subset_connectedComponentIn hxI hsub (right_mem_Icc.2 hxy)⟩
  · rintro ⟨hx, hy, hxy, hc⟩
    refine ⟨hx, hy, hxy, ?_⟩
    have hK : IsPreconnected (connectedComponentIn ((U : Set ℝ) ∪ {0}) x) :=
      isPreconnected_connectedComponentIn
    exact (hK.Icc_subset (mem_connectedComponentIn (Or.inl hx)) hc).trans
      (connectedComponentIn_subset _ _)

/-- Away from the transparent point, the transparent line extends the timelike line. -/
theorem transparentLine_le_of_timelike (h : timelikeLine.le U x y) : transparentLine.le U x y :=
  ⟨h.2 (left_mem_Icc.2 h.1), h.2 (right_mem_Icc.2 h.1), h.1, h.2.trans subset_union_left⟩

theorem transparentLine_lt_of_timelike (h : timelikeLine.lt U x y) : transparentLine.lt U x y :=
  ⟨h.2 (left_mem_Icc.2 h.1.le), h.2 (right_mem_Icc.2 h.1.le), h.1, h.2.trans subset_union_left⟩

/-! ### Causally plain -/

/-- `cexemple:point_transparent`: "it is even causally plain". -/
theorem transparentLine_causallyPlain : transparentLine.CausallyPlain := by
  intro U A
  constructor
  · refine interior_subset.trans ?_
    rintro y ⟨a, ha, haU, hyU, hay, hsub⟩
    rw [mem_closure_iff_nhds]
    intro N hN
    obtain ⟨l, u, ⟨hl, hu⟩, hlu⟩ :=
      mem_nhds_iff_exists_Ioo_subset.1 (Filter.inter_mem hN (U.isOpen.mem_nhds hyU))
    have hmem : (y + u) / 2 ∈ Ioo l u := ⟨by linarith, by linarith⟩
    refine ⟨(y + u) / 2, (hlu hmem).1, a, ha, haU, (hlu hmem).2, by linarith, ?_⟩
    rintro z ⟨hz1, hz2⟩
    by_cases hzy : z ≤ y
    · exact hsub ⟨hz1, hzy⟩
    · exact Or.inl (hlu ⟨hl.trans (not_le.1 hzy), by linarith⟩).2
  · refine interior_subset.trans ?_
    rintro y ⟨a, ha, hyU, haU, hya, hsub⟩
    rw [mem_closure_iff_nhds]
    intro N hN
    obtain ⟨l, u, ⟨hl, hu⟩, hlu⟩ :=
      mem_nhds_iff_exists_Ioo_subset.1 (Filter.inter_mem hN (U.isOpen.mem_nhds hyU))
    have hmem : (l + y) / 2 ∈ Ioo l u := ⟨by linarith, by linarith⟩
    refine ⟨(l + y) / 2, (hlu hmem).1, a, ha, (hlu hmem).2, haU, by linarith, ?_⟩
    rintro z ⟨hz1, hz2⟩
    by_cases hyz : y ≤ z
    · exact hsub ⟨hyz, hz2⟩
    · exact Or.inl (hlu ⟨by linarith, (not_le.1 hyz).trans hu⟩).2

/-! ### Absolutely minimal on `ℝ` -/

section Minimal

variable {S : Set (Opens ℝ)}

/-- A segment inside `V` is a generated chain of the transparent line, causal case. -/
theorem transparentLine_chain_le (hS : ∀ x ∈ (⊤ : Opens ℝ), ∃ O ∈ S, x ∈ O) (hxy : x ≤ y)
    (hsub : Icc x y ⊆ (V : Set ℝ)) :
    TransGen (fun a b => ∃ O ∈ S, transparentLine.le (V ⊓ O) a b) x y := by
  have h := ((timelikeLine_absolutelyMinimalOn ⊤) S hS V le_top x y).1 ⟨hxy, hsub⟩
  exact TransGen.mono (fun a b ⟨O, hO, hab⟩ => ⟨O, hO, transparentLine_le_of_timelike hab⟩) h

/-- A segment inside `V` is a generated chain of the transparent line, chronological case. -/
theorem transparentLine_chain_lt (hS : ∀ x ∈ (⊤ : Opens ℝ), ∃ O ∈ S, x ∈ O) (hxy : x < y)
    (hsub : Icc x y ⊆ (V : Set ℝ)) :
    TransGen (fun a b => ∃ O ∈ S, transparentLine.lt (V ⊓ O) a b) x y := by
  have h := ((timelikeLine_absolutelyMinimalOn ⊤) S hS V le_top x y).2 ⟨hxy, hsub⟩
  exact TransGen.mono (fun a b ⟨O, hO, hab⟩ => ⟨O, hO, transparentLine_lt_of_timelike hab⟩) h

/-- The step across the puncture: if `0 ∈ ]x,y[`, `0 ∉ V` and `[x,y] ⊂ V ∪ {0}`, a member `O₀`
of the cover contains `0`, and there are `x < u < 0 < v < y` with `u ≪_{V ∩ O₀} v`. -/
theorem transparentLine_exists_crossing (hS : ∀ x ∈ (⊤ : Opens ℝ), ∃ O ∈ S, x ∈ O)
    (hx0 : x < 0) (h0y : 0 < y) (hsub : Icc x y ⊆ (V : Set ℝ) ∪ {0}) :
    ∃ u v, x < u ∧ u < 0 ∧ 0 < v ∧ v < y ∧ Icc x u ⊆ (V : Set ℝ) ∧ Icc v y ⊆ (V : Set ℝ) ∧
      ∃ O ∈ S, transparentLine.lt (V ⊓ O) u v := by
  obtain ⟨O, hO, h0O⟩ := hS 0 trivial
  obtain ⟨l, r, ⟨hl, hr⟩, hlr⟩ := mem_nhds_iff_exists_Ioo_subset.1 (O.isOpen.mem_nhds h0O)
  set u := max l x / 2 with hu
  set v := min r y / 2 with hv
  have hmax : max l x < 0 := max_lt hl hx0
  have hmin : 0 < min r y := lt_min hr h0y
  have hxu : x < u := by
    have := le_max_right l x; rw [hu]; linarith
  have hlu : l < u := by
    have := le_max_left l x; rw [hu]; linarith
  have hu0 : u < 0 := by rw [hu]; linarith
  have h0v : 0 < v := by rw [hv]; linarith
  have hvy : v < y := by
    have := min_le_right r y; rw [hv]; linarith
  have hvr : v < r := by
    have := min_le_left r y; rw [hv]; linarith
  -- a point of `[x,y]` other than `0` lies in `V`
  have hV : ∀ z ∈ Icc x y, z ≠ 0 → z ∈ (V : Set ℝ) := fun z hz hz0 =>
    (hsub hz).resolve_right hz0
  refine ⟨u, v, hxu, hu0, h0v, hvy, ?_, ?_, O, hO, ?_⟩
  · rintro z ⟨hz1, hz2⟩
    exact hV z ⟨hz1, by linarith⟩ (by linarith)
  · rintro z ⟨hz1, hz2⟩
    exact hV z ⟨by linarith, hz2⟩ (by linarith)
  · have huO : u ∈ O := hlr ⟨hlu, by linarith⟩
    have hvO : v ∈ O := hlr ⟨by linarith, hvr⟩
    refine ⟨⟨hV u ⟨hxu.le, by linarith⟩ hu0.ne, huO⟩, ⟨hV v ⟨by linarith, hvy.le⟩ h0v.ne', hvO⟩,
      by linarith, ?_⟩
    rintro z ⟨hz1, hz2⟩
    by_cases hz0 : z = 0
    · exact Or.inr hz0
    · exact Or.inl ⟨hV z ⟨by linarith, by linarith⟩ hz0, hlr ⟨by linarith, by linarith⟩⟩

/-- If `[x,y] ⊂ V ∪ {0}` with `x, y ∈ V`, either `[x,y] ⊂ V` or `x < 0 < y`. -/
theorem Icc_subset_or_cross (hx : x ∈ V) (hy : y ∈ V) (hsub : Icc x y ⊆ (V : Set ℝ) ∪ {0}) :
    Icc x y ⊆ (V : Set ℝ) ∨ (x < 0 ∧ 0 < y) := by
  by_cases h : Icc x y ⊆ (V : Set ℝ)
  · exact Or.inl h
  · right
    obtain ⟨z, hz, hzV⟩ := not_subset.1 h
    have hz0 : z = 0 := (hsub hz).resolve_left hzV
    subst hz0
    refine ⟨lt_of_le_of_ne hz.1 ?_, lt_of_le_of_ne hz.2 ?_⟩
    · rintro rfl; exact hzV hx
    · rintro rfl; exact hzV hy

/-- `cexemple:point_transparent`: "it is absolutely minimal on `ℝ`", on the relations. -/
theorem transparentLine_absolutelyMinimalOn_top :
    transparentLine.AbsolutelyMinimalOn ⊤ := by
  intro S hS V _ x y
  constructor
  · rintro ⟨hx, hy, hxy, hsub⟩
    rcases Icc_subset_or_cross hx hy hsub with h | ⟨hx0, h0y⟩
    · exact transparentLine_chain_le hS hxy h
    · obtain ⟨u, v, hxu, -, -, hvy, hxuV, hvyV, O, hO, huv⟩ :=
        transparentLine_exists_crossing hS hx0 h0y hsub
      exact ((transparentLine_chain_le hS hxu.le hxuV).tail
        ⟨O, hO, transparentLine.le_of_lt huv⟩).trans (transparentLine_chain_le hS hvy.le hvyV)
  · rintro ⟨hx, hy, hxy, hsub⟩
    rcases Icc_subset_or_cross hx hy hsub with h | ⟨hx0, h0y⟩
    · exact transparentLine_chain_lt hS hxy h
    · obtain ⟨u, v, hxu, -, -, hvy, hxuV, hvyV, O, hO, huv⟩ :=
        transparentLine_exists_crossing hS hx0 h0y hsub
      exact ((transparentLine_chain_lt hS hxu hxuV).tail ⟨O, hO, huv⟩).trans
        (transparentLine_chain_lt hS hvy hvyV)

/-- `cexemple:point_transparent`: "it is absolutely minimal on `ℝ`". -/
theorem transparentLine_absolutelyMinimal : transparentLine.AbsolutelyMinimal :=
  Precausality.absolutelyMinimal_iff.2 transparentLine_absolutelyMinimalOn_top

end Minimal

/-! ### The restriction to `ℝ ∖ {0}` is not absolutely minimal -/

/-- The open subset `ℝ ∖ {0}`. -/
def realMinusZero : Opens ℝ := ⟨{0}ᶜ, isOpen_compl_singleton⟩

/-- `cexemple:point_transparent`: "its restriction to the open subset `U := ℝ ∖ {0}` is not
absolutely minimal", with the paper's cover `V_± = ]0,±∞[` and the paper's `W = ]-2,2[ ∖ {0}`. -/
theorem transparentLine_not_absolutelyMinimalOn :
    ¬ transparentLine.AbsolutelyMinimalOn realMinusZero := by
  intro h
  let Vm : Opens ℝ := ⟨Iio 0, isOpen_Iio⟩
  let Vp : Opens ℝ := ⟨Ioi 0, isOpen_Ioi⟩
  let W : Opens ℝ := ⟨Ioo (-2) 2 ∩ {0}ᶜ, isOpen_Ioo.inter isOpen_compl_singleton⟩
  have hS : ∀ x ∈ realMinusZero, ∃ O ∈ ({Vm, Vp} : Set (Opens ℝ)), x ∈ O := by
    intro x hx
    rcases lt_or_gt_of_ne (show x ≠ 0 from hx) with h | h
    · exact ⟨Vm, by simp, h⟩
    · exact ⟨Vp, by simp, h⟩
  have hW : W ≤ realMinusZero := fun _ hx => hx.2
  have hrel : transparentLine.le W (-1) 1 := by
    refine ⟨⟨⟨by norm_num, by norm_num⟩, by norm_num⟩, ⟨⟨by norm_num, by norm_num⟩, by norm_num⟩,
      by norm_num, ?_⟩
    rintro z ⟨hz1, hz2⟩
    by_cases hz : z = 0
    · exact Or.inr hz
    · exact Or.inl ⟨⟨by linarith, by linarith⟩, hz⟩
  have hchain := ((h _ hS W hW (-1) 1).1 hrel)
  -- every point reached from `-1` is negative: a step cannot cross `0`
  have key : ∀ b, TransGen (fun a b => ∃ O ∈ ({Vm, Vp} : Set (Opens ℝ)),
      transparentLine.le (W ⊓ O) a b) (-1) b → b < 0 := by
    have step : ∀ a b, a < 0 → (∃ O ∈ ({Vm, Vp} : Set (Opens ℝ)),
        transparentLine.le (W ⊓ O) a b) → b < 0 := by
      rintro a b ha ⟨O, hO, haW, hbW, -⟩
      rcases hO with rfl | hO
      · exact hbW.2
      · rw [mem_singleton_iff] at hO
        subst hO
        exact absurd haW.2 (not_lt.2 ha.le)
    intro b hb
    induction hb with
    | single hl => exact step _ _ (by norm_num) hl
    | tail _ hl ih => exact step _ _ ih hl
  exact absurd (key 1 hchain) (by norm_num)

/-- **`cexemple:point_transparent`**, the four assertions together. -/
theorem point_transparent :
    transparentLine.CausallyPlain ∧ transparentLine.AbsolutelyMinimal ∧
      ¬ transparentLine.AbsolutelyMinimalOn realMinusZero :=
  ⟨transparentLine_causallyPlain, transparentLine_absolutelyMinimal,
    transparentLine_not_absolutelyMinimalOn⟩

/-! ### `rem:minimalite_non_hereditaire` -/

section NonHereditary

universe u v

variable {M : Type u} [TopologicalSpace M] {ι : Type v} {P : Precausality M} {O : ι → Opens M}
  {hO : ∀ x : M, ∃ i, x ∈ O i} {U V : Opens M} {x y : M}

/-- `rem:minimalite_non_hereditaire`, "restriction commutes with generation", causal half: in an
open `V ⊂ U`, the precausality generated by `𝒪` is the one generated by its trace
`𝒪|_U = (O_a ∩ U)_a`. -/
theorem generated_restrict_le (hVU : V ≤ U) :
    (Precausality.generated O hO (fun _ => P)).le V x y ↔
      TransGen (Precausality.LinkLe (fun i => O i ⊓ U) (fun _ => P) V) x y := by
  have : ∀ i, V ⊓ (O i ⊓ U) = V ⊓ O i := fun i => by
    rw [inf_comm (O i) U, ← inf_assoc, inf_eq_left.2 hVU]
  have hfun : Precausality.LinkLe (fun i => O i ⊓ U) (fun _ => P) V =
      Precausality.LinkLe O (fun _ => P) V := by
    funext a b
    simp only [Precausality.LinkLe, this]
  rw [Precausality.generated_le, hfun]

/-- `rem:minimalite_non_hereditaire`, "restriction commutes with generation", chronological
half. -/
theorem generated_restrict_lt (hVU : V ≤ U) :
    (Precausality.generated O hO (fun _ => P)).lt V x y ↔
      TransGen (Precausality.LinkLt (fun i => O i ⊓ U) (fun _ => P) V) x y := by
  have : ∀ i, V ⊓ (O i ⊓ U) = V ⊓ O i := fun i => by
    rw [inf_comm (O i) U, ← inf_assoc, inf_eq_left.2 hVU]
  have hfun : Precausality.LinkLt (fun i => O i ⊓ U) (fun _ => P) V =
      Precausality.LinkLt O (fun _ => P) V := by
    funext a b
    simp only [Precausality.LinkLt, this]
  rw [Precausality.generated_lt, hfun]

/-- `rem:minimalite_non_hereditaire`, the direction it asserts implicitly: absolute minimality is
inherited by an open subset which is closed. -/
theorem Precausality.AbsolutelyMinimalOn.of_isClosed {W : Opens M} (h : P.AbsolutelyMinimalOn W)
    (hUW : U ≤ W) (hU : IsClosed (U : Set M)) : P.AbsolutelyMinimalOn U := by
  intro S hS V hVU x y
  let Uc : Opens M := ⟨(U : Set M)ᶜ, hU.isOpen_compl⟩
  have hS' : ∀ z ∈ W, ∃ N ∈ insert Uc S, z ∈ N := by
    intro z _
    by_cases hz : z ∈ U
    · obtain ⟨N, hN, hzN⟩ := hS z hz
      exact ⟨N, mem_insert_of_mem _ hN, hzN⟩
    · exact ⟨Uc, mem_insert _ _, hz⟩
  -- a step localised in `V ∩ (M ∖ U)` is impossible, since `V ⊂ U`
  have hnot : ∀ {a : M}, a ∈ V ⊓ Uc → False := fun ha => ha.2 (hVU ha.1)
  obtain ⟨h₁, h₂⟩ := h (insert Uc S) hS' V (hVU.trans hUW) x y
  refine ⟨fun hxy => TransGen.mono ?_ (h₁ hxy), fun hxy => TransGen.mono ?_ (h₂ hxy)⟩
  · rintro a b ⟨N, hN, hab⟩
    rcases hN with rfl | hN
    · exact (hnot (P.le_mem_left hab)).elim
    · exact ⟨N, hN, hab⟩
  · rintro a b ⟨N, hN, hab⟩
    rcases hN with rfl | hN
    · exact (hnot (P.lt_mem_left hab)).elim
    · exact ⟨N, hN, hab⟩

/-- `rem:minimalite_non_hereditaire`: an absolutely minimal precausality restricts to an
absolutely minimal one on every clopen subset. -/
theorem Precausality.AbsolutelyMinimal.absolutelyMinimalOn_of_isClopen
    (h : P.AbsolutelyMinimal) (hU : IsClopen (U : Set M)) : P.AbsolutelyMinimalOn U :=
  Precausality.AbsolutelyMinimalOn.of_isClosed (Precausality.absolutelyMinimal_iff.1 h) le_top hU.1

end NonHereditary

/-- Rules out the per-precausality reading of the last sentence of
`rem:minimalite_non_hereditaire` ("`P|_U` absolutely minimal ⇒ `U` clopen"), which is not the
paper's intent (it would contradict `lem:precausalite_restriction_minimale`): the timelike line
is absolutely minimal, and so is its restriction to `]0,+∞[`, which is not clopen in `ℝ`. The
intended, subset, reading is not addressed. -/
theorem timelikeLine_rules_out_per_precausality_reading :
    timelikeLine.AbsolutelyMinimal ∧
      ∃ U : Opens ℝ, timelikeLine.AbsolutelyMinimalOn U ∧ ¬ IsClopen (U : Set ℝ) := by
  refine ⟨timelikeLine_absolutelyMinimal, ⟨Ioi 0, isOpen_Ioi⟩,
    timelikeLine_absolutelyMinimalOn _, ?_⟩
  intro h
  rcases isClopen_iff.1 h with h | h
  · have h1 : (1 : ℝ) ∈ ((⟨Ioi 0, isOpen_Ioi⟩ : Opens ℝ) : Set ℝ) := (one_pos : (0 : ℝ) < 1)
    rw [h] at h1
    exact h1
  · have h0 : (0 : ℝ) ∈ ((⟨Ioi 0, isOpen_Ioi⟩ : Opens ℝ) : Set ℝ) := by rw [h]; trivial
    exact lt_irrefl (0 : ℝ) h0

end Causal
