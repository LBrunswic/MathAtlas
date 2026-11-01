import CausalScaffold.Flat.Externals

/-!
# `CausalScaffold.Flat.Lox.RegularLattice` — `𝒩` is a lattice in a spacelike `E`, and `Ω + E = Ω`, for a group acting properly on a one-sided convex domain

T. Barbot, *Globally hyperbolic flat space-times* (`papers/barbot`, arXiv math/0402257), §10,
item **[10.G]** of `docs/BARBOT.md` (`GHFspace.tex` l.3406–3417 and l.3432–3435, labelled copy).
**No ledger label is certified here** (no `**` mark): this is one step of the prose of [10.G],
served to `loxo_generic_centralExtension` (`Flat/Loxodromic.lean`) and through it to
`loxo_generic_torusProduct`: the `𝒩`-conjuncts of family (b) for the RESTRICTED group `Γ''_U`
acting on `ι⁻¹Ω(S̃)`, where no `CCAction` exists. `kerTranslations_spacelike`, `_ballFinite`,
`span_kerTranslations_spacelike` and `omegaS_add_mem_span` (`Flat/Loxodromic.lean`) all take a
`CCAction`; `kerTranslations_lattice_of_oneSided` frees them from it: any subgroup `Γ` of
`Isom(𝐌ⁿ)` (`𝐌ⁿ = Minkowski d`, Barbot's `n` is `d + 1`) acting properly on an open convex
nonempty `Ω` lying on one side of a set `Λ ⊆ 𝒥` containing two distinct null directions.

> $L$ might be noninjective! Let $\mathcal N$ be its
> kernel: its elements are translations, and the translation vectors
> form a lattice in some spacelike linear space $E$. (l.3407–3409)

> Hence, replacing $\Gamma$ by some finite index subgroup,
> we can assume that this action is trivial. (l.3416–3417)

> On the other hand, since it is convex, and since
> it is preserved by translations in $\mathcal N$, the regular
> convex domain $\Omega(\widetilde{S})$ is preserved by translations
> by vectors in $E$. (l.3432–3435)

The three conjuncts: `E = span 𝒩` is spacelike (`minkQ > 0` on `E ∖ 0`); `𝒩` is discrete (finite
in every ball, the form `Lox.exists_finiteIndex_linOf_eq_on_span` of `Lox/LatticeTrivial.lean`
consumes); `Ω + E = Ω`. Proofs: `Ω + E = Ω` is `omegaS_add_mem_span` with convexity and
invariance as hypotheses; spacelikeness is `span_kerTranslations_spacelike` with `hside`/`htwo`
in place of `blem:loxregular` and `exists_two_loxRepSet` (a line `x + ℝ v` inside `Ω` stays on one
side of each light hyperplane of `Λ`, so `v` is orthogonal to two distinct null directions);
discreteness covers the ball `B(0, R)` by finitely many balls of radius `ε/4`, `ε` the radius of a
ball `B(x, ε) ⊆ Ω`, and two vectors `v₀, v` of `𝒩` in one small ball give `γ₀⁻¹ γ` moving `x`
inside `K = B̄(x, ε/2)`, finitely many by `hprop`.

## Hypothesis checklist
| paper hypothesis | here |
|---|---|
| `Γ` acts freely and properly discontinuously on `Ω(S̃)` (Cor 10.3) | ⚠ weakened: only `hprop`, finiteness of `{γ | γK ∩ K ≠ ∅}` for compact `K ⊆ Ω`; freeness is not used |
| `Ω(S̃)` the regular convex domain `Ω^±(Λ(ρ))` (l.3398–3403) | ⚠ weakened: `Ω` open, convex, nonempty, `Γ`-invariant, contained in `Ω^+(Λ)` or `Ω^-(Λ)` for a `Λ` with two distinct null directions (`htwo`); no equality, no closure |
| `Γ` nonelementary loxodromic (§10) | ⚠ weakened: used only through `htwo` |

## SCOPE (disclosed)
Nothing is left unproved. "Lattice" is read as discrete (finite in every ball), as in
`Lox/LatticeTrivial.lean`; cocompactness of `𝒩` in `E` is neither claimed nor needed downstream.
Spacelikeness of `E` is a step the paper asserts without argument (see
`span_kerTranslations_spacelike`'s docstring).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Written by a prover
of the Barbot campaign (`Lox/` split of `loxo_generic_centralExtension`, the restriction to `U`),
adapting `omegaS_add_mem_span` and `span_kerTranslations_spacelike` (`Flat/Loxodromic.lean`
l.2452–2558) to hypotheses without `CCAction`.
-/

namespace Causal.Flat.Lox
open Set
open scoped Pointwise
variable {d : ℕ}

/-- **[10.G], l.3432–3435, without `CCAction`**: a convex `Ω` invariant under a group `Γ` is
invariant under the translations by the span of the translation vectors of `Γ`. -/
theorem add_mem_of_mem_span_translVec {Γ : Subgroup (isom d)} {Ω : Set (Minkowski d)}
    (hΩc : Convex ℝ Ω) (hinv : ∀ γ ∈ Γ, ∀ p ∈ Ω, γ • p ∈ Ω) {v : Minkowski d}
    (hv : v ∈ Submodule.span ℝ {v : Minkowski d | ∃ γ ∈ Γ, linOf γ = 1 ∧ trOf γ = v})
    {p : Minkowski d} (hp : p ∈ Ω) : p + v ∈ Ω := by
  -- the translations preserving `Ω` in both directions form a submodule
  let T : Submodule ℝ (Minkowski d) :=
    { carrier := {v | ∀ p ∈ Ω, p + v ∈ Ω ∧ p - v ∈ Ω}
      add_mem' := by
        intro a b ha hb p hp
        refine ⟨?_, ?_⟩
        · rw [← add_assoc]; exact (hb _ (ha p hp).1).1
        · rw [sub_add_eq_sub_sub]; exact (hb _ (ha p hp).2).2
      zero_mem' := fun p hp => by simpa using hp
      smul_mem' := by
        intro t a ha p hp
        have hnat : ∀ n : ℕ, ∀ q ∈ Ω, q + (n : ℝ) • a ∈ Ω ∧ q - (n : ℝ) • a ∈ Ω := by
          intro n; induction n with
          | zero => intro q hq; simpa using hq
          | succ n ih =>
            intro q hq
            obtain ⟨h1, h2⟩ := ih q hq
            push_cast
            refine ⟨?_, ?_⟩
            · rw [add_smul, one_smul, ← add_assoc]; exact (ha _ h1).1
            · rw [add_smul, one_smul, sub_add_eq_sub_sub]; exact (ha _ h2).2
        have key : ∀ s : ℝ, ∀ q ∈ Ω, q + s • a ∈ Ω := by
          intro s q hq
          obtain ⟨n, hn⟩ := exists_nat_gt |s|
          have hn0 : (0 : ℝ) < n := lt_of_le_of_lt (abs_nonneg s) hn
          rcases le_total 0 s with hs | hs
          · have := hΩc.add_smul_mem hq (hnat n q hq).1 (t := s / n)
              ⟨div_nonneg hs hn0.le, (div_le_one hn0).2 (by
                rw [abs_of_nonneg hs] at hn; exact hn.le)⟩
            rwa [smul_smul, div_mul_cancel₀ _ hn0.ne'] at this
          · have h2 : q + (n : ℝ) • (-a) ∈ Ω := by
              rw [smul_neg, ← sub_eq_add_neg]; exact (hnat n q hq).2
            have := hΩc.add_smul_mem hq h2 (t := -s / n)
              ⟨div_nonneg (by linarith) hn0.le, (div_le_one hn0).2 (by
                rw [abs_of_nonpos hs] at hn; exact hn.le)⟩
            rwa [smul_smul, div_mul_cancel₀ _ hn0.ne', smul_neg, neg_smul, neg_neg] at this
        exact ⟨key t p hp, by rw [sub_eq_add_neg, ← neg_smul]; exact key (-t) p hp⟩ }
  have hsub : {v : Minkowski d | ∃ γ ∈ Γ, linOf γ = 1 ∧ trOf γ = v} ⊆ T := by
    rintro _ ⟨γ, hγ, hL, rfl⟩ q hq
    have hsm : ∀ x, γ • x = x + trOf γ := fun x => by rw [smul_eq_lin_add, hL]; rfl
    have h1 : γ • q ∈ Ω := hinv γ hγ q hq
    have h2 : γ⁻¹ • q ∈ Ω := hinv γ⁻¹ (Γ.inv_mem hγ) q hq
    refine ⟨by rw [← hsm]; exact h1, ?_⟩
    have : γ⁻¹ • q = q - trOf γ := by rw [inv_smul_eq_iff, hsm]; abel
    rw [← this]; exact h2
  exact ((Submodule.span_le.2 hsub) hv p hp).1

/-- **[10.G], l.3409, without `CCAction`: `E = span 𝒩` is spacelike** when `Ω` (convex,
`Γ`-invariant, nonempty) lies on one side of a `Λ` with two distinct null directions: a line
`x + ℝ v ⊆ Ω` forces `v` orthogonal to both null directions. -/
theorem span_translVec_spacelike_of_oneSided {Γ : Subgroup (isom d)} {Ω : Set (Minkowski d)}
    {Λ : Set (PenroseSphere d × ℝ)} (hΩc : Convex ℝ Ω) (hΩn : Ω.Nonempty)
    (hinv : ∀ γ ∈ Γ, ∀ p ∈ Ω, γ • p ∈ Ω)
    (hside : Ω ⊆ omegaPlus Λ ∨ Ω ⊆ omegaMinus Λ)
    (htwo : ∃ w₁ ∈ Λ, ∃ w₂ ∈ Λ, w₁.1 ≠ w₂.1) :
    ∀ v ∈ Submodule.span ℝ {v : Minkowski d | ∃ γ ∈ Γ, linOf γ = 1 ∧ trOf γ = v},
      v ≠ 0 → 0 < minkQ v := by
  intro v hv hv0
  obtain ⟨w₁, hw₁, w₂, hw₂, hne⟩ := htwo
  obtain ⟨x, hxΩ⟩ := hΩn
  have hline : ∀ t : ℝ, x + t • v ∈ Ω := fun t =>
    add_mem_of_mem_span_translVec hΩc hinv (Submodule.smul_mem _ t hv) hxΩ
  -- `⟨n_w | v⟩ = 0` for `w ∈ Λ`
  have hkill : ∀ w ∈ Λ, minkB (nullVec w.1) v = 0 := by
    intro w hw
    by_contra hB
    have hbd : (∀ t : ℝ, minkB (nullVec w.1) (x + t • v) < w.2) ∨
        ∀ t : ℝ, w.2 < minkB (nullVec w.1) (x + t • v) := by
      rcases hside with hF | hP
      · exact Or.inl fun t => mem_omegaPlus.1 (hF (hline t)) w hw
      · exact Or.inr fun t => mem_omegaMinus.1 (hP (hline t)) w hw
    have e : ∀ t : ℝ, minkB (nullVec w.1) (x + t • v) =
        minkB (nullVec w.1) x + t * minkB (nullVec w.1) v := fun t => by
      rw [minkB_add_right, minkB_smul_right]
    set β := minkB (nullVec w.1) v
    set a := minkB (nullVec w.1) x
    have ht : a + (w.2 - a) / β * β = w.2 := by rw [div_mul_cancel₀ _ hB]; ring
    rcases hbd with hb | hb
    · have := hb ((w.2 - a) / β); rw [e, ht] at this; exact lt_irrefl _ this
    · have := hb ((w.2 - a) / β); rw [e, ht] at this; exact lt_irrefl _ this
  have h1 := hkill w₁ hw₁
  have h2 := hkill w₂ hw₂
  have key : ∀ u : Minkowski d, u ≠ 0 → IsFutureCausal u → minkB (nullVec w₁.1) u = 0 →
      minkB (nullVec w₂.1) u = 0 → False := by
    intro u hu0 hc hu1 hu2
    rcases lt_or_eq_of_le hc.2 with hq | hq
    · have := minkB_neg_of_future (isFutureCausal_nullVec w₁.1) (nullVec_ne_zero w₁.1)
        ⟨lt_of_le_of_ne hc.1 (fun e => hu0 (eq_zero_of_fst_eq_zero e.symm hc.2)), hq⟩
      linarith
    · obtain ⟨c₁, hc₁⟩ := eq_smul_of_null_orth hq hu0 (minkQ_nullVec w₁.1)
        (by rw [minkB_comm]; exact hu1)
      obtain ⟨c₂, hc₂⟩ := eq_smul_of_null_orth hq hu0 (minkQ_nullVec w₂.1)
        (by rw [minkB_comm]; exact hu2)
      have hc₂0 : c₂ ≠ 0 := fun e => nullVec_ne_zero w₂.1 (by rw [hc₂, e, zero_smul])
      exact hne (nullVec_injective_smul (c := c₁ / c₂) (by
        rw [hc₁, hc₂, smul_smul, div_mul_cancel₀ _ hc₂0]))
  by_contra hle
  have hq : minkQ v ≤ 0 := not_lt.1 hle
  rcases le_total 0 v.1 with hv1 | hv1
  · exact key v hv0 ⟨hv1, hq⟩ h1 h2
  · exact key (-v) (neg_ne_zero.2 hv0) ⟨by simpa using hv1, by rw [minkQ_neg]; exact hq⟩
      (by rw [minkB_neg_right, h1, neg_zero]) (by rw [minkB_neg_right, h2, neg_zero])

/-- **[10.G], l.3409, without `CCAction`: the translation vectors of `Γ` are discrete** (finitely
many in each ball) when `Γ` acts properly on an open nonempty `Ω`. -/
theorem translVec_ballFinite_of_proper {Γ : Subgroup (isom d)} {Ω : Set (Minkowski d)}
    (hΩo : IsOpen Ω) (hΩn : Ω.Nonempty)
    (hprop : ∀ K ⊆ Ω, IsCompact K → {γ : isom d | γ ∈ Γ ∧ (γ • K ∩ K).Nonempty}.Finite)
    (R : ℝ) :
    ({v : Minkowski d | ∃ γ ∈ Γ, linOf γ = 1 ∧ trOf γ = v} ∩ Metric.closedBall 0 R).Finite := by
  set N := {v : Minkowski d | ∃ γ ∈ Γ, linOf γ = 1 ∧ trOf γ = v}
  obtain ⟨x, hx⟩ := hΩn
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hΩo x hx
  set K := Metric.closedBall x (ε / 2)
  have hKΩ : K ⊆ Ω := (Metric.closedBall_subset_ball (half_lt_self hε)).trans hball
  have hF := hprop K hKΩ (isCompact_closedBall x (ε / 2))
  have hxK : x ∈ K := Metric.mem_closedBall_self (by positivity)
  have hδ : (0 : ℝ) < ε / 4 := by positivity
  -- two translation vectors in one ball of radius `ε/4` differ by a move of `x` inside `K`
  have hloc : ∀ c : Minkowski d, (N ∩ Metric.ball c (ε / 4)).Finite := by
    intro c
    rcases (N ∩ Metric.ball c (ε / 4)).eq_empty_or_nonempty with h | ⟨_, ⟨γ₀, hγ₀, hL₀, rfl⟩, hv₀c⟩
    · rw [h]; exact finite_empty
    have hsm₀ : ∀ y, γ₀ • y = y + trOf γ₀ := fun y => by rw [smul_eq_lin_add, hL₀]; rfl
    have hsm₀' : ∀ y, γ₀⁻¹ • y = y - trOf γ₀ := fun y => by rw [inv_smul_eq_iff, hsm₀]; abel
    refine (hF.image (fun g : isom d => g • x - x + trOf γ₀)).subset ?_
    rintro _ ⟨⟨γ, hγ, hL, rfl⟩, hvc⟩
    have hsm : ∀ y, γ • y = y + trOf γ := fun y => by rw [smul_eq_lin_add, hL]; rfl
    have he : (γ₀⁻¹ * γ) • x = x + (trOf γ - trOf γ₀) := by
      rw [mul_smul, hsm, hsm₀']; abel
    have hd : ‖trOf γ - trOf γ₀‖ < ε / 2 := by
      have h1 := Metric.mem_ball.1 hvc
      have h2 := Metric.mem_ball.1 hv₀c
      calc ‖trOf γ - trOf γ₀‖ = dist (trOf γ) (trOf γ₀) := (dist_eq_norm _ _).symm
        _ ≤ dist (trOf γ) c + dist (trOf γ₀) c := dist_triangle_right _ _ _
        _ < ε / 4 + ε / 4 := add_lt_add h1 h2
        _ = ε / 2 := by ring
    have hgxK : (γ₀⁻¹ * γ) • x ∈ K := by
      rw [Metric.mem_closedBall, he, dist_eq_norm, add_sub_cancel_left]; exact hd.le
    refine ⟨γ₀⁻¹ * γ, ⟨Γ.mul_mem (Γ.inv_mem hγ₀) hγ, (γ₀⁻¹ * γ) • x,
      Set.smul_mem_smul_set hxK, hgxK⟩, ?_⟩
    show (γ₀⁻¹ * γ) • x - x + trOf γ₀ = trOf γ
    rw [he]; abel
  obtain ⟨t, -, ht, hcov⟩ :=
    finite_cover_balls_of_compact (isCompact_closedBall (0 : Minkowski d) R) hδ
  refine (ht.biUnion fun c _ => hloc c).subset ?_
  rintro v ⟨hvN, hvR⟩
  obtain ⟨c, hc, hvc⟩ := mem_iUnion₂.1 (hcov hvR)
  exact mem_iUnion₂.2 ⟨c, hc, hvN, hvc⟩

/-- **[10.G], l.3406–3417 and l.3432–3435, for any group acting properly on a one-sided convex
domain**: the translation vectors `𝒩` of `Γ` span a spacelike `E`, are discrete, and `Ω + E = Ω`.
The `𝒩`-conjuncts of family (b) for the restricted group `Γ''_U` acting on `ι⁻¹Ω(S̃)`, where no
`CCAction` exists; the output feeds `Lox.exists_finiteIndex_linOf_eq_on_span`. -/
theorem kerTranslations_lattice_of_oneSided {d : ℕ} {Γ : Subgroup (isom d)} {Ω : Set (Minkowski d)}
    {Λ : Set (PenroseSphere d × ℝ)} (hΩo : IsOpen Ω) (hΩc : Convex ℝ Ω) (hΩn : Ω.Nonempty)
    (hinv : ∀ γ ∈ Γ, ∀ p ∈ Ω, γ • p ∈ Ω)
    (hprop : ∀ K ⊆ Ω, IsCompact K → {γ : isom d | γ ∈ Γ ∧ (γ • K ∩ K).Nonempty}.Finite)
    (hside : Ω ⊆ omegaPlus Λ ∨ Ω ⊆ omegaMinus Λ)
    (htwo : ∃ w₁ ∈ Λ, ∃ w₂ ∈ Λ, w₁.1 ≠ w₂.1) :
    (∀ v ∈ Submodule.span ℝ {v : Minkowski d | ∃ γ ∈ Γ, linOf γ = 1 ∧ trOf γ = v},
        v ≠ 0 → 0 < minkQ v) ∧
      (∀ R : ℝ, ({v : Minkowski d | ∃ γ ∈ Γ, linOf γ = 1 ∧ trOf γ = v} ∩
        Metric.closedBall 0 R).Finite) ∧
      ∀ v ∈ Submodule.span ℝ {v : Minkowski d | ∃ γ ∈ Γ, linOf γ = 1 ∧ trOf γ = v},
        ∀ p ∈ Ω, p + v ∈ Ω :=
  ⟨span_translVec_spacelike_of_oneSided hΩc hΩn hinv hside htwo,
    translVec_ballFinite_of_proper hΩo hΩn hprop,
    fun _ hv _ hp => add_mem_of_mem_span_translVec hΩc hinv hv hp⟩

end Causal.Flat.Lox
