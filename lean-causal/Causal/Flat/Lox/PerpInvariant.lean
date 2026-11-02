import Causal.Flat.TwistedProduct
import Causal.Flat.Externals

/-!
# `Ω^±(Λ)` is invariant under the translations by `U^⊥` when `Γ` preserves `U`

Gap G6 for `Ω(S̃)` (`docs/BARBOT-THEOREMS.md` §6): the hypothesis `hperp` of
`TwistedProduct.suspendre` (`blem:suspendre`), served to `loxo_generic_centralExtension`
(`Flat/Loxodromic.lean`, `[10.G]`) and `loxo_elementary_misner` (`[10.M]`). **No label is
marked**: this is one sentence of two proofs, not a statement of the paper.

* `[10.G]`, `GHFspace.tex:3391–3396`, partial (the `U^⊥`-invariance only; **no `sorry`**):
  `add_perp_mem_omega_of_preserves`.
* `[10.M]`, `GHFspace.tex:3279–3283`, partial (same step): `add_perp_mem_omega_of_preserves`.

> Actually, thanks to Proposition \ref{suspendre}, we can restrict our
> study to the case ${\bf U} = {\bf M}^{n}$ (be aware that
> $\Omega_{lox}(\Gamma)$ is obviously equal to
> ${\bf U}^{\perp} \oplus \Omega_{lox}(\Gamma_{\mid \bf U})$,

> Since it is $\Gamma$-invariant, up to a linear twisted product,
> we can assume thanks to
> lemma \ref{suspendre} that
> ${\bf U}$ is the entire Minkowski space

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `U` is `Γ`-invariant | ✓ carried (`hpres`, the set-image form of `RestrictsIn.preserves`) |
| `Λ` is the limit set of the loxodromic part | ⚠ weakened: any `Λ` in the closure of the points `(u, s)` whose null direction is an eigenline of some `L(γ)`, `γ ∈ Γ`, of eigenvalue `≠ 1` (`hΛ`) |
| `U` timelike | ⚠ weakened: not used beyond what `AffineMinkEmbedding` gives (`U^⊥` spacelike) |

## SCOPE (disclosed)

Only the "obvious" invariance `Ω^±(Λ) + U^⊥ = Ω^±(Λ)` is proved; the splitting
`Ω_lox(Γ) = U^⊥ ⊕ Ω_lox(Γ|_U)` as an identification of the base is the business of `suspendre`.
The integration (`Λ := limitSetJ ρ.range`, `ι` from `exists_affineMinkEmbedding_of_isTimelike`,
`hpres` from the `Γ`-invariance of `U`) is the caller's.

Proof: `L(γ)` preserves `range ι.lin` in both directions (`hpres` read at two points), hence
preserves `U^⊥`. If `L(γ) n = l n`, `l ≠ 1`, `l > 0`, write `n = ι.lin c + n'` with `n' ∈ U^⊥`;
uniqueness of the decomposition gives `L(γ) n' = l n'`, so `minkQ n' = l² minkQ n'`, `minkQ n' = 0`
and `n' = 0` (`U^⊥` spacelike). Hence `⟨n | v⟩ = 0` for `v ∈ U^⊥`; this is a closed condition on
`w`, so it holds on `Λ`, and `⟨n | p + v⟩ = ⟨n | p⟩`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Barbot campaign,
planner proof plan (gap G6, `Ω(S̃)`).
-/

namespace Causal.Flat.Lox
open Set
variable {d d₁ : ℕ}

private theorem pinv_smul_sub (γ : isom d) (x y : Minkowski d) :
    γ • x - γ • y = linOf γ (x - y) := by
  rw [smul_eq_lin_add, smul_eq_lin_add, map_sub]; abel

private theorem pinv_apply_sub_zero (ι : AffineMinkEmbedding d₁ d) (u : Minkowski d₁) :
    ι u - ι 0 = ι.lin u := by
  have := ι.apply_sub 0 u; rwa [sub_zero] at this

/-- `L(γ)` maps `range ι.lin` onto itself: every `ι.lin u` is `L(γ) (ι.lin u')`. -/
private theorem pinv_lin_eq_linOf (ι : AffineMinkEmbedding d₁ d) {γ : isom d}
    (hpres : (fun p => γ • p) '' Set.range ι = Set.range ι) (u : Minkowski d₁) :
    ∃ u', ι.lin u = linOf γ (ι.lin u') := by
  have h1 : ι u ∈ (fun p => γ • p) '' Set.range ι := by rw [hpres]; exact mem_range_self u
  have h0 : ι 0 ∈ (fun p => γ • p) '' Set.range ι := by rw [hpres]; exact mem_range_self 0
  obtain ⟨_, ⟨a, rfl⟩, ha⟩ := h1
  obtain ⟨_, ⟨b, rfl⟩, hb⟩ := h0
  refine ⟨a - b, ?_⟩
  rw [← pinv_apply_sub_zero, ← ha, ← hb, pinv_smul_sub, ← ι.apply_sub b a]

/-- `L(γ)` maps `range ι.lin` into itself. -/
private theorem pinv_linOf_lin (ι : AffineMinkEmbedding d₁ d) {γ : isom d}
    (hpres : (fun p => γ • p) '' Set.range ι = Set.range ι) (u : Minkowski d₁) :
    ∃ u', linOf γ (ι.lin u) = ι.lin u' := by
  have h1 : γ • ι u ∈ Set.range ι := by rw [← hpres]; exact mem_image_of_mem _ (mem_range_self u)
  have h0 : γ • ι 0 ∈ Set.range ι := by rw [← hpres]; exact mem_image_of_mem _ (mem_range_self 0)
  obtain ⟨a, ha⟩ := h1
  obtain ⟨b, hb⟩ := h0
  refine ⟨a - b, ?_⟩
  rw [← pinv_apply_sub_zero, ← pinv_smul_sub, ← ha, ← hb, ι.apply_sub b a]

/-- `L(γ)` preserves `U^⊥`. -/
private theorem pinv_linOf_mem_perp (ι : AffineMinkEmbedding d₁ d) {γ : isom d}
    (hpres : (fun p => γ • p) '' Set.range ι = Set.range ι) {w : Minkowski d}
    (hw : w ∈ ι.perp) : linOf γ w ∈ ι.perp := fun u => by
  obtain ⟨u', hu'⟩ := pinv_lin_eq_linOf ι hpres u
  rw [hu', lorentz.minkB_apply (linOf_mem γ)]; exact hw u'

/-- An eigenvector of `L(γ)` of eigenvalue `l > 0`, `l ≠ 1`, lies in `range ι.lin`, hence is
orthogonal to `U^⊥`. -/
private theorem pinv_minkB_eq_zero (ι : AffineMinkEmbedding d₁ d) {γ : isom d}
    (hpres : (fun p => γ • p) '' Set.range ι = Set.range ι) {l : ℝ} (hl0 : 0 < l) (hl1 : l ≠ 1)
    {n : Minkowski d} (hn : linOf γ n = l • n) {v : Minkowski d} (hv : v ∈ ι.perp) :
    minkB n v = 0 := by
  set c := ι.coproj n
  set n' := n - ι.lin c with hn'def
  have hn' : n' ∈ ι.perp := ι.sub_lin_coproj_mem_perp n
  obtain ⟨c₁, hc₁⟩ := pinv_linOf_lin ι hpres c
  have hLn' : linOf γ n' ∈ ι.perp := pinv_linOf_mem_perp ι hpres hn'
  -- `L(γ) n' - l n' = ι.lin (l c - c₁)`
  have hdiff : linOf γ n' - l • n' = ι.lin (l • c - c₁) := by
    rw [hn'def, map_sub, hn, hc₁, map_sub, map_smul]; module
  have hmem : ι.lin (l • c - c₁) ∈ ι.perp := by
    rw [← hdiff]; exact ι.sub_mem_perp hLn' (ι.smul_mem_perp l hn')
  have hzero : l • c - c₁ = 0 := ι.lin_mem_perp_iff.1 hmem
  have heig : linOf γ n' = l • n' := by
    rw [hzero, map_zero] at hdiff; exact sub_eq_zero.1 hdiff
  have hQ : minkQ n' = l ^ 2 * minkQ n' := by
    rw [← minkQ_smul, ← heig, lorentz.minkQ_apply (linOf_mem γ)]
  have hl2 : l ^ 2 ≠ 1 := by
    intro h
    have : l = 1 := by nlinarith
    exact hl1 this
  have hQ0 : minkQ n' = 0 := by
    have : (l ^ 2 - 1) * minkQ n' = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · exact absurd (sub_eq_zero.1 h) hl2
    · exact h
  have hn'0 : n' = 0 := by
    by_contra hne
    exact (ι.minkQ_pos_of_mem_perp hn' hne).ne' hQ0
  have hn_eq : n = ι.lin c := sub_eq_zero.1 hn'0
  rw [hn_eq, minkB_comm]; exact hv c

/-- **`Ω^±(Λ)` is invariant under `U^⊥`** (gap G6 for `Ω(S̃)`, the `hperp` of `suspendre`):
if `Γ` preserves `U = range ι` and `Λ` lies in the closure of the points whose null direction is
an eigenline of some `L(γ)`, `γ ∈ Γ`, of eigenvalue `l > 0`, `l ≠ 1`, then `Ω⁺(Λ)` and `Ω⁻(Λ)`
are invariant under the translations by `U^⊥`. -/
theorem add_perp_mem_omega_of_preserves {d d₁ : ℕ} (ι : AffineMinkEmbedding d₁ d) {Γ : Subgroup (isom d)}
    (hpres : ∀ γ ∈ Γ, (fun p => γ • p) '' Set.range ι = Set.range ι)
    {Λ : Set (PenroseSphere d × ℝ)}
    (hΛ : Λ ⊆ closure {w : PenroseSphere d × ℝ | ∃ γ ∈ Γ, ∃ l : ℝ, 0 < l ∧ l ≠ 1 ∧
      linOf γ (nullVec w.1) = l • nullVec w.1})
    {v : Minkowski d} (hv : v ∈ ι.perp) :
    (∀ p ∈ omegaPlus Λ, p + v ∈ omegaPlus Λ) ∧ (∀ p ∈ omegaMinus Λ, p + v ∈ omegaMinus Λ) := by
  have hclosed : IsClosed {w : PenroseSphere d × ℝ | minkB (nullVec w.1) v = 0} :=
    isClosed_eq (continuous_minkB_nullVec_param v) continuous_const
  have hgen : {w : PenroseSphere d × ℝ | ∃ γ ∈ Γ, ∃ l : ℝ, 0 < l ∧ l ≠ 1 ∧
      linOf γ (nullVec w.1) = l • nullVec w.1} ⊆
      {w : PenroseSphere d × ℝ | minkB (nullVec w.1) v = 0} := by
    rintro w ⟨γ, hγ, l, hl0, hl1, hn⟩
    exact pinv_minkB_eq_zero ι (hpres γ hγ) hl0 hl1 hn hv
  have hΛv : ∀ w ∈ Λ, minkB (nullVec w.1) v = 0 := fun w hw =>
    closure_minimal hgen hclosed (hΛ hw)
  have hadd : ∀ w ∈ Λ, ∀ p : Minkowski d,
      minkB (nullVec w.1) (p + v) = minkB (nullVec w.1) p := fun w hw p => by
    rw [minkB_add_right, hΛv w hw, add_zero]
  refine ⟨fun p hp => mem_omegaPlus.2 fun w hw => ?_, fun p hp => mem_omegaMinus.2 fun w hw => ?_⟩
  · rw [hadd w hw]; exact mem_omegaPlus.1 hp w hw
  · rw [hadd w hw]; exact mem_omegaMinus.1 hp w hw

end Causal.Flat.Lox
