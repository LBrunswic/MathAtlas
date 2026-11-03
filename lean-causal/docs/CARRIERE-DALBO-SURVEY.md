# Carrière–Dal'bo survey: Thm 5.1 (`bthm:ausl`) and Prop 5.2 (`bthm:unip`)

Survey of 2026-11-03, read-only, against lean-causal at `d29f400` (Selberg is proved at `8b3ec2d`).
It synthesises three research passes (Auslander route search, unipotent-subspace route search,
consumption audit) plus the synthesizer's own checks of the Lean sources and of the
Fried–Goldman–Hirsch text. Throughout, **[src]** marks what a source says, **[repo]** marks what
was read in this repository, and **[inf]** marks inference by a researcher or by the synthesizer
that no source states.

**What was and was not read.** The Carrière–Dal'bo paper itself was **not read**: e-periodica
serves its PDF only behind a captcha. Its content is known from the zbMATH review (Zbl 0697.20037,
fetched through the zbMATH API), from Carrière's 1988 survey, and from Barbot's citation.
Fried–Goldman–Hirsch 1981 §1 **was** read; Lemmas 1.1, 1.4 and 1.6 were re-checked verbatim for
this file. Raghunathan, Auslander 1963 and Abels 2001 were **not** accessed.

---

## TL;DR

1. **Prop 5.2 can be proved outright, as stated, for every nilpotent N ≤ Isom(𝐌ⁿ).** Use
   Fried–Goldman–Hirsch's Fitting-submodule argument. Uniqueness and maximality hold for *every*
   group and cost nothing. The only content is one cohomology fact: H¹(N; W) = 0 when N is
   nilpotent and W^N = 0. It has an elementary proof by induction on the centre. Estimate
   ~600–1000 lines, independent of Thm 5.1. **Do this first.**
2. **Thm 5.1 has no published short proof.** It does have an elementary Lorentz-specific route
   ("Lorentz Zassenhaus–Frobenius"). It proves the formalized `AusConclusion` exactly, reuses
   TitsNull, BieberbachZassenhaus, Gromov and Bieberbach Item 1, and needs no Lie theory.
   Estimate 2–3k lines in 2–3 waves. Its single hard core is the lemma (★): there is an ε > 0
   such that elements of L(Γ) within ε of 1 commute.
3. Narrowing Thm 5.1 to what is consumed (conjunct 2 only, k = d only, or the nonelementary
   "G₀ compact" form M1) **does not remove the hard core**. It is worth doing only as statement
   hygiene.

---

## 1. The statements and how they are consumed

### 1.1 As printed (Barbot, `GHFspace.tex`)

- **Thm 5.1, `bthm:ausl`, l.1696–1704 [src].** Let Γ be a discrete subgroup of Aff(n, ℝ). Then the
  identity component G₀ of the closure of L(Γ) in GL(n, ℝ) is nilpotent. "In particular",
  Γ_nd = L⁻¹(G₀ ∩ L(Γ)) is nilpotent. Cited as a refinement by Carrière–Dal'bo of Auslander's
  theorem, [cardal] Thm 1.2.1.
- **Prop 5.2, `bthm:unip`, l.1709–1717 [src].** Let Γ be a nilpotent group of affine
  transformations of ℝⁿ. Then there is a maximal Γ-invariant affine subspace **U** on which the
  action is unipotent, and it is unique. Cited as [cardal] Prop 1.2.2.
- The zbMATH review of [cardal] states the theorem in its own form [src]: for every discrete
  Γ ≤ Aff(ℝⁿ), Γ_nd = Γ ∩ L⁻¹(L(Γ) ∩ cl(L(Γ))₀) is nilpotent, and it is unipotent when Γ is
  crystallographic. The review also mentions a polynomial-growth approach and a proof of
  Goldman–Kamishima. So the "G₀ nilpotent" form is Barbot's; it follows from Γ_nd nilpotent by
  taking closures [inf].

### 1.2 As formalized (`Causal/Flat/Externals.lean`) [repo]

- `linClosureIdentityComponent Γ := connectedComponentIn (closure L(Γ)) 1` (l.267). The closure
  is taken in `lorentz d` = SO₀(1, d). It agrees with the closure in GL because SO₀(1, d) is
  closed.
- `nonDiscretePart Γ := Γ ⊓ (Subgroup.closure G₀).comap linearPart` (l.272). Barbot's Γ_nd is
  recovered, since G₀ is already a subgroup.
- `AusConclusion Γ := IsNilpotent (closure G₀) ∧ IsNilpotent (nonDiscretePart Γ)` (l.276).
- `AuslanderCarriereDalbo d := ∀ Γ, DiscreteTopology Γ → AusConclusion Γ` (l.283). The topology
  is `isomTopology`. The statement is restricted to Isom(𝐌ⁿ), which is weaker than the printed
  Aff(n, ℝ) form.
- `IsUnipotentInvariant N U`: U is N-invariant, and for each γ ∈ N some power of L(γ) − id kills
  dir U. `IsMaxUnipotent N U` says U is maximal among such subspaces.
- `MaxUnipotentSubspace d`: every nilpotent N ≤ isom d has a **nonempty** U with
  `IsMaxUnipotent N U`, and every maximal U′ equals U (l.321). Nonemptiness is explicit, which
  is necessary: ⊥ is always unipotent-invariant.
- Witnesses already in the file: d = 0 for both; abelian Γ for `AusConclusion`;
  `not_maxUnipotent_conclusion_top`, showing that N = ⊤ (not nilpotent) has no nonempty
  unipotent-invariant subspace.

### 1.3 Where they are spent [repo, verified by grep at `d29f400`]

**One live use site.** `Classification.caseOutput` (l.561) passes
`hE.auslander d le_rfl` and `hE.unipotent d le_rfl` to `caseOutput_generic`. That is the
loxodromic, **nonelementary** branch, at dimension k = d only. The path continues through
`loxo_generic_centralExtension` (Loxodromic.lean:3393) to `exists_generic_reduction`
(Loxodromic.lean:3063). Inside that funnel:

| step (file:line) | what of Thm 5.1 it uses | what of Prop 5.2 it uses | minimal statement it needs |
|---|---|---|---|
| `exists_invariant_maxUnipotent` (Externals:501) | conjunct 2 (Γ_nd nilpotent), as Prop 5.2's input | existence, nonempty, `IsMaxUnipotent`, **uniqueness** (spent for Γ-invariance through `conj_mem_nonDiscretePart`) | a nonempty maximal Γ_nd-unipotent U that is Γ-invariant |
| `bprop_U_timelike` (Loxodromic:2415) | conjunct 2, pushed to L(Γ_nd) nilpotent for `Lox.exists_finiteIndex_fix_of_nilpotent_normal` (l.2450) | maximality, only through `IsMaxUnipotent.mem_direction_of_linFixed`; the uniqueness call at l.2425 is redundant, since U already comes from the row above | L(Γ_nd) nilpotent; Fix L(Γ_nd) ⊆ dir U |
| `Lox.exists_restrictsIn_ge` (RestrictUnipotent:101) | — | `hmax.1.2` (Γ_nd unipotent on U), used only to get Γ_nd ≤ Γ₂ | Γ_nd acts unipotently on U |
| `bprop_LU_discrete` (Loxodromic:2640) | conjunct 2, via `UnipotentCentre` (l.114–126): L_U(Γ_nd) nilpotent and unipotent, so its centre contains a parabolic | `hU` unused; `hmax` used as given | L_U(Γ_nd) nilpotent (on the branch L_U(Γ_nd) ≠ ⊥ only) |

**Not on the A/B path** (per the consumption pass; the first two were spot-checked):

- `Nonloxodromic.lean:1883/1900` are unused alternatives, superseded by TitsNull.
- `NilpotentFix.lean:204` is an `example`.
- §5.1's Bieberbach recovery is replaced by the proved Bieberbach.
- §10's Misner case is replaced by `loxo_elementary_misner`, which does not carry
  `MaxUnipotentSubspace` (Loxodromic:313).
- `loxo_generic_torusProduct` has no caller.

**Consequences:**

- **Conjunct 1 of `AusConclusion` (G₀ nilpotent) is never consumed.** Every call takes `.2`.
- **The bundles' `∀ k ≤ d`** (Classification:347–348, GromovProof:115–116,
  BieberbachProof:110–111) **is stronger than needed.** Only k = d is used for these two fields.
  The lower-dimensional AMGH lemmas use `benoist` only.
- **Nonelementarity is available at the use site.** This is what makes the narrower M1 form
  (§2.3) possible.

---

## 2. Routes, ranked

Ranking criteria: correctness first, then Lean cost given the library, then reuse of
BieberbachZassenhaus, TitsNull, GromovProof and ClosedSubgroupNhds.

### 2.1 Prop 5.2 (`MaxUnipotentSubspace`)

#### P1. Fitting submodule + H¹ vanishing by centre induction — RECOMMENDED

**Source [src].** Fried–Goldman–Hirsch 1981, §1:

- Lemma 1.1 (credited to Hirsch 1977; see also Dwyer 1975): for G nilpotent, H⁰(G; E) = 0
  implies Hⁱ(G; E) = 0 for all i.
- The Fitting submodule E_u: "there is a unique maximal submodule E_u ⊂ E upon which G acts
  unipotently".
- Lemma 1.4: H⁰(G; E/E_u) = 0.
- Lemma 1.6: if G is nilpotent, some coset of E_u is invariant. The proof: the translational
  part mod E_u is a crossed homomorphism, and H¹ = 0 by 1.1 and 1.4.

The three lemmas were re-read verbatim from the FGH text for this file.

**Idea, in affine form [inf; checked by the synthesizer].**

*Group-agnostic part.* This holds for any subgroup N, nilpotent or not.

- Define V₁ := ⨅_{γ∈N} maxGenEigenspace(L γ, 1).
- V₁ is L(N)-invariant: h·V₁(γ) = V₁(hγh⁻¹), and conjugation permutes N.
- Let F := {x | ∀γ ∈ N, γx − x ∈ V₁}.
- Every `IsUnipotentInvariant N U` satisfies U ⊆ F. Indeed dir U ⊆ V₁, and γx − x ∈ dir U.
  This includes U = ⊥.
- F is empty or a single coset of V₁. If x, y ∈ F, then (Lγ − 1)(x − y) ∈ V₁, so x − y lies in
  every maxGenEigenspace(Lγ, 1), that is, in V₁. This is FGH 1.4 in affine form.
- x₀ + V₁ is unipotent-invariant.
- Hence, if F ≠ ∅, x₀ + V₁ is the **greatest** unipotent-invariant subspace. Maximality, and
  uniqueness among maximal subspaces, follow at once.
- If F = ∅, ⊥ is the unique maximal one. The uniqueness clause therefore never fails.

*The only content: F ≠ ∅.* Work in W := Minkowski d ⧸ V₁. Here W^N = 0. Show that the cocycle
u(γ) := trOf γ mod V₁ is a coboundary δw; then x₀ := −w.

*The H¹ lemma.* For G nilpotent and W finite-dimensional over a field, W^G = 0 implies that every
1-cocycle is a coboundary. This proof is a synthesis, not FGH's text; FGH cite Hirsch and Dwyer.
It uses an outer induction on nilpotency class (`Group.nilpotent_center_quotient_ind`,
Nilpotent.lean:900) and an inner strong induction on dim W.

- **Case A: some central z is non-unipotent on W.**
  - Fitting-decompose W = ker(z−1)ⁿ ⊕ range(z−1)ⁿ. Both summands are N-invariant because z is
    central.
  - On the range, z − 1 is invertible. From zg = gz we get (z−1)u(g) = (g−1)u(z), so
    u = δ((z−1)⁻¹u(z)).
  - The kernel is proper, so the dimension induction applies.
- **Case B: the centre Z acts unipotently.**
  - Commuting unipotents have a common fixed vector, so W^Z ≠ 0.
  - Let φ be a cocycle with values in W^Z. Then (g−1)φ(z) = (z−1)φ(g) = 0, so φ(z) ∈ W^N = 0.
    Hence φ factors through N/Z, and the class induction applies to W^Z.
  - The same identity applied to φ = δw shows (W/W^Z)^N = 0.
  - Run the dimension induction on W/W^Z, then correct inside W^Z.

The synthesizer re-derived each step and found no gap. The proof needs no finite generation, no
Zariski closure, no Jordan decomposition and no group-cohomology library.

**Ingredients at the pin [repo; the consumption and unipotent passes checked that each exists].**

- `Module.End.maxGenEigenspace`, `maxGenEigenspace_eq` (Eigenspace/Basic.lean:559).
- `LinearMap.eventually_isCompl_ker_pow_range_pow` (Artinian/Module.lean:317–326).
- `Group.nilpotent_center_quotient_ind`.
- `Submodule.mapQ`, `QuotientGroup.lift`.
- Use bare cocycle predicates, not the `groupCohomology` Rep machinery.

**Cost.** ~600–1000 lines:

- (a) V₁ and its invariance: ~60.
- (b) The greatest-element wrap-up into `IsMaxUnipotent` / `MaxUnipotentSubspace`: ~150–250.
- (c) The generic H¹ lemma: ~350–600.

State (c) for an arbitrary `Group G` acting on a `Module K W`, then instantiate it at ↥N acting
on Minkowski d ⧸ V₁.

**Risks.**

- Plumbing: the motive of `nilpotent_center_quotient_ind` ranges over `G : Type*`, so the
  instantiation is at ↥N; the action of N/Z on W^Z needs `QuotientGroup.lift`.
- The inner dimension induction must sit inside the outer class step, because Case B's
  (W/W^Z)^N = 0 uses the class hypothesis.
- **Do not use per-element weight decompositions.** For a non-connected nilpotent group, the
  generalized eigenspaces of a single g need not be N-invariant. Counterexamples: D₈ on ℝ²,
  where ker(s−1) is not r-invariant, and Q₈. Only the joint V₁ and central elements are safe.

**Faithfulness.** It proves `MaxUnipotentSubspace d` exactly as stated, for every d, and closes
the ledger row as printed.

#### P0 (sub-route, do first inside P1): "F ≠ ∅ ⇒ conclusion"

This is the group-agnostic half of P1, as a standalone lemma: for any N ≤ isom d, if some x₀
satisfies γx₀ − x₀ ∈ V₁ for all γ ∈ N, then x₀ + V₁ is nonempty, `IsMaxUnipotent`, and unique.

- Cost ~200 lines; minimal risk.
- The definition quantifies m per γ; supply m = finrank via `maxGenEigenspace_eq`.
- Value: it isolates all remaining work in a single cocycle statement, and it is reusable.

#### P2. Elimination of Prop 5.2 given M1, via the proved Bieberbach

**Source.** Consumption pass [inf]. This route removes Prop 5.2 from A/B rather than proving it.

**Idea.**

- Assume M1 (§2.3): L(Γ_nd) fixes a timelike u.
- Then L(Γ_nd) preserves the positive-definite form B_u, so Γ_nd is a discrete Euclidean group.
- Bieberbach (`bieberbachI` / `BieberbachMaxConclusion`) gives a finite-index subgroup acting by
  translations on some U′.
- cl L(Γ_nd) is connected (local Cartan + `FiniteIndexND`). So P := {x | ∀η ∈ Γ_nd, ηx − x ∈ Fix}
  is nonempty, after passing to a normal core.
- P is Γ-invariant and timelike, and Γ_nd acts on P by translations.
- `discreteTopology_restrictGroup_of_nonDiscretePart_bot` then gives discreteness. NilpotentFix,
  UnipotentCentre and uniqueness are all bypassed.

**Cost.** 400–800 lines. The transport of Γ_nd into `AffineIsometryEquiv` for B_u, with matching
topologies, is the fiddly part.

**Ranking.** Below P1. It depends on M1 (still an external), it changes the proof architecture,
and P1 is comparable in cost while proving the statement as printed. Keep it as the fallback if
P1's plumbing stalls.

#### Rejected for Prop 5.2

- **Carrière–Dal'bo's own proof.** Not retrieved, content unknown; P1 does not need it.
- **Algebraic hull / Zariski closure, T × U Jordan structure (FGH's remark after 1.7; Fried–Goldman
  1983).** Needs algebraic-group infrastructure that mathlib lacks. Thousands of lines.
- **Lorentz case split via GromovProof.** It re-proves P1's H¹ vanishing case by case on top of
  Barbot's §6 normal forms. The ledger records those normal forms as overlapping, and Lemma 7.1
  as false for n ≥ 4.

### 2.2 Thm 5.1 (`AuslanderCarriereDalbo`)

#### Reduction common to the good routes: everything follows from (★_Γ)

The synthesizer checked Route A's Steps 3–5 below and found them sound. They show that both
conjuncts follow from one statement:

> **(★_Γ)** For discrete Γ ≤ isom d there is ε > 0 such that any two elements of L(Γ) within ε of
> 1 commute.

ε may depend on Γ. The research pass aimed at a uniform ε₀ (~1/64), which is stronger than
needed. The three steps, with Γ_ε := ⟨γ ∈ Γ : ‖L(γ) − 1‖ < ε⟩:

- **Step 3: G₀ is abelian, which gives conjunct 1.**
  - Let O := cl L(Γ_ε) ∩ cl L(Γ). It is a subgroup containing cl L(Γ) ∩ B(1, ε), so it is open,
    hence clopen, hence contains G₀.
  - O is abelian, by `lorentz_closure_comm` applied to the abelian L(Γ_ε).
  - Then apply `isNilpotent_closure_of_comm`.
- **Step 4: Γ_nd ≤ Γ_ε.**
  - L(Γ) ∩ cl L(Γ_ε) = L(Γ_ε). If y_k → x with y_k ∈ L(Γ_ε) and x ∈ L(Γ), then y_k⁻¹x ∈ L(Γ) is
    near 1.
  - The translation kernel K = Γ ∩ ker L lies in Γ_ε.
- **Step 5: Γ_ε is nilpotent, which gives conjunct 2.**
  - L(Γ_ε) is abelian, so [Γ_ε, Γ_ε] ≤ K.
  - K is a lattice in V_K (Bieberbach Item 1: `discreteSubmodule_free/finite`).
  - Take a generator γ (ε < 1 suffices) and v ∈ K. Then (L(γ) − 1)^m v ∈ K and its norm is at most
    ε^m‖v‖, so it is eventually 0.
  - Commuting nilpotents generate a nilpotent algebra (mathlib's Engel, or a direct flag
    argument).
  - Hence [K, Γ_ε, …, Γ_ε] = 1, with dim V_K copies of Γ_ε, and class(Γ_ε) ≤ dim V_K + 1.

These three steps are purely topological and linear-algebraic: ~500–900 lines, no Lie theory.
**The whole difficulty of Thm 5.1 is (★_Γ).**

#### T1. Route A, "Lorentz Zassenhaus–Frobenius" — RECOMMENDED

**Source.** A synthesis [inf]. It draws on:

- Carrière–Dal'bo's commutator-contraction method. Carrière's 1988 survey [src] calls CD's proof
  "in the same spirit" as Buser's geometric proof of Bieberbach, which is "inspired directly" by
  Gromov's.
- Zassenhaus' lemma (Raghunathan Ch. VIII; Thurston §4.1).
- The library's own Euclidean and null-screen versions.

The decomposition into steps is the research pass's, not a source's.

**Step 1: local nilpotency from discreteness.**

- Let g, h ∈ Γ have linear parts near 1.
- Conjugate by the dilation x ↦ x/K (TitsNull's `affExt` / `scaleBy`, or BieberbachZassenhaus'
  `euclAffExt K`). This puts g^{±1} and h^{±1} within 1/32 of 1 in the extended-matrix norm.
- `norm_commutator_le_half` (TitsNull:600) bounds every weight-k left-normed commutator in the
  set by 3·2^{−(k−1)}. Unscaling costs a factor K, and the bound still tends to 0.
- So `exists_affExt_isolated` (TitsNull:1073) kills all those commutators of weight ≥ k₀.
- A group-theory lemma closes the step: γ_k(⟨S⟩) is generated by the left-normed commutators of
  weight ≥ k in S^{±1} (Hall; Magnus–Karrass–Solitar). Hence ⟨g, h⟩ is nilpotent. Its class
  depends on the pair, which does not matter, because Step 2 converts nilpotency into
  commutation.

**Step 2: Lorentz Frobenius lemma, with no discreteness.** Claim: if N ≤ SO₀(1, d) is nilpotent
and a, b ∈ N are within ε₀ of 1, then ab = ba. Apply GromovProof's dichotomy to N:

- **N fixes a timelike w.** N lies in the compact group O(w^⊥). Use Frobenius plus backward
  induction (`commute_of_commute_conj_linearIsometryEquiv` BZ:99,
  `commute_linearPart_of_iterate_eq_one` BZ:136), starting from [a,ₙ b] = 1.
  - Constants transfer through fact (F): for an orthogonal a on w^⊥, the deviation from 1 in the
    intrinsic norm is max|e^{iθ} − 1| = ρ(a − 1), and this is at most ‖a − 1‖ in any operator
    norm.
  - (F) is a synthesizer-checked derivation.
- **N fixes a null v₀ and has no loxodromic.** Then λ ≡ 1.
  - The screen rotations commute, by `commute_screenRot_of_iterate_eq_one` (TitsNull:932).
  - So c = [a, b] is a null rotation by some z. The Engel conditions force
    (ρa − 1)z = (ρb − 1)z = 0, since ρ is orthogonal and hence semisimple.
  - But z ∈ Im(ρa−1) + Im(ρb−1), which is orthogonal to ker(ρa−1) ∩ ker(ρb−1). So z = 0.
- **N contains a loxodromic ℓ.**
  - Nilpotency forces every element to preserve {ℓ⁺, ℓ⁻}: a swap would give an infinite
    dihedral subgroup, and moving an endpoint gives ax+b or free behaviour, neither nilpotent.
  - So N ≤ A × M, where A is central and the M-parts commute by intrinsic Frobenius on the
    complement of the axis plane.
  - **This case is argued on paper only.**

Applying Step 2 to N = L(⟨g, h⟩) gives (★_Γ), even with a uniform ε₀. Steps 3–5 then finish.

**Ingredients.**

- Library: TitsNull (halving, `affExt`, isolation, screen-rotation Frobenius); BieberbachZassenhaus
  (Frobenius, backward induction); GromovProof / GromovBounded / GromovUnbounded; `Externals`
  (`lorentz_closure_comm`, `isNilpotent_closure_of_comm`); `FiniteIndexND`
  (`lorentz_isTopologicalGroup`); Bieberbach Item 1; the Lox/ API (elliptic, parabolic,
  loxodromic, null rotations).
- New:
  - (i) The Hall γ_k lemma.
  - (ii) Multi-generator halving.
  - (iii) The loxodromic case of Step 2 (fixes ℓ±; A × M plumbing).
  - (iv) Fact (F) for w^⊥, the axis complement and the screen.
  - (v) The z = 0 step.
- ClosedSubgroupNhds (local Cartan) is not needed.

**Cost.** Total ~2–3k lines, 2–3 waves, comparable to TitsNull + BieberbachZassenhaus combined:

| step | lines | note |
|---|---|---|
| 1 | 400–700 | about half is the Hall lemma |
| 2 | 900–1500 | the loxodromic case is the heaviest |
| 3–5 | 500–900 | |

Steps 1 and 2 are independent packages. Step 2 is a discreteness-free statement about nilpotent
subgroups of SO₀(1, d), so the two can run in parallel.

**Risks.**

- Step 2's loxodromic case is unformalized and may be the plumbing-heaviest part.
- **Do not try to skip Step 1** by using only the cheap pairwise Engel property. In the
  elliptic–elliptic case with distant fixed points, pairwise Engel gives no common fixed point
  and therefore no Frobenius constant.
- Check the scaled extension's inverse bounds against `norm_commutator_le_half`'s hypotheses
  (δ ≤ 1/32, m ≤ 3).
- The side remark that connected nilpotent subgroups of SO₀(1, d) are abelian is derived, not
  sourced. Route A does not use it.

**Faithfulness.** Proves `AusConclusion` exactly, both conjuncts, every d, no new externals.

#### T1′. Variant of T1 that shortens two of Step 2's cases [inf, synthesizer]

Use local Cartan (`exists_nhds_subset_connectedComponentIn_closure`, ClosedSubgroupNhds:409) to
pick ε with L(Γ) ∩ B(1, ε) ⊆ G₀. Then apply the Gromov dichotomy **once**, to G₀, instead of once
per pair:

- **G₀ bounded, fixing a timelike w.** Γ ∩ L⁻¹(Stab w) is a discrete group of B_w-Euclidean
  isometries. BieberbachZassenhaus' `commute_linearPart_of_near_one` (BZ:334), transported with
  fact (F), gives (★_Γ) directly: no Step 1, no Hall lemma.
- **G₀ fixes a null v₀ and has no loxodromic.** TitsNull's `exists_commute_screenRot_of_discrete`
  (TitsNull:1554, uniform 1/64) applied to Γ ∩ L⁻¹(Stab v₀), plus the z = 0 step with the
  **pairwise** Engel property, gives (★_Γ).
- **G₀ contains a loxodromic.** The near-1 generators may all be elliptic with no common fixed
  point. Here Step 1 and Step 2's loxodromic case appear to be unavoidable. No cheaper argument
  was found.

So T1′ does not remove the Hall lemma. It does make waves 1–2 deliver a fully proved Thm 5.1 for
every Γ whose G₀ contains no loxodromic, which is a useful intermediate checkpoint. Unverified;
treat it as a scheduling option.

#### T2. Homothety conjugation + strong Zassenhaus neighbourhood — the classical proof

**Sources.** Zassenhaus 1938; Raghunathan Ch. VIII; Thurston §4.1. CD is reported to argue in this
spirit.

**Idea.**

- Dilation-conjugate a finite F ⊂ Γ_W into a Zassenhaus neighbourhood Ω.
- Strong Zassenhaus places ⟨Γ′ ∩ Ω⟩ inside a connected nilpotent Lie subgroup, so the class is
  at most dim Aff(n).
- A uniform class bound turns local nilpotency into nilpotency.

This is valid for all of Aff(ℝⁿ).

**Cost and risk.**

- The weak half is Route A's Step 1. The uniform class bound needs a log chart, BCH and
  connected-subgroup theory: 3–6k lines, high risk.
- Without the class bound, one only gets local nilpotency, which does not imply nilpotency. The
  Prüfer quaternion group is locally nilpotent and linear.
- The exact form and number of Raghunathan's strong statement are unverified.

#### T3. Auslander solvability, then rank-one elimination

**Sources.** Auslander 1963; Raghunathan Thm 8.24, quoted by Fried–Goldman 1983 §2 [src]: "for
any discrete subgroup Γ ⊂ Aff(E) the group cl(L(Γ))⁰ is solvable".

**Assessment.** Highest cost (5k+): Lie subalgebras of closed subgroups, the radical,
Lie–Kolchin. It also still needs Steps 4–5 afterwards. Fried–Goldman remark that a *different*
Auslander paper, on the virtual-solvability conjecture, is incorrect. If cited, cite
Raghunathan's proof.

#### T4. Gromov/Buser short-basis proof

**Source.** Buser 1985; Gromov 1978.

**Assessment.** For Euclidean Γ this is what the library already did (DEC-110). For Lorentz Γ it
collapses to either T2 (needs a class bound) or T1 (rank-one structure). Whether CD's actual
proof uses Gromov's class bound is unknown.

#### T5. Polynomial growth — REJECTED

The idea would be to apply Gromov's polynomial-growth theorem to a hull. It fails on three
counts:

- Isom(𝐌ⁿ) has exponential growth.
- Proving that the relevant hull has polynomial growth presupposes G₀ nilpotent, which is
  circular.
- It yields "virtually nilpotent", not "Γ_nd nilpotent".

### 2.3 Narrowing what is carried (not a proof)

- **N1: carry conjunct 2 only, at k = d only.** A statement change of tens of lines, plus a DEC
  entry. Conjunct 1 follows from conjunct 2 anyway: L(Γ) ∩ G₀ is dense in G₀, and the closure of
  a nilpotent group is nilpotent, a ~150-line lemma not found at the pin.
- **N2: M1 ("AusCompact_d").** For discrete Γ with `IsNonelementary Γ`, L(Γ_nd) fixes a timelike
  vector; equivalently, G₀ is compact.
  - M1 follows from conjunct 2 with library pieces only: NilpotentFix plus the lightlike exclusion
    of `bprop_U_timelike`.
  - With P2 it would replace both externals at the single live site.
  - **Nonelementarity cannot be dropped** (§4).
  - **But M1's proof contains the same hard core.** The case "G₀ contains a loxodromic" must still
    be excluded, and under nonelementarity the elementary subcases die cheaply: the fixed boundary
    set of G₀ is L(Γ)-invariant. What remains is "G₀ nonelementary", which is exactly what
    (★_Γ) excludes.
  - Narrowing therefore saves no hard mathematics. It only trades a faithful statement for a
    bespoke one.
- **Do not weaken to "solvable" or "locally nilpotent".** Prop 5.2 is false for solvable groups:
  ⟨x ↦ 2x, x ↦ x+1⟩ on ℝ has no nonempty unipotent-invariant subspace. NilpotentFix and
  UnipotentCentre induct along the upper central series.

---

## 3. Recommended plan

1. **Wave 1: Prop 5.2 in full, faithful form (P0 then P1).**
   - Prove the generic H¹ lemma in its own module (e.g. `Flat/HirschH1.lean`), over an arbitrary
     group and field.
   - Then P0's greatest-element lemma, then instantiate to discharge `MaxUnipotentSubspace d` for
     every d.
   - This removes one of the two open ledger rows exactly as printed. No statement change, no DEC
     beyond the proof record.
   - It does not depend on Thm 5.1.
   - Optional cleanup: drop the redundant uniqueness call at Loxodromic:2425.
2. **Wave 2: Thm 5.1, Steps 3–5 first, with (★_Γ) as a named, isolated hypothesis.**
   - Prove `(★_Γ) → AusConclusion Γ` (~500–900 lines).
   - This fixes the interface and shows that nothing else is missing.
3. **Waves 2–3: (★_Γ) by Route A.** Run Step 1 (Hall lemma + multi-generator halving) and Step 2
   (Lorentz Frobenius for nilpotent N ≤ SO₀(1, d)) in parallel. If scheduling favours it, land
   T1′'s bounded and null cases first as a checkpoint.
4. **Statement hygiene, independent of the above.**
   - Replace the bundles' `∀ k ≤ d` by k = d for `auslander` / `unipotent`, and record that
     conjunct 1 is unused.
   - Do **not** switch to M1 unless T1's loxodromic case fails. In that case:
     - M1 + P2 is the fallback architecture;
     - the residual external becomes "nonelementary ⇒ G₀ compact", which is sharper but
       non-literal and needs a DEC entry.
5. **Ask a human** to download the Carrière–Dal'bo PDF through a browser:
   https://www.e-periodica.ch/digbib/view?pid=ens-001:1989:35::412. Their Thm 1.2.1 proof may
   contain an Isom(𝐌ⁿ)-specific shortcut that no pass could check. Nothing above depends on it.

---

## 4. Counterexamples and flaws in the formalized statements

**No counterexample to either Prop as formalized was found.** Findings:

1. **`MaxUnipotentSubspace` is true, and its uniqueness clause holds for every group.** Nilpotency
   buys only nonemptiness (§2.1 P1, P0). The explicit `Nonempty` conjunct is therefore the
   correct and necessary strengthening of the printed wording: ⊥ is always unipotent-invariant.
   Sanity checks:

   | N | maximal unipotent subspace U |
   |---|---|
   | {1} | 𝐌ⁿ |
   | elliptic rotation R | Fix R |
   | screw motion | its axis |
   | ⟨g^m⟩, g^m a translation | 𝐌ⁿ |
   | ⊤ | none nonempty (F = ∅), matching `not_maxUnipotent_conclusion_top` |

   The ⟨g^m⟩ row agrees with ledger [5.B], line 168.
2. **`AuslanderCarriereDalbo` is a faithful restriction.**
   - The printed Aff(n, ℝ) form is restricted to Isom(𝐌ⁿ). The closure is taken in SO₀(1, d),
     which is closed, so it equals the GL closure. `nonDiscretePart` uses the subgroup generated
     by G₀, which equals G₀.
   - No defect, but it is over-strong for its consumer: conjunct 1 is unused, and so is k < d.
3. **"G₀ compact" (M1) is NOT a consequence of Thm 5.1 without nonelementarity.** Counterexample
   (consumption pass; the synthesizer checked discreteness), for d ≥ 2:
   - Γ = ⟨(B_a, e), (B_b, θe)⟩ ≅ ℤ², where B_s are boosts in one timelike plane, e is spacelike
     and orthogonal to that plane, a/b is irrational, and aθ ≠ b.
   - Γ is abelian, and discrete because (m, n) ↦ (ma + nb, m + nθ) is a lattice.
   - G₀ is the whole one-parameter boost group: abelian, consistent with Thm 5.1, and
     non-compact.
   - So any M1 rewording must keep `IsNonelementary`.
4. **Pitfall for proofs, not a flaw in the statements.** Per-element generalized eigenspaces of a
   nilpotent N are not N-invariant when N is not connected: D₈ on ℝ², Q₈. The research brief's
   per-element decomposition ("Lemma K") is false in that generality. Only V₁ (the joint
   1-eigenspace) and central elements may be used.
5. **Already in the ledger:**
   - [5.B], line 45: the kernel of Γ → Isom(U) is finite, not of finite index.
   - [5.B], line 169: the maximal unipotent U and the cocompact U are different subspaces.
6. **Unverified side claim.** "Connected nilpotent subgroups of SO₀(1, d) are abelian" was derived
   by the Auslander pass from real-rank-one structure, with no source. It is not used by any
   recommended route, and is recorded only as the explanation of why (★) holds.

---

## 5. References

Read status: **read** = text read in this survey; **review** = known through a review or survey;
**not accessed** = cited from secondary sources only. DOIs were not verified and are not given;
URLs are the ones actually used.

- **[cardal]** Y. Carrière, F. Dal'bo, *Généralisations du premier théorème de Bieberbach sur les
  groupes cristallographiques*, Enseign. Math. (2) 35 (1989) 245–262. e-periodica
  https://www.e-periodica.ch/digbib/view?pid=ens-001:1989:35::412. The two passes recorded
  different pids for the article and its PDF (`::412`, `::115`, `::120`); check in a browser
  which one opens it. The PDF is captcha-blocked:
  **not read**. Barbot's bibitem is at GHFspace.tex:3779.
- J.-P. Pier, zbMATH review of [cardal], **Zbl 0697.20037**, via
  https://api.zbmath.org/v1/document/_search?search_string=an%3A0697.20037. **review**: gives the
  Γ_nd statement for Aff(ℝⁿ), the polynomial-growth approach, and Goldman–Kamishima.
- Y. Carrière, *Un survol de la théorie des variétés affines*, Séminaire de théorie spectrale et
  géométrie 6 (1987–1988) 9–22, https://www.numdam.org/item/TSG_1987-1988__6__9_0.pdf. **read** by
  the Auslander pass. It locates CD "dans le même esprit" as Buser's Gromov-inspired proof.
- F. Dal'bo, *Une géométrie sans métrique : la géométrie affine*, Séminaire TSG (1991),
  https://www.numdam.org/item/TSG_1991__S9__77_0. **review**.
- D. Fried, W. Goldman, M. W. Hirsch, *Affine manifolds with nilpotent holonomy*, Comment. Math.
  Helv. 56 (1981) 487–523, https://www.math.umd.edu/~wmg/NilpotentHolonomy.pdf. **read**, §1:
  Lemma 1.1, Thm 1.2, Lemma 1.4, Lemma 1.6, Thm 1.7. These are the source of route P1.
- M. W. Hirsch, *Flat manifolds and the cohomology of groups*, in Algebraic and Geometric
  Topology, LNM 664, Springer 1977. Source of FGH Lemma 1.1. **Not accessed.**
- W. G. Dwyer, *Vanishing homology over nilpotent groups*, Proc. Amer. Math. Soc. 49 (1975) 8–12.
  **Not accessed.**
- D. Fried, W. Goldman, *Three-dimensional affine crystallographic groups*, Adv. Math. 47 (1983)
  1–49, https://www.math.umd.edu/~wmg/ThreeDimAffCryst.pdf. **read** (§2, the Auslander and
  Raghunathan 8.24 quote).
- M. S. Raghunathan, *Discrete Subgroups of Lie Groups*, Ergebnisse 68, Springer 1972, Ch. VIII
  (Zassenhaus neighbourhoods; Thm 8.24). **Not accessed**; theorem numbers come from secondary
  quotes.
- L. Auslander, *On radicals of discrete subgroups of Lie groups*, Amer. J. Math. 85 (1963).
  **Not accessed.**
- P. Buser, *A geometric proof of Bieberbach's theorems on crystallographic groups*, Enseign.
  Math. 31 (1985) 137–145. **review**, via Carrière.
- M. Gromov, *Almost flat manifolds*, J. Differential Geom. 13 (1978) 231–241. **Not accessed.**
- W. Goldman, Y. Kamishima, *The fundamental group of a compact flat Lorentz space form is
  virtually polycyclic*, J. Differential Geom. 19 (1984) 233–240. **review**.
- W. Goldman, M. W. Hirsch, G. Levitt, *Invariant measures for affine foliations*. Restates "H
  leaves invariant a unique coset of E_u". **review**.
- H. Abels, *Properly discontinuous groups of affine transformations: a survey*, Geom. Dedicata
  87 (2001). **Not read.**
- J. Danciger, T. Drumm, W. Goldman, I. Smilga, *Proper actions of discrete groups of affine
  transformations* (survey), https://math.umd.edu/~wmg/Margulis_final.pdf. **Context only.**
- W. Thurston, *Three-Dimensional Geometry and Topology* Vol. 1, §4.1; J. Ratcliffe, *Foundations
  of Hyperbolic Manifolds*. Zassenhaus lemma. **Not accessed.**
- W. Magnus, A. Karrass, D. Solitar, *Combinatorial Group Theory*, for the γ_k-generation lemma
  (Hall). Recalled; the exact theorem number is **unverified**.

**Repository sources**

- Barbot: `papers/barbot/legacy/labeled/GHFspace.tex` (l.1688–1735, 3270–3280, 3333–3388, 3779)
  and `papers/barbot/ledger/LEDGER.md` (l.45, 163–169, 367–368).
- lean-causal at `d29f400`:
  - `Causal/Flat/Externals.lean` (l.256–512)
  - `Classification.lean` (l.343–353, 551–570)
  - `Loxodromic.lean` (l.2201, 2359–2457, 2636–2670, 3063–3091)
  - `Lox/{NilpotentFix,UnipotentCentre,RestrictUnipotent,ClosedSubgroupNhds,FiniteIndexND}.lean`
  - `TitsNull.lean` (l.600, 932, 1013–1103, 1514–1568)
  - `BieberbachZassenhaus.lean` (l.99, 136, 185, 274, 334, 344)
  - `GromovProof.lean`, `GromovBounded.lean`, `GromovUnbounded.lean`
  - `BieberbachProof.lean`
- Mathlib at the pin: `GroupTheory/Nilpotent.lean:900`, `RingTheory/Artinian/Module.lean:317–326`,
  `LinearAlgebra/Eigenspace/Basic.lean:559`.
