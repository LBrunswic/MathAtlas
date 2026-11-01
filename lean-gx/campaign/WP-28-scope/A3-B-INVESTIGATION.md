# A3 at BTZ points without the thesis's hypothesis (B)

*Read-only investigation, 2026-11-01. This file is the only one written. Nothing here is a ruling.*

## 1. What A3 states, and where "(B)" comes from

**A3 in the design.** `lean-causal/docs/CBG-DESIGN.md`:
- l.51: `germExt : … -- A3, Sbierski Lemma 3.8 / cor:ext_continue, K⁻ AND K⁺ versions (no duality)`.
- l.60: "No time reversal: the time reverse of an E₀-manifold is not one (gx D-12(e)): A3/A4 stated in both directions."
- l.69: "Lemma 3.8 = A3 … Thm 3.6 = A4 + A3".
- l.86–87: gx discharges "(v) K± calculus at BTZ points".
- l.96 and l.105: package 5 carries the risk "BTZ points", and R3 is "K⁻ at BTZ points".

**A3 in Lean.** `lean-causal/scaffold/CausalScaffold/CBG/Geometry.lean`:
- l.232–246, `germExt_future`. Hypotheses:
  - `U : Opens M`, and `ψ` with `IsMor s t U ψ` and `InjOn ψ U`;
  - M, N, U and ψ(U) are all globally hyperbolic;
  - `S ⊆ U`, and S is a Cauchy surface of M and of U, and ψ '' S is a Cauchy surface of N and of ψ(U);
  - `p ∈ frontier U`, `p ∈ J⁺(S)`, and `MapClusterPt q (𝓝[U] p) ψ` (Sbierski Def 3.5, l.69).

  Conclusion: `∃ O φ, p ∈ O ∧ IsMor s t O φ ∧ φ p = q ∧ EqOn φ ψ (O ⊓ U)`.
- l.247–259, `germExt_past`: the same, with `p ∈ J⁻(S)`.

No (B)-type hypothesis appears in either field. That is deliberate. The SCOPE note at l.77–80 says: *"The thesis extends only under `J(Σ,p) ∖ {p} ⊂ N` (`prop:Cauchy_non_max`, `these.tex:6634–6640`); A3 asks it at every corresponding point."* The flag itself is in `lean-causal/campaign/WP-36a-CBGGeometry/REPORT.json` l.224: *"A3 at BTZ points without the thesis's hypothesis (B)"*.

**Hypothesis (B) in the thesis** (`papers/gx/sources/thesis/these.tex`). (B) is the hypothesis of `prop:Cauchy_non_max`, l.6634–6638:

> S'il existe $(p,q)\in C$ tels que $J_{M_1}(\Sigma_1,p)\setminus \{p\} \subset j_1(N)$; alors $N$ n'est pas maximale parmi les sous-extensions de Cauchy de $M_1$ et $M_2$.

It is only named "(B)" inside the proof, at l.6693:

> … car $J(\Sigma_1,p)\setminus\{p\}\subset N$ par hypothèse $(B)$ ;

It is used unnamed at l.6658:

> $N\cap \U_1$ est un ouvert contenant $J^-_{\U_1}(\phi_1(p))$ par hypothèse

The statement should read J⁻ ∖ {p}, since p ∉ N.

The label is a leftover. The only other "(B)"s in the thesis belong to `theo:causalite_engendre` (l.4956), which is unrelated.

**What (B) is for.** The thesis does not prove Sbierski's Lemma 3.8, which extends ψ at every corresponding point. It proves Thm 3.6 (non-maximality) in one step, at a single good point.
- (B) gives an acausal surface Σ′ ∋ p inside N ∪ {p}, and its Cauchy development D₁.
- Each inextensible curve of D₁ either meets Σ′ in N, or meets it at p with its past part in N (l.6693).
- From this the proof gets three things:
  - W₁ = D₁ ∩ N is connected, so a single g ∈ Isom(E_α) represents f on it;
  - W₁ = U₁ ∩ f⁻¹(W₂);
  - Σ is Cauchy in N ∪ D₁.

`prop:Cauchy_point_min` (l.6802ff) then produces a point satisfying (B) by walking down past null geodesics.

(B) is equivalent to Sbierski Lemma 3.9's conclusion J⁻(p) ∩ ∂U ∩ J⁺(Σ) = {p}. Proof: a causal curve from Σ ⊂ U to a point x ∉ U of J(Σ,p) leaves U at some b ∈ J⁻(p) ∩ ∂U ∩ J⁺(Σ). Then b = p, so x = p.

So in the design's split, (B) is **A4's hypothesis** (`slice_future`, l.264), not A3's. A3 is consumed without (B):
- Sbierski's Lemma 3.9 walks along boundary points using the extension to U ∪ C;
- Thm 3.6 uses `V ∩ ∂U ⊆ C` (pdf p.17), which means extension at every nearby corresponding point, and those points do not satisfy (B) individually.

Adding (B) to A3 would therefore break Sbierski's order.

## 2. (B) is automatic at a BTZ point in the future of Σ (the thesis proves it)

`lem:passe_pgcd` (l.6541–6554) says: for a Cauchy extension i : M → N and p ∈ ∂i(M) ∩ J⁺(i(Σ)),

> si $p\in \sing_{0}(M)$ alors $J_{N}(i(\Sigma),p)\setminus\{p\}\subset i(M)$.

This is exactly (B). The thesis uses it in that role at l.6836: *"P ne peut pas être dans sing₀(M) car sinon J⁻(Σ,P)∖{P} ⊂ j₁(N)"*.

A direct proof in the model. Work in E₀ = ℝ³ with metric −2dτdr + dr² + r²dθ².
- Along a future causal curve, r′ ≥ 0 and 2τ′r′ ≥ r′² + r²θ′². So f = τ − r/2 and h = τ + r are non-decreasing, and ∂_τ is null.
- J⁻(p) is the singular half-line below p (`lem:past_BTZ`, l.5772; B21 l.535).

Proof that (B) holds:
1. Let x* ∈ J(Σ,p) ∖ {p}. A causal curve from x* to p ends on the line, so it passes through y = (τ_p − ε, 0) inside the chart, with ε > 0.
2. Take x_n ∈ U with x_n → p. Since f(x_n) → τ_p > τ_y, we get y ≤ x_n for n large.
3. Pick σ ∈ Σ with σ ≤ x*. Then σ ≤ x* ≤ y ≤ x_n with σ, x_n ∈ U, and U is causally convex, so x* ∈ U. ∎

## 3. Does A3 hold at BTZ points without (B)? Yes, in both directions, by different proofs

Ingredients, all already owed by gx item (v) or by Level A/B:
- causal convexity of U and ψ(U);
- ≤ closed (GH);
- push-up, and ≪ open;
- compact diamonds (A2);
- `prop:K_calcul` (l.5817): K⁺ = I⁺ at BTZ points and K⁻ = J⁻ ∖ {p};
- `cor:K_injectif` (l.5838);
- B1 rigidity;
- B2 `localUnique_sing` (B21 `prop:isom_strong`, l.468; f is defined on reg of the neighbourhood only).

Use the corrected I⁺(p) = {r > 0, f > τ_p} locally (CBG-REVIEW (a)), not `BTZAxioms.Iplus_eq`.

### Future side (`germExt_future`, p ∈ ∂U ∩ J⁺(Σ), p ∈ sing₀)

1. **Choose O.** Take O = {f > τ_p − a, h < τ_p + a} in a chart at p, with a small. This shrinks to p, since r < 4a/3. It lies in J⁺(Σ), because (τ_p − a, 0) ≤ x for every x ∈ O.
2. **U ∩ O is connected.** Let x ∈ U ∩ O and set y_x = (f(x), 0).
   - The radial null curve s ↦ (f(x) + s/2, s, θ_x) joins y_x to x inside O, because f is constant and h increases along it.
   - It lies in U by causal convexity, since some σ ∈ Σ satisfies σ ≤ y_x.
   - y_x ≠ p and τ_{y_x} < τ_p, since otherwise p ∈ U.
   - By §2, the segment from y_x to p is in U ∩ O.

   So every point of U ∩ O is joined to the connected line segment.
3. **Find q′.** ψ∘(segment) is future causal and lies in sing₀(N) (`isMor_sing`), inside a compact diamond. So it has an endpoint q′ ∈ sing₀(N), which is closed.
4. **Extend near p.** At a segment point y near p, B2 (MapsTo the E₀ component holds, since q′ is BTZ) gives g ∈ Aut(E₀) with ψ = φ₂⁻¹ g φ₁ near y. Set φ := φ₂⁻¹ g φ₁ on O, shrinking a so that gφ₁(O) lies in the chart at q′. Then φ(p) = lim ψ(c(t)) = q′.
5. **Agreement and q′ = q.** ψ and φ agree on all of the connected set U ∩ O by A1. φ is continuous at p and N is T2, so every cluster value of ψ at p along U equals q′. Hence q = q′. ∎

### Past side (`germExt_past`, p ∈ ∂U ∩ J⁻(Σ), p ∈ sing₀)

Here (B) is **not** automatic. Example in M = N = E₀: take Σ = {h = 1}, U = I⁺(0) ∪ {h > 1/2}, p = 0. Then:
- U is open, a future set, and globally hyperbolic, with Σ Cauchy (h is a strict time function, and sublevel sets {h ≥ c, f ≤ f₀} are compact);
- the null line above p, up to h = 1/2, lies outside U.

A3 still holds:
1. **I⁺(p) ∩ J⁻(Σ) ⊂ U.** If z ∈ I⁺(p), then I⁻(z) is a neighbourhood of p, so x_n ≪ z ≤ σ for large n, and U is causally convex.
2. **Choose O.** Take O = {f > τ_p − a, h < τ_p + 2a, r < a/2}, with O ⊂ J⁻(Σ).
3. **U ∩ O is connected.** U ∩ J⁻(Σ) is a future set, and line points ≤ p are not in U. Flowing along ∂_τ at fixed (r, θ) takes each point of U ∩ O into the connected set I⁺(p) ∩ O inside O.
4. **ψ is continuous along I⁺(p).** We have ψ(I⁺(p) ∩ U) = I⁺(q) ∩ ψ(U), by Sbierski's Prop 3.7 argument run with I⁻(z) as the neighbourhood. If z_k ↓ p chronologically, then ψ(z_k) → some q*, and the same identity holds with q*. So I⁺(q) ∩ J⁻(ψΣ) = I⁺(q*) ∩ J⁻(ψΣ). By `cor:K_injectif` (K⁺ = I⁺), q = q*. Shrinking diamonds then give ψ(I⁺(p) ∩ O) ⊂ chart(q).
5. **q is BTZ.** A massive line above q would pull back into the regular set I⁺(p). A regular q has simply connected I⁺ germs, and parabolic holonomy rules that out.
6. **Extend.** Take a line point w above p, with a ball B ∋ w, B ⊂ {f > τ_p} ∩ O. Then reg(B) ⊂ U, and B2 applies on reg(B) even though w ∉ U. Rigidity on U ∩ O and continuity at p finish as on the future side. ∎

## 4. Recommendation

**Drop (B) from consideration for A3 in E₀, and keep A3 as stated, in both directions.**
- (B) is A4's hypothesis, through the equivalence with Lemma 3.9's conclusion, and Sbierski consumes A3 at points without it.
- At BTZ points (B) is a theorem on the future side (`lem:passe_pgcd`), and it is not needed on the past side.

What gx owes in package 11 / item (v) at BTZ points:
- the two connectedness arguments above, which answer CBG-REVIEW C5's "agreement on all of O ⊓ U";
- the past-side B2 application at a point **outside** U;
- `cor:K_injectif` for K⁺.

Record a thesis finding: `prop:Cauchy_non_max`'s hypothesis is labelled "(B)" only in its proof, and l.6658 omits the "∖{p}". The thesis also never treats the past side; it assumes time symmetry, which E₀ lacks (D-12(e)).

The one real risk is in the past-side holonomy step (5). If Level B's B2 cannot see type there, add `sing_mem`-style type preservation to the derivation, not a hypothesis to A3.
