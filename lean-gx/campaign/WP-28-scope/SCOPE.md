# WP-28 scope: the closure of gx Section 4 (uniformization of BTZ-manifolds)

*This is the scoping that DEC-26 calls for: "formalized fully, its cited results included … the
closure of what they need is scoped and put to the author before authoring". It is a read-only
study, done on 2026-10-31 on node1, and no Lean is authored here. Line numbers refer to the files
named. The gx text is `papers/gx/legacy/labeled/RamcovGX.tex`, the accepted 2023 version (DEC-24).
Result numbers for the cited papers follow their arXiv PDFs, checked with `pdftotext`. Nothing
below is a ruling. §5 lists the rulings this scope needs, and every size is an estimate.*

| key | file | role |
|---|---|---|
| **gx** | `papers/gx/legacy/labeled/RamcovGX.tex`, l.1942–1971 (BTZ example), l.1974–2140 (`theo:local_virt_tame`), l.2163–2400 (§4) | the statements |
| **B21** = `brunswic2021cauchy` | `papers/gx/sources/2108.12631/src/BTZ_1.tex` | Thm 3, Lemma 2.4, and what they rest on |
| **B16** | `papers/gx/sources/1605.05530/src/BTZ_HAL_1.tex` | the longer predecessor of B21's preliminaries: the definitions of Cauchy surface and Cauchy-completeness, Geroch, the smoothing theorem `theo:smooth`, and the half-tube `prop:tube` |
| **Bar** = `barbot_globally_2004` | `papers/gx/sources/math_0402257/src/GHFspace.tex` | the classification |
| **ETT** | `lean-causal/Causal/` (strict, 18,439 lines, 0 sorry) and `lean-causal/scaffold/` (4 real sorries) | what already exists in Lean |

`lean-gx` contains no mathematics yet (`GX/Basic.lean` is 8 lines). §4 also rests on the
general gx theory that waves WP-24…27 build: the maximal branched covering, Galois groups,
virtual tameness, `theo:local_virt_tame` and the singular developing map. **Those are
prerequisites and are not counted in this closure.**

---

## 0. Headline

1. **The closure is about 40–60k lines of Lean**, against 18.4k for the entire ETT library to
   date. With every cut in §4 taken it is roughly 35k. If CBG, the smooth splitting and Barbot's
   full classification are built as literally cited, it is 70k or more.
2. **The main theorem `theo:globally_hyperbolic_cauchy_complete_cauchy_maximal` is not supported
   by the cited results as stated.**
   - Barbot gives `D(M̃) = Ω` only for *absolutely* maximal spacetimes (Bar Prop 8.12 gives `⊂`
     only; Rem 8.13 and §11.3).
   - B21 gives absolute maximality of `reg(M)` only when `M` is **Cauchy-compact** (B21 Cor 2.18).
   - Theorem 3, which gx cites, yields Cauchy-maximality only.
   - The finite-type, `χ<0` hypothesis appears in §4.3's prose but not in the statement. Without
     it there is a candidate counterexample, the tube `{r<c} ⊂ E₀` (§3, D-12).
   - **The Cauchy-compact version is fully supported**, by a route through B21 Prop 2.17 and
     Cor 2.18 instead of Thm 3. That choice is ruling R1.
3. **`prop:globally_hyperbolic_cauchy_complete_manifolds` is false as written.** It is missing
   Cauchy-maximality. A counterexample is the past half `{τ<0}` of `E₀`, which B21 itself
   mentions at l.1105.
4. **"Lemma 2.4 of B21" is the wrong citation.** The full future BTZ ray is given by **Lemma 2.3**.
   Lemma 2.4 presupposes a spear neighbourhood.
5. **The four expensive external theorems are all avoidable or reducible**:
   - Choquet-Bruhat–Geroch (Sbierski), XL. It is hidden in B21 Lemma 2.3's "since M is
     Cauchy-maximal, M₂ embeds into M".
   - The Bernard–Surh smooth splitting, XL.
   - Intersection theory for curves and surfaces, L–XL.
   - Fuchsian discreteness, L.

   Each reduction is listed in §4, and three of them need a ruling.

---

## 1. Inventory of gx §4 (l.2163–2400)

| # | label (line) | kind | proof in gx? | external use |
|---|---|---|---|---|
| G-1 | §4.1 `sec:Minkowski` (2172–2189): `E^{1,2}`, `G = SO₀(1,2)⋉ℝ³`, the linear part `L`, `H`, `SO₀(1,2)≅PSL₂ℝ`, the parabolic/elliptic/hyperbolic trichotomy and its "useful characterisation" by stabilised lines | defs + claimed facts | no | classical |
| G-2 | §4.2 `sec:mink_caus` (2193–2213): `<`, `≪`, causal/timelike vectors, `G` acts monotonically | defs + fact | no | classical |
| G-3 | §4.3 `sec:mess` (2215–2246): sheaf of preorders; *causal*, *globally hyperbolic*, *Cauchy-compact*, *Cauchy-complete*; `J^±`, `I^±` | defs | — | `oneil`, `MR2196783` |
| G-4 | 2235: "Geroch: GH ⇔ causal + compact `J⁺(p)∩J⁻(q)`" | cited thm | no | `MR0270697`, `MR2196783` |
| G-5 | 2235: "Choquet-Bruhat–Geroch: maximal Cauchy extension exists" | cited thm | no | `MR0250640`, `sbierski_geroch` (used **only as a hypothesis**, per gx's own words) |
| G-6 | 2239–2245: **Mess–Bonsante–Barbot** — `M ≅ ρ\Ω`, `ρ_L` discrete faithful, `Ω = ⋂ I⁺(Δ_i)` up to time reversal | cited thm | no | `mess`, `MR2499272`, `MR2170277`, Bar |
| G-7 | 2247–2263: the BTZ developing map `D`, `T_BTZ` (sets `U_λ`), `D(BTZ̃) = J⁺(Δ)`, `Γ ≅ ℤ` fixing the singular locus pointwise, `ρ(γ)` parabolic | facts | partly (l.1942–1971) | — |
| G-8 | `prop:BTZ_virt_tame` (2252) | prop | yes (thin) | — |
| G-9 | `prop:BTZ_manifold_virt_tame` (2262) | prop | yes | gx `theo:local_virt_tame` |
| G-10 | 2268–2279: `D̄: BTZ → Γ\J⁺(Δ)` is a continuous bijection, not open; non-Hausdorff example | remark | yes | — |
| G-11 | `defi:BTZtop` (2281) | def | — | — |
| G-12 | `prop:quotient_chart` (2286) | prop | **no proof** | — |
| G-13 | `rem:tamifying_topology_generated_open` (2292) | claim | **no proof** | — |
| G-14 | `prop:manifold_admits_galoisian_maximal` (2307) | prop | yes (2300–2306) | gx general theory |
| G-15 | `def:manifolds_future_distinguishing_map` (2317), duplicated at `…_map_2` (2355) | def | — | — |
| G-16 | `def:singular_manifold_endowed_causal` (2319): causally connected | def | — | — |
| G-17 | `lem:globally_hyperbolic_manifolds_manifolds` (2325): GH ⇒ future distinguishing | lem | **omitted** | (B21 Prop 1.10) |
| G-18 | `lem:manifolds_manifolds_causally_connected` (2329) | lem | **omitted** | — |
| G-19 | `lem:increasing_map` (2334) | lem | yes | — |
| G-20 | `def:manifold_future_complete_all` (2344) | def | — | — |
| G-21 | `prop:globally_hyperbolic_cauchy_complete_manifolds` (2348) | prop | yes (3 lines) | **B21 Thm 3; Bar; B21 "Lemma 2.4"** |
| G-22 | `lem:globally_hyperbolic_manifolds_maximal` (2359): `M̃` future distinguishing | lem | **no proof** ("not different from Lorentzian") | — |
| G-23 | `theo:globally_hyperbolic_cauchy_complete_cauchy_maximal` (2363) | **main thm** | yes (2377–2396) | **B21 Thm 3; Bar** |

**External results actually invoked.**

| use site | as cited | what it is in the source | direction or part used |
|---|---|---|---|
| G-21, G-23 | "Theorem 3 of `brunswic2021cauchy`" | B21 `theo:BTZ_Cauchy-completness` (l.1582; PDF Thm 3): for GH `M`, (i) `reg_{>0}(M)` Cauchy-complete and Cauchy-maximal ⇔ (ii) some BTZ-extension Cauchy-complete and Cauchy-maximal ⇔ (iii) `Ext_BTZ(M)` is. | **only (ii)⇒(i)**, with the trivial extension. That is exactly B21 **Prop 4.9** `prop:reg_complete` (l.1566). (i)⇒(iii) needs the maximal BTZ-extension Theorem 2 (B21 §4, ~350 lines of tex) and **is not needed**. |
| G-21 | "Lemma 2.4 of `brunswic2021cauchy`" | B21 Lemma 2.4 `lem:add_BTZ_param` (l.685) **presupposes** a spear neighbourhood | the claim "the singular locus contains full future BTZ rays" is **Lemma 2.3** `lem:tube` (l.635). A spear neighbourhood of vertex `p` contains `[p,+∞[` by Def 2.1. Same as B16 `prop:tube`. |
| G-21, G-23 | "Barbot uniformization" | Bar has **no single statement** of what is used. It is assembled from **Prop 8.12** (l.2435: `D` injective, `D(M̃) ⊂ Ω(S̃)`), **Lemma 10.2** (l.3130: `Ω(S̃)` a regular domain, up to time reversal), **Cor 10.3** (l.3173: `Γ` acts freely and properly), **§11.3** (l.3520: equality under absolute maximality), and the remark after Def 4.4 (l.905: `Ω⁺(Λ)` future complete) | U1 = injectivity, the holonomy and `Ω = ⋂ I⁺(Π_j)`. U2 = future completeness. |
| G-4, G-5, G-6 | Geroch, CBG, Mess, Bonsante | context only in gx | they enter the closure through B21 and Bar, see §2 |

---

## 2. The dependency closure

Size codes: **S** ≤ 200 Lean lines, **M** ≤ 1,000, **L** ≤ 5,000, **XL** > 5,000. In the
"smooth?" column, **flat** means the work happens in affine charts of `E^{1,2}`/`E₀` with the
constant quadratic form. No Lorentzian manifold theory, connections or curvature is needed there,
because every (G,X)-manifold here is flat and `G` acts affinely. **PL** means piecewise-smooth
surfaces with an induced length metric. **TOP** means topology or order theory only.

### 2a. gx-internal nodes (the §4 statements themselves)

| id | source | statement (one line) | uses | size | smooth? |
|---|---|---|---|---|---|
| G-1 | gx 2172 | `E^{1,2}`, `SO₀(1,2)⋉ℝ³`, classification **by fixed vectors of the linear part** (corrected; see D-1) | Mathlib `Matrix`, `QuadraticForm` | M (~800) | flat |
| G-2 | gx 2193 | `<`, `≪`; `G` monotone | G-1 | S | flat |
| G-7a | gx 1944, 2237 | `E₀` = ℝ³ with `-2dτdr+dr²+r²dθ²`; `BTZ̃` = maximal branched cover of ℝ³ over a line (`C_∞^{(3)}`); `D` (pull-back of `Q` checked: `D*Q = ds₀²`) | G-1; WP-25 branched covers | M–L (~1,500) | flat |
| G-7b | gx 2250 | `D(BTZ̃) = J⁺(Δ)`, `D` injective, `Γ≅ℤ`, `ρ(γ)` parabolic fixing `Δ` pointwise | G-7a | M | flat |
| G-7c | gx 1958 | `T_BTZ` makes `D` continuous, `Aut(BTZ̃)` continuous, `reg` `T`-portly | G-7a; WP-24 portly | M | TOP |
| G-8 | `prop:BTZ_virt_tame` | quotient topology of `T_BTZ` on `BTZ` is the natural one | G-7c | S–M | TOP |
| G-9 | `prop:BTZ_manifold_virt_tame` | all BTZ-manifolds are virtually tame | G-8, gx `theo:local_virt_tame` (WP-27) | S | TOP |
| G-11/12 | `defi:BTZtop`, `prop:quotient_chart` | `D̄: E₀ → Γ\J⁺(Δ)` is an isomorphism for the BTZ topology. **No proof in gx** | G-7 | M (~800) | TOP + flat |
| G-13 | `rem:tamifying…` | `T_BTZ` is generated by `T_BTZ`-open diamonds. **No proof** | G-7c, B-4 | M | flat |
| G-14 | `prop:manifold_admits_galoisian_maximal` | `M̃` Galoisian, exactly branched over `sing(M)`, `T_BTZ`-continuous `D`, `M̃` a `BTZ̃`-manifold | G-9, WP-25/27 | S–M | TOP |
| C-1 | gx 2215 + 2313 | causal structure (sheaf of preorders) on `BTZ`- and `BTZ̃`-manifolds; **bridge to ETT's `Causality`** | B-4, ETT `Causality`, `GXStructure`, `scaffold/GXSingular` | L (~2,500) | TOP |
| G-17 | `lem:…_manifolds_manifolds` | GH ⇒ future distinguishing (proof = B21 Prop 1.10) | ETT `Iplus_injOn_Zplus`, `GloballyHyperbolic.stronglyCausal`, C-1 | S–M | TOP |
| G-18 | `lem:…causally_connected` | `x ≤ y` ⇒ a causal path exists. **Tautological or not, depending on how `≤` is defined (R6)** | C-1 | S (or M) | TOP |
| G-19 | `lem:increasing_map` | `D` increasing on `M̃` | G-18, G-7b | S–M | TOP |
| G-22 | `lem:…_maximal` | `M̃` is GH, hence future distinguishing (a lift of a Cauchy surface through a branched covering is Cauchy) | G-17, WP-25 | M | TOP |
| G-21 | `prop:…future_complete` | **corrected form** (D-11): GH, Cauchy-complete, **Cauchy-maximal**, χ<0 ⇒ future complete | B-17 or B-16, Bar X5, B-8 (=Lemma 2.3) | S | — |
| G-23 | main theorem | **corrected form** (D-12) | everything | M (~1,000) | TOP |

**gx-internal subtotal: about 10k lines.** WP-24…27 are not included.

### 2b. B21 = `brunswic2021cauchy` (arXiv 2108.12631)

Only the part needed for Thm 3 (ii)⇒(i), i.e. **Prop 4.9**, plus Lemma 2.3, is listed. Two items
are gone from the cut: §3 (holonomy and Teichmüller: Goldman, Troyanov–Hulin) and §4 (the
maximal BTZ-extension, Thm 2). **Neither is needed.**

| id | B21 ref (tex line) | statement | uses | size | smooth? |
|---|---|---|---|---|---|
| B-0 | §1.1 (l.260–285) | an `E_{≥0}`-manifold with only type-0 singularities **is** a gx `E₀`-manifold (DEC-25 maximal a.e. atlas) | G-7, WP-27 | S–M | TOP |
| B-1 | Lemma 1.2 `lem:liouville` (360) | a.e. (G,X)-morphisms agreeing on an open set agree | WP-24 rigidity | S | TOP |
| B-2 | **Prop 1.3** `prop:isom` (378) | a local-homeo a.e. morphism near a singular point is a rotation-translation, and the type `α` is preserved (via holonomy type, lift to `E_{0∞}`, uniqueness of developing maps) | G-7, B-1, WP-24 | L (~2,000) | flat |
| B-3 | Cor 1.4–1.7 (l.462–475) | unique type; local homeo ⇒ local diffeo; `M` is a smooth 3-manifold; `sing` is a closed 1-submanifold | B-2; Mathlib `ChartedSpace`/`SmoothManifoldWithCorners` | M–L | smooth structure only |
| — | Prop 1.8 `prop:isom_strong` (468) | injective `reg`-morphisms extend; uses **invariance of domain** (absent from Mathlib) | — | **cut**: not used by the route below | — |
| B-4 | `E₀` causal model (l.520–533; B16 `lem:BTZ_causal_curve` l.515) | along future causal curves `0 ≤ ṙ ≤ 2τ̇`; `J⁻(p)` = the singular half-line and `I⁻(p) = ∅` for singular `p`; `I^±` open; `τ` is a Cauchy time function; diamonds form a basis. **Discharges ETT's `BTZAxioms` / `SingularFlatAxioms` (kb/0012) by construction** | G-7a, ETT `SingularFlat` | L (~1,500) | flat |
| B-5 | Lemma 1.9 `lem:past_BTZ` (535) | a component of `sing` is inextendible causal; BTZ part precedes the rest on a causal curve | B-3, B-4, ETT `Inextensible` | M | TOP |
| B-6 | Prop 1.10 `prop:FZenon_injectif` (576) | strongly causal ⇒ `I⁺` injective | ETT **has it**: `Iplus_injOn_Zplus` | S (bridge) | TOP |
| B-7 | "Geroch / CBG / smooth splitting hold for `E_{≥0}`" (l.556–573) | three cited theorems, proofs deferred to `[thesis]`, B16, Bernard–Surh `MR3783554`, Sbierski | see Geroch, CBG and SPLIT below | — | — |
| Geroch-⇒ | (GH by a Cauchy surface ⇒ causal + compact diamonds) | used by Lemma 2.12's proof (convergence of monotone sequences, `I⁺(q)` as a limit) | ETT **proves** `geroch_i_imp_ii` abstractly; needs C-1 to instantiate | S–M (bridge) | TOP |
| Geroch-⇐ | (causal + compact diamonds ⇒ GH) | used by Rem `rem:reg_GH` and Prop 2.17's GH step | ETT has `geroch_iii_imp_i` as **sorry** (`scaffold/GerochEquiv.lean:75`). **Cut**: the route below exhibits the Cauchy surface directly (B-13), so Geroch-⇐ is not needed | — | — |
| **CBG** | singular Choquet-Bruhat–Geroch (Sbierski, adapted) | **hidden in Lemma 2.3**: "M₂ is a Cauchy-extension of M₀, M is Cauchy-maximal, so M₂ embeds into M". That needs *uniqueness / common extension*, not maximality alone | B-2 (local uniqueness), ETT `SubExtension` (2 sorries, `IsRigid` hypothesis), `CauchyExtension` | **XL** (6–12k) **or ruling R2** | TOP + flat |
| **SPLIT** | Bernard–Surh smooth Cauchy time function | Lemma 2.3 needs a time function with C¹ level sets through `p`; Prop 2.16 needs a smooth spacelike splitting of `N` | — | **XL**; **cut for Lemma 2.3**: use the piecewise-smooth spacelike Cauchy surface that Cauchy-completeness *provides*, and place the spear vertex below it. Not cut for Prop 2.16 (R1) | smooth |
| B-8 | **Lemma 2.3** `lem:tube` (635) | GH and Cauchy-maximal ⇒ every BTZ line has a spear neighbourhood at every vertex, hence **full future BTZ rays** | B-4, B-5, CBG (or R2), a gluing-Hausdorff step (asserted, not proved) | M (+CBG) | PL |
| B-9 | **Lemma 2.4** `lem:add_BTZ_param` (685) | the spear can be chosen so that `Σ∩S` is a graph over `D_R` | B-2 (chart changes are rotation-translations), compactness, B-10 | M | PL |
| B-10 | Lemma 2.7 `lem:surface_causal` (749) | graph `τ_Σ(r,θ)` spacelike ⇔ `1 − 2∂_rτ − (∂_θτ/r)² > 0` | calculus | S–M | PL |
| B-11 | Lemma 2.8 `lem:surface_complete` (781) | (1) `δ ≥ C²/r²` ⇒ complete; (2) complete ⇒ `τ_Σ → +∞` at the line | B-10; a length-space lemma ("finite-length curves extend ⇒ complete", elementary, no Hopf–Rinow) | M | PL |
| B-12 | Lemma 2.6 `lem:curve_extension` (704) | explicit extensions: compact disc (i) / complete cusp (ii) | B-10, B-11 | S–M | PL |
| B-13 | Lemmas 2.9/2.10 + Cor 2.11 (885–912) | a causal arc in a (blunt) spear meets a spacelike graph Σ 0 or 1 times, according to `sup(c)`. Proof by **oriented intersection numbers** (`MR2680546`), sketched | — | **L–XL as written; cut to M**: `f = τ∘c − τ_Σ(r∘c, θ∘c)` is strictly increasing along causal curves (B21's own commented-out proof at l.759–777, made order-theoretic via B-4), then the intermediate value theorem | PL |
| B-14 | Lemma 2.12 `lem:extension_hausdorff` (941) | the push-out of a BTZ-extension and an embedding into a GH manifold is Hausdorff | Geroch-⇒, B-2 (holonomy type), B-5 | M–L | TOP |
| B-15 | Lemma 2.13, Lemma 2.14, Cor 2.15 (999–1040) | causal convexity of BTZ-extensions; BTZ-extension of strongly causal is causal | B-5, B-2 | M | TOP |
| B-16 | **Prop 2.17** `prop:abs_max` + **Cor 2.18** (1078–1120) | `M` GH, **Cauchy-compact**, Cauchy-maximal ⇒ `reg(M)` GH, Cauchy-complete, **absolutely maximal** | B-8, B-9, B-12, B-13, B-14, B-15, **Prop 2.16** | M–L | PL |
| B-16a | **Prop 2.16** `prop:cauchy_abs_max` (1048) | Cauchy-compact: Cauchy-maximal ⇔ `E_A`-maximal | **SPLIT of N**, O'Neill Lemma 45 p.427 (covering ⇒ achronal), **intersection theory** | **XL** as written; L with a topological splitting | smooth |
| B-17 | **Prop 4.9** `prop:reg_complete` (1566) = Thm 3 (ii)⇒(i) | GH, Cauchy-**complete**, Cauchy-maximal ⇒ `reg` GH, Cauchy-complete, **Cauchy-maximal** (not absolutely) | "Prop 2.17's proof applies as is"; B-8, B-12(ii), B-13, B-14 | M–L | PL |

**B21 subtotal: about 14–18k lines without CBG. CBG adds 6–12k, and Prop 2.16 with SPLIT adds
5–10k.**

### 2c. Bar = `barbot_globally_2004`: the minimal 2+1 route to U1/U2

U1 is injectivity of `D`, the holonomy, and `Ω = ⋂ I⁺(Π_j)`. U2 is future completeness. The
nodes and line numbers are from a dedicated read of GHFspace.tex, and Prop 8.12, Rem 8.13 and
Lemma 10.2 were spot-checked.

| id | Bar ref (tex line) | statement | uses | size | smooth? |
|---|---|---|---|---|---|
| A0 | §2.4–2.5 (496–570) | GH, Cauchy-complete, AMGH | — | S–M | — |
| A1 | Prop 8.11 (2426) | `M ≅ S×ℝ`; the lift `S̃` is Cauchy in `M̃` | `[beem]` Geroch splitting | **XL** to prove smoothly; M for "lift of a Cauchy surface is Cauchy" plus `π₁(S) ≅ π₁(M)` (**ruling R5**) | smooth / TOP |
| B1 | §6, Rem 6.1 (1824–1995) | normal forms of affine isometries in dim 3 | G-1 | M | flat |
| B2 | §7.1–7.3 (1995–2140) | achronal domains `Ω_g` per type | B1 | M | flat |
| C1 | **Prop 8.1** (2207) | `S` complete ⇒ `π∘D∘f̃ : S̃ → Q(Δ)` is a homeomorphism (covering of ℝ²) | completeness (metric only), path lifting; Mathlib `IsCoveringMap` | M–L | PL |
| C2–C4 | Cor 8.2, 8.3, Lemma 8.6 (2237–2380) | `D∘f̃` embedding, `S̃` entire achronal graph; no nonspacelike elliptic or transverse parabolic holonomy | C1, B2 | M | flat |
| C5 | Prop 8.10 (2388) | `Ω(S̃)` open convex GH, `Γ` acts freely | C2, Geroch-⇐ **in Minkowski space only** (cheap there) | S–M | flat |
| C6 | **Prop 8.12** (2435) | `D` injective, `D(M̃) ⊂ Ω(S̃)` | A1, C1–C4 | M–L | TOP |
| D1–D3 | Lemmas 4.6–4.9, 10.1, **10.2** (921–990, 3102, 3130) | `Ω(S̃) = Ω⁺(Λ(Γ))`, a regular domain, up to time reversal (one "easy check" left unproved) | C2, B2, **existence of a loxodromic element** | M–L | flat |
| X1 | (not in Bar; replaces §5 Bieberbach/Auslander and §9) | 2+1, `χ(Σ*)<0`: `ker L` trivial; `L(Γ)` non-elementary with no elliptics ⇒ discrete (Katok ch. 2) ⇒ loxodromics exist | Fuchsian group theory (absent from Mathlib) | L (~3,000) | flat |
| E1/X2 | Prop 4.14, `[bonsante]` (1134) | a regular domain is GH; cosmological time `T` is C¹ with retraction; `Γ` proper on `Ω` via `p ↦ (n(p),T(p)) ∈ H²×ℝ₊` | convex analysis in Minkowski space | L (~3,000) | C¹ convex |
| G1 | §11.3 (3520) | `M` AMGH ⇒ `D(M̃) = Ω(S̃)` | C6, E1, **absolute maximality of `reg(M)`** (from B-16, Cauchy-compact only) | S–M | TOP |
| X5 | (l.905 remark) | U2: `Ω` future complete ⇒ `D(J^±(x)) = J^±(Dx)` | G1 | S–M | flat |
| ρ-cheap | (not in Bar) | `ρ` faithful and discrete from a free, properly discontinuous action on `Ω`; torsion-free since a finite-order affine map preserving a convex set fixes the barycentre of an orbit | G1 | S | flat |

**Not needed:** Bar Thm 1.1 as a whole (translation, Misner and unipotent cases, twisted
products), §5 (Bieberbach, Auslander, Carrière–Dal'bo), §9, and Props 4.10/4.17/4.22/Thm 4.25.

**Bar subtotal for the minimal route: about 15–20k lines.**

### 2d. What ETT already contributes

Already proved in ETT:

- Minkowski as a topological spacetime (`Minkowski.lean`).
- The cone models `E_α` for α > 0 (`Model/Cone.lean`, `Model/Massive.lean`).
- `GloballyHyperbolic := IsCausal ∧ compact diamonds`.
- Geroch (i)⇒(ii)⇒(iii) (`Geroch.lean`).
- Cauchy surfaces and Cauchy time functions (`Cauchy.lean`).
- Inextensible curves, push-up, and `prop:FZenon_injectif` (`Iplus_injOn_Zplus`).
- The (G,X)-groupoid and causality (`GXStructure.lean`).
- Cauchy embeddings (`CauchyExtension.lean`).

**Absent from ETT:**

- `E₀` itself. It is a named hypothesis there: `BTZAxioms`/`SingularFlatAxioms`.
- The Lorentz group and the isometry classification.
- Lightlike planes, developing maps and holonomy.
- Cauchy-maximality and CBG.
- Cauchy-completeness and length metrics.
- Regular domains and Fuchsian groups.

ETT's Minkowski is the static metric-space construction; it has no `QuadraticForm`. G-1 must
connect the two (`minkowski_le_top_iff_sq` is the existing seam). gx does not depend on
`lean-causal` (DEC-23, ported files only), so every ETT reuse above is a **port**. That costs
little per file, but C-1 is a real bridge.

---

## 3. Defects in §4 as written (DEC-27 candidates)

| # | where | defect | strongest true form / fix |
|---|---|---|---|
| D-1 | §4.1, l.2183–2189 | the characterisation by stabilised lines is **false for affine isometries**. A linear parabolic `L` stabilises a one-parameter family of parallel lightlike lines; an affine parabolic whose translation part is not in `u^⊥` stabilises none; a hyperbolic one with a translation component along its spacelike eigenline stabilises no lightlike line | state it for the linear part: parabolic ⇔ `L≠1` fixes a non-zero lightlike vector; elliptic ⇔ fixes a timelike vector; hyperbolic ⇔ two lightlike eigenlines with eigenvalues ≠1. G-7b's "Δ lightlike ⇒ φ parabolic" then holds, using `φ≠1` |
| D-2 | §4.3, l.2224 | GH: "every future causal curve intersects Σ exactly once" has no "inextendible", so no such Σ exists | "every **inextendible** causal curve" (B16 l.360, Bar) |
| D-3 | §4.3, l.2235 | Geroch is cited with "causal" | the causal (not strongly causal) form is Bernal–Sánchez 2007, not `MR0270697`; a citation precision only |
| D-4 | §4.3, l.2239–2245 | MBB as stated: `ρ_L` discrete faithful and `Ω = ⋂ I⁺(Δ_i)` | Bar proves equality only for **absolutely** maximal spacetimes (Rem 8.13: false in general for non-closed `S`); faithfulness and discreteness of `ρ_L` in 2+1 need χ<0 (X1). Barbot's general statement is "up to finite coverings and linear twisted products" (Thm 1.1). Note that `I⁺(lightlike line)` is an open half-space bounded by a lightlike plane, so the two phrasings agree, provided the family is closed (Bar Lemma 4.9) |
| D-5 | l.1947, 2237; l.1944 | `D(τ,r,θ/2π)` while the formula is in `θ`; metric "`r² dθ`" | `D(τ,r,θ)` with `θ∈ℝ` and `r²dθ²`. Checked: `D*(−dt²+dx²+dy²) = −2dτdr+dr²+r²dθ²` |
| D-6 | `prop:BTZ_virt_tame` | "contains `{r<λ/4π²}` and is thus open" is a non sequitur | the image of `U_λ ∩ V` (V standard-open) is `{r·d(θ,0)² < λ} ∩ π(V)`, which is open. Short fix; the statement stands |
| D-7 | G-12, G-13, G-17, G-18, G-22 | no proof given (the ledger marks `prop:quotient_chart` and `…_maximal` `open`) | to be written; all believed true (G-22 via "a lift of a Cauchy surface is Cauchy") |
| D-8 | l.2317 / 2355 | the same definition twice | one definition |
| D-9 | G-18 | "causally connected" is the definition of `≤` if `≤` is "there is a causal curve" | depends on R6 |
| D-10 | `lem:increasing_map` | quantifies `x,y ∈ M` where `D` lives on `M̃`; the proof uses causal connectedness of `M̃` (not "M connected") | `∀x,y∈M̃` |
| **D-11** | `prop:globally_hyperbolic_cauchy_complete_manifolds` | **false as written**: `M = {τ<0} ⊂ E₀` is GH (Cauchy surface `τ=−1`), Cauchy-complete (induced metric `dr²+r²dθ²`, flat and complete), and its BTZ ray stops at `τ=0`, so `D(J⁺(x)) ≠ J⁺(D(x))`. The proof's ingredients also need: (a) **Cauchy-maximality** (B21 Lemma 2.3); (b) the cited "Lemma 2.4" should be **Lemma 2.3**; (c) Barbot gives future completeness only after **absolute** maximality **and** non-elementarity (the unipotent slab is not future complete); (d) "up to time reversal" must be excluded, which holds when `sing ≠ ∅` (if `Ω` were past complete, a ray point `q ∈ ∂Ω` and `y ∈ I⁺(q)∩Ω` give `q ∈ I⁻(y) ⊂ Ω`, a contradiction), but this is unwritten | add Cauchy-maximal; Cauchy-compact (or absolutely maximal `reg`); `χ(Σ*)<0`; `sing(M)≠∅` or "up to time reversal when `sing=∅`" |
| **D-12** | main theorem | (a) **hypothesis missing**: §4.3's "Σ of finite type, 2g−2+s>0" is not in the statement. **Candidate counterexample**: the tube `T = {r<c} ⊂ E₀`. It is GH; it is Cauchy-complete, since the graph `τ = −1/(c−r)` is spacelike (`δ = 1−2∂_rτ > 0`) and complete (`∫√δ dr = ∞`); `D(reg T̃)` is the slab between two parallel lightlike planes, which is neither future nor past complete. Its Cauchy-maximality still has to be checked (Bar §11.3 makes the slab quotient AMGH among regular spacetimes). (b) Under Cauchy-maximality alone, Bar gives `D(reg M̃) ⊂ Ω` only; equality needs absolute maximality of `reg(M)`, which B21 gives **only for Cauchy-compact `M`** (Cor 2.18), not through Thm 3. (c) The display `⋂_i J⁺(Δ_i) ∪ ⋂_{j∈I} I⁺(Π_j)` is wrong; the proof establishes `(⋃_i Δ_i) ∪ ⋂_{j∈J} I⁺(Π_j)`. (d) "rays" can be full lines in elementary cases (`E₀` itself); under χ<0 they are proper rays (B21 footnote, l.1105). (e) "up to time reversal of M" is meaningless for an `E₀`-manifold, whose time reverse is not one, and the future orientation is forced when `sing≠∅` (see D-11). (f) Proof gaps: the fixed-point set of `Γ_x` is a lightlike line *because* it contains `D(S_x)`; `Γ_x≅ℤ` comes from the local model; the "BTZ topology near a family of rays" is defined (`defi:BTZtop`) only for one `Δ` | **Strongest form supported by the cited literature**: `M` GH, **Cauchy-compact**, Cauchy-maximal `E₀`-manifold, Cauchy surface of genus `g` with `s ≥ 1` BTZ lines and `2g−2+s>0` ⇒ all four bullets, with `D(M̃) = (⋃Δ_i) ∪ ⋂ I⁺(Π_j)`. The Cauchy-complete version is **open** pending R1 |

**Defects in B21 that the formalization must route around:**

- Lemma 2.6's proofs of (i) and (ii) are **swapped**: the `M(1/r−1/R)` formula is the complete
  cusp.
- Lemma 2.3 asserts that `M₂` is Hausdorff without proof, and uses CBG uniqueness where it says
  "Cauchy-maximal".
- Prop 4.9 says "Prop 2.17's proof applies as is", but that proof uses **finitely many** BTZ
  lines (Cauchy-compactness). For Cauchy-complete `M` it needs a **locally finite** family of
  disjoint spears plus completeness of the glued surface, which is unproved.
- Lemmas 2.9 and 2.10 are proof sketches via intersection numbers.

**Defects in Bar** (from the dedicated read, checked where cited):

- Prop 4.10's sign.
- Lemma 4.6: `Ω⁺(Λ̄)` should be `Λ̄`.
- The definition of `Ω_g` must exclude `q=0`.
- Lemma 8.6's τ=0 subcase.
- Lemma 10.2's "easy check".
- Cor 4.13 uses geodesics on a C¹ surface.
- Prop 8.12's second half applies results to the non-complete `S̃×{t}`.

All are fixable, none is fatal.

---

## 4. Where the closure can be cut

| cut | replaces | saving | changes a statement? |
|---|---|---|---|
| K-1: Thm 3 used only in direction (ii)⇒(i) = Prop 4.9 | the maximal BTZ-extension (B21 Thm 2, §4) and Thm 3 (i)⇒(iii) | ~8–12k | no |
| K-2: the spear vertex is placed below the *given* complete Cauchy surface | the Bernard–Surh smooth time function in Lemma 2.3 | XL → S | no (the hypothesis supplies the surface) |
| K-3: monotonicity + IVT in spear coordinates | intersection theory in Lemmas 2.9–2.11 | L–XL → M | no |
| K-4: exhibit Cauchy surfaces directly (Σ*, Σ) | Geroch-⇐ (ETT's sorry) in `rem:reg_GH` and Prop 2.17 | avoids the open ETT sorry | no |
| K-5: all geometry in flat affine charts (`G` affine, `Q` constant) | Lorentzian differential geometry (connections, geodesics, Hopf–Rinow) | most of the "smooth" risk | no |
| K-6: Cauchy-completeness = metric completeness of the induced length metric on a piecewise-smooth (or locally Lipschitz, X3) spacelike Cauchy surface | Riemannian completeness of a smooth induced metric | Riemannian-geometry layer | no for piecewise-smooth (B16's own definition, l.379); **yes, weakening the hypothesis**, for Lipschitz (R3) |
| K-7: 2+1 Fuchsian argument X1 + ρ-cheap | Bar §5 (Bieberbach, Auslander, Carrière–Dal'bo) and §9–10.1 | XL → L | no |
| K-8: only U1/U2 from Bar | Bar Thm 1.1 (full classification) | ~30k+ | no, but this is the reading of DEC-26 (R4) |
| K-9: **Cauchy-compact route** — B21 Prop 2.17 + Cor 2.18 (absolute maximality), skipping Thm 3 | Thm 3 / Prop 4.9 **and** the unproved locally finite surgery | moderate; it is also the only route the literature supports | **yes**: the main theorem becomes Cauchy-compact (R1). It costs Prop 2.16 (SPLIT of `N` + covering argument), unless the strong maximality definition of R2 is adopted, in which case it is S |
| K-10: strong Cauchy-maximality as the definition | CBG uniqueness (Sbierski, singular) | XL → S | **yes, definitional** (R2) |

---

## 5. Rulings the author must make

**R1 — Which theorem is formalized (Cauchy-complete or Cauchy-compact)?**

| option | what it means | cost |
|---|---|---|
| (a) Cauchy-compact | closed Σ, s ≥ 1 BTZ lines, `2g−2+s>0` | supported end to end: B21 Prop 2.17/Cor 2.18 + Bar §11.3. About 35–45k. The statement narrows, so under DEC-27 it becomes `partial` with a finding. Thm 3 is then cited only for the remark |
| (b) Cauchy-complete + finite type + `reg(M)` absolutely maximal as a hypothesis | an extra hypothesis | about 40–50k. Uses Thm 3 (Prop 4.9) plus the locally finite surgery (new proof, M–L). An honest hypothesis, but not the author's |
| (c) Cauchy-complete + finite type as written | the theorem as stated | **an open research step**: no cited result gives `D(reg M̃) = Ω` under Cauchy-maximality for non-closed Σ. First the tube `{r<c}` (D-12a) must be settled, and the literature checked (Bonsante, or Barbot's later papers) for "MGH + Cauchy-complete + cusped ⇒ AMGH" |

**R2 — Cauchy-maximality and CBG.**

| option | cost |
|---|---|
| (a) Formalize singular CBG (Sbierski, with B2-type rigidity; ETT `SubExtension` is a start with 2 sorries) | XL, 6–12k |
| (b) Define Cauchy-maximal strongly ("every Cauchy-extension of every Cauchy sub-development embeds over it"), which CBG shows equivalent to the usual definition | S, but definitional, so the paper's hypothesis is read strongly and recorded as such |
| (c) Prove only the local spear-gluing instance Lemma 2.3 needs | L, ~3–4k; it is in effect a local maximal-common-extension argument, so it may grow toward (a) |

For R1(a), the same choice also prices Prop 2.16: (b) gives `E_A`-maximality almost for free,
while (a) still needs a splitting of `N`.

**R3 — What "Cauchy-complete" means in Lean.**

| option | cost |
|---|---|
| (a) piecewise-smooth spacelike Cauchy surface, complete for the induced length metric extended over singular points (B16 l.1169) | M–L; faithful to B16 and B21 |
| (b) locally Lipschitz achronal Cauchy surface, metrically complete (Barbot endorses this, l.2278–2290) | cheaper in Bar C1, but B21's Lemma 2.4 transversality must be redone; it weakens a hypothesis, which strengthens the theorem |
| (c) a smooth surface with a complete Riemannian metric, literally | needs a Mathlib Riemannian layer (Hopf–Rinow absent); L–XL; not recommended |

**R4 — What "Barbot's classification" in DEC-26 covers.**

| option | cost |
|---|---|
| (a) the 2+1 consequences U1/U2 that §4 uses (K-7, K-8) | ~15–20k |
| (b) Bar Thm 1.1 and Thm 1.2 in full, all dimensions or dim 3 | > 40k: Bieberbach/Auslander theory, unipotent spacetimes, Misner, twisted products, none of it used by gx |

**R5 — Splitting and fundamental groups.** Bar (A1) and the finite-type hypothesis use
`M ≅ Σ×ℝ`, i.e. `π₁(Σ*) ≅ π₁(reg M)`.

| option | cost |
|---|---|
| (a) prove a topological Geroch splitting | L–XL; needs a timelike vector field or flow in the flat smooth structure (Mathlib has local integral curves only) |
| (b) state the topology in the hypothesis ("M homeomorphic to Σ×ℝ with Σ×{0} Cauchy", as B21 Thm 1 does) | S |
| (c) prove only what is used: the lift of a Cauchy surface is Cauchy, plus `π₁` surjectivity from Cauchy-ness | M, if it suffices for X1 |

**R6 — The causal preorder on `BTZ`-/`BTZ̃`-manifolds.** Two readings:

- `≤` is generated by future causal curves. Then G-18 is tautological, which is consistent
  with ETT DEC-6/DEC-20.
- `≤` is the "sheaf of preorders" glued from charts. Then G-18 is a lemma (M).

Also: are BTZ points' `I⁻` empty by definition or by computation? (B-4 computes it.) The answer
fixes how C-1 bridges to ETT.

**Also for the author's attention, no ruling needed.** These are recorded under DEC-27 once the
author agrees:

- D-1 (the classification corrected to linear parts).
- D-2 ("inextendible").
- D-5 (θ normalization).
- D-11 (the hypotheses added to `prop:…future_complete`).
- "Lemma 2.4" → "Lemma 2.3".

---

## 6. Size summary

| block | low | high | comment |
|---|---|---|---|
| gx §4 internal (G-*, C-1) | 8k | 12k | excludes WP-24…27 |
| B21 needed part (B-0…B-17, with cuts K-1…K-6) | 12k | 18k | |
| CBG (R2a) or strong definition (R2b) | 0.2k | 12k | |
| Prop 2.16 with splitting (only under R1a with R2a) | 0 | 10k | |
| Bar minimal route (A0…X5, K-7/K-8) | 15k | 20k | X1 (Fuchsian) and E1 (cosmological time) are the two L items |
| splitting (R5a) | 0 | 6k | |
| **total** | **~35k** | **~78k** | **most likely, with R1a R2b R3a R4a R5b/c: ~40–45k** |

For calibration: the ETT library is 18.4k strict lines after three waves (57/136 closed). The
recommended configuration is about 2–2.5 times that. The XL cliffs (CBG, the smooth splitting,
the full Barbot classification, intersection theory) are all avoidable by K-cuts or by the
rulings above. No node requires curvature or Lorentzian connection theory: everything is flat
affine geometry in charts, or topology.
