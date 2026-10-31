# Barbot's Theorems A and B — statements, and the rulings OQ-21 … OQ-23

A design note (2026-10-31, read-only design agent of the Barbot campaign; WP-34). Nothing here is
Lean yet. Line numbers are those of `papers/barbot/legacy/labeled/GHFspace.tex` (the labelled
copy; `docs/BARBOT.md` uses the original's, 3–45 lines earlier).

## 1. Definitions (namespace `Causal.Flat`, Barbot's `n = d + 1`)

```lean
structure FlatSpacetime (d : ℕ) where            -- (isom d, Minkowski d)-manifold
  carrier : Type
  [top : TopologicalSpace carrier] [t2 : T2Space carrier]
  [conn : ConnectedSpace carrier]                -- needed: else M ↪ M ⊔ 𝐌ⁿ breaks AM
  [cs : ChartedSpace (Minkowski d) carrier]
  [gx : HasGroupoid carrier (gxGroupoid (isom d) (Minkowski d))]
-- causality: flatCausality (IsomCausal); GH := (flatCausality M).GloballyHyperbolic

def IsLocalIsometry (f : M → N) : Prop := Continuous f ∧ ∀ x, ∃ g : isom d,
  (chartAt _ (f x)) ∘ f ∘ (chartAt _ x).symm =ᶠ[𝓝 (chartAt _ x x)] (g • ·)
def IsIsometricEmbedding f := IsLocalIsometry f ∧ Injective f                       -- OQ-23
def IsTameEmbedding f := ∃ h : IsIsometricEmbedding f,
  ∀ x, Bijective (FundamentalGroup.map ⟨f, h.1.1⟩ x)
def IsFlatCauchyEmbedding f := IsIsometricEmbedding f ∧
  IsCauchyEmbedding (flatCausality M) (flatCausality N) f        -- CauchyExtension.lean:768
def CauchyComplete (M) : Prop   -- DEC-35: ∃ S Cauchy, complete for its induced length
def CauchyCompact M := ∃ S, IsCauchySurface S ∧ IsCompact S ∧ IsSpacelike S
def MGH M := GH M ∧ ∀ (N : FlatSpacetime d) f, IsFlatCauchyEmbedding f → Surjective f
def AbsMax (P : FlatSpacetime d → Prop) M :=
  ∀ N, GH N → P N → ∀ f : M → N, IsIsometricEmbedding f → Surjective f
def AMGH M := GH M ∧ CauchyComplete M ∧ AbsMax CauchyComplete M          -- Rem 2.3, l.572
def IsFiniteCover (p : M' → M) := IsCoveringMap p ∧ IsLocalIsometry p ∧ ∀ y, (p⁻¹'{y}).Finite
structure IsQuotientOf (M) (Γ : Subgroup (isom d)) (Ω : Set (Minkowski d)) : Prop where
  isOpen : IsOpen Ω ;  inv : ∀ γ ∈ Γ, (γ • ·) '' Ω = Ω
  quot : ∃ π : Ω → M, IsCoveringMap π ∧ IsLocalIsometry π ∧ Surjective π ∧
           ∀ p q, π p = π q ↔ ∃ γ ∈ Γ, γ • (p : Minkowski d) = q
```

**GH.** Barbot's (l.497–513: a proper time function with spacelike Cauchy fibres) and ETT's (causal +
compact diamonds) agree in the smooth setting (Geroch + smoothing, external). ETT's is used; Theorem
A's hypotheses still give a Cauchy surface through `CauchyComplete`.

**Linear twisted product** (§5.S, l.1751–1797), quotient form (Lemma 5.5, l.1833):

```lean
def IsLTPOver (B : FlatSpacetime d) (M₁ : FlatSpacetime d₁) := ∃ Γ Ω (ι : Minkowski d₁ →ᵃⁱ Minkowski d),
  TimelikeImage ι ∧ (∀ γ ∈ Γ, γ preserves range ι) ∧ (∀ w ∈ (range ι)ᗮ, Ω + w = Ω) ∧
  IsQuotientOf B Γ Ω ∧ IsQuotientOf M₁ (Γ.restrict ι) (ι ⁻¹' Ω)
```

**The model families** (φ a frame change in `isom d`):
- *Translation*: `IsQuotientOf M Γ univ`, Γ translations whose **span** is spacelike (a rank-2
  lattice in a Lorentzian plane always has timelike vectors), l.587–592.
- *Misner* (l.597–627): Γ discrete in `φG₀φ⁻¹`, `G₀ = {(x,y,z) ↦ (eˢx, e⁻ˢy, z+w)}` (`minkQ =
  2xy + |z|²`), `Ω = φ{xy<0, ±x>0}` (both signs: Isom is SO₀; l.618), **and ∃ γ ∈ Γ, s(γ) ≠ 0 (F1)**.
- *Unipotent* (l.632–753): Γ discrete in `φA_{λ,e}φ⁻¹`, Ω = φ(component of `{∀i, 1+yλᵢ ≠ 0}`).
- *Cauchy-hyperbolic* (Def 4.18, l.1277): `IsQuotientOf M Γ (Ω^±(Λ Γ))`, `L` injective on Γ, `L(Γ)`
  discrete nonelementary, admissible (torsion-freeness from `IsQuotientOf`).
- *CH × torus*: (a) literal twisted product by a flat torus with translation monodromy; (b) the
  central-extension form [10.G] builds (l.3416–3455): spacelike `E`, `ker L ∩ Γ` a lattice of `E`,
  `L(γ)|_E = id`, image in `Isom(𝐌ⁿ/E)` discrete nonelementary, `IsQuotientOf M Γ (p⁻¹ Ω^±(Λ))`.
  (b) = (a) iff `L(Γ)` is torsion-free.

## 2. Theorem A and Theorem B (recommended forms)

```lean
theorem barbot_A (M : FlatSpacetime d) (hd : 1 ≤ d) (hGH : GH M) (hCC : CauchyComplete M) :
  ∃ (M' : FlatSpacetime d) (p : M' → M), IsFiniteCover p ∧
  ∃ (d₁) (_ : d₁ ≤ d) (M₁ : FlatSpacetime d₁) (B : FlatSpacetime d),
    AMGH M₁ ∧ (IsTranslation M₁ ∨ IsMisner M₁ ∨ IsUnipotent M₁ ∨ IsCHTorus M₁) ∧
    IsLTPOver B M₁ ∧ ∃ f : M' → B, IsTameEmbedding f

theorem barbot_B (M) (hGH) (hC : CauchyCompact M) (hM : MGH M) :
  ∃ (M₁ : FlatSpacetime d) (p : M₁ → M), IsFiniteCover p ∧ AMGH M₁ ∧
    (IsTranslation M₁ ∨ IsMisner M₁ ∨ (IsCHTorus M₁ ∧ CauchyCompact M₁))   -- "standard"
```

## 3. OQ-21 — "up to finite coverings and linear twisted products"

- **R1 (recommended)** = `barbot_A`: a finite cover of `M` tamely embeds in an LTP `B` over a model
  `M₁` of dimension `d₁ ≤ d`, `M₁` AMGH in its dimension. It is what §11 proves (conclusions about
  `M(S) = Γ\Ω(S̃)`: l.2616, l.3326–3330, l.3453–3455; the parabolic reduction l.2904–2907 then
  l.3120–3127; absolute maximality for the base by (i), l.3568–3571). The base must drop dimension
  (screw motion with irrational rotation in 𝐌⁴). Cost: finite covers, LTP functoriality, gaps G3/G6.
  Gives up: AMGH is about `M₁`, not `B`.
- **R1′ (equivalent)**: `M` itself tamely embeds into `Γ\Ω_B`, finitely covered by an LTP over an AM
  model (§11.3(ii), l.3573 "embedded in a finite quotient of"); equivalent through `remplacefini`
  (l.2403) and torsion-freeness.
- **R2 (false)**: "a finite cover of M *is* an LTP over a spacetime tamely embedding in an AM model"
  (l.3504–3506 literally). Counterexample: `M = ⟨screw⟩\{t > √(x₂²+x₃²)}` in 𝐌⁴.
- **R3 (stronger)**: R1 + "`B` itself AMGH" (l.340–347 most literally); needs §11.3 redone for LTPs
  (canonical domains split `U^⊥ ⊕ Ω_U`), unwritten.

gx needs none of R1–R3 (its SCOPE §2c): it needs *uniformization* (nonelementary, `ker L` trivial:
D injective, `D(M̃) ⊆ Ω^±(Λ)`, Γ free proper — Prop 8.12, Lemma 10.2, Cor 10.3) and *equality*
(`AbsMax P M → range D = Ω`, §11.3). Ship those as separate lemmas whichever reading.

## 4. OQ-22 — Rem 2.3

- Literal "CGH ⇒ AMGH" is **false**: `Γ = ℤᵈ` spatial translations, `M = Γ\{0<t<1}` is
  Cauchy-compact and sits non-surjectively in `Γ\𝐌ⁿ`. "Any spacelike hypersurface is Cauchy" fails for
  a small spacelike disc.
- **Corrected**: `GH M → CauchyCompact M → MGH M → AbsMax (fun _ => True) M` (hence AMGH). Proof: f(S) is
  a compact spacelike hypersurface of N, hence Cauchy by **lemma K** ("a closed connected spacelike
  hypersurface of a GH spacetime is Cauchy" — asserted, never proved in the paper; proof as B21
  Prop 2.16: covering of the Cauchy surface + O'Neill 14.45 + intersection theory, cost M–L, needed by
  gx too), so f is Cauchy and maximality makes it onto. Also `¬ ∀ M, CauchyCompact M → AMGH M`.

## 5. OQ-23 — isometric embedding, absolute maximality

- Isometric embedding: **(i) recommended** — injective local `(isom d, 𝐌ⁿ)`-morphism (same dimension,
  orientations preserved, l.469–480); prove it is an `IsEMorphism` and an open embedding. (ii)
  rejected — injective causal `IsEMorphism` (`(u,v) ↦ (arctan u, arctan v)` would make 𝐌² non-AM).
  (iii) rejected — smooth metric local isometry (same as (i) by rigidity, costs a metric layer).
- Target class of AM (connected, same `d`): **(α) for Theorem A** — Cauchy-complete targets (Barbot,
  l.202–206, l.574; what §11.3 proves); **(β) for gx** — all flat GH targets (B21's notion), proved
  only for maximal CGH; (γ) (CC′) targets. **Keep `AbsMax P` parametric.**

## 6. Gaps §11 leaves to fill

- **G1** unbounded unipotent case of [11.i] (l.3678–3679), needs one-sided 9.3/9.5; WLOG `y₊ = −y₋`.
- **G2 = F1** Misner AM false for Γ ⊆ ker s; the proof assumes a loxodromic (l.3620).
- **G3** (i)'s proof (l.3586–3592) drops the LTP and finite-cover clauses; redo with
  `B = Γ₁\(Ω₁ ⊕ U^⊥)`, layered A₀ (embedding) → (i) → A against circularity.
- **G4** Theorem B's "standard" (l.358): define standard := Cauchy-compact CH.
- **G5 = F2** torsion of `L(Γ)` in [10.G]. *Candidate counterexample (to check)*: `G ≤ SO₀(1,2)`
  discrete, infinitely generated, elliptic generators `g_m` of every order `m`; Γ ≤ Isom(𝐌⁴) generated
  by `ℤe` and `γ_m = g_m ⊕ (translation by e/m)`: torsion-free, free and proper on `Ω⁺(Λ)×ℝe`,
  Cauchy-complete GH; every finite-index subgroup of `L(Γ)` has torsion; reading (a) excluded by
  tameness. Fix: family (b) in Theorem A; (a) under "π₁ finitely generated" via Selberg's lemma (a
  DEC-36 external); Theorem B has π₁ finitely generated.
- **G6** Lemma 5.5's hypothesis (Ω invariant under `U^⊥`) asserted at l.2904, l.3280, l.3391–3395;
  true for regular domains; to prove for Ω(S̃) in the parabolic case.
- **G7** the Misner "appropriate use of Bieberbach" (l.3327), to write with Bieberbach-light.
- **G8** Theorem B: lemma K suffices (M ↪ M(S) Cauchy ⇒ M = M(S)) in place of Rem `dependance`.
- **G9** "nontrivial LTPs destroy Cauchy-compactness" (l.3542); "unipotent spacetimes never CGH" (l.744).
- **G10** the upstream defects already in `BARBOT.md`.
