# 3+1 intuition log — a co-construction

*Started 2026-11-02. The author proposes an intuition; the session answers with what the flat
(G,X) setting forces, what it leaves open, and what would settle it. **[r]** marks the session's own
reasoning, which nobody has proved yet. Entries are append-only: each new entry gets a date, and a
superseded one is marked rather than edited.*

---

## N1 (2026-11-02) — strings interacting along a surface; knotted traces; a minimal surface instead of a cone

### The author's picture

- In string theory, strings interact along a codimension-2 surface (the worldsheet), not at a point.
- Suppose a massive string leaves a **knotted** trace in the future hyperbolic region ℍ³₊ of the link.
  Then near the event, the future is the suspension of a topologically non-trivial hyperbolic
  (cone-)manifold.
- The surface joining the past knot to the future knot could be a **minimal surface**, rather than
  the cone from the centre O.
- **Question:** can such a suspension, which is no longer the pure conical one, still give a
  standard topology?

### Session answer **[r]**

**(a) The manifold M is already standard; the pair (M, S) is what the knot spoils.**
- In the conical picture, M is locally the cone over the link Σ_x. M is a manifold at x iff
  Σ_x ≅ S³ (BBS l.963, one dimension up).
- Knotting the singular set *inside* Σ_x ≅ S³ does not change that, so M ≅ ℝ⁴ near x.
- What the knot changes is the **pair**. The singular sheet near x is the cone over a knot K ⊂ S³,
  which is a disc that is **not locally flat at O** unless K is the unknot. This is the Fox–Milnor
  cone. So the question becomes: can the pair (M, S) be made standard, with S a locally flat
  surface?

**(b) In flat (G,X) geometry, a singular sheet cannot be a curved minimal surface.**
- At a codimension-2 point y, the local model is (the 2+1 BBS line model) × ℝ (REVIEW §D).
- The holonomy around the sheet lies in the **pointwise** stabiliser of its tangent plane P. So the
  sheet develops into the fixed set of a non-trivial isometry, which is an affine 2-plane.
- Consequently every sheet is **totally geodesic**: minimal, but planar. All the curvature of S sits
  on the lower strata: junction lines (codim 3) and vertices (codim 4).
- **A lone string cannot even bend.** Take a timelike junction line where only two sheet-pieces
  meet. Its link is a spherical cone S² with exactly two cone points. Those points are antipodal,
  with equal angles: the "football", by Troyanov's classification of spherical metrics with two
  cone points, which has to be checked against `references/` before it is cited. So the two pieces
  are one plane. Bending needs a third sheet: **strings bend only by interacting.**
- For spacelike junction lines, the analogue is BBS's own commented-out
  `le:interaction` (TeX l.1128–1129): *"a singularity is an interaction iff the HS-surface has at
  least 3 singularities"*. It is announced and never proved in the paper.

**(c) The minimal-surface picture belongs to Ricci-flat geometry, not to flat geometry.**
- In 2+1, vacuum Einstein means locally constant curvature. That is why BBS's (G,X) approach
  captures *all* of 2+1 gravity with particles.
- In 3+1, vacuum means Ricci-flat, which is not flat: there are gravitational waves.
- A curved, Nambu–Goto-like worldsheet would need a non-flat vacuum outside the string, which is
  beyond any (G,X)-structure.
- So the flat cone-manifolds of this campaign are the **wave-free sector** of 3+1. The author's
  minimal surface is either outside that sector, or it survives in *discrete* form:
  - a **polyhedral** worldsheet with a balance condition at each junction line;
  - at a timelike junction, that balance is exactly the existence condition for the spherical cone
    sphere (Troyanov's angle condition, already `TroyanovAngleCondition` in gx);
  - physically, this reads as tension balance at a string Y-junction.

  The analogy "balance at junctions ≈ discrete stationarity, hence discrete minimality" is a
  heuristic. It is not a theorem.

**(d) Inside flat geometry, a "smeared" interaction is a polyhedral worldsheet, and its topology is
a question of 4-ball genus.**
- Replace the single vertex O by an *interaction region*: a ball B containing several vertices,
  junction lines and sheet-pieces. Each point of B is still conical, with its own link, so smearing
  does not remove vertices; it distributes them.
- The pair (B, S ∩ B) is standard, i.e. S is a locally flat surface, iff **every vertex link is an
  unknotted circle** (for a vertex of a surface; vertices where three or more sheets meet carry a
  graph instead).
- Globally, let K ⊂ ∂B ≅ S³ be the knot that the singular set traces on the sphere around the region
  (past and future strands together). A smeared interaction with a locally flat worldsheet of
  genus g exists *topologically* iff K bounds a **PL** locally flat genus-g surface in B⁴.
  - A disc exists iff K is **smoothly** slice. In dimension 4 the PL and smooth categories agree.
  - In general the genus must be at least the smooth 4-ball genus g₄(K).
- **Striking consequence.** Flat structures are piecewise linear, so they see *smooth* 4-dimensional
  topology, not topological. Freedman's topologically-slice-but-not-smoothly-slice knots, such as
  the untwisted Whitehead double of the trefoil, could not be smeared to a disc in flat geometry,
  although a topological disc exists.
- The **genus of the interaction worldsheet** is bounded below by g₄ of the knot it resolves, which
  is a 4-ball analogue of a string loop order.

**(e) In 2+1 terms, this is BBS §7.2 surgery.**
- BBS replace a *cylindrical neighbourhood* (Def, TeX l.3019) of a particle point by one containing
  an interaction (Lemma `surgery-key`, l.2950; Cor l.3042).
- The 3+1 version would replace the cone over K by a polyhedral worldsheet inside B, with the
  boundary data on ∂B held fixed.
- So the non-conical "suspension" the author asks about is a **surgery on a cylindrical
  neighbourhood**, not a new local model. Every point stays conical; only the *region* is
  non-conical.

### Open, and what would settle it

| id | question | what would settle it |
|---|---|---|
| N1-Q1 | Does an HS³-sphere exist whose singular set is a **closed knotted cone geodesic** inside the ℍ³₊ region, with the rest (photon sphere, dS³, ℍ³₋) regular? Physically: a knotted closed string born at x. | Hyperbolic cone-manifolds of infinite volume with a cone knot and a standard conformal boundary S². Geometrically finite cone-manifold theory (Hodgson–Kerckhoff for deformations; Bromberg for the geometrically finite case) is the place to look. **Not yet in `references/`**, and the citations must be fetched and checked before use. |
| N1-Q2 | The same, with K passing through every region (a string through x, knotted in Σ_x). | As N1-Q1, plus an HS³ gluing across ∂ℍ³₊, which needs the photon sphere's two Möbius structures to match (REVIEW §D, codim 4). |
| N1-Q3 | Do two singular points on an HS²-sphere force antipodality (BBS's unproved `le:interaction`)? This decides whether spacelike strings can bend without interacting. | A proof by the developing map, or a counterexample. It belongs to W2/W4 of REVIEW §E. |
| N1-Q4 | Can every smoothly slice knot be realised as the boundary of a **flat** polyhedral disc interaction, i.e. with the geometric constraints (causality, positivity, balance) and not only the PL topology? | First test: the unknot with a non-trivial band move (a ribbon disc). Then 6₁, the first non-trivial slice knot. |
| N1-Q5 | Should the campaign admit the Ricci-flat (non-flat) sector, where curved worldsheets live, or stay inside (G,X)? | The author's ruling. Admitting it leaves the gx library's scope. |

---

## N2 (2026-11-02) — two competing theories, a physical selection principle, and the Ricci-flat sector

### The author's direction

- **Build both theories and compare them:**
  - **F**, flat (G,X), polyhedral;
  - **R**, Ricci-flat, with conical sheets.
- There may be many polyhedral, non-minimal interacting sheets. **The right property should come
  from physics.**
- The author's main interest is **R**, because it allows physically realistic interactions: a long-range
  gravitational field coming from the interaction core, Ricci-flat and Schwarzschild-like far away.

### What the literature already says about the competition (checked by web search 2026-11-02; PDFs **not yet archived**)

- **The thin limit of a self-gravitating string (Boisseau, Charmousis and Linet).**
  Sources: gr-qc/9607029 (Phys. Rev. D 55, 616, 1997) and gr-qc/9710071 ("Can a self-gravitating thin
  cosmic string obey the Nambu-Goto dynamics?"). Model the string as a smoothed cone in GR and let its
  radius go to zero:
  - in general, the worldsheet of the central line is **totally geodesic**;
  - it obeys **Nambu–Goto**, i.e. is a minimal surface, only when an extra constraint is imposed on
    the core model.

  So the F-versus-minimal competition already exists *inside* R. Totally geodesic is the generic
  thin limit; minimal needs a core assumption. The "property from physics" is a property of the
  **thick-string model**: which matter fills the core.
  - The global-vortex variant (gr-qc/9708001) also concludes "totally geodesic".
  - The scalar-tensor variant (gr-qc/9706020) gives "generically null extrinsic curvature; with a
    constraint, only the mean curvature vanishes".
- **Thin strings are not distributional sources (Geroch–Traschen, Phys. Rev. D 36, 1017, 1987).**
  For their regular class of metrics, curvature can concentrate only on codimension ≤ 1. Strings
  (codim 2) and point particles (codim 3) are excluded. Consequences for R:
  - "Einstein's equations with a string source" has no meaning in the thin limit.
  - R must be posed either **geometrically**, as a Ricci-flat metric off the sheets with a prescribed
    conical behaviour at them (BBS-style, a local-model definition), or as a **limit of thick
    strings**.
  - Later frameworks, Garfinkle's class and Colombeau nonlinear distributions, are the known ways
    around this. *[to verify on archive]*

### Comparison of the two theories **[r]**, to be grounded entry by entry

| axis | F: flat (G,X) | R: Ricci-flat with conical sheets |
|---|---|---|
| local model at a sheet | (2+1 BBS line) × ℝ; holonomy fixes the plane pointwise | tangent cone = an F model (the bridge conjecture below) |
| shape of a sheet | totally geodesic: locally an affine plane | totally geodesic in the curved metric generically; minimal (Nambu–Goto) under a core constraint (BCL) |
| bending | only at junctions (N1 (b)) | possible through the ambient curvature; gravitational waves can travel along the string *[to ground: Garfinkle–Vachaspati travelling waves]* |
| string **endpoints** | impossible: a round-sphere link with one cone point does not exist, so strings end only at junctions **[r]** | possible **on horizons**: Schwarzschild pierced by a string (Aryal–Ford–Vilenkin 1986), a black hole pulled by a string (the C-metric, Kinnersley–Walker) *[to verify]* |
| **point particles** (codim 3) | none: a timelike line whose link is a regular round S² is regular, so the 3+1 analogue of a 2+1 particle is a *string* | yes: Schwarzschild cores, black holes |
| negative-mass sheets (θ > 2π) | allowed (BBS l.1157) | appear as **struts** holding black holes apart (Bach–Weyl, Israel–Khan) *[to verify]* |
| long-range field | none: locally flat outside the sheets; only global holonomy and deficit | ADM/Bondi mass; Schwarzschild at leading order when asymptotically flat; **conical at infinity** if a string reaches infinity (Schwarzschild × deficit) |
| interactions | junction balance = holonomy product = 1 (non-linear momentum conservation); the continuation is **not unique** (BBS Rem l.2766, already in 2+1) | thin-limit dynamics ill-posed (Geroch–Traschen); determinism must come from the thick-string model |
| formalisability (Lean) | high: gx/ETT, waves W0–W5 | the causal and topological skeleton (ETT is metric-free) and the link/tangent-cone layer; the analysis stays at paper level for now |

### The bridge between the theories **[r]** (conjecture)

**Conjecture.** At a point of an R-spacetime with conical singularities (under a regularity class
still to be fixed, e.g. polyhomogeneous edge expansions in the sense of Mazzeo's edge calculus), the
**tangent cone** is the flat cone over a singular HS³-sphere. So **F classifies the infinitesimal
singularities of R**.

If this holds:
- the whole link layer (REVIEW §B, L0–L2) is shared by both theories;
- the theories differ only in how the cones are assembled:
  - F assembles them rigidly, by flat gluing;
  - R assembles them with curvature in between, which is where the long-range field comes from.

### Candidate selection principles from physics, cheapest to test first

1. **Y-junction kinematics.** Compare F's holonomy balance at a timelike junction (Troyanov's
   condition on the spherical link) with the Nambu–Goto junction constraints of Copeland, Kibble and
   Steer (2006) *[to verify]*. Do they agree to first order in Gμ?
2. **Reconnection (intercommutation).** Abelian-Higgs simulations, starting with Shellard 1987
   *[to verify]*, say crossing strings exchange partners. Does that pick one F continuation among
   the many?
3. **The Regge action.** Is Σ (area × deficit) − Σ (tension × area) stationary among polyhedral
   continuations? (The Schläfli identity kills the variation of the deficit angles.)
4. **The thick-string limit.** Which core matter gives "totally geodesic" and which gives
   "Nambu–Goto" (BCL's extra constraint)? This is the physical input that decides between the two
   sheet laws in R.

### The author's target, stated

**Interaction core → Ricci-flat → Schwarzschild far field.** The exact solutions above (Schwarzschild
with strings, the C-metric, Israel–Khan) are the **static and stationary test cases**: a core with
strings attached and a computable far field. The dynamical version, where a string loop collapses into
a core that then radiates, is where R really departs from F. The relevant literature is the formation
of black holes by collapsing cosmic-string loops (Hawking 1990) *[to verify]*.

### Open (N2)

| id | question |
|---|---|
| N2-Q1 | The regularity class for R: Geroch–Traschen-excluded but geometric (Ricci-flat off S, plus a conical edge expansion)? This is what the bridge conjecture is stated over. |
| N2-Q2 | Do the F junction conditions coincide with the Nambu–Goto ones to leading order in Gμ (selection test 1)? |
| N2-Q3 | Archive the eight R references: BCL ×2, Geroch–Traschen, Aryal–Ford–Vilenkin, Kinnersley–Walker, Israel–Khan, Garfinkle–Vachaspati, Hawking 1990. Plus N1's Hodgson–Kerckhoff and Bromberg. Each gets a note with verbatim quotes before any of it is cited as established. |

---

## N3 (2026-11-02) — interactions are not deterministic: an outcome law on moduli space, and a dictionary from geometry to physics

### The author's idea (held for a long time)

- Interacting particles are **not deterministic**.
- **The moduli space of interaction manifolds should contain the law of in→out probabilities.**
- Geometric invariants should carry physical meaning. The angular defect is the mass. In 2+1, as far
  as the author knows, **the momentum law has never been written out explicitly**.

### (a) The 2+1 momentum law, read off the link **[r]**

Let Σ be the HS-sphere at an interaction point x, with singular points p₁…p_n. Fix a base point and
a standard set of loops γ_i around the p_i on the punctured sphere, so that γ₁⋯γ_n = 1 in π₁. The
holonomy P_i := ρ(γ_i) ∈ SO₀(1,2) lies in the **pointwise** stabiliser Γ_{p_i}, which gives the
following correspondence for a single singular point:

| singularity | P_i | physical reading |
|---|---|---|
| massive particle | rotation about the timelike direction p_i ∈ ℍ²_± by the deficit 2π − θ_i | **group-valued momentum**: the axis is the velocity, the angle is the mass. To first order, P_i ≈ 1 + (2π−θ_i)·u_i·J, i.e. linear momentum m_i u_i |
| tachyon | a boost fixing the spacelike p_i | spacelike momentum; the sign ± (BBS l.906–915) says whether light rays are attracted |
| photon | parabolic | null momentum |
| BTZ-like | hyperbolic, degree 0 | black-hole mass (the trace) |
| spin | a translation along the line | **excluded** by the pointwise stabiliser. gx's `massive_particle_intended` has spin (a screw motion) |

**Theorem M (momentum conservation, to state and prove).** The ordered relation

  ∏ P_i = 1

holds. In the causally regular case (Theorem 5.6, type 1), where the past disc carries the incoming
particles and the future disc the outgoing ones, it splits into three parts:

- **(M1) Incoming total.** hol(C₋) = ordered product of the incoming P_i.
- **(M2) Outgoing total.** hol(C₊) = ordered product of the outgoing P_j.
- **(M3) Conservation across the de Sitter annulus.**
  - With no singularity in the annulus, BBS prove that **C₋ and C₊ are projectively isomorphic**
    (Remark after Lemma `surgery-key`, TeX l.3013). That is **conservation of total momentum**.
  - If C₊ is elliptic of angle Θ, the interaction **embeds in the one-particle model 𝒫_Θ** (Lemma
    `surgery-key`, l.2950). So from outside, the whole interaction looks like **one particle of
    total mass 1 − Θ/2π**.
  - With tachyons or photons in the annulus, the two sides differ by one parabolic or hyperbolic
    factor per such singularity (§5.1, l.1926–1930). That is momentum carried off by tachyons and
    photons.

**Linear limit.** Σ m_i u_i (in) = Σ m_j u_j (out) + tachyon and photon terms.

So the law *is* in BBS, but only implicitly, scattered across §5.1 and §7.2, and only for the
elliptic case. Making it explicit is **Theorem M**.

**The dictionary between geometric invariants and physics:**

| geometry | physics |
|---|---|
| deficit 2π − θ | rest mass (×8πG) |
| p ∈ ℍ² | velocity |
| holonomy P | group-valued momentum (non-commutative) |
| the class of the photon-circle holonomy (angle Θ) | total mass of the in- or out-system |
| BBS Def 4.2: closed spacelike dS geodesics have length < 2π | **positive total energy** |
| causality: no CCC, no Misner | no Gott-type time machine *[to ground: Gott 1991; Deser–Jackiw–'t Hooft 1992]* |

**Non-commutativity is physical.** The product depends on the cyclic order of the p_i on the
sphere. That order is geometric data of the interaction, and it disappears only in the linear limit.

**3+1 version.**
- At a junction line, the product of the sheets' holonomies is 1. This is tension balance.
- At a vertex with singular graph K ⊂ S³, the holonomy is a representation of the **knot or graph
  group** π₁(S³ ∖ K) sending meridians to elliptic, boost or parabolic classes. **The Wirtinger
  relations are the momentum law of a knotted interaction.** This connects to N1-Q1, because
  hyperbolic Dehn filling deforms exactly such representations.

### (b) Where the law of outcomes could live **[r]**

- Fix the singularity classes, i.e. the masses. By the Ehresmann–Thurston principle, the space of
  interaction spheres is locally the **relative character variety**

  𝓜(C₁…C_n) = {(P_i) ∈ ∏ C_i : ∏ P_i = 1} / conjugation.

  For n elliptic classes in PSL(2,ℝ) its dimension is 2n − 6, as for hyperbolic cone spheres.
- **It carries a canonical symplectic form**: Goldman's, relative to the boundary classes. On the
  Teichmüller-type component, this is the **Weil–Petersson** form of the hyperbolic cone metric
  *[to verify: Goldman 1984; Weil–Petersson for cone metrics with angles < π, e.g. Schumacher–Trapani,
  Mondello]*.
- **Candidate law.** The probability of an outcome given the incoming data is proportional to the
  **Liouville / Weil–Petersson volume of the fibre** of 𝓜 over the incoming data.
  - For cone angles ≤ π, these volumes are **computable by recursion**: Mirzakhani's volume
    polynomials, extended to cone points *[to verify: Tan–Wong–Zhang; Do–Norbury]*.
  - In the spherical (Euclidean-signature) analogue, Witten's character formula computes the volume
    of the moduli of flat SU(2)-connections on a punctured sphere *[to verify]*.
- **The physics reading.** 2+1 gravity is a Chern–Simons theory whose phase space is a moduli space of
  flat connections (Witten 1988). The Liouville measure is its canonical classical measure, and in
  "effective 3d quantum gravity" the Feynman rules carry group-valued momenta and Haar-measure delta
  functions δ(∏P) *[to verify: Freidel–Livine 2006; Ponzano–Regge with particles, Freidel–Louapre]*.
  The author's "law in the moduli space" would be the semiclassical shadow of that.
- **The key difficulty, where a coupling constant must enter.** Outcomes with different particle
  numbers live on strata of **different dimensions** (2n − 6). Comparing their volumes needs a
  weight per particle, as a vertex factor does in a Feynman expansion. Geometry alone does not fix
  it. That weight is the dimensionful input, e.g. G or ħ in Planck units.
- **The non-compactness question.** Teichmüller space has infinite volume, while moduli space (after
  the mapping class group, i.e. relabelling and braiding) has finite volume. Which quotient is
  physical depends on whether outgoing particles are **distinguishable** and whether **braiding**
  (the order of (a)) is observable.

### What would settle it, cheapest first

| id | step | kind |
|---|---|---|
| N3-1 | State and prove **Theorem M** (M1–M3) in 2+1 from BBS §5.1 / §7.2 | paper; then Lean in gx: holonomy of a punctured HS-sphere. Needs a presentation of π₁ of a punctured sphere, **not in mathlib** |
| N3-2 | Compute 𝓜 and its Goldman volume for the smallest interactions. **2 → 1** (n = 3): 𝓜 is 0-dimensional, so given the incoming pair, P₃ = (P₁P₂)⁻¹ is forced and the outcome is **deterministic**, as momentum conservation says it should be. **2 → 2** (n = 4): 𝓜 is 2-dimensional; the incoming data (P₁, P₂) up to conjugation is 1-dimensional (the relative rapidity); so the **fibre is 1-dimensional**, the analogue of the CM scattering angle. This is the first non-trivial **outcome distribution**: an explicit density on one angle, with the out-masses fixed. Freeing the out-masses adds 2 dimensions | paper / sympy |
| N3-3 | Compare that density with the 2+1 scattering literature *[to verify: 't Hooft; Deser–Jackiw; Carlip's book]* | literature |
| N3-4 | 3+1: momentum law = representations of the knot or graph group of the vertex link; outcome law = volume on the corresponding relative character variety into SO₀(1,3) (dimensions to compute) | research |
| N3-5 | The author's ruling: distinguishable or indistinguishable outcomes (Teichmüller or moduli quotient), and where the per-particle weight comes from | ruling |

---

## N4 (2026-11-03) — Theorem M on paper, and the first outcome law (2 → 2)

*A paper derivation. The topology here is elementary; the cited external results (Goldman's twist
flows) are **[to verify]** before this leaves the notes.*

### Setting

- Σ is a **causally regular** HS-sphere (Thm `tm:thierry` type 1, TeX l.2175).
- The past hyperbolic region D₋ is a disc carrying the incoming massive particles p₁…p_a.
- The future disc D₊ carries the outgoing ones, q₁…q_b.
- A de Sitter annulus A joins the photon circles C₋ = ∂D₋ and C₊ = ∂D₊.
- In this entry: only elliptic singularities, and A and C_± regular, which is BBS's `surgery-key`
  setting (l.2950).
- Write P(x) ∈ PSL(2,ℝ) ≅ SO₀(1,2) for the holonomy of a small positive loop around x.
- Write P̃(x) for its canonical lift to the universal cover G̃ of PSL(2,ℝ). This is the rotation by
  the **real** cone angle, not taken mod 2π (BBS §3.3.1, l.742–744).

### Theorem M (momentum and energy conservation at a 2+1 interaction)

Choose a base point on C₋, with arcs to the p_i in the cyclic order the orientation induces (BBS
l.621–623). Then:

- **(M1) Incoming total.** hol(C₋) = P(p₁)⋯P(p_a).
  - Proof: π₁(D₋ ∖ {p_i}) is free on loops γ_i around the p_i, and a loop parallel to C₋ inside D₋
    is homotopic to γ₁⋯γ_a.
  - Lifted to G̃, this defines the **total angle** Θ₋ ∈ ℝ of the incoming system. Θ₋ is the angle
    of the elliptic ℝP¹-circle C₋ from the hyperbolic side (BBS §5.1, l.1900–1912).
- **(M2) Outgoing total.** hol(C₊) = P(q₁)⋯P(q_b), with total angle Θ₊. The proof is the same.
- **(M3) Conservation.** Θ₋ = Θ₊, **as real numbers**, and hol(C₋) = hol(C₊).
  - At the level of holonomy, this is topology: a loop parallel to C₋ is homotopic across the
    regular annulus A to a loop parallel to C₊.
  - At the level of the **real** angle, it is BBS's remark after Lemma `surgery-key` (l.3013).
    There, the left isotropic foliation of A induces a projective isomorphism ῑ : C₋ → C₊, so the
    two ℝP¹-circles, degree included, are isomorphic.
  - By Lemma `surgery-key`, the interaction then embeds in the one-particle model 𝒫_Θ.
- **Physical reading.**
  - (M1–M2) say total momentum is the ordered product of the group-valued momenta.
  - (M3) says **total energy is conserved as a real number, not just mod 2π**. That is why the
    universal cover G̃ is needed, and the holonomy representation alone does not see it.
  - From outside, the interaction is one particle of total mass M = 1 − Θ/2π.
  - Positivity of the total mass is Θ < 2π. On the annulus 𝒫_Θ ⊃ A, the closed spacelike geodesic
    has length Θ, so this is **exactly BBS Def 4.2** (positive mass, l.1821) **[r]**.
- **With tachyons or photons in A** (beyond the `surgery-key` setting): hol(C₊) = hol(C₋)·∏(one
  parabolic or hyperbolic factor per singularity of A), as in BBS §5.1 (l.1926–1930). This is
  momentum radiated into tachyons and photons. Writing it with the order and the lifts made precise
  is **(M4)**, still to do.

**Conjecture G (Gott exclusion) [r].** Suppose Σ is causal and causally regular, but with C_±
allowed to be non-elliptic. Then C_± is elliptic or parabolic: **the total momentum of a causal
interaction is never spacelike**.
- Heuristic: a hyperbolic total holonomy makes A a quotient of a dS region by a boost. The causality
  of such a quotient (Misner-like) is what has to be checked.
- Physics context *[to verify]*: Gott's two-particle spacetime (1991) has spacelike total momentum
  and contains CTCs. Carroll, Farhi and Guth (1992) and Deser, Jackiw and 't Hooft (1992) show that
  such a total cannot arise from timelike constituents in an open universe.
- In BBS's language this would be a corollary of causality (Def `def:Hcausal`) together with
  Prop `pro.hyphyp`.

### The 2 → 2 outcome law

**The moduli.** Fix four elliptic classes (the masses m₁…m₄). The relative character variety
𝓜 = {(P₁,…,P₄) ∈ ∏ C_i : P₁P₂P₃P₄ = 1}/conj has dimension 2·4 − 6 = 2.

- **Incoming data:** the conjugacy class of (P₁, P₂), equivalently the total angle Φ of P₁P₂ (the
  relative rapidity of the pair, given m₁ and m₂). This is 1-dimensional.
- **The fibre over the incoming data.** P_tot := P₁P₂ is elliptic with fixed point u_tot ∈ ℍ² (the
  **CM frame**). Write R_s for the rotation by s about u_tot. The pairs (P₃, P₄) with
  P₃P₄ = P_tot⁻¹ and the out-masses fixed form exactly one orbit of conjugation by the R_s. So the
  fibre is that orbit. Physically this is 2-body kinematics: in the CM frame the magnitudes are fixed
  by conservation, and **only the direction s is free**.

**The Liouville law.**
- Goldman's Hamiltonian flow of the angle function Φ = angle(hol γ), where γ separates {1,2} from
  {3,4}, is the **twist along γ at unit speed**: conjugate one side by R_s *[to verify: Goldman 1986,
  "Invariant functions on Lie groups and Hamiltonian flows of surface group representations"]*.
- Hence ω = dΦ ∧ ds, the elliptic analogue of Fenchel–Nielsen length–twist.
- **The conditional law on the fibre is therefore uniform in the twist s.**

**The period of s, which is the subtle point [r].**
- At the level of representations, s is defined mod 2π, because R_{2π} = 1 in PSL(2,ℝ).
- **Geometrically** the gluing of D₊ to A along C₊ is a lift to G̃ acting on C̃₊. It is defined
  modulo the deck generator, which is the rotation by the **real** total angle Θ. So the geometric
  twist lives in ℝ/Θℤ, the circle of length Θ.
- Twists by s and s + 2π have the same holonomy but different HS-spheres unless 2π ∈ Θℤ. Here the
  Ehresmann–Thurston map is a local homeomorphism and **not** injective.
- A full Dehn twist about γ (s ↦ s + Θ) changes only the marking, not the spacetime. It is a pure
  mapping class, so the particles' labels are preserved, and **the physical outcome space is the
  circle ℝ/Θℤ.**

**Prediction (2 → 2, fixed species).** The out-pair direction is **uniformly distributed on the
CM-frame circle of length Θ**, the total cone angle: isotropic scattering in the conical CM frame.
- In the weak-gravity limit (Θ → 2π) this is ordinary isotropic 2-body phase space in two spatial
  dimensions.
- Gravity changes the kinematics (group-valued momenta, non-additive total mass) and the **period**
  of the angle (Θ instead of 2π). It does not change the uniformity.

**What the simplest case does *not* fix.**
- **Masses are Casimirs.** The boundary classes are Casimirs of Goldman's Poisson structure, so the
  Liouville measure lives on leaves of fixed mass. **Branching ratios between species, or between
  out-masses, are not geometric**: they need an external measure on masses, which is the particle
  spectrum.
- **Different particle numbers** (2 → 2 versus 2 → 3) compare leaves of different dimension. This
  needs a per-particle weight (N3 (b)).
- **Radiation into tachyons and photons** changes A: a new stratum, (M4).

So the geometry yields the **angular** law canonically, and the **branching** law needs input. That
is a clean division of labour between geometry and physics.

### Next (N4)

| id | step |
|---|---|
| N4-1 | Prove (M3) at the level of the real angle directly from BBS l.2960–3013 (it is their argument), and write (M4) with tachyon and photon factors |
| N4-2 | Prove or refute Conjecture G (whether a boost quotient of the dS annulus is causal) |
| N4-3 | Check the twist-flow claim against Goldman 1986 (archive the PDF) and confirm ω = dΦ∧ds with the normalisation |
| N4-4 | 2 → 3, with the out-masses fixed: dim 𝓜 = 2·5 − 6 = 4, and the incoming data is 1-dimensional, so the **fibre is 3-dimensional**. Its coordinates are the CM direction plus two internal parameters of the out-triple, e.g. the angle and twist of the sub-pair {4,5}. Compute the Liouville density (angle–twist coordinates of a pants decomposition of the out-side). This is the first case where the law is **not uniform** in the naive kinematic variables |
| N4-5 | Lean (later): (M1–M3) need π₁ of a punctured disc with its free generators. **Not in mathlib**; gx's `Paths`/`Galois` may have pieces (check before building) |

---

## N5 (2026-11-03) — Conjecture G becomes Theorem G (spacelike total momentum forms a black hole), and the 2 → 3 law

### Theorem G: the outcome class is set by the type of the total incoming momentum

**What BBS's proof actually uses.**
- In Prop `pro.hyphyp` (TeX l.2056), the hypothesis "H̄ is not a disc" is used **only once**: through
  Prop `pro.hypdegree0` (l.1938), to get that C is a **hyperbolic ℝP¹-circle of degree 0 from the
  hyperbolic side** (l.2083–2085).
- Everything after that runs on that one fact plus positivity and causality: the regularisation of
  tachyons and photons in T (l.2069–2081), the development of the regularised T′ onto W/⟨γ₀⟩
  (l.2087–2101), and the first-return-map argument (l.2129–2147).
- Regularisation acts on the de Sitter side, so it does not change the structure of C from the
  hyperbolic side.

**Proposition G0 (BBS's proof, re-hypothesised).** Let Σ be a positive, causal singular HS-surface.
Let T be a de Sitter region adjacent to a hyperbolic region H along a photon circle C, and assume C
is hyperbolic of degree 0 from the hyperbolic side. Then **either** T is a disc containing exactly
one BTZ-like singularity, **or** ∂T = C ⊔ {one extreme BTZ-like singularity}. In particular, T does
not connect H to a hyperbolic region of the opposite time orientation.
- *Proof:* that of `pro.hyphyp` from l.2083 on, unchanged.

**Lemma F (the funnel lemma) [r], to be written in full.** Let H be a complete hyperbolic cone disc
(the region D₋) with all cone angles < 2π (positive), and suppose the holonomy of its end loop is
**hyperbolic**. Then the end is a funnel, and C is hyperbolic of degree 0 from the hyperbolic side.
- *Sketch.* Minimise length in the free homotopy class of the end loop in H ∖ {cone points}. Loops
  escaping to the end get longer. A minimiser is either a closed geodesic, or a geodesic polygon whose
  vertices are cone points where the *inner* angle is ≥ π. In both cases the region between it and
  C is a regular hyperbolic annulus with locally convex inner boundary and hyperbolic holonomy. That
  annulus embeds in the funnel ℍ²/⟨γ₀⟩, so C is the quotient of an interval between consecutive fixed
  points, i.e. **degree 0**.
- The cone-point bookkeeping is the induction of `pro.hypdegree0`'s proof (l.1957–2017). Note that
  this proof itself assumes the angle relevant to minimisation is < π (l.1979–1981). That is to be
  checked when it is written out.

**Theorem G (classification by total momentum) [r], from G0 + F + Theorem M.** Let Σ be a positive,
causal HS-sphere, let D₋ be its past hyperbolic region, assume D₋ is a disc, and let P_in = hol(C₋)
be the total incoming momentum.

| P_in | end of D₋ | outcome, absent tachyons and photons in the adjacent T |
|---|---|---|
| **elliptic** (timelike total momentum, angle Θ) | conical at infinity, C₋ elliptic | causally regular scattering into a future disc is possible (type 1, `tm:thierry`). By `surgery-key`, from outside it is one particle of angle Θ |
| **hyperbolic** (spacelike total momentum: **a Gott pair**) | a funnel, C₋ hyperbolic of degree 0 (Lemma F) | **no outgoing hyperbolic region through T.** T is a disc carrying **one future BTZ-like singularity**, whose holonomy is P_in⁻¹ by Theorem M; or T ends at an extreme BTZ-like singularity. **The pair forms a black hole** (Thm 5.6, type 2) |
| **parabolic** | a cusp: no photon circle, and D₋ closes up at a cuspidal singularity | the extreme case |

- If T *does* carry tachyons or photons, the holonomies on the two sides of T differ by their factors
  (Theorem M, part M4), and P_in alone no longer decides the outcome.
- **Physical reading.** A causal, positive interaction whose incoming total momentum is spacelike
  cannot emit massive particles into a future disc: it **collapses to a black hole (BTZ-like)
  singularity**. This is the geometric counterpart, inside BBS's local theory, of two pieces of 2+1
  physics *[to verify, archive]*:
  - 't Hooft's resolution of Gott's time machine: the universe crunches before a CTC forms.
  - Matschull's creation of BTZ black holes from colliding particles in AdS. BBS cite this at
    l.1397–1401, and it fits the table above.
- Conjecture G (N4) is the corollary: **in type 1, C_± are elliptic**, i.e. the total momentum of a
  scattering interaction is timelike.

### The 2 → 3 outcome law **[r]**

**Moduli and coordinates.**
- Five elliptic classes (masses m₁…m₅), so dim 𝓜 = 4.
- Use a pants decomposition of the 5-punctured sphere by γ_tot (separating {1,2} from {3,4,5}) and
  γ₄₅ (around {4,5}).
- Angle–twist coordinates are (Φ_tot, s_tot; Φ₄₅, s₄₅). By the elliptic analogue of Fenchel–Nielsen
  coordinates, ω = dΦ_tot∧ds_tot + dΦ₄₅∧ds₄₅ *[to verify: Goldman 1986]*.

**The fibre over the incoming data** (Φ_tot fixed) has coordinates (s_tot, Φ₄₅, s₄₅):
- **s_tot**, the CM direction: uniform on ℝ/Θ_totℤ (as in N4).
- **Φ₄₅**, the total angle of the sub-pair {4,5}, i.e. its gravitational invariant mass. It ranges
  over the **kinematic interval** where the two pants (3, 45, tot) and (4, 5, 45) exist with the
  prescribed elliptic classes. Three elliptic elements with product 1 exist iff a hyperbolic cone
  sphere with three cone points exists, which is the triangle condition on the angles.
- **s₄₅**: uniform on ℝ/Φ₄₅ℤ. The geometric period is the **real** angle Φ₄₅, by the argument of
  N4.

**Integrating out the twists gives the law of the sub-pair's angle:**

  **dP(Φ₄₅) ∝ Φ₄₅ dΦ₄₅ on the kinematic interval.**

The period of s₄₅ is what produces the factor Φ₄₅. This is the first non-uniform law.

**Check against special relativity (weak gravity).**
- In 2+1 gravity the deficit of a system at rest is 8πG × (its energy) (Deser–Jackiw–'t Hooft
  *[to verify]*). So Φ₄₅ = 2π − 8πG M₄₅, and dP ∝ (1 − 4G M₄₅) dM₄₅.
- Relativistic 3-body phase space in **2 spatial dimensions**, written in the sub-pair mass, is
  **uniform in M₄₅**. The reason: 2-body phase space in 2 spatial dimensions is ∝ dθ/√s, with no
  power of |p|, so dΦ₃ ∝ d(M₄₅²)/M₄₅ ∝ dM₄₅. *[standard, to verify against a reference]*
- **The Liouville law reproduces it as G → 0**, with an explicit **gravitational correction factor
  (1 − 4G M₄₅)** that suppresses heavy sub-pairs.
- This is the first quantitative statement of the program: **geometry gives phase space plus a
  gravitational correction**.
- The kinematic interval's ends should likewise tend to [m₄ + m₅, E_cm − m₃] in the CM frame.

### Next (N5)

| id | step |
|---|---|
| N5-1 | Write Lemma F in full, including whether the angle-< π restriction in `pro.hypdegree0` (l.1979–1981) is a genuine restriction |
| N5-2 | Verify the Goldman normalisation, ω = dΦ∧ds with geometric twist period Φ. **The 2 → 3 law depends on it** |
| N5-3 | Compute the kinematic interval of Φ₄₅ exactly (triangle conditions for elliptic triples in PSL(2,ℝ), with real angles in the universal cover) |
| N5-4 | Archive the physics references: Deser–Jackiw–'t Hooft 1984, Gott 1991, Carroll–Farhi–Guth 1992, 't Hooft 1992, Matschull 1999, and a 2+1 phase-space reference |

---

## N6 (2026-11-03) — what Seppi's work gives the cocycle suspension, and the first 3+1 vertex examples

The reading is `SEPPI-READING.md`, with sources in `sources/seppi/` (seven papers, sha256 recorded).
All 55 table quotes were re-checked against `pdftotext` by the main session; every one is found in
its paper. Below, **[q]** = established by a quoted source, **[r]** = inference.

**Design consequences for L0/L1 (to be adopted after the gx round-2 audit):**

1. **Equivariance on germs, not on a fixed neighbourhood [r].** With boosts present there is no
   bounded H-invariant neighbourhood of the apex. So `ConicStructure`'s equivariance must be required
   on germs at the apex (on U ∩ h⁻¹U, shrinking), not on a fixed U_p.

2. **The radial cocycle takes values in germs at 0 of homeomorphisms of [0,∞) [r], refining the
   author's "cocycle on Susp L".** H acts on germs of Susp L at O by (σ, r) ↦ (h·σ, ρ(h,σ)(r)), and ρ
   satisfies the cocycle identity. There are three instances:

   | instance | ρ(h,σ)(r) | where it is used |
   |---|---|---|
   | trivial | r | Riemannian / Thurston (the current `ConicStructure`) |
   | linear scalar | c(h,σ)·r, with c(h,σ) = ‖hσ‖ for the unit-sphere section | the flat point suspension Sing HS^n → Sing E^{1,n} (L3b) |
   | projective | b·r/(1 + a·r) | the HS-level suspension at a **null** point p (photon, extreme BTZ, cuspidal) |

   In the projective case, the pointwise stabiliser of a null vector (null rotations) has no
   invariant complement to ℝv, so no linear chart exists at p.

   **The class of ρ is canonical** (projective setting [q] FS1–FS6, Fillastre–Seppi §2–3); a choice
   of section changes ρ by a coboundary.

   **The obstruction, sharpened [r].** The class is trivial on a subgroup iff every element has
   eigenvalue 1 on each null ray it fixes. A boost fails this, which is the sharp form of F2. BBS's
   pointwise stabiliser is precisely this condition along the apex ray. On non-null rays, the
   hyperboloid / de Sitter normalisation v/√|Q(v)| is invariant, so ρ ≡ id there.

   **The celestial suspension becomes a twisted cone.** It is homeomorphic to Susp Σ, because the
   structure group (germs of homeomorphisms of [0,∞) fixing 0) is contractible. The homeomorphism
   needs a choice of trivialisation; the geometry does not.

3. **Correction: spin is not an instance of the point suspension [q][r].** The aside under ruling 1
   ("spin later as an instance of H") was the session's, not the author's, and it is wrong. A screw
   holonomy fixes no point: with spin, the singular line "is a circle and not a line"
   (Barbot–Meusburger 1108.1005 [q]). Spin belongs to the **line model**, as a translation cocycle
   z ↦ z + a·r + τ, i.e. the `Affine` bridge to `quotientBase`. Both Bonsante–Seppi (elliptic) and
   Nie–Seppi (parabolic) express "no spin" as the triviality of the translation cocycle around the
   singularity [q]. A null singular line already carries a second cocycle z ↦ z + a·r even without
   spin [r].

4. **The curvature family κ ∈ {−1, 0, 1} (BBS-Q8) [r].**
   - In the Klein chart at p, the curvature-κ model is the H-invariant region
     D_κ = {w : −κQ(w) < 1}, with the same H, link and cocycle for every κ.
   - Fillastre–Seppi's transition by "blowing up a point" sends D_κ to D_{κt²} [q].
   - So there is **one suspension with a family of domains**. This holds for germs only: BBS's AdS
     e(Σ) extends past the chart.

5. **The first 3+1 vertex examples: Riolo–Seppi's foams [q].** The four-dimensional cone-manifolds
   transitioning from hyperbolic to AdS have singular loci made of:
   - **spacelike sheets with boost holonomy** (tachyonic sheets);
   - **triple-junction spacelike edges**, whose link is a theta-graph;
   - **four-valent vertices**, whose link carries the tetrahedron's edge graph, K₄.

   No massive, photon or knotted strata occur, and they say it is unknown whether embedded-surface
   singular loci can even deform. The links do not depend on κ [r], so these give **flat 3+1 vertex
   links** too: singular HS³-spheres whose singular graph is K₄ inside the de Sitter region. Their
   half-pipe meridians are Minkowski translations, i.e. dislocations, so they fall outside the
   spinless setting.

**Still open from the reading:**
- the conformal-factor reading of ρ on the photon sphere ∂ℍ^n (to check against a reference);
- whether BBS's light-like HS singularities act projectively as predicted by row 3 of the table;
- Nie–Seppi 2111.04532 and Danciger's half-pipe papers, not yet fetched.

---

## N7 (2026-11-03) — Benzécri: the suspension systematised

### The author's recollection

Benzécri did a lot of work on **affine suspensions**. The author was inspired by it at the time, and
thought **the general approach should be systematised to the singular case**.

### The classical construction *[to verify, archive]*

- **Source.** J.-P. Benzécri, *Sur les variétés localement affines et localement projectives*,
  Bull. SMF 88 (1960) 229–332.
- **The construction.** Start from a real projective manifold M, developing into the projective
  sphere S^n = (ℝ^{n+1}∖0)/ℝ₊*, with holonomy lifted to GL(n+1). Pulling back the ℝ₊*-bundle
  ℝ^{n+1}∖0 → S^n gives a **radiant affine** (n+1)-manifold: a cone over M, carrying the Euler
  (radial) vector field.
- **Two classical quotients:**
  - the quotient by a homothety, M × S¹, is the **Benzécri suspension**;
  - the quotient by a projective automorphism is the **affine suspension**.

  (Modern literature on radiant affine manifolds and generalised affine suspensions: Choi; Fox,
  arXiv:2106.04270 *[to verify]*.)

### Why this is exactly the framework the campaign needs **[r]**

1. **It is the intrinsic form of the author's "cocycle on Susp L"** (ruling 2026-11-03).
   - HS^n *is* the projective sphere S^n of V = ℝ^{1,n}, and SO₀(1,n) ⊂ SL(n+1) acts **linearly**. So
     the lift from projective to linear holonomy is canonical, and the Benzécri cone over a singular
     HS-manifold is canonical: the ℝ₊*-bundle with its Euler flow.
   - The cocycle c(h,σ) on Susp L is this cone written in the trivialisation given by a radius
     function (the unit sphere: c = ‖hσ‖).
   - The class of c is canonical; c itself is not. This matches N6 (2).
   - The **flat point suspension Sing HS^n → Sing E^{1,n} is Benzécri's radiant cone with the apex
     added.**
2. **Linear versus projective radial action.** These are the two Benzécri-type suspensions, and they
   explain the two cocycle instances of N6 (2).
   - **(B1) The linear (radiant) suspension** at the origin of a vector space: (G ≤ GL(V), S(V)) →
     (G, V). Rays are lines through 0, and the radial action is r ↦ c(h,σ)·r.
     - G = SO(n+1) gives c ≡ 1: Thurston's Euclidean cone.
     - G = SO₀(1,n) gives a non-trivial c: Minkowski.
   - **(B2) The projective suspension** at a point p = [v] of S(V): (Γ_p, S(V/ℝv)) → (G, S(V)). This
     is BBS's 𝔢(L), along projective segments [p, −p] (TeX l.776–781).
     - A direction at p is defined only **modulo v**, so g sends [v + t w] to [v + t(a v + b w′)],
       which is [v + (b t/(1 + a t)) w′]. **The radial action is r ↦ b r/(1 + a r).**
     - When v is timelike or spacelike, v^⊥ is an invariant complement, so a = 0 and the action is
       linear.
     - When v is null, the null rotations admit **no** invariant complement, so a ≠ 0 is
       unavoidable. This is exactly N6's projective instance, now *derived* rather than observed.
3. **The whole BBS / Thurston / thesis scheme becomes one recursion of Benzécri suspensions:**

   E^{1,n} ←(B1)— HS^n ←(B2)— {S^{n−1}, HS^{n−1}, E^{n−1}₊ ⊔ S^{n−2} ⊔ E^{n−1}₋} ←(B2)— …

   - The first step is linear and every later step is projective.
   - At each step, the "link by signature" layer (REVIEW §B, L2) chooses the linear group: the
     pointwise stabiliser of the stratum's tangent subspace.
   - The Riemannian branch is the special case in which every cocycle is trivial (orthogonal
     groups).
4. **What "singular" adds to Benzécri.** Benzécri's suspension takes a *regular* projective manifold
   and produces a cone without its apex. Systematising to the singular case means three things:
   - the input is a singular (a.e.) projective manifold Σ (`SingularGXStructure`);
   - the output is a singular (G, V)-manifold on the twisted cone **with** the apex;
   - the regularity of the apex, and of every ray, is read off Σ. This is the "ray over a regular
     point is regular iff …" result now proved in `Celestial` (`mk_mem_reg_iff`, with compact links),
     in the radius-preserving case.

   So **gx L0 = the singular Benzécri suspension**, in its two forms (B1) and (B2).

### Consequence for the Lean redesign (after gx graduates the current three modules)

| new module | what it defines |
|---|---|
| `RadiantCone` (B1) | for G ≤ GL(V), the cone over a singular (G, S(V))-manifold as the ℝ₊*-bundle with the Euler flow; its identification with `Susp Σ` via a radius function, with the cocycle as the coordinate form; the apex; regularity |
| `ProjectiveCone` (B2) | for p = [v] ∈ S(V) and its pointwise stabiliser, the cone over a singular (Γ_p, S(V/ℝv))-manifold inside S(V), with the projective radial cocycle; the linear specialisation when ℝv has an invariant complement |

The current radius-preserving `ConicStructure` is the trivial-cocycle special case. The counterexamples
in `Affine` (`isEmpty_conicStructure_nullIsom0_stabilizer`) mark exactly where the cocycle becomes
necessary.

**References to archive:** Benzécri 1960 (numdam), the relevant chapter of Goldman's *Geometric
structures on manifolds*, and Choi's work on radiant affine manifolds.
