# Rationale — punctured-torus

## Idea

We have established (in the `cycle-gcd` / `cocycle-combine` line of work) that the
**cycle problem** for the Syracuse map is identical to a **divisibility condition on a
cocycle** defined on the **free group on two generators** $F_2 = \langle a, b\rangle$.
The two generators are the two affine maps that compose to make the Syracuse dynamics:

$$a:\; x \mapsto \tfrac{3x+1}{2}, \qquad b:\; x \mapsto \tfrac{x}{2}.$$

Both are affine. A trajectory word is a sequence in $\{a,b\}$, and the cocycle records
its affine displacement; a cycle is a closed word whose cocycle satisfies the
divisibility condition $D \mid S$.

The free group $F_2$ is the **fundamental group of the once-punctured torus**
$\Sigma_{1,1}$ (equivalently of a thrice-punctured sphere / a wedge of two circles).
This invites a geometric reading: if we can realize the two affine generators as the
**holonomy / side-pairings of an affine structure on a surface homeomorphic to the
punctured torus**, then closed words in $F_2$ become **closed curves** on that surface,
and the cycle problem becomes a question about **closed geodesics** (or closed affine
trajectories) on a natural affine surface.

> **Goal in one line:** build an affine surface $\simeq$ punctured torus whose
> fundamental-group holonomy *is* the pair $\{a,b\}$, so that "Syracuse has no
> nontrivial cycle" reads as a statement that a certain class of closed geodesics does
> not exist (or fails an integrality/divisibility condition).

## Why it might work

- **The free group is already there, naturally.** We did not impose $F_2$ — it arose
  from the two affine maps. The punctured torus is the most standard surface with
  $\pi_1 = F_2$, so the dictionary $\{$closed words$\} \leftrightarrow \{$free homotopy
  classes of loops$\}$ is immediate.
- **Affine + surface = mature theory.** Affine/translation surfaces, $\mathrm{GL}_2(\mathbb{R})$
  action, Veech groups, and the modular-torus picture ($\mathbb{H}/\mathrm{PSL}_2(\mathbb{Z})$,
  whose unit tangent bundle is the punctured-torus / trefoil-complement geodesic flow)
  are heavily developed. If the Syracuse generators land inside one of these structures,
  a large toolbox (closed-geodesic counting, dynamics of the geodesic flow, continued
  fractions) becomes available.
- **Cycles ↔ closed geodesics is a known fertile bridge.** On hyperbolic/affine
  surfaces, conjugacy classes of $\pi_1$ correspond to free homotopy classes of closed
  curves, each with a unique geodesic representative; length and existence questions are
  exactly the regime where rigidity and counting theorems live. Recasting "no nontrivial
  Syracuse cycle" as "no closed geodesic of such-and-such combinatorial type" is the
  kind of translation that can import a non-elementary obstruction.
- **It composes with what we already have.** The cocycle $S/D$ is already understood as
  a transfer-matrix monoid hom; a geometric model would give an independent coordinate
  on the same object and might explain the wedge/Plücker structure
  (`cocycle-combine` structure.md) as intersection/cup-product geometry on the surface.
- **Choice of geometry is a coordinate, and moving between geometries is Teichmüller
  theory (standard).** Once *any* geometric formulation is fixed, passing from affine to
  hyperbolic, to singular-flat, or to Lorentzian structures on the same surface is
  fundamentally deformation theory of $(G,X)$-structures — i.e. Teichmüller theory and
  the character variety $\operatorname{Hom}(F_2,G)/G$ — which is mature and manageable
  from the geometric viewpoint. So the unequal linear parts of $a,b$ are not an
  obstruction: they fix which chart we *start* in (affine), and we are free to deform to
  whichever structure makes the Syracuse integrality/divisibility condition most visible.
  This is the strategic spine of the approach: **establish one geometric model, then use
  standard Teichmüller/character-variety machinery to transport the closed-geodesic
  question between structure types.**

## Known prior art / why it isn't obviously dead

- **Modular torus & geodesic flow.** The once-punctured torus carries the canonical
  complete hyperbolic structure $\mathbb{H}/\Gamma'$ ($\Gamma'$ the commutator subgroup
  of $\mathrm{PSL}_2(\mathbb{Z})$); its geodesic flow, continued-fraction coding, and
  closed-geodesic ↔ conjugacy-class dictionary are classical (Series, McShane, the
  Markoff spectrum). This is the obvious ambient model to test the Syracuse generators
  against.
- **Affine/translation surfaces.** Punctured tori appear as the simplest translation
  surfaces; the $\mathrm{SL}_2(\mathbb{R})$/Veech-group machinery and saddle-connection /
  closed-geodesic counting are well developed (Veech, Eskin–Mirzakhani–Mohammadi).
- **The generators start in the affine chart — and that is fine.** $a,b$ are affine maps
  of $\mathbb{R}$ (or $\mathbb{Z}_2$, or $\mathbb{R}^2$ in homogeneous form) with different
  linear parts ($\times\tfrac32$ vs $\times\tfrac12$), so they are **not** a discrete
  subgroup of isometries of one hyperbolic metric. The natural starting category is
  therefore **affine** (dilation/affine surfaces, or a $(G,X)$-structure with $G$ affine).
  Per the Teichmüller point above, this is a *chart*, not a ceiling: we identify the
  correct affine $(G,X)$ first, then deform.
- **The deformation space of the punctured torus is exceptionally concrete.** The
  ($\mathrm{SL}_2$) relative character variety of $\Sigma_{1,1}$ is the **Markoff cubic**
  $x^2+y^2+z^2 - xyz = \operatorname{tr}[A,B]+2$ in the trace coordinates
  $x=\operatorname{tr}A$, $y=\operatorname{tr}B$, $z=\operatorname{tr}AB$ (Goldman); the
  cusped modular-torus / Markoff-triple locus sits inside it, with the mapping class
  group acting and continued-fraction coding of closed geodesics attached. This gives an
  explicit, elementary deformation space to move the Syracuse holonomy through.
- **The affine → Lorentzian bridge is a studied object, not a leap.** "Affine deformations
  of a Fuchsian (free / punctured-torus) group" is exactly the setting of **Margulis
  spacetimes** and the Drumm–Goldman–Margulis theory of proper affine actions of free
  groups, and AdS Lorentzian structures on surfaces × $\mathbb{R}$ correspond to pairs of
  Teichmüller points (Mess). So the very feature that looked like a defect — affine
  generators over a free group — is the entry point to a developed Lorentzian/Teichmüller
  theory we can cite.
- **Why not obviously dead:** nothing here asks the surface to be a *quotient by a
  Fuchsian group*; we only need an affine structure whose side-pairings realize $a,b$,
  which we can then deform. The punctured torus admits a rich family of affine/dilation
  structures, so there is room to fit two prescribed affine generators — the question is
  whether the fit can be made *natural* enough that the integrality/divisibility
  condition becomes geometric.
