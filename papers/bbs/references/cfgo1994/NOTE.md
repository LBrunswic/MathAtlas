# Carroll, Farhi, Guth, Olum 1994: energy-momentum restrictions on Gott time machines

- **Source.** arXiv:gr-qc/9404065 v1 (1 May 1994); Phys. Rev. D 50 (1994) 6190.
- **File.** `pdf/gr-qc-9404065.pdf`, sha256 `64454951…592d` (full hash in `../README.md`).
- **Pages.** References below are to PDF pages. The PDF prints two pages of the preprint side by
  side, so « PDF p.4 » covers printed pp. 6–7.
- **Checking.** Every quote was found with `pdftotext -q -f N -l N`, whitespace normalised.

## Verbatim quotes

1. PDF p.1, abstract: « we find that there is never enough energy for a Gott-like time machine to
   evolve from the specified data; it is impossible to accelerate two particles to sufficiently
   high velocity. »
2. PDF p.1, replacement note: « This version is precise about the meaning of “open universe,” and
   proves that if the total momentum of such a universe is timelike then the total deficit angle
   is no more than 2π. »
3. PDF p.3: « Deser, Jackiw, and ’t Hooft [16] have shown that the group element corresponding to
   the Gott time machine is boostlike, i.e., equivalent under similarity transformation to a pure
   boost. »
4. PDF p.3: « The energy-momentum vector for a single particle is timelike, while that of the Gott
   two-particle system is spacelike (tachyonic), despite the fact that each particle is moving
   slower than c. »
5. PDF p.4: « We show that if S has the topology of IR2 and the total momentum passing through S
   is timelike, then there is insufficient energy for a spacelike subsystem to arise. »
6. PDF p.4: « As the key step in our demonstration, we associate with every collection of
   particles an element of the universal covering group of SO(2,1), and show that an element
   corresponding to an open hypersurface with timelike momentum is never the product of an
   element representing the Gott time machine and any number of elements representing massive
   particles. »
7. PDF p.4. The sentence crosses a printed page break, with footnotes 4–5 between its two parts:
   « However, ’t Hooft [17] has shown that causal disaster is avoided in this » … « case, since the
   universe shrinks to zero volume before any CTC’s can arise. »
8. PDF p.12: « Any particle in its rest frame has a deficit angle α < 2π, so one can uniquely
   define Ti in the universal covering group by using Eq. (2), interpreting R(α) as the element of
   the universal covering group described by (θ = α, ζ ′ = 0), where 0 ≤ α < 2π. »
9. PDF p.12: « it is also necessary to specify, up to continuous deformation, a disk DC of which C
   is the boundary. »
10. PDF p.13: « We then show that this deficit angle must be less than or equal to 2π if S has the
    topology of IR2 , i.e., if the (2+1)-dimensional universe is open. »
11. PDF p.18: « However, as we mentioned in the introduction, ’t Hooft [17] has shown that the size
    of the universe begins to shrink after the decays, leading to a crunch (zero volume) before any
    CTC’s can arise. »
12. PDF pp.20–21, the reference list (reference 8 on p.20, the other four on p.21). Verbatim, these are the citations of the 1991–1992 papers not
    archived here:
    - « 8. J. R. Gott, Phys. Rev. Lett. 66, 1126 (1991). »
    - « 12. S. Deser, R. Jackiw, and G. ’t Hooft, Ann. Phys. 152, 220 (1984). »
    - « 14. S. M. Carroll, E. Farhi, and A. H. Guth, Phys. Rev. Lett. 68, 263 (1992); Erratum: 68,
      3368 (1992). »
    - « 16. S. Deser, R. Jackiw, and G. ’t Hooft, Phys. Rev. Lett. 68, 267 (1992). »
    - « 17. G. ’t Hooft, Class. Quantum Grav. 9, 1335 (1992); Class. Quantum Grav. 10, 1023
      (1993). »

## What it bears on in `../../NOTES-3+1.md` [r]

These are the planner's readings, not the paper's.

- **N4, Conjecture G's « Physics context *[to verify]* ».** Quotes 1, 3–5 and 10 support it:
  - a Gott pair has a spacelike, boostlike total;
  - in an open universe with timelike total momentum, no spacelike subsystem can arise.

  N4 attributes this to « Carroll, Farhi and Guth (1992) and Deser, Jackiw and 't Hooft (1992) ».
  This is the 1994 paper, which replaces the 1992 CFG preprint (quote 2). The 1992 papers
  themselves are not archived.
- **N5, Theorem G's physical reading, « 't Hooft's resolution of Gott's time machine: the universe
  crunches before a CTC forms ».** Quotes 7 and 11 are this paper's report of 't Hooft [17], for
  a closed universe. An HS-sphere is a closed surface (a link), so the closed-universe case is the
  relevant comparison. Theorem G's black hole plays the role of 't Hooft's crunch.
- **N9 §3–§4 (Lemma F).** CFGO also lift to the universal cover of SO(2,1).
  - They lift each particle by its deficit angle in [0, 2π) (quote 8).
  - They note that the lift of a loop depends on a disc it bounds (quote 9).

  The relations to N9 [r]:
  - N9 lifts by the cone angle θ = 2π − α instead, and R̃(θ) = δ·R̃(−α). In those terms (N)
    reads hol̃(C) = δ·∏ R̃(−α_j)′, and for an elliptic total Θ = 2π − (total deficit).
  - Quote 10 (total deficit ≤ 2π for an open universe) is then Θ ≥ 0. N9 gets Θ > 0 from (eq>),
    BBS l.735–737.
  - N9's other bound, Θ < 2π, is total deficit > 0. That is positivity of the masses.

  This is a consistency check, not a proof of (N). CFGO define the lift by deforming loops in the
  disc, which is the framing lift of N9 §3.1 for the disc's framing.
