# T-bz-chapter2: notes on the transcription of Chapter 2 (DEC-137)

File: `benzecri1960_ch2.tex` in this directory. It is a transcription draft made on 2026-11-20
from the page images of the Numdam scan (sha256 `77e0b535…6306`), with the OCR layer used only
as a help. **To be checked by the author.**

## Range covered

- **Journal pp. 246–259 (PDF pp. 19–32).** The file starts at the title « CHAPITRE 2. CONVEXITÉ DE
  CERTAINES VARIÉTÉS BALAYABLES. » on p. 246, which follows the last lines of the proof of Ch. 1,
  § 3, Prop. 4. It ends just before the title « CHAPITRE 3. COMPLÉMENTS SUR LES CONVEXES. » on
  p. 259, which follows the end of the proof of § 3, Prop. 2.
- § 1 « Coques et poches » runs from p. 246 to p. 248, § 2 « La pseudo-longueur » from p. 248 to
  p. 253, and § 3 « Applications » from p. 253 to p. 259. Each journal page is marked
  `% --- p. NNN ---`.
- The running head of p. 258 reads « [CHAPITRE III », but the page is still Chapter 2. This is a
  misprint in the running head. Running heads are not transcribed, so it appears only here.

## Statements and the labels to insert

The scheme is `bz<kind>:c2s<section><initial><number>_<slug>`, as in Chapter 1. Three cases have
no Chapter 1 precedent, so a rule had to be chosen for them:

- **Prime.** A printed prime becomes the suffix `prime`: `d1prime` for « Définition 1′ » and
  `p7prime` for « Proposition 7′ ».
- **Unnumbered statements.**
  - A corollary gets the number of its proposition plus `c`, as `c1s3p1c` does in Chapter 1.
  - § 2's only remark gets `r1`, as Chapter 1's only unnumbered remark got `c1s1r1`.
  - § 1's unnumbered remark gets **`r0`**. `r1` and `r2` are already taken there by the printed
    « REMARQUE 1 » and « REMARQUE 2 ». `r0` is printed before them, and p. 253 cites it as
    « chap. 2, § 1, déf. 1′, remarque ».
  - The two theorems of § 3 are both printed « THÉORÈME. » with no number. The projective one is
    **`t1`**, because the chapter plan (p. 246) calls it « le théorème 1 ». The affine one is
    **`t2`**, which is numbered by order only and has no printed number.
- **The editorial `enonce`.** It gets `bzthm:c2s2_…` with no initial and no number, like Chapter 1's
  enonce labels (`bzthm:c1s1_…`, `bzthm:c1s2_…`).

To match Chapter 1, insert each `\label` right after `\begin{env}[…]`.

| p. | environment (printed heading) | label |
|---|---|---|
| 246 | `defin[1 (dans le cas affin)]` | `bzdef:c2s1d1_poche_affine` |
| 247 | `defin[1$'$ (dans le cas projectif)]` | `bzdef:c2s1d1prime_poche_projective` |
| 247 | `remarque` (REMARQUE, unnumbered) | `bzrem:c2s1r0_poche_affine_vers_projective` |
| 247 | `exemple[Exemple dans le cas affin]` | none (exemple) |
| 248 | `exemple[Exemple dans le cas projectif]` | none (exemple) |
| 248 | `defin[2]` | `bzdef:c2s1d2_coque` |
| 248 | `defin[3]` | `bzdef:c2s1d3_coque_stricte` |
| 248 | `remarque[1]` | `bzrem:c2s1r1_droite_hemisphere` |
| 248 | `remarque[2]` | `bzrem:c2s1r2_coque_stricte_corps_convexe` |
| 249 | `enonce` (properties 1°–7°, editorial) | `bzthm:c2s2_proprietes_pseudo_longueur` |
| 249 | `defin[1]` | `bzdef:c2s2d1_mesure_projective` |
| 249 | `prop[1]` | `bzprop:c2s2p1_mesure_projective_monotone` |
| 250 | `defin[2]` | `bzdef:c2s2d2_segment_majore` |
| 250 | `defin[3]` | `bzdef:c2s2d3_pseudo_longueur` |
| 250 | `prop[2]` | `bzprop:c2s2p2_pseudo_longueur_corps_convexe` |
| 251 | `defin[4]` | `bzdef:c2s2d4_partie_majoree` |
| 251 | `prop[3]` | `bzprop:c2s2p3_voisinage_majore` |
| 251 | `defin[5]` | `bzdef:c2s2d5_nombre_recouvrement` |
| 251 | `prop[4]` | `bzprop:c2s2p4_ligne_brisee` |
| 252 | `defin[6]` | `bzdef:c2s2d6_pseudo_boule` |
| 252 | `prop[5]` | `bzprop:c2s2p5_ouvert_plein` |
| 252 | `prop[6]` | `bzprop:c2s2p6_ligne_brisee_poche` |
| 252 | `prop[7]` | `bzprop:c2s2p7_compact_dans_poche` |
| 253 | `corollaire` | `bzcor:c2s2p7c_deux_points_dans_poche` |
| 253 | `remarque` (REMARQUE, unnumbered) | `bzrem:c2s2r1_cas_affin` |
| 253 | `prop[7$'$]` | `bzprop:c2s2p7prime_compact_dans_poche_affine` |
| 253 | `theoreme` (THÉORÈME, projective) | `bzthm:c2s3t1_poche_balayable` |
| 255 | `theoreme` (THÉORÈME, affine) | `bzthm:c2s3t2_poche_balayable_affine` |
| 256 | `prop[1]` | `bzprop:c2s3p1_projection_non_bornee` |
| 257 | `prop[2]` | `bzprop:c2s3p2_hemisphere_corps_convexe` |

**Counts.** There are 28 ledger statements:

- 10 definitions;
- 10 propositions;
- 3 theorem-kind statements: the 2 `theoreme` and the editorial `enonce`;
- 1 corollary;
- 4 remarks;
- no lemma.

There are also 2 `exemple` environments, which carry no label, and 13 `proof` environments. § 2
Prop. 1 and § 2 Prop. 7′ have no printed proof. The REMARQUE just before Prop. 7′ is its
justification.

**Ledger check.** I inserted the labels above into a copy in `/tmp`. I then parsed it with the
repository's own `tools/texgraph.py` (`scan` + `link`, with benzecri's `env_alias`):

- It finds all 28 statements.
- Each of the 13 proofs attaches to the intended statement.
- Every `\ref` resolves against these labels plus those of `legacy/labeled/benzecri1960_ch1.tex`.

`env_alias` in `papers/benzecri/ledger/ledger.toml` already covers every environment used:
`defin`, `prop`, `theoreme`, `corollaire`, `remarque`, `enonce`. As in Chapter 1, `exemple` is
not aliased.

## Editorial choices the master and the author should see

1. **The `enonce` of the properties 1°–7° (p. 249).** It is editorial, like the DEC-122 enonce of
   Chapter 1. The list is printed without a number, but the chapter cites it about ten times
   (« la septième propriété de la pseudo-longueur », « cf. 3°, 5° », « du 6° »). Five `\bzcf` refs
   point to it.
   - The sentence before it, « La pseudo-longueur … est notée : l_V(M, N). », is notation and
     stays outside.
   - The proof of the properties is printed after Déf. 3 and is cut in two by Prop. 2 and its
     one-line proof. Each of its two `proof` environments carries the editorial optional argument
     `[Proof of \ref{bzthm:c2s2_proprietes_pseudo_longueur}]`, which is not printed. This is the
     only `\ref` outside a `\bzcf`.
   - Without that argument, the ledger's "nearest unproved statement" rule attaches the two parts
     to Déf. 3 and Déf. 2. I checked this with the simulation.
   - If the author rejects the wrap, drop the `enonce`, its five `\bzcf` (keeping their printed
     text) and the two optional arguments.
2. **Preamble.** It is Chapter 1's preamble, with three backward-compatible changes. Chapter 1's
   uses still print identically.
   - `\bznum{…}` was added. It prints « ␣n » for a non-empty argument and nothing for an empty
     one, using `\detokenize`, which needs e-TeX (pdflatex has it).
   - `theoreme` and `remarque` print « Théorème. » and « Remarque. » with no stray space when they
     have no argument, and « Remarque 1. » with one. Chapter 2 needs both the unnumbered and the
     numbered forms.
   - `proof` accepts an optional argument and does not print it.
   - No new environment was needed.
3. **Where an environment ends.** In § 3 the statements are printed in italics (THÉORÈME, Prop. 1,
   Prop. 2), so their end is printed: it is where the roman resumes. In §§ 1–2 everything is
   roman, so each end is editorial. These are the ends I hesitated over:
   - **§ 2, Déf. 1.** I kept inside it the two claims of its own paragraph: « Ce rapport
     anharmonique est une quantité supérieure ou égale à l'unité; la notion de mesure projective
     est invariante par … GS(n, R) ».
   - **§ 2, Déf. 6.** It ends at « majoré par r. ». The next two paragraphs are left outside as
     commentary:
     - « La pseudo-boule … est un ouvert connexe (cf. 3°, 5°). »
     - « Si V est l'intérieur d'un corps convexe, il résulte du 6° que les pseudo-boules … forment
       une base de voisinages de M. »

     Both are unproved claims, and the proof of § 3 Prop. 2, 2° uses the second one. They could
     instead be made a remark.
   - **§ 2, the unnumbered REMARQUE.** It keeps its last words, « on a l'énoncé : », which
     introduce Prop. 7′. This follows the rule that an environment ends with its paragraph.
   - **The two EXEMPLE blocks of § 1.** Each keeps its verification, « Il suffit de vérifier … »,
     like Chapter 1's torus example. The paragraph that follows them, « Nous verrons (§ 3,
     théorème) que … », is commentary and stays outside.
   - **§ 2, Props. 3–6.** Their proofs have no « En effet ». In each case the paragraph after the
     one-paragraph statement starts the proof.
   - **§ 2, Prop. 7.** Its proof is headed « DÉMONSTRATION. — », which is kept as text.
   - **§ 3, Theorem 1.** Its proof runs from « La démonstration du 1° … » to « La démonstration du
     théorème est achevée. ».
   - **« Dans le cas affin, on a le »** is free text before Theorem 2.

## [sic] flagged (10)

| p. | printed | intended reading |
|---|---|---|
| 247 | « (Le système P, H̊, φ, z) doit satisfaire » | « Le système (P, H̊, φ, z) » (misplaced parenthesis) |
| 250 | « (af′ × bf)/(af × ff′) » | denominator « af × bf′ »: the cross-ratio (a, b, f′, f); p. 251 uses the quotients af′/bf′ and bf/af |
| 252 | « puisque O_a est composante connexe » | « O_Q » |
| 252 | « que lcs pseudo-boules » | « les ». The glyph is a clear « c », so I kept it as a misprint. It may be a broken « e »; see « Illegible » below |
| 254 | « L'assertation a » | « assertion » |
| 255 | « Soit M ∈ φ̃⁻¹(D ∩ φ̃(V)) nous : allons montrer » | « nous allons montrer » (misplaced colon) |
| 255 | « de cote constante égale à z(M) » | « z(gM) » (M is the point of L that g sends into P) |
| 258 | « La démonstation » | « démonstration » |
| 258 | « une pseudo-boule (cf. § 2, déf. 5) » | « déf. 6 », the pseudo-boule. Déf. 5 is n(E, k). Following the header's convention, the `\ref` names the **printed** déf. 5 (`bzdef:c2s2d5_nombre_recouvrement`). This is a candidate for the same kind of author ruling that redirected Chapter 1's two misprinted edges (déf. 13, déf. 15) on 2026-11-03 |
| 259 | « (une telle pseudo-boule existe dans V d'après 4°) » | « d'après 3° »: point 3° of the proof gives the pseudo-boules of radius r, and 4° is p(V) = W |

**Kept as printed, with a comment but no [sic].** These are oddities rather than misprints:

- p. 249, 7°, « z φ(N) < K z(φ(M)) », and p. 253, « cote z φ(M⁰) »: parentheses are missing around
  φ(N) and φ(M⁰).
- p. 250: the proof of 7° writes (A, B) for the segment (M, N) of 7°.
- p. 253: « Soit K un domaine générateur compact » and, a few lines later, « k = log K », so K names
  two things.
- « théorème 1 » in the chapter plan (p. 246) names a theorem printed without a number.
- **Not commented in the file.** « borné par k » is used as a synonym of « majoré par k » on
  pp. 250, 251, 252 and 253. Points are called « inclus » in a pseudo-boule (p. 259). « Soit M et
  N deux points » (p. 255) is the period's usage.

## Illegible

Nothing illegible was met. The one doubtful glyph is « lcs » on p. 252, read and flagged above. I
checked a 500-dpi render of it.

## Cross-references marked with `\bzcf`

**To Chapter 1.** There are eight occurrences, pointing to six labels. Each was checked against
`papers/benzecri/legacy/labeled/benzecri1960_ch1.tex`.

| p. | printed text | Ch. 1 label |
|---|---|---|
| 247 | « cf. chap. 1, § 1, déf. 14 » (Déf. 1, b) | `bzdef:c1s1d14_segment_variete` |
| 247 | « cf. chap. 1, § 1, prop. 1, 2° » (Déf. 1, b) | `bzprop:c1s1p1_cartes_compatibles` |
| 247 | « cf. chap. 1, § 1, déf. 6 » (Déf. 1′) | `bzdef:c1s1d6_structure_affine_hemisphere` |
| 247 | « cf. chap. 1, § 1, déf. 12, remarque » (remark r0) | `bzrem:c1s1r1_affine_vers_projective` |
| 248 | « chap. 1, § 1, déf. 12, remarque » (§ 2 introduction) | `bzrem:c1s1r1_affine_vers_projective` |
| 252 | « cf. chap. 1, § 1, déf. 15 » (Prop. 7) | `bzdef:c1s1d15_homogene_balayable_divisible` |
| 253 | « cf. chap. 1, § 1, déf. 12, remarque » (remark of § 2) | `bzrem:c1s1r1_affine_vers_projective` |
| 254 | « cf. chap. 1, § 1, déf. 12 » (proof of Theorem 1, a) | `bzdef:c1s1d12_variete_localement_projective` |

**To the introduction.** Chapter 2 makes none. In the other direction, result B of the
introduction cites Chapter 2 in plain text, without `\bzcf`, in the Chapter 1 file (orig ll.
86–105). Now that these labels exist, a later re-snapshot of that file could mark them; that is
outside this target:

- « chap. 2, § 3, théorème » → `t1`;
- « chap. 2, § 3, théorème et prop. 2 » → `t1`, `c2s3p2`;
- « chap. 2, § 3 : la proposition 1 » → `c2s3p1`;
- « chapitre 2, paragraphe 1, définitions 1, 2, 3 » → `d1` (and `d1prime`), `d2`, `d3`.

**Within Chapter 2.** These references are marked with the labels above:

- p. 246 (plan): « théorème 1 » → `t1`; « prop. 1 » → `c2s3p1`; « 2 » → `c2s3p2`.
- p. 248: « § 3, théorème » → `t1`.
- p. 250: « la proposition 1 » → `c2s2p1`; « cf. déf. 2 » → `c2s2d2`; « la proposition 2 » →
  `c2s2p2`.
- p. 251: « la définition 1′ du paragraphe 1 » → `d1prime`; « la sixième propriété … », « la
  quatrième propriété de la pseudo-longueur » → the enonce.
- p. 252: « cf. 3°, 5° », « du 6° », « la septième propriété de la pseudo-longueur » → the enonce.
- p. 253: « prop. 4 » → `p4`; « la proposition 6 » → `p6`; « cf. chap. 2, § 1, déf. 1′, remarque »
  → `r0`; « La proposition 7 » → `p7`; « son corollaire » → `p7c`.
- p. 254: « la proposition 7 du paragraphe 2 » → `p7`.
- p. 255: « § 1, déf. 1′, b » → `d1prime`.
- p. 258: « cf. § 2, déf. 5 » → `d5` [sic, see above]; « cf. § 2, prop. 5 » → `p5`.

**Marked although they name a statement by description rather than by number.** Chapter 1 has no
such reference. They designate a unique statement, and the master may unmark them, keeping the
printed text:

- « la définition d'une poche » (p. 251) → `d1prime`, in the proof of 7°, which is projective;
- « la définition des poches » (p. 255, twice) → `d1prime`;
- « comme le précédent » (p. 256, proof of Theorem 2) → `t1`;
- « en b dans la démonstration du théorème » (p. 258, proof of § 3 Prop. 2) → `t1`.

**Not marked:**

- A proof's references to its own statement: « la proposition 4 » in the proof of Prop. 4, and
  « les propriétés 1° à 7° », « 4° » inside the proof of the properties.
- An unnumbered « la définition », meaning Déf. 4 in the proof of Prop. 4 and Déf. 3 in the
  proof of the properties.
- The points 1°–5° and a, b, c of a proof referring to one another.

**Implicit uses that may matter for the DAG.** None of these is a printed reference:

- The proof of Theorem 1, 2° uses Prop. 7 (« il existe un automorphisme de V qui envoie le
  compact L dans P »).
- Prop. 5's proof uses Prop. 4.
- § 3 Prop. 2, 2° uses the commentary after Déf. 6.
- § 3 Prop. 2, 3° uses property 6° / Prop. 2 of § 2 (« la continuité de la pseudo-longueur sur
  W »).
- Notions from Chapter 1 are used without citation: segment (déf. 7, 14), demi-droite and
  diamétralement opposés (déf. 4), hémisphère (déf. 5), corps convexe (déf. 11), domaine
  générateur (déf. 15), J(V) (déf. 12), ouvert étalé (prop. 2).

## Build

`pdflatex -interaction=nonstopmode` was run on a copy in `/tmp/bzch2/build`. It produced 14 pages
with no error, no warning, no overfull box and no undefined reference. The `\begin`/`\end` counts
balance (44 each), and no build file was written into the repository.
