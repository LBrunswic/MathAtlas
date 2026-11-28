# T-bz-chapter3: notes on the transcription of Chapter 3 (DEC-195)

File: `benzecri1960_ch3.tex` in this directory. It is a transcription draft made on 2026-11-28
from the page images of the Numdam scan (sha256 `77e0b535…6306`, rendered at 200 dpi, doubtful
glyphs re-checked on zoomed crops), with the OCR layer used only as a help. **To be checked by
the author.** It follows the T-bz-chapter2 precedent (`../T-bz-chapter2/`) in every convention.

## Range covered

- **Chapter 3 complete: journal pp. 259–283 (PDF pp. 32–56), 25 pages.** The file starts at the
  title « CHAPITRE 3. COMPLÉMENTS SUR LES CONVEXES. » on p. 259, which follows the end of the proof
  of Ch. 2, § 3, Prop. 2. It ends at the foot of p. 283, with the proof of § 6, Prop. 4. The
  title « CHAPITRE 4. CORPS ET FORMES CONVEXES AFFINES. » opens p. 284. Nothing was left out.
- Sections, each marked `\subsection*`, and each with its own numbering:
  - § 1 « Facettes et variétés d'appui », pp. 259–262;
  - § 2 « Sommes de convexes », pp. 262–268;
  - § 3 « Dualité des corps convexes », pp. 268–272;
  - § 4 « Contingent des ensembles convexes », pp. 272–276;
  - § 5 « Sur les convexes, réunions de deux convexes disjoints », pp. 276–281;
  - § 6 « Prolongement d'un convexe au-delà d'un hémisphère », pp. 281–283.
- Each journal page is marked `% --- p. NNN ---`. The chapter's own introduction (p. 259) says it
  serves Chapter 5 (« l'étude des convexes balayables »).

## Statements and the labels to insert

The scheme is `bz<kind>:c3s<section><initial><number>_<slug>`, as in Chapters 1–2, with the
Chapter 2 rules (`prime` for a printed prime, `c` for a corollary after the number of its
statement, `r<n>` for unnumbered remarks by order within the section). New cases:

- **Double prime.** « Définition 1″ » (§ 4) becomes `d1primeprime`.
- **Unnumbered DÉFINITION and LEMME.** § 6 has one unnumbered definition: `d1`. § 2 has one
  unnumbered lemma (inside the proof of Theorem 1): `bzlem:c3s2l1_…`. `lemme` is already in
  `env_alias` and `bzlem` in `label_prefixes`.
- **Numbered corollaries.** § 5 prints « COROLLAIRE 1 » and « COROLLAIRE 2 » after Prop. 8:
  `p8c1`, `p8c2`.
- **Corollaries of theorems.** `t1c`, `t2c`, `t3c` (§ 2).
- **The second « THÉORÈME 1. » of § 5** (p. 280, the projective case) is labelled **`t1prime`**:
  the head of § 5 (p. 276) announces « les théorèmes 1 et 1′ », and the proof on p. 281 says « le
  théorème 1′ est un corollaire du théorème 1 ». Its printed heading « 1 » is kept as the
  environment's argument and flagged [sic].
- Remarks: § 1 has 2 (r1, r2), § 2 has 4 (r1–r4), § 3 has 1, § 4 has 1; all are printed
  « REMARQUE. » without number.

As in Chapters 1–2, insert each `\label` right after `\begin{env}[…]`.

| p. | § | environment (printed heading) | label |
|---|---|---|---|
| 259 | 1 | `defin[1]` (DÉFINITION 1) | `bzdef:c3s1d1_preordre_alpha` |
| 260 | 1 | `defin[2]` (DÉFINITION 2) | `bzdef:c3s1d2_facette` |
| 260 | 1 | `remarque` (REMARQUE, unnumbered) | `bzrem:c3s1r1_facette_points_interieurs` |
| 260 | 1 | `prop[1]` (PROPOSITION 1) | `bzprop:c3s1p1_facette_ouverte` |
| 260 | 1 | `prop[2]` (PROPOSITION 2) | `bzprop:c3s1p2_alpha_support` |
| 260 | 1 | `prop[3]` (PROPOSITION 3) | `bzprop:c3s1p3_ordre_supports` |
| 260 | 1 | `prop[4]` (PROPOSITION 4) | `bzprop:c3s1p4_facettes_filtrant` |
| 260 | 1 | `corollaire` (COROLLAIRE, unnumbered) | `bzcor:c3s1p4c_supports_filtrant` |
| 261 | 1 | `defin[3]` (DÉFINITION 3) | `bzdef:c3s1d3_variete_appui` |
| 261 | 1 | `prop[5]` (PROPOSITION 5) | `bzprop:c3s1p5_appui_facette_dim_finie` |
| 261 | 1 | `remarque` (REMARQUE, unnumbered) | `bzrem:c3s1r2_support_interieur_fermeture` |
| 261 | 1 | `prop[6]` (PROPOSITION 6) | `bzprop:c3s1p6_alpha_induit` |
| 262 | 1 | `defin[4]` (DÉFINITION 4) | `bzdef:c3s1d4_facettes_sphere` |
| 262 | 1 | `defin[5]` (DÉFINITION 5) | `bzdef:c3s1d5_noyau` |
| 262 | 1 | `defin[6]` (DÉFINITION 6) | `bzdef:c3s1d6_variete_appui_sphere` |
| 262 | 2 | `defin[1]` (DÉFINITION 1) | `bzdef:c3s2d1_somme_convexes` |
| 263 | 2 | `remarque` (REMARQUE, unnumbered) | `bzrem:c3s2r1_somme_classes` |
| 263 | 2 | `prop[1]` (PROPOSITION 1) | `bzprop:c3s2p1_decomposition_origine` |
| 264 | 2 | `remarque` (REMARQUE, unnumbered) | `bzrem:c3s2r2_somme_infinie` |
| 264 | 2 | `remarque` (REMARQUE, unnumbered) | `bzrem:c3s2r3_somme_directe` |
| 264 | 2 | `prop[2]` (PROPOSITION 2) | `bzprop:c3s2p2_alpha_somme` |
| 264 | 2 | `defin[2]` (DÉFINITION 2) | `bzdef:c3s2d2_fibre` |
| 264 | 2 | `defin[3]` (DÉFINITION 3) | `bzdef:c3s2d3_fibre_cylindriquement` |
| 264 | 2 | `remarque` (REMARQUE, unnumbered) | `bzrem:c3s2r4_fibre_translate` |
| 264 | 2 | `prop[3]` (PROPOSITION 3) | `bzprop:c3s2p3_fibre_cylindriquement` |
| 265 | 2 | `defin[4]` (DÉFINITION 4) | `bzdef:c3s2d4_conjugues` |
| 265 | 2 | `theoreme[1]` (THÉORÈME 1) | `bzthm:c3s2t1_conjugues_intersection` |
| 266 | 2 | `lemme` (LEMME, unnumbered) | `bzlem:c3s2l1_projection_somme` |
| 266 | 2 | `corollaire` (COROLLAIRE, unnumbered) | `bzcor:c3s2t1c_projections_commutent` |
| 267 | 2 | `theoreme[2]` (THÉORÈME 2) | `bzthm:c3s2t2_algebre_boole_affine` |
| 267 | 2 | `corollaire` (COROLLAIRE, unnumbered) | `bzcor:c3s2t2c_algebre_parties_affine` |
| 267 | 2 | `defin[5]` (DÉFINITION 5) | `bzdef:c3s2d5_somme_sphere` |
| 267 | 2 | `defin[6]` (DÉFINITION 6) | `bzdef:c3s2d6_distingue_projectif` |
| 267 | 2 | `theoreme[3]` (THÉORÈME 3) | `bzthm:c3s2t3_algebre_boole_projective` |
| 268 | 2 | `corollaire` (COROLLAIRE, unnumbered) | `bzcor:c3s2t3c_algebre_parties_projective` |
| 268 | 2 | `prop[4]` (PROPOSITION 4) | `bzprop:c3s2p4_automorphisme_compatible` |
| 268 | 2 | `prop[5]` (PROPOSITION 5) | `bzprop:c3s2p5_balayable_somme` |
| 268 | 2 | `corollaire` (COROLLAIRE, unnumbered) | `bzcor:c3s2p5c_balayable_somme_quelconque` |
| 269 | 3 | `prop[1]` (PROPOSITION 1) | `bzprop:c3s3p1_dualite_biunivoque` |
| 269 | 3 | `prop[2]` (PROPOSITION 2) | `bzprop:c3s3p2_dual_fermeture` |
| 270 | 3 | `prop[3]` (PROPOSITION 3) | `bzprop:c3s3p3_hemispheres_points` |
| 270 | 3 | `prop[4]` (PROPOSITION 4) | `bzprop:c3s3p4_dual_geometrique` |
| 270 | 3 | `prop[5]` (PROPOSITION 5) | `bzprop:c3s3p5_dual_variete_lineaire` |
| 270 | 3 | `prop[6]` (PROPOSITION 6) | `bzprop:c3s3p6_dual_sous_variete` |
| 270 | 3 | `prop[7]` (PROPOSITION 7) | `bzprop:c3s3p7_noyau_support` |
| 271 | 3 | `prop[8]` (PROPOSITION 8) | `bzprop:c3s3p8_dual_corps_convexe` |
| 271 | 3 | `prop[9]` (PROPOSITION 9) | `bzprop:c3s3p9_hemisphere_dual` |
| 271 | 3 | `corollaire` (COROLLAIRE, unnumbered) | `bzcor:c3s3p9c_corps_convexe_hemisphere` |
| 271 | 3 | `prop[10]` (PROPOSITION 10) | `bzprop:c3s3p10_interieur_dual` |
| 272 | 3 | `prop[11]` (PROPOSITION 11) | `bzprop:c3s3p11_dualite_automorphisme` |
| 272 | 3 | `remarque` (REMARQUE, unnumbered) | `bzrem:c3s3r1_transposition` |
| 272 | 4 | `defin[1]` (DÉFINITION 1) | `bzdef:c3s4d1_cone_appui` |
| 272 | 4 | `defin[1$'$]` (DÉFINITION 1′) | `bzdef:c3s4d1prime_cone_appui_demi_droites` |
| 272 | 4 | `defin[1$''$]` (DÉFINITION 1″) | `bzdef:c3s4d1primeprime_cone_appui_vecteurs` |
| 272 | 4 | `defin[2]` (DÉFINITION 2) | `bzdef:c3s4d2_contingent` |
| 273 | 4 | `prop[1]` (PROPOSITION 1) | `bzprop:c3s4p1_alpha_cone_appui` |
| 273 | 4 | `prop[2]` (PROPOSITION 2) | `bzprop:c3s4p2_dual_cone_appui_sature` |
| 274 | 4 | `defin[3]` (DÉFINITION 3) | `bzdef:c3s4d3_orthogonalite_points` |
| 274 | 4 | `prop[3]` (PROPOSITION 3) | `bzprop:c3s4p3_dual_cone_appui` |
| 274 | 4 | `prop[4]` (PROPOSITION 4) | `bzprop:c3s4p4_orthogonalite_facettes` |
| 274 | 4 | `defin[4]` (DÉFINITION 4) | `bzdef:c3s4d4_orthogonalite_facettes` |
| 275 | 4 | `prop[5]` (PROPOSITION 5) | `bzprop:c3s4p5_orthogonalite_alpha` |
| 275 | 4 | `prop[6]` (PROPOSITION 6) | `bzprop:c3s4p6_facette_duale` |
| 275 | 4 | `prop[7]` (PROPOSITION 7) | `bzprop:c3s4p7_facette_duale_minimale` |
| 275 | 4 | `prop[8]` (PROPOSITION 8) | `bzprop:c3s4p8_D_cube` |
| 275 | 4 | `prop[9]` (PROPOSITION 9) | `bzprop:c3s4p9_facette_exposee` |
| 276 | 4 | `defin[5]` (DÉFINITION 5) | `bzdef:c3s4d5_facette_conique` |
| 276 | 4 | `prop[10]` (PROPOSITION 10) | `bzprop:c3s4p10_contingent_conique` |
| 276 | 4 | `defin[6]` (DÉFINITION 6) | `bzdef:c3s4d6_base_facette_conique` |
| 276 | 4 | `remarque` (REMARQUE, unnumbered) | `bzrem:c3s4r1_somme_facettes_coniques` |
| 276 | 5 | `defin[1]` (DÉFINITION 1) | `bzdef:c3s5d1_propriete_I` |
| 277 | 5 | `prop[1]` (PROPOSITION 1) | `bzprop:c3s5p1_reunion_convexe_supports` |
| 277 | 5 | `prop[2]` (PROPOSITION 2) | `bzprop:c3s5p2_support_appui` |
| 277 | 5 | `prop[3]` (PROPOSITION 3) | `bzprop:c3s5p3_complementaire_appui` |
| 277 | 5 | `prop[4]` (PROPOSITION 4) | `bzprop:c3s5p4_propriete_I_appui` |
| 277 | 5 | `prop[5]` (PROPOSITION 5) | `bzprop:c3s5p5_support_complementaire` |
| 278 | 5 | `defin[2]` (DÉFINITION 2) | `bzdef:c3s5d2_ensemble_contact` |
| 278 | 5 | `prop[6]` (PROPOSITION 6) | `bzprop:c3s5p6_contact_convexe` |
| 278 | 5 | `prop[7]` (PROPOSITION 7) | `bzprop:c3s5p7_hyperplan_separant` |
| 279 | 5 | `prop[8]` (PROPOSITION 8) | `bzprop:c3s5p8_proprietes_I_II` |
| 280 | 5 | `corollaire[1]` (COROLLAIRE 1) | `bzcor:c3s5p8c1_II_appui` |
| 280 | 5 | `corollaire[2]` (COROLLAIRE 2) | `bzcor:c3s5p8c2_II_section_appui` |
| 280 | 5 | `theoreme[1]` (THÉORÈME 1) | `bzthm:c3s5t1_reunion_convexes_affine` |
| 280 | 5 | `theoreme[1]` (THÉORÈME 1 [sic], announced as 1′) | `bzthm:c3s5t1prime_reunion_convexes_sphere` |
| 281 | 6 | `defin` (DÉFINITION, unnumbered) | `bzdef:c3s6d1_prolonge` |
| 281 | 6 | `prop[1]` (PROPOSITION 1) | `bzprop:c3s6p1_sature` |
| 282 | 6 | `corollaire` (COROLAIRE [sic], unnumbered) | `bzcor:c3s6p1c_sature_corps_convexe` |
| 282 | 6 | `prop[2]` (PROPOSITION 2) | `bzprop:c3s6p2_sature_limite` |
| 282 | 6 | `prop[3]` (PROPOSITION 3) | `bzprop:c3s6p3_raccordement` |
| 283 | 6 | `prop[4]` (PROPOSITION 4) | `bzprop:c3s6p4_deux_points_extremaux` |

**Counts.** There are **90 ledger statements**:

- 23 definitions;
- 44 propositions;
- 5 theorems (§ 2: t1, t2, t3; § 5: t1, t1prime), no editorial `enonce`;
- 1 lemma;
- 9 corollaries;
- 8 remarks.

There are also **48 `proof` environments**. No `exemple` environment: the example of p. 276 is
printed without a heading and is left as free text.

**Statements with no printed proof (42).** All definitions except § 1 Déf. 1 (whose preorder
claim is verified); the 8 remarks except § 3's (which has an « En effet »); § 1 Prop. 3 and its
corollary to Prop. 4; § 2 Theorem 2 and its corollary (« De là on déduit aussitôt le », free
text); § 3 Prop. 4, Prop. 11 and the corollary of Prop. 9; § 4 Prop. 7; § 5 Prop. 4, Corollaries
1 and 2, Theorem 1 (« Des propositions 7, 8 et 4 résulte le », free text); § 6 the corollary of
Prop. 1.

**Ledger check.** I inserted the labels above into a copy in `/tmp` and parsed it with the
repository's own `tools/texgraph.py` (`configure` with benzecri's `env_alias`, `scan` of
`legacy/labeled/benzecri1960_ch1.tex`, `_ch2.tex` and the copy, then `link`):

- it finds all 90 statements, with the kinds counted above;
- each of the 48 proofs attaches to the intended statement (checked one by one), including the
  four tagged ones and the three cases discussed under « Editorial choices » 3;
- every `\ref` resolves (56 reference edges out of Chapter 3); the only dangling edge is the
  header comment's literal `\ref{...}`, which Chapters 1 and 2 also produce;
- `env_alias` needs no change. The ledger's `files` list will need
  `["benzecri1960_ch3.tex", "body", "P"]` when the master snapshots it.

## Editorial choices the master and the author should see

1. **The hypotheses a, b, c, d of § 3 (pp. 268–269) are left as free text.** They carry claims:
   - (a) « Soit W₁ ⊂ W₂ …; on a D(W₂) ⊂ D(W₁) »;
   - (b) « D envoie C(S(E)) dans C(S(E′)) »;
   - (c) « Alors D′∘D induit l'identité sur C(S(E)) », with its own proof « En effet, soit W … Le
     résultat annoncé en résulte. ».

   They are cited later only as hypotheses (« sous les hypothèses de (b) », « (d) », « définie en
   (a) », « cf. § 3, a) »), never as results, and Prop. 2, 2° restates (c) for the closure. So no
   environment was made. The proof of (c) is also left as free text: a `proof` environment there
   would be attached by the ledger to the corollary of § 2 Prop. 5. If the author wants (c) as a
   row, wrap it as an editorial `enonce` (`bzthm:c3s3_dualite_involution`), as was done for the
   properties 1°–7° of Chapter 2, and its proof as `proof[Proof of …]`.
2. **Three printed references name the wrong statement.** Following the header's convention,
   the `\ref` names the **printed** target, and each is flagged [sic]. These are candidates for
   an author ruling of the kind that redirected Chapter 1's two edges on 2026-11-03.
   - p. 273, § 4 Prop. 1 proof: « la définition de α(W) (cf. § 2 déf. 3) ». It points to
     `bzdef:c3s2d3_fibre_cylindriquement`. α(W) is § 1, Déf. 1 (`c3s1d1`), or Déf. 4 (`c3s1d4`)
     on the sphere.
   - p. 281, § 6 Prop. 1: « de noyau vide (cf. § 2, déf. 4) ». It points to
     `bzdef:c3s2d4_conjugues`. The noyau is § 1, Déf. 5 (`c3s1d5_noyau`).
   - p. 264, § 2 Prop. 2: « x α(W) y (cf. déf. 1) ». Inside § 2, « déf. 1 » would be § 2
     Déf. 1, the sum of convexes. I read it as § 1 Déf. 1, the relation α, and the `\ref` names
     `c3s1d1`. **This is a reading, not a misprint, and it is not flagged [sic].**
   - Two more are resolved by reading and not flagged:
     - p. 262, « (cf. § 1, déf. 1) » inside § 1 Déf. 4 is the present § 1 (`c3s1d1`);
     - p. 262, « (cf. § 1, déf. 9) » inside § 1 Déf. 5 cannot be the present § 1, which has no
       Déf. 9. It is Chapter 1, § 1, Déf. 9, the convexe strict (`bzdef:c1s1d9_convexe_strict`).
3. **Proofs printed away from their statement.**
   - **§ 2 Prop. 3.** Its proof, « Démontrons maintenant la proposition : … », is printed after
     Déf. 4, which « Cette proposition légitimera ». It is tagged `[Proof of \ref{…p3…}]`.
   - **§ 2 Theorem 1.** Its proof is cut by the LEMME and the lemma's proof. Both parts are
     tagged. The first part ends « la démonstration repose sur le »; the second part starts
     « Soit a ∈ W ∩ D ».
   - **§ 1 Déf. 1.** The verification that α(W) is a preorder (« Pour montrer qu'on a bien une
     relation de préordre … ») is a `proof` with no tag, so it attaches to Déf. 1.
   - **§ 2, p. 268.** « Pour justifier la définition 6 et démontrer le théorème 3 et son corollaire,
     il suffit de se reporter aux énoncés … dans le cas affin. » This is an untagged `proof`, so it
     attaches to the corollary of Theorem 3, the nearest statement. Theorem 3 and Déf. 6 thus
     have no proof row. The alternative is to tag it for Theorem 3.
   - **§ 3 Prop. 1.** Its proof is « Cela résulte de la », and the sentence runs into the
     heading « PROPOSITION 2. ». This is the edge Prop. 1 → Prop. 2, but the printed text has no
     reference to mark. The same thing happened in Chapter 2 (« La propriété 6° résulte de la »).
   - **§ 5 Theorem 1′.** Its proof is printed on p. 281, at the top of the next page. It is
     untagged and attaches correctly.
4. **Two theorems whose only justification is a free-text lead-in.** These sentences stay prose,
   as in Chapter 2 (« Dans le cas affin, on a le »), so the theorem rows have no proof:
   - « De là on déduit aussitôt le » (§ 2 Theorem 2);
   - « Des propositions 7,8 et 4 résulte le » (§ 5 Theorem 1, with the three references marked).

   The author may prefer to make them `proof`s.
5. **Where a roman statement ends.** Only the THÉORÈMES are printed in italics, so every other
   end is editorial. The rule was « the statement's own paragraphs, up to the first proof or
   commentary ». These are the ends I hesitated over, each kept inside the statement:
   - § 1 Déf. 4 keeps its 3 paragraphs: the α(k) definition, the k-facettes, and « La relation
     α(k) peut être définie directement ».
   - § 2 Déf. 5 keeps « En particulier, soient w, v₁, v₂ … On convient que w est somme de w et du
     convexe vide. ».
   - § 2 Déf. 6 keeps the claim « La donnée du sous-espace distingué l détermine complètement le
     sous-espace distingué l′ ».
   - The corollaries of § 2 Theorems 2 and 3 keep their second paragraph, « Tout sous-espace
     (resp. sous-variété) distingué(e) est obtenu(e) d'une façon et d'une seule … ».
   - § 4 Déf. 3 keeps « On peut encore l'énoncer : … ».
   - § 5 Prop. 1 keeps « D'une façon plus précise : … ». The DÉMONSTRATION proves that sharper
     form.
   - § 5 Prop. 8 keeps the reformulation « II(V, W) peut encore s'énoncer : … ».
   - **§ 6 Prop. 3** keeps the two definitions it introduces: « Nous dirons que W′ est obtenu en
     *raccordant* W₁ et W₂ … en *accolant* W₂ à W₁ ». These named notions have no statement of
     their own. The author may want a definition row for them.
   - § 3 Prop. 8 is the single printed sentence « Le dual d'un corps convexe de S(n) est un
     convexe. ». The next three paragraphs are its proof: the corps convexe as σ = n, ν = −1, and
     « La proposition résulte immédiatement de la proposition 7 ».
   - § 6 Déf. keeps « Si H̊ ∩ W ≠ ∅ et si V et W sont fermés, on a de plus : W ∩ H = V ∩ H. ».
6. **Claims left outside any environment, as commentary.** These are all unproved claims or
   transfers:
   - p. 261, after § 1 Déf. 3: the facts « L'espace tout entier est une variété d'appui, le
     support d'une facette est une variété d'appui », and the counterexample in dimension > ℵ₀;
   - p. 262: the transfers « Les propositions 2, 3, 4 et le corollaire sont valables pour les
     convexes de S(E). La proposition 1 aussi, … » and « Les propositions 5 et 6 sont également
     valables … »;
   - p. 262: « le noyau de k est une variété d'appui de k »;
   - p. 274: « La proposition 3 permet d'ailleurs … la proposition 2 peut donc être démontrée comme
     un corollaire de la proposition 1 »;
   - p. 274, after § 4 Déf. 4: « D'après la proposition précédente, s'il existe m … on a ⟨F, F′⟩
     = 0 »;
   - p. 275, after § 4 Prop. 7: « 𝒟(F) est la facette minimale … ».

   The transfers on p. 262 could matter for Lean: § 1 Props. 1–6 are stated for convexes of a
   vector space, and the text asserts them for S(E) without a separate statement.
7. **Preamble.** It is Chapter 2's preamble, with backward-compatible changes. Chapters 1–2 would
   still print identically.
   - `defin`, `lemme` and `corollaire` use `\bznum`, so their unnumbered forms print no stray
     space. `corollaire` now takes an optional number.
   - Two macros were added: `\intr{X}`, for the printed ring over an arc (interior of X, § 3
     Props. 9–10), and `\Dc`, for the script 𝒟 of § 4.
   - `\setlength{\emergencystretch}{2em}` was added. It is layout only.
   - No new environment was needed.
   - The printed open interval )a, b( is kept as printed, as in Chapter 2.
   - The script letters w, v (classes, convexes of S(E), points) are rendered as plain italic $w$
     and $v$.
8. **Descriptive references marked with `\bzcf`.** They designate a unique statement, and the
   master may unmark them, keeping the printed text:
   - « la remarque ci-dessus » (p. 260) → `c3s1r1`;
   - « le lemme » (p. 266, twice) → `c3s2l1`;
   - « la précédente », « la proposition précédente » (pp. 268, 271, 272, 274) → the preceding
     proposition;
   - « la définition de la variété d'appui » (p. 277) → `c3s1d3`.

   « son corollaire » (p. 268) is not marked.

## [sic] flagged (37 certain, 4 probable)

| p. | printed | intended reading |
|---|---|---|
| 261 | « En dimension finie. on a » | comma for period |
| 261 | « la fermeture compacte E de F » (§ 1 remark, 2°) | F̄; E is the support of W |
| 261 | « W′ = W ∩ L = ∅ » (§ 1 Prop. 6) | « ≠ ∅ » |
| 263 | « x′ᵢ ∈ Vᵢ » (§ 2 Prop. 1 proof) | « x′ᵢ ∈ V′ᵢ » |
| 263 | « de classe v_t » | « vᵢ » |
| 264 | « famillle » | « famille » |
| 264 | « xᵢ. yᵢ ∈ Vᵢ » (§ 2 Prop. 2) | « xᵢ, yᵢ » |
| 265 | « transforme U en U(W) » | « U(w) » |
| 267 | « coujugués » | « conjugués » |
| 268 | « relarivement » | « relativement » |
| 269 | « W′ ⊂ K(S(E′)) » | « ∈ » |
| 269 | « soit W ⊂ C(S(E)) » | « ∈ » |
| 269 | « m′ ∈ E′. la correspondance » (§ 3 Prop. 1) | « La » |
| 270 | « l'hémisphère fermé de E » (§ 3 Prop. 3 proof) | « de S(E) » |
| 270 | « alors D est une variété linéaire » (§ 3 Prop. 5) | « D(W) » |
| 271 | « la proposition résulte » (§ 3 Prop. 7 proof) | capital « La » |
| 271 | « un convexe formé W » | « fermé » |
| 271 | « une section de R^{n−1} − {O} » | « R^{n+1} » |
| 271 | « équivalente à D(B) ⊂ A » (§ 3 Prop. 9 proof) | « D(B) ⊂ D(A) » |
| 271 | « Or (D(B) n'est autre » | stray parenthesis |
| 271 | « la boule du centre M » | « de centre M » |
| 272 | « Soit g ∈ (GS(n − 1, R) » | stray parenthesis |
| 273 | « (cf. § 2 déf. 3) » for α(W) | § 1, déf. 1 (choice 2) |
| 273 | « Soit W ⊂ K(S(E)) » (§ 4 Prop. 2) | « ∈ » |
| 273 | « ⟨A M″₂⟩ = 0 » | « ⟨A M′₂⟩ » |
| 276 | « d'un corps convexe de W » (§ 4 Déf. 6) | « d'un corps convexe W » |
| 276 | « [L ∩ L′ = E » | « = ∅ » |
| 276 | « Le but de ce paragraphe et de démontrer » | « est de » |
| 276 | « la sphère projection » | « projective » |
| 278 | « conxexe » (§ 5 Prop. 6) | « convexe » |
| 278 | « soient C ∈ V̊; B ∈ V̊ » (§ 5 Prop. 7 proof) | « B ∈ Ů »; then « )A′, B( ⊂ Ů » |
| 280 | « THÉORÈME 1. » (projective case) | « THÉORÈME 1′ » (choice above) |
| 281 | « si si V ∩ H̊ » | word doubled |
| 281 | « (cf. § 2, déf. 4) » for the noyau | § 1, déf. 5 (choice 2) |
| 281 | « au-dela » | « au-delà » |
| 281 | « proprieté » | « propriété » |
| 282 | « COROLAIRE. » | « COROLLAIRE » |

**Probable, flagged `[sic?]`, to be ruled.**

- **p. 271, § 3 Prop. 8.** « Le dual d'un corps convexe de S(n) est un convexe. » The proof (via
  Prop. 7: σ = n, ν = −1 for the dual) gives « est un **corps** convexe », and that is the
  content worth having. **Lean ≥ paper would formalize the stronger form; the author should rule
  which statement is the paper's.**
- **p. 272, § 3 Prop. 10 proof.** « il suffit donc d'établir que … D(B) ⊂ D({M}) » is printed
  without the ring of interior, which the display just above requires.
  - Separately, and **mathematically**, not as a misprint: the display « int D(A) = ⋂_{M∈A} int
    D({M}) » interchanges interior and an infinite intersection. It holds only with care, for
    compact A.
- **p. 275, § 4 Prop. 9 proof.** « p ∈ W » reads as « p ∈ D(W) ».
- **p. 279, § 5 Prop. 7 proof.** « C n'appartient donc pas à la variété engendrée par PA_i ».
  No point C is in play there, and the absurdity concerns B.

**Kept as printed, with a comment but no [sic].**

- p. 261: « {O, A, …} » for {O, A₁, …}, and S names both the variété d'appui and the
  ℵ₀-simplexe.
- p. 263: « dans Vᵢ » has no final period.
- p. 264: the heading reads « DÉFINITION 2, — ».
- p. 266: « tout point de V′ » for D′ ∩ W.
- p. 268: the heading « 3. Dualité des corps convexes — » has no period.
- p. 270: « tel que W̄ » (« tel que » meaning « such as »), « D′M », « un sous-espace R^{n+1} »
  (« de » is missing).
- p. 272: « chap. 4. § 1 ».
- p. 275: « PROPOSITION 8. » has no dash.
- p. 277: C names both a convex part and a point.
- p. 278: « le théorème » for § 5 Prop. 7.
- p. 279: « PAᵢ », « PBᵢ » for the points Aᵢ, Bᵢ.
- p. 280: « (b, b′) ∈ ∁H », « (b, b′) ∈ W − V » for ⊂.
- p. 262: « la plus fine sous-variété l » (« de la » is missing).

**Not commented.** These are the period's usage: « Soit F, F′ deux facettes »; « l'application …
défini »; « la réunion … contiennent ».

## Illegible

Nothing illegible was met. The doubtful glyphs were checked on zoomed crops:

- « = ∅ » and « E » on p. 261;
- « L ∩ L′ = E » on p. 276;
- « B ∈ V̊ » on p. 278;
- « au-dela » and « proprieté » on p. 281.

## OCR agreement

The OCR layer was compared with the transcription page by page, by word sequence. The script was
kept outside the repository.

- **Transcription words.** Letters only, words of at least two letters, lower-cased. The
  following were dropped: comments, math (`$…$`, `\[…\]`), command names and environment
  headings. `\bzcf` keeps its printed text.
- **OCR words.** `pdftotext` per page, running heads and the footer line dropped, end-of-line
  hyphenations rejoined. For p. 259, only the part from « CHAPITRE » on is used.
- **Score.** The Dice ratio of the longest matching blocks: 2m / (|OCR| + |transcription|).

| p. | 259 | 260 | 261 | 262 | 263 | 264 | 265 | 266 | 267 | 268 | 269 | 270 | 271 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| % | 98.9 | 95.0 | 96.6 | 95.3 | 95.7 | 93.4 | 97.2 | 82.8 | 95.5 | 98.1 | 96.4 | 95.5 | 96.7 |

| p. | 272 | 273 | 274 | 275 | 276 | 277 | 278 | 279 | 280 | 281 | 282 | 283 | all |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| % | 92.9 | 88.3 | 96.5 | 93.2 | 96.8 | 96.6 | 97.9 | 91.5 | 95.7 | 96.5 | 94.4 | 96.6 | **95.3** |

Overall: 6,862 OCR words, 6,368 transcription words, 6,306 matched. The range is 82.8–98.9%,
and 88–99% without p. 266.

- The residue was read word by word. It is OCR debris of formulas (« pl », « wç », « aç », « cd
  »), the headings that the environments replace, and OCR-joined words (« toutpointde »,
  « diuomm », « sousespace »).
- p. 266 is low because it is almost all formulas: the lemma and the projections P_L, P_D.
- Every word disagreement in running text was checked against the image. The checks turned up
  the misprints of the table above (« au-dela », « proprieté », « COROLAIRE », « conxexe »), and no
  error of the transcription was found.

The Chapter 2 figure (90–98%) was measured by a method its notes do not record, so the two
ranges are comparable only roughly.

## Cross-references marked with `\bzcf`

**To Chapter 1.** There are six occurrences, each checked against
`legacy/labeled/benzecri1960_ch1.tex`:

| p. | printed text | Ch. 1 label |
|---|---|---|
| 262 | « cf. § 1, déf. 9 » (§ 1 Déf. 5, convexe strict) | `bzdef:c1s1d9_convexe_strict` (see choice 2) |
| 268 | « chapitre 1, paragraphe 3, définition 2 » (§ 2 Prop. 4) | `bzdef:c1s3d2_automorphisme_compatible` |
| 268 | « la proposition 4 du chapitre 1, paragraphe 3 » (§ 2 Prop. 5 proof) | `bzprop:c1s3p4_reciproque` |
| 269 | « voir § 1, chap. 1, déf. 3 » (definition of s, § 3 a) | `bzdef:c1s1d3_sphere` |
| 270 | « cf. chap. 1, § 1, déf. 5 » (§ 3 Prop. 3 proof) | `bzdef:c1s1d5_hemisphere` |
| 271 | « cf. chap. 1, § 1, déf. 11 » (§ 3 Prop. 8 proof) | `bzdef:c1s1d11_corps_convexe` |

**To Chapter 2.** None.

**Not marked:**

- « avec les notations du chapitre 1, paragraphes 1 et 2 » (§ 2 Prop. 4): notation, no single
  statement;
- « cf. chap. 4. § 1, prop. 9 et 11 » (p. 272): Chapter 4 is not transcribed yet. This is a
  forward edge into Chapter 4 for § 3 Prop. 11;
- the references to Bourbaki: *E.V.T.* chap. II p. 83 (§ 1 Déf. 3); chap. II § 3 cor. 1 of
  prop. 4 (§ 3 c); chap. II § 3 prop. 4 (§ 5 Prop. 8); chap. II § 4 th. 1, Krein–Milman (§ 6
  Prop. 4). These are **cited results**: under the hub's rules they are to be formalized (mathlib
  has Hahn–Banach separation and Krein–Milman), not assumed.

**Within Chapter 3.** There are 52 `\bzcf` marks inside Chapter 3, so 58 in all with the six to
Chapter 1. There are also the 3 `\ref`s of the proof tags. All resolve to the labels above, and
each is next to its printed text in the file. Their targets by section, with the tags in
brackets:

- **§ 1:** d1 (×3, from §§ 1, 2, 5), d3, p1, p2, p3 (×3), p4, p4c, p5, p6, r1;
- **§ 2:** d3 and d4 (the two [sic] references of choice 2), d6 (×2), l1 (×2), t1 (×2: the plan
  sentence of p. 263 and the corollary's proof; [+2 tags]), t2, t3, p4 (×2), p5, [p3 tag];
- **§ 3:** p6, p7, p9, p10;
- **§ 4:** d1, d1prime, p1 (×2), p2 (×2), p3 (×2), p4 (×2);
- **§ 5:** d2, p4 (×2), p5 (×2), p7, p8, t1 (×2), t1prime (×2).

**Implicit uses that may matter for the DAG.** None of these is a printed reference:

- **§ 1.** Prop. 1 is proved from the remark r1, which is marked.
- **§ 2.**
  - Theorem 2 rests on Theorem 1 and its corollary (« De là »).
  - Theorem 3 and its corollary are proved by the affine Theorem 2 and its corollary (« se
    reporter aux énoncés … affin »).
  - Prop. 4 uses Theorem 3's decomposition (« les p sous-variétés distinguées simples »).
- **§ 3.**
  - Prop. 1 is proved by Prop. 2 (the heading run-in).
  - Prop. 2, 2° is the claim (c).
  - The corollary of Prop. 9 uses Props. 8 and 9.
  - Prop. 11 uses Prop. 10 and Chapter 4 § 1 Props. 9 and 11.
- **§ 4.**
  - Prop. 6 uses Prop. 3.
  - Props. 8 and 9 use the minimality of Prop. 7.
  - Prop. 10 uses Déf. 5.
- **§ 5.**
  - Prop. 7 uses Déf. 2 and Prop. 6 (the contact set).
  - Prop. 8 uses Bourbaki's strict separation.
- **§ 6.**
  - Prop. 1 uses Zorn (« inductif »).
  - The corollary uses Prop. 1, 4°.
  - Props. 2 and 3 use the saturé of Prop. 1.
- **Chapter 1 notions used without citation:**
  - S(E), F, s, S(n) (déf. 3);
  - hémisphère (déf. 5) and its affine structure (déf. 6);
  - segment, demi-droite, diamétralement opposés (déf. 4, 7);
  - partie convexe (déf. 8);
  - corps convexe (déf. 11);
  - balayable, homogène (déf. 15);
  - GS(n, R), GP(n, R).

## Questions (readings taken, not resolved)

1. **« cf. déf. 1 » in § 2 Prop. 2 (p. 264).** I read it as § 1 Déf. 1 (α), not § 2 Déf. 1 (sum).
2. **« cf. § 1, déf. 9 » in § 1 Déf. 5 (p. 262).** I read it as Chapter 1 § 1 Déf. 9.
3. **Whether the claims a–c of § 3, the free-text lead-ins of § 2 Theorem 2 and § 5 Theorem 1,
   and the raccordant/accolant definitions inside § 6 Prop. 3 should carry rows.** I took: no
   (choices 1, 4, 5).
4. **§ 3 Prop. 8, « est un convexe » vs « est un corps convexe ».** I transcribed as printed and
   flagged `[sic?]`.

## Build

`pdflatex -interaction=nonstopmode` was run twice on a copy in `/tmp/bzch3/build`. It produced 28
pages with no error, no warning, no overfull or underfull box, and no undefined reference. The
`\begin`/`\end` counts balance (152 each), and no build file was written into the repository.
