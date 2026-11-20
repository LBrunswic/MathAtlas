# The /atlas-team journal

One entry per iteration, appended by the loop (`.claude/skills/atlas-team/SKILL.md`, step 6).

## 2026-11-20 13:40 · close · T-ett-cbg-anchor
- result: 10/10 rows stated and anchored (Causal.CBG.ETTSection4, strict), all partial over an abstract Geometry until T-ett-port-e0; ETT 119 stated / 57 closed / 58 partial (was 109 / 57 / 48)
- findings: prop:Cauchy_non_max false with the literal C (counterexample on Minkowski space); prop:Cauchy_point_min vacuous with the literal C; proof gaps at l.2303, cor:ext_continue, theo:CBG's directed limit; rem:CBG_analytique needs A3/A4
- questions: OQ-25 (sing_α reading, model_corresponding scope), OQ-26 (the pgcd of defi:ppcm)
- audit: minor (round 1), folded into the curation
- gates: lean-causal ✓ (196 modules, 11926 decls, 0 strict sorry), roadmap ✓, atlas ✓, hub: no new red
- commits: 8e7e7ee 347e1cb 7c5ef82
- next: close T-ett-unanchored (p2), or set up T-bbs-ledger (p2, master); T-ett-port-e0 (p4) unlocks the 10 rows above

## 2026-11-20 14:27 · close · T-ett-unanchored
- result: 17/17 rows dealt with: 13 stated and partial (Causal.Remarks.BTZPoints, .Tarentin, .MassiveManifold, strict, sorry-free, unmarked), 4 not attempted with the missing infrastructure recorded (rem:terminology_borrowed_archytas_tarentum: no assertion; theo:geroch_mr, prop:GX_sing_dec: smooth structure; lem:vecteur: differentiable structure); ETT 131 stated / 57 closed / 70 partial (was 119 / 57 / 58)
- findings: rem:pas_plat (ii) a BTZ point does not violate causal plainness; cor:K_lorentzien's proof omits plainness; cexemple:misner_tarentin's inference needs J⁺(x) ∉ 𝓝 x; cor:massA_causalite's proof checks the wrong hypotheses; rem:recursion_these's hypotheses beyond A ∩ U₁ = ∅ unnecessary
- questions: OQ-27 (Misner J⁺), OQ-28 (regularity of 'Lorentzian'), OQ-29 (recursion seed), OQ-30 (anchor the informal FZenon remark?), OQ-31 (Archytas gloss)
- audit: minor (round 1: non-local witness overclaimed, hreg undisclosed, smoothness sentence, docstring contract), fixed by the closer, checked by the master
- gates: lean-causal ✓ (199 modules, 12014 decls, 0 strict sorry), roadmap ✓, atlas ✓, hub: no new red
- commits: 5e1b357 b2cbc51 458f216
- note: the lock's pid was a dead Bash subshell's ($$), so the liveness check could not see the previous iteration; this lock held the session process's pid instead
- next: set up T-bbs-ledger (p2, master, rule 4); the builder (T-atlas-lean-dag) comes due the iteration after

## 2026-11-20 14:36 · set up · T-bbs-ledger
- result: papers/bbs counted as an external paper (DEC-132, Barbot's DEC-34 wave 0 as the model): snapshot of colI_v1.tex, 71 bbs-prefixed labels, ledger rooted in lean-gx (71 statements, none Lean-stated), curation (4 rows proved where the argument is not a following proof environment, 2 open with no proof in the paper), a three-fragment reading map
- gaps left: the statement DAG has no edges (the authors' \ref's target secondary labels, unresolved by texgraph, as for Barbot); the atlas does not list bbs yet (extract.py PAPERS and hub.toml's "no ledger" badge are the builder's)
- audit: none (master set-up, no agent)
- gates: roadmap ✓, atlas ✓, papers_check all green, hub make -k check ALL GREEN; [gates] known_red emptied
- commits: 0e44367 6884f56
- next: build T-atlas-lean-dag (rule 3: no builder run in the last three iterations); give the builder the bbs listing too

## 2026-11-20 15:26 · build · T-atlas-lean-dag
- result: atlas: Lean dependency edges between labels, through principals (tools/doubledag.py), each with its witness chain (file:line), drawn on the statement DAG with toggle and legend; ETT 48 both / 1036 lean-only / 120 tex-only, Barbot 0 / 103 / 0, gx 29 / 890 / 26; Benzécri and bbs none yet; facts from lean-causal 5e1b357, lean-gx and lean-benzecri 18d8c16; default build Lean-free (make -C reports/atlas lean refreshes); bbs listed as a ledgered paper (71 rows)
- findings: 37 ETT curation decls carry a prose prefix "(related, curve reading (b), CausalScaffold.ChainsCurves)" and resolve to nothing (def:causally_complete 28, rem:causal_completeness_slightly_weaker 9); the committed GFN Bounds double DAG no longer matches its inputs (1,879 vs 2,344 mapped declarations); Benzécri's ledger maps no label to a declaration (names only in scope_notes)
- audit: builder self-check + master: two forced rebuilds byte-identical, headless Chromium 0 page errors
- gates: roadmap ✓, atlas ✓, hub make -k check all green
- commits: 8afcced aa2c707
- next: close T-ett-geroch-iii-i (rule 4); the planner comes due at the next iteration after (five iterations without one) — the three findings above are for it

## 2026-11-20 16:14 · close · T-ett-geroch-iii-i
- result: blocked on OQ-32: theo:geroch's (iii)⇒(i), and the equivalence, are FALSE as printed (chronological Minkowski space satisfies every hypothesis, (ii) and (iii), not (i); sorry-free, audited); the formalized theo:geroch_sing is false too (OQ-33), the paper's not refuted; Causal.LimitCurves graduated (sorry-free infrastructure); CausalScaffold.GerochCauchy holds the counterexample and a conjectured repair ('≤ closed', one open sorry)
- questions: OQ-32 (which repair, and does the compactness lemma hold), OQ-33 (local closedness in SingularFlatAxioms)
- audit: minor (round 1: repair overstated, a citation, a 'time function' wording), fixed by the closer
- gates: lean-causal ✓ (0 strict sorry in 199 files), roadmap ✓, atlas ✓ (Lean overlay refreshed), hub make -k check all green
- commits: 5cccb12 f2938c6
- note: the author's 1bc58a7 (waves of parallel targets, MAX_PARALLEL 6) landed mid-iteration; this iteration finished under the one-target protocol, the next runs as a wave
- next: plan (rule 2: five iterations without a planner run); the planner gets the atlas builder's findings (37 malformed ETT decls, stale GFN double DAG, Benzécri unmapped decls) and the BBS \ref-edge gap

## 2026-11-20 16:37 · plan · —
- result: planned 20 new targets, re-scoped 4 (24 -> 44), roadmap wave-ready (package / depends / exclusive); the loop's findings are targets (T-ett-curation-decls, T-bz-curation-decls, T-ledger-secondary-labels, T-gfn-doubledag-refresh)
- new needs-ruling: T-gfn-doubledag-refresh (regenerate the GFN double DAG or pin the 09-20 measurement), T-bbs-layer-home (BBS-Q1: lean-gx or a new lean-bbs), T-barbot-terminal (leave bucket T?)
- planner notes: package = "none" for master curation targets counts as one more package (cap 3); nothing promotes a planned target when its dependencies close, so chains (port-e0 -> port-e0-sfa) wait for a planner run; T-ett-minkowski-graduate is a graduation; T-ett-cbg-e0 would port a ~52k-line gx import cone
- gates: roadmap ✓, atlas ✓, hub make -k check all green
- commits: 81cb8fe
- wall time: 15:16–16:12; agents in parallel: 1 (planner, alone)
- next: wave of 6: T-ett-ruled-rows, T-bz-universal-cover, T-egf-package, T-ett-port-e0, T-3p1-theorem-m, T-ledger-secondary-labels

## 2026-11-20 17:39 · wave of 6 · T-ett-ruled-rows, T-ledger-secondary-labels, T-egf-package, T-ett-port-e0, T-bz-universal-cover, T-3p1-theorem-m
- T-ett-ruled-rows (master): closed 3/3 rows as DEC-7/DEC-8 rule (ETT 57 -> 60 closed)
- T-ledger-secondary-labels (master): texgraph resolves refs to a statement's secondary labels; bbs 0 -> 17 edges, ett +1; Barbot still 0 (its \preua proofs are not parsed: a separate gap, for the planner)
- T-egf-package (master): lean-egf created (Mathlib-only wave 0), make check green, EGF ledger rooted in it
- T-ett-port-e0: E₀ ported verbatim from gx (Causal.Port.E0*, Causal.E0.btzAxioms); defi:causal_E0 partial on readings OQ-34, OQ-35; audit minor (round 1)
- T-bz-universal-cover: closed 1/1 (Benzécri 36/38 closed), marked; universal cover ported Mathlib-only; audit minor (fixed at graduation)
- T-3p1-theorem-m: research partial: Theorem M's holonomy half proved (scaffold); Θ₋ = Θ₊ needs an HS²/ℝP¹/G̃ layer (for the planner); the notes' orientation conventions disagree (OQ-36); audit minor (round 1)
- gates: lean-causal ✓ (0 strict sorry, 202 files), lean-benzecri ✓, lean-gx ✓, lean-egf ✓, roadmap ✓, atlas ✓ (overlay refreshed, egf added), hub make -k check all green (papers-check red mid-wave only until the ledgers were regenerated after the work commits, as the protocol orders)
- commits: 25da51a 43c0840 4a0e1d4 0fe9136 2ed332b 7a47172 4f60649 cd18d22
- wall time: 16:39–17:39 (Paris); agents in parallel: 3 closers (+3 auditors), 3 master set-ups
- next: wave: T-ett-subextension,T-gx-spherical-cone,T-ett-minkowski-graduate,T-ett-k-borelien,T-gx-slsc-compact,T-ett-curation-decls
- for the planner: planned targets whose dependencies just closed (T-ett-port-e0-sfa, T-ett-e0-model-rows, T-egf-headline) are not promoted by the loop; a Θ-half target for Theorem M; Barbot's \preua proof parsing

## 2026-11-20 19:05 · wave of 6 · T-ett-curation-decls, T-ett-minkowski-graduate, T-ett-k-borelien, T-ett-subextension, T-gx-spherical-cone, T-gx-slsc-compact
- T-ett-curation-decls (master): the 37 prose-prefixed decls moved to notes (DEC-21); ledger.py check refuses a decl that is not a Lean name (fixture added); the stale registers `references` fixture repaired, so `make selftest` passes again
- T-ett-minkowski-graduate: audit minor (no closer: the file was sorry-free but unaudited); Causal.MinkowskiMeasure graduated, docstrings and 7 stale references fixed, the row explicitly partial (instance only), bucket D
- T-ett-k-borelien: rem:K_borelien FALSE as printed (Minkowski space with spokes, local, from a non-Borel subset of ℝ); strongest true forms proved; audit minor (round 1)
- T-ett-subextension: both rows anchored over the CBG geometry (partial until T-ett-cbg-e0); the abstract cauchy_pgcd refuted for non-local causalities (directional and morphism-requiring symmetric readings; the generated equivalence not refuted); audits minor (2 rounds)
- T-gx-spherical-cone: (SO(4), 𝕊³), spherical cones, cone-angle invariance, Thurston suspension (strict); TroyanovSuspensionTheoremS3 stated (2 tagged sorrys); readings OQ-37; audit minor (round 1)
- T-gx-slsc-compact: the Griffiths twin cone (compact Peano continuum) refutes the iff, sorry-free, self-contained non-null-homotopy; audit minor
- gates: lean-causal ✓ (0 strict sorry, 206 files), lean-gx ✓ (0 strict sorry, 48 files), roadmap ✓, atlas ✓, selftest ✓, hub make -k check all green
- commits: 68ad60e 04ac55f acab730 8ecc33f 491f924 7d7d6fa 24d9429 11f649a b308ecb 5cefc9a
- wall time: 17:41–19:05 (Paris); agents in parallel: 4 closers + 1 auditor-only target, 9 audits (incl. 1 re-audit), 1 master target
- next: wave: T-ett-deux-pushup,T-bz-curation-decls,T-bz-chapter2,T-syracuse-package,T-yamabe-package

## 2026-11-20 19:47 · wave of 5 · T-ett-deux-pushup, T-bz-curation-decls, T-bz-chapter2, T-syracuse-package, T-yamabe-package
- T-ett-deux-pushup: rem:deux_pushup's independence witnessed in the library's reading; the plain-without-push-up witness is NON-local, necessarily (on T1: absolutely minimal + causally plain ⇒ push-up); OQ-39 (with OQ-18); audit minor; kept in the scaffold — graduation deferred because /ett-programme's closers were working in lean-causal (strict library frozen)
- T-bz-curation-decls (master): the 36 closed Benzécri rows name their declarations (checked against the environment)
- T-bz-chapter2 (master; the transcription drafted by an agent from the page images, snapshotted, labelled and ledgered by the master): Chapter 2, pp. 246–259, 28 rows (66 total), TO BE CHECKED BY THE AUTHOR; result B leaves T; editorial choices OQ-38
- T-syracuse-package, T-yamabe-package (master): lean-syracuse, lean-yamabe (Mathlib-only wave 0), make check green, Dropbox-ignored, ledgers rooted in them
- protocol change mid-wave: c6dc0bb (the author's /ett-programme) moved /atlas-team to path leases, `git commit --only` and per-paper ledger rebuilds; applied from 041ae20 on
- gates: lean-syracuse ✓, lean-yamabe ✓, lean-causal: DeuxPushup typechecked (warningAsError), package check deferred (programme closers active); roadmap ✓, atlas ✓; hub: papers-check RED for papers/sbierski-mghd and papers/ers-predictability only — /ett-programme's papers (its lease), stale after my lean-causal commit 286cebe; the programme loop rebuilt them on request (89d49b8): papers_check all green again before the push
- commits: cef20e6 0b6a128 979b864 041ae20 2492979 286cebe 8bd43e5 bed0110 673464a
- wall time: 19:07–20:40 (Paris); agents in parallel: 1 closer + 1 transcriber, 1 audit, 4 master set-ups
- next: wave: T-ett-gxsingular-dec25; owed: graduate CausalScaffold.DeuxPushup at the next lean-causal integration with no programme closer in the package; planned targets with done dependencies await a planner run

## 2026-11-20 20:14 · plan · —
- result: 44 -> 69 targets (18 ready, 18 planned, 6 needs-ruling, 4 blocked); promoted the targets the last waves unblocked; a full Benzécri Chapter 2 plan; first targets for lean-syracuse and lean-yamabe; Theorem M's Θ-half layers; follow-ups as targets (DeuxPushup graduation gated on lean-causal being free, pgcd retirement, Barbot proof macros, hub.toml refresh); nothing duplicating /ett-programme's roadmap
- new needs-ruling: T-yamabe-scope (which §6 analysis is a named external), T-egf-families (the two spectral-gap theorems: externals or proved), T-bz-transcription-check now covering Chapter 2
- gates: roadmap ✓, atlas ✓, hub make -k check all green
- commits: 4d9a2da
- wall time: 19:50–20:40 (Paris); agents: 1 (planner, alone)
- next: wave: T-egf-headline,T-bz-c2-poches,T-bz-c2-mesure,T-gx-cone-football,T-syr-base,T-yamabe-quotient (no lean-causal: /ett-programme's closers are there)

## 2026-11-20 21:25 · wave of 6 · T-syr-base, T-gx-cone-football, T-yamabe-quotient, T-bz-c2-poches, T-bz-c2-mesure, T-egf-headline
- T-syr-base: def:define_n__n_ closed; def:ring_define, def:ring_define_2, lem:base, lem:ring_maps_rhs_n_ partial on findings of the printed text (f_A's cases swapped; T_A undefined at −1/3 when 3 is a unit; Z/2Z is a Z/2Z-ring with 2 = 0), strongest true forms proved, OQ-42; audit major (an accidental bold mark), round 1, AUDIT-2 clean; ledger.py learned `class` and `scoped`
- T-gx-cone-football: the football F_θ, the first IsConeSphere with genuine cone points; cex:start_singular_manifold_homeomorphic stays partial (s = 2 < 3); audit minor
- T-yamabe-quotient: lem:stability and rem:sign proved over an abstract measured model, partial pending T-yamabe-scope and OQ-44; eq:hoelder's boundary line false as printed (exponent 1/(N−1), sharp); audit minor, round 1
- T-bz-c2-poches: closed 7/7 (Ch. 2 § 1); the unlabelled examples need p injective (OQ-46); audit minor, round 1
- T-bz-c2-mesure: closed 5/5 (Ch. 2 § 2, Déf. 1–4, Prop. 1); property 1° fails in dimension 0 (OQ-45), to be passed to the T-bz-c2-proprietes and T-bz-c2-hilbert dispatches; audit minor, round 1; owed: Poches and Mesure both prove the chart change on a projective segment and GS(E)'s action on closed segments (kb 0006), keep one copy in a later target
- T-egf-headline: closed 2/4 — theo:universality_true (Lean ≥ paper; the general form needs only γ₀ < ∞, γₙ → 0) and def:summably_mixing; def:egf, def:universal_family partial on OQ-48–50; both marks rest on the confirmation OQ-47; audits minor (round 1), minor (wording, fixed at graduation)
- gates: lean-syracuse ✓, lean-gx ✓, lean-yamabe ✓, lean-benzecri ✓ (0 sorry, 31 strict files), lean-egf ✓ (0 sorry, 130 strict declarations), roadmap ✓, atlas ✓ (Lean overlay refreshed for the wave's six papers; the four lean-causal papers' overlay left stale for /ett-programme), hub make -k check all green
- commits: 895d501 f382449 e4e12c0 4621f2b 254419e 245693e a3690fd 742a9c5 599595d b62ca3a
- wall time: 20:16–21:25 (Paris); agents in parallel: 6 closers, 8 audits (2 re-audits), 5 fix rounds
- next: wave: T-ett-deux-pushup-graduate (exclusive in lean-causal, coordinated with /ett-programme), T-gx-troyanov-triangle, T-bz-c2-projection, T-bbs-triage, T-barbot-proof-macros (the builder T-atlas-hub-refresh if due)

## 2026-11-20 23:10 · wave of 6 · T-ett-deux-pushup-graduate, T-barbot-proof-macros, T-bbs-triage, T-atlas-hub-refresh, T-bz-c2-projection, T-gx-troyanov-triangle
- T-ett-deux-pushup-graduate (master): Causal.DeuxPushup strict (file move, no statement changed); rem:deux_pushup stays partial (OQ-39); done in a window /ett-programme opened for it, lean-causal leased and handed back
- T-barbot-proof-macros (master): texgraph reads a paper's proof macros (`proof_macros` in ledger.toml); papers/barbot 0 → 17 dependencies, 28/44 statements with a proof; ledger check fails on a macro that opens no proof (fixture); every other ledger byte-identical
- T-bbs-triage (master): 71 rows bucket D, each with its REVIEW §A row, layer and wave; no row needs only L0–L1, so bbs close targets wait on BBS-Q1 (T-bbs-layer-home)
- T-atlas-hub-refresh (builder): hub.toml current; lib cards for every package; two -B rebuilds byte-identical, 0 page errors (re-checked by the master)
- T-bz-c2-projection: Ch. 2 § 3 Prop. 1 proved sorry-free for n ≥ 1, unmarked, partial on OQ-45 (a) (false as printed for n = 0); a slip in the printed 1°; audit minor, fixed at graduation
- T-gx-troyanov-triangle: Troyanov's theorem for s = 3 (GX.troyanovTheorem_three, exactly TroyanovTheorem at s = 3) by doubling a spherical triangle, sorry-free; Troyanov reduced to s ≥ 4; cex row stays partial; audit minor, fixed at graduation; owed to T-gx-troyanov: l.1930's bound against MR1005085
- gates: lean-causal ✓, lean-benzecri ✓, lean-gx ✓, roadmap ✓, atlas ✓ (overlay refreshed for lean-gx, lean-benzecri; lean-causal's stays stale while /ett-programme holds it); hub: papers_check all green, one red not this wave's (gate-tests: /ett-programme's in-flight ladder.toml not re-emitted, its lease)
- commits: c628a74 d2af417 5c3474e a06acc2 dbccb84 6d457b8 d6cd71b 6195fbb 3591466 bd9c8f8
- wall time: 21:23–23:10 (Paris); agents in parallel: 2 closers + 1 builder, 2 audits; 4 master targets
- coordination: shared cap 6 with /ett-programme (3 + 3, then 1 + 5); OQ-id race caught before it landed (the programme's rows renumbered OQ-51, OQ-52)
- next: plan — the only ready closers are in lean-causal (T-ett-port-e0-sfa, T-ett-e0-model-rows, T-ett-gxsingular-dec25), which /ett-programme holds exclusively; planned targets whose dependencies are now all done (T-bz-c2-hilbert, T-syr-rep, T-syr-integer-bounds, T-egf-backward-policy) await promotion; T-bz-c2-lignes, -compact, -theoreme and T-egf-sampling follow in chain
