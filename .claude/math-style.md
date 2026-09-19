# Mathematical writing style — the shared rules

The rules for how formal mathematics is written in *Universality and Convergence of Generative
Flows*. **This file is the only copy.** `draft-writer` reads it before writing or rewording a
statement, a proof or a display; `math-stylist` audits against it. Neither restates it —
`notation.tex`'s own header records what happened the last time one rule block lived in three
places, and `CLAUDE.md` says it plainly: two copies drift.

Five rule blocks, A–E. Each rule is stated as a test with a decidable answer, because a rule that
cannot be decided cannot be audited.

Rules A5 and E were added on 2026-09-05 from the author's own words, after they rewrote the
opening paragraph of Appendix H (the doubling graph, lettered I until 2026-09-05), and from their earlier practice: the thesis
(`~/Dropbox/Archive/these_2/these.tex` — chapter 6 opening at `:10863–10911`, tagged proofs at
`:8401`, a roadmap inside a proof at `:9002`) and the ICML 2025 paper
(`~/Dropbox/ErgodicGFN Camera ready/main.tex`). One earlier habit is dropped by E2:
proof-strategy prose between a theorem and its proof (`these.tex:8143`, `main.tex:314`).

Rules A3, A4, A6, B1, B2, B5–B7, C and D were amended on 2026-09-05 from `STYLE-CALIBRATION.md`
(2026-09-04 — a snapshot, not a standard; its numbers come from `audit_style_corpus.py`): every
rule measured against the author's corpus — the thesis, five sole-author `math.GT` papers, the
2026 paper in progress *Topological spacetimes (I)* (`~/Dropbox/lectures/Articles/Espaces-temps
Topologiques/ETT.tex`, the control for how the author writes now), and three GFlowNet papers.
Four amendments reversed a rule and were ruled by the author on 2026-09-05 — the marker form
(R1), argument by analogy (R2), the standing-hypotheses block (R3), connectors (R4); the others
record measured mature practice.

---

## A. Notation: introduced, and scoped

**Global means one thing: defined by `\def` in `notation.tex`.** There are 34 such definitions and
they are the whole global vocabulary of the paper:

```
grep -oE '^\\def\\[A-Za-z]+' notation.tex
```

From that, six tests.

**A1 — a symbol crossing statements must be global.** A symbol used in more than one theorem-like
environment must have a macro in `notation.tex`. `q^*` fails this today: defined in prose at
`proofs.tex:14` and used in the body at `cv_stable.tex:45`, some forty pages ahead of its own
definition.

*Making* a symbol global is `draft-writer`'s edit and never `math-stylist`'s. `notation.tex` is
`\input` by both mainfiles and by `notes_finit_replay.tex`, and the last time a notation pass ran
three times it produced `\def\lamreg{\lamreg}` and a build that never terminated. That repair is
never mechanical.

**A2 — a local symbol is introduced in its scope, and dies with it.** Anything written literally is
local to the environment that introduces it, must be introduced there, and is dead at the closing
`\end{}`. A symbol that escapes is either promoted to `notation.tex` or re-introduced at the new
site: `u_0`, `M` and `E` currently escape proofs in `proofs.tex` into `app_replay.tex:11` and
`:188`, where nothing introduces them.

**A3a — within one scope, one rendered glyph names one object, macro or not.** Shadowing is
judged on the *rendered glyph*, not the source: a bare `S` is fine beside `\Statespace`, a bare
`\mathcal S` is not, because the macro renders as `\mathcal S`. The same test binds two literals:
`g` may not be the divergence generator and a vector field in one proof. The `grep` over
`notation.tex` produces candidates; the finding is made by reading, because a dead or redundant
macro fires the grep and collides with nothing. The live failure is κ: `notation.tex:69` is
`\def\target{\kappa}` with 223 uses, while `\kappa:=` is the Łojasiewicz constant at
`proofs.tex:878`. Same class: `g` is the divergence generator everywhere and `\dln` at
`app_finit.tex:79`.

**A3b — one object is written one way.** An object that has a macro is never typed longhand
beside it (`\foutstar` and a literal `f^*_\rightarrow` in one proof); an object without a macro
keeps one glyph across its scope. Routing `WRITER`: the repair has one form, but which form, and
whether the object deserves a macro, is a writing decision.

Two standing exceptions, both from `notation.tex`'s measure-convention block, and neither a
finding: `\lambda` / `\lamreg` / `\Lambda` are deliberately distinct objects that resemble each
other, and `\eta` is a scalar lifting level rather than a measure. `notes_finit_replay.tex` is out
of scope entirely — the lab record has its own convention by design.

**A4 — every variable defined at first use, and constant families numbered consecutively from
their first index, 0 or 1.** Knuth's rule 11. A base index 0 may carry meaning ($R_0$,
$\varphi_0=1$); primes serve for at most three constants ($C$, $C'$, $C''$). `proofs.tex:626`
numbers its constants `C_4`…`C_7`; `C_1`, `C_2` and `C_3` occur nowhere in the project — a gap,
hence a defect.

**A5 — conditioning is a bar, never a subscript.** Conditional expectation and probability are
written $\mathbb E(\sigma\mid X_0=j)$, $\mathbb P(X_n=y\mid X_0=x)$, with parentheses. A
subscript on $\mathbb E$ or $\mathbb P$ names a law — $\mathbb E_{x\sim\mu}$, $\mathbb E_\mu$ —
and never a state or an index: $\mathbb E_x(X_n)$ reads three ways (the law started at $x$, a
parameter, an index), and on the doubling graph the chain in play itself changes between the loop
closure, the descent chain and the truncation, so the bar has to say which variable is
conditioned. Test: `grep -nE 'mathbb ?\{?[EP]\}?_' *.tex` returns law subscripts only. The sweep ran
2026-09-05: all state/index subscripts were converted to the bar form (76 in `app_doubling.tex`,
9 in `proofs.tex`, one in `app_replay.tex`, two in `cv_divergence.tex`), conditioning on the
initial state of the chain in play ($X_0$ for the loop closure and truncation, $Y_0$ for the
descent chain). What remains are law subscripts, which A5 keeps: `\mathbb E_{x\sim\mu}`,
`\mathbb E_{\widehat\nu}` and the like in `silva_comparison.tex`, `app_pbtrain.tex`,
`app_sgd.tex`, `introduction.tex`, `empirical_training.tex`, and the outer `x\sim\widehat\BackwardPolicy`
sites. `notes_finit_replay.tex` is out of scope by design.

**A6 — `notation.tex` is clean: no macro defined twice, none unused, and every occurrence of a
global object uses its macro.** A dead macro makes A3a misfire (a literal glyph "shadows" a
corpse), a double definition lets the second silently win, and a global object typed longhand is
what the next mechanical notation pass misses. Test: for each `\def` name, `grep -c` across the
`.tex` files that `\input` `notation.tex` is at least one, and no name is defined twice. Adding or
deleting a macro is `draft-writer`'s edit under the build gate, never `math-stylist`'s.

## B. Self-contained statements — appendices only

Knuth's rule 5: *"The statement of a theorem should usually be self-contained, not depending on the
assumptions in the preceding text."*

**Scope: theorem-like environments in the appendices, `_full` or not. Explicitly not the body**,
where `draft-writer.md` §2 governs and moving a technical hypothesis into a body sentence is a
defect rather than a fix.

**B1 — hypotheses are readable off the statement, or off one named source.** Three forms, and
only these: (i) the hypotheses stated in the statement; (ii) *"In the setting of Theorem \ref{…},
assume moreover that…"* — one level deep, one source, named in the statement, as at
`proofs.tex:593` and `:614`; (iii) the section's **standing hypotheses** — a labelled block at the
head of the section, a `definition` environment as `def:doubling_setting` in `app_doubling.tex` or
a `\paragraph{Standing hypotheses.}`, invoked as *"In the setting of Definition \ref{…}"* or
*"Under the standing hypotheses of \S\ref{…}"* (ruled 2026-09-05). A hypothesis carried by a
defined term ("summably $L^2$-mixing", "an EGF family") counts as stated. Not carried, hence a
defect: a hypothesis living in running prose, in a list between environments, in quotation marks,
in a figure, or in another proof's body. `theo:universality_L2_body` (`proofs.tex:119`) fails: "Under the same hypotheses as in Theorem
\ref{…}", no name on the environment, and `\Finit`, `\Fterm` never quantified although the quantity
it bounds depends on them.

**B2 — every symbol in the statement is a `notation.tex` macro, a symbol of the named source
(B1), or introduced in the statement**, and no abbreviation is left unexpanded. Not abbreviations:
a proper name or acronym introduced once in the paper ("BTZ", "EGF", "GFN", the FM/DB/TB
subscripts — after that one expansion), the house abbreviations i.e., resp., a.e., iff, and a
quoted theorem in its source's vocabulary. "EGF" appears in `proofs.tex:119` and is expanded only
in `universality.tex:35`.

**B3 — construct the object, then state its properties.** Serre's article trap: *"there exists an
isomorphism $f$"* followed by *"$f$ is continuous"* silently promotes *a* to *the* and claims a
choice never made; the first statement asserts only that the set of isomorphisms is non-empty.

**B4 — the statement reads as an unambiguous rendering of a quantified formula.** Serre's other
trap: *"(a) there exists $f$; (b) $f$ is …"* — does *some* $f$ satisfying (a) satisfy (b), or
*every* one? If two readings survive, the statement is not finished.

**B5 — a hypothesis or clause that will be cited carries a handle, and is never re-typed.** The
handle is a labelled item — (A), (B) for hypotheses; (i), (ii) for equivalent properties; (a), (b)
for conclusions — or an equation number on exactly the line cited, as `eq:doubling_star` inside
`theo:doubling_unbounded` at `app_doubling.tex:1885`, so a later proof can point at it and a
reader can check it. A `\label` on a multi-line `align` points at its first line, so a cited line
carries its own. Without a handle the condition is re-typed where it is used and drifts ($>0$
becomes $\geq0$).

**B6 — names follow the tiering.** Theorems and the propositions the body cites carry a bracketed
name — the object, or the deliverable as a short sentence; an imported result carries its citation
as its name, with a locator ("Theorem 5 of \cite{…}"). Corollaries are unnamed; lemmas are named
when the body cites them. The draft names 84 of 97 statements (2026-09-04) against the author's
5–26 %; the unnaming is its own pass.

**B7 — twins are diffed, and the body form is a written specialisation.** A body statement and its
`_full` twin differ only by hypotheses the body defers, and the appendix says which — *"The body
form assumes in addition …"*. Twins are diffed at every edit of either; a restatement is a copy,
not a retyping. The `W2` row of the register is the live failure.

## C. Commentary — not restated here

Commentary inside theorem and proof environments is `draft-writer.md` §5, "Bourbaki: a statement or
a proof, nothing else". It is complete there, it is not repeated here, and a Bourbaki violation is
**not a finding of this file**.

Two boundaries belong here because they aim that rule. **Connectors are structure, not
commentary** (ruled 2026-09-05): "Note that", "Recall that", "Observe that", "Finally,", "To begin
with", "It remains to prove", introducing a fact that is then used, are admissible inside
statements and proofs — the author writes them at 0.4–1.3 per 1,000 words in his pure
mathematics; a connector introducing nothing is struck. **True hedges stay struck**: clearly,
obviously, easily, trivially, it is clear / easy / immediate. And **a remark is never cited from a
proof**: a remark whose content a proof needs is a lemma (rule E3).

One observation belongs here because it aims the rule: in this project the proofs are clean, and
the leak is into **theorem statements**:
`proofs.tex:601`, `:791`, `:918`, `app_finit.tex:299`, `:316`, `app_replay.tex:129`,
`app_pbtrain.tex:346`, `app_sgd.tex:88`.

## D. Proof shape

Eight shapes, one rule for choosing, one house form for the markers.

| shape | how it is written |
|---|---|
| **direct argument** | continuous prose, every step naming its justification |
| **computation** | a chain of (in)equalities whose justifications are named before it, after it, or by line ("the second line by Lemma …"); it ends in a sentence stating what it gave — never in a bare display |
| **sub-claim + proof** | a list item led by the claim as a full sentence, emphasised, its proof following in the same item after *Indeed,*; several sub-claims share a list and a closing sentence assembles them; `Claim N:` numbering only when a later item cites one by number |
| **Steps** | a construction whose stages each produce what the next consumes: a list, each item led by its deliverable as a full sentence, emphasised, read in order; a counter only when the order itself is cited |
| **item-mirror** | the statement has parts → one item per part, each closing on its part |
| **case analysis** | one item per case, led by the case, merged by a closing sentence |
| **implication split** | one item per implication, led by it: `\emph{(i) $\Rightarrow$ (ii).}` |
| **lemma ladder** | the difficulty in lemmas, and a titled assembling proof — `\begin{proof}[Proof of Theorem \ref{…}]` — that only cites them |

**The selection rule: choose the shape from the statement and the argument, not from the
references.** The statement has parts → item-mirror. The proof builds an object in stages → Steps.
The argument splits into cases → case analysis. Equivalent properties → implication split. A fact
is needed later by name → a sub-claim, or a lemma if anything **outside** the proof needs it; that
is the boundary. A proof that refers to "the point above" or "by Step 2" has an item that should
have been titled — **a step is never cited by number** (ruled 2026-09-05).

**One shape per level.** A Step or a case may contain sub-claims or a case split; a sub-claim
contains neither. The author's levels have two to four items; there is no floor. The roadmap of a
structured proof, when it has one, is its first sentence inside the environment (rule E3); nothing
before the `\begin{proof}` describes the proof.

**House form of a marker: `\item \emph{<the deliverable, as a full sentence>.}`** — the author's
2026 form (`ETT.tex:2249` "$C_1$ is open.", `:2289` "The procedure is well defined and does not
stall.", `:2306` "The procedure stops."), in which the title *is* the deliverable and there is no
counter. The draft's `\emph{Step N (…)}` — 81 markers and 8 back-references by number — appears
nowhere in the author's corpus; it is converted in its own pass and is the live debt, not the
model.

**Argument by analogy** (ruled 2026-09-05): admitted in one form only — the proof's title declares
it and the body lists the differences, `\begin{proof}[Same argument as Lemma \ref{…}, with two
differences]`. "In the same way", "the proof of Proposition X shows" inside a proof body is not a
proof.

**Supporting tests.** Lamport's *curious child*: after each assertion, "Why?" must be answerable by
naming the facts used — a step whose justification cannot be named is not written. A step cites only
steps that dominate it and never reaches into a sibling sub-proof, whose assumptions may not hold
where it is cited.

What this prevents is Serre's: putting the difficulty in one lemma and discharging it with "it is a
computation", "it follows from the definitions", or a bare QED box. `draft-writer` §5 already bans
those phrases; this rule says what to write instead.

Where the discipline is currently absent: **Appendices C–F hold 25 proofs with no step or sub-claim
marker at all** (`app_finit` 7, `app_replay` 5, `app_pbtrain` 10, `app_sgd` 3),
the 84-line proof of the KL-weak-FM bound at `proofs.tex:289–372` — a headline result — has none,
and the 17 structured proofs carry the retired `Step N` form with 8 back-references by number.

## E. Reading levels — what each pass of the reader is assumed to hold

The paper is read in four passes. Each level of text may assume only what the level above handed
the reader, and may point downward only at milestones. The contract:

| level | text | the reader holds | the text may point at |
|---|---|---|---|
| 0 | the paper's introduction | general knowledge | the milestones, by description; the sections |
| 1 | a section or appendix introduction | the story of the paper; for an appendix, the body section it serves | the headline statements of the section and its subsections, by `\ref`, as milestones |
| 2 | a statement and the prose around it | the story and the section's target | the statement's proof, by its tag; its interpretation, in a `remark` or the prose after it |
| 3 | a proof | the statement being proved, and the statements — not the proofs — of what it cites | labels, hypotheses of the statement, steps of this proof, cited external results |

Three tests.

**E1 — an introduction states the target and names the milestones; it uses nothing.** The first
sentence of a section says what the section proves or measures. The sentences after it name, by
`\ref`, every headline statement the target rests on and each subsection that carries one, in
order. Every `\ref` or `\eqref` in the introduction is a pointer — "Theorem~\ref{…} collects",
"\S\ref{…} measures", "the family \eqref{…} below" — and the sentence around it uses nothing from
its target: no hypothesis is invoked, no symbol is manipulated; naming an object the reader will
meet is allowed, computing with it is not. Every symbol otherwise present is a `notation.tex`
macro, a symbol of the body section the appendix serves, or introduced in the paragraph itself.
No sentence of it describes a proof method. Model: the first paragraph of `app_doubling.tex` (the author's,
2026-09-05); extended model: `these.tex:10863–10911`. A subsection holding more than two
statements opens the same way.

**E2 — the prose around a statement says what it is for and what it gives, never how it is
proved.** Outside `proof` environments no sentence names a Step, "the proof of Theorem X" (except
inside a `\begin{proof}[Proof of …]` tag), "the argument", a function or construction "of the
proof", or justifies a claim "by Lemma X" — justification language belongs inside proofs. A
detached proof is pointed at by its tag; a sentence saying where a proof is, or what it uses, is a
defect. Interpretation of the result goes to a `remark` or to the prose after the statement.
Prose that itself argues — constructs an object, verifies a hypothesis of a cited theorem, derives
an inequality — is not commentary but an unlabelled proof: it becomes a lemma with a proof (rule
D's boundary), or it goes, and which is the author's decision, never a style repair.

**E3 — a proof assumes only its statement and the statements it cites.** Every justification
points at a label, a hypothesis of the statement, a step of this proof, or a named external
result; no `\ref` to a section; no "recall", "as we saw", "above" by position; no mention of the
paper's story. A symbol not in the statement or in `notation.tex` is introduced at the head of the
proof. One roadmap sentence may open a multi-step proof ("The proof has three Steps: …") — inside
the environment, as the thesis does at `these.tex:9002`, never as prose before it.

**Scope.** Appendices in full. Body sections: E1 in the milestone sense only, by description —
the body register is `draft-writer.md` §2 and does not change. Appendix H (the doubling graph) was brought under
E1–E2 on 2026-09-05: `app_doubling.tex:350–366` is the model of a subsection introduction, and
each of its six `\subsubsection`s opens the same way. Pending the author's call there:
`rem:doubling_route` (`:1414`) narrates proof routes; the `c=2.5` scope disclosure of §H.2
(`:2328`) and two arguments of §H.3 — the adjoint that licenses the $\varrho$ column (`:2501`)
and the $G_K$ construction with $\sigma_*\geq K$ (`:2547`) — are proofs carried in prose, which E2
sends to a lemma or out. Where the discipline is otherwise absent: `app_finit.tex:138` and
`silva_comparison.tex:27` describe a proof method in prose; `proofs.tex:4` states a target with
no milestones; `app_finit.tex:4` and `app_replay.tex:4` open on formula recaps.

---

## Two exemplars

Cite these rather than arguing from first principles.

**Best, for rules B and C — `cor:doubling_truncation`, `app_doubling.tex:2135–2248`.** A statement
made in one named setting, with nothing else imported by reference; three numbered conclusions,
each carrying its own handle so a later proof can point at it and a reader can check it; every
constant saying what it depends on; no commentary in either environment, the interpretation left
to the prose that follows. **Not the model for rule D**: its seven `\emph{Step n (…)}` markers and
its "by Step 1", "with Steps 5 and 6" are the form and the back-references the 2026-09-05 ruling
retires. Until a draft proof is converted, D's model is the author's own
`~/Dropbox/lectures/Articles/Espaces-temps Topologiques/ETT.tex:2249–2306` — titled bullets, each
led by its deliverable, an assembly sentence at the end.

**Worst — `theo:universality_L2_body`, `proofs.tex:119–144`.** No bracketed name; no hypotheses of
its own; the bounded quantity never quantified; "EGF" unexpanded; a proof that opens "Continuing
where we left at the end of the proof of Theorem …", reuses that proof's variables without
restating them, and silently redefines `δF_init` against the global definition at `proofs.tex:45`.
