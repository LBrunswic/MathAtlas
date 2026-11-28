#!/usr/bin/env python3
"""The causality ladder of ETT (programme/ladder.toml): check it, classify it, emit its Lean rules.

    python3 tools/ladder.py check [--file F]   schema, ids, sorts, labels, Lean names, no contradiction
    python3 tools/ladder.py matrix [--file F]  every ordered pair of properties, classified (below)
    python3 tools/ladder.py emit-lean [--dry-run]  write lean-causal/Causal/Ladder/Rules.lean from the
                                               checked edges and facts (and its tests,
                                               Causal/Ladder/Test.lean); when a property carries
                                               a `dual` key, also Causal/Ladder/Dual.lean and
                                               DualTest.lean, unless they are hand-written
    python3 tools/ladder.py dot                the implication DAG in Graphviz
    -h, --help anywhere                        this text; nothing is read or written. Any other
                                               argument a subcommand does not take: exit 2.
                                               --dry-run: say whether Rules.lean / Test.lean would
                                               change, write nothing.

Schema. Every table and key not listed here is a violation (a misspelt `standing` would otherwise
be dropped silently, and its edge chained as unconditional).

    [ambient]        optional. standing (list of words, below), label (an ETT label), note. Absent:
                     the standing hypotheses of ETT's topological spacetimes, T2 and
                     second_countable (def:category_topological_spacetimes, ETT.tex:255).
    [[property]]     id, lean, what; label (a label of papers/ett/ledger/ledger.json); sort
                     (causality | geometry | pair; absent means causality); dual (optional, below)
    [[implies]]      from (an id or a list, read as a conjunction), to, witness, status; under (side
                     conditions in words); standing (list of words)
    [[fails]]        from (an id or a list: the counterexample has every one), to, witness, status;
                     space (list of words: what the counterexample's space satisfies; absent: the
                     ambient, i.e. the counterexample is one of ETT's spacetimes)
    [[consequence]]  at (an id or a list, read as a conjunction, of one sort), statement, witness,
                     status; under; standing
    [[open]]         from, to, note
    [[transfer]]     pair (an id of sort pair: C nested in C', C the narrower), property (an id of
                     sort causality), direction (to_narrower: C' has it, hence C; or to_wider;
                     absent means to_narrower), narrower and wider (lists of causality-sort ids
                     asked besides of C and of C'), exactly one of witness (a Lean proof of the
                     transfer; with standing) or counterexample (a Lean nesting whose source has
                     `property` and the listed ids, whose target has the listed ids and lacks
                     `property`; with space), status; under (a witness proved only under a
                     condition in words: conditional, not applied by the contradiction check)
    [[fact]]         property (an id: it holds outright on every object of its sort, no premise),
                     witness, status; standing; note (T-tool-ladder-py-2)
    [[edge_hypothesis]]  id, lean, what; label (an ETT label); reads (words: what it is a
                     hypothesis on, e.g. "a causality and an open set"); note. A localisation hypothesis
                     the rulings keep OUT of the nodes (DEC-159, DEC-162, DEC-166 (b)): it classifies no
                     pair, so matrix and emit-lean ignore the table; an `under` may cite it by id, and
                     tools/binder.py accepts its ids as localisation, open_localisation and proves ids.
                     Its id is no [[property]] id, and its Lean name resolves (T-tool-ladder-edge-hypotheses).

status is seed | checked. Lean names (property `lean`, every witness and counterexample) resolve
NAMESPACE-EXACTLY: a name is found when it is the full name of a declaration of
lean-causal/Causal (namespace and section blocks read, comments blanked: lean_index); a dotted
suffix is not enough. tools/binder.py inherits this.

The `dual` key (T-tac-ladder-dual-key). Time reversal C ↦ C.dual, on a [[property]] of sort causality
or pair (never geometry: those have none). It is either

    dual = "<full name>"   a two-sided node: its time-reversal lemma. An iff `C.dual.P ↔ C.P` (for a
                           pair node `R C.dual C'.dual ↔ R C C'`, both causalities reversed, an open
                           W kept), or the implication `C.P → C.dual.P` with one explicit hypothesis,
                           which is enough since `C.dual.dual` is `C` by `rfl`;
    dual = { introduces = "<id>", lemma = "<full name>" }
                           a one-sided node P of sort causality (P of C.dual is its past form, not a
                           node): the two-sided node Q it introduces, `C.P ∧ C.dual.P → C.Q`, with
                           the library lemma that builds it. That is an iff `C.Q ↔ C.P ∧ C.dual.P`,
                           a theorem `(hf : C.P) (hp : C.dual.P) : C.Q`, or Q's own definition
                           (its `lean`) when `C.Q` is `C.P ∧ C.dual.P` by definition.

check refuses: a key on a geometry node; a lemma that names no declaration; a lemma (and, for the
node's own definition, its module) outside the ETT layer, or in a module that is or imports
Causal.Ladder.Rules or Causal.Ladder.Dual (Dual.lean is where the rules are written, and Rules
imports it); a lemma whose statement, read off the source, has neither shape, or has one for
another definition (the node's name, the last component of its `lean`, must occur as a whole word
or followed by `On` only, its form on an open set: dual_stronglyCausalOpen is not strongly_causal's
lemma, dual_causallyArcConnectedOn is causally_arc_connected's); an introduction on a pair node, of an unknown id, of the node itself, of a node of
another sort, or of a node that is not two-sided (its own key is an introduction, or it has no
key); and a contradiction across time reversal: a counterexample that has, by the edges and facts
valid on its space applied to C and to C.dual, the reversals and the introductions, a property
of C or of C.dual it lacks (a key the ladder's counterexamples call one-sided). emit-lean turns the
keys into rules (above `emit_dual`); with no key it writes what it wrote before the key existed.

Standing hypotheses. `standing` lists hypotheses on the topological space M that are not ladder
nodes; each word is a Mathlib class on M, which the witness takes as an instance argument:

    T0 T1 T2 T3 regular normal   T0Space T1Space T2Space T3Space RegularSpace NormalSpace
    R1                           R1Space
    first_countable              FirstCountableTopology
    second_countable             SecondCountableTopology
    separable                    TopologicalSpace.SeparableSpace
    nonempty                     Nonempty
    preconnected connected       PreconnectedSpace ConnectedSpace
    locally_connected            LocallyConnectedSpace
    locally_compact              LocallyCompactSpace
    sigma_compact compact        SigmaCompactSpace CompactSpace
    paracompact                  ParacompactSpace
    metrizable                   TopologicalSpace.MetrizableSpace

with the implications T3 → T2, regular; T2 → T1 → T0; T2 → R1; regular → R1; second_countable → first_countable,
separable; connected → preconnected, nonempty; compact → sigma_compact; metrizable → T2 (each a
Mathlib instance, so a context with the stronger class gives the weaker). A set of words is read
closed under them: the ambient {T2, second_countable} is {T0, T1, R1, T2, second_countable,
first_countable, separable}.

Classification. An edge is valid on a space S (a closed set of words) when its `standing` is in S.
For each property a, closure(a) is the transitive closure of {a} through the [[implies]] edges
valid on the ambient (a conjunction premise counts only when all its ids hold). An [[implies]] with
`under` and no `standing` is read as before this field existed: chained as unconditional (since
T-lad-local-nodes its `under` holds only separation and countability words, which are ambient; the
keeper migrates them to `standing`). `matrix` gives every ordered pair (a, b), a != b, the first of
these values that applies:

    ill-typed         a and b are of different sorts: neither implication is a statement. Not
                      counted among the pairs to classify.
    implied           b is in closure(a): exact on ETT's spacetimes. The closure starts from a and
                      the [[fact]]s of a's sort valid on the ambient (a property holding outright on
                      its sort's objects, no premise: every property of the sort implies it).
    fails             a counterexample refutes it: it has every id of its `from`, hence everything
                      the edges valid on ITS space chain from them (a' among these), and it lacks
                      `to`, hence every b' whose closure on its space reaches `to`; (a', b') fails.
                      A non-Hausdorff counterexample says `space = ["T1"]` (or less), and is then
                      not read against an edge whose standing asks T2. A counterexample is also read
                      backwards through a conjunctive edge valid on its space, to a fixpoint: lacking
                      the conclusion and having every premise but one, it lacks that one and every id
                      implying it (T-tool-ladder-py-2).
    open              an [[open]] entry.
    fails-off         only counterexamples OFF the ambient refute it: their `space` (closed) does
                      not contain the ambient's words (the vee, space = ["T0"], is no ETT
                      spacetime), so the pair may still hold on every ETT spacetime. Not counted as
                      classified; `matrix` names the spaces' words; an [[open]] entry for it stays
                      legal. `fails` counts only counterexamples whose space contains the ambient
                      (no `space`, or one that implies the ambient's words) (T-tool-ladder-space).
    implied-standing  b is reached from a only through an edge whose standing is beyond the
                      ambient (e.g. connected): implied under standing hypotheses, not on every
                      ETT spacetime. Not counted as classified; `matrix` names the words.
    unknown           none of these.

`check` fails on: a counterexample that has its `to` by the edges and facts valid on its space (a
contradiction), an [[open]] pair already implied or refuted, an entry joining two sorts, a
[[transfer]] whose counterexample satisfies the hypotheses of a proved, unconditional transfer of
the same property and direction (one with `under`, proved only under a condition in words, is
conditional and not applied) (its nesting reaching the proved one's in the pair-sort closure), and every
schema fault above. Its summary line is

    ladder: P properties, I implications, F counterexamples, C consequences; K of N ordered pairs
    classified (within one sort), X ill-typed (across sorts), S implied under standing only,
    R refuted off the ambient only, T transfers

(one line; `N violation(s)` after the semicolon instead when there are any): K counts implied,
fails and open pairs among the N pairs within one sort; summary() gives the same numbers as a
dict. What emit-lean makes of `standing`, and which edges it skips, is said above `emitted`.
No model is called; Lean names are resolved by reading the sources.
"""
import glob
import json
import os
import re
import sys
import tomllib

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
FILE = os.path.join(ROOT, "programme", "ladder.toml")
LEAN_ROOT = os.path.join(ROOT, "lean-causal")
RULES = os.path.join(LEAN_ROOT, "Causal", "Ladder", "Rules.lean")
ETT_LEDGER = os.path.join(ROOT, "papers", "ett", "ledger", "ledger.json")
STATUS = ("seed", "checked")
SORTS = ("causality", "geometry", "pair")
DEFAULT_SORT = "causality"
DIRECTIONS = ("to_narrower", "to_wider")
CLASSIFIED = ("implied", "fails", "open")

# word -> (the Mathlib class on M, the words it implies). Each implication is a Mathlib instance.
STANDING = {
    "T0": ("T0Space", ()),
    "T1": ("T1Space", ("T0",)),
    "T2": ("T2Space", ("T1", "R1")),
    "R1": ("R1Space", ()),
    "regular": ("RegularSpace", ("R1",)),
    "T3": ("T3Space", ("T2", "regular")),
    "normal": ("NormalSpace", ()),
    "first_countable": ("FirstCountableTopology", ()),
    "second_countable": ("SecondCountableTopology", ("first_countable", "separable")),
    "separable": ("TopologicalSpace.SeparableSpace", ()),
    "nonempty": ("Nonempty", ()),
    "preconnected": ("PreconnectedSpace", ()),
    "connected": ("ConnectedSpace", ("preconnected", "nonempty")),
    "locally_connected": ("LocallyConnectedSpace", ()),
    "locally_compact": ("LocallyCompactSpace", ()),
    "sigma_compact": ("SigmaCompactSpace", ()),
    "compact": ("CompactSpace", ("sigma_compact",)),
    "paracompact": ("ParacompactSpace", ()),
    "metrizable": ("TopologicalSpace.MetrizableSpace", ("T2",)),
}
AMBIENT = ("T2", "second_countable")
AMBIENT_LABEL = "def:category_topological_spacetimes"

KEYS = {
    "ambient": {"standing", "label", "note"},
    "property": {"id", "lean", "what", "label", "sort", "dual"},
    "implies": {"from", "to", "witness", "status", "under", "standing"},
    "fails": {"from", "to", "witness", "status", "space"},
    "consequence": {"at", "statement", "witness", "status", "under", "standing"},
    "open": {"from", "to", "note"},
    "transfer": {"pair", "property", "direction", "narrower", "wider", "witness", "counterexample",
                 "status", "under", "standing", "space"},
    "fact": {"property", "witness", "status", "standing", "note"},
    "edge_hypothesis": {"id", "lean", "what", "label", "reads", "note"},
}


def load(path=FILE):
    with open(path, "rb") as fh:
        return tomllib.load(fh)


def ids_of(x):
    """An id or a list of ids, as a list; None when it is neither."""
    if x is None:
        return []
    if isinstance(x, str):
        return [x]
    if isinstance(x, list) and all(isinstance(y, str) for y in x):
        return list(x)
    return None


def sort_of(data):
    return {p.get("id"): p.get("sort", DEFAULT_SORT) for p in data.get("property", [])}


def vocab_closure(words):
    """`words` closed under the vocabulary's implications (unknown words are kept as they are)."""
    out, todo = set(), list(words)
    while todo:
        w = todo.pop()
        if w not in out:
            out.add(w)
            todo.extend(STANDING.get(w, ("", ()))[1])
    return frozenset(out)


def ambient(data):
    """The ambient space: the ladder's [ambient] standing, or ETT's spacetimes, closed."""
    a = data.get("ambient")
    words = a.get("standing", AMBIENT) if isinstance(a, dict) else AMBIENT
    return vocab_closure(words if isinstance(words, (list, tuple)) else AMBIENT)


def standing(e):
    s = e.get("standing", [])
    return list(s) if isinstance(s, list) else []


def space(f, data):
    """The closed set of words a counterexample's space satisfies (absent: the ambient)."""
    if "space" in f and isinstance(f["space"], list):
        return vocab_closure(f["space"])
    return ambient(data)


def on_ambient(f, data):
    """Is the counterexample `f` one of the ambient's spaces (its closed space contains the ambient's
    words)? Only such a counterexample refutes a pair of the matrix (T-tool-ladder-space)."""
    return ambient(data) <= space(f, data)


def valid(e, on):
    """Is the edge `e` valid on the closed space `on` (None: on every space, i.e. any standing)?"""
    return on is None or set(standing(e)) <= on


def edges_on(data, on):
    return [e for e in data.get("implies", []) if valid(e, on) and ids_of(e.get("from"))]


def facts_on(data, on):
    """The properties holding outright ([[fact]], premise-free) on the closed space `on` (None: every
    fact, whatever its standing), by sort: sort -> set of ids (T-tool-ladder-py-2)."""
    sort, out = sort_of(data), {}
    for f in data.get("fact", []):
        if valid(f, on) and f.get("property") in sort:
            out.setdefault(sort[f["property"]], set()).add(f["property"])
    return out


def _start(ids, facts, sort):
    """`ids` with the facts of their sort: what a space with `ids` has before any edge."""
    have = set(ids)
    for x in ids:
        have |= facts.get(sort.get(x, DEFAULT_SORT), set())
    return have


def _saturate(start, edges):
    have = set(start)
    changed = True
    while changed:
        changed = False
        for e in edges:
            if set(ids_of(e.get("from")) or ()) <= have and e.get("to") not in have:
                have.add(e.get("to"))
                changed = True
    return have


def closure(data, on=None):
    """id -> set of ids implied (reflexive), through the implies edges valid on the ambient (or on
    the closed space `on`, a set of words)."""
    on = ambient(data) if on is None else frozenset(on)
    edges, facts, sort = edges_on(data, on), facts_on(data, on), sort_of(data)
    return {p["id"]: _saturate(_start([p["id"]], facts, sort), edges) for p in data.get("property", [])}


def closure_any(data):
    """id -> set of ids implied through every implies edge, whatever its standing."""
    edges, facts, sort = edges_on(data, None), facts_on(data, None), sort_of(data)
    return {p["id"]: _saturate(_start([p["id"]], facts, sort), edges) for p in data.get("property", [])}


def counterexample(data, f, cache=None):
    """(has, lacks) of the counterexample `f`: the ids its space has (the closure of its `from`, with
    the facts of their sort, through the edges valid on its space) and the ids it lacks (those whose
    closure there reaches its `to`), read backwards through conjunctive edges to a fixpoint: an edge
    valid on its space whose conclusion it lacks and all of whose premises but one it has makes it
    lack that one, and every id implying it (T-tool-ladder-py-2). The backward reading finds no
    contradiction the forward one misses (a premise it would lack and have makes the conclusion had);
    it classifies pairs."""
    on = space(f, data)
    key = on
    if cache is not None and key in cache:
        edges, clo, facts = cache[key]
    else:
        edges, facts, sort = edges_on(data, on), facts_on(data, on), sort_of(data)
        clo = {p["id"]: _saturate(_start([p["id"]], facts, sort), edges) for p in data.get("property", [])}
        if cache is not None:
            cache[key] = (edges, clo, facts)
    has = _saturate(_start(ids_of(f.get("from")) or [], facts, sort_of(data)), edges)
    lacks = {b for b, c in clo.items() if f.get("to") in c}
    changed = True
    while changed:
        changed = False
        for e in edges:
            frm = ids_of(e.get("from")) or []
            if e.get("to") in lacks and len(frm) > 1:
                missing = [x for x in frm if x not in has]
                if len(missing) == 1:
                    new = {b for b, c in clo.items() if missing[0] in c} - lacks
                    if new:
                        lacks |= new
                        changed = True
    return has, lacks


def refuted(data, clo=None, off=False):
    """Pairs (a, b) refuted by a counterexample, propagated along the closure valid on its space.
    Only counterexamples on the ambient count (on_ambient); with `off`, only those OFF it.
    With `clo` given (id -> set), that one closure is used for every counterexample, and a list
    `from` contributes the union of its members' closures (the reading of older callers)."""
    bad, cache = set(), {}
    for f in data.get("fails", []):
        if on_ambient(f, data) == off:
            continue
        frm = ids_of(f.get("from")) or []
        if clo is not None:
            has = set().union(*(clo.get(x, {x}) for x in frm)) if frm else set()
            lacks = {b for b, c in clo.items() if f.get("to") in c}
        else:
            has, lacks = counterexample(data, f, cache)
        bad.update((a, b) for a in has for b in lacks)
    return bad


def lean_names(root=LEAN_ROOT):
    """The full names of the declarations of lean-causal/Causal (lean_index's)."""
    return set(lean_index(root)["decls"])


def resolves(name, names):
    """Namespace-exact: `name` is the full name of a declaration."""
    return isinstance(name, str) and name in names


def ett_labels(path=None):
    """The labels of papers/ett/ledger/ledger.json, or None when the ledger is absent."""
    path = ETT_LEDGER if path is None else path
    if not os.path.exists(path):
        return None
    with open(path, encoding="utf-8") as fh:
        return {r["label"] for r in json.load(fh)["statements"]}


def _words(tag, e, key, errs):
    v = e.get(key)
    if v is None:
        return
    if not isinstance(v, list) or not all(isinstance(w, str) for w in v):
        errs.append("%s: %s must be a list of words" % (tag, key))
        return
    for w in v:
        if w not in STANDING:
            errs.append("%s: unknown %s word %r (the vocabulary: %s)" % (tag, key, w, ", ".join(STANDING)))


def _label(tag, lab, labels, errs):
    if labels is None:
        errs.append("%s: label %s cannot be checked: no ETT ledger (%s)" % (
            tag, lab, os.path.relpath(ETT_LEDGER, ROOT)))
    elif lab not in labels:
        errs.append("%s: label %s is not a label of papers/ett/ledger/ledger.json" % (tag, lab))


def _one_sort(tag, xs, sort, errs):
    sorts = sorted({sort[x] for x in xs if x in sort})
    if len(sorts) > 1:
        errs.append("%s: joins two sorts (ill-typed): %s" % (
            tag, ", ".join("%s (%s)" % (x, sort[x]) for x in xs if x in sort)))


def _transfer_sides(t):
    """(source ids, target ids) of a transfer: the wider C' is the source of `to_narrower`."""
    nar, wid = ids_of(t.get("narrower")) or [], ids_of(t.get("wider")) or []
    return (wid, nar) if t.get("direction", "to_narrower") == "to_narrower" else (nar, wid)


def check(data, names=None, labels=None, index=None):
    """The violations of the ladder `data` (a list of strings). `names` (the full names of the
    declarations), `labels` (the ETT labels) and `index` (lean_index's, read only when a property
    carries a `dual` key) default to the repository's."""
    errs = []
    names = lean_names() if names is None else names
    labels = ett_labels() if labels is None else labels
    for kind in KEYS:
        if kind != "ambient" and kind in data and not (
                isinstance(data[kind], list) and all(isinstance(e, dict) for e in data[kind])):
            errs.append("%s: must be an array of tables ([[%s]])" % (kind, kind))
    data = {k: v for k, v in data.items() if k == "ambient" or k not in KEYS or (
        isinstance(v, list) and all(isinstance(e, dict) for e in v))}
    for k in data:
        if k not in KEYS:
            errs.append("unknown table %r (the tables: %s)" % (k, ", ".join(KEYS)))
    for kind, allowed in KEYS.items():
        rows = data.get(kind)
        rows = [rows] if isinstance(rows, dict) and kind == "ambient" else (rows or [])
        for e in rows:
            for k in sorted(set(e) - allowed):
                errs.append("%s %s: unknown key %r (the keys: %s)" % (
                    kind, e.get("id") or e.get("witness") or e.get("counterexample") or "?", k,
                    ", ".join(sorted(allowed))))
    amb = data.get("ambient")
    if amb is not None:
        if not isinstance(amb, dict):
            errs.append("ambient: must be a table")
        else:
            _words("ambient", amb, "standing", errs)
            if amb.get("label"):
                _label("ambient", amb["label"], labels, errs)
    props = data.get("property", [])
    ids = [p.get("id") for p in props]
    known = set(ids)
    sort = sort_of(data)
    for i in sorted(set(x for x in ids if ids.count(x) > 1), key=str):
        errs.append("property %s: duplicate id" % i)
    for p in props:
        for k in ("id", "lean", "what"):
            if not p.get(k):
                errs.append("property %s: missing %s" % (p.get("id"), k))
        if p.get("lean") and not resolves(p["lean"], names):
            errs.append("property %s: Lean definition %s not found in lean-causal (a full name)" % (
                p.get("id"), p["lean"]))
        if p.get("sort", DEFAULT_SORT) not in SORTS:
            errs.append("property %s: sort %r is not one of %s" % (p.get("id"), p.get("sort"), SORTS))
        if p.get("label"):
            _label("property %s" % p.get("id"), p["label"], labels, errs)
    ehs = data.get("edge_hypothesis", [])
    eids = [e.get("id") for e in ehs]
    for i in sorted(set(x for x in eids if eids.count(x) > 1), key=str):
        errs.append("edge_hypothesis %s: duplicate id" % i)
    for e in ehs:
        tag = "edge_hypothesis %s" % e.get("id")
        for k in ("id", "lean", "what"):
            if not e.get(k):
                errs.append("%s: missing %s" % (tag, k))
        if e.get("id") in known:
            errs.append("%s: id is a [[property]] id (an edge hypothesis is not a node)" % tag)
        if e.get("lean") and not resolves(e["lean"], names):
            errs.append("%s: Lean definition %s not found in lean-causal (a full name)" % (tag, e["lean"]))
        if e.get("reads") is not None and not isinstance(e["reads"], str):
            errs.append("%s: reads must be words (a string)" % tag)
        if e.get("label"):
            _label(tag, e["label"], labels, errs)
    if has_dual_keys(data):
        index = lean_index() if index is None else index
        for pid, why in dual_keys(data, index)[2]:
            errs.append("property %s: dual: %s" % (pid, why))

    def lean_ref(tag, key, e, required=True):
        if not e.get(key):
            if required:
                errs.append("%s: missing %s" % (tag, key))
        elif not resolves(e[key], names):
            errs.append("%s: %s not found in lean-causal (a full name)" % (tag, key))

    def known_ids(tag, xs):
        for x in xs:
            if x not in known:
                errs.append("%s: unknown property %r" % (tag, x))

    for kind in ("implies", "fails", "consequence"):
        for e in data.get(kind, []):
            tag = "%s %s" % (kind, e.get("witness", "?"))
            if e.get("status") not in STATUS:
                errs.append("%s: status must be one of %s" % (tag, STATUS))
            lean_ref(tag, "witness", e)
            if kind == "consequence":
                at = ids_of(e.get("at"))
                if at is None:
                    errs.append("%s: at must be an id or a list of ids" % tag)
                    at = []
                elif not at:
                    errs.append("%s: missing at" % tag)
                ends = at
                if not e.get("statement"):
                    errs.append("%s: missing statement" % tag)
                _words(tag, e, "standing", errs)
            else:
                frm = ids_of(e.get("from"))
                if frm is None:
                    errs.append("%s: from must be an id or a list of ids" % tag)
                    frm = []
                elif not frm:
                    errs.append("%s: empty premise" % tag)
                ends = frm + [e.get("to")]
                _words(tag, e, "standing" if kind == "implies" else "space", errs)
            known_ids(tag, ends)
            if len(set(ends)) < len(ends):
                errs.append("%s: an id is repeated" % tag)
            _one_sort(tag, ends, sort, errs)
    for f in data.get("fact", []):
        tag = "fact %s" % f.get("property")
        if f.get("status") not in STATUS:
            errs.append("%s: status must be one of %s" % (tag, STATUS))
        lean_ref(tag, "witness", f)
        if not isinstance(f.get("property"), str):
            errs.append("%s: property must be one id" % tag)
        else:
            known_ids(tag, [f["property"]])
        _words(tag, f, "standing", errs)
    for o in data.get("open", []):
        tag = "open %s→%s" % (o.get("from"), o.get("to"))
        ends = [o.get("from"), o.get("to")]
        known_ids(tag, ends)
        _one_sort(tag, ends, sort, errs)
    for t in data.get("transfer", []):
        tag = "transfer %s of %s along %s" % (t.get("direction", "to_narrower"), t.get("property"), t.get("pair"))
        if t.get("status") not in STATUS:
            errs.append("%s: status must be one of %s" % (tag, STATUS))
        if t.get("direction", "to_narrower") not in DIRECTIONS:
            errs.append("%s: direction must be one of %s" % (tag, DIRECTIONS))
        for key, want in (("pair", "pair"), ("property", "causality")):
            x = t.get(key)
            if not isinstance(x, str) or x not in known:
                errs.append("%s: %s %r is not a property" % (tag, key, x))
            elif sort[x] != want:
                errs.append("%s: %s %s is of sort %s, not %s" % (tag, key, x, sort[x], want))
        for key in ("narrower", "wider"):
            xs = ids_of(t.get(key))
            if xs is None:
                errs.append("%s: %s must be a list of ids" % (tag, key))
                continue
            known_ids(tag, xs)
            for x in xs:
                if x in known and sort[x] != "causality":
                    errs.append("%s: %s id %s is of sort %s, not causality" % (tag, key, x, sort[x]))
        has_w, has_c = bool(t.get("witness")), bool(t.get("counterexample"))
        if has_w == has_c:
            errs.append("%s: exactly one of witness (the transfer) and counterexample" % tag)
        lean_ref(tag, "witness", t, required=False)
        lean_ref(tag, "counterexample", t, required=False)
        if has_c and "standing" in t:
            errs.append("%s: standing is a witness's field; a counterexample's space is `space`" % tag)
        if has_w and "space" in t:
            errs.append("%s: space is a counterexample's field; a witness's hypotheses are `standing`" % tag)
        _words(tag, t, "standing", errs)
        _words(tag, t, "space", errs)
        if has_w and t.get("property") in (_transfer_sides(t)[1]):
            errs.append("%s: asks %s of the causality it concludes it for (vacuous)" % (tag, t.get("property")))
    if not errs:
        errs += _contradictions(data)
    if not errs and has_dual_keys(data):
        errs += dual_contradictions(data, index)
    return errs


def _contradictions(data):
    """The semantic violations, on a ladder whose schema is sound."""
    errs, cache = [], {}
    for f in data.get("fails", []):
        has, lacks = counterexample(data, f, cache)
        if f["to"] in has:
            errs.append("contradiction: counterexample %s has %s, hence %s by the implications (and facts) valid "
                        "on its space (%s), and lacks it" % (f.get("witness"), " ∧ ".join(ids_of(f["from"])), f["to"],
                                                       ", ".join(sorted(space(f, data)))))
        elif has & lacks:
            errs.append("contradiction: counterexample %s has and lacks %s on its space (%s)" % (
                f.get("witness"), ", ".join(sorted(has & lacks)), ", ".join(sorted(space(f, data)))))
    clo, bad = closure(data), refuted(data)
    for o in data.get("open", []):
        a, b = o["from"], o["to"]
        if b in clo[a] or (a, b) in bad:
            errs.append("open %s→%s is already settled; remove it" % (a, b))
    # a transfer proved under a condition in words (`under`) is conditional: a counterexample need not
    # meet the condition, so the check does not apply it (T-tool-ladder-py-2)
    proved = [t for t in data.get("transfer", []) if t.get("witness") and not t.get("under")]
    for c in (t for t in data.get("transfer", []) if t.get("counterexample")):
        on = space(c, data)
        edges = edges_on(data, on)
        src, tgt = _transfer_sides(c)
        has_src = _saturate(set(src) | {c["property"]}, edges)
        has_tgt = _saturate(tgt, edges)
        if c["property"] in has_tgt:
            errs.append("contradiction: transfer counterexample %s: its target has %s, hence %s, which it "
                        "lacks" % (c["counterexample"], " ∧ ".join(tgt), c["property"]))
            continue
        pairs = _saturate({c["pair"]}, edges)
        for w in proved:
            wsrc, wtgt = _transfer_sides(w)
            if (w["property"] == c["property"] and w.get("direction", "to_narrower") == c.get("direction", "to_narrower")
                    and w["pair"] in pairs and set(standing(w)) <= on
                    and set(wsrc) <= has_src and set(wtgt) <= has_tgt):
                errs.append("contradiction: transfer %s (%s of %s along %s) applies to counterexample %s" % (
                    w["witness"], w.get("direction", "to_narrower"), w["property"], w["pair"], c["counterexample"]))
    return errs


def matrix(data):
    """(a, b) -> ill-typed | implied | fails | open | fails-off | implied-standing | unknown, every a != b."""
    sort = sort_of(data)
    clo, every, bad, off = closure(data), closure_any(data), refuted(data), refuted(data, off=True)
    opens = {(o.get("from"), o.get("to")) for o in data.get("open", [])}
    ids = [p["id"] for p in data.get("property", [])]
    out = {}
    for a in ids:
        for b in ids:
            if a == b:
                continue
            out[(a, b)] = ("ill-typed" if sort[a] != sort[b] else "implied" if b in clo[a]
                           else "fails" if (a, b) in bad else "open" if (a, b) in opens
                           else "fails-off" if (a, b) in off
                           else "implied-standing" if b in every[a] else "unknown")
    return out


def off_spaces(data, a, b):
    """The spaces (sorted word lists) of the counterexamples off the ambient refuting (a, b)."""
    out, cache = set(), {}
    for f in data.get("fails", []):
        if not on_ambient(f, data):
            has, lacks = counterexample(data, f, cache)
            if a in has and b in lacks:
                out.add(tuple(sorted(f.get("space", []))))
    return sorted(out)


def fact_edges(data, a):
    """The [[fact]]s of a's sort as premise-free steps from a, with their own standing: what
    needed_standing must count besides the edges for a pair implied under standing (T-tool-ladder-py-2;
    emit-lean reads the facts it emits through _fact_edge instead)."""
    sort = sort_of(data)
    return [{"from": [a], "to": f.get("property"), "standing": standing(f)} for f in data.get("fact", [])
            if sort.get(f.get("property")) is not None and sort.get(f.get("property")) == sort.get(a)]


def needed_standing(src, b, edges, base=()):
    """An irredundant set of standing words (beyond the closed set `base`) with which `edges` chain
    `b` from `src`: every word of the edges, then each dropped in turn while `b` stays reached, the
    strongest first (a word implying more is tried first), so that T1 is kept rather than T2."""
    words = set().union(*(set(standing(e)) for e in edges)) if edges else set()
    words -= set(base)
    for w in sorted(words, key=lambda x: (-len(vocab_closure([x])), x)):
        on = vocab_closure((words - {w}) | set(base))
        if b in _saturate(src, [e for e in edges if valid(e, on)]):
            words.discard(w)
    return sorted(words)


def summary(data, errs=()):
    m = matrix(data) if not errs else {}
    within = [v for v in m.values() if v != "ill-typed"]
    return {"properties": len(data.get("property", [])), "implies": len(data.get("implies", [])),
            "fails": len(data.get("fails", [])), "consequences": len(data.get("consequence", [])),
            "transfers": len(data.get("transfer", [])), "violations": len(errs), "pairs": len(m),
            "within": len(within), "ill_typed": len(m) - len(within),
            "classified": sum(1 for v in within if v in CLASSIFIED),
            "implied_standing": sum(1 for v in within if v == "implied-standing"),
            "fails_off": sum(1 for v in within if v == "fails-off")}


def check_line(s):
    head = "ladder: %d properties, %d implications, %d counterexamples, %d consequences; " % (
        s["properties"], s["implies"], s["fails"], s["consequences"])
    if s["violations"]:
        return head + "%d violation(s)" % s["violations"]
    return head + ("%d of %d ordered pairs classified (within one sort), %d ill-typed (across sorts), "
                   "%d implied under standing only, %d refuted off the ambient only, %d transfers" % (
                       s["classified"], s["within"], s["ill_typed"], s["implied_standing"], s["fails_off"],
                       s["transfers"]))


# ------------------------------------------------------------------ emit-lean
#
# `emit-lean` writes two generated modules of the strict library:
#   Causal/Ladder/Rules.lean  one aesop rule `safe forward` of the rule set CausalLadder per emitted
#                             edge, and the imports of the witnesses' modules;
#   Causal/Ladder/Test.lean   `example`s: `causal_ladder` derives every pair of the closure of the
#                             EMITTED edges, and fails on every other ordered pair.
# An edge is emitted when it is `checked`, has a premise, carries no `under` (a side condition in
# words is not a ladder node, and a rule with an unprovable side goal must not exist), joins
# properties of the sort `causality` only (a `geometry` or `pair` property is not a predicate on one
# causality), its `standing` words are in the vocabulary, its witness is declared in a module of the
# ETT layer (one that imports, directly or transitively, no model: MODEL_LAYER, so that the layer-1
# modules which call `causal_ladder` stay model-free), and each of its properties has a Lean form
# (lean_form: a Prop-valued def of the ETT layer on one causality; a rule about a formless property
# could never be tested, and was inert when the property's def imported a model).
# `standing` does not stop an edge: every vocabulary word is a Mathlib class on M, which the witness
# takes as an instance argument, and aesop's forward rules synthesise instance arguments and do not
# fire when synthesis fails (Aesop/RuleTac/Forward.lean, makeForwardHypProofs): no side goal is left.
# Test.lean derives a pair reached through such a rule with exactly the instances its derivation
# needs (needed_standing) and checks, in the bare context, that it is not derived without them; so
# a `standing` that misses an instance the witness needs, or is declared on a witness that takes
# none, makes Test.lean fail to build (a stronger or an extra class is not detected: it only narrows
# where the rule is tested). Checked 2026-11-21 (T-tool-ladder-py) by compiling, with `lake env
# lean` on one file outside the tree, the rules and tests emitted for programme/ladder.toml with its
# four separation/countability `under`s moved to `standing`, and three mutants of that file.
# A skipped checked edge is a comment line in Rules.lean that names it and says why.
#
# Since T-tac-ladder-integration (2026-11-22):
# * Rules.lean imports Causal.Ladder.Dual (the hand-written time-reversal rules) when that module
#   exists and does not import Rules (dual_import); every causal_ladder user then reasons across
#   C.dual.
# * An edge whose witness's module imports Causal.Ladder.Rules is skipped (`cycle`): Rules.lean
#   cannot import it. None does today.
# * A checked [[fact]] of the sort causality is a rule (emitted_facts) when its standing words are
#   in the vocabulary, its witness is found in an ETT-layer module, its property has a Lean form,
#   and its witness is a theorem whose one explicit binder is the causality (fact_binder, read off
#   `tsigs`). The rule is `safe apply` (it closes `P t` for any causality term t; aesop synthesises
#   the standing instances, and the rule fails, leaving no goal, where synthesis fails), plus
#   `safe forward` with the rule pattern of that binder when the property is a premise of an
#   emitted edge (the fact must then feed the saturation; the pattern makes it hold of every
#   causality term in sight, fvar, constant or C.dual, and writes no new term). Apply only, when
#   nothing reads the fact: measured on Test.lean with the fact curves_extend, the forward form
#   costs +12 s (a failing synthesis of T1Space M and SecondCountableTopology M, 8 ms each, at
#   every goal of every search with a causality in sight), the apply form +0.6 s.
# * A fact passing every check but whose witness's module imports Causal.Ladder.Rules (curves_extend
#   was one until T-tac-curves-fact-rule split Causal.AbstractDev out of MaximalZorn) is a skipped line in
#   Rules.lean and is registered LOCALLY in a last section of Test.lean, which tests the rule there
#   (the fact with exactly its standing, from ⊤ and from each property; not without it; not with any
#   one word dropped; of C.dual) and shows, outside that section, that the shipped tactic lacks it.
# * Test.lean: a rule with two standing words or more is not derived from its premises with any one
#   word dropped (word_drops), so a word the witness does not need turns Test.lean red too.

TEST = os.path.join(LEAN_ROOT, "Causal", "Ladder", "Test.lean")
RULES_MODULE = "Causal.Ladder.Rules"
DUAL_MODULE = "Causal.Ladder.Dual"
GENERATED = "-- generated by tools/ladder.py emit-lean from programme/ladder.toml: do not edit"
MODEL_LAYER = ("Causal.Minkowski", "Causal.Static", "Causal.SingularFlat",
               "Causal.Flat", "Causal.Model", "Causal.Port")
DECL_FQ = re.compile(r"(?:(?:private|protected|noncomputable|public|partial|unsafe|nonrec)\s+)*"
                     r"(theorem|lemma|def|abbrev|structure|class|instance|inductive|opaque|axiom)"
                     r"\s+([^\s(:{\[⦃]+)")
IMPORT = re.compile(r"(?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?([\w.']+)\s*$")


_COMMENT = re.compile(r"/-|-/|--")
_NOT_NL = re.compile(r"[^\n]")


def _code(text):
    """`text` with its comments (`--`, nested `/- -/`, docstrings) blanked, newlines kept. Scans
    from one comment token to the next (a token is read where it applies, as a character otherwise)."""
    out, i, depth, n = [], 0, 0, len(text)
    while i < n:
        m = _COMMENT.search(text, i)
        j = m.start() if m else n
        out.append(_NOT_NL.sub(" ", text[i:j]) if depth else text[i:j])
        if m is None:
            break
        tok = m.group()
        if tok == "/-":
            depth += 1
            out.append("  ")
            i = j + 2
        elif tok == "-/" and depth:
            depth -= 1
            out.append("  ")
            i = j + 2
        elif tok == "--" and not depth:
            k = text.find("\n", j)
            k = n if k == -1 else k
            out.append(" " * (k - j))
            i = k
        else:
            out.append(" " if depth and text[j] != "\n" else text[j])
            i = j + 1
    return "".join(out)


def _signature(code, pos):
    """The explicit binders and the type of the declaration whose name ends at `pos`:
    ([binder text, ...], type text or None). Read up to the first top-level `:=` or `where`."""
    close = {"(": ")", "[": "]", "{": "}", "⦃": "⦄"}
    explicit, stack, start, i = [], [], None, pos
    end = min(len(code), pos + 4000)
    while i < end:
        c = code[i]
        if c in close:
            if not stack and c == "(":
                start = i + 1
            stack.append(close[c])
        elif stack and c == stack[-1]:
            stack.pop()
            if not stack and start is not None:
                explicit.append(" ".join(code[start:i].split()))
                start = None
        elif not stack and c == ":" and not code.startswith(":=", i):
            rest = code[i + 1:end]
            m = re.search(r":=|\bwhere\b|^\s*\|", rest, re.M)
            return explicit, " ".join((rest[:m.start()] if m else rest).split())
        elif not stack and (code.startswith(":=", i) or (
                code.startswith("where", i) and not re.match(r"[\w.']", code[i - 1])
                and not re.match(r"[\w']", code[i + 5:i + 6]))):
            return explicit, None
        i += 1
    return explicit, None


_INDEX = {}


def lean_index(root=LEAN_ROOT):
    """Memoised _lean_index, keyed on the root and every source's size and mtime."""
    files = sorted(glob.glob(os.path.join(root, "Causal", "**", "*.lean"), recursive=True))
    key = (os.path.abspath(root), tuple((f, os.stat(f).st_mtime_ns, os.stat(f).st_size) for f in files))
    if key not in _INDEX:
        _INDEX.clear()
        _INDEX[key] = _lean_index(root)
    return _INDEX[key]


def _lean_index(root=LEAN_ROOT):
    """What emit-lean reads off the Causal library's sources, without Lean:
    `decls`   fully qualified name -> module, for every declaration (namespaces tracked);
    `imports` module -> the Causal modules its header imports;
    `sigs`    fully qualified name -> (explicit binders, type), for every `def` and `abbrev`;
    `tsigs`   the same for every `theorem` and `lemma` (what a [[fact]]'s witness is stated for);
    `generated` the modules whose first line is emit-lean's GENERATED line (T-tac-ladder-dual-key: a
              hand-written Causal/Ladder/Dual.lean is never overwritten)."""
    decls, imports, sigs, tsigs, generated = {}, {}, {}, {}, set()
    for f in sorted(glob.glob(os.path.join(root, "Causal", "**", "*.lean"), recursive=True)):
        mod = os.path.relpath(f, root)[:-len(".lean")].replace(os.sep, ".")
        with open(f, encoding="utf-8") as fh:
            raw = fh.read()
        if raw.split("\n", 1)[0] == GENERATED:
            generated.add(mod)
        code = _code(raw)
        imports[mod] = []
        stack = []          # one entry per namespace component or section: (kind, component)
        header = True
        offset = 0
        for line in code.split("\n"):
            here, offset = offset, offset + len(line) + 1
            s = line.strip()
            if not s:
                continue
            if header:
                if s in ("module", "prelude"):
                    continue
                m = IMPORT.match(s)
                if m:
                    if m.group(1).startswith("Causal."):
                        imports[mod].append(m.group(1))
                    continue
                header = False
            m = re.match(r"namespace\s+(\S+)", s)
            if m:
                stack.extend(("namespace", x) for x in m.group(1).split("."))
                continue
            m = re.match(r"(?:@\[.*\]\s*)?(?:(?:public|private|noncomputable)\s+)*section\b\s*(\S*)", s)
            if m:
                stack.extend(("section", x) for x in (m.group(1).split(".") if m.group(1) else [""]))
                continue
            m = re.match(r"end\b\s*(\S*)", s)
            if m:
                for _ in (m.group(1).split(".") if m.group(1) else [""]):
                    if stack:
                        stack.pop()
                continue
            while s.startswith("@["):                  # attributes, brackets balanced
                d, k = 0, 1
                for k in range(1, len(s)):
                    d += s[k] == "["
                    d -= s[k] == "]"
                    if d == 0:
                        break
                s = s[k + 1:].lstrip()
            m = DECL_FQ.match(s)
            if not m:
                continue
            name = m.group(2)
            if name.startswith("_root_."):
                full = name[len("_root_."):]
            else:
                full = ".".join([x for k, x in stack if k == "namespace"] + [name])
            decls.setdefault(full, mod)
            if m.group(1) in ("def", "abbrev", "theorem", "lemma"):
                at = here + (len(line) - len(line.lstrip())) + (len(line.strip()) - len(s)) + m.end()
                (sigs if m.group(1) in ("def", "abbrev") else tsigs).setdefault(full, _signature(code, at))
    return {"decls": decls, "imports": imports, "sigs": sigs, "tsigs": tsigs, "generated": generated}


def is_model(mod):
    """A module of the model layer (MODEL_LAYER): one of them, or below one of them."""
    return any(mod == m or mod.startswith(m + ".") for m in MODEL_LAYER)


def model_path(mod, imports):
    """The shortest import chain from `mod` to a model module, or None if `mod` is ETT-layer."""
    seen, queue = {mod: None}, [mod]
    while queue:
        m = queue.pop(0)
        if is_model(m):
            path = [m]
            while seen[path[-1]] is not None:
                path.append(seen[path[-1]])
            return path[::-1]
        for n in imports.get(m, []):
            if n not in seen:
                seen[n] = m
                queue.append(n)
    return None


def import_chain(mod, imports, target):
    """The shortest import chain from `mod` to the module `target` (`[target]` when `mod` is it),
    or None when `mod` does not import it, directly or transitively."""
    seen, queue = {mod: None}, [mod]
    while queue:
        m = queue.pop(0)
        if m == target:
            path = [m]
            while seen[path[-1]] is not None:
                path.append(seen[path[-1]])
            return path[::-1]
        for n in imports.get(m, []):
            if n not in seen:
                seen[n] = m
                queue.append(n)
    return None


def lean_form(prop, index, term="C"):
    """`P C` for a property of one causality `C : Causal.Causality M`, or (None, why); with `term`,
    the same property of that causality (`C.dual`)."""
    name = prop.get("lean", "")
    if prop.get("sort", "causality") != "causality":
        return None, "sort %s" % prop["sort"]
    mod = index["decls"].get(name)
    if mod is None or name not in index["sigs"]:
        return None, "no def or abbrev %s in lean-causal/Causal" % name
    if model_path(mod, index["imports"]):
        return None, "%s lives in %s, which imports a model" % (name, mod)
    explicit, typ = index["sigs"][name]
    if typ != "Prop":
        return None, "%s is not a Prop-valued def (type %s)" % (name, typ)
    ns = name.rsplit(".", 1)[0]
    subject = {"Causal.Causality": term, "Causal.Precausality": term + ".toPrecausality"}
    if not explicit and ns in subject:
        return "%s %s" % (name, subject[ns]), None
    if len(explicit) == 1:
        m = re.match(r"[^:]*:\s*(?:Causal\.)?(Causality|Precausality)\b", explicit[0])
        if m:
            return "%s %s" % (name, subject["Causal." + m.group(1)]), None
    return None, "%s is not a predicate on one causality (explicit binders %s)" % (name, explicit)


def emitted(data, index=None):
    """(edges emitted as rules, with the witness's module; checked edges skipped, with the reason)."""
    index = lean_index() if index is None else index
    sort = sort_of(data)
    props = {p.get("id"): p for p in data.get("property", [])}
    forms = {}

    def form(x):
        if x not in forms:
            forms[x] = lean_form(props[x], index) if x in props else (None, "not a property of the ladder")
        return forms[x]
    rules, skipped = [], []
    for e in data.get("implies", []):
        if e.get("status") != "checked":
            continue
        w = e.get("witness", "?")
        mod = index["decls"].get(w)
        chain = model_path(mod, index["imports"]) if mod else None
        cycle = import_chain(mod, index["imports"], RULES_MODULE) if mod else None
        ends = (ids_of(e.get("from")) or []) + [e.get("to")]
        raw = e.get("standing", [])
        unknown = [str(x) for x in raw if x not in STANDING] if isinstance(raw, list) else ["%r (not a list)" % (raw,)]
        formless = [(x, form(x)[1]) for x in ends if not form(x)[0]]
        if not e.get("from"):
            skipped.append((e, "no premise"))
        elif e.get("under"):
            skipped.append((e, "under: %s" % " ".join(e["under"].split())))
        elif any(sort.get(x, DEFAULT_SORT) != DEFAULT_SORT for x in ends):
            skipped.append((e, "sort: joins a property not of the sort causality"))
        elif unknown:
            skipped.append((e, "standing: %s not in the vocabulary" % ", ".join(unknown)))
        elif mod is None:
            skipped.append((e, "not found: no declaration of this name in lean-causal/Causal"))
        elif chain:
            skipped.append((e, "layer: %s lives in %s, which imports a model (%s)" % (
                w, mod, " → ".join(chain))))
        elif cycle:
            skipped.append((e, _cycle(w, mod, cycle)))
        elif formless:
            skipped.append((e, "no Lean form: %s" % "; ".join("%s (%s)" % xw for xw in formless)))
        else:
            rules.append((e, mod))
    return rules, skipped


def _cycle(w, mod, chain):
    return "cycle: %s lives in %s, which imports %s (%s)" % (w, mod, RULES_MODULE, " → ".join(chain))


FACT_BINDER = re.compile(r"([^\s:]+)\s*:\s*(?:Causal\.)?(?:Causality|Precausality)\s+[^\s:]+$")


def fact_binder(witness, index):
    """(the name of the causality a [[fact]]'s witness is stated for, None), or (None, why): the
    witness is a theorem whose one explicit binder is `(C : Causality M)` (or a Precausality);
    its instance arguments are the fact's standing, which the rule synthesises."""
    sig = index.get("tsigs", {}).get(witness)
    if sig is None:
        return None, "%s is not a theorem of lean-causal/Causal" % witness
    explicit = sig[0]
    m = FACT_BINDER.match(explicit[0]) if len(explicit) == 1 else None
    if m is None:
        return None, "%s does not take exactly one explicit causality (explicit binders %s)" % (
            witness, explicit or "none")
    return m.group(1), None


def emitted_facts(data, index=None, rules=None):
    """The checked [[fact]]s as CausalLadder rules: (in_rules, in_test_only, skipped).

    in_rules      (fact, module, binder, forward): a rule of Rules.lean. `forward` when the fact's
                  property is a premise of an emitted edge (the rule must then also feed the
                  saturation, not only close a goal).
    in_test_only  (fact, module, binder, forward, chain): every check passed, but the witness's module
                  imports Causal.Ladder.Rules (the chain), so Rules.lean cannot import it: Test.lean
                  registers the rule locally, to test it, and the tactic does not have it.
    skipped       (fact, why): sort, standing, not found, layer, no Lean form, witness shape.
    Seed facts are ignored, as seed edges are."""
    index = lean_index() if index is None else index
    rules = emitted(data, index)[0] if rules is None else rules
    sort, props = sort_of(data), {p.get("id"): p for p in data.get("property", [])}
    premises = {x for e, _ in rules for x in ids_of(e["from"])}
    in_rules, in_test, skipped = [], [], []
    for f in data.get("fact", []):
        if f.get("status") != "checked":
            continue
        p, w = f.get("property"), f.get("witness", "?")
        mod = index["decls"].get(w)
        raw = f.get("standing", [])
        unknown = [str(x) for x in raw if x not in STANDING] if isinstance(raw, list) else ["%r (not a list)" % (raw,)]
        chain = model_path(mod, index["imports"]) if mod else None
        if p not in props:
            skipped.append((f, "not a property of the ladder"))
        elif sort.get(p) != DEFAULT_SORT:
            skipped.append((f, "sort: %s is not of the sort causality" % p))
        elif unknown:
            skipped.append((f, "standing: %s not in the vocabulary" % ", ".join(unknown)))
        elif mod is None:
            skipped.append((f, "not found: no declaration of this name in lean-causal/Causal"))
        elif chain:
            skipped.append((f, "layer: %s lives in %s, which imports a model (%s)" % (w, mod, " → ".join(chain))))
        else:
            form, why = lean_form(props[p], index)
            binder, bwhy = fact_binder(w, index)
            if not form:
                skipped.append((f, "no Lean form: %s (%s)" % (p, why)))
            elif not binder:
                skipped.append((f, "shape: %s" % bwhy))
            else:
                cycle = import_chain(mod, index["imports"], RULES_MODULE)
                item = (f, mod, binder, p in premises)
                if cycle:
                    in_test.append(item + (cycle,))
                else:
                    in_rules.append(item)
    return in_rules, in_test, skipped


def dual_import(index):
    """(import Causal.Ladder.Dual into Rules.lean?, why not): only when the module exists and does
    not itself import Causal.Ladder.Rules (which would be a cycle)."""
    if DUAL_MODULE not in index["imports"]:
        return False, None
    chain = import_chain(DUAL_MODULE, index["imports"], RULES_MODULE)
    if chain:
        return False, "not imported: %s imports %s (%s)" % (DUAL_MODULE, RULES_MODULE, " → ".join(chain))
    return True, None


def _fact_lines(f, binder, forward, local=False):
    """The attribute lines of a [[fact]]'s rule: `safe apply` (closes a goal `P t`, for any causality
    term t, its standing synthesised: never a side goal), and `safe forward` with the rule pattern
    `binder` when the fact feeds an edge (it then holds of every causality term in sight)."""
    kw = "local aesop" if local else "aesop"
    out = ["attribute [%s safe apply (rule_sets := [CausalLadder])] %s" % (kw, f["witness"])]
    if forward:
        out.append("attribute [%s safe forward (pattern := %s) (rule_sets := [CausalLadder])] %s" % (
            kw, binder, f["witness"]))
    return out


def _fact_edge(f):
    """A fact as a premise-free edge with its standing (what _saturate and needed_standing read)."""
    return {"from": [], "to": f["property"], "standing": standing(f), "witness": f["witness"]}


def _edge(e):
    return "%s ⇒ %s" % (" ∧ ".join(ids_of(e["from"])), e["to"])


def _std(words):
    return " (standing: %s)" % ", ".join(words) if words else ""


def instances(words):
    """The instance binders of the standing `words`, on the space M of Causal.Ladder.Test."""
    return " ".join("[%s M]" % STANDING[w][0] for w in words)


def emit_lean(data, index=None):
    """The text of Causal/Ladder/Rules.lean."""
    index = lean_index() if index is None else index
    rules, skipped = emitted(data, index)
    facts, local, fskipped = emitted_facts(data, index, rules)
    gen = dual_generated(data, index)
    dual, dual_why = (True, None) if gen else dual_import(index)
    mods = sorted({m for _, m in rules} | {x[1] for x in facts})
    lines = ([GENERATED, "import Causal.Ladder.Basic"] + (["import " + DUAL_MODULE] if dual else []) +
             ["import %s" % m for m in mods if m != DUAL_MODULE] + [
        "",
        "/-!",
        "# The rules of `causal_ladder`, generated from the causality ladder",
        "",
        "One aesop `safe forward` rule of the rule set `CausalLadder` per `checked` implication of",
        "`programme/ladder.toml` with no side condition in words (`under`), between properties of the",
        "sort `causality` that each have a Lean form (a predicate on one causality, as",
        "`Causal.Ladder.Test` writes it), whose witness lives in the ETT layer (no model imported,",
        "directly or transitively) in a module that does not import this one. An implication with",
        "`standing` hypotheses (separation, countability, connectedness of `M`: Mathlib classes its",
        "witness takes as instance arguments) is a rule too: aesop synthesises those arguments, and the",
        "rule does not fire where they are not in context.",
        ""] + ([
        "A `checked` [[fact]] of the sort `causality` (a property every causality has, on the spaces of",
        "its `standing`), whose witness is a theorem of the ETT layer taking the causality as its one",
        "explicit argument, is a `safe apply` rule: it closes a goal `P t` for any causality term `t`",
        "once aesop synthesises its standing instances, and fails, leaving no goal, where it cannot.",
        "When the fact's property is a premise of an implication above, it is also a `safe forward`",
        "rule with the rule pattern of its causality (it holds of every causality term in sight, so the",
        "implications can use it). A fact whose witness's module imports this module cannot be a rule",
        "here (an import cycle): `Causal.Ladder.Test` registers it locally, to test the rule.",
        ""] if facts or local else []) + (([
        "This module imports `Causal.Ladder.Dual`, the time-reversal rules of the same rule set, generated",
        "with it from the ladder's `dual` keys, so every user of `causal_ladder` reasons across `C.dual`.",
        ] if gen else [
        "This module imports `Causal.Ladder.Dual`, the hand-written time-reversal rules of the same rule",
        "set, so every user of `causal_ladder` reasons across `C.dual` (T-tac-ladder-dual).",
        ]) if dual else []) + [
        "Every other checked implication or fact is a `-- skipped` line below, with its reason.",
        "Regenerate with `python3 tools/ladder.py emit-lean`; `Causal.Ladder.Test` is generated with it.",
        "",
        "Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.",
        "-/",
        ""])
    if dual_why:
        lines += ["-- %s" % dual_why, ""]
    for e, _ in rules:
        lines.append("-- %s%s" % (_edge(e), _std(standing(e))))
        lines.append("attribute [aesop safe forward (rule_sets := [CausalLadder])] %s" % e["witness"])
    for f, _, binder, forward in facts:
        lines.append("-- fact: %s%s%s" % (f["property"], _std(standing(f)),
                                          ", a premise above: also forward" if forward else ""))
        lines += _fact_lines(f, binder, forward)
    if skipped or local or fskipped:
        lines.append("")
    for e, why in skipped:
        lines.append("-- skipped %s (%s): %s" % (e.get("witness", "?"), _edge(e) if e.get("from") else "?", why))
    for f, mod, _, _, chain in local:
        lines.append("-- skipped fact %s (%s): %s; Causal.Ladder.Test registers it locally" % (
            f["witness"], f["property"], _cycle(f["witness"], mod, chain)))
    for f, why in fskipped:
        lines.append("-- skipped fact %s (%s): %s" % (f.get("witness", "?"), f.get("property", "?"), why))
    return "\n".join(lines) + "\n"


def _src(src):
    return " ∧ ".join(src) if src else "⊤"


def emit_test(data, index=None):
    """The text of Causal/Ladder/Test.lean: the closure of the emitted edges and facts, both ways. A
    pair reached only through a rule with `standing` is derived with the instances it needs and is
    not derived without them; a rule with two standing words or more is not derived with any one of
    them dropped. The facts Rules.lean cannot import (a cycle) are registered locally in a last
    section, tested there the same way, and shown not derived by the shipped tactic."""
    index = lean_index() if index is None else index
    rules, _ = emitted(data, index)
    facts, local, _ = emitted_facts(data, index, rules)
    edges = [e for e, _ in rules] + [_fact_edge(x[0]) for x in facts]
    ledges = [_fact_edge(x[0]) for x in local]
    bare = [e for e in edges if not standing(e)]
    props = [p for p in data.get("property", []) if p.get("sort", DEFAULT_SORT) == DEFAULT_SORT]
    pmap = {p["id"]: p for p in props}
    form, why = {}, {}
    for p in props:
        f, w = lean_form(p, index)
        if f:
            form[p["id"]] = f
        else:
            why[p["id"]] = w
    ids = [p["id"] for p in props if p["id"] in form]
    mat = matrix(data)
    mods = sorted({index["decls"][p["lean"]] for p in props if p["id"] in form} | {x[1] for x in local})
    fact_ids = {f.get("property") for f in data.get("fact", [])}
    local_ids = {x[0]["property"] for x in local}
    note = {"implied": "the matrix chains it through an edge not emitted",
            "fails": "refuted by a counterexample", "open": "an open pair", "unknown": "unknown",
            "implied-standing": "implied under standing hypotheses beyond the ambient, through an edge not emitted",
            "fails-off": "refuted only by a counterexample off the ambient"}

    def word_drops(rs, scope, seen, neg):
        """A rule (edge or fact) of `rs` with two standing words or more, from its own premises, is
        not derived with any one word dropped (the others kept): each word is needed."""
        for r in rs:
            src, words = tuple(ids_of(r["from"])), standing(r)
            if len(words) < 2 or not all(x in form for x in src) or r["to"] not in form:
                continue
            for w in words:
                keep = [x for x in words if x != w]
                on = vocab_closure(keep)
                key = (src, r["to"], tuple(keep))
                if r["to"] not in _saturate(src, [e for e in scope if valid(e, on)]) and key not in seen:
                    seen.add(key)
                    neg.append((src, r["to"], keep, "standing dropped: %s, of %s" % (w, r["witness"])))

    pos, neg, drop, seen = [], [], [], set()
    sources = [(a,) for a in ids] + [tuple(ids_of(e["from"])) for e in edges if len(ids_of(e["from"])) > 1]
    if facts:
        sources.append(())
    for src in sources:
        if src in seen or not all(x in form for x in src):
            continue
        seen.add(src)
        reach0 = _saturate(src, bare)
        for b in sorted(_saturate(src, edges) - set(src)):
            if b in form:
                words = [] if b in reach0 else needed_standing(src, b, edges)
                pos.append((src, b, words))
                if words:                # derived with its instances: not without them
                    drop.append((src, b, words))
    seen = set()                         # (premises, conclusion, instances) of the examples written
    for a in ids:
        reach = _saturate((a,), edges)
        for b in ids:
            if b != a and b not in reach:
                seen.add(((a,), b, ()))
                cls = mat.get((a, b))
                if cls == "implied" and b in local_ids:
                    why_neg = ("implied through a [[fact]] whose rule is not in %s (a cycle; registered "
                               "locally below)" % RULES_MODULE)
                elif cls == "implied" and b in fact_ids:
                    why_neg = "implied through a [[fact]] (no CausalLadder rule)"
                else:
                    why_neg = note.get(cls, cls)
                neg.append(((a,), b, [], "matrix: %s" % why_neg))
    for src, b, words in drop:
        seen.add((src, b, ()))
        neg.append((src, b, [], "standing dropped: %s" % ", ".join(words)))
    word_drops(edges, edges, seen, neg)
    for e in edges:                      # a conjunctive rule needs every premise, its instances given
        frm = ids_of(e["from"])
        if len(frm) > 1 and all(x in form for x in frm) and e["to"] in form:
            for x in frm:
                src = tuple(y for y in frm if y != x)
                key = (src, e["to"], tuple(standing(e)))
                if e["to"] not in _saturate(src, edges) and key not in seen:
                    seen.add(key)
                    neg.append((src, e["to"], standing(e), "%s dropped from %s" % (x, e["witness"])))
    for f, _, _, _, chain in local:      # the shipped tactic does not have a fact Rules cannot import
        if f["property"] in form and f["property"] not in _saturate((), edges):
            neg.append(((), f["property"], standing(f), "a [[fact]] whose rule is not in %s: %s "
                        "imports it" % (RULES_MODULE, chain[0])))
    dual_pos = [((), f["property"], standing(f)) for f, *_ in facts if f["property"] in form]

    lpos, lneg, lseen = [], [], set()    # the section of the facts registered locally
    if local:
        scope = edges + ledges
        for src in [(a,) for a in ids] + [()]:
            for b in sorted(_saturate(src, scope) - _saturate(src, edges) - set(src)):
                if b in form:
                    words = needed_standing(src, b, scope)
                    lpos.append((src, b, words))
                    # without its instances: the fact itself (from ⊤), and what it gives beyond itself
                    if words and (not src or b not in local_ids):
                        lseen.add((src, b, ()))
                        lneg.append((src, b, [], "standing dropped: %s" % ", ".join(words)))
        word_drops(ledges, scope, lseen, lneg)
    ldual = [((), f["property"], standing(f)) for f, *_ in local if f["property"] in form]

    def hyps(words, src):
        return " ".join(([instances(words)] if words else []) +
                        ["(_h%d : %s)" % (i, form[x]) for i, x in enumerate(src)])

    def derived(src, b, words, term=None):
        goal = form[b] if term is None else lean_form(pmap[b], index, term)[0]
        on = "" if term is None else " of %s" % term
        return ["-- %s ⇒ %s%s%s" % (_src(src), b, on, _std(words)),
                ("example %s : %s := by causal_ladder" % (hyps(words, src), goal)).replace("example  :", "example :")]

    def not_derived(src, b, words, reason):
        return ["-- %s ⇏ %s (%s)" % (_src(src), b, reason),
                ("example %s : True := by" % hyps(words, src)).replace("example  :", "example :"),
                "  fail_if_success have : %s := by causal_ladder" % form[b], "  trivial"]

    lines = [GENERATED, "import Causal.Ladder.Rules"] + ["import %s" % m for m in mods] + [
        "",
        "/-!",
        "# Tests of `causal_ladder`, generated from the causality ladder",
        "",
        "For `C` a causality on a topological space, `causal_ladder` derives every implication of",
        "the transitive closure of the rules of `Causal.Ladder.Rules` (the emitted edges and facts of",
        "`programme/ladder.toml`), from each property, from the premises of each conjunctive rule and,",
        "when a fact is a rule, from nothing (`⊤`), and each fact of `C.dual` too",
        "(%d examples, `Derived`). It fails on every other ordered pair of the properties of the" % (
            len(pos) + len(dual_pos)),
        "sort `causality` written here, and on each conjunctive rule with one premise dropped",
        "(%d examples, `Not derived`). A pair derived only through a rule with `standing` hypotheses" % len(neg),
        "is derived with exactly the instances its derivation needs among its binders, and is not",
        "derived without them (`standing dropped`); a rule with two standing words or more is not",
        "derived from its premises with any one of them dropped: so Lean checks each rule's `standing`",
        "against its witness, an instance missing and an instance not needed alike (a class stronger",
        "than needed is not detected). A pair the ladder's matrix calls `implied` that is not derived",
        "goes through an edge or a fact that was not emitted (a side condition `under`, a witness",
        "outside the ETT layer, or one whose module imports `Causal.Ladder.Rules`).",
        "The first command fails if a model module is imported, directly or transitively: the ladder's",
        "Lean stays in the ETT layer, so that layer-1 modules may use it.",
        ] + ([
        "",
        "A fact whose witness's module imports `Causal.Ladder.Rules` cannot be one of its rules (an",
        "import cycle). The last section registers its rule locally, as `Causal.Ladder.Rules` would",
        "carry it, and tests it like the others (%d examples derived, %d not derived): the shipped" % (
            len(lpos) + len(ldual), len(lneg)),
        "tactic does not have it (`Not derived`: the fact with its standing, from `⊤`).",
        ] if local else []) + [
        "Regenerate with `python3 tools/ladder.py emit-lean`.",
        "",
        "Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.",
        "-/",
        "",
        "open Lean in",
        "run_cmd do",
        "  let models : List Name := [%s]" % ", ".join("`" + m for m in MODEL_LAYER),
        "  for m in (← getEnv).header.moduleNames do",
        "    if models.any (·.isPrefixOf m) then",
        "      throwError \"the ladder's Lean imports the model module {m}\"",
        ""]
    for p in props:
        if p["id"] in why:
            lines.append("-- no example for %s: %s" % (p["id"], why[p["id"]]))
    lines += ["", "section", "", "universe u", "",
              "variable {M : Type u} [TopologicalSpace M] (C : Causal.Causality M)", "",
              "/-! ## Derived -/", ""]
    for src, b, words in pos:
        lines += derived(src, b, words)
    for src, b, words in dual_pos:
        lines += derived(src, b, words, "C.dual")
    lines += ["", "/-! ## Not derived -/", ""]
    for src, b, words, reason in neg:
        lines += not_derived(src, b, words, reason)
    if local:
        lines += ["", "/-! ## Facts whose witness's module imports `Causal.Ladder.Rules`, registered here",
                  "", "Their rules, as `Causal.Ladder.Rules` would carry them, local to this section. -/", "",
                  "section", ""]
        for f, mod, binder, forward, chain in local:
            lines.append("-- fact: %s%s (%s)" % (f["property"], _std(standing(f)), " → ".join(chain)))
            lines += _fact_lines(f, binder, forward, local=True)
        lines.append("")
        for src, b, words in lpos:
            lines += derived(src, b, words)
        for src, b, words in ldual:
            lines += derived(src, b, words, "C.dual")
        for src, b, words, reason in lneg:
            lines += not_derived(src, b, words, reason)
        lines += ["", "end"]
    lines += ["", "end"]
    return "\n".join(lines) + "\n"


# ------------------------------------------------------------------ dual keys (T-tac-ladder-dual-key)
#
# The `dual` key of a [[property]] (schema in the module docstring) makes emit-lean write two more
# generated modules, and only when at least one property carries a key:
#   Causal/Ladder/Dual.lean      per two-sided node P, `p_of_dual : P C.dual → P C` (plain forward)
#                                and `p_dual : P C → P C.dual` (forward with the rule pattern
#                                `Causal.Causality.dual C`: it fires only where `C.dual` is in sight,
#                                kb/0224); per one-sided node P introducing Q,
#                                `q_of_future_of_past : P C → P C.dual → Q C` (plain forward); per
#                                pair node R, the same two rules as a two-sided node, both causalities
#                                reversed, the pattern on the first. The stem p is the last component
#                                of the node's `lean` with its first letter lowered
#                                (Causal.Causality.IsCausal: isCausal): the names and the namespace
#                                Causal.LadderDual of the hand-written module of T-tac-ladder-dual;
#   Causal/Ladder/DualTest.lean  examples, from the closure over literals (property, side) of
#                                dual_lits / dual_close (the port of
#                                campaign/T-tac-ladder-dual/dual_closure.py, which read the edges off
#                                Rules.lean; these are read off `emitted`): every single-property pair
#                                across time reversal derived on a bare space, each conjunctive edge
#                                on C.dual with its two-sided premises on C, each introduction, each
#                                pair node both ways; and, not derived, every cross pair a
#                                counterexample of the ladder, or its time reversal, refutes.
# A module on disk whose first line is not GENERATED is never overwritten (_written): the hand-written
# Dual.lean and DualTest.lean of T-tac-ladder-dual stay until T-tac-dual-generated removes them, and
# Rules.lean calls Dual hand-written until then (dual_generated). With no key, emit-lean writes
# exactly what it wrote before the key existed.

DUAL = os.path.join(LEAN_ROOT, "Causal", "Ladder", "Dual.lean")
DUAL_TEST = os.path.join(LEAN_ROOT, "Causal", "Ladder", "DualTest.lean")
DUAL_TEST_MODULE = "Causal.Ladder.DualTest"
DUAL_NAMESPACE = "Causal.LadderDual"
INTRO_KEYS = ("introduces", "lemma")
FORWARD = "attribute [aesop safe forward (rule_sets := [CausalLadder])] "
PATTERN = "attribute [aesop safe forward (pattern := Causal.Causality.dual C) (rule_sets := [CausalLadder])] "
SHAPES = {"iff": "an iff", "imp": "an implication, read at C and at C.dual",
          "builder": "a theorem taking both forms", "def": "the definition of the two-sided node"}
_BRACKETS = {"(": ")", "[": "]", "{": "}", "⦃": "⦄", "⟨": "⟩"}


def has_dual_keys(data):
    """Does a [[property]] of `data` carry a `dual` key?"""
    props = data.get("property")
    return isinstance(props, list) and any(isinstance(p, dict) and "dual" in p for p in props)


def _written(module, index):
    """May emit-lean write `module`: is it absent from the tree, or already generated?"""
    return module not in index["imports"] or module in index.get("generated", ())


def dual_generated(data, index):
    """Does emit-lean write Causal/Ladder/Dual.lean? Only when a `dual` key is present and the module is
    absent or already generated: a hand-written Dual.lean is kept, and Rules.lean calls it so."""
    return has_dual_keys(data) and _written(DUAL_MODULE, index)


def _top_split(text, sep):
    """`text` split at each `sep` outside brackets, the parts stripped."""
    parts, stack, start, i = [], [], 0, 0
    while i < len(text):
        c = text[i]
        if c in _BRACKETS:
            stack.append(_BRACKETS[c])
        elif stack and c == stack[-1]:
            stack.pop()
        elif not stack and text.startswith(sep, i):
            parts.append(text[start:i].strip())
            i += len(sep)
            start = i
            continue
        i += 1
    parts.append(text[start:].strip())
    return parts


def _mentions(text, lean):
    """Does `text` name the definition `lean`: its last component as a whole word, or followed by `On`
    only (its form on an open set, of which the node is the one at ⊤: causally_arc_connected's key
    is dual_causallyArcConnectedOn)? A name the last component merely starts (StronglyCausalOpen for
    StronglyCausal, IsCausalChain for IsCausal) is another definition (T-tac-ladder-dual-key's audit)."""
    return re.search(r"(?<![\w'])%s(?:On)?(?![\w'])" % re.escape(lean.rsplit(".", 1)[-1]), text or "") is not None


def _hyp(binder):
    """The type of the explicit binder `h : T`."""
    return binder.split(":", 1)[1].strip() if ":" in binder else binder


def reversal_shape(sig, lean):
    """('iff' | 'imp', None) for the statement `sig` (explicit binders, type, as lean_index reads them)
    of a time-reversal lemma of the definition `lean`, or (None, why). 'iff': no explicit binder and
    `L ↔ R`, L with a `dual`, R without, both naming `lean`; 'imp': one explicit hypothesis without
    a `dual` and a conclusion with one, both naming `lean` (_mentions). A statement of one of these
    shapes about another definition is refused with its own reason. Lean checks the rest when the
    rules are compiled."""
    explicit, typ = sig[0], sig[1] or ""
    sides = _top_split(typ, "↔")
    shown = "(explicit binders %s; type %s)" % (explicit or "none", typ or "not read")
    if not explicit and len(sides) == 2:
        lhs, rhs = sides
        if "dual" in lhs and "dual" not in rhs:
            if _mentions(lhs, lean) and _mentions(rhs, lean):
                return "iff", None
            return None, ("its statement %s is `C.dual.P ↔ C.P` for a P other than %s (another node's "
                          "lemma?)" % (shown, lean))
    if len(explicit) == 1 and len(sides) == 1:
        hyp = _hyp(explicit[0])
        if "dual" not in hyp and "dual" in typ:
            if _mentions(hyp, lean) and _mentions(typ, lean):
                return "imp", None
            return None, ("its statement %s is `C.P → C.dual.P` for a P other than %s (another node's "
                          "lemma?)" % (shown, lean))
    return None, ("its statement %s is neither `C.dual.P ↔ C.P` nor `C.P → C.dual.P` for P = %s" % (shown, lean))


def intro_shape(lemma, sig, one, two):
    """('iff' | 'builder' | 'def', None) for the lemma `lemma` (statement `sig`, or None) building the
    two-sided definition `two` from the one-sided `one` and its past form, or (None, why). 'iff':
    `C.Q ↔ C.P ∧ C.dual.P`; 'builder': `(hf : C.P) (hp : C.dual.P) : C.Q`; 'def': `lemma` is Q's
    own definition, `C.P ∧ C.dual.P` by definition (Lean checks the unfolding)."""
    if lemma == two:
        return "def", None
    if sig is None:
        return None, "%s is neither a theorem of lean-causal/Causal nor %s's definition" % (lemma, two)
    explicit, typ = sig[0], sig[1] or ""
    sides = _top_split(typ, "↔")
    shown = "(explicit binders %s; type %s)" % (explicit or "none", typ or "not read")
    other = ("its statement %s is `%%s` for a P other than %s or a Q other than %s (another node's "
             "lemma?)" % (shown, one, two))
    if not explicit and len(sides) == 2:
        conj = _top_split(sides[1], "∧")
        if "dual" not in sides[0] and len(conj) == 2 and "dual" not in conj[0] and "dual" in conj[1]:
            if _mentions(sides[0], two) and _mentions(conj[0], one) and _mentions(conj[1], one):
                return "iff", None
            return None, other % "C.Q ↔ C.P ∧ C.dual.P"
    if len(explicit) == 2 and len(sides) == 1:
        a, b = _hyp(explicit[0]), _hyp(explicit[1])
        if "dual" not in a and "dual" in b and "dual" not in typ:
            if _mentions(a, one) and _mentions(b, one) and _mentions(typ, two):
                return "builder", None
            return None, other % "C.P → C.dual.P → C.Q"
    return None, ("its statement %s is none of `C.Q ↔ C.P ∧ C.dual.P` and `C.P → C.dual.P → C.Q` for "
                  "P = %s, Q = %s, nor Q's definition" % (shown, one, two))


def pair_form(prop, index):
    """(f, None): f(c, c2) is `R c c2` (`R c c2 W` when R takes an open set last) for `prop` a
    Prop-valued def of the ETT layer on two causalities; or (None, why)."""
    name = prop.get("lean", "")
    mod = index["decls"].get(name)
    if mod is None or name not in index["sigs"]:
        return None, "no def or abbrev %s in lean-causal/Causal" % name
    if model_path(mod, index["imports"]):
        return None, "%s lives in %s, which imports a model" % (name, mod)
    explicit, typ = index["sigs"][name]
    if typ != "Prop":
        return None, "%s is not a Prop-valued def (type %s)" % (name, typ)
    cs, opens = [], []
    for b in explicit:
        m = re.match(r"([^:]+):\s*(?:Causal\.)?Causality\s+\S+$", b)
        o = re.match(r"(\S+)\s*:\s*(?:TopologicalSpace\.)?Opens\s+\S+$", b)
        if m and not opens:
            cs += m.group(1).split()
        elif o and not opens:
            opens.append(o.group(1))
        else:
            cs = None
            break
    if cs is None or len(cs) != 2:
        return None, ("%s is not a relation between two causalities, perhaps on an open set "
                      "(explicit binders %s)" % (name, explicit))
    w = " W" if opens else ""
    return (lambda c, c2: "%s %s %s%s" % (name, c, c2, w)), None


def _dual_forms(prop, index):
    """((the property of C, of C.dual), None) for a causality- or pair-sort property (a pair: of
    (C, C') and of (C.dual, C'.dual)), or (None, why)."""
    if prop.get("sort", DEFAULT_SORT) == "pair":
        f, why = pair_form(prop, index)
        return ((f("C", "C'"), f("C.dual", "C'.dual")), None) if f else (None, why)
    f0, why = lean_form(prop, index)
    if not f0:
        return None, why
    return (f0, lean_form(prop, index, "C.dual")[0]), None


def _dual_home(name, index, what="lemma"):
    """None when the generated Causal/Ladder/Dual.lean may import the module of `name` (found; ETT
    layer; the module neither is nor imports Causal.Ladder.Rules or Causal.Ladder.Dual), else why."""
    mod = index["decls"].get(name) if isinstance(name, str) else None
    if mod is None:
        return "%s %r not found in lean-causal (a full name)" % (what, name)
    chain = model_path(mod, index["imports"])
    if chain:
        return "%s %s lives in %s, which imports a model (%s)" % (what, name, mod, " → ".join(chain))
    for target in (RULES_MODULE, DUAL_MODULE):
        chain = import_chain(mod, index["imports"], target)
        if chain:
            return "%s %s lives in %s, which %s %s%s: the dual rules cannot import it" % (
                what, name, mod, "is" if len(chain) == 1 else "imports", target,
                "" if len(chain) == 1 else " (%s)" % " → ".join(chain))
    return None


def _stem(lean):
    last = (lean or "").rsplit(".", 1)[-1]
    return last[:1].lower() + last[1:]


def dual_keys(data, index=None):
    """The `dual` keys read against the Lean index: (reversals, introductions, faults).

    reversals      a dict per two-sided node (sort causality or pair): id, sort, lemma, shape ('iff'
                   or 'imp'), mods (the modules to import), forms (the property of C, of C.dual),
                   name (the stem of its two rules);
    introductions  a dict per one-sided node: id, target (the two-sided id), lemma, shape ('iff',
                   'builder' or 'def'), mods, forms (the one-sided property of C, of C.dual),
                   tform (the two-sided property of C), name (the rule's name);
    faults         (id, why) for each key `check` refuses (the module docstring); none is a rule."""
    index = lean_index() if index is None else index
    plist = [p for p in (data.get("property") or []) if isinstance(p, dict)]
    props = {p.get("id"): p for p in plist}
    rev, intro, faults, names = [], [], [], set()

    def name(stem, fallback):
        out = stem if stem and stem not in names else fallback
        k = 2
        while out in names:
            out, k = "%s%d" % (fallback, k), k + 1
        names.add(out)
        return out
    for p in plist:
        if "dual" not in p:
            continue
        pid, key, srt = p.get("id"), p["dual"], p.get("sort", DEFAULT_SORT)

        def fault(why):
            faults.append((pid, why))
        if srt == "geometry":
            fault("a geometry node has no time reversal: it takes no dual key")
            continue
        if srt not in ("causality", "pair"):
            fault("a node of sort %r takes no dual key" % (srt,))
            continue
        if isinstance(key, dict):
            if sorted(key) != sorted(INTRO_KEYS) or not all(isinstance(v, str) and v for v in key.values()):
                fault("an introduction is a table {introduces = <id>, lemma = <full name>} (got %r)" % (key,))
                continue
            if srt != DEFAULT_SORT:
                fault("an introduction is the key of a one-sided node of sort causality; a pair node's key "
                      "names its time-reversal lemma")
                continue
            lemma, target = key["lemma"], key["introduces"]
        elif isinstance(key, str) and key:
            lemma, target = key, None
        else:
            fault("must be the full name of a time-reversal lemma, or a table {introduces, lemma} (got %r)" % (key,))
            continue
        forms, why = _dual_forms(p, index)
        if forms is None:
            fault("no Lean form: %s" % why)
            continue
        home = _dual_home(p.get("lean"), index, "definition")
        if home:
            fault(home)
            continue
        mods = {index["decls"][p["lean"]]}
        q = None
        if target is not None:
            q = props.get(target)
            if q is None:
                fault("introduces %r, which is not a property" % (target,))
                continue
            if target == pid:
                fault("introduces itself: an introduction concludes another node, a two-sided one")
                continue
            if q.get("sort", DEFAULT_SORT) != DEFAULT_SORT:
                fault("introduces %s, of sort %s, not causality" % (target, q.get("sort")))
                continue
            qkey = q.get("dual")
            if isinstance(qkey, dict):
                fault("introduces %s, a one-sided node (its own key is an introduction): the node an "
                      "introduction concludes is two-sided" % target)
                continue
            if not isinstance(qkey, str) or not qkey:
                fault("introduces %s, which carries no two-sided dual key: the node an introduction concludes "
                      "is two-sided, its key naming its time-reversal lemma" % target)
                continue
            tforms, why = _dual_forms(q, index)
            if tforms is None:
                fault("introduces %s, which has no Lean form: %s" % (target, why))
                continue
            home = _dual_home(q.get("lean"), index, "definition")
            if home:
                fault("introduces %s: %s" % (target, home))
                continue
            mods.add(index["decls"][q["lean"]])
        home = _dual_home(lemma, index)
        if home:
            fault(home)
            continue
        mods.add(index["decls"][lemma])
        sig = index.get("tsigs", {}).get(lemma)
        if target is None:
            if sig is None:
                fault("lemma %s is not a theorem of lean-causal/Causal" % lemma)
                continue
            shape, why = reversal_shape(sig, p["lean"])
            if not shape:
                fault("lemma %s: %s" % (lemma, why))
                continue
            rev.append({"id": pid, "sort": srt, "lemma": lemma, "shape": shape, "mods": mods, "forms": forms,
                        "name": name(_stem(p["lean"]), re.sub(r"_(\w)", lambda m: m.group(1).upper(), str(pid)))})
        else:
            shape, why = intro_shape(lemma, sig, p["lean"], q["lean"])
            if not shape:
                fault("lemma %s: %s" % (lemma, why))
                continue
            intro.append({"id": pid, "target": target, "lemma": lemma, "shape": shape, "mods": mods,
                          "forms": forms, "tform": tforms[0],
                          "name": name("%s_of_future_of_past" % _stem(q["lean"]),
                                       "%s_of_%s_of_past" % (_stem(q["lean"]), _stem(p["lean"])))})
    return rev, intro, faults


def dual_close(start, edges, two, one):
    """The closure of the literals `start` ((id, side): side 0 a property of C, side 1 of C.dual) under
    `edges` on each side (a premise-free edge, a fact, holds on both), the reversal of every id of
    `two` and the introductions `one` (one-sided id -> two-sided id: both sides of the first give
    the second of C)."""
    have = set(start)
    changed = True
    while changed:
        changed = False
        new = set()
        for e in edges:
            frm = ids_of(e.get("from")) or []
            for s in (0, 1):
                if all((x, s) in have for x in frm):
                    new.add((e.get("to"), s))
        for x in two:
            if (x, 0) in have or (x, 1) in have:
                new |= {(x, 0), (x, 1)}
        for x, t in one.items():
            if (x, 0) in have and (x, 1) in have:
                new.add((t, 0))
        if not new <= have:
            have |= new
            changed = True
    return have


def dual_contradictions(data, index=None):
    """The counterexamples the `dual` keys contradict: from what it has (of C), the edges and the
    causality-sort facts valid on its space, read on C and on C.dual, the reversals and the
    introductions reach a property it lacks (of C; of C.dual when the property is two-sided)."""
    index = lean_index() if index is None else index
    rev, intro, _ = dual_keys(data, index)
    two, one = [r["id"] for r in rev], {i["id"]: i["target"] for i in intro}
    if not two and not one:
        return []
    errs, cache, sort = [], {}, sort_of(data)
    for f in data.get("fails", []):
        on = space(f, data)
        has, lacks = counterexample(data, f, cache)
        edges = edges_on(data, on) + [{"from": [], "to": x} for x in facts_on(data, on).get(DEFAULT_SORT, ())]
        lits = dual_close({(x, 0) for x in has}, edges, two, one)
        bad = sorted({"%s of %s" % (x, "C.dual" if s else "C") for x, s in lits
                      if x in lacks and (s == 0 or x in two) and sort.get(x) is not None})
        if bad:
            errs.append("contradiction across time reversal: counterexample %s has %s, hence by the dual keys %s, "
                        "which it lacks (a key it shows one-sided?)" % (
                            f.get("witness"), " ∧ ".join(ids_of(f.get("from")) or []), ", ".join(bad)))
    return errs


def _module_doc(lines):
    return ["/-!"] + lines + ["", "Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.", "-/"]


def emit_dual(data, index=None):
    """The text of Causal/Ladder/Dual.lean generated from the `dual` keys (dual_keys), or None when no
    property carries one (the hand-written module of T-tac-ladder-dual is then the one)."""
    index = lean_index() if index is None else index
    if not has_dual_keys(data):
        return None
    rev, intro, faults = dual_keys(data, index)
    mods = sorted(set().union(*(x["mods"] for x in rev + intro)) if rev or intro else ())
    one_c = [r for r in rev if r["sort"] == DEFAULT_SORT]
    pairs = [r for r in rev if r["sort"] == "pair"]
    table = ["| node | key | rules |", "|---|---|---|"]
    for r in one_c + pairs:
        table.append("| `%s`%s | `%s` (%s) | `%s_of_dual`, `%s_dual` |" % (
            r["id"], " (pair)" if r["sort"] == "pair" else "", r["lemma"], SHAPES[r["shape"]], r["name"], r["name"]))
    for i in intro:
        table.append("| `%s` (one-sided) | introduces `%s`: `%s` (%s) | `%s` |" % (
            i["id"], i["target"], i["lemma"], SHAPES[i["shape"]], i["name"]))
    nrules = 2 * len(rev) + len(intro)
    doc = [
        "# `causal_ladder` across time reversal: the rules of the ladder's `dual` keys",
        "",
        "The rules of `Causal.Ladder.Rules` apply to any causality term, so `causal_ladder` reasons about",
        "`C.dual` from hypotheses about `C.dual`; the rules here cross from `C` to `C.dual`, in the same",
        "rule set `CausalLadder`. They are generated by `python3 tools/ladder.py emit-lean` from the `dual`",
        "keys of `programme/ladder.toml`, never edited by hand (%d rules from %d keys):" % (
            nrules, len(rev) + len(intro)),
        "",
        "* a **two-sided** node `P`, whose key is its time-reversal lemma (`C.dual.P ↔ C.P`, or",
        "  `C.P → C.dual.P`, read at `C.dual` too since `C.dual.dual` is `C` by `rfl`), gives",
        "  `p_of_dual : P C.dual → P C`, a plain forward rule that shrinks the term, and",
        "  `p_dual : P C → P C.dual`, a forward rule with the aesop **rule pattern** `Causality.dual C`:",
        "  its `C` is read off a subterm `C.dual` of the goal or of a hypothesis, so it fires only for a",
        "  `C` whose time reversal is already in sight. Without the pattern it would loop",
        "  (`C.dual.dual.…`): aesop compares hypotheses up to reducible transparency, and",
        "  `Causality.dual` is not reducible (kb/0224);",
        "* a **one-sided** node `P`, whose key is the two-sided node `Q` it introduces and the lemma",
        "  building it, gives `q_of_future_of_past : P C → P C.dual → Q C`, a plain forward rule. A",
        "  one-sided fact is never transported: `P C` does not give `P C.dual`;",
        "* a **pair** node `R` (a relation between two causalities, perhaps on an open `W`) gives the",
        "  two rules of a two-sided node, both causalities reversed, the pattern on the first.",
        "",
        "**Termination.** The rules on one causality create no new subterm `t.dual`: `p_dual` writes",
        "`t.dual` only for a `t.dual` already present, `p_of_dual` and the edge rules write terms already",
        "present, and an introduction concludes about `C` from facts about `C` and `C.dual`."] + ([
        "A pair rule `r_dual` does create one: its pattern binds the first causality only, so from",
        "`R C C'` with `C.dual` in sight it writes `C'.dual`. Such a reversal appears only beside an",
        "existing one of the same depth along a relation already in the context, so the reversal depths",
        "in sight stay bounded by those of the goal and the hypotheses, and over the finitely many",
        "causalities named there the saturated facts are finite (T-tac-ladder-dual's audit)."] if pairs else []) + [
        "",
        "Every rule is a theorem here, a restatement of the key's lemma: an aesop rule is a",
        "declaration, and an iff gives a forward rule nothing to match. The keys, node by node:",
        ""] + table + [
        "",
        "`Causal.Ladder.Rules` imports this module, so every user of `causal_ladder` has these rules;",
        "`Causal.Ladder.DualTest`, generated with it, shows what they derive and what they do not.",
        "",
        "## SCOPE (disclosed)",
        "",
        "* Time reversal is entered only where a `C.dual` occurs in the goal or a hypothesis (the",
        "  pattern): a goal about `C` from hypotheses about `C` is never sent through `C.dual`.",
        "* A goal about `C.dual.dual` is closed through the hypotheses of its terms or the builtin",
        "  `assumption`, which sees `C.dual.dual` as `C` up to definitional equality; nothing rewrites",
        "  `C.dual.dual` to `C`.",
        "* Like the edge rules, these are forward: a hypothesis under a binder is not used, and no",
        "  hypothesis is destructed through a definition (an introduction only builds its node).",
        "* Transport doubles the facts of a saturation, and every forward step counts towards aesop's",
        "  `maxRuleApplicationDepth`, which `causal_ladder` sets to 60 (kb/0225): close a long",
        "  conjunction one conjunct at a time.",
        "* A node without a `dual` key has no rule here%s." % (
            "; a key `check` refuses is a `-- skipped` line below" if faults else "")]
    lines = [GENERATED, "import Causal.Ladder.Basic"] + ["import %s" % m for m in mods] + [""] + _module_doc(doc) + [
        "", "namespace %s" % DUAL_NAMESPACE, "", "universe u", "",
        "variable {M : Type u} [TopologicalSpace M] {C C' : Causal.Causality M} {W : TopologicalSpace.Opens M}", ""]

    def pair_rules(r):
        f0, f1 = r["forms"]
        of, du = r["name"] + "_of_dual", r["name"] + "_dual"
        if r["shape"] == "iff":
            p_of, p_du = "%s.1 h" % r["lemma"], "%s.2 h" % r["lemma"]
        else:
            p_of, p_du = "(%s h :)" % r["lemma"], "%s h" % r["lemma"]
        return ["-- %s: %s (%s)" % (r["id"], r["lemma"], SHAPES[r["shape"]]),
                "theorem %s (h : %s) : %s :=" % (of, f1, f0), "  " + p_of,
                "theorem %s (h : %s) : %s :=" % (du, f0, f1), "  " + p_du,
                FORWARD + of, PATTERN + du, ""]
    if one_c:
        lines += ["/-! ## Two-sided nodes: `P C.dual → P C` and `P C → P C.dual` -/", ""]
        for r in one_c:
            lines += pair_rules(r)
    if intro:
        lines += ["/-! ## One-sided nodes: the two-sided node from the future and the past forms -/", ""]
        for i in intro:
            proof = {"iff": "%s.2 ⟨hf, hp⟩" % i["lemma"], "builder": "%s hf hp" % i["lemma"],
                     "def": "⟨hf, hp⟩"}[i["shape"]]
            lines += ["-- %s introduces %s: %s (%s)" % (i["id"], i["target"], i["lemma"], SHAPES[i["shape"]]),
                      "theorem %s (hf : %s) (hp : %s) : %s :=" % (i["name"], i["forms"][0], i["forms"][1], i["tform"]),
                      "  " + proof, FORWARD + i["name"], ""]
    if pairs:
        lines += ["/-! ## Pair nodes: both causalities reversed, the pattern on the first -/", ""]
        for r in pairs:
            lines += pair_rules(r)
    for pid, why in faults:
        lines.append("-- skipped dual key of %s: %s" % (pid, why))
    if faults:
        lines.append("")
    lines.append("end %s" % DUAL_NAMESPACE)
    return "\n".join(lines) + "\n"


def dual_lits(data, index):
    """What Causal/Ladder/DualTest.lean reads, on a bare space: (forms: id -> (the property of C, of
    C.dual), for the causality-sort properties with a Lean form; ids, in the ladder's order; two,
    the ids with reversal rules; one, one-sided id -> the two-sided id it introduces; edges, the
    emitted edges and facts without standing)."""
    rules, _ = emitted(data, index)
    facts, _, _ = emitted_facts(data, index, rules)
    edges = [e for e, _ in rules if not standing(e)] + [_fact_edge(f) for f, *_ in facts if not standing(f)]
    rev, intro, _ = dual_keys(data, index)
    forms = {}
    for p in data.get("property", []):
        if p.get("sort", DEFAULT_SORT) == DEFAULT_SORT:
            f0 = lean_form(p, index)[0]
            if f0:
                forms[p["id"]] = (f0, lean_form(p, index, "C.dual")[0])
    ids = [p["id"] for p in data.get("property", []) if p.get("id") in forms]
    two = [r["id"] for r in rev if r["id"] in forms]
    one = {i["id"]: i["target"] for i in intro if i["id"] in forms and i["target"] in forms}
    return forms, ids, two, one, edges


def dual_refutations(data, lits):
    """(has, lacks, why) literal sets, one per counterexample of the ladder and one per its time
    reversal: what it has, closed by dual_close, and what it lacks, read backwards to a fixpoint (a
    literal whose closure with what it has meets what it lacks is lacked). A counterexample whose
    sets meet is a contradiction (check's dual_contradictions) and refutes nothing here."""
    forms, ids, two, one, edges = lits
    out, cache = [], {}
    for f in data.get("fails", []):
        has, lacks = counterexample(data, f, cache)
        hl = dual_close({(x, 0) for x in has if x in forms}, edges, two, one)
        ll = {(x, 0) for x in lacks if x in forms} | {(x, 1) for x in lacks if x in two}
        changed = True
        while changed:
            changed = False
            for x in ids:
                for s in (0, 1):
                    if (x, s) not in hl and (x, s) not in ll and dual_close(hl | {(x, s)}, edges, two, one) & ll:
                        ll.add((x, s))
                        changed = True
        if hl & ll:
            continue
        out.append((hl, ll, f.get("witness")))
        out.append(({(x, 1 - s) for x, s in hl}, {(x, 1 - s) for x, s in ll}, "%s, time-reversed" % f.get("witness")))
    return out


def dual_pairs(data, lits):
    """The single-literal pairs across time reversal: (derived, refuted, unknown); a refuted pair
    carries the counterexample's witness."""
    forms, ids, two, one, edges = lits
    refs = dual_refutations(data, lits)
    der, ref, unk = [], [], []
    for a in ids:
        for s in (0, 1):
            clo = dual_close({(a, s)}, edges, two, one)
            for b in ids:
                goal = (b, 1 - s)
                if goal in clo:
                    der.append(((a, s), goal))
                    continue
                w = next((w for hl, ll, w in refs if (a, s) in hl and goal in ll), None)
                (ref if w else unk).append(((a, s), goal, w))
    return der, ref, unk


def emit_dual_test(data, index=None):
    """The text of Causal/Ladder/DualTest.lean generated from the `dual` keys, or None when no property
    carries one. Derived: every single-property pair across time reversal of the closure on a bare
    space, each conjunctive edge on C.dual with its two-sided premises on C, each introduction (of C
    and of C.dual), each pair node both ways. Not derived: every P(C) ⇏ Q(C.dual), and every
    P(C.dual) ⇏ Q(C) with a one-sided end, that a counterexample or its time reversal refutes."""
    index = lean_index() if index is None else index
    if not has_dual_keys(data):
        return None
    lits = dual_lits(data, index)
    forms, ids, two, one, edges = lits
    rev, intro, _ = dual_keys(data, index)
    der, ref, _ = dual_pairs(data, lits)
    ref = [r for r in ref if r[0][1] == 0 or r[0][0] in one or r[1][0] in one]
    mix = []
    for e in edges:
        frm = ids_of(e["from"]) or []
        if len(frm) > 1 and any(x in two for x in frm) and all(x in forms for x in frm) and e["to"] in forms:
            mix.append(([(x, 0) if x in two else (x, 1) for x in frm], (e["to"], 1), e["witness"]))
    intros = [i for i in intro if i["id"] in one]
    pairs = [r for r in rev if r["sort"] == "pair"]
    props = {p.get("id"): p for p in data.get("property", [])}
    mods = sorted({index["decls"][props[x]["lean"]] for x in forms} |
                  {index["decls"][props[r["id"]]["lean"]] for r in pairs})

    def lit(l):
        return forms[l[0]][l[1]]

    def name(l):
        return "%s(%s)" % (l[0], "C.dual" if l[1] else "C")

    def pos(src, goal, comment, pre=""):
        hyps = " ".join([pre] * bool(pre) + ["(_h%d : %s)" % (k, x) for k, x in enumerate(src)])
        return ["-- %s" % comment, "example %s : %s := by causal_ladder" % (hyps, goal)]

    def neg(src, goal, comment):
        hyps = " ".join("(_h%d : %s)" % (k, x) for k, x in enumerate(src))
        return ["-- %s" % comment, "example %s : True := by" % hyps,
                "  fail_if_success have : %s := by causal_ladder" % goal, "  trivial"]
    nint, npair = 2 * len(intros), 2 * len(pairs)
    doc = [
        "# Tests of `causal_ladder` across time reversal, generated from the ladder's `dual` keys",
        "",
        "For `C` a causality on a topological space, `causal_ladder` with the rules of",
        "`Causal.Ladder.Rules` and of `Causal.Ladder.Dual` (generated with this file from the `dual` keys",
        "of `programme/ladder.toml` by `python3 tools/ladder.py emit-lean`) closes a goal about `C.dual`",
        "from hypotheses about `C`, and conversely. `Derived`: every single-property pair",
        "`P(C) ⊢ Q(C.dual)` and `P(C.dual) ⊢ Q(C)` of the closure of the rules on a bare space (%d" % len(der),
        "examples), each conjunctive rule used on `C.dual` with its two-sided premises given on `C` (%d)," % len(mix),
        "each introduction of a two-sided node from a one-sided one and its past form, of `C` and of",
        "`C.dual` (%d), and each pair node both ways (%d). `Not derived`: the pairs across time reversal" % (nint, npair),
        "that a counterexample of the ladder, or its time reversal, refutes (%d examples: every" % len(ref),
        "`P(C) ⇏ Q(C.dual)`, and every `P(C.dual) ⇏ Q(C)` with a one-sided end). A refuted pair stays",
        "underived however the ladder grows; a derived one goes with a withdrawn rule, and emit-lean",
        "writes this file again. The first command fails if a model module is imported, directly or",
        "transitively, as in `Causal.Ladder.Test`.",
        "",
        "## SCOPE (disclosed)",
        "",
        "* The examples are on a bare topological space: a rule with `standing` instances is not",
        "  exercised here (`Causal.Ladder.Test` exercises it on `C`).",
        "* No example has more than one time reversal: `C.dual.dual` is `C` by `rfl`, so the builtin",
        "  `assumption` closes such a goal without the rules (kb/0264).",
        "* A pair node is tested both ways; no pair is refuted across one reversal here."]
    lines = [GENERATED, "import Causal.Ladder.Rules", "import %s" % DUAL_MODULE] + [
        "import %s" % m for m in mods if m != DUAL_MODULE] + [""] + _module_doc(doc) + [
        "",
        "open Lean in",
        "run_cmd do",
        "  let models : List Name := [%s]" % ", ".join("`" + m for m in MODEL_LAYER),
        "  for m in (← getEnv).header.moduleNames do",
        "    if models.any (·.isPrefixOf m) then",
        "      throwError \"the ladder's Lean imports the model module {m}\"",
        "", "section", "", "universe u", "",
        "variable {M : Type u} [TopologicalSpace M] (C C' : Causal.Causality M)", "",
        "/-! ## Derived across time reversal, from one property -/", ""]
    for a, b in der:
        lines += pos([lit(a)], lit(b), "%s ⇒ %s" % (name(a), name(b)))
    lines += ["", "/-! ## Derived on `C.dual` through a conjunctive rule, two-sided premises on `C` -/", ""]
    for src, goal, w in mix:
        lines += pos([lit(x) for x in src], lit(goal), "%s ⇒ %s (%s on C.dual)" % (
            " ∧ ".join(name(x) for x in src), name(goal), w))
    if intros:
        lines += ["", "/-! ## Introductions: the two-sided node from a one-sided node and its past form -/", ""]
        for i in intros:
            src = [lit((i["id"], 0)), lit((i["id"], 1))]
            for s in (0, 1):
                lines += pos(src, lit((i["target"], s)), "%s ∧ %s ⇒ %s (%s)" % (
                    name((i["id"], 0)), name((i["id"], 1)), name((i["target"], s)), i["name"]))
    if pairs:
        lines += ["", "/-! ## Pair nodes, both causalities reversed -/", ""]
        for r in pairs:
            f0, f1 = r["forms"]
            pre = "(W : TopologicalSpace.Opens M)" if f0.endswith(" W") else ""
            lines += pos([f0], f1, "%s(C, C') ⇒ %s(C.dual, C'.dual)" % (r["id"], r["id"]), pre)
            lines += pos([f1], f0, "%s(C.dual, C'.dual) ⇒ %s(C, C')" % (r["id"], r["id"]), pre)
    lines += ["", "/-! ## Not derived across time reversal: refuted pairs -/", ""]
    for a, b, w in ref:
        lines += neg([lit(a)], lit(b), "%s ⇏ %s (refuted: %s)" % (name(a), name(b), w))
    lines += ["", "end"]
    return "\n".join(lines) + "\n"


#: The options each subcommand takes (name -> number of values). Anything else is refused with exit
#: status 2 before the ladder is read or a file written, so that a misspelt flag never runs a
#: subcommand with its defaults (T-tool-ladder-emit-args: `emit-lean --help` used to rewrite the
#: generated Rules.lean and Test.lean, kb/0252).
OPTIONS = {"check": {"--file": 1}, "matrix": {"--file": 1}, "dot": {"--file": 1},
           "emit-lean": {"--dry-run": 0}}


def parse_args(argv):
    """(cmd, opts) from the command line; `-h`/`--help` anywhere prints the usage and exits 0 having
    read and written nothing; an unknown subcommand or argument exits 2 with a message."""
    if not argv or any(a in ("-h", "--help") for a in argv):
        print(__doc__)
        sys.exit(0 if argv else 2)
    cmd, rest = argv[0], argv[1:]
    if cmd not in OPTIONS:
        sys.stderr.write("ladder: unknown subcommand %r (one of %s)\n" % (cmd, ", ".join(sorted(OPTIONS))))
        sys.exit(2)
    opts, k = {}, 0
    while k < len(rest):
        a = rest[k]
        if a not in OPTIONS[cmd]:
            sys.stderr.write("ladder: %s takes no argument %r (it takes: %s)\n" % (
                cmd, a, ", ".join(sorted(OPTIONS[cmd])) or "none"))
            sys.exit(2)
        n = OPTIONS[cmd][a]
        if n and k + n >= len(rest):
            sys.stderr.write("ladder: %s needs a value\n" % a)
            sys.exit(2)
        opts[a] = rest[k + 1] if n else True
        k += 1 + n
    return cmd, opts


def main(argv):
    cmd, opts = parse_args(argv)
    path = opts.get("--file", FILE)
    data = load(path)
    if cmd == "check":
        errs = check(data)
        for e in errs:
            print("ladder: " + e)
        print(check_line(summary(data, errs)))
        sys.exit(1 if errs else 0)
    if cmd == "matrix":
        edges = edges_on(data, None)
        amb = ambient(data)
        for (a, b), v in sorted(matrix(data).items()):
            extra = ""
            if v == "implied-standing":
                extra = " (%s)" % ", ".join(needed_standing((a,), b, edges + fact_edges(data, a), amb))
            elif v == "fails-off":
                extra = " (on %s)" % "; ".join(", ".join(w) for w in off_spaces(data, a, b))
            print("%-24s %-24s %s%s" % (a, b, v, extra))
        return
    if cmd == "emit-lean":
        index = lean_index()
        rules, skipped = emitted(data, index)
        facts, local, fskipped = emitted_facts(data, index, rules)
        text, test = emit_lean(data, index), emit_test(data, index)
        outs, kept = [(RULES, text), (TEST, test)], []
        if has_dual_keys(data):          # T-tac-ladder-dual-key: never over a hand-written module
            if dual_generated(data, index):
                outs.append((DUAL, emit_dual(data, index)))
                if _written(DUAL_TEST_MODULE, index):
                    outs.append((DUAL_TEST, emit_dual_test(data, index)))
                else:
                    kept.append(DUAL_TEST)
            else:
                kept += [DUAL, DUAL_TEST]
        if opts.get("--dry-run"):
            for p, body in outs:
                try:
                    with open(p, encoding="utf-8") as fh:
                        cur = fh.read()
                except FileNotFoundError:
                    cur = None
                print("ladder: %s %s" % (os.path.relpath(p, ROOT), "unchanged" if cur == body else
                                         "absent" if cur is None else "would change"))
            for p in kept:
                print("ladder: %s is hand-written: kept (emit-lean writes it from the dual keys once it is "
                      "removed)" % os.path.relpath(p, ROOT))
            return
        os.makedirs(os.path.dirname(RULES), exist_ok=True)
        for p, body in outs:
            with open(p, "w", encoding="utf-8") as fh:
                fh.write(body)
        print("ladder: wrote %s (%d rules from edges, %d checked edges skipped; %d fact rules, %d facts "
              "registered in Test only, %d skipped) and %s (%d derived, %d not derived)" % (
                  os.path.relpath(RULES, ROOT), len(rules), len(skipped), len(facts), len(local),
                  len(fskipped), os.path.relpath(TEST, ROOT),
                  sum(1 for x in test.splitlines() if x.startswith("example") and x.endswith("by causal_ladder")),
                  test.count("fail_if_success")))
        for p, body in outs[2:]:
            print("ladder: wrote %s (%d theorems, %d examples)" % (
                os.path.relpath(p, ROOT), body.count("\ntheorem "), body.count("\nexample ")))
        for p in kept:
            print("ladder: %s is hand-written: kept" % os.path.relpath(p, ROOT))
        return
    if cmd == "dot":
        print("digraph ladder { rankdir=BT; node [shape=box];")
        for e in data.get("implies", []):
            for a in ids_of(e["from"]):
                print('  "%s" -> "%s" [style=%s];' % (a, e["to"], "solid" if e["status"] == "checked" else "dashed"))
        print("}")
        return


if __name__ == "__main__":
    main(sys.argv[1:])
