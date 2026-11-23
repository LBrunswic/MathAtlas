#!/usr/bin/env python3
"""The causality ladder of ETT (programme/ladder.toml): check it, classify it, emit its Lean rules.

    python3 tools/ladder.py check [--file F]   schema, ids, sorts, labels, Lean names, no contradiction
    python3 tools/ladder.py matrix [--file F]  every ordered pair of properties, classified (below)
    python3 tools/ladder.py emit-lean [--dry-run]  write lean-causal/Causal/Ladder/Rules.lean from the
                                               checked edges and facts (and its tests,
                                               Causal/Ladder/Test.lean)
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
                     (causality | geometry | pair; absent means causality)
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

status is seed | checked. Lean names (property `lean`, every witness and counterexample) resolve
NAMESPACE-EXACTLY: a name is found when it is the full name of a declaration of
lean-causal/Causal (namespace and section blocks read, comments blanked: lean_index); a dotted
suffix is not enough. tools/binder.py inherits this.

Standing hypotheses. `standing` lists hypotheses on the topological space M that are not ladder
nodes; each word is a Mathlib class on M, which the witness takes as an instance argument:

    T0 T1 T2 T3 regular normal   T0Space T1Space T2Space T3Space RegularSpace NormalSpace
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

with the implications T3 → T2, regular; T2 → T1 → T0; second_countable → first_countable,
separable; connected → preconnected, nonempty; compact → sigma_compact; metrizable → T2 (each a
Mathlib instance, so a context with the stronger class gives the weaker). A set of words is read
closed under them: the ambient {T2, second_countable} is {T0, T1, T2, second_countable,
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
    "T2": ("T2Space", ("T1",)),
    "regular": ("RegularSpace", ()),
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
    "property": {"id", "lean", "what", "label", "sort"},
    "implies": {"from", "to", "witness", "status", "under", "standing"},
    "fails": {"from", "to", "witness", "status", "space"},
    "consequence": {"at", "statement", "witness", "status", "under", "standing"},
    "open": {"from", "to", "note"},
    "transfer": {"pair", "property", "direction", "narrower", "wider", "witness", "counterexample",
                 "status", "under", "standing", "space"},
    "fact": {"property", "witness", "status", "standing", "note"},
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


def check(data, names=None, labels=None):
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
# * A fact passing every check but whose witness's module imports Causal.Ladder.Rules (curves_extend:
#   Causal.CurvesExtendSecondCountable → MaximalZorn → ErsMughd → Rules) is a skipped line in
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
    `tsigs`   the same for every `theorem` and `lemma` (what a [[fact]]'s witness is stated for)."""
    decls, imports, sigs, tsigs = {}, {}, {}, {}
    for f in sorted(glob.glob(os.path.join(root, "Causal", "**", "*.lean"), recursive=True)):
        mod = os.path.relpath(f, root)[:-len(".lean")].replace(os.sep, ".")
        with open(f, encoding="utf-8") as fh:
            code = _code(fh.read())
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
    return {"decls": decls, "imports": imports, "sigs": sigs, "tsigs": tsigs}


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
    dual, dual_why = dual_import(index)
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
        ""] if facts or local else []) + ([
        "This module imports `Causal.Ladder.Dual`, the hand-written time-reversal rules of the same rule",
        "set, so every user of `causal_ladder` reasons across `C.dual` (T-tac-ladder-dual).",
        ] if dual else []) + [
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
        if opts.get("--dry-run"):
            for p, body in ((RULES, text), (TEST, test)):
                try:
                    with open(p, encoding="utf-8") as fh:
                        cur = fh.read()
                except FileNotFoundError:
                    cur = None
                print("ladder: %s %s" % (os.path.relpath(p, ROOT), "unchanged" if cur == body else
                                         "absent" if cur is None else "would change"))
            return
        os.makedirs(os.path.dirname(RULES), exist_ok=True)
        for p, body in ((RULES, text), (TEST, test)):
            with open(p, "w", encoding="utf-8") as fh:
                fh.write(body)
        print("ladder: wrote %s (%d rules from edges, %d checked edges skipped; %d fact rules, %d facts "
              "registered in Test only, %d skipped) and %s (%d derived, %d not derived)" % (
                  os.path.relpath(RULES, ROOT), len(rules), len(skipped), len(facts), len(local),
                  len(fskipped), os.path.relpath(TEST, ROOT),
                  sum(1 for x in test.splitlines() if x.startswith("example") and x.endswith("by causal_ladder")),
                  test.count("fail_if_success")))
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
