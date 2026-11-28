#!/usr/bin/env python3
"""A miniature hub for tools/rename_tool.py, its rename map, and one breakage per rule.

    python3 minihub.py --list            # breakage names and the rule each must fail with
    python3 minihub.py DIR               # build the unbroken miniature hub in DIR (its check passes)
    python3 minihub.py DIR NAME          # build it with breakage NAME applied

The miniature hub has one package, lean-alpha (libs Alpha and AlphaScaffold), whose module
Alpha.Flat.Basic declares namespace Alpha.Flat, and every file kind the tool rewrites: a curation,
a binder, the ladder, both roadmaps, a kb entry, the atlas's hub.toml, a facts file and an edges
file, each naming Alpha.Flat.* declarations and Alpha/Flat/*.lean paths. MAP renames Alpha.Flat to
Alpha.Lorentz. Every breakage writes into DIR only:

  dangling-decl        a curation row names Alpha.Flat.ghost, declared nowhere      -> `dangling`
  dangling-path        a curation row names Alpha/Flat/Ghost.lean, which is absent  -> `dangling`
  dangling-import      a module imports Alpha.Flat.Ghost, which has no file         -> `dangling`
  relative-namespace   Alpha/Flat/Extra.lean opens `namespace Flat` inside `namespace Alpha`,
                       which the rewrite cannot carry; after `apply MAP` the ladder's
                       Alpha.Lorentz.qux no longer resolves                         -> `regression`
The first three are found by `check`, the last by `apply` (on a copy of DIR).
"""
import json
import os
import sys

MAP = '[rename]\n"Alpha.Flat" = "Alpha.Lorentz"\n"AlphaScaffold.Flat" = "AlphaScaffold.Lorentz"\n'

LAKE = '''name = "Alpha"
[[lean_lib]]
name = "Alpha"
[[lean_lib]]
name = "AlphaScaffold"
srcDir = "scaffold"
'''

FILES = {
    "lean-alpha/lakefile.toml": LAKE,
    "lean-alpha/Alpha.lean": "import Alpha.Flat.Basic\nimport Alpha.Core\n",
    "lean-alpha/Alpha/Flat/Basic.lean": '''import Mathlib.Logic.Basic

/-! Alpha.Flat.Basic: the flat layer. See also Alpha/Flat/Basic.lean. -/

namespace Alpha.Flat

/-- A structure. -/
structure Bar where
  x : Nat

theorem foo : True := trivial

theorem foo' : True := Alpha.Flat.foo

end Alpha.Flat
''',
    "lean-alpha/Alpha/Core.lean": '''import Alpha.Flat.Basic

namespace Alpha

open Alpha.Flat in
theorem baz : True := foo

theorem baz' : True := _root_.Alpha.Flat.foo'

def bar (b : Alpha.Flat.Bar) : Nat := b.x

end Alpha
''',
    "lean-alpha/scaffold/AlphaScaffold.lean": "import AlphaScaffold.Flat.Draft\n",
    "lean-alpha/scaffold/AlphaScaffold/Flat/Draft.lean": '''import Alpha.Flat.Basic

namespace AlphaScaffold.Flat

theorem draft : True := Alpha.Flat.foo

end AlphaScaffold.Flat
''',
    "lean-alpha/kb/entries/0001-flat.md": "# The flat layer\n\nUse `Alpha.Flat.foo` (Alpha/Flat/Basic.lean); "
                                          "Alpha.Flat is the namespace. Alpha theory, in prose, is not renamed.\n",
    "papers/p/certificate/curation.toml": '''# Alpha.Flat.foo is the anchor.
[[row]]
label = "thm:one"
decls = ["Alpha.Flat.foo", "Alpha.baz"]
extra_lean_files = ["Alpha/Flat/Basic.lean"]
notes = "Anchored by Alpha.Flat.foo and Alpha.Flat.Bar.x in Alpha/Flat/Basic.lean:9."
''',
    "papers/p/certificate/binder.toml": '''[[bind]]
label = "thm:one"
ett = ["Alpha.Flat.foo", "T-some-target"]
localisation = ["some_ladder_id"]
note = "Alpha.Flat.foo'."
''',
    "programme/ladder.toml": '''[[property]]
id = "flat"
lean = "Alpha.Flat.Bar"

[[implies]]
from = ["flat"]
to = "flat"
witness = "Alpha.baz"
''',
    "roadmap/roadmap.toml": '''[[target]]
id = "T-one"
evidence = "Done: Alpha.Flat.{foo,foo'} (Alpha/Flat/Basic.lean:11), Alpha.Flat.Basic."
''',
    "programme/roadmap.toml": '''[[target]]
id = "T-two"
evidence = "AlphaScaffold.Flat.draft in scaffold/AlphaScaffold/Flat/Draft.lean."
''',
    "reports/atlas/hub.toml": '''[paper.p]
short = "P"
headline = ["Alpha.Flat.foo", "Alpha.baz"]
summary = "Alpha.Flat.foo and Alpha.Flat.Bar."
''',
}

FACTS = {
    "declarations": {
        "Alpha.Flat.Bar": {"module": "Alpha.Flat.Basic"},
        "Alpha.Flat.Bar.x": {"module": "Alpha.Flat.Basic"},
        "Alpha.Flat.Bar.mk": {"module": "Alpha.Flat.Basic"},
        "Alpha.Flat.foo": {"module": "Alpha.Flat.Basic"},
        "Alpha.Flat.foo'": {"module": "Alpha.Flat.Basic"},
        "Alpha.baz": {"module": "Alpha.Core"},
        "Alpha.baz'": {"module": "Alpha.Core"},
        "Alpha.bar": {"module": "Alpha.Core"},
        "AlphaScaffold.Flat.draft": {"module": "AlphaScaffold.Flat.Draft"},
    },
    "extracted": {"package": "lean-alpha", "libs": [["Alpha", "."], ["AlphaScaffold", "scaffold"]]},
    "modules": 4,
    "roots": ["Alpha", "AlphaScaffold"],
}

EDGES = {
    "decls": {"Alpha.Flat.foo": "lean-alpha/Alpha/Flat/Basic.lean:11", "Alpha.baz": "lean-alpha/Alpha/Core.lean:5"},
    "principals": {"thm:one": ["Alpha.Flat.foo"]},
    "edges": [{"kind": "lean-only", "source": "thm:one", "target": "thm:one", "witness": ["Alpha.baz", "Alpha.Flat.foo"]}],
    "package": "lean-alpha",
    "paper": "p",
}

EXTRA = '''import Alpha.Flat.Basic

namespace Alpha

namespace Flat

theorem qux : True := trivial

end Flat

end Alpha
'''

# name -> (rule, how it is found, what it does)
BREAKAGES = {
    "dangling-decl": ("dangling", "check", "a curation row names Alpha.Flat.ghost"),
    "dangling-path": ("dangling", "check", "a curation row names Alpha/Flat/Ghost.lean"),
    "dangling-import": ("dangling", "check", "Alpha.Core imports Alpha.Flat.Ghost"),
    "relative-namespace": ("regression", "apply", "namespace Flat inside namespace Alpha, then apply MAP"),
}


def write(d, rel, text):
    p = os.path.join(d, rel)
    os.makedirs(os.path.dirname(p), exist_ok=True)
    with open(p, "w", encoding="utf-8") as f:
        f.write(text)


def build(d, breakage=None):
    for rel, text in FILES.items():
        write(d, rel, text)
    write(d, "reports/atlas/lean/facts-lean-alpha.json", json.dumps(FACTS, indent=1, sort_keys=True) + "\n")
    write(d, "reports/atlas/lean/edges-p.json", json.dumps(EDGES, indent=1, sort_keys=True) + "\n")
    write(d, "rename.toml", MAP)
    cur = os.path.join(d, "papers/p/certificate/curation.toml")
    if breakage == "dangling-decl":
        with open(cur, "a") as f:
            f.write('\n[[row]]\nlabel = "thm:two"\ndecls = ["Alpha.Flat.ghost"]\n')
    elif breakage == "dangling-path":
        with open(cur, "a") as f:
            f.write('\n[[row]]\nlabel = "thm:two"\ndecls = []\nextra_lean_files = ["Alpha/Flat/Ghost.lean"]\n')
    elif breakage == "dangling-import":
        write(d, "lean-alpha/Alpha/Core.lean", "import Alpha.Flat.Ghost\n" + FILES["lean-alpha/Alpha/Core.lean"])
    elif breakage == "relative-namespace":
        write(d, "lean-alpha/Alpha/Flat/Extra.lean", EXTRA)
        write(d, "lean-alpha/Alpha.lean", FILES["lean-alpha/Alpha.lean"] + "import Alpha.Flat.Extra\n")
        with open(os.path.join(d, "programme/ladder.toml"), "a") as f:
            f.write('\n[[property]]\nid = "extra"\nlean = "Alpha.Flat.qux"\n')
    elif breakage is not None:
        raise SystemExit("unknown breakage %s" % breakage)


def main(argv):
    if argv[:1] == ["--list"]:
        for n, (rule, how, _) in BREAKAGES.items():
            print(n, rule, how)
        return 0
    if not argv or len(argv) > 2:
        print(__doc__)
        return 2
    build(argv[0], argv[1] if len(argv) > 1 else None)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
