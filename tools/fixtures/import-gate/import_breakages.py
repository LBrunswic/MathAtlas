#!/usr/bin/env python3
"""A miniature hub for tools/import_gate.py, and one breakage per rule.

    python3 import_breakages.py --list              # the breakage names
    python3 import_breakages.py DIR                 # build the unbroken miniature hub in DIR (it must pass)
    python3 import_breakages.py DIR NAME            # build it with breakage NAME applied (it must fail NAME)

The miniature hub has one library per tier: A (general), A2 (general), B (local, depends A),
O (orbit), G and H (global; G takes O as an input; H imports G), Z (outside), and a scaffold
AScaffold of A. A.Core carries `import` in a line comment and in a block comment after the
header, which the header reader must not count. Every breakage writes into DIR only.
"""
import os
import sys

LAKE = 'name = "{pkg}"\n[[lean_lib]]\nname = "{lib}"\nglobs = ["{lib}.*"]\n'
SCAFFOLD = '[[lean_lib]]\nname = "{lib}Scaffold"\nsrcDir = "scaffold"\nglobs = ["{lib}Scaffold.*"]\n'

TIERS = '''
[[library]]
name = "A"
tier = "general"
modules = ["A"]

[[library]]
name = "A2"
tier = "general"
modules = ["A2"]

[[library]]
name = "B"
tier = "local"
modules = ["B"]
depends = ["A"]

[[library]]
name = "O"
tier = "orbit"
modules = ["O"]

[[library]]
name = "G"
tier = "global"
modules = ["G"]
inputs = ["O"]

[[library]]
name = "H"
tier = "global"
modules = ["H"]

[[library]]
name = "Z"
tier = "outside"
modules = ["Z"]
'''

BASE = {
    "lean-a/lakefile.toml": LAKE.format(pkg="A", lib="A") + SCAFFOLD.format(lib="A"),
    "lean-a/A.lean": "import A.Core\n",
    "lean-a/A/Core.lean": ("/-! a module doc -/\nimport Mathlib.Logic.Basic\n-- import B.M\n\n"
                           "/-! ## not the header\nimport Z.W\n-/\nnamespace A\nend A\n"
                           "import G.X\n"),
    "lean-a/scaffold/AScaffold/S.lean": "import A.Core\n",
    "lean-a2/lakefile.toml": LAKE.format(pkg="A2", lib="A2"),
    "lean-a2/A2/Core.lean": "import Mathlib.Logic.Basic\n",
    "lean-b/lakefile.toml": LAKE.format(pkg="B", lib="B"),
    "lean-b/B/M.lean": "import A.Core\n",
    "lean-o/lakefile.toml": LAKE.format(pkg="O", lib="O"),
    "lean-o/O/G.lean": "import Mathlib.Logic.Basic\n",
    "lean-g/lakefile.toml": LAKE.format(pkg="G", lib="G"),
    "lean-g/G/X.lean": "import B.M\nimport O.G\n",
    "lean-h/lakefile.toml": LAKE.format(pkg="H", lib="H"),
    "lean-h/H/Y.lean": "import G.X\n",
    "lean-z/lakefile.toml": LAKE.format(pkg="Z", lib="Z"),
    "lean-z/Z/W.lean": "public import A.Core\nimport G.X\n",
    "hub.toml": '[hub]\ndropbox_ignored = ["lean-a/.lake", "lean-b/.lake"]\n',
}

# name -> (the rule the gate must report, files written over the base, text appended to the tiers)
BREAKAGES = {
    "upward": ("upward", {"lean-a/A/Up.lean": "import B.M\n"}, ""),
    "general-imports-general": ("upward", {"lean-a/A/Side.lean": "import A2.Core\n"}, ""),
    "cycle": ("cycle", {"lean-g/G/Back.lean": "import H.Y\n"}, ""),
    "undeclared-orbit": ("undeclared-orbit", {"lean-b/B/N.lean": "import O.G\n"}, ""),
    "orbit-imports-hub": ("orbit-imports-hub", {"lean-o/O/H.lean": "import A.Core\n"}, ""),
    "into-outside": ("into-outside", {"lean-g/G/Z.lean": "import Z.W\n"}, ""),
    "undeclared-dep": ("undeclared-dep", {"lean-b/B/P.lean": "import A2.Core\n"}, ""),
    "strict-imports-scaffold": ("strict-imports-scaffold", {"lean-a/A/Sc.lean": "import AScaffold.S\n"}, ""),
    "undeclared-module": ("undeclared-module", {"lean-u/lakefile.toml": LAKE.format(pkg="U", lib="U"),
                                                "lean-u/U/Q.lean": "import A.Core\n"}, ""),
    "unresolved": ("unresolved", {"lean-a/A/Gone.lean": "import A.Nowhere\n"}, ""),
    "root-aggregator": ("root-aggregator", {"lean-a/A.lean": "import A.Core\nimport B.M\n"}, ""),
    "hub-package-missing": ("CONFIG", {"hub.toml": '[hub]\ndropbox_ignored = ["lean-a/.lake", "lean-q/.lake"]\n'}, ""),
    "bad-tier": ("CONFIG", {}, '\n[[library]]\nname = "Q"\ntier = "semi-local"\nmodules = []\n'),
    "input-not-orbit": ("CONFIG", {}, '\n[[library]]\nname = "Q"\ntier = "global"\nmodules = []\ninputs = ["B"]\n'),
}


def build(d, name=None):
    files, extra = dict(BASE), ""
    if name is not None:
        _, over, extra = BREAKAGES[name]
        files.update(over)
    for rel, text in files.items():
        p = os.path.join(d, rel)
        os.makedirs(os.path.dirname(p), exist_ok=True)
        with open(p, "w", encoding="utf-8") as f:
            f.write(text)
    with open(os.path.join(d, "tiers.toml"), "w", encoding="utf-8") as f:
        f.write(TIERS + extra)


def main(argv):
    if argv[1:] == ["--list"]:
        for n, (rule, _, _) in BREAKAGES.items():
            print(n, rule)
        return 0
    if len(argv) not in (2, 3) or (len(argv) == 3 and argv[2] not in BREAKAGES):
        print(__doc__)
        return 2
    build(argv[1], argv[2] if len(argv) == 3 else None)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
