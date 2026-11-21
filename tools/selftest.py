#!/usr/bin/env python3
"""Every gate is shown to bite.

    python3 tools/selftest.py   # exit 1 if any fixture fails to make its gate fail

Runs `tools/registers.py selftest` (JSON fixtures, one per rule) and then every
`tools/fixtures/<gate>/run.sh`, each of which sets up a broken copy of the thing its gate checks
(in a temporary directory, never in the tree) and runs the gate; the gate must exit non-zero.
A gate directory under tools/fixtures/ with no run.sh, or a gate script under tools/ with no
fixture directory, is itself a failure: a gate nobody has seen fail proves nothing.
"""
import os
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
FIX = os.path.join(ROOT, "tools", "fixtures")
# gate script -> fixture directory (registers has its own selftest; the regression is a test, not a gate)
GATES = {"host_guard.py": "host", "dropbox_ignore.py": "dropbox-ignore", "deps_register.py": "deps",
         "legacy_check.py": "legacy-frozen", "ledger.py": "ledger", "story_lint.py": "story",
         "no_legacy_prose.py": "no-legacy-prose", "papers_check.py": "papers-check",
         "doubledag.py": "doubledag", "ladder.py": "ladder"}


def main():
    fail = 0
    r = subprocess.run(["python3", os.path.join(ROOT, "tools", "registers.py"), "selftest"], cwd=ROOT)
    if r.returncode != 0:
        fail += 1
    for script, gate in GATES.items():
        run = os.path.join(FIX, gate, "run.sh")
        if not os.path.exists(run):
            print("selftest: FAIL %s has no fixture (%s/run.sh)" % (script, gate))
            fail += 1
            continue
        r = subprocess.run(["bash", run], cwd=ROOT, capture_output=True, text=True,
                           env={**os.environ, "LEANARTICLES_HUB": ROOT})
        last = (r.stdout.strip().split("\n") or [""])[-1]
        if r.returncode == 0:
            print("selftest: FAIL %s passed on its fixture: %s" % (gate, last))
            fail += 1
        else:
            print("selftest: %s -> exit %d: %s" % (gate, r.returncode, last))
    if fail:
        return 1
    print("selftest: every gate shown to bite")
    return 0


if __name__ == "__main__":
    sys.exit(main())
