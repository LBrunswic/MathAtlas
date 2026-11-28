# In-memory emit-lean dry run for T-abs-sc-open-hoist (kb/0252: never run `ladder.py emit-lean`).
# Computes ladder.emit_lean / emit_test from the working tree's sources and diffs them against the
# Rules.lean / Test.lean on disk. Writes nothing. Run: python3 -I emit_probe.py
import sys, difflib
sys.path.insert(0, "/home/maxbrain/Dropbox/LeanArticles/tools")
import ladder
ROOT = "/home/maxbrain/Dropbox/LeanArticles/lean-causal"
data = ladder.load(ladder.FILE)
idx = ladder._lean_index(ROOT)
rules, skipped = ladder.emitted(data, idx)
facts, local, fskipped = ladder.emitted_facts(data, idx, rules)
print("rules", len(rules), "skipped", len(skipped), "facts", len(facts), "local", len(local),
      "fskipped", len(fskipped))
for name, text in (("Rules.lean", ladder.emit_lean(data, idx)), ("Test.lean", ladder.emit_test(data, idx))):
    cur = open(f"{ROOT}/Causal/Ladder/{name}", encoding="utf-8").read()
    d = list(difflib.unified_diff(cur.splitlines(), text.splitlines(), "on disk", "emit-lean now",
                                  lineterm="", n=0))
    print("---", name, "identical:", cur == text, "diff lines:", len(d))
    for l in d:
        print(l)
