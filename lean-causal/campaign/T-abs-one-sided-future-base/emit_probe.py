# In-memory emit-lean dry run (T-abs-one-sided-future-base): ladder.emit_lean / emit_test from HEAD's sources
# (extract them first: git archive HEAD lean-causal/Causal | tar -x -C /tmp/osfb/headsrc) and from the
# working tree, compared with each other and with the files on disk. Writes nothing. Run: python3 -I emit_probe.py
import sys
sys.path.insert(0, "/home/maxbrain/Dropbox/LeanArticles/tools")
import ladder
data = ladder.load(ladder.FILE)
res = {}
for tag, root in (("head", "/tmp/osfb/headsrc/lean-causal"), ("now", "/home/maxbrain/Dropbox/LeanArticles/lean-causal")):
    idx = ladder._lean_index(root)
    rules, skipped = ladder.emitted(data, idx)
    facts, local, fskipped = ladder.emitted_facts(data, idx, rules)
    res[tag] = dict(rules=rules, skipped=skipped, facts=facts, local=local, fskipped=fskipped,
                    text=ladder.emit_lean(data, idx), test=ladder.emit_test(data, idx))
    print(tag, "rules", len(rules), "skipped", len(skipped), "facts", len(facts), "local", len(local), "fskipped", len(fskipped))
a, b = res["head"], res["now"]
print("Rules.lean text identical:", a["text"] == b["text"]); print("Test.lean text identical:", a["test"] == b["test"])
cur = open("/home/maxbrain/Dropbox/LeanArticles/lean-causal/Causal/Ladder/Rules.lean", encoding="utf-8").read()
curt = open("/home/maxbrain/Dropbox/LeanArticles/lean-causal/Causal/Ladder/Test.lean", encoding="utf-8").read()
print("on-disk Rules == head emit:", cur == a["text"], "; == now emit:", cur == b["text"])
print("on-disk Test == head emit:", curt == a["test"], "; == now emit:", curt == b["test"])
import difflib
for name in ("text", "test"):
    d = list(difflib.unified_diff(a[name].splitlines(), b[name].splitlines(), lineterm="", n=0))
    print("---", name, "diff lines", len(d))
    for l in d[:80]: print(l)
