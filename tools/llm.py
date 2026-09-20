#!/usr/bin/env python3
"""The LLM backend: Claude Opus through the `claude` CLI, recorded so a test never calls a model.

    python3 tools/llm.py ask --task smoke --prompt 'Reply {"ok": true}.' --schema '{...}'
    python3 tools/llm.py cassettes          # what has been recorded, with its cost
    python3 tools/llm.py verify             # every cassette replays and validates; exit 1 if not

A model is asked *one* question at a time, with a JSON schema it must answer in
(`--json-schema`, enforced by the CLI), and every exchange is written to a **cassette**: the
task, the model, the prompt, the schema, the answer, the cost and the date, in
`tools/cassettes/<task>/<sha8>.json`. Cassettes are committed. So:

  * a test replays the recorded answer and never spends a cent or needs a network;
  * a reviewer reads what was asked and what came back, beside the code that asked it;
  * re-running with `LEANARTICLES_LLM=live` re-asks, and the diff of the cassette is the drift.

`LEANARTICLES_LLM` selects the mode:

    cassette   (default) replay only; a miss is an error. This is what tests run under.
    live       replay a hit, ask on a miss and record it.
    refresh    ask every time and overwrite the cassette.
    off        every ask raises. For proving that a gate calls no model.

**No gate calls a model** (`tests/test_no_model_in_gates.py` asserts it). A model proposes;
the author disposes. An answer that fails its schema, or the caller's `validate` hook -- which is
how "the model named a declaration that does not exist" is caught -- is *refused*: recorded as a
refusal, never returned as an answer.
"""
import argparse
import datetime
import hashlib
import json
import os
import subprocess
import sys

ROOT = os.environ.get("LEANARTICLES_ROOT") or os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
CASSETTES = os.path.join(ROOT, "tools", "cassettes")
MODEL = os.environ.get("LEANARTICLES_MODEL", "claude-opus-5")
CMD = os.environ.get("LEANARTICLES_LLM_CMD", "claude -p --allowed-tools ''")
TIMEOUT = int(os.environ.get("LEANARTICLES_LLM_TIMEOUT", "300"))
MODES = ("cassette", "live", "refresh", "off")


class Refused(Exception):
    """The answer may not be used: no answer, a malformed one, or one the validator rejected."""


def mode():
    m = os.environ.get("LEANARTICLES_LLM", "cassette")
    if m not in MODES:
        raise Refused("LEANARTICLES_LLM=%r is not one of %s" % (m, ", ".join(MODES)))
    return m


def key(task, prompt, schema, model):
    """The cassette's identity: change any of these and it is a different question."""
    blob = "\0".join([model, task, prompt, json.dumps(schema, sort_keys=True) if schema else ""])
    return hashlib.sha256(blob.encode("utf-8")).hexdigest()


def path_for(task, k):
    return os.path.join(CASSETTES, task, k[:8] + ".json")


def load_cassette(task, k):
    p = path_for(task, k)
    if not os.path.exists(p):
        return None
    c = json.load(open(p, encoding="utf-8"))
    return c if c.get("key") == k else None


def save_cassette(task, k, rec):
    p = path_for(task, k)
    os.makedirs(os.path.dirname(p), exist_ok=True)
    with open(p, "w", encoding="utf-8") as fh:
        json.dump(rec, fh, indent=2, ensure_ascii=False, sort_keys=False)
        fh.write("\n")
    return p


def call_model(prompt, schema, model):
    """One CLI call. Returns (answer_text, meta). Raises Refused on anything unusable."""
    import shlex
    cmd = shlex.split(CMD) + ["--model", model, "--output-format", "json"]
    if schema is not None:
        cmd += ["--json-schema", json.dumps(schema)]
    try:
        r = subprocess.run(cmd, input=prompt, capture_output=True, text=True, timeout=TIMEOUT)
    except subprocess.TimeoutExpired:
        raise Refused("the model did not answer within %d s" % TIMEOUT)
    if r.returncode != 0:
        raise Refused("the CLI exited %d: %s" % (r.returncode, (r.stderr or r.stdout)[:400]))
    try:
        env = json.loads(r.stdout)
    except json.JSONDecodeError:
        raise Refused("the CLI did not return JSON: %s" % r.stdout[:400])
    if env.get("is_error"):
        raise Refused("the CLI reported an error: %s" % str(env.get("result"))[:400])
    text = env.get("result")
    if not isinstance(text, str) or not text.strip():
        raise Refused("the model returned no text")
    meta = {"cost_usd": env.get("total_cost_usd"), "duration_ms": env.get("duration_ms"),
            "stop_reason": env.get("stop_reason"), "num_turns": env.get("num_turns")}
    return text, meta


def parse(text, schema):
    """The answer as a dict when a schema was asked for, else the raw text."""
    if schema is None:
        return text
    t = text.strip()
    if t.startswith("```"):                       # a fenced block, when the CLI relays one
        t = t.split("\n", 1)[1].rsplit("```", 1)[0] if "\n" in t else t
    try:
        return json.loads(t)
    except json.JSONDecodeError:
        start, end = t.find("{"), t.rfind("}")
        if start != -1 and end > start:
            try:
                return json.loads(t[start:end + 1])
            except json.JSONDecodeError:
                pass
        raise Refused("the answer is not JSON: %s" % t[:300])


def ask(task, prompt, schema=None, validate=None, model=None, note=None):
    """Ask one question. Returns the parsed answer. Raises Refused rather than returning a bad one.

    `validate(answer)` returns None to accept, or a string saying why the answer is unusable --
    the hook that refuses an answer naming a label or a declaration that does not exist.
    """
    model = model or MODEL
    m = mode()
    if m == "off":
        raise Refused("LEANARTICLES_LLM=off: this code path must not call a model")
    k = key(task, prompt, schema, model)
    rec = load_cassette(task, k) if m in ("cassette", "live") else None
    if rec is None:
        if m == "cassette":
            raise Refused("no cassette for %s/%s — record it with LEANARTICLES_LLM=live" % (task, k[:8]))
        text, meta = call_model(prompt, schema, model)
        rec = {"key": k, "task": task, "model": model, "recorded": datetime.date.today().isoformat(),
               "note": note, "prompt": prompt, "schema": schema, "answer": text, **meta}
        save_cassette(task, k, rec)
    # A refusal is a property of (answer, validator), not of the cassette: re-validate the
    # recorded answer every time, so that fixing a validator that was too strict clears the
    # refusal without asking the model again, and loosening one that was too lax raises it.
    answer = parse(rec["answer"], schema)
    why = validate(answer) if validate else None
    if why != rec.get("refused"):
        rec = dict(rec)
        if why:
            rec["refused"] = why
        else:
            rec.pop("refused", None)
        save_cassette(task, k, rec)
    if why:
        raise Refused(why)
    return answer


# --------------------------------------------------------------------------- cli --
def cmd_ask(a):
    schema = json.loads(a.schema) if a.schema else None
    try:
        print(json.dumps(ask(a.task, a.prompt, schema, note=a.note), indent=2, ensure_ascii=False)
              if schema else ask(a.task, a.prompt))
    except Refused as e:
        print("refused: %s" % e)
        return 1
    return 0


def all_cassettes():
    for task in sorted(os.listdir(CASSETTES)) if os.path.isdir(CASSETTES) else []:
        d = os.path.join(CASSETTES, task)
        if not os.path.isdir(d):
            continue
        for f in sorted(os.listdir(d)):
            if f.endswith(".json"):
                yield task, os.path.join(d, f)


def cmd_cassettes(_a):
    total, n = 0.0, 0
    for task, p in all_cassettes():
        c = json.load(open(p, encoding="utf-8"))
        cost = c.get("cost_usd") or 0.0
        total += cost
        n += 1
        print("%-22s %-10s %6.3f USD  %s%s" % (task, c["key"][:8], cost, c.get("note") or "",
                                               "  REFUSED: " + c["refused"] if c.get("refused") else ""))
    print("%d cassettes, %.3f USD recorded" % (n, total))
    return 0


def cmd_verify(_a):
    """Every cassette is well formed, keyed by its own contents, and replays."""
    bad = 0
    n = 0
    for task, p in all_cassettes():
        c = json.load(open(p, encoding="utf-8"))
        n += 1
        for f in ("key", "task", "model", "prompt", "answer", "recorded"):
            if f not in c:
                print("verify: FAIL %s lacks %r" % (p, f))
                bad += 1
        if c.get("task") != task:
            print("verify: FAIL %s says task %r but lives under %r" % (p, c.get("task"), task))
            bad += 1
        k = key(c["task"], c["prompt"], c.get("schema"), c["model"])
        if k != c.get("key"):
            print("verify: FAIL %s: key does not match its prompt/schema/model (edited by hand?)" % p)
            bad += 1
        elif os.path.basename(p) != k[:8] + ".json":
            print("verify: FAIL %s: filename is not the key" % p)
            bad += 1
        if not c.get("refused") and c.get("schema"):
            try:
                parse(c["answer"], c["schema"])
            except Refused as e:
                print("verify: FAIL %s: %s" % (p, e))
                bad += 1
    if bad:
        return 1
    print("verify: %d cassettes replay" % n)
    return 0


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    sub = ap.add_subparsers(dest="cmd")
    a = sub.add_parser("ask")
    a.add_argument("--task", required=True)
    a.add_argument("--prompt", required=True)
    a.add_argument("--schema")
    a.add_argument("--note")
    a.set_defaults(fn=cmd_ask)
    sub.add_parser("cassettes").set_defaults(fn=cmd_cassettes)
    sub.add_parser("verify").set_defaults(fn=cmd_verify)
    args = ap.parse_args(argv)
    if not getattr(args, "fn", None):
        ap.print_help()
        return 2
    return args.fn(args)


if __name__ == "__main__":
    sys.exit(main())
