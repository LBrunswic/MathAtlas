#!/usr/bin/env python3
"""The model backend: recorded, replayable, and refusing rather than returning a bad answer.

Every test here runs with the CLI command set to something that fails if it is ever executed, so
a test that accidentally reaches for a model fails instead of spending money.
"""
import contextlib
import io
import json
import os
import shutil
import sys
import tempfile
import unittest

TOOLS = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "tools")
sys.path.insert(0, TOOLS)
import llm  # noqa: E402

SCHEMA = {"type": "object", "properties": {"verdict": {"type": "string"}},
          "required": ["verdict"], "additionalProperties": False}


class Base(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.mkdtemp()
        self.old_cassettes, llm.CASSETTES = llm.CASSETTES, self.tmp
        self.env = dict(os.environ)
        os.environ["LEANARTICLES_LLM"] = "cassette"
        # If anything calls out despite the mode, this command fails and the test fails with it.
        os.environ["LEANARTICLES_LLM_CMD"] = "false"

    def tearDown(self):
        llm.CASSETTES = self.old_cassettes
        shutil.rmtree(self.tmp)
        os.environ.clear()
        os.environ.update(self.env)

    def record(self, task="t", prompt="p", schema=SCHEMA, answer='{"verdict":"yes"}', **extra):
        k = llm.key(task, prompt, schema, llm.MODEL)
        rec = {"key": k, "task": task, "model": llm.MODEL, "recorded": "2026-09-20",
               "prompt": prompt, "schema": schema, "answer": answer, "cost_usd": 0.5}
        rec.update(extra)
        llm.save_cassette(task, k, rec)
        return k


class Keys(Base):
    def test_the_key_is_stable(self):
        a = llm.key("t", "p", SCHEMA, "m")
        self.assertEqual(a, llm.key("t", "p", SCHEMA, "m"))

    def test_every_input_is_part_of_the_identity(self):
        base = llm.key("t", "p", SCHEMA, "m")
        self.assertNotEqual(base, llm.key("t2", "p", SCHEMA, "m"))
        self.assertNotEqual(base, llm.key("t", "p2", SCHEMA, "m"))
        self.assertNotEqual(base, llm.key("t", "p", None, "m"))
        self.assertNotEqual(base, llm.key("t", "p", SCHEMA, "m2"),
                            "a different model must be a different cassette")


class Replay(Base):
    def test_a_recorded_answer_replays_without_a_model(self):
        self.record()
        self.assertEqual(llm.ask("t", "p", SCHEMA), {"verdict": "yes"})

    def test_a_miss_is_an_error_rather_than_a_silent_call(self):
        with self.assertRaises(llm.Refused) as e:
            llm.ask("t", "never recorded", SCHEMA)
        self.assertIn("no cassette", str(e.exception))

    def test_off_refuses_every_ask(self):
        self.record()
        os.environ["LEANARTICLES_LLM"] = "off"
        with self.assertRaises(llm.Refused) as e:
            llm.ask("t", "p", SCHEMA)
        self.assertIn("must not call a model", str(e.exception))

    def test_an_unknown_mode_is_refused(self):
        os.environ["LEANARTICLES_LLM"] = "sometimes"
        with self.assertRaises(llm.Refused):
            llm.ask("t", "p", SCHEMA)

    def test_a_cassette_whose_key_does_not_match_is_ignored(self):
        k = self.record()
        p = llm.path_for("t", k)
        with open(p) as fh:
            c = json.load(fh)
        c["prompt"] = "a different question"          # the file no longer answers its own key
        with open(p, "w") as fh:
            json.dump(c, fh)
        with self.assertRaises(llm.Refused):
            llm.ask("t", "a different question", SCHEMA)


class Validation(Base):
    def test_an_answer_the_validator_rejects_is_refused_and_recorded(self):
        k = self.record()
        with self.assertRaises(llm.Refused) as e:
            llm.ask("t", "p", SCHEMA, validate=lambda a: "invented a name")
        self.assertIn("invented a name", str(e.exception))
        with open(llm.path_for("t", k)) as fh:
            self.assertEqual(json.load(fh)["refused"], "invented a name")

    def test_fixing_a_validator_clears_the_refusal_without_asking_again(self):
        """A refusal belongs to (answer, validator), not to the recording."""
        k = self.record(refused="was too strict")
        self.assertEqual(llm.ask("t", "p", SCHEMA, validate=lambda a: None), {"verdict": "yes"})
        with open(llm.path_for("t", k)) as fh:
            self.assertNotIn("refused", json.load(fh))

    def test_a_malformed_answer_is_refused(self):
        self.record(answer="not json at all")
        with self.assertRaises(llm.Refused) as e:
            llm.ask("t", "p", SCHEMA)
        self.assertIn("not JSON", str(e.exception))

    def test_a_fenced_answer_still_parses(self):
        self.record(answer='```json\n{"verdict":"yes"}\n```')
        self.assertEqual(llm.ask("t", "p", SCHEMA), {"verdict": "yes"})

    def test_prose_around_the_object_still_parses(self):
        self.record(answer='Here you go: {"verdict":"yes"} — hope that helps.')
        self.assertEqual(llm.ask("t", "p", SCHEMA), {"verdict": "yes"})


class Verify(Base):
    @staticmethod
    def quiet(fn, *a):
        with contextlib.redirect_stdout(io.StringIO()) as out:
            rc = fn(*a)
        return rc, out.getvalue()

    def test_verify_passes_on_a_sound_cassette(self):
        self.record()
        self.assertEqual(self.quiet(llm.cmd_verify, None)[0], 0)

    def test_verify_catches_a_hand_edited_prompt(self):
        k = self.record()
        p = llm.path_for("t", k)
        with open(p) as fh:
            c = json.load(fh)
        c["prompt"] = "edited by hand"
        with open(p, "w") as fh:
            json.dump(c, fh)
        rc, said = self.quiet(llm.cmd_verify, None)
        self.assertEqual(rc, 1)
        self.assertIn("edited by hand", said)

    def test_verify_catches_an_answer_that_no_longer_parses(self):
        self.record(answer="{oops")
        rc, said = self.quiet(llm.cmd_verify, None)
        self.assertEqual(rc, 1)
        self.assertIn("not JSON", said)


class CommittedCassettes(unittest.TestCase):
    """The cassettes in the repository are sound, and nothing in them was edited by hand."""

    def test_every_committed_cassette_verifies(self):
        with contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(llm.cmd_verify(None), 0)

    def test_every_committed_cassette_names_the_model_it_was_asked_of(self):
        seen = 0
        for _task, p in llm.all_cassettes():
            with open(p, encoding="utf-8") as fh:
                c = json.load(fh)
            self.assertTrue(c.get("model"), p)
            seen += 1
        self.assertGreater(seen, 0, "no cassettes are committed, so nothing is pinned")


if __name__ == "__main__":
    unittest.main()
