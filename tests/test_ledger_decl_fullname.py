#!/usr/bin/env python3
"""A curated decl resolves by its full name only (T-ledger-decl-fullname).

`decl_line` used to match the last name component, with any dotted prefix and a dot allowed after:
`BTZAxioms.K_neq_I` passed against `theorem K_neq_I` of namespace `Causal.E0`, and
`Sphere.IsConvexPart` against `def IsConvexPart.cone`."""
import os
import sys
import unittest

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(ROOT, "tools"))
import ledger  # noqa: E402

SRC = """import Mathlib

/-! A module docstring that mentions
end
namespace Fake
theorem fake_in_doc : True := trivial
-/

namespace Causal.E0

theorem K_neq_I : True := trivial  -- end

section Inner
variable (x : Nat)

@[simp] protected lemma inner_lemma : True := trivial

end Inner

noncomputable section

def withUniverse.{u} (α : Type u) : Type u := α

theorem _root_.rootLevel : True := trivial

end

def str : String := "namespace Bogus
end"

theorem ι₁_name' : True := trivial

end Causal.E0

namespace Sphere

def IsConvexPart.cone : Nat := 0

structure Pocket (n : Nat) where
  carrier : Nat
  /-- a field with a docstring -/
  mem_of_segment (k : Nat) : k = k

structure Renamed where
  mkR ::
  val : Nat

inductive Shape
| dot : Shape
  | seg (n : Nat) : Shape

end Sphere

mutual
def evenM : Nat → Bool
  | 0 => true
  | n + 1 => oddM n
def oddM : Nat → Bool
  | 0 => false
  | n + 1 => evenM n
end

theorem after_mutual : True := trivial
"""


class DeclFullName(unittest.TestCase):
    def setUp(self):
        self.names = ledger.declared_names(SRC)

    def test_namespaces_and_sections(self):
        for n in ("Causal.E0.K_neq_I", "Causal.E0.inner_lemma", "Causal.E0.withUniverse",
                  "Causal.E0.str", "Causal.E0.ι₁_name'", "rootLevel", "Sphere.IsConvexPart.cone",
                  "evenM", "oddM", "after_mutual"):
            self.assertIn(n, self.names, n)

    def test_structures_and_inductives(self):
        for n in ("Sphere.Pocket", "Sphere.Pocket.carrier", "Sphere.Pocket.mem_of_segment",
                  "Sphere.Pocket.mk", "Sphere.Renamed.mkR", "Sphere.Renamed.val",
                  "Sphere.Shape.dot", "Sphere.Shape.seg"):
            self.assertIn(n, self.names, n)
        self.assertNotIn("Sphere.Renamed.mk", self.names)

    def test_no_false_resolution(self):
        # same last component, another namespace; a dotted extension; text inside comments and
        # strings; a universe binder kept in the name
        for n in ("Causal.Causality.BTZAxioms.K_neq_I", "K_neq_I", "Sphere.IsConvexPart",
                  "Fake.fake_in_doc", "Causal.E0.Bogus", "Causal.E0.withUniverse.{u}",
                  "Causal.E0.rootLevel", "Causal.E0.Inner.inner_lemma"):
            self.assertNotIn(n, self.names, n)

    def test_decl_line(self):
        src = {"A.lean": SRC}
        f, ln = ledger.decl_line(src, ["A.lean"], "Causal.E0.K_neq_I")
        self.assertEqual(f, "A.lean")
        self.assertEqual(SRC.split("\n")[ln - 1].split()[1], "K_neq_I")
        self.assertEqual(ledger.decl_line(src, ["A.lean"], "Other.K_neq_I"), (None, None))
        self.assertEqual(ledger.decl_line(src, ["B.lean"], "Causal.E0.K_neq_I"), (None, None))

    def test_comment_stripping_keeps_lines(self):
        s = ledger.strip_lean_comments(SRC)
        self.assertEqual(s.count("\n"), SRC.count("\n"))
        self.assertNotIn("fake_in_doc", s)


if __name__ == "__main__":
    unittest.main()
