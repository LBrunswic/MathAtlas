"""Shared sympy machinery for the cocycle-combine approach.

Everything is built on the polynomial sum functional of `cycle-gcd/periodic-words.md`:
for a gap word w = (d_0,...,d_{n-1}) of positive integers,

    S(w) = sum_{k=0}^{n-1} X^{e_k} Y^{n-1-k},      e_0 = 0, e_k = sum_{i<k} d_i
    D(w) = X^{|w|} - Y^{n}                          (|w| = sum d_i,  n = len w)

Specializing (X,Y) -> (2,3) recovers the integer rotation sums S^{(j)} and
D = 2^E - 3^o of the cycle-gcd program, where on a genuine cycle
gcd_j S^{(j)} = |D| exactly.

The whole approach hunts for Z[X,Y]-linear combinations of the cyclic rotations
of a word whose sum *compensates* down to a small / q-free core C. Because the
shift-gcd G = gcd_j S^{(j)} divides every such combination and (on a cycle) G is
odd and equals |D|, any compensation C with C != 0 yields the a-priori ceiling
G | C, hence |2^E - 3^o| <= |C| -- finitely many words in the family.

This module is the trusted kernel: combinator agents import it, build a candidate
combination on top, and call `verify_*` to certify it. Keep it dependency-light
(sympy only) and never put approach-specific guesswork here.
"""

from __future__ import annotations

from math import gcd
from functools import reduce
import sympy as sp

# Canonical indeterminates. X tracks gap-sums (-> 2), Y tracks positions (-> 3).
X, Y = sp.symbols("X Y")


# --------------------------------------------------------------------------- #
# Core functionals                                                            #
# --------------------------------------------------------------------------- #
def partial_sums(word):
    """e_0..e_{n-1}: e_k = sum_{i<k} d_i (e_0 = 0)."""
    e, acc = [], 0
    for d in word:
        e.append(acc)
        acc += d
    return e


def S(word, x=X, y=Y):
    """Polynomial sum functional S(word) in Z[X,Y] (or evaluated at x,y)."""
    n = len(word)
    e = partial_sums(word)
    return sum((x ** e[k]) * (y ** (n - 1 - k)) for k in range(n))


def D(word, x=X, y=Y):
    """D(word) = X^{|word|} - Y^{len word}."""
    return x ** sum(word) - y ** len(word)


def rotate(word, j):
    """Left cyclic rotation of `word` by j letters."""
    j %= len(word)
    return tuple(word[j:]) + tuple(word[:j])


def rotations(word):
    """All len(word) left rotations, j = 0 .. n-1 (rotation index = letters)."""
    return [rotate(word, j) for j in range(len(word))]


def S_rot(word, j, x=X, y=Y):
    """The j-th rotation sum S^{(j)} = S(rotate(word, j))."""
    return S(rotate(word, j), x, y)


# --------------------------------------------------------------------------- #
# Integer layer (X,Y) = (2,3)                                                 #
# --------------------------------------------------------------------------- #
def S_int(word, base2=2, base3=3):
    return int(S(word, base2, base3))


def D_int(word, base2=2, base3=3):
    return int(D(word, base2, base3))


def gcd_rotations(word, base2=2, base3=3):
    """gcd over all cyclic rotations of S, at (2,3). On a cycle this equals |D|."""
    vals = [int(S(r, base2, base3)) for r in rotations(word)]
    return reduce(gcd, (abs(v) for v in vals))


# --------------------------------------------------------------------------- #
# Cocycle identities (the compensation primitives)                            #
# --------------------------------------------------------------------------- #
def cocycle_check(u, v):
    """Concatenation cocycle  S(uv) = Y^{len v} S(u) + X^{|u|} S(v).  Returns 0."""
    lhs = S(tuple(u) + tuple(v))
    rhs = Y ** len(v) * S(u) + X ** sum(u) * S(v)
    return sp.expand(lhs - rhs)


def antisymmetry_check(u, v):
    """Rotation antisymmetry  S(uv) - S(vu) = D(u)S(v) - D(v)S(u).  Returns 0."""
    lhs = S(tuple(u) + tuple(v)) - S(tuple(v) + tuple(u))
    rhs = D(u) * S(v) - D(v) * S(u)
    return sp.expand(lhs - rhs)


def core_C(w, wp):
    """C(w,w') = S(ww') - S(w'w) = D(w)S(w') - D(w')S(w)  (the prototype core)."""
    return sp.expand(D(w) * S(wp) - D(wp) * S(w))


# --------------------------------------------------------------------------- #
# The compensation certifier -- the function combinators must call            #
# --------------------------------------------------------------------------- #
def verify_symbolic_identity(combination_expr, target_expr):
    """Certify a polynomial identity  combination == target  in Z[X,Y].

    `combination_expr` is the candidate Z[X,Y]-linear combination of rotation
    sums (built with S_rot / S and integer-or-monomial coefficients); `target_expr`
    is the claimed compensated core C. Returns True iff they are equal as
    polynomials (the difference expands/simplifies to 0).
    """
    diff = sp.simplify(sp.expand(combination_expr - target_expr))
    return diff == 0


def verify_divisibility_battery(instances, core_fn, base2=2, base3=3):
    """Numeric safety net at (2,3).

    `instances` is an iterable of concrete words (e.g. the pattern unrolled over
    a range of parameters). `core_fn(word) -> int` returns the claimed core C for
    that word. For each instance we check the necessary cycle condition
        gcd_j S^{(j)}  divides  C.
    Returns (ok, failures) where failures lists (word, G, C) that violate it.
    A passing battery is necessary, not sufficient -- the symbolic identity is the
    real proof; this catches sign/indexing mistakes fast.
    """
    failures = []
    for word in instances:
        G = gcd_rotations(word, base2, base3)
        C = int(core_fn(word))
        if C == 0:
            # degenerate locus: ceiling is vacuous, nothing to check
            continue
        if C % G != 0:
            failures.append((word, G, C))
    return (len(failures) == 0, failures)


if __name__ == "__main__":
    # Self-test against the known periodic-words results.
    assert cocycle_check((1, 2), (3,)) == 0
    assert antisymmetry_check((1, 2), (3,)) == 0
    # C((1,2),(3)) = -26 at (2,3); -5->-7 cycle word (1,2): gcd of rotations = 1 = |D|.
    assert int(core_C((1, 2), (3,)).subs({X: 2, Y: 3})) == -26
    assert gcd_rotations((1, 2)) == 1 and D_int((1, 2)) == -1
    assert gcd_rotations((2,)) == 1 and D_int((2,)) == 1  # trivial 1->1 cycle
    print("cocycle.py self-test OK")
