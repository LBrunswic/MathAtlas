from __future__ import annotations
import sympy as sp
from typing import Sequence, Union

class CollatzWord:
    """A word in the free monoid {0, 1}* dedicated to Collatz dynamics."""
    
    def __init__(self, bits: Union[str, Sequence[int]], a=sp.Integer(3), b=sp.Integer(1), s0=sp.Integer(1)):
        if isinstance(bits, str):
            self.bits = tuple(int(bit) for bit in bits)
        else:
            self.bits = tuple(bits)
        
        if not all(bit in (0, 1) for bit in self.bits):
            raise ValueError("Bits must be 0 or 1")
        
        self.a = a if isinstance(a, sp.Basic) else sp.Integer(a)
        self.b = b if isinstance(b, sp.Basic) else sp.Integer(b)
        self.s0 = s0 if isinstance(s0, sp.Basic) else sp.Integer(s0)

    def __repr__(self):
        return "".join(map(str, self.bits))

    def __len__(self):
        return len(self.bits)

    def __add__(self, other: CollatzWord) -> CollatzWord:
        if self.a != other.a or self.b != other.b or self.s0 != other.s0:
            raise ValueError("Cannot concatenate words with different parameters a, b, s0")
        return CollatzWord(self.bits + other.bits, a=self.a, b=self.b, s0=self.s0)

    def chi_bit(self, bit: int):
        """Character on bits: chi(0) = 1/2, chi(1) = a."""
        if bit == 0:
            return sp.Rational(1, 2)
        if bit == 1:
            return self.a
        raise ValueError("Bit must be 0 or 1")

    def chi(self):
        """Character on words: chi(w) = product of chi(bits)."""
        res = sp.Integer(1)
        for bit in self.bits:
            res *= self.chi_bit(bit)
        return res

    def s_bit(self, bit: int):
        """The chi-cocycle S on bits: S(0) = s0, S(1) = b."""
        if bit == 0:
            return self.s0
        if bit == 1:
            return self.b
        raise ValueError("Bit must be 0 or 1")

    def S(self):
        """
        The chi-cocycle S satisfying S(0) = s0, S(1) = b and the cocycle property:
        S(uv) = chi(v)S(u) + S(v)
        """
        res = sp.Integer(0)
        # Process from left to right: T(x, wb) = chi(b)T(x, w) + S(b)
        # = chi(b)(chi(w)x + S(w)) + S(b) = chi(wb)x + (chi(b)S(w) + S(b))
        for bit in self.bits:
            res = self.chi_bit(bit) * res + self.s_bit(bit)
        return res

    def T(self, x):
        """
        The Collatz map T(x, w).
        Calculated as T(x, w) = chi(w)x + S(w).
        """
        return self.chi() * x + self.S()

    def diophantine(self, x=sp.Symbol('x')):
        """The Diophantine equation y = chi(w)x + S(w)."""
        return self.T(x)

    def solve_cycle(self):
        """Solve T(x, w) = x for x."""
        x = sp.Symbol('x')
        eq = sp.Eq(self.T(x), x)
        return sp.solve(eq, x)

    def get_cocycle_stats(self):
        """Returns statistics of the cocycle S(w)."""
        # This is a placeholder for actual statistical study
        # In a real study, we might look at the growth of S(w)
        # or its distribution for words of a certain length.
        return {
            "chi": self.chi(),
            "S": self.S(),
            "length": len(self),
            "num_ones": sum(self.bits)
        }

def verify():
    # 1. Basic numerical tests
    w0 = CollatzWord("0")
    w1 = CollatzWord("1")
    
    assert w0.chi() == sp.Rational(1, 2)
    assert w1.chi() == 3
    assert w0.S() == 1
    assert w1.S() == 1
    
    assert w0.T(10) == 6  # 0.5 * 10 + 1
    assert w1.T(7) == 22  # 3 * 7 + 1
    
    # 2. Cocycle property: S(uv) = chi(v)S(u) + S(v)
    u = CollatzWord("10")
    v = CollatzWord("110")
    uv = u + v
    assert uv.S() == v.chi() * u.S() + v.S()
    print("Cocycle property verified.")

    # 3. Formal computation with sympy Symbols
    x = sp.Symbol('x')
    w = CollatzWord("101")
    expr = w.T(x)
    print(f"Formal T(x, 101) = {expr}")
    # chi(101) = chi(1)*chi(0)*chi(1) = 3 * 1/2 * 3 = 9/2
    # S(1) = 1
    # S(10) = chi(0)S(1) + S(0) = 1/2 * 1 + 1 = 3/2
    # S(101) = chi(1)S(10) + S(1) = 3 * 3/2 + 1 = 9/2 + 1 = 11/2
    # T(x, 101) = 9/2 * x + 11/2
    assert expr == sp.Rational(9, 2) * x + sp.Rational(11, 2)

    # 4. Verify T(x, uv) = T(T(x, u), v) formally
    u_word = CollatzWord("1")
    v_word = CollatzWord("0")
    uv_word = u_word + v_word
    
    lhs = uv_word.T(x)
    rhs = v_word.T(u_word.T(x))
    print(f"LHS T(x, 10) = {lhs}")
    print(f"RHS T(T(x, 1), 0) = {rhs}")
    assert sp.simplify(lhs - rhs) == 0
    print("Composition property T(x, uv) = T(T(x, u), v) verified formally.")

    # 5. Symbolic parameters a, b, s0
    a, b, s0 = sp.symbols('a b s0')
    ws = CollatzWord("110", a=a, b=b, s0=s0)
    print(f"Symbolic chi(110) = {ws.chi()}")
    assert ws.chi() == a**2 / 2
    print(f"Symbolic S(110) = {ws.S()}")
    # S(1) = b
    # S(11) = chi(1)S(1) + S(1) = a*b + b
    # S(110) = chi(0)S(11) + S(0) = 1/2*(a*b + b) + s0
    assert sp.simplify(ws.S() - (a*b/2 + b/2 + s0)) == 0
    
    # 6. Cycle solving
    w_cycle = CollatzWord("01") # T(x, 01) = T(T(x,0), 1) = T(x/2+1, 1) = 3(x/2+1)+1 = 3x/2 + 4
    # 3x/2 + 4 = x => x/2 = -4 => x = -8
    sol = w_cycle.solve_cycle()
    print(f"Cycle solution for '01': {sol}")
    assert sol[0] == -8

if __name__ == "__main__":
    verify()
    print("All verifications passed!")
