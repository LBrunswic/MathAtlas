#!/usr/bin/env python3
"""The tropical budget of an independent-block family (approaches/places-elimination/SCHEME.md §2.4).

A family W(a) = u_1^{a_1} x_1 ... u_k^{a_k} x_k with independent exponents has, for each block i, the
rotation core C(u_i, rest_i), and |D(W)| <= |C(u_i, rest_i)| on every cycle off the locus C = 0.
Archimedean heights: log|C(u_i, rest_i)| <= sum_{j != i} a_j g_j + O(log|a|), with g = log G,
G = max(2^{|u|}, 3^{len u}); log|D| >= max(sum a_j p_j, sum a_j q_j) - O(log|a|) by Matveev, where
p = |u| log 2 and q = len(u) log 3.

Finiteness off the loci follows when
    for all a >= 0, a != 0:   min_i sum_{j != i} a_j g_j  <  max(sum a_j p_j, sum a_j q_j).
By minimax this holds iff  min(A, B) < 1, where
    A = sum over blocks above log2 3 of (1 - q_j/p_j),
    B = sum over blocks below of (1 - p_j/q_j).

Blocks are given as words over the gap alphabet (letters >= 1). The pseudo-letter '0' is a T-parity
even step (|0| = 1, len 0), so that parity-vector families such as m-cycles can be entered.

Usage:  budget.py "1" "2" "1"          blocks of 1^a 2^b 1^c (spacers do not matter)
        budget.py --examples
"""
import sys, math

L2, L3 = math.log(2), math.log(3)


def pq(block):
    E = sum(1 if d == 0 else d for d in block)
    o = sum(0 if d == 0 else 1 for d in block)
    return E * L2, o * L3


def budget(blocks):
    A = B = 0.0
    for blk in blocks:
        p, q = pq(blk)
        if p > q: A += 1 - q / p
        else: B += 1 - p / q
    return A, B


def fmt(blocks):
    return ' '.join('(' + ','.join(map(str, b)) + ')' for b in blocks)


def report(blocks, label=None):
    A, B = budget(blocks)
    ok = min(A, B) < 1
    print(f'{label or fmt(blocks):38s} A = {A:.4f}  B = {B:.4f}  ->  '
          + ('settled off the loci (Matveev)' if ok else 'OUTSIDE the budget'))
    return ok


def examples():
    print('-- gap-word families --')
    for bl in ([[1], [2]], [[1], [3]], [[2], [1, 1]], [[1], [2], [1]], [[1], [2], [1], [2]],
               [[1], [1], [1], [2]], [[1], [3], [1], [3], [1], [3]], [[1], [2], [1], [2], [1], [2]],
               [[1], [4], [1], [4], [1]], [[1, 2], [3], [1, 2]]):
        report(bl)
    print('-- m-cycles: parity blocks 1^{k_i} 0^{l_i}, i = 1..m --')
    for m in range(1, 6):
        report([[1], [0]] * m, f'm = {m}')
    print('-- largest number of below-blocks [1] with every above-block [2] --')
    for nb in range(1, 5):
        for na in range(0, 7):
            if not min(budget([[1]] * nb + [[2]] * na)) < 1:
                print(f'  {nb} blocks (1), {na} blocks (2): first failure'); break
        else:
            print(f'  {nb} blocks (1): settled with up to 6 blocks (2)')


if __name__ == '__main__':
    if sys.argv[1:2] == ['--examples'] or len(sys.argv) == 1:
        examples()
    else:
        report([[int(c) for c in a.split(',')] for a in sys.argv[1:]])
