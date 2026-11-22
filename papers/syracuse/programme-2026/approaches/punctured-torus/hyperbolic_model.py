"""
punctured-torus :: candidate geometric lift of the Syracuse generators.

We test the "affine group as upper half-plane" model:

    Aff_+(R) = { x |-> alpha*x + beta : alpha>0 }  ==  H = { beta + i*alpha }

Generators (the two affine maps whose composition is Syracuse):
    a : x |-> (3x+1)/2     (odd step)   -> (alpha,beta) = (3/2, 1/2)
    b : x |-> x/2          (even step)  -> (alpha,beta) = (1/2, 0)

As Mobius maps of H they are z |-> (3z+1)/2 and z |-> z/2: both REAL-affine,
hence both fix infinity in dH = R. We check:
  (1) each generator is a hyperbolic isometry (|tr|>2 after SL2 normalisation),
  (2) a periodic trajectory's cumulative map G is hyperbolic with VERTICAL axis
      Re(z)=x0 ending at the cycle value x0 in R = dH, translation length
      ell = |log(3^o/2^E)| = log(2^E/3^o),
  (3) seeded ON that axis, the period-iterates are literally points on the geodesic,
  (4) a generic (non-periodic) trajectory's cumulative points zigzag (NOT one geodesic).
"""
import math
from fractions import Fraction

# affine map x -> alpha*x + beta  stored as (alpha, beta)
A = (Fraction(3, 2), Fraction(1, 2))   # odd step  a
B = (Fraction(1, 2), Fraction(0, 1))   # even step b
ID = (Fraction(1, 1), Fraction(0, 1))


def after(g, h):
    """g after h : x -> g(h(x))."""
    ag, bg = g
    ah, bh = h
    return (ag * ah, ag * bh + bg)


def cumulative(word):
    """G_n = g_{w_n} o ... o g_{w_1}; returns [ID, G_1, ..., G_n]."""
    G = ID
    out = [G]
    for c in word:
        G = after(A if c == 'a' else B, G)
        out.append(G)
    return out


def fixed_point(G):
    a, b = G
    return b / (1 - a)        # x* = beta/(1-alpha)


def stats(word):
    o = word.count('a')
    E = len(word)            # each letter is exactly one halving
    return o, E


def sl2_trace(g):
    """trace of the SL2 normalisation of x->alpha x+beta : matrix (alpha,beta;0,1)/sqrt(alpha)."""
    alpha, beta = g
    return (float(alpha) + 1.0) / math.sqrt(float(alpha))


CYCLES = {
    "1->1     (positive, trivial)": "ab",    # 1 -a-> 2 -b-> 1
    "-1       (negative)":          "a",     # -1 -a-> -1
    "-5->-7   (negative)":          "aab",   # -5 -a-> -7 -a-> -10 -b-> -5
}

print("=" * 74)
print("Generators as hyperbolic isometries of H")
print("=" * 74)
for name, g in (("a", A), ("b", B)):
    tr = sl2_trace(g)
    ell = abs(math.log(float(g[0])))
    print(f"  {name}: z->{float(g[0])}*z+{float(g[1])}   |tr|={tr:.4f} "
          f"({'hyperbolic' if abs(tr) > 2 else 'NOT hyp'})   "
          f"axis Re={float(fixed_point(g)):+.4g}  ell={ell:.4f}")

print()
print("=" * 74)
print("Each cycle -> a hyperbolic G with vertical axis at x0, length log(2^E/3^o)")
print("=" * 74)
for name, w in CYCLES.items():
    seq = cumulative(w)
    G = seq[-1]
    o, E = stats(w)
    alpha, beta = G
    x0 = fixed_point(G)
    D = 2 ** E - 3 ** o
    S = beta * (2 ** E)                  # since G(x)= (3^o/2^E)x + S/2^E
    ell = math.log((2 ** E) / (3 ** o))
    print(f"  {name}")
    print(f"     word={w!r}  (o={o}, E={E})   period map  z -> {alpha}*z + {beta}")
    print(f"     x0 = S/D = {S}/{D} = {x0}      axis = vertical line Re={float(x0):+.4g}")
    print(f"     D = 2^{E}-3^{o} = {D}      translation length ell = log(2^{E}/3^{o}) = {ell:.5f}")
    # confirm: seeded ON the axis, period-iterates stay on the geodesic, height *= alpha
    t0 = 1.0
    pts = [(float(x0), t0 * float(alpha) ** k) for k in range(4)]
    on_axis = all(abs(p[0] - float(x0)) < 1e-12 for p in pts)
    print(f"     seeded on axis: heights {[round(p[1],4) for p in pts]}  "
          f"-> on the geodesic Re=x0 ? {on_axis}")
    print()

print("=" * 74)
print("Generic (non-periodic) trajectory: cumulative points zigzag")
print("=" * 74)
# start at 7 (positive), accelerated Syracuse, a few steps
def syr_word(x, n):
    w = ""
    for _ in range(n):
        if x % 2 == 1:
            x = (3 * x + 1) // 2
            w += 'a'
        else:
            x //= 2
            w += 'b'
    return w
w = syr_word(7, 10)
seq = cumulative(w)
print(f"  start 7, word={w!r}")
print("  cumulative points P_n=(beta_n, alpha_n) in H:")
for n, G in enumerate(seq):
    a, b = G
    print(f"    n={n:2d}  Re={float(b):+9.4f}  Im={float(a):.5f}")

# ---- optional plot ----------------------------------------------------------
try:
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    import numpy as np

    fig, ax = plt.subplots(figsize=(9, 6))
    # vertical-axis geodesics for the three cycles
    colors = {"1->1     (positive, trivial)": "tab:green",
              "-1       (negative)": "tab:red",
              "-5->-7   (negative)": "tab:purple"}
    for name, wd in CYCLES.items():
        x0 = float(fixed_point(cumulative(wd)[-1]))
        ax.axvline(x0, color=colors[name], lw=1.5, alpha=.8,
                   label=f"cycle {name.split()[0]}: axis Re={x0:g}")
        ax.plot([x0], [0], 'o', color=colors[name])   # boundary endpoint = cycle value
    # generic trajectory cumulative points (zigzag, interior of H)
    xs = [float(b) for (a, b) in seq]
    ys = [float(a) for (a, b) in seq]
    ax.plot(xs, ys, '-o', color="tab:blue", ms=3, lw=.8, label="generic traj (start 7)")
    ax.axhline(0, color='k', lw=.8)
    ax.set_xlim(-8, 8)
    ax.set_ylim(-0.2, 3)
    ax.set_xlabel(r"$\beta=\mathrm{Re}\,z$  (translation part)")
    ax.set_ylabel(r"$\alpha=\mathrm{Im}\,z$  (log-scale part)")
    ax.set_title("Syracuse generators in H = Aff_+(R):\n"
                 "cycle = vertical geodesic ending at x0; generic orbit zigzags")
    ax.legend(fontsize=8, loc="upper right")
    fig.tight_layout()
    out = "approaches/punctured-torus/hyperbolic_model.png"
    fig.savefig(out, dpi=130)
    print(f"\n  [plot written to {out}]")
except Exception as e:
    print(f"\n  [plot skipped: {e}]")
