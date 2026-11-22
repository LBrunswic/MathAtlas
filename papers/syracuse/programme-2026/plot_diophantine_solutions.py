import os
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from itertools import combinations
from collatz_algebra import CollatzWord

# Parameters
K_zeros = 10
M_max = 10
OUT = "/home/maxbrain/Syracuse/approaches/diophantine-distribution/results"
os.makedirs(OUT, exist_ok=True)

def words_fixed_zeros(k, m):
    """Generate all words with k zeros and m ones."""
    # A word is a sequence of bits 0 and 1.
    # We can represent it by the indices of the ones.
    for ones_indices in combinations(range(k + m), m):
        bits = [0] * (k + m)
        for i in ones_indices:
            bits[i] = 1
        yield bits

def solve_canonical(word_bits, k):
    """
    Find the smallest positive integer x such that T(x, w) is an integer.
    Using S(0)=0, S(1)=1 for standard Collatz behavior in this context.
    """
    w = CollatzWord(word_bits, a=3, b=1, s0=0)
    # T(x, w) = (3^m / 2^k) * x + S(w)
    # 2^k * T(x, w) = 3^m * x + 2^k * S(w)
    # We want 3^m * x + 2^k * S(w) = 0 (mod 2^k)
    m = sum(word_bits)
    S_val = w.S()
    S_num = int(S_val * (2**k))
    
    # Solve 3^m * x + S_num = 0 (mod 2^k)
    # 3^m * x = -S_num (mod 2^k)
    inv3m = pow(3**m, -1, 2**k)
    x = (inv3m * (-S_num)) % (2**k)
    if x == 0: x = 2**k
    return x

def calculate_imbalance(bits, k, m):
    """Calculate imbalance p = max_k |e_k - (k_zeros/length) * i|."""
    # Here bits are 0 and 1.
    # Standard definition in RATIONALE.md uses gap-sums e_k.
    # For bits, e_k is the number of 0s before the i-th one.
    length = k + m
    zeros_count = 0
    ones_count = 0
    mean_zeros_per_one = k / m if m > 0 else 0
    p = 0.0
    for bit in bits:
        if bit == 0:
            zeros_count += 1
        else:
            ones_count += 1
            # Current zeros_count vs expected zeros_count
            dev = abs(zeros_count - mean_zeros_per_one * ones_count)
            if dev > p: p = dev
    return p

def main():
    print(f"Generating data for k={K_zeros} zeros, m up to {M_max} ones...")
    results = []
    
    for m in range(1, M_max + 1):
        print(f" Processing m={m} ones...")
        # Number of words is (k+m) choose m
        for bits in words_fixed_zeros(K_zeros, m):
            x = solve_canonical(bits, K_zeros)
            p = calculate_imbalance(bits, K_zeros, m)

            results.append({
                'm': m,
                'x': float(x),
                'p': p,
            })

    # Convert to numpy for plotting
    m_arr = np.array([r['m'] for r in results])
    x_arr = np.array([r['x'] for r in results])
    p_arr = np.array([r['p'] for r in results])

    # Plot: fundamental solution size versus number of ones
    plt.figure(figsize=(10, 6))
    plt.scatter(m_arr + np.random.normal(0, 0.1, len(m_arr)), x_arr, c=p_arr, s=5, alpha=0.5, cmap='viridis')
    plt.xlabel("Number of ones (m)")
    plt.ylabel(f"Fundamental solution size x (mod 2^{K_zeros})")
    plt.title(f"Fundamental solution size vs. number of ones for fixed k={K_zeros} zeros")
    plt.colorbar(label="Imbalance p")
    plt.savefig(os.path.join(OUT, f"diophantine_x_vs_m_k{K_zeros}.png"))
    plt.close()

    print(f"Plots saved to {OUT}")

if __name__ == "__main__":
    main()
