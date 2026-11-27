"""Exact computation of N_n = max ||m^{-1} e||^2 over nonsingular n x n sign matrices m.

Then dMat(n) = 1/sqrt(N_n). Integer arithmetic only (fraction-free Gaussian elimination),
standard library only.

Reductions used (each preserves ||m^{-1} e||):
  * permuting the rows of m;
  * flipping the sign of a column of m (m -> m D with D = diag(+-1), so m^{-1} e -> D m^{-1} e).
Flipping columns makes the first row all ones, and the rows are then an unordered set of
n distinct vectors containing (1,...,1). So it suffices to scan all (n-1)-subsets of the other
2^n - 1 sign vectors: C(2^n - 1, n - 1) systems (7,028,847 for n = 6).

For each subset we solve m w = e exactly: Bareiss elimination on [m | e] returns det m and the
integer vector v = det(m) * w (Cramer), and we check m v = det(m) e in integers before using it.
N = |v|^2 / det^2 is kept as an exact fraction.

Usage: python scripts/matrix_side.py [nmax=6] [workers=8]
"""
import itertools
import sys
from fractions import Fraction
from multiprocessing import Pool


def sign_vectors(n):
    return [tuple(1 - 2 * ((k >> i) & 1) for i in range(n)) for k in range(2 ** n)]


def solve(rows):
    """Return (det, v) with m v = det * e, v integer, or (0, None) if m is singular."""
    n = len(rows)
    a = [list(r) + [1] for r in rows]
    prev = 1
    sign = 1
    for k in range(n):
        p = next((i for i in range(k, n) if a[i][k] != 0), None)
        if p is None:
            return 0, None
        if p != k:
            a[k], a[p] = a[p], a[k]
            sign = -sign
        akk = a[k][k]
        for i in range(k + 1, n):
            aik = a[i][k]
            row_i, row_k = a[i], a[k]
            for j in range(k + 1, n + 1):
                row_i[j] = (row_i[j] * akk - aik * row_k[j]) // prev
            row_i[k] = 0
        prev = akk
    det_u = a[n - 1][n - 1]  # determinant of the row-swapped matrix
    # back substitution in exact fractions, scaled to integers
    x = [Fraction(0)] * n
    for i in range(n - 1, -1, -1):
        s = Fraction(a[i][n]) - sum(a[i][j] * x[j] for j in range(i + 1, n))
        x[i] = s / a[i][i]
    det = sign * det_u
    v = [xi * det for xi in x]
    assert all(vi.denominator == 1 for vi in v)
    v = [int(vi) for vi in v]
    for r in rows:  # exact certificate: m v = det e
        assert sum(ri * vi for ri, vi in zip(r, v)) == det
    return det, v


def scan_chunk(args):
    n, first_indices = args
    vecs = sign_vectors(n)
    ones = vecs[0]
    others = vecs[1:]
    best = Fraction(-1)
    best_rows = None
    nonsing = 0
    for i0 in first_indices:
        for rest in itertools.combinations(range(i0 + 1, len(others)), n - 2):
            rows = [ones, others[i0]] + [others[j] for j in rest]
            det, v = solve(rows)
            if det == 0:
                continue
            nonsing += 1
            N = Fraction(sum(vi * vi for vi in v), det * det)
            if N > best:
                best, best_rows = N, rows
    return best, best_rows, nonsing


def max_N(n, workers):
    if n == 1:
        return Fraction(1), [(1,)], 1
    others = 2 ** n - 1
    starts = list(range(others))
    chunks = [(n, starts[w::workers]) for w in range(workers)]
    with Pool(workers) as pool:
        res = pool.map(scan_chunk, chunks)
    best = max(r[0] for r in res)
    rows = next(r[1] for r in res if r[0] == best)
    return best, rows, sum(r[2] for r in res)


def main():
    nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    workers = int(sys.argv[2]) if len(sys.argv) > 2 else 8
    print("n | nonsingular sets scanned | N_n = max |m^-1 e|^2 | bound (n+1)^n/4^(n-1) - 1 | N_n <= bound | equality")
    for n in range(1, nmax + 1):
        N, rows, count = max_N(n, workers)
        bound = Fraction((n + 1) ** n, 4 ** (n - 1)) - 1
        print(f"{n} | {count} | {N} | {bound} | {N <= bound} | {N == bound}")
        print(f"    a maximizing matrix (rows): {rows}")
        det, v = solve(rows)
        print(f"    det = {det}, det * m^-1 e = {v}")
        assert N <= bound


if __name__ == "__main__":
    main()
