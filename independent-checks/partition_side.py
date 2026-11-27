"""Independent check from the partition definition of d_n (no sign matrices are used).

For every partition of C_n = {-1,1}^n by a hyperplane through 0 that avoids C_n, with positive
half P, the optimized margin is 1/|u*|, where u* solves the convex QP

    minimize |u|^2  subject to  u . x >= 1 for all x in P.            (QP)

(For u feasible, u . x <= -1 on -P = C_n \\ P, so u induces the same partition and its margin is
min_P u.x / |u| >= 1/|u|; conversely any normal of the same partition can be scaled to be
feasible with min_P u.x = 1.) Hence 1/d_n^2 = max over partitions of |u*|^2.

How (QP) is solved: Wolfe's min-norm-point algorithm in floating point on P gives a candidate
support S. Then everything is redone in exact rationals: y = the min-norm point of aff(S),
y = sum alpha_s s with sum alpha_s = 1. We check exactly that alpha_s > 0, that y . s = |y|^2
on S, and that y . x >= |y|^2 for every x in P. Then u = y/|y|^2 satisfies the KKT conditions of
(QP) (feasible, u = sum (alpha_s/|y|^2) s with nonnegative multipliers, constraints active on S),
so it is optimal and |u*|^2 = 1/|y|^2. Floating point is only used to guess S.

Enumeration of partitions: the optimized margin is invariant under the signed permutations of
the coordinates (isometries of C_n), so it is enough to take one partition from each orbit. We
take all integer weight vectors 0 <= a_1 <= ... <= a_n <= W that avoid C_n, and check that the
orbits of the partitions found cover exactly A000609(n-1) partitions, the known number of
threshold functions of n-1 variables (OEIS A000609: 2, 4, 14, 104, 1882, 94572), which is in
bijection with the homogeneous threshold functions (= our partitions) of n variables. That
count check certifies that no orbit was missed.

Usage: python partition_side.py [nmax=6] [W=12]
"""
import itertools
import sys
from fractions import Fraction

A000609 = [2, 4, 14, 104, 1882, 94572, 15028134]


def cube(n):
    return [tuple(1 - 2 * ((k >> i) & 1) for i in range(n)) for k in range(2 ** n)]


def dot(a, b):
    return sum(x * y for x, y in zip(a, b))


def solve_lin(A, b, exact):
    """Gaussian elimination; A square. Returns x or None if singular."""
    n = len(A)
    M = [list(A[i]) + [b[i]] for i in range(n)]
    for k in range(n):
        if exact:
            p = next((i for i in range(k, n) if M[i][k] != 0), None)
        else:
            p = max(range(k, n), key=lambda i: abs(M[i][k]))
            if abs(M[p][k]) < 1e-12:
                p = None
        if p is None:
            return None
        M[k], M[p] = M[p], M[k]
        for i in range(k + 1, n):
            f = M[i][k] / M[k][k]
            for j in range(k, n + 1):
                M[i][j] -= f * M[k][j]
    x = [0] * n
    for i in range(n - 1, -1, -1):
        x[i] = (M[i][n] - sum(M[i][j] * x[j] for j in range(i + 1, n))) / M[i][i]
    return x


def affine_min_norm(S, exact):
    """Coefficients alpha (sum 1) of the min-norm point of aff(S)."""
    k = len(S)
    G = [[dot(S[i], S[j]) for j in range(k)] + [1] for i in range(k)]
    G.append([1] * k + [0])
    zero, one = (Fraction(0), Fraction(1)) if exact else (0.0, 1.0)
    if exact:
        G = [[Fraction(v) for v in row] for row in G]
    sol = solve_lin(G, [zero] * k + [one], exact)
    return None if sol is None else sol[:k]


def combo(S, w):
    n = len(S[0])
    return [sum(w[i] * S[i][j] for i in range(len(S))) for j in range(n)]


def wolfe(P, eps=1e-10):
    S = [P[0]]
    w = [1.0]
    x = list(map(float, P[0]))
    for _ in range(1000):
        j = min(range(len(P)), key=lambda i: dot(x, P[i]))
        if dot(x, x) - dot(x, P[j]) <= eps * max(1.0, dot(x, x)) or P[j] in S:
            return S
        S.append(P[j])
        w.append(0.0)
        while True:
            alpha = affine_min_norm(S, exact=False)
            if alpha is None:
                raise RuntimeError("affinely dependent support")
            if all(a > eps for a in alpha):
                w = alpha
                x = combo(S, w)
                break
            theta = min(w[i] / (w[i] - alpha[i]) for i in range(len(S)) if alpha[i] <= eps)
            w = [theta * alpha[i] + (1 - theta) * w[i] for i in range(len(S))]
            keep = [i for i in range(len(S)) if w[i] > eps]
            S = [S[i] for i in keep]
            w = [w[i] for i in keep]
            x = combo(S, w)
    raise RuntimeError("Wolfe did not converge")


def opt_u_sq(P):
    """Exact |u*|^2 for (QP), with a KKT certificate."""
    S = wolfe(P)
    alpha = affine_min_norm(S, exact=True)
    assert alpha is not None and all(a > 0 for a in alpha), "certificate failed (alpha)"
    y = combo(S, alpha)
    yy = dot(y, y)
    assert yy > 0
    assert all(dot(y, s) == yy for s in S), "certificate failed (support)"
    assert all(dot(y, x) >= yy for x in P), "certificate failed (feasibility)"
    return 1 / yy


def signed_perm_tables(n, C):
    index = {v: i for i, v in enumerate(C)}
    tables = []
    for perm in itertools.permutations(range(n)):
        for signs in itertools.product((1, -1), repeat=n):
            tables.append([index[tuple(signs[i] * v[perm[i]] for i in range(n))] for v in C])
    return tables


def run(n, W):
    C = cube(n)
    reps = {}
    for a in itertools.combinations_with_replacement(range(W + 1), n):
        vals = [dot(a, x) for x in C]
        if 0 in vals:
            continue
        mask = sum(1 << i for i, v in enumerate(vals) if v > 0)
        reps.setdefault(mask, a)
    tables = signed_perm_tables(n, C)
    covered = set()
    classes = []
    for mask, a in reps.items():
        if mask in covered:
            continue
        bits = [i for i in range(len(C)) if mask >> i & 1]
        orbit = {sum(1 << t[i] for i in bits) for t in tables}
        covered |= orbit
        P = [C[i] for i in bits]
        classes.append((opt_u_sq(P), a, len(orbit)))
    return classes, len(covered)


def main():
    nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    W = int(sys.argv[2]) if len(sys.argv) > 2 else 12
    for n in range(1, nmax + 1):
        classes, total = run(n, W)
        ok = total == A000609[n - 1]
        worst = max(c[0] for c in classes)
        print(f"n = {n}: {len(classes)} orbits of partitions, {total} partitions "
              f"(A000609({n - 1}) = {A000609[n - 1]}, complete: {ok})")
        for usq, a, size in sorted(classes, reverse=True):
            print(f"    weights {a}: orbit size {size}, 1/(optimized margin)^2 = {usq}")
        print(f"    1/d_{n}^2 = {worst}")
        assert ok


if __name__ == "__main__":
    main()
