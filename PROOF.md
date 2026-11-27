# The worst margin when halving the hypercube

*Draft, November 2026. Written with AI assistance (Claude) and not yet checked by a human expert;
see [CHECKS.md](CHECKS.md) for how it has been checked so far. Every step below is also proved in
Lean 4 with Mathlib (Section 6).*

## 1. Introduction

Let C_n = {−1, 1}ⁿ and e = (1, …, 1). A hyperplane through the origin that contains no point of C_n
splits C_n into two halves. In MathOverflow question 448472, V. Elser asks for the *worst margin* of
such a split: for each split, take the supremum, over the hyperplanes that realize it, of the
distance to the nearest point of C_n (it is attained; see Step D), and then take the split for
which this best distance is smallest. Call this number d_n. Elser states, without proof, that

  d_n = min { 1/‖m⁻¹e‖ : m an n × n matrix with entries ±1 and det m ≠ 0 },   (1)

and asks what is known about d_n and whether it has a simple nontrivial lower bound. When we
wrote the statement (November 2026) the question had no posted answer.

**Theorem.** For every n ≥ 1:

(a) the two definitions agree: d_n = dMat_n, where dMat_n is the right-hand side of (1);

(b) d_n² · ((n+1)ⁿ/4ⁿ⁻¹ − 1) ≥ 1, that is,

  d_n ≥ ((n+1)ⁿ/4ⁿ⁻¹ − 1)^(−1/2).

For n ≤ 6 the exact values are 1/d_n² = 1, 1, 3, 7, 19, 59, computed in two independent ways
(Section 5). The bound (b) holds with equality for n = 1 and n = 3 and is strict for n = 2, 4, 5, 6.
In particular d_n > 2ⁿ⁻¹(n+1)^(−n/2) for every n, and for large n the two bounds agree up to a
factor 1 + o(1).

*Idea of the proof.* Write N(m) = ‖m⁻¹e‖² and let m be a nonsingular sign matrix with N(m) as large
as possible; put w = m⁻¹e, so that w · r = 1 for every row r of m. Replacing one row of m by
another sign vector changes m⁻¹e along a line, and comparing with the maximum gives two facts:
|w · x| ≥ 1 for every x ∈ C_n, and w is a combination of the rows of m with positive coefficients.
The first fact says that w defines a split of C_n; the second is a certificate, in the sense of
support vector machines, that no hyperplane realizing this split has margin larger than 1/‖w‖. So
d_n ≤ 1/‖w‖. Conversely, for any split, the point of least norm in the convex hull of one half
gives a hyperplane with margin at least 1/‖m′⁻¹e‖ for some nonsingular sign matrix m′, and so at
least 1/‖w‖. This proves (a). The bound (b) is an upper bound on N(m): the matrix determinant lemma
gives det(mmᵀ + eeᵀ) = det(m)²(1 + N(m)), Hadamard's inequality bounds the left side by (n+1)ⁿ,
and 2ⁿ⁻¹ divides det m.

*What is standard and what is new.* The ingredients of (b) are classical: the matrix determinant
lemma, Hadamard's inequality and the divisibility 2ⁿ⁻¹ | det m for sign matrices. The duality
between the largest-margin hyperplane and the point of least norm in a convex hull is standard in
the theory of support vector machines. As far as we know, the proof of (1) through the
maximizer m (Steps A–C in Section 4) is new, but we have not done a systematic search of the
literature; see Section 7.

## 2. Definitions

Throughout, n ≥ 1, x · y is the standard inner product on ℝⁿ and ‖x‖ = √(x · x). The rows of a
matrix m are r_1, …, r_n.

- A vector a ∈ ℝⁿ *avoids* C_n if a · x ≠ 0 for every x ∈ C_n. Its *positive half* is
  P(a) = {x ∈ C_n : a · x > 0}. Since C_n = −C_n, a avoiding C_n gives C_n = P(a) ⊔ (−P(a)).
- u and a *induce the same split* if P(u) = P(a). If a avoids C_n this forces u to avoid C_n
  (if u · x = 0 then neither x nor −x is in P(u), but one of them is in P(a)).
- The *margin* of u ≠ 0 is margin(u) = min_{x ∈ C_n} |u · x| / ‖u‖, the distance from the
  hyperplane u^⊥ to the nearest point of C_n.
- The *optimized margin* of a split is optMargin(a) = sup { margin(u) : P(u) = P(a) }. The set is
  nonempty (it contains a) and bounded by √n, since |u · x| ≤ ‖u‖‖x‖ = ‖u‖√n.
- d_n = inf { optMargin(a) : a avoids C_n } (an infimum over the finitely many splits).
- A *sign matrix* is an n × n matrix with entries ±1. For a nonsingular one, N(m) = ‖m⁻¹e‖², and
  dMat_n = min { N(m)^(−1/2) : m a nonsingular sign matrix }. Let N_n = max N(m); then
  dMat_n = N_n^(−1/2). The set of sign matrices is finite, and it contains nonsingular ones
  because C_n spans ℝⁿ: the i-th unit vector is (e − x⁽ⁱ⁾)/2, where x⁽ⁱ⁾ is e with its i-th entry
  replaced by −1.

These are exactly the definitions of the Lean statement `oma/statement-mo-448472.lean`
(Section 6), where the vertices of C_n are indexed by Boolean vectors and inf/sup are `sInf`/`sSup` over sets
that are shown there to be nonempty and bounded.

## 3. The bound on N(m)

**Lemma 1 (matrix determinant lemma).** For a nonsingular n × n matrix m,
det(mmᵀ + eeᵀ) = det(m)² (1 + N(m)).

*Proof.* With A = mmᵀ, which is invertible, det(A + eeᵀ) = det(A)(1 + eᵀA⁻¹e), and
eᵀ(mmᵀ)⁻¹e = (m⁻¹e)ᵀ(m⁻¹e) = N(m). ∎

**Lemma 2.** For a sign matrix m, det(mmᵀ + eeᵀ) ≤ (n+1)ⁿ.

*Proof.* G = mmᵀ + eeᵀ is positive semidefinite, so its eigenvalues μ_i are ≥ 0, and by the
inequality of arithmetic and geometric means det G = ∏ μ_i ≤ (tr G / n)ⁿ. Each diagonal entry of
mmᵀ is ‖r_i‖² = n and each diagonal entry of eeᵀ is 1, so tr G = n(n+1). (Equivalently: G = BBᵀ
for the n × (n+1) matrix B = [m | e], whose rows have squared norm n + 1, and this is Hadamard's
inequality.) ∎

**Lemma 3.** For a sign matrix m, 2ⁿ⁻¹ divides det m. Hence det(m)² ≥ 4ⁿ⁻¹ if det m ≠ 0.

*Proof.* Subtracting the first row from each other row does not change the determinant, and turns
every entry of the rows 2, …, n into 0 or ±2. Taking a factor 2 out of each of these n − 1 rows
leaves an integer matrix. ∎

**Proposition 4.** For every nonsingular sign matrix m, N(m) ≤ (n+1)ⁿ/4ⁿ⁻¹ − 1.

*Proof.* By Lemmas 1–3, 4ⁿ⁻¹(1 + N(m)) ≤ det(m)²(1 + N(m)) ≤ (n+1)ⁿ. ∎

## 4. The two definitions agree

Fix a nonsingular sign matrix m with N(m) = N_n (a maximizer), and put w = m⁻¹e. Then
w · r_j = 1 for every row r_j of m. Let z_j = m⁻¹e_j be the j-th column of m⁻¹; then
r_i · z_j = δ_ij, and z_j ≠ 0.

**Lemma 5 (replacing a row).** Let m be a nonsingular matrix, w = m⁻¹e, j an index, y ∈ ℝⁿ with
z_j · y ≠ 0, and let m′ be m with its j-th row replaced by y. Then m′ is nonsingular and

  m′⁻¹e = w + t z_j,  t = (1 − w · y)/(z_j · y).

*Proof.* m′ = m + e_j(y − r_j)ᵀ, so det m′ = det m · (1 + (y − r_j) · m⁻¹e_j) = det m · (z_j · y),
which is nonzero. For i ≠ j, r_i · (w + t z_j) = 1 + 0 = 1, and y · (w + t z_j) = w · y + t (z_j · y) = 1. ∎

If y is a sign vector, m′ is again a sign matrix, so maximality gives ‖w + t z_j‖² ≤ ‖w‖², that is

  2t (w · z_j) + t² ‖z_j‖² ≤ 0.   (2)

**Step A.** |w · x| ≥ 1 for every x ∈ C_n. In particular w avoids C_n.

*Proof.* Suppose x ∈ C_n and a = w · x satisfies |a| < 1. Some j has c = z_j · x ≠ 0: otherwise
xᵀm⁻¹ = 0, so x = 0. Apply (2) with y = x, which gives t₁ = (1 − a)/c, and with y = −x, which gives
t₂ = −(1 + a)/c. Then t₁t₂ = −(1 − a²)/c² < 0, so one of t₁, t₂ is positive and the other negative.
For t > 0, (2) gives w · z_j ≤ −t‖z_j‖²/2 < 0; for t < 0 it gives w · z_j ≥ −t‖z_j‖²/2 > 0. These
contradict each other. ∎

**Step B.** λ_j := z_j · w ≥ ‖z_j‖² > 0 for every j.

*Proof.* Apply Lemma 5 with y = −r_j: z_j · y = −1 and w · y = −1, so t = −2, and (2) reads
−4 (w · z_j) + 4‖z_j‖² ≤ 0. ∎

The vector λ = (m⁻¹)ᵀw satisfies mᵀλ = w, that is,

  w = Σ_j λ_j r_j,  and  Σ_j λ_j = eᵀλ = (mw)ᵀλ = wᵀ(mᵀλ) = ‖w‖².   (3)

**Step C.** optMargin(w) = 1/‖w‖. Hence d_n ≤ N_n^(−1/2).

*Proof.* By Step A, margin(w) ≥ 1/‖w‖. Conversely, let P(u) = P(w) and μ = min_{x ∈ C_n} |u · x|.
Each row r_j lies in C_n and w · r_j = 1 > 0, so r_j ∈ P(w) = P(u) and μ ≤ u · r_j. By (3) and
Step B,

  u · w = Σ_j λ_j (u · r_j) ≥ μ Σ_j λ_j = μ ‖w‖²,

and u · w ≤ ‖u‖‖w‖ by Cauchy–Schwarz. Hence margin(u) = μ/‖u‖ ≤ 1/‖w‖. Since w avoids C_n,
d_n ≤ optMargin(w) = 1/‖w‖ = N_n^(−1/2). ∎

In the language of support vector machines, λ is a vector of nonnegative dual weights on the
support vectors r_1, …, r_n, and (3) is the optimality certificate for the normal w.

**Step D.** For every a that avoids C_n there is a nonsingular sign matrix m′ with
optMargin(a) ≥ N(m′)^(−1/2). Hence d_n ≥ N_n^(−1/2).

*Proof.* Let P = P(a), which is nonempty because C_n = P ⊔ (−P), and let p be the point of least norm in the compact
convex set K = conv P. For x ∈ K and 0 < s ≤ 1, p + s(x − p) ∈ K, so
2s p · (x − p) + s²‖x − p‖² ≥ 0; letting s → 0 gives the variational inequality

  p · x ≥ ‖p‖²  for every x ∈ K.   (4)

Writing p = Σ_{y ∈ P} ν_y y as a convex combination gives a · p > 0, so p ≠ 0. By (4),
p · x ≥ ‖p‖² > 0 for x ∈ P and p · x ≤ −‖p‖² for x ∈ −P. So P(p) = P and
margin(p) ≥ ‖p‖²/‖p‖ = ‖p‖, whence optMargin(a) ≥ ‖p‖ (the set in the supremum is bounded, Section 2).

Next, Σ_y ν_y (p · y − ‖p‖²) = p · p − ‖p‖² = 0 and every term is ≥ 0 by (4), so ν_y = 0 unless y
lies in the tight set T = {y ∈ P : p · y = ‖p‖²}. Hence p ∈ span T. Choose a basis B ⊆ T of
span T and extend it by points of C_n to a basis B′ of ℝⁿ (possible since C_n spans ℝⁿ). Let m′
be the matrix with rows B′; it is a nonsingular sign matrix, and w′ = m′⁻¹e satisfies w′ · b = 1
for b ∈ B′. The linear functionals x ↦ (w′ · x)‖p‖² and x ↦ p · x agree on B (both give ‖p‖²),
hence on span B, which contains p. So (w′ · p)‖p‖² = ‖p‖², i.e. w′ · p = 1, and by Cauchy–Schwarz
1 ≤ ‖w′‖‖p‖. Therefore optMargin(a) ≥ ‖p‖ ≥ 1/‖w′‖ = N(m′)^(−1/2) ≥ N_n^(−1/2). ∎

**Proof of the Theorem.** Steps C and D give d_n = N_n^(−1/2) = dMat_n, which is (a). Then
d_n² = 1/N_n, and Proposition 4 applied to the maximizer gives (b). ∎

**Remarks.** (i) The proof identifies a worst split: the one induced by w = m⁻¹e for any maximizer
m of N, whose optimal hyperplane is w^⊥ itself. It is the only one: margin(u) = 1/‖w‖ forces
equality in the Cauchy–Schwarz step of Step C, so u is a positive multiple of w. (ii) The inequality d_n ≥ dMat_n (Step D) is the
easier half of (1); the content of Elser's claim is d_n ≤ dMat_n, and this is where maximality is
used (Steps A–C). (iii) Equality in (b) needs equality in Lemma 2 and in Lemma 3, i.e. the rows of
[m | e] pairwise orthogonal and |det m| = 2ⁿ⁻¹. For n = 3 the matrix with rows (1,1,1), (−1,−1,1),
(−1,1,−1) does this: N = 3. (iv) We do not address Elser's closing question about whether fewer
than n points can realize the minimum, or the true order of growth of d_n.

## 5. Computer checks

These checks are evidence, not part of the proof. They use only the Python standard library
(Python ≥ 3.10) and exact integer and rational arithmetic.

**Table 1. Computer checks.**

| Script (log) | What it computes | Outcome |
|---|---|---|
| `scripts/matrix_side.py` (`logs/matrix_side.log`) | N_n = max ‖m⁻¹e‖² over all nonsingular sign matrices, n ≤ 6, by fraction-free elimination with an integer certificate m v = det(m) e for each system; rows normalized so that the first is e (column sign changes and row permutations do not change N) | N_n = 1, 1, 3, 7, 19, 59; N_n ≤ (n+1)ⁿ/4ⁿ⁻¹ − 1 with equality only for n = 1, 3 |
| `independent-checks/partition_side.py` (`logs/partition_side.log`) | d_n from the split definition, without sign matrices: for one split from each orbit under signed coordinate permutations, the optimal hyperplane is found from the quadratic program min ‖u‖² s.t. u · x ≥ 1 on the positive half, and certified exactly by its KKT conditions; completeness of the enumeration is checked against A000609(n−1), the number of threshold functions of n − 1 variables, which are in bijection with the splits of C_n | 1/d_n² = 1, 1, 3, 7, 19, 59, the same as N_n; all 2, 4, 14, 104, 1882, 94572 splits accounted for |

The two scripts share no code and compute the two sides of (1) separately, so their agreement
for n ≤ 6 is a check of (a) in those cases, and of (b) through the first table.

## 6. Lean formalization

The directory `lean/` is a Lean 4 (v4.33.1) project depending on Mathlib (tag `v4.33.1`).

- `HypercubeMargin/Defs.lean` contains the definitions `vertex`, `Avoids`, `SamePartition`,
  `margin`, `optMargin`, `d`, `IsSignMatrix` and `dMat`, copied verbatim from the statement file
  `oma/statement-mo-448472.lean`.
- `HypercubeMargin/Main.lean` proves

  ```lean
  theorem OMA.S_mo_448472.main : ∀ n : ℕ, 1 ≤ n →
      d n = dMat n ∧ 1 ≤ d n ^ 2 * (((n : ℝ) + 1) ^ n / 4 ^ (n - 1) - 1)
  ```

  which is the statement of `oma/statement-mo-448472.lean` word for word. The proof follows
  Sections 3–4: `det_gram_add` (Lemma 1), `det_le_trace_pow` (Lemma 2), `two_pow_dvd_det` and
  `det_sq_ge` (Lemma 3), `norm_bound` (Proposition 4), `pencil_det`/`pencil_sol` (Lemma 5),
  `stepA`, `stepB`, `margin_le_of_max` (Step C) and `exists_matrix_le` (Step D).
- There is no `sorry`, `native_decide` or added axiom; `#print axioms OMA.S_mo_448472.main` gives
  `[propext, Classical.choice, Quot.sound]` (`logs/lean_build.log`).

The directory `oma/` holds the same statement and proof in the single-file format of the
open-math-agents registry: `statement-mo-448472.lean` (the statement, with `sorry` in place of
the proof, as required there) and `proof-mo-448472.lean` (`theorem OMA.solution : type_of% @…main`).
The registry's own checker accepted both files locally. The statement was submitted to the
registry as pull request #2867, which at the time of writing awaits review by a maintainer.

## 7. Prior work and open questions

We have not made a systematic search of the literature, and the ingredients are classical, so
parts of this argument may already be known; we would be grateful for references. Related work on
threshold functions: Håstad [Hå94] showed that some threshold functions need exponentially large
integer weights, and Alon and Vũ [AV97] show that some threshold functions on n variables need
integer weights as large as n^(n/2) 2^(−n(1+o(1))), and use matrices of ±1 entries whose inverses
have large entries. Whether their constructions give an upper bound on d_n of the same order as
the lower bound (b), which would determine log d_n up to o(n log n), is a natural next question.

## References

- [AV97] N. Alon and V. H. Vũ, Anti-Hadamard matrices, coin weighing, threshold gates and
  indecomposable hypergraphs, *J. Combin. Theory Ser. A* 79 (1997), 133–160.
- [Hå94] J. Håstad, On the size of weights for threshold gates, *SIAM J. Discrete Math.* 7 (1994),
  484–492.
- [El23] V. Elser, question 448472 on MathOverflow, https://mathoverflow.net/questions/448472 (2023).
- [OEIS] The On-Line Encyclopedia of Integer Sequences, A000609 (number of threshold functions of
  n or fewer variables).
