# The worst margin when halving the hypercube

This repository contains a proof, checked in Lean 4, of an answer to MathOverflow question
[448472](https://mathoverflow.net/questions/448472) (V. Elser, 2023): how close to the cube
{−1, 1}ⁿ must a hyperplane through the origin come, at best, when it splits the cube in the worst
possible way?

## The problem and the result

Let C_n = {−1, 1}ⁿ and e = (1, …, 1). Each hyperplane through 0 that misses C_n splits it into two
halves. For a given split, take the largest distance to C_n that a hyperplane realizing that split
can have. Elser's d_n is the smallest of these best distances, over all splits. He states, without
proof, that

  d_n = min { 1/‖m⁻¹e‖ : m an n × n matrix with entries ±1, det m ≠ 0 },

and asks what is known about d_n and whether it has a simple nontrivial lower bound.

**Theorem.** For every n ≥ 1,

(a) d_n equals Elser's matrix quantity above, and

(b) d_n ≥ ((n+1)ⁿ/4ⁿ⁻¹ − 1)^(−1/2). In particular d_n > 2ⁿ⁻¹(n+1)^(−n/2).

For n ≤ 6 the exact values are 1/d_n² = 1, 1, 3, 7, 19, 59, so d_6 = 1/√59. The bound (b) is an
equality for n = 1, 3 and strict for n = 2, 4, 5, 6.

**Idea of the proof.** Take a sign matrix m that maximizes ‖m⁻¹e‖ and put w = m⁻¹e. Swapping one row
of m for another sign vector moves m⁻¹e along a line, and comparing with the maximum shows two
things. First, |w · x| ≥ 1 on C_n, so w defines a split. Second, w is a positive combination of the
rows of m, which certifies that no hyperplane realizing this split does better than 1/‖w‖. In the
other direction, the point of least norm in the convex hull of one half of any split produces a sign
matrix with 1/‖m⁻¹e‖ at most the optimized margin of that split. For (b), the matrix determinant lemma
gives det(mmᵀ + eeᵀ) = det(m)²(1 + ‖m⁻¹e‖²), Hadamard's inequality bounds the left side by (n+1)ⁿ,
and 2ⁿ⁻¹ divides det m. The full argument is in [PROOF.md](PROOF.md).

## Status

- **Lean.** The Theorem is proved in Lean 4 with Mathlib, with no `sorry` and no added axioms
  (`#print axioms` gives `[propext, Classical.choice, Quot.sound]`). The definitions follow
  Elser's question directly: splits, optimized margins and d_n as an infimum of suprema, not the
  matrix form. See PROOF.md, Section 6. The statement was submitted to the
  [open-math-agents](https://github.com/GuillaumeBAUD-coder/open-math-agents) registry as
  pull request #2867, which is awaiting review by a maintainer.
- **Paper proof.** Complete in [PROOF.md](PROOF.md). It has **not yet been checked by a human
  expert**.
- **AI assistance.** The proof was found and written with the help of Claude (Anthropic). Three
  further, separate Claude sessions checked the Lean proof, the faithfulness of the Lean statement,
  and the paper proof, two of them asked to look for an error. They found none. See
  [CHECKS.md](CHECKS.md).
- **Computer checks.** Two separate exact computations, one from each side of Elser's identity, agree
  for n ≤ 6. These are evidence; the proof is the Lean proof.

I take responsibility for the claims made here. Corrections and references to earlier work are
welcome.

## Reproducing the checks

Python ≥ 3.10, standard library only:

```bash
python scripts/matrix_side.py 6                     # max ‖m⁻¹e‖² over all sign matrices, n ≤ 6 (~3 min on 8 cores)
python independent-checks/partition_side.py 6 12    # d_n from the split definition, n ≤ 6 (~5 min)
```

Lean (toolchain in `lean/lean-toolchain`, Mathlib `v4.33.1`):

```bash
cd lean && lake exe cache get && lake build && lake env lean Axioms.lean
```

## Contents

- `PROOF.md`: statement, proof, computer checks, Lean formalization, related work
- `CHECKS.md`: the three independent checks and the changes they led to
- `lean/`: the Lean 4 project (`HypercubeMargin/Defs.lean`, `HypercubeMargin/Main.lean`)
- `oma/`: the same statement and proof as single files in the open-math-agents registry format
- `scripts/`, `logs/`: the exact computation of max ‖m⁻¹e‖², and all logs
- `independent-checks/`: the computation of d_n from the split definition, sharing no code with
  `scripts/`

## Reference

V. Elser, MathOverflow question 448472 (2023), https://mathoverflow.net/questions/448472.
