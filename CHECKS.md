# Independent checks of the proof

The proof was found and written with the help of Claude, an AI model made by Anthropic, first as a
Lean proof and then as the paper proof in [PROOF.md](PROOF.md). To test it we ran three further
Claude sessions, each separate from the one that wrote the proof and from the others. Two of
them were asked to assume that something was wrong and to look for the error. None found an error
in the mathematics or in the Lean statement. The points they raised have been dealt with, as
listed below.

These checks were done by AI models, not by a specialist in the field, and should be read in that
light. The Lean proof does not depend on them: it is checked by the Lean kernel.

## First check: the Lean proof

A fresh session with no prior context audited `oma/proof-mo-448472.lean`, the single-file version
of `lean/HypercubeMargin/Main.lean`.

- The file compiles from scratch, and `#print axioms OMA.solution` gives
  `[propext, Classical.choice, Quot.sound]`.
- `example : type_of% @OMA.solution = type_of% @OMA.S_mo_448472.main := rfl` passes, so the proof
  proves exactly the stated theorem. The helper lemmas live in their own namespace and shadow
  nothing.
- There are no forbidden constructs (`sorry`, `admit`, `axiom`, `native_decide`), and the file
  passes the open-math-agents registry linter.
- On the mathematics, the audit confirmed the matrix determinant lemma, AM–GM and 2ⁿ⁻¹ | det m;
  the row-replacement lemmas behind Steps A and B; the dual certificate of Step C; and that every
  `sInf`/`sSup` is taken over a nonempty, bounded set, so no junk values are used.
- Non-fatal: two unnecessary `<;>` and two unused `simp` arguments (linter warnings, left as they
  are so that the file stays identical to the one that was checked).

## Second check: faithfulness of the statement

A fresh session was asked to find ways in which `oma/statement-mo-448472.lean` fails to say what
MathOverflow 448472 asks, or is vacuous.

- It found no faithfulness bug and no reliance on junk values. It confirmed the statement for
  n ≤ 6 by its own exact computation: 1/d_n² = 1, 1, 3, 7, 19, 59, with equality in the bound
  exactly for n = 1, 3.
- Its main concern was that d n = dMat n (Elser's claim, given without proof) might be false, which
  would make the statement false even with a correct bound. That claim is part (a) of the Theorem
  and is proved here (Steps A–D); the reviewer had not seen the proof.
- It asked for docstring changes: not to describe the statement as "one concrete answer" (the
  question has no posted answer), and to say where the bound comes from and when it is sharp. These
  were made. The Lean statement itself was not changed. The registry checker accepted the statement
  and the proof again after the change.
- It suggested splitting `main` into two theorems. This was not done, because both parts are
  proved.

## Third check: the paper proof

A fresh session was given PROOF.md and the Lean definitions and asked to assume that the proof was
wrong and to find the error. It checked Sections 2–4 line by line, worked n = 1, 2 and the n = 3
equality example by hand, and recomputed N_n for n ≤ 5 with its own exact code (1, 1, 3, 7, 19).
It found no mathematical error, and confirmed that the definitions in Section 2 match the Lean
statement. It asked for these changes, all made:

1. Section 1 described the optimized margin as a maximum; it is a supremum (attained, by Step D).
2. Step D: say why P(a) is nonempty and that the supremum is over a bounded set.
3. Remark (i): justify that w^⊥ is the *only* optimal hyperplane for its split (equality in
   Cauchy–Schwarz).
4. The asymptotic form of (b) undersold it: d_n > 2ⁿ⁻¹(n+1)^(−n/2) holds for every n.
5. Section 2 said splits are indexed by Boolean vectors; it is the vertices that are.
6. Section 5: the split counts are A000609(n−1), not A000609(n).
7. Section 7: mention Håstad's earlier work on weights of threshold gates.

It could not check the literature claims offline; Section 7 says that no systematic literature
search was made.

## Reference

[El23] V. Elser, MathOverflow question 448472, https://mathoverflow.net/questions/448472 (2023).
