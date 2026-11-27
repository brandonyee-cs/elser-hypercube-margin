import Mathlib

/-!
# Worst margin when halving the hypercube with a hyperplane (MathOverflow 448472)

Source: https://mathoverflow.net/questions/448472 (V. Elser, 2023)
Credit: @brandonyee-cs

Let `C_n = {-1,1}^n`. A hyperplane through the origin that avoids `C_n`, with normal `a`, splits
`C_n` into two halves. For that partition, optimize the normal `u` (over all normals inducing the
same partition) to maximize the margin, the minimum distance `|u . x| / |u|` from the
hyperplane to the points `x` of `C_n`. `d n` is the worst (smallest) optimized margin over all
partitions. Elser also gives an equivalent definition: the minimum of `1 / |m⁻¹ e|` over
nonsingular `n × n` matrices `m` with entries `±1`, where `e` is the all-ones vector.
Here that quantity is `dMat n`.

The question is open-ended: what is known about `d n`, and does it have a simple nontrivial lower
bound? No answer has been posted on MathOverflow. This statement formalizes a candidate answer
supplied by the submitter:
* (a) the two definitions agree, `d n = dMat n`. Elser asserts this without proof. The inequality
  `dMat n ≤ d n` is elementary; the reverse inequality is the substantive part. Exact computation
  confirms it for `n ≤ 6` (`d 6 = 1/√59`); and
* (b) the explicit lower bound `d n ^ 2 * ((n+1)^n / 4^(n-1) - 1) ≥ 1`, i.e.
  `d n ≥ ((n+1)^n / 4^(n-1) - 1)^(-1/2)`. It comes from Hadamard's inequality for the
  `n × (n+1)` matrix `[m | e]` together with `2^(n-1) ∣ det m`. Equality holds for `n = 1, 3`,
  and not for `n = 2, 4, 5, 6`.
Both conjuncts are needed: (b) is about the partition definition `d`, and it is (a) that ties it to
the matrix definition. Not formalized here: Elser's closing question (whether fewer than `n` points
can realize the minimum) and any asymptotic statement.

Reviewer notes on the translation:
* Vertices of `C_n` are indexed by `s : Fin n → Bool` (`vertex s i = 1` if `s i`, else `-1`).
* `SamePartition u a` says `u` and `a` have the same positive half on `C_n`. Because `C_n = -C_n`,
  this forces `u` to avoid `C_n` too, and `u ≠ 0`.
* `optMargin a` is a supremum over a nonempty set bounded above by `√n`. `d n` is an infimum over
  finitely many values, one per partition. `dMat n` is a minimum over a finite set.
* `n = 0` is excluded (`1 ≤ n`).
-/

namespace OMA.S_mo_448472

open Matrix

/-- The vertex of `{-1,1}^n` indexed by `s`. -/
def vertex {n : ℕ} (s : Fin n → Bool) : Fin n → ℝ := fun i => if s i then 1 else -1

/-- The hyperplane through the origin with normal `a` contains no vertex of the cube. -/
def Avoids {n : ℕ} (a : Fin n → ℝ) : Prop := ∀ s : Fin n → Bool, a ⬝ᵥ vertex s ≠ 0

/-- The normals `u` and `a` induce the same partition of the cube. -/
def SamePartition {n : ℕ} (u a : Fin n → ℝ) : Prop :=
  ∀ s : Fin n → Bool, (0 < u ⬝ᵥ vertex s ↔ 0 < a ⬝ᵥ vertex s)

/-- The minimum distance from the hyperplane `u⊥` to the vertices of the cube. -/
noncomputable def margin {n : ℕ} (u : Fin n → ℝ) : ℝ :=
  (⨅ s : Fin n → Bool, |u ⬝ᵥ vertex s|) / √(u ⬝ᵥ u)

/-- The optimized margin of the partition induced by `a`. -/
noncomputable def optMargin {n : ℕ} (a : Fin n → ℝ) : ℝ :=
  sSup {γ : ℝ | ∃ u : Fin n → ℝ, SamePartition u a ∧ γ = margin u}

/-- Elser's `d_n`: the worst optimized margin over all partitions. -/
noncomputable def d (n : ℕ) : ℝ :=
  sInf {γ : ℝ | ∃ a : Fin n → ℝ, Avoids a ∧ γ = optMargin a}

/-- All entries are `1` or `-1`. -/
def IsSignMatrix {n : ℕ} (m : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ i j, m i j = 1 ∨ m i j = -1

/-- Elser's matrix form of `d_n`: the minimum of `1 / ‖m⁻¹ e‖` over nonsingular sign matrices. -/
noncomputable def dMat (n : ℕ) : ℝ :=
  sInf {γ : ℝ | ∃ m : Matrix (Fin n) (Fin n) ℝ, IsSignMatrix m ∧ m.det ≠ 0 ∧
    γ = 1 / √((m⁻¹ *ᵥ fun _ => (1 : ℝ)) ⬝ᵥ (m⁻¹ *ᵥ fun _ => (1 : ℝ)))}

/-- The two definitions agree, and `d n` satisfies the explicit lower bound
`d n ^ 2 * ((n+1)^n / 4^(n-1) - 1) ≥ 1`. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    d n = dMat n ∧ 1 ≤ d n ^ 2 * (((n : ℝ) + 1) ^ n / 4 ^ (n - 1) - 1) := by
  sorry

end OMA.S_mo_448472
