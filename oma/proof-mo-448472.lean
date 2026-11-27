import OMAStatements.S_mo_448472

open Matrix OMA.S_mo_448472

namespace HHMProof

lemma sign_sq {n : ℕ} {m : Matrix (Fin n) (Fin n) ℝ} (hm : IsSignMatrix m) (i j : Fin n) :
    m i j * m i j = 1 := by
  rcases hm i j with h | h <;> simp [h]

/-- det (m mᵀ + e eᵀ) = det m ^ 2 * (1 + N). -/
lemma det_gram_add {n : ℕ} (m : Matrix (Fin n) (Fin n) ℝ) (hd : m.det ≠ 0) :
    (m * mᵀ + vecMulVec (fun _ => (1:ℝ)) (fun _ => (1:ℝ))).det =
      m.det ^ 2 * (1 + (m⁻¹ *ᵥ fun _ => (1 : ℝ)) ⬝ᵥ (m⁻¹ *ᵥ fun _ => (1 : ℝ))) := by
  have hA : IsUnit (m * mᵀ).det := by
    rw [det_mul, det_transpose]; exact (mul_ne_zero hd hd).isUnit
  rw [vecMulVec_eq Unit, det_add_replicateCol_mul_replicateRow hA, det_mul, det_transpose]
  have h1 : ((1 : Matrix Unit Unit ℝ) + replicateRow Unit (fun _ : Fin n => (1:ℝ)) * (m * mᵀ)⁻¹ *
      replicateCol Unit (fun _ : Fin n => (1:ℝ))).det =
      1 + (fun _ : Fin n => (1:ℝ)) ⬝ᵥ ((m * mᵀ)⁻¹ *ᵥ fun _ => (1:ℝ)) := by
    rw [det_unique]
    simp [mul_apply, dotProduct, mulVec]
    exact Finset.sum_comm
  rw [h1, Matrix.mul_inv_rev, ← transpose_nonsing_inv, ← mulVec_mulVec, dotProduct_mulVec,
    vecMul_transpose, sq]

lemma det_le_trace_pow {n : ℕ} (hn : 0 < n) (G : Matrix (Fin n) (Fin n) ℝ) (hG : G.PosSemidef) :
    G.det ≤ (G.trace / n) ^ n := by
  classical
  have hH := hG.isHermitian
  set μ := hH.eigenvalues with hμ
  have hdet : G.det = ∏ i, μ i := by
    rw [hH.det_eq_prod_eigenvalues]; simp [μ]
  have htr : G.trace = ∑ i, μ i := by
    rw [hH.trace_eq_sum_eigenvalues]; simp [μ]
  have hnn : ∀ i, 0 ≤ μ i := fun i => hG.eigenvalues_nonneg i
  have amgm := Real.geom_mean_le_arith_mean Finset.univ (fun _ => (1:ℝ)) μ
    (fun _ _ => zero_le_one) (by simp [hn]) (fun i _ => hnn i)
  simp only [Real.rpow_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one, one_mul] at amgm
  have hP : 0 ≤ ∏ i, μ i := Finset.prod_nonneg fun i _ => hnn i
  rw [hdet, htr]
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  calc ∏ i, μ i = ((∏ i, μ i) ^ ((n : ℝ)⁻¹)) ^ n := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hP, inv_mul_cancel₀ hn', Real.rpow_one]
    _ ≤ ((∑ i, μ i) / n) ^ n := by
        apply pow_le_pow_left₀ (Real.rpow_nonneg hP _) amgm

lemma two_pow_dvd_det {k : ℕ} (K : Matrix (Fin (k+1)) (Fin (k+1)) ℤ)
    (hK : ∀ i j, K i j = 1 ∨ K i j = -1) : (2:ℤ) ^ k ∣ K.det := by
  classical
  let B : Matrix (Fin (k+1)) (Fin (k+1)) ℤ :=
    Matrix.of fun i j => if i = 0 then K 0 j else K i j - K 0 j
  have hKB : K.det = B.det := by
    apply det_eq_of_forall_row_eq_smul_add_const (fun i => if i = 0 then (0:ℤ) else 1) 0 (by simp)
    intro i j
    by_cases hi : i = 0 <;> simp [B, hi]
  let C : Matrix (Fin (k+1)) (Fin (k+1)) ℤ :=
    Matrix.of fun i j => if i = 0 then K 0 j else (K i j - K 0 j) / 2
  let d : Fin (k+1) → ℤ := fun i => if i = 0 then 1 else 2
  have hBC : B = diagonal d * C := by
    ext i j
    rw [diagonal_mul]
    by_cases hi : i = 0
    · simp [B, C, d, hi]
    · simp only [B, C, d, hi, of_apply, if_false]
      have : (2:ℤ) ∣ K i j - K 0 j := by
        rcases hK i j with h1 | h1 <;> rcases hK 0 j with h2 | h2 <;> rw [h1, h2] <;> norm_num
      exact (Int.mul_ediv_cancel' this).symm
  rw [hKB, hBC, det_mul, det_diagonal, Fin.prod_univ_succ]
  simp [d, Fin.succ_ne_zero]

lemma det_sq_ge {n : ℕ} (hn : 1 ≤ n) {m : Matrix (Fin n) (Fin n) ℝ} (hm : IsSignMatrix m)
    (hd : m.det ≠ 0) : (4:ℝ) ^ (n - 1) ≤ m.det ^ 2 := by
  classical
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  let K : Matrix (Fin (k+1)) (Fin (k+1)) ℤ := Matrix.of fun i j => if m i j = 1 then 1 else -1
  have hK : ∀ i j, K i j = 1 ∨ K i j = -1 := by
    intro i j; by_cases h : m i j = 1 <;> simp [K, h]
  have hmK : m = (Int.castRingHom ℝ).mapMatrix K := by
    ext i j
    rcases hm i j with h | h <;> simp [K, h]
  have hdet : m.det = ((K.det : ℤ) : ℝ) := by
    rw [hmK, ← RingHom.map_det]; rfl
  obtain ⟨c, hc⟩ := two_pow_dvd_det K hK
  have hc0 : c ≠ 0 := by
    rintro rfl; apply hd; rw [hdet, hc]; simp
  have hc1 : (1:ℝ) ≤ (c:ℝ) ^ 2 := by
    have : (1:ℤ) ≤ c ^ 2 := by
      have := Int.one_le_abs hc0
      nlinarith [abs_mul_abs_self c, abs_nonneg c]
    exact_mod_cast this
  rw [hdet, hc]
  push_cast
  have h4 : (4:ℝ) ^ k = ((2:ℝ) ^ k) ^ 2 := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [h4, mul_pow]
  have : (0:ℝ) ≤ ((2:ℝ) ^ k) ^ 2 := by positivity
  nlinarith

theorem norm_bound {n : ℕ} (hn : 1 ≤ n) {m : Matrix (Fin n) (Fin n) ℝ} (hm : IsSignMatrix m)
    (hd : m.det ≠ 0) :
    (m⁻¹ *ᵥ fun _ => (1 : ℝ)) ⬝ᵥ (m⁻¹ *ᵥ fun _ => (1 : ℝ)) ≤
      ((n : ℝ) + 1) ^ n / 4 ^ (n - 1) - 1 := by
  classical
  set e : Fin n → ℝ := fun _ => 1 with he
  set G := m * mᵀ + vecMulVec e e with hG
  have hpsd : G.PosSemidef := by
    have h1 : (m * mᵀ).PosSemidef := by
      have := posSemidef_self_mul_conjTranspose m
      rwa [conjTranspose_eq_transpose_of_trivial] at this
    have h2 : (vecMulVec e e).PosSemidef := by
      have := posSemidef_vecMulVec_self_star e
      rwa [star_trivial] at this
    exact h1.add h2
  have htr : G.trace = (n : ℝ) * ((n : ℝ) + 1) := by
    have t1 : (m * mᵀ).trace = (n : ℝ) * n := by
      simp [trace, mul_apply, sign_sq hm]
    have t2 : (vecMulVec e e).trace = n := by
      simp [trace, vecMulVec_apply, he]
    rw [hG, trace_add, t1, t2]; ring
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  have hle : G.det ≤ ((n:ℝ) + 1) ^ n := by
    have := det_le_trace_pow (by omega) G hpsd
    rwa [htr, mul_div_cancel_left₀ _ hn0.ne'] at this
  rw [hG, det_gram_add m hd] at hle
  have h4 := det_sq_ge hn hm hd
  have h4pos : (0:ℝ) < 4 ^ (n - 1) := by positivity
  set N := (m⁻¹ *ᵥ e) ⬝ᵥ (m⁻¹ *ᵥ e)
  have hN : 0 ≤ N := by
    simp only [N, dotProduct]; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  rw [le_sub_iff_add_le, le_div_iff₀ h4pos]
  nlinarith

end HHMProof

open Matrix OMA.S_mo_448472

namespace HHMProof

/-- The all-ones vector. -/
abbrev E (n : ℕ) : Fin n → ℝ := fun _ => 1

/-- `m⁻¹ e`. -/
noncomputable abbrev sol {n : ℕ} (m : Matrix (Fin n) (Fin n) ℝ) : Fin n → ℝ := m⁻¹ *ᵥ E n

lemma mul_sol {n : ℕ} {m : Matrix (Fin n) (Fin n) ℝ} (hd : m.det ≠ 0) : m *ᵥ sol m = E n := by
  rw [sol, mulVec_mulVec, mul_nonsing_inv _ hd.isUnit, one_mulVec]

lemma sol_eq {n : ℕ} {m : Matrix (Fin n) (Fin n) ℝ} (hd : m.det ≠ 0) {v : Fin n → ℝ}
    (hv : m *ᵥ v = E n) : sol m = v := by
  rw [sol, ← hv, mulVec_mulVec, nonsing_inv_mul _ hd.isUnit, one_mulVec]

lemma mulVec_inv_single {n : ℕ} {m : Matrix (Fin n) (Fin n) ℝ} (hd : m.det ≠ 0) (j : Fin n) :
    m *ᵥ (m⁻¹ *ᵥ Pi.single j 1) = Pi.single j 1 := by
  rw [mulVec_mulVec, mul_nonsing_inv _ hd.isUnit, one_mulVec]

lemma row_dot {n : ℕ} (m : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) (v : Fin n → ℝ) :
    m i ⬝ᵥ v = (m *ᵥ v) i := rfl

lemma updateRow_mulVec_ne {n : ℕ} (m : Matrix (Fin n) (Fin n) ℝ) (j : Fin n) (y v : Fin n → ℝ)
    {i : Fin n} (hi : i ≠ j) : (m.updateRow j y *ᵥ v) i = (m *ᵥ v) i := by
  simp [mulVec, updateRow_ne hi]

lemma updateRow_mulVec_self {n : ℕ} (m : Matrix (Fin n) (Fin n) ℝ) (j : Fin n) (y v : Fin n → ℝ) :
    (m.updateRow j y *ᵥ v) j = y ⬝ᵥ v := by
  simp [mulVec, updateRow_self]

/-- Replacing row `j` by `y` keeps `m` nonsingular when `⟨z, y⟩ ≠ 0`, `z = m⁻¹ e_j`. -/
lemma pencil_det {n : ℕ} {m : Matrix (Fin n) (Fin n) ℝ} (hd : m.det ≠ 0) (j : Fin n)
    (y : Fin n → ℝ) (hc : (m⁻¹ *ᵥ Pi.single j 1) ⬝ᵥ y ≠ 0) : (m.updateRow j y).det ≠ 0 := by
  classical
  intro h0
  obtain ⟨v, hv0, hv⟩ := (exists_mulVec_eq_zero_iff).2 h0
  set z := m⁻¹ *ᵥ Pi.single j (1:ℝ)
  have hmv : m *ᵥ v = (m j ⬝ᵥ v) • Pi.single j 1 := by
    ext i
    by_cases hi : i = j
    · subst hi; simp [row_dot]
    · have := congrFun hv i
      rw [updateRow_mulVec_ne m j y v hi] at this
      simp [this, hi]
  generalize hs : m j ⬝ᵥ v = s at hmv
  have hvz : v = s • z := by
    calc v = m⁻¹ *ᵥ (m *ᵥ v) := by
          rw [mulVec_mulVec, nonsing_inv_mul _ hd.isUnit, one_mulVec]
      _ = s • z := by rw [hmv, mulVec_smul]
  have hy : y ⬝ᵥ v = 0 := by
    have := congrFun hv j
    rwa [updateRow_mulVec_self] at this
  rw [hvz, dotProduct_smul, smul_eq_mul, dotProduct_comm] at hy
  rcases mul_eq_zero.1 hy with h | h
  · apply hv0; rw [hvz, h, zero_smul]
  · exact hc h

/-- The solution after replacing row `j` by `y`. -/
lemma pencil_sol {n : ℕ} {m : Matrix (Fin n) (Fin n) ℝ} (hd : m.det ≠ 0) (j : Fin n)
    (y : Fin n → ℝ) (hc : (m⁻¹ *ᵥ Pi.single j 1) ⬝ᵥ y ≠ 0) :
    sol (m.updateRow j y) = sol m +
      ((1 - sol m ⬝ᵥ y) / ((m⁻¹ *ᵥ Pi.single j 1) ⬝ᵥ y)) • (m⁻¹ *ᵥ Pi.single j 1) := by
  classical
  apply sol_eq (pencil_det hd j y hc)
  set z := m⁻¹ *ᵥ Pi.single j (1:ℝ)
  ext i
  by_cases hi : i = j
  · subst hi
    rw [updateRow_mulVec_self, dotProduct_add, dotProduct_smul, smul_eq_mul, dotProduct_comm y z,
      dotProduct_comm y]
    field_simp
    ring
  · rw [updateRow_mulVec_ne m j y _ hi, mulVec_add, mulVec_smul, mulVec_inv_single hd,
      mul_sol hd]
    simp [hi]

lemma norm_add_smul {n : ℕ} (w z : Fin n → ℝ) (t : ℝ) :
    (w + t • z) ⬝ᵥ (w + t • z) = w ⬝ᵥ w + 2 * t * (w ⬝ᵥ z) + t ^ 2 * (z ⬝ᵥ z) := by
  simp only [dotProduct_add, add_dotProduct, dotProduct_smul, smul_dotProduct, smul_eq_mul,
    dotProduct_comm z w]
  ring

lemma dot_self_pos {n : ℕ} {z : Fin n → ℝ} (hz : z ≠ 0) : 0 < z ⬝ᵥ z := by
  have hnn : 0 ≤ z ⬝ᵥ z := Finset.sum_nonneg fun i _ => mul_self_nonneg (z i)
  rcases hnn.lt_or_eq with h | h
  · exact h
  · exact absurd (dotProduct_self_eq_zero.1 h.symm) hz

lemma inv_single_ne_zero {n : ℕ} {m : Matrix (Fin n) (Fin n) ℝ} (hd : m.det ≠ 0) (j : Fin n) :
    m⁻¹ *ᵥ Pi.single j (1:ℝ) ≠ 0 := by
  intro h
  have := mulVec_inv_single hd j
  rw [h, mulVec_zero] at this
  have := congrFun this j
  simp at this

lemma updateRow_sign {n : ℕ} {m : Matrix (Fin n) (Fin n) ℝ} (hm : IsSignMatrix m) (j : Fin n)
    {y : Fin n → ℝ} (hy : ∀ i, y i = 1 ∨ y i = -1) : IsSignMatrix (m.updateRow j y) := by
  classical
  intro i k
  by_cases hi : i = j
  · subst hi; rw [updateRow_self]; exact hy k
  · rw [updateRow_ne hi]; exact hm i k

/-- The set of nonsingular sign matrices. -/
def SM (n : ℕ) : Set (Matrix (Fin n) (Fin n) ℝ) := {m | IsSignMatrix m ∧ m.det ≠ 0}

lemma SM_finite (n : ℕ) : (SM n).Finite := by
  classical
  apply (Set.finite_range (fun B : Fin n → Fin n → Bool =>
    (Matrix.of fun i j => if B i j then (1:ℝ) else -1))).subset
  rintro m ⟨hm, -⟩
  refine ⟨fun i j => decide (m i j = 1), ?_⟩
  ext i j
  rcases hm i j with h | h <;> simp [h] <;> norm_num

/-- Maximality of `m` among nonsingular sign matrices. -/
def IsMax {n : ℕ} (m : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  m ∈ SM n ∧ ∀ m' ∈ SM n, sol m' ⬝ᵥ sol m' ≤ sol m ⬝ᵥ sol m

/-- Step A: at a maximizer, `|⟨w, x⟩| ≥ 1` for every sign vector `x`. -/
theorem stepA {n : ℕ} (hn : 1 ≤ n) {m : Matrix (Fin n) (Fin n) ℝ} (hmax : IsMax m)
    {x : Fin n → ℝ} (hx : ∀ i, x i = 1 ∨ x i = -1) : 1 ≤ |sol m ⬝ᵥ x| := by
  classical
  obtain ⟨⟨hm, hd⟩, hM⟩ := hmax
  by_contra hlt
  push Not at hlt
  set w := sol m with hw
  set a := w ⬝ᵥ x
  -- some coordinate c_j ≠ 0
  obtain ⟨j, hj⟩ : ∃ j, (m⁻¹ *ᵥ Pi.single j 1) ⬝ᵥ x ≠ 0 := by
    by_contra hall
    push Not at hall
    have hxm : x ᵥ* m⁻¹ = 0 := by
      ext j
      have := hall j
      rw [dotProduct_comm, dotProduct_mulVec, dotProduct_single_one] at this
      simpa using this
    have : x = (x ᵥ* m⁻¹) ᵥ* m := by
      rw [vecMul_vecMul, nonsing_inv_mul _ hd.isUnit, vecMul_one]
    rw [hxm, zero_vecMul] at this
    have h0 := congrFun this ⟨0, hn⟩
    rcases hx ⟨0, hn⟩ with h | h <;> simp [h] at h0
  set z := m⁻¹ *ᵥ Pi.single j (1:ℝ)
  set c := z ⬝ᵥ x
  have hz : 0 < z ⬝ᵥ z := dot_self_pos (inv_single_ne_zero hd j)
  have hnx : ∀ i, (-x) i = 1 ∨ (-x) i = -1 := by
    intro i; rcases hx i with h | h <;> simp [h]
  have hc' : z ⬝ᵥ (-x) ≠ 0 := by rw [dotProduct_neg]; exact neg_ne_zero.2 hj
  have h1 := hM _ ⟨updateRow_sign hm j hx, pencil_det hd j x hj⟩
  have h2 := hM _ ⟨updateRow_sign hm j hnx, pencil_det hd j (-x) hc'⟩
  rw [pencil_sol hd j x hj, norm_add_smul] at h1
  rw [pencil_sol hd j (-x) hc', norm_add_smul] at h2
  rw [dotProduct_neg, dotProduct_neg] at h2
  set b := w ⬝ᵥ z
  set t1 := (1 - a) / c
  set t2 := (1 - -a) / -c
  have ha : -1 < a ∧ a < 1 := abs_lt.1 hlt
  have hprod : t1 * t2 < 0 := by
    have : t1 * t2 = -((1 - a) * (1 + a)) / (c * c) := by
      simp only [t1, t2]; field_simp; ring
    rw [this]
    apply div_neg_of_neg_of_pos
    · nlinarith
    · exact mul_self_pos.2 hj
  have e1 : 2 * t1 * b + t1 ^ 2 * (z ⬝ᵥ z) ≤ 0 := by linarith
  have e2 : 2 * t2 * b + t2 ^ 2 * (z ⬝ᵥ z) ≤ 0 := by linarith
  -- t2 * e1 - t1 * e2 = t1 t2 (t1 - t2) |z|^2
  rcases lt_or_gt_of_ne (show t1 ≠ 0 by intro h; simp [h] at hprod) with ht1 | ht1
  · have ht2 : 0 < t2 := by nlinarith
    nlinarith [mul_nonpos_of_nonneg_of_nonpos ht2.le e1, mul_nonneg_of_nonpos_of_nonpos ht1.le e2,
      mul_pos (mul_pos_of_neg_of_neg ht1 (by linarith : t1 - t2 < 0)) (mul_pos ht2 hz)]
  · have ht2 : t2 < 0 := by nlinarith
    nlinarith [mul_nonneg_of_nonpos_of_nonpos ht2.le e1, mul_nonpos_of_nonneg_of_nonpos ht1.le e2,
      mul_pos (mul_pos ht1 (by linarith : (0:ℝ) < t1 - t2)) (mul_pos_of_neg_of_neg ht2 (neg_neg_of_pos hz))]

/-- Step B: at a maximizer, `⟨m⁻¹ e_j, w⟩ ≥ 0` for every `j`. -/
theorem stepB {n : ℕ} {m : Matrix (Fin n) (Fin n) ℝ} (hmax : IsMax m) (j : Fin n) :
    0 ≤ (m⁻¹ *ᵥ Pi.single j 1) ⬝ᵥ sol m := by
  classical
  obtain ⟨⟨hm, hd⟩, hM⟩ := hmax
  by_contra hlt
  push Not at hlt
  set z := m⁻¹ *ᵥ Pi.single j (1:ℝ)
  have hz : 0 < z ⬝ᵥ z := dot_self_pos (inv_single_ne_zero hd j)
  have hzr : z ⬝ᵥ m j = 1 := by
    rw [dotProduct_comm, row_dot, mulVec_inv_single hd]; simp
  have hwr : sol m ⬝ᵥ m j = 1 := by
    rw [dotProduct_comm, row_dot, mul_sol hd]
  have hc : z ⬝ᵥ (-m j) ≠ 0 := by rw [dotProduct_neg, hzr]; norm_num
  have hy : ∀ i, (-m j) i = 1 ∨ (-m j) i = -1 := by
    intro i; rcases hm j i with h | h <;> simp [h]
  have h1 := hM _ ⟨updateRow_sign hm j hy, pencil_det hd j _ hc⟩
  rw [pencil_sol hd j _ hc, norm_add_smul, dotProduct_neg, dotProduct_neg, hzr, hwr,
    dotProduct_comm (sol m) z] at h1
  have key : ((1:ℝ) - -1) / -1 = -2 := by norm_num
  rw [key] at h1
  nlinarith

end HHMProof

open Matrix OMA.S_mo_448472

namespace HHMProof

lemma vertex_sign {n : ℕ} (s : Fin n → Bool) (i : Fin n) : vertex s i = 1 ∨ vertex s i = -1 := by
  unfold vertex; by_cases h : s i <;> simp [h]

lemma vertex_not {n : ℕ} (s : Fin n → Bool) : vertex (fun i => !s i) = -vertex s := by
  ext i; unfold vertex; by_cases h : s i <;> simp [h]

lemma eq_vertex {n : ℕ} {x : Fin n → ℝ} (hx : ∀ i, x i = 1 ∨ x i = -1) :
    vertex (fun i => decide (x i = 1)) = x := by
  ext i; unfold vertex; rcases hx i with h | h <;> simp [h] <;> norm_num

lemma vertex_dot_self {n : ℕ} (s : Fin n → Bool) : vertex s ⬝ᵥ vertex s = n := by
  simp only [dotProduct]
  rw [show (n:ℝ) = ∑ _i : Fin n, (1:ℝ) by simp]
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases vertex_sign s i with h | h <;> rw [h] <;> norm_num

lemma dot_self_nonneg' {n : ℕ} (u : Fin n → ℝ) : 0 ≤ u ⬝ᵥ u :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (u i)

lemma cs {n : ℕ} (u w : Fin n → ℝ) : u ⬝ᵥ w ≤ √(u ⬝ᵥ u) * √(w ⬝ᵥ w) := by
  rw [← Real.sqrt_mul (dot_self_nonneg' u)]
  refine (le_abs_self _).trans (Real.abs_le_sqrt ?_)
  have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ u w
  simpa [dotProduct, sq] using this

lemma dot_mulVec_T {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (x y : Fin n → ℝ) :
    (A *ᵥ x) ⬝ᵥ y = x ⬝ᵥ (Aᵀ *ᵥ y) := by
  rw [dotProduct_mulVec, vecMul_transpose]

lemma margin_nonneg {n : ℕ} (u : Fin n → ℝ) : 0 ≤ margin u := by
  unfold margin
  apply div_nonneg _ (Real.sqrt_nonneg _)
  exact le_ciInf fun s => abs_nonneg _

lemma inf_le {n : ℕ} (u : Fin n → ℝ) (s : Fin n → Bool) :
    (⨅ s : Fin n → Bool, |u ⬝ᵥ vertex s|) ≤ |u ⬝ᵥ vertex s| :=
  ciInf_le ⟨0, by rintro _ ⟨t, rfl⟩; exact abs_nonneg _⟩ s

lemma margin_le_sqrt {n : ℕ} (u : Fin n → ℝ) : margin u ≤ √n := by
  unfold margin
  rcases (dot_self_nonneg' u).lt_or_eq with h | h
  · have hs : 0 < √(u ⬝ᵥ u) := Real.sqrt_pos.2 h
    rw [div_le_iff₀ hs]
    refine (inf_le u (fun _ => true)).trans ?_
    have h1 := cs u (vertex fun _ => true)
    have h2 := cs (-u) (vertex fun _ => true)
    rw [vertex_dot_self] at h1 h2
    have e : (-u) ⬝ᵥ (-u) = u ⬝ᵥ u := by simp
    rw [e, neg_dotProduct] at h2
    rw [abs_le]; constructor <;> nlinarith [mul_comm (√(u ⬝ᵥ u)) (√(n:ℝ))]
  · rw [← h]; simp

lemma bdd_margins {n : ℕ} (a : Fin n → ℝ) :
    BddAbove {γ : ℝ | ∃ u : Fin n → ℝ, SamePartition u a ∧ γ = margin u} :=
  ⟨√n, by rintro _ ⟨u, -, rfl⟩; exact margin_le_sqrt u⟩

lemma le_optMargin {n : ℕ} {a u : Fin n → ℝ} (hu : SamePartition u a) : margin u ≤ optMargin a :=
  le_csSup (bdd_margins a) ⟨u, hu, rfl⟩

lemma optMargin_nonneg {n : ℕ} (a : Fin n → ℝ) : 0 ≤ optMargin a :=
  (margin_nonneg a).trans (le_optMargin (fun _ => Iff.rfl))

/-- The SVM certificate: at a maximizer `m`, every normal inducing the same partition as
`w = m⁻¹ e` has margin at most `1/‖w‖`. -/
theorem margin_le_of_max {n : ℕ} (hn : 1 ≤ n) {m : Matrix (Fin n) (Fin n) ℝ} (hmax : IsMax m)
    {u : Fin n → ℝ} (hu : SamePartition u (sol m)) : margin u ≤ 1 / √(sol m ⬝ᵥ sol m) := by
  classical
  have hd := hmax.1.2
  have hm := hmax.1.1
  set w := sol m with hw
  set μ := ⨅ s : Fin n → Bool, |u ⬝ᵥ vertex s|
  -- rows are vertices, on the positive side
  have hrow : ∀ j, μ ≤ u ⬝ᵥ m j := by
    intro j
    have hv := eq_vertex (hm j)
    have hpos : 0 < w ⬝ᵥ m j := by rw [dotProduct_comm, row_dot, mul_sol hd]; norm_num
    have hup : 0 < u ⬝ᵥ m j := by
      have := (hu (fun i => decide (m j i = 1))).2; rw [hv] at this; exact this hpos
    have := inf_le u (fun i => decide (m j i = 1))
    rw [hv, abs_of_pos hup] at this
    exact this
  -- dual weights
  set lam : Fin n → ℝ := (m⁻¹)ᵀ *ᵥ w with hlam
  have hlam_j : ∀ j, lam j = (m⁻¹ *ᵥ Pi.single j 1) ⬝ᵥ w := by
    intro j
    simp [hlam, mulVec, dotProduct, transpose_apply, Pi.single_apply, mul_comm]
  have hlam_nn : ∀ j, 0 ≤ lam j := fun j => by rw [hlam_j]; exact stepB hmax j
  have hw_eq : mᵀ *ᵥ lam = w := by
    rw [hlam, mulVec_mulVec, ← transpose_mul, nonsing_inv_mul _ hd.isUnit, transpose_one, one_mulVec]
  have hsum : ∑ j, lam j = w ⬝ᵥ w := by
    calc ∑ j, lam j = E n ⬝ᵥ lam := by simp [dotProduct]
      _ = (m *ᵥ w) ⬝ᵥ lam := by rw [show m *ᵥ w = E n from mul_sol hd]
      _ = w ⬝ᵥ (mᵀ *ᵥ lam) := dot_mulVec_T m w lam
      _ = w ⬝ᵥ w := by rw [hw_eq]
  have huw : u ⬝ᵥ w = ∑ j, lam j * (u ⬝ᵥ m j) := by
    calc u ⬝ᵥ w = u ⬝ᵥ (mᵀ *ᵥ lam) := by rw [hw_eq]
      _ = (m *ᵥ u) ⬝ᵥ lam := (dot_mulVec_T m u lam).symm
      _ = ∑ j, lam j * (u ⬝ᵥ m j) := by
        simp only [dotProduct]; refine Finset.sum_congr rfl fun j _ => ?_
        rw [mul_comm]; congr 1; simp [mulVec, dotProduct, mul_comm]
  have hge : μ * (w ⬝ᵥ w) ≤ u ⬝ᵥ w := by
    rw [huw, ← hsum, Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => by rw [mul_comm]; exact mul_le_mul_of_nonneg_left (hrow j) (hlam_nn j)
  have hN : 0 < w ⬝ᵥ w := by
    apply dot_self_pos
    intro h0
    have := mul_sol hd
    rw [← hw, h0, mulVec_zero] at this
    have := congrFun this ⟨0, hn⟩
    simp at this
  have hu0 : 0 < u ⬝ᵥ u := by
    apply dot_self_pos
    intro h0
    have := (hu (fun i => decide (m ⟨0, hn⟩ i = 1))).2
    rw [eq_vertex (hm ⟨0, hn⟩), h0, zero_dotProduct] at this
    have hpos : 0 < w ⬝ᵥ m ⟨0, hn⟩ := by rw [dotProduct_comm, row_dot, mul_sol hd]; norm_num
    exact lt_irrefl _ (this hpos)
  have hcs := cs u w
  have hsu := Real.sqrt_pos.2 hu0
  have hsw := Real.sqrt_pos.2 hN
  have hsq : √(w ⬝ᵥ w) * √(w ⬝ᵥ w) = w ⬝ᵥ w := Real.mul_self_sqrt hN.le
  unfold margin
  rw [div_le_div_iff₀ hsu hsw, one_mul]
  nlinarith [mul_pos hsw hsw]

end HHMProof

open Matrix OMA.S_mo_448472

namespace HHMProof

/-- Every partition has optimized margin at least `1/‖m⁻¹e‖` for some nonsingular sign matrix `m`.
Proof: the least-norm point `p` of the convex hull of the positive half-cube. Its tight set lies on a
hyperplane through `p`; extend a basis of its span to a basis of cube vertices. -/
theorem exists_matrix_le {n : ℕ} {a : Fin n → ℝ} (ha : Avoids a) :
    ∃ m ∈ SM n, 1 / √(sol m ⬝ᵥ sol m) ≤ optMargin a := by
  classical
  let S : Finset (Fin n → ℝ) :=
    (Finset.univ.filter (fun s : Fin n → Bool => 0 < a ⬝ᵥ vertex s)).image vertex
  have hS : ∀ y ∈ S, 0 < a ⬝ᵥ y := by
    intro y hy
    simp only [S, Finset.mem_image, Finset.mem_filter] at hy
    obtain ⟨s, ⟨-, hs⟩, rfl⟩ := hy
    exact hs
  have hSv : ∀ s, 0 < a ⬝ᵥ vertex s → vertex s ∈ S :=
    fun s hs => Finset.mem_image.2 ⟨s, by simp [hs], rfl⟩
  have hneg : ∀ s, a ⬝ᵥ vertex s < 0 → vertex (fun i => !s i) ∈ S := by
    intro s hs; apply hSv; rw [vertex_not, dotProduct_neg]; linarith
  have hSne : (S : Set (Fin n → ℝ)).Nonempty := by
    rcases lt_or_gt_of_ne (ha (fun _ => true)) with h | h
    · exact ⟨_, hneg _ h⟩
    · exact ⟨_, hSv _ h⟩
  set K := convexHull ℝ (S : Set (Fin n → ℝ)) with hKdef
  have hK : IsCompact K := S.finite_toSet.isCompact_convexHull (𝕜 := ℝ)
  have hcont : Continuous fun v : Fin n → ℝ => v ⬝ᵥ v := by
    unfold dotProduct; fun_prop
  obtain ⟨p, hpK, hpmin⟩ :=
    hK.exists_isMinOn (hSne.mono (subset_convexHull ℝ _)) hcont.continuousOn
  have hSK : ∀ y ∈ S, y ∈ K := fun y hy => subset_convexHull ℝ _ hy
  -- variational inequality
  have hvar : ∀ x ∈ K, p ⬝ᵥ p ≤ p ⬝ᵥ x := by
    intro x hx
    by_contra hlt
    push Not at hlt
    set δ := p ⬝ᵥ (x - p) with hδdef
    have hδ : δ < 0 := by rw [hδdef, dotProduct_sub]; linarith
    set q := (x - p) ⬝ᵥ (x - p)
    have hq : 0 ≤ q := dot_self_nonneg' _
    set t := min 1 (-δ / (q + 1))
    have ht0 : 0 < t := lt_min one_pos (div_pos (by linarith) (by linarith))
    have ht1 : t ≤ 1 := min_le_left _ _
    have htq : t * q < -δ := by
      have h1 : t ≤ -δ / (q + 1) := min_le_right _ _
      have h2 : t * q ≤ (-δ / (q + 1)) * q := mul_le_mul_of_nonneg_right h1 hq
      have h3 : (-δ / (q + 1)) * q < -δ := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]; nlinarith
      linarith
    have hmem : p + t • (x - p) ∈ K :=
      (convex_convexHull ℝ _).add_smul_sub_mem hpK hx ⟨ht0.le, ht1⟩
    have hle := (isMinOn_iff.1 hpmin) _ hmem
    rw [norm_add_smul] at hle
    nlinarith [mul_neg_of_pos_of_neg ht0 (show 2 * δ + t * q < 0 by linarith)]
  obtain ⟨lam, hlam0, hlam1, hlamp⟩ := Finset.mem_convexHull'.1 hpK
  have hap : 0 < a ⬝ᵥ p := by
    rw [← hlamp, dotProduct_sum]
    simp only [dotProduct_smul, smul_eq_mul]
    obtain ⟨y0, hy0, hlpos⟩ : ∃ y ∈ S, 0 < lam y := by
      by_contra h
      push Not at h
      have : ∑ y ∈ S, lam y ≤ 0 := Finset.sum_nonpos h
      linarith
    exact Finset.sum_pos' (fun y hy => mul_nonneg (hlam0 y hy) (hS y hy).le)
      ⟨y0, hy0, mul_pos hlpos (hS y0 hy0)⟩
  have hp0 : p ≠ 0 := by rintro rfl; simp at hap
  have hpp : 0 < p ⬝ᵥ p := dot_self_pos hp0
  have hpos_side : ∀ s, 0 < a ⬝ᵥ vertex s → p ⬝ᵥ p ≤ p ⬝ᵥ vertex s :=
    fun s hs => hvar _ (hSK _ (hSv s hs))
  have hneg_side : ∀ s, a ⬝ᵥ vertex s < 0 → p ⬝ᵥ vertex s ≤ -(p ⬝ᵥ p) := by
    intro s hs
    have := hvar _ (hSK _ (hneg s hs))
    rw [vertex_not, dotProduct_neg] at this
    linarith
  have hsame : SamePartition p a := by
    intro s
    constructor
    · intro h
      rcases lt_or_gt_of_ne (ha s) with h' | h'
      · have := hneg_side s h'; linarith
      · exact h'
    · intro h; have := hpos_side s h; linarith
  have hmarg : √(p ⬝ᵥ p) ≤ margin p := by
    unfold margin
    rw [le_div_iff₀ (Real.sqrt_pos.2 hpp), Real.mul_self_sqrt hpp.le]
    apply le_ciInf
    intro s
    rcases lt_or_gt_of_ne (ha s) with h' | h'
    · have := hneg_side s h'; rw [abs_of_neg (by linarith)]; linarith
    · have := hpos_side s h'; rw [abs_of_pos (by linarith)]; linarith
  -- p lies in the span of the tight set
  set T0 : Set (Fin n → ℝ) := {y | y ∈ S ∧ p ⬝ᵥ y = p ⬝ᵥ p} with hT0
  have hpspan : p ∈ Submodule.span ℝ T0 := by
    have h1 : p ⬝ᵥ (∑ y ∈ S, lam y • y) = ∑ y ∈ S, lam y * (p ⬝ᵥ y) := by
      simp [dotProduct_sum, dotProduct_smul]
    rw [hlamp] at h1
    have hzero : ∑ y ∈ S, lam y * (p ⬝ᵥ y - p ⬝ᵥ p) = 0 := by
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hlam1, one_mul]
      linarith
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg (fun y hy =>
      mul_nonneg (hlam0 y hy) (by linarith [hvar y (hSK y hy)]))).1 hzero
    rw [← hlamp]
    refine Submodule.sum_mem _ fun y hy => ?_
    rcases mul_eq_zero.1 (hterm y hy) with h | h
    · rw [h, zero_smul]; exact Submodule.zero_mem _
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨hy, by linarith⟩)
  -- bases
  set C : Set (Fin n → ℝ) := Set.range vertex
  have hT0C : T0 ⊆ C := by
    rintro y ⟨hy, -⟩
    simp only [S, Finset.mem_image] at hy
    obtain ⟨s, -, rfl⟩ := hy
    exact ⟨s, rfl⟩
  obtain ⟨B, hBT, -, hTB, hBli⟩ :=
    exists_linearIndepOn_id_extension (linearIndepOn_empty ℝ id) (Set.empty_subset T0)
  obtain ⟨B', hB'C, hBB', hCB', hB'li⟩ := exists_linearIndepOn_id_extension hBli (hBT.trans hT0C)
  have hCspan : Submodule.span ℝ C = ⊤ := by
    rw [eq_top_iff, ← (Pi.basisFun ℝ (Fin n)).span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have : Pi.basisFun ℝ (Fin n) i =
        (1/2 : ℝ) • (vertex (fun _ => true) - vertex (fun k => decide (k ≠ i))) := by
      ext k
      by_cases hk : k = i
      · subst hk; simp [vertex]; norm_num
      · simp [vertex, hk, Pi.single_apply]
    rw [this]
    exact Submodule.smul_mem _ _
      (Submodule.sub_mem _ (Submodule.subset_span ⟨_, rfl⟩) (Submodule.subset_span ⟨_, rfl⟩))
  have hB'top : ⊤ ≤ Submodule.span ℝ (Set.range ((↑) : B' → Fin n → ℝ)) := by
    rw [Subtype.range_coe, ← hCspan]; exact Submodule.span_le.2 hCB'
  let bas := Module.Basis.mk hB'li hB'top
  let eqv : B' ≃ Fin n := bas.indexEquiv (Pi.basisFun ℝ (Fin n))
  let m : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i => ((eqv.symm i : B') : Fin n → ℝ)
  have hmrow : ∀ i, m i ∈ B' := fun i => (eqv.symm i).2
  have hmsign : IsSignMatrix m := by
    intro i j
    obtain ⟨s, hs⟩ := hB'C (hmrow i)
    rw [← hs]
    exact vertex_sign s j
  have hmdet : m.det ≠ 0 := by
    have hli : LinearIndependent ℝ m.row := by
      have := hB'li.comp eqv.symm eqv.symm.injective
      exact this
    exact ((isUnit_iff_isUnit_det m).1 (linearIndependent_rows_iff_isUnit.1 hli)).ne_zero
  set w := sol m
  have hwB' : ∀ b ∈ B', w ⬝ᵥ b = 1 := by
    intro b hb
    have hrow : m (eqv ⟨b, hb⟩) = b := by
      change ((eqv.symm (eqv ⟨b, hb⟩) : B') : Fin n → ℝ) = b
      rw [Equiv.symm_apply_apply]
    rw [← hrow, dotProduct_comm, row_dot, mul_sol hmdet]
  -- w · x * |p|^2 = p · x on span B
  have hspanB : ∀ x ∈ Submodule.span ℝ B, (w ⬝ᵥ x) * (p ⬝ᵥ p) = p ⬝ᵥ x := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      rw [hwB' x (hBB' hx), one_mul]
      exact (hBT hx).2.symm
    | zero => simp
    | add x y _ _ hx hy => rw [dotProduct_add, dotProduct_add, add_mul, hx, hy]
    | smul c x _ hx => rw [dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul, mul_assoc, hx]
  have hpB : p ∈ Submodule.span ℝ B := (Submodule.span_le.2 hTB) hpspan
  have hwp : w ⬝ᵥ p = 1 := by
    have := hspanB p hpB
    field_simp at this
    nlinarith [this]
  have hcs := cs w p
  rw [hwp] at hcs
  have hww : 0 < w ⬝ᵥ w := by
    rcases (dot_self_nonneg' w).lt_or_eq with h | h
    · exact h
    · rw [← h] at hcs; simp at hcs; linarith
  refine ⟨m, ⟨hmsign, hmdet⟩, ?_⟩
  have hsw := Real.sqrt_pos.2 hww
  calc 1 / √(w ⬝ᵥ w) ≤ √(p ⬝ᵥ p) := by
        rw [div_le_iff₀ hsw]; linarith
    _ ≤ margin p := hmarg
    _ ≤ optMargin a := le_optMargin hsame

end HHMProof

open Matrix OMA.S_mo_448472

namespace HHMProof

/-- The normal `(1, 2, 4, …)` avoids the cube: `⟨a, x⟩` is an odd integer. -/
lemma avoids_pow {n : ℕ} (hn : 1 ≤ n) : Avoids (fun i : Fin n => (2:ℝ) ^ (i : ℕ)) := by
  classical
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  intro s
  let z : Fin (k+1) → ℤ := fun i => 2 ^ (i : ℕ) * (if s i then 1 else -1)
  have hcast : (fun i : Fin (k+1) => (2:ℝ) ^ (i : ℕ)) ⬝ᵥ vertex s = ((∑ i, z i : ℤ) : ℝ) := by
    simp only [dotProduct, vertex, z]
    push_cast
    rfl
  rw [hcast]
  have hodd : ∑ i, z i = (if s 0 then 1 else -1) + 2 * ∑ i : Fin k, 2 ^ (i : ℕ) *
      (if s i.succ then 1 else -1) := by
    rw [Fin.sum_univ_succ, Finset.mul_sum]
    congr 1
    · simp [z]
    · refine Finset.sum_congr rfl fun i _ => ?_
      simp only [z, Fin.val_succ, pow_succ]
      ring
  intro h0
  have h0' : ∑ i, z i = 0 := by exact_mod_cast h0
  rw [hodd] at h0'
  by_cases hs : s 0 <;> simp [hs] at h0' <;> omega

end HHMProof

open HHMProof in
theorem OMA.solution : type_of% @OMA.S_mo_448472.main := by
  intro n hn
  classical
  obtain ⟨m0, hm0, -⟩ := exists_matrix_le (avoids_pow hn)
  obtain ⟨mx, hmx, hmax⟩ :=
    Set.exists_max_image (SM n) (fun m => sol m ⬝ᵥ sol m) (SM_finite n) ⟨m0, hm0⟩
  have hIM : IsMax mx := ⟨hmx, hmax⟩
  set w := sol mx with hw
  set N := w ⬝ᵥ w with hN
  have hNpos : 0 < N := by
    apply dot_self_pos
    intro h0
    have := mul_sol hmx.2
    rw [← hw, h0, mulVec_zero] at this
    have := congrFun this ⟨0, hn⟩
    simp at this
  have hsN := Real.sqrt_pos.2 hNpos
  -- the maximizer's hyperplane avoids the cube
  have hwav : Avoids w := by
    intro s h0
    have := stepA hn hIM (vertex_sign s)
    rw [← hw, h0, abs_zero] at this
    linarith
  -- dMat n = 1/√N
  have hdMat : dMat n = 1 / √N := by
    apply le_antisymm
    · apply csInf_le
      · exact ⟨0, by rintro _ ⟨m, -, -, rfl⟩; positivity⟩
      · exact ⟨mx, hmx.1, hmx.2, rfl⟩
    · refine le_csInf ⟨1 / √N, mx, hmx.1, hmx.2, rfl⟩ ?_
      rintro _ ⟨m, hm, hd, rfl⟩
      have hle := hmax m ⟨hm, hd⟩
      have hpos : 0 < sol m ⬝ᵥ sol m := by
        apply dot_self_pos
        intro h0
        have := mul_sol hd
        rw [h0, mulVec_zero] at this
        have := congrFun this ⟨0, hn⟩
        simp at this
      exact one_div_le_one_div_of_le (Real.sqrt_pos.2 hpos) (Real.sqrt_le_sqrt hle)
  -- d n = 1/√N
  have hd : d n = 1 / √N := by
    apply le_antisymm
    · have h1 : d n ≤ optMargin w := by
        apply csInf_le
        · exact ⟨0, by rintro _ ⟨a, -, rfl⟩; exact optMargin_nonneg a⟩
        · exact ⟨w, hwav, rfl⟩
      have h2 : optMargin w ≤ 1 / √N := by
        refine csSup_le ⟨margin w, w, fun _ => Iff.rfl, rfl⟩ ?_
        rintro _ ⟨u, hu, rfl⟩
        exact margin_le_of_max hn hIM hu
      exact h1.trans h2
    · refine le_csInf ⟨optMargin w, w, hwav, rfl⟩ ?_
      rintro _ ⟨a, ha, rfl⟩
      obtain ⟨m, hm, hle⟩ := exists_matrix_le ha
      have hle2 := hmax m hm
      have hpos : 0 < sol m ⬝ᵥ sol m := by
        apply dot_self_pos
        intro h0
        have := mul_sol hm.2
        rw [h0, mulVec_zero] at this
        have := congrFun this ⟨0, hn⟩
        simp at this
      exact (one_div_le_one_div_of_le (Real.sqrt_pos.2 hpos) (Real.sqrt_le_sqrt hle2)).trans hle
  refine ⟨hd.trans hdMat.symm, ?_⟩
  -- the explicit bound
  have hb := norm_bound hn hmx.1 hmx.2
  rw [hd, div_pow, Real.sq_sqrt hNpos.le, one_pow, one_div_mul_eq_div, le_div_iff₀ hNpos, one_mul]
  exact hb
