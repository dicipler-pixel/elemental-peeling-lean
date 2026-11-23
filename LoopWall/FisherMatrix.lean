import Mathlib

/-!
# The Fisher matrix of a colour, and the determinant ledger

Direction C2 (matrix-ledger topic) of the fourth round.  `shareMatrix_det`, `fisherMatrix_det`, the
inverse pair `fisherMatrix_mul_shareMatrix`/`shareMatrix_mul_fisherMatrix`, and `fisherMatrix_posDef`;
`fisherForm_eq_rawForm` identifies the Fisher form with `Σ v i^2 / x i`; `covariance_mul_fisherVelocity`
and `fisherForm_eq_covariance` show the covariance is the exact Fisher pseudoinverse on zero-sum
tangents.  For two normalized channels, `shareMatrix_det_balance` gives `det = (1 - balance^2)/4`,
`shareMatrix_det_wall_iff` turns the wall into `det = 1/8`, and
`matrixLedger_eq_two_scalarLedgerPotential` proves the determinant ledger is twice the scalar peel
potential, `matrixLedger_at_wall` giving `log 2`.

Written in the fourth parallel formalization round (swarm `smws625cs`, direction m5),
recompiled and reviewed here; namespace and header added, `#print axioms` lines removed.
-/

namespace ElementalPeeling.LoopWall.FisherMatrix

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The diagonal matrix whose entries are the channel shares. -/
noncomputable def shareMatrix (p : n → ℝ) : Matrix n n ℝ := Matrix.diagonal p

/-- The diagonal Fisher matrix, written without a matrix inverse. -/
noncomputable def fisherMatrix (p : n → ℝ) : Matrix n n ℝ :=
  Matrix.diagonal (fun i => (p i)⁻¹)

/-- The second-moment (covariance) matrix of a colour vector. -/
noncomputable def covariance (p : n → ℝ) : Matrix n n ℝ :=
  Matrix.diagonal p - Matrix.vecMulVec p p

/-- The displacement obtained by applying the Fisher matrix. -/
noncomputable def fisherVelocity (p u : n → ℝ) : n → ℝ := fisherMatrix p *ᵥ u

/-- The raw Schrödinger quadratic form on readings. -/
noncomputable def rawForm (x v : n → ℝ) : ℝ := ∑ i, (v i)^2 / x i

/-- The Fisher quadratic form as a matrix quadratic form. -/
noncomputable def fisherForm (p v : n → ℝ) : ℝ := v ⬝ᵥ fisherMatrix p *ᵥ v

/-- Total brightness of a vector of readings. -/
noncomputable def brightness (x : n → ℝ) : ℝ := ∑ i, x i

/-- The shares obtained by dividing by total brightness. -/
noncomputable def shares (x : n → ℝ) (i : n) : ℝ := x i / brightness x

/-- The two-channel signed share balance. -/
noncomputable def balance (p : Fin 2 → ℝ) : ℝ := p 0 - p 1

/-- The normalized two-channel log-determinant ledger. -/
noncomputable def matrixLedger (p : Fin 2 → ℝ) : ℝ :=
  -Real.log (4 * (shareMatrix p).det)

/-- The usual scalar ledger potential, included for the determinant comparison. -/
noncomputable def scalarLedgerPotential (Γ : ℝ) : ℝ :=
  -(1 / 2 : ℝ) * Real.log (1 - Γ^2)

/-- The determinant of a diagonal share matrix is the product of its shares. -/
theorem shareMatrix_det (p : n → ℝ) :
    (shareMatrix p).det = ∏ i, p i := by
  simp [shareMatrix]

/-- The determinant of the explicit Fisher matrix. -/
theorem fisherMatrix_det (p : n → ℝ) :
    (fisherMatrix p).det = ∏ i, (p i)⁻¹ := by
  simp [fisherMatrix]

/-- The share and Fisher matrices are two-sided inverses, left version. -/
theorem fisherMatrix_mul_shareMatrix (p : n → ℝ) (hp : ∀ i, p i ≠ 0) :
    fisherMatrix p * shareMatrix p = 1 := by
  rw [fisherMatrix, shareMatrix, Matrix.diagonal_mul_diagonal,
    ← Matrix.diagonal_one]
  congr 1
  funext i
  exact inv_mul_cancel₀ (hp i)

/-- The share and Fisher matrices are two-sided inverses, right version. -/
theorem shareMatrix_mul_fisherMatrix (p : n → ℝ) (hp : ∀ i, p i ≠ 0) :
    shareMatrix p * fisherMatrix p = 1 := by
  rw [fisherMatrix, shareMatrix, Matrix.diagonal_mul_diagonal,
    ← Matrix.diagonal_one]
  congr 1
  funext i
  exact mul_inv_cancel₀ (hp i)

/-- The matrix Fisher form is exactly the coordinate sum of squared steps
weighted by inverse shares.  No nonzero-denominator hypothesis is needed. -/
theorem fisherForm_eq_rawForm (p v : n → ℝ) :
    fisherForm p v = rawForm p v := by
  simp only [fisherForm, fisherMatrix, Matrix.mulVec_diagonal, dotProduct,
    rawForm, div_eq_mul_inv]
  apply Finset.sum_congr rfl
  intro i _hi
  ring

omit [Fintype n] in
/-- Nonnegative shares make the Fisher matrix positive semidefinite. -/
theorem fisherMatrix_posSemidef (p : n → ℝ) (hp : ∀ i, 0 ≤ p i) :
    (fisherMatrix p).PosSemidef := by
  apply Matrix.PosSemidef.diagonal
  intro i
  exact inv_nonneg.mpr (hp i)

omit [Fintype n] in
/-- Strictly positive shares make the Fisher matrix positive definite. -/
theorem fisherMatrix_posDef (p : n → ℝ) (hp : ∀ i, 0 < p i) :
    (fisherMatrix p).PosDef := by
  apply Matrix.PosDef.diagonal
  intro i
  exact inv_pos.mpr (hp i)

omit [DecidableEq n] in
/-- The raw form is nonnegative for positive readings. -/
theorem rawForm_nonneg (x v : n → ℝ) (hx : ∀ i, 0 < x i) :
    0 ≤ rawForm x v := by
  apply Finset.sum_nonneg
  intro i _hi
  exact div_nonneg (sq_nonneg (v i)) (hx i).le

/-- Positive-definiteness of the Fisher form in elementary coordinate form. -/
theorem fisherForm_eq_zero_iff (p v : n → ℝ) (hp : ∀ i, 0 < p i) :
    fisherForm p v = 0 ↔ v = 0 := by
  rw [fisherForm_eq_rawForm]
  constructor
  · intro h
    have hnonneg : ∀ i ∈ Finset.univ, 0 ≤ (v i)^2 / p i := by
      intro i _hi
      exact div_nonneg (sq_nonneg (v i)) (hp i).le
    have hz := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp
      (show (∑ i ∈ Finset.univ, (v i)^2 / p i) = 0 from h)
    funext i
    have hi : (v i)^2 / p i = 0 := hz i (Finset.mem_univ i)
    have hsq : (v i)^2 = 0 := by
      rcases div_eq_zero_iff.mp hi with hsq | hpi
      · exact hsq
      · exact False.elim ((ne_of_gt (hp i)) hpi)
    exact sq_eq_zero_iff.mp hsq
  · rintro rfl
    simp [rawForm]

/-- On the zero-sum tangent space, covariance exactly undoes the Fisher
matrix.  This is the finite colour analogue of the simplex pseudoinverse. -/
theorem covariance_mul_fisherVelocity (p u : n → ℝ)
    (hp : ∀ i, p i ≠ 0) (hu : ∑ i, u i = 0) :
    covariance p *ᵥ fisherVelocity p u = u := by
  have hdot : p ⬝ᵥ fisherVelocity p u = 0 := by
    calc
      p ⬝ᵥ fisherVelocity p u = ∑ i, u i := by
        simp only [dotProduct, fisherVelocity, fisherMatrix,
          Matrix.mulVec_diagonal]
        apply Finset.sum_congr rfl
        intro i _hi
        rw [← mul_assoc, mul_inv_cancel₀ (hp i), one_mul]
      _ = 0 := hu
  funext i
  rw [covariance, Matrix.sub_mulVec]
  simp only [Pi.sub_apply, Matrix.mulVec_diagonal, Matrix.vecMulVec_mulVec,
    Pi.smul_apply, op_smul_eq_mul]
  rw [hdot, mul_zero, sub_zero]
  simp [fisherVelocity, fisherMatrix, Matrix.mulVec_diagonal, hp]

/-- The Fisher form of a tangent equals the covariance quadratic form of its
Fisher velocity. -/
theorem fisherForm_eq_covariance (p u : n → ℝ)
    (hp : ∀ i, p i ≠ 0) (hu : ∑ i, u i = 0) :
    fisherForm p u =
      fisherVelocity p u ⬝ᵥ covariance p *ᵥ fisherVelocity p u := by
  rw [covariance_mul_fisherVelocity p u hp hu]
  exact dotProduct_comm _ _

/-- Positivity of the Fisher form, specialized from the raw coordinate sum. -/
theorem fisherForm_nonneg (p v : n → ℝ) (hp : ∀ i, 0 < p i) :
    0 ≤ fisherForm p v := by
  rw [fisherForm_eq_rawForm]
  exact rawForm_nonneg p v hp

omit [DecidableEq n] in
/-- Positive readings on a nonempty finite set have positive brightness. -/
theorem brightness_pos [Nonempty n] (x : n → ℝ) (hx : ∀ i, 0 < x i) :
    0 < brightness x := by
  apply Finset.sum_pos
  · intro i _hi
    exact hx i
  · exact Finset.univ_nonempty

omit [DecidableEq n] in
/-- Shares form a probability vector whenever total brightness is nonzero. -/
theorem shares_sum (x : n → ℝ) (hb : brightness x ≠ 0) :
    ∑ i, shares x i = 1 := by
  simp only [shares]
  rw [← Finset.sum_div]
  exact div_self hb

omit [DecidableEq n] in
/-- Positive readings have positive shares. -/
theorem shares_pos [Nonempty n] (x : n → ℝ) (hx : ∀ i, 0 < x i) :
    ∀ i, 0 < shares x i := by
  intro i
  exact div_pos (hx i) (brightness_pos x hx)

omit [DecidableEq n] in
/-- A common nonzero brightness factor does not change the shares. -/
theorem shares_scale (x : n → ℝ) (c : ℝ) (hc : c ≠ 0) :
    shares (c • x) = shares x := by
  funext i
  simp only [shares, brightness, Pi.smul_apply, smul_eq_mul]
  rw [← Finset.mul_sum, mul_div_mul_left _ _ hc]

omit [DecidableEq n] in
/-- The raw form scales by the inverse of a common reading factor.  This also
holds at scale zero, with Lean's total zero inverse. -/
theorem rawForm_scale (x v : n → ℝ) (c : ℝ) :
    rawForm (c • x) v = c⁻¹ * rawForm x v := by
  simp only [rawForm, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    div_eq_mul_inv, _root_.mul_inv_rev]
  apply Finset.sum_congr rfl
  intro i _hi
  ring

/-- Passing from readings to shares multiplies the raw quadratic form by
brightness.  The algebraic identity is valid without positivity assumptions. -/
theorem fisherForm_shares (x v : n → ℝ) :
    fisherForm (shares x) v = brightness x * rawForm x v := by
  rw [fisherForm_eq_rawForm]
  simp only [rawForm, shares, div_div_eq_mul_div, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  ring

/-- The Fisher form computed from shares is invariant under common nonzero
brightness rescaling. -/
theorem fisherForm_shares_scale (x v : n → ℝ) (c : ℝ) (hc : c ≠ 0) :
    fisherForm (shares (c • x)) v = fisherForm (shares x) v := by
  rw [shares_scale x c hc]

/-- Two-channel brightness is the sum of the two readings. -/
theorem brightness_two (x : Fin 2 → ℝ) : brightness x = x 0 + x 1 := by
  simp [brightness, Fin.sum_univ_two]

/-- Two-channel raw form, expanded coordinatewise. -/
theorem rawForm_two (x v : Fin 2 → ℝ) :
    rawForm x v = (v 0)^2 / x 0 + (v 1)^2 / x 1 := by
  simp [rawForm, Fin.sum_univ_two]

/-- Two-channel Fisher form, expanded coordinatewise. -/
theorem fisherForm_two (p v : Fin 2 → ℝ) :
    fisherForm p v = (v 0)^2 / p 0 + (v 1)^2 / p 1 := by
  rw [fisherForm_eq_rawForm, rawForm_two]

/-- The two-channel determinant is the product of the two shares. -/
theorem shareMatrix_det_two (p : Fin 2 → ℝ) :
    (shareMatrix p).det = p 0 * p 1 := by
  rw [shareMatrix_det]
  exact Fin.prod_univ_two p

/-- Normalization turns the determinant into the complement of squared balance. -/
theorem shareMatrix_det_balance (p : Fin 2 → ℝ) (hp : p 0 + p 1 = 1) :
    (shareMatrix p).det = (1 - (balance p)^2) / 4 := by
  rw [shareMatrix_det_two]
  unfold balance
  nlinarith

/-- At normalized shares, the wall is exactly determinant level one eighth. -/
theorem shareMatrix_det_wall_iff (p : Fin 2 → ℝ) (hp : p 0 + p 1 = 1) :
    (shareMatrix p).det = 1 / 8 ↔ (balance p)^2 = 1 / 2 := by
  rw [shareMatrix_det_balance p hp]
  constructor <;> intro h
  · nlinarith
  · rw [h]
    norm_num

/-- The normalized matrix ledger is the negative logarithm of the complement
of squared balance. -/
theorem matrixLedger_eq_neg_log (p : Fin 2 → ℝ) (hp : p 0 + p 1 = 1) :
    matrixLedger p = -Real.log (1 - (balance p)^2) := by
  unfold matrixLedger
  rw [shareMatrix_det_balance p hp]
  congr 2
  ring

/-- Hence the matrix ledger is twice the scalar ledger potential. -/
theorem matrixLedger_eq_two_scalarLedgerPotential (p : Fin 2 → ℝ)
    (hp : p 0 + p 1 = 1) :
    matrixLedger p = 2 * scalarLedgerPotential (balance p) := by
  rw [matrixLedger_eq_neg_log p hp]
  unfold scalarLedgerPotential
  ring

/-- Positive normalized shares make the matrix ledger nonnegative. -/
theorem matrixLedger_nonneg (p : Fin 2 → ℝ)
    (hp : ∀ i, 0 < p i) (hnorm : p 0 + p 1 = 1) :
    0 ≤ matrixLedger p := by
  have hprod : 0 < p 0 * p 1 := mul_pos (hp 0) (hp 1)
  have hprod_le : p 0 * p 1 ≤ 1 / 4 := by
    nlinarith [sq_nonneg (p 0 - p 1)]
  have hpos : 0 < 4 * (shareMatrix p).det := by
    rw [shareMatrix_det_two]
    positivity
  have hle : 4 * (shareMatrix p).det ≤ 1 := by
    rw [shareMatrix_det_two]
    nlinarith
  exact neg_nonneg.mpr (Real.log_nonpos hpos.le hle)

/-- For positive normalized shares, the matrix ledger vanishes exactly at zero
balance, equivalently at equal shares. -/
theorem matrixLedger_eq_zero_iff (p : Fin 2 → ℝ)
    (hp : ∀ i, 0 < p i) (hnorm : p 0 + p 1 = 1) :
    matrixLedger p = 0 ↔ balance p = 0 := by
  rw [matrixLedger_eq_neg_log p hnorm]
  have hpos : 0 < 1 - (balance p)^2 := by
    have hprod : 0 < p 0 * p 1 := mul_pos (hp 0) (hp 1)
    have hdet := shareMatrix_det_balance p hnorm
    rw [shareMatrix_det_two] at hdet
    nlinarith
  constructor
  · intro h
    have hlog : Real.log (1 - (balance p)^2) = 0 := by linarith
    have hone : 1 - (balance p)^2 = 1 := by
      rcases Real.log_eq_zero.mp hlog with hzero | hone | hneg
      · nlinarith
      · exact hone
      · nlinarith
    exact sq_eq_zero_iff.mp (by nlinarith)
  · intro h
    rw [h]
    norm_num

/-- At the wall, the normalized matrix ledger is exactly `log 2`. -/
theorem matrixLedger_at_wall (p : Fin 2 → ℝ) (hp : p 0 + p 1 = 1)
    (hb : (balance p)^2 = 1 / 2) : matrixLedger p = Real.log 2 := by
  rw [matrixLedger_eq_neg_log p hp, hb]
  have hhalf : 1 - (1 / 2 : ℝ) = (2 : ℝ)⁻¹ := by norm_num
  rw [hhalf, Real.log_inv]
  norm_num

end ElementalPeeling.LoopWall.FisherMatrix
