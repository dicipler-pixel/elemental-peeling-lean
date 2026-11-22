import Mathlib

/-!
# The ledger is additive over channels only in its matrix form

Direction B3 of the fourth round.  For diagonal positive blocks `a b : Fin n → ℝ` the matrix ledger
`Sm a b = log (∏ i, (a i + b i)/2) - (1/2) log (∏ i, a i) - (1/2) log (∏ i, b i)` is the sum of the
scalar ledgers of its channels (`Sm_eq_sum_scalar`), equals `Σ i, log cosh ((log (a i / b i))/2)`
(`Sm_eq_sum_log_cosh`), is nonnegative with equality exactly when the blocks agree (`Sm_nonneg`,
`Sm_eq_zero_iff`), and is additive over direct sums (`Sm_append`).

The scalar ledger itself is **not** additive in the spacing: `scalarLedger_not_additive` gives the
explicit witness `t₁ = t₂ = 2`, from `cosh 2 > cosh 1 ^ 2`.  So the channel-additive object is the
log-determinant ledger; `channel_additive_ledger` records that reading.

Written in the fourth parallel formalization round (swarm `smws625cs`, direction m8), recompiled and
reviewed here; namespace and header added, `#print axioms` lines removed.
-/

namespace ElementalPeeling.LoopWall.MatrixLedger

open scoped BigOperators
open Finset

/-- Signed logarithmic spacing of a peel step (the scalar-ledger coordinate). -/
noncomputable def t (I J : ℝ) : ℝ := Real.log (I / J)

/-- The one-channel arithmetic/geometric-mean ledger. -/
noncomputable def S (I J : ℝ) : ℝ :=
  Real.log ((I + J) / (2 * Real.sqrt (I * J)))

/-- The arithmetic/geometric mean ratio is `cosh` of half the log spacing.
This is the checked `LoopWall.ScalarLedger` calculation, reproduced here so
that this deliverable needs no separately compiled project module. -/
theorem mean_ratio_eq_cosh_half_t {I J : ℝ} (hI : 0 < I) (hJ : 0 < J) :
    (I + J) / (2 * Real.sqrt (I * J)) = Real.cosh (t I J / 2) := by
  have hz : 0 < I / J := div_pos hI hJ
  have hsI : 0 < Real.sqrt I := Real.sqrt_pos.2 hI
  have hsJ : 0 < Real.sqrt J := Real.sqrt_pos.2 hJ
  have hsqI : Real.sqrt I ^ 2 = I := Real.sq_sqrt hI.le
  have hsqJ : Real.sqrt J ^ 2 = J := Real.sq_sqrt hJ.le
  unfold t
  rw [Real.cosh_eq, Real.exp_neg, Real.exp_half, Real.exp_log hz,
    Real.sqrt_div hI.le, Real.sqrt_mul hI.le]
  field_simp [ne_of_gt hsI, ne_of_gt hsJ]
  nlinarith

/-- The scalar ledger is `log cosh` of half the logarithmic spacing. -/
theorem S_eq_log_cosh_half_t {I J : ℝ} (hI : 0 < I) (hJ : 0 < J) :
    S I J = Real.log (Real.cosh (t I J / 2)) := by
  unfold S
  rw [mean_ratio_eq_cosh_half_t hI hJ]

/-- The scalar ledger is nonnegative. -/
theorem S_nonneg {I J : ℝ} (hI : 0 < I) (hJ : 0 < J) : 0 ≤ S I J := by
  rw [S_eq_log_cosh_half_t hI hJ]
  exact Real.log_nonneg (Real.one_le_cosh _)

/-- The scalar ledger vanishes exactly when its two readings agree. -/
theorem S_eq_zero_iff {I J : ℝ} (hI : 0 < I) (hJ : 0 < J) :
    S I J = 0 ↔ I = J := by
  constructor
  · intro h
    rw [S_eq_log_cosh_half_t hI hJ] at h
    have hc : Real.cosh (t I J / 2) = 1 :=
      Real.eq_one_of_pos_of_log_eq_zero (Real.cosh_pos _) h
    have ht0 : t I J / 2 = 0 := by
      by_contra ht
      have hc1 : 1 < Real.cosh (t I J / 2) := Real.one_lt_cosh.2 ht
      linarith
    have hlog : Real.log (I / J) = 0 := by
      unfold t at ht0
      linarith
    have hratio : I / J = 1 :=
      Real.eq_one_of_pos_of_log_eq_zero (div_pos hI hJ) hlog
    exact (div_eq_one_iff_eq (ne_of_gt hJ)).1 hratio
  · intro h
    subst J
    rw [S_eq_log_cosh_half_t hI hI]
    simp [t]

/-- The log-determinant ledger of two positive diagonal matrices, written
explicitly in terms of their diagonal entries. -/
noncomputable def Sm {n : ℕ} (a b : Fin n → ℝ) : ℝ :=
  Real.log (∏ i, ((a i + b i) / 2)) -
    (1 / 2 : ℝ) * Real.log (∏ i, a i) -
    (1 / 2 : ℝ) * Real.log (∏ i, b i)

/-- The one-channel ledger in the coordinates used in `Sm`. -/
theorem S_eq_log_mean_sub_half_logs {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    S a b = Real.log ((a + b) / 2) -
      (1 / 2 : ℝ) * Real.log a - (1 / 2 : ℝ) * Real.log b := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hb0 : b ≠ 0 := ne_of_gt hb
  have hab : 0 < a * b := mul_pos ha hb
  have hsqrt : Real.sqrt (a * b) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hab)
  unfold S
  rw [Real.log_div (ne_of_gt (add_pos ha hb)) (by positivity),
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hsqrt,
    Real.log_sqrt hab.le, Real.log_mul ha0 hb0,
    Real.log_div (ne_of_gt (add_pos ha hb)) (by norm_num : (2 : ℝ) ≠ 0)]
  ring

/-- The scalar ledger is not additive when independent spacings are added.
Here both spacings are `2`; the inequality follows from `cosh 2 > cosh 1 ^ 2`. -/
theorem scalarLedger_not_additive :
    ∃ t₁ t₂ : ℝ,
      Real.log (Real.cosh ((t₁ + t₂) / 2)) ≠
        Real.log (Real.cosh (t₁ / 2)) + Real.log (Real.cosh (t₂ / 2)) := by
  refine ⟨2, 2, ?_⟩
  have hc : 1 < Real.cosh (1 : ℝ) := Real.one_lt_cosh.2 (by norm_num)
  have hs : 0 < Real.sinh (1 : ℝ) := Real.sinh_pos_iff.2 (by norm_num)
  have harg : Real.cosh (1 : ℝ) ^ 2 < Real.cosh 2 := by
    rw [show (2 : ℝ) = 2 * 1 by norm_num, Real.cosh_two_mul]
    nlinarith [sq_pos_of_pos hs]
  have hlog : Real.log (Real.cosh (1 : ℝ) ^ 2) < Real.log (Real.cosh 2) :=
    Real.log_lt_log (sq_pos_of_pos (lt_trans zero_lt_one hc)) harg
  rw [Real.log_pow] at hlog
  norm_num at hlog
  norm_num
  intro h
  nlinarith

/-- The diagonal log-determinant ledger is the sum of the scalar ledgers
of its channels. -/
theorem Sm_eq_sum_scalar {n : ℕ} (a b : Fin n → ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) :
    Sm a b = ∑ i, S (a i) (b i) := by
  have hlog_a : Real.log (∏ i, a i) = ∑ i, Real.log (a i) := by
    apply Real.log_prod
    intro i _
    exact ne_of_gt (ha i)
  have hlog_b : Real.log (∏ i, b i) = ∑ i, Real.log (b i) := by
    apply Real.log_prod
    intro i _
    exact ne_of_gt (hb i)
  have hlog_mean : Real.log (∏ i, ((a i + b i) / 2)) =
      ∑ i, Real.log ((a i + b i) / 2) := by
    apply Real.log_prod
    intro i _
    exact ne_of_gt (div_pos (add_pos (ha i) (hb i)) (by norm_num))
  unfold Sm
  rw [hlog_mean, hlog_a, hlog_b]
  symm
  calc
    (∑ i, S (a i) (b i)) =
        ∑ i, (Real.log ((a i + b i) / 2) -
          (1 / 2 : ℝ) * Real.log (a i) - (1 / 2 : ℝ) * Real.log (b i)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact S_eq_log_mean_sub_half_logs (ha i) (hb i)
    _ = (∑ i, Real.log ((a i + b i) / 2)) -
        (∑ i, (1 / 2 : ℝ) * Real.log (a i)) -
        (∑ i, (1 / 2 : ℝ) * Real.log (b i)) := by
      simp only [Finset.sum_sub_distrib]
    _ = _ := by simp only [Finset.mul_sum]

/-- The matrix ledger is the channel sum of `log cosh` of half the signed
logarithmic spacing, exactly as required by the scalar peel formula. -/
theorem Sm_eq_sum_log_cosh {n : ℕ} (a b : Fin n → ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) :
    Sm a b = ∑ i, Real.log (Real.cosh ((Real.log (a i / b i)) / 2)) := by
  rw [Sm_eq_sum_scalar a b ha hb]
  apply Finset.sum_congr rfl
  intro i _
  simpa [t] using S_eq_log_cosh_half_t (ha i) (hb i)

/-- Channelwise nonnegativity gives nonnegativity of the matrix ledger. -/
theorem Sm_nonneg {n : ℕ} (a b : Fin n → ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) : 0 ≤ Sm a b := by
  rw [Sm_eq_sum_scalar a b ha hb]
  exact Finset.sum_nonneg (fun i _ => S_nonneg (ha i) (hb i))

/-- Two positive diagonal matrices have zero ledger exactly when all their
diagonal entries, and hence the matrices themselves, agree. -/
theorem Sm_eq_zero_iff {n : ℕ} (a b : Fin n → ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) :
    Sm a b = 0 ↔ a = b := by
  constructor
  · intro h
    rw [Sm_eq_sum_scalar a b ha hb] at h
    have hz := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i (_ : i ∈ Finset.univ) => S_nonneg (ha i) (hb i))).1 h
    funext i
    exact (S_eq_zero_iff (ha i) (hb i)).1 (hz i (Finset.mem_univ i))
  · intro h
    subst b
    rw [Sm_eq_sum_scalar a a ha ha]
    apply Finset.sum_eq_zero
    intro i _
    exact (S_eq_zero_iff (ha i) (ha i)).2 rfl

/-- Additivity over direct sums of diagonal blocks. -/
theorem Sm_append {m n : ℕ} (a₁ b₁ : Fin m → ℝ) (a₂ b₂ : Fin n → ℝ)
    (ha₁ : ∀ i, 0 < a₁ i) (hb₁ : ∀ i, 0 < b₁ i)
    (ha₂ : ∀ i, 0 < a₂ i) (hb₂ : ∀ i, 0 < b₂ i) :
    Sm (Fin.append a₁ a₂) (Fin.append b₁ b₂) = Sm a₁ b₁ + Sm a₂ b₂ := by
  have ha : ∀ i, 0 < Fin.append a₁ a₂ i := by
    intro i
    exact Fin.addCases
      (fun j => by simpa using ha₁ j)
      (fun j => by simpa using ha₂ j) i
  have hb : ∀ i, 0 < Fin.append b₁ b₂ i := by
    intro i
    exact Fin.addCases
      (fun j => by simpa using hb₁ j)
      (fun j => by simpa using hb₂ j) i
  rw [Sm_eq_sum_scalar _ _ ha hb,
    Sm_eq_sum_scalar a₁ b₁ ha₁ hb₁,
    Sm_eq_sum_scalar a₂ b₂ ha₂ hb₂, Fin.sum_univ_add]
  simp

/-- The explicit product formula really is the stated log-determinant
formula for diagonal matrices. -/
theorem Sm_eq_diagonal_determinants {n : ℕ} (a b : Fin n → ℝ) :
    Sm a b = Real.log (Matrix.diagonal (fun i => (a i + b i) / 2)).det -
      (1 / 2 : ℝ) * Real.log (Matrix.diagonal a).det -
      (1 / 2 : ℝ) * Real.log (Matrix.diagonal b).det := by
  simp only [Sm, Matrix.det_diagonal]

/-- Summary: the channel-additive object is the diagonal log-determinant
ledger, and its channel summands are precisely the scalar peel ledgers. -/
theorem channel_additive_ledger {n : ℕ} (a b : Fin n → ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) :
    Sm a b = ∑ i, S (a i) (b i) := Sm_eq_sum_scalar a b ha hb

end ElementalPeeling.LoopWall.MatrixLedger
