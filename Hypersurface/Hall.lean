import Mathlib

set_option autoImplicit false

/-!
A declared real, quasistatic constitutive model. These are algebraic identities
and inequalities, not a microscopic derivation of a material Hall coefficient.
The exact expansion specifies the differential without importing a derivative.
CURRENT STATUS: uncompiled candidate, not a Lean-certified result.
-/
namespace Hypersurface

def hallX (σ χ x y : ℝ) : ℝ := σ * x - χ * x * y
def hallY (σ χ x y : ℝ) : ℝ := σ * y + χ * x ^ 2

theorem hall_power (σ χ x y : ℝ) :
    x * hallX σ χ x y + y * hallY σ χ x y = σ * (x^2 + y^2) := by
  unfold hallX hallY
  ring

theorem hall_power_nonnegative (σ χ x y : ℝ) (hσ : 0 ≤ σ) :
    0 ≤ x * hallX σ χ x y + y * hallY σ χ x y := by
  rw [hall_power]
  exact mul_nonneg hσ (add_nonneg (sq_nonneg x) (sq_nonneg y))

theorem hall_expand_x (σ χ b t x y : ℝ) :
    hallX σ χ (b + t*x) (t*y) =
    hallX σ χ b 0 + t*(σ*x - χ*b*y) + t^2*(-χ*x*y) := by
  unfold hallX
  ring

theorem hall_expand_y (σ χ b t x y : ℝ) :
    hallY σ χ (b + t*x) (t*y) =
    hallY σ χ b 0 + t*(σ*y + 2*χ*b*x) + t^2*(χ*x^2) := by
  unfold hallY
  ring

def incrementalForm (σ c x y : ℝ) : ℝ := σ*(x^2+y^2)+c*x*y

theorem differential_pairing (σ χ b x y : ℝ) :
    x*(σ*x-χ*b*y)+y*(σ*y+2*χ*b*x) = incrementalForm σ (χ*b) x y := by
  unfold incrementalForm
  ring

theorem incremental_diagonalization (σ c x y : ℝ) :
    incrementalForm σ c x y =
      (2*σ+c)/4*(x+y)^2 + (2*σ-c)/4*(x-y)^2 := by
  unfold incrementalForm
  ring

theorem incremental_nonnegative (σ c x y : ℝ)
    (hp : 0 ≤ 2*σ+c) (hm : 0 ≤ 2*σ-c) :
    0 ≤ incrementalForm σ c x y := by
  rw [incremental_diagonalization]
  apply add_nonneg
  · exact mul_nonneg (div_nonneg hp (by norm_num)) (sq_nonneg (x+y))
  · exact mul_nonneg (div_nonneg hm (by norm_num)) (sq_nonneg (x-y))

theorem incremental_negative_witness (σ c : ℝ) (h : 2*σ<c) :
    incrementalForm σ c 1 (-1) < 0 := by
  unfold incrementalForm
  nlinarith

theorem explicit_negative_control : incrementalForm 1 3 1 (-1) = -1 := by
  norm_num [incrementalForm]

theorem bias_power_cancellation (χ b x y : ℝ) :
    x*(-χ*b*y) + y*(2*χ*b*x) + b*(-χ*x*y) = 0 := by
  ring

end Hypersurface
