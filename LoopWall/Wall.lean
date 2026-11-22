import Mathlib
import LoopWall.Ledger

/-!
# The wall as an equality, and the two reciprocal ratios

`LoopWall.Elements.wall_quadratic` compares `Γ²` with `1/2` by a strict inequality.  This module
records the equality case: over the positive reals the wall is exactly `z = 3 ± 2√2`, and the two
roots are reciprocal, so the wall "cuts the positive real ray at two reciprocal ratios" (the
paper's phrase).  Nothing here depends on the archive.
-/

namespace ElementalPeeling.LoopWall.Wall

open ElementalPeeling.LoopWall.Ledger (gam)

/-- **The wall, as an equality.**  For a positive ratio, `Γ² = 1/2` exactly at the two loop-wall
ratios. -/
theorem wall_eq_iff (z : ℝ) (hz : 0 < z) :
    gam z * gam z = 1 / 2 ↔
      z = 3 + 2 * Real.sqrt 2 ∨ z = 3 - 2 * Real.sqrt 2 := by
  have hz1 : z + 1 ≠ 0 := by positivity
  have hs : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hkey : gam z * gam z = 1 / 2 ↔ z ^ 2 - 6 * z + 1 = 0 := by
    rw [show gam z = (z - 1) / (z + 1) from rfl, div_mul_div_comm,
      div_eq_div_iff (by positivity) (by norm_num : (2 : ℝ) ≠ 0)]
    constructor <;> intro h <;> nlinarith
  rw [hkey]
  constructor
  · intro h
    have hfac : z ^ 2 - 6 * z + 1 =
        (z - (3 + 2 * Real.sqrt 2)) * (z - (3 - 2 * Real.sqrt 2)) := by
      nlinarith
    rw [hfac] at h
    rcases mul_eq_zero.mp h with h' | h'
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  · rintro (rfl | rfl) <;> nlinarith

/-- The two wall ratios are reciprocal: their product is one.  This is why the wall meets the
positive real ray twice, once below one and once above it. -/
theorem wall_ratios_reciprocal :
    (3 + 2 * Real.sqrt 2) * (3 - 2 * Real.sqrt 2) = 1 := by
  have hs : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  nlinarith

/-- The upper wall ratio is the squared hyperbolic-cotangent form the paper quotes numerically. -/
theorem wall_ratio_numerals :
    (5.8284 : ℝ) < 3 + 2 * Real.sqrt 2 ∧ 3 + 2 * Real.sqrt 2 < 5.8285 := by
  have hlo : (1.41421 : ℝ) < Real.sqrt 2 := (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  have hhi : Real.sqrt 2 < (1.41422 : ℝ) := (Real.sqrt_lt (by norm_num) (by norm_num)).2 (by norm_num)
  constructor <;> linarith

/-- The upper wall ratio is outside the wall and the lower one is outside on the reverse branch,
so both roots of the equality are boundary points rather than interior points. -/
theorem wall_ratios_are_boundary :
    gam (3 + 2 * Real.sqrt 2) * gam (3 + 2 * Real.sqrt 2) = 1 / 2 ∧
      gam (3 - 2 * Real.sqrt 2) * gam (3 - 2 * Real.sqrt 2) = 1 / 2 := by
  have hp : 0 < (3 : ℝ) + 2 * Real.sqrt 2 := by positivity
  have hm : 0 < (3 : ℝ) - 2 * Real.sqrt 2 := by
    have : Real.sqrt 2 < (1.5 : ℝ) := (Real.sqrt_lt (by norm_num) (by norm_num)).2 (by norm_num)
    linarith
  exact ⟨(wall_eq_iff _ hp).2 (Or.inl rfl), (wall_eq_iff _ hm).2 (Or.inr rfl)⟩

end ElementalPeeling.LoopWall.Wall
