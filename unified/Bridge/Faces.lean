import Mathlib
import LoopWall.Ledger
import LoopWall.Wall

/-!
# Bridge V — the Ramanujan faces are peel steps

Ramanujan's gamma-quotient continued fractions

`4 Γ((x+3)/4)² / Γ((x+1)/4)² = x + 1²/(2x + 3²/(2x + 5²/(2x + …)))`

have step matrices `M_n = [[0, (2n−1)²], [1, 2x]]`, characteristic roots `x ± s_n` with
`s_n = √(x² + (2n−1)²)`.  So each term is one face with step ratio `z_n = (s_n + x)/(s_n − x)`
and reflection

`Γ_n = x / √(x² + (2n−1)²)`.

That is the same `z`, `Γ`, wall algebra as every other leg of this body, with the fraction's own
parameter `x` playing the role of the charge.  The wall `Γ_n² = ½` is `2n − 1 = x`, so:

* **Brouncker, `x = 1`, first face:** exactly at the wall, `z₁ = 3 + 2√2`.  The document's
  headline exact statement, proved here.
* faces with `2n − 1 < x` are outside the wall, faces with `2n − 1 > x` inside it, and the
  crossing is between consecutive odd integers, so an integer `x` has a face exactly on the wall
  and a non-integer `x` does not.

The document's power law (error falling like `N^{-x}`) is the ledger sum
`Σ 2 artanh Γ_n ≈ x log N`, which is asymptotic and is *measured*, not proved here.
-/

namespace Unified.Bridge.Faces

open ElementalPeeling.LoopWall.Ledger (gam)

/-- The `n`-th face's reflection, `Γ_n = x / √(x² + (2n−1)²)`. -/
noncomputable def faceGamma (x : ℝ) (n : ℕ) : ℝ :=
  x / Real.sqrt (x ^ 2 + (2 * (n : ℝ) - 1) ^ 2)

/-- The `n`-th face's step ratio, `z_n = (s + x)/(s − x)` with `s = √(x² + (2n−1)²)`. -/
noncomputable def faceRatio (x : ℝ) (n : ℕ) : ℝ :=
  (Real.sqrt (x ^ 2 + (2 * (n : ℝ) - 1) ^ 2) + x) /
    (Real.sqrt (x ^ 2 + (2 * (n : ℝ) - 1) ^ 2) - x)

/-- The face's ratio is positive: a positive `x` is inside the root. -/
theorem faceRatio_pos (x : ℝ) (hx : 0 < x) (n : ℕ) (hn : 1 ≤ n) : 0 < faceRatio x n := by
  have hm : (0 : ℝ) < 2 * (n : ℝ) - 1 := by
    have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hs : x < Real.sqrt (x ^ 2 + (2 * (n : ℝ) - 1) ^ 2) := by
    rw [Real.lt_sqrt hx.le]
    nlinarith [sq_pos_of_pos hm]
  unfold faceRatio
  exact div_pos (by positivity) (by linarith)

/-- **The face reflection.**  `(z_n − 1)/(z_n + 1) = x/√(x² + (2n−1)²)`. -/
theorem faceRatio_eq_gam (x : ℝ) (hx : 0 < x) (n : ℕ) (hn : 1 ≤ n) :
    gam (faceRatio x n) = faceGamma x n := by
  have hm : (0 : ℝ) < 2 * (n : ℝ) - 1 := by
    have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hs2 : 0 < x ^ 2 + (2 * (n : ℝ) - 1) ^ 2 := by positivity
  have hs : 0 < Real.sqrt (x ^ 2 + (2 * (n : ℝ) - 1) ^ 2) := Real.sqrt_pos.2 hs2
  have hsx : x < Real.sqrt (x ^ 2 + (2 * (n : ℝ) - 1) ^ 2) := by
    rw [Real.lt_sqrt hx.le]
    nlinarith [sq_pos_of_pos hm]
  have hd : Real.sqrt (x ^ 2 + (2 * (n : ℝ) - 1) ^ 2) - x ≠ 0 := by linarith
  unfold gam faceRatio faceGamma
  have hz1 : 0 < (Real.sqrt (x ^ 2 + (2 * (n : ℝ) - 1) ^ 2) + x) /
      (Real.sqrt (x ^ 2 + (2 * (n : ℝ) - 1) ^ 2) - x) + 1 := by
    have hpos : 0 < (Real.sqrt (x ^ 2 + (2 * (n : ℝ) - 1) ^ 2) + x) /
        (Real.sqrt (x ^ 2 + (2 * (n : ℝ) - 1) ^ 2) - x) :=
      div_pos (by positivity) (by linarith)
    linarith
  rw [div_eq_div_iff (ne_of_gt hz1) (ne_of_gt hs)]
  field_simp
  ring

/-- **The wall on a face.**  `Γ_n² = ½` exactly when `(2n−1)² = x²`. -/
theorem faceGamma_sq_eq_half_iff (x : ℝ) (hx : 0 < x) (n : ℕ) :
    faceGamma x n ^ 2 = 1 / 2 ↔ (2 * (n : ℝ) - 1) ^ 2 = x ^ 2 := by
  have hs2 : 0 < x ^ 2 + (2 * (n : ℝ) - 1) ^ 2 := by positivity
  unfold faceGamma
  rw [div_pow, Real.sq_sqrt hs2.le]
  constructor
  · intro h
    field_simp at h
    nlinarith
  · intro h
    field_simp
    nlinarith

/-- **The odd-integer wall.**  For a positive `x`, a face is exactly on the wall when `2n−1 = x`;
there is at most one such face. -/
theorem faceGamma_sq_eq_half_iff_odd (x : ℝ) (hx : 0 < x) (n : ℕ) (hn : 1 ≤ n) :
    faceGamma x n ^ 2 = 1 / 2 ↔ 2 * (n : ℝ) - 1 = x := by
  rw [faceGamma_sq_eq_half_iff x hx n]
  have hm : (0 : ℝ) < 2 * (n : ℝ) - 1 := by
    have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  constructor
  · intro h
    nlinarith [sq_nonneg (2 * (n : ℝ) - 1 - x)]
  · intro h
    rw [h]

/-- A face is inside the disk for every positive `x`. -/
theorem faceGamma_lt_one (x : ℝ) (hx : 0 < x) (n : ℕ) (hn : 1 ≤ n) :
    faceGamma x n < 1 := by
  have hm : (0 : ℝ) < 2 * (n : ℝ) - 1 := by
    have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hs2 : 0 < x ^ 2 + (2 * (n : ℝ) - 1) ^ 2 := by positivity
  have hs : x < Real.sqrt (x ^ 2 + (2 * (n : ℝ) - 1) ^ 2) := by
    rw [Real.lt_sqrt hx.le]
    nlinarith [sq_pos_of_pos hm]
  unfold faceGamma
  rw [div_lt_one (Real.sqrt_pos.2 hs2)]
  exact hs

/-- **Brouncker's first face is exactly on the wall.**  At `x = 1`, `Γ₁² = ½` and
`z₁ = 3 + 2√2`.  This is the exact statement the session record singles out; it is the same
`3 + 2√2` as the loop wall of every other leg. -/
theorem brouncker_first_face :
    faceGamma 1 1 ^ 2 = 1 / 2 ∧ faceRatio 1 1 = 3 + 2 * Real.sqrt 2 := by
  have hs : Real.sqrt (1 ^ 2 + (2 * ((1 : ℕ) : ℝ) - 1) ^ 2) = Real.sqrt 2 := by norm_num
  constructor
  · unfold faceGamma
    rw [hs]
    have h2 : Real.sqrt 2 ≠ 0 := by positivity
    field_simp
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  · unfold faceRatio
    rw [hs]
    have h2 : Real.sqrt 2 - 1 ≠ 0 := by
      have : (1 : ℝ) < Real.sqrt 2 := by
        rw [show (1 : ℝ) = Real.sqrt 1 by simp]
        exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
      linarith
    field_simp
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

end Unified.Bridge.Faces
