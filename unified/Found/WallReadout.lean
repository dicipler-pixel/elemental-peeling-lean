import LoopWall.CompositionBridge
import LoopWall.Wall

/-!
# The exact determinant/wall interface

The definitions used here are the repository's own definitions:
`FisherMatrix.lean:26,51-56`, `CompositionBridge.lean:118,123-124,244-245`.
In particular, `blockDet` is a product of one-block normalized determinants.
-/

namespace ElementalPeeling.LoopWall.WallReadoutInterface

open ElementalPeeling.LoopWall.FisherMatrix
open ElementalPeeling.LoopWall.CompositionBridge
open ElementalPeeling.LoopWall.Ledger (gam)

noncomputable section

/-- The one-block identity under the normalized-balance chart. No positivity is needed. -/
theorem four_det_eq_one_sub_gam_sq (p : Fin 2 → ℝ) (z : ℝ)
    (hnorm : p 0 + p 1 = 1) (hbalance : balance p = gam z) :
    4 * (shareMatrix p).det = 1 - (gam z) ^ 2 := by
  rw [shareMatrix_det_balance p hnorm, hbalance]
  ring

/-- Without assuming normalization, the identity is equivalent to `(p 0 + p 1)^2 = 1`.
Therefore either normalization to sum `1` or normalization to sum `-1` suffices, and neither
possibility requires positivity. -/
theorem four_det_eq_one_sub_gam_sq_iff (p : Fin 2 → ℝ) (z : ℝ)
    (hbalance : balance p = gam z) :
    4 * (shareMatrix p).det = 1 - (gam z) ^ 2 ↔ (p 0 + p 1) ^ 2 = 1 := by
  rw [shareMatrix_det_two]
  have hb : gam z = p 0 - p 1 := by
    simpa only [balance] using hbalance.symm
  rw [hb]
  constructor <;> intro h <;> nlinarith

/-- Equivalently, the physical determinant is one quarter of the complement. -/
theorem det_eq_one_sub_gam_sq_div_four (p : Fin 2 → ℝ) (z : ℝ)
    (hnorm : p 0 + p 1 = 1) (hbalance : balance p = gam z) :
    (shareMatrix p).det = (1 - (gam z) ^ 2) / 4 := by
  rw [shareMatrix_det_balance p hnorm, hbalance]

/-- The prescribed-balance shares give a completely hypothesis-free realization. -/
theorem normalizedDet_sharesOfBalance_gam (z : ℝ) :
    normalizedDet (sharesOfBalance (gam z)) = 1 - (gam z) ^ 2 := by
  rw [normalizedDet_eq_one_sub_balance_sq _ (sharesOfBalance_sum (gam z)),
    balance_sharesOfBalance]

/-- `blockDet` reduces to the advertised `4 det` only for a singleton family. -/
theorem blockDet_singleton (p : Fin 2 → ℝ) :
    blockDet (fun _ : Fin 1 => p) = 4 * (shareMatrix p).det := by
  simp [blockDet, normalizedDet]

/-- If all blocks have the same balance, `blockDet` is a power, not one complement. -/
theorem blockDet_eq_pow_of_constant_balance {n : ℕ} (p : Fin n → Fin 2 → ℝ) (Γ : ℝ)
    (hnorm : ∀ i, p i 0 + p i 1 = 1) (hbalance : ∀ i, balance (p i) = Γ) :
    blockDet p = (1 - Γ ^ 2) ^ n := by
  unfold blockDet
  have hfactor (i : Fin n) : normalizedDet (p i) = 1 - Γ ^ 2 := by
    rw [normalizedDet_eq_one_sub_balance_sq _ (hnorm i), hbalance i]
  simp_rw [hfactor]
  simp

/-- An explicit two-block counterexample to identifying `blockDet` with `1-Γ²`.
Each block is at the wall, so the block product is `1/4`, while `1-Γ² = 1/2`. -/
theorem two_wall_blocks_refute_single_block_identity :
    let p : Fin 2 → Fin 2 → ℝ :=
      fun _ => sharesOfBalance ElementalPeeling.LoopWall.PeelPotential.wall
    blockDet p = 1 / 4 ∧ blockDet p ≠
      1 - ElementalPeeling.LoopWall.PeelPotential.wall ^ 2 := by
  dsimp only
  rw [blockDet_eq_pow_of_constant_balance _
    ElementalPeeling.LoopWall.PeelPotential.wall
    (fun _ => sharesOfBalance_sum _) (fun _ => balance_sharesOfBalance _),
    ElementalPeeling.LoopWall.PeelPotential.wall_sq]
  norm_num

/-- At normalized shares with balance `gam z`, the wall is exactly determinant `1/8`. -/
theorem det_eighth_iff_gam_wall (p : Fin 2 → ℝ) (z : ℝ)
    (hnorm : p 0 + p 1 = 1) (hbalance : balance p = gam z) :
    (shareMatrix p).det = 1 / 8 ↔ (gam z) ^ 2 = 1 / 2 := by
  rw [shareMatrix_det_wall_iff p hnorm, hbalance]

/-- Degeneracy of the determinant is exactly unit absolute balance. Again no positivity
hypothesis is needed for this purely algebraic equivalence. -/
theorem det_zero_iff_abs_gam_eq_one (p : Fin 2 → ℝ) (z : ℝ)
    (hnorm : p 0 + p 1 = 1) (hbalance : balance p = gam z) :
    (shareMatrix p).det = 0 ↔ |gam z| = 1 := by
  rw [shareMatrix_det_balance p hnorm, hbalance]
  constructor
  · intro hdet
    have hsq : (gam z) ^ 2 = 1 := by nlinarith
    have habs_sq : |gam z| ^ 2 = 1 := by nlinarith [sq_abs (gam z)]
    nlinarith [abs_nonneg (gam z)]
  · intro habs
    have hsq : (gam z) ^ 2 = 1 := by nlinarith [sq_abs (gam z)]
    rw [hsq]
    norm_num

/-- Positive peel ratios lie strictly inside the unit reflection interval. -/
theorem abs_gam_lt_one_of_pos {z : ℝ} (hz : 0 < z) : |gam z| < 1 := by
  rw [abs_lt]
  have hden : 0 < z + 1 := by positivity
  constructor
  · rw [gam]
    apply (lt_div_iff₀ hden).2
    nlinarith
  · rw [gam]
    apply (div_lt_iff₀ hden).2
    nlinarith

/-- Hence no genuine positive peel ratio reaches the degenerate determinant endpoint. -/
theorem det_ne_zero_of_pos (p : Fin 2 → ℝ) {z : ℝ} (hz : 0 < z)
    (hnorm : p 0 + p 1 = 1) (hbalance : balance p = gam z) :
    (shareMatrix p).det ≠ 0 := by
  intro hdet
  have habs := (det_zero_iff_abs_gam_eq_one p z hnorm hbalance).mp hdet
  exact (ne_of_lt (abs_gam_lt_one_of_pos hz)) habs

private theorem upperWall_pos : 0 < (3 : ℝ) + 2 * Real.sqrt 2 := by
  positivity

private theorem lowerWall_pos : 0 < (3 : ℝ) - 2 * Real.sqrt 2 := by
  have hs : Real.sqrt 2 < (1.5 : ℝ) :=
    (Real.sqrt_lt (by norm_num) (by norm_num)).2 (by norm_num)
  linarith

private theorem lowerWall_log :
    Real.log (3 - 2 * Real.sqrt 2) = -Real.log (3 + 2 * Real.sqrt 2) := by
  have hrecip : 3 - 2 * Real.sqrt 2 = (3 + 2 * Real.sqrt 2)⁻¹ :=
    eq_inv_of_mul_eq_one_right ElementalPeeling.LoopWall.Wall.wall_ratios_reciprocal
  rw [hrecip, Real.log_inv]

private theorem upperWall_log_nonneg : 0 ≤ Real.log (3 + 2 * Real.sqrt 2) := by
  apply Real.log_nonneg
  have hs : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  linarith

/-- The two reciprocal wall ratios are precisely the two solutions of the absolute-log
equation. This avoids incorrectly discarding the lower, reciprocal branch. -/
theorem wall_ratios_iff_abs_log (z : ℝ) (hz : 0 < z) :
    z = 3 + 2 * Real.sqrt 2 ∨ z = 3 - 2 * Real.sqrt 2 ↔
      |Real.log z| = Real.log (3 + 2 * Real.sqrt 2) := by
  constructor
  · rintro (rfl | rfl)
    · exact abs_of_nonneg upperWall_log_nonneg
    · rw [lowerWall_log, abs_neg]
      exact abs_of_nonneg upperWall_log_nonneg
  · intro h
    rcases (abs_eq upperWall_log_nonneg).mp h with hplus | hminus
    · left
      exact Real.log_injOn_pos hz upperWall_pos hplus
    · right
      apply Real.log_injOn_pos hz lowerWall_pos
      rw [lowerWall_log]
      exact hminus

/-- Quantised-ledger form of the wall, including both signs of the log ledger. -/
theorem gam_wall_iff_abs_log (z : ℝ) (hz : 0 < z) :
    (gam z) ^ 2 = 1 / 2 ↔ |Real.log z| = Real.log (3 + 2 * Real.sqrt 2) := by
  rw [pow_two, ElementalPeeling.LoopWall.Wall.wall_eq_iff z hz,
    wall_ratios_iff_abs_log z hz]

/-- On the rising side, the absolute value disappears and the unique wall ratio is the upper
root `3 + 2√2`. -/
theorem gam_wall_iff_upper_root_of_one_le (z : ℝ) (hz : 0 < z) (hz1 : 1 ≤ z) :
    (gam z) ^ 2 = 1 / 2 ↔ z = 3 + 2 * Real.sqrt 2 := by
  rw [gam_wall_iff_abs_log z hz, abs_of_nonneg (Real.log_nonneg hz1)]
  constructor
  · intro h
    exact Real.log_injOn_pos hz upperWall_pos h
  · intro h
    rw [h]

/-- The determinant and logarithmic formulations are therefore identical. -/
theorem det_eighth_iff_abs_log (p : Fin 2 → ℝ) (z : ℝ) (hz : 0 < z)
    (hnorm : p 0 + p 1 = 1) (hbalance : balance p = gam z) :
    (shareMatrix p).det = 1 / 8 ↔
      |Real.log z| = Real.log (3 + 2 * Real.sqrt 2) := by
  rw [det_eighth_iff_gam_wall p z hnorm hbalance, gam_wall_iff_abs_log z hz]

/-- The upper-root-only assertion is valid only after imposing the rising-side condition.
The lower positive root is a second wall point and is different from the upper root. -/
theorem lower_wall_refutes_upper_only_without_branch :
    (gam (3 - 2 * Real.sqrt 2)) ^ 2 = 1 / 2 ∧
      3 - 2 * Real.sqrt 2 ≠ 3 + 2 * Real.sqrt 2 := by
  constructor
  · have h := (ElementalPeeling.LoopWall.Wall.wall_eq_iff _ lowerWall_pos).2 (Or.inr rfl)
    simpa only [pow_two] using h
  · have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    nlinarith

end

end ElementalPeeling.LoopWall.WallReadoutInterface
