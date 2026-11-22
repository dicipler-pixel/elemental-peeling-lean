import Mathlib

/-!
# Polarizer ports, and the wall at forty-five degrees

Direction C5 of the fourth round.  For a retardance `δ` the crossed and parallel port intensities
are `Ec δ = sin (δ/2)^2` and `Ep δ = cos (δ/2)^2`: they sum to one (`crossed_add_parallel`), are
nonnegative, and their signed balance is `Ep − Ec = cos δ` (`parallel_sub_crossed`).  With the
documented orientation `portPeel crossed parallel = (parallel − crossed)/(crossed + parallel)`, the
peel of the two ports is `cos δ` (`portPeel_eq_cos`).  The wall is therefore a phase:
`(Ep − Ec)^2 = 1/2 ↔ cos δ^2 = 1/2`, and on `[0, π]` that is exactly `δ = π/4` or `3π/4`
(`wall_angles`); the "secondary" at balance `1/√2` is `δ = π/4` (`secondary_angle`,
`secondary_balance_angle`).

Written in the fourth parallel formalization round (swarm `smws625cs`, direction m7), recompiled and
reviewed here; namespace and header added, `#print axioms` lines removed.
-/

namespace ElementalPeeling.LoopWall.PolarizerPorts

open Set

/-- Crossed-port intensity at relative phase `δ`. -/
noncomputable def Ec (δ : ℝ) : ℝ := Real.sin (δ / 2) ^ 2

/-- Parallel-port intensity at relative phase `δ`. -/
noncomputable def Ep (δ : ℝ) : ℝ := Real.cos (δ / 2) ^ 2

/-- The peel of two readings, with the second reading in the numerator. -/
noncomputable def portPeel (crossed parallel : ℝ) : ℝ :=
  (parallel - crossed) / (crossed + parallel)

/-- The two port intensities are normalized. -/
theorem crossed_add_parallel (δ : ℝ) : Ec δ + Ep δ = 1 := by
  exact Real.sin_sq_add_cos_sq (δ / 2)

/-- Crossed intensity is nonnegative. -/
theorem crossed_nonneg (δ : ℝ) : 0 ≤ Ec δ := by
  exact sq_nonneg _

/-- Parallel intensity is nonnegative. -/
theorem parallel_nonneg (δ : ℝ) : 0 ≤ Ep δ := by
  exact sq_nonneg _

/-- The signed port balance is the cosine of the relative phase. -/
theorem parallel_sub_crossed (δ : ℝ) : Ep δ - Ec δ = Real.cos δ := by
  have hcos := Real.cos_two_mul (δ / 2)
  have hsum := Real.sin_sq_add_cos_sq (δ / 2)
  rw [show 2 * (δ / 2) = δ by ring] at hcos
  dsimp [Ec, Ep]
  nlinarith

/-- Consequently the normalized port peel is `cos δ`. -/
theorem portPeel_eq_cos (δ : ℝ) : portPeel (Ec δ) (Ep δ) = Real.cos δ := by
  rw [portPeel, crossed_add_parallel, parallel_sub_crossed]
  norm_num

/-- Squaring the balance gives the two possible wall signs. -/
theorem wall_balance_sq (δ : ℝ) :
    (Ep δ - Ec δ) ^ 2 = 1 / 2 ↔ Real.cos δ ^ 2 = 1 / 2 := by
  rw [parallel_sub_crossed]

/-- On `[0, π]`, the two wall phases are exactly `π/4` and `3π/4`. -/
theorem wall_angles {δ : ℝ} (hδ0 : 0 ≤ δ) (hδπ : δ ≤ Real.pi) :
    Real.cos δ ^ 2 = 1 / 2 ↔ δ = Real.pi / 4 ∨ δ = 3 * Real.pi / 4 := by
  have hsqrt : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hcos3 : Real.cos (3 * Real.pi / 4) = -Real.sqrt 2 / 2 := by
    rw [show 3 * Real.pi / 4 = Real.pi - Real.pi / 4 by ring,
      Real.cos_pi_sub, Real.cos_pi_div_four]
    ring
  constructor
  · intro h
    have hfactor :
        (Real.cos δ - Real.sqrt 2 / 2) * (Real.cos δ + Real.sqrt 2 / 2) = 0 := by
      nlinarith
    rcases mul_eq_zero.mp hfactor with hpos | hneg
    · left
      apply Real.injOn_cos ⟨hδ0, hδπ⟩
        ⟨by positivity, by linarith [Real.pi_pos]⟩
      rw [Real.cos_pi_div_four]
      linarith
    · right
      apply Real.injOn_cos ⟨hδ0, hδπ⟩
        ⟨by positivity, by linarith [Real.pi_pos]⟩
      rw [hcos3]
      linarith
  · rintro (rfl | rfl)
    · rw [Real.cos_pi_div_four]
      nlinarith
    · rw [hcos3]
      nlinarith

/-- The squared port balance is at the wall precisely at the two wall phases. -/
theorem wall_ports {δ : ℝ} (hδ0 : 0 ≤ δ) (hδπ : δ ≤ Real.pi) :
    (Ep δ - Ec δ) ^ 2 = 1 / 2 ↔
      δ = Real.pi / 4 ∨ δ = 3 * Real.pi / 4 := by
  rw [wall_balance_sq, wall_angles hδ0 hδπ]

/-- A positive wall-valued secondary peel selects the phase `π/4`. -/
theorem secondary_angle {δ : ℝ} (hδ0 : 0 ≤ δ) (hδπ : δ ≤ Real.pi) :
    portPeel (Ec δ) (Ep δ) = 1 / Real.sqrt 2 ↔ δ = Real.pi / 4 := by
  have hsqrt0 : Real.sqrt 2 ≠ 0 := by positivity
  have hsqrt : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hinv : 1 / Real.sqrt 2 = Real.sqrt 2 / 2 := by
    field_simp
    nlinarith
  rw [portPeel_eq_cos]
  constructor
  · intro h
    apply Real.injOn_cos ⟨hδ0, hδπ⟩
      ⟨by positivity, by linarith [Real.pi_pos]⟩
    rw [Real.cos_pi_div_four, h, hinv]
  · rintro rfl
    rw [Real.cos_pi_div_four, hinv]

/-- Equivalently, the unscaled signed balance of a secondary selects `π/4`. -/
theorem secondary_balance_angle {δ : ℝ} (hδ0 : 0 ≤ δ) (hδπ : δ ≤ Real.pi) :
    Ep δ - Ec δ = 1 / Real.sqrt 2 ↔ δ = Real.pi / 4 := by
  simpa only [parallel_sub_crossed, portPeel_eq_cos] using secondary_angle hδ0 hδπ


end ElementalPeeling.LoopWall.PolarizerPorts
