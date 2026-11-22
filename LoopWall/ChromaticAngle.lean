import Mathlib

/-!
# The peel is minus the cosine of the chromatic angle, and the wall is 45 degrees

Direction C3 of the fourth round.  With shares `p 0 = sin (φ/2)^2`, `p 1 = cos (φ/2)^2`, the
balance `p 0 - p 1` equals `-cos φ`, and `share_balance_eq_peel`/`peel_eq_neg_cos` identify it with
the peel of the two readings: `peel m p = -cos φ`.  Hence `peel_sq_one_half_iff_wall`: on
`[0, π]`, `Γ^2 = 1/2` iff the chromatic angle is `π/4` or `3π/4`.  The projective distance is the
peel distance (`peelDistance_eq_abs_log_div`, `peelDistance_ratios`).

Written in the fourth parallel formalization round (swarm `smws625cs`, direction m2),
recompiled and reviewed here; namespace and header added, `#print axioms` lines removed.
-/

namespace ElementalPeeling.LoopWall.ChromaticAngle

open Real

/-- The first share in the two-channel chromatic parametrization. -/
noncomputable def shareZero (φ : ℝ) : ℝ := Real.sin (φ / 2) ^ 2

/-- The second share in the two-channel chromatic parametrization. -/
noncomputable def shareOne (φ : ℝ) : ℝ := Real.cos (φ / 2) ^ 2

/-- The peel coordinate of two readings. -/
noncomputable def peel (m p : ℝ) : ℝ := (m - p) / (m + p)

/-- Signed logarithmic spacing of a colour ratio. -/
noncomputable def signedSpacing (z : ℝ) : ℝ := Real.log z

/-- Projective (Hilbert) distance of two colour ratios. -/
noncomputable def peelDistance (z₁ z₂ : ℝ) : ℝ := |signedSpacing z₁ - signedSpacing z₂|

/-- The two chromatic shares are normalized. -/
theorem shareZero_add_shareOne (φ : ℝ) : shareZero φ + shareOne φ = 1 := by
  exact Real.sin_sq_add_cos_sq (φ / 2)

/-- Share balance is minus the cosine of the chromatic angle. -/
theorem shareZero_sub_shareOne (φ : ℝ) : shareZero φ - shareOne φ = -Real.cos φ := by
  have h := Real.cos_two_mul' (φ / 2)
  have harg : 2 * (φ / 2) = φ := by ring
  rw [harg] at h
  dsimp [shareZero, shareOne]
  nlinarith

/-- Positive readings with first share `m / (m + p)` realize the share balance as their peel. -/
theorem share_balance_eq_peel {φ m p : ℝ} (hm : 0 < m) (hp : 0 < p)
    (hzero : shareZero φ = m / (m + p)) :
    shareZero φ - shareOne φ = peel m p := by
  have hnorm := shareZero_add_shareOne φ
  have hmp : m + p ≠ 0 := ne_of_gt (add_pos hm hp)
  calc
    shareZero φ - shareOne φ = 2 * shareZero φ - 1 := by nlinarith
    _ = 2 * (m / (m + p)) - 1 := by rw [hzero]
    _ = peel m p := by
      dsimp [peel]
      field_simp
      ring

/-- Under the reading-share identification, peel is exactly minus the chromatic cosine. -/
theorem peel_eq_neg_cos {φ m p : ℝ} (hm : 0 < m) (hp : 0 < p)
    (hzero : shareZero φ = m / (m + p)) : peel m p = -Real.cos φ := by
  rw [← share_balance_eq_peel hm hp hzero]
  exact shareZero_sub_shareOne φ

/-- The wall equation for peel is equivalent to the squared-cosine equation. -/
theorem peel_sq_one_half_iff_cos_sq {Γ φ : ℝ} (hΓ : Γ = -Real.cos φ) :
    Γ ^ 2 = 1 / 2 ↔ Real.cos φ ^ 2 = 1 / 2 := by
  rw [hΓ, neg_sq]

/-- On `[0, π]`, the squared-cosine wall equation has exactly the two angles `π/4` and `3π/4`. -/
theorem cos_sq_one_half_iff_wall {φ : ℝ} (hφ0 : 0 ≤ φ) (hφπ : φ ≤ Real.pi) :
    Real.cos φ ^ 2 = 1 / 2 ↔ φ = Real.pi / 4 ∨ φ = 3 * Real.pi / 4 := by
  have hsqrt : (Real.sqrt 2 / 2) ^ 2 = 1 / 2 := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hcos3 : Real.cos (3 * Real.pi / 4) = -(Real.sqrt 2 / 2) := by
    have hangle : 3 * Real.pi / 4 = Real.pi - Real.pi / 4 := by ring
    rw [hangle, Real.cos_pi_sub, Real.cos_pi_div_four]
  have hmem : φ ∈ Set.Icc (0 : ℝ) Real.pi := ⟨hφ0, hφπ⟩
  have hmem4 : Real.pi / 4 ∈ Set.Icc (0 : ℝ) Real.pi := by
    constructor
    · positivity
    · nlinarith [Real.pi_pos]
  have hmem3 : 3 * Real.pi / 4 ∈ Set.Icc (0 : ℝ) Real.pi := by
    constructor
    · positivity
    · nlinarith [Real.pi_pos]
  constructor
  · intro h
    have hs : Real.cos φ ^ 2 = (Real.sqrt 2 / 2) ^ 2 := h.trans hsqrt.symm
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with hpos | hneg
    · left
      apply Real.injOn_cos hmem hmem4
      rw [Real.cos_pi_div_four]
      exact hpos
    · right
      apply Real.injOn_cos hmem hmem3
      rw [hcos3]
      exact hneg
  · rintro (rfl | rfl)
    · rw [Real.cos_pi_div_four]
      exact hsqrt
    · rw [hcos3, neg_sq]
      exact hsqrt

/-- The absolute peel wall has exactly the two stated chromatic angles. -/
theorem peel_sq_one_half_iff_wall {Γ φ : ℝ} (hΓ : Γ = -Real.cos φ)
    (hφ0 : 0 ≤ φ) (hφπ : φ ≤ Real.pi) :
    Γ ^ 2 = 1 / 2 ↔ φ = Real.pi / 4 ∨ φ = 3 * Real.pi / 4 :=
  (peel_sq_one_half_iff_cos_sq hΓ).trans (cos_sq_one_half_iff_wall hφ0 hφπ)

/-- The difference of signed logarithmic spacings is the logarithm of the ratio. -/
theorem abs_log_sub_eq_abs_log_div {z₁ z₂ : ℝ} (hz₁ : 0 < z₁) (hz₂ : 0 < z₂) :
    |Real.log z₁ - Real.log z₂| = |Real.log (z₁ / z₂)| := by
  rw [Real.log_div (ne_of_gt hz₁) (ne_of_gt hz₂)]

/-- Projective colour distance is the absolute logarithm of the cross ratio. -/
theorem peelDistance_eq_abs_log_div {z₁ z₂ : ℝ} (hz₁ : 0 < z₁) (hz₂ : 0 < z₂) :
    peelDistance z₁ z₂ = |Real.log (z₁ / z₂)| := by
  exact abs_log_sub_eq_abs_log_div hz₁ hz₂

/-- For a ratio of readings, its signed spacing is the difference of the reading spacings. -/
theorem abs_log_ratio {m p : ℝ} (hm : 0 < m) (hp : 0 < p) :
    |Real.log (m / p)| = |Real.log m - Real.log p| := by
  rw [Real.log_div (ne_of_gt hm) (ne_of_gt hp)]

/-- The projective-distance identity specialized to ratios of positive readings. -/
theorem peelDistance_ratios {m₁ p₁ m₂ p₂ : ℝ}
    (hm₁ : 0 < m₁) (hp₁ : 0 < p₁) (hm₂ : 0 < m₂) (hp₂ : 0 < p₂) :
    peelDistance (m₁ / p₁) (m₂ / p₂) =
      |Real.log ((m₁ / p₁) / (m₂ / p₂))| := by
  exact peelDistance_eq_abs_log_div (div_pos hm₁ hp₁) (div_pos hm₂ hp₂)


end ElementalPeeling.LoopWall.ChromaticAngle
