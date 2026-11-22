import Mathlib
import LoopWall.Ledger

/-!
# Clock coordinates: the face apex, the double angle, and the two-boost condition

A positive ratio `z` carries three coordinates (paper, "Clock, apex, interface"): the log spacing
`r = log z`, the **face apex** `a = tanh (r/4)`, and the reflection `Γ = tanh (r/2)`.  This module
proves that apex and reflection are the two halves of the double-angle identity
(`Γ = 2a/(1+a²)`), that the apex inverts to the ratio (`((1+a)/(1−a))² = z`), that `z = 3` gives
`a = 2 − √3` and `Γ = 1/2`, and that four aligned steps of ratio `3` give ratio `81` and reflection
`40/41`.

It then proves the two-boost condition of the two-face construction: the trace
`2 − 4 sinh²h_a sinh²h_b` is `−2` exactly when `sinh² h_a · sinh² h_b = 1`, which in the squared
reflections `u = Γ_a²`, `v = Γ_b²` is `u + v = 1` on the interior — equal faces giving `u = v = 1/2`.
The bridge `sinh² h = Γ²/(1 − Γ²)` is proved from the definition of `tanh`.

Finally the envelope remark: the rate of `Γ²` along a symmetric path is `sin(2θ)` times the rate of
`θ = arcsin Γ`, so for a fixed bound on the latter the envelope `4u(1−u)` peaks exactly at
`u = 1/2`, the wall.

Nothing here refers to an element, a spectrum, or a measurement.
-/

namespace ElementalPeeling.LoopWall.Clock

open ElementalPeeling.LoopWall.Ledger (gam)

theorem tanh_double (x : ℝ) : Real.tanh (2 * x) = 2 * Real.tanh x / (1 + Real.tanh x ^ 2) := by
  have h2 : Real.exp (2 * x) = Real.exp x ^ 2 := by
    rw [show 2 * x = x + x by ring, Real.exp_add]; ring
  rw [Real.tanh_eq, Real.tanh_eq, h2, Real.exp_neg, Real.exp_neg]
  have hu : 0 < Real.exp x := Real.exp_pos x
  have hun : Real.exp x + (Real.exp x)⁻¹ ≠ 0 := by positivity
  have h2' : Real.exp (x * 2) = Real.exp x ^ 2 := by rw [mul_comm]; exact h2
  field_simp
  rw [h2]
  ring

noncomputable def apex (z : ℝ) : ℝ := Real.tanh (Real.log z / 4)

theorem gam_eq_two_apex (z : ℝ) (hz : 0 < z) :
    gam z = 2 * apex z / (1 + apex z ^ 2) := by
  have h : Real.log z / 2 = 2 * (Real.log z / 4) := by ring
  rw [ElementalPeeling.LoopWall.Ledger.gam_eq_tanh_half_log z hz, h, tanh_double]
  rfl

theorem apex_inverse (z : ℝ) (hz : 0 < z) :
    ((1 + apex z) / (1 - apex z)) ^ 2 = z := by
  have hs0 : 0 < Real.sqrt z := Real.sqrt_pos.2 hz
  have hapex : apex z = gam (Real.sqrt z) := by
    unfold apex
    rw [show Real.log z / 4 = Real.log (Real.sqrt z) / 2 by
      rw [Real.log_sqrt hz.le]; ring]
    exact (ElementalPeeling.LoopWall.Ledger.gam_eq_tanh_half_log _ hs0).symm
  rw [hapex, ElementalPeeling.LoopWall.Ledger.inverse_gam _ hs0, Real.sq_sqrt hz.le]

theorem apex_three : apex 3 = 2 - Real.sqrt 3 := by
  have h3 : (0:ℝ) < 3 := by norm_num
  have hs0 : 0 < Real.sqrt 3 := Real.sqrt_pos.2 h3
  have hapex : apex 3 = gam (Real.sqrt 3) := by
    unfold apex
    rw [show Real.log 3 / 4 = Real.log (Real.sqrt 3) / 2 by
      rw [Real.log_sqrt h3.le]; ring]
    exact (ElementalPeeling.LoopWall.Ledger.gam_eq_tanh_half_log _ hs0).symm
  rw [hapex, show gam (Real.sqrt 3) = (Real.sqrt 3 - 1)/(Real.sqrt 3 + 1) from rfl]
  rw [div_eq_iff (by positivity)]
  nlinarith [Real.sq_sqrt h3.le, Real.sqrt_nonneg 3]

theorem gam_three : gam 3 = 1 / 2 := by
  rw [show gam 3 = (3 - 1) / (3 + 1) from rfl]; norm_num

theorem four_steps_three : gam ((3 : ℝ) ^ 4) = 40 / 41 := by
  rw [show gam ((3 : ℝ) ^ 4) = ((3 : ℝ) ^ 4 - 1) / ((3 : ℝ) ^ 4 + 1) from rfl]; norm_num

noncomputable def twoBoostTrace (ha hb : ℝ) : ℝ := 2 - 4 * Real.sinh ha ^ 2 * Real.sinh hb ^ 2

theorem twoBoostTrace_eq_neg_two_iff (ha hb : ℝ) :
    twoBoostTrace ha hb = -2 ↔ Real.sinh ha ^ 2 * Real.sinh hb ^ 2 = 1 := by
  unfold twoBoostTrace; constructor <;> intro h <;> linarith

theorem sinh_sq_eq_gam_sq (z : ℝ) (hz : 0 < z) :
    Real.sinh (Real.log z / 2) ^ 2 = gam z ^ 2 / (1 - gam z ^ 2) := by
  have hs := Real.sinh_sq (Real.log z / 2)
  have hc := Real.cosh_sq (Real.log z / 2)
  have hcpos : 0 < Real.cosh (Real.log z / 2) := Real.cosh_pos _
  have hg : gam z = Real.sinh (Real.log z / 2) / Real.cosh (Real.log z / 2) := by
    rw [ElementalPeeling.LoopWall.Ledger.gam_eq_tanh_half_log z hz, Real.tanh_eq_sinh_div_cosh]
  rw [hg, div_pow]
  field_simp
  nlinarith

theorem wall_condition_iff (u v : ℝ) (hu : u < 1) (hv : v < 1) :
    u / (1 - u) * (v / (1 - v)) = 1 ↔ u + v = 1 := by
  have h1 : 0 < 1 - u := by linarith
  have h2 : 0 < 1 - v := by linarith
  constructor
  · intro h
    rw [div_mul_div_comm, div_eq_one_iff_eq (by positivity)] at h
    linarith
  · intro h
    rw [div_mul_div_comm, div_eq_one_iff_eq (by positivity)]
    linarith

theorem equal_faces (u : ℝ) (_hu : u < 1) (_hu0 : 0 ≤ u) (h : u + u = 1) : u = 1 / 2 := by linarith

theorem hasDerivAt_sin_mul_self (θ : ℝ) :
    HasDerivAt (fun t => Real.sin t * Real.sin t) (Real.sin (2 * θ)) θ := by
  have h2 := (Real.hasDerivAt_sin θ).mul (Real.hasDerivAt_sin θ)
  have hderiv : Real.cos θ * Real.sin θ + Real.sin θ * Real.cos θ = Real.sin (2 * θ) := by
    rw [Real.sin_two_mul]; ring
  rw [hderiv] at h2
  exact h2

theorem hasDerivAt_sin_sq (θ : ℝ) :
    HasDerivAt (fun t => Real.sin t ^ 2) (Real.sin (2 * θ)) θ := by
  have h := hasDerivAt_sin_mul_self θ
  simpa [pow_two] using h

theorem envelope (u : ℝ) : 4 * u * (1 - u) ≤ 1 ∧ (4 * u * (1 - u) = 1 ↔ u = 1 / 2) := by
  have hsq : 4 * u * (1 - u) = 1 - (2 * u - 1) ^ 2 := by ring
  constructor
  · rw [hsq]; nlinarith [sq_nonneg (2 * u - 1)]
  · rw [hsq]
    constructor
    · intro h
      have h0 : (2 * u - 1) ^ 2 = 0 := by linarith
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h0
      linarith
    · intro h; subst h; norm_num

end ElementalPeeling.LoopWall.Clock
