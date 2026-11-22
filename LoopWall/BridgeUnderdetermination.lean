import Mathlib

/-!
# The two-jet cannot select the bridge

Direction B2 of the fourth round.  `phi1 Γ = Γ^2/2` and `phi2 Γ = -(1/2) log (1-Γ^2)` have the same
value, first and second derivative at `Γ = 0`, while their forces at the wall differ
(`equal_two_jets_but_different_wall_forces`).  The universal form is
`no_function_of_two_jet_computes_wall_force`: no `F` of the 2-jet at 0 gives the wall force for all
`φ`.  The ledger force at the wall is the square root of two (`deriv_phi2_wall`); the value twice
that, which I first wrote, is refuted in `ledger_wall_force_is_not_two_mul_sqrt_two`.

Written in the fourth parallel formalization round (swarm `smws625cs`, direction m6),
recompiled and reviewed here; namespace and header added, `#print axioms` lines removed.
-/

namespace ElementalPeeling.LoopWall.BridgeUnderdetermination

open Filter Topology

noncomputable def phi1 (Γ : ℝ) : ℝ := (1 / 2 : ℝ) * Γ ^ 2

noncomputable def phi2 (Γ : ℝ) : ℝ := -(1 / 2 : ℝ) * Real.log (1 - Γ ^ 2)

/-- The wall point used to compare the two forces. -/
noncomputable def wall : ℝ := 1 / Real.sqrt 2

theorem wall_sq : wall ^ 2 = 1 / 2 := by
  rw [wall, div_pow, one_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

theorem wall_pos : 0 < wall := by
  rw [wall]
  positivity

theorem abs_wall_lt_one : |wall| < 1 := by
  rw [abs_of_pos wall_pos]
  by_contra h
  have h1 : 1 ≤ wall := le_of_not_gt h
  have hprod : 0 ≤ (wall - 1) * (wall + 1) :=
    mul_nonneg (sub_nonneg.mpr h1) (by linarith [wall_pos])
  nlinarith [wall_sq]

theorem hasDerivAt_phi1 (x : ℝ) : HasDerivAt phi1 x x := by
  unfold phi1
  convert (hasDerivAt_pow 2 x).const_mul (1 / 2 : ℝ) using 1 <;> norm_num <;>
    ring

theorem deriv_phi1 (x : ℝ) : deriv phi1 x = x :=
  (hasDerivAt_phi1 x).deriv

theorem phi1_zero : phi1 0 = 0 := by
  simp [phi1]

theorem deriv_phi1_zero : deriv phi1 0 = 0 := by
  rw [deriv_phi1]

theorem deriv_deriv_phi1_zero : deriv (deriv phi1) 0 = 1 := by
  have hfun : deriv phi1 = fun x : ℝ => x := funext deriv_phi1
  rw [hfun]
  exact (hasDerivAt_id 0).deriv

theorem hasDerivAt_phi2 {x : ℝ} (hx : |x| < 1) :
    HasDerivAt phi2 (x / (1 - x ^ 2)) x := by
  rcases abs_lt.mp hx with ⟨hxneg, hxpos⟩
  have hprod : 0 < (1 - x) * (1 + x) :=
    mul_pos (sub_pos.mpr hxpos) (by linarith)
  have hpos : 0 < 1 - x ^ 2 := by nlinarith
  have hsq : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
    simpa using hasDerivAt_pow 2 x
  have hinner : HasDerivAt (fun y : ℝ => 1 - y ^ 2) (-2 * x) x := by
    convert hsq.const_sub 1 using 1 <;> ring
  unfold phi2
  convert (hinner.log hpos.ne').const_mul (-(1 / 2 : ℝ)) using 1 <;> ring

theorem deriv_phi2 {x : ℝ} (hx : |x| < 1) :
    deriv phi2 x = x / (1 - x ^ 2) :=
  (hasDerivAt_phi2 hx).deriv

theorem phi2_zero : phi2 0 = 0 := by
  simp [phi2]

theorem deriv_phi2_zero : deriv phi2 0 = 0 := by
  rw [deriv_phi2 (by simp)]
  norm_num

theorem eventually_deriv_phi2 :
    deriv phi2 =ᶠ[𝓝 0] fun x : ℝ => x / (1 - x ^ 2) := by
  filter_upwards [Ioo_mem_nhds (show (-1 : ℝ) < 0 by norm_num)
    (show (0 : ℝ) < 1 by norm_num)] with x hx
  exact deriv_phi2 (abs_lt.mpr hx)

theorem hasDerivAt_wall_force_formula_at_zero :
    HasDerivAt (fun x : ℝ => x / (1 - x ^ 2)) 1 0 := by
  have hsq : HasDerivAt (fun x : ℝ => x ^ 2) (2 * 0) 0 := by
    simpa using hasDerivAt_pow 2 (0 : ℝ)
  have hden : HasDerivAt (fun x : ℝ => 1 - x ^ 2) 0 0 := by
    convert hsq.const_sub 1 using 1 <;> norm_num
  have hid : HasDerivAt (fun x : ℝ => x) 1 0 := by
    simpa using hasDerivAt_pow 1 (0 : ℝ)
  simpa using hid.fun_div hden (by norm_num : (1 : ℝ) - 0 ^ 2 ≠ 0)

theorem deriv_deriv_phi2_zero : deriv (deriv phi2) 0 = 1 := by
  rw [eventually_deriv_phi2.deriv_eq]
  exact hasDerivAt_wall_force_formula_at_zero.deriv

theorem deriv_phi1_wall : deriv phi1 wall = 1 / Real.sqrt 2 := by
  rw [deriv_phi1, wall]

theorem deriv_phi2_wall_formula : deriv phi2 wall = wall / (1 - wall ^ 2) :=
  deriv_phi2 abs_wall_lt_one

/-- The correct wall force.  The value `2 * sqrt 2` sometimes quoted here is
false: dividing by `1 - wall² = 1/2` gives `2 / sqrt 2 = sqrt 2`. -/
theorem deriv_phi2_wall : deriv phi2 wall = Real.sqrt 2 := by
  rw [deriv_phi2_wall_formula, wall_sq, wall]
  have hs : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  field_simp [hs]
  nlinarith

/-- Refutation of the uncorrected wall-force statement. -/
theorem ledger_wall_force_is_not_two_mul_sqrt_two :
    deriv phi2 wall ≠ 2 * Real.sqrt 2 := by
  rw [deriv_phi2_wall]
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  nlinarith

theorem wall_forces_differ : deriv phi1 wall ≠ deriv phi2 wall := by
  rw [deriv_phi1_wall, deriv_phi2_wall]
  intro h
  have hs : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  field_simp [hs] at h
  nlinarith

/-- The explicit counterexample: equal two-jets at zero, unequal wall forces. -/
theorem equal_two_jets_but_different_wall_forces :
    ∃ φ ψ : ℝ → ℝ,
      φ 0 = ψ 0 ∧
      deriv φ 0 = deriv ψ 0 ∧
      deriv (deriv φ) 0 = deriv (deriv ψ) 0 ∧
      deriv φ wall ≠ deriv ψ wall := by
  refine ⟨phi1, phi2, ?_, ?_, ?_, wall_forces_differ⟩
  · rw [phi1_zero, phi2_zero]
  · rw [deriv_phi1_zero, deriv_phi2_zero]
  · rw [deriv_deriv_phi1_zero, deriv_deriv_phi2_zero]

/-- No scalar function of the two-jet at zero computes the wall force for all
real functions.  Here `deriv` is total, so no extra differentiability side
condition on the universally quantified functions is needed. -/
theorem no_function_of_two_jet_computes_wall_force :
    ¬ ∃ F : ℝ × ℝ × ℝ → ℝ,
      ∀ φ : ℝ → ℝ,
        F (φ 0, deriv φ 0, deriv (deriv φ) 0) = deriv φ wall := by
  rintro ⟨F, hF⟩
  have h1 := hF phi1
  have h2 := hF phi2
  rw [phi1_zero, deriv_phi1_zero, deriv_deriv_phi1_zero] at h1
  rw [phi2_zero, deriv_phi2_zero, deriv_deriv_phi2_zero] at h2
  have heq : deriv phi1 wall = deriv phi2 wall := by
    rw [← h1, ← h2]
  exact wall_forces_differ heq


end ElementalPeeling.LoopWall.BridgeUnderdetermination
