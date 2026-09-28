import Mathlib

set_option autoImplicit false

/-!
Scalar boundary, branch and normalization identities. The analytic existence of
waveguide roots, Berry integrals, and physical gravity identification are NOT
claimed by these lemmas. CURRENT STATUS: uncompiled candidate.
-/
namespace Hypersurface

theorem scalar_boundary_numerator (a b c d e f g : ℂ)
    (ha : a ≠ 0) (he : e ≠ 0) :
    (d - c/a*b - g/e*f)*(a*e) = d*a*e-c*b*e-g*f*a := by
  field_simp [ha,he] <;> ring

theorem dark_coordinate_invisible (e₁ e₂ e₃ z g d : ℂ) :
    d - g^2/(e₁-z) - 0/(e₂-z) = d - g^2/(e₁-z) - 0/(e₃-z) := by
  simp

theorem omit_exterior_is_wrong :
    (4-(1:ℚ)/2-1/3) ≠ (4-1/2) := by
  norm_num

theorem residual_rigidity_on_shell (η r : ℝ) (hr : r=0) :
    1/(r^2+η) = 1/η := by
  simp [hr]

theorem index_ratios_cannot_match_constant_rigidity
    (R c n₁ n₂ : ℝ) (hc : c ≠ 0) (h₁ : R=c*n₁) (h₂ : R=c*n₂) : n₁=n₂ := by
  exact (mul_left_cancel₀ hc) (h₁.symm.trans h₂)

-- Algebra of the mode sensitivity. The integral normalization T and exterior
-- fraction must first be obtained from the explicitly stated TE eigenfunction.
theorem exterior_sensitivity_dictionary (β n k c κ T : ℝ)
    (hβ : β ≠ 0) (hκ : κ ≠ 0) (hT : T ≠ 0) (hc : c ≠ 0) :
    -(n*k^2/κ)/(-β*T/c^2) = n*k^2/β*(c^2/(κ*T)) := by
  field_simp [hβ,hκ,hT,hc] <;> ring <;> simp

-- A nonzero gapped Dirac mass gives a positive metric coefficient at k=0.
-- Neutrality and the microscopic Hamiltonian are not encoded by this scalar.
theorem neutral_dirac_metric_coefficient (m : ℝ) (hm : m ≠ 0) :
    0 < 1/(4*m^2) := by
  apply one_div_pos.mpr
  exact mul_pos (by norm_num) (sq_pos_of_ne_zero hm)

end Hypersurface
