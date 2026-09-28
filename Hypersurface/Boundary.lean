import Mathlib

set_option autoImplicit false

/-!
Rectangular block identities for the two-sided boundary reduction.
Left and right spaces are allowed different dimensions. Explicit inverses are
supplied with their inverse hypotheses; invertibility is not inferred from a
numerical spectral gap. CURRENT STATUS: uncompiled candidate.
-/
open Matrix

namespace Hypersurface

section Rectangular
variable {ι β ο : Type*}
variable [Fintype ι] [Fintype β] [Fintype ο]
variable [DecidableEq ι] [DecidableEq β] [DecidableEq ο]

noncomputable def boundaryKernel (D : Matrix β β ℂ) (C : Matrix β ι ℂ)
    (R : Matrix ι ι ℂ) (B : Matrix ι β ℂ)
    (G : Matrix β ο ℂ) (T : Matrix ο ο ℂ) (F : Matrix ο β ℂ) : Matrix β β ℂ :=
  D - C*R*B - G*T*F

theorem inside_lift_equation (A R : Matrix ι ι ℂ) (B : Matrix ι β ℂ)
    (hAR : A*R=1) : A * (-(R*B)) + B = 0 := by
  simp only [Matrix.mul_neg, ← Matrix.mul_assoc, hAR, Matrix.one_mul, neg_add_cancel]

theorem outside_lift_equation (E T : Matrix ο ο ℂ) (F : Matrix ο β ℂ)
    (hET : E*T=1) : E * (-(T*F)) + F = 0 := by
  simp only [Matrix.mul_neg, ← Matrix.mul_assoc, hET, Matrix.one_mul, neg_add_cancel]

theorem boundary_lift_equation (D : Matrix β β ℂ) (C : Matrix β ι ℂ)
    (R : Matrix ι ι ℂ) (B : Matrix ι β ℂ)
    (G : Matrix β ο ℂ) (T : Matrix ο ο ℂ) (F : Matrix ο β ℂ) :
    C * (-(R*B)) + D + G * (-(T*F)) = boundaryKernel D C R B G T F := by
  unfold boundaryKernel
  simp only [Matrix.mul_neg, ← Matrix.mul_assoc]
  abel

theorem boundary_frame_covariance (D q qi : Matrix β β ℂ)
    (C : Matrix β ι ℂ) (R : Matrix ι ι ℂ) (B : Matrix ι β ℂ)
    (G : Matrix β ο ℂ) (T : Matrix ο ο ℂ) (F : Matrix ο β ℂ) :
    boundaryKernel (qi*D*q) (qi*C) R (B*q) (qi*G) T (F*q) =
      qi * boundaryKernel D C R B G T F * q := by
  unfold boundaryKernel
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]

-- This verifies the boundary equation for any declared second-order source N.
-- The physical assumption that N is the surface quadratic susceptibility must
-- be established outside this lemma. No microscopic Hall model is assumed.
theorem second_harmonic_equation (K V : Matrix β β ℂ)
    (N : (β → ℂ) → (β → ℂ)) (u : β → ℂ) (hKV : K*V=1) :
    K *ᵥ (-(V *ᵥ (N u))) + N u = 0 := by
  rw [Matrix.mulVec_neg, Matrix.mulVec_mulVec, hKV, Matrix.one_mulVec]
  exact neg_add_cancel (N u)
end Rectangular

end Hypersurface
