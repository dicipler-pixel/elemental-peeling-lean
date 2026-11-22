import Mathlib

/-!
# Two-level control: the Bloch square, the positive projector, and the velocity decomposition

Direction D4.  `pauli_sq`/`pauli_charpoly`/`pauli_spectrum` give the square, the characteristic
polynomial and the spectrum of `aσ₁ + bσ₂`; `projector_*` give the projector
`(1 + cos φ σ₁ + sin φ σ₂)/2`; `velocity_norm_sq_decomposition` and `chi_derivative_bound` give
`‖ḋ‖² = ρ̇² + Δ²g` and `ρ²χ̇² ≤ Δ²g` in the stated algebraic derivative model on `Fin 3 → ℝ`
(`v` plays the role of `ḋ`).

Written in the parallel formalization round (swarm `smws25izm`, direction m1),
then recompiled and reviewed here; namespace and header added, trailing `#print axioms` lines
removed because `scripts/verify.py` audits every named theorem.  See PROVENANCE.md.
-/

/-!
# Two-level identities

The Pauli matrices are complex, as they must be for the projector in part (ii)
to be Hermitian. Part (iii) will use the algebraic derivative model allowed by
the question: position `d`, velocity `v`, radial speed `q = (d·v)/ρ`, and the
explicit vector `normalizedDerivative d v = (v - q(d/ρ))/ρ` for `ṅ`.
-/

namespace ElementalPeeling.LoopWall.TwoLevel

open scoped Matrix Polynomial
open Matrix Polynomial

/-- The first Pauli matrix. -/
def sigmaX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- The second Pauli matrix. -/
def sigmaY : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]

/-- The real linear combination `aσ₁ + bσ₂`, with real coefficients coerced to `ℂ`. -/
def pauli (a b : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (a : ℂ) • sigmaX + (b : ℂ) • sigmaY

theorem pauli_apply (a b : ℝ) :
    pauli a b = !![0, (a : ℂ) - (b : ℂ) * Complex.I;
                    (a : ℂ) + (b : ℂ) * Complex.I, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauli, sigmaX, sigmaY] <;> ring

theorem pauli_sq (a b : ℝ) :
    pauli a b * pauli a b = (((a ^ 2 + b ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) := by
  rw [pauli_apply]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ] <;> ring_nf <;> rw [Complex.I_sq] <;> ring

theorem pauli_trace (a b : ℝ) : (pauli a b).trace = 0 := by
  rw [pauli_apply, Matrix.trace_fin_two]
  simp

theorem pauli_det (a b : ℝ) : (pauli a b).det = -(((a ^ 2 + b ^ 2 : ℝ) : ℂ)) := by
  rw [pauli_apply, Matrix.det_fin_two_of]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

theorem pauli_charpoly (a b : ℝ) :
    (pauli a b).charpoly = X ^ 2 - C (((a ^ 2 + b ^ 2 : ℝ) : ℂ)) := by
  rw [Matrix.charpoly_fin_two, pauli_trace, pauli_det]
  simp only [map_zero, zero_mul, sub_zero, C_neg]
  rw [sub_eq_add_neg]

/-- The eigenvalues, expressed as the matrix spectrum, are exactly the two square roots. -/
theorem pauli_spectrum (a b : ℝ) :
    spectrum ℂ (pauli a b) =
      {(((Real.sqrt (a ^ 2 + b ^ 2) : ℝ) : ℂ)),
       -(((Real.sqrt (a ^ 2 + b ^ 2) : ℝ) : ℂ))} := by
  ext z
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, pauli_charpoly]
  have hsq : (Real.sqrt (a ^ 2 + b ^ 2)) ^ 2 = a ^ 2 + b ^ 2 := by
    rw [Real.sq_sqrt]
    positivity
  have hroot : (((Real.sqrt (a ^ 2 + b ^ 2) : ℝ) : ℂ)) ^ 2 =
      (((a ^ 2 + b ^ 2 : ℝ) : ℂ)) := by
    rw [← Complex.ofReal_pow, hsq]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff,
    Polynomial.IsRoot, eval_sub, eval_pow, eval_X, eval_C]
  constructor
  · intro hz
    apply sq_eq_sq_iff_eq_or_eq_neg.mp
    rw [sub_eq_zero.mp hz, hroot]
  · rintro (rfl | rfl)
    · exact sub_eq_zero.mpr hroot
    · rw [neg_sq]
      exact sub_eq_zero.mpr hroot

/-- The Hermitian projector in the direction `(cos φ, sin φ)`. -/
noncomputable def projector (φ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (2 : ℂ)⁻¹ • (1 + pauli (Real.cos φ) (Real.sin φ))

theorem directional_pauli_sq (φ : ℝ) :
    pauli (Real.cos φ) (Real.sin φ) * pauli (Real.cos φ) (Real.sin φ) = 1 := by
  rw [pauli_sq]
  have h := Real.sin_sq_add_cos_sq φ
  norm_cast
  rw [show Real.cos φ ^ 2 + Real.sin φ ^ 2 = 1 by nlinarith]
  simp

theorem projector_idempotent (φ : ℝ) : projector φ * projector φ = projector φ := by
  unfold projector
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [add_mul, mul_add, mul_add, one_mul, mul_one, one_mul, directional_pauli_sq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp_all [pauli_apply, sigmaX, sigmaY, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    norm_num <;> ring

theorem sigmaX_hermitian : sigmaXᴴ = sigmaX := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sigmaX, Matrix.conjTranspose_apply]

theorem sigmaY_hermitian : sigmaYᴴ = sigmaY := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sigmaY, Matrix.conjTranspose_apply, Complex.star_def, Complex.conj_I]

theorem pauli_hermitian (a b : ℝ) : (pauli a b)ᴴ = pauli a b := by
  simp only [pauli, Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
    sigmaX_hermitian, sigmaY_hermitian, Complex.star_def, Complex.conj_ofReal]

theorem projector_hermitian (φ : ℝ) : (projector φ)ᴴ = projector φ := by
  unfold projector
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
    Matrix.conjTranspose_one, pauli_hermitian]
  norm_num [Complex.star_def]

theorem pauli_radial (r φ : ℝ) :
    pauli (r * Real.cos φ) (r * Real.sin φ) =
      (r : ℂ) • pauli (Real.cos φ) (Real.sin φ) := by
  rw [pauli_apply, pauli_apply]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.smul_apply] <;> push_cast <;> ring

theorem projector_commutes (r φ : ℝ) :
    projector φ * pauli (r * Real.cos φ) (r * Real.sin φ) =
      pauli (r * Real.cos φ) (r * Real.sin φ) * projector φ := by
  rw [pauli_radial]
  unfold projector
  have hcomm :
      (1 + pauli (Real.cos φ) (Real.sin φ)) * pauli (Real.cos φ) (Real.sin φ) =
        pauli (Real.cos φ) (Real.sin φ) * (1 + pauli (Real.cos φ) (Real.sin φ)) := by
    noncomm_ring
  simp only [Matrix.smul_mul, Matrix.mul_smul, hcomm]
  module

/-! ## Algebraic derivative form of the metric identities -/

/-- Real 3-vectors, with their coordinates indexed by `Fin 3`. -/
abbrev Vec3 := Fin 3 → ℝ

/-- Squared Euclidean norm, expanded without square roots. -/
def normSq (v : Vec3) : ℝ := ∑ i, v i ^ 2

/-- Euclidean dot product. -/
def dot (d v : Vec3) : ℝ := ∑ i, d i * v i

/-- The radius `ρ = ‖d‖`. -/
noncomputable def radius (d : Vec3) : ℝ := Real.sqrt (normSq d)

/-- The third component of `n = d/ρ`. -/
noncomputable def chi (d : Vec3) : ℝ := d 2 / radius d

/-- The radial derivative `ρ̇ = (d·v)/ρ`, where `v = ḋ`. -/
noncomputable def radialSpeed (d v : Vec3) : ℝ := dot d v / radius d

/-- The explicit quotient-rule vector `(v - q(d/ρ))/ρ`, which plays the role of `ṅ`. -/
noncomputable def normalizedDerivative (d v : Vec3) : Vec3 := fun i =>
  (v i - radialSpeed d v * (d i / radius d)) / radius d

/-- The gap `Δ = 2ρ`. -/
noncomputable def gap (d : Vec3) : ℝ := 2 * radius d

/-- The normalized quantum metric `g = ‖ṅ‖²/4`. -/
noncomputable def normalizedMetric (d v : Vec3) : ℝ :=
  normSq (normalizedDerivative d v) / 4

/-- Since `χ` is the third component of `n`, `χ̇` is the third component of `ṅ`. -/
noncomputable def chiDerivative (d v : Vec3) : ℝ := normalizedDerivative d v 2

theorem normSq_nonneg (v : Vec3) : 0 ≤ normSq v := by
  unfold normSq
  positivity

theorem normSq_eq_zero_iff (v : Vec3) : normSq v = 0 ↔ v = 0 := by
  constructor
  · intro h
    have h' : v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 = 0 := by
      simpa [normSq, Fin.sum_univ_three] using h
    have h0 : v 0 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 2)]
    have h1 : v 1 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 2)]
    have h2 : v 2 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 2)]
    funext i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  · rintro rfl
    simp [normSq]

theorem radius_pos_iff (d : Vec3) : 0 < radius d ↔ d ≠ 0 := by
  rw [radius, Real.sqrt_pos]
  constructor
  · intro h hdz
    subst d
    simp [normSq] at h
  · intro hd
    have hns : normSq d ≠ 0 := (not_congr (normSq_eq_zero_iff d)).2 hd
    exact lt_of_le_of_ne (normSq_nonneg d) (Ne.symm hns)

theorem radius_sq (d : Vec3) : radius d ^ 2 = normSq d := by
  rw [radius, Real.sq_sqrt (normSq_nonneg d)]

/-- Algebraic form of `‖ḋ‖² = ρ̇² + Δ²g`. -/
theorem velocity_norm_sq_decomposition (d v : Vec3) (hd : d ≠ 0) :
    normSq v = radialSpeed d v ^ 2 + gap d ^ 2 * normalizedMetric d v := by
  have hρ : 0 < radius d := (radius_pos_iff d).2 hd
  have hρ0 : radius d ≠ 0 := ne_of_gt hρ
  have hr2 : radius d ^ 2 = d 0 ^ 2 + d 1 ^ 2 + d 2 ^ 2 := by
    simpa [normSq, Fin.sum_univ_three] using radius_sq d
  simp only [radialSpeed, gap, normalizedMetric, normalizedDerivative,
    normSq, dot, Fin.sum_univ_three]
  field_simp
  linear_combination (4 * (d 0 * v 0 + d 1 * v 1 + d 2 * v 2) ^ 2) * hr2

/-- Algebraic form of `ρ²χ̇² ≤ Δ²g`. -/
theorem chi_derivative_bound (d v : Vec3) :
    radius d ^ 2 * chiDerivative d v ^ 2 ≤ gap d ^ 2 * normalizedMetric d v := by
  have hcoord : chiDerivative d v ^ 2 ≤ normSq (normalizedDerivative d v) := by
    simp only [chiDerivative, normSq, Fin.sum_univ_three]
    nlinarith [sq_nonneg (normalizedDerivative d v 0), sq_nonneg (normalizedDerivative d v 1)]
  have hmul := mul_le_mul_of_nonneg_left hcoord (sq_nonneg (radius d))
  unfold gap normalizedMetric
  convert hmul using 1 <;> ring

end ElementalPeeling.LoopWall.TwoLevel
