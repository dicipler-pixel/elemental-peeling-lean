import Mathlib

/-!
# The positivity domain of the two-by-two Hermitian form

Direction D1 of the second formalization round.  For the Hermitian form with matrix
`!![a, b + ω/2·i; b − ω/2·i, c]`, `H_posSemidef_iff` gives the exact positivity domain
`0 ≤ a ∧ 0 ≤ c ∧ ω² ≤ 4(ac − b²)` and `H_posDef_iff` its strict form `0 < a ∧ ω² < 4(ac − b²)`.
Two of my transcriptions of the strict case are refuted here: `psd_and_positive_a_do_not_imply_posDef`
(`H 1 1 0 1` is PSD with `a > 0` and singular) and `positive_reduced_determinant_alone_does_not_imply_posDef`
(`ac − b² > 0` with both diagonal entries negative).

At `a = c = 1`, `b = Γa`, `ω = 2·Γb` the boundary is exactly `Γa² + Γb² = 1` (`unit_boundary_iff`),
the equal-face point `Γ = 1/√2` lies on it (`equal_face_point`, `equal_face_point_is_boundary`), and
the conditioning reciprocal `1/(1 − u − v)` is at least one and strictly increasing in `u + v`
(`conditioning_ge_one`, `conditioning_strict_of_sum_lt`).

Recompiled and reviewed here; namespace and header added, `lemma` renamed to `theorem`,
`#print axioms` lines removed (the repository audit covers every named theorem).
-/

open scoped ComplexConjugate ComplexOrder

namespace ElementalPeeling.LoopWall.Positivity

/-- The Hermitian matrix in the positivity question. -/
noncomputable def H (a c ω b : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(a : ℂ), (b : ℂ) + (ω / 2 : ℝ) * Complex.I;
    (b : ℂ) - (ω / 2 : ℝ) * Complex.I, (c : ℂ)]

theorem H_apply00 (a c ω b : ℝ) : H a c ω b 0 0 = (a : ℂ) := rfl
theorem H_apply01 (a c ω b : ℝ) :
    H a c ω b 0 1 = (b : ℂ) + (ω / 2 : ℝ) * Complex.I := rfl
theorem H_apply10 (a c ω b : ℝ) :
    H a c ω b 1 0 = (b : ℂ) - (ω / 2 : ℝ) * Complex.I := rfl
theorem H_apply11 (a c ω b : ℝ) : H a c ω b 1 1 = (c : ℂ) := rfl

theorem H_isHermitian (a c ω b : ℝ) : (H a c ω b).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [H, Matrix.conjTranspose_apply, Complex.ext_iff]

theorem H_det (a c ω b : ℝ) :
    (H a c ω b).det = ((a * c - b ^ 2 - ω ^ 2 / 4 : ℝ) : ℂ) := by
  rw [Matrix.det_fin_two]
  simp only [H_apply00, H_apply01, H_apply10, H_apply11]
  push_cast
  apply Complex.ext <;> simp [pow_two] <;> ring

theorem H_posSemidef_diagonal {a c ω b : ℝ} (h : (H a c ω b).PosSemidef) : 0 ≤ a := by
  have ha := h.diag_nonneg (i := (0 : Fin 2))
  rw [H_apply00] at ha
  exact_mod_cast ha


/-- The unipotent factor in the LDL* decomposition when `a ≠ 0`. -/
noncomputable def ldlFactor (a ω b : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 0; ((b : ℂ) - (ω / 2 : ℝ) * Complex.I) / (a : ℂ), 1]

/-- The two real diagonal pivots, coerced to `ℂ`. -/
noncomputable def ldlPivots (a c ω b : ℝ) : Fin 2 → ℂ :=
  ![(a : ℂ), (((a * c - b ^ 2 - ω ^ 2 / 4) / a : ℝ) : ℂ)]

theorem H_eq_ldl {a c ω b : ℝ} (ha : a ≠ 0) :
    ldlFactor a ω b * Matrix.diagonal (ldlPivots a c ω b) *
      Matrix.conjTranspose (ldlFactor a ω b) = H a c ω b := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ldlFactor, ldlPivots, H, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.conjTranspose_apply, Matrix.vecMul_eq_sum, Matrix.diagonal_apply,
      ha] <;>
    field_simp [ha] <;> ring_nf <;> simp [Complex.I_sq, map_ofNat (starRingEnd ℂ) 2] <;> ring

theorem H_posSemidef_diagonal_right {a c ω b : ℝ} (h : (H a c ω b).PosSemidef) : 0 ≤ c := by
  have hc := h.diag_nonneg (i := (1 : Fin 2))
  rw [H_apply11] at hc
  exact_mod_cast hc

theorem H_posSemidef_det {a c ω b : ℝ} (h : (H a c ω b).PosSemidef) :
    ω ^ 2 ≤ 4 * (a * c - b ^ 2) := by
  have hd := h.det_nonneg
  rw [H_det] at hd
  have hd' : (0 : ℝ) ≤ a * c - b ^ 2 - ω ^ 2 / 4 := by
    exact_mod_cast hd
  linarith


theorem H_posSemidef_of_conditions {a c ω b : ℝ}
    (ha : 0 ≤ a) (hc : 0 ≤ c) (hd : ω ^ 2 ≤ 4 * (a * c - b ^ 2)) :
    (H a c ω b).PosSemidef := by
  by_cases ha0 : a = 0
  · subst a
    have hb : b = 0 := by nlinarith [sq_nonneg b, sq_nonneg ω]
    have hω : ω = 0 := by nlinarith [sq_nonneg b, sq_nonneg ω]
    subst b
    subst ω
    have heq : H 0 c 0 0 = Matrix.diagonal ![(0 : ℂ), (c : ℂ)] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [H, Matrix.diagonal]
    rw [heq]
    apply Matrix.PosSemidef.diagonal
    intro i
    fin_cases i <;> simp [hc]
  · have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    have hpivots : 0 ≤ ldlPivots a c ω b := by
      intro i
      fin_cases i
      · simpa [ldlPivots] using ha
      · change (0 : ℂ) ≤ (((a * c - b ^ 2 - ω ^ 2 / 4) / a : ℝ) : ℂ)
        rw [Complex.zero_le_real]
        exact div_nonneg (by linarith) ha
    have hdiag : (Matrix.diagonal (ldlPivots a c ω b)).PosSemidef :=
      Matrix.PosSemidef.diagonal hpivots
    have hcong := hdiag.mul_mul_conjTranspose_same (ldlFactor a ω b)
    rw [H_eq_ldl ha0] at hcong
    exact hcong

/-- Exact positive-semidefinite domain of the two-by-two Hermitian form. -/
theorem H_posSemidef_iff {a c ω b : ℝ} :
    (H a c ω b).PosSemidef ↔
      0 ≤ a ∧ 0 ≤ c ∧ ω ^ 2 ≤ 4 * (a * c - b ^ 2) := by
  constructor
  · intro h
    exact ⟨H_posSemidef_diagonal h, H_posSemidef_diagonal_right h,
      H_posSemidef_det h⟩
  · rintro ⟨ha, hc, hd⟩
    exact H_posSemidef_of_conditions ha hc hd


/-- Positive definiteness is the strict form of Sylvester's two minor tests. -/
theorem H_posDef_iff {a c ω b : ℝ} :
    (H a c ω b).PosDef ↔ 0 < a ∧ ω ^ 2 < 4 * (a * c - b ^ 2) := by
  constructor
  · intro h
    have ha := h.diag_pos (i := (0 : Fin 2))
    rw [H_apply00] at ha
    have ha' : 0 < a := by exact_mod_cast ha
    have hdet := h.det_pos
    rw [H_det] at hdet
    have hdet' : (0 : ℝ) < a * c - b ^ 2 - ω ^ 2 / 4 := by
      exact_mod_cast hdet
    exact ⟨ha', by linarith⟩
  · rintro ⟨ha, hd⟩
    have hc : 0 < c := by
      have hac : 0 < a * c := by nlinarith [sq_nonneg b, sq_nonneg ω]
      exact (mul_pos_iff_of_pos_left ha).mp hac
    have hpsd : (H a c ω b).PosSemidef :=
      H_posSemidef_of_conditions ha.le hc.le hd.le
    apply hpsd.posDef_iff_det_ne_zero.mpr
    rw [H_det, ne_eq, Complex.ofReal_eq_zero]
    linarith

/-- The same criterion written using the determinant itself. -/
theorem H_posDef_iff_positive_leading_minors {a c ω b : ℝ} :
    (H a c ω b).PosDef ↔ 0 < a ∧ 0 < a * c - b ^ 2 - ω ^ 2 / 4 := by
  rw [H_posDef_iff]
  constructor <;> rintro ⟨ha, hd⟩ <;> exact ⟨ha, by linarith⟩

/-- The literal assertion `PosSemidef ∧ 0 < a → PosDef` is false:
this matrix is the positive-semidefinite, singular matrix with every entry one. -/
theorem psd_and_positive_a_do_not_imply_posDef :
    (H 1 1 0 1).PosSemidef ∧ 0 < (1 : ℝ) ∧ ¬(H 1 1 0 1).PosDef := by
  rw [H_posSemidef_iff, H_posDef_iff]
  norm_num

/-- Positivity of `a*c-b^2` cannot replace the sign condition on `a`:
both diagonal entries may be negative. -/
theorem positive_reduced_determinant_alone_does_not_imply_posDef :
    0 < (-1 : ℝ) * (-1) - 0 ^ 2 ∧ 0 ^ 2 < 4 * ((-1 : ℝ) * (-1) - 0 ^ 2) ∧
      ¬(H (-1) (-1) 0 0).PosDef := by
  rw [H_posDef_iff]
  norm_num

/-- Even inside the semidefinite domain, `0 < a*c-b^2` is not a strictness
condition: equality `ω^2 = 4*(a*c-b^2)` still gives a zero determinant. -/
theorem psd_and_positive_reduced_determinant_do_not_imply_posDef :
    (H 1 1 2 0).PosSemidef ∧ 0 < (1 : ℝ) * 1 - 0 ^ 2 ∧
      ¬(H 1 1 2 0).PosDef := by
  rw [H_posSemidef_iff, H_posDef_iff]
  norm_num

/-- At unit diagonal the semidefinite domain is the closed unit disc. -/
theorem unit_posSemidef_iff (Γa Γb : ℝ) :
    (H 1 1 (2 * Γb) Γa).PosSemidef ↔ Γa ^ 2 + Γb ^ 2 ≤ 1 := by
  rw [H_posSemidef_iff]
  constructor
  · rintro ⟨_, _, h⟩
    nlinarith
  · intro h
    exact ⟨zero_le_one, zero_le_one, by nlinarith⟩

/-- At unit diagonal the definite domain is the open unit disc. -/
theorem unit_posDef_iff (Γa Γb : ℝ) :
    (H 1 1 (2 * Γb) Γa).PosDef ↔ Γa ^ 2 + Γb ^ 2 < 1 := by
  rw [H_posDef_iff]
  constructor
  · rintro ⟨_, h⟩
    nlinarith
  · intro h
    exact ⟨zero_lt_one, by nlinarith⟩

/-- The boundary (positive semidefinite but not positive definite) is exactly
`Γa^2 + Γb^2 = 1`. -/
theorem unit_boundary_iff (Γa Γb : ℝ) :
    (H 1 1 (2 * Γb) Γa).PosSemidef ∧ ¬(H 1 1 (2 * Γb) Γa).PosDef ↔
      Γa ^ 2 + Γb ^ 2 = 1 := by
  rw [unit_posSemidef_iff, unit_posDef_iff]
  constructor
  · rintro ⟨hle, hnlt⟩
    have hnle : 1 ≤ Γa ^ 2 + Γb ^ 2 := le_of_not_gt hnlt
    exact le_antisymm hle hnle
  · intro heq
    constructor
    · exact heq.le
    · rw [heq]
      exact lt_irrefl 1

/-- On the equal-face line, `2*Γ^2 = 1` is precisely the boundary equation. -/
theorem equal_face_boundary (Γ : ℝ) :
    (H 1 1 (2 * Γ) Γ).PosSemidef ∧ ¬(H 1 1 (2 * Γ) Γ).PosDef ↔
      2 * Γ ^ 2 = 1 := by
  rw [unit_boundary_iff]
  constructor <;> intro h <;> nlinarith

theorem inv_sqrt_two_sq : (1 / Real.sqrt 2) ^ 2 = (1 : ℝ) / 2 := by
  have h : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  rw [div_pow, one_pow, h]

/-- The positive equal-face boundary point is `Γa = Γb = 1/√2`. -/
theorem equal_face_point :
    (1 / Real.sqrt 2) ^ 2 + (1 / Real.sqrt 2) ^ 2 = 1 ∧
      2 * (1 / Real.sqrt 2) ^ 2 = 1 := by
  have h := inv_sqrt_two_sq
  constructor <;> nlinarith

theorem equal_face_point_is_boundary :
    (H 1 1 (2 * (1 / Real.sqrt 2)) (1 / Real.sqrt 2)).PosSemidef ∧
      ¬(H 1 1 (2 * (1 / Real.sqrt 2)) (1 / Real.sqrt 2)).PosDef := by
  apply (equal_face_boundary (1 / Real.sqrt 2)).mpr
  exact equal_face_point.2


/-- The projector-conditioning denominator is at least one on the stated domain. -/
theorem conditioning_ge_one {u v : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : u + v < 1) :
    1 ≤ 1 / (1 - u - v) := by
  have hd : 0 < 1 - u - v := by linarith
  apply (le_div_iff₀ hd).mpr
  nlinarith

/-- The conditioning reciprocal strictly increases when the sum of the two
nonnegative coordinates strictly increases. -/
theorem conditioning_strict_of_sum_lt {u v u' v' : ℝ}
    (_hu : 0 ≤ u) (_hv : 0 ≤ v) (_huv : u + v < 1)
    (_hu' : 0 ≤ u') (_hv' : 0 ≤ v') (huv' : u' + v' < 1)
    (hsum : u + v < u' + v') :
    1 / (1 - u - v) < 1 / (1 - u' - v') := by
  have hd : 0 < 1 - u - v := by linarith
  have hd' : 0 < 1 - u' - v' := by linarith
  apply (div_lt_div_iff₀ hd hd').mpr
  nlinarith

/-- The conditioning function, written with `u=Γa^2` and `v=Γb^2`. -/
noncomputable def kappaSq (Γa Γb : ℝ) : ℝ := 1 / (1 - Γa ^ 2 - Γb ^ 2)

theorem kappaSq_ge_one {Γa Γb : ℝ} (h : Γa ^ 2 + Γb ^ 2 < 1) :
    1 ≤ kappaSq Γa Γb := by
  exact conditioning_ge_one (sq_nonneg Γa) (sq_nonneg Γb) h

/-- The coordinatewise-ordered domain of the two summands. -/
def conditioningDomain : Set (ℝ × ℝ) :=
  {p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 < 1}

/-- The reciprocal conditioning function is strictly monotone on the pair domain
for the coordinatewise product order. -/
theorem conditioning_strictMonoOn :
    StrictMonoOn (fun p : ℝ × ℝ => 1 / (1 - p.1 - p.2)) conditioningDomain := by
  intro p hp q hq hpq
  change 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 < 1 at hp
  change 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 < 1 at hq
  apply conditioning_strict_of_sum_lt hp.1 hp.2.1 hp.2.2 hq.1 hq.2.1 hq.2.2
  have hle : p ≤ q := hpq.le
  have hp1 : p.1 ≤ q.1 := hle.1
  have hp2 : p.2 ≤ q.2 := hle.2
  by_contra hn
  have hs : q.1 + q.2 ≤ p.1 + p.2 := le_of_not_gt hn
  have he1 : p.1 = q.1 := le_antisymm hp1 (by linarith)
  have he2 : p.2 = q.2 := le_antisymm hp2 (by linarith)
  exact hpq.ne (Prod.ext he1 he2)

/-- One-variable form of the same statement, with `s = u+v`. -/
theorem conditioning_one_variable_strictMonoOn :
    StrictMonoOn (fun s : ℝ => 1 / (1 - s)) {s | 0 ≤ s ∧ s < 1} := by
  intro s hs t ht hst
  change 0 ≤ s ∧ s < 1 at hs
  change 0 ≤ t ∧ t < 1 at ht
  have hd : 0 < 1 - s := by linarith
  have hd' : 0 < 1 - t := by linarith
  apply (div_lt_div_iff₀ hd hd').mpr
  nlinarith

end ElementalPeeling.LoopWall.Positivity


-- Axiom audit: every proved declaration above, including helper lemmas.
