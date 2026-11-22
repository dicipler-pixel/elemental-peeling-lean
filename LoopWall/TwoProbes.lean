import Mathlib

/-!
# Two probes on a two-qubit phase state

Direction D8.  `left_marginal`/`right_marginal` are `(1/2) • 1` for every phase;
`expectation_probeA = cos Φ`, `expectation_probeB = −sin Φ`, and `requested_probeB_formula_is_false`
records that the sign I first wrote is wrong, with `expectation_sineProbe` the probe that reads
`+sin Φ`; `supplement_observations_ne` separates `Φ` from `π − Φ`, while
`marginals_do_not_determine_phase` and `marginals_do_not_determine_state` show the marginals
alone keep nothing.

Written in the second parallel formalization round (swarm `smws2pzvk`, direction m8),
then recompiled and reviewed here; namespace and header added, `lemma` renamed to `theorem` so the
repository audit sees it, trailing `#print axioms` lines removed because `scripts/verify.py` audits
every named theorem.  See PROVENANCE.md.
-/

namespace ElementalPeeling.LoopWall.TwoProbes

open scoped Matrix Complex

abbrev QubitPair := Fin 4

/-- The basis index of a pair of qubits, in the order `00, 01, 10, 11`. -/
def idx : Fin 2 × Fin 2 → QubitPair := fun p => !![0, 1; 2, 3] p.1 p.2

def ket (i : QubitPair) : QubitPair → ℂ := fun j => if j = i then 1 else 0

def outer (v w : QubitPair → ℂ) : Matrix QubitPair QubitPair ℂ :=
  fun i j => v i * (starRingEnd ℂ) (w j)

/-- `phase Φ = exp (I * Φ)`, with the real parameter coerced to `ℂ`. -/
noncomputable def phase (Φ : ℝ) : ℂ := Complex.exp (Complex.I * (Φ : ℂ))

/-- `( |01⟩ + exp(I Φ) |10⟩ ) / √2`. -/
noncomputable def psi (Φ : ℝ) : QubitPair → ℂ :=
  ![0, (Real.sqrt 2 : ℂ)⁻¹, phase Φ * (Real.sqrt 2 : ℂ)⁻¹, 0]

noncomputable def rho (Φ : ℝ) : Matrix QubitPair QubitPair ℂ := outer (psi Φ) (psi Φ)

/-- Left reduced density matrix, obtained by summing over the right qubit. -/
noncomputable def leftMarginal (Φ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun a b => ∑ c, rho Φ (idx (a, c)) (idx (b, c))

/-- Right reduced density matrix, obtained by summing over the left qubit. -/
noncomputable def rightMarginal (Φ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun c d => ∑ a, rho Φ (idx (a, c)) (idx (a, d))

/-- `|01⟩⟨10| + |10⟩⟨01|`. -/
def probeA : Matrix QubitPair QubitPair ℂ :=
  outer (ket (idx (0, 1))) (ket (idx (1, 0))) +
    outer (ket (idx (1, 0))) (ket (idx (0, 1)))

/-- The probe `B` exactly as written in the question. -/
def probeB : Matrix QubitPair QubitPair ℂ :=
  Complex.I • (outer (ket (idx (0, 1))) (ket (idx (1, 0))) -
    outer (ket (idx (1, 0))) (ket (idx (0, 1))))

/-- The sign-corrected sine probe, `-probeB`. -/
def sineProbe : Matrix QubitPair QubitPair ℂ := -probeB

/-- The standard bra--ket expectation `⟨v|M|v⟩`. -/
noncomputable def expectation (v : QubitPair → ℂ) (M : Matrix QubitPair QubitPair ℂ) : ℂ :=
  ∑ i, ∑ j, (starRingEnd ℂ) (v i) * M i j * v j

theorem phase_eq (Φ : ℝ) : phase Φ = (Real.cos Φ : ℂ) + (Real.sin Φ : ℂ) * Complex.I := by
  rw [phase, mul_comm, Complex.exp_ofReal_mul_I]

theorem sqrt_two_cast_ne_zero : (Real.sqrt 2 : ℂ) ≠ 0 := by
  exact Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (by norm_num)))

theorem inv_sqrt_two_mul_self : (Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ = 1 / 2 := by
  field_simp [sqrt_two_cast_ne_zero]
  norm_cast
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

theorem phase_mul_conj (Φ : ℝ) : phase Φ * (starRingEnd ℂ) (phase Φ) = 1 := by
  rw [phase_eq]
  simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
  calc
    ((Real.cos Φ : ℂ) + (Real.sin Φ : ℂ) * Complex.I) *
        ((Real.cos Φ : ℂ) + (Real.sin Φ : ℂ) * -Complex.I) =
        (Real.cos Φ : ℂ) * (Real.cos Φ : ℂ) +
          (Real.sin Φ : ℂ) * (Real.sin Φ : ℂ) := by
      calc
        _ = (Real.cos Φ : ℂ) * (Real.cos Φ : ℂ) -
            ((Real.sin Φ : ℂ) * (Real.sin Φ : ℂ)) * (Complex.I * Complex.I) := by ring
        _ = _ := by rw [Complex.I_mul_I]; ring
    _ = ((Real.cos Φ ^ 2 + Real.sin Φ ^ 2 : ℝ) : ℂ) := by
      simp only [Complex.ofReal_add, Complex.ofReal_mul, pow_two]
    _ = 1 := by norm_cast; nlinarith [Real.sin_sq_add_cos_sq Φ]

theorem phase_normalized (Φ : ℝ) :
    phase Φ * (Real.sqrt 2 : ℂ)⁻¹ *
      ((starRingEnd ℂ) (phase Φ) * (Real.sqrt 2 : ℂ)⁻¹) = 1 / 2 := by
  calc
    _ = (phase Φ * (starRingEnd ℂ) (phase Φ)) *
        ((Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹) := by ring
    _ = 1 / 2 := by rw [phase_mul_conj, inv_sqrt_two_mul_self, one_mul]

theorem left_marginal (Φ : ℝ) : leftMarginal Φ = (1 / 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [leftMarginal, rho, outer, psi, idx, Fin.sum_univ_two,
      inv_sqrt_two_mul_self, phase_normalized]

theorem right_marginal (Φ : ℝ) : rightMarginal Φ = (1 / 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rightMarginal, rho, outer, psi, idx, Fin.sum_univ_two,
      inv_sqrt_two_mul_self, phase_normalized]

theorem phase_add_conj (Φ : ℝ) :
    phase Φ + (starRingEnd ℂ) (phase Φ) = 2 * (Real.cos Φ : ℂ) := by
  rw [phase_eq]
  simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
  ring

theorem phase_sub_conj (Φ : ℝ) :
    phase Φ - (starRingEnd ℂ) (phase Φ) = 2 * (Real.sin Φ : ℂ) * Complex.I := by
  rw [phase_eq]
  simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
  ring

theorem expectation_probeA (Φ : ℝ) : expectation (psi Φ) probeA = (Real.cos Φ : ℂ) := by
  conv_lhs => simp [expectation, probeA, outer, ket, psi, idx, Fin.sum_univ_four]
  calc
    _ = (phase Φ + (starRingEnd ℂ) (phase Φ)) *
        ((Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹) := by ring
    _ = (2 * (Real.cos Φ : ℂ)) * (1 / 2) := by
      rw [phase_add_conj, inv_sqrt_two_mul_self]
    _ = (Real.cos Φ : ℂ) := by ring

theorem expectation_probeB (Φ : ℝ) : expectation (psi Φ) probeB = -(Real.sin Φ : ℂ) := by
  conv_lhs => simp [expectation, probeB, outer, ket, psi, idx, Fin.sum_univ_four]
  calc
    _ = Complex.I * (phase Φ - (starRingEnd ℂ) (phase Φ)) *
        ((Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹) := by ring
    _ = Complex.I * (2 * (Real.sin Φ : ℂ) * Complex.I) * (1 / 2) := by
      rw [phase_sub_conj, inv_sqrt_two_mul_self]
    _ = (Real.sin Φ : ℂ) * (Complex.I * Complex.I) := by ring
    _ = -(Real.sin Φ : ℂ) := by rw [Complex.I_mul_I]; ring

theorem expectation_neg (v : QubitPair → ℂ) (M : Matrix QubitPair QubitPair ℂ) :
    expectation v (-M) = -expectation v M := by
  simp [expectation, mul_neg]

theorem expectation_sineProbe (Φ : ℝ) :
    expectation (psi Φ) sineProbe = (Real.sin Φ : ℂ) := by
  rw [sineProbe, expectation_neg, expectation_probeB, neg_neg]

/-- The requested `+sin Φ` formula for `probeB` is false under `⟨v|B|v⟩`. -/
theorem requested_probeB_formula_is_false :
    ¬ ∀ Φ : ℝ, expectation (psi Φ) probeB = (Real.sin Φ : ℂ) := by
  intro h
  have h' := h (Real.pi / 2)
  rw [expectation_probeB, Real.sin_pi_div_two] at h'
  norm_num at h'

/-- The two corrected probe readings, regarded as one ordered pair. -/
noncomputable def observations (Φ : ℝ) : ℂ × ℂ :=
  (expectation (psi Φ) probeA, expectation (psi Φ) sineProbe)

theorem observations_eq (Φ : ℝ) :
    observations Φ = ((Real.cos Φ : ℂ), (Real.sin Φ : ℂ)) := by
  rw [observations, expectation_probeA, expectation_sineProbe]

theorem supplement_left_marginal (Φ : ℝ) :
    leftMarginal (Real.pi - Φ) = leftMarginal Φ := by
  rw [left_marginal, left_marginal]

theorem supplement_right_marginal (Φ : ℝ) :
    rightMarginal (Real.pi - Φ) = rightMarginal Φ := by
  rw [right_marginal, right_marginal]

theorem supplement_probeA_expectation (Φ : ℝ) :
    expectation (psi (Real.pi - Φ)) probeA = -expectation (psi Φ) probeA := by
  rw [expectation_probeA, expectation_probeA, Real.cos_pi_sub, Complex.ofReal_neg]

theorem supplement_sineProbe_expectation (Φ : ℝ) :
    expectation (psi (Real.pi - Φ)) sineProbe = expectation (psi Φ) sineProbe := by
  rw [expectation_sineProbe, expectation_sineProbe, Real.sin_pi_sub]

/-- In a nondegenerate case, the first corrected probe separates the supplements. -/
theorem supplement_observations_ne (Φ : ℝ) (hΦ : Real.cos Φ ≠ 0) :
    observations (Real.pi - Φ) ≠ observations Φ := by
  intro h
  have hA := congrArg Prod.fst h
  change expectation (psi (Real.pi - Φ)) probeA = expectation (psi Φ) probeA at hA
  rw [expectation_probeA, expectation_probeA, Real.cos_pi_sub, Complex.ofReal_neg] at hA
  apply hΦ
  apply Complex.ofReal_eq_zero.mp
  linear_combination -hA / 2

/-- Without `cos Φ ≠ 0`, universal supplement separation is false. -/
theorem supplement_observations_eq_iff (Φ : ℝ) :
    observations (Real.pi - Φ) = observations Φ ↔ Real.cos Φ = 0 := by
  constructor
  · intro h
    by_contra hΦ
    exact supplement_observations_ne Φ hΦ h
  · intro hΦ
    rw [observations_eq, observations_eq, Real.cos_pi_sub, Real.sin_pi_sub, hΦ]
    norm_num

theorem universal_supplement_separation_is_false :
    ¬ ∀ Φ : ℝ, observations (Real.pi - Φ) ≠ observations Φ := by
  intro h
  apply h (Real.pi / 2)
  congr 1
  ring

theorem phase_zero : phase 0 = 1 := by
  simp [phase]

theorem phase_pi_div_two : phase (Real.pi / 2) = Complex.I := by
  rw [phase_eq, Real.cos_pi_div_two, Real.sin_pi_div_two]
  norm_num

theorem psi_eq_iff_phase_eq (Φ Ψ : ℝ) : psi Φ = psi Ψ ↔ phase Φ = phase Ψ := by
  constructor
  · intro h
    have h2 := congrFun h (idx (1, 0))
    simp [psi, idx] at h2
    exact h2
  · intro h
    simp [psi, h]

theorem phase_zero_ne_pi_div_two : phase 0 ≠ phase (Real.pi / 2) := by
  rw [phase_zero, phase_pi_div_two]
  intro h
  have him := congrArg Complex.im h
  norm_num at him

theorem psi_zero_ne_pi_div_two : psi 0 ≠ psi (Real.pi / 2) := by
  intro h
  exact phase_zero_ne_pi_div_two ((psi_eq_iff_phase_eq 0 (Real.pi / 2)).mp h)

/-- Equal marginals do not determine the relative phase. -/
theorem marginals_do_not_determine_phase :
    ∃ Φ Ψ : ℝ, leftMarginal Φ = leftMarginal Ψ ∧
      rightMarginal Φ = rightMarginal Ψ ∧ phase Φ ≠ phase Ψ := by
  refine ⟨0, Real.pi / 2, ?_, ?_, phase_zero_ne_pi_div_two⟩
  · rw [left_marginal, left_marginal]
  · rw [right_marginal, right_marginal]

/-- Indeed, the same two marginal matrices accompany two different state vectors. -/
theorem marginals_do_not_determine_state :
    ∃ Φ Ψ : ℝ, leftMarginal Φ = leftMarginal Ψ ∧
      rightMarginal Φ = rightMarginal Ψ ∧ psi Φ ≠ psi Ψ := by
  refine ⟨0, Real.pi / 2, ?_, ?_, psi_zero_ne_pi_div_two⟩
  · rw [left_marginal, left_marginal]
  · rw [right_marginal, right_marginal]


end ElementalPeeling.LoopWall.TwoProbes
