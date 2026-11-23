/-
VOTKP §20.5: equal present summaries, different futures (Jeromie Beasley).

* **§20.5.2.** On the one-excitation basis `{|10⟩, |01⟩}`, the exchange `gX` gives
  `U(t) = cos(gt) I − i sin(gt) X`. For `ψ_φ = (|10⟩ + e^{iφ}|01⟩)/√2` the readout
  `Z = diag(1, −1)` is `⟨Z⟩_t = sin(2gt) sin φ` (`readout`). The preparations `φ = ±π/2` have
  the same norm and the same exchange expectation (zero) (`same_present`), and opposite
  readouts `±sin(2gt)` (`opposite_futures`). The equal local reductions `I/2` of the two
  preparations are not restated here; the paper's §20.5.2 computes them.
* **§20.5.3.** After a nonselective phase measurement the state is `I/2`; under the same `U(t)`
  its readout is `0` (`dephased_readout`).
* **§20.5.5.** For a correlation matrix `C_A = [[C_B, c], [cᵀ, γ]]`, Schur elimination gives
  `det C_A = det C_B · s₁` and `det(I − C_A) = det(I − C_B) · s₀`; when
  `det C_B = det(I − C_B)` the signed offset `log det(I − C_A) − log det C_A` is `log(s₀/s₁)`
  (`offset_schur`). The particle-hole partner `I − C_A` has the opposite offset
  (`offset_particle_hole`).
Developed with AI assistance.
-/
import Mathlib

namespace VOTKP.Witnesses

open Complex Matrix

/-! ## §20.5.2 Equal local summaries, different futures -/

/-- The exchange `X = [[0, 1], [1, 0]]`. -/
def X : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- The readout `Z = diag(1, −1)`. -/
def Z : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- `U(t) = cos(gt) I − i sin(gt) X`, the exchange evolution with the common phase removed. -/
noncomputable def U (g t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(Real.cos (g * t) : ℂ), -I * Real.sin (g * t); -I * Real.sin (g * t), Real.cos (g * t)]

/-- `ψ_φ ∝ (1, e^{iφ})`, with `e^{iφ} = cos φ + i sin φ`; its squared norm is `2`
(`same_present`), so readouts below carry the normalizing `1/2`. -/
noncomputable def psi (φ : ℝ) : Fin 2 → ℂ := ![1, (Real.cos φ : ℂ) + Real.sin φ * I]

/-- The normalized readout `⟨v, Z v⟩/‖v‖² = (|v₀|² − |v₁|²)/2` for `‖v‖² = 2`. -/
noncomputable def readoutOf (v : Fin 2 → ℂ) : ℝ := (normSq (v 0) - normSq (v 1)) / 2

/-- **§20.5.2, the readout.** `⟨Z⟩_t = sin(2gt) sin φ`. -/
theorem readout (g t φ : ℝ) : readoutOf (U g t *ᵥ psi φ) = Real.sin (2 * g * t) * Real.sin φ := by
  have hpy := Real.sin_sq_add_cos_sq φ
  rw [show 2 * g * t = 2 * (g * t) by ring, Real.sin_two_mul]
  simp only [readoutOf, U, psi]
  generalize Real.cos (g * t) = c
  generalize Real.sin (g * t) = s
  generalize Real.cos φ = cf at hpy ⊢
  generalize Real.sin φ = sf at hpy ⊢
  simp [mulVec, dotProduct, Fin.sum_univ_two, normSq_apply]
  linear_combination (s ^ 2 - c ^ 2) / 2 * hpy

/-- **§20.5.2, the present summaries.** Every `ψ_φ` has squared norm `2`, and its normalized
exchange expectation is `⟨ψ, Xψ⟩/2 = cos φ`, which vanishes for both `φ = ±π/2`. -/
theorem same_present (φ : ℝ) :
    normSq (psi φ 0) + normSq (psi φ 1) = 2 ∧
      star (psi φ) ⬝ᵥ (X *ᵥ psi φ) / 2 = (Real.cos φ : ℂ) ∧
      Real.cos (Real.pi / 2) = 0 ∧ Real.cos (-(Real.pi / 2)) = 0 := by
  have hpy := Real.sin_sq_add_cos_sq φ
  refine ⟨?_, ?_, Real.cos_pi_div_two, by rw [Real.cos_neg, Real.cos_pi_div_two]⟩
  · simp only [psi]
    generalize Real.cos φ = cf at hpy ⊢
    generalize Real.sin φ = sf at hpy ⊢
    simp [normSq_apply]
    linear_combination hpy
  · simp only [psi, X]
    generalize Real.cos φ = cf
    generalize Real.sin φ = sf
    apply Complex.ext <;> simp [mulVec, dotProduct, Fin.sum_univ_two] <;> ring

/-- **§20.5.2, different futures.** The two preparations give opposite readouts `±sin(2gt)`;
at `g = 0.7`, `t = 0.4` these are `±sin(0.56) ≈ ±0.531186`. -/
theorem opposite_futures (g t : ℝ) :
    readoutOf (U g t *ᵥ psi (Real.pi / 2)) = Real.sin (2 * g * t) ∧
      readoutOf (U g t *ᵥ psi (-(Real.pi / 2))) = -Real.sin (2 * g * t) := by
  rw [readout, readout, Real.sin_neg, Real.sin_pi_div_two]
  constructor <;> ring

/-! ## §20.5.3 An intervention -/

/-- `U(t)` is unitary. -/
theorem U_unitary (g t : ℝ) : U g t * (U g t)ᴴ = 1 := by
  have hpy := Real.sin_sq_add_cos_sq (g * t)
  simp only [U]
  generalize Real.cos (g * t) = c at hpy ⊢
  generalize Real.sin (g * t) = s at hpy ⊢
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [U, Matrix.mul_apply, Fin.sum_univ_two, Complex.ext_iff, conjTranspose_apply] <;>
    first
      | linear_combination hpy
      | linear_combination (0 : ℝ) * hpy
      | nlinarith [hpy]

/-- **§20.5.3.** The dephased state `ρ = I/2` gives readout `Tr(Z U ρ U†) = 0` under the same
evolution. -/
theorem dephased_readout (g t : ℝ) :
    trace (Z * (U g t * ((1 / 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) * (U g t)ᴴ)) = 0 := by
  rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, U_unitary, Matrix.mul_smul,
    Matrix.mul_one, trace_smul]
  simp [Z, trace, Fin.sum_univ_two]

/-! ## §20.5.5 A boundary residual keeps a signed distinction -/

section Offset

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- `I − [[C_B, c], [cᵀ, γ]] = [[I − C_B, −c], [−cᵀ, 1 − γ]]`. -/
lemma one_sub_fromBlocks (CB : Matrix m m ℝ) (c : Matrix m Unit ℝ) (γ : Matrix Unit Unit ℝ) :
    (1 : Matrix (m ⊕ Unit) (m ⊕ Unit) ℝ) - fromBlocks CB c cᵀ γ
      = fromBlocks (1 - CB) (-c) (-cᵀ) (1 - γ) := by
  ext (i | i) (j | j) <;> simp [Matrix.one_apply]

/-- **§20.5.5, Schur elimination of the offset.** With `s₁ = γ − cᵀC_B⁻¹c` and
`s₀ = (1 − γ) − cᵀ(I − C_B)⁻¹c`, if the interior determinants agree
(`det C_B = det(I − C_B) ≠ 0`) then `det(I − C_A)/det C_A = det s₀ / det s₁`: the interior
factor cancels and the residual keeps the coupling `c`. -/
theorem offset_schur (CB : Matrix m m ℝ) (c : Matrix m Unit ℝ) (γ : Matrix Unit Unit ℝ)
    [Invertible CB] [Invertible (1 - CB)] (heq : det CB = det (1 - CB)) (h0 : det CB ≠ 0) :
    det (1 - fromBlocks CB c cᵀ γ) / det (fromBlocks CB c cᵀ γ)
      = det ((1 - γ) - (-cᵀ) * ⅟(1 - CB) * (-c)) / det (γ - cᵀ * ⅟CB * c) := by
  rw [one_sub_fromBlocks, det_fromBlocks₁₁, det_fromBlocks₁₁, ← heq]
  rw [mul_div_mul_left _ _ h0]

/-- **§20.5.5, the particle-hole partner.** The signed offset
`ϑ(C) = log det(I − C) − log det C` changes sign under `C ↦ I − C`, while any function of the
unordered pair `{C, I − C}`, such as the mode entropy, is unchanged. -/
theorem offset_particle_hole (C : Matrix m m ℝ) :
    (Real.log (det (1 - (1 - C))) - Real.log (det (1 - C)))
      = -(Real.log (det (1 - C)) - Real.log (det C)) := by
  rw [sub_sub_cancel]
  ring

end Offset

end VOTKP.Witnesses
