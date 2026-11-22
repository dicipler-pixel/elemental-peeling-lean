import Mathlib
/-!
# Junction energy: the commutator identity and the block Frobenius identity

Direction D3.  `junction_commutator`: `HH† − H†H = −2(DA − AD)` for `H = D + A` with `D`
Hermitian and `A` skew-adjoint.  The module records that the two-block matrix with lower-left
block `Aᴴ` is Hermitian, so its residual vanishes and the identity fails as I first stated it
(`original_block_energy_identity_false`), and proves the correct two-block statement for the
anti-Hermitian convention of the paper: `(1/8)‖HH† − H†H‖_F² = ‖D₀ − A D₁ Aᴴ‖_F²` for `A` unitary
(`corrected_junction_energy`, `corrected_junction_energy_sum`).

Written in the parallel formalization round (swarm `smws25izm`, direction m8),
then recompiled and reviewed here; namespace and header added, trailing `#print axioms` lines
removed because `scripts/verify.py` audits every named theorem.  See PROVENANCE.md.
-/

/-
Junction energy for finite complex block matrices.

The sign in the two-block formula of the prompt is inconsistent as written:
`fromBlocks D₀ A Aᴴ D₁` is Hermitian when `D₀` and `D₁` are Hermitian.  The
file proves that its residual is zero and refutes the claimed identity with
`D₀ = 0`, `D₁ = A = 1` on `Fin 1`.

The corrected Hamiltonian is `fromBlocks D₀ A (-Aᴴ) D₁`, exactly a
self-adjoint diagonal part plus a skew-adjoint off-diagonal part.  For this
matrix the desired factor-eight identity is proved for finite block types.
`energy` is exactly the entrywise sum of squared complex absolute values.
-/


namespace ElementalPeeling.LoopWall.Junction

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The Hermitian-minus-skew commutator identity. -/
theorem junction_commutator (D A : Matrix n n ℂ)
    (hD : Dᴴ = D) (hA : Aᴴ = -A) :
    (D + A) * (D + A)ᴴ - (D + A)ᴴ * (D + A) = -2 * (D * A - A * D) := by
  simp only [Matrix.conjTranspose_add, hD, hA]
  noncomm_ring

end ElementalPeeling.LoopWall.Junction


namespace ElementalPeeling.LoopWall.Junction

open Matrix

/-- `energy M` is the squared Frobenius norm, written entrywise. -/
noncomputable def energy {m n : Type*} [Fintype m] [Fintype n] (M : Matrix m n ℂ) : ℝ :=
  ∑ i, ∑ j, ‖M i j‖ ^ 2

theorem fromBlocks_sub {m n p q : Type*} {α : Type*} [Sub α]
    (A : Matrix m n α) (B : Matrix m p α) (C : Matrix q n α) (D : Matrix q p α)
    (A' : Matrix m n α) (B' : Matrix m p α) (C' : Matrix q n α) (D' : Matrix q p α) :
    Matrix.fromBlocks A B C D - Matrix.fromBlocks A' B' C' D' =
      Matrix.fromBlocks (A - A') (B - B') (C - C') (D - D') := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> rfl

/-- The residual whose off-diagonal blocks carry the junction energy. -/
def residual {n : Type*} [Fintype n] (H : Matrix n n ℂ) : Matrix n n ℂ :=
  H * Hᴴ - Hᴴ * H

/-- The Hamiltonian with skew-adjoint off-diagonal part (the sign needed for (i)). -/
def correctedJunction {m n : Type*} (D₀ : Matrix m m ℂ) (D₁ : Matrix n n ℂ)
    (A : Matrix m n ℂ) : Matrix (m ⊕ n) (m ⊕ n) ℂ :=
  Matrix.fromBlocks D₀ A (-Aᴴ) D₁

variable {m p : Type*} [Fintype m] [Fintype p]

theorem correctedJunction_residual (D₀ : Matrix m m ℂ) (D₁ : Matrix p p ℂ)
    (A : Matrix m p ℂ) (hD₀ : D₀ᴴ = D₀) (hD₁ : D₁ᴴ = D₁) :
    residual (correctedJunction D₀ D₁ A) =
      Matrix.fromBlocks 0 ((-2 : ℂ) • (D₀ * A - A * D₁))
        ((2 : ℂ) • (D₁ * Aᴴ - Aᴴ * D₀)) 0 := by
  rw [residual, correctedJunction, Matrix.fromBlocks_conjTranspose]
  simp only [hD₀, hD₁, Matrix.conjTranspose_neg, Matrix.conjTranspose_conjTranspose,
    Matrix.fromBlocks_multiply]
  rw [fromBlocks_sub]
  rw [Matrix.fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [neg_smul, neg_neg, Matrix.neg_mul, Matrix.mul_neg] <;>
    module

end ElementalPeeling.LoopWall.Junction

namespace ElementalPeeling.LoopWall.Junction

open Matrix

theorem energy_zero {m n : Type*} [Fintype m] [Fintype n] :
    energy (0 : Matrix m n ℂ) = 0 := by
  simp [energy]

theorem energy_fromBlocks {m n p q : Type*} [Fintype m] [Fintype n]
    [Fintype p] [Fintype q] (A : Matrix m n ℂ) (B : Matrix m p ℂ)
    (C : Matrix q n ℂ) (D : Matrix q p ℂ) :
    energy (Matrix.fromBlocks A B C D) = energy A + energy B + energy C + energy D := by
  simp only [energy, Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁,
    Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  ring

theorem energy_eq_trace_re {m n : Type*} [Fintype m] [Fintype n] (M : Matrix m n ℂ) :
    energy M = (Matrix.trace (M * Mᴴ)).re := by
  simp [energy, Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.mul_conj, Complex.normSq_eq_norm_sq]
  norm_cast

theorem energy_conjTranspose {m n : Type*} [Fintype m] [Fintype n] (M : Matrix m n ℂ) :
    energy Mᴴ = energy M := by
  rw [energy_eq_trace_re, energy_eq_trace_re, Matrix.conjTranspose_conjTranspose,
    Matrix.trace_mul_comm]

theorem energy_neg {m n : Type*} [Fintype m] [Fintype n] (M : Matrix m n ℂ) :
    energy (-M) = energy M := by
  simp [energy]

theorem energy_smul {m n : Type*} [Fintype m] [Fintype n] (c : ℂ) (M : Matrix m n ℂ) :
    energy (c • M) = ‖c‖ ^ 2 * energy M := by
  simp [energy, mul_pow, Finset.mul_sum]

theorem energy_mul_right_unitary {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
    [DecidableEq n] (E : Matrix m n ℂ) (A : Matrix n p ℂ) (hA : A * Aᴴ = 1) :
    energy (E * A) = energy E := by
  rw [energy_eq_trace_re, energy_eq_trace_re]
  congr 1
  congr 1
  rw [Matrix.conjTranspose_mul]
  calc
    (E * A) * (Aᴴ * Eᴴ) = E * (A * Aᴴ) * Eᴴ := by
      simp only [Matrix.mul_assoc]
    _ = E * Eᴴ := by rw [hA, Matrix.mul_one]

end ElementalPeeling.LoopWall.Junction

namespace ElementalPeeling.LoopWall.Junction

open Matrix

/-- Corrected form of the two-block identity: the lower-left block must be `-Aᴴ`,
not `Aᴴ`, for the block Hamiltonian to have the self-adjoint + skew-adjoint form in (i). -/
theorem corrected_junction_energy {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (D₀ : Matrix m m ℂ) (D₁ : Matrix n n ℂ) (A : Matrix m n ℂ)
    (hD₀ : D₀ᴴ = D₀) (hD₁ : D₁ᴴ = D₁)
    (hA : A * Aᴴ = 1) (hA' : Aᴴ * A = 1) :
    (1 / 8 : ℝ) * energy (residual (correctedJunction D₀ D₁ A)) =
      energy (D₀ - A * D₁ * Aᴴ) := by
  let F : Matrix m n ℂ := D₀ * A - A * D₁
  let E : Matrix m m ℂ := D₀ - A * D₁ * Aᴴ
  have hEA : E * A = F := by
    simp only [E, F, Matrix.sub_mul, Matrix.mul_assoc, hA', Matrix.mul_one]
  have hF : energy F = energy E := by
    calc
      energy F = energy (E * A) := by rw [hEA]
      _ = energy E := energy_mul_right_unitary E A hA
  have hG : D₁ * Aᴴ - Aᴴ * D₀ = -Fᴴ := by
    simp only [F, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hD₀, hD₁]
    abel
  have hGenergy : energy (D₁ * Aᴴ - Aᴴ * D₀) = energy F := by
    calc
      energy (D₁ * Aᴴ - Aᴴ * D₀) = energy (-Fᴴ) := congrArg energy hG
      _ = energy Fᴴ := energy_neg Fᴴ
      _ = energy F := energy_conjTranspose F
  have hmain : energy (residual (correctedJunction D₀ D₁ A)) = 8 * energy E := by
    rw [correctedJunction_residual D₀ D₁ A hD₀ hD₁, energy_fromBlocks,
      energy_smul, energy_smul, energy_zero, energy_zero]
    norm_num [hGenergy, hF, F]
    ring
  rw [hmain]
  simp only [E]
  ring

end ElementalPeeling.LoopWall.Junction

namespace ElementalPeeling.LoopWall.Junction

open Matrix

/-- The corrected identity with `energy` unfolded to the exact entrywise sums
in the mathematical statement. -/
theorem corrected_junction_energy_sum {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (D₀ : Matrix m m ℂ) (D₁ : Matrix n n ℂ) (A : Matrix m n ℂ)
    (hD₀ : D₀ᴴ = D₀) (hD₁ : D₁ᴴ = D₁)
    (hA : A * Aᴴ = 1) (hA' : Aᴴ * A = 1) :
    (1 / 8 : ℝ) *
        ∑ i, ∑ j, ‖residual (correctedJunction D₀ D₁ A) i j‖ ^ 2 =
      ∑ i, ∑ j, ‖(D₀ - A * D₁ * Aᴴ) i j‖ ^ 2 := by
  simpa only [energy] using corrected_junction_energy D₀ D₁ A hD₀ hD₁ hA hA'

end ElementalPeeling.LoopWall.Junction


namespace ElementalPeeling.LoopWall.Junction

open Matrix

/-- The block matrix in the original statement, with lower-left block `Aᴴ`. -/
def originalJunction {m n : Type*} (D₀ : Matrix m m ℂ) (D₁ : Matrix n n ℂ)
    (A : Matrix m n ℂ) : Matrix (m ⊕ n) (m ⊕ n) ℂ :=
  Matrix.fromBlocks D₀ A Aᴴ D₁

theorem originalJunction_conjTranspose {m n : Type*} [Fintype m] [Fintype n]
    (D₀ : Matrix m m ℂ) (D₁ : Matrix n n ℂ) (A : Matrix m n ℂ)
    (hD₀ : D₀ᴴ = D₀) (hD₁ : D₁ᴴ = D₁) :
    (originalJunction D₀ D₁ A)ᴴ = originalJunction D₀ D₁ A := by
  simp only [originalJunction, Matrix.fromBlocks_conjTranspose, hD₀, hD₁,
    Matrix.conjTranspose_conjTranspose]

/-- With the sign in the original statement the block Hamiltonian is Hermitian,
so its residual is identically zero. -/
theorem originalJunction_residual {m n : Type*} [Fintype m] [Fintype n]
    (D₀ : Matrix m m ℂ) (D₁ : Matrix n n ℂ) (A : Matrix m n ℂ)
    (hD₀ : D₀ᴴ = D₀) (hD₁ : D₁ᴴ = D₁) :
    residual (originalJunction D₀ D₁ A) = 0 := by
  rw [residual, originalJunction_conjTranspose D₀ D₁ A hD₀ hD₁]
  simp

/-- Exact `1 × 1`-block counterexample to the identity as written.
Take `D₀ = 0`, `D₁ = A = 1`; all hypotheses hold, but the left side is zero
and the right side is one. -/
theorem original_block_energy_identity_false :
    ¬ (∀ (D₀ D₁ A : Matrix (Fin 1) (Fin 1) ℂ),
      D₀ᴴ = D₀ → D₁ᴴ = D₁ → A * Aᴴ = 1 → Aᴴ * A = 1 →
      (1 / 8 : ℝ) * energy (residual (originalJunction D₀ D₁ A)) =
        energy (D₀ - A * D₁ * Aᴴ)) := by
  intro h
  have he := h 0 1 1 (by simp) (by simp) (by simp) (by simp)
  rw [originalJunction_residual 0 1 1 (by simp) (by simp), energy_zero] at he
  norm_num [energy] at he

end ElementalPeeling.LoopWall.Junction
