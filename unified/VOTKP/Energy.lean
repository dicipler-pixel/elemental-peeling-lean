/-
VOTKP energy ledger (Jeromie Beasley, 11 October 2026).
Exact finite-ladder identities, conditional on a supplied threshold function.
These theorems do not assert atomic spectra, transition rates or a binding force.
Developed with AI assistance.
-/
import Mathlib

namespace VOTKP.Energy

/-- Removal energy accumulated through the first q thresholds. -/
noncomputable def removed (I : ℕ → ℝ) (q : ℕ) : ℝ :=
  ∑ j ∈ Finset.range q, I j

/-- Complete neutral-to-bare electronic binding ledger. -/
noncomputable def total (I : ℕ → ℝ) (Z : ℕ) : ℝ := removed I Z

/-- Binding left after q removals. Physical interpretation uses q ≤ Z. -/
noncomputable def binding (I : ℕ → ℝ) (Z q : ℕ) : ℝ :=
  total I Z - removed I q

/-- Ground energy relative to the bare nucleus and free electrons. -/
noncomputable def ground (I : ℕ → ℝ) (Z q : ℕ) : ℝ := -binding I Z q

theorem removed_zero (I : ℕ → ℝ) : removed I 0 = 0 := by
  simp [removed]

theorem removed_succ (I : ℕ → ℝ) (q : ℕ) :
    removed I (q + 1) = removed I q + I q := by
  simp [removed, Finset.sum_range_succ]

theorem binding_neutral (I : ℕ → ℝ) (Z : ℕ) :
    binding I Z 0 = total I Z := by
  simp [binding, removed_zero]

theorem binding_bare (I : ℕ → ℝ) (Z : ℕ) : binding I Z Z = 0 := by
  simp [binding, total]

theorem ground_bare (I : ℕ → ℝ) (Z : ℕ) : ground I Z Z = 0 := by
  simp [ground, binding_bare]

theorem ledger_decomposition (I : ℕ → ℝ) (Z q : ℕ) :
    removed I q + binding I Z q = total I Z := by
  unfold binding
  ring

theorem binding_succ (I : ℕ → ℝ) (Z q : ℕ) :
    binding I Z q = I q + binding I Z (q + 1) := by
  simp only [binding, removed_succ]
  ring

theorem ground_step (I : ℕ → ℝ) (Z q : ℕ) :
    ground I Z (q + 1) - ground I Z q = I q := by
  simp only [ground, binding, removed_succ]
  ring

theorem ground_reference (I : ℕ → ℝ) (Z q : ℕ) :
    ground I Z q = removed I q - total I Z := by
  unfold ground binding
  ring

/-- Any finite sequence of state-energy differences telescopes. -/
theorem energy_telescope (E : ℕ → ℝ) (n : ℕ) :
    (∑ j ∈ Finset.range n, (E (j + 1) - E j)) = E n - E 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    ring

theorem removed_monotone (I : ℕ → ℝ) (hI : ∀ j, 0 ≤ I j) :
    Monotone (removed I) := by
  apply monotone_nat_of_le_succ
  intro q
  rw [removed_succ]
  linarith [hI q]

theorem binding_nonnegative (I : ℕ → ℝ) (hI : ∀ j, 0 ≤ I j)
    (Z q : ℕ) (hq : q ≤ Z) : 0 ≤ binding I Z q := by
  unfold binding total
  exact sub_nonneg.mpr (removed_monotone I hI hq)

/-- Changing the origin of energy leaves every state-energy gap unchanged. -/
theorem energy_origin_invariance (a b c : ℝ) :
    (b + c) - (a + c) = b - a := by ring

/-- The full peel record reconstructs a next threshold from its anchor. -/
theorem peel_anchor_reconstruction (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    a * (1 + (b - a) / (b + a)) / (1 - (b - a) / (b + a)) = b := by
  have hab : b + a ≠ 0 := by linarith
  have hden : 1 - (b - a) / (b + a) ≠ 0 := by
    intro h
    have heq : (b - a) / (b + a) = 1 := by linarith
    have hba : b - a = b + a := (div_eq_one_iff_eq hab).mp heq
    linarith
  field_simp [ha.ne', hab, hden]
  <;> ring

/-- A common positive rescaling preserves the peel but rescales binding. -/
theorem binding_scale (I : ℕ → ℝ) (l : ℝ) (Z q : ℕ) :
    binding (fun j => l * I j) Z q = l * binding I Z q := by
  simp only [binding, total, removed, ← Finset.mul_sum]
  ring

noncomputable def toyA (j : ℕ) : ℝ := if j = 0 then 1 else if j = 1 then 2 else 6
noncomputable def toyB (j : ℕ) : ℝ := if j = 0 then 1 else if j = 1 then 3 else 6

/-- The same first threshold does not determine complete binding. -/
theorem first_threshold_not_total :
    toyA 0 = toyB 0 ∧ total toyA 3 = 9 ∧ total toyB 3 = 10 := by
  norm_num [toyA, toyB, total, removed, Finset.sum_range_succ]

/-- A gap without a coupling weight does not determine a weighted readout. -/
theorem same_gap_different_weights :
    (1 : ℝ) / 2 ≠ 3 / 2 := by norm_num

end VOTKP.Energy
