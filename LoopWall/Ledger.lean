import Mathlib

/-!
# The peel ledger: log spacing, telescoping, scale invariance, reconstruction

Direction D5.  `gam_eq_tanh_half_log` proves `Γ = tanh(½ log z)`; `prod_range_ratios` and
`sum_range_log_ratios` (with their `Fin` versions) telescope; `gam_scale` is the exact loss of
absolute scale; `reconstruct_range` inverts a positive ladder from its reflections;
`reciprocal_variance`, `reciprocal_scale_at_wall` and `gam_of_nu` close the ν-chain.

Written in the parallel formalization round (swarm `smws25izm`, direction m4),
then recompiled and reviewed here; namespace and header added, trailing `#print axioms` lines
removed because `scripts/verify.py` audits every named theorem.  See PROVENANCE.md.
-/

/-!
# D5: ledger and scale invariance

The peel reflection is defined over the reals.  Finite products and sums use
`Fin n` for the steps of a ladder with `n + 1` entries.  Reconstruction is
also stated for an infinite positive sequence and a product over `range k`;
this includes every finite ladder and avoids a dependent-cast in its statement.
-/

namespace ElementalPeeling.LoopWall.Ledger

open scoped BigOperators
open Finset

/-- The reflection associated with a positive peel ratio. -/
noncomputable def gam (z : ℝ) : ℝ := (z - 1) / (z + 1)

/-- The logarithmic-ledger form of the reflection. -/
theorem gam_eq_tanh_half_log (z : ℝ) (hz : 0 < z) :
    gam z = Real.tanh (Real.log z / 2) := by
  have hs : 0 < Real.sqrt z := Real.sqrt_pos.2 hz
  have hs0 : Real.sqrt z ≠ 0 := ne_of_gt hs
  have hsq : (Real.sqrt z) ^ 2 = z := Real.sq_sqrt hz.le
  rw [Real.tanh_eq, Real.exp_neg, Real.exp_half, Real.exp_log hz]
  unfold gam
  field_simp [hs0]
  nlinarith

/-- A nonzero sequence has the usual telescoping product of consecutive ratios. -/
theorem prod_range_ratios (I : ℕ → ℝ) (hI : ∀ k, I k ≠ 0) (n : ℕ) :
    (∏ k ∈ range n, I (k + 1) / I k) = I n / I 0 := by
  induction n with
  | zero => simp [hI 0]
  | succ n ih =>
      rw [prod_range_succ, ih]
      field_simp [hI 0, hI n]

/-- Telescope the consecutive ratios of a finite positive ladder. -/
theorem fin_prod_ratios {n : ℕ} (I : Fin (n + 1) → ℝ)
    (hI : ∀ k, I k ≠ 0) :
    (∏ k : Fin n, I k.succ / I k.castSucc) = I (Fin.last n) / I 0 := by
  rw [Finset.prod_fin_eq_prod_range]
  let J : ℕ → ℝ := fun k => if h : k < n + 1 then I ⟨k, h⟩ else 1
  have hJ : ∀ k, J k ≠ 0 := by
    intro k
    simp only [J]
    split_ifs with h
    · exact hI _
    · exact one_ne_zero
  have ht := prod_range_ratios J hJ n
  simp only [J] at ht
  convert ht using 1
  · apply Finset.prod_congr rfl
    intro k hk
    have hk' : k < n := mem_range.mp hk
    have hkn : k < n + 1 := Nat.lt_succ_of_lt hk'
    have hks : k + 1 < n + 1 := Nat.succ_lt_succ hk'
    simp [hk', hkn, hks]
  · simp only [Nat.lt_succ_self, Nat.zero_lt_succ, dite_true]
    rfl

/-- The logarithms of consecutive ratios telescope. -/
theorem sum_range_log_ratios (I : ℕ → ℝ) (hI : ∀ k, I k ≠ 0) (n : ℕ) :
    (∑ k ∈ range n, Real.log (I (k + 1) / I k)) = Real.log (I n / I 0) := by
  have hlog (k : ℕ) : Real.log (I (k + 1) / I k) =
      Real.log (I (k + 1)) - Real.log (I k) :=
    Real.log_div (hI (k + 1)) (hI k)
  calc
    _ = ∑ k ∈ range n, (Real.log (I (k + 1)) - Real.log (I k)) := by
      apply Finset.sum_congr rfl
      intro k _
      exact hlog k
    _ = Real.log (I n) - Real.log (I 0) :=
      Finset.sum_range_sub (fun k => Real.log (I k)) n
    _ = Real.log (I n / I 0) := (Real.log_div (hI n) (hI 0)).symm

/-- The logarithmic ledger of a finite positive ladder telescopes. -/
theorem fin_sum_log_ratios {n : ℕ} (I : Fin (n + 1) → ℝ)
    (hI : ∀ k, I k ≠ 0) :
    (∑ k : Fin n, Real.log (I k.succ / I k.castSucc)) =
      Real.log (I (Fin.last n) / I 0) := by
  rw [Finset.sum_fin_eq_sum_range]
  let J : ℕ → ℝ := fun k => if h : k < n + 1 then I ⟨k, h⟩ else 1
  have hJ : ∀ k, J k ≠ 0 := by
    intro k
    simp only [J]
    split_ifs with h
    · exact hI _
    · exact one_ne_zero
  have ht := sum_range_log_ratios J hJ n
  simp only [J] at ht
  convert ht using 1
  · apply Finset.sum_congr rfl
    intro k hk
    have hk' : k < n := mem_range.mp hk
    have hkn : k < n + 1 := Nat.lt_succ_of_lt hk'
    have hks : k + 1 < n + 1 := Nat.succ_lt_succ hk'
    simp [hk', hkn, hks]
  · simp only [Nat.lt_succ_self, Nat.zero_lt_succ, dite_true]
    rfl

/-- A reflection coefficient recovers its positive ratio. -/
theorem inverse_gam (z : ℝ) (hz : 0 < z) : (1 + gam z) / (1 - gam z) = z := by
  have hz0 : z ≠ 0 := ne_of_gt hz
  have hz1 : z + 1 ≠ 0 := by positivity
  unfold gam
  field_simp
  ring

/-- Positive scaling of both thresholds leaves the reflection unchanged. -/
theorem gam_scale (a b c : ℝ) (hc : 0 < c) :
    gam ((c * b) / (c * a)) = gam (b / a) := by
  rw [mul_div_mul_left b a (ne_of_gt hc)]

/-- Reconstruct any initial segment of a positive sequence from its reflections. -/
theorem reconstruct_range (I Γ : ℕ → ℝ) (hI : ∀ k, 0 < I k)
    (hΓ : ∀ k, Γ k = gam (I (k + 1) / I k)) (n : ℕ) :
    I n = I 0 * ∏ k ∈ range n, (1 + Γ k) / (1 - Γ k) := by
  have hfactor (k : ℕ) : (1 + Γ k) / (1 - Γ k) = I (k + 1) / I k := by
    rw [hΓ]
    exact inverse_gam _ (div_pos (hI (k + 1)) (hI k))
  simp_rw [hfactor]
  rw [prod_range_ratios I (fun k => ne_of_gt (hI k))]
  field_simp [ne_of_gt (hI 0)]

/-- The two reciprocal-variance coordinates satisfy the exact complement identity. -/
theorem reciprocal_variance (ν Γ : ℝ) (hΓ : Γ = 1 - 2 * ν) :
    ν * (1 - ν) = (1 - Γ ^ 2) / 4 := by
  rw [hΓ]
  ring

/-- At the loop wall the reciprocal scale `4 / (1 - Γ²)` is eight. -/
theorem reciprocal_scale_at_wall (Γ : ℝ) (hΓ : Γ ^ 2 = 1 / 2) :
    4 / (1 - Γ ^ 2) = 8 := by
  rw [hΓ]
  norm_num

/-- The ratio `(1 - ν) / ν` has reflection `1 - 2ν`. -/
theorem gam_of_nu (ν : ℝ) (hν0 : 0 < ν) (hν1 : ν < 1) :
    gam ((1 - ν) / ν) = 1 - 2 * ν := by
  have hν : ν ≠ 0 := ne_of_gt hν0
  have hd : (1 - ν) / ν + 1 ≠ 0 := by
    have : (1 - ν) / ν + 1 = 1 / ν := by field_simp; ring
    rw [this]
    positivity
  unfold gam
  field_simp
  ring

/-- Reversing a positive peel step negates its reflection. -/
theorem gam_reverse (z : ℝ) (hz : 0 < z) : gam (1 / z) = -gam z := by
  have hz0 : z ≠ 0 := ne_of_gt hz
  have hz1 : z + 1 ≠ 0 := by positivity
  unfold gam
  field_simp
  ring

/-- Reversal preserves returned power. -/
theorem gam_sq_reverse (z : ℝ) (hz : 0 < z) :
    (gam (1 / z)) ^ 2 = (gam z) ^ 2 := by
  rw [gam_reverse z hz]
  ring

end ElementalPeeling.LoopWall.Ledger
