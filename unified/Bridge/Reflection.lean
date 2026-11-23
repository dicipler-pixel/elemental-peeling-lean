import Mathlib
import LoopWall.Ledger
import LoopWall.Wall
import LoopWall.CompositionBridge
import DiracTime.PathLedger
import VOTKP.Smith

/-!
# Bridge I — the peel ledger, the reflection, and the wall

This file is the first of three that join the *elemental peeling / loop wall* development to
*Dirac Time* and to *VOTKP*.  It contains only statements that are not in any of the three:

* `log_wall_ratio`, `wall_ledger_value` — the wall is a **quantised ledger value**:
  if the peel ledger is `ℓ = log z` and the reflection is `Γ = tanh (ℓ/2)`, then `Γ² = 1/2`
  forces `ℓ = ±2 log (1 + √2)`.
* `tanh_ledger_descent` — Dirac Time's `PathLedger.descent_iff` read through the peel
  coordinate: `Γ` is a function of the endpoints alone exactly when every closed loop is
  silent.  This is the join between the two ledger theorems.
* `wall_iff_share_det`, `gam_sq_eq_one_iff_det_zero` — the wall and the perfect-reflection
  limit in the two-channel determinant coordinates that `CompositionBridge` uses.

Nothing here mentions an element, a spectrum, or a measurement.
-/

namespace Unified.Bridge.Reflection

open ElementalPeeling.LoopWall.Ledger (gam)

/-! ## 1. The wall as a quantised ledger value -/

/-- `3 + 2√2 = (1 + √2)²`, so its logarithm is twice `log (1 + √2)`. -/
theorem log_wall_ratio :
    Real.log (3 + 2 * Real.sqrt 2) = 2 * Real.log (1 + Real.sqrt 2) := by
  have hp : 0 < 1 + Real.sqrt 2 := by positivity
  have hsq : (3 : ℝ) + 2 * Real.sqrt 2 = (1 + Real.sqrt 2) ^ 2 := by
    rw [add_sq, Real.sq_sqrt (by norm_num : (2 : ℝ) ≥ 0)]
    ring
  rw [hsq, pow_two, Real.log_mul hp.ne' hp.ne']
  ring

/-- **The wall is a quantised ledger value.**  With `ℓ = log z` the peel ledger and
`Γ = tanh (ℓ/2)` the reflection, the wall `Γ² = 1/2` is exactly `|ℓ| = 2 log (1 + √2)`.
The two signs are the two reciprocal wall ratios `3 ± 2√2`. -/
theorem wall_ledger_value (ℓ : ℝ) (h : Real.tanh (ℓ / 2) ^ 2 = 1 / 2) :
    ℓ = 2 * Real.log (1 + Real.sqrt 2) ∨ ℓ = -(2 * Real.log (1 + Real.sqrt 2)) := by
  have hz : 0 < Real.exp ℓ := Real.exp_pos ℓ
  have hgam : gam (Real.exp ℓ) = Real.tanh (ℓ / 2) := by
    have := ElementalPeeling.LoopWall.Ledger.gam_eq_tanh_half_log (Real.exp ℓ) hz
    rwa [Real.log_exp] at this
  have hwall : gam (Real.exp ℓ) * gam (Real.exp ℓ) = 1 / 2 := by
    rw [hgam, ← pow_two]
    exact h
  have hroot := (ElementalPeeling.LoopWall.Wall.wall_eq_iff (Real.exp ℓ) hz).mp hwall
  have hpos : 0 < (3 : ℝ) + 2 * Real.sqrt 2 := by positivity
  have hrecip := ElementalPeeling.LoopWall.Wall.wall_ratios_reciprocal
  rcases hroot with hroot | hroot
  · left
    have hlog : ℓ = Real.log (3 + 2 * Real.sqrt 2) := by
      rw [← hroot, Real.log_exp]
    rw [hlog, log_wall_ratio]
  · right
    have hinv : (3 : ℝ) - 2 * Real.sqrt 2 = (3 + 2 * Real.sqrt 2)⁻¹ := by
      have hmul : (3 - 2 * Real.sqrt 2) * (3 + 2 * Real.sqrt 2) = 1 := by
        rw [mul_comm]; exact hrecip
      exact (inv_eq_of_mul_eq_one_left hmul).symm
    have hlog : ℓ = Real.log (3 - 2 * Real.sqrt 2) := by
      rw [← hroot, Real.log_exp]
    rw [hlog, hinv, Real.log_inv, log_wall_ratio]

/-! ## 2. The ledger descent, in the peel coordinate -/

/-- **The join between the two ledger theorems.**  Dirac Time's `PathLedger.descent_iff` says a
path ledger is an endpoint potential exactly when every loop is silent.  Read through the peel
coordinate, the same hypothesis makes `Γ = tanh (ℓ/2)` a function of the endpoints alone.

The ledger is `ℓ`, an additive reversal-odd real weight on admitted paths; `ℓ = log z` for the
peel ratio of a step.  No positivity of `z` is needed for the descent itself. -/
theorem tanh_ledger_descent {X : Type*} {P : X → X → Type*}
    (comp : ∀ {x y z : X}, P x y → P y z → P x z)
    (rev : ∀ {x y : X}, P x y → P y x) (ℓ : ∀ {x y : X}, P x y → ℝ)
    (hcomp : ∀ {x y z : X} (p : P x y) (q : P y z), ℓ (comp p q) = ℓ p + ℓ q)
    (hrev : ∀ {x y : X} (p : P x y), ℓ (rev p) = -ℓ p)
    (hconn : ∀ x y : X, Nonempty (P x y)) :
    (∃ n : X → ℝ, ∀ {x y : X} (γ : P x y),
        Real.tanh (ℓ γ / 2) = Real.tanh ((n y - n x) / 2)) ↔
      ∀ {x : X} (c : P x x), ℓ c = 0 := by
  constructor
  · rintro ⟨n, hn⟩ x c
    have h0 : Real.tanh (ℓ c / 2) = Real.tanh ((n x - n x) / 2) := hn c
    rw [sub_self, zero_div, Real.tanh_zero] at h0
    have h1 : ℓ c / 2 = 0 := Real.tanh_injective (h0.trans (Real.tanh_zero).symm)
    linarith
  · intro hloop
    obtain ⟨n, hn⟩ :=
      DiracTime.PathLedger.descent_iff (X := X) (P := P) comp rev ℓ hcomp hrev hconn |>.mpr hloop
    exact ⟨n, fun γ => by rw [hn γ]⟩

/-! ## 3. The wall and the perfect-reflection limit in determinant coordinates -/

/-- `1 − Γ²` is four times the block determinant.  This is `normalizedDet` unfolded, recorded
here as the bridge relation so that the wall can be read in the `CompositionBridge` coordinates. -/
theorem one_sub_gam_sq_eq_four_det (p : Fin 2 → ℝ) (hnorm : p 0 + p 1 = 1) :
    1 - (ElementalPeeling.LoopWall.FisherMatrix.balance p) ^ 2 =
      4 * (ElementalPeeling.LoopWall.FisherMatrix.shareMatrix p).det := by
  have h :=
    ElementalPeeling.LoopWall.CompositionBridge.normalizedDet_eq_one_sub_balance_sq p hnorm
  unfold ElementalPeeling.LoopWall.CompositionBridge.normalizedDet at h
  linarith

/-- **The wall is the determinant `1/8`.**  In the two-channel block coordinates the wall
`Γ² = 1/2` is the determinant `p₀p₁ = 1/8`; the transmission `1 − Γ²` is `1/2` there. -/
theorem wall_iff_share_det (p : Fin 2 → ℝ) (hnorm : p 0 + p 1 = 1) :
    (ElementalPeeling.LoopWall.FisherMatrix.balance p) ^ 2 = 1 / 2 ↔
      (ElementalPeeling.LoopWall.FisherMatrix.shareMatrix p).det = 1 / 8 := by
  have key := one_sub_gam_sq_eq_four_det p hnorm
  constructor <;> intro h <;> linarith

/-- **Perfect reflection is a pure block.**  `|Γ| = 1`, the limit in which nothing is
transmitted, is exactly `det p = 0`; the maximally mixed block `Γ = 0` is `det p = 1/4`. -/
theorem gam_sq_eq_one_iff_det_zero (p : Fin 2 → ℝ) (hnorm : p 0 + p 1 = 1) :
    (ElementalPeeling.LoopWall.FisherMatrix.balance p) ^ 2 = 1 ↔
      (ElementalPeeling.LoopWall.FisherMatrix.shareMatrix p).det = 0 := by
  have key := one_sub_gam_sq_eq_four_det p hnorm
  constructor <;> intro h <;> linarith

/-! ## 4. The common definition, proved twice and joined here -/

/-- **One identity, two proofs.**  `LoopWall/Ledger.lean:34` and `VOTKP/Smith.lean:42` prove the
same Smith identity independently, in two repositories.  Stated together, the two developments are
joined at their shared definition rather than by analogy. -/
theorem two_smith_identities (z : ℝ) (hz : 0 < z) :
    gam z = (z - 1) / (z + 1) ∧ (z - 1) / (z + 1) = Real.tanh (Real.log z / 2) := by
  refine ⟨rfl, ?_⟩
  exact VOTKP.Smith.smith_identity z hz

/-- **The double angle is the diagonal of the velocity law.**  `LoopWall/Clock.lean:25` proves
`tanh (2x) = 2 tanh x / (1 + tanh x²)`; `VOTKP/Smith.lean:72` proves `tanh (a+b) = tanh a ⊕ tanh b`.
The first is the second at `a = b`. -/
theorem tanh_double_eq_oplus (x : ℝ) :
    Real.tanh (2 * x) = VOTKP.Smith.oplus (Real.tanh x) (Real.tanh x) := by
  rw [two_mul]
  exact VOTKP.Smith.tanh_add' x x

end Unified.Bridge.Reflection
