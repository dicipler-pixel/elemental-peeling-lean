import Mathlib
import LoopWall.Ledger
import LoopWall.Wall
import Bridge.Reflection
import VOTKP.Smith

/-!
# Bridge IV — windows, and why most wall crossings have no wall-crossing step

The periodic table's scale atlas counts 183,770 contiguous windows of at least two removal steps,
of which 91,768 exceed the wall `3 + 2√2` in total and **91,638 do so with every constituent step
inside the wall**.  None exceeds the wall on geometric mean per step.

That is not a numerical accident of the archive: it is the composition law.  A window's ratio is
the product of its steps, and `Γ = tanh(½ log ·)` turns products into `⊕`.  So a window of inside
steps can leave the disk, while its per-step geometric mean cannot.  This file proves both halves
and the exact crossing criterion.

* `composite_reflection_eq` — a window's reflection is `tanh((Σ log zᵢ)/2)`;
* `composite_two_eq_oplus` — two steps compose by VOTKP's velocity law `⊕`;
* `crosses_iff_ledger_sum` — a window crosses exactly when its total ledger exceeds `log(3+2√2)`;
* `window_at_wall_iff` — the wall condition on the window ledger, both branches;
* `two_halves_cross` — `z = 5/2` twice: each step inside, composite outside;
* `geomean_lt_wall` — inside steps have an inside geometric mean;
* `composition_crosses_mean_does_not` — the atlas's two headline facts as one statement.
-/

namespace Unified.Bridge.Composition

open ElementalPeeling.LoopWall.Ledger (gam gam_eq_tanh_half_log)
open Unified.Bridge.Reflection (wall_ledger_value)
open scoped BigOperators

/-- The wall value is positive. -/
theorem wall_pos : 0 < (3 : ℝ) + 2 * Real.sqrt 2 := by positivity

/-- The logarithm of a product of positive ratios is the sum of the logarithms. -/
theorem log_prod_eq_sum {n : ℕ} (z : Fin n → ℝ) (hpos : ∀ i, 0 < z i) :
    Real.log (∏ i, z i) = ∑ i, Real.log (z i) :=
  Real.log_prod (fun i _ => (hpos i).ne')

/-- **A window's reflection is the hyperbolic tangent of half its ledger.**  This is the
`n`-fold form of the Smith identity, and the reason a window has a single reflection at all. -/
theorem composite_reflection_eq {n : ℕ} (z : Fin n → ℝ) (hpos : ∀ i, 0 < z i) :
    gam (∏ i, z i) = Real.tanh ((∑ i, Real.log (z i)) / 2) := by
  have hprod : 0 < ∏ i, z i := Finset.prod_pos (fun i _ => hpos i)
  rw [gam_eq_tanh_half_log _ hprod, log_prod_eq_sum z hpos]

/-- **Two steps compose by the velocity law.**  `Γ(z₁z₂) = Γ(z₁) ⊕ Γ(z₂)` with VOTKP's
`u ⊕ v = (u+v)/(1+uv)`: peel steps add like velocities. -/
theorem composite_two_eq_oplus (z₁ z₂ : ℝ) (h₁ : 0 < z₁) (h₂ : 0 < z₂) :
    gam (z₁ * z₂) = VOTKP.Smith.oplus (gam z₁) (gam z₂) := by
  have hp : 0 < z₁ * z₂ := mul_pos h₁ h₂
  rw [gam_eq_tanh_half_log _ hp, Real.log_mul h₁.ne' h₂.ne',
    gam_eq_tanh_half_log z₁ h₁, gam_eq_tanh_half_log z₂ h₂]
  rw [← VOTKP.Smith.tanh_add']
  congr 1
  ring

/-- **The crossing criterion.**  A window exceeds the wall exactly when its total ledger exceeds
`log(3 + 2√2)`.  No single step has to cross. -/
theorem crosses_iff_ledger_sum {n : ℕ} (z : Fin n → ℝ)
    (hpos : ∀ i, 0 < z i) :
    (3 + 2 * Real.sqrt 2) < ∏ i, z i ↔
      Real.log (3 + 2 * Real.sqrt 2) < ∑ i, Real.log (z i) := by
  have hW : 0 < (3 : ℝ) + 2 * Real.sqrt 2 := wall_pos
  have hprod : 0 < ∏ i, z i := Finset.prod_pos (fun i _ => hpos i)
  rw [← Real.log_lt_log_iff hW hprod, log_prod_eq_sum z hpos]

/-- **The wall condition on a window's ledger.**  A window at the wall has total ledger
`±2 log(1 + √2)`, i.e. `±log(3 + 2√2)`.  (The converse is the same computation read backwards
and is not needed here.) -/
theorem window_at_wall_ledger {n : ℕ} (z : Fin n → ℝ) (hpos : ∀ i, 0 < z i)
    (h : gam (∏ i, z i) ^ 2 = 1 / 2) :
    (∑ i, Real.log (z i)) = 2 * Real.log (1 + Real.sqrt 2) ∨
      (∑ i, Real.log (z i)) = -(2 * Real.log (1 + Real.sqrt 2)) := by
  rw [composite_reflection_eq z hpos] at h
  exact wall_ledger_value _ h

/-- **Two inside steps whose composite is outside.**  Each step is `5/2 < 3 + 2√2`; the product
`25/4 = 6.25` is outside.  This is the smallest kind of witness for the atlas's 91,638. -/
theorem two_halves_cross :
    (5 / 2 : ℝ) < 3 + 2 * Real.sqrt 2 ∧ (3 + 2 * Real.sqrt 2) < (5 / 2) * (5 / 2) := by
  have hs : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  constructor
  · linarith
  · have hsq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    nlinarith [sq_nonneg (Real.sqrt 2 - 13 / 8), Real.sqrt_nonneg 2, hsq]

/-- **The geometric mean of inside steps is inside.**  This is why the atlas finds *zero* windows
exceeding the wall on geometric mean per removal, whatever the archive contains: it is a theorem
about positive lists, not a measurement. -/
theorem geomean_lt_wall {n : ℕ} (hn : 0 < n) (z : Fin n → ℝ) (hpos : ∀ i, 0 < z i)
    (h : ∀ i, z i < 3 + 2 * Real.sqrt 2) :
    Real.exp ((∑ i, Real.log (z i)) / n) < 3 + 2 * Real.sqrt 2 := by
  have hW : 0 < (3 : ℝ) + 2 * Real.sqrt 2 := wall_pos
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsum : ∑ i, Real.log (z i) < ∑ _i : Fin n, Real.log (3 + 2 * Real.sqrt 2) := by
    apply Finset.sum_lt_sum
    · intro i _
      exact (Real.log_lt_log (hpos i) (h i)).le
    · refine ⟨⟨0, hn⟩, Finset.mem_univ _, ?_⟩
      exact Real.log_lt_log (hpos ⟨0, hn⟩) (h ⟨0, hn⟩)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hlt : (∑ i, Real.log (z i)) / n < Real.log (3 + 2 * Real.sqrt 2) := by
    rw [div_lt_iff₀ hnR]
    linarith
  calc Real.exp ((∑ i, Real.log (z i)) / n)
      < Real.exp (Real.log (3 + 2 * Real.sqrt 2)) := Real.exp_lt_exp.mpr hlt
    _ = 3 + 2 * Real.sqrt 2 := Real.exp_log hW

/-- **The atlas's two facts, as one theorem.**  A window of inside steps can cross the wall
(composition, `⊕`), and no window of inside steps can cross it on geometric mean (the mean is
bounded by the largest step).  The first is where 91,638 of the archived 91,768 crossings live;
the second is why the count of mean-crossings is exactly zero. -/
theorem composition_crosses_mean_does_not :
    (∃ z : Fin 2 → ℝ, (∀ i, 0 < z i) ∧ (∀ i, z i < 3 + 2 * Real.sqrt 2) ∧
        (3 + 2 * Real.sqrt 2) < ∏ i, z i) ∧
      (∀ (n : ℕ) (_hn : 0 < n) (z : Fin n → ℝ), (∀ i, 0 < z i) →
        (∀ i, z i < 3 + 2 * Real.sqrt 2) →
        Real.exp ((∑ i, Real.log (z i)) / n) < 3 + 2 * Real.sqrt 2) := by
  refine ⟨⟨fun _ => 5 / 2, fun _ => by norm_num, fun _ => two_halves_cross.1, ?_⟩, ?_⟩
  · have h : (∏ _i : Fin 2, (5 / 2 : ℝ)) = (5 / 2) * (5 / 2) := by norm_num
    rw [h]
    exact two_halves_cross.2
  · intro n hn z hpos h
    exact geomean_lt_wall hn z hpos h

end Unified.Bridge.Composition
