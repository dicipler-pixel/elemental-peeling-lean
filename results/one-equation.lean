/-
  one-equation.lean

  The one equation, in the form a scientist can use it, and its three readings.

  The per-handoff law is measured (`results/air-law-offset.md`): the total gap between consecutive twin
  starts is `t²/(2C₂)` with `t = log p` and `1/(2C₂) = 0.757390`. The cumulative statement is *exact*
  given that law, by telescoping — which is what this file proves. The chain's span is the sum of the
  squared logs over the handoffs, scaled once:

      span = (1/(2C₂)) · Σ log²p        (cumulative)
      span = c · m · ΔT                 (the same, with c = 1/(2C₂), m handoffs, ΔT = mean log²p)
      d²E/dt² = a = 1/C₂ = 1.51478      (per handoff, in the (log p, span) plane)

  Proved below: the cumulative identity from the per-handoff law (`span_from_logs`), its c·m·ΔT form
  (`span_eq_c_m_dT`), the inversion that gives the count from the span (`count_from_span`), the
  acceleration form (`acceleration_form`), the discrete constant-acceleration identities
  (`const_accel_second_difference`, `velocity_is_linear`), and the one-reading recovery that the fission
  pin uses (`partner_from_pin`).

  What is *not* here: the per-handoff law itself. It is a measurement, not a theorem; the file takes it
  as the hypothesis `h` of `span_from_logs`, which is the honest place for it.

  No `sorry`, no `axiom`, no `native_decide`.
-/
import Mathlib

namespace Law

/-- **The cumulative law.** If every handoff satisfies the measured law
`p(i+1) − p i − 2 = t i²/(2C₂) − 2` (i.e. air `= t²/(2C₂) − 2`), then the whole chain's span is the sum
of the squared logs over `2C₂`, with nothing left over. Proved by telescoping
(`Finset.sum_range_sub`); no approximation beyond the per-handoff law. -/
theorem span_from_logs (p t : ℕ → ℚ) (C2 : ℚ) (n : ℕ)
    (h : ∀ i < n, p (i + 1) - p i - 2 = t i ^ 2 / (2 * C2) - 2) :
    p n - p 0 = (Finset.range n).sum (fun i => t i ^ 2 / (2 * C2)) := by
  have hsum : (Finset.range n).sum (fun i => (p (i + 1) - p i))
      = (Finset.range n).sum (fun i => t i ^ 2 / (2 * C2)) := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    have := h i (Finset.mem_range.mp hi)
    linarith
  rw [← hsum]
  exact (Finset.sum_range_sub p n).symm

/-- **The same equation with a mean: `span = c · m · ΔT`.** With `c = 1/(2C₂)`, `m` handoffs and
`ΔT = ⟨log²p⟩` the mean over them, the cumulative law is exactly this product. -/
theorem span_eq_c_m_dT (n : ℕ) (S m span C2 : ℚ)
    (hS : S = (n : ℚ) * m) (hspan : span = S / (2 * C2)) :
    span = (1 / (2 * C2)) * (n : ℚ) * m := by
  rw [hspan, hS]
  ring

/-- **The inversion: the count from the span.** Solving the cumulative law for the sum of the squared
logs is the same statement read the other way, which is how a scientist holding a span (not a list of
primes) recovers how many handoffs it contains. -/
theorem count_from_span (p t : ℕ → ℚ) (C2 span : ℚ) (n : ℕ) (hC : C2 ≠ 0)
    (hspan : span = p n - p 0)
    (h : ∀ i < n, p (i + 1) - p i - 2 = t i ^ 2 / (2 * C2) - 2) :
    (Finset.range n).sum (fun i => t i ^ 2) = 2 * C2 * span := by
  have hcum := span_from_logs p t C2 n h
  rw [← hspan] at hcum
  calc (Finset.range n).sum (fun i => t i ^ 2)
      = (Finset.range n).sum (fun i => t i ^ 2 / (2 * C2)) * (2 * C2) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl ?_
        intro i _
        field_simp
    _ = span * (2 * C2) := by rw [← hcum]
    _ = 2 * C2 * span := by ring

/-- **The acceleration form, per handoff.** One handoff's gap is `½ a t²` with `a = 1/C₂ = 1.51478`:
the "constant acceleration in the (log p, span) plane" reading is this identity, one handoff at a time,
not a limit. -/
theorem acceleration_form (C2 t : ℚ) : t ^ 2 / (2 * C2) = (1 / 2) * (1 / C2) * t ^ 2 := by
  ring

/-- **Constant acceleration, discretely.** For `E(t) = ½ a t²` the second difference is `a h²` at every
step — the exact content of `d²E/dt² = a` without any calculus, and the form in which it can be checked
against a table of spans. -/
theorem const_accel_second_difference (a t h : ℚ) :
    (1 / 2) * a * (t + h) ^ 2 - 2 * ((1 / 2) * a * t ^ 2) + (1 / 2) * a * (t - h) ^ 2 = a * h ^ 2 := by
  ring

/-- **The velocity is linear in `log p`.** The first difference of `½ a t²` over a step `h` is
`a t + a h/2`: the "speed" of the chain in the (log p, span) plane grows linearly with `t`, and the
growth rate is the same `a`. -/
theorem velocity_is_linear (a t h : ℚ) (hh : h ≠ 0) :
    ((1 / 2) * a * (t + h) ^ 2 - (1 / 2) * a * t ^ 2) / h = a * t + a * h / 2 := by
  field_simp
  ring

/-- **One reading recovers the partner.** With the heavy piece pinned at the closure 54, the light piece
is `Z − 54` and nothing else — the fission version of the old layer's rule that `n` readings determine
`n` parameters: here one known constant and one measured count determine the second count. -/
theorem partner_from_pin (Z Z1 : ℚ) : (Z1 = Z - 54 ↔ Z = Z1 + 54) := by
  constructor <;> intro h <;> linarith

/-! ## 7. The ratio a segment carries, and which standard ratios it can hold

A segment's ratio is `r = air/T = air/(air+4)`. Since air ≥ 4 it is always at least one half, and since
air grows without bound it approaches 1 — so **a segment is always majority air**. On the five classes the
ratio takes five values, and among the textbook stoichiometric ratios only `1:2` is on that ladder: `1:1`
needs air = ∞, `2:1` and `3:1` would need air < 0, and `1:3`, `2:3`, `3:4` need air = 2, 8, 12 — none of
which is `4 (mod 6)`. -/

/-- **A segment is at least half air**: `air ≥ 4` gives `air/(air+4) ≥ 1/2`. -/
theorem air_at_least_half (air : ℚ) (h : 4 ≤ air) : 1 / 2 ≤ air / (air + 4) := by
  have h4 : (0 : ℚ) < air + 4 := by linarith
  field_simp
  linarith

/-- The ratio is strictly below 1, so the band is `[1/2, 1)`. -/
theorem air_ratio_lt_one (air : ℚ) (h : 0 < air) : air / (air + 4) < 1 := by
  have h4 : (0 : ℚ) < air + 4 := by linarith
  field_simp
  linarith

/-- **The five rungs of the ratio ladder**, one per class. -/
theorem ratio_ladder :
    (4 : ℚ) / 8 = 1 / 2 ∧ (10 : ℚ) / 14 = 5 / 7 ∧ (16 : ℚ) / 20 = 4 / 5 ∧
      (22 : ℚ) / 26 = 11 / 13 ∧ (28 : ℚ) / 32 = 7 / 8 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> norm_num

/-- **`1:3` is not on the ladder**: it needs `air = 2`, which is not `4 (mod 6)`. -/
theorem no_one_third (air : ℕ) (h6 : air % 6 = 4) : 3 * air ≠ air + 4 := by omega

/-- **`2:3` is not on the ladder** (it needs `air = 8 ≡ 2`). -/
theorem no_two_thirds (air : ℕ) (h6 : air % 6 = 4) : 3 * air ≠ 2 * (air + 4) := by omega

/-- **`3:4` is not on the ladder** (it needs `air = 12 ≡ 0`). -/
theorem no_three_quarters (air : ℕ) (h6 : air % 6 = 4) : 4 * air ≠ 3 * (air + 4) := by omega

/-- **`1:2` is on the ladder**, and only at `air = 4` — the minimal merge, the quadruplet. -/
theorem one_half_at_four (air : ℕ) (h : 2 * air = air + 4) : air = 4 := by omega

end Law
