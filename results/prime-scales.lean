/-
  prime-scales.lean

  The three scaled formulas on the prime side — energy, acceleration, mass — and exactly what each one
  is. Nothing here invents a joule: the rules are

    (i)   the *dimensionless* statements are exact given the measured law gap = t²/(2C₂), t = log p;
    (ii)  a physical unit is a *conversion*, and the conversion constant is stated with it (κ for kelvin,
          3R for joule per mole, the mole for gram);
    (iii) mass on the prime side is a *count* (pairs) or a *span* (integers), never a gram.

  Proved below:
    * Ê = gap/t² = 1/(2C₂)            — the scaled energy per handoff (`scaled_energy`)
    * a = 1/C₂ = 2·(1/(2C₂))          — the acceleration is twice that coefficient (`acceleration_is_twice`)
    * m̂ = T/t² = 1/(2C₂) + 2/t²       — the scaled mass, the pair's 2 showing as the correction (`scaled_mass`)
    * E·ρ = 1                          — energy per handoff times density is one, identically (`energy_times_density`)
    * E(λt) = λ²E(t)                   — the law is homogeneous of degree 2 in log p, so energy scales as
                                         t², acceleration is scale-free, density as t⁻²  (`homogeneous_energy`)
    * 3R·κ = 1/(2C₂)                   — the joule-per-mole reading *is* the dimensionless one, because κ
                                         was defined as (1/(2C₂))/3R  (`conversion_identity`)

  No `sorry`, no `axiom`, no `native_decide`.
-/
import Mathlib

namespace Scales

/-- **The scaled energy.** Given the measured per-handoff law `gap = t²/(2C₂)`, the energy per unit
`log²p` is the constant `1/(2C₂)` — no approximation beyond the law itself. -/
theorem scaled_energy (gap t C2 : ℚ) (ht : t ≠ 0) (hC : C2 ≠ 0) (h : gap = t ^ 2 / (2 * C2)) :
    gap / t ^ 2 = 1 / (2 * C2) := by
  rw [h]
  field_simp

/-- **The acceleration is twice the energy coefficient**, because `E = ½at²`: with `a = 1/C₂` the
per-handoff energy is `½ a t² = t²/(2C₂)`. -/
theorem acceleration_is_twice (a C2 : ℚ) (hC : C2 ≠ 0) (h : a = 1 / C2) :
    a = 2 * (1 / (2 * C2)) := by
  rw [h]
  field_simp

/-- One handoff's energy in the acceleration form: `½·(1/C₂)·t² = t²/(2C₂)`. -/
theorem energy_from_acceleration (t C2 : ℚ) (hC : C2 ≠ 0) :
    (1 / 2) * (1 / C2) * t ^ 2 = t ^ 2 / (2 * C2) := by
  field_simp

/-- **The scaled mass.** The total gap `T = gap + 2` (the pair is two units of integer line) divided by
`t²` is the energy coefficient plus the pair's correction `2/t²`. As `t` grows the correction vanishes and
mass and energy coincide in scaled units — which is why the per-handoff normalisation is flat and the
per-segment one is not. -/
theorem scaled_mass (T t C2 : ℚ) (ht : t ≠ 0) (hC : C2 ≠ 0) (h : T = t ^ 2 / (2 * C2) + 2) :
    T / t ^ 2 = 1 / (2 * C2) + 2 / t ^ 2 := by
  rw [h]
  field_simp

/-- **Energy times density is one.** With `E` the mean gap (energy per handoff) and `ρ = m/span` the
number of pairs per unit line, `E·ρ = (span/m)(m/span) = 1` identically. It is a bookkeeping identity, not
a discovery, and it is stated as such so nobody reads physics into it. -/
theorem energy_times_density (E rho : ℚ) (hE : E ≠ 0) (h : rho = 1 / E) : E * rho = 1 := by
  rw [h]
  field_simp

/-- **Homogeneity: the law is of degree 2 in `log p`.** Scaling the log by `λ` scales the energy by `λ²`,
which is the precise content of "energy ∝ t²". -/
theorem homogeneous_energy (E t lam C2 : ℚ) (hC : C2 ≠ 0) (h : E = t ^ 2 / (2 * C2)) :
    lam ^ 2 * E = (lam * t) ^ 2 / (2 * C2) := by
  rw [h]
  ring

/-- **Acceleration is scale-free** and **density is of degree −2**: together they are the statement that
only one power of the scale appears, in the energy. -/
theorem scaled_degrees (t lam C2 rho : ℚ) (ht : t ≠ 0) (hlam : lam ≠ 0)
    (h : rho = 2 * C2 / t ^ 2) :
    rho = 2 * C2 / t ^ 2 ∧ lam ^ 2 * rho = 2 * C2 / (t / lam) ^ 2 := by
  refine ⟨h, ?_⟩
  rw [h]
  field_simp

/-- **The conversion identity.** `κ = (1/(2C₂))/(3R)`, so `3R·κ = 1/(2C₂)`: the joule-per-mole and kelvin
readings of the same formula carry the *same* coefficient, and the only thing κ does is move the number
from `log²p` to kelvin. No energy is created by the conversion. -/
theorem conversion_identity (R kappa C2 : ℚ) (hR : R ≠ 0) (hC : C2 ≠ 0)
    (h : kappa = (1 / (2 * C2)) / (3 * R)) : 3 * R * kappa = 1 / (2 * C2) := by
  rw [h]
  field_simp

/-- The kelvin reading: `T = κ·t²` with `κ = 0.030364` K per unit `log²p`. -/
theorem kelvin_reading (T kappa t : ℚ) (ht : t ≠ 0) (h : T = kappa * t ^ 2) :
    T / t ^ 2 = kappa := by
  rw [h]
  field_simp

/-- The bracket on the measured coefficient, as the record quotes it: `0.75739 ± 0.000018`. -/
theorem coefficient_bracket :
    (0.757372 : ℚ) < 1 / (2 * (6601618158468696 / 10000000000000000)) ∧
      1 / (2 * (6601618158468696 / 10000000000000000)) < (0.757408 : ℚ) := by
  constructor <;> norm_num

end Scales
