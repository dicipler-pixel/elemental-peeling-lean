/-
VOTKP v1.1, knot side: Proposition 11.1's key step (Appendix A.12).

On the unit circle, `(1 − ω)/(1 − ω̄) = −ω` for `ω ≠ 1`.
-/
import Mathlib

namespace VOTKP.Knot

open Complex

/-- **Appendix A.12.** For `|ω| = 1`, `ω ≠ 1`: `(1 − ω)/(1 − ω̄) = −ω`. -/
theorem unit_circle_ratio (ω : ℂ) (hn : normSq ω = 1) (h1 : ω ≠ 1) :
    (1 - ω) / (1 - (starRingEnd ℂ) ω) = -ω := by
  have hc : ω * (starRingEnd ℂ) ω = 1 := by rw [mul_conj, hn]; simp
  have hne : 1 - (starRingEnd ℂ) ω ≠ 0 := by
    intro h
    apply h1
    have : (starRingEnd ℂ) ω = 1 := by linear_combination -h
    have := congrArg (starRingEnd ℂ) this
    simpa using this
  rw [div_eq_iff hne]
  linear_combination (-1 : ℂ) * hc

end VOTKP.Knot
