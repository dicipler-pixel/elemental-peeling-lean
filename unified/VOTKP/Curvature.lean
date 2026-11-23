/-
VOTKP §4, Theorem 4.1: occupation sets a response curvature (Jeromie Beasley).

`H_M(a) = δI + δσ_x + c a σ_z = [[δ + ca, δ], [δ, δ − ca]]` has eigenvalues `δ ∓ E(a)` with
`E(a) = √(δ² + c²a²)`. A population-preserving occupation `r` of the lower level gives the
electronic energy `δ + (1 − 2r)E(a)`; with the bare energy `μ_b a²/2 + λa⁴/4` the total is `U(a)`.
Its curvature at `a = 0` is `μ_eff(r) = μ_b + c²(1 − 2r)/δ = μ_base − χr`, `χ = 2c²/δ = 8δ g_aa(0)`,
and it vanishes at `r_c = (1 + μ_b δ/c²)/2`.

"Curvature" is stated with an explicit remainder: `|U(a) − U(0) − μ_eff a²/2| ≤ C a⁴`, with `C`
written out, so the quadratic coefficient is pinned exactly.
Developed with AI assistance.
-/
import Mathlib

namespace VOTKP.Curvature

open Real

/-- The two-level model `H_M(a)`. -/
def HM (δ c a : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![δ + c * a, δ; δ, δ - c * a]

/-- The half-splitting `E(a) = √(δ² + c²a²)`. -/
noncomputable def Ehalf (δ c a : ℝ) : ℝ := √(δ ^ 2 + c ^ 2 * a ^ 2)

/-- Total energy: bare part plus the occupation-weighted electronic part. -/
noncomputable def U (μb lam δ c r a : ℝ) : ℝ :=
  μb * a ^ 2 / 2 + lam * a ^ 4 / 4 + (δ + (1 - 2 * r) * Ehalf δ c a)

/-- The effective curvature `μ_eff(r) = μ_b + c²(1 − 2r)/δ`. -/
noncomputable def μeff (μb δ c r : ℝ) : ℝ := μb + c ^ 2 * (1 - 2 * r) / δ

lemma det_shift (δ c a l : ℝ) :
    (HM δ c a - l • (1 : Matrix (Fin 2) (Fin 2) ℝ)).det
      = (δ + c * a - l) * (δ - c * a - l) - δ * δ := by
  rw [Matrix.det_fin_two]
  simp [HM] <;> ring

/-- **Theorem 4.1, the spectrum.** `δ − E(a)` and `δ + E(a)` are the eigenvalues of `H_M(a)`. -/
theorem eigenvalues_HM (δ c a : ℝ) :
    (HM δ c a - (δ - Ehalf δ c a) • (1 : Matrix (Fin 2) (Fin 2) ℝ)).det = 0 ∧
      (HM δ c a - (δ + Ehalf δ c a) • (1 : Matrix (Fin 2) (Fin 2) ℝ)).det = 0 := by
  have hs : Ehalf δ c a ^ 2 = δ ^ 2 + c ^ 2 * a ^ 2 := Real.sq_sqrt (by positivity)
  constructor
  · rw [det_shift]; linear_combination hs
  · rw [det_shift]; linear_combination hs

/-- Two-sided Taylor bound for the square root:
`0 ≤ δ + q/(2δ) − √(δ² + q) ≤ q²/(8δ³)` for `δ > 0`, `q ≥ 0`. -/
lemma sqrt_two_sided (δ q : ℝ) (hδ : 0 < δ) (hq : 0 ≤ q) :
    0 ≤ δ + q / (2 * δ) - √(δ ^ 2 + q) ∧
      δ + q / (2 * δ) - √(δ ^ 2 + q) ≤ q ^ 2 / (8 * δ ^ 3) := by
  have hδ0 : δ ≠ 0 := hδ.ne'
  have hs0 : 0 ≤ √(δ ^ 2 + q) := Real.sqrt_nonneg _
  have hs2 : √(δ ^ 2 + q) ^ 2 = δ ^ 2 + q := Real.sq_sqrt (by positivity)
  have hsδ : δ ≤ √(δ ^ 2 + q) := by nlinarith
  have hqd : 0 ≤ q / (2 * δ) := by positivity
  have hm2 : (δ + q / (2 * δ)) ^ 2 = δ ^ 2 + q + (q / (2 * δ)) ^ 2 := by
    field_simp
    try ring
  have key : (δ + q / (2 * δ) - √(δ ^ 2 + q)) * (δ + q / (2 * δ) + √(δ ^ 2 + q))
      = (q / (2 * δ)) ^ 2 := by
    linear_combination hm2 - hs2
  have hms : 0 < δ + q / (2 * δ) + √(δ ^ 2 + q) := by linarith
  have hdiff : 0 ≤ δ + q / (2 * δ) - √(δ ^ 2 + q) := by
    nlinarith [sq_nonneg (q / (2 * δ))]
  refine ⟨hdiff, ?_⟩
  have h2 : (δ + q / (2 * δ) - √(δ ^ 2 + q)) * (2 * δ) ≤ (q / (2 * δ)) ^ 2 := by
    rw [← key]
    exact mul_le_mul_of_nonneg_left (by linarith) hdiff
  have h3 : q ^ 2 / (8 * δ ^ 3) = (q / (2 * δ)) ^ 2 / (2 * δ) := by
    field_simp
    try ring
  rw [h3, le_div_iff₀ (by positivity)]
  exact h2

/-- **Theorem 4.1, the curvature.** `U(a) = U(0) + μ_eff a²/2 + O(a⁴)`, with the remainder
bounded explicitly by `(|λ|/4 + |1 − 2r| c⁴/(8δ³)) a⁴`. -/
theorem curvature (μb lam δ c r a : ℝ) (hδ : 0 < δ) :
    |U μb lam δ c r a - U μb lam δ c r 0 - μeff μb δ c r * a ^ 2 / 2|
      ≤ (|lam| / 4 + |1 - 2 * r| * c ^ 4 / (8 * δ ^ 3)) * a ^ 4 := by
  have hδ0 : δ ≠ 0 := hδ.ne'
  obtain ⟨h0, h1⟩ := sqrt_two_sided δ (c ^ 2 * a ^ 2) hδ (by positivity)
  have hU0 : U μb lam δ c r 0 = δ + (1 - 2 * r) * δ := by
    simp [U, Ehalf, Real.sqrt_sq hδ.le]
  have hexpr : U μb lam δ c r a - U μb lam δ c r 0 - μeff μb δ c r * a ^ 2 / 2
      = lam * a ^ 4 / 4
        - (1 - 2 * r) * (δ + c ^ 2 * a ^ 2 / (2 * δ) - √(δ ^ 2 + c ^ 2 * a ^ 2)) := by
    rw [hU0]
    simp only [U, μeff, Ehalf]
    field_simp
    try ring
  rw [hexpr]
  have hA : |lam * a ^ 4 / 4| = |lam| / 4 * a ^ 4 := by
    rw [abs_div, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ a ^ 4),
      abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    ring
  have hB : |(1 - 2 * r) * (δ + c ^ 2 * a ^ 2 / (2 * δ) - √(δ ^ 2 + c ^ 2 * a ^ 2))|
      ≤ |1 - 2 * r| * (c ^ 4 / (8 * δ ^ 3) * a ^ 4) := by
    rw [abs_mul, abs_of_nonneg h0]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    calc δ + c ^ 2 * a ^ 2 / (2 * δ) - √(δ ^ 2 + c ^ 2 * a ^ 2)
        ≤ (c ^ 2 * a ^ 2) ^ 2 / (8 * δ ^ 3) := h1
      _ = c ^ 4 / (8 * δ ^ 3) * a ^ 4 := by ring
  calc _ ≤ |lam * a ^ 4 / 4|
        + |(1 - 2 * r) * (δ + c ^ 2 * a ^ 2 / (2 * δ) - √(δ ^ 2 + c ^ 2 * a ^ 2))| :=
        abs_sub _ _
    _ ≤ |lam| / 4 * a ^ 4 + |1 - 2 * r| * (c ^ 4 / (8 * δ ^ 3) * a ^ 4) := by
        rw [hA]; linarith
    _ = (|lam| / 4 + |1 - 2 * r| * c ^ 4 / (8 * δ ^ 3)) * a ^ 4 := by ring

/-- **Theorem 4.1, the metric.** The ground Bloch direction `n(a) = (δ, 0, ca)/E(a)` has
`∂ₐn(0) = (0, 0, c/δ)`: the `z`-component has slope `c/δ` and the `x`-component slope `0`. -/
theorem bloch_slope (δ c : ℝ) (hδ : 0 < δ) :
    HasDerivAt (fun a => c * a / Ehalf δ c a) (c / δ) 0 ∧
      HasDerivAt (fun a => δ / Ehalf δ c a) 0 0 := by
  have hf : HasDerivAt (fun a : ℝ => δ ^ 2 + c ^ 2 * a ^ 2) 0 0 := by
    have := ((hasDerivAt_pow 2 (0 : ℝ)).const_mul (c ^ 2)).const_add (δ ^ 2)
    simpa using this
  have hf0 : δ ^ 2 + c ^ 2 * (0 : ℝ) ^ 2 ≠ 0 := by
    rw [show (0 : ℝ) ^ 2 = 0 by norm_num, mul_zero, add_zero]
    exact (pow_pos hδ 2).ne'
  have hE : HasDerivAt (fun a => Ehalf δ c a) 0 0 := by
    have := hf.sqrt hf0
    simpa [Ehalf] using this
  have hE0 : Ehalf δ c 0 = δ := by simp [Ehalf, Real.sqrt_sq hδ.le]
  have hEne : Ehalf δ c 0 ≠ 0 := by rw [hE0]; exact hδ.ne'
  constructor
  · have h := ((hasDerivAt_id' (x := (0 : ℝ))).const_mul c).fun_div hE hEne
    refine h.congr_deriv ?_
    simp only [hE0, mul_one, mul_zero, sub_zero]
    rw [div_eq_div_iff (pow_ne_zero 2 hδ.ne') hδ.ne']
    ring
  · have h := (hasDerivAt_const (x := (0 : ℝ)) (c := δ)).fun_div hE hEne
    refine h.congr_deriv ?_
    simp

/-- **Theorem 4.1, the constants.** `g_aa(0) = |∂ₐn(0)|²/4 = c²/(4δ²)`, `χ = 2c²/δ = 8δ g_aa(0)`,
`μ_eff = μ_base − χ r` with `μ_base = μ_b + c²/δ`. -/
theorem metric_and_susceptibility (μb δ c r : ℝ) (hδ : 0 < δ) :
    ((0 : ℝ) ^ 2 + 0 ^ 2 + (c / δ) ^ 2) / 4 = c ^ 2 / (4 * δ ^ 2) ∧
      2 * c ^ 2 / δ = 8 * δ * (c ^ 2 / (4 * δ ^ 2)) ∧
      μeff μb δ c r = (μb + c ^ 2 / δ) - 2 * c ^ 2 / δ * r := by
  have hδ0 : δ ≠ 0 := hδ.ne'
  refine ⟨?_, ?_, ?_⟩
  · field_simp
    try ring
  · field_simp
    try ring
  · unfold μeff
    field_simp
    try ring

/-- **Theorem 4.1, the critical occupation.** `μ_eff(r_c) = 0` at `r_c = (1 + μ_b δ/c²)/2`. -/
theorem critical_occupation (μb δ c : ℝ) (hδ : 0 < δ) (hc : c ≠ 0) :
    μeff μb δ c ((1 + μb * δ / c ^ 2) / 2) = 0 := by
  have hδ0 : δ ≠ 0 := hδ.ne'
  unfold μeff
  field_simp
  try ring

end VOTKP.Curvature
