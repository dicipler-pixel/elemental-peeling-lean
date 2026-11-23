/-
VOTKP v1.1: the thinning peel of a metal film.

The film reflection is `r = (Γ + x)/(1 + Γx)` with front-surface reflection `Γ` and echo
`x = r₁₂ e^{4πiNd/λ}`.

* Corollary 15.3: `r` is `Γ ⊕ x`, and its derivative at `x = 0` is `1 − Γ²`, the first-order
  echo coefficient of Theorem 6.1.
* Theorem 6.1: for `|Γx| < 1`, `Σ_{m≥1} (−Γ)^{m−1} x^m = x/(1 + Γx)`, and
  `Γ + (1 − Γ²) x/(1 + Γx) = r`, so `r = Γ + (1 − Γ²) Σ (−Γ)^{m−1} x^m`.
* Theorem 6.2: `|r|² − |a|² = ((1 − |a|⁴)|x|² + 2 Re[ā(1 − a²)x]) / |1 + ax|²`; with
  `A = 1 − |a|⁴ > 0` and `C = ā(1 − a²)`, the film reflects more than its bulk exactly when
  `|x − x_c| > |x_c|` with `x_c = −C̄/A`: outside one circle through the origin.
* Consequence 2 of Theorem 6.2: one radius cannot decide. With `a = 1/2`, the echo `x = 1/5`
  gives `R = 49/121 > 1/4` and `x = −1/5` gives `R = 1/9 < 1/4`.
* Section 15.2: at zero phase a stack telescopes,
  `r₀₁ ⊕ r₁₂ = r₀₂` with `rᵢⱼ = (Nᵢ − Nⱼ)/(Nᵢ + Nⱼ) = tanh(½ ln(Nᵢ/Nⱼ))`, so the inner layer
  drops out.
-/
import VOTKP.Smith

namespace VOTKP.Film

open Complex VOTKP.Smith

/-! ## Corollary 15.3 and Theorem 6.1 -/

/-- The film reflection is `Γ ⊕ x`. -/
theorem film_is_oplus (g x : ℂ) : (g + x) / (1 + g * x) = oplus g x := rfl

/-- **Corollary 15.3.** The first-order echo coefficient is the derivative of `Γ ⊕ x` at
`x = 0`, namely `1 − Γ²`. -/
theorem echo_derivative (g : ℂ) :
    HasDerivAt (fun x : ℂ => (g + x) / (1 + g * x)) (1 - g * g) 0 := by
  have h1 : HasDerivAt (fun x : ℂ => g + x) 1 0 := (hasDerivAt_id (0 : ℂ)).const_add g
  have h2 : HasDerivAt (fun x : ℂ => 1 + g * x) (g * 1) 0 :=
    ((hasDerivAt_id (0 : ℂ)).const_mul g).const_add 1
  have h := h1.div h2 (by simp)
  exact h.congr_deriv (by simp; try ring)

/-- **Theorem 6.1, the series.** For `‖Γx‖ < 1`, `Σ_{m≥0} (−Γ)^m x^{m+1} = x/(1 + Γx)`. -/
theorem echo_series (g x : ℂ) (h : ‖g * x‖ < 1) :
    HasSum (fun m : ℕ => (-g) ^ m * x ^ (m + 1)) (x / (1 + g * x)) := by
  have hg : ‖-(g * x)‖ < 1 := by rwa [norm_neg]
  have hs := (hasSum_geometric_of_norm_lt_one hg).mul_left x
  convert hs using 1
  · funext m
    rw [show -(g * x) = (-g) * x by ring, mul_pow, pow_succ]
    ring
  · rw [sub_neg_eq_add, div_eq_mul_inv]

/-- **Theorem 6.1, the sum.** `Γ + (1 − Γ²) · x/(1 + Γx) = (Γ + x)/(1 + Γx)`. -/
theorem echo_resum (g x : ℂ) (h : 1 + g * x ≠ 0) :
    g + (1 - g * g) * (x / (1 + g * x)) = (g + x) / (1 + g * x) := by
  field_simp
  ring

/-! ## Theorem 6.2: the exact boundary is a circle -/

/-- **Theorem 6.2.** `|r|² − |a|² = ((1 − |a|⁴)|x|² + 2 Re[ā(1 − a²)x]) / |1 + ax|²`. -/
theorem echo_circle (a x : ℂ) (h : 1 + a * x ≠ 0) :
    normSq ((a + x) / (1 + a * x)) - normSq a =
      ((1 - normSq a ^ 2) * normSq x + 2 * ((starRingEnd ℂ) a * (1 - a * a) * x).re) /
        normSq (1 + a * x) := by
  have hn : normSq (1 + a * x) ≠ 0 := by
    intro h0; exact h (normSq_eq_zero.mp h0)
  rw [normSq_div, eq_div_iff hn, sub_mul, div_mul_cancel₀ _ hn]
  simp only [normSq_apply, add_re, add_im, mul_re, mul_im, one_re, one_im, sub_re, sub_im,
    conj_re, conj_im]
  ring

/-- The centre of the circle, `x_c = −C̄/A`, written out in coordinates. -/
noncomputable def centre (A : ℝ) (C : ℂ) : ℂ := ⟨-C.re / A, C.im / A⟩

theorem centre_eq (A : ℝ) (hA : A ≠ 0) (C : ℂ) :
    centre A C = -(starRingEnd ℂ) C / (A : ℂ) := by
  apply Complex.ext <;> simp [centre, div_ofReal_re, div_ofReal_im] <;> field_simp

/-- The circle identity: `A(|x − x_c|² − |x_c|²) = A|x|² + 2 Re(Cx)`. -/
theorem circle_identity (A : ℝ) (hA : A ≠ 0) (C x : ℂ) :
    A * (normSq (x - centre A C) - normSq (centre A C)) = A * normSq x + 2 * (C * x).re := by
  simp only [centre, normSq_apply, sub_re, sub_im, mul_re, mul_im]
  field_simp
  ring

/-- **Theorem 6.2, the criterion.** For `A > 0`, `A|x|² + 2 Re(Cx) > 0` exactly when `x` lies
outside the circle `|x − x_c| = |x_c|`, which passes through the origin. With `A = 1 − |a|⁴` and
`C = ā(1 − a²)`, `echo_circle` makes this the condition for the film to reflect more than its
bulk; that combined statement is not proved here. -/
theorem circle_criterion (A : ℝ) (hA : 0 < A) (C x : ℂ) :
    0 < A * normSq x + 2 * (C * x).re ↔ normSq (centre A C) < normSq (x - centre A C) := by
  rw [← circle_identity A hA.ne' C x]
  constructor
  · intro h
    by_contra hc
    push_neg at hc
    nlinarith
  · intro h
    exact mul_pos hA (by linarith)

/-- The circle passes through the origin: `|0 − x_c| = |x_c|`. -/
theorem circle_through_origin (A : ℝ) (C : ℂ) :
    normSq (0 - centre A C) = normSq (centre A C) := by
  rw [zero_sub, normSq_neg]

/-- **One radius cannot decide.** With `a = 1/2`, the echo `x = 1/5` raises the reflectance
to `49/121 > 1/4` and `x = −1/5` lowers it to `1/9 < 1/4`. -/
theorem one_radius_cannot_decide :
    ((1 / 2 + 1 / 5) / (1 + 1 / 2 * (1 / 5)) : ℝ) ^ 2 = 49 / 121 ∧ (1 / 2 : ℝ) ^ 2 < 49 / 121 ∧
      ((1 / 2 - 1 / 5) / (1 - 1 / 2 * (1 / 5)) : ℝ) ^ 2 = 1 / 9 ∧ (1 / 9 : ℝ) < (1 / 2) ^ 2 := by
  norm_num

/-! ## Section 15.2: the zero-phase stack telescopes -/

/-- The interface reflection is the Smith coordinate of the index ratio. -/
theorem interface_smith (Ni Nj : ℝ) (hi : 0 < Ni) (hj : 0 < Nj) :
    (Ni - Nj) / (Ni + Nj) = Real.tanh (Real.log (Ni / Nj) / 2) := by
  rw [← smith_identity _ (div_pos hi hj)]
  have : Nj ≠ 0 := hj.ne'
  have : Ni + Nj ≠ 0 := by linarith
  field_simp

/-- **Zero phase.** `r₀₁ ⊕ r₁₂ = r₀₂`: the inner layer drops out. -/
theorem stack_telescopes (N0 N1 N2 : ℝ) (h0 : 0 < N0) (h1 : 0 < N1) (h2 : 0 < N2) :
    oplus ((N0 - N1) / (N0 + N1)) ((N1 - N2) / (N1 + N2)) = (N0 - N2) / (N0 + N2) := by
  have a : N0 + N1 ≠ 0 := by linarith
  have b : N1 + N2 ≠ 0 := by linarith
  have c : (N0 + N1) * (N1 + N2) ≠ 0 := mul_ne_zero a b
  have d : (N0 + N1) * (N1 + N2) + (N0 - N1) * (N1 - N2) ≠ 0 := by
    rw [show (N0 + N1) * (N1 + N2) + (N0 - N1) * (N1 - N2) = 2 * N1 * (N0 + N2) by ring]
    positivity
  have e : N0 + N2 ≠ 0 := by linarith
  unfold oplus
  rw [div_add_div _ _ a b, div_mul_div_comm, one_add_div c, div_div_div_cancel_right₀ c,
    div_eq_div_iff d e]
  ring

end VOTKP.Film
