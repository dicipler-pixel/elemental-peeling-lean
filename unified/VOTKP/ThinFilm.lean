/-
VOTKP §6.4, Theorem 6.3: the thin end is a shunt admittance (Jeromie Beasley).

A film of index `N` and thickness `d` between an ambient `n₀` and a substrate `n_b`, time
dependence `e^{−iωt}`, has the characteristic-matrix outputs (Born & Wolf)
  `B = cos δ − i (n_b/N) sin δ`,  `C = n_b cos δ − i N sin δ`,  `δ = kNd`,
and the exact reflection at its top face `r_top = (n₀B − C)/(n₀B + C)`. The theorem: to first
order in `d` this is the reflection of the bare substrate loaded by the shunt admittance
`y = −ikd(N² − n_b²)` (top face), equivalently `y = −ikd(N² − n₀²)` once `r` is referred to the
substrate face by the factor `e^{−2ikn₀d}`. "First order" is stated exactly: the exact and shunt
reflections agree at `d = 0` and have the same derivative in the real thickness `d` there, and
their difference is `O(d²)` as `d → 0` (`thin_end_top_remainder`, `thin_end_substrate_remainder`).
The remainder bound uses that both reflections are complex-analytic in `d` near `0`.
Developed with AI assistance.
-/
import Mathlib

namespace VOTKP.ThinFilm

open Complex

/-- `B = cos δ − i (n_b/N) sin δ`, `δ = kNd`. -/
noncomputable def Bm (nb N k d : ℂ) : ℂ := cos (k * N * d) - I * (nb / N) * sin (k * N * d)

/-- `C = n_b cos δ − i N sin δ`, `δ = kNd`. -/
noncomputable def Cm (nb N k d : ℂ) : ℂ := nb * cos (k * N * d) - I * N * sin (k * N * d)

/-- The exact reflection referred to the film's top face. -/
noncomputable def rTop (n0 nb N k d : ℂ) : ℂ :=
  (n0 * Bm nb N k d - Cm nb N k d) / (n0 * Bm nb N k d + Cm nb N k d)

/-- The shunt law at the top face: `Y = n_b − ikd(N² − n_b²)`, `r = (n₀ − Y)/(n₀ + Y)`. -/
noncomputable def rShuntTop (n0 nb N k d : ℂ) : ℂ :=
  (n0 - (nb - I * k * d * (N ^ 2 - nb ^ 2))) / (n0 + (nb - I * k * d * (N ^ 2 - nb ^ 2)))

/-- The exact reflection referred to the substrate face. -/
noncomputable def rSub (n0 nb N k d : ℂ) : ℂ := exp (-(2 * I * k * n0 * d)) * rTop n0 nb N k d

/-- The shunt law at the substrate face: `Y = n_b − ikd(N² − n₀²)`. -/
noncomputable def rShuntSub (n0 nb N k d : ℂ) : ℂ :=
  (n0 - (nb - I * k * d * (N ^ 2 - n0 ^ 2))) / (n0 + (nb - I * k * d * (N ^ 2 - n0 ^ 2)))

lemma rTop_zero (n0 nb N k : ℂ) : rTop n0 nb N k 0 = (n0 - nb) / (n0 + nb) := by
  simp [rTop, Bm, Cm]

lemma hasDerivAt_rTop (n0 nb N k : ℂ) (hN : N ≠ 0) (hsum : n0 + nb ≠ 0) :
    HasDerivAt (rTop n0 nb N k) (2 * I * k * n0 * (N ^ 2 - nb ^ 2) / (n0 + nb) ^ 2) 0 := by
  have hδ : HasDerivAt (fun d : ℂ => k * N * d) (k * N) 0 := by
    simpa using (hasDerivAt_id' (x := (0 : ℂ))).const_mul (k * N)
  have hc := hδ.ccos
  have hs := hδ.csin
  have hB : HasDerivAt (fun d => Bm nb N k d) (-(I * nb * k)) 0 := by
    refine (hc.fun_sub (hs.const_mul (I * (nb / N)))).congr_deriv ?_
    simp only [mul_zero, Complex.sin_zero, Complex.cos_zero]
    field_simp
    try ring
  have hC : HasDerivAt (fun d => Cm nb N k d) (-(I * k * N ^ 2)) 0 := by
    refine ((hc.const_mul nb).fun_sub (hs.const_mul (I * N))).congr_deriv ?_
    simp only [mul_zero, Complex.sin_zero, Complex.cos_zero]
    ring
  have hB0 : Bm nb N k 0 = 1 := by simp [Bm]
  have hC0 : Cm nb N k 0 = nb := by simp [Cm]
  have hden : n0 * Bm nb N k 0 + Cm nb N k 0 ≠ 0 := by rw [hB0, hC0, mul_one]; exact hsum
  refine (((hB.const_mul n0).fun_sub hC).fun_div ((hB.const_mul n0).fun_add hC) hden).congr_deriv ?_
  rw [hB0, hC0]
  field_simp
  try ring

lemma hasDerivAt_rShuntTop (n0 nb N k : ℂ) (hsum : n0 + nb ≠ 0) :
    HasDerivAt (rShuntTop n0 nb N k) (2 * I * k * n0 * (N ^ 2 - nb ^ 2) / (n0 + nb) ^ 2) 0 := by
  have hY : HasDerivAt (fun d : ℂ => I * k * d * (N ^ 2 - nb ^ 2)) (I * k * (N ^ 2 - nb ^ 2)) 0 := by
    simpa using ((hasDerivAt_id' (x := (0 : ℂ))).const_mul (I * k)).mul_const (N ^ 2 - nb ^ 2)
  have hY' := hY.const_sub nb
  have hden : n0 + (nb - I * k * 0 * (N ^ 2 - nb ^ 2)) ≠ 0 := by simpa using hsum
  refine ((hY'.const_sub n0).fun_div (hY'.const_add n0) hden).congr_deriv ?_
  simp only [mul_zero, zero_mul, sub_zero]
  field_simp
  try ring

lemma hasDerivAt_rSub (n0 nb N k : ℂ) (hN : N ≠ 0) (hsum : n0 + nb ≠ 0) :
    HasDerivAt (rSub n0 nb N k) (2 * I * k * n0 * (N ^ 2 - n0 ^ 2) / (n0 + nb) ^ 2) 0 := by
  have hE : HasDerivAt (fun d : ℂ => exp (-(2 * I * k * n0 * d)))
      (exp (-(2 * I * k * n0 * 0)) * -(2 * I * k * n0 * 1)) 0 :=
    ((hasDerivAt_id' (x := (0 : ℂ))).const_mul (2 * I * k * n0)).fun_neg.cexp
  refine (hE.fun_mul (hasDerivAt_rTop n0 nb N k hN hsum)).congr_deriv ?_
  rw [rTop_zero]
  simp only [mul_zero, neg_zero, Complex.exp_zero, one_mul, mul_one]
  field_simp
  try ring

lemma hasDerivAt_rShuntSub (n0 nb N k : ℂ) (hsum : n0 + nb ≠ 0) :
    HasDerivAt (rShuntSub n0 nb N k) (2 * I * k * n0 * (N ^ 2 - n0 ^ 2) / (n0 + nb) ^ 2) 0 := by
  have hY : HasDerivAt (fun d : ℂ => I * k * d * (N ^ 2 - n0 ^ 2)) (I * k * (N ^ 2 - n0 ^ 2)) 0 := by
    simpa using ((hasDerivAt_id' (x := (0 : ℂ))).const_mul (I * k)).mul_const (N ^ 2 - n0 ^ 2)
  have hY' := hY.const_sub nb
  have hden : n0 + (nb - I * k * 0 * (N ^ 2 - n0 ^ 2)) ≠ 0 := by simpa using hsum
  refine ((hY'.const_sub n0).fun_div (hY'.const_add n0) hden).congr_deriv ?_
  simp only [mul_zero, zero_mul, sub_zero]
  field_simp
  try ring

/-- **Theorem 6.3, top face.** In the real thickness `d`, the exact film reflection and the shunt
law `Y = n_b − ikd(N² − n_b²)` agree at `d = 0` and share the derivative
`2ikn₀(N² − n_b²)/(n₀ + n_b)²` there: they agree to first order in `d`. -/
theorem thin_end_top (n0 nb N k : ℂ) (hN : N ≠ 0) (hsum : n0 + nb ≠ 0) :
    rTop n0 nb N k 0 = rShuntTop n0 nb N k 0 ∧
      HasDerivAt (fun d : ℝ => rTop n0 nb N k d)
        (2 * I * k * n0 * (N ^ 2 - nb ^ 2) / (n0 + nb) ^ 2) 0 ∧
      HasDerivAt (fun d : ℝ => rShuntTop n0 nb N k d)
        (2 * I * k * n0 * (N ^ 2 - nb ^ 2) / (n0 + nb) ^ 2) 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [rTop_zero]
    simp [rShuntTop]
  · refine HasDerivAt.comp_ofReal (z := 0) ?_
    rw [Complex.ofReal_zero]
    exact hasDerivAt_rTop n0 nb N k hN hsum
  · refine HasDerivAt.comp_ofReal (z := 0) ?_
    rw [Complex.ofReal_zero]
    exact hasDerivAt_rShuntTop n0 nb N k hsum

/-- **Theorem 6.3, substrate face.** Referred to the substrate face (factor `e^{−2ikn₀d}`), the
same first-order law reads `Y = n_b − ikd(N² − n₀²)`, the thin-sheet formula
`y = Z₀σ_s` with `σ_s = −iωε₀(N² − n₀²)d`. -/
theorem thin_end_substrate (n0 nb N k : ℂ) (hN : N ≠ 0) (hsum : n0 + nb ≠ 0) :
    rSub n0 nb N k 0 = rShuntSub n0 nb N k 0 ∧
      HasDerivAt (fun d : ℝ => rSub n0 nb N k d)
        (2 * I * k * n0 * (N ^ 2 - n0 ^ 2) / (n0 + nb) ^ 2) 0 ∧
      HasDerivAt (fun d : ℝ => rShuntSub n0 nb N k d)
        (2 * I * k * n0 * (N ^ 2 - n0 ^ 2) / (n0 + nb) ^ 2) 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [rSub, rTop_zero]
    simp [rShuntSub]
  · refine HasDerivAt.comp_ofReal (z := 0) ?_
    rw [Complex.ofReal_zero]
    exact hasDerivAt_rSub n0 nb N k hN hsum
  · refine HasDerivAt.comp_ofReal (z := 0) ?_
    rw [Complex.ofReal_zero]
    exact hasDerivAt_rShuntSub n0 nb N k hsum

/-! ## The size of the remainder -/

/-- An analytic function vanishing to first order at `0` is `O(z²)` there: its derivative is
`O(z)` (it is analytic with `g'(0) = 0`), and the mean value theorem on a small closed disk turns
that into `‖g z‖ ≤ C‖z‖²`. -/
lemma isBigO_sq_of_deriv_zero {g : ℂ → ℂ} (hg : AnalyticAt ℂ g 0) (h0 : g 0 = 0)
    (h1 : deriv g 0 = 0) : g =O[nhds 0] fun z => z ^ 2 := by
  have hO : (fun z => deriv g z - deriv g 0) =O[nhds 0] fun z => z - 0 :=
    hg.deriv.differentiableAt.isBigO_sub
  simp only [h1, sub_zero] at hO
  obtain ⟨C, hCpos, hC⟩ := hO.exists_pos
  have hev := hC.bound.and hg.eventually_analyticAt
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.1 hev
  refine Asymptotics.IsBigO.of_bound C ?_
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hr] with z hz
  have hzr : ‖z‖ < r := by simpa using hz
  have hsub : Metric.closedBall (0 : ℂ) ‖z‖ ⊆ Metric.ball 0 r := Metric.closedBall_subset_ball hzr
  have hdiff : ∀ w ∈ Metric.closedBall (0 : ℂ) ‖z‖, DifferentiableAt ℂ g w :=
    fun w hw => (hball w (hsub hw)).2.differentiableAt
  have hbound : ∀ w ∈ Metric.closedBall (0 : ℂ) ‖z‖, ‖deriv g w‖ ≤ C * ‖z‖ := by
    intro w hw
    have h1' := (hball w (hsub hw)).1
    have hw' : ‖w‖ ≤ ‖z‖ := by simpa using hw
    calc ‖deriv g w‖ ≤ C * ‖w‖ := h1'
      _ ≤ C * ‖z‖ := by gcongr
  have hmv := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbound (convex_closedBall 0 ‖z‖)
    (Metric.mem_closedBall_self (norm_nonneg z)) (show z ∈ Metric.closedBall (0 : ℂ) ‖z‖ by simp)
  rw [h0, sub_zero, sub_zero] at hmv
  calc ‖g z‖ ≤ C * ‖z‖ * ‖z‖ := hmv
    _ = C * ‖z ^ 2‖ := by rw [norm_pow]; ring

/-- Pull an `O(z²)` statement on `ℂ` back to the real thickness. -/
lemma isBigO_sq_ofReal {g : ℂ → ℂ} (h : g =O[nhds 0] fun z => z ^ 2) :
    (fun d : ℝ => g d) =O[nhds 0] fun d : ℝ => d ^ 2 := by
  have ht : Filter.Tendsto (fun d : ℝ => (d : ℂ)) (nhds 0) (nhds 0) := by
    simpa using (Complex.continuous_ofReal.tendsto (0 : ℝ))
  refine (h.comp_tendsto ht).trans ?_
  refine Asymptotics.IsBigO.of_bound 1 (Filter.Eventually.of_forall fun d => ?_)
  simp [norm_pow]

lemma analyticAt_rTop (n0 nb N k : ℂ) (hsum : n0 + nb ≠ 0) :
    AnalyticAt ℂ (rTop n0 nb N k) 0 := by
  have hnum : AnalyticAt ℂ (fun d => n0 * Bm nb N k d - Cm nb N k d) 0 := by
    unfold Bm Cm
    fun_prop
  have hden : AnalyticAt ℂ (fun d => n0 * Bm nb N k d + Cm nb N k d) 0 := by
    unfold Bm Cm
    fun_prop
  have h0 : n0 * Bm nb N k 0 + Cm nb N k 0 ≠ 0 := by simpa [Bm, Cm] using hsum
  exact hnum.fun_div hden h0

lemma analyticAt_rShuntTop (n0 nb N k : ℂ) (hsum : n0 + nb ≠ 0) :
    AnalyticAt ℂ (rShuntTop n0 nb N k) 0 := by
  have hnum : AnalyticAt ℂ (fun d : ℂ => n0 - (nb - I * k * d * (N ^ 2 - nb ^ 2))) 0 := by
    fun_prop
  have hden : AnalyticAt ℂ (fun d : ℂ => n0 + (nb - I * k * d * (N ^ 2 - nb ^ 2))) 0 := by
    fun_prop
  have h0 : n0 + (nb - I * k * 0 * (N ^ 2 - nb ^ 2)) ≠ 0 := by simpa using hsum
  exact hnum.fun_div hden h0

lemma analyticAt_rSub (n0 nb N k : ℂ) (hsum : n0 + nb ≠ 0) :
    AnalyticAt ℂ (rSub n0 nb N k) 0 := by
  have hE : AnalyticAt ℂ (fun d : ℂ => exp (-(2 * I * k * n0 * d))) 0 := by fun_prop
  exact hE.fun_mul (analyticAt_rTop n0 nb N k hsum)

lemma analyticAt_rShuntSub (n0 nb N k : ℂ) (hsum : n0 + nb ≠ 0) :
    AnalyticAt ℂ (rShuntSub n0 nb N k) 0 := by
  have hnum : AnalyticAt ℂ (fun d : ℂ => n0 - (nb - I * k * d * (N ^ 2 - n0 ^ 2))) 0 := by
    fun_prop
  have hden : AnalyticAt ℂ (fun d : ℂ => n0 + (nb - I * k * d * (N ^ 2 - n0 ^ 2))) 0 := by
    fun_prop
  have h0 : n0 + (nb - I * k * 0 * (N ^ 2 - n0 ^ 2)) ≠ 0 := by simpa using hsum
  exact hnum.fun_div hden h0

/-- **Theorem 6.3, top face, with its remainder.** The exact film reflection and the shunt law
differ by `O(d²)` as the real thickness `d → 0`. -/
theorem thin_end_top_remainder (n0 nb N k : ℂ) (hN : N ≠ 0) (hsum : n0 + nb ≠ 0) :
    (fun d : ℝ => rTop n0 nb N k d - rShuntTop n0 nb N k d) =O[nhds 0] fun d : ℝ => d ^ 2 := by
  apply isBigO_sq_ofReal (g := fun z => rTop n0 nb N k z - rShuntTop n0 nb N k z)
  apply isBigO_sq_of_deriv_zero
  · exact (analyticAt_rTop n0 nb N k hsum).fun_sub (analyticAt_rShuntTop n0 nb N k hsum)
  · show rTop n0 nb N k 0 - rShuntTop n0 nb N k 0 = 0
    rw [rTop_zero]
    simp [rShuntTop]
  · rw [((hasDerivAt_rTop n0 nb N k hN hsum).fun_sub
      (hasDerivAt_rShuntTop n0 nb N k hsum)).deriv, sub_self]

/-- **Theorem 6.3, substrate face, with its remainder.** Referred to the substrate face, the
exact reflection and the shunt law `Y = n_b − ikd(N² − n₀²)` differ by `O(d²)`. -/
theorem thin_end_substrate_remainder (n0 nb N k : ℂ) (hN : N ≠ 0) (hsum : n0 + nb ≠ 0) :
    (fun d : ℝ => rSub n0 nb N k d - rShuntSub n0 nb N k d) =O[nhds 0] fun d : ℝ => d ^ 2 := by
  apply isBigO_sq_ofReal (g := fun z => rSub n0 nb N k z - rShuntSub n0 nb N k z)
  apply isBigO_sq_of_deriv_zero
  · exact (analyticAt_rSub n0 nb N k hsum).fun_sub (analyticAt_rShuntSub n0 nb N k hsum)
  · show rSub n0 nb N k 0 - rShuntSub n0 nb N k 0 = 0
    rw [rSub, rTop_zero]
    simp [rShuntSub]
  · rw [((hasDerivAt_rSub n0 nb N k hN hsum).fun_sub
      (hasDerivAt_rShuntSub n0 nb N k hsum)).deriv, sub_self]

end VOTKP.ThinFilm
