import Mathlib

/-!
# The scalar ledger: log of the mean ratio is log cosh of half the spacing

Direction D2 of the third round.  For positive readings `I J`, with `t = log (I/J)` and
`Γ = (I-J)/(I+J)`, the module proves `Γ = tanh (t/2)`, `log ((I+J)/(2√(IJ))) = log cosh (t/2)`,
`log cosh (t/2) = -(1/2) log (1 - Γ^2)`, `S ≥ 0` with `S = 0 ↔ I = J`, that swapping the readings
sends `Γ ↦ -Γ` and fixes `S`, that `S = (1/2) log 2` at `Γ^2 = 1/2`, and that `S` is strictly
increasing in `|Γ|` on `[0,1)`.  The peel keeps which way, the scalar keeps how much.

Written in the third parallel formalization round (swarm `smws58h9u`, direction m6),
then recompiled and reviewed here; namespace and header added, `lemma` renamed to `theorem`, and
the trailing `#print axioms` lines removed because `scripts/verify.py` audits every named theorem.
-/

namespace ElementalPeeling.LoopWall.ScalarLedger

/-- Signed logarithmic spacing of a peel step. -/
noncomputable def t (I J : ℝ) : ℝ := Real.log (I / J)

/-- Signed peel reflection. -/
noncomputable def G (I J : ℝ) : ℝ := (I - J) / (I + J)

/-- The scalar ledger: logarithm of the arithmetic/geometric mean ratio. -/
noncomputable def S (I J : ℝ) : ℝ :=
  Real.log ((I + J) / (2 * Real.sqrt (I * J)))

/-- The scalar ledger expressed solely in terms of the reflection magnitude. -/
noncomputable def S_abs (r : ℝ) : ℝ := -(1 / 2 : ℝ) * Real.log (1 - r ^ 2)

/-- The ratio form of the reflection is `tanh` of half its logarithm. -/
theorem ratio_reflection_eq_tanh {z : ℝ} (hz : 0 < z) :
    (z - 1) / (z + 1) = Real.tanh (Real.log z / 2) := by
  have hs : 0 < Real.sqrt z := Real.sqrt_pos.2 hz
  have hs0 : Real.sqrt z ≠ 0 := ne_of_gt hs
  have hsq : Real.sqrt z ^ 2 = z := Real.sq_sqrt hz.le
  rw [Real.tanh_eq, Real.exp_neg, Real.exp_half, Real.exp_log hz]
  field_simp [hs0]
  nlinarith

/-- (a) The peel reflection is the hyperbolic tangent of half the log spacing. -/
theorem G_eq_tanh_half_t {I J : ℝ} (hI : 0 < I) (hJ : 0 < J) :
    G I J = Real.tanh (t I J / 2) := by
  have hz : 0 < I / J := div_pos hI hJ
  unfold G t
  rw [← ratio_reflection_eq_tanh hz]
  field_simp [ne_of_gt hI, ne_of_gt hJ]

/-- The arithmetic/geometric mean ratio is `cosh` of half the log spacing. -/
theorem mean_ratio_eq_cosh_half_t {I J : ℝ} (hI : 0 < I) (hJ : 0 < J) :
    (I + J) / (2 * Real.sqrt (I * J)) = Real.cosh (t I J / 2) := by
  have hz : 0 < I / J := div_pos hI hJ
  have hsI : 0 < Real.sqrt I := Real.sqrt_pos.2 hI
  have hsJ : 0 < Real.sqrt J := Real.sqrt_pos.2 hJ
  have hsqI : Real.sqrt I ^ 2 = I := Real.sq_sqrt hI.le
  have hsqJ : Real.sqrt J ^ 2 = J := Real.sq_sqrt hJ.le
  unfold t
  rw [Real.cosh_eq, Real.exp_neg, Real.exp_half, Real.exp_log hz,
    Real.sqrt_div hI.le, Real.sqrt_mul hI.le]
  field_simp [ne_of_gt hsI, ne_of_gt hsJ]
  nlinarith

/-- (b) The scalar ledger is `log cosh` of half the log spacing. -/
theorem S_eq_log_cosh_half_t {I J : ℝ} (hI : 0 < I) (hJ : 0 < J) :
    S I J = Real.log (Real.cosh (t I J / 2)) := by
  unfold S
  rw [mean_ratio_eq_cosh_half_t hI hJ]

/-- The exact `log cosh`/`tanh` identity, valid for every real argument. -/
theorem log_cosh_eq_neg_half_log_one_sub_tanh_sq (x : ℝ) :
    Real.log (Real.cosh x) =
      -(1 / 2 : ℝ) * Real.log (1 - Real.tanh x ^ 2) := by
  have hc : Real.cosh x ≠ 0 := ne_of_gt (Real.cosh_pos x)
  have hden : 1 - Real.tanh x ^ 2 = (Real.cosh x ^ 2)⁻¹ := by
    rw [Real.tanh_eq_sinh_div_cosh, div_pow]
    field_simp [hc]
    nlinarith [Real.cosh_sq_sub_sinh_sq x]
  rw [hden, Real.log_inv, Real.log_pow]
  norm_num
  ring

/-- (c) The scalar ledger depends only on the square of the reflection. -/
theorem log_cosh_half_t_eq_neg_half_log_one_sub_G_sq {I J : ℝ}
    (hI : 0 < I) (hJ : 0 < J) :
    Real.log (Real.cosh (t I J / 2)) =
      -(1 / 2 : ℝ) * Real.log (1 - G I J ^ 2) := by
  rw [G_eq_tanh_half_t hI hJ]
  exact log_cosh_eq_neg_half_log_one_sub_tanh_sq (t I J / 2)

/-- (c), written directly for the scalar ledger. -/
theorem S_eq_neg_half_log_one_sub_G_sq {I J : ℝ} (hI : 0 < I) (hJ : 0 < J) :
    S I J = -(1 / 2 : ℝ) * Real.log (1 - G I J ^ 2) := by
  rw [S_eq_log_cosh_half_t hI hJ]
  exact log_cosh_half_t_eq_neg_half_log_one_sub_G_sq hI hJ

/-- (d), nonnegativity: the arithmetic/geometric mean ratio is at least one. -/
theorem S_nonneg {I J : ℝ} (hI : 0 < I) (hJ : 0 < J) : 0 ≤ S I J := by
  rw [S_eq_log_cosh_half_t hI hJ]
  exact Real.log_nonneg (Real.one_le_cosh _)

/-- (d), equality case: the scalar ledger vanishes exactly when the readings agree. -/
theorem S_eq_zero_iff {I J : ℝ} (hI : 0 < I) (hJ : 0 < J) :
    S I J = 0 ↔ I = J := by
  constructor
  · intro h
    rw [S_eq_log_cosh_half_t hI hJ] at h
    have hc : Real.cosh (t I J / 2) = 1 :=
      Real.eq_one_of_pos_of_log_eq_zero (Real.cosh_pos _) h
    have ht0 : t I J / 2 = 0 := by
      by_contra ht
      have hc1 : 1 < Real.cosh (t I J / 2) := Real.one_lt_cosh.2 ht
      linarith
    have hlog : Real.log (I / J) = 0 := by
      unfold t at ht0
      linarith
    have hratio : I / J = 1 :=
      Real.eq_one_of_pos_of_log_eq_zero (div_pos hI hJ) hlog
    exact (div_eq_one_iff_eq (ne_of_gt hJ)).1 hratio
  · intro h
    subst J
    rw [S_eq_log_cosh_half_t hI hI]
    simp [t]

/-- (e) Reversing the peel step negates its signed reflection. -/
theorem G_swap (I J : ℝ) : G J I = -G I J := by
  unfold G
  rw [add_comm J I]
  ring

/-- (e) Reversing the peel step leaves its scalar ledger unchanged. -/
theorem S_swap (I J : ℝ) : S J I = S I J := by
  unfold S
  rw [add_comm J I, mul_comm J I]

/-- The scalar ledger is exactly `S_abs` evaluated at the reflection magnitude. -/
theorem S_eq_S_abs {I J : ℝ} (hI : 0 < I) (hJ : 0 < J) :
    S I J = S_abs |G I J| := by
  rw [S_eq_neg_half_log_one_sub_G_sq hI hJ]
  simp [S_abs, sq_abs]

/-- (f) At the wall `G² = 1/2`, the scalar ledger is exactly `log 2 / 2`. -/
theorem S_at_half_wall {I J : ℝ} (hI : 0 < I) (hJ : 0 < J)
    (hG : G I J ^ 2 = 1 / 2) : S I J = (1 / 2 : ℝ) * Real.log 2 := by
  rw [S_eq_neg_half_log_one_sub_G_sq hI hJ, hG]
  have hlog : Real.log (1 - (1 / 2 : ℝ)) = -Real.log 2 := by
    rw [show 1 - (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [hlog]
  ring

/-- Every reflection arising from positive readings has magnitude strictly below one. -/
theorem abs_G_lt_one {I J : ℝ} (hI : 0 < I) (hJ : 0 < J) : |G I J| < 1 := by
  rw [G_eq_tanh_half_t hI hJ]
  exact Real.abs_tanh_lt_one _

/-- (g), intrinsic form: on reflection magnitudes in `[0,1)`, the ledger is
strictly increasing. -/
theorem strictMonoOn_S_abs : StrictMonoOn S_abs (Set.Ico 0 1) := by
  intro x hx y hy hxy
  have hy0 : 0 ≤ y := hx.1.trans hxy.le
  have hsq : x ^ 2 < y ^ 2 := (sq_lt_sq₀ hx.1 hy0).2 hxy
  have hy_sq : y ^ 2 < 1 := by
    have h := (sq_lt_sq₀ hy0 (by norm_num : (0 : ℝ) ≤ 1)).2 hy.2
    simpa using h
  have hypos : 0 < 1 - y ^ 2 := sub_pos.mpr hy_sq
  have harg : 1 - y ^ 2 < 1 - x ^ 2 := by linarith
  have hlog := Real.log_lt_log hypos harg
  unfold S_abs
  linarith

/-- (g), peel form: a strictly larger reflection magnitude gives a strictly
larger scalar ledger, for any two positive peel steps. -/
theorem S_strict_of_abs_G_lt {I₁ J₁ I₂ J₂ : ℝ}
    (hI₁ : 0 < I₁) (hJ₁ : 0 < J₁) (hI₂ : 0 < I₂) (hJ₂ : 0 < J₂)
    (h : |G I₁ J₁| < |G I₂ J₂|) : S I₁ J₁ < S I₂ J₂ := by
  have hG₂ : |G I₂ J₂| < 1 := abs_G_lt_one hI₂ hJ₂
  have hG₁ : |G I₁ J₁| < 1 := h.trans hG₂
  rw [S_eq_S_abs hI₁ hJ₁, S_eq_S_abs hI₂ hJ₂]
  exact strictMonoOn_S_abs ⟨abs_nonneg _, hG₁⟩ ⟨abs_nonneg _, hG₂⟩ h

end ElementalPeeling.LoopWall.ScalarLedger
