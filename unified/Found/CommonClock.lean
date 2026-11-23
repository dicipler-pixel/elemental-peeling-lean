import Mathlib

/-!
# CommonClock spectral gaps drive exactly the LoopWall peel flow

Self-contained so that it compiles with the system `LEAN_PATH`.  The definitions
`gam` and `gapPeel` are LoopWall's definitions with `μj - μk` substituted for
its log-ratio frequency.  No spectral assertion about a knot is made.
-/

namespace CommonClockPeel

open Matrix

noncomputable section

/-- The scalar reflection from `LoopWall/Ledger.lean:30-31`. -/
def gam (z : ℝ) : ℝ := (z - 1) / (z + 1)

/-- The log-ratio ledger carried by a spectral gap `δ = μj - μk`. -/
def gapLedger (δ c τ : ℝ) : ℝ := 2 * c + δ * τ

/-- The resulting reflection, with initial offset `c = artanh Γ(0)`. -/
def gapPeel (δ c τ : ℝ) : ℝ := Real.tanh (gapLedger δ c τ / 2)

/-- The positive ratio underlying the same ledger. -/
def gapRatio (δ c τ : ℝ) : ℝ := Real.exp (gapLedger δ c τ)

/-- The hyperbolic-tangent derivative; also proved at WallClock.lean:39-47. -/
theorem hasDerivAt_tanh (x : ℝ) :
    HasDerivAt Real.tanh (1 - Real.tanh x ^ 2) x := by
  have hc : Real.cosh x ≠ 0 := ne_of_gt (Real.cosh_pos x)
  have h := (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x) hc
  convert h using 1
  · ext y
    exact Real.tanh_eq_sinh_div_cosh y
  · rw [Real.tanh_eq_sinh_div_cosh]
    field_simp [hc]

/-- THEOREM: the gap ledger has the spectral gap as its constant rate. -/
theorem hasDerivAt_gapLedger (δ c τ : ℝ) :
    HasDerivAt (gapLedger δ c) δ τ := by
  have h := ((hasDerivAt_id τ).const_mul δ).const_add (2 * c)
  convert h using 1
  · ext u
    rfl
  · norm_num

/-- THEOREM: a common spectral gap gives exactly the peel Riccati equation. -/
theorem hasDerivAt_gapPeel (δ c τ : ℝ) :
    HasDerivAt (gapPeel δ c)
      ((δ / 2) * (1 - gapPeel δ c τ ^ 2)) τ := by
  have hinner : HasDerivAt (fun u => gapLedger δ c u / 2) (δ / 2) τ := by
    exact (hasDerivAt_gapLedger δ c τ).div_const 2
  have h := (hasDerivAt_tanh (gapLedger δ c τ / 2)).comp τ hinner
  change HasDerivAt (fun u : ℝ => Real.tanh (gapLedger δ c u / 2))
    ((δ / 2) * (1 - Real.tanh (gapLedger δ c τ / 2) ^ 2)) τ
  convert h using 1
  · ext u
    rfl
  · ring

/-- THEOREM: exponentiating the gap ledger recovers the ratio/reflection relation. -/
theorem gam_gapRatio (δ c τ : ℝ) :
    gam (gapRatio δ c τ) = gapPeel δ c τ := by
  have hexp : 0 < Real.exp (gapLedger δ c τ) := Real.exp_pos _
  have hs : 0 < Real.sqrt (Real.exp (gapLedger δ c τ)) := Real.sqrt_pos.2 hexp
  have hs0 : Real.sqrt (Real.exp (gapLedger δ c τ)) ≠ 0 := ne_of_gt hs
  have hsq : Real.sqrt (Real.exp (gapLedger δ c τ)) ^ 2 =
      Real.exp (gapLedger δ c τ) := Real.sq_sqrt hexp.le
  rw [gapPeel, Real.tanh_eq, Real.exp_neg, Real.exp_half]
  unfold gam gapRatio
  field_simp [hs0]
  nlinarith

/-- Reality conditions needed to use the complex CommonClock theorem (`ℂ` at
`DiracTime/CommonClock.lean:29-34`) in the real LoopWall flow. -/
theorem real_common_clock_gap {τdot Ej Ek μj μk : ℂ}
    (hτdot : τdot.im = 0) (hEj : Ej.im = 0) (hEk : Ek.im = 0)
    (hgap : μj - μk = τdot * (Ej - Ek)) :
    μj.re - μk.re = τdot.re * (Ej.re - Ek.re) := by
  have h := congrArg Complex.re hgap
  simpa [Complex.mul_re, hτdot, hEj, hEk] using h

/-- THEOREM: the CommonClock gap identity is precisely the frequency substitution. -/
theorem gapPeel_of_common_gap {τdot Ej Ek μj μk : ℝ}
    (hgap : μj - μk = τdot * (Ej - Ek)) (c τ : ℝ) :
    gapPeel (μj - μk) c τ = gapPeel (τdot * (Ej - Ek)) c τ := by
  rw [hgap]

/-- The normalized adjacent-level case identifies `τdot` with LoopWall's `ω`. -/
theorem gapPeel_of_unit_energy_gap {τdot Ej Ek μj μk : ℝ}
    (hgap : μj - μk = τdot * (Ej - Ek)) (hE : Ej - Ek = 1) (c τ : ℝ) :
    gapPeel (μj - μk) c τ = gapPeel τdot c τ := by
  rw [hgap, hE, mul_one]

/-- Every real peel frequency occurs as the gap of an explicit non-scalar two-level
real matrix clock.  This specializes the affine generator law proved over `ℂ`
at `DiracTime/CommonClock.lean:22-34`. -/
theorem two_level_common_gap (τdot a : ℝ) :
    ∃ (G H₀ : Matrix (Fin 2) (Fin 2) ℝ) (μj μk : ℝ) (v w : Fin 2 → ℝ),
      G = τdot • H₀ + a • (1 : Matrix (Fin 2) (Fin 2) ℝ) ∧
      H₀ *ᵥ v = (1 : ℝ) • v ∧ H₀ *ᵥ w = (0 : ℝ) • w ∧
      G *ᵥ v = μj • v ∧ G *ᵥ w = μk • w ∧ μj - μk = τdot := by
  let H₀ : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 0]
  let G : Matrix (Fin 2) (Fin 2) ℝ := τdot • H₀ + a • 1
  let v : Fin 2 → ℝ := ![1, 0]
  let w : Fin 2 → ℝ := ![0, 1]
  refine ⟨G, H₀, τdot + a, a, v, w, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · ext i
    fin_cases i <;> simp [H₀, v, Matrix.mulVec, dotProduct]
  · ext i
    fin_cases i <;> simp [H₀, w, Matrix.mulVec, dotProduct]
  · ext i
    fin_cases i <;> simp [G, H₀, v, Matrix.mulVec, dotProduct]
  · ext i
    fin_cases i <;> simp [G, H₀, w, Matrix.mulVec, dotProduct]
  · ring

/-- The positive wall coordinate, as in PeelPotential.lean. -/
def wall : ℝ := 1 / Real.sqrt 2

theorem wall_pos : 0 < wall := by
  rw [wall]
  positivity

theorem wall_sq : wall ^ 2 = (1 / 2 : ℝ) := by
  have hs : Real.sqrt (2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rw [wall, div_pow, one_pow, hs]

theorem wall_mem_Ioo : wall ∈ Set.Ioo (-1 : ℝ) 1 := by
  have hspos : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hsone : 1 < Real.sqrt (2 : ℝ) := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  constructor
  · linarith [wall_pos]
  · exact (div_lt_one hspos).2 hsone

/-- THEOREM: for positive gap and zero initial reflection, the positive wall is
reached at precisely `2 artanh(wall)/δ`. -/
theorem gapPeel_eq_wall_iff {δ : ℝ} (hδ : 0 < δ) (τ : ℝ) :
    gapPeel δ 0 τ = wall ↔ τ = 2 * Real.artanh wall / δ := by
  have hδ0 : δ ≠ 0 := ne_of_gt hδ
  simp only [gapPeel, gapLedger, mul_zero, zero_add]
  constructor
  · intro h
    have ha := congrArg Real.artanh h
    rw [Real.artanh_tanh] at ha
    field_simp [hδ0]
    linarith
  · intro h
    subst τ
    convert Real.tanh_artanh wall_mem_Ioo using 1
    field_simp [hδ0]

/-- The elementary log form of the wall, also proved at WallClock.lean:177-200. -/
theorem artanh_wall : Real.artanh wall = Real.log (1 + Real.sqrt 2) := by
  have hs : Real.sqrt (2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hspos : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hden : 1 - wall ≠ 0 := ne_of_gt (sub_pos.mpr wall_mem_Ioo.2)
  have hsone : 1 < Real.sqrt (2 : ℝ) := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hsne : Real.sqrt (2 : ℝ) - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hsone)
  have harg : (1 + wall) / (1 - wall) = (1 + Real.sqrt 2) ^ 2 := by
    rw [wall] at hden ⊢
    field_simp [hden, ne_of_gt hspos, hsne]
    nlinarith
  rw [Real.artanh_eq_half_log ⟨wall_mem_Ioo.1.le, wall_mem_Ioo.2.le⟩,
    harg, Real.log_pow]
  norm_num
  ring

theorem two_artanh_wall :
    2 * Real.artanh wall = Real.log (3 + 2 * Real.sqrt 2) := by
  rw [artanh_wall]
  have hs : Real.sqrt (2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have harg : (3 : ℝ) + 2 * Real.sqrt 2 = (1 + Real.sqrt 2) ^ 2 := by
    nlinarith
  rw [harg, Real.log_pow]
  norm_num

theorem tanh_nonneg_of_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ Real.tanh x := by
  rw [Real.tanh_eq_sinh_div_cosh]
  exact div_nonneg (Real.sinh_nonneg_iff.mpr hx) (Real.cosh_pos x).le

theorem gapPeel_nonneg {δ τ : ℝ} (hδ : 0 < δ) (hτ : 0 ≤ τ) :
    0 ≤ gapPeel δ 0 τ := by
  apply tanh_nonneg_of_nonneg
  simp only [gapLedger, mul_zero, zero_add]
  positivity

/-- Reversing the gap reverses the reflection, hence not its square. -/
theorem gapPeel_neg_rate_sq (δ τ : ℝ) :
    gapPeel (-δ) 0 τ ^ 2 = gapPeel δ 0 τ ^ 2 := by
  have h : gapPeel (-δ) 0 τ = -gapPeel δ 0 τ := by
    simp only [gapPeel, gapLedger, mul_zero, zero_add]
    rw [show -δ * τ / 2 = -(δ * τ / 2) by ring, Real.tanh_neg]
  rw [h, neg_sq]

/-- THEOREM: the forward squared-wall equation for a positive gap has exactly
one solution, at the inverse-hyperbolic wall time. -/
theorem positive_gap_sq_wall_iff {δ τ : ℝ} (hδ : 0 < δ) (hτ : 0 ≤ τ) :
    gapPeel δ 0 τ ^ 2 = (1 / 2 : ℝ) ↔
      τ = 2 * Real.artanh wall / δ := by
  constructor
  · intro hsq
    apply (gapPeel_eq_wall_iff hδ τ).1
    apply (sq_eq_sq₀ (gapPeel_nonneg hδ hτ) wall_pos.le).1
    rw [hsq, wall_sq]
  · intro ht
    have he : gapPeel δ 0 τ = wall := (gapPeel_eq_wall_iff hδ τ).2 ht
    rw [he, wall_sq]

/-- THEOREM: every nonzero real common gap gives exactly one forward squared-wall
crossing from `Γ(0)=0`; a zero gap gives none. -/
theorem existsUnique_forward_wall_iff (δ : ℝ) :
    (∃! τ : ℝ, 0 ≤ τ ∧ gapPeel δ 0 τ ^ 2 = (1 / 2 : ℝ)) ↔ δ ≠ 0 := by
  constructor
  · intro hex hzero
    subst δ
    obtain ⟨τ, hτ, _⟩ := hex
    have hz := hτ.2
    norm_num [gapPeel, gapLedger] at hz
  · intro hδ
    rcases lt_or_gt_of_ne hδ with hneg | hpos
    · let T := 2 * Real.artanh wall / (-δ)
      have hp : 0 < -δ := neg_pos.mpr hneg
      have hT : 0 ≤ T := by
        have ha : 0 ≤ Real.artanh wall := Real.artanh_nonneg wall_pos.le
        exact div_nonneg (by positivity) hp.le
      refine ⟨T, ⟨hT, ?_⟩, ?_⟩
      · rw [← gapPeel_neg_rate_sq]
        exact (positive_gap_sq_wall_iff hp hT).2 rfl
      · intro y hy
        apply (positive_gap_sq_wall_iff hp hy.1).1
        rw [gapPeel_neg_rate_sq]
        exact hy.2
    · let T := 2 * Real.artanh wall / δ
      have hT : 0 ≤ T := by
        have ha : 0 ≤ Real.artanh wall := Real.artanh_nonneg wall_pos.le
        exact div_nonneg (by positivity) hpos.le
      refine ⟨T, ⟨hT, (positive_gap_sq_wall_iff hpos hT).2 rfl⟩, ?_⟩
      intro y hy
      exact (positive_gap_sq_wall_iff hpos hy.1).1 hy.2

/-- THEOREM: the wall time and spectral-gap magnitude satisfy the exact scale law
`|δ| τ_wall = 2 artanh(1/√2)`. -/
theorem forward_wall_time_mul_abs_gap {δ τ : ℝ} (hδ : δ ≠ 0) (hτ : 0 ≤ τ)
    (hsq : gapPeel δ 0 τ ^ 2 = (1 / 2 : ℝ)) :
    |δ| * τ = 2 * Real.artanh wall := by
  rcases lt_or_gt_of_ne hδ with hneg | hpos
  · have hp : 0 < -δ := neg_pos.mpr hneg
    have hsqp : gapPeel (-δ) 0 τ ^ 2 = (1 / 2 : ℝ) := by
      rw [gapPeel_neg_rate_sq]
      exact hsq
    have ht := (positive_gap_sq_wall_iff hp hτ).1 hsqp
    rw [abs_of_neg hneg, ht]
    field_simp [ne_of_gt hp]
  · have he : gapPeel δ 0 τ = wall := by
      apply (sq_eq_sq₀ (gapPeel_nonneg hpos hτ) wall_pos.le).1
      rw [hsq, wall_sq]
    have ht := (gapPeel_eq_wall_iff hpos τ).1 he
    rw [abs_of_pos hpos, ht]
    field_simp [ne_of_gt hpos]

/-- The same scale law as the quantised logarithmic-ledger value. -/
theorem forward_wall_time_mul_abs_gap_log {δ τ : ℝ} (hδ : δ ≠ 0) (hτ : 0 ≤ τ)
    (hsq : gapPeel δ 0 τ ^ 2 = (1 / 2 : ℝ)) :
    |δ| * τ = Real.log (3 + 2 * Real.sqrt 2) := by
  rw [forward_wall_time_mul_abs_gap hδ hτ hsq, two_artanh_wall]

/-- Zero gap is an explicit counterexample to a wall crossing from the origin. -/
theorem zero_gap_never_wall (τ : ℝ) :
    gapPeel 0 0 τ ^ 2 ≠ (1 / 2 : ℝ) := by
  simp [gapPeel, gapLedger]

/-- REFUTED: a nonzero common-clock gap does not imply affine phase silence.
For the affine readout `x = δτ`, `y = 1`, the numerator is `-δ`, not zero. -/
theorem affine_ledger_numerator (δ τ : ℝ) :
    (0 + δ * τ) * 0 - (1 + 0 * τ) * δ = -δ := by
  ring

theorem nonzero_gap_affine_readout_not_silent {δ : ℝ} (hδ : δ ≠ 0) (τ : ℝ) :
    (0 + δ * τ) * 0 - (1 + 0 * τ) * δ ≠ 0 := by
  rw [affine_ledger_numerator]
  exact neg_ne_zero.mpr hδ

end

end CommonClockPeel
