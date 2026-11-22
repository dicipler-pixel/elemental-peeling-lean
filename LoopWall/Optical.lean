import Mathlib

/-!
# The same half power in optics, and the Rice–Mele band-edge condition

Direction D8.  `reflectance_*_half_iff` are the three sign cases of the normal-incidence
reflectance against `1/2`; `loop_quadratic_roots` and `loop_ratio_squared`; `rice_mele_energy_iff`
and `rice_mele_zero_v_roots`.  The module also records that the implication
`T/L ≤ ε_s ∧ 3 + 2√2 < T/L → 17 + 12√2 < ε_s` is FALSE (`squared_bound_as_written_false`), proves
the valid consequence `3 + 2√2 < ε_s`, and proves the corrected version that needs
`(T/L)² ≤ ε_s`.

Written in the parallel formalization round (swarm `smws25izm`, direction m5),
then recompiled and reviewed here; namespace and header added, trailing `#print axioms` lines
removed because `scripts/verify.py` audits every named theorem.  See PROVENANCE.md.
-/

/-!
# Optical reflectance and Rice--Mele loop-wall identities

All numerical statements are over `ℝ`.  The final part of D8(iv), as literally
stated, is false: `T/L ≤ ε_s` and `T/L > 3 + 2√2` do not imply that `ε_s` is
larger than the *square* of `3 + 2√2`.  `squared_bound_as_written_false` below
gives the counterexample `T = ε_s = 6`, `L = 1`.  We then prove the valid
consequence `ε_s > 3 + 2√2`, and a corrected square-controlled implication in
which `T/L ≤ ε_s` is replaced by `(T/L)^2 ≤ ε_s`.
-/

namespace ElementalPeeling.LoopWall.Optical

/-- Normal-incidence optical reflectance, in the real `(n, κ)` parametrization. -/
noncomputable def reflectance (n κ : ℝ) : ℝ :=
  ((n - 1)^2 + κ^2) / ((n + 1)^2 + κ^2)

/-- D8(i), strict outside form. -/
theorem reflectance_gt_half_iff (n κ : ℝ)
    (hden : 0 < (n + 1)^2 + κ^2) :
    1 / 2 < reflectance n κ ↔ 8 < (n - 3)^2 + κ^2 := by
  unfold reflectance
  rw [lt_div_iff₀ hden]
  constructor <;> intro h <;> nlinarith

/-- D8(i), strict inside form. -/
theorem reflectance_lt_half_iff (n κ : ℝ)
    (hden : 0 < (n + 1)^2 + κ^2) :
    reflectance n κ < 1 / 2 ↔ (n - 3)^2 + κ^2 < 8 := by
  unfold reflectance
  rw [div_lt_iff₀ hden]
  constructor <;> intro h <;> nlinarith

/-- D8(i), boundary form. -/
theorem reflectance_eq_half_iff (n κ : ℝ)
    (hden : 0 < (n + 1)^2 + κ^2) :
    reflectance n κ = 1 / 2 ↔ (n - 3)^2 + κ^2 = 8 := by
  unfold reflectance
  rw [div_eq_iff hden.ne']
  constructor <;> intro h <;> nlinarith

/-- D8(ii): the two real square-root expressions are precisely the roots of
`X² - 6X + 1`. -/
theorem loop_quadratic_roots (x : ℝ) :
    x^2 - 6 * x + 1 = 0 ↔
      x = 3 + 2 * Real.sqrt 2 ∨ x = 3 - 2 * Real.sqrt 2 := by
  have hs : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
  have hfactor : x^2 - 6 * x + 1 =
      (x - (3 + 2 * Real.sqrt 2)) * (x - (3 - 2 * Real.sqrt 2)) := by
    nlinarith
  rw [hfactor]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (sub_eq_zero.mp h)
  · rintro (rfl | rfl) <;> ring

/-- D8(iii), exact polynomial identity. -/
theorem rice_mele_energy_iff (t₁ t₂ v : ℝ) :
    2 * ((t₁ - t₂)^2 + v^2) = (t₁ + t₂)^2 + v^2 ↔
      t₁^2 + t₂^2 + v^2 = 6 * t₁ * t₂ := by
  constructor <;> intro h <;> nlinarith

/-- D8(iii), zero onsite offset.  The stated hypothesis `0 < t₁` is included;
in fact the equivalence is valid for every real `t₁`. -/
theorem rice_mele_zero_v_roots (t₁ t₂ : ℝ) (_ht₁ : 0 < t₁) :
    2 * ((t₁ - t₂)^2 + (0 : ℝ)^2) = (t₁ + t₂)^2 + (0 : ℝ)^2 ↔
      t₂ = (3 + 2 * Real.sqrt 2) * t₁ ∨
        t₂ = (3 - 2 * Real.sqrt 2) * t₁ := by
  rw [rice_mele_energy_iff]
  have hs : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
  have hfactor : t₁^2 + t₂^2 + (0 : ℝ)^2 - 6 * t₁ * t₂ =
      (t₂ - (3 + 2 * Real.sqrt 2) * t₁) *
        (t₂ - (3 - 2 * Real.sqrt 2) * t₁) := by
    nlinarith
  constructor
  · intro h
    have hzero : t₁^2 + t₂^2 + (0 : ℝ)^2 - 6 * t₁ * t₂ = 0 :=
      sub_eq_zero.mpr h
    rw [hfactor] at hzero
    rcases mul_eq_zero.mp hzero with hzero | hzero
    · exact Or.inl (sub_eq_zero.mp hzero)
    · exact Or.inr (sub_eq_zero.mp hzero)
  · intro h
    have hprod :
        (t₂ - (3 + 2 * Real.sqrt 2) * t₁) *
          (t₂ - (3 - 2 * Real.sqrt 2) * t₁) = 0 := by
      rcases h with rfl | rfl <;> ring
    have hzero : t₁^2 + t₂^2 + (0 : ℝ)^2 - 6 * t₁ * t₂ = 0 := by
      rw [hfactor]
      exact hprod
    exact sub_eq_zero.mp hzero

/-- D8(iv), algebraic square of the rising loop-wall ratio. -/
theorem loop_ratio_squared :
    (3 + 2 * Real.sqrt 2)^2 = 17 + 12 * Real.sqrt 2 := by
  have hs : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
  nlinarith

/-- The last implication in D8(iv), with only `T/L ≤ ε_s`, is false. -/
theorem squared_bound_as_written_false :
    ¬ (∀ T L εs : ℝ,
      1 < T / L → T / L ≤ εs → 3 + 2 * Real.sqrt 2 < T / L →
        17 + 12 * Real.sqrt 2 < εs) := by
  intro h
  have hs : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hs_upper : Real.sqrt 2 < 3 / 2 := by
    nlinarith [sq_nonneg (Real.sqrt 2 - 3 / 2)]
  have hlarge : 3 + 2 * Real.sqrt 2 < (6 : ℝ) / 1 := by
    norm_num
    nlinarith
  have hbad := h 6 1 6 (by norm_num) (by norm_num) hlarge
  nlinarith

/-- What does follow from the original inequalities, without changing any
hypothesis, is the unsquared lower bound. -/
theorem threshold_bound_valid_consequence (T L εs : ℝ)
    (_hratio : 1 < T / L) (hle : T / L ≤ εs)
    (hlarge : 3 + 2 * Real.sqrt 2 < T / L) :
    3 + 2 * Real.sqrt 2 < εs :=
  hlarge.trans_le hle

/-- Corrected squared version of D8(iv): the scale parameter must control the
square of `T/L`, rather than only `T/L` itself. -/
theorem squared_threshold_bound_corrected (T L εs : ℝ)
    (_hratio : 1 < T / L) (hle : (T / L)^2 ≤ εs)
    (hlarge : 3 + 2 * Real.sqrt 2 < T / L) :
    17 + 12 * Real.sqrt 2 < εs := by
  rw [← loop_ratio_squared]
  have hscale : 0 ≤ T / L := by linarith
  have hbase : 0 ≤ 3 + 2 * Real.sqrt 2 := by positivity
  have hsq : (3 + 2 * Real.sqrt 2)^2 < (T / L)^2 := by
    nlinarith [mul_pos (sub_pos.mpr hlarge)
      (add_pos_of_nonneg_of_pos hbase (sub_pos.mpr hlarge))]
  exact hsq.trans_le hle

end ElementalPeeling.LoopWall.Optical
