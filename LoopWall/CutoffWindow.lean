import Mathlib

/-!
# The cutoff window: which thresholds sort a finite table the same way

Direction D6.  `cutoff_window` is the finite max/min lemma, `outsideSet_antitone` the
monotonicity in the cutoff, `rational_wall_quadratic` the √2-free rational test,
`loop_wall_ratio_bounds` places `3 + 2√2` inside the paper's data window with explicit rational
bounds on `√2`, and `quadratic_pos_iff_two_branches`/`peel_threshold_two_branches` give the
two-branch form and the exact `2(b−a)² > (b+a)²` test.

Written in the parallel formalization round (swarm `smws25izm`, direction m2),
then recompiled and reviewed here; namespace and header added, trailing `#print axioms` lines
removed because `scripts/verify.py` audits every named theorem.  See PROVENANCE.md.
-/

/-!
# The cutoff window and the loop-wall quadratic

This file formalizes direction D6. The finite-window theorem is stated for
arbitrary finite sets of real numbers; positivity of their elements is not
needed. For (ii), `outsideSet c` is the rising-side set `{z | c < z}`.
-/

namespace ElementalPeeling.LoopWall.CutoffWindow

/-- A finite set lies strictly below `c` and another lies strictly above `c`
exactly when the maximum of the first and minimum of the second leave a window
around `c`. -/
theorem cutoff_window (S T : Finset ℝ) (hS : S.Nonempty) (hT : T.Nonempty)
    (c : ℝ) :
    ((∀ w ∈ T, w < c) ∧ (∀ v ∈ S, c < v)) ↔
      (T.max' hT < c ∧ c < S.min' hS) := by
  simp only [Finset.max'_lt_iff, Finset.lt_min'_iff]

/-- The part of the rising side beyond a real cutoff. -/
def outsideSet (c : ℝ) : Set ℝ := {z | c < z}

/-- Raising the cutoff shrinks the outside set. -/
theorem outsideSet_antitone : Antitone outsideSet := by
  intro c d hcd z hz
  exact hcd.trans_lt hz

/-- The peel reflection on rational ratios. -/
def gam (z : ℚ) : ℚ := (z - 1) / (z + 1)

/-- On rationals greater than one, the wall test is exactly positivity of the
loop-wall quadratic. -/
theorem rational_wall_quadratic (c : ℚ) (hc : 1 < c) :
    1 / 2 < gam c * gam c ↔ 0 < c * c - 6 * c + 1 := by
  have hpos : (0 : ℚ) < c + 1 := by linarith
  have hsq : gam c * gam c = (c - 1) ^ 2 / (c + 1) ^ 2 := by
    simp only [gam, div_mul_div_comm]
    ring
  rw [hsq, lt_div_iff₀ (sq_pos_of_pos hpos)]
  constructor <;> intro h <;> nlinarith

/-- The real loop-wall root lies strictly between the two quoted decimal
bounds. -/
theorem loop_wall_ratio_bounds :
    (5.8079020598 : ℝ) < 3 + 2 * Real.sqrt 2 ∧
      3 + 2 * Real.sqrt 2 < 5.8665387761 := by
  have hlo : (1.41 : ℝ) < Real.sqrt 2 :=
    (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  have hhi : Real.sqrt 2 < (1.42 : ℝ) :=
    (Real.sqrt_lt (by norm_num) (by norm_num)).2 (by norm_num)
  constructor <;> nlinarith

/-- Positivity of `z² - 6z + 1` is precisely the two exterior root branches.
This form does not need a positivity hypothesis on `z`. -/
theorem quadratic_pos_iff_two_branches (z : ℝ) :
    0 < z ^ 2 - 6 * z + 1 ↔
      (3 + 2 * Real.sqrt 2 < z ∨ z < 3 - 2 * Real.sqrt 2) := by
  have hs : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hspos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hfactor : z ^ 2 - 6 * z + 1 =
      (z - (3 + 2 * Real.sqrt 2)) * (z - (3 - 2 * Real.sqrt 2)) := by
    nlinarith
  rw [hfactor, mul_pos_iff]
  constructor
  · rintro (⟨hp, hm⟩ | ⟨hp, hm⟩)
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  · rintro (hp | hm)
    · exact Or.inl ⟨by linarith, by linarith⟩
    · exact Or.inr ⟨by linarith, by linarith⟩

/-- The reduced two-face inequality is equivalent to the two exact root
branches for the peel ratio `b / a`. -/
theorem peel_threshold_two_branches {a b : ℝ} (ha : 0 < a) (_hb : 0 < b) :
    2 * (b - a) ^ 2 > (b + a) ^ 2 ↔
      (b / a > 3 + 2 * Real.sqrt 2 ∨ b / a < 3 - 2 * Real.sqrt 2) := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hid : (b / a) ^ 2 - 6 * (b / a) + 1 =
      (b ^ 2 - 6 * b * a + a ^ 2) / a ^ 2 := by
    field_simp
  calc
    2 * (b - a) ^ 2 > (b + a) ^ 2 ↔ 0 < b ^ 2 - 6 * b * a + a ^ 2 := by
      constructor <;> intro h <;> nlinarith
    _ ↔ 0 < (b / a) ^ 2 - 6 * (b / a) + 1 := by
      rw [hid, div_pos_iff_of_pos_right (sq_pos_of_pos ha)]
    _ ↔ (b / a > 3 + 2 * Real.sqrt 2 ∨ b / a < 3 - 2 * Real.sqrt 2) :=
      quadratic_pos_iff_two_branches (b / a)

end ElementalPeeling.LoopWall.CutoffWindow
