import Mathlib

/-!
# The anion rung in hardness/electronegativity language, and the two-face product form

Direction D7.  `anion_rung_eq_hardness_div_electronegativity` is `Γ₀ = η/χ`.  The module
records that `ω > η ↔ 1/2 < Γ₀²` is FALSE (`electrophilicity_wall_as_written_false`) and proves the
correct direction, `ω > η ↔ Γ₀² < 1/2`; `two_face_product_iff_of_nonneg` and
`sinh_product_lt_one_iff` link `sinh h_a · sinh h_b < 1` to `x + y < 1` and to
`x·y < (1−x)(1−y)`; `uniqueInteriorBoundary` and `strictCounterexample` are the real-valued
uniqueness of the diagonal threshold and its counterexample away from `1/2`.

Written in the parallel formalization round (swarm `smws25izm`, direction m7),
then recompiled and reviewed here; namespace and header added, trailing `#print axioms` lines
removed because `scripts/verify.py` audits every named theorem.  See PROVENANCE.md.
-/

/-!
# Anion rung and the two-face product form

All numerical comparisons in this file are over the real numbers.  The cleared
polynomials `additive` and `product` are the same ones as in the rational
`BoundaryAgreement` development.
-/

namespace ElementalPeeling.LoopWall.Rung

/-- Pearson hardness. -/
noncomputable def hardness (I E : ℝ) : ℝ := (I - E) / 2

/-- Mulliken electronegativity. -/
noncomputable def electronegativity (I E : ℝ) : ℝ := (I + E) / 2

/-- Electrophilicity, in the convention `ω = χ² / (2η)`. -/
noncomputable def electrophilicity (I E : ℝ) : ℝ :=
  electronegativity I E ^ 2 / (2 * hardness I E)

/-- The anion reflection is hardness divided by electronegativity. -/
theorem anion_rung_eq_hardness_div_electronegativity (I E : ℝ)
    (hE : 0 < E) (hIE : E < I) :
    (I - E) / (I + E) = hardness I E / electronegativity I E := by
  have hsum : I + E ≠ 0 := ne_of_gt (by linarith)
  have hchi : electronegativity I E ≠ 0 := by
    unfold electronegativity
    exact div_ne_zero hsum (by norm_num)
  unfold hardness electronegativity
  field_simp

/-- The comparison stated with `1/2 < Γ₀²` is false: at `I = 3`, `E = 1`,
electrophilicity exceeds hardness although `Γ₀² = 1/4`. -/
theorem electrophilicity_wall_as_written_false :
    ¬ (electrophilicity 3 1 > hardness 3 1 ↔
      1 / 2 < (((3 : ℝ) - 1) / (3 + 1)) ^ 2) := by
  norm_num [electrophilicity, hardness, electronegativity]

/-- Corrected comparison: electrophilicity exceeds hardness exactly below the
squared loop wall. -/
theorem electrophilicity_gt_hardness_iff (I E : ℝ)
    (hE : 0 < E) (hIE : E < I) :
    electrophilicity I E > hardness I E ↔
      ((I - E) / (I + E)) ^ 2 < 1 / 2 := by
  have hη : 0 < hardness I E := by
    unfold hardness
    linarith
  have hχ : 0 < electronegativity I E := by
    unfold electronegativity
    linarith
  rw [anion_rung_eq_hardness_div_electronegativity I E hE hIE]
  unfold electrophilicity
  change hardness I E < electronegativity I E ^ 2 / (2 * hardness I E) ↔ _
  rw [lt_div_iff₀ (show 0 < 2 * hardness I E by positivity)]
  rw [div_pow, div_lt_iff₀ (sq_pos_of_pos hχ)]
  constructor
  · intro h
    have hh := mul_lt_mul_of_pos_left h (show (0 : ℝ) < 1 / 2 by norm_num)
    convert hh using 1 <;> ring
  · intro h
    have hh := mul_lt_mul_of_pos_left h (show (0 : ℝ) < 2 by norm_num)
    convert hh using 1 <;> ring

/-- The elementary product-of-odds comparison is the sum comparison. -/
theorem two_face_odds_lt_iff (x y : ℝ) :
    x * y < (1 - x) * (1 - y) ↔ x + y < 1 := by
  constructor <;> intro h <;> nlinarith

/-- Algebraic form of the two-face product test, with `u,v` playing the roles
of the two (nonnegative) hyperbolic sines. -/
theorem two_face_product_iff_of_nonneg (u v x y : ℝ)
    (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hx : 0 ≤ x) (hx1 : x < 1) (hy : 0 ≤ y) (hy1 : y < 1)
    (hu2 : u ^ 2 = x / (1 - x)) (hv2 : v ^ 2 = y / (1 - y)) :
    u * v < 1 ↔ x + y < 1 := by
  have hden : 0 < (1 - x) * (1 - y) := mul_pos (by linarith) (by linarith)
  have huv : 0 ≤ u * v := mul_nonneg hu hv
  have hsq : (u * v) ^ 2 = x * y / ((1 - x) * (1 - y)) := by
    rw [mul_pow, hu2, hv2, div_mul_div_comm]
  rw [← sq_lt_one_iff₀ huv, hsq, div_lt_one hden]
  exact (two_face_odds_lt_iff x y)

/-- The intended, signed-height-corrected two-face equivalence. -/
theorem sinh_product_lt_one_iff (ha hb x y : ℝ)
    (ha0 : 0 ≤ Real.sinh ha) (hb0 : 0 ≤ Real.sinh hb)
    (hx : 0 ≤ x) (hx1 : x < 1) (hy : 0 ≤ y) (hy1 : y < 1)
    (ha2 : Real.sinh ha ^ 2 = x / (1 - x))
    (hb2 : Real.sinh hb ^ 2 = y / (1 - y)) :
    Real.sinh ha * Real.sinh hb < 1 ↔ x + y < 1 :=
  two_face_product_iff_of_nonneg _ _ _ _ ha0 hb0 hx hx1 hy hy1 ha2 hb2

/-- The equivalent product-of-odds form of the corrected two-face test. -/
theorem sinh_product_lt_one_iff_odds (ha hb x y : ℝ)
    (ha0 : 0 ≤ Real.sinh ha) (hb0 : 0 ≤ Real.sinh hb)
    (hx : 0 ≤ x) (hx1 : x < 1) (hy : 0 ≤ y) (hy1 : y < 1)
    (ha2 : Real.sinh ha ^ 2 = x / (1 - x))
    (hb2 : Real.sinh hb ^ 2 = y / (1 - y)) :
    Real.sinh ha * Real.sinh hb < 1 ↔ x * y < (1 - x) * (1 - y) :=
  (sinh_product_lt_one_iff ha hb x y ha0 hb0 hx hx1 hy hy1 ha2 hb2).trans
    (two_face_odds_lt_iff x y).symm

/-- The statement without a sign hypothesis is false.  At the exhibited pair,
the left side is true (`-1 < 1`) while the right side is false (`1 < 1`). -/
theorem sinh_product_counterexample :
    ∃ ha hb x y : ℝ, 0 ≤ x ∧ x < 1 ∧ 0 ≤ y ∧ y < 1 ∧
      Real.sinh ha ^ 2 = x / (1 - x) ∧
      Real.sinh hb ^ 2 = y / (1 - y) ∧
      ¬ (Real.sinh ha * Real.sinh hb < 1 ↔ x + y < 1) := by
  refine ⟨-Real.arsinh 1, Real.arsinh 1, 1 / 2, 1 / 2,
    by norm_num, by norm_num, by norm_num, by norm_num, ?_, ?_, ?_⟩
  · norm_num [Real.sinh_neg, Real.sinh_arsinh]
  · norm_num [Real.sinh_arsinh]
  · norm_num [Real.sinh_neg, Real.sinh_arsinh]

/-- Sum-form margin at diagonal threshold `t`. -/
def additive (t x y : ℝ) : ℝ := x + y - 2 * t

/-- Product-form margin after clearing its positive denominators. -/
def product (t x y : ℝ) : ℝ :=
  x * y * (1 - t) * (1 - t) - t * t * (1 - x) * (1 - y)

/-- Agreement of negative, zero, and positive comparisons. -/
def ThreeClasses (a b : ℝ) : Prop :=
  ((a < 0) ↔ (b < 0)) ∧ ((a = 0) ↔ (b = 0)) ∧ ((0 < a) ↔ (0 < b))

/-- The two cleared forms agree on the open interior square. -/
def Agree (t : ℝ) : Prop :=
  ∀ x y : ℝ, 0 < x → x < 1 → 0 < y → y < 1 →
    ThreeClasses (additive t x y) (product t x y)

/-- An interior pair lying on the additive boundary. -/
theorem witnessInterior (t : ℝ) (h0 : 0 < t) (h1 : t < 1) :
    0 < t * t ∧ t * t < 1 ∧ 0 < 2 * t - t * t ∧ 2 * t - t * t < 1 := by
  have hd : 0 < 1 - t := by linarith
  have ht : 0 < t * t := mul_pos h0 h0
  have hprod : 0 < t * (1 - t) := mul_pos h0 hd
  have hs : 0 < (1 - t) * (1 - t) := mul_pos hd hd
  constructor
  · exact ht
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem witnessTie (t : ℝ) : additive t (t * t) (2 * t - t * t) = 0 := by
  unfold additive
  ring

theorem witnessProduct (t : ℝ) :
    product t (t * t) (2 * t - t * t) =
      (t * t * ((1 - t) * (1 - t))) * (2 * t - 1) := by
  unfold product
  ring

theorem halfScaling (x y : ℝ) :
    4 * product (1 / 2) x y = additive (1 / 2) x y := by
  unfold additive product
  ring

/-- Only the diagonal threshold `1/2` makes all three comparison classes agree. -/
theorem uniqueInteriorBoundary (t : ℝ) (h0 : 0 < t) (h1 : t < 1) :
    Agree t ↔ t = 1 / 2 := by
  constructor
  · intro hall
    obtain ⟨hx0, hx1, hy0, hy1⟩ := witnessInterior t h0 h1
    have hclass := hall (t * t) (2 * t - t * t) hx0 hx1 hy0 hy1
    have hzero := hclass.2.1.mp (witnessTie t)
    rw [witnessProduct] at hzero
    have hd : 0 < 1 - t := by linarith
    have hne : t * t * ((1 - t) * (1 - t)) ≠ 0 := by
      exact ne_of_gt (mul_pos (mul_pos h0 h0) (mul_pos hd hd))
    have hz : 2 * t - 1 = 0 := by
      rcases mul_eq_zero.mp hzero with hh | hh
      · exact False.elim (hne hh)
      · exact hh
    linarith
  · rintro rfl x y _ _ _ _
    have h := halfScaling x y
    unfold ThreeClasses
    rw [← h]
    constructor
    · constructor <;> intro hh <;> nlinarith
    constructor
    · constructor <;> intro hh <;> nlinarith
    · constructor <;> intro hh <;> nlinarith

/-- Midpoint between the two competing `y`-boundaries at `x = t²`. -/
noncomputable def midY (t : ℝ) : ℝ := ((2 * t - t * t) + (1 + t) / 2) / 2

theorem midInterior (t : ℝ) (h0 : 0 < t) (h1 : t < 1) :
    0 < midY t ∧ midY t < 1 := by
  obtain ⟨_, _, hy0, hy1⟩ := witnessInterior t h0 h1
  unfold midY
  constructor <;> nlinarith

theorem midMargins (t : ℝ) :
    4 * additive t (t * t) (midY t) = (1 - t) * (1 - 2 * t) ∧
    product t (t * t) (midY t) =
      -(2 * t * t * (1 - t)) * additive t (t * t) (midY t) := by
  unfold midY additive product
  constructor <;> ring

/-- Away from `1/2`, strictly interior inputs make opposite strict calls. -/
theorem strictCounterexample (t : ℝ) (h0 : 0 < t) (h1 : t < 1)
    (hn : t ≠ 1 / 2) :
    ∃ x y : ℝ, 0 < x ∧ x < 1 ∧ 0 < y ∧ y < 1 ∧
      ((additive t x y < 0 ∧ 0 < product t x y) ∨
       (0 < additive t x y ∧ product t x y < 0)) := by
  obtain ⟨hx0, hx1, _, _⟩ := witnessInterior t h0 h1
  obtain ⟨hy0, hy1⟩ := midInterior t h0 h1
  obtain ⟨ha, hp⟩ := midMargins t
  have hd : 0 < 1 - t := by linarith
  have hpcoef : 0 < 2 * t * t * (1 - t) := by positivity
  refine ⟨t * t, midY t, hx0, hx1, hy0, hy1, ?_⟩
  by_cases hlt : t < 1 / 2
  · have hm : 0 < (1 - t) * (1 - 2 * t) :=
      mul_pos hd (by linarith)
    have haPos : 0 < additive t (t * t) (midY t) := by nlinarith
    have hh : 0 < (2 * t * t * (1 - t)) * additive t (t * t) (midY t) :=
      mul_pos hpcoef haPos
    exact Or.inr ⟨haPos, by nlinarith⟩
  · have hgt : 1 / 2 < t := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hn)
    have hm : (1 - t) * (1 - 2 * t) < 0 :=
      mul_neg_of_pos_of_neg hd (by linarith)
    have haNeg : additive t (t * t) (midY t) < 0 := by nlinarith
    have hh : 0 < (2 * t * t * (1 - t)) * (-additive t (t * t) (midY t)) :=
      mul_pos hpcoef (neg_pos.mpr haNeg)
    exact Or.inl ⟨haNeg, by nlinarith⟩

end ElementalPeeling.LoopWall.Rung
