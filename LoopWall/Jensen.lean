import Mathlib

/-!
# Weighted Jensen for f x = x/(1+x), and the ratio bounds

Direction D5.  `weighted_jensen` (tangent-line proof, with the exact remainder `tangent_sub_f`),
`sum_rule_bounds` (0 < L, L ≤ S/(1+S) < 1, 1 + S ≤ S/L), the equality case
`weighted_jensen_eq_iff` under strictly positive weights, the zero-weight
`zero_weight_equality_counterexample`, and `special_static_value` at `3 + 2√2`.

Written in the second parallel formalization round (swarm `smws2pzvk`, direction m2),
then recompiled and reviewed here; namespace and header added, `lemma` renamed to `theorem` so the
repository audit sees it, trailing `#print axioms` lines removed because `scripts/verify.py` audits
every named theorem.  See PROVENANCE.md.
-/

open scoped BigOperators

namespace ElementalPeeling.LoopWall.Jensen

/-- The concave response function appearing in the sum rule. -/
noncomputable def f (x : ℝ) : ℝ := x / (1 + x)

theorem f_pos {x : ℝ} (hx : 0 < x) : 0 < f x := by
  exact div_pos hx (by linarith)

theorem f_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ f x := by
  exact div_nonneg hx (by linarith)

theorem f_lt_one {x : ℝ} (hx : 0 ≤ x) : f x < 1 := by
  rw [f, div_lt_one (by linarith)]
  linarith

/-- The exact error in the tangent-line upper bound at `S`. -/
theorem tangent_sub_f (x S : ℝ) (hx : 0 ≤ x) (hS : 0 ≤ S) :
    f S + (x - S) / (1 + S) ^ 2 - f x =
      (x - S) ^ 2 / ((1 + x) * (1 + S) ^ 2) := by
  have hx1 : 1 + x ≠ 0 := by positivity
  have hS1 : 1 + S ≠ 0 := by positivity
  simp only [f]
  field_simp
  ring

theorem f_le_tangent (x S : ℝ) (hx : 0 ≤ x) (hS : 0 ≤ S) :
    f x ≤ f S + (x - S) / (1 + S) ^ 2 := by
  have h := tangent_sub_f x S hx hS
  have hn : 0 ≤ (x - S) ^ 2 / ((1 + x) * (1 + S) ^ 2) := by
    positivity
  linarith

theorem f_lt_tangent (x S : ℝ) (hx : 0 ≤ x) (hS : 0 ≤ S) (hxS : x ≠ S) :
    f x < f S + (x - S) / (1 + S) ^ 2 := by
  have h := tangent_sub_f x S hx hS
  have hn : 0 < (x - S) ^ 2 / ((1 + x) * (1 + S) ^ 2) := by
    have hs : 0 < (x - S) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hxS)
    positivity
  linarith

/-- Weighted Jensen's inequality, proved by summing the tangent-line errors. -/
theorem weighted_jensen {ι : Type*} [Fintype ι] (w x : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hwsum : ∑ i, w i = 1) (hx : ∀ i, 0 ≤ x i) :
    ∑ i, w i * f (x i) ≤ f (∑ i, w i * x i) := by
  let S := ∑ i, w i * x i
  have hS : 0 ≤ S := Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (hx i)
  have hpoint (i : ι) :
      w i * f (x i) ≤ w i * (f S + (x i - S) / (1 + S) ^ 2) :=
    mul_le_mul_of_nonneg_left (f_le_tangent (x i) S (hx i) hS) (hw i)
  have hlin : ∑ i, w i * ((x i - S) / (1 + S) ^ 2) = 0 := by
    calc
      ∑ i, w i * ((x i - S) / (1 + S) ^ 2) =
          (∑ i, (w i * x i - w i * S)) / (1 + S) ^ 2 := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = 0 := by
        rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hwsum]
        simp [S]
  calc
    ∑ i, w i * f (x i) ≤
        ∑ i, w i * (f S + (x i - S) / (1 + S) ^ 2) :=
      Finset.sum_le_sum fun i _ => hpoint i
    _ = (∑ i, w i) * f S + ∑ i, w i * ((x i - S) / (1 + S) ^ 2) := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib, Finset.sum_mul]
    _ = f S := by rw [hwsum, hlin]; ring
    _ = f (∑ i, w i * x i) := rfl


theorem weighted_response_pos {ι : Type*} [Fintype ι] (w x : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hx : ∀ i, 0 ≤ x i)
    (hS : 0 < ∑ i, w i * x i) : 0 < ∑ i, w i * f (x i) := by
  have hex : ∃ i, 0 < w i * x i := by
    by_contra h
    push Not at h
    have hn := Finset.sum_nonpos (s := Finset.univ) (fun i _ => h i)
    linarith
  obtain ⟨i, hi⟩ := hex
  have hwi : 0 < w i := pos_of_mul_pos_left hi (hx i)
  have hxi : 0 < x i := pos_of_mul_pos_right hi (hw i)
  exact Finset.sum_pos'
    (fun j _ => mul_nonneg (hw j) (f_nonneg (hx j)))
    ⟨i, Finset.mem_univ i, mul_pos hwi (f_pos hxi)⟩

/-- The positivity, static upper bound, and lower ratio bound in one package. -/
theorem sum_rule_bounds {ι : Type*} [Fintype ι] (w x : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hwsum : ∑ i, w i = 1) (hx : ∀ i, 0 ≤ x i)
    (hS : 0 < ∑ i, w i * x i) :
    0 < ∑ i, w i * f (x i) ∧
    (∑ i, w i * f (x i)) ≤ (∑ i, w i * x i) / (1 + ∑ i, w i * x i) ∧
    (∑ i, w i * x i) / (1 + ∑ i, w i * x i) < 1 ∧
    1 + (∑ i, w i * x i) ≤
      (∑ i, w i * x i) / (∑ i, w i * f (x i)) ∧
    1 < (∑ i, w i * x i) / (∑ i, w i * f (x i)) := by
  set S : ℝ := ∑ i, w i * x i with hSdef
  set L : ℝ := ∑ i, w i * f (x i) with hLdef
  have hL : 0 < L := weighted_response_pos w x hw hx hS
  have hJL : L ≤ S / (1 + S) := by
    simpa only [hLdef, hSdef, f] using weighted_jensen w x hw hwsum hx
  have hstatic : S / (1 + S) < 1 := by
    simpa only [hSdef, f] using f_lt_one hS.le
  have hS1 : 0 < 1 + S := by linarith
  have hmul : (1 + S) * L ≤ S := by
    have hh := mul_le_mul_of_nonneg_left hJL hS1.le
    have heq : (1 + S) * (S / (1 + S)) = S := by
      field_simp
    rw [heq] at hh
    exact hh
  have hratio : 1 + S ≤ S / L := (le_div_iff₀ hL).2 hmul
  exact ⟨hL, hJL, hstatic, hratio, lt_of_lt_of_le (by linarith) hratio⟩


/-- With strictly positive weights, equality holds exactly for a constant family.
The value of that constant is necessarily its weighted mean `S`. -/
theorem weighted_jensen_eq_iff {ι : Type*} [Fintype ι] (w x : ι → ℝ)
    (hw : ∀ i, 0 < w i) (hwsum : ∑ i, w i = 1) (hx : ∀ i, 0 ≤ x i) :
    (∑ i, w i * f (x i)) = f (∑ i, w i * x i) ↔
      ∀ i, x i = ∑ i, w i * x i := by
  set S : ℝ := ∑ i, w i * x i with hSdef
  have hS : 0 ≤ S := Finset.sum_nonneg fun i _ => mul_nonneg (hw i).le (hx i)
  have hpoint (i : ι) :
      w i * f (x i) ≤ w i * (f S + (x i - S) / (1 + S) ^ 2) :=
    mul_le_mul_of_nonneg_left (f_le_tangent (x i) S (hx i) hS) (hw i).le
  have hlin : ∑ i, w i * ((x i - S) / (1 + S) ^ 2) = 0 := by
    calc
      ∑ i, w i * ((x i - S) / (1 + S) ^ 2) =
          (∑ i, (w i * x i - w i * S)) / (1 + S) ^ 2 := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = 0 := by
        rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hwsum]
        simp [S]
  have htan : ∑ i, w i * (f S + (x i - S) / (1 + S) ^ 2) = f S := by
    calc
      ∑ i, w i * (f S + (x i - S) / (1 + S) ^ 2) =
          (∑ i, w i) * f S + ∑ i, w i * ((x i - S) / (1 + S) ^ 2) := by
        simp_rw [mul_add]
        rw [Finset.sum_add_distrib, Finset.sum_mul]
      _ = f S := by rw [hwsum, hlin]; ring
  constructor
  · intro heq i
    by_contra hne
    have hi : w i * f (x i) < w i * (f S + (x i - S) / (1 + S) ^ 2) :=
      mul_lt_mul_of_pos_left (f_lt_tangent (x i) S (hx i) hS hne) (hw i)
    have hstrict : (∑ j, w j * f (x j)) <
        ∑ j, w j * (f S + (x j - S) / (1 + S) ^ 2) :=
      Finset.sum_lt_sum (fun j _ => hpoint j) ⟨i, Finset.mem_univ i, hi⟩
    rw [htan] at hstrict
    exact (ne_of_lt hstrict) heq
  · intro h
    calc
      ∑ i, w i * f (x i) = ∑ i, w i * f S := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [h i]
      _ = (∑ i, w i) * f S := by rw [Finset.sum_mul]
      _ = f S := by rw [hwsum, one_mul]

/-- Strict positivity of the weights cannot be omitted from the equality claim:
here the upper bound is attained although the two values are different. -/
theorem zero_weight_equality_counterexample :
    ∃ w x : Fin 2 → ℝ,
      (∀ i, 0 ≤ w i) ∧ (∑ i, w i) = 1 ∧ (∀ i, 0 ≤ x i) ∧
      (∑ i, w i * f (x i)) = f (∑ i, w i * x i) ∧
      x 0 ≠ x 1 := by
  refine ⟨![1, 0], ![0, 1], ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> norm_num
  · norm_num [Fin.sum_univ_two]
  · intro i
    fin_cases i <;> norm_num
  · norm_num [Fin.sum_univ_two, f]
  · norm_num

/-- The algebraic value at the special static input `3 + 2 * sqrt 2`. -/
theorem special_static_value :
    f (3 + 2 * Real.sqrt 2) = 1 - 1 / (4 + 2 * Real.sqrt 2) := by
  have hr : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hden : 4 + 2 * Real.sqrt 2 ≠ 0 := by positivity
  simp only [f]
  field_simp
  ring

/-
Scope: these are deterministic inequalities for the explicitly defined real
function `f` and finite normalized weights.  No assumption identifying
`S / (1 + S)`, `L`, or `S / L` with a physical `ε_s` is made or proved here.
-/


end ElementalPeeling.LoopWall.Jensen
