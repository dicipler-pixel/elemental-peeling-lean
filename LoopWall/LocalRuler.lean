import Mathlib

/-!
# The local ruler does not fix the ledger

Direction D3 of the third round.  For `ruler a t = sqrt (log (cosh (a*t/2)))/a`: `ruler_scaling`
is the exact `ruler a t = ruler 1 (a t)/a`; `ruler_one_strictAntiOn` and `ruler_one_eq_iff` show the
finite unit-time readings separate every positive scale; and `ruler_right_slope` proves every scale
has the same right-hand infinitesimal slope `1/(2√2)`, obtained from the density squeeze
`2/(x²+4) ≤ log (cosh x)/x² ≤ 1/2` and `tendsto_log_cosh_div_sq` (a punctured-neighbourhood limit,
not a one-sided estimate).  `local_ruler_does_not_fix_ledger` packages the two halves: the local
ruler cannot select the ledger, the finite readings can.

Written in the third parallel formalization round (swarm `smws58h9u`, direction m3),
recompiled and reviewed here; namespace and header added, `#print axioms` lines removed.
-/

open Filter Set
open scoped Topology

namespace ElementalPeeling.LoopWall.LocalRuler

noncomputable def ruler (a t : ℝ) : ℝ :=
  Real.sqrt (Real.log (Real.cosh (a * t / 2))) / a

/-- Exact scaling of the ruler. -/
theorem ruler_scaling (a t : ℝ) : ruler a t = ruler 1 (a * t) / a := by
  simp [ruler]

/-- The quadratic lower bound obtained by retaining the first two cosh terms. -/
theorem one_add_sq_div_two_le_cosh (x : ℝ) : 1 + x ^ 2 / 2 ≤ Real.cosh x := by
  have hnonneg : ∀ i ∉ Finset.range 2,
      0 ≤ x ^ (2 * i) / (2 * i).factorial := by
    intro i hi
    exact div_nonneg ((even_two_mul i).pow_nonneg x) (by positivity)
  have h := sum_le_hasSum (Finset.range 2) hnonneg (Real.hasSum_cosh x)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  exact h

theorem log_cosh_le_sq_div_two (x : ℝ) : Real.log (Real.cosh x) ≤ x ^ 2 / 2 := by
  rw [Real.log_le_iff_le_exp (Real.cosh_pos x)]
  exact Real.cosh_le_exp_half_sq x

/-- A global rational lower bound for `log (cosh x)`. -/
theorem sq_two_mul_div_add_four_le_log_cosh (x : ℝ) :
    2 * x ^ 2 / (x ^ 2 + 4) ≤ Real.log (Real.cosh x) := by
  have hu : 0 ≤ Real.cosh x - 1 := sub_nonneg.mpr (Real.one_le_cosh x)
  have hlog := Real.le_log_one_add_of_nonneg hu
  have hquad := one_add_sq_div_two_le_cosh x
  have hden : 0 < (Real.cosh x - 1) + 2 := by positivity
  have hfrac : 2 * x ^ 2 / (x ^ 2 + 4) ≤
      2 * (Real.cosh x - 1) / ((Real.cosh x - 1) + 2) := by
    rw [div_le_div_iff₀ (by positivity) hden]
    nlinarith
  calc
    2 * x ^ 2 / (x ^ 2 + 4) ≤ 2 * (Real.cosh x - 1) /
        ((Real.cosh x - 1) + 2) := hfrac
    _ ≤ Real.log (1 + (Real.cosh x - 1)) := hlog
    _ = Real.log (Real.cosh x) := by ring_nf

theorem log_cosh_div_sq_lower {x : ℝ} (hx : x ≠ 0) :
    2 / (x ^ 2 + 4) ≤ Real.log (Real.cosh x) / x ^ 2 := by
  have hx2 : 0 < x ^ 2 := sq_pos_of_ne_zero hx
  calc
    2 / (x ^ 2 + 4) = (2 * x ^ 2 / (x ^ 2 + 4)) / x ^ 2 := by
      field_simp
    _ ≤ Real.log (Real.cosh x) / x ^ 2 :=
      (div_le_div_iff_of_pos_right hx2).2 (sq_two_mul_div_add_four_le_log_cosh x)

theorem log_cosh_div_sq_upper {x : ℝ} (hx : x ≠ 0) :
    Real.log (Real.cosh x) / x ^ 2 ≤ 1 / 2 := by
  have hx2 : 0 < x ^ 2 := sq_pos_of_ne_zero hx
  rw [div_le_iff₀ hx2]
  nlinarith [log_cosh_le_sq_div_two x]

/-- The quadratic density of `log cosh` has limit `1/2` at the punctured origin. -/
theorem tendsto_log_cosh_div_sq :
    Tendsto (fun x : ℝ => Real.log (Real.cosh x) / x ^ 2)
      (𝓝[≠] 0) (𝓝 (1 / 2)) := by
  have hx : Tendsto (fun x : ℝ => x) (𝓝[≠] 0) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have hlower : Tendsto (fun x : ℝ => 2 / (x ^ 2 + 4))
      (𝓝[≠] 0) (𝓝 (2 / (0 ^ 2 + 4))) := by
    exact tendsto_const_nhds.div ((hx.pow 2).add_const 4) (by norm_num)
  norm_num at hlower
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower tendsto_const_nhds
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact log_cosh_div_sq_lower (by simpa using hx)
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact log_cosh_div_sq_upper (by simpa using hx)

/-- Derivative of real `tanh`, with no extra nonzero hypothesis. -/
theorem hasDerivAt_real_tanh (x : ℝ) :
    HasDerivAt Real.tanh (1 / (Real.cosh x) ^ 2) x := by
  have h := (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x)
    (Real.cosh_pos x).ne'
  have heq : (Real.cosh x * Real.cosh x - Real.sinh x * Real.sinh x) /
      Real.cosh x ^ 2 = 1 / Real.cosh x ^ 2 := by
    have hc := Real.cosh_sq_sub_sinh_sq x
    congr 1
    nlinarith
  rw [heq] at h
  have ht : Real.tanh = Real.sinh / Real.cosh := by
    funext y
    exact Real.tanh_eq_sinh_div_cosh y
  rw [ht]
  exact h

theorem hasDerivAt_log_cosh_aux (x : ℝ) :
    HasDerivAt (fun y : ℝ => 2 * Real.log (Real.cosh y) - y * Real.tanh y)
      (Real.tanh x - x * (1 / (Real.cosh x) ^ 2)) x := by
  have hlog := (Real.hasDerivAt_cosh x).log (Real.cosh_pos x).ne'
  rw [← Real.tanh_eq_sinh_div_cosh] at hlog
  have hprod := (hasDerivAt_id x).mul (hasDerivAt_real_tanh x)
  have h := hlog.const_mul 2 |>.sub hprod
  have heq : 2 * Real.tanh x - (1 * Real.tanh x + id x * (1 / Real.cosh x ^ 2)) =
      Real.tanh x - x * (1 / Real.cosh x ^ 2) := by
    dsimp [id]
    ring
  rw [heq] at h
  convert h using 1
  ext y
  simp

/-- The numerator-sign lemma behind strict decrease of the quadratic density. -/
theorem log_cosh_aux_pos {x : ℝ} (hx : 0 < x) :
    0 < 2 * Real.log (Real.cosh x) - x * Real.tanh x := by
  let F : ℝ → ℝ := fun y => 2 * Real.log (Real.cosh y) - y * Real.tanh y
  have hcont : Continuous F := by
    rw [continuous_iff_continuousAt]
    intro y
    exact (hasDerivAt_log_cosh_aux y).continuousAt
  have hmono : StrictMonoOn F (Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0) hcont.continuousOn
    intro y hy
    rw [interior_Ici, mem_Ioi] at hy
    rw [(hasDerivAt_log_cosh_aux y).deriv]
    have hysinh : y < Real.sinh y := Real.self_lt_sinh_iff.mpr hy
    have hysinhpos : 0 < Real.sinh y := Real.sinh_pos_iff.mpr hy
    have hycosh : 1 < Real.cosh y := Real.one_lt_cosh.mpr hy.ne'
    have hcpos : 0 < Real.cosh y := Real.cosh_pos y
    have hprod : y < Real.sinh y * Real.cosh y := by
      apply hysinh.trans
      nlinarith
    have heq : Real.tanh y - y * (1 / (Real.cosh y) ^ 2) =
        (Real.sinh y * Real.cosh y - y) / (Real.cosh y) ^ 2 := by
      rw [Real.tanh_eq_sinh_div_cosh]
      field_simp
    change 0 < Real.tanh y - y * (1 / (Real.cosh y) ^ 2)
    rw [heq]
    exact div_pos (sub_pos.mpr hprod) (sq_pos_of_pos hcpos)
  have hlt := hmono (show 0 ∈ Ici (0 : ℝ) by simp)
    (show x ∈ Ici (0 : ℝ) by exact hx.le) hx
  have hzero : F 0 = 0 := by simp [F]
  rw [hzero] at hlt
  exact hlt

theorem hasDerivAt_log_cosh_div_sq (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt (fun y : ℝ => Real.log (Real.cosh y) / y ^ 2)
      ((x * Real.tanh x - 2 * Real.log (Real.cosh x)) / x ^ 3) x := by
  have hlog := (Real.hasDerivAt_cosh x).log (Real.cosh_pos x).ne'
  rw [← Real.tanh_eq_sinh_div_cosh] at hlog
  have h := hlog.div (hasDerivAt_pow 2 x) (pow_ne_zero 2 hx)
  have heq : (Real.tanh x * x ^ 2 - Real.log (Real.cosh x) * (2 * x)) /
      (x ^ 2) ^ 2 = (x * Real.tanh x - 2 * Real.log (Real.cosh x)) / x ^ 3 := by
    field_simp
  norm_num at h
  rw [heq] at h
  exact h

/-- The quadratic density is strictly decreasing on positive arguments. -/
theorem strictAntiOn_log_cosh_div_sq :
    StrictAntiOn (fun x : ℝ => Real.log (Real.cosh x) / x ^ 2) (Ioi 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioi 0)
  · intro x hx
    exact (hasDerivAt_log_cosh_div_sq x hx.ne').continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioi, mem_Ioi] at hx
    rw [(hasDerivAt_log_cosh_div_sq x hx.ne').deriv]
    exact div_neg_of_neg_of_pos (by linarith [log_cosh_aux_pos hx]) (pow_pos hx 3)

/-- The exact square-root density formula, valid at every positive scale and time. -/
theorem ruler_div_eq_half_sqrt_density {a t : ℝ} (ha : 0 < a) (ht : 0 < t) :
    ruler a t / t = (1 / 2) *
      Real.sqrt (Real.log (Real.cosh (a * t / 2)) / (a * t / 2) ^ 2) := by
  unfold ruler
  rw [Real.sqrt_div (Real.log_nonneg (Real.one_le_cosh _)),
    Real.sqrt_sq (by positivity : 0 ≤ a * t / 2)]
  field_simp

/-- The finite unit-time readings form a strictly decreasing family. -/
theorem ruler_one_strictAntiOn : StrictAntiOn (fun a : ℝ => ruler a 1) (Ioi 0) := by
  intro a ha b hb hab
  have ha' : 0 < a / 2 := div_pos ha (by norm_num)
  have hb' : 0 < b / 2 := div_pos hb (by norm_num)
  have hlt : Real.log (Real.cosh (b / 2)) / (b / 2) ^ 2 <
      Real.log (Real.cosh (a / 2)) / (a / 2) ^ 2 := by
    apply strictAntiOn_log_cosh_div_sq ha' hb'
    exact (div_lt_div_iff_of_pos_right (show 0 < (2 : ℝ) by norm_num)).2 hab
  have hnonneg : 0 ≤ Real.log (Real.cosh (b / 2)) / (b / 2) ^ 2 :=
    div_nonneg (Real.log_nonneg (Real.one_le_cosh _)) (sq_nonneg _)
  have hsqrt := Real.sqrt_lt_sqrt hnonneg hlt
  have har : ruler a 1 = (1 / 2) *
      Real.sqrt (Real.log (Real.cosh (a / 2)) / (a / 2) ^ 2) := by
    simpa only [mul_one, div_one] using ruler_div_eq_half_sqrt_density ha zero_lt_one
  have hbr : ruler b 1 = (1 / 2) *
      Real.sqrt (Real.log (Real.cosh (b / 2)) / (b / 2) ^ 2) := by
    simpa only [mul_one, div_one] using ruler_div_eq_half_sqrt_density hb zero_lt_one
  change ruler b 1 < ruler a 1
  rw [har, hbr]
  linarith

/-- Different positive scales have different unit-time readings. -/
theorem ruler_one_ne {a : ℝ} (ha : 0 < a) (hne : a ≠ 1) :
    ruler a 1 ≠ ruler 1 1 := by
  intro heq
  exact hne (ruler_one_strictAntiOn.injOn ha (by simp) heq)

/-- Equality of unit-time readings is equivalent to equality of positive scales. -/
theorem ruler_one_eq_iff {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ruler a 1 = ruler b 1 ↔ a = b := by
  constructor
  · exact ruler_one_strictAntiOn.injOn ha hb
  · intro h
    rw [h]

/-- Every positive scale has the same right-hand infinitesimal ruler slope. -/
theorem ruler_right_slope (a : ℝ) (ha : 0 < a) :
    Tendsto (fun t => ruler a t / t) (𝓝[>] 0) (𝓝 (1 / (2 * Real.sqrt 2))) := by
  have ht : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have hx : Tendsto (fun t : ℝ => a * t / 2) (𝓝[>] 0) (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · convert (ht.const_mul a).div_const 2 using 1
      norm_num
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact div_pos (mul_pos ha ht) (by norm_num)
  have hpunct : 𝓝[>] (0 : ℝ) ≤ 𝓝[≠] 0 := by
    apply nhdsWithin_mono
    intro x hx
    simpa only [mem_compl_iff, mem_singleton_iff] using ne_of_gt hx
  have hdensity : Tendsto (fun x : ℝ => Real.log (Real.cosh x) / x ^ 2)
      (𝓝[>] 0) (𝓝 (1 / 2)) := tendsto_log_cosh_div_sq.mono_left hpunct
  have hlim := ((hdensity.comp hx).sqrt.const_mul (1 / 2))
  have hsqrt : (1 / 2) * Real.sqrt (1 / 2) = 1 / (2 * Real.sqrt 2) := by
    rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1)]
    norm_num
    ring
  simp only [Function.comp_apply] at hlim
  rw [hsqrt] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (ruler_div_eq_half_sqrt_density ha ht).symm

/-- Infinitesimal slopes cannot distinguish any two positive scale parameters. -/
theorem local_slopes_agree {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun t => ruler a t / t) (𝓝[>] 0) (𝓝 (1 / (2 * Real.sqrt 2))) ∧
      Tendsto (fun t => ruler b t / t) (𝓝[>] 0) (𝓝 (1 / (2 * Real.sqrt 2))) :=
  ⟨ruler_right_slope a ha, ruler_right_slope b hb⟩

/-- The local behaviour cannot select `a`, whereas finite readings separate all scales. -/
theorem local_ruler_does_not_fix_ledger {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (Tendsto (fun t => ruler a t / t) (𝓝[>] 0) (𝓝 (1 / (2 * Real.sqrt 2))) ∧
      Tendsto (fun t => ruler b t / t) (𝓝[>] 0) (𝓝 (1 / (2 * Real.sqrt 2)))) ∧
      (a ≠ b → ruler a 1 ≠ ruler b 1) := by
  refine ⟨local_slopes_agree ha hb, ?_⟩
  intro hab heq
  exact hab (ruler_one_strictAntiOn.injOn ha hb heq)


end ElementalPeeling.LoopWall.LocalRuler
