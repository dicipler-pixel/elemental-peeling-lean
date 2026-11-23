/-
VOTKP §19: directed peels, cancellation and the geometry of a retained subspace
(Jeromie Beasley).

* Proposition 19.1 (directed real peel): for positive energies, with no ordering assumed,
  `G = tanh(½ ln(E'/E)) = (E' − E)/(E' + E) ∈ (−1, 1)`; reversing an edge negates both the
  rapidity and `G`; `⊕` is a group law on `(−1, 1)` with identity `0` and inverse `−u`; the
  composite of a whole directed record telescopes to `(E_m − E_0)/(E_m + E_0)`; and a negative
  step shrinks the distance from the origin exactly when `−2r < v < 0`.
* Proposition 19.2 (cancellation defect): traversed length minus endpoint distance is
  `4 min(R₊, R₋)`, zero exactly when all increments share a sign.
* Proposition 19.3 (non-unique Grassmannian lift): the families `H_b = U_b D U_bᵀ` all have the
  spectrum of `D(ρ) = diag(0, e^{2ρ}, e^{2ρ} + e^{4ρ})`, hence the same gaps and gap coordinate
  `tanh ρ`, while the ground projector moves with metric `b²`.
* Proposition 19.4 (route-sensitive lifted bound): `h ≥ a²` gives `𝓛 ≥ a·TV(ρ)`; with the
  spectral weighting `ζ ≥ w* h ρ̇²` and Cauchy–Schwarz, `W ≥ w* 𝓛²/T ≥ w* a² L_rec²/(4T)`.
* §19.6: two distinct gaps carry the same friction weight exactly when `de = 1/τ²`
  (`1` and `4` at `τ = 1/2` both give `4/5`), and equal populations give zero rotation friction.
Developed with AI assistance.
-/
import Mathlib
import VOTKP.Smith

namespace VOTKP.Directed

open Real VOTKP.Smith Matrix

/-! ## 19.2 The directed coordinate and its inverse -/

/-- **Proposition 19.1, the step.** For any positive `a, b`, in either order,
`tanh(½ ln(b/a)) = (b − a)/(b + a)`, which lies in `(−1, 1)`. -/
theorem directed_step (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    tanh (log (b / a) / 2) = (b - a) / (b + a) ∧
      -1 < (b - a) / (b + a) ∧ (b - a) / (b + a) < 1 := by
  have ha0 : a ≠ 0 := ha.ne'
  have hab : 0 < b + a := by linarith
  have hab0 : b + a ≠ 0 := hab.ne'
  refine ⟨?_, ?_, ?_⟩
  · rw [← smith_identity _ (div_pos hb ha)]
    field_simp
    try ring
  · rw [lt_div_iff₀ hab]
    linarith
  · rw [div_lt_one hab]
    linarith

/-- **Proposition 19.1, reversal.** Reversing an edge negates the rapidity and the coordinate. -/
theorem directed_reverse (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    log (a / b) / 2 = -(log (b / a) / 2) ∧ (a - b) / (a + b) = -((b - a) / (b + a)) := by
  constructor
  · rw [log_div ha.ne' hb.ne', log_div hb.ne' ha.ne']
    ring
  · rw [add_comm a b]
    ring

/-- **Proposition 19.1, closure.** On `(−1, 1)` the law `⊕` never divides by zero and stays
inside the interval. -/
theorem oplus_closed (u v : ℝ) (hu : |u| < 1) (hv : |v| < 1) :
    0 < 1 + u * v ∧ |oplus u v| < 1 := by
  rw [abs_lt] at hu hv
  obtain ⟨hu1, hu2⟩ := hu
  obtain ⟨hv1, hv2⟩ := hv
  have hp : 0 < (1 + u) * (1 + v) := mul_pos (by linarith) (by linarith)
  have hm : 0 < (1 - u) * (1 - v) := mul_pos (by linarith) (by linarith)
  have h1 : 0 < 1 + u * v := by nlinarith
  refine ⟨h1, ?_⟩
  rw [oplus, abs_div, abs_of_pos h1, div_lt_one h1, abs_lt]
  constructor <;> nlinarith

/-- **Proposition 19.1, identity and inverse.** `u ⊕ 0 = u` and `u ⊕ (−u) = 0`. -/
theorem oplus_identity_inverse (u : ℝ) : oplus u 0 = u ∧ oplus u (-u) = 0 := by
  constructor <;> simp [oplus]

/-- **Proposition 19.1, the composite.** For any positive record (no ordering assumed) the
`⊕`-sum of its steps, `Γ_{0→m}` (built step by step by `Smith.block_succ`), is
`(E_m − E_0)/(E_m + E_0)`. -/
theorem directed_composite (E : ℕ → ℝ) (hpos : ∀ j, 0 < E j) (m : ℕ) :
    blockΓ E 0 m = (E m - E 0) / (E m + E 0) := by
  have h0 : E 0 ≠ 0 := (hpos 0).ne'
  have hs : E m + E 0 ≠ 0 := by linarith [hpos m, hpos 0]
  rw [block_smith E hpos 0 m, zero_add]
  field_simp
  try ring

/-- **Proposition 19.1, distance.** For initial rapidity `r > 0` and an added `v`, the distance
from the origin shrinks, `|r + v| < r`, exactly when `−2r < v < 0`. -/
theorem shrinks_iff (r v : ℝ) (hr : 0 < r) : |r + v| < r ↔ -2 * r < v ∧ v < 0 := by
  rw [abs_lt]
  constructor
  · rintro ⟨h1, h2⟩
    constructor <;> linarith
  · rintro ⟨h1, h2⟩
    constructor <;> linarith

/-! ## 19.3 Net change does not record the route -/

lemma abs_split (x : ℝ) : |x| = max x 0 + max (-x) 0 := by
  rcases le_total 0 x with h | h
  · rw [abs_of_nonneg h, max_eq_left h, max_eq_right (by linarith : -x ≤ 0)]
    ring
  · rw [abs_of_nonpos h, max_eq_right h, max_eq_left (by linarith : 0 ≤ -x)]
    ring

lemma self_split (x : ℝ) : x = max x 0 - max (-x) 0 := by
  rcases le_total 0 x with h | h
  · rw [max_eq_left h, max_eq_right (by linarith : -x ≤ 0)]
    ring
  · rw [max_eq_right h, max_eq_left (by linarith : 0 ≤ -x)]
    ring

/-- **Proposition 19.2, the cancellation defect.** With `L_rec = 2 Σ|rⱼ|`, `D_end = 2|Σ rⱼ|`,
`R₊ = Σ max(rⱼ, 0)` and `R₋ = Σ max(−rⱼ, 0)`: `L_rec − D_end = 4 min(R₊, R₋)`. -/
theorem cancellation_defect (r : ℕ → ℝ) (n : ℕ) :
    2 * ∑ j ∈ Finset.range n, |r j| - 2 * |∑ j ∈ Finset.range n, r j|
      = 4 * min (∑ j ∈ Finset.range n, max (r j) 0)
          (∑ j ∈ Finset.range n, max (-r j) 0) := by
  have hs1 : ∑ j ∈ Finset.range n, |r j|
      = ∑ j ∈ Finset.range n, max (r j) 0 + ∑ j ∈ Finset.range n, max (-r j) 0 := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => abs_split (r j)
  have hs2 : ∑ j ∈ Finset.range n, r j
      = ∑ j ∈ Finset.range n, max (r j) 0 - ∑ j ∈ Finset.range n, max (-r j) 0 := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => self_split (r j)
  rw [hs1, hs2]
  rcases le_total (∑ j ∈ Finset.range n, max (r j) 0) (∑ j ∈ Finset.range n, max (-r j) 0)
    with h | h
  · rw [abs_of_nonpos (by linarith), min_eq_left h]
    ring
  · rw [abs_of_nonneg (by linarith), min_eq_right h]
    ring

/-- **Proposition 19.2, equality.** Length equals endpoint distance exactly when all increments
have the same sign. -/
theorem no_defect_iff (r : ℕ → ℝ) (n : ℕ) :
    2 * ∑ j ∈ Finset.range n, |r j| = 2 * |∑ j ∈ Finset.range n, r j| ↔
      (∀ j ∈ Finset.range n, r j ≤ 0) ∨ (∀ j ∈ Finset.range n, 0 ≤ r j) := by
  have hd := cancellation_defect r n
  have hP0 : 0 ≤ ∑ j ∈ Finset.range n, max (r j) 0 :=
    Finset.sum_nonneg fun j _ => le_max_right _ _
  have hM0 : 0 ≤ ∑ j ∈ Finset.range n, max (-r j) 0 :=
    Finset.sum_nonneg fun j _ => le_max_right _ _
  have hPz : ∑ j ∈ Finset.range n, max (r j) 0 = 0 ↔ ∀ j ∈ Finset.range n, r j ≤ 0 := by
    rw [Finset.sum_eq_zero_iff_of_nonneg fun j _ => le_max_right _ _]
    exact forall₂_congr fun j _ => max_eq_right_iff
  have hMz : ∑ j ∈ Finset.range n, max (-r j) 0 = 0 ↔ ∀ j ∈ Finset.range n, 0 ≤ r j := by
    rw [Finset.sum_eq_zero_iff_of_nonneg fun j _ => le_max_right _ _]
    exact forall₂_congr fun j _ => by rw [max_eq_right_iff, neg_nonpos]
  constructor
  · intro heq
    have hmin : min (∑ j ∈ Finset.range n, max (r j) 0)
        (∑ j ∈ Finset.range n, max (-r j) 0) = 0 := by linarith
    rcases le_total (∑ j ∈ Finset.range n, max (r j) 0)
      (∑ j ∈ Finset.range n, max (-r j) 0) with h | h
    · rw [min_eq_left h] at hmin
      exact Or.inl (hPz.mp hmin)
    · rw [min_eq_right h] at hmin
      exact Or.inr (hMz.mp hmin)
  · rintro (h | h)
    · have hz := hPz.mpr h
      have hmin : min (∑ j ∈ Finset.range n, max (r j) 0)
          (∑ j ∈ Finset.range n, max (-r j) 0) = 0 := by
        rw [hz]
        exact min_eq_left hM0
      linarith
    · have hz := hMz.mpr h
      have hmin : min (∑ j ∈ Finset.range n, max (r j) 0)
          (∑ j ∈ Finset.range n, max (-r j) 0) = 0 := by
        rw [hz]
        exact min_eq_right hP0
      linarith

/-- **Proposition 19.2, the example.** `r₀ = 0.4`, `r₁ = −0.4`: endpoint distance `0`,
traversed length `1.6`. -/
theorem out_and_back :
    2 * |∑ j ∈ Finset.range 2, (if j = 0 then (0.4 : ℝ) else -0.4)| = 0 ∧
      2 * ∑ j ∈ Finset.range 2, |(if j = 0 then (0.4 : ℝ) else -0.4)| = 1.6 := by
  constructor <;> norm_num [Finset.sum_range_succ]

/-! ## 19.4 The scalar record does not fix the projector geometry -/

/-- `D(ρ) = diag(0, e^{2ρ}, e^{2ρ} + e^{4ρ})`: adjacent gaps `e^{2ρ}` and `e^{4ρ}`. -/
noncomputable def Dlad (ρ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.diagonal ![0, exp (2 * ρ), exp (2 * ρ) + exp (4 * ρ)]

/-- Rotation of modes `0` and `1` by `θ`, mode `2` fixed. -/
noncomputable def rot (θ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![cos θ, -sin θ, 0; sin θ, cos θ, 0; 0, 0, 1]

/-- The lifted family `H_b(ρ) = U_b(ρ) D(ρ) U_b(ρ)ᵀ`, `U_b(ρ)` the rotation by `bρ`. -/
noncomputable def Hlift (b ρ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  rot (b * ρ) * Dlad ρ * (rot (b * ρ))ᵀ

/-- The ground direction `U_b(ρ) e₀ = (cos bρ, sin bρ, 0)`. -/
noncomputable def gvec (b ρ : ℝ) : Fin 3 → ℝ := ![cos (b * ρ), sin (b * ρ), 0]

/-- Its `ρ`-derivative. -/
noncomputable def gvec' (b ρ : ℝ) : Fin 3 → ℝ := ![-sin (b * ρ) * b, cos (b * ρ) * b, 0]

lemma rot_orth (θ : ℝ) : (rot θ)ᵀ * rot θ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rot, Matrix.mul_apply, Fin.sum_univ_three] <;>
    first
    | linear_combination Real.cos_sq_add_sin_sq θ
    | ring

/-- **Proposition 19.3, the spectrum.** Every lift has the characteristic polynomial of `D(ρ)`:
the same eigenvalues, gaps and gap coordinate, for every `b`. -/
theorem lift_isospectral (b ρ : ℝ) : (Hlift b ρ).charpoly = (Dlad ρ).charpoly := by
  unfold Hlift
  rw [mul_assoc, Matrix.charpoly_mul_comm, mul_assoc, rot_orth, mul_one]

/-- **Proposition 19.3, the gap coordinate.** `tanh(½ ln(d₂/d₁)) = tanh ρ` for `d₁ = e^{2ρ}`,
`d₂ = e^{4ρ}`. -/
theorem gap_coordinate (ρ : ℝ) : tanh (log (exp (4 * ρ) / exp (2 * ρ)) / 2) = tanh ρ := by
  rw [← exp_sub, log_exp]
  congr 1
  ring

/-- **Proposition 19.3, the ground state.** `(cos bρ, sin bρ, 0)` is a unit vector annihilated by
`H_b(ρ)`; since `0 < e^{2ρ}` the other eigenvalues are positive, so it spans the ground space. -/
theorem lift_ground (b ρ : ℝ) :
    Hlift b ρ *ᵥ gvec b ρ = 0 ∧ ∑ i, gvec b ρ i ^ 2 = 1 := by
  constructor
  · have h1 : (rot (b * ρ))ᵀ *ᵥ gvec b ρ = ![1, 0, 0] := by
      ext i
      fin_cases i <;>
        simp [rot, gvec, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;>
        first
        | linear_combination Real.cos_sq_add_sin_sq (b * ρ)
        | ring
    have h2 : Dlad ρ *ᵥ ![1, 0, 0] = 0 := by
      ext i
      fin_cases i <;> simp [Dlad, Matrix.mulVec_diagonal]
    unfold Hlift
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h1, h2, Matrix.mulVec_zero]
  · simp [gvec, Fin.sum_univ_three]

lemma gvec_deriv (b ρ : ℝ) (i : Fin 3) :
    HasDerivAt (fun ρ => gvec b ρ i) (gvec' b ρ i) ρ := by
  have hθ : HasDerivAt (fun ρ : ℝ => b * ρ) b ρ := by
    simpa using (hasDerivAt_id' (x := ρ)).const_mul b
  fin_cases i
  · exact hθ.cos
  · exact hθ.sin
  · exact hasDerivAt_const (x := ρ) (c := (0 : ℝ))

/-- The ground projector `P = v vᵀ` has entrywise derivative `v' vᵀ + v v'ᵀ`. -/
theorem projector_deriv (b ρ : ℝ) (i j : Fin 3) :
    HasDerivAt (fun ρ => gvec b ρ i * gvec b ρ j)
      (gvec' b ρ i * gvec b ρ j + gvec b ρ i * gvec' b ρ j) ρ :=
  (gvec_deriv b ρ i).fun_mul (gvec_deriv b ρ j)

/-- **Proposition 19.3, the metric.** `½ Tr((∂_ρ P_b)²) = b²` for every `ρ`: the lift moves at
speed `|b|`, so `𝓛_b = |b| ∫ |ρ̇| dt`, while the spectrum does not depend on `b`. -/
theorem lift_metric (b ρ : ℝ) :
    (1 / 2) * ∑ i, ∑ j, (gvec' b ρ i * gvec b ρ j + gvec b ρ i * gvec' b ρ j) ^ 2 = b ^ 2 := by
  simp [Fin.sum_univ_three, gvec, gvec']
  linear_combination (b ^ 2 * (sin (b * ρ) ^ 2 + cos (b * ρ) ^ 2 + 1))
    * Real.sin_sq_add_cos_sq (b * ρ)

/-- **Proposition 19.3.** The constant lift (`b = 0`) and a rotating lift (`b ≠ 0`) share the
spectrum, yet one projector is stationary and the other moves. -/
theorem nonunique_lift (b ρ : ℝ) (hb : b ≠ 0) :
    (Hlift 0 ρ).charpoly = (Hlift b ρ).charpoly ∧
      (1 / 2) * ∑ i, ∑ j, (gvec' 0 ρ i * gvec 0 ρ j + gvec 0 ρ i * gvec' 0 ρ j) ^ 2 = 0 ∧
      0 < (1 / 2) * ∑ i, ∑ j, (gvec' b ρ i * gvec b ρ j + gvec b ρ i * gvec' b ρ j) ^ 2 := by
  refine ⟨by rw [lift_isospectral, lift_isospectral], ?_, ?_⟩
  · rw [lift_metric]
    ring
  · rw [lift_metric]
    positivity

/-! ## 19.5 A conditional bridge that does hold -/

/-- **Proposition 19.4, the length.** If the pullback metric obeys `h ≥ a²` along the route,
the lifted length `𝓛 = ∫ √h |ρ̇|` is at least `a · TV(ρ) = (a/2) L_rec`. -/
theorem lifted_length_bound (a T : ℝ) (hT : 0 ≤ T) (ha : 0 ≤ a) (ρ' h : ℝ → ℝ)
    (hρ : Continuous ρ') (hh : Continuous h) (hbound : ∀ t, a ^ 2 ≤ h t) :
    a * ∫ t in (0 : ℝ)..T, |ρ' t| ≤ ∫ t in (0 : ℝ)..T, √(h t) * |ρ' t| := by
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_mono_on hT ?_ ?_ (fun t _ => ?_)
  · exact (continuous_const.mul hρ.abs).intervalIntegrable _ _
  · exact (hh.sqrt.mul hρ.abs).intervalIntegrable _ _
  · have hle : a ≤ √(h t) := by
      have := Real.abs_le_sqrt (hbound t)
      rwa [abs_of_nonneg ha] at this
    exact mul_le_mul_of_nonneg_right hle (abs_nonneg _)

/-- Cauchy–Schwarz on `[0, T]`: `(∫ f)² ≤ T ∫ f²`. -/
theorem sq_integral_le (f : ℝ → ℝ) (hf : Continuous f) (T : ℝ) (hT : 0 < T) :
    (∫ t in (0 : ℝ)..T, f t) ^ 2 ≤ T * ∫ t in (0 : ℝ)..T, f t ^ 2 := by
  have hT0 : T ≠ 0 := hT.ne'
  have hnn : 0 ≤ ∫ t in (0 : ℝ)..T, (f t - (∫ s in (0 : ℝ)..T, f s) / T) ^ 2 :=
    intervalIntegral.integral_nonneg hT.le (fun t _ => sq_nonneg _)
  have e : ∀ t, (f t - (∫ s in (0 : ℝ)..T, f s) / T) ^ 2
      = (f t ^ 2 - (2 * ((∫ s in (0 : ℝ)..T, f s) / T)) * f t)
        + ((∫ s in (0 : ℝ)..T, f s) / T) ^ 2 := fun t => by ring
  simp_rw [e] at hnn
  have i1 : IntervalIntegrable (fun t => f t ^ 2) MeasureTheory.volume 0 T :=
    (hf.pow 2).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun t => (2 * ((∫ s in (0 : ℝ)..T, f s) / T)) * f t)
      MeasureTheory.volume 0 T := (continuous_const.mul hf).intervalIntegrable _ _
  have i12 : IntervalIntegrable
      (fun t => f t ^ 2 - (2 * ((∫ s in (0 : ℝ)..T, f s) / T)) * f t)
      MeasureTheory.volume 0 T :=
    ((hf.pow 2).sub (continuous_const.mul hf)).intervalIntegrable _ _
  have i3 : IntervalIntegrable
      (fun _ : ℝ => ((∫ s in (0 : ℝ)..T, f s) / T) ^ 2) MeasureTheory.volume 0 T :=
    continuous_const.intervalIntegrable _ _
  rw [intervalIntegral.integral_add i12 i3, intervalIntegral.integral_sub i1 i2,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const, sub_zero,
    smul_eq_mul] at hnn
  have key : (∫ t in (0 : ℝ)..T, f t ^ 2)
      - 2 * ((∫ s in (0 : ℝ)..T, f s) / T) * (∫ t in (0 : ℝ)..T, f t)
      + T * ((∫ s in (0 : ℝ)..T, f s) / T) ^ 2
      = (∫ t in (0 : ℝ)..T, f t ^ 2) - (∫ t in (0 : ℝ)..T, f t) ^ 2 / T := by
    field_simp
    try ring
  have h3 : (∫ t in (0 : ℝ)..T, f t) ^ 2 / T ≤ ∫ t in (0 : ℝ)..T, f t ^ 2 := by
    linarith [hnn, key]
  rw [div_le_iff₀ hT] at h3
  linarith

/-- The finite spectral-weighting step: if every active weight is at least `w*`, then
`ζ = Σ wₙ cₙ ≥ w* Σ cₙ = w* h` for nonnegative couplings `cₙ = |⟨n|∂0⟩|²`. -/
theorem spectral_weighting {ι : Type*} (s : Finset ι) (w c : ι → ℝ) (wstar : ℝ)
    (hc : ∀ n ∈ s, 0 ≤ c n) (hw : ∀ n ∈ s, wstar ≤ w n) :
    wstar * ∑ n ∈ s, c n ≤ ∑ n ∈ s, w n * c n := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun n hn => mul_le_mul_of_nonneg_right (hw n hn) (hc n hn)

/-- **Proposition 19.4, the work bound.** With `h ≥ a²` along the route and the leading
excess-work density bounded below by `w* h ρ̇²`, the leading excess work obeys
`W ≥ w* 𝓛²/T ≥ w* a² L_rec²/(4T)`, `L_rec = 2 ∫|ρ̇|`. -/
theorem route_cost (ζ h ρ' : ℝ → ℝ) (T a wstar : ℝ) (hT : 0 < T) (ha : 0 ≤ a)
    (hw : 0 ≤ wstar) (hρ : Continuous ρ') (hh : Continuous h) (hζc : Continuous ζ)
    (hbound : ∀ t, a ^ 2 ≤ h t) (hζ : ∀ t, wstar * (h t * ρ' t ^ 2) ≤ ζ t) :
    wstar * (∫ t in (0 : ℝ)..T, √(h t) * |ρ' t|) ^ 2 / T ≤ ∫ t in (0 : ℝ)..T, ζ t ∧
      wstar * a ^ 2 * (2 * ∫ t in (0 : ℝ)..T, |ρ' t|) ^ 2 / (4 * T)
        ≤ ∫ t in (0 : ℝ)..T, ζ t := by
  have hh0 : ∀ t, 0 ≤ h t := fun t => le_trans (sq_nonneg a) (hbound t)
  have hfc : Continuous fun t => √(h t) * |ρ' t| := hh.sqrt.mul hρ.abs
  have hsq : ∀ t, (√(h t) * |ρ' t|) ^ 2 = h t * ρ' t ^ 2 := fun t => by
    rw [mul_pow, Real.sq_sqrt (hh0 t), sq_abs]
  have hCS := sq_integral_le _ hfc T hT
  simp_rw [hsq] at hCS
  have hW : wstar * ∫ t in (0 : ℝ)..T, h t * ρ' t ^ 2 ≤ ∫ t in (0 : ℝ)..T, ζ t := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_mono_on hT.le
      ((continuous_const.mul (hh.mul (hρ.pow 2))).intervalIntegrable _ _)
      (hζc.intervalIntegrable _ _) (fun t _ => hζ t)
  have hfirst : wstar * (∫ t in (0 : ℝ)..T, √(h t) * |ρ' t|) ^ 2 / T
      ≤ ∫ t in (0 : ℝ)..T, ζ t := by
    rw [div_le_iff₀ hT]
    calc wstar * (∫ t in (0 : ℝ)..T, √(h t) * |ρ' t|) ^ 2
        ≤ wstar * (T * ∫ t in (0 : ℝ)..T, h t * ρ' t ^ 2) :=
          mul_le_mul_of_nonneg_left hCS hw
      _ = (wstar * ∫ t in (0 : ℝ)..T, h t * ρ' t ^ 2) * T := by ring
      _ ≤ (∫ t in (0 : ℝ)..T, ζ t) * T := mul_le_mul_of_nonneg_right hW hT.le
  refine ⟨hfirst, ?_⟩
  have hL := lifted_length_bound a T hT.le ha ρ' h hρ hh hbound
  have hTV : 0 ≤ ∫ t in (0 : ℝ)..T, |ρ' t| :=
    intervalIntegral.integral_nonneg hT.le (fun t _ => abs_nonneg _)
  have hsq' : (a * ∫ t in (0 : ℝ)..T, |ρ' t|) ^ 2
      ≤ (∫ t in (0 : ℝ)..T, √(h t) * |ρ' t|) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg ha hTV) hL 2
  calc wstar * a ^ 2 * (2 * ∫ t in (0 : ℝ)..T, |ρ' t|) ^ 2 / (4 * T)
      = wstar * (a * ∫ t in (0 : ℝ)..T, |ρ' t|) ^ 2 / T := by
        have hT0 : T ≠ 0 := hT.ne'
        field_simp
        try ring
    _ ≤ wstar * (∫ t in (0 : ℝ)..T, √(h t) * |ρ' t|) ^ 2 / T :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsq' hw) hT.le
    _ ≤ ∫ t in (0 : ℝ)..T, ζ t := hfirst

/-! ## 19.6 The saturation condition -/

/-- The zero-temperature friction weight `w(Δ) = 2τΔ/(1 + τ²Δ²)` (coherent precession). -/
noncomputable def wgt (τ d : ℝ) : ℝ := 2 * τ * d / (1 + τ ^ 2 * d ^ 2)

/-- **§19.6.** Two distinct positive gaps carry the same weight exactly when `de = 1/τ²`. -/
theorem equal_weights_iff (τ d e : ℝ) (hτ : 0 < τ) (hd : 0 < d) (he : 0 < e) (hde : d ≠ e) :
    wgt τ d = wgt τ e ↔ d * e = 1 / τ ^ 2 := by
  unfold wgt
  have h1 : 0 < 1 + τ ^ 2 * d ^ 2 := by positivity
  have h2 : 0 < 1 + τ ^ 2 * e ^ 2 := by positivity
  rw [div_eq_div_iff h1.ne' h2.ne', eq_div_iff (by positivity)]
  have hfac : 2 * τ * d * (1 + τ ^ 2 * e ^ 2) - 2 * τ * e * (1 + τ ^ 2 * d ^ 2)
      = 2 * τ * (d - e) * (1 - τ ^ 2 * d * e) := by ring
  constructor
  · intro h
    have h0 : 2 * τ * (d - e) * (1 - τ ^ 2 * d * e) = 0 := by rw [← hfac]; linarith
    have hne : 2 * τ * (d - e) ≠ 0 := mul_ne_zero (by positivity) (sub_ne_zero.mpr hde)
    have h3 := (mul_eq_zero.mp h0).resolve_left hne
    linarith
  · intro h
    have h' : 1 - τ ^ 2 * d * e = 0 := by linarith
    have h0 : 2 * τ * d * (1 + τ ^ 2 * e ^ 2) - 2 * τ * e * (1 + τ ^ 2 * d ^ 2) = 0 := by
      rw [hfac, h', mul_zero]
    linarith

/-- **§19.6, the example.** At `τ = 1/2` the gaps `1` and `4` both carry weight `4/5`. -/
theorem weights_one_four : wgt (1 / 2) 1 = 4 / 5 ∧ wgt (1 / 2) 4 = 4 / 5 := by
  constructor <;> norm_num [wgt]

/-- The rotational friction weight of a pair, `2τ(p_m − p_n)Δ/(1 + (τΔ)²)`. -/
noncomputable def pairFriction (τ pm pn Δ : ℝ) : ℝ := 2 * τ * (pm - pn) * Δ / (1 + (τ * Δ) ^ 2)

/-- **§19.6, RP-RANK.** A pair with equal populations contributes no rotation friction, however
the retained projector moves. -/
theorem equal_populations_no_friction (τ p Δ : ℝ) : pairFriction τ p p Δ = 0 := by
  simp [pairFriction]

end VOTKP.Directed
