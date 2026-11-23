/-
VOTKP v1.1, Section 5: finite peel theorems, and the reduced-product associator of §15.2.

* 5.1 Positive-channel peel: for `G = Σ wᵢ vᵢvᵢᵀ` the form is `xᵀGx = Σ wᵢ (vᵢ·x)²`; lowering
  weights (`0 ≤ w' ≤ w`) lowers the form, keeps it nonnegative, and `ker G ⊆ ker G'`.
* 5.2 Form tomography: `G_jk = ½[Q(e_j + e_k) − Q(e_j) − Q(e_k)]` for symmetric `G`.
* 5.3 Schur boundary memory: eliminating the hidden layer leaves `(z − A − B(z − D)⁻¹C)x = f`.
* 5.6 Four-reading certificate, per channel: the four readings give the coefficient
  `c = 2Δ³/((Δ² − y₁)(Δ² − y₂))`, positive when both probes lie below the pole and negative
  when the pole lies between them.
* 5.7 Phase reference: `z = (I₀⁺ − I₀⁻)/(4a) + i (I₉₀⁺ − I₉₀⁻)/(4a)`, and reading errors of size
  at most `ε` give `|error|² ≤ ε²/(2a²)`, i.e. `|error| ≤ ε/(√2 a)`.
* 5.8 Cumulants: `{1/5, 1/2, 4/5}` and `{3/10, (6 ± √6)/10}` share `c₁ = 3/2` and `c₂ = 57/100`
  but have `c₃ = 0` and `3/50`.
* 5.9 The reduced-record bound, its witness: `T_s(x) = (x − s)²/(x⁴ − 2sx³ + 2)` equals
  `1/(1 + (x − Σ_s)²)` with `Σ_s = 1/(x − s)`; both signs give `T(0) = T(√2) = 1/2`; at `x = 1`
  they give `0` and `4/5`; at `x = 1/10` they differ by `79,600,000/400,039,601`.
* 5.10 One-energy snapshots: `Σ_λ(E) = cλ/(E − λ)` has `Σ_λ(0) = −c` for every `λ` but
  derivative `−c/λ` there.
* §15.2: for a reduced product `x ⋆ y = P(xy)`,
  `(x ⋆ y) ⋆ z − x ⋆ (y ⋆ z) = P(x(I − P)(yz) − (I − P)(xy)z)`.
-/
import Mathlib

namespace VOTKP.Peel

open Matrix

/-! ## 5.1 Positive-channel peel -/

variable {n ι : Type*} [Fintype n] [Fintype ι]

/-- `G x = Σ wᵢ (vᵢ·x) vᵢ`, the action of `G = Σ wᵢ vᵢvᵢᵀ`. -/
def Gop (w : ι → ℝ) (v : ι → n → ℝ) (x : n → ℝ) : n → ℝ := ∑ i, (w i * (v i ⬝ᵥ x)) • v i

/-- The form of a positive-channel sum: `xᵀGx = Σ wᵢ (vᵢ·x)²`. -/
theorem quad_form (w : ι → ℝ) (v : ι → n → ℝ) (x : n → ℝ) :
    x ⬝ᵥ Gop w v x = ∑ i, w i * (v i ⬝ᵥ x) ^ 2 := by
  unfold Gop
  rw [dotProduct_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [dotProduct_smul, smul_eq_mul, dotProduct_comm]
  ring

/-- **5.1.** Lowering the weights lowers the form: `0 ⪯ G' ⪯ G`. -/
theorem peel_lowers (w w' : ι → ℝ) (v : ι → n → ℝ) (h0 : ∀ i, 0 ≤ w' i) (h : ∀ i, w' i ≤ w i)
    (x : n → ℝ) : 0 ≤ x ⬝ᵥ Gop w' v x ∧ x ⬝ᵥ Gop w' v x ≤ x ⬝ᵥ Gop w v x := by
  rw [quad_form, quad_form]
  exact ⟨Finset.sum_nonneg (fun i _ => mul_nonneg (h0 i) (sq_nonneg _)),
    Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (h i) (sq_nonneg _))⟩

/-- **5.1, kernels.** `ker G ⊆ ker G'`: a direction the peel had already silenced stays
silent. -/
theorem peel_kernel (w w' : ι → ℝ) (v : ι → n → ℝ) (h0 : ∀ i, 0 ≤ w' i) (h : ∀ i, w' i ≤ w i)
    (x : n → ℝ) (hx : Gop w v x = 0) : Gop w' v x = 0 := by
  have hw : ∀ i, 0 ≤ w i := fun i => (h0 i).trans (h i)
  have hq : ∑ i, w i * (v i ⬝ᵥ x) ^ 2 = 0 := by rw [← quad_form, hx, dotProduct_zero]
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => mul_nonneg (hw i) (sq_nonneg _))] at hq
  unfold Gop
  refine Finset.sum_eq_zero (fun i hi => ?_)
  rcases mul_eq_zero.mp (hq i hi) with h1 | h1
  · have : w' i = 0 := le_antisymm (h1 ▸ h i) (h0 i)
    simp [this]
  · have : v i ⬝ᵥ x = 0 := pow_eq_zero_iff (two_ne_zero) |>.mp h1
    simp [this]

/-! ## 5.2 Form tomography -/

/-- The quadratic form `Q(u) = uᵀGu`. -/
def Q (G : Matrix n n ℝ) (u : n → ℝ) : ℝ := u ⬝ᵥ G *ᵥ u

/-- **5.2.** A symmetric form is recovered from basis and pair-sum readings. -/
theorem form_tomography [DecidableEq n] (G : Matrix n n ℝ) (hG : Gᵀ = G) (j k : n) :
    G j k = (Q G (Pi.single j 1 + Pi.single k 1) - Q G (Pi.single j 1) - Q G (Pi.single k 1)) / 2 := by
  have sym : Pi.single k (1 : ℝ) ⬝ᵥ G *ᵥ Pi.single j 1 = Pi.single j 1 ⬝ᵥ G *ᵥ Pi.single k 1 := by
    rw [dotProduct_mulVec, dotProduct_comm]
    conv_rhs => rw [← hG, mulVec_transpose]
  have e : Pi.single j (1 : ℝ) ⬝ᵥ G *ᵥ Pi.single k 1 = G j k := by
    rw [mulVec_single_one, single_dotProduct, one_mul, Matrix.col_apply]
  unfold Q
  rw [mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct, sym, e]
  ring

/-! ## 5.3 Schur boundary memory -/

/-- **5.3.** If `(z − A)x − By = f` and `−Cx + (z − D)y = 0` with `M(z − D) = 1`, then the
retained equation is `(z − A − BMC)x = f`: the hidden layer survives as the self-energy `BMC`. -/
theorem schur_memory {m k : Type*} [Fintype m] [Fintype k] [DecidableEq k] (A : Matrix m m ℝ) (B : Matrix m k ℝ)
    (C : Matrix k m ℝ) (Dz M : Matrix k k ℝ) (hM : M * Dz = 1) (Az : Matrix m m ℝ) (x f : m → ℝ)
    (y : k → ℝ) (h1 : Az *ᵥ x - B *ᵥ y = f) (h2 : -(C *ᵥ x) + Dz *ᵥ y = 0) :
    (Az - B * M * C) *ᵥ x = f := by
  have hy : y = M *ᵥ (C *ᵥ x) := by
    have e : Dz *ᵥ y = C *ᵥ x := by linear_combination h2
    calc y = (M * Dz) *ᵥ y := by rw [hM, one_mulVec]
      _ = M *ᵥ (Dz *ᵥ y) := by rw [mulVec_mulVec]
      _ = M *ᵥ (C *ᵥ x) := by rw [e]
  rw [sub_mulVec, ← h1, hy, mulVec_mulVec, mulVec_mulVec]

/-! ## 5.6 The four-reading certificate, one channel -/

/-- **5.6, the coefficient.** For one channel with pole `Δ² ≠ y₁, y₂` and `y₁ ≠ y₂`, the four
readings combine to `c · (s − s')` with `c = 2Δ³/((Δ² − y₁)(Δ² − y₂))`. -/
theorem four_reading (d y1 y2 s s' : ℝ) (h1 : d ^ 2 - y1 ≠ 0) (h2 : d ^ 2 - y2 ≠ 0)
    (h12 : y2 - y1 ≠ 0) :
    (2 * d ^ 3 * s / (d ^ 2 - y2) - 2 * d ^ 3 * s / (d ^ 2 - y1) - 2 * d ^ 3 * s' / (d ^ 2 - y2)
        + 2 * d ^ 3 * s' / (d ^ 2 - y1)) / (y2 - y1) =
      2 * d ^ 3 / ((d ^ 2 - y1) * (d ^ 2 - y2)) * (s - s') := by
  field_simp
  ring

/-- Both probes below the pole: the coefficient is positive. -/
theorem coeff_pos_below (d y1 y2 : ℝ) (hd : 0 < d) (h1 : y1 < d ^ 2) (h2 : y2 < d ^ 2) :
    0 < 2 * d ^ 3 / ((d ^ 2 - y1) * (d ^ 2 - y2)) := by
  apply div_pos (by positivity)
  exact mul_pos (by linarith) (by linarith)

/-- The pole between the probes: the coefficient is negative, which is why the side condition
is needed. -/
theorem coeff_neg_between (d y1 y2 : ℝ) (hd : 0 < d) (h1 : y1 < d ^ 2) (h2 : d ^ 2 < y2) :
    2 * d ^ 3 / ((d ^ 2 - y1) * (d ^ 2 - y2)) < 0 := by
  apply div_neg_of_pos_of_neg (by positivity)
  exact mul_neg_of_pos_of_neg (by linarith) (by linarith)

/-! ## 5.7 Phase reference -/

open Complex in
/-- **5.7, real part.** `Re z = (|z + a|² − |z − a|²)/(4a)` for a real reference `a ≠ 0`. -/
theorem phase_reference_re (z : ℂ) (a : ℝ) (ha : a ≠ 0) :
    z.re = (normSq (z + a) - normSq (z - a)) / (4 * a) := by
  simp only [normSq_apply, add_re, add_im, sub_re, sub_im, ofReal_re, ofReal_im]
  field_simp
  ring

open Complex in
/-- **5.7, imaginary part.** `Im z = (|z + ia|² − |z − ia|²)/(4a)`, so the four readings
`I₀^± = |z ± a|²` and `I₉₀^± = |z ± ia|²` recover `z`. -/
theorem phase_reference_im (z : ℂ) (a : ℝ) (ha : a ≠ 0) :
    z.im = (normSq (z + a * I) - normSq (z - a * I)) / (4 * a) := by
  simp only [normSq_apply, add_re, add_im, sub_re, sub_im, mul_re, mul_im, ofReal_re, ofReal_im,
    I_re, I_im]
  field_simp
  ring

/-- **5.7, the error bound.** If each of the four readings is off by at most `ε`, the recovered
value is off by `e` with `|e|² ≤ ε²/(2a²)`, i.e. `|e| ≤ ε/(√2 a)`. -/
theorem phase_error (a ε d1 d2 d3 d4 : ℝ) (ha : 0 < a) (h1 : |d1| ≤ ε) (h2 : |d2| ≤ ε)
    (h3 : |d3| ≤ ε) (h4 : |d4| ≤ ε) :
    ((d1 - d2) / (4 * a)) ^ 2 + ((d3 - d4) / (4 * a)) ^ 2 ≤ ε ^ 2 / (2 * a ^ 2) := by
  obtain ⟨a1, b1⟩ := abs_le.mp h1
  obtain ⟨a2, b2⟩ := abs_le.mp h2
  obtain ⟨a3, b3⟩ := abs_le.mp h3
  obtain ⟨a4, b4⟩ := abs_le.mp h4
  have s1 : (d1 - d2) ^ 2 ≤ (2 * ε) ^ 2 := sq_le_sq' (by linarith) (by linarith)
  have s2 : (d3 - d4) ^ 2 ≤ (2 * ε) ^ 2 := sq_le_sq' (by linarith) (by linarith)
  have ha2 : (0 : ℝ) ≤ 2 * a ^ 2 := by positivity
  rw [div_pow, div_pow, ← add_div, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_right (add_le_add s1 s2) ha2]

/-! ## 5.8 Cumulants -/

/-- The power sums `p_k = a^k + b^k + c^k`. -/
def pw (k : ℕ) (a b c : ℝ) : ℝ := a ^ k + b ^ k + c ^ k

/-- **5.8.** Conductance and Fano factor do not fix the channels: `{1/5, 1/2, 4/5}` and
`{3/10, (6 + √6)/10, (6 − √6)/10}` share `c₁ = 3/2` and `c₂ = p₁ − p₂ = 57/100`, but
`c₃ = p₁ − 3p₂ + 2p₃` is `0` against `3/50`. -/
theorem cumulant_witness :
    pw 1 (1 / 5) (1 / 2) (4 / 5) = 3 / 2 ∧
      pw 1 (3 / 10) ((6 + √6) / 10) ((6 - √6) / 10) = 3 / 2 ∧
      pw 1 (1 / 5) (1 / 2) (4 / 5) - pw 2 (1 / 5) (1 / 2) (4 / 5) = 57 / 100 ∧
      pw 1 (3 / 10) ((6 + √6) / 10) ((6 - √6) / 10) -
        pw 2 (3 / 10) ((6 + √6) / 10) ((6 - √6) / 10) = 57 / 100 ∧
      pw 1 (1 / 5) (1 / 2) (4 / 5) - 3 * pw 2 (1 / 5) (1 / 2) (4 / 5) +
        2 * pw 3 (1 / 5) (1 / 2) (4 / 5) = 0 ∧
      pw 1 (3 / 10) ((6 + √6) / 10) ((6 - √6) / 10) -
        3 * pw 2 (3 / 10) ((6 + √6) / 10) ((6 - √6) / 10) +
        2 * pw 3 (3 / 10) ((6 + √6) / 10) ((6 - √6) / 10) = 3 / 50 := by
  have hr : √6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  unfold pw
  refine ⟨by norm_num, by ring, by norm_num, ?_, by norm_num, ?_⟩
  · linear_combination (-2 / 100 : ℝ) * hr
  · linear_combination (12 / 1000 : ℝ) * hr

/-! ## 5.9 The reduced-record impossibility bound: the witness -/

/-- The transmission through the first site when the second is hidden. -/
noncomputable def T (s x : ℝ) : ℝ := (x - s) ^ 2 / (x ^ 4 - 2 * s * x ^ 3 + 2)

/-- **5.9, the closed form.** With `s² = 1` and `x ≠ s`, the transmission has the self-energy form
`T_s(x) = 1/(1 + (x − Σ_s)²)` with `Σ_s = 1/(x − s)`. -/
theorem transmission_closed (s x : ℝ) (hs : s ^ 2 = 1) (hx : x - s ≠ 0) :
    1 / (1 + (x - 1 / (x - s)) ^ 2) = T s x := by
  have hden : x ^ 4 - 2 * s * x ^ 3 + 2 = (x - s) ^ 2 + (x * (x - s) - 1) ^ 2 := by
    linear_combination (-(x ^ 2 + 1)) * hs
  have hpos : (x - s) ^ 2 + (x * (x - s) - 1) ^ 2 ≠ 0 := by positivity
  unfold T
  rw [hden]
  field_simp
  try ring

/-- **5.9, the shared records.** Both signs give `T(0) = T(√2) = 1/2`. -/
theorem shared_records :
    T 1 0 = 1 / 2 ∧ T (-1) 0 = 1 / 2 ∧ T 1 √2 = 1 / 2 ∧ T (-1) √2 = 1 / 2 := by
  have hr : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h0 : 0 ≤ √2 := Real.sqrt_nonneg 2
  have hlt : √2 < 3 / 2 := by nlinarith
  unfold T
  refine ⟨by norm_num, by norm_num, ?_, ?_⟩
  · have hd : √2 ^ 4 - 2 * 1 * √2 ^ 3 + 2 = 6 - 4 * √2 := by
      linear_combination (√2 ^ 2 - 2 * √2 + 2) * hr
    have hne : √2 ^ 4 - 2 * 1 * √2 ^ 3 + 2 ≠ 0 := by rw [hd]; intro h; linarith
    rw [div_eq_iff hne]
    linear_combination (-√2 ^ 2 / 2 + √2) * hr
  · have t3 : 0 ≤ √2 ^ 3 := by positivity
    have t4 : 0 ≤ √2 ^ 4 := by positivity
    have hne : √2 ^ 4 - 2 * -1 * √2 ^ 3 + 2 ≠ 0 := by intro h; linarith
    rw [div_eq_iff hne]
    linear_combination (-√2 ^ 2 / 2 - √2) * hr

/-- **5.9, the later outcomes.** At `x = 1` the two states transmit `0` and `4/5`; at
`x = 1/10` they differ by `79,600,000/400,039,601`. -/
theorem later_outcomes :
    T 1 1 = 0 ∧ T (-1) 1 = 4 / 5 ∧ T (-1) (1 / 10) - T 1 (1 / 10) = 79600000 / 400039601 := by
  unfold T
  norm_num

/-! ## 5.10 One-energy snapshots -/

/-- **5.10.** `Σ_λ(0) = −c` for every `λ ≠ 0`. -/
theorem snapshot_value (c l : ℝ) (hl : l ≠ 0) : c * l / (0 - l) = -c := by
  have : (0 : ℝ) - l ≠ 0 := by simpa using hl
  rw [div_eq_iff this]
  ring

/-- **5.10.** The slope at `0` is `−c/λ`, which depends on `λ`. -/
theorem snapshot_slope (c l : ℝ) (hl : l ≠ 0) :
    HasDerivAt (fun E : ℝ => c * l / (E - l)) (-c / l) 0 := by
  have h := ((hasDerivAt_id (0 : ℝ)).sub_const l).inv (by simp [hl])
  have h' := h.const_mul (c * l)
  refine (h'.congr_deriv ?_).congr_of_eventuallyEq ?_
  · simp only [id]
    field_simp
    ring
  · filter_upwards with E
    simp [div_eq_mul_inv]

/-! ## §15.2: a reduction that throws information away has an order -/

/-- **The associator of a reduced product.** For any additive map `P` on a ring,
`P(P(xy)z) − P(xP(yz)) = P(x(yz − P(yz)) − (xy − P(xy))z)`. -/
theorem reduced_associator {R : Type*} [Ring R] (P : R →+ R) (x y z : R) :
    P (P (x * y) * z) - P (x * P (y * z)) =
      P (x * (y * z - P (y * z)) - (x * y - P (x * y)) * z) := by
  rw [← map_sub]
  congr 1
  simp only [mul_sub, sub_mul, mul_assoc]
  abel

end VOTKP.Peel
