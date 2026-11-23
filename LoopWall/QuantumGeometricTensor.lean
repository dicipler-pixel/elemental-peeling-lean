import Mathlib

/-!
# The intrinsic quantum geometric tensor: metric, curvature, and the Wirtinger bound

Direction D7 of the third round.  `Q P V W = (P*V*W).trace`, `metric V W = (V*W).trace/2`,
`curvature P V W = -2*(Q P V W).im`.  `Q_hermitian_symmetric`; `Q_re_eq_metric` (the real part is
the metric) and `Q_eq_metric_sub_curvature_mul_I` (`Q = g - Ω i/2`); `metric_symmetric`,
`curvature_antisymmetric`, `curvature_self`; positivity `Q_self_re_nonneg` and definiteness
`Q_self_re_eq_zero_iff`.  `Q_norm_sq_le` is Cauchy–Schwarz for the form, from which
`wirtinger_inequality` (`g(V,W)² + Ω(V,W)²/4 ≤ g(V,V) g(W,W)`) follows on the off-diagonal-block
tangents — and `crossBlock_only_counterexample` shows the complementary diagonal block must vanish
for the real-part identity.  Unitary covariance for all three, `deriv_sin_sq` with
`peel_rate_bound` for `|d(Γ²)/ds|² ≤ 16 g Γ²(1-Γ²)`, `wall_factor_eq_quarter_iff` for the maximum
at `Γ² = 1/2`, and `peel_rate_counterexample_without_nonnegative_metric` for the necessity of
`0 ≤ g`.

Written in the third parallel formalization round (swarm `smws58h9u`, direction m7),
recompiled and reviewed here; namespace and header added, `#print axioms` lines removed.
-/

namespace ElementalPeeling.LoopWall.QuantumGeometricTensor

open scoped ComplexConjugate ComplexOrder
open Matrix

variable {n : ℕ}

/-- The projector-weighted quantum geometric sesquilinear form. -/
def Q (P V W : Matrix (Fin n) (Fin n) ℂ) : ℂ := (P * V * W).trace

/-- The real quantum metric (the trace of Hermitian matrices is real). -/
noncomputable def metric (V W : Matrix (Fin n) (Fin n) ℂ) : ℝ := ((V * W).trace).re / 2

/-- The Berry curvature convention from the peel ledger. -/
def curvature (P V W : Matrix (Fin n) (Fin n) ℂ) : ℝ := -2 * (Q P V W).im

/-- An idempotent Hermitian matrix is positive semidefinite. -/
theorem projector_posSemidef {P : Matrix (Fin n) (Fin n) ℂ}
    (hP : P * P = P) (hPh : Pᴴ = P) : P.PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self P
  rwa [hPh, hP] at h

/-- Hermitian symmetry of `Q`; no idempotence or cross-block condition is used. -/
theorem Q_hermitian_symmetric {P V W : Matrix (Fin n) (Fin n) ℂ}
    (hPh : Pᴴ = P) (hV : Vᴴ = V) (hW : Wᴴ = W) :
    Q P V W = star (Q P W V) := by
  unfold Q
  rw [← Matrix.trace_conjTranspose]
  simp only [Matrix.conjTranspose_mul, hPh, hV, hW]
  simpa only [Matrix.mul_assoc] using (Matrix.trace_mul_cycle V W P).symm

/-- The diagonal of `Q` is real. -/
theorem Q_self_im_zero {P V : Matrix (Fin n) (Fin n) ℂ}
    (hPh : Pᴴ = P) (hV : Vᴴ = V) : (Q P V V).im = 0 := by
  have h := Q_hermitian_symmetric hPh hV hV
  have hi := congrArg Complex.im h
  simp only [Complex.star_def, Complex.conj_im] at hi
  linarith

/-- `Q` is the Frobenius square of `P * V` on the diagonal. -/
theorem Q_self_eq_frobenius {P V : Matrix (Fin n) (Fin n) ℂ}
    (hP : P * P = P) (hPh : Pᴴ = P) (hV : Vᴴ = V) :
    Q P V V = ((P * V)ᴴ * (P * V)).trace := by
  symm
  calc
    ((P * V)ᴴ * (P * V)).trace = (V * P * (P * V)).trace := by
      rw [Matrix.conjTranspose_mul, hV, hPh]
    _ = (V * (P * P) * V).trace := by congr 1; noncomm_ring
    _ = (V * P * V).trace := by rw [hP]
    _ = (P * V * V).trace := (Matrix.trace_mul_cycle P V V).symm

/-- Positive semidefiniteness on the diagonal, under the original hypotheses. -/
theorem Q_self_re_nonneg {P V : Matrix (Fin n) (Fin n) ℂ}
    (hP : P * P = P) (hPh : Pᴴ = P) (hV : Vᴴ = V) :
    0 ≤ (Q P V V).re := by
  rw [Q_self_eq_frobenius hP hPh hV]
  exact (RCLike.nonneg_iff.mp
    (Matrix.posSemidef_conjTranspose_mul_self (P * V)).trace_nonneg).1

/-- The metric is symmetric (indeed cyclicity of trace needs no Hermitian hypothesis). -/
theorem metric_symmetric (V W : Matrix (Fin n) (Fin n) ℂ) :
    metric V W = metric W V := by
  unfold metric
  rw [Matrix.trace_mul_comm V W]

/-- The curvature is antisymmetric on Hermitian tangents. -/
theorem curvature_antisymmetric {P V W : Matrix (Fin n) (Fin n) ℂ}
    (hPh : Pᴴ = P) (hV : Vᴴ = V) (hW : Wᴴ = W) :
    curvature P V W = -curvature P W V := by
  unfold curvature
  rw [Q_hermitian_symmetric hPh hW hV]
  simp

/-- The curvature of a tangent with itself vanishes. -/
theorem curvature_self {P V : Matrix (Fin n) (Fin n) ℂ}
    (hPh : Pᴴ = P) (hV : Vᴴ = V) : curvature P V V = 0 := by
  unfold curvature
  rw [Q_self_im_zero hPh hV]
  ring

/-- Vanishing of both diagonal blocks is equivalent to this useful splitting. -/
theorem eq_projector_mul_add_mul_projector {P V : Matrix (Fin n) (Fin n) ℂ}
    (hVP : P * V * P = 0) (hVR : (1 - P) * V * (1 - P) = 0) :
    V = P * V + V * P := by
  rw [← sub_eq_zero]
  calc
    V - (P * V + V * P) = (1 - P) * V * (1 - P) - P * V * P := by
      noncomm_ring
    _ = 0 := by rw [hVR, hVP, sub_zero]

/-- With both diagonal blocks removed, the real part of `Q` is exactly the metric. -/
theorem Q_re_eq_metric {P V W : Matrix (Fin n) (Fin n) ℂ}
    (hPh : Pᴴ = P) (hV : Vᴴ = V) (hW : Wᴴ = W)
    (hVP : P * V * P = 0) (hVR : (1 - P) * V * (1 - P) = 0) :
    (Q P V W).re = metric V W := by
  have hsplit := eq_projector_mul_add_mul_projector hVP hVR
  have htrace : (V * W).trace = Q P V W + Q P W V := by
    calc
      (V * W).trace = ((P * V + V * P) * W).trace := by rw [← hsplit]
      _ = (P * V * W).trace + ((V * P) * W).trace := by
        rw [add_mul, Matrix.trace_add]
      _ = Q P V W + Q P W V := by
        unfold Q
        rw [Matrix.mul_assoc V P W, Matrix.trace_mul_comm V (P * W)]
  unfold metric
  rw [htrace, Q_hermitian_symmetric hPh hW hV]
  simp only [Complex.star_def, Complex.add_re, Complex.conj_re]
  ring

/-- The corrected complex decomposition of the quantum geometric tensor. -/
theorem Q_eq_metric_sub_curvature_mul_I {P V W : Matrix (Fin n) (Fin n) ℂ}
    (hPh : Pᴴ = P) (hV : Vᴴ = V) (hW : Wᴴ = W)
    (hVP : P * V * P = 0) (hVR : (1 - P) * V * (1 - P) = 0) :
    Q P V W = (metric V W : ℂ) - (curvature P V W : ℂ) * Complex.I / 2 := by
  have hre := Q_re_eq_metric hPh hV hW hVP hVR
  apply Complex.ext <;> simp [curvature, hre]; ring


/-- On the corrected tangent space, `Q` is positive definite. -/
theorem Q_self_re_eq_zero_iff {P V : Matrix (Fin n) (Fin n) ℂ}
    (hP : P * P = P) (hPh : Pᴴ = P) (hV : Vᴴ = V)
    (hVP : P * V * P = 0) (hVR : (1 - P) * V * (1 - P) = 0) :
    (Q P V V).re = 0 ↔ V = 0 := by
  constructor
  · intro hre
    have hq : Q P V V = 0 := by
      apply Complex.ext
      · simpa using hre
      · simpa using Q_self_im_zero hPh hV
    have htr : ((P * V)ᴴ * (P * V)).trace = 0 := by
      rw [← Q_self_eq_frobenius hP hPh hV]
      exact hq
    have hpv : P * V = 0 := Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp htr
    have hvp : V * P = 0 := by
      have hh := congrArg Matrix.conjTranspose hpv
      simpa [Matrix.conjTranspose_mul, hV, hPh] using hh
    rw [eq_projector_mul_add_mul_projector hVP hVR, hpv, hvp, add_zero]
  · rintro rfl
    simp [Q]

/-- The rank-one projector and complementary rank-one tangent used below. -/
def counterP : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 0]

/-- A nonzero Hermitian matrix invisible to `Q counterP`. -/
def counterV : Matrix (Fin 2) (Fin 2) ℂ := !![0, 0; 0, 1]

/-- The prompt's real-part identity and definiteness fail with only `P * V * P = 0`.
The missing condition is precisely the vanishing complementary diagonal block. -/
theorem crossBlock_only_counterexample :
    ∃ P V : Matrix (Fin 2) (Fin 2) ℂ,
      P * P = P ∧ Pᴴ = P ∧ Vᴴ = V ∧ P * V * P = 0 ∧
      (Q P V V).re ≠ metric V V ∧ (Q P V V).re = 0 ∧ V ≠ 0 := by
  refine ⟨counterP, counterV, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [counterP, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [counterP, Matrix.conjTranspose_apply]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [counterV, Matrix.conjTranspose_apply]
  · ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [counterP, counterV, Matrix.mul_apply, Fin.sum_univ_two]
  · norm_num [Q, metric, counterP, counterV, Matrix.trace_fin_two,
      Matrix.mul_apply, Fin.sum_univ_two]
  · norm_num [Q, counterP, counterV, Matrix.trace_fin_two,
      Matrix.mul_apply, Fin.sum_univ_two]
  · intro h
    have h11 := congrFun (congrFun h 1) 1
    norm_num [counterV] at h11


/-- Cauchy--Schwarz for the (possibly degenerate) form `Q`. -/
theorem Q_norm_sq_le {P V W : Matrix (Fin n) (Fin n) ℂ}
    (hP : P * P = P) (hPh : Pᴴ = P) (hV : Vᴴ = V) (hW : Wᴴ = W) :
    ‖Q P V W‖ ^ 2 ≤ (Q P V V).re * (Q P W W).re := by
  have hPS := projector_posSemidef hP hPh
  let : SeminormedAddCommGroup (Matrix (Fin n) (Fin n) ℂ) :=
    Matrix.toMatrixSeminormedAddCommGroup P hPS
  let : InnerProductSpace ℂ (Matrix (Fin n) (Fin n) ℂ) :=
    Matrix.toMatrixInnerProductSpace P hPS
  have hinner (A B : Matrix (Fin n) (Fin n) ℂ) (hA : Aᴴ = A) :
      inner ℂ A B = Q P A B := by
    change (B * P * Aᴴ).trace = (P * A * B).trace
    rw [hA]
    exact (Matrix.trace_mul_cycle P A B).symm
  have hcs := inner_mul_inner_self_le (𝕜 := ℂ) V W
  rw [hinner V W hV, hinner W V hW, hinner V V hV, hinner W W hW] at hcs
  rw [Q_hermitian_symmetric hPh hW hV, norm_star] at hcs
  simpa [pow_two] using hcs

/-- The Wirtinger inequality on the corrected (off-diagonal-block) tangent space. -/
theorem wirtinger_inequality {P V W : Matrix (Fin n) (Fin n) ℂ}
    (hP : P * P = P) (hPh : Pᴴ = P) (hV : Vᴴ = V) (hW : Wᴴ = W)
    (hVP : P * V * P = 0) (hWP : P * W * P = 0)
    (hVR : (1 - P) * V * (1 - P) = 0) (hWR : (1 - P) * W * (1 - P) = 0) :
    metric V W ^ 2 + (curvature P V W) ^ 2 / 4 ≤ metric V V * metric W W := by
  have hcs := Q_norm_sq_le hP hPh hV hW
  rw [Complex.sq_norm, Complex.normSq_apply] at hcs
  rw [← Q_re_eq_metric hPh hV hW hVP hVR,
    ← Q_re_eq_metric hPh hV hV hVP hVR,
    ← Q_re_eq_metric hPh hW hW hWP hWR]
  unfold curvature
  nlinarith

/-- Conjugating all three matrices by a unitary preserves `Q`. -/
theorem Q_unitary_covariant {P V W U : Matrix (Fin n) (Fin n) ℂ}
    (_hU : U * Uᴴ = 1) (hU' : Uᴴ * U = 1) :
    Q (U * P * Uᴴ) (U * V * Uᴴ) (U * W * Uᴴ) = Q P V W := by
  unfold Q
  calc
    ((U * P * Uᴴ) * (U * V * Uᴴ) * (U * W * Uᴴ)).trace =
        (U * (P * V * W) * Uᴴ).trace := by
      congr 1
      simp only [Matrix.mul_assoc]
      simp only [← Matrix.mul_assoc Uᴴ U, hU', Matrix.one_mul]
    _ = (Uᴴ * (U * (P * V * W))).trace :=
      Matrix.trace_mul_comm (U * (P * V * W)) Uᴴ
    _ = (P * V * W).trace := by
      rw [← Matrix.mul_assoc, hU', Matrix.one_mul]

/-- Conjugating both tangents by a unitary preserves the metric. -/
theorem metric_unitary_covariant {V W U : Matrix (Fin n) (Fin n) ℂ}
    (_hU : U * Uᴴ = 1) (hU' : Uᴴ * U = 1) :
    metric (U * V * Uᴴ) (U * W * Uᴴ) = metric V W := by
  unfold metric
  congr 2
  calc
    ((U * V * Uᴴ) * (U * W * Uᴴ)).trace = (U * (V * W) * Uᴴ).trace := by
      congr 1
      simp only [Matrix.mul_assoc]
      simp only [← Matrix.mul_assoc Uᴴ U, hU', Matrix.one_mul]
    _ = (Uᴴ * (U * (V * W))).trace := Matrix.trace_mul_comm (U * (V * W)) Uᴴ
    _ = (V * W).trace := by rw [← Matrix.mul_assoc, hU', Matrix.one_mul]

/-- Conjugating projector and tangents by a unitary preserves the curvature. -/
theorem curvature_unitary_covariant {P V W U : Matrix (Fin n) (Fin n) ℂ}
    (hU : U * Uᴴ = 1) (hU' : Uᴴ * U = 1) :
    curvature (U * P * Uᴴ) (U * V * Uᴴ) (U * W * Uᴴ) = curvature P V W := by
  unfold curvature
  rw [Q_unitary_covariant hU hU']


/-- Derivative of the peel observation `sin (θ) ^ 2`. -/
theorem deriv_sin_sq (θ : ℝ → ℝ) (hθ : Differentiable ℝ θ) (s : ℝ) :
    deriv (fun x => Real.sin (θ x) ^ 2) s =
      2 * Real.sin (θ s) * Real.cos (θ s) * deriv θ s := by
  have h := ((hθ s).hasDerivAt.sin.pow 2).deriv
  change deriv ((fun x => Real.sin (θ x)) ^ 2) s = _
  rw [h]
  ring

/-- The peel-rate bound; nonnegativity of the metric density is necessary. -/
theorem peel_rate_bound (θ : ℝ → ℝ) (hθ : Differentiable ℝ θ) (gv : ℝ → ℝ)
    (s : ℝ) (hgv : 0 ≤ gv s) (hbound : |deriv θ s| ≤ 2 * Real.sqrt (gv s)) :
    |deriv (fun x => Real.sin (θ x) ^ 2) s| ^ 2 ≤
      16 * gv s * (Real.sin (θ s) ^ 2 * (1 - Real.sin (θ s) ^ 2)) := by
  rw [deriv_sin_sq θ hθ s]
  have hd : |deriv θ s| * |deriv θ s| ≤
      (2 * Real.sqrt (gv s)) * (2 * Real.sqrt (gv s)) :=
    mul_self_le_mul_self (abs_nonneg _) hbound
  have hd2 : (deriv θ s) ^ 2 ≤ 4 * gv s := by
    rw [← sq_abs]
    calc
      |deriv θ s| ^ 2 = |deriv θ s| * |deriv θ s| := pow_two _
      _ ≤ (2 * Real.sqrt (gv s)) * (2 * Real.sqrt (gv s)) := hd
      _ = 4 * gv s := by nlinarith [Real.sq_sqrt hgv]
  calc
    |2 * Real.sin (θ s) * Real.cos (θ s) * deriv θ s| ^ 2 =
        4 * (Real.sin (θ s) ^ 2 * Real.cos (θ s) ^ 2) * (deriv θ s) ^ 2 := by
      rw [show |2 * Real.sin (θ s) * Real.cos (θ s) * deriv θ s| =
        2 * |Real.sin (θ s)| * |Real.cos (θ s)| * |deriv θ s| by
          rw [abs_mul, abs_mul, abs_mul, abs_two]]
      simp only [mul_pow, sq_abs]
      ring
    _ ≤ 4 * (Real.sin (θ s) ^ 2 * Real.cos (θ s) ^ 2) * (4 * gv s) :=
      mul_le_mul_of_nonneg_left hd2 (by positivity)
    _ = 16 * gv s * (Real.sin (θ s) ^ 2 * (1 - Real.sin (θ s) ^ 2)) := by
      rw [Real.cos_sq']
      ring

/-- The wall factor has its global maximum `1/4` at `u = 1/2`. -/
theorem wall_factor_le_quarter (u : ℝ) : u * (1 - u) ≤ 1 / 4 := by
  nlinarith [sq_nonneg (u - 1 / 2)]

/-- Equality at the wall holds exactly halfway between the two face readings. -/
theorem wall_factor_eq_quarter_iff (u : ℝ) : u * (1 - u) = 1 / 4 ↔ u = 1 / 2 := by
  constructor
  · intro h
    nlinarith [sq_nonneg (u - 1 / 2)]
  · rintro rfl
    norm_num

/-- Without `0 ≤ gv s`, the peel-rate conclusion in the prompt is false.
Here `θ` is constant and `gv = -1`; the premise holds, but the claimed bound is `0 ≤ -3`. -/
theorem peel_rate_counterexample_without_nonnegative_metric :
    ∃ θ gv : ℝ → ℝ, Differentiable ℝ θ ∧
      |deriv θ 0| ≤ 2 * Real.sqrt (gv 0) ∧
      ¬ |deriv (fun x => Real.sin (θ x) ^ 2) 0| ^ 2 ≤
        16 * gv 0 * (Real.sin (θ 0) ^ 2 * (1 - Real.sin (θ 0) ^ 2)) := by
  refine ⟨fun _ => Real.arcsin (1 / 2), fun _ => -1, differentiable_const _, ?_, ?_⟩
  · norm_num [Real.sqrt_eq_zero']
  · have hsin : Real.sin (Real.arcsin (1 / 2 : ℝ)) = 1 / 2 :=
      Real.sin_arcsin (by norm_num) (by norm_num)
    norm_num [hsin]

end ElementalPeeling.LoopWall.QuantumGeometricTensor
