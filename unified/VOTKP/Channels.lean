/-
VOTKP §5.6 and §§20.3, 20.5.1: channel forms, the retained resolvent and contour selection
(Jeromie Beasley).

* **5.6, matrix form.** Channels `m` carry positive semidefinite forms `Kₘ`, poles `Δₘ²` and
  weights `sₘ`; the response is `𝓡(s, y) = Σₘ 2Δₘ³ sₘ Kₘ/(Δₘ² − y)`. The four readings give
  `D = Σₘ cₘ δsₘ Kₘ` (`four_reading_matrix`); with `L = Σₘ δsₘ Kₘ` and every active `cₘ` in
  `[β₋, β₊]`, `β₋ L ≼ D ≼ β₊ L` (`four_reading_sandwich`); when `β₋ > 0`, `ker D = ker L`
  (`four_reading_kernel`) and `ker L = ⋂_{active} ker Kₘ` (`kernel_active`). The forms are real
  symmetric here.
* **§20.3, the retained resolvent.** For `H = [[A, B], [B†, D]]`, the retained block of
  `(z − H)⁻¹` is `(z − A − Σ(z))⁻¹` with `Σ(z) = B(z − D)⁻¹B†` (`retained_resolvent`).
* **§20.3.3, contour selection.** For `Σ(z) = Σₖ Wₖ/(z − eₖ)` and `f` holomorphic on a closed
  disk whose circle avoids every `eₖ`, `(2πi)⁻¹∮ f Σ = Σ_{eₖ inside} f(eₖ) Wₖ`
  (`channel_contour`), by Cauchy's integral formula and Cauchy–Goursat from Mathlib.
* **§20.5.1, the coupling footprint.** With `P` the retained projector and `C = [H, P]`,
  `Tr C² = −2 Tr(BB†)` (`commutator_coupling`); for `B = (0.7, 0.3i)`, `BB† = 0.58`
  (`footprint_example`).
Developed with AI assistance.
-/
import Mathlib

namespace VOTKP.Channels

open Matrix

/-! ## 5.6 The four-reading certificate, matrix form -/

section FourReading

variable {ι n : Type*} [Fintype ι] [Fintype n]

/-- The response `𝓡(s, y) = Σₘ 2Δₘ³ sₘ Kₘ/(Δₘ² − y)` at squared probe frequency `y`. -/
noncomputable def response (Δ s : ι → ℝ) (K : ι → Matrix n n ℝ) (y : ℝ) : Matrix n n ℝ :=
  ∑ m, (2 * Δ m ^ 3 * s m / (Δ m ^ 2 - y)) • K m

/-- `cₘ = 2Δₘ³/((Δₘ² − y₁)(Δₘ² − y₂))`. -/
noncomputable def coeff (Δ : ι → ℝ) (y1 y2 : ℝ) (m : ι) : ℝ :=
  2 * Δ m ^ 3 / ((Δ m ^ 2 - y1) * (Δ m ^ 2 - y2))

/-- **5.6, the matrix coefficient formula.** The four readings, before and after the peel at
`y₁` and `y₂`, combine to `D = Σₘ cₘ (s_before − s_after)ₘ Kₘ`. -/
theorem four_reading_matrix (Δ sb sa : ι → ℝ) (K : ι → Matrix n n ℝ) (y1 y2 : ℝ)
    (h1 : ∀ m, Δ m ^ 2 - y1 ≠ 0) (h2 : ∀ m, Δ m ^ 2 - y2 ≠ 0) (h12 : y2 - y1 ≠ 0) :
    (y2 - y1)⁻¹ • (response Δ sb K y2 - response Δ sb K y1 - response Δ sa K y2
        + response Δ sa K y1) = ∑ m, (coeff Δ y1 y2 m * (sb m - sa m)) • K m := by
  simp only [response, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, Finset.smul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← sub_smul, ← sub_smul, ← add_smul, smul_smul]
  congr 1
  have a1 := h1 m
  have a2 := h2 m
  simp only [coeff]
  field_simp
  ring

lemma sum_smul_posSemidef (a : ι → ℝ) (K : ι → Matrix n n ℝ) (ha : ∀ m, 0 ≤ a m)
    (hK : ∀ m, (K m).PosSemidef) : (∑ m, a m • K m).PosSemidef :=
  Matrix.posSemidef_sum Finset.univ fun m _ => (hK m).smul (ha m)

/-- **5.6, the sandwich.** With nonnegative weight changes `δsₘ`, positive semidefinite `Kₘ`
and every active coefficient in `[β₋, β₊]`: `β₋ L ≼ D ≼ β₊ L`. -/
theorem four_reading_sandwich (c ds : ι → ℝ) (K : ι → Matrix n n ℝ) (bmin bmax : ℝ)
    (hds : ∀ m, 0 ≤ ds m) (hK : ∀ m, (K m).PosSemidef)
    (hc : ∀ m, ds m ≠ 0 → bmin ≤ c m ∧ c m ≤ bmax) :
    (∑ m, (c m * ds m) • K m - bmin • ∑ m, ds m • K m).PosSemidef ∧
      (bmax • ∑ m, ds m • K m - ∑ m, (c m * ds m) • K m).PosSemidef := by
  have e1 : ∑ m, (c m * ds m) • K m - bmin • ∑ m, ds m • K m
      = ∑ m, ((c m - bmin) * ds m) • K m := by
    rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [smul_smul, ← sub_smul]
    congr 1
    ring
  have e2 : bmax • ∑ m, ds m • K m - ∑ m, (c m * ds m) • K m
      = ∑ m, ((bmax - c m) * ds m) • K m := by
    rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [smul_smul, ← sub_smul]
    congr 1
    ring
  rw [e1, e2]
  constructor
  · refine sum_smul_posSemidef _ K (fun m => ?_) hK
    by_cases h : ds m = 0
    · simp [h]
    · exact mul_nonneg (sub_nonneg.2 (hc m h).1) (hds m)
  · refine sum_smul_posSemidef _ K (fun m => ?_) hK
    by_cases h : ds m = 0
    · simp [h]
    · exact mul_nonneg (sub_nonneg.2 (hc m h).2) (hds m)

lemma quad_sub (X Y : Matrix n n ℝ) (b : ℝ) (v : n → ℝ) :
    v ⬝ᵥ ((X - b • Y) *ᵥ v) = v ⬝ᵥ (X *ᵥ v) - b * (v ⬝ᵥ (Y *ᵥ v)) := by
  rw [sub_mulVec, dotProduct_sub, smul_mulVec, dotProduct_smul, smul_eq_mul]

lemma quad_sub' (X Y : Matrix n n ℝ) (b : ℝ) (v : n → ℝ) :
    v ⬝ᵥ ((b • Y - X) *ᵥ v) = b * (v ⬝ᵥ (Y *ᵥ v)) - v ⬝ᵥ (X *ᵥ v) := by
  rw [sub_mulVec, dotProduct_sub, smul_mulVec, dotProduct_smul, smul_eq_mul]

lemma psd_quad_nonneg {M : Matrix n n ℝ} (hM : M.PosSemidef) (v : n → ℝ) :
    0 ≤ v ⬝ᵥ (M *ᵥ v) := by
  simpa using hM.dotProduct_mulVec_nonneg v

lemma psd_quad_zero {M : Matrix n n ℝ} (hM : M.PosSemidef) {v : n → ℝ} :
    v ⬝ᵥ (M *ᵥ v) = 0 ↔ M *ᵥ v = 0 := by
  simpa using hM.dotProduct_mulVec_zero_iff (x := v)

/-- **5.6, the kernel.** If moreover `β₋ > 0`, then `D` and `L` have the same kernel: `D`
vanishes on exactly the directions the peel left untouched. -/
theorem four_reading_kernel (c ds : ι → ℝ) (K : ι → Matrix n n ℝ) (bmin bmax : ℝ)
    (hb : 0 < bmin) (hds : ∀ m, 0 ≤ ds m) (hK : ∀ m, (K m).PosSemidef)
    (hc : ∀ m, ds m ≠ 0 → bmin ≤ c m ∧ c m ≤ bmax) (v : n → ℝ) :
    (∑ m, (c m * ds m) • K m) *ᵥ v = 0 ↔ (∑ m, ds m • K m) *ᵥ v = 0 := by
  obtain ⟨hlo, hhi⟩ := four_reading_sandwich c ds K bmin bmax hds hK hc
  have hL : (∑ m, ds m • K m).PosSemidef := sum_smul_posSemidef ds K hds hK
  have hD : (∑ m, (c m * ds m) • K m).PosSemidef := by
    have : ∑ m, (c m * ds m) • K m
        = (∑ m, (c m * ds m) • K m - bmin • ∑ m, ds m • K m) + bmin • ∑ m, ds m • K m := by
      abel
    rw [this]
    exact hlo.add (hL.smul hb.le)
  have q1 := psd_quad_nonneg hlo v
  have q2 := psd_quad_nonneg hhi v
  have qL := psd_quad_nonneg hL v
  have qD := psd_quad_nonneg hD v
  rw [quad_sub] at q1
  rw [quad_sub'] at q2
  constructor
  · intro h
    have h0 : v ⬝ᵥ ((∑ m, (c m * ds m) • K m) *ᵥ v) = 0 := by rw [h, dotProduct_zero]
    refine (psd_quad_zero hL).1 ?_
    have : bmin * (v ⬝ᵥ ((∑ m, ds m • K m) *ᵥ v)) ≤ 0 := by linarith
    have : v ⬝ᵥ ((∑ m, ds m • K m) *ᵥ v) ≤ 0 := by
      by_contra hneg
      push_neg at hneg
      have := mul_pos hb hneg
      linarith
    linarith
  · intro h
    have h0 : v ⬝ᵥ ((∑ m, ds m • K m) *ᵥ v) = 0 := by rw [h, dotProduct_zero]
    refine (psd_quad_zero hD).1 ?_
    rw [h0, mul_zero] at q2
    linarith

/-- **5.6, the untouched directions.** `ker L` is the intersection of the kernels of the active
forms. -/
theorem kernel_active (ds : ι → ℝ) (K : ι → Matrix n n ℝ) (hds : ∀ m, 0 ≤ ds m)
    (hK : ∀ m, (K m).PosSemidef) (v : n → ℝ) :
    (∑ m, ds m • K m) *ᵥ v = 0 ↔ ∀ m, ds m ≠ 0 → K m *ᵥ v = 0 := by
  have hsum : v ⬝ᵥ ((∑ m, ds m • K m) *ᵥ v) = ∑ m, ds m * (v ⬝ᵥ (K m *ᵥ v)) := by
    rw [sum_mulVec, dotProduct_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [smul_mulVec, dotProduct_smul, smul_eq_mul]
  have hL : (∑ m, ds m • K m).PosSemidef := sum_smul_posSemidef ds K hds hK
  constructor
  · intro h m hm
    have h0 : ∑ m, ds m * (v ⬝ᵥ (K m *ᵥ v)) = 0 := by rw [← hsum, h, dotProduct_zero]
    have hnn : ∀ m ∈ Finset.univ, 0 ≤ ds m * (v ⬝ᵥ (K m *ᵥ v)) :=
      fun m _ => mul_nonneg (hds m) (psd_quad_nonneg (hK m) v)
    have hm0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h0 m (Finset.mem_univ m)
    rcases mul_eq_zero.1 hm0 with h' | h'
    · exact absurd h' hm
    · exact (psd_quad_zero (hK m)).1 h'
  · intro h
    rw [sum_mulVec]
    refine Finset.sum_eq_zero fun m _ => ?_
    by_cases hm : ds m = 0
    · simp [hm]
    · rw [smul_mulVec, h m hm, smul_zero]

end FourReading

/-! ## §20.3 The retained resolvent -/

section Resolvent

variable {p q : Type*} [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q]

/-- `z − [[A, B], [B†, D]] = [[z − A, −B], [−B†, z − D]]`. -/
lemma shift_fromBlocks (A : Matrix p p ℂ) (B : Matrix p q ℂ) (D : Matrix q q ℂ) (z : ℂ) :
    z • (1 : Matrix (p ⊕ q) (p ⊕ q) ℂ) - fromBlocks A B Bᴴ D
      = fromBlocks (z • 1 - A) (-B) (-Bᴴ) (z • 1 - D) := by
  ext (i | i) (j | j) <;> simp [Matrix.one_apply]

/-- **§20.3, the retained resolvent.** If `z − D` and the Schur complement
`z − A − B(z − D)⁻¹B†` are invertible, the retained block of `(z − H)⁻¹` is
`(z − A − Σ(z))⁻¹` with `Σ(z) = B(z − D)⁻¹B†`. -/
theorem retained_resolvent (A : Matrix p p ℂ) (B : Matrix p q ℂ) (D : Matrix q q ℂ) (z : ℂ)
    (hD : IsUnit (z • (1 : Matrix q q ℂ) - D).det)
    (hS : IsUnit (z • (1 : Matrix p p ℂ) - A - B * (z • (1 : Matrix q q ℂ) - D)⁻¹ * Bᴴ).det) :
    (z • (1 : Matrix (p ⊕ q) (p ⊕ q) ℂ) - fromBlocks A B Bᴴ D)⁻¹.toBlocks₁₁
      = (z • (1 : Matrix p p ℂ) - A - B * (z • (1 : Matrix q q ℂ) - D)⁻¹ * Bᴴ)⁻¹ := by
  letI iD : Invertible (z • (1 : Matrix q q ℂ) - D) := invertibleOfIsUnitDet _ hD
  have hS' : IsUnit ((z • (1 : Matrix p p ℂ) - A)
      - (-B) * ⅟(z • (1 : Matrix q q ℂ) - D) * (-Bᴴ)).det := by
    simpa only [invOf_eq_nonsing_inv, Matrix.neg_mul, Matrix.mul_neg, neg_neg] using hS
  letI iS : Invertible ((z • (1 : Matrix p p ℂ) - A)
      - (-B) * ⅟(z • (1 : Matrix q q ℂ) - D) * (-Bᴴ)) := invertibleOfIsUnitDet _ hS'
  letI iM := fromBlocks₂₂Invertible (z • (1 : Matrix p p ℂ) - A) (-B) (-Bᴴ)
    (z • (1 : Matrix q q ℂ) - D)
  have key := invOf_fromBlocks₂₂_eq (z • (1 : Matrix p p ℂ) - A) (-B) (-Bᴴ)
    (z • (1 : Matrix q q ℂ) - D)
  simp only [invOf_eq_nonsing_inv] at key
  rw [shift_fromBlocks, key, toBlocks_fromBlocks₁₁]
  simp only [Matrix.neg_mul, Matrix.mul_neg, neg_neg]

end Resolvent

/-! ## §20.3.3 Contour selection of channels -/

section Contour

open Complex Metric Real

open Classical in
/-- **§20.3.3, contour selection.** For the channel sum `Σ(z) = Σₖ Wₖ/(z − eₖ)` and `f`
holomorphic on the closed disk `|z − c| ≤ R` whose circle avoids every `eₖ`,
`(2πi)⁻¹ ∮ f(z)Σ(z) dz` keeps exactly the channels inside the circle, each weighted by
`f(eₖ)`. Taking `f = 1` gives the enclosed coupling weight, `f(z) = zⁿ` an energy moment, and
`f(z) = e^{−izt/ℏ}` the enclosed part of the time kernel. -/
theorem channel_contour {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {ι : Type*} (s : Finset ι) (e : ι → ℂ) (W : ι → E) (f : ℂ → ℂ) (c : ℂ) (R : ℝ)
    (hR : 0 < R) (hf : DifferentiableOn ℂ f (closedBall c R)) (he : ∀ k ∈ s, e k ∉ sphere c R) :
    (2 * π * I : ℂ)⁻¹ • ∮ z in C(c, R), ∑ k ∈ s, (f z * (z - e k)⁻¹) • W k
      = ∑ k ∈ s, (if e k ∈ ball c R then f (e k) else 0) • W k := by
  have hint : ∀ k ∈ s, CircleIntegrable (fun z => (f z * (z - e k)⁻¹) • W k) c R := by
    intro k hk
    apply ContinuousOn.circleIntegrable hR.le
    refine ContinuousOn.smul ?_ continuousOn_const
    refine (hf.continuousOn.mono sphere_subset_closedBall).mul ?_
    refine (continuousOn_id.sub continuousOn_const).inv₀ ?_
    intro z hz h
    apply he k hk
    have hz' : z = e k := by simpa [sub_eq_zero] using h
    rw [← hz']
    exact hz
  rw [circleIntegral.integral_fun_sum hint, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [circleIntegral.integral_smul_const, smul_smul]
  congr 1
  by_cases hin : e k ∈ ball c R
  · rw [if_pos hin]
    have hC := hf.circleIntegral_sub_inv_smul hin
    have heq : (∮ z in C(c, R), f z * (z - e k)⁻¹) = ∮ z in C(c, R), (z - e k)⁻¹ • f z := by
      congr 1
      funext z
      rw [smul_eq_mul, mul_comm]
    rw [heq, hC, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ two_pi_I_ne_zero, one_mul]
  · rw [if_neg hin]
    have hout : e k ∉ closedBall c R := by
      intro h
      rcases (mem_closedBall.1 h).lt_or_eq with h' | h'
      · exact hin (mem_ball.2 h')
      · exact he k hk (mem_sphere.2 h')
    have hne : ∀ z ∈ closedBall c R, z - e k ≠ 0 := by
      intro z hz h
      rw [sub_eq_zero] at h
      exact hout (by rw [← h]; exact hz)
    have hzero : (∮ z in C(c, R), f z * (z - e k)⁻¹) = 0 := by
      refine circleIntegral_eq_zero_of_differentiable_on_off_countable hR.le Set.countable_empty
        ?_ ?_
      · exact hf.continuousOn.mul ((continuousOn_id.sub continuousOn_const).inv₀
          fun z hz => by simpa using hne z hz)
      · intro z hz
        have hzb : z ∈ closedBall c R := ball_subset_closedBall hz.1
        have hfz : DifferentiableAt ℂ f z :=
          hf.differentiableAt (Filter.mem_of_superset (isOpen_ball.mem_nhds hz.1)
            ball_subset_closedBall)
        exact hfz.mul ((differentiableAt_id.sub_const (e k)).inv (by simpa using hne z hzb))
    rw [hzero, mul_zero]

end Contour

/-! ## §20.5.1 The coupling footprint -/

section Footprint

variable {p q : Type*} [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q]

/-- **§20.5.1.** For `H = [[A, B], [B†, D]]` and the retained projector `P = [[1, 0], [0, 0]]`,
the commutator `C = HP − PH` satisfies `Tr C² = −2 Tr(BB†)`: half its trace square is minus the
coupling footprint `Tr K(0) = Tr BB†`, the skew-adjoint convention of the paper. -/
theorem commutator_coupling (A : Matrix p p ℂ) (B : Matrix p q ℂ) (D : Matrix q q ℂ) :
    trace ((fromBlocks A B Bᴴ D * fromBlocks (1 : Matrix p p ℂ) 0 0 0
        - fromBlocks (1 : Matrix p p ℂ) 0 0 0 * fromBlocks A B Bᴴ D)
      * (fromBlocks A B Bᴴ D * fromBlocks (1 : Matrix p p ℂ) 0 0 0
        - fromBlocks (1 : Matrix p p ℂ) 0 0 0 * fromBlocks A B Bᴴ D))
      = -2 * trace (B * Bᴴ) := by
  have hC : fromBlocks A B Bᴴ D * fromBlocks (1 : Matrix p p ℂ) 0 0 0
      - fromBlocks (1 : Matrix p p ℂ) 0 0 0 * fromBlocks A B Bᴴ D
      = fromBlocks 0 (-B) Bᴴ 0 := by
    rw [fromBlocks_multiply, fromBlocks_multiply]
    ext (i | i) (j | j) <;> simp
  rw [hC, fromBlocks_multiply]
  simp only [Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero, Matrix.neg_mul,
    Matrix.mul_neg, neg_zero]
  have htr : ∀ (X : Matrix p p ℂ) (Y : Matrix q q ℂ),
      trace (fromBlocks X 0 0 Y) = trace X + trace Y := by
    intro X Y
    simp [trace, Matrix.diag, Fintype.sum_sum_type]
  rw [htr, trace_neg, trace_neg, trace_mul_comm Bᴴ B]
  ring

/-- The footprint of a two-channel coupling `B = (a, ib)`: `BB† = a² + b²`. -/
lemma footprint_two (a b : ℝ) :
    (!![(a : ℂ), (b : ℂ) * Complex.I] * (!![(a : ℂ), (b : ℂ) * Complex.I])ᴴ) 0 0
      = ((a ^ 2 + b ^ 2 : ℝ) : ℂ) := by
  refine Complex.ext ?_ ?_ <;> simp [Matrix.mul_apply, Fin.sum_univ_two, pow_two] <;> ring

/-- **§20.5.1, the example.** For `B = (0.7, 0.3i)` the footprint is `BB† = 0.58`. -/
theorem footprint_example :
    (!![((7 / 10 : ℝ) : ℂ), ((3 / 10 : ℝ) : ℂ) * Complex.I]
      * (!![((7 / 10 : ℝ) : ℂ), ((3 / 10 : ℝ) : ℂ) * Complex.I])ᴴ) 0 0
      = ((58 / 100 : ℝ) : ℂ) := by
  rw [footprint_two]
  norm_num

end Footprint

end VOTKP.Channels
