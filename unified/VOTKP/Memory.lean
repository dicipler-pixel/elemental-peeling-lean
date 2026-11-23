/-
VOTKP §5.4–5.5: the memory kernel and transfer silence (Jeromie Beasley).

A retained block `x` coupled to a peeled block `y`,
  `ẋ = A x + B y`,  `ẏ = C x + D y`,
loses `y` from the record but not from the dynamics: eliminating `y` by variation of constants
leaves a memory kernel `B e^{(t−u)D} C` and a forcing term `B e^{tD} y(0)` (5.4, `memory_kernel`).

The transfer `B(zI − D)⁻¹C` of the peeled layer is silent exactly when its first `q = dim` Markov
parameters `B Dʲ C`, `j < q`, vanish (5.5, `transfer_silence`), and the bound `q` is sharp
(`shift5_moments`). Silence is stated without inverses: at every `z` outside the spectrum
(`χ_D(z) ≠ 0`), every solution `y` of `(zI − D)y = Ce` has `By = 0`. The resolvent is written
explicitly as `χ_D(z)⁻¹ S(z)`, `S(z) = Σ aₘ(z) Dᵐ`, which proves existence and uniqueness of that
solution and reduces silence to a polynomial in `z` vanishing at infinitely many points.
Developed with AI assistance.
-/
import Mathlib
import VOTKP.Observer

namespace VOTKP.Memory

/-! ## 5.4 The memory kernel -/

section Kernel

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]

/-- The free evolution `e^{tD}` of the peeled layer. -/
noncomputable def flow (D : Y →L[ℝ] Y) (t : ℝ) : Y →L[ℝ] Y := NormedSpace.exp (t • D)

lemma flow_add (D : Y →L[ℝ] Y) (s t : ℝ) : flow D (s + t) = flow D s * flow D t := by
  letI : NormedAlgebra ℚ (Y →L[ℝ] Y) := NormedAlgebra.restrictScalars ℚ ℝ (Y →L[ℝ] Y)
  unfold flow
  rw [add_smul]
  exact NormedSpace.exp_add_of_commute (((Commute.refl D).smul_left s).smul_right t)

lemma flow_zero (D : Y →L[ℝ] Y) : flow D 0 = 1 := by
  simp [flow]

lemma hasDerivAt_flow (D : Y →L[ℝ] Y) (s : ℝ) : HasDerivAt (flow D) (flow D s * D) s :=
  hasDerivAt_exp_smul_const D s

lemma hasDerivAt_flow_neg (D : Y →L[ℝ] Y) (s : ℝ) :
    HasDerivAt (fun s => flow D (-s)) (-(flow D (-s) * D)) s := by
  have h := (hasDerivAt_flow D (-s)).scomp s (hasDerivAt_neg' (x := s))
  exact h.congr_deriv (neg_one_smul ℝ _)

lemma flow_cancel (D : Y →L[ℝ] Y) (s : ℝ) (v : Y) : flow D s (flow D (-s) v) = v := by
  rw [← mul_apply_eq_comp, ← flow_add, add_neg_cancel, flow_zero, one_apply_eq_self]

/-- **5.4 Memory kernel.** If `ẋ = Ax + By` and `ẏ = Cx + Dy`, then
`ẋ(t) = Ax(t) + ∫₀ᵗ B e^{(t−u)D} C x(u) du + B e^{tD} y(0)`. -/
theorem memory_kernel (A : X →L[ℝ] X) (B : Y →L[ℝ] X) (C : X →L[ℝ] Y) (D : Y →L[ℝ] Y)
    (x : ℝ → X) (y : ℝ → Y) (x' : ℝ → X) (y' : ℝ → Y)
    (hx : ∀ t, HasDerivAt x (x' t) t) (hy : ∀ t, HasDerivAt y (y' t) t)
    (hxe : ∀ t, x' t = A (x t) + B (y t)) (hye : ∀ t, y' t = C (x t) + D (y t)) (t : ℝ) :
    x' t = A (x t) + (∫ u in (0 : ℝ)..t, B (flow D (t - u) (C (x u)))) + B (flow D t (y 0)) := by
  have hxc : Continuous x := continuous_iff_continuousAt.2 fun s => (hx s).continuousAt
  have hflow : Continuous (flow D) :=
    continuous_iff_continuousAt.2 fun s => (hasDerivAt_flow D s).continuousAt
  have hint : IntervalIntegrable (fun s => flow D (-s) (C (x s))) MeasureTheory.volume 0 t :=
    ((hflow.comp continuous_neg).clm_apply (C.continuous.comp hxc)).intervalIntegrable 0 t
  have hint2 : IntervalIntegrable (fun u => flow D (t - u) (C (x u))) MeasureTheory.volume 0 t :=
    ((hflow.comp (continuous_const.sub continuous_id)).clm_apply
      (C.continuous.comp hxc)).intervalIntegrable 0 t
  -- the peeled layer in the interaction picture, `e^{-sD} y(s)`
  have hz : ∀ s, HasDerivAt (fun s => flow D (-s) (y s)) (flow D (-s) (C (x s))) s := by
    intro s
    have h := (hasDerivAt_flow_neg D s).clm_apply (hy s)
    refine h.congr_deriv ?_
    rw [hye s, neg_apply, mul_apply_eq_comp, map_add]
    abel
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hz s) hint
  have e1 : flow D (-t) (y t) = y 0 + ∫ s in (0 : ℝ)..t, flow D (-s) (C (x s)) := by
    rw [hftc]
    simp [flow_zero]
  have hyt : y t = flow D t (y 0) + ∫ u in (0 : ℝ)..t, flow D (t - u) (C (x u)) := by
    calc y t = flow D t (flow D (-t) (y t)) := (flow_cancel D t (y t)).symm
      _ = flow D t (y 0) + flow D t (∫ s in (0 : ℝ)..t, flow D (-s) (C (x s))) := by
          rw [e1, map_add]
      _ = flow D t (y 0) + ∫ s in (0 : ℝ)..t, flow D t (flow D (-s) (C (x s))) := by
          rw [(flow D t).intervalIntegral_comp_comm hint]
      _ = flow D t (y 0) + ∫ u in (0 : ℝ)..t, flow D (t - u) (C (x u)) := by
          congr 1
          refine intervalIntegral.integral_congr (fun u _ => ?_)
          show flow D t (flow D (-u) (C (x u))) = flow D (t - u) (C (x u))
          rw [← mul_apply_eq_comp, ← flow_add, sub_eq_add_neg]
  rw [hxe t, hyt, map_add, ← B.intervalIntegral_comp_comm hint2]
  abel

end Kernel

/-! ## 5.5 Transfer silence -/

section Transfer

open Polynomial Module

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [FiniteDimensional ℝ F]

/-- The `j`-th Markov parameter `B Dʲ C` of the peeled layer. -/
def moment (B : F →ₗ[ℝ] E) (D : F →ₗ[ℝ] F) (C : E →ₗ[ℝ] F) (j : ℕ) : E →ₗ[ℝ] E :=
  B ∘ₗ (D ^ j) ∘ₗ C

/-- **5.5, the horizon.** All Markov parameters vanish iff the first `q = dim F` do
(Cayley–Hamilton). -/
theorem moment_horizon (B : F →ₗ[ℝ] E) (D : F →ₗ[ℝ] F) (C : E →ₗ[ℝ] F) :
    (∀ j, moment B D C j = 0) ↔ ∀ j < finrank ℝ F, moment B D C j = 0 := by
  constructor
  · intro h j _
    exact h j
  · intro h j
    ext e
    have hv : ∀ i < finrank ℝ F, B ((D ^ i) (C e)) = 0 := fun i hi => by
      simpa [moment] using LinearMap.congr_fun (h i hi) e
    simpa [moment] using VOTKP.Observer.horizon D B (C e) hv j

/-- `aₘ(z) = Σ_{j < q − m} c_{m+1+j} zʲ`, the coefficients of the resolvent numerator. -/
noncomputable def acoef (c : ℕ → ℝ) (q : ℕ) (z : ℝ) (m : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (q - m), c (m + 1 + j) * z ^ j

lemma acoef_succ (c : ℕ → ℝ) (q : ℕ) (z : ℝ) (m : ℕ) (hc : ∀ k, q < k → c k = 0) :
    z * acoef c q z (m + 1) = acoef c q z m - c (m + 1) := by
  by_cases hm : m + 1 ≤ q
  · obtain ⟨r, hr⟩ : ∃ r, q - m = r + 1 := ⟨q - m - 1, by omega⟩
    have hr' : q - (m + 1) = r := by omega
    unfold acoef
    rw [hr, hr', Finset.sum_range_succ', Finset.mul_sum]
    simp only [add_zero, pow_zero, mul_one, add_sub_cancel_right]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show m + 1 + (j + 1) = m + 1 + 1 + j by omega]
    ring
  · push_neg at hm
    unfold acoef
    rw [show q - (m + 1) = 0 by omega, show q - m = 0 by omega, hc (m + 1) hm]
    simp

lemma acoef_zero (c : ℕ → ℝ) (q : ℕ) (z : ℝ) :
    z * acoef c q z 0 + c 0 = ∑ i ∈ Finset.range (q + 1), c i * z ^ i := by
  unfold acoef
  rw [Nat.sub_zero, Finset.sum_range_succ', Finset.mul_sum]
  simp only [pow_zero, mul_one]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show 0 + 1 + j = j + 1 by omega]
  ring

/-- The resolvent numerator `S(z) = Σ_{m ≤ q} aₘ(z) Dᵐ`. -/
noncomputable def Snum (c : ℕ → ℝ) (q : ℕ) (z : ℝ) (D : F →ₗ[ℝ] F) : F →ₗ[ℝ] F :=
  ∑ m ∈ Finset.range (q + 1), acoef c q z m • D ^ m

lemma telescope (c : ℕ → ℝ) (q : ℕ) (hc : ∀ k, q < k → c k = 0) (z : ℝ) (D : F →ₗ[ℝ] F) :
    z • Snum c q z D - D * Snum c q z D
      = (∑ i ∈ Finset.range (q + 1), c i * z ^ i) • (1 : F →ₗ[ℝ] F)
        - ∑ i ∈ Finset.range (q + 1), c i • D ^ i := by
  have haq : acoef c q z q = 0 := by simp [acoef]
  have h1 : z • Snum c q z D
      = (∑ m ∈ Finset.range q, (acoef c q z m - c (m + 1)) • D ^ (m + 1))
        + (z * acoef c q z 0) • (1 : F →ₗ[ℝ] F) := by
    unfold Snum
    rw [Finset.smul_sum, Finset.sum_range_succ']
    simp only [smul_smul, pow_zero]
    congr 1
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [acoef_succ c q z m hc]
  have h2 : D * Snum c q z D = ∑ m ∈ Finset.range q, acoef c q z m • D ^ (m + 1) := by
    unfold Snum
    rw [Finset.mul_sum, Finset.sum_range_succ, haq, zero_smul, mul_zero, add_zero]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [mul_smul_comm, ← pow_succ']
  have h3 : ∑ i ∈ Finset.range (q + 1), c i • D ^ i
      = ∑ m ∈ Finset.range q, c (m + 1) • D ^ (m + 1) + c 0 • (1 : F →ₗ[ℝ] F) := by
    rw [Finset.sum_range_succ', pow_zero]
  rw [h1, h2, h3, ← acoef_zero c q z, add_smul]
  simp only [sub_smul, Finset.sum_sub_distrib]
  abel

/-- With Cayley–Hamilton, `(zI − D) S(z) = χ_D(z) I`. -/
lemma resolvent_identity (D : F →ₗ[ℝ] F) (z : ℝ) :
    (z • (1 : F →ₗ[ℝ] F) - D) * Snum D.charpoly.coeff (finrank ℝ F) z D
      = D.charpoly.eval z • (1 : F →ₗ[ℝ] F) := by
  have hdeg := LinearMap.charpoly_natDegree D
  have hc : ∀ k, finrank ℝ F < k → D.charpoly.coeff k = 0 := fun k hk =>
    coeff_eq_zero_of_natDegree_lt (by rw [hdeg]; exact hk)
  have h := telescope D.charpoly.coeff (finrank ℝ F) hc z D
  have hCH : ∑ i ∈ Finset.range (finrank ℝ F + 1), D.charpoly.coeff i • D ^ i = 0 := by
    have := LinearMap.aeval_self_charpoly D
    rwa [aeval_eq_sum_range, hdeg] at this
  have hev : D.charpoly.eval z
      = ∑ i ∈ Finset.range (finrank ℝ F + 1), D.charpoly.coeff i * z ^ i := by
    rw [eval_eq_sum_range, hdeg]
  rw [sub_mul, smul_mul_assoc, one_mul, h, hCH, sub_zero, hev]

lemma snum_commute (c : ℕ → ℝ) (q : ℕ) (z : ℝ) (D : F →ₗ[ℝ] F) :
    Commute (z • (1 : F →ₗ[ℝ] F) - D) (Snum c q z D) := by
  unfold Snum
  refine Commute.sum_right _ _ _ fun m _ => ?_
  refine Commute.smul_right ?_ _
  exact ((Commute.one_left _).smul_left z).sub_left ((Commute.refl D).pow_right m)

/-- Outside the spectrum, `y = χ_D(z)⁻¹ S(z) w` solves `(zI − D)y = w`. -/
lemma solve_exists (D : F →ₗ[ℝ] F) (z : ℝ) (hz : D.charpoly.eval z ≠ 0) (w : F) :
    z • ((D.charpoly.eval z)⁻¹ • Snum D.charpoly.coeff (finrank ℝ F) z D w)
      - D ((D.charpoly.eval z)⁻¹ • Snum D.charpoly.coeff (finrank ℝ F) z D w) = w := by
  have h3 := LinearMap.congr_fun (resolvent_identity D z) w
  simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.one_apply] at h3
  rw [map_smul, smul_comm z (D.charpoly.eval z)⁻¹, ← smul_sub, h3, smul_smul,
    inv_mul_cancel₀ hz, one_smul]

/-- ... and it is the only solution. -/
lemma solve_unique (D : F →ₗ[ℝ] F) (z : ℝ) (hz : D.charpoly.eval z ≠ 0) (w y : F)
    (hy : z • y - D y = w) :
    y = (D.charpoly.eval z)⁻¹ • Snum D.charpoly.coeff (finrank ℝ F) z D w := by
  have h2 : Snum D.charpoly.coeff (finrank ℝ F) z D * (z • (1 : F →ₗ[ℝ] F) - D)
      = D.charpoly.eval z • (1 : F →ₗ[ℝ] F) :=
    (snum_commute D.charpoly.coeff (finrank ℝ F) z D).eq.symm.trans (resolvent_identity D z)
  have h3 := LinearMap.congr_fun h2 y
  simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.one_apply] at h3
  rw [hy] at h3
  rw [h3, smul_smul, inv_mul_cancel₀ hz, one_smul]

/-- The transfer `B(zI − D)⁻¹C` vanishes identically: at every `z` outside the spectrum, every
solution `y` of `(zI − D)y = Ce` has `By = 0`. -/
def Silent (B : F →ₗ[ℝ] E) (D : F →ₗ[ℝ] F) (C : E →ₗ[ℝ] F) : Prop :=
  ∀ z : ℝ, D.charpoly.eval z ≠ 0 → ∀ (e : E) (y : F), z • y - D y = C e → B y = 0

/-- The polynomial `Σₘ aₘ(X) vₘ` whose value at `z` is a functional of `B S(z) C e`. -/
noncomputable def transferPoly (c : ℕ → ℝ) (q : ℕ) (v : ℕ → ℝ) : ℝ[X] :=
  ∑ m ∈ Finset.range (q + 1), ∑ j ∈ Finset.range (q - m),
    Polynomial.C (c (m + 1 + j) * v m) * Polynomial.X ^ j

lemma transferPoly_eval (c : ℕ → ℝ) (q : ℕ) (v : ℕ → ℝ) (z : ℝ) :
    (transferPoly c q v).eval z = ∑ m ∈ Finset.range (q + 1), acoef c q z m * v m := by
  simp only [transferPoly, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X, acoef,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun j _ => ?_
  ring

lemma transferPoly_coeff (c : ℕ → ℝ) (q : ℕ) (v : ℕ → ℝ) (n : ℕ) :
    (transferPoly c q v).coeff n
      = ∑ m ∈ Finset.range (q + 1), if n < q - m then c (m + 1 + n) * v m else 0 := by
  simp only [transferPoly, finsetSum_coeff, coeff_C_mul_X_pow]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_range]

lemma coeff_extract (c : ℕ → ℝ) (q : ℕ) (v : ℕ → ℝ) (hcq : c q = 1) (s : ℕ) (hs : s < q)
    (hlow : ∀ m < s, v m = 0) :
    (transferPoly c q v).coeff (q - 1 - s) = v s := by
  rw [transferPoly_coeff, Finset.sum_eq_single s]
  · rw [if_pos (by omega), show s + 1 + (q - 1 - s) = q by omega, hcq, one_mul]
  · intro m hm hms
    have hm' := Finset.mem_range.mp hm
    by_cases hlt : m < s
    · rw [hlow m hlt]
      simp
    · rw [if_neg (by omega)]
  · intro hs'
    exact absurd (Finset.mem_range.mpr (by omega)) hs'

/-- **5.5 Transfer silence.** The transfer `B(zI − D)⁻¹C` of the peeled layer vanishes
identically iff `B Dʲ C = 0` for every `j < q = dim F`. -/
theorem transfer_silence (B : F →ₗ[ℝ] E) (D : F →ₗ[ℝ] F) (C : E →ₗ[ℝ] F) :
    Silent B D C ↔ ∀ j < finrank ℝ F, moment B D C j = 0 := by
  constructor
  · intro hS j hj
    have hq := LinearMap.charpoly_natDegree D
    have hcq : D.charpoly.coeff (finrank ℝ F) = 1 := by
      have := (LinearMap.charpoly_monic D).coeff_natDegree
      rwa [hq] at this
    have hev : ∀ (e : E) (φ : Module.Dual ℝ E) (z : ℝ), D.charpoly.eval z ≠ 0 →
        (transferPoly D.charpoly.coeff (finrank ℝ F)
          (fun m => φ (B ((D ^ m) (C e))))).eval z = 0 := by
      intro e φ z hz
      have hB := hS z hz e _ (solve_exists D z hz (C e))
      rw [map_smul, smul_eq_zero] at hB
      rcases hB with h | h
      · exact absurd h (inv_ne_zero hz)
      · have h0 : φ (B (Snum D.charpoly.coeff (finrank ℝ F) z D (C e))) = 0 := by
          rw [h, map_zero]
        rw [transferPoly_eval, ← h0]
        simp only [Snum, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul,
          smul_eq_mul]
    have hzero : ∀ (e : E) (φ : Module.Dual ℝ E),
        transferPoly D.charpoly.coeff (finrank ℝ F) (fun m => φ (B ((D ^ m) (C e)))) = 0 := by
      intro e φ
      apply eq_zero_of_infinite_isRoot
      have hfin : Set.Finite {z : ℝ | IsRoot D.charpoly z} :=
        finite_setOfPred_isRoot (LinearMap.charpoly_monic D).ne_zero
      refine Set.Infinite.mono ?_ hfin.infinite_compl
      intro z hz
      exact hev e φ z hz
    have hall : ∀ s, s < finrank ℝ F → ∀ (e : E) (φ : Module.Dual ℝ E),
        φ (B ((D ^ s) (C e))) = 0 := by
      intro s
      induction s using Nat.strong_induction_on with
      | _ s ih =>
        intro hs e φ
        have := coeff_extract D.charpoly.coeff (finrank ℝ F)
          (fun m => φ (B ((D ^ m) (C e)))) hcq s hs
          (fun m hm => ih m hm (by omega) e φ)
        rw [hzero e φ, coeff_zero] at this
        exact this.symm
    ext e
    have := (Module.forall_dual_apply_eq_zero_iff ℝ (B ((D ^ j) (C e)))).mp (hall j hj e)
    simpa [moment] using this
  · intro hm z hz e y hy
    have hall := (moment_horizon B D C).2 hm
    rw [solve_unique D z hz (C e) y hy, map_smul]
    unfold Snum
    rw [LinearMap.sum_apply, map_sum, Finset.sum_eq_zero, smul_zero]
    intro m _
    have := LinearMap.congr_fun (hall m) e
    simp only [moment, LinearMap.comp_apply, LinearMap.zero_apply] at this
    rw [LinearMap.smul_apply, map_smul, this, smul_zero]

/-- **5.5, sharpness.** The nilpotent shift on five sites (`D eᵢ = eᵢ₊₁`), read in at site `0`
and out at site `4`, has `B Dʲ C = (Dʲ)₄₀ = 0` for `j ≤ 3` and `B D⁴ C = 1`: the first `q − 1`
Markov parameters can vanish while the transfer is not silent. -/
def shift5 : Matrix (Fin 5) (Fin 5) ℤ := Matrix.of fun i j => if (i : ℕ) = j + 1 then 1 else 0

theorem shift5_moments : (∀ j < 4, (shift5 ^ j) 4 0 = 0) ∧ (shift5 ^ 4) 4 0 = 1 := by
  decide

end Transfer

end VOTKP.Memory
