/-
VOTKP §15.3, Theorem 15.4: scale blindness (Jeromie Beasley).

Take a Coulomb Hamiltonian `H = Σ p²/2m + V` on a configuration space `E`, and multiply every mass
by `λ > 0`. Writing the coordinate scale `r = r'/λ`, the kinetic term scales by `λ²/λ = λ` and
the Coulomb term, homogeneous of degree `−1`, by `λ`, so `H_λ` is unitarily equivalent to `λH`:
every energy scales by `λ` and every ratio `IE_{k+1}/IE_k` is unchanged (`Smith.scale_blind`).

The kinetic operator is written with one mass per coordinate direction `b k` (three directions per
particle), `(Tψ)(x) = −Σₖ (ℏ²/2mₖ) ∂²_{bₖ}ψ(x)`. The theorem `scale_blindness` is the pointwise
intertwining: if `Hψ = Eψ`, then `φ(x) = ψ(λx)` satisfies `H_λ φ = λE φ`. Any potential with
`V(λx) = λ⁻¹V(x)` qualifies; `coulomb_homogeneous` shows every pair-Coulomb sum does.

The dilation is unitary on `L²`: with `n = dim E` and an additive Haar measure,
`(U_λ f)(x) = λ^{n/2} f(λx)` preserves every inner product `∫ conj f · g`
(`dilation_inner`, from Mathlib's `integral_comp_smul_of_nonneg`), and `U_{1/λ}` inverts it
(`dilation_inverse`).
Developed with AI assistance.
-/
import Mathlib

namespace VOTKP.Scaling

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι]

/-- `(T_m ψ)(x) = −Σₖ (ℏ²/2mₖ) ∂²_{bₖ} ψ(x)`. -/
noncomputable def kinetic (hbar : ℝ) (m : ι → ℝ) (b : ι → E) (ψ : E → ℂ) (x : E) : ℂ :=
  -∑ k, (hbar ^ 2 / (2 * m k)) • iteratedFDeriv ℝ 2 ψ x (fun _ => b k)

/-- `(Hψ)(x) = (T_m ψ)(x) + V(x) ψ(x)`. -/
noncomputable def hamiltonian (hbar : ℝ) (m : ι → ℝ) (b : ι → E) (V : E → ℝ) (ψ : E → ℂ)
    (x : E) : ℂ :=
  kinetic hbar m b ψ x + (V x : ℂ) * ψ x

/-- A sum of pair Coulomb terms `V(x) = Σₚ Qₚ/‖Lₚ x‖`, `Lₚ` the relative coordinate of pair `p`
and `Qₚ = qᵢqⱼ/(4πε₀)`. -/
noncomputable def coulomb {P : Type*} [Fintype P] (Q : P → ℝ) (L : P → E →L[ℝ] E) (x : E) : ℝ :=
  ∑ p, Q p / ‖L p x‖

/-- Second derivatives scale by `λ²` under the dilation `x ↦ λx`. -/
lemma iteratedFDeriv_two_dilate (ψ : E → ℂ) (hψ : ContDiff ℝ 2 ψ) (l : ℝ) (x v : E) :
    iteratedFDeriv ℝ 2 (fun y => ψ (l • y)) x (fun _ => v)
      = (l ^ 2) • iteratedFDeriv ℝ 2 ψ (l • x) (fun _ => v) := by
  have hcomp : (fun y => ψ (l • y)) = ψ ∘ (l • ContinuousLinearMap.id ℝ E) := by
    funext y
    simp
  rw [hcomp, ContinuousLinearMap.iteratedFDeriv_comp_right (i := 2) _ hψ x (by norm_num),
    ContinuousMultilinearMap.compContinuousLinearMap_apply]
  have hv : (fun i : Fin 2 => (l • ContinuousLinearMap.id ℝ E) ((fun _ => v) i))
      = fun i => (fun _ : Fin 2 => l) i • (fun _ : Fin 2 => v) i := by
    funext i
    simp
  rw [hv, ContinuousMultilinearMap.map_smul_univ]
  simp

/-- **Theorem 15.4, the potential.** A pair-Coulomb sum is homogeneous of degree `−1`. -/
theorem coulomb_homogeneous {P : Type*} [Fintype P] (Q : P → ℝ) (L : P → E →L[ℝ] E)
    (l : ℝ) (hl : 0 < l) (x : E) : coulomb Q L (l • x) = l⁻¹ * coulomb Q L x := by
  unfold coulomb
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hl]
  ring

lemma mass_coefficient (hbar l mk : ℝ) (hl : 0 < l) :
    hbar ^ 2 / (2 * (l * mk)) * l ^ 2 = l * (hbar ^ 2 / (2 * mk)) := by
  by_cases hm : mk = 0
  · simp [hm]
  · have hl0 : l ≠ 0 := hl.ne'
    field_simp
    try ring

/-- **Theorem 15.4, the kinetic term.** With every mass multiplied by `λ`, the kinetic operator on
`ψ(λ·)` is `λ` times the original kinetic operator at `λx`. -/
theorem kinetic_scaling (hbar : ℝ) (m : ι → ℝ) (b : ι → E) (ψ : E → ℂ) (hψ : ContDiff ℝ 2 ψ)
    (l : ℝ) (hl : 0 < l) (x : E) :
    kinetic hbar (fun k => l * m k) b (fun y => ψ (l • y)) x
      = (l : ℂ) * kinetic hbar m b ψ (l • x) := by
  unfold kinetic
  rw [mul_neg, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [iteratedFDeriv_two_dilate ψ hψ l x (b k), smul_smul, mass_coefficient hbar l (m k) hl,
    Complex.real_smul, Complex.real_smul]
  push_cast
  ring

/-- **Theorem 15.4, scale blindness.** If `Hψ = Eψ` with a potential homogeneous of degree `−1`,
then `φ(x) = ψ(λx)` satisfies `H_λ φ = λE φ`, where `H_λ` has every mass multiplied by `λ`. -/
theorem scale_blindness (hbar : ℝ) (m : ι → ℝ) (b : ι → E) (V : E → ℝ) (l : ℝ) (hl : 0 < l)
    (hV : ∀ x, V (l • x) = l⁻¹ * V x) (ψ : E → ℂ) (hψ : ContDiff ℝ 2 ψ) (En : ℂ)
    (heig : ∀ y, hamiltonian hbar m b V ψ y = En * ψ y) (x : E) :
    hamiltonian hbar (fun k => l * m k) b V (fun y => ψ (l • y)) x = (l * En) * ψ (l • x) := by
  have hl0 : l ≠ 0 := hl.ne'
  have hVx : V x = l * V (l • x) := by
    rw [hV x]
    field_simp
  have h := heig (l • x)
  unfold hamiltonian at h ⊢
  rw [kinetic_scaling hbar m b ψ hψ l hl x, hVx]
  push_cast
  linear_combination (l : ℂ) * h

/-! ## The dilation is unitary -/

section Unitary

open MeasureTheory Module ComplexConjugate

variable [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

/-- `(U_λ f)(x) = λ^{n/2} f(λx)`, `n = dim E`. -/
noncomputable def dilation (l : ℝ) (f : E → ℂ) (x : E) : ℂ :=
  ((Real.sqrt (l ^ finrank ℝ E) : ℝ) : ℂ) * f (l • x)

/-- **Theorem 15.4, unitarity.** For `λ > 0` the dilation preserves the `L²` inner product
`∫ conj f · g` with respect to any additive Haar measure. -/
theorem dilation_inner (μ : Measure E) [μ.IsAddHaarMeasure] (l : ℝ) (hl : 0 < l)
    (f g : E → ℂ) :
    ∫ x, conj (dilation l f x) * dilation l g x ∂μ = ∫ x, conj (f x) * g x ∂μ := by
  have ha : (0 : ℝ) ≤ l ^ finrank ℝ E := pow_nonneg hl.le _
  have ha0 : (l ^ finrank ℝ E : ℝ) ≠ 0 := pow_ne_zero _ hl.ne'
  have hs : ((Real.sqrt (l ^ finrank ℝ E) : ℝ) : ℂ) * ((Real.sqrt (l ^ finrank ℝ E) : ℝ) : ℂ)
      = ((l ^ finrank ℝ E : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt ha]
  have key : ∀ x, conj (dilation l f x) * dilation l g x
      = ((l ^ finrank ℝ E : ℝ) : ℂ) * (conj (f (l • x)) * g (l • x)) := by
    intro x
    simp only [dilation, map_mul, Complex.conj_ofReal]
    rw [← hs]
    ring
  simp_rw [key]
  have hc := Measure.integral_comp_smul_of_nonneg μ (fun y => conj (f y) * g y) l (hR := hl.le)
  rw [integral_const_mul, show (∫ x, conj (f (l • x)) * g (l • x) ∂μ)
      = (l ^ finrank ℝ E)⁻¹ • ∫ y, conj (f y) * g y ∂μ from hc]
  rw [Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ ha0,
    Complex.ofReal_one, one_mul]

/-- **Theorem 15.4, unitarity.** In particular the dilation preserves the `L²` norm. -/
theorem dilation_norm_sq (μ : Measure E) [μ.IsAddHaarMeasure] (l : ℝ) (hl : 0 < l)
    (f : E → ℂ) :
    ∫ x, conj (dilation l f x) * dilation l f x ∂μ = ∫ x, conj (f x) * f x ∂μ :=
  dilation_inner μ l hl f f

/-- **Theorem 15.4, unitarity.** `U_{1/λ}` inverts `U_λ`, so the dilation is onto. -/
theorem dilation_inverse (l : ℝ) (hl : 0 < l) (f : E → ℂ) (x : E) :
    dilation l⁻¹ (dilation l f) x = f x := by
  have ha : (0 : ℝ) ≤ l ^ finrank ℝ E := pow_nonneg hl.le _
  have ha0 : (l ^ finrank ℝ E : ℝ) ≠ 0 := pow_ne_zero _ hl.ne'
  simp only [dilation, smul_smul, mul_inv_cancel₀ hl.ne', one_smul]
  rw [← mul_assoc, ← Complex.ofReal_mul, inv_pow, ← Real.sqrt_mul (inv_nonneg.2 ha),
    inv_mul_cancel₀ ha0, Real.sqrt_one, Complex.ofReal_one, one_mul]

end Unitary

end VOTKP.Scaling
