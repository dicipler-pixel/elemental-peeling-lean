import Mathlib
import LoopWall.PeelPotential
import LoopWall.ScalarLedger

/-!
Direction B6 of the fifth round (swarm `smws70oju`, member m7). Coupling: when the frequency depends
on the peel, the oscillator's energy is not conserved — its rate is `m ω ω'(Γ) q² Γ'` — and on an open
interval with `q` and `ω∘Γ` nonvanishing, energy constancy is *equivalent* to constancy of `ω∘Γ`.
Witnesses show that global frequency constancy is not needed for conservation on an interval, and that
the frequency work is genuinely nonzero in examples. So the one-way determination of the potential
holds for a frozen frequency, and fails as soon as the frequency reads the peel.

Written in the fifth parallel formalization round and recompiled here before acceptance;
imports hoisted, namespace prefixed to `ElementalPeeling.LoopWall`, nothing else changed.
-/

/-!
# Energy balance for a peel-dependent oscillator frequency

The harmonic energy is conserved in the coupled model only after the work done by
changing the frequency is included. We also compute the derivative of the scalar
ledger separately: it is a function of the peel path, not the mechanical energy.
-/

namespace ElementalPeeling.LoopWall.PhaseEnergyBalance

open ElementalPeeling.LoopWall.PeelPotential

noncomputable section

/-- The instantaneous harmonic energy when the frequency is read from the peel. -/
def phaseEnergy (m : ℝ) (ω Γ q p : ℝ → ℝ) : ℝ → ℝ :=
  fun s => harmonicEnergy m (ω (Γ s)) (q s) (p s)

/-- Exact local energy balance for the phase-dependent canonical equations. -/
theorem hasDerivAt_phaseEnergy
    {m : ℝ} {ω Γ q p : ℝ → ℝ} {s : ℝ} (hm : 0 < m)
    (hω : DifferentiableAt ℝ ω (Γ s)) (hΓ : DifferentiableAt ℝ Γ s)
    (hq : DifferentiableAt ℝ q s) (hp : DifferentiableAt ℝ p s)
    (hqs : deriv q s = p s / m)
    (hps : deriv p s = -(m * (ω (Γ s)) ^ 2 * q s)) :
    HasDerivAt (phaseEnergy m ω Γ q p)
      (m * ω (Γ s) * deriv ω (Γ s) * q s ^ 2 * deriv Γ s) s := by
  have hm0 : m ≠ 0 := ne_of_gt hm
  have hωΓ : HasDerivAt (fun u => ω (Γ u))
      (deriv ω (Γ s) * deriv Γ s) s := by
    simpa only [Function.comp_def] using hω.hasDerivAt.comp s hΓ.hasDerivAt
  have hkin : HasDerivAt (fun u => p u ^ 2 / (2 * m))
      (p s * deriv p s / m) s := by
    have h := (hp.hasDerivAt.pow 2).div_const (2 * m)
    convert h using 1
    field_simp [hm0]
    ring
  have hpot : HasDerivAt (fun u => V m (ω (Γ u)) (q u))
      ((1 / 2 : ℝ) * m *
        ((2 * ω (Γ s) * (deriv ω (Γ s) * deriv Γ s)) * q s ^ 2 +
          (ω (Γ s)) ^ 2 * (2 * q s * deriv q s))) s := by
    have h := ((hωΓ.pow 2).mul (hq.hasDerivAt.pow 2)).const_mul ((1 / 2 : ℝ) * m)
    convert h using 1
    · ext u
      simp only [V, Pi.pow_apply, Pi.mul_apply]
      ring
    · norm_num
  have hsum := hkin.add hpot
  unfold phaseEnergy harmonicEnergy
  convert hsum using 1
  rw [hqs, hps]
  field_simp [hm0]
  ring

/-- The derivative form of the coupled energy balance. -/
theorem deriv_phaseEnergy
    {m : ℝ} {ω Γ q p : ℝ → ℝ} (hm : 0 < m)
    (hω : Differentiable ℝ ω) (hΓ : Differentiable ℝ Γ)
    (hq : Differentiable ℝ q) (hp : Differentiable ℝ p)
    (hmodel : PhaseDependentCanonicalEquations m ω Γ q p) (s : ℝ) :
    deriv (phaseEnergy m ω Γ q p) s =
      m * ω (Γ s) * deriv ω (Γ s) * q s ^ 2 * deriv Γ s := by
  exact (hasDerivAt_phaseEnergy hm (hω (Γ s)) (hΓ s) (hq s) (hp s)
    (hmodel s).1 (hmodel s).2).deriv

/-- At a fixed time, energy is stationary exactly when the frequency-work term vanishes. -/
theorem phaseEnergy_stationary_iff
    {m : ℝ} {ω Γ q p : ℝ → ℝ} {s : ℝ} (hm : 0 < m)
    (hω : DifferentiableAt ℝ ω (Γ s)) (hΓ : DifferentiableAt ℝ Γ s)
    (hq : DifferentiableAt ℝ q s) (hp : DifferentiableAt ℝ p s)
    (hqs : deriv q s = p s / m)
    (hps : deriv p s = -(m * (ω (Γ s)) ^ 2 * q s)) :
    deriv (phaseEnergy m ω Γ q p) s = 0 ↔
      m * ω (Γ s) * deriv ω (Γ s) * q s ^ 2 * deriv Γ s = 0 := by
  rw [(hasDerivAt_phaseEnergy hm hω hΓ hq hp hqs hps).deriv]

/-- The same balance, with the total derivative of the frequency along the peel path. -/
theorem deriv_phaseEnergy_eq_frequencyWork
    {m : ℝ} {ω Γ q p : ℝ → ℝ} (hm : 0 < m)
    (hω : Differentiable ℝ ω) (hΓ : Differentiable ℝ Γ)
    (hq : Differentiable ℝ q) (hp : Differentiable ℝ p)
    (hmodel : PhaseDependentCanonicalEquations m ω Γ q p) (s : ℝ) :
    deriv (phaseEnergy m ω Γ q p) s =
      (m * ω (Γ s) * q s ^ 2) * deriv (fun u => ω (Γ u)) s := by
  have hchain : HasDerivAt (fun u => ω (Γ u))
      (deriv ω (Γ s) * deriv Γ s) s := by
    simpa only [Function.comp_def] using
      (hω (Γ s)).hasDerivAt.comp s (hΓ s).hasDerivAt
  rw [deriv_phaseEnergy hm hω hΓ hq hp hmodel, hchain.deriv]
  ring

/-- On any open preconnected time interval where configuration and frequency do not
vanish, constancy of mechanical energy is exactly constancy of frequency along
that peel trajectory. -/
theorem phaseEnergy_constOn_iff_frequency_comp_constOn
    {m : ℝ} {ω Γ q p : ℝ → ℝ} {I : Set ℝ}
    (hIopen : IsOpen I) (hIpre : IsPreconnected I) (hm : 0 < m)
    (hω : Differentiable ℝ ω) (hΓ : Differentiable ℝ Γ)
    (hq : Differentiable ℝ q) (hp : Differentiable ℝ p)
    (hmodel : PhaseDependentCanonicalEquations m ω Γ q p)
    (hq0 : ∀ s ∈ I, q s ≠ 0) (hω0 : ∀ s ∈ I, ω (Γ s) ≠ 0) :
    (∀ x ∈ I, ∀ y ∈ I, phaseEnergy m ω Γ q p x = phaseEnergy m ω Γ q p y) ↔
      (∀ x ∈ I, ∀ y ∈ I, ω (Γ x) = ω (Γ y)) := by
  constructor
  · intro hE x hx y hy
    have hEder : I.EqOn (deriv (phaseEnergy m ω Γ q p)) 0 := by
      intro s hs
      have heq : (fun _ : ℝ => phaseEnergy m ω Γ q p s) =ᶠ[nhds s]
          phaseEnergy m ω Γ q p := by
        filter_upwards [hIopen.mem_nhds hs] with u hu
        exact (hE u hu s hs).symm
      simpa using heq.deriv_eq.symm
    apply hIopen.is_const_of_deriv_eq_zero (f := fun u => ω (Γ u)) hIpre
      (hω.comp hΓ).differentiableOn _ hx hy
    intro s hs
    have hchain : HasDerivAt (fun u => ω (Γ u))
        (deriv ω (Γ s) * deriv Γ s) s := by
      simpa only [Function.comp_def] using
        (hω (Γ s)).hasDerivAt.comp s (hΓ s).hasDerivAt
    rw [hchain.deriv]
    have hz : m * ω (Γ s) * deriv ω (Γ s) * q s ^ 2 * deriv Γ s = 0 := by
      rw [← deriv_phaseEnergy hm hω hΓ hq hp hmodel]
      exact hEder hs
    have hfactor : m * ω (Γ s) * q s ^ 2 ≠ 0 :=
      mul_ne_zero (mul_ne_zero (ne_of_gt hm) (hω0 s hs)) (pow_ne_zero 2 (hq0 s hs))
    have hprod : (m * ω (Γ s) * q s ^ 2) *
        (deriv ω (Γ s) * deriv Γ s) = 0 := by
      calc
        (m * ω (Γ s) * q s ^ 2) * (deriv ω (Γ s) * deriv Γ s) =
            m * ω (Γ s) * deriv ω (Γ s) * q s ^ 2 * deriv Γ s := by ring
        _ = 0 := hz
    exact (mul_eq_zero.mp hprod).resolve_left hfactor
  · intro hW x hx y hy
    have hWder : I.EqOn (deriv (fun u => ω (Γ u))) 0 := by
      intro s hs
      have heq : (fun _ : ℝ => ω (Γ s)) =ᶠ[nhds s] (fun u => ω (Γ u)) := by
        filter_upwards [hIopen.mem_nhds hs] with u hu
        exact (hW u hu s hs).symm
      simpa using heq.deriv_eq.symm
    apply hIopen.is_const_of_deriv_eq_zero (f := phaseEnergy m ω Γ q p) hIpre _ _ hx hy
    · intro s hs
      exact (hasDerivAt_phaseEnergy hm (hω (Γ s)) (hΓ s) (hq s) (hp s)
        (hmodel s).1 (hmodel s).2).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [deriv_phaseEnergy_eq_frequencyWork hm hω hΓ hq hp hmodel, hWder hs]
      simp

/-- A frequency constant along the peel path reduces the coupled model to the frozen one. -/
theorem phaseDependent_eq_frozen_of_frequency_comp_const
    {m c : ℝ} {ω Γ q p : ℝ → ℝ} (hωΓ : ∀ s, ω (Γ s) = c) :
    PhaseDependentCanonicalEquations m ω Γ q p ↔
      FrozenCanonicalEquations m c q p := by
  unfold PhaseDependentCanonicalEquations FrozenCanonicalEquations
  simp_rw [hωΓ]

/-- Chain rule for the scalar ledger along an arbitrary peel trajectory. -/
theorem hasDerivAt_ledger_comp
    {Γ : ℝ → ℝ} {s : ℝ} (hΓ : DifferentiableAt ℝ Γ s)
    (habs : |Γ s| < 1) :
    HasDerivAt (fun u => φled (Γ u))
      ((Γ s / (1 - Γ s ^ 2)) * deriv Γ s) s := by
  simpa only [Function.comp_def] using
    (hasDerivAt_φled habs).comp s hΓ.hasDerivAt

/-- The ledger rate vanishes at a point precisely when `Γ * Γ'` vanishes there. -/
theorem ledger_comp_stationary_iff
    {Γ : ℝ → ℝ} {s : ℝ} (hΓ : DifferentiableAt ℝ Γ s)
    (habs : |Γ s| < 1) :
    deriv (fun u => φled (Γ u)) s = 0 ↔ Γ s * deriv Γ s = 0 := by
  rw [(hasDerivAt_ledger_comp hΓ habs).deriv]
  have hden : 1 - Γ s ^ 2 ≠ 0 :=
    ne_of_gt (sub_pos.mpr (sq_lt_one_of_abs_lt_one habs))
  constructor
  · intro h
    have hdiv : Γ s / (1 - Γ s ^ 2) = 0 ∨ deriv Γ s = 0 := mul_eq_zero.mp h
    rcases hdiv with hdiv | hvel
    · have hg : Γ s = 0 := (div_eq_zero_iff).mp hdiv |>.resolve_right hden
      rw [hg, zero_mul]
    · rw [hvel, mul_zero]
  · intro h
    rcases mul_eq_zero.mp h with hg | hvel
    · rw [hg]
      simp
    · rw [hvel, mul_zero]

/-- In particular, a moving nonzero peel cannot have a stationary scalar ledger.
This statement involves neither the frequency nor the mechanical energy. -/
theorem ledger_comp_not_stationary
    {Γ : ℝ → ℝ} {s : ℝ} (hΓ : DifferentiableAt ℝ Γ s)
    (habs : |Γ s| < 1) (hg : Γ s ≠ 0) (hvel : deriv Γ s ≠ 0) :
    deriv (fun u => φled (Γ u)) s ≠ 0 := by
  intro hz
  exact mul_ne_zero hg hvel ((ledger_comp_stationary_iff hΓ habs).mp hz)

/-- Global constancy of `ω` is too strong a conclusion.  Here `ω x = x + 1`
is nonconstant globally, but the frozen peel `Γ = 0` sees only frequency one,
and the usual unit oscillator has constant energy. -/
theorem conserved_energy_does_not_force_global_frequency_constancy :
    ∃ ω Γ q p : ℝ → ℝ,
      Differentiable ℝ ω ∧ Differentiable ℝ Γ ∧
      Differentiable ℝ q ∧ Differentiable ℝ p ∧
      PhaseDependentCanonicalEquations 1 ω Γ q p ∧
      (∀ x y, phaseEnergy 1 ω Γ q p x = phaseEnergy 1 ω Γ q p y) ∧
      ¬ (∀ x y, ω x = ω y) := by
  refine ⟨fun x => x + 1, fun _ => 0, Real.cos, fun s => -Real.sin s,
    by fun_prop, by fun_prop, Real.differentiable_cos, Real.differentiable_sin.neg,
    ?_, ?_, ?_⟩
  · intro s
    constructor
    · simp
    · simp
  · have hval (u : ℝ) :
        phaseEnergy 1 (fun x => x + 1) (fun _ => 0) Real.cos
          (fun s => -Real.sin s) u = (1 / 2 : ℝ) := by
      have h := Real.sin_sq_add_cos_sq u
      norm_num [phaseEnergy, harmonicEnergy, V]
      nlinarith
    intro x y
    rw [hval x, hval y]
  · intro h
    have h01 := h 0 1
    norm_num at h01

/-- The variable-frequency branch is non-vacuous: these paths satisfy the coupled
canonical equations at time zero, while the frequency changes along the peel and
the exact energy derivative there is one. -/
theorem nonzero_frequency_work_witness :
    ∃ ω Γ q p : ℝ → ℝ,
      DifferentiableAt ℝ ω (Γ 0) ∧ DifferentiableAt ℝ Γ 0 ∧
      DifferentiableAt ℝ q 0 ∧ DifferentiableAt ℝ p 0 ∧
      deriv q 0 = p 0 / 1 ∧
      deriv p 0 = -(1 * (ω (Γ 0)) ^ 2 * q 0) ∧
      deriv (phaseEnergy 1 ω Γ q p) 0 = 1 ∧
      ω (Γ 0) ≠ ω (Γ 1) := by
  have hΓ : HasDerivAt (fun u : ℝ => u + 1) 1 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).add_const 1
  have hq : HasDerivAt (fun u : ℝ => 1 + u - u ^ 2 / 2) 1 0 := by
    have h := ((hasDerivAt_const (0 : ℝ) (1 : ℝ)).add (hasDerivAt_id 0)).sub
      (((hasDerivAt_id (0 : ℝ)).pow 2).div_const 2)
    convert h using 1
    · ext u
      simp only [Pi.sub_apply, Pi.add_apply, Pi.pow_apply, id_eq]
    · norm_num
  have hp : HasDerivAt (fun u : ℝ => 1 - u) (-1) 0 := by
    have h := (hasDerivAt_id (0 : ℝ)).neg.add_const (1 : ℝ)
    convert h using 1
    ext u
    simp only [Pi.neg_apply, id_eq]
    ring
  have hω : DifferentiableAt ℝ (fun x : ℝ => x) ((fun u : ℝ => u + 1) 0) := by
    simp
  refine ⟨fun x : ℝ => x, fun u : ℝ => u + 1,
    fun u : ℝ => 1 + u - u ^ 2 / 2, fun u : ℝ => 1 - u,
    hω, hΓ.differentiableAt, hq.differentiableAt, hp.differentiableAt, ?_, ?_, ?_, ?_⟩
  · rw [hq.deriv]
    norm_num
  · rw [hp.deriv]
    norm_num
  · have he := hasDerivAt_phaseEnergy (m := 1) (s := 0)
      (ω := fun x : ℝ => x) (Γ := fun u : ℝ => u + 1)
      (q := fun u : ℝ => 1 + u - u ^ 2 / 2) (p := fun u : ℝ => 1 - u)
      zero_lt_one hω hΓ.differentiableAt hq.differentiableAt hp.differentiableAt
      (by rw [hq.deriv]; norm_num) (by rw [hp.deriv]; norm_num)
    rw [he.deriv, hΓ.deriv]
    norm_num
  · norm_num

end
end ElementalPeeling.LoopWall.PhaseEnergyBalance
