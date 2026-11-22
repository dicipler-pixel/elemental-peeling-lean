import Mathlib
import LoopWall.PeelPotential
import LoopWall.ScalarLedger

/-!
# The damped phase and the logarithmic ledger

Direction B7 of the fifth round.  The damping law `t'' = -γ t'` has the explicit solution
`t τ = t₀ + (ω/γ)(1 - exp (-γτ))`, so that the phase rate is `ω exp (-γτ)` and decays to zero.
Composing it with the peel and the library's ledger `φled` gives the damped peel equation of
motion `Γ' = (ω/2) exp (-γτ)(1 - Γ²)` and the exact ledger rate `S' = (ω/2) exp (-γτ) Γ`; on the
nonnegative branch the ledger is strictly increasing in forward time, it passes the library's
exact wall value `(1/2) log 2` strictly at any wall crossing, and it converges to the finite
endpoint `log cosh ((t₀ + ω/γ)/2)`.  Damping does not remove the wall; it dates it.

`hasDerivAt_tanh_aux` and `hasDerivAt_log_cosh_aux` are proved here because this Mathlib snapshot
exports no named derivative for `tanh` or `log ∘ cosh`; the first is the quotient rule on
`sinh/cosh`, the second the chain rule with `cosh > 0`.

Written in the fifth parallel formalization round (swarm `smws70oju`, direction m8), recompiled and
reviewed here; namespace, header and imports kept, nothing else changed.  It is the first module in
this layer that imports another project module (`PeelPotential`, `ScalarLedger`) rather than
Mathlib alone, and `LoopWall.lean` therefore imports it after them.
-/

namespace ElementalPeeling.LoopWall.DampedLedgerBridge

open Filter Set
open ElementalPeeling.LoopWall.PeelPotential

noncomputable section

/-- The phase with initial value `t₀`, initial rate `ω`, and damping `γ`. -/
def dampedPhase (t₀ ω γ τ : ℝ) : ℝ :=
  t₀ + (ω / γ) * (1 - Real.exp (-γ * τ))

/-- The reflection associated with the damped phase. -/
def dampedPeel (t₀ ω γ τ : ℝ) : ℝ :=
  Real.tanh (dampedPhase t₀ ω γ τ / 2)

/-- The library's logarithmic ledger evaluated on the damped reflection. -/
def dampedLedger (t₀ ω γ τ : ℝ) : ℝ :=
  φled (dampedPeel t₀ ω γ τ)

/-- `tanh` has derivative `1 - tanh²` (proved here because this snapshot does
not export the usual named tanh derivative theorem). -/
theorem hasDerivAt_tanh_aux (x : ℝ) :
    HasDerivAt Real.tanh (1 - Real.tanh x ^ 2) x := by
  have hc : Real.cosh x ≠ 0 := ne_of_gt (Real.cosh_pos x)
  have h := (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x) hc
  convert h using 1
  · ext y
    exact Real.tanh_eq_sinh_div_cosh y
  · rw [Real.tanh_eq_sinh_div_cosh, div_pow]
    field_simp [hc]

/-- The phase is the exact integrating-factor solution of exponential damping. -/
theorem hasDerivAt_dampedPhase (t₀ ω γ : ℝ) (hγ : γ ≠ 0) (τ : ℝ) :
    HasDerivAt (dampedPhase t₀ ω γ) (ω * Real.exp (-γ * τ)) τ := by
  have hlin : HasDerivAt (fun u : ℝ => -γ * u) (-γ) τ := by
    convert (hasDerivAt_id τ).const_mul (-γ) using 1 <;> simp
  have hexp : HasDerivAt (fun u : ℝ => Real.exp (-γ * u))
      (Real.exp (-γ * τ) * (-γ)) τ := hlin.exp
  have h := ((hasDerivAt_const τ (1 : ℝ)).sub hexp).const_mul (ω / γ)
  have h' := h.const_add t₀
  convert h' using 1
  · ext u
    rfl
  · field_simp [hγ]
    ring

/-- In derivative notation, the phase rate is exactly `ω exp (-γτ)`. -/
theorem deriv_dampedPhase (t₀ ω γ : ℝ) (hγ : γ ≠ 0) (τ : ℝ) :
    deriv (dampedPhase t₀ ω γ) τ = ω * Real.exp (-γ * τ) :=
  (hasDerivAt_dampedPhase t₀ ω γ hγ τ).deriv

/-- The explicit phase satisfies `t'' = -γ t'`. -/
theorem hasDerivAt_deriv_dampedPhase (t₀ ω γ : ℝ) (hγ : γ ≠ 0) (τ : ℝ) :
    HasDerivAt (fun u => deriv (dampedPhase t₀ ω γ) u)
      (-γ * deriv (dampedPhase t₀ ω γ) τ) τ := by
  have hlin : HasDerivAt (fun u : ℝ => -γ * u) (-γ) τ := by
    convert (hasDerivAt_id τ).const_mul (-γ) using 1 <;> simp
  have hexp : HasDerivAt (fun u : ℝ => Real.exp (-γ * u))
      (Real.exp (-γ * τ) * (-γ)) τ := hlin.exp
  have h := hexp.const_mul ω
  have heq : (fun u => deriv (dampedPhase t₀ ω γ) u) =
      (fun u => ω * Real.exp (-γ * u)) := by
    funext u
    exact deriv_dampedPhase t₀ ω γ hγ u
  rw [heq, deriv_dampedPhase t₀ ω γ hγ τ]
  convert h using 1
  ring

/-- The induced equation of motion for the peel coordinate. -/
theorem hasDerivAt_dampedPeel (t₀ ω γ : ℝ) (hγ : γ ≠ 0) (τ : ℝ) :
    HasDerivAt (dampedPeel t₀ ω γ)
      ((ω / 2) * Real.exp (-γ * τ) * (1 - dampedPeel t₀ ω γ τ ^ 2)) τ := by
  have hp := (hasDerivAt_dampedPhase t₀ ω γ hγ τ).div_const 2
  have h := (hasDerivAt_tanh_aux (dampedPhase t₀ ω γ τ / 2)).comp τ hp
  unfold dampedPeel
  convert h using 1
  · ext u
    rfl
  · ring

/-- Derivative form of the induced peel ODE. -/
theorem deriv_dampedPeel (t₀ ω γ : ℝ) (hγ : γ ≠ 0) (τ : ℝ) :
    deriv (dampedPeel t₀ ω γ) τ =
      (ω / 2) * Real.exp (-γ * τ) * (1 - dampedPeel t₀ ω γ τ ^ 2) :=
  (hasDerivAt_dampedPeel t₀ ω γ hγ τ).deriv

/-- Derivative of `log cosh`, with no restriction on its argument. -/
theorem hasDerivAt_log_cosh_aux (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.log (Real.cosh y)) (Real.tanh x) x := by
  have h := (Real.hasDerivAt_cosh x).log (ne_of_gt (Real.cosh_pos x))
  convert h using 1
  exact Real.tanh_eq_sinh_div_cosh x

/-- On the damped phase, the potential ledger is exactly `log cosh (t/2)`. -/
theorem dampedLedger_eq_log_cosh (t₀ ω γ τ : ℝ) :
    dampedLedger t₀ ω γ τ = Real.log (Real.cosh (dampedPhase t₀ ω γ τ / 2)) := by
  unfold dampedLedger dampedPeel φled
  exact (ElementalPeeling.LoopWall.ScalarLedger.log_cosh_eq_neg_half_log_one_sub_tanh_sq
    (dampedPhase t₀ ω γ τ / 2)).symm

/-- The ledger rate along the damped flow is exponentially damped peel. -/
theorem hasDerivAt_dampedLedger (t₀ ω γ : ℝ) (hγ : γ ≠ 0) (τ : ℝ) :
    HasDerivAt (dampedLedger t₀ ω γ)
      ((ω / 2) * Real.exp (-γ * τ) * dampedPeel t₀ ω γ τ) τ := by
  have hp := (hasDerivAt_dampedPhase t₀ ω γ hγ τ).div_const 2
  have h := (hasDerivAt_log_cosh_aux (dampedPhase t₀ ω γ τ / 2)).comp τ hp
  have heq : dampedLedger t₀ ω γ =
      (fun u => Real.log (Real.cosh (dampedPhase t₀ ω γ u / 2))) := by
    funext u
    exact dampedLedger_eq_log_cosh t₀ ω γ u
  rw [heq]
  unfold dampedPeel
  convert h using 1
  · ext u
    rfl
  · ring

/-- The phase is strictly increasing when its initial rate and damping are positive. -/
theorem strictMono_dampedPhase (t₀ ω γ : ℝ) (hω : 0 < ω) (hγ : 0 < γ) :
    StrictMono (dampedPhase t₀ ω γ) := by
  intro a b hab
  have hlin : -γ * b < -γ * a := by nlinarith
  have he : Real.exp (-γ * b) < Real.exp (-γ * a) := Real.exp_lt_exp.mpr hlin
  have hcoef : 0 < ω / γ := div_pos hω hγ
  have hm := mul_lt_mul_of_pos_left (sub_lt_sub_left he 1) hcoef
  unfold dampedPhase
  linarith

/-- Forward phase is nonnegative on the nonnegative branch. -/
theorem dampedPhase_nonneg (t₀ ω γ τ : ℝ) (ht₀ : 0 ≤ t₀)
    (hω : 0 ≤ ω) (hγ : 0 < γ) (hτ : 0 ≤ τ) : 0 ≤ dampedPhase t₀ ω γ τ := by
  have he : Real.exp (-γ * τ) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hcoef : 0 ≤ ω / γ := div_nonneg hω hγ.le
  have hm : 0 ≤ (ω / γ) * (1 - Real.exp (-γ * τ)) :=
    mul_nonneg hcoef (sub_nonneg.mpr he)
  unfold dampedPhase
  linarith

/-- On the nonnegative phase branch, the ledger strictly increases in forward time. -/
theorem strictMonoOn_dampedLedger (t₀ ω γ : ℝ) (ht₀ : 0 ≤ t₀)
    (hω : 0 < ω) (hγ : 0 < γ) : StrictMonoOn (dampedLedger t₀ ω γ) (Set.Ici 0) := by
  intro a ha b hb hab
  have hpa : 0 ≤ dampedPhase t₀ ω γ a :=
    dampedPhase_nonneg t₀ ω γ a ht₀ hω.le hγ ha
  have hpb : 0 ≤ dampedPhase t₀ ω γ b :=
    dampedPhase_nonneg t₀ ω γ b ht₀ hω.le hγ hb
  have hphase : dampedPhase t₀ ω γ a < dampedPhase t₀ ω γ b :=
    strictMono_dampedPhase t₀ ω γ hω hγ hab
  have hcosh : Real.cosh (dampedPhase t₀ ω γ a / 2) <
      Real.cosh (dampedPhase t₀ ω γ b / 2) :=
    Real.cosh_strictMonoOn (div_nonneg hpa (by norm_num))
      (div_nonneg hpb (by norm_num)) (by linarith)
  rw [dampedLedger_eq_log_cosh, dampedLedger_eq_log_cosh]
  exact Real.log_lt_log (Real.cosh_pos _) hcosh

/-- In particular the ledger is monotone (and not merely convergent) in forward time. -/
theorem monotoneOn_dampedLedger (t₀ ω γ : ℝ) (ht₀ : 0 ≤ t₀)
    (hω : 0 < ω) (hγ : 0 < γ) : MonotoneOn (dampedLedger t₀ ω γ) (Set.Ici 0) :=
  (strictMonoOn_dampedLedger t₀ ω γ ht₀ hω hγ).monotoneOn

/-- Crossing the positive wall strictly increases the ledger through its exact
wall value `log 2 / 2`. -/
theorem ledger_strict_increase_across_wall (t₀ ω γ τw a b : ℝ)
    (ht₀ : 0 ≤ t₀) (hω : 0 < ω) (hγ : 0 < γ)
    (hwall : dampedPeel t₀ ω γ τw = wall)
    (ha : 0 ≤ a) (hτw : 0 ≤ τw) (hb : 0 ≤ b) (haτ : a < τw) (hτb : τw < b) :
    dampedLedger t₀ ω γ a < (1 / 2 : ℝ) * Real.log 2 ∧
      (1 / 2 : ℝ) * Real.log 2 < dampedLedger t₀ ω γ b := by
  have hmono := strictMonoOn_dampedLedger t₀ ω γ ht₀ hω hγ
  have h₁ : dampedLedger t₀ ω γ a < dampedLedger t₀ ω γ τw :=
    hmono ha hτw haτ
  have h₂ : dampedLedger t₀ ω γ τw < dampedLedger t₀ ω γ b :=
    hmono hτw hb hτb
  have hw : dampedLedger t₀ ω γ τw = (1 / 2 : ℝ) * Real.log 2 := by
    unfold dampedLedger
    rw [hwall]
    exact φled_wall
  rw [hw] at h₁ h₂
  exact ⟨h₁, h₂⟩


/-- Damping drives the phase to the finite endpoint `t₀ + ω / γ`. -/
theorem tendsto_dampedPhase (t₀ ω γ : ℝ) (hγ : 0 < γ) :
    Tendsto (dampedPhase t₀ ω γ) atTop (nhds (t₀ + ω / γ)) := by
  have hlin : Tendsto (fun τ : ℝ => γ * τ) atTop atTop :=
    Filter.Tendsto.const_mul_atTop hγ tendsto_id
  have he : Tendsto (fun τ : ℝ => Real.exp (-γ * τ)) atTop (nhds 0) := by
    have h := Real.tendsto_exp_neg_atTop_nhds_zero.comp hlin
    simpa [Function.comp_def, neg_mul] using h
  have hone : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
  have ht₀ : Tendsto (fun _ : ℝ => t₀) atTop (nhds t₀) := tendsto_const_nhds
  have h := ht₀.add ((hone.sub he).const_mul (ω / γ))
  unfold dampedPhase
  simpa [neg_mul] using h

/-- The peel itself converges to the reflection of the finite phase endpoint. -/
theorem tendsto_dampedPeel (t₀ ω γ : ℝ) (hγ : 0 < γ) :
    Tendsto (dampedPeel t₀ ω γ) atTop
      (nhds (Real.tanh ((t₀ + ω / γ) / 2))) := by
  have ht : Differentiable ℝ Real.tanh := fun x => (hasDerivAt_tanh_aux x).differentiableAt
  have hc : ContinuousAt Real.tanh ((t₀ + ω / γ) / 2) := ht.continuous.continuousAt
  have h := hc.tendsto.comp ((tendsto_dampedPhase t₀ ω γ hγ).div_const 2)
  unfold dampedPeel
  simpa only [Function.comp_def] using h

/-- The damped ledger converges to an explicit finite value. -/
theorem tendsto_dampedLedger (t₀ ω γ : ℝ) (hγ : 0 < γ) :
    Tendsto (dampedLedger t₀ ω γ) atTop
      (nhds (Real.log (Real.cosh ((t₀ + ω / γ) / 2)))) := by
  have hd : Differentiable ℝ (fun x : ℝ => Real.log (Real.cosh x)) :=
    fun x => (hasDerivAt_log_cosh_aux x).differentiableAt
  have hc : ContinuousAt (fun x : ℝ => Real.log (Real.cosh x))
      ((t₀ + ω / γ) / 2) := hd.continuous.continuousAt
  have h := hc.tendsto.comp ((tendsto_dampedPhase t₀ ω γ hγ).div_const 2)
  convert h using 1
  ext u
  exact dampedLedger_eq_log_cosh t₀ ω γ u

/-- The same endpoint written directly as the library's logarithmic ledger. -/
theorem tendsto_dampedLedger_φled (t₀ ω γ : ℝ) (hγ : 0 < γ) :
    Tendsto (dampedLedger t₀ ω γ) atTop
      (nhds (φled (Real.tanh ((t₀ + ω / γ) / 2)))) := by
  have h := tendsto_dampedLedger t₀ ω γ hγ
  have heq : φled (Real.tanh ((t₀ + ω / γ) / 2)) =
      Real.log (Real.cosh ((t₀ + ω / γ) / 2)) := by
    unfold φled
    exact (ElementalPeeling.LoopWall.ScalarLedger.log_cosh_eq_neg_half_log_one_sub_tanh_sq
      ((t₀ + ω / γ) / 2)).symm
  rwa [heq]

end

end ElementalPeeling.LoopWall.DampedLedgerBridge
