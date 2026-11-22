import Mathlib
import LoopWall.PeelPotential
import LoopWall.ChromaticAngle

/-!
Direction B3 of the fifth round (swarm `smws70oju`, member m2). The uniform chromatic angle: the
closed form `Γ = -cos (ωτ + c)`, the harmonic law, the ledger `S = -log |sin φ|`, and the angle
bridge equation `S'' = ω² exp (2S)` with its own first integral and Euler–Lagrange residual. The
density there is `T + U` with `U = -(ω²/2)e^{2S}`, unbounded below — the contrast with the log-ratio
phase in `LoopWall/UniformLogRatio.lean`, whose effective potential is bounded below.

Written in the fifth parallel formalization round and recompiled here before acceptance;
imports hoisted, namespace prefixed to `ElementalPeeling.LoopWall`, nothing else changed.
-/

/-!
# The uniform chromatic-angle bridge

Uniform angular motion, unlike uniform logarithmic spacing, makes the peel a
harmonic coordinate.  On a regular interval (`sin φ ≠ 0`) the scalar ledger is
`-log |sin φ|` and obeys a repulsive exponential equation.  The corresponding
potential is unbounded below and the ledger blows up at the next zero of sine.
-/

namespace ElementalPeeling.LoopWall.UniformAngularBridge

open scoped Topology
open Filter
open ElementalPeeling.LoopWall.PeelPotential

noncomputable section

/-- Linear chromatic phase, with initial phase `c`. -/
def phase (ω c : ℝ) (τ : ℝ) : ℝ := ω * τ + c

/-- The chromatic peel `Γ = -cos φ` along a linear phase. -/
def angularPeel (ω c : ℝ) (τ : ℝ) : ℝ := -Real.cos (phase ω c τ)

/-- The scalar-ledger potential evaluated on the chromatic peel. -/
def angularLedger (ω c : ℝ) (τ : ℝ) : ℝ := φled (angularPeel ω c τ)

/-- Ordinary potential in the ledger coordinate: the Lagrangian is kinetic minus this. -/
def effectivePotential (ω : ℝ) (S : ℝ) : ℝ := -(ω ^ 2 / 2) * Real.exp (2 * S)

/-- Lagrangian whose Euler--Lagrange equation is the angular ledger equation. -/
def angularLagrangian (ω : ℝ) (S v : ℝ) : ℝ := v ^ 2 / 2 - effectivePotential ω S

theorem hasDerivAt_phase (ω c τ : ℝ) : HasDerivAt (phase ω c) ω τ := by
  convert ((hasDerivAt_id τ).const_mul ω).add_const c using 1
  · ext u
    rfl
  · simp

/-- A differentiable phase of constant derivative is exactly the linear phase. -/
theorem eq_phase_of_deriv_eq_const {φ : ℝ → ℝ} {ω : ℝ}
    (hφ : Differentiable ℝ φ) (hφ' : ∀ τ, deriv φ τ = ω) (τ : ℝ) :
    φ τ = phase ω (φ 0) τ := by
  let f : ℝ → ℝ := fun u => φ u - phase ω (φ 0) u
  have hf : Differentiable ℝ f := by
    apply hφ.sub
    intro u
    exact (hasDerivAt_phase ω (φ 0) u).differentiableAt
  have hf' : ∀ u, deriv f u = 0 := by
    intro u
    rw [show deriv f u = deriv φ u - deriv (phase ω (φ 0)) u from
      deriv_sub (hφ u) (hasDerivAt_phase ω (φ 0) u).differentiableAt]
    rw [hφ' u, (hasDerivAt_phase ω (φ 0) u).deriv]
    ring
  have hconst := is_const_of_deriv_eq_zero hf hf' τ 0
  dsimp [f] at hconst
  simp [phase] at hconst
  change φ τ = ω * τ + φ 0
  linarith

/-- Consequently a peel read directly from any uniform phase has the shifted-cosine form. -/
theorem peel_closed_form_of_uniform {φ Γ : ℝ → ℝ} {ω : ℝ}
    (hΓ : ∀ τ, Γ τ = -Real.cos (φ τ))
    (hφ : Differentiable ℝ φ) (hφ' : ∀ τ, deriv φ τ = ω) (τ : ℝ) :
    Γ τ = -Real.cos (ω * τ + φ 0) := by
  rw [hΓ τ, eq_phase_of_deriv_eq_const hφ hφ' τ]
  rfl

/-- Library colour shares realise precisely the peel used in this file. -/
theorem chromatic_peel_eq_angularPeel {ω m p c : ℝ} (hm : 0 < m) (hp : 0 < p)
    (hshare : ElementalPeeling.LoopWall.ChromaticAngle.shareZero c = m / (m + p)) :
    ElementalPeeling.LoopWall.ChromaticAngle.peel m p = angularPeel ω c 0 := by
  rw [ElementalPeeling.LoopWall.ChromaticAngle.peel_eq_neg_cos hm hp hshare]
  simp only [angularPeel, phase, mul_zero, zero_add]

theorem hasDerivAt_angularPeel (ω c τ : ℝ) :
    HasDerivAt (angularPeel ω c) (ω * Real.sin (phase ω c τ)) τ := by
  have h := (hasDerivAt_phase ω c τ).cos.neg
  convert h using 1
  · ext u
    rfl
  · ring

theorem deriv_angularPeel (ω c τ : ℝ) :
    deriv (angularPeel ω c) τ = ω * Real.sin (phase ω c τ) :=
  (hasDerivAt_angularPeel ω c τ).deriv

/-- The derivative of the peel is again explicit, so the second derivative is harmonic. -/
theorem hasDerivAt_deriv_angularPeel (ω c τ : ℝ) :
    HasDerivAt (deriv (angularPeel ω c)) (ω ^ 2 * Real.cos (phase ω c τ)) τ := by
  have hfun : deriv (angularPeel ω c) =
      fun u => ω * Real.sin (phase ω c u) := by
    funext u
    exact deriv_angularPeel ω c u
  rw [hfun]
  convert (hasDerivAt_phase ω c τ).sin.const_mul ω using 1
  ring

/-- Uniform chromatic phase makes the peel a harmonic coordinate. -/
theorem peel_equation_of_motion (ω c τ : ℝ) :
    deriv (deriv (angularPeel ω c)) τ = -ω ^ 2 * angularPeel ω c τ := by
  rw [(hasDerivAt_deriv_angularPeel ω c τ).deriv]
  simp [angularPeel]

/-- Harmonic peel energy is exactly the complementary peel square. -/
theorem peel_velocity_sq (ω c τ : ℝ) :
    (deriv (angularPeel ω c) τ) ^ 2 = ω ^ 2 * (1 - angularPeel ω c τ ^ 2) := by
  rw [deriv_angularPeel]
  have h := Real.sin_sq_add_cos_sq (phase ω c τ)
  simp only [angularPeel, neg_sq]
  nlinarith

/-- The complementary peel square is the squared sine of the chromatic angle. -/
theorem one_sub_angularPeel_sq (ω c τ : ℝ) :
    1 - angularPeel ω c τ ^ 2 = Real.sin (phase ω c τ) ^ 2 := by
  have h := Real.sin_sq_add_cos_sq (phase ω c τ)
  simp only [angularPeel, neg_sq]
  nlinarith

/-- Away from the colour singularities, the angular peel is inside its domain. -/
theorem abs_angularPeel_lt_one {ω c τ : ℝ}
    (hs : Real.sin (phase ω c τ) ≠ 0) : |angularPeel ω c τ| < 1 := by
  rw [← sq_lt_one_iff_abs_lt_one]
  have hcomp := one_sub_angularPeel_sq ω c τ
  have hspos : 0 < Real.sin (phase ω c τ) ^ 2 := sq_pos_of_ne_zero hs
  linarith

/-- The scalar ledger along an angular trajectory is minus log absolute sine. -/
theorem angularLedger_eq_neg_log_abs_sin (ω c τ : ℝ) :
    angularLedger ω c τ = -Real.log |Real.sin (phase ω c τ)| := by
  unfold angularLedger φled
  rw [one_sub_angularPeel_sq, Real.log_pow]
  norm_num [Real.log_abs]
  ring

/-- Twice the ledger is minus the logarithm of squared sine. -/
theorem two_mul_angularLedger (ω c τ : ℝ) :
    2 * angularLedger ω c τ = -Real.log (Real.sin (phase ω c τ) ^ 2) := by
  unfold angularLedger φled
  rw [one_sub_angularPeel_sq, Real.log_pow]
  norm_num
  ring

/-- The exponential in the angular ledger equation is exactly `1 / sin²`. -/
theorem exp_two_mul_angularLedger {ω c τ : ℝ}
    (hs : Real.sin (phase ω c τ) ≠ 0) :
    Real.exp (2 * angularLedger ω c τ) = (Real.sin (phase ω c τ) ^ 2)⁻¹ := by
  rw [two_mul_angularLedger, Real.exp_neg, Real.exp_log (sq_pos_of_ne_zero hs)]

/-- First ledger-velocity law on a regular angular trajectory. -/
theorem hasDerivAt_angularLedger {ω c τ : ℝ}
    (hs : Real.sin (phase ω c τ) ≠ 0) :
    HasDerivAt (angularLedger ω c)
      (-(ω * Real.cos (phase ω c τ) / Real.sin (phase ω c τ))) τ := by
  have h := (hasDerivAt_φled (abs_angularPeel_lt_one hs)).comp τ
    (hasDerivAt_angularPeel ω c τ)
  convert h using 1
  · ext u
    rfl
  · rw [one_sub_angularPeel_sq]
    simp only [angularPeel]
    field_simp [hs]

/-- Derivative of the explicit ledger velocity at a regular point. -/
theorem hasDerivAt_ledgerVelocity {ω c τ : ℝ}
    (hs : Real.sin (phase ω c τ) ≠ 0) :
    HasDerivAt
      (fun u => -(ω * Real.cos (phase ω c u) / Real.sin (phase ω c u)))
      (ω ^ 2 / Real.sin (phase ω c τ) ^ 2) τ := by
  have hcos := (hasDerivAt_phase ω c τ).cos
  have hsin := (hasDerivAt_phase ω c τ).sin
  have hdiv := (hcos.const_mul (-ω)).div hsin hs
  convert hdiv using 1
  · ext u
    simp only [Pi.div_apply]
    ring
  · have htri := Real.sin_sq_add_cos_sq (phase ω c τ)
    field_simp [hs]
    nlinarith

/-- The derivative of `deriv S` exists at every regular angular point. -/
theorem hasDerivAt_deriv_angularLedger {ω c τ : ℝ}
    (hs : Real.sin (phase ω c τ) ≠ 0) :
    HasDerivAt (deriv (angularLedger ω c))
      (ω ^ 2 / Real.sin (phase ω c τ) ^ 2) τ := by
  have hcont : ContinuousAt (fun u => Real.sin (phase ω c u)) τ :=
    Real.continuous_sin.continuousAt.comp (hasDerivAt_phase ω c τ).continuousAt
  have hev : ∀ᶠ u in 𝓝 τ, Real.sin (phase ω c u) ≠ 0 := hcont.eventually_ne hs
  have heq : deriv (angularLedger ω c) =ᶠ[𝓝 τ]
      fun u => -(ω * Real.cos (phase ω c u) / Real.sin (phase ω c u)) := by
    filter_upwards [hev] with u hu
    exact (hasDerivAt_angularLedger hu).deriv
  exact (hasDerivAt_ledgerVelocity hs).congr_of_eventuallyEq heq

/-- The angular scalar ledger obeys a repulsive exponential equation. -/
theorem ledger_equation_of_motion {ω c τ : ℝ}
    (hs : Real.sin (phase ω c τ) ≠ 0) :
    deriv (deriv (angularLedger ω c)) τ =
      ω ^ 2 * Real.exp (2 * angularLedger ω c τ) := by
  rw [(hasDerivAt_deriv_angularLedger hs).deriv, exp_two_mul_angularLedger hs]
  ring

/-- First-order energy law for the angular scalar ledger. -/
theorem ledger_velocity_sq {ω c τ : ℝ}
    (hs : Real.sin (phase ω c τ) ≠ 0) :
    (deriv (angularLedger ω c) τ) ^ 2 =
      ω ^ 2 * (Real.exp (2 * angularLedger ω c τ) - 1) := by
  rw [(hasDerivAt_angularLedger hs).deriv, exp_two_mul_angularLedger hs]
  have htri := Real.sin_sq_add_cos_sq (phase ω c τ)
  field_simp [hs]
  nlinarith

/-- The angular ledger motion has the exact constant Hamiltonian value `-ω²/2`. -/
theorem ledger_first_integral {ω c τ : ℝ}
    (hs : Real.sin (phase ω c τ) ≠ 0) :
    (deriv (angularLedger ω c) τ) ^ 2 / 2 +
        effectivePotential ω (angularLedger ω c τ) = -ω ^ 2 / 2 := by
  rw [ledger_velocity_sq hs]
  simp only [effectivePotential, exp_two_mul_angularLedger hs]
  ring

/-- Derivative of the effective potential. -/
theorem hasDerivAt_effectivePotential (ω S : ℝ) :
    HasDerivAt (effectivePotential ω) (-ω ^ 2 * Real.exp (2 * S)) S := by
  have hline := (hasDerivAt_id S).const_mul (2 : ℝ)
  have h := hline.exp.const_mul (-(ω ^ 2 / 2))
  convert h using 1
  · ext u
    rfl
  · simp only [id_eq]
    ring

/-- Momentum `∂L/∂v` of the angular Lagrangian. -/
theorem hasDerivAt_angularLagrangian_velocity (ω S v : ℝ) :
    HasDerivAt (angularLagrangian ω S) v v := by
  unfold angularLagrangian
  convert (((hasDerivAt_id v).pow 2).div_const 2).sub_const
    (effectivePotential ω S) using 1
  · ext u
    rfl
  · norm_num

/-- Position derivative `∂L/∂S` of the angular Lagrangian. -/
theorem hasDerivAt_angularLagrangian_position (ω v S : ℝ) :
    HasDerivAt (fun s => angularLagrangian ω s v)
      (ω ^ 2 * Real.exp (2 * S)) S := by
  unfold angularLagrangian
  convert (hasDerivAt_const S (v ^ 2 / 2)).sub
    (hasDerivAt_effectivePotential ω S) using 1
  ring

/-- The full Euler--Lagrange residual of `L = S'²/2 + ω²exp(2S)/2` vanishes. -/
theorem angular_eulerLagrange {ω c τ : ℝ}
    (hs : Real.sin (phase ω c τ) ≠ 0) :
    deriv (fun u => deriv (angularLagrangian ω (angularLedger ω c u))
        (deriv (angularLedger ω c) u)) τ -
      deriv (fun s => angularLagrangian ω s (deriv (angularLedger ω c) τ))
        (angularLedger ω c τ) = 0 := by
  have hmom : (fun u => deriv (angularLagrangian ω (angularLedger ω c u))
      (deriv (angularLedger ω c) u)) = deriv (angularLedger ω c) := by
    funext u
    exact (hasDerivAt_angularLagrangian_velocity ω _ _).deriv
  rw [hmom]
  rw [(hasDerivAt_angularLagrangian_position ω _ _).deriv]
  rw [ledger_equation_of_motion hs]
  ring

/-- For nonzero frequency the effective potential tends to negative infinity. -/
theorem tendsto_effectivePotential_atTop {ω : ℝ} (hω : ω ≠ 0) :
    Tendsto (effectivePotential ω) atTop atBot := by
  have hlin : Tendsto (fun S : ℝ => 2 * S) atTop atTop := by
    simpa using (tendsto_id.const_mul_atTop (show (0 : ℝ) < 2 by norm_num))
  have hexp : Tendsto (fun S : ℝ => Real.exp (2 * S)) atTop atTop := by
    simpa only [Function.comp_def] using Real.tendsto_exp_atTop.comp hlin
  have hcoef : -(ω ^ 2 / 2) < 0 := by
    have hsquare : 0 < ω ^ 2 := sq_pos_of_ne_zero hω
    linarith
  change Tendsto (fun S : ℝ => -(ω ^ 2 / 2) * Real.exp (2 * S)) atTop atBot
  exact hexp.const_mul_atTop_of_neg hcoef

/-- In particular, no real number is a lower bound for the effective potential. -/
theorem effectivePotential_unbounded_below {ω : ℝ} (hω : ω ≠ 0) (b : ℝ) :
    ∃ S : ℝ, effectivePotential ω S < b := by
  exact ((tendsto_effectivePotential_atTop hω).eventually_lt_atBot b).exists

/-- Sine approaches zero from the right as the angle approaches `π` from the left. -/
theorem tendsto_sin_pi_left :
    Tendsto Real.sin (𝓝[<] Real.pi) (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · convert Real.continuous_sin.continuousWithinAt.tendsto
    simp
  · filter_upwards [Ioo_mem_nhdsLT Real.pi_pos] with x hx
    exact Real.sin_pos_of_pos_of_lt_pi hx.1 hx.2

/-- The negative logarithm of sine diverges at the left side of `π`. -/
theorem tendsto_neg_log_sin_pi_left :
    Tendsto (fun x => -Real.log (Real.sin x)) (𝓝[<] Real.pi) atTop := by
  have hlog : Tendsto (fun x => Real.log (Real.sin x)) (𝓝[<] Real.pi) atBot := by
    simpa only [Function.comp_def] using Real.tendsto_log_nhdsGT_zero.comp tendsto_sin_pi_left
  simpa only [Function.comp_def] using tendsto_neg_atBot_atTop.comp hlog

/-- The next positive-phase collision time for `0 < c < π` and positive frequency. -/
def collisionTime (ω c : ℝ) : ℝ := (Real.pi - c) / ω

theorem collisionTime_pos {ω c : ℝ} (hω : 0 < ω) (hc : c < Real.pi) :
    0 < collisionTime ω c := div_pos (sub_pos.mpr hc) hω

theorem phase_collisionTime {ω c : ℝ} (hω : 0 < ω) :
    phase ω c (collisionTime ω c) = Real.pi := by
  simp only [phase, collisionTime]
  field_simp [ne_of_gt hω]
  ring

theorem phase_lt_of_lt_collisionTime {ω c τ : ℝ} (hω : 0 < ω)
    (hτ : τ < collisionTime ω c) : phase ω c τ < Real.pi := by
  calc
    phase ω c τ < phase ω c (collisionTime ω c) := by
      simp only [phase]
      gcongr
    _ = Real.pi := phase_collisionTime hω

/-- On an initial segment in `(0,π)`, no sine zero occurs before the collision time. -/
theorem sin_pos_before_collision {ω c τ : ℝ} (hω : 0 < ω) (hc : 0 < c)
    (hτ0 : 0 ≤ τ) (hτ : τ < collisionTime ω c) :
    0 < Real.sin (phase ω c τ) := by
  apply Real.sin_pos_of_pos_of_lt_pi
  · simp only [phase]
    nlinarith [mul_nonneg hω.le hτ0]
  · exact phase_lt_of_lt_collisionTime hω hτ

/-- The ledger diverges in finite forward time at the explicit next zero of sine. -/
theorem tendsto_angularLedger_collision {ω c : ℝ} (hω : 0 < ω) :
    Tendsto (angularLedger ω c) (𝓝[<] collisionTime ω c) atTop := by
  have hcont : Tendsto (phase ω c) (𝓝[<] collisionTime ω c) (𝓝 Real.pi) := by
    have h := (hasDerivAt_phase ω c (collisionTime ω c)).continuousAt.tendsto
    rw [phase_collisionTime hω] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ τ in 𝓝[<] collisionTime ω c, phase ω c τ ∈ Set.Iio Real.pi := by
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    exact phase_lt_of_lt_collisionTime hω hτ
  have hphase : Tendsto (phase ω c) (𝓝[<] collisionTime ω c) (𝓝[<] Real.pi) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hcont hev
  have hbase : Tendsto (fun τ => -Real.log (Real.sin (phase ω c τ)))
      (𝓝[<] collisionTime ω c) atTop := by
    simpa only [Function.comp_def] using tendsto_neg_log_sin_pi_left.comp hphase
  apply Filter.Tendsto.congr' _ hbase
  have hsinpos : ∀ᶠ x in 𝓝[<] Real.pi, Real.sin x ∈ Set.Ioi (0 : ℝ) :=
    (tendsto_nhdsWithin_iff.mp tendsto_sin_pi_left).2
  filter_upwards [hphase.eventually hsinpos] with τ hτ
  rw [angularLedger_eq_neg_log_abs_sin, abs_of_pos hτ]

/-- For an initial angle strictly between zero and `π`, the collision is both future and first. -/
theorem finite_future_ledger_divergence {ω c : ℝ} (hω : 0 < ω)
    (hc0 : 0 < c) (hcπ : c < Real.pi) :
    0 < collisionTime ω c ∧
      (∀ τ, 0 ≤ τ → τ < collisionTime ω c → 0 < Real.sin (phase ω c τ)) ∧
      Tendsto (angularLedger ω c) (𝓝[<] collisionTime ω c) atTop := by
  exact ⟨collisionTime_pos hω hcπ,
    fun τ hτ0 hτ => sin_pos_before_collision hω hc0 hτ0 hτ,
    tendsto_angularLedger_collision hω⟩

/-- At equal peel, the angular and uniform-log-ratio velocities are genuinely different. -/
theorem angular_velocity_ne_logRatio_velocity (ω : ℝ) (hω : ω ≠ 0) :
    deriv (angularPeel ω (Real.pi / 2)) 0 ≠
      (ω / 2) * (1 - angularPeel ω (Real.pi / 2) 0 ^ 2) := by
  rw [deriv_angularPeel]
  simp [angularPeel, phase, Real.sin_pi_div_two, Real.cos_pi_div_two]
  intro h
  apply hω
  linarith

end

end ElementalPeeling.LoopWall.UniformAngularBridge
