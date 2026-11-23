import Mathlib

/-!
Direction B2 of the fifth round (swarm `smws70oju`, member m6). The uniform log-ratio phase in full:
affine phase, closed form `Γ = tanh (ωτ/2 + t₀/2)`, the peel and ledger rates, the bridge equation
`S'' = (ω²/4)e^{-2S}` with its first integral `T + U = ω²/8`, and — a correction to my own task
statement — the Euler–Lagrange density is `T - U` with `U = +(ω²/8)e^{-2S}`, not `T + U`; the module
proves the corrected density and refutes the sign I wrote.

Written in the fifth parallel formalization round and recompiled here before acceptance;
imports hoisted, namespace prefixed to `ElementalPeeling.LoopWall`, nothing else changed.
-/

set_option maxHeartbeats 1000000

/-!
# Uniform log-ratio phase: peel flow and logarithmic-ledger dynamics

The ledger below is exactly the library's `log cosh (t/2)` form.  The final
identities also express it as `φled Γ = -(1/2) log (1 - Γ^2)`.
-/

namespace ElementalPeeling.LoopWall.UniformLogRatio

noncomputable section

/-- The peel coordinate induced by a log-ratio phase. -/
def peel (t : ℝ → ℝ) (τ : ℝ) : ℝ := Real.tanh (t τ / 2)

/-- The scalar logarithmic ledger induced by a log-ratio phase. -/
def ledger (t : ℝ → ℝ) (τ : ℝ) : ℝ := Real.log (Real.cosh (t τ / 2))

/-- The ledger written as a potential of the peel (the library's `φled`). -/
def φled (Γ : ℝ) : ℝ := -(1 / 2 : ℝ) * Real.log (1 - Γ ^ 2)

/-- The hyperbolic-tangent derivative, proved here because this Mathlib
snapshot does not export `Real.hasDerivAt_tanh`. -/
theorem hasDerivAt_tanh (x : ℝ) :
    HasDerivAt Real.tanh (1 - Real.tanh x ^ 2) x := by
  have h := (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x)
    (ne_of_gt (Real.cosh_pos x))
  have _hc := Real.cosh_sq_sub_sinh_sq x
  have hpos := Real.cosh_pos x
  convert h using 1
  · ext y
    exact Real.tanh_eq_sinh_div_cosh y
  · rw [Real.tanh_eq_sinh_div_cosh]
    field_simp [ne_of_gt hpos]

/-- A constant derivative makes the log-ratio phase affine. -/
theorem phase_eq_affine {t : ℝ → ℝ} (ht : Differentiable ℝ t) {ω : ℝ}
    (ht' : ∀ τ, deriv t τ = ω) (τ : ℝ) :
    t τ = t 0 + ω * τ := by
  have hd : ∀ u, HasDerivAt (fun v => t v - ω * v) 0 u := by
    intro u
    have hw : HasDerivAt (fun v : ℝ => ω * v) ω u := by
      simpa using (hasDerivAt_id u).const_mul ω
    convert (ht u).hasDerivAt.sub hw using 1
    simp [ht' u]
  have hconst : t τ - ω * τ = t 0 - ω * 0 := is_const_of_deriv_eq_zero
    (fun u => (hd u).differentiableAt) (fun u => (hd u).deriv) τ 0
  linarith

/-- The closed form of the peel under a uniform log-ratio phase. -/
theorem peel_closed_form {t : ℝ → ℝ} (ht : Differentiable ℝ t) {ω : ℝ}
    (ht' : ∀ τ, deriv t τ = ω) (τ : ℝ) :
    peel t τ = Real.tanh (ω * τ / 2 + t 0 / 2) := by
  rw [peel, phase_eq_affine ht ht' τ]
  congr 1
  ring

/-- General peel chain rule for a differentiable log-ratio phase. -/
theorem hasDerivAt_peel {t : ℝ → ℝ} {τ : ℝ} (ht : DifferentiableAt ℝ t τ) :
    HasDerivAt (peel t) ((1 - peel t τ ^ 2) * (deriv t τ / 2)) τ := by
  have hi : HasDerivAt (fun u => t u / 2) (deriv t τ / 2) τ :=
    ht.hasDerivAt.div_const 2
  have h := (hasDerivAt_tanh (t τ / 2)).comp τ hi
  change HasDerivAt (fun u => Real.tanh (t u / 2))
    ((1 - Real.tanh (t τ / 2) ^ 2) * (deriv t τ / 2)) τ
  convert h using 1
  rfl

/-- General ledger chain rule for a differentiable log-ratio phase. -/
theorem hasDerivAt_ledger {t : ℝ → ℝ} {τ : ℝ} (ht : DifferentiableAt ℝ t τ) :
    HasDerivAt (ledger t) ((deriv t τ / 2) * peel t τ) τ := by
  have hi : HasDerivAt (fun u => t u / 2) (deriv t τ / 2) τ :=
    ht.hasDerivAt.div_const 2
  have h := hi.cosh.log (ne_of_gt (Real.cosh_pos (t τ / 2)))
  have hc : Real.cosh (t τ / 2) ≠ 0 := ne_of_gt (Real.cosh_pos _)
  change HasDerivAt (fun u => Real.log (Real.cosh (t u / 2)))
    ((deriv t τ / 2) * Real.tanh (t τ / 2)) τ
  convert h using 1
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp [hc]

/-- The uniform phase induces exactly the logistic peel equation. -/
theorem hasDerivAt_peel_uniform {t : ℝ → ℝ} (ht : Differentiable ℝ t) {ω : ℝ}
    (ht' : ∀ τ, deriv t τ = ω) (τ : ℝ) :
    HasDerivAt (peel t) ((ω / 2) * (1 - peel t τ ^ 2)) τ := by
  convert hasDerivAt_peel (ht τ) using 1
  rw [ht' τ]
  ring

/-- The ledger rate is one half the phase frequency times the peel. -/
theorem hasDerivAt_ledger_uniform {t : ℝ → ℝ} (ht : Differentiable ℝ t) {ω : ℝ}
    (ht' : ∀ τ, deriv t τ = ω) (τ : ℝ) :
    HasDerivAt (ledger t) ((ω / 2) * peel t τ) τ := by
  simpa only [ht' τ] using hasDerivAt_ledger (ht τ)

/-- Derivative form of the uniform peel equation. -/
theorem deriv_peel_uniform {t : ℝ → ℝ} (ht : Differentiable ℝ t) {ω : ℝ}
    (ht' : ∀ τ, deriv t τ = ω) (τ : ℝ) :
    deriv (peel t) τ = (ω / 2) * (1 - peel t τ ^ 2) :=
  (hasDerivAt_peel_uniform ht ht' τ).deriv

/-- Derivative form of the ledger-rate equation. -/
theorem deriv_ledger_uniform {t : ℝ → ℝ} (ht : Differentiable ℝ t) {ω : ℝ}
    (ht' : ∀ τ, deriv t τ = ω) (τ : ℝ) :
    deriv (ledger t) τ = (ω / 2) * peel t τ :=
  (hasDerivAt_ledger_uniform ht ht' τ).deriv

/-- `sech²` in its exact form needed by the energy and force laws. -/
theorem one_sub_tanh_sq (x : ℝ) :
    1 - Real.tanh x ^ 2 = (Real.cosh x ^ 2)⁻¹ := by
  have hc : Real.cosh x ≠ 0 := ne_of_gt (Real.cosh_pos x)
  rw [Real.tanh_eq_sinh_div_cosh, div_pow]
  field_simp [hc]
  nlinarith [Real.cosh_sq_sub_sinh_sq x]

/-- Exponentiating twice the logarithmic ledger gives `cosh²`. -/
theorem exp_neg_two_log_cosh (x : ℝ) :
    Real.exp (-(2 * Real.log (Real.cosh x))) = 1 - Real.tanh x ^ 2 := by
  rw [one_sub_tanh_sq]
  have hp : 0 < (Real.cosh x ^ 2)⁻¹ := inv_pos.mpr (pow_pos (Real.cosh_pos x) 2)
  rw [← Real.exp_log hp]
  congr 1
  rw [Real.log_inv, Real.log_pow]
  norm_num

/-- The same identity along a phase trajectory. -/
theorem exp_neg_two_ledger (t : ℝ → ℝ) (τ : ℝ) :
    Real.exp (-(2 * ledger t τ)) = 1 - peel t τ ^ 2 := by
  exact exp_neg_two_log_cosh (t τ / 2)

/-- The second ledger derivative before the exponential rewrite. -/
theorem hasDerivAt_deriv_ledger_uniform {t : ℝ → ℝ} (ht : Differentiable ℝ t)
    {ω : ℝ} (ht' : ∀ τ, deriv t τ = ω) (τ : ℝ) :
    HasDerivAt (deriv (ledger t)) ((ω ^ 2 / 4) * (1 - peel t τ ^ 2)) τ := by
  have hfun : deriv (ledger t) = fun u => (ω / 2) * peel t u := by
    funext u
    exact deriv_ledger_uniform ht ht' u
  rw [hfun]
  convert (hasDerivAt_peel_uniform ht ht' τ).const_mul (ω / 2) using 1
  all_goals ring

/-- The ledger obeys the exponential-force second-order equation. -/
theorem hasDerivAt_deriv_ledger_exp {t : ℝ → ℝ} (ht : Differentiable ℝ t)
    {ω : ℝ} (ht' : ∀ τ, deriv t τ = ω) (τ : ℝ) :
    HasDerivAt (deriv (ledger t))
      ((ω ^ 2 / 4) * Real.exp (-(2 * ledger t τ))) τ := by
  rw [exp_neg_two_ledger]
  exact hasDerivAt_deriv_ledger_uniform ht ht' τ

/-- `S'' = (ω²/4) exp (-2S)` for the uniform log-ratio phase. -/
theorem deriv_deriv_ledger_uniform {t : ℝ → ℝ} (ht : Differentiable ℝ t)
    {ω : ℝ} (ht' : ∀ τ, deriv t τ = ω) (τ : ℝ) :
    deriv (deriv (ledger t)) τ =
      (ω ^ 2 / 4) * Real.exp (-(2 * ledger t τ)) :=
  (hasDerivAt_deriv_ledger_exp ht ht' τ).deriv

/-- The exact first integral `(S')² = (ω²/4)(1-exp(-2S))`. -/
theorem ledger_sq_deriv_eq {t : ℝ → ℝ} (ht : Differentiable ℝ t) {ω : ℝ}
    (ht' : ∀ τ, deriv t τ = ω) (τ : ℝ) :
    deriv (ledger t) τ ^ 2 =
      (ω ^ 2 / 4) * (1 - Real.exp (-(2 * ledger t τ))) := by
  rw [deriv_ledger_uniform ht ht' τ, exp_neg_two_ledger]
  ring

/-- The two phase descriptions of the scalar ledger agree exactly. -/
theorem ledger_eq_φled_peel (t : ℝ → ℝ) (τ : ℝ) :
    ledger t τ = φled (peel t τ) := by
  rw [ledger, φled, peel]
  have hden : 1 - Real.tanh (t τ / 2) ^ 2 = (Real.cosh (t τ / 2) ^ 2)⁻¹ :=
    one_sub_tanh_sq _
  rw [hden, Real.log_inv, Real.log_pow]
  norm_num
  ring

/-! ## The variational bridge

The effective energy potential is `U = (ω²/8) exp (-2S)`.  A standard
variational calculation gives `S'' = -U'(S)` for the motion action `T - U`.
The plus-sign density `T + U` has the opposite Euler--Lagrange equation; both
formulae are proved below so that the sign convention is explicit.
-/

/-- The positive, exponentially decaying effective potential. -/
def effectivePotential (ω S : ℝ) : ℝ :=
  (ω ^ 2 / 8) * Real.exp (-(2 * S))

/-- The corrected variational density whose Euler--Lagrange equation is the
ledger dynamics: kinetic energy minus effective potential. -/
def motionLagrangian (ω S v : ℝ) : ℝ :=
  (1 / 2 : ℝ) * v ^ 2 - effectivePotential ω S

/-- The plus-sign density from the original proposal, retained as a contrast. -/
def plusLagrangian (ω S v : ℝ) : ℝ :=
  (1 / 2 : ℝ) * v ^ 2 + effectivePotential ω S

/-- The interval action of a smooth readout for any curried density. It is declared for
reference; this module proves the Euler--Lagrange residual of two densities, not that
stationarity of this integral is equivalent to that residual vanishing. -/
noncomputable def variationalAction (L : ℝ → ℝ → ℝ) (S : ℝ → ℝ)
    (a b : ℝ) : ℝ := ∫ τ in a..b, L (S τ) (deriv S τ)

/-- The standard (first-variation) Euler--Lagrange residual of a density. -/
def eulerLagrangeResidual (L : ℝ → ℝ → ℝ) (S : ℝ → ℝ) (τ : ℝ) : ℝ :=
  deriv (fun u => deriv (L (S u)) (deriv S u)) τ -
    deriv (fun s => L s (deriv S τ)) (S τ)

/-- Both densities have velocity derivative `v`. -/
theorem hasDerivAt_lagrangian_velocity (plus : Bool) (ω S v : ℝ) :
    HasDerivAt (fun w => (if plus then plusLagrangian else motionLagrangian) ω S w) v v := by
  have h := ((hasDerivAt_id v).pow 2).const_mul (1 / 2 : ℝ)
  cases plus with
  | false =>
      unfold motionLagrangian
      convert h.sub_const (effectivePotential ω S) using 1
      all_goals norm_num
      all_goals ring
  | true =>
      unfold plusLagrangian
      convert h.add_const (effectivePotential ω S) using 1
      all_goals norm_num
      all_goals ring

/-- Velocity derivative of the corrected motion density. -/
theorem deriv_motionLagrangian_velocity (ω S v : ℝ) :
    deriv (motionLagrangian ω S) v = v := by
  have h := hasDerivAt_lagrangian_velocity false ω S v
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  exact h.deriv

/-- Velocity derivative of the plus-sign density. -/
theorem deriv_plusLagrangian_velocity (ω S v : ℝ) :
    deriv (plusLagrangian ω S) v = v := by
  have h := hasDerivAt_lagrangian_velocity true ω S v
  simp only [↓reduceIte] at h
  exact h.deriv

/-- Derivative of the exponential part in the position variable. -/
theorem hasDerivAt_exp_neg_two (S : ℝ) :
    HasDerivAt (fun s : ℝ => Real.exp (-(2 * s)))
      (-2 * Real.exp (-(2 * S))) S := by
  have hi : HasDerivAt (fun s : ℝ => -(2 * s)) (-2) S := by
    convert (hasDerivAt_id S).const_mul (-2 : ℝ) using 1
    all_goals simp [id_eq]
  convert hi.exp using 1
  all_goals ring

/-- The effective potential has derivative `-(ω²/4) exp (-2S)`. -/
theorem hasDerivAt_effectivePotential (ω S : ℝ) :
    HasDerivAt (effectivePotential ω)
      (-(ω ^ 2 / 4) * Real.exp (-(2 * S))) S := by
  unfold effectivePotential
  convert (hasDerivAt_exp_neg_two S).const_mul (ω ^ 2 / 8) using 1
  all_goals ring

/-- Position derivative of the corrected (`T-U`) motion density. -/
theorem hasDerivAt_motionLagrangian_position (ω S v : ℝ) :
    HasDerivAt (fun s => motionLagrangian ω s v)
      ((ω ^ 2 / 4) * Real.exp (-(2 * S))) S := by
  have h := ((hasDerivAt_effectivePotential ω S).const_sub
    ((1 / 2 : ℝ) * v ^ 2))
  unfold motionLagrangian
  convert h using 1
  all_goals ring

/-- Position derivative of the proposed plus-sign (`T+U`) density. -/
theorem hasDerivAt_plusLagrangian_position (ω S v : ℝ) :
    HasDerivAt (fun s => plusLagrangian ω s v)
      (-(ω ^ 2 / 4) * Real.exp (-(2 * S))) S := by
  have h := (hasDerivAt_const S ((1 / 2 : ℝ) * v ^ 2)).add
    (hasDerivAt_effectivePotential ω S)
  unfold plusLagrangian
  convert h using 1
  all_goals ring

/-- Derivative form of the motion-density position derivative. -/
theorem deriv_motionLagrangian_position (ω S v : ℝ) :
    deriv (fun s => motionLagrangian ω s v) S =
      (ω ^ 2 / 4) * Real.exp (-(2 * S)) :=
  (hasDerivAt_motionLagrangian_position ω S v).deriv

/-- Derivative form of the plus-density position derivative. -/
theorem deriv_plusLagrangian_position (ω S v : ℝ) :
    deriv (fun s => plusLagrangian ω s v) S =
      -(ω ^ 2 / 4) * Real.exp (-(2 * S)) :=
  (hasDerivAt_plusLagrangian_position ω S v).deriv

/-- Exact Euler--Lagrange residual for the corrected motion action. -/
theorem motion_eulerLagrangeResidual_eq (ω : ℝ) (S : ℝ → ℝ) (τ : ℝ) :
    eulerLagrangeResidual (motionLagrangian ω) S τ =
      deriv (deriv S) τ - (ω ^ 2 / 4) * Real.exp (-(2 * S τ)) := by
  unfold eulerLagrangeResidual
  have hv : (fun u => deriv (motionLagrangian ω (S u)) (deriv S u)) = deriv S := by
    funext u
    exact deriv_motionLagrangian_velocity ω (S u) (deriv S u)
  rw [hv, deriv_motionLagrangian_position]

/-- Exact Euler--Lagrange residual for the proposed plus-sign action. -/
theorem plus_eulerLagrangeResidual_eq (ω : ℝ) (S : ℝ → ℝ) (τ : ℝ) :
    eulerLagrangeResidual (plusLagrangian ω) S τ =
      deriv (deriv S) τ + (ω ^ 2 / 4) * Real.exp (-(2 * S τ)) := by
  unfold eulerLagrangeResidual
  have hv : (fun u => deriv (plusLagrangian ω (S u)) (deriv S u)) = deriv S := by
    funext u
    exact deriv_plusLagrangian_velocity ω (S u) (deriv S u)
  rw [hv, deriv_plusLagrangian_position]
  ring

/-- The Euler--Lagrange residual of the corrected motion action vanishes exactly when the ledger
ODE holds. This is the residual identity; the passage from stationarity of `variationalAction`
to the vanishing of this residual is the classical first-variation argument, which this module
does not formalize. -/
theorem motion_eulerLagrange_eq_zero_iff (ω : ℝ) (S : ℝ → ℝ) (τ : ℝ) :
    eulerLagrangeResidual (motionLagrangian ω) S τ = 0 ↔
      deriv (deriv S) τ = (ω ^ 2 / 4) * Real.exp (-(2 * S τ)) := by
  rw [motion_eulerLagrangeResidual_eq]
  exact sub_eq_zero

/-- The plus-sign action instead imposes the opposite acceleration. -/
theorem plus_eulerLagrange_eq_zero_iff (ω : ℝ) (S : ℝ → ℝ) (τ : ℝ) :
    eulerLagrangeResidual (plusLagrangian ω) S τ = 0 ↔
      deriv (deriv S) τ = -(ω ^ 2 / 4) * Real.exp (-(2 * S τ)) := by
  rw [plus_eulerLagrangeResidual_eq]
  constructor <;> intro h <;> linarith

/-- The uniform phase solves precisely the corrected action's Euler--Lagrange equation. -/
theorem motion_eulerLagrangeResidual_uniform {t : ℝ → ℝ} (ht : Differentiable ℝ t)
    {ω : ℝ} (ht' : ∀ τ, deriv t τ = ω) (τ : ℝ) :
    eulerLagrangeResidual (motionLagrangian ω) (ledger t) τ = 0 := by
  rw [motion_eulerLagrange_eq_zero_iff]
  exact deriv_deriv_ledger_uniform ht ht' τ

/-- At nonzero frequency, the proposed plus-sign action does not have the
uniform-phase ledger as a solution (even at one time). -/
theorem plus_eulerLagrangeResidual_uniform_ne_zero {t : ℝ → ℝ}
    (ht : Differentiable ℝ t) {ω : ℝ} (hω : ω ≠ 0)
    (ht' : ∀ τ, deriv t τ = ω) (τ : ℝ) :
    eulerLagrangeResidual (plusLagrangian ω) (ledger t) τ ≠ 0 := by
  rw [plus_eulerLagrangeResidual_eq, deriv_deriv_ledger_uniform ht ht' τ]
  have he : 0 < Real.exp (-(2 * ledger t τ)) := Real.exp_pos _
  have hw : 0 < ω ^ 2 / 4 := by positivity
  positivity

/-- The effective potential is bounded below by zero. -/
theorem effectivePotential_nonneg (ω S : ℝ) : 0 ≤ effectivePotential ω S := by
  unfold effectivePotential
  positivity

/-- Compact restatement of the global lower bound. -/
theorem effectivePotential_bounded_below (ω : ℝ) :
    ∃ c : ℝ, ∀ S : ℝ, c ≤ effectivePotential ω S :=
  ⟨0, effectivePotential_nonneg ω⟩

/-- For nonzero frequency the lower bound is strict at every finite ledger value. -/
theorem effectivePotential_pos {ω : ℝ} (hω : ω ≠ 0) (S : ℝ) :
    0 < effectivePotential ω S := by
  unfold effectivePotential
  have hw : 0 < ω ^ 2 / 8 := by positivity
  exact mul_pos hw (Real.exp_pos _)

/-- The physical energy `T+U` is the constant `ω²/8` on every uniform-phase ledger. -/
theorem effectiveEnergy_uniform {t : ℝ → ℝ} (ht : Differentiable ℝ t) {ω : ℝ}
    (ht' : ∀ τ, deriv t τ = ω) (τ : ℝ) :
    (1 / 2 : ℝ) * deriv (ledger t) τ ^ 2 + effectivePotential ω (ledger t τ) =
      ω ^ 2 / 8 := by
  rw [ledger_sq_deriv_eq ht ht' τ]
  unfold effectivePotential
  ring

end

end ElementalPeeling.LoopWall.UniformLogRatio
