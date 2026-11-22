import Mathlib

/-!
# A potential of the peel coordinate: the force, and the wall

Direction B1 of the fourth round.  For `Γ = G X = (X - 1)/(X + 1)` and a potential `V = φ (Γ)`, the
force is `-φ'(Γ) · 2/(1+X)^2 · X'` (`potentialForce_eq`), and the ledger potential
`φled Γ = -(1/2) log (1 - Γ^2)` has `deriv φled Γ = Γ/(1-Γ^2)` on `|Γ| < 1`.

At the wall: `φled (1/√2) = (1/2) log 2` and `deriv φled (1/√2) = √2` — not twice that, as I first
wrote, which is refuted here.  The wall is not a singular point: the potential is differentiable and
continuous there (`abs_wall_lt_one`, `wall_log_argument_pos`, `differentiableAt_φled_wall`,
`continuousAt_φled_wall`).

The worked model is separated from the theorems: `V`, `harmonicEnergy` and the two canonical systems
are definitions; the derivative of `V`, the frozen energy conservation, and the reduction of the
phase-dependent system to the frozen one at constant phase (`phaseDependent_frozen_iff`) are proved.

Written in the fourth parallel formalization round (swarm `smws625cs`, direction m3), recompiled and
reviewed here; namespace and header added, `#print axioms` lines removed.
-/

namespace ElementalPeeling.LoopWall.PeelPotential

noncomputable section

/-- The peel reflection as a function of a phase ratio. -/
def G (z : ℝ) : ℝ := (z - 1) / (z + 1)

/-- The scalar ledger regarded as a potential of the reflection. -/
def φled (Γ : ℝ) : ℝ := -(1 / 2 : ℝ) * Real.log (1 - Γ ^ 2)

/-- The wall point on the positive side of the reflection interval. -/
def wall : ℝ := 1 / Real.sqrt 2

/-- The signed force associated with a potential on the peel coordinate. -/
def potentialForce (φ X : ℝ → ℝ) (s : ℝ) : ℝ :=
  -deriv (fun u => φ (G (X u))) s

/-- Derivative of the rational peel map away from its pole. -/
theorem hasDerivAt_G (z : ℝ) (hz : 1 + z ≠ 0) :
    HasDerivAt G (2 / (1 + z) ^ 2) z := by
  have hz' : z + 1 ≠ 0 := by simpa [add_comm] using hz
  have h := ((hasDerivAt_id z).sub_const 1).div
    ((hasDerivAt_id z).add_const 1) hz'
  convert h using 1
  · ext w
    rfl
  · field_simp [hz']
    simp only [id_eq]
    ring

/-- Derivative form of `hasDerivAt_G`. -/
theorem deriv_G (z : ℝ) (hz : 1 + z ≠ 0) :
    deriv G z = 2 / (1 + z) ^ 2 :=
  (hasDerivAt_G z hz).deriv

/-- Chain rule for an arbitrary differentiable potential through the peel map. -/
theorem hasDerivAt_peel_potential
    {φ X Γ : ℝ → ℝ} {s : ℝ}
    (hφ : Differentiable ℝ φ) (hX : Differentiable ℝ X)
    (hΓ : Γ s = G (X s)) (hXden : 1 + X s ≠ 0) :
    HasDerivAt (fun u => φ (G (X u)))
      (deriv φ (Γ s) * (2 / (1 + X s) ^ 2) * deriv X s) s := by
  have hGX : HasDerivAt (fun u => G (X u))
      ((2 / (1 + X s) ^ 2) * deriv X s) s := by
    simpa only [Function.comp_def] using
      (hasDerivAt_G (X s) hXden).comp s (hX s).hasDerivAt
  have hcomp := (hφ (G (X s))).hasDerivAt.comp s hGX
  rw [hΓ]
  convert hcomp using 1
  · ext u
    rfl
  · ring

/-- Derivative form of the peel-potential chain rule. -/
theorem deriv_peel_potential
    {φ X Γ : ℝ → ℝ} {s : ℝ}
    (hφ : Differentiable ℝ φ) (hX : Differentiable ℝ X)
    (hΓ : Γ s = G (X s)) (hXden : 1 + X s ≠ 0) :
    deriv (fun u => φ (G (X u))) s =
      deriv φ (Γ s) * (2 / (1 + X s) ^ 2) * deriv X s :=
  (hasDerivAt_peel_potential hφ hX hΓ hXden).deriv

/-- The force is the negative derivative, with the stated rational peel factor. -/
theorem potentialForce_eq
    {φ X Γ : ℝ → ℝ} {s : ℝ}
    (hφ : Differentiable ℝ φ) (hX : Differentiable ℝ X)
    (hΓ : Γ s = G (X s)) (hXden : 1 + X s ≠ 0) :
    potentialForce φ X s =
      -deriv φ (Γ s) * (2 / (1 + X s) ^ 2) * deriv X s := by
  rw [potentialForce, deriv_peel_potential hφ hX hΓ hXden]
  ring

/-- Squaring a number of absolute value below one gives a number below one. -/
theorem sq_lt_one_of_abs_lt_one {Γ : ℝ} (hΓ : |Γ| < 1) : Γ ^ 2 < 1 := by
  have h := (sq_lt_sq₀ (abs_nonneg Γ) (by norm_num : (0 : ℝ) ≤ 1)).2 hΓ
  simpa [sq_abs] using h

/-- Derivative of the ledger potential on the open reflection interval. -/
theorem hasDerivAt_φled {Γ : ℝ} (hΓ : |Γ| < 1) :
    HasDerivAt φled (Γ / (1 - Γ ^ 2)) Γ := by
  have hpos : 0 < 1 - Γ ^ 2 := sub_pos.mpr (sq_lt_one_of_abs_lt_one hΓ)
  have hsq : HasDerivAt (fun x : ℝ => x ^ 2) (2 * Γ) Γ := by
    convert (hasDerivAt_id Γ).pow 2 using 1
    · ext x
      rfl
    · norm_num
  have hinner : HasDerivAt (fun x : ℝ => 1 - x ^ 2) (-2 * Γ) Γ := by
    convert (hasDerivAt_const Γ (1 : ℝ)).sub hsq using 1
    ring
  have hlog := hinner.log (ne_of_gt hpos)
  have h := hlog.const_mul (-(1 / 2 : ℝ))
  convert h using 1
  · ext x
    rfl
  · field_simp [ne_of_gt hpos]

/-- The ledger derivative is `Γ / (1 - Γ²)` inside the wall. -/
theorem deriv_φled {Γ : ℝ} (hΓ : |Γ| < 1) :
    deriv φled Γ = Γ / (1 - Γ ^ 2) :=
  (hasDerivAt_φled hΓ).deriv

/-- The square of the positive wall coordinate is exactly one half. -/
theorem wall_sq : wall ^ 2 = (1 / 2 : ℝ) := by
  have hs : Real.sqrt (2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rw [wall, div_pow, one_pow, hs]

/-- The wall lies strictly inside the reflection interval. -/
theorem abs_wall_lt_one : |wall| < 1 := by
  have hspos : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hsone : 1 < Real.sqrt (2 : ℝ) := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hw : 0 < wall := by
    rw [wall]
    positivity
  rw [abs_of_pos hw]
  exact (div_lt_one hspos).2 hsone

/-- The logarithm's argument remains positive at the wall. -/
theorem wall_log_argument_pos : 0 < 1 - wall ^ 2 := by
  rw [wall_sq]
  norm_num

/-- The ledger has its exact finite value `log 2 / 2` at the wall. -/
theorem φled_wall : φled (1 / Real.sqrt 2) = (1 / 2 : ℝ) * Real.log 2 := by
  change φled wall = (1 / 2 : ℝ) * Real.log 2
  have hlog : Real.log (1 - (1 / 2 : ℝ)) = -Real.log 2 := by
    rw [show 1 - (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [φled, wall_sq, hlog]
  ring

/-- In particular, the wall is not a singular point of the ledger potential. -/
theorem differentiableAt_φled_wall : DifferentiableAt ℝ φled wall :=
  (hasDerivAt_φled abs_wall_lt_one).differentiableAt

/-- Continuity at the wall is another explicit form of finite, nonsingular behaviour. -/
theorem continuousAt_φled_wall : ContinuousAt φled wall :=
  differentiableAt_φled_wall.continuousAt

/-- Corrected wall force coefficient: it is `sqrt 2`, not `2 * sqrt 2`. -/
theorem ledger_force_coefficient_at_wall :
    (1 / Real.sqrt 2) / (1 - (1 / Real.sqrt 2) ^ 2) = Real.sqrt 2 := by
  change wall / (1 - wall ^ 2) = Real.sqrt 2
  have hspos : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hs : Real.sqrt (2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rw [wall_sq, wall]
  field_simp [ne_of_gt hspos]
  nlinarith

/-- The value `2 * sqrt 2` in the original request is false. -/
theorem ledger_force_coefficient_at_wall_ne_two_mul_sqrt_two :
    (1 / Real.sqrt 2) / (1 - (1 / Real.sqrt 2) ^ 2) ≠ 2 * Real.sqrt 2 := by
  change wall / (1 - wall ^ 2) ≠ 2 * Real.sqrt 2
  rw [show wall / (1 - wall ^ 2) = Real.sqrt 2 from ledger_force_coefficient_at_wall]
  have hs : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  nlinarith

/-- The derivative of the ledger at the wall, with the corrected value. -/
theorem deriv_φled_wall : deriv φled (1 / Real.sqrt 2) = Real.sqrt 2 := by
  change deriv φled wall = Real.sqrt 2
  rw [deriv_φled abs_wall_lt_one,
    show wall / (1 - wall ^ 2) = Real.sqrt 2 from ledger_force_coefficient_at_wall]

/-!
## The worked oscillator model

The next definitions are model choices, not consequences of the peel calculus.
In the frozen model `ω₀` is constant.  In the phase-dependent model the *only*
change to the canonical ODE is the replacement `ω₀ ↦ ω (Γ s)`.  In particular,
no formula for `ω` and no equation for `Γ` is inferred.
-/

/-- Harmonic potential in the frozen-phase regime.  This is a model choice. -/
def V (m ω₀ X : ℝ) : ℝ := (1 / 2 : ℝ) * m * ω₀ ^ 2 * X ^ 2

/-- One-degree-of-freedom Hamiltonian for that model. -/
def harmonicEnergy (m ω₀ q p : ℝ) : ℝ := p ^ 2 / (2 * m) + V m ω₀ q

/-- Frozen-phase canonical equations, taken as the equations of the model. -/
def FrozenCanonicalEquations (m ω₀ : ℝ) (q p : ℝ → ℝ) : Prop :=
  ∀ s, deriv q s = p s / m ∧ deriv p s = -(m * ω₀ ^ 2 * q s)

/-- Canonical equations with an explicitly hypothesized phase-dependent frequency. -/
def PhaseDependentCanonicalEquations
    (m : ℝ) (ω Γ q p : ℝ → ℝ) : Prop :=
  ∀ s, deriv q s = p s / m ∧ deriv p s = -(m * (ω (Γ s)) ^ 2 * q s)

/-- Derivative of the declared harmonic potential. -/
theorem hasDerivAt_V (m ω₀ X : ℝ) :
    HasDerivAt (V m ω₀) (m * ω₀ ^ 2 * X) X := by
  have h := ((hasDerivAt_id X).pow 2).const_mul ((1 / 2 : ℝ) * m * ω₀ ^ 2)
  convert h using 1
  · ext x
    rfl
  · simp only [id_eq]
    ring

/-- The configuration force is `-m ω₀² X` in the worked model. -/
theorem deriv_V (m ω₀ X : ℝ) : deriv (V m ω₀) X = m * ω₀ ^ 2 * X :=
  (hasDerivAt_V m ω₀ X).deriv

/-- Hamilton's equations for the frozen model conserve its Hamiltonian energy. -/
theorem hasDerivAt_harmonicEnergy_of_frozen
    {m ω₀ : ℝ} {q p : ℝ → ℝ} {s : ℝ} (hm : 0 < m)
    (hq : DifferentiableAt ℝ q s) (hp : DifferentiableAt ℝ p s)
    (hqs : deriv q s = p s / m)
    (hps : deriv p s = -(m * ω₀ ^ 2 * q s)) :
    HasDerivAt (fun u => harmonicEnergy m ω₀ (q u) (p u)) 0 s := by
  have hm0 : m ≠ 0 := ne_of_gt hm
  have hkin : HasDerivAt (fun u => p u ^ 2 / (2 * m))
      (p s * deriv p s / m) s := by
    have h := (hp.hasDerivAt.pow 2).div_const (2 * m)
    convert h using 1
    field_simp [hm0]
    ring
  have hpot : HasDerivAt (fun u => V m ω₀ (q u))
      (m * ω₀ ^ 2 * q s * deriv q s) s := by
    simpa only [Function.comp_def] using
      (hasDerivAt_V m ω₀ (q s)).comp s hq.hasDerivAt
  have hsum := hkin.add hpot
  have hzero : p s * deriv p s / m + m * ω₀ ^ 2 * q s * deriv q s = 0 := by
    rw [hqs, hps]
    field_simp [hm0]
    ring
  unfold harmonicEnergy
  convert hsum using 1
  exact hzero.symm

/-- Derivative form of frozen-model energy conservation. -/
theorem deriv_harmonicEnergy_of_frozen
    {m ω₀ : ℝ} {q p : ℝ → ℝ} (hm : 0 < m) (hω₀ : 0 < ω₀)
    (hq : Differentiable ℝ q) (hp : Differentiable ℝ p)
    (hmodel : FrozenCanonicalEquations m ω₀ q p) (s : ℝ) :
    deriv (fun u => harmonicEnergy m ω₀ (q u) (p u)) s = 0 := by
  have _ := hω₀
  exact (hasDerivAt_harmonicEnergy_of_frozen hm (hq s) (hp s)
    (hmodel s).1 (hmodel s).2).deriv

/-- Constant phase and constant frequency recover the frozen equations exactly. -/
theorem phaseDependent_frozen_iff (m ω₀ Γ₀ : ℝ) (q p : ℝ → ℝ) :
    PhaseDependentCanonicalEquations m (fun _ => ω₀) (fun _ => Γ₀) q p ↔
      FrozenCanonicalEquations m ω₀ q p := by
  rfl

end

end ElementalPeeling.LoopWall.PeelPotential
