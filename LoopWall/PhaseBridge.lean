import Mathlib

/-!
# The phase bridge: an equation of motion for the peel coordinate

`LoopWall/PeelPotential.lean` states the chain rule `force = -φ'(Γ) · 2/(1+X)² · X'` for a
potential of the peel coordinate, but it gives `Γ` no equation of motion of its own: the
oscillator acts on `X`, and the potential `φ` stays a free choice.  `BRIDGE.md` records that
gap.  Here `Γ` gets its equation of motion, from each of the two phase motions the framework
already uses, and the consequences for the potential are proved.

## The two phase motions

The library contains both of these as theorems about the same object:

* the log-ratio spacing `t = log (I/J)`, with `Γ = tanh (t/2) = G (exp t)`
  (`LoopWall/Ledger.lean`);
* the chromatic angle `φ`, with `Γ = -cos φ` (`LoopWall/ChromaticAngle.lean`,
  `peel_eq_neg_cos`).

A uniform phase means `t' = ω` in the first case and `φ' = ω` in the second.  Writing the
first through the phase ratio `z = exp t`, so that `t' = ω` is exactly `z' = ω z`, it gives
the peel equation of motion

  `Γ' = (ω/2) (1 - Γ²)`   (`peel_ode_of_phase_ode`),

and the reconstruction runs the other way too (`phase_ode_of_peel_ode`): the peel ODE *is*
the uniform-log-ratio phase statement, written in the peel variable.  The second gives

  `Γ' = ω sin φ`,  `Γ'' = -ω² Γ`,  `(Γ')² = ω² (1 - Γ²)`
  (`angle_peel_ode`, `angle_peel_harmonic`, `angle_speed_sq`):

the peel is a harmonic oscillator.

## What the equation of motion forces about the potential

Along the peel ODE the ledger `φled Γ = -(1/2) log (1 - Γ²)` has rate `S' = (ω/2) Γ`
(`ledger_rate`) — it is the readout whose rate is *proportional to the peel itself* — and it
obeys the bridge equation

  `S'' = (ω²/4) exp (-2 S)`,  `(S')² = (ω²/4) (1 - exp (-2 S))`
  (`ledger_second_order`, `ledger_speed_sq`),

the Euler–Lagrange equation of `½ S'² - (ω²/8) exp (-2 S)`, with the exact conserved value
`ω²/8` (`ledger_energy_eq`, `ledger_is_euler_lagrange`).  The angle phase gives the other
bridge equation, `S'' = ω² exp (2 S)` (`angle_ledger_second_order`).

## What it does not force

The equation of motion does not select the ledger.  The phase motion's own potential,
written in the peel coordinate, is `1/2 m ω² X²` with `X = (1+Γ)/(1-Γ)`, i.e.
`harmPotInPeel m ω Γ = (m ω²/2) ((1+Γ)/(1-Γ))²` (`harmPotInPeel_G`); it differs from the
ledger already at `Γ = 0` (`potentials_differ_at_zero`), and at the wall it is
`(m ω²/2)(17 + 12√2)` against `(1/2) log 2` (`harmPotInPeel_wall`,
`potentials_differ_at_wall`).  What does select the ledger is the composition principle: it
is the log-determinant of the shares, exactly (`φled_eq_log_det_shares`), matching
`LoopWall/MatrixLedger.lean` and `FisherMatrix.matrixLedger_eq_two_scalarLedgerPotential`.

## The wall has a clock

Both phase motions date the wall exactly.  A uniform log-ratio phase reaches it at
`2 log (1+√2) / ω`, the ratio there being `3 + 2√2` (`wall_clock`, `wall_ratio_sq`,
`G_at_wall_ratio`).  A uniform angle phase reaches it at `φ = π/4` (`angle_wall_clock`).
The two motions also predict different peel rates: `ω/4` against `ω/√2` at the wall
(`peel_rate_at_wall_log_ratio`, `peel_speed_sq_at_zero_angle`), and `ω/2` against `ω` at
zero reflection (`peel_rate_at_zero_log_ratio`).  The two bridges are therefore separated by
a first-derivative measurement, not only by the potential they choose.
-/

namespace ElementalPeeling.LoopWall.PhaseBridge

noncomputable section

/-- The peel map: a ratio of two readings goes to the reflection. -/
def G (z : ℝ) : ℝ := (z - 1) / (z + 1)

/-- The scalar ledger as a potential of the peel coordinate. -/
def φled (Γ : ℝ) : ℝ := -(1 / 2 : ℝ) * Real.log (1 - Γ ^ 2)

/-- The wall coordinate. -/
def wall : ℝ := 1 / Real.sqrt 2

/-- The inverse peel map: the phase ratio behind a reflection. -/
def phaseOfPeel (Γ : ℝ) : ℝ := (1 + Γ) / (1 - Γ)

/-- The peel of a chromatic angle. -/
def peelOfAngle (φ : ℝ) : ℝ := -Real.cos φ

/-! ## Derivative of the peel map and its inverse -/

theorem hasDerivAt_G (z : ℝ) (hz : 1 + z ≠ 0) : HasDerivAt G (2 / (1 + z) ^ 2) z := by
  have hz' : z + 1 ≠ 0 := by simpa [add_comm] using hz
  have h := ((hasDerivAt_id z).sub_const 1).div
    ((hasDerivAt_id z).add_const 1) hz'
  convert h using 1
  · ext w
    rfl
  · field_simp [hz']
    simp only [id_eq]
    ring

theorem deriv_G (z : ℝ) (hz : 1 + z ≠ 0) : deriv G z = 2 / (1 + z) ^ 2 :=
  (hasDerivAt_G z hz).deriv

theorem hasDerivAt_phaseOfPeel (Γ : ℝ) (h : 1 - Γ ≠ 0) :
    HasDerivAt phaseOfPeel (2 / (1 - Γ) ^ 2) Γ := by
  have hnum : HasDerivAt (fun x : ℝ => 1 + x) 1 Γ := (hasDerivAt_id Γ).const_add 1
  have hden : HasDerivAt (fun x : ℝ => 1 - x) (-1) Γ := by
    have h := (hasDerivAt_const Γ (1 : ℝ)).sub (hasDerivAt_id Γ)
    convert h using 1
    · ext x
      rfl
    · ring
  have h := hnum.div hden h
  convert h using 1
  · ext w
    rfl
  · field_simp [h]
    ring

theorem deriv_phaseOfPeel (Γ : ℝ) (h : 1 - Γ ≠ 0) :
    deriv phaseOfPeel Γ = 2 / (1 - Γ) ^ 2 :=
  (hasDerivAt_phaseOfPeel Γ h).deriv

/-! ## The algebraic heart: the peel map sends the phase volume to the reflection -/

theorem one_sub_sq_G (z : ℝ) (hz : 1 + z ≠ 0) : 1 - G z ^ 2 = 4 * z / (1 + z) ^ 2 := by
  unfold G
  have hz' : z + 1 ≠ 0 := by simpa [add_comm] using hz
  field_simp [hz']
  ring

theorem one_sub_sq_G_pos {z : ℝ} (hz : 0 < z) : 0 < 1 - G z ^ 2 := by
  have h : 1 + z ≠ 0 := by positivity
  rw [one_sub_sq_G z h]
  have : 0 < (1 + z) ^ 2 := by positivity
  positivity

theorem phaseOfPeel_G (z : ℝ) (hz : 1 + z ≠ 0) : phaseOfPeel (G z) = z := by
  unfold phaseOfPeel G
  have hz' : z + 1 ≠ 0 := by simpa [add_comm] using hz
  field_simp [hz']
  ring

theorem G_phaseOfPeel (Γ : ℝ) (h : 1 - Γ ≠ 0) : G (phaseOfPeel Γ) = Γ := by
  unfold phaseOfPeel G
  field_simp [h]
  ring

/-! ## The equation of motion for the peel coordinate -/

/-- A uniform log-ratio phase `z' = ω z` is the same motion as the peel-coordinate ODE
`Γ' = (ω/2)(1 - Γ²)`. -/
theorem peel_ode_of_phase_ode {z : ℝ → ℝ} {ω s : ℝ}
    (hz : HasDerivAt z (ω * z s) s) (h : 1 + z s ≠ 0) :
    HasDerivAt (fun u => G (z u)) ((ω / 2) * (1 - G (z s) ^ 2)) s := by
  have hcomp : HasDerivAt (fun u => G (z u)) ((2 / (1 + z s) ^ 2) * (ω * z s)) s :=
    (hasDerivAt_G (z s) h).comp s hz
  have key : (2 / (1 + z s) ^ 2) * (ω * z s) = (ω / 2) * (1 - G (z s) ^ 2) := by
    rw [one_sub_sq_G (z s) h]
    field_simp [h]
    ring
  rw [key] at hcomp
  exact hcomp

/-- Conversely the peel ODE reconstructs the uniform log-ratio phase: no information is lost. -/
theorem phase_ode_of_peel_ode {Γ : ℝ → ℝ} {ω s : ℝ}
    (hΓ : HasDerivAt Γ ((ω / 2) * (1 - Γ s ^ 2)) s) (h : Γ s ≠ 1) :
    HasDerivAt (fun u => phaseOfPeel (Γ u)) (ω * phaseOfPeel (Γ s)) s := by
  have h1 : 1 - Γ s ≠ 0 := by
    intro h0
    exact h (by linarith)
  have hcomp : HasDerivAt (fun u => phaseOfPeel (Γ u))
      ((2 / (1 - Γ s) ^ 2) * ((ω / 2) * (1 - Γ s ^ 2))) s :=
    (hasDerivAt_phaseOfPeel (Γ s) h1).comp s hΓ
  have key : (2 / (1 - Γ s) ^ 2) * ((ω / 2) * (1 - Γ s ^ 2)) = ω * phaseOfPeel (Γ s) := by
    unfold phaseOfPeel
    field_simp [h1]
    ring
  rw [key] at hcomp
  exact hcomp

/-- The closed form of the uniform log-ratio phase: the peel starts at `0` and moves as
`G (exp (ω s))`. -/
theorem peel_zero : G 1 = 0 := by
  unfold G
  norm_num

theorem phase_ode_exp (ω z₀ s : ℝ) :
    HasDerivAt (fun u => z₀ * Real.exp (ω * u)) ((ω * z₀ * Real.exp (ω * s))) s := by
  have h : HasDerivAt (fun u : ℝ => ω * u) ω s := by
    simpa using (hasDerivAt_id s).const_mul ω
  have hexp := Real.hasDerivAt_exp (ω * s)
  have := hexp.comp s h
  have h2 : HasDerivAt (fun u : ℝ => z₀ * Real.exp (ω * u))
      (z₀ * (Real.exp (ω * s) * ω)) s := this.const_mul z₀
  convert h2 using 1
  ring

theorem sq_lt_one_of_abs_lt_one {Γ : ℝ} (hΓ : |Γ| < 1) : Γ ^ 2 < 1 := by
  have h := (sq_lt_sq₀ (abs_nonneg Γ) (by norm_num : (0 : ℝ) ≤ 1)).2 hΓ
  simpa [sq_abs] using h

theorem abs_lt_one_of_sq_lt_one {Γ : ℝ} (h : Γ ^ 2 < 1) : |Γ| < 1 := by
  rw [abs_lt]
  constructor <;> nlinarith [sq_nonneg (Γ + 1), sq_nonneg (Γ - 1)]

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

theorem deriv_φled {Γ : ℝ} (hΓ : |Γ| < 1) : deriv φled Γ = Γ / (1 - Γ ^ 2) :=
  (hasDerivAt_φled hΓ).deriv

/-- The key identity: the potential's exponential is the phase volume `1 - Γ²`. -/
theorem exp_neg_two_φled {Γ : ℝ} (h : |Γ| < 1) : Real.exp (-2 * φled Γ) = 1 - Γ ^ 2 := by
  have hpos : 0 < 1 - Γ ^ 2 := sub_pos.mpr (sq_lt_one_of_abs_lt_one h)
  unfold φled
  rw [show -2 * (-(1 / 2 : ℝ) * Real.log (1 - Γ ^ 2)) = Real.log (1 - Γ ^ 2) by ring]
  exact Real.exp_log hpos

/-- Along the peel equation of motion the ledger's rate is proportional to the peel. -/
theorem ledger_rate {Γ : ℝ → ℝ} {ω s : ℝ}
    (hΓ : HasDerivAt Γ ((ω / 2) * (1 - Γ s ^ 2)) s) (habs : |Γ s| < 1) :
    HasDerivAt (fun u => φled (Γ u)) ((ω / 2) * Γ s) s := by
  have h1 : 1 - Γ s ^ 2 ≠ 0 := ne_of_gt (sub_pos.mpr (sq_lt_one_of_abs_lt_one habs))
  have hcomp := (hasDerivAt_φled habs).comp s hΓ
  have key : (Γ s / (1 - Γ s ^ 2)) * ((ω / 2) * (1 - Γ s ^ 2)) = (ω / 2) * Γ s := by
    field_simp [h1]
  rw [key] at hcomp
  exact hcomp

/-- The bridge equation: the ledger obeys `S'' = (ω²/4) exp (-2 S)`. -/
theorem ledger_second_order {Γ : ℝ → ℝ} {ω : ℝ}
    (hΓ : ∀ u, HasDerivAt Γ ((ω / 2) * (1 - Γ u ^ 2)) u)
    (habs : ∀ u, |Γ u| < 1) (s : ℝ) :
    HasDerivAt (fun u => deriv (fun v => φled (Γ v)) u)
      ((ω ^ 2 / 4) * Real.exp (-2 * φled (Γ s))) s := by
  have hfun : (fun u => deriv (fun v => φled (Γ v)) u) = fun u => (ω / 2) * Γ u := by
    funext u
    exact (ledger_rate (hΓ u) (habs u)).deriv
  rw [hfun]
  have hd : HasDerivAt (fun u => (ω / 2) * Γ u) ((ω / 2) * ((ω / 2) * (1 - Γ s ^ 2))) s :=
    (hΓ s).const_mul (ω / 2)
  have key : (ω / 2) * ((ω / 2) * (1 - Γ s ^ 2)) =
      (ω ^ 2 / 4) * Real.exp (-2 * φled (Γ s)) := by
    rw [exp_neg_two_φled (habs s)]
    ring
  rw [key] at hd
  exact hd

/-- The first-order law: the ledger's squared speed is `(ω²/4)(1 - exp (-2 S))`. -/
theorem ledger_speed_sq {Γ : ℝ → ℝ} {ω : ℝ}
    (hΓ : ∀ u, HasDerivAt Γ ((ω / 2) * (1 - Γ u ^ 2)) u)
    (habs : ∀ u, |Γ u| < 1) (u : ℝ) :
    (deriv (fun v => φled (Γ v)) u) ^ 2 =
      (ω ^ 2 / 4) * (1 - Real.exp (-2 * φled (Γ u))) := by
  rw [(ledger_rate (hΓ u) (habs u)).deriv, exp_neg_two_φled (habs u)]
  ring

/-- The conserved quantity of the bridge equation is exactly `ω²/8`. -/
theorem ledger_energy_eq {Γ : ℝ → ℝ} {ω : ℝ}
    (hΓ : ∀ u, HasDerivAt Γ ((ω / 2) * (1 - Γ u ^ 2)) u)
    (habs : ∀ u, |Γ u| < 1) (u : ℝ) :
    (1 / 2) * (deriv (fun v => φled (Γ v)) u) ^ 2
      + (ω ^ 2 / 8) * Real.exp (-2 * φled (Γ u)) = ω ^ 2 / 8 := by
  rw [(ledger_rate (hΓ u) (habs u)).deriv, exp_neg_two_φled (habs u)]
  ring

theorem deriv_exp_neg_two_mul (c S : ℝ) :
    deriv (fun x => c * Real.exp (-2 * x)) S = -2 * c * Real.exp (-2 * S) := by
  have h : HasDerivAt (fun x : ℝ => -2 * x) (-2) S := by
    simpa using (hasDerivAt_id S).const_mul (-2)
  have h2 : HasDerivAt (fun x : ℝ => Real.exp (-2 * x)) (Real.exp (-2 * S) * -2) S :=
    (Real.hasDerivAt_exp (-2 * S)).comp S h
  have h3 : HasDerivAt (fun x : ℝ => c * Real.exp (-2 * x)) (c * (Real.exp (-2 * S) * -2)) S :=
    h2.const_mul c
  rw [h3.deriv]
  ring

/-- The bridge equation is the Euler–Lagrange equation of `½ S'² - (ω²/8) exp (-2 S)`,
so the ledger is a variational object, not just a bookkeeping choice. -/
theorem ledger_is_euler_lagrange {Γ : ℝ → ℝ} {ω : ℝ}
    (hΓ : ∀ u, HasDerivAt Γ ((ω / 2) * (1 - Γ u ^ 2)) u)
    (habs : ∀ u, |Γ u| < 1) (s : ℝ) :
    HasDerivAt (fun u => deriv (fun v => φled (Γ v)) u)
      (-deriv (fun x => (ω ^ 2 / 8) * Real.exp (-2 * x)) (φled (Γ s))) s := by
  rw [deriv_exp_neg_two_mul]
  have h := ledger_second_order hΓ habs s
  convert h using 1
  ring

/-! ## The chromatic-angle phase -/

theorem hasDerivAt_peelOfAngle (φ : ℝ) : HasDerivAt peelOfAngle (Real.sin φ) φ := by
  have h := (Real.hasDerivAt_cos φ).neg
  convert h using 1
  · ext x
    rfl
  · simp

theorem angle_peel_ode {φ : ℝ → ℝ} {ω s : ℝ} (hφ : HasDerivAt φ ω s) :
    HasDerivAt (fun u => peelOfAngle (φ u)) (ω * Real.sin (φ s)) s := by
  have hcomp := (hasDerivAt_peelOfAngle (φ s)).comp s hφ
  convert hcomp using 1
  · ext u
    rfl
  · ring

theorem one_sub_sq_peelOfAngle (φ : ℝ) : 1 - peelOfAngle φ ^ 2 = Real.sin φ ^ 2 := by
  unfold peelOfAngle
  have := Real.sin_sq φ
  nlinarith

theorem φled_peelOfAngle (φ : ℝ) :
    φled (peelOfAngle φ) = -(1 / 2 : ℝ) * Real.log (Real.sin φ ^ 2) := by
  unfold φled
  rw [one_sub_sq_peelOfAngle]

/-- Under a uniform angle the peel is a harmonic oscillator with the same frequency. -/
theorem angle_peel_harmonic {φ : ℝ → ℝ} {ω : ℝ} (hφ : ∀ u, HasDerivAt φ ω u) (s : ℝ) :
    HasDerivAt (fun u => deriv (fun v => peelOfAngle (φ v)) u)
      (-(ω ^ 2) * peelOfAngle (φ s)) s := by
  have hfun : (fun u => deriv (fun v => peelOfAngle (φ v)) u) = fun u => ω * Real.sin (φ u) := by
    funext u
    exact (angle_peel_ode (hφ u)).deriv
  rw [hfun]
  have hsin : HasDerivAt (fun u => Real.sin (φ u)) (Real.cos (φ s) * ω) s :=
    (Real.hasDerivAt_sin (φ s)).comp s (hφ s)
  have hd : HasDerivAt (fun u => ω * Real.sin (φ u)) (ω * (Real.cos (φ s) * ω)) s :=
    hsin.const_mul ω
  have key : ω * (Real.cos (φ s) * ω) = -(ω ^ 2) * peelOfAngle (φ s) := by
    unfold peelOfAngle
    ring
  rw [key] at hd
  exact hd

theorem angle_speed_sq {φ : ℝ → ℝ} {ω : ℝ} (hφ : ∀ u, HasDerivAt φ ω u) (s : ℝ) :
    (deriv (fun v => peelOfAngle (φ v)) s) ^ 2 = ω ^ 2 * (1 - peelOfAngle (φ s) ^ 2) := by
  rw [(angle_peel_ode (hφ s)).deriv, one_sub_sq_peelOfAngle]
  ring

/-- The ledger along a uniform angle: rate `-ω cot φ`. -/
theorem angle_ledger_rate {φ : ℝ → ℝ} {ω : ℝ} (hφ : ∀ u, HasDerivAt φ ω u)
    (hsin : ∀ u, Real.sin (φ u) ≠ 0) (s : ℝ) :
    HasDerivAt (fun u => φled (peelOfAngle (φ u)))
      (-(ω * Real.cos (φ s)) / Real.sin (φ s)) s := by
  have hfun : (fun u => φled (peelOfAngle (φ u)))
      = fun u => -(1 / 2 : ℝ) * Real.log (Real.sin (φ u) ^ 2) := by
    funext u
    rw [φled_peelOfAngle]
  rw [hfun]
  have hsin' : HasDerivAt (fun u => Real.sin (φ u)) (Real.cos (φ s) * ω) s :=
    (Real.hasDerivAt_sin (φ s)).comp s (hφ s)
  have hsq : HasDerivAt (fun u => Real.sin (φ u) ^ 2)
      (2 * Real.sin (φ s) ^ (2 - 1) * (Real.cos (φ s) * ω)) s := hsin'.pow 2
  have hne : Real.sin (φ s) ^ 2 ≠ 0 := pow_ne_zero 2 (hsin s)
  have hlog := hsq.log hne
  have hfin := hlog.const_mul (-(1 / 2 : ℝ))
  have hval : -(1 / 2 : ℝ) * ((2 * Real.sin (φ s) ^ (2 - 1) * (Real.cos (φ s) * ω))
      / Real.sin (φ s) ^ 2) = -(ω * Real.cos (φ s)) / Real.sin (φ s) := by
    field_simp [hsin s]
    ring
  rw [hval] at hfin
  exact hfin

theorem exp_two_φled_peelOfAngle {φ : ℝ} (h : Real.sin φ ≠ 0) :
    Real.exp (2 * φled (peelOfAngle φ)) = 1 / Real.sin φ ^ 2 := by
  rw [φled_peelOfAngle]
  have hpos : 0 < Real.sin φ ^ 2 := by positivity
  rw [show 2 * (-(1 / 2 : ℝ) * Real.log (Real.sin φ ^ 2)) = -Real.log (Real.sin φ ^ 2) by ring,
    Real.exp_neg, Real.exp_log hpos]
  ring

/-- The angle bridge equation in the ledger variable: `S'' = ω² exp (2 S)`. -/
theorem angle_ledger_second_order {φ : ℝ → ℝ} {ω : ℝ} (hφ : ∀ u, HasDerivAt φ ω u)
    (hsin : ∀ u, Real.sin (φ u) ≠ 0) (s : ℝ) :
    HasDerivAt (fun u => deriv (fun v => φled (peelOfAngle (φ v))) u)
      (ω ^ 2 * Real.exp (2 * φled (peelOfAngle (φ s)))) s := by
  rw [exp_two_φled_peelOfAngle (hsin s)]
  have hfun : (fun u => deriv (fun v => φled (peelOfAngle (φ v))) u)
      = fun u => -(ω * Real.cos (φ u)) / Real.sin (φ u) := by
    funext u
    exact (angle_ledger_rate hφ hsin u).deriv
  rw [hfun]
  have hnum : HasDerivAt (fun u => -(ω * Real.cos (φ u))) (ω ^ 2 * Real.sin (φ s)) s := by
    have hc : HasDerivAt (fun u => Real.cos (φ u)) (-Real.sin (φ s) * ω) s :=
      (Real.hasDerivAt_cos (φ s)).comp s (hφ s)
    have h1 : HasDerivAt (fun u => ω * Real.cos (φ u)) (ω * (-Real.sin (φ s) * ω)) s :=
      hc.const_mul ω
    have h2 := h1.neg
    convert h2 using 1
    ring
  have hden : HasDerivAt (fun u => Real.sin (φ u)) (Real.cos (φ s) * ω) s :=
    (Real.hasDerivAt_sin (φ s)).comp s (hφ s)
  have hquot := hnum.div hden (hsin s)
  have hval : (ω ^ 2 * Real.sin (φ s) * Real.sin (φ s)
        - (-(ω * Real.cos (φ s))) * (Real.cos (φ s) * ω)) / Real.sin (φ s) ^ 2
      = ω ^ 2 * (Real.sin (φ s) ^ 2)⁻¹ := by
    have hs : Real.sin (φ s) ^ 2 + Real.cos (φ s) ^ 2 = 1 := Real.sin_sq_add_cos_sq (φ s)
    field_simp [hsin s]
    nlinarith [hs]
  rw [hval] at hquot
  convert hquot using 1
  ring

theorem φled_zero : φled 0 = 0 := by
  unfold φled
  norm_num

theorem φled_wall : φled wall = (1 / 2 : ℝ) * Real.log 2 := by
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hw : wall ^ 2 = (1 / 2 : ℝ) := by
    unfold wall
    rw [div_pow, one_pow, hs]
  unfold φled
  rw [hw]
  have hlog : Real.log (1 - (1 / 2 : ℝ)) = -Real.log 2 := by
    rw [show 1 - (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [hlog]
  ring

theorem two_φled_eq_neg_log_volume (Γ : ℝ) : 2 * φled Γ = -Real.log (1 - Γ ^ 2) := by
  unfold φled
  ring

/-! ## The wall ratios and the clock -/

theorem G_at_wall_ratio : G (3 + 2 * Real.sqrt 2) = wall := by
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hpos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  unfold G wall
  rw [div_eq_div_iff (by positivity) (by positivity)]
  field_simp
  nlinarith [hs]

/-- Swapping the two readings negates the peel: `G` is odd under `z ↦ 1/z`. -/
theorem G_inv (z : ℝ) (hz : z ≠ 0) : G (1 / z) = -G z := by
  unfold G
  field_simp [hz]
  ring

theorem three_sub_two_sqrt_two_inv :
    (3 - 2 * Real.sqrt 2) = 1 / (3 + 2 * Real.sqrt 2) := by
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rw [eq_div_iff (by positivity)]
  nlinarith [hs]

theorem G_at_conjugate_ratio : G (3 - 2 * Real.sqrt 2) = -wall := by
  rw [three_sub_two_sqrt_two_inv, G_inv _ (by positivity), G_at_wall_ratio]

/-- The wall is exactly the pair of phase ratios `3 ± 2√2`. -/
theorem wall_ratio_sq {z : ℝ} (hz : 1 + z ≠ 0) : G z ^ 2 = 1 / 2 ↔ z ^ 2 - 6 * z + 1 = 0 := by
  have hz' : z + 1 ≠ 0 := by simpa [add_comm] using hz
  have hz2 : (z + 1) ^ 2 ≠ 0 := pow_ne_zero 2 hz'
  unfold G
  rw [div_pow]
  constructor
  · intro h
    have h2 : 2 * ((z - 1) ^ 2) = (z + 1) ^ 2 := by
      rw [div_eq_iff (pow_ne_zero 2 hz')] at h
      linarith
    nlinarith [h2]
  · intro h
    have h2 : 2 * ((z - 1) ^ 2) = (z + 1) ^ 2 := by nlinarith [h]
    rw [div_eq_iff (pow_ne_zero 2 hz')]
    linarith

theorem log_wall_ratio : Real.log (3 + 2 * Real.sqrt 2) = 2 * Real.log (1 + Real.sqrt 2) := by
  have hsq : (1 + Real.sqrt 2) ^ 2 = 3 + 2 * Real.sqrt 2 := by
    rw [add_sq, Real.sq_sqrt (by norm_num)]
    ring
  rw [← hsq, Real.log_pow]
  push_cast
  ring

/-- The exact time at which a uniform log-ratio phase reaches the wall. -/
theorem wall_clock {ω : ℝ} (hω : ω ≠ 0) :
    G (Real.exp (ω * (2 * Real.log (1 + Real.sqrt 2) / ω))) = wall := by
  have h1 : ω * (2 * Real.log (1 + Real.sqrt 2) / ω) = 2 * Real.log (1 + Real.sqrt 2) := by
    field_simp [hω]
  rw [h1, ← log_wall_ratio,
    Real.exp_log (by positivity : (0 : ℝ) < 3 + 2 * Real.sqrt 2), G_at_wall_ratio]

theorem wall_clock_value : 2 * Real.log (1 + Real.sqrt 2) = Real.log (3 + 2 * Real.sqrt 2) :=
  log_wall_ratio.symm

theorem cos_pi_div_four : Real.cos (Real.pi / 4) = Real.sqrt 2 / 2 := Real.cos_pi_div_four

theorem wall_eq_sqrt_two_div_two : wall = Real.sqrt 2 / 2 := by
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hpos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  unfold wall
  rw [div_eq_div_iff (by positivity) (by norm_num)]
  nlinarith [hs]

/-- The exact angle at which a uniform angle phase reaches the wall. -/
theorem angle_wall_clock : peelOfAngle (Real.pi / 4) = -wall := by
  unfold peelOfAngle
  rw [cos_pi_div_four, wall_eq_sqrt_two_div_two]

/-! ## The composition identity: the ledger is the log-determinant of the shares -/

theorem one_sub_sq_eq_four_shares {p0 p1 Γ : ℝ} (h : p0 + p1 = 1) (hΓ : Γ = p0 - p1) :
    1 - Γ ^ 2 = 4 * (p0 * p1) := by
  rw [hΓ]
  nlinarith [h]

theorem log_four : Real.log (4 : ℝ) = 2 * Real.log 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  push_cast
  ring

/-- The ledger is exactly the log-determinant of the two shares, up to the constant `log 2`. -/
theorem φled_eq_log_det_shares {p0 p1 Γ : ℝ} (h : p0 + p1 = 1) (hΓ : Γ = p0 - p1)
    (hpos : 0 < p0 * p1) :
    φled Γ = -(1 / 2 : ℝ) * Real.log (p0 * p1) - Real.log 2 := by
  unfold φled
  rw [one_sub_sq_eq_four_shares h hΓ,
    Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (ne_of_gt hpos), log_four]
  ring

/-! ## The oscillator's potential in the peel coordinate -/

/-- The harmonic potential of the phase motion, written in the peel coordinate. -/
def harmPotInPeel (m ω Γ : ℝ) : ℝ := (m * ω ^ 2 / 2) * phaseOfPeel Γ ^ 2

theorem phaseOfPeel_wall : phaseOfPeel wall = 3 + 2 * Real.sqrt 2 := by
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hpos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have h1 : 1 - 1 / Real.sqrt 2 ≠ 0 := by
    have hone : (1 : ℝ) < Real.sqrt 2 := by
      rw [Real.lt_sqrt (by norm_num)]
      norm_num
    have : 1 / Real.sqrt 2 < 1 := by
      rw [div_lt_one hpos]
      exact hone
    linarith
  unfold phaseOfPeel wall
  rw [div_eq_iff h1]
  field_simp
  nlinarith [hs]

theorem phaseOfPeel_zero : phaseOfPeel 0 = 1 := by
  unfold phaseOfPeel
  norm_num

theorem harmPotInPeel_G (m ω z : ℝ) (hz : 1 + z ≠ 0) :
    harmPotInPeel m ω (G z) = (m * ω ^ 2 / 2) * z ^ 2 := by
  unfold harmPotInPeel
  rw [phaseOfPeel_G z hz]

theorem harmPotInPeel_zero (m ω : ℝ) : harmPotInPeel m ω 0 = m * ω ^ 2 / 2 := by
  unfold harmPotInPeel
  rw [phaseOfPeel_zero]
  ring

theorem sq_three_add_two_sqrt_two : (3 + 2 * Real.sqrt 2) ^ 2 = 17 + 12 * Real.sqrt 2 := by
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rw [add_sq]
  nlinarith [hs]

theorem harmPotInPeel_wall (m ω : ℝ) :
    harmPotInPeel m ω wall = (m * ω ^ 2 / 2) * (17 + 12 * Real.sqrt 2) := by
  unfold harmPotInPeel
  rw [phaseOfPeel_wall, sq_three_add_two_sqrt_two]

/-- The ledger's force vanishes at zero reflection. -/
theorem deriv_φled_zero : deriv φled 0 = 0 := by
  rw [deriv_φled (by norm_num : |(0 : ℝ)| < 1)]
  norm_num

/-- The phase motion's own potential has a nonvanishing force there: `2 m ω²`. -/
theorem deriv_harmPotInPeel_zero (m ω : ℝ) :
    deriv (harmPotInPeel m ω) 0 = 2 * m * ω ^ 2 := by
  have hf : HasDerivAt phaseOfPeel (2 : ℝ) 0 := by
    have h := hasDerivAt_phaseOfPeel 0 (by norm_num : (1 : ℝ) - 0 ≠ 0)
    simpa using h
  have hsq : HasDerivAt (fun x : ℝ => phaseOfPeel x ^ 2)
      (2 * phaseOfPeel 0 ^ (2 - 1) * 2) 0 := by
    have h := hf.pow 2
    convert h using 1
  have hmul := hsq.const_mul (m * ω ^ 2 / 2)
  have hderiv : deriv (harmPotInPeel m ω) 0
      = (m * ω ^ 2 / 2) * (2 * phaseOfPeel 0 ^ (2 - 1) * 2) := by
    have hfun : harmPotInPeel m ω = fun x => (m * ω ^ 2 / 2) * (phaseOfPeel x ^ 2) := rfl
    rw [hfun]
    exact hmul.deriv
  rw [hderiv, phaseOfPeel_zero]
  norm_num
  ring

/-- The two candidate bridges disagree already at zero reflection. -/
theorem potentials_differ_at_zero {m ω : ℝ} (h : m * ω ^ 2 ≠ 0) :
    harmPotInPeel m ω 0 ≠ φled 0 := by
  rw [harmPotInPeel_zero, φled_zero]
  intro h0
  apply h
  linarith

/-- And they disagree by an unbounded factor at the wall: `(17 + 12√2)/2` against `½ log 2`. -/
theorem potentials_differ_at_wall : harmPotInPeel 1 1 wall ≠ φled wall := by
  rw [harmPotInPeel_wall, φled_wall]
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hlog : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  intro h0
  nlinarith [hs, hlog]

/-! ## The peel rates the two phase motions predict -/

theorem peel_rate_at_zero_log_ratio {Γ : ℝ → ℝ} {ω : ℝ}
    (hΓ : ∀ u, HasDerivAt Γ ((ω / 2) * (1 - Γ u ^ 2)) u) (h : Γ 0 = 0) :
    deriv Γ 0 = ω / 2 := by
  rw [(hΓ 0).deriv, h]
  ring

theorem peel_rate_at_wall_log_ratio {Γ : ℝ → ℝ} {ω : ℝ}
    (hΓ : ∀ u, HasDerivAt Γ ((ω / 2) * (1 - Γ u ^ 2)) u) (h : Γ 0 ^ 2 = 1 / 2) :
    deriv Γ 0 = ω / 4 := by
  rw [(hΓ 0).deriv, h]
  ring

theorem peel_speed_sq_at_zero_angle {φ : ℝ → ℝ} {ω : ℝ} (hφ : ∀ u, HasDerivAt φ ω u)
    (h : peelOfAngle (φ 0) = 0) :
    (deriv (fun v => peelOfAngle (φ v)) 0) ^ 2 = ω ^ 2 := by
  have := angle_speed_sq hφ 0
  rw [this, h]
  ring
end

end ElementalPeeling.LoopWall.PhaseBridge
