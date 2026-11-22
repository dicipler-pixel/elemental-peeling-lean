import Mathlib
import LoopWall.PeelPotential

/-!
Direction B1 of the fifth round (swarm `smws70oju`, member m1). The closure equation of motion on
the peel coordinate induced by a harmonic motion of `X`, and the exact first integral of it. This is
the module that answers the question `LoopWall/PeelPotential.lean` left open: the oscillator does act
on `X`, and pulling its motion through `Γ = G X` gives `Γ` an equation of motion — together with a
potential that is *not* the ledger.

Written in the fifth parallel formalization round and recompiled here before acceptance;
imports hoisted, namespace prefixed to `ElementalPeeling.LoopWall`, nothing else changed.
-/

/-
# Harmonic motion in the ratio coordinate induces peel dynamics

The oscillator acts on `X`.  We set `peel X s = G (X s)` and derive, rather than
assume, its second-order equation and its conserved energy.  The induced
potential is then compared with the scalar ledger, including after removing
the arbitrary additive constant at `Γ = 0`.
-/

namespace ElementalPeeling.LoopWall.PeelDynamics

noncomputable section

set_option maxHeartbeats 1000000

open ElementalPeeling.LoopWall.PeelPotential

/-- The peel path induced by a ratio path. -/
def peel (X : ℝ → ℝ) : ℝ → ℝ := fun s => G (X s)

/-- Harmonic energy written in the peel coordinate and its velocity. -/
def peelEnergy (m ω γ v : ℝ) : ℝ :=
  (1 / 2 : ℝ) * m *
    (4 * v ^ 2 / (1 - γ) ^ 4 + ω ^ 2 * (1 + γ) ^ 2 / (1 - γ) ^ 2)

/-- Mechanical harmonic energy of the original ratio path. -/
def mechanicalEnergy (m ω : ℝ) (X : ℝ → ℝ) : ℝ → ℝ := fun s =>
  (1 / 2 : ℝ) * m * ((deriv X s) ^ 2 + ω ^ 2 * (X s) ^ 2)

/-- The harmonic potential pulled back to the peel coordinate. -/
def inducedPotential (m ω γ : ℝ) : ℝ :=
  V m ω ((1 + γ) / (1 - γ))

/-- The same potential with its irrelevant additive constant fixed at zero. -/
def normalizedInducedPotential (m ω γ : ℝ) : ℝ :=
  inducedPotential m ω γ - inducedPotential m ω 0

section HarmonicPath

variable {m ω : ℝ} {X : ℝ → ℝ}
  (hX : Differentiable ℝ X)
  (hX2 : Differentiable ℝ (deriv X))
  (hden : ∀ s, 1 + X s ≠ 0)

include hden in
theorem one_sub_peel (s : ℝ) : 1 - peel X s = 2 / (1 + X s) := by
  have hx : X s + 1 ≠ 0 := by simpa [add_comm] using hden s
  simp only [peel, G]
  field_simp [hden s, hx]
  ring

include hden in
theorem one_add_peel (s : ℝ) : 1 + peel X s = 2 * X s / (1 + X s) := by
  have hx : X s + 1 ≠ 0 := by simpa [add_comm] using hden s
  simp only [peel, G]
  field_simp [hden s, hx]
  ring

include hden in
theorem one_sub_peel_ne (s : ℝ) : 1 - peel X s ≠ 0 := by
  rw [one_sub_peel hden]
  exact div_ne_zero (by norm_num) (hden s)

include hden in
/-- The inverse rational coordinate really undoes `G` away from its pole. -/
theorem inverse_peel (s : ℝ) : (1 + peel X s) / (1 - peel X s) = X s := by
  have hx : X s + 1 ≠ 0 := by simpa [add_comm] using hden s
  simp only [peel, G]
  field_simp [hden s, hx]
  ring

include hden in
/-- The pullback potential along the path is the oscillator's original potential. -/
theorem inducedPotential_peel (m ω : ℝ) (s : ℝ) :
    inducedPotential m ω (peel X s) = V m ω (X s) := by
  rw [inducedPotential, inverse_peel hden]

include hX hden in
theorem hasDerivAt_peel (s : ℝ) :
    HasDerivAt (peel X) (2 / (1 + X s) ^ 2 * deriv X s) s := by
  change HasDerivAt (fun u => G (X u))
    (2 / (1 + X s) ^ 2 * deriv X s) s
  exact (hasDerivAt_G (X s) (hden s)).comp s (hX s).hasDerivAt

include hX hden in
theorem deriv_peel (s : ℝ) :
    deriv (peel X) s = 2 / (1 + X s) ^ 2 * deriv X s :=
  (hasDerivAt_peel hX hden s).deriv

include hX hden in
theorem deriv_peel_function : deriv (peel X) =
    fun s => 2 * deriv X s / (1 + X s) ^ 2 := by
  funext s
  rw [deriv_peel hX hden]
  ring

include hX hX2 hden in
/-- A closed derivative formula for the induced peel velocity. -/
theorem hasDerivAt_deriv_peel (s : ℝ) :
    HasDerivAt (deriv (peel X))
      (2 * deriv (deriv X) s / (1 + X s) ^ 2
        - 4 * (deriv X s) ^ 2 / (1 + X s) ^ 3) s := by
  have hbase : HasDerivAt (fun u => 1 + X u) (deriv X s) s :=
    (hX s).hasDerivAt.const_add 1
  have hsq : HasDerivAt (fun u => (1 + X u) ^ 2)
      (2 * (1 + X s) * deriv X s) s := by
    convert hbase.pow 2 using 1
    norm_num
  have hqv := ((hX2 s).hasDerivAt.const_mul (2 : ℝ)).div hsq
    (pow_ne_zero 2 (hden s))
  rw [deriv_peel_function hX hden]
  have hqv' : HasDerivAt (fun u => 2 * deriv X u / (1 + X u) ^ 2)
      ((2 * deriv (deriv X) s * (1 + X s) ^ 2
        - 2 * deriv X s * (2 * (1 + X s) * deriv X s)) /
        ((1 + X s) ^ 2) ^ 2) s := by
    exact hqv
  convert hqv' using 1
  field_simp [hden s]
  ring

include hX hX2 hden in
/-- Harmonic motion of `X` closes to precisely this second-order ODE on its peel. -/
theorem peel_closure_ode
    (hosc : ∀ s, deriv (deriv X) s + ω ^ 2 * X s = 0) (s : ℝ) :
    deriv (deriv (peel X)) s * (1 - peel X s)
      + 2 * (deriv (peel X) s) ^ 2
      + (ω ^ 2 / 2) * (1 - peel X s) ^ 2 * (1 + peel X s) = 0 := by
  rw [(hasDerivAt_deriv_peel hX hX2 hden s).deriv, deriv_peel hX hden]
  have hacc : deriv (deriv X) s = -ω ^ 2 * X s := by
    linarith [hosc s]
  rw [hacc, one_sub_peel hden, one_add_peel hden]
  field_simp [hden s]
  ring

include hX hX2 in
/-- The original mechanical energy is conserved by the harmonic equation. -/
theorem hasDerivAt_mechanicalEnergy
    (hosc : ∀ s, deriv (deriv X) s + ω ^ 2 * X s = 0) (s : ℝ) :
    HasDerivAt (mechanicalEnergy m ω X) 0 s := by
  have hacc : deriv (deriv X) s = -ω ^ 2 * X s := by
    linarith [hosc s]
  have h := (((hX2 s).hasDerivAt.pow 2).add
    (((hX s).hasDerivAt.pow 2).const_mul (ω ^ 2))).const_mul ((1 / 2 : ℝ) * m)
  have hzero : (1 / 2 : ℝ) * m *
      (2 * deriv X s * deriv (deriv X) s
        + ω ^ 2 * (2 * X s * deriv X s)) = 0 := by
    rw [hacc]
    ring
  rw [← hzero]
  convert h using 1
  · ext u
    simp only [mechanicalEnergy, Pi.add_apply, Pi.pow_apply]
  · norm_num

include hX hden in
/-- The peel expression is exactly the original harmonic energy. -/
theorem peelEnergy_eq_mechanicalEnergy (s : ℝ) :
    peelEnergy m ω (peel X s) (deriv (peel X) s) = mechanicalEnergy m ω X s := by
  simp only [peelEnergy, mechanicalEnergy]
  rw [deriv_peel hX hden, one_sub_peel hden, one_add_peel hden]
  field_simp [hden s]
  ring

include hX hX2 hden in
/-- Hence the harmonic energy written in peel variables has derivative zero. -/
theorem hasDerivAt_peelEnergy
    (hosc : ∀ s, deriv (deriv X) s + ω ^ 2 * X s = 0) (s : ℝ) :
    HasDerivAt (fun u => peelEnergy m ω (peel X u) (deriv (peel X) u)) 0 s := by
  have heq : (fun u => peelEnergy m ω (peel X u) (deriv (peel X) u)) =
      mechanicalEnergy m ω X := by
    funext u
    exact peelEnergy_eq_mechanicalEnergy hX hden u
  rw [heq]
  exact hasDerivAt_mechanicalEnergy hX hX2 hosc s

include hX hX2 hden in
/-- The peel energy is a global first integral, not merely a pointwise identity. -/
theorem peelEnergy_first_integral
    (hosc : ∀ s, deriv (deriv X) s + ω ^ 2 * X s = 0) (s τ : ℝ) :
    peelEnergy m ω (peel X s) (deriv (peel X) s) =
      peelEnergy m ω (peel X τ) (deriv (peel X) τ) := by
  let E : ℝ → ℝ := fun u => peelEnergy m ω (peel X u) (deriv (peel X) u)
  have hdiff : Differentiable ℝ E := by
    intro u
    exact (hasDerivAt_peelEnergy hX hX2 hden hosc u).differentiableAt
  have hzero : ∀ u, deriv E u = 0 := by
    intro u
    exact (hasDerivAt_peelEnergy hX hX2 hden hosc u).deriv
  exact is_const_of_deriv_eq_zero hdiff hzero s τ

end HarmonicPath


/-- Derivative of the inverse peel coordinate. -/
theorem hasDerivAt_inverseCoordinate {γ : ℝ} (hγ : 1 - γ ≠ 0) :
    HasDerivAt (fun u : ℝ => (1 + u) / (1 - u)) (2 / (1 - γ) ^ 2) γ := by
  have h := ((hasDerivAt_id γ).const_add (1 : ℝ)).div
    ((hasDerivAt_const γ (1 : ℝ)).sub (hasDerivAt_id γ)) hγ
  convert h using 1
  · ext u
    rfl
  · norm_num
    ring

/-- The pullback harmonic potential has the expected rational force coefficient. -/
theorem hasDerivAt_inducedPotential (m ω : ℝ) {γ : ℝ} (hγ : 1 - γ ≠ 0) :
    HasDerivAt (inducedPotential m ω)
      (m * ω ^ 2 * ((1 + γ) / (1 - γ)) * (2 / (1 - γ) ^ 2)) γ := by
  change HasDerivAt (fun u : ℝ => V m ω ((1 + u) / (1 - u))) _ γ
  exact HasDerivAt.comp (h₂ := V m ω) γ
    (hasDerivAt_V m ω ((1 + γ) / (1 - γ))) (hasDerivAt_inverseCoordinate hγ)

/-- The induced potential is precisely the stated rational pullback of `V`. -/
theorem inducedPotential_eq (m ω γ : ℝ) :
    inducedPotential m ω γ = (1 / 2 : ℝ) * m * ω ^ 2 * ((1 + γ) / (1 - γ)) ^ 2 := by
  rfl

theorem inducedPotential_zero (m ω : ℝ) :
    inducedPotential m ω 0 = (1 / 2 : ℝ) * m * ω ^ 2 := by
  norm_num [inducedPotential, V]

theorem φled_zero : φled 0 = 0 := by
  norm_num [φled]

/-- At the symmetric point, the unnormalised pullback is not the ledger. -/
theorem inducedPotential_zero_ne_ledger {m ω : ℝ} (hm : 0 < m) (hω : ω ≠ 0) :
    inducedPotential m ω 0 ≠ φled 0 := by
  rw [inducedPotential_zero, φled_zero]
  exact mul_ne_zero (mul_ne_zero (by norm_num) (ne_of_gt hm)) (pow_ne_zero 2 hω)

theorem normalizedInducedPotential_zero (m ω : ℝ) :
    normalizedInducedPotential m ω 0 = 0 := by
  simp [normalizedInducedPotential]

theorem deriv_inducedPotential_zero (m ω : ℝ) :
    deriv (inducedPotential m ω) 0 = 2 * m * ω ^ 2 := by
  have h := (hasDerivAt_inducedPotential m ω (γ := 0) (by norm_num)).deriv
  norm_num at h
  rw [h]
  ring

theorem deriv_normalizedInducedPotential_zero (m ω : ℝ) :
    deriv (normalizedInducedPotential m ω) 0 = 2 * m * ω ^ 2 := by
  have h := (hasDerivAt_inducedPotential m ω (γ := 0) (by norm_num)).sub_const
    (inducedPotential m ω 0)
  change HasDerivAt (normalizedInducedPotential m ω) _ 0 at h
  rw [h.deriv]
  norm_num
  ring

theorem deriv_φled_zero : deriv φled 0 = 0 := by
  rw [deriv_φled (by norm_num : |(0 : ℝ)| < 1)]
  norm_num

/-- Even after matching the arbitrary additive constants, the slopes at zero differ. -/
theorem normalizedPotential_deriv_zero_ne_ledger {m ω : ℝ}
    (hm : 0 < m) (hω : ω ≠ 0) :
    deriv (normalizedInducedPotential m ω) 0 ≠ deriv φled 0 := by
  rw [deriv_normalizedInducedPotential_zero, deriv_φled_zero]
  exact mul_ne_zero (mul_ne_zero (by norm_num) (ne_of_gt hm)) (pow_ne_zero 2 hω)

/-- The ratio corresponding to the wall is exactly `(1 + sqrt 2)^2`. -/
theorem inverse_wall : (1 + wall) / (1 - wall) = 3 + 2 * Real.sqrt 2 := by
  have hr : Real.sqrt (2 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hr2 : Real.sqrt (2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hrgt : (1 : ℝ) < Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hrsub : Real.sqrt (2 : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr (ne_of_gt hrgt)
  have hradd : Real.sqrt (2 : ℝ) + 1 ≠ 0 := by positivity
  rw [wall]
  field_simp [hr, hrsub, hradd]
  nlinarith

theorem inducedPotential_wall (m ω : ℝ) :
    inducedPotential m ω wall = (1 / 2 : ℝ) * m * ω ^ 2 * (3 + 2 * Real.sqrt 2) ^ 2 := by
  rw [inducedPotential, inverse_wall, V]

theorem normalizedInducedPotential_wall_one_one :
    normalizedInducedPotential 1 1 wall = 8 + 6 * Real.sqrt 2 := by
  rw [normalizedInducedPotential, inducedPotential_wall, inducedPotential_zero]
  have hr2 : Real.sqrt (2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  norm_num
  nlinarith

/-- The zero-normalised unit pullback and the ledger are different at the wall. -/
theorem normalizedPotential_wall_ne_ledger :
    normalizedInducedPotential 1 1 wall ≠ φled wall := by
  rw [normalizedInducedPotential_wall_one_one]
  change 8 + 6 * Real.sqrt 2 ≠ φled (1 / Real.sqrt 2)
  rw [φled_wall]
  have hlog : Real.log 2 < 1 := by
    have h := Real.log_lt_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
      (show (2 : ℝ) ≠ 1 by norm_num)
    norm_num at h
    exact h
  have hsqrt : 1 < Real.sqrt (2 : ℝ) := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  nlinarith


end

end ElementalPeeling.LoopWall.PeelDynamics
