import Mathlib

/-!
# The conservative Hamiltonian block, and what it cannot produce

Direction D8 of the third round.  For `H (q p) = Σ i, p i^2/(2 m i) + V q` the module proves that
the canonical flow conserves the energy (`deriv_hamiltonian_conservative`) and, with a Rayleigh term
`- η i * p i` added to the momentum equation, that the energy derivative is the negative of the
dissipation power (`deriv_hamiltonian_rayleigh`), hence nonpositive for `η ≥ 0`
(`deriv_hamiltonian_rayleigh_nonpos`) and zero exactly when every momentum vanishes, which needs
`η > 0` (`deriv_hamiltonian_rayleigh_eq_zero_iff`).

The two controls are what the framework needs: the conservative and damped momentum equations are
incompatible at any nonzero momentum (`conservative_cannot_produce_rayleigh_at_nonzero_momentum`),
so dissipation is an addition and not a consequence of `H`; and Hamiltonian forcing must be
momentum-independent and equal to `-DW q` (`potential_forcing_is_configuration_gradient`), which a
nonzero Rayleigh term provably is not (`rayleigh_forcing_not_configuration_gradient`).

Written in the third parallel formalization round (swarm `smws58h9u`, direction m5), recompiled and
reviewed here; namespace and header added, `#print axioms` lines removed.
-/

namespace ElementalPeeling.LoopWall.Hamiltonian

open scoped BigOperators
open Finset

noncomputable section

variable {ι : Type*}

/-- The kinetic term in the Hamiltonian block. -/
def kineticEnergy [Fintype ι] (m : ι → ℝ) (p : ι → ℝ) : ℝ :=
  ∑ i, p i ^ 2 / (2 * m i)

/-- The conservative Hamiltonian block. -/
noncomputable def hamiltonian [Fintype ι] (m : ι → ℝ) (V : (ι → ℝ) → ℝ)
    (q p : ι → ℝ) : ℝ :=
  kineticEnergy m p + V q

/-- Coordinates of the configuration gradient, in the standard basis. -/
noncomputable def configurationGradient [DecidableEq ι] (V : (ι → ℝ) → ℝ) (q : ι → ℝ) (i : ι) : ℝ :=
  fderiv ℝ V q (Pi.single i 1)

/-- The (nonnegative, for positive masses and damping coefficients) Rayleigh power. -/
def rayleighPower [Fintype ι] (m η : ι → ℝ) (p : ι → ℝ) : ℝ :=
  ∑ i, η i * p i ^ 2 / m i

/-- A continuous linear functional on a finite real coordinate space is determined by
its values on the coordinate vectors. -/
theorem continuousLinearMap_apply_eq_sum_single [Fintype ι] [DecidableEq ι]
    (L : (ι → ℝ) →L[ℝ] ℝ) (v : ι → ℝ) :
    L v = ∑ i, v i * L (Pi.single i 1) := by
  conv_lhs => rw [pi_eq_sum_univ' v]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_smul]
  rfl

/-- Chain rule for the potential, written in coordinate-gradient form. -/
theorem hasDerivAt_potential_comp [Fintype ι] [DecidableEq ι]
    {V : (ι → ℝ) → ℝ} {q p : ℝ → ι → ℝ} {m : ι → ℝ} {s : ℝ}
    (hq : ∀ i, DifferentiableAt ℝ (fun t => q t i) s)
    (hV : DifferentiableAt ℝ V (q s))
    (hq' : ∀ i, deriv (fun t => q t i) s = p s i / m i) :
    HasDerivAt (fun t => V (q t))
      (∑ i, (p s i / m i) * configurationGradient V (q s) i) s := by
  have hqvec : HasDerivAt q (fun i => p s i / m i) s := by
    apply hasDerivAt_pi.mpr
    intro i
    rw [← hq' i]
    exact (hq i).hasDerivAt
  have hcomp := hV.hasFDerivAt.comp_hasDerivAt s hqvec
  convert hcomp using 1
  · ext t
    rfl
  · simpa only [configurationGradient] using
      (continuousLinearMap_apply_eq_sum_single (ι := ι)
        (fderiv ℝ V (q s)) (fun i => p s i / m i)).symm

/-- Energy derivative for the kinetic-plus-potential block, with an arbitrary
additional momentum forcing `F`.  The Hamiltonian terms cancel exactly. -/
theorem hasDerivAt_hamiltonian_forced [Fintype ι] [DecidableEq ι]
    {m : ι → ℝ} {V : (ι → ℝ) → ℝ}
    {F : (ι → ℝ) → (ι → ℝ) → ι → ℝ}
    {q p : ℝ → ι → ℝ} {s : ℝ}
    (hm : ∀ i, m i ≠ 0)
    (hq : ∀ i, DifferentiableAt ℝ (fun t => q t i) s)
    (hp : ∀ i, DifferentiableAt ℝ (fun t => p t i) s)
    (hV : DifferentiableAt ℝ V (q s))
    (hq' : ∀ i, deriv (fun t => q t i) s = p s i / m i)
    (hp' : ∀ i, deriv (fun t => p t i) s =
      -configurationGradient V (q s) i + F (q s) (p s) i) :
    HasDerivAt (fun t => hamiltonian m V (q t) (p t))
      (∑ i, (p s i / m i) * F (q s) (p s) i) s := by
  have hterm (i : ι) :
      HasDerivAt (fun t => p t i ^ 2 / (2 * m i))
        (p s i * deriv (fun t => p t i) s / m i) s := by
    have hpi := (hp i).hasDerivAt
    have hprod := (hpi.mul hpi).div_const (2 * m i)
    convert hprod using 1
    · ext t
      simp only [pow_two, Pi.mul_apply]
    · field_simp [hm i]
      ring
  have hkin : HasDerivAt (fun t => kineticEnergy m (p t))
      (∑ i, p s i * deriv (fun t => p t i) s / m i) s := by
    have h := HasDerivAt.sum (u := Finset.univ) (fun i _ => hterm i)
    unfold kineticEnergy
    convert h using 1
    ext t
    simp only [Finset.sum_apply]
  have hpot := hasDerivAt_potential_comp hq hV hq'
  have hsum := hkin.add hpot
  convert hsum using 1
  · rfl
  · rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hp' i]
    field_simp [hm i]
    ring

/-- Conservative Hamilton equations imply conservation of the Hamiltonian. -/
theorem hasDerivAt_hamiltonian_conservative [Fintype ι] [DecidableEq ι]
    {m : ι → ℝ} {V : (ι → ℝ) → ℝ}
    {q p : ℝ → ι → ℝ} {s : ℝ}
    (hm : ∀ i, m i ≠ 0)
    (hq : ∀ i, DifferentiableAt ℝ (fun t => q t i) s)
    (hp : ∀ i, DifferentiableAt ℝ (fun t => p t i) s)
    (hV : DifferentiableAt ℝ V (q s))
    (hq' : ∀ i, deriv (fun t => q t i) s = p s i / m i)
    (hp' : ∀ i, deriv (fun t => p t i) s = -configurationGradient V (q s) i) :
    HasDerivAt (fun t => hamiltonian m V (q t) (p t)) 0 s := by
  let F : (ι → ℝ) → (ι → ℝ) → ι → ℝ := fun _ _ _ => 0
  have h := hasDerivAt_hamiltonian_forced (F := F) hm hq hp hV hq'
    (fun i => by simpa [F] using hp' i)
  simpa [F] using h

/-- Derivative form of conservative energy conservation. -/
theorem deriv_hamiltonian_conservative [Fintype ι] [DecidableEq ι]
    {m : ι → ℝ} {V : (ι → ℝ) → ℝ}
    {q p : ℝ → ι → ℝ} {s : ℝ}
    (hm : ∀ i, m i ≠ 0)
    (hq : ∀ i, DifferentiableAt ℝ (fun t => q t i) s)
    (hp : ∀ i, DifferentiableAt ℝ (fun t => p t i) s)
    (hV : DifferentiableAt ℝ V (q s))
    (hq' : ∀ i, deriv (fun t => q t i) s = p s i / m i)
    (hp' : ∀ i, deriv (fun t => p t i) s = -configurationGradient V (q s) i) :
    deriv (fun t => hamiltonian m V (q t) (p t)) s = 0 :=
  (hasDerivAt_hamiltonian_conservative hm hq hp hV hq' hp').deriv

/-- Rayleigh damping gives the exact energy-loss rate. -/
theorem hasDerivAt_hamiltonian_rayleigh [Fintype ι] [DecidableEq ι]
    {m η : ι → ℝ} {V : (ι → ℝ) → ℝ}
    {q p : ℝ → ι → ℝ} {s : ℝ}
    (hm : ∀ i, m i ≠ 0)
    (hq : ∀ i, DifferentiableAt ℝ (fun t => q t i) s)
    (hp : ∀ i, DifferentiableAt ℝ (fun t => p t i) s)
    (hV : DifferentiableAt ℝ V (q s))
    (hq' : ∀ i, deriv (fun t => q t i) s = p s i / m i)
    (hp' : ∀ i, deriv (fun t => p t i) s =
      -configurationGradient V (q s) i - η i * p s i) :
    HasDerivAt (fun t => hamiltonian m V (q t) (p t))
      (-rayleighPower m η (p s)) s := by
  let F : (ι → ℝ) → (ι → ℝ) → ι → ℝ := fun _ p i => -η i * p i
  have h := hasDerivAt_hamiltonian_forced (F := F) hm hq hp hV hq'
    (fun i => by simpa [F, sub_eq_add_neg, add_comm] using hp' i)
  convert h using 1
  simp only [F, rayleighPower, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  field_simp [hm i]

/-- Derivative form of the Rayleigh energy-loss identity. -/
theorem deriv_hamiltonian_rayleigh [Fintype ι] [DecidableEq ι]
    {m η : ι → ℝ} {V : (ι → ℝ) → ℝ}
    {q p : ℝ → ι → ℝ} {s : ℝ}
    (hm : ∀ i, m i ≠ 0)
    (hq : ∀ i, DifferentiableAt ℝ (fun t => q t i) s)
    (hp : ∀ i, DifferentiableAt ℝ (fun t => p t i) s)
    (hV : DifferentiableAt ℝ V (q s))
    (hq' : ∀ i, deriv (fun t => q t i) s = p s i / m i)
    (hp' : ∀ i, deriv (fun t => p t i) s =
      -configurationGradient V (q s) i - η i * p s i) :
    deriv (fun t => hamiltonian m V (q t) (p t)) s =
      -rayleighPower m η (p s) :=
  (hasDerivAt_hamiltonian_rayleigh hm hq hp hV hq' hp').deriv

theorem rayleighPower_nonneg [Fintype ι] {m η : ι → ℝ} {p : ι → ℝ}
    (hm : ∀ i, 0 < m i) (hη : ∀ i, 0 ≤ η i) :
    0 ≤ rayleighPower m η p := by
  unfold rayleighPower
  apply Finset.sum_nonneg
  intro i hi
  exact div_nonneg (mul_nonneg (hη i) (sq_nonneg (p i))) (le_of_lt (hm i))

theorem rayleighPower_eq_zero_iff [Fintype ι] {m η : ι → ℝ} {p : ι → ℝ}
    (hm : ∀ i, 0 < m i) (hη : ∀ i, 0 < η i) :
    rayleighPower m η p = 0 ↔ ∀ i, p i = 0 := by
  constructor
  · intro h
    have hnonneg : ∀ i ∈ Finset.univ, 0 ≤ η i * p i ^ 2 / m i := by
      intro i hi
      exact div_nonneg (mul_nonneg (le_of_lt (hη i)) (sq_nonneg (p i)))
        (le_of_lt (hm i))
    have hz := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp h
    intro i
    have hi := hz i (Finset.mem_univ i)
    have hprod : η i * p i ^ 2 = 0 := (div_eq_zero_iff).mp hi |>.resolve_right (ne_of_gt (hm i))
    have hsq : p i ^ 2 = 0 := (mul_eq_zero.mp hprod).resolve_left (ne_of_gt (hη i))
    exact (sq_eq_zero_iff).mp hsq
  · intro h
    simp [rayleighPower, h]

/-- With positive masses and damping coefficients, energy strictly decreases unless
all momenta vanish; in particular the derivative is always nonpositive. -/
theorem deriv_hamiltonian_rayleigh_nonpos [Fintype ι] [DecidableEq ι]
    {m η : ι → ℝ} {V : (ι → ℝ) → ℝ}
    {q p : ℝ → ι → ℝ} {s : ℝ}
    (hm : ∀ i, 0 < m i) (hη : ∀ i, 0 ≤ η i)
    (hq : ∀ i, DifferentiableAt ℝ (fun t => q t i) s)
    (hp : ∀ i, DifferentiableAt ℝ (fun t => p t i) s)
    (hV : DifferentiableAt ℝ V (q s))
    (hq' : ∀ i, deriv (fun t => q t i) s = p s i / m i)
    (hp' : ∀ i, deriv (fun t => p t i) s =
      -configurationGradient V (q s) i - η i * p s i) :
    deriv (fun t => hamiltonian m V (q t) (p t)) s ≤ 0 := by
  rw [deriv_hamiltonian_rayleigh (fun i => ne_of_gt (hm i)) hq hp hV hq' hp']
  exact neg_nonpos.mpr (rayleighPower_nonneg hm hη)

/-- The zero-loss criterion for Rayleigh damping. -/
theorem deriv_hamiltonian_rayleigh_eq_zero_iff [Fintype ι] [DecidableEq ι]
    {m η : ι → ℝ} {V : (ι → ℝ) → ℝ}
    {q p : ℝ → ι → ℝ} {s : ℝ}
    (hm : ∀ i, 0 < m i) (hη : ∀ i, 0 < η i)
    (hq : ∀ i, DifferentiableAt ℝ (fun t => q t i) s)
    (hp : ∀ i, DifferentiableAt ℝ (fun t => p t i) s)
    (hV : DifferentiableAt ℝ V (q s))
    (hq' : ∀ i, deriv (fun t => q t i) s = p s i / m i)
    (hp' : ∀ i, deriv (fun t => p t i) s =
      -configurationGradient V (q s) i - η i * p s i) :
    deriv (fun t => hamiltonian m V (q t) (p t)) s = 0 ↔ ∀ i, p s i = 0 := by
  rw [deriv_hamiltonian_rayleigh (fun i => ne_of_gt (hm i)) hq hp hV hq' hp']
  constructor
  · intro h
    apply (rayleighPower_eq_zero_iff hm hη).mp
    exact neg_eq_zero.mp h
  · intro h
    rw [(rayleighPower_eq_zero_iff hm hη).mpr h]
    exact neg_zero

/-- A path with nonzero momentum in a genuinely damped coordinate cannot satisfy
both the conservative and the Rayleigh-damped momentum equations. -/
theorem conservative_cannot_produce_rayleigh_at_nonzero_momentum
    [Fintype ι] [DecidableEq ι]
    {η : ι → ℝ} {V : (ι → ℝ) → ℝ}
    {q p : ℝ → ι → ℝ} {s : ℝ}
    (hp_conservative : ∀ i, deriv (fun t => p t i) s =
      -configurationGradient V (q s) i)
    (hp_rayleigh : ∀ i, deriv (fun t => p t i) s =
      -configurationGradient V (q s) i - η i * p s i)
    (i : ι) (hη : η i ≠ 0) (hpi : p s i ≠ 0) : False := by
  have heq := (hp_conservative i).symm.trans (hp_rayleigh i)
  have hz : η i * p s i = 0 := by linarith
  exact (mul_eq_zero.mp hz).elim hη hpi

/-- The standard two-by-two symplectic matrix `[[0,1],[-1,0]]`, acting on a pair. -/
def standardSymplecticMap (v : ℝ × ℝ) : ℝ × ℝ := (v.2, -v.1)

/-- One-degree-of-freedom Hamiltonian, before pairing it with the symplectic form. -/
noncomputable def hamiltonianOne (m : ℝ) (V : ℝ → ℝ) (q p : ℝ) : ℝ :=
  p ^ 2 / (2 * m) + V q

/-- Symplectic form of energy conservation in one degree of freedom.  The gradient
of `hamiltonianOne` in coordinates `(q,p)` is `(D V, p/m)`, so the hypothesis is
precisely `(q̇,ṗ) = [[0,1],[-1,0]] (D V,p/m)`. -/
theorem deriv_hamiltonianOne_symplectic
    {m : ℝ} {V : ℝ → ℝ} {q p : ℝ → ℝ} {s : ℝ}
    (hm : m ≠ 0)
    (hq : DifferentiableAt ℝ q s) (hp : DifferentiableAt ℝ p s)
    (hV : DifferentiableAt ℝ V (q s))
    (hJ : (deriv q s, deriv p s) =
      standardSymplecticMap (fderiv ℝ V (q s) 1, p s / m)) :
    deriv (fun t => hamiltonianOne m V (q t) (p t)) s = 0 := by
  have hq' : deriv q s = p s / m := by
    simpa [standardSymplecticMap] using congrArg Prod.fst hJ
  have hp' : deriv p s = -fderiv ℝ V (q s) 1 := by
    simpa [standardSymplecticMap] using congrArg Prod.snd hJ
  have hqder : HasDerivAt q (p s / m) s := by
    rw [← hq']
    exact hq.hasDerivAt
  have hLin : fderiv ℝ V (q s) (p s / m) =
      (p s / m) * fderiv ℝ V (q s) 1 := by
    calc
      fderiv ℝ V (q s) (p s / m) =
          fderiv ℝ V (q s) ((p s / m) • (1 : ℝ)) := by simp
      _ = (p s / m) • fderiv ℝ V (q s) 1 := by rw [map_smul]
      _ = (p s / m) * fderiv ℝ V (q s) 1 := rfl
  have hVder : HasDerivAt (fun t => V (q t))
      (fderiv ℝ V (q s) (p s / m)) s := by
    have hcomp := hV.hasFDerivAt.comp_hasDerivAt s hqder
    convert hcomp using 1
    ext t
    rfl
  have hterm : HasDerivAt (fun t => p t ^ 2 / (2 * m))
      (p s * deriv p s / m) s := by
    have hprod := (hp.hasDerivAt.mul hp.hasDerivAt).div_const (2 * m)
    convert hprod using 1
    · ext t
      simp only [pow_two, Pi.mul_apply]
    · field_simp [hm]
      ring
  have hzero : p s * deriv p s / m + fderiv ℝ V (q s) (p s / m) = 0 := by
    rw [hp', hLin]
    field_simp [hm]
    ring
  have hresult : HasDerivAt (fun t => hamiltonianOne m V (q t) (p t)) 0 s := by
    have hsum := hterm.add hVder
    convert hsum using 1
    · ext t
      rfl
    · exact hzero.symm
  exact hresult.deriv

/-- If a momentum forcing is generated by a potential-only Hamiltonian, it is
necessarily independent of momentum and equal to the negative configuration
gradient of that potential. -/
theorem potential_forcing_is_configuration_gradient [Fintype ι] [DecidableEq ι]
    {W : (ι → ℝ) → ℝ}
    {F : (ι → ℝ) → (ι → ℝ) → ι → ℝ}
    {q p : ℝ → ι → ℝ} {s : ℝ}
    (hforced : ∀ i, deriv (fun t => p t i) s = F (q s) (p s) i)
    (hhamiltonian : ∀ i, deriv (fun t => p t i) s = -configurationGradient W (q s) i) :
    F (q s) (p s) = fun i => -configurationGradient W (q s) i := by
  funext i
  rw [← hforced i, hhamiltonian i]

/-- Consequently nonzero Rayleigh forcing cannot be the gradient of a potential
depending on configuration alone.  This is the needed correction to the informal
claim that arbitrary state-dependent forcing is a potential gradient. -/
theorem rayleigh_forcing_not_configuration_gradient [Fintype ι] [DecidableEq ι]
    {η : ι → ℝ} {W : (ι → ℝ) → ℝ} {q : ι → ℝ}
    (h : ∀ p : ι → ℝ, ∀ i,
      -η i * p i = -configurationGradient W q i)
    (i : ι) (hη : η i ≠ 0) : False := by
  have hzero := h 0 i
  have hone := h (Pi.single i 1) i
  simp only [Pi.zero_apply, mul_zero, zero_eq_neg] at hzero
  simp only [Pi.single_eq_same, mul_one, neg_inj] at hone
  apply hη
  rw [hone]
  exact hzero

end

end ElementalPeeling.LoopWall.Hamiltonian
