import Mathlib

/-!
# The oscillator Lagrangian: Legendre transform, energy, and why it cannot force null motion

Direction D5 of the third round.  `legendre_hamiltonian_eq` gives `p v - L = p^2/(2m) + U` for
`p = m v`; `euler_lagrange_of_acceleration` and the `hamilton_*` lemmas give the Euler–Lagrange /
Hamilton equivalence; `energy_conservation` proves the energy is constant along solutions.  The
negative result the framework needs is `free_lagrangian_has_nonnull_linear_solution`: for every
`c` a free linear solution has `(deriv ψ s)^2 ≠ c^2`, so a Lagrangian of this shape imposes no null
condition.  `nonnull_claim_as_written_false` records that the hypothesis `v ≠ c` alone is not
enough (take `v = -c`).

Written in the third parallel formalization round (swarm `smws58h9u`, direction m2),
then recompiled and reviewed here; namespace and header added, `lemma` renamed to `theorem`, and
the trailing `#print axioms` lines removed because `scripts/verify.py` audits every named theorem.
-/

namespace ElementalPeeling.LoopWall.Oscillator

/-- The oscillator Lagrangian `L = ½ m v² - U(ψ)`. -/
noncomputable def lagrangian (m : ℝ) (U : ℝ → ℝ) (ψ v : ℝ) : ℝ :=
  (1 / 2) * m * v ^ 2 - U ψ

/-- The Legendre transform, written before eliminating `v = p/m`. -/
noncomputable def legendreHamiltonian (m : ℝ) (U : ℝ → ℝ) (ψ p v : ℝ) : ℝ :=
  p * v - lagrangian m U ψ v

/-- Canonical momentum along a path. -/
noncomputable def canonicalMomentum (m : ℝ) (ψ : ℝ → ℝ) : ℝ → ℝ :=
  fun t => m * deriv ψ t

/-- Mechanical energy along a path. -/
noncomputable def energy (m : ℝ) (U : ℝ → ℝ) (ψ : ℝ → ℝ) : ℝ → ℝ :=
  fun t => (1 / 2) * m * (deriv ψ t) ^ 2 + U (ψ t)

/-- D5(i): the Legendre transform is `p²/(2m) + U(ψ)`. -/
theorem legendre_hamiltonian_eq {m p v : ℝ} (_hm : 0 < m)
    (U : ℝ → ℝ) (ψ : ℝ) (hp : p = m * v) :
    legendreHamiltonian m U ψ p v = p ^ 2 / (2 * m) + U ψ := by
  rw [legendreHamiltonian, lagrangian, hp]
  field_simp
  ; ring

/-- D5(ii): the acceleration equation implies the Euler--Lagrange equation. -/
theorem euler_lagrange_of_acceleration {m : ℝ} (hm : 0 < m)
    {U ψ : ℝ → ℝ} {s : ℝ} (hψ₂ : DifferentiableAt ℝ (deriv ψ) s)
    (hacc : deriv (deriv ψ) s = -(deriv U (ψ s)) / m) :
    deriv (fun t => m * deriv ψ t) s = -(deriv U (ψ s)) := by
  have hd : HasDerivAt (fun t => m * deriv ψ t)
      (m * deriv (deriv ψ) s) s :=
    HasDerivAt.const_mul m hψ₂.hasDerivAt
  rw [hd.deriv, hacc]
  field_simp [ne_of_gt hm]

/-- The first Hamilton equation is exactly the definition `p = m ψ̇`. -/
theorem hamilton_position {m : ℝ} (hm : 0 < m) (ψ : ℝ → ℝ) (s : ℝ) :
    deriv ψ s = canonicalMomentum m ψ s / m := by
  unfold canonicalMomentum
  field_simp [ne_of_gt hm]

/-- D5(iii), momentum equation: the second Hamilton equation is the
Euler--Lagrange equation for `p = m ψ̇`. -/
theorem hamilton_momentum {m : ℝ} (hm : 0 < m)
    {U ψ : ℝ → ℝ} {s : ℝ} (hψ₂ : DifferentiableAt ℝ (deriv ψ) s)
    (hacc : deriv (deriv ψ) s = -(deriv U (ψ s)) / m) :
    deriv (canonicalMomentum m ψ) s = -(deriv U (ψ s)) := by
  exact euler_lagrange_of_acceleration hm hψ₂ hacc

/-- Both Hamilton equations for the oscillator, in the variables `(ψ, p)`. -/
theorem hamilton_equations {m : ℝ} (hm : 0 < m)
    {U ψ : ℝ → ℝ} {s : ℝ} (hψ₂ : DifferentiableAt ℝ (deriv ψ) s)
    (hacc : deriv (deriv ψ) s = -(deriv U (ψ s)) / m) :
    deriv ψ s = canonicalMomentum m ψ s / m ∧
      deriv (canonicalMomentum m ψ) s = -(deriv U (ψ s)) :=
  ⟨hamilton_position hm ψ s, hamilton_momentum hm hψ₂ hacc⟩

/-- Conversely, Hamilton's momentum equation recovers precisely the assumed
acceleration equation.  Thus the Hamiltonian formulation adds no further
equation of motion. -/
theorem acceleration_of_hamilton_momentum {m : ℝ} (hm : 0 < m)
    {U ψ : ℝ → ℝ} {s : ℝ} (hψ₂ : DifferentiableAt ℝ (deriv ψ) s)
    (hp : deriv (canonicalMomentum m ψ) s = -(deriv U (ψ s))) :
    deriv (deriv ψ) s = -(deriv U (ψ s)) / m := by
  have hd : deriv (canonicalMomentum m ψ) s = m * deriv (deriv ψ) s := by
    exact (HasDerivAt.const_mul m hψ₂.hasDerivAt).deriv
  rw [hd] at hp
  apply (eq_div_iff (ne_of_gt hm)).2
  linear_combination hp

/-- D5(iv): conservation of mechanical energy. -/
theorem energy_conservation {m : ℝ} (hm : 0 < m)
    {U ψ : ℝ → ℝ} (hU : Differentiable ℝ U)
    (hψ : Differentiable ℝ ψ) (hψ₂ : Differentiable ℝ (deriv ψ))
    {s : ℝ} (hacc : deriv (deriv ψ) s = -(deriv U (ψ s)) / m) :
    deriv (energy m U ψ) s = 0 := by
  have hkin : HasDerivAt (fun t => (1 / 2) * m * (deriv ψ t) ^ 2)
      ((1 / 2) * m *
        (2 * (deriv ψ s) ^ (2 - 1) * deriv (deriv ψ) s)) s :=
    HasDerivAt.const_mul ((1 / 2) * m) ((hψ₂ s).hasDerivAt.pow 2)
  have hpot : HasDerivAt (fun t => U (ψ t))
      (deriv U (ψ s) * deriv ψ s) s := by
    simpa only [Function.comp_def] using
      (HasDerivAt.comp s (hU (ψ s)).hasDerivAt (hψ s).hasDerivAt)
  have he : HasDerivAt (energy m U ψ)
      ((1 / 2) * m *
          (2 * (deriv ψ s) ^ (2 - 1) * deriv (deriv ψ) s) +
        deriv U (ψ s) * deriv ψ s) s := hkin.add hpot
  rw [he.deriv]
  norm_num [hacc]
  field_simp [ne_of_gt hm]
  ; ring

/-- Velocity of the free linear path `ψ(t) = v t`. -/
theorem deriv_linear_motion (v s : ℝ) :
    deriv (fun t : ℝ => v * t) s = v := by
  have h : HasDerivAt (fun t : ℝ => v * t) v s := by
    simpa using HasDerivAt.const_mul v (hasDerivAt_id s)
  exact h.deriv

/-- Every linear path solves the free (`U = 0`) Euler--Lagrange equation. -/
theorem free_linear_euler_lagrange (m v s : ℝ) :
    deriv (fun t => m * deriv (fun r : ℝ => v * r) t) s =
      -(deriv (fun _ : ℝ => (0 : ℝ)) (v * s)) := by
  have hvel : deriv (fun t : ℝ => v * t) = fun _ => v := by
    funext r
    exact deriv_linear_motion v r
  rw [hvel]
  simp

/-- The literal claim that `v ≠ c` makes a linear solution non-null is false.
At `v = -1`, `c = 1` the speed is lightlike although `v ≠ c`. -/
theorem nonnull_claim_as_written_false :
    ¬ (∀ (m v c : ℝ), 0 < m → v ≠ c →
      ((∀ s : ℝ,
        deriv (fun t => m * deriv (fun r : ℝ => v * r) t) s =
          -(deriv (fun _ : ℝ => (0 : ℝ)) (v * s))) ∧
       (∀ s : ℝ, (deriv (fun t : ℝ => v * t) s) ^ 2 ≠ c ^ 2))) := by
  intro h
  have hn := (h 1 (-1) 1 (by norm_num) (by norm_num)).2 0
  rw [deriv_linear_motion] at hn
  norm_num at hn

/-- D5(v), corrected literal form: the two exclusions `v ≠ c` and
`v ≠ -c` give a non-null free linear solution.  Equivalently, the single
assumption `v^2 ≠ c^2` suffices. -/
theorem free_linear_motion_not_null (m v c : ℝ)
    (hv : v ≠ c) (hvn : v ≠ -c) :
    (∀ s : ℝ,
      deriv (fun t => m * deriv (fun r : ℝ => v * r) t) s =
        -(deriv (fun _ : ℝ => (0 : ℝ)) (v * s))) ∧
      (∀ s : ℝ, (deriv (fun t : ℝ => v * t) s) ^ 2 ≠ c ^ 2) := by
  refine ⟨fun s => free_linear_euler_lagrange m v s, fun s hsq => ?_⟩
  rw [deriv_linear_motion] at hsq
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
  · exact hv h
  · exact hvn h

/-- The conceptual negative result: for every positive mass and every `c`,
the free Lagrangian has a linear Euler--Lagrange solution whose squared speed
is different from `c²`.  Hence this Lagrangian shape cannot force null motion. -/
theorem free_lagrangian_has_nonnull_linear_solution {m : ℝ} (_hm : 0 < m) (c : ℝ) :
    ∃ v : ℝ,
      (∀ s : ℝ,
        deriv (fun t => m * deriv (fun r : ℝ => v * r) t) s =
          -(deriv (fun _ : ℝ => (0 : ℝ)) (v * s))) ∧
      (∀ s : ℝ, (deriv (fun t : ℝ => v * t) s) ^ 2 ≠ c ^ 2) := by
  by_cases hc : c = 0
  · refine ⟨1, fun s => free_linear_euler_lagrange m 1 s, ?_⟩
    intro s
    rw [deriv_linear_motion, hc]
    norm_num
  · refine ⟨0, fun s => free_linear_euler_lagrange m 0 s, ?_⟩
    intro s
    rw [deriv_linear_motion]
    simpa using (Ne.symm (pow_ne_zero 2 hc))


end ElementalPeeling.LoopWall.Oscillator
