import Mathlib
import DiracTime.PredictiveQuotient
import VOTKP.Observer

/-!
# Bridge III — one predictive quotient, two developments, and the peel

`VOTKP/Observer.lean` (Theorem 3.1 of *VOTKP*) and `DiracTime/PredictiveQuotient.lean` (Section 2
of *The Dirac Time of the Gigantefermion*) prove the same theorem independently: `N`, the
intersection of all `ker (R Lⁿ)`, is what a predictor may forget, and `V ⧸ N` is the smallest
state that reproduces every future reading.

`unseen_eq_unobservable` proves the two formalisations are the same subspace — the VOTKP one is
the kernel of the finite observability map, the Dirac Time one an infinite intersection, and
Cayley–Hamilton closes the gap.

The rest instantiates the quotient on the peel ladder.  The result is a negative one worth having:
the peel ratio `z` is a **complete** predictive state for every `z ≠ 0`, so the wall
`z = 3 + 2√2` changes no predictive dimension.  Whatever the loop wall is, it is not a transition
in how much memory the ladder needs.
-/

namespace Unified.Bridge.Quotient

open Module
open DiracTime.PredictiveQuotient

/-! ## 1. The two formalisations agree -/

/-- **One theorem, two proofs.**  VOTKP's `unseen` and Dirac Time's `unobservable` are the same
subspace; VOTKP's `horizon` (Cayley–Hamilton) is exactly the step that identifies them. -/
theorem unseen_eq_unobservable {K V Y : Type*} [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup Y] [Module K Y]
    (L : V →ₗ[K] V) (R : V →ₗ[K] Y) :
    VOTKP.Observer.unseen L R = DiracTime.PredictiveQuotient.unobservable L R := by
  ext v
  rw [VOTKP.Observer.mem_unseen, DiracTime.PredictiveQuotient.mem_unobservable]
  exact ⟨fun h k => VOTKP.Observer.horizon L R v h k, fun h i _ => h i⟩

/-- The same statement as an iff on states, in the form both papers use. -/
theorem same_future_iff_votkp {K V Y : Type*} [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup Y] [Module K Y]
    (L : V →ₗ[K] V) (R : V →ₗ[K] Y) (v w : V) :
    (∀ k : ℕ, R ((L ^ k) v) = R ((L ^ k) w)) ↔
      v - w ∈ DiracTime.PredictiveQuotient.unobservable L R := by
  rw [← unseen_eq_unobservable L R]
  exact VOTKP.Observer.same_future_iff L R v w

/-! ## 2. The peel ladder -/

/-- The peel ladder as a linear readout system: one multiplication by the peel ratio. -/
noncomputable def peelL (z : ℝ) : ℝ →ₗ[ℝ] ℝ := z • LinearMap.id

/-- The peel reads the state itself. -/
def peelR : ℝ →ₗ[ℝ] ℝ := LinearMap.id

@[simp] theorem peelL_apply (z x : ℝ) : peelL z x = z * x := rfl

@[simp] theorem peelR_apply (x : ℝ) : peelR x = x := rfl

/-- The peel ratio is a complete state: nothing is forgotten, for every ratio including `0`.
(The time-zero observation alone decides it, so no invertibility of `z` is needed.) -/
theorem peel_unobservable_eq_bot (z : ℝ) :
    DiracTime.PredictiveQuotient.unobservable (peelL z) peelR = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  rw [DiracTime.PredictiveQuotient.mem_unobservable] at hv
  rw [Submodule.mem_bot]
  have h0 := hv 0
  simpa using h0

/-- **The wall changes no predictive dimension in the scalar present-reading model.**  Every peel
ratio, the wall included, has a one-dimensional predictive quotient.  This is a statement about
this `(L, R)`; `Found.PredictivePeel` shows other linearisations of the same ladder do jump, so the
dimension is not intrinsic to `z`. -/
theorem peel_predictive_dim (z : ℝ) :
    finrank ℝ (ℝ ⧸ DiracTime.PredictiveQuotient.unobservable (peelL z) peelR) = 1 := by
  rw [peel_unobservable_eq_bot z]
  have h := Submodule.finrank_quotient_add_finrank (⊥ : Submodule ℝ ℝ)
  rw [finrank_bot, add_zero, Module.finrank_self] at h
  exact h

/-- The wall and the neutral ratio `1` have the same predictive quotient in this model.  So in the
scalar present-reading model the wall is not a memory transition: it is a transition in a value,
not in observability.  The qualifier matters — see `Found.PredictivePeel` for models that do
separate the wall. -/
theorem wall_is_not_a_memory_transition :
    finrank ℝ (ℝ ⧸ DiracTime.PredictiveQuotient.unobservable
        (peelL (3 + 2 * Real.sqrt 2)) peelR) =
      finrank ℝ (ℝ ⧸ DiracTime.PredictiveQuotient.unobservable (peelL 1) peelR) := by
  rw [peel_predictive_dim, peel_predictive_dim]

/-- The present peel ratio always closes on its own (`R L = z · R`), so Dirac Time's closure
criterion is met at every ratio and `N∞ = ker R = ⊥` there. -/
theorem peel_closes (z : ℝ) :
    ∃ A : ℝ →ₗ[ℝ] ℝ, peelR ∘ₗ peelL z = A ∘ₗ peelR :=
  ⟨z • LinearMap.id, by
    refine LinearMap.ext fun x => ?_
    simp [peelL, smul_eq_mul]⟩

end Unified.Bridge.Quotient
