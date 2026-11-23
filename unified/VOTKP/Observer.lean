/-
VOTKP §3, Theorem 3.1: the finite linear predictive quotient (Jeromie Beasley).

A linear evolution `L` on a finite-dimensional space `V` is observed through `R : V → Y`.
The observability map `𝒪 v = (Rv, RLv, …, RL^{n-1}v)`, `n = dim V`, stacks the first `n`
observations, and `N = ker 𝒪` holds the differences that no future observation can see.
The five parts of Theorem 3.1 are `same_future_iff`, `unseen_invariant`, `quotient_dim`,
`summary_kernel` with `quotient_is_summary`, and `closes_iff`. The reduction of every power
`L^k`, `k ≥ n`, to lower ones is Cayley–Hamilton (`horizon`).

Futures are read along the discrete evolution `v ↦ Lv`, so "identical futures" means
`R(L^k v) = R(L^k w)` for every `k`. For the flow `e^{tL}` these are the Taylor coefficients of
`R e^{tL}(v − w)`, which is how Appendix A.1 passes between the two.
Developed with AI assistance.
-/
import Mathlib

namespace VOTKP.Observer

open Polynomial Module

variable {K V Y W : Type*} [Field K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup Y] [Module K Y] [AddCommGroup W] [Module K W]

/-- Cayley–Hamilton written as a recursion: `L ^ n = -∑_{i<n} cᵢ • L ^ i`, `n = dim V`, where
`cᵢ` are the coefficients of the characteristic polynomial of `L`. -/
lemma pow_finrank_eq (L : V →ₗ[K] V) :
    L ^ finrank K V = -∑ i ∈ Finset.range (finrank K V), L.charpoly.coeff i • L ^ i := by
  have h := LinearMap.aeval_self_charpoly L
  rw [aeval_eq_sum_range, LinearMap.charpoly_natDegree, Finset.sum_range_succ] at h
  have hc : L.charpoly.coeff (finrank K V) = 1 := by
    have := (LinearMap.charpoly_monic L).coeff_natDegree
    rwa [LinearMap.charpoly_natDegree] at this
  rw [hc, one_smul] at h
  rw [← sub_eq_zero, sub_neg_eq_add, add_comm]
  exact h

/-- **The Cayley–Hamilton horizon.** An observation that vanishes on `L^i v` for every
`i < dim V` vanishes on `L^k v` for every `k`. -/
theorem horizon (L : V →ₗ[K] V) (R : V →ₗ[K] Y) (v : V)
    (h : ∀ i < finrank K V, R ((L ^ i) v) = 0) (k : ℕ) : R ((L ^ k) v) = 0 := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    by_cases hk : k < finrank K V
    · exact h k hk
    · push_neg at hk
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
      have hsplit : (L ^ (finrank K V + j)) v
          = -∑ i ∈ Finset.range (finrank K V), L.charpoly.coeff i • (L ^ (j + i)) v := by
        rw [show finrank K V + j = j + finrank K V from add_comm _ _, pow_add,
          Module.End.mul_apply, pow_finrank_eq]
        simp only [LinearMap.neg_apply, LinearMap.sum_apply, LinearMap.smul_apply, map_neg, map_sum, map_smul, pow_add, Module.End.mul_apply]
      rw [hsplit, map_neg, map_sum, Finset.sum_eq_zero, neg_zero]
      intro i hi
      have hi' : j + i < finrank K V + j := by
        have := Finset.mem_range.mp hi
        omega
      rw [map_smul, ih (j + i) hi', smul_zero]

/-- The observability map `𝒪 v = (Rv, RLv, …, RL^{n-1}v)`. -/
noncomputable def obs (L : V →ₗ[K] V) (R : V →ₗ[K] Y) : V →ₗ[K] (Fin (finrank K V) → Y) :=
  LinearMap.pi fun i => R ∘ₗ (L ^ (i : ℕ))

/-- `N = ker 𝒪`, the differences no observation in the horizon can see. -/
noncomputable def unseen (L : V →ₗ[K] V) (R : V →ₗ[K] Y) : Submodule K V :=
  LinearMap.ker (obs L R)

lemma mem_unseen {L : V →ₗ[K] V} {R : V →ₗ[K] Y} {v : V} :
    v ∈ unseen L R ↔ ∀ i < finrank K V, R ((L ^ i) v) = 0 := by
  simp only [unseen, obs, LinearMap.mem_ker, funext_iff, LinearMap.pi_apply,
    LinearMap.comp_apply, Pi.zero_apply]
  constructor
  · intro h i hi
    exact h ⟨i, hi⟩
  · intro h i
    exact h i i.2

/-- **Theorem 3.1 (1).** Two states give identical futures exactly when their difference
lies in `N`. -/
theorem same_future_iff (L : V →ₗ[K] V) (R : V →ₗ[K] Y) (v w : V) :
    (∀ k : ℕ, R ((L ^ k) v) = R ((L ^ k) w)) ↔ v - w ∈ unseen L R := by
  rw [mem_unseen]
  constructor
  · intro h i _
    rw [map_sub, map_sub, h i, sub_self]
  · intro h k
    have := horizon L R (v - w) h k
    rwa [map_sub, map_sub, sub_eq_zero] at this

/-- **Theorem 3.1 (2).** `N` is `L`-invariant. -/
theorem unseen_invariant (L : V →ₗ[K] V) (R : V →ₗ[K] Y) {v : V} (hv : v ∈ unseen L R) :
    L v ∈ unseen L R := by
  rw [mem_unseen] at hv ⊢
  intro i _
  have := horizon L R v hv (i + 1)
  rwa [pow_succ, Module.End.mul_apply] at this

/-- **Theorem 3.1 (3).** `dim V/N = rank 𝒪`. -/
theorem quotient_dim (L : V →ₗ[K] V) (R : V →ₗ[K] Y) :
    finrank K (V ⧸ unseen L R) = finrank K (LinearMap.range (obs L R)) :=
  (obs L R).quotKerEquivRange.finrank_eq

/-- **Theorem 3.1 (4), minimality.** Every output-preserving autonomous summary
`F : V → W` (`FL = AF`, `R = QF`) forgets only directions in `N`. -/
theorem summary_kernel (L : V →ₗ[K] V) (R : V →ₗ[K] Y) (F : V →ₗ[K] W) (A : W →ₗ[K] W)
    (Q : W →ₗ[K] Y) (hFL : F ∘ₗ L = A ∘ₗ F) (hR : R = Q ∘ₗ F) :
    LinearMap.ker F ≤ unseen L R := by
  intro v hv
  rw [LinearMap.mem_ker] at hv
  rw [mem_unseen]
  intro i _
  have key : ∀ k : ℕ, F ((L ^ k) v) = (A ^ k) (F v) := by
    intro k
    induction k with
    | zero => simp
    | succ k ihk =>
      rw [pow_succ', Module.End.mul_apply, pow_succ', Module.End.mul_apply, ← ihk]
      exact LinearMap.congr_fun hFL _
  rw [hR, LinearMap.comp_apply, key, hv, map_zero, map_zero]

/-- **Theorem 3.1 (4), existence.** The quotient `V → V/N` is itself an output-preserving
autonomous summary, with kernel exactly `N`; by `summary_kernel` it is the minimal one. -/
theorem quotient_is_summary (L : V →ₗ[K] V) (R : V →ₗ[K] Y) :
    ∃ (A : (V ⧸ unseen L R) →ₗ[K] (V ⧸ unseen L R)) (Q : (V ⧸ unseen L R) →ₗ[K] Y),
      (unseen L R).mkQ ∘ₗ L = A ∘ₗ (unseen L R).mkQ ∧ R = Q ∘ₗ (unseen L R).mkQ ∧
      LinearMap.ker (unseen L R).mkQ = unseen L R := by
  refine ⟨(unseen L R).mapQ (unseen L R) L (fun v hv => unseen_invariant L R hv),
    (unseen L R).liftQ R (fun v hv => LinearMap.mem_ker.mpr ?_), ?_, ?_,
    Submodule.ker_mkQ _⟩
  · simpa using horizon L R v (mem_unseen.mp hv) 0
  · exact (Submodule.mapQ_mkQ _ _ _).symm
  · exact (Submodule.liftQ_mkQ _ _ _).symm

/-- **Theorem 3.1 (5).** The present observation closes autonomously (`RL = AR` for some `A`)
exactly when `ker R` is `L`-invariant. -/
theorem closes_iff (L : V →ₗ[K] V) (R : V →ₗ[K] Y) :
    (∃ A : Y →ₗ[K] Y, R ∘ₗ L = A ∘ₗ R) ↔ ∀ v, R v = 0 → R (L v) = 0 := by
  constructor
  · rintro ⟨A, hA⟩ v hv
    have := LinearMap.congr_fun hA v
    simp only [LinearMap.comp_apply] at this
    rw [this, hv, map_zero]
  · intro h
    set g : (V ⧸ LinearMap.ker R) →ₗ[K] Y := (LinearMap.ker R).liftQ (R ∘ₗ L)
      (fun v hv => LinearMap.mem_ker.mpr (h v (LinearMap.mem_ker.mp hv))) with hg
    obtain ⟨A, hA⟩ := LinearMap.exists_extend (g ∘ₗ R.quotKerEquivRange.symm.toLinearMap)
    refine ⟨A, ?_⟩
    ext v
    have h1 : A (R v) = g (R.quotKerEquivRange.symm ⟨R v, LinearMap.mem_range_self R v⟩) := by
      have := LinearMap.congr_fun hA ⟨R v, LinearMap.mem_range_self R v⟩
      simpa using this
    have h2 : R.quotKerEquivRange.symm ⟨R v, LinearMap.mem_range_self R v⟩
        = (LinearMap.ker R).mkQ v := by
      rw [LinearEquiv.symm_apply_eq, Submodule.mkQ_apply]
      apply Subtype.ext
      rw [LinearMap.quotKerEquivRange_apply_mk]
    rw [LinearMap.comp_apply, LinearMap.comp_apply, h1, h2, hg, Submodule.mkQ_apply,
      Submodule.liftQ_apply, LinearMap.comp_apply]

end VOTKP.Observer
