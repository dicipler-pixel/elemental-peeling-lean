import Mathlib

/-!
# Compression variance: what a retained observable loses

Direction D2.  `compression_variance_identity` proves
`J†A²J − (J†AJ)² = (QAJ)†(QAJ)` for `Q = 1 − JJ†`, `J†J = 1`, `A† = A`, over any `RCLike` field;
`compressionVariance_isPositive` and `compressionVariance_eq_zero_iff` are its consequences, and
`real_pauliX_variance_eq_one` is the two-state falsifier: the compressed `σ₁` is zero while the
compressed square is one.

Written in the parallel formalization round (swarm `smws25izm`, direction m3),
then recompiled and reviewed here; namespace and header added, trailing `#print axioms` lines
removed because `scripts/verify.py` audits every named theorem.  See PROVENANCE.md.
-/

/-!
# Compression variance

For an isometric inclusion `J`, this file identifies the variance of a self-adjoint
operator in the retained coordinates with the Gram operator of the discarded residual.
-/

namespace ElementalPeeling.LoopWall.CompressionVariance

noncomputable section

open LinearMap

variable {𝕜 V W : Type*} [RCLike 𝕜]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [FiniteDimensional 𝕜 V]
  [NormedAddCommGroup W] [InnerProductSpace 𝕜 W] [FiniteDimensional 𝕜 W]

/-- The projection onto the coordinates discarded by an inclusion `J`. -/
def complementProjection (J : W →ₗ[𝕜] V) : V →ₗ[𝕜] V :=
  1 - J ∘ₗ J.adjoint

/-- The compressed second moment minus the square of the compressed first moment. -/
def compressionVariance (J : W →ₗ[𝕜] V) (A : V →ₗ[𝕜] V) : W →ₗ[𝕜] W :=
  J.adjoint ∘ₗ A ∘ₗ A ∘ₗ J -
    (J.adjoint ∘ₗ A ∘ₗ J) ∘ₗ (J.adjoint ∘ₗ A ∘ₗ J)

/-- The part of `A` applied to the retained coordinates that lies outside their range. -/
def discardedResidual (J : W →ₗ[𝕜] V) (A : V →ₗ[𝕜] V) : W →ₗ[𝕜] V :=
  complementProjection J ∘ₗ A ∘ₗ J

theorem complementProjection_adjoint (J : W →ₗ[𝕜] V) :
    (complementProjection J).adjoint = complementProjection J := by
  simp [complementProjection, map_sub]

theorem isometry_apply (J : W →ₗ[𝕜] V) (hJ : J.adjoint ∘ₗ J = 1) (x : W) :
    J.adjoint (J x) = x := by
  simpa using LinearMap.congr_fun hJ x

theorem complementProjection_comp_self (J : W →ₗ[𝕜] V)
    (hJ : J.adjoint ∘ₗ J = 1) :
    complementProjection J ∘ₗ complementProjection J = complementProjection J := by
  ext x
  simp only [LinearMap.comp_apply, complementProjection, LinearMap.sub_apply,
    Module.End.one_apply, map_sub, isometry_apply J hJ]
  abel

theorem discardedResidual_adjoint (J : W →ₗ[𝕜] V) (A : V →ₗ[𝕜] V)
    (hA : A.adjoint = A) :
    (discardedResidual J A).adjoint =
      J.adjoint ∘ₗ A ∘ₗ complementProjection J := by
  simp [discardedResidual, complementProjection_adjoint, hA, comp_assoc]

/-- **Compression variance identity.** -/
theorem compression_variance_identity (J : W →ₗ[𝕜] V) (A : V →ₗ[𝕜] V)
    (hJ : J.adjoint ∘ₗ J = 1) (hA : A.adjoint = A) :
    compressionVariance J A =
      (discardedResidual J A).adjoint ∘ₗ discardedResidual J A := by
  rw [discardedResidual_adjoint J A hA]
  ext x
  change J.adjoint (A (A (J x))) -
      J.adjoint (A (J (J.adjoint (A (J x))))) =
    J.adjoint (A (complementProjection J
      (complementProjection J (A (J x)))))
  have hQ : complementProjection J (complementProjection J (A (J x))) =
      complementProjection J (A (J x)) := by
    simpa only [LinearMap.comp_apply] using
      LinearMap.congr_fun (complementProjection_comp_self J hJ) (A (J x))
  rw [hQ]
  simp only [complementProjection, LinearMap.sub_apply, Module.End.one_apply,
    LinearMap.comp_apply, map_sub]

theorem compressionVariance_isPositive (J : W →ₗ[𝕜] V) (A : V →ₗ[𝕜] V)
    (hJ : J.adjoint ∘ₗ J = 1) (hA : A.adjoint = A) :
    (compressionVariance J A).IsPositive := by
  rw [compression_variance_identity J A hJ hA]
  exact LinearMap.isPositive_adjoint_comp_self _

theorem compressionVariance_eq_zero_iff (J : W →ₗ[𝕜] V) (A : V →ₗ[𝕜] V)
    (hJ : J.adjoint ∘ₗ J = 1) (hA : A.adjoint = A) :
    compressionVariance J A = 0 ↔ discardedResidual J A = 0 := by
  rw [compression_variance_identity J A hJ hA]
  constructor
  · intro h
    have hk : (discardedResidual J A).ker = ⊤ := by
      rw [← LinearMap.ker_adjoint_comp_self (discardedResidual J A), h]
      exact LinearMap.ker_zero
    exact LinearMap.ker_eq_top.mp hk
  · intro h
    rw [h]
    simp

/-! ## The real two-dimensional falsifier -/

/-- Real two-dimensional Euclidean space. -/
abbrev RealTwo := EuclideanSpace ℝ (Fin 2)

/-- The two standard unit vectors. -/
def basisVector (i : Fin 2) : RealTwo := EuclideanSpace.single i 1

/-- Inclusion of the first retained coordinate, `x ↦ x • e₀`. -/
def firstInclusion : ℝ →ₗ[ℝ] RealTwo :=
  LinearMap.toSpanSingleton ℝ RealTwo (basisVector 0)

/-- The Pauli `σ₁` operator in the basis `(e₀,e₁)`. -/
def pauliX : RealTwo →ₗ[ℝ] RealTwo :=
  LinearMap.toSpanSingleton ℝ RealTwo (basisVector 0) ∘ₗ (innerₛₗ ℝ) (basisVector 1) +
    LinearMap.toSpanSingleton ℝ RealTwo (basisVector 1) ∘ₗ (innerₛₗ ℝ) (basisVector 0)

theorem firstInclusion_adjoint_comp_self :
    firstInclusion.adjoint ∘ₗ firstInclusion = 1 := by
  ext
  simp [firstInclusion, basisVector, LinearMap.adjoint_toSpanSingleton,
    EuclideanSpace.inner_single_left]

theorem pauliX_adjoint : pauliX.adjoint = pauliX := by
  simp [pauliX, LinearMap.adjoint_comp, LinearMap.adjoint_toSpanSingleton,
    LinearMap.adjoint_innerₛₗ_apply, add_comm]

theorem pauliX_firstInclusion (x : ℝ) :
    pauliX (firstInclusion x) = x • basisVector 1 := by
  simp [pauliX, firstInclusion, basisVector, EuclideanSpace.inner_single_left]

theorem pauliX_secondBasis (x : ℝ) :
    pauliX (x • basisVector 1) = x • basisVector 0 := by
  simp [pauliX, basisVector, EuclideanSpace.inner_single_left]

theorem pauliX_sq_firstInclusion (x : ℝ) :
    pauliX (pauliX (firstInclusion x)) = firstInclusion x := by
  rw [pauliX_firstInclusion, pauliX_secondBasis]
  rfl

theorem pauliX_firstMoment (x : ℝ) :
    firstInclusion.adjoint (pauliX (firstInclusion x)) = 0 := by
  rw [pauliX_firstInclusion]
  simp [firstInclusion, basisVector, LinearMap.adjoint_toSpanSingleton,
    EuclideanSpace.inner_single_left]

theorem pauliX_secondMoment (x : ℝ) :
    firstInclusion.adjoint (pauliX (pauliX (firstInclusion x))) = x := by
  rw [pauliX_sq_firstInclusion]
  have h := LinearMap.congr_fun firstInclusion_adjoint_comp_self x
  simpa only [LinearMap.comp_apply, Module.End.one_apply] using h

/-- In the `σ₁`, first-coordinate example, compression variance is exactly `1`. -/
theorem real_pauliX_variance_eq_one :
    compressionVariance firstInclusion pauliX = 1 := by
  ext
  simp only [compressionVariance, LinearMap.sub_apply, LinearMap.comp_apply,
    Module.End.one_apply]
  rw [pauliX_secondMoment, pauliX_firstMoment]
  simp

theorem real_pauliX_variance_ne_zero :
    compressionVariance firstInclusion pauliX ≠ 0 := by
  rw [real_pauliX_variance_eq_one]
  exact one_ne_zero

end
end ElementalPeeling.LoopWall.CompressionVariance
