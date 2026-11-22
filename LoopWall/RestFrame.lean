import Mathlib

/-!
# Two lightlike momenta carry a rest frame

Direction D4 of the third round.  `twoLightlike_invariant`: for `p± = ±E±/c` the pair has
`E^2 - c^2 p^2 = 4 E+ E-`; `forwardLightlike_null`/`backwardLightlike_null`; equal energies give zero
momentum and mass `2 E0 / c^2`; `exists_lightlike_decomposition` proves every positive timelike
`(E,p)` splits into two null pieces with `E± = (E ± c p)/2`.  The vector version
`twoLightlike_invariant_vector` and `momentumVector_norm_le` (`‖p⃗‖ ≤ E/c`) are proved in an
arbitrary real normed space with `‖n‖ = 1`.

Written in the third parallel formalization round (swarm `smws58h9u`, direction m4),
then recompiled and reviewed here; namespace and header added, `lemma` renamed to `theorem`, and
the trailing `#print axioms` lines removed because `scripts/verify.py` audits every named theorem.
-/

namespace ElementalPeeling.LoopWall.RestFrame

/-- The mostly-spatial Minkowski quadratic form. -/
def minkowskiSq (c E p : ℝ) : ℝ := E ^ 2 - c ^ 2 * p ^ 2

/-- The scalar momentum of a pair of oppositely directed lightlike pieces. -/
noncomputable def scalarMomentum (c Eplus Eminus : ℝ) : ℝ := (Eplus - Eminus) / c

/-- Invariant mass associated with energy and scalar momentum. -/
noncomputable def invariantMass (c E p : ℝ) : ℝ := Real.sqrt (minkowskiSq c E p) / c ^ 2

/-- The momentum vector of two lightlike pieces directed along `n` and `-n`. -/
noncomputable def momentumVector {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (c Eplus Eminus : ℝ) (n : V) : V :=
  ((Eplus - Eminus) / c) • n

/-- Adding two oppositely directed null vectors gives invariant `4 E₊ E₋`. -/
theorem twoLightlike_invariant (c Eplus Eminus : ℝ) (hc : 0 < c) :
    (Eplus + Eminus) ^ 2 - c ^ 2 * ((Eplus - Eminus) / c) ^ 2 =
      4 * Eplus * Eminus := by
  field_simp [ne_of_gt hc]
  ring

/-- The forward lightlike component is null. -/
theorem forwardLightlike_null (c Eplus : ℝ) (hc : 0 < c) :
    Eplus ^ 2 - c ^ 2 * (Eplus / c) ^ 2 = 0 := by
  field_simp [ne_of_gt hc]
  ring

/-- The backward lightlike component is null. -/
theorem backwardLightlike_null (c Eminus : ℝ) (hc : 0 < c) :
    Eminus ^ 2 - c ^ 2 * (Eminus / c) ^ 2 = 0 := by
  field_simp [ne_of_gt hc]
  ring

/-- Equal energies in opposite directions have zero total momentum. -/
theorem restFrame_scalarMomentum (c E0 : ℝ) :
    scalarMomentum c E0 E0 = 0 := by
  simp [scalarMomentum]

/-- Equal energies `E0` give the rest mass `2 E0 / c²`. -/
theorem restFrame_invariantMass (c E0 : ℝ) (_hc : 0 < c) (hE0 : 0 < E0) :
    invariantMass c (E0 + E0) (scalarMomentum c E0 E0) = 2 * E0 / c ^ 2 := by
  have hzero : scalarMomentum c E0 E0 = 0 := restFrame_scalarMomentum c E0
  unfold invariantMass minkowskiSq
  rw [hzero]
  have hrad : (E0 + E0) ^ 2 - c ^ 2 * 0 ^ 2 = (E0 + E0) ^ 2 := by ring
  rw [hrad, Real.sqrt_sq (by positivity : 0 ≤ E0 + E0)]
  ring

/-- Every positive timelike scalar energy-momentum has a positive null
 decomposition.  The two exhibited energies are `(E ± cp)/2`. -/
theorem exists_lightlike_decomposition (c E p : ℝ) (hc : 0 < c)
    (hE : 0 < E) (htimelike : 0 < E ^ 2 - c ^ 2 * p ^ 2) :
    ∃ Eplus Eminus : ℝ, 0 < Eplus ∧ 0 < Eminus ∧
      E = Eplus + Eminus ∧ p = scalarMomentum c Eplus Eminus := by
  have hplus : 0 < E + c * p := by
    by_contra h
    have hnonpos : E + c * p ≤ 0 := le_of_not_gt h
    have hminus : 0 ≤ E - c * p := by linarith
    have hprod : (E - c * p) * (E + c * p) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hminus hnonpos
    nlinarith
  have hminus : 0 < E - c * p := by
    by_contra h
    have hnonpos : E - c * p ≤ 0 := le_of_not_gt h
    have hplus' : 0 ≤ E + c * p := by linarith
    have hprod : (E - c * p) * (E + c * p) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hnonpos hplus'
    nlinarith
  refine ⟨(E + c * p) / 2, (E - c * p) / 2, by linarith, by linarith, by ring, ?_⟩
  unfold scalarMomentum
  field_simp [ne_of_gt hc]
  ring

/-- For a unit direction, the vector momentum has the expected scalar norm. -/
theorem norm_momentumVector {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (c Eplus Eminus : ℝ) (n : V) (hn : ‖n‖ = 1) :
    ‖momentumVector c Eplus Eminus n‖ = |(Eplus - Eminus) / c| := by
  simp [momentumVector, norm_smul, hn, Real.norm_eq_abs, abs_div]

/-- The `3+1`-dimensional (indeed, arbitrary normed-space) invariant identity. -/
theorem twoLightlike_invariant_vector {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (c Eplus Eminus : ℝ) (n : V) (hc : 0 < c) (hn : ‖n‖ = 1) :
    (Eplus + Eminus) ^ 2 - c ^ 2 * ‖momentumVector c Eplus Eminus n‖ ^ 2 =
      4 * Eplus * Eminus := by
  rw [norm_momentumVector c Eplus Eminus n hn, sq_abs]
  exact twoLightlike_invariant c Eplus Eminus hc

/-- Positive lightlike energies give the subluminal total-momentum bound
 `‖p⃗‖ ≤ E/c`, with equality precisely when one of the two energies vanishes
 (the boundary of the positive-energy hypothesis). -/
theorem momentumVector_norm_le {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (c Eplus Eminus : ℝ) (n : V) (hc : 0 < c) (hplus : 0 < Eplus)
    (hminus : 0 < Eminus) (hn : ‖n‖ = 1) :
    ‖momentumVector c Eplus Eminus n‖ ≤ (Eplus + Eminus) / c := by
  rw [norm_momentumVector c Eplus Eminus n hn, abs_div, abs_of_pos hc]
  apply (div_le_div_iff_of_pos_right hc).2
  rw [abs_sub_le_iff]
  constructor <;> linarith


end ElementalPeeling.LoopWall.RestFrame
