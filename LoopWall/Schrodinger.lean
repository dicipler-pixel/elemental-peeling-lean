import Mathlib

/-!
# The Schrödinger split: brightness and chromatic parts of a small step

Direction C1 of the fourth round.  `schrodinger_split`: for positive channels `x`, brightness
`h = x 0 + x 1`, shares `p i = x i / h` and any displacement `v`, the exact identity
`(1/h) * Σ (v i)^2/x i = (vh/h)^2 + Σ (vp i)^2/p i` holds — the brightness/chromatic split, with no
hypotheses beyond positivity.  `roundShare_add` gives the round two-channel shares, and
`round_fisher` proves the Fisher form equals `dφ^2` away from the coordinate singularities; m1 is
right that the φ = 0 form of that identity is false (`round_fisher_at_zero_ne_one`), since the
first share vanishes there.

Written in the fourth parallel formalization round (swarm `smws625cs`, direction m1),
recompiled and reviewed here; namespace and header added, `#print axioms` lines removed.
-/

namespace ElementalPeeling.LoopWall.Schrodinger

noncomputable section

/-- The two positive-channel brightness/chromatic decomposition. -/
theorem schrodinger_split {x : Fin 2 → ℝ} (hx : ∀ i, 0 < x i) (v : Fin 2 → ℝ) :
    let h := x 0 + x 1
    let p : Fin 2 → ℝ := fun i => x i / h
    let vh := v 0 + v 1
    let vp : Fin 2 → ℝ := fun i => (v i * h - x i * vh) / h ^ 2
    (1 / h) * (∑ i, (v i) ^ 2 / x i) =
      (vh / h) ^ 2 + ∑ i, (vp i) ^ 2 / p i := by
  dsimp
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  have hx0 : x 0 ≠ 0 := ne_of_gt (hx 0)
  have hx1 : x 1 ≠ 0 := ne_of_gt (hx 1)
  have hh : x 0 + x 1 ≠ 0 := ne_of_gt (add_pos (hx 0) (hx 1))
  field_simp
  ring

/-- The first round-metric share. -/
def roundP0 (s : ℝ) : ℝ := Real.sin (s / 2) ^ 2

/-- The second round-metric share. -/
def roundP1 (s : ℝ) : ℝ := Real.cos (s / 2) ^ 2

/-- The shares as a two-channel colour. -/
def roundShare (s : ℝ) : Fin 2 → ℝ := ![roundP0 s, roundP1 s]

theorem roundShare_zero : roundShare 0 0 = 0 := by
  simp [roundShare, roundP0]

theorem roundShare_one : roundShare 0 1 = 1 := by
  simp [roundShare, roundP1]

theorem roundShare_add (s : ℝ) : roundShare s 0 + roundShare s 1 = 1 := by
  simp [roundShare, roundP0, roundP1]

theorem hasDerivAt_roundP0 (s : ℝ) :
    HasDerivAt roundP0 (Real.sin (s / 2) * Real.cos (s / 2)) s := by
  unfold roundP0
  convert (((Real.hasDerivAt_sin (s / 2)).comp s
    ((hasDerivAt_id s).div_const 2)).pow 2) using 1
  · ext u
    simp [Function.comp_def]
  · simp
    ring

theorem hasDerivAt_roundP1 (s : ℝ) :
    HasDerivAt roundP1 (-(Real.sin (s / 2) * Real.cos (s / 2))) s := by
  unfold roundP1
  convert (((Real.hasDerivAt_cos (s / 2)).comp s
    ((hasDerivAt_id s).div_const 2)).pow 2) using 1
  · ext u
    simp [Function.comp_def]
  · simp
    ring

theorem deriv_roundP0 (s : ℝ) :
    deriv roundP0 s = Real.sin (s / 2) * Real.cos (s / 2) :=
  (hasDerivAt_roundP0 s).deriv

theorem deriv_roundP1 (s : ℝ) :
    deriv roundP1 s = -(Real.sin (s / 2) * Real.cos (s / 2)) :=
  (hasDerivAt_roundP1 s).deriv

/-- The endpoint value in the proposed differentiated statement is zero, not one. -/
theorem round_fisher_at_zero_eq_zero :
    (∑ i, (deriv (fun s => roundShare s i) 0) ^ 2 / roundShare 0 i) = 0 := by
  rw [Fin.sum_univ_two]
  change (deriv roundP0 0) ^ 2 / roundP0 0 +
    (deriv roundP1 0) ^ 2 / roundP1 0 = 0
  norm_num [deriv_roundP0, deriv_roundP1, roundP0, roundP1]

/-- Refutation of the proposed round-metric formula at the endpoint `φ = 0`. -/
theorem round_fisher_at_zero_ne_one :
    (∑ i, (deriv (fun s => roundShare s i) 0) ^ 2 / roundShare 0 i) ≠ 1 := by
  rw [round_fisher_at_zero_eq_zero]
  norm_num

/-- The corrected round-metric identity, away from the singularities of the
square-root coordinates.  The hypothesis is equivalent to both shares being
nonzero for this parametrization. -/
theorem round_fisher (s : ℝ) (hs : Real.sin s ≠ 0) :
    (∑ i, (deriv (fun u => roundShare u i) s) ^ 2 / roundShare s i) = 1 := by
  rw [Fin.sum_univ_two]
  change (deriv roundP0 s) ^ 2 / roundP0 s +
    (deriv roundP1 s) ^ 2 / roundP1 s = 1
  rw [deriv_roundP0, deriv_roundP1]
  have hdouble : Real.sin s =
      2 * Real.sin (s / 2) * Real.cos (s / 2) := by
    calc
      Real.sin s = Real.sin (2 * (s / 2)) := by congr 1; ring
      _ = 2 * Real.sin (s / 2) * Real.cos (s / 2) := Real.sin_two_mul _
  have ha : Real.sin (s / 2) ≠ 0 := by
    intro ha
    apply hs
    rw [hdouble, ha]
    ring
  have hb : Real.cos (s / 2) ≠ 0 := by
    intro hb
    apply hs
    rw [hdouble, hb]
    ring
  have h0 : (Real.sin (s / 2) * Real.cos (s / 2)) ^ 2 /
      Real.sin (s / 2) ^ 2 = Real.cos (s / 2) ^ 2 := by
    field_simp
  have h1 : (-(Real.sin (s / 2) * Real.cos (s / 2))) ^ 2 /
      Real.cos (s / 2) ^ 2 = Real.sin (s / 2) ^ 2 := by
    field_simp
  rw [roundP0, roundP1, h0, h1]
  exact Real.cos_sq_add_sin_sq _

/-- Derivative-at-zero form of the corrected round-metric identity. -/
theorem round_fisher_along (s : ℝ) (hs : Real.sin s ≠ 0) :
    (∑ i, (deriv (fun u => roundShare (s + u) i) 0) ^ 2 / roundShare s i) = 1 := by
  have hshift (i : Fin 2) :
      deriv (fun u => roundShare (s + u) i) 0 =
        deriv (fun u => roundShare u i) s := by
    simpa only [add_zero] using
      (deriv_comp_const_add (fun u : ℝ => roundShare u i) s 0)
  simp_rw [hshift]
  exact round_fisher s hs

end
end ElementalPeeling.LoopWall.Schrodinger
