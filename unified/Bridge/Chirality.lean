import Mathlib
import LoopWall.Ledger
import LoopWall.Wall

/-!
# Bridge II — one involution lemma for three developments

`DiracTime.ChiralPairing` proves that `S T S⁻¹ = −T` pairs the spectrum under `μ ↦ −μ` and kills
every odd spectral moment.  The VOTKP knot work rests on `θ (mirror K) = −θ K`, so an amphichiral
knot has `θ = 0`.  The loop wall has `Γ (1/z) = −Γ z`, i.e. the reflection is odd under the mirror.

These are three instances of one lemma, proved once here (`odd_involution_vanishes`).  What the
lemma does **not** give is any converse: oddness alone never forces the odd invariant to be
complete.  `odd_does_not_imply_converse` is the control that keeps the VOTKP census honest — the
78-of-78 agreement is evidence for Conjecture 21, not a consequence of the lemma.

The second half records what the peel datum can and cannot see.  Every readout that factors
through `Γ²` is mirror-blind, while the wall itself is *not* mirror-fixed: at `z = 3 + 2√2` the
reflection is nonzero.  So the wall is a chirality-bearing configuration whose sign no loop-wall
readout can report.
-/

namespace Unified.Bridge.Chirality

open ElementalPeeling.LoopWall.Ledger (gam gam_reverse)

/-! ## 1. The lemma -/

/-- **The shared involution lemma.**  If `f` changes sign under an involution `σ` and `x` is
fixed, then `f x = 0`.  Stated over a `ℚ`-module so that it applies to the Laurent-polynomial
ring in which `θ` lives as well as to the real line on which `Γ` lives. -/
theorem odd_involution_vanishes {X A : Type*} [AddCommGroup A] [Module ℚ A]
    (σ : X → X) (f : X → A) (hodd : ∀ x, f (σ x) = -f x) {x : X} (hfix : σ x = x) :
    f x = 0 := by
  have h : f x = -f x := by rw [← hodd x, hfix]
  have h2 : (2 : ℚ) • f x = 0 := by
    rw [two_smul]
    nth_rewrite 1 [h]
    exact neg_add_cancel _
  rcases smul_eq_zero.mp h2 with h3 | h3
  · exact absurd h3 (by norm_num)
  · exact h3

/-- The θ schema, as an instance.  An invariant odd under mirror vanishes on amphichiral knots.
This is the *easy* direction of the VOTKP statement; it says nothing about the converse. -/
theorem theta_vanishes_on_amphichiral {K R : Type*} [AddCommGroup R] [Module ℚ R]
    (mirror : K → K) (theta : K → R) (hodd : ∀ k, theta (mirror k) = -theta k)
    {k : K} (hfix : mirror k = k) : theta k = 0 :=
  odd_involution_vanishes mirror theta hodd hfix

/-- **The control.**  Oddness alone does not give the converse: `x ↦ x³ − x` is odd and vanishes
at `1`, which is not mirror-fixed.  So no argument from oddness can prove VOTKP Conjecture 21;
that needs the specific `θ`, and the 78/78 census is evidence, not proof. -/
theorem odd_does_not_imply_converse :
    ∃ f : ℝ → ℝ, (∀ x, f (-x) = -f x) ∧ ∃ x, f x = 0 ∧ -x ≠ x := by
  refine ⟨fun x => x ^ 3 - x, ?_, 1, by norm_num, by norm_num⟩
  intro x
  ring

/-! ## 2. What the peel datum can see -/

/-- The mirror acts on the peel ratio by inversion, and the reflection is odd under it. -/
theorem gam_mirror (z : ℝ) (hz : 0 < z) : gam (1 / z) = -gam z :=
  gam_reverse z hz

/-- **Everything read through `Γ²` is mirror-blind.**  No function of `Γ²` — the wall
indicator, the transmission `1 − Γ²`, the normalised determinant, the induced potential — can
distinguish a peel ratio from its reciprocal. -/
theorem even_readout_blind (A : ℝ → ℝ) (z : ℝ) (hz : 0 < z) :
    A ((gam (1 / z)) ^ 2) = A (gam z ^ 2) := by
  rw [gam_reverse z hz, neg_sq]

/-- The wall indicator itself is mirror-blind. -/
theorem wall_indicator_blind (z : ℝ) (hz : 0 < z) :
    ((gam (1 / z)) ^ 2 = 1 / 2 ↔ gam z ^ 2 = 1 / 2) := by
  rw [gam_reverse z hz, neg_sq]

/-- **The wall is chirality-bearing.**  The upper wall ratio is not mirror-fixed, and there the
reflection is nonzero, so the sign of `Γ` — the only odd part of the peel datum — is a genuine
label at the wall.  Compare `DiracTime.ChiralPairing`: the wall is exactly where the paired
spectrum `μ ↦ −μ` has a nonzero member. -/
theorem wall_is_chiral :
    gam (3 + 2 * Real.sqrt 2) ≠ 0 ∧ (3 + 2 * Real.sqrt 2 : ℝ) ≠ 1 := by
  have hwall := ElementalPeeling.LoopWall.Wall.wall_ratios_are_boundary
  have hs : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  constructor
  · intro h
    have hsq : gam (3 + 2 * Real.sqrt 2) * gam (3 + 2 * Real.sqrt 2) = 1 / 2 := hwall.1
    rw [h, mul_zero] at hsq
    norm_num at hsq
  · intro h
    linarith

/-- The only mirror-fixed peel ratio is `z = 1`, where `Γ = 0`.  So a mirror-symmetric ladder is
silent, and no silent ladder is at the wall. -/
theorem mirror_fixed_iff_gam_eq_zero (z : ℝ) (hz : 0 < z) :
    gam z = 0 ↔ (1 / z : ℝ) = z := by
  have hz0 : z ≠ 0 := hz.ne'
  have hz1 : z + 1 ≠ 0 := by positivity
  have hg : gam z = 0 ↔ z = 1 := by
    rw [show gam z = (z - 1) / (z + 1) from rfl, div_eq_zero_iff]
    constructor
    · rintro (h | h)
      · linarith
      · exact absurd h hz1
    · intro h
      left
      linarith
  rw [hg]
  constructor
  · intro h
    rw [h]
    norm_num
  · intro h
    have hzz : z * z = 1 := by
      field_simp at h
      linarith
    nlinarith [sq_nonneg (z - 1), hz]

end Unified.Bridge.Chirality
