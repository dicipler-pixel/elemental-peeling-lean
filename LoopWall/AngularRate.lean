import Mathlib

/-!
# The angular rate in a declared chart, and a moving path with zero numerator

Direction D7.  `hasDerivAt_angle`/`deriv_angle` give `dθ = (x ẏ − y ẋ)/(x² + y²)` for the
chart `arctan (y/x)` with `x ≠ 0`; no global continuous angle exists on the punctured plane and the
file says so.  `progressing_path_with_zero_angular_numerator_and_no_origin` is the paper's §9
remark with the parabola `(s, s²+1)`; `affinePath_isStuck_iff` separates "numerator zero" from
"stuck".

Written in the second parallel formalization round (swarm `smws2pzvk`, direction m7),
then recompiled and reviewed here; namespace and header added, `lemma` renamed to `theorem` so the
repository audit sees it, trailing `#print axioms` lines removed because `scripts/verify.py` audits
every named theorem.  See PROVENANCE.md.
-/

namespace ElementalPeeling.LoopWall.AngularRate

/-- The usual polar-angle chart on the right half-plane. -/
noncomputable def angle (x y : ℝ) : ℝ := Real.arctan (y / x)

/-- The numerator of angular velocity for a position `p` and velocity `v`. -/
def angularNumerator (p v : ℝ × ℝ) : ℝ := p.1 * v.2 - p.2 * v.1

/-- Affine paths, with position `(A,C)` and velocity `(B,D)`. -/
def affinePath (A B C D : ℝ) (s : ℝ) : ℝ × ℝ := (A + B * s, C + D * s)

/-- A globally nonvanishing parabolic path used for the moving-path example. -/
def parabolaPath (s : ℝ) : ℝ × ℝ := (s, s ^ 2 + 1)

/-- A path is stuck when all its positions are equal. -/
def IsStuck (p : ℝ → ℝ × ℝ) : Prop := ∀ s t, p s = p t

/-- Derivative of the declared angle chart along a differentiable path. -/
theorem hasDerivAt_angle {x y : ℝ → ℝ} {s x' y' : ℝ}
    (hx : HasDerivAt x x' s) (hy : HasDerivAt y y' s) (hxs : x s ≠ 0) :
    HasDerivAt (fun t => angle (x t) (y t))
      ((x s * y' - y s * x') / ((x s) ^ 2 + (y s) ^ 2)) s := by
  have hq : HasDerivAt (fun t => y t / x t)
      ((y' * x s - y s * x') / (x s) ^ 2) s := hy.div hx hxs
  have h := hq.arctan
  have hden : (x s) ^ 2 + (y s) ^ 2 ≠ 0 := by
    have hx2 : 0 < (x s) ^ 2 := sq_pos_of_ne_zero hxs
    have hy2 : 0 ≤ (y s) ^ 2 := sq_nonneg (y s)
    linarith
  unfold angle
  convert h using 1
  field_simp

/-- The angular derivative formula, expressed with `deriv`. -/
theorem deriv_angle {x y : ℝ → ℝ} (hx : Differentiable ℝ x)
    (hy : Differentiable ℝ y) {s : ℝ} (hxs : x s ≠ 0) :
    deriv (fun t => angle (x t) (y t)) s =
      (x s * deriv y s - y s * deriv x s) / ((x s) ^ 2 + (y s) ^ 2) := by
  exact (hasDerivAt_angle (hx s).hasDerivAt (hy s).hasDerivAt hxs).deriv

/-- The angular derivative formula on paths staying in the right half-plane. -/
theorem hasDerivAt_angle_of_pos {x y : ℝ → ℝ} {s x' y' : ℝ}
    (hx : HasDerivAt x x' s) (hy : HasDerivAt y y' s) (hxs : 0 < x s) :
    HasDerivAt (fun t => angle (x t) (y t))
      ((x s * y' - y s * x') / ((x s) ^ 2 + (y s) ^ 2)) s :=
  hasDerivAt_angle hx hy hxs.ne'

/-- An affine path has its declared constant velocity. -/
theorem hasDerivAt_affinePath (A B C D s : ℝ) :
    HasDerivAt (affinePath A B C D) (B, D) s := by
  have hlin (a b : ℝ) : HasDerivAt (fun t : ℝ => a + b * t) b s := by
    simpa using (HasDerivAt.const_mul b (hasDerivAt_id s)).const_add a
  exact (hlin A B).prodMk (hlin C D)

/-- Along an affine path the angular numerator is the constant determinant. -/
theorem affinePath_angularNumerator (A B C D s : ℝ) :
    angularNumerator (affinePath A B C D s) (B, D) = A * D - B * C := by
  simp only [angularNumerator, affinePath]
  ring

/-- The velocity of the parabolic path. -/
theorem hasDerivAt_parabolaPath (s : ℝ) :
    HasDerivAt parabolaPath (1, 2 * s) s := by
  have hx : HasDerivAt (id : ℝ → ℝ) 1 s := hasDerivAt_id s
  have hy : HasDerivAt (fun t : ℝ => t ^ 2 + 1) (2 * s) s := by
    convert ((hasDerivAt_id s).pow 2).add_const 1 using 1 <;> simp [id_eq]
  exact hx.prodMk hy

/-- Its angular numerator is `s² - 1`, so it vanishes at `s = 1`. -/
theorem parabolaPath_angularNumerator (s : ℝ) :
    angularNumerator (parabolaPath s) (1, 2 * s) = s ^ 2 - 1 := by
  simp only [angularNumerator, parabolaPath]
  ring

/--
A moving path whose angular numerator vanishes at `s = 1`.  Unlike a radial
straight line, this example stays away from the origin at every parameter.
-/
theorem progressing_path_with_zero_angular_numerator_and_no_origin :
    HasDerivAt parabolaPath (1, 2) 1 ∧
      angularNumerator (parabolaPath 1) (1, 2) = 0 ∧
      (1, 2) ≠ (0, 0) ∧
      ∀ s : ℝ, 0 < (parabolaPath s).1 ^ 2 + (parabolaPath s).2 ^ 2 := by
  refine ⟨?_, ?_, by norm_num [Prod.ext_iff], ?_⟩
  · simpa using hasDerivAt_parabolaPath 1
  · simpa using parabolaPath_angularNumerator 1
  · intro s
    have hy : 0 < s ^ 2 + 1 := by nlinarith [sq_nonneg s]
    have hy2 : 0 < (s ^ 2 + 1) ^ 2 := sq_pos_of_pos hy
    simp only [parabolaPath]
    nlinarith [sq_nonneg s]

/-- The requested determinant-zero example with nonzero radial dot product. -/
theorem affine_determinant_zero_but_radial_dot_nonzero :
    ∃ A B C D : ℝ, A * D - B * C = 0 ∧ A * B + C * D ≠ 0 := by
  refine ⟨1, 1, 0, 0, ?_, ?_⟩ <;> norm_num

/-- In that example the path has nonzero velocity and zero angular numerator. -/
theorem progressing_path_with_zero_angular_numerator :
    HasDerivAt (affinePath 1 1 0 0) (1, 0) 0 ∧
      angularNumerator (affinePath 1 1 0 0 0) (1, 0) = 0 ∧
      (1 : ℝ) * 1 + 0 * 0 ≠ 0 ∧ (1, 0) ≠ (0, 0) := by
  refine ⟨hasDerivAt_affinePath 1 1 0 0 0, ?_, by norm_num, by norm_num [Prod.ext_iff]⟩
  rw [affinePath_angularNumerator]
  norm_num

/-- An affine path is stuck exactly when both velocity coordinates vanish. -/
theorem affinePath_isStuck_iff (A B C D : ℝ) :
    IsStuck (affinePath A B C D) ↔ B = 0 ∧ D = 0 := by
  constructor
  · intro h
    have h01 := h 0 1
    have hx := congrArg Prod.fst h01
    have hy := congrArg Prod.snd h01
    simp only [affinePath, mul_zero, add_zero, mul_one] at hx hy
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨rfl, rfl⟩ s t
    simp [affinePath]
