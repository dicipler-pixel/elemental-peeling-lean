import Mathlib

/-!
# The common algebraic interface of mirror oddness and chiral odd moments

The core is torsion-freeness, not a knot-theoretic analogy. The file is independent of the
three repositories so that it compiles with the system `LEAN_PATH`. The repository statements
instantiated below are:

* `LoopWall/Ledger.lean:30-35,165-177`: `gam`, reversal oddness, and evenness of `gam^2`;
* `DiracTime/ChiralPairing.lean:69-89`: zero odd traces;
* `lean/ThetaCensus.lean:1-21`: the explicit limitation that theta and amphichirality are not
  formalised there.

No assertion below assumes the computational knot census or the authors' mirror theorem.
-/

namespace ChiralityInterface

/-- THEOREM (algebraic core). In an additively torsion-free group, a self-negating element is
zero. Characteristic zero of the scalar field is what supplies this in the chiral trace theorem. -/
theorem eq_zero_of_eq_neg {A : Type*} [AddCommGroup A] [NoZeroSMulDivisors ℕ A]
    {a : A} (h : a = -a) : a = 0 := by
  have h2 : (2 : ℕ) • a = 0 := by
    rw [two_smul]
    exact add_eq_zero_iff_eq_neg.mpr h
  exact (smul_eq_zero.mp h2).resolve_left (by norm_num)

/-- THEOREM (rational-module form). This version applies directly to rational Laurent
polynomials, without requiring a separate natural-number torsion-free instance. -/
theorem eq_zero_of_eq_neg_rational {A : Type*} [AddCommGroup A] [Module ℚ A]
    {a : A} (h : a = -a) : a = 0 := by
  have h2 : (2 : ℚ) • a = 0 := by
    rw [two_smul]
    exact add_eq_zero_iff_eq_neg.mpr h
  exact (smul_eq_zero.mp h2).resolve_left (by norm_num)

/-- THEOREM (exact value-type instance for theta). If an invariant valued in two-variable rational
Laurent polynomials is odd under `m`, it vanishes at each `m`-fixed point. This constructs neither
a knot type nor the invariant theta; it formalises precisely the algebraic step once those are
supplied. -/
theorem laurent_odd_vanishes_on_fixed {X : Type*} (m : X → X)
    (theta : X → LaurentPolynomial (LaurentPolynomial ℚ))
    (hodd : ∀ x, theta (m x) = -theta x) {x : X} (hx : m x = x) : theta x = 0 := by
  apply eq_zero_of_eq_neg_rational
  calc
    theta x = theta (m x) := congrArg theta hx.symm
    _ = -theta x := hodd x

/-- THEOREM. An odd invariant vanishes at every fixed point of the symmetry. In fact the
proof needs only the fixed-point equation, not that `m` be globally involutive. -/
theorem odd_vanishes_on_fixed {X A : Type*} [AddCommGroup A] [NoZeroSMulDivisors ℕ A]
    (m : X → X) (f : X → A) (hodd : ∀ x, f (m x) = -f x)
    {x : X} (hx : m x = x) : f x = 0 := by
  apply eq_zero_of_eq_neg
  calc
    f x = f (m x) := congrArg f hx.symm
    _ = -f x := hodd x

/-- THEOREM. Oddness makes the zero predicate symmetry-invariant. It therefore cannot separate
`x` from `m x`; proving that zeros occur only at fixed points is additional input. -/
theorem zero_mirror_iff_of_odd {X A : Type*} [AddGroup A]
    (m : X → X) (f : X → A) (hodd : ∀ x, f (m x) = -f x) (x : X) :
    f (m x) = 0 ↔ f x = 0 := by
  rw [hodd, neg_eq_zero]

/-- THEOREM. A readout factoring through an even quotient has identical values at `x` and `m x`. -/
theorem even_factor_blind {X B A : Type*} (m : X → X) (q : X → B) (r : B → A)
    (hq : ∀ x, q (m x) = q x) (x : X) : r (q (m x)) = r (q x) := by
  rw [hq]

/-- The even part of an invariant, averaging over the two symmetry images. -/
def evenPart {X A : Type*} [AddCommGroup A] [Module ℚ A]
    (m : X → X) (f : X → A) (x : X) : A := (2 : ℚ)⁻¹ • (f x + f (m x))

/-- THEOREM. For an involution, the even part is even. -/
theorem evenPart_even {X A : Type*} [AddCommGroup A] [Module ℚ A]
    (m : X → X) (hm : Function.Involutive m) (f : X → A) (x : X) :
    evenPart m f (m x) = evenPart m f x := by
  simp [evenPart, hm x, add_comm]

/-- THEOREM. The even part of an odd invariant is identically zero. Consequently no readout
factoring through that even part retains any information carried only by the odd invariant. -/
theorem evenPart_of_odd {X A : Type*} [AddCommGroup A] [Module ℚ A]
    (m : X → X) (f : X → A) (hodd : ∀ x, f (m x) = -f x) (x : X) :
    evenPart m f x = 0 := by
  simp [evenPart, hodd]

/-! ## The positive peel-ratio instance -/

/-- Positive real peel ratios; using a subtype makes reciprocal reversal a total involution. -/
abbrev PosReal := {z : ℝ // 0 < z}

/-- Reciprocal reversal of a positive peel ratio. -/
noncomputable def mirror : PosReal → PosReal := fun z => ⟨1 / z.1, one_div_pos.mpr z.2⟩

/-- The literal formula of `LoopWall/Ledger.lean:31`, transported to positive ratios. -/
noncomputable def reflection (z : PosReal) : ℝ := (z.1 - 1) / (z.1 + 1)

/-- THEOREM. Reciprocal reversal is an involution on positive ratios. -/
theorem mirror_involutive : Function.Involutive mirror := by
  intro z
  apply Subtype.ext
  simp [mirror]

/-- THEOREM. This is `LoopWall/Ledger.lean:166-171` in subtype form. -/
theorem reflection_mirror (z : PosReal) : reflection (mirror z) = -reflection z := by
  have hz : 0 < z.1 := z.2
  have hz0 : z.1 ≠ 0 := ne_of_gt hz
  have hz1 : z.1 + 1 ≠ 0 := by nlinarith
  have hz1' : 1 + z.1 ≠ 0 := by nlinarith
  have hi1 : 1 / z.1 + 1 ≠ 0 := by positivity
  unfold reflection mirror
  dsimp
  field_simp [hz0, hz1, hz1', hi1]
  ring

/-- THEOREM. Squared reflection is blind to reciprocal reversal; compare
`LoopWall/Ledger.lean:174-177`. -/
theorem reflection_sq_mirror (z : PosReal) :
    (reflection (mirror z)) ^ 2 = (reflection z) ^ 2 := by
  rw [reflection_mirror]
  ring

/-- THEOREM. Every readout factoring through squared reflection is reciprocal-blind. -/
theorem peel_readout_mirror_blind {A : Type*} (r : ℝ → A) (z : PosReal) :
    r ((reflection (mirror z)) ^ 2) = r ((reflection z) ^ 2) := by
  rw [reflection_sq_mirror]

/-- THEOREM. A reciprocal-symmetric positive ratio has zero signed reflection. -/
theorem reflection_eq_zero_of_mirror_fixed {z : PosReal} (hz : mirror z = z) :
    reflection z = 0 :=
  odd_vanishes_on_fixed mirror reflection reflection_mirror hz

/-- THEOREM. Such a symmetric ratio is never on the wall `reflection² = 1/2`. -/
theorem mirror_fixed_not_wall {z : PosReal} (hz : mirror z = z) :
    (reflection z) ^ 2 ≠ 1 / 2 := by
  rw [reflection_eq_zero_of_mirror_fixed hz]
  norm_num

/-- THEOREM. Wall membership cannot distinguish a ratio from its reciprocal reversal. -/
theorem wall_mirror_blind {z : PosReal} (hwall : (reflection z) ^ 2 = 1 / 2) :
    (reflection (mirror z)) ^ 2 = 1 / 2 := by
  rw [reflection_sq_mirror, hwall]

/-! ## Why oddness does not prove the converse -/

/-- An explicit odd invariant with a zero away from the fixed locus of negation. -/
def oddCubic (x : ℚ) : ℚ := x ^ 3 - x

/-- REFUTED (the proposed logical shortcut, not Conjecture 21). There are an involution `m`, an
`m`-odd invariant `f`, and a non-fixed `x` with `f x = 0`. Thus oddness plus `f x = 0` does not
imply `m x = x`. Instantiating `f` by theta would require knot-specific input; this example shows
that the general symmetry argument supplies none. -/
theorem odd_zero_need_not_be_fixed :
    ∃ (m : ℚ → ℚ) (f : ℚ → ℚ) (x : ℚ),
      Function.Involutive m ∧
      (∀ y, f (m y) = -f y) ∧
      f x = 0 ∧ m x ≠ x := by
  refine ⟨(fun x : ℚ => -x), oddCubic, 1, ?_, ?_, ?_, ?_⟩
  · intro x
    simp
  · intro x
    simp only [oddCubic]
    ring
  · norm_num [oddCubic]
  · norm_num

end ChiralityInterface
