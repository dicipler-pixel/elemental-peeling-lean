/-
# Only the equal-face threshold makes the two forms agree

Ported unchanged (namespace and header only) from `lean/BoundaryAgreement.lean` of the v1.1 package.
-/

/- The rational, strictly interior domain models squared reflection
   coordinates x,y. Two independently declared mixed continuations of
   the same diagonal threshold t are compared. -/
namespace ElementalPeeling.LoopWall.BoundaryAgreement

def additive (t x y : Rat) := x + y - 2*t

/-- Product-of-odds comparison with the common diagonal threshold t.
    The positive denominators have been cleared on (0,1)^3. -/
def product (t x y : Rat) := x*y*(1-t)*(1-t) - t*t*(1-x)*(1-y)

def ThreeClasses (a b : Rat) : Prop :=
  ((a < 0) ↔ (b < 0)) ∧ ((a = 0) ↔ (b = 0)) ∧ ((0 < a) ↔ (0 < b))

def Agree (t : Rat) : Prop :=
  ∀ x y : Rat, 0 < x → x < 1 → 0 < y → y < 1 →
      ThreeClasses (additive t x y) (product t x y)

theorem witnessInterior (t : Rat) (h0 : 0 < t) (h1 : t < 1) :
    0 < t*t ∧ t*t < 1 ∧ 0 < 2*t-t*t ∧ 2*t-t*t < 1 := by
  have hdiff : 0 < 1-t := by grind
  have hq := Rat.mul_pos h0 h0
  have hr := Rat.mul_pos hdiff hdiff
  have hs := Rat.mul_pos h0 hdiff
  grind

theorem witnessTie (t : Rat) : additive t (t*t) (2*t-t*t) = 0 := by
  unfold additive
  grind

theorem witnessProduct (t : Rat) :
    product t (t*t) (2*t-t*t) = ((t*t)*((1-t)*(1-t)))*(2*t-1) := by
  unfold product
  grind

theorem halfScaling (x y : Rat) :
    4 * product (1/2) x y = additive (1/2) x y := by
  unfold additive product
  grind

theorem uniqueInteriorBoundary (t : Rat) (h0 : 0 < t) (h1 : t < 1) :
    Agree t ↔ t=1/2 := by
  constructor
  · intro hall
    obtain ⟨hx0,hx1,hy0,hy1⟩ := witnessInterior t h0 h1
    have hclass := hall (t*t) (2*t-t*t) hx0 hx1 hy0 hy1
    have hzero := hclass.2.1.mp (witnessTie t)
    rw [witnessProduct] at hzero
    have ht := Rat.mul_pos h0 h0
    have hdiff : 0 < 1-t := by grind
    have hpos := Rat.mul_pos ht (Rat.mul_pos hdiff hdiff)
    have hne : (t*t)*((1-t)*(1-t)) ≠ 0 := by grind
    have hz : 2*t-1=0 := by
      rcases (Rat.mul_eq_zero.mp hzero) with hh | hh
      · exact False.elim (hne hh)
      · exact hh
    grind
  · rintro rfl x y _ _ _ _
    have h := halfScaling x y
    unfold ThreeClasses
    grind

/-- Midpoint between the competing y-boundaries at x=t². -/
def midY (t : Rat) := ((2*t-t*t) + (1+t)/2)/2

theorem midInterior (t : Rat) (h0 : 0 < t) (h1 : t < 1) :
    0 < midY t ∧ midY t < 1 := by
  obtain ⟨_, _, hy0, hy1⟩ := witnessInterior t h0 h1
  unfold midY
  grind

theorem midMargins (t : Rat) :
    4 * additive t (t*t) (midY t) = (1-t)*(1-2*t) ∧
    product t (t*t) (midY t) =
      -(2*t*t*(1-t))*additive t (t*t) (midY t) := by
  unfold midY additive product
  constructor <;> grind

/-- For any competing threshold away from half, strictly interior inputs
    give opposite strict calls. The result survives small errors by
    ordinary continuity of the polynomials. -/
theorem strictCounterexample (t : Rat) (h0 : 0 < t) (h1 : t < 1)
    (hn : t ≠ 1/2) :
    ∃ x y : Rat, 0 < x ∧ x < 1 ∧ 0 < y ∧ y < 1 ∧
      ((additive t x y < 0 ∧ 0 < product t x y) ∨
       (0 < additive t x y ∧ product t x y < 0)) := by
  obtain ⟨hx0,hx1,_,_⟩ := witnessInterior t h0 h1
  obtain ⟨hy0,hy1⟩ := midInterior t h0 h1
  obtain ⟨ha,hp⟩ := midMargins t
  have hd : 0 < 1-t := by grind
  have hpcoef : 0 < 2*t*t*(1-t) := by
    have h := Rat.mul_pos (Rat.mul_pos (by grind : (0:Rat)<2) hx0) hd
    grind
  refine ⟨t*t, midY t, hx0, hx1, hy0, hy1, ?_⟩
  by_cases hlt : t < 1/2
  · have h := Rat.mul_pos hd (by grind : 0 < 1-2*t)
    have haPos : 0 < additive t (t*t) (midY t) := by grind
    have hh := Rat.mul_pos hpcoef haPos
    exact Or.inr ⟨haPos, by grind⟩
  · have h := Rat.mul_pos hd (by grind : 0 < 2*t-1)
    have haNeg : additive t (t*t) (midY t) < 0 := by grind
    have hh := Rat.mul_pos hpcoef (by grind : 0 < -additive t (t*t) (midY t))
    exact Or.inl ⟨haNeg, by grind⟩

/-- Lowering the diagonal threshold increases the cleared product sign
    margin on the interior square. -/
theorem productAntitone (t u x y : Rat) (ht : 0 ≤ t) (htu : t ≤ u) (hu : u ≤ 1)
    (hx : 0 ≤ x) (hx' : x ≤ 1) (hy : 0 ≤ y) (hy' : y ≤ 1) :
    product u x y ≤ product t x y := by
  have h1 := Rat.mul_nonneg (Rat.mul_nonneg hx hy)
    (Rat.mul_nonneg (by grind : 0 ≤ u-t) (by grind : 0 ≤ 2-t-u))
  have h2 := Rat.mul_nonneg
    (Rat.mul_nonneg (by grind : 0 ≤ 1-x) (by grind : 0 ≤ 1-y))
    (Rat.mul_nonneg (by grind : 0 ≤ u-t) (by grind : 0 ≤ u+t))
  unfold product
  grind

def power (z : Rat) := ((z-1)/(z+1))*((z-1)/(z+1))

/-- Programmable forward ratios 3 and 13.99. The calibrated range
    contains six rival midpoint choices and their quoted uncertainty boxes. -/
theorem rationalThreeWayControl (t : Rat) (ht : 50051/100000 ≤ t)
    (ht' : t ≤ 50054/100000) :
    0 < additive (1/2) (power 3) (power (1399/100)) ∧
    additive t (power 3) (power (1399/100)) < 0 ∧
    0 < product t (power 3) (power (1399/100)) := by
  have h := productAntitone t (50054/100000) (power 3) (power (1399/100))
    (by grind) ht' (by grind) (by unfold power; grind) (by unfold power; grind)
    (by unfold power; grind) (by unfold power; grind)
  have hp : 0 < product (50054/100000) (power 3) (power (1399/100)) := by
    unfold product power
    grind
  refine ⟨?_, ?_, by grind⟩ <;> unfold additive power <;> grind

theorem wrongThird : ¬ Agree (1/3) := by
  intro h
  have hb := (uniqueInteriorBoundary (1/3) (by grind) (by grind)).mp h
  exact (by grind : ¬ ((1:Rat)/3 = 1/2)) hb

end ElementalPeeling.LoopWall.BoundaryAgreement
