import Mathlib

/-!
# The 48 integral quaternions of norm five, and why a count decides no partition

Direction D3 of the second formalization round.  `normSq_five_card`: the integral quaternions
`a + bi + cj + dk` with `a² + b² + c² + d² = 5` number 48 (a complete count: every coordinate of
such a vector is bounded by 2, and the kernel decides the finite cube).  `normSq_qMul` gives norm
multiplicativity; the norm-one vectors are exactly 8 and form a group (`qUnitsGroup`) — the
Hamilton units, not the 24 Hurwitz units, which would need half-integer coordinates.
`exists_equalPartition` shows any finite set of size `d * k` splits into `d` blocks of size `k`,
and `cardinality_alone_cannot_distinguish_six_and_three` applies it to this 48-element set in both
the `6 × 8` and `3 × 16` readings, so no counting argument separates them.

Recompiled and reviewed here; namespace and header added, `lemma` renamed to `theorem`,
`#print axioms` lines removed (the repository audit covers every named theorem).
-/

set_option maxHeartbeats 800000

open scoped BigOperators

namespace ElementalPeeling.LoopWall.Quaternions

abbrev Quat4 := Fin 4 → ℤ

def normSq (v : Quat4) : ℤ := ∑ i, (v i) ^ 2

def cube (n : ℤ) : Finset Quat4 :=
  Fintype.piFinset (fun _ => Finset.Icc (-n) n)

def sol5 : Finset Quat4 := (cube 2).filter (fun v => normSq v = 5)
def sol1 : Finset Quat4 := (cube 1).filter (fun v => normSq v = 1)

theorem bounds_of_sq_le_five (x : ℤ) (h : x ^ 2 ≤ 5) : -2 ≤ x ∧ x ≤ 2 := by
  constructor <;> nlinarith

theorem bounds_of_sq_le_one (x : ℤ) (h : x ^ 2 ≤ 1) : -1 ≤ x ∧ x ≤ 1 := by
  constructor <;> nlinarith

theorem coord_sq_le {v : Quat4} {m : ℤ} (hv : normSq v = m) (i : Fin 4) :
    (v i) ^ 2 ≤ m := by
  rw [← hv, normSq]
  exact Finset.single_le_sum (fun j _ => sq_nonneg (v j)) (Finset.mem_univ i)

theorem mem_cube_two_of_normSq_five {v : Quat4} (hv : normSq v = 5) : v ∈ cube 2 := by
  rw [cube, Fintype.mem_piFinset]
  intro i
  exact Finset.mem_Icc.mpr (bounds_of_sq_le_five (v i) (coord_sq_le hv i))

theorem mem_cube_one_of_normSq_one {v : Quat4} (hv : normSq v = 1) : v ∈ cube 1 := by
  rw [cube, Fintype.mem_piFinset]
  intro i
  exact Finset.mem_Icc.mpr (bounds_of_sq_le_one (v i) (coord_sq_le hv i))

theorem mem_sol5 (v : Quat4) : v ∈ sol5 ↔ normSq v = 5 := by
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro hv
    exact Finset.mem_filter.mpr ⟨mem_cube_two_of_normSq_five hv, hv⟩

theorem mem_sol1 (v : Quat4) : v ∈ sol1 ↔ normSq v = 1 := by
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro hv
    exact Finset.mem_filter.mpr ⟨mem_cube_one_of_normSq_one hv, hv⟩

abbrev Sol5 := {v : Quat4 // normSq v = 5}
abbrev QUnits := {v : Quat4 // normSq v = 1}

instance : Fintype Sol5 := Fintype.ofFinset sol5 (fun v => mem_sol5 v)
instance : Fintype QUnits := Fintype.ofFinset sol1 (fun v => mem_sol1 v)

theorem sol5_card : Fintype.card Sol5 = 48 := by
  change sol5.card = 48
  decide

theorem sol1_card : Fintype.card QUnits = 8 := by
  change sol1.card = 8
  decide

theorem normSq_five_card : Nat.card Sol5 = 48 := by
  rw [Nat.card_eq_fintype_card]
  exact sol5_card

theorem normSq_one_card : Nat.card QUnits = 8 := by
  rw [Nat.card_eq_fintype_card]
  exact sol1_card

/-- The proposed norm-one count of 24 is false for integer vectors. -/
theorem normSq_one_card_ne_24 : Nat.card QUnits ≠ 24 := by
  rw [normSq_one_card]
  decide

/-- Hamilton multiplication on four integer coordinates `(1, i, j, k)`. -/
def qMul (u v : Quat4) : Quat4 :=
  ![u 0 * v 0 - u 1 * v 1 - u 2 * v 2 - u 3 * v 3,
    u 0 * v 1 + u 1 * v 0 + u 2 * v 3 - u 3 * v 2,
    u 0 * v 2 - u 1 * v 3 + u 2 * v 0 + u 3 * v 1,
    u 0 * v 3 + u 1 * v 2 - u 2 * v 1 + u 3 * v 0]

def qOne : Quat4 := ![1, 0, 0, 0]

def qConj (u : Quat4) : Quat4 := ![u 0, -u 1, -u 2, -u 3]

theorem normSq_apply (u : Quat4) :
    normSq u = u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 + u 3 ^ 2 := by
  simp [normSq, Fin.sum_univ_four]

theorem normSq_qConj (u : Quat4) : normSq (qConj u) = normSq u := by
  simp [normSq_apply, qConj]

theorem normSq_qMul (u v : Quat4) : normSq (qMul u v) = normSq u * normSq v := by
  simp [normSq_apply, qMul]
  ring

theorem normSq_qMul_of_one {u v : Quat4} (hu : normSq u = 1) (hv : normSq v = 1) :
    normSq (qMul u v) = 1 := by
  rw [normSq_qMul, hu, hv, one_mul]

theorem qOne_mul (u : Quat4) : qMul qOne u = u := by
  funext i
  fin_cases i <;> simp [qMul, qOne]

theorem qMul_one (u : Quat4) : qMul u qOne = u := by
  funext i
  fin_cases i <;> simp [qMul, qOne]

theorem qMul_assoc (u v w : Quat4) : qMul (qMul u v) w = qMul u (qMul v w) := by
  funext i
  fin_cases i <;> simp [qMul] <;> ring

theorem qConj_qMul (u : Quat4) : qMul (qConj u) u = (normSq u) • qOne := by
  funext i
  fin_cases i <;> simp [qMul, qConj, qOne, normSq_apply] <;> ring

theorem qConj_qMul_of_one {u : Quat4} (hu : normSq u = 1) : qMul (qConj u) u = qOne := by
  rw [qConj_qMul, hu, one_smul]

/-- The corrected norm-one units form a group under Hamilton multiplication. -/
instance qUnitsGroup : Group QUnits where
  one := ⟨qOne, by norm_num [normSq_apply, qOne]⟩
  mul u v := ⟨qMul u v, normSq_qMul_of_one u.property v.property⟩
  inv u := ⟨qConj u, by rw [normSq_qConj, u.property]⟩
  mul_assoc u v w := Subtype.ext (qMul_assoc u v w)
  one_mul u := Subtype.ext (qOne_mul u)
  mul_one u := Subtype.ext (qMul_one u)
  inv_mul_cancel u := Subtype.ext (qConj_qMul_of_one u.property)

/-- `block` partitions `α` into `d` fibers, all of cardinality `k`. -/
def EqualPartition (α : Type*) (d k : ℕ) (block : α → Fin d) : Prop :=
  ∀ b, Nat.card {a // block a = b} = k

/-- Every finite type of cardinality `d * k` has an equal-fiber `d`-block partition. -/
theorem exists_equalPartition (α : Type*) [Finite α] (d k : ℕ)
    (hcard : Nat.card α = d * k) :
    ∃ block : α → Fin d, EqualPartition α d k block := by
  letI : Fintype α := Fintype.ofFinite α
  have hc : Fintype.card α = Fintype.card (Fin d × Fin k) := by
    rw [Nat.card_eq_fintype_card] at hcard
    simpa using hcard
  let e : α ≃ Fin d × Fin k := Fintype.equivOfCardEq hc
  let block : α → Fin d := fun a => (e a).1
  refine ⟨block, fun b => ?_⟩
  let fiberEquiv : {a // block a = b} ≃ Fin k :=
    { toFun := fun a => (e a.1).2
      invFun := fun j => ⟨e.symm (b, j), by
        change (e (e.symm (b, j))).1 = b
        rw [e.apply_symm_apply]⟩
      left_inv := fun a => by
        apply Subtype.ext
        change e.symm (b, (e a.1).2) = a.1
        have ha : (b, (e a.1).2) = e a.1 := by
          apply Prod.ext
          · exact a.property.symm
          · rfl
        rw [ha, e.symm_apply_apply]
      right_inv := fun j => by
        change (e (e.symm (b, j))).2 = j
        rw [e.apply_symm_apply] }
  calc
    Nat.card {a // block a = b} = Nat.card (Fin k) := Nat.card_congr fiberEquiv
    _ = k := by simp

/-- The 48 norm-five vectors have a partition into six blocks of eight vectors. -/
theorem normSq_five_six_block_partition :
    ∃ block : Sol5 → Fin 6, EqualPartition Sol5 6 8 block := by
  apply exists_equalPartition
  simpa using normSq_five_card

/-- The same 48 norm-five vectors have a partition into three blocks of sixteen vectors. -/
theorem normSq_five_three_block_partition :
    ∃ block : Sol5 → Fin 3, EqualPartition Sol5 3 16 block := by
  apply exists_equalPartition
  simpa using normSq_five_card

/--
Cardinality alone cannot distinguish the two block readings: two different
block counts coexist on the very same 48-element type. This is the precise
non-uniqueness statement; it does not assert that arbitrary partitions coincide.
-/
theorem cardinality_alone_cannot_distinguish_six_and_three :
    ∃ block₆ : Sol5 → Fin 6, ∃ block₃ : Sol5 → Fin 3,
      EqualPartition Sol5 6 8 block₆ ∧
      EqualPartition Sol5 3 16 block₃ ∧ (6 : ℕ) ≠ 3 := by
  obtain ⟨block₆, h₆⟩ := normSq_five_six_block_partition
  obtain ⟨block₃, h₃⟩ := normSq_five_three_block_partition
  exact ⟨block₆, block₃, h₆, h₃, by decide⟩


end ElementalPeeling.LoopWall.Quaternions
