import Mathlib

/-!
# The A2 weights, roots, and the two Cartan directions

Direction D2.  The orthogonal projection `P` onto the zero-sum subspace (`P_orthogonal`,
`P_idempotent`, `P_self_adjoint`, `ker_P = ℝ ∙ oneVec`); the six weights `± P e_i` with
`w_normSq = 2/3`, `w_sum = 0`, `weightList_length = 6` and `weightList_nodup`; the six roots
`e_i − e_j` with `r_normSq = 2`, `rootList_length = 6`, `rootList_sum = 0`,
`rootList_opposite_pairs`; the only linear relation has equal coefficients
(`linear_relation_iff`, `cartan_directions_independent`); and `adjointWeights_length = 8`,
`adjointWeights_sum = 0` for the six roots plus two zeros.

Written in the second parallel formalization round (swarm `smws2pzvk`, direction m4),
then recompiled and reviewed here; namespace and header added, `lemma` renamed to `theorem` so the
repository audit sees it, trailing `#print axioms` lines removed because `scripts/verify.py` audits
every named theorem.  See PROVENANCE.md.
-/

namespace ElementalPeeling.LoopWall.A2

noncomputable section

open scoped BigOperators

abbrev V := Fin 3 → ℝ

/-- The standard Euclidean inner product on coordinate vectors. -/
def stdInner (x y : V) : ℝ := ∑ i, x i * y i

/-- The standard Euclidean squared norm. -/
def normSq (x : V) : ℝ := stdInner x x

/-- The all-ones vector. -/
def oneVec : V := fun _ => 1

/-- A standard basis vector. -/
def e (i : Fin 3) : V := fun j => if i = j then 1 else 0

/-- The sum-of-coordinates functional. -/
def coordinateSum : V →ₗ[ℝ] ℝ where
  toFun x := x 0 + x 1 + x 2
  map_add' x y := by simp; ring
  map_smul' c x := by simp; ring

/-- The sum-zero plane, the A2 weight/root plane. -/
def zeroSum : Submodule ℝ V := LinearMap.ker coordinateSum

/-- Orthogonal projection onto the sum-zero plane. -/
def P : V →ₗ[ℝ] V where
  toFun x := fun i => x i - (x 0 + x 1 + x 2) / 3
  map_add' x y := by funext i; simp; ring
  map_smul' c x := by funext i; simp; ring

@[simp] theorem P_apply (x : V) (i : Fin 3) :
    P x i = x i - (x 0 + x 1 + x 2) / 3 := rfl

@[simp] theorem mem_zeroSum (x : V) : x ∈ zeroSum ↔ x 0 + x 1 + x 2 = 0 := by
  rfl

theorem P_mem_zeroSum (x : V) : P x ∈ zeroSum := by
  rw [mem_zeroSum]
  simp only [P_apply]
  ring

theorem stdInner_comm (x y : V) : stdInner x y = stdInner y x := by
  simp only [stdInner, Fin.sum_univ_three]
  ring

theorem stdInner_add_left (x y z : V) :
    stdInner (x + y) z = stdInner x z + stdInner y z := by
  simp only [stdInner, Fin.sum_univ_three, Pi.add_apply]
  ring

theorem stdInner_sub_left (x y z : V) :
    stdInner (x - y) z = stdInner x z - stdInner y z := by
  simp only [stdInner, Fin.sum_univ_three, Pi.sub_apply]
  ring

theorem stdInner_smul_left (c : ℝ) (x y : V) :
    stdInner (c • x) y = c * stdInner x y := by
  simp only [stdInner, Fin.sum_univ_three, Pi.smul_apply, smul_eq_mul]
  ring

/-- `P` really is orthogonal projection: the residual is orthogonal to the plane. -/
theorem P_orthogonal (x y : V) (hy : y ∈ zeroSum) :
    stdInner (x - P x) y = 0 := by
  rw [mem_zeroSum] at hy
  simp only [stdInner, Fin.sum_univ_three, Pi.sub_apply, P_apply]
  linear_combination ((x 0 + x 1 + x 2) / 3) * hy

theorem P_idempotent (x : V) : P (P x) = P x := by
  have h := (mem_zeroSum (P x)).mp (P_mem_zeroSum x)
  funext i
  change P x i - (P x 0 + P x 1 + P x 2) / 3 = P x i
  rw [h]
  ring

theorem P_self_adjoint (x y : V) : stdInner (P x) y = stdInner x (P y) := by
  simp only [stdInner, Fin.sum_univ_three, P_apply]
  ring

theorem P_eq_self_of_mem_zeroSum {x : V} (hx : x ∈ zeroSum) : P x = x := by
  rw [mem_zeroSum] at hx
  funext i
  simp only [P_apply, hx]
  ring

theorem ker_P : LinearMap.ker P = ℝ ∙ oneVec := by
  ext x
  constructor
  · intro hx
    have hx0 : P x = 0 := hx
    have heq : ∀ i : Fin 3, x i = (x 0 + x 1 + x 2) / 3 := by
      intro i
      have hi := congrFun hx0 i
      simp only [P_apply, Pi.zero_apply] at hi
      linarith
    rw [Submodule.mem_span_singleton]
    refine ⟨(x 0 + x 1 + x 2) / 3, ?_⟩
    funext i
    simp [oneVec, heq i]
  · intro hx
    rw [Submodule.mem_span_singleton] at hx
    obtain ⟨c, rfl⟩ := hx
    change P (c • oneVec) = 0
    funext i
    fin_cases i <;> simp [oneVec] <;> ring

/-- The three projected basis vectors. -/
def w (i : Fin 3) : V := P (e i)

theorem w_mem_zeroSum (i : Fin 3) : w i ∈ zeroSum := P_mem_zeroSum (e i)

theorem w_apply (i j : Fin 3) :
    w i j = (if i = j then 1 else 0) - 1 / 3 := by
  simp only [w, P_apply]
  have h : e i 0 + e i 1 + e i 2 = 1 := by
    fin_cases i <;> norm_num [e]
  rw [h]
  simp only [e]

@[simp] theorem e_apply (i j : Fin 3) : e i j = if i = j then 1 else 0 := rfl

theorem w_normSq (i : Fin 3) : normSq (w i) = 2 / 3 := by
  fin_cases i <;>
    norm_num [normSq, stdInner, Fin.sum_univ_three, w_apply]

end
end ElementalPeeling.LoopWall.A2


namespace ElementalPeeling.LoopWall.A2

noncomputable section

/-- Coordinate equality for vectors in `Fin 3 → ℝ`. -/
theorem vec_eq_iff {x y : V} : x = y ↔ x 0 = y 0 ∧ x 1 = y 1 ∧ x 2 = y 2 := by
  constructor
  · intro h; exact ⟨congrFun h 0, congrFun h 1, congrFun h 2⟩
  · rintro ⟨h0, h1, h2⟩
    funext i
    fin_cases i <;> assumption

/-- The six signed projected basis vectors, without duplicates. -/
def weightList : List V := [w 0, w 1, w 2, -w 0, -w 1, -w 2]

theorem w_sum : ∑ i, w i = 0 := by
  funext j
  simp only [Fin.sum_univ_three, Finset.sum_apply, Pi.add_apply, Pi.zero_apply]
  fin_cases j <;> norm_num [w_apply]

theorem w_injective : Function.Injective w := by
  intro i j h
  by_contra hij
  have hji : j ≠ i := Ne.symm hij
  have hh := congrFun h i
  norm_num [w_apply, hij, hji] at hh

theorem w_ne_neg_w (i j : Fin 3) : w i ≠ -w j := by
  intro h
  by_cases hij : i = j
  · subst j
    have hh := congrFun h i
    norm_num [w_apply] at hh
  · have hji : j ≠ i := Ne.symm hij
    have hh := congrFun h i
    norm_num [w_apply, hij, hji] at hh

theorem neg_w_ne_w (i j : Fin 3) : -w i ≠ w j := by
  intro h
  exact w_ne_neg_w i j (by simpa only [neg_neg] using congrArg Neg.neg h)

theorem weightList_nodup : weightList.Nodup := by
  simp [weightList, List.nodup_cons, w_injective.eq_iff, w_ne_neg_w, neg_w_ne_w]

theorem weightList_length : weightList.length = 6 := by rfl

theorem mem_weightList_iff (x : V) :
    x ∈ weightList ↔ ∃ i : Fin 3, x = w i ∨ x = -w i := by
  constructor
  · intro hx
    simp only [weightList, List.mem_cons, List.mem_singleton, List.not_mem_nil,
      or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨0, Or.inl rfl⟩
    · exact ⟨1, Or.inl rfl⟩
    · exact ⟨2, Or.inl rfl⟩
    · exact ⟨0, Or.inr rfl⟩
    · exact ⟨1, Or.inr rfl⟩
    · exact ⟨2, Or.inr rfl⟩
  · rintro ⟨i, hi⟩
    fin_cases i <;> simp [weightList] at hi ⊢ <;> tauto

/-- Ordered roots `e i - e j`; ordered pairs give the usual opposite pairs. -/
def r (i j : Fin 3) : V := e i - e j

/-- The six nonzero A2 roots, with opposite roots adjacent. -/
def rootList : List V := [r 0 1, r 1 0, r 0 2, r 2 0, r 1 2, r 2 1]

theorem r_mem_zeroSum (i j : Fin 3) : r i j ∈ zeroSum := by
  rw [mem_zeroSum]
  fin_cases i <;> fin_cases j <;> norm_num [r, e]

theorem r_ne_zero {i j : Fin 3} (hij : i ≠ j) : r i j ≠ 0 := by
  intro h
  have hh := congrFun h i
  have hji : j ≠ i := Ne.symm hij
  simp [r, e, hij, hji] at hh

theorem r_normSq {i j : Fin 3} (hij : i ≠ j) : normSq (r i j) = 2 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [normSq, stdInner, Fin.sum_univ_three, r, e] at *

theorem rootList_nodup : rootList.Nodup := by
  norm_num [rootList, List.nodup_cons, vec_eq_iff, r, e]

theorem rootList_length : rootList.length = 6 := by rfl

end
end ElementalPeeling.LoopWall.A2


namespace ElementalPeeling.LoopWall.A2

theorem mem_rootList_iff (x : V) :
    x ∈ rootList ↔ ∃ i j : Fin 3, i ≠ j ∧ x = r i j := by
  constructor
  · intro hx
    simp only [rootList, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨0, 1, by decide, rfl⟩
    · exact ⟨1, 0, by decide, rfl⟩
    · exact ⟨0, 2, by decide, rfl⟩
    · exact ⟨2, 0, by decide, rfl⟩
    · exact ⟨1, 2, by decide, rfl⟩
    · exact ⟨2, 1, by decide, rfl⟩
  · rintro ⟨i, j, hij, rfl⟩
    fin_cases i <;> fin_cases j <;> simp_all [rootList]

theorem rootList_sum : rootList.sum = 0 := by
  apply vec_eq_iff.mpr
  norm_num [rootList, r, e]

theorem r_reverse (i j : Fin 3) : r j i = -r i j := by
  dsimp [r]
  abel

/-- Opposite roots are displayed as three pairs. -/
theorem rootList_opposite_pairs :
    rootList = [r 0 1, -r 0 1, r 0 2, -r 0 2, r 1 2, -r 1 2] := by
  simp only [rootList]
  rw [show r 1 0 = -r 0 1 from r_reverse 0 1,
    show r 2 0 = -r 0 2 from r_reverse 0 2,
    show r 2 1 = -r 1 2 from r_reverse 1 2]

/-- The explicit eight-weight list of the adjoint: six roots and two zeros. -/
def adjointWeights : List V := rootList ++ [0, 0]

theorem adjointWeights_length : adjointWeights.length = 8 := by rfl

theorem adjointWeights_sum : adjointWeights.sum = 0 := by
  simp [adjointWeights, rootList_sum]

theorem mem_adjointWeights_iff (x : V) :
    x ∈ adjointWeights ↔ x ∈ rootList ∨ x = 0 := by
  simp [adjointWeights]

theorem zero_not_mem_rootList : (0 : V) ∉ rootList := by
  intro h
  obtain ⟨i, j, hij, hz⟩ := (mem_rootList_iff 0).mp h
  exact r_ne_zero hij hz.symm

/-- The only linear relations among the three projected coordinate weights are
scalar multiples of their displayed relation `w 0 + w 1 + w 2 = 0`. -/
theorem linear_relation_iff (c : Fin 3 → ℝ) :
    (∑ i, c i • w i) = 0 ↔ c 0 = c 1 ∧ c 1 = c 2 := by
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp only [Fin.sum_univ_three, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, Pi.zero_apply] at h0 h1
    norm_num [w_apply] at h0 h1
    constructor <;> linarith
  · rintro ⟨h01, h12⟩
    have hc : ∀ i, c i = c 0 := by
      intro i
      fin_cases i
      · rfl
      · exact h01.symm
      · exact h12.symm.trans h01.symm
    simp_rw [hc]
    rw [← Finset.smul_sum, w_sum, smul_zero]

/-- The two independent zero-weight directions can be represented explicitly by
`r 0 1` and `r 1 2`: they are linearly independent. -/
theorem cartan_directions_independent :
    LinearIndependent ℝ ![r 0 1, r 1 2] := by
  rw [Fintype.linearIndependent_iff]
  intro c h i
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp [r, e, Fin.sum_univ_two] at h0 h1
  fin_cases i <;> simp at * <;> linarith

/-- The two Cartan directions span the sum-zero plane. -/
theorem mem_zeroSum_iff_cartan_combination (x : V) :
    x ∈ zeroSum ↔ ∃ a b : ℝ, x = a • r 0 1 + b • r 1 2 := by
  constructor
  · intro hx
    rw [mem_zeroSum] at hx
    refine ⟨x 0, x 0 + x 1, ?_⟩
    apply vec_eq_iff.mpr
    norm_num [r, e]
    linarith
  · rintro ⟨a, b, rfl⟩
    rw [mem_zeroSum]
    norm_num [r, e]

end ElementalPeeling.LoopWall.A2

open ElementalPeeling.LoopWall.A2
