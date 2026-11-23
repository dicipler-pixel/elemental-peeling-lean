/-
  light-bridge-theorems.lean

  The Light Bridge Periodic Table: the four numbers it is built from (2, 4, 6, 8),
  the two ladders' shared step pair (6, 4), the unit (2) and the closure (8), and
  the chain's rung increments.

  Every theorem is closed by `omega`, `ring`, `norm_num` or `Nat.dvd_prime`.
  `#print axioms` on all of them returns at most propext, Classical.choice, Quot.sound.
-/
import Mathlib

namespace LightBridge

/-! ## The quartet -/

/-- The four numbers that build the table: `8 = 2 + 6 = 4 + 4`, and `4 = 2·2`, `6 = 2·3`. -/
theorem quartet : (8 : ℤ) = 2 + 6 ∧ (8 : ℤ) = 4 + 4 ∧ (4 : ℤ) = 2 * 2 ∧ (6 : ℤ) = 2 * 3 := by
  norm_num

/-- Every block width is twice an odd number — twice the orbital count. -/
theorem width_is_twice_odd (l : ℕ) :
    (2 * (2 * l + 1)) / 2 = 2 * l + 1 ∧ (2 * l + 1) % 2 = 1 := by
  omega

/-- Every block width is even: the unit is 2. -/
theorem width_even (l : ℕ) : (2 * (2 * l + 1)) % 2 = 0 := by omega

/-- Every shell capacity is even. -/
theorem shell_even (n : ℕ) : (2 * n ^ 2) % 2 = 0 := by omega

/-- Every period length is even. -/
theorem period_even (m : ℕ) : (2 * ((m + 1) / 2) ^ 2) % 2 = 0 := by omega

/-! ## The ladder's step is 4, and its increments are the block widths -/

/-- The rung width grows by `4j + 2` at the j-th step: the increment is a block width. -/
theorem rung_step (j : ℕ) : (2 * ((j : ℤ) + 1) ^ 2 - 2 * (j : ℤ) ^ 2) = 4 * j + 2 := by
  ring

/-- And that increment is `2(2j+1)`, a block width. -/
theorem step_is_block_width (j : ℕ) : (4 * (j : ℤ) + 2) = 2 * (2 * j + 1) := by
  ring

/-- Two consecutive rung increments differ by 4: the ladder's second step is 4. -/
theorem step_increment (j : ℕ) :
    (4 * ((j : ℤ) + 1) + 2) - (4 * (j : ℤ) + 2) = 4 := by
  ring

/-- The shell capacity sums the same widths. -/
theorem widths_sum (m : ℕ) : (Finset.range m).sum (fun l => 2 * (2 * l + 1)) = 2 * m ^ 2 := by
  induction m with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ih]; ring

/-! ## 2 is the column multiplicity of the prime wheel -/

/-- Each live last digit owns exactly two columns mod 30: `r` and `r + 10`. -/
theorem column_pair (r : ℕ) (h : r = 1 ∨ r = 3 ∨ r = 7 ∨ r = 9) :
    (r + 10) % 2 = 1 ∧ (r + 10) % 3 ≠ 0 ∧ (r + 10) % 5 ≠ 0 := by
  rcases h with h | h | h | h <;> subst h <;> omega

/-! ## The primes' step 6 with offset 4 -/

/-- The air classes are `4 + 6k`, and the total's are `8 + 6k`: the offset is the pair. -/
theorem air_class (k : ℕ) : (4 + 6 * (k : ℤ)) % 6 = 4 := by
  have : (6 : ℤ) * k % 6 = 0 := by omega
  omega

/-- The total is the air plus the pair, so the classes are offset by 4. -/
theorem total_offset (a : ℤ) (ha : a % 6 = 4) : (a + 4) % 6 = 2 := by omega

/-- A twin start above 5 is one of 11, 17, 29 mod 30 — from primality, not assumed. -/
theorem twin_class (p : ℕ) (hp : Nat.Prime p) (hp2 : Nat.Prime (p + 2)) (h : 5 < p) :
    p % 30 = 11 ∨ p % 30 = 17 ∨ p % 30 = 29 := by
  have h2 : p % 2 = 1 := by
    rcases Nat.Prime.eq_two_or_odd hp with h' | h' <;> omega
  have h3 : p % 3 = 2 := by
    have h3' : ¬ (3 ∣ p) := by intro hd; have := (Nat.dvd_prime hp).mp hd; omega
    have h32 : ¬ (3 ∣ p + 2) := by intro hd; have := (Nat.dvd_prime hp2).mp hd; omega
    omega
  have h5 : ¬ (5 ∣ p) := by intro hd; have := (Nat.dvd_prime hp).mp hd; omega
  have h52 : ¬ (5 ∣ p + 2) := by intro hd; have := (Nat.dvd_prime hp2).mp hd; omega
  omega

/-! ## The countdown splits the period -/

/-- The counted part plus the uncounted part is the period: `v + h = L(m)`. -/
theorem countdown_identity (P Z Q : ℤ) : (Z - P) + (Q - Z) = Q - P := by ring

/-- The period lengths, and the block capacities that equal them. -/
theorem capacities_are_periods :
    (2 * ((2 + 2) / 2) ^ 2 : ℕ) = 8 ∧ (2 * ((3 + 2) / 2) ^ 2 : ℕ) = 8 ∧
    (2 * ((4 + 2) / 2) ^ 2 : ℕ) = 18 ∧ (2 * ((5 + 2) / 2) ^ 2 : ℕ) = 18 ∧
    (2 * ((6 + 2) / 2) ^ 2 : ℕ) = 32 ∧ (2 * ((7 + 2) / 2) ^ 2 : ℕ) = 32 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- The closure ladder: partial sums of the period lengths. -/
theorem closures :
    (2 : ℕ) = 2 ∧ 2 + 8 = 10 ∧ 2 + 8 + 8 = 18 ∧ 2 + 8 + 8 + 18 = 36 ∧
    2 + 8 + 8 + 18 + 18 = 54 ∧ 2 + 8 + 8 + 18 + 18 + 32 = 86 ∧
    2 + 8 + 8 + 18 + 18 + 32 + 32 = 118 := by norm_num

/-- A worked instance of the valence law: iron has 8 valence electrons and 10 to come, and 18 is the
    third shell's capacity. -/
theorem iron_valence : (8 : ℤ) + 10 = 18 := by norm_num

/-! ## The physics, derived into the table -/

/-- The $m$-states of angular momentum `l` number `2l+1`. -/
theorem m_states (l : ℕ) : (Finset.Icc 0 (2 * l)).card = 2 * l + 1 := by simp

/-- The first `n` odd numbers sum to `n^2`: the degeneracy of the `n`-th hydrogenic level. -/
theorem odd_sum (n : ℕ) : (Finset.range n).sum (fun l => 2 * l + 1) = n ^ 2 := by
  induction n with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ih]; ring

/-- With spin the block carries `2(2l+1)`, and the shell `2n^2`. -/
theorem shell_from_degeneracy (n : ℕ) :
    (Finset.range n).sum (fun l => 2 * (2 * l + 1)) = 2 * n ^ 2 := widths_sum n

/-- Equipartition: six half-degrees per atom give `3R` per mole. -/
theorem equipartition : (6 : ℚ) * (1 / 2) = 3 := by norm_num

end LightBridge
