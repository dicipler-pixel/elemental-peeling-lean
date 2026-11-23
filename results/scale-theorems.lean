/-
  scale-theorems.lean

  The residue skeleton of the two ladders, with the primality step discharged:
  from "p and p+2 are prime" to the class, and from the class to the segment
  classes; then the element ladder's counting, and the dichotomy that keeps the
  two alphabets apart.

  Every theorem is proved by `omega`, `ring`, `norm_num` or `Nat.dvd_prime`;
  `#print axioms` returns propext, Classical.choice, Quot.sound and nothing else.
-/
import Mathlib

namespace Scale

/-! ## A. The prime ladder, from primality -/

/-- A prime above 2 is odd. -/
theorem prime_odd (p : ℕ) (hp : Nat.Prime p) (h : 2 < p) : p % 2 = 1 := by
  rcases Nat.Prime.eq_two_or_odd hp with h' | h' <;> omega

/-- If `p` and `p+2` are primes above 5, then `p ≡ 2 (mod 3)`: `3 ∣ p` would force `p = 3`,
    and `3 ∣ p+2` would force `p+2 = 3`. -/
theorem prime_mod3 (p : ℕ) (hp : Nat.Prime p) (hp2 : Nat.Prime (p + 2)) (h : 5 < p) :
    p % 3 = 2 := by
  have h3 : ¬ (3 ∣ p) := by intro hd; have := (Nat.dvd_prime hp).mp hd; omega
  have h32 : ¬ (3 ∣ p + 2) := by intro hd; have := (Nat.dvd_prime hp2).mp hd; omega
  omega

/-- **The class of a twin start.** If `p` and `p+2` are primes above 5, then `p` is one of
    `11, 17, 29` modulo 30 — the three twin classes. The exclusion of `23` is
    `5 ∣ p+2`, and the exclusion of `1, 7, 13, 19` is `3`. -/
theorem twin_class (p : ℕ) (hp : Nat.Prime p) (hp2 : Nat.Prime (p + 2)) (h : 5 < p) :
    p % 30 = 11 ∨ p % 30 = 17 ∨ p % 30 = 29 := by
  have h2 : p % 2 = 1 := prime_odd p hp (by omega)
  have h3 : p % 3 = 2 := prime_mod3 p hp hp2 h
  have h5 : ¬ (5 ∣ p) := by intro hd; have := (Nat.dvd_prime hp).mp hd; omega
  have h52 : ¬ (5 ∣ p + 2) := by intro hd; have := (Nat.dvd_prime hp2).mp hd; omega
  omega

/-- A number in one of the three twin classes is `≡ 2 (mod 3)`. -/
theorem class_mod3 (p : ℤ) (h : p % 30 = 11 ∨ p % 30 = 17 ∨ p % 30 = 29) : p % 3 = 2 := by
  rcases h with h | h | h <;> omega

/-- Two odd numbers both `≡ 2 (mod 3)` differ by a multiple of 6. -/
theorem twin_gap_mod6 (p q : ℤ) (hp : p % 3 = 2) (hq : q % 3 = 2)
    (hp2 : p % 2 = 1) (hq2 : q % 2 = 1) : (q - p) % 6 = 0 := by
  omega

/-- Hence the air of a twin segment, `q - p - 2`, is `≡ 4 (mod 6)`. -/
theorem air_mod6 (p q : ℤ) (hp : p % 3 = 2) (hq : q % 3 = 2)
    (hp2 : p % 2 = 1) (hq2 : q % 2 = 1) : (q - p - 2) % 6 = 4 := by
  omega

/-- So the air takes exactly five classes modulo 30. -/
theorem air_five_classes (a : ℤ) (h : a % 6 = 4) :
    a % 30 = 4 ∨ a % 30 = 10 ∨ a % 30 = 16 ∨ a % 30 = 22 ∨ a % 30 = 28 := by
  omega

/-- The five classes carry five distinct end digits: the class determines the digit and
    conversely, so the map is injective on a five-element set — a bijection. -/
theorem class_digit_inj (a b : ℤ)
    (ha : a % 30 = 4 ∨ a % 30 = 10 ∨ a % 30 = 16 ∨ a % 30 = 22 ∨ a % 30 = 28)
    (hb : b % 30 = 4 ∨ b % 30 = 10 ∨ b % 30 = 16 ∨ b % 30 = 22 ∨ b % 30 = 28)
    (hd : a % 10 = b % 10) : a % 30 = b % 30 := by
  rcases ha with h | h | h | h | h <;> rcases hb with k | k | k | k | k <;> omega

/-- The twin total is the air plus the pair, so its class is the air's class plus 4. -/
theorem total_class (a t : ℤ) (h : t = a + 4)
    (ha : a % 30 = 4 ∨ a % 30 = 10 ∨ a % 30 = 16 ∨ a % 30 = 22 ∨ a % 30 = 28) :
    t % 30 = 8 ∨ t % 30 = 14 ∨ t % 30 = 20 ∨ t % 30 = 26 ∨ t % 30 = 2 := by
  rcases ha with h' | h' | h' | h' | h' <;> omega

/-- The carry: a prime `≡ 2 (mod 3)` cannot be followed by a gap of 2, since `p+4` is
    divisible by 3. -/
theorem carry_mod3 (p : ℤ) (h : p % 3 = 2) : (p + 4) % 3 = 0 := by
  omega

/-- One of the eight admissible classes of any 30-block is divisible by 7. -/
theorem row_capacity_seven (k : ℕ) :
    (30*k + 7) % 7 = 0 ∨ (30*k + 29) % 7 = 0 ∨ (30*k + 11) % 7 = 0 ∨ (30*k + 13) % 7 = 0 ∨
    (30*k + 17) % 7 = 0 ∨ (30*k + 19) % 7 = 0 ∨ (30*k + 23) % 7 = 0 ∨ (30*k + 1) % 7 = 0 := by
  have h : k % 7 = 0 ∨ k % 7 = 1 ∨ k % 7 = 2 ∨ k % 7 = 3 ∨ k % 7 = 4 ∨ k % 7 = 5 ∨ k % 7 = 6 := by omega
  rcases h with h | h | h | h | h | h | h <;> omega

/-- A multiple of 7 above 7 is not prime, so the divisible class of the previous theorem
    is composite — the row holds at most seven primes. -/
theorem seven_dvd_not_prime (n : ℕ) (hn : 7 < n) (hd : 7 ∣ n) : ¬ Nat.Prime n := by
  intro hp
  have := (Nat.dvd_prime hp).mp hd
  omega

/-- Among any seven consecutive terms of a progression of step 30 one is divisible by 7
    (`30 ≡ 2`, `2⁻¹ ≡ 4 (mod 7)`). -/
theorem run_bound (a : ℕ) : ∃ i < 7, (a + 30*i) % 7 = 0 := by
  refine ⟨(7 - (4*(a%7))%7) % 7, by omega, by omega⟩

/-- The only seven-term progression of that shape that survives the divisibility is the one
    through 7, and it fails at its last term. -/
theorem seven_187 : ¬ Nat.Prime (7 + 30*6) := by norm_num

/-! ## B. The element ladder -/

/-- The widths of the blocks nested in a shell sum to twice a square. -/
theorem widths_sum (m : ℕ) : (Finset.range m).sum (fun l => 2*(2*l+1)) = 2*m^2 := by
  induction m with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ih]; ring

/-- The rung width: a rung `q` collects `l = 0 … ⌈q/2⌉-1`, so `W(q) = 2⌈q/2⌉²`. -/
theorem rung_width (q : ℕ) :
    (Finset.range ((q+1)/2)).sum (fun l => 2*(2*l+1)) = 2*((q+1)/2)^2 :=
  widths_sum ((q+1)/2)

/-- Every block width is even: capacities count pairs. -/
theorem width_even (l : ℕ) : (2*(2*l+1)) % 2 = 0 := by omega

/-- Every block width ends in one of the five even digits. -/
theorem width_digit_even (l : ℕ) :
    (2*(2*l+1)) % 10 = 2 ∨ (2*(2*l+1)) % 10 = 6 ∨ (2*(2*l+1)) % 10 = 0 ∨
    (2*(2*l+1)) % 10 = 4 ∨ (2*(2*l+1)) % 10 = 8 := by omega

/-- Every shell capacity is even. -/
theorem shell_even (n : ℕ) : (2*n^2) % 2 = 0 := by omega

/-- Every shell capacity also ends in one of the five even digits. -/
theorem shell_digit_even (n : ℕ) :
    (2*n^2) % 10 = 0 ∨ (2*n^2) % 10 = 2 ∨ (2*n^2) % 10 = 4 ∨
    (2*n^2) % 10 = 6 ∨ (2*n^2) % 10 = 8 := by omega

/-- The inventory of the measured table. -/
theorem inventory : (2:ℤ)*7 + 6*6 + 10*4 + 14*2 = 118 := by norm_num

/-- And the next two closures, from the same depth law. -/
theorem closures_next :
    (2:ℤ)*8 + 6*7 + 10*5 + 14*3 + 18*1 = 168 ∧
    (2:ℤ)*9 + 6*8 + 10*6 + 14*4 + 18*2 = 218 := by norm_num

/-! ## C. The dichotomy -/

/-- No capacity ends in an odd digit, so the four live prime digits cannot label one. -/
theorem capacity_never_odd (l n : ℕ) :
    (2*(2*l+1)) % 2 = 0 ∧ (2*n^2) % 2 = 0 ∧
    ¬ ((2*(2*l+1)) % 10 = 1 ∨ (2*(2*l+1)) % 10 = 3 ∨
       (2*(2*l+1)) % 10 = 7 ∨ (2*(2*l+1)) % 10 = 9) := by
  refine ⟨by omega, by omega, ?_⟩
  omega

end Scale
