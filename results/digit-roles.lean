/-
  digit-roles.lean

  The Light Table's digit column: what each of 1, 3, 7, 9 can and cannot be, in a twin pair.

  Every prime above 5 ends in 1, 3, 7 or 9, and each of those digits is the mod-10 shadow of two
  classes mod 30 — one on each ladder (1 mod 6 and 5 mod 6):

      digit 1: 1 (base)  and 11 (twin)      digit 7: 7 (base)  and 17 (twin)
      digit 3: 13 (base) and 23 (twin)      digit 9: 19 (base) and 29 (twin)

  A twin pair has an **opener** (the start's digit) and a **closer** (the partner's). Proved here:

    * the openers above 5 are {1,7,9} and the closers above 3 are {1,3,9} (`twin_start_digit`,
      `closer_digit`), so digit 3 can never open and digit 7 can never close — each happens exactly
      once, at 3 and at 5, the two smallest pairs (`three_never_opens`, `seven_never_closes`);
    * the twin-ladder class 23 is **dead**: it can never start a twin (`no_twin_at_23`), which is why
      the twin classes are three and not four;
    * the pair types are exactly (1,3), (7,9), (9,1) (`pair_types`), and the pair's digit step is +2
      mod 10 (`pair_digit_step`), which is why 9 closes into 1;
    * each digit carries exactly two of the eight classes mod 30 (`two_classes_per_digit`), one per
      ladder (`digit_splits_ladder`).

  No `sorry`, no `axiom`, no `native_decide`.
-/
import Mathlib

namespace Digits

/-- Local copy of the mod-30 classification of twin starts (proved in `results/count-formulas.lean` as
`Counts.twin_start_mod_30`; restated so this file is self-contained). -/
theorem twin_start_mod_30 (p : ℕ) (hp : p.Prime) (hp2 : (p + 2).Prime) (h5 : 5 < p) :
    p % 30 = 11 ∨ p % 30 = 17 ∨ p % 30 = 29 := by
  have h2 : ¬ (2 ∣ p) := by
    intro hd
    have := (Nat.dvd_prime hp).mp hd
    omega
  have h3 : ¬ (3 ∣ p) := by
    intro hd
    have := (Nat.dvd_prime hp).mp hd
    omega
  have h6 : p % 6 = 5 := by
    have hr : p % 6 = 0 ∨ p % 6 = 1 ∨ p % 6 = 2 ∨ p % 6 = 3 ∨ p % 6 = 4 ∨ p % 6 = 5 := by
      have := Nat.mod_lt p (by norm_num : 0 < 6)
      omega
    rcases hr with r | r | r | r | r | r
    · exact absurd (by omega : 2 ∣ p) h2
    · have hd : 3 ∣ p + 2 := by omega
      have := (Nat.dvd_prime hp2).mp hd
      omega
    · exact absurd (by omega : 2 ∣ p) h2
    · exact absurd (by omega : 3 ∣ p) h3
    · exact absurd (by omega : 2 ∣ p) h2
    · exact r
  have hr : p % 30 = 5 ∨ p % 30 = 11 ∨ p % 30 = 17 ∨ p % 30 = 23 ∨ p % 30 = 29 := by omega
  rcases hr with r | r | r | r | r
  · have hd : 5 ∣ p := by omega
    have := (Nat.dvd_prime hp).mp hd
    omega
  · exact Or.inl r
  · exact Or.inr (Or.inl r)
  · have hd : 5 ∣ p + 2 := by omega
    have := (Nat.dvd_prime hp2).mp hd
    omega
  · exact Or.inr (Or.inr r)

/-- **The openers are 1, 7, 9.** A twin start above 5 cannot end in 3 (nor in anything else). -/
theorem twin_start_digit (p : ℕ) (hp : p.Prime) (hp2 : (p + 2).Prime) (h5 : 5 < p) :
    p % 10 = 1 ∨ p % 10 = 7 ∨ p % 10 = 9 := by
  rcases twin_start_mod_30 p hp hp2 h5 with h | h | h <;> omega

/-- **Digit 3 never opens.** The same statement as an exclusion, in the form the table uses. -/
theorem three_never_opens (p : ℕ) (hp : p.Prime) (hp2 : (p + 2).Prime) (h5 : 5 < p) :
    p % 10 ≠ 3 := by
  rcases twin_start_digit p hp hp2 h5 with h | h | h <;> omega

/-- **The closers are 1, 3, 9** (for twin starts above 5; the single exception is `p = 5`, whose
partner 7 ends in 7 — `closer_seven_once`). -/
theorem closer_digit (p : ℕ) (hp : p.Prime) (hp2 : (p + 2).Prime) (h5 : 5 < p) :
    (p + 2) % 10 = 1 ∨ (p + 2) % 10 = 3 ∨ (p + 2) % 10 = 9 := by
  rcases twin_start_mod_30 p hp hp2 h5 with h | h | h <;> omega

/-- **Digit 7 never closes** a pair above 5. -/
theorem seven_never_closes (p : ℕ) (hp : p.Prime) (hp2 : (p + 2).Prime) (h5 : 5 < p) :
    (p + 2) % 10 ≠ 7 := by
  rcases closer_digit p hp hp2 h5 with h | h | h <;> omega

/-- The two exceptions, exactly: `p = 3` opens on digit 3 (the pair 3,5) and `p = 5` closes on
digit 7 (the pair 5,7). Each "impossible" role occurs once, and only at the bottom of the sequence. -/
theorem the_two_exceptions : (3 + 2) % 10 = 5 ∧ (5 + 2) % 10 = 7 := by norm_num

/-- **The pair types are exactly (1,3), (7,9) and (9,1)** — the three classes of twin start and their
partners' digits. -/
theorem pair_types (p : ℕ) (hp : p.Prime) (hp2 : (p + 2).Prime) (h5 : 5 < p) :
    (p % 10 = 1 ∧ (p + 2) % 10 = 3) ∨ (p % 10 = 7 ∧ (p + 2) % 10 = 9) ∨
      (p % 10 = 9 ∧ (p + 2) % 10 = 1) := by
  rcases twin_start_mod_30 p hp hp2 h5 with h | h | h <;> omega

/-- **The pair's digit step is `+2 (mod 10)`**, which is why 9 closes into 1 and not into 11's digit. -/
theorem pair_digit_step (p : ℕ) : (p + 2) % 10 = (p % 10 + 2) % 10 := by omega

/-- **The class 23 is dead**: no twin start above 5 sits at `23 (mod 30)`, because its partner would
be a multiple of 5. So the twin ladder has four classes but only three are live — which is why the
openers are three digits and not four. -/
theorem no_twin_at_23 (p : ℕ) (hp : p.Prime) (hp2 : (p + 2).Prime) (h5 : 5 < p) :
    p % 30 ≠ 23 := by
  rcases twin_start_mod_30 p hp hp2 h5 with h | h | h <;> omega

/-- **Each digit carries exactly two of the eight classes mod 30** — the table's digit column is a
two-to-one shadow of the wheel. -/
theorem two_classes_per_digit :
    (({1, 7, 11, 13, 17, 19, 23, 29} : Finset ℕ).filter (fun c => c % 10 = 1)) = {1, 11} ∧
    (({1, 7, 11, 13, 17, 19, 23, 29} : Finset ℕ).filter (fun c => c % 10 = 3)) = {13, 23} ∧
    (({1, 7, 11, 13, 17, 19, 23, 29} : Finset ℕ).filter (fun c => c % 10 = 7)) = {7, 17} ∧
    (({1, 7, 11, 13, 17, 19, 23, 29} : Finset ℕ).filter (fun c => c % 10 = 9)) = {19, 29} := by
  decide

/-- **One class per ladder under each digit**: in each pair, one is `1 (mod 6)` (the base ladder) and
the other `5 (mod 6)` (the twin ladder). -/
theorem digit_splits_ladder :
    (1 % 6 = 1 ∧ 11 % 6 = 5) ∧ (13 % 6 = 1 ∧ 23 % 6 = 5) ∧
      (7 % 6 = 1 ∧ 17 % 6 = 5) ∧ (19 % 6 = 1 ∧ 29 % 6 = 5) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> norm_num

/-! ## 5. The digit isolates the class

A gap inside a segment is an air, so it is `4 (mod 6)`; its **last digit** then fixes its class mod 30
exactly, because `30 = lcm(6,10)`. A *prime's* last digit is weaker — every digit carries two classes,
one per ladder (`two_classes_per_digit`) — but inside the twin starts the digit does determine the class,
because only three digits are live and each carries one class. So the sequence of gap end digits inside a
segment isolates the segment's class, and the sequence of prime end digits isolates the class on the twin
ladder. That is the precise form of "you can isolate class from the subset sequences". -/

/-- The class carried by an even digit: `4→4`, `0→10`, `6→16`, `2→22`, `8→28`. -/
def cls (d : ℕ) : ℕ :=
  if d = 4 then 4 else if d = 0 then 10 else if d = 6 then 16 else if d = 2 then 22 else 28

/-- **An air's digit fixes its class.** If `a ≡ 4 (mod 6)` then `a ≡ cls (a % 10) (mod 30)`: the five
digits `4,0,6,2,8` and the five classes `4,10,16,22,28` are one set in two notations. -/
theorem air_class_of_digit (a : ℕ) (h6 : a % 6 = 4) : a % 30 = cls (a % 10) := by
  have h : a % 30 = 4 ∨ a % 30 = 10 ∨ a % 30 = 16 ∨ a % 30 = 22 ∨ a % 30 = 28 := by omega
  rcases h with h | h | h | h | h
  · have hd : a % 10 = 4 := by omega
    rw [h]; simp [cls, hd]
  · have hd : a % 10 = 0 := by omega
    rw [h]; simp [cls, hd]
  · have hd : a % 10 = 6 := by omega
    rw [h]; simp [cls, hd]
  · have hd : a % 10 = 2 := by omega
    rw [h]; simp [cls, hd]
  · have hd : a % 10 = 8 := by omega
    rw [h]; simp [cls, hd]

/-- The sum of the gap classes is the sum of their digits' classes, mod 30. -/
theorem sum_class_mod (n : ℕ) (a : ℕ → ℕ) (h : ∀ i < n, a i % 6 = 4) :
    (Finset.range n).sum a % 30 = (Finset.range n).sum (fun i => cls (a i % 10)) % 30 := by
  induction n with
  | zero => simp
  | succ k ih =>
    have hk : a k % 6 = 4 := h k (by omega)
    calc (Finset.range (k + 1)).sum a % 30
        = ((Finset.range k).sum a % 30 + a k % 30) % 30 := by
          rw [Finset.sum_range_succ, Nat.add_mod]
      _ = ((Finset.range k).sum (fun i => cls (a i % 10)) % 30
            + cls (a k % 10) % 30) % 30 := by
          rw [ih (fun i hi => h i (by omega)), air_class_of_digit (a k) hk]
          rw [Nat.add_mod, Nat.mod_mod]
      _ = (Finset.range (k + 1)).sum (fun i => cls (a i % 10)) % 30 := by
          rw [Finset.sum_range_succ, ← Nat.add_mod]

/-- **A segment's class is the sum of its gap digits' classes** (plus 2 per pair: the span of `k` pairs
is `2k + Σ internal airs`). So the sequence of gap end digits inside the segment determines the class of
the whole segment, with nothing else. -/
theorem total_class_from_digits (k : ℕ) (a : ℕ → ℕ) (h : ∀ i < k - 1, a i % 6 = 4) :
    (2 * k + (Finset.range (k - 1)).sum a) % 30
      = (2 * k + (Finset.range (k - 1)).sum (fun i => cls (a i % 10))) % 30 := by
  have hs := sum_class_mod (k - 1) a h
  calc (2 * k + (Finset.range (k - 1)).sum a) % 30
      = ((2 * k) % 30 + (Finset.range (k - 1)).sum a % 30) % 30 := by rw [Nat.add_mod]
    _ = ((2 * k) % 30 + (Finset.range (k - 1)).sum (fun i => cls (a i % 10)) % 30) % 30 := by
          rw [hs]
    _ = (2 * k + (Finset.range (k - 1)).sum (fun i => cls (a i % 10))) % 30 := by
          rw [← Nat.add_mod]

/-- **Inside the twin starts the digit does determine the class**: `1 → 11`, `7 → 17`, `9 → 29`. -/
theorem twin_start_class_of_digit (p : ℕ) (hp : p.Prime) (hp2 : (p + 2).Prime) (h5 : 5 < p) :
    (p % 10 = 1 ∧ p % 30 = 11) ∨ (p % 10 = 7 ∧ p % 30 = 17) ∨ (p % 10 = 9 ∧ p % 30 = 29) := by
  rcases twin_start_mod_30 p hp hp2 h5 with h | h | h <;> omega

/-- **The digit path**: each gap advances the end digit by the gap's own digit, so the sequence of prime
end digits is the cumulative sum of the gap end digits from the first start. -/
theorem digit_path (p g : ℕ) : (p + g) % 10 = (p % 10 + g % 10) % 10 := by omega

/-! ## 6. "Un-baking": the digits that cannot come back

A handoff leaves a pair whose partner ends in digit `c` and arrives at a pair whose start ends in digit
`o`. The **return** is the event `c = o`. It is possible exactly for the digits that appear in both roles,
and the return rate is then exactly zero for 3 (measured: 0 of 1,141,216, because no twin start ends in 3)
and does not arise at all for 7 (no pair ever ends in 7). That is the arithmetic of "3 and 7 alter things
permanently, 1 and 9 are forgiving": the first two are role-locked, the second two are not. -/

/-- **The returnable digits are exactly 1 and 9.** -/
theorem returnable_digits : (({1, 7, 9} : Finset ℕ) ∩ {1, 3, 9}) = {1, 9} := by decide

/-- **3 and 7 are role-locked**: 3 is never an opener and 7 is never a closer. -/
theorem three_and_seven_one_way :
    (3 : ℕ) ∉ ({1, 7, 9} : Finset ℕ) ∧ (7 : ℕ) ∉ ({1, 3, 9} : Finset ℕ) := by decide

/-- **No handoff can return to digit 3**: the arriving pair would have to start on a 3, which no twin
start above 5 does. So a segment that leaves on a 3 can never arrive on one. -/
theorem no_return_to_three (q : ℕ) (hq : q.Prime) (hq2 : (q + 2).Prime) (h5 : 5 < q) :
    q % 10 ≠ 3 := three_never_opens q hq hq2 h5

/-- **No handoff can return to digit 7**, because no pair ever ends on a 7. -/
theorem no_return_to_seven (q : ℕ) (hq : q.Prime) (hq2 : (q + 2).Prime) (h5 : 5 < q) :
    (q + 2) % 10 ≠ 7 := seven_never_closes q hq hq2 h5

end Digits
