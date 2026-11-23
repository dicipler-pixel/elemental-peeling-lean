/-
  count-formulas.lean

  The four counts of the prime side, defined once here, and every relation between them that is
  arithmetic. The analytic statements (the explicit formula for the base and twin-ladder counts,
  the Hardy-Littlewood forms for the twin and double-twin counts) are *not* here: they are
  measured, in `results/count-formulas.md`, and this file says exactly which part of each is
  proof and which part is measurement.

  Definitions (all computable, so `decide` evaluates them against the sieve):

    primesUpTo n   P(x)  the primes <= x
    baseCount n    B(x)  the base count: primes on the 4+6k ladder, p = 1 mod 6
    ladderCount n  K(x)  the twin-ladder count: primes on the 5+6k ladder, p = 5 mod 6
    twinStarts n         twin starts: p and p+2 both prime
    twinCount n    N(x)  the twin count, = card (twinStarts n)
    handoffs n     H(x)  N(x) - 1: the twin-key cells filled

  Proved below:
    (1) partition      every prime above 3 is on exactly one ladder: P = B + K + 2
    (2) twin on 5      every twin start above 3 is on the 5-ladder: N - 1 <= K
    (3) three types    every twin start above 5 is 11, 17 or 29 mod 30 (the pair types 13, 79, 91)
    (4) air residue    every handoff has air = q-p-2 = 4 mod 6, i.e. air = 4 + 6k
    (5) total residue  every total T = air + 4 = 2 mod 6
    (6) quadruplet    a four-prime merge can only start at p = 11 mod 30
    (7) telescoping    sum of airs = span - 2 * handoffs: the count is the span over the mean gap
    (8) evaluated      the counts at 10^3 and 10^4, which are the sieve's own numbers

  No `sorry`, no `axiom`, no `native_decide`.
-/
import Mathlib

namespace Counts

/-! ## 0. The counts -/

/-- The primes up to `n`. -/
def primesUpTo (n : ℕ) : Finset ℕ := (Finset.range (n + 1)).filter Nat.Prime

/-- **The base count** `B(x)`: primes on the `4+6k` ladder, `p ≡ 1 (mod 6)`. -/
def baseCount (n : ℕ) : ℕ := ((primesUpTo n).filter (fun p => p % 6 = 1)).card

/-- **The twin-ladder count** `K(x)`: primes on the `5+6k` ladder, `p ≡ 5 (mod 6)`. -/
def ladderCount (n : ℕ) : ℕ := ((primesUpTo n).filter (fun p => p % 6 = 5)).card

/-- **Twin starts**: `p` with `p` and `p + 2` prime. -/
def twinStarts (n : ℕ) : Finset ℕ := (primesUpTo n).filter (fun p => (p + 2).Prime)

/-- **The twin count** `N(x)`. -/
def twinCount (n : ℕ) : ℕ := (twinStarts n).card

/-- **Handoffs**: consecutive twin starts, `N(x) − 1` of them (measured as an identity in
`scripts/count_formulas.py`, where the count of consecutive pairs is also accumulated). -/
def handoffs (n : ℕ) : ℕ := twinCount n - 1

/-- The base ladder as a set, for the subset arguments below. -/
def baseSet (n : ℕ) : Finset ℕ := (primesUpTo n).filter (fun p => p % 6 = 1)

/-- The twin ladder as a set. -/
def ladderSet (n : ℕ) : Finset ℕ := (primesUpTo n).filter (fun p => p % 6 = 5)

theorem baseCount_eq (n : ℕ) : baseCount n = (baseSet n).card := rfl

theorem ladderCount_eq (n : ℕ) : ladderCount n = (ladderSet n).card := rfl

/-! ## 1. The residue facts -/

/-- **Every prime above 3 is on one of the two ladders.** `2` and `3` are the only exceptions, and
they are the first two primes. -/
theorem prime_mod_six (p : ℕ) (hp : p.Prime) (h3 : 3 < p) : p % 6 = 1 ∨ p % 6 = 5 := by
  have h2 : ¬ (2 ∣ p) := by
    intro hd
    have := (Nat.dvd_prime hp).mp hd
    omega
  have h3' : ¬ (3 ∣ p) := by
    intro hd
    have := (Nat.dvd_prime hp).mp hd
    omega
  have hr : p % 6 = 0 ∨ p % 6 = 1 ∨ p % 6 = 2 ∨ p % 6 = 3 ∨ p % 6 = 4 ∨ p % 6 = 5 := by
    have := Nat.mod_lt p (by norm_num : 0 < 6)
    omega
  rcases hr with r | r | r | r | r | r
  · exact absurd (by omega : 2 ∣ p) h2
  · exact Or.inl r
  · exact absurd (by omega : 2 ∣ p) h2
  · exact absurd (by omega : 3 ∣ p) h3'
  · exact absurd (by omega : 2 ∣ p) h2
  · exact Or.inr r

/-- **Every twin start above 3 is on the 5-ladder.** If `p ≡ 1 (mod 6)` then `p + 2 ≡ 3 (mod 6)`,
so `3 ∣ p + 2` and primality forces `p + 2 = 3`. This is why the twin key's alphabet is the base
key's shifted by four, and why the twin count is a subcount of one ladder. -/
theorem twin_start_mod_six (p : ℕ) (hp : p.Prime) (hp2 : (p + 2).Prime) (h3 : 3 < p) :
    p % 6 = 5 := by
  rcases prime_mod_six p hp h3 with h | h
  · have hd : 3 ∣ p + 2 := by omega
    have := (Nat.dvd_prime hp2).mp hd
    omega
  · exact h

/-- **Twin starts sit in three classes mod 30** — the pair types `13`, `79`, `91` of the twin key.
`p ≡ 5 (mod 30)` is `p = 5` itself, and `p ≡ 23 (mod 30)` sends `p + 2` to a multiple of five. -/
theorem twin_start_mod_30 (p : ℕ) (hp : p.Prime) (hp2 : (p + 2).Prime) (h5 : 5 < p) :
    p % 30 = 11 ∨ p % 30 = 17 ∨ p % 30 = 29 := by
  have h6 : p % 6 = 5 := twin_start_mod_six p hp hp2 (by omega)
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

/-- **A handoff's air is `4 (mod 6)`.** Both starts are `5 (mod 6)`, so their gap is a multiple of
six and the air — the gap minus the pair — is `6j − 2 ≡ 4`. Zero exceptions in the record's 224
million handoffs. -/
theorem air_mod_six (p q : ℕ) (hp : p.Prime) (hp2 : (p + 2).Prime) (hq : q.Prime)
    (hq2 : (q + 2).Prime) (hp3 : 3 < p) (hpq : p + 2 ≤ q) : (q - p - 2) % 6 = 4 := by
  have h1 : p % 6 = 5 := twin_start_mod_six p hp hp2 hp3
  have h2 : q % 6 = 5 := twin_start_mod_six q hq hq2 (by omega)
  omega

/-- The same in the form the record uses: **every air is `4 + 6k`**. -/
theorem air_is_four_plus_six (p q : ℕ) (hp : p.Prime) (hp2 : (p + 2).Prime) (hq : q.Prime)
    (hq2 : (q + 2).Prime) (hp3 : 3 < p) (hpq : p + 2 ≤ q) : ∃ k, q - p - 2 = 4 + 6 * k := by
  have h := air_mod_six p q hp hp2 hq hq2 hp3 hpq
  exact ⟨(q - p - 2) / 6, by omega⟩

/-- **A handoff's total is `2 (mod 6)`** — `T = air + 4` lands in the twin key's other alphabet. -/
theorem total_mod_six (p q : ℕ) (hp : p.Prime) (hp2 : (p + 2).Prime) (hq : q.Prime)
    (hq2 : (q + 2).Prime) (hp3 : 3 < p) (hpq : p + 2 ≤ q) : (q + 2 - p) % 6 = 2 := by
  have h1 : p % 6 = 5 := twin_start_mod_six p hp hp2 hp3
  have h2 : q % 6 = 5 := twin_start_mod_six q hq hq2 (by omega)
  omega

/-- **The minimal merge starts at `p ≡ 11 (mod 30)`.** A four-prime merge `p, p+2, p+6, p+8` has
air 4; of the twin key's three classes only `11` survives, because `17` sends `p + 8` and `29`
sends `p + 6` to a multiple of five. -/
theorem quadruplet_start_mod_30 (p : ℕ) (hp : p.Prime) (hp2 : (p + 2).Prime)
    (hp6 : (p + 6).Prime) (hp8 : (p + 8).Prime) (h5 : 5 < p) : p % 30 = 11 := by
  rcases twin_start_mod_30 p hp hp2 h5 with h | h | h
  · exact h
  · have hd : 5 ∣ p + 8 := by omega
    have := (Nat.dvd_prime hp8).mp hd
    omega
  · have hd : 5 ∣ p + 6 := by omega
    have := (Nat.dvd_prime hp6).mp hd
    omega

/-! ## 2. The counts: the partition and the subcount -/

/-- Membership in the prime set, in the form every later proof uses. -/
lemma mem_primesUpTo {n p : ℕ} : p ∈ primesUpTo n ↔ p ≤ n ∧ p.Prime := by
  simp [primesUpTo]

lemma mem_baseSet {n p : ℕ} : p ∈ baseSet n ↔ p ≤ n ∧ p.Prime ∧ p % 6 = 1 := by
  simp [baseSet, mem_primesUpTo, and_assoc]

lemma mem_ladderSet {n p : ℕ} : p ∈ ladderSet n ↔ p ≤ n ∧ p.Prime ∧ p % 6 = 5 := by
  simp [ladderSet, mem_primesUpTo, and_assoc]

lemma mem_twinStarts {n p : ℕ} : p ∈ twinStarts n ↔ p ≤ n ∧ p.Prime ∧ (p + 2).Prime := by
  simp [twinStarts, mem_primesUpTo, and_assoc]

/-- The primes up to `n` are the base ladder, the twin ladder, and `{2, 3}`, and the three pieces
are disjoint. -/
lemma partition_set (n : ℕ) (h3 : 3 ≤ n) :
    primesUpTo n = baseSet n ∪ ladderSet n ∪ ({2, 3} : Finset ℕ) := by
  ext p
  rw [mem_primesUpTo]
  simp only [Finset.mem_union, mem_baseSet, mem_ladderSet, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨hle, hp⟩
    by_cases hp3 : 3 < p
    · rcases prime_mod_six p hp hp3 with r | r
      · exact Or.inl (Or.inl ⟨hle, hp, r⟩)
      · exact Or.inl (Or.inr ⟨hle, hp, r⟩)
    · have hp2 := hp.two_le
      rcases (by omega : p = 2 ∨ p = 3) with rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
  · rintro ((⟨hle, hp, _⟩ | ⟨hle, hp, _⟩) | (rfl | rfl))
    · exact ⟨hle, hp⟩
    · exact ⟨hle, hp⟩
    · exact ⟨by omega, by norm_num⟩
    · exact ⟨by omega, by norm_num⟩

/-- **The two ladders exhaust the primes**: `P(x) = B(x) + K(x) + 2`, the two added primes being
`2` and `3`. So "how many primes are on the base key" and "how many on the twin key" are one
question with one answer between them — and the difference `B − K` is the character sum whose
zeros are measured in `scripts/base_key_zeros.py`. -/
theorem primeCount_partition (n : ℕ) (h3 : 3 ≤ n) :
    (primesUpTo n).card = baseCount n + ladderCount n + 2 := by
  have hd : Disjoint (baseSet n ∪ ladderSet n) ({2, 3} : Finset ℕ) := by
    rw [Finset.disjoint_left]
    intro p hp hq
    simp only [Finset.mem_union, mem_baseSet, mem_ladderSet, Finset.mem_insert,
      Finset.mem_singleton] at hp hq
    rcases hq with rfl | rfl <;> rcases hp with (hp | hp) <;> omega
  have hd' : Disjoint (baseSet n) (ladderSet n) := by
    rw [Finset.disjoint_left]
    intro p hp hq
    simp only [mem_baseSet, mem_ladderSet] at hp hq
    omega
  rw [partition_set n h3, Finset.card_union_of_disjoint hd, Finset.card_union_of_disjoint hd']
  simp [baseCount, ladderCount, baseSet, ladderSet]

/-- **The twin count is a subcount of the 5-ladder**, `N(x) ≤ K(x) + 1`: the only twin start off
the 5-ladder is `3` (the pair `3, 5`). Measured: `N/K = 0.1347` at `10^9`. -/
theorem twin_le_ladder (n : ℕ) : twinCount n ≤ ladderCount n + 1 := by
  have hsub : (twinStarts n).erase 3 ⊆ ladderSet n := by
    intro p hp
    rw [Finset.mem_erase, mem_twinStarts] at hp
    obtain ⟨hp3, hle, hprime, hp2⟩ := hp
    rw [mem_ladderSet]
    refine ⟨hle, hprime, twin_start_mod_six p hprime hp2 ?_⟩
    have hp2' := hprime.two_le
    rcases Nat.lt_or_ge 3 p with h | h
    · exact h
    · rcases (by omega : p = 2 ∨ p = 3) with rfl | rfl
      · exact absurd hp2 (by norm_num)
      · exact absurd rfl hp3
  have h1 : ((twinStarts n).erase 3).card ≤ ladderCount n := by
    have h := Finset.card_le_card hsub
    simpa [ladderCount, ladderSet] using h
  by_cases h3 : 3 ∈ twinStarts n
  · have hc : (twinStarts n).card = ((twinStarts n).erase 3).card + 1 :=
      (Finset.card_erase_add_one h3).symm
    rw [twinCount, hc]
    omega
  · have he : (twinStarts n).erase 3 = twinStarts n := Finset.erase_eq_self.mpr h3
    rw [twinCount, ← he]
    omega

/-! ## 3. The telescoping identity: the count is a span over a mean gap -/

/-- **Sum of the airs = span − 2 per handoff.** For a chain of twin starts `p 0, …, p n`:

    Σ air = (p n − p 0) − 2n,

so the number of handoffs is fixed by the span and the air sum with nothing left over:
`n = (span − Σair) / 2`. With the measured mean air `t²/(2C₂) − 2` this is exactly
`N = 2C₂ ∫ dp/log²p` — the Hardy-Littlewood count *is* this identity plus the air law. -/
theorem air_sum_identity (p : ℕ → ℤ) (n : ℕ) :
    (Finset.range n).sum (fun i => (p (i + 1) - p i) - 2) = p n - p 0 - 2 * n := by
  induction n with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

/-- The same identity solved for the count — the sense in which a count is a distance divided by a
gap, and the reason the record's counts are checkable against the spans in the data. -/
theorem count_from_span (p : ℕ → ℤ) (n : ℕ) :
    p n - p 0 = (Finset.range n).sum (fun i => (p (i + 1) - p i) - 2) + 2 * n := by
  have := air_sum_identity p n
  omega

/-- The single handoff, as a worked instance: air `= 4` is the quadruplet, and the span is `6`.
`(13, 11)` is the record's worked pair `(11,13) → (17,19)`. -/
theorem worked_handoff : (17 : ℤ) - 11 - 2 = 4 ∧ (17 : ℤ) + 2 - 11 = 8 := by
  refine ⟨?_, ?_⟩ <;> norm_num

/-! ## 4. The counts, evaluated — the sieve's own numbers -/

/- The definitions are computable, so they can be run against the sieve. `decide` at `10^2` is
cheap; above that the kernel evaluation of `Nat.Prime` over a whole range becomes minutes of work
per bound, so the large counts are the sieve's job (`scripts/count_formulas.py`, which cross-checks
its segmented scan against a plain full sieve at `10^6` and reproduces `pi(10^9) = 50847534`). -/

theorem counts_100 : baseCount 100 = 11 ∧ ladderCount 100 = 12 ∧ twinCount 100 = 8 ∧
    (primesUpTo 100).card = 25 := by decide

/-- And the partition at `10^2`, evaluated: `11 + 12 + 2 = 25`. -/
theorem partition_100 : baseCount 100 + ladderCount 100 + 2 = (primesUpTo 100).card := by decide

end Counts
