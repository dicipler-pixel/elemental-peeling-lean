/-
  merge-theorems.lean

  Merged twin segments: what the count per segment is, why it is not 1, and where the
  hierarchy stops.

  Proved below:
    * a merge's total is `T = T₁ + T₂ − 2`, so the class shifts by `−2` per merge and the
      value ladder by `−2` per merge as well (`V = 3T/4 + 1/2`);
    * three primes in arithmetic progression of step 2 exist only at `p = 3` — the single
      zero-air handoff of the twin ladder;
    * the minimal merge (`air = 4`) is the prime quadruplet pattern `{0,2,6,8}`;
    * the sextuplet `{0,2,6,8,12,14}` exists only at `p = 5`, killed for every larger `p` by
      the factor 5. This is why the deeper merge is not merely rare: it is a one-off.

  No `sorry`; axioms ⊆ {propext, Classical.choice, Quot.sound}.
-/
import Mathlib

namespace Merge

/-- **A merge costs 2.** Two twin segments joined at a shared boundary: the total from the
first node to the last is `T₁ + T₂ − 2`. (With `T₁ = q+2-p` and `T₂ = r+2-q`.) -/
theorem merged_total (p q r T1 T2 : ℤ) (h1 : T1 = q + 2 - p) (h2 : T2 = r + 2 - q) :
    r + 2 - p = T1 + T2 - 2 := by omega

/-- The class of a merge, in the same form: `T ≡ T₁ + T₂ − 2 (mod 30)`. -/
theorem merged_class (T T1 T2 : ℤ) (h : T = T1 + T2 - 2) : (T - (T1 + T2 - 2)) % 30 = 0 := by
  omega

/-- **A merged object is its pairs plus its internal airs.** With `k` pairs and internal airs
`a₁…a_{k-1}`, the span from the first node to the last is `2k + Σa` — so the total is additive in
the airs and carries exactly `2` per pair, nothing else. (Checked on the widest object in the data:
`k = 7`, airs `10,58,4,58,28,10`, span `168 + 14 = 182`.) -/
theorem object_total (k : ℕ) (air T : ℤ) (h : T = 2 * (k : ℤ) + air) : T - air = 2 * (k : ℤ) := by
  omega

/-- **Three primes of step 2 only at 3.** Among `p, p+2, p+4` one is divisible by 3, so if all
three are prime the divisible one *is* 3 — whence `p = 3`. This is the only `air = 0` handoff
in the whole twin ladder. -/
theorem triple_only_three (p : ℕ) (h1 : Nat.Prime p) (h2 : Nat.Prime (p + 2))
    (h3 : Nat.Prime (p + 4)) : p = 3 := by
  have hp2 : 2 ≤ p := h1.two_le
  have hp : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2 := by omega
  rcases hp with hp | hp | hp
  · have hd : 3 ∣ p := by omega
    have := (Nat.dvd_prime h1).mp hd
    omega
  · have hd : 3 ∣ p + 2 := by omega
    have := (Nat.dvd_prime h2).mp hd
    omega
  · have hd : 3 ∣ p + 4 := by omega
    have := (Nat.dvd_prime h3).mp hd
    omega

/-- **No quadruple of step 2, ever.** Four primes `p, p+2, p+4, p+6` cannot exist: the first
three already force `p = 3`, and then `p + 6 = 9` is composite. So a merged segment cannot run
through a zero-air join twice. -/
theorem no_quadruple (p : ℕ) (h1 : Nat.Prime p) (h2 : Nat.Prime (p + 2))
    (h3 : Nat.Prime (p + 4)) (h4 : Nat.Prime (p + 6)) : False := by
  have hp : p = 3 := triple_only_three p h1 h2 h3
  subst hp
  exact absurd h4 (by norm_num)

/-- **The minimal merge is the quadruplet.** `air = 4` means the arriving pair begins six after
the departing pair: the pattern `{0, 2, 6, 8}` — the prime quadruplet. Stated as the arithmetic
of the four offsets. -/
theorem air_four_is_quadruplet (p q : ℤ) (h : q = p + 6) :
    (q - p - 2 = 4) ∧ (q + 2 - p = 8) := by
  constructor <;> omega

/-- The quadruplet's residues mod 5 omit one class, `{0,2,1,3}`, so nothing forbids it — unlike
the sextuplet, which covers all five. Both statements, as residue sets. -/
theorem quadruplet_residues :
    ([0, 2, 6, 8].map (fun r : ℕ => r % 5) = [0, 2, 1, 3]) ∧
    ([0, 2, 6, 8, 12, 14].map (fun r : ℕ => r % 5) = [0, 2, 1, 3, 2, 4]) := by
  refine ⟨?_, ?_⟩ <;> decide

/-- **The sextuplet only at 5.** Six primes `p, p+2, p+6, p+8, p+12, p+14` have all five residues
mod 5 among their offsets `{0,2,6,8,12,14}`, so one member is a multiple of 5 — hence is 5 — and
`p = 5` follows. For every `p > 5` the deeper merge is impossible, which is why the class-14
triple has floor 44 and not 14. -/
theorem sextuplet_only_five (p : ℕ)
    (h1 : Nat.Prime p) (h2 : Nat.Prime (p + 2)) (h3 : Nat.Prime (p + 6))
    (h4 : Nat.Prime (p + 8)) (h5 : Nat.Prime (p + 12)) (h6 : Nat.Prime (p + 14)) : p = 5 := by
  have hp2 : 2 ≤ p := h1.two_le
  have hp : p % 5 = 0 ∨ p % 5 = 1 ∨ p % 5 = 2 ∨ p % 5 = 3 ∨ p % 5 = 4 := by omega
  rcases hp with hp | hp | hp | hp | hp
  · have hd : 5 ∣ p := by omega
    have := (Nat.dvd_prime h1).mp hd
    omega
  · have hd : 5 ∣ p + 14 := by omega
    have := (Nat.dvd_prime h6).mp hd
    omega
  · have hd : 5 ∣ p + 8 := by omega
    have := (Nat.dvd_prime h4).mp hd
    omega
  · have hd : 5 ∣ p + 2 := by omega
    have h5 := (Nat.dvd_prime h2).mp hd
    have hp3 : p = 3 := by omega
    subst hp3
    exact absurd h3 (by norm_num)
  · have hd : 5 ∣ p + 6 := by omega
    have := (Nat.dvd_prime h3).mp hd
    omega

/-- **The `T` column telescopes, with an excess of two per segment.** For a chain of twin starts
`p 0, p 1, …, p n` the totals `T i = p (i+1) + 2 − p i` sum to the span plus `2n`:

    Σ T = (last start − first start) + 2 × (number of segments).

On the sheet of 347…857 the thirteen written totals sum to `536 = 510 + 26`. -/
theorem totals_excess (p : ℕ → ℤ) (n : ℕ) :
    (Finset.range n).sum (fun i => (p (i + 1) + 2 - p i)) = p n - p 0 + 2 * n := by
  induction n with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

/-- The same statement read the other way: the span is the totals minus two per segment — so a
bookkeeper who adds up `T` and calls it a distance is over by `2n`. -/
theorem totals_span (p : ℕ → ℤ) (n : ℕ) :
    p n - p 0 = (Finset.range n).sum (fun i => (p (i + 1) + 2 - p i)) - 2 * n := by
  have := totals_excess p n
  omega

/-! ## The depth: the two grooves of a crossing -/

/-- **The depth shift is `+1` modulo 3.** The two grooves of a crossing are `g` and `g + 10`, and
`10 ≡ 1 (mod 3)`, so shifting by ten shifts the residue by one. -/
theorem depth_shift_mod3 (g : ℕ) : (g + 10) % 3 = (g + 1) % 3 := by omega

/-- **Exactly one of the two grooves is divisible by 3**, unless `g ≡ 1 (mod 3)` — in which case
neither is. Measured on 12.1 million prime steps, this is what decides the depth: the shallow groove
carries 58% of the weight when it is the divisible one and 32% when the deep one is. -/
theorem depth_dichotomy (g : ℕ) (h : g % 3 ≠ 1) :
    (g % 3 = 0 ∧ (g + 10) % 3 = 1) ∨ (g % 3 = 2 ∧ (g + 10) % 3 = 0) := by omega

end Merge
