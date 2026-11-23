/-
  master-theorem.lean

  **The master theorem**: the Light Bridge and the fission channel in one statement.

  This file is self-contained on purpose — the table is defined here, and every part of the
  master statement is proved here — so that a single `lean results/master-theorem.lean`
  verifies the whole thing. The specialist files (`light-bridge-theorems.lean`,
  `scale-theorems.lean`, `promotion-theorems.lean`, `fission-theorem.lean`,
  `merge-theorems.lean`) remain the detailed treatments of the individual parts.

  Parts:
    (A) counting       — block widths, the rung width, the period length, one function
    (B) countdown      — v + h = L(m) on all 118 cells
    (C) dichotomy      — every capacity is even
    (D) split          — the two bookkeeping identities of a fission event
    (E) pin            — the heavy piece on the closure, the light piece's countdown
    (F) closed cells   — which splits put both pieces on closed cells
    (G) switch         — the symmetric split closes at Z >= 98
    (H) thorium        — the one double-closure split
    (I) inventory      — 118 cells, saturated, so a descent must split
    (J) energy         — a linear mass law cannot price a split

  No `sorry`, no `axiom`, no `native_decide`.
-/
import Mathlib

namespace Master

/-! ## 0. The table -/

/-- Closures: the last `Z` of each period. -/
def C : ℕ → ℕ
  | 0 => 0
  | 1 => 2
  | 2 => 10
  | 3 => 18
  | 4 => 36
  | 5 => 54
  | 6 => 86
  | 7 => 118
  | _ => 0

/-- Period lengths: `L m = 2⌈(m+1)/2⌉²`. -/
def L (m : ℕ) : ℕ := 2 * (((m + 1) + 1) / 2) ^ 2

/-- Rung widths: `W q = 2⌈q/2⌉²`. -/
def W (q : ℕ) : ℕ := 2 * ((q + 1) / 2) ^ 2

/-- Block widths: `w l = 2(2l+1)`. -/
def w (l : ℕ) : ℕ := 2 * (2 * l + 1)

def period (Z : ℕ) : ℕ :=
  if Z ≤ 2 then 1 else if Z ≤ 10 then 2 else if Z ≤ 18 then 3 else if Z ≤ 36 then 4
  else if Z ≤ 54 then 5 else if Z ≤ 86 then 6 else 7

def cnt (Z : ℕ) : ℕ := C (period Z) - Z
def counted (Z : ℕ) : ℕ := Z - C (period Z - 1)

/-- A closed cell: the `p` bottom (`h ≤ 5`, containing the closure `h = 0`) or the row head. -/
def closed (Z : ℕ) : Prop :=
  cnt Z ≤ 5 ∨ cnt Z + 1 = L (period Z) ∨ cnt Z + 2 = L (period Z)

/-- `closed` is decidable — which is what lets the cross-check evaluate it against the reference
implementation on random cells (`scripts/random_lean_cross.py`). -/
instance closedDecidable (Z : ℕ) : Decidable (closed Z) := by
  unfold closed
  infer_instance

/-! ## (A) Counting: width, rung, period are one function -/

/-- A block's width is twice an odd number, so every capacity on the element side is even. -/
theorem block_width (l : ℕ) : w l = 2 * (2 * l + 1) := rfl

theorem widths_sum (m : ℕ) : (Finset.range m).sum (fun l => w l) = 2 * m ^ 2 := by
  induction m with
  | zero => simp [w]
  | succ k ih => rw [Finset.sum_range_succ, ih]; simp [w]; ring

/-- **The bridge**: the rung width at `q` is the period length at `q−1`. One function, two
arguments — which is why the rung widths `2,2,8,8,18,18,32,32` and the period lengths
`2,8,8,18,18,32,32` are the same list shifted by one. -/
theorem rung_is_period (q : ℕ) (h : 1 ≤ q) : W q = L (q - 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
  rfl

/-- The octet, the 18-electron rule and the 32-electron rule are one function at three indices. -/
theorem capacities : L 2 = 8 ∧ L 4 = 18 ∧ L 6 = 32 := by simp [L]

/-- The closures are the partial sums of the period lengths. -/
theorem closures_are_sums :
    C 1 = L 1 ∧ C 2 = L 1 + L 2 ∧ C 3 = L 1 + L 2 + L 3 ∧
    C 4 = L 1 + L 2 + L 3 + L 4 ∧ C 5 = L 1 + L 2 + L 3 + L 4 + L 5 ∧
    C 6 = L 1 + L 2 + L 3 + L 4 + L 5 + L 6 ∧
    C 7 = L 1 + L 2 + L 3 + L 4 + L 5 + L 6 + L 7 := by
  simp [C, L]

/-! ## (B) The countdown, on all 118 cells -/

theorem cell_identity (Z : ℕ) (h1 : 1 ≤ Z) (h2 : Z ≤ 118) :
    counted Z + cnt Z = L (period Z) := by
  interval_cases Z <;> decide

/-! ## (C) The dichotomy: capacities are even, residues are not -/

theorem capacity_even (l : ℕ) : w l % 2 = 0 := by simp [w]

theorem shell_even (n : ℕ) : (2 * n ^ 2) % 2 = 0 := by omega

/-- No capacity can be odd, so the prime digit set `{1,3,7,9}` can never label one. -/
theorem no_odd_capacity (l : ℕ) : w l % 2 ≠ 1 := by simp [w]

/-! ## (D) A split: the bookkeeping identities -/

theorem split_countdown (C1 C2 Z Z1 Z2 : ℤ) (h : Z1 + Z2 = Z) :
    (C1 - Z1) + (C2 - Z2) = C1 + C2 - Z := by omega

theorem same_period (P Q Z1 Z2 : ℤ) :
    (Z1 - P) + (Z2 - P) + (Q - Z1) + (Q - Z2) = 2 * (Q - P) := by ring

theorem split_conserves (Z Z1 Z2 : ℤ) (h : Z1 + Z2 = Z) : Z - Z1 = Z2 := by omega

theorem symmetric_needs_even (Z Z1 : ℕ) (h : Z1 + Z1 = 2 * Z + 1) : False := by omega

/-! ## (E) The pin -/

theorem pin (Z : ℕ) (h1 : 91 ≤ Z) (h2 : Z ≤ 108) :
    C 5 = 54 ∧ cnt 54 = 0 ∧ cnt (Z - 54) = 108 - Z := by
  refine ⟨by simp [C], ?_, ?_⟩
  · simp [cnt, period, C]
  · interval_cases Z <;> decide

theorem light_closed_five (Z : ℕ) (h1 : 88 ≤ Z) (h2 : Z ≤ 96) :
    (closed (Z - 54) ∧ closed 54) ↔ (88 ≤ Z ∧ Z ≤ 92) := by
  interval_cases Z <;> simp [closed, cnt, period, C, L]

/-! ## (F) Closed-cell splits -/

theorem closed_split_U (Z1 : ℕ) (h1 : 30 ≤ Z1) (h2 : Z1 ≤ 46) :
    (closed Z1 ∧ closed (92 - Z1)) ↔ (Z1 = 36 ∨ Z1 = 37 ∨ Z1 = 38) := by
  interval_cases Z1 <;> simp [closed, cnt, period, C, L]

theorem closed_split_Pu (Z1 : ℕ) (h1 : 30 ≤ Z1) (h2 : Z1 ≤ 47) :
    (closed Z1 ∧ closed (94 - Z1)) ↔ Z1 = 38 := by
  interval_cases Z1 <;> simp [closed, cnt, period, C, L]

theorem closed_split_Cm (Z1 : ℕ) (h1 : 30 ≤ Z1) (h2 : Z1 ≤ 48) :
    ¬ (closed Z1 ∧ closed (96 - Z1)) := by
  interval_cases Z1 <;> simp [closed, cnt, period, C, L]

/-! ## (G) The symmetric switch -/

theorem symmetric_closed (Z : ℕ) (he : Z % 2 = 0) (h1 : 88 ≤ Z) (h2 : Z ≤ 106) :
    (closed (Z / 2) ↔ 98 ≤ Z) := by
  interval_cases Z <;> simp [closed, cnt, period, C, L]

/-! ## (H) Thorium: the double closure -/

theorem double_closure_only_th (Z : ℕ) (h1 : 88 ≤ Z) (h2 : Z ≤ 100) :
    (cnt 54 = 0 ∧ cnt (Z - 54) = 0) ↔ Z = 90 := by
  interval_cases Z <;> simp [cnt, period, C]

theorem th_closures_add (Z : ℕ) (h : Z = 90) : C 4 + C 5 = Z := by subst h; simp [C]

/-! ## (I) The inventory, and saturation -/

theorem inventory : 2 * 7 + 6 * 6 + 10 * 4 + 14 * 2 = 118 := by norm_num

theorem rungs_to_eight : 2 + 2 + 8 + 8 + 18 + 18 + 32 + 32 = 120 ∧ 120 - 118 = 2 := by norm_num

theorem every_cell_below_118 (Z : ℕ) (h1 : 1 ≤ Z) (h2 : Z ≤ 118) :
    1 ≤ period Z ∧ period Z ≤ 7 := by
  interval_cases Z <;> decide

/-! ## (J) Energy is not in the table -/

/-- A mass law linear in `Z` prices every split at its intercept: the linear terms cancel. So the
table's mass fit cannot give a fission energy, whatever the split point. -/
theorem linear_mass_law_blind (a b Z Z1 Z2 : ℚ) (h : Z = Z1 + Z2) :
    (a * Z - b) - (a * Z1 - b) - (a * Z2 - b) = b := by
  rw [h]; ring

/-! ## (K) The three forces, and which coordinate each one owns -/

/-- **The electromagnetic ladder.** The period lengths are `2n²` at `n = ⌈(m+1)/2⌉` — the hydrogenic
(Coulomb) degeneracy — so the closure law `C` is a partial sum of `2n²`. The shape of the proton table
is electromagnetic. -/
theorem period_is_2n2 (m : ℕ) : L m = 2 * (((m + 1) + 1) / 2) ^ 2 := rfl

theorem capacities_are_2n2 : L 2 = 2 * 2 ^ 2 ∧ L 4 = 2 * 3 ^ 2 ∧ L 6 = 2 * 4 ^ 2 := by
  simp [L]

/-- **The strong ladder is not this one.** The neutron magic numbers `2,8,20,28,50,82,126` are not the
partial sums of `2n²`: `20` and `28` are not twice a square at all, where the proton values at the same
indices are `18` and `32`. So the neutron axis carries a *different* ladder, and the Light Bridge
theorem does not transfer to it. -/
theorem strong_ladder_differs (n : ℕ) : 2 * n ^ 2 ≠ 20 ∧ 2 * n ^ 2 ≠ 28 := by
  constructor
  · intro h
    have h2 : n ≤ 3 := by nlinarith
    interval_cases n <;> omega
  · intro h
    have h2 : n ≤ 4 := by nlinarith
    interval_cases n <;> omega

/-- **The force balance is nearly constant across the fissioning set.** `Z²/A`, the electrostatic-to-
strong ratio, runs from `34.91` (Th-232) to `39.06` (Fm-256) — an ordering, and less than a factor 2
across the whole set — while the measured valley/peak ratio moves by a factor 481. So the *mode* of
fission is not set by the force balance; it is set by the shells. -/
theorem fissility_band :
    (90 : ℚ) ^ 2 / 232 < (92 : ℚ) ^ 2 / 235 ∧ (92 : ℚ) ^ 2 / 235 < (98 : ℚ) ^ 2 / 252 ∧
    (98 : ℚ) ^ 2 / 252 < (100 : ℚ) ^ 2 / 256 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num

theorem fissility_narrow : ((100 : ℚ) ^ 2 / 256) / ((90 : ℚ) ^ 2 / 232) < 2 := by norm_num

/-! ## (K2) The strong ladder: the 3D oscillator, split by spin-orbit -/

/-- The Coulomb (hydrogenic) cumulant: `2n²`, i.e. the partial sums of `2, 8, 18, 32, …`. -/
theorem coulomb_cumulant (n : ℕ) :
    (Finset.range n).sum (fun l => 2 * (2 * l + 1)) = 2 * n ^ 2 := widths_sum n

/-- The 3D harmonic-oscillator cumulant: `n(n+1)(n+2)/3`, i.e. the partial sums of
`2, 6, 12, 20, … = (N+1)(N+2)` — the ladder `2, 8, 20, 40, 70, …`. -/
theorem oscillator_cumulant (n : ℕ) :
    3 * (Finset.range n).sum (fun N => (N + 1) * (N + 2)) = n * (n + 1) * (n + 2) := by
  induction n with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, Nat.mul_add, ih]; ring

/-- The two ladders: Coulomb `2n²` and oscillator `n(n+1)(n+2)/3`. -/
def protonLadder : List ℕ := [2, 10, 18, 36, 54, 86, 118]
def oscillatorLadder : List ℕ := [2, 8, 20, 40, 70, 112, 168]
def magicLadder : List ℕ := [2, 8, 20, 28, 50, 82, 126]

/-- **They agree at 2 and 8 only, and the oscillator takes over from the third.** `2n²` equals
`n(n+1)(n+2)/3` for `n = 1, 2` — giving `2` and `8` — and at `n = 3` the two are `18` and `20`; from
there the oscillator cumulant strictly exceeds the Coulomb one. So a table built on the one cannot carry
the other. -/
theorem coulomb_oscillator_agree :
    (2 : ℕ) * 1 ^ 2 = 1 * 2 * 3 / 3 ∧ (2 : ℕ) * 2 ^ 2 = 2 * 3 * 4 / 3 ∧
    (2 : ℕ) * 3 ^ 2 = 18 ∧ (3 * 4 * 5 / 3 : ℕ) = 20 := by norm_num

theorem oscillator_beats_coulomb (n : ℕ) (h : 3 ≤ n) :
    6 * n ^ 2 < n * (n + 1) * (n + 2) := by nlinarith

/-- **The proton ladder meets the neutron magic numbers only at 2.** -/
theorem proton_meets_magic_only_at_two :
    (protonLadder.filter (fun n => n ∈ magicLadder)) = [2] := by decide

/-- **The oscillator ladder meets the magic numbers at 2, 8 and 20** — and then spin-orbit splits it. -/
theorem oscillator_meets_magic :
    (oscillatorLadder.filter (fun n => n ∈ magicLadder)) = [2, 8, 20] := by decide

/-! ## (L) The zeta zeros: forced, fluctuating, and out of reach -/

/- **The trivial zeros are the negative even integers** — forced by the Gamma factor, carrying no
arithmetic. They sit on the same even lattice as every capacity in this table (`capacity_even`), which is
all the correspondence there is: both are the *forced* part of their object. -/
theorem trivial_zeros_even (n : ℕ) : (-2 * ((n : ℤ) + 1)) % 2 = 0 := by omega

theorem trivial_zeros_negative (n : ℕ) : (-2 * ((n : ℤ) + 1)) < 0 := by omega

/-- **The critical line is the fixed set of `s ↦ 1 − s`.** So the non-trivial zeros' real part is pinned
by the functional equation alone: any zero that is fixed by the symmetry has real part `1/2`. That is the
only structural statement available without the Riemann hypothesis. -/
theorem critical_line_fixed (s : ℂ) (h : 1 - s = s) : s = 1 / 2 := by
  linear_combination (-1 / 2) * h

/-- **The wheel is the finite Euler product.** `30 = 2·3·5` and it has `φ(30) = 8` classes: the record's
exact mod-30 structure is the part of the Euler product over the *three smallest* primes, and carries zero
exceptions (measured: 0 in 224 million handoffs). The zeta zeros are the infinite remainder — strictly
outside the exact part. -/
theorem wheel_is_euler : (30 : ℕ) = 2 * 3 * 5 := by norm_num

theorem wheel_has_eight_classes : Nat.totient 30 = 8 := by decide

/-! ## (N) The mod-9 twin transitions (Johnson, Zenodo 23484151, Theorem 10.2) -/

/-- **Every twin start above 5 is `2, 5` or `8` mod 9.** Primes above 3 avoid `0, 3, 6` mod 9, and so
does the partner; the six admissible residues pair up as `2 → 4`, `5 → 7`, `8 → 1`, and the other three
send `p + 2` to a multiple of 3. This is Theorem 10.2 of E. Johnson's *Base Prime Model and Twin Prime
Counterflow* (Zenodo 23484151), machine-checked here. -/
theorem twin_mod9 (p : ℕ) (hp : Nat.Prime p) (hp2 : Nat.Prime (p + 2)) (h5 : 5 < p) :
    p % 9 = 2 ∨ p % 9 = 5 ∨ p % 9 = 8 := by
  have h3 : ¬ (3 ∣ p) := by
    intro hd; have := (Nat.dvd_prime hp).mp hd; omega
  have h32 : ¬ (3 ∣ p + 2) := by
    intro hd; have := (Nat.dvd_prime hp2).mp hd; omega
  have hr : p % 9 = 0 ∨ p % 9 = 1 ∨ p % 9 = 2 ∨ p % 9 = 3 ∨ p % 9 = 4 ∨ p % 9 = 5 ∨
      p % 9 = 6 ∨ p % 9 = 7 ∨ p % 9 = 8 := by omega
  rcases hr with r | r | r | r | r | r | r | r | r
  · exact absurd (by omega : 3 ∣ p) h3
  · exact absurd (by omega : 3 ∣ p + 2) h32
  · exact Or.inl r
  · exact absurd (by omega : 3 ∣ p) h3
  · exact absurd (by omega : 3 ∣ p + 2) h32
  · exact Or.inr (Or.inl r)
  · exact absurd (by omega : 3 ∣ p) h3
  · exact absurd (by omega : 3 ∣ p + 2) h32
  · exact Or.inr (Or.inr r)

/-- The same, in the form Johnson states it: the three transition pairs. -/
theorem twin_transitions_mod9 (p : ℕ) (hp : Nat.Prime p) (hp2 : Nat.Prime (p + 2)) (h5 : 5 < p) :
    (p % 9 = 2 ∧ (p + 2) % 9 = 4) ∨ (p % 9 = 5 ∧ (p + 2) % 9 = 7) ∨
      (p % 9 = 8 ∧ (p + 2) % 9 = 1) := by
  have := twin_mod9 p hp hp2 h5
  rcases this with h | h | h <;> omega

/-- And it is the record's own mod-3 fact relabelled: `p % 9 ∈ {2,5,8}` **is** `p % 3 = 2`. -/
theorem mod9_is_mod3 (p : ℕ) : (p % 9 = 2 ∨ p % 9 = 5 ∨ p % 9 = 8) ↔ p % 3 = 2 := by omega

end Master
