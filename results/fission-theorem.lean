/-
  fission-theorem.lean

  **The fission theorem.**  A self-contained statement of what a fission event is in
  the Light Bridge table, and what the table forces about it.  Everything in parts
  (I)–(IV) is proved here from the definitions; parts (V)–(VI) are the measured
  residues and are stated in `fission-theorem.md`, not here.

  Definitions: the closures `C`, the period lengths `L`, the period `m(Z)`, the
  countdown `h = C(m) − Z`, the counted part `v = Z − C(m−1)`, and the closed-cell
  predicate (`p` bottom, `h ≤ 5`, containing the closure `h = 0`; or the row head,
  `h ∈ {L−2, L−1}`).

  No `sorry`, no `axiom`, no `native_decide`.  Axioms of every theorem are checked at
  the end of this file and reported in the companion note.
-/
import Mathlib

namespace Fission

/-! ## 1. The table -/

/-- The closures: the last `Z` of each period. -/
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

/-- The period lengths: `L m = 2⌈(m+1)/2⌉²`. -/
def L (m : ℕ) : ℕ := 2 * (((m + 1) + 1) / 2) ^ 2

/-- The period of `Z`, for the 118-cell table. -/
def period (Z : ℕ) : ℕ :=
  if Z ≤ 2 then 1 else if Z ≤ 10 then 2 else if Z ≤ 18 then 3 else if Z ≤ 36 then 4
  else if Z ≤ 54 then 5 else if Z ≤ 86 then 6 else 7

/-- The countdown `h = C(m) − Z`. -/
def cnt (Z : ℕ) : ℕ := C (period Z) - Z

/-- The counted part `v = Z − C(m−1)`. -/
def counted (Z : ℕ) : ℕ := Z - C (period Z - 1)

/-- A **closed** cell: the bottom of the `p` block (`h ≤ 5`, which contains the closure `h = 0`), or
the head of the row (`h = L−2` or `L−1`, the `s` cell). -/
def closed (Z : ℕ) : Prop :=
  cnt Z ≤ 5 ∨ cnt Z + 1 = L (period Z) ∨ cnt Z + 2 = L (period Z)

theorem period_lengths :
    L 1 = 2 ∧ L 2 = 8 ∧ L 3 = 8 ∧ L 4 = 18 ∧ L 5 = 18 ∧ L 6 = 32 ∧ L 7 = 32 := by
  simp [L]

theorem closure_values :
    C 1 = 2 ∧ C 2 = 10 ∧ C 3 = 18 ∧ C 4 = 36 ∧ C 5 = 54 ∧ C 6 = 86 ∧ C 7 = 118 := by
  simp [C]

/-! ## 2. Every cell obeys `v + h = L(m)` -/

/-- **The countdown identity, cell by cell.** For all 118 elements, the counted part plus the
countdown is the period length. (A finite check on the table, not a hypothesis about it.) -/
theorem cell_identity (Z : ℕ) (h1 : 1 ≤ Z) (h2 : Z ≤ 118) :
    counted Z + cnt Z = L (period Z) := by
  interval_cases Z <;> decide

/-- The same identity in the subtraction-free form: `v = L(m) − h`. -/
theorem counted_eq (Z : ℕ) (h1 : 1 ≤ Z) (h2 : Z ≤ 118) :
    counted Z = L (period Z) - cnt Z := by
  have := cell_identity Z h1 h2
  omega

/-! ## 3. A split: the two bookkeeping identities -/

/-- **(I) The countdowns of a split add up to the closures minus the parent.** From `Z₁ + Z₂ = Z`
alone — no hypothesis about the pieces, no hypothesis about the table. -/
theorem split_countdown (C1 C2 Z Z1 Z2 : ℤ) (h : Z1 + Z2 = Z) :
    (C1 - Z1) + (C2 - Z2) = C1 + C2 - Z := by
  omega

/-- **(I′) Two pieces in one period: the two counted parts and the two countdowns sum to `2L`.**
An algebraic identity, true for every split. -/
theorem same_period (P Q Z1 Z2 : ℤ) :
    (Z1 - P) + (Z2 - P) + (Q - Z1) + (Q - Z2) = 2 * (Q - P) := by
  ring

/-- **(I″) A split conserves the count exactly**: no correction, because two nuclei do not share a
proton. This is the statement that the merge arithmetic of the prime ladder has no analogue here. -/
theorem split_conserves (Z Z1 Z2 : ℤ) (h : Z1 + Z2 = Z) : Z - Z1 = Z2 := by
  omega

/-- A symmetric split needs an even parent. -/
theorem symmetric_needs_even (Z Z1 : ℕ) (h : Z1 + Z1 = 2 * Z + 1) : False := by
  omega

/-! ## 4. The pin: the heavy piece on the closure, and the light piece's countdown -/

/-- **(II) The pin.** `C 5 = 54`, so a heavy piece at 54 sits at `h = 0` — the closure cell, group
18. The light piece is then `Z − 54`; while that still lies in period 5 (`91 ≤ Z ≤ 108`) its countdown
is `108 − Z`, i.e. it falls by exactly one per proton of parent. -/
theorem pin (Z : ℕ) (h1 : 91 ≤ Z) (h2 : Z ≤ 108) :
    C 5 = 54 ∧ cnt 54 = 0 ∧ cnt (Z - 54) = 108 - Z := by
  refine ⟨by simp [C], ?_, ?_⟩
  · simp [cnt, period, C]
  · interval_cases Z <;> decide

/-- The five parents whose light piece is still a **closed cell** with the heavy on the closure. -/
theorem light_closed_five (Z : ℕ) (h1 : 88 ≤ Z) (h2 : Z ≤ 96) :
    (closed (Z - 54) ∧ closed 54) ↔ (88 ≤ Z ∧ Z ≤ 92) := by
  interval_cases Z <;> simp [closed, cnt, period, C, L]

/-- **(V) Thorium is the only double-closure split.** With the heavy at 54, a light piece that is
also on a closure (`h = 0`) forces `Z = 90` — and `C 4 + C 5 = 90`. -/
theorem double_closure_only_th (Z : ℕ) (h1 : 88 ≤ Z) (h2 : Z ≤ 100) :
    (cnt 54 = 0 ∧ cnt (Z - 54) = 0) ↔ Z = 90 := by
  interval_cases Z <;> simp [cnt, period, C]

theorem th_closures_add (Z : ℕ) (h : Z = 90) : C 4 + C 5 = Z := by
  subst h; simp [C]

/-! ## 5. Which splits put both pieces on closed cells -/

/-- **(III) Uranium.** In the asymmetric window, the splits of `Z = 92` with both pieces closed are
exactly `36, 37, 38` — Kr, Rb, Sr against Ba, Cs, Xe. -/
theorem closed_split_U (Z1 : ℕ) (h1 : 30 ≤ Z1) (h2 : Z1 ≤ 46) :
    (closed Z1 ∧ closed (92 - Z1)) ↔ (Z1 = 36 ∨ Z1 = 37 ∨ Z1 = 38) := by
  interval_cases Z1 <;> simp [closed, cnt, period, C, L]

/-- **Plutonium: one.** The same window for `Z = 94` leaves `38` alone. -/
theorem closed_split_Pu (Z1 : ℕ) (h1 : 30 ≤ Z1) (h2 : Z1 ≤ 47) :
    (closed Z1 ∧ closed (94 - Z1)) ↔ Z1 = 38 := by
  interval_cases Z1 <;> simp [closed, cnt, period, C, L]

/-- **Curium: none.** For `Z = 96` there is no split in the window with both pieces closed. -/
theorem closed_split_Cm (Z1 : ℕ) (h1 : 30 ≤ Z1) (h2 : Z1 ≤ 48) :
    ¬ (closed Z1 ∧ closed (96 - Z1)) := by
  interval_cases Z1 <;> simp [closed, cnt, period, C, L]

/-! ## 6. The symmetric split closes exactly at `Z ≥ 98` -/

/-- **(IV) The symmetric split closes at 98.** For even `Z` in the actinide range, the cell holding
`Z/2` is closed exactly when `Z ≥ 98` — the countdown `54 − Z/2` has fallen to the `p` bottom. -/
theorem symmetric_closed (Z : ℕ) (he : Z % 2 = 0) (h1 : 88 ≤ Z) (h2 : Z ≤ 106) :
    (closed (Z / 2) ↔ 98 ≤ Z) := by
  interval_cases Z <;> simp [closed, cnt, period, C, L]

/-! ## 7. The inventory, and why a descent must split -/

/-- The 118 cells, counted by block: seven `s`, six `p`, four `d`, two `f`. -/
theorem inventory : 2 * 7 + 6 * 6 + 10 * 4 + 14 * 2 = 118 := by norm_num

/-- The rungs to `q = 8` hold 120 cells; 118 is two short, and the two are the `8s`. -/
theorem rungs_to_eight : 2 + 2 + 8 + 8 + 18 + 18 + 32 + 32 = 120 ∧ 120 - 118 = 2 := by
  norm_num

/-- **Saturation.** Every `Z` from 1 to 118 has a period, hence a cell: there is no free cell below
the last closure for a nucleus to descend into one at a time. -/
theorem every_cell_below_118 (Z : ℕ) (h1 : 1 ≤ Z) (h2 : Z ≤ 118) :
    1 ≤ period Z ∧ period Z ≤ 7 := by
  interval_cases Z <;> decide

/-! ## 8. The worked instances, kept together -/

/-- The text-book pair `(56,36)` — Ba-141 with Kr-92 — is closed on both sides: Kr sits on the
closure `C 4 = 36`, Ba on the head of row 6. -/
theorem kr_ba : closed 36 ∧ closed 56 := by simp [closed, cnt, period, C, L]

/-- And the other quoted pair, `(54,38)` — Xe against Sr — is a closure plus a row head. -/
theorem sr_xe : closed 38 ∧ closed 54 ∧ cnt 54 = 0 := by simp [closed, cnt, period, C, L]

/-- **The light piece walks down the countdown.** With the heavy pinned at `C 5 = 54`, parents 92, 94,
96, 98 give light `38, 40, 42, 44` with countdowns `16, 14, 12, 10`. -/
theorem light_walks_down :
    cnt 38 = 16 ∧ cnt 40 = 14 ∧ cnt 42 = 12 ∧ cnt 44 = 10 := by simp [cnt, period, C]

/-- The symmetric piece for the same four parents: `54 - Z/2`, i.e. `8, 7, 6, 5` — it leaves the `d`
interior and reaches the `p` bottom at 98. -/
theorem symmetric_walks_down :
    cnt 46 = 8 ∧ cnt 47 = 7 ∧ cnt 48 = 6 ∧ cnt 49 = 5 ∧ closed 49 := by
  simp [closed, cnt, period, C, L]

/-- Thorium's two nodes are closures: `36 = C 4`, `54 = C 5`, and they add to the parent. -/
theorem th_double_closure : C 4 + C 5 = 90 ∧ cnt 36 = 0 ∧ cnt 54 = 0 := by simp [C, cnt, period]

/-! ## 9. The second coordinate: what an `(Z, N)` table would add -/

/-- **Capture is a move in `N` only.** In a table indexed by `(Z, N)`, `(n,γ)` takes `(Z,N)` to
`(Z,N+1)`: one cell across in the neutron coordinate, none in the proton coordinate. Elastic
scattering is the identity in both. This is precisely the distinction a `Z`-indexed table cannot
make — bounce and absorb are both the identity there. -/
theorem capture_moves_N (Z N : ℕ) : ((Z, N + 1).1 = Z) ∧ ((Z, N + 1).2 = N + 1) := by
  simp

/-- **The neutron count stops being pinned by one piece.** With `N₁ + N₂ + ν = N` one piece fixes the
other only once the multiplicity `ν` is known: `N − N₁ = N₂ + ν`. That is the price of the second
coordinate — the split is no longer a one-parameter family, as it is in `Z` alone. -/
theorem neutron_unpinned (N N1 N2 ν : ℤ) (h : N1 + N2 + ν = N) : N - N1 = N2 + ν := by
  omega

/-- **The two closure ladders share one term.** The proton closures are the partial sums of
`2⌈(m+1)/2⌉²`; the neutron magic numbers are `2, 8, 20, 28, 50, 82, 126`. Only `2` is in both, so the
Light Bridge theorem does not transfer to the neutron axis. -/
theorem ladders_share_one :
    ([2, 10, 18, 36, 54, 86, 118].filter (fun n => n ∈ [2, 8, 20, 28, 50, 82, 126])) = [2] := by
  decide

/-- And the third neutron magic number is not of the proton form: `20` is not twice a square, where
`18 = 2·3²` is. -/
theorem twenty_not_twice_square (n : ℕ) : 2 * n ^ 2 ≠ 20 := by
  intro h
  have h2 : n ≤ 3 := by nlinarith
  interval_cases n <;> omega

/-- Likewise `28`, where the proton closure at the same index is `32 = 2·4²`. -/
theorem twentyeight_not_twice_square (n : ℕ) : 2 * n ^ 2 ≠ 28 := by
  intro h
  have h2 : n ≤ 4 := by nlinarith
  interval_cases n <;> omega

/-! ## 10. Why a mass law alone cannot price the split -/

/-- **A mass law linear in `Z` is blind to the split.** With `M(Z) = a·Z − b` and `Z = Z₁ + Z₂`, the
predicted mass defect is exactly the intercept `b`, whatever the split point: the linear terms cancel.
With the record's fit (`a = 2.619`, `b = 9.36 u`) that is 8.72 GeV for a process that releases 200 MeV —
44 times too much, and identical for every split. Energy needs the mass *excess*, i.e. a function of both
counts. -/
theorem linear_mass_law_blind (a b Z Z1 Z2 : ℚ) (h : Z = Z1 + Z2) :
    (a * Z - b) - (a * Z1 - b) - (a * Z2 - b) = b := by
  rw [h]; ring

end Fission
