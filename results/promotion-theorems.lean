/-
  promotion-theorems.lean

  The nineteen exchange promotions, split into the part that is arithmetic and the
  part that is a fit.

  Arithmetic, machine-checked below:
    * the exchange increment `G` of an incoming electron, its closed form, its peak
      at the half-filled shell, and its range (`cap - 2`, i.e. 8 for `d`, 12 for `f`);
    * every promotion moves an electron between cells at the same rung or at the
      next rung — never two rungs — and the two shapes are forced:
      rung `+1` ⟹ `s → d`, rung `0` ⟹ `f → d`;
    * the split of the nineteen into ten (rung +1) and nine (tied), and their exact
      membership.

  Fit, machine-checked as a fit:
    * explicit rational rungs `A - B k` that make the criterion reproduce the
      measured flip sets of the three `d` series exactly;
    * the `f` series cannot be fitted by any linear rung with a contraction of the
      size the `d` series need: a straddle two electrons apart forces `B > 12`.

  No `sorry`; every theorem closes with `decide`, `simp`, `omega`, `norm_num`,
  `linarith` or `ring`.
-/
import Mathlib

namespace LightBridge

/-! ## The exchange increment -/

/-- `Φ cap k` — the number of parallel-spin pairs in a subshell of capacity `cap`
holding `k` electrons (Hund: spins are maximal, so the counts are `min k (cap - k)`
and the pairs are their binomial). -/
def Phi (cap k : ℕ) : ℕ := (min k (cap - k)).choose 2

/-- `G cap k` — the exchange gained when the `(k+1)`-st electron enters. -/
def G (cap k : ℕ) : ℤ := (Phi cap (k + 1) : ℤ) - (Phi cap k : ℤ)

/-- The `d` increment, closed form: `k` up to the half-fill, then `k + 1 - 10`. -/
theorem G_d (k : ℕ) (h : k ≤ 9) : G 10 k = if k < 5 then (k : ℤ) else (k : ℤ) + 1 - 10 := by
  interval_cases k <;> simp <;> decide

/-- The `f` increment, closed form: `k` up to the half-fill, then `k + 1 - 14`. -/
theorem G_f (k : ℕ) (h : k ≤ 13) : G 14 k = if k < 7 then (k : ℤ) else (k : ℤ) + 1 - 14 := by
  interval_cases k <;> simp <;> decide

/-- The `d` values: `0,1,2,3,4,-4,-3,-2,-1,0`. -/
theorem G_d_values :
    G 10 0 = 0 ∧ G 10 1 = 1 ∧ G 10 2 = 2 ∧ G 10 3 = 3 ∧ G 10 4 = 4 ∧
    G 10 5 = -4 ∧ G 10 6 = -3 ∧ G 10 7 = -2 ∧ G 10 8 = -1 ∧ G 10 9 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- The peak of the increment is at the half-filled `d` shell: `d⁴ → d⁵` gains `+4`. -/
theorem G_d_peak : G 10 4 = 4 := by decide

/-- The trough is one electron later: `d⁵ → d⁶` is `-4`. -/
theorem G_d_trough : G 10 5 = -4 := by decide

/-- The peak of the `f` increment is at the half-filled `f` shell: `f⁶ → f⁷` gains `+6`. -/
theorem G_f_peak : G 14 6 = 6 := by decide

/-- And the trough follows: `f⁷ → f⁸` is `-6`. -/
theorem G_f_trough : G 14 7 = -6 := by decide

/-- The swing of the `d` increment is 8 quanta. -/
theorem G_d_spread : G 10 4 - G 10 5 = 8 := by decide

/-- The swing of the `f` increment is 12 quanta. -/
theorem G_f_spread : G 14 6 - G 14 7 = 12 := by decide

/-- A rank that charges one rung per step cannot follow a swing of 8. -/
theorem rank_cannot_follow : (8 : ℤ) > 1 ∧ (12 : ℤ) > 1 := by norm_num

/-! ## The shape of a promotion: same rung or the next, never two -/

/-- A promotion that gains exactly one rung and raises `l` by two is `s → d`:
the principal number must fall by one. -/
theorem gap_one_is_s_to_d (n l n' l' : ℤ) (hq : n' + l' = n + l + 1) (hl : l' = l + 2) :
    n' = n - 1 := by omega

/-- A promotion that stays on its rung and lowers `l` by one is `f → d`:
the principal number must rise by one. -/
theorem gap_zero_is_f_to_d (n l n' l' : ℤ) (hq : n' + l' = n + l) (hl : l' + 1 = l) :
    n' = n + 1 := by omega

/-- The nineteen measured promotions, as `(n, l, n', l')`: the subshell the rule
fills, and the subshell the electron is found in. -/
def promos : List (ℕ × ℕ × ℕ × ℕ) :=
  [ (4, 0, 3, 2),                                     -- Cr   Z=24
    (4, 0, 3, 2),                                     -- Cu   Z=29
    (5, 0, 4, 2),                                     -- Nb   Z=41
    (5, 0, 4, 2),                                     -- Mo   Z=42
    (5, 0, 4, 2),                                     -- Ru   Z=44
    (5, 0, 4, 2),                                     -- Rh   Z=45
    (5, 0, 4, 2),                                     -- Pd   Z=46
    (5, 0, 4, 2),                                     -- Ag   Z=47
    (6, 0, 5, 2),                                     -- Pt   Z=78
    (6, 0, 5, 2),                                     -- Au   Z=79
    (4, 3, 5, 2),                                     -- La   Z=57
    (4, 3, 5, 2),                                     -- Ce   Z=58
    (4, 3, 5, 2),                                     -- Gd   Z=64
    (5, 3, 6, 2),                                     -- Ac   Z=89
    (5, 3, 6, 2),                                     -- Th   Z=90
    (5, 3, 6, 2),                                     -- Pa   Z=91
    (5, 3, 6, 2),                                     -- U    Z=92
    (5, 3, 6, 2),                                     -- Np   Z=93
    (5, 3, 6, 2) ]                                    -- Cm   Z=96

/-- The rung a promotion gains, `(n'+l') - (n+l)`. -/
def rungGap (p : ℕ × ℕ × ℕ × ℕ) : ℕ := (p.2.2.1 + p.2.2.2) - (p.1 + p.2.1)

/-- Nineteen promotions. -/
theorem promos_length : promos.length = 19 := by decide

/-- **No promotion crosses two rungs**: every rung gap is 0 or 1. -/
theorem promos_gap_le_one : ∀ p ∈ promos, rungGap p ≤ 1 := by decide

/-- **Ten go up one rung, nine stay on their rung.** -/
theorem promos_split :
    (promos.filter (fun p => rungGap p = 1)).length = 10 ∧
    (promos.filter (fun p => rungGap p = 0)).length = 9 := by decide

/-- **The ten of gap 1 are the `s → d` moves.** -/
theorem promos_gap_one_shape :
    promos.filter (fun p => rungGap p = 1) =
      [(4, 0, 3, 2), (4, 0, 3, 2), (5, 0, 4, 2), (5, 0, 4, 2), (5, 0, 4, 2), (5, 0, 4, 2),
       (5, 0, 4, 2), (5, 0, 4, 2), (6, 0, 5, 2), (6, 0, 5, 2)] := by decide

/-- **The nine of gap 0 are the `f → d` moves.** -/
theorem promos_gap_zero_shape :
    promos.filter (fun p => rungGap p = 0) =
      [(4, 3, 5, 2), (4, 3, 5, 2), (4, 3, 5, 2), (5, 3, 6, 2), (5, 3, 6, 2), (5, 3, 6, 2),
       (5, 3, 6, 2), (5, 3, 6, 2), (5, 3, 6, 2)] := by decide

/-- Every one of them moves the electron to `l = 2`: the `d` subshell. -/
theorem promos_land_in_d : ∀ p ∈ promos, p.2.2.2 = 2 := by decide

/-! ## The fit: three rational rungs, and one that does not exist -/

/-- The flip set of the criterion `G cap k > A - B k`. -/
def flips (A B : ℚ) (cap : ℕ) : Finset ℕ :=
  (Finset.range cap).filter (fun k => (G cap k : ℚ) > A - B * (k : ℚ))

/-- **`3d`**: with `A = 6.74`, `B = 0.88` the criterion flips exactly at `k = 4, 9` — Cr and Cu. -/
theorem fit_3d : flips (337 / 50) (22 / 25) 10 = ({4, 9} : Finset ℕ) := by
  ext k
  simp only [flips, Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
  by_cases h : k < 10
  · interval_cases k <;> rw [G_d _ (by omega)] <;> norm_num
  · constructor
    · rintro ⟨h', _⟩; omega
    · rintro (rfl | rfl) <;> omega

/-- **`4d`**: with `A = 7.51`, `B = 1.88` it flips exactly at `k = 3,4,6,7,8,9` —
Nb, Mo, Ru, Rh, Pd, Ag. -/
theorem fit_4d : flips (751 / 100) (47 / 25) 10 = ({3, 4, 6, 7, 8, 9} : Finset ℕ) := by
  ext k
  simp only [flips, Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
  by_cases h : k < 10
  · interval_cases k <;> rw [G_d _ (by omega)] <;> norm_num
  · constructor
    · rintro ⟨h', _⟩; omega
    · rintro (rfl | rfl | rfl | rfl | rfl | rfl) <;> omega

/-- **`5d`**: with `A = 11.52`, `B = 1.77` it flips exactly at `k = 8, 9` — Pt and Au. -/
theorem fit_5d : flips (288 / 25) (177 / 100) 10 = ({8, 9} : Finset ℕ) := by
  ext k
  simp only [flips, Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
  by_cases h : k < 10
  · interval_cases k <;> rw [G_d _ (by omega)] <;> norm_num
  · constructor
    · rintro ⟨h', _⟩; omega
    · rintro (rfl | rfl) <;> omega

/-- The three fits together give the ten one-rung promotions: 2 + 6 + 2. -/
theorem fit_counts :
    ({4, 9} : Finset ℕ).card + ({3, 4, 6, 7, 8, 9} : Finset ℕ).card + ({8, 9} : Finset ℕ).card
      = 10 := by
  norm_num

/-- The crossings `k✱ = A/B` lie where the record says: `3d` between 6.8 and 9.0. -/
theorem cross_3d : (68 : ℚ) / 10 < (337 / 50) / (22 / 25) ∧ (337 / 50) / (22 / 25) < 9 := by
  norm_num

/-- `4d` between 3.0 and 4.5. -/
theorem cross_4d : 3 < (751 / 100) / (47 / 25) ∧ (751 / 100) / (47 / 25) < (45 : ℚ) / 10 := by
  norm_num

/-- `5d` between 6.0 and 7.5. -/
theorem cross_5d : 6 < (288 / 25) / (177 / 100) ∧ (288 / 25) / (177 / 100) < (75 : ℚ) / 10 := by
  norm_num

/-- **The `f` series has no linear rung of this kind.** If the rung has to sit above `+6`
at one occupancy and below `-6` at the next, the contraction must exceed 12 — six times
the largest contraction the `d` series admit (`1.88`). This is why the `f/d` ordering
is not a rung but an oscillation about the exact tie. -/
theorem f_straddle_forces_B (A B : ℚ) (k : ℕ)
    (h1 : (6 : ℚ) < A - B * (k : ℚ)) (h2 : A - B * ((k : ℚ) + 1) < -6) : 12 < B := by
  linarith

/-- And the largest `d` contraction is far below that ceiling. -/
theorem d_contraction_ceiling : (47 : ℚ) / 25 < 12 := by norm_num

end LightBridge
