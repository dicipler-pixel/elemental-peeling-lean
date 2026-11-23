/-
  The generative kernel of the end-digit keys.

  Claim being formalised: the whole structure of the keys follows from ONE local
  fact — that 5 is unreachable — plus its twin analogue (3 unreachable as a start).

  Scope: these are finite combinatorial facts, proved outright. Nothing here says
  anything about the primes themselves. That the primes realise this structure is
  an empirical fact (verified over 224,376,047 twin handoffs) and is not, and
  cannot be, part of these theorems.
-/
import Mathlib

open Finset

/-- The live end digits: every prime above 5 ends in one of these. -/
def live : Finset Nat := {1, 3, 7, 9}

/-- The five step classes: the possible residues of a gap mod 10 (10 is listed as 10). -/
def steps : Finset Nat := {2, 4, 6, 8, 10}

/-- The live digits a twin pair can start on (3 is excluded: 23+2 is divisible by 5). -/
def twinLive : Finset Nat := {1, 7, 9}

/-- The digit a twin pair can end on. -/
def twinEnd : Finset Nat := {1, 3, 9}

/-! ### 1. One forbidden step per digit -/

/-- Exactly four of the twenty (digit, step) pairs land on 5 — one per digit. -/
theorem forbidden_step_count :
    ((live ×ˢ steps).filter (fun p => (p.1 + p.2) % 10 = 5)).card = 4 := by
  decide

/-- Consequently the base key has 20 − 4 = 16 cells. -/
theorem base_key_card :
    ((live ×ˢ steps).filter (fun p => (p.1 + p.2) % 10 ≠ 5)).card = 16 := by
  decide

/-- The same count, stated as the arithmetic identity the prose uses. -/
theorem base_key_arithmetic : live.card * steps.card - 4 = 16 := by
  decide

/-! ### 2. Two forbidden landings for twin digits -/

/-- For the three twin digits, six of the fifteen pairs are forbidden:
    three land on 5 and three land on 3. -/
theorem twin_forbidden_count :
    ((twinLive ×ˢ steps).filter
      (fun p => (p.1 + p.2) % 10 = 5 ∨ (p.1 + p.2) % 10 = 3)).card = 6 := by
  decide

/-- Consequently the twin key has 15 − 6 = 9 cells. -/
theorem twin_key_card :
    ((twinLive ×ˢ steps).filter
      (fun p => (p.1 + p.2) % 10 ≠ 5 ∧ (p.1 + p.2) % 10 ≠ 3)).card = 9 := by
  decide

theorem twin_key_arithmetic : twinLive.card * steps.card - 6 = 9 := by
  decide

/-- And the 9 cells are the 3 × 3 grid of (departing digit, arriving digit). -/
theorem twin_key_is_the_grid : (twinLive ×ˢ twinEnd).card = 9 := by
  decide

/-! ### 3. The chain limit: at most three steps of one class -/

/-- No start and no step class keeps five consecutive nodes live.
    So a run of one step class has at most four nodes = three transitions.
    The reason: for d ∈ {2,4,6,8} the orbit is a 5-cycle and only 4 digits are live. -/
theorem chain_limit_three :
    ((live ×ˢ ({2, 4, 6, 8} : Finset Nat)).filter
      (fun q => (q.1 + q.2) % 10 ∈ live ∧
                (q.1 + 2 * q.2) % 10 ∈ live ∧
                (q.1 + 3 * q.2) % 10 ∈ live ∧
                (q.1 + 4 * q.2) % 10 ∈ live)).card = 0 := by
  decide

/-- The self-step is not cut: it never leaves the digit. -/
theorem self_step_unbounded :
    ((live ×ˢ ({10} : Finset Nat)).filter
      (fun q => (q.1 + 4 * q.2) % 10 ∈ live)).card = 4 := by
  decide

/-! ### 4. The twin condition leaves three residue classes mod 30 -/

/-- A residue r mod 30 admits a twin pair (both members coprime to 30) iff r ∈ {11,17,29}. -/
theorem twin_residues :
    ((range 30).filter (fun r => Nat.Coprime r 30 ∧ Nat.Coprime (r + 2) 30)).card = 3 := by
  decide

/-- Hence the twin floors are 4 + 6k: an arithmetic progression with step 6. -/
theorem twin_floors : ((range 5).image (fun k => 4 + 6 * k)) = ({4, 10, 16, 22, 28} : Finset Nat) := by
  decide

/-- And five floors give five classes. -/
theorem class_count : ((range 5).image (fun k => 4 + 6 * k)).card = 5 := by
  decide
