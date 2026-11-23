/-
VOTKP v1.2, negative control 41 (§18): zero normalized permutation entropy does not rule
out a transposition defect.

At embedding dimension 2 the ordinal pattern of a pair `(x i, x (i+τ))` is "rise" or "fall",
and the normalized permutation entropy is zero exactly when one pattern occurs throughout.
The clean ladder `1,2,3,4,5,6` and the ladder with one adjacent transposition `1,2,4,3,5,6`
both show a single pattern at delay 2, so zero entropy at that delay cannot tell them apart;
delay 1 does.
-/

namespace VOTKP.Ordinal

/-- The delay-`τ` rise pattern of a list: `true` where `x i < x (i+τ)`. -/
def rises (τ : Nat) (xs : List Nat) : List Bool :=
  (List.range (xs.length - τ)).map fun i => decide (xs.getD i 0 < xs.getD (i + τ) 0)

/-- Zero normalized permutation entropy at dimension 2: one ordinal pattern throughout. -/
def singlePattern (τ : Nat) (xs : List Nat) : Bool :=
  (rises τ xs).all id || (rises τ xs).all not

/-- The clean ladder. -/
def clean : List Nat := [1, 2, 3, 4, 5, 6]

/-- The same ladder with one adjacent transposition. -/
def swapped : List Nat := [1, 2, 4, 3, 5, 6]

/-- The two ladders differ: the second carries a transposition defect. -/
theorem swapped_ne_clean : swapped ≠ clean := by decide

/-- At delay 2 the clean ladder rises throughout. -/
theorem clean_single_pattern : singlePattern 2 clean = true := by decide

/-- At delay 2 the transposed ladder also rises throughout. -/
theorem swapped_single_pattern : singlePattern 2 swapped = true := by decide

/-- At delay 1 the transposition shows: the pattern is no longer single. -/
theorem delay_one_sees_swap : singlePattern 1 swapped = false := by decide

/-- **Negative control 41.** Zero normalized permutation entropy (delay 2) holds for both a
clean ladder and one with a transposition defect, so it does not identify the defect. -/
theorem zero_entropy_not_identifying :
    singlePattern 2 clean = true ∧ singlePattern 2 swapped = true ∧ swapped ≠ clean :=
  ⟨clean_single_pattern, swapped_single_pattern, swapped_ne_clean⟩

end VOTKP.Ordinal
