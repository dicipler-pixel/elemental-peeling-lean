import Mathlib

/-!
# The colour wheel: orbits of the units are the divisor classes

Direction C4 of the fourth round.  `units_orbit_eq_setOf_gcd` proves, for every `W > 0`, that the
orbit of `x` under `(ZMod W)ˣ` is exactly the set of residues with the same gcd with `W`; at `W = 10`
the primaries, secondaries, grey and base are enumerated (`card_units_zmod10`, `orbit_two_zmod10`,
`orbit_five_zmod10`, `orbit_zero_zmod10`) and `cyclotomic_ten_eq_cyclotomic_five_comp_neg` gives
`Φ₁₀ = Φ₅.comp (-X)`.  Two corrections are recorded: the doubling kernel on `Z/10` is `{0, 5}`, not
`{5}` (`doubling_kernel_zmod10`, `doubling_kernel_zmod10_not_singleton`), and the `W = 2p` criterion
fails both ways (`fourteen_counterexample_to_two_mul_odd_prime`,
`five_counterexample_to_two_mul_odd_prime`), with `card_units_eq_four_iff_of_le_thirty` giving the
true list `W ∈ {5, 8, 10, 12}`.

Written in the fourth parallel formalization round (swarm `smws625cs`, direction m4),
recompiled and reviewed here; namespace and header added, `#print axioms` lines removed.
-/

open scoped BigOperators

namespace ElementalPeeling.LoopWall.ColourWheel

open Polynomial

/-- Multiplication by a unit followed by reduction modulo `W` does not change
`gcd (·, W)`. -/
theorem gcd_val_unit_smul {W : ℕ} [NeZero W] (u : (ZMod W)ˣ) (x : ZMod W) :
    Nat.gcd ((u • x : ZMod W).val) W = Nat.gcd x.val W := by
  have hcast : (((u • x : ZMod W).val : ℕ) : ZMod W) =
      (((u : ZMod W).val * x.val : ℕ) : ZMod W) := by
    simp only [ZMod.natCast_zmod_val, Nat.cast_mul]
    rfl
  have hmod : (u • x : ZMod W).val ≡ (u : ZMod W).val * x.val [MOD W] :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mp hcast
  exact hmod.gcd_eq.trans
    (Nat.Coprime.gcd_mul_left_cancel x.val (ZMod.val_coe_unit_coprime u))

/-- If a residue is a unit times a natural divisor `d` of the modulus, then
that divisor is its gcd with the modulus. -/
theorem gcd_val_of_unit_mul_natCast {W d : ℕ} [NeZero W] (hd : d ∣ W)
    (u : (ZMod W)ˣ) (x : ZMod W) (hx : x = (u : ZMod W) * (d : ZMod W)) :
    Nat.gcd x.val W = d := by
  have hcast : ((x.val : ℕ) : ZMod W) =
      (((u : ZMod W).val * d : ℕ) : ZMod W) := by
    rw [ZMod.natCast_zmod_val, hx, Nat.cast_mul, ZMod.natCast_zmod_val]
  have hmod : x.val ≡ (u : ZMod W).val * d [MOD W] :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mp hcast
  exact hmod.gcd_eq.trans
    (Nat.gcd_mul_of_coprime_of_dvd (ZMod.val_coe_unit_coprime u) hd)

/-- Canonical unit-times-gcd decomposition of a residue. -/
theorem exists_unit_smul_gcd {W : ℕ} [NeZero W] (x : ZMod W) :
    ∃ u : (ZMod W)ˣ, u • (Nat.gcd x.val W : ZMod W) = x := by
  obtain ⟨d, hd, u, hu, hx⟩ := ZMod.eq_unit_mul_divisor x
  let v : (ZMod W)ˣ := hu.unit
  have hv : (v : ZMod W) = u := IsUnit.unit_spec hu
  have hx' : x = (v : ZMod W) * (d : ZMod W) := by simpa [hv] using hx
  have hg : Nat.gcd x.val W = d := gcd_val_of_unit_mul_natCast hd v x hx'
  refine ⟨v, ?_⟩
  change (v : ZMod W) * (Nat.gcd x.val W : ZMod W) = x
  rw [hg]
  exact hx'.symm

/-- Two residues modulo a positive `W` lie in the same orbit under multiplication
by units exactly when they have the same gcd with `W`. -/
theorem units_orbit_eq_setOf_gcd {W : ℕ} (hW : 0 < W) (x : ZMod W) :
    MulAction.orbit (ZMod W)ˣ x = {y | Nat.gcd y.val W = Nat.gcd x.val W} := by
  let : NeZero W := ⟨Nat.ne_of_gt hW⟩
  ext y
  constructor
  · rintro ⟨u, rfl⟩
    exact gcd_val_unit_smul u x
  · intro hy
    change Nat.gcd y.val W = Nat.gcd x.val W at hy
    obtain ⟨u, hu⟩ := exists_unit_smul_gcd x
    obtain ⟨v, hv⟩ := exists_unit_smul_gcd y
    refine ⟨v * u⁻¹, ?_⟩
    have hux : u⁻¹ • x = (Nat.gcd x.val W : ZMod W) := by
      calc
        u⁻¹ • x = u⁻¹ • (u • (Nat.gcd x.val W : ZMod W)) :=
          congrArg (fun z : ZMod W => u⁻¹ • z) hu.symm
        _ = (Nat.gcd x.val W : ZMod W) := inv_smul_smul _ _
    calc
      (v * u⁻¹) • x = v • (u⁻¹ • x) := mul_smul _ _ _
      _ = v • (Nat.gcd x.val W : ZMod W) := by rw [hux]
      _ = v • (Nat.gcd y.val W : ZMod W) := by rw [hy]
      _ = y := hv

/-- Membership formulation of the orbit classification. -/
theorem mem_units_orbit_iff_gcd {W : ℕ} (hW : 0 < W) (x y : ZMod W) :
    y ∈ MulAction.orbit (ZMod W)ˣ x ↔ Nat.gcd y.val W = Nat.gcd x.val W := by
  rw [units_orbit_eq_setOf_gcd hW]
  rfl

/-- The four units modulo 10, enumerated by their residues. -/
theorem units_zmod10_image :
    Finset.univ.image (fun u : (ZMod 10)ˣ => (u : ZMod 10)) = {1, 3, 7, 9} := by
  decide

theorem card_units_zmod10 : Fintype.card (ZMod 10)ˣ = 4 := by decide

/-- The four secondaries modulo 10 are the unit orbit of 2. -/
theorem orbit_two_zmod10 :
    MulAction.orbit (ZMod 10)ˣ (2 : ZMod 10) = {2, 4, 6, 8} := by
  ext y
  rw [mem_units_orbit_iff_gcd (by norm_num : 0 < 10)]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  change Nat.gcd (show Fin 10 from y).val 10 = 2 ↔
    (show Fin 10 from y) = 2 ∨ (show Fin 10 from y) = 4 ∨
      (show Fin 10 from y) = 6 ∨ (show Fin 10 from y) = 8
  fin_cases y <;> decide

/-- The special primary 5 is fixed by every unit modulo 10. -/
theorem orbit_five_zmod10 :
    MulAction.orbit (ZMod 10)ˣ (5 : ZMod 10) = {5} := by
  ext y
  rw [mem_units_orbit_iff_gcd (by norm_num : 0 < 10)]
  simp only [Set.mem_singleton_iff]
  change Nat.gcd (show Fin 10 from y).val 10 = 5 ↔ (show Fin 10 from y) = 5
  fin_cases y <;> decide

theorem five_add_five_zmod10 : (5 : ZMod 10) + 5 = 0 := by decide

/-- The zero residue is a singleton unit orbit. -/
theorem orbit_zero_zmod10 :
    MulAction.orbit (ZMod 10)ˣ (0 : ZMod 10) = {0} := by
  ext y
  rw [mem_units_orbit_iff_gcd (by norm_num : 0 < 10)]
  simp only [Set.mem_singleton_iff]
  change Nat.gcd (show Fin 10 from y).val 10 = 10 ↔ (show Fin 10 from y) = 0
  fin_cases y <;> decide

/-- The claimed singleton kernel is false: zero is also killed by doubling. -/
theorem doubling_kernel_zmod10_not_singleton :
    {x : ZMod 10 | 2 * x = 0} ≠ {5} := by
  intro h
  have h0 : (0 : ZMod 10) ∈ {x : ZMod 10 | 2 * x = 0} := by
    change 2 * (0 : ZMod 10) = 0
    simp
  rw [h] at h0
  have h05 : (0 : ZMod 10) = 5 := by simpa using h0
  exact (by decide : (0 : ZMod 10) ≠ 5) h05

/-- Corrected form: the kernel of doubling modulo 10 is exactly `{0, 5}`. -/
theorem doubling_kernel_zmod10 :
    {x : ZMod 10 | 2 * x = 0} = {0, 5} := by
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  change 2 * (show Fin 10 from x) = 0 ↔
    (show Fin 10 from x) = 0 ∨ (show Fin 10 from x) = 5
  fin_cases x <;> decide

/-- `Φ₁₀(X) = Φ₅(-X)`.  Polynomial composition is written with `comp`;
the function-composition symbol in the informal statement is not the
corresponding Lean operation on polynomials; the substitution polynomial is
`-X` itself, not `C (-X)`. -/
theorem cyclotomic_ten_eq_cyclotomic_five_comp_neg :
    cyclotomic 10 ℤ = (cyclotomic 5 ℤ).comp (-X) := by
  let : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  apply mul_right_cancel₀ (cyclotomic_ne_zero 5 ℤ)
  rw [show 10 = 5 * 2 by norm_num,
    ← cyclotomic_expand_eq_cyclotomic_mul Nat.prime_two (by norm_num)]
  simp [cyclotomic_prime, Finset.sum_range_succ]
  ring

/-- Exact enumeration, through modulus 30, of the colour wheels having four
units.  `NeZero W` is the typeclass encoding of the hypothesis `0 < W`. -/
theorem card_units_eq_four_iff_of_le_thirty {W : ℕ} [NeZero W] (hW30 : W ≤ 30) :
    Fintype.card (ZMod W)ˣ = 4 ↔ W = 5 ∨ W = 8 ∨ W = 10 ∨ W = 12 := by
  rw [ZMod.card_units_eq_totient]
  have hW : 0 < W := NeZero.pos W
  interval_cases W <;> decide

/-- The proposed `2p` condition is not sufficient: 14 has the required form
with the odd prime 7, but its unit group has six elements rather than four. -/
theorem fourteen_counterexample_to_two_mul_odd_prime :
    Nat.Prime 7 ∧ Odd 7 ∧ 14 = 2 * 7 ∧ Fintype.card (ZMod 14)ˣ ≠ 4 := by
  decide

/-- The proposed `2p` condition is not necessary either: 5 has four units but
is not twice an odd prime. -/
theorem five_counterexample_to_two_mul_odd_prime :
    Fintype.card (ZMod 5)ˣ = 4 ∧
      ¬ ∃ p : ℕ, p.Prime ∧ Odd p ∧ 5 = 2 * p := by
  constructor
  · decide
  · rintro ⟨p, hp, ho, heq⟩
    rcases ho with ⟨k, hk⟩
    omega

/-- Thus “four units iff `W = 2*p` for an odd prime `p`” is false.
The hypothesis `0 < W` is represented by the `NeZero W` binder. -/
theorem two_mul_odd_prime_criterion_false :
    ¬ (∀ W : ℕ, ∀ [NeZero W],
      (Fintype.card (ZMod W)ˣ = 4 ↔
        ∃ p : ℕ, p.Prime ∧ Odd p ∧ W = 2 * p)) := by
  intro h
  have hc := (h 14).mpr ⟨7, by decide, ⟨3, by decide⟩, by decide⟩
  exact (by decide : Fintype.card (ZMod 14)ˣ ≠ 4) hc

end ElementalPeeling.LoopWall.ColourWheel
