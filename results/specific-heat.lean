/-
  specific-heat.lean

  The heat capacity of a solid, in the three readings the density triangle gives it, and the one
  number that converts the solid side to the prime side. Every theorem here is exact algebra or a
  statement about the table's own capacities; the two constants (3R and 1/(2C₂)) are *measured*, and
  the file says so where it uses them.

  The three capacities this record deals with, and which one each theorem is about:

    (L1) COUNT capacity      — the Light Bridge's cell capacity `L m = 2n²`, `w l = 2(2l+1)`.
                               A count of slots. Even. Cannot be an energy per kelvin.
    (L2) MOLAR heat capacity — `C = 3R` (Dulong–Petit). Energy per kelvin per mole. Universal.
    (L3) SPECIFIC heat       — `c = C/M` per gram, `c = ΣT/Σt²` per log² on the prime side.
                               Not universal: it moves with the unit.

  Proved below:
    * the density triangle in all three forms, and its heat twin `C = c·(D·V)`;
    * Dulong–Petit in the per-gram, per-mole and per-volume readings, and the corollary that two
      Dulong–Petit solids with the same molar volume have the same volumetric heat capacity;
    * equipartition: `(6/2)R = 3R`, the 6 being 3 directions × 2 (kinetic + potential);
    * the parity split (L1) vs (L2)/(L3): 3 is odd, every table capacity is even, so the heat
      capacity's 3 can never label a cell;
    * the exchange rate is *forced* by the two laws — there is no free parameter in it;
    * the prime-side heat of a window, from the telescoping identity (R23).

  No `sorry`, no `axiom`, no `native_decide`.
-/
import Mathlib

namespace Heat

/-! ## 1. The density triangle — three forms of one relation -/

/-- **The density triangle, read for `D`.** `M = D·V ⟺ D = M/V`. -/
theorem triangle_density (M D V : ℚ) (hV : V ≠ 0) : (M = D * V) ↔ D = M / V := by
  rw [eq_div_iff hV]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

/-- **The density triangle, read for `V`.** `M = D·V ⟺ V = M/D`. -/
theorem triangle_volume (M D V : ℚ) (hD : D ≠ 0) : (M = D * V) ↔ V = M / D := by
  rw [eq_div_iff hD]
  constructor
  · intro h; rw [h]; ring
  · intro h; rw [← h]; ring

/-- All three at once: from any one reading, the other two follow. -/
theorem triangle_all (M D V : ℚ) (hD : D ≠ 0) (hV : V ≠ 0) :
    (M = D * V) ↔ (D = M / V ∧ V = M / D) := by
  constructor
  · intro h
    exact ⟨(triangle_density M D V hV).mp h, (triangle_volume M D V hD).mp h⟩
  · rintro ⟨h1, _⟩
    exact (triangle_density M D V hV).mpr h1

/-! ## 2. The heat twin: `C = c·M = c·D·V` -/

/-- **The heat triangle.** Molar heat `C`, specific heat `c`, molar mass `M`: any two give the third.
This is the density triangle with `M` renamed to `C` and `D` renamed to `c`. -/
theorem heat_triangle (C c M : ℚ) (hM : M ≠ 0) (hc : c ≠ 0) :
    (C = c * M) ↔ (c = C / M ∧ M = C / c) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · rw [eq_div_iff hM, h]
    · rw [eq_div_iff hc, h]; ring
  · rintro ⟨h1, _⟩
    rw [eq_div_iff hM] at h1
    exact h1.symm

/-- **Through the density:** `C = c·D·V` — the molar heat is the specific heat times the *volume*
times the *density*, so the density triangle enters the heat calculation unchanged. -/
theorem heat_from_density (C c D V : ℚ) (h : D * V ≠ 0) :
    (C = c * (D * V)) ↔ c = C / (D * V) := by
  rw [eq_div_iff h]
  exact ⟨fun h' => h'.symm, fun h' => h'.symm⟩

/-- **The volumetric heat capacity.** `D·c = C/V`: per unit volume, the heat capacity is the molar one
over the molar volume. This is the reading the density triangle exists for. -/
theorem volumetric_heat (C c D V : ℚ) (hV : V ≠ 0) (h : C = c * (D * V)) : D * c = C / V := by
  rw [eq_div_iff hV, h]
  ring

/-! ## 3. Dulong–Petit in the three readings -/

/-- **Dulong–Petit, per gram.** `c = 3R/M` is the same statement as `M·c = 3R`. -/
theorem dulong_petit_gram (c M R : ℚ) (hM : M ≠ 0) (h : c = 3 * R / M) : M * c = 3 * R := by
  rw [h]
  field_simp

/-- **Dulong–Petit, per mole.** Reading the molar heat off the measured per-gram value. -/
theorem dulong_petit_molar (C c M R : ℚ) (hM : M ≠ 0) (hc : c = 3 * R / M) (h : C = c * M) :
    C = 3 * R := by
  rw [h, hc]
  field_simp

/-- **Dulong–Petit, per unit volume.** The volumetric heat capacity of a Dulong–Petit solid is
`3R/V`, i.e. it depends on the molar volume **and on nothing else** — not on the mass, not on `Z`. -/
theorem dulong_petit_volumetric (c D V R : ℚ) (hD : D ≠ 0) (hV : V ≠ 0)
    (h : c = 3 * R / (D * V)) : D * c = 3 * R / V := by
  rw [h]
  field_simp

/-- **The corollary worth quoting:** two Dulong–Petit solids with the same molar volume have the same
volumetric heat capacity, whatever their masses. That is the prediction the third reading makes. -/
theorem same_molar_volume_same_volumetric (c₁ D₁ c₂ D₂ V R : ℚ)
    (hD₁ : D₁ ≠ 0) (hD₂ : D₂ ≠ 0) (hV : V ≠ 0)
    (h₁ : c₁ = 3 * R / (D₁ * V)) (h₂ : c₂ = 3 * R / (D₂ * V)) : D₁ * c₁ = D₂ * c₂ := by
  rw [dulong_petit_volumetric c₁ D₁ V R hD₁ hV h₁,
      dulong_petit_volumetric c₂ D₂ V R hD₂ hV h₂]

/-- The measured ratio the record quotes, as a statement: `C/(3R) = 1` exactly when the solid is
classical. Anything else is the quantum deficit, labelled. -/
theorem dp_ratio_one (C R : ℚ) (hR : R ≠ 0) : (C = 3 * R) ↔ (C / (3 * R) = 1) := by
  have h3 : (3 : ℚ) * R ≠ 0 := mul_ne_zero (by norm_num) hR
  constructor
  · intro h; rw [h, div_self h3]
  · intro h
    rw [div_eq_iff h3] at h
    linarith

/-! ## 4. Equipartition, and the parity split between the capacities -/

/-- **`3R` is six quadratic degrees of freedom**, `(6/2)R`: three directions, each with a kinetic and
a potential term. This is the arithmetic of the "3" — it counts directions. -/
theorem equipartition_six (R : ℚ) : (6 / 2 : ℚ) * R = 3 * R := by norm_num

/-- The same thing unsimplified: three modes add. -/
theorem three_directions (R : ℚ) : 3 * R = R + R + R := by ring

/-- **The heat capacity's 3 is odd, and no table capacity is.** Every block width is `2(2l+1)`, so no
cell can carry the value 3 — the theorem that rules out an odd *digit* rules out the Dulong–Petit
*integer* too. The two 3s are different objects: one counts spatial directions, the other would have
to be a count of slots. -/
theorem three_not_a_capacity (l : ℕ) : 2 * (2 * l + 1) ≠ 3 := by omega

/-- And the parity, stated on its own: the count capacities are even, the heat integer is not. -/
theorem capacity_even_heat_odd : (∀ l : ℕ, ∃ k, 2 * (2 * l + 1) = 2 * k) ∧ ¬ ∃ k, 3 = 2 * k := by
  refine ⟨fun l => ⟨2 * l + 1, rfl⟩, ?_⟩
  rintro ⟨k, hk⟩
  omega

/-! ## 5. The exchange rate is forced by the two laws -/

/-- **There is no free parameter in the conversion.** If a prime-side coefficient `a` and a
solid-side constant `b` are put in correspondence, `a·t² = b·T`, then `T = (a/b)·t²` — the rate is the
ratio of the two coefficients and nothing else. With `a = 1/(2C₂) = 0.75739` and `b = 3R = 24.943`
this is the record's `κ = 0.03036` K per unit `t²`. -/
theorem conversion_is_forced (a b t T : ℚ) (hb : b ≠ 0) (h : a * t ^ 2 = b * T) :
    T = (a / b) * t ^ 2 := by
  have key : a / b * t ^ 2 = a * t ^ 2 / b := by ring
  rw [key, eq_div_iff hb]
  linear_combination -h

/-- The record's `κ`, bracketed exactly: `0.03036 < 0.75739/(3·8.314462618) < 0.03037`. -/
theorem kappa_bracket :
    (0.03036 : ℚ) < (75739 / 100000 : ℚ) / (3 * (8314462618 / 1000000000)) ∧
      (75739 / 100000 : ℚ) / (3 * (8314462618 / 1000000000)) < 0.03037 := by
  constructor <;> norm_num

/-! ## 6. The prime side's own heat: a window's `ΣT/Σt²`, from the telescoping identity -/

/-- **The specific heat of a window, exactly.** With `ΣT = c·Σt²`, `ΣT = span + 2n` (the companion of
R23, `Merge.totals_excess`) and `span = Σair + 2n` (R23), the window's heat is `c·Σt² = Σair + 4n`:
fixed by its air sum, its handoff count and its `Σ log²p` — no free parameter, and computable from
the chain alone. The division-free form. -/
theorem segment_heat (c air span n t2 : ℚ) (h : c * t2 = span + 2 * n) (hspan : span = air + 2 * n) :
    c * t2 = air + 4 * n := by
  rw [hspan] at h
  linarith

/-- The same solved for the heat, which is how the record tabulates it: `c = (Σair + 4n)/Σt²`. -/
theorem segment_heat_ratio (c air n t2 : ℚ) (ht2 : t2 ≠ 0) (h : c * t2 = air + 4 * n) :
    c = (air + 4 * n) / t2 := by
  rw [eq_div_iff ht2]
  linear_combination h

end Heat
