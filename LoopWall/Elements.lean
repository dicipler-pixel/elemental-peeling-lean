/-
# The element ledger layer of the loop wall

Ported from the checked source `lean/LoopWall.lean` of *Periodic Table of Elemental Peels v1.1*
(Jeromie Beasley, 21 November 2026), whose header reads:

  the peel reflection, its reversal, the loop wall, and the element certificates. Core Lean 4.34.1,
  no Mathlib. All arithmetic is exact over `Rat`.

The proofs are unchanged; only the namespace wrapper, this header and the removal of the trailing
`#print axioms` lines (the repository's `scripts/verify.py` performs that audit for every named
theorem) differ from the source. See PROVENANCE.md.
-/

namespace ElementalPeeling.LoopWall

/-
# SCRIPT: VOTKP-ELEMENTS-LOOPWALL-01
VOTKP elements, H to Ne: the peel reflection, its reversal, the loop wall, and the
element certificates. Core Lean 4.34.1, no Mathlib. All arithmetic is exact over `Rat`.

The peel step of an ordered pair of thresholds (a then b) has ratio z = b/a and reflection
  Γ(z) = (z - 1)/(z + 1)  ( = tanh(½ ln z), proved for reals in votkp-lean `VOTKP.Smith.smith_identity` ).
The loop wall is Γ² = 1/2, the equal-face condition sinh h_a sinh h_b = 1 with h_a = h_b = ½ ln z.
Over the rationals it is written without √2:  z > 3 + 2√2  ⇔  z > 3 ∧ (z - 3)² > 8.
Energies are NIST ASD v5.12 (2024) ionization energies and measured electron affinities, in eV.
-/

/-- The peel reflection of a ratio `z`. -/
def gam (z : Rat) : Rat := (z - 1) / (z + 1)

/-- Outside the loop wall (Γ² > 1/2 on the rising side), written without √2. -/
def outside (z : Rat) : Prop := 3 < z ∧ 8 < (z - 3) * (z - 3)

/-- Inside the loop wall on the rising side: 1 < z < 3 + 2√2. -/
def inside (z : Rat) : Prop := 1 < z ∧ (z - 3) * (z - 3) < 8

/-! ## 1. Direction: reversing the peel order flips the sign and keeps the power -/

/-- Reversal is odd: the reverse step (b then a) has ratio 1/z and reflection −Γ(z). -/
theorem gam_reverse (z : Rat) (hz : 0 < z) : gam (1 / z) = - gam z := by
  unfold gam
  have : z ≠ 0 := by grind
  grind

/-- The returned power Γ² is even: both orders give the same Γ². A ledger that keeps only Γ²
cannot tell the two directions apart; the sign carries the direction. -/
theorem power_even (z : Rat) (hz : 0 < z) : gam (1 / z) * gam (1 / z) = gam z * gam z := by
  rw [gam_reverse z hz]
  grind

/-! ## 2. The loop wall -/

/-- Γ² > 1/2 exactly when z² − 6z + 1 > 0 (for z > 0). -/
theorem wall_quadratic (z : Rat) (hz : 0 < z) :
    1 / 2 < gam z * gam z ↔ 0 < z * z - 6 * z + 1 := by
  unfold gam
  have h1 : 0 < z + 1 := by grind
  have hp : 0 < (z + 1) * (z + 1) := Rat.mul_pos h1 h1
  have key : (z - 1) / (z + 1) * ((z - 1) / (z + 1)) = (z - 1) * (z - 1) / ((z + 1) * (z + 1)) := by
    grind
  rw [key, Rat.lt_div_iff hp]
  constructor <;> intro h <;> grind

/-- On the rising side (z > 1), outside the wall in the √2-free form is Γ² > 1/2. -/
theorem outside_iff (z : Rat) (hz : 1 < z) : outside z ↔ 1 / 2 < gam z * gam z := by
  rw [wall_quadratic z (by grind)]
  unfold outside
  constructor
  · intro ⟨h3, h8⟩; grind
  · intro h
    refine ⟨?_, by grind⟩
    -- if z ≤ 3 then z² − 6z + 1 = (z − 3)² − 8 ≤ (3 − 1)² − 8 < 0 for 1 < z ≤ 3
    by_cases h3 : 3 < z
    · exact h3
    · exfalso
      have hpos : 0 < (z - 1) * (5 - z) := Rat.mul_pos (by grind) (by grind)
      grind

/-- The equal-face form: with h = ½ ln z, sinh² h = (z − 1)²/(4z), and this equals Γ²/(1 − Γ²).
So sinh h_a · sinh h_b = 1 at equal faces is exactly Γ² = 1/2. -/
theorem sinh_sq_form (z : Rat) (hz : 0 < z) :
    (z - 1) * (z - 1) / (4 * z) = gam z * gam z / (1 - gam z * gam z) := by
  unfold gam
  have h0 : z ≠ 0 := by grind
  have h1 : z + 1 ≠ 0 := by grind
  have h2 : 1 - (z - 1) / (z + 1) * ((z - 1) / (z + 1)) = 4 * z / ((z + 1) * (z + 1)) := by
    grind
  rw [h2]
  grind

/-! ## 3. Fixed points of the ladder -/

/-- The hydrogenic n = 2 → 1 limit: z = 4, Γ = 3/5 (inside the wall). -/
theorem hydrogenic_limit : gam 4 = 3 / 5 ∧ inside 4 := by
  unfold gam inside; constructor <;> grind

/-- Γ = 2/3 exactly at z = 5. -/
theorem two_thirds_iff (z : Rat) (hz : 0 < z) : gam z = 2 / 3 ↔ z = 5 := by
  unfold gam
  have h1 : z + 1 ≠ 0 := by grind
  constructor
  · intro h
    have e : (z - 1) / (z + 1) * (z + 1) = z - 1 := Rat.div_mul_cancel h1
    rw [h] at e
    grind
  · intro h; subst h; grind

/-! ## 4. Element certificates (NIST ASD v5.12; measured electron affinities) -/

/-- The 1s core opening (last 2s removal → first 1s removal) for Li to Ne.
Li, Be, B, C stand outside the loop wall; N, O, F, Ne stand inside it. -/
theorem k_opening_Li : outside (75.6400970 / 5.391714996) := by unfold outside; grind
theorem k_opening_Be : outside (153.896205 / 18.21115) := by unfold outside; grind
theorem k_opening_B : outside (259.374379 / 37.93059) := by unfold outside; grind
theorem k_opening_C : outside (392.09056 / 64.49352) := by unfold outside; grind
theorem k_opening_N : inside (552.06741 / 97.8901) := by unfold inside; grind
theorem k_opening_O : inside (739.32697 / 138.1189) := by unfold inside; grind
theorem k_opening_F : inside (953.8983 / 185.1868) := by unfold inside; grind
theorem k_opening_Ne : inside (1195.8082 / 239.0970) := by unfold inside; grind

/-- The crossing lies between carbon and nitrogen. -/
theorem crossing_C_N : outside (392.09056 / 64.49352) ∧ inside (552.06741 / 97.8901) :=
  ⟨k_opening_C, k_opening_N⟩

/-- Neon's encoded core-opening ratio is strictly greater than five, so its Γ is just above 2/3.
This is a statement about the encoded reference thresholds; measurement uncertainty is a
separate question. -/
theorem neon_just_above_two_thirds :
    5 < 1195.8082 / 239.0970 ∧ 1195.8082 / 239.0970 < (5.0014 : Rat) := by decide +kernel

/-- Rung 0 (anion → neutral: electron affinity, then first ionization energy).
H, Li, B, C, O stand outside the wall; F stands inside. He, Be, N, Ne have no bound anion. -/
theorem rung0_H : outside (13.598434599702 / 0.754195) := by unfold outside; grind
theorem rung0_Li : outside (5.391714996 / 0.618049) := by unfold outside; grind
theorem rung0_B : outside (8.298019 / 0.279723) := by unfold outside; grind
theorem rung0_C : outside (11.2602880 / 1.2621226) := by unfold outside; grind
theorem rung0_O : outside (13.618055 / 1.4611136) := by unfold outside; grind
theorem rung0_F : inside (17.42282 / 3.4011898) := by unfold inside; grind

/-- Oxygen's anion rung is outside the loop wall and its 1s core-opening rung is inside,
using the encoded reference thresholds: one element, two boundaries, two sides. -/
theorem oxygen_two_sides :
    outside (13.618055 / 1.4611136) ∧ inside (739.32697 / 138.1189) := ⟨rung0_O, k_opening_O⟩

/-! ## 5. The screened series (Hartree units) puts the crossing between Z = 6 and Z = 7 -/

/-- Screened core and valence energies from the 11 November 2026 shell-screening note. -/
def Icore (Z : Rat) : Rat := Z * Z / 2 - 5 * Z / 8 + 0.157666
def Ival (Z : Rat) : Rat := Z * Z / 8 - 290 * Z / 729 + 0.250500

theorem screened_six_outside : outside (Icore 6 / Ival 6) := by unfold outside Icore Ival; grind
theorem screened_seven_inside : inside (Icore 7 / Ival 7) := by unfold inside Icore Ival; grind

/-- Control: with the core unscreened (Z²/2) the crossing moves to between 9 and 10. -/
def IcoreBare (Z : Rat) : Rat := Z * Z / 2
theorem bare_nine_outside : outside (IcoreBare 9 / Ival 9) := by unfold outside IcoreBare Ival; grind
theorem bare_ten_inside : inside (IcoreBare 10 / Ival 10) := by unfold inside IcoreBare Ival; grind
theorem bare_seven_still_outside : outside (IcoreBare 7 / Ival 7) := by
  unfold outside IcoreBare Ival; grind

/-! ## 6. The false controls, refuted -/

/-- The two sides of the wall exclude each other. -/
theorem not_both (z : Rat) (h : inside z) : ¬ outside z := by
  unfold inside at h; unfold outside; grind

theorem refute_N_outside : ¬ outside (552.06741 / 97.8901) := not_both _ k_opening_N
theorem refute_F_rung0_outside : ¬ outside (17.42282 / 3.4011898) := not_both _ rung0_F
theorem refute_C_inside : ¬ inside (392.09056 / 64.49352) := by
  intro h; exact not_both _ h k_opening_C
theorem refute_Ne_exactly_five : (1195.8082 / 239.0970 : Rat) ≠ 5 := by decide +kernel
theorem refute_screened_seven_outside : ¬ outside (Icore 7 / Ival 7) := not_both _ screened_seven_inside
/-- Γ² cannot be odd under reversal: at z = 2 both orders give 1/9, not 1/9 and −1/9. -/
theorem refute_power_odd :
    ¬ (∀ z : Rat, 0 < z → gam (1 / z) * gam (1 / z) = - (gam z * gam z)) := by
  intro h
  have := h 2 (by decide)
  unfold gam at this
  grind

/-! ## 7. Both peel directions: the wall has two branches -/

/-- Below one: the reverse branch of the wall. For 0 < z < 1, Γ² > 1/2 exactly when
z < 3 − 2√2, written without √2 as z < 3 ∧ (3 − z)² > 8. -/
def outsideReverse (z : Rat) : Prop := 0 < z ∧ z < 3 ∧ 8 < (3 - z) * (3 - z)

/-- For every positive z the wall classification is the polynomial one, so it covers both
branches: 0 < z < 3 − 2√2 or z > 3 + 2√2. -/
theorem wall_two_branches (z : Rat) (hz : 0 < z) :
    1 / 2 < gam z * gam z ↔ (outsideReverse z ∨ outside z) := by
  rw [wall_quadratic z hz]
  unfold outsideReverse outside
  constructor
  · intro h
    by_cases h3 : 3 < z
    · exact Or.inr ⟨h3, by grind⟩
    · by_cases hlt : z < 3
      · exact Or.inl ⟨hz, hlt, by grind⟩
      · exfalso
        have e : z = 3 := by grind
        subst e
        grind
  · intro h
    rcases h with ⟨_, _, h8⟩ | ⟨_, h8⟩ <;> grind

/-- Reversal keeps the wall classification: a step and its reverse are on the same side. -/
theorem reverse_same_side (z : Rat) (hz : 0 < z) :
    (1 / 2 < gam (1 / z) * gam (1 / z)) ↔ (1 / 2 < gam z * gam z) := by
  rw [power_even z hz]

/-- The exact-fraction illustration: z = 6 gives Γ = 5/7, z = 1/6 gives Γ = −5/7,
and both have Γ² = 25/49 > 1/2. -/
theorem six_and_sixth :
    gam 6 = 5 / 7 ∧ gam (1 / 6) = -(5 / 7) ∧ gam 6 * gam 6 = 25 / 49 ∧
      gam (1 / 6) * gam (1 / 6) = 25 / 49 ∧ (1 : Rat) / 2 < 25 / 49 := by
  unfold gam; refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-! ## 8. Batch 3: sodium to phosphorus (NIST ASD v5.12; electron affinities from the 2022
atomic negative-ion evaluation), using the encoded reference thresholds -/

/-- The L opening (last 3s removal → first 2p removal) crosses the wall between Na and Mg. -/
theorem l_opening_Na : outside (47.28636 / 5.13907696) := by unfold outside; grind
theorem l_opening_Mg : inside (80.1436 / 15.035271) := by unfold inside; grind
theorem l_opening_Al : inside (119.9924 / 28.447642) := by unfold inside; grind
theorem l_opening_Si : inside (166.767 / 45.14179) := by unfold inside; grind
theorem l_opening_P : inside (220.43 / 65.02511) := by unfold inside; grind
theorem l_crossing_Na_Mg : outside (47.28636 / 5.13907696) ∧ inside (80.1436 / 15.035271) :=
  ⟨l_opening_Na, l_opening_Mg⟩

/-- The K opening stays inside the wall for all five. -/
theorem k_opening_Na : inside (1465.0992 / 299.856) := by unfold inside; grind
theorem k_opening_Mg : inside (1761.8049 / 367.489) := by unfold inside; grind
theorem k_opening_Al : inside (2085.97693 / 442.005) := by unfold inside; grind
theorem k_opening_Si : inside (2437.65805 / 523.415) := by unfold inside; grind
theorem k_opening_P : inside (2816.90868 / 611.741) := by unfold inside; grind

/-- Rung 0: Na, Al, Si, P outside. Mg has no bound ground-state anion. -/
theorem rung0_Na : outside (5.13907696 / 0.547926) := by unfold outside; grind
theorem rung0_Al : outside (5.985769 / 0.43283) := by unfold outside; grind
theorem rung0_Si : outside (8.15168 / 1.3895212) := by unfold outside; grind
theorem rung0_P : outside (10.486686 / 0.746609) := by unfold outside; grind

/-- Silicon's anion rung stays outside at both ends of its quoted uncertainties
(I₁ = 8.15168(3) eV, EA = 1.3895212(7) eV). -/
theorem rung0_Si_low : outside (8.15165 / 1.3895219) := by unfold outside; grind
theorem rung0_Si_high : outside (8.15171 / 1.3895205) := by unfold outside; grind

/-- Magnesium: every step of its ladder is inside the wall, yet the metal conducts.
So an outside atomic rung is not required for conduction. -/
theorem mg_all_inside :
    inside (15.035271 / 7.646236) ∧ inside (80.1436 / 15.035271) ∧
    inside (109.2654 / 80.1436) ∧ inside (141.33 / 109.2654) ∧ inside (186.76 / 141.33) ∧
    inside (225.02 / 186.76) ∧ inside (265.924 / 225.02) ∧ inside (327.99 / 265.924) ∧
    inside (367.489 / 327.99) ∧ inside (1761.8049 / 367.489) ∧
    inside (1962.663889 / 1761.8049) := by
  unfold inside; refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> grind

/-- The strongest ordinary step changes identity between Mg and Al: L opening above K opening
at Mg, K opening above L opening at Al. A change of rank, not a wall crossing. -/
theorem rank_swap_Mg_Al :
    1761.8049 / 367.489 < (80.1436 / 15.035271 : Rat) ∧
    119.9924 / 28.447642 < (2085.97693 / 442.005 : Rat) := by
  constructor <;> grind

/-- The screened series keeps the K opening inside the wall from Z = 11 to 15. -/
theorem screened_inside_11_to_15 :
    inside (Icore 11 / Ival 11) ∧ inside (Icore 12 / Ival 12) ∧ inside (Icore 13 / Ival 13) ∧
    inside (Icore 14 / Ival 14) ∧ inside (Icore 15 / Ival 15) := by
  unfold inside Icore Ival; refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> grind

theorem refute_Mg_L_outside : ¬ outside (80.1436 / 15.035271) := not_both _ l_opening_Mg
theorem refute_Si_rung0_inside : ¬ inside (8.15168 / 1.3895212) := by
  intro h; exact not_both _ h rung0_Si

/-! ## 9. Batch 4: sulfur to calcium, using the encoded reference thresholds -/

/-- The M opening (last 4s removal → first 3p removal) crosses the wall between K and Ca. -/
theorem m_opening_K : outside (31.625 / 4.34066373) := by unfold outside; grind
theorem m_opening_Ca : inside (50.91316 / 11.871719) := by unfold inside; grind
theorem m_crossing_K_Ca : outside (31.625 / 4.34066373) ∧ inside (50.91316 / 11.871719) :=
  ⟨m_opening_K, m_opening_Ca⟩

/-- The L opening and the K opening are inside for all five. -/
theorem l_openings_S_to_Ca :
    inside (280.954 / 88.0529) ∧ inside (348.306 / 114.2013) ∧ inside (422.6 / 143.4567) ∧
    inside (503.67 / 175.8174) ∧ inside (591.6 / 211.275) := by
  unfold inside; refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> grind
theorem k_openings_S_to_Ca :
    inside (3223.78057 / 706.994) ∧ inside (3658.34366 / 809.198) ∧ inside (4120.66559 / 918.375) ∧
    inside (4610.80714 / 1034.542) ∧ inside (5128.8576 / 1157.726) := by
  unfold inside; refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> grind

/-- Rung 0: S and Cl inside, K and Ca outside; Ar has no bound ground-state anion. -/
theorem rung0_S : inside (10.36001 / 2.0771042) := by unfold inside; grind
theorem rung0_Cl : inside (12.967633 / 3.612725) := by unfold inside; grind
theorem rung0_K : outside (4.34066373 / 0.501459) := by unfold outside; grind
theorem rung0_Ca : outside (6.11315547 / 0.02455) := by unfold outside; grind
/-- Calcium's anion rung stays far outside even at the high end of its quoted EA, 0.02465 eV. -/
theorem rung0_Ca_high : outside (6.11315547 / 0.02465) := by unfold outside; grind

/-- Calcium: every ordinary step of its ladder is inside the wall, and calcium is a metal. -/
theorem ca_all_ordinary_inside :
    inside (11.871719 / 6.11315547) ∧ inside (50.91316 / 11.871719) ∧ inside (67.2732 / 50.91316) ∧
    inside (84.34 / 67.2732) ∧ inside (108.78 / 84.34) ∧ inside (127.21 / 108.78) ∧
    inside (147.24 / 127.21) ∧ inside (188.54 / 147.24) ∧ inside (211.275 / 188.54) ∧
    inside (591.6 / 211.275) ∧ inside (658.2 / 591.6) ∧ inside (728.6 / 658.2) ∧
    inside (817.2 / 728.6) ∧ inside (894.0 / 817.2) ∧ inside (973.7 / 894.0) ∧
    inside (1086.8 / 973.7) ∧ inside (1157.726 / 1086.8) ∧ inside (5128.8576 / 1157.726) ∧
    inside (5469.86358 / 5128.8576) := by
  unfold inside
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> grind

/-- The strongest ordinary step changes identity between K and Ca: M above K at potassium,
K above M at calcium. -/
theorem rank_swap_K_Ca :
    4610.80714 / 1034.542 < (31.625 / 4.34066373 : Rat) ∧
    50.91316 / 11.871719 < (5128.8576 / 1157.726 : Rat) := by
  constructor <;> grind

/-! ## 10. The two screening readouts, exactly -/

/-- With b = (Z − σ)²/2 the He-like energy, h the H-like energy and S = (h − b)/Z,
the gap between the two readouts is exact: Z(S − σ) = (h − Z²/2) − σ²/2. -/
theorem readouts_identity (Z σ h : Rat) (hZ : Z ≠ 0) :
    Z * ((h - (Z - σ) * (Z - σ) / 2) / Z - σ) = (h - Z * Z / 2) - σ * σ / 2 := by
  have e : (h - (Z - σ) * (Z - σ) / 2) / Z * Z = h - (Z - σ) * (Z - σ) / 2 :=
    Rat.div_mul_cancel hZ
  grind

/-- The control: if the H-like energy is the bare hydrogenic Z²/2, then S − σ = −σ²/(2Z) ≤ 0
for every positive Z and every σ. So S can rise above σ only through the extra binding of the
H-like ion beyond Z²/2 (Dirac, mass and Lamb terms). -/
theorem readouts_control (Z σ : Rat) (hZ : 0 < Z) :
    (Z * Z / 2 - (Z - σ) * (Z - σ) / 2) / Z - σ ≤ 0 := by
  have hz : Z ≠ 0 := by grind
  have e : (Z * Z / 2 - (Z - σ) * (Z - σ) / 2) / Z * Z = Z * Z / 2 - (Z - σ) * (Z - σ) / 2 :=
    Rat.div_mul_cancel hz
  have sq : 0 ≤ σ * σ := by
    by_cases hs : 0 ≤ σ
    · exact Rat.mul_nonneg hs hs
    · have h1 : 0 ≤ -σ := by grind
      have := Rat.mul_nonneg h1 h1
      grind
  by_cases hpos : 0 < (Z * Z / 2 - (Z - σ) * (Z - σ) / 2) / Z - σ
  · exfalso
    have := Rat.mul_pos hpos hZ
    grind
  · grind

theorem refute_Ca_M_outside : ¬ outside (50.91316 / 11.871719) := not_both _ m_opening_Ca
theorem refute_K_M_inside : ¬ inside (31.625 / 4.34066373) := by
  intro h; exact not_both _ h m_opening_K

/-! ## 11. Junctions, faces and the shell floors -/

/-- Equal clocks at a junction give no reflection: z = 1 is transparent. -/
theorem matched_junction : gam 1 = 0 := by unfold gam; grind

/-- The ratio is recovered from the reflection: z = (1 + Γ)/(1 − Γ). -/
theorem gam_inverse (z : Rat) (hz : 0 < z) : (1 + gam z) / (1 - gam z) = z := by
  unfold gam
  have h1 : z + 1 ≠ 0 := by grind
  have e1 : 1 + (z - 1) / (z + 1) = 2 * z / (z + 1) := by grind
  have e2 : 1 - (z - 1) / (z + 1) = 2 / (z + 1) := by grind
  rw [e1, e2]
  have h2 : (2 : Rat) / (z + 1) ≠ 0 := by
    intro h
    have := Rat.div_mul_cancel (a := (2 : Rat)) h1
    rw [h] at this; grind
  grind

/-- The face apex. With r = ln z and w = √z, the apex tanh(r/4) is Γ(w) = (w − 1)/(w + 1), and
the face gives back the full ratio: ((1 + a)/(1 − a))² = w² = z. -/
theorem face_apex (w : Rat) (hw : 0 < w) :
    (1 + gam w) / (1 - gam w) * ((1 + gam w) / (1 - gam w)) = w * w := by
  rw [gam_inverse w hw]

/-- The hydrogenic shell floors ((n+1)/n)² for n = 1 to 6 (4, 9/4, 16/9, 25/16, 36/25, 49/36)
all sit inside the loop wall: a bare change of shell never reaches it. -/
theorem shell_floors_inside :
    inside 4 ∧ inside (9 / 4) ∧ inside (16 / 9) ∧ inside (25 / 16) ∧ inside (36 / 25) ∧
    inside (49 / 36) := by
  unfold inside; refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> grind

/-! ## 12. Batch 5: the anion rungs of Sc, Ti, V, Cr (Mn has no bound ground-state anion) -/

theorem rung0_Sc : outside (6.56149 / 0.179380) := by unfold outside; grind
theorem rung0_Ti : outside (6.82812 / 0.07554) := by unfold outside; grind
theorem rung0_V : outside (6.746187 / 0.52766) := by unfold outside; grind
theorem rung0_Cr : outside (6.76651 / 0.675928) := by unfold outside; grind

/-! ## 13. Batch 6: the anion rungs of Fe, Co, Ni, Cu (Zn has no bound ground-state anion) -/

theorem rung0_Fe : outside (7.9024681 / 0.153236) := by unfold outside; grind
theorem rung0_Co : outside (7.88101 / 0.662255) := by unfold outside; grind
theorem rung0_Ni : outside (7.639878 / 1.157368) := by unfold outside; grind
theorem rung0_Cu : outside (7.72638 / 1.23578) := by unfold outside; grind

/-- Batch 7 anion rungs, gallium to bromine. Arsenic and selenium are certified at both the older
evaluated affinity and the newer measurement (arsenic 0.8048 eV and 0.804486 eV, 2025; selenium
2.0206046 eV, 2012, and 2.020667 eV, 2026): neither revision changes the side of the wall. -/
theorem rung0_Ga : outside (5.999302 / 0.301166) := by unfold outside; grind
theorem rung0_Ge : outside (7.899435 / 1.2326764) := by unfold outside; grind
theorem rung0_As : outside (9.78855 / 0.804486) ∧ outside (9.78855 / 0.8048) := by
  unfold outside; constructor <;> grind
theorem rung0_Se : inside (9.752368 / 2.020667) ∧ inside (9.752368 / 2.0206046) := by
  unfold inside; constructor <;> grind
theorem rung0_Br : inside (11.81381 / 3.363588) := by unfold inside; grind

/-- Batch 8 anion rungs, rubidium to zirconium (krypton has no bound anion). -/
theorem rung0_Rb : outside (4.1771281 / 0.485916) := by unfold outside; grind
theorem rung0_Sr : outside (5.69486745 / 0.05206) := by unfold outside; grind
theorem rung0_Y : outside (6.21726 / 0.31129) := by unfold outside; grind
theorem rung0_Zr : outside (6.634126 / 0.433283) := by unfold outside; grind

/-- Batch 9 anion rungs, niobium to rhodium. Technetium's affinity is a calculated value (0.636 eV),
so its call is also certified for any affinity up to 1.2 eV; rhodium uses the 2026 measurement
1.14273 eV and is also certified at the older 1.14289 eV. -/
theorem rung0_Nb : outside (6.75885 / 0.91740) := by unfold outside; grind
theorem rung0_Mo : outside (7.09243 / 0.74723) := by unfold outside; grind
theorem rung0_Tc : outside (7.11938 / 0.636) ∧ outside (7.11938 / 1.2) := by
  unfold outside; constructor <;> grind
theorem rung0_Ru : outside (7.3605 / 1.046270) := by unfold outside; grind
theorem rung0_Rh : outside (7.4589 / 1.14273) ∧ outside (7.4589 / 1.14289) := by
  unfold outside; constructor <;> grind

/-- Batch 10 anion rungs, palladium to tin (cadmium has no bound anion). Silver's rung is the
closest inside value from hydrogen to tin (5.8079); with silicon's (5.8665, outside) it brackets
every cutoff that sorts the archive the same way, and 3 + 2√2 lies between them. -/
theorem rung0_Pd : outside (8.336839 / 0.56214) := by unfold outside; grind
theorem rung0_Ag : inside (7.576234 / 1.30447) := by unfold inside; grind
theorem rung0_In : outside (5.7863558 / 0.38392) := by unfold outside; grind
theorem rung0_Sn : outside (7.343918 / 1.112070) := by unfold outside; grind
/-- Batch 11 anion rungs, antimony to caesium (xenon has no bound anion). -/
theorem rung0_Sb : outside (8.608389 / 1.047401) := by unfold outside; grind
theorem rung0_Te : inside (9.009808 / 1.970875) := by unfold inside; grind
theorem rung0_I : inside (10.451236 / 3.0590465) := by unfold inside; grind
theorem rung0_Cs : outside (3.89390572743 / 0.471626) := by unfold outside; grind
/-- Ordinary steps alone, hydrogen to caesium: nitrogen's helium-core opening is the largest inside
and caesium's xenon-core opening the smallest outside, so a cutoff of 6 no longer sorts them. -/
theorem ordinary_window_nitrogen_caesium :
    inside (552.06741 / 97.8901) ∧ outside (23.15745 / 3.89390572743) ∧
    (23.15745 / 3.89390572743 : Rat) < 6 := by
  unfold inside outside; refine ⟨?_, ?_, ?_⟩ <;> grind
/-- Batches 12 and 13 anion rungs, barium to terbium (Ning and Lu 2022 unless noted). Europium is
from Cheng and Castleman (2015); gadolinium's preliminary value is certified across its quoted
uncertainty. Promethium (theory only) and samarium (lower bound only) are not certified. -/
theorem rung0_Ba : outside (5.2116646 / 0.14462) := by unfold outside; grind
theorem rung0_La : outside (5.5769 / 0.557546) := by unfold outside; grind
theorem rung0_Ce : outside (5.5386 / 0.600160) := by unfold outside; grind
theorem rung0_Pr : outside (5.4702 / 0.10923) := by unfold outside; grind
theorem rung0_Nd : outside (5.525 / 0.09748) := by unfold outside; grind
theorem rung0_Eu : outside (5.670385 / 0.129) := by unfold outside; grind
theorem rung0_Gd : outside (6.1498 / 0.242) := by unfold outside; grind
theorem rung0_Tb : outside (5.8638 / 0.13131) := by unfold outside; grind
/-- Batches 15 to 17 anion rungs, lutetium to astatine (measured or evaluated affinities; dysprosium and
thulium have only estimated affinities and are not certified). -/
theorem rung0_Lu : outside (5.425871 / 0.23882) := by unfold outside; grind
theorem rung0_Hf : outside (6.82507 / 0.1780) := by unfold outside; grind
theorem rung0_Ta : outside (7.549571 / 0.328859) := by unfold outside; grind
theorem rung0_W : outside (7.86403 / 0.816500) := by unfold outside; grind
theorem rung0_Re : outside (7.83352 / 0.060396) := by unfold outside; grind
theorem rung0_Os : outside (8.43823 / 1.077661) := by unfold outside; grind
theorem rung0_Tl : outside (6.1082873 / 0.320053) := by unfold outside; grind
theorem rung0_Pb : outside (7.4166799 / 0.356721) := by unfold outside; grind
theorem rung0_Bi : outside (7.285516 / 0.942362) := by unfold outside; grind
theorem rung0_Ir : inside (8.96702 / 1.564057) := by unfold inside; grind
theorem rung0_Pt : inside (8.95883 / 2.12510) := by unfold inside; grind
theorem rung0_Au : inside (9.225554 / 2.30861) := by unfold inside; grind
theorem rung0_At : inside (9.31751 / 2.41578) := by unfold inside; grind
/-- The heavy-anion prediction written at 09:24 on 21 November 2026, before the numbers were opened:
gold, platinum, iridium and astatine inside; osmium, bismuth and lead outside (polonium has no
established affinity yet and stays open). All seven calls hold. -/
theorem heavy_anion_prediction :
    inside (9.225554 / 2.30861) ∧ inside (8.95883 / 2.12510) ∧
    inside (8.96702 / 1.564057) ∧ inside (9.31751 / 2.41578) ∧
    outside (8.43823 / 1.077661) ∧ outside (7.285516 / 0.942362) ∧
    outside (7.4166799 / 0.356721) := by
  unfold inside outside; refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> grind
/-- The data window: silver's anion rung is inside and silicon's is outside. -/
theorem window_silver_silicon :
    inside (7.576234 / 1.30447) ∧ outside (8.15168 / 1.3895212) := by
  unfold inside outside; constructor <;> grind

/-! ## 14. The junction cutoff in a dilute band, and the screw sign -/

/-- Dilute-band bound. Per spin the neighbour element of the projector is at most the filling f,
so X ≤ 2f², while the off-site budget is B = 2f(1 − f); with n neighbours the shell fraction
nX/B is at most nf/(1 − f). For bcc (n = 8) and 0 < f ≤ 1/25 that is at most 1/3, so the
coordination-normalised cutoff (shell fraction > 1/3) must fail, though the band is partly filled. -/
theorem dilute_bcc_fails (f : Rat) (h0 : 0 < f) (h1 : f ≤ 1 / 25) : 8 * f / (1 - f) ≤ 1 / 3 := by
  have hp : 0 < 1 - f := by grind
  have e : 8 * f / (1 - f) * (1 - f) = 8 * f := Rat.div_mul_cancel (by grind)
  by_cases h : 8 * f / (1 - f) ≤ 1 / 3
  · exact h
  · exfalso
    have hg : 1 / 3 < 8 * f / (1 - f) := by grind
    have := Rat.mul_lt_mul_of_pos_right hg hp
    grind

/-- The triple product of three displacement vectors. -/
def triple (a b c : Rat × Rat × Rat) : Rat :=
  (a.2.1 * b.2.2 - a.2.2 * b.2.1) * c.1 + (a.2.2 * b.1 - a.1 * b.2.2) * c.2.1 +
    (a.1 * b.2.1 - a.2.1 * b.1) * c.2.2

def vneg (a : Rat × Rat × Rat) : Rat × Rat × Rat := (-a.1, -a.2.1, -a.2.2)
def vmirror (a : Rat × Rat × Rat) : Rat × Rat × Rat := (-a.1, a.2.1, a.2.2)

/-- Traversing a four-site path backwards replaces (d₀, d₁, d₂) by (−d₂, −d₁, −d₀):
the screw sign χ = (d₀ × d₁) · d₂ is unchanged. -/
theorem chi_reverse (a b c : Rat × Rat × Rat) :
    triple (vneg c) (vneg b) (vneg a) = triple a b c := by
  unfold triple vneg; grind

/-- A spatial mirror flips the screw sign. -/
theorem chi_mirror (a b c : Rat × Rat × Rat) :
    triple (vmirror a) (vmirror b) (vmirror c) = - triple a b c := by
  unfold triple vmirror; grind


/-! ## Hardness over electronegativity: the anion rung in conceptual-DFT language -/

/-- At the anion rung z = IE/EA, the reflection is (IE − EA)/(IE + EA): the Pearson absolute
hardness (IE − EA)/2 divided by the Mulliken electronegativity (IE + EA)/2. So the loop wall at
the anion rung is hardness / electronegativity = 1/√2. -/
theorem gam_anion_rung (I A : Rat) (hA : 0 < A) (hI : 0 < I) : gam (I / A) = (I - A) / (I + A) := by
  unfold gam
  have hA' : A ≠ 0 := by grind
  have hs : I + A ≠ 0 := by grind
  have k : A * A⁻¹ = 1 := Rat.mul_inv_cancel A hA'
  have ks : (I + A) * (I + A)⁻¹ = 1 := Rat.mul_inv_cancel (I + A) hs
  rw [Rat.div_def I A, Rat.div_def, Rat.div_def]
  have h1 : I * A⁻¹ - 1 = (I - A) * A⁻¹ := by grind
  have h2 : I * A⁻¹ + 1 = (I + A) * A⁻¹ := by grind
  have h3 : ((I + A) * A⁻¹)⁻¹ = A * (I + A)⁻¹ := by
    apply Rat.inv_eq_of_mul_eq_one; grind
  rw [h1, h2, h3]
  grind

/-- Electrophilicity equals hardness at the wall. With η = (I − A)/2, χ = (I + A)/2 and
ω = χ²/(2η), the comparison ω > η is χ² > 2η², i.e. (I + A)² > 2(I − A)², and that difference is
exactly −(I² − 6IA + A²): the wall quadratic z² − 6z + 1 written in I and A. -/
theorem omega_eta_wall (I A : Rat) :
    (I + A) * (I + A) - 2 * ((I - A) * (I - A)) = -(I * I - 6 * I * A + A * A) := by grind

end ElementalPeeling.LoopWall
