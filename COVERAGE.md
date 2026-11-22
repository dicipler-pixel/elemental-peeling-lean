# Coverage: every claim against its Lean name

The papers' prose is the source; this register says, claim by claim, whether the statement is
machine-checked here and where. Names are namespaced by module: `LoopWall.Archive.ordinary_count`
is the theorem `ordinary_count` in [`LoopWall/Archive.lean`](LoopWall/Archive.lean).

**Status key.** *proved* — a theorem in this repository, checked by the kernel with only the three
standard axioms. *refuted* — false as I first transcribed it; the refutation and the corrected
statement are both in the library, and the correction is described. *not here* — not formalized,
with the reason. *carried* — formalized only as the arithmetic of the archive's numbers, not as the
physics the paper reads into them.

## Rule, reflection, wall

| Claim | Status |
| :--- | :--- |
| A peel step is `z = IE(k+1)/IE(k) > 1` | proved: `Archive.ordinary_one_lt`, `Archive.anion_one_lt` |
| `Γ(z) = (z−1)/(z+1) = tanh(½ log z)` | proved: `Ledger.gam_eq_tanh_half_log` |
| `Γ² > 1/2 ⟺ z² − 6z + 1 > 0` | proved: `Elements.wall_quadratic` |
| `Γ² = 1/2 ⟺ z = 3 ± 2√2`, and the two ratios are reciprocal | proved: `Wall.wall_eq_iff`, `Wall.wall_ratios_reciprocal` |
| Both branches: outside is `z < 3−2√2` or `z > 3+2√2` | proved: `Elements.wall_two_branches`, `CutoffWindow.quadratic_pos_iff_two_branches` |
| The √2-free test `2(b−a)² > (b+a)²` for a step `b/a` | proved: `CutoffWindow.peel_threshold_two_branches` |
| Reversal sends `Γ ↦ −Γ` and fixes `Γ²` | proved: `Elements.gam_reverse`, `Elements.power_even`, `Ledger.gam_reverse`, `Ledger.gam_sq_reverse` |
| `z = (1+Γ)/(1−Γ)` | proved: `Ledger.inverse_gam`, `Elements.gam_inverse` |
| Face apex `a = tanh(r/4)`; `Γ = 2a/(1+a²)`; `z = ((1+a)/(1−a))²` | proved: `Clock.tanh_double`, `Clock.gam_eq_two_apex`, `Clock.apex_inverse` |
| `z = 3` gives `a = 2−√3`, `Γ = 1/2` | proved: `Clock.apex_three`, `Clock.gam_three` |
| Four aligned steps of ratio 3 give ratio 81 and `Γ = 40/41` | proved: `Clock.four_steps_three` |
| Hydrogenic shell floors `((n+1)/n)²` are inside the wall | proved: `Elements.shell_floors_inside` |
| Equal clocks at a junction are transparent (`Γ(1) = 0`) | proved: `Elements.matched_junction` |

## The ledger

| Claim | Status |
| :--- | :--- |
| `∏ z_k = I_last/I_first` | proved: `Ledger.prod_range_ratios`, `Ledger.fin_prod_ratios` |
| `∑ log z_k = log(I_last/I_first)` | proved: `Ledger.sum_range_log_ratios`, `Ledger.fin_sum_log_ratios` |
| Losing absolute scale is exact: `Γ` is unchanged by `I ↦ c·I` | proved: `Ledger.gam_scale` |
| One threshold plus the ratios reconstructs the ladder | proved: `Ledger.reconstruct_range` |
| `ν = I_k/(I_k + I_{k+1})` gives `Γ = 1−2ν`, `ν(1−ν) = (1−Γ²)/4`, `S = 4/(1−Γ²)` | proved: `Ledger.reciprocal_variance`, `Ledger.gam_of_nu` |
| Equal faces give `S = 8` | proved: `Ledger.reciprocal_scale_at_wall` |
| Log steps `a,b` and `b,a` share an endpoint while `a,−a` and `0,0` differ in path | proved for the telescoping endpoint (`Ledger.sum_range_log_ratios`); the "interior shape stays free" reading is a consequence of `Ledger.reconstruct_range`, not a separate theorem |
| A loop-vanishing, additive, reversal-antisymmetric ledger is an endpoint potential | proved: `LedgerDescent.endpointPotential_iff_vanishesOnLoops`, with the explicit potential in `LedgerDescent.walkSum_eq_radialPotential_sub` |
| Skew weights alone make a walk sum a potential difference | **refuted**: `LedgerDescent.chiralWeight_triangle_sum` (= 3) and `chiralWeight_has_no_potential`; the corrected hypothesis is the cocycle identity, `LedgerDescent.walkSum_eq_weight_of_cocycle` |

## Two faces

| Claim | Status |
| :--- | :--- |
| `sinh² h = Γ²/(1−Γ²)` | proved: `Elements.sinh_sq_form` over ℚ, `Clock.sinh_sq_eq_gam_sq` over ℝ |
| `sinh h_a · sinh h_b < 1` is the sum form `Γ_a² + Γ_b² < 1` | proved: `TwoFace.two_face_forms_agree`, `Rung.two_face_product_iff_of_nonneg`, `Rung.sinh_product_lt_one_iff` (needs `0 ≤ sinh h`, stated) |
| The two forms agree at every interior pair only at the diagonal `t = 1/2` | proved: `BoundaryAgreement.uniqueInteriorBoundary`, `Rung.uniqueInteriorBoundary` |
| Every other `t` admits an interior pair on which the forms disagree | proved: `BoundaryAgreement.strictCounterexample`, `BoundaryAgreement.two_face_forms_split_at_midpoint` |
| Two-boost trace `2 − 4 sinh²h_a sinh²h_b = −2` exactly when the product of squared sines is 1 | proved: `Clock.twoBoostTrace_eq_neg_two_iff` |
| In squared reflections that condition is `u + v = 1`; equal faces give `u = v = 1/2` | proved: `Clock.wall_condition_iff`, `Clock.equal_faces` |
| The C/N mixed pair has margin `≈ 0.00309334`, positive across both input rectangles | proved: `Archive.twoFace_margin_C_N` (every ratio in both propagated intervals), `Archive.twoFace_margin_C_N_central` (the bracketed central value) |

## The anion rung

| Claim | Status |
| :--- | :--- |
| `Γ₀ = (I−E)/(I+E) = η/χ` | proved: `Elements.gam_anion_rung`, `Rung.anion_rung_eq_hardness_div_electronegativity` |
| `ω = η` on the wall | proved: `Elements.omega_eta_wall` (the quadratic identity `(I+A)² − 2(I−A)² = −(I² − 6IA + A²)`) |
| `ω > η` exactly when `Γ₀² > 1/2` | **refuted**: `Rung.electrophilicity_wall_as_written_false` (I = 3, E = 1 gives ω > η and `Γ₀² = 1/4`); correct direction proved in `Rung.electrophilicity_gt_hardness_iff` |
| The Roman numeral octave reading and the S/Se/Te/Po pattern | not here: a reading of tabulated affinities, not a theorem |

## The archive

| Claim | Status |
| :--- | :--- |
| 3,570 ordinary steps, 8 outside | proved: `Archive.ordinary_count` (kernel recount from the exact decimals in `data/`) |
| 67 anion rungs, 55 outside, 12 inside | proved: `Archive.anion_outside_count`, `Archive.anion_inside_count` |
| The ordinary window `[5.639665400281, 5.947100834227)`, the rung window `[5.80790205984, 5.866538776091)` | proved: `Archive.ordinary_cutoff_window`, `Archive.anion_cutoff_window`, `Archive.ordinary_cutoff_count`, `Archive.anion_cutoff_count` |
| Every rational cutoff in a window sorts the table identically, so the table cannot single out `3+2√2` | proved: the same four theorems (equality of filters for any `c` in the window) |
| `3 + 2√2` lies inside the data window | proved: `CutoffWindow.loop_wall_ratio_bounds` |
| 3,614 error rectangles, none crossing the wall | proved: `Archive.ratioBoxes_no_crossing`, `Archive.ratioBoxes_ok`, `Archive.ratioBoxes_length` |
| The two propagated endpoints are rebuilt from the raw widths | **not here**: the certificate reads `z_lower`/`z_upper` from the CSV; rebuilding them from `(b∓δb)/(a±δa)` and modelling correlation between the two inputs is not formalized |
| The eight outside steps are core openings of Li, Be, B, C, Na, K, Rb, Cs | *carried*: the eight values are enumerated (`Archive.ordinaryOutside`) and each element's opening is a separate certificate (`OpeningMap`, `Elements`); the identification "this ratio is the first opening of a core" is a reading of the configuration, not proved |
| The noble-core opening map element by element | proved: `OpeningMap.*` (117 theorems), including the francium straddle and the frozen Rb/Sr call |

## Linear algebra and optics

| Claim | Status |
| :--- | :--- |
| A compressed linear observer exists iff `R` vanishes on `ker R` | proved: `Observer.observer_iff` |
| `N_∞ = ker O_d` stabilizes at `finrank − 1` | **refuted as first stated**: `Observer.rawKer_not_antitone`, `rawKer_map_direction_false`, `rawKer_intersection_false`; corrected for the cumulative kernels in `Observer.iInf_rawKer_eq` and `Observer.iInf_obsKer_eq` |
| `J†A²J − (J†AJ)² = (QAJ)†(QAJ)`, positive, vanishing iff `QAJ = 0` | proved: `CompressionVariance.compression_variance_identity`, `compressionVariance_isPositive`, `compressionVariance_eq_zero_iff` |
| The two-state falsifier (compressed `σ₁` is 0, compressed `σ₁²` is 1) | proved: `CompressionVariance.real_pauliX_variance_eq_one`, `real_pauliX_variance_ne_zero` |
| `[H,H†] = −2[D,A]` for `H = D + A`, `D` Hermitian, `A` skew-adjoint | proved: `Junction.junction_commutator` |
| `(1/8)‖[H,H†]‖²_F = ‖D₀ − A D₁ A†‖²_F` for a unitary edge block | proved for the paper's anti-Hermitian convention: `Junction.corrected_junction_energy`, `corrected_junction_energy_sum`. The transcription with lower-left block `A†` is **refuted** (`original_block_energy_identity_false`) because that matrix is Hermitian |
| `(aσ₁+bσ₂)² = (a²+b²)`, spectrum `±√(a²+b²)`, projector `(1+cos φ σ₁+sin φ σ₂)/2` | proved: `TwoLevel.pauli_sq`, `pauli_charpoly`, `pauli_spectrum`, `projector_idempotent`, `projector_hermitian`, `projector_commutes` |
| `‖ḋ‖² = ρ̇² + Δ²g` and `ρ²χ̇² ≤ Δ²g` | proved: `TwoLevel.velocity_norm_sq_decomposition`, `chi_derivative_bound` |
| The 2×2 Hermitian form is positive semidefinite exactly on `0 ≤ a ∧ 0 ≤ c ∧ ω² ≤ 4(ac − b²)` | proved: `Positivity.H_posSemidef_iff`; the strict form `Positivity.H_posDef_iff` |
| Positive definiteness needs `0 < a` in addition to semidefiniteness | **refuted as I wrote it**: `Positivity.psd_and_positive_a_do_not_imply_posDef` and `positive_reduced_determinant_alone_does_not_imply_posDef`; the correct criterion is `H_posDef_iff` |
| At `a = c = 1`, `b = Γa`, `ω = 2Γb` the boundary is `Γa² + Γb² = 1`, with `Γ = 1/√2` on it | proved: `Positivity.unit_boundary_iff`, `equal_face_point`, `equal_face_point_is_boundary` |
| The conditioning `1/(1−Γa²−Γb²)` is at least one and increases towards the wall | proved: `Positivity.conditioning_ge_one`, `conditioning_strict_of_sum_lt` |
| The `Γ²` rate envelope peaks at `Γ² = 1/2` | proved: `Clock.hasDerivAt_sin_sq`, `Clock.envelope` |
| The angular rate is `(xẏ − yẋ)/(x² + y²)` and its numerator can vanish on a moving path | proved in a declared chart: `AngularRate.hasDerivAt_angle`, `progressing_path_with_zero_angular_numerator_and_no_origin`, `affinePath_isStuck_iff` |
| Reflectance `R > 1/2 ⟺ (n−3)² + κ² > 8` | proved: `Optical.reflectance_gt_half_iff`, `reflectance_lt_half_iff`, `reflectance_eq_half_iff` |
| Rice–Mele: `t₁²+t₂²+v² = 6t₁t₂`, and `t₂ = (3±2√2)t₁` at `v = 0` | proved: `Optical.rice_mele_energy_iff`, `rice_mele_zero_v_roots` |
| `(3+2√2)² = 17 + 12√2` | proved: `Optical.loop_ratio_squared` |
| `T/L ≤ ε_s` and `T/L > 3+2√2` give `ε_s > 17+12√2` | **refuted**: `Optical.squared_bound_as_written_false`; the valid consequence `ε_s > 3+2√2` is `threshold_bound_valid_consequence`, and the squared form needs `(T/L)² ≤ ε_s` (`squared_threshold_bound_corrected`) |
| `T > L` for `f x = x/(1+x)` | proved: `SumRule.f_lt_self`, `sum_f_lt_sum`, `lintegral_fENN_lt` (with `∫⁻ a ≠ ∞`, which `counting_measure_counterexample` shows is needed) |
| `L ≤ S/(1+S) < 1` and `1 < S/L` | proved: `Jensen.weighted_jensen`, `sum_rule_bounds`, `weighted_jensen_eq_iff` |

## The representation passage and the two-probe witness

| Claim | Status |
| :--- | :--- |
| The six weights `±P e_i` in three opposite pairs (the `3 ⊕ 3̄` weight multiset); the six roots are `e_i − e_j`; the adjoint's weights are those six plus two zeros | proved as statements about explicit finite vector sets: `A2.weightList_nodup`/`_length`, `A2.w_ne_neg_w`, `A2.rootList_nodup`/`_length`, `A2.rootList_opposite_pairs`, `A2.linear_relation_iff`, `A2.cartan_directions_independent`, `A2.adjointWeights_length` (= 8), `A2.adjointWeights_sum` (= 0). No representation or Lie algebra is defined, so `3 ⊕ 3̄` itself is not proved |
| The 48 integral quaternions of norm 5 | proved: `Quaternions.normSq_five_card`, with the coordinate bound `Quaternions.bounds_of_sq_le_five` making the enumeration complete |
| Those 48 "form six packets of eight", and 48 can also be read as three packets of sixteen | proved as a partition statement: `Quaternions.exists_equalPartition`, `normSq_five_six_block_partition`, `normSq_five_three_block_partition` — so the counts alone decide nothing |
| The norm-1 integral quaternions are 24 | **refuted**: the Hamilton units in `ℤ⁴` are 8 (`Quaternions.sol1_card`, `normSq_one_card`), and they do form a group (`qUnitsGroup`); the 24 needs the Hurwitz order with half-integer coordinates, which is not formalized |
| The phase state `(|01⟩ + e^{iΦ}|10⟩)/√2` has both marginals `I/2`, and the probes read `cos Φ`, `sin Φ` | proved: `TwoProbes.left_marginal`, `right_marginal`, `observations_eq`; the literal sign I wrote for the second probe is **refuted** (`requested_probeB_formula_is_false`) |
| `Φ` and `π−Φ` share the marginals but differ under the probes; the marginals determine nothing | proved: `TwoProbes.supplement_observations_ne`, `marginals_do_not_determine_phase`, `marginals_do_not_determine_state` |

## The framework's own statements (third round)

| Claim | Status |
| :--- | :--- |
| If the spacing depends only on the ratio and is additive over composition, it is `c * log` (continuous or monotone) | proved: `SpacingLaw.continuous_additive_eq_mul`, `continuousOn_multiplicative_eq_log`, `monotone_additive_eq_mul` |
| Two such laws are proportional, i.e. the law matches up to a unit | proved with the necessary nondegeneracy hypothesis: `SpacingLaw.multiplicative_laws_proportional_of_nondegenerate`; without it `SpacingLaw.proportionality_fails_without_nondegeneracy` |
| Additivity alone forces nothing more | proved by construction: `SpacingLaw.additivity_alone_does_not_suffice` (an additive map with `1 ↦ 0`, `√2 ↦ 1`) |
| `S = log((I+J)/(2√(IJ))) = log cosh(t/2) = −½log(1−Γ²)`, `S ≥ 0`, `S = ½log 2` at `Γ² = ½` | proved: `ScalarLedger.S_eq_log_cosh_half_t`, `S_eq_neg_half_log_one_sub_G_sq`, `S_nonneg`, `S_at_half_wall` |
| The peel keeps which way, the scalar keeps how much | proved: `ScalarLedger.G_swap`, `S_swap`, `strictMonoOn_S_abs` |
| An oscillator Lagrangian has Legendre transform `p²/2m + U` and conserves energy | proved: `Oscillator.legendre_hamiltonian_eq`, `energy_conservation`, `euler_lagrange_of_acceleration` |
| An oscillator Lagrangian imposes no null condition | proved: `Oscillator.free_lagrangian_has_nonnull_linear_solution`; the literal hypothesis `v ≠ c` is refuted in `nonnull_claim_as_written_false` (take `v = −c`) |
| Two lightlike momenta carry `E² − c²p² = 4E₊E₋`, and every positive timelike momentum splits into two null pieces | proved: `RestFrame.twoLightlike_invariant`, `exists_lightlike_decomposition`, `twoLightlike_invariant_vector`, `momentumVector_norm_le` |
| The conservative Hamiltonian block conserves energy but cannot produce Rayleigh dissipation | proved: `Hamiltonian.deriv_hamiltonian_conservative`, `deriv_hamiltonian_rayleigh_nonpos`, `conservative_cannot_produce_rayleigh_at_nonzero_momentum`, `rayleigh_forcing_not_configuration_gradient` |
| The local ruler alone does not fix the ledger | proved: `LocalRuler.ruler_scaling`, `ruler_one_strictAntiOn`, `ruler_right_slope`, `local_ruler_does_not_fix_ledger` |
| The two-field variation gives the coupled equations, and the printed signs fix the coupling | proved: `TwoFieldAction.firstVariation_eq_neg_elResidual_add_deriv`, `integral_firstVariation_eq_neg_integral_elResidual`, `elPair_eq_zero_iff` (density with `+g Φ K(ψ)`: right-hand sides `+g Φ K'`, `+g K`) and `elPair_neg_eq_zero_iff` (density with `−g Φ K(ψ)`: the printed `−g Φ K'`, `−g K`). A constant density changes nothing (`gateauxVariation_Ld_add_one`) and a total derivative contributes nothing (`integral_gateaux_totalDerivativeDensity_eq_zero`) |
| The IQGT splits into a metric and a 2-form, with the Wirtinger bound and the peel rate bound | proved: `QuantumGeometricTensor.Q_eq_metric_sub_curvature_mul_I`, `metric_symmetric`, `curvature_antisymmetric`, `wirtinger_inequality`, `Q_unitary_covariant`, `peel_rate_bound`, `wall_factor_eq_quarter_iff`; the real-part identity needs the complementary block (`crossBlock_only_counterexample`) and the rate bound needs `g ≥ 0` (`peel_rate_counterexample_without_nonnegative_metric`) |

## The colour side and the bridge (fourth round)

| Claim | Status |
| :--- | :--- |
| The Schrödinger split `(1/h) Σ dx_i²/x_i = (d log h)² + Σ dp_i²/p_i` | proved as an exact identity for every displacement: `Schrodinger.schrodinger_split` |
| The Fisher form on two channels is the round metric `dφ²` | proved away from the coordinate singularity: `Schrodinger.round_fisher`; the `φ = 0` form is **refuted** (`round_fisher_at_zero_ne_one`) because the first share vanishes there |
| The peel is minus the cosine of the chromatic angle | proved: `ChromaticAngle.share_balance_eq_peel`, `peel_eq_neg_cos` |
| The wall `Γ² = 1/2` is the chromatic angle 45° (and 135°) | proved on `[0, π]`: `ChromaticAngle.peel_sq_one_half_iff_wall` |
| The Hilbert-projective distance between two two-channel colours is the peel distance | proved: `ChromaticAngle.peelDistance_eq_abs_log_div`, `peelDistance_ratios` |
| Polarizer ports, balance `cos δ`, and the wall at `δ = π/4` | proved: `PolarizerPorts.crossed_add_parallel`, `parallel_sub_crossed`, `portPeel_eq_cos`, `wall_angles`, `secondary_balance_angle` |
| The determinant ledger is the sum of the per-channel scalar ledgers and is additive over blocks | proved: `MatrixLedger.Sm_eq_sum_scalar`, `Sm_eq_sum_log_cosh`, `Sm_append`, `channel_additive_ledger` |
| The scalar ledger is additive in the spacing | **refuted**: `MatrixLedger.scalarLedger_not_additive` (`t₁ = t₂ = 2`) |
| For two channels the determinant ledger is twice the scalar potential; `det = (1 − Γ²)/4`; the wall is `det = 1/8` | proved: `FisherMatrix.matrixLedger_eq_two_scalarLedgerPotential`, `shareMatrix_det_balance`, `shareMatrix_det_wall_iff`, `matrixLedger_at_wall` (= log 2) |
| The Fisher matrix is the inverse of the share matrix and is positive definite; covariance is its pseudoinverse on zero-sum tangents | proved: `FisherMatrix.fisherMatrix_mul_shareMatrix`, `fisherMatrix_posDef`, `fisherForm_eq_covariance` |
| Units-orbit structure of the colour wheel = divisor classes | proved for every `W > 0`: `ColourWheel.units_orbit_eq_setOf_gcd` |
| At `W = 10`: primaries `{1,3,7,9}`, secondaries `{2,4,6,8}`, grey `5`, base `0`; `Φ₁₀(x) = Φ₅(−x)` | proved: `ColourWheel.card_units_zmod10`, `orbit_two_zmod10`, `orbit_five_zmod10`, `cyclotomic_ten_eq_cyclotomic_five_comp_neg` |
| Grey is the kernel of doubling | **refuted as stated**: the kernel is `{0, 5}` (`doubling_kernel_zmod10_not_singleton`) |
| A wheel is viable iff `W = 2p` with `p` an odd prime | **refuted both ways** (`fourteen_counterexample_to_two_mul_odd_prime`, `five_counterexample_to_two_mul_odd_prime`); the true list below 30 is `W ∈ {5, 8, 10, 12}` (`card_units_eq_four_iff_of_le_thirty`) |
| A potential of the peel coordinate: force `−φ'(Γ)·2/(1+X)²·X'` | proved: `PeelPotential.potentialForce_eq`, `deriv_φled` |
| The ledger potential at the wall: value `½log2`, force `√2`, differentiable there | proved: `PeelPotential.φled_wall`, `deriv_φled_wall`, `differentiableAt_φled_wall`; the value twice that which I first wrote is **refuted** (`ledger_force_coefficient_at_wall_ne_two_mul_sqrt_two`) |
| The 2-jet at `Γ = 0` determines the bridge | **refuted**: `BridgeUnderdetermination.equal_two_jets_but_different_wall_forces`, `no_function_of_two_jet_computes_wall_force` |
| The phase motion gives `Γ` an equation of motion | proved: `PhaseBridge.peel_ode_of_phase_ode` (`Γ' = (ω/2)(1−Γ²)` from `z' = ωz`), and conversely `phase_ode_of_peel_ode` — the peel ODE *is* the uniform-log-ratio phase statement |
| A uniform chromatic angle makes the peel a harmonic oscillator | proved: `PhaseBridge.angle_peel_ode`, `angle_peel_harmonic` (`Γ'' = −ω²Γ`), `angle_speed_sq` (`(Γ')² = ω²(1−Γ²)`) |
| The ledger's rate along the peel motion is proportional to the peel | proved: `PhaseBridge.ledger_rate` (`S' = (ω/2)Γ`) |
| The bridge equation for the ledger, `S'' = (ω²/4)e^{−2S}` | proved: `PhaseBridge.ledger_second_order`, `ledger_speed_sq`, and it is the Euler–Lagrange equation of `½S'² − (ω²/8)e^{−2S}` (`ledger_is_euler_lagrange`) with conserved value `ω²/8` (`ledger_energy_eq`) |
| The angle phase gives the other bridge equation, `S'' = ω²e^{2S}` | proved: `PhaseBridge.angle_ledger_second_order`, with `angle_ledger_rate` (`S' = −ω cot φ`) |
| The equation of motion selects the ledger | **refuted**: the phase motion's potential in the peel coordinate is `(mω²/2)((1+Γ)/(1−Γ))²` (`PhaseBridge.harmPotInPeel_G`), which is not the ledger at `Γ = 0` (`potentials_differ_at_zero`) nor at the wall, `(mω²/2)(17+12√2)` against `½log2` (`harmPotInPeel_wall`, `potentials_differ_at_wall`) |
| The ledger is the log-determinant of the two shares | proved exactly: `PhaseBridge.φled_eq_log_det_shares` (`φled Γ = −½log(p₀p₁) − log2` when `Γ = p₀−p₁`, `p₀+p₁ = 1`), `two_φled_eq_neg_log_volume` |
| The wall has a clock | proved: `PhaseBridge.wall_clock` (log-ratio phase reaches it at `2log(1+√2)/ω`), `G_at_wall_ratio`, `G_at_conjugate_ratio`, `wall_ratio_sq` (the ratios there are `3 ± 2√2`), `angle_wall_clock` (`φ = π/4`) |
| Damping `t'' = −γt'` keeps the phase and dates the wall | proved: `DampedLedgerBridge.hasDerivAt_dampedPeel` (`Γ' = (ω/2)e^{−γτ}(1−Γ²)`), `hasDerivAt_dampedLedger` (`S' = (ω/2)e^{−γτ}Γ`), `strictMonoOn_dampedLedger`, `ledger_strict_increase_across_wall` (strict passage through `½log2`), `tendsto_dampedLedger` (finite endpoint `log cosh((t₀+ω/γ)/2)`) |
| The two phase motions predict different peel rates | proved: `PhaseBridge.peel_rate_at_zero_log_ratio` (`ω/2`), `peel_speed_sq_at_zero_angle` (`ω²`), `peel_rate_at_wall_log_ratio` (`ω/4`) |

| The oscillator's motion induces a closure ODE on `Γ` | proved: `PeelDynamics.peel_closure_ode` (`Γ''(1−Γ) + 2Γ'² + (ω²/2)(1−Γ)²(1+Γ) = 0` from `X'' + ω²X = 0`), with the exact first integral `peelEnergy_first_integral` and `hasDerivAt_peelEnergy` |
| The induced potential is not the ledger | proved: `PeelDynamics.inducedPotential_zero_ne_ledger`, `normalizedPotential_deriv_zero_ne_ledger` (slope `2mω²` against `0`), `normalizedPotential_wall_ne_ledger` (`8+6√2` against `½log2`) |
| The angle phase gives `S = −log|sin φ|` and `S'' = ω²e^{2S}` | proved: `UniformAngularBridge` (the closed form `Γ = −cos(ωτ+c)`, `(Γ')² = ω²(1−Γ²)`, the ledger identity, the second-order law, the exact first integral, and the vanishing Euler–Lagrange residual), with `U = −(ω²/2)e^{2S}` unbounded below |
| The wall is crossed exactly once in forward time | proved: `WallClock.existsUnique_forward_wall_crossing`, `peelFlow_eq_wall_iff`, `strictMono_peelFlow`; the crossing is at `wallTime ω = 2log(1+√2)/ω` (`wallTime_eq_log`, `artanh_wall`), at rate `ω/4` (`deriv_peelFlow_wallTime`), with `φled = ½log2` there (`ledger_at_wallTime`) |
| An append-additive readout of the normalised determinant must be `c·log`, and the wall reading fixes `c = −1` | proved: `CompositionBridge.eq_const_mul_log_of_append_additive`, `mul_add_of_append_additive`, `determinantReadout_append`, `determinantReadout_eq_neg_matrixLedger`, `coefficient_eq_neg_one_of_wall_normalization`, `determinantReadout_eq_matrixLedger_of_wall_normalization`. The scope is stated: the hypothesis is additivity of a *determinant* readout over channel blocks, with regularity. Append-additivity of a channel sum alone does **not** select the ledger — `append_additivity_alone_does_not_select_ledger` exhibits the ledger and `Γ²` as two admissible, different, even, zero-normalised examples |
| The proportional-rate readout is the ledger, up to an affine map | proved on all of `(−1,1)`: `ReadoutUniqueness.readout_eq_affine_ledger_of_rate` (`R = (2λ/ω)φled + R₀`), `readout_eq_ledger_of_normalized_rate`; the constant-rate readout is `ReadoutUniqueness.readout_eq_affine_artanh_of_constant_rate`, and `artanh_not_affine_ledger` says it is not affine in `φled` |
| The uniform log-ratio phase has the closed form `Γ = tanh(ωτ/2 + t₀/2)` and its bridge density is `T − U` | proved: `UniformLogRatio.phase_eq_affine`, `peel_closed_form`, `deriv_deriv_ledger_uniform`, `ledger_sq_deriv_eq`; the density with the sign I first wrote (`T + U`) is **refuted** there |
| A peel-dependent frequency destroys the oscillator's energy conservation, and constancy on an interval forces `ω∘Γ` constant | proved: `PhaseEnergyBalance.deriv_phaseEnergy_eq_frequencyWork` (rate `mωω'(Γ)q²Γ'`), `phaseEnergy_constOn_iff_frequency_comp_constOn`, `phaseDependent_eq_frozen_of_frequency_comp_const`, plus the witnesses `conserved_energy_does_not_force_global_frequency_constancy`, `nonzero_frequency_work_witness` |

## Not formalized here

* The physical interpretation of any of it: no Hamiltonian, surface, spectrum, optical constant,
  nuclear mass or measured width is derived.
* The grades, sources and revisions of the archive entries, and the display-rounding audit.
* The holmium–dysprosium calibration margin (`0.664383%`, first exhausted at charge 56): the two
  ladders, their widths and the neutral anchor are not in this repository.
* The full-spectrum moment analysis: `T = ∫ a`, `L = ∫ f(a)` with `1 < T/L ≤ ε_s`, the oscillator
  saturation and the ellipsoid bound `M_{N₁}/M_{N₂} ≤ √(N₂/N₁)`. `SumRule` and `Jensen` prove the
  finite and integral inequalities these rest on, not the dispersion-theoretic derivation.
* The knot section: `8_19 = T(3,4)`, the longitude `β = 1/2 − 6α`, the Levine–Tristram signatures
  of `13a_3542` and the mirror of `13a_4018`, and the arc-count formula. These need a knot theory
  library; the numbers can be looked up in KnotInfo but not proved there.
* The finite-block numerics (traces of 12 units, energy residuals of order `1e-14`, link weights)
  and the Russell octave tabulation.
