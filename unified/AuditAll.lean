/-
Axiom audit for every PROVED citation of the paper outside `Bridge/Audit.lean`: the
common-clock declarations, the VOTKP Smith identity and the Dirac-time gap theorem.
Same standard: propext, Classical.choice, Quot.sound only.
-/
import Unified

#print axioms CommonClockPeel.hasDerivAt_tanh
#print axioms CommonClockPeel.hasDerivAt_gapLedger
#print axioms CommonClockPeel.hasDerivAt_gapPeel
#print axioms CommonClockPeel.gam_gapRatio
#print axioms CommonClockPeel.real_common_clock_gap
#print axioms CommonClockPeel.gapPeel_of_common_gap
#print axioms CommonClockPeel.gapPeel_of_unit_energy_gap
#print axioms CommonClockPeel.two_level_common_gap
#print axioms CommonClockPeel.wall_pos
#print axioms CommonClockPeel.wall_sq
#print axioms CommonClockPeel.wall_mem_Ioo
#print axioms CommonClockPeel.gapPeel_eq_wall_iff
#print axioms CommonClockPeel.artanh_wall
#print axioms CommonClockPeel.two_artanh_wall
#print axioms CommonClockPeel.tanh_nonneg_of_nonneg
#print axioms CommonClockPeel.gapPeel_nonneg
#print axioms CommonClockPeel.gapPeel_neg_rate_sq
#print axioms CommonClockPeel.positive_gap_sq_wall_iff
#print axioms CommonClockPeel.existsUnique_forward_wall_iff
#print axioms CommonClockPeel.forward_wall_time_mul_abs_gap
#print axioms CommonClockPeel.forward_wall_time_mul_abs_gap_log
#print axioms CommonClockPeel.zero_gap_never_wall
#print axioms CommonClockPeel.affine_ledger_numerator
#print axioms CommonClockPeel.nonzero_gap_affine_readout_not_silent
#print axioms VOTKP.Smith.smith_identity
#print axioms DiracTime.CommonClock.common_gap_scaling
