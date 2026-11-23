/-
Axiom audit for every declaration added by the three bridge modules.  Same standard as the
three legs: `propext`, `Classical.choice`, `Quot.sound` and nothing else — no `sorry`, no
project axiom, no `native_decide`.
-/
import Unified
open Unified.Bridge

#print axioms Reflection.log_wall_ratio
#print axioms Reflection.wall_ledger_value
#print axioms Reflection.tanh_ledger_descent
#print axioms Reflection.one_sub_gam_sq_eq_four_det
#print axioms Reflection.wall_iff_share_det
#print axioms Reflection.gam_sq_eq_one_iff_det_zero
#print axioms Reflection.two_smith_identities
#print axioms Reflection.tanh_double_eq_oplus

#print axioms Chirality.odd_involution_vanishes
#print axioms Chirality.theta_vanishes_on_amphichiral
#print axioms Chirality.odd_does_not_imply_converse
#print axioms Chirality.gam_mirror
#print axioms Chirality.even_readout_blind
#print axioms Chirality.wall_indicator_blind
#print axioms Chirality.wall_is_chiral
#print axioms Chirality.mirror_fixed_iff_gam_eq_zero

#print axioms Quotient.peelL_apply
#print axioms Quotient.peelR_apply
#print axioms Quotient.unseen_eq_unobservable
#print axioms Quotient.same_future_iff_votkp
#print axioms Quotient.peel_unobservable_eq_bot
#print axioms Quotient.peel_predictive_dim
#print axioms Quotient.wall_is_not_a_memory_transition
#print axioms Quotient.peel_closes

#print axioms Composition.wall_pos
#print axioms Composition.log_prod_eq_sum
#print axioms Composition.composite_reflection_eq
#print axioms Composition.composite_two_eq_oplus
#print axioms Composition.crosses_iff_ledger_sum
#print axioms Composition.window_at_wall_ledger
#print axioms Composition.two_halves_cross
#print axioms Composition.geomean_lt_wall
#print axioms Composition.composition_crosses_mean_does_not

#print axioms Faces.faceRatio_pos
#print axioms Faces.faceRatio_eq_gam
#print axioms Faces.faceGamma_sq_eq_half_iff
#print axioms Faces.faceGamma_sq_eq_half_iff_odd
#print axioms Faces.faceGamma_lt_one
#print axioms Faces.brouncker_first_face
