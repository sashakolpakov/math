import StickKnots.AsymptoticCertificate
import StickKnots.CertificationLogic
import StickKnots.Counting
import StickKnots.DoublyAlternating
import StickKnots.FewnomialBound
import StickKnots.Geometry
import StickKnots.LowerCertification
import StickKnots.ManuscriptArithmetic
import StickKnots.PolygonalCore
import StickKnots.StickUpperCertificate

/-!
# Conditional Lean certificate for stick-knot counting

The root imports the complete publication target and audits the principal
declarations.  Deep cited inputs are theorem parameters, never project axioms.
-/

/-! The declarations below should depend only on standard Lean/mathlib
foundations such as propositional extensionality, choice, and quotient
soundness. -/

#print axioms StickKnots.segment_intersection_implies_det_wall
#print axioms StickKnots.adjacent_improper_intersection_implies_crossSq_wall
#print axioms StickKnots.weighted_partial_choose_le
#print axioms StickKnots.Config.wallFree_embedded
#print axioms StickKnots.Config.wallFree_iff_forall_indexedWallPolynomial_ne_zero
#print axioms StickKnots.boundedStickKnot_count_le_unsliced
#print axioms StickKnots.factorial_fourth_power_le_card_doublyDownUp
#print axioms StickKnots.exists_doublyDownUp_word_endpoint_fiber
#print axioms StickKnots.KnotTransferCertificate.finite_stick_lower_bound
#print axioms StickKnots.certifiedKnotCount_finite_lower_at
#print axioms StickKnots.optimizedStirlingLowerLog_le_log_certifiedKnotCount
#print axioms StickKnots.certifiedKnotCount_log_isTheta
#print axioms StickKnots.eventually_coefficient_lower_bound_fixedWord
#print axioms StickKnots.eventually_optimized_deficit_lower_bound
#print axioms StickKnots.eventually_coefficient_upper_bound
#print axioms StickKnots.provedOptimizedDeficitArithmetic
#print axioms StickKnots.eventually_optimized_deficit_lower_bound_proved
