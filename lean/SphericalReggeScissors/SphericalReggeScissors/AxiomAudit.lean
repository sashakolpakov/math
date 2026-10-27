/-
Discussions and model prompting: Alexander Kolpakov (UATX).

Source: sashakolpakov/spherical-regge-scissors, commit
d40eb8990bcf1ba5525435f8517e9ba5c202b549.
-/

import SphericalReggeScissors

/-!
# Public trust audit

Compiling this module prints the axiom dependencies of the algebraic core,
contract deductions, final theorem, and specification models.  The repository
checker accepts only Lean's standard logical foundations.
-/

namespace SphericalReggeScissors

#print axioms reggeMatrix_mul_self
#print axioms reggeMatrix_orthogonal
#print axioms PhasePoint.regge_involutive
#print axioms gramMatrix_det
#print axioms gramMatrix_det_quadratic
#print axioms determinantB_regge_invariant
#print axioms determinantC_regge_invariant
#print axioms chart_cover
#print axioms fixedPhase_deck_preserves_root
#print axioms six_channel_tensor_invariance
#print axioms coproduct_of_regge_difference_eq_zero
#print axioms primitive_eq_zero
#print axioms universal_framed_defect_vanishes
#print axioms contract_universal_coproduct_zero
#print axioms contract_quadric_dual_defect_is_primitive
#print axioms goncharov_spherical_defect_vanishes
#print axioms reduced_rational_defect_vanishes_of_presentation
#print axioms integral_reduced_defect_vanishes
#print axioms full_defect_vanishes
#print axioms spherical_regge_scissors
#print axioms finiteContract
#print axioms equal_volume_does_not_force_scissors_class

end SphericalReggeScissors
