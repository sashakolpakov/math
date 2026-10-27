/-
Discussions and model prompting: Alexander Kolpakov (UATX).

Source: sashakolpakov/spherical-regge-scissors, commit
d40eb8990bcf1ba5525435f8517e9ba5c202b549.
-/

import SphericalReggeScissors.ContractAudit

/-!
# Conditional spherical Regge scissors theorem

This module assembles the complete internal implication chain.  Its sole
argument is an explicit `ProofContract`; consequently `#print axioms`
reports no project axioms for any public result.
-/

namespace SphericalReggeScissors

universe uU uM uL uA uH uF uQ uQM uK uP uS uR uRQ uG uT uPiece

section MainTheorem

variable {Universal : Type uU} {Middle : Type uM} {H1 : Type uH}
variable {LeftFactor : Type uL} {RightFactor : Type uA}
variable {Fibre : Type uF} {Quadric : Type uQ} {QuadricMiddle : Type uQM}
variable {K3 : Type uK}
variable {Plane : Type uP} {Full : Type uS} {Reduced : Type uR}
variable {ReducedRational : Type uRQ}
variable {SphericalPresentation : Type uG}
variable {Tetrahedron : Type uT}
variable {Piece : Type uPiece}
variable [AddCommGroup Universal] [Module ℚ Universal]
variable [AddCommGroup Middle] [Module ℚ Middle]
variable [AddCommGroup LeftFactor] [Module ℚ LeftFactor]
variable [AddCommGroup RightFactor] [Module ℚ RightFactor]
variable [AddCommGroup H1] [Module ℚ H1]
variable [AddCommGroup Fibre] [Module ℚ Fibre]
variable [AddCommGroup Quadric] [Module ℚ Quadric]
variable [AddCommGroup QuadricMiddle] [Module ℚ QuadricMiddle]
variable [AddCommGroup K3] [Module ℚ K3]
variable [AddCommGroup Plane] [AddCommGroup Full] [AddCommGroup Reduced]
variable [AddCommGroup ReducedRational] [Module ℚ ReducedRational]
variable [AddCommGroup SphericalPresentation] [Module ℚ SphericalPresentation]

variable (C : ProofContract Universal Middle LeftFactor RightFactor H1 Fibre
  Quadric QuadricMiddle K3 Plane Full Reduced ReducedRational
  SphericalPresentation Tetrahedron Piece)

/-- The universal relative framed defect vanishes. -/
theorem contract_universal_defect_zero : C.universalDefect = 0 :=
  universal_framed_defect_vanishes C.motivic C.universalDefect (by
    rw [C.universal_defect_is_difference]
    exact coproduct_of_regge_difference_eq_zero C.motivic C.coproductBridge)

/-- The universal defect also has zero reduced coproduct. -/
theorem contract_universal_coproduct_zero :
    C.motivic.coproduct C.universalDefect = 0 := by
  rw [C.universal_defect_is_difference]
  exact coproduct_of_regge_difference_eq_zero C.motivic C.coproductBridge

/-- Fibre primitivity is derived from the commuting specialization square,
not supplied as a standalone hypothesis. -/
theorem contract_quadric_dual_defect_is_primitive :
    C.quadricDualDefect ∈ C.specialization.quadricCoproduct.ker := by
  change C.specialization.quadricCoproduct C.quadricDualDefect = 0
  rw [C.quadric_coproduct_specialization,
    contract_universal_coproduct_zero C]
  simp

/-- The specialized defect first vanishes in Goncharov's spherical
presentation. -/
theorem contract_goncharov_spherical_defect_zero :
    C.goncharovSphericalDefect = 0 := by
  apply goncharov_spherical_defect_vanishes C.specialization
    C.universalDefect C.quadricDualDefect C.goncharovSphericalDefect
    (contract_quadric_dual_defect_is_primitive C)
    (contract_universal_defect_zero C)
    (C.fibre_endpoint_eq_cG (contract_quadric_dual_defect_is_primitive C))
    C.duality_comparison

/-- The explicit E7 presentation isomorphism transports that identity to
the rationalized reduced spherical scissors group. -/
theorem contract_reduced_rational_defect_zero :
    C.reducedRationalDefect = 0 := by
  exact reduced_rational_defect_vanishes_of_presentation
    C.presentationComparison C.reducedRationalDefect
    C.goncharovSphericalDefect
    (contract_goncharov_spherical_defect_zero C)
    C.presentation_defect_comparison

/-- Unique divisibility (presented as injectivity of rationalization in
the contract) descends the preceding vanishing to the integral reduced
scissors group. -/
theorem contract_reduced_defect_zero : C.reducedDefect = 0 := by
  exact integral_reduced_defect_vanishes C.scissors C.reducedDefect
    C.reducedRationalDefect (contract_reduced_rational_defect_zero C)
    C.rationalization_comparison

/-- The Regge difference vanishes in the full spherical scissors group. -/
theorem contract_full_defect_zero :
    C.scissors.scissorsClass C.original -
      C.scissors.scissorsClass C.reggeMate = 0 := by
  let z := C.scissors.scissorsClass C.original -
    C.scissors.scissorsClass C.reggeMate
  have hReduced : C.scissors.reduction z = 0 := by
    rw [← C.reduced_comparison]
    exact contract_reduced_defect_zero C
  have hVolume : C.scissors.volume z = 0 := by
    exact volume_defect_vanishes C.scissors C.regge_volume
  exact full_defect_vanishes C.scissors z hReduced hVolume

/--
The manuscript's main proposition, conditional only on the explicitly
bundled external theorem contract: an elementary spherical Regge pair has
a finite spherical equidecomposition.
-/
theorem spherical_regge_equidecomposable :
    Nonempty (FiniteEquidecomposition Tetrahedron Piece
      C.scissors.decomposes C.scissors.pieceIsometric
      C.original C.reggeMate) := by
  apply equidecomposable_of_full_defect_zero C.scissors
  exact contract_full_defect_zero C

/-- Canonical theorem name matching the public repository and the
manuscript's main statement. -/
theorem spherical_regge_scissors :
    Nonempty (FiniteEquidecomposition Tetrahedron Piece
      C.scissors.decomposes C.scissors.pieceIsometric
      C.original C.reggeMate) :=
  spherical_regge_equidecomposable C

end MainTheorem

-- These commands are a machine-checked audit of the trusted basis.
#print axioms primitive_eq_zero
#print axioms universal_framed_defect_vanishes
#print axioms coproduct_of_regge_difference_eq_zero
#print axioms goncharov_spherical_defect_vanishes
#print axioms reduced_rational_defect_vanishes_of_presentation
#print axioms integral_reduced_defect_vanishes
#print axioms full_defect_vanishes
#print axioms spherical_regge_scissors
#print axioms finiteContract
#print axioms equal_volume_does_not_force_scissors_class

end SphericalReggeScissors
