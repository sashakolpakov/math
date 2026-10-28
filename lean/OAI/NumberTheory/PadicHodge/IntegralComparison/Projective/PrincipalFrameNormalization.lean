import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.PrincipalResidueCoordinates

/-! # Principal Frame Normalization -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.PrincipalFrameNormalization.Residue

noncomputable section

/-! Passing the actual projective scalar frame back to affine sections
recovers the same parameter adjunction frame. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial
open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R] {c g : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra
  ParameterNeighborhood.sectionAlgebra
variable (j : Fin (c+g+1)) (U : (IntrinsicOverlap.Intrinsic.space R (c+g)).Opens) (hU : IsAffineOpen U)
  (i : Fin (c+g+1)) (hi : U ≤ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i)
  (b : Module.Basis (Fin (c+g)) Γ(IntrinsicOverlap.Intrinsic.space R (c+g), U) Ω[Γ(IntrinsicOverlap.Intrinsic.space R (c+g), U)⁄R])

omit [IsNoetherianRing R] in
theorem lineIso_scalarFrame :
    Principal.OrientedResidueNormalizationBase.lineIso U hU
      (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (c+g+1))
      (PrincipalResidueCoordinates.scalarFrame j U hU i hi b) =
    ParameterAdjunction.parameterFrame j U hU i hi b :=
  Affine.LineFrameNormalization.PrincipalOrientedResidue.lineIso_sectionFrame U hU
    (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (c+g+1))
    (ParameterAdjunction.parameterFrame j U hU i hi b)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.PrincipalFrameNormalization.Residue
