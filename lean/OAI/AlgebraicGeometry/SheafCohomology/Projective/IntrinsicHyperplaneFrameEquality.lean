import OAI.AlgebraicGeometry.SheafCohomology.Projective.HyperplaneFrames

/-! # Intrinsic Hyperplane Frame Equality -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.IntrinsicHyperplaneFrameEquality.MvPolynomial

noncomputable section

open _root_.MvPolynomial

/-! The chosen native pole frame is the dual of the chosen ideal frame. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {R : Type u} {σ : Type} [CommRing R]
attribute [local instance] MvPolynomial.gradedAlgebra

theorem coordinateHyperplanePoleNativeFrame_eq (i j : σ) :
    HyperplaneFrames.MvPolynomial.coordinateHyperplanePoleSheafTrivialization (R := R) i j =
    Dual.Scheme.Modules.dualRestrictIsoOfRestrictIso
      (IdealModule.idealModule (SpaceHyperplane.MvPolynomial.coordinateHyperplaneι (R := R) j))
      (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i)
      (HyperplaneFrames.MvPolynomial.coordinateHyperplaneIdealModuleTrivialization (R := R) i j).symm := rfl

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.IntrinsicHyperplaneFrameEquality.MvPolynomial
