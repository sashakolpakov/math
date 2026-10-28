import OAI.AlgebraicGeometry.SheafCohomology.Projective.DualFrameTransition
import OAI.AlgebraicGeometry.SheafCohomology.Projective.HyperplaneTransitions
import OAI.AlgebraicGeometry.SheafCohomology.Projective.IntrinsicHyperplaneFrameEquality

/-! # Hyperplane Frame Transition -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.HyperplaneFrameTransition.MvPolynomial

noncomputable section

open _root_.MvPolynomial

/-! The coordinate pole-frame transition as a relation on the frames themselves. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {R : Type u} {σ : Type} [CommRing R]
attribute [local instance] MvPolynomial.gradedAlgebra

theorem coordinateHyperplanePole_frameTransition (i k j : σ) :
    DualFrameTransition.FrameTransition
      (OpenFrames.Scheme.Modules.restrictOpenTrivialization
        (CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_left (R := R) i k)
        (HyperplaneFrames.MvPolynomial.coordinateHyperplanePoleSheafTrivialization (R := R) i j))
      (OpenFrames.Scheme.Modules.restrictOpenTrivialization
        (CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_right (R := R) i k)
        (HyperplaneFrames.MvPolynomial.coordinateHyperplanePoleSheafTrivialization (R := R) k j))
      (UnitScalar.unitEndomorphismOfTopSection
        (OpenFrames.Scheme.Modules.openTopSection (CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k)
          (CoordinateExtensions.MvPolynomial.coordinateOpenTransitionUnit (R := R) i k :
            Γ(Proj (homogeneousSubmodule σ R), CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k)))) :=
  DualFrameTransition.dualOpenOverlap_frameTransition
    (X := Proj (homogeneousSubmodule σ R))
    (U := MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i) (V := MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) k)
    (W := CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k)
    (IdealModule.idealModule (SpaceHyperplane.MvPolynomial.coordinateHyperplaneι (R := R) j))
    (CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_left (R := R) i k)
    (CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_right (R := R) i k)
    (HyperplaneFrames.MvPolynomial.coordinateHyperplaneIdealModuleTrivialization (R := R) i j).symm
    (HyperplaneFrames.MvPolynomial.coordinateHyperplaneIdealModuleTrivialization (R := R) k j).symm
    (HyperplaneFrames.MvPolynomial.coordinateHyperplanePoleSheafTrivialization (R := R) i j)
    (HyperplaneFrames.MvPolynomial.coordinateHyperplanePoleSheafTrivialization (R := R) k j)
    (IntrinsicHyperplaneFrameEquality.MvPolynomial.coordinateHyperplanePoleNativeFrame_eq (R := R) i j)
    (IntrinsicHyperplaneFrameEquality.MvPolynomial.coordinateHyperplanePoleNativeFrame_eq (R := R) k j)
    (CoordinateExtensions.MvPolynomial.coordinateOpenTransitionUnit (R := R) i k :
      Γ(Proj (homogeneousSubmodule σ R), CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k))
    (HyperplaneTransitions.MvPolynomial.coordinateHyperplaneIdealOver_restrict_transition (R := R) i k j)

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.HyperplaneFrameTransition.MvPolynomial
