import OAI.AlgebraicGeometry.SheafCohomology.Projective.PowerFrameTransition
import OAI.AlgebraicGeometry.SheafCohomology.Projective.HyperplaneFrameTransition

/-! # Hyperplane Power Frame Transition -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.HyperplanePowerFrameTransition.MvPolynomial

noncomputable section

open _root_.MvPolynomial

/-! The standard coordinate transition for every nonnegative hyperplane power. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {R : Type u} {σ : Type} [CommRing R]
attribute [local instance] MvPolynomial.gradedAlgebra

theorem coordinateHyperplanePolePower_frameTransition (i k j : σ) (n : ℕ) :
    DualFrameTransition.FrameTransition
      (OpenFrames.Scheme.Modules.restrictOpenTrivialization
        (CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_left (R := R) i k)
        (TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPowerTrivialization (R := R) i j n))
      (OpenFrames.Scheme.Modules.restrictOpenTrivialization
        (CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_right (R := R) i k)
        (TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPowerTrivialization (R := R) k j n))
      (UnitScalar.unitEndomorphismOfTopSection
        ((OpenFrames.Scheme.Modules.openTopSection (CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k)
          (CoordinateExtensions.MvPolynomial.coordinateOpenTransitionUnit (R := R) i k :
            Γ(Proj (homogeneousSubmodule σ R), CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k))) ^ n)) :=
  PowerFrameTransition.MvPolynomial.coordinateHyperplanePoleSheafPowerTrivializationOf_frameTransition
    (CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_left (R := R) i k)
    (CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_right (R := R) i k) j
    (HyperplaneFrames.MvPolynomial.coordinateHyperplanePoleSheafTrivialization (R := R) i j)
    (HyperplaneFrames.MvPolynomial.coordinateHyperplanePoleSheafTrivialization (R := R) k j)
    (OpenFrames.Scheme.Modules.openTopSection (CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k)
      (CoordinateExtensions.MvPolynomial.coordinateOpenTransitionUnit (R := R) i k :
        Γ(Proj (homogeneousSubmodule σ R), CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k)))
    (HyperplaneFrameTransition.MvPolynomial.coordinateHyperplanePole_frameTransition (R := R) i k j) n

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.HyperplanePowerFrameTransition.MvPolynomial
