import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.TensorPowerComparison
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.LineBundleTensorPullback
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProjectiveCoordinatesApp
import OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistPowers

/-! # Projective Twist Comparison -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ProjectiveTwistComparison.Construction

noncomputable section

/-! Compare projective twists with the actual tensor powers used by Openness. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

def sheafTensorPowerCongr {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N) :
    (n : ℕ) → TensorRestriction.Construction.sheafTensorPower M n ≅ TensorRestriction.Construction.sheafTensorPower N n
  | 0 => Iso.refl _
  | n + 1 => SheafTensor.Construction.sheafTensorCongr (sheafTensorPowerCongr e n) e

variable {R : Type u} [CommRing R] {σ : Type}
attribute [local instance] MvPolynomial.gradedAlgebra

def projectiveTwistTensorPowerIso (j : σ) : (n : ℕ) →
    AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n ≅
      TensorRestriction.Construction.sheafTensorPower (AlgebraicGeometry.Quotients.FiniteDescent.ProjectiveCoordinatesApp.Construction.ProjectiveCoordinates.bundle (R := R) j).sheaf n
  | 0 => AlgebraicGeometry.SheafCohomology.Projective.TensorSections.monoidalUnitObjIso _
  | n + 1 => AlgebraicGeometry.SheafCohomology.Projective.TensorSections.monoidalTensorObjIso _ _ ≪≫
      SheafTensor.Construction.sheafTensorCongr (projectiveTwistTensorPowerIso j n) (Iso.refl _)

def pullbackProjectiveTwistIso {X : Scheme.{u}}
    (f : X ⟶ Proj (MvPolynomial.homogeneousSubmodule σ R)) (j : σ)
    (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X)
    (e : (Scheme.Modules.pullback f).obj (AlgebraicGeometry.Quotients.FiniteDescent.ProjectiveCoordinatesApp.Construction.ProjectiveCoordinates.bundle (R := R) j).sheaf ≅
      L.sheaf) (n : ℕ) :
    (Scheme.Modules.pullback f).obj (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n) ≅
      (L.tensorPower n).sheaf :=
  (Scheme.Modules.pullback f).mapIso (Construction.projectiveTwistTensorPowerIso j n) ≪≫
    LineBundleTensorPullback.Construction.pullbackLineBundleTensorPowerIso f (AlgebraicGeometry.Quotients.FiniteDescent.ProjectiveCoordinatesApp.Construction.ProjectiveCoordinates.bundle (R := R) j).locallyTrivial n ≪≫
      Construction.sheafTensorPowerCongr e n ≪≫ (TensorPowerComparison.Construction.lineBundleTensorPowerComparison L n).symm

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ProjectiveTwistComparison.Construction
