import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProjectiveCoordinatesApp
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.TensorPullback
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.PicardPowersAdd
import OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistPowers

/-! # Universal Powers -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.UniversalPowers

noncomputable section

/-! Projective twists and universal multilinear line-bundle powers agree over any coefficient ring. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
namespace Dimension

universe u
variable {R : Type u} [CommRing R] {σ : Type}
attribute [local instance] MvPolynomial.gradedAlgebra

def projectiveTwistUniversalPowerIso (j : σ) : (n : ℕ) →
    TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n ≅
      ((Quotients.FiniteDescent.ProjectiveCoordinatesApp.Construction.ProjectiveCoordinates.bundle (R := R) j).tensorPower n).sheaf
  | 0 => TensorSections.monoidalUnitObjIso _ ≪≫
      (show Nonempty (((Quotients.FiniteDescent.ProjectiveCoordinatesApp.Construction.ProjectiveCoordinates.bundle (R := R) j).tensorPower 0).sheaf ≅
        AbelianModuli.HilbertConstruction.Line.Bundles.structureModule _) from Quotient.exact
          (Quotients.FiniteDescent.PicardPowersAdd.Construction.PicardPowers.class_zero (Quotients.FiniteDescent.ProjectiveCoordinatesApp.Construction.ProjectiveCoordinates.bundle (R := R) j))).some.symm
  | n + 1 => TensorSections.monoidalTensorObjIso _ _ ≪≫
      AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr (projectiveTwistUniversalPowerIso j n)
        ((((Quotients.FiniteDescent.ProjectiveCoordinatesApp.Construction.ProjectiveCoordinates.bundle (R := R) j).tensorPower_isTensorPower 1).unique
          (AbelianModuli.HilbertConstruction.Tensor.Powers.isTensorPower_one _)).some.symm) ≪≫
        (Quotients.FiniteDescent.TensorPower.Construction.TensorPowerAddition.iso
          (Quotients.FiniteDescent.ProjectiveCoordinatesApp.Construction.ProjectiveCoordinates.bundle (R := R) j).sheaf n 1).symm

def pullbackProjectiveTwistUniversalIso {X : Scheme.{u}}
    (f : X ⟶ Proj (MvPolynomial.homogeneousSubmodule σ R)) (j : σ)
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X)
    (e : (Scheme.Modules.pullback f).obj (Quotients.FiniteDescent.ProjectiveCoordinatesApp.Construction.ProjectiveCoordinates.bundle (R := R) j).sheaf ≅
      L.sheaf) (n : ℕ) :
    (Scheme.Modules.pullback f).obj
        (TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n) ≅
      (L.tensorPower n).sheaf :=
  (Scheme.Modules.pullback f).mapIso (Dimension.projectiveTwistUniversalPowerIso j n) ≪≫
    Quotients.FiniteDescent.TensorPullback.Construction.TensorPullbackMap.iso f (Quotients.FiniteDescent.ProjectiveCoordinatesApp.Construction.ProjectiveCoordinates.bundle (R := R) j) n ≪≫
      (AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerFunctor X n).mapIso e

end Dimension

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.UniversalPowers
