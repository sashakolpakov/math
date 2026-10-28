import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FixedDimension.PointData
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Fixed.GroupUniversalRecovery
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GroupPullbackComposition

/-! # Universal Recovery -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Fixed.UniversalRecovery

noncomputable section

/-! Native abelian point data are recovered from the actual universal
abelian family, including preservation of the group operations. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (S : Scheme.{u}) [IsNoetherian S] (n : ℕ) (P : Polynomial ℚ) (g : ℕ) (Pm Pi : Polynomial ℚ)

local instance abelianRecoveryUniversalGroup :
    GrpObj (FixedDimension.GroupParameters.fixedDimensionHilbertGroupUniversalFamily S n P g Pm Pi) :=
  FixedDimension.GroupParameters.fixedDimensionHilbertGroupUniversalGroupObj S n P g Pm Pi

variable {T : Over S} (y : T ⟶ FixedDimension.AbelianParameters.fixedDimensionHilbertAbelianParameter S n P g Pm Pi)

def fixedDimensionHilbertAbelianPointFamilyIso :
    ((FixedDimension.AbelianParameters.fixedDimensionHilbertUniversalAbelianScheme S n P g Pm Pi).pullback y.left).scheme ≅
      ((FixedDimension.PointData.fixedDimensionHilbertAbelianNativePointEquiv S n P g Pm Pi T y).abelianScheme S n P g Pm Pi).scheme :=
  (GroupPullbackComposition.groupPullbackCompIso (FixedDimension.GroupParameters.fixedDimensionHilbertGroupUniversalFamily S n P g Pm Pi)
    (FixedDimension.AbelianParameters.fixedDimensionHilbertAbelianParameterInclusion S n P g Pm Pi).left y.left).symm ≪≫
      GroupUniversalRecovery.fixedDimensionHilbertGroupPointFamilyIso S n P g Pm Pi
        (y ≫ FixedDimension.AbelianParameters.fixedDimensionHilbertAbelianParameterInclusion S n P g Pm Pi)

instance fixedDimensionHilbertAbelianPointFamilyIso_isMonHom :
    IsMonHom (fixedDimensionHilbertAbelianPointFamilyIso S n P g Pm Pi y).hom := by
  let : GrpObj (FixedDimension.GroupParameters.fixedDimensionHilbertGroupUniversalFamily S n P g Pm Pi) :=
    FixedDimension.GroupParameters.fixedDimensionHilbertGroupUniversalGroupObj S n P g Pm Pi
  let : GrpObj ((FixedDimension.GroupPointData.fixedDimensionHilbertGroupPointEquiv S n P g Pm Pi T
      (y ≫ FixedDimension.AbelianParameters.fixedDimensionHilbertAbelianParameterInclusion S n P g Pm Pi)).family S n P g Pm Pi) :=
    (FixedDimension.GroupPointData.fixedDimensionHilbertGroupPointEquiv S n P g Pm Pi T
      (y ≫ FixedDimension.AbelianParameters.fixedDimensionHilbertAbelianParameterInclusion S n P g Pm Pi)).groupObj S n P g Pm Pi
  let : IsMonHom (GroupUniversalRecovery.fixedDimensionHilbertGroupPointFamilyIso S n P g Pm Pi
      (y ≫ FixedDimension.AbelianParameters.fixedDimensionHilbertAbelianParameterInclusion S n P g Pm Pi)).hom :=
    GroupUniversalRecovery.fixedDimensionHilbertGroupPointFamilyIso_isMonHom S n P g Pm Pi
      (y ≫ FixedDimension.AbelianParameters.fixedDimensionHilbertAbelianParameterInclusion S n P g Pm Pi)
  let : IsMonHom
      (GroupPullbackComposition.groupPullbackCompIso (FixedDimension.GroupParameters.fixedDimensionHilbertGroupUniversalFamily S n P g Pm Pi)
        (FixedDimension.AbelianParameters.fixedDimensionHilbertAbelianParameterInclusion S n P g Pm Pi).left y.left).inv :=
    GroupPullbackComposition.groupPullbackCompIso_inv_isMonHom
      (FixedDimension.GroupParameters.fixedDimensionHilbertGroupUniversalFamily S n P g Pm Pi)
      (FixedDimension.AbelianParameters.fixedDimensionHilbertAbelianParameterInclusion S n P g Pm Pi).left y.left
  exact CategoryTheory.instIsMonHomComp
    (GroupPullbackComposition.groupPullbackCompIso (FixedDimension.GroupParameters.fixedDimensionHilbertGroupUniversalFamily S n P g Pm Pi)
      (FixedDimension.AbelianParameters.fixedDimensionHilbertAbelianParameterInclusion S n P g Pm Pi).left y.left).inv
    (GroupUniversalRecovery.fixedDimensionHilbertGroupPointFamilyIso S n P g Pm Pi
      (y ≫ FixedDimension.AbelianParameters.fixedDimensionHilbertAbelianParameterInclusion S n P g Pm Pi)).hom

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Fixed.UniversalRecovery
