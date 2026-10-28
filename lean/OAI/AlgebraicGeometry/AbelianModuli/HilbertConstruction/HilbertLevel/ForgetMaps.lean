import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FixedDimension.LevelParameters

/-! # Forget Maps -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.HilbertLevel.ForgetMaps

noncomputable section

/-! The original bounded full-level Hilbert parameter has explicit
forgetful maps to its abelian and fixed-dimension Hilbert parameters.
The maps agree with the corresponding components of its point data. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable (S : Scheme.{u}) [IsNoetherian S] (n : ℕ) (P : Polynomial ℚ) (g : ℕ) (Pm Pi : Polynomial ℚ)

def fixedDimensionHilbertAbelianHilbertMap :
    FixedDimension.AbelianParameters.fixedDimensionHilbertAbelianParameter S n P g Pm Pi ⟶ FixedDimension.Parameters.fixedDimensionHilbertParameter S n P g :=
  FixedDimension.AbelianParameters.fixedDimensionHilbertAbelianParameterInclusion S n P g Pm Pi ≫
    FixedDimension.GroupGlobalParameter.fixedDimensionHilbertGroupHilbertMap S n P g Pm Pi

theorem fixedDimensionHilbertAbelianNativePoint_hilbert {T : Over S}
    (y : T ⟶ FixedDimension.AbelianParameters.fixedDimensionHilbertAbelianParameter S n P g Pm Pi) :
    (FixedDimension.PointData.fixedDimensionHilbertAbelianNativePointEquiv S n P g Pm Pi T y).val.1 =
      y ≫ fixedDimensionHilbertAbelianHilbertMap S n P g Pm Pi := by
  change (y ≫ FixedDimension.AbelianParameters.fixedDimensionHilbertAbelianParameterInclusion S n P g Pm Pi) ≫
    FixedDimension.GroupGlobalParameter.fixedDimensionHilbertGroupHilbertMap S n P g Pm Pi = _
  exact Category.assoc _ _ _

variable (N : ℕ) [NeZero N]

def fixedDimensionHilbertFullLevelAbelianMap :
    FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameter S n P g Pm Pi N ⟶
      FixedDimension.AbelianParameters.fixedDimensionHilbertAbelianParameter S n P g Pm Pi :=
  CompositeParameterPoints.compositeParameterProjection (FixedDimension.AbelianParameters.fixedDimensionHilbertAbelianParameter S n P g Pm Pi)
    (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelRelativeParameter S n P g Pm Pi N)

def fixedDimensionHilbertFullLevelHilbertMap :
    FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameter S n P g Pm Pi N ⟶ FixedDimension.Parameters.fixedDimensionHilbertParameter S n P g :=
  fixedDimensionHilbertFullLevelAbelianMap S n P g Pm Pi N ≫
    fixedDimensionHilbertAbelianHilbertMap S n P g Pm Pi

theorem fixedDimensionHilbertFullLevelPoint_abelian {T : Over S}
    (y : T ⟶ FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameter S n P g Pm Pi N) :
    (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameterPointEquiv S n P g Pm Pi N T y).1 =
      y ≫ fixedDimensionHilbertFullLevelAbelianMap S n P g Pm Pi N := rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.HilbertLevel.ForgetMaps
