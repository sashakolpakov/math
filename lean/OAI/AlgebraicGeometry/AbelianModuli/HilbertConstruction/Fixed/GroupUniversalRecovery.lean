import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FixedDimension.GroupPointData
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.GroupUniversalFamilyRecovery

/-! # Group Universal Recovery -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Fixed.GroupUniversalRecovery

noncomputable section

/-! A point of the global Hilbert group parameter recovers the native
pullback of the universal family as a group scheme. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (S : Scheme.{u}) [IsNoetherian S] (n : ℕ) (P : Polynomial ℚ) (g : ℕ) (Pm Pi : Polynomial ℚ)
variable {T : Over S} (y : T ⟶ FixedDimension.GroupGlobalParameter.fixedDimensionHilbertGroupParameter S n P g Pm Pi)

def fixedDimensionHilbertGroupPointRelativeMap :
    Over.mk ((FixedDimension.GroupPointData.fixedDimensionHilbertGroupPointEquiv S n P g Pm Pi T y).1.left) ⟶
      FixedDimension.GroupParameters.fixedDimensionHilbertGroupRelativeParameter S n P g Pm Pi :=
  (CompositeParameterPoints.compositeParameterPointEquiv (FixedDimension.Parameters.fixedDimensionHilbertParameter S n P g)
    (FixedDimension.GroupParameters.fixedDimensionHilbertGroupRelativeParameter S n P g Pm Pi) T y).2

def fixedDimensionHilbertGroupPointFamilyIso :
    (Over.pullback y.left).obj (FixedDimension.GroupParameters.fixedDimensionHilbertGroupUniversalFamily S n P g Pm Pi) ≅
      (FixedDimension.GroupPointData.fixedDimensionHilbertGroupPointEquiv S n P g Pm Pi T y).family S n P g Pm Pi :=
  Bounded.GroupUniversalFamilyRecovery.boundedFamilyGroupNativeUniversalFamilyIso
    (FixedDimension.GroupParameters.fixedDimensionHilbertMultiplicationPresentation S n P g).embedding
    (FixedDimension.GroupParameters.fixedDimensionHilbertInversionPresentation S n P g).embedding Pm Pi
    (FixedDimension.Family.fixedDimensionHilbertUniversalProjectivePresentation S n P g).quasiProjective
    (fixedDimensionHilbertGroupPointRelativeMap S n P g Pm Pi y)

theorem fixedDimensionHilbertGroupPointFamilyIso_isMonHom :
    letI : GrpObj (FixedDimension.GroupParameters.fixedDimensionHilbertGroupUniversalFamily S n P g Pm Pi) :=
      FixedDimension.GroupParameters.fixedDimensionHilbertGroupUniversalGroupObj S n P g Pm Pi
    letI : GrpObj ((FixedDimension.GroupPointData.fixedDimensionHilbertGroupPointEquiv S n P g Pm Pi T y).family S n P g Pm Pi) :=
      (FixedDimension.GroupPointData.fixedDimensionHilbertGroupPointEquiv S n P g Pm Pi T y).groupObj S n P g Pm Pi
    IsMonHom (fixedDimensionHilbertGroupPointFamilyIso S n P g Pm Pi y).hom :=
  Bounded.GroupUniversalFamilyRecovery.boundedFamilyGroupNativeUniversalFamilyIso_isMonHom
    (FixedDimension.GroupParameters.fixedDimensionHilbertMultiplicationPresentation S n P g).embedding
    (FixedDimension.GroupParameters.fixedDimensionHilbertInversionPresentation S n P g).embedding Pm Pi
    (FixedDimension.Family.fixedDimensionHilbertUniversalProjectivePresentation S n P g).quasiProjective
    (fixedDimensionHilbertGroupPointRelativeMap S n P g Pm Pi y)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Fixed.GroupUniversalRecovery
