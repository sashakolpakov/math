import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FixedDimension.LevelParameters
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.UniversalFamilyRecovery

/-! # Level Universal Recovery -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Fixed.LevelUniversalRecovery

noncomputable section

/-! A point of the global full-level Hilbert parameter recovers both the
universal abelian family and its actual universal ordered level. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable (S : Scheme.{u}) [IsNoetherian S] (n : ℕ) (P : Polynomial ℚ) (g : ℕ) (Pm Pi : Polynomial ℚ)
variable (N : ℕ) [NeZero N]
variable {T : Over S} (y : T ⟶ FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameter S n P g Pm Pi N)

def fixedDimensionHilbertFullLevelPointRelativeMap :
    Over.mk ((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameterPointEquiv S n P g Pm Pi N T y).1.left) ⟶
      FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelRelativeParameter S n P g Pm Pi N :=
  (CompositeParameterPoints.compositeParameterPointEquiv (FixedDimension.AbelianParameters.fixedDimensionHilbertAbelianParameter S n P g Pm Pi)
    (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelRelativeParameter S n P g Pm Pi N) T y).2

def fixedDimensionHilbertFullLevelPointFamilyIso :
    ((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalAbelianScheme S n P g Pm Pi N).pullback y.left).scheme ≅
      ((FixedDimension.AbelianParameters.fixedDimensionHilbertUniversalAbelianScheme S n P g Pm Pi).pullback
        (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameterPointEquiv S n P g Pm Pi N T y).1.left).scheme :=
  ((FixedDimension.AbelianParameters.fixedDimensionHilbertUniversalAbelianScheme S n P g Pm Pi).parameterPullbackIso
    (fixedDimensionHilbertFullLevelPointRelativeMap S n P g Pm Pi N y)).symm

instance fixedDimensionHilbertFullLevelPointFamilyIso_isMonHom :
    IsMonHom (fixedDimensionHilbertFullLevelPointFamilyIso S n P g Pm Pi N y).hom :=
  inferInstanceAs (IsMonHom
    ((FixedDimension.AbelianParameters.fixedDimensionHilbertUniversalAbelianScheme S n P g Pm Pi).parameterPullbackIso
      (fixedDimensionHilbertFullLevelPointRelativeMap S n P g Pm Pi N y)).symm.hom)

theorem fixedDimensionHilbertFullLevelPointFamilyIso_level :
    ((FixedDimension.LevelParameters.fixedDimensionHilbertUniversalFullLevel S n P g Pm Pi N).pullback y.left).transport
      (fixedDimensionHilbertFullLevelPointFamilyIso S n P g Pm Pi N y) =
        (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameterPointEquiv S n P g Pm Pi N T y).2 :=
  (FixedDimension.AbelianParameters.fixedDimensionHilbertUniversalAbelianScheme S n P g Pm Pi).universalFullLevel_point N
    (fixedDimensionHilbertFullLevelPointRelativeMap S n P g Pm Pi N y)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Fixed.LevelUniversalRecovery
