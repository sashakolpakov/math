import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ConormalClassAddition
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualAffine.RegularScalars
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RegularPair.ClassScalars
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.StructureComplexScalars
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ConormalSheafClassCriterion

/-! # Conormal Obstruction Linear -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ConormalObstructionLinear

noncomputable section

/-! The actual deformation obstruction is a complex-linear map
from the constructed identity conormal module into original algebraic
structure-sheaf H1, with zero equivalent to an actual normalized product. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.CategoryTheory.MonObj

variable (X : Over (Spec (.of (DualNumber ℂ)))) [Smooth X.hom] [IsSeparated X.hom]
    [IsIntegral (DualAffine.ConormalInclusions.dualFamilySpecialFiberObject ℂ X).left]
    [Smooth (DualAffine.ConormalInclusions.dualFamilySpecialFiberObject ℂ X).hom] [GrpObj (DualAffine.ConormalInclusions.dualFamilySpecialFiberObject ℂ X)]
    (U : X.left.AffineOpenCover)

local instance dualConormalH1_complexModule :
    Module ℂ (SheafCohomology.AffineH.Projective.H (HilbertConstruction.Line.Bundles.structureModule (DualAffine.ConormalInclusions.dualFamilySpecialFiberObject ℂ X).left) 1) :=
  StructureComplexScalars.structureH1ComplexModule (DualAffine.ConormalInclusions.dualFamilySpecialFiberObject ℂ X)

theorem dualSpecialFiberRegularPair_smul (c : ℂ)
    (z : Constructed.IdentityConormal.constructedIdentityConormal ℂ (DualAffine.ConormalInclusions.dualFamilySpecialFiberObject ℂ X)) (i j : U.I₀) :
    ReducedCechCover.dualSpecialFiberRegularPair X U (c • z) i j =
      (DualAffine.ConormalInclusions.dualFamilySpecialFiberObject ℂ X).left.presheaf.map
        (homOfLE (show ReducedCechCover.dualSpecialFiberCechCover X U i ⊓ ReducedCechCover.dualSpecialFiberCechCover X U j ≤ ⊤ from le_top)).op
          (Open.ComplexConstants.complexGlobalSectionMap (DualAffine.ConormalInclusions.dualFamilySpecialFiberObject ℂ X) c) * ReducedCechCover.dualSpecialFiberRegularPair X U z i j :=
  (congrArg (DualAffine.RegularSections.dualAffineRegularSectionEquiv ℂ X (CommonOpenCocycle.dualFamilyPairAffineOpen ℂ X U i j))
    ((DualAffine.ConormalCocycle.dualFamilyPairConormalTransition X U i j).map_smul c z)).trans
      (DualAffine.RegularScalars.dualAffineRegularSectionEquiv_smul X (CommonOpenCocycle.dualFamilyPairAffineOpen ℂ X U i j) c _)

theorem dualConormalSheafClass_smul (c : ℂ)
    (z : Constructed.IdentityConormal.constructedIdentityConormal ℂ (DualAffine.ConormalInclusions.dualFamilySpecialFiberObject ℂ X)) :
    ConormalSheafClass.dualConormalSheafClass X U (c • z) = c •
      (show SheafCohomology.AffineH.Projective.H (HilbertConstruction.Line.Bundles.structureModule (DualAffine.ConormalInclusions.dualFamilySpecialFiberObject ℂ X).left) 1 from
        ConormalSheafClass.dualConormalSheafClass X U z) :=
  RegularPair.ClassScalars.regularPairSheafClass_globalScalar (DualAffine.ConormalInclusions.dualFamilySpecialFiberObject ℂ X).left (ReducedCechCover.dualSpecialFiberCechCover X U)
    (ReducedCechCover.dualSpecialFiberCechCover_covers X U) (ReducedCechCover.dualSpecialFiberRegularPair X U z) (ReducedCechCover.dualSpecialFiberRegularPair X U (c • z))
    (ReducedCechCover.dualSpecialFiberRegularPair_cocycle X U z) (ReducedCechCover.dualSpecialFiberRegularPair_cocycle X U (c • z))
    (Open.ComplexConstants.complexGlobalSectionMap (DualAffine.ConormalInclusions.dualFamilySpecialFiberObject ℂ X) c) (dualSpecialFiberRegularPair_smul X U c z)

def dualConormalObstructionLinear :
    Constructed.IdentityConormal.constructedIdentityConormal ℂ (DualAffine.ConormalInclusions.dualFamilySpecialFiberObject ℂ X) →ₗ[ℂ]
      SheafCohomology.AffineH.Projective.H (HilbertConstruction.Line.Bundles.structureModule (DualAffine.ConormalInclusions.dualFamilySpecialFiberObject ℂ X).left) 1 where
  toFun := ConormalSheafClass.dualConormalSheafClass X U
  map_add' := ConormalClassAddition.dualConormalSheafClass_add X U
  map_smul' := dualConormalSheafClass_smul X U

theorem dualConormalObstructionLinear_zero_iff_product :
    dualConormalObstructionLinear X U = 0 ↔
      ∃ e : X ≅ (Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseProjection ℂ)).obj (DualAffine.ConormalInclusions.dualFamilySpecialFiberObject ℂ X),
        NormalizedDual.OpenProductData.NormalizesDualProductFiber ℂ e := by
  rw [LinearMap.ext_iff]
  exact (ConormalSheafClassCriterion.normalizedDualProduct_iff_conormalSheafClasses_zero X U).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ConormalObstructionLinear
