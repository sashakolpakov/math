import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FamilyTangent.NormalizedProduct
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FamilyTangent.PrimitiveCriterion

/-! # Obstruction Product -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FamilyTangent.ObstructionProduct

noncomputable section

/-! A zero value of the constructed complex-linear base-tangent
obstruction gives an actual global product, normalized on the actual
special fiber. No global trivialization or descent datum is assumed. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable (R : Type) [CommRing R] [Algebra ℂ R] [Algebra R ℂ] [IsScalarTower ℂ R ℂ]
    (X : Over (Spec (.of R))) [Smooth X.hom] [IsSeparated X.hom]
    [IsIntegral (TangentBasePoint.fixedFamilyFiber ℂ R X).left] [Smooth (TangentBasePoint.fixedFamilyFiber ℂ R X).hom]
    [GrpObj (TangentBasePoint.fixedFamilyFiber ℂ R X)] (U : X.left.AffineOpenCover)

local instance familyProductH1_complexModule :
    Module ℂ (SheafCohomology.AffineH.Projective.H (HilbertConstruction.Line.Bundles.structureModule (TangentBasePoint.fixedFamilyFiber ℂ R X).left) 1) :=
  StructureComplexScalars.structureH1ComplexModule (TangentBasePoint.fixedFamilyFiber ℂ R X)

theorem familyBaseTangentObstruction_zero_product (d : Derivation ℂ R ℂ)
    (h : Family.BaseTangentObstruction.familyBaseTangentObstruction R X U d = 0) :
    ∃ e : TangentBasePoint.tangentFamily ℂ R X d ≅ (Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseProjection ℂ)).obj
      ((Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseReduction ℂ)).obj (TangentBasePoint.tangentFamily ℂ R X d)),
      NormalizedDual.OpenProductData.NormalizesDualProductFiber ℂ e := by
  obtain ⟨a, ha⟩ := Primitives.familyTangentDerivationPrimitive_of_obstruction_zero R X U d h
  exact ⟨NormalizedProduct.familyTangentNormalizedProduct R X U d a ha,
    NormalizedProduct.familyTangentNormalizedProduct_normalized R X U d a ha⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FamilyTangent.ObstructionProduct
