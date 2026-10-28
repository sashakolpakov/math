import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FamilyTangent.GlobalProduct
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Product.IsoReidentifiedFiber

/-! # Normalized Product -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FamilyTangent.NormalizedProduct

noncomputable section

/-! The product constructed by gluing can be normalized on the
tangent family's own actual special fiber. This uses the proved
functorial fiber comparison and retains an actual global isomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (R : Type) [CommRing R] [Algebra ℂ R] [Algebra R ℂ] [IsScalarTower ℂ R ℂ]
    (X : Over (Spec (.of R))) [Smooth X.hom] [IsSeparated X.hom]
    (U : X.left.AffineOpenCover) (d : Derivation ℂ R ℂ)
    (a : Primitives.fixedFamilyDerivationGauges R X U) (ha : Primitives.IsFamilyTangentDerivationPrimitive R X U d a)

attribute [local irreducible] GlobalProduct.familyTangentGlobalProduct Normalized.SmoothAffineDualProduct.dualProductSpecialFiberIso

def familyTangentNormalizedProduct : TangentBasePoint.tangentFamily ℂ R X d ≅
    (Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseProjection ℂ)).obj
      ((Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseReduction ℂ)).obj (TangentBasePoint.tangentFamily ℂ R X d)) :=
  Product.IsoReidentifiedFiber.productIsoCanonicalFiber (Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseProjection ℂ))
    (Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseReduction ℂ)) (Normalized.SmoothAffineDualProduct.dualProductSpecialFiberIso ℂ)
    (TangentBasePoint.tangentFamily ℂ R X d) (TangentBasePoint.fixedFamilyFiber ℂ R X) (GlobalProduct.familyTangentGlobalProduct R X U d a ha)

theorem familyTangentNormalizedProduct_normalized :
    NormalizedDual.OpenProductData.NormalizesDualProductFiber ℂ (familyTangentNormalizedProduct R X U d a ha) :=
  Product.IsoReidentifiedFiber.productIsoCanonicalFiber_normalized (Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseProjection ℂ))
    (Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseReduction ℂ)) (Normalized.SmoothAffineDualProduct.dualProductSpecialFiberIso ℂ)
    (TangentBasePoint.tangentFamily ℂ R X d) (TangentBasePoint.fixedFamilyFiber ℂ R X) (GlobalProduct.familyTangentGlobalProduct R X U d a ha)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FamilyTangent.NormalizedProduct
