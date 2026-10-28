import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.CorrectedIntrinsicAgreement
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.CoverIsomorphismGluing
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Fixed.ProductFunctor

/-! # Corrected Cover Data -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.CorrectedCoverData

noncomputable section

/-! A primitive of the actual tangent cocycle supplies the native
chart isomorphisms and both intersection squares required for gluing. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (R : Type) [CommRing R] [Algebra ℂ R] [Algebra R ℂ] [IsScalarTower ℂ R ℂ]
    (X : Over (Spec (.of R))) [Smooth X.hom] [IsSeparated X.hom]
    (U : X.left.AffineOpenCover) (d : Derivation ℂ R ℂ)
    (a : FamilyTangent.Primitives.fixedFamilyDerivationGauges R X U) (ha : FamilyTangent.Primitives.IsFamilyTangentDerivationPrimitive R X U d a)

attribute [local implicit_reducible] AffineCoverIntersections.familyCoverAffineOpen AffineCoverIntersections.familyCoverPairAffineOpen
attribute [local implicit_reducible] Fixed.ProductFunctor.fixedFamilyProductFunctor FixedFiber.AffineDiagram.fixedFiberAffineDiagram Affine.OpenDiagram.familyAffineOpenDiagram
attribute [local irreducible] CorrectedIntrinsicProducts.familyCorrectedNativeProduct

def familyCorrectedCoverData : CoverIsomorphismGluing.FamilyCoverIsomorphisms R X U
    (Over.pullback (TangentBasePoint.tangentBasePoint ℂ R d)) (Fixed.ProductFunctor.fixedFamilyProductFunctor ℂ R) where
  chart i := CorrectedIntrinsicProducts.familyCorrectedNativeProduct ℂ R X
    (V := AffineCoverIntersections.familyCoverAffineOpen R X U i) le_rfl d (a i)
  pair i j := CorrectedIntrinsicProducts.familyCorrectedNativeProduct ℂ R X
    (V := AffineCoverIntersections.familyCoverPairAffineOpen R X U i j) (W := AffineCoverIntersections.familyCoverAffineOpen R X U i) inf_le_left d (a i)
  left_square i j := CorrectedIntrinsicProducts.familyCorrectedNativeProduct_restrict ℂ R X
    (U := AffineCoverIntersections.familyCoverPairAffineOpen R X U i j) (V := AffineCoverIntersections.familyCoverAffineOpen R X U i)
    inf_le_left le_rfl d (a i)
  right_square i j := by
    have hn := CorrectedIntrinsicProducts.familyCorrectedNativeProduct_restrict ℂ R X
      (U := AffineCoverIntersections.familyCoverPairAffineOpen R X U i j) (V := AffineCoverIntersections.familyCoverAffineOpen R X U j)
      inf_le_right le_rfl d (a j)
    have he := CorrectedIntrinsicAgreement.familyCorrectedNativeProduct_common_eq R X U d a ha
      (AffineCoverIntersections.familyCoverPairAffineOpen R X U i j) i j inf_le_left inf_le_right
    rw [← he] at hn
    exact hn

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.CorrectedCoverData
