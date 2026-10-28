import OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.MapPairs
import OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.OpenProducts
import OAI.NumberTheory.PadicHodge.GeometricComparison.Section.GeometricRestriction
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralFirst.ThreePullback

/-! # Pair Section Algebra Pullback -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.PairSectionAlgebraPullback.AffinePairSectionAlgebraPullback

noncomputable section

/-! Actual geometric pullback of section algebras is natural on
compatible affine pairs over the original coefficient ring. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

variable (R : Type) [CommRing R]
  {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y)

def transformation : (MapPairs.AffineMapPairs.target f.left).op ⋙ (OpenProducts.AffineOpenProducts.inclusion Y.left).op ⋙
    AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras R Y ⟶
      (MapPairs.AffineMapPairs.source f.left).op ⋙ (OpenProducts.AffineOpenProducts.inclusion X.left).op ⋙
        AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras R X where
  app U := CommAlgCat.ofHom (OpenSectionPullback.DeRham.sectionPullbackLE f U.unop.val.2.val U.unop.val.1.val U.unop.property)
  naturality U V a := by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro x
    exact ConcreteCategory.congr_hom
      (Section.GeometricRestriction.SectionGeometricRestriction.square f.left V.unop.val.2.val U.unop.val.2.val
        V.unop.val.1.val U.unop.val.1.val
        (leOfHom ((MapPairs.AffineMapPairs.target f.left).map a.unop))
        (leOfHom ((MapPairs.AffineMapPairs.source f.left).map a.unop))
        V.unop.property U.unop.property).symm x

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.PairSectionAlgebraPullback.AffinePairSectionAlgebraPullback
