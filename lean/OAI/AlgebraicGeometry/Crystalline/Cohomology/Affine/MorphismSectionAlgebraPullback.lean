import OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs
import OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.OpenProducts
import OAI.AlgebraicGeometry.Crystalline.Cohomology.OpenSectionGeometricPullback

/-! # Morphism Section Algebra Pullback -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismSectionAlgebraPullback.AffineMorphismSectionAlgebraPullback

noncomputable section

/-! Actual geometric pullback of section algebras is natural on
compatible affine pairs over the original coefficient ring. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u
variable (R : Type u) [CommRing R]
  {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y)

def transformation : (MorphismPairs.AffineMorphismPairs.target f.left).op ⋙ (NumberTheory.PadicHodge.GeometricComparison.Affine.OpenProducts.AffineOpenProducts.inclusion Y.left).op ⋙
    AlgebraicForms.AlgebraicDeRham.sectionAlgebras R Y ⟶
      (MorphismPairs.AffineMorphismPairs.source f.left).op ⋙ (NumberTheory.PadicHodge.GeometricComparison.Affine.OpenProducts.AffineOpenProducts.inclusion X.left).op ⋙
        AlgebraicForms.AlgebraicDeRham.sectionAlgebras R X where
  app U := CommAlgCat.ofHom (OpenSectionGeometricPullback.DeRhamPullback.sectionPullbackLE f U.unop.val.2.val U.unop.val.1.val U.unop.property)
  naturality U V a := by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro x
    have hs := f.left.appLE_map U.unop.property (homOfLE (leOfHom a.unop).1).op
    have ht := f.left.map_appLE V.unop.property (homOfLE (leOfHom a.unop).2).op
    exact (ConcreteCategory.congr_hom (hs.trans ht.symm) x).symm

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismSectionAlgebraPullback.AffineMorphismSectionAlgebraPullback
