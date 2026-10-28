import OAI.AlgebraicGeometry.Crystalline.Cohomology.OpenSectionGeometricPullback
import OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.OpenProducts
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs

/-! # Algebra Pullback -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.AlgebraPullback

noncomputable section

/-! Actual section algebras pull back on compatible affine chart pairs
over an arbitrary commutative base ring. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u
variable (R : Type u) [CommRing R]
  {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y)

def diagram (X : Over (Spec (CommRingCat.of R))) :=
  (GeometricComparison.Affine.OpenProducts.AffineOpenProducts.inclusion X.left).op ⋙ AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras R X

def transformation : (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.target f.left).op ⋙ diagram R Y ⟶
    (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.source f.left).op ⋙ diagram R X where
  app U := CommAlgCat.ofHom
    (AlgebraicGeometry.Crystalline.Cohomology.OpenSectionGeometricPullback.DeRhamPullback.sectionPullbackLE f U.unop.val.2.val U.unop.val.1.val U.unop.property)
  naturality U V a := by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro x
    have hs := f.left.appLE_map U.unop.property (homOfLE (leOfHom a.unop).1).op
    have ht := f.left.map_appLE V.unop.property (homOfLE (leOfHom a.unop).2).op
    exact (ConcreteCategory.congr_hom (hs.trans ht.symm) x).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.AlgebraPullback
