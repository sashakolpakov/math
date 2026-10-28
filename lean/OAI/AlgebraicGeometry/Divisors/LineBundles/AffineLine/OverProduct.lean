import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.Charts
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-! # Over Product -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.OverProduct.BundleCycles

noncomputable section

/-! The actual affine line over a complex scheme is the product with
the complex affine line, through the native affine-space pullback square. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.CartesianMonoidalCategory
open scoped MonoidalCategory

def complexAffineLineOver : Over Foundations.Scheme.ProjectiveSpace.complexBase := Over.mk (Charts.BundleCycles.affineLineProjection Foundations.Scheme.ProjectiveSpace.complexBase)

def affineLineOver (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) : Over Foundations.Scheme.ProjectiveSpace.complexBase :=
  Over.mk (Charts.BundleCycles.affineLineProjection X.left ≫ X.hom)

def affineLineProductSchemeIso (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) :
    Charts.BundleCycles.affineLine X.left ≅ (X ⊗ complexAffineLineOver).left :=
  (AffineSpace.isPullback_map (n := PUnit) X.hom).flip.isoPullback

theorem affineLineProductSchemeIso_fst (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) :
    (affineLineProductSchemeIso X).hom ≫ (fst X complexAffineLineOver).left =
      Charts.BundleCycles.affineLineProjection X.left :=
  (AffineSpace.isPullback_map (n := PUnit) X.hom).flip.isoPullback_hom_fst

theorem affineLineProductSchemeIso_snd (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) :
    (affineLineProductSchemeIso X).hom ≫ (snd X complexAffineLineOver).left =
      AffineSpace.map PUnit X.hom :=
  (AffineSpace.isPullback_map (n := PUnit) X.hom).flip.isoPullback_hom_snd

def affineLineProductOverIso (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) : affineLineOver X ≅ X ⊗ complexAffineLineOver :=
  Over.isoMk (affineLineProductSchemeIso X) (by
    change (affineLineProductSchemeIso X).hom ≫
      ((fst X complexAffineLineOver).left ≫ X.hom) = Charts.BundleCycles.affineLineProjection X.left ≫ X.hom
    rw [← Category.assoc, affineLineProductSchemeIso_fst])

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.OverProduct.BundleCycles
