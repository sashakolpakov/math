import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.InverseImageMap
import OAI.AlgebraicTopology.Singular.SheafCochainRestriction

/-! # Singular Inverse Image -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Reference.SingularInverseImage

noncomputable section

/-! # Genuine inverse image of the original singular cochain sheaves

The unchanged upstream singular cochain restriction is defined for every
continuous map. Here it is adjointed to genuine inverse image under the
actual scheme-point map, with its original coefficients and complexes.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint

variable {X Y : Over (Spec (.of ℂ))} (R : Type) [CommRing R]

/-- Actual inverse-image pullback of the unchanged singular sheaf complex. -/
def originalSingularInverseImagePullbackNat (f : X ⟶ Y) :
    ((AnalyticInverseImage.originalAnalyticSheafInverseImage f).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (AlgebraicTopology.Singular.SheafCochain.singularCochainSheafComplex R
          (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y))) ⟶
      AlgebraicTopology.Singular.SheafCochain.singularCochainSheafComplex R
        (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) :=
  InverseImageMap.originalInverseImageComplexMap f _ _ _
    (AlgebraicTopology.Singular.SheafCochainRestriction.singularRestrictionSheafComplex R
      (DeRhamPresheafPullback.originalAnalyticSchemeMap f))

/-- The same actual pullback on the original integer-indexed singular complex. -/
def originalSingularInverseImagePullback (f : X ⟶ Y) :
    (AnalyticInverseImage.originalAnalyticInverseImageLocalizer f).functor.obj
        (ComplexPoint.Basic.ComplexSchemePoint.singularCochainSheafComplexInt Y R) ⟶ ComplexPoint.Basic.ComplexSchemePoint.singularCochainSheafComplexInt X R :=
  (Algebra.Homology.MapExtend.HomologicalComplex.mapExtendCanonicalIso (AnalyticInverseImage.originalAnalyticSheafInverseImage f)
    (AlgebraicTopology.Singular.SheafCochain.singularCochainSheafComplex R
      (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y))) ComplexShape.embeddingUpNat).hom ≫
    HomologicalComplex.extendMap (originalSingularInverseImagePullbackNat R f)
      ComplexShape.embeddingUpNat

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Reference.SingularInverseImage
