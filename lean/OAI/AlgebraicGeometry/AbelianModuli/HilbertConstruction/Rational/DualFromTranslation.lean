import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.TranslationGeometricPicard
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Rational.PicardRepresentation
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.HomogeneousPicardDescent
import OAI.RepresentationTheory.Theta.Geometric.Dual.PicardData

/-! # Dual From Translation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The actual ample translation quotient supplies dual abelian data
once the original difference line is homogeneous. All-test
representability is proved by the rational Picard comparison theorem. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

open OAI.RepresentationTheory.Theta.Geometric.Dual.PicardData

variable {R : Type} [CommRing R] [IsNoetherianRing R] {g : ℕ}
    {A : Abelian.Schemes.AbelianScheme g (Spec (.of R))} {L : Line.Bundles.LineBundle A.scheme.left}
    {P : Projective.ProjectivePresentations.ProjectivePresentation A.scheme} (Q : Ample.TranslationQuotient.AmpleTranslationQuotient A L P)

local instance Ample.TranslationQuotient.AmpleTranslationQuotient.rationalDual_isogeny_etale : Etale Q.isogeny.hom.left := Q.etale

theorem Ample.TranslationQuotient.AmpleTranslationQuotient.descendedDifference_homogeneous_of_difference
    (hδ : A.IsHomogeneousPicardClass A.scheme (Line.Bundles.LineBundle.classOf (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L))) :
    A.IsHomogeneousPicardClass Q.target.scheme (Line.Bundles.LineBundle.classOf Q.descendedDifference.bundle) := by
  apply AbelianScheme.IsogenyQuotient.HomogeneousPicardDescent.Construction.homogeneousPicardClass_of_fppf_pullback A.scheme Q.isogeny.hom
  change A.IsHomogeneousPicardClass A.scheme
    (Line.Bundles.LineBundle.pullbackClass (Q.isogeny.hom ⊗ₘ 𝟙 A.scheme).left
      (Line.Bundles.LineBundle.classOf Q.descendedDifference.bundle))
  exact (congrArg (A.IsHomogeneousPicardClass A.scheme)
    Q.descendedDifference_pullback_class).mpr hδ

theorem Ample.TranslationQuotient.AmpleTranslationQuotient.homogeneousParameterMap_isIso_of_difference
    (qS : Spec (.of R) ⟶ Spec (.of ℚ)) (hL : L.IsAmple)
    (hδ : A.IsHomogeneousPicardClass A.scheme (Line.Bundles.LineBundle.classOf (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L))) :
    IsIso (RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.homogeneousParameterMap A Q.descendedDifference.bundle
      (Q.descendedDifference_homogeneous_of_difference hδ)) :=
  Rational.PicardRepresentation.rationalHomogeneousParameterMap_isIso qS A Q.target P Q.descendedDifference
    (Q.descendedDifference_homogeneous_of_difference hδ) Q.descendedDifference_value_injective
    (fun _ _ _ f x => Q.descendedDifference_geometric_surjective qS hL f x)

def Ample.TranslationQuotient.AmpleTranslationQuotient.dualData_of_difference
    (qS : Spec (.of R) ⟶ Spec (.of ℚ)) (hL : L.IsAmple)
    (hδ : A.IsHomogeneousPicardClass A.scheme (Line.Bundles.LineBundle.classOf (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L))) :
    Dual.Data.DualAbelianData A := by
  let : IsIso (RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.homogeneousParameterMap A Q.descendedDifference.bundle
    (Q.descendedDifference_homogeneous_of_difference hδ)) :=
      Q.homogeneousParameterMap_isIso_of_difference qS hL hδ
  exact RepresentationTheory.Theta.Geometric.Dual.PicardData.dualDataOfHomogeneousParameterIso A Q.target Q.descendedDifference.bundle
    (Q.descendedDifference_homogeneous_of_difference hδ) Q.descendedDifference.axis
    Q.descendedDifference_secondAxis

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
