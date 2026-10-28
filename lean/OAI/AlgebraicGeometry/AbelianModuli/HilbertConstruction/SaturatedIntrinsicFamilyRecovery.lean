import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SaturatedIdealCoordinateLift
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.AffineFamilyTransport
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.FamilyTestPoints

/-! # Saturated Intrinsic Family Recovery -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The original saturated homogeneous family is canonically isomorphic
to its native Hilbert family, with the actual ambient embedding retained. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

def SaturatedIntrinsicFamilyRecovery.homogeneousIdealEqIso {C : Type u} [CommRing C] {n : ℕ}
    {I J : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading C n)} (h : I = J) :
    Projective.EmbeddingBaseChange.homogeneousProjectiveFamily I ≅ Projective.EmbeddingBaseChange.homogeneousProjectiveFamily J :=
  eqToIso (congrArg Projective.EmbeddingBaseChange.homogeneousProjectiveFamily h)

theorem SaturatedIntrinsicFamilyRecovery.homogeneousIdealEqIso_ambient {C : Type u} [CommRing C] {n : ℕ}
    {I J : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading C n)} (h : I = J) :
    (SaturatedIntrinsicFamilyRecovery.homogeneousIdealEqIso h).hom.left ≫ HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion J =
      HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I := by
  subst J
  exact Category.id_comp _

variable {C : Type u} [CommRing C] [IsNoetherianRing C] {n : ℕ} {H : Polynomial ℚ}
    (I : SaturatedFlatIdeals.SaturatedFlatHilbertIdeal C n H) {S : Scheme.{u}} (f : Spec (.of C) ⟶ S)

def SaturatedFlatIdeals.SaturatedFlatHilbertIdeal.nativeFamilyIso : Projective.EmbeddingBaseChange.homogeneousProjectiveFamily I.ideal ≅
    Intrinsic.FamilyTestPoints.nativeFamilyOver (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Over.mk f) (I.nativeHilbertFamily f) :=
  SaturatedIntrinsicFamilyRecovery.homogeneousIdealEqIso (I.nativeHilbertFamily_coordinates f).symm ≪≫
    Intrinsic.AffineFamilyTransport.affineNativeHomogeneousFamilyIso n f (I.nativeHilbertFamily f)

theorem SaturatedFlatIdeals.SaturatedFlatHilbertIdeal.nativeFamilyIso_ambient :
    (I.nativeFamilyIso f).hom.left ≫ (I.nativeHilbertFamily f).val.subschemeι =
      HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I.ideal ≫ (HilbertScheme.Presentations.Affine.ProjectiveAmbient.GradedHilbert.affineProjectiveAmbientIso n f).hom := by
  let e := SaturatedIntrinsicFamilyRecovery.homogeneousIdealEqIso (I.nativeHilbertFamily_coordinates f).symm
  let r := Intrinsic.AffineFamilyTransport.affineNativeHomogeneousFamilyIso n f (I.nativeHilbertFamily f)
  exact (Category.assoc e.hom.left r.hom.left (I.nativeHilbertFamily f).val.subschemeι).trans
    ((congrArg (fun q => e.hom.left ≫ q)
      (Intrinsic.AffineFamilyTransport.affineNativeHomogeneousFamilyIso_ambient n f (I.nativeHilbertFamily f))).trans
        ((Category.assoc e.hom.left
          (HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion (HilbertScheme.Presentations.Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n f (I.nativeHilbertFamily f)))
          (HilbertScheme.Presentations.Affine.ProjectiveAmbient.GradedHilbert.affineProjectiveAmbientIso n f).hom).symm.trans
            (congrArg (fun q => q ≫ (HilbertScheme.Presentations.Affine.ProjectiveAmbient.GradedHilbert.affineProjectiveAmbientIso n f).hom)
              (SaturatedIntrinsicFamilyRecovery.homogeneousIdealEqIso_ambient (I.nativeHilbertFamily_coordinates f).symm))))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
