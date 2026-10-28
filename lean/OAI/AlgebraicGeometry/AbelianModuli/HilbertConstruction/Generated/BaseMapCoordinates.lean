import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Generated.BaseMapClassifiers
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Generated.FamilyClassification
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Generated.PullbackAffineCharts

/-! # Base Map Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Generated.BaseMapCoordinates

noncomputable section

/-! A parameter base map preserves the actual finite homogeneous quotient coordinates and their embedded projective families. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S T : Scheme.{u}} (f : T ⟶ S) {n B N : ℕ} {r : ℕ → ℕ} (hN : N ≤ B)
variable {R : CommRingCat.{u}} (x : Spec R ⟶ (Truncated.GeneratedParameters.truncatedGeneratedParameters T n B r N).left)

theorem generatedParameterBaseMap_coordinates :
    Truncated.AffineUniversalData.truncatedAffineUniversalData
      ((x ≫ ParameterBaseMaps.generatedParameterBaseMap f n B r N hN) ≫ (Truncated.GeneratedParameters.truncatedGeneratedInclusion S n B r N).left) =
    Truncated.AffineUniversalData.truncatedAffineUniversalData (x ≫ (Truncated.GeneratedParameters.truncatedGeneratedInclusion T n B r N).left) := by
  let g := x ≫ (Truncated.GeneratedParameters.truncatedGeneratedParameters T n B r N).hom
  let a : Over.mk g ⟶ Truncated.GeneratedParameters.truncatedGeneratedParameters T n B r N := Over.homMk x rfl
  let D := (Truncated.GeneratedParameters.truncatedGeneratedAffinePointEquiv R g).symm a
  have hx : (Truncated.GeneratedParameters.truncatedGeneratedAffinePointEquiv R g D).left = x :=
    congrArg Over.Hom.left ((Truncated.GeneratedParameters.truncatedGeneratedAffinePointEquiv R g).apply_symm_apply a)
  have hm : x ≫ ParameterBaseMaps.generatedParameterBaseMap f n B r N hN =
      (Truncated.GeneratedParameters.truncatedGeneratedAffinePointEquiv R (g ≫ f) D).left :=
    (congrArg (fun c => c ≫ ParameterBaseMaps.generatedParameterBaseMap f n B r N hN) hx.symm).trans
      (BaseMapClassifiers.generatedParameterBaseMap_classifier f hN R g D)
  calc
    _ = Truncated.AffineUniversalData.truncatedAffineUniversalData
        ((Truncated.GeneratedParameters.truncatedGeneratedAffinePointEquiv R (g ≫ f) D).left ≫ (Truncated.GeneratedParameters.truncatedGeneratedInclusion S n B r N).left) :=
      congrArg (fun c => Truncated.AffineUniversalData.truncatedAffineUniversalData (c ≫ (Truncated.GeneratedParameters.truncatedGeneratedInclusion S n B r N).left)) hm
    _ = D.val := FamilyClassification.truncatedGeneratedClassifier_data (g ≫ f) D
    _ = Truncated.AffineUniversalData.truncatedAffineUniversalData
        ((Truncated.GeneratedParameters.truncatedGeneratedAffinePointEquiv R g D).left ≫ (Truncated.GeneratedParameters.truncatedGeneratedInclusion T n B r N).left) :=
      (FamilyClassification.truncatedGeneratedClassifier_data g D).symm
    _ = _ := congrArg (fun c => Truncated.AffineUniversalData.truncatedAffineUniversalData (c ≫ (Truncated.GeneratedParameters.truncatedGeneratedInclusion T n B r N).left)) hx

theorem generatedParameterBaseMap_affineFamily (hflat : Truncated.FinitePersistence.truncatedFlatnessBound n N ≤ B) :
    PullbackAffineCharts.generatedPullbackFamilyAtAffinePoint (x ≫ ParameterBaseMaps.generatedParameterBaseMap f n B r N hN) hflat =
      PullbackAffineCharts.generatedPullbackFamilyAtAffinePoint x hflat := by
  apply Closed.Families.FlatClosedFamily.ext
  exact (PullbackAffineCharts.generatedPullbackFlatFamily_affine_ideal (x ≫ ParameterBaseMaps.generatedParameterBaseMap f n B r N hN) hflat).trans
    ((congrArg Truncated.GradedClassification.TruncatedGradedQuotientData.projectiveIdeal (generatedParameterBaseMap_coordinates f hN x)).trans
      (PullbackAffineCharts.generatedPullbackFlatFamily_affine_ideal x hflat).symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Generated.BaseMapCoordinates
