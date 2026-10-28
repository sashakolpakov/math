import OAI.AlgebraicGeometry.Divisors.LineBundles.Punctured.DeformationFlat
import OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.Dimension

/-! # Function Field -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Punctured.FunctionField.BundleCycles

noncomputable section

/-! # LineBundleCycles: the native function-field map of the punctured deformation -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace
open _root_.AlgebraicGeometry.Scheme.AffineZariskiSite

variable {X : Scheme.{0}} (I : X.IdealSheafData) [IsIntegral X]

instance globalDeformationPunctured_isIntegral : IsIntegral (Deformation.ChowLocalization.BundleCycles.globalDeformationPunctured I) := by
  have : Nonempty (Deformation.ChowLocalization.BundleCycles.globalDeformationPunctured I) := by
    obtain ⟨y, _⟩ := DeformationFlat.BundleCycles.puncturedDeformationProjection_surjective I (genericPoint X)
    exact ⟨y⟩
  exact isIntegral_of_isOpenImmersion (Deformation.ChowLocalization.BundleCycles.globalDeformationPuncturedInclusion I)

theorem puncturedDeformationProjection_genericPoint :
    DeformationCharts.BundleCycles.puncturedDeformationProjection I (genericPoint (Deformation.ChowLocalization.BundleCycles.globalDeformationPunctured I)) = genericPoint X :=
  Deformation.FunctionField.BundleCycles.genericPoint_eq_of_surjective (DeformationCharts.BundleCycles.puncturedDeformationProjection I)
    (DeformationFlat.BundleCycles.puncturedDeformationProjection_surjective I)

def puncturedFunctionFieldMap : X.functionField ⟶ (Deformation.ChowLocalization.BundleCycles.globalDeformationPunctured I).functionField :=
  Cycles.Functoriality.FunctionFields.Construction.genericFieldMap (DeformationCharts.BundleCycles.puncturedDeformationProjection I)
    (puncturedDeformationProjection_genericPoint I)

theorem puncturedFunctionFieldMap_on_chart (U : X.AffineZariskiSite) [Nonempty U.1] :
    puncturedFunctionFieldMap I ≫ RationalDivisorRestriction.BundleCycles.openFunctionFieldMap (DeformationCharts.BundleCycles.puncturedLaurentChart I U) =
      RationalDivisorRestriction.BundleCycles.openFunctionFieldMap U.2.fromSpec ≫ Laurent.FiberGenericPoint.BundleCycles.laurentFunctionFieldMap Γ(X, U.1) := by
  exact (GenericFieldComposition.BundleCycles.genericFieldMap_comp (DeformationCharts.BundleCycles.puncturedLaurentChart I U) (DeformationCharts.BundleCycles.puncturedDeformationProjection I)
    (genericPoint_eq_of_isOpenImmersion _) (puncturedDeformationProjection_genericPoint I)).symm.trans
      ((GenericFieldComposition.BundleCycles.genericFieldMap_congr (DeformationCharts.BundleCycles.puncturedLaurentChart_toBase I U) _ _).trans
        (GenericFieldComposition.BundleCycles.genericFieldMap_comp (Laurent.FiberGenericPoint.BundleCycles.laurentProjection Γ(X, U.1)) U.2.fromSpec
          (Laurent.FiberGenericPoint.BundleCycles.laurentProjection_genericPoint Γ(X, U.1)) (genericPoint_eq_of_isOpenImmersion _)))

theorem puncturedDeformation_dimension (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f] :
    Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (DeformationCharts.BundleCycles.puncturedDeformationProjection I ≫ f) =
      Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension f + 1 := by
  exact (congrArg (fun g => Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension g)
    (Category.assoc (Deformation.ChowLocalization.BundleCycles.globalDeformationPuncturedInclusion I) (Global.Deformation.BundleCycles.globalDeformationProjection I) f)).trans
      ((Foundations.Scheme.OpenFunctionField.schemeTranscendenceDimension_openImmersion (Deformation.ChowLocalization.BundleCycles.globalDeformationPuncturedInclusion I)
        (Global.Deformation.BundleCycles.globalDeformationProjection I ≫ f)).trans (Deformation.Dimension.BundleCycles.globalDeformation_dimension I f))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Punctured.FunctionField.BundleCycles
