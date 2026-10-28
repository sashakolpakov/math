import OAI.AlgebraicGeometry.Divisors.LineBundles.Support.PuncturedGenericPoint
import OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.Dimension
import OAI.AlgebraicGeometry.Divisors.LineBundles.GenericFieldComposition

/-! # Punctured Function Field -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Support.PuncturedFunctionField.BundleCycles

noncomputable section

/-! # LineBundleCycles: actual rational functions and dimensions on punctured support deformations -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace
open _root_.AlgebraicGeometry.Scheme.AffineZariskiSite

variable {X : Scheme.{0}} (I P : X.IdealSheafData) [IsIntegral P.subscheme]

instance supportPuncturedDeformation_isIntegral : IsIntegral (LaurentChart.BundleCycles.supportPuncturedDeformation I P) := by
  have : Nonempty (LaurentChart.BundleCycles.supportPuncturedDeformation I P) :=
    ⟨PuncturedGenericPoint.BundleCycles.supportPuncturedGenericPoint I P (genericPoint P.subscheme)⟩
  exact isIntegral_of_isOpenImmersion (LaurentChart.BundleCycles.supportPuncturedInclusion I P)

theorem supportPuncturedProjection_genericPoint :
    LaurentChart.BundleCycles.supportPuncturedProjection I P (genericPoint (LaurentChart.BundleCycles.supportPuncturedDeformation I P)) =
      genericPoint P.subscheme :=
  Deformation.FunctionField.BundleCycles.genericPoint_eq_of_surjective (LaurentChart.BundleCycles.supportPuncturedProjection I P) (PuncturedGenericPoint.BundleCycles.supportPuncturedProjection_surjective I P)

def supportPuncturedFunctionFieldMap : P.subscheme.functionField ⟶ (LaurentChart.BundleCycles.supportPuncturedDeformation I P).functionField :=
  Cycles.Functoriality.FunctionFields.Construction.genericFieldMap (LaurentChart.BundleCycles.supportPuncturedProjection I P) (supportPuncturedProjection_genericPoint I P)

theorem supportPuncturedFunctionFieldMap_on_chart (U : X.AffineZariskiSite)
    [Nonempty (Spec ((CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).obj (.op U)))] :
    supportPuncturedFunctionFieldMap I P ≫ RationalDivisorRestriction.BundleCycles.openFunctionFieldMap (LaurentChart.BundleCycles.supportPuncturedLaurentChart I P U) =
      RationalDivisorRestriction.BundleCycles.openFunctionFieldMap (Projection.BundleCycles.supportCoefficientChart P U) ≫
        Laurent.FiberGenericPoint.BundleCycles.laurentFunctionFieldMap ((CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).obj (.op U)) := by
  exact (GenericFieldComposition.BundleCycles.genericFieldMap_comp (LaurentChart.BundleCycles.supportPuncturedLaurentChart I P U) (LaurentChart.BundleCycles.supportPuncturedProjection I P)
    (genericPoint_eq_of_isOpenImmersion _) (supportPuncturedProjection_genericPoint I P)).symm.trans
      ((GenericFieldComposition.BundleCycles.genericFieldMap_congr (LaurentChart.BundleCycles.supportPuncturedLaurentChart_toSupport I P U) _ _).trans
        (GenericFieldComposition.BundleCycles.genericFieldMap_comp (Laurent.FiberGenericPoint.BundleCycles.laurentProjection ((CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).obj (.op U)))
          (Projection.BundleCycles.supportCoefficientChart P U) (Laurent.FiberGenericPoint.BundleCycles.laurentProjection_genericPoint ((CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).obj (.op U)))
          (genericPoint_eq_of_isOpenImmersion _)))

theorem supportPunctured_dimension (f : P.subscheme ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f] :
    Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (LaurentChart.BundleCycles.supportPuncturedProjection I P ≫ f) =
      Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension f + 1 := by
  exact (congrArg (fun g => Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension g)
    (Category.assoc (LaurentChart.BundleCycles.supportPuncturedInclusion I P) (Projection.BundleCycles.globalSupportDeformationToSupport I P) f)).trans
      ((Foundations.Scheme.OpenFunctionField.schemeTranscendenceDimension_openImmersion (LaurentChart.BundleCycles.supportPuncturedInclusion I P)
        (Projection.BundleCycles.globalSupportDeformationToSupport I P ≫ f)).trans (Deformation.Dimension.BundleCycles.globalSupportDeformation_dimension I P f))

theorem supportPuncturedGenericPoint_generic :
    PuncturedGenericPoint.BundleCycles.supportPuncturedGenericPoint I P (genericPoint P.subscheme) =
      genericPoint (LaurentChart.BundleCycles.supportPuncturedDeformation I P) := by
  exact ((PuncturedGenericPoint.BundleCycles.supportPuncturedGenericPoint_specializes I P _ _ (supportPuncturedProjection_genericPoint I P)).antisymm
    ((genericPoint_spec (LaurentChart.BundleCycles.supportPuncturedDeformation I P)).specializes trivial)).eq

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Support.PuncturedFunctionField.BundleCycles
