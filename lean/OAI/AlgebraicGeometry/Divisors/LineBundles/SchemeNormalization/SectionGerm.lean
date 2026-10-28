import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.NormalizedSectionCycle
import OAI.AlgebraicGeometry.Divisors.LineBundles.SchemeNormalization.FiniteParent

/-! # Section Germ -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.SchemeNormalization.SectionGerm.BundleCycles

noncomputable section

/-! The regular section on the actual normalization ambient open pulls to the original normalized rational function, with nonvanishing and the full graded divisor identity preserved. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
  [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]
  (W : IrreducibleCloseds X.left) (s : Γ(X.left, ⊤))

local instance normalizationSectionGermSupportTop : Nonempty (⊤ : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).Opens) :=
  ⟨⟨genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme W), Opens.mem_top _⟩⟩
local instance normalizationSectionGermSourceTop : Nonempty (⊤ : (AmbientMap.BundleCycles.schemeSmoothNormalizationOver X W).left.Opens) :=
  ⟨⟨genericPoint (AmbientMap.BundleCycles.schemeSmoothNormalizationOver X W).left, Opens.mem_top _⟩⟩

omit [AlgebraicGeometry.IsIntegral X.left] [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] in
theorem schemeNormalizedFunction_restrictedAmbientSection :
    LineBundles.Scheme.NormalizedFunction.BundleCycles.schemeNormalizedFunction X W ((CycleClass.Geometric.GenericPoint.reducedSupportScheme W).germToFunctionField ⊤ ((CycleClass.Geometric.GenericPoint.reducedSupportι W).appTop s)) =
    (AmbientMap.BundleCycles.schemeSmoothNormalizationOver X W).left.germToFunctionField ⊤
      ((AmbientMap.BundleCycles.schemeSmoothNormalizationToAmbient X W).left.appTop
        ((CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeInclusion X (AmbientMap.BundleCycles.schemeNormalizationAmbientOpen X W)).left.appTop s)) := by
  have he := ConcreteCategory.congr_hom
    (Scheme.Hom.comp_appTop (AmbientMap.BundleCycles.schemeSmoothNormalizationToAmbient X W).left
      (CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeInclusion X (AmbientMap.BundleCycles.schemeNormalizationAmbientOpen X W)).left) s
  exact (LineBundles.Scheme.NormalizedSection.BundleCycles.schemeNormalizedFunction_ambientSection X W s).trans
    (congrArg ((AmbientMap.BundleCycles.schemeSmoothNormalizationOver X W).left.germToFunctionField ⊤) he)

omit [AlgebraicGeometry.IsIntegral X.left] [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] in
theorem schemeNormalizedSection_ne_zero
    (hs : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).germToFunctionField ⊤ ((CycleClass.Geometric.GenericPoint.reducedSupportι W).appTop s) ≠ 0) :
    (AmbientMap.BundleCycles.schemeSmoothNormalizationOver X W).left.germToFunctionField ⊤
      ((AmbientMap.BundleCycles.schemeSmoothNormalizationToAmbient X W).left.appTop
        ((CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeInclusion X (AmbientMap.BundleCycles.schemeNormalizationAmbientOpen X W)).left.appTop s)) ≠ 0 :=
  fun h => LineBundles.Scheme.NormalizedFunction.BundleCycles.schemeNormalizedFunction_ne_zero X W _ hs
    ((schemeNormalizedFunction_restrictedAmbientSection X W s).trans h)

omit [AlgebraicGeometry.IsIntegral X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] in
theorem schemePrincipal_open_eq_normalizedRestrictedSectionPush (d : ℕ)
    (hW : Foundations.Scheme.SupportDimension.supportTranscendenceDimension W X.hom = d + 1)
    (hs : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).germToFunctionField ⊤ ((CycleClass.Geometric.GenericPoint.reducedSupportι W).appTop s) ≠ 0) :
    Open.GradedOverRestriction.BundleCycles.openOverGradedRestriction (CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeInclusion X (AmbientMap.BundleCycles.schemeNormalizationAmbientOpen X W)) d
      (Graded.GlobalSpecialization.BundleCycles.schemeGradedPrincipalDivisor X.hom d W
        ((CycleClass.Geometric.GenericPoint.reducedSupportScheme W).germToFunctionField ⊤ ((CycleClass.Geometric.GenericPoint.reducedSupportι W).appTop s))) =
    Finite.GradedOverPushforward.BundleCycles.finiteOverGradedPushforward (AmbientMap.BundleCycles.schemeSmoothNormalizationToAmbient X W) d
      (Graded.RationalPointDivisor.BundleCycles.gradedRationalPointDivisor (AmbientMap.BundleCycles.schemeSmoothNormalizationOver X W).left
        (AmbientMap.BundleCycles.schemeSmoothNormalizationOver X W).hom d
        ((AmbientMap.BundleCycles.schemeSmoothNormalizationOver X W).left.germToFunctionField ⊤
          ((AmbientMap.BundleCycles.schemeSmoothNormalizationToAmbient X W).left.appTop
            ((CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeInclusion X (AmbientMap.BundleCycles.schemeNormalizationAmbientOpen X W)).left.appTop s)))) := by
  have h := LineBundles.Scheme.NormalizedGradedPush.BundleCycles.schemePrincipal_open_eq_normalizedPush X W d hW
    ((CycleClass.Geometric.GenericPoint.reducedSupportScheme W).germToFunctionField ⊤ ((CycleClass.Geometric.GenericPoint.reducedSupportι W).appTop s)) hs
  exact h.trans (congrArg (fun r => Finite.GradedOverPushforward.BundleCycles.finiteOverGradedPushforward (AmbientMap.BundleCycles.schemeSmoothNormalizationToAmbient X W) d
    (Graded.RationalPointDivisor.BundleCycles.gradedRationalPointDivisor (AmbientMap.BundleCycles.schemeSmoothNormalizationOver X W).left (AmbientMap.BundleCycles.schemeSmoothNormalizationOver X W).hom d r))
    (schemeNormalizedFunction_restrictedAmbientSection X W s))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.SchemeNormalization.SectionGerm.BundleCycles
