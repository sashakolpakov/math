import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.NormalizedSection
import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.NormalizedGradedPush

/-! # Normalized Section Cycle -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.NormalizedSectionCycle.BundleCycles

noncomputable section

/-! The actual normalized pushforward of an ambient section divisor equals the original principal cycle on the normalization ambient open, in its full dimension grade. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
  [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]
  (W : IrreducibleCloseds X.left) (d : ℕ)
  (hW : Foundations.Scheme.SupportDimension.supportTranscendenceDimension W X.hom = d + 1) (s : Γ(X.left, ⊤))

local instance normalizedSectionCycleSupportTopNonempty : Nonempty (⊤ : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).Opens) :=
  ⟨⟨genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme W), Opens.mem_top _⟩⟩
local instance normalizedSectionCycleSourceTopNonempty : Nonempty (⊤ : (SchemeNormalization.AmbientMap.BundleCycles.schemeSmoothNormalizationOver X W).left.Opens) :=
  ⟨⟨genericPoint (SchemeNormalization.AmbientMap.BundleCycles.schemeSmoothNormalizationOver X W).left, Opens.mem_top _⟩⟩

variable (hs : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).germToFunctionField ⊤ ((CycleClass.Geometric.GenericPoint.reducedSupportι W).appTop s) ≠ 0)

include hW hs in
omit [AlgebraicGeometry.IsIntegral X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] in
theorem schemePrincipal_open_eq_normalizedSectionPush :
    Open.GradedOverRestriction.BundleCycles.openOverGradedRestriction (CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeInclusion X (SchemeNormalization.AmbientMap.BundleCycles.schemeNormalizationAmbientOpen X W)) d
      (Graded.GlobalSpecialization.BundleCycles.schemeGradedPrincipalDivisor X.hom d W
        ((CycleClass.Geometric.GenericPoint.reducedSupportScheme W).germToFunctionField ⊤ ((CycleClass.Geometric.GenericPoint.reducedSupportι W).appTop s))) =
    Finite.GradedOverPushforward.BundleCycles.finiteOverGradedPushforward (SchemeNormalization.AmbientMap.BundleCycles.schemeSmoothNormalizationToAmbient X W) d
      (Graded.RationalPointDivisor.BundleCycles.gradedRationalPointDivisor (SchemeNormalization.AmbientMap.BundleCycles.schemeSmoothNormalizationOver X W).left
        (SchemeNormalization.AmbientMap.BundleCycles.schemeSmoothNormalizationOver X W).hom d
        ((SchemeNormalization.AmbientMap.BundleCycles.schemeSmoothNormalizationOver X W).left.germToFunctionField ⊤
          ((NormalizedFunction.BundleCycles.schemeNormalizationFullAmbientMap X W).left.appTop s))) := by
  have h := NormalizedGradedPush.BundleCycles.schemePrincipal_open_eq_normalizedPush X W d hW
    ((CycleClass.Geometric.GenericPoint.reducedSupportScheme W).germToFunctionField ⊤ ((CycleClass.Geometric.GenericPoint.reducedSupportι W).appTop s)) hs
  have he : NormalizedGradedPush.BundleCycles.schemeNormalizedGradedPrincipal X W d
      ((CycleClass.Geometric.GenericPoint.reducedSupportScheme W).germToFunctionField ⊤ ((CycleClass.Geometric.GenericPoint.reducedSupportι W).appTop s)) =
    Graded.RationalPointDivisor.BundleCycles.gradedRationalPointDivisor (SchemeNormalization.AmbientMap.BundleCycles.schemeSmoothNormalizationOver X W).left
      (SchemeNormalization.AmbientMap.BundleCycles.schemeSmoothNormalizationOver X W).hom d
      ((SchemeNormalization.AmbientMap.BundleCycles.schemeSmoothNormalizationOver X W).left.germToFunctionField ⊤
        ((NormalizedFunction.BundleCycles.schemeNormalizationFullAmbientMap X W).left.appTop s)) :=
    congrArg (Graded.RationalPointDivisor.BundleCycles.gradedRationalPointDivisor (SchemeNormalization.AmbientMap.BundleCycles.schemeSmoothNormalizationOver X W).left
      (SchemeNormalization.AmbientMap.BundleCycles.schemeSmoothNormalizationOver X W).hom d) (NormalizedSection.BundleCycles.schemeNormalizedFunction_ambientSection X W s)
  exact h.trans (congrArg (Finite.GradedOverPushforward.BundleCycles.finiteOverGradedPushforward (SchemeNormalization.AmbientMap.BundleCycles.schemeSmoothNormalizationToAmbient X W) d) he)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.NormalizedSectionCycle.BundleCycles
