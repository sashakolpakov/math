import OAI.AlgebraicGeometry.Divisors.LineBundles.Closed.SupportExceptionalDetection
import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.OpenPairSupport
import OAI.AlgebraicGeometry.Divisors.LineBundles.SchemeNormalization.IntersectionSupport
import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.SupportSection

/-! # Section Detection -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.SchemeNormalization.SectionDetection.BundleCycles

noncomputable section

/-! The actual normalization ambient inclusion detects section-intersection supported classes in the principal-cycle degree. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SectionEvaluation.Constructions

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
  [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]
  (W : IrreducibleCloseds X.left) (s : Γ(X.left, ⊤))

local instance normalizationSectionDetectionTop : Nonempty (⊤ : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).Opens) :=
  ⟨⟨genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme W), Opens.mem_top _⟩⟩

variable (hs : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).germToFunctionField ⊤ ((CycleClass.Geometric.GenericPoint.reducedSupportι W).appTop s) ≠ 0)
  (p : ℕ) (hp : Foundations.Scheme.SupportDimension.supportTranscendenceDimension W X.hom + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom)

include hs hp in
theorem schemeNormalizationSectionPullback_injective :
    Function.Injective (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map (CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeInclusion X (AmbientMap.BundleCycles.schemeNormalizationAmbientOpen X W)))
      (Scheme.SupportSectionCup.BundleCycles.schemeNormalizationSectionCup_mapsTo X W s) (2 * (p + 1))) := by
  have h : Function.Injective (CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ)
      (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (Scheme.SupportSectionCup.BundleCycles.schemeSupportSectionIntersection X W s)ᶜ
      (CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction.schemeAnalyticOpen X (AmbientMap.BundleCycles.schemeNormalizationAmbientOpen X W)) (2 * (p + 1))) := by
    rw [← Scheme.SupportSection.BundleCycles.schemeSupportSectionClosed_analytic X W s]
    exact Closed.SupportExceptionalDetection.BundleCycles.closedSupport_exceptionalRestriction_injective X (Scheme.SupportSection.BundleCycles.schemeSupportSectionClosed X W s)
      (Boundary.BundleCycles.schemeNormalizationExceptional X W) (p + 1)
      (Scheme.SupportSection.BundleCycles.schemeSupportSectionClosed_codimension X W s hs p hp)
      (Boundary.BundleCycles.schemeNormalizationExceptional_codimension X W p hp)
  exact Scheme.OpenPairSupport.BundleCycles.schemeOpenPairPullback_injective_of_analytic_support X (AmbientMap.BundleCycles.schemeNormalizationAmbientOpen X W)
    (Scheme.SupportSectionCup.BundleCycles.schemeSupportSectionIntersection X W s) (SectionFormula.BundleCycles.schemeNormalizationSectionSupport X W s)
    (IntersectionSupport.BundleCycles.schemeNormalizationSectionSupport_preimage X W s) (2 * (p + 1)) h

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.SchemeNormalization.SectionDetection.BundleCycles
