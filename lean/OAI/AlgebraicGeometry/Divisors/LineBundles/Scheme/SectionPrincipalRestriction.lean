import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.OpenPairSupport
import OAI.AlgebraicGeometry.Divisors.LineBundles.SchemeNormalization.IntersectionSupport
import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.SupportSection

/-! # Section Principal Restriction -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.SectionPrincipalRestriction.BundleCycles

noncomputable section

/-! The canonical class of the original full principal cycle restricts to the principal class appearing in the finite normalization formula. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
  [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]
  (W : IrreducibleCloseds X.left) (s : Γ(X.left, ⊤))

local instance sectionPrincipalRestrictionTop : Nonempty (⊤ : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).Opens) :=
  ⟨⟨genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme W), Opens.mem_top _⟩⟩

variable (n p : ℕ) (hn : n + (p + 1) = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom)

def schemeSectionPrincipalSupportedClass :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
      (SupportSectionCup.BundleCycles.schemeSupportSectionIntersection X W s)ᶜ (2 * (p + 1)) :=
  OpenSupportedCycle.BundleCycles.schemeClosedRelativeClassMap X (SupportSectionCup.BundleCycles.schemeSupportSectionIntersection X W s) n (p + 1) hn
    (OpenSupportedCycle.BundleCycles.schemeClosedRestrictCycle X (SupportSectionCup.BundleCycles.schemeSupportSectionIntersection X W s) n
      (Graded.GlobalSpecialization.BundleCycles.schemeGradedPrincipalDivisor X.hom n W
        ((CycleClass.Geometric.GenericPoint.reducedSupportScheme W).germToFunctionField ⊤ ((CycleClass.Geometric.GenericPoint.reducedSupportι W).appTop s))))

theorem schemeSectionPrincipalSupportedClass_normalization :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map (CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeInclusion X (SchemeNormalization.AmbientMap.BundleCycles.schemeNormalizationAmbientOpen X W)))
      (SupportSectionCup.BundleCycles.schemeNormalizationSectionCup_mapsTo X W s) (2 * (p + 1))
      (schemeSectionPrincipalSupportedClass X W s n p hn) =
    OpenSupportedCycle.BundleCycles.schemeClosedRelativeClassMap (SchemeNormalization.Ambient.BundleCycles.schemeNormalizationAmbientOver X W) (SchemeNormalization.SectionFormula.BundleCycles.schemeNormalizationSectionSupport X W s)
      n (p + 1) (hn.trans (SchemeNormalization.Ambient.BundleCycles.schemeNormalizationAmbient_dimension X W).symm)
      (OpenSupportedCycle.BundleCycles.schemeClosedRestrictCycle (SchemeNormalization.Ambient.BundleCycles.schemeNormalizationAmbientOver X W) (SchemeNormalization.SectionFormula.BundleCycles.schemeNormalizationSectionSupport X W s) n
        (Open.GradedOverRestriction.BundleCycles.openOverGradedRestriction (CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeInclusion X (SchemeNormalization.AmbientMap.BundleCycles.schemeNormalizationAmbientOpen X W)) n
          (Graded.GlobalSpecialization.BundleCycles.schemeGradedPrincipalDivisor X.hom n W
            ((CycleClass.Geometric.GenericPoint.reducedSupportScheme W).germToFunctionField ⊤ ((CycleClass.Geometric.GenericPoint.reducedSupportι W).appTop s))))) :=
  OpenPairSupport.BundleCycles.schemeClosedRestrictedClass_openPullback_of_support
    (CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeInclusion X (SchemeNormalization.AmbientMap.BundleCycles.schemeNormalizationAmbientOpen X W))
    (SupportSectionCup.BundleCycles.schemeSupportSectionIntersection X W s) (SchemeNormalization.SectionFormula.BundleCycles.schemeNormalizationSectionSupport X W s)
    (SchemeNormalization.IntersectionSupport.BundleCycles.schemeNormalizationSectionSupport_preimage X W s) n (p + 1) hn _
    (SupportSection.BundleCycles.schemeGradedPrincipalSection_supported X W s n)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.SectionPrincipalRestriction.BundleCycles
