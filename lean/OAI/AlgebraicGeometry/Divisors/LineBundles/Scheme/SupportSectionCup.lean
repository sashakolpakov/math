import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.SectionClassPullback
import OAI.AlgebraicGeometry.Divisors.LineBundles.SchemeNormalization.ParentClass
import OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.GlobalSectionClassRestriction

/-! # Support Section Cup -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.SupportSectionCup.BundleCycles

noncomputable section

/-! The actual supported cup of a cycle with a global section restricts to the constructed finite normalization cup. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ProperSupport.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation
open OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionCup.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionTo.Constructions.Restriction

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
  [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]
  (W : IrreducibleCloseds X.left) (s : Γ(X.left, ⊤))

def schemeSupportSectionIntersection : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) :=
  Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion X W) ∩ Set.range (CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage X s)

omit [AlgebraicGeometry.IsIntegral X.left] [Smooth X.hom] [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] in
theorem schemeSupport_openComplement : IsOpen (Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion X W))ᶜ :=
  (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isClosedEmbedding_map_of_isClosedImmersion (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportToAmbient X W)).isClosed_range.isOpen_compl

def schemeSupportSectionCup (p : ℕ)
    (hp : Foundations.Scheme.SupportDimension.supportTranscendenceDimension W X.hom + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
      (schemeSupportSectionIntersection X W s)ᶜ (2 * (p + 1)) :=
  CycleClass.Thom.ImageIntersectionCup.Constructions.imageIntersectionCup (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion X W) (CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage X s)
    (schemeSupport_openComplement X W) (CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage_openComplement X s) p 1
    (SupportedCycleClass.BundleCycles.schemeSupportedCycleClass X W p hp) (Finite.GlobalSectionClassRestriction.BundleCycles.schemeSectionSupportedClass X s)

omit [AlgebraicGeometry.IsIntegral X.left] [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] in
theorem schemeNormalizationSectionCup_mapsTo : Set.MapsTo
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map (CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeInclusion X (SchemeNormalization.AmbientMap.BundleCycles.schemeNormalizationAmbientOpen X W)))
    (Finite.RegularPrincipalSupport.BundleCycles.finiteRegularSectionSupport (SchemeNormalization.AmbientMap.BundleCycles.schemeSmoothNormalizationToAmbient X W)
      ((CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeInclusion X (SchemeNormalization.AmbientMap.BundleCycles.schemeNormalizationAmbientOpen X W)).left.appTop s))ᶜ
    (schemeSupportSectionIntersection X W s)ᶜ :=
  CycleClass.Thom.ImageIntersectionTo.Constructions.Restriction.intersectionMapsTo (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion X W) (CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage X s)
    (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion (SchemeNormalization.Ambient.BundleCycles.schemeNormalizationAmbientOver X W)
      (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport (SchemeNormalization.AmbientMap.BundleCycles.schemeSmoothNormalizationToAmbient X W) (Finite.WholeSupport.BundleCycles.wholeSchemeSupport (SchemeNormalization.AmbientMap.BundleCycles.schemeSmoothNormalizationOver X W))))
    (CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage (SchemeNormalization.Ambient.BundleCycles.schemeNormalizationAmbientOver X W)
      ((CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeInclusion X (SchemeNormalization.AmbientMap.BundleCycles.schemeNormalizationAmbientOpen X W)).left.appTop s))
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map (CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeInclusion X (SchemeNormalization.AmbientMap.BundleCycles.schemeNormalizationAmbientOpen X W)))
    (SchemeCycle.PreimageSupport.BundleCycles.schemeSupportPreimage_mapsTo _ W _ (SchemeNormalization.ParentClass.BundleCycles.schemeNormalizationParent_preimage X W))
    (SectionClassPullback.BundleCycles.schemeSectionClass_mapsTo _ s)

theorem schemeSupportSectionCup_normalization (p : ℕ)
    (hp : Foundations.Scheme.SupportDimension.supportTranscendenceDimension W X.hom + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map (CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeInclusion X (SchemeNormalization.AmbientMap.BundleCycles.schemeNormalizationAmbientOpen X W)))
      (schemeNormalizationSectionCup_mapsTo X W s) (2 * (p + 1)) (schemeSupportSectionCup X W s p hp) =
    Finite.GlobalSectionClassRestriction.BundleCycles.finiteGlobalSectionCup (SchemeNormalization.AmbientMap.BundleCycles.schemeSmoothNormalizationToAmbient X W)
      ((CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeInclusion X (SchemeNormalization.AmbientMap.BundleCycles.schemeNormalizationAmbientOpen X W)).left.appTop s)
      p (SchemeNormalization.FiniteParent.BundleCycles.schemeSmoothNormalization_nativeCodimension X W p hp) := by
  let j := CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeInclusion X (SchemeNormalization.AmbientMap.BundleCycles.schemeNormalizationAmbientOpen X W)
  let k := SchemeNormalization.AmbientMap.BundleCycles.schemeSmoothNormalizationToAmbient X W
  have h := CycleClass.Thom.ImageIntersectionTo.Constructions.Restriction.imageIntersectionCup_restriction (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion X W) (CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage X s)
    (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion (SchemeNormalization.Ambient.BundleCycles.schemeNormalizationAmbientOver X W) (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport k (Finite.WholeSupport.BundleCycles.wholeSchemeSupport (SchemeNormalization.AmbientMap.BundleCycles.schemeSmoothNormalizationOver X W))))
    (CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage (SchemeNormalization.Ambient.BundleCycles.schemeNormalizationAmbientOver X W) (j.left.appTop s))
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map j)
    (SchemeCycle.PreimageSupport.BundleCycles.schemeSupportPreimage_mapsTo j W _ (SchemeNormalization.ParentClass.BundleCycles.schemeNormalizationParent_preimage X W))
    (SectionClassPullback.BundleCycles.schemeSectionClass_mapsTo j s)
    (schemeSupport_openComplement X W) (CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage_openComplement X s)
    (Finite.GlobalSectionClassRestriction.BundleCycles.finiteParentImage_openComplement k) (CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage_openComplement _ _)
    p 1 (SupportedCycleClass.BundleCycles.schemeSupportedCycleClass X W p hp) (Finite.GlobalSectionClassRestriction.BundleCycles.schemeSectionSupportedClass X s)
  unfold Finite.GlobalSectionClassRestriction.BundleCycles.finiteGlobalSectionCup
  rw [SchemeNormalization.FiniteParent.BundleCycles.schemeSmoothNormalization_genericDegree, Nat.cast_one, one_smul]
  exact h.trans (congrArg₂
    (CycleClass.Thom.ImageIntersectionCup.Constructions.imageIntersectionCup
      (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion (SchemeNormalization.Ambient.BundleCycles.schemeNormalizationAmbientOver X W) (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport k (Finite.WholeSupport.BundleCycles.wholeSchemeSupport (SchemeNormalization.AmbientMap.BundleCycles.schemeSmoothNormalizationOver X W))))
      (CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage (SchemeNormalization.Ambient.BundleCycles.schemeNormalizationAmbientOver X W) (j.left.appTop s))
      (Finite.GlobalSectionClassRestriction.BundleCycles.finiteParentImage_openComplement k) (CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage_openComplement _ _) p 1)
    (SchemeNormalization.ParentClass.BundleCycles.schemeNormalizationParentClass_pullback X W p hp)
    (SectionClassPullback.BundleCycles.schemeSectionSupportedClass_pullback j s))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.SupportSectionCup.BundleCycles
