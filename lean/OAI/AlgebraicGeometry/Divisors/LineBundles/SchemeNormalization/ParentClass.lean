import OAI.AlgebraicGeometry.Divisors.LineBundles.SchemeNormalization.FiniteParent
import OAI.AlgebraicGeometry.Divisors.LineBundles.SchemeCycle.PreimageSupport
import OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.ParentGraphProjection

/-! # Parent Class -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.SchemeNormalization.ParentClass.BundleCycles

noncomputable section

/-! The canonical class of the finite smooth normalization image is the actual open pullback of the original support class. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ProperSupport.Constructions

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
  [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]
  (W : IrreducibleCloseds X.left)

omit [AlgebraicGeometry.IsIntegral X.left] [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] in
theorem schemeNormalizationParent_preimage :
    (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport (AmbientMap.BundleCycles.schemeSmoothNormalizationToAmbient X W)
      (Finite.WholeSupport.BundleCycles.wholeSchemeSupport (AmbientMap.BundleCycles.schemeSmoothNormalizationOver X W)) : Set (Ambient.BundleCycles.schemeNormalizationAmbientOver X W).left) =
    (CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeInclusion X (AmbientMap.BundleCycles.schemeNormalizationAmbientOpen X W)).left ⁻¹' (W : Set X.left) := by
  rw [FiniteParent.BundleCycles.schemeNormalizationFiniteParent_image, Open.SupportRestriction.BundleCycles.openRestrictedSupport_coe]

theorem schemeNormalizationParentClass_pullback (p : ℕ)
    (hp : Foundations.Scheme.SupportDimension.supportTranscendenceDimension W X.hom + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map (CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeInclusion X (AmbientMap.BundleCycles.schemeNormalizationAmbientOpen X W)))
      (SchemeCycle.PreimageSupport.BundleCycles.schemeSupportPreimage_mapsTo _ W _ (schemeNormalizationParent_preimage X W)) (2 * p)
      (Scheme.SupportedCycleClass.BundleCycles.schemeSupportedCycleClass X W p hp) =
    Scheme.SupportedCycleClass.BundleCycles.schemeSupportedCycleClass (Ambient.BundleCycles.schemeNormalizationAmbientOver X W)
      (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport (AmbientMap.BundleCycles.schemeSmoothNormalizationToAmbient X W) (Finite.WholeSupport.BundleCycles.wholeSchemeSupport (AmbientMap.BundleCycles.schemeSmoothNormalizationOver X W)))
      p (Finite.ParentGraphProjection.BundleCycles.finiteWholeImage_codimension (AmbientMap.BundleCycles.schemeSmoothNormalizationToAmbient X W) p
        (FiniteParent.BundleCycles.schemeSmoothNormalization_nativeCodimension X W p hp)) :=
  SchemeCycle.PreimageSupport.BundleCycles.schemeSupportedCycleClass_open_of_support _ W _ (schemeNormalizationParent_preimage X W) p hp _

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.SchemeNormalization.ParentClass.BundleCycles
