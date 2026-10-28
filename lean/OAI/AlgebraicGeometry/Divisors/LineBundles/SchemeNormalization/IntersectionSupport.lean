import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.SupportSectionCup
import OAI.AlgebraicGeometry.Divisors.LineBundles.SchemeNormalization.SectionFormula

/-! # Intersection Support -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.SchemeNormalization.IntersectionSupport.BundleCycles

noncomputable section

/-! The normalized section support is the literal inverse image of the original section intersection. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ProperSupport.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
  [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]
  (W : IrreducibleCloseds X.left) (s : Γ(X.left, ⊤))

omit [AlgebraicGeometry.IsIntegral X.left] [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] in
theorem schemeNormalizationSectionSupport_preimage :
    SectionFormula.BundleCycles.schemeNormalizationSectionSupport X W s =
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeInclusion X (AmbientMap.BundleCycles.schemeNormalizationAmbientOpen X W)) ⁻¹'
        Scheme.SupportSectionCup.BundleCycles.schemeSupportSectionIntersection X W s := by
  unfold SectionFormula.BundleCycles.schemeNormalizationSectionSupport Finite.RegularPrincipalSupport.BundleCycles.finiteRegularSectionSupport
  rw [SchemeCycle.PreimageSupport.BundleCycles.schemeSupportPreimage_pointRange _ W _ (ParentClass.BundleCycles.schemeNormalizationParent_preimage X W),
    Scheme.SectionClassPullback.BundleCycles.schemeSectionZeroImage_pullback]
  rfl

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.SchemeNormalization.IntersectionSupport.BundleCycles
