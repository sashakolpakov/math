import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.OpenSupportedCycle

/-! # Supported Generator Comparison -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.SupportedGeneratorComparison.BundleCycles

noncomputable section

/-! Replacing a graded point's support by its proved geometric image does not change its canonical common-support class. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
  [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]
  (U : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (S : Set U) (d p : ℕ)
  (hd : d + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom)

theorem schemeOpenRelativeGenerator_of_support_eq (x : OpenSupportedCycle.BundleCycles.schemeOpenSupportedPoint X U S d)
    (C : IrreducibleCloseds X.left)
    (hC : Foundations.Scheme.SupportDimension.supportTranscendenceDimension C X.hom + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom)
    (he : irreducibleSetEquivPoints.symm x.val.val = C)
    (hm : Set.MapsTo (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)))
      Sᶜ (Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion X C))ᶜ) :
    OpenSupportedCycle.BundleCycles.schemeOpenRelativeGenerator X U S d p hd x =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
        (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))) hm (2 * p)
        (SupportedCycleClass.BundleCycles.schemeSupportedCycleClass X C p hC) := by
  subst C
  rfl

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.SupportedGeneratorComparison.BundleCycles
