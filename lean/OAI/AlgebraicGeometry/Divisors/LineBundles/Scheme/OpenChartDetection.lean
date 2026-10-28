import OAI.AlgebraicGeometry.Divisors.LineBundles.Open.ImageCohomologyDetection

/-! # Open Chart Detection -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.OpenChartDetection.BundleCycles

noncomputable section

/-! Algebraic open charts covering the regular support detect equality
of supported cycle-degree classes through their actual point maps. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
    [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]
    (Z : IrreducibleCloseds X.left)

local notation "T" => TopCat.of (OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
local notation "S" => (Set.range (OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion X Z))ᶜ

theorem schemeSupportedClass_eq_of_open_charts (p : ℕ)
    (hp : Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z X.hom + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom)
    (U : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularOver X Z) → Over Foundations.Scheme.ProjectiveSpace.complexBase)
    (i : ∀ x, U x ⟶ X) [∀ x, IsOpenImmersion (i x).left]
    (hU : ∀ x, CycleClass.Thom.Scheme.RegularSupport.Constructions.regularInclusion X Z x ∈ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (i x)))
    (a b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) T S (2 * p))
    (hab : ∀ x, AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map (i x))
        (A := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (i x) ⁻¹' S) (B := S) (fun _ hy => hy) (2 * p) a =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map (i x))
        (A := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (i x) ⁻¹' S) (B := S) (fun _ hy => hy) (2 * p) b) : a = b := by
  apply SupportNeighborhoodDetection.BundleCycles.schemeSupportedClass_eq_of_regular_neighborhoods X Z p hp
    (fun x => HolomorphicOpenImage.BundleCycles.holomorphicOpenImage (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (i x))
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isOpenEmbedding_map_of_isOpenImmersion (i x))) hU
  intro x
  exact Open.ImageCohomologyDetection.BundleCycles.openImageRestriction_eq_of_pullback_eq (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (i x))
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isOpenEmbedding_map_of_isOpenImmersion (i x)) S (2 * p) a b (hab x)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.OpenChartDetection.BundleCycles
