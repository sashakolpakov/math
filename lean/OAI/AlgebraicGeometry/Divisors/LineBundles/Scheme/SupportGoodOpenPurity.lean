import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.SupportNeighborhoodDetection
import OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SmoothSupportOpen
import OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.OpenSupportRemoval

/-! # Support Good Open Purity -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.SupportGoodOpenPurity.BundleCycles

noncomputable section

/-! On every analytic ambient neighborhood, deleting the omitted
boundary of a dense support open preserves supported cycle-degree classes. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SmoothSupportOpen.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.OpenSupportRemoval.Constructions

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
    [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]
    (Z : IrreducibleCloseds X.left) (W : (CycleClass.Geometric.GenericPoint.reducedSupportScheme Z).Opens)
    (U : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))

omit [AlgebraicGeometry.IsIntegral X.left] [Smooth X.hom] [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] in
theorem schemeSupportComplement_subset_goodOpen :
    AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion X Z))ᶜ U ⊆
      {x : U | ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x.val ∈ CycleClass.Thom.Scheme.SmoothSupportOpen.Constructions.supportOpenBoundary X Z W}ᶜ := by
  intro x hx h
  apply hx
  rw [CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion_range]
  exact CycleClass.Thom.Scheme.SmoothSupportOpen.Constructions.supportOpenBoundary_subset X Z W h

theorem schemeSupport_goodRestriction_isIso (p : ℕ)
    (hp : Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z X.hom + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom)
    (hW : genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme Z) ∈ W) :
    IsIso (CycleClass.Geometric.RelativeCochainTriple.Cohomology.relativeCohomologyTripleRestriction (ModuleCat.of ℚ ℚ) (TopCat.of U)
      {x : U | ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x.val ∈ CycleClass.Thom.Scheme.SmoothSupportOpen.Constructions.supportOpenBoundary X Z W}ᶜ
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion X Z))ᶜ U) (2 * p)) := by
  have hc (A : IrreducibleCloseds X.left) (hA : (A : Set X.left) ⊆ CycleClass.Thom.Scheme.SmoothSupportOpen.Constructions.supportOpenBoundary X Z W) :
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension A X.hom + (p + 1) ≤ Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom := by
    have h := CycleClass.Thom.Scheme.SmoothSupportOpen.Constructions.supportOpenBoundary_dimension_lt X Z W hW A hA
    omega
  exact CycleClass.Thom.Scheme.OpenSupportRemoval.Constructions.open_relativeRestriction_isIso X (CycleClass.Thom.Scheme.SmoothSupportOpen.Constructions.supportOpenBoundary X Z W) (p + 1) hc U
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion X Z))ᶜ U)
    (schemeSupportComplement_subset_goodOpen X Z W U) (2 * p) (by omega)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.SupportGoodOpenPurity.BundleCycles
