import OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SupportDetection

/-! # Support Exceptional Detection -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Closed.SupportExceptionalDetection.BundleCycles

noncomputable section

/-! Removing any algebraic exceptional set of greater codimension detects the first supported degree, even when the exceptional set is not contained in the support. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SectionEvaluation.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SupportDetection.Constructions.Neighborhoods OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SupportDetection.Constructions

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
  [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]
  (F E : Closeds X.left) (c : ℕ)
  (hF : ∀ Z : IrreducibleCloseds X.left, (Z : Set X.left) ⊆ F →
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z X.hom + c ≤ Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom)
  (hE : ∀ Z : IrreducibleCloseds X.left, (Z : Set X.left) ⊆ E →
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z X.hom + (c + 1) ≤ Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom)

include hE in
omit [Smooth X.hom] [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] in
theorem closedSupportMinimalPoint_avoids_exceptional (Z : CycleClass.Thom.Scheme.SupportDetection.Constructions.Neighborhoods.MinimalSupport X F c) :
    irreducibleSetEquivPoints Z.val ∈ E.compl := by
  intro hz
  have he : (Z.val : Set X.left) ⊆ E := by
    have hc := closure_minimal (Set.singleton_subset_iff.mpr hz) E.isClosed
    change (irreducibleSetEquivPoints.symm (irreducibleSetEquivPoints Z.val) : Set X.left) ⊆ E at hc
    simpa only [OrderIso.symm_apply_apply] using hc
  have hd := hE Z.val he
  have hzdim := Z.property.2
  omega

include hF hE in
theorem closedSupport_exceptionalRestriction_injective :
    Function.Injective (CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ)
      (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (CycleClass.Thom.Scheme.SectionEvaluation.Constructions.analyticOpen X F.compl : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
      (CycleClass.Thom.Scheme.SectionEvaluation.Constructions.analyticOpen X E.compl) (2 * c)) := by
  intro a b hab
  exact CycleClass.Thom.Scheme.SupportDetection.Constructions.relativeClass_eq_of_component_neighborhoods X F c hF (fun _ => E.compl)
    (closedSupportMinimalPoint_avoids_exceptional X F E c hE) a b (fun _ => hab)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Closed.SupportExceptionalDetection.BundleCycles
