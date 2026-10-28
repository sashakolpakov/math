import OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ClosedSupportPurity

/-! # Open Support Removal -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.OpenSupportRemoval.Constructions

noncomputable section

/-! Removing a higher-codimension algebraic exceptional set preserves actual supported cohomology on every analytic open neighborhood. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
  [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]
  (F : Closeds X.left) (c : ℕ)
  (hc : ∀ Z : IrreducibleCloseds X.left, (Z : Set X.left) ⊆ F →
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z X.hom + c ≤ Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom)
  (U : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (B : Set U)
  (hB : B ⊆ {x : U | ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x.val ∈ F}ᶜ)
  (n : ℕ) (hn : n + 1 < 2 * c)

include hc hB hn in
theorem open_relativeRestriction_isIso :
    IsIso (Geometric.RelativeCochainTriple.Cohomology.relativeCohomologyTripleRestriction (ModuleCat.of ℚ ℚ) (TopCat.of U)
      {x : U | ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x.val ∈ F}ᶜ B n) :=
  Geometric.RelativeCochainTriple.Cohomology.relativeCohomologyTripleRestriction_isIso (ModuleCat.of ℚ ℚ) (TopCat.of U) _ B hB n
    (ClosedSupportPurity.Constructions.closedSupport_open_cohomology_isZero X F c hc U n (by omega))
    (ClosedSupportPurity.Constructions.closedSupport_open_cohomology_isZero X F c hc U (n + 1) hn)

include hc hB hn in
theorem open_relativeRestriction_injective :
    Function.Injective (Geometric.RelativeCochainTriple.Cohomology.relativeCohomologyTripleRestriction (ModuleCat.of ℚ ℚ) (TopCat.of U)
      {x : U | ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x.val ∈ F}ᶜ B n) := by
  let := open_relativeRestriction_isIso X F c hc U B hB n hn
  exact (ModuleCat.mono_iff_injective _).mp inferInstance

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.OpenSupportRemoval.Constructions
