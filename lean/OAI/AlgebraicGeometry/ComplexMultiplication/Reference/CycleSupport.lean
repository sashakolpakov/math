import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.DimensionCycleSupports
import OAI.AlgebraicGeometry.ComplexMultiplication.PointBettiBridge
import OAI.AlgebraicGeometry.ComplexMultiplication.AnalyticIntrinsicAtlasRegular
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.SupportRegularBoundary

/-! # Cycle Support -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Reference.CycleSupport

noncomputable section

/-! # The same analytic support and actual smooth locus of every cycle -/

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint _root_.TopologicalSpace

attribute [-instance] ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.instTopologicalSpace

open OAI.AlgebraicGeometry.ComplexPoints.Analytic.SupportRegularBoundary

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]
  [Foundations.ProjectiveSpaceIs.IsProjective X.hom] (p : ℕ) (x : CycleClassMap.OriginalCycleComponent X p)

local notation "D" => OAI.AlgebraicGeometry.ComplexMultiplication.Reference.DimensionCycleSupports.originalDimensionSupport X p x

/-- The image of the actual native cycle inclusion is the original analytic support. -/
theorem originalDimensionSupport_analyticSupport :
    Set.range (D).analyticInclusion =
      (PointBettiBridge.complexPointSpaceIso X).hom ⁻¹' Cycle.Support.cycleComponentSupport X x.val := by
  rw [(D).range_analyticInclusion]
  ext q
  change ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying q ∈ closure {x.val} ↔
    ComplexPoint.Basic.Point.underlying q ∈ closure {x.val}
  rw [AnalyticIntrinsicAtlasRegular.nativeUnderlying_eq_original]

/-- Both singular boundaries remove exactly the same actual nonsmooth scheme points. -/
theorem originalDimensionSupport_singularBoundary :
    (D).analyticSingularBoundary =
      (PointBettiBridge.complexPointSpaceIso X).hom ⁻¹'
        (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSingularAnalyticClosedFiltration X x.val 0 : Set _) := by
  ext q
  change ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying q ∈
      Cycle.Support.cycleComponentι X.left x.val ''
        ((Cycle.Support.cycleComponentι X.left x.val ≫ X.hom).smoothLocus : Set _)ᶜ ↔
    ComplexPoint.Basic.Point.underlying q ∈ Cycle.Support.cycleComponentι X.left x.val ''
        ((Cycle.Support.cycleComponentι X.left x.val ≫ X.hom).smoothLocus : Set _)ᶜ
  rw [AnalyticIntrinsicAtlasRegular.nativeUnderlying_eq_original]

/-- The native smooth-stratum structure map differs only by category associativity. -/
theorem originalDimensionSupport_regularToBase :
    (D).regularToBase = (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothLocusOver X x.val).hom := by
  change (Cycle.Support.cycleComponentι X.left x.val ≫ X.hom).smoothLocus.ι ≫
      (Cycle.Support.cycleComponentι X.left x.val ≫ X.hom) =
    ((Cycle.Support.cycleComponentι X.left x.val ≫ X.hom).smoothLocus.ι ≫
      Cycle.Support.cycleComponentι X.left x.val) ≫ X.hom
  exact (Category.assoc _ _ _).symm

/-- The regular support is the literal original smooth-locus scheme over the same field. -/
def originalDimensionSupport_regularOverIso :
    (D).regularOver ≅ ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothLocusOver X x.val :=
  eqToIso (congrArg Over.mk (originalDimensionSupport_regularToBase X p x))

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Reference.CycleSupport
