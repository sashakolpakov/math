import OAI.AlgebraicGeometry.ComplexMultiplication.IntrinsicOpenImmersionDifferentiable
import OAI.AlgebraicGeometry.DivisorClass.Chern.Open.ImmersionPurity

/-! # Open Chart Restriction -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.OpenChartRestriction

noncomputable section

section

/-! # Restricting the actual complex chart to an ambient open preserves differentiability -/

open _root_.TopologicalSpace
open scoped ContDiff _root_.Manifold

variable {E F M N : Type}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace F N]

theorem complexOpenInclusion_mDifferentiable (U : Opens M) (hU : Nonempty U) :
    (U.openPartialHomeomorphSubtypeCoe hU).MDifferentiable 𝓘(ℂ, E) 𝓘(ℂ, E) := by
  constructor
  · exact (contMDiff_subtype_val (I := 𝓘(ℂ, E)) (U := U) (n := ∞)).mdifferentiable
      (by simp) |>.mdifferentiableOn
  · intro y hy
    have hyU : y ∈ (U : Set M) := by
      simpa only [Opens.openPartialHomeomorphSubtypeCoe_target] using hy
    exact ((DivisorClass.Chern.Open.ImmersionPurity.complexOpenInverse_contMDiffAt U hU hyU).mdifferentiableAt
      (by simp)).mdifferentiableWithinAt

theorem complexChart_subtypeRestr_mDifferentiable (e : OpenPartialHomeomorph M N)
    (he : e.MDifferentiable 𝓘(ℂ, E) 𝓘(ℂ, F)) (U : Opens M) (hU : Nonempty U) :
    (e.subtypeRestr hU).MDifferentiable 𝓘(ℂ, E) 𝓘(ℂ, F) := by
  exact (complexOpenInclusion_mDifferentiable U hU).trans he

end

/-! # The original open-scheme points and the native ambient points use the same differentiable map -/

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint _root_.TopologicalSpace
open scoped _root_.Manifold

attribute [-instance] ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.instTopologicalSpace

variable {Y X : Over (Spec (.of ℂ))} [IsIntegral Y.left] [Smooth Y.hom]
  [IsIntegral X.left] [Smooth X.hom] [Nonempty (AnalyticIntrinsicAtlasRegular.NativePointManifold Y)]
  (φ : Y ⟶ X) [IsOpenImmersion φ.left]

/-- This is the actual original point map into the actual native ambient manifold. -/
def originalOpenImmersionPointPartialHomeomorph :
    OpenPartialHomeomorph (ComplexPoint.Basic.ComplexSchemePoint Y) (AnalyticIntrinsicAtlasRegular.NativePointManifold X) :=
  (AnalyticIntrinsicAtlasRegular.nativePointManifoldHomeomorph Y).symm.toOpenPartialHomeomorph.trans
    (IntrinsicOpenImmersionDifferentiable.nativeOpenImmersionPointPartialHomeomorph φ)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem originalOpenImmersionPointPartialHomeomorph_mDifferentiable :
    (originalOpenImmersionPointPartialHomeomorph φ).MDifferentiable
      𝓘(ℂ, Fin (Topology.Dimension.Basic.TopologicalSpace.dim Y.left) → ℂ)
      𝓘(ℂ, Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ) := by
  have hh : (AnalyticIntrinsicAtlasRegular.nativePointManifoldHomeomorph Y).symm.toOpenPartialHomeomorph.MDifferentiable
      𝓘(ℂ, Fin (Topology.Dimension.Basic.TopologicalSpace.dim Y.left) → ℂ)
      𝓘(ℂ, Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom) → ℂ) := by
    constructor
    · intro x _
      exact ((AnalyticIntrinsicAtlasRegular.contMDiff_nativePointManifoldHomeomorph_symm Y 1).mdifferentiableAt
        one_ne_zero).mdifferentiableWithinAt
    · intro y _
      exact ((AnalyticIntrinsicAtlasRegular.contMDiff_nativePointManifoldHomeomorph Y 1).mdifferentiableAt
        one_ne_zero).mdifferentiableWithinAt
  exact hh.trans (IntrinsicOpenImmersionDifferentiable.nativeOpenImmersionPointPartialHomeomorph_mDifferentiable φ)

omit [IsIntegral Y.left] [Smooth Y.hom] [IsIntegral X.left] [Smooth X.hom] in
@[simp] theorem originalOpenImmersionPointPartialHomeomorph_apply (y : ComplexPoint.Basic.ComplexSchemePoint Y) :
    originalOpenImmersionPointPartialHomeomorph φ y = ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map φ y := rfl

omit [IsIntegral Y.left] [Smooth Y.hom] [IsIntegral X.left] [Smooth X.hom] in
@[simp] theorem originalOpenImmersionPointPartialHomeomorph_source :
    (originalOpenImmersionPointPartialHomeomorph φ).source = Set.univ := by
  have hs : (IntrinsicOpenImmersionDifferentiable.nativeOpenImmersionPointPartialHomeomorph φ).source = Set.univ := rfl
  simp only [originalOpenImmersionPointPartialHomeomorph, OpenPartialHomeomorph.trans_source,
    Homeomorph.toOpenPartialHomeomorph_source, hs, Set.preimage_univ, Set.inter_self]

end

end OAI.AlgebraicGeometry.ComplexMultiplication.OpenChartRestriction
