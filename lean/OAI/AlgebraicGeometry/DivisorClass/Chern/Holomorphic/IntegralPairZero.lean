import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.VariableMetricIntegral
import Mathlib.Analysis.InnerProductSpace.Completion

/-! # Integral Pair Zero -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.DivisorClass.Chern.Holomorphic.IntegralPairZero

/-! Native Hilbert completions for every actual Hermitian metric on the original bundle. -/

open _root_.TopologicalSpace UniformSpace
open scoped _root_.Manifold

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace}
  (h : HolomorphicMetric.Data.HolomorphicLineMetricData u) (n : ℕ)

abbrev HolomorphicMetricFormWith :=
  OAI.Analysis.HodgeTheory.Decomposition.MetricFiber.Constructions.HermitianFiber (HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) (h.formInnerProductCore V n)

abbrev HolomorphicFormL2With := Completion (HolomorphicMetricFormWith V h n)

def holomorphicFormL2WithInclusion : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n →ₗ[ℂ] HolomorphicFormL2With V h n :=
  (Completion.toComplₗᵢ : HolomorphicMetricFormWith V h n →ₗᵢ[ℂ] HolomorphicFormL2With V h n).toLinearMap.comp
    (OAI.Analysis.HodgeTheory.Decomposition.MetricFiber.Constructions.hermitianFiberEquiv _ (h.formInnerProductCore V n)).symm.toLinearMap

theorem holomorphicFormL2WithInclusion_injective : Function.Injective (holomorphicFormL2WithInclusion V h n) :=
  (Completion.toComplₗᵢ : HolomorphicMetricFormWith V h n →ₗᵢ[ℂ] HolomorphicFormL2With V h n).injective.comp
    (OAI.Analysis.HodgeTheory.Decomposition.MetricFiber.Constructions.hermitianFiberEquiv _ (h.formInnerProductCore V n)).symm.injective

theorem holomorphicFormL2WithInclusion_inner (a b : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) :
    inner ℂ (holomorphicFormL2WithInclusion V h n a) (holomorphicFormL2WithInclusion V h n b) =
      h.formIntegralPair V n a b := by
  change inner ℂ ((OAI.Analysis.HodgeTheory.Decomposition.MetricFiber.Constructions.HermitianFiber.mk a : HolomorphicMetricFormWith V h n) : HolomorphicFormL2With V h n)
    ((OAI.Analysis.HodgeTheory.Decomposition.MetricFiber.Constructions.HermitianFiber.mk b : HolomorphicMetricFormWith V h n) : HolomorphicFormL2With V h n) = _
  rw [Completion.inner_coe]
  rfl

theorem holomorphicFormL2WithInclusion_norm_sq (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) :
    ‖holomorphicFormL2WithInclusion V h n a‖ ^ 2 = (h.formIntegralPair V n a a).re := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), holomorphicFormL2WithInclusion_inner]
  rfl

theorem holomorphicFormL2WithInclusion_dense : DenseRange (holomorphicFormL2WithInclusion V h n) := by
  change DenseRange ((fun a : HolomorphicMetricFormWith V h n => (a : HolomorphicFormL2With V h n)) ∘
    (OAI.Analysis.HodgeTheory.Decomposition.MetricFiber.Constructions.hermitianFiberEquiv _ (h.formInnerProductCore V n)).symm)
  change Dense (Set.range _)
  rw [Set.range_comp, (OAI.Analysis.HodgeTheory.Decomposition.MetricFiber.Constructions.hermitianFiberEquiv _ (h.formInnerProductCore V n)).symm.surjective.range_eq,
    Set.image_univ]
  exact Completion.denseRange_coe

end AlgebraicGeometry.DivisorClass.Chern.Holomorphic.IntegralPairZero

namespace AlgebraicGeometry.DivisorClass.Chern

/-! Zero arguments vanish in the actual original metric integral pairing. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u) (n : ℕ)

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.formIntegralPair_zero_right (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) :
    h.formIntegralPair V n a 0 = 0 := by
  rw [← Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion_inner, map_zero, inner_zero_right]

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.formIntegralPair_zero_left (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) :
    h.formIntegralPair V n 0 a = 0 := by
  rw [← Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion_inner, map_zero, inner_zero_left]

end AlgebraicGeometry.DivisorClass.Chern

end

end OAI
