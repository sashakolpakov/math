import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.FormIntegralPair
import Mathlib.Analysis.InnerProductSpace.Completion

/-! # Form Completion -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.FormCompletion

noncomputable section

/-! Native Hilbert completions of the actual metric on smooth bundle-valued forms in every degree. -/

open _root_.TopologicalSpace UniformSpace
open scoped _root_.Manifold

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] NormedSpace.complexToReal

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (u : Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace) (n : ℕ)

abbrev HolomorphicMetricForm :=
  OAI.Analysis.HodgeTheory.Decomposition.MetricFiber.Constructions.HermitianFiber (HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) (FormIntegralPair.holomorphicLineFormInnerProductCore V u n)

abbrev HolomorphicFormL2 := Completion (HolomorphicMetricForm V u n)

def holomorphicFormL2Inclusion : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n →ₗ[ℂ] HolomorphicFormL2 V u n :=
  (Completion.toComplₗᵢ : HolomorphicMetricForm V u n →ₗᵢ[ℂ] HolomorphicFormL2 V u n).toLinearMap.comp
    (OAI.Analysis.HodgeTheory.Decomposition.MetricFiber.Constructions.hermitianFiberEquiv _ (FormIntegralPair.holomorphicLineFormInnerProductCore V u n)).symm.toLinearMap

theorem holomorphicFormL2Inclusion_injective : Function.Injective (holomorphicFormL2Inclusion V u n) :=
  (Completion.toComplₗᵢ : HolomorphicMetricForm V u n →ₗᵢ[ℂ] HolomorphicFormL2 V u n).injective.comp
    (OAI.Analysis.HodgeTheory.Decomposition.MetricFiber.Constructions.hermitianFiberEquiv _ (FormIntegralPair.holomorphicLineFormInnerProductCore V u n)).symm.injective

theorem holomorphicFormL2Inclusion_inner (a b : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) :
    inner ℂ (holomorphicFormL2Inclusion V u n a) (holomorphicFormL2Inclusion V u n b) =
      FormIntegralPair.holomorphicLineFormIntegralPair V u n a b := by
  change inner ℂ ((OAI.Analysis.HodgeTheory.Decomposition.MetricFiber.Constructions.HermitianFiber.mk a : HolomorphicMetricForm V u n) : HolomorphicFormL2 V u n)
    ((OAI.Analysis.HodgeTheory.Decomposition.MetricFiber.Constructions.HermitianFiber.mk b : HolomorphicMetricForm V u n) : HolomorphicFormL2 V u n) = _
  rw [Completion.inner_coe]
  rfl

theorem holomorphicFormL2Inclusion_norm_sq (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) :
    ‖holomorphicFormL2Inclusion V u n a‖ ^ 2 = (FormIntegralPair.holomorphicLineFormIntegralPair V u n a a).re := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), holomorphicFormL2Inclusion_inner]
  rfl

theorem holomorphicFormL2Inclusion_dense : DenseRange (holomorphicFormL2Inclusion V u n) := by
  change DenseRange ((fun a : HolomorphicMetricForm V u n => (a : HolomorphicFormL2 V u n)) ∘
    (OAI.Analysis.HodgeTheory.Decomposition.MetricFiber.Constructions.hermitianFiberEquiv _ (FormIntegralPair.holomorphicLineFormInnerProductCore V u n)).symm)
  change Dense (Set.range _)
  rw [Set.range_comp, (OAI.Analysis.HodgeTheory.Decomposition.MetricFiber.Constructions.hermitianFiberEquiv _ (FormIntegralPair.holomorphicLineFormInnerProductCore V u n)).symm.surjective.range_eq,
    Set.image_univ]
  exact Completion.denseRange_coe

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.FormCompletion
