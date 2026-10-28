import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicSmooth.DolbeaultBound
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.WeightedNorm

/-! # Dolbeault Integral Bound -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.DolbeaultIntegralBound

noncomputable section

/-! The actual smooth Dolbeault primitive estimate as an exact weighted integral for original bundle forms. -/

open _root_.MeasureTheory
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)

theorem holomorphicMetric_primitive_integral_bound
    (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1) (b : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 0)
    (hb : ‖IntegralPairZero.holomorphicFormL2WithInclusion V h 0 b.val‖ ≤ ‖AntiOneSourcePair.holomorphicMetricAntiOneInclusion V h a‖) :
    (h.formIntegralPair V 0 b.val b.val).re ≤ (h.formIntegralPair V 1 a.val a.val).re :=
  le_of_eq_of_le (IntegralPairZero.holomorphicFormL2WithInclusion_norm_sq V h 0 b.val).symm
    (le_of_le_of_eq ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hb)
      (HolomorphicSmooth.EnergyCoercivity.holomorphicMetricAntiOneInclusion_norm_sq V h a))

theorem holomorphicMetricSmoothDolbeault_solve_weighted (f : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 0)
    (hc : (h.withPotential f).smoothDolbeaultOneCoercive V) (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1)
    (ha : HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 a = 0) :
    ∃ b : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 0, HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 0 b = a ∧
      (∫ x, Real.exp (ScalarPotentialFunctions.realPotentialScalar f x) * (h.globalFormPair V 0 b.val b.val x).re ∂(ComplexMultiplication.HodgeComparison.GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V)) ≤
        ∫ x, Real.exp (ScalarPotentialFunctions.realPotentialScalar f x) * (h.globalFormPair V 1 a.val a.val x).re ∂(ComplexMultiplication.HodgeComparison.GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V) := by
  let result := HolomorphicSmooth.DolbeaultBound.holomorphicMetricSmoothDolbeault_solve_bound V (h.withPotential f) hc a ha
  refine ⟨result.choose, result.choose_spec.1, ?_⟩
  have hb := holomorphicMetric_primitive_integral_bound V (h.withPotential f) a result.choose result.choose_spec.2
  exact le_of_eq_of_le (h.rescale_formIntegralPair_re V _ _ _ 0 result.choose.val result.choose.val).symm
    (le_of_le_of_eq hb (h.rescale_formIntegralPair_re V _ _ _ 1 a.val a.val))

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.DolbeaultIntegralBound
