import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.CoefficientDerivative
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.DerivativeBound

/-! # Coefficient Energy Bound -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.CoefficientEnergyBound

noncomputable section

/-! The literal exterior coefficients and their first derivatives are bounded by the original native joint energy norm. -/

open _root_.TopologicalSpace _root_.MeasureTheory
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] EnergyContinuousExt.smoothCore_fullNormedSpace EnergyContinuousExt.smoothCore_fullInnerProductSpace
  EnergyContinuousExt.smoothCore_normedSpace EnergyContinuousExt.smoothCore_innerProductSpace

def HolomorphicFrameCoefficientEnergyBound (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
 : Prop :=
  ∀ (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (_ : e ∈ atlas V.analyticModel V.analyticSpace)
    (i : V.analyticSpace)
    (f : V.analyticSpace → ℂ) (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f)
    (hs : tsupport f ⊆ (Analysis.DifferentialForms.Manifold.ChartEquiv.chartSourceOpen e ⊓ CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i : Opens V.analyticSpace)),
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ ∀ (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1),
      (∫ z, ‖HolomorphicFrame.CoordinatesLp.holomorphicLineFrameCoefficientLinear V e i 1 f hf hs a.val z‖ ^ 2) ≤
        C * ‖EnergyContinuousExt.holomorphicMetricSmoothEnergyInclusion V h a‖ ^ 2 ∧
      ∀ v : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, ‖v‖ = 1 →
        (∫ z, ‖fderiv ℝ (HolomorphicFrame.CoordinatesLp.holomorphicLineFrameCoefficientLinear V e i 1 f hf hs a.val) z v‖ ^ 2) ≤
          D * ‖EnergyContinuousExt.holomorphicMetricSmoothEnergyInclusion V h a‖ ^ 2

theorem holomorphicMetricFrameCoefficient_energy_bound (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
 :
    HolomorphicFrameCoefficientEnergyBound V h := by
  intro e he i f hf hs
  have HN := DerivativeBound.holomorphicMetricCompactField_energy_bound V h e he i f hf hs
  let N := HN.choose
  have hN := HN.choose_spec.1
  have hn := HN.choose_spec.2
  have HD := DerivativeBound.holomorphicMetricCompactDerivative_energy_bound V h e he i f hf hs
  let D := HD.choose
  have hD := HD.choose_spec.1
  have hd := HD.choose_spec.2
  let L := (Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis 1).toContinuousLinearMap.restrictScalars ℝ
  refine ⟨‖L‖ ^ 2 * N, ‖L‖ ^ 2 * D, mul_nonneg (sq_nonneg _) hN.le, mul_nonneg (sq_nonneg _) hD.le, fun a => ?_⟩
  constructor
  · exact (CoefficientDerivative.holomorphicLineFrameCoefficient_norm_integral_le V e he i 1 f hf hs a.val).trans
      ((mul_le_mul_of_nonneg_left (hn a) (sq_nonneg ‖L‖)).trans_eq (mul_assoc _ _ _).symm)
  · intro v hv
    exact (CoefficientDerivative.holomorphicLineFrameCoefficient_derivative_integral_le V e he i 1 f hf hs a.val v).trans
      ((mul_le_mul_of_nonneg_left (hd a v hv) (sq_nonneg ‖L‖)).trans_eq (mul_assoc _ _ _).symm)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.CoefficientEnergyBound
