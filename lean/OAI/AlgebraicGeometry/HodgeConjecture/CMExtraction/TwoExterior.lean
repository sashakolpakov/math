import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.TwoChart
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.HolomorphicExteriorTrace

/-! # Two Exterior -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.TwoExterior.Closedness

noncomputable section

/-! Holomorphic coefficients of the actual exterior derivative of a (1,0) form. -/

open OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.HolomorphicExteriorTrace.CM.Construction Filter
open scoped ContDiff _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

theorem holomorphicTwoCoefficient_extDeriv (f : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E 1) {x : E}
    (hf : DifferentiableAt ℝ f x) (u v : E) :
    HolomorphicTwoCoefficient.Closedness.holomorphicTwoCoefficient (extDeriv f x) u v =
      ComplexMultiplication.HodgeComparison.MetricDerivative.CM.Construction.holomorphicDirectionalDerivative
        (fun y => ComplexMultiplication.HodgeComparison.ComplexCovector.CM.Construction.holomorphicCovectorProjection (ComplexMultiplication.HodgeComparison.HolomorphicMixedChartPair.CM.Construction.oneCovectorCLM (f y)) v) x u -
      ComplexMultiplication.HodgeComparison.MetricDerivative.CM.Construction.holomorphicDirectionalDerivative
        (fun y => ComplexMultiplication.HodgeComparison.ComplexCovector.CM.Construction.holomorphicCovectorProjection (ComplexMultiplication.HodgeComparison.HolomorphicMixedChartPair.CM.Construction.oneCovectorCLM (f y)) u) x v := by
  rw [HolomorphicTwoCoefficient.Closedness.holomorphicTwoCoefficient_apply]
  simp only [ComplexMultiplication.HodgeComparison.ClosedTwo.CM.Construction.oneForm_extDeriv_apply f hf]
  rw [ComplexMultiplication.HodgeComparison.MetricDerivative.CM.Construction.holomorphicDirectionalDerivative, ComplexMultiplication.HodgeComparison.MetricDerivative.CM.Construction.holomorphicDirectionalDerivative,
    ComplexMultiplication.HodgeComparison.ClosedOneMixedDerivatives.CM.Construction.holomorphic_projection_coefficient_derivative f hf,
    ComplexMultiplication.HodgeComparison.ClosedOneMixedDerivatives.CM.Construction.holomorphic_projection_coefficient_derivative f hf,
    ComplexMultiplication.HodgeComparison.ClosedOneMixedDerivatives.CM.Construction.holomorphic_projection_coefficient_derivative f hf,
    ComplexMultiplication.HodgeComparison.ClosedOneMixedDerivatives.CM.Construction.holomorphic_projection_coefficient_derivative f hf]
  ring_nf
  simp only [Complex.I_sq]
  ring

theorem holomorphicTwoCoefficient_extDeriv_type10 (f : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E 1) {x : E}
    (hf : DifferentiableAt ℝ f x) (ht : ∀ᶠ y in 𝓝 x, Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E 1 0 (f y)) (u v : E) :
    HolomorphicTwoCoefficient.Closedness.holomorphicTwoCoefficient (extDeriv f x) u v =
      ComplexMultiplication.HodgeComparison.MetricDerivative.CM.Construction.holomorphicDirectionalDerivative (fun y => f y (fun _ => v)) x u -
        ComplexMultiplication.HodgeComparison.MetricDerivative.CM.Construction.holomorphicDirectionalDerivative (fun y => f y (fun _ => u)) x v := by
  have hH (w : E) : (fun y => ComplexMultiplication.HodgeComparison.ComplexCovector.CM.Construction.holomorphicCovectorProjection (ComplexMultiplication.HodgeComparison.HolomorphicMixedChartPair.CM.Construction.oneCovectorCLM (f y)) w) =ᶠ[𝓝 x]
      (fun y => f y (fun _ => w)) := by
    filter_upwards [ht] with y hy
    exact ComplexMultiplication.HodgeComparison.HolomorphicMixedDerivative.CM.Construction.holomorphicCovectorProjection_type10 (f y) hy w
  rw [holomorphicTwoCoefficient_extDeriv f hf, ComplexMultiplication.HodgeComparison.MetricCoefficientDivergence.CM.Construction.holomorphicDirectionalDerivative_congr (hH v),
    ComplexMultiplication.HodgeComparison.MetricCoefficientDivergence.CM.Construction.holomorphicDirectionalDerivative_congr (hH u)]

theorem variety_type10_exterior_holomorphic_coefficient (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 1)
    (ha : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree V.analyticModel V.analyticSpace 1 0 a.val)
    {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V} (hz : z ∈ ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
    (i j : Fin V.complexDimension) :
    TwoChart.Closedness.varietyHolomorphicTwoCoefficient V e (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a) i j z =
      ComplexMultiplication.HodgeComparison.MetricDerivative.CM.Construction.holomorphicDirectionalDerivative (ComplexMultiplication.HodgeComparison.HolomorphicAdjointFlux.CM.Construction.varietyOneFormComplexCoefficient V e a j) z
        (EuclideanSpace.basisFun (Fin V.complexDimension) ℂ i) -
      ComplexMultiplication.HodgeComparison.MetricDerivative.CM.Construction.holomorphicDirectionalDerivative (ComplexMultiplication.HodgeComparison.HolomorphicAdjointFlux.CM.Construction.varietyOneFormComplexCoefficient V e a i) z
        (EuclideanSpace.basisFun (Fin V.complexDimension) ℂ j) := by
  let f := Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1 a.val
  have hf : DifferentiableAt ℝ f z :=
    ((Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm_smooth V e he 1 a).contDiffAt
      ((ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen.mem_nhds hz)).differentiableAt (by simp)
  have ht : ∀ᶠ y in 𝓝 z, Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) 1 0 (f y) := by
    filter_upwards [(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen.mem_nhds hz] with y hy
    intro c v
    change a.val.inChart e (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V y)
      (fun l => ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V ((c : ℂ) • v l)) =
      Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter 1 0 c * a.val.inChart e (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V y)
        (fun l => ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V (v l))
    simp only [map_smul]
    exact ha e he _ hy c _
  rw [TwoChart.Closedness.varietyHolomorphicTwoCoefficient_eq_euclidean,
    Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm_d V e he 1 a z hz,
    holomorphicTwoCoefficient_extDeriv_type10 f hf ht]
  rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.TwoExterior.Closedness
