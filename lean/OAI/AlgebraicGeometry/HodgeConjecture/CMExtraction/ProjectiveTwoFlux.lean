import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.TwoChart
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.TwoDensity
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.AntiholomorphicIntegration

/-! # Projective Two Flux -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ProjectiveTwoFlux.Closedness

noncomputable section

/-! The actual projective metric flux of a closed (2,0) form has zero divergence. -/

open OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.AntiholomorphicIntegration.CM.Construction
open scoped ContDiff _root_.Topology ComplexOrder

def varietyHolomorphicTwoMatrix (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 2) (z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    Matrix (Fin V.complexDimension) (Fin V.complexDimension) ℂ :=
  Matrix.of fun i j => TwoChart.Closedness.varietyHolomorphicTwoCoefficient V e a i j z

def varietyHolomorphicTwoFlux (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 2) (j d : Fin V.complexDimension) :
    ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℂ :=
  TwoDensity.Closedness.holomorphicTwoFlux (fun z => (ComplexMultiplication.HodgeComparison.Metric.CM.Construction.varietyMetricDensity V e z : ℂ))
    (ComplexMultiplication.HodgeComparison.AntiholomorphicIntegration.CM.Construction.varietyInverseHermitianMatrix V e) (varietyHolomorphicTwoMatrix V e a) j d

theorem varietyHolomorphicTwoFlux_smooth (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 2) (j d : Fin V.complexDimension) :
    ContDiffOn ℝ ∞ (varietyHolomorphicTwoFlux V e a j d) (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e : Set _) := by
  unfold varietyHolomorphicTwoFlux TwoDensity.Closedness.holomorphicTwoFlux
  apply ContDiffOn.sum
  intro r _
  apply ContDiffOn.sum
  intro k _
  exact (((Complex.ofRealCLM.contDiff.comp_contDiffOn (ComplexMultiplication.HodgeComparison.Metric.CM.Construction.varietyMetricDensity_smooth V e he)).mul
    (ComplexMultiplication.HodgeComparison.AntiholomorphicIntegration.CM.Construction.varietyInverseHermitianMatrix_smooth V e he r d)).mul
      (ComplexMultiplication.HodgeComparison.AntiholomorphicIntegration.CM.Construction.varietyInverseHermitianMatrix_smooth V e he k j)).mul
        (TwoChart.Closedness.varietyHolomorphicTwoCoefficient_smooth V e he a r k)

theorem variety_closed_type20_flux_divergence (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 2)
    (ha : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree V.analyticModel V.analyticSpace 2 0 a.val)
    (hc : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a = 0)
    {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V} (hz : z ∈ ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) (j : Fin V.complexDimension) :
    (∑ d, ComplexMultiplication.HodgeComparison.AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative (varietyHolomorphicTwoFlux V e a j d) z
      (EuclideanSpace.basisFun (Fin V.complexDimension) ℂ d)) = 0 := by
  let P := ComplexMultiplication.HodgeComparison.AntiholomorphicIntegration.CM.Construction.varietyInverseHermitianMatrix V e
  let S := varietyHolomorphicTwoMatrix V e a
  let ρ := fun y => (ComplexMultiplication.HodgeComparison.Metric.CM.Construction.varietyMetricDensity V e y : ℂ)
  have hρ : DifferentiableAt ℝ ρ z :=
    ((Complex.ofRealCLM.contDiff.comp_contDiffOn (ComplexMultiplication.HodgeComparison.Metric.CM.Construction.varietyMetricDensity_smooth V e he)).contDiffAt
      ((ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen.mem_nhds hz)).differentiableAt (by simp)
  have hP (r k : Fin V.complexDimension) : DifferentiableAt ℝ (fun y => P y r k) z :=
    ((ComplexMultiplication.HodgeComparison.AntiholomorphicIntegration.CM.Construction.varietyInverseHermitianMatrix_smooth V e he r k).contDiffAt
      ((ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen.mem_nhds hz)).differentiableAt (by simp)
  have hS (r k : Fin V.complexDimension) : DifferentiableAt ℝ (fun y => S y r k) z :=
    ((TwoChart.Closedness.varietyHolomorphicTwoCoefficient_smooth V e he a r k).contDiffAt
      ((ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen.mem_nhds hz)).differentiableAt (by simp)
  exact TwoDensity.Closedness.holomorphicTwoFlux_divergence_zero ρ P S hρ hP hS
    (EuclideanSpace.basisFun (Fin V.complexDimension) ℂ)
    (ComplexMultiplication.HodgeComparison.AntiholomorphicDivergence.CM.Construction.varietyEuclideanMetric_weighted_inverse_antiholomorphic_divergence V e he hz)
    (ComplexMultiplication.HodgeComparison.ProjectiveInverseTransport.CM.Construction.varietyEuclideanInverse_antiholomorphic_transport V e he hz)
    (fun r k => HolomorphicTwoCoefficient.Closedness.holomorphicTwoCoefficient_skew _ _ _)
    (TwoChart.Closedness.variety_closed_type20_antiholomorphic_derivative V e he a ha hc hz) j

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ProjectiveTwoFlux.Closedness
