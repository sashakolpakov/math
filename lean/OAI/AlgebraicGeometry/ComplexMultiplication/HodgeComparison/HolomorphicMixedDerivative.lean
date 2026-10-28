import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ClosedTwo

/-! # Holomorphic Mixed Derivative -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.HolomorphicMixedDerivative.CM.Construction

noncomputable section

/-! For a genuine one-form of type (1,0), the mixed exterior derivative
has precisely its antiholomorphic coefficient derivatives. -/

open Filter
open scoped _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

theorem holomorphicCovectorProjection_type10 (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E 1) (ha : Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E 1 0 a) (u : E) :
    ComplexCovector.CM.Construction.holomorphicCovectorProjection (HolomorphicMixedChartPair.CM.Construction.oneCovectorCLM a) u = a (fun _ => u) := by
  have hI : HolomorphicMixedChartPair.CM.Construction.oneCovectorCLM a (Complex.I • u) = Complex.I * HolomorphicMixedChartPair.CM.Construction.oneCovectorCLM a u :=
    (PureOneCovector.CM.Construction.holomorphicOneCovector a ha).map_smul Complex.I u
  rw [ComplexCovector.CM.Construction.holomorphicCovectorProjection_apply, hI]
  change (1 / 2 : ℂ) * (a (fun _ => u) - Complex.I * (Complex.I * a (fun _ => u))) = _
  rw [← mul_assoc, Complex.I_mul_I]
  ring

theorem antiholomorphicCovectorProjection_type10 (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E 1) (ha : Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E 1 0 a) (u : E) :
    Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E ℂ (HolomorphicMixedChartPair.CM.Construction.oneCovectorCLM a) u = 0 := by
  have hI : HolomorphicMixedChartPair.CM.Construction.oneCovectorCLM a (Complex.I • u) = Complex.I * HolomorphicMixedChartPair.CM.Construction.oneCovectorCLM a u :=
    (PureOneCovector.CM.Construction.holomorphicOneCovector a ha).map_smul Complex.I u
  rw [Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM_apply, hI]
  change (1 / 2 : ℂ) * (a (fun _ => u) + Complex.I * (Complex.I * a (fun _ => u))) = 0
  rw [← mul_assoc, Complex.I_mul_I]
  ring

theorem mixedTwoCoefficient_extDeriv_type10 (f : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E 1) {x : E}
    (hf : DifferentiableAt ℝ f x) (ht : ∀ᶠ y in 𝓝 x, Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E 1 0 (f y)) (u v : E) :
    MixedTwoCoefficient.CM.Construction.mixedTwoCoefficient (extDeriv f x) u v =
      AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative (fun y => f y (fun _ => v)) x u := by
  have hH : (fun y => ComplexCovector.CM.Construction.holomorphicCovectorProjection (HolomorphicMixedChartPair.CM.Construction.oneCovectorCLM (f y)) v) =ᶠ[𝓝 x]
      (fun y => f y (fun _ => v)) := by
    filter_upwards [ht] with y hy
    exact holomorphicCovectorProjection_type10 (f y) hy v
  have hA : (fun y => Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E ℂ (HolomorphicMixedChartPair.CM.Construction.oneCovectorCLM (f y)) u) =ᶠ[𝓝 x]
      (fun _ => (0 : ℂ)) := by
    filter_upwards [ht] with y hy
    exact antiholomorphicCovectorProjection_type10 (f y) hy u
  rw [ClosedTwo.CM.Construction.mixedTwoCoefficient_extDeriv f hf, AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative_congr hH,
    MetricCoefficientDivergence.CM.Construction.holomorphicDirectionalDerivative_congr hA]
  simp only [MetricDerivative.CM.Construction.holomorphicDirectionalDerivative, fderiv_const_apply, zero_apply, mul_zero, sub_zero]

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.HolomorphicMixedDerivative.CM.Construction
