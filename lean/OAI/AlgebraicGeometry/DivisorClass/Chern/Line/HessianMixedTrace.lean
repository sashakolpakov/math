import OAI.AlgebraicGeometry.DivisorClass.Chern.Line.HessianBilinear
import OAI.AlgebraicGeometry.DivisorClass.Chern.BilinearComplexTrace

/-! # Hessian Mixed Trace -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Line.HessianMixedTrace

noncomputable section

/-! The complex mixed Hessian trace is exactly half the curvature commutator trace. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {E ι : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Fintype ι] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

theorem lineCovectorHessian_mixed_trace (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E →L[ℝ] E →L[ℝ] ℝ) (hB : ∀ v w, B v w = B w v)
    (hpos : ∀ v : E, v ≠ 0 → 0 < B v v)
    (hBJ : ∀ v w, B (Complex.I • v) w = -B v (Complex.I • w))
    (G : E → E →L[ℝ] E →L[ℝ] E) (A : E → E →L[ℝ] ℂ) (a : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E n)
    {x : E} (ha : DifferentiableAt ℝ (ConnectionSymbols.lineCovectorConnectionDerivative n G A a) x) (t : Fin n → E) :
    (∑ j, CovectorHessian.lineCovectorHessian n G A a x (b j) (Complex.I • Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp B (b.coord j).toContinuousLinearMap) t) =
      (1 / 2 : ℂ) * ∑ j,
        (CovectorHessian.lineCovectorHessian n G A a x (b j) (Complex.I • Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp B (b.coord j).toContinuousLinearMap) -
          CovectorHessian.lineCovectorHessian n G A a x (Complex.I • Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp B (b.coord j).toContinuousLinearMap) (b j)) t := by
  have hh := BilinearComplexTrace.bilinearMetric_complex_trace_J_skew B hB hpos hBJ b
    (HessianBilinear.lineCovectorTensorScalarBilinear n G A (ConnectionSymbols.lineCovectorConnectionDerivative n G A a) x t)
  simp only [← HessianBilinear.lineCovectorHessian_scalar_bilinear n G A a ha] at hh
  simp only [ContinuousAlternatingMap.sub_apply, Finset.sum_sub_distrib]
  rw [hh]
  ring

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Line.HessianMixedTrace
