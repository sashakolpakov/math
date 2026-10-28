import OAI.AlgebraicGeometry.DivisorClass.Chern.OneCovectorAntiPair
import OAI.AlgebraicGeometry.DivisorClass.Chern.Line.RoughDivergence
import OAI.AlgebraicGeometry.DivisorClass.Chern.Line.CovectorTypes

/-! # Anti Test Energy -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Line.AntiTestEnergy

noncomputable section

/-! The actual real energy pairing of an antiholomorphic field is unchanged by projection of an arbitrary smooth test. -/

open Filter
open scoped _root_.Topology ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] HessianBilinear.tensorConnection_formNormed HessianBilinear.tensorConnection_formSpace
  HessianBilinear.tensorConnection_oneNormed HessianBilinear.tensorConnection_oneSpace

variable {E ι : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [Fintype ι] [LinearOrder ι]

theorem covectorTensorMetricPair_anti_projection_re (b : Module.Basis ι ℝ E)
    (B : E →L[ℝ] E →L[ℝ] ℝ) (hB : ∀ v w, B v w = B w v)
    (hpos : ∀ v : E, v ≠ 0 → 0 < B v v)
    (hBJ : ∀ v w, B (Complex.I • v) w = -B v (Complex.I • w))
    (N P : E →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E 1) (hN : ∀ v, Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E 0 1 (N v)) :
    (CovectorTensorAlgebra.covectorTensorMetricPair b 1 B N (OneCovectorAntiProjection.oneCovectorAntiProjection.comp P)).re =
      (CovectorTensorAlgebra.covectorTensorMetricPair b 1 B N P).re := by
  simp only [CovectorTensorAlgebra.covectorTensorMetricPair, Complex.re_sum, ContinuousLinearMap.comp_apply]
  exact Finset.sum_congr rfl (fun i _ => OneCovectorAntiPair.bilinearFormMetricPair_anti_projection_re b B hB hpos hBJ _ _ (hN _))

theorem lineCovectorFullEnergyPair_anti_test_re (b : Module.Basis ι ℝ E)
    (B : E → E →L[ℝ] E →L[ℝ] ℝ) (G : E → E →L[ℝ] E →L[ℝ] E) (A : E → E →L[ℝ] ℂ)
    (w : E → ℂ) (a c : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E 1) {x : E}
    (ha : DifferentiableAt ℝ a x) (hc : DifferentiableAt ℝ c x)
    (hpure : ∀ᶠ y in 𝓝 x, Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E 0 1 (a y))
    (hG : ∀ v t, G x v (Complex.I • t) = Complex.I • G x v t)
    (hB : ∀ v t, B x v t = B x t v)
    (hpos : ∀ v : E, v ≠ 0 → 0 < B x v v)
    (hBJ : ∀ v t, B x (Complex.I • v) t = -B x v (Complex.I • t))
    (hw : w x = Complex.ofReal (w x).re) :
    (RoughDivergence.lineCovectorFullEnergyPair b 1 B G A w a (fun y => OneCovectorAntiProjection.oneCovectorAntiProjection (c y)) x).re =
      (RoughDivergence.lineCovectorFullEnergyPair b 1 B G A w a c x).re := by
  have hD : ConnectionSymbols.lineCovectorConnectionDerivative 1 G A (fun y => OneCovectorAntiProjection.oneCovectorAntiProjection (c y)) x =
      OneCovectorAntiProjection.oneCovectorAntiProjection.comp (ConnectionSymbols.lineCovectorConnectionDerivative 1 G A c x) := by
    apply ContinuousLinearMap.ext
    intro v
    exact OneCovectorAntiProjection.oneCovectorAntiProjection_covariant_derivative G A c hc hG v
  have hN (v : E) : Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E 0 1 (ConnectionSymbols.lineCovectorConnectionDerivative 1 G A a x v) :=
    CovectorTypes.lineCovectorConnectionDerivative_pure 0 1 G A a x ha hpure hG v
  have hp := covectorTensorMetricPair_anti_projection_re b (B x) hB hpos hBJ
    (ConnectionSymbols.lineCovectorConnectionDerivative 1 G A a x) (ConnectionSymbols.lineCovectorConnectionDerivative 1 G A c x) hN
  unfold RoughDivergence.lineCovectorFullEnergyPair
  rw [hD, hw]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, zero_mul, add_zero, sub_zero]
  exact congrArg (fun r : ℝ => ComplexMultiplication.HodgeComparison.Metric.CM.Construction.metricDensity b (B x) * (w x).re * r) hp

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Line.AntiTestEnergy
