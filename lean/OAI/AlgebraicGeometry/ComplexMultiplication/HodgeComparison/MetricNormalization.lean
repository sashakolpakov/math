import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.MetricDirichlet
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.GlobalMetricCoefficient

/-! # Metric Normalization -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.MetricNormalization.CM.Construction

noncomputable section

/-! Explicit volume and complex-gradient normalization in the actual metric
energy, needed to compare the global and Euclidean weak equations. -/

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fintype ι]

theorem complexGradientComponent_re_smul (b : OrthonormalBasis ι ℝ E)
    (c : ℂ) (z : EuclideanSpace ℂ ι) :
    Metric.CM.Construction.complexGradientComponent b Complex.reCLM (c • z) =
      c.re • Metric.CM.Construction.complexGradientComponent b Complex.reCLM z -
        c.im • Metric.CM.Construction.complexGradientComponent b Complex.imCLM z := by
  simp only [Metric.CM.Construction.complexGradientComponent_apply, Finset.smul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  change (c * z i).re • b i = c.re • ((z i).re • b i) - c.im • ((z i).im • b i)
  rw [Complex.mul_re, sub_smul, smul_smul, smul_smul]

theorem complexGradientComponent_im_smul (b : OrthonormalBasis ι ℝ E)
    (c : ℂ) (z : EuclideanSpace ℂ ι) :
    Metric.CM.Construction.complexGradientComponent b Complex.imCLM (c • z) =
      c.re • Metric.CM.Construction.complexGradientComponent b Complex.imCLM z +
        c.im • Metric.CM.Construction.complexGradientComponent b Complex.reCLM z := by
  simp only [Metric.CM.Construction.complexGradientComponent_apply, Finset.smul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  change (c * z i).im • b i = c.re • ((z i).im • b i) + c.im • ((z i).re • b i)
  rw [Complex.mul_im, add_smul, smul_smul, smul_smul]

theorem complexGradientMetric_smul_both (b : OrthonormalBasis ι ℝ E)
    (B : E →L[ℝ] E →L[ℝ] ℝ) (c : ℂ) (z w : EuclideanSpace ℂ ι) :
    Metric.CM.Construction.complexGradientMetric b B (c • z) (c • w) = ‖c‖ ^ 2 * Metric.CM.Construction.complexGradientMetric b B z w := by
  simp only [Metric.CM.Construction.complexGradientMetric_apply, complexGradientComponent_re_smul,
    complexGradientComponent_im_smul, map_add, map_sub, map_smul, add_apply,
    sub_apply, smul_apply, smul_eq_mul]
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  ring

theorem varietyComplexDirichletOperator_density (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V)) (z : EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    MetricDirichlet.CM.Construction.varietyComplexDirichletOperator V e b z =
      Metric.CM.Construction.varietyMetricDensity V e z • GlobalMetricCoefficient.CM.Construction.varietyInverseMetricOperator V e b z := by
  unfold MetricDirichlet.CM.Construction.varietyComplexDirichletOperator Metric.CM.Construction.varietyDirichletCoefficient GlobalMetricCoefficient.CM.Construction.varietyInverseMetricOperator
  rw [map_smul, map_smul]

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.MetricNormalization.CM.Construction
