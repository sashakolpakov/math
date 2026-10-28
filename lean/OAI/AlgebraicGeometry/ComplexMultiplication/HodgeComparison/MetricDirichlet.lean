import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Metric
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EllipticExtension
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.GradientSupport

/-! # Metric Dirichlet -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.MetricDirichlet.CM.Construction

noncomputable section

/-! Weak Dirichlet solvability for the actual projective metric coefficients. -/

open _root_.MeasureTheory Set
open scoped ContDiff _root_.Manifold

variable {ι : Type*} [Fintype ι]

def varietyComplexDirichletOperator (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V)) (z : EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    EuclideanSpace ℂ ι →L[ℝ] EuclideanSpace ℂ ι :=
  InverseMetric.CM.Construction.realBilinearOperator (Metric.CM.Construction.complexGradientMetric b (Metric.CM.Construction.varietyDirichletCoefficient V e z))

theorem varietyComplexDirichletOperator_smooth (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V)) :
    ContDiffOn ℝ ∞ (varietyComplexDirichletOperator V e b)
      (EuclideanMetric.CM.Construction.varietyEuclideanDomain V e : Set (EuclideanMetric.CM.Construction.varietyEuclideanModel V)) := by
  have hC := (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := (∞ : ℕ∞ω))
    (E := EuclideanMetric.CM.Construction.varietyEuclideanModel V →L[ℝ] EuclideanMetric.CM.Construction.varietyEuclideanModel V →L[ℝ] ℝ)
    (F := EuclideanSpace ℂ ι →L[ℝ] EuclideanSpace ℂ ι →L[ℝ] ℝ)
    (Metric.CM.Construction.complexGradientMetric b)).comp_contDiffOn (Metric.CM.Construction.varietyDirichletCoefficient_smooth V e he)
  exact (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := (∞ : ℕ∞ω))
    (E := EuclideanSpace ℂ ι →L[ℝ] EuclideanSpace ℂ ι →L[ℝ] ℝ)
    (F := EuclideanSpace ℂ ι →L[ℝ] EuclideanSpace ℂ ι)
    (InverseMetric.CM.Construction.realBilinearOperator (E := EuclideanSpace ℂ ι))).comp_contDiffOn hC

def varietyMetricDirichletOperator (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V)) (K : Set (EuclideanMetric.CM.Construction.varietyEuclideanModel V)) :
    EuclideanMetric.CM.Construction.varietyEuclideanModel V → EuclideanSpace ℂ ι →L[ℝ] EuclideanSpace ℂ ι :=
  EllipticExtension.CM.Construction.ellipticFieldExtension K (varietyComplexDirichletOperator V e b)

/-- On the Dirichlet domain, the operator is precisely the positive metric
coefficient applied to the real and imaginary parts of the complex gradient. -/
theorem varietyMetricDirichletOperator_apply (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V)) (K : Set (EuclideanMetric.CM.Construction.varietyEuclideanModel V))
    {z : EuclideanMetric.CM.Construction.varietyEuclideanModel V} (hz : z ∈ K) (u v : EuclideanSpace ℂ ι) :
    inner ℝ (varietyMetricDirichletOperator V e b K z u) v =
      Metric.CM.Construction.varietyDirichletCoefficient V e z
        (Metric.CM.Construction.complexGradientComponent b Complex.reCLM u) (Metric.CM.Construction.complexGradientComponent b Complex.reCLM v) +
      Metric.CM.Construction.varietyDirichletCoefficient V e z
        (Metric.CM.Construction.complexGradientComponent b Complex.imCLM u) (Metric.CM.Construction.complexGradientComponent b Complex.imCLM v) := by
  rw [varietyMetricDirichletOperator, EllipticExtension.CM.Construction.ellipticFieldExtension_of_mem K _ hz,
    varietyComplexDirichletOperator, InverseMetric.CM.Construction.realBilinearOperator_apply, Metric.CM.Construction.complexGradientMetric_apply]

/-- The actual projective metric gives a unique weak Dirichlet solution on
every compact coordinate domain of positive ambient dimension. -/
theorem variety_metric_dirichlet_weak_existsUnique (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    [Nontrivial (EuclideanMetric.CM.Construction.varietyEuclideanModel V)]
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V))
    {K : Set (EuclideanMetric.CM.Construction.varietyEuclideanModel V)} (hK : IsCompact K) (hKU : K ⊆ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
    (ℓ : SobolevIs.CM.Construction.supportedH1Coordinates K →L[ℝ] ℝ) :
    ∃! u : SobolevIs.CM.Construction.supportedH1Coordinates K, ∀ v : SobolevIs.CM.Construction.supportedH1Coordinates K,
      (∫ z, inner ℝ (varietyMetricDirichletOperator V e b K z (GradientSupport.CM.Construction.supportedH1VectorGradient b K u z))
        (GradientSupport.CM.Construction.supportedH1VectorGradient b K v z)) = ℓ v := by
  let A := varietyComplexDirichletOperator V e b
  have hcont : ContinuousOn A K :=
    (varietyComplexDirichletOperator_smooth V e he b).continuousOn.mono hKU
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont
  obtain ⟨a, ha, hpos⟩ := Metric.CM.Construction.varietyDirichletCoefficient_uniform_lower_bound V e he hK hKU
  have hposA : ∀ z ∈ K, ∀ w : EuclideanSpace ℂ ι, a * ‖w‖ * ‖w‖ ≤ inner ℝ (A z w) w := by
    intro z hz w
    change _ ≤ inner ℝ (InverseMetric.CM.Construction.realBilinearOperator (Metric.CM.Construction.complexGradientMetric b (Metric.CM.Construction.varietyDirichletCoefficient V e z)) w) w
    rw [InverseMetric.CM.Construction.realBilinearOperator_apply]
    exact Metric.CM.Construction.complexGradientMetric_lower_bound b _ (hpos z hz) w
  exact GradientSupport.CM.Construction.variable_dirichlet_weak_existsUnique b hK (EllipticExtension.CM.Construction.ellipticFieldExtension K A)
    (EllipticExtension.CM.Construction.ellipticFieldExtension_aestronglyMeasurable K A hK.measurableSet hcont volume)
    (Filter.Eventually.of_forall (EllipticExtension.CM.Construction.ellipticFieldExtension_bound K A hC))
    (lt_min ha zero_lt_one)
    (Filter.Eventually.of_forall (EllipticExtension.CM.Construction.ellipticFieldExtension_lower_bound K A hposA)) ℓ

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.MetricDirichlet.CM.Construction
