import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.MetricDirichlet
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.GradientSupport

/-! # Local Metric Equation -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.LocalMetricEquation.CM.Construction

noncomputable section

/-! The projective metric's weak equation expressed solely on its coordinate domain. -/

open _root_.MeasureTheory Set
open scoped _root_.Manifold

variable {ι : Type*} [Fintype ι]

def varietyLocalDirichletEnergy (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V)) (K : Set (EuclideanMetric.CM.Construction.varietyEuclideanModel V))
    (u v : SobolevIs.CM.Construction.supportedH1Coordinates K) : ℝ :=
  ∫ z in K, Metric.CM.Construction.complexGradientMetric b (Metric.CM.Construction.varietyDirichletCoefficient V e z)
    (GradientSupport.CM.Construction.supportedH1VectorGradient b K u z) (GradientSupport.CM.Construction.supportedH1VectorGradient b K v z)

theorem varietyLocalDirichletEnergy_eq_extended (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V))
    {K : Set (EuclideanMetric.CM.Construction.varietyEuclideanModel V)} (hK : IsClosed K) (u v : SobolevIs.CM.Construction.supportedH1Coordinates K) :
    varietyLocalDirichletEnergy V e b K u v =
      ∫ z, inner ℝ (MetricDirichlet.CM.Construction.varietyMetricDirichletOperator V e b K z (GradientSupport.CM.Construction.supportedH1VectorGradient b K u z))
        (GradientSupport.CM.Construction.supportedH1VectorGradient b K v z) := by
  have hout : ∀ᵐ z ∂(volume : Measure (EuclideanMetric.CM.Construction.varietyEuclideanModel V)), z ∉ K →
      inner ℝ (MetricDirichlet.CM.Construction.varietyMetricDirichletOperator V e b K z (GradientSupport.CM.Construction.supportedH1VectorGradient b K u z))
        (GradientSupport.CM.Construction.supportedH1VectorGradient b K v z) = 0 := by
    filter_upwards [GradientSupport.CM.Construction.supportedH1VectorGradient_support b hK u] with z hz hzK
    rw [hz hzK, map_zero, inner_zero_left]
  rw [← setIntegral_eq_integral_of_ae_compl_eq_zero hout]
  apply setIntegral_congr_fun hK.measurableSet
  intro z hz
  dsimp only
  rw [MetricDirichlet.CM.Construction.varietyMetricDirichletOperator, EllipticExtension.CM.Construction.ellipticFieldExtension_of_mem K _ hz,
    MetricDirichlet.CM.Construction.varietyComplexDirichletOperator, InverseMetric.CM.Construction.realBilinearOperator_apply]

/-- Every bounded functional on the actual supported H1 completion is
represented uniquely by the metric Dirichlet energy over the compact domain. -/
theorem variety_local_dirichlet_weak_existsUnique (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    [Nontrivial (EuclideanMetric.CM.Construction.varietyEuclideanModel V)]
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V))
    {K : Set (EuclideanMetric.CM.Construction.varietyEuclideanModel V)} (hK : IsCompact K) (hKU : K ⊆ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
    (ℓ : SobolevIs.CM.Construction.supportedH1Coordinates K →L[ℝ] ℝ) :
    ∃! u : SobolevIs.CM.Construction.supportedH1Coordinates K, ∀ v : SobolevIs.CM.Construction.supportedH1Coordinates K,
      varietyLocalDirichletEnergy V e b K u v = ℓ v := by
  obtain ⟨u, hu, huniq⟩ := MetricDirichlet.CM.Construction.variety_metric_dirichlet_weak_existsUnique V e he b hK hKU ℓ
  refine ⟨u, fun v => ?_, fun w hw => huniq w (fun v => ?_)⟩
  · exact (varietyLocalDirichletEnergy_eq_extended V e b hK.isClosed u v).trans (hu v)
  · exact (varietyLocalDirichletEnergy_eq_extended V e b hK.isClosed w v).symm.trans (hw v)

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.LocalMetricEquation.CM.Construction
