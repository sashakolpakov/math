import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SmoothCoefficientExtension
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.MetricDirichlet

/-! # Smooth Metric Localization -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SmoothMetricLocalization.CM.Construction

noncomputable section

/-! Every projective coordinate point admits a smooth, uniformly positive,
bounded Lipschitz extension of its actual Dirichlet coefficients. -/

open Set _root_.Metric
open scoped ContDiff _root_.Topology _root_.Manifold

theorem exists_smooth_local_cutoff {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {U : Set E} (hU : IsOpen U) {z : E} (hz : z ∈ U) :
    ∃ η : E → ℝ, ContDiff ℝ ∞ η ∧ HasCompactSupport η ∧ tsupport η ⊆ U ∧
      (∀ x, 0 ≤ η x) ∧ (∀ x, η x ≤ 1) ∧ η =ᶠ[𝓝 z] 1 := by
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp hU z hz
  let η : ContDiffBump z :=
    { rIn := r / 4
      rOut := r / 2
      rIn_pos := by positivity
      rIn_lt_rOut := by linarith }
  refine ⟨η, η.contDiff, η.hasCompactSupport, ?_, η.nonneg', (fun _ => η.le_one),
    η.eventuallyEq_one⟩
  rw [η.tsupport_eq]
  apply Subset.trans ?_ hrU
  exact closedBall_subset_ball (by dsimp [η]; linarith)

variable {ι : Type*} [Fintype ι]

theorem variety_smooth_metric_extension (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V))
    (η : EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℝ) (hη : ContDiff ℝ ∞ η)
    (hηc : HasCompactSupport η) (hηU : tsupport η ⊆ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
    (hη₀ : ∀ x, 0 ≤ η x) (hη₁ : ∀ x, η x ≤ 1) :
    let A := SmoothCoefficientExtension.CM.Construction.smoothCoefficientExtension η (MetricDirichlet.CM.Construction.varietyComplexDirichletOperator V e b)
    ContDiff ℝ ∞ A ∧
      (∃ C : ℝ, ∀ x, ‖A x‖ ≤ C) ∧ (∃ L : NNReal, LipschitzWith L A) ∧
      ∃ a : ℝ, 0 < a ∧ ∀ x, ∀ w : EuclideanSpace ℂ ι,
        a * ‖w‖ * ‖w‖ ≤ inner ℝ (A x w) w := by
  dsimp only
  have hs := SmoothCoefficientExtension.CM.Construction.smoothCoefficientExtension_smooth η (MetricDirichlet.CM.Construction.varietyComplexDirichletOperator V e b)
    (EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen hη hηU (MetricDirichlet.CM.Construction.varietyComplexDirichletOperator_smooth V e he b)
  refine ⟨hs, SmoothCoefficientExtension.CM.Construction.smoothCoefficientExtension_bounded _ _ hs hηc,
    SmoothCoefficientExtension.CM.Construction.smoothCoefficientExtension_lipschitz _ _ hs hηc, ?_⟩
  obtain ⟨a, ha, hpos⟩ := HodgeComparison.Metric.CM.Construction.varietyDirichletCoefficient_uniform_lower_bound V e he hηc hηU
  refine ⟨min a 1, lt_min ha zero_lt_one, ?_⟩
  apply SmoothCoefficientExtension.CM.Construction.smoothCoefficientExtension_lower_bound η _ hη₀ hη₁
  intro x hx w
  change _ ≤ inner ℝ (InverseMetric.CM.Construction.realBilinearOperator
    (HodgeComparison.Metric.CM.Construction.complexGradientMetric b (HodgeComparison.Metric.CM.Construction.varietyDirichletCoefficient V e x)) w) w
  rw [InverseMetric.CM.Construction.realBilinearOperator_apply]
  exact HodgeComparison.Metric.CM.Construction.complexGradientMetric_lower_bound b _ (hpos x hx) w

/-- The extension agrees with the genuine metric on a neighborhood of the
chosen coordinate point; no ellipticity or regularity hypothesis on the variety
has been added. -/
theorem variety_exists_smooth_metric_extension (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V))
    {z : EuclideanMetric.CM.Construction.varietyEuclideanModel V} (hz : z ∈ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    ∃ A : EuclideanMetric.CM.Construction.varietyEuclideanModel V → EuclideanSpace ℂ ι →L[ℝ] EuclideanSpace ℂ ι,
      A =ᶠ[𝓝 z] MetricDirichlet.CM.Construction.varietyComplexDirichletOperator V e b ∧ ContDiff ℝ ∞ A ∧
      (∃ C : ℝ, ∀ x, ‖A x‖ ≤ C) ∧ (∃ L : NNReal, LipschitzWith L A) ∧
      ∃ a : ℝ, 0 < a ∧ ∀ x, ∀ w : EuclideanSpace ℂ ι,
        a * ‖w‖ * ‖w‖ ≤ inner ℝ (A x w) w := by
  obtain ⟨η, hη, hηc, hηU, hη₀, hη₁, hηz⟩ :=
    exists_smooth_local_cutoff (EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen hz
  refine ⟨SmoothCoefficientExtension.CM.Construction.smoothCoefficientExtension η (MetricDirichlet.CM.Construction.varietyComplexDirichletOperator V e b), ?_,
    variety_smooth_metric_extension V e he b η hη hηc hηU hη₀ hη₁⟩
  filter_upwards [hηz] with x hx
  exact SmoothCoefficientExtension.CM.Construction.smoothCoefficientExtension_eq_coefficient η _ hx

theorem variety_exists_compact_smooth_metric_extension (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V))
    {z : EuclideanMetric.CM.Construction.varietyEuclideanModel V} (hz : z ∈ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    ∃ A : EuclideanMetric.CM.Construction.varietyEuclideanModel V → EuclideanSpace ℂ ι →L[ℝ] EuclideanSpace ℂ ι,
      A =ᶠ[𝓝 z] MetricDirichlet.CM.Construction.varietyComplexDirichletOperator V e b ∧
      HasCompactSupport (fun x => A x - ContinuousLinearMap.id ℝ (EuclideanSpace ℂ ι)) ∧
      ContDiff ℝ ∞ A ∧ (∃ C : ℝ, ∀ x, ‖A x‖ ≤ C) ∧ (∃ L : NNReal, LipschitzWith L A) ∧
      ∃ a : ℝ, 0 < a ∧ ∀ x, ∀ w : EuclideanSpace ℂ ι,
        a * ‖w‖ * ‖w‖ ≤ inner ℝ (A x w) w := by
  obtain ⟨η, hη, hηc, hηU, hη₀, hη₁, hηz⟩ :=
    exists_smooth_local_cutoff (EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen hz
  refine ⟨SmoothCoefficientExtension.CM.Construction.smoothCoefficientExtension η (MetricDirichlet.CM.Construction.varietyComplexDirichletOperator V e b), ?_,
    SmoothCoefficientExtension.CM.Construction.smoothCoefficientExtension_compact_perturbation η _ hηc,
    variety_smooth_metric_extension V e he b η hη hηc hηU hη₀ hη₁⟩
  filter_upwards [hηz] with x hx
  exact SmoothCoefficientExtension.CM.Construction.smoothCoefficientExtension_eq_coefficient η _ hx

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SmoothMetricLocalization.CM.Construction
