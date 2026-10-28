import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartCutoffDerivative
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SmoothEstimate
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.GlobalSobolevGraph

/-! # Chart Estimate -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartEstimate.CM.Construction

noncomputable section

/-! Actual chart localization is bounded in the global derivative graph
norm, with no additional regularity assumption on a completed element. -/

open _root_.MeasureTheory Set
open scoped SchwartzMap LineDeriv

theorem varietyScalarChartSobolevCoordinate_bound (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (C : CompactMetricCover.CM.Construction.CompactMetricChartCover V)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V))
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (g : 𝓢(EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) (hgc : HasCompactSupport (g : EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℂ))
    (hg : tsupport g ⊆ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ f : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 0,
      ‖ChartCutoffLp.CM.Construction.varietyScalarChartSobolevCoordinate V e he g hgc hg f‖ ≤
        B * (‖GlobalLp.CM.Construction.varietySmoothScalarL2 V f‖ + ‖GlobalLp.CM.Construction.varietySmoothDifferentialL2 V C b f‖) := by
  classical
  obtain ⟨B, hB, hder⟩ := ChartCutoffDerivative.CM.Construction.varietyScalarChartCutoff_derivative_bound V C b e he g hgc hg
  let T : Lp ℂ 2 (GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V) →L[ℝ] Lp ℂ 2 (volume : Measure (EuclideanMetric.CM.Construction.varietyEuclideanModel V)) :=
    ChartCutoffLp.CM.Construction.varietyChartCutoffL2 V e he g hgc hg
  let c : ℝ := ‖(2 * Real.pi * Complex.I : ℂ)⁻¹‖
  refine ⟨‖T‖ + c * ∑ _ : ι, B, by dsimp [c]; positivity, ?_⟩
  intro f
  let s : ℝ := ‖GlobalLp.CM.Construction.varietySmoothScalarL2 V f‖ + ‖GlobalLp.CM.Construction.varietySmoothDifferentialL2 V C b f‖
  have hL2 : ‖(ScalarChartLocalization.CM.Construction.varietyScalarChartCutoff V e he g hgc hg f).toLp 2 volume‖ ≤ ‖T‖ * s := by
    rw [← ChartCutoffLp.CM.Construction.varietyChartCutoffL2_smooth V e he g hgc hg f]
    exact (T.le_opNorm _).trans (mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_right (norm_nonneg _)) (norm_nonneg T))
  have hsum : ∑ i, ‖(∂_{b i} (ScalarChartLocalization.CM.Construction.varietyScalarChartCutoff V e he g hgc hg f)).toLp 2 volume‖ ≤
      (∑ _ : ι, B) * s := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum (fun i _ => hder f i)
  have hs := SmoothEstimate.CM.Construction.schwartzSobolevCoordinate_one_bound b (ScalarChartLocalization.CM.Construction.varietyScalarChartCutoff V e he g hgc hg f)
  change ‖SobolevIs.CM.Construction.schwartzSobolevCoordinate 1 (ScalarChartLocalization.CM.Construction.varietyScalarChartCutoff V e he g hgc hg f)‖ ≤ _
  calc
    _ ≤ ‖T‖ * s + c * ((∑ _ : ι, B) * s) :=
      hs.trans (add_le_add hL2 (mul_le_mul_of_nonneg_left hsum (norm_nonneg _)))
    _ = _ := by ring

theorem varietyScalarChartSobolevCoordinate_graph_bound (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (C : CompactMetricCover.CM.Construction.CompactMetricChartCover V)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V))
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (g : 𝓢(EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) (hgc : HasCompactSupport (g : EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℂ))
    (hg : tsupport g ⊆ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    ∃ B : ℝ, ∀ f : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 0,
      ‖ChartCutoffLp.CM.Construction.varietyScalarChartSobolevCoordinate V e he g hgc hg f‖ ≤ B * ‖GlobalSobolevGraph.CM.Construction.varietySmoothToSobolev V C b f‖ := by
  obtain ⟨B, hB, hbound⟩ := varietyScalarChartSobolevCoordinate_bound V C b e he g hgc hg
  refine ⟨2 * B, fun f => ?_⟩
  have hnorm := GlobalSobolevGraph.CM.Construction.varietySobolevGraph_norm_sq V C b (GlobalSobolevGraph.CM.Construction.varietySmoothToSobolev V C b f)
  change ‖GlobalSobolevGraph.CM.Construction.varietySmoothToSobolev V C b f‖ ^ 2 =
    ‖GlobalLp.CM.Construction.varietySmoothScalarL2 V f‖ ^ 2 + ‖GlobalLp.CM.Construction.varietySmoothDifferentialL2 V C b f‖ ^ 2 at hnorm
  have hJ : ‖GlobalLp.CM.Construction.varietySmoothScalarL2 V f‖ ≤ ‖GlobalSobolevGraph.CM.Construction.varietySmoothToSobolev V C b f‖ := by
    nlinarith [sq_nonneg ‖GlobalLp.CM.Construction.varietySmoothDifferentialL2 V C b f‖,
      norm_nonneg (GlobalLp.CM.Construction.varietySmoothScalarL2 V f), norm_nonneg (GlobalSobolevGraph.CM.Construction.varietySmoothToSobolev V C b f)]
  have hD : ‖GlobalLp.CM.Construction.varietySmoothDifferentialL2 V C b f‖ ≤ ‖GlobalSobolevGraph.CM.Construction.varietySmoothToSobolev V C b f‖ := by
    nlinarith [sq_nonneg ‖GlobalLp.CM.Construction.varietySmoothScalarL2 V f‖,
      norm_nonneg (GlobalLp.CM.Construction.varietySmoothDifferentialL2 V C b f), norm_nonneg (GlobalSobolevGraph.CM.Construction.varietySmoothToSobolev V C b f)]
  calc
    _ ≤ B * (‖GlobalLp.CM.Construction.varietySmoothScalarL2 V f‖ + ‖GlobalLp.CM.Construction.varietySmoothDifferentialL2 V C b f‖) := hbound f
    _ ≤ B * (2 * ‖GlobalSobolevGraph.CM.Construction.varietySmoothToSobolev V C b f‖) :=
      mul_le_mul_of_nonneg_left (by linarith) hB
    _ = _ := by ring

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartEstimate.CM.Construction
