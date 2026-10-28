import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.HolomorphicMixedChartPair
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.MetricCoefficientDivergence
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartTestDifferential

/-! # Holomorphic Test Differential -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.HolomorphicTestDifferential.CM.Construction

noncomputable section

section

/-! Holomorphic coefficients of the differential of an actual global
chart test form are the genuine Euclidean holomorphic test derivatives. -/

open Filter
open scoped _root_.Topology SchwartzMap

theorem oneCovectorCLM_d_inChart (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (f : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 0)
    {y : V.analyticModel} (hy : y ∈ e.target) :
    HolomorphicMixedChartPair.CM.Construction.oneCovectorCLM ((Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d f).val.inChart e y) =
      fderiv ℝ (HolomorphicPrimitive.CM.Construction.zeroFormScalar f ∘ e.symm) y := by
  rw [Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d_inChart f e he hy, HolomorphicPrimitive.CM.Construction.zeroFormScalar_reconstruct, extDeriv_constOfIsEmpty]
  ext u
  rfl

theorem varietyChartTestForm_holomorphic_derivative (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (g : 𝓢(EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) (hgc : HasCompactSupport (g : EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℂ))
    (hg : tsupport g ⊆ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
    {z : EuclideanMetric.CM.Construction.varietyEuclideanModel V} (hz : z ∈ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) (u : EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    ComplexCovector.CM.Construction.holomorphicCovectorProjection
      (HolomorphicMixedChartPair.CM.Construction.oneCovectorCLM ((Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (ChartTestFunction.CM.Construction.varietyChartTestForm V e he g hgc hg)).val.inChart e
        (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z))) (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V u) =
      MetricDerivative.CM.Construction.holomorphicDirectionalDerivative g z u := by
  let f := ChartTestFunction.CM.Construction.varietyChartTestForm V e he g hgc hg
  rw [oneCovectorCLM_d_inChart V e he f hz]
  change MetricDerivative.CM.Construction.holomorphicDirectionalDerivative (HolomorphicPrimitive.CM.Construction.zeroFormScalar f ∘ e.symm)
    (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z) (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V u) = _
  refine (MetricCoefficientDivergence.CM.Construction.holomorphicDirectionalDerivative_comp_complexLinear
    (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).toContinuousLinearMap (HolomorphicPrimitive.CM.Construction.zeroFormScalar f ∘ e.symm)
    ((HolomorphicPrimitive.CM.Construction.zeroFormScalar_contDiffAt_inChart f e he hz).differentiableAt (by simp)) u).symm.trans ?_
  change MetricDerivative.CM.Construction.holomorphicDirectionalDerivative (ScalarChartLocalization.CM.Construction.varietyScalarChart V e f) z u = _
  apply MetricCoefficientDivergence.CM.Construction.holomorphicDirectionalDerivative_congr
  filter_upwards [(EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen.mem_nhds hz] with w hw
  exact ChartTestFunction.CM.Construction.varietyChartTestForm_in_chart V e he g hgc hg hw

end

/-! The genuine global one-form pairing with a chart test has its explicit
inverse-Hermitian expression, including the metric density and type factor. -/

open _root_.MeasureTheory
open scoped SchwartzMap

theorem projectiveL2Pair_holomorphic_chart_test (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 1)
    (ha : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree V.analyticModel V.analyticSpace 1 0 a.val)
    (g : 𝓢(EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) (hgc : HasCompactSupport (g : EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℂ))
    (hg : tsupport g ⊆ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    Analysis.HodgeTheory.Decomposition.Form.Constructions.projectiveL2Pair V 1 a
      (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (ChartTestFunction.CM.Construction.varietyChartTestForm V e he g hgc hg)) =
      ∫ z in (EuclideanMetric.CM.Construction.varietyEuclideanDomain V e : Set (EuclideanMetric.CM.Construction.varietyEuclideanModel V)),
        (Metric.CM.Construction.varietyMetricDensity V e z : ℂ) *
          (2 * ∑ j, ∑ k, star (a.val.inChart e (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z)
            (fun _ => HermitianVolumeDensity.CM.Construction.varietyEuclideanComplexBasis V k)) *
            (InverseCoefficientCancellation.CM.Construction.varietyHermitianMatrix V e (HermitianVolumeDensity.CM.Construction.varietyEuclideanComplexBasis V)
              (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z))⁻¹ j k *
            MetricDerivative.CM.Construction.holomorphicDirectionalDerivative g z (EuclideanSpace.basisFun (Fin V.complexDimension) ℂ j)) := by
  let c := Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (ChartTestFunction.CM.Construction.varietyChartTestForm V e he g hgc hg)
  have hc : ∀ x, x ∉ e.source → c x = 0 := by
    intro x hx
    exact ChartTestDifferential.CM.Construction.varietyChartTestForm_d_zero V e he g hgc hg
      (fun h => hx (ChartAlmostEverywhere.CM.Construction.varietyCompactChartImage_subset_source V e hg h))
  rw [Analysis.HodgeTheory.Decomposition.Form.Constructions.projectiveL2Pair, Analysis.HodgeTheory.Decomposition.ChartIntegral.Constructions.projectiveMetricVolume_integral_chart V e he
    (Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveFormPointPair V 1 a.val c.val)
    (Analysis.HodgeTheory.Decomposition.MetricCoefficients.Constructions.projectiveFormPointPair_continuous V 1 a c).aestronglyMeasurable
    (fun x hx => Analysis.HodgeTheory.Decomposition.LocalMetric.Constructions.projectiveFormPointPair_zero_of_right V 1 a.val c.val x (hc x hx))]
  apply setIntegral_congr_fun (EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen.measurableSet
  intro z hz
  change (Metric.CM.Construction.varietyMetricDensity V e z : ℂ) *
    Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveFormPointPair V 1 a.val c.val (e.symm (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z)) = _
  have hzy : EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z ∈ e.target := hz
  have hchart : Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveFormPointPair V 1 a.val c.val (e.symm (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z)) =
      Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveChartFormPair V e he (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z) hzy 1
        (a.val.inChart e (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z)) (c.val.inChart e (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z)) := by
    simpa only [e.right_inv hzy] using
      Analysis.HodgeTheory.Decomposition.ProjectiveFormMetric.Constructions.projectiveFormPointPair_eq_chart V e he _ (e.map_target hzy) 1 a.val c.val
  rw [hchart, HolomorphicMixedChartPair.CM.Construction.projectiveChartPair_holomorphic_left V e he _ hzy (HermitianVolumeDensity.CM.Construction.varietyEuclideanComplexBasis V) _ _
      (ha e he _ hzy)]
  congr 2
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  exact varietyChartTestForm_holomorphic_derivative V e he g hgc hg hz
    (EuclideanSpace.basisFun (Fin V.complexDimension) ℂ j)

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.HolomorphicTestDifferential.CM.Construction
