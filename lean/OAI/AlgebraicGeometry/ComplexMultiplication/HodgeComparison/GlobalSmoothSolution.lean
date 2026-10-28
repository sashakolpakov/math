import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.LocalSmoothGerm
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SmoothRepresentativeGluing
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.GlobalSobolevFaithful

/-! # Global Smooth Solution -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.GlobalSmoothSolution.CM.Construction

noncomputable section

/-! Every actual global weak metric solution with smooth forcing is the
Sobolev image of a genuine global smooth scalar function. -/

open _root_.MeasureTheory Set Filter

variable {ι : Type*} [Fintype ι]

theorem globalWeakMetricSolution_smooth (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (C : CompactMetricCover.CM.Construction.CompactMetricChartCover V) (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V))
    (u : GlobalSobolevGraph.CM.Construction.varietySobolevGraph V C b) (F : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 0)
    (hsol : GlobalInteriorSmooth.CM.Construction.IsGlobalWeakMetricSolution V C b u F) :
    ∃ f : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 0, GlobalSobolevGraph.CM.Construction.varietySmoothToSobolev V C b f = u := by
  have hlocal : ∀ x : V.analyticSpace, ∃ U : Set V.analyticSpace,
      IsOpen U ∧ x ∈ U ∧ ∃ f : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 0,
        GlobalSobolevGraph.CM.Construction.varietySobolevFunction V C b u =ᵐ[(GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V).restrict U] HolomorphicPrimitive.CM.Construction.zeroFormScalar f := by
    intro x
    let e := chartAt V.analyticModel x
    have he : e ∈ atlas V.analyticModel V.analyticSpace := chart_mem_atlas _ _
    have hex : x ∈ e.source := mem_chart_source _ _
    let z := (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).symm (e x)
    have hz : z ∈ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e := by
      change EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V ((EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).symm (e x)) ∈ e.target
      rw [ContinuousLinearEquiv.apply_symm_apply]
      exact e.map_source hex
    obtain ⟨U, hU, hzU, hUe, v, hvs, hrep⟩ :=
      GlobalLocalRepresentative.CM.Construction.globalWeakMetricSolution_local_representative V C b e he u F hsol hz
    have h := LocalSmoothGerm.CM.Construction.chart_smooth_representative_global_germ V e he (GlobalSobolevGraph.CM.Construction.varietySobolevFunction V C b u)
      hU hUe hzU v hvs hrep
    simpa only [z, ContinuousLinearEquiv.apply_symm_apply, e.left_inv hex] using h
  obtain ⟨f, hf⟩ := SmoothRepresentativeGluing.CM.Construction.smooth_representative_of_local_germs V (GlobalSobolevGraph.CM.Construction.varietySobolevFunction V C b u) hlocal
  refine ⟨f, GlobalSobolevFaithful.CM.Construction.varietySobolevFunction_injective V C b ?_⟩
  rw [GlobalSobolevGraph.CM.Construction.varietySobolevFunction_smooth, hf]

theorem derivative_zero_isGlobalWeakMetricSolution (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (C : CompactMetricCover.CM.Construction.CompactMetricChartCover V) (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V))
    (u : GlobalSobolevGraph.CM.Construction.varietySobolevGraph V C b) (hu : GlobalSobolevGraph.CM.Construction.varietySobolevDerivative V C b u = 0) :
    GlobalInteriorSmooth.CM.Construction.IsGlobalWeakMetricSolution V C b u 0 := by
  intro v
  rw [map_zero, inner_zero_left, hu]
  apply integral_eq_zero_of_ae
  filter_upwards [Lp.coeFn_zero (EuclideanSpace ℂ ι) 2 (GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V)] with x hx
  rw [hx, Pi.zero_apply, map_zero, inner_zero_left]
  rfl

theorem derivative_kernel_smooth (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (C : CompactMetricCover.CM.Construction.CompactMetricChartCover V) (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V))
    (u : GlobalSobolevGraph.CM.Construction.varietySobolevGraph V C b) (hu : GlobalSobolevGraph.CM.Construction.varietySobolevDerivative V C b u = 0) :
    ∃ f : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 0, GlobalSobolevGraph.CM.Construction.varietySmoothToSobolev V C b f = u :=
  globalWeakMetricSolution_smooth V C b u 0 (derivative_zero_isGlobalWeakMetricSolution V C b u hu)

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.GlobalSmoothSolution.CM.Construction
