import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartFrameLp

/-! # Frame Identity -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.FrameIdentity.CM.Construction

noncomputable section

/-! A chart's own component transition is the identity, including on
the corresponding piece of the global measurable frame. -/

open Set Filter
open scoped _root_.Topology

theorem complexCovectorPullback_id {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Fintype ι] (b : OrthonormalBasis ι ℝ E) :
    GlobalLp.CM.Construction.complexCovectorPullback b (ContinuousLinearMap.id ℝ E) = ContinuousLinearMap.id ℝ (EuclideanSpace ℂ ι) := by
  apply ContinuousLinearMap.ext
  intro z
  change GlobalLp.CM.Construction.complexCovectorComponents b ((GlobalLp.CM.Construction.complexCovectorSynthesis b z).comp (ContinuousLinearMap.id ℝ E)) = z
  rw [ContinuousLinearMap.comp_id, GlobalLp.CM.Construction.complexCovectorComponents_synthesis]

theorem varietyEuclideanConjugateOperator_id (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    OneFormFrameChange.CM.Construction.varietyEuclideanConjugateOperator V (ContinuousLinearMap.id ℝ V.analyticModel) =
      ContinuousLinearMap.id ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V) := by
  apply ContinuousLinearMap.ext
  intro u
  exact (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).symm_apply_apply u

theorem varietyOneFormFrameChange_self (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V))
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    {x : V.analyticSpace} (hx : x ∈ e.source) :
    OneFormFrameChange.CM.Construction.varietyOneFormFrameChange V b e e x = ContinuousLinearMap.id ℝ (EuclideanSpace ℂ ι) := by
  have heq : (e ∘ e.symm) =ᶠ[𝓝 (e x)] id := by
    filter_upwards [e.open_target.mem_nhds (e.map_source hx)] with y hy
    exact e.right_inv hy
  have hD : fderiv ℝ (e ∘ e.symm) (e x) = ContinuousLinearMap.id ℝ V.analyticModel := by
    rw [heq.fderiv_eq, fderiv_id]
  rw [OneFormFrameChange.CM.Construction.varietyOneFormFrameChange, hD, varietyEuclideanConjugateOperator_id, complexCovectorPullback_id]

theorem varietyChartFrameCoefficient_on_own_piece (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (C : CompactMetricCover.CM.Construction.CompactMetricChartCover V) {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V)) (i : Fin C.size)
    {K : Set V.analyticSpace} {x : V.analyticSpace} (hxK : x ∈ K) (hxi : x ∈ C.piece i) :
    ChartFrameLp.CM.Construction.varietyChartFrameCoefficient V C b (C.chart i) K x = ContinuousLinearMap.id ℝ (EuclideanSpace ℂ ι) := by
  change K.indicator (C.patchField (fun j => OneFormFrameChange.CM.Construction.varietyOneFormFrameChange V b (C.chart i) (C.chart j))) x = _
  rw [indicator_of_mem hxK, C.patchField_eq _ hxi]
  exact varietyOneFormFrameChange_self V b (C.chart i) (C.piece_subset_source i hxi)

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.FrameIdentity.CM.Construction
