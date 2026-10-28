import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.RestrictedPatchFields
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.OneFormFrameChange
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartCutoffLp
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartAlmostEverywhere

/-! # Chart Frame Lp -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartFrameLp.CM.Construction

noncomputable section

/-! Bounded changes from the global measurable one-form frame to any
compact chart frame, acting on actual L2 fields. -/

open _root_.MeasureTheory Set
open scoped SchwartzMap

variable {ι : Type*} [Fintype ι]

def varietyChartFrameCoefficient (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (C : CompactMetricCover.CM.Construction.CompactMetricChartCover V)
    (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V))
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (K : Set V.analyticSpace) :
    V.analyticSpace → EuclideanSpace ℂ ι →L[ℝ] EuclideanSpace ℂ ι :=
  C.restrictedPatchField K (fun i => OneFormFrameChange.CM.Construction.varietyOneFormFrameChange V b e (C.chart i))

theorem varietyChartFrameCoefficient_measurable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (C : CompactMetricCover.CM.Construction.CompactMetricChartCover V)
    (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V))
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    {K : Set V.analyticSpace} (hK : IsCompact K) (hKe : K ⊆ e.source) :
    AEStronglyMeasurable (varietyChartFrameCoefficient V C b e K) (GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V) :=
  C.restrictedPatchField_aestronglyMeasurable hK _ (fun i =>
    (OneFormFrameChange.CM.Construction.varietyOneFormFrameChange_continuousOn V b e (C.chart i) he (C.chart_mem i)).mono
      (fun _ hx => ⟨hKe hx.1, C.subset_source i hx.2⟩))

theorem varietyChartFrameCoefficient_bounded (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (C : CompactMetricCover.CM.Construction.CompactMetricChartCover V)
    (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V))
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    {K : Set V.analyticSpace} (hK : IsCompact K) (hKe : K ⊆ e.source) :
    ∃ B : ℝ, 0 < B ∧ ∀ x, ‖varietyChartFrameCoefficient V C b e K x‖ ≤ B :=
  C.restrictedPatchField_bounded hK _ (fun i =>
    (OneFormFrameChange.CM.Construction.varietyOneFormFrameChange_continuousOn V b e (C.chart i) he (C.chart_mem i)).mono
      (fun _ hx => ⟨hKe hx.1, C.subset_source i hx.2⟩))

theorem varietyChartFrameCoefficient_form (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (C : CompactMetricCover.CM.Construction.CompactMetricChartCover V)
    (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V))
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    {K : Set V.analyticSpace} (hKe : K ⊆ e.source)
    (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 1) {x : V.analyticSpace} (hx : x ∈ K) :
    varietyChartFrameCoefficient V C b e K x (GlobalLp.CM.Construction.varietyOneFormField V C b form x) =
      GlobalLp.CM.Construction.varietyOneFormInChart V b e form x := by
  obtain ⟨i, hi⟩ := C.exists_piece x
  change K.indicator (C.patchField (fun i => OneFormFrameChange.CM.Construction.varietyOneFormFrameChange V b e (C.chart i))) x
    (C.patchField (fun i => GlobalLp.CM.Construction.varietyOneFormInChart V b (C.chart i) form) x) = _
  rw [indicator_of_mem hx, C.patchField_eq _ hi, C.patchField_eq _ hi]
  exact (OneFormFrameChange.CM.Construction.varietyOneFormInChart_transition V b e (C.chart i) he (C.chart_mem i) form
    (hKe hx) (C.piece_subset_source i hi)).symm

def varietyChartFrameL2 (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (C : CompactMetricCover.CM.Construction.CompactMetricChartCover V)
    (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V))
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    {K : Set V.analyticSpace} (hK : IsCompact K) (hKe : K ⊆ e.source) :
    Lp (EuclideanSpace ℂ ι) 2 (GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V) →L[ℝ]
      Lp (EuclideanSpace ℂ ι) 2 (GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V) :=
  LpCoefficients.CM.Construction.boundedFieldLp (varietyChartFrameCoefficient V C b e K)
    (varietyChartFrameCoefficient_measurable V C b e he hK hKe)
    (Filter.Eventually.of_forall (varietyChartFrameCoefficient_bounded V C b e he hK hKe).choose_spec.2)

theorem varietyChartFrameL2_coe (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (C : CompactMetricCover.CM.Construction.CompactMetricChartCover V)
    (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V))
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    {K : Set V.analyticSpace} (hK : IsCompact K) (hKe : K ⊆ e.source)
    (u : Lp (EuclideanSpace ℂ ι) 2 (GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V)) :
    varietyChartFrameL2 V C b e he hK hKe u =ᵐ[GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V]
      (fun x => varietyChartFrameCoefficient V C b e K x (u x)) :=
  LpCoefficients.CM.Construction.boundedFieldLp_coe _ _ _ u

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartFrameLp.CM.Construction
