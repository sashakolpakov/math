import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.OneFormFrameChange
import OAI.Analysis.DifferentialForms.Manifold.ChartEquiv

/-! # Smooth One Form Faithful -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SmoothOneFormFaithful.CM.Construction

noncomputable section

/-! The actual smooth one-form inclusion into the global L2 covector
space is injective, using chart transitions and positivity on open sets. -/

open Set _root_.MeasureTheory Filter

variable {ι : Type*} [Fintype ι]

theorem varietyOneFormComponents_injective (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V)) :
    Function.Injective (GlobalLp.CM.Construction.varietyOneFormComponents V b) := by
  intro φ ψ h
  have hcov : OneFormFrameChange.CM.Construction.varietyCovectorOfFormValue V φ = OneFormFrameChange.CM.Construction.varietyCovectorOfFormValue V ψ :=
    GlobalLp.CM.Construction.complexCovectorComponents_injective b h
  apply ContinuousAlternatingMap.ext
  intro v
  have hv : v = fun _ => v 0 := funext (fun i => congrArg v (Subsingleton.elim i 0))
  rw [hv]
  have hval := congrArg (fun q : EuclideanMetric.CM.Construction.varietyEuclideanModel V →L[ℝ] ℂ => q ((EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).symm (v 0))) hcov
  change φ (fun _ => EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V ((EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).symm (v 0))) =
    ψ (fun _ => EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V ((EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).symm (v 0))) at hval
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using hval

theorem varietyOneFormL2_eq_zero_imp (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (C : CompactMetricCover.CM.Construction.CompactMetricChartCover V)
    (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V))
    (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 1)
    (hform : GlobalLp.CM.Construction.varietyOneFormL2 V C b form = 0) : form = 0 := by
  have hfield : ∀ᵐ x ∂ GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V, GlobalLp.CM.Construction.varietyOneFormField V C b form x = 0 := by
    have hf := GlobalLp.CM.Construction.varietyOneFormL2_coe V C b form
    rw [hform] at hf
    filter_upwards [hf, Lp.coeFn_zero (EuclideanSpace ℂ ι) 2 (GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V)] with x hx hz
    exact hx.symm.trans hz
  have hchart (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
      (he : e ∈ atlas V.analyticModel V.analyticSpace) :
      EqOn (GlobalLp.CM.Construction.varietyOneFormInChart V b e form) 0 e.source := by
    apply Measure.eqOn_open_of_ae_eq (μ := GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V) ?_ e.open_source
      (GlobalLp.CM.Construction.varietyOneFormInChart_continuousOn V b e he form) continuousOn_const
    apply (ae_restrict_iff' e.open_source.measurableSet).mpr
    filter_upwards [hfield] with x hx
    intro hxe
    obtain ⟨i, hi⟩ := C.exists_piece x
    have hxi : GlobalLp.CM.Construction.varietyOneFormInChart V b (C.chart i) form x = 0 := (C.patchField_eq _ hi).symm.trans hx
    rw [OneFormFrameChange.CM.Construction.varietyOneFormInChart_transition V b e (C.chart i) he (C.chart_mem i) form hxe (C.piece_subset_source i hi),
      hxi, map_zero]
    rfl
  apply Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ext
  intro x
  let e := chartAt V.analyticModel x
  have he : e ∈ atlas V.analyticModel V.analyticSpace := chart_mem_atlas _ _
  have hx : x ∈ e.source := mem_chart_source _ _
  have hc : form.val.inChart e (e x) = 0 :=
    varietyOneFormComponents_injective V b (by
      rw [map_zero]
      exact hchart e he hx)
  rw [← Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.fromChart_inChart_apply e he form.val hx]
  change (form.val.inChart e (e x)).compContinuousLinearMap _ = 0
  rw [hc]
  ext v
  rfl

theorem varietyOneFormL2_injective (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (C : CompactMetricCover.CM.Construction.CompactMetricChartCover V)
    (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V)) : Function.Injective (GlobalLp.CM.Construction.varietyOneFormL2 V C b) := by
  intro form other h
  apply sub_eq_zero.mp
  apply varietyOneFormL2_eq_zero_imp V C b
  rw [map_sub, h, sub_self]

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SmoothOneFormFaithful.CM.Construction
