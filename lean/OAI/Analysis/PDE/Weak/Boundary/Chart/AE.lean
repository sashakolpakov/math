import OAI.Analysis.PDE.Weak.Boundary.Chart.Measure

noncomputable section
open Set Filter _root_.MeasureTheory
open scoped Topology ContDiff
namespace OAI.Analysis.PDE.Weak

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem chart_quasiMeasurePreserving (μ : Measure E) [μ.IsAddHaarMeasure]
    {U V : Set E} (hU : IsOpen U) (hV : IsOpen V) (hVb : Bornology.IsBounded V)
    {G P : E → E} (hG : Continuous G) (hP : ContDiff ℝ 1 P)
    (hGU : MapsTo G U V) (hPV : MapsTo P V U)
    (hPG : ∀ y ∈ U, P (G y) = y) (hGP : ∀ z ∈ V, G (P z) = z) :
    Measure.QuasiMeasurePreserving G (μ.restrict U) μ := by
  have hVc : IsCompact (closure V) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_closure hVb.closure
  have hd : Continuous (fun y => (fderiv ℝ P y).det) :=
    ContinuousLinearMap.continuous_det.comp (hP.continuous_fderiv (by norm_num))
  obtain ⟨C, hC⟩ := hVc.exists_bound_of_continuousOn hd.continuousOn
  refine ⟨hG.measurable, Measure.absolutelyContinuous_of_le_smul
    (chart_map_measure_le_of_fderiv μ hU hV hG (hP.differentiable one_ne_zero) (C := C)
      hGU hPV hPG hGP ?_)⟩
  intro y hy
  simpa only [Real.norm_eq_abs] using hC y (subset_closure hy)

end OAI.Analysis.PDE.Weak
