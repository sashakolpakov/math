import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.MetricIntegration
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-! # Metric Chart Measure -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.MetricChartMeasure.CM.Construction

noncomputable section

section

/-! The actual positive projective metric density defines a Borel measure
on every chart source by pushforward of weighted Euclidean volume. -/

open _root_.MeasureTheory Set
open scoped ENNReal _root_.Manifold

instance varietyAnalyticSpaceMeasurable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    MeasurableSpace V.analyticSpace := borel V.analyticSpace

instance varietyAnalyticSpaceBorel (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) : BorelSpace V.analyticSpace :=
  ⟨rfl⟩

def varietyEuclideanChartPoint (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (z : EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) : V.analyticSpace :=
  e.symm (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z.val)

theorem varietyEuclideanChartPoint_continuous (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) :
    Continuous (varietyEuclideanChartPoint V e) :=
  e.continuousOn_symm.comp_continuous
    ((EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).continuous.comp continuous_subtype_val) (fun z => z.property)

theorem varietyEuclideanChartPoint_mem_source (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (z : EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    varietyEuclideanChartPoint V e z ∈ e.source := e.map_target z.property

def varietyMetricChartMeasure (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) : Measure V.analyticSpace :=
  Measure.map (varietyEuclideanChartPoint V e)
    (((volume : Measure (EuclideanMetric.CM.Construction.varietyEuclideanModel V)).comap
      (Subtype.val : EuclideanMetric.CM.Construction.varietyEuclideanDomain V e → EuclideanMetric.CM.Construction.varietyEuclideanModel V)).withDensity
      (fun z => ENNReal.ofReal (Metric.CM.Construction.varietyMetricDensity V e z.val)))

theorem varietyMetricChartMeasure_compl_source (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) :
    varietyMetricChartMeasure V e e.sourceᶜ = 0 := by
  rw [varietyMetricChartMeasure, Measure.map_apply
    (varietyEuclideanChartPoint_continuous V e).measurable e.open_source.measurableSet.compl]
  have hpre : varietyEuclideanChartPoint V e ⁻¹' e.sourceᶜ = ∅ := by
    ext z
    simp only [mem_preimage, mem_compl_iff, varietyEuclideanChartPoint_mem_source,
      not_true_eq_false, mem_empty_iff_false]
  rw [hpre, measure_empty]

theorem varietyMetricChartMeasure_lintegral (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (h : V.analyticSpace → ℝ≥0∞) (hh : Measurable h) :
    (∫⁻ x, h x ∂ varietyMetricChartMeasure V e) =
      ∫⁻ z in (EuclideanMetric.CM.Construction.varietyEuclideanDomain V e : Set (EuclideanMetric.CM.Construction.varietyEuclideanModel V)),
        ENNReal.ofReal (Metric.CM.Construction.varietyMetricDensity V e z) * h (e.symm (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z)) := by
  have hρ : Measurable (fun z : EuclideanMetric.CM.Construction.varietyEuclideanDomain V e =>
      ENNReal.ofReal (Metric.CM.Construction.varietyMetricDensity V e z.val)) := by
    have hcont : Continuous (fun z : EuclideanMetric.CM.Construction.varietyEuclideanDomain V e => Metric.CM.Construction.varietyMetricDensity V e z.val) :=
      (Metric.CM.Construction.varietyMetricDensity_smooth V e he).continuousOn.comp_continuous continuous_subtype_val
        (fun z => z.property)
    exact (ENNReal.continuous_ofReal.comp hcont).measurable
  rw [varietyMetricChartMeasure, lintegral_map hh (varietyEuclideanChartPoint_continuous V e).measurable]
  have hcomp : Measurable (fun z : EuclideanMetric.CM.Construction.varietyEuclideanDomain V e => h (varietyEuclideanChartPoint V e z)) :=
    hh.comp (varietyEuclideanChartPoint_continuous V e).measurable
  rw [lintegral_withDensity_eq_lintegral_mul _ hρ hcomp]
  exact lintegral_subtype_comap (EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen.measurableSet
    (fun z => ENNReal.ofReal (Metric.CM.Construction.varietyMetricDensity V e z) * h (e.symm (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z)))

def varietyMetricChartCoordinates (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (S : Set V.analyticSpace) :
    Set (EuclideanMetric.CM.Construction.varietyEuclideanModel V) :=
  (Subtype.val : EuclideanMetric.CM.Construction.varietyEuclideanDomain V e → EuclideanMetric.CM.Construction.varietyEuclideanModel V) ''
    (varietyEuclideanChartPoint V e ⁻¹' S)

theorem mem_varietyMetricChartCoordinates (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (S : Set V.analyticSpace)
    (z : EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    z ∈ varietyMetricChartCoordinates V e S ↔ z ∈ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e ∧
      e.symm (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z) ∈ S := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w.property, hw⟩
  · rintro ⟨hz, hs⟩
    exact ⟨⟨z, hz⟩, hs, rfl⟩

theorem varietyMetricChartCoordinates_measurable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) {S : Set V.analyticSpace}
    (hS : MeasurableSet S) : MeasurableSet (varietyMetricChartCoordinates V e S) :=
  (MeasurableEmbedding.subtype_coe (EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen.measurableSet).measurableSet_image.mpr
    (hS.preimage (varietyEuclideanChartPoint_continuous V e).measurable)

theorem varietyMetricChartMeasure_apply (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) {S : Set V.analyticSpace}
    (hS : MeasurableSet S) :
    varietyMetricChartMeasure V e S =
      ∫⁻ z in varietyMetricChartCoordinates V e S, ENNReal.ofReal (Metric.CM.Construction.varietyMetricDensity V e z) := by
  rw [varietyMetricChartMeasure, Measure.map_apply
    (varietyEuclideanChartPoint_continuous V e).measurable hS,
    withDensity_apply _ (hS.preimage (varietyEuclideanChartPoint_continuous V e).measurable)]
  exact setLIntegral_subtype (EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen.measurableSet
    (varietyEuclideanChartPoint V e ⁻¹' S) (fun z => ENNReal.ofReal (Metric.CM.Construction.varietyMetricDensity V e z))

end

/-! The genuine metric chart measures agree on every measurable subset of
an overlap, by the proved Jacobian transformation of their densities. -/

open _root_.MeasureTheory Set
open scoped ENNReal _root_.Manifold

theorem varietyEuclideanTransition_mem_target (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e f : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (z : EuclideanMetric.CM.Construction.varietyEuclideanModel V)
    (hz : e.symm (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z) ∈ f.source) :
    MetricJacobian.CM.Construction.varietyEuclideanTransition V e f z ∈ EuclideanMetric.CM.Construction.varietyEuclideanDomain V f := by
  change EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V (MetricJacobian.CM.Construction.varietyEuclideanTransition V e f z) ∈ f.target
  simp only [MetricJacobian.CM.Construction.varietyEuclideanTransition, Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply]
  exact f.map_source hz

theorem varietyEuclideanTransition_inverse (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e f : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (z : EuclideanMetric.CM.Construction.varietyEuclideanModel V)
    (hz : z ∈ EuclideanMetric.CM.Construction.varietyEuclideanDomain V f)
    (he : f.symm (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z) ∈ e.source) :
    MetricJacobian.CM.Construction.varietyEuclideanTransition V e f (MetricJacobian.CM.Construction.varietyEuclideanTransition V f e z) = z := by
  apply (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).injective
  simp only [MetricJacobian.CM.Construction.varietyEuclideanTransition, Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply]
  rw [e.left_inv he, f.right_inv hz]

theorem varietyMetricChartCoordinates_transition (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e f : OpenPartialHomeomorph V.analyticSpace V.analyticModel) {S : Set V.analyticSpace}
    (hSe : S ⊆ e.source) (hSf : S ⊆ f.source) :
    MetricJacobian.CM.Construction.varietyEuclideanTransition V e f '' varietyMetricChartCoordinates V e S =
      varietyMetricChartCoordinates V f S := by
  apply Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩
    have h := (mem_varietyMetricChartCoordinates V e S z).mp hz
    apply (mem_varietyMetricChartCoordinates V f S _).mpr
    refine ⟨varietyEuclideanTransition_mem_target V e f z (hSf h.2), ?_⟩
    rw [MetricIntegration.CM.Construction.varietyEuclideanTransition_inverse_point V e f (hSf h.2)]
    exact h.2
  · intro z hz
    have h := (mem_varietyMetricChartCoordinates V f S z).mp hz
    refine ⟨MetricJacobian.CM.Construction.varietyEuclideanTransition V f e z, ?_, varietyEuclideanTransition_inverse V e f z h.1 (hSe h.2)⟩
    apply (mem_varietyMetricChartCoordinates V e S _).mpr
    refine ⟨varietyEuclideanTransition_mem_target V f e z (hSe h.2), ?_⟩
    rw [MetricIntegration.CM.Construction.varietyEuclideanTransition_inverse_point V f e (hSe h.2)]
    exact h.2

theorem varietyMetricChartMeasure_eq_on_overlap (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e f : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace) (hf : f ∈ atlas V.analyticModel V.analyticSpace)
    {S : Set V.analyticSpace} (hS : MeasurableSet S) (hSe : S ⊆ e.source) (hSf : S ⊆ f.source) :
    varietyMetricChartMeasure V e S = varietyMetricChartMeasure V f S := by
  rw [varietyMetricChartMeasure_apply V e hS, varietyMetricChartMeasure_apply V f hS]
  have h := MetricIntegration.CM.Construction.varietyMetric_lintegral_transition V e f he hf
    (varietyMetricChartCoordinates_measurable V e hS)
    (fun z hz => ((mem_varietyMetricChartCoordinates V e S z).mp hz).1)
    (fun z hz => hSf ((mem_varietyMetricChartCoordinates V e S z).mp hz).2)
    (fun _ => (1 : ℝ≥0∞))
  rw [varietyMetricChartCoordinates_transition V e f hSe hSf] at h
  simpa only [mul_one] using h.symm

theorem varietyMetricChartMeasure_restrict_overlap (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e f : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace) (hf : f ∈ atlas V.analyticModel V.analyticSpace) :
    (varietyMetricChartMeasure V e).restrict (e.source ∩ f.source) =
      (varietyMetricChartMeasure V f).restrict (e.source ∩ f.source) := by
  apply (Measure.restrict_congr_meas (e.open_source.measurableSet.inter f.open_source.measurableSet)).mpr
  intro S hS hSm
  exact varietyMetricChartMeasure_eq_on_overlap V e f he hf hSm
    (hS.trans inter_subset_left) (hS.trans inter_subset_right)

theorem varietyMetricChartMeasure_restrict_source (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) :
    (varietyMetricChartMeasure V e).restrict e.source = varietyMetricChartMeasure V e := by
  apply Measure.restrict_eq_self_of_ae_mem
  exact ae_iff.mpr (varietyMetricChartMeasure_compl_source V e)

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.MetricChartMeasure.CM.Construction
