import OAI.Analysis.HodgeTheory.Decomposition.MetricCoefficients
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.MetricIntegration
import Mathlib.MeasureTheory.Measure.WithDensity

/-! # Measure Volume -/

namespace OAI.Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions

noncomputable section

section

/-! Local volume measures derived from the actual projective metric density.
These are the chart measures to be glued for the global L² construction. -/

open scoped _root_.Manifold ENNReal
open _root_.MeasureTheory Set

open OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.MetricIntegration.CM.Construction

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  [MeasurableSpace V.analyticSpace] [BorelSpace V.analyticSpace]
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace)

def chartMetricDensityMeasure : Measure (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) :=
  (volume.restrict (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)).withDensity
    (fun z => ENNReal.ofReal (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Metric.CM.Construction.varietyMetricDensity V e z))

def chartCoordinateInverse (z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) : V.analyticSpace :=
  e.symm (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z)

omit [MeasurableSpace V.analyticSpace] [BorelSpace V.analyticSpace] in
theorem chartCoordinateInverse_continuousOn :
    ContinuousOn (chartCoordinateInverse V e) (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :=
  e.continuousOn_symm.comp (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).continuous.continuousOn
    (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates_mapsTo V e)

theorem chartCoordinateInverse_aemeasurable :
    AEMeasurable (chartCoordinateInverse V e) (chartMetricDensityMeasure V e) :=
  ((chartCoordinateInverse_continuousOn V e).aemeasurable
    (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen.measurableSet).mono_ac
      (withDensity_absolutelyContinuous _ _)

/-- The projective metric's local volume, pushed onto the actual chart source. -/
def projectiveChartMeasure : Measure V.analyticSpace :=
  (chartMetricDensityMeasure V e).map (chartCoordinateInverse V e)

include he

omit [MeasurableSpace V.analyticSpace] [BorelSpace V.analyticSpace] in
theorem chartMetricDensity_aemeasurable :
    AEMeasurable (fun z => ENNReal.ofReal (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Metric.CM.Construction.varietyMetricDensity V e z))
      (volume.restrict (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)) :=
  ((ENNReal.continuous_ofReal.comp_continuousOn
    (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Metric.CM.Construction.varietyMetricDensity_smooth V e he).continuousOn).aemeasurable
      (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen.measurableSet)

/-- Integrating in the local volume is exactly integration against the constructed metric density. -/
theorem projectiveChartMeasure_lintegral (h : V.analyticSpace → ℝ≥0∞) (hh : Measurable h) :
    (∫⁻ x, h x ∂ projectiveChartMeasure V e) =
      ∫⁻ z in AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e,
        ENNReal.ofReal (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Metric.CM.Construction.varietyMetricDensity V e z) * h (e.symm (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z)) := by
  rw [projectiveChartMeasure, lintegral_map' hh.aemeasurable (chartCoordinateInverse_aemeasurable V e)]
  exact lintegral_withDensity_eq_lintegral_mul₀' (chartMetricDensity_aemeasurable V e he)
    (hh.comp_aemeasurable (chartCoordinateInverse_aemeasurable V e))

omit he in
/-- The chart measure has no mass outside its genuine chart source. -/
theorem projectiveChartMeasure_compl_source : projectiveChartMeasure V e e.sourceᶜ = 0 := by
  rw [projectiveChartMeasure, Measure.map_apply_of_aemeasurable
    (chartCoordinateInverse_aemeasurable V e) e.open_source.measurableSet.compl]
  apply withDensity_absolutelyContinuous
  apply (Measure.restrict_apply_eq_zero' (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen.measurableSet).mpr
  have hdis : (chartCoordinateInverse V e ⁻¹' e.sourceᶜ) ∩ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e : Set _) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro z hz
    exact hz.1 (e.map_target hz.2)
  rw [hdis]
  exact measure_empty

end

section

/-! Compatibility of the actual metric volume measures on overlapping charts. -/

open scoped _root_.Manifold ENNReal
open _root_.MeasureTheory Set

open OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.MetricIntegration.CM.Construction

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  [MeasurableSpace V.analyticSpace] [BorelSpace V.analyticSpace]

def chartCoordinateForward (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (x : V.analyticSpace) : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V :=
  (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).symm (e x)

omit [MeasurableSpace V.analyticSpace] [BorelSpace V.analyticSpace] in
theorem chartCoordinateForward_mem (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (x : V.analyticSpace) (hx : x ∈ e.source) :
    chartCoordinateForward V e x ∈ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e := by
  change AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V ((AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).symm (e x)) ∈ e.target
  rw [ContinuousLinearEquiv.apply_symm_apply]
  exact e.map_source hx

omit [MeasurableSpace V.analyticSpace] [BorelSpace V.analyticSpace] in
theorem chartCoordinateInverse_forward (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (x : V.analyticSpace) (hx : x ∈ e.source) :
    chartCoordinateInverse V e (chartCoordinateForward V e x) = x := by
  simp only [chartCoordinateInverse, chartCoordinateForward, ContinuousLinearEquiv.apply_symm_apply,
    e.left_inv hx]

omit [MeasurableSpace V.analyticSpace] [BorelSpace V.analyticSpace] in
theorem chartCoordinateForward_inverse (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) (hz : z ∈ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    chartCoordinateForward V e (chartCoordinateInverse V e z) = z := by
  simp only [chartCoordinateForward, chartCoordinateInverse, e.right_inv hz,
    ContinuousLinearEquiv.symm_apply_apply]

def chartCoordinateSet (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (s : Set V.analyticSpace) : Set (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) :=
  (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e : Set _) ∩ chartCoordinateInverse V e ⁻¹' s

theorem chartCoordinateSet_measurable (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    {s : Set V.analyticSpace} (hs : MeasurableSet s) : MeasurableSet (chartCoordinateSet V e s) := by
  have hc : Continuous (fun z : (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e : Set (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) =>
      chartCoordinateInverse V e z.val) :=
    continuousOn_iff_continuous_domRestrict.mp (chartCoordinateInverse_continuousOn V e)
  have hm := (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen.measurableSet.subtype_image (hc.measurable hs)
  convert hm using 1
  ext z
  simp [chartCoordinateSet, and_comm]

/-- The local volume of a measurable set equals its coordinate density integral. -/
theorem projectiveChartMeasure_apply (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace) {s : Set V.analyticSpace} (hs : MeasurableSet s) :
    projectiveChartMeasure V e s =
      ∫⁻ z in chartCoordinateSet V e s, ENNReal.ofReal (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Metric.CM.Construction.varietyMetricDensity V e z) := by
  classical
  have h := projectiveChartMeasure_lintegral V e he (s.indicator (fun _ => 1))
    (measurable_const.indicator hs)
  rw [lintegral_indicator_const hs, one_mul] at h
  rw [h]
  calc
    (∫⁻ z in AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e,
        ENNReal.ofReal (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Metric.CM.Construction.varietyMetricDensity V e z) *
          s.indicator (fun _ => 1) (e.symm (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z))) =
      ∫⁻ z in AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e,
        (chartCoordinateSet V e s).indicator (fun w => ENNReal.ofReal (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Metric.CM.Construction.varietyMetricDensity V e w)) z := by
      apply setLIntegral_congr_fun (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen.measurableSet
      intro z hz
      change ENNReal.ofReal (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Metric.CM.Construction.varietyMetricDensity V e z) *
        s.indicator (fun _ => 1) (chartCoordinateInverse V e z) = _
      by_cases hzs : chartCoordinateInverse V e z ∈ s
      · have hS : z ∈ chartCoordinateSet V e s := ⟨hz, hzs⟩
        rw [Set.indicator_of_mem hzs, Set.indicator_of_mem hS, mul_one]
      · have hS : z ∉ chartCoordinateSet V e s := fun h => hzs h.2
        rw [Set.indicator_of_notMem hzs, Set.indicator_of_notMem hS, mul_zero]
    _ = _ := by
      rw [setLIntegral_indicator (chartCoordinateSet_measurable V e hs),
        inter_eq_left.mpr (show chartCoordinateSet V e s ⊆ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e from fun _ hz => hz.1)]

omit [MeasurableSpace V.analyticSpace] [BorelSpace V.analyticSpace] in
theorem chartCoordinateSet_transition (e f : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    {s : Set V.analyticSpace} (hse : s ⊆ e.source) (hsf : s ⊆ f.source) :
    AlgebraicGeometry.ComplexMultiplication.HodgeComparison.MetricJacobian.CM.Construction.varietyEuclideanTransition V e f '' chartCoordinateSet V e s = chartCoordinateSet V f s := by
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hfx : chartCoordinateInverse V e z ∈ f.source := hsf hz.2
    change chartCoordinateForward V f (chartCoordinateInverse V e z) ∈ chartCoordinateSet V f s
    exact ⟨chartCoordinateForward_mem V f _ hfx, by
      change chartCoordinateInverse V f (chartCoordinateForward V f (chartCoordinateInverse V e z)) ∈ s
      rw [chartCoordinateInverse_forward V f _ hfx]
      exact hz.2⟩
  · intro hw
    let x := chartCoordinateInverse V f w
    have hxe : x ∈ e.source := hse hw.2
    refine ⟨chartCoordinateForward V e x, ⟨chartCoordinateForward_mem V e x hxe, ?_⟩, ?_⟩
    · change chartCoordinateInverse V e (chartCoordinateForward V e x) ∈ s
      rw [chartCoordinateInverse_forward V e x hxe]
      exact hw.2
    · change chartCoordinateForward V f (chartCoordinateInverse V e (chartCoordinateForward V e x)) = w
      rw [chartCoordinateInverse_forward V e x hxe]
      exact chartCoordinateForward_inverse V f w hw.1

/-- The local metric measures agree on every measurable set contained in an overlap. -/
theorem projectiveChartMeasure_overlap (e f : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (hf : f ∈ atlas V.analyticModel V.analyticSpace)
    {s : Set V.analyticSpace} (hs : MeasurableSet s) (hse : s ⊆ e.source) (hsf : s ⊆ f.source) :
    projectiveChartMeasure V e s = projectiveChartMeasure V f s := by
  rw [projectiveChartMeasure_apply V e he hs, projectiveChartMeasure_apply V f hf hs,
    ← chartCoordinateSet_transition V e f hse hsf]
  have h := AlgebraicGeometry.ComplexMultiplication.HodgeComparison.MetricIntegration.CM.Construction.varietyMetric_lintegral_transition V e f he hf (chartCoordinateSet_measurable V e hs)
    (fun _ hz => hz.1) (fun _ hz => hsf hz.2) (fun _ => 1)
  simpa only [mul_one] using h.symm

end

section

/-! Gluing compatible local measures along a countable measurable cover.
This is used with a finite chart cover of the projective manifold. -/

open _root_.MeasureTheory Set

variable {M ι : Type*} [MeasurableSpace M] [Countable ι] [LinearOrder ι]
  [LocallyFiniteOrderBot ι]

theorem disjointed_measurable (U : ι → Set M) (hU : ∀ i, MeasurableSet (U i)) (i : ι) :
    MeasurableSet (disjointed U i) := by
  rw [disjointed_eq_inter_compl]
  exact (hU i).inter (MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ => (hU j).compl)

def glueLocalMeasures (U : ι → Set M) (μ : ι → Measure M) : Measure M :=
  Measure.sum (fun i => (μ i).restrict (disjointed U i))

/-- Compatible chart measures glue to a measure with exactly those local restrictions. -/
theorem glueLocalMeasures_restrict_of_compatible (U : ι → Set M) (hU : ∀ i, MeasurableSet (U i))
    (hcover : (⋃ i, U i) = univ) (μ : ι → Measure M)
    (W : Set M) (hW : MeasurableSet W) (ν : Measure M)
    (hcompat : ∀ i, ∀ s : Set M, MeasurableSet s → s ⊆ U i → s ⊆ W → μ i s = ν s) :
    (glueLocalMeasures U μ).restrict W = ν.restrict W := by
  have hpiece (i : ι) : ((μ i).restrict (disjointed U i)).restrict W =
      (ν.restrict (disjointed U i)).restrict W := by
    ext s hs
    rw [Measure.restrict_apply hs, Measure.restrict_apply (hs.inter hW),
      Measure.restrict_apply hs, Measure.restrict_apply (hs.inter hW)]
    exact hcompat i _ ((hs.inter hW).inter (disjointed_measurable U hU i))
      (fun _ hx => disjointed_subset U i hx.2) (fun _ hx => hx.1.2)
  calc
    (glueLocalMeasures U μ).restrict W =
        Measure.sum (fun i => ((μ i).restrict (disjointed U i)).restrict W) :=
      Measure.restrict_sum _ hW
    _ = Measure.sum (fun i => (ν.restrict (disjointed U i)).restrict W) :=
      congrArg Measure.sum (funext hpiece)
    _ = (Measure.sum (fun i => ν.restrict (disjointed U i))).restrict W :=
      (Measure.restrict_sum _ hW).symm
    _ = (ν.restrict (⋃ i, disjointed U i)).restrict W := by
      rw [Measure.restrict_iUnion (disjoint_disjointed U) (disjointed_measurable U hU)]
    _ = ν.restrict W := by
      rw [iUnion_disjointed, hcover, Measure.restrict_univ]

theorem glueLocalMeasures_restrict (U : ι → Set M) (hU : ∀ i, MeasurableSet (U i))
    (hcover : (⋃ i, U i) = univ) (μ : ι → Measure M)
    (hcompat : ∀ i j, ∀ s : Set M, MeasurableSet s → s ⊆ U i → s ⊆ U j → μ i s = μ j s)
    (k : ι) : (glueLocalMeasures U μ).restrict (U k) = (μ k).restrict (U k) :=
  glueLocalMeasures_restrict_of_compatible U hU hcover μ (U k) (hU k) (μ k)
    (fun i => hcompat i k)

/-- The local restrictions uniquely determine the glued measure. -/
theorem glueLocalMeasures_unique (U : ι → Set M) (hU : ∀ i, MeasurableSet (U i))
    (hcover : (⋃ i, U i) = univ) (μ : ι → Measure M)
    (hcompat : ∀ i j, ∀ s : Set M, MeasurableSet s → s ⊆ U i → s ⊆ U j → μ i s = μ j s)
    (ν : Measure M) (hν : ∀ i, ν.restrict (U i) = (μ i).restrict (U i)) :
    ν = glueLocalMeasures U μ := by
  have hres : ν.restrict (⋃ i, U i) = (glueLocalMeasures U μ).restrict (⋃ i, U i) := by
    apply Measure.restrict_iUnion_congr.mpr
    intro i
    exact (hν i).trans (glueLocalMeasures_restrict U hU hcover μ hcompat i).symm
  simpa only [hcover, Measure.restrict_univ] using hres

end

section

/-! The actual global projective metric volume, glued from its compatible
coordinate densities. No global solvability assumption is used. -/

open scoped _root_.Manifold Classical
open _root_.MeasureTheory Set

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)

theorem exists_projective_chart_cover :
    ∃ S : Finset V.analyticSpace, ∀ x : V.analyticSpace,
      ∃ y ∈ S, x ∈ (chartAt V.analyticModel y).source := by
  obtain ⟨S, hS⟩ := isCompact_univ.elim_finite_subcover
    (fun y : V.analyticSpace => (chartAt V.analyticModel y).source)
    (fun y => (chartAt V.analyticModel y).open_source) (by
      intro x _
      exact mem_iUnion.mpr ⟨x, mem_chart_source V.analyticModel x⟩)
  refine ⟨S, fun x => ?_⟩
  simpa only [mem_iUnion, exists_prop] using hS (mem_univ x)

def projectiveChartCoverPoints : Finset V.analyticSpace :=
  (exists_projective_chart_cover V).choose

abbrev ProjectiveChartIndex := Fin (Fintype.card (projectiveChartCoverPoints V))

def projectiveCoverChart (i : ProjectiveChartIndex V) :
    OpenPartialHomeomorph V.analyticSpace V.analyticModel :=
  chartAt V.analyticModel (((Fintype.equivFin (projectiveChartCoverPoints V)).symm i).val)

theorem projectiveCoverChart_mem_atlas (i : ProjectiveChartIndex V) :
    projectiveCoverChart V i ∈ atlas V.analyticModel V.analyticSpace :=
  chart_mem_atlas V.analyticModel _

theorem projectiveCoverChart_covers (x : V.analyticSpace) :
    ∃ i : ProjectiveChartIndex V, x ∈ (projectiveCoverChart V i).source := by
  obtain ⟨y, hy, hx⟩ := (exists_projective_chart_cover V).choose_spec x
  refine ⟨Fintype.equivFin (projectiveChartCoverPoints V) ⟨y, hy⟩, ?_⟩
  simpa only [projectiveCoverChart, Equiv.symm_apply_apply] using hx

theorem projectiveCoverChart_iUnion : (⋃ i : ProjectiveChartIndex V, (projectiveCoverChart V i).source) = univ := by
  apply Set.eq_univ_of_forall
  intro x
  exact mem_iUnion.mpr (projectiveCoverChart_covers V x)

variable [MeasurableSpace V.analyticSpace] [BorelSpace V.analyticSpace]

/-- Riemannian volume of the genuine projective Kähler metric. -/
def projectiveMetricVolume : Measure V.analyticSpace :=
  glueLocalMeasures (fun i : ProjectiveChartIndex V => (projectiveCoverChart V i).source)
    (fun i => projectiveChartMeasure V (projectiveCoverChart V i))

/-- Every chart, including those outside the selected cover, has its original metric density. -/
theorem projectiveMetricVolume_restrict
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace) :
    (projectiveMetricVolume V).restrict e.source = (projectiveChartMeasure V e).restrict e.source := by
  apply glueLocalMeasures_restrict_of_compatible
    (fun i : ProjectiveChartIndex V => (projectiveCoverChart V i).source)
    (fun i => (projectiveCoverChart V i).open_source.measurableSet) (projectiveCoverChart_iUnion V)
    (fun i => projectiveChartMeasure V (projectiveCoverChart V i)) e.source e.open_source.measurableSet
  intro i s hs hsi hse
  exact projectiveChartMeasure_overlap V (projectiveCoverChart V i) e
    (projectiveCoverChart_mem_atlas V i) he hs hsi hse

theorem projectiveMetricVolume_apply_chart
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace) {s : Set V.analyticSpace}
    (hs : MeasurableSet s) (hse : s ⊆ e.source) :
    projectiveMetricVolume V s = projectiveChartMeasure V e s := by
  have h := congrArg (fun μ : Measure V.analyticSpace => μ s) (projectiveMetricVolume_restrict V e he)
  simpa only [Measure.restrict_apply hs, inter_eq_left.mpr hse] using h

/-- The local metric densities uniquely determine the global volume. -/
theorem projectiveMetricVolume_unique (ν : Measure V.analyticSpace)
    (hν : ∀ e ∈ atlas V.analyticModel V.analyticSpace,
      ν.restrict e.source = (projectiveChartMeasure V e).restrict e.source) :
    ν = projectiveMetricVolume V := by
  apply glueLocalMeasures_unique
    (fun i : ProjectiveChartIndex V => (projectiveCoverChart V i).source)
    (fun i => (projectiveCoverChart V i).open_source.measurableSet) (projectiveCoverChart_iUnion V)
    (fun i => projectiveChartMeasure V (projectiveCoverChart V i))
  · intro i j s hs hsi hsj
    exact projectiveChartMeasure_overlap V (projectiveCoverChart V i) (projectiveCoverChart V j)
      (projectiveCoverChart_mem_atlas V i) (projectiveCoverChart_mem_atlas V j) hs hsi hsj
  · intro i
    exact hν (projectiveCoverChart V i) (projectiveCoverChart_mem_atlas V i)

end

/-! Finiteness of the actual projective metric volume. Compact coordinate
balls have finite density integrals, giving local finiteness; compactness of
the genuine manifold then gives finite total volume. -/

open scoped _root_.Manifold ENNReal _root_.Topology
open _root_.MeasureTheory Set _root_.Metric

open OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.MetricIntegration.CM.Construction

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  [MeasurableSpace V.analyticSpace] [BorelSpace V.analyticSpace]

omit [MeasurableSpace V.analyticSpace] [BorelSpace V.analyticSpace] in
theorem chartCoordinateSet_image (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    {K : Set (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)} (hKU : K ⊆ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    chartCoordinateSet V e (chartCoordinateInverse V e '' K) = K := by
  ext z
  constructor
  · rintro ⟨hz, w, hw, h⟩
    have heq := congrArg (chartCoordinateForward V e) h
    rw [chartCoordinateForward_inverse V e w (hKU hw), chartCoordinateForward_inverse V e z hz] at heq
    exact heq ▸ hw
  · intro hz
    exact ⟨hKU hz, z, hz, rfl⟩

omit [MeasurableSpace V.analyticSpace] [BorelSpace V.analyticSpace] in
theorem compactMetricDensity_integral_lt_top
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    {K : Set (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)} (hK : IsCompact K) (hKU : K ⊆ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    (∫⁻ z in K, ENNReal.ofReal (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Metric.CM.Construction.varietyMetricDensity V e z)) < ⊤ := by
  have hc := (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Metric.CM.Construction.varietyMetricDensity_smooth V e he).continuousOn.mono hKU
  obtain ⟨C, hC⟩ := hK.bddAbove_image hc
  calc
    (∫⁻ z in K, ENNReal.ofReal (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Metric.CM.Construction.varietyMetricDensity V e z)) ≤ ∫⁻ _z in K, ENNReal.ofReal C :=
      setLIntegral_mono' hK.measurableSet (fun z hz => ENNReal.ofReal_le_ofReal (hC ⟨z, hz, rfl⟩))
    _ = ENNReal.ofReal C * volume K := by simp only [lintegral_const, Measure.restrict_apply_univ]
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK.measure_lt_top

theorem projectiveMetricVolume_compact_chart_image_lt_top
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    {K : Set (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)} (hK : IsCompact K) (hKU : K ⊆ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    projectiveMetricVolume V (chartCoordinateInverse V e '' K) < ⊤ := by
  have hS := hK.image_of_continuousOn ((chartCoordinateInverse_continuousOn V e).mono hKU)
  have hSe : chartCoordinateInverse V e '' K ⊆ e.source := by
    rintro _ ⟨z, hz, rfl⟩
    exact e.map_target (hKU hz)
  rw [projectiveMetricVolume_apply_chart V e he hS.measurableSet hSe,
    projectiveChartMeasure_apply V e he hS.measurableSet, chartCoordinateSet_image V e hKU]
  exact compactMetricDensity_integral_lt_top V e he hK hKU

/-- A small coordinate ball gives a finite-volume neighborhood of every actual manifold point. -/
instance projectiveMetricVolume_locallyFinite : IsLocallyFiniteMeasure (projectiveMetricVolume V) where
  finiteAtNhds x := by
    let e := chartAt V.analyticModel x
    have he := chart_mem_atlas V.analyticModel x
    have hx := mem_chart_source V.analyticModel x
    let z := chartCoordinateForward V e x
    have hz : z ∈ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e := chartCoordinateForward_mem V e x hx
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp ((AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen.mem_nhds hz)
    have hhalf : 0 < r / 2 := half_pos hr
    have hKU : closedBall z (r / 2) ⊆ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e :=
      (closedBall_subset_ball (by linarith : r / 2 < r)).trans hball
    let W : Set V.analyticSpace :=
      e.source ∩ e ⁻¹' ((AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).symm ⁻¹' ball z (r / 2))
    have hW : IsOpen W := e.isOpen_inter_preimage
      (isOpen_ball.preimage (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).symm.continuous)
    have hxW : x ∈ W := ⟨hx, mem_ball_self hhalf⟩
    refine ⟨W, hW.mem_nhds hxW, ?_⟩
    have hWS : W ⊆ chartCoordinateInverse V e '' closedBall z (r / 2) := by
      intro y hy
      refine ⟨chartCoordinateForward V e y, ?_, chartCoordinateInverse_forward V e y hy.1⟩
      exact ball_subset_closedBall hy.2
    exact (measure_mono hWS).trans_lt
      (projectiveMetricVolume_compact_chart_image_lt_top V e he (isCompact_closedBall z (r / 2)) hKU)

/-- The projective metric has finite total volume on the compact manifold. -/
instance projectiveMetricVolume_finite : IsFiniteMeasure (projectiveMetricVolume V) := inferInstance

end

end OAI.Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions
