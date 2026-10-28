import OAI.Geometry.Riemannian.NikodymRiemannianLevelHoles
import OAI.Geometry.Nikodym.CoordinateLevelMeasurable
import OAI.Geometry.Nikodym.Porosity
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

noncomputable section
open Set Metric Filter _root_.MeasureTheory Bundle Manifold
open scoped Topology ENNReal

namespace OAI.Geometry.Riemannian

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {M : Type*} [PseudoMetricSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ,E) x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace 𝓘(ℝ,E) x)]
  [IsRiemannianManifold 𝓘(ℝ,E) M]

/-- Positive levels of distance to any nonempty set are null in local
coordinates. The distance is the ambient Riemannian distance, not the
distance intrinsic to the coordinate patch. -/
theorem exists_distance_level_coordinate_null
    (μ : Measure E) [IsUnifLocDoublingMeasure μ] [IsLocallyFiniteMeasure μ]
    (a : M) {A : Set M} (hA : A.Nonempty) {δ : ℝ} (hδ : 0 < δ) :
    ∃ U : Set M, IsOpen U ∧ a ∈ U ∧ U ⊆ (extChartAt 𝓘(ℝ,E) a).source ∧
      μ ((extChartAt 𝓘(ℝ,E) a) '' ({z | infDist z A = δ} ∩ U)) = 0 := by
  obtain ⟨U,hU,ha,hUs,C,hC,hholes⟩ :=
    exists_distance_level_coordinate_holes (E := E) a hA hδ
  refine ⟨U,hU,ha,hUs,?_⟩
  apply OAI.Geometry.Nikodym.measure_eq_zero_of_small_holes μ _ C hholes
  have hm := OAI.Geometry.Nikodym.measurableSet_coordinate_distance_level
    (chartAt E a) hU (by simpa only [extChartAt_source] using hUs) A δ
  simpa only [extChartAt_coe,modelWithCornersSelf_coe,Function.id_comp] using hm

theorem exists_distance_level_coordinate_haar_null
    [FiniteDimensional ℝ E] (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    (a : M) {A : Set M} (hA : A.Nonempty) {δ : ℝ} (hδ : 0 < δ) :
    ∃ U : Set M, IsOpen U ∧ a ∈ U ∧ U ⊆ (extChartAt 𝓘(ℝ,E) a).source ∧
      μ ((extChartAt 𝓘(ℝ,E) a) '' ({z | infDist z A = δ} ∩ U)) = 0 :=
  exists_distance_level_coordinate_null μ a hA hδ

end OAI.Geometry.Riemannian
