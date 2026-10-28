import OAI.Geometry.Nikodym.Abstract.Volume
import OAI.Geometry.Nikodym.MetricMaximal
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.OpenPos

noncomputable section
open Set _root_.MeasureTheory Manifold Bundle
open scoped ContDiff ENNReal

namespace OAI.Geometry.Nikodym

theorem SmoothCoordinateMetric.volume_restrict_absolutelyContinuous_coordinateVolume
    {n : ℕ} (g : SmoothCoordinateMetric (EuclideanSpace ℝ (Fin n))) :
    volume.restrict g.domain ≪ g.coordinateVolume := by
  apply withDensity_absolutelyContinuous'
    (g.continuousOn_volumeDensity.aemeasurable g.isOpen_domain.measurableSet).ennreal_ofReal
  filter_upwards [ae_restrict_mem g.isOpen_domain.measurableSet] with x hx
  exact (ENNReal.ofReal_pos.mpr (g.volumeDensity_pos hx)).ne'

theorem SmoothCoordinateMetric.coordinateVolume_pos_of_isOpen
    {n : ℕ} (g : SmoothCoordinateMetric (EuclideanSpace ℝ (Fin n)))
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U) (hne : U.Nonempty)
    (hUD : U ⊆ g.domain) : 0 < g.coordinateVolume U := by
  apply pos_iff_ne_zero.mpr
  intro hz
  have hv := g.volume_restrict_absolutelyContinuous_coordinateVolume hz
  rw [Measure.restrict_apply hU.measurableSet,inter_eq_left.mpr hUD] at hv
  exact (hU.measure_pos volume hne).ne' hv

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [MeasurableSpace M] [BorelSpace M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞
    (EuclideanSpace ℝ (Fin n))
    (fun x : M => TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) x)]

/-- Every nonempty open part of the atlas source has positive genuine
Riemannian volume. -/
theorem atlasRiemannianVolume_pos_of_isOpen (p : M) {U : Set M}
    (hU : IsOpen U) (hne : U.Nonempty)
    (hUS : U ⊆ (extChartAt 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) p).source) :
    0 < atlasRiemannianVolume (n:=n) p U := by
  rw [atlasRiemannianVolume_eq_coordinateVolume_image p hU.measurableSet hUS]
  apply OAI.Geometry.Nikodym.SmoothCoordinateMetric.coordinateVolume_pos_of_isOpen
  · have he : atlasForward (E:=EuclideanSpace ℝ (Fin n)) p '' U =
        (chartAt (EuclideanSpace ℝ (Fin n)) p) '' U := by
      apply image_congr
      intro x hx
      exact atlasForward_eq p (hUS hx)
    rw [he]
    apply (chartAt (EuclideanSpace ℝ (Fin n)) p).isOpen_image_of_subset_source hU
    simpa only [extChartAt_source] using hUS
  · exact hne.image _
  · rintro y ⟨x,hx,rfl⟩
    exact atlasForward_mem p (hUS hx)

/-- A genuine metric tube meeting the open chart has a strictly positive
normalizing volume, including for a degenerate endpoint pair. -/
theorem atlasRiemannianVolume_metricTube_pos
    {n : ℕ} {M : Type*} [MetricSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [MeasurableSpace M] [BorelSpace M]
    [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) x)]
    [IsContMDiffRiemannianBundle 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞
      (EuclideanSpace ℝ (Fin n))
      (fun x : M => TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) x)]
    (p : M) {S J : Set M} (hS : IsOpen S)
    (hSS : S ⊆ (extChartAt 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) p).source)
    {δ : ℝ} (hδ : 0 < δ) (hmeet : (J ∩ S).Nonempty) :
    0 < (atlasRiemannianVolume (n:=n) p).restrict S (metricTube δ J) := by
  have hT : IsOpen (metricTube δ J) := by
    rw [metricTube_eq_thickening]
    exact Metric.isOpen_thickening
  rw [Measure.restrict_apply hT.measurableSet]
  apply atlasRiemannianVolume_pos_of_isOpen p (hT.inter hS)
  · obtain ⟨x,hxJ,hxS⟩ := hmeet
    exact ⟨x,⟨⟨x,hxJ,by simpa only [dist_self] using hδ⟩,hxS⟩⟩
  · exact inter_subset_right.trans hSS

end OAI.Geometry.Nikodym
