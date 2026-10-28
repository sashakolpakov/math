import OAI.Geometry.Riemannian.LocalNull
import OAI.Geometry.Nikodym.Abstract.Volume

noncomputable section
open Set _root_.MeasureTheory Manifold Bundle
open scoped ContDiff

namespace OAI.Geometry.Nikodym

variable {n : ℕ}

/-- The genuine metric determinant density assigns zero mass to every
Lebesgue-null coordinate set. No boundedness of the density is needed. -/
theorem SmoothCoordinateMetric.coordinateVolume_null_of_volume_null
    (g : SmoothCoordinateMetric (EuclideanSpace ℝ (Fin n)))
    {S : Set (EuclideanSpace ℝ (Fin n))} (hS : volume S = 0) :
    g.coordinateVolume S = 0 := by
  exact (withDensity_absolutelyContinuous _ _)
    (Measure.absolutelyContinuous_restrict hS)

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [MeasurableSpace M] [BorelSpace M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞
    (EuclideanSpace ℝ (Fin n))
    (fun x : M => TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) x)]

/-- Local coordinate nullness implies nullness for the actual Riemannian volume
on any fixed atlas chart, even when its closure is not compact. -/
theorem atlasRiemannianVolume_null_of_locally_chart_null
    (p : M) {S : Set M} (hS : MeasurableSet S)
    (hloc : ∀ x ∈ S, ∃ q : M, ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
      U ⊆ (extChartAt 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) q).source ∧
      volume (extChartAt 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) q '' (S ∩ U)) = 0) :
    atlasRiemannianVolume (n:=n) p S = 0 := by
  let K := (extChartAt 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) p).source
  have hK : MeasurableSet K := (isOpen_extChartAt_source p).measurableSet
  have hnull := OAI.Geometry.Riemannian.chart_image_null_of_locally_chart_null volume p S hloc
  have himage : atlasForward (E:=EuclideanSpace ℝ (Fin n)) p '' (S ∩ K) =
      extChartAt 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) p '' (S ∩ K) := by
    apply image_congr
    intro x hx
    exact atlasForward_eq p hx.2
  have hzero : atlasRiemannianVolume (n:=n) p (S ∩ K) = 0 := by
    rw [atlasRiemannianVolume_eq_coordinateVolume_image p (hS.inter hK)
      inter_subset_right, himage]
    exact OAI.Geometry.Nikodym.SmoothCoordinateMetric.coordinateVolume_null_of_volume_null _ hnull
  rw [← atlasRiemannianVolume_restrict_source (n:=n) p,
    Measure.restrict_apply hS]
  exact hzero

theorem atlasRiemannianVolume_null_of_locally_centered_chart_null
    (p : M) {S : Set M} (hS : MeasurableSet S)
    (hloc : ∀ x ∈ S, ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
      U ⊆ (extChartAt 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) x).source ∧
      volume (extChartAt 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) x '' (S ∩ U)) = 0) :
    atlasRiemannianVolume (n:=n) p S = 0 := by
  apply atlasRiemannianVolume_null_of_locally_chart_null p hS
  intro x hx
  obtain ⟨U, hU⟩ := hloc x hx
  exact ⟨x, U, hU⟩

end OAI.Geometry.Nikodym
