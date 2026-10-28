import OAI.Geometry.Nikodym.Riemannian.Coordinates
import OAI.Geometry.Nikodym.Riemannian.Volume
import Mathlib.MeasureTheory.Measure.Comap

noncomputable section
namespace OAI.Geometry.Nikodym.IntrinsicDomain

open Set _root_.MeasureTheory
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

instance intrinsicMeasurableSpace (g : SmoothCoordinateMetric E) :
    MeasurableSpace (IntrinsicDomain g) := borel (IntrinsicDomain g)

instance intrinsicBorelSpace (g : SmoothCoordinateMetric E) :
    BorelSpace (IntrinsicDomain g) := ⟨rfl⟩

omit [FiniteDimensional ℝ E] in
theorem range_coordinate (g : SmoothCoordinateMetric E) :
    Set.range (IntrinsicDomain.coordinate g) = g.domain := by
  ext x
  constructor
  · rintro ⟨y,rfl⟩
    exact IntrinsicDomain.coordinate_mem g y
  · intro hx
    exact ⟨IntrinsicDomain.ofCoordinate g ⟨x,hx⟩,rfl⟩

omit [FiniteDimensional ℝ E] in
theorem measurableEmbedding_coordinate [MeasurableSpace E] [BorelSpace E]
    (g : SmoothCoordinateMetric E) : MeasurableEmbedding (IntrinsicDomain.coordinate g) := by
  have hi : Topology.IsEmbedding (IntrinsicDomain.coordinate g) := Topology.IsEmbedding.subtypeVal
  exact hi.measurableEmbedding (by rw [IntrinsicDomain.range_coordinate]; exact g.isOpen_domain.measurableSet)

variable {n : ℕ}

/-- The actual Riemannian volume on the intrinsic metric carrier: the
pullback of the coordinate density, not Euclidean volume on that carrier. -/
def intrinsicVolume (g : SmoothCoordinateMetric (EuclideanSpace ℝ (Fin n))) :
    Measure (IntrinsicDomain g) := g.coordinateVolume.comap (IntrinsicDomain.coordinate g)

theorem coordinateVolume_restrict_domain
    (g : SmoothCoordinateMetric (EuclideanSpace ℝ (Fin n))) :
    g.coordinateVolume.restrict g.domain = g.coordinateVolume := by
  unfold OAI.Geometry.Nikodym.SmoothCoordinateMetric.coordinateVolume
  rw [restrict_withDensity g.isOpen_domain.measurableSet,
    Measure.restrict_restrict g.isOpen_domain.measurableSet,inter_self]

/-- Exact coordinate change for the intrinsic Riemannian volume. -/
theorem map_intrinsicVolume
    (g : SmoothCoordinateMetric (EuclideanSpace ℝ (Fin n))) :
    Measure.map (IntrinsicDomain.coordinate g) (IntrinsicDomain.intrinsicVolume g) = g.coordinateVolume := by
  have hm := IntrinsicDomain.measurableEmbedding_coordinate g
  have he : Measure.map (IntrinsicDomain.coordinate g) (IntrinsicDomain.intrinsicVolume g) =
      g.coordinateVolume.restrict g.domain := by
    ext s hs
    rw [Measure.map_apply hm.measurable hs,IntrinsicDomain.intrinsicVolume,
      Measure.comap_preimage _ _ hm.injective hm.measurable
        (fun t ht => (hm.measurableSet_image.mpr ht).nullMeasurableSet) hs,
      IntrinsicDomain.range_coordinate,Measure.restrict_apply hs]
  rw [he,IntrinsicDomain.coordinateVolume_restrict_domain]

theorem intrinsicVolume_apply
    (g : SmoothCoordinateMetric (EuclideanSpace ℝ (Fin n)))
    {S : Set (IntrinsicDomain g)} (hS : MeasurableSet S) :
    IntrinsicDomain.intrinsicVolume g S = g.coordinateVolume (IntrinsicDomain.coordinate g '' S) := by
  have hm := IntrinsicDomain.measurableEmbedding_coordinate g
  exact Measure.comap_apply _ hm.injective
    (fun t ht => hm.measurableSet_image.mpr ht) _ hS

end OAI.Geometry.Nikodym.IntrinsicDomain
