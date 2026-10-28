import OAI.AlgebraicGeometry.HilbertScheme.Presentations.BoundedHilbert.ChartPullback
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Local.RingPointOpenLift

/-! # Local Chart Lift -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.BoundedHilbert.LocalChartLift.GradedHilbert

noncomputable section

/-! Every point over a local test ring of the actual bounded Hilbert
scheme lifts to one normalized chart over the original base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι] {n N : ℕ}
variable {S : Scheme.{u}} {R : Type u} [CommRing R] [IsLocalRing R]

theorem boundedHilbert_local_chart_lift (q : ℕ → ℕ) (f : Spec (.of R) ⟶ S)
    (x : Over.mk f ⟶ Data.GradedHilbert.boundedHilbertOver (ι := ι) n N S q) :
    ∃ a : ι → Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N, ∃ y : Over.mk f ⟶ NormalizedHilbert.Chart.GradedHilbert.normalizedHilbertChart a S q,
      y ≫ ChartPullback.GradedHilbert.boundedHilbertChartOverMap a S q = x := by
  let C := (Data.GradedHilbert.boundedHilbertGlueData (ι := ι) n N S q).openCover
  obtain ⟨a, b, hb⟩ := Local.RingPointOpenLift.localRingPoint_lift_openCover C x.left
  change ι → Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N at a
  change Spec (.of R) ⟶ (NormalizedHilbert.Chart.GradedHilbert.normalizedHilbertChart a S q).left at b
  change b ≫ (ChartPullback.GradedHilbert.boundedHilbertChartOverMap a S q).left = x.left at hb
  have hbase : b ≫ (NormalizedHilbert.Chart.GradedHilbert.normalizedHilbertChart a S q).hom = f := by
    rw [← (ChartPullback.GradedHilbert.boundedHilbertChartOverMap a S q).w, ← Category.assoc, hb]
    exact x.w
  exact ⟨a, Over.homMk b hbase, Over.OverMorphism.ext hb⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.BoundedHilbert.LocalChartLift.GradedHilbert
