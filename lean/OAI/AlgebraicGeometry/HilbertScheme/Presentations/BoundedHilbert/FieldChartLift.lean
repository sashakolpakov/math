import OAI.AlgebraicGeometry.HilbertScheme.Presentations.BoundedHilbert.ChartPullback
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.FieldPointOpenLift

/-! # Field Chart Lift -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.BoundedHilbert.FieldChartLift.GradedHilbert

noncomputable section

/-! Every field-valued point of the actual bounded Hilbert scheme lifts
to a normalized chart as a morphism over the original base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι] {n N : ℕ}
variable {S : Scheme.{u}} {K : Type u} [Field K]

theorem boundedHilbert_field_chart_lift (q : ℕ → ℕ) (f : Spec (.of K) ⟶ S)
    (x : Over.mk f ⟶ Data.GradedHilbert.boundedHilbertOver (ι := ι) n N S q) :
    ∃ a : ι → Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N, ∃ y : Over.mk f ⟶ NormalizedHilbert.Chart.GradedHilbert.normalizedHilbertChart a S q,
      y ≫ ChartPullback.GradedHilbert.boundedHilbertChartOverMap a S q = x := by
  let C := (Data.GradedHilbert.boundedHilbertGlueData (ι := ι) n N S q).openCover
  obtain ⟨a, b, hb⟩ := FieldPointOpenLift.fieldPoint_lift_openCover C x.left
  change ι → Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N at a
  change Spec (.of K) ⟶ (NormalizedHilbert.Chart.GradedHilbert.normalizedHilbertChart a S q).left at b
  change b ≫ (ChartPullback.GradedHilbert.boundedHilbertChartOverMap a S q).left = x.left at hb
  have hbase : b ≫ (NormalizedHilbert.Chart.GradedHilbert.normalizedHilbertChart a S q).hom = f := by
    rw [← (ChartPullback.GradedHilbert.boundedHilbertChartOverMap a S q).w, ← Category.assoc, hb]
    exact x.w
  exact ⟨a, Over.homMk b hbase, Over.OverMorphism.ext hb⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.BoundedHilbert.FieldChartLift.GradedHilbert
