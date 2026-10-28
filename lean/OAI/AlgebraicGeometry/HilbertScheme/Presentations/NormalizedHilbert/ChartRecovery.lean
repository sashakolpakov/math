import OAI.AlgebraicGeometry.HilbertScheme.Presentations.NormalizedHilbert.Intersections

/-! # Chart Recovery -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.NormalizedHilbert.ChartRecovery.GradedHilbert

noncomputable section

/-! A point of one Hilbert chart lying in another Grassmannian chart
uniquely recovers a point of that Hilbert chart. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι] {n N : ℕ}
variable (a b : ι → Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N) (S : Scheme.{u}) (q : ℕ → ℕ)

theorem normalizedHilbertChart_recovery {T : Over S}
    (x : T ⟶ Normalized.Chart.Grassmannian.normalizedChart a S) (y : T ⟶ Chart.GradedHilbert.normalizedHilbertChart b S q)
    (h : x ≫ Grassmannian.Gluing.grassmannianChartOverMap a S = y ≫ OpenOverlap.GradedHilbert.normalizedHilbertChartParameter b S q) :
    ∃! z : T ⟶ Chart.GradedHilbert.normalizedHilbertChart a S q, z ≫ Chart.GradedHilbert.normalizedHilbertChartInclusion a S q = x := by
  let hp := OpenOverlap.GradedHilbert.normalizedGrassmannianOverlap_isPullback_over a b S
  have hc : x ≫ Grassmannian.Gluing.grassmannianChartOverMap a S =
      (y ≫ Chart.GradedHilbert.normalizedHilbertChartInclusion b S q) ≫ Grassmannian.Gluing.grassmannianChartOverMap b S := by
    simpa only [OpenOverlap.GradedHilbert.normalizedHilbertChartParameter, Category.assoc] using h
  let w := hp.lift x (y ≫ Chart.GradedHilbert.normalizedHilbertChartInclusion b S q) hc
  have hw₁ : w ≫ Normalized.Overlap.Grassmannian.normalizedOverlapInclusion a b S = x := hp.lift_fst _ _ hc
  have hw₂ : w ≫ (Normalized.Overlap.Grassmannian.normalizedOverlapTransition a b S).hom ≫ Normalized.Overlap.Grassmannian.normalizedOverlapInclusion b a S =
      y ≫ Chart.GradedHilbert.normalizedHilbertChartInclusion b S q := hp.lift_snd _ _ hc
  apply (Chart.GradedHilbert.normalizedHilbertChart_factorization_iff a S q x).mp
  rw [← hw₁]
  apply (OverlapCriterion.GradedHilbert.normalizedHilbertChart_overlap_mem_iff a b S q w).mpr
  rw [hw₂]
  exact (Chart.GradedHilbert.normalizedHilbertChartSubfunctor b S q).map y.op (Chart.GradedHilbert.normalizedHilbertChart_universal_mem b S q)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.NormalizedHilbert.ChartRecovery.GradedHilbert
