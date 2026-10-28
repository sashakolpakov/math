import OAI.AlgebraicGeometry.HilbertScheme.Presentations.NormalizedHilbert.OpenOverlap

/-! # Intersections -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.NormalizedHilbert.Intersections.GradedHilbert

noncomputable section

/-! The open chart overlaps are exactly the fiber products inside the actual
Grassmannian parameter scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι] {n N : ℕ}
variable (a b : ι → Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N) (S : Scheme.{u}) (q : ℕ → ℕ)

theorem normalizedHilbertOpenOverlap_parameter :
    OpenOverlap.GradedHilbert.normalizedHilbertOpenOverlapInclusion a b S q ≫ OpenOverlap.GradedHilbert.normalizedHilbertChartParameter a S q =
      OpenOverlap.GradedHilbert.normalizedHilbertOpenOverlapToSecond a b S q ≫ OpenOverlap.GradedHilbert.normalizedHilbertChartParameter b S q := by
  dsimp only [OpenOverlap.GradedHilbert.normalizedHilbertChartParameter]
  rw [← Category.assoc, OpenOverlap.GradedHilbert.normalizedHilbertOpenOverlap_condition, Category.assoc,
    (OpenOverlap.GradedHilbert.normalizedGrassmannianOverlap_isPullback_over a b S).w]
  have he := congrArg (fun k => k ≫ Grassmannian.Gluing.grassmannianChartOverMap b S)
    (OpenOverlap.GradedHilbert.normalizedHilbertOpenOverlapToSecond_inclusion a b S q)
  simpa only [Category.assoc] using he.symm

theorem normalizedHilbertOpenOverlap_isPullback :
    IsPullback (OpenOverlap.GradedHilbert.normalizedHilbertOpenOverlapInclusion a b S q)
      (OpenOverlap.GradedHilbert.normalizedHilbertOpenOverlapToSecond a b S q)
      (OpenOverlap.GradedHilbert.normalizedHilbertChartParameter a S q) (OpenOverlap.GradedHilbert.normalizedHilbertChartParameter b S q) := by
  have : Mono (OpenOverlap.GradedHilbert.normalizedHilbertOpenOverlapInclusion a b S q) := Over.mono_of_mono_left _
  apply IsPullback.mk'
  · exact normalizedHilbertOpenOverlap_parameter a b S q
  · intro T f g h _
    exact (cancel_mono (OpenOverlap.GradedHilbert.normalizedHilbertOpenOverlapInclusion a b S q)).mp h
  · intro T f g h
    let hp := OpenOverlap.GradedHilbert.normalizedGrassmannianOverlap_isPullback_over a b S
    have hc : (f ≫ Chart.GradedHilbert.normalizedHilbertChartInclusion a S q) ≫ Grassmannian.Gluing.grassmannianChartOverMap a S =
        (g ≫ Chart.GradedHilbert.normalizedHilbertChartInclusion b S q) ≫ Grassmannian.Gluing.grassmannianChartOverMap b S := by
      simpa only [OpenOverlap.GradedHilbert.normalizedHilbertChartParameter, Category.assoc] using h
    let z := hp.lift (f ≫ Chart.GradedHilbert.normalizedHilbertChartInclusion a S q)
      (g ≫ Chart.GradedHilbert.normalizedHilbertChartInclusion b S q) hc
    have hz : z ≫ Normalized.Overlap.Grassmannian.normalizedOverlapInclusion a b S = f ≫ Chart.GradedHilbert.normalizedHilbertChartInclusion a S q :=
      hp.lift_fst _ _ hc
    let y : T ⟶ OpenOverlap.GradedHilbert.normalizedHilbertOpenOverlap a b S q := pullback.lift f z hz.symm
    have hy : y ≫ OpenOverlap.GradedHilbert.normalizedHilbertOpenOverlapInclusion a b S q = f := pullback.lift_fst _ _ _
    refine ⟨y, hy, ?_⟩
    apply (cancel_mono (OpenOverlap.GradedHilbert.normalizedHilbertChartParameter b S q)).mp
    rw [Category.assoc, ← normalizedHilbertOpenOverlap_parameter, ← Category.assoc, hy]
    exact h

instance normalizedHilbertIntersection_fst_isOpenImmersion :
    IsOpenImmersion (pullback.fst (OpenOverlap.GradedHilbert.normalizedHilbertChartParameter a S q)
      (OpenOverlap.GradedHilbert.normalizedHilbertChartParameter b S q)).left := by
  let hp := normalizedHilbertOpenOverlap_isPullback a b S q
  have he := congrArg Over.Hom.left hp.isoPullback_inv_fst
  have : IsIso hp.isoPullback.inv.left :=
    inferInstanceAs (IsIso ((Over.forget S).map hp.isoPullback.inv))
  have hi : IsOpenImmersion (hp.isoPullback.inv.left ≫
      (OpenOverlap.GradedHilbert.normalizedHilbertOpenOverlapInclusion a b S q).left) := inferInstance
  change hp.isoPullback.inv.left ≫ (OpenOverlap.GradedHilbert.normalizedHilbertOpenOverlapInclusion a b S q).left = _ at he
  rw [he] at hi
  exact hi

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.NormalizedHilbert.Intersections.GradedHilbert
