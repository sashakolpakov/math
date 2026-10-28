import OAI.AlgebraicGeometry.HilbertScheme.Presentations.NormalizedHilbert.OverlapCriterion

/-! # Open Overlap -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.NormalizedHilbert.OpenOverlap.GradedHilbert

noncomputable section

/-! Open overlaps of the constructed Hilbert charts, obtained by pulling
back the actual Grassmannian determinant opens. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι] {n N : ℕ}
variable (a b : ι → Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N) (S : Scheme.{u}) (q : ℕ → ℕ)

def normalizedHilbertChartParameter :
    Chart.GradedHilbert.normalizedHilbertChart a S q ⟶ Grassmannian.Gluing.grassmannianOver (ι := ι) (ν := Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N) S :=
  Chart.GradedHilbert.normalizedHilbertChartInclusion a S q ≫ Grassmannian.Gluing.grassmannianChartOverMap a S

instance normalizedHilbertChartParameter_mono : Mono (normalizedHilbertChartParameter a S q) := by
  have : Mono (Grassmannian.Gluing.grassmannianChartOverMap a S).left := inferInstanceAs (Mono (Grassmannian.Gluing.grassmannianChartMap a S))
  have : Mono (Grassmannian.Gluing.grassmannianChartOverMap a S) := Over.mono_of_mono_left _
  exact inferInstanceAs (Mono (Chart.GradedHilbert.normalizedHilbertChartInclusion a S q ≫ Grassmannian.Gluing.grassmannianChartOverMap a S))

theorem normalizedGrassmannianOverlap_isPullback_over :
    IsPullback (Normalized.Overlap.Grassmannian.normalizedOverlapInclusion a b S)
      ((Normalized.Overlap.Grassmannian.normalizedOverlapTransition a b S).hom ≫ Normalized.Overlap.Grassmannian.normalizedOverlapInclusion b a S)
      (Grassmannian.Gluing.grassmannianChartOverMap a S) (Grassmannian.Gluing.grassmannianChartOverMap b S) := by
  apply IsPullback.of_map_of_faithful (Over.forget S)
  exact Grassmannian.Gluing.grassmannianChart_intersection_isPullback a b S

def normalizedHilbertOpenOverlap : Over S :=
  pullback (Chart.GradedHilbert.normalizedHilbertChartInclusion a S q) (Normalized.Overlap.Grassmannian.normalizedOverlapInclusion a b S)

def normalizedHilbertOpenOverlapInclusion :
    normalizedHilbertOpenOverlap a b S q ⟶ Chart.GradedHilbert.normalizedHilbertChart a S q := pullback.fst _ _

def normalizedHilbertOpenOverlapAmbient :
    normalizedHilbertOpenOverlap a b S q ⟶ Normalized.Overlap.Grassmannian.normalizedChartOverlap a b S := pullback.snd _ _

theorem normalizedHilbertOpenOverlap_condition :
    normalizedHilbertOpenOverlapInclusion a b S q ≫ Chart.GradedHilbert.normalizedHilbertChartInclusion a S q =
      normalizedHilbertOpenOverlapAmbient a b S q ≫ Normalized.Overlap.Grassmannian.normalizedOverlapInclusion a b S := pullback.condition

instance normalizedHilbertOpenOverlapInclusion_isOpenImmersion :
    IsOpenImmersion (normalizedHilbertOpenOverlapInclusion a b S q).left := by
  have hp := (IsPullback.of_hasPullback (Chart.GradedHilbert.normalizedHilbertChartInclusion a S q)
    (Normalized.Overlap.Grassmannian.normalizedOverlapInclusion a b S)).map (Over.forget S)
  exact MorphismProperty.of_isPullback hp.flip (Normalized.Overlap.Grassmannian.normalizedOverlapInclusion_isOpenImmersion a b S)

theorem normalizedHilbertOpenOverlap_second_mem :
    normalizedHilbertOpenOverlapAmbient a b S q ≫ (Normalized.Overlap.Grassmannian.normalizedOverlapTransition a b S).hom ≫
      Normalized.Overlap.Grassmannian.normalizedOverlapInclusion b a S ∈
        (Chart.GradedHilbert.normalizedHilbertChartSubfunctor b S q).obj (.op (normalizedHilbertOpenOverlap a b S q)) := by
  apply (OverlapCriterion.GradedHilbert.normalizedHilbertChart_overlap_mem_iff a b S q _).mp
  rw [← normalizedHilbertOpenOverlap_condition]
  exact (Chart.GradedHilbert.normalizedHilbertChartSubfunctor a S q).map
    (normalizedHilbertOpenOverlapInclusion a b S q).op (Chart.GradedHilbert.normalizedHilbertChart_universal_mem a S q)

def normalizedHilbertOpenOverlapToSecond :
    normalizedHilbertOpenOverlap a b S q ⟶ Chart.GradedHilbert.normalizedHilbertChart b S q :=
  Classical.choose ((Chart.GradedHilbert.normalizedHilbertChart_factorization_iff b S q _).mp
    (normalizedHilbertOpenOverlap_second_mem a b S q))

theorem normalizedHilbertOpenOverlapToSecond_inclusion :
    normalizedHilbertOpenOverlapToSecond a b S q ≫ Chart.GradedHilbert.normalizedHilbertChartInclusion b S q =
      normalizedHilbertOpenOverlapAmbient a b S q ≫ (Normalized.Overlap.Grassmannian.normalizedOverlapTransition a b S).hom ≫
        Normalized.Overlap.Grassmannian.normalizedOverlapInclusion b a S :=
  (Classical.choose_spec ((Chart.GradedHilbert.normalizedHilbertChart_factorization_iff b S q _).mp
    (normalizedHilbertOpenOverlap_second_mem a b S q))).1

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.NormalizedHilbert.OpenOverlap.GradedHilbert
