import OAI.AlgebraicGeometry.HilbertScheme.Presentations.BoundedHilbert.ChartRestriction

/-! # Chart Pullback -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.BoundedHilbert.ChartPullback.GradedHilbert

noncomputable section

/-! Each bounded Hilbert chart is the actual base change of the global
parameter scheme along the corresponding Grassmannian open chart. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι] {n N : ℕ}
variable (a : ι → Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N) (S : Scheme.{u}) (q : ℕ → ℕ)

def boundedHilbertChartOverMap : NormalizedHilbert.Chart.GradedHilbert.normalizedHilbertChart a S q ⟶ Data.GradedHilbert.boundedHilbertOver (ι := ι) n N S q :=
  Over.homMk (Data.GradedHilbert.boundedHilbertChartMap n N S q a) (by
    change Data.GradedHilbert.boundedHilbertChartMap n N S q a ≫
      (Data.GradedHilbert.boundedHilbertParameter n N S q ≫ Grassmannian.Gluing.grassmannianStructureMap S) = (NormalizedHilbert.Chart.GradedHilbert.normalizedHilbertChart a S q).hom
    rw [← Category.assoc, Data.GradedHilbert.boundedHilbertChartMap_parameter, Category.assoc,
      Grassmannian.Gluing.grassmannianChartMap_structureMap, (NormalizedHilbert.Chart.GradedHilbert.normalizedHilbertChartInclusion a S q).w])

theorem boundedHilbertChartOverMap_parameter :
    boundedHilbertChartOverMap a S q ≫ Data.GradedHilbert.boundedHilbertParameterOver (ι := ι) n N S q =
      NormalizedHilbert.Chart.GradedHilbert.normalizedHilbertChartInclusion a S q ≫ Grassmannian.Gluing.grassmannianChartOverMap a S :=
  Over.OverMorphism.ext (Data.GradedHilbert.boundedHilbertChartMap_parameter n N S q a)

instance boundedHilbertChartOverMap_mono : Mono (boundedHilbertChartOverMap a S q) := by
  have : Mono (boundedHilbertChartOverMap a S q).left :=
    inferInstanceAs (Mono (Data.GradedHilbert.boundedHilbertChartMap n N S q a))
  exact Over.mono_of_mono_left _

theorem boundedHilbertChart_isPullback_over :
    IsPullback (boundedHilbertChartOverMap a S q) (NormalizedHilbert.Chart.GradedHilbert.normalizedHilbertChartInclusion a S q)
      (Data.GradedHilbert.boundedHilbertParameterOver (ι := ι) n N S q) (Grassmannian.Gluing.grassmannianChartOverMap a S) := by
  apply IsPullback.mk'
  · exact boundedHilbertChartOverMap_parameter a S q
  · intro T f g h _
    exact (cancel_mono (boundedHilbertChartOverMap a S q)).mp h
  · intro T f g h
    have hlocal : Representation.GradedHilbert.boundedHilbertLocalCondition n N S q (f ≫ Data.GradedHilbert.boundedHilbertParameterOver n N S q) :=
      (Representation.GradedHilbert.boundedHilbertLocalCondition_iff_lift n N S q _).mpr
        ⟨f, rfl, fun z hz => (cancel_mono (Data.GradedHilbert.boundedHilbertParameterOver n N S q)).mp hz⟩
    rw [h] at hlocal
    have hmem := (ChartRestriction.GradedHilbert.boundedHilbertLocalCondition_chart_iff a S q g).mp hlocal
    obtain ⟨z, hz, _⟩ := (NormalizedHilbert.Chart.GradedHilbert.normalizedHilbertChart_factorization_iff a S q g).mp hmem
    refine ⟨z, ?_, hz⟩
    apply (cancel_mono (Data.GradedHilbert.boundedHilbertParameterOver n N S q)).mp
    rw [Category.assoc, boundedHilbertChartOverMap_parameter, ← Category.assoc, hz]
    exact h.symm

theorem boundedHilbertChart_isPullback :
    IsPullback (Data.GradedHilbert.boundedHilbertChartMap n N S q a) (NormalizedHilbert.Chart.GradedHilbert.normalizedHilbertChartInclusion a S q).left
      (Data.GradedHilbert.boundedHilbertParameter (ι := ι) n N S q) (Grassmannian.Gluing.grassmannianChartMap a S) :=
  (boundedHilbertChart_isPullback_over a S q).map (Over.forget S)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.BoundedHilbert.ChartPullback.GradedHilbert
