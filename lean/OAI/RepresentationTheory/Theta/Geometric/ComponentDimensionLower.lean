import OAI.RepresentationTheory.Theta.Geometric.CountableReferenceBallImages
import OAI.RepresentationTheory.Theta.Geometric.Holomorphic.ImageMeasure
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-! # Component Dimension Lower -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! At least one actual projective component has dimension at least
two: the open reference ball cannot be covered by countably many
holomorphic images of smaller complex dimension. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MeasureTheory _root_.MeasureTheory.Measure
open scoped Classical

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)

theorem Data.ActiveHeckeThetaData.exists_reference_component_dimension_at_least_two (hg : D.pel.HasIntegralModelGeometry) :
    ∃ j : Fin D.pel.componentCount, 2 ≤ (D.componentVariety hg j).complexDimension ∧
      ∃ a : D.domain, ∃ x : (D.componentVariety hg j).analyticSpace,
        x ≫ D.componentComplexInclusion j = D.referenceModuliMap hg a := by
  by_contra h
  let hit (j : Fin D.pel.componentCount) := ∃ a : D.domain,
    ∃ x : (D.componentVariety hg j).analyticSpace,
      x ≫ D.componentComplexInclusion j = D.referenceModuliMap hg a
  have hdim (j : Fin D.pel.componentCount) (hj : hit j) :
      (D.componentVariety hg j).complexDimension < 2 :=
    lt_of_not_ge (fun hd => h ⟨j, hd, hj⟩)
  obtain ⟨I, hI, j, O, period, hO, hcover⟩ := D.exists_countable_reference_ball_images hg
  let : Countable I := hI
  let J := {i : I // hit (j i)}
  let μ : Measure Geometry.ComplexBall.PrescribedSignsB.BallChart := volume
  have hzero (i : J) : μ (period i.val '' O i.val) = 0 := by
    apply Holomorphic.ImageMeasure.measure_image_eq_zero_of_complex_finrank_lt μ (hO i.val).1 (hO i.val).2
    rw [(D.componentVariety hg (j i.val)).analyticModel_complex_finrank]
    simpa only [Geometry.ComplexBall.PrescribedSignsB.BallChart, Module.finrank_pi, Fintype.card_fin] using hdim (j i.val) i.property
  have hnull : μ (D.domain : Set Geometry.ComplexBall.PrescribedSignsB.BallChart) = 0 := by
    apply measure_mono_null (t := ⋃ i : J, period i.val '' O i.val) ?_ (measure_iUnion_null hzero)
    intro a ha
    obtain ⟨i, hx, hi⟩ := hcover ⟨a, ha⟩
    exact Set.mem_iUnion.mpr ⟨⟨i, ⟨⟨a, ha⟩, hx⟩⟩, hi⟩
  have hne : (D.domain : Set Geometry.ComplexBall.PrescribedSignsB.BallChart).Nonempty := by
    refine ⟨0, ?_⟩
    change Complex.normSq 0 + Complex.normSq 0 < -(D.pel.reference.μ D.pel.reference.b).re
    simp only [Complex.normSq_zero, zero_add]
    exact neg_pos.mpr hg.reference_admissible.2.2.2.1
  exact (ne_of_gt (D.domain.isOpen.measure_pos (μ := μ) hne)) hnull

theorem Data.ActiveHeckeThetaData.exists_component_dimension_at_least_two (hg : D.pel.HasIntegralModelGeometry) :
    ∃ j : Fin D.pel.componentCount, 2 ≤ (D.componentVariety hg j).complexDimension := by
  obtain ⟨j, hj, _⟩ := D.exists_reference_component_dimension_at_least_two hg
  exact ⟨j, hj⟩

end

end OAI.RepresentationTheory.Theta.Geometric
