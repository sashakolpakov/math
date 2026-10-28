import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveCoordinate.BasicOpen
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.FunctionNonvanishing

/-! # Nonvanishing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveCoordinate.Nonvanishing

noncomputable section

/-! Each global homogeneous coordinate section is nonvanishing exactly on its standard projective chart. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] {n : ℕ} (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))

theorem projectiveCoordinateSection_nonvanishing_on_chart (i j : Fin (n + 1)) :
    (ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i}).ι ⁻¹ᵁ Ample.LineBundles.sectionNonvanishing (GlobalSections.projectiveCoordinateSection I j) =
      (ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i}).ι ⁻¹ᵁ
        (ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i} ⊓ ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {j}) := by
  let D := ProjectiveTwisting.Bundle.projectiveTwistingTransitions I 1
  have hc : (show Γ(Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I), ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i}) from
      OpenFrame.CoefficientSections.openFrameGlobalTupleMap D
        (Global.Sections.moduleSectionHomEquiv (ProjectiveTwisting.Bundle.projectiveTwistingBundle I 1).sheaf (GlobalSections.projectiveCoordinateSection I j))
        (ULift.up i)) = Coordinate.RatioSections.coordinateRatioSection I {i} i j (Finset.mem_singleton_self i) :=
    congrFun (GlobalSections.projectiveCoordinateSection_tuple I j) (ULift.up i)
  have hb := congrArg (fun r : Γ(Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I), ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i}) =>
    (Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)).basicOpen r) hc
  exact (OpenFrame.FunctionNonvanishing.openFrameSection_nonvanishing_chart_function D (GlobalSections.projectiveCoordinateSection I j) (ULift.up i)).trans
    (congrArg (fun V => (ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i}).ι ⁻¹ᵁ V)
      (hb.trans (BasicOpen.coordinateRatioSection_singleton_basicOpen I i j)))

theorem projectiveCoordinateSection_nonvanishing (j : Fin (n + 1)) :
    Ample.LineBundles.sectionNonvanishing (GlobalSections.projectiveCoordinateSection I j) = ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {j} := by
  ext x
  obtain ⟨i, hi⟩ := ProjectiveTwisting.Bundle.projectiveTwistingCover I x
  let y : (ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i.down}).toScheme := ⟨x, hi⟩
  have h := congrArg (fun V : (ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i.down}).toScheme.Opens => y ∈ V)
    (projectiveCoordinateSection_nonvanishing_on_chart I i.down j)
  change (x ∈ Ample.LineBundles.sectionNonvanishing (GlobalSections.projectiveCoordinateSection I j)) =
    (x ∈ ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i.down} ∧ x ∈ ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {j}) at h
  exact h.to_iff.trans (and_iff_right hi)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveCoordinate.Nonvanishing
