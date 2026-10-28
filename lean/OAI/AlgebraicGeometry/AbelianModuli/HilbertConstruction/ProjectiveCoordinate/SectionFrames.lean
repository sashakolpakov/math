import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveCoordinate.Nonvanishing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.SectionCoordinateValues
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.GeneratorNaturality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coordinate.FromSectionValue

/-! # Section Frames -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveCoordinate.SectionFrames

noncomputable section

/-! The actual homogeneous coordinate sections form the standard chart
frames. Their frame coordinates are the genuine coordinate-ratio
functions on the projective quotient. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

variable {R : Type u} [CommRing R] {n : ℕ} (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))

instance projectiveCoordinateSection_chart_isIso (i : Fin (n + 1)) :
    IsIso (Ample.LineBundles.pullbackSection (ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i}).ι (GlobalSections.projectiveCoordinateSection I i)) := by
  rw [← Nonvanishing.projectiveCoordinateSection_nonvanishing I i]
  infer_instance

theorem projectiveCoordinateSectionFamily_covers :
    ∀ x : Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I), ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (GlobalSections.projectiveCoordinateSection I i) := by
  intro x
  obtain ⟨i, hi⟩ := ProjectiveTwisting.Bundle.projectiveTwistingCover I x
  refine ⟨i.down, ?_⟩
  rw [Nonvanishing.projectiveCoordinateSection_nonvanishing]
  exact hi

private theorem projectiveCoordinateSection_chart_value (i k : Fin (n + 1)) :
    (GlobalSections.projectiveCoordinateSection I k).app (ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i})
        (1 : Γ(Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I), ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i})) =
      OpenFrame.SectionGenerators.openFrameGenerator (ProjectiveTwisting.Bundle.projectiveTwistingTransitions I 1)
        (ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i}) (ULift.up i) le_rfl
        (Coordinate.RatioSections.coordinateRatioSection I {i} i k (Finset.mem_singleton_self i)) := by
  have hc := congrFun (GlobalSections.projectiveCoordinateSection_tuple I k) (ULift.up i)
  exact (OpenFrame.SectionCoordinateValues.openFrameSection_app_of_tuple (ProjectiveTwisting.Bundle.projectiveTwistingTransitions I 1)
    (GlobalSections.projectiveCoordinateSection I k) (ULift.up i)).trans
      (congrArg (OpenFrame.SectionGenerators.openFrameGenerator (ProjectiveTwisting.Bundle.projectiveTwistingTransitions I 1)
        (ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i}) (ULift.up i) le_rfl) hc)

private theorem frameCoordinate_from_generator {Y : Scheme.{u}} {M : Y.Modules}
    (U : Y.Opens) (s t : Line.Bundles.structureModule Y ⟶ M) [IsIso (Ample.LineBundles.pullbackSection U.ι s)]
    (r : Γ(Y, U)) (v : Γ(Y, U) → Γ(M, U))
    (hs : s.app U (1 : Γ(Y, U)) = v 1)
    (ht : t.app U (1 : Γ(Y, U)) = v r) (hv : r • v 1 = v r) :
    Frame.Coordinates.frameCoordinate (Ample.LineBundles.pullbackSection U.ι s) (Ample.LineBundles.pullbackSection U.ι t) = U.topIso.inv r := by
  apply Coordinate.FromSectionValue.local_frameCoordinate_eq_of_value_on_open U s t (U.topIso.inv r)
  rw [show U.topIso.hom (U.topIso.inv r) = r from
    ConcreteCategory.congr_hom U.topIso.inv_hom_id r, hs, ht]
  exact hv.symm

theorem projectiveCoordinateSection_frameCoordinate (i j : Fin (n + 1)) :
    Frame.Coordinates.frameCoordinate
      (Ample.LineBundles.pullbackSection (ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i}).ι (GlobalSections.projectiveCoordinateSection I i))
      (Ample.LineBundles.pullbackSection (ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i}).ι (GlobalSections.projectiveCoordinateSection I j)) =
    (ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i}).topIso.inv
      (Coordinate.RatioSections.coordinateRatioSection I {i} i j (Finset.mem_singleton_self i)) := by
  let U := ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i}
  let D := ProjectiveTwisting.Bundle.projectiveTwistingTransitions I 1
  let r := Coordinate.RatioSections.coordinateRatioSection I {i} i j (Finset.mem_singleton_self i)
  have hv := projectiveCoordinateSection_chart_value I i
  have hs : (GlobalSections.projectiveCoordinateSection I i).app U (1 : Γ(Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I), U)) =
      OpenFrame.SectionGenerators.openFrameGenerator D U (ULift.up i) le_rfl 1 := by
    simpa only [Coordinate.RatioSections.coordinateRatioSection_self] using hv i
  have ht := hv j
  exact frameCoordinate_from_generator U
    (GlobalSections.projectiveCoordinateSection I i) (GlobalSections.projectiveCoordinateSection I j) r
    (OpenFrame.SectionGenerators.openFrameGenerator D U (ULift.up i) le_rfl) hs ht
    (OpenFrame.GeneratorNaturality.openFrameGenerator_smul_one D U (ULift.up i) le_rfl r)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveCoordinate.SectionFrames
