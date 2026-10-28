import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coordinate.SectionCover
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveCoordinate.BasicOpen

/-! # Section Cover -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.SectionCover

noncomputable section

/-! The actual projective quotient charts and coordinate ratios instantiate the coordinate data used for quasicoherent section extension. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

universe u

variable {R : Type u} [CommRing R] {n : ℕ} (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))

theorem projectiveCoordinateRatio_transition (i k j : Fin (n + 1)) :
    (Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)).presheaf.map
      (homOfLE (show ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i} ⊓ ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {k} ≤
        ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i} from inf_le_left)).op
      (Coordinate.RatioSections.coordinateRatioSection I {i} i j (Finset.mem_singleton_self i)) =
    (Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)).presheaf.map
      (homOfLE (show ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i} ⊓ ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {k} ≤
        ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i} from inf_le_left)).op
      (Coordinate.RatioSections.coordinateRatioSection I {i} i k (Finset.mem_singleton_self i)) *
    (Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)).presheaf.map
      (homOfLE (show ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i} ⊓ ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {k} ≤
        ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {k} from inf_le_right)).op
      (Coordinate.RatioSections.coordinateRatioSection I {k} k j (Finset.mem_singleton_self k)) := by
  let V := ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i} ⊓ ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {k}
  have hV : V ≤ ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i, k} :=
    (ProjectiveCoordinate.Cover.coordinateProjectiveChartOpen_pair I i k).symm.le
  have hi : i ∈ ({i, k} : Finset (Fin (n + 1))) := Finset.mem_insert_self _ _
  have hk : k ∈ ({i, k} : Finset (Fin (n + 1))) := Finset.mem_insert_of_mem (Finset.mem_singleton_self k)
  have hl (a : Fin (n + 1)) :
      Coordinate.RatioSubopens.coordinateRatioOn I V {i} inf_le_left i a (Finset.mem_singleton_self i) =
        Coordinate.RatioSubopens.coordinateRatioOn I V {i, k} hV i a hi :=
    Coordinate.RatioSubopens.coordinateRatioOn_change I V (Finset.singleton_subset_iff.mpr hi) hV i a (Finset.mem_singleton_self i)
  have hr (a : Fin (n + 1)) :
      Coordinate.RatioSubopens.coordinateRatioOn I V {k} inf_le_right k a (Finset.mem_singleton_self k) =
        Coordinate.RatioSubopens.coordinateRatioOn I V {i, k} hV k a hk :=
    Coordinate.RatioSubopens.coordinateRatioOn_change I V (Finset.singleton_subset_iff.mpr hk) hV k a (Finset.mem_singleton_self k)
  change Coordinate.RatioSubopens.coordinateRatioOn I V {i} inf_le_left i j _ =
    Coordinate.RatioSubopens.coordinateRatioOn I V {i} inf_le_left i k _ * Coordinate.RatioSubopens.coordinateRatioOn I V {k} inf_le_right k j _
  rw [hl j, hl k, hr j]
  exact (Coordinate.RatioSubopens.coordinateRatioOn_comp I V {i, k} hV i k j hi hk).symm

def projectiveCoordinateSectionCover : Coordinate.SectionCover.CoordinateSectionCover (Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)) (Fin (n + 1)) where
  opens i := ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i}
  affine i := by
    rw [ProjectiveCoordinate.Cover.coordinateProjectiveChartOpen_singleton]
    exact Proj.isAffineOpen_basicOpen (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I) (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.gradedQuotientMap I (X i))
      ((HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.gradedQuotientMap I).map_mem (isHomogeneous_X R i)) Nat.zero_lt_one
  affine_overlap i k := by
    rw [← ProjectiveCoordinate.Cover.coordinateProjectiveChartOpen_pair]
    exact Proj.isAffineOpen_basicOpen (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I) _
      (HilbertScheme.Presentations.Flat.ProjectiveCoordinatePieces.GradedHilbert.quotient_inversionMonomial_homogeneous I {i, k})
      (Finset.card_pos.mpr ⟨i, Finset.mem_insert_self i {k}⟩)
  covers x := by
    have h : x ∈ (⨆ i : Fin (n + 1), ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i}) := by
      rw [ProjectiveCoordinate.Cover.coordinateProjectiveChartOpen_cover]
      exact True.intro
    exact TopologicalSpace.Opens.mem_iSup.mp h
  ratio i j := Coordinate.RatioSections.coordinateRatioSection I {i} i j (Finset.mem_singleton_self i)
  ratio_self i := Coordinate.RatioSections.coordinateRatioSection_self I {i} i (Finset.mem_singleton_self i)
  basicOpen_ratio := ProjectiveCoordinate.BasicOpen.coordinateRatioSection_singleton_basicOpen I
  ratio_transition := projectiveCoordinateRatio_transition I

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.SectionCover
