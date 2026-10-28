import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quotient.CoordinatePullback
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.SectionPullbackComposition

/-! # Compatible Quotient Coordinate Pullbacks -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CompatibleQuotientCoordinatePullbacks

noncomputable section

/-! A morphism of homogeneous projective quotients compatible with their ambient embeddings preserves standard coordinate opens and ratio functions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

universe u

variable {R : Type u} [CommRing R] {n : ℕ}
variable (I J : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))
variable (m : Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I) ⟶ Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading J))
variable (hm : m ≫ HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion J = HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I)

include hm

theorem compatibleQuotient_coordinate_preimage (i : Fin (n + 1)) :
    m ⁻¹ᵁ ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen J {i} = ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i} :=
  (congrArg (fun U => m ⁻¹ᵁ U) (Quotient.CoordinatePullback.projectiveQuotient_coordinate_preimage J i)).symm.trans
    ((congrArg (fun q => q ⁻¹ᵁ Proj.basicOpen (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n) (X i)) hm).trans
      (Quotient.CoordinatePullback.projectiveQuotient_coordinate_preimage I i))

theorem compatibleQuotient_coordinate_pullback (i j : Fin (n + 1))
    (V : (Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)).Opens)
    (hV : V ≤ m ⁻¹ᵁ ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen J {i})
    (hI : V ≤ ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i}) :
    Open.SectionPullback.openSectionPullback m (ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen J {i}) V hV
      (Coordinate.RatioSections.coordinateRatioSection J {i} i j (Finset.mem_singleton_self i)) =
      (Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)).presheaf.map (homOfLE hI).op
        (Coordinate.RatioSections.coordinateRatioSection I {i} i j (Finset.mem_singleton_self i)) := by
  let U := Proj.basicOpen (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n) (X i)
  let r := Quotient.CoordinatePullback.projectiveCoordinateFunction R i j
  have hqJ := (Quotient.CoordinatePullback.projectiveQuotient_coordinate_preimage J i).ge
  have hqI := (Quotient.CoordinatePullback.projectiveQuotient_coordinate_preimage I i).ge
  have hmq : V ≤ (m ≫ HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion J) ⁻¹ᵁ U :=
    hV.trans ((TopologicalSpace.Opens.map m.base).monotone hqJ)
  have he := Open.SectionPullbackComposition.openSectionPullback_comp m (HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion J) U
    (ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen J {i}) V hqJ hV hmq r
  have hJ := congrArg (Open.SectionPullback.openSectionPullback m (ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen J {i}) V hV)
    (Quotient.CoordinatePullback.projectiveQuotient_coordinate_pullback J i j hqJ)
  have hres := Open.SectionPullback.openSectionPullback_restrict_target (HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I) U
    (ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i}) V hqI hI r
  have hIc := congrArg ((Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)).presheaf.map (homOfLE hI).op)
    (Quotient.CoordinatePullback.projectiveQuotient_coordinate_pullback I i j hqI)
  exact hJ.symm.trans (he.trans ((Open.SectionPullbackComposition.openSectionPullback_congr hm U V hmq (hI.trans hqI) r).trans
    (hres.symm.trans hIc)))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CompatibleQuotientCoordinatePullbacks
