import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveCoordinate.CoefficientPullback
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.SectionPullbackComposition

/-! # Quotient Coordinate Pullbacks -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.QuotientCoordinatePullbacks

noncomputable section

/-! Compatible morphisms of projective quotients over changing coefficient rings preserve their actual coordinate opens and ratio sections. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

universe u

variable {R A : CommRingCat.{u}} (φ : R ⟶ A) {n : ℕ}
variable (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading A n)) (J : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))
variable (m : Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I) ⟶ Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading J))
variable (hm : m ≫ HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion J = HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I ≫ Projective.CoefficientFunctoriality.polynomialProjectiveMap φ n)

include hm

theorem coefficientQuotient_coordinate_preimage (i : Fin (n + 1)) :
    m ⁻¹ᵁ ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen J {i} = ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i} := by
  have hJ := congrArg (fun U => m ⁻¹ᵁ U) (Quotient.CoordinatePullback.projectiveQuotient_coordinate_preimage J i)
  have he := congrArg (fun q => q ⁻¹ᵁ Proj.basicOpen (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n) (X i)) hm
  have hφ := congrArg (fun U => HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I ⁻¹ᵁ U)
    (ProjectiveCoordinate.CoefficientPullback.polynomialProjectiveMap_coordinate_preimage φ i)
  exact hJ.symm.trans (he.trans (hφ.trans (Quotient.CoordinatePullback.projectiveQuotient_coordinate_preimage I i)))

theorem coefficientQuotient_coordinate_pullback (i j : Fin (n + 1))
    (V : (Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)).Opens)
    (hV : V ≤ m ⁻¹ᵁ ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen J {i})
    (hI : V ≤ ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i}) :
    Open.SectionPullback.openSectionPullback m (ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen J {i}) V hV
      (Coordinate.RatioSections.coordinateRatioSection J {i} i j (Finset.mem_singleton_self i)) =
      (Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)).presheaf.map (homOfLE hI).op
        (Coordinate.RatioSections.coordinateRatioSection I {i} i j (Finset.mem_singleton_self i)) := by
  let U := Proj.basicOpen (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n) (X i)
  let W := Proj.basicOpen (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading A n) (X i)
  let r := Quotient.CoordinatePullback.projectiveCoordinateFunction R i j
  have hqJ := (Quotient.CoordinatePullback.projectiveQuotient_coordinate_preimage J i).ge
  have hqI := (Quotient.CoordinatePullback.projectiveQuotient_coordinate_preimage I i).ge
  have hφ := (ProjectiveCoordinate.CoefficientPullback.polynomialProjectiveMap_coordinate_preimage φ i).ge
  have hmq : V ≤ (m ≫ HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion J) ⁻¹ᵁ U :=
    hV.trans ((TopologicalSpace.Opens.map m.base).monotone hqJ)
  have hqφ : V ≤ (HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I ≫ Projective.CoefficientFunctoriality.polynomialProjectiveMap φ n) ⁻¹ᵁ U :=
    (hI.trans hqI).trans ((TopologicalSpace.Opens.map (HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I).base).monotone hφ)
  have he := Open.SectionPullbackComposition.openSectionPullback_comp m (HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion J) U
    (ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen J {i}) V hqJ hV hmq r
  have hJ := congrArg (Open.SectionPullback.openSectionPullback m (ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen J {i}) V hV)
    (Quotient.CoordinatePullback.projectiveQuotient_coordinate_pullback J i j hqJ)
  have hcomp := Open.SectionPullbackComposition.openSectionPullback_comp (HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I) (Projective.CoefficientFunctoriality.polynomialProjectiveMap φ n)
    U W V hφ (hI.trans hqI) hqφ r
  have hval := congrArg (Open.SectionPullback.openSectionPullback (HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I) W V (hI.trans hqI))
    (ProjectiveCoordinate.CoefficientPullback.polynomialProjectiveMap_coordinate_pullback φ i j hφ)
  have hres := Open.SectionPullback.openSectionPullback_restrict_target (HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I) W
    (ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i}) V hqI hI (Quotient.CoordinatePullback.projectiveCoordinateFunction A i j)
  have hIc := congrArg ((Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)).presheaf.map (homOfLE hI).op)
    (Quotient.CoordinatePullback.projectiveQuotient_coordinate_pullback I i j hqI)
  exact hJ.symm.trans (he.trans ((Open.SectionPullbackComposition.openSectionPullback_congr hm U V hmq hqφ r).trans
    (hcomp.symm.trans (hval.trans (hres.symm.trans hIc)))))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.QuotientCoordinatePullbacks
