import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveChart.SectionCoordinates
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.SingletonCoordinates

/-! # Cover -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveCoordinate.Cover

noncomputable section

/-! Singleton projective coordinate charts cover the quotient, and their tuples of actual sections are the first coordinate Čech term. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

universe u

variable {R : Type u} [CommRing R] {n : ℕ} (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))

theorem coordinateProjectiveChartOpen_singleton (i : Fin (n + 1)) :
    ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i} = Proj.basicOpen (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I) (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.gradedQuotientMap I (X i)) := by
  unfold ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen
  rw [HilbertScheme.Presentations.EventualDegreeFlatness.ProjectiveCech.inversionMonomial_singleton]
  rfl

theorem coordinateProjectiveChartOpen_cover : (⨆ i : Fin (n + 1), ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i}) = ⊤ := by
  simp_rw [coordinateProjectiveChartOpen_singleton]
  exact Proj.iSup_basicOpen_eq_top (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I) _ (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.quotient_irrelevant_le_span_variables I)

theorem coordinateProjectiveChartOpen_pair (i j : Fin (n + 1)) :
    ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i, j} =
      ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i} ⊓ ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {j} := by
  by_cases hij : i = j
  · subst j
    simp only [Finset.insert_eq_of_mem (Finset.mem_singleton_self i), inf_idem]
  · have he : ({i, j} : Finset (Fin (n + 1))).erase i = {j} := by simp [hij]
    have hp : HilbertScheme.Presentations.LaurentMonomials.ProjectiveCech.inversionMonomial R {i, j} = X i * X j :=
      (HilbertScheme.Presentations.EventualDegreeFlatness.ProjectiveCech.inversionMonomial_factor_variable R {i, j} i (Finset.mem_insert_self i {j})).trans
        (congrArg (fun s => X i * HilbertScheme.Presentations.LaurentMonomials.ProjectiveCech.inversionMonomial R s) he |>.trans
          (congrArg (fun p : HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n => X i * p) (HilbertScheme.Presentations.EventualDegreeFlatness.ProjectiveCech.inversionMonomial_singleton R j)))
    simp only [ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen, hp, map_mul, HilbertScheme.Presentations.EventualDegreeFlatness.ProjectiveCech.inversionMonomial_singleton, Proj.basicOpen_mul]

def coordinateChartTupleCechEquiv :
    ((i : Fin (n + 1)) → Coefficient.AlgebraPresheaf.coefficientAlgebraSections
      (Affine.ChartCoefficientSections.schemeGlobalCoefficient (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)))
      (ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i})) ≃ₗ[R]
      HilbertScheme.Presentations.ModuleCech.Terms.ProjectiveCech.moduleCechTerm (σ := Fin (n + 1)) R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) 0 1 :=
  (LinearEquiv.piCongrRight (fun i => ProjectiveChart.SectionCoordinates.coordinateProjectiveChartSectionEquiv I {i} (Finset.singleton_nonempty i))).trans
    (Cech.SingletonCoordinates.moduleCechOneTermEquiv R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) 0).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveCoordinate.Cover
