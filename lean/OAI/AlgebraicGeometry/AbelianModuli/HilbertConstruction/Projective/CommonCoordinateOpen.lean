import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveCoordinate.Cover

/-! # Common Coordinate Open -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.CommonCoordinateOpen

noncomputable section

/-! An open lies in a multi-coordinate chart exactly when all its named coordinates are invertible there. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

universe u

variable {R : Type u} [CommRing R] {n : ℕ} (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))

theorem le_coordinateProjectiveChartOpen (V : (Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)).Opens)
    (s : Finset (Fin (n + 1))) (h : ∀ i ∈ s, V ≤ ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i}) :
    V ≤ ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I s := by
  induction s using Finset.induction_on with
  | empty =>
      simp only [ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen, HilbertScheme.Presentations.Cech.AugmentationDegree.ProjectiveCech.inversionMonomial_empty, map_one, Proj.basicOpen_one, le_top]
  | @insert i s hi ih =>
      have he : HilbertScheme.Presentations.LaurentMonomials.ProjectiveCech.inversionMonomial R (insert i s) = X i * HilbertScheme.Presentations.LaurentMonomials.ProjectiveCech.inversionMonomial R s := by
        rw [HilbertScheme.Presentations.EventualDegreeFlatness.ProjectiveCech.inversionMonomial_factor_variable R (insert i s) i (Finset.mem_insert_self _ _),
          Finset.erase_insert hi]
      change V ≤ Proj.basicOpen (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I) (algebraMap _ _ (HilbertScheme.Presentations.LaurentMonomials.ProjectiveCech.inversionMonomial R (insert i s)))
      rw [he, map_mul, Proj.basicOpen_mul]
      exact le_inf (by simpa only [ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen, HilbertScheme.Presentations.EventualDegreeFlatness.ProjectiveCech.inversionMonomial_singleton] using h i (Finset.mem_insert_self _ _))
        (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.CommonCoordinateOpen
