import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Segre.TensorCoordinates
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.SpaceReindex

/-! # Reindexed Segre Evaluation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ReindexedSegreEvaluation

noncomputable section

/-! Reindexing the matrix coordinates by a finite ordinal makes the Segre
chart evaluation equal to the standard projective-chart evaluation on
products of row and column coordinates. -/
open _root_.MvPolynomial
universe u
variable (R : Type u) [CommRing R] {n m d : ℕ}
variable (e : Segre.ChartProjections.SegreProjectiveIndex.{u} n m ≃ Fin (d + 1)) (p : Segre.ChartProjections.SegreProjectiveIndex.{u} n m)

def segreReindexedChartCoordinates (i : Fin (d + 1)) : Segre.ProjectiveCharts.SegreHomogeneousChart R p.1 p.2 :=
  Segre.ChartCoordinates.segreChartCoordinate R p.1 p.2 (e.symm i)

theorem segreReindexedChartCoordinates_pivot : segreReindexedChartCoordinates R e p (e p) = 1 := by
  rw [segreReindexedChartCoordinates, e.symm_apply_apply]
  exact Segre.ChartCoordinates.segreChartCoordinate_pivot R p.1 p.2

def segreStandardChartAlgebra :
    ProjectiveChart.Evaluation.projectiveChartRing R d (e p) →ₐ[R] Segre.ProjectiveCharts.SegreHomogeneousChart R p.1 p.2 :=
  ProjectiveChart.Algebra.projectiveChartEvaluationAlg (segreReindexedChartCoordinates R e p) (e p)
    (segreReindexedChartCoordinates_pivot R e p)

theorem segreStandardChartAlgebra_coordinate (i : Fin (d + 1)) :
    segreStandardChartAlgebra R e p (HilbertScheme.Presentations.Polynomial.Dehomogenization.PolynomialProjective.dehomogenize (e p) (X i)) =
      Segre.ChartCoordinates.segreChartCoordinate R p.1 p.2 (e.symm i) :=
  ProjectiveChart.Algebra.projectiveChartEvaluationAlg_coordinate (segreReindexedChartCoordinates R e p) (e p)
    (segreReindexedChartCoordinates_pivot R e p) i

variable {B : Type u} [CommRing B] [Algebra R B]
variable (r : Fin (n + 1) → B) (c : Fin (m + 1) → B)
variable (hr : r p.1.down = 1) (hc : c p.2.down = 1)

def reindexedSegreSectionCoordinates (i : Fin (d + 1)) : B :=
  r (e.symm i).1.down * c (e.symm i).2.down

include hr hc in
theorem reindexedSegreSectionCoordinates_pivot :
    reindexedSegreSectionCoordinates e r c (e p) = 1 := by
  rw [reindexedSegreSectionCoordinates, e.symm_apply_apply, hr, hc, one_mul]

theorem segreStandardChartAlgebra_evaluation :
    (Segre.TensorCoordinates.segreHomogeneousSectionEvaluation R p r c hr hc).comp (segreStandardChartAlgebra R e p) =
      ProjectiveChart.Algebra.projectiveChartEvaluationAlg (reindexedSegreSectionCoordinates e r c) (e p)
        (reindexedSegreSectionCoordinates_pivot e p r c hr hc) := by
  apply ProjectiveChart.Algebra.projectiveChartAlgebra_ext (e p)
  intro i
  change Segre.TensorCoordinates.segreHomogeneousSectionEvaluation R p r c hr hc
      (segreStandardChartAlgebra R e p (HilbertScheme.Presentations.Polynomial.Dehomogenization.PolynomialProjective.dehomogenize (e p) (X i))) = _
  rw [segreStandardChartAlgebra_coordinate, ProjectiveChart.Algebra.projectiveChartEvaluationAlg_coordinate]
  exact Segre.TensorCoordinates.segreHomogeneousSectionEvaluation_coordinate R p r c hr hc
    (e.symm i).1.down (e.symm i).2.down

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ReindexedSegreEvaluation
