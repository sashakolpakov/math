import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Segre.ProductChartEquivalence
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Segre.ChartProjections

/-! # Chart Product Algebra -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Segre.ChartProductAlgebra

noncomputable section

/-! The product chart algebra equivalence realizes the previously constructed row and column maps. -/

open _root_.MvPolynomial

universe u

variable (R : Type u) [CommRing R] {n m : ℕ} (p : ChartProjections.SegreProjectiveIndex.{u} n m)

def segreHomogeneousProductChartEquiv :
    ProductChartMaps.ProjectiveProductChartRing R p.1.down p.2.down ≃ₐ[R] ProjectiveCharts.SegreHomogeneousChart R p.1 p.2 :=
  (ProductChartEquivalence.segreProductChartEquiv R p.1.down p.2.down).trans (ProjectiveCharts.segreHomogeneousChartEquiv R p.1 p.2).symm

def segreRowChartAlgebra : ProjectiveChart.Evaluation.projectiveChartRing R n p.1.down →ₐ[R] ProjectiveCharts.SegreHomogeneousChart R p.1 p.2 :=
  ProjectiveChart.Algebra.projectiveChartEvaluationAlg (fun a => ChartCoordinates.segreChartCoordinate R p.1 p.2 (ULift.up a, p.2))
    p.1.down (ChartCoordinates.segreChartCoordinate_pivot R p.1 p.2)

def segreColumnChartAlgebra : ProjectiveChart.Evaluation.projectiveChartRing R m p.2.down →ₐ[R] ProjectiveCharts.SegreHomogeneousChart R p.1 p.2 :=
  ProjectiveChart.Algebra.projectiveChartEvaluationAlg (fun b => ChartCoordinates.segreChartCoordinate R p.1 p.2 (p.1, ULift.up b))
    p.2.down (ChartCoordinates.segreChartCoordinate_pivot R p.1 p.2)

theorem segreRowChartAlgebra_coordinate (a : Fin (n + 1)) :
    segreRowChartAlgebra R p (HilbertScheme.Presentations.Polynomial.Dehomogenization.PolynomialProjective.dehomogenize p.1.down (X a)) =
      ChartCoordinates.segreChartCoordinate R p.1 p.2 (ULift.up a, p.2) :=
  ProjectiveChart.Algebra.projectiveChartEvaluationAlg_coordinate (R := R)
    (fun a => ChartCoordinates.segreChartCoordinate R p.1 p.2 (ULift.up a, p.2)) p.1.down
    (ChartCoordinates.segreChartCoordinate_pivot R p.1 p.2) a

theorem segreColumnChartAlgebra_coordinate (b : Fin (m + 1)) :
    segreColumnChartAlgebra R p (HilbertScheme.Presentations.Polynomial.Dehomogenization.PolynomialProjective.dehomogenize p.2.down (X b)) =
      ChartCoordinates.segreChartCoordinate R p.1 p.2 (p.1, ULift.up b) :=
  ProjectiveChart.Algebra.projectiveChartEvaluationAlg_coordinate (R := R)
    (fun b => ChartCoordinates.segreChartCoordinate R p.1 p.2 (p.1, ULift.up b)) p.2.down
    (ChartCoordinates.segreChartCoordinate_pivot R p.1 p.2) b

theorem segreHomogeneousChartEquiv_row (a : ULift.{u} (Fin (n + 1))) :
    ProjectiveCharts.segreHomogeneousChartEquiv R p.1 p.2 (ChartCoordinates.segreChartCoordinate R p.1 p.2 (a, p.2)) =
      NormalizedCoordinates.segreRowCoordinate R p.1 p.2 a := by
  have h := ProjectiveCharts.segreHomogeneousChartEquiv_variable R p.1 p.2 a p.2
  simp only [NormalizedCoordinates.segreColumnCoordinate, dite_true, mul_one] at h
  exact h

theorem segreHomogeneousChartEquiv_column (b : ULift.{u} (Fin (m + 1))) :
    ProjectiveCharts.segreHomogeneousChartEquiv R p.1 p.2 (ChartCoordinates.segreChartCoordinate R p.1 p.2 (p.1, b)) =
      NormalizedCoordinates.segreColumnCoordinate R p.1 p.2 b := by
  have h := ProjectiveCharts.segreHomogeneousChartEquiv_variable R p.1 p.2 p.1 b
  simp only [NormalizedCoordinates.segreRowCoordinate, dite_true, one_mul] at h
  exact h

theorem segreHomogeneousProductChartEquiv_left :
    (segreHomogeneousProductChartEquiv R p).toAlgHom.comp Algebra.TensorProduct.includeLeft =
      segreRowChartAlgebra R p := by
  apply ProjectiveChart.Algebra.projectiveChartAlgebra_ext (R := R) (A := ProjectiveCharts.SegreHomogeneousChart R p.1 p.2) p.1.down
  intro a
  apply (ProjectiveCharts.segreHomogeneousChartEquiv R p.1 p.2).injective
  change ProjectiveCharts.segreHomogeneousChartEquiv R p.1 p.2
    ((ProjectiveCharts.segreHomogeneousChartEquiv R p.1 p.2).symm
      (ProductChartMaps.segreProductChartForward R p.1.down p.2.down
        (Algebra.TensorProduct.includeLeft (S := R) (HilbertScheme.Presentations.Polynomial.Dehomogenization.PolynomialProjective.dehomogenize p.1.down (X a))))) = _
  rw [AlgEquiv.apply_symm_apply, ProductChartMaps.segreProductChartForward_left, ProductChartMaps.segreProductChartRow_coordinate]
  exact (congrArg (ProjectiveCharts.segreHomogeneousChartEquiv R p.1 p.2)
    (segreRowChartAlgebra_coordinate R p a)).trans
      (segreHomogeneousChartEquiv_row R p (ULift.up a)) |>.symm

theorem segreHomogeneousProductChartEquiv_right :
    (segreHomogeneousProductChartEquiv R p).toAlgHom.comp Algebra.TensorProduct.includeRight =
      segreColumnChartAlgebra R p := by
  apply ProjectiveChart.Algebra.projectiveChartAlgebra_ext (R := R) (A := ProjectiveCharts.SegreHomogeneousChart R p.1 p.2) p.2.down
  intro b
  apply (ProjectiveCharts.segreHomogeneousChartEquiv R p.1 p.2).injective
  change ProjectiveCharts.segreHomogeneousChartEquiv R p.1 p.2
    ((ProjectiveCharts.segreHomogeneousChartEquiv R p.1 p.2).symm
      (ProductChartMaps.segreProductChartForward R p.1.down p.2.down
        (Algebra.TensorProduct.includeRight (HilbertScheme.Presentations.Polynomial.Dehomogenization.PolynomialProjective.dehomogenize p.2.down (X b))))) = _
  rw [AlgEquiv.apply_symm_apply, ProductChartMaps.segreProductChartForward_right, ProductChartMaps.segreProductChartColumn_coordinate]
  exact (congrArg (ProjectiveCharts.segreHomogeneousChartEquiv R p.1 p.2)
    (segreColumnChartAlgebra_coordinate R p b)).trans
      (segreHomogeneousChartEquiv_column R p (ULift.up b)) |>.symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Segre.ChartProductAlgebra
