import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Segre.ChartProductAlgebra

/-! # Tensor Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Segre.TensorCoordinates

noncomputable section

/-! Under the actual Segre chart equivalence, every normalized matrix
coordinate is the product of its row and column coordinates. Evaluation
therefore agrees with the products used by tensor-product sections. -/
open _root_.MvPolynomial
open scoped TensorProduct
universe u
variable (R : Type u) [CommRing R] {n m : ℕ} (p : ChartProjections.SegreProjectiveIndex.{u} n m)

theorem segreHomogeneousProductChartEquiv_symm_coordinate
    (a : Fin (n + 1)) (b : Fin (m + 1)) :
    (ChartProductAlgebra.segreHomogeneousProductChartEquiv R p).symm
      (ChartCoordinates.segreChartCoordinate R p.1 p.2 (ULift.up a, ULift.up b)) =
    Algebra.TensorProduct.includeLeft (S := R) (HilbertScheme.Presentations.Polynomial.Dehomogenization.PolynomialProjective.dehomogenize p.1.down (X a)) *
      Algebra.TensorProduct.includeRight (HilbertScheme.Presentations.Polynomial.Dehomogenization.PolynomialProjective.dehomogenize p.2.down (X b)) := by
  let e := ChartProductAlgebra.segreHomogeneousProductChartEquiv R p
  apply e.injective
  rw [AlgEquiv.apply_symm_apply, map_mul]
  have hl := AlgHom.congr_fun (ChartProductAlgebra.segreHomogeneousProductChartEquiv_left R p)
    (HilbertScheme.Presentations.Polynomial.Dehomogenization.PolynomialProjective.dehomogenize p.1.down (X a))
  have hr := AlgHom.congr_fun (ChartProductAlgebra.segreHomogeneousProductChartEquiv_right R p)
    (HilbertScheme.Presentations.Polynomial.Dehomogenization.PolynomialProjective.dehomogenize p.2.down (X b))
  change e (Algebra.TensorProduct.includeLeft (S := R) (HilbertScheme.Presentations.Polynomial.Dehomogenization.PolynomialProjective.dehomogenize p.1.down (X a))) =
    ChartProductAlgebra.segreRowChartAlgebra R p (HilbertScheme.Presentations.Polynomial.Dehomogenization.PolynomialProjective.dehomogenize p.1.down (X a)) at hl
  change e (Algebra.TensorProduct.includeRight (HilbertScheme.Presentations.Polynomial.Dehomogenization.PolynomialProjective.dehomogenize p.2.down (X b))) =
    ChartProductAlgebra.segreColumnChartAlgebra R p (HilbertScheme.Presentations.Polynomial.Dehomogenization.PolynomialProjective.dehomogenize p.2.down (X b)) at hr
  rw [hl, hr, ChartProductAlgebra.segreRowChartAlgebra_coordinate, ChartProductAlgebra.segreColumnChartAlgebra_coordinate]
  exact ChartCoordinates.segreChartCoordinate_entry R p.1 (ULift.up a) p.2 (ULift.up b)

variable {B : Type u} [CommRing B] [Algebra R B]
variable (r : Fin (n + 1) → B) (c : Fin (m + 1) → B)
variable (hr : r p.1.down = 1) (hc : c p.2.down = 1)

def segreProductChartEvaluation : ProductChartMaps.ProjectiveProductChartRing R p.1.down p.2.down →ₐ[R] B :=
  Algebra.TensorProduct.lift (ProjectiveChart.Algebra.projectiveChartEvaluationAlg (R := R) r p.1.down hr)
    (ProjectiveChart.Algebra.projectiveChartEvaluationAlg (R := R) c p.2.down hc) (fun _ _ => Commute.all _ _)

theorem segreProductChartEvaluation_left (a : Fin (n + 1)) :
    segreProductChartEvaluation R p r c hr hc
      (Algebra.TensorProduct.includeLeft (S := R) (HilbertScheme.Presentations.Polynomial.Dehomogenization.PolynomialProjective.dehomogenize p.1.down (X a))) = r a :=
  (AlgHom.congr_fun (Algebra.TensorProduct.lift_comp_includeLeft
    (ProjectiveChart.Algebra.projectiveChartEvaluationAlg (R := R) r p.1.down hr)
    (ProjectiveChart.Algebra.projectiveChartEvaluationAlg (R := R) c p.2.down hc) (fun _ _ => Commute.all _ _))
      (HilbertScheme.Presentations.Polynomial.Dehomogenization.PolynomialProjective.dehomogenize p.1.down (X a))).trans
        (ProjectiveChart.Algebra.projectiveChartEvaluationAlg_coordinate (R := R) r p.1.down hr a)

theorem segreProductChartEvaluation_right (b : Fin (m + 1)) :
    segreProductChartEvaluation R p r c hr hc
      (Algebra.TensorProduct.includeRight (HilbertScheme.Presentations.Polynomial.Dehomogenization.PolynomialProjective.dehomogenize p.2.down (X b))) = c b :=
  (AlgHom.congr_fun (Algebra.TensorProduct.lift_comp_includeRight'
    (ProjectiveChart.Algebra.projectiveChartEvaluationAlg (R := R) r p.1.down hr)
    (ProjectiveChart.Algebra.projectiveChartEvaluationAlg (R := R) c p.2.down hc) (fun _ _ => Commute.all _ _))
      (HilbertScheme.Presentations.Polynomial.Dehomogenization.PolynomialProjective.dehomogenize p.2.down (X b))).trans
        (ProjectiveChart.Algebra.projectiveChartEvaluationAlg_coordinate (R := R) c p.2.down hc b)

def segreHomogeneousSectionEvaluation : ProjectiveCharts.SegreHomogeneousChart R p.1 p.2 →ₐ[R] B :=
  (segreProductChartEvaluation R p r c hr hc).comp
    (ChartProductAlgebra.segreHomogeneousProductChartEquiv R p).symm.toAlgHom

theorem segreHomogeneousSectionEvaluation_coordinate (a : Fin (n + 1)) (b : Fin (m + 1)) :
    segreHomogeneousSectionEvaluation R p r c hr hc
      (ChartCoordinates.segreChartCoordinate R p.1 p.2 (ULift.up a, ULift.up b)) = r a * c b := by
  change segreProductChartEvaluation R p r c hr hc
    ((ChartProductAlgebra.segreHomogeneousProductChartEquiv R p).symm
      (ChartCoordinates.segreChartCoordinate R p.1 p.2 (ULift.up a, ULift.up b))) = _
  rw [segreHomogeneousProductChartEquiv_symm_coordinate, map_mul,
    segreProductChartEvaluation_left, segreProductChartEvaluation_right]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Segre.TensorCoordinates
