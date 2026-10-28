import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveChart.Algebra
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Segre.NormalizedCoordinates
import Mathlib.RingTheory.TensorProduct.Maps

/-! # Product Chart Maps -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Segre.ProductChartMaps

noncomputable section

/-! The two explicit algebra maps between a Segre chart and a product of standard projective charts. -/

open _root_.MvPolynomial
open scoped TensorProduct

universe u

variable (R : Type u) [CommRing R] {n m : ℕ} (i : Fin (n + 1)) (j : Fin (m + 1))

abbrev SegreFiniteChartRing :=
  NormalizedCoordinates.SegreChartRing R (ULift.up i : ULift.{u} (Fin (n + 1))) (ULift.up j : ULift.{u} (Fin (m + 1)))

abbrev ProjectiveProductChartRing := ProjectiveChart.Evaluation.projectiveChartRing R n i ⊗[R] ProjectiveChart.Evaluation.projectiveChartRing R m j

def segreProductChartRow : ProjectiveChart.Evaluation.projectiveChartRing R n i →ₐ[R] SegreFiniteChartRing R i j :=
  ProjectiveChart.Algebra.projectiveChartEvaluationAlg
    (fun a => NormalizedCoordinates.segreRowCoordinate R (ULift.up i) (ULift.up j) (ULift.up a)) i
      (by simp [NormalizedCoordinates.segreRowCoordinate])

def segreProductChartColumn : ProjectiveChart.Evaluation.projectiveChartRing R m j →ₐ[R] SegreFiniteChartRing R i j :=
  ProjectiveChart.Algebra.projectiveChartEvaluationAlg
    (fun b => NormalizedCoordinates.segreColumnCoordinate R (ULift.up i) (ULift.up j) (ULift.up b)) j
      (by simp [NormalizedCoordinates.segreColumnCoordinate])

def segreProductChartForward : ProjectiveProductChartRing R i j →ₐ[R] SegreFiniteChartRing R i j :=
  Algebra.TensorProduct.lift (segreProductChartRow R i j) (segreProductChartColumn R i j)
    (fun _ _ => Commute.all _ _)

def segreProductChartInverse : SegreFiniteChartRing R i j →ₐ[R] ProjectiveProductChartRing R i j :=
  aeval (Sum.elim
    (fun a => Algebra.TensorProduct.includeLeft (R := R) (S := R)
      (HilbertScheme.Presentations.Polynomial.Dehomogenization.PolynomialProjective.dehomogenize i (X a.val.down)))
    (fun b => Algebra.TensorProduct.includeRight (R := R)
      (HilbertScheme.Presentations.Polynomial.Dehomogenization.PolynomialProjective.dehomogenize j (X b.val.down))))

theorem segreProductChartRow_coordinate (a : Fin (n + 1)) :
    segreProductChartRow R i j (HilbertScheme.Presentations.Polynomial.Dehomogenization.PolynomialProjective.dehomogenize i (X a)) =
      NormalizedCoordinates.segreRowCoordinate R (ULift.up i) (ULift.up j) (ULift.up a) :=
  ProjectiveChart.Algebra.projectiveChartEvaluationAlg_coordinate _ _ _ _

theorem segreProductChartColumn_coordinate (b : Fin (m + 1)) :
    segreProductChartColumn R i j (HilbertScheme.Presentations.Polynomial.Dehomogenization.PolynomialProjective.dehomogenize j (X b)) =
      NormalizedCoordinates.segreColumnCoordinate R (ULift.up i) (ULift.up j) (ULift.up b) :=
  ProjectiveChart.Algebra.projectiveChartEvaluationAlg_coordinate _ _ _ _

theorem segreProductChartForward_left (x : ProjectiveChart.Evaluation.projectiveChartRing R n i) :
    segreProductChartForward R i j (Algebra.TensorProduct.includeLeft (S := R) x) = segreProductChartRow R i j x := by
  exact AlgHom.congr_fun (Algebra.TensorProduct.lift_comp_includeLeft
    (segreProductChartRow R i j) (segreProductChartColumn R i j) (fun _ _ => Commute.all _ _)) x

theorem segreProductChartForward_right (x : ProjectiveChart.Evaluation.projectiveChartRing R m j) :
    segreProductChartForward R i j (Algebra.TensorProduct.includeRight x) = segreProductChartColumn R i j x := by
  exact AlgHom.congr_fun (Algebra.TensorProduct.lift_comp_includeRight'
    (segreProductChartRow R i j) (segreProductChartColumn R i j) (fun _ _ => Commute.all _ _)) x

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Segre.ProductChartMaps
