import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann.Charts
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Algebra.MvPolynomial.Eval

/-! # Polynomial Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann.PolynomialCoordinates

noncomputable section

/-! Polynomial coordinates for the finite-free quotient charts. -/

universe u v

variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A] {k l : ℕ}

/-- A finite-free quotient chart is parametrized by a rectangular matrix. -/
def grassmannChartMatrixEquiv : Charts.GrassmannChart A (Fin l → A) k ≃ Matrix (Fin k) (Fin l) A :=
  Charts.grassmannChartCoordinates.trans LinearMap.toMatrix'.toEquiv

/-- Algebra maps out of a polynomial ring classify the points of the quotient chart. -/
def grassmannChartPolynomialEquiv :
    (MvPolynomial (Fin k × Fin l) R →ₐ[R] A) ≃ Charts.GrassmannChart A (Fin l → A) k where
  toFun φ := grassmannChartMatrixEquiv.symm (fun i j => φ (MvPolynomial.X (i, j)))
  invFun c := MvPolynomial.aeval (fun ij => grassmannChartMatrixEquiv c ij.1 ij.2)
  left_inv φ := by
    ext ⟨i, j⟩
    rw [MvPolynomial.aeval_X]
    exact congrFun (congrFun (grassmannChartMatrixEquiv.apply_symm_apply _) i) j
  right_inv c := by
    apply grassmannChartMatrixEquiv.injective
    ext i j
    simp

/-- The coefficient of a chart point is the value assigned to its polynomial coordinate. -/
theorem grassmannChartPolynomialEquiv_matrix
    (φ : MvPolynomial (Fin k × Fin l) R →ₐ[R] A) (i : Fin k) (j : Fin l) :
    grassmannChartMatrixEquiv (grassmannChartPolynomialEquiv φ) i j = φ (MvPolynomial.X (i, j)) := by
  exact congrFun (congrFun (grassmannChartMatrixEquiv.apply_symm_apply _) i) j

/-- The universal quotient chart point over its polynomial coordinate algebra. -/
def universalGrassmannChart (R : Type u) [CommRing R] (k l : ℕ) :
    Charts.GrassmannChart (MvPolynomial (Fin k × Fin l) R)
      (Fin l → MvPolynomial (Fin k × Fin l) R) k :=
  grassmannChartPolynomialEquiv (AlgHom.id R _)

theorem universalGrassmannChart_matrix (R : Type u) [CommRing R] (k l : ℕ)
    (i : Fin k) (j : Fin l) :
    grassmannChartMatrixEquiv (universalGrassmannChart R k l) i j = MvPolynomial.X (i, j) :=
  grassmannChartPolynomialEquiv_matrix (AlgHom.id R _) i j

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann.PolynomialCoordinates
