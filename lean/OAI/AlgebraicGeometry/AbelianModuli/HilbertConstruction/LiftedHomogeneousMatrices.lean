import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.QuotientParameters
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.MultiplicationMatrices

/-! # Lifted Homogeneous Matrices -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LiftedHomogeneousMatrices

noncomputable section

/-!
Multiplication matrices on the lifted monomial index types used by the global
homogeneous quotient parameter schemes. The linear maps and coefficient
naturality are preserved by the index lift.
-/

universe u v

variable (R : Type (max u v)) [CommRing R] (σ : Type v) [Finite σ] (d : ℕ)

def liftedHomogeneousMultiplicationMatrix (i : σ) :
    Matrix (ULift.{u} (Homogeneous.Coordinates.HomogeneousMonomials σ (d + 1))) (ULift.{u} (Homogeneous.Coordinates.HomogeneousMonomials σ d)) R :=
  (Homogeneous.MultiplicationMatrices.homogeneousMultiplicationMatrix R σ d i).submatrix ULift.down ULift.down

omit [Finite σ] in
theorem liftedHomogeneousMultiplicationMatrix_map {A : Type (max u v)} [CommRing A]
    (φ : R →+* A) (i : σ) :
    (liftedHomogeneousMultiplicationMatrix R σ d i).map φ =
      liftedHomogeneousMultiplicationMatrix A σ d i := by
  change ((Homogeneous.MultiplicationMatrices.homogeneousMultiplicationMatrix R σ d i).map φ).submatrix ULift.down ULift.down = _
  rw [Homogeneous.MultiplicationMatrices.homogeneousMultiplicationMatrix_map]
  rfl

theorem liftedHomogeneousMultiplicationMatrix_represents (i : σ)
    (p : MvPolynomial.homogeneousSubmodule σ R d) :
    Matrix.toLin' (liftedHomogeneousMultiplicationMatrix R σ d i)
        (Homogeneous.QuotientParameters.homogeneousLiftedCoordinates σ d R p) =
      Homogeneous.QuotientParameters.homogeneousLiftedCoordinates σ (d + 1) R (Homogeneous.MultiplicationMatrices.homogeneousMultiplyX R σ d i p) := by
  change Matrix.toLin' ((Homogeneous.MultiplicationMatrices.homogeneousMultiplicationMatrix R σ d i).submatrix ULift.down
      (Equiv.ulift : ULift.{u} (Homogeneous.Coordinates.HomogeneousMonomials σ d) ≃ Homogeneous.Coordinates.HomogeneousMonomials σ d)) _ = _
  rw [Matrix.toLin'_submatrix]
  change (fun b : ULift.{u} (Homogeneous.Coordinates.HomogeneousMonomials σ (d + 1)) =>
    Matrix.toLin' (Homogeneous.MultiplicationMatrices.homogeneousMultiplicationMatrix R σ d i) (Homogeneous.Coordinates.homogeneousCoordinates R σ d p) b.down) =
      (fun b => Homogeneous.Coordinates.homogeneousCoordinates R σ (d + 1) (Homogeneous.MultiplicationMatrices.homogeneousMultiplyX R σ d i p) b.down)
  rw [Homogeneous.MultiplicationMatrices.homogeneousMultiplicationMatrix_represents]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LiftedHomogeneousMatrices
