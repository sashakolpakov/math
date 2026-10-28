import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.Coordinates
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! # Multiplication Matrices -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.MultiplicationMatrices

noncomputable section

/-!
Multiplication by each polynomial variable is an explicit coefficient-natural
matrix between the finite homogeneous coordinate modules. These are the
linear maps used in graded-ideal incidence conditions.
-/

universe u v

variable (R : Type u) [CommRing R] (σ : Type v) [Finite σ] (d : ℕ)

def homogeneousMultiplyX (i : σ) :
    MvPolynomial.homogeneousSubmodule σ R d →ₗ[R]
      MvPolynomial.homogeneousSubmodule σ R (d + 1) where
  toFun p := ⟨MvPolynomial.X i * p.val, by
    change (MvPolynomial.X i * p.val).IsHomogeneous (d + 1)
    simpa only [Nat.add_comm] using (MvPolynomial.isHomogeneous_X R i).mul p.property⟩
  map_add' p q := Subtype.ext (mul_add _ _ _)
  map_smul' r p := Subtype.ext (mul_smul_comm r _ _)

def homogeneousMultiplicationMatrix (i : σ) :
    Matrix (Coordinates.HomogeneousMonomials σ (d + 1)) (Coordinates.HomogeneousMonomials σ d) R :=
  fun b a => AddMonoidAlgebra.coeff ((MvPolynomial.X i * MvPolynomial.monomial a.val 1)) (b.val)

omit [Finite σ] in
theorem homogeneousMultiplicationMatrix_map {A : Type*} [CommRing A] (φ : R →+* A) (i : σ) :
    (homogeneousMultiplicationMatrix R σ d i).map φ = homogeneousMultiplicationMatrix A σ d i := by
  ext b a
  change φ (AddMonoidAlgebra.coeff ((MvPolynomial.X i * MvPolynomial.monomial a.val 1)) (b.val)) = _
  rw [← MvPolynomial.coeff_map, map_mul, MvPolynomial.map_X, MvPolynomial.map_monomial, map_one]
  rfl

theorem homogeneousCoordinates_symm_single (a : Coordinates.HomogeneousMonomials σ d) (r : R) :
    (Coordinates.homogeneousCoordinates R σ d).symm (Pi.single a r) =
      ⟨MvPolynomial.monomial a.val r, MvPolynomial.isHomogeneous_monomial r a.property⟩ := by
  apply (Coordinates.homogeneousCoordinates R σ d).injective
  rw [LinearEquiv.apply_symm_apply, Coordinates.homogeneousCoordinates_monomial]

theorem homogeneousMultiplicationMatrix_toMatrix (i : σ) :
    homogeneousMultiplicationMatrix R σ d i =
      LinearMap.toMatrix' ((Coordinates.homogeneousCoordinates R σ (d + 1)).toLinearMap.comp
        ((homogeneousMultiplyX R σ d i).comp (Coordinates.homogeneousCoordinates R σ d).symm.toLinearMap)) := by
  classical
  ext b a
  rw [LinearMap.toMatrix'_apply]
  change AddMonoidAlgebra.coeff ((MvPolynomial.X i * MvPolynomial.monomial a.val 1)) (b.val) =
    Coordinates.homogeneousCoordinates R σ (d + 1)
      (homogeneousMultiplyX R σ d i ((Coordinates.homogeneousCoordinates R σ d).symm (Pi.single a 1))) b
  rw [homogeneousCoordinates_symm_single, Coordinates.homogeneousCoordinates_apply]
  rfl

theorem homogeneousMultiplicationMatrix_represents (i : σ)
    (p : MvPolynomial.homogeneousSubmodule σ R d) :
    Matrix.toLin' (homogeneousMultiplicationMatrix R σ d i) (Coordinates.homogeneousCoordinates R σ d p) =
      Coordinates.homogeneousCoordinates R σ (d + 1) (homogeneousMultiplyX R σ d i p) := by
  classical
  rw [homogeneousMultiplicationMatrix_toMatrix, Matrix.toLin'_toMatrix']
  change Coordinates.homogeneousCoordinates R σ (d + 1)
    (homogeneousMultiplyX R σ d i
      ((Coordinates.homogeneousCoordinates R σ d).symm (Coordinates.homogeneousCoordinates R σ d p))) = _
  rw [LinearEquiv.symm_apply_apply]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.MultiplicationMatrices
