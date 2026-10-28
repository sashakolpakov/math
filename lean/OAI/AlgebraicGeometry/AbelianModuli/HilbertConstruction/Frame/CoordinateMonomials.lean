import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Frame.CoordinateExponents
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DeterminantFrameLinearMap

/-! # Coordinate Monomials -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Frame.CoordinateMonomials

noncomputable section

/-! The exponent formula for a frame coordinate evaluates to the
corresponding coordinate of the determinant normalization map. -/
open scoped BigOperators Classical
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type u} [CommRing R] {r m : ℕ}

theorem labeledDeterminant_update_eq_basis (σ : Fin r → Fin m)
    (v : Fin m → Fin r → R) (k : Fin r) (z : Fin m) :
    LabeledDeterminantPolynomials.labeledDeterminant (Function.update σ k z) v =
      (Pi.basisFun R (Fin r)).det (Function.update (fun j => v (σ j)) k (v z)) := by
  rw [LabeledDeterminantPolynomials.labeledDeterminant_eq_basis]
  congr 1
  funext j
  by_cases h : j = k
  · subst j
    simp only [Function.update_self]
  · simp only [Function.update_of_ne h]

theorem frameCoordinateExponent_monomial (σ : Fin r → Fin m)
    (v : Fin m → Fin r → R) (e z : Fin m) (k : Fin r) :
    Balanced.MonomialAlgebra.exponentMonomial (fun τ => LabeledDeterminantPolynomials.labeledDeterminant τ v) (CoordinateExponents.frameCoordinateExponent σ e z k) =
      ProjectiveFrame.DeterminantCoordinates.projectiveFrameDeterminantCoordinates (Pi.basisFun R (Fin r))
        (fun j => v (σ j)) (v e) (v z) k := by
  have hsingle (j : Fin r → Fin m) :
      Balanced.MonomialAlgebra.exponentMonomial (fun τ => LabeledDeterminantPolynomials.labeledDeterminant τ v) (Pi.single j 1) = LabeledDeterminantPolynomials.labeledDeterminant j v := by
    simp [Balanced.MonomialAlgebra.exponentMonomial, Pi.single_apply]
  simp only [CoordinateExponents.frameCoordinateExponent, Balanced.MonomialAlgebra.exponentMonomial_add, MonomialFiniteSums.exponentMonomial_sum,
    hsingle, labeledDeterminant_update_eq_basis,
    ProjectiveFrame.DeterminantCoordinates.projectiveFrameDeterminantCoordinates]
  congr!

theorem frameCoordinateExponent_linearMap (σ : Fin r → Fin m)
    (v : Fin m → Fin r → R) (e z : Fin m) (k : Fin r) :
    Balanced.MonomialAlgebra.exponentMonomial (fun τ => LabeledDeterminantPolynomials.labeledDeterminant τ v) (CoordinateExponents.frameCoordinateExponent σ e z k) =
      DeterminantFrameLinearMap.determinantFrameLinearMap (Pi.basisFun R (Fin r))
        (fun j => v (σ j)) (v e) (v z) k := by
  rw [DeterminantFrameLinearMap.determinantFrameLinearMap_apply, frameCoordinateExponent_monomial]

theorem frameCoordinateExponent_polynomial (σ : Fin r → Fin m)
    (e z : Fin m) (k : Fin r) :
    Balanced.MonomialAlgebra.exponentMonomial (LabeledDeterminantPolynomials.labeledDeterminantPolynomial R) (CoordinateExponents.frameCoordinateExponent σ e z k) =
      ProjectiveFrame.DeterminantCoordinates.projectiveFrameDeterminantCoordinates
        (Pi.basisFun (MvPolynomial (Fin m × Fin r) R) (Fin r))
        (fun j l => MvPolynomial.X (σ j, l))
        (fun l => MvPolynomial.X (e, l)) (fun l => MvPolynomial.X (z, l)) k :=
  frameCoordinateExponent_monomial σ (fun i j => MvPolynomial.X (i, j)) e z k

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Frame.CoordinateMonomials
