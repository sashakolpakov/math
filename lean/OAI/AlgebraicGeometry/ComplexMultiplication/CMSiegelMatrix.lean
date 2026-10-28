import OAI.AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Symmetric

/-! # CM Siegel Matrix -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM

noncomputable section

/-!
# Siegel matrices and the explicit coordinate theta series

A symmetric complex matrix with positive definite imaginary part gives
the positive bilinear phase used in the analytic construction. This
identifies the terms with the usual matrix exponential formula and
applies the proved gradient-spanning theorem in its full cotangent space.
-/

open scoped Classical _root_.Matrix

variable {ι : Type*} [Fintype ι]

def siegelMatrixForm (Z : Matrix ι ι ℂ) : (ι → ℝ) →L[ℝ] (ι → ℝ) →L[ℝ] ℂ :=
  ∑ i : ι, ∑ j : ι,
    (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ).smulRight
      ((ContinuousLinearMap.proj j : (ι → ℝ) →L[ℝ] ℝ).smulRight (Z i j))

theorem siegelMatrixForm_apply (Z : Matrix ι ι ℂ) (x y : ι → ℝ) :
    siegelMatrixForm Z x y = ∑ i, ∑ j, (x i : ℂ) * ((y j : ℂ) * Z i j) := by
  simp [siegelMatrixForm, Complex.real_smul]

theorem siegelMatrixForm_symmetric (Z : Matrix ι ι ℂ) (hZ : Z.IsSymm) (x y : ι → ℝ) :
    siegelMatrixForm Z x y = siegelMatrixForm Z y x := by
  simp only [siegelMatrixForm_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hZ.apply i j]
  ring

theorem siegelMatrixForm_im (Z : Matrix ι ι ℂ) (x y : ι → ℝ) :
    (siegelMatrixForm Z x y).im = x ⬝ᵥ ((fun i j => (Z i j).im) *ᵥ y) := by
  simp [siegelMatrixForm_apply, dotProduct, Matrix.mulVec, Finset.mul_sum,
    mul_comm, mul_left_comm]

/-- The standard Siegel positivity hypotheses, stated directly on a matrix. -/
structure SiegelMatrix (ι : Type*) [Fintype ι] where
  matrix : Matrix ι ι ℂ
  symmetric : matrix.IsSymm
  imaginary_posDef : Matrix.PosDef (fun i j => (matrix i j).im)

namespace SiegelMatrix

variable (Z : SiegelMatrix ι)

def phase : CMSiegelPhase.CM.SiegelPhase (ι → ℝ) where
  form := siegelMatrixForm Z.matrix
  symmetric := siegelMatrixForm_symmetric Z.matrix Z.symmetric
  positive x hx := by
    rw [siegelMatrixForm_im]
    simpa only [star_trivial] using Z.imaginary_posDef.dotProduct_mulVec_pos hx

theorem thetaTerm_formula (x : ι → ℝ) (z : ι → ℂ) :
    Z.phase.thetaTerm (ThetaCoordinates.CM.thetaCoordinatePairing ι) x z =
      Complex.exp ((Real.pi : ℂ) * Complex.I *
        (∑ i, ∑ j, (x i : ℂ) * ((x j : ℂ) * Z.matrix i j)) +
        (2 * (Real.pi : ℂ) * Complex.I) * (∑ i, (x i : ℂ) * z i)) := by
  simp only [CMSiegelPhase.CM.SiegelPhase.thetaTerm, SiegelMatrix.phase, siegelMatrixForm_apply, ThetaCoordinates.CM.thetaCoordinatePairing_apply]

/-- For every genuine Siegel matrix, actual first derivatives of the
positive-degree sparse coordinate theta series span the whole cotangent space. -/
theorem span_sparseThetaGradients_eq_top :
    Submodule.span ℂ (Set.range (fun an : ThetaCoordinates.CM.thetaCoordinateLattice ι × ℕ =>
      Z.phase.sparseThetaGradient (ThetaCoordinates.CM.thetaCoordinatePairing ι) (ThetaCoordinates.CM.thetaCoordinateLattice ι)
        an.1 an.2)) = ⊤ :=
  ThetaCoordinates.CM.span_coordinate_sparseThetaGradients_eq_top ι Z.phase

end SiegelMatrix

end

end OAI.AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM
