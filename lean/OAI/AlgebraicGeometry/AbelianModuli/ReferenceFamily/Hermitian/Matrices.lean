import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Hermitian.Reconstruction
import Mathlib.LinearAlgebra.Matrix.SesquilinearForm

/-! # Matrices -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Hermitian.Matrices.TraceReconstruction

noncomputable section

/-! Bundle the reconstructed Hermitian form and compute its actual
matrix in coordinates. Nondegeneracy gives a nonzero determinant. -/

variable {E V : Type*} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
  [AddCommGroup V] [Module ℚ V] [Module E V] [IsScalarTower ℚ E V]

def hermitianForm (ξ : E) (ψ : V →ₗ[ℚ] V →ₗ[ℚ] ℚ) (hψ : Reconstruction.TraceReconstruction.RosatiBalanced (E := E) ψ) :
    V →ₗ[E] V →ₛₗ[(ComplexMultiplication.CM.TraceForm.cmFieldConjugation E).toRingHom] E where
  toFun x := {
    toFun := Reconstruction.TraceReconstruction.hermitianCoefficient ξ ψ x
    map_add' y z := Reconstruction.TraceReconstruction.hermitianCoefficient_add_right ξ ψ x y z
    map_smul' a y := Reconstruction.TraceReconstruction.hermitianCoefficient_smul_right ξ ψ hψ a x y }
  map_add' x z := by ext y; exact Reconstruction.TraceReconstruction.hermitianCoefficient_add_left ξ ψ x z y
  map_smul' a x := by ext y; exact Reconstruction.TraceReconstruction.hermitianCoefficient_smul_left ξ ψ a x y

theorem hermitianForm_apply (ξ : E) (ψ : V →ₗ[ℚ] V →ₗ[ℚ] ℚ)
    (hψ : Reconstruction.TraceReconstruction.RosatiBalanced (E := E) ψ) (x y : V) :
    hermitianForm ξ ψ hψ x y = Reconstruction.TraceReconstruction.hermitianCoefficient ξ ψ x y := rfl

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def hermitianMatrix (ξ : E) (ψ : (ι → E) →ₗ[ℚ] (ι → E) →ₗ[ℚ] ℚ)
    (hψ : Reconstruction.TraceReconstruction.RosatiBalanced (E := E) ψ) : Matrix ι ι E :=
  LinearMap.toMatrixₛₗ₂' E (hermitianForm ξ ψ hψ)

theorem hermitianMatrix_apply (ξ : E) (ψ : (ι → E) →ₗ[ℚ] (ι → E) →ₗ[ℚ] ℚ)
    (hψ : Reconstruction.TraceReconstruction.RosatiBalanced (E := E) ψ) (i j : ι) :
    hermitianMatrix ξ ψ hψ i j = Reconstruction.TraceReconstruction.hermitianCoefficient ξ ψ (Pi.single i 1) (Pi.single j 1) := rfl

theorem hermitianMatrix_symmetry (ξ : E) (hξ : ComplexMultiplication.CM.TraceForm.cmFieldConjugation E ξ = -ξ)
    (ψ : (ι → E) →ₗ[ℚ] (ι → E) →ₗ[ℚ] ℚ) (hψ : Reconstruction.TraceReconstruction.RosatiBalanced (E := E) ψ)
    (hAlt : ∀ x, ψ x x = 0) (i j : ι) :
    hermitianMatrix ξ ψ hψ i j = ComplexMultiplication.CM.TraceForm.cmFieldConjugation E (hermitianMatrix ξ ψ hψ j i) :=
  (Reconstruction.TraceReconstruction.hermitianCoefficient_symmetry ξ hξ ψ hψ hAlt (Pi.single j 1) (Pi.single i 1)).symm

theorem hermitianMatrix_evaluate (ξ : E) (ψ : (ι → E) →ₗ[ℚ] (ι → E) →ₗ[ℚ] ℚ)
    (hψ : Reconstruction.TraceReconstruction.RosatiBalanced (E := E) ψ) (x y : ι → E) :
    (∑ i, ∑ j, x i * hermitianMatrix ξ ψ hψ i j * ComplexMultiplication.CM.TraceForm.cmFieldConjugation E (y j)) =
      Reconstruction.TraceReconstruction.hermitianCoefficient ξ ψ x y := by
  have h := LinearMap.toLinearMap₂'Aux_toMatrix₂Aux E (hermitianForm ξ ψ hψ)
  have he := congrArg (fun f => f x y) h
  change (∑ i, ∑ j, ComplexMultiplication.CM.TraceForm.cmFieldConjugation E (y j) * (x i * hermitianMatrix ξ ψ hψ i j)) =
    Reconstruction.TraceReconstruction.hermitianCoefficient ξ ψ x y at he
  rw [← he]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem hermitianMatrix_det_ne_zero (ξ : E) (hξ : ξ ≠ 0)
    (ψ : (ι → E) →ₗ[ℚ] (ι → E) →ₗ[ℚ] ℚ) (hψ : Reconstruction.TraceReconstruction.RosatiBalanced (E := E) ψ)
    (hnd : ∀ x, (∀ y, ψ x y = 0) → x = 0) : (hermitianMatrix ξ ψ hψ).det ≠ 0 := by
  apply Matrix.separatingLeft_iff_det_ne_zero.mp
  apply Matrix.separatingLeft_def.mpr
  intro x hx
  apply Reconstruction.TraceReconstruction.hermitianCoefficient_nondegenerate ξ hξ ψ hnd x
  intro y
  rw [← hermitianMatrix_evaluate ξ ψ hψ x y]
  have h := hx (fun j => ComplexMultiplication.CM.TraceForm.cmFieldConjugation E (y j))
  simpa only [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc] using h

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Hermitian.Matrices.TraceReconstruction
