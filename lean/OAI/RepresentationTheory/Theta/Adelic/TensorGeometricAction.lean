import OAI.RepresentationTheory.Theta.Adelic.GeometricGroup

/-! # Tensor Geometric Action -/

namespace OAI.RepresentationTheory.Theta.Adelic.TensorGeometricAction

noncomputable section

/-! Linear tensor actions and their change to the given orthonormal
bases, including the actual standard/dual geometric representation. -/

open scoped Classical _root_.NumberField Kronecker

open _root_.Matrix OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.RationalSU

section Tensor
variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]

theorem tensor_first_mulVec (M : Matrix I I ℂ) (x : I × J → ℂ) (i : I) (j : J) :
    (M ⊗ₖ (1 : Matrix J J ℂ)).mulVec x (i, j) = ∑ k, M i k * x (k, j) := by
  simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.one_apply]

variable [DecidableEq I]

theorem tensor_conjugated_action (B : (Matrix I I ℂ)ˣ) (C : (Matrix J J ℂ)ˣ)
    (M : Matrix I I ℂ) (x : I × J → ℂ) :
    (B.inv ⊗ₖ C.inv).mulVec ((M ⊗ₖ (1 : Matrix J J ℂ)).mulVec x) =
      ((B.inv * M * B.val) ⊗ₖ (1 : Matrix J J ℂ)).mulVec ((B.inv ⊗ₖ C.inv).mulVec x) := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  congr 1
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, mul_one, one_mul,
    Matrix.mul_assoc (B.inv * M) B.val B.inv, B.val_inv, mul_one]

end Tensor

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable (A : BallGeometryData.BallArithmeticData F d m H K)

def geometricActionLinear (g : RationalSU.ArchimedeanSU F H) : BallGeometryData.ComplexPhase A →ₗ[ℂ] BallGeometryData.ComplexPhase A :=
  LinearMap.pi (fun v =>
    LinearMap.comp ((Matrix.mulVecLin ((BallGeometryData.standardMatrix A g v) ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ))).prodMap
      (Matrix.mulVecLin (((BallGeometryData.standardMatrix A g v)⁻¹).transpose ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ))))
        (LinearMap.proj v))

theorem geometricActionLinear_apply (g : RationalSU.ArchimedeanSU F H) (w : BallGeometryData.ComplexPhase A) :
    geometricActionLinear A g w = BallGeometryData.geometricAction A g w := by
  funext v
  apply Prod.ext
  · funext ij
    exact tensor_first_mulVec _ _ ij.1 ij.2
  · funext ij
    exact tensor_first_mulVec _ _ ij.1 ij.2

end

end OAI.RepresentationTheory.Theta.Adelic.TensorGeometricAction
