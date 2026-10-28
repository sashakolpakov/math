import Mathlib.RingTheory.TensorProduct.Maps

/-! # Tensor Evaluation -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.TensorEvaluation.TestTransport

noncomputable section

/-! Scalar formulas for evaluation of a tensor algebra, stated before
specializing either factor to a completed coefficient algebra. -/

open scoped TensorProduct

variable {R A B C : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra R A] [Algebra R B] [Algebra R C]

def tensorEvaluation (f : A →ₐ[R] C) (g : B →ₐ[R] C) : A ⊗[R] B →ₐ[R] C :=
  Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _)

theorem tensorEvaluation_tmul (f : A →ₐ[R] C) (g : B →ₐ[R] C) (a : A) (b : B) :
    tensorEvaluation f g (a ⊗ₜ[R] b) = f a * g b := rfl

theorem tensorEvaluation_smul (f : A →ₐ[R] C) (g : B →ₐ[R] C) (a : A) (x : A ⊗[R] B) :
    tensorEvaluation f g (a • x) = f a * tensorEvaluation f g x := by
  rw [Algebra.smul_def, map_mul]
  congr 1
  change tensorEvaluation f g (a ⊗ₜ[R] 1) = f a
  rw [tensorEvaluation_tmul, map_one, mul_one]

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.TensorEvaluation.TestTransport
