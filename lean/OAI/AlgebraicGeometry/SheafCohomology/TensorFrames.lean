import OAI.AlgebraicGeometry.DivisorClass.Chern.FramesFrame
import Mathlib.LinearAlgebra.TensorProduct.Basic

/-! # Tensor Frames -/

namespace OAI.AlgebraicGeometry.SheafCohomology.TensorFrames.Projective

noncomputable section

/-! Rank-one tensor frames and their genuine transition units. -/

open OAI.AlgebraicGeometry.DivisorClass.Chern.FramesFrame.Construction
open scoped TensorProduct

variable {R M N : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- The local frame of a tensor product is the product of the two coordinates. -/
def tensorFrame (e : M ≃ₗ[R] R) (f : N ≃ₗ[R] R) : M ⊗[R] N ≃ₗ[R] R :=
  (TensorProduct.congr e f).trans (TensorProduct.lid R R)

@[simp] theorem tensorFrame_tmul (e : M ≃ₗ[R] R) (f : N ≃ₗ[R] R) (x : M) (y : N) :
    tensorFrame e f (x ⊗ₜ[R] y) = e x * f y := by
  simp [tensorFrame]

theorem tensorFrame_symm_one (e : M ≃ₗ[R] R) (f : N ≃ₗ[R] R) :
    (tensorFrame e f).symm 1 = e.symm 1 ⊗ₜ[R] f.symm 1 := by
  apply (tensorFrame e f).injective
  simp

/-- Changing the two local frames multiplies their transition units. -/
theorem tensorFrame_transition (e e' : M ≃ₗ[R] R) (f f' : N ≃ₗ[R] R) :
    DivisorClass.Chern.FramesFrame.Construction.frameTransitionUnit (tensorFrame e f) (tensorFrame e' f') =
      DivisorClass.Chern.FramesFrame.Construction.frameTransitionUnit e e' * DivisorClass.Chern.FramesFrame.Construction.frameTransitionUnit f f' := by
  apply Units.ext
  change tensorFrame e f ((tensorFrame e' f').symm 1) =
    e (e'.symm 1) * f (f'.symm 1)
  rw [tensorFrame_symm_one, tensorFrame_tmul]

/-- Multiplication of transition units only requires the coordinate formula
on pure tensors, so it also applies after sheafification. -/
theorem frameTransitionUnit_of_product_coordinates
    {T : Type*} [AddCommGroup T] [Module R T]
    (E F : T ≃ₗ[R] R) (e e' : M ≃ₗ[R] R) (f f' : N ≃ₗ[R] R)
    (t : M → N → T)
    (hE : ∀ m n, E (t m n) = e m * f n)
    (hF : ∀ m n, F (t m n) = e' m * f' n) :
    DivisorClass.Chern.FramesFrame.Construction.frameTransitionUnit E F = DivisorClass.Chern.FramesFrame.Construction.frameTransitionUnit e e' * DivisorClass.Chern.FramesFrame.Construction.frameTransitionUnit f f' := by
  have ht : t (e'.symm 1) (f'.symm 1) = F.symm 1 := by
    apply F.injective
    rw [hF, e'.apply_symm_apply, f'.apply_symm_apply, one_mul, F.apply_symm_apply]
  apply Units.ext
  change E (F.symm 1) = e (e'.symm 1) * f (f'.symm 1)
  rw [← ht, hE]

end

end OAI.AlgebraicGeometry.SheafCohomology.TensorFrames.Projective
