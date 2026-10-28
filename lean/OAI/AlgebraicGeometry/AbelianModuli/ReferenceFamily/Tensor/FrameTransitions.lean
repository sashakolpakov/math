import OAI.AlgebraicGeometry.DivisorClass.Chern.FramesFrame
import Mathlib.LinearAlgebra.TensorProduct.Map

/-! # Frame Transitions -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Tensor.FrameTransitions

noncomputable section

/-! Transition units of actual tensor-product frames are products of
the two transition units. This is the rank-one algebra used for Chern
additivity on tensor products of module sheaves. -/

open OAI.AlgebraicGeometry.DivisorClass.Chern.FramesFrame.Construction
open scoped TensorProduct

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

def tensorFrame (e : M ≃ₗ[R] R) (f : N ≃ₗ[R] R) : M ⊗[R] N ≃ₗ[R] R :=
  (TensorProduct.congr e f).trans (TensorProduct.lid R R)

theorem tensorFrame_tmul (e : M ≃ₗ[R] R) (f : N ≃ₗ[R] R) (m : M) (n : N) :
    tensorFrame e f (m ⊗ₜ[R] n) = e m * f n := rfl

theorem tensorFrame_generator (e : M ≃ₗ[R] R) (f : N ≃ₗ[R] R) :
    (tensorFrame e f).symm 1 = e.symm 1 ⊗ₜ[R] f.symm 1 := by
  apply (tensorFrame e f).injective
  rw [LinearEquiv.apply_symm_apply, tensorFrame_tmul,
    LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, one_mul]

theorem frameTransitionUnit_tensor (e e' : M ≃ₗ[R] R) (f f' : N ≃ₗ[R] R) :
    DivisorClass.Chern.FramesFrame.Construction.frameTransitionUnit (tensorFrame e f) (tensorFrame e' f') =
      DivisorClass.Chern.FramesFrame.Construction.frameTransitionUnit e e' * DivisorClass.Chern.FramesFrame.Construction.frameTransitionUnit f f' := by
  apply Units.ext
  change tensorFrame e f ((tensorFrame e' f').symm 1) = e (e'.symm 1) * f (f'.symm 1)
  rw [tensorFrame_generator, tensorFrame_tmul]

theorem frameTransitionUnit_bilinear {P : Type*} [AddCommGroup P] [Module R P]
    (B : M →ₗ[R] N →ₗ[R] P) (e e' : M ≃ₗ[R] R) (f f' : N ≃ₗ[R] R) (c c' : P ≃ₗ[R] R)
    (hc : ∀ x y, c (B x y) = e x * f y) (hc' : ∀ x y, c' (B x y) = e' x * f' y) :
    DivisorClass.Chern.FramesFrame.Construction.frameTransitionUnit c c' = DivisorClass.Chern.FramesFrame.Construction.frameTransitionUnit e e' * DivisorClass.Chern.FramesFrame.Construction.frameTransitionUnit f f' := by
  have hgen : c'.symm 1 = B (e'.symm 1) (f'.symm 1) := by
    apply c'.injective
    rw [LinearEquiv.apply_symm_apply, hc', LinearEquiv.apply_symm_apply,
      LinearEquiv.apply_symm_apply, one_mul]
  apply Units.ext
  change c (c'.symm 1) = e (e'.symm 1) * f (f'.symm 1)
  rw [hgen, hc]

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Tensor.FrameTransitions
