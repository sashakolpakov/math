import OAI.AlgebraicGeometry.HilbertScheme.Presentations.TensorInjectivityExtensions
import Mathlib.RingTheory.Flat.Equalizer

/-! # Reduction Tensor Injectivity -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Flat.ReductionTensorInjectivity

noncomputable section

/-! Once a presentation is injective after reduction and its reduced
cokernel is flat, every module over the reduced ring preserves injectivity. -/

open TensorProduct

universe u v w t z z'
variable {B : Type u} [CommRing B]
variable {K : Type v} [AddCommGroup K] [Module B K]
variable {F : Type w} [AddCommGroup F] [Module B F]
variable {M : Type t} [AddCommGroup M] [Module B M]

theorem lTensor_injective_of_flat_reduction
    (A : Type z) [CommRing A] [Algebra B A]
    (N : Type z') [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower B A N]
    (f : K →ₗ[B] F) (g : F →ₗ[B] M)
    (hfg : Function.Exact f g) (hg : Function.Surjective g)
    (hf : Function.Injective (f.lTensor A)) [Module.Flat A (A ⊗[B] M)] :
    Function.Injective (f.lTensor N) := by
  let fA : A ⊗[B] K →ₗ[A] A ⊗[B] F := AlgebraTensorModule.lTensor A A f
  let gA : A ⊗[B] F →ₗ[A] A ⊗[B] M := AlgebraTensorModule.lTensor A A g
  have hfA : Function.Injective fA := hf
  have hgA : Function.Surjective gA := LinearMap.lTensor_surjective A hg
  have hexA : Function.Exact fA gA := lTensor_exact A hfg hg
  have hinj : Function.Injective (fA.lTensor N) :=
    LinearMap.lTensor_injective_of_exact_of_flat gA hgA fA hfA hexA N
  let eK := AlgebraTensorModule.cancelBaseChange B A A N K
  let eF := AlgebraTensorModule.cancelBaseChange B A A N F
  have he (x : N ⊗[A] (A ⊗[B] K)) :
      f.lTensor N (eK x) = eF (fA.lTensor N x) := by
    exact LinearMap.congr_fun (AlgebraTensorModule.lTensor_comp_cancelBaseChange B A A f) x
  intro x y hxy
  apply eK.symm.injective
  apply hinj
  apply eF.injective
  rw [← he, ← he, eK.apply_symm_apply, eK.apply_symm_apply]
  exact hxy

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Flat.ReductionTensorInjectivity
