import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ExternalTensor
import Mathlib.RingTheory.Spectrum.Prime.Module

/-! # External Tensor Support -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ExternalTensorSupport

noncomputable section

/-! A prime supporting an external tensor product contracts to the
support of each finite input. The proof uses the native annihilator
actions of the two product factors. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct

universe u

variable (K R S : Type u) [CommRing K] [CommRing R] [CommRing S] [Algebra K R] [Algebra K S]
  (M N : Type u) [AddCommGroup M] [AddCommGroup N]
  [Module K M] [Module R M] [IsScalarTower K R M]
  [Module K N] [Module S N] [IsScalarTower K S N]

attribute [local instance] ExternalTensor.module

theorem annihilator_left (r : R) (hr : r ∈ Module.annihilator R M) :
    (Algebra.TensorProduct.includeLeft : R →ₐ[K] R ⊗[K] S) r ∈
      Module.annihilator (R ⊗[K] S) (ExternalTensor.obj K R S M N) := by
  apply Module.mem_annihilator.mpr
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul m n =>
    change (r • m) ⊗ₜ[K] ((1 : S) • n) = 0
    rw [Module.mem_annihilator.mp hr m, TensorProduct.zero_tmul]
  | add x y hx hy => rw [smul_add, hx, hy, add_zero]

theorem annihilator_right (s : S) (hs : s ∈ Module.annihilator S N) :
    (Algebra.TensorProduct.includeRight : S →ₐ[K] R ⊗[K] S) s ∈
      Module.annihilator (R ⊗[K] S) (ExternalTensor.obj K R S M N) := by
  apply Module.mem_annihilator.mpr
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul m n =>
    change ((1 : R) • m) ⊗ₜ[K] (s • n) = 0
    rw [Module.mem_annihilator.mp hs n, TensorProduct.tmul_zero]
  | add x y hx hy => rw [smul_add, hx, hy, add_zero]

theorem left [Module.Finite R M] (p : PrimeSpectrum (R ⊗[K] S))
    (hp : p ∈ Module.support (R ⊗[K] S) (ExternalTensor.obj K R S M N)) :
    PrimeSpectrum.comap (Algebra.TensorProduct.includeLeft : R →ₐ[K] R ⊗[K] S).toRingHom p ∈
      Module.support R M := by
  apply Module.mem_support_iff_of_finite.mpr
  intro r hr
  exact Module.annihilator_le_of_mem_support hp (annihilator_left K R S M N r hr)

theorem right [Module.Finite S N] (p : PrimeSpectrum (R ⊗[K] S))
    (hp : p ∈ Module.support (R ⊗[K] S) (ExternalTensor.obj K R S M N)) :
    PrimeSpectrum.comap (Algebra.TensorProduct.includeRight : S →ₐ[K] R ⊗[K] S).toRingHom p ∈
      Module.support S N := by
  apply Module.mem_support_iff_of_finite.mpr
  intro s hs
  exact Module.annihilator_le_of_mem_support hp (annihilator_right K R S M N s hs)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ExternalTensorSupport
