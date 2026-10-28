import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.IsTensorProduct

/-! # Basis Base Change -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BasisBaseChange

noncomputable section

/-!
# IntegralComparison: a map preserving two bases exhibits scalar extension
-/

open scoped TensorProduct

universe u v w z t

variable {R : Type u} {S : Type v} [CommSemiring R] [CommSemiring S] [Algebra R S]
  {M : Type w} {N : Type z} [AddCommMonoid M] [AddCommMonoid N]
  [Module R M] [Module R N] [Module S N] [IsScalarTower R S N]
  {ι : Type t} (f : M →ₗ[R] N) (b : Module.Basis ι R M) (c : Module.Basis ι S N)

theorem isBaseChange (hf : ∀ i, f (b i) = c i) : IsBaseChange S f := by
  let e := (b.baseChange S).equiv c (Equiv.refl _)
  have he : (e.toLinearMap.restrictScalars R).comp (TensorProduct.mk R S M 1) = f := by
    apply b.ext
    intro i
    change e (1 ⊗ₜ[R] b i) = f (b i)
    rw [← Module.Basis.baseChange_apply, Module.Basis.equiv_apply, Equiv.refl_apply, hf]
  exact IsBaseChange.of_equiv e (fun x => LinearMap.congr_fun he x)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BasisBaseChange
