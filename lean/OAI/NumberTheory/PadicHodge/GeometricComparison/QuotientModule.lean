import Mathlib.RingTheory.IsTensorProduct
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Quotient Module -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.QuotientModule.QuotientModuleBaseChange

noncomputable section

/-! A module base change along a surjective coefficient map has precisely the coefficient-ideal kernel. -/

open scoped TensorProduct

universe u v w

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
  {M : Type v} [AddCommGroup M] [Module R M]
  {N : Type w} [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
  (f : M →ₗ[R] N) (hf : IsBaseChange S f)
  (hS : Function.Surjective (algebraMap R S))

include hf hS

theorem surjective : Function.Surjective f := by
  intro y
  obtain ⟨t, rfl⟩ := hf.equiv.surjective y
  induction t using TensorProduct.inductionOn with
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by simp only [map_add, ha, hb]⟩
  | tmul s x =>
    obtain ⟨r, rfl⟩ := hS s
    exact ⟨r • x, by rw [map_smul, hf.equiv_tmul, IsScalarTower.algebraMap_smul]⟩

theorem ker_eq : f.ker = RingHom.ker (algebraMap R S) • ⊤ := by
  let I := RingHom.ker (algebraMap R S)
  let e : (R ⧸ I) ≃ₐ[R] S := Ideal.quotientKerAlgEquivOfSurjective
    (f := Algebra.ofId R S) hS
  let E : (R ⧸ I) ⊗[R] M ≃ₗ[R] N :=
    (e.toLinearEquiv.rTensor M).trans (hf.equiv.restrictScalars R)
  have he (x : M) : E (1 ⊗ₜ[R] x) = f x := by
    change hf.equiv (e.toLinearEquiv.rTensor M (1 ⊗ₜ[R] x)) = f x
    rw [LinearEquiv.rTensor_tmul]
    change hf.equiv (e 1 ⊗ₜ[R] x) = f x
    rw [map_one, hf.equiv_tmul, one_smul]
  ext x
  change f x = 0 ↔ x ∈ RingHom.ker (algebraMap R S) • ⊤
  rw [← he, E.map_eq_zero_iff]
  change x ∈ (TensorProduct.mk R (R ⧸ I) M 1).ker ↔ _
  rw [LinearMap.ker_tensorProductMk]

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.QuotientModule.QuotientModuleBaseChange
