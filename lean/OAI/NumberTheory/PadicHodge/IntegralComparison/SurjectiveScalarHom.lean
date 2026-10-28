import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Algebra.Algebra.Tower

/-! # Surjective Scalar Hom -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SurjectiveScalarHom

noncomputable section

/-! For a surjective scalar map, linearity over the quotient is
equivalent to linearity over the original ring. -/

universe u
variable (R Q : Type u) [CommRing R] [CommRing Q] [Algebra R Q]
  (hQ : Function.Surjective (algebraMap R Q))
  (M N : Type u) [AddCommGroup M] [AddCommGroup N]
  [Module R M] [Module Q M] [IsScalarTower R Q M]
  [Module R N] [Module Q N] [IsScalarTower R Q N]

def lift (f : M →ₗ[R] N) : M →ₗ[Q] N where
  toFun := f
  map_add' := f.map_add
  map_smul' q m := by
    obtain ⟨r, rfl⟩ := hQ q
    change f ((algebraMap R Q r) • m) = (algebraMap R Q r) • f m
    rw [IsScalarTower.algebraMap_smul Q, IsScalarTower.algebraMap_smul Q]
    exact f.map_smul r m

def equiv : (M →ₗ[Q] N) ≃ₗ[R] (M →ₗ[R] N) where
  toFun := LinearMap.restrictScalars R
  invFun := lift R Q hQ M N
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem equiv_apply (f : M →ₗ[Q] N) (m : M) : equiv R Q hQ M N f m = f m := rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SurjectiveScalarHom
