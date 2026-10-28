import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! # Rational Regular Element -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.RationalRegularElement.Construction

noncomputable section

/-! An injective integral multiplication map stays injective after rationalization.
Finite-dimensionality then makes the rationalized element a unit. -/

open scoped TensorProduct

universe u

theorem rationalized_isRightRegular {R : Type u} [Ring R] (a : R) (ha : IsRightRegular a) :
    IsRightRegular ((1 : ℚ) ⊗ₜ[ℤ] a : TensorProduct ℤ ℚ R) := by
  have : Module.Flat ℤ ℚ := IsLocalization.flat ℚ (nonZeroDivisors ℤ)
  let f := LinearMap.mulRight ℤ a
  have hi : Function.Injective (f.baseChange ℚ) := by
    rw [LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap _ ha
  have he : f.baseChange ℚ = LinearMap.mulRight ℚ ((1 : ℚ) ⊗ₜ[ℤ] a) := by
    ext x
    change (1 : ℚ) ⊗ₜ[ℤ] (x * a) = ((1 : ℚ) ⊗ₜ[ℤ] x) * ((1 : ℚ) ⊗ₜ[ℤ] a)
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rw [he] at hi
  exact hi

theorem isUnit_of_isRightRegular_finiteDimensional
    {D : Type u} [Ring D] [Algebra ℚ D] [FiniteDimensional ℚ D]
    (a : D) (ha : IsRightRegular a) : IsUnit a := by
  let f := LinearMap.mulRight ℚ a
  have hs : Function.Surjective f := (LinearMap.injective_iff_surjective).mp ha
  exact IsUnit.isUnit_iff_mulRight_bijective.mpr ⟨ha, hs⟩

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.RationalRegularElement.Construction
