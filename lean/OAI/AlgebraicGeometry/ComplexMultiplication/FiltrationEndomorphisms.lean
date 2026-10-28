import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.LinearAlgebra.Complex.Module

/-! # Filtration Endomorphisms -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.FiltrationEndomorphisms

noncomputable section

/-! # Rational endomorphisms preserving a complexified filtration -/

open scoped TensorProduct

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

/-- This algebra consists of actual rational linear endomorphisms whose complexifications
preserve a specified complex subspace. No geometric realization is asserted. -/
def filtrationEndomorphismAlgebra (F : Submodule ℂ (ℂ ⊗[ℚ] V)) :
    Subalgebra ℚ (Module.End ℚ V) where
  carrier := {f | ∀ z ∈ F, f.baseChange ℂ z ∈ F}
  zero_mem' := by
    intro z hz
    rw [LinearMap.baseChange_zero, LinearMap.zero_apply]
    exact F.zero_mem
  one_mem' := by
    intro z hz
    rw [LinearMap.baseChange_one]
    exact hz
  add_mem' := by
    intro f g hf hg z hz
    rw [LinearMap.baseChange_add, LinearMap.add_apply]
    exact F.add_mem (hf z hz) (hg z hz)
  mul_mem' := by
    intro f g hf hg z hz
    rw [LinearMap.baseChange_mul]
    exact hf _ (hg z hz)
  algebraMap_mem' := by
    intro r z hz
    rw [Module.algebraMap_end_eq_smul_id, LinearMap.baseChange_smul,
      LinearMap.baseChange_id, LinearMap.smul_apply, LinearMap.id_apply]
    exact (F.restrictScalars ℚ).smul_mem r hz

end

end OAI.AlgebraicGeometry.ComplexMultiplication.FiltrationEndomorphisms
