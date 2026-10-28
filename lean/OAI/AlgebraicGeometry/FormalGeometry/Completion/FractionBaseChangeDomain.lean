import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Ideal

/-! # Fraction Base Change Domain -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.FractionBaseChangeDomain.Construction

noncomputable section

/-! # Completion: fraction-field base change of a faithfully embedded domain -/

open scoped TensorProduct nonZeroDivisors

universe u v w

variable (R : Type u) (K : Type v) (T : Type w)
  [CommRing R] [Field K] [Algebra R K] [IsFractionRing R K]
  [CommRing T] [IsDomain T] [Algebra R T] [FaithfulSMul R T]

/-- Nonzero base elements remain nonzero in the domain. -/
theorem fraction_tensor_denominators :
    Algebra.algebraMapSubmonoid T R⁰ ≤ nonZeroDivisors T :=
  map_le_nonZeroDivisors_of_injective (algebraMap R T) (FaithfulSMul.algebraMap_injective R T) le_rfl

/-- The actual tensor product with the fraction field remains a domain. -/
theorem fraction_tensor_isDomain : IsDomain (K ⊗[R] T) := by
  let : Algebra T (K ⊗[R] T) := Algebra.TensorProduct.rightAlgebra
  have : IsLocalization (Algebra.algebraMapSubmonoid T R⁰) (K ⊗[R] T) :=
    IsLocalization.tensorRight K R⁰
  have : IsDomain (Localization (Algebra.algebraMapSubmonoid T R⁰)) :=
    IsLocalization.isDomain_localization (fraction_tensor_denominators R T)
  exact (IsLocalization.algEquiv (Algebra.algebraMapSubmonoid T R⁰)
    (K ⊗[R] T) (Localization (Algebra.algebraMapSubmonoid T R⁰))).toRingEquiv.toMulEquiv.isDomain _

/-- The canonical map into the actual fraction-field base change is injective. -/
theorem fraction_tensor_includeRight_injective :
    Function.Injective (Algebra.TensorProduct.includeRight : T →ₐ[R] K ⊗[R] T) := by
  let : Algebra T (K ⊗[R] T) := Algebra.TensorProduct.rightAlgebra
  have : IsLocalization (Algebra.algebraMapSubmonoid T R⁰) (K ⊗[R] T) :=
    IsLocalization.tensorRight K R⁰
  exact IsLocalization.injective (K ⊗[R] T) (fraction_tensor_denominators R T)

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.FractionBaseChangeDomain.Construction
