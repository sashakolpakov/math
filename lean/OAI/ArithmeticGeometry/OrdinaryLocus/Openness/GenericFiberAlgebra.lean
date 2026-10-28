import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-! # Generic Fiber Algebra -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.GenericFiberAlgebra.Construction

noncomputable section

/-! The generic fiber algebra of a finite inclusion of integral domains. -/

open scoped TensorProduct

theorem isDomain_genericFiberAlgebra
    (R B K : Type*) [CommRing R] [IsDomain R] [CommRing B] [IsDomain B]
    [Algebra R B] [FaithfulSMul R B] [Field K] [Algebra R K] [IsFractionRing R K] :
    IsDomain (K ⊗[R] B) := by
  let : Algebra B (K ⊗[R] B) := Algebra.TensorProduct.rightAlgebra
  apply IsLocalization.isDomain_of_le_nonZeroDivisors (K ⊗[R] B)
    (M := Algebra.algebraMapSubmonoid B (nonZeroDivisors R))
  rintro x ⟨r, hr, rfl⟩
  rw [mem_nonZeroDivisors_iff_ne_zero]
  exact fun h => nonZeroDivisors.ne_zero hr
    ((FaithfulSMul.algebraMap_injective R B) ((map_zero (algebraMap R B)).symm ▸ h))

theorem isField_genericFiberAlgebra
    (R B K : Type*) [CommRing R] [IsDomain R] [CommRing B] [IsDomain B]
    [Algebra R B] [FaithfulSMul R B] [Module.Finite R B]
    [Field K] [Algebra R K] [IsFractionRing R K] :
    IsField (K ⊗[R] B) := by
  have : IsDomain (K ⊗[R] B) := isDomain_genericFiberAlgebra R B K
  exact isField_of_isIntegral_of_isField' (R := K) (Field.toIsField K)

/-- The generic fiber field is also the fraction field of the source domain. -/
theorem isFractionRing_genericFiberAlgebra
    (R B K : Type*) [CommRing R] [IsDomain R] [CommRing B] [IsDomain B]
    [Algebra R B] [FaithfulSMul R B] [Module.Finite R B]
    [Field K] [Algebra R K] [IsFractionRing R K] :
    letI : Algebra B (K ⊗[R] B) := Algebra.TensorProduct.rightAlgebra
    IsFractionRing B (K ⊗[R] B) := by
  let : Algebra B (K ⊗[R] B) := Algebra.TensorProduct.rightAlgebra
  let : Field (K ⊗[R] B) := (isField_genericFiberAlgebra R B K).toField
  have hM : Algebra.algebraMapSubmonoid B (nonZeroDivisors R) ≤ nonZeroDivisors B :=
    map_le_nonZeroDivisors_of_injective _ (FaithfulSMul.algebraMap_injective R B) le_rfl
  apply IsLocalization.of_le (Algebra.algebraMapSubmonoid B (nonZeroDivisors R))
    (nonZeroDivisors B) hM
  intro b hb
  rw [isUnit_iff_ne_zero]
  exact (map_ne_zero_iff _ (IsLocalization.injective (K ⊗[R] B) hM)).mpr
    (nonZeroDivisors.ne_zero hb)

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.GenericFiberAlgebra.Construction
