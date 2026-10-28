import OAI.NumberTheory.ArithmeticGroups.Lattices.TensorDomainSpecialization
import OAI.NumberTheory.ArithmeticGroups.Lattices.GeometricIrreducibility

/-! # Reduced Field Base Change -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.ReducedFieldBaseChange.Construction

noncomputable section

/-! Reducedness over the algebraic closure implies reducedness over
every extension field. In characteristic zero this applies to domains. -/

open scoped Classical TensorProduct

theorem finiteType_domain_tensor_reduced_of_algClosure
    (k A B : Type*) [Field k] [CommRing A] [Algebra k A]
    [CommRing B] [IsDomain B] [Algebra k B] [Algebra.FiniteType k B]
    [IsReduced (AlgebraicClosure k ⊗[k] A)] : IsReduced (B ⊗[k] A) := by
  constructor
  intro x hx
  by_contra hn
  obtain ⟨φ, hφ⟩ := TensorDomainSpecialization.Construction.exists_nonzero_tensor_specialization k A B hn
  exact hφ (hx.map (Algebra.TensorProduct.map φ (AlgHom.id k A))).eq_zero

theorem field_tensor_reduced_of_algClosure
    (k K A : Type*) [Field k] [Field K] [Algebra k K]
    [CommRing A] [Algebra k A] [IsReduced (AlgebraicClosure k ⊗[k] A)] :
    IsReduced (K ⊗[k] A) := by
  have hr : IsReduced (A ⊗[k] K) := by
    apply IsReduced.tensorProduct_of_flat_of_forall_fg
    intro B hB
    let : Algebra.FiniteType k B := B.fg_iff_finiteType.mp hB
    let : IsReduced (B ⊗[k] A) := finiteType_domain_tensor_reduced_of_algClosure k A B
    exact isReduced_of_injective (Algebra.TensorProduct.comm k A B)
      (Algebra.TensorProduct.comm k A B).injective
  let : IsReduced (A ⊗[k] K) := hr
  exact isReduced_of_injective (Algebra.TensorProduct.comm k K A)
    (Algebra.TensorProduct.comm k K A).injective

theorem field_tensor_domain_charZero_reduced
    (k K A : Type*) [Field k] [CharZero k] [Field K] [Algebra k K]
    [CommRing A] [IsDomain A] [Algebra k A] : IsReduced (K ⊗[k] A) := by
  let : IsReduced (AlgebraicClosure k ⊗[k] A) :=
    GeometricIrreducibility.Construction.separable_tensor_domain_reduced k (AlgebraicClosure k) A
  exact field_tensor_reduced_of_algClosure k K A

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.ReducedFieldBaseChange.Construction
