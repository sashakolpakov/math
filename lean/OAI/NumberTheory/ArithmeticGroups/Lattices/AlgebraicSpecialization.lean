import Mathlib

/-! # Algebraic Specialization -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.AlgebraicSpecialization.Construction

noncomputable section

/-! Specializing a finitely generated domain to an algebraic closure
while keeping a prescribed nonzero element nonzero. -/

open scoped Classical

theorem finiteType_exists_algHom_to_algClosure
    (k B : Type*) [Field k] [CommRing B] [Nontrivial B] [Algebra k B]
    [Algebra.FiniteType k B] : Nonempty (B →ₐ[k] AlgebraicClosure k) := by
  obtain ⟨I, hI⟩ := Ideal.exists_maximal B
  let : I.IsMaximal := hI
  let : Field (B ⧸ I) := Ideal.Quotient.field I
  let : Module.Finite k (B ⧸ I) := finite_of_finite_type_of_isJacobsonRing k (B ⧸ I)
  let φ : (B ⧸ I) →ₐ[k] AlgebraicClosure k := IsAlgClosed.lift
  exact ⟨φ.comp (Ideal.Quotient.mkₐ k I)⟩

theorem finiteType_specialization_nonzero
    (k B : Type*) [Field k] [CommRing B] [IsDomain B] [Algebra k B]
    [Algebra.FiniteType k B] {b : B} (hb : b ≠ 0) :
    ∃ φ : B →ₐ[k] AlgebraicClosure k, φ b ≠ 0 := by
  let C := Localization.Away b
  have hinj : Function.Injective (algebraMap B C) :=
    IsLocalization.injective C (powers_le_nonZeroDivisors_of_noZeroDivisors hb)
  let : Nontrivial C := nontrivial_of_ne (algebraMap B C 0) (algebraMap B C 1)
    (fun h => zero_ne_one (hinj h))
  obtain ⟨ψ⟩ := finiteType_exists_algHom_to_algClosure k C
  let φ : B →ₐ[k] AlgebraicClosure k := ψ.comp (IsScalarTower.toAlgHom k B C)
  refine ⟨φ, ?_⟩
  have hbunit : IsUnit (algebraMap B C b) := IsLocalization.Away.algebraMap_isUnit b
  exact (hbunit.map ψ.toRingHom).ne_zero

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.AlgebraicSpecialization.Construction
