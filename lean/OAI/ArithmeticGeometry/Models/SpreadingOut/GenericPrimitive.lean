import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed

/-! # Generic Primitive -/

namespace OAI.ArithmeticGeometry.Models.SpreadingOut.GenericPrimitive.Construction

noncomputable section

/-! Primitive generators in finite integral algebras after passing to the
fraction field of the polynomial base. -/

open scoped TensorProduct nonZeroDivisors
open IntermediateField

universe u

theorem finite_domain_generic_fiber_isField
    (P A F : Type u) [CommRing P] [IsDomain P] [CommRing A] [IsDomain A]
    [Field F] [Algebra P A] [FaithfulSMul P A] [Algebra P F] [IsFractionRing P F]
    [Module.Finite P A] : IsField (F ⊗[P] A) := by
  let : Algebra A (F ⊗[P] A) := Algebra.TensorProduct.rightAlgebra
  have hM : Algebra.algebraMapSubmonoid A P⁰ ≤ A⁰ := by
    rintro _ ⟨p, hp, rfl⟩
    exact mem_nonZeroDivisors_of_ne_zero
      (by simpa only [map_zero] using
        (FaithfulSMul.algebraMap_injective P A).ne (mem_nonZeroDivisors_iff_ne_zero.mp hp))
  have : IsDomain (F ⊗[P] A) := IsLocalization.isDomain_of_le_nonZeroDivisors _ hM
  exact isField_of_isIntegral_of_isField' (R := F) (Field.toIsField F)

theorem primitive_generator_in_localized_algebra
    (P A F E : Type u) [CommRing P] [IsDomain P] [CommRing A]
    [Field F] [Field E] [Algebra P A] [Algebra P F] [IsFractionRing P F]
    [Algebra F E] [Algebra P E] [IsScalarTower P F E]
    [FiniteDimensional F E] [Algebra.IsSeparable F E]
    (f : A →ₗ[P] E) [IsLocalizedModule P⁰ f] :
    ∃ a : A, F⟮f a⟯ = ⊤ := by
  obtain ⟨z, hz⟩ := Field.exists_primitive_element F E
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalizedModule.surj P⁰ f z
  refine ⟨a, top_unique ?_⟩
  rw [← hz]
  apply IntermediateField.adjoin_simple_le_iff.mpr
  have hs0 : algebraMap P F (s : P) ≠ 0 :=
    by simpa only [map_zero] using
      (IsFractionRing.injective P F).ne (nonZeroDivisors.coe_ne_zero s)
  have hmem : (s : P) • z ∈ F⟮f a⟯ := by
    rw [← Submonoid.smul_def, hs]
    exact mem_adjoin_simple_self F (f a)
  have H := (F⟮f a⟯).toSubalgebra.smul_mem
    (r := (algebraMap P F (s : P))⁻¹) hmem
  rw [← algebraMap_smul F (s : P) z, inv_smul_smul₀ hs0] at H
  exact H

theorem finite_domain_generic_fiber_has_algebra_generator
    (P A F : Type u) [CommRing P] [IsDomain P] [CommRing A] [IsDomain A]
    [Field F] [CharZero F] [Algebra P A] [FaithfulSMul P A]
    [Algebra P F] [IsFractionRing P F] [Module.Finite P A] :
    ∃ a : A, Algebra.adjoin F ({1 ⊗ₜ[P] a} : Set (F ⊗[P] A)) = ⊤ := by
  let : Field (F ⊗[P] A) := (finite_domain_generic_fiber_isField P A F).toField
  obtain ⟨a, ha⟩ := primitive_generator_in_localized_algebra P A F (F ⊗[P] A)
    (TensorProduct.mk P F A 1)
  change F⟮1 ⊗ₜ[P] a⟯ = ⊤ at ha
  refine ⟨a, ?_⟩
  rw [← IntermediateField.adjoin_toSubalgebra, ha]
  rfl

end

end OAI.ArithmeticGeometry.Models.SpreadingOut.GenericPrimitive.Construction
