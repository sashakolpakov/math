import OAI.ArithmeticGeometry.Models.SpreadingOut.GenericPrimitive
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.Flat.Basic

/-! # Common Denominator -/

namespace OAI.ArithmeticGeometry.Models.SpreadingOut.CommonDenominator.Construction

noncomputable section

/-! A finite integral algebra and its primitive subalgebra agree after
inverting one nonzero element of the base. -/

open scoped TensorProduct nonZeroDivisors

universe u

theorem finite_submodule_common_denominator
    (R M : Type u) [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] (N : Submodule R M)
    (h : ∀ m : M, ∃ r : R, r ≠ 0 ∧ r • m ∈ N) :
    ∃ r : R, r ≠ 0 ∧ ∀ m : M, r • m ∈ N := by
  have hQ : Module.IsTorsion R (M ⧸ N) := by
    intro q
    obtain ⟨m, rfl⟩ := N.mkQ_surjective q
    obtain ⟨r, hr, hm⟩ := h m
    refine ⟨⟨r, mem_nonZeroDivisors_of_ne_zero hr⟩, ?_⟩
    change r • N.mkQ m = 0
    rw [← map_smul]
    exact (Submodule.Quotient.mk_eq_zero N).mpr hm
  obtain ⟨r, hr, hr0⟩ := Submodule.annihilator_top_inter_nonZeroDivisors hQ
  refine ⟨r, mem_nonZeroDivisors_iff_ne_zero.mp hr0, fun m ↦ ?_⟩
  have H := (Submodule.mem_annihilator.mp hr) (N.mkQ m) Submodule.mem_top
  rw [← map_smul] at H
  exact (Submodule.Quotient.mk_eq_zero N).mp H

theorem primitive_subalgebra_common_denominator
    (P A F E : Type u) [CommRing P] [IsDomain P] [CommRing A]
    [Field F] [CommRing E] [Algebra P A] [Algebra P F] [IsFractionRing P F]
    [Algebra F E] [Algebra P E] [IsScalarTower P F E]
    [Module.Finite P A] (f : A →ₐ[P] E) (hf : Function.Injective f)
    (a : A) (hgen : Algebra.adjoin F ({f a} : Set E) = ⊤) :
    ∃ d : P, d ≠ 0 ∧ ∀ x : A, d • x ∈ Algebra.adjoin P ({a} : Set A) := by
  apply finite_submodule_common_denominator P A (Algebra.adjoin P {a}).toSubmodule
  intro x
  have hx : f x ∈ Algebra.adjoin F ({f a} : Set E) := by rw [hgen]; trivial
  obtain ⟨s, hs⟩ := multiple_mem_adjoin_of_mem_localization_adjoin P⁰ F {f a} (f x) hx
  refine ⟨s, nonZeroDivisors.coe_ne_zero s, ?_⟩
  rw [← f.map_adjoin_singleton a] at hs
  obtain ⟨y, hy, he⟩ := hs
  have hxy : y = (s : P) • x := hf (by
    rw [map_smul]
    exact he)
  exact hxy ▸ hy

theorem finite_domain_primitive_common_denominator
    (P A F : Type u) [CommRing P] [IsDomain P] [CommRing A] [IsDomain A]
    [Field F] [CharZero F] [Algebra P A] [FaithfulSMul P A]
    [Algebra P F] [IsFractionRing P F] [Module.Finite P A] :
    ∃ (a : A) (d : P), d ≠ 0 ∧ ∀ x : A, d • x ∈ Algebra.adjoin P ({a} : Set A) := by
  obtain ⟨a, ha⟩ := GenericPrimitive.Construction.finite_domain_generic_fiber_has_algebra_generator P A F
  let f : A →ₐ[P] F ⊗[P] A := Algebra.TensorProduct.includeRight
  have hf : Function.Injective f := by
    apply (injective_iff_map_eq_zero f).mpr
    intro x hx
    obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_zero_iff P⁰ (TensorProduct.mk P F A 1)).mp hx
    have hs0 : algebraMap P A (s : P) ≠ 0 := by
      simpa only [map_zero] using
        (FaithfulSMul.algebraMap_injective P A).ne (nonZeroDivisors.coe_ne_zero s)
    exact (mul_eq_zero.mp (show algebraMap P A (s : P) * x = 0 by
      simpa only [Submonoid.smul_def, Algebra.smul_def] using hs)).resolve_left hs0
  obtain ⟨d, hd, hdx⟩ := primitive_subalgebra_common_denominator P A F (F ⊗[P] A) f hf a ha
  exact ⟨a, d, hd, hdx⟩

end

end OAI.ArithmeticGeometry.Models.SpreadingOut.CommonDenominator.Construction
