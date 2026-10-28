import OAI.ArithmeticGeometry.Models.SpreadingOut.PrincipalFiberDensity

/-! # Principal Density Shrink -/

namespace OAI.ArithmeticGeometry.Models.SpreadingOut.PrincipalDensityShrink.Construction

noncomputable section

/-! One base element controls density of a principal open in all fibers
without changing the original affine coordinates. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped TensorProduct

universe u

theorem tensor_regular_after_inverting_base_element
    (R B : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing B] [IsDomain B] [IsNoetherianRing B] [Algebra R B]
    (b : B) (hb : b ≠ 0) :
    ∃ r : R, r ≠ 0 ∧
      ∀ (S : Type u) [CommRing S] [Algebra R S], IsUnit (algebraMap R S r) →
        Function.Injective (fun x : S ⊗[R] B ↦ (1 ⊗ₜ[R] b) * x) := by
  obtain ⟨r, hr, hf⟩ := PrincipalFlatShrink.Construction.principal_quotient_flat_after_inverting_base_element R B b
  have := hf
  refine ⟨r, hr, fun S _ _ hunit ↦ ?_⟩
  let φ : Localization.Away r →+* S := IsLocalization.Away.lift r hunit
  let : Algebra (Localization.Away r) S := φ.toAlgebra
  have : IsScalarTower R (Localization.Away r) S :=
    IsScalarTower.of_algebraMap_eq' (IsLocalization.Away.lift_comp r hunit).symm
  have hreg : Function.Injective
      (fun x : Localization.Away r ⊗[R] B ↦ (1 ⊗ₜ[R] b) * x) := by
    change Function.Injective (LinearMap.mulLeft R (1 ⊗ₜ[R] b : Localization.Away r ⊗[R] B))
    rw [PrincipalFlatShrink.Construction.tensor_mulLeft_eq_lTensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap (LinearMap.mulLeft R b)
      (mul_right_injective₀ hb)
  have ht := FiberRegularity.Construction.tensor_mul_injective_of_flat_quotient (Localization.Away r)
    (Localization.Away r ⊗[R] B) S (1 ⊗ₜ[R] b) hreg
  let e := Algebra.TensorProduct.cancelBaseChange R (Localization.Away r) S S B
  have he : e (1 ⊗ₜ[Localization.Away r] ((1 : Localization.Away r) ⊗ₜ[R] b)) =
      (1 ⊗ₜ[R] b : S ⊗[R] B) := by
    simp only [e, Algebra.TensorProduct.cancelBaseChange_tmul, one_smul]
  intro x y h
  apply e.symm.injective
  apply ht
  apply e.injective
  simpa only [map_mul, he, AlgEquiv.apply_symm_apply] using h

end

end OAI.ArithmeticGeometry.Models.SpreadingOut.PrincipalDensityShrink.Construction
