import OAI.ArithmeticGeometry.Models.SpreadingOut.FiberDomainTransfer
import Mathlib.RingTheory.TensorProduct.Quotient

/-! # Principal Flat Shrink -/

namespace OAI.ArithmeticGeometry.Models.SpreadingOut.PrincipalFlatShrink.Construction

noncomputable section

/-! Shrinking a Dedekind base makes a prescribed principal quotient flat,
so integrality of the principal chart controls every ambient field fiber. -/

open scoped TensorProduct

universe u

def tensorPrincipalQuotientIso
    (R S B : Type u) [CommRing R] [CommRing S] [CommRing B]
    [Algebra R S] [Algebra R B] (b : B) :
    S ⊗[R] (B ⧸ Ideal.span ({b} : Set B)) ≃ₐ[S]
      (S ⊗[R] B) ⧸ Ideal.span ({(1 : S) ⊗ₜ[R] b} : Set _) := by
  refine (Algebra.TensorProduct.tensorQuotientEquiv S B S (Ideal.span {b})).trans
    (Ideal.quotientEquivAlgOfEq S ?_)
  rw [Ideal.map_span, Set.image_singleton]
  rfl

theorem tensor_mulLeft_eq_lTensor
    (R S B : Type u) [CommRing R] [CommRing S] [CommRing B]
    [Algebra R S] [Algebra R B] (b : B) :
    LinearMap.mulLeft R (1 ⊗ₜ[R] b : S ⊗[R] B) = (LinearMap.mulLeft R b).lTensor S := by
  ext s x
  change (1 ⊗ₜ[R] b) * (s ⊗ₜ[R] x) = s ⊗ₜ[R] (b * x)
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem principal_quotient_flat_after_inverting_base_element
    (R B : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing B] [IsNoetherianRing B] [Algebra R B] (b : B) :
    ∃ r : R, r ≠ 0 ∧ Module.Flat (Localization.Away r)
      ((Localization.Away r ⊗[R] B) ⧸ Ideal.span ({(1 : Localization.Away r) ⊗ₜ[R] b} : Set _)) := by
  obtain ⟨r, hr, hf⟩ := GenericFlatness.Construction.finite_module_flat_over_localization R B (B ⧸ Ideal.span {b})
  have := hf
  exact ⟨r, hr, Module.Flat.of_linearEquiv (tensorPrincipalQuotientIso R (Localization.Away r) B b).symm.toLinearEquiv⟩

theorem principal_chart_controls_fibers_after_shrinking
    (R B : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing B] [IsDomain B] [IsNoetherianRing B] [Algebra R B] (b : B) (hb : b ≠ 0) :
    ∃ r : R, r ≠ 0 ∧
      ∀ (k : Type u) [Field k] [Algebra (Localization.Away r) k],
        IsDomain (k ⊗[Localization.Away r]
          Localization.Away (1 ⊗ₜ[R] b : Localization.Away r ⊗[R] B)) →
        IsDomain (k ⊗[Localization.Away r] (Localization.Away r ⊗[R] B)) := by
  obtain ⟨r, hr, hf⟩ := principal_quotient_flat_after_inverting_base_element R B b
  have := hf
  refine ⟨r, hr, fun k _ _ hk ↦ ?_⟩
  have := hk
  apply FiberDomainTransfer.Construction.fiber_domain_of_flat_principal_quotient (Localization.Away r) k
    (Localization.Away r ⊗[R] B) (1 ⊗ₜ[R] b)
  change Function.Injective (LinearMap.mulLeft R (1 ⊗ₜ[R] b : Localization.Away r ⊗[R] B))
  rw [tensor_mulLeft_eq_lTensor]
  exact Module.Flat.lTensor_preserves_injective_linearMap (LinearMap.mulLeft R b)
    (mul_right_injective₀ hb)

end

end OAI.ArithmeticGeometry.Models.SpreadingOut.PrincipalFlatShrink.Construction
