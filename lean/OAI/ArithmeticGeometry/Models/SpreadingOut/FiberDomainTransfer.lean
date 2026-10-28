import OAI.ArithmeticGeometry.Models.SpreadingOut.FiberRegularity
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.Away.Basic

/-! # Fiber Domain Transfer -/

namespace OAI.ArithmeticGeometry.Models.SpreadingOut.FiberDomainTransfer.Construction

noncomputable section

/-! Transfer integrality from a principal open to its ambient fiber when
the complement is defined by a universally regular element. -/

open scoped TensorProduct

universe u

theorem away_algebraMap_injective_of_mul_injective
    (B : Type u) [CommRing B] (b : B) (hb : Function.Injective (fun x : B ↦ b * x)) :
    Function.Injective (algebraMap B (Localization.Away b)) := by
  apply (injective_iff_map_eq_zero (algebraMap B (Localization.Away b))).mpr
  intro x hx
  obtain ⟨s, hs⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers b)
    (Localization.Away b) x).mp hx
  obtain ⟨n, hn⟩ := s.property
  have hpow (m : ℕ) : Function.Injective (fun x : B ↦ b ^ m * x) := by
    induction m with
    | zero =>
      intro x y h
      simpa only [pow_zero, one_mul] using h
    | succ m ih =>
      intro x y h
      apply ih
      apply hb
      simpa only [pow_succ', mul_assoc] using h
  rw [← hn] at hs
  exact hpow n (hs.trans (mul_zero _).symm)

theorem fiber_domain_of_flat_principal_quotient
    (R k B : Type u) [CommRing R] [CommRing k] [CommRing B]
    [Algebra R k] [Algebra R B] (b : B)
    (hb : Function.Injective (fun x : B ↦ b * x))
    [Module.Flat R (B ⧸ Ideal.span ({b} : Set B))]
    [IsDomain (k ⊗[R] Localization.Away b)] : IsDomain (k ⊗[R] B) := by
  let e := IsLocalization.Away.tensorProductEquivTMulRight R k b (Localization.Away b)
  have : IsDomain (Localization.Away (1 ⊗ₜ[R] b : k ⊗[R] B)) :=
    Function.Injective.isDomain e.symm.toRingHom e.symm.injective
  exact Function.Injective.isDomain (algebraMap _ (Localization.Away (1 ⊗ₜ[R] b : k ⊗[R] B)))
    (away_algebraMap_injective_of_mul_injective _ _
      (FiberRegularity.Construction.tensor_mul_injective_of_flat_quotient R B k b hb))

end

end OAI.ArithmeticGeometry.Models.SpreadingOut.FiberDomainTransfer.Construction
