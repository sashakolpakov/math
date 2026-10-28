import Mathlib

/-! # Torsion Quotient Descent -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.TorsionQuotientDescent

/-!
# Isomorphisms descend through scalar-torsion quotients

A commuting square of surjections whose kernels are exactly scalar
torsion transports bijectivity from the upper map to the lower map.
-/

variable {R : Type*} [CommRing R]
  {M N P Q : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
  [AddCommGroup Q] [Module R Q]

theorem bijective (a : R) (qM : M →ₗ[R] N) (qP : P →ₗ[R] Q)
    (hqM : Function.Surjective qM) (hqP : Function.Surjective qP)
    (hkerM : ∀ x, qM x = 0 ↔ a • x = 0) (hkerP : ∀ x, qP x = 0 ↔ a • x = 0)
    (u : M →ₗ[R] P) (v : N →ₗ[R] Q) (hu : Function.Bijective u)
    (hcomm : v.comp qM = qP.comp u) : Function.Bijective v := by
  constructor
  · intro x y hxy
    apply sub_eq_zero.mp
    obtain ⟨z, hz⟩ := hqM (x - y)
    have hv : v (qM z) = 0 := by rw [hz, map_sub, hxy, sub_self]
    have hqPz : qP (u z) = 0 := (DFunLike.congr_fun hcomm z).symm.trans hv
    have haz : a • z = 0 := by
      apply hu.1
      rw [map_smul, (hkerP (u z)).mp hqPz, map_zero]
    exact hz.symm.trans ((hkerM z).mpr haz)
  · intro y
    obtain ⟨z, hz⟩ := hqP y
    obtain ⟨x, hx⟩ := hu.2 z
    refine ⟨qM x, (DFunLike.congr_fun hcomm x).trans ?_⟩
    change qP (u x) = y
    rw [hx, hz]

end OAI.NumberTheory.PadicHodge.PeriodInvariants.TorsionQuotientDescent
