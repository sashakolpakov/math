import Mathlib

/-! # Inverse -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.DividedPower.Inverse

noncomputable section

/-!
# IntegralComparison: inverses of divided-power ring maps

A bijective divided-power ring map whose map on quotient rings is
injective has a divided-power inverse. The quotient condition ensures
that the inverse preserves the ideal as well as the ring operations.
-/

universe u v

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]
variable {I : Ideal A} {J : Ideal B} {δ : DividedPowers I} {ε : DividedPowers J}
variable (φ : DividedPowers.DPMorphism δ ε)

def quotientMap : A ⧸ I →+* B ⧸ J :=
  Ideal.quotientMap J φ.toRingHom (Ideal.map_le_iff_le_comap.mp φ.ideal_comp)

variable (hφ : Function.Bijective φ) (hq : Function.Injective (Inverse.quotientMap φ))

def ringEquiv : A ≃+* B := RingEquiv.ofBijective φ.toRingHom hφ

include hq in
lemma inverse_mem {x : B} (hx : x ∈ J) : (ringEquiv φ hφ).symm x ∈ I := by
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  apply hq
  change Ideal.Quotient.mk J (φ ((ringEquiv φ hφ).symm x)) = (Inverse.quotientMap φ) 0
  rw [map_zero]
  change Ideal.Quotient.mk J ((ringEquiv φ hφ) ((ringEquiv φ hφ).symm x)) = 0
  rw [RingEquiv.apply_symm_apply]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hx

def inverse : DividedPowers.DPMorphism ε δ where
  toRingHom := (ringEquiv φ hφ).symm.toRingHom
  ideal_comp := Ideal.map_le_iff_le_comap.mpr (fun _ hx => inverse_mem φ hφ hq hx)
  dpow_comp {n} x hx := by
    have h := φ.dpow_comp (n := n) ((ringEquiv φ hφ).symm x) (inverse_mem φ hφ hq hx)
    change ε.dpow n ((ringEquiv φ hφ) ((ringEquiv φ hφ).symm x)) =
      (ringEquiv φ hφ) (δ.dpow n ((ringEquiv φ hφ).symm x)) at h
    rw [RingEquiv.apply_symm_apply] at h
    apply (ringEquiv φ hφ).injective
    exact h.symm.trans ((ringEquiv φ hφ).apply_symm_apply (ε.dpow n x)).symm

lemma inverse_comp : (inverse φ hφ hq).comp φ = DividedPowers.DPMorphism.id δ := by
  apply DFunLike.ext
  intro x
  exact (ringEquiv φ hφ).symm_apply_apply x

lemma comp_inverse : φ.comp (inverse φ hφ hq) = DividedPowers.DPMorphism.id ε := by
  apply DFunLike.ext
  intro x
  exact (ringEquiv φ hφ).apply_symm_apply x

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.DividedPower.Inverse
