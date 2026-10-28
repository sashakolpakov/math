import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Algebra.Module.LinearMap.Defs

/-! # Additive Linearity -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.AdditiveLinearity

noncomputable section

/-! An additive map from a p-adic integer module to p-adic integers is
automatically linear, by its values modulo every prime power. -/

variable (ℓ : ℕ) [Fact ℓ.Prime] {M : Type*} [AddCommGroup M] [Module ℤ_[ℓ] M]

theorem map_smul (f : M →+ ℤ_[ℓ]) (a : ℤ_[ℓ]) (x : M) : f (a • x) = a * f x := by
  apply PadicInt.ext_of_toZModPow.mp
  intro n
  let m := (PadicInt.toZModPow n a).val
  have hm : (m : ZMod (ℓ ^ n)) = PadicInt.toZModPow n a := ZMod.natCast_zmod_val _
  have hdvd : (ℓ : ℤ_[ℓ]) ^ n ∣ a - (m : ℤ_[ℓ]) := by
    apply Ideal.mem_span_singleton.mp
    rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_natCast, hm, sub_self]
  obtain ⟨b, hb⟩ := hdvd
  have ha : a = (m : ℤ_[ℓ]) + (ℓ : ℤ_[ℓ]) ^ n * b := by rw [← hb]; abel
  have hp (y : M) : PadicInt.toZModPow n (f ((ℓ : ℤ_[ℓ]) ^ n • y)) = 0 := by
    rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul, map_nsmul, map_nsmul, nsmul_eq_mul,
      ZMod.natCast_self, zero_mul]
  calc
    PadicInt.toZModPow n (f (a • x)) = (m : ZMod (ℓ ^ n)) * PadicInt.toZModPow n (f x) := by
      rw [ha, add_smul, map_add, map_add, mul_smul, hp, add_zero,
        Nat.cast_smul_eq_nsmul, map_nsmul, map_nsmul, nsmul_eq_mul]
    _ = PadicInt.toZModPow n (a * f x) := by rw [hm, map_mul]

def linearMap (f : M →+ ℤ_[ℓ]) : M →ₗ[ℤ_[ℓ]] ℤ_[ℓ] :=
  { f with map_smul' := map_smul ℓ f }

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.AdditiveLinearity
