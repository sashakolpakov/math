import Mathlib.RingTheory.WittVector.Complete
import Mathlib.Data.ZMod.Basic
import OAI.AlgebraicGeometry.Picard.Homomorphisms.Frobenius

/-! # Witt Prime -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.WittPrime.WittPrimeZeroFrobenius

noncomputable section

/-! Every map from prime-field Witt vectors to a ring killed by p has
Frobenius-fixed image, including when the target ring is zero. -/

universe u
variable (p : ℕ) [Fact p.Prime] {A : Type u} [CommRing A]
  (hp : (p : A) = 0) (f : WittVector p (ZMod p) →+* A)

include hp in
theorem fixed (w : WittVector p (ZMod p)) : (f w) ^ p = f w := by
  have hk : RingHom.ker (WittVector.constantCoeff : WittVector p (ZMod p) →+* ZMod p) ≤ RingHom.ker f := by
    rw [WittVector.ker_constantCoeff, Ideal.span_singleton_le_iff_mem]
    change f p = 0
    rw [map_natCast, hp]
  have hw : w ^ p - w ∈ RingHom.ker
      (WittVector.constantCoeff : WittVector p (ZMod p) →+* ZMod p) := by
    change WittVector.constantCoeff (w ^ p - w) = 0
    rw [map_sub, map_pow, ZMod.pow_card, sub_self]
  have h := hk hw
  change f (w ^ p - w) = 0 at h
  simpa only [map_sub, map_pow, sub_eq_zero] using h

theorem comp : (AlgebraicGeometry.Picard.Homomorphisms.Frobenius.Construction.powerRingHom p Fact.out A hp).comp f = f :=
  RingHom.ext (fixed p hp f)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.WittPrime.WittPrimeZeroFrobenius
