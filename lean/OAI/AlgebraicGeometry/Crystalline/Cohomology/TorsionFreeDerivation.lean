import Mathlib.RingTheory.DividedPowers.Basic
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Algebra.Module.Torsion.Free

/-! # Torsion Free Derivation -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.TorsionFreeDerivation.TorsionFreePDDerivation

/-! # Derivations into torsion-free modules respect existing divided powers -/

variable (R A M : Type*) [CommRing R] [CommRing A] [IsDomain A] [CharZero A]
  [Algebra R A] [AddCommGroup M] [Module A M] [Module R M] [Module.IsTorsionFree A M]
  (I : Ideal A) (δ : DividedPowers I) (D : Derivation R A M)

theorem compatible (n : ℕ) (x : A) (hx : x ∈ I) :
    D (δ.dpow (n + 1) x) = δ.dpow n x • D x := by
  have hd := congrArg D (δ.factorial_mul_dpow_eq_pow (n := n + 1) hx)
  rw [D.leibniz, Derivation.map_natCast, smul_zero, add_zero, Derivation.leibniz_pow] at hd
  simp only [Nat.add_sub_cancel, ← Nat.cast_smul_eq_nsmul A, smul_smul] at hd
  apply smul_right_injective M (show ((n + 1).factorial : A) ≠ 0 from
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
  dsimp only
  rw [hd, smul_smul, Nat.factorial_succ, Nat.cast_mul, mul_assoc, δ.factorial_mul_dpow_eq_pow hx]

end OAI.AlgebraicGeometry.Crystalline.Cohomology.TorsionFreeDerivation.TorsionFreePDDerivation
