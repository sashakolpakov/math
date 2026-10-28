import Mathlib.RingTheory.DividedPowers.DPMorphism
import Mathlib.Algebra.CharZero.Defs

/-! # Torsion Free DP -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.TorsionFreeDP.TorsionFreeDPMorphism

/-! # Divided powers are forced by their factorial identities in characteristic zero domains -/

variable {A B : Type*} [CommRing A] [CommRing B] [IsDomain B] [CharZero B]
  (I : Ideal A) (δI : DividedPowers I) (J : Ideal B) (δJ : DividedPowers J)
  (f : A →+* B) (hf : I.map f ≤ J)

include hf in
theorem isDPMorphism : DividedPowers.IsDPMorphism δI δJ f where
  ideal_comp := hf
  dpow_comp {n} x hx := by
    apply mul_left_cancel₀ (show (n.factorial : B) ≠ 0 from Nat.cast_ne_zero.mpr n.factorial_ne_zero)
    calc
      _ = (f x) ^ n := δJ.factorial_mul_dpow_eq_pow (hf (Ideal.mem_map_of_mem f hx))
      _ = f (x ^ n) := (f.map_pow x n).symm
      _ = f ((n.factorial : A) * δI.dpow n x) := congrArg f (δI.factorial_mul_dpow_eq_pow hx).symm
      _ = _ := by rw [f.map_mul, map_natCast]

end OAI.AlgebraicGeometry.Crystalline.Cohomology.TorsionFreeDP.TorsionFreeDPMorphism
