import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpActualRing
import OAI.Algorithms.SubexponentialSAT.SubexpResidueInverse

namespace OAI.Algorithms

/-! The source-field specialization of the actual Fermat power. No new field
instance on the precision-one quotient ring is required. -/

namespace SubexponentialSAT.SubexpFieldCacheAlgebra

open SubexpActualRing

variable (p : ℕ) [Fact p.Prime]

theorem source_defect_zero (a : Ring p 1)
    (ha : rho p 1 (by decide) a ≠ 0) :
    1 - a * a ^ (p^4 - 2) = 0 := by
  have h := SubexpResidueInverse.fermat_defect_nilpotent
    (rho p 1 (by decide)) (p^4) (extension_card p) (p : Ring p 1) 1
    (prime_power_zero p 1)
    (fun x hx => (rho_eq_zero_iff p 1 (by decide) x).mp hx) a ha
  simpa only [pow_one] using h

theorem source_power_inverse (a b : Ring p 1)
    (hb : b = a ^ (p^4 - 2)) (ha : rho p 1 (by decide) a ≠ 0) :
    b * a = 1 := by
  have h := (sub_eq_zero.mp (source_defect_zero p a ha)).symm
  rw [hb, mul_comm]
  exact h

theorem source_difference_inverse (a b inverse : Ring p 1)
    (hv : inverse = (a - b) ^ (p^4 - 2))
    (hne : rho p 1 (by decide) a ≠ rho p 1 (by decide) b) :
    inverse * (a - b) = 1 := by
  apply source_power_inverse p (a - b) inverse hv
  rw [map_sub]
  exact sub_ne_zero.mpr hne

theorem source_zero_power : (0 : Ring p 1) ^ (p^4 - 2) = 0 := by
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hq : 16 ≤ p^4 := by
    calc
      16 = (2 : ℕ)^4 := by norm_num
      _ ≤ p^4 := Nat.pow_le_pow_left hp 4
  exact zero_pow (by omega)

end SubexponentialSAT.SubexpFieldCacheAlgebra

end OAI.Algorithms
