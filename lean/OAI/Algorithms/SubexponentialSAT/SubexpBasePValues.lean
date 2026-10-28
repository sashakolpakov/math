import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpBasePUnranking
import OAI.Algorithms.SubexponentialSAT.BooleanPackingLE

namespace OAI.Algorithms

/-!
# Numeric specification of the actual fixed-width digit stream

The proved unranking program can preserve arbitrary leading zeroes in its
working rank. Its output digit words nevertheless depend only on the numeric
rank, since each digit has the fixed modulus width.
-/

namespace SubexponentialSAT.SubexpBasePValues

open BinaryArithmetic SubexpBasePUnranking

/-- One actual remainder word is the canonical little-endian representation
of the numeric remainder at exactly the modulus width. -/
theorem digit_eq_fixedBits (modulus rank : List Bool) (hm : 0 < BinaryArithmetic.toNat modulus) :
    digit modulus rank = SubexpLiftRing.fixedBits modulus.length (BinaryArithmetic.toNat rank % BinaryArithmetic.toNat modulus) := by
  apply BooleanPackingLE.word_eq_of_length_value
  · simp only [digit_length, SubexpLiftRing.fixedBits_length]
  · rw [digit_value modulus rank hm, SubexpLiftRing.toNat_fixedBits_of_lt]
    exact (Nat.mod_lt _ hm).trans (ModularArithmetic.toNat_lt_pow_length modulus)

/-- The actual output words are fixed-width encodings of the numeric digit
list, with the least-significant base-p coordinate first. -/
theorem digitWords_eq_numeric (modulus rank : List Bool) (k : ℕ)
    (hm : 0 < BinaryArithmetic.toNat modulus) :
    digitWords modulus k rank =
      (numericDigits (BinaryArithmetic.toNat modulus) k (BinaryArithmetic.toNat rank)).map
        (SubexpLiftRing.fixedBits modulus.length) := by
  induction k generalizing rank with
  | zero => rfl
  | succ k ih =>
      simp only [digitWords, numericDigits, List.map_cons, digit_eq_fixedBits modulus rank hm,
        ih, nextRank_value modulus rank hm]

/-- In particular, leading zeroes in the scalar-rank register do not change
any local field label or the emitted row semantics. -/
theorem digitWords_congr (modulus left right : List Bool) (k : ℕ)
    (hm : 0 < BinaryArithmetic.toNat modulus) (hvalue : BinaryArithmetic.toNat left = BinaryArithmetic.toNat right) :
    digitWords modulus k left = digitWords modulus k right := by
  rw [digitWords_eq_numeric modulus left k hm, digitWords_eq_numeric modulus right k hm, hvalue]

end SubexponentialSAT.SubexpBasePValues

end OAI.Algorithms
