import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentProgramArrays
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgramSerialization

namespace OAI.Algorithms

/-! Canonical-word uniqueness allows native preparation to construct each
small integer by any measured arithmetic sequence, not a fixed syntax tree. -/
namespace SubexponentialSAT.SqrtLog.IdempotentProgram

open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

variable (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t)

theorem naturalRun_canonical
    (hz : BinaryArithmetic.toNat cache.zero.val < p^t) (n : ℕ) :
    BinaryArithmetic.toNat (naturalRun (RingProgram.scalarProgram p t M cache) n).1.val < p^t := by
  cases n with
  | zero => exact hz
  | succ n => exact SubexpPreparedQuartic.wordAdd_canonical p t M _ _

theorem integerRun_canonical
    (hz : BinaryArithmetic.toNat cache.zero.val < p^t) (z : ℤ) :
    BinaryArithmetic.toNat (integerRun (RingProgram.scalarProgram p t M cache) z).1.val < p^t := by
  cases z with
  | ofNat n => exact naturalRun_canonical p t M cache hz n
  | negSucc n => exact RingProgram.wordMul_canonical p t M _ _

/-- The native selector need only prove its cached output canonical and give
its integer residue; exact equality with the functional generator follows. -/
theorem integerRun_eq_of_value
    (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    (z : ℤ) (word : RingProgram.ScalarCode p t)
    (hw : BinaryArithmetic.toNat word.val < p^t)
    (hvalue : wordValue p t word = (z : ZMod (p^t))) :
    (integerRun (RingProgram.scalarProgram p t M cache) z).1 = word := by
  apply RingProgram.word_eq_of_value p t _ _
    (integerRun_canonical p t M cache hz z) hw
  have h := integerRun_correct (RingProgram.scalarRing p t M cache) z
  exact h.trans hvalue.symm

theorem tableCode_eq_of_value
    (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    {height : ℕ} (i j k : Fin (3*height)) (word : RingProgram.ScalarCode p t)
    (hw : BinaryArithmetic.toNat word.val < p^t)
    (hvalue : wordValue p t word = (hadicTable i j k : ZMod (p^t))) :
    tableCode (RingProgram.scalarProgram p t M cache) i j k = word := by
  rw [tableCode_apply]
  exact integerRun_eq_of_value p t M cache hz (hadicTable i j k) word hw hvalue

end SubexponentialSAT.SqrtLog.IdempotentProgram

end OAI.Algorithms
