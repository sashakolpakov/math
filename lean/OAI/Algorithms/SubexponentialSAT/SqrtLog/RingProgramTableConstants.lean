import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgramSerialization

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingProgram

open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing SubexponentialSAT.BinaryArithmetic

theorem prepareScalarCache_one_canonical (p t : ℕ) [Fact p.Prime]
    (M : SubexponentialSAT.SubexpPreparedQuartic.Modulus p t) (ht : 0 < t) :
    BinaryArithmetic.toNat (prepareScalarCache p t M ht).1.one.val < p^t := by
  have hB : 0 < baseWidth p t := Nat.mul_pos ht (Nat.zero_lt_succ _)
  have hone : BinaryArithmetic.toNat [true] < 2^baseWidth p t :=
    Nat.one_lt_pow (Nat.ne_of_gt hB) Nat.one_lt_two
  change BinaryArithmetic.toNat (SubexponentialSAT.SubexpModulusConstruction.normalizeRun (baseWidth p t) [true]).1 < p^t
  rw [SubexponentialSAT.SubexpModulusConstruction.normalizeRun_value _ _ hone]
  simpa [BinaryArithmetic.toNat, bitVal] using Nat.one_lt_pow (Nat.ne_of_gt ht) (Fact.out : p.Prime).one_lt

end SubexponentialSAT.SqrtLog.RingProgram

end OAI.Algorithms
