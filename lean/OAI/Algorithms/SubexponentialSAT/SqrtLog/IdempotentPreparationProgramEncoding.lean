import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgramArrays
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgramSerialization
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentProgramConstants

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

open SubexpSymbolicCost SubexpQuarticRing

theorem flat_three {B : ℕ} (n : ℕ) (a b c z : Word B) :
    RingProgram.flat (fun k : Fin (n+3) =>
      if k.val=0 then a else if k.val=1 then b else if k.val=2 then c else z) =
      a.val ++ b.val ++ c.val ++ Subexp.BlockCopyProgram.copies n z.val := by
  simp [RingProgram.flat,List.ofFn_succ,Subexp.BlockCopyProgram.copies,
    List.ofFn_const,List.append_assoc]

theorem flat_one {B : ℕ} (n : ℕ) (a z : Word B) :
    RingProgram.flat (fun k : Fin (n+1) => if k.val=0 then a else z) =
      a.val ++ Subexp.BlockCopyProgram.copies n z.val := by
  simp [RingProgram.flat,List.ofFn_succ,Subexp.BlockCopyProgram.copies,List.ofFn_const]

theorem initialRun_flat {B : ℕ} (ops : RingProgram (Word B)) (t : ℕ)
    (ht : 0 < t) (u : Word B) :
    RingProgram.flat (IdempotentProgram.initialRun ops t u).1 =
      (ops.addRun u u).1.val ++ (ops.negRun (ops.addRun (ops.addRun u u).1 u).1).1.val ++
        u.val ++ Subexp.BlockCopyProgram.copies (3*t-3) ops.zeroRun.1.val := by
  have hd : 3*t = (3*t-3)+3 := by omega
  change RingProgram.flat (fun k : Fin (3*t) =>
    if k.val=0 then (ops.addRun u u).1
    else if k.val=1 then (ops.negRun (ops.addRun (ops.addRun u u).1 u).1).1
    else if k.val=2 then u else ops.zeroRun.1) = _
  conv_lhs => rw [hd]
  exact flat_three _ _ _ _ _

theorem scalar_neg_zero (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    (hz : BinaryArithmetic.toNat cache.zero.val < p^t) :
    ((RingProgram.scalarProgram p t M cache).negRun cache.zero).1 = cache.zero := by
  exact IdempotentProgram.scalar_neg_zero p t M cache hz

theorem scalar_neg_one (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    (hm : BinaryArithmetic.toNat cache.minusOne.val < p^t) :
    ((RingProgram.scalarProgram p t M cache).negRun cache.one).1 = cache.minusOne := by
  exact IdempotentProgram.scalar_neg_one p t M cache hm

theorem minusOneRun_flat (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    (ht : 0 < t) (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    (hm : BinaryArithmetic.toNat cache.minusOne.val < p^t) :
    RingProgram.flat (IdempotentProgram.minusOneRun (RingProgram.scalarProgram p t M cache) t).1 =
      cache.minusOne.val ++ Subexp.BlockCopyProgram.copies (3*t-1) cache.zero.val := by
  simpa only [Subexp.BlockCopyProgram.copies] using
    IdempotentProgram.minusOneRun_flat p t M cache hz hm t ht

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

end OAI.Algorithms
