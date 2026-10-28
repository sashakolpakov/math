import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentProgramBinary
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgramSerialization

namespace OAI.Algorithms

/-! Exact word identities connecting the padded native preparation arrays
to the finite H-adic implementation. -/
namespace SubexponentialSAT.SqrtLog.IdempotentProgram

open SubexponentialSAT.SubexpSymbolicCost SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

variable (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t)

theorem scalar_neg_zero (hz : BinaryArithmetic.toNat cache.zero.val < p^t) :
    ((RingProgram.scalarProgram p t M cache).negRun cache.zero).1 = cache.zero := by
  apply RingProgram.word_eq_of_value p t _ _
  · exact RingProgram.wordMul_canonical p t M _ _
  · exact hz
  · simp only [RingProgram.scalarProgram, SubexpPreparedQuartic.wordMul_correct,
      cache.zero_correct, zero_mul]

theorem scalar_neg_one (hm : BinaryArithmetic.toNat cache.minusOne.val < p^t) :
    ((RingProgram.scalarProgram p t M cache).negRun cache.one).1 = cache.minusOne := by
  apply RingProgram.word_eq_of_value p t _ _
  · exact RingProgram.wordMul_canonical p t M _ _
  · exact hm
  · simp only [RingProgram.scalarProgram, SubexpPreparedQuartic.wordMul_correct,
      cache.one_correct, one_mul]

theorem minusOneRun_apply (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    (hm : BinaryArithmetic.toNat cache.minusOne.val < p^t)
    (height : ℕ) (i : Fin (3*height)) :
    (minusOneRun (RingProgram.scalarProgram p t M cache) height).1 i =
      if i.val = 0 then cache.minusOne else cache.zero := by
  simp only [minusOneRun, RingProgram.negRun, RingProgram.tabulateRun_eq, oneCode]
  by_cases hi : i.val = 0
  · simp only [hi, ↓reduceIte, RingProgram.scalarProgram]
    exact scalar_neg_one p t M cache hm
  · simp only [hi, ↓reduceIte, RingProgram.scalarProgram]
    exact scalar_neg_zero p t M cache hz

end SubexponentialSAT.SqrtLog.IdempotentProgram

namespace SubexponentialSAT.SqrtLog.IdempotentProgram

open SubexponentialSAT.SubexpQuarticRing

/-- A sparse constant vector is exactly one word followed by zero padding. -/
theorem flat_sparse {B dim : ℕ} (hd : 0 < dim) (first zero : Word B) :
    RingProgram.flat (fun i : Fin dim => if i.val = 0 then first else zero) =
      first.val ++ (List.replicate (dim-1) zero.val).flatten := by
  cases dim with
  | zero => omega
  | succ n =>
      simp [RingProgram.flat, List.ofFn_succ]

theorem minusOneRun_flat (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    (hm : BinaryArithmetic.toNat cache.minusOne.val < p^t)
    (height : ℕ) (ht : 0 < height) :
    RingProgram.flat (minusOneRun (RingProgram.scalarProgram p t M cache) height).1 =
      cache.minusOne.val ++ (List.replicate (3*height-1) cache.zero.val).flatten := by
  have hfun : (minusOneRun (RingProgram.scalarProgram p t M cache) height).1 =
      fun i => if i.val = 0 then cache.minusOne else cache.zero := by
    funext i
    exact minusOneRun_apply p t M cache hz hm height i
  rw [hfun]
  exact flat_sparse (by omega) cache.minusOne cache.zero

end SubexponentialSAT.SqrtLog.IdempotentProgram

end OAI.Algorithms
