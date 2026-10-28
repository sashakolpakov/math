import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgramTableSemantics

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingProgramTable

open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing SubexponentialSAT.BinaryArithmetic

variable (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
variable (cache : RingProgram.ScalarCache p t)

theorem powerData_canonical {d : ℕ} (c : List.Vector (Word (baseWidth p t)) d)
    (hz : BinaryArithmetic.toNat cache.zero.val < p^t) (ho : BinaryArithmetic.toNat cache.one.val < p^t)
    (n : ℕ) (i : Fin d) :
    BinaryArithmetic.toNat ((iterData p t M cache.zero cache.minusOne c n
      (initialData d cache.one cache.zero)).coefficients.get i).val < p^t := by
  cases n with
  | zero =>
    change BinaryArithmetic.toNat ((initialData d cache.one cache.zero).coefficients.get i).val < p^t
    rw [initialData_get]
    split <;> assumption
  | succ n =>
    rw [iterData_succ]
    exact advance_canonical p t M cache.zero cache.minusOne c _ i

theorem callbackPower_canonical {d : ℕ} (c : Fin d → Word (baseWidth p t))
    (hz : BinaryArithmetic.toNat cache.zero.val < p^t) (ho : BinaryArithmetic.toNat cache.one.val < p^t)
    (n : ℕ) (i : Fin d) :
    BinaryArithmetic.toNat ((RingProgram.powerVectorRun (RingProgram.scalarProgram p t M cache) c n).1 i).val < p^t := by
  cases n with
  | zero =>
    simp only [RingProgram.powerVectorRun, RingProgram.oneVectorRun, RingProgram.tabulateRun_eq]
    split <;> assumption
  | succ n =>
    simp only [RingProgram.powerVectorRun, RingProgram.mulXRun, RingProgram.tabulateRun_eq]
    exact SubexpPreparedQuartic.wordAdd_canonical p t M _ _

theorem powerData_eq_callback {d : ℕ} (hd : 0 < d)
    (c : List.Vector (Word (baseWidth p t)) d)
    (hz : BinaryArithmetic.toNat cache.zero.val < p^t) (ho : BinaryArithmetic.toNat cache.one.val < p^t)
    (n : ℕ) (i : Fin d) :
    (iterData p t M cache.zero cache.minusOne c n (initialData d cache.one cache.zero)).coefficients.get i =
      (RingProgram.powerVectorRun (RingProgram.scalarProgram p t M cache) c.get n).1 i := by
  apply RingProgram.word_eq_of_value p t
  · exact powerData_canonical p t M cache c hz ho n i
  · exact callbackPower_canonical p t M cache c.get hz ho n i
  · have h := congrFun (powerData_decode p t M hd cache.one cache.zero cache.minusOne
      cache.one_correct cache.zero_correct cache.minusOne_correct c n) i
    have h' := congrFun (RingProgram.powerVectorRun_correct
      (RingProgram.scalarRing p t M cache) c.get n) i
    exact h.trans h'.symm

end SubexponentialSAT.SqrtLog.RingProgramTable

end OAI.Algorithms
