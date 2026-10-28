import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramConstants
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgramModel

namespace OAI.Algorithms

/-! The generated dynamic vectors are constants in the supplied ring model. -/

namespace SubexponentialSAT.SqrtLog.LeafProgram.Constants

open SubexponentialSAT.SubexpQuarticRing SubexponentialSAT.SubexpLiftRing RingProgramTable
open scoped BigOperators

def constantCode {B : ℕ} (d : ℕ) (seed zeroWord : Word B) : RingProgram.Code (Word B) d :=
  fun i => if i.val = 0 then seed else zeroWord

theorem constantCode_flat {B : ℕ} (d : ℕ) (seed zeroWord : Word B) :
    RingProgram.flat (constantCode d seed zeroWord) = literalBits d seed zeroWord := by
  induction d generalizing seed with
  | zero => simp [RingProgram.flat,literalBits]
  | succ d ih =>
    rw [RingProgram.flat,List.ofFn_succ,List.flatten_cons]
    change seed.val ++ RingProgram.flat (fun i : Fin d => constantCode (d+1) seed zeroWord i.succ) = _
    have htail : (fun i : Fin d => constantCode (d+1) seed zeroWord i.succ) =
        constantCode d zeroWord zeroWord := by
      funext i
      simp [constantCode]
    rw [htail,ih]

theorem constantCode_decode (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (model : RingModel.Data d) (M : SubexponentialSAT.SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (seed zeroWord : RingProgram.ScalarCode 3 t)
    (hz : wordValue 3 t zeroWord = 0) :
    (RingProgram.modelRing t ht hd model M cache).decode (constantCode d seed zeroWord) =
      SubexponentialSAT.LiftRing.of (model.F t) (wordValue 3 t seed) := by
  classical
  change (∑ i : Fin d, SubexponentialSAT.LiftRing.of (model.F t)
    (wordValue 3 t (constantCode d seed zeroWord i)) * RingBasis.basis (model.F t) i) = _
  rw [Finset.sum_eq_single (⟨0,hd⟩ : Fin d)]
  · simp [constantCode,RingBasis.basis]
  · intro i _ hi
    have hv : i.val ≠ 0 := by intro h; apply hi; exact Fin.ext h
    simp [constantCode,hv,hz]
  · simp

theorem one_decode (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (model : RingModel.Data d) (M : SubexponentialSAT.SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) :
    (RingProgram.modelRing t ht hd model M cache).decode
      (constantCode d cache.one cache.zero) = 1 := by
  rw [constantCode_decode t ht hd model M cache _ _ cache.zero_correct,cache.one_correct,map_one]

theorem zero_decode (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (model : RingModel.Data d) (M : SubexponentialSAT.SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) :
    (RingProgram.modelRing t ht hd model M cache).decode
      (constantCode d cache.zero cache.zero) = 0 := by
  rw [constantCode_decode t ht hd model M cache _ _ cache.zero_correct,cache.zero_correct,map_zero]

theorem minusOne_decode (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (model : RingModel.Data d) (M : SubexponentialSAT.SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) :
    (RingProgram.modelRing t ht hd model M cache).decode
      (constantCode d cache.minusOne cache.zero) = -1 := by
  rw [constantCode_decode t ht hd model M cache _ _ cache.zero_correct,cache.minusOne_correct,
    map_neg,map_one]

end SubexponentialSAT.SqrtLog.LeafProgram.Constants

end OAI.Algorithms
