import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgramScalarOutput

namespace OAI.Algorithms

/-! Native scalar preparation contract for the 41-stack H-adic setup.
All generated constants are canonical; the selector and array builder receive
exact functional words. The only unbounded iteration uses cached unary t. -/
namespace SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar
open BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing BinaryArithmetic
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

structure Prepared (t:ℕ) (M:SubexpPreparedQuartic.Modulus 3 t)
    (cache:RingProgram.ScalarCache 3 t) (u:RingProgram.ScalarCode 3 t) (d:Data) : Prop where
  table : ∀i:Fin 6,d.stacks (port (tableRegister i))=
    (IdempotentProgram.integerRun (RingProgram.scalarProgram 3 t M cache)
      (IdempotentTableEntryProgram.codeValue i)).1.val
  zero : d.stacks 17=cache.zero.val
  one : d.stacks 18=cache.one.val
  half : d.stacks 27=u.val
  minusOne : d.stacks 28=cache.minusOne.val
  twice : d.stacks 30=(SubexpPreparedQuartic.wordAdd 3 t M u u).1.val
  minusThree : d.stacks 31=(SubexpPreparedQuartic.wordMul 3 t M
    (SubexpPreparedQuartic.wordAdd 3 t M (SubexpPreparedQuartic.wordAdd 3 t M u u).1 u).1 cache.minusOne).1.val
  inverse : (2:ZMod (3^t))*wordValue 3 t u=1
  minusOneCanonical : BinaryArithmetic.toNat cache.minusOne.val < 3^t
  zeroCanonical : BinaryArithmetic.toNat cache.zero.val < 3^t
  oneCanonical : BinaryArithmetic.toNat cache.one.val < 3^t
  rest : Rest d M.bits
  temporary24 : d.stacks 24=[]
  temporary25 : d.stacks 25=[]

theorem command_prepares (t:ℕ) (ht:0 < t) (M:SubexpPreparedQuartic.Modulus 3 t)
    (shape:List Bool) (hs:shape.length=baseWidth 3 t) (d:Data) (W:ℕ)
    (h:Rest d M.bits) (h12:d.stacks 12=shape) (hW:shape.length ≤ W)
    (hslots:∀i,(d.stacks (port i)).length ≤ W)
    (h29:d.stacks 29=List.replicate t true) (h40:d.stacks 40=[]) :
    ∃ n e cache u, Eval command n d e ∧ Prepared t M cache u e ∧ Frame d e ∧
      n ≤ 400*(baseWidth 3 t+W+1)+(3*t+10)*stepBudget 3 t+9*t+4*baseWidth 3 t+13 := by
  let v:=baseValues t M shape hs
  have hv:=baseValues_correct t ht M shape hs
  let cache:=generatedCache t M v hv.1 hv.2.1 hv.2.2.1
  let u:=finalValues t M v 8
  obtain ⟨n,e,he,ho,hf,hn⟩:=command_eval t M shape hs d W h h12 hW hslots h29 h40
  have hc:Canonical 3 t v:=hv.2.2.2
  have hcoeff:=final_coefficients t M v
  refine ⟨n,e,cache,u,he,?_,hf,hn⟩
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,ho.1,ho.2.1,ho.2.2.1⟩
  · intro i
    rw [ho.2.2.2 (tableRegister i) (by fin_cases i <;> decide) (by fin_cases i <;> decide)]
    exact congrArg Subtype.val (generated_table t M v hv.1 hv.2.1 hv.2.2.1 hc i).symm
  · exact ho.2.2.2 0 (by decide) (by decide)
  · exact ho.2.2.2 1 (by decide) (by decide)
  · exact ho.2.2.2 8 (by decide) (by decide)
  · exact ho.2.2.2 9 (by decide) (by decide)
  · rw [show e.stacks 30=(finalValues t M v 10).val from ho.2.2.2 10 (by decide) (by decide)]
    exact congrArg Subtype.val hcoeff.1
  · rw [show e.stacks 31=(finalValues t M v 11).val from ho.2.2.2 11 (by decide) (by decide)]
    simpa [cache,u,generatedCache,hcoeff.1] using congrArg Subtype.val hcoeff.2
  · exact (final_half t M v hv.1 hv.2.1 hv.2.2.1).1
  · exact final_canonical t M v hc 9
  · exact final_canonical t M v hc 0
  · exact final_canonical t M v hc 1

/-- Canonical scalar zero is literally the all-false fixed-width word. -/
theorem canonical_zero_bytes (t:ℕ) (cache:RingProgram.ScalarCache 3 t)
    (hz:BinaryArithmetic.toNat cache.zero.val < 3^t) :
    cache.zero.val=List.replicate (baseWidth 3 t) false := by
  have hn:∀n,BinaryArithmetic.toNat (List.replicate n false)=0 := by
    intro n; induction n with
    | zero=>rfl
    | succ n ih=>simp [List.replicate_succ,bitVal,ih]
  have he:cache.zero=SubexpPreparedQuartic.zeroWord 3 t := by
    apply RingProgram.word_eq_of_value 3 t _ _ hz
    · change BinaryArithmetic.toNat (List.replicate (baseWidth 3 t) false) < 3^t
      rw [hn]; positivity
    · rw [cache.zero_correct,SubexpPreparedQuartic.zeroWord_value]
  exact congrArg Subtype.val he

theorem budget_polynomial (t W:ℕ) :
    400*(baseWidth 3 t+W+1)+(3*t+10)*stepBudget 3 t+9*t+4*baseWidth 3 t+13
      ≤ 500000*(t+W+1)^3 := by
  simp only [stepBudget,RingProgram.ternary_baseWidth]
  nlinarith [Nat.zero_le (t^3),Nat.zero_le (t*W),Nat.zero_le (t^2*W),Nat.zero_le (t*W^2),Nat.zero_le (W^3)]

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar

end OAI.Algorithms
