import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentProgramComplete

namespace OAI.Algorithms

/-! An explicit polynomial primitive-time envelope for native preparation
and all Newton iterations, as a function of precision and input length. -/
namespace SubexponentialSAT.SqrtLog.IdempotentProgram

open BitProgram

theorem binaryClog_le (t : ℕ) : Nat.clog 2 t ≤ t := by
  have hp : t+1 ≤ 2^t := by
    induction t with
    | zero => simp
    | succ t ih =>
      rw [pow_succ]
      omega
  exact (Nat.le_pow_iff_clog_le (by decide)).mp (by omega)

def polynomialBudget (t inputWidth : ℕ) : ℕ :=
  100000000*(t+inputWidth+2)^4 +
  7*t*(41000*(3*t+1)^3*(2*t+1)^2) +
  (t+1)*(16*(inputWidth+1)+16)+2

theorem completeBudget_polynomial (t inputWidth : ℕ) :
    completeBudget t inputWidth ≤ polynomialBudget t inputWidth := by
  have hp:=IdempotentPreparationProgram.preparationBudget_polynomial t inputWidth
  have ha:=arithmeticBudget_polynomial (SubexpLiftRing.baseWidth 3 t) (3*t)
  rw [RingProgram.ternary_baseWidth] at ha
  have hl:=binaryClog_le t
  unfold completeBudget nativeLiftBudget polynomialBudget
  rw [RingProgram.ternary_baseWidth]
  calc
    _ ≤ 100000000*(t+inputWidth+2)^4 +
        (7*t*(41000*(3*t+1)^3*(2*t+1)^2)+
          (t+1)*(16*(inputWidth+1)+16)+1)+1 := by gcongr
    _ = _ := by omega

theorem completeProgram_polynomial (bits : List Bool) (t : ℕ)
    (hv : CounterPrograms.value bits=t) (ht : 0 < t) :
    ∃ next : RegisterData, ∃ (M : SubexpPreparedQuartic.Modulus 3 t),
      ∃ (cache : RingProgram.ScalarCache 3 t) (u : RingProgram.ScalarCode 3 t),
      RunsIn completeProgram (polynomialBudget t bits.length)
        ((IdempotentPreparationProgram.inputData bits).withPC (some completeProgram.entry))
        (next.withPC none) ∧
      next.stacks 32=RingProgram.flat (binaryLiftWords t M cache u) ∧
      (2 : ZMod (3^t))*SubexpQuarticRing.wordValue 3 t u=1 := by
  obtain ⟨next,M,cache,u,⟨n,hn,hr⟩,ho,hu⟩:=completeProgram_runs bits t hv ht
  exact ⟨next,M,cache,u,⟨n,hn.trans (completeBudget_polynomial t bits.length),hr⟩,ho,hu⟩

/-- Primitive execution of the fixed complete program, retaining the exact
computed output and its explicit inverse-of-two constant. -/
theorem completeProgram_primitive (bits : List Bool) (t : ℕ)
    (hv : CounterPrograms.value bits=t) (ht : 0 < t) :
    ∃ next : RegisterData, ∃ (M : SubexpPreparedQuartic.Modulus 3 t),
      ∃ (cache : RingProgram.ScalarCache 3 t) (u : RingProgram.ScalarCode 3 t),
      Computation.RunsIn (primitive completeProgram).step
        (primitiveOverhead completeProgram * polynomialBudget t bits.length)
        (primitiveCfg completeProgram
          ((IdempotentPreparationProgram.inputData bits).withPC (some completeProgram.entry)))
        (primitiveCfg completeProgram (next.withPC none)) ∧
      next.stacks 32=RingProgram.flat (binaryLiftWords t M cache u) ∧
      (2 : ZMod (3^t))*SubexpQuarticRing.wordValue 3 t u=1 := by
  obtain ⟨next,M,cache,u,hr,ho,hu⟩:=completeProgram_polynomial bits t hv ht
  exact ⟨next,M,cache,u,primitive_execution completeProgram hr,ho,hu⟩

end SubexponentialSAT.SqrtLog.IdempotentProgram

end OAI.Algorithms
