import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentProgramFinal
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

namespace OAI.Algorithms

/-! A fixed finite bit program constructs the ternary H-adic lift from its
binary precision alone. Preparation, array arithmetic, iteration and output
serialization are all covered by actual bit-instruction traces. -/
namespace SubexponentialSAT.SqrtLog.IdempotentProgram

open scoped BigOperators
open BitProgram StructuredCalls SubexpQuarticRing
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

abbrev completeCommand : Cmd 8 41 :=
  .seq IdempotentPreparationProgram.preparation (.call newtonProgram)

def completeProgram := compiled completeCommand 31 32

def completeBudget (t inputWidth : ℕ) : ℕ :=
  IdempotentPreparationProgram.preparationBudget t inputWidth +
    nativeLiftBudget t (inputWidth+1)+1

theorem nativeLiftBudget_mono (t : ℕ) {a b : ℕ} (h : a ≤ b) :
    nativeLiftBudget t a ≤ nativeLiftBudget t b := by
  unfold nativeLiftBudget
  gcongr

/-- The input has only the binary precision in stack 31. No arithmetic table,
constants, counter, advice or other prepared data is supplied to the machine. -/
theorem completeProgram_runs (bits : List Bool) (t : ℕ)
    (hv : CounterPrograms.value bits=t) (ht : 0 < t) :
    ∃ next : RegisterData, ∃ (M : SubexpPreparedQuartic.Modulus 3 t),
      ∃ (cache : RingProgram.ScalarCache 3 t) (u : RingProgram.ScalarCode 3 t),
      RunsIn completeProgram (completeBudget t bits.length)
        ((IdempotentPreparationProgram.inputData bits).withPC (some completeProgram.entry))
        (next.withPC none) ∧
      next.stacks 32=RingProgram.flat (binaryLiftWords t M cache u) ∧
      (2 : ZMod (3^t))*wordValue 3 t u=1 := by
  obtain ⟨np,prepared,M,cache,u,hp,ready,hnp⟩ :=
    IdempotentPreparationProgram.preparation_eval bits t hv ht
  obtain ⟨next,⟨nl,hnl,hl⟩,hout⟩ := nativeLiftWords_run t M cache ready.zeroCanonical u
    (List.replicate (3*t) true) (List.replicate (2*t) true)
    (by simp) (by simp [RingProgram.ternary_baseWidth])
    (IdempotentPreparationProgram.initialRegisters t M cache u) prepared
    ready.encoded rfl ready.counter ready.loopScratch
  have hbound := nativeLiftBudget_mono t ready.counterLength
  refine ⟨next,M,cache,u,⟨np+nl+1,?_,?_⟩,hout,ready.inverse⟩
  · unfold completeBudget
    omega
  · exact compiled_halt_trace (hp.seq (Eval.call newtonProgram hl)) 31 32

theorem completeProgram_output_length (t : ℕ)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (u : RingProgram.ScalarCode 3 t) :
    (RingProgram.flat (binaryLiftWords t M cache u)).length=6*t^2 := by
  rw [RingProgram.flat_length,RingProgram.ternary_baseWidth]
  ring

variable {R K : Type*} [CommRing R] [CommRing K]

/-- The actual output words are t polynomials of degree below three whose
H-adic sum is the required local indicator. -/
theorem completeProgram_indicator [DecidableEq K]
    (bits : List Bool) (t : ℕ) (hv : CounterPrograms.value bits=t) (ht : 0 < t)
    (φ : ZMod (3^t) →+* R) (ρ : R →+* K)
    (q : R) (hq : q^t=0) (hker : ∀ y, ρ y=0 → q∣y)
    (x : R) (hx : ρ x=0 ∨ ρ x=1 ∨ ρ x=2) :
    ∃ next : RegisterData, ∃ (M : SubexpPreparedQuartic.Modulus 3 t),
      ∃ (cache : RingProgram.ScalarCache 3 t) (u : RingProgram.ScalarCode 3 t),
      RunsIn completeProgram (completeBudget t bits.length)
        ((IdempotentPreparationProgram.inputData bits).withPC (some completeProgram.entry))
        (next.withPC none) ∧
      next.stacks 32=RingProgram.flat (binaryLiftWords t M cache u) ∧
      (∑ s : Fin t,
        (digitPolynomial (RingProgram.scalarRing 3 t M cache)
          (binaryLiftWords t M cache u) s).eval₂ φ x * hValue x^s.val) =
        if ρ x=0 then 1 else 0 := by
  obtain ⟨next,M,cache,u,hr,hout,hu⟩ := completeProgram_runs bits t hv ht
  exact ⟨next,M,cache,u,hr,hout,binaryLiftWords_indicator t M cache u hu φ ρ q hq hker x hx⟩

end SubexponentialSAT.SqrtLog.IdempotentProgram

end OAI.Algorithms
