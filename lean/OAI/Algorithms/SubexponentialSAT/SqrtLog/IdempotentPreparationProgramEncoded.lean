import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgramEncoding
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgramFinish
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentProgramMachine

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

open SubexpQuarticRing
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

def initialRegisters (t : ℕ) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (u : RingProgram.ScalarCode 3 t) :
    IdempotentProgram.Registers (RingProgram.Code (RingProgram.ScalarCode 3 t) (3*t)) :=
  fun _ => (IdempotentProgram.initialRun (RingProgram.scalarProgram 3 t M cache) t u).1

theorem finished_encoded (t : ℕ) (ht : 0 < t) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (u : RingProgram.ScalarCode 3 t)
    (d e : Data) (hp : Scalar.Prepared t M cache u d)
    (h12 : d.stacks 12=List.replicate (2*t) true)
    (h37 : d.stacks 37=List.replicate (3*t) true)
    (he : e.stacks=finishedStacks d.stacks t
      (IdempotentProgram.tableTape (IdempotentProgram.tableCode (t := t) (RingProgram.scalarProgram 3 t M cache)))) :
    IdempotentProgram.RegistersEncoded M.bits (List.replicate (2*t) true) cache.zero.val
      (RingTriple.tableEncoding (IdempotentProgram.tableCode (t := t) (RingProgram.scalarProgram 3 t M cache)))
      (List.replicate (3*t) true)
      (IdempotentProgram.minusOneRun (RingProgram.scalarProgram 3 t M cache) t).1
      (initialRegisters t M cache u) e := by
  have h5 : d.stacks 5=M.bits := hp.rest.1 5
  have hz : d.stacks 17=cache.zero.val := prepared_zero t M cache u d hp
  have hi : d.stacks 30 ++ d.stacks 31 ++ d.stacks 27 ++
      Subexp.BlockCopyProgram.copies (3*t-3) (d.stacks 17) =
      RingProgram.flat (IdempotentProgram.initialRun (RingProgram.scalarProgram 3 t M cache) t u).1 := by
    rw [initialRun_flat _ t ht u]
    simp [hp.twice,hp.minusThree,hp.half,hz,RingProgram.scalarProgram]
  have hm : d.stacks 28 ++ Subexp.BlockCopyProgram.copies (3*t-1) (d.stacks 17) =
      RingProgram.flat (IdempotentProgram.minusOneRun (RingProgram.scalarProgram 3 t M cache) t).1 := by
    rw [minusOneRun_flat 3 t M cache ht hp.zeroCanonical hp.minusOneCanonical]
    rw [hp.minusOne,hz]
  rw [←IdempotentProgram.tableTape_eq_encoding]
  constructor
  · intro i
    fin_cases i <;>
      simp [he,finishedStacks,arrayStacks,preparationDiscard,IdempotentProgram.servicePorts,
        RingScan.serviceState,RingScan.serviceWorkState,RingScan.serviceTapes,h5,h12,hz]
  · intro i
    fin_cases i <;>
      simpa [he,finishedStacks,arrayStacks,preparationDiscard,IdempotentProgram.arrayRegister,
        initialRegisters] using hi
  · simpa [he,finishedStacks,arrayStacks,preparationDiscard] using hm
  · simp [he,finishedStacks,arrayStacks,preparationDiscard,h37]
  · simp [he,finishedStacks,preparationDiscard]

theorem finished_counter (t : ℕ) (d e : Data) (table : List Bool)
    (he : e.stacks=finishedStacks d.stacks t table) :
    e.stacks 39=d.stacks 39 ∧ e.stacks 40=[] := by
  simp [he,finishedStacks,arrayStacks,preparationDiscard]

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

end OAI.Algorithms
