import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgramTableRun
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgramScalar

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

open BitProgram StructuredCalls SubexpQuarticRing
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

theorem entrySource_eq_scalar (c : Fin 6) :
    entrySource c = Scalar.port (Scalar.tableRegister c) := by
  fin_cases c <;> rfl

theorem prepared_zero (t : ℕ) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (u : RingProgram.ScalarCode 3 t)
    (d : Data) (hp : Scalar.Prepared t M cache u d) :
    d.stacks 17 = cache.zero.val := by
  exact hp.zero

theorem prepared_source_width (t : ℕ) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (u : RingProgram.ScalarCode 3 t)
    (d : Data) (hp : Scalar.Prepared t M cache u d) (c : Fin 6) :
    (d.stacks (entrySource c)).length = SubexpLiftRing.baseWidth 3 t := by
  rw [entrySource_eq_scalar,hp.table]
  exact (IdempotentProgram.integerRun (RingProgram.scalarProgram 3 t M cache)
    (IdempotentTableEntryProgram.codeValue c)).1.property

theorem prepared_tableCells (t : ℕ) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (u : RingProgram.ScalarCode 3 t)
    (d : Data) (hp : Scalar.Prepared t M cache u d) :
    Scan.tableCells (cachedEntry d.stacks) (3*t) =
      IdempotentProgram.tableTape (IdempotentProgram.tableCode (t := t) (RingProgram.scalarProgram 3 t M cache)) := by
  apply Scan.tableCells_eq_tableTape
  intro i j k
  rw [cachedEntry,entrySource_eq_scalar,hp.table,IdempotentTableEntryProgram.entryCode_correct]
  simp only [IdempotentProgram.tableCode_apply,IdempotentProgram.tableRun]

theorem prepared_nativeTable_eval (t : ℕ) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (u : RingProgram.ScalarCode 3 t)
    (d : Data) (hp : Scalar.Prepared t M cache u d)
    (h37 : d.stacks 37=List.replicate (3*t) true)
    (h26 : d.stacks 26=[]) (h22 : d.stacks 22=[]) :
    ∃ cost rf, cost ≤ Scan.tableBudget (3*t) (200*(3*t+SubexpLiftRing.baseWidth 3 t+1)) ∧
      Eval nativeTable cost d ⟨rf,Function.update d.stacks 22
        (IdempotentProgram.tableTape (IdempotentProgram.tableCode (t := t) (RingProgram.scalarProgram 3 t M cache)))⟩ := by
  have h0 : d.stacks 0=[] := hp.rest.1 0
  have h1 : d.stacks 1=[] := hp.rest.1 1
  have h2 : d.stacks 2=[] := hp.rest.1 2
  have h3 : d.stacks 3=[] := hp.rest.1 3
  have h4 : d.stacks 4=[] := hp.rest.1 4
  obtain ⟨cost,rf,hcost,he⟩ := nativeTable_eval d (3*t) (SubexpLiftRing.baseWidth 3 t)
    h37 hp.temporary24 hp.temporary25 h26 hp.rest.2 h0 h1 h2 h3 h4
    (fun c => (prepared_source_width t M cache u d hp c).le)
  refine ⟨cost,rf,hcost,?_⟩
  simpa only [prepared_tableCells t M cache u d hp,h22,List.append_nil] using he

theorem prepared_pool_length (t : ℕ) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (u : RingProgram.ScalarCode 3 t)
    (d : Data) (hp : Scalar.Prepared t M cache u d) (i : Scalar.Reg) :
    (d.stacks (Scalar.port i)).length ≤ SubexpLiftRing.baseWidth 3 t := by
  fin_cases i
  · exact (prepared_source_width t M cache u d hp 0).le
  · exact (prepared_source_width t M cache u d hp 1).le
  · exact (prepared_source_width t M cache u d hp 3).le
  · exact (prepared_source_width t M cache u d hp 2).le
  · exact (prepared_source_width t M cache u d hp 4).le
  · exact (prepared_source_width t M cache u d hp 5).le
  · simp [Scalar.port,hp.temporary24]
  · simp [Scalar.port,hp.temporary25]
  · simp [Scalar.port,hp.half,u.property]
  · simp [Scalar.port,hp.minusOne,cache.minusOne.property]
  · change (d.stacks 30).length ≤ _
    rw [hp.twice]
    exact (SubexpPreparedQuartic.wordAdd 3 t M u u).1.property.le
  · change (d.stacks 31).length ≤ _
    rw [hp.minusThree]
    exact (SubexpPreparedQuartic.wordMul 3 t M
      (SubexpPreparedQuartic.wordAdd 3 t M (SubexpPreparedQuartic.wordAdd 3 t M u u).1 u).1
      cache.minusOne).1.property.le

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

end OAI.Algorithms
