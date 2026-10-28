import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpOrderedTupleData
import OAI.Algorithms.SubexponentialSAT.SubexpNormalizeProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.BlockSearchPreparation

namespace OAI.Algorithms

/-! # A fixed Cartesian expansion in exact enumeration order -/

namespace SubexponentialSAT.SubexpOrderedTupleStep

open BitProgram StructuredCalls Subexp.TupleProgram SubexpOrderedTupleData
open Subexp.BlockSearchPreparation (restrictState lifted_call)

def reverseRegisters : Fin 3 → Fin 10 := ![0,1,2]
def reverseStacks : Fin 4 → Fin 9 := ![5,1,0,2]

theorem reverseRegisters_injective : Function.Injective reverseRegisters := by decide
theorem reverseStacks_injective : Function.Injective reverseStacks := by decide

abbrev reverseRecords : Cmd 10 9 :=
  .call (ProgramLinking.liftProgram SubexpNormalizeProgram.reverseRecordsProgram
    reverseRegisters reverseStacks)

theorem reverseRecords_eval (records : Records) (a : State 10 9)
    (h0 : a.stacks 0 = [false]) (h2 : a.stacks 2 = [])
    (h5 : a.stacks 5 = ProgramEncoding.encodeRecords records) :
    ∃ n next, n ≤ 10 * (ProgramEncoding.encodeRecords records).length ∧
      next.stacks 0 = ProgramEncoding.encodeRecords records.reverse ∧
      next.stacks 2 = [] ∧ next.stacks 5 = [] ∧
      (∀ i, i ≠ 0 → i ≠ 2 → i ≠ 5 → next.stacks i = a.stacks i) ∧
      next.regs 9 = a.regs 9 ∧ Eval reverseRecords n a next := by
  let small := SubexpNormalizeProgram.filterState false true false [] (a.stacks 1)
    (ProgramEncoding.encodeRecords records.reverse) []
  have hstart : restrictState reverseRegisters reverseStacks a =
      SubexpNormalizeProgram.filterState (a.regs 0) (a.regs 1) (a.regs 2)
        (ProgramEncoding.encodeRecords records) (a.stacks 1) [false] [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i
      fin_cases i <;> simp [reverseRegisters,SubexpPostfixControl.triple]
    · funext i
      fin_cases i <;> simp [reverseStacks,SubexpPostfixControl.quadruple,h0,h2,h5]
  have hr := SubexpNormalizeProgram.reverseRecords_runsIn records [] [] (a.stacks 1)
    (a.regs 0) (a.regs 1) (a.regs 2)
  obtain ⟨n,hn,he⟩ := lifted_call SubexpNormalizeProgram.reverseRecordsProgram
    reverseRegisters reverseStacks reverseRegisters_injective reverseStacks_injective
    a small (10 * (ProgramEncoding.encodeRecords records).length)
    (by simpa [hstart,small,ProgramEncoding.encodeRecords,Encoding.encodeList] using hr)
  refine ⟨n,embedState reverseRegisters reverseStacks a small,hn,?_,?_,?_,?_,?_,he⟩
  · simpa [reverseStacks,small,SubexpNormalizeProgram.filterState,
      SubexpPostfixControl.quadruple] using
      embedState_stack reverseRegisters reverseStacks a small reverseStacks_injective 2
  · simpa [reverseStacks,small,SubexpNormalizeProgram.filterState,
      SubexpPostfixControl.quadruple] using
      embedState_stack reverseRegisters reverseStacks a small reverseStacks_injective 3
  · simpa [reverseStacks,small,SubexpNormalizeProgram.filterState,
      SubexpPostfixControl.quadruple] using
      embedState_stack reverseRegisters reverseStacks a small reverseStacks_injective 0
  · intro i hi0 hi2 hi5
    by_cases hi1 : i = 1
    · subst i
      simpa [reverseStacks,small,SubexpNormalizeProgram.filterState,
        SubexpPostfixControl.quadruple] using
        embedState_stack reverseRegisters reverseStacks a small reverseStacks_injective 1
    · apply embedState_stack_frame
      rintro ⟨j,hj⟩
      fin_cases j <;> simp_all [reverseStacks]
  · apply embedState_register_frame
    rintro ⟨j,hj⟩
    fin_cases j <;> simp [reverseRegisters] at hj

/-- Expand all tuples, reverse the record order, and restore the empty
accumulator. Every loop is in the two fixed called programs. -/
abbrev step : Cmd 10 9 :=
  .seq cartesianCmd (.seq (pushConst 0 6 false)
    (.seq reverseRecords (pushConst 5 6 false)))

def stepCost (rows alphabet : Records) : ℕ :=
  expansionCost rows alphabet +
    10 * (ProgramEncoding.encodeRecords (cartesianOutput rows alphabet)).length + 4

theorem step_eval (alphabet rows : Records) (depth : List Bool) (guard : Bool)
    (a : State 10 9) (ha : Ready alphabet rows depth guard a) :
    ∃ n next, n ≤ stepCost rows alphabet ∧
      Ready alphabet (orderedCartesian rows alphabet) depth guard next ∧
      Eval step n a next := by
  obtain ⟨n,b,hn,hb,hb0,hb2,hb5,ht⟩ :=
    cartesian_eval rows alphabet [] depth guard a ha.1 ha.2.1 ha.2.2.1 ha.2.2.2
  simp only [List.append_nil] at hb5
  let c := pushedState 0 6 false b
  have hc0 : c.stacks 0 = [false] := by simp [c,hb0]
  have hc2 : c.stacks 2 = [] := by simp [c,hb2]
  have hc5 : c.stacks 5 = ProgramEncoding.encodeRecords (cartesianOutput rows alphabet) := by
    simp [c,hb5]
  obtain ⟨m,d,hm,hd0,hd2,hd5,hframe,hreg,hr⟩ :=
    reverseRecords_eval (cartesianOutput rows alphabet) c hc0 hc2 hc5
  let e := pushedState 5 6 false d
  have h1 := pushConst_eval 0 6 false b
  have h2 := pushConst_eval 5 6 false d
  refine ⟨n + (2 + (m + 2)),e,?_,?_,ht.seq (h1.seq (hr.seq h2))⟩
  · dsimp [stepCost]
    omega
  · rcases hb with ⟨hb1,hb3,hb4,hb6,hb7,hb8,hb9⟩
    have hd1 := hframe 1 (by decide) (by decide) (by decide)
    have hd3 := hframe 3 (by decide) (by decide) (by decide)
    have hd4 := hframe 4 (by decide) (by decide) (by decide)
    have hd6 := hframe 6 (by decide) (by decide) (by decide)
    have hd7 := hframe 7 (by decide) (by decide) (by decide)
    have hd8 := hframe 8 (by decide) (by decide) (by decide)
    simp [Ready,outerInvariant,e,hd0,hd2,hd5,hd1,hd3,hd4,hd6,hd7,hd8,
      hreg,c,hb1,hb3,hb4,hb6,hb7,hb8,hb9,orderedCartesian_eq_reverse]

end SubexponentialSAT.SubexpOrderedTupleStep

end OAI.Algorithms
