import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpNormalizeProgram
import OAI.Algorithms.SubexponentialSAT.ProgramFrames

namespace OAI.Algorithms

/-! Shared actual record reversal for the clause-filter storage layout. -/

namespace SubexponentialSAT.ExecClauseFilterReverse

open BitProgram StructuredCalls

abbrev Regs := Fin 15 → Bool
abbrev Data := State 15 16

def state (regs : Regs) (source output payload : List Bool) : Data :=
  ⟨regs, ![[], [], [], [], [], [], [], [], [], [], [], [], [], source, output, payload]⟩

def flags (regs : Regs) (value present found : Bool) : Regs :=
  Function.update (Function.update (Function.update regs 0 value) 1 present) 14 found

theorem flags_self (regs : Regs) : flags regs (regs 0) (regs 1) (regs 14) = regs := by
  funext i
  by_cases h0 : i = 0 <;> by_cases h1 : i = 1 <;> by_cases h14 : i = 14 <;>
    simp_all [flags ]

def regPort : Fin 3 → Fin 15 := ![0, 1, 14]
def stackPort : Fin 4 → Fin 16 := ![14, 9, 13, 15]

theorem regPort_injective : Function.Injective regPort := by decide
theorem stackPort_injective : Function.Injective stackPort := by decide

def program := ProgramLinking.liftProgram
  SubexpNormalizeProgram.reverseRecordsProgram regPort stackPort
abbrev command : Cmd 15 16 := .call program

private theorem embed_reverse (regs : Regs) (value present found : Bool)
    (source0 output0 payload0 source output payload : List Bool) :
    embedState regPort stackPort (state regs source0 output0 payload0)
      (SubexpNormalizeProgram.filterState value present found source [] output payload) =
      state (flags regs value present found) output source payload := by
  apply embedState_eq_of_ports regPort stackPort _ _ _ regPort_injective stackPort_injective
  · intro i
    fin_cases i <;> simp [regPort, flags, state, SubexpNormalizeProgram.filterState,
      SubexpPostfixControl.triple]
  · intro i hi
    have h0 : i ≠ 0 := fun h => hi ⟨0, h.symm⟩
    have h1 : i ≠ 1 := fun h => hi ⟨1, h.symm⟩
    have h14 : i ≠ 14 := fun h => hi ⟨2, h.symm⟩
    simp [state, flags, h0, h1, h14]
  · intro i
    fin_cases i <;> rfl
  · intro i hi
    have h14 : i ≠ 14 := fun h => hi ⟨0, h.symm⟩
    have h9 : i ≠ 9 := fun h => hi ⟨1, h.symm⟩
    have h13 : i ≠ 13 := fun h => hi ⟨2, h.symm⟩
    have h15 : i ≠ 15 := fun h => hi ⟨3, h.symm⟩
    fin_cases i <;> simp_all [state]

/-- Reverse whole records from stack 14 onto the encoded accumulator in
stack 13. All thirteen work stacks and payload stack 15 finish empty. -/
theorem reverse_eval (records acc : List (List Bool)) (regs : Regs) :
    ∃ n ≤ 10 * (Encoding.encodeList id records).length,
      Eval command n
        (state regs (Encoding.encodeList id acc) (Encoding.encodeList id records) [])
        (state (flags regs false true false)
          (Encoding.encodeList id (records.reverse ++ acc)) [] []) := by
  obtain ⟨n, hn, ht⟩ := SubexpNormalizeProgram.reverseRecords_runsIn records acc [] []
    (regs 0) (regs 1) (regs 14)
  simp only [List.append_nil] at ht
  have he := eval_call_lifted SubexpNormalizeProgram.reverseRecordsProgram regPort stackPort
    (state regs (Encoding.encodeList id acc) (Encoding.encodeList id records) [])
    regPort_injective stackPort_injective ht
  refine ⟨n, hn, ?_⟩
  simpa only [embed_reverse, flags_self, command, program] using he

end SubexponentialSAT.ExecClauseFilterReverse

end OAI.Algorithms
