import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpEmptyClauseProgram

namespace OAI.Algorithms

/-! Actual classification of the two trivial leaf cases. The empty formula
and an empty clause are detected separately on the preserved encoded leaf. -/

namespace SubexponentialSAT.SqrtLog.LeafProgram.Trivial

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev Data := State 10 10

abbrev command : Cmd 10 10 :=
  .seq (.call SubexpEmptyClauseProgram.program) (.base (.atom (.peek 9 7 8)))

def result (a : Data) (records : List (List Bool)) : Data :=
  ⟨readRegs (SubexpEmptyClauseProgram.result a (decide ([false] ∈ records))).regs 7 8
      (Encoding.encodeList id records).head?, a.stacks⟩

theorem command_eval (a : Data) (records : List (List Bool))
    (hbody : a.stacks 9 = Encoding.encodeList id records) (hready : SubexpEmptyClauseProgram.Ready a) :
    ∃ cost ≤ 100*((a.stacks 9).length+1)+2,
      Eval command cost a (result a records) := by
  obtain ⟨k,hk,he⟩ := SubexpEmptyClauseProgram.program_runsIn records a hbody hready
  have hp := Eval.base (StructuredProgram.Eval.atom
    (StructuredProgram.Atom.peek (9 : Fin 10) (7 : Fin 10) 8)
    (SubexpEmptyClauseProgram.result a (decide ([false] ∈ records))))
  have hresult : (StructuredProgram.Atom.peek (9 : Fin 10) (7 : Fin 10) 8).eval
      (SubexpEmptyClauseProgram.result a (decide ([false] ∈ records))) = result a records := by
    simp only [StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg,execInstr,
      SubexpEmptyClauseProgram.result,result,hbody]
  rw [hresult] at hp
  exact ⟨k+1,by omega,(Eval.call _ he).seq hp⟩

@[simp] theorem result_stacks (a : Data) (records : List (List Bool)) :
    (result a records).stacks = a.stacks := rfl

theorem result_nonempty (a : Data) (records : List (List Bool)) :
    (result a records).regs 7 = decide (records ≠ []) := by
  cases records <;> simp [result,readRegs,Encoding.encodeList]

theorem result_empty_clause (a : Data) (records : List (List Bool)) :
    (result a records).regs 0 = decide ([false] ∈ records) := by
  simp [result,readRegs,SubexpEmptyClauseProgram.result]

theorem result_formula_empty_clause {α : Type*} [DecidableEq α] (encode : α → List Bool)
    (a : Data) (F : List (List α)) :
    (result a (F.map (Encoding.encodeList encode))).regs 0 = decide ([] ∈ F) := by
  simp only [result_empty_clause,SubexpEmptyClauseProgram.empty_record_iff]

theorem result_formula_nonempty {α : Type*} [DecidableEq α] (encode : α → List Bool)
    (a : Data) (F : List (List α)) :
    (result a (F.map (Encoding.encodeList encode))).regs 7 = decide (F ≠ []) := by
  rw [result_nonempty]
  simp

def program := compiled command 9 9

theorem program_run (a : Data) (records : List (List Bool))
    (hbody : a.stacks 9 = Encoding.encodeList id records) (hready : SubexpEmptyClauseProgram.Ready a) :
    RunsIn program (100*((a.stacks 9).length+1)+3)
      (a.withPC (some program.entry)) ((result a records).withPC none) := by
  obtain ⟨k,hk,he⟩ := command_eval a records hbody hready
  exact ⟨k+1,by omega,compiled_halt_trace he 9 9⟩

end SubexponentialSAT.SqrtLog.LeafProgram.Trivial

end OAI.Algorithms
