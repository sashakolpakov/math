import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SquarefreeProgramLookupBound
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames

namespace OAI.Algorithms

/-!
# Native literal parsing and hash-specific incidence lookup

A literal payload is `key ++ [positive]`; the existing record parser supplies
its reversal. The key selects a variable in a physically selected hash slice.
The fixed command pops the polarity, copies and scans the saved incidence
slice, returns its framed dictionary payload, and reclaims both scan and query.
There is no circuit-evaluation instruction and no scope truth table.
-/
namespace SubexponentialSAT.SqrtLog.HashCircuitProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpRecordScan

abbrev Data := State 6 7

abbrev extend (d : State 5 6) (positive : Bool) (table : List Bool) : Data :=
  ⟨![d.regs 0,d.regs 1,d.regs 2,d.regs 3,d.regs 4,positive],
   ![d.stacks 0,d.stacks 1,d.stacks 2,d.stacks 3,d.stacks 4,d.stacks 5,table]⟩

abbrev data (regs : Fin 5 → Bool) (positive : Bool)
    (scan query output table : List Bool) : Data :=
  extend (recordState regs scan [] query [] [] output) positive table

theorem embed_extend (a b : State 5 6) (positive : Bool) (table : List Bool) :
    embedState Fin.castSucc Fin.castSucc (extend a positive table) b =
      extend b positive table := by
  apply embedState_eq_of_ports _ _ _ _ _ (Fin.castSucc_injective 5) (Fin.castSucc_injective 6)
  · intro i; fin_cases i <;> rfl
  · intro i hi
    fin_cases i <;> simp_all [ Fin.exists_fin_succ]
  · intro i; fin_cases i <;> rfl
  · intro i hi
    fin_cases i <;> simp_all [ Fin.exists_fin_succ]

abbrev lookupCall : Cmd 6 7 :=
  liftCommand Squarefree.Program.dictionaryLookup 0 5 Fin.castSucc Fin.castSucc

theorem lookupCall_eval (query : List Bool)
    (entries : List (List Bool × List Bool)) (regs : Fin 5 → Bool)
    (positive : Bool) (table : List Bool) :
    ∃ n ≤ Squarefree.Program.lookupBudget query entries + 3, ∃ regs' tail,
      Eval lookupCall n
        (data regs positive (Squarefree.Program.lookupRecords entries) query.reverse [] table)
        (data regs' positive tail query.reverse
          (Squarefree.Program.lookupResult (entries.lookup query)) table) ∧
      regs' 4 = (entries.lookup query).isSome ∧
      tail.length ≤ (Squarefree.Program.lookupRecords entries).length := by
  obtain ⟨n,hn,rr,tail,he,hflag,htail⟩ :=
    Squarefree.Program.dictionaryLookup_eval_tail query entries regs
  have hh := eval_liftCommand he 0 5 Fin.castSucc Fin.castSucc
    (data regs positive (Squarefree.Program.lookupRecords entries) query.reverse [] table)
    (Fin.castSucc_injective 5) (Fin.castSucc_injective 6)
  simp only [data, embed_extend] at hh
  exact ⟨n+1,by omega,rr,tail,hh,hflag,htail⟩

abbrev copy (src dst tmp : Fin 7) : Cmd 6 7 :=
  .call (StackRoutines.copyProgram src dst tmp (0 : Fin 6) 1)

def copied (d : Data) (src dst : Fin 7) : Data :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.copyStacks src dst d.stacks⟩

theorem copy_eval (d : Data) (src dst tmp : Fin 7)
    (hsd : src ≠ dst) (hst : src ≠ tmp) (htd : tmp ≠ dst)
    (htmp : d.stacks tmp = []) :
    Eval (copy src dst tmp) (7 * (d.stacks src).length + 5) d (copied d src dst) := by
  apply Eval.call
  have h := StackRoutines.copyProgram_trace src dst tmp (0 : Fin 6) 1
    hsd hst htd (by decide) d.regs d.stacks htmp
  have hh := StackRoutines.halt_after_trace _ h 7 rfl rfl
  simpa [copied,StackRoutines.copyResult,StructuredProgram.State.withPC,
    StackRoutines.copyProgram,Nat.add_assoc] using hh

abbrev clear (src : Fin 7) : Cmd 6 7 :=
  .call (StackRoutines.clearProgram src (0 : Fin 6) 1)

def cleared (d : Data) (src : Fin 7) : Data :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.clearStacks src d.stacks⟩

theorem clear_eval (d : Data) (src : Fin 7) :
    Eval (clear src) (2*(d.stacks src).length+3) d (cleared d src) := by
  apply Eval.call
  have h := StackRoutines.clearProgram_trace src (0 : Fin 6) 1 d.regs d.stacks
  have hh := StackRoutines.halt_after_trace _ h 2 rfl rfl
  simpa [cleared,StackRoutines.clearResult,StructuredProgram.State.withPC,
    StackRoutines.clearProgram,Nat.add_assoc] using hh

abbrev popLiteral : Cmd 6 7 := .base (.atom (.pop 2 5 1))

theorem popLiteral_eval (regs : Fin 5 → Bool) (old positive : Bool)
    (key table : List Bool) :
    Eval popLiteral 1 (data regs old [] (positive :: key.reverse) [] table)
      (data (Function.update regs 1 true) positive [] key.reverse [] table) := by
  convert (Eval.base (StructuredProgram.Eval.atom (.pop (2 : Fin 7) (5 : Fin 6) 1)
    (data regs old [] (positive :: key.reverse) [] table))) using 1
  apply congrArg₂ StructuredProgram.State.mk
  · funext i; fin_cases i <;>
      simp [StructuredProgram.Atom.instr,execInstr,readRegs]
  · funext i; fin_cases i <;>
      simp [StructuredProgram.Atom.instr,execInstr]

private theorem copied_data (regs : Fin 5 → Bool) (positive : Bool)
    (query output table : List Bool) :
    copied (data regs positive [] query output table) 6 0 =
      data (readRegs regs 0 1 none) positive table query output table := by
  apply congrArg₂ StructuredProgram.State.mk
  · funext i; fin_cases i <;> simp [readRegs]
  · funext i; fin_cases i <;> simp [StackRoutines.copyStacks]

private theorem cleared_scan (regs : Fin 5 → Bool) (positive : Bool)
    (scan query output table : List Bool) :
    cleared (data regs positive scan query output table) 0 =
      data (readRegs regs 0 1 none) positive [] query output table := by
  apply congrArg₂ StructuredProgram.State.mk
  · funext i; fin_cases i <;> simp [readRegs]
  · funext i; fin_cases i <;> simp [StackRoutines.clearStacks]

private theorem cleared_query (regs : Fin 5 → Bool) (positive : Bool)
    (query output table : List Bool) :
    cleared (data regs positive [] query output table) 2 =
      data (readRegs regs 0 1 none) positive [] [] output table := by
  apply congrArg₂ StructuredProgram.State.mk
  · funext i; fin_cases i <;> simp [readRegs]
  · funext i; fin_cases i <;> simp [StackRoutines.clearStacks]

/-- One fixed finite command, independent of variable indices, hash-row width,
coefficient widths, and the number of entries in the selected incidence slice. -/
abbrev literalFetch : Cmd 6 7 :=
  .seq popLiteral (.seq (copy 6 0 1) (.seq lookupCall (.seq (clear 0) (clear 2))))

def literalFetchBudget (key : List Bool) (entries : List (List Bool × List Bool)) : ℕ :=
  9*(Squarefree.Program.lookupRecords entries).length + 2*key.length +
    Squarefree.Program.lookupBudget key entries + 15

theorem literalFetch_eval (regs : Fin 5 → Bool) (old positive : Bool)
    (key : List Bool) (entries : List (List Bool × List Bool)) :
    ∃ n ≤ literalFetchBudget key entries, ∃ regs',
      Eval literalFetch n
        (data regs old [] (key ++ [positive]).reverse []
          (Squarefree.Program.lookupRecords entries))
        (data regs' positive [] [] (Squarefree.Program.lookupResult (entries.lookup key))
          (Squarefree.Program.lookupRecords entries)) ∧
      regs' 4 = (entries.lookup key).isSome := by
  let table := Squarefree.Program.lookupRecords entries
  let r1 := Function.update regs (1 : Fin 5) true
  let r2 := readRegs r1 0 1 none
  have hp := popLiteral_eval regs old positive key table
  have hc := copy_eval (data r1 positive [] key.reverse [] table) 6 0 1
    (by decide) (by decide) (by decide) rfl
  simp only [copied_data] at hc
  obtain ⟨n,hn,rr,tail,hl,hflag,htail⟩ := lookupCall_eval key entries r2 positive table
  have hcs := clear_eval (data rr positive tail key.reverse
    (Squarefree.Program.lookupResult (entries.lookup key)) table) 0
  simp only [cleared_scan] at hcs
  have hcq := clear_eval (data (readRegs rr 0 1 none) positive [] key.reverse
    (Squarefree.Program.lookupResult (entries.lookup key)) table) 2
  simp only [cleared_query] at hcq
  refine ⟨1 + ((7*table.length+5) + (n + ((2*tail.length+3) + (2*key.reverse.length+3)))),
    ?_,readRegs (readRegs rr 0 1 none) 0 1 none,?_,?_⟩
  · dsimp [literalFetchBudget,table] at *
    simp only [List.length_reverse] at *
    omega
  · have hrun := hp.seq (hc.seq (hl.seq (hcs.seq hcq)))
    simp [data, extend, storage] at hrun
    simpa [literalFetch, table, data, extend, recordState, storage, readRegs] using hrun
  · simpa [readRegs] using hflag

def literalFetchProgram := compiled literalFetch 2 5

theorem literalFetch_runs (regs : Fin 5 → Bool) (old positive : Bool)
    (key : List Bool) (entries : List (List Bool × List Bool)) :
    ∃ regs', RunsIn literalFetchProgram (literalFetchBudget key entries+1)
      ((data regs old [] (key ++ [positive]).reverse []
        (Squarefree.Program.lookupRecords entries)).withPC (some literalFetchProgram.entry))
      ((data regs' positive [] [] (Squarefree.Program.lookupResult (entries.lookup key))
        (Squarefree.Program.lookupRecords entries)).withPC none) ∧
      regs' 4 = (entries.lookup key).isSome := by
  obtain ⟨n,hn,rr,he,hf⟩ := literalFetch_eval regs old positive key entries
  exact ⟨rr,⟨n+1,by omega,compiled_halt_trace he 2 5⟩,hf⟩

end SubexponentialSAT.SqrtLog.HashCircuitProgram

end OAI.Algorithms
