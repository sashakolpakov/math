import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramMetadata

namespace OAI.Algorithms

/-! Two actual metadata lookups with disjoint returned records. Both query
indices and the computed metadata master are preserved. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.LookupPair

open SubexponentialSAT.Subexp SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open GlobalBasisMetadata

abbrev Data := State 6 16

def rowRegisters : Fin 5 → Fin 6 := Fin.castAdd 1
def colRegisters : Fin 5 → Fin 6 := ![0,1,2,3,5]
def rowPorts : Fin 12 → Fin 16 := ![0,1,3,4,5,9,10,11,12,13,14,15]
def colPorts : Fin 12 → Fin 16 := ![0,2,6,7,8,9,10,11,12,13,14,15]

def state (regs : Fin 6 → Bool) (master row col : List Bool)
    (rb rt rr cb ct cr : List Bool) : Data :=
  ⟨regs,![master,row,col,rb,rt,rr,cb,ct,cr,[],[],[],[],[],[],[]]⟩

abbrev rowCall : Cmd 6 16 := .call (ProgramLinking.liftProgram GlobalBasisMetadata.program
  rowRegisters rowPorts)
abbrev colCall : Cmd 6 16 := .call (ProgramLinking.liftProgram GlobalBasisMetadata.program
  colRegisters colPorts)
abbrev command : Cmd 6 16 := .seq rowCall colCall
def program := compiled command 0 3

private theorem rowRegisters_inj : Function.Injective rowRegisters := Fin.castAdd_injective _ _
private theorem colRegisters_inj : Function.Injective colRegisters := by decide
private theorem rowPorts_inj : Function.Injective rowPorts := by decide
private theorem colPorts_inj : Function.Injective colPorts := by decide

private theorem row_embed (regs : Fin 6 → Bool) (master row col : List Bool) (m : Metadata) :
    embedState rowRegisters rowPorts (state regs master row col [] [] [] [] [] [])
      (GlobalBasisMetadata.outputState master row m) =
      state ![false,false,false,false,m.coveredFlag,regs 5]
        master row col m.block m.typeCode m.rank [] [] [] := by
  apply embedState_eq_of_ports _ _ _ _ _ rowRegisters_inj rowPorts_inj
  · intro j; fin_cases j <;> simp [state,GlobalBasisMetadata.outputState,rowRegisters]
  · intro j hj
    have h : j = 5 := by
      fin_cases j <;> simp_all [rowRegisters,Fin.exists_fin_succ]
    subst j; rfl
  · intro j; fin_cases j <;> simp [state,GlobalBasisMetadata.outputState,rowPorts]
  · intro j hj
    fin_cases j <;> simp_all [state,rowPorts,Fin.exists_fin_succ]

private theorem col_embed (regs : Fin 6 → Bool) (master row col : List Bool)
    (rb rt rr : List Bool) (m : Metadata) :
    embedState colRegisters colPorts (state regs master row col rb rt rr [] [] [])
      (GlobalBasisMetadata.outputState master col m) =
      state ![false,false,false,false,regs 4,m.coveredFlag]
        master row col rb rt rr m.block m.typeCode m.rank := by
  apply embedState_eq_of_ports _ _ _ _ _ colRegisters_inj colPorts_inj
  · intro j; fin_cases j <;> simp [state,GlobalBasisMetadata.outputState,colRegisters]
  · intro j hj
    fin_cases j <;> simp_all [state,colRegisters,Fin.exists_fin_succ]
  · intro j; fin_cases j <;> simp [state,GlobalBasisMetadata.outputState,colPorts]
  · intro j hj
    fin_cases j <;> simp_all [state,colPorts,Fin.exists_fin_succ]

/-- The lookup hypotheses identify the actual serialized metadata records.
They are discharged by `PackingMetadata.lookup_eq`, not by a supplied oracle. -/
theorem program_runsIn (records : List (List Bool × List Bool)) (row col : List Bool)
    (mr mc : Metadata) (hr : records.lookup row = some mr.encode)
    (hc : records.lookup col = some mc.encode) (regs : Fin 6 → Bool) :
    RunsIn program (400*(volume records row)^2+400*(volume records col)^2+1)
      ((state regs (SelectorProgram.rawRecords records) row col [] [] [] [] [] []).withPC
        (some program.entry))
      ((state ![false,false,false,false,mr.coveredFlag,mc.coveredFlag]
        (SelectorProgram.rawRecords records) row col mr.block mr.typeCode mr.rank
          mc.block mc.typeCode mc.rank).withPC none) := by
  let master := SelectorProgram.rawRecords records
  let a := state regs master row col [] [] [] [] [] []
  obtain ⟨nr,hnr,tr⟩ := GlobalBasisMetadata.program_runsIn records row mr hr
    (regs ∘ rowRegisters)
  have hp : projectState rowRegisters rowPorts a =
      GlobalBasisMetadata.inputState (regs ∘ rowRegisters) master row := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext j
    fin_cases j <;> simp [a,state,rowPorts
]
  rw [← hp] at tr
  have er := eval_call_from_state GlobalBasisMetadata.program rowRegisters rowPorts a
    rowRegisters_inj rowPorts_inj tr
  rw [show a = state regs master row col [] [] [] [] [] [] from rfl,row_embed] at er
  let midregs : Fin 6 → Bool := ![false,false,false,false,mr.coveredFlag,regs 5]
  let b := state midregs master row col mr.block mr.typeCode mr.rank [] [] []
  obtain ⟨nc,hnc,tc⟩ := GlobalBasisMetadata.program_runsIn records col mc hc
    (midregs ∘ colRegisters)
  have hq : projectState colRegisters colPorts b =
      GlobalBasisMetadata.inputState (midregs ∘ colRegisters) master col := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext j
    fin_cases j <;> simp [b,state,colPorts
]
  rw [← hq] at tc
  have ec := eval_call_from_state GlobalBasisMetadata.program colRegisters colPorts b
    colRegisters_inj colPorts_inj tc
  rw [show b = state midregs master row col mr.block mr.typeCode mr.rank [] [] [] from rfl,
    col_embed] at ec
  refine ⟨nr+nc+1,by omega,?_⟩
  exact compiled_halt_trace (er.seq ec) 0 3

end SubexponentialSAT.SqrtLog.LayoutProgram.LookupPair

end OAI.Algorithms
