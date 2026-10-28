import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketTupleProgramTable
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames

namespace OAI.Algorithms

/-! One fixed, paid append of the attained buckets of the current head to the
current tuple table. The current head table is data, and may differ each call. -/
namespace SubexponentialSAT.SqrtLog.BucketTupleProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
namespace Expand

abbrev Data := State 10 16
abbrev Code := Cmd 10 16
abbrev Records := List (List Bool)

def state (regs : Fin 10 → Bool) (rows : Records)
    (mask context table alphabet : List Bool) : Data :=
  ⟨regs, ![ProgramEncoding.encodeRecords rows,alphabet,[],[],[],[false],[],[],[],
    table,mask,context,[],[],[],[]]⟩

def tableRegs : Fin 8 → Fin 10 := Fin.castAdd 2
def tablePorts : Fin 8 → Fin 16 := ![9,12,13,14,10,11,1,15]
theorem tablePorts_injective : Function.Injective tablePorts := by decide

def tableCall : Code := .call (ProgramLinking.liftProgram Table.program tableRegs tablePorts)
def productPorts : Fin 9 → Fin 16 := Fin.castAdd 7

def productCall : Code :=
  liftCommand SubexponentialSAT.Subexp.TupleProgram.expandStep 0 0 id productPorts

def command : Code := .seq (SubexponentialSAT.Subexp.TupleProgram.pushConst 1 0 false)
  (.seq tableCall (.seq productCall (WorkspaceCleanupProgram.command 0 1 [1])))

def alphabet (mask context : List Bool) (bs : List Table.Bucket) : Records :=
  (bs.map (Table.alphabetWord mask context)).reverse

def nextRows (rows : Records) (mask context : List Bool) (bs : List Table.Bucket) : Records :=
  SubexponentialSAT.Subexp.TupleProgram.cartesianOutput rows (alphabet mask context bs)

def cost (rows : Records) (mask context : List Bool) (bs : List Table.Bucket) : ℕ :=
  Table.cost mask context bs + SubexponentialSAT.Subexp.TupleProgram.stepCost rows (alphabet mask context bs) +
  2*(ProgramEncoding.encodeRecords (alphabet mask context bs)).length + 8

theorem tableCall_eval (regs : Fin 10 → Bool) (rows : Records)
    (mask context : List Bool) (bs : List Table.Bucket) :
    ∃ t ≤ Table.cost mask context bs+1, ∃ rf,
      Eval tableCall t (state regs rows mask context (Table.tableBits bs) [false])
        (state rf rows mask context [] (ProgramEncoding.encodeRecords (alphabet mask context bs))) := by
  let d := state regs rows mask context (Table.tableBits bs) [false]
  have hd : projectState tableRegs tablePorts d =
      Table.state (regs ∘ tableRegs) mask context (Table.tableBits bs) [false] := by
    apply congrArg (StructuredProgram.State.mk (regs ∘ tableRegs))
    funext i; fin_cases i <;> rfl
  obtain ⟨rf,t,ht,he⟩ := Table.program_runsIn (regs ∘ tableRegs) mask context bs
  rw [←hd] at he
  have hc := eval_call_from_state Table.program tableRegs tablePorts d
    (Fin.castAdd_injective _ _) tablePorts_injective he
  let b := Table.state rf mask context [] (ProgramEncoding.encodeRecords (alphabet mask context bs))
  let e := embedState tableRegs tablePorts d b
  have hend : e = state e.regs rows mask context [] (ProgramEncoding.encodeRecords (alphabet mask context bs)) := by
    apply embedState_eq_of_ports tableRegs tablePorts d _ b
      (Fin.castAdd_injective _ _) tablePorts_injective
    · intro i; exact embedState_register tableRegs tablePorts d b (Fin.castAdd_injective _ _) i
    · intro i hi; exact embedState_register_frame tableRegs tablePorts d b i hi
    · intro i; fin_cases i <;> rfl
    · intro i hi; fin_cases i <;> simp_all [Fin.exists_fin_succ,tablePorts,state,d]
  change Eval tableCall t d e at hc
  rw [hend] at hc
  exact ⟨t,ht,e.regs,hc⟩

theorem productCall_eval (regs : Fin 10 → Bool) (rows al : Records)
    (mask context : List Bool) :
    ∃ t ≤ SubexponentialSAT.Subexp.TupleProgram.stepCost rows al+1, ∃ rf,
      Eval productCall t (state regs rows mask context [] (ProgramEncoding.encodeRecords al))
        (state rf (SubexponentialSAT.Subexp.TupleProgram.cartesianOutput rows al) mask context []
          (ProgramEncoding.encodeRecords al)) := by
  let d := state regs rows mask context [] (ProgramEncoding.encodeRecords al)
  have hd : SubexponentialSAT.Subexp.TupleProgram.Ready al rows [] (regs 9)
      (projectState id productPorts d) := by
    simp [SubexponentialSAT.Subexp.TupleProgram.Ready,SubexponentialSAT.Subexp.TupleProgram.outerInvariant,
      projectState,productPorts,d,state]
  obtain ⟨t,b,ht,hb,he⟩ := SubexponentialSAT.Subexp.TupleProgram.expandStep_eval al rows [] (regs 9)
    (projectState id productPorts d) hd
  have hc := eval_liftCommand_from_state SubexponentialSAT.Subexp.TupleProgram.expandStep 0 0 id productPorts d
    Function.injective_id (Fin.castAdd_injective _ _) he
  let e := embedState id productPorts d b
  have hend : e = state e.regs (SubexponentialSAT.Subexp.TupleProgram.cartesianOutput rows al) mask context []
      (ProgramEncoding.encodeRecords al) := by
    rcases hb with ⟨⟨h1,h3,h4,h6,h7,h8,h9⟩,h0,h2,h5⟩
    apply embedState_eq_of_ports id productPorts d _ b Function.injective_id (Fin.castAdd_injective _ _)
    · intro i; exact embedState_register id productPorts d b Function.injective_id i
    · intro i hi; exact (hi ⟨i,rfl⟩).elim
    · intro i; fin_cases i <;> simp_all [productPorts,state]
    · intro i hi; fin_cases i <;> simp_all [Fin.exists_fin_succ,productPorts,state,d]
  change Eval productCall (t+1) d e at hc
  rw [hend] at hc
  exact ⟨t+1,by omega,e.regs,hc⟩

theorem command_eval (regs : Fin 10 → Bool) (rows : Records)
    (mask context : List Bool) (bs : List Table.Bucket) :
    ∃ t ≤ cost rows mask context bs, ∃ rf,
      Eval command t (state regs rows mask context (Table.tableBits bs) [])
        (state rf (nextRows rows mask context bs) mask context [] []) := by
  let d := state regs rows mask context (Table.tableBits bs) []
  let a := SubexponentialSAT.Subexp.TupleProgram.pushedState (1 : Fin 16) (0 : Fin 10) false d
  have ha := SubexponentialSAT.Subexp.TupleProgram.pushConst_eval (1 : Fin 16) (0 : Fin 10) false d
  have hea : a = state a.regs rows mask context (Table.tableBits bs) [false] := by
    apply congrArg (StructuredProgram.State.mk a.regs)
    funext i; fin_cases i <;> rfl
  obtain ⟨t,ht,rb,hb⟩ := tableCall_eval a.regs rows mask context bs
  rw [←hea] at hb
  obtain ⟨u,hu,rc,hc⟩ := productCall_eval rb rows (alphabet mask context bs) mask context
  let c := state rc (nextRows rows mask context bs) mask context []
    (ProgramEncoding.encodeRecords (alphabet mask context bs))
  let f := WorkspaceCleanupProgram.finish (0 : Fin 10) 1 ([1] : List (Fin 16)) c
  have hf := WorkspaceCleanupProgram.command_eval (0 : Fin 10) 1
    ([1] : List (Fin 16)) (by decide) c
  have hef : f = state f.regs (nextRows rows mask context bs) mask context [] [] := by
    apply congrArg (StructuredProgram.State.mk f.regs)
    funext i; fin_cases i <;> simp [c,state,BankRoutines.clearBankStacks]
  change Eval (WorkspaceCleanupProgram.command (0 : Fin 10) 1 ([1] : List (Fin 16)))
    (WorkspaceCleanupProgram.cost ([1] : List (Fin 16)) c) c f at hf
  rw [hef] at hf
  refine ⟨_,?_,f.regs,ha.seq (hb.seq (hc.seq hf))⟩
  simp [cost,WorkspaceCleanupProgram.cost,c,state]
  omega

theorem nextRows_length (rows : Records) (mask context : List Bool) (bs : List Table.Bucket) :
    (nextRows rows mask context bs).length = rows.length*bs.length := by
  simp [nextRows,alphabet,SubexponentialSAT.Subexp.TupleProgram.cartesianOutput_length]

def program := compiled command 9 0

theorem program_runsIn (regs : Fin 10 → Bool) (rows : Records)
    (mask context : List Bool) (bs : List Table.Bucket) :
    ∃ rf, RunsIn program (cost rows mask context bs+1)
      ((state regs rows mask context (Table.tableBits bs) []).withPC (some program.entry))
      ((state rf (nextRows rows mask context bs) mask context [] []).withPC none) := by
  obtain ⟨t,ht,rf,he⟩ := command_eval regs rows mask context bs
  exact ⟨rf,t+1,by omega,compiled_halt_trace he 9 0⟩

end Expand
end SubexponentialSAT.SqrtLog.BucketTupleProgram

end OAI.Algorithms
