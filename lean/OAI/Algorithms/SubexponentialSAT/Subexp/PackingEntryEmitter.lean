import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport

namespace OAI.Algorithms

/-!
# Fixed emission of one covered packing vertex

The three accumulators are real runtime stacks. Storage receives one reversed
outer record; the two lookup streams receive raw pairs of framed words.
All payloads and counters are data, and every frame is built by fixed programs.
-/
namespace SubexponentialSAT.Subexp.PackingEntryEmitter

open BitProgram StructuredCalls MatrixProgramSupport

abbrev Data := StructuredProgram.State 8 10
abbrev Code := Cmd 8 10

private def workState (regs : Fin 8 → Bool)
    (vertex typeBytes block address storage metadata addresses scratch temp frame : List Bool) : Data :=
  ⟨regs, ![vertex,typeBytes,block,address,storage,metadata,addresses,scratch,temp,frame]⟩

/-- Persistent ports 0--6; work ports 7--9 start and finish empty. -/
def state (regs : Fin 8 → Bool)
    (vertex typeBytes block address storage metadata addresses : List Bool) : Data :=
  workState regs vertex typeBytes block address storage metadata addresses [] [] []

def metadataPayload (block typeBytes : List Bool) : List Bool :=
  true :: (Encoding.frame block ++ Encoding.frame typeBytes)

def storageOutput (vertex storage : List Bool) : List Bool :=
  (true :: Encoding.frame vertex).reverse ++ storage

def metadataOutput (vertex typeBytes block metadata : List Bool) : List Bool :=
  Encoding.frame vertex ++ (Encoding.frame (metadataPayload block typeBytes) ++ metadata)

def addressOutput (vertex address addresses : List Bool) : List Bool :=
  Encoding.frame vertex ++ (Encoding.frame address ++ addresses)

private def sequence (commands : List Code) : Code :=
  commands.foldr Cmd.seq (.base .skip)

def command : Code := sequence [
  MatrixProgramSupport.copy 0 8 7,
  emitFrame 8 9 7 (by decide),
  TupleProgram.pushConst 9 0 true,
  transfer 9 4,
  emitFrame 1 8 7 (by decide),
  MatrixProgramSupport.copy 2 9 7,
  emitFrame 9 8 7 (by decide),
  TupleProgram.pushConst 8 0 true,
  emitFrame 8 5 7 (by decide),
  MatrixProgramSupport.copy 0 9 7,
  emitFrame 9 5 7 (by decide),
  MatrixProgramSupport.copy 3 8 7,
  emitFrame 8 6 7 (by decide),
  emitFrame 0 6 7 (by decide),
  TupleProgram.pushConst 3 0 true]

abbrev program : Program 8 10 (size command+1) := compiled command 0 4

/-- Exact structured instruction count, independent of accumulator lengths. -/
def commandCost (vertex typeBytes block address : List Bool) : ℕ :=
  44*vertex.length + 24*typeBytes.length + 31*block.length + 15*address.length + 115

abbrev emitterCost := commandCost

theorem command_eval_exact
    (vertex typeBytes block address storage metadata addresses : List Bool)
    (regs : Fin 8 → Bool) :
    ∃ rf, Eval command (commandCost vertex typeBytes block address)
      (state regs vertex typeBytes block address storage metadata addresses)
      (state rf [] [] block (true::address) (storageOutput vertex storage)
        (metadataOutput vertex typeBytes block metadata)
        (addressOutput vertex address addresses)) := by
  let a0 := workState regs vertex typeBytes block address storage metadata addresses [] [] []
  obtain ⟨d1,h1,s1⟩ := copy_eval (0 : Fin 10) 8 7 (by decide) (by decide) (by decide) a0 rfl
  let a1 := workState d1.regs
    vertex typeBytes block address storage metadata addresses [] vertex []
  have e1 : d1 = a1 := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    rw [s1]
    funext j
    fin_cases j <;> simp [a0,workState,StackRoutines.copyStacks]
  rw [e1] at h1
  obtain ⟨d2,h2,s2⟩ := emitFrame_eval (8 : Fin 10) 9 7 (by decide) (by decide) (by decide) a1 rfl
  let a2 := workState d2.regs
    vertex typeBytes block address storage metadata addresses [] [] (Encoding.frame vertex)
  have e2 : d2 = a2 := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    rw [s2]
    funext j
    fin_cases j <;> simp [a1,workState]
  rw [e2] at h2
  have h3 := TupleProgram.pushConst_eval (9 : Fin 10) (0 : Fin 8) true a2
  let a3 := workState (Function.update a2.regs 0 true)
    vertex typeBytes block address storage metadata addresses [] [] (true :: (Encoding.frame vertex))
  have e3 : TupleProgram.pushedState 9 0 true a2 = a3 := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext j
    fin_cases j <;> simp [a2,workState]
  rw [e3] at h3
  obtain ⟨d4,h4,s4⟩ := transfer_eval (9 : Fin 10) 4 (by decide) a3
  let a4 := workState d4.regs
    vertex typeBytes block address ((true :: (Encoding.frame vertex)).reverse ++ storage) metadata addresses [] [] []
  have e4 : d4 = a4 := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    rw [s4]
    funext j
    fin_cases j <;> simp [a3,workState,StackRoutines.transferStacks]
  rw [e4] at h4
  obtain ⟨d5,h5,s5⟩ := emitFrame_eval (1 : Fin 10) 8 7 (by decide) (by decide) (by decide) a4 rfl
  let a5 := workState d5.regs
    vertex [] block address ((true :: (Encoding.frame vertex)).reverse ++ storage) metadata addresses [] (Encoding.frame typeBytes) []
  have e5 : d5 = a5 := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    rw [s5]
    funext j
    fin_cases j <;> simp [a4,workState]
  rw [e5] at h5
  obtain ⟨d6,h6,s6⟩ := copy_eval (2 : Fin 10) 9 7 (by decide) (by decide) (by decide) a5 rfl
  let a6 := workState d6.regs
    vertex [] block address ((true :: (Encoding.frame vertex)).reverse ++ storage) metadata addresses [] (Encoding.frame typeBytes) block
  have e6 : d6 = a6 := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    rw [s6]
    funext j
    fin_cases j <;> simp [a5,workState,StackRoutines.copyStacks]
  rw [e6] at h6
  obtain ⟨d7,h7,s7⟩ := emitFrame_eval (9 : Fin 10) 8 7 (by decide) (by decide) (by decide) a6 rfl
  let a7 := workState d7.regs
    vertex [] block address ((true :: (Encoding.frame vertex)).reverse ++ storage) metadata addresses [] (Encoding.frame block ++ (Encoding.frame typeBytes)) []
  have e7 : d7 = a7 := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    rw [s7]
    funext j
    fin_cases j <;> simp [a6,workState]
  rw [e7] at h7
  have h8 := TupleProgram.pushConst_eval (8 : Fin 10) (0 : Fin 8) true a7
  let a8 := workState (Function.update a7.regs 0 true)
    vertex [] block address ((true :: (Encoding.frame vertex)).reverse ++ storage) metadata addresses [] (true :: (Encoding.frame block ++ (Encoding.frame typeBytes))) []
  have e8 : TupleProgram.pushedState 8 0 true a7 = a8 := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext j
    fin_cases j <;> simp [a7,workState]
  rw [e8] at h8
  obtain ⟨d9,h9,s9⟩ := emitFrame_eval (8 : Fin 10) 5 7 (by decide) (by decide) (by decide) a8 rfl
  let a9 := workState d9.regs
    vertex [] block address ((true :: (Encoding.frame vertex)).reverse ++ storage) (Encoding.frame (true :: (Encoding.frame block ++ (Encoding.frame typeBytes))) ++ metadata) addresses [] [] []
  have e9 : d9 = a9 := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    rw [s9]
    funext j
    fin_cases j <;> simp [a8,workState]
  rw [e9] at h9
  obtain ⟨d10,h10,s10⟩ := copy_eval (0 : Fin 10) 9 7 (by decide) (by decide) (by decide) a9 rfl
  let a10 := workState d10.regs
    vertex [] block address ((true :: (Encoding.frame vertex)).reverse ++ storage) (Encoding.frame (true :: (Encoding.frame block ++ (Encoding.frame typeBytes))) ++ metadata) addresses [] [] vertex
  have e10 : d10 = a10 := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    rw [s10]
    funext j
    fin_cases j <;> simp [a9,workState,StackRoutines.copyStacks]
  rw [e10] at h10
  obtain ⟨d11,h11,s11⟩ := emitFrame_eval (9 : Fin 10) 5 7 (by decide) (by decide) (by decide) a10 rfl
  let a11 := workState d11.regs
    vertex [] block address ((true :: (Encoding.frame vertex)).reverse ++ storage) (Encoding.frame vertex ++ (Encoding.frame (true :: (Encoding.frame block ++ (Encoding.frame typeBytes))) ++ metadata)) addresses [] [] []
  have e11 : d11 = a11 := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    rw [s11]
    funext j
    fin_cases j <;> simp [a10,workState]
  rw [e11] at h11
  obtain ⟨d12,h12,s12⟩ := copy_eval (3 : Fin 10) 8 7 (by decide) (by decide) (by decide) a11 rfl
  let a12 := workState d12.regs
    vertex [] block address ((true :: (Encoding.frame vertex)).reverse ++ storage) (Encoding.frame vertex ++ (Encoding.frame (true :: (Encoding.frame block ++ (Encoding.frame typeBytes))) ++ metadata)) addresses [] address []
  have e12 : d12 = a12 := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    rw [s12]
    funext j
    fin_cases j <;> simp [a11,workState,StackRoutines.copyStacks]
  rw [e12] at h12
  obtain ⟨d13,h13,s13⟩ := emitFrame_eval (8 : Fin 10) 6 7 (by decide) (by decide) (by decide) a12 rfl
  let a13 := workState d13.regs
    vertex [] block address ((true :: (Encoding.frame vertex)).reverse ++ storage) (Encoding.frame vertex ++ (Encoding.frame (true :: (Encoding.frame block ++ (Encoding.frame typeBytes))) ++ metadata)) (Encoding.frame address ++ addresses) [] [] []
  have e13 : d13 = a13 := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    rw [s13]
    funext j
    fin_cases j <;> simp [a12,workState]
  rw [e13] at h13
  obtain ⟨d14,h14,s14⟩ := emitFrame_eval (0 : Fin 10) 6 7 (by decide) (by decide) (by decide) a13 rfl
  let a14 := workState d14.regs
    [] [] block address ((true :: (Encoding.frame vertex)).reverse ++ storage) (Encoding.frame vertex ++ (Encoding.frame (true :: (Encoding.frame block ++ (Encoding.frame typeBytes))) ++ metadata)) (Encoding.frame vertex ++ (Encoding.frame address ++ addresses)) [] [] []
  have e14 : d14 = a14 := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    rw [s14]
    funext j
    fin_cases j <;> simp [a13,workState]
  rw [e14] at h14
  have h15 := TupleProgram.pushConst_eval (3 : Fin 10) (0 : Fin 8) true a14
  let a15 := workState (Function.update a14.regs 0 true)
    [] [] block (true :: address) ((true :: (Encoding.frame vertex)).reverse ++ storage) (Encoding.frame vertex ++ (Encoding.frame (true :: (Encoding.frame block ++ (Encoding.frame typeBytes))) ++ metadata)) (Encoding.frame vertex ++ (Encoding.frame address ++ addresses)) [] [] []
  have e15 : TupleProgram.pushedState 3 0 true a14 = a15 := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext j
    fin_cases j <;> simp [a14,workState]
  rw [e15] at h15
  have hrun := h1.seq (h2.seq (h3.seq (h4.seq (h5.seq (h6.seq (h7.seq (h8.seq (h9.seq (h10.seq (h11.seq (h12.seq (h13.seq (h14.seq (h15.seq ((.base (.skip a15)))))))))))))))))
  have hcost : (7*(a0.stacks 0).length+5)+((8*(a1.stacks 8).length+8)+(2+((3*(a3.stacks 9).length+3)+((8*(a4.stacks 1).length+8)+((7*(a5.stacks 2).length+5)+((8*(a6.stacks 9).length+8)+(2+((8*(a8.stacks 8).length+8)+((7*(a9.stacks 0).length+5)+((8*(a10.stacks 9).length+8)+((7*(a11.stacks 3).length+5)+((8*(a12.stacks 8).length+8)+((8*(a13.stacks 0).length+8)+(2+(0))))))))))))))) =
      commandCost vertex typeBytes block address := by
    simp [a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,workState,commandCost,Encoding.length_frame]
    ring
  rw [hcost] at hrun
  exact ⟨a15.regs,hrun⟩

theorem command_eval
    (vertex typeBytes block address storage metadata addresses : List Bool)
    (regs : Fin 8 → Bool) :
    ∃ n ≤ commandCost vertex typeBytes block address, ∃ rf,
      Eval command n (state regs vertex typeBytes block address storage metadata addresses)
        (state rf [] [] block (true::address) (storageOutput vertex storage)
          (metadataOutput vertex typeBytes block metadata)
          (addressOutput vertex address addresses)) := by
  obtain ⟨rf,h⟩ := command_eval_exact vertex typeBytes block address storage metadata addresses regs
  exact ⟨_,le_rfl,rf,h⟩

theorem program_trace
    (vertex typeBytes block address storage metadata addresses : List Bool)
    (regs : Fin 8 → Bool) :
    ∃ rf, Trace program (commandCost vertex typeBytes block address+1)
      ((state regs vertex typeBytes block address storage metadata addresses).withPC (some program.entry))
      ((state rf [] [] block (true::address) (storageOutput vertex storage)
        (metadataOutput vertex typeBytes block metadata)
        (addressOutput vertex address addresses)).withPC none) := by
  obtain ⟨rf,h⟩ := command_eval_exact vertex typeBytes block address storage metadata addresses regs
  exact ⟨rf,compiled_halt_trace h 0 4⟩

theorem program_run
    (vertex typeBytes block address storage metadata addresses : List Bool)
    (regs : Fin 8 → Bool) :
    ∃ rf, RunsIn program (commandCost vertex typeBytes block address+1)
      ((state regs vertex typeBytes block address storage metadata addresses).withPC (some program.entry))
      ((state rf [] [] block (true::address) (storageOutput vertex storage)
        (metadataOutput vertex typeBytes block metadata)
        (addressOutput vertex address addresses)).withPC none) := by
  obtain ⟨rf,h⟩ := program_trace vertex typeBytes block address storage metadata addresses regs
  exact ⟨rf,_,le_rfl,h⟩

theorem program_primitive
    (vertex typeBytes block address storage metadata addresses : List Bool)
    (regs : Fin 8 → Bool) :
    ∃ rf, Computation.RunsIn (BitProgram.primitive program).step
      (BitProgram.primitiveOverhead program * (commandCost vertex typeBytes block address+1))
      (BitProgram.primitiveCfg program
        ((state regs vertex typeBytes block address storage metadata addresses).withPC (some program.entry)))
      (BitProgram.primitiveCfg program
        ((state rf [] [] block (true::address) (storageOutput vertex storage)
          (metadataOutput vertex typeBytes block metadata)
          (addressOutput vertex address addresses)).withPC none)) := by
  obtain ⟨rf,h⟩ := program_run vertex typeBytes block address storage metadata addresses regs
  exact ⟨rf,BitProgram.primitive_execution program h⟩

@[simp] theorem metadataPayload_length (block typeBytes : List Bool) :
    (metadataPayload block typeBytes).length = 2*block.length+2*typeBytes.length+3 := by
  simp [metadataPayload,Encoding.length_frame]
  omega

@[simp] theorem storageOutput_length (vertex storage : List Bool) :
    (storageOutput vertex storage).length = 2*vertex.length+2+storage.length := by
  simp [storageOutput,Encoding.length_frame]
  omega

@[simp] theorem metadataOutput_length (vertex typeBytes block metadata : List Bool) :
    (metadataOutput vertex typeBytes block metadata).length =
      2*vertex.length+4*block.length+4*typeBytes.length+8+metadata.length := by
  simp [metadataOutput,Encoding.length_frame]
  omega

@[simp] theorem addressOutput_length (vertex address addresses : List Bool) :
    (addressOutput vertex address addresses).length =
      2*vertex.length+2*address.length+2+addresses.length := by
  simp [addressOutput,Encoding.length_frame]
  omega

theorem unary_command_eval (vertex block address : ℕ)
    (typeBytes storage metadata addresses : List Bool) (regs : Fin 8 → Bool) :
    ∃ rf, Eval command
      (44*vertex+24*typeBytes.length+31*block+15*address+115)
      (state regs (List.replicate vertex true) typeBytes (List.replicate block true)
        (List.replicate address true) storage metadata addresses)
      (state rf [] [] (List.replicate block true) (List.replicate (address+1) true)
        (storageOutput (List.replicate vertex true) storage)
        (metadataOutput (List.replicate vertex true) typeBytes (List.replicate block true) metadata)
        (addressOutput (List.replicate vertex true) (List.replicate address true) addresses)) := by
  simpa only [commandCost,List.length_replicate,List.replicate_succ] using
    command_eval_exact (List.replicate vertex true) typeBytes (List.replicate block true)
      (List.replicate address true) storage metadata addresses regs

end SubexponentialSAT.Subexp.PackingEntryEmitter


end OAI.Algorithms
