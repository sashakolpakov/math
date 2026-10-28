import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadScatterProgramInit
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadScatterProgramSemantics
import OAI.Algorithms.SubexponentialSAT.WorkspaceCleanupProgram

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HeadScatterProgram
open SubexponentialSAT BitProgram StructuredCalls

def finishWidth : Code := WorkspaceCleanupProgram.command 0 1 [2,5]

def command : Code := .seq initCommand (.seq scanCommand finishWidth)
abbrev program : Program 8 13 (size command+1) := compiled command 10 0

def result (regs : Fin 8 → Bool) (js : List ℕ) (bits : List Bool) (n : ℕ) : Data :=
  ⟨regs, ![mask n js bits,[],[],[],[],[],[],[],[],[],indices js,bits,unary n]⟩

def totalCost (n : ℕ) (js : List ℕ) (bits : List Bool) : ℕ :=
  initCost js bits n+scanCost js+12

theorem command_eval (regs : Fin 8 → Bool) (n : ℕ) (js : List ℕ) (bits : List Bool)
    (hlen : js.length=bits.length) (hb : ∀ j ∈ js,j < n) :
    ∃ rf, Eval command (totalCost n js bits-1) (input regs js bits n) (result rf js bits n) := by
  obtain ⟨ra,ha⟩ := initCommand_eval regs js bits n
  obtain ⟨rb,hb'⟩ := scanCommand_eval ra (savedInputs js bits n) js bits
    (List.replicate n false) hlen (by simpa using hb)
  let b := state rb (savedInputs js bits n) [] [] (mask n js bits)
  let rf := readRegs rb 0 1 none
  have hf : Eval finishWidth 10 b (result rf js bits n) := by
    have h := WorkspaceCleanupProgram.command_eval (0 : Fin 8) 1
      ([2,5] : List (Fin 13)) (by decide) b
    convert h using 1 <;>
      simp [finishWidth,WorkspaceCleanupProgram.cost,b,state,indices,
        ProgramEncoding.encodeRecords,Encoding.encodeList,result,rf,savedInputs]
    apply congrArg (StructuredProgram.State.mk _)
    funext i; fin_cases i <;> rfl
  refine ⟨rf, ?_⟩
  have he := ha.seq (hb'.seq hf)
  convert he using 1 <;> simp [command,totalCost] ; omega

theorem indices_length_bound (n : ℕ) (js : List ℕ) (hb : ∀ j ∈ js,j < n) :
    (indices js).length ≤ js.length*(2*n+2)+1 := by
  induction js with
  | nil => simp [indices,ProgramEncoding.encodeRecords,Encoding.encodeList]
  | cons j js ih =>
      have hj := hb j (by simp)
      have ht := ih (by intro k hk; exact hb k (by simp [hk]))
      simp only [indices,List.map_cons,ProgramEncoding.encodeRecords,Encoding.encodeList,
        List.length_cons,List.length_append,Encoding.length_frame, id_eq, unary,List.length_replicate]
      change 2*j+1+(indices js).length+1 ≤ (js.length+1)*(2*n+2)+1
      nlinarith

theorem totalCost_polynomial (n : ℕ) (js : List ℕ) (bits : List Bool)
    (hlen : js.length=bits.length) (hb : ∀ j ∈ js,j < n) :
    totalCost n js bits ≤ 100*(n+1)*(js.length+1) := by
  have hi := indices_length_bound n js hb
  have hs := scanCost_bound n js hb
  unfold totalCost initCost
  rw [← hlen]
  nlinarith

theorem program_runsIn (regs : Fin 8 → Bool) (n : ℕ) (js : List ℕ) (bits : List Bool)
    (hlen : js.length=bits.length) (hb : ∀ j ∈ js,j < n) :
    ∃ rf, RunsIn program (100*(n+1)*(js.length+1))
      ((input regs js bits n).withPC (some program.entry))
      ((result rf js bits n).withPC none) := by
  obtain ⟨rf,he⟩ := command_eval regs n js bits hlen hb
  refine ⟨rf,totalCost n js bits-1+1,?_,compiled_halt_trace he 10 0⟩
  have hpos : 1 ≤ totalCost n js bits := by unfold totalCost; omega
  rw [Nat.sub_add_cancel hpos]
  exact totalCost_polynomial n js bits hlen hb

theorem program_primitive (regs : Fin 8 → Bool) (n : ℕ) (js : List ℕ) (bits : List Bool)
    (hlen : js.length=bits.length) (hb : ∀ j ∈ js,j < n) :
    ∃ rf, Computation.RunsIn (primitive program).step
      (primitiveOverhead program*(100*(n+1)*(js.length+1)))
      (primitiveCfg program ((input regs js bits n).withPC (some program.entry)))
      (primitiveCfg program ((result rf js bits n).withPC none)) := by
  obtain ⟨rf,he⟩ := program_runsIn regs n js bits hlen hb
  exact ⟨rf,primitive_execution program he⟩

theorem result_inputs (regs : Fin 8 → Bool) (n : ℕ) (js : List ℕ) (bits : List Bool) :
    (result regs js bits n).stacks 10 = indices js ∧
    (result regs js bits n).stacks 11 = bits ∧
    (result regs js bits n).stacks 12 = unary n := by
  exact ⟨rfl,rfl,rfl⟩

theorem result_clean (regs : Fin 8 → Bool) (n : ℕ) (js : List ℕ) (bits : List Bool)
    (i : Fin 13) (hi : i ∈ ([1,2,3,4,5,6,7,8,9] : List (Fin 13))) :
    (result regs js bits n).stacks i=[] := by
  fin_cases i <;> simp_all [result]

end SubexponentialSAT.SqrtLog.HeadScatterProgram

end OAI.Algorithms
