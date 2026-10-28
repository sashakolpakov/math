import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpScanPrimitives

namespace OAI.Algorithms

/-! Explicit order conversion between the reverse high-incidence mask and the
forward low-variable mask consumed by head-identifier selection. -/
namespace SubexponentialSAT.SqrtLog.HeadIdentifierProgram.LowMask
open SubexponentialSAT BitProgram StructuredCalls

abbrev Data := State 2 2

def state (regs : Fin 2 → Bool) (xs out : List Bool) : Data := ⟨regs,![xs,out]⟩

@[simp] private theorem stacks_update0 (a b c : List Bool) :
    Function.update ![a,b] (0 : Fin 2) c = ![c,b] := by
  funext i; fin_cases i <;> rfl
@[simp] private theorem stacks_update1 (a b c : List Bool) :
    Function.update ![a,b] (1 : Fin 2) c = ![a,c] := by
  funext i; fin_cases i <;> rfl

abbrev program : Program 2 2 7 where
  inputStack := 0
  outputStack := 1
  entry := 0
  code := ![.pop 0 0 1 1,.branch 1 2 6,.branch 0 3 4,
    .set 0 false 5,.set 0 true 5,.push 1 0 0,.halt]

def stepRegs (regs : Fin 2 → Bool) (b : Bool) : Fin 2 → Bool :=
  Function.update (readRegs regs 0 1 (some b)) 0 (!b)

theorem cycle (regs : Fin 2 → Bool) (b : Bool) (xs out : List Bool) :
    Trace program 5 ((state regs (b::xs) out).withPC (some 0))
      ((state (stepRegs regs b) xs ((!b)::out)).withPC (some 0)) := by
  refine .cons (b := (state (readRegs regs 0 1 (some b)) xs out).withPC (some 1)) ?_ ?_
  · simp [state,StructuredProgram.State.withPC,step,execInstr,readRegs]
  · refine .cons (b := (state (readRegs regs 0 1 (some b)) xs out).withPC (some 2)) ?_ ?_
    · simp [state,StructuredProgram.State.withPC,step,execInstr,readRegs]
    · cases b
      · refine .cons (b := (state (readRegs regs 0 1 (some false)) xs out).withPC (some 4)) ?_ ?_
        · simp [state,StructuredProgram.State.withPC,step,execInstr,readRegs]
        · refine .cons (b := (state (stepRegs regs false) xs out).withPC (some 5)) ?_ ?_
          · simp [state,stepRegs,StructuredProgram.State.withPC,step,execInstr]
          · refine .cons ?_ (.refl _)
            simp [state,stepRegs,StructuredProgram.State.withPC,step,execInstr,readRegs]
      · refine .cons (b := (state (readRegs regs 0 1 (some true)) xs out).withPC (some 3)) ?_ ?_
        · simp [state,StructuredProgram.State.withPC,step,execInstr,readRegs]
        · refine .cons (b := (state (stepRegs regs true) xs out).withPC (some 5)) ?_ ?_
          · simp [state,stepRegs,StructuredProgram.State.withPC,step,execInstr]
          · refine .cons ?_ (.refl _)
            simp [state,stepRegs,StructuredProgram.State.withPC,step,execInstr,readRegs]

theorem finish (regs : Fin 2 → Bool) (out : List Bool) :
    Trace program 3 ((state regs [] out).withPC (some 0))
      ((state (readRegs regs 0 1 none) [] out).withPC none) := by
  refine .cons (b := (state (readRegs regs 0 1 none) [] out).withPC (some 1)) ?_ ?_
  · simp [state,StructuredProgram.State.withPC,step,execInstr,readRegs]
  · refine .cons (b := (state (readRegs regs 0 1 none) [] out).withPC (some 6)) ?_ ?_
    · simp [state,StructuredProgram.State.withPC,step,execInstr,readRegs]
    · refine .cons ?_ (.refl _)
      simp [state,StructuredProgram.State.withPC,step,execInstr]

theorem trace (regs : Fin 2 → Bool) (xs out : List Bool) :
    ∃ rf, Trace program (5*xs.length+3) ((state regs xs out).withPC (some program.entry))
      ((state rf [] ((xs.map (fun b => !b)).reverse++out)).withPC none) := by
  induction xs generalizing regs out with
  | nil => exact ⟨_,finish regs out⟩
  | cons b xs ih =>
      obtain ⟨rf,ht⟩ := ih (stepRegs regs b) ((!b)::out)
      have he := (cycle regs b xs out).trans ht
      refine ⟨rf,?_⟩
      convert he using 1 <;> simp [List.reverse_cons,List.append_assoc] ; omega

/-- Consumes a reverse original-order high mask and emits the forward low
mask. Original coordinate j now carries exactly the complement of high[j]. -/
theorem program_runsIn (regs : Fin 2 → Bool) (high : List Bool) :
    ∃ rf, RunsIn program (5*high.length+3)
      ((state regs high.reverse []).withPC (some program.entry))
      ((state rf [] (high.map (fun b => !b))).withPC none) := by
  obtain ⟨rf,ht⟩ := trace regs high.reverse []
  refine ⟨rf,5*high.length+3,le_rfl,?_⟩
  simpa only [List.length_reverse,List.map_reverse,List.reverse_reverse,List.append_nil] using ht

theorem program_primitive (regs : Fin 2 → Bool) (high : List Bool) :
    ∃ rf, Computation.RunsIn (primitive program).step
      (primitiveOverhead program*(5*high.length+3))
      (primitiveCfg program ((state regs high.reverse []).withPC (some program.entry)))
      (primitiveCfg program ((state rf [] (high.map (fun b => !b))).withPC none)) := by
  obtain ⟨rf,he⟩ := program_runsIn regs high
  exact ⟨rf,primitive_execution program he⟩

end SubexponentialSAT.SqrtLog.HeadIdentifierProgram.LowMask

end OAI.Algorithms
