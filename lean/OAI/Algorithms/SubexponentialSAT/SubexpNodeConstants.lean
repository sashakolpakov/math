import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpConstantPrograms
import OAI.Algorithms.SubexponentialSAT.SubexpScalarLiteralProgram
import OAI.Algorithms.SubexponentialSAT.SubexpBlockAssembly
import OAI.Algorithms.SubexponentialSAT.SubexpNodeCacheSetup

namespace OAI.Algorithms

/-!
# Actual target constants for the node worker

The target setup's flat zero, flat one and scalar minus one are copied to
119--121 by the Main adapter. This module constructs the remaining values
with finite programs: raw polynomial literals on122/123 and a target-width
scalar one on124. Workspace200--216 is temporary and restored by the calls.
-/

namespace SubexponentialSAT.SubexpNodeConstants

open BitProgram StructuredCalls SubexpScanPrimitives

abbrev Data := State 16 256

def unitRegs : Fin 8 → Fin 16 := Fin.castAdd 8
def unitPorts : Fin 3 → Fin 256 := ![124, 215, 216]

theorem unitRegs_injective : Function.Injective unitRegs := Fin.castAdd_injective _ _
theorem unitPorts_injective : Function.Injective unitPorts := by decide

abbrev unitCall : Cmd 16 256 :=
  .call (ProgramLinking.liftProgram (SubexpConstantPrograms.program true) unitRegs unitPorts)

abbrev unitInit : Cmd 16 256 :=
  .seq (.call (StackRoutines.copyProgram 10 124 0 0 1)) unitCall

theorem unit_call_eval (d : Data) (h215 : d.stacks 215 = []) (h216 : d.stacks 216 = [])
    (hwidth : 0 < (d.stacks 124).length) :
    ∃ out : Data, Eval unitCall (7 * (d.stacks 124).length + 9) d out ∧
      out.stacks = Function.update d.stacks 124
        (SubexpLiftRing.fixedBits (d.stacks 124).length 1) := by
  obtain ⟨regs, ht⟩ := SubexpConstantPrograms.run_literal true (d.regs ∘ unitRegs)
    (d.stacks 124) (fun _ => hwidth)
  let before := SubexpConstantPrograms.state (d.regs ∘ unitRegs) (d.stacks 124) []
  let after := SubexpConstantPrograms.state regs
    (SubexpLiftRing.fixedBits (d.stacks 124).length 1) []
  have hin : embedState unitRegs unitPorts d before = d := by
    apply embedState_eq _ _ unitRegs_injective unitPorts_injective
    · intros; rfl
    · intro i
      fin_cases i <;> simp [before, SubexpConstantPrograms.state,
        ModularPrograms.operandStacks, unitPorts, h215, h216]
    · intros; rfl
    · intros; rfl
  have hs : after.stacks = Function.update before.stacks 0
      (SubexpLiftRing.fixedBits (d.stacks 124).length 1) := by
    funext i
    fin_cases i <;> simp [before, after, SubexpConstantPrograms.state,
      ModularPrograms.operandStacks]
  let out := embedState unitRegs unitPorts d after
  refine ⟨out, ?_, ?_⟩
  · have he := eval_call_lifted (SubexpConstantPrograms.program true) unitRegs unitPorts d
      unitRegs_injective unitPorts_injective ht
    convert he using 1 <;>
      simp [hin, before, after, out, BinaryArithmetic.bitVal]
    all_goals omega
  · change Function.extend unitPorts after.stacks d.stacks = _
    rw [hs, ProgramLinking.extend_update unitPorts_injective]
    have hbefore := congrArg StructuredProgram.State.stacks hin
    change Function.extend unitPorts before.stacks d.stacks = d.stacks at hbefore
    rw [hbefore]
    rfl

/-- The width shape is copied and read by the existing literal-word table.
No unbounded arithmetic operation is added to the instruction set. -/
theorem unit_init_eval (d : Data) (h0 : d.stacks 0 = [])
    (h124 : d.stacks 124 = []) (h215 : d.stacks 215 = []) (h216 : d.stacks 216 = [])
    (hwidth : 0 < (d.stacks 10).length) :
    ∃ out : Data, Eval unitInit (14 * (d.stacks 10).length + 14) d out ∧
      out.stacks = Function.update d.stacks 124
        (SubexpLiftRing.fixedBits (d.stacks 10).length 1) := by
  have hc := copy_eval d 10 124 0 0 1 (by decide) (by decide) (by decide) (by decide) h0
  let mid := afterCopy d 10 124 0 1
  have hs : mid.stacks = Function.update d.stacks 124 (d.stacks 10) := by
    simp [mid, afterCopy, StackRoutines.copyStacks, h124]
  obtain ⟨out, he, hout⟩ := unit_call_eval mid
    (by simpa [hs] using h215) (by simpa [hs] using h216)
    (by simpa [hs] using hwidth)
  refine ⟨out, ?_, ?_⟩
  · have h := hc.seq he
    simpa only [hs, Function.update_same, unitInit,
      show ∀ n : ℕ, (7*n+5)+(7*n+9)=14*n+14 by omega] using h
  · simpa [hs] using hout

def frameRegs : Fin 3 → Fin 16 := Fin.castAdd 13
def framePorts (src : Fin 256) : Fin 3 → Fin 256 := ![src, 215, 216]

theorem frameRegs_injective : Function.Injective frameRegs := Fin.castAdd_injective _ _

theorem framePorts_injective (src : Fin 256) (h215 : src ≠ 215) (h216 : src ≠ 216) :
    Function.Injective (framePorts src) := by
  intro i j he
  fin_cases i <;> fin_cases j <;> simp_all [framePorts]

abbrev frameCall (src : Fin 256) : Cmd 16 256 :=
  .call (ProgramLinking.liftProgram SubexpBlockAssembly.frameBody frameRegs (framePorts src))

abbrev frame (src : Fin 256) : Cmd 16 256 :=
  .seq (.base (.atom (.set 2 true))) (frameCall src)

def framed (d : Data) (src : Fin 256) : Data :=
  ⟨Function.update (Function.update (Function.update d.regs 0 false) 1 false) 2 true,
    Function.update d.stacks 215 ((Encoding.frame (d.stacks src)).reverse ++ d.stacks 215)⟩

theorem frame_call_eval (d : Data) (src : Fin 256)
    (hs215 : src ≠ 215) (hs216 : src ≠ 216)
    (h216 : d.stacks 216 = []) (hreg : d.regs 2 = true) :
    Eval (frameCall src) (8 * (d.stacks src).length + 6) d (framed d src) := by
  let before : State 3 3 := ⟨SubexpHornerProgram.triple (d.regs 0) (d.regs 1) true,
    SubexpHornerProgram.triple (d.stacks src) (d.stacks 215) []⟩
  let after : State 3 3 := ⟨SubexpHornerProgram.triple false false true,
    SubexpHornerProgram.triple (d.stacks src)
      ((Encoding.frame (d.stacks src)).reverse ++ d.stacks 215) []⟩
  have hin : embedState frameRegs (framePorts src) d before = d := by
    apply embedState_eq _ _ frameRegs_injective (framePorts_injective src hs215 hs216)
    · intro i; fin_cases i <;> simp [before, SubexpHornerProgram.triple, frameRegs, hreg]
    · intro i; fin_cases i <;> simp [before, SubexpHornerProgram.triple, framePorts, h216]
    · intros; rfl
    · intros; rfl
  have hout : embedState frameRegs (framePorts src) d after = framed d src := by
    apply embedState_eq _ _ frameRegs_injective (framePorts_injective src hs215 hs216)
    · intro i; fin_cases i <;> simp [after, SubexpHornerProgram.triple, frameRegs, framed]
    · intro i; fin_cases i <;> simp [after, SubexpHornerProgram.triple, framePorts,
        framed, hs215, h216]
    · intro j hj
      have h0 : j ≠ 0 := fun he => hj ⟨0, he.symm⟩
      have h1 : j ≠ 1 := fun he => hj ⟨1, he.symm⟩
      have h2 : j ≠ 2 := fun he => hj ⟨2, he.symm⟩
      simp [framed, h0, h1, h2]
    · intro j hj
      have h215 : j ≠ 215 := fun he => hj ⟨1, he.symm⟩
      simp [framed, h215]
  have ht : Trace SubexpBlockAssembly.frameBody (8 * (d.stacks src).length + 6)
      (before.withPC (some SubexpBlockAssembly.frameBody.entry)) (after.withPC none) :=
    SubexpBlockAssembly.frameBody_trace (d.stacks src) (d.stacks 215) (d.regs 0) (d.regs 1)
  have he := eval_call_lifted SubexpBlockAssembly.frameBody frameRegs (framePorts src) d
    frameRegs_injective (framePorts_injective src hs215 hs216) ht
  simpa only [frameCall, hin, hout] using he

abbrev unitProgram : Program 16 256 (size unitInit + 1) := compiled unitInit 10 124

end SubexponentialSAT.SubexpNodeConstants

end OAI.Algorithms
