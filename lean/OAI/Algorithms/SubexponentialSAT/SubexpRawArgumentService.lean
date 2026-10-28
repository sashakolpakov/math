import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpArgumentKeyEmitter
import OAI.Algorithms.SubexponentialSAT.SubexpDenseProgram
import OAI.Algorithms.SubexponentialSAT.ProgramFrames

namespace OAI.Algorithms

/-! Concrete restricted-key generation followed by raw-coefficient term emission. -/
namespace SubexponentialSAT.SubexpRawArgumentService

open BitProgram StructuredCalls

abbrev Data := State 5 10

def state (regs : Fin 5 → Bool) (coefficient key left output right z width spare : List Bool) : Data :=
  ⟨regs, ![coefficient,key,left,output,right,z,width,spare,[],[]]⟩

def keyRegs : Fin 4 → Fin 5 := Fin.castAdd 1

def keyPorts : Fin 5 → Fin 10 := ![2,4,5,6,1]
def rawPorts : Fin 6 → Fin 10 := ![0,1,7,3,8,9]

theorem keyRegs_injective : Function.Injective keyRegs := by
  intro i j h; apply Fin.ext; exact congrArg (fun x : Fin 5 => x.val) h

theorem keyPorts_injective : Function.Injective keyPorts := by decide
theorem rawPorts_injective : Function.Injective rawPorts := by decide

def keyProgram := ProgramLinking.liftProgram SubexpArgumentKeyEmitter.program keyRegs keyPorts
def rawProgram := ProgramLinking.liftProgram SubexpDenseProgram.RawEmitter.emitRawTermProgram id rawPorts

abbrev command : Cmd 5 10 := .seq (.call keyProgram) (.call rawProgram)
def program := compiled command 0 3

def cost (left right j B : ℕ) (mark u : Bool) (c : List Bool) : ℕ :=
  SubexpArgumentKeyEmitter.rawCost left right j mark u +
    4 * (B - (SubexpArgumentKeyEmitter.rawKey left right j mark u).length) + 3 +
    (37 * c.length + 21 * (SubexpArgumentKeyEmitter.paddedKey left right j B mark u).length + 57)

theorem command_eval (left right j B : ℕ) (regs : Fin 5 → Bool)
    (coefficient output spare : List Bool) :
    Eval command (cost left right j B (regs 2) (regs 3) coefficient)
      (state regs coefficient [] (List.replicate left true) output
        (List.replicate right true) (List.replicate j true) (List.replicate B true) spare)
      (state (SubexpArgumentProgram.finishedRegs regs) [] [] []
        (true :: (Encoding.frame (SubexpArgumentProgram.recordBody
          (SubexpArgumentKeyEmitter.paddedKey left right j B (regs 2) (regs 3)) coefficient) ++ output))
        [] [] [] spare) := by
  let key := SubexpArgumentKeyEmitter.paddedKey left right j B (regs 2) (regs 3)
  let start := state regs coefficient [] (List.replicate left true) output
    (List.replicate right true) (List.replicate j true) (List.replicate B true) spare
  let rr := readRegs regs 0 1 none
  let middle := state rr coefficient key.reverse [] output [] [] [] spare
  let finish := state (SubexpArgumentProgram.finishedRegs regs) [] [] []
    (true :: (Encoding.frame (SubexpArgumentProgram.recordBody key coefficient) ++ output)) [] [] [] spare
  let ka := SubexpArgumentKeyProgram.state (regs 0) (regs 1) (regs 2) (regs 3)
    (SubexpArgumentKeyEmitter.counters left right j) (List.replicate B true) []
  let kb := SubexpArgumentKeyProgram.state false false (regs 2) (regs 3)
    (SubexpArgumentKeyEmitter.counters 0 0 0) [] key.reverse
  have hka : embedState keyRegs keyPorts start ka = start := by
    apply embedState_eq_of_ports _ _ _ _ _ keyRegs_injective keyPorts_injective
    · intro i; fin_cases i <;> rfl
    · intros; rfl
    · intro i; fin_cases i <;> rfl
    · intros; rfl
  have hkb : embedState keyRegs keyPorts start kb = middle := by
    apply embedState_eq_of_ports _ _ _ _ _ keyRegs_injective keyPorts_injective
    · intro i; fin_cases i <;> simp [kb,middle,state,rr,readRegs,keyRegs,
        SubexpArgumentKeyProgram.state,SubexpArgumentKeyProgram.regs,SubexpPostfixControl.quadruple]
    · intro i hi
      have h0 : i ≠ 0 := fun h => hi ⟨0,h.symm⟩
      have h1 : i ≠ 1 := fun h => hi ⟨1,h.symm⟩
      simp [middle,start,state,rr,readRegs,h0,h1]
    · intro i; fin_cases i <;> rfl
    · intro i hi
      have h1 : i ≠ 1 := fun h => hi ⟨4,h.symm⟩
      have h2 : i ≠ 2 := fun h => hi ⟨0,h.symm⟩
      have h4 : i ≠ 4 := fun h => hi ⟨1,h.symm⟩
      have h5 : i ≠ 5 := fun h => hi ⟨2,h.symm⟩
      have h6 : i ≠ 6 := fun h => hi ⟨3,h.symm⟩
      fin_cases i <;> first | rfl | contradiction
  have kh := eval_call_lifted SubexpArgumentKeyEmitter.program keyRegs keyPorts start
    keyRegs_injective keyPorts_injective
    (SubexpArgumentKeyEmitter.program_trace left right j B (regs 0) (regs 1) (regs 2) (regs 3) [])
  simp only [List.append_nil] at kh
  change Eval (.call keyProgram) _ (embedState keyRegs keyPorts start ka)
    (embedState keyRegs keyPorts start kb) at kh
  rw [hka,hkb] at kh
  let ra := SubexpRecordScan.recordState rr coefficient key.reverse spare output [] []
  let rb := SubexpRecordScan.recordState (SubexpArgumentProgram.finishedRegs rr) [] [] spare
    (true :: (Encoding.frame (SubexpArgumentProgram.recordBody key coefficient) ++ output)) [] []
  have hra : embedState id rawPorts middle ra = middle := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id rawPorts_injective
    · intros; rfl
    · intro i hi; exact (hi ⟨i,rfl⟩).elim
    · intro i; fin_cases i <;> rfl
    · intros; rfl
  have hrb : embedState id rawPorts middle rb = finish := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id rawPorts_injective
    · intro i; fin_cases i <;> simp [rb,finish,state,rr,readRegs,
        SubexpArgumentProgram.finishedRegs]
    · intro i hi; exact (hi ⟨i,rfl⟩).elim
    · intro i; fin_cases i <;> rfl
    · intro i hi
      have h0 : i ≠ 0 := fun h => hi ⟨0,h.symm⟩
      have h1 : i ≠ 1 := fun h => hi ⟨1,h.symm⟩
      have h3 : i ≠ 3 := fun h => hi ⟨3,h.symm⟩
      fin_cases i <;> first | rfl | contradiction
  have rh := eval_call_lifted SubexpDenseProgram.RawEmitter.emitRawTermProgram id rawPorts middle
    Function.injective_id rawPorts_injective
    (SubexpDenseProgram.RawEmitter.emitRawTerm_trace key coefficient spare output rr)
  change Eval (.call rawProgram) _ (embedState id rawPorts middle ra) (embedState id rawPorts middle rb) at rh
  rw [hra,hrb] at rh
  exact Eval.seq kh rh

theorem program_trace (left right j B : ℕ) (regs : Fin 5 → Bool)
    (coefficient output spare : List Bool) :
    Trace program (cost left right j B (regs 2) (regs 3) coefficient + 1)
      ((state regs coefficient [] (List.replicate left true) output
        (List.replicate right true) (List.replicate j true) (List.replicate B true) spare).withPC
        (some program.entry))
      ((state (SubexpArgumentProgram.finishedRegs regs) [] [] []
        (true :: (Encoding.frame (SubexpArgumentProgram.recordBody
          (SubexpArgumentKeyEmitter.paddedKey left right j B (regs 2) (regs 3)) coefficient) ++ output))
        [] [] [] spare).withPC none) :=
  compiled_halt_trace (command_eval left right j B regs coefficient output spare) 0 3

end SubexponentialSAT.SubexpRawArgumentService

end OAI.Algorithms
