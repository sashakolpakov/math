import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SquarefreeProgramPrepend
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SquarefreeSparseOps
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SquarefreeIndexEncoding
import OAI.Algorithms.SubexponentialSAT.SubexpDenseLiteralPadding

namespace OAI.Algorithms

/-! Construct a cached sparse constant from a shape word and a forward flat
coefficient. Zero support bits, key delimiters, reversal, record framing and
cleanup all execute on the native bit machine. -/
namespace SubexponentialSAT.SqrtLog.HashCircuitProgram.Constant
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev Data := State 8 6

def data (regs : Fin 8 → Bool) (shape input key coeff rev output : List Bool) : Data :=
  ⟨regs,![shape,input,key,coeff,rev,output]⟩

def key (n : ℕ) : List Bool := List.replicate (n+2) false

theorem key_eq_origin (n : ℕ) : key n = Squarefree.encodeIndex (Squarefree.Index.origin : Squarefree.Index (Fin n)) := by
  unfold key
  rw [Nat.add_comm n 2,List.replicate_add]
  simp [Squarefree.encodeIndex,Squarefree.Index.origin,Encoding.encodeNat,Squarefree.encodeMask,
    List.ofFn_const]

def padStacks : Fin 3 → Fin 6 := Fin.castAdd 3
theorem padStacks_injective : Function.Injective padStacks := Fin.castAdd_injective _ _
abbrev pad : Cmd 8 6 := .call (ProgramLinking.liftProgram ModularPrograms.paddingProgram id padStacks)

private theorem embedPad (regs rr : Fin 8 → Bool)
    (shape input before coeff rev out shape' input' after : List Bool) :
    embedState id padStacks (data regs shape input before coeff rev out)
      (⟨rr,ModularPrograms.operandStacks shape' input' after⟩ : State 8 3) =
        data rr shape' input' after coeff rev out := by
  apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id padStacks_injective
  · intro i; rfl
  · intro i hi; exact False.elim (hi ⟨i,rfl⟩)
  · intro i; fin_cases i <;> rfl
  · intro i hi; fin_cases i <;> simp_all [padStacks,data,Fin.exists_fin_succ]

theorem pad_eval (regs : Fin 8 → Bool) (shape coeff : List Bool) :
    ∃ rr, Eval pad (4*shape.length+3) (data regs shape [] [] coeff [] [])
      (data rr [] [] (List.replicate shape.length false) coeff [] []) := by
  obtain ⟨rr,h⟩ := SubexponentialSAT.SubexpDenseLiteralPadding.padding_trace_any regs shape [] []
  have ht : Trace ModularPrograms.paddingProgram (4*shape.length+3)
      ((⟨regs,ModularPrograms.operandStacks shape [] []⟩ : State 8 3).withPC
        (some ModularPrograms.paddingProgram.entry))
      ((⟨rr,ModularPrograms.operandStacks [] (([] : List Bool).drop shape.length)
        ((ModularArithmetic.padTo shape []).reverse ++ [])⟩ : State 8 3).withPC none) := by
    simpa [ModularPrograms.paddingCfg,ModularPrograms.paddingProgram,StructuredProgram.State.withPC] using h
  have he := eval_call_lifted ModularPrograms.paddingProgram id padStacks
    (data regs shape [] [] coeff [] []) Function.injective_id padStacks_injective ht
  simp only [embedPad] at he
  have hp : ModularArithmetic.padTo shape [] = List.replicate shape.length false := by
    clear h ht he
    induction shape with
    | nil => rfl
    | cons b shape ih => simpa [ModularArithmetic.padTo,List.replicate_succ] using congrArg (false :: ·) ih
  refine ⟨rr,?_⟩
  simpa [hp] using he

abbrev tag : Cmd 8 6 :=
  .seq (.base (.atom (.set 0 false)))
    (.seq (.base (.atom (.push 2 0))) (.base (.atom (.push 2 0))))

theorem tag_eval (regs : Fin 8 → Bool) (n : ℕ) (coeff : List Bool) :
    Eval tag 3 (data regs [] [] (List.replicate n false) coeff [] [])
      (data (Function.update regs 0 false) [] [] (key n) coeff [] []) := by
  let d := data regs [] [] (List.replicate n false) coeff [] []
  have h := (Eval.base (StructuredProgram.Eval.atom (.set (0 : Fin 8) false) d)).seq
    ((Eval.base (StructuredProgram.Eval.atom (.push (2 : Fin 6) (0 : Fin 8)) _)).seq
      (Eval.base (StructuredProgram.Eval.atom (.push (2 : Fin 6) (0 : Fin 8)) _)))
  convert h using 1
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i; fin_cases i <;>
      simp [d,data,key,StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
        StructuredProgram.State.ofCfg,execInstr,List.replicate_succ]

abbrev reverseCoefficient : Cmd 8 6 :=
  .call (StackRoutines.transferProgram (3 : Fin 6) 4 (0 : Fin 8) 1)

theorem reverseCoefficient_eval (regs : Fin 8 → Bool) (k coeff : List Bool) :
    Eval reverseCoefficient (3*coeff.length+3) (data regs [] [] k coeff [] [])
      (data (readRegs regs 0 1 none) [] [] k [] coeff.reverse []) := by
  let d := data regs [] [] k coeff [] []
  have h := StackRoutines.transferProgram_trace (3 : Fin 6) 4 (0 : Fin 8) 1
    (by decide) (by decide) d.regs d.stacks
  have hh := StackRoutines.halt_after_trace _ h 3 rfl rfl
  have hs : StackRoutines.transferStacks (3 : Fin 6) 4 d.stacks =
      (data (readRegs regs 0 1 none) [] [] k [] coeff.reverse []).stacks := by
    funext i; fin_cases i <;> simp [d,data,StackRoutines.transferStacks]
  apply Eval.call
  simp only [StackRoutines.transferResult] at hh
  rw [hs] at hh
  simpa [d,data,StructuredProgram.State.withPC,StackRoutines.transferProgram,Nat.add_assoc] using hh

def emitRegisters : Fin 3 → Fin 8 := Fin.castAdd 5
def emitStacks : Fin 3 → Fin 6 := ![2,4,5]
theorem emitRegisters_injective : Function.Injective emitRegisters := Fin.castAdd_injective _ _
theorem emitStacks_injective : Function.Injective emitStacks := by decide

abbrev emit : Cmd 8 6 :=
  .call (ProgramLinking.liftProgram Squarefree.Program.prependRecordProgram emitRegisters emitStacks)

private theorem embedEmit (regs : Fin 8 → Bool) (rr : Fin 3 → Bool)
    (beforeKey beforeCoeff beforeOut k c o : List Bool) :
    embedState emitRegisters emitStacks (data regs [] [] beforeKey [] beforeCoeff beforeOut)
      (Squarefree.Program.prependData rr k c o) =
        data (Function.extend emitRegisters rr regs) [] [] k [] c o := by
  apply embedState_eq_of_ports _ _ _ _ _ emitRegisters_injective emitStacks_injective
  · intro i
    exact emitRegisters_injective.extend_apply rr regs i
  · intro i hi
    exact Function.extend_apply' rr regs i hi
  · intro i; fin_cases i <;> rfl
  · intro i hi; fin_cases i <;> simp_all [emitStacks,data,Fin.exists_fin_succ]

theorem emit_eval (regs : Fin 8 → Bool) (n : ℕ) (coeff : List Bool) :
    ∃ rr, Eval emit (4*(n+2)+4*coeff.length+13)
      (data regs [] [] (key n) [] coeff.reverse [])
      (data rr [] [] [] [] [] (Encoding.frame (key n) ++ Encoding.frame coeff)) := by
  obtain ⟨rr,h⟩ := Squarefree.Program.prependRecord_trace (regs ∘ emitRegisters) (key n) coeff []
  have he := eval_call_lifted Squarefree.Program.prependRecordProgram emitRegisters emitStacks
    (data regs [] [] (key n) [] coeff.reverse []) emitRegisters_injective emitStacks_injective h
  have hr : Function.extend emitRegisters (regs ∘ emitRegisters) regs = regs := by
    funext i
    by_cases hi : ∃ j, emitRegisters j = i
    · obtain ⟨j,rfl⟩ := hi
      exact emitRegisters_injective.extend_apply _ _ _
    · exact Function.extend_apply' _ _ _ hi
  simp only [embedEmit,hr] at he
  refine ⟨Function.extend emitRegisters rr regs,?_⟩
  simpa [key] using he

abbrev command : Cmd 8 6 := .seq pad (.seq tag (.seq reverseCoefficient emit))
def program := compiled command 0 5

theorem command_eval (regs : Fin 8 → Bool) (shape coeff : List Bool) :
    ∃ rr, Eval command (8*shape.length+7*coeff.length+30)
      (data regs shape [] [] coeff [] [])
      (data rr [] [] [] [] [] (Encoding.frame (key shape.length) ++ Encoding.frame coeff)) := by
  obtain ⟨r1,h1⟩ := pad_eval regs shape coeff
  have h2 := tag_eval r1 shape.length coeff
  have h3 := reverseCoefficient_eval (Function.update r1 0 false) (key shape.length) coeff
  obtain ⟨r4,h4⟩ := emit_eval (readRegs (Function.update r1 0 false) 0 1 none) shape.length coeff
  refine ⟨r4,?_⟩
  convert h1.seq (h2.seq (h3.seq h4)) using 1 ; omega

theorem program_runs (regs : Fin 8 → Bool) (shape coeff : List Bool) :
    ∃ rr, RunsIn program (8*shape.length+7*coeff.length+31)
      ((data regs shape [] [] coeff [] []).withPC (some program.entry))
      ((data rr [] [] [] [] [] (Encoding.frame (key shape.length) ++ Encoding.frame coeff)).withPC none) := by
  obtain ⟨rr,he⟩ := command_eval regs shape coeff
  exact ⟨rr,_,by omega,compiled_halt_trace he 0 5⟩
end SubexponentialSAT.SqrtLog.HashCircuitProgram.Constant

end OAI.Algorithms
