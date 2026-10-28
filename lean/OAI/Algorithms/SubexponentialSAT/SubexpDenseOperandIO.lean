import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpDenseProgram
import OAI.Algorithms.SubexponentialSAT.SubexpEvaluationProgram

namespace OAI.Algorithms

/-! Fixed finite framing operations at the physical postfix operand port.
These routines preserve the code/depth stacks and all surrounding data. -/

namespace SubexponentialSAT.SubexpDenseOperandIO

open BitProgram StructuredCalls SubexpScanPrimitives

abbrev Data := State 16 128

def parseRegs : Fin 2 → Fin 16 := Fin.castAdd 14
def parseStacks : Fin 2 → Fin 128 := ![27, 29]
abbrev parseProgram : Program 16 128 7 :=
  ProgramLinking.liftProgram ParserProgram.frameProgram parseRegs parseStacks

theorem parseRegs_injective : Function.Injective parseRegs := by
  intro a b h
  apply Fin.ext
  exact congrArg (fun i : Fin 16 => i.val) h

theorem parseStacks_injective : Function.Injective parseStacks := by decide

abbrev afterParse (d : Data) (bits tail : List Bool) : Data :=
  ⟨readRegs d.regs 0 1 (some false),
    Function.update (Function.update d.stacks 27 tail) 29 bits.reverse⟩

theorem parse_eval (d : Data) (bits tail : List Bool)
    (hin : d.stacks 27 = Encoding.frame bits ++ tail) (hscratch : d.stacks 29 = []) :
    Eval (.call parseProgram) (6 * bits.length + 4) d (afterParse d bits tail) := by
  let a : State 2 2 :=
    ⟨ParserProgram.pair (d.regs 0) (d.regs 1),
      ParserProgram.pair (Encoding.frame bits ++ tail) []⟩
  let b : State 2 2 :=
    ⟨ParserProgram.pair false true, ParserProgram.pair tail bits.reverse⟩
  have ha : embedState parseRegs parseStacks d a = d := by
    apply embedState_eq_of_ports _ _ _ _ _ parseRegs_injective parseStacks_injective
    · intro i; fin_cases i <;> rfl
    · intros; rfl
    · intro i; fin_cases i
      · exact hin
      · exact hscratch
    · intros; rfl
  have hb : embedState parseRegs parseStacks d b = afterParse d bits tail := by
    apply embedState_eq_of_ports _ _ _ _ _ parseRegs_injective parseStacks_injective
    · intro i; fin_cases i <;> simp [ parseRegs, readRegs, b, ParserProgram.pair]
    · intro i hi
      have h0 : i ≠ 0 := fun h => hi ⟨0, by simpa [parseRegs] using h.symm⟩
      have h1 : i ≠ 1 := fun h => hi ⟨1, by simpa [parseRegs] using h.symm⟩
      simp [ readRegs, h0, h1]
    · intro i; fin_cases i <;> simp [ parseStacks, b, ParserProgram.pair]
    · intro i hi
      have h27 : i ≠ 27 := fun h => hi ⟨0, by simpa [parseStacks] using h.symm⟩
      have h29 : i ≠ 29 := fun h => hi ⟨1, by simpa [parseStacks] using h.symm⟩
      simp [ h27, h29]
  have ht : Trace ParserProgram.frameProgram (6 * bits.length + 4)
      (a.withPC (some ParserProgram.frameProgram.entry)) (b.withPC none) := by
    change Trace ParserProgram.frameProgram (6 * bits.length + 4)
      (ParserProgram.cfg (some 0) (d.regs 0) (d.regs 1)
        (Encoding.frame bits ++ tail) [])
      (ParserProgram.cfg none false true tail bits.reverse)
    simpa only [List.append_nil] using
      ParserProgram.frame_trace bits tail [] (d.regs 0) (d.regs 1)
  simpa only [parseProgram, ha, hb] using
    eval_call_lifted ParserProgram.frameProgram parseRegs parseStacks d
      parseRegs_injective parseStacks_injective ht

abbrev takeOperand (dst : Fin 128) : Cmd 16 128 :=
  .seq (.base (.atom (.pop 27 0 1)))
    (.seq (.call parseProgram) (.call (StackRoutines.transferProgram 29 dst 0 1)))

def popped (d : Data) : Data := (StructuredProgram.Atom.pop 27 0 1).eval d

def takeResult (d : Data) (dst : Fin 128) (bits tail : List Bool) : Data :=
  afterTransfer (afterParse (popped d) bits tail) 29 dst 0 1

theorem takeOperand_eval (d : Data) (dst : Fin 128) (bits tail : List Bool)
    (hdst : (29 : Fin 128) ≠ dst)
    (hin : d.stacks 27 = true :: (Encoding.frame bits ++ tail))
    (hscratch : d.stacks 29 = []) :
    Eval (takeOperand dst) (9 * bits.length + 8) d (takeResult d dst bits tail) := by
  have hp : Eval (.base (.atom (.pop 27 0 1))) 1 d (popped d) :=
    .base (.atom _ _)
  have hp27 : (popped d).stacks 27 = Encoding.frame bits ++ tail := by
    simp [popped, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg, execInstr, hin]
  have hp29 : (popped d).stacks 29 = [] := by
    simpa [popped, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.withPC, StructuredProgram.State.ofCfg, execInstr] using hscratch
  have hr := parse_eval (popped d) bits tail hp27 hp29
  have ht := transfer_eval (afterParse (popped d) bits tail) 29 dst 0 1 hdst (by decide)
  have hs : ((afterParse (popped d) bits tail).stacks 29).length = bits.length := by
    simp []
  rw [hs] at ht
  have h := Eval.seq hp (Eval.seq hr ht)
  convert h using 1 <;> first | omega | rfl

theorem takeResult_stack (d : Data) (dst : Fin 128) (bits tail : List Bool)
    (hdst : dst ≠ 27) (hdst' : dst ≠ 29) :
    (takeResult d dst bits tail).stacks =
      Function.update (Function.update (Function.update d.stacks 27 tail)
        dst (bits ++ d.stacks dst)) 29 [] := by
  funext i
  by_cases h27 : i = 27 <;> by_cases h29 : i = 29 <;> by_cases hd : i = dst <;>
    simp_all [takeResult, afterTransfer, popped, StackRoutines.transferStacks,
      StructuredProgram.Atom.eval, StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg, execInstr
      ]

def writeRegs : Fin 3 → Fin 16 := Fin.castAdd 13
def writeStacks : Fin 4 → Fin 128 := ![26, 28, 27, 29]
abbrev writeProgram : Program 16 128 17 :=
  ProgramLinking.liftProgram SubexpNormalizeProgram.emitRecordProgram writeRegs writeStacks

theorem writeRegs_injective : Function.Injective writeRegs := by
  intro a b h
  apply Fin.ext
  exact congrArg (fun i : Fin 16 => i.val) h
theorem writeStacks_injective : Function.Injective writeStacks := by decide

def afterWrite (d : Data) (bits : List Bool) : Data :=
  ⟨Function.update (Function.update d.regs 0 true) 1 false,
    Function.update (Function.update d.stacks 27
      (true :: (Encoding.frame bits ++ d.stacks 27))) 29 []⟩

theorem write_eval (d : Data) (bits : List Bool) (hscratch : d.stacks 29 = bits.reverse) :
    Eval (.call writeProgram) (5 * bits.length + 7) d (afterWrite d bits) := by
  let a := SubexpNormalizeProgram.filterState (d.regs 0) (d.regs 1) (d.regs 2)
    (d.stacks 26) (d.stacks 28) (d.stacks 27) bits.reverse
  let b := SubexpNormalizeProgram.filterState true false (d.regs 2)
    (d.stacks 26) (d.stacks 28) (true :: (Encoding.frame bits ++ d.stacks 27)) []
  have ha : embedState writeRegs writeStacks d a = d := by
    apply embedState_eq_of_ports _ _ _ _ _ writeRegs_injective writeStacks_injective
    · intro i; fin_cases i <;> rfl
    · intros; rfl
    · intro i; fin_cases i <;> first | rfl | exact hscratch
    · intros; rfl
  have hb : embedState writeRegs writeStacks d b = afterWrite d bits := by
    apply embedState_eq_of_ports _ _ _ _ _ writeRegs_injective writeStacks_injective
    · intro i; fin_cases i <;>
        simp [afterWrite, writeRegs, b, SubexpNormalizeProgram.filterState,
          SubexpPostfixControl.triple]
    · intro i hi
      have h0 : i ≠ 0 := fun h => hi ⟨0, by simpa [writeRegs] using h.symm⟩
      have h1 : i ≠ 1 := fun h => hi ⟨1, by simpa [writeRegs] using h.symm⟩
      simp [afterWrite,h0,h1]
    · intro i; fin_cases i <;>
        simp [afterWrite, writeStacks, b, SubexpNormalizeProgram.filterState,
          SubexpPostfixControl.quadruple]
    · intro i hi
      have h27 : i ≠ 27 := fun h => hi ⟨2, by simpa [writeStacks] using h.symm⟩
      have h29 : i ≠ 29 := fun h => hi ⟨3, by simpa [writeStacks] using h.symm⟩
      simp [afterWrite,h27,h29]
  have ht := SubexpNormalizeProgram.emitRecord_trace bits (d.stacks 26) (d.stacks 28)
    (d.stacks 27) (d.regs 0) (d.regs 1) (d.regs 2)
  simpa only [writeProgram, ha, hb] using
    eval_call_lifted SubexpNormalizeProgram.emitRecordProgram writeRegs writeStacks d
      writeRegs_injective writeStacks_injective (a := a) (b := b) ht

abbrev putOperand : Cmd 16 128 :=
  .seq (.call (StackRoutines.transferProgram 21 29 0 1)) (.call writeProgram)

def putResult (d : Data) (bits : List Bool) : Data :=
  afterWrite (afterTransfer d 21 29 0 1) bits

theorem putOperand_eval (d : Data) (bits : List Bool)
    (hinput : d.stacks 21 = bits) (hscratch : d.stacks 29 = []) :
    Eval putOperand (8 * bits.length + 10) d (putResult d bits) := by
  have ht := transfer_eval d 21 29 0 1 (by decide) (by decide)
  rw [hinput] at ht
  have hs : (afterTransfer d 21 29 0 1).stacks 29 = bits.reverse := by
    simp [afterTransfer, StackRoutines.transferStacks, hinput, hscratch]
  have hw := write_eval (afterTransfer d 21 29 0 1) bits hs
  convert Eval.seq ht hw using 1 <;> first | omega | rfl

theorem putResult_stack (d : Data) (bits : List Bool) :
    (putResult d bits).stacks =
      Function.update (Function.update (Function.update d.stacks 21 [])
        27 (true :: (Encoding.frame bits ++ d.stacks 27))) 29 [] := by
  funext i
  by_cases h21 : i = 21 <;> by_cases h27 : i = 27 <;> by_cases h29 : i = 29 <;>
    simp_all [putResult, afterWrite, afterTransfer, StackRoutines.transferStacks
      ]

abbrev reset : Cmd 16 128 := .call SubexpEvaluationProgram.resetProgram

theorem reset_eval (d : Data) : Eval reset 17 d ⟨fun _ => false, d.stacks⟩ := by
  exact .call _ (SubexpEvaluationProgram.reset_trace d.regs d.stacks)

end SubexponentialSAT.SubexpDenseOperandIO

end OAI.Algorithms
