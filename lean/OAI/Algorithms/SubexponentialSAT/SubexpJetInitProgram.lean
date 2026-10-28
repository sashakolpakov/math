import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpScanPrimitives
import OAI.Algorithms.SubexponentialSAT.Subexp.BlockCopyProgram

namespace OAI.Algorithms

/-!
# Initializing the packed output jet

The input dimension is a unary word on stack 109 and the scalar word width is
the length of stack 10.  The fixed program constructs one four-word zero
coefficient on stack 104 and copies it D times to stack 102.  It preserves both
input words.  No zero array is supplied as an input certificate.
-/

namespace SubexponentialSAT.SubexpJetInitProgram

open BitProgram StructuredCalls SubexpScanPrimitives

abbrev Data := State 16 128
abbrev Code := Cmd 16 128

def blockRegisters : Fin 3 → Fin 16 := Fin.castAdd 13
def blockStacks : Fin 4 → Fin 128 := ![104, 102, 107, 108]

theorem blockRegisters_injective : Function.Injective blockRegisters :=
  by
    intro a b h
    apply Fin.ext
    exact congrArg (fun x : Fin 16 => x.val) h

theorem blockStacks_injective : Function.Injective blockStacks := by decide

abbrev copyWidth : Code := .call (StackRoutines.copyProgram 10 106 107 0 1)
abbrev zeroCell : Code := .call (zeroFillProgram 106 104 0 1)
abbrev copyDimension : Code := .call (StackRoutines.copyProgram 109 108 107 0 1)
def resetActive : Code := .base (.atom (.set 2 false))
abbrev repeatCell : Code := .call (ProgramLinking.liftProgram
  Subexp.BlockCopyProgram.program blockRegisters blockStacks)

def command : Code :=
  .seq copyWidth (.seq zeroCell (.seq copyDimension (.seq resetActive repeatCell)))

abbrev program : Program 16 128 (size command + 1) := compiled command 109 102

def repeatOut (d : Data) (D : ℕ) (cell output : List Bool) : Data :=
  ⟨Function.update (Function.update (Function.update d.regs 0 false) 1 false) 2 false,
    Function.update (Function.update d.stacks 108 []) 102
      (Subexp.BlockCopyProgram.copies D cell ++ output)⟩

theorem repeatCell_eval (d : Data) (D : ℕ) (cell output : List Bool)
    (h0 : d.regs 0 = false) (h1 : d.regs 1 = false) (h2 : d.regs 2 = false)
    (hc : d.stacks 104 = cell) (ho : d.stacks 102 = output)
    (ht : d.stacks 107 = []) (hn : d.stacks 108 = List.replicate D true) :
    Eval repeatCell (D * (7 * cell.length + 7) + 3) d (repeatOut d D cell output) := by
  have hi : embedState blockRegisters blockStacks d
      (Subexp.BlockCopyProgram.initialState D cell output) = d := by
    apply embedState_eq _ _ blockRegisters_injective blockStacks_injective
    · intro i
      fin_cases i <;>
        simp [blockRegisters, Subexp.BlockCopyProgram.initialState,
          Subexp.BlockCopyProgram.data, h0, h1, h2]
    · intro i
      fin_cases i <;>
        simp [blockStacks, Subexp.BlockCopyProgram.initialState,
          Subexp.BlockCopyProgram.data, hc, ho, ht, hn]
    · intros; rfl
    · intros; rfl
  have hf : embedState blockRegisters blockStacks d
      (Subexp.BlockCopyProgram.data false false cell
        (Subexp.BlockCopyProgram.copies D cell ++ output) []) =
          repeatOut d D cell output := by
    apply embedState_eq _ _ blockRegisters_injective blockStacks_injective
    · intro i
      fin_cases i <;> simp [blockRegisters, repeatOut, Subexp.BlockCopyProgram.data]
    · intro i
      fin_cases i <;> simp [blockStacks, repeatOut, Subexp.BlockCopyProgram.data, hc, ht]
    · intro i hi
      have h0 : i ≠ 0 := fun h => hi ⟨0, by simpa [blockRegisters] using h.symm⟩
      have h1 : i ≠ 1 := fun h => hi ⟨1, by simpa [blockRegisters] using h.symm⟩
      have h2 : i ≠ 2 := fun h => hi ⟨2, by simpa [blockRegisters] using h.symm⟩
      simp [repeatOut, h0, h1, h2]
    · intro i hi
      have h102 : i ≠ 102 := fun h => hi ⟨1, by simpa [blockStacks] using h.symm⟩
      have h108 : i ≠ 108 := fun h => hi ⟨3, by simpa [blockStacks] using h.symm⟩
      simp [repeatOut, h102, h108]
  have h := eval_call_lifted Subexp.BlockCopyProgram.program blockRegisters blockStacks d
    blockRegisters_injective blockStacks_injective
    (Subexp.BlockCopyProgram.program_trace D cell output)
  simpa only [hi, hf] using h

def initialized (d : Data) (D B : ℕ) : Data :=
  ⟨Function.update (Function.update (Function.update d.regs 0 false) 1 false) 2 false,
    Function.update (Function.update d.stacks 104 (List.replicate (4 * B) false))
      102 (List.replicate (D * (4 * B)) false)⟩

theorem copies_zeroCell (D B : ℕ) :
    Subexp.BlockCopyProgram.copies D (List.replicate (4 * B) false) =
      List.replicate (D * (4 * B)) false := by
  induction D with
  | zero => simp
  | succ D ih =>
      rw [Subexp.BlockCopyProgram.copies_succ, ih, ← List.replicate_add]
      congr 1
      ring

/-- The program builds all D zero coefficients by actual copying loops. -/
theorem command_eval (d : Data) (D B : ℕ)
    (hB : (d.stacks 10).length = B)
    (hD : d.stacks 109 = List.replicate D true)
    (h102 : d.stacks 102 = []) (h104 : d.stacks 104 = [])
    (h106 : d.stacks 106 = []) (h107 : d.stacks 107 = []) (h108 : d.stacks 108 = []) :
    Eval command (14 * B + D * (28 * B + 14) + 17) d (initialized d D B) := by
  let d1 := afterCopy d 10 106 0 1
  let d2 : Data := ⟨readRegs d1.regs 0 1 none,
    zeroFillStacks 106 104 (d1.stacks 106).length d1.stacks⟩
  let d3 := afterCopy d2 109 108 0 1
  let d4 : Data := ⟨Function.update d3.regs 2 false, d3.stacks⟩
  have e1 : Eval copyWidth (7 * B + 5) d d1 := by
    simpa only [copyWidth, hB] using
      copy_eval d 10 106 107 0 1 (by decide) (by decide) (by decide) (by decide) h107
  have l1 : (d1.stacks 106).length = B := by
    simp [d1, afterCopy, StackRoutines.copyStacks, h106, hB]
  have e2 : Eval zeroCell (7 * B + 3) d1 d2 := by
    simpa only [zeroCell, d2, l1] using
      zeroFill_eval 106 104 0 1 (by decide) (by decide) d1
  have e3 : Eval copyDimension (7 * D + 5) d2 d3 := by
    have ht : d2.stacks 107 = [] := by
      simp [d2, d1, afterCopy, StackRoutines.copyStacks, zeroFillStacks, h107]
    have hl : (d2.stacks 109).length = D := by
      simp [d2, d1, afterCopy, StackRoutines.copyStacks, zeroFillStacks, hD]
    simpa only [copyDimension, hl] using
      copy_eval d2 109 108 107 0 1 (by decide) (by decide) (by decide) (by decide) ht
  have e4 : Eval resetActive 1 d3 d4 := by
    exact .base (.atom _ _)
  have e5 : Eval repeatCell (D * (7 * (4 * B) + 7) + 3) d4
      (repeatOut d4 D (List.replicate (4 * B) false) []) := by
    have he := repeatCell_eval d4 D (List.replicate (4 * B) false) []
      (by simp [d4, d3, afterCopy, readRegs])
      (by simp [d4, d3, afterCopy, readRegs])
      (by simp [d4])
      (by simp [d4, d3, d2, d1, afterCopy, StackRoutines.copyStacks,
        zeroFillStacks, h104, h106, hB])
      (by simp [d4, d3, d2, d1, afterCopy, StackRoutines.copyStacks,
        zeroFillStacks, h102])
      (by simp [d4, d3, d2, d1, afterCopy, StackRoutines.copyStacks,
        zeroFillStacks, h107])
      (by simp [d4, d3, d2, d1, afterCopy, StackRoutines.copyStacks,
        zeroFillStacks, h108, hD])
    simpa only [List.length_replicate] using he
  have hout : repeatOut d4 D (List.replicate (4 * B) false) [] = initialized d D B := by
    apply state_ext
    · funext i
      fin_cases i <;> simp [repeatOut, initialized, d4, d3, d2, d1, afterCopy, readRegs]
    · funext i
      by_cases hi102 : i = 102
      · subst i
        simp [repeatOut, initialized, copies_zeroCell]
      · by_cases hi104 : i = 104
        · subst i
          simp [repeatOut, initialized, d4, d3, d2, d1, afterCopy,
            StackRoutines.copyStacks, zeroFillStacks, h104, h106, hB]
        · by_cases hi106 : i = 106
          · subst i
            simp [repeatOut, initialized, d4, d3, d2, d1, afterCopy,
              StackRoutines.copyStacks, zeroFillStacks, h106]
          · by_cases hi108 : i = 108
            · subst i
              simp [repeatOut, initialized, h108]
            · simp [repeatOut, initialized, d4, d3, d2, d1, afterCopy,
                StackRoutines.copyStacks, zeroFillStacks, hi102, hi104, hi106, hi108]
  have h := Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4 e5)))
  rw [hout] at h
  convert h using 1
  · rfl
  · ring

theorem program_trace (d : Data) (D B : ℕ)
    (hB : (d.stacks 10).length = B)
    (hD : d.stacks 109 = List.replicate D true)
    (h102 : d.stacks 102 = []) (h104 : d.stacks 104 = [])
    (h106 : d.stacks 106 = []) (h107 : d.stacks 107 = []) (h108 : d.stacks 108 = []) :
    Trace program (14 * B + D * (28 * B + 14) + 18)
      (d.withPC (some program.entry)) ((initialized d D B).withPC none) := by
  simpa only [program, Nat.add_assoc] using
    compiled_halt_trace (command_eval d D B hB hD h102 h104 h106 h107 h108) 109 102

theorem primitive_execution (d : Data) (D B : ℕ)
    (hB : (d.stacks 10).length = B)
    (hD : d.stacks 109 = List.replicate D true)
    (h102 : d.stacks 102 = []) (h104 : d.stacks 104 = [])
    (h106 : d.stacks 106 = []) (h107 : d.stacks 107 = []) (h108 : d.stacks 108 = []) :
    Computation.RunsIn (primitive program).step
      (primitiveOverhead program * (14 * B + D * (28 * B + 14) + 18))
      (primitiveCfg program (d.withPC (some program.entry)))
      (primitiveCfg program ((initialized d D B).withPC none)) :=
  primitive_trace _ (program_trace d D B hB hD h102 h104 h106 h107 h108)

theorem initialized_layout (d : Data) (D B : ℕ) :
    (initialized d D B).stacks 102 = List.replicate (D * (4 * B)) false ∧
    (initialized d D B).stacks 104 = List.replicate (4 * B) false ∧
    ∀ i, i ≠ 102 → i ≠ 104 → (initialized d D B).stacks i = d.stacks i := by
  refine ⟨by simp [initialized], by simp [initialized], ?_⟩
  intro i h102 h104
  simp [initialized, h102, h104]

end SubexponentialSAT.SubexpJetInitProgram

end OAI.Algorithms
