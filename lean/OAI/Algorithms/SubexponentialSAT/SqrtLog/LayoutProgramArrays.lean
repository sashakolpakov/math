import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ArrayUpdateLifted
import OAI.Algorithms.SubexponentialSAT.BinaryArithmetic

namespace OAI.Algorithms

/-! Physical access to the two-array integer matrix ABI. Every array entry is a
runtime-width binary word; its signed value is positive minus negative. The
fixed program below preserves both arrays, the index and width. It does not
assume a unit-cost array lookup or add an integer primitive to the machine. -/

namespace SubexponentialSAT.SqrtLog.LayoutProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.ArrayUpdateLifted

abbrev ArrayData := State 2 11

def signedValue (positive negative : List Bool) : ℤ :=
  (SubexponentialSAT.BinaryArithmetic.toNat positive : ℤ) -
    (SubexponentialSAT.BinaryArithmetic.toNat negative : ℤ)

def positivePorts : Fin 8 ↪ Fin 11 :=
  ⟨![0,5,3,4,7,8,9,10], by decide⟩

def negativePorts : Fin 8 ↪ Fin 11 :=
  ⟨![1,6,3,4,7,8,9,10], by decide⟩

/-- Source arrays 0,1; preserved unary index 2; temporary index 3; preserved
unary width 4; positive/negative outputs 5,6; scratch 7--10. -/
abbrev readSignedCommand : Cmd 2 11 :=
  .seq (.call (copyProgram 2 3 7 0 1))
    (.seq (.call (readProgramAt positivePorts 0 1))
      (.seq (.call (copyProgram 2 3 7 0 1))
        (.call (readProgramAt negativePorts 0 1))))

def readSignedProgram := compiled readSignedCommand 0 5

def readSignedStacks (positive negative : List Bool)
    (stk : Stacks (Fin 11)) : Stacks (Fin 11) :=
  Function.update (Function.update stk 5 (positive ++ stk 5))
    6 (negative ++ stk 6)

private theorem copyIndex_eval (d : ArrayData) (ht : d.stacks 7 = []) :
    Eval (.call (copyProgram 2 3 7 0 1)) (7 * (d.stacks 2).length + 5) d
      ⟨readRegs d.regs 0 1 none, copyStacks 2 3 d.stacks⟩ := by
  apply Eval.call
  have h := halt_after_trace _
    (copyProgram_trace (2 : Fin 11) 3 7 (0 : Fin 2) 1
      (by decide) (by decide) (by decide) (by decide) d.regs d.stacks ht)
    7 rfl rfl
  simpa [SubexponentialSAT.StructuredProgram.State.withPC, copyResult, copyProgram, Nat.add_assoc] using h

private theorem after_positive (positive : List Bool) (stk : Stacks (Fin 11))
    (h3 : stk 3 = []) :
    readStacksAt positivePorts positive (copyStacks 2 3 stk) =
      Function.update stk 5 (positive ++ stk 5) := by
  funext j
  fin_cases j <;> simp [readStacksAt, positivePorts, copyStacks, h3]

private theorem after_negative (negative : List Bool) (stk : Stacks (Fin 11))
    (h3 : stk 3 = []) :
    readStacksAt negativePorts negative (copyStacks 2 3 stk) =
      Function.update stk 6 (negative ++ stk 6) := by
  funext j
  fin_cases j <;> simp [readStacksAt, negativePorts, copyStacks, h3]

/-- The two signed components are read by actual preserving array scans.
No relation between the component magnitudes is needed. -/
theorem readSignedCommand_eval (d : ArrayData)
    (beforeP beforeN : List (List Bool))
    (positive negative restP restN width index : List Bool)
    (hp : d.stacks 0 = beforeP.flatten ++ (positive ++ restP))
    (hn : d.stacks 1 = beforeN.flatten ++ (negative ++ restN))
    (hi : d.stacks 2 = index) (hw : d.stacks 4 = width)
    (hip : index.length = beforeP.length) (hin : index.length = beforeN.length)
    (hwp : ∀ x ∈ beforeP, x.length = width.length)
    (hwn : ∀ x ∈ beforeN, x.length = width.length)
    (hlp : positive.length = width.length) (hln : negative.length = width.length)
    (h3 : d.stacks 3 = [])
    (hs : ∀ j : Fin 11, 7 ≤ j.val → d.stacks j = []) :
    Eval readSignedCommand
      (index.length * (28 * width.length + 34) + 30 * width.length + 42) d
      ⟨readRegs d.regs 0 1 none, readSignedStacks positive negative d.stacks⟩ := by
  let d1 : ArrayData := ⟨readRegs d.regs 0 1 none, copyStacks 2 3 d.stacks⟩
  have hc1 := copyIndex_eval d (hs 7 (by decide))
  have hp1 := readProgramAt_eval positivePorts (0 : Fin 2) 1 (by decide)
    beforeP positive restP width index d1.regs d1.stacks
    (by simpa [d1, positivePorts, copyStacks] using hp)
    (by simpa [d1, positivePorts, copyStacks] using hw)
    (by simp [d1, positivePorts, copyStacks, hi, h3]) hip hwp hlp
    (by simpa [d1, positivePorts, copyStacks] using hs 7 (by decide))
    (by simpa [d1, positivePorts, copyStacks] using hs 8 (by decide))
    (by simpa [d1, positivePorts, copyStacks] using hs 9 (by decide))
    (by simpa [d1, positivePorts, copyStacks] using hs 10 (by decide))
  let d2 : ArrayData := ⟨readRegs d.regs 0 1 none,
    Function.update d.stacks 5 (positive ++ d.stacks 5)⟩
  have hp2 : Eval (.call (readProgramAt positivePorts 0 1))
      (beforeP.length * (14 * width.length + 10) + 15 * width.length + 16) d1 d2 := by
    simpa [d1, d2, readRegs_reset, after_positive positive d.stacks h3] using hp1
  have hc2 := copyIndex_eval d2 (by simpa [d2] using hs 7 (by decide))
  let d3 : ArrayData := ⟨readRegs d2.regs 0 1 none, copyStacks 2 3 d2.stacks⟩
  have hn1 := readProgramAt_eval negativePorts (0 : Fin 2) 1 (by decide)
    beforeN negative restN width index d3.regs d3.stacks
    (by simpa [d3, d2, negativePorts, copyStacks] using hn)
    (by simpa [d3, d2, negativePorts, copyStacks] using hw)
    (by simp [d3, d2, negativePorts, copyStacks, hi, h3]) hin hwn hln
    (by simpa [d3, d2, negativePorts, copyStacks] using hs 7 (by decide))
    (by simpa [d3, d2, negativePorts, copyStacks] using hs 8 (by decide))
    (by simpa [d3, d2, negativePorts, copyStacks] using hs 9 (by decide))
    (by simpa [d3, d2, negativePorts, copyStacks] using hs 10 (by decide))
  have hn2 : Eval (.call (readProgramAt negativePorts 0 1))
      (beforeN.length * (14 * width.length + 10) + 15 * width.length + 16) d3
      ⟨readRegs d.regs 0 1 none, readSignedStacks positive negative d.stacks⟩ := by
    have h3' : d2.stacks 3 = [] := by simpa [d2] using h3
    simpa [d3, after_negative negative d2.stacks h3', d2,
      readRegs_reset, readSignedStacks] using hn1
  have h := hc1.seq (hp2.seq (hc2.seq hn2))
  convert h using 1 ; simp [ hi, d2, ← hip, ← hin] ; ring

/-- Fixed-control primitive transition bound, including the final halt. -/
theorem readSignedProgram_runsIn (d : ArrayData)
    (beforeP beforeN : List (List Bool))
    (positive negative restP restN width index : List Bool)
    (hp : d.stacks 0 = beforeP.flatten ++ (positive ++ restP))
    (hn : d.stacks 1 = beforeN.flatten ++ (negative ++ restN))
    (hi : d.stacks 2 = index) (hw : d.stacks 4 = width)
    (hip : index.length = beforeP.length) (hin : index.length = beforeN.length)
    (hwp : ∀ x ∈ beforeP, x.length = width.length)
    (hwn : ∀ x ∈ beforeN, x.length = width.length)
    (hlp : positive.length = width.length) (hln : negative.length = width.length)
    (h3 : d.stacks 3 = [])
    (hs : ∀ j : Fin 11, 7 ≤ j.val → d.stacks j = []) :
    RunsIn readSignedProgram
      (index.length * (28 * width.length + 34) + 30 * width.length + 43)
      (d.withPC (some readSignedProgram.entry))
      ((⟨readRegs d.regs 0 1 none, readSignedStacks positive negative d.stacks⟩ :
        ArrayData).withPC none) := by
  have h := readSignedCommand_eval d beforeP beforeN positive negative restP restN
    width index hp hn hi hw hip hin hwp hwn hlp hln h3 hs
  refine ⟨_, ?_, compiled_halt_trace h 0 5⟩
  omega

@[simp] theorem readSignedStacks_positive (p n : List Bool)
    (stk : Stacks (Fin 11)) : readSignedStacks p n stk 5 = p ++ stk 5 := by
  simp [readSignedStacks]

@[simp] theorem readSignedStacks_negative (p n : List Bool)
    (stk : Stacks (Fin 11)) : readSignedStacks p n stk 6 = n ++ stk 6 := by
  simp [readSignedStacks]

theorem readSignedStacks_frame (p n : List Bool)
    (stk : Stacks (Fin 11)) (j : Fin 11) (h5 : j ≠ 5) (h6 : j ≠ 6) :
    readSignedStacks p n stk j = stk j := by simp [readSignedStacks, h5, h6]

end SubexponentialSAT.SqrtLog.LayoutProgram

end OAI.Algorithms
