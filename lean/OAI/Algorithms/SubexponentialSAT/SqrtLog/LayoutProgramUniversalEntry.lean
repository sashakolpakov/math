import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramGuard
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScanRestore
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramDiagonalTest
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalarFromCountsDefinitions
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramDefect

namespace OAI.Algorithms

/-! Fixed control for one universal integer constraint entry. The concrete
local stages are lifted into one bank; subsequent lemmas compose their traces.
No ring inversion or field-valued matrix is used in this integer procedure. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.UniversalEntry

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp
open SubexponentialSAT.MulticolorTypes

abbrev Data := State 10 64

def guardPorts : Fin 42 → Fin 64 := Fin.castAdd 22
def smallRegs : Fin 8 → Fin 10 := Fin.castAdd 2
def diagonalPorts : Fin 23 → Fin 64 := Fin.castAdd 41
def scalarRegs : Fin 9 → Fin 10 := Fin.castAdd 1
def scalarPorts : Fin 40 → Fin 64 :=
  ![42,43,44,45,46,47,48,2,3,0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,
    27,28,29,30,31,32,33,34,35,50,51,36]
def defectPorts : Fin 10 → Fin 64 := ![50,51,45,53,54,0,1,4,5,6]

abbrev guard : Cmd 10 64 := liftCommand MatrixExtendedEntryProgram.guardStage 23 0 id guardPorts
abbrev diagonal : Cmd 10 64 := liftCommand DiagonalTest.command 0 0 smallRegs diagonalPorts
abbrev saveDiagonal : Cmd 10 64 := .base (.atom (.push 49 6))
abbrev scalar : Cmd 10 64 := .call (ProgramLinking.liftProgram
  LayoutProgramScalar.FromCounts.program scalarRegs scalarPorts)
abbrev loadDiagonal : Cmd 10 64 := .base (.atom (.pop 49 7 8))
abbrev defect : Cmd 10 64 := liftCommand Defect.command 0 3 smallRegs defectPorts
abbrev clear (src : Fin 64) : Cmd 10 64 := .call (StackRoutines.clearProgram src 0 1)
abbrev clearNumerator : Cmd 10 64 := .seq (clear 50) (clear 51)
abbrev clearCounts : Cmd 10 64 := .seq (clear 2) (clear 3)
abbrev success : Cmd 10 64 := .seq diagonal (.seq saveDiagonal (.seq scalar
  (.seq loadDiagonal (.seq defect clearNumerator))))
abbrev guarded : Cmd 10 64 := .seq ScanRestore.command (.ite 7 success clearCounts)
abbrev command : Cmd 10 64 := .seq guard (.ite 9 guarded (.base .skip))
def program := compiled command 23 53

theorem guardPorts_inj : Function.Injective guardPorts := Fin.castAdd_injective _ _
theorem smallRegs_inj : Function.Injective smallRegs := Fin.castAdd_injective _ _
theorem diagonalPorts_inj : Function.Injective diagonalPorts := Fin.castAdd_injective _ _
theorem scalarRegs_inj : Function.Injective scalarRegs := Fin.castAdd_injective _ _
theorem scalarPorts_inj : Function.Injective scalarPorts := by decide
theorem defectPorts_inj : Function.Injective defectPorts := by decide

variable {r Q : ℕ}

theorem guard_eval (t : Fin Q) (u y : UniversalType r Q 1) (a : Data)
    (ha : projectState id guardPorts a = Guard.guardInput (0 : Fin 1) t u y
      [] [] [] [] a.regs) :
    ∃ n ≤ MatrixExtendedEntryProgram.guardStageCost r Q 1 0 t.val+1,
      ∃ e : Data, Eval guard n a e ∧ e.stacks=a.stacks ∧
      e.regs 9=decide (MatrixExtendedEntryProgram.anchorValid (0 : Fin 1) t u y) := by
  obtain ⟨n,hn,b,hb,hs,hflag⟩ := Guard.guardStage_eval (0 : Fin 1) t u y [] [] [] [] a.regs
  rw [← ha] at hb
  let e := embedState id guardPorts a b
  have he := eval_liftCommand_from_state MatrixExtendedEntryProgram.guardStage 23 0 id guardPorts a
    Function.injective_id guardPorts_inj hb
  have hstacks : e.stacks=a.stacks := by
    change Function.extend guardPorts b.stacks a.stacks = a.stacks
    rw [hs]
    have hh := congrArg StructuredProgram.State.stacks
      (embedState_project id guardPorts a Function.injective_id guardPorts_inj)
    rw [ha] at hh
    exact hh
  have h9 : e.regs 9 = b.regs 9 :=
    embedState_register id guardPorts a b Function.injective_id 9
  have hn' : n ≤ MatrixExtendedEntryProgram.guardStageCost r Q 1 0 t.val := by simpa using hn
  exact ⟨n+1,by omega,e,he,hstacks,h9.trans hflag⟩

theorem diagonal_eval (a : Data) :
    ∃ n ≤ 6, ∃ e : Data, Eval diagonal n a e ∧ e.stacks=a.stacks ∧
      e.regs 6=(a.regs 7 && (a.stacks 3).isEmpty) ∧ e.regs 7=a.regs 7 := by
  let projected :=  projectState smallRegs diagonalPorts a
  obtain ⟨n,hn,b,hb,hs,h6,h7⟩ := DiagonalTest.command_eval projected
  let e := embedState smallRegs diagonalPorts a b
  have he := eval_liftCommand_from_state DiagonalTest.command 0 0 smallRegs diagonalPorts a
    smallRegs_inj diagonalPorts_inj hb
  have hstacks : e.stacks=a.stacks := by
    change Function.extend diagonalPorts b.stacks a.stacks=a.stacks
    rw [hs]
    exact congrArg StructuredProgram.State.stacks
      (embedState_project smallRegs diagonalPorts a smallRegs_inj diagonalPorts_inj)
  have he6 : e.regs 6=b.regs 6 :=
    embedState_register smallRegs diagonalPorts a b smallRegs_inj 6
  have he7 : e.regs 7=b.regs 7 :=
    embedState_register smallRegs diagonalPorts a b smallRegs_inj 7
  refine ⟨n+1,by omega,e,he,hstacks,?_,?_⟩
  · simpa [projected,diagonalFromScan,projectState,smallRegs,diagonalPorts] using he6.trans h6
  · simpa [projected,projectState,smallRegs] using he7.trans h7

end SubexponentialSAT.SqrtLog.LayoutProgram.UniversalEntry

end OAI.Algorithms
