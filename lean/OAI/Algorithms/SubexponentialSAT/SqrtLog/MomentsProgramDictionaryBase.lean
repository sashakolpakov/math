import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SquarefreeProgramSemantics
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingScanAddLoop

namespace OAI.Algorithms

/-! Fixed physical dictionary-insertion program. All dictionary/key/vector
lengths are input data. The complete semantic composition is proved separately;
this file defines the finite table and its paid stack primitives. -/
namespace SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

abbrev Data := State 8 27

abbrev copy (src dst tmp : Fin 27) : Cmd 8 27 :=
  .call (copyProgram src dst tmp (0 : Fin 8) 1)
abbrev transfer (src dst : Fin 27) : Cmd 8 27 :=
  .call (transferProgram src dst (0 : Fin 8) 1)
abbrev clear (src : Fin 27) : Cmd 8 27 :=
  .call (clearProgram src (0 : Fin 8) 1)

def copied (d : Data) (src dst : Fin 27) : Data :=
  ⟨readRegs d.regs 0 1 none, copyStacks src dst d.stacks⟩
def transferred (d : Data) (src dst : Fin 27) : Data :=
  ⟨readRegs d.regs 0 1 none, transferStacks src dst d.stacks⟩
def cleared (d : Data) (src : Fin 27) : Data :=
  ⟨readRegs d.regs 0 1 none, clearStacks src d.stacks⟩

theorem copy_eval (d : Data) (src dst tmp : Fin 27)
    (hsd : src ≠ dst) (hst : src ≠ tmp) (htd : tmp ≠ dst) (htmp : d.stacks tmp = []) :
    Eval (copy src dst tmp) (7 * (d.stacks src).length + 5) d (copied d src dst) := by
  apply Eval.call
  have h := copyProgram_trace src dst tmp (0 : Fin 8) 1 hsd hst htd (by decide)
    d.regs d.stacks htmp
  have hh := halt_after_trace _ h 7 rfl rfl
  simpa [copy, copied, copyResult, StructuredProgram.State.withPC, copyProgram,
    Nat.add_assoc] using hh

theorem transfer_eval (d : Data) (src dst : Fin 27) (hsd : src ≠ dst) :
    Eval (transfer src dst) (3 * (d.stacks src).length + 3) d (transferred d src dst) := by
  apply Eval.call
  have h := transferProgram_trace src dst (0 : Fin 8) 1 hsd (by decide) d.regs d.stacks
  have hh := halt_after_trace _ h 3 rfl rfl
  simpa [transfer, transferred, transferResult, StructuredProgram.State.withPC,
    transferProgram, Nat.add_assoc] using hh

theorem clear_eval (d : Data) (src : Fin 27) :
    Eval (clear src) (2 * (d.stacks src).length + 3) d (cleared d src) := by
  apply Eval.call
  have h := clearProgram_trace src (0 : Fin 8) 1 d.regs d.stacks
  have hh := halt_after_trace _ h 2 rfl rfl
  simpa [clear, cleared, clearResult, StructuredProgram.State.withPC,
    clearProgram, Nat.add_assoc] using hh

def smallRegs : Fin 5 → Fin 8 := Fin.castAdd 3
def lookupStacks : Fin 6 → Fin 27 := ![18,19,16,20,21,22]
def replaceStacks : Fin 8 → Fin 27 := ![15,19,16,20,21,25,18,26]
def nativeStacks : Fin 15 → Fin 27 := Fin.castAdd 12

theorem smallRegs_injective : Function.Injective smallRegs := Fin.castAdd_injective _ _
theorem lookupStacks_injective : Function.Injective lookupStacks := by decide
theorem replaceStacks_injective : Function.Injective replaceStacks := by decide
theorem nativeStacks_injective : Function.Injective nativeStacks := Fin.castAdd_injective _ _

abbrev lookup : Cmd 8 27 := .call
  (ProgramLinking.liftProgram Squarefree.Program.dictionaryLookupProgram smallRegs lookupStacks)
abbrev replace : Cmd 8 27 := .call
  (ProgramLinking.liftProgram Squarefree.Program.dictionaryReplaceProgram smallRegs replaceStacks)
abbrev add : Cmd 8 27 := .call
  (ProgramLinking.liftProgram RingScan.addVectorProgram id nativeStacks)

/-- The parser's destination is reversed; transferring it to native stack9
restores the old coefficient vector to forward order before addition. -/
def parseRegisters : Fin 5 → Fin 8 := smallRegs
def parseStacks : Fin 6 → Fin 27 := ![22,8,19,20,21,23]
abbrev parseOld : Cmd 8 27 := .call
  (ProgramLinking.liftProgram (SubexponentialSAT.SubexpRecordScan.parseFrame 0 1) parseRegisters parseStacks)

abbrev onHit : Cmd 8 27 :=
  .seq parseOld (.seq (transfer 8 9)
    (.seq (copy 17 8 23) (.seq (copy 24 11 23) add)))
abbrev onMiss : Cmd 8 27 := copy 17 0 23

/-- Dictionary15, query.reverse16, new coefficient17, modulus5, coefficient
width12, extension dimension24 are inputs. Result dictionary15 replaces the
old value by new+old, once the local semantic composition is discharged. -/
abbrev insert : Cmd 8 27 :=
  .seq (copy 15 18 23)
    (.seq lookup
      (.seq (.ite 4 onHit onMiss)
        (.seq (clear 18)
          (.seq (transfer 0 26)
            (.seq replace (.seq (copy 25 15 23) (clear 25)))))))

def insertProgram := compiled insert 15 15

end SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary

end OAI.Algorithms
