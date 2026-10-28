import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutMatrixProgramPrimitives
import OAI.Algorithms.SubexponentialSAT.SubexpNodeIndexProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.PackingMetadata
import OAI.Algorithms.SubexponentialSAT.Subexp.SeedIndexFormulas

namespace OAI.Algorithms

/-! A fixed twelve-stack workspace for a full pair-key lookup. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

abbrev Data := State 16 12
abbrev Code := Cmd 16 12

def data (regs : Fin 16 → Bool)
    (literal ambient factor master count query field frameTmp scan payload work tmp : List Bool) : Data :=
  ⟨regs,![literal,ambient,factor,master,count,query,field,frameTmp,scan,payload,work,tmp]⟩

def copy (src dst : Fin 12) : Code :=
  .call (StackRoutines.copyProgram src dst 11 (0 : Fin 16) 1)

def push (dst : Fin 12) (bit : Bool) : Code :=
  .seq (.base (.atom (.set 0 bit))) (.base (.atom (.push dst 0)))

theorem push_eval (dst : Fin 12) (bit : Bool) (d : Data) :
    Eval (push dst bit) 2 d
      ⟨Function.update d.regs 0 bit,Function.update d.stacks dst (bit::d.stacks dst)⟩ := by
  have h1 := Eval.base (StructuredProgram.Eval.atom (.set (0 : Fin 16) bit) d)
  have h2 := Eval.base (StructuredProgram.Eval.atom (.push dst 0)
    ((StructuredProgram.Atom.set 0 bit).eval d))
  simpa [push,StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg,StructuredProgram.State.withPC,execInstr] using h1.seq h2

def clear (src : Fin 12) : Code :=
  .call (StackRoutines.clearProgram src (0 : Fin 16) 1)

theorem clear_eval (src : Fin 12) (d : Data) :
    Eval (clear src) (2*(d.stacks src).length+3) d
      ⟨readRegs d.regs 0 1 none,Function.update d.stacks src []⟩ := by
  apply Eval.call
  have h := StackRoutines.clearProgram_trace src (0 : Fin 16) 1 d.regs d.stacks
  have hh := StackRoutines.halt_after_trace _ h 2 rfl rfl
  simpa [clear,StackRoutines.clearResult,StackRoutines.clearStacks,
    StructuredProgram.State.withPC,StackRoutines.clearProgram,Nat.add_assoc] using hh

/-- Exact nested record representation searched in the plan. -/
def pairKey (literal factor : List Bool) : List Bool :=
  Encoding.frame (ProgramEncoding.encodeRecords [literal,factor])

@[simp] theorem pairKey_length (literal factor : List Bool) :
    (pairKey literal factor).length=4*literal.length+4*factor.length+11 := by
  simp [pairKey,ProgramEncoding.encodeRecords,Encoding.encodeList,Encoding.length_frame]
  omega

def buildQuery : Code :=
  .seq (copy 2 6) (.seq (copy 1 6) (.seq (push 5 false)
    (.seq (LayoutMatrixProgram.frame 6 5 7 (by decide)) (.seq (push 5 true)
      (.seq (copy 0 6) (.seq (LayoutMatrixProgram.frame 6 5 7 (by decide))
        (.seq (push 5 true) (LayoutMatrixProgram.frame 5 6 7 (by decide)))))))))

end SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup

end OAI.Algorithms
