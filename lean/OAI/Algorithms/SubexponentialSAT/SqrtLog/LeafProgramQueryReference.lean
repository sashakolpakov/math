import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryCleanup
import OAI.Algorithms.SubexponentialSAT.SubexpParameterProgram

namespace OAI.Algorithms

/-! The marked collector supplies a reversed reference payload on321. The
query itself pays to copy and reverse that reference into the frontend's
forward index slot705. The original payload survives until the branch exit. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Query
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

def markedFlag : Code := .base (SubexpParameterProgram.atoms [.set 0 true,.push 706 0])
def flagged (a : Data) : Data :=
  SubexpParameterProgram.runAtoms [.set 0 true,.push 706 0] a

theorem markedFlag_eval (a : Data) : Eval markedFlag 2 a (flagged a) :=
  .base (SubexpParameterProgram.atoms_eval _ a)

def markInput : Code := .seq (.call (StackRoutines.copyProgram 321 699 698 0 1))
  (.seq (.call (StackRoutines.transferProgram 699 705 0 1)) markedFlag)

def markedInput (a : Data) : Data :=
  flagged (afterTransfer (afterCopy a 321 699 0 1) 699 705 0 1)

theorem markInput_eval (a : Data) (h698 : a.stacks 698=[]) (h699 : a.stacks 699=[]) :
    Eval markInput (10*(a.stacks 321).length+10) a (markedInput a) := by
  have hc := copy_eval a 321 699 698 0 1 (by decide) (by decide) (by decide) (by decide) h698
  have ht := transfer_eval (afterCopy a 321 699 0 1) 699 705 0 1 (by decide) (by decide)
  have hf := markedFlag_eval (afterTransfer (afterCopy a 321 699 0 1) 699 705 0 1)
  have hl : ((afterCopy a 321 699 0 1).stacks 699).length=(a.stacks 321).length := by
    simp [afterCopy,StackRoutines.copyStacks,h699]
  rw [hl] at ht
  convert hc.seq (ht.seq hf) using 1 <;> first | rfl | omega

theorem markedInput_index (a : Data) (h699 : a.stacks 699=[]) (h705 : a.stacks 705=[]) :
    (markedInput a).stacks 705=(a.stacks 321).reverse := by
  simp [markedInput,flagged,SubexpParameterProgram.runAtoms,StructuredProgram.Atom.eval,
    StructuredProgram.Atom.instr,BitProgram.execInstr,
    StructuredProgram.State.ofCfg,afterTransfer,afterCopy,
    StackRoutines.transferStacks,StackRoutines.copyStacks,h699,h705]

theorem markedInput_flag (a : Data) (h706 : a.stacks 706=[]) :
    (markedInput a).stacks 706=[true] := by
  simp [markedInput,flagged,SubexpParameterProgram.runAtoms,StructuredProgram.Atom.eval,
    StructuredProgram.Atom.instr,BitProgram.execInstr,
    StructuredProgram.State.ofCfg,afterTransfer,afterCopy,
    StackRoutines.transferStacks,StackRoutines.copyStacks,h706]

theorem markedInput_frame (a : Data) (i : Fin 768)
    (hi : i≠699) (h705 : i≠705) (h706 : i≠706) :
    (markedInput a).stacks i=a.stacks i := by
  simp [markedInput,flagged,SubexpParameterProgram.runAtoms,StructuredProgram.Atom.eval,
    StructuredProgram.Atom.instr,BitProgram.execInstr,
    StructuredProgram.State.ofCfg,afterTransfer,afterCopy,
    StackRoutines.transferStacks,StackRoutines.copyStacks,hi,h705,h706]

theorem markedInput_temporary (a : Data) : (markedInput a).stacks 699=[] := by
  simp [markedInput,flagged,SubexpParameterProgram.runAtoms,StructuredProgram.Atom.eval,
    StructuredProgram.Atom.instr,BitProgram.execInstr,
    StructuredProgram.State.ofCfg,afterTransfer,afterCopy,
    StackRoutines.transferStacks]

theorem markedInput_register_frame (a : Data) (i : Fin 40) (hi : 2 ≤ i.val) :
    (markedInput a).regs i=a.regs i := by
  have h0 : i≠0 := by intro h; subst i; simp at hi
  have h1 : i≠1 := by intro h; subst i; simp at hi
  simp [markedInput,flagged,SubexpParameterProgram.runAtoms,StructuredProgram.Atom.eval,
    StructuredProgram.Atom.instr,BitProgram.execInstr,
    StructuredProgram.State.ofCfg,afterTransfer,afterCopy,
    readRegs,h0,h1]

def noMarkInput : Code :=
  .base (SubexpParameterProgram.atoms [.set 0 false,.push 705 0,.push 706 0])
def unmarkedInput (a : Data) : Data :=
  SubexpParameterProgram.runAtoms [.set 0 false,.push 705 0,.push 706 0] a

theorem noMarkInput_eval (a : Data) : Eval noMarkInput 3 a (unmarkedInput a) :=
  .base (SubexpParameterProgram.atoms_eval _ a)

theorem unmarkedInput_index (a : Data) (h705 : a.stacks 705=[]) :
    (unmarkedInput a).stacks 705=[false] := by
  simp [unmarkedInput,SubexpParameterProgram.runAtoms,StructuredProgram.Atom.eval,
    StructuredProgram.Atom.instr,BitProgram.execInstr,
    StructuredProgram.State.ofCfg,h705]

theorem unmarkedInput_flag (a : Data) (h706 : a.stacks 706=[]) :
    (unmarkedInput a).stacks 706=[false] := by
  simp [unmarkedInput,SubexpParameterProgram.runAtoms,StructuredProgram.Atom.eval,
    StructuredProgram.Atom.instr,BitProgram.execInstr,
    StructuredProgram.State.ofCfg,h706]

theorem unmarkedInput_frame (a : Data) (i : Fin 768) (h705 : i≠705) (h706 : i≠706) :
    (unmarkedInput a).stacks i=a.stacks i := by
  simp [unmarkedInput,SubexpParameterProgram.runAtoms,StructuredProgram.Atom.eval,
    StructuredProgram.Atom.instr,BitProgram.execInstr,
    StructuredProgram.State.ofCfg,h705,h706]

end SubexponentialSAT.SqrtLog.LeafProgram.Query

end OAI.Algorithms
