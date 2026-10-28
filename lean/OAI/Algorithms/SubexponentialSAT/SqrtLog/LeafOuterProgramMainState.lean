import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ExecutionLeafBounded
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ExecutionLeaf

namespace OAI.Algorithms

/-! Physical record-loop state for the complete wide leaf.  Only the current
leaf, its two immutable metadata words, and blank reusable work are needed. -/
namespace SubexponentialSAT.SqrtLog.LeafOuterProgram.MainAdapter
open SubexponentialSAT BitProgram StructuredCalls SubexpMainProgram Execution

abbrev Data (c : SubexponentialSAT.SubexpSetupProgram.Config) := MainState finalExtraRegisters (SubexponentialSAT.SubexpSetupProgram.mainExtraStacks c)

structure Invariant (c : SubexponentialSAT.SubexpSetupProgram.Config) (hc : 896 < SubexponentialSAT.SubexpSetupProgram.helperSize c)
    (nw Bw : List Bool) (a : Data c) : Prop where
  work : ∀ i, a.stacks (WideLeaf.stack c hc i)=[]
  leaf : a.stacks (persistent (SubexponentialSAT.SubexpSetupProgram.mainExtraStacks c) 9)=[]
  answer : a.stacks (persistent (SubexponentialSAT.SubexpSetupProgram.mainExtraStacks c) 10)=[]
  ambient : a.stacks (persistent (SubexponentialSAT.SubexpSetupProgram.mainExtraStacks c) 2)=nw
  occurrence : a.stacks (persistent (SubexponentialSAT.SubexpSetupProgram.mainExtraStacks c) 24)=Bw

def CoreInput (a : State 40 896) (bits nw Bw : List Bool) : Prop :=
  ∀ i, a.stacks i = if i=784 then bits else if i=785 then nw else if i=786 then Bw else []

abbrev CoreContract (core : Cmd 40 896) (test : List Bool → Bool)
    (cost : List Bool → ℕ) (valid : List Bool → Prop) (nw Bw : List Bool) : Prop :=
  ∀ bits, valid bits → ∀ a, CoreInput a bits nw Bw →
    ∃ t ≤ cost bits, ∃ b, Eval core t a b ∧ b.stacks 787=[test bits]

theorem input_stack_frame {er es : ℕ} (a : MainState er es) (tail bits : List Bool)
    (i : Fin (totalStacks es)) (h7 : i≠persistent es 7) (h8 : i≠persistent es 8) :
    (leafInput a tail bits).stacks i=a.stacks i := by
  simp [leafInput,RecordPrograms.state,ports,h7,h8]

theorem transferred_stack_frame {er es : ℕ} (a : MainState er es)
    (i : Fin (totalStacks es)) (h8 : i≠persistent es 8) (h9 : i≠persistent es 9) :
    (transferredData a).stacks i=a.stacks i := by
  simp [transferredData,StackRoutines.transferStacks,h8,h9]

theorem finished_stack_frame {er es : ℕ} (a : MainState er es)
    (i : Fin (totalStacks es)) (h9 : i≠persistent es 9) (h10 : i≠persistent es 10) :
    (finishedData a).stacks i=a.stacks i := by
  simp [finishedData,poppedAnswer,clearedData,StackRoutines.clearStacks,
    StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
StructuredProgram.State.ofCfg,execInstr,h9,h10]

theorem transfer_cost {er es : ℕ} (a : MainState er es) (tail bits : List Bool) :
    transferCost (leafInput a tail bits)=3*bits.length+3 := by
  simp [transferCost,leafInput,RecordPrograms.state,ports]

theorem finish_cost {er es : ℕ} (a : MainState er es) (bits : List Bool) (bit : Bool)
    (h9 : a.stacks (persistent es 9)=bits) (h10 : a.stacks (persistent es 10)=[bit]) :
    finishCost a=2*bits.length+9 := by
  simp [finishCost,clearCost,poppedAnswer,clearedData,StackRoutines.clearStacks,
    StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
StructuredProgram.State.ofCfg,execInstr,h9,h10]
  omega

theorem prepared_input (c : SubexponentialSAT.SubexpSetupProgram.Config) (hc : 896 < SubexponentialSAT.SubexpSetupProgram.helperSize c) (core : Cmd 40 896)
    (a : Data c) (bits nw Bw : List Bool) (hready : LeafMain.Ready c hc core a)
    (h9 : a.stacks (persistent (SubexponentialSAT.SubexpSetupProgram.mainExtraStacks c) 9)=bits)
    (h2 : a.stacks (persistent (SubexponentialSAT.SubexpSetupProgram.mainExtraStacks c) 2)=nw)
    (h24 : a.stacks (persistent (SubexponentialSAT.SubexpSetupProgram.mainExtraStacks c) 24)=Bw) :
    CoreInput (projectState id LeafIO.work
      (LeafIO.prepared ((LeafMain.procedure c hc core).project a))) bits nw Bw := by
  intro i
  have hi := LeafIO.prepared_work ((LeafMain.procedure c hc core).project a) hready i
  change (LeafIO.prepared ((LeafMain.procedure c hc core).project a)).stacks (LeafIO.work i)=_
  rw [hi]
  have h784 : i.val=784 ↔ i=(784 : Fin 896) := ⟨fun h => Fin.ext h,fun h => congrArg Fin.val h⟩
  have h785 : i.val=785 ↔ i=(785 : Fin 896) := ⟨fun h => Fin.ext h,fun h => congrArg Fin.val h⟩
  have h786 : i.val=786 ↔ i=(786 : Fin 896) := ⟨fun h => Fin.ext h,fun h => congrArg Fin.val h⟩
  change (if i.val=784 then a.stacks (persistent (SubexponentialSAT.SubexpSetupProgram.mainExtraStacks c) 9) else
    if i.val=785 then a.stacks (persistent (SubexponentialSAT.SubexpSetupProgram.mainExtraStacks c) 2) else
    if i.val=786 then a.stacks (persistent (SubexponentialSAT.SubexpSetupProgram.mainExtraStacks c) 24) else [])=_
  simp only [h9,h2,h24,h784,h785,h786]

theorem project_wordBound (c : SubexponentialSAT.SubexpSetupProgram.Config) (hc : 896 < SubexponentialSAT.SubexpSetupProgram.helperSize c) (core : Cmd 40 896)
    (a : Data c) (bits nw Bw : List Bool) (hready : LeafMain.Ready c hc core a)
    (h9 : a.stacks (persistent (SubexponentialSAT.SubexpSetupProgram.mainExtraStacks c) 9)=bits)
    (h2 : a.stacks (persistent (SubexponentialSAT.SubexpSetupProgram.mainExtraStacks c) 2)=nw)
    (h24 : a.stacks (persistent (SubexponentialSAT.SubexpSetupProgram.mainExtraStacks c) 24)=Bw) :
    SubexpSetupStorage.WordBound (bits.length+nw.length+Bw.length+1)
      ((LeafMain.procedure c hc core).project a) := by
  intro i
  refine Fin.addCases (m:=896) (n:=4) (fun j => ?_) (fun j => ?_) i
  · have h := hready.1 (j.castAdd 4) j.isLt
    rw [h]
    simp
  · fin_cases j
    · change (a.stacks (persistent (SubexponentialSAT.SubexpSetupProgram.mainExtraStacks c) 9)).length ≤ _
      rw [h9]; omega
    · change (a.stacks (persistent (SubexponentialSAT.SubexpSetupProgram.mainExtraStacks c) 2)).length ≤ _
      rw [h2]; omega
    · change (a.stacks (persistent (SubexponentialSAT.SubexpSetupProgram.mainExtraStacks c) 24)).length ≤ _
      rw [h24]; omega
    · change (((LeafMain.procedure c hc core).project a).stacks (899 : Fin 900)).length ≤ _
      rw [hready.2]; simp

end SubexponentialSAT.SqrtLog.LeafOuterProgram.MainAdapter

end OAI.Algorithms
