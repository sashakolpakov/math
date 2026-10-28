import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgramEntriesEmit
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames

namespace OAI.Algorithms

/-! Preserving signed-pair emission into a reverse buffer. The existing exact
pair serializer is called on paid copies, and its output is transferred once.
All source words survive; the four work stacks are restored to empty. -/
namespace SubexponentialSAT.SqrtLog.LayoutScalarEmitter
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.Subexp.MatrixProgramSupport

abbrev Data := State 8 7
abbrev Code := Cmd 8 7

def pairRegisters : Fin 3 → Fin 8 := Fin.castAdd 5
def pairPorts : Fin 6 → Fin 7 := ![3,4,6,0,1,2]

theorem pairRegisters_injective : Function.Injective pairRegisters := Fin.castAdd_injective _ _
theorem pairPorts_injective : Function.Injective pairPorts := by decide

def pairCall : Code := liftCommand RowSelectionProgram.Entries.emitPair 0 2 pairRegisters pairPorts

def record (positive negative : List Bool) : List Bool :=
  RowSelectionProgram.Entries.pairPrefix positive negative

@[simp] theorem record_length (positive negative : List Bool) :
    (record positive negative).length = 2*(positive.length+negative.length)+3 := by
  simp [record,RowSelectionProgram.Entries.pairPrefix]
  omega

theorem pairCall_eval (d : Data) :
    ∃ e, Eval pairCall (5*((d.stacks 3).length+(d.stacks 4).length)+16) d e ∧
      e.stacks = Function.update (Function.update (Function.update d.stacks 3 []) 4 []) 6
        (record (d.stacks 3) (d.stacks 4) ++ d.stacks 6) := by
  let a := projectState pairRegisters pairPorts d
  obtain ⟨b,hb,hsb⟩ := RowSelectionProgram.Entries.emitPair_eval a
  let e := embedState pairRegisters pairPorts d b
  have he := eval_liftCommand_from_state RowSelectionProgram.Entries.emitPair 0 2
    pairRegisters pairPorts d pairRegisters_injective pairPorts_injective hb
  refine ⟨e,?_,?_⟩
  · simpa [e, pairCall, a, projectState, pairPorts, Nat.add_assoc] using he
  · change Function.extend pairPorts b.stacks d.stacks = _
    rw [hsb,ProgramLinking.extend_update pairPorts_injective,
      ProgramLinking.extend_update pairPorts_injective,
      ProgramLinking.extend_update pairPorts_injective]
    have hbase := congrArg StructuredProgram.State.stacks
      (embedState_project pairRegisters pairPorts d pairRegisters_injective pairPorts_injective)
    change Function.extend pairPorts a.stacks d.stacks = d.stacks at hbase
    rw [hbase]
    rfl

/-- P0,N1 survive. Buffer2 is extended. Scratch3--6 starts and ends empty. -/
def emitPair : Code :=
  .seq (copy 0 3 5) (.seq (copy 1 4 5) (.seq pairCall (transfer 6 2)))

def Ready (d : Data) : Prop :=
  d.stacks 3 = [] ∧ d.stacks 4 = [] ∧ d.stacks 5 = [] ∧ d.stacks 6 = []

theorem emitPair_eval (d : Data) (hready : Ready d) :
    ∃ e, Eval emitPair (18*((d.stacks 0).length+(d.stacks 1).length)+38) d e ∧
      e.stacks = Function.update d.stacks 2
        ((record (d.stacks 0) (d.stacks 1)).reverse ++ d.stacks 2) := by
  obtain ⟨h3,h4,h5,h6⟩ := hready
  obtain ⟨a,ha,hsa⟩ := copy_eval (0 : Fin 7) 3 5
    (by decide) (by decide) (by decide) d h5
  obtain ⟨b,hb,hsb⟩ := copy_eval (1 : Fin 7) 4 5
    (by decide) (by decide) (by decide) a (by simp [hsa,StackRoutines.copyStacks,h5])
  obtain ⟨c,hc,hsc⟩ := pairCall_eval b
  obtain ⟨e,he,hse⟩ := transfer_eval (6 : Fin 7) 2 (by decide) c
  have ha1 : a.stacks 1 = d.stacks 1 := by simp [hsa,StackRoutines.copyStacks]
  have hb3 : b.stacks 3 = d.stacks 0 := by simp [hsb,hsa,StackRoutines.copyStacks,h3]
  have hb4 : b.stacks 4 = d.stacks 1 := by simp [hsb,hsa,StackRoutines.copyStacks,h4]
  have hb6 : b.stacks 6 = [] := by simp [hsb,hsa,StackRoutines.copyStacks,h6]
  have hc6 : c.stacks 6 = record (d.stacks 0) (d.stacks 1) := by simp [hsc,hb3,hb4,hb6]
  have hall := ha.seq (hb.seq (hc.seq he))
  rw [ha1,hb3,hb4,hc6,record_length] at hall
  have ht : (7*(d.stacks 0).length+5)+((7*(d.stacks 1).length+5)+
      ((5*((d.stacks 0).length+(d.stacks 1).length)+16)+
        (3*(2*((d.stacks 0).length+(d.stacks 1).length)+3)+3))) =
      18*((d.stacks 0).length+(d.stacks 1).length)+38 := by omega
  rw [ht] at hall
  refine ⟨e,hall,?_⟩
  rw [hse,hsc,hsb,hsa]
  funext i; fin_cases i <;>
    simp [StackRoutines.transferStacks,StackRoutines.copyStacks,h3,h4,h5,h6]

def emitPairProgram := compiled emitPair 0 2

theorem emitPair_trace (d : Data) (hready : Ready d) :
    ∃ e : Data, Trace emitPairProgram (18*((d.stacks 0).length+(d.stacks 1).length)+39)
      (d.withPC (some emitPairProgram.entry)) (e.withPC none) ∧
      e.stacks = Function.update d.stacks 2
        ((record (d.stacks 0) (d.stacks 1)).reverse ++ d.stacks 2) := by
  obtain ⟨e,he,hs⟩ := emitPair_eval d hready
  exact ⟨e,by simpa [emitPairProgram,Nat.add_assoc] using compiled_halt_trace he 0 2,hs⟩

/-- Append the final false tag, then reverse the complete accumulated list. -/
def finishList : Code :=
  .seq (.base (.atom (.set 0 false)))
    (.seq (.base (.atom (.push 2 0))) (transfer 2 6))

def finishListProgram := compiled finishList 2 6

theorem finishList_eval (d : Data) (h6 : d.stacks 6 = []) :
    ∃ e, Eval finishList (3*(d.stacks 2).length+8) d e ∧
      e.stacks = Function.update (Function.update d.stacks 2 []) 6
        ((d.stacks 2).reverse ++ [false]) := by
  let a := (StructuredProgram.Atom.set (0 : Fin 8) false).eval d
  let b := (StructuredProgram.Atom.push (2 : Fin 7) (0 : Fin 8)).eval a
  have ha : Eval (.base (.atom (.set 0 false))) 1 d a := .base (.atom _ _)
  have hb : Eval (.base (.atom (.push 2 0))) 1 a b := .base (.atom _ _)
  obtain ⟨e,he,hse⟩ := transfer_eval (2 : Fin 7) 6 (by decide) b
  have hbs : b.stacks = Function.update d.stacks 2 (false :: d.stacks 2) := by
    simp [b,a,StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg,execInstr]
  have hall := ha.seq (hb.seq he)
  have hb2 : (b.stacks 2).length = (d.stacks 2).length+1 := by simp [hbs]
  rw [hb2] at hall
  have ht : 1+(1+(3*((d.stacks 2).length+1)+3)) = 3*(d.stacks 2).length+8 := by omega
  rw [ht] at hall
  refine ⟨e,hall,?_⟩
  rw [hse,hbs]
  funext i; fin_cases i <;> simp [StackRoutines.transferStacks,h6,List.reverse_cons]

theorem finishList_trace (d : Data) (h6 : d.stacks 6 = []) :
    ∃ e : Data, Trace finishListProgram (3*(d.stacks 2).length+9)
      (d.withPC (some finishListProgram.entry)) (e.withPC none) ∧
      e.stacks = Function.update (Function.update d.stacks 2 []) 6
        ((d.stacks 2).reverse ++ [false]) := by
  obtain ⟨e,he,hs⟩ := finishList_eval d h6
  exact ⟨e,by simpa [finishListProgram,Nat.add_assoc] using compiled_halt_trace he 2 6,hs⟩

end SubexponentialSAT.SqrtLog.LayoutScalarEmitter

end OAI.Algorithms
