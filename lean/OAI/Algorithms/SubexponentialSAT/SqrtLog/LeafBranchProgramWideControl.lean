import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafBranchProgramRun
import OAI.Algorithms.SubexponentialSAT.ListRegisterProgram

namespace OAI.Algorithms

/-! Native setup and cleanup for the full branch query in the collector's
fixed register layout. No branch bound or answer list is supplied as code. -/
namespace SubexponentialSAT.SqrtLog.LeafBranchProgram.Wide
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
abbrev Data := State 40 768
abbrev Code := Cmd 40 768

/-- Wide ambient state for residual ring/layout setup; branch ports are unchanged. -/
def fixedPorts : Ports 40 768 where
  counter := {
    register := ⟨fun i => ⟨19 + i.val, by omega⟩, by intro i j h; apply Fin.ext; simpa using congrArg Fin.val h⟩
    counter := 330
    scratch := 331
    counter_ne_scratch := by decide }
  mass := {
    register := fun i => i.castAdd 32
    stack := ![332,323,324]
    register_injective := Fin.castAdd_injective 8 32
    stack_injective := by decide }
  disjoint_counter := by decide
  disjoint_scratch := by decide

def initReg (i : Fin 2) : Fin 40 := i.castAdd 38
def initStack : Fin 2 → Fin 768 := ![333,330]
theorem initReg_injective : Function.Injective initReg := Fin.castAdd_injective 2 38
theorem initStack_injective : Function.Injective initStack := by decide

def initCommand : Code := .call (ProgramLinking.liftProgram
  HighIncidenceProgram.Branches.program initReg initStack)
noncomputable def initialized (a : Data) (regs : Fin 2 → Bool) (mask : List Bool) : Data :=
  embedState initReg initStack a (HighIncidenceProgram.Branches.state regs []
    (Encoding.encodeList id (List.replicate (HighIncidenceProgram.Branches.trueCount mask) [false])))

theorem init_self (a : Data) (he : a.stacks 330 = []) :
    embedState initReg initStack a (HighIncidenceProgram.Branches.state
      (fun i => a.regs (initReg i)) (a.stacks 333) []) = a := by
  apply congrArg₂ StructuredProgram.State.mk
  · funext i
    by_cases h : ∃ j, initReg j = i
    · obtain ⟨j,rfl⟩ := h
      exact embedState_register initReg initStack a
        (HighIncidenceProgram.Branches.state (fun i => a.regs (initReg i)) (a.stacks 333) [])
        initReg_injective j
    · exact embedState_register_frame initReg initStack a
        (HighIncidenceProgram.Branches.state (fun i => a.regs (initReg i)) (a.stacks 333) []) i h
  · funext i
    by_cases h : ∃ j, initStack j = i
    · obtain ⟨j,rfl⟩ := h
      calc
        _ = (HighIncidenceProgram.Branches.state (fun i => a.regs (initReg i))
          (a.stacks 333) []).stacks j := embedState_stack initReg initStack a _ initStack_injective j
        _ = _ := by fin_cases j <;> simp [initStack,HighIncidenceProgram.Branches.state,he]
    · exact embedState_stack_frame initReg initStack a
        (HighIncidenceProgram.Branches.state (fun i => a.regs (initReg i)) (a.stacks 333) []) i h

theorem initialize_eval (a : Data) (he : a.stacks 330 = []) :
    ∃ n regs, n ≤ 11*(a.stacks 333).length+5 ∧
      Eval initCommand n a (initialized a regs (a.stacks 333)) := by
  obtain ⟨regs,n,hn,ht⟩ := HighIncidenceProgram.Branches.program_runsIn
    (fun i => a.regs (initReg i)) (a.stacks 333)
  have hh := eval_call_lifted HighIncidenceProgram.Branches.program initReg initStack a
    initReg_injective initStack_injective ht
  rw [init_self a he] at hh
  exact ⟨n,regs,hn,hh⟩

theorem initialized_counter (a : Data) (regs : Fin 2 → Bool) (mask : List Bool) :
    (initialized a regs mask).stacks 330 =
      Encoding.encodeList id (List.replicate (HighIncidenceProgram.Branches.trueCount mask) [false]) :=
  embedState_stack _ _ _ _ initStack_injective 1

theorem initialized_mask (a : Data) (regs : Fin 2 → Bool) (mask : List Bool) :
    (initialized a regs mask).stacks 333 = [] :=
  embedState_stack _ _ _ _ initStack_injective 0

theorem initialized_frame (a : Data) (regs : Fin 2 → Bool) (mask : List Bool)
    (i : Fin 768) (h1 : i ≠ 330) (h2 : i ≠ 333) :
    (initialized a regs mask).stacks i = a.stacks i := by
  apply embedState_stack_frame
  rintro ⟨j,hj⟩
  fin_cases j <;> simp [initStack] at hj
  · exact h2 hj.symm
  · exact h1 hj.symm

def cleared (j : Fin 768) (a : Data) : Data :=
  ⟨readRegs a.regs 0 1 none, StackRoutines.clearStacks j a.stacks⟩
theorem clear_eval (j : Fin 768) (a : Data) :
    Eval (.call (StackRoutines.clearProgram j 0 1)) (2*(a.stacks j).length+3) a (cleared j a) :=
  Eval.call _ (ListRegisterProgram.clear_run j 0 1 a.regs a.stacks)

def move : Code :=
  .seq (.call (StackRoutines.transferProgram 332 324 0 1))
    (.call (StackRoutines.transferProgram 324 323 0 1))
def moved (a : Data) : Data :=
  ⟨readRegs a.regs 0 1 none,
    StackRoutines.transferStacks 324 323 (StackRoutines.transferStacks 332 324 a.stacks)⟩
theorem move_eval (a : Data) (hs : a.stacks 324 = []) :
    Eval move (6*(a.stacks 332).length+6) a (moved a) := by
  let mid : Data := ⟨readRegs a.regs 0 1 none,
    StackRoutines.transferStacks 332 324 a.stacks⟩
  have h1 := ListRegisterProgram.transfer_run (332 : Fin 768) 324 (0 : Fin 40) 1
    (by decide) (by decide) a.regs a.stacks
  have h2 := ListRegisterProgram.transfer_run (324 : Fin 768) 323 (0 : Fin 40) 1
    (by decide) (by decide) (readRegs a.regs 0 1 none)
    (StackRoutines.transferStacks 332 324 a.stacks)
  have e1 : Eval (.call (StackRoutines.transferProgram 332 324 0 1))
      (3*(a.stacks 332).length+3) a mid := Eval.call _ h1
  have e2 : Eval (.call (StackRoutines.transferProgram 324 323 0 1))
      (3*(mid.stacks 324).length+3) mid
      ⟨readRegs mid.regs 0 1 none, StackRoutines.transferStacks 324 323 mid.stacks⟩ :=
    Eval.call _ h2
  have he := Eval.seq e1 e2
  convert he using 1 <;>
    simp [move,moved,mid,StackRoutines.transferStacks,hs,
      StackRoutines.readRegs_reset] ; omega

def restore : Code := .seq (.base (.atom (.set 16 false)))
  (.seq (.base (.atom (.set 17 true))) (.base (.atom (.set 18 false))))
def restored (a : Data) : Data :=
  ⟨Function.update (Function.update (Function.update a.regs 16 false) 17 true) 18 false,a.stacks⟩
theorem restore_eval (a : Data) : Eval restore 3 a (restored a) := by
  exact Eval.seq (.base (.atom _ _)) (Eval.seq (.base (.atom _ _)) (.base (.atom _ _)))

def finish : Code := .seq (.call (StackRoutines.clearProgram 330 0 1))
  (.seq move (.seq (.call (StackRoutines.clearProgram 321 0 1)) restore))
def finished (a : Data) : Data := restored (cleared 321 (moved (cleared 330 a)))

theorem finish_eval (a : Data) (hs : a.stacks 324 = []) :
    Eval finish (2*(a.stacks 330).length+6*(a.stacks 332).length+
      2*(a.stacks 321).length+15) a (finished a) := by
  have hs' : (cleared 330 a).stacks 324 = [] := by simp [cleared,StackRoutines.clearStacks,hs]
  have he := (clear_eval 330 a).seq ((move_eval (cleared 330 a) hs').seq
    ((clear_eval 321 (moved (cleared 330 a))).seq (restore_eval _)))
  convert he using 1 <;> simp [finish,finished,cleared,moved,StackRoutines.clearStacks,
    StackRoutines.transferStacks] ; ring

theorem finished_output (a : Data) (h1 : a.stacks 323 = []) (h2 : a.stacks 324 = []) :
    (finished a).stacks 323 = a.stacks 332 := by
  simp [finished,restored,cleared,moved,StackRoutines.clearStacks,StackRoutines.transferStacks,h1,h2]

theorem finished_empty (a : Data) :
    (finished a).stacks 321 = [] ∧ (finished a).stacks 324 = [] ∧
    (finished a).stacks 330 = [] ∧ (finished a).stacks 332 = [] := by
  simp [finished,restored,cleared,moved,StackRoutines.clearStacks,StackRoutines.transferStacks]

theorem finished_frame (a : Data) (i : Fin 768)
    (h1 : i ≠ 321) (h2 : i ≠ 323) (h3 : i ≠ 324) (h4 : i ≠ 330) (h5 : i ≠ 332) :
    (finished a).stacks i = a.stacks i := by
  simp [finished,restored,cleared,moved,StackRoutines.clearStacks,StackRoutines.transferStacks,
    h1,h2,h3,h4,h5]

theorem finished_parser (a : Data) : (finished a).regs 16 = false ∧
    (finished a).regs 17 = true ∧ (finished a).regs 18 = false := by simp [finished,restored]

def command (query : Code) : Code := .seq initCommand
  (.seq (ExecCNFTupleEnumeration.enumerate fixedPorts.counter (body fixedPorts query)) finish)
def program (query : Code) := compiled (command query) 333 323

theorem program_trace (query : Code) {n : ℕ} {a b : Data}
    (he : Eval (command query) n a b) :
    Trace (program query) (n+1) (a.withPC (some (program query).entry)) (b.withPC none) :=
  compiled_halt_trace he 333 323

end SubexponentialSAT.SqrtLog.LeafBranchProgram.Wide

namespace SubexponentialSAT.SqrtLog.LeafBranchProgram
/-- Exact callback interface used by the final wide residual evaluator. -/
abbrev WideResidualSpec (query : Wide.Code) (shape : List ℕ) (I : Wide.Data → Prop)
    (budget width : ℕ) (value : ℕ → ℕ) : Prop :=
  ResidualSpec Wide.fixedPorts query shape I budget width value
end SubexponentialSAT.SqrtLog.LeafBranchProgram

end OAI.Algorithms
