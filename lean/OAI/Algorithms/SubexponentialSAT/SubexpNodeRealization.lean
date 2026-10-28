import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpNodePorts
import OAI.Algorithms.SubexponentialSAT.ProgramEmbeddingComposition

namespace OAI.Algorithms

/-! Transfer the actual local node contract into the main program's protected
port layout. The local code remains a fixed 32-register, `k+39`-stack program. -/

namespace SubexponentialSAT.SubexpNodeRealization

open BitProgram StructuredCalls SubexpMainProgram SubexpNodePorts

def coreRegister : Fin 4 → Fin 32 := Fin.castAdd 28
def coreStack (k : ℕ) (i : Fin 5) : Fin (k + 39) := i.castLE (by omega)

theorem coreRegister_injective : Function.Injective coreRegister := Fin.castAdd_injective 4 28

theorem coreStack_injective (k : ℕ) : Function.Injective (coreStack k) := by
  intro i j hij
  exact Fin.ext (congrArg (fun x : Fin (k + 39) => x.val) hij)

theorem main_realizes {α : Type*} {k er es labels : ℕ}
    (p : Program 32 (k + 39) labels) (helper : ℕ)
    (hhelper : 37 ≤ helper) (hfit : helper + (k - 1) ≤ workStacks es)
    (hr : 32 ≤ workRegs er) (frame : State (workRegs er) (totalStacks es))
    (enc : α → List Bool) (split : α → Option (α × α))
    (P : α → Prop) (cost : α → ℕ)
    (h : ExecWorklistLoop.Ambient.BoundedRealizesOn p coreRegister (coreStack k)
      (projectState (registerMap hr) (stackMap helper hhelper hfit) frame) enc split P cost) :
    ExecWorklistLoop.Ambient.BoundedRealizesOn (liftNode p helper hhelper hfit hr)
      (SubexpMainSparsify.mainPorts er es).register
      (SubexpMainSparsify.mainPorts er es).coreStack frame enc split P cost := by
  have ht := ProgramEmbeddingComposition.boundedRealizesOn_lift p
    (registerMap hr) (stackMap helper hhelper hfit) coreRegister (coreStack k)
    (registerMap_injective hr) (stackMap_injective hhelper hfit)
    coreRegister_injective (coreStack_injective k) frame enc split P cost h
  have hreg : registerMap hr ∘ coreRegister =
      (SubexpMainSparsify.mainPorts er es).register := by
    funext i
    exact registerMap_core hr i
  have hstack : stackMap helper hhelper hfit ∘ coreStack k =
      (SubexpMainSparsify.mainPorts er es).coreStack := by
    funext i
    exact stackMap_core hhelper hfit i
  simpa only [liftNode, hreg, hstack] using ht

theorem project_regs_zero {k er es helper : ℕ}
    (hhelper : 37 ≤ helper) (hfit : helper + (k - 1) ≤ workStacks es)
    (hr : 32 ≤ workRegs er) (frame : State (workRegs er) (totalStacks es))
    (hz : ∀ i, frame.regs i = false) :
    ∀ i, (projectState (registerMap hr) (stackMap helper hhelper hfit) frame).regs i = false := by
  intro i
  exact hz (registerMap hr i)

theorem project_work_empty {k er es helper : ℕ}
    (hhelper : 37 ≤ helper) (hfit : helper + (k - 1) ≤ workStacks es)
    (hr : 32 ≤ workRegs er) (frame : State (workRegs er) (totalStacks es))
    (hw : ∀ i : Fin (totalStacks es), 5 ≤ i.val → i.val < 37 → frame.stacks i = [])
    (i : Fin (k + 39)) (hlo : 5 ≤ i.val) (hhi : i.val < 37) :
    (projectState (registerMap hr) (stackMap helper hhelper hfit) frame).stacks i = [] := by
  have hv : (stackMap helper hhelper hfit i).val = i.val := by
    simp only [stackMap_val, address, hhi, ite_true]
  exact hw _ (by omega) (by omega)

theorem project_M {k er es helper : ℕ}
    (hhelper : 37 ≤ helper) (hfit : helper + (k - 1) ≤ workStacks es)
    (hr : 32 ≤ workRegs er) (frame : State (workRegs er) (totalStacks es)) :
    (projectState (registerMap hr) (stackMap helper hhelper hfit) frame).stacks (mPort k) =
      frame.stacks (persistent es 23) := by
  change frame.stacks (stackMap helper hhelper hfit (mPort k)) = _
  rw [stackMap_M]

theorem project_threshold {k er es helper : ℕ}
    (hhelper : 37 ≤ helper) (hfit : helper + (k - 1) ≤ workStacks es)
    (hr : 32 ≤ workRegs er) (frame : State (workRegs er) (totalStacks es))
    (i : Fin (k - 1)) :
    (projectState (registerMap hr) (stackMap helper hhelper hfit) frame).stacks (thresholdPort k i) =
      frame.stacks (protectedPort helper hfit i) := by
  change frame.stacks (stackMap helper hhelper hfit (thresholdPort k i)) = _
  rw [stackMap_threshold]

theorem setup_project_threshold {er : ℕ} (c : SubexpSetupProgram.Config)
    (hr : 32 ≤ workRegs er)
    (frame : State (workRegs er) (totalStacks (SubexpSetupProgram.mainExtraStacks c)))
    (i : Fin (c.k - 1)) :
    (projectState (registerMap hr) (setupStackMap c) frame).stacks (thresholdPort c.k i) =
      frame.stacks (SubexpSetupProgram.mainStack c (SubexpSetupProgram.threshold c i)) := by
  change frame.stacks (setupStackMap c (thresholdPort c.k i)) = _
  rw [setupStackMap_threshold]

theorem setup_realizes {α : Type*} {er labels : ℕ}
    (c : SubexpSetupProgram.Config) (p : Program 32 (c.k + 39) labels)
    (hr : 32 ≤ workRegs er)
    (frame : State (workRegs er) (totalStacks (SubexpSetupProgram.mainExtraStacks c)))
    (enc : α → List Bool) (split : α → Option (α × α))
    (P : α → Prop) (cost : α → ℕ)
    (h : ExecWorklistLoop.Ambient.BoundedRealizesOn p coreRegister (coreStack c.k)
      (projectState (registerMap hr) (setupStackMap c) frame) enc split P cost) :
    ExecWorklistLoop.Ambient.BoundedRealizesOn
      (liftNode p (SubexpSetupProgram.helperSize c)
        (by have := SubexpSetupProgram.helperSize_ge c; omega) (setup_fit c).le hr)
      (SubexpMainSparsify.mainPorts er (SubexpSetupProgram.mainExtraStacks c)).register
      (SubexpMainSparsify.mainPorts er (SubexpSetupProgram.mainExtraStacks c)).coreStack
      frame enc split P cost :=
  main_realizes p _ _ _ hr frame enc split P cost h

end SubexponentialSAT.SubexpNodeRealization

end OAI.Algorithms
