import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.OuterQueryEncoding
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgramHistoryServices

namespace OAI.Algorithms

/-! The actual MassSpec input state retains the selected table and immutable
outer context. No current-state row subset is substituted for the exact
controller history. -/
namespace SubexponentialSAT.SqrtLog.OuterQuery
open SubexponentialSAT BitProgram StructuredCalls HashSelectProgram LeafScopeResourceBounds
open LeafOuterProgram

noncomputable section

def massInput (current : Data) (regs : Fin 8 → Bool)
    (bits : List Bool) (best : Entry) (queue : List Bool) : Data :=
  state selector.controller.trial.core (afterCopyFamily selector.controller.trial current)
    regs ⟨bits,[]⟩ best queue

private theorem selector_stack_val (j : Fin 14) : (selector.stack j).val=768+j.val := by
  fin_cases j <;> rfl

private theorem core_stack_val (j : Fin 9) :
    (selector.controller.trial.core.stack j).val=768+j.val := by
  fin_cases j <;> rfl

theorem massInput_frame (current : Data) (regs : Fin 8 → Bool)
    (bits : List Bool) (best : Entry) (queue : List Bool) (i : Fin 896)
    (hi : ∀ j, selector.controller.trial.core.stack j≠i) :
    (massInput current regs bits best queue).stacks i=current.stacks i := by
  rw [massInput,state,embedState_stack_frame _ _ _ _ i (by
    rintro ⟨j,hj⟩; exact hi j hj)]
  change (StackRoutines.copyStacks _ _ current.stacks) i=current.stacks i
  simp only [StackRoutines.copyStacks,Function.update_of_ne (Ne.symm (hi 8))]

theorem massInput_payload (current : Data) (regs : Fin 8 → Bool)
    (bits : List Bool) (best : Entry) (queue : List Bool) :
    (massInput current regs bits best queue).stacks 768=bits := by
  exact state_stack selector.controller.trial.core _ regs ⟨bits,[]⟩ best queue 0

theorem massInput_outer {a frame current : Data} {family rows : Records}
    (hf : Execution.Hash.ContextFrame selector a frame)
    (hr : ControllerReady selector.controller frame family rows current)
    (regs : Fin 8 → Bool) (bits : List Bool) (best : Entry) (queue : List Bool)
    (i : Fin 896) (hi : i.val < 768 ∨ 782 ≤ i.val) :
    (massInput current regs bits best queue).stacks i=a.stacks i := by
  have hs : ∀ j, selector.stack j≠i := by
    intro j he
    have hh := congrArg Fin.val he
    rw [selector_stack_val] at hh
    have hj := j.isLt
    omega
  have hc : ∀ j, selector.controller.trial.core.stack j≠i := by
    intro j he
    exact hs (localController.trial.core.stack j) he
  rw [massInput_frame current regs bits best queue i hc]
  exact (hr.2.2.2.1 i (Ne.symm (hs 9)) (Ne.symm (hs 13)) hc).trans (hf.1 i hs)

theorem massInput_rows {frame current : Data} {family rows : Records}
    (hr : ControllerReady selector.controller frame family rows current)
    (regs : Fin 8 → Bool) (bits : List Bool) (best : Entry) (queue : List Bool) :
    (massInput current regs bits best queue).stacks 777=candidateEncoding rows := by
  rw [massInput_frame current regs bits best queue 777 (by
    intro j he
    have hh := congrArg Fin.val he
    rw [core_stack_val] at hh
    have hj := j.isLt
    change 768+j.val=777 at hh
    omega)]
  exact hr.2.2.1

theorem massInput_worker {a frame current : Data} {family rows : Records}
    (ha : WorkerEmpty a) (hf : Execution.Hash.ContextFrame selector a frame)
    (hr : ControllerReady selector.controller frame family rows current)
    (regs : Fin 8 → Bool) (bits : List Bool) (best : Entry) (queue : List Bool) :
    WorkerEmpty (massInput current regs bits best queue) := by
  intro i
  rw [massInput_outer hf hr regs bits best queue (workerStack i) (Or.inl i.isLt)]
  exact ha i

/-- The prefix physically assembled from payload768 and table777 is exactly
the raw table of this candidate followed by the current selected rows. -/
theorem massInput_trial_bytes {n B : ℕ} (F : Formula n) (a frame current : Data)
    (ha : StartReady a n (formulaRecords F).length B)
    (hm : 0 < (formulaRecords F).length)
    (s : SparseCode.SuppliedShifts (formulaRecords F).length B)
    (Q : SparseCode.SuppliedLocal (formulaRecords F).length B)
    (score : Records → List Bool → List Bool) (seed : List Bool) (rest : Records)
    (hfamily : generatedPayloads (SubexpAlphabetProgram.alphabetWords (a.stacks 768))
      (SparseCode.distanceDenom (formulaRecords F).length B)=seed::rest)
    (round : ℕ)
    (hr : ControllerReady selector.controller frame (seed::rest)
      (selected score seed rest (initial F a s Q) round) current)
    (regs : Fin 8 → Bool) (bits : List Bool) (best : Entry) (queue : List Bool)
    (hb : bits ∈ seed::rest) :
    true::(Encoding.frame ((massInput current regs bits best queue).stacks 768).reverse ++
      (massInput current regs bits best queue).stacks 777)=
        HashScopeProgram.RawTable.inputBits (a.stacks 783).length
          (trialRows F a hm s Q score seed rest round bits) := by
  rw [massInput_payload,massInput_rows hr]
  exact trial_encoding F a ha hm s Q score seed rest hfamily round bits hb

end
end SubexponentialSAT.SqrtLog.OuterQuery

end OAI.Algorithms
