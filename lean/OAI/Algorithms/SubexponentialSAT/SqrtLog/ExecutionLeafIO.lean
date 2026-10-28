import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames
import OAI.Algorithms.SubexponentialSAT.BankRoutines
import OAI.Algorithms.SubexponentialSAT.RegisterResetProgram

namespace OAI.Algorithms

/-! The physical I/O boundary around the 40-register, 896-stack leaf core.
The four extra ports retain Main's leaf bytes, n, occurrence bound, and answer.
The core is still supplied as fixed code with an actual Eval trace. -/
namespace SubexponentialSAT.SqrtLog.Execution.LeafIO

open BitProgram StructuredCalls
abbrev Data := State 40 900

def work (i : Fin 896) : Fin 900 := i.castAdd 4

theorem work_injective : Function.Injective work := by
  intro i j h
  exact Fin.ext (congrArg (fun q : Fin 900 => q.val) h)

def workerPorts : List (Fin 900) := (List.finRange 896).map work

theorem workerPorts_nodup : workerPorts.Nodup :=
  (List.nodup_finRange 896).map work_injective

@[simp] theorem mem_workerPorts (i : Fin 900) : i ∈ workerPorts ↔ i.val < 896 := by
  simp only [workerPorts, List.mem_map, List.mem_finRange, true_and]
  constructor
  · rintro ⟨j,rfl⟩; exact j.isLt
  · intro hi
    exact ⟨⟨i.val,hi⟩,Fin.ext rfl⟩

def Ready (a : Data) : Prop :=
  (∀ i : Fin 900, i.val < 896 → a.stacks i = []) ∧ a.stacks 899 = []

abbrev copy (src dst : Fin 900) : Cmd 40 900 :=
  .call (StackRoutines.copyProgram src dst 895 0 1)

abbrev copied (src dst : Fin 900) (a : Data) : Data :=
  ⟨readRegs a.regs 0 1 none,StackRoutines.copyStacks src dst a.stacks⟩

@[simp] theorem copied_stack (src dst i : Fin 900) (a : Data) :
    (copied src dst a).stacks i = if i = dst then a.stacks src ++ a.stacks dst else a.stacks i := by
  simp [StackRoutines.copyStacks,Function.update_apply]

abbrev prepare : Cmd 40 900 :=
  .seq (copy 896 784) (.seq (copy 897 785) (copy 898 786))

abbrev prepared (a : Data) : Data := copied 898 786 (copied 897 785 (copied 896 784 a))

def prepareCost (a : Data) : ℕ :=
  7*((a.stacks 896).length+(a.stacks 897).length+(a.stacks 898).length)+15

theorem prepare_eval (a : Data) (h : Ready a) :
    Eval prepare (prepareCost a) a (prepared a) := by
  have htmp := h.1 895 (by decide)
  have h1 := BankRoutines.copy_call_eval (896 : Fin 900) 784 895 (0 : Fin 40) 1
    (by decide) (by decide) (by decide) (by decide) a.regs a.stacks htmp
  have h2 := BankRoutines.copy_call_eval (897 : Fin 900) 785 895 (0 : Fin 40) 1
    (by decide) (by decide) (by decide) (by decide)
    (copied 896 784 a).regs (copied 896 784 a).stacks
      (by simpa [copied, StackRoutines.copyStacks] using htmp)
  have h3 := BankRoutines.copy_call_eval (898 : Fin 900) 786 895 (0 : Fin 40) 1
    (by decide) (by decide) (by decide) (by decide)
    (copied 897 785 (copied 896 784 a)).regs
    (copied 897 785 (copied 896 784 a)).stacks
      (by simpa [copied, StackRoutines.copyStacks] using htmp)
  have hh : Eval prepare
      ((7*(a.stacks 896).length+5)+
        ((7*(a.stacks 897).length+5)+(7*(a.stacks 898).length+5))) a (prepared a) := by
    simpa [prepare, copy, prepared, copied, StackRoutines.copyStacks, Function.update_apply,
      show (897 : Fin 900) ≠ 784 by decide,show (898 : Fin 900) ≠ 785 by decide,
      show (898 : Fin 900) ≠ 784 by decide] using h1.seq (h2.seq h3)
  convert hh using 1 ; simp only [prepareCost] ; ring

@[simp] theorem prepared_external (a : Data) (i : Fin 900) (hi : 896 ≤ i.val) :
    (prepared a).stacks i = a.stacks i := by
  have h784 : i ≠ 784 := by
    intro he; have hv := congrArg (fun q : Fin 900 => q.val) he
    change i.val = 784 at hv; omega
  have h785 : i ≠ 785 := by
    intro he; have hv := congrArg (fun q : Fin 900 => q.val) he
    change i.val = 785 at hv; omega
  have h786 : i ≠ 786 := by
    intro he; have hv := congrArg (fun q : Fin 900 => q.val) he
    change i.val = 786 at hv; omega
  simp [h784,h785,h786]

theorem prepared_work (a : Data) (h : Ready a) (i : Fin 896) :
    (prepared a).stacks (work i) =
      if i.val = 784 then a.stacks 896 else
      if i.val = 785 then a.stacks 897 else
      if i.val = 786 then a.stacks 898 else [] := by
  have hw := h.1 (work i) i.isLt
  have h784 := h.1 784 (by decide)
  have h785 := h.1 785 (by decide)
  have h786 := h.1 786 (by decide)
  simp only []
  by_cases h1 : i.val = 784
  · have he : work i = 784 := Fin.ext h1
    simp [h1,he,h784]
  · by_cases h2 : i.val = 785
    · have he : work i = 785 := Fin.ext h2
      simp [h2,he,h785]
    · by_cases h3 : i.val = 786
      · have he : work i = 786 := Fin.ext h3
        simp [h3,he,h786]
      · have hn1 : work i ≠ 784 := fun he => h1 (congrArg Fin.val he)
        have hn2 : work i ≠ 785 := fun he => h2 (congrArg Fin.val he)
        have hn3 : work i ≠ 786 := fun he => h3 (congrArg Fin.val he)
        simp [h1,h2,h3,hn1,hn2,hn3,hw]

abbrev clearTemporary : Cmd 40 900 := .call (StackRoutines.clearProgram 895 0 1)
abbrev temporaryCleared (a : Data) : Data :=
  ⟨readRegs a.regs 0 1 none,StackRoutines.clearStacks 895 a.stacks⟩
abbrev exported (a : Data) : Data := copied 787 899 (temporaryCleared a)
abbrev cleared (a : Data) : Data :=
  ⟨readRegs a.regs 0 1 none,BankRoutines.clearBankStacks workerPorts a.stacks⟩
abbrev finished (a : Data) : Data := RegisterResetProgram.zeroed (cleared (exported a))
abbrev finish : Cmd 40 900 :=
  .seq clearTemporary (.seq (copy 787 899)
    (.seq (BankRoutines.clearCmd 895 0 1 workerPorts) RegisterResetProgram.all))
def finishCost (a : Data) : ℕ :=
  (2*(a.stacks 895).length+3)+(7*(a.stacks 787).length+5)+
    (2*(workerPorts.map (fun i => ((exported a).stacks i).length)).sum+
      3*workerPorts.length+3)+40

theorem finish_eval (a : Data) : Eval finish (finishCost a) a (finished a) := by
  have h1 := BankRoutines.clear_call_eval (895 : Fin 900) (0 : Fin 40) 1 a.regs a.stacks
  have h2 := BankRoutines.copy_call_eval (787 : Fin 900) 899 895 (0 : Fin 40) 1
    (by decide) (by decide) (by decide) (by decide)
    (temporaryCleared a).regs (temporaryCleared a).stacks (by simp [])
  have htmp : (exported a).stacks 895 = [] := by simp []
  have h3 := BankRoutines.clear_eval (895 : Fin 900) (0 : Fin 40) 1
    workerPorts workerPorts_nodup (exported a).regs (exported a).stacks htmp
  have h4 := RegisterResetProgram.all_eval (cleared (exported a))
  have hh := h1.seq (h2.seq (h3.seq h4))
  simpa only [finish,finishCost,finished,clearTemporary,copy,temporaryCleared,
    exported,cleared,StackRoutines.clearStacks,Function.update_of_ne (show (787 : Fin 900) ≠ 895 by decide),
    Nat.add_assoc] using hh

theorem finished_work (a : Data) (i : Fin 896) : (finished a).stacks (work i) = [] := by
  simp [work,i.isLt]

theorem finished_regs (a : Data) (i : Fin 40) : (finished a).regs i = false := rfl

theorem finished_answer (a : Data) (ha : a.stacks 899 = []) :
    (finished a).stacks 899 = a.stacks 787 := by
  have hn : (899 : Fin 900) ∉ workerPorts := by rw [mem_workerPorts]; decide
  simp only []
  rw [BankRoutines.clearBankStacks_frame _ _ _ hn]
  simp [StackRoutines.clearStacks,ha]

theorem finished_source (a : Data) (i : Fin 900)
    (hi : 896 ≤ i.val) (hi' : i.val < 899) :
    (finished a).stacks i = a.stacks i := by
  have hn895 : i ≠ 895 := by
    intro he; have hv := congrArg (fun q : Fin 900 => q.val) he
    change i.val = 895 at hv; omega
  have hn899 : i ≠ 899 := by
    intro he; have hv := congrArg (fun q : Fin 900 => q.val) he
    change i.val = 899 at hv; omega
  simp [BankRoutines.clearBankStacks,StackRoutines.clearStacks,hn895,hn899,show ¬i.val < 896 by omega]

abbrev command (core : Cmd 40 896) : Cmd 40 900 :=
  .seq prepare (.seq (liftCommand core 784 787 id work) finish)

/-- A core trace is composed with the actual copies, export, and full cleanup.
All source and cleanup lengths occur in the displayed transition count. -/
theorem command_eval (core : Cmd 40 896) (a : Data) (ha : Ready a)
    {t : ℕ} {b : State 40 896}
    (hb : Eval core t (projectState id work (prepared a)) b) :
    let middle := embedState id work (prepared a) b
    Eval (command core) (prepareCost a+(t+1)+finishCost middle) a (finished middle) := by
  dsimp only
  have hc := eval_liftCommand_from_state core 784 787 id work (prepared a)
    Function.injective_id work_injective hb
  simpa only [command,Nat.add_assoc] using (prepare_eval a ha).seq (hc.seq (finish_eval _))

end SubexponentialSAT.SqrtLog.Execution.LeafIO

end OAI.Algorithms
