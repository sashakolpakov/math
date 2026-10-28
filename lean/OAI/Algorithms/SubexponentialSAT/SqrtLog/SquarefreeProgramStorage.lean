import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames
import OAI.Algorithms.SubexponentialSAT.SubexpRecordScan

namespace OAI.Algorithms

/-! Port relocation and paid bit-copy primitives for the dictionary builder. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.Program
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpRecordScan

abbrev StorageData := State 5 7

def extendStorage (d : State 5 6) (saved : List Bool) : StorageData :=
  ⟨d.regs, ![d.stacks 0,d.stacks 1,d.stacks 2,d.stacks 3,d.stacks 4,d.stacks 5,saved]⟩

theorem extendStorage_low (d : State 5 6) (saved : List Bool) (i : Fin 6) :
    (extendStorage d saved).stacks i.castSucc = d.stacks i := by fin_cases i <;> rfl

@[simp] theorem extendStorage_saved (d : State 5 6) (saved : List Bool) :
    (extendStorage d saved).stacks 6 = saved := rfl

theorem embedStorage (a b : State 5 6) (saved : List Bool) :
    embedState id Fin.castSucc (extendStorage a saved) b = extendStorage b saved := by
  apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id (Fin.castSucc_injective 6)
  · intro i; rfl
  · intro i hi; exact False.elim (hi ⟨i,rfl⟩)
  · intro i; fin_cases i <;> rfl
  · intro i hi
    have hi' : ¬ i.val < 6 := by
      intro hil
      apply hi
      exact ⟨⟨i.val, hil⟩, Fin.ext rfl⟩
    have hv : i.val = 6 := by have := i.isLt; omega
    have he : i = (6 : Fin 7) := Fin.ext hv
    subst i
    rfl

abbrev storageCall (c : Cmd 5 6) : Cmd 5 7 := liftCommand c 0 5 id Fin.castSucc

theorem storageCall_eval {c : Cmd 5 6} {n : ℕ} {a b : State 5 6}
    (h : Eval c n a b) (saved : List Bool) :
    Eval (storageCall c) (n + 1) (extendStorage a saved) (extendStorage b saved) := by
  have hh := eval_liftCommand h 0 5 id Fin.castSucc (extendStorage a saved)
    Function.injective_id (Fin.castSucc_injective 6)
  simpa only [storageCall, embedStorage] using hh

abbrev storageCopy (src dst tmp : Fin 7) : Cmd 5 7 :=
  .call (StackRoutines.copyProgram src dst tmp (0 : Fin 5) 1)

def storageCopied (d : StorageData) (src dst : Fin 7) : StorageData :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.copyStacks src dst d.stacks⟩

theorem storageCopy_eval (d : StorageData) (src dst tmp : Fin 7)
    (hsd : src ≠ dst) (hst : src ≠ tmp) (htd : tmp ≠ dst)
    (htmp : d.stacks tmp = []) :
    Eval (storageCopy src dst tmp) (7 * (d.stacks src).length + 5)
      d (storageCopied d src dst) := by
  apply Eval.call
  have h := StackRoutines.copyProgram_trace src dst tmp (0 : Fin 5) 1
    hsd hst htd (by decide) d.regs d.stacks htmp
  have hh := StackRoutines.halt_after_trace _ h 7 rfl rfl
  simpa [storageCopied, StackRoutines.copyResult, StructuredProgram.State.withPC,
    StackRoutines.copyProgram, Nat.add_assoc] using hh

abbrev storageClear (src : Fin 7) : Cmd 5 7 :=
  .call (StackRoutines.clearProgram src (0 : Fin 5) 1)

def storageCleared (d : StorageData) (src : Fin 7) : StorageData :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.clearStacks src d.stacks⟩

theorem storageClear_eval (d : StorageData) (src : Fin 7) :
    Eval (storageClear src) (2 * (d.stacks src).length + 3)
      d (storageCleared d src) := by
  apply Eval.call
  have h := StackRoutines.clearProgram_trace src (0 : Fin 5) 1 d.regs d.stacks
  have hh := StackRoutines.halt_after_trace _ h 2 rfl rfl
  simpa [storageCleared, StackRoutines.clearResult, StructuredProgram.State.withPC,
    StackRoutines.clearProgram, Nat.add_assoc] using hh
end SubexponentialSAT.SqrtLog.Squarefree.Program

end OAI.Algorithms
