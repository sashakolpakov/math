import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgramDictionaryState

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

theorem copy_machine (regs : Fin 8 → Bool) (a b : Tape) (src dst tmp : Fin 27)
    (hsd : src ≠ dst) (hst : src ≠ tmp) (htd : tmp ≠ dst)
    (htmp : tapes a tmp = []) (hs : copyStacks src dst (tapes a) = tapes b) :
    Eval (copy src dst tmp) (7 * (tapes a src).length + 5) (machine regs a)
      (machine (readRegs regs 0 1 none) b) := by
  simpa only [copied,machine,hs] using copy_eval (machine regs a) src dst tmp hsd hst htd htmp

theorem transfer_machine (regs : Fin 8 → Bool) (a b : Tape) (src dst : Fin 27)
    (hsd : src ≠ dst) (hs : transferStacks src dst (tapes a) = tapes b) :
    Eval (transfer src dst) (3 * (tapes a src).length + 3) (machine regs a)
      (machine (readRegs regs 0 1 none) b) := by
  simpa only [transferred,machine,hs] using transfer_eval (machine regs a) src dst hsd

theorem clear_machine (regs : Fin 8 → Bool) (a b : Tape) (src : Fin 27)
    (hs : clearStacks src (tapes a) = tapes b) :
    Eval (clear src) (2 * (tapes a src).length + 3) (machine regs a)
      (machine (readRegs regs 0 1 none) b) := by
  simpa only [cleared,machine,hs] using clear_eval (machine regs a) src

theorem copyDict_eval (regs : Fin 8 → Bool) (a : Tape) (he : a.remain = []) :
    Eval (copy 15 18 23) (7 * a.dict.length + 5) (machine regs a)
      (machine (readRegs regs 0 1 none) { a with remain := a.dict }) := by
  apply copy_machine regs a _ 15 18 23 (by decide) (by decide) (by decide) rfl
  funext i; fin_cases i <;> simp [copyStacks,tapes,he]

theorem copyNew_eval (regs : Fin 8 → Bool) (a : Tape) (he : a.left = []) :
    Eval (copy 17 8 23) (7 * a.coeff.length + 5) (machine regs a)
      (machine (readRegs regs 0 1 none) { a with left := a.coeff }) := by
  apply copy_machine regs a _ 17 8 23 (by decide) (by decide) (by decide) rfl
  funext i; fin_cases i <;> simp [copyStacks,tapes,he]

theorem copyCount_eval (regs : Fin 8 → Bool) (a : Tape) (he : a.steps = []) :
    Eval (copy 24 11 23) (7 * a.count.length + 5) (machine regs a)
      (machine (readRegs regs 0 1 none) { a with steps := a.count }) := by
  apply copy_machine regs a _ 24 11 23 (by decide) (by decide) (by decide) rfl
  funext i; fin_cases i <;> simp [copyStacks,tapes,he]

theorem copyMiss_eval (regs : Fin 8 → Bool) (a : Tape) (he : a.out = []) :
    Eval (copy 17 0 23) (7 * a.coeff.length + 5) (machine regs a)
      (machine (readRegs regs 0 1 none) { a with out := a.coeff }) := by
  apply copy_machine regs a _ 17 0 23 (by decide) (by decide) (by decide) rfl
  funext i; fin_cases i <;> simp [copyStacks,tapes,he]

theorem copyResult_eval (regs : Fin 8 → Bool) (a : Tape) (he : a.dict = []) :
    Eval (copy 25 15 23) (7 * a.result.length + 5) (machine regs a)
      (machine (readRegs regs 0 1 none) { a with dict := a.result }) := by
  apply copy_machine regs a _ 25 15 23 (by decide) (by decide) (by decide) rfl
  funext i; fin_cases i <;> simp [copyStacks,tapes,he]

theorem transferOld_eval (regs : Fin 8 → Bool) (a : Tape) (he : a.right = []) :
    Eval (transfer 8 9) (3 * a.left.length + 3) (machine regs a)
      (machine (readRegs regs 0 1 none) { a with left := [], right := a.left.reverse }) := by
  apply transfer_machine regs a _ 8 9 (by decide)
  funext i; fin_cases i <;> simp [transferStacks,tapes,he]

theorem transferSum_eval (regs : Fin 8 → Bool) (a : Tape) (he : a.combined = []) :
    Eval (transfer 0 26) (3 * a.out.length + 3) (machine regs a)
      (machine (readRegs regs 0 1 none) { a with out := [], combined := a.out.reverse }) := by
  apply transfer_machine regs a _ 0 26 (by decide)
  funext i; fin_cases i <;> simp [transferStacks,tapes,he]

theorem clearRemain_eval (regs : Fin 8 → Bool) (a : Tape) :
    Eval (clear 18) (2 * a.remain.length + 3) (machine regs a)
      (machine (readRegs regs 0 1 none) { a with remain := [] }) := by
  apply clear_machine regs a _ 18
  funext i; fin_cases i <;> simp [clearStacks,tapes]

theorem clearResult_eval (regs : Fin 8 → Bool) (a : Tape) :
    Eval (clear 25) (2 * a.result.length + 3) (machine regs a)
      (machine (readRegs regs 0 1 none) { a with result := [] }) := by
  apply clear_machine regs a _ 25
  funext i; fin_cases i <;> simp [clearStacks,tapes]

end SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary

end OAI.Algorithms
