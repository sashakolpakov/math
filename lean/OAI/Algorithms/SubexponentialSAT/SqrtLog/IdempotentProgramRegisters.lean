import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentProgramNative
import OAI.Algorithms.SubexponentialSAT.ArithmeticCalls

namespace OAI.Algorithms

/-! Source-preserving storage for the fixed Newton register machine. Every
copy, replacement, and clearing operation is an actual finite bit program. -/
namespace SubexponentialSAT.SqrtLog.IdempotentProgram

open BitProgram StructuredCalls StackRoutines

abbrev RegisterData := State 8 41

def arrayRegister (i : Fin 4) : Fin 41 := ⟨32+i.val, by omega⟩

abbrev registerCopy (source target : Fin 41) : Cmd 8 41 :=
  ArithmeticCalls.copyAt source target 38

abbrev registerClear (target : Fin 41) : Cmd 8 41 :=
  .call (clearProgram target 0 1)

def cleared (d : RegisterData) (target : Fin 41) : RegisterData :=
  ⟨readRegs d.regs 0 1 none, Function.update d.stacks target []⟩

theorem registerClear_eval (d : RegisterData) (target : Fin 41) :
    Eval (registerClear target) (2*(d.stacks target).length+3) d (cleared d target) :=
  .call _ (ListRegisterProgram.clear_run target 0 1 d.regs d.stacks)

/-- Store the computed result, preserving bit order and emptying the result port. -/
abbrev storeResult (target : Fin 41) : Cmd 8 41 :=
  .seq (registerClear target)
    (.seq (registerCopy 0 target) (registerClear 0))

def storedResult (d : RegisterData) (target : Fin 41) : RegisterData :=
  cleared (ArithmeticCalls.afterCopy 0 target (cleared d target)) 0

theorem storeResult_eval (d : RegisterData) (target : Fin 41)
    (ht : target ≠ 0) (h38 : target ≠ 38) (hs : d.stacks 38 = []) :
    Eval (storeResult target)
      (2*(d.stacks target).length + 9*(d.stacks 0).length + 11)
      d (storedResult d target) := by
  have h1 := registerClear_eval d target
  have h2 := ArithmeticCalls.copyAt_eval (0 : Fin 41) target 38 (cleared d target)
    ht.symm (by decide) h38.symm (by simp [cleared])
    (by simp [cleared, h38.symm, hs])
  have h3 := registerClear_eval (ArithmeticCalls.afterCopy 0 target (cleared d target)) 0
  convert h1.seq (h2.seq h3) using 1 <;>
    simp [ storedResult, cleared, ArithmeticCalls.afterCopy, ht.symm] ; omega

theorem storedResult_stacks (d : RegisterData) (target : Fin 41)
    (ht : target ≠ 0) :
    (storedResult d target).stacks =
      Function.update (Function.update d.stacks target (d.stacks 0)) 0 [] := by
  simp [storedResult, cleared, ArithmeticCalls.afterCopy, ht.symm,
    Function.update_idem]

/-- The cached unary degree is copied; the raw service may consume its copy. -/
abbrev prepareOperands (left right : Fin 41) : Cmd 8 41 :=
  .seq (registerCopy left 8)
    (.seq (registerCopy right 9) (registerCopy 37 11))

def preparedOperands (d : RegisterData) (left right : Fin 41) : RegisterData :=
  ArithmeticCalls.afterCopy 37 11
    (ArithmeticCalls.afterCopy right 9 (ArithmeticCalls.afterCopy left 8 d))

theorem prepareOperands_eval (d : RegisterData) (left right : Fin 41)
    (hl : 32 ≤ left.val) (hr : 32 ≤ right.val)
    (hl38 : left ≠ 38) (hr38 : right ≠ 38)
    (h8 : d.stacks 8 = []) (h9 : d.stacks 9 = [])
    (h11 : d.stacks 11 = []) (h38 : d.stacks 38 = []) :
    Eval (prepareOperands left right)
      (7*(d.stacks left).length + 7*(d.stacks right).length +
        7*(d.stacks 37).length + 15) d (preparedOperands d left right) := by
  have hl8 : left ≠ 8 := by intro h; have hv : left.val = 8 := congrArg Fin.val h; omega
  have hr8 : right ≠ 8 := by intro h; have hv : right.val = 8 := congrArg Fin.val h; omega
  have hr9 : right ≠ 9 := by intro h; have hv : right.val = 9 := congrArg Fin.val h; omega
  have h1 := ArithmeticCalls.copyAt_eval left (8 : Fin 41) 38 d
    hl8 hl38 (by decide) h8 h38
  have h2 := ArithmeticCalls.copyAt_eval right (9 : Fin 41) 38
    (ArithmeticCalls.afterCopy left 8 d) hr9 hr38 (by decide)
    (by simp [ArithmeticCalls.afterCopy, h9])
    (by simp [ArithmeticCalls.afterCopy, h38])
  have h3 := ArithmeticCalls.copyAt_eval (37 : Fin 41) 11 38
    (ArithmeticCalls.afterCopy right 9 (ArithmeticCalls.afterCopy left 8 d))
    (by decide) (by decide) (by decide)
    (by simp [ArithmeticCalls.afterCopy, h11])
    (by simp [ArithmeticCalls.afterCopy, h38])
  convert h1.seq (h2.seq h3) using 1 <;>
    simp [ preparedOperands, ArithmeticCalls.afterCopy,
      hr8] ; omega

@[simp] theorem preparedOperands_stacks (d : RegisterData) (left right : Fin 41)
    (hr : 32 ≤ right.val) :
    (preparedOperands d left right).stacks =
      Function.update (Function.update (Function.update d.stacks 8 (d.stacks left))
        9 (d.stacks right)) 11 (d.stacks 37) := by
  have hr8 : right ≠ 8 := by intro h; have hv : right.val = 8 := congrArg Fin.val h; omega
  simp [preparedOperands, ArithmeticCalls.afterCopy, hr8]

/-- The complete register operation has fixed syntax. `raw` is the shared
native service, lifted to the low 32 stacks. -/
abbrev registerBinary (raw : Cmd 8 41) (target left right : Fin 41) : Cmd 8 41 :=
  .seq (prepareOperands left right) (.seq raw (storeResult target))

/-- All argument copies and the replacement are paid. The only hypothesis
about the arithmetic itself is an actual evaluation of its fixed command. -/
theorem registerBinary_eval (raw : Cmd 8 41) (d e : RegisterData)
    (target left right : Fin 41) (result : List Bool) (n : ℕ)
    (ht : 32 ≤ target.val) (hl : 32 ≤ left.val) (hr : 32 ≤ right.val)
    (ht38 : target ≠ 38) (hl38 : left ≠ 38) (hr38 : right ≠ 38)
    (h0 : d.stacks 0 = []) (h8 : d.stacks 8 = []) (h9 : d.stacks 9 = [])
    (h11 : d.stacks 11 = []) (h38 : d.stacks 38 = [])
    (run : Eval raw n (preparedOperands d left right) e)
    (output : e.stacks = Function.update d.stacks 0 result) :
    ∃ f, Eval (registerBinary raw target left right)
      (n + 7*(d.stacks left).length + 7*(d.stacks right).length +
        7*(d.stacks 37).length + 2*(d.stacks target).length + 9*result.length + 26) d f ∧
      f.stacks = Function.update d.stacks target result := by
  have ht0 : target ≠ 0 := by intro h; have hv : target.val = 0 := congrArg Fin.val h; omega
  have prepare := prepareOperands_eval d left right hl hr hl38 hr38 h8 h9 h11 h38
  have store := storeResult_eval e target ht0 ht38 (by rw [output]; simpa using h38)
  refine ⟨storedResult e target, ?_, ?_⟩
  · convert prepare.seq (run.seq store) using 1 ;
      simp [ output, ht0] ; omega
  · rw [storedResult_stacks e target ht0, output]
    funext j
    by_cases hjt : j = target
    · subst j; simp [ht0]
    · by_cases hj0 : j = 0
      · subst j; simp [hjt, h0]
      · simp [hjt, hj0]

end SubexponentialSAT.SqrtLog.IdempotentProgram

end OAI.Algorithms
