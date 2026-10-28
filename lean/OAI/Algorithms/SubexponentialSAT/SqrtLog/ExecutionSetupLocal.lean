import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SetupPrimitives
import OAI.Algorithms.SubexponentialSAT.ArithmeticExpressionSupport
import OAI.Algorithms.SubexponentialSAT.RegisterResetProgram

namespace OAI.Algorithms

/-! A concrete fixed local controller for L(n) and w(n). The input is kept
on stack0; outputs are stack4 and stack5. Three scratch stacks are restored. -/

namespace SubexponentialSAT.SqrtLog.Execution.SetupLocal

open BitProgram StructuredCalls ArithmeticExpressionSupport

abbrev Data := StructuredProgram.State 8 6

def state (n work l w : List Bool) : Data :=
  ⟨fun _ => false, ![n, work, [], [], l, w]⟩

def registerMap (i : Fin 3) : Fin 8 := i.castLE (by decide)
def stackMap : Fin 3 → Fin 6 := ![1, 2, 3]

theorem registerMap_injective : Function.Injective registerMap := by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 8 => k.val) h)

theorem stackMap_injective : Function.Injective stackMap := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [stackMap]

abbrev localCall (c : Cmd 3 3) : Cmd 8 6 :=
  liftCommand c 0 0 registerMap stackMap

theorem localCall_eval (c : Cmd 3 3) (n xs ys l w : List Bool) {t : ℕ}
    (h : Eval c t (Setup.io xs) (Setup.io ys)) :
    Eval (localCall c) (t + 1) (state n xs l w) (state n ys l w) := by
  have he := eval_liftCommand h 0 0 registerMap stackMap (state n xs l w)
    registerMap_injective stackMap_injective
  have hstate (zs : List Bool) :
      embedState registerMap stackMap (state n xs l w) (Setup.io zs) = state n zs l w := by
    apply embedState_eq_of_ports _ _ _ _ _ registerMap_injective stackMap_injective
    · intro i; fin_cases i <;> rfl
    · intro i hi; rfl
    · intro i; fin_cases i <;> rfl
    · intro i hi
      fin_cases i <;> simp_all [stackMap, state, Fin.exists_fin_succ]
  simpa only [hstate, localCall] using he

abbrev core : Cmd 8 6 :=
  .seq (copyCmd 0 1 2)
    (.seq (localCall Setup.computeL)
      (.seq (copyCmd 1 4 2)
        (.seq (localCall Setup.logSucc)
          (.seq (copyCmd 1 5 2)
            (.seq (clearCmd 1) RegisterResetProgram.all)))))

abbrev command : Cmd 8 6 := .seq RegisterResetProgram.all core

private theorem copied01 (n : List Bool) :
    Eval (copyCmd (0 : Fin 6) 1 2) (7 * n.length + 5)
      (state n [] [] []) (state n n [] []) := by
  convert copy_eval (0 : Fin 6) 1 2 (state n [] [] [])
    (by decide) (by decide) (by decide) rfl rfl using 1
  · simp [state]
  · apply congrArg₂ StructuredProgram.State.mk <;> funext i <;> fin_cases i <;>
      simp [state, readRegs ]

private theorem copied14 (n l : List Bool) :
    Eval (copyCmd (1 : Fin 6) 4 2) (7 * l.length + 5)
      (state n l [] []) (state n l l []) := by
  convert copy_eval (1 : Fin 6) 4 2 (state n l [] [])
    (by decide) (by decide) (by decide) rfl rfl using 1
  · simp [state]
  · apply congrArg₂ StructuredProgram.State.mk <;> funext i <;> fin_cases i <;>
      simp [state, readRegs ]

private theorem copied15 (n l w : List Bool) :
    Eval (copyCmd (1 : Fin 6) 5 2) (7 * w.length + 5)
      (state n w l []) (state n w l w) := by
  convert copy_eval (1 : Fin 6) 5 2 (state n w l [])
    (by decide) (by decide) (by decide) rfl rfl using 1
  · simp [state]
  · apply congrArg₂ StructuredProgram.State.mk <;> funext i <;> fin_cases i <;>
      simp [state, readRegs ]

private theorem cleared1 (n l w : List Bool) :
    Eval (clearCmd (1 : Fin 6)) (2 * w.length + 3)
      (state n w l w) (state n [] l w) := by
  convert clear_eval (1 : Fin 6) (state n w l w) using 1
  · simp [state]
  · apply congrArg₂ StructuredProgram.State.mk <;> funext i <;> fin_cases i <;>
      simp [state, readRegs ]

theorem core_eval (n : List Bool) :
    ∃ l w t, CounterPrograms.value l = Asymptotic.L (CounterPrograms.value n) ∧
      CounterPrograms.value w = Asymptotic.w (CounterPrograms.value n) ∧
      l.length ≤ n.length + 17 ∧ w.length ≤ n.length + 18 ∧
      t ≤ 40000 * (n.length + 1)^2 ∧
      Eval core t (state n [] [] []) (state n [] l w) := by
  obtain ⟨l, t, hl, hlen, ht, he⟩ := Setup.computeL_eval n
  obtain ⟨w, u, hw, hwlen, hu, hf⟩ := Setup.logSucc_eval l
  have hreset : Eval (@RegisterResetProgram.all 8 6) 8
      (state n [] l w) (state n [] l w) := RegisterResetProgram.all_eval _
  refine ⟨l, w, (7*n.length+5)+((t+1)+((7*l.length+5)+
    ((u+1)+((7*w.length+5)+((2*w.length+3)+8))))), hl, ?_, hlen, by omega, ?_, ?_⟩
  · simpa only [hl, Asymptotic.w] using hw
  · nlinarith
  · exact (copied01 n).seq ((localCall_eval _ n n l [] [] he).seq
      ((copied14 n l).seq ((localCall_eval _ n l w l [] hf).seq
        ((copied15 n l w).seq ((cleared1 n l w).seq hreset)))))

/-- Incoming Boolean work registers may be dirty; they are physically reset.
Only the five non-input local stacks need to be empty. -/
theorem command_eval (n : List Bool) (regs : Fin 8 → Bool) :
    ∃ l w t, CounterPrograms.value l = Asymptotic.L (CounterPrograms.value n) ∧
      CounterPrograms.value w = Asymptotic.w (CounterPrograms.value n) ∧
      l.length ≤ n.length + 17 ∧ w.length ≤ n.length + 18 ∧
      t ≤ 40008 * (n.length + 1)^2 ∧
      Eval command t ⟨regs, (state n [] [] []).stacks⟩ (state n [] l w) := by
  obtain ⟨l, w, t, hl, hw, hlen, hwlen, ht, he⟩ := core_eval n
  refine ⟨l, w, 8+t, hl, hw, hlen, hwlen, by nlinarith, ?_⟩
  exact (RegisterResetProgram.all_eval _).seq he

end SubexponentialSAT.SqrtLog.Execution.SetupLocal

end OAI.Algorithms
