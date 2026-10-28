import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.CounterConversions
import OAI.Algorithms.SubexponentialSAT.SubexpScanPrimitives
import OAI.Algorithms.SubexponentialSAT.RegisterResetProgram
import OAI.Algorithms.SubexponentialSAT.ProgramFrames

namespace OAI.Algorithms

/-! Physical runtime-counter preparation and cleanup for the Main basis batch. -/

namespace SubexponentialSAT.SubexpLocalBasisPrepare

open BitProgram StructuredCalls SubexpScanPrimitives

abbrev Data := State 32 131

abbrev clear (i : Fin 131) : Cmd 32 131 := .call (StackRoutines.clearProgram i 0 1)
def cleared (i : Fin 131) (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.clearStacks i d.stacks⟩

theorem clear_eval (i : Fin 131) (d : Data) :
    Eval (clear i) (2 * (d.stacks i).length + 3) d (cleared i d) := by
  apply Eval.call
  have ht := StackRoutines.clearProgram_trace i (0 : Fin 32) 1 d.regs d.stacks
  have hh := StackRoutines.halt_after_trace _ ht 2 rfl rfl
  simpa [cleared, StackRoutines.clearResult, StructuredProgram.State.withPC,
    Nat.add_assoc] using hh

def conversionRegisters : Fin 3 → Fin 32 := Fin.castAdd 29
def conversionPorts : Fin 3 → Fin 131 := ![129, 111, 130]

theorem conversionRegisters_injective : Function.Injective conversionRegisters := by
  intro i j h
  exact Fin.ext (congrArg (fun q : Fin 32 => q.val) h)
theorem conversionPorts_injective : Function.Injective conversionPorts := by decide

abbrev convertCounter : Cmd 32 131 := .call (ProgramLinking.liftProgram
  CounterConversions.unaryProgram conversionRegisters conversionPorts)

theorem conversionPorts_range (i : Fin 3) :
    conversionPorts i = 129 ∨ conversionPorts i = 111 ∨ conversionPorts i = 130 := by
  fin_cases i <;> simp [conversionPorts]

/-- A true-unary counter is produced by the concrete binary-counter loop. -/
theorem convertCounter_eval (d : Data)
    (h111 : d.stacks 111 = []) (h130 : d.stacks 130 = []) :
    ∃ n e, n ≤ CounterConversions.runtimeBound (d.stacks 129) ∧
      Eval convertCounter n d e ∧
      e.stacks = Function.update (Function.update d.stacks 129 []) 111
        (List.replicate (CounterPrograms.value (d.stacks 129)) true) := by
  let input := CounterConversions.state (d.regs ∘ conversionRegisters) (d.stacks 129) []
  let output := CounterConversions.state CounterConversions.zeroRegs []
    (List.replicate (CounterPrograms.value (d.stacks 129)) true)
  have hi : embedState conversionRegisters conversionPorts d input = d := by
    apply embedState_eq_of_ports _ _ _ _ _ conversionRegisters_injective conversionPorts_injective
    · intro i; rfl
    · intros; rfl
    · intro i
      fin_cases i <;> simp [input, CounterConversions.state, conversionPorts, h111, h130]
    · intros; rfl
  obtain ⟨n, hn, ht⟩ := CounterConversions.unary_runs (d.regs ∘ conversionRegisters)
    (d.stacks 129) []
  simp only [List.append_nil] at ht
  let e := embedState conversionRegisters conversionPorts d output
  have he := eval_call_lifted CounterConversions.unaryProgram conversionRegisters conversionPorts
    d conversionRegisters_injective conversionPorts_injective ht
  change Eval convertCounter n (embedState conversionRegisters conversionPorts d input) e at he
  rw [hi] at he
  refine ⟨n, e, hn, he, ?_⟩
  funext i
  by_cases h129i : i = 129
  · subst i
    have hs := embedState_stack conversionRegisters conversionPorts d output conversionPorts_injective 0
    simpa [e, output, conversionPorts, CounterConversions.state] using hs
  by_cases h111i : i = 111
  · subst i
    have hs := embedState_stack conversionRegisters conversionPorts d output conversionPorts_injective 1
    simpa [e, output, conversionPorts, CounterConversions.state] using hs
  by_cases h130i : i = 130
  · subst i
    have hs := embedState_stack conversionRegisters conversionPorts d output conversionPorts_injective 2
    simpa [e, output, conversionPorts, CounterConversions.state, h130] using hs
  · have hi : ¬ ∃ j, conversionPorts j = i := by
      rintro ⟨j, hj⟩
      have hr := conversionPorts_range j
      rw [hj] at hr
      exact hr.elim h129i (fun h => h.elim h111i h130i)
    simpa [e, h129i, h111i] using
      embedState_stack_frame conversionRegisters conversionPorts d output i hi

abbrev copyCounter : Cmd 32 131 := .call (StackRoutines.copyProgram 128 129 130 0 1)

abbrev prepare : Cmd 32 131 :=
  .seq (clear 111) (.seq (clear 127) (.seq copyCounter convertCounter))

def prepareCost (d : Data) : ℕ :=
  2 * (d.stacks 111).length + 2 * (d.stacks 127).length +
    7 * (d.stacks 128).length + CounterConversions.runtimeBound (d.stacks 128) + 11

theorem prepare_eval (d : Data) (h129 : d.stacks 129 = []) (h130 : d.stacks 130 = []) :
    ∃ n e, n ≤ prepareCost d ∧ Eval prepare n d e ∧
      e.stacks = Function.update (Function.update d.stacks 127 []) 111
        (List.replicate (CounterPrograms.value (d.stacks 128)) true) := by
  let d1 := cleared 111 d
  let d2 := cleared 127 d1
  let d3 := afterCopy d2 128 129 0 1
  have h1 := clear_eval 111 d
  have h2 := clear_eval 127 d1
  have h3 := copy_eval d2 128 129 130 0 1
    (by decide) (by decide) (by decide) (by decide)
    (by simpa [d2, d1, cleared, StackRoutines.clearStacks] using h130)
  have hsrc : d3.stacks 129 = d.stacks 128 := by
    simp [d3, d2, d1, cleared, afterCopy, StackRoutines.clearStacks,
      StackRoutines.copyStacks, h129]
  obtain ⟨n, e, hn, he, hs⟩ := convertCounter_eval d3
    (by simp [d3, d2, d1, cleared, afterCopy, StackRoutines.clearStacks, StackRoutines.copyStacks])
    (by simpa [d3, d2, d1, cleared, afterCopy, StackRoutines.clearStacks,
      StackRoutines.copyStacks] using h130)
  have htotal := h1.seq (h2.seq (h3.seq he))
  refine ⟨_, e, ?_, htotal, ?_⟩
  · rw [hsrc] at hn
    simp only [d2, d1, cleared, StackRoutines.clearStacks,
      Function.update_of_ne (by decide : (127 : Fin 131) ≠ 111),
      Function.update_of_ne (by decide : (128 : Fin 131) ≠ 127),
      Function.update_of_ne (by decide : (128 : Fin 131) ≠ 111)]
    unfold prepareCost
    omega
  · rw [hs, hsrc]
    funext i
    by_cases hi111 : i = 111
    · subst i; simp
    by_cases hi127 : i = 127
    · subst i
      simp [d3, d2, d1, cleared, afterCopy, StackRoutines.clearStacks, StackRoutines.copyStacks]
    by_cases hi129 : i = 129
    · subst i; simp [h129]
    simp [d3, d2, d1, cleared, afterCopy, StackRoutines.clearStacks,
      StackRoutines.copyStacks, hi111, hi127, hi129]

abbrev finish : Cmd 32 131 :=
  .seq (clear 111) (.seq (clear 114) RegisterResetProgram.all)

def finishCost (d : Data) : ℕ := 2 * (d.stacks 111).length + 2 * (d.stacks 114).length + 38

def finished (d : Data) : Data :=
  ⟨fun _ => false, Function.update (Function.update d.stacks 111 []) 114 []⟩

theorem finish_eval (d : Data) : Eval finish (finishCost d) d (finished d) := by
  have h1 := clear_eval 111 d
  have h2 := clear_eval 114 (cleared 111 d)
  have h3 := RegisterResetProgram.all_eval (cleared 114 (cleared 111 d))
  have h := h1.seq (h2.seq h3)
  convert h using 1
  · simp [finishCost, cleared, StackRoutines.clearStacks]
    omega
  · simp [finished, RegisterResetProgram.zeroed, cleared, StackRoutines.clearStacks]

end SubexponentialSAT.SubexpLocalBasisPrepare

end OAI.Algorithms
