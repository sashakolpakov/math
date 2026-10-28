import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassAdapter

/-! Actual per-mark staging and return adapters. Each reference is copied and
reversed into the frontend marker words. Each completed high-assignment count
is moved to the marked collector, with its temporary words reclaimed and parser
registers reset by real instructions. Fresh high-query setup remains mandatory. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMarkedQueryAdapter

open BitProgram StructuredCalls SqrtLog LeafOuterProgram

abbrev Data := State 40 896
abbrev Code := Cmd 40 896

def markCopy (a : Data) : Data :=
  ⟨readRegs a.regs 0 1 none, StackRoutines.copyStacks 321 699 a.stacks⟩
def markTransfer (a : Data) : Data :=
  ⟨readRegs a.regs 0 1 none, StackRoutines.transferStacks 699 705 a.stacks⟩
def markResult (a : Data) : Data :=
  SubexpParameterProgram.runAtoms [.set 0 true, .push 706 0] (markTransfer (markCopy a))

def markInput : Code := .seq (.call (StackRoutines.copyProgram 321 699 698 0 1))
  (.seq (.call (StackRoutines.transferProgram 699 705 0 1))
    (.base (SubexpParameterProgram.atoms [.set 0 true, .push 706 0])))

/-- This is the original reverse-aware marker staging on the shared leaf bank. -/
theorem markInput_eval (a : Data) (h698 : a.stacks 698 = []) (h699 : a.stacks 699 = []) :
    Eval markInput (10 * (a.stacks 321).length + 10) a (markResult a) := by
  have hc := BankRoutines.copy_call_eval (321 : Fin 896) 699 698 (0 : Fin 40) 1
    (by decide) (by decide) (by decide) (by decide) a.regs a.stacks h698
  have ht : Eval (.call (StackRoutines.transferProgram (699 : Fin 896) 705 (0 : Fin 40) 1))
      (3 * ((markCopy a).stacks 699).length + 3) (markCopy a) (markTransfer (markCopy a)) :=
    Eval.call _ (ListRegisterProgram.transfer_run 699 705 0 1 (by decide) (by decide)
      (markCopy a).regs (markCopy a).stacks)
  have hf := Eval.base (SubexpParameterProgram.atoms_eval [.set (0 : Fin 40) true, .push 706 0]
    (markTransfer (markCopy a)))
  have hl : ((markCopy a).stacks 699).length = (a.stacks 321).length := by
    simp [markCopy, StackRoutines.copyStacks, h699]
  rw [hl] at ht
  convert hc.seq (ht.seq hf) using 1
  · rfl
  · simp only [List.length_cons, List.length_nil]
    omega
  · rfl

theorem markResult_stacks (a : Data) (h699 : a.stacks 699 = [])
    (h705 : a.stacks 705 = []) (h706 : a.stacks 706 = []) :
    (markResult a).stacks = Function.update (Function.update a.stacks 705
      (a.stacks 321).reverse) 706 [true] := by
  funext i
  by_cases h699i : i = 699 <;> by_cases h705i : i = 705 <;> by_cases h706i : i = 706 <;>
    simp [markResult, SubexpParameterProgram.runAtoms, StructuredProgram.Atom.eval,
      StructuredProgram.Atom.instr, execInstr, StructuredProgram.State.ofCfg,
      markCopy, markTransfer, StackRoutines.copyStacks,
      StackRoutines.transferStacks, h699, h705, h706, h699i, h705i, h706i]

theorem markInput_trace_space (a : Data) (L : ℕ)
    (ha : ∀ i, (a.stacks i).length ≤ L) (h698 : a.stacks 698 = []) (h699 : a.stacks 699 = []) :
    Trace (compiled markInput 321 705) (10 * (a.stacks 321).length + 11)
      (a.withPC (some (compiled markInput 321 705).entry)) ((markResult a).withPC none) ∧
      ∀ k c, k ≤ 10 * (a.stacks 321).length + 11 →
        Trace (compiled markInput 321 705) k
          (a.withPC (some (compiled markInput 321 705).entry)) c →
          ∀ i, (c.stacks i).length ≤ 906 * L + 11 := by
  refine ⟨compiled_halt_trace (markInput_eval a h698 h699) 321 705, ?_⟩
  intro k c hk hc i
  have hstart : dataBits (a.withPC (some (compiled markInput 321 705).entry)) ≤ 896 * L :=
    StreamResources.dataBits_le_mul _ ha
  have h := StructuredSpace.local_stack_bound (compiled markInput 321 705)
    (steps := 10 * L + 11) hstart k c (by have := ha 321; omega) hc i
  omega

/-- These words are freshly created by the marker/high-query invocation and
must have been empty at its external entry. No shared-H assumption is used. -/
def cleanupPorts : List (Fin 896) :=
  [321,330,698,699,705,706,788,789,790,791,792,793,794]

def resetParser : Code := .base (SubexpParameterProgram.atoms
  [.set 16 false, .set 17 true, .set 18 false])
def parserReset (a : Data) : Data := SubexpParameterProgram.runAtoms
  [.set 16 false, .set 17 true, .set 18 false] a

def clearState (a : Data) : Data :=
  ⟨readRegs a.regs 0 1 none, BankRoutines.clearBankStacks cleanupPorts a.stacks⟩

def finish : Code := .seq (route (788,323))
  (.seq (BankRoutines.clearCmd 767 0 1 cleanupPorts) resetParser)
def finishState (a : Data) : Data := parserReset (clearState (routed (788,323) a))
def finishSteps (a : Data) : ℕ := routeCost (788,323) a +
  (2 * (cleanupPorts.map fun i => ((routed (788,323) a).stacks i).length).sum +
    3 * cleanupPorts.length + 3 + 3)

theorem finish_eval (a : Data) (ht : a.stacks 767 = []) :
    Eval finish (finishSteps a) a (finishState a) := by
  have hr := route_eval (788,323) (by unfold routeValid; decide) a ht
  have hc := BankRoutines.clear_eval (767 : Fin 896) (0 : Fin 40) 1 cleanupPorts
    (by decide) (routed (788,323) a).regs (routed (788,323) a).stacks
    (by simpa [routed] using ht)
  have hp := Eval.base (SubexpParameterProgram.atoms_eval
    [.set (16 : Fin 40) false, .set 17 true, .set 18 false]
    (clearState (routed (788,323) a)))
  exact hr.seq (hc.seq hp)

theorem finishState_stacks (a : Data) :
    (finishState a).stacks = BankRoutines.clearBankStacks cleanupPorts
      (Function.update a.stacks 323 (a.stacks 788)) := by
  rfl

theorem finishState_count (a : Data) : (finishState a).stacks 323 = a.stacks 788 := by
  simp [finishState_stacks, BankRoutines.clearBankStacks, cleanupPorts]

theorem finishState_clean (a : Data) (i : Fin 896) (hi : i ∈ cleanupPorts) :
    (finishState a).stacks i = [] := by
  simp [finishState_stacks, BankRoutines.clearBankStacks, hi]

theorem finishState_frame (a : Data) (i : Fin 896) (hi : i ∉ cleanupPorts) (h323 : i ≠ 323) :
    (finishState a).stacks i = a.stacks i := by
  simp [finishState_stacks, BankRoutines.clearBankStacks, hi, h323]

theorem finishState_parser (a : Data) :
    (finishState a).regs 16 = false ∧ (finishState a).regs 17 = true ∧
      (finishState a).regs 18 = false := by
  simp [finishState, parserReset, SubexpParameterProgram.runAtoms, StructuredProgram.Atom.eval,
    StructuredProgram.Atom.instr, execInstr, StructuredProgram.State.ofCfg]

theorem finish_steps_le (a : Data) (L : ℕ) (ha : ∀ i, (a.stacks i).length ≤ L) :
    finishSteps a ≤ 35 * L + 53 := by
  have hsum : (cleanupPorts.map fun i => ((routed (788,323) a).stacks i).length).sum ≤ 13 * L := by
    have h := List.sum_le_length_nsmul
      (cleanupPorts.map fun i => ((routed (788,323) a).stacks i).length) L
      (by
        intro x hx
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
        by_cases h323 : i = 323
        · subst i; simpa [routed] using ha 788
        simpa [routed, h323] using ha i)
    simpa [cleanupPorts] using h
  have hs := ha 788
  have hd := ha 323
  simp only [finishSteps, routeCost, cleanupPorts, List.length_cons, List.length_nil] at *
  omega

theorem finish_trace_space (a : Data) (L : ℕ)
    (ha : ∀ i, (a.stacks i).length ≤ L) (ht : a.stacks 767 = []) :
    Trace (compiled finish 788 323) (finishSteps a + 1)
      (a.withPC (some (compiled finish 788 323).entry)) ((finishState a).withPC none) ∧
      ∀ k c, k ≤ finishSteps a + 1 → Trace (compiled finish 788 323) k
        (a.withPC (some (compiled finish 788 323).entry)) c →
        ∀ i, (c.stacks i).length ≤ 931 * L + 54 := by
  refine ⟨compiled_halt_trace (finish_eval a ht) 788 323, ?_⟩
  intro k c hk hc i
  have hstart : dataBits (a.withPC (some (compiled finish 788 323).entry)) ≤ 896 * L :=
    StreamResources.dataBits_le_mul _ ha
  have hsteps := finish_steps_le a L ha
  have h := StructuredSpace.local_stack_bound (compiled finish 788 323)
    (steps := 35 * L + 54) hstart k c (by omega) hc i
  omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMarkedQueryAdapter
