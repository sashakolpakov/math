import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.CounterConversions
import OAI.Algorithms.SubexponentialSAT.Subexp.UnaryCompare
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames
import OAI.Algorithms.SubexponentialSAT.ProgramFrames

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingWeightProgram.Gate
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev Data := State 4 7
abbrev Code := Cmd 4 7

def copy (src dst : Fin 7) : Code := .call (StackRoutines.copyProgram src dst 6 0 1)
def copied (d : Data) (src dst : Fin 7) : Data :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.copyStacks src dst d.stacks⟩
theorem copy_eval (d : Data) (src dst : Fin 7) (hne : src ≠ dst)
    (hs : src ≠ 6) (ht : (6 : Fin 7) ≠ dst) (h6 : d.stacks 6 = []) :
    Eval (copy src dst) (7 * (d.stacks src).length + 5) d (copied d src dst) :=
  .call _ (ListRegisterProgram.copy_run src dst 6 0 1 hne hs ht (by decide)
    d.regs d.stacks h6)

def clear (j : Fin 7) : Code := .call (StackRoutines.clearProgram j 0 1)
def cleared (d : Data) (j : Fin 7) : Data :=
  ⟨readRegs d.regs 0 1 none, Function.update d.stacks j []⟩
theorem clear_eval (d : Data) (j : Fin 7) :
    Eval (clear j) (2 * (d.stacks j).length + 3) d (cleared d j) :=
  .call _ (ListRegisterProgram.clear_run j 0 1 d.regs d.stacks)

def unaryRegisters : Fin 3 → Fin 4 := Fin.castAdd 1
def unaryStacks : Fin 3 → Fin 7 := ![3,4,6]
theorem unaryRegisters_injective : Function.Injective unaryRegisters := Fin.castAdd_injective _ _
theorem unaryStacks_injective : Function.Injective unaryStacks := by decide
def convert : Code := liftCommand CounterConversions.unaryCmd 0 1 unaryRegisters unaryStacks

theorem convert_eval (d : Data) (h4 : d.stacks 4 = []) (h6 : d.stacks 6 = []) :
    ∃ t ≤ CounterConversions.runtimeBound (d.stacks 3), ∃ e : Data,
      Eval convert t d e ∧ e.stacks 3 = [] ∧
      e.stacks 4 = List.replicate (CounterPrograms.value (d.stacks 3)) true ∧
      (∀ j, j ≠ 3 → j ≠ 4 → e.stacks j = d.stacks j) := by
  let a := projectState unaryRegisters unaryStacks d
  obtain ⟨t, ht, hb⟩ := CounterConversions.unary_correct a h6
  let b := CounterConversions.state CounterConversions.zeroRegs []
    (List.replicate (CounterPrograms.value (a.stacks 0)) true ++ a.stacks 1)
  let e := embedState unaryRegisters unaryStacks d b
  have he := eval_liftCommand_from_state CounterConversions.unaryCmd 0 1
    unaryRegisters unaryStacks d unaryRegisters_injective unaryStacks_injective ht
  have hbound := CounterConversions.coreBound_le (d.stacks 3)
  change t ≤ CounterConversions.coreBound (d.stacks 3) at hb
  refine ⟨t+1, by omega, e, he, ?_, ?_, ?_⟩
  · exact embedState_stack unaryRegisters unaryStacks d b unaryStacks_injective 0
  · have h := embedState_stack unaryRegisters unaryStacks d b unaryStacks_injective 1
    simpa [e, b, a, projectState, unaryStacks, CounterConversions.state, h4] using h
  · intro j hj3 hj4
    by_cases hj6 : j = 6
    · subst j
      have h := embedState_stack unaryRegisters unaryStacks d b unaryStacks_injective 2
      simpa [e, b, unaryStacks, CounterConversions.state, h6] using h
    · apply embedState_stack_frame
      rintro ⟨i, rfl⟩
      fin_cases i <;> simp [unaryStacks] at hj3 hj4 hj6

def compareStacks : Fin 2 → Fin 7 := ![4,5]
theorem compareStacks_injective : Function.Injective compareStacks := by decide
def compare : Code := .call (ProgramLinking.liftProgram Subexp.UnaryCompare.program id compareStacks)

theorem compare_eval (d : Data) :
    ∃ t ≤ 4 * min (d.stacks 4).length (d.stacks 5).length + 6, ∃ e : Data,
      Eval compare t d e ∧
      e.regs 3 = decide ((d.stacks 4).length ≤ (d.stacks 5).length) ∧
      (e.stacks 4).length ≤ (d.stacks 4).length ∧
      (e.stacks 5).length ≤ (d.stacks 5).length ∧
      (∀ j, j ≠ 4 → j ≠ 5 → e.stacks j = d.stacks j) := by
  obtain ⟨t, hb, c, ht, hpc, hf⟩ := Subexp.UnaryCompare.runs d.regs (d.stacks 4) (d.stacks 5)
  let a : State 4 2 := ⟨c.regs, c.stacks⟩
  have hc : a.withPC none = c := by cases c; simp_all [a, StructuredProgram.State.withPC]
  have hp : Subexp.UnaryCompare.start d.regs (d.stacks 4) (d.stacks 5) =
      (projectState id compareStacks d).withPC (some Subexp.UnaryCompare.program.entry) := by
    change Cfg.mk _ _ _ = Cfg.mk _ _ _
    congr 1
    funext i; fin_cases i <;> rfl
  rw [hp, ← hc] at ht
  let e := embedState id compareStacks d a
  have he := eval_call_from_state Subexp.UnaryCompare.program id compareStacks d
    Function.injective_id compareStacks_injective ht
  have hs (i : Fin 2) : e.stacks (compareStacks i) = c.stacks i :=
    embedState_stack _ _ _ _ compareStacks_injective i
  refine ⟨t, hb, e, he, ?_, ?_, ?_, ?_⟩
  · exact (embedState_register _ _ _ _ Function.injective_id 3).trans hf
  · have h := Subexp.UnaryCompare.trace_length_le ht 0
    change (c.stacks 0).length ≤ (d.stacks 4).length at h
    have he : e.stacks 4 = c.stacks 0 := by simpa [compareStacks] using hs 0
    rw [he]
    exact h
  · have h := Subexp.UnaryCompare.trace_length_le ht 1
    change (c.stacks 1).length ≤ (d.stacks 5).length at h
    have he : e.stacks 5 = c.stacks 1 := by simpa [compareStacks] using hs 1
    rw [he]
    exact h
  · intro j hj4 hj5
    apply embedState_stack_frame
    rintro ⟨i, rfl⟩
    fin_cases i <;> simp [compareStacks] at hj4 hj5

end SubexponentialSAT.SqrtLog.PackingWeightProgram.Gate

end OAI.Algorithms
