import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.BlockSearchPrepared
import OAI.Algorithms.SubexponentialSAT.Subexp.BlockSearchOuter

namespace OAI.Algorithms

/-! The fixed tuple preparation runs in the actual search machine's frame. -/

namespace SubexponentialSAT.Subexp.BlockSearchSetup

open BitProgram StructuredCalls BlockSearchLoop BlockSearchNested BlockSearchOuter

def registers (i : Fin 15) : Fin 24 := Fin.castAdd 9 i
def stackMap (i : Fin 22) : Fin 42 := Fin.castAdd 20 i

theorem registers_injective : Function.Injective registers := Fin.castAdd_injective _ _
theorem stacks_injective : Function.Injective stackMap := Fin.castAdd_injective _ _

abbrev command : Cmd 24 42 :=
  .call (ProgramLinking.liftProgram BlockSearchPreparation.program registers stackMap)

def contextStacks (ctx : Context) (j : Fin 42) : List Bool :=
  if j = 27 then ctx.modulus else if j = 36 then ctx.zeroWord else
    if j = 38 then ctx.matrix else if j = 39 then ctx.rowCount else []

/-- All variable dimensions and field data are runtime stack contents. -/
def inputState (ctx : Context) (alphabet : List (List Bool))
    (tableDepth vectorDepth : List Bool) (regs : Fin 24 → Bool) : StructuredProgram.State 24 42 :=
  ⟨regs, fun j => if h : j.val < 22 then
    (BlockSearchPreparation.inputState alphabet tableDepth vectorDepth
      (regs ∘ registers)).stacks ⟨j.val, h⟩ else contextStacks ctx j⟩

theorem input_low (ctx : Context) (alphabet : List (List Bool))
    (tableDepth vectorDepth : List Bool) (regs : Fin 24 → Bool) (i : Fin 22) :
    (inputState ctx alphabet tableDepth vectorDepth regs).stacks (stackMap i) =
      (BlockSearchPreparation.inputState alphabet tableDepth vectorDepth
        (regs ∘ registers)).stacks i := by
  simp [inputState, stackMap, i.isLt]

theorem input_high (ctx : Context) (alphabet : List (List Bool))
    (tableDepth vectorDepth : List Bool) (regs : Fin 24 → Bool) (j : Fin 42)
    (hj : 22 ≤ j.val) :
    (inputState ctx alphabet tableDepth vectorDepth regs).stacks j = contextStacks ctx j := by
  simp [inputState, Nat.not_lt.mpr hj]

theorem command_eval (ctx : Context) (alphabet : List (List Bool))
    (tableDepth vectorDepth : List Bool) (regs : Fin 24 → Bool) (tableLimit : ℕ)
    (hdimension : ctx.dimension = List.replicate vectorDepth.length true) :
    ∃ n next, n ≤ BlockSearchPreparation.cost alphabet tableDepth vectorDepth ∧
      TableEntry ctx (TupleProgram.powerRows alphabet vectorDepth.length [[]])
        (DimensionProgram.dimensionRows 0 vectorDepth.length) vectorDepth.length tableLimit next ∧
      next.stacks 0 = ProgramEncoding.encodeRecords
        (TupleProgram.powerRows alphabet tableDepth.length [[]]) ∧ next.stacks 2 = [] ∧
      Eval command n (inputState ctx alphabet tableDepth vectorDepth regs) next := by
  let start := inputState ctx alphabet tableDepth vectorDepth regs
  have hrestrict : BlockSearchPreparation.restrictState registers stackMap start =
      BlockSearchPreparation.inputState alphabet tableDepth vectorDepth (regs ∘ registers) := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      exact input_low ctx alphabet tableDepth vectorDepth regs i
  obtain ⟨b, hp, hc, hr⟩ := BlockSearchPrepared.program_runsIn_clean alphabet tableDepth
    vectorDepth (regs ∘ registers)
  have hr' : RunsIn BlockSearchPreparation.program
      (BlockSearchPreparation.cost alphabet tableDepth vectorDepth)
      ((BlockSearchPreparation.restrictState registers stackMap start).withPC
        (some BlockSearchPreparation.program.entry)) (b.withPC none) := by
    simpa only [hrestrict] using hr
  obtain ⟨n, hn, he⟩ := BlockSearchPreparation.lifted_call BlockSearchPreparation.program
    registers stackMap registers_injective stacks_injective start b _ hr'
  let next := embedState registers stackMap start b
  have low (i : Fin 22) : next.stacks (stackMap i) = b.stacks i :=
    embedState_stack _ _ _ _ stacks_injective i
  have high (j : Fin 42) (hj : 22 ≤ j.val) : next.stacks j = contextStacks ctx j := by
    have h := embedState_stack_frame registers stackMap start b j (by
      rintro ⟨i, hi⟩
      have hv := congrArg Fin.val hi
      change i.val = j.val at hv
      omega)
    exact h.trans (input_high ctx alphabet tableDepth vectorDepth regs j hj)
  have h8 : next.stacks 8 = [] := (low 8).trans hc.2.2.2.2.2.1
  have h9 : next.stacks 9 = [] := (low 9).trans hc.2.2.2.2.2.2
  have h41 : next.stacks 41 = [] := by simpa [contextStacks] using high 41 (by decide)
  refine ⟨n, next, hn, ?_, (low 0).trans hp.1, (low 2).trans hc.1, he⟩
  refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_, rfl, rfl, ?_⟩, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · simpa [contextStacks] using high 27 (by decide)
  · simpa [contextStacks] using high 36 (by decide)
  · simpa [contextStacks] using high 38 (by decide)
  · simpa [contextStacks] using high 39 (by decide)
  · exact ((low 10).trans hp.2.2.2.2).trans hdimension.symm
  · refine ⟨h9, ?_⟩
    intro j hj h27 h36 h38 h39 h41
    simpa [contextStacks, h27, h36, h38, h39] using high j hj
  · exact (low 14).trans hp.2.2.2.1
  · exact (low 6).trans hc.2.2.2.1
  · exact (low 7).trans hc.2.2.2.2.1
  · simp [h8]
  · exact (low 12).trans hp.2.2.1
  · exact (low 3).trans hc.2.1
  · exact (low 4).trans hc.2.2.1
  · simp [h41]

end SubexponentialSAT.Subexp.BlockSearchSetup

end OAI.Algorithms
