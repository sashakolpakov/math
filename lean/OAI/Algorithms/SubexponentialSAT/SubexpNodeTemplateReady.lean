import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpNodeStageCopies
import OAI.Algorithms.SubexponentialSAT.SubexpNodeTemplateStage
import OAI.Algorithms.SubexponentialSAT.SubexpTemplateState

namespace OAI.Algorithms

/-! Physical readiness and context cleanup for the node-template call. -/

namespace SubexponentialSAT.SubexpNodeTemplateReady

open BitProgram StructuredCalls SubexpScanPrimitives
open SubexpNodeCacheSetup
open SubexpNodeStageCopies
open SubexpNodeTemplateStage (port localState)
open SubexpTemplateProgram (Context serviceState)

attribute [local simp] Fin.coe_ofNat_eq_mod

structure Ready (d : Data) (ctx : Context) (raw : List Bool) : Prop where
  sourceModulus : d.stacks 128 = ctx.sourceModulus
  sourceReduction : d.stacks 130 = ctx.sourceReduction
  sourceWidth : d.stacks 129 = ctx.sourceWidth
  sourceZero : d.stacks 131 = ctx.sourceZero
  targetWidth : d.stacks 10 = ctx.targetWidth
  targetModulus : d.stacks 5 = ctx.targetModulus
  targetMinusOne : d.stacks 121 = ctx.targetMinusOne
  dimension : d.stacks 109 = List.replicate ctx.dimension true
  indexWidth : d.stacks 92 = List.replicate ctx.indexWidth true
  input : d.stacks 15 = raw
  work : ∀ i : Fin 142, i ≠ 130 → d.stacks (port i) = []

def preparedStacks (s : Store) : Store :=
  Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update
      (Function.update s 204 (s 128)) 211 (s 130)) 212 (s 129)) 217 (s 10))
      228 (s 131)) 230 (s 5)) 231 (s 121)) 232 (s 109)) 233 (s 92)

theorem Ready.zero {d : Data} {ctx : Context} {raw : List Bool}
    (h : Ready d ctx raw) : d.stacks 0 = [] := h.work 117 (by decide)

theorem Ready.destinations {d : Data} {ctx : Context} {raw : List Bool}
    (h : Ready d ctx raw) : ∀ i ∈ templateWork, d.stacks i = [] := by
  intro i hi
  simp only [templateWork, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h.work 66 (by decide)
  · exact h.work 73 (by decide)
  · exact h.work 74 (by decide)
  · exact h.work 79 (by decide)
  · exact h.work 90 (by decide)
  · exact h.work 92 (by decide)
  · exact h.work 93 (by decide)
  · exact h.work 94 (by decide)
  · exact h.work 95 (by decide)

theorem copied_stacks (d : Data) (hempty : ∀ i ∈ templateWork, d.stacks i = []) :
    (copied templateMoves d).stacks = preparedStacks d.stacks := by
  have h204 := hempty 204 (by simp [templateWork])
  have h211 := hempty 211 (by simp [templateWork])
  have h212 := hempty 212 (by simp [templateWork])
  have h217 := hempty 217 (by simp [templateWork])
  have h228 := hempty 228 (by simp [templateWork])
  have h230 := hempty 230 (by simp [templateWork])
  have h231 := hempty 231 (by simp [templateWork])
  have h232 := hempty 232 (by simp [templateWork])
  have h233 := hempty 233 (by simp [templateWork])
  simp [copied, templateMoves, afterCopy, StackRoutines.copyStacks, preparedStacks,
    h204, h211, h212, h217, h228, h230, h231, h232, h233]

theorem prepared_frame (s : Store) (i : Fin 256) (hi : i ∉ templateWork) :
    preparedStacks s i = s i := by
  have hh : i ≠ 204 ∧ i ≠ 211 ∧ i ≠ 212 ∧ i ≠ 217 ∧ i ≠ 228 ∧ i ≠ 230 ∧
      i ≠ 231 ∧ i ≠ 232 ∧ i ≠ 233 := by
    simpa only [templateWork, List.mem_cons, List.not_mem_nil, or_false, not_or] using hi
  simp [preparedStacks, hh.1, hh.2.1, hh.2.2.1, hh.2.2.2.1, hh.2.2.2.2.1,
    hh.2.2.2.2.2.1, hh.2.2.2.2.2.2.1, hh.2.2.2.2.2.2.2.1, hh.2.2.2.2.2.2.2.2]

/-- The copies install precisely the native template context. No execution
of the template program is assumed to establish its input state. -/
theorem ready_serviceState (d : Data) (ctx : Context) (raw : List Bool)
    (h : Ready d ctx raw) :
    localState (copied templateMoves d) =
      serviceState ctx (localState (copied templateMoves d)).regs raw := by
  apply state_ext
  · rfl
  · funext i
    change (copied templateMoves d).stacks (port i) = _
    rw [copied_stacks d h.destinations]
    by_cases h66 : i = 66
    · subst i; simpa [port, Equiv.swap_apply_def, SubexpNodeTemplateStage.basePort,
        preparedStacks, serviceState,
        SubexpTemplateProgram.state_stack_eq]
        using h.sourceModulus
    by_cases h73 : i = 73
    · subst i; simpa [port, Equiv.swap_apply_def, SubexpNodeTemplateStage.basePort,
        preparedStacks, serviceState,
        SubexpTemplateProgram.state_stack_eq]
        using h.sourceReduction
    by_cases h74 : i = 74
    · subst i; simpa [port, Equiv.swap_apply_def, SubexpNodeTemplateStage.basePort,
        preparedStacks, serviceState,
        SubexpTemplateProgram.state_stack_eq]
        using h.sourceWidth
    by_cases h79 : i = 79
    · subst i; simpa [port, Equiv.swap_apply_def, SubexpNodeTemplateStage.basePort,
        preparedStacks, serviceState,
        SubexpTemplateProgram.state_stack_eq]
        using h.targetWidth
    by_cases h90 : i = 90
    · subst i; simpa [port, Equiv.swap_apply_def, SubexpNodeTemplateStage.basePort,
        preparedStacks, serviceState,
        SubexpTemplateProgram.state_stack_eq]
        using h.sourceZero
    by_cases h92 : i = 92
    · subst i; simpa [port, Equiv.swap_apply_def, SubexpNodeTemplateStage.basePort,
        preparedStacks, serviceState,
        SubexpTemplateProgram.state_stack_eq]
        using h.targetModulus
    by_cases h93 : i = 93
    · subst i; simpa [port, Equiv.swap_apply_def, SubexpNodeTemplateStage.basePort,
        preparedStacks, serviceState,
        SubexpTemplateProgram.state_stack_eq]
        using h.targetMinusOne
    by_cases h94 : i = 94
    · subst i; simpa [port, Equiv.swap_apply_def, SubexpNodeTemplateStage.basePort,
        preparedStacks, serviceState,
        SubexpTemplateProgram.state_stack_eq]
        using h.dimension
    by_cases h95 : i = 95
    · subst i; simpa [port, Equiv.swap_apply_def, SubexpNodeTemplateStage.basePort,
        preparedStacks, serviceState,
        SubexpTemplateProgram.state_stack_eq]
        using h.indexWidth
    have hport : port i ∉ templateWork := by
      intro hi
      simp only [templateWork, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with hi | hi | hi | hi | hi | hi | hi | hi | hi
      · exact h66 (SubexpNodeTemplateStage.port_injective hi)
      · exact h73 (SubexpNodeTemplateStage.port_injective hi)
      · exact h74 (SubexpNodeTemplateStage.port_injective hi)
      · exact h79 (SubexpNodeTemplateStage.port_injective hi)
      · exact h90 (SubexpNodeTemplateStage.port_injective hi)
      · exact h92 (SubexpNodeTemplateStage.port_injective hi)
      · exact h93 (SubexpNodeTemplateStage.port_injective hi)
      · exact h94 (SubexpNodeTemplateStage.port_injective hi)
      · exact h95 (SubexpNodeTemplateStage.port_injective hi)
    rw [prepared_frame _ _ hport]
    by_cases h130 : i = 130
    · subst i
      simpa [serviceState, SubexpTemplateProgram.state_stack_eq] using h.input
    · rw [h.work i h130]
      simp [serviceState, SubexpTemplateProgram.state_stack_eq, h66, h73, h74, h79,
        h90, h92, h93, h94, h95, h130]

theorem prepare_eval (d : Data) (ctx : Context) (raw : List Bool) (h : Ready d ctx raw) :
    Eval prepareTemplate (copyCost templateMoves d) d (copied templateMoves d) ∧
      localState (copied templateMoves d) =
        serviceState ctx (localState (copied templateMoves d)).regs raw :=
  ⟨prepareTemplate_eval d h.zero, ready_serviceState d ctx raw h⟩

def contextSize (ctx : Context) : ℕ :=
  ctx.sourceModulus.length + ctx.sourceReduction.length + ctx.sourceWidth.length +
    ctx.targetWidth.length + ctx.sourceZero.length + ctx.targetModulus.length +
    ctx.targetMinusOne.length + ctx.dimension + ctx.indexWidth

theorem prepare_cost (d : Data) (ctx : Context) (raw : List Bool) (h : Ready d ctx raw) :
    copyCost templateMoves d = 7 * contextSize ctx + 45 := by
  rw [template_cost, h.sourceModulus, h.sourceReduction, h.sourceWidth, h.targetWidth,
    h.sourceZero, h.targetModulus, h.targetMinusOne, h.dimension, h.indexWidth]
  simp only [List.length_replicate, contextSize]

/-- The stack effect returned by the actual template execution and its
Taylor-cache cleanup. This is only the common endpoint expression. -/
def finishedStacks (s : Store) (output : List Bool) : Store :=
  fun i => if i ∈ cleanupPorts then [] else Function.update (Function.update s 15 []) 200 output i

theorem finished_frame (s : Store) (output : List Bool) (i : Fin 256)
    (hi : i ∉ cleanupPorts) (h15 : i ≠ 15) (h200 : i ≠ 200) :
    finishedStacks s output i = s i := by
  simp only [finishedStacks, ite_eq_right hi, Function.update_of_ne h200, Function.update_of_ne h15]

theorem clearTemplate_cost (e : Data) :
    clearCost templateWork e =
      2 * ((e.stacks 204).length + (e.stacks 211).length + (e.stacks 212).length +
        (e.stacks 217).length + (e.stacks 228).length + (e.stacks 230).length +
        (e.stacks 231).length + (e.stacks 232).length + (e.stacks 233).length) + 27 := by
  simp [clearCost, templateWork, clearOut]
  omega

/-- Clearing the nine copied context words restores their original empty
cells. The actual template result and the earlier cache cleanup are retained. -/
theorem clearTemplate_stacks (d e : Data) (output : List Bool)
    (hempty : ∀ i ∈ templateWork, d.stacks i = [])
    (he : e.stacks = finishedStacks (copied templateMoves d).stacks output) :
    (cleared templateWork e).stacks = finishedStacks d.stacks output := by
  funext i
  rw [cleared_stacks]
  by_cases hi : i ∈ templateWork
  · rw [ite_eq_left hi]
    have hc : i ∉ cleanupPorts ∧ i ≠ 15 ∧ i ≠ 200 := by
      simp only [templateWork, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [cleanupPorts]
    rw [finished_frame _ _ _ hc.1 hc.2.1 hc.2.2, hempty i hi]
  · rw [ite_eq_right hi, he, copied_stacks d hempty]
    simp only [finishedStacks, Function.update_apply, prepared_frame d.stacks i hi]

theorem cleanup_cost (d e : Data) (ctx : Context) (raw output : List Bool)
    (h : Ready d ctx raw)
    (he : e.stacks = finishedStacks (copied templateMoves d).stacks output) :
    clearCost templateWork e = 2 * contextSize ctx + 27 := by
  rw [clearTemplate_cost, he, copied_stacks d h.destinations]
  simp [finishedStacks, cleanupPorts, preparedStacks, contextSize, h.sourceModulus,
    h.sourceReduction, h.sourceWidth, h.targetWidth, h.sourceZero, h.targetModulus,
    h.targetMinusOne, h.dimension, h.indexWidth]

theorem clearTemplate_eval_exact (d e : Data) (ctx : Context) (raw output : List Bool)
    (h : Ready d ctx raw)
    (he : e.stacks = finishedStacks (copied templateMoves d).stacks output) :
    Eval clearTemplate (2 * contextSize ctx + 27) e (cleared templateWork e) ∧
      (cleared templateWork e).stacks = finishedStacks d.stacks output := by
  refine ⟨?_, clearTemplate_stacks d e output h.destinations he⟩
  rw [← cleanup_cost d e ctx raw output h he]
  exact SubexpNodeStageCopies.clearTemplate_eval e

theorem clearTemplate_output (d e : Data) (ctx : Context) (raw output : List Bool)
    (h : Ready d ctx raw)
    (he : e.stacks = finishedStacks (copied templateMoves d).stacks output) :
    (cleared templateWork e).stacks 200 = output := by
  rw [clearTemplate_stacks d e output h.destinations he]
  simp [finishedStacks, cleanupPorts]

theorem clearTemplate_frame (d e : Data) (ctx : Context) (raw output : List Bool)
    (h : Ready d ctx raw)
    (he : e.stacks = finishedStacks (copied templateMoves d).stacks output)
    (i : Fin 256) (hi : i ∉ cleanupPorts) (h15 : i ≠ 15) (h200 : i ≠ 200) :
    (cleared templateWork e).stacks i = d.stacks i := by
  rw [clearTemplate_stacks d e output h.destinations he]
  exact finished_frame d.stacks output i hi h15 h200

end SubexponentialSAT.SubexpNodeTemplateReady

end OAI.Algorithms
