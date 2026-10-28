import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpNodeStageCopies
import OAI.Algorithms.SubexponentialSAT.SubexpNodeJobsStage
import OAI.Algorithms.SubexponentialSAT.SubexpMomentSourceHost

namespace OAI.Algorithms

/-! Physical source/grid readiness after the node's actual context copies,
and cleanup of that context after the generated jobs have reached port 100. -/

namespace SubexponentialSAT.SubexpNodeJobsReady

open BitProgram StructuredCalls SubexpScanPrimitives
open SubexpNodeCacheSetup
open SubexpNodeStageCopies

abbrev Context := SubexpMomentSourceProgram.Context

attribute [local simp] Fin.coe_ofNat_eq_mod

def sourcePort (i : Fin 63) : Fin 256 :=
  SubexpNodeJobsStage.port (SubexpMomentSourceHost.ports i)

theorem sourcePort_injective : Function.Injective sourcePort :=
  SubexpNodeJobsStage.port_injective.comp SubexpMomentSourceHost.ports_injective

def copiedPorts : List (Fin 256) := jobMoves.map Prod.snd

/-- These are stored-word and empty-workspace facts before the real copies.
The already-produced template is the only occupied source-service port. -/
structure Ready (d : Data) (ctx : Context) : Prop where
  sourceWidth : d.stacks 129 = ctx.width
  targetWidth : d.stacks 10 = ctx.target
  modulus : d.stacks 5 = ctx.modulus
  unit : d.stacks 124 = ctx.unit
  dimension : d.stacks 109 = List.replicate ctx.dimension true
  indexWidth : d.stacks 92 = List.replicate ctx.indexWidth true
  zero : d.stacks 122 = ctx.zero
  one : d.stacks 123 = ctx.one
  template : d.stacks 200 = ctx.template
  indexExact : ctx.indexWidth = SubexpSymbolicCost.indexBits ctx.dimension
  scratch : d.stacks 0 = []
  work : ∀ i : Fin 63, i ≠ 62 → d.stacks (sourcePort i) = []

def preparedStacks (s : Store) : Store :=
  Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update s
      140 (s 109)) 141 (s 92)) 161 (s 129)) 162 (s 10)) 163 (s 5))
      164 (s 124)) 197 (s 122)) 198 (s 123)

theorem Ready.destinations {d : Data} {ctx : Context} (h : Ready d ctx) :
    ∀ i ∈ copiedPorts, d.stacks i = [] := by
  intro i hi
  simp only [copiedPorts, jobMoves, List.map_cons, List.map_nil,
    List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h.work 27 (by decide)
  · exact h.work 28 (by decide)
  · exact h.work 23 (by decide)
  · exact h.work 24 (by decide)
  · exact h.work 25 (by decide)
  · exact h.work 26 (by decide)
  · exact h.work 59 (by decide)
  · exact h.work 60 (by decide)

theorem copied_stacks (d : Data) (hempty : ∀ i ∈ copiedPorts, d.stacks i = []) :
    (copied jobMoves d).stacks = preparedStacks d.stacks := by
  have h140 := hempty 140 (by simp [copiedPorts, jobMoves])
  have h141 := hempty 141 (by simp [copiedPorts, jobMoves])
  have h161 := hempty 161 (by simp [copiedPorts, jobMoves])
  have h162 := hempty 162 (by simp [copiedPorts, jobMoves])
  have h163 := hempty 163 (by simp [copiedPorts, jobMoves])
  have h164 := hempty 164 (by simp [copiedPorts, jobMoves])
  have h197 := hempty 197 (by simp [copiedPorts, jobMoves])
  have h198 := hempty 198 (by simp [copiedPorts, jobMoves])
  simp [copied, jobMoves, afterCopy, StackRoutines.copyStacks, preparedStacks,
    h140, h141, h161, h162, h163, h164, h197, h198]

theorem prepared_frame (s : Store) (i : Fin 256) (hi : i ∉ copiedPorts) :
    preparedStacks s i = s i := by
  have hh : i ≠ 140 ∧ i ≠ 141 ∧ i ≠ 161 ∧ i ≠ 162 ∧ i ≠ 163 ∧
      i ≠ 164 ∧ i ≠ 197 ∧ i ≠ 198 := by
    simpa only [copiedPorts, jobMoves, List.map_cons, List.map_nil,
      List.mem_cons, List.not_mem_nil, or_false, not_or] using hi
  simp [preparedStacks, hh.1, hh.2.1, hh.2.2.1, hh.2.2.2.1, hh.2.2.2.2.1,
    hh.2.2.2.2.2.1, hh.2.2.2.2.2.2.1, hh.2.2.2.2.2.2.2]

private theorem source_state_stack (ctx : Context) (r : Fin 8 → Bool) (i : Fin 63) :
    (SubexpMomentSourceProgram.state {ctx with exponent := []} r []
      SubexpBlockAssembly.emptyBuffers [] [] [] []).stacks i =
    if i = 23 then ctx.width else if i = 24 then ctx.target
    else if i = 25 then ctx.modulus else if i = 26 then ctx.unit
    else if i = 27 then List.replicate ctx.dimension true
    else if i = 28 then List.replicate ctx.indexWidth true
    else if i = 59 then ctx.zero else if i = 60 then ctx.one
    else if i = 62 then ctx.template else [] := by
  fin_cases i <;> rfl

/-- Readiness is derived from the real copied state, not supplied as a source
execution contract. No source bytes or source-service output are assumed. -/
theorem ready_source (d : Data) (ctx : Context) (h : Ready d ctx) :
    SubexpMomentSourceHost.Ready {ctx with exponent := []}
      (SubexpNodeJobsStage.project (copied jobMoves d)) := by
  apply state_ext
  · rfl
  · funext i
    change (copied jobMoves d).stacks (sourcePort i) = _
    rw [copied_stacks d h.destinations, source_state_stack]
    by_cases h23 : i = 23
    · subst i; simpa [preparedStacks, sourcePort, SubexpNodeJobsStage.port,
        SubexpMomentSourceHost.ports] using h.sourceWidth
    by_cases h24 : i = 24
    · subst i; simpa [preparedStacks, sourcePort, SubexpNodeJobsStage.port,
        SubexpMomentSourceHost.ports] using h.targetWidth
    by_cases h25 : i = 25
    · subst i; simpa [preparedStacks, sourcePort, SubexpNodeJobsStage.port,
        SubexpMomentSourceHost.ports] using h.modulus
    by_cases h26 : i = 26
    · subst i; simpa [preparedStacks, sourcePort, SubexpNodeJobsStage.port,
        SubexpMomentSourceHost.ports] using h.unit
    by_cases h27 : i = 27
    · subst i; simpa [preparedStacks, sourcePort, SubexpNodeJobsStage.port,
        SubexpMomentSourceHost.ports] using h.dimension
    by_cases h28 : i = 28
    · subst i; simpa [preparedStacks, sourcePort, SubexpNodeJobsStage.port,
        SubexpMomentSourceHost.ports] using h.indexWidth
    by_cases h59 : i = 59
    · subst i; simpa [preparedStacks, sourcePort, SubexpNodeJobsStage.port,
        SubexpMomentSourceHost.ports] using h.zero
    by_cases h60 : i = 60
    · subst i; simpa [preparedStacks, sourcePort, SubexpNodeJobsStage.port,
        SubexpMomentSourceHost.ports] using h.one
    have hi : sourcePort i ∉ copiedPorts := by
      intro hi
      simp only [copiedPorts, jobMoves, List.map_cons, List.map_nil,
        List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with hi | hi | hi | hi | hi | hi | hi | hi
      · exact h27 (sourcePort_injective hi)
      · exact h28 (sourcePort_injective hi)
      · exact h23 (sourcePort_injective hi)
      · exact h24 (sourcePort_injective hi)
      · exact h25 (sourcePort_injective hi)
      · exact h26 (sourcePort_injective hi)
      · exact h59 (sourcePort_injective hi)
      · exact h60 (sourcePort_injective hi)
    rw [prepared_frame _ _ hi]
    by_cases h62 : i = 62
    · subst i; simpa [sourcePort, SubexpNodeJobsStage.port,
        SubexpMomentSourceHost.ports] using h.template
    · simp only [h23, h24, h25, h26, h27, h28, h59, h60, h62, ite_false]
      exact h.work i h62

theorem ready_grid (d : Data) (ctx : Context) (h : Ready d ctx) :
    SubexpOuterJobs.Context (SubexpNodeJobsStage.project (copied jobMoves d))
      ctx.dimension (SubexpSymbolicCost.indexBits ctx.dimension) := by
  have hs := ready_source d ctx h
  have hp (i : Fin 63) := congrArg
    (fun x : StructuredProgram.State 8 63 => x.stacks i) hs
  constructor
  · exact hp 27
  · have hw := hp 28
    change (SubexpNodeJobsStage.project (copied jobMoves d)).stacks 3 =
      List.replicate ctx.indexWidth true at hw
    simpa only [h.indexExact] using hw
  · intro i hi
    simp only [SubexpOuterJobs.work, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hp 4
    · exact hp 5
    · exact hp 6
    · exact hp 7
    · exact hp 8
    · exact hp 9
    · exact hp 10
    · exact hp 11
    · exact hp 12
    · exact hp 15
    · exact hp 17

theorem prepare_eval (d : Data) (ctx : Context) (h : Ready d ctx) :
    Eval prepareJobs (copyCost jobMoves d) d (copied jobMoves d) ∧
    SubexpMomentSourceHost.Ready {ctx with exponent := []}
      (SubexpNodeJobsStage.project (copied jobMoves d)) ∧
    SubexpOuterJobs.Context (SubexpNodeJobsStage.project (copied jobMoves d))
      ctx.dimension (SubexpSymbolicCost.indexBits ctx.dimension) :=
  ⟨prepareJobs_eval d h.scratch, ready_source d ctx h, ready_grid d ctx h⟩

def contextSize (ctx : Context) : ℕ :=
  ctx.dimension + ctx.indexWidth + ctx.width.length + ctx.target.length +
    ctx.modulus.length + ctx.unit.length + ctx.zero.length + ctx.one.length

theorem prepare_cost (d : Data) (ctx : Context) (h : Ready d ctx) :
    copyCost jobMoves d = 7 * contextSize ctx + 40 := by
  rw [job_cost, h.dimension, h.indexWidth, h.sourceWidth, h.targetWidth,
    h.modulus, h.unit, h.zero, h.one]
  simp only [contextSize, List.length_replicate]

/-- The template is consumed at this stage; the generated jobs stay on 100. -/
def finishedStacks (s : Store) (output : List Bool) : Store :=
  Function.update (Function.update s 200 []) 100 output

theorem finished_frame (s : Store) (output : List Bool) (i : Fin 256)
    (h100 : i ≠ 100) (h200 : i ≠ 200) : finishedStacks s output i = s i := by
  simp only [finishedStacks, Function.update_of_ne h100, Function.update_of_ne h200]

theorem clearJobs_cost (e : Data) :
    clearCost jobWork e = 2 * ((e.stacks 140).length + (e.stacks 141).length +
      (e.stacks 161).length + (e.stacks 162).length + (e.stacks 163).length +
      (e.stacks 164).length + (e.stacks 197).length + (e.stacks 198).length +
      (e.stacks 200).length) + 27 := by
  simp [clearCost, jobWork, clearOut]
  omega

theorem clearJobs_stacks (d e : Data) (output : List Bool)
    (hempty : ∀ i ∈ copiedPorts, d.stacks i = [])
    (he : e.stacks = Function.update (copied jobMoves d).stacks 100 output) :
    (cleared jobWork e).stacks = finishedStacks d.stacks output := by
  funext i
  rw [cleared_stacks]
  by_cases hi : i ∈ jobWork
  · rw [ite_eq_left hi]
    by_cases h200 : i = 200
    · subst i; simp [finishedStacks]
    have hm : i ∈ copiedPorts := by
      simpa only [jobWork, copiedPorts, jobMoves, List.map_cons, List.map_nil,
        List.mem_cons, List.not_mem_nil, or_false, h200, or_false] using hi
    have h100 : i ≠ 100 := by
      intro heq; subst i; simp [copiedPorts, jobMoves] at hm
    rw [finished_frame _ _ _ h100 h200, hempty i hm]
  · rw [ite_eq_right hi, he, copied_stacks d hempty]
    have hm : i ∉ copiedPorts := by
      intro him
      apply hi
      simp only [copiedPorts, jobMoves, List.map_cons, List.map_nil,
        List.mem_cons, List.not_mem_nil, or_false] at him
      rcases him with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [jobWork]
    have h200 : i ≠ 200 := by
      intro heq; subst i; exact hi (by simp [jobWork])
    by_cases h100 : i = 100
    · subst i; simp [finishedStacks]
    · simp only [finishedStacks, Function.update_of_ne h100,
        Function.update_of_ne h200, prepared_frame _ _ hm]

theorem cleanup_cost (d e : Data) (ctx : Context) (output : List Bool)
    (h : Ready d ctx)
    (he : e.stacks = Function.update (copied jobMoves d).stacks 100 output) :
    clearCost jobWork e = 2 * (contextSize ctx + ctx.template.length) + 27 := by
  rw [clearJobs_cost, he, copied_stacks d h.destinations]
  simp [preparedStacks, contextSize, h.sourceWidth, h.targetWidth, h.modulus, h.unit,
    h.dimension, h.indexWidth, h.zero, h.one, h.template]

theorem clearJobs_eval_exact (d e : Data) (ctx : Context) (output : List Bool)
    (h : Ready d ctx)
    (he : e.stacks = Function.update (copied jobMoves d).stacks 100 output) :
    Eval clearJobs (2 * (contextSize ctx + ctx.template.length) + 27)
      e (cleared jobWork e) ∧
    (cleared jobWork e).stacks = finishedStacks d.stacks output := by
  refine ⟨?_, clearJobs_stacks d e output h.destinations he⟩
  rw [← cleanup_cost d e ctx output h he]
  exact SubexpNodeStageCopies.clearJobs_eval e

theorem clearJobs_work (e : Data) :
    ∀ i ∈ jobWork, (cleared jobWork e).stacks i = [] := by
  intro i hi
  simp only [cleared_stacks, ite_eq_left hi]

theorem clearJobs_output (d e : Data) (ctx : Context) (output : List Bool)
    (h : Ready d ctx)
    (he : e.stacks = Function.update (copied jobMoves d).stacks 100 output) :
    (cleared jobWork e).stacks 100 = output := by
  rw [clearJobs_stacks d e output h.destinations he]
  simp [finishedStacks]

theorem clearJobs_frame (d e : Data) (ctx : Context) (output : List Bool)
    (h : Ready d ctx)
    (he : e.stacks = Function.update (copied jobMoves d).stacks 100 output)
    (i : Fin 256) (h100 : i ≠ 100) (h200 : i ≠ 200) :
    (cleared jobWork e).stacks i = d.stacks i := by
  rw [clearJobs_stacks d e output h.destinations he]
  exact finished_frame d.stacks output i h100 h200

end SubexponentialSAT.SubexpNodeJobsReady

end OAI.Algorithms
