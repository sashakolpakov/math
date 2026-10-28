import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpNodeCacheSetup

namespace OAI.Algorithms

/-!
# Physical arithmetic contexts between node stages

Source-field arithmetic for template construction uses source caches128--131.
Weight arithmetic uses the target modulus and target-width scalar one. The
two copy lists make that distinction explicit in the finite program.
-/

namespace SubexponentialSAT.SubexpNodeStageCopies

open BitProgram StructuredCalls SubexpNodeCacheSetup

def templateMoves : List Move :=
  [(128,204), (130,211), (129,212), (10,217), (131,228),
    (5,230), (121,231), (109,232), (92,233)]

def jobMoves : List Move :=
  [(109,140), (92,141), (129,161), (10,162),
    (5,163), (124,164), (122,197), (123,198)]

def templateWork : List (Fin 256) := [204,211,212,217,228,230,231,232,233]
def jobWork : List (Fin 256) := [140,141,161,162,163,164,197,198,200]

abbrev prepareTemplate : Cmd 16 256 := copies templateMoves
abbrev prepareJobs : Cmd 16 256 := copies jobMoves
abbrev clearTemplate : Cmd 16 256 := clears templateWork
abbrev clearJobs : Cmd 16 256 := clears jobWork

theorem templateMoves_valid :
    ∀ m ∈ templateMoves, m.1 ≠ m.2 ∧ m.1 ≠ 0 ∧ m.2 ≠ 0 := by
  intro m hm
  simp only [templateMoves, List.mem_cons, List.mem_nil_iff, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem jobMoves_valid :
    ∀ m ∈ jobMoves, m.1 ≠ m.2 ∧ m.1 ≠ 0 ∧ m.2 ≠ 0 := by
  intro m hm
  simp only [jobMoves, List.mem_cons, List.mem_nil_iff, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem prepareTemplate_eval (d : Data) (h0 : d.stacks 0 = []) :
    Eval prepareTemplate (copyCost templateMoves d) d (copied templateMoves d) :=
  copies_eval templateMoves d h0 templateMoves_valid

theorem prepareJobs_eval (d : Data) (h0 : d.stacks 0 = []) :
    Eval prepareJobs (copyCost jobMoves d) d (copied jobMoves d) :=
  copies_eval jobMoves d h0 jobMoves_valid

theorem template_cost (d : Data) : copyCost templateMoves d =
    7 * ((d.stacks 128).length + (d.stacks 130).length + (d.stacks 129).length +
      (d.stacks 10).length + (d.stacks 131).length + (d.stacks 5).length +
      (d.stacks 121).length + (d.stacks 109).length + (d.stacks 92).length) + 45 := by
  simp [templateMoves, copyCost, SubexpScanPrimitives.afterCopy, StackRoutines.copyStacks]
  omega

theorem job_cost (d : Data) : copyCost jobMoves d =
    7 * ((d.stacks 109).length + (d.stacks 92).length + (d.stacks 129).length +
      (d.stacks 10).length + (d.stacks 5).length + (d.stacks 124).length +
      (d.stacks 122).length + (d.stacks 123).length) + 40 := by
  simp [jobMoves, copyCost, SubexpScanPrimitives.afterCopy, StackRoutines.copyStacks]
  omega

theorem clearTemplate_eval (d : Data) :
    Eval clearTemplate (clearCost templateWork d) d (cleared templateWork d) :=
  clears_eval templateWork d

/-- Run after jobs have reached100. This clears the reusable node template
and only the copied job context; the generated job stream remains intact. -/
theorem clearJobs_eval (d : Data) :
    Eval clearJobs (clearCost jobWork d) d (cleared jobWork d) :=
  clears_eval jobWork d

theorem clearJobs_output (d : Data) : (cleared jobWork d).stacks 100 = d.stacks 100 := by
  simp [cleared_stacks, jobWork]

theorem template_target_frame (d : Data) (i : Fin 256)
    (hi : i ∈ ([5,10,25,91,92,109,119,120,121,122,123,124,126,127,255] : List (Fin 256))) :
    (copied templateMoves d).stacks i = d.stacks i := by
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl <;>
    simp [copied, templateMoves, SubexpScanPrimitives.afterCopy, StackRoutines.copyStacks]

theorem job_target_frame (d : Data) (i : Fin 256)
    (hi : i ∈ ([5,10,25,91,92,109,119,120,121,122,123,124,126,127,255] : List (Fin 256))) :
    (copied jobMoves d).stacks i = d.stacks i := by
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl <;>
    simp [copied, jobMoves, SubexpScanPrimitives.afterCopy, StackRoutines.copyStacks]

end SubexponentialSAT.SubexpNodeStageCopies

end OAI.Algorithms
