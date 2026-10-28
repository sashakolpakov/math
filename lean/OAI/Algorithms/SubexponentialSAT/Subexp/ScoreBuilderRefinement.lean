import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.ScoreBuilderInput
import OAI.Algorithms.SubexponentialSAT.Subexp.SequentialStep

namespace OAI.Algorithms

/-!
# Exact refinement of the fixed score builder

The execution theorem below starts from the actual controller memory and
encoded read-only tables. Its output is the natural conditional objective in
the exact order consumed by the first-minimum routine.
-/

namespace SubexponentialSAT.Subexp.ScoreBuilderRefinement

open BitProgram StructuredCalls MulticolorTypes SlotAssignment

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E]
variable {r Q Δ : ℕ} [NeZero r] (P : SubexponentialSAT.Factor.Pattern V E) (slots : SlotMap P Δ)

def cost (a : Word r Q) (tail : List (Word r Q)) (vertices : List V) (factors : List E)
    (pairs : List (V × V)) (fixed : List (Word r Q)) (n : ℕ) (d : ScoreBuilderProgram.Data) : ℕ :=
  ScoreBuilderProgram.sourceBudget
    (ScoreBuilderInput.preparationContext P slots vertices factors pairs d)
    (ScoreBuilderInput.context P slots (a :: tail) vertices factors a fixed n pairs d)

omit [Fintype V] [NeZero r] in
theorem run_from_memory (a : Word r Q) (tail : List (Word r Q))
    (vertices : List V) (factors : List E) (hv : ∀ v, v ∈ vertices) (he : ∀ e, e ∈ factors)
    (pairs : List (V × V)) (hpairs : pairs.Perm (vertices.product vertices))
    (fixed : List (Word r Q)) (n : ℕ) (d : ScoreBuilderProgram.Data)
    (hsize : n + 1 + fixed.length = (AssignmentEnumeration.seedIndices vertices factors Δ).length)
    (hm : SequentialProgram.Memory ReadPlan.encodeWord a tail (n + 1) fixed d.stacks)
    (hh : SequentialProgram.HighState
      (ScoreBuilderInput.environment P slots (a :: tail) vertices factors pairs) d.stacks) :
    ∃ t ≤ cost P slots a tail vertices factors pairs fixed n d, ∃ e : ScoreBuilderProgram.Data,
      Eval ScoreBuilderProgram.command t d e ∧
      e.stacks 0 = ProgramEncoding.encodeRecords ((a :: tail).map (fun candidate =>
        UnaryCompare.encode (NaturalAssignment.sequentialNumerator P slots (a :: tail) vertices
          (AssignmentEnumeration.seedIndices vertices factors Δ) a n (candidate :: fixed)))) ∧
      (∀ j : Fin 48, j ≠ 0 → e.stacks j = d.stacks j) := by
  have hi := ScoreBuilderInput.inputFor_of_memory P slots a tail vertices factors fixed n pairs d hm hh
  have hc := ScoreBuilderInput.candidate_valid_of_memory P slots a tail vertices factors
    hv he fixed n pairs d hm hsize
  obtain ⟨t, ht, regs, hrun⟩ := ScoreBuilderProgram.command_eval _ _ hc d hi
  refine ⟨t, ht.trans (Nat.sub_le _ _), _, hrun, ?_, ?_⟩
  · simp only [ScoreBuilderProgram.resultState, Function.update_same]
    exact ScoreBuilderInput.scoreBytes_eq P slots a tail vertices factors hv he
      fixed n pairs d hm hsize hpairs
  · intro j hj
    simp [ScoreBuilderProgram.resultState, hj]

omit [Fintype V] [NeZero r] in
/-- The remaining premise is a uniform numerical bound on an already proved
instruction count, not an assumed execution of a score oracle. -/
theorem refines_of_cost_bound (a : Word r Q) (tail : List (Word r Q))
    (vertices : List V) (factors : List E) (hv : ∀ v, v ∈ vertices) (he : ∀ e, e ∈ factors)
    (pairs : List (V × V)) (hpairs : pairs.Perm (vertices.product vertices)) (B : ℕ)
    (hcost : ∀ n fixed (d : ScoreBuilderProgram.Data),
      n + 1 + fixed.length = (AssignmentEnumeration.seedIndices vertices factors Δ).length →
      SequentialProgram.Memory ReadPlan.encodeWord a tail (n + 1) fixed d.stacks →
      SequentialProgram.HighState
        (ScoreBuilderInput.environment P slots (a :: tail) vertices factors pairs) d.stacks →
      cost P slots a tail vertices factors pairs fixed n d ≤ B) :
    SequentialProgram.ScoreBuilderRefines ReadPlan.encodeWord a tail
      (NaturalAssignment.sequentialNumerator P slots (a :: tail) vertices
        (AssignmentEnumeration.seedIndices vertices factors Δ) a)
      ScoreBuilderProgram.command B (AssignmentEnumeration.seedIndices vertices factors Δ).length
      (ScoreBuilderInput.environment P slots (a :: tail) vertices factors pairs) := by
  intro n fixed d hsize hm _ hh
  obtain ⟨t, ht, e, heval, hout, hframe⟩ :=
    run_from_memory P slots a tail vertices factors hv he pairs hpairs fixed n d hsize hm hh
  refine ⟨t, ht.trans (hcost n fixed d hsize hm hh), e, heval, hout, ?_, ?_⟩
  · intro j _ hj
    exact hframe j hj
  · intro j hj
    rw [hframe j (by intro h; subst j; omega)]
    exact hh j hj

/-- One fixed controller, independent of all mathematical parameters. -/
def assignmentProgram := SequentialProgram.program ScoreBuilderProgram.command

omit [Fintype V] [NeZero r] in
theorem assignment_run (a : Word r Q) (tail : List (Word r Q))
    (haNodup : (a :: tail).Nodup) (haFull : ∀ w, w ∈ a :: tail)
    (vertices : List V) (factors : List E) (hv : ∀ v, v ∈ vertices) (he : ∀ e, e ∈ factors)
    (pairs : List (V × V)) (hpairs : pairs.Perm (vertices.product vertices)) (B : ℕ)
    (hcost : ∀ n fixed (d : ScoreBuilderProgram.Data),
      n + 1 + fixed.length = (AssignmentEnumeration.seedIndices vertices factors Δ).length →
      SequentialProgram.Memory ReadPlan.encodeWord a tail (n + 1) fixed d.stacks →
      SequentialProgram.HighState
        (ScoreBuilderInput.environment P slots (a :: tail) vertices factors pairs) d.stacks →
      cost P slots a tail vertices factors pairs fixed n d ≤ B) :
    let indices := AssignmentEnumeration.seedIndices vertices factors Δ
    let env := ScoreBuilderInput.environment P slots (a :: tail) vertices factors pairs
    ∃ e : SequentialProgram.Data,
      RunsIn assignmentProgram
        (indices.length * (B + SequentialProgram.selectionBudget (a :: tail).length
          (vertices.length ^ 2 * (blockSize r Q Δ) ^ 2) indices.length
          (ReadPlan.encodeWord a).length + 3) + 3)
        ((SequentialProgram.initialData ReadPlan.encodeWord a tail indices.length env).withPC
          (some assignmentProgram.entry)) (e.withPC none) ∧
      e.stacks 8 = ((NaturalAssignment.naturalValues P slots a tail vertices indices).reverse.map
        ReadPlan.encodeWord).flatten := by
  exact SequentialProgram.naturalValues_program P slots ReadPlan.encodeWord a tail haNodup haFull
    vertices (AssignmentEnumeration.seedIndices vertices factors Δ) ScoreBuilderProgram.command B
    (ScoreBuilderInput.environment P slots (a :: tail) vertices factors pairs)
    (by intro x; simp [ReadPlan.encodeWord_length])
    (refines_of_cost_bound P slots a tail vertices factors hv he pairs hpairs B hcost)

end SubexponentialSAT.Subexp.ScoreBuilderRefinement

end OAI.Algorithms
