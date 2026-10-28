import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.ScoreBuilderRawInput
import OAI.Algorithms.SubexponentialSAT.Subexp.ScoreBuilderRefinement

namespace OAI.Algorithms

/-!
# The actual assignment program with generated pair-plan order

The pair table is literal runtime data. Its mathematical requirement is a
permutation of the complete pair table; no inverse decoding of vertex plans
and no canonical pair order is used by the program.
-/

namespace SubexponentialSAT.Subexp.ScoreBuilderRawRefinement

open BitProgram StructuredCalls MulticolorTypes SlotAssignment

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E]
variable {r Q Δ : ℕ} [NeZero r] (P : SubexponentialSAT.Factor.Pattern V E) (slots : SlotMap P Δ)

def cost (a : Word r Q) (tail : List (Word r Q)) (vertices : List V) (factors : List E)
    (rawPlans : List PairScoreProgram.PlanPair) (fixed : List (Word r Q)) (n : ℕ)
    (d : ScoreBuilderProgram.Data) : ℕ :=
  let M := (AssignmentEnumeration.seedIndices vertices factors Δ).length
  ScoreBuilderProgram.sourceBudget
    (ScoreBuilderRawInput.preparationContext M rawPlans d)
    (ScoreBuilderRawInput.context Δ (a :: tail) a fixed n M rawPlans d)

omit [Fintype V] [NeZero r] in
theorem run_from_memory (a : Word r Q) (tail : List (Word r Q))
    (vertices : List V) (factors : List E) (hv : ∀ v, v ∈ vertices) (he : ∀ e, e ∈ factors)
    (rawPlans : List PairScoreProgram.PlanPair) (pairs : List (V × V))
    (hraw : rawPlans.Perm
      (pairs.map (CandidateScoreRefinement.rawPairPlans P slots vertices factors)))
    (hpairs : pairs.Perm (vertices.product vertices))
    (fixed : List (Word r Q)) (n : ℕ) (d : ScoreBuilderProgram.Data)
    (hsize : n + 1 + fixed.length = (AssignmentEnumeration.seedIndices vertices factors Δ).length)
    (hm : SequentialProgram.Memory ReadPlan.encodeWord a tail (n + 1) fixed d.stacks)
    (hh : SequentialProgram.HighState
      (ScoreBuilderRawInput.environment Δ (a :: tail)
        (AssignmentEnumeration.seedIndices vertices factors Δ).length rawPlans) d.stacks) :
    ∃ t ≤ cost (Δ := Δ) a tail vertices factors rawPlans fixed n d,
      ∃ e : ScoreBuilderProgram.Data,
      Eval ScoreBuilderProgram.command t d e ∧
      e.stacks 0 = ProgramEncoding.encodeRecords ((a :: tail).map (fun candidate =>
        UnaryCompare.encode (NaturalAssignment.sequentialNumerator P slots (a :: tail) vertices
          (AssignmentEnumeration.seedIndices vertices factors Δ) a n (candidate :: fixed)))) ∧
      (∀ j : Fin 48, j ≠ 0 → e.stacks j = d.stacks j) := by
  have hi := ScoreBuilderRawInput.inputFor_of_memory Δ a tail fixed n
    (AssignmentEnumeration.seedIndices vertices factors Δ).length rawPlans d hm hh
  have hc := ScoreBuilderRawInput.candidate_valid_of_memory P slots a tail vertices factors
    hv he fixed n rawPlans pairs d hm hsize hraw
  obtain ⟨t, ht, regs, hrun⟩ := ScoreBuilderProgram.command_eval _ _ hc d hi
  refine ⟨t, ht.trans (Nat.sub_le _ _), _, hrun, ?_, ?_⟩
  · simp only [ScoreBuilderProgram.resultState, Function.update_same]
    exact ScoreBuilderRawInput.scoreBytes_eq P slots a tail vertices factors hv he
      fixed n rawPlans pairs d hm hsize hraw hpairs
  · intro j hj
    simp [ScoreBuilderProgram.resultState, hj]

omit [Fintype V] [NeZero r] in
theorem refines_of_cost_bound (a : Word r Q) (tail : List (Word r Q))
    (vertices : List V) (factors : List E) (hv : ∀ v, v ∈ vertices) (he : ∀ e, e ∈ factors)
    (rawPlans : List PairScoreProgram.PlanPair) (pairs : List (V × V))
    (hraw : rawPlans.Perm
      (pairs.map (CandidateScoreRefinement.rawPairPlans P slots vertices factors)))
    (hpairs : pairs.Perm (vertices.product vertices)) (B : ℕ)
    (hcost : ∀ n fixed (d : ScoreBuilderProgram.Data),
      n + 1 + fixed.length = (AssignmentEnumeration.seedIndices vertices factors Δ).length →
      SequentialProgram.Memory ReadPlan.encodeWord a tail (n + 1) fixed d.stacks →
      SequentialProgram.HighState
        (ScoreBuilderRawInput.environment Δ (a :: tail)
          (AssignmentEnumeration.seedIndices vertices factors Δ).length rawPlans) d.stacks →
      cost (Δ := Δ) a tail vertices factors rawPlans fixed n d ≤ B) :
    SequentialProgram.ScoreBuilderRefines ReadPlan.encodeWord a tail
      (NaturalAssignment.sequentialNumerator P slots (a :: tail) vertices
        (AssignmentEnumeration.seedIndices vertices factors Δ) a)
      ScoreBuilderProgram.command B (AssignmentEnumeration.seedIndices vertices factors Δ).length
      (ScoreBuilderRawInput.environment Δ (a :: tail)
        (AssignmentEnumeration.seedIndices vertices factors Δ).length rawPlans) := by
  intro n fixed d hsize hm _ hh
  obtain ⟨t, ht, e, heval, hout, hframe⟩ :=
    run_from_memory P slots a tail vertices factors hv he rawPlans pairs hraw hpairs
      fixed n d hsize hm hh
  refine ⟨t, ht.trans (hcost n fixed d hsize hm hh), e, heval, hout, ?_, ?_⟩
  · intro j _ hj
    exact hframe j hj
  · intro j hj
    rw [hframe j (by intro h; subst j; omega)]
    exact hh j hj

omit [Fintype V] [NeZero r] in
/-- The instruction table is exactly the previously defined fixed table;
only its input records and their proof of coverage vary. -/
theorem assignment_run (a : Word r Q) (tail : List (Word r Q))
    (haNodup : (a :: tail).Nodup) (haFull : ∀ w, w ∈ a :: tail)
    (vertices : List V) (factors : List E) (hv : ∀ v, v ∈ vertices) (he : ∀ e, e ∈ factors)
    (rawPlans : List PairScoreProgram.PlanPair) (pairs : List (V × V))
    (hraw : rawPlans.Perm
      (pairs.map (CandidateScoreRefinement.rawPairPlans P slots vertices factors)))
    (hpairs : pairs.Perm (vertices.product vertices)) (B : ℕ)
    (hcost : ∀ n fixed (d : ScoreBuilderProgram.Data),
      n + 1 + fixed.length = (AssignmentEnumeration.seedIndices vertices factors Δ).length →
      SequentialProgram.Memory ReadPlan.encodeWord a tail (n + 1) fixed d.stacks →
      SequentialProgram.HighState
        (ScoreBuilderRawInput.environment Δ (a :: tail)
          (AssignmentEnumeration.seedIndices vertices factors Δ).length rawPlans) d.stacks →
      cost (Δ := Δ) a tail vertices factors rawPlans fixed n d ≤ B) :
    let indices := AssignmentEnumeration.seedIndices vertices factors Δ
    let env := ScoreBuilderRawInput.environment Δ (a :: tail) indices.length rawPlans
    ∃ e : SequentialProgram.Data,
      RunsIn ScoreBuilderRefinement.assignmentProgram
        (indices.length * (B + SequentialProgram.selectionBudget (a :: tail).length
          (vertices.length ^ 2 * (blockSize r Q Δ) ^ 2) indices.length
          (ReadPlan.encodeWord a).length + 3) + 3)
        ((SequentialProgram.initialData ReadPlan.encodeWord a tail indices.length env).withPC
          (some ScoreBuilderRefinement.assignmentProgram.entry)) (e.withPC none) ∧
      e.stacks 8 = ((NaturalAssignment.naturalValues P slots a tail vertices indices).reverse.map
        ReadPlan.encodeWord).flatten := by
  exact SequentialProgram.naturalValues_program P slots ReadPlan.encodeWord a tail haNodup haFull
    vertices (AssignmentEnumeration.seedIndices vertices factors Δ) ScoreBuilderProgram.command B
    (ScoreBuilderRawInput.environment Δ (a :: tail)
      (AssignmentEnumeration.seedIndices vertices factors Δ).length rawPlans)
    (by intro x; simp [ReadPlan.encodeWord_length])
    (refines_of_cost_bound P slots a tail vertices factors hv he rawPlans pairs hraw hpairs B hcost)

end SubexponentialSAT.Subexp.ScoreBuilderRawRefinement

end OAI.Algorithms
