import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.InitializedAssignmentProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.ScoreBuilderRawRefinement

namespace OAI.Algorithms

/-! Physical initialization and assignment with the actual generated pair order. -/

namespace SubexponentialSAT.Subexp.InitializedRawAssignmentProgram

open BitProgram StructuredCalls MulticolorTypes SlotAssignment

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E]
variable {r Q Δ : ℕ} [NeZero r] (P : SubexponentialSAT.Factor.Pattern V E) (slots : SlotMap P Δ)

def initialContext (a : Word r Q) (tail : List (Word r Q))
    (vertices : List V) (factors : List E) (rawPlans : List PairScoreProgram.PlanPair) :
    AssignmentInitProgram.Context where
  defaultWord := ReadPlan.encodeWord a
  packedAlphabet := ((a :: tail).map ReadPlan.encodeWord).flatten
  alphabetRecords := ProgramEncoding.encodeRecords ((a :: tail).map ReadPlan.encodeWord)
  width := List.replicate (ReadPlan.encodeWord a).length true
  depth := List.replicate (2 * (Δ + 1)) true
  rawPairs := PairScoreProgram.pairRecords rawPlans
  seedRecords := PairPreparationProgram.seedBytes
    (AssignmentEnumeration.seedIndices vertices factors Δ).length
  seedCount := (AssignmentEnumeration.seedIndices vertices factors Δ).length

/-- No new instruction table is introduced for a different pair order. -/
abbrev program := InitializedAssignmentProgram.program

def sourceBudget (a : Word r Q) (tail : List (Word r Q))
    (vertices : List V) (factors : List E) (rawPlans : List PairScoreProgram.PlanPair)
    (scoreBound : ℕ) : ℕ :=
  let M := (AssignmentEnumeration.seedIndices vertices factors Δ).length
  AssignmentInitProgram.sourceCost (initialContext (Δ := Δ) a tail vertices factors rawPlans) +
    (M * (scoreBound + SequentialProgram.selectionBudget (a :: tail).length
      (vertices.length ^ 2 * (blockSize r Q Δ) ^ 2) M
      (ReadPlan.encodeWord a).length + 3) + 3) + 1

omit [Fintype V] [NeZero r] in
theorem program_run_framed (a : Word r Q) (tail : List (Word r Q))
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
      ScoreBuilderRawRefinement.cost (Δ := Δ) a tail vertices factors rawPlans fixed n d ≤ B)
    (regs : Fin 16 → Bool) :
    ∃ e : SequentialProgram.Data,
      RunsIn program (sourceBudget (Δ := Δ) a tail vertices factors rawPlans B)
        ((AssignmentInitProgram.inputState
          (initialContext (Δ := Δ) a tail vertices factors rawPlans) regs).withPC
            (some program.entry)) (e.withPC none) ∧
      SequentialProgram.Memory ReadPlan.encodeWord a tail 0
        (NaturalAssignment.naturalValues P slots a tail vertices
          (AssignmentEnumeration.seedIndices vertices factors Δ)) e.stacks ∧
      e.stacks 11 = [] ∧
      SequentialProgram.HighState
        (ScoreBuilderRawInput.environment Δ (a :: tail)
          (AssignmentEnumeration.seedIndices vertices factors Δ).length rawPlans) e.stacks := by
  have hb := ScoreBuilderRawRefinement.refines_of_cost_bound P slots a tail vertices factors
    hv he rawPlans pairs hraw hpairs B hcost
  exact InitializedAssignmentProgram.run_of_refines_framed ReadPlan.encodeWord a tail
    (NaturalAssignment.sequentialNumerator P slots (a :: tail) vertices
      (AssignmentEnumeration.seedIndices vertices factors Δ) a)
    (initialContext (Δ := Δ) a tail vertices factors rawPlans)
    (ScoreBuilderRawInput.environment Δ (a :: tail)
      (AssignmentEnumeration.seedIndices vertices factors Δ).length rawPlans)
    B (vertices.length ^ 2 * (blockSize r Q Δ) ^ 2)
    rfl rfl (by simp [initialContext]) rfl
    (by intro x; simp [ReadPlan.encodeWord_length])
    (fun n fixed x _ _ => NaturalAssignment.sequentialNumerator_le P slots
      (a :: tail) haNodup haFull vertices
      (AssignmentEnumeration.seedIndices vertices factors Δ) a n (x :: fixed)) hb regs

omit [Fintype V] [NeZero r] in
theorem program_run (a : Word r Q) (tail : List (Word r Q))
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
      ScoreBuilderRawRefinement.cost (Δ := Δ) a tail vertices factors rawPlans fixed n d ≤ B)
    (regs : Fin 16 → Bool) :
    ∃ e : SequentialProgram.Data,
      RunsIn program (sourceBudget (Δ := Δ) a tail vertices factors rawPlans B)
        ((AssignmentInitProgram.inputState
          (initialContext (Δ := Δ) a tail vertices factors rawPlans) regs).withPC
            (some program.entry)) (e.withPC none) ∧
      e.stacks 8 = ((NaturalAssignment.naturalValues P slots a tail vertices
        (AssignmentEnumeration.seedIndices vertices factors Δ)).reverse.map
          ReadPlan.encodeWord).flatten := by
  have hb := ScoreBuilderRawRefinement.refines_of_cost_bound P slots a tail vertices factors
    hv he rawPlans pairs hraw hpairs B hcost
  exact InitializedAssignmentProgram.run_of_refines ReadPlan.encodeWord a tail
    (NaturalAssignment.sequentialNumerator P slots (a :: tail) vertices
      (AssignmentEnumeration.seedIndices vertices factors Δ) a)
    (initialContext (Δ := Δ) a tail vertices factors rawPlans)
    (ScoreBuilderRawInput.environment Δ (a :: tail)
      (AssignmentEnumeration.seedIndices vertices factors Δ).length rawPlans)
    B (vertices.length ^ 2 * (blockSize r Q Δ) ^ 2)
    rfl rfl (by simp [initialContext]) rfl
    (by intro x; simp [ReadPlan.encodeWord_length])
    (fun n fixed x _ _ => NaturalAssignment.sequentialNumerator_le P slots
      (a :: tail) haNodup haFull vertices
      (AssignmentEnumeration.seedIndices vertices factors Δ) a n (x :: fixed)) hb regs

omit [Fintype V] [NeZero r] in
theorem primitive_run (a : Word r Q) (tail : List (Word r Q))
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
      ScoreBuilderRawRefinement.cost (Δ := Δ) a tail vertices factors rawPlans fixed n d ≤ B)
    (regs : Fin 16 → Bool) :
    ∃ e : SequentialProgram.Data,
      Computation.RunsIn (primitive program).step
        (primitiveOverhead program * sourceBudget (Δ := Δ) a tail vertices factors rawPlans B)
        (primitiveCfg program ((AssignmentInitProgram.inputState
          (initialContext (Δ := Δ) a tail vertices factors rawPlans) regs).withPC
            (some program.entry))) (primitiveCfg program (e.withPC none)) ∧
      e.stacks 8 = ((NaturalAssignment.naturalValues P slots a tail vertices
        (AssignmentEnumeration.seedIndices vertices factors Δ)).reverse.map
          ReadPlan.encodeWord).flatten := by
  obtain ⟨e, hr, hout⟩ := program_run P slots a tail haNodup haFull vertices factors hv he
    rawPlans pairs hraw hpairs B hcost regs
  exact ⟨e, primitive_execution program hr, hout⟩

end SubexponentialSAT.Subexp.InitializedRawAssignmentProgram

end OAI.Algorithms
