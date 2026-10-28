import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceProgramPairs
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceProgramRefinement

namespace OAI.Algorithms

/-! The actual generated incidence-pair order is accepted by the fixed scorer. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp

section Plans
variable {I V E : Type*} [DecidableEq V] [DecidableEq E]
  (ivar : I → V) (factor : I → E)

def incidencePlans (indices : List (V ⊕ E)) (incidences : List I) : List (List ℕ) :=
  incidences.map (incidencePlan ivar factor indices)

theorem generatedIncidencePairs_perm (indices : List (V ⊕ E)) (incidences : List I) :
    (generatedRawPairs (incidencePlans ivar factor indices incidences)).Perm
      (rawPairs ivar factor indices incidences) := by
  simpa [incidencePlans, rawPairs, incidencePair, List.product, List.flatMap_map,
    List.map_flatMap, List.map_map, Function.comp_def] using
    generatedRawPairs_perm (incidencePlans ivar factor indices incidences)

theorem incidencePlans_valid (indices : List (V ⊕ E)) (hi : ∀ x, x ∈ indices)
    (incidences : List I) :
    (∀ p ∈ incidencePlans ivar factor indices incidences, p.length ≤ 2) ∧
    (∀ p ∈ incidencePlans ivar factor indices incidences, ∀ i ∈ p, i < indices.length) := by
  constructor
  · intro p hp
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hp
    simp [incidencePlan]
  · intro p hp j hj
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hp
    exact (incidencePair_valid ivar factor indices hi (i,i)).left_valid j hj

theorem generatedIncidencePairs_cost (indices : List (V ⊕ E)) (hi : ∀ x, x ∈ indices)
    (incidences : List I) (hne : incidences ≠ []) :
    TupleProgram.powerCost (planAlphabet (incidencePlans ivar factor indices incidences))
      2 [[]] + 9 ≤ 2400 * incidences.length^2 * (24*indices.length+34) + 9 := by
  have hv := incidencePlans_valid ivar factor indices hi incidences
  have hn : incidencePlans ivar factor indices incidences ≠ [] := by
    simpa [incidencePlans] using hne
  simpa only [incidencePlans, List.length_map] using
    rawPairProgram_cost indices.length (incidencePlans ivar factor indices incidences) hn hv.1 hv.2
end Plans

section Semantics
variable {I V E : Type*} [Fintype I] [Fintype V] [Fintype E]
  [DecidableEq I] [DecidableEq V] [DecidableEq E]
  (ivar : I → V) (factor : I → E) {r Q : ℕ}

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] in
theorem generated_refines (a : Word r Q) (tail : List (Word r Q))
    (indices : List (V ⊕ E)) (hi : ∀ x, x ∈ indices) (incidences : List I) :
    SequentialProgram.ScoreBuilderRefines ReadPlan.encodeWord a tail
      (incidenceNumerator ivar factor (a::tail) (incidences.product incidences) indices a)
      command (runtimeBound indices.length (incidences.length^2) (a::tail).length
        (ReadPlan.wordWidth r Q)) indices.length
      (ScoreBuilderRawInput.environment 1 (a::tail) indices.length
        (generatedRawPairs (incidencePlans ivar factor indices incidences))) := by
  have h := refines ivar factor a tail (incidences.product incidences) indices hi
    (generatedRawPairs (incidencePlans ivar factor indices incidences))
    (generatedIncidencePairs_perm ivar factor indices incidences)
  simpa only [generatedRawPairs_length, incidencePlans, List.length_map] using h

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] in
/-- An actual finite instruction trace produces the mathematical count records. -/
theorem program_produces (a : Word r Q) (tail fixed : List (Word r Q))
    (pairs : List (I × I)) (indices : List (V ⊕ E)) (hi : ∀ x, x ∈ indices)
    (n : ℕ) (raw : List PlanPair) (d : ScoreBuilderProgram.Data)
    (hraw : raw.Perm (pairs.map (incidencePair ivar factor indices)))
    (hm : SequentialProgram.Memory ReadPlan.encodeWord a tail (n+1) fixed d.stacks)
    (hh : SequentialProgram.HighState
      (ScoreBuilderRawInput.environment 1 (a::tail) indices.length raw) d.stacks)
    (hsize : n+1+fixed.length = indices.length) :
    ∃ e : ScoreBuilderProgram.Data,
      RunsIn program
        (runtimeBound indices.length raw.length (a::tail).length (ReadPlan.wordWidth r Q)+1)
        (d.withPC (some program.entry)) (e.withPC none) ∧
      e.stacks 0 = ProgramEncoding.encodeRecords ((a::tail).map (fun candidate =>
        UnaryCompare.encode (incidenceNumerator ivar factor (a::tail) pairs indices a
          n (candidate::fixed)))) ∧
      (∀ j, j ≠ 0 → e.stacks j = d.stacks j) := by
  obtain ⟨t, ht, e, he, hout, hframe⟩ :=
    run_from_memory ivar factor a tail fixed pairs indices hi n raw d hraw hm hh hsize
  exact ⟨e, ⟨t+1, by omega, SubexponentialSAT.StructuredCalls.compiled_halt_trace he 8 0⟩, hout, hframe⟩

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] in
/-- The same exact counts are produced in the primitive bit machine. -/
theorem primitive_produces (a : Word r Q) (tail fixed : List (Word r Q))
    (pairs : List (I × I)) (indices : List (V ⊕ E)) (hi : ∀ x, x ∈ indices)
    (n : ℕ) (raw : List PlanPair) (d : ScoreBuilderProgram.Data)
    (hraw : raw.Perm (pairs.map (incidencePair ivar factor indices)))
    (hm : SequentialProgram.Memory ReadPlan.encodeWord a tail (n+1) fixed d.stacks)
    (hh : SequentialProgram.HighState
      (ScoreBuilderRawInput.environment 1 (a::tail) indices.length raw) d.stacks)
    (hsize : n+1+fixed.length = indices.length) :
    ∃ e : ScoreBuilderProgram.Data,
      SubexponentialSAT.Computation.RunsIn (primitive program).step
        (primitiveOverhead program *
          (runtimeBound indices.length raw.length (a::tail).length (ReadPlan.wordWidth r Q)+1))
        (primitiveCfg program (d.withPC (some program.entry)))
        (primitiveCfg program (e.withPC none)) ∧
      e.stacks 0 = ProgramEncoding.encodeRecords ((a::tail).map (fun candidate =>
        UnaryCompare.encode (incidenceNumerator ivar factor (a::tail) pairs indices a
          n (candidate::fixed)))) ∧
      (∀ j, j ≠ 0 → e.stacks j = d.stacks j) := by
  obtain ⟨e, hr, hout, hframe⟩ :=
    program_produces ivar factor a tail fixed pairs indices hi n raw d hraw hm hh hsize
  exact ⟨e, primitive_execution program hr, hout, hframe⟩
end Semantics
end SubexponentialSAT.SqrtLog.PackingIncidenceProgram

end OAI.Algorithms
