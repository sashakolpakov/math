import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceProgramGenerated

namespace OAI.Algorithms

/-! The incidence scorer does not touch controller storage on ports 12--18. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput
open SubexponentialSAT.BitProgram SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp
open SubexponentialSAT.SqrtLog.PackingIncidenceProgram

structure LooseMemory {r Q : ℕ} (a : Word r Q) (fixed : List (Word r Q))
    (n : ℕ) (d : ScoreBuilderProgram.Data) : Prop where
  assignment : d.stacks 8 =
    (fixed.reverse.map ReadPlan.encodeWord ++ List.replicate (n+1) (ReadPlan.encodeWord a)).flatten
  width : (d.stacks 10).length = ReadPlan.wordWidth r Q
  processed : (d.stacks 19).length = fixed.length
  scratch : ∀ j : Fin 48, j.val < 8 → d.stacks j = []

private def cleaned {r Q : ℕ} (a : Word r Q) (tail : List (Word r Q))
    (d : ScoreBuilderProgram.Data) : ScoreBuilderProgram.Data :=
  ⟨d.regs, fun j => if j ∈ SequentialProgram.scratchPorts then []
    else if j = 9 then ((a::tail).map ReadPlan.encodeWord).flatten else d.stacks j⟩

private theorem cleaned_memory {r Q : ℕ} (a : Word r Q) (tail fixed : List (Word r Q))
    (n : ℕ) (d : ScoreBuilderProgram.Data) (hm : LooseMemory a fixed n d) :
    SequentialProgram.Memory ReadPlan.encodeWord a tail (n+1) fixed (cleaned a tail d).stacks := by
  constructor
  · simpa [cleaned, SequentialProgram.scratchPorts] using hm.assignment
  · simp [cleaned, SequentialProgram.scratchPorts]
  · simpa [cleaned, SequentialProgram.scratchPorts, ReadPlan.encodeWord_length] using hm.width
  · simpa [cleaned, SequentialProgram.scratchPorts] using hm.processed
  · intro j hj; simp [cleaned, hj]

private theorem cleaned_high {r Q : ℕ} (a : Word r Q) (tail : List (Word r Q))
    (d : ScoreBuilderProgram.Data) (env : Fin 48 → List Bool)
    (hh : SequentialProgram.HighState env d.stacks) :
    SequentialProgram.HighState env (cleaned a tail d).stacks := by
  intro j hj
  have hnot : j ∉ SequentialProgram.scratchPorts := by
    have hs : ∀ k ∈ SequentialProgram.scratchPorts, k.val < 20 := by decide
    exact fun h => (Nat.not_le_of_lt (hs j h)) hj
  have h9 : j ≠ 9 := by intro h; subst j; omega
  simpa [cleaned, hnot, h9] using hh j hj

private theorem cleaned_context {r Q : ℕ} (a : Word r Q) (tail fixed : List (Word r Q))
    (n M : ℕ) (raw : List PlanPair) (d : ScoreBuilderProgram.Data) :
    context (a::tail) a fixed n M raw (cleaned a tail d) =
      context (a::tail) a fixed n M raw d := by
  simp [context, ScoreBuilderRawInput.context, cleaned, SequentialProgram.scratchPorts]

private theorem cleaned_preparation {r Q : ℕ} (a : Word r Q) (tail : List (Word r Q))
    (M : ℕ) (raw : List PlanPair) (d : ScoreBuilderProgram.Data) :
    ScoreBuilderRawInput.preparationContext M raw (cleaned a tail d) =
      ScoreBuilderRawInput.preparationContext M raw d := by
  simp [ScoreBuilderRawInput.preparationContext, cleaned, SequentialProgram.scratchPorts]

theorem inputFor_of_loose {r Q : ℕ} (a : Word r Q) (tail fixed : List (Word r Q))
    (n M : ℕ) (raw : List PlanPair) (d : ScoreBuilderProgram.Data)
    (hm : LooseMemory a fixed n d)
    (hh : SequentialProgram.HighState (ScoreBuilderRawInput.environment 1 (a::tail) M raw)
      d.stacks) :
    ScoreBuilderProgram.InputFor (ScoreBuilderRawInput.preparationContext M raw d)
      (context (a::tail) a fixed n M raw d) d := by
  have hi := ScoreBuilderRawInput.inputFor_of_memory 1 a tail fixed n M raw
    (cleaned a tail d) (cleaned_memory a tail fixed n d hm) (cleaned_high a tail d _ hh)
  change ScoreBuilderProgram.InputFor _ (context (a::tail) a fixed n M raw (cleaned a tail d)) _ at hi
  rw [cleaned_context, cleaned_preparation] at hi
  have h0 := hm.scratch 0 (by decide)
  have h1 := hm.scratch 1 (by decide)
  have h2 := hm.scratch 2 (by decide)
  have h3 := hm.scratch 3 (by decide)
  have h4 := hm.scratch 4 (by decide)
  have h5 := hm.scratch 5 (by decide)
  have h6 := hm.scratch 6 (by decide)
  have h7 := hm.scratch 7 (by decide)
  constructor
  · intro i
    have h := hi.preparation i
    fin_cases i <;>
      simpa [cleaned, SequentialProgram.scratchPorts, ScoreBuilderProgram.preparationPorts,
        h0,h1,h2,h3,h4,h5,h6,h7] using h
  · intro i
    have h := hi.candidates i
    fin_cases i <;>
      simpa [ScoreBuilderProgram.prepared, cleaned, SequentialProgram.scratchPorts,
        ScoreBuilderProgram.candidatePorts,h0,h1,h2,h3,h4,h5,h6,h7] using h

theorem command_eval_loose {r Q : ℕ} (a : Word r Q) (tail fixed : List (Word r Q))
    (n M : ℕ) (raw : List PlanPair) (d : ScoreBuilderProgram.Data)
    (hm : LooseMemory a fixed n d)
    (hh : SequentialProgram.HighState (ScoreBuilderRawInput.environment 1 (a::tail) M raw)
      d.stacks) (hsize : n+1+fixed.length = M)
    (hp : ∀ pair ∈ raw, ValidRawPair M pair) :
    ∃ t ≤ runtimeBound M raw.length (a::tail).length (ReadPlan.wordWidth r Q),
      ∃ regs, SubexponentialSAT.StructuredCalls.Eval command t d
        (ScoreBuilderProgram.resultState d regs
          (ScoreBuilderProgram.scoreBytes (context (a::tail) a fixed n M raw d))) := by
  have hc := context_valid (a::tail) a fixed n M raw d hsize hm.width hm.processed hp
  obtain ⟨t, ht, regs, he⟩ := ScoreBuilderProgram.command_eval _ _ hc d
    (inputFor_of_loose a tail fixed n M raw d hm hh)
  have hb := boundedInputs a tail fixed n M raw (cleaned a tail d)
    (cleaned_memory a tail fixed n d hm) hsize hp
  rw [cleaned_context, cleaned_preparation] at hb
  have hb' := ScoreBuilderBounds.sourceBudget_le _ _ hc _ hb
    (by simp [context, ScoreBuilderRawInput.context, CandidateScoreRefinement.candidateContext]) rfl
  refine ⟨t, ?_, regs, he⟩
  exact (ht.trans (Nat.sub_le _ _)).trans (by
    simpa [runtimeBound, context, ScoreBuilderRawInput.context,
      CandidateScoreRefinement.candidateContext] using hb')

section Semantics
variable {I V E : Type*} [Fintype I] [Fintype V] [Fintype E]
  [DecidableEq I] [DecidableEq V] [DecidableEq E]
  (ivar : I → V) (factor : I → E) {r Q : ℕ}

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] in
theorem run_from_memory_loose (a : Word r Q) (tail fixed : List (Word r Q))
    (pairs : List (I × I)) (indices : List (V ⊕ E)) (hi : ∀ x, x ∈ indices)
    (n : ℕ) (raw : List PlanPair) (d : ScoreBuilderProgram.Data)
    (hraw : raw.Perm (pairs.map (incidencePair ivar factor indices)))
    (hm : LooseMemory a fixed n d)
    (hh : SequentialProgram.HighState
      (ScoreBuilderRawInput.environment 1 (a::tail) indices.length raw) d.stacks)
    (hsize : n+1+fixed.length = indices.length) :
    ∃ t ≤ runtimeBound indices.length raw.length (a::tail).length (ReadPlan.wordWidth r Q),
      ∃ e : ScoreBuilderProgram.Data,
      SubexponentialSAT.StructuredCalls.Eval command t d e ∧
      e.stacks 0 = ProgramEncoding.encodeRecords ((a::tail).map (fun candidate =>
        UnaryCompare.encode (incidenceNumerator ivar factor (a::tail) pairs indices a
          n (candidate::fixed)))) ∧
      (∀ j, j ≠ 0 → e.stacks j = d.stacks j) := by
  have hp : ∀ pair ∈ raw, ValidRawPair indices.length pair := by
    intro pair hpair
    obtain ⟨p, _, rfl⟩ := List.mem_map.mp (hraw.mem_iff.mp hpair)
    exact incidencePair_valid ivar factor indices hi p
  obtain ⟨t, ht, regs, he⟩ := command_eval_loose a tail fixed n indices.length raw d hm hh hsize hp
  refine ⟨t, ht, _, he, ?_, output_frame d regs _⟩
  have hout := scoreBytes_eq ivar factor a tail fixed pairs indices hi n raw
    (cleaned a tail d) hraw (cleaned_memory a tail fixed n d hm) hsize
  rw [cleaned_context] at hout
  simpa [ScoreBuilderProgram.resultState] using hout
end Semantics
end SubexponentialSAT.SqrtLog.PackingIncidenceInput

end OAI.Algorithms
