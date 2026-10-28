import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.ScoreBuilderRawInput
import OAI.Algorithms.SubexponentialSAT.Subexp.ScoreBuilderBounds
import OAI.Algorithms.SubexponentialSAT.Subexp.ScoreBuilderInputBounds

namespace OAI.Algorithms

/-! Concrete incidence collision scoring from raw two-word read plans.
The fixed legacy program constructs its selection tables and all four-word
completion tuples at runtime. No precomputed collision table is an input. -/

namespace SubexponentialSAT.SqrtLog.PackingIncidenceProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp

abbrev PlanPair := PairScoreProgram.PlanPair

/-- Each incidence reads an original-variable word and a factor word. -/
structure ValidRawPair (M : ℕ) (pair : PlanPair) : Prop where
  left_length : pair.1.length ≤ 2
  right_length : pair.2.length ≤ 2
  left_valid : ∀ i ∈ pair.1, i < M
  right_valid : ∀ i ∈ pair.2, i < M

theorem remaining_length_le (M processed : ℕ) (pair : PlanPair)
    (hp : ValidRawPair M pair) :
    (PairPreparationProgram.remaining M processed pair).length ≤ 4 := by
  have hn := ActivePlanProgram.active_nodup (List.range M)
    (pair.1.reverse ++ pair.2) (processed + 1) List.nodup_range
  change (PairPreparationProgram.remaining M processed pair).Nodup at hn
  have hs : PairPreparationProgram.remaining M processed pair ⊆ pair.1.reverse ++ pair.2 := by
    intro i hi
    exact ((ActivePlanProgram.mem_active _ _ _ _).mp hi).2.2
  have hsub : (PairPreparationProgram.remaining M processed pair).toFinset ⊆
      (pair.1.reverse ++ pair.2).toFinset := by
    intro i hi
    exact List.mem_toFinset.mpr (hs (List.mem_toFinset.mp hi))
  have hlen := (Finset.card_le_card hsub).trans (List.toFinset_card_le _)
  rw [List.toFinset_card_of_nodup hn] at hlen
  simp only [List.length_append, List.length_reverse] at hlen
  have hleft := hp.left_length
  have hright := hp.right_length
  exact hlen.trans (by omega)

theorem selected_valid (M processed : ℕ) (pair : PlanPair)
    (hp : ValidRawPair M pair) :
    (∀ i ∈ (PairPreparationProgram.selectedPair M processed pair).1, i < M + 4) ∧
    (∀ i ∈ (PairPreparationProgram.selectedPair M processed pair).2, i < M + 4) := by
  have hlen := remaining_length_le M processed pair hp
  exact ⟨ReadPlan.completionPlan_valid M 4 _ _ hlen hp.left_valid,
    ReadPlan.completionPlan_valid M 4 _ _ hlen hp.right_valid⟩

def context {r Q : ℕ} (alphabet : List (Word r Q)) (default : Word r Q)
    (fixed : List (Word r Q)) (n M : ℕ) (raw : List PlanPair)
    (d : ScoreBuilderProgram.Data) : CandidateScoreProgram.Context :=
  ScoreBuilderRawInput.context 1 alphabet default fixed n M raw d

theorem context_valid {r Q : ℕ} (alphabet : List (Word r Q)) (default : Word r Q)
    (fixed : List (Word r Q)) (n M : ℕ) (raw : List PlanPair)
    (d : ScoreBuilderProgram.Data)
    (hsize : n + 1 + fixed.length = M)
    (hw : (d.stacks 10).length = ReadPlan.wordWidth r Q)
    (hi : (d.stacks 19).length = fixed.length)
    (hp : ∀ pair ∈ raw, ValidRawPair M pair) :
    (context alphabet default fixed n M raw d).Valid := by
  constructor
  · simpa [context, ScoreBuilderRawInput.context, CandidateScoreRefinement.candidateContext] using hi
  · intro row hrow
    obtain ⟨word, _, rfl⟩ := List.mem_map.mp hrow
    simp [context, ScoreBuilderRawInput.context, CandidateScoreRefinement.candidateContext,
      ReadPlan.encodeWord_length, hw]
  · simp [context, ScoreBuilderRawInput.context, CandidateScoreRefinement.candidateContext,
      ReadPlan.encodeWord_length, hw]
  · intro row hrow
    obtain ⟨word, _, rfl⟩ := List.mem_map.mp hrow
    simp [context, ScoreBuilderRawInput.context, CandidateScoreRefinement.candidateContext,
      ReadPlan.encodeWord_length, hw]
  · intro row hrow
    obtain ⟨word, _, rfl⟩ := List.mem_map.mp hrow
    simp [context, ScoreBuilderRawInput.context, CandidateScoreRefinement.candidateContext,
      ReadPlan.encodeWord_length, hw]
  · intro row hrow
    obtain ⟨word, _, rfl⟩ := List.mem_map.mp hrow
    simp [context, ScoreBuilderRawInput.context, CandidateScoreRefinement.candidateContext,
      ReadPlan.encodeWord_length, hw]
  · intro pair hpair
    obtain ⟨original, horiginal, rfl⟩ := List.mem_map.mp hpair
    have hv := selected_valid M (d.stacks 19).length original (hp original horiginal)
    simpa [context, ScoreBuilderRawInput.context, CandidateScoreRefinement.candidateContext,
      CandidateScoreProgram.pairContext, PairScoreProgram.ValidPair, ← hsize,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hv

theorem pairBytes_length_le (M : ℕ) (pair : PlanPair) (hp : ValidRawPair M pair) :
    (PairScoreProgram.pairBytes pair).length ≤ 16 * (M + 1) + 6 := by
  have hl := PairPreparationBounds.planBytes_le pair.1 M
    (fun i hi => (hp.left_valid i hi).le)
  have hr := PairPreparationBounds.planBytes_le pair.2 M
    (fun i hi => (hp.right_valid i hi).le)
  have hleft := hp.left_length
  have hright := hp.right_length
  simp only [PairScoreProgram.pairBytes, List.length_append, Encoding.length_frame]
  nlinarith

/-- Fixed polynomial in the original input sizes, before preparing any table. -/
def inputBound (M pairs q width : ℕ) : ℕ := 32 * (M + pairs + q + width + 1)^2

def runtimeBound (M pairs q width : ℕ) : ℕ :=
  ScoreBuilderBounds.runtimeBound (inputBound M pairs q width) q 4

theorem boundedInputs {r Q : ℕ} (a : Word r Q) (tail fixed : List (Word r Q))
    (n M : ℕ) (raw : List PlanPair) (d : ScoreBuilderProgram.Data)
    (hm : SequentialProgram.Memory ReadPlan.encodeWord a tail (n + 1) fixed d.stacks)
    (hsize : n + 1 + fixed.length = M)
    (hp : ∀ pair ∈ raw, ValidRawPair M pair) :
    ScoreBuilderBounds.BoundedInputs
      (ScoreBuilderRawInput.preparationContext M raw d)
      (context (a :: tail) a fixed n M raw d)
      (inputBound M raw.length (a :: tail).length (ReadPlan.wordWidth r Q)) := by
  let s := M + raw.length + (a :: tail).length + ReadPlan.wordWidth r Q + 1
  have hs : 1 ≤ s := by dsimp [s]; omega
  have hM : M + 1 ≤ s := by dsimp [s]; omega
  have hpairs : raw.length ≤ s := by dsimp [s]; omega
  have hq : (a :: tail).length ≤ s := by dsimp [s]; omega
  have hw : ReadPlan.wordWidth r Q ≤ s := by dsimp [s]; omega
  have hs2 : s ≤ s^2 := le_self_pow₀ hs (by omega)
  have hfixed : fixed.length ≤ M := by omega
  have hwidth : (d.stacks 10).length = ReadPlan.wordWidth r Q := by
    simpa only [ReadPlan.encodeWord_length] using hm.width
  have hmw : M * ReadPlan.wordWidth r Q ≤ s^2 := by
    simpa only [pow_two] using Nat.mul_le_mul (show M ≤ s by omega) hw
  change ScoreBuilderBounds.BoundedInputs _ _ (32*s^2)
  constructor
  · change M ≤ _
    nlinarith only [hM, hs2]
  · change (d.stacks 19).length ≤ _
    rw [hm.processed]
    nlinarith only [hfixed, hM, hs2]
  · change raw.length ≤ _
    nlinarith only [hpairs, hs2]
  · intro pair hpair
    have hb := pairBytes_length_le M pair (hp pair hpair)
    nlinarith only [hb, hM, hs2, hs]
  · change ((fixed.reverse.map ReadPlan.encodeWord).flatten ++
      (ReadPlan.encodeWord a ++ ((List.replicate n a).map ReadPlan.encodeWord).flatten)).length ≤ _
    rw [List.length_append, List.length_append, ScoreBuilderInputBounds.encodedWords_length,
      ScoreBuilderInputBounds.encodedWords_length, List.length_reverse, List.length_replicate,
      ReadPlan.encodeWord_length]
    have heq : fixed.length * ReadPlan.wordWidth r Q +
        (ReadPlan.wordWidth r Q + n * ReadPlan.wordWidth r Q) =
        M * ReadPlan.wordWidth r Q := by rw [← hsize]; ring
    rw [heq]
    nlinarith only [hmw]
  · change (fixed.reverse.map ReadPlan.encodeWord).length ≤ _
    simp only [List.length_map, List.length_reverse]
    nlinarith only [hfixed, hM, hs2]
  · change (d.stacks 10).length ≤ _
    rw [hwidth]
    nlinarith only [hw, hs2]
  · change (List.replicate (2 * (1 + 1)) true).length ≤ _
    rw [List.length_replicate]
    nlinarith only [hs, hs2]
  · change ((a :: tail).map ReadPlan.encodeWord).length ≤ _
    rw [List.length_map]
    nlinarith only [hq, hs2]

abbrev command := ScoreBuilderProgram.command
abbrev program := ScoreBuilderProgram.program

/-- The raw-plan builder executes its real selection and tuple loops. The
output is a framed unary count for each candidate, in candidate order. -/
theorem command_eval {r Q : ℕ} (a : Word r Q) (tail fixed : List (Word r Q))
    (n M : ℕ) (raw : List PlanPair) (d : ScoreBuilderProgram.Data)
    (hm : SequentialProgram.Memory ReadPlan.encodeWord a tail (n + 1) fixed d.stacks)
    (hh : SequentialProgram.HighState (ScoreBuilderRawInput.environment 1 (a::tail) M raw)
      d.stacks)
    (hsize : n + 1 + fixed.length = M)
    (hp : ∀ pair ∈ raw, ValidRawPair M pair) :
    ∃ t ≤ runtimeBound M raw.length (a::tail).length (ReadPlan.wordWidth r Q),
      ∃ regs, SubexponentialSAT.StructuredCalls.Eval command t d
        (ScoreBuilderProgram.resultState d regs
          (ScoreBuilderProgram.scoreBytes (context (a::tail) a fixed n M raw d))) := by
  have hw : (d.stacks 10).length = ReadPlan.wordWidth r Q := by
    simpa only [ReadPlan.encodeWord_length] using hm.width
  have hc := context_valid (a::tail) a fixed n M raw d hsize hw hm.processed hp
  have hi := ScoreBuilderRawInput.inputFor_of_memory 1 a tail fixed n M raw d hm hh
  obtain ⟨t, ht, regs, he⟩ := ScoreBuilderProgram.command_eval
    (ScoreBuilderRawInput.preparationContext M raw d)
    (context (a::tail) a fixed n M raw d) hc d hi
  have hb := ScoreBuilderBounds.sourceBudget_le _ _ hc _
    (boundedInputs a tail fixed n M raw d hm hsize hp)
    (by simp [context, ScoreBuilderRawInput.context, CandidateScoreRefinement.candidateContext]) rfl
  refine ⟨t, ?_, regs, he⟩
  have ht' := ht.trans (Nat.sub_le _ _)
  exact ht'.trans (by simpa [runtimeBound, context, ScoreBuilderRawInput.context,
    CandidateScoreRefinement.candidateContext] using hb)

/-- A single finite BitProgram, independent of the incidence instance. -/
theorem program_runsIn {r Q : ℕ} (a : Word r Q) (tail fixed : List (Word r Q))
    (n M : ℕ) (raw : List PlanPair) (d : ScoreBuilderProgram.Data)
    (hm : SequentialProgram.Memory ReadPlan.encodeWord a tail (n + 1) fixed d.stacks)
    (hh : SequentialProgram.HighState (ScoreBuilderRawInput.environment 1 (a::tail) M raw)
      d.stacks)
    (hsize : n + 1 + fixed.length = M)
    (hp : ∀ pair ∈ raw, ValidRawPair M pair) :
    ∃ regs, RunsIn program
      (runtimeBound M raw.length (a::tail).length (ReadPlan.wordWidth r Q) + 1)
      (d.withPC (some program.entry))
      ((ScoreBuilderProgram.resultState d regs
        (ScoreBuilderProgram.scoreBytes (context (a::tail) a fixed n M raw d))).withPC none) := by
  obtain ⟨t, ht, regs, he⟩ := command_eval a tail fixed n M raw d hm hh hsize hp
  exact ⟨regs, t+1, by omega, SubexponentialSAT.StructuredCalls.compiled_halt_trace he 8 0⟩

theorem primitive_runsIn {r Q : ℕ} (a : Word r Q) (tail fixed : List (Word r Q))
    (n M : ℕ) (raw : List PlanPair) (d : ScoreBuilderProgram.Data)
    (hm : SequentialProgram.Memory ReadPlan.encodeWord a tail (n + 1) fixed d.stacks)
    (hh : SequentialProgram.HighState (ScoreBuilderRawInput.environment 1 (a::tail) M raw)
      d.stacks)
    (hsize : n + 1 + fixed.length = M)
    (hp : ∀ pair ∈ raw, ValidRawPair M pair) :
    ∃ regs, SubexponentialSAT.Computation.RunsIn (primitive program).step
      (primitiveOverhead program *
        (runtimeBound M raw.length (a::tail).length (ReadPlan.wordWidth r Q) + 1))
      (primitiveCfg program (d.withPC (some program.entry)))
      (primitiveCfg program ((ScoreBuilderProgram.resultState d regs
        (ScoreBuilderProgram.scoreBytes (context (a::tail) a fixed n M raw d))).withPC none)) := by
  obtain ⟨regs, he⟩ := program_runsIn a tail fixed n M raw d hm hh hsize hp
  exact ⟨regs, primitive_execution program he⟩

theorem output_frame (d : ScoreBuilderProgram.Data) (regs : Fin 16 → Bool)
    (scores : List Bool) (j : Fin 48) (hj : j ≠ 0) :
    (ScoreBuilderProgram.resultState d regs scores).stacks j = d.stacks j := by
  simp [ScoreBuilderProgram.resultState, hj]

end SubexponentialSAT.SqrtLog.PackingIncidenceProgram

end OAI.Algorithms
