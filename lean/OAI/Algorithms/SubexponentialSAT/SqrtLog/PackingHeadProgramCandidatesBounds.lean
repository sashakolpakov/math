import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingHeadProgramCandidatesRun

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingHeadProgramCandidates
open SubexponentialSAT BitProgram StructuredCalls StackRoutines SubexpScanPrimitives Subexp
open scoped BigOperators

theorem jointTrue_le (xs ys : List Bool) : PackingHeadProgramAnd.jointTrue xs ys ≤ xs.length := by
  have h := @List.count_le_length Bool _ true (List.zipWith (· && ·) xs ys)
  exact h.trans (by simp)

theorem score_le (candidate : List Bool) (rows : List (List Bool)) :
    PackingHeadProgramPrefix.score candidate rows ≤ rows.length*candidate.length := by
  induction rows with
  | nil => simp [PackingHeadProgramPrefix.score]
  | cons word rows ih =>
    have h := jointTrue_le candidate word
    simp only [PackingHeadProgramPrefix.score,List.map_cons,List.sum_cons,List.length_cons] at *
    nlinarith

theorem recordBudget_le (rows candidates : List (List Bool)) (W : ℕ)
    (hlen : ∀ candidate ∈ candidates,candidate.length=W) :
    RecordPrograms.budget (callbackCost rows) candidates ≤
      candidates.length*(rows.length*(25*W+20)+17*W+48) := by
  induction candidates with
  | nil => simp [RecordPrograms.budget]
  | cons candidate candidates ih =>
    have hc := score_le candidate rows
    have hl := hlen candidate (by simp)
    have hi := ih (by intro x hx; exact hlen x (by simp [hx]))
    simp only [RecordPrograms.budget,callbackCost,List.length_cons]
    rw [hl] at hc ⊢
    nlinarith

theorem output_length_le (rows candidates : List (List Bool)) (W : ℕ)
    (hlen : ∀ candidate ∈ candidates,candidate.length=W) :
    (ProgramEncoding.encodeRecords (scoreRecords rows candidates)).length ≤
      1+(2*(rows.length*W)+2)*candidates.length := by
  have h := ProgramEncoding.encodeRecords_length_le (scoreRecords rows candidates) (rows.length*W) ?_
  · simpa [scoreRecords] using h
  · intro payload hp
    obtain ⟨candidate,hc,rfl⟩ := List.mem_map.mp hp
    simp only [scoreBits,List.length_replicate]
    simpa [hlen candidate hc] using score_le candidate rows

theorem budget_le (rows candidates : List (List Bool)) (W : ℕ)
    (hlen : ∀ candidate ∈ candidates,candidate.length=W) :
    budget rows candidates ≤
      candidates.length*(43*rows.length*W+20*rows.length+17*W+66)+22 := by
  have hr := recordBudget_le rows candidates W hlen
  have ho := output_length_le rows candidates W hlen
  have he : (TupleProgram.appendEncoded (scoreRecords rows candidates) []).length+1 =
      (ProgramEncoding.encodeRecords (scoreRecords rows candidates)).length := by
    have h := congrArg List.length (CandidateScoreProgram.reverseRecord_finish (scoreRecords rows candidates))
    simpa using h
  unfold budget
  rw [he]
  nlinarith

def coordinateOverlap {r Q : ℕ} (candidate : MulticolorTypes.Word r Q)
    (prior : List (MulticolorTypes.Word r Q)) : ℕ :=
  (prior.map (fun word => ∑ t : Fin Q, if candidate t=word t then 1 else 0)).sum

theorem scoreRecords_words {r Q : ℕ} (prior candidates : List (MulticolorTypes.Word r Q)) :
    scoreRecords (prior.map ReadPlan.encodeWord) (candidates.map ReadPlan.encodeWord) =
      candidates.map (fun candidate => List.replicate (coordinateOverlap candidate prior) false) := by
  simp only [scoreRecords,List.map_map]
  apply List.map_congr_left
  intro candidate _
  simp only [Function.comp_apply,scoreBits,PackingHeadProgramPreserve.score_words,coordinateOverlap]

theorem program_run_words {r Q : ℕ} (prior candidates : List (MulticolorTypes.Word r Q)) :
    RunsIn program (candidates.length*(43*prior.length*(Q*r)+20*prior.length+17*(Q*r)+66)+22)
      ((inputState (prior.map ReadPlan.encodeWord) (candidates.map ReadPlan.encodeWord)).withPC
        (some program.entry))
      ((baseState (prior.map ReadPlan.encodeWord) (ProgramEncoding.encodeRecords
        (candidates.map (fun candidate => List.replicate (coordinateOverlap candidate prior) false)))).withPC none) := by
  have hv : ∀ candidate ∈ candidates.map ReadPlan.encodeWord,
      validPayload (prior.map ReadPlan.encodeWord) candidate := by
    intro candidate hc row hr
    obtain ⟨c,_,rfl⟩ := List.mem_map.mp hc
    obtain ⟨w,_,rfl⟩ := List.mem_map.mp hr
    simp
  obtain ⟨n,hn,ht⟩ := program_run (prior.map ReadPlan.encodeWord) (candidates.map ReadPlan.encodeWord) hv
  have hb := budget_le (prior.map ReadPlan.encodeWord) (candidates.map ReadPlan.encodeWord) (Q*r) (by
    intro candidate hc
    obtain ⟨c,_,rfl⟩ := List.mem_map.mp hc
    simp [ReadPlan.wordWidth])
  rw [scoreRecords_words] at ht
  exact ⟨n,hn.trans (by simpa using hb),ht⟩


theorem source_frame (rows candidates : List (List Bool)) (j : Fin 12)
    (hs : j ≠ 8) (ho : j ≠ 9) :
    (baseState rows (ProgramEncoding.encodeRecords (scoreRecords rows candidates))).stacks j =
      (inputState rows candidates).stacks j := by
  fin_cases j <;> simp_all [baseState,inputState,RecordPrograms.state,ports]

theorem primitive_run_words {r Q : ℕ} (prior candidates : List (MulticolorTypes.Word r Q)) :
    Computation.RunsIn (primitive program).step
      (primitiveOverhead program *
        (candidates.length*(43*prior.length*(Q*r)+20*prior.length+17*(Q*r)+66)+22))
      (primitiveCfg program
        ((inputState (prior.map ReadPlan.encodeWord) (candidates.map ReadPlan.encodeWord)).withPC
          (some program.entry)))
      (primitiveCfg program
        ((baseState (prior.map ReadPlan.encodeWord) (ProgramEncoding.encodeRecords
          (candidates.map (fun candidate => List.replicate (coordinateOverlap candidate prior) false)))).withPC none)) :=
  BitProgram.primitive_execution program (program_run_words prior candidates)

end SubexponentialSAT.SqrtLog.PackingHeadProgramCandidates

end OAI.Algorithms
