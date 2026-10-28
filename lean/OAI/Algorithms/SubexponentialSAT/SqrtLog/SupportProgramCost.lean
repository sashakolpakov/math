import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SupportProgramSteps
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SupportProgramAppend
import OAI.Algorithms.SubexponentialSAT.SubexpNodeCost

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.SupportProgram.Steps

open SubexponentialSAT.Subexp.TupleProgram

theorem output_eq_appendGrow (budget : List Bool) (rows : Records) :
    output budget rows = appendGrow budget.length rows := by
  simp [output, filtered, cartesianOutput, alphabet, appendGrow,
    List.filter_reverse]
  rfl

theorem output_correct (n : ℕ) (budget : List Bool) (rows : Records)
    (h : Correct n budget.length rows) : Correct (n + 1) budget.length (output budget rows) := by
  rw [output_eq_appendGrow]
  exact appendGrow_correct n budget.length rows h

theorem candidate_width (n : ℕ) (rows : Records)
    (h : ∀ w ∈ rows, w.length ≤ n) :
    ∀ w ∈ cartesianOutput rows alphabet, w.length ≤ n + 1 := by
  intro w hw
  simp only [cartesianOutput, List.mem_reverse, List.mem_flatMap] at hw
  obtain ⟨v,hv,hw⟩ := hw
  simp [alphabet] at hw
  rcases hw with rfl | rfl <;> simpa using Nat.add_le_add_right (h v hv) 1

theorem encoded_length_le (rows : Records) (n : ℕ) (h : ∀ w ∈ rows, w.length ≤ n) :
    (SubexponentialSAT.ProgramEncoding.encodeRecords rows).length ≤ (2*n+2)*rows.length+1 := by
  rw [SubexponentialSAT.ProgramEncoding.encodeRecords_length]
  have hp := SubexponentialSAT.SubexpNodeCost.payloadSize_le rows n h
  unfold SubexponentialSAT.SubexpNodeCost.payloadSize at hp
  nlinarith

theorem stepCost_le (n : ℕ) (budget : List Bool) (rows : Records)
    (h : ∀ w ∈ rows, w.length ≤ n) :
    stepCost budget rows ≤ 1000 * (n + budget.length + 1) * (rows.length + 1) := by
  have hc := candidate_width n rows h
  have hf := Filter.cost_bound budget (cartesianOutput rows alphabet) (n+1) hc
  have hp := SubexponentialSAT.SubexpNodeCost.payloadSize_le rows n h
  have ho : ∀ w ∈ output budget rows, w.length ≤ n+1 := by
    intro w hw
    exact hc w ((List.mem_filter.mp (List.mem_reverse.mp hw)).1)
  have he := encoded_length_le (output budget rows) (n+1) ho
  have hol : (output budget rows).length ≤ (cartesianOutput rows alphabet).length := by
    simp only [output, filtered, List.length_reverse]
    exact List.length_filter_le _ _
  have hcl : (cartesianOutput rows alphabet).length = 2 * rows.length := by
    simp [cartesianOutput_length, alphabet, Nat.mul_comm]
  rw [hcl] at hf hol
  have heu : (SubexponentialSAT.ProgramEncoding.encodeRecords (output budget rows)).length ≤
      (2*(n+1)+2)*(2*rows.length)+1 := by
    exact he.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ hol) 1)
  rw [stepCost, SubexponentialSAT.SubexpNodeCost.stepCost_eq]
  simp only [alphabet, List.length_cons, List.length_nil, SubexponentialSAT.SubexpNodeCost.payloadSize_cons,
    SubexponentialSAT.SubexpNodeCost.payloadSize_nil]
  dsimp only [alphabet] at hf
  nlinarith

end SubexponentialSAT.SqrtLog.SupportProgram.Steps

end OAI.Algorithms
