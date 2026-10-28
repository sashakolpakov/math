import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketTupleProgramExpand

namespace OAI.Algorithms

/-! The paid Cartesian step is linear in the number of emitted bucket tuples,
up to a polynomial factor in the maximum record widths. -/
namespace SubexponentialSAT.SqrtLog.BucketTupleProgram.ProductBounds

open SubexponentialSAT.Subexp.TupleProgram

theorem budget_le (xs : Records) (cost : List Bool → ℕ) (L C : ℕ)
    (hlen : ∀ x∈xs,x.length ≤ L) (hc : ∀ x∈xs,cost x ≤ C) :
    SubexponentialSAT.RecordPrograms.budget cost xs ≤ xs.length*(6*L+C+7) := by
  induction xs with
  | nil => simp [SubexponentialSAT.RecordPrograms.budget]
  | cons x xs ih =>
      have hx := hlen x (by simp)
      have hxc := hc x (by simp)
      have ht := ih (fun y hy=>hlen y (by simp [hy])) (fun y hy=>hc y (by simp [hy]))
      simp only [SubexponentialSAT.RecordPrograms.budget,List.length_cons]
      nlinarith

theorem tupleCost_le (alphabet : Records) (tuple : List Bool) (R L : ℕ)
    (hr : tuple.length ≤ R) (hl : ∀ w∈alphabet,w.length ≤ L) :
    tupleCost alphabet tuple ≤ 100*(alphabet.length+1)*(R+L+1) := by
  have he := SubexponentialSAT.Encoding.length_encodeList_upper id alphabet L hl
  have hb := budget_le alphabet (fun w=>5*w.length+12*tuple.length+15) L (5*L+12*R+15)
    hl (by
      intro w hw
      have := hl w hw
      change 5*w.length+12*tuple.length+15 ≤ 5*L+12*R+15
      omega)
  change (SubexponentialSAT.ProgramEncoding.encodeRecords alphabet).length ≤ _ at he
  unfold tupleCost
  nlinarith [Nat.zero_le (alphabet.length*R),Nat.zero_le (alphabet.length*L)]

theorem expansionCost_le (rows alphabet : Records) (R L : ℕ)
    (hr : ∀ row∈rows,row.length ≤ R) (hl : ∀ w∈alphabet,w.length ≤ L) :
    expansionCost rows alphabet ≤ 120*(rows.length+1)*(alphabet.length+1)*(R+L+1) := by
  have hb := budget_le rows (tupleCost alphabet) R (100*(alphabet.length+1)*(R+L+1))
    hr (by intro row hm; exact tupleCost_le alphabet row R L (hr row hm) hl)
  unfold expansionCost
  nlinarith [Nat.zero_le (rows.length*alphabet.length*R),
    Nat.zero_le (rows.length*alphabet.length*L),Nat.zero_le (rows.length*alphabet.length)]

theorem output_width (rows alphabet : Records) (R L : ℕ)
    (hr : ∀ row∈rows,row.length ≤ R) (hl : ∀ w∈alphabet,w.length ≤ L) :
    ∀ word∈cartesianOutput rows alphabet,word.length ≤ R+L := by
  intro word hw
  simp only [cartesianOutput,List.mem_reverse,List.mem_flatMap,List.mem_map] at hw
  obtain ⟨row,hm,w,hw,rfl⟩ := hw
  have hrow := hr row hm
  have hal := hl w hw
  simp only [List.length_append]
  omega

theorem stepCost_le (rows alphabet : Records) (R L : ℕ)
    (hr : ∀ row∈rows,row.length ≤ R) (hl : ∀ w∈alphabet,w.length ≤ L) :
    stepCost rows alphabet ≤ 150*(rows.length+1)*(alphabet.length+1)*(R+L+1) := by
  have he := expansionCost_le rows alphabet R L hr hl
  have ho := SubexponentialSAT.Encoding.length_encodeList_upper id (cartesianOutput rows alphabet) (R+L)
    (output_width rows alphabet R L hr hl)
  rw [cartesianOutput_length] at ho
  change (SubexponentialSAT.ProgramEncoding.encodeRecords (cartesianOutput rows alphabet)).length ≤ _ at ho
  unfold stepCost
  nlinarith [Nat.zero_le (rows.length*alphabet.length*R),
    Nat.zero_le (rows.length*alphabet.length*L),Nat.zero_le (rows.length*alphabet.length)]

end SubexponentialSAT.SqrtLog.BucketTupleProgram.ProductBounds

end OAI.Algorithms
