import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.PackingVertexLabels
import OAI.Algorithms.SubexponentialSAT.Subexp.AssignmentLabelSerialization

namespace OAI.Algorithms

/-! Materialize incidence labels from actual two-address read plans. The
physical gather reads the head and factor words in that order. Incidence
numbers are the read-plan list positions, including repeated plans. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram

open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp
open SubexponentialSAT.BitProgram

variable {D r Q : ℕ}

def labelPlans (words : List (Word r Q))
    (address : Fin D → Fin words.length × Fin words.length) : List (List ℕ) :=
  (List.finRange D).map (fun i => [(address i).1.val, (address i).2.val])

def addressLabel (words : List (Word r Q))
    (address : Fin D → Fin words.length × Fin words.length) (i : Fin D) :
    UniversalType r Q 1 :=
  ⟨words.get (address i).1, fun _ => words.get (address i).2⟩

theorem gathered_addressLabel (words : List (Word r Q))
    (address : Fin D → Fin words.length × Fin words.length) (i : Fin D) :
    GatherProgram.gathered (words.map ReadPlan.encodeWord)
      [(address i).1.val, (address i).2.val] =
      CollisionProgram.encodeType (addressLabel words address i) := by
  have hp : (address i).1.val < (words.map ReadPlan.encodeWord).length := by
    simp
  have hn : (address i).2.val < (words.map ReadPlan.encodeWord).length := by
    simp
  simp [GatherProgram.gathered,
    ReadPlan.encodeType_eq_words, List.ofFn_succ, CollisionProgram.registerWord,
    addressLabel]

theorem labelPlans_valid (words : List (Word r Q))
    (address : Fin D → Fin words.length × Fin words.length) :
    ∀ plan ∈ labelPlans words address, ∀ j ∈ plan,
      j < (words.map ReadPlan.encodeWord).length := by
  intro plan hplan j hj
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hplan
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl
  · simp
  · simp

theorem addressLabel_records (words : List (Word r Q))
    (address : Fin D → Fin words.length × Fin words.length) :
    PackingVertexLabels.labelRecords (words.map ReadPlan.encodeWord)
      (labelPlans words address) 0 =
      BucketProgram.vertexRecords (List.finRange D) (addressLabel words address)
        CollisionProgram.encodeType (fun i => List.replicate i.val true) := by
  rw [labelPlans, AssignmentLabelSerialization.labelRecords_finRange]
  unfold BucketProgram.vertexRecords
  apply List.map_congr_left
  intro i _
  exact Prod.ext (gathered_addressLabel words address i) rfl

/-- Actual input bytes to the controller, in the read-plan producer's order. -/
theorem addressLabels_trace (words : List (Word r Q))
    (address : Fin D → Fin words.length × Fin words.length) (regs : Fin 8 → Bool) :
    ∃ steps rf,
      steps ≤ PackingVertexLabels.traceCost (Q*r) (labelPlans words address) 0 ∧
      Trace PackingVertexLabels.program steps
        ((PackingVertexLabels.state regs (words.map ReadPlan.encodeWord).flatten []
          (List.replicate (Q*r) true) []
          (SubexponentialSAT.ProgramEncoding.encodeRecords
            ((labelPlans words address).map PackingVertexLabels.planPayload)) [] [] [] []).withPC
          (some PackingVertexLabels.program.entry))
        ((PackingVertexLabels.state rf (words.map ReadPlan.encodeWord).flatten []
          (List.replicate (Q*r) true) [] [] [] (List.replicate D true)
          (BucketProgram.encodeRecords
            (BucketProgram.vertexRecords (List.finRange D) (addressLabel words address)
              CollisionProgram.encodeType (fun i => List.replicate i.val true)).reverse) []).withPC none) := by
  obtain ⟨n,rf,hn,ht⟩ := PackingVertexLabels.program_trace
    (words.map ReadPlan.encodeWord) (List.replicate (Q*r) true)
    (labelPlans words address) regs 0 [] []
    (by intro row hrow; obtain ⟨w,_,rfl⟩ := List.mem_map.mp hrow
        simp [ReadPlan.encodeWord_length, ReadPlan.wordWidth]) (labelPlans_valid words address)
  refine ⟨n,rf,?_,?_⟩
  · simpa using hn
  · rw [addressLabel_records] at ht
    simpa only [List.append_nil, List.replicate_zero, Nat.zero_add,
      labelPlans, List.length_map, List.length_finRange,
      List.length_replicate] using ht

end SubexponentialSAT.SqrtLog.LayoutProgram

end OAI.Algorithms
