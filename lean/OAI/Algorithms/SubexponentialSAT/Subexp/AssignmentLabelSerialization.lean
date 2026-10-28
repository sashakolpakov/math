import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.AssignmentSerialization
import OAI.Algorithms.SubexponentialSAT.Subexp.PackingVertexLabels

namespace OAI.Algorithms

/-! The vertex-label producer emits exactly the semantic bucket records,
in ascending vertex order before its explicit accumulator reversal. -/

namespace SubexponentialSAT.Subexp.AssignmentLabelSerialization

open SubexponentialSAT.MulticolorTypes SubexponentialSAT.SubexpTypeVariance SubexponentialSAT.SlotAssignment

theorem labelRecords_finRange {D : ℕ} (rows : List (List Bool))
    (plans : Fin D → List ℕ) :
    PackingVertexLabels.labelRecords rows ((List.finRange D).map plans) 0 =
      (List.finRange D).map (fun v =>
        (GatherProgram.gathered rows (plans v), List.replicate v.val true)) := by
  unfold PackingVertexLabels.labelRecords
  rw [List.length_map, List.length_finRange, ← List.range_eq_range',
    ← List.map_coe_finRange D, List.zipWith_map, List.zipWith_self]

variable {D E r Q Δ : ℕ}
variable (P : SubexponentialSAT.Factor.Pattern (Fin D) (Fin E)) (slots : SlotMap P Δ)

/-- Gathering every actual seed array at the supplied typed read plans
produces exactly the type-key and unary-vertex records used by the bucket. -/
theorem labelRecords_eq_vertexRecords (ω : Assignment (Fin D) (Fin E) r Q Δ) :
    PackingVertexLabels.labelRecords
      (ReadPlan.seedRows (List.finRange D) (List.finRange E) ω)
      ((List.finRange D).map
        (ReadPlan.vertexPlan P slots (List.finRange D) (List.finRange E))) 0 =
      BucketProgram.vertexRecords (List.finRange D) (assignmentType P slots ω)
        CollisionProgram.encodeType (fun v => List.replicate v.val true) := by
  rw [labelRecords_finRange]
  unfold BucketProgram.vertexRecords
  apply List.map_congr_left
  intro v _
  apply Prod.ext
  · exact (PackingVertexLabels.gathered_eq_readPlan _ _).trans
      (ReadPlan.gather_seedRows P slots (List.finRange D) (List.finRange E)
        (fun v => List.mem_finRange v) (fun e => List.mem_finRange e) ω v)
  · rfl

/-- The physical accumulator stores the same records in reverse list order. -/
theorem labelBytes_eq_vertexRecords (ω : Assignment (Fin D) (Fin E) r Q Δ) :
    BucketProgram.encodeRecords
      ((PackingVertexLabels.labelRecords
        (ReadPlan.seedRows (List.finRange D) (List.finRange E) ω)
        ((List.finRange D).map
          (ReadPlan.vertexPlan P slots (List.finRange D) (List.finRange E))) 0).reverse) =
      BucketProgram.encodeRecords
        ((BucketProgram.vertexRecords (List.finRange D) (assignmentType P slots ω)
          CollisionProgram.encodeType (fun v => List.replicate v.val true)).reverse) :=
  congrArg (fun records => BucketProgram.encodeRecords records.reverse)
    (labelRecords_eq_vertexRecords P slots ω)

variable [NeZero r]

omit [NeZero r] in
/-- The producer can consume the rows already emitted by the natural
assignment loop, without reserializing or reordering that assignment. -/
theorem natural_labelRecords_eq_vertexRecords (a : Word r Q) (tail : List (Word r Q)) :
    let indices := AssignmentEnumeration.seedIndices (List.finRange D) (List.finRange E) Δ
    let ω := NaturalAssignment.naturalAssignment P slots a tail (List.finRange D) indices
    PackingVertexLabels.labelRecords
      ((NaturalAssignment.naturalValues P slots a tail (List.finRange D) indices).reverse.map
        ReadPlan.encodeWord)
      ((List.finRange D).map
        (ReadPlan.vertexPlan P slots (List.finRange D) (List.finRange E))) 0 =
      BucketProgram.vertexRecords (List.finRange D) (assignmentType P slots ω)
        CollisionProgram.encodeType (fun v => List.replicate v.val true) := by
  dsimp only
  rw [AssignmentSerialization.naturalValues_reverse_map_eq_seedRows P slots a tail
    (List.finRange D) (List.finRange E) (List.nodup_finRange D) (List.nodup_finRange E)]
  exact labelRecords_eq_vertexRecords P slots _

omit [NeZero r] in
theorem natural_labelBytes_eq_vertexRecords (a : Word r Q) (tail : List (Word r Q)) :
    let indices := AssignmentEnumeration.seedIndices (List.finRange D) (List.finRange E) Δ
    let ω := NaturalAssignment.naturalAssignment P slots a tail (List.finRange D) indices
    BucketProgram.encodeRecords
      ((PackingVertexLabels.labelRecords
        ((NaturalAssignment.naturalValues P slots a tail (List.finRange D) indices).reverse.map
          ReadPlan.encodeWord)
        ((List.finRange D).map
          (ReadPlan.vertexPlan P slots (List.finRange D) (List.finRange E))) 0).reverse) =
      BucketProgram.encodeRecords
        ((BucketProgram.vertexRecords (List.finRange D) (assignmentType P slots ω)
          CollisionProgram.encodeType (fun v => List.replicate v.val true)).reverse) := by
  exact congrArg (fun records => BucketProgram.encodeRecords records.reverse)
    (natural_labelRecords_eq_vertexRecords P slots a tail)

end SubexponentialSAT.Subexp.AssignmentLabelSerialization

end OAI.Algorithms
