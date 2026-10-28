import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.ReadPlan

namespace OAI.Algorithms

/-! The physical assignment array and the semantic seed assignment have
the same order. The sequential search stores its chosen values in reverse;
decoding at the supplied seed indices restores their original list order. -/

namespace SubexponentialSAT.Subexp.AssignmentSerialization

open SubexponentialSAT.MulticolorTypes SubexponentialSAT.SlotAssignment SubexponentialSAT.SubexpTypeVariance

/-- A duplicate-free index list recovers the whole reversed value array
from the existing decoder, provided the two lists have equal lengths. -/
theorem reverse_eq_map_decode {I W : Type*} [DecidableEq I]
    (default : W) (indices : List I) (values : List W)
    (hn : indices.Nodup) (hsize : values.length = indices.length) :
    values.reverse = indices.map (fun i => SubexponentialSAT.LocalExpectation.decode default values
      (SubexponentialSAT.LocalExpectation.indexCode indices i)) := by
  apply List.ext_getElem
  · simpa only [List.length_reverse, List.length_map] using hsize
  · intro i hi hj
    have hindex : i < indices.length := by simpa only [List.length_map] using hj
    simp only [List.getElem_map, SubexponentialSAT.LocalExpectation.indexCode,
      hn.idxOf_getElem i hindex, AssignmentEnumeration.decode_eq_reverse_getD,
      List.getD_eq_getElem values.reverse default hi]

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E]
variable {r Q Δ : ℕ} [NeZero r] (P : SubexponentialSAT.Factor.Pattern V E) (slots : SlotMap P Δ)

omit [NeZero r] in
theorem naturalValues_length (a : Word r Q) (tail : List (Word r Q))
    (vertices : List V) (indices : List (SeedIndex V E Δ)) :
    (NaturalAssignment.naturalValues P slots a tail vertices indices).length = indices.length := by
  rw [NaturalAssignment.naturalValues_eq_localAssign]
  simp only [SubexponentialSAT.LocalExpectation.localAssign,
    AssignmentEnumeration.assignWithEvaluator_length, List.length_nil, Nat.add_zero]

omit [NeZero r] in
/-- The assignment's physical rows are in the exact supplied index order. -/
theorem naturalValues_reverse_eq_map (a : Word r Q) (tail : List (Word r Q))
    (vertices : List V) (indices : List (SeedIndex V E Δ)) (hn : indices.Nodup) :
    (NaturalAssignment.naturalValues P slots a tail vertices indices).reverse =
      indices.map (NaturalAssignment.naturalAssignment P slots a tail vertices indices) :=
  reverse_eq_map_decode a indices _ hn (naturalValues_length P slots a tail vertices indices)

omit [NeZero r] in
/-- The row encoding expected by packing is exactly the array produced by
the sequential assignment controller. -/
theorem naturalValues_reverse_map_eq_seedRows (a : Word r Q) (tail : List (Word r Q))
    (vertices : List V) (factors : List E) (hv : vertices.Nodup) (he : factors.Nodup) :
    ((NaturalAssignment.naturalValues P slots a tail vertices
      (AssignmentEnumeration.seedIndices vertices factors Δ)).reverse.map ReadPlan.encodeWord) =
      ReadPlan.seedRows vertices factors (NaturalAssignment.naturalAssignment P slots a tail vertices
        (AssignmentEnumeration.seedIndices vertices factors Δ)) := by
  rw [naturalValues_reverse_eq_map P slots a tail vertices _
    (AssignmentEnumeration.seedIndices_nodup vertices factors Δ hv he)]
  rfl

omit [NeZero r] in
theorem naturalValues_bytes_eq_seedRows (a : Word r Q) (tail : List (Word r Q))
    (vertices : List V) (factors : List E) (hv : vertices.Nodup) (he : factors.Nodup) :
    ((NaturalAssignment.naturalValues P slots a tail vertices
      (AssignmentEnumeration.seedIndices vertices factors Δ)).reverse.map ReadPlan.encodeWord).flatten =
      (ReadPlan.seedRows vertices factors (NaturalAssignment.naturalAssignment P slots a tail vertices
        (AssignmentEnumeration.seedIndices vertices factors Δ))).flatten :=
  congrArg List.flatten (naturalValues_reverse_map_eq_seedRows P slots a tail vertices factors hv he)

end SubexponentialSAT.Subexp.AssignmentSerialization

end OAI.Algorithms
