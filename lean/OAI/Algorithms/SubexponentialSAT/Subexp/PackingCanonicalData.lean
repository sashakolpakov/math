import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.AssignmentLabelSerialization
import OAI.Algorithms.SubexponentialSAT.Subexp.IncidencePlanSpec
import OAI.Algorithms.SubexponentialSAT.Subexp.TypeEnumeration

namespace OAI.Algorithms

/-!
# The actual assignment data used by canonical packing

The rows are the array emitted by the natural assignment program. Numeric
scope plans recover its actual type labels. The universal type enumeration
names the order of the physical tuple generator, without supplying a lookup
table or assuming the correctness of a packing result.
-/

namespace SubexponentialSAT.Subexp.PackingCanonicalSpec

open MulticolorTypes SubexpTypeVariance ConstructivePacking

variable {D r Q Δ : ℕ}

def indices (D Δ : ℕ) (scopes : List (List ℕ)) :=
  AssignmentEnumeration.seedIndices (List.finRange D) (List.finRange scopes.length) Δ

def plans (D Δ : ℕ) (scopes : List (List ℕ)) : List (List ℕ) :=
  (List.finRange D).map (fun v => IncidencePlanSpec.vertexPlan D Δ scopes v.val)

noncomputable def types (hr : 0 < r) (hQ : 0 < Q) (Δ : ℕ) :
    FiniteEnumeration (UniversalType r Q Δ) :=
  ⟨TypeEnumeration.typeList hr hQ Δ, TypeEnumeration.typeList_nodup hr hQ Δ,
    TypeEnumeration.mem_typeList hr hQ⟩

theorem types_bytes (hr : 0 < r) (hQ : 0 < Q) (Δ : ℕ) :
    (types hr hQ Δ).values.map CollisionProgram.encodeType =
      TypeEnumeration.universalBytes r Q Δ :=
  TypeEnumeration.typeList_bytes hr hQ Δ

theorem types_length (hr : 0 < r) (hQ : 0 < Q) (Δ : ℕ) :
    (types hr hQ Δ).values.length = blockSize r Q Δ := by
  have h := congrArg List.length (types_bytes hr hQ Δ)
  simpa only [List.length_map, TypeEnumeration.universalBytes_length] using h

variable [NeZero r]

def values (scopes : List (List ℕ))
    (hd : ∀ v : Fin D, IncidencePlanSpec.degree scopes v.val ≤ Δ)
    (first : Word r Q) (tail : List (Word r Q)) : List (Word r Q) :=
  NaturalAssignment.naturalValues (IncidencePlanSpec.pattern D scopes)
    (IncidencePlanSpec.slots D Δ scopes hd) first tail (List.finRange D)
    (indices D Δ scopes)

def assignment (scopes : List (List ℕ))
    (hd : ∀ v : Fin D, IncidencePlanSpec.degree scopes v.val ≤ Δ)
    (first : Word r Q) (tail : List (Word r Q)) :
    Assignment (Fin D) (Fin scopes.length) r Q Δ :=
  NaturalAssignment.naturalAssignment (IncidencePlanSpec.pattern D scopes)
    (IncidencePlanSpec.slots D Δ scopes hd) first tail (List.finRange D)
    (indices D Δ scopes)

def rows (scopes : List (List ℕ))
    (hd : ∀ v : Fin D, IncidencePlanSpec.degree scopes v.val ≤ Δ)
    (first : Word r Q) (tail : List (Word r Q)) : List (List Bool) :=
  (values scopes hd first tail).reverse.map ReadPlan.encodeWord

def label (scopes : List (List ℕ))
    (hd : ∀ v : Fin D, IncidencePlanSpec.degree scopes v.val ≤ Δ)
    (first : Word r Q) (tail : List (Word r Q)) : Fin D → UniversalType r Q Δ :=
  assignmentType (IncidencePlanSpec.pattern D scopes) (IncidencePlanSpec.slots D Δ scopes hd)
    (assignment scopes hd first tail)

omit [NeZero r] in
theorem rows_eq_seedRows (scopes : List (List ℕ))
    (hd : ∀ v : Fin D, IncidencePlanSpec.degree scopes v.val ≤ Δ)
    (first : Word r Q) (tail : List (Word r Q)) :
    rows scopes hd first tail =
      ReadPlan.seedRows (List.finRange D) (List.finRange scopes.length)
        (assignment scopes hd first tail) :=
  AssignmentSerialization.naturalValues_reverse_map_eq_seedRows
    (IncidencePlanSpec.pattern D scopes) (IncidencePlanSpec.slots D Δ scopes hd)
    first tail (List.finRange D) (List.finRange scopes.length)
    (List.nodup_finRange D) (List.nodup_finRange scopes.length)

omit [NeZero r] in
theorem rows_width (scopes : List (List ℕ))
    (hd : ∀ v : Fin D, IncidencePlanSpec.degree scopes v.val ≤ Δ)
    (first : Word r Q) (tail : List (Word r Q))
    (row : List Bool) (hrow : row ∈ rows scopes hd first tail) : row.length = Q * r := by
  obtain ⟨w, _, rfl⟩ := List.mem_map.mp hrow
  exact ReadPlan.encodeWord_length w

omit [NeZero r] in
theorem rows_count (scopes : List (List ℕ))
    (hd : ∀ v : Fin D, IncidencePlanSpec.degree scopes v.val ≤ Δ)
    (first : Word r Q) (tail : List (Word r Q)) :
    (rows scopes hd first tail).length = scopes.length + (Δ + 1) * D := by
  simp only [rows, List.length_map, List.length_reverse, values,
    AssignmentSerialization.naturalValues_length, indices,
    AssignmentEnumeration.seedIndices_length, List.length_finRange]

theorem plans_eq_readPlans (scopes : List (List ℕ))
    (hd : ∀ v : Fin D, IncidencePlanSpec.degree scopes v.val ≤ Δ) :
    plans D Δ scopes = (List.finRange D).map
      (ReadPlan.vertexPlan (IncidencePlanSpec.pattern D scopes)
        (IncidencePlanSpec.slots D Δ scopes hd)
        (List.finRange D) (List.finRange scopes.length)) := by
  apply List.map_congr_left
  intro v _
  exact IncidencePlanSpec.vertexPlan_eq_readPlan D Δ scopes hd v

omit [NeZero r] in
theorem label_records (scopes : List (List ℕ))
    (hd : ∀ v : Fin D, IncidencePlanSpec.degree scopes v.val ≤ Δ)
    (first : Word r Q) (tail : List (Word r Q)) :
    PackingVertexLabels.labelRecords (rows scopes hd first tail) (plans D Δ scopes) 0 =
      BucketProgram.vertexRecords (List.finRange D) (label scopes hd first tail)
        CollisionProgram.encodeType (fun v => List.replicate v.val true) := by
  rw [plans_eq_readPlans scopes hd]
  exact AssignmentLabelSerialization.natural_labelRecords_eq_vertexRecords
    (IncidencePlanSpec.pattern D scopes) (IncidencePlanSpec.slots D Δ scopes hd) first tail

end SubexponentialSAT.Subexp.PackingCanonicalSpec

end OAI.Algorithms
