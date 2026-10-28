import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.PackingCanonicalData
import OAI.Algorithms.SubexponentialSAT.Subexp.PackingExecutionSpec

namespace OAI.Algorithms

/-!
# Canonical packing specification from the produced assignment

All representation fields are proved from the natural assignment array,
the numeric scope plans, and the physical universal-type enumeration. The
width word is retained literally; only its length matters to the gather
program. No packing result or lookup correctness is an input.
-/

namespace SubexponentialSAT.Subexp.PackingCanonicalSpec

open MulticolorTypes

variable {D r Q Δ : ℕ} [NeZero r]

def params (scopes : List (List ℕ))
    (hd : ∀ v : Fin D, IncidencePlanSpec.degree scopes v.val ≤ Δ)
    (first : Word r Q) (tail : List (Word r Q)) (width : List Bool) :
    PackingFrontend.Params where
  D := D
  Δ := Δ
  scopes := scopes
  rows := rows scopes hd first tail
  width := width
  alphabet := AssignmentAlphabetSemantics.wordBytes r Q

omit [NeZero r] in
/-- Concrete input data accepted by the existing packing program. -/
theorem input_eq (scopes : List (List ℕ))
    (hd : ∀ v : Fin D, IncidencePlanSpec.degree scopes v.val ≤ Δ)
    (first : Word r Q) (tail : List (Word r Q)) (width : List Bool) :
    (params scopes hd first tail width).input =
      ⟨(rows scopes hd first tail).flatten, width, List.replicate D true,
        List.replicate Δ true, SubexpPlanAlphabetBase.scopeBytes scopes,
        ProgramEncoding.encodeRecords (AssignmentAlphabetSemantics.wordBytes r Q)⟩ := rfl

omit [NeZero r] in
/-- The saved alphabet can be identified using the actual assignment
frontend's word-order theorem. No permutation of the emitted bytes occurs. -/
theorem input_eq_of_wordOrder (scopes : List (List ℕ))
    (hd : ∀ v : Fin D, IncidencePlanSpec.degree scopes v.val ≤ Δ)
    (first : Word r Q) (tail : List (Word r Q)) (width : List Bool)
    (horder : (first :: tail).map ReadPlan.encodeWord =
      AssignmentAlphabetSemantics.wordBytes r Q) :
    (params scopes hd first tail width).input =
      ⟨(rows scopes hd first tail).flatten, width, List.replicate D true,
        List.replicate Δ true, SubexpPlanAlphabetBase.scopeBytes scopes,
        ProgramEncoding.encodeRecords ((first :: tail).map ReadPlan.encodeWord)⟩ := by
  rw [horder]
  rfl

/-- Every `Spec` field is discharged from the actual input construction.
In particular the label records are derived, not assumed. -/
noncomputable def specWithWidth (hr : 0 < r) (hQ : 0 < Q)
    (scopes : List (List ℕ))
    (hd : ∀ v : Fin D, IncidencePlanSpec.degree scopes v.val ≤ Δ)
    (first : Word r Q) (tail : List (Word r Q)) (width : List Bool)
    (hwidth : width.length = Q * r) : PackingExecution.Spec (UniversalType r Q Δ) where
  params := params scopes hd first tail width
  types := types hr hQ Δ
  label := label scopes hd first tail
  encodeType := CollisionProgram.encodeType
  encodeType_injective := CollisionProgram.encodeType_injective
  rows_width := fun row hrow => (rows_width scopes hd first tail row hrow).trans hwidth.symm
  rows_count := rows_count scopes hd first tail
  degree_bound := hd
  label_records := label_records scopes hd first tail
  type_records := (types_bytes hr hQ Δ).symm

/-- Convenience specialization when the width word is canonical unary. -/
noncomputable def spec (hr : 0 < r) (hQ : 0 < Q)
    (scopes : List (List ℕ))
    (hd : ∀ v : Fin D, IncidencePlanSpec.degree scopes v.val ≤ Δ)
    (first : Word r Q) (tail : List (Word r Q)) :
    PackingExecution.Spec (UniversalType r Q Δ) :=
  specWithWidth hr hQ scopes hd first tail (List.replicate (Q * r) true)
    (by simp only [List.length_replicate])

omit [NeZero r] in
@[simp] theorem specWithWidth_params (hr : 0 < r) (hQ : 0 < Q)
    (scopes : List (List ℕ))
    (hd : ∀ v : Fin D, IncidencePlanSpec.degree scopes v.val ≤ Δ)
    (first : Word r Q) (tail : List (Word r Q)) (width : List Bool)
    (hwidth : width.length = Q * r) :
    (specWithWidth hr hQ scopes hd first tail width hwidth).params =
      params scopes hd first tail width := rfl

omit [NeZero r] in
@[simp] theorem specWithWidth_label (hr : 0 < r) (hQ : 0 < Q)
    (scopes : List (List ℕ))
    (hd : ∀ v : Fin D, IncidencePlanSpec.degree scopes v.val ≤ Δ)
    (first : Word r Q) (tail : List (Word r Q)) (width : List Bool)
    (hwidth : width.length = Q * r) :
    (specWithWidth hr hQ scopes hd first tail width hwidth).label =
      label scopes hd first tail := rfl

omit [NeZero r] in
@[simp] theorem specWithWidth_types (hr : 0 < r) (hQ : 0 < Q)
    (scopes : List (List ℕ))
    (hd : ∀ v : Fin D, IncidencePlanSpec.degree scopes v.val ≤ Δ)
    (first : Word r Q) (tail : List (Word r Q)) (width : List Bool)
    (hwidth : width.length = Q * r) :
    (specWithWidth hr hQ scopes hd first tail width hwidth).types = types hr hQ Δ := rfl

end SubexponentialSAT.Subexp.PackingCanonicalSpec

end OAI.Algorithms
