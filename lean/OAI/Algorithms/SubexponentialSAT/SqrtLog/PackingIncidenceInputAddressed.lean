import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInputAddress
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram

namespace OAI.Algorithms

/-! The saved stream contains word addresses, so its second component is the
ambient-offset factor address. Incidence positions and owner fibers are unchanged. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput
open SubexponentialSAT.Subexp

def addressedEntries (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool) : List (ℕ × ℕ) :=
  (Semantics.nativeEntries scopes mask).map (fun p => (p.1,n+p.2))

@[simp] theorem addressedEntries_length (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool) :
    (addressedEntries scopes n mask).length = (Semantics.nativeEntries scopes mask).length := by
  simp [addressedEntries]

/-- Equality transport of incidence positions preserves their numeric indices. -/
def addressedIndex (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool) :
    Fin (addressedEntries scopes n mask).length ≃ Semantics.Incidences scopes mask where
  toFun i := ⟨i.val,by simpa only [addressedEntries_length] using i.isLt⟩
  invFun i := ⟨i.val,by simpa only [addressedEntries_length] using i.isLt⟩
  left_inv i := Fin.ext rfl
  right_inv i := Fin.ext rfl

@[simp] theorem addressedIndex_val (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool)
    (i : Fin (addressedEntries scopes n mask).length) :
    (addressedIndex scopes n mask i).val = i.val := rfl

@[simp] theorem addressedEntries_get (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool)
    (i : Fin (addressedEntries scopes n mask).length) :
    (addressedEntries scopes n mask).get i =
      (let p := (Semantics.nativeEntries scopes mask).get (addressedIndex scopes n mask i)
       (p.1,n+p.2)) := by
  change
    (List.map (fun p => (p.1,n+p.2)) (Semantics.nativeEntries scopes mask))[i.val] =
      (let p := (Semantics.nativeEntries scopes mask)[(addressedIndex scopes n mask i).val]
       (p.1,n+p.2))
  rw [List.getElem_map]
  rfl

@[simp] theorem addressedEntries_owners (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool) :
    (addressedEntries scopes n mask).map Prod.fst =
      (Semantics.nativeEntries scopes mask).map Prod.fst := by
  simp [addressedEntries,List.map_map]

theorem fiberIndices_shift (ps : List (ℕ × ℕ)) (n query start : ℕ) :
    LayoutOwnerFiberProgram.fiberIndices query start (ps.map (fun p => (p.1,n+p.2))) =
      LayoutOwnerFiberProgram.fiberIndices query start ps := by
  induction ps generalizing start with
  | nil => rfl
  | cons p ps ih => simp [LayoutOwnerFiberProgram.fiberIndices,ih]

theorem addressedEntries_fibers (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool)
    (query start : ℕ) :
    LayoutOwnerFiberProgram.fiberIndices query start (addressedEntries scopes n mask) =
      LayoutOwnerFiberProgram.fiberIndices query start (Semantics.nativeEntries scopes mask) :=
  fiberIndices_shift _ n query start

theorem addressedEntries_plans (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool) :
    (addressedEntries scopes n mask).map (fun p => [p.1,p.2]) = Install.plans scopes n mask := by
  rw [Install.plans,Semantics.plans_eq]
  simp only [addressedEntries,Semantics.nativeEntries,List.map_map,Function.comp_def]

theorem addressedEntries_stream (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool) :
    LayoutOwnerFiberProgram.stream (addressedEntries scopes n mask) =
      ProgramEncoding.encodeRecords
        (PackingIncidenceProgram.planAlphabet (Install.plans scopes n mask)) := by
  calc
    _ = ProgramEncoding.encodeRecords
        (((addressedEntries scopes n mask).map (fun p => [p.1,p.2])).map
          PackingVertexLabels.planPayload) := by
      rw [LayoutOwnerFiberProgram.stream_original,List.map_map]
      rfl
    _ = ProgramEncoding.encodeRecords
        ((Install.plans scopes n mask).map PackingVertexLabels.planPayload) := by
      rw [addressedEntries_plans]
    _ = _ := rfl

end SubexponentialSAT.SqrtLog.PackingIncidenceInput

end OAI.Algorithms
