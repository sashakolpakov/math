import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramSourceTables
import OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowSourceBound

namespace OAI.Algorithms

/-! Uniform byte and running-time bounds for each actually emitted finite
source row. The bound uses the full table width, not the rational rank. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceTyped

open SubexponentialSAT.Subexp SubexponentialSAT.Subexp.UniversalRowTableSource

variable {C : Type*} {Q : ℕ}

theorem positions_length_le (s : Finset (Fin Q)) : (positions s).length ≤ Q := by
  rw [positions_length]
  simpa using Finset.card_le_univ s

theorem positions_value_le (s : Finset (Fin Q)) (i : ℕ) (hi : i∈positions s) : i ≤ Q := by
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp hi
  exact Nat.le_of_lt j.isLt

/-- The scalar table and inverse tables have been materialized. The audited
emitter bound now applies to the actual finite row, including all reads. -/
theorem source_bounds (encode : C → List Bool) (values inverse negative : Fin Q → C)
    (difference : Fin Q → Fin Q → C) (width rowWidth : List Bool)
    (hwidth : ∀ c,(encode c).length=width.length)
    (hrow : rowWidth.length=Q*width.length) (s : Finset (Fin Q))
    (delta limit zero one : List Bool) (S : ℕ)
    (hQ : Q ≤ S) (hw : width.length ≤ S) (hr : rowWidth.length ≤ S)
    (hd : delta.length ≤ S) (hl : limit.length ≤ S)
    (hz : zero.length ≤ S) (ho : one.length ≤ S) :
    UniversalRowSourceProgram.bound (tables encode values inverse negative difference)
      width rowWidth (positions s) delta limit zero one ≤ UniversalRowSourceBound.sourceBound S ∧
    (UniversalRowProgram.rowCode zero one (zero++one)
      (UniversalRowDataProgram.row (tables encode values inverse negative difference)
        (positions s) delta limit)).length ≤ UniversalRowSourceBound.sourceLengthBound S := by
  exact UniversalRowSourceBound.source_bound_le _ width rowWidth (positions s)
    delta limit zero one S
    (tables_valid encode values inverse negative difference width rowWidth hwidth hrow s)
    ((positions_length_le s).trans hQ)
    (fun i hi => (positions_value_le s i hi).trans hQ) hw hr hd hl hz ho

/-- The native mismatch-index stream is itself polynomial-sized. -/
theorem indices_length_le (s : Finset (Fin Q)) :
    (UniversalRowTermProgram.indices (positions s)).length ≤ UniversalRowSourceBound.indicesBound Q :=
  UniversalRowSourceBound.indices_length_le _ Q (positions_length_le s) (positions_value_le s)

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceTyped

end OAI.Algorithms
