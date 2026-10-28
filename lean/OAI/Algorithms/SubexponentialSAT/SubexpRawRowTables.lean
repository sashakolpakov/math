import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpRawRow
import OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowDataProgram

namespace OAI.Algorithms

/-! Fixed-width validity of the actual indexed row record. All payload
lengths follow from the same table and index bounds used by its machine
producer; no equality to a precomputed polynomial row is required. -/

namespace SubexponentialSAT.SubexpRawRow

open Subexp.UniversalRowProgram
open Subexp.UniversalRowLoop (Tables Valid)

private theorem getD_length (rows : List (List Bool)) (B i : ℕ)
    (hrows : ∀ row ∈ rows, row.length = B) (hi : i < rows.length) :
    (rows.getD i []).length = B := by
  rw [List.getD_eq_getElem _ _ hi]
  exact hrows _ (List.getElem_mem hi)

theorem valid_dataTerm (B : ℕ) (t : Tables) (width rowWidth : List Bool)
    (positions : List ℕ) (h : Valid t width rowWidth positions)
    (hwidth : width.length = 4 * B) (i : ℕ) (hi : i ∈ positions) :
    ValidTerm B (Subexp.UniversalRowLoop.term t positions i) := by
  constructor
  · change (t.values.getD i []).length = 4 * B
    rw [getD_length t.values width.length i h.values (h.bounds i hi).1, hwidth]
  · change (t.inverses.getD i []).length = 4 * B
    rw [getD_length t.inverses width.length i h.inverses (h.bounds i hi).2.1, hwidth]
  · intro factor hfactor
    change factor ∈ Subexp.UniversalRowFactorLoop.factors
      (t.differences.getD i []) t.negatives i positions at hfactor
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hfactor
    have hj' : j ∈ positions := (List.mem_filter.mp hj).1
    constructor
    · change ((t.differences.getD i []).getD j []).length = 4 * B
      rw [getD_length (t.differences.getD i []) width.length j
        (h.differences i hi) (h.innerBounds i hi j hj').1, hwidth]
    · change (t.negatives.getD j []).length = 4 * B
      rw [getD_length t.negatives width.length j h.negatives (h.innerBounds i hi j hj').2, hwidth]

/-- The real cardinality guard either emits no correction terms or terms
whose scalar and factor payloads all have the fixed quartet width. -/
theorem valid_dataRow (B : ℕ) (t : Tables) (width rowWidth : List Bool)
    (positions : List ℕ) (delta limit : List Bool)
    (h : Valid t width rowWidth positions) (hwidth : width.length = 4 * B)
    (hdelta : delta.length = 4 * B) :
    ValidRow B (Subexp.UniversalRowDataProgram.row t positions delta limit) := by
  constructor
  · exact hdelta
  · intro term hterm
    change term ∈ (if positions.length ≤ limit.length then
      positions.map (Subexp.UniversalRowLoop.term t positions) else []) at hterm
    split_ifs at hterm with hc
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hterm
      exact valid_dataTerm B t width rowWidth positions h hwidth i hi
    · simp at hterm

end SubexponentialSAT.SubexpRawRow

end OAI.Algorithms
