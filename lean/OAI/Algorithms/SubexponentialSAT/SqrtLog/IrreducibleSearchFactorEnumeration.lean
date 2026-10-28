import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchEnumeration

namespace OAI.Algorithms

/-! One fixed tuple-generation call produces all concatenated factor pairs. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearch

open SubexpOrderedTupleData SubexpTupleRefinement SubexpEnumerationPayload

private theorem orderedRows_add (alphabet : List (List Bool)) (n m : ℕ)
    (rows : List (List Bool)) :
    orderedRows alphabet (n + m) rows =
      orderedRows alphabet m (orderedRows alphabet n rows) := by
  induction n generalizing rows with
  | zero => simp [orderedRows]
  | succ n ih =>
      simpa only [Nat.succ_add, orderedRows] using ih (orderedCartesian rows alphabet)

private theorem orderedRows_from_rows (alphabet : List (List Bool)) (n : ℕ)
    (rows : List (List Bool)) :
    orderedRows alphabet n rows =
      rows.flatMap (fun pre => (orderedRows alphabet n [[]]).map (pre ++ ·)) := by
  rw [orderedRows_eq, orderedRows_empty]
  simp only [List.map_map, Function.comp_def]

theorem encoded_candidates_add (d e : ℕ) :
    (candidates (d + e)).map (encodeTuple (scalarCode 3)) =
      (candidates d).flatMap (fun a =>
        (candidates e).map (fun b => encodeTuple (scalarCode 3) a ++
          encodeTuple (scalarCode 3) b)) := by
  change (QuarticSearch.vectors (QuarticSearch.elements 3) (d + e)).map _ = _
  rw [← orderedRows_encoded, orderedRows_add, orderedRows_from_rows]
  rw [orderedRows_encoded, orderedRows_encoded]
  simp only [List.flatMap_map, List.map_map, Function.comp_def, candidates]

theorem encoded_factorPairs (d : ℕ) :
    (candidates ((d + 1) + (d + 1))).map (encodeTuple (scalarCode 3)) =
      (factorPairs d).map (fun ab => encodeTuple (scalarCode 3) ab.1 ++
        encodeTuple (scalarCode 3) ab.2) := by
  rw [encoded_candidates_add]
  simp only [factorPairs, List.map_flatMap, List.map_map, Function.comp_def]

end SubexponentialSAT.SqrtLog.IrreducibleSearch

end OAI.Algorithms
