import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpTupleRefinement

namespace OAI.Algorithms

/-! # Exact lexicographic tuple order for the selected quartic search -/

namespace SubexponentialSAT.SubexpOrderedTupleData

open SubexpTupleRefinement

def orderedCartesian (rows alphabet : List (List Bool)) : List (List Bool) :=
  rows.flatMap fun row => alphabet.map (row ++ ·)

theorem orderedCartesian_eq_reverse (rows alphabet : List (List Bool)) :
    orderedCartesian rows alphabet = (Subexp.TupleProgram.cartesianOutput rows alphabet).reverse := by
  simp [orderedCartesian, Subexp.TupleProgram.cartesianOutput]

@[simp] theorem orderedCartesian_length (rows alphabet : List (List Bool)) :
    (orderedCartesian rows alphabet).length = rows.length * alphabet.length := by
  rw [orderedCartesian_eq_reverse, List.length_reverse, Subexp.TupleProgram.cartesianOutput_length]

def orderedRows (alphabet : List (List Bool)) : ℕ → List (List Bool) → List (List Bool)
  | 0, rows => rows
  | n + 1, rows => orderedRows alphabet n (orderedCartesian rows alphabet)

theorem orderedRows_eq (alphabet rows : List (List Bool)) (n : ℕ) :
    orderedRows alphabet n rows =
      rows.flatMap fun pre => (QuarticSearch.vectors alphabet n).map
        (fun v => pre ++ tuplePayload v) := by
  induction n generalizing rows with
  | zero => simp [orderedRows, QuarticSearch.vectors, tuplePayload]
  | succ n ih =>
      rw [orderedRows, ih]
      simp only [orderedCartesian, QuarticSearch.vectors, List.flatMap_assoc,
        List.flatMap_map, List.map_flatMap, List.map_map, Function.comp_def,
        tuplePayload_cons, List.append_assoc]

theorem orderedRows_empty (alphabet : List (List Bool)) (n : ℕ) :
    orderedRows alphabet n [[]] = (QuarticSearch.vectors alphabet n).map tuplePayload := by
  simpa using orderedRows_eq alphabet [[]] n

theorem orderedRows_encoded {A : Type*} (code : StackEncoding.BlockCode A)
    (alphabet : List A) (n : ℕ) :
    orderedRows (alphabet.map code.block) n [[]] =
      (QuarticSearch.vectors alphabet n).map (encodeTuple code) := by
  rw [orderedRows_empty, vectors_map]
  simp only [List.map_map, Function.comp_def, tuplePayload_map]

@[simp] theorem orderedRows_empty_length (alphabet : List (List Bool)) (n : ℕ) :
    (orderedRows alphabet n [[]]).length = alphabet.length ^ n := by
  rw [orderedRows_empty, List.length_map, QuarticSearch.length_vectors]

end SubexponentialSAT.SubexpOrderedTupleData

end OAI.Algorithms
