import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpFactorPrefixControl

namespace OAI.Algorithms

/-! Encounter-order grouping for the physical prefix producer. -/

namespace SubexponentialSAT.SubexpFactorPrefixProgram

open Subexp.FactorPacketCoordinates (Word Prefix originBytes taylorBytes)

def chunk {α : Type*} (enc : α → Word) : List α → Word
  | [] => []
  | x :: xs => true :: (Encoding.frame (enc x) ++ chunk enc xs)

theorem chunk_append {α : Type*} (enc : α → Word) (xs ys : List α) :
    chunk enc (xs ++ ys) = chunk enc xs ++ chunk enc ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.cons_append, chunk, ih, List.append_assoc]

theorem chunk_encodeList {α : Type*} (enc : α → Word) (xs : List α) :
    chunk enc xs ++ [false] = Encoding.encodeList enc xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [chunk, Encoding.encodeList, List.cons_append, List.append_assoc, ih]

theorem chunk_encodeList_append {α : Type*} (enc : α → Word) (xs ys : List α) :
    chunk enc xs ++ Encoding.encodeList enc ys = Encoding.encodeList enc (xs ++ ys) := by
  rw [← chunk_encodeList, ← List.append_assoc, ← chunk_append, chunk_encodeList]

theorem encodeList_map {α β : Type*} (enc : β → Word) (f : α → β) (xs : List α) :
    Encoding.encodeList enc (xs.map f) = Encoding.encodeList (enc ∘ f) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, Encoding.encodeList, Function.comp_apply, ih]

theorem regroup_lengths (ns : List ℕ) (ps : List Prefix) (h : ns.sum = ps.length) :
    (regroup ns ps).map List.length = ns := by
  induction ns generalizing ps with
  | nil => rfl
  | cons n ns ih =>
    have hn : n ≤ ps.length := by simp only [List.sum_cons] at h; omega
    have hd : ns.sum = (ps.drop n).length := by
      simp only [List.length_drop, List.sum_cons] at *
      omega
    simp only [regroup, List.map_cons, List.length_take, Nat.min_eq_left hn, ih _ hd]

theorem regroup_flatten (ns : List ℕ) (ps : List Prefix) (h : ns.sum = ps.length) :
    (regroup ns ps).flatten = ps := by
  induction ns generalizing ps with
  | nil =>
    have hz : ps = [] := List.length_eq_zero_iff.mp (by simpa using h.symm)
    subst ps
    rfl
  | cons n ns ih =>
    have hd : ns.sum = (ps.drop n).length := by
      simp only [List.length_drop, List.sum_cons] at *
      omega
    simp only [regroup, List.flatten_cons, ih _ hd, List.take_append_drop]

def zipPrefixes (origins : List (List Word)) (columns : List (List (List Word))) : List Prefix :=
  List.zipWith Prefix.mk origins columns

theorem zipPrefixes_origins (origins : List (List Word)) (columns : List (List (List Word)))
    (h : origins.length = columns.length) :
    (zipPrefixes origins columns).map Prefix.origin = origins := by
  induction origins generalizing columns with
  | nil => simp [zipPrefixes]
  | cons x xs ih =>
    cases columns with
    | nil => simp at h
    | cons y ys =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      simp only [zipPrefixes, List.zipWith_cons_cons, List.map_cons]
      exact congrArg (x :: ·) (ih ys h)

theorem zipPrefixes_columns (origins : List (List Word)) (columns : List (List (List Word)))
    (h : origins.length = columns.length) :
    (zipPrefixes origins columns).map Prefix.taylor = columns := by
  induction origins generalizing columns with
  | nil =>
    have hz : columns = [] := List.length_eq_zero_iff.mp h.symm
    subst columns
    rfl
  | cons x xs ih =>
    cases columns with
    | nil => simp at h
    | cons y ys =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      simp only [zipPrefixes, List.zipWith_cons_cons, List.map_cons]
      exact congrArg (y :: ·) (ih ys h)

theorem zipPrefixes_length (origins : List (List Word)) (columns : List (List (List Word)))
    (h : origins.length = columns.length) : (zipPrefixes origins columns).length = origins.length := by
  simpa only [List.length_map] using congrArg List.length (zipPrefixes_origins origins columns h)

def grouped (scopes : List (List ℕ)) (origins : List (List Word))
    (columns : List (List (List Word))) : List (List Prefix) :=
  regroup (scopes.map List.length) (zipPrefixes origins columns)

theorem grouped_lengths (scopes : List (List ℕ)) (origins : List (List Word))
    (columns : List (List (List Word))) (heq : origins.length = columns.length)
    (hsize : (scopes.map List.length).sum = origins.length) :
    (grouped scopes origins columns).map List.length = scopes.map List.length := by
  apply regroup_lengths
  rw [zipPrefixes_length origins columns heq]
  exact hsize

theorem grouped_flatten (scopes : List (List ℕ)) (origins : List (List Word))
    (columns : List (List (List Word))) (heq : origins.length = columns.length)
    (hsize : (scopes.map List.length).sum = origins.length) :
    (grouped scopes origins columns).flatten = zipPrefixes origins columns := by
  apply regroup_flatten
  rw [zipPrefixes_length origins columns heq]
  exact hsize

theorem originStream_zip (origins : List (List Word)) (columns : List (List (List Word)))
    (h : origins.length = columns.length) :
    originStream (zipPrefixes origins columns) = Encoding.encodeList (Encoding.encodeList id) origins := by
  have he := congrArg (Encoding.encodeList (Encoding.encodeList id))
    (zipPrefixes_origins origins columns h)
  rw [encodeList_map] at he
  exact he

theorem taylorStream_zip (origins : List (List Word)) (columns : List (List (List Word)))
    (h : origins.length = columns.length) :
    taylorStream (zipPrefixes origins columns) =
      Encoding.encodeList (Encoding.encodeList (Encoding.encodeList id)) columns := by
  have he := congrArg (Encoding.encodeList (Encoding.encodeList (Encoding.encodeList id)))
    (zipPrefixes_columns origins columns h)
  rw [encodeList_map] at he
  exact he

end SubexponentialSAT.SubexpFactorPrefixProgram

end OAI.Algorithms
