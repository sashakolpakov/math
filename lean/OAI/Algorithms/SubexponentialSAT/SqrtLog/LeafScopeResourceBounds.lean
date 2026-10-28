import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgramNativeSemantics
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgramSupplied

namespace OAI.Algorithms

/-! Resource bounds for the exact physical scope stream, including zero
coefficients, repeated raw slots, empty hash rows, and the optional mark. -/
namespace SubexponentialSAT.SqrtLog.LeafScopeResourceBounds
open HashScopeProgram

abbrev slots {α : Type*} (rows : List (List α)) : ℕ :=
  (rows.map List.length).sum

theorem slots_le {α : Type*} (rows : List (List α)) (D : ℕ)
    (h : ∀ row ∈ rows, row.length ≤ D) : slots rows ≤ rows.length * D := by
  induction rows with
  | nil => simp [slots]
  | cons row rows ih =>
    have hr := h row (by simp)
    have hs := ih (fun r hr => h r (by simp [hr]))
    simp only [slots, List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul] at *
    omega

theorem row_length (t d k : ℕ) {clauses : List (List Bool)}
    (codes : Fin clauses.length → List ℕ) (hcodes : ∀ i, (codes i).length ≤ k)
    (row : List (Fin clauses.length × ZMod 3)) :
    (scope (FromTuple.interpretedTerms t d codes row)).length ≤ row.length * k := by
  apply (scope_length_le _).trans
  simpa [slots, FromTuple.interpretedTerms, List.map_map, Function.comp_def] using
    slots_le (row.map fun a => codes a.1) k (by
      intro r hr
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
      exact hcodes a.1)

theorem mark_length (k : ℕ) {clauses : List (List Bool)}
    (codes : Fin clauses.length → List ℕ) (hcodes : ∀ i, (codes i).length ≤ k)
    (i : Fin clauses.length) : (Marked.markedScope (codes i)).length ≤ k :=
  (SubexpScopeProducer.scope_length_le _ _).trans (hcodes i)

theorem scope_mass (t d k : ℕ) {clauses : List (List Bool)}
    (codes : Fin clauses.length → List ℕ) (hcodes : ∀ i, (codes i).length ≤ k)
    (rows : RawTable.Rows clauses.length) (mark : Option (Fin clauses.length)) :
    slots (Complete.scopes t d codes rows mark) ≤ (slots rows + mark.isSome.toNat) * k := by
  have hr : slots (rows.map fun row => scope (FromTuple.interpretedTerms t d codes row)) ≤ slots rows * k := by
    induction rows with
    | nil => simp [slots]
    | cons row rows ih =>
      have hh := row_length t d k codes hcodes row
      simp only [slots, List.map_cons, List.sum_cons, Nat.add_mul] at *
      omega
  cases mark with
  | none => simpa [Complete.scopes, slots] using hr
  | some i =>
    have hm := mark_length k codes hcodes i
    simp only [Complete.scopes, Option.toList_some, List.map_cons, List.map_nil,
      slots, List.map_append, List.sum_append, List.sum_cons, List.sum_nil,
      Nat.add_zero, Option.isSome_some, Bool.toNat_true, Nat.add_mul, Nat.one_mul] at *
    omega

theorem scope_arity (t d k D : ℕ) {clauses : List (List Bool)}
    (codes : Fin clauses.length → List ℕ) (hcodes : ∀ i, (codes i).length ≤ k)
    (rows : RawTable.Rows clauses.length) (mark : Option (Fin clauses.length))
    (hrows : ∀ row ∈ rows, row.length ≤ D) (hD : 1 ≤ D) :
    ∀ row ∈ Complete.scopes t d codes rows mark, row.length ≤ D * k := by
  intro row hr
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨r, hrmem, rfl⟩ := List.mem_map.mp hr
    exact (row_length t d k codes hcodes r).trans (Nat.mul_le_mul_right k (hrows r hrmem))
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr
    exact (mark_length k codes hcodes i).trans (by simpa using Nat.mul_le_mul_right k hD)

theorem scopes_nodup (t d : ℕ) {clauses : List (List Bool)}
    (codes : Fin clauses.length → List ℕ) (rows : RawTable.Rows clauses.length)
    (mark : Option (Fin clauses.length)) :
    ∀ row ∈ Complete.scopes t d codes rows mark, row.Nodup := by
  intro row hr
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hr
    exact scope_nodup _
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr
    exact SubexpScopeProducer.scope_nodup _ _

theorem supplied_slots {m B : ℕ} (s : SparseCode.SuppliedShifts m B)
    (Q : SparseCode.SuppliedLocal m B) :
    slots (CodeRowsProgram.serializedRows m s Q) ≤
      SparseCode.totalRows m B * SparseCode.degreeBound m B := by
  simpa [CodeRowsProgram.serializedRows_supplied_length] using
    slots_le (CodeRowsProgram.serializedRows m s Q) (SparseCode.degreeBound m B)
      (CodeRowsProgram.serializedRows_supplied_slots s Q)

end SubexponentialSAT.SqrtLog.LeafScopeResourceBounds

end OAI.Algorithms
