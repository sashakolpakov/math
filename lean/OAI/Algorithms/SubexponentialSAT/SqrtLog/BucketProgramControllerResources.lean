import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInputStats
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsSemantics
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgramLabelBounds
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgramSignedCost

namespace OAI.Algorithms

/-! Ordinary sizes of the actual all-row bucket input.  The row count here
is the length of the emitted incidence plan, and is never replaced by rank. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram.Controller.Resources

open scoped BigOperators
open SubexponentialSAT.Subexp.MatrixProgramSupport

theorem native_rows_le (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool) :
    (PackingIncidenceInput.Loop.plans scopes n 0 scopes.length mask).length ≤
      (LeafStatisticsProgram.variableTotals scopes 0 mask LeafStatisticsSemantics.zero).free *
      (LeafStatisticsProgram.variableTotals scopes 0 mask LeafStatisticsSemantics.zero).occurrence := by
  rw [PackingIncidenceInput.Stats.native_incidence_count]
  change (LeafStatisticsProgram.variableTotals scopes 0 mask LeafStatisticsSemantics.zero).incidences ≤ _
  rw [LeafStatisticsSemantics.incidences_exact, LeafStatisticsSemantics.free_exact,
    LeafStatisticsSemantics.occurrence_exact, HighIncidence.totalScope, ← Incidence.sum_degrees]
  calc
    _ ≤ ∑ _v : LeafStatisticsSemantics.Free mask,
        Finset.univ.sup (Incidence.degree (LeafStatisticsSemantics.completedScope scopes mask)) := by
      apply Finset.sum_le_sum
      intro v _
      exact Finset.le_sup (f := Incidence.degree (LeafStatisticsSemantics.completedScope scopes mask))
        (Finset.mem_univ v)
    _ = _ := by simp

theorem signedWords_length_le (xs : List SignedWord) (L : ℕ)
    (h : preWordsBounded L xs) : (signedWords xs).length ≤ xs.length*(4*L+2) := by
  induction xs with
  | nil => simp [signedWords]
  | cons x xs ih =>
      have hx := h x (by simp)
      have ht := ih (fun y hy => h y (by simp [hy]))
      simp only [signedWords,List.length_append,Encoding.length_frame,List.length_cons]
      nlinarith

theorem signed_matrix_length_le (rows : List (List SignedWord)) (h L : ℕ)
    (hw : ∀ row∈rows,row.length=h) (hb : ∀ row∈rows,preWordsBounded L row) :
    (words (rows.map signedWords)).length ≤ rows.length*(2*(h*(4*L+2))+1) := by
  have hr : ∀ r∈rows.map signedWords,r.length ≤ h*(4*L+2) := by
    intro r hr
    obtain ⟨row,hrow,rfl⟩ := List.mem_map.mp hr
    simpa [hw row hrow] using signedWords_length_le row L (hb row hrow)
  simpa using words_length_bound (rows.map signedWords) (h*(4*L+2)) hr

/-- The actual preprocessor output retains every input row and column. -/
theorem shifted_payload_bounds {W : List Bool} {rows : List (List SignedWord)}
    {shifted : List (List (List Bool))} (h L : ℕ)
    (hr : List.Forall₂ (List.Forall₂ (shiftedWord W)) rows shifted)
    (hW : W.length ≤ L) (hw : ∀ row∈rows,row.length=h)
    (hb : ∀ row∈rows,preWordsBounded L row) :
    shifted.length=rows.length ∧
    (∀ row∈shifted,row.length=h) ∧
    (∀ row∈shifted,∀ x∈row,x.length ≤ 3*L+1) ∧
    (words (shifted.map words)).length ≤ Label.matrixBound h rows.length (3*L+1) := by
  have hl : shifted.length=rows.length := hr.length_eq.symm
  have hw' := shiftedMatrix_rowWidth hr h hw
  have hb' := shiftedMatrix_entries_bound hr L hW hb
  refine ⟨hl,hw',hb',?_⟩
  simpa [hl] using Label.matrix_length_bound shifted h (3*L+1) hw' hb'

theorem shifted_key_length_le {W : List Bool} {rows : List (List SignedWord)}
    {shifted : List (List (List Bool))} (h L : ℕ)
    (hr : List.Forall₂ (List.Forall₂ (shiftedWord W)) rows shifted)
    (hW : W.length ≤ L) (hw : ∀ row∈rows,row.length=h)
    (hb : ∀ row∈rows,preWordsBounded L row) (bits : List Bool) (hlen : bits.length=h) :
    (signatureValue W bits shifted).length ≤ Label.keyBound W h rows.length (3*L+1) := by
  obtain ⟨hl,hw',hb',_⟩ := shifted_payload_bounds h L hr hW hw hb
  have hs := signatureValue_length_bound W bits shifted (3*L+1)
    (by intro row hrow; exact (hw' row hrow).trans hlen.symm) hb'
  simpa [hlen,hl,Label.keyBound] using hs

theorem preprocess_controller_cost_le (W : List Bool) (rows : List (List SignedWord))
    (shifted : List (List (List Bool))) (js : List ℕ) (n h L : ℕ)
    (hr : List.Forall₂ (List.Forall₂ (shiftedWord W)) rows shifted)
    (hW : W.length ≤ L) (hw : ∀ row∈rows,row.length=h)
    (hb : ∀ row∈rows,preWordsBounded L row) (hlen : js.length=h)
    (hjs : ∀ j∈js,j < n) :
    preMatrixCost W rows+Controller.cost W shifted js n h+2 ≤
      Cost.signedTotal W h rows.length L n := by
  have hp := preMatrixCost_polynomial W rows L h hW
    (fun row hrow => ⟨hb row hrow,(hw row hrow).le⟩)
  obtain ⟨hl,hw',hb',_⟩ := shifted_payload_bounds h L hr hW hw hb
  have hc := Cost.controller_cost_bound W shifted js n h (3*L+1) hw' hb' hlen hjs
  rw [hl] at hc
  unfold Cost.signedTotal
  omega

end SubexponentialSAT.SqrtLog.BucketProgram.Controller.Resources

end OAI.Algorithms
