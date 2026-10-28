import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterNativeReferences
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramMarked
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashSelectSAT

namespace OAI.Algorithms

/-! The actual reverse-order reference stream still sums each original clause
exactly once. No equality of an unexecuted favorable enumeration is assumed. -/
namespace SubexponentialSAT.SqrtLog.LeafOuterNative
open SubexponentialSAT LeafProgram
open scoped BigOperators

theorem reference_sum (count : List Bool → ℕ) (m : ℕ) :
    ((RowSelectionProgram.Index.alphabet m).map count).sum=
      ∑ i : Fin m, count (Encoding.encodeNat i.val) := by
  rw [Fin.sum_univ_eq_sum_range (fun j => count (Encoding.encodeNat j)) m]
  simp only [RowSelectionProgram.Index.alphabet,List.map_map,List.map_reverse,List.sum_reverse]
  induction m with
  | zero => simp
  | succ m ih =>
      simpa [List.sum_range_succ,Finset.sum_range_succ,Function.comp_def] using
        congrArg (fun v => v+count (Encoding.encodeNat m)) ih

theorem reference_sum_marked {X Row : Type*} [Fintype X] {m : ℕ}
    (rowAccept : Row → X → Bool) (rows : List Row) (bad : Fin m → X → Bool)
    (count : List Bool → ℕ)
    (hc : ∀ i : Fin m, count (Encoding.encodeNat i.val)=markedCount rowAccept rows bad i) :
    ((RowSelectionProgram.Index.alphabet m).map count).sum=
      HashSelect.mass rowAccept (violationWeight bad) rows := by
  rw [reference_sum]
  simp_rw [hc]
  exact sum_markedCount rowAccept rows bad

theorem reference_sum_cnf {n m : ℕ} (clauses : Fin m → SAT.Clause (Fin n))
    (rows : List (HashSelect.Row m)) (count : List Bool → ℕ)
    (hc : ∀ i : Fin m, count (Encoding.encodeNat i.val)=
      markedCount (HashSelect.cnfRowAccept clauses) rows (fun e x => !(clauses e).eval x) i) :
    ((RowSelectionProgram.Index.alphabet m).map count).sum=
      HashSelect.mass (HashSelect.cnfRowAccept clauses) (HashInput.violationWeight clauses) rows := by
  have h := reference_sum_marked (HashSelect.cnfRowAccept clauses) rows
    (fun e x => !(clauses e).eval x) count hc
  have hw : violationWeight (fun e x => !(clauses e).eval x)=HashInput.violationWeight clauses :=
    funext (cnf_weight clauses)
  exact hw ▸ h

end SubexponentialSAT.SqrtLog.LeafOuterNative

end OAI.Algorithms
