import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedBranchCount
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramMarked
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafScopeResourceBoundsDecode
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashSelectSAT
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgramInitial

namespace OAI.Algorithms

/-! Raw tuple rows and decoded selector rows have identical acceptance,
including repeated clause IDs and zero coefficients. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.OuterQuery.Count
open LeafProgram
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {n m : ℕ}

def rawHashes (source : Fin m → List (SAT.Literal (Fin n)))
    (rows : List (List (Fin m × ZMod 3))) : List (SparseRow (Fin n) (ZMod 3)) :=
  rows.map (fun row => row.map (fun term => (term.2,source term.1)))

theorem rawRow_eq (source : Fin m → List (SAT.Literal (Fin n)))
    (row : List (Fin m × ZMod 3)) :
    row.map (fun term => (term.2,source term.1)) =
      HashInputProgram.rawRow source (LeafScopeResourceBounds.listCandidate row) := by
  have h := congrArg (List.map (fun term : Fin m × ZMod 3 => (term.2,source term.1)))
    (List.ofFn_get row)
  simpa only [HashInputProgram.rawRow, LeafScopeResourceBounds.listCandidate,
    List.map_ofFn, Function.comp_def] using h.symm

theorem rawRow_value (source : Fin m → List (SAT.Literal (Fin n)))
    (row : List (Fin m × ZMod 3)) (x : Fin n → Bool) :
    rowValue (ringAlgebra (ZMod 3)) id (fun v => HashInput.boolValue (x v))
      (row.map (fun term => (term.2,source term.1))) =
    ∑ i,HashFamily.row (LeafScopeResourceBounds.listCandidate row) i *
      HashInput.violationVector (fun i => (source i).toFinset) x i := by
  rw [rawRow_eq,HashInputProgram.rawRow_value,HashFamily.row_dot]
  unfold HashFamily.eval
  apply Finset.sum_congr rfl
  intro i _
  rw [HashInputProgram.clauseValue_original]
  rfl

theorem raw_accepts (source : Fin m → List (SAT.Literal (Fin n)))
    (rows : List (List (Fin m × ZMod 3))) (x : Fin n → Bool) :
    (∀ row ∈ rawHashes source rows,
      rowValue (ringAlgebra (ZMod 3)) id (fun v => HashInput.boolValue (x v)) row=0) ↔
    HashSelect.accepts (HashSelect.cnfRowAccept (fun i => (source i).toFinset))
      (rows.map (fun row => HashFamily.row (LeafScopeResourceBounds.listCandidate row))) x=true := by
  simp only [rawHashes,HashSelect.accepts,List.all_map,List.all_eq_true,List.mem_map,
    forall_exists_index,and_imp,forall_apply_eq_imp_iff₂,Function.comp_apply,
    HashSelect.cnfRowAccept,decide_eq_true_eq,rawRow_value]

theorem violates_eq (clause : List (SAT.Literal (Fin n))) (x : Fin n → Bool) :
    NodeSemantics.violates clause x= !(SAT.Clause.eval x clause.toFinset) := by
  induction clause with
  | nil => simp [NodeSemantics.violates,SAT.Clause.eval]
  | cons l ls ih => simp [NodeSemantics.violates,List.all_cons,SAT.Clause.eval_insert,
      ← ih,NodeSemantics.violates]

theorem fullCount_raw_none (source : Fin m → List (SAT.Literal (Fin n)))
    (rows : List (List (Fin m × ZMod 3))) (clause : List (SAT.Literal (Fin n))) :
    PreparedBranchCount.fullCount (rawHashes source rows) false clause =
      HashSelect.acceptedCount (HashSelect.cnfRowAccept (fun i => (source i).toFinset))
        (rows.map (fun row => HashFamily.row (LeafScopeResourceBounds.listCandidate row))) := by
  unfold PreparedBranchCount.fullCount HashSelect.acceptedCount NodeSemantics.ternaryAccepted
  apply Finset.sum_congr rfl
  intro x _
  simp only [Bool.false_eq_true,IsEmpty.forall_iff,and_true,raw_accepts]

theorem fullCount_raw_marked (source : Fin m → List (SAT.Literal (Fin n)))
    (rows : List (List (Fin m × ZMod 3))) (i : Fin m) :
    PreparedBranchCount.fullCount (rawHashes source rows) true (source i) =
      markedCount (HashSelect.cnfRowAccept (fun i => (source i).toFinset))
        (rows.map (fun row => HashFamily.row (LeafScopeResourceBounds.listCandidate row)))
        (fun i x => !(SAT.Clause.eval x (source i).toFinset)) i := by
  unfold PreparedBranchCount.fullCount markedCount NodeSemantics.ternaryAccepted
  apply Finset.sum_congr rfl
  intro x _
  simp only [true_implies,raw_accepts,violates_eq,Bool.and_eq_true]

theorem decode_raw (width : ℕ) (hm : 0 < m) (payload : List Bool) :
    HashFamily.row (LeafScopeResourceBounds.listCandidate
      (LeafScopeResourceBounds.rawDecode m width hm payload)) =
      HashFamilyPayload.decodeVariableRow m width payload := by
  rw [LeafOuterProgram.listCandidate_row]
  unfold HashFamilyPayload.decodeVariableRow HashFamilyPayload.decodeRow
  rw [dite_eq_left hm]
  funext i
  simp only [LeafScopeResourceBounds.rawDecode,HashInputProgram.candidateTerms,
    CodeRowsProgram.coefficient,List.map_ofFn,List.sum_ofFn,HashFamily.row,Function.comp_def]

theorem fullCount_payload_none (source : Fin m → List (SAT.Literal (Fin n)))
    (width : ℕ) (hm : 0 < m) (payloads : List (List Bool))
    (clause : List (SAT.Literal (Fin n))) :
    PreparedBranchCount.fullCount
      (rawHashes source (payloads.map (LeafScopeResourceBounds.rawDecode m width hm))) false clause =
      HashSelect.acceptedCount (HashSelect.cnfRowAccept (fun i => (source i).toFinset))
        (payloads.map (HashFamilyPayload.decodeVariableRow m width)) := by
  rw [fullCount_raw_none]
  simp only [List.map_map,Function.comp_def,decode_raw]

theorem fullCount_payload_marked (source : Fin m → List (SAT.Literal (Fin n)))
    (width : ℕ) (hm : 0 < m) (payloads : List (List Bool)) (i : Fin m) :
    PreparedBranchCount.fullCount
      (rawHashes source (payloads.map (LeafScopeResourceBounds.rawDecode m width hm))) true (source i) =
      markedCount (HashSelect.cnfRowAccept (fun i => (source i).toFinset))
        (payloads.map (HashFamilyPayload.decodeVariableRow m width))
        (fun i x => !(SAT.Clause.eval x (source i).toFinset)) i := by
  rw [fullCount_raw_marked]
  simp only [List.map_map,Function.comp_def,decode_raw]

end SubexponentialSAT.SqrtLog.OuterQuery.Count

end

end OAI.Algorithms
