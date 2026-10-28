import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMaterializedBits
import OAI.Algorithms.SubexponentialSAT.SubexpLEFactorSystem

namespace OAI.Algorithms

/-!
# The materialized clause row is the little-endian factor table

The two physical validity checks are exactly the local-label validity in the
factor definition. Clause evaluation uses the materialized input bits. All
premises describe the input words and their scope membership, not an assumed
output table or polynomial equality.
-/

namespace SubexponentialSAT.SubexpMaterializedTable

open SubexpScopeMaterializer SubexpMaterializedBits SubexpFactorProgram

variable {D n p : ℕ} {b : Fin D → ℕ} [NeZero p]

/-- The scalar output expression of the actual materializer/finalizer/evaluator. -/
def output (ell : ℕ) (jobs : List (Fin D × List Bool)) (chunks : List (List Bool))
    (literals : List (SAT.Literal (Fin n)))
    (hlen : ((materialize ell jobs chunks true).1.flatten.take n).length = n) : Bool :=
  ((materialize ell jobs chunks true).2 &&
    allZero ((materialize ell jobs chunks true).1.flatten.drop n)) &&
      literals.any (fun l => l.eval (SubexpClauseRowProgram.wordAssignment
        ((materialize ell jobs chunks true).1.flatten.take n) hlen))

/-- No sort order is required: jobs are associated to the actual local scope
by their chunk index, and each such index occurs exactly once. -/
theorem output_eq_table (ell width : ℕ)
    (positions : Fin n ≃ ((j : Fin D) × Fin (b j)))
    (capacity : ∀ j, 2 ^ b j ≤ p) (F : SAT.CNF (Fin n)) (e : {C // C ∈ F})
    (x : {j // j ∈ FactorReduction.cnfScope positions F e} → ZMod p)
    (jobs : List (Fin D × List Bool)) (chunks : List (List Bool))
    (literals : List (SAT.Literal (Fin n))) (hliterals : literals.toFinset = e.val)
    (hcount : chunks.length = D) (hrows : ∀ row ∈ chunks, row.length = ell)
    (hwidth : ∀ job ∈ jobs, job.2.length = width) (hell : ell ≤ width)
    (hdistinct : (jobs.map Prod.fst).Nodup)
    (hsize : ∀ j, b j = min ell (n - j.val * ell))
    (hpositions : ∀ v : Fin n, v.val = (positions v).1.val * ell + (positions v).2.val)
    (hcovered : ∀ j : {j // j ∈ FactorReduction.cnfScope positions F e},
      ∃ label, (j.val, label) ∈ jobs ∧ BinaryArithmetic.toNat label = (x j).val)
    (honly : ∀ job ∈ jobs, ∃ j : {j // j ∈ FactorReduction.cnfScope positions F e},
      j.val = job.1 ∧ BinaryArithmetic.toNat job.2 = (x j).val)
    (hpadding : allZero (chunks.flatten.drop n) = true)
    (hlen : ((materialize ell jobs chunks true).1.flatten.take n).length = n) :
    output ell jobs chunks literals hlen =
      (SubexpLEFactorSystem.system positions capacity F).table (.inr e) x := by
  have hvalid :
      ((materialize ell jobs chunks true).2 = true ∧
        allZero ((materialize ell jobs chunks true).1.flatten.drop n) = true) ↔
        ∀ j, (x j).val < 2 ^ b j.val := by
    rw [materialize_validity_iff_actualWidths ell width n jobs chunks
      hcount hrows hwidth hell hdistinct hpadding]
    constructor
    · intro h j
      obtain ⟨label, hmem, hvalue⟩ := hcovered j
      have hj := h (j.val, label) hmem
      simpa only [hvalue, ← hsize j.val] using hj
    · intro h job hmem
      obtain ⟨j, hj, hvalue⟩ := honly job hmem
      rw [hvalue, ← hj, ← hsize j.val]
      exact h j
  have hclause := materialize_clause_eq_cnfTable ell width positions F e x jobs chunks true
    literals hliterals hcount hrows hwidth hell hdistinct
    (fun j => (hsize j).trans_le (Nat.min_le_left _ _)) hpositions hcovered hlen
  apply Bool.eq_iff_iff.mpr
  simp only [output, Bool.and_eq_true]
  rw [hvalid, hclause, SubexpLEFactorSystem.clause_table_iff]

end SubexponentialSAT.SubexpMaterializedTable

end OAI.Algorithms
